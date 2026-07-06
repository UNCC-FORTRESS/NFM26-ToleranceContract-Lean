/-
Copyright (c) 2026 dL-tolcontract contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-tolcontract contributors
-/
import DLLean

/-!
# Tolerance contracts (NFM'26) — semantic definitions (review gate)

This module transcribes, into the dL-lean foundation, the four semantic objects
of "Sensor Tolerance Contracts for Safety Assurance in CPS" (NFM'26) that
Theorem 1 (soundness of contract governance) is stated over:

* `cTol` / `RecTol`  — Definitions 3 and 4: the single tolerance cycle and its
  recursive (recurring) extension over sensor-estimate time-series;
* `Sat` / `SatInf`   — Satisfaction `S ⊨[Ts,Te] tc` (Def 4, last paragraph);
* `tcHP` / `cCPS`    — Definition 5 + Figure 6: the contract-governance program
  and the contracted CPS;
* `WellFormed`       — the well-formedness side condition (Var(ψn)∪Var(ψt) ⊆ …);
* `downS`            — the `⇓s` extraction `{ω ∈ V | ω(_tc)=true}`.

These are the **faithfulness gate**: no theorem is proved here. `NOTE:` marks a
fidelity decision flagged for review; `GATE:` marks a point where the Lean text
is the literal transcription of the paper and must be checked against it.

Boolean variables (`cd`) are not primitive in dL; the paper's footnote 2 says
they "can be encoded". We encode a Boolean `b` as a real with the convention
`true ≡ (b = 1)`, `false ≡ (b = 0)` (see `bTrue`/`bFalse`/`setTrue`/`setFalse`).
The extraction variable `_tc` uses the same convention.
-/

namespace DLTol

open DL

variable {V : Type*}

/-! ## Boolean-as-real encoding (footnote 2) -/

/-- `?b` guard: the Boolean variable `b` is true, encoded `b = 1`. -/
def bTrue (b : V) : Formula V := .cmp .eq (.var b) (.const 1)

/-- `b := true`, encoded `b := 1`. -/
def setTrue (b : V) : Program V := .assign b (.const 1)

/-- `b := false`, encoded `b := 0`. -/
def setFalse (b : V) : Program V := .assign b (.const 0)

/-- `?¬b`: the guard `¬(b = 1)`.

NOTE: we read the paper's `¬cd` as the logical negation of the `?cd` guard, i.e.
`¬(cd = 1)`, rather than `cd = 0`. This makes the branch pair `?cd ∪ ?¬cd`
*exhaustive* for an arbitrary initial real value of `cd` (Theorem 1 does not
initialize `cd`), which is what branch-reachability at `tc = 0` relies on. Once
`cd` has been assigned via `setTrue`/`setFalse` it is `∈ {0,1}` and the two
readings coincide. -/
def bFalse (b : V) : Formula V := .neg (bTrue b)

/-! ## The distinguished variables of contract governance

`tc-hp` reads the global clock `clk` (the CPS's own time variable `tc`, which
lives in `Var(α)`) and writes the four fresh auxiliary variables
`cd, tab, tcd, tcAcc` (the paper's `cd, tab, tcd, _tc`). Bundled so that `tcHP`
reads cleanly and so freshness/distinctness can be stated over one record. -/
structure Scheme (V : Type*) where
  /-- cooldown phase flag `cd`. -/
  cd : V
  /-- start time of the current abnormality duration `tab`. -/
  tab : V
  /-- start time of the current cooldown duration `tcd`. -/
  tcd : V
  /-- acceptance marker `_tc`. -/
  tcAcc : V
  /-- global clock `tc` (belongs to `Var(α)`, only read by `tc-hp`). -/
  clk : V

/-! ## Definition 5 + Figure 6 — contract-governance program `tc-hp`

We transcribe Figure 6 exactly. Recall dL precedence: `;` binds tighter than
`∪`, so `A;B ∪ C;D = (A;B) ∪ (C;D)`; the trailing `_tc`-updates are attached to
the *whole* two-case choice via explicit parenthesisation, matching the figure's
outer indentation. -/

/-- Normal case, cooldown already running: `?cd`. -/
def normalContinue (S : Scheme V) : Program V := .test (bTrue S.cd)

/-- Normal case, cooldown starts: `?¬cd ; cd := true ; tcd := tc`. -/
def normalStart (S : Scheme V) : Program V :=
  .seq (.test (bFalse S.cd)) (.seq (setTrue S.cd) (.assign S.tcd (.var S.clk)))

/-- Abnormality starts (was in cooldown, and it is long enough):
`?cd ; cd := false ; ?(tc − tcd ≥ δ) ; tab := tc`. -/
def abnormalStart (S : Scheme V) (δ : ℝ) : Program V :=
  .seq (.test (bTrue S.cd))
    (.seq (setFalse S.cd)
      (.seq (.test (.cmp .ge (.binop .sub (.var S.clk) (.var S.tcd)) (.const δ)))
        (.assign S.tab (.var S.clk))))

/-- Abnormality continues (not in cooldown, duration bound holds):
`?¬cd ; ?(tc − tab ≤ τ)`. -/
def abnormalContinue (S : Scheme V) (τ : ℝ) : Program V :=
  .seq (.test (bFalse S.cd))
    (.test (.cmp .le (.binop .sub (.var S.clk) (.var S.tab)) (.const τ)))

/-- **Figure 6: `tc-hp(ψn, ψt, τ, δ)`.**

```
  ( ?ψn ; (?cd ∪ ?¬cd; cd:=true; tcd:=tc)
    ∪
    ?(¬ψn ∧ ψt) ; ( ?cd; cd:=false; ?(tc−tcd≥δ); tab:=tc
                    ∪ ?¬cd; ?(tc−tab≤τ) ) )
  ; _tc := true ; _tc := false
```

GATE: the trailing `_tc := true ; _tc := false` is transcribed **verbatim** from
the figure — both assignments, in sequence, on every path. Net effect: `_tc = 0`
(false) at the *end* of `tc-hp`. See `Contract`'s companion analysis for why this
is load-bearing for whether `downS` of the loop's reachable set is non-empty. -/
def tcHP (S : Scheme V) (ψn ψt : Formula V) (τ δ : ℝ) : Program V :=
  .seq
    (.choice
      (.seq (.test ψn) (.choice (normalContinue S) (normalStart S)))
      (.seq (.test (.and (.neg ψn) ψt)) (.choice (abnormalStart S δ) (abnormalContinue S τ))))
    (.seq (setTrue S.tcAcc) (setFalse S.tcAcc))

/-- **Definition 5: contracted CPS `c-cps(α*, tc)`.**
`(sensing ; tc-hp(ψn,ψt,τ,δ) ; ctrl_logic ; plant)*`. -/
def cCPS (S : Scheme V) (sensing ctrlLogic plant : Program V)
    (ψn ψt : Formula V) (τ δ : ℝ) : Program V :=
  .star (.seq sensing (.seq (tcHP S ψn ψt τ δ) (.seq ctrlLogic plant)))

/-! ## Well-formedness (Def 5 companion) -/

/-- All variables of a program, `Var(α) = FV(α) ∪ BV(α)`. -/
def Program.vars (α : Program V) : Set V := α.fv ∪ α.bv

/-- All variables of a constraint formula.

NOTE: contract constraints (Fig. 5) are the quantifier-free, modality-free
fragment, so `Var(ψ) = FV(ψ)` (no bound variables). We use `Formula.fv`. -/
def Formula.vars (ψ : Formula V) : Set V := ψ.fv

/-- **Well-formed contracted CPS.**
`(Var(ψn) ∪ Var(ψt)) ⊆ (Var(α) \ BV(plant)) ∪ BV(sensing ; ctrl_logic)`.

GATE: `\` and `∪` associate as `(Var(α) \ BV(plant)) ∪ BV(sensing;ctrl_logic)`.
Under `BV(sensing;ctrl_logic) ⊆ Var(α)` this equals `Var(α)` minus the
solely-plant-modifiable variables `BV(plant) \ BV(sensing;ctrl_logic)`, matching
the prose ("accessible by the original CPS, and not solely modifiable by the
plant"). -/
def WellFormed (sensing ctrlLogic plant : Program V) (ψn ψt : Formula V) : Prop :=
  (Formula.vars ψn ∪ Formula.vars ψt) ⊆
    (Program.vars (sensing.seq (ctrlLogic.seq plant)) \ plant.bv) ∪ (sensing.seq ctrlLogic).bv

/-! ## `⇓s` extraction and reachable-set (strongest-postcondition) -/

/-- Strongest postcondition set `φpre⟨α⟩ = {ν | ∃ ω ∈ ⟦φpre⟧, (ω,ν) ∈ ⟦α⟧}`
(Def 1's `[[φpre⟨α⟩]]`). -/
def spSet (φpre : Formula V) (α : Program V) : Set (State V) :=
  {ν | ∃ ω, Formula.sat φpre ω ∧ Program.sem α ω ν}

/-- **`⇓s` extraction** `V⇓s = {ω ∈ V | ω(_tc) = true}` (encoded `_tc = 1`). -/
def downS (S : Scheme V) (Vset : Set (State V)) : Set (State V) :=
  {ω ∈ Vset | ω S.tcAcc = 1}

/-! ## Definition 3 — single tolerance cycle `c-tol`

A "set of sensor estimates with timestamps" is modelled as a set of dL states
`S : Set (State V)`; the timestamp of an estimate `ω` is `ω clk` (its value of
the global clock). "All estimates in interval `[a,b]`" ranges over the `ω ∈ S`
with `a ≤ ω clk ≤ b`; normality/tolerability are the dL formulas `ψn`/`ψt`
evaluated at `ω`. -/

/-- **`c-tol[Ts,Te](S, ψn, ψt, τ, δ)`** (Def 3): there exist `Tas`, `Tae` with
`Ts < Tas < Tae < Te` splitting `[Ts,Te]` into a normal prefix (all `ψn`), a
bounded-abnormal middle (all `ψt`, length `≤ τ`), and a normal cooldown suffix
(all `ψn`, length `≥ δ`).

GATE: intervals are transcribed **closed** as in the paper. The shared endpoints
`Tas` (in both the normal prefix and the abnormal middle) and `Tae` (in both the
abnormal middle and the cooldown) therefore carry *both* constraints; e.g. an
estimate at exactly `Tas` must satisfy `ψn ∧ ψt`. -/
def cTol (clk : V) (S : Set (State V)) (ψn ψt : Formula V) (τ δ : ℝ)
    (Ts Te : ℝ) : Prop :=
  ∃ Tas Tae : ℝ, Ts < Tas ∧ Tas < Tae ∧ Tae < Te ∧
    -- (normality) `[Ts, Tas]` all normal
    (∀ ω ∈ S, Ts ≤ ω clk → ω clk ≤ Tas → Formula.sat ψn ω) ∧
    -- (abnormal duration) `[Tas, Tae]` all tolerable, and length `≤ τ`
    ((∀ ω ∈ S, Tas ≤ ω clk → ω clk ≤ Tae → Formula.sat ψt ω) ∧ Tae - Tas ≤ τ) ∧
    -- (cooldown duration) `[Tae, Te]` all normal, and length `≥ δ`
    ((∀ ω ∈ S, Tae ≤ ω clk → ω clk ≤ Te → Formula.sat ψn ω) ∧ δ ≤ Te - Tae)

/-! ## Definition 4 — recurring tolerance `rec-tol`

The paper's recursive definition (base = one cycle; recursive = a cycle
`[Ts,Tm]` followed by `rec-tol` on `[Tm,Te]`) is a least fixed point, hence a
**finite** chain of cycles covering `[Ts,Te]`. We encode it as an inductive
`Prop` with exactly the two constructors — this is the least fixed point. -/

/-- **`rec-tol[Ts,Te](S, ψn, ψt, τ, δ)`** (Def 4). -/
inductive RecTol (clk : V) (S : Set (State V)) (ψn ψt : Formula V) (τ δ : ℝ) :
    ℝ → ℝ → Prop
  /-- base case: a single tolerance cycle covers `[Ts,Te]`. -/
  | base {Ts Te : ℝ} : cTol clk S ψn ψt τ δ Ts Te → RecTol clk S ψn ψt τ δ Ts Te
  /-- recursive case: `[Ts,Tm]` is one cycle and `[Tm,Te]` recurs, for some
  `Ts < Tm < Te`. -/
  | step {Ts Tm Te : ℝ} : Ts < Tm → Tm < Te →
      cTol clk S ψn ψt τ δ Ts Tm → RecTol clk S ψn ψt τ δ Tm Te →
      RecTol clk S ψn ψt τ δ Ts Te

/-- **Satisfaction over a finite interval** `S ⊨[Ts,Te] tc(ψn,ψt,τ,δ)`
(Def 4, satisfaction paragraph): `rec-tol[Ts,Te](S,…)`. -/
def Sat (clk : V) (S : Set (State V)) (ψn ψt : Formula V) (τ δ : ℝ)
    (Ts Te : ℝ) : Prop :=
  RecTol clk S ψn ψt τ δ Ts Te

/-- **Satisfaction over `[Ts, ∞)`** `S ⊨[Ts,∞) tc(ψn,ψt,τ,δ)`, the form used in
Theorem 1's `⊨[0,∞)`.

NOTE: `rec-tol` (Def 4) is a *finite* chain over a finite `[Ts,Te]`; the paper
writes the conclusion over the unbounded interval `[0,∞)`. We model `[Ts,∞)` as
an **unbounded, strictly increasing chain of cycles** `Ts = T₀ < T₁ < T₂ < …`
(each `[Tₙ,Tₙ₊₁]` a `c-tol` cycle, boundaries unbounded above) — i.e. recurring
tolerance that never stops. Flagged for review: this is the natural
`ω`-extension of Def 4 to `[0,∞)` but is a modelling choice the paper leaves
implicit. -/
def SatInf (clk : V) (S : Set (State V)) (ψn ψt : Formula V) (τ δ : ℝ)
    (Ts : ℝ) : Prop :=
  ∃ T : ℕ → ℝ, T 0 = Ts ∧ StrictMono T ∧ ¬ BddAbove (Set.range T) ∧
    ∀ n, cTol clk S ψn ψt τ δ (T n) (T (n + 1))

end DLTol
