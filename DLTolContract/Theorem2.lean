/-
Copyright (c) 2026 dL-tolcontract contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-tolcontract contributors
-/
import DLTolContract.Corrected

/-!
# Theorem 2 (safety via tolerance-cycle invariant) — Lemma 1 audit

Theorem 2 reduces safety over unbounded recurring tolerance cycles to safety over
a single canonical cycle, via **Lemma 1 (time-shift invariance)**: any
abnormality-start state reached at time `T` can be "shifted" to the canonical
start (`tc=0, tab=0, tcd=−δ, cd=false`) by adjusting only `{tc,tab,tcd}`, giving
another execution of `α*_c` that agrees on **all** other variables. The paper
justifies it as "the two transition pairs differ only in timing variables, which
do not affect controller or plant behavior after contract acceptance."

## `tc`-purity is the load-bearing assumption (tightness witness, not a defect)

Lemma 1's justification is a non-interference claim; `tc`-purity is the paper's
intended assumption. The witness below shows it is genuinely load-bearing. Split
by variable:

* `tab`, `tcd` are **fresh** (Def 5, *stated*): `sensing`/`ctrl_logic`/`plant` do
  not read them; only `tc-hp`'s guards do. The canonical shift preserves the
  *relative* timing the guards test (`tc − tab = 0` at an abnormality start in
  both; `tcd` is dead — overwritten by the next `normalStart` before it is read
  again). So freshness covers `tab, tcd`.
* `tc` is the CPS's **own global clock** — `tc ∈ Var(α)`, **not** fresh. Nothing
  in the paper forbids `ctrl_logic` or `plant` from reading `tc`. If they do, the
  shift (which changes `tc` from `T` to `0`) changes the evolution of non-timing
  variables, and the "agree off `{tc,tab,tcd}`" conclusion fails.

So Lemma 1 requires `tc` to be a *pure clock* — its absolute value not read by
`ctrl_logic`/`plant` into any non-timing variable (the paper's intended reading;
the water tank satisfies it: `ctrl` reads only local clock `tl`, `plant` reads
`tc` only via `tc' = 1`). The mechanization (`Lemma1.lean`) carries this as the
explicit component-equivariance hypotheses. Same clock-variable shape as the
CSF'25 `tg`-monotonicity assumption.

The witness below shows the assumption is load-bearing (a **tightness**
demonstration, not a refutation of the paper): a **well-formed** contracted CPS
whose `ctrl_logic` reads `tc` (`z := tc`, `z` non-timing). An abnormality-start
execution sets `z := 5`; every execution from the canonical shift has `z = 0`, so
no `ν'` can agree on `z`. `#print axioms` clean.
-/

namespace DLTol

open DL

/-- Scheme: `cd=4, tab=1, tcd=2, _tc=3, clk(tc)=0`; the non-timing witness is `z=6`. -/
def Sℓ : Scheme ℕ := { cd := 4, tab := 1, tcd := 2, tcAcc := 3, clk := 0 }

/-- `ctrl_logic ≡ z := tc` — legally reads the global clock into a non-timing
variable `z = 6`. This is what breaks Lemma 1. -/
def ctrlReadsTc : Program ℕ := .assign 6 (.var 0)

/-- The witnessing contracted CPS (corrected construction; `ψn = ψt = ⊤`,
`sensing = plant = ?⊤`, `τ = δ = 1`). -/
def αcℓ : Program ℕ :=
  cCPSfixed Sℓ (.test .tt) ctrlReadsTc (.test .tt) .tt .tt 1 1

/-- One control cycle of the witness. -/
def bodℓ : Program ℕ :=
  bodyFixed Sℓ (.test .tt) ctrlReadsTc (.test .tt) .tt .tt 1 1

/-- `clk = 0` is not a bound variable of `tc-hp`. -/
theorem zero_notin_tcHP : (0 : ℕ) ∉ (tcHPfixed Sℓ .tt .tt 1 1).bv := fun h => by
  have := bv_tcHPfixed_subset Sℓ .tt .tt 1 1 h; simp [freshVars, Sℓ] at this

/-- `clk = 0` is not a bound variable of `sensingReset`. -/
theorem zero_notin_SR : (0 : ℕ) ∉ (sensingReset Sℓ (.test .tt)).bv := by
  simp [sensingReset, setFalse, Program.bv, Sℓ]

/-- `clk = 0` is not a bound variable of one control cycle (`sensing`/`ctrl_logic`
/`plant` do not write `tc`; `tc-hp` writes only the fresh variables). -/
theorem zero_notin_bodℓ : (0 : ℕ) ∉ bodℓ.bv := by
  intro h
  simp only [bodℓ, bodyFixed, Program.bv, Set.mem_union] at h
  rcases h with h | h | h | h
  · exact zero_notin_SR h
  · exact zero_notin_tcHP h
  · simp [ctrlReadsTc, Program.bv] at h
  · simp at h

/-- **`z` is pinned to `0` from any `tc = 0` start.** One cycle sets `z := tc`, and
`tc` is untouched by the cycle, so if `tc = 0` on entry then `z = 0` on exit. -/
theorem bodℓ_forces_z {μ ν : State ℕ} (h : Program.sem bodℓ μ ν) (hclk : μ 0 = 0) :
    ν 6 = 0 := by
  -- bodℓ = sensingReset ; tcHPfixed ; ctrl ; plant
  obtain ⟨a, hSR, b, hTC, c, hCtrl, hPl⟩ := h
  -- clk (0) is untouched by sensingReset and tcHPfixed
  have ha0 : a 0 = 0 := by rw [← Program.bound_effect _ hSR 0 zero_notin_SR, hclk]
  have hb0 : b 0 = 0 := by rw [← Program.bound_effect _ hTC 0 zero_notin_tcHP, ha0]
  -- ctrl sets z (6) := (var clk).eval b = b 0 = 0
  have hc6 : c 6 = 0 := by rw [hCtrl.1]; simpa [Term.eval] using hb0
  -- plant ?⊤ is a no-op
  obtain ⟨rfl, -⟩ := hPl
  exact hc6

/-- **Every state reachable from a `tc=0, z=0` start has `z = 0`.** -/
theorem reachℓ_z_zero {ω ν : State ℕ} (h : Program.sem αcℓ ω ν)
    (hclk : ω 0 = 0) (hz : ω 6 = 0) : ν 6 = 0 := by
  induction h with
  | refl => exact hz
  | @tail μ ν _hpre hlast _ih =>
      -- clk stays 0 along the whole prefix (clk ∉ BV(bodℓ) = BV(bodℓ*))
      have hμ0 : μ 0 = 0 := by
        rw [← Program.bound_effect (.star bodℓ) _hpre 0 zero_notin_bodℓ, hclk]
      exact bodℓ_forces_z hlast hμ0

/-! ## The countermodel to Lemma 1 (as stated) -/

/-- Abnormality-start state at time `5`: `cd=false, tab=tc=5, _tc=true`, `z=0`. -/
def ωℓ : State ℕ := fun k => if k = 0 then 5 else if k = 1 then 5 else if k = 3 then 1 else 0

/-- The state after one control cycle from `ωℓ`; the cooldown starts (`cd:=1`,
`tcd:=tc=5`), the marker is set (`_tc:=1`), and crucially `z := tc = 5`. -/
def νℓ : State ℕ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update ωℓ Sℓ.tcAcc 0) Sℓ.cd 1) Sℓ.tcd 5) Sℓ.tcAcc 1) 6 5

/-- `νℓ` really is reached in one control cycle from `ωℓ` (normal estimate,
cooldown-starts branch of `tc-hp`). -/
theorem sem_ωℓ_νℓ : Program.sem bodℓ ωℓ νℓ := by
  classical
  -- intermediate states along the cycle
  set a := Function.update ωℓ Sℓ.tcAcc 0 with ha
  set b1 := Function.update a Sℓ.cd 1 with hb1
  set bp := Function.update b1 Sℓ.tcd 5 with hbp
  set b := Function.update bp Sℓ.tcAcc 1 with hb
  refine ⟨a, ⟨a, ⟨by simp [Term.eval, ha], fun y hy => Function.update_of_ne hy _ _⟩,
      rfl, trivial⟩, ?_⟩
  refine ⟨b, ⟨bp, Or.inl ⟨a, ⟨rfl, trivial⟩,
      Or.inr ⟨a, ⟨rfl, ?_⟩, b1,
        ⟨by simp [Term.eval, hb1], fun y hy => Function.update_of_ne hy _ _⟩,
        ⟨by simp [Term.eval, hbp, hb1, ha, Sℓ, ωℓ], fun y hy => Function.update_of_ne hy _ _⟩⟩⟩,
      ⟨by simp [Term.eval, hb], fun y hy => Function.update_of_ne hy _ _⟩⟩, ?_⟩
  · -- ?¬cd at a: cd = 4, value 0 ≠ 1
    simp [bFalse, bTrue, Formula.sat, Term.eval, CompOp.interp, ha, Sℓ, ωℓ]
  · -- ctrl (z := tc) ; plant ?⊤
    refine ⟨νℓ, ⟨?_, ?_⟩, rfl, trivial⟩
    · -- ctrl: z (6) := (var clk).eval b = b 0 = 5
      simp [νℓ, Term.eval, hb, hbp, hb1, ha, Sℓ, ωℓ]
    · intro y hy; exact Function.update_of_ne hy _ _

/-- **Tightness of the `tc`-purity assumption (mechanized).** For this well-formed
contracted CPS whose `ctrl_logic` reads the global clock (`z := tc`), there is an
abnormality-start execution `(ωℓ, νℓ)` with `νℓ(z) = 5`, yet **no** canonical
time-shift `(ω', ν')` can agree with it on the non-timing variable `z`: every
execution from a `tc = 0` canonical start pins `z = 0`. Hence Lemma 1 genuinely
needs `tc`-purity — dropping it breaks the lemma. -/
theorem lemma1_countermodel :
    ∃ ω ν : State ℕ,
      Program.sem αcℓ ω ν ∧
      -- ω is an abnormality-start state (Lemma 1's hypothesis)
      ω Sℓ.cd = 0 ∧ ω Sℓ.tab = ω Sℓ.clk ∧ ω Sℓ.tcAcc = 1 ∧
      -- but no canonical shift preserves the non-timing variables
      ∀ ω' ν' : State ℕ,
        Program.sem αcℓ ω' ν' →
        (∀ x, x ∉ ({Sℓ.clk, Sℓ.tab, Sℓ.tcd} : Set ℕ) → ω' x = ω x) →
        (∀ x, x ∉ ({Sℓ.clk, Sℓ.tab, Sℓ.tcd} : Set ℕ) → ν' x = ν x) →
        ω' Sℓ.clk = 0 ∧ ω' Sℓ.tab = 0 ∧ ω' Sℓ.tcd = -1 ∧ ω' Sℓ.cd = 0 →
        False := by
  refine ⟨ωℓ, νℓ, Relation.ReflTransGen.single sem_ωℓ_νℓ, rfl, rfl, rfl, ?_⟩
  rintro ω' ν' hsem' hagω hagν ⟨hclk', -, -, -⟩
  have h6notin : (6 : ℕ) ∉ ({Sℓ.clk, Sℓ.tab, Sℓ.tcd} : Set ℕ) := by simp [Sℓ]
  -- ω'(z) = ω(z) = 0, so every reachable ν'(z) = 0
  have hω'6 : ω' 6 = 0 := by rw [hagω 6 h6notin]; simp [ωℓ]
  have hν'6 : ν' 6 = 0 := reachℓ_z_zero hsem' hclk' hω'6
  -- but ν'(z) must equal νℓ(z) = 5
  have : (0 : ℝ) = 5 := by rw [← hν'6, hagν 6 h6notin]; simp [νℓ]
  norm_num at this

end DLTol
