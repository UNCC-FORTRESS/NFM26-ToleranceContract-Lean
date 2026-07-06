/-
Copyright (c) 2026 dL-tolcontract contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-tolcontract contributors
-/
import DLTolContract.Lemma1

/-!
# Theorem 2 — the tolerance-cycle reduction (structure)

Theorem 2 reduces safety over unbounded recurring cycles to safety over a single
canonical cycle. Per the audit plan we mechanize the **reduction structure** —
the step where the corrected Lemma 1 (`lemma1`) realigns an abnormality start at
an arbitrary time to the canonical cycle — and leave the timed-Q-safety GLB
computation (Items 4/5, dischargeable from dL-caltiming's `TSafe`) as explicit
premises.

**Abstraction.** `Safe P pre post` — "every state reachable by `P` from `pre`
satisfies `post`" — is the Boolean shadow of the paper's `T-safe^[0,∞)_u` with
`u ≥ 0⁺` (non-negative Q-safety margin ⟺ `post` holds on the reachable set;
the paper itself leaves the exact `u₂` uncharacterized). Over the full run it
matches dL-caltiming's `TSafe D u P φpre tg 0 ∞` at `u ≥ 0⁺`.

The genuinely-new content — how Lemma 1 makes the reduction go through — is
`abnormality_phase_safe`, proved below. `ϕinv`/`ϕpost` are physical (no timing
variables), so agreement off `{tc,tab,tcd}` transfers their truth via the
frame/coincidence lemma.
-/

namespace DLTol

open DL Set

variable {V : Type*} [DecidableEq V]

/-- Boolean safety shadow of `T-safe^[0,∞)_u` (`u ≥ 0⁺`): every state reachable
by `P` from `pre` satisfies `post`. -/
def Safe (P : Program V) (pre post : Formula V) : Prop :=
  ∀ ω ν, Formula.sat pre ω → Program.sem P ω ν → Formula.sat post ν

/-- **The Lemma-1 realignment (heart of Theorem 2's reduction).**

An abnormality-phase state `ν`, reached from an abnormality start `ωm` (`cd=false`,
`tab=tc`) that satisfies the invariant `ϕinv`, is `ϕpost`-safe — *because* Lemma 1
shifts `(ωm, ν)` to a canonical counterpart `(ω', ν')` (same execution relation,
agreeing on non-timing variables, `tc=0 ∧ tab=0 ∧ cd=false`), the canonical
execution is safe by Item 4, and `ϕinv`/`ϕpost` — being physical (no timing
variables) — transfer across the shift by coincidence.

Item 4 (`hItem4`) is the premise dischargeable from dL-caltiming's `TSafe`. -/
theorem abnormality_phase_safe {S : Scheme V} (hd : S.Distinct)
    {sensing ctrlLogic plant : Program V} {ψn ψt : Formula V} {τ δ : ℝ}
    (hψn : ∀ (T : ℝ) (s : State V), Formula.sat ψn (shiftBy S T s) ↔ Formula.sat ψn s)
    (hψt : ∀ (T : ℝ) (s : State V), Formula.sat ψt (shiftBy S T s) ↔ Formula.sat ψt s)
    (hsens : Equivariant S sensing) (hctrl : Equivariant S ctrlLogic)
    (hplant : Equivariant S plant)
    {ϕinv ϕpost : Formula V}
    -- ϕinv, ϕpost are physical: they mention no timing variable
    (hinvFV : Formula.fv ϕinv ⊆ ({S.clk, S.tab, S.tcd} : Set V)ᶜ)
    (hpostFV : Formula.fv ϕpost ⊆ ({S.clk, S.tab, S.tcd} : Set V)ᶜ)
    -- Item 4 (shadow): canonical abnormality-start executions are ϕpost-safe
    (hItem4 : ∀ ω' ν', ω' S.clk = 0 → ω' S.tab = 0 → ω' S.cd = 0 → Formula.sat ϕinv ω' →
        Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω' ν' →
        Formula.sat ϕpost ν')
    {ωm ν : State V}
    (hcd : ωm S.cd = 0) (htab : ωm S.tab = ωm S.clk) (hinv : Formula.sat ϕinv ωm)
    (hrun : Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ωm ν) :
    Formula.sat ϕpost ν := by
  -- realign the abnormality start to the canonical cycle
  obtain ⟨ω', ν', hrun', hagree, hclk', htab', hcd'⟩ :=
    lemma1 hd hψn hψt hsens hctrl hplant hrun hcd htab
  -- ϕinv transfers ωm → ω' (physical invariant, agreement off timing)
  have hinv' : Formula.sat ϕinv ω' :=
    (Formula.coincidence ϕinv (fun x hx => (hagree x (hinvFV hx)).1.symm)).mp hinv
  -- Item 4 on the canonical execution
  have hpost' : Formula.sat ϕpost ν' := hItem4 ω' ν' hclk' htab' hcd' hinv' hrun'
  -- ϕpost transfers ν' → ν
  exact (Formula.coincidence ϕpost (fun x hx => (hagree x (hpostFV hx)).2.symm)).mpr hpost'

/-- **Theorem 2 (reduction).** Every reachable state is `ϕpost`-safe, by splitting
into the two phases the abnormality-duration induction produces:

* **normal phase** (`ν ⊨ ϕinv`) — safe by Item 3's control-cycle invariant
  `ϕinv → ϕpost`;
* **abnormality phase** (`ν` reachable from an abnormality start `ωm ⊨ ϕinv`) —
  safe by `abnormality_phase_safe`, i.e. Lemma 1 realigns `ωm` to the canonical
  cycle and Item 4 applies.

`hClassify` is the phase-decomposition premise — the remaining Q-safety glue
(Items 5/6, the connecting-state / recovery argument, deferred). The Lemma-1
content is fully discharged in the abnormality branch. -/
theorem theorem2_reduction {S : Scheme V} (hd : S.Distinct)
    {sensing ctrlLogic plant : Program V} {ψn ψt : Formula V} {τ δ : ℝ}
    (hψn : ∀ (T : ℝ) (s : State V), Formula.sat ψn (shiftBy S T s) ↔ Formula.sat ψn s)
    (hψt : ∀ (T : ℝ) (s : State V), Formula.sat ψt (shiftBy S T s) ↔ Formula.sat ψt s)
    (hsens : Equivariant S sensing) (hctrl : Equivariant S ctrlLogic)
    (hplant : Equivariant S plant)
    {ϕinit ϕpre ϕinv ϕpost : Formula V}
    (hinvFV : Formula.fv ϕinv ⊆ ({S.clk, S.tab, S.tcd} : Set V)ᶜ)
    (hpostFV : Formula.fv ϕpost ⊆ ({S.clk, S.tab, S.tcd} : Set V)ᶜ)
    -- Item 3: the control-cycle invariant implies the safety postcondition
    (hItem3 : ∀ ν, Formula.sat ϕinv ν → Formula.sat ϕpost ν)
    -- Item 4 (shadow): canonical abnormality-start executions are ϕpost-safe
    (hItem4 : ∀ ω' ν', ω' S.clk = 0 → ω' S.tab = 0 → ω' S.cd = 0 → Formula.sat ϕinv ω' →
        Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω' ν' →
        Formula.sat ϕpost ν')
    -- phase decomposition (Items 5/6 glue): every reachable state is normal, or
    -- reachable from an abnormality start satisfying ϕinv
    (hClassify : ∀ ω ν, Formula.sat ϕinit ω → Formula.sat ϕpre ω →
        Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω ν →
        Formula.sat ϕinv ν ∨
          (∃ ωm, ωm S.cd = 0 ∧ ωm S.tab = ωm S.clk ∧ Formula.sat ϕinv ωm ∧
            Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ωm ν)) :
    Safe (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) (.and ϕinit ϕpre) ϕpost := by
  rintro ω ν ⟨hi, hp⟩ hrun
  rcases hClassify ω ν hi hp hrun with hnorm | ⟨ωm, hcd, htab, hinvm, hrunm⟩
  · -- normal phase: Item 3
    exact hItem3 ν hnorm
  · -- abnormality phase: Lemma 1 realignment + Item 4
    exact abnormality_phase_safe hd hψn hψt hsens hctrl hplant hinvFV hpostFV hItem4
      hcd htab hinvm hrunm

end DLTol
