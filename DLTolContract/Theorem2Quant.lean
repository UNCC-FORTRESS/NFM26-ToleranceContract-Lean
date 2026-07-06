/-
Copyright (c) 2026 dL-tolcontract contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-tolcontract contributors
-/
import DLTolContract.Lemma1
import DLQSafety
import DLCalTiming.TimedSafety

/-!
# Theorem 2 — quantitative reduction (real Q-safety margin)

Upgrades the Boolean `Safe` shadow (`Theorem2Reduction.lean`) to the actual
Q-safety quantity, using dL-qsafety's `Dist` (the signed safety margin). The
paper's conclusion `T-safe^[0,∞)_{u₂}` with `u₂ ≥ min(u,u₁)` is exactly:
*every reachable state has margin `≥ min(u,u₁)`* (a lower bound on the reachable
infimum). We prove that reduction, with the Lemma-1 realignment now carrying the
**margin** across the shift.

`D : Dist H ⟦ϕpost⟧` is dL-qsafety's abstract signed distance. Since `Dist.val`
is an arbitrary function, margin-preservation across the time-shift is not
automatic; it is the hypothesis `hDframe` — `D` depends only on non-timing
variables (`H = Var(ϕpost)` is physical). This holds for the water tank's
`Dist.coordHalfspace` (`val = 40 − xₚ`, `xₚ` physical).

Item 4's timed Q-safety enters as `hItem4` — the per-state margin lower bound
`u ≤ D.val ν'`, which is exactly `IsGLB.1` of dL-caltiming's `TSafe` applied to a
canonical-cycle-reachable state.
-/

namespace DLTol

open DL DLQSafety

variable {V : Type*} [DecidableEq V]

/-- **Item 4/5 discharge from dL-caltiming.** dL-caltiming's timed Q-safety
`TSafe D u P φpre tg Tl Tu` (`= IsGLB (D.val '' spTimed …) u`) delivers exactly the
per-state margin lower bound the reduction consumes: any timed-reachable state has
margin `≥ u`. This is `IsGLB.1` (the lower-bound half) applied to that state — the
concrete link that makes Items 4/5 dischargeable from the CSF'25 mechanization. -/
theorem tsafe_margin_lb {H : Finset V} {ϕpost : Formula V} (D : Dist H (sat_set ϕpost))
    {u : ℝ} {P : Program V} {φpre : Formula V} {tg : V} {Tl Tu : ℝ}
    (h : DLCalTiming.TSafe D u P φpre tg Tl Tu)
    {ν : State V} (hν : ν ∈ DLCalTiming.spTimed φpre P tg Tl Tu) :
    u ≤ D.val ν :=
  h.1 ⟨ν, hν, rfl⟩

/-- **Quantitative Lemma-1 realignment.** An abnormality-phase state `ν` inherits
the canonical cycle's margin: `u ≤ D.val ν`. Proof — `lemma1` shifts `(ωm,ν)` to
canonical `(ω',ν')`; Item 4 gives `u ≤ D.val ν'`; and `D` (physical) is unchanged
by the shift, so `D.val ν = D.val ν'`. -/
theorem abnormality_phase_margin {S : Scheme V} (hd : S.Distinct)
    {sensing ctrlLogic plant : Program V} {ψn ψt : Formula V} {τ δ : ℝ}
    (hψn : ∀ (T : ℝ) (s : State V), Formula.sat ψn (shiftBy S T s) ↔ Formula.sat ψn s)
    (hψt : ∀ (T : ℝ) (s : State V), Formula.sat ψt (shiftBy S T s) ↔ Formula.sat ψt s)
    (hsens : Equivariant S sensing) (hctrl : Equivariant S ctrlLogic)
    (hplant : Equivariant S plant)
    {H : Finset V} {ϕpost ϕinv : Formula V} (D : Dist H (sat_set ϕpost)) {u : ℝ}
    -- `D` depends only on non-timing variables (H = Var(ϕpost) is physical)
    (hDframe : ∀ s s' : State V,
        (∀ x, x ∉ ({S.clk, S.tab, S.tcd} : Set V) → s x = s' x) → D.val s = D.val s')
    (hinvFV : Formula.fv ϕinv ⊆ ({S.clk, S.tab, S.tcd} : Set V)ᶜ)
    -- Item 4 (margin form): canonical executions have margin ≥ u (`IsGLB.1` of `TSafe`)
    (hItem4 : ∀ ω' ν', ω' S.clk = 0 → ω' S.tab = 0 → ω' S.cd = 0 → Formula.sat ϕinv ω' →
        Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω' ν' → u ≤ D.val ν')
    {ωm ν : State V}
    (hcd : ωm S.cd = 0) (htab : ωm S.tab = ωm S.clk) (hinv : Formula.sat ϕinv ωm)
    (hrun : Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ωm ν) :
    u ≤ D.val ν := by
  obtain ⟨ω', ν', hrun', hagree, hclk', htab', hcd'⟩ :=
    lemma1 hd hψn hψt hsens hctrl hplant hrun hcd htab
  have hinv' : Formula.sat ϕinv ω' :=
    (Formula.coincidence ϕinv (fun x hx => (hagree x (hinvFV hx)).1.symm)).mp hinv
  have hmargin : u ≤ D.val ν' := hItem4 ω' ν' hclk' htab' hcd' hinv' hrun'
  have hframe : D.val ν = D.val ν' := hDframe ν ν' (fun x hx => (hagree x hx).2.symm)
  rw [hframe]; exact hmargin

/-- **Theorem 2 (quantitative reduction): `u₂ ≥ min(u,u₁)`-Q-safety.** Every
reachable state has margin `≥ min(u,u₁)`, by the normal/abnormality phase split:
normal states carry the invariant margin `u₁` (Item 3/5), abnormality-phase states
carry the canonical-cycle margin `u` (Lemma 1 + Item 4). This is exactly the
paper's `T-safe^[0,∞)_{u₂}` with `u₂ = min(u,u₁)` as a lower bound on the reachable
Q-safety infimum. The phase decomposition `hClassify` (Items 5/6) remains the
deferred glue. -/
theorem theorem2_reduction_quant {S : Scheme V} (hd : S.Distinct)
    {sensing ctrlLogic plant : Program V} {ψn ψt : Formula V} {τ δ : ℝ}
    (hψn : ∀ (T : ℝ) (s : State V), Formula.sat ψn (shiftBy S T s) ↔ Formula.sat ψn s)
    (hψt : ∀ (T : ℝ) (s : State V), Formula.sat ψt (shiftBy S T s) ↔ Formula.sat ψt s)
    (hsens : Equivariant S sensing) (hctrl : Equivariant S ctrlLogic)
    (hplant : Equivariant S plant)
    {H : Finset V} {ϕpost ϕinv ϕinit ϕpre : Formula V} (D : Dist H (sat_set ϕpost))
    {u u₁ : ℝ}
    (hDframe : ∀ s s' : State V,
        (∀ x, x ∉ ({S.clk, S.tab, S.tcd} : Set V) → s x = s' x) → D.val s = D.val s')
    (hinvFV : Formula.fv ϕinv ⊆ ({S.clk, S.tab, S.tcd} : Set V)ᶜ)
    -- Item 3/5 (margin form): invariant states carry margin ≥ u₁
    (hItem3 : ∀ ν, Formula.sat ϕinv ν → u₁ ≤ D.val ν)
    -- Item 4 (margin form): canonical executions carry margin ≥ u
    (hItem4 : ∀ ω' ν', ω' S.clk = 0 → ω' S.tab = 0 → ω' S.cd = 0 → Formula.sat ϕinv ω' →
        Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω' ν' → u ≤ D.val ν')
    -- phase decomposition (Items 5/6 glue, deferred)
    (hClassify : ∀ ω ν, Formula.sat ϕinit ω → Formula.sat ϕpre ω →
        Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω ν →
        Formula.sat ϕinv ν ∨
          (∃ ωm, ωm S.cd = 0 ∧ ωm S.tab = ωm S.clk ∧ Formula.sat ϕinv ωm ∧
            Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ωm ν)) :
    ∀ ω ν, Formula.sat ϕinit ω → Formula.sat ϕpre ω →
      Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω ν →
      min u u₁ ≤ D.val ν := by
  intro ω ν hi hp hrun
  rcases hClassify ω ν hi hp hrun with hnorm | ⟨ωm, hcd, htab, hinvm, hrunm⟩
  · exact le_trans (min_le_right u u₁) (hItem3 ν hnorm)
  · exact le_trans (min_le_left u u₁)
      (abnormality_phase_margin hd hψn hψt hsens hctrl hplant D hDframe hinvFV hItem4
        hcd htab hinvm hrunm)

end DLTol
