/-
Copyright (c) 2026 dL-tolcontract contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-tolcontract contributors
-/
import DLTolContract.Theorem2Reduction
import DLTolContract.Theorem2Quant

/-!
# Theorem 2 — the recurring→single-cycle loop induction (`hClassify`)

This discharges the phase-decomposition premise `hClassify` of
`theorem2_reduction`/`theorem2_reduction_quant` by **boundary-granular** loop
induction over `α*c = (bodyFixed)*` — the faithful formulation, since Theorem 2's
conclusion `T-safe^[0,∞)` is a Q-safety statement over the loop's
strongest-postcondition (boundary-reachable states); the mid-body abnormality
starts are proof-internal (`Lemma1.lean`).

`Phase ν` is the loop invariant: every boundary state is normal (`ϕinv`) or lies
within an abnormality window opened by an abnormality start `ωm` that itself
satisfies `ϕinv` and is within `tm` in time. The single-cycle phase transitions
are premises:

* `hInit` — `ϕinit ∧ ϕpre → ϕinv` (Item 3, initialisation).
* `hNormalStep` — from a normal boundary, one cycle stays normal or opens a new
  abnormality window whose start satisfies `ϕinv`. **This is where Item 3 and the
  onset condition enter** (`ϕinv` must survive the sensor-havoc onset — carried
  explicitly here, since Item 3 covers only normal cycles).
* `hRecovery` — from an in-window abnormality state, one cycle stays in-window or
  recovers to `ϕinv`. **This is where Items 5/6 enter** (the `ε`-connecting-state
  recovery; the timing `τ ≤ tm ≤ δ−ε` lives inside this premise).

The loop lift itself — the "unbounded recurring cycles reduce to a single cycle"
core — is proved here; the two step premises are the single-cycle obligations the
paper reuses from timed Q-safety ([80], Items 4/5). `#print axioms`-clean.
-/

namespace DLTol

open DL

variable {V : Type*}

/-- Boundary-granular phase invariant: normal (`ϕinv`), or in an abnormality
window opened by a `ϕinv`-satisfying abnormality start `ωm`, within `tm`. -/
def Phase {S : Scheme V} (αc : Program V) (ϕinv : Formula V) (tm : ℝ) (ν : State V) : Prop :=
  Formula.sat ϕinv ν ∨
    (∃ ωm, ωm S.cd = 0 ∧ ωm S.tab = ωm S.clk ∧ Formula.sat ϕinv ωm ∧
      Program.sem αc ωm ν ∧ ν S.clk - ωm S.clk ≤ tm)

/-- **The recurring→single-cycle loop induction.** From the single-cycle phase
transitions, `Phase` holds at every boundary reachable from an initial state. -/
theorem phase_invariant {S : Scheme V}
    {sensing ctrlLogic plant : Program V} {ψn ψt : Formula V} {τ δ : ℝ}
    {ϕinit ϕpre ϕinv : Formula V} {tm : ℝ}
    (hInit : ∀ ω, Formula.sat ϕinit ω → Formula.sat ϕpre ω → Formula.sat ϕinv ω)
    (hNormalStep : ∀ μ ν', Formula.sat ϕinv μ →
        Program.sem (bodyFixed S sensing ctrlLogic plant ψn ψt τ δ) μ ν' →
        Phase (S := S) (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ϕinv tm ν')
    (hRecovery : ∀ ωm μ ν', ωm S.cd = 0 → ωm S.tab = ωm S.clk → Formula.sat ϕinv ωm →
        Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ωm μ →
        μ S.clk - ωm S.clk ≤ tm →
        Program.sem (bodyFixed S sensing ctrlLogic plant ψn ψt τ δ) μ ν' →
        Phase (S := S) (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ϕinv tm ν')
    {ω ν : State V}
    (hinit : Formula.sat ϕinit ω) (hpre : Formula.sat ϕpre ω)
    (hrun : Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω ν) :
    Phase (S := S) (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ϕinv tm ν := by
  have h0 : Phase (S := S) (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ϕinv tm ω :=
    Or.inl (hInit ω hinit hpre)
  have hrun' : Relation.ReflTransGen
      (Program.sem (bodyFixed S sensing ctrlLogic plant ψn ψt τ δ)) ω ν := hrun
  clear hrun
  induction hrun' with
  | refl => exact h0
  | tail _ hlast ih =>
      rcases ih with hnorm | ⟨ωm, hcd, htab, hinvm, hreach, hwin⟩
      · exact hNormalStep _ _ hnorm hlast
      · exact hRecovery ωm _ _ hcd htab hinvm hreach hwin hlast

/-- **`hClassify` discharged.** `Phase` implies the phase decomposition
`theorem2_reduction`/`theorem2_reduction_quant` consume (dropping the window
bound). So the loop-induction premises above discharge that premise, reducing
Theorem 2 to the single-cycle phase obligations. -/
theorem hClassify_of_phase {S : Scheme V}
    {sensing ctrlLogic plant : Program V} {ψn ψt : Formula V} {τ δ : ℝ}
    {ϕinit ϕpre ϕinv : Formula V} {tm : ℝ}
    (hInit : ∀ ω, Formula.sat ϕinit ω → Formula.sat ϕpre ω → Formula.sat ϕinv ω)
    (hNormalStep : ∀ μ ν', Formula.sat ϕinv μ →
        Program.sem (bodyFixed S sensing ctrlLogic plant ψn ψt τ δ) μ ν' →
        Phase (S := S) (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ϕinv tm ν')
    (hRecovery : ∀ ωm μ ν', ωm S.cd = 0 → ωm S.tab = ωm S.clk → Formula.sat ϕinv ωm →
        Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ωm μ →
        μ S.clk - ωm S.clk ≤ tm →
        Program.sem (bodyFixed S sensing ctrlLogic plant ψn ψt τ δ) μ ν' →
        Phase (S := S) (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ϕinv tm ν') :
    ∀ ω ν, Formula.sat ϕinit ω → Formula.sat ϕpre ω →
      Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω ν →
      Formula.sat ϕinv ν ∨
        (∃ ωm, ωm S.cd = 0 ∧ ωm S.tab = ωm S.clk ∧ Formula.sat ϕinv ωm ∧
          Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ωm ν) := by
  intro ω ν hinit hpre hrun
  rcases phase_invariant hInit hNormalStep hRecovery hinit hpre hrun with
    hnorm | ⟨ωm, hcd, htab, hinvm, hreach, _hwin⟩
  · exact Or.inl hnorm
  · exact Or.inr ⟨ωm, hcd, htab, hinvm, hreach⟩

/-- **Theorem 2 (quantitative), reduced to single-cycle obligations.** Composing
the loop induction (`hClassify_of_phase`) with the quantitative reduction
(`theorem2_reduction_quant`): every state reachable by the contracted CPS has
Q-safety margin `≥ min(u,u₁)` — the paper's `T-safe^[0,∞)_{u₂}`, `u₂ ≥ min(u,u₁)`.

Everything unbounded/recurring is discharged. What remains are exactly the
**single-cycle** premises the paper reuses from timed Q-safety (Items 3/4/5, the
onset condition, and Item 6's timing inside `hRecovery`) — none of which mention
the loop. This is the faithful statement of "recurring cycles reduce to a single
canonical cycle." -/
theorem theorem2_quant {V : Type*} [DecidableEq V] {S : Scheme V} (hd : S.Distinct)
    {sensing ctrlLogic plant : Program V} {ψn ψt : Formula V} {τ δ : ℝ}
    (hψn : ∀ (T : ℝ) (s : State V), Formula.sat ψn (shiftBy S T s) ↔ Formula.sat ψn s)
    (hψt : ∀ (T : ℝ) (s : State V), Formula.sat ψt (shiftBy S T s) ↔ Formula.sat ψt s)
    (hsens : Equivariant S sensing) (hctrl : Equivariant S ctrlLogic)
    (hplant : Equivariant S plant)
    {H : Finset V} {ϕpost ϕinv ϕinit ϕpre : Formula V} (D : DLQSafety.Dist H (DLQSafety.sat_set ϕpost))
    {u u₁ tm : ℝ}
    (hDframe : ∀ s s' : State V,
        (∀ x, x ∉ ({S.clk, S.tab, S.tcd} : Set V) → s x = s' x) → D.val s = D.val s')
    (hinvFV : Formula.fv ϕinv ⊆ ({S.clk, S.tab, S.tcd} : Set V)ᶜ)
    (hItem3 : ∀ ν, Formula.sat ϕinv ν → u₁ ≤ D.val ν)
    (hItem4 : ∀ ω' ν', ω' S.clk = 0 → ω' S.tab = 0 → ω' S.cd = 0 → Formula.sat ϕinv ω' →
        Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω' ν' → u ≤ D.val ν')
    (hInit : ∀ ω, Formula.sat ϕinit ω → Formula.sat ϕpre ω → Formula.sat ϕinv ω)
    (hNormalStep : ∀ μ ν', Formula.sat ϕinv μ →
        Program.sem (bodyFixed S sensing ctrlLogic plant ψn ψt τ δ) μ ν' →
        Phase (S := S) (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ϕinv tm ν')
    (hRecovery : ∀ ωm μ ν', ωm S.cd = 0 → ωm S.tab = ωm S.clk → Formula.sat ϕinv ωm →
        Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ωm μ →
        μ S.clk - ωm S.clk ≤ tm →
        Program.sem (bodyFixed S sensing ctrlLogic plant ψn ψt τ δ) μ ν' →
        Phase (S := S) (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ϕinv tm ν') :
    ∀ ω ν, Formula.sat ϕinit ω → Formula.sat ϕpre ω →
      Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω ν →
      min u u₁ ≤ D.val ν :=
  theorem2_reduction_quant hd hψn hψt hsens hctrl hplant D hDframe hinvFV hItem3 hItem4
    (hClassify_of_phase hInit hNormalStep hRecovery)

end DLTol
