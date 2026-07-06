/-
Copyright (c) 2026 dL-tolcontract contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-tolcontract contributors
-/
import DLTolContract.Governance

/-!
# Corrected contract governance and Theorem 1 (intended reading)

Findings F1/F2 (`Governance.lean`, `Findings.lean`) show the literally-transcribed
`tc-hp` (ending `_tc := true ; _tc := false`) makes Theorem 1 vacuous-or-false.
Here we mechanize the **intended** construction and its guarantees:

* **Marker fix.** `tc-hp` ends `_tc := true` only (`tcHPfixed`); the reset
  `_tc := false` moves to the head of `sensing` (`sensingReset`).
* **Observation point.** The contract governs the states reached *right after*
  `tc-hp` in each iteration, `acceptedSet = spSet Φ0 ((body)* ; sensing ; tc-hp)`,
  not the post-`plant` loop boundaries `⟨α*_c⟩` exposes.

This file proves the *local* content that F2 was missing — every accepted state
is contract-classified (`tcHPfixed_classifies`) and marked (`tcHPfixed_marks`) —
and isolates the load-bearing initial values `tcd = −δ` and `tab = 0`
(`abnormalStart_*`, `abnormalContinue_*`).
-/

namespace DLTol

open DL

variable {V : Type*}

/-! ## The corrected construction -/

/-- The two-case choice at the heart of `tc-hp` (shared by literal and fixed). -/
def tcCore (S : Scheme V) (ψn ψt : Formula V) (τ δ : ℝ) : Program V :=
  .choice
    (.seq (.test ψn) (.choice (normalContinue S) (normalStart S)))
    (.seq (.test (.and (.neg ψn) ψt)) (.choice (abnormalStart S δ) (abnormalContinue S τ)))

/-- **Marker-fixed `tc-hp`**: the core, then `_tc := true` only. -/
def tcHPfixed (S : Scheme V) (ψn ψt : Formula V) (τ δ : ℝ) : Program V :=
  .seq (tcCore S ψn ψt τ δ) (setTrue S.tcAcc)

/-- Sensing with the acceptance marker reset at the head of the cycle. -/
def sensingReset (S : Scheme V) (sensing : Program V) : Program V :=
  .seq (setFalse S.tcAcc) sensing

/-- One control cycle of the corrected contracted CPS. -/
def bodyFixed (S : Scheme V) (sensing ctrlLogic plant : Program V)
    (ψn ψt : Formula V) (τ δ : ℝ) : Program V :=
  .seq (sensingReset S sensing) (.seq (tcHPfixed S ψn ψt τ δ) (.seq ctrlLogic plant))

/-- The corrected contracted CPS `α*_c`. -/
def cCPSfixed (S : Scheme V) (sensing ctrlLogic plant : Program V)
    (ψn ψt : Formula V) (τ δ : ℝ) : Program V :=
  .star (bodyFixed S sensing ctrlLogic plant ψn ψt τ δ)

/-- **Accepted-estimate set**: states reachable right after `tc-hp` in some
iteration (the object the contract governs, per the paper's intent). -/
def acceptedSet (S : Scheme V) (sensing ctrlLogic plant : Program V)
    (ψn ψt : Formula V) (τ δ : ℝ) (φpre : Formula V) : Set (State V) :=
  spSet φpre
    (.seq (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ)
      (.seq (sensingReset S sensing) (tcHPfixed S ψn ψt τ δ)))

/-! ## The distinguished (fresh) variables as a plain set -/

/-- `BV(tc-hp) = {cd, tab, tcd, _tc}`. -/
def freshVars (S : Scheme V) : Set V := {S.cd, S.tab, S.tcd, S.tcAcc}

/-- The bound variables of `tcHPfixed` are contained in `{cd, tab, tcd, _tc}`. -/
theorem bv_tcHPfixed_subset (S : Scheme V) (ψn ψt : Formula V) (τ δ : ℝ) :
    (tcHPfixed S ψn ψt τ δ).bv ⊆ freshVars S := by
  simp only [tcHPfixed, tcCore, normalContinue, normalStart, abnormalStart,
    abnormalContinue, setTrue, setFalse, freshVars, Program.bv]
  intro x hx
  simp only [Set.mem_union, Set.mem_empty_iff_false, Set.mem_singleton_iff, false_or,
    or_false] at hx ⊢
  tauto

/-! ## Per-estimate soundness (the local core F2 was missing)

Under Def-5 freshness — `Var(ψn) ∪ Var(ψt)` disjoint from `{cd,tab,tcd,_tc}` —
`tc-hp` only accepts an estimate through one of its two guarded cases, and the
subsequent auxiliary-variable writes cannot change `ψn`/`ψt`. Hence every
accepted state is contract-classified. -/

/-- A run of `tcHPfixed` changes only the fresh variables. -/
theorem tcHPfixed_frame (S : Scheme V) (ψn ψt : Formula V) (τ δ : ℝ)
    {ν ω : State V} (h : Program.sem (tcHPfixed S ψn ψt τ δ) ν ω) :
    ∀ x, x ∉ freshVars S → ν x = ω x :=
  fun x hx => Program.bound_effect _ h x (fun hxbv => hx (bv_tcHPfixed_subset S ψn ψt τ δ hxbv))

/-- **Acceptance is contract-classified.** If `Var(ψn) ∪ Var(ψt)` avoids the fresh
variables, then any state accepted by `tcHPfixed` satisfies the normal condition
`ψn`, or is a tolerable abnormality `¬ψn ∧ ψt`. -/
theorem tcHPfixed_classifies (S : Scheme V) (ψn ψt : Formula V) (τ δ : ℝ)
    (hn : Formula.fv ψn ⊆ (freshVars S)ᶜ) (ht : Formula.fv ψt ⊆ (freshVars S)ᶜ)
    {ν ω : State V} (h : Program.sem (tcHPfixed S ψn ψt τ δ) ν ω) :
    Formula.sat ψn ω ∨ (¬ Formula.sat ψn ω ∧ Formula.sat ψt ω) := by
  -- ν and ω agree off the fresh variables
  have hframe : Set.EqOn ν ω (freshVars S)ᶜ :=
    fun x hx => tcHPfixed_frame S ψn ψt τ δ h x hx
  -- split on which case of the core fired
  obtain ⟨μ, hcore, _htrue⟩ := h
  rcases hcore with hnorm | habn
  · -- normal case: ψn held at ν, transported to ω
    obtain ⟨ν1, ⟨rfl, hψn⟩, _⟩ := hnorm
    exact Or.inl ((Formula.coincidence ψn (hframe.mono hn)).mp hψn)
  · -- abnormal case: (¬ψn ∧ ψt) held at ν, transported to ω
    obtain ⟨ν1, ⟨rfl, hnn, hψt⟩, _⟩ := habn
    exact Or.inr ⟨fun hω => hnn ((Formula.coincidence ψn (hframe.mono hn)).mpr hω),
      (Formula.coincidence ψt (hframe.mono ht)).mp hψt⟩

/-- **Acceptance sets the marker.** Every state accepted by `tcHPfixed` has
`_tc = 1` (true) — so `⇓s` retains exactly the accepted states (contrast F1). -/
theorem tcHPfixed_marks (S : Scheme V) (ψn ψt : Formula V) (τ δ : ℝ)
    {ν ω : State V} (h : Program.sem (tcHPfixed S ψn ψt τ δ) ν ω) :
    ω S.tcAcc = 1 := by
  obtain ⟨_μ, _hcore, htrue⟩ := h
  exact htrue.1

/-! ## Isolating the load-bearing initial values `tcd = −δ` and `tab = 0`

Theorem 1's precondition fixes `tab = 0` and `tcd = −δ` "to ensure all branches
of `tc-hp` are reachable even at `tc = 0`." We test that claim at the branch
guards directly. The exact condition for each abnormal branch to be *enabled* at
`tc = 0` is:

* `abnormalStart` (guard `?(tc − tcd ≥ δ)`): enabled  ⟺  `tcd ≤ −δ`.
* `abnormalContinue` (guard `?(tc − tab ≤ τ)`): enabled  ⟺  `tab ≥ −τ`.

So `tcd = −δ` is **tight** (the *largest* admissible initial `tcd`; any larger
kills the branch — `abnormalStart_blocked`), whereas `tab = 0` is merely
**sufficient**: the real requirement is `tab ≥ −τ`, and since `τ > 0` many other
values (including the natural `tab = 0`) work. The paper's `tab = 0` is therefore
stronger than branch-reachability needs. -/

/-- **`abnormalStart` enabled ⇐ `tcd ≤ −δ`** at `tc = 0`. With `tcd = −δ` the
cooldown-length guard `tc − tcd ≥ δ` holds with equality, so the branch fires. -/
theorem abnormalStart_reachable (S : Scheme V) (δ : ℝ) {ν : State V}
    (hcd : ν S.cd = 1) (hclk : ν S.clk = 0) (htcd : ν S.tcd ≤ -δ)
    (hkc : S.clk ≠ S.cd) (htc : S.tcd ≠ S.cd) :
    ∃ ω, Program.sem (abnormalStart S δ) ν ω := by
  classical
  refine ⟨Function.update (Function.update ν S.cd 0) S.tab ((Function.update ν S.cd 0) S.clk),
    ν, ⟨rfl, by simpa [bTrue, Formula.sat, Term.eval, CompOp.interp] using hcd⟩,
    Function.update ν S.cd 0,
    ⟨by simp [Term.eval], fun y hy => Function.update_of_ne hy _ _⟩,
    Function.update ν S.cd 0, ⟨rfl, ?_⟩,
    Function.update_self _ _ _, fun y hy => Function.update_of_ne hy _ _⟩
  -- guard tc − tcd ≥ δ at μ2 = update ν cd 0: reads clk, tcd (both ≠ cd)
  have hc : (Function.update ν S.cd 0) S.clk = 0 := by rw [Function.update_of_ne hkc, hclk]
  have ht : (Function.update ν S.cd 0) S.tcd = ν S.tcd := Function.update_of_ne htc _ _
  simp only [Formula.sat, Term.eval, CompOp.interp, AOp.interp, hc, ht]
  linarith

/-- **`abnormalStart` blocked ⇐ `tcd > −δ`** at `tc = 0`: the guard `tc−tcd ≥ δ`
becomes `0 − tcd ≥ δ`, i.e. `tcd ≤ −δ`, which fails. Countermodel to any initial
`tcd` strictly above `−δ` (e.g. the natural but wrong `tcd = 0` with `δ > 0`). -/
theorem abnormalStart_blocked (S : Scheme V) (δ : ℝ) {ν : State V}
    (hclk : ν S.clk = 0) (htcd : -δ < ν S.tcd)
    (hkc : S.clk ≠ S.cd) (htc : S.tcd ≠ S.cd) :
    ¬ ∃ ω, Program.sem (abnormalStart S δ) ν ω := by
  rintro ⟨ω, _μ, ⟨rfl, -⟩, μ2, hA2, _μ3, ⟨rfl, hguard⟩, -⟩
  -- μ2 = ν off cd; read clk and tcd through it
  have hclk2 : μ2 S.clk = 0 := by rw [hA2.2 S.clk hkc, hclk]
  have htcd2 : μ2 S.tcd = ν S.tcd := hA2.2 S.tcd htc
  simp only [Formula.sat, Term.eval, CompOp.interp, AOp.interp, hclk2, htcd2] at hguard
  linarith

/-- **`abnormalContinue` enabled ⇐ `tab ≥ −τ`** at `tc = 0`. Both statements are
tests (no writes), so no freshness/distinctness is needed. `tab = 0` is one such
value (using `τ > 0`), but any `tab ≥ −τ` works. -/
theorem abnormalContinue_reachable (S : Scheme V) (τ : ℝ) {ν : State V}
    (hcd : ν S.cd ≠ 1) (hclk : ν S.clk = 0) (htab : -τ ≤ ν S.tab) :
    ∃ ω, Program.sem (abnormalContinue S τ) ν ω := by
  refine ⟨ν, ν, ⟨rfl, ?_⟩, rfl, ?_⟩
  · -- test ?¬cd : ¬(ν cd = 1)
    simpa [bFalse, bTrue, Formula.sat, Term.eval, CompOp.interp] using hcd
  · -- guard tc − tab ≤ τ : 0 − tab ≤ τ
    simp only [Formula.sat, Term.eval, CompOp.interp, AOp.interp, hclk]
    linarith

/-- **`abnormalContinue` blocked ⇐ `tab < −τ`** at `tc = 0`: the guard
`tc − tab ≤ τ` becomes `0 − tab ≤ τ`, i.e. `tab ≥ −τ`, which fails. -/
theorem abnormalContinue_blocked (S : Scheme V) (τ : ℝ) {ν : State V}
    (hclk : ν S.clk = 0) (htab : ν S.tab < -τ) :
    ¬ ∃ ω, Program.sem (abnormalContinue S τ) ν ω := by
  rintro ⟨ω, _μ, ⟨rfl, -⟩, rfl, hguard⟩
  simp only [Formula.sat, Term.eval, CompOp.interp, AOp.interp, hclk] at hguard
  linarith

/-! ## Non-vacuity: the corrected Theorem 1's conclusion is satisfiable

Mirroring the family's witness discipline (`timed_witness_fires`), we exhibit a
genuine unbounded recurring pattern satisfying `SatInf`, so the corrected
conclusion `⊨[0,∞)` is not vacuous. Every estimate is normal (`ψn ≡ x_s ≤ 0`),
`ψt ≡ ⊤`; cycle boundaries are spaced `M = δ + τ + 3` apart, and inside each
cycle the required abnormal window has length exactly `τ` and the cooldown length
`δ + 2 ≥ δ`. -/

/-- `ψn ≡ x_s ≤ 0` on sensor variable `5`; timestamp is variable `0`. -/
def ψnW : Formula ℕ := .cmp .le (.var 5) (.const 0)

/-- **Non-vacuity of the corrected Theorem 1.** For any `τ, δ > 0`, the all-normal
estimate set `{ω | x_s ≤ 0}` recurringly tolerates over `[0,∞)`. -/
theorem satInf_witness (τ δ : ℝ) (hτ : 0 < τ) (hδ : 0 < δ) :
    SatInf 0 {ω : State ℕ | ω 5 ≤ 0} ψnW .tt τ δ 0 := by
  set M : ℝ := δ + τ + 3 with hM
  have hMpos : 0 < M := by rw [hM]; linarith
  refine ⟨fun k => (k : ℝ) * M, by simp, ?_, ?_, ?_⟩
  · -- StrictMono
    intro a b hab
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hab) hMpos
  · -- unbounded above
    rw [not_bddAbove_iff]
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (x / M)
    exact ⟨(n : ℝ) * M, ⟨n, rfl⟩, (div_lt_iff₀ hMpos).mp hn⟩
  · -- each [nM, (n+1)M] is a c-tol cycle
    intro n
    have hTe : ((n + 1 : ℕ) : ℝ) * M = (n : ℝ) * M + M := by push_cast; ring
    refine ⟨(n : ℝ) * M + 1, (n : ℝ) * M + 1 + τ, by linarith, by linarith,
      by simp only [hTe]; linarith,
      fun ω hω _ _ => hω, ⟨fun ω _ _ _ => trivial, by linarith⟩,
      ⟨fun ω hω _ _ => hω, by simp only [hTe]; linarith⟩⟩

end DLTol
