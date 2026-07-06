/-
Copyright (c) 2026 dL-tolcontract contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-tolcontract contributors
-/
import DLTolContract.Governance

/-!
# Finding F2 — a countermodel to Theorem 1 *as literally transcribed*

Finding F1 (`Governance.lean`) showed the `⇓s`-set of a contracted CPS is exactly
the initial `Φ0`-states with `_tc = 1`. Those states all sit at timestamp
`clk = tc = 0` (`Φ0` fixes `tc = 0`). Any recurring-tolerance witness must open
with a normality window `[0, Tas]` (`0 = Ts < Tas`), which forces `ψn` on every
estimate at timestamp `0` — including these initial states. But `_tc` is fresh,
so `Φ0` does **not** constrain it, and an initial state may have `_tc = 1` while
violating `ψn`. Hence Theorem 1's conclusion `⊨[0,∞)` fails.

We exhibit a **well-formed** instance and prove Theorem 1's conclusion false for
it. The refutation touches only the *first* normality window, so it is robust to
how `[0,∞)`-satisfaction is modelled (it breaks `SatInf`, the base `cTol[0,·]`,
and any `RecTol 0 _`).

Instance (`V = ℕ`):
* clock `tc = 0`, `tab = 1`, `tcd = 2`, `_tc = 3`, `cd = 4`, sensor `x_s = 5`;
* `ψn ≡ x_s ≤ 0`, `ψt ≡ ⊤`, `τ = δ = 1`;
* `sensing ≡ x_s := *` (makes `x_s ∈ Var(α)`, so the contract is well-formed),
  `ctrl_logic ≡ plant ≡ ?⊤`;
* `Φ0 ≡ tc = 0 ∧ tab = 0 ∧ tcd = −1` (`φpre ≡ ⊤`, `−δ = −1`);
* witness state `ω₀`: `tc,tab ↦ 0`, `tcd ↦ −1`, `_tc ↦ 1`, `x_s ↦ 1` (so `¬ψn`).
-/

namespace DLTol

open DL

/-- The distinguished variables, as `ℕ` indices. -/
def S6 : Scheme ℕ := { cd := 4, tab := 1, tcd := 2, tcAcc := 3, clk := 0 }

/-- `ψn ≡ x_s ≤ 0`. -/
def ψnCM : Formula ℕ := .cmp .le (.var 5) (.const 0)

/-- The diamond precondition `Φ0 ≡ tc = 0 ∧ tab = 0 ∧ tcd = −1` (`φpre ≡ ⊤`). -/
def Φ0CM : Formula ℕ :=
  .and (.cmp .eq (.var 0) (.const 0))
    (.and (.cmp .eq (.var 1) (.const 0)) (.cmp .eq (.var 2) (.const (-1))))

/-- Sensing writes the sensor variable, so `x_s ∈ Var(α)` and the contract is
well-formed. -/
def sensingCM : Program ℕ := .assignAny 5

/-- The witness accepted-estimate state: at timestamp `0`, marked `_tc = 1`, but
`x_s = 1` so it violates `ψn`. -/
def ω₀ : State ℕ := fun k => if k = 2 then -1 else if k = 3 then 1 else if k = 5 then 1 else 0

/-- The instance is **well-formed** (Def 5 side condition): `Var(ψn) = {x_s}` and
`x_s ∈ BV(sensing)`. -/
theorem wellFormed_CM :
    WellFormed sensingCM (.test .tt) (.test .tt) ψnCM .tt := by
  intro x hx
  -- Var(ψn) ∪ Var(ψt) = {5}; RHS contains BV(sensing) = {5}.
  simp only [Formula.vars, ψnCM, Formula.fv, Term.fv, sensingCM, Set.mem_union] at hx ⊢
  right
  rcases hx with (h | h) | h
  · simpa [Program.bv, Program.seq] using h
  · simp at h
  · simp at h

/-- `ω₀` is in the `⇓s`-extracted reachable set of the contracted CPS. -/
theorem ω₀_mem :
    ω₀ ∈ downS S6 (spSet Φ0CM (cCPS S6 sensingCM (.test .tt) (.test .tt) ψnCM .tt 1 1)) := by
  rw [downS_spSet_cCPS S6 sensingCM (.test .tt) (.test .tt) ψnCM .tt 1 1 Φ0CM
        (by simp [Program.bv]) (by simp [Program.bv])]
  refine ⟨?_, ?_⟩
  · -- Φ0CM holds at ω₀
    simp only [Φ0CM, Formula.sat, CompOp.interp, Term.eval, ω₀]
    norm_num
  · -- ω₀ _tc = 1
    simp [ω₀, S6]

/-- **Finding F2 (mechanized): Theorem 1, transcribed literally, is false.**
For the well-formed instance above, the conclusion of Theorem 1 —
`(Φ0⟨α*_c⟩)⇓s ⊨[0,∞) tc(ψn,ψt,τ,δ)` — does not hold. -/
theorem theorem1_literal_countermodel :
    ¬ SatInf S6.clk
        (downS S6 (spSet Φ0CM (cCPS S6 sensingCM (.test .tt) (.test .tt) ψnCM .tt 1 1)))
        ψnCM .tt 1 1 0 := by
  rintro ⟨T, hT0, _hmono, _hunb, hcyc⟩
  -- first cycle [T 0, T 1] = [0, T 1]
  obtain ⟨Tas, _Tae, hTas, _h2, _h3, hnorm, _hab, _hcd⟩ := hcyc 0
  rw [hT0] at hTas hnorm
  -- ω₀ sits at timestamp 0 ∈ [0, Tas], so the normality window forces ψn ω₀
  have hclk0 : ω₀ S6.clk = 0 := by simp [S6, ω₀]
  have hψn : Formula.sat ψnCM ω₀ :=
    hnorm ω₀ ω₀_mem (by rw [hclk0]) (by rw [hclk0]; linarith)
  -- but ω₀ violates ψn (x_s = 1 ≰ 0)
  simp only [ψnCM, Formula.sat, CompOp.interp, Term.eval, ω₀] at hψn
  norm_num at hψn

end DLTol
