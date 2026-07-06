/-
Copyright (c) 2026 dL-tolcontract contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-tolcontract contributors
-/
import DLTolContract.Contract

/-!
# Contract governance: the `_tc` marker and the reachable accepted-estimate set

Before Theorem 1 (soundness of contract governance), we mechanize what the
`⇓s`-extracted set `((… ⟨α*_c⟩))⇓s` of Theorem 1 actually **is** under the
foundation's semantics, because Figure 6 ends `tc-hp` with the verbatim pair

```
    _tc := true ; _tc := false
```

The two proofs below establish, with no extra assumptions beyond Def 5 freshness:

* `tcHP_tcAcc_eq_zero` — every run of `tc-hp` ends with `_tc = 0` (false);
* `downS_spSet_cCPS` — consequently the extracted accepted-estimate set equals
  exactly the set of **initial** states (reached in zero loop iterations) whose
  `_tc` happens to be `1`. No state produced by executing ≥ 1 control cycle is in
  it, because every completed cycle drives `_tc` back to `0`.

This is reported as **Finding F1**: as literally transcribed, Theorem 1's
`⇓s`-set carries no processed estimate, so its `⊨[0,∞)` conclusion is degenerate
(vacuous over the non-initial estimates). The fix consistent with the paper's
intent — mark acceptance and *keep* it until the next reset — is `tc-hp` ending
in `_tc := true` only, with `_tc := false` at the head of `sensing`.
-/

namespace DLTol

open DL

variable {V : Type*}

/-- **The acceptance marker is cleared by `tc-hp`.** Every transition of
`tc-hp(ψn,ψt,τ,δ)` ends in a state with `_tc = 0`, because the program's final
two statements are `_tc := true ; _tc := false`. -/
theorem tcHP_tcAcc_eq_zero (S : Scheme V) (ψn ψt : Formula V) (τ δ : ℝ)
    {ν ω : State V} (h : Program.sem (tcHP S ψn ψt τ δ) ν ω) :
    ω S.tcAcc = 0 := by
  -- tcHP = (choice …) ; (setTrue tcAcc ; setFalse tcAcc)
  obtain ⟨_μ, _hCH, μ2, _hTrue, hFalse⟩ := h
  -- hFalse : sem (assign tcAcc (const 0)) μ2 ω
  exact hFalse.1

/-- One full control cycle of a contracted CPS clears `_tc`, provided `_tc` is
fresh for `ctrl_logic` and `plant` (Def 5 freshness: `BV(tc-hp)` — which contains
`_tc` — is disjoint from the original CPS, hence from `BV(ctrl_logic)` and
`BV(plant)`). -/
theorem body_tcAcc_eq_zero (S : Scheme V) (sensing ctrlLogic plant : Program V)
    (ψn ψt : Formula V) (τ δ : ℝ)
    (hctrl : S.tcAcc ∉ ctrlLogic.bv) (hplant : S.tcAcc ∉ plant.bv)
    {ν ω : State V}
    (h : Program.sem (.seq sensing (.seq (tcHP S ψn ψt τ δ) (.seq ctrlLogic plant))) ν ω) :
    ω S.tcAcc = 0 := by
  obtain ⟨a, _hsens, b, htc, c, hctl, hpl⟩ := h
  have hb : b S.tcAcc = 0 := tcHP_tcAcc_eq_zero S ψn ψt τ δ htc
  -- ctrl_logic and plant do not write _tc, so its value is preserved through them.
  have hbc : b S.tcAcc = c S.tcAcc := Program.bound_effect ctrlLogic hctl _ hctrl
  have hcω : c S.tcAcc = ω S.tcAcc := Program.bound_effect plant hpl _ hplant
  rw [← hcω, ← hbc, hb]

/-- **Finding F1 (mechanized).** The `⇓s`-extracted reachable set of a contracted
CPS is *exactly* the set of initial `φpre`-states whose `_tc` is already `1`;
equivalently, no state reachable by executing one or more control cycles survives
the `⇓s` filter. Hypotheses are just Def 5 freshness of `_tc` for `ctrl_logic`
and `plant`. -/
theorem downS_spSet_cCPS (S : Scheme V) (sensing ctrlLogic plant : Program V)
    (ψn ψt : Formula V) (τ δ : ℝ) (φpre : Formula V)
    (hctrl : S.tcAcc ∉ ctrlLogic.bv) (hplant : S.tcAcc ∉ plant.bv) :
    downS S (spSet φpre (cCPS S sensing ctrlLogic plant ψn ψt τ δ))
      = {ω | Formula.sat φpre ω ∧ ω S.tcAcc = 1} := by
  set body := (Program.seq sensing (.seq (tcHP S ψn ψt τ δ) (.seq ctrlLogic plant)))
    with hbody
  ext ω
  simp only [downS, spSet, cCPS, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨init, hpre, hstar⟩, hacc⟩
    -- hstar : ReflTransGen (sem body) init ω ; hacc : ω tcAcc = 1
    rcases Relation.ReflTransGen.cases_tail hstar with heq | ⟨μ, _hμ, hlast⟩
    · -- zero iterations: ω = init, so φpre holds at ω
      subst heq; exact ⟨hpre, hacc⟩
    · -- ≥ 1 iteration: the last cycle forces ω tcAcc = 0, contradicting hacc = 1
      have : ω S.tcAcc = 0 :=
        body_tcAcc_eq_zero S sensing ctrlLogic plant ψn ψt τ δ hctrl hplant hlast
      rw [this] at hacc; norm_num at hacc
  · rintro ⟨hpre, hacc⟩
    -- reachable in zero iterations (loop reflexivity)
    exact ⟨⟨ω, hpre, Relation.ReflTransGen.refl⟩, hacc⟩

end DLTol
