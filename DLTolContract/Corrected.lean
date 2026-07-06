/-
Copyright (c) 2026 dL-tolcontract contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-tolcontract contributors
-/
import DLTolContract.Contract

/-!
# The contracted CPS `α*c`

Assembles the `tc-hp` branches ([`Contract.lean`](Contract.lean)) into the
contract-governance program and the contracted CPS Theorem 2 reasons about:

* `tcCore` — the two-case choice; `tcHPfixed` — the governance program (ends with
  the acceptance marker `_tc := true`);
* `sensingReset` resets `_tc` at the head of each cycle;
* `bodyFixed` — one control cycle `sensing ; tc-hp ; ctrl_logic ; plant`;
* `cCPSfixed` — `α*c = bodyFixed*`.

`bv_tcHPfixed_subset` records that `tc-hp` writes only the fresh variables
`{cd, tab, tcd, _tc}` — the frame fact the equivariance and reachability proofs
([`Lemma1.lean`](Lemma1.lean), [`Theorem2.lean`](Theorem2.lean)) consume.
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

end DLTol
