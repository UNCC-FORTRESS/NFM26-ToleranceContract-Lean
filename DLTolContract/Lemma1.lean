/-
Copyright (c) 2026 dL-tolcontract contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-tolcontract contributors
-/
import DLTolContract.Corrected

/-!
# Corrected Lemma 1 — time-shift invariance via a relative-timing simulation

`Theorem2.lean` shows the `tc`-purity assumption is load-bearing (tightness
witness), and that Lemma 1 is **not** a `Program.coincidence` instance (the program
reads `tc`). The correct proof is a *relative-timing simulation*: translating the
timing variables `{tc,tab,tcd}` by a constant `−T` is an automorphism of the
transition relation, because

* `tc-hp`'s guards test only **differences** `tc − tab`, `tc − tcd` (shift-invariant),
  and its assignments `tab := tc`, `tcd := tc` commute with the translation;
* `sensing`, `ctrl_logic`, `plant` are **shift-equivariant** — the explicit form of
  the paper's implicit "do not affect controller or plant behavior" claim
  (i.e. `tc`-purity; `plant`'s `tc' = 1` clock is itself translation-invariant).

We define the shift, prove `tc-hp` equivariant outright, take component
equivariance as the stated `tc`-purity hypotheses, lift through the loop, and
conclude Lemma 1.

`shiftBy S T` translates `clk (tc)`, `tab`, `tcd` by `−T`, fixing everything else.
`Equivariant` is one-directional (`sem → sem` of the shifted pair) — the direction
Lemma 1 uses (original execution ↦ canonical execution).
-/

namespace DLTol

open DL

variable {V : Type*} [DecidableEq V]

/-- Translate the three timing variables of `S` by `−T`, fixing all others. -/
def shiftBy (S : Scheme V) (T : ℝ) (s : State V) : State V :=
  fun x => if x = S.clk then s x - T
           else if x = S.tab then s x - T
           else if x = S.tcd then s x - T else s x

@[simp] theorem shiftBy_clk (S : Scheme V) (T : ℝ) (s : State V) :
    shiftBy S T s S.clk = s S.clk - T := by simp [shiftBy]

/-- A program is (one-directionally) **shift-equivariant**: every transition maps,
under the timing translation, to another transition. -/
def Equivariant (S : Scheme V) (P : Program V) : Prop :=
  ∀ (T : ℝ) (s s' : State V), Program.sem P s s' → Program.sem P (shiftBy S T s) (shiftBy S T s')

/-! ## Compositional closure -/

theorem Equivariant.seq {S : Scheme V} {a b : Program V}
    (ha : Equivariant S a) (hb : Equivariant S b) : Equivariant S (.seq a b) := by
  rintro T s s' ⟨μ, hsμ, hμs'⟩; exact ⟨shiftBy S T μ, ha T s μ hsμ, hb T μ s' hμs'⟩

theorem Equivariant.choice {S : Scheme V} {a b : Program V}
    (ha : Equivariant S a) (hb : Equivariant S b) : Equivariant S (.choice a b) := by
  rintro T s s' (h | h)
  · exact Or.inl (ha T s s' h)
  · exact Or.inr (hb T s s' h)

theorem Equivariant.star {S : Scheme V} {a : Program V}
    (ha : Equivariant S a) : Equivariant S (.star a) := by
  rintro T s s' h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih => exact ih.tail (ha T _ _ hlast)

/-- The five variables of `S` are pairwise distinct (the fresh auxiliaries
`cd,tab,tcd,_tc` are distinct from each other and from the clock `tc`). -/
structure Scheme.Distinct (S : Scheme V) : Prop where
  cd_clk : S.cd ≠ S.clk
  cd_tab : S.cd ≠ S.tab
  cd_tcd : S.cd ≠ S.tcd
  acc_clk : S.tcAcc ≠ S.clk
  acc_tab : S.tcAcc ≠ S.tab
  acc_tcd : S.tcAcc ≠ S.tcd
  tab_clk : S.tab ≠ S.clk
  tcd_clk : S.tcd ≠ S.clk
  tcd_tab : S.tcd ≠ S.tab

/-- Non-timing variables are fixed by the shift. -/
theorem shiftBy_nontiming {S : Scheme V} {T : ℝ} {s : State V} {x : V}
    (h1 : x ≠ S.clk) (h2 : x ≠ S.tab) (h3 : x ≠ S.tcd) : shiftBy S T s x = s x := by
  simp [shiftBy, h1, h2, h3]

@[simp] theorem shiftBy_tab {S : Scheme V} (hd : S.Distinct) (T : ℝ) (s : State V) :
    shiftBy S T s S.tab = s S.tab - T := by simp [shiftBy, hd.tab_clk]

@[simp] theorem shiftBy_tcd {S : Scheme V} (hd : S.Distinct) (T : ℝ) (s : State V) :
    shiftBy S T s S.tcd = s S.tcd - T := by simp [shiftBy, hd.tcd_clk, hd.tcd_tab]

/-! ## Atomic equivariance -/

/-- A test is equivariant when its guard is shift-invariant. -/
theorem Equivariant.test {S : Scheme V} {φ : Formula V}
    (h : ∀ (T : ℝ) (s : State V), Formula.sat φ s → Formula.sat φ (shiftBy S T s)) :
    Equivariant S (.test φ) := by
  rintro T s s' ⟨rfl, hφ⟩; exact ⟨rfl, h T s hφ⟩

/-- Assigning a constant to a **non-timing** variable is equivariant. -/
theorem Equivariant.assign_const_nontiming {S : Scheme V} {x : V} {c : ℝ}
    (h1 : x ≠ S.clk) (h2 : x ≠ S.tab) (h3 : x ≠ S.tcd) :
    Equivariant S (.assign x (.const c)) := by
  rintro T s s' ⟨hx, hfr⟩
  refine ⟨?_, ?_⟩
  · rw [shiftBy_nontiming h1 h2 h3, hx]; rfl
  · intro y hy
    by_cases hyt : y = S.clk
    · subst hyt; simp only [shiftBy_clk, hfr _ hy]
    by_cases hya : y = S.tab
    · subst hya; simp only [shiftBy, if_neg hyt, hfr _ hy]
    by_cases hyd : y = S.tcd
    · subst hyd; simp only [shiftBy, if_neg hyt, if_neg hya, hfr _ hy]
    · rw [shiftBy_nontiming hyt hya hyd, shiftBy_nontiming hyt hya hyd, hfr _ hy]

/-- Assigning the clock `tc` to `tab` or `tcd` (a timing variable) is equivariant:
`tab := tc` translated is `(tab−T) := (tc−T)`. -/
theorem Equivariant.assign_clk_timing {S : Scheme V} (hd : S.Distinct) {x : V}
    (hx : x = S.tab ∨ x = S.tcd) :
    Equivariant S (.assign x (.var S.clk)) := by
  rintro T s s' ⟨hx', hfr⟩
  have hxt : x ≠ S.clk := by
    rcases hx with h | h
    · subst h; exact hd.tab_clk
    · subst h; exact hd.tcd_clk
  refine ⟨?_, ?_⟩
  · -- (shift s') x = (var clk).eval (shift s) = (shift s) clk = s clk − T
    have hsx : shiftBy S T s' x = s' x - T := by
      rcases hx with h | h <;> subst h
      · exact shiftBy_tab hd T s'
      · exact shiftBy_tcd hd T s'
    simp only [Term.eval, shiftBy_clk, hsx, hx']
  · intro y hy
    by_cases hyt : y = S.clk
    · subst hyt; simp only [shiftBy_clk, hfr _ hy]
    by_cases hya : y = S.tab
    · subst hya; rw [shiftBy_tab hd, shiftBy_tab hd, hfr _ hy]
    by_cases hyd : y = S.tcd
    · subst hyd; rw [shiftBy_tcd hd, shiftBy_tcd hd, hfr _ hy]
    · rw [shiftBy_nontiming hyt hya hyd, shiftBy_nontiming hyt hya hyd, hfr _ hy]

/-! ## Guard shift-invariance — the crux: `tc-hp`'s guards test only *differences* -/

/-- The cooldown-length guard `tc − tcd ≥ δ` is shift-invariant: `(tc−T)−(tcd−T) = tc−tcd`. -/
theorem guard_ge_invariant {S : Scheme V} (hd : S.Distinct) (δ T : ℝ) (s : State V)
    (h : Formula.sat (.cmp .ge (.binop .sub (.var S.clk) (.var S.tcd)) (.const δ)) s) :
    Formula.sat (.cmp .ge (.binop .sub (.var S.clk) (.var S.tcd)) (.const δ)) (shiftBy S T s) := by
  simp only [Formula.sat, Term.eval, CompOp.interp, AOp.interp, shiftBy_clk, shiftBy_tcd hd] at h ⊢
  linarith

/-- The abnormality-duration guard `tc − tab ≤ τ` is shift-invariant. -/
theorem guard_le_invariant {S : Scheme V} (hd : S.Distinct) (τ T : ℝ) (s : State V)
    (h : Formula.sat (.cmp .le (.binop .sub (.var S.clk) (.var S.tab)) (.const τ)) s) :
    Formula.sat (.cmp .le (.binop .sub (.var S.clk) (.var S.tab)) (.const τ)) (shiftBy S T s) := by
  simp only [Formula.sat, Term.eval, CompOp.interp, AOp.interp, shiftBy_clk, shiftBy_tab hd] at h ⊢
  linarith

/-- The cooldown flag guard `?cd` is shift-invariant (`cd` is non-timing). -/
theorem bTrue_cd_invariant {S : Scheme V} (hd : S.Distinct) (T : ℝ) (s : State V)
    (h : Formula.sat (bTrue S.cd) s) : Formula.sat (bTrue S.cd) (shiftBy S T s) := by
  simpa only [bTrue, Formula.sat, Term.eval, CompOp.interp,
    shiftBy_nontiming hd.cd_clk hd.cd_tab hd.cd_tcd] using h

/-- The guard `?¬cd` is shift-invariant. -/
theorem bFalse_cd_invariant {S : Scheme V} (hd : S.Distinct) (T : ℝ) (s : State V)
    (h : Formula.sat (bFalse S.cd) s) : Formula.sat (bFalse S.cd) (shiftBy S T s) := by
  simpa only [bFalse, bTrue, Formula.sat, Term.eval, CompOp.interp,
    shiftBy_nontiming hd.cd_clk hd.cd_tab hd.cd_tcd] using h

/-! ## `tc-hp` is shift-equivariant

The contract predicates `ψn, ψt` are assumed shift-invariant (they constrain
sensor estimates, not clocks — the natural reading of well-formedness). Everything
else is discharged by the atomic and guard lemmas above. -/

theorem tcHPfixed_equivariant {S : Scheme V} (hd : S.Distinct) {ψn ψt : Formula V} {τ δ : ℝ}
    (hψn : ∀ (T : ℝ) (s : State V), Formula.sat ψn (shiftBy S T s) ↔ Formula.sat ψn s)
    (hψt : ∀ (T : ℝ) (s : State V), Formula.sat ψt (shiftBy S T s) ↔ Formula.sat ψt s) :
    Equivariant S (tcHPfixed S ψn ψt τ δ) := by
  simp only [tcHPfixed, tcCore, normalContinue, normalStart, abnormalStart, abnormalContinue]
  refine Equivariant.seq (Equivariant.choice ?_ ?_)
    (Equivariant.assign_const_nontiming hd.acc_clk hd.acc_tab hd.acc_tcd)
  · -- normal case: ?ψn ; (?cd ∪ ?¬cd; cd:=true; tcd:=tc)
    refine Equivariant.seq (Equivariant.test (fun T s h => (hψn T s).mpr h))
      (Equivariant.choice (Equivariant.test (fun T s h => bTrue_cd_invariant hd T s h)) ?_)
    exact Equivariant.seq (Equivariant.test (fun T s h => bFalse_cd_invariant hd T s h))
      (Equivariant.seq (Equivariant.assign_const_nontiming hd.cd_clk hd.cd_tab hd.cd_tcd)
        (Equivariant.assign_clk_timing hd (Or.inr rfl)))
  · -- abnormal case: ?(¬ψn ∧ ψt) ; (abnormalStart ∪ abnormalContinue)
    refine Equivariant.seq
      (Equivariant.test (fun T s h => ⟨fun hc => h.1 ((hψn T s).mp hc), (hψt T s).mpr h.2⟩))
      (Equivariant.choice ?_ ?_)
    · -- abnormalStart: ?cd ; cd:=false ; ?(tc−tcd≥δ) ; tab:=tc
      exact Equivariant.seq (Equivariant.test (fun T s h => bTrue_cd_invariant hd T s h))
        (Equivariant.seq (Equivariant.assign_const_nontiming hd.cd_clk hd.cd_tab hd.cd_tcd)
          (Equivariant.seq (Equivariant.test (fun T s h => guard_ge_invariant hd δ T s h))
            (Equivariant.assign_clk_timing hd (Or.inl rfl))))
    · -- abnormalContinue: ?¬cd ; ?(tc−tab≤τ)
      exact Equivariant.seq (Equivariant.test (fun T s h => bFalse_cd_invariant hd T s h))
        (Equivariant.test (fun T s h => guard_le_invariant hd τ T s h))

/-! ## Lifting to the loop, given `tc`-purity of `sensing`/`ctrl_logic`/`plant`

The equivariance of `sensing`, `ctrl_logic`, `plant` is the **explicit `tc`-purity
hypothesis** without which the realignment fails. For the paper's water tank it
holds: `ctrl` reads only the local clock `tl`, and `plant`'s `tc' = 1` clock is
translation-invariant. -/

theorem bodyFixed_equivariant {S : Scheme V} (hd : S.Distinct)
    {sensing ctrlLogic plant : Program V} {ψn ψt : Formula V} {τ δ : ℝ}
    (hψn : ∀ (T : ℝ) (s : State V), Formula.sat ψn (shiftBy S T s) ↔ Formula.sat ψn s)
    (hψt : ∀ (T : ℝ) (s : State V), Formula.sat ψt (shiftBy S T s) ↔ Formula.sat ψt s)
    (hsens : Equivariant S sensing) (hctrl : Equivariant S ctrlLogic)
    (hplant : Equivariant S plant) :
    Equivariant S (bodyFixed S sensing ctrlLogic plant ψn ψt τ δ) :=
  Equivariant.seq
    (Equivariant.seq (Equivariant.assign_const_nontiming hd.acc_clk hd.acc_tab hd.acc_tcd) hsens)
    (Equivariant.seq (tcHPfixed_equivariant hd hψn hψt) (Equivariant.seq hctrl hplant))

theorem cCPSfixed_equivariant {S : Scheme V} (hd : S.Distinct)
    {sensing ctrlLogic plant : Program V} {ψn ψt : Formula V} {τ δ : ℝ}
    (hψn : ∀ (T : ℝ) (s : State V), Formula.sat ψn (shiftBy S T s) ↔ Formula.sat ψn s)
    (hψt : ∀ (T : ℝ) (s : State V), Formula.sat ψt (shiftBy S T s) ↔ Formula.sat ψt s)
    (hsens : Equivariant S sensing) (hctrl : Equivariant S ctrlLogic)
    (hplant : Equivariant S plant) :
    Equivariant S (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) :=
  Equivariant.star (bodyFixed_equivariant hd hψn hψt hsens hctrl hplant)

/-- **Corrected Lemma 1 (time-shift invariance).** Under the `tc`-purity
hypotheses (`sensing`/`ctrl_logic`/`plant` shift-equivariant) and `ψn`/`ψt`
shift-invariance, any abnormality-start execution `(ω,ν)` of the contracted CPS
has a time-shifted counterpart `(ω',ν')` that: is itself a valid execution; agrees
with the original on **all** non-timing variables; and is canonical
(`tc = 0, tab = 0, cd = false`).

The shift is `shiftBy S (ω tc)` — translate `{tc,tab,tcd}` by `−ω(tc)`. Proved
purely from equivariance; the crux `tcHPfixed_equivariant` supplies that the
`tc-hp` guards, testing only `tc−tab`/`tc−tcd`, are shift-invariant.

Construction detail: the shift yields `ω'(tcd) = ω(tcd) − ω(tc) ≤ −δ`, not exactly
the paper's `tcd = −δ`. Immaterial — `tcd` is **dead** from an abnormality start
(read only by `abnormalStart`'s guard, gated by `?cd`; reaching `cd=true` from
`cd=false` requires `normalStart`, which overwrites `tcd` first). This conclusion
does not expose `tcd` and the reduction does not require it; the exact `−δ` is a
free reset justified by deadness. -/
theorem lemma1 {S : Scheme V} (hd : S.Distinct)
    {sensing ctrlLogic plant : Program V} {ψn ψt : Formula V} {τ δ : ℝ}
    (hψn : ∀ (T : ℝ) (s : State V), Formula.sat ψn (shiftBy S T s) ↔ Formula.sat ψn s)
    (hψt : ∀ (T : ℝ) (s : State V), Formula.sat ψt (shiftBy S T s) ↔ Formula.sat ψt s)
    (hsens : Equivariant S sensing) (hctrl : Equivariant S ctrlLogic)
    (hplant : Equivariant S plant)
    {ω ν : State V}
    (hrun : Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω ν)
    (hcd : ω S.cd = 0) (htab : ω S.tab = ω S.clk) :
    ∃ ω' ν',
      Program.sem (cCPSfixed S sensing ctrlLogic plant ψn ψt τ δ) ω' ν' ∧
      (∀ x, x ∉ ({S.clk, S.tab, S.tcd} : Set V) → ω' x = ω x ∧ ν' x = ν x) ∧
      ω' S.clk = 0 ∧ ω' S.tab = 0 ∧ ω' S.cd = 0 := by
  refine ⟨shiftBy S (ω S.clk) ω, shiftBy S (ω S.clk) ν,
    cCPSfixed_equivariant hd hψn hψt hsens hctrl hplant (ω S.clk) ω ν hrun, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [not_or] at hx
    exact ⟨shiftBy_nontiming hx.1 hx.2.1 hx.2.2, shiftBy_nontiming hx.1 hx.2.1 hx.2.2⟩
  · simp [shiftBy_clk]
  · rw [shiftBy_tab hd, htab]; ring
  · rw [shiftBy_nontiming hd.cd_clk hd.cd_tab hd.cd_tcd]; exact hcd

end DLTol
