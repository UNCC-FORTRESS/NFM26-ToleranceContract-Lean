# NFM'26 tolerance contracts — mechanization report

**Summary.** Theorem 1's *literal* Fig-6 construction has genuine defects (F1/F2
below — the `_tc := true ; _tc := false` slip); the corrected construction is
sound. Theorem 2 is **sound and cleanly mechanized** under its stated assumption
(`tc`-purity): no genuine findings — the Lemma-1 crux and the reduction are proved,
with the load-bearing assumptions carried as explicit hypotheses plus tightness
witnesses. This is verification, as expected for the paper's own latest result.

Mechanized in Lean 4 on the `dL-lean` (DI) foundation. Every claim below is a
compiled theorem; `#print axioms` reports only `propext, Classical.choice,
Quot.sound`.

## F1 — the acceptance marker is always cleared (proved)

Figure 6 ends `tc-hp` with `_tc := true ; _tc := false` (both statements, in
sequence). Hence every run of `tc-hp` ends with `_tc = 0`.

* `tcHP_tcAcc_eq_zero` (Governance.lean) — `⟦tc-hp⟧ ν ω → ω(_tc) = 0`.
* `downS_spSet_cCPS` (Governance.lean) — consequently

  ```
  (Φ0⟨α*_c⟩)⇓s  =  { ω | Φ0(ω) ∧ ω(_tc)=1 }
  ```

  i.e. the `⇓s`-extracted set is exactly the **initial** states (reached in zero
  loop iterations); no state produced by ≥ 1 completed control cycle survives the
  `⇓s` filter, because each cycle drives `_tc → 0`.

Only Def-5 freshness of `_tc` for `ctrl_logic`/`plant` is assumed.

## F2 — Theorem 1, transcribed literally, is FALSE (countermodel proved)

The surviving initial states all sit at timestamp `tc = 0` (`Φ0` fixes `tc = 0`).
Any recurring-tolerance witness must open with a normality window `[0, Tas]`
(`0 = Ts < Tas`), forcing `ψn` at timestamp `0`. But `_tc` is fresh, so `Φ0`
cannot constrain it — an initial state may have `_tc = 1` **and** `¬ψn`.

* `theorem1_literal_countermodel` (Findings.lean) — a **well-formed** instance
  (`ψn ≡ x_s ≤ 0`, `sensing ≡ x_s := *`, witness `x_s = 1, _tc = 1, tc = 0`)
  refutes Theorem 1's conclusion `⊨[0,∞)`. The refutation touches only the first
  `c-tol[0,·]` window, so it is robust to how `[0,∞)`-satisfaction is modelled.

So as literally stated, Theorem 1 is **vacuous-or-false** — both faces of the
`_tc := true ; _tc := false` sequencing (the CSF'25-style implicit-assumption
defect).

## The two-part fix (intended reading)

1. **Marker.** End `tc-hp` with `_tc := true` only; move `_tc := false` to the
   head of `sensing` (reset each cycle). → `tcHPfixed`, `sensingReset`.
2. **Observation point.** `⟨α*_c⟩` (a star's strongest postcondition) exposes
   only post-`plant` loop boundaries, not the post-`tc-hp` accepted-estimate
   states the contract governs. The intended object is
   `acceptedSet = spSet Φ0 ((body)* ; sensing ; tc-hp)`.

### Local soundness of the corrected construction (proved)

* `tcHPfixed_classifies` (Corrected.lean) — under Def-5 freshness, every accepted
  state satisfies `ψn`, or is a tolerable abnormality `¬ψn ∧ ψt`. This is the
  per-estimate faithfulness core that F2 exposed as missing.
* `tcHPfixed_marks` — every accepted state has `_tc = 1`; so `⇓s` now retains
  exactly the accepted states.
* `satInf_witness` — non-vacuity: a genuine unbounded recurring pattern satisfies
  the corrected conclusion `SatInf … [0,∞)` for any `τ, δ > 0`.

### Still open (the centerpiece)

The full trace-induction assembling the global `SatInf` cycle chain from an
*arbitrary* execution of `α*_c` is **not** closed here. It needs (a) extracting
the indexed sequence of accepted states from the loop, (b) a `plant`-advances-the-
clock hypothesis giving strictly increasing timestamps, and (c) the discreteness
of estimate timestamps (which lets the required abnormal window in an all-normal
cycle be placed in a timestamp gap). These hypotheses are identified but the
induction is future work.

## Load-bearing initial values `tab = 0`, `tcd = −δ` (isolated, proved)

Theorem 1 fixes `tab = 0`, `tcd = −δ` "to ensure all branches of `tc-hp` are
reachable even at `tc = 0`." Tested at the branch guards directly:

| branch | guard at `tc=0` | enabled iff | paper's value | verdict |
|---|---|---|---|---|
| `abnormalStart` | `tc − tcd ≥ δ` | `tcd ≤ −δ` | `tcd = −δ` | **tight** (largest admissible) |
| `abnormalContinue` | `tc − tab ≤ τ` | `tab ≥ −τ` | `tab = 0` | **sufficient, not tight** (`τ>0`, many values work) |

* `abnormalStart_reachable` / `abnormalStart_blocked` — enabled for `tcd ≤ −δ`,
  dead for `tcd > −δ` (e.g. the natural-but-wrong `tcd = 0` with `δ > 0`).
* `abnormalContinue_reachable` / `abnormalContinue_blocked` — enabled for
  `tab ≥ −τ`, dead for `tab < −τ`.

**Conclusion.** `tcd = −δ` is exactly the tightest value branch-reachability
needs; `tab = 0` is stronger than needed (`tab ≥ −τ` suffices). Both are relevant
only to *branch reachability / non-vacuity* of governance, not to the soundness
(classification) direction — `tcHPfixed_classifies` uses neither.

# Theorem 2 — verification (Lemma 1 + reduction), no genuine findings

Theorem 2 rests on **Lemma 1 (time-shift invariance)**. It is mechanized under the
paper's intended assumption that `tc` is a pure clock; that assumption is carried
as an *explicit hypothesis*, with a tightness witness that it is load-bearing.

## Modeling assumption made explicit: `tc`-purity

Lemma 1 shifts an abnormality-start `{tc,tab,tcd}` to canonical values and claims
the rest of the execution is unchanged. By variable:

* `tab`, `tcd` — **fresh** (Def 5): only `tc-hp`'s guards read them; covered.
* `tc` — the CPS's global clock, not fresh. The shift is behavior-preserving iff
  `ctrl_logic`/`plant` do not read `tc`'s absolute value into a non-timing
  variable. This is the paper's intended reading ("do not affect controller or
  plant behavior after contract acceptance") and holds for the water tank
  (`ctrl` reads local clock `tl`; `plant` reads `tc` only via `tc' = 1`).

The mechanization states this as the three component-equivariance hypotheses
(`Equivariant S sensing/ctrlLogic/plant`) in `lemma1` — the assumption made
explicit, not a defect.

**Tightness witness (not a refutation).** `lemma1_countermodel` (Theorem2.lean)
exhibits a well-formed CPS with `ctrl_logic ≡ z := tc` where the shift changes a
non-timing variable — demonstrating the `tc`-purity hypothesis is genuinely
load-bearing (drop it and Lemma 1 fails). Same clock-variable shape as the CSF'25
`tg`-monotonicity assumption.

## Corrected Lemma 1 — PROVED (Lemma1.lean)

Mechanized as a **relative-timing simulation**:

* `shiftBy S T` translates `{tc,tab,tcd}` by `−T`; `Equivariant S P` := every
  transition maps to another under the shift.
* **Crux** `tcHPfixed_equivariant` — `tc-hp` is equivariant: its guards test only
  *differences* (`guard_ge_invariant`: `(tc−T)−(tcd−T)=tc−tcd`; `guard_le_invariant`)
  and its `tab:=tc`/`tcd:=tc` assignments commute with translation
  (`assign_clk_timing`). `ψn,ψt` shift-invariance is a stated hypothesis.
* `cCPSfixed_equivariant` lifts through `seq`/`choice`/`star`.
* `lemma1` — the shift at `T = ω(tc)` gives the canonical counterpart.

*Methodology note (not a finding).* Lemma 1 is **not** a `Program.coincidence`
instance: `α*_c` reads `tc` (the guards) and `plant` writes it (`tc'=1`), so
`tc ∈ FV(α*_c)` and coincidence's `FV`-agreement premise fails. Hence a simulation
argument rather than a direct frame-lemma application.

*Construction detail (not a finding): `tcd` is dead.* The uniform shift yields
`tcd = ω(tcd) − ω(tc) ≤ −δ`, not exactly `−δ`. This is immaterial: `tcd` is read
only by `abnormalStart`'s guard, which is gated by `?cd`; from an abnormality
start (`cd=false`) the only route to `cd=true` is `normalStart`, which *overwrites*
`tcd` first. So `tcd`'s pre-shift value is never read before being overwritten —
genuinely dead. `lemma1`'s conclusion does not even expose `tcd`, and the reduction
does not require it; the exact `−δ` is a free reset justified by deadness.

## Items 4/5 reuse — confirmed faithful

dL-caltiming's `TSafe D u P φpre tg Tl Tu = IsGLB (D.val '' spTimed φpre P tg Tl Tu) u`
is exactly the paper's `T-safe^[Tl,Tu]_u`. Items 4/5 are this with `P = α*ct`,
`tg = tc`, windows `[0,tm]` / `[tm,δ]` — the same timed Q-safety mechanized in
dL-caltiming (its Definition 3). Dischargeable by citation.

## Theorem 2 reduction — PROVED, Boolean and quantitative

**Boolean** (`Theorem2Reduction.lean`): `abnormality_phase_safe` (Lemma-1
realignment + Item 4 + `Formula.coincidence`) and `theorem2_reduction` (normal /
abnormality phase split).

**Quantitative** (`Theorem2Quant.lean`, dL-qsafety/dL-caltiming wired into the
build): the Boolean `Safe` shadow is replaced by dL-qsafety's real signed margin
`Dist`:

* `abnormality_phase_margin` — the Lemma-1 realignment carrying the **margin**:
  `u ≤ D.val ν` for an abnormality-phase state (Item 4 margin at the canonical
  shift, transported by `hDframe` — `D` is physical).
* `theorem2_reduction_quant` — every reachable state has margin `≥ min(u,u₁)`,
  i.e. the paper's `T-safe^[0,∞)_{u₂}` with `u₂ ≥ min(u,u₁)` as a lower bound on
  the reachable Q-safety infimum. **This is the paper's quantitative conclusion.**
* `tsafe_margin_lb` — Items 4/5 discharged concretely: dL-caltiming's `TSafe`
  (`= IsGLB (D.val '' spTimed …) u`) yields the per-state margin lower bound via
  `IsGLB.1`.

**Remaining for full Theorem 2 (task #6):** only the phase-decomposition premise
`hClassify` — the abnormality-duration induction (Items 5/6, Item 6's ε-connecting
state). The Lemma-1 crux, the quantitative GLB reduction, and the Item 4/5 reuse
are all proved. Item 6 tightness audit deferred. All theorems `#print axioms`-clean.
