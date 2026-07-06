# dL-tolcontract

A Lean 4 + Mathlib mechanization of **"Sensor Tolerance Contracts for Safety
Assurance in Cyber-Physical Systems"** (Jian Xiang, NFM'26).

The paper introduces *tolerance contracts* — specifications of how much, how long,
and how frequently sensor abnormalities are permitted — and reasoning techniques
for the safety of *contracted CPSs* in differential dynamic logic (dL). This repo
formalizes the syntax/semantics of tolerance contracts (Defs 3–5, Fig 6) and the
two central theorems, on the [`dL-lean`](https://github.com/UNCC-FORTRESS/dL-formalization-Lean)
foundation, reusing the timed Q-safety of
[`dL-caltiming`](https://github.com/UNCC-FORTRESS/CSF25-Timed-Qsafety-Lean) (CSF'25)
and [`dL-qsafety`](https://github.com/UNCC-FORTRESS/HSCC26-Qsafety-Lean) (HSCC).

## Status

`lake build` green · `grep -rn sorry` clean · `#print axioms` =
`propext / Classical.choice / Quot.sound` only, on every theorem.

The paper's central contribution — **Theorem 2's recurring→single-cycle
reduction** — is mechanized end-to-end, boundary-granular, over the real
Q-safety margin. Theorem 1's *literal* Fig-6 construction is shown defective
(machine-checked countermodels); the corrected construction is sound.

| File | Content |
|---|---|
| [`Contract.lean`](DLTolContract/Contract.lean) | Defs 3–5: `cTol`/`RecTol`/`Sat`/`SatInf`, `tcHP`/`cCPS`, `WellFormed`, `downS` |
| [`Governance.lean`](DLTolContract/Governance.lean) | Theorem 1 governance; finding **F1** |
| [`Findings.lean`](DLTolContract/Findings.lean) | Theorem 1 literal countermodel (**F2**) |
| [`Corrected.lean`](DLTolContract/Corrected.lean) | corrected `tc-hp`; per-estimate soundness; init-value isolation |
| [`Lemma1.lean`](DLTolContract/Lemma1.lean) | **Lemma 1** (time-shift invariance) via relative-timing simulation |
| [`Theorem2.lean`](DLTolContract/Theorem2.lean) | `tc`-purity tightness witness (**F3**) |
| [`Theorem2Reduction.lean`](DLTolContract/Theorem2Reduction.lean) | Boolean reduction |
| [`Theorem2Quant.lean`](DLTolContract/Theorem2Quant.lean) | quantitative reduction over `Dist` |
| [`Theorem2Induction.lean`](DLTolContract/Theorem2Induction.lean) | recurring→single-cycle loop induction; **`theorem2_quant`** capstone |
| [`Item6.lean`](DLTolContract/Item6.lean) | Item 6 (`τ ≤ tm ≤ δ−ϵ`) tightness audit |

---

## Theorem 2 — safety of contracted CPS via tolerance-cycle invariant (main result)

Theorem 2 is the paper's central reasoning technique: it reduces safety over
*unbounded, recurring* tolerance cycles to safety over a *single canonical cycle*.
The recurring→single-cycle reduction is mechanized in full.

### The capstone

[`theorem2_quant`](DLTolContract/Theorem2Induction.lean) — every state reachable by
the contracted CPS `α*c` has Q-safety margin `≥ min(u, u₁)`, i.e. the paper's
`T-safe^[0,∞)_{u₂}` with `u₂ ≥ min(u,u₁)`, expressed over
[`dL-qsafety`](https://github.com/UNCC-FORTRESS/HSCC26-Qsafety-Lean)'s real signed
distance `Dist`. Everything unbounded/recurring is discharged; what remains are
exactly the *single-cycle* premises the paper itself imports from prior work
("Item 4 and 5 … not the focus of this work").

### How it is built (three layers)

1. **Lemma 1 — time-shift invariance** ([`Lemma1.lean`](DLTolContract/Lemma1.lean)).
   An abnormality start at an arbitrary time is realigned to the canonical cycle by
   translating the timing variables `{tc,tab,tcd}`. Mechanized as a **shift
   equivariance**, *not* a frame-lemma instance (the program reads `tc`). The crux
   [`tcHPfixed_equivariant`](DLTolContract/Lemma1.lean) proves `tc-hp` equivariant
   because its guards test only *differences* `tc−tab`, `tc−tcd`, and its
   assignments `tab:=tc`/`tcd:=tc` commute with the translation;
   [`cCPSfixed_equivariant`](DLTolContract/Lemma1.lean) lifts through
   `seq`/`choice`/`star`; [`lemma1`](DLTolContract/Lemma1.lean) assembles it.

2. **Quantitative reduction** ([`Theorem2Quant.lean`](DLTolContract/Theorem2Quant.lean)).
   [`abnormality_phase_margin`](DLTolContract/Theorem2Quant.lean) — Lemma 1 carries
   the **margin** across the shift (Item 4 at the canonical start, transported by
   coincidence since `Dist` is physical);
   [`theorem2_reduction_quant`](DLTolContract/Theorem2Quant.lean) splits normal /
   abnormality phases;
   [`tsafe_margin_lb`](DLTolContract/Theorem2Quant.lean) ties Items 4/5 to
   `dL-caltiming`'s `TSafe` via `IsGLB.1`.

3. **Recurring→single-cycle loop induction**
   ([`Theorem2Induction.lean`](DLTolContract/Theorem2Induction.lean)).
   [`phase_invariant`](DLTolContract/Theorem2Induction.lean) proves the
   boundary-granular `Phase` invariant holds at every reachable loop boundary by
   `ReflTransGen` induction;
   [`hClassify_of_phase`](DLTolContract/Theorem2Induction.lean) discharges the
   phase decomposition. Boundary-granular is the faithful granularity: Theorem 2's
   conclusion is Q-safety over the loop's strongest-postcondition.

### Item 6 tightness audit

[`Item6.lean`](DLTolContract/Item6.lean) unfolds the connecting-control-cycle
condition inside recovery and confirms Item 6's `τ ≤ tm ≤ δ−ϵ` is **exactly tight**:
[`item6_equiv`](DLTolContract/Item6.lean) shows it equals the connecting-cycle
condition; [`item6_epsilon_tight`](DLTolContract/Item6.lean) shows `−ϵ` is precisely
one max-latency control cycle of slack; [`item6_tau_tight`](DLTolContract/Item6.lean)
shows `τ ≤ tm` is the post-abnormality requirement. Both bounds load-bearing.

---

## Machinery, connections, and auxiliary results

### (i) Main machinery built here

* **Tolerance-contract semantics** ([`Contract.lean`](DLTolContract/Contract.lean)) —
  `cTol` (Def 3, single cycle) and `RecTol` (Def 4, recurring; an inductive `Prop`
  = the least-fixed-point finite cycle chain), satisfaction `Sat`/`SatInf`, the
  contract-governance program `tcHP` (Fig 6, transcribed verbatim), the contracted
  CPS `cCPS` (Def 5), `WellFormed`, and the `⇓s` extraction `downS`.
* **Shift-equivariance framework** ([`Lemma1.lean`](DLTolContract/Lemma1.lean)) —
  `shiftBy` (timing-variable translation), `Equivariant`, its closure under
  `seq`/`choice`/`star`, and atomic equivariance lemmas. The reusable core behind
  Lemma 1's relative-timing simulation.
* **Boundary-granular phase invariant** ([`Theorem2Induction.lean`](DLTolContract/Theorem2Induction.lean)) —
  `Phase` and the loop-induction lift that reduces the unbounded loop to
  single-cycle obligations.
* **Corrected contract governance** ([`Corrected.lean`](DLTolContract/Corrected.lean)) —
  the marker-fixed `tcHPfixed`/`sensingReset`/`bodyFixed`/`cCPSfixed`, per-estimate
  soundness (`tcHPfixed_classifies`, `tcHPfixed_marks`).

### (ii) Connections to other repos

Pinned dependencies (see [`lakefile.toml`](lakefile.toml)):

* [`dL-lean`](https://github.com/UNCC-FORTRESS/dL-formalization-Lean) `@ v0.1.0-DI` —
  dL syntax, `⟦·⟧`, `FV`/`BV`/`MBV`, coincidence + bound-effect (the frame
  metatheory Lemma 1 and the classification lemmas route through), loop induction.
* [`dL-qsafety`](https://github.com/UNCC-FORTRESS/HSCC26-Qsafety-Lean) `@ v0.1.0-HSCC23` —
  the signed safety distance `Dist`, over which the quantitative Theorem 2 is stated.
* [`dL-caltiming`](https://github.com/UNCC-FORTRESS/CSF25-Timed-Qsafety-Lean) `@ v0.1.0-CSF25` —
  timed Q-safety `TSafe` (`= IsGLB (Dist.val '' spTimed …) u`), the exact object of
  Theorem 2's Items 4/5.

### (iii) Auxiliary results and findings

The mechanization applies the same audit discipline as the CSF'25 work — pin
exactly what each theorem depends on.

* **Theorem 1 — genuine construction defects (F1/F2).** Figure 6 ends `tc-hp` with
  `_tc := true ; _tc := false`, so the acceptance marker is always cleared
  ([`tcHP_tcAcc_eq_zero`](DLTolContract/Governance.lean)) and the `⇓s`-extracted
  reachable set collapses to initial states
  ([`downS_spSet_cCPS`](DLTolContract/Governance.lean)); a **well-formed
  countermodel** ([`theorem1_literal_countermodel`](DLTolContract/Findings.lean))
  refutes Theorem 1's literal `⊨[0,∞)` conclusion. The corrected construction
  (marker `_tc := true` only, reset in `sensing`; observe the post-`tc-hp` set) is
  sound: [`tcHPfixed_classifies`](DLTolContract/Corrected.lean) proves every
  accepted estimate is contract-classified; [`satInf_witness`](DLTolContract/Corrected.lean)
  shows the corrected conclusion is satisfiable.
* **Theorem 1 initial values.** `tcd = −δ` is *tight* (branch reachable iff
  `tcd ≤ −δ`); `tab = 0` is only *sufficient* (`tab ≥ −τ` suffices) —
  [`abnormalStart_reachable`/`_blocked`, `abnormalContinue_reachable`/`_blocked`](DLTolContract/Corrected.lean).
* **Theorem 2 — `tc`-purity (F3, tightness note).** Lemma 1 needs `tc` a pure clock
  (its intended assumption, carried as explicit hypotheses); the witness
  [`lemma1_countermodel`](DLTolContract/Theorem2.lean) (`ctrl_logic ≡ z := tc`) shows
  it is load-bearing.
* **Theorem 2 base case — `ϕinv` at onset (F5, completeness note).** "`ωm ⊨ ϕinv`
  by Item 3" is imprecise: Item 3 preserves `ϕinv` only across normal cycles;
  crossing the sensor-havoc onset needs a condition not among Items 1–6 (present in
  §5's prose sensing assumption `x_s ≥ x_p`). Not unsoundness — carried explicitly
  as a premise.

Full write-up: [`FINDINGS.md`](FINDINGS.md).

---

## Build

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build
```

All three foundations are git-pinned to their released milestone tags in
[`lakefile.toml`](lakefile.toml): `dL-lean @ v0.1.0-DI`,
`dL-qsafety @ v0.1.0-HSCC23`, `dL-caltiming @ v0.1.0-CSF25`.
