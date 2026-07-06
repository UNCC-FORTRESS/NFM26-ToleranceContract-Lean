# dL-tolcontract

A Lean 4 + Mathlib mechanization of **Theorem 2** of *"Sensor Tolerance Contracts
for Safety Assurance in Cyber-Physical Systems"* (Jian Xiang, NFM'26) — the safety
of a *contracted CPS* via a *tolerance-cycle invariant*.

The paper introduces *tolerance contracts* — specifications of how much, how long,
and how frequently sensor abnormalities are permitted — and its central reasoning
technique (Theorem 2) reduces safety over *unbounded, recurring* tolerance cycles
to safety over a *single canonical cycle*. This repo mechanizes that reduction
end-to-end, on the [`dL-lean`](https://github.com/UNCC-FORTRESS/dL-formalization-Lean)
foundation, over the real Q-safety margin of
[`dL-qsafety`](https://github.com/UNCC-FORTRESS/HSCC26-Qsafety-Lean) and reusing the
timed Q-safety of
[`dL-caltiming`](https://github.com/UNCC-FORTRESS/CSF25-Timed-Qsafety-Lean) (CSF'25).

## Status

`lake build` green · `grep -rn sorry` clean · `#print axioms` =
`propext / Classical.choice / Quot.sound` only, on every theorem.

The recurring→single-cycle reduction — Theorem 2's contribution — is mechanized
end-to-end, boundary-granular, over the real signed safety margin. What remains as
hypotheses are exactly the *single-cycle* timed-Q-safety facts the paper itself
imports from prior work ("Item 4 and 5 … not the focus of this work").

| File | Content |
|---|---|
| [`Lemma1.lean`](DLTolContract/Lemma1.lean) | **Lemma 1** (time-shift invariance) via relative-timing simulation |
| [`Theorem2Quant.lean`](DLTolContract/Theorem2Quant.lean) | quantitative reduction over the signed distance `Dist` |
| [`Theorem2Induction.lean`](DLTolContract/Theorem2Induction.lean) | recurring→single-cycle loop induction; **`theorem2_quant`** capstone |
| [`Item6.lean`](DLTolContract/Item6.lean) | Item 6 (`τ ≤ tm ≤ δ−ϵ`) tightness |
| [`Theorem2Reduction.lean`](DLTolContract/Theorem2Reduction.lean) | Boolean shadow of the reduction |
| [`Theorem2.lean`](DLTolContract/Theorem2.lean) | `tc`-purity tightness witness |
| [`Contract.lean`](DLTolContract/Contract.lean) · [`Corrected.lean`](DLTolContract/Corrected.lean) | contract-governance program `tc-hp` and the contracted CPS `α*c` |

---

## Theorem 2 — safety of contracted CPS via tolerance-cycle invariant

Theorem 2 reduces safety over unbounded recurring tolerance cycles to safety over a
single canonical cycle. The reduction is mechanized in full.

### The capstone

[`theorem2_quant`](DLTolContract/Theorem2Induction.lean) — every state reachable by
the contracted CPS `α*c` has Q-safety margin `≥ min(u, u₁)`, i.e. the paper's
`T-safe^[0,∞)_{u₂}` with `u₂ ≥ min(u,u₁)`, expressed over
[`dL-qsafety`](https://github.com/UNCC-FORTRESS/HSCC26-Qsafety-Lean)'s real signed
distance `Dist`. Everything unbounded/recurring is discharged; the residual premises
are the *single-cycle* obligations the paper imports from prior work.

### Three layers

1. **Lemma 1 — time-shift invariance** ([`Lemma1.lean`](DLTolContract/Lemma1.lean)).
   An abnormality start at an arbitrary time is realigned to the canonical cycle by
   translating the timing variables `{tc,tab,tcd}`. Mechanized as a **shift
   equivariance**, *not* a frame-lemma instance (the program reads `tc`, so
   `tc ∈ FV(α*c)` and coincidence's agreement premise fails — a relative-timing
   simulation is required instead). The crux
   [`tcHPfixed_equivariant`](DLTolContract/Lemma1.lean) proves `tc-hp` equivariant
   because its guards test only *differences* `tc−tab`, `tc−tcd`, and its
   assignments `tab:=tc`/`tcd:=tc` commute with the translation;
   [`cCPSfixed_equivariant`](DLTolContract/Lemma1.lean) lifts through
   `seq`/`choice`/`star`; [`lemma1`](DLTolContract/Lemma1.lean) assembles it.

2. **Quantitative reduction** ([`Theorem2Quant.lean`](DLTolContract/Theorem2Quant.lean)).
   [`abnormality_phase_margin`](DLTolContract/Theorem2Quant.lean) — Lemma 1 carries
   the safety **margin** across the shift (Item 4 at the canonical start,
   transported by coincidence since `Dist` is physical);
   [`theorem2_reduction_quant`](DLTolContract/Theorem2Quant.lean) splits normal /
   abnormality phases; [`tsafe_margin_lb`](DLTolContract/Theorem2Quant.lean) ties
   Items 4/5 to `dL-caltiming`'s `TSafe` via `IsGLB.1`.

3. **Recurring→single-cycle loop induction**
   ([`Theorem2Induction.lean`](DLTolContract/Theorem2Induction.lean)).
   [`phase_invariant`](DLTolContract/Theorem2Induction.lean) proves the
   boundary-granular `Phase` invariant holds at every reachable loop boundary by
   `ReflTransGen` induction;
   [`hClassify_of_phase`](DLTolContract/Theorem2Induction.lean) discharges the phase
   decomposition. Boundary-granular is the faithful granularity: Theorem 2's
   conclusion `T-safe^[0,∞)` is Q-safety over the loop's strongest-postcondition
   (boundary-reachable states); the mid-body abnormality starts are proof-internal.

### Item 6 is exactly tight

[`Item6.lean`](DLTolContract/Item6.lean) unfolds the connecting-control-cycle
condition inside recovery: after Item 5 re-establishes `ϕinv` at recovery time
`tm`, one normal cycle must complete within the cooldown `[tm, δ]` (the controller
fires every `≤ ϵ`, so it finishes by `tm+ϵ`) to carry `ϕinv` to the next
abnormality (`≥ δ`).
[`item6_equiv`](DLTolContract/Item6.lean) shows this condition is **exactly**
`τ ≤ tm ≤ δ−ϵ` — Item 6's stated form, neither stronger nor weaker.
[`item6_epsilon_tight`](DLTolContract/Item6.lean): the `−ϵ` is precisely one
max-latency control cycle of slack (drop it and `tm=δ` overruns).
[`item6_tau_tight`](DLTolContract/Item6.lean): `τ ≤ tm` is the post-abnormality
requirement. Both bounds load-bearing.

---

## Machinery, connections, and auxiliary results

### (i) Main machinery built here

* **Shift-equivariance framework** ([`Lemma1.lean`](DLTolContract/Lemma1.lean)) —
  `shiftBy` (timing-variable translation), the `Equivariant` predicate, its closure
  under `seq`/`choice`/`star`, and atomic equivariance lemmas (guards, clock
  assignments, constant assignments). The reusable core behind Lemma 1's
  relative-timing simulation.
* **Boundary-granular phase invariant**
  ([`Theorem2Induction.lean`](DLTolContract/Theorem2Induction.lean)) — `Phase` and
  the loop-induction lift that reduces the unbounded loop to single-cycle
  obligations.
* **Contract-governance construction**
  ([`Contract.lean`](DLTolContract/Contract.lean),
  [`Corrected.lean`](DLTolContract/Corrected.lean)) — the boolean-as-real encoding,
  the two-case `tc-hp` core, the contracted CPS `α*c = (sensing ; tc-hp ;
  ctrl_logic ; plant)*`, and the fresh-variable bookkeeping the equivariance proofs
  route through.

### (ii) Connections to other repos

All pinned to released milestone tags (see [`lakefile.toml`](lakefile.toml)):

* [`dL-lean`](https://github.com/UNCC-FORTRESS/dL-formalization-Lean) `@ v0.1.0-DI` —
  dL syntax, `⟦·⟧`, `FV`/`BV`/`MBV`, coincidence + bound-effect (the frame
  metatheory Lemma 1 routes through), loop induction (`ReflTransGen`).
* [`dL-qsafety`](https://github.com/UNCC-FORTRESS/HSCC26-Qsafety-Lean) `@ v0.1.0-HSCC23` —
  the signed safety distance `Dist`, over which the quantitative reduction is stated.
* [`dL-caltiming`](https://github.com/UNCC-FORTRESS/CSF25-Timed-Qsafety-Lean) `@ v0.1.0-CSF25` —
  timed Q-safety `TSafe` (`= IsGLB (Dist.val '' spTimed …) u`), the exact object of
  Theorem 2's Items 4/5. `tsafe_margin_lb` confirms the reuse is faithful.

### (iii) Auxiliary results — what the mechanization pins down

Same discipline as the CSF'25 work: make every load-bearing assumption explicit.

* **`tc`-purity is the intended assumption of Lemma 1, and it is load-bearing.**
  The realignment is behavior-preserving only if `ctrl_logic`/`plant` do not read
  the absolute value of the global clock `tc` (the paper's water tank satisfies
  this: `ctrl` reads only the local clock `tl`, `plant` reads `tc` only via
  `tc'=1`). The mechanization carries this as explicit component-equivariance
  hypotheses; the witness
  [`lemma1_countermodel`](DLTolContract/Theorem2.lean) (`ctrl_logic ≡ z := tc`)
  demonstrates that dropping it breaks the lemma. Same clock-variable shape as the
  CSF'25 `tg`-monotonicity assumption.

* **The base case needs `ϕinv` at the abnormality onset — an explicit premise.**
  Item 3 preserves `ϕinv` only across *normal* cycles; the abnormality onset
  (sensor havoc `x_s := *` then the abnormal branch) is not one, so `ϕinv` at the
  abnormality start does not follow from Item 3 alone. It holds under an onset
  condition (`ϕinv` survives the havoc) — present in the paper's §5 as the stated
  sensing assumption `x_s ≥ x_p`, and carried explicitly here as a premise of the
  loop induction (`hNormalStep`). Theorem 2's *statement* is unaffected — Item 4's
  own precondition already carries `ϕinv`.

* **Item 6's `τ ≤ tm ≤ δ−ϵ` is exactly the connecting-cycle condition** — both
  bounds load-bearing, `−ϵ` precisely one max-latency cycle of slack (see above).

---

## Build

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build
```

All three foundations are git-pinned to their released milestone tags in
[`lakefile.toml`](lakefile.toml): `dL-lean @ v0.1.0-DI`,
`dL-qsafety @ v0.1.0-HSCC23`, `dL-caltiming @ v0.1.0-CSF25`.
