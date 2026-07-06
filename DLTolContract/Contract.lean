/-
Copyright (c) 2026 dL-tolcontract contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-tolcontract contributors
-/
import DLLean

/-!
# Contract governance — building blocks

The syntactic pieces of the contract-governance program `tc-hp` (NFM'26, Fig 6),
on the dL-lean foundation, over which the corrected contracted CPS `α*c`
([`Corrected.lean`](Corrected.lean)) and Theorem 2 are built:

* the boolean-as-real encoding of the flag `cd` and the marker `_tc`;
* the distinguished-variable record `Scheme` — the global clock `tc = clk` (in
  `Var(α)`) and the fresh auxiliaries `cd, tab, tcd, _tc`;
* the two guarded branches of `tc-hp` (`normalContinue`/`normalStart`,
  `abnormalStart`/`abnormalContinue`), whose guards test only the *differences*
  `tc − tab`, `tc − tcd` — the property Lemma 1's shift equivariance rests on.

Boolean variables (`cd`) are not primitive in dL; the paper's footnote 2 says
they "can be encoded". We encode a Boolean `b` as a real with the convention
`true ≡ (b = 1)`, `false ≡ (b = 0)` (`bTrue`/`bFalse`/`setTrue`/`setFalse`).
The marker `_tc` uses the same convention.
-/

namespace DLTol

open DL

variable {V : Type*}

/-! ## Boolean-as-real encoding (footnote 2) -/

/-- `?b` guard: the Boolean variable `b` is true, encoded `b = 1`. -/
def bTrue (b : V) : Formula V := .cmp .eq (.var b) (.const 1)

/-- `b := true`, encoded `b := 1`. -/
def setTrue (b : V) : Program V := .assign b (.const 1)

/-- `b := false`, encoded `b := 0`. -/
def setFalse (b : V) : Program V := .assign b (.const 0)

/-- `?¬b`: the guard `¬(b = 1)`.

NOTE: we read the paper's `¬cd` as the logical negation of the `?cd` guard, i.e.
`¬(cd = 1)`, rather than `cd = 0`. This makes the branch pair `?cd ∪ ?¬cd`
*exhaustive* for an arbitrary initial real value of `cd` (the precondition need
not initialize `cd`), which is what branch reachability relies on. Once
`cd` has been assigned via `setTrue`/`setFalse` it is `∈ {0,1}` and the two
readings coincide. -/
def bFalse (b : V) : Formula V := .neg (bTrue b)

/-! ## The distinguished variables of contract governance

`tc-hp` reads the global clock `clk` (the CPS's own time variable `tc`, which
lives in `Var(α)`) and writes the four fresh auxiliary variables
`cd, tab, tcd, tcAcc` (the paper's `cd, tab, tcd, _tc`). Bundled so the branch
programs read cleanly and freshness/distinctness is stated over one record. -/
structure Scheme (V : Type*) where
  /-- cooldown phase flag `cd`. -/
  cd : V
  /-- start time of the current abnormality duration `tab`. -/
  tab : V
  /-- start time of the current cooldown duration `tcd`. -/
  tcd : V
  /-- acceptance marker `_tc`. -/
  tcAcc : V
  /-- global clock `tc` (belongs to `Var(α)`, only read by `tc-hp`). -/
  clk : V

/-! ## The `tc-hp` branches (Figure 6)

The two guarded cases of `tc-hp` — normal (`ψn`) and tolerable-abnormal
(`¬ψn ∧ ψt`) — each split on the cooldown flag `cd`. `Corrected.lean` assembles
them into the marker-fixed governance program. -/

/-- Normal case, cooldown already running: `?cd`. -/
def normalContinue (S : Scheme V) : Program V := .test (bTrue S.cd)

/-- Normal case, cooldown starts: `?¬cd ; cd := true ; tcd := tc`. -/
def normalStart (S : Scheme V) : Program V :=
  .seq (.test (bFalse S.cd)) (.seq (setTrue S.cd) (.assign S.tcd (.var S.clk)))

/-- Abnormality starts (was in cooldown, and it is long enough):
`?cd ; cd := false ; ?(tc − tcd ≥ δ) ; tab := tc`. -/
def abnormalStart (S : Scheme V) (δ : ℝ) : Program V :=
  .seq (.test (bTrue S.cd))
    (.seq (setFalse S.cd)
      (.seq (.test (.cmp .ge (.binop .sub (.var S.clk) (.var S.tcd)) (.const δ)))
        (.assign S.tab (.var S.clk))))

/-- Abnormality continues (not in cooldown, duration bound holds):
`?¬cd ; ?(tc − tab ≤ τ)`. -/
def abnormalContinue (S : Scheme V) (τ : ℝ) : Program V :=
  .seq (.test (bFalse S.cd))
    (.test (.cmp .le (.binop .sub (.var S.clk) (.var S.tab)) (.const τ)))

end DLTol
