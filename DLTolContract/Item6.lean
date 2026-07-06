/-
Copyright (c) 2026 dL-tolcontract contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-tolcontract contributors
-/
import Mathlib

/-!
# Item 6 tightness audit — `τ ≤ tm ≤ δ − ϵ`

Item 6 of Theorem 2 constrains the time point `tm`. It enters the proof only
inside `hRecovery` (`Theorem2Induction.lean`), via the **connecting control
cycle**: after Item 5 re-establishes `ϕinv` at recovery time `tm` (relative to
the abnormality start), one normal cycle `αn` must complete **within** the
cooldown window `[tm, δ]` to carry `ϕinv` forward to the next abnormality (which
cannot begin before `δ`, the minimum cooldown).

We unfold that connecting-cycle condition and confirm each bound is load-bearing:

* the cycle is **post-abnormality** (so Item 5 applies, not Item 4) iff `τ ≤ tm`
  — the abnormality duration is `≤ τ`, so `tm` must clear it;
* the cycle **completes inside the cooldown** iff `tm + ϵ ≤ δ` — the controller
  fires at least every `ϵ` (max closed-loop latency), so the connecting cycle
  finishes by `tm + ϵ`, which must not overrun `δ`.

`ConnectingFits` is exactly the conjunction of these two, and `item6_equiv` shows
it is **exactly** `τ ≤ tm ≤ δ − ϵ`. So Item 6's stated form is tight: the `−ϵ` is
precisely one max-latency control cycle of slack (`item6_epsilon_tight` — without
it, `tm = δ` fails whenever `ϵ > 0`), and `τ ≤ tm` is precisely the
post-abnormality requirement (`item6_tau_tight`).
-/

namespace DLTol

/-- The connecting control cycle fits: it is post-abnormality (`τ ≤ tm`) and
completes within the cooldown (`tm + ϵ ≤ δ`). -/
def ConnectingFits (τ tm δ ε : ℝ) : Prop := τ ≤ tm ∧ tm + ε ≤ δ

/-- **Item 6 is exactly the connecting-cycle condition.** `ConnectingFits` holds
iff `τ ≤ tm ≤ δ − ϵ` — the stated form of Item 6, not stronger or weaker. -/
theorem item6_equiv (τ tm δ ε : ℝ) :
    ConnectingFits τ tm δ ε ↔ (τ ≤ tm ∧ tm ≤ δ - ε) := by
  unfold ConnectingFits
  constructor <;> (rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩)

/-- Item 6 (stated form) suffices for the connecting cycle to fit. -/
theorem item6_sufficient (τ tm δ ε : ℝ) (h : τ ≤ tm ∧ tm ≤ δ - ε) :
    ConnectingFits τ tm δ ε := (item6_equiv τ tm δ ε).mpr h

/-- **`−ϵ` is load-bearing.** The naive bound `tm ≤ δ` (connecting cycle merely
"before the cooldown ends") is **not** enough: at `tm = δ` the cycle overruns by
`ϵ`, so `ConnectingFits` fails whenever `ϵ > 0`. The `−ϵ` is exactly the one
max-latency cycle of slack the connecting state needs. -/
theorem item6_epsilon_tight (τ δ ε : ℝ) (hε : 0 < ε) :
    ¬ ConnectingFits τ δ δ ε := by
  rintro ⟨_, h⟩; linarith

/-- More precisely: for any `tm` in the gap `δ − ϵ < tm ≤ δ` (satisfying the naive
`tm ≤ δ` but not Item 6), the connecting cycle overruns the cooldown. Countermodel
to dropping the `−ϵ`. -/
theorem item6_epsilon_needed (τ tm δ ε : ℝ) (hgap : δ - ε < tm) :
    ¬ ConnectingFits τ tm δ ε := by
  rintro ⟨_, h⟩; linarith

/-- **`τ ≤ tm` is load-bearing.** If `tm < τ`, the state at `tm` may still be
within the abnormality duration (bounded by `τ`), so Item 5 (which measures
post-abnormality recovery) does not apply there. -/
theorem item6_tau_tight (τ tm δ ε : ℝ) (h : tm < τ) :
    ¬ ConnectingFits τ tm δ ε := by
  rintro ⟨ht, _⟩; linarith

/-- **Non-vacuity: the Item 6 window is inhabited exactly when `τ + ϵ ≤ δ`.** A
valid `tm` exists iff the minimum cooldown `δ` leaves room for the max abnormality
`τ` plus one latency cycle `ϵ` — the design constraint the contract parameters
must satisfy for Theorem 2 to apply at all. -/
theorem item6_window_nonempty (τ δ ε : ℝ) (h : τ + ε ≤ δ) :
    ∃ tm, ConnectingFits τ tm δ ε :=
  ⟨τ, le_refl τ, by linarith⟩

/-- …and if `δ < τ + ϵ` the window is empty — no `tm` works. -/
theorem item6_window_empty (τ δ ε : ℝ) (h : δ < τ + ε) :
    ¬ ∃ tm, ConnectingFits τ tm δ ε := by
  rintro ⟨tm, h1, h2⟩; linarith

end DLTol
