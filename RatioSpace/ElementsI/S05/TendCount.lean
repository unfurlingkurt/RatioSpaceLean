/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S05.Depth
/-!
  Elements I Def 5.4: how often `T_end` fails the triangle inequality in the
  box of components 1 to 6, proved by the kernel.

  `Depth.lean` proves that `T_end` is not a metric with two witnesses
  (`Tend_not_triangle`, `Tend_not_triangle_again`). The ledger's Def 5.4 row
  also reported an exhaustive count, "5,332 of 46,656 triples violate", that
  came from `experiments/tend_triangle_search.py` and stood in a Lean ledger
  with no Lean behind it (audit 2026-09-26, E1-A15). This file proves it.

  What is proved, over `boxPres 6`, the 36 interior presentations `p:q` with
  `1 ≤ p, q ≤ 6` (presentations, not values: `1:1` and `2:2` are both in it):
  * `boxTriples_six_length`: 46,656 ordered triples `(A, B, C)`.
  * `Tend_box_six_violations`: exactly 5,332 of them have
    `T_end(A,B) + T_end(B,C) < T_end(A,C)`.
  * `Tend_box_six_excess_le`: on every triple the excess is at most 25.
  * `Tend_box_six_excess_attained`: 25 is reached at `A = 1:6`, `B = 1:1`,
    `C = 6:1`, where `T_end(A,C) = 35` against `5 + 5`.

  Every count is the kernel's own evaluation of `Tend` (`decide +kernel`):
  no script, no `native_decide`. Only the root `RatioSpace.lean` imports this
  file, so its evaluation time stays out of every other file's build.
-/

namespace RatioSpace
namespace Pres

/-- The interior presentations with both components in `1..n`, as a list. -/
def boxPres (n : ℕ) : List IPres :=
  (List.range n).flatMap fun i => (List.range n).map fun j =>
    ⟨i + 1, j + 1, Nat.succ_pos i, Nat.succ_pos j⟩

/-- All ordered triples drawn from `boxPres n`. -/
def boxTriples (n : ℕ) : List (IPres × IPres × IPres) :=
  (boxPres n).flatMap fun A => (boxPres n).flatMap fun B =>
    (boxPres n).map fun C => (A, B, C)

/-- The triple `(A, B, C)` violates the triangle inequality for `T_end`. -/
def TendViolates (t : IPres × IPres × IPres) : Bool :=
  decide (Tend t.1 t.2.1 + Tend t.2.1 t.2.2 < Tend t.1 t.2.2)

/-- The triple's excess is at most `k`: `T_end(A,C) ≤ T_end(A,B) + T_end(B,C) + k`. -/
def TendExcessLe (k : ℕ) (t : IPres × IPres × IPres) : Bool :=
  decide (Tend t.1 t.2.2 ≤ Tend t.1 t.2.1 + Tend t.2.1 t.2.2 + k)

theorem boxPres_six_length : (boxPres 6).length = 36 := by decide

theorem boxTriples_six_length : (boxTriples 6).length = 46656 := by decide +kernel

/-- **5,332 of the 46,656 triples violate the triangle inequality.** The
    ledger's former script count, now the kernel's. -/
theorem Tend_box_six_violations :
    ((boxTriples 6).filter TendViolates).length = 5332 := by decide +kernel

/-- **No triple in the box exceeds the triangle bound by more than 25.** -/
theorem Tend_box_six_excess_le :
    (boxTriples 6).all (TendExcessLe 25) = true := by decide +kernel

/-- **The excess 25 is attained**, on the reciprocal pair `1:6`, `6:1` around
    the root: `T_end(1:6, 6:1) = d_SB(1:36) = 35`, each half is `5`. -/
theorem Tend_box_six_excess_attained :
    Tend ⟨1, 6, by decide, by decide⟩ ⟨1, 1, by decide, by decide⟩ = 5 ∧
    Tend ⟨1, 1, by decide, by decide⟩ ⟨6, 1, by decide, by decide⟩ = 5 ∧
    Tend ⟨1, 6, by decide, by decide⟩ ⟨6, 1, by decide, by decide⟩ = 35 := by
  refine ⟨by decide, by decide, by decide⟩

end Pres
end RatioSpace
