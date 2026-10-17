/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S12.Encoding
import RatioSpace.ElementsI.S12.Continuum
/-!
  Elements I §12, Definitions 12.1 and 12.4: the §12 witnesses read `ν` at
  the anchor.

  **Book statement.** Def 12.1's fourth arrow is the coordinate reading of Def
  11.4, which is Def 1.7's `ν([p:q]) = p/q ∈ ℚ≥0 ∪ {∞}`. Def 12.4 (E1-44):
  the scalar width `p₊/q₊ − p₋/q₋ = 1/(q₋q₊)` is the coordinate realization of
  the determinant-one contact, for finite boundaries; on frames with boundary
  `1:0` the integer `q₋q₊` is defined and the scalar width is not.

  **The coordinate reading.** `coordinateOf` (`Encoding.lean`) is `Pres.nu`,
  landing in `Pres.ProjValue`, so `1:0` reads `∞` and `0:1` reads `0`;
  `Pres.realize` sends `1:0` to `0`, the value of `0:1`, and merges the two.
  `the_chain_identifies` holds by `rfl`. Arrow 4's fiber is the proportional
  class (`coordinate_fiber_is_the_class`), with
  `coordinate_many_to_one` (`2:4`, `1:2`), `coordinate_injective_on_primitive`,
  `coordinate_after_reduction_injective` (after `reduction`, arrow 4
  identifies nothing further), `coordinate_separates_the_improper_endpoints`.
  The statement "all four arrows are many-to-one" has its witness at arrow 4
  on non-primitive presentations.

  **The width.** `cellWidth_defined_iff` (`Continuum.lean`: both
  boundaries read finite under `ν` iff both denominators are positive) and
  `cellWidth_undefined_one_step_R` (upper boundary reads `∞`, no rational
  width). Both are choice-free.

  **In this file.** `g122_arrow4_is_coordinate` (arrow 4 of Def 12.1 and Def
  11.4's `coordinate` are one map, `rfl`), `g122_width_reading_on_finite`
  (on finite boundaries both `ν` readings are the finite rationals
  `cellWidth_eq` subtracts), `g122_empty_frame_width_undefined` (the canonical
  frame `F_∅` itself, named first in E1-44), `g122_R_ray_width_undefined` (every
  frame reached from `F_∅` by `R` alone, E1-44's wording).
-/
namespace RatioSpace

namespace Gaps.G1_22

open Layer

/-- **Arrow 4 of Def 12.1 is Def 11.4's `coordinate`.** One map, not two. -/
theorem g122_arrow4_is_coordinate (A : Pres) :
    coordinateOf A = coordinate.readout A := rfl

/-- **On finite boundaries the width is read through `ν`.** Both boundary
    readings are the finite rationals `cellWidth_eq` subtracts. -/
theorem g122_width_reading_on_finite (F : Frame) (hp : 0 < F.plus.q)
    (hm : 0 < F.minus.q) :
    Pres.nu F.plus = Pres.ProjValue.finite ⟨Pres.realize F.plus, Pres.realize_nonneg _⟩
    ∧ Pres.nu F.minus
        = Pres.ProjValue.finite ⟨Pres.realize F.minus, Pres.realize_nonneg _⟩ :=
  ⟨Pres.nu_eq_finite_of_q_ne_zero (Nat.pos_iff_ne_zero.mp hp),
    Pres.nu_eq_finite_of_q_ne_zero (Nat.pos_iff_ne_zero.mp hm)⟩

/-- **At the canonical frame `F_∅ = (1:0, 0:1)` the width is undefined**, and
    the integer `q₋q₊` is `0`. -/
theorem g122_empty_frame_width_undefined :
    cellWidthRecip Frame.empty = 0
    ∧ ¬ ∃ a b, Pres.nu Frame.empty.plus = Pres.ProjValue.finite a
        ∧ Pres.nu Frame.empty.minus = Pres.ProjValue.finite b := by
  refine ⟨rfl, fun h => ?_⟩
  exact absurd ((cellWidth_defined_iff _).mp h).1 (by decide)

/-- The `R` steps never move the upper boundary. -/
theorem g122_R_ray_plus (n : ℕ) :
    (Frame.stepR^[n] Frame.empty).plus = Frame.empty.plus := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih

/-- **On every frame reached from `F_∅` by `R` alone the width is undefined.**
    E1-44's "such as `F_∅` and every frame reached from it by `R` alone": the
    upper boundary stays `1:0`, reads `∞` under `ν`, and `q₋q₊ = 0`. -/
theorem g122_R_ray_width_undefined (n : ℕ) :
    Pres.nu (Frame.stepR^[n] Frame.empty).plus = Pres.ProjValue.atBoundary
    ∧ cellWidthRecip (Frame.stepR^[n] Frame.empty) = 0
    ∧ ¬ ∃ a b, Pres.nu (Frame.stepR^[n] Frame.empty).plus = Pres.ProjValue.finite a
        ∧ Pres.nu (Frame.stepR^[n] Frame.empty).minus = Pres.ProjValue.finite b := by
  have hq : (Frame.stepR^[n] Frame.empty).plus.q = 0 := by rw [g122_R_ray_plus]; rfl
  refine ⟨(Pres.nu_atBoundary_iff _).mpr hq, ?_, fun h => ?_⟩
  · unfold cellWidthRecip; rw [hq, Nat.zero_mul]
  · exact absurd ((cellWidth_defined_iff _).mp h).1 (by rw [hq]; decide)

end Gaps.G1_22

end RatioSpace
