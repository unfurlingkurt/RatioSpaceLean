/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S11.Perspective
/-!
  Elements I §11, Definition 11.4, coordinate realization: the map
  `coordinate` read.

  **Book statement.** "The exact rational realization from Definition 1.7,
  `ν([p:q]) = p/q ∈ ℚ≥0 ∪ {∞}`, assigns a conventional number-line value to a
  projective relation."

  **The map.** `coordinate : Projection Pres ProjValue := ⟨Pres.nu⟩`
  (`Perspective.lean`), Definition 1.7's `ν`, reading `1:0` as `atBoundary`. The
  rational realization `realize` sends `1:0` to `0`, the same rational as `0:1`, so a
  projection through `realize` would merge the two orientation anchors the book
  keeps apart, and its codomain has no `∞`.
  `coordinate_is_applied_after_the_loss` states
  `coordinate.Equiv oneTwo twoFour ∧ oneTwo ≠ twoFour`.

  **Added here.**
  * `g119_coordinate_equiv_iff_prop`: the equivalence `coordinate` induces is
    exactly proportional equivalence (Def 1.7's bracket, both directions).
  * `g119_coordinate_injective_on_primitive`: on primitive presentations,
    reading the same is being the same.
  * `g119_coordinate_separates_the_anchors`: `1:0` and `0:1` are not
    `coordinate`-equivalent, while `realize` reads them the same.
  * `g119_coordinate_anchorBoundary`: `1:0` reads as the boundary value, the
    book's `∞`.

  **In §12.** Arrow 4 (`coordinateOf`, `Encoding.lean`) reads `ν`; the §12
  witnesses are in `CoordinateRealizationWitnesses.lean`.
-/
namespace RatioSpace

namespace Gaps.G1_19

open Pres

/-- **The equivalence Def 11.4's projection induces is proportional
    equivalence.** Nothing finer and nothing coarser than the class. -/
theorem g119_coordinate_equiv_iff_prop {A B : Pres} :
    coordinate.Equiv A B ↔ A ~ B :=
  nu_eq_iff_prop

/-- **On primitive presentations `coordinate` is injective.** -/
theorem g119_coordinate_injective_on_primitive {A B : Pres}
    (hA : Primitive A) (hB : Primitive B) (h : coordinate.Equiv A B) : A = B :=
  nu_injective_on_primitive hA hB h

/-- **The anchors, separated.** `1:0` and `0:1` are not proportional, the
    rational reading `realize` merges them, and `coordinate` does not. -/
theorem g119_coordinate_separates_the_anchors :
    ¬ (anchorBoundary ~ anchorZero)
      ∧ realize anchorBoundary = realize anchorZero
      ∧ ¬ coordinate.Equiv anchorBoundary anchorZero :=
  nu_separates_the_anchors

/-- **`1:0` reads as the boundary**, the book's `∞`, which is not a rational. -/
theorem g119_coordinate_anchorBoundary :
    coordinate.readout anchorBoundary = Pres.ProjValue.atBoundary :=
  nu_anchorBoundary

end Gaps.G1_19

end RatioSpace

