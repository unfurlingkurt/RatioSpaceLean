/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S11.Perspective
/-!
  Gap G1-19 — Elements I §11, Definition 11.4, coordinate realization: the map
  `coordinate` read.

  **Book statement.** "The exact rational realization from Definition 1.7,
  `ν([p:q]) = p/q ∈ ℚ≥0 ∪ {∞}`, assigns a conventional number-line value to a
  projective relation."

  **What was wrong.** `coordinate` (`Perspective.lean`) was
  `⟨Pres.realize⟩ : Projection Pres ℚ`. `realize` sends `1:0` to `0`, the same
  rational as `0:1`, which is the defect D-02 repaired in Definition 1.7 by
  adding `Pres.nu`. Definition 11.4 names Definition 1.7's `ν` but was not
  repointed, so the projection merged the two orientation anchors the book keeps
  apart, and its codomain had no `∞`.

  **Changed.** `coordinate : Projection Pres ProjValue := ⟨Pres.nu⟩`.
  `coordinate_is_applied_after_the_loss` used to restate
  `reduction_identifies_proportional` and said nothing about `coordinate`; it
  now states `coordinate.Equiv oneTwo twoFour ∧ oneTwo ≠ twoFour`. Nothing else
  in the tree used `coordinate`.

  **Added here.**
  * `g119_coordinate_equiv_iff_prop`: the equivalence `coordinate` induces is
    exactly proportional equivalence (Def 1.7's bracket, both directions).
  * `g119_coordinate_injective_on_primitive`: on primitive presentations,
    reading the same is being the same.
  * `g119_coordinate_separates_the_anchors`: `1:0` and `0:1` are not
    `coordinate`-equivalent, while the old map `realize` reads them the same.
  * `g119_coordinate_anchorBoundary`: `1:0` reads as the boundary value, the
    book's `∞`.

  **Not done here.** §12 read `realize` at arrow 4 (`coordinateOf`,
  `Encoding.lean`) and in `Continuum.lean`: repointed to `ν` by gap G1-22
  (`Gaps/G1_22.lean`).
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
    old reading `realize` merged them, and `coordinate` does not. -/
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

