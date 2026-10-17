/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S09.Question
/-!
  Elements I §7, Definition 7.3 Relative encounter matrix.

  **Book statement.** "It is exactly unimodular: \(\det Q_{O,P}=1\)."

  **The determinant of `encounter O P := inv2 O.matrix * P.matrix`**
  (`Question.lean`). The pieces are in the tree:
  `det_mul` (`Braid.lean`), `det_toMat2` and `det_G` (`Walk.lean`).

  **Here.** The adjugate keeps the determinant (`g111_det_inv2`), every
  observer's accumulated transform has determinant one (`g111_det_matrix`, the
  same fact as `Minimal.det_matrix`, restated here so this file needs only
  `Question`), and the encounter is exactly unimodular (`g111_encounter_det`).
  All by `ring` and rewriting; no ordered-ring automation.
-/

namespace RatioSpace
namespace Gaps
namespace G1_11

open Mat2 Word Frame Pres

/-- The adjugate has the same determinant. -/
theorem g111_det_inv2 (M : Mat2) : (inv2 M).det = M.det := by
  cases M with | mk a b c d =>
  change d * a - -b * -c = a * d - b * c
  ring

/-- `det M_O = 1`: the declared start is a frame and the word is a product of
    generators. -/
theorem g111_det_matrix (O : Observer) : O.matrix.det = 1 := by
  rw [Observer.matrix, det_mul, Frame.det_toMat2, det_G]
  rfl

/-- **Definition 7.3.** The relative encounter matrix is exactly unimodular:
    `det Q_{O,P} = 1`. -/
theorem g111_encounter_det (O P : Observer) : (encounter O P).det = 1 := by
  rw [encounter, det_mul, g111_det_inv2, g111_det_matrix, g111_det_matrix]
  rfl

end G1_11
end Gaps
end RatioSpace
