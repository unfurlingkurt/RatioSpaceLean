/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S07.RelativeEncounterMatrix
/-!
  Elements I §7, Definition 7.5: Directional admission.

  **Book statement, closing paragraph of Definition 7.5.** Contact
  states that two frames meet unimodularly; admission states that one is
  reachable from the other through the permitted directed grammar. The
  sentence is about the encounter of two frames.

  **The encounter witness.** `admission_is_not_contact`
  (`Question.lean`) proves `S ∉ Mplus`. `S` has determinant one, but it is
  not the encounter of any two observers, so it does not witness the book's
  sentence. The witness below is an encounter.

  * `g110_S_not_encounter`: for every two observers, `encounter O P ≠ S`.
    If `Q = S` then `P.matrix = O.matrix * S`, whose second column is
    `(-a, -c)`; both matrices are nonnegative, so `a = c = 0`, against
    `det M_O = 1`.
  * `g110_contact_without_admission`: the encounter of the observers at the
    canonical frame with words `R` and `L` has determinant one, and neither
    observer is forward admissible to the other. The matrix is `⟨0, -1, 1, 1⟩`
    (`g110_witness_matrix`).
-/

namespace RatioSpace
namespace Gaps
namespace G1_10

open Mat2 Word Frame Pres

/-- A product of nonnegative matrices is nonnegative. -/
theorem g110_nonneg_mul {M N : Mat2} (hM : Nonneg M) (hN : Nonneg N) :
    Nonneg (M * N) := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  obtain ⟨k1, k2, k3, k4⟩ := hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Int.add_nonneg (Int.mul_nonneg h1 k1) (Int.mul_nonneg h2 k3)
  · exact Int.add_nonneg (Int.mul_nonneg h1 k2) (Int.mul_nonneg h2 k4)
  · exact Int.add_nonneg (Int.mul_nonneg h3 k1) (Int.mul_nonneg h4 k3)
  · exact Int.add_nonneg (Int.mul_nonneg h3 k2) (Int.mul_nonneg h4 k4)

/-- Every observer's accumulated transform is nonnegative. -/
theorem g110_matrix_nonneg (O : Observer) : Nonneg O.matrix :=
  g110_nonneg_mul (Frame.toMat2_nonneg O.start) (nonneg_G O.word)

/-- **The witness `S` is not an encounter.** No two observers meet with
    relative matrix `S`, so `admission_is_not_contact` does not speak about
    the encounter of two frames. -/
theorem g110_S_not_encounter (O P : Observer) : encounter O P ≠ S := by
  intro h
  have hdet := G1_11.g111_det_matrix O
  have hP : P.matrix = O.matrix * S := by
    calc P.matrix = 1 * P.matrix := (one_mul' _).symm
      _ = (O.matrix * inv2 O.matrix) * P.matrix := by
          rw [mul_inv2_of_det _ hdet]
      _ = O.matrix * encounter O P := by rw [encounter, mul_assoc']
      _ = O.matrix * S := by rw [h]
  have hn := g110_matrix_nonneg P
  rw [hP] at hn
  obtain ⟨hOa, -, hOc, -⟩ := g110_matrix_nonneg O
  obtain ⟨-, hb, -, hd⟩ := hn
  cases hM : O.matrix with | mk a b c d =>
  rw [hM] at hb hd hOa hOc hdet
  have hb' : 0 ≤ a * -1 + b * 0 := hb
  have hd' : 0 ≤ c * -1 + d * 0 := hd
  have ha0 : a = 0 := by
    have : a * -1 + b * 0 = -a := by ring
    rw [this] at hb'
    exact Int.le_antisymm (Int.neg_nonneg.mp hb') hOa
  have hc0 : c = 0 := by
    have : c * -1 + d * 0 = -c := by ring
    rw [this] at hd'
    exact Int.le_antisymm (Int.neg_nonneg.mp hd') hOc
  have hdet' : a * d - b * c = 1 := hdet
  rw [ha0, hc0] at hdet'
  have : (0 : ℤ) * d - b * 0 = 0 := by ring
  rw [this] at hdet'
  exact absurd hdet' (by decide)

/-- The observer at the canonical frame who has taken one `R` step. -/
def g110_O : Observer := ⟨Frame.empty, [true], 1⟩

/-- The observer at the canonical frame who has taken one `L` step. -/
def g110_P : Observer := ⟨Frame.empty, [false], 1⟩

theorem g110_witness_matrix : encounter g110_O g110_P = ⟨0, -1, 1, 1⟩ := by
  decide

/-- **Definition 7.5, closing paragraph, witnessed by an encounter.** Two
    observers meet unimodularly and neither reaches the other forward: contact
    is not admission. -/
theorem g110_contact_without_admission :
    (encounter g110_O g110_P).det = 1 ∧ forwardAdmissible g110_O g110_P = false ∧
      forwardAdmissible g110_P g110_O = false :=
  ⟨G1_11.g111_encounter_det _ _, by decide, by decide⟩

end G1_10
end Gaps
end RatioSpace
