/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S24.Lifecycle
/-!
  Gap G2-21 · Elements II Proposition 24.3, the closing remark: "The left action in
  Proposition 24.3 is receiver transport. It is not the right action `M ↦ Mg` by
  which a presented history continues."

  `Two/Lifecycle.lean`'s `history_right_action` restates `G_snoc`, and its
  docstring's "They are different actions" is not proved. This file proves it at
  the strength the remark needs: for every unimodular `Q` and each generator `g`,
  `g⁻¹Q ≠ Qg`. So on every transported relative matrix, one appended generator
  moves `Q` by the left action and never by the right one, while the receiver's
  own matrix moves by the right action. No existing declaration is changed.

  The integer core: `g⁻¹Q = Qg` forces `c = 0, d = −a` (for `g = R`) or `b = 0,
  d = −a` (for `g = L`), so `det Q = −a²`, which is never `1` because `a² ≥ 0`.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_21

open RatioSpace.Two RatioSpace.Two.Lifecycle Mat2 Word

/-- A square integer is nonnegative, by cases on the sign (no `Classical.choice`). -/
theorem g21_sq_nonneg (a : ℤ) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -a := Int.neg_nonneg_of_nonpos h
    have := Int.mul_nonneg h' h'
    rwa [Int.neg_mul_neg] at this

/-- **`g⁻¹Q ≠ Qg` on the unimodular shell**, for both generators. -/
theorem g21_left_ne_right (Q : Mat2) (hQ : Q.det = 1) (g : Bool) :
    inv2 (gen g) * Q ≠ Q * gen g := by
  obtain ⟨a, b, c, d⟩ := Q
  have hdet : a * d - b * c = 1 := hQ
  intro h
  have h1 := congrArg Mat2.a h
  have h2 := congrArg Mat2.b h
  have h3 := congrArg Mat2.c h
  have hsq := g21_sq_nonneg a
  cases g with
  | false =>
    simp only [mul_def, inv2, gen, Bool.false_eq_true, ite_false, L] at h1 h3
    have hb0 : b = 0 := by omega
    have hda : d = -a := by omega
    rw [hb0, hda, Int.mul_neg, Int.zero_mul] at hdet
    omega
  | true =>
    simp only [mul_def, inv2, gen, ite_true, R] at h1 h2
    have hc0 : c = 0 := by omega
    have hda : d = -a := by omega
    rw [hc0, hda, Int.mul_neg, Int.mul_zero] at hdet
    omega

theorem g21_det_A (s : Bool) : (Two.A s).det = 1 := by cases s <;> decide

theorem g21_det_Qf (wx : Word) (s : Bool) (v : Word) : (Qf wx s v).det = 1 := by
  rw [transport_Q, Mat2.det_mul, det_inv2, det_G, g21_det_A, Int.one_mul]

/-- **Proposition 24.3's remark.** Appending one lawful generator `g` to the
    receiver trail moves the transported relative matrix by the left action
    `Q ↦ g⁻¹Q`, and the result is never the right action `Q ↦ Qg`. -/
theorem g21_transport_not_right_action (wx : Word) (s : Bool) (v : Word) (g : Bool) :
    Qf wx s (v ++ [g]) = inv2 (gen g) * Qf wx s v ∧
    Qf wx s (v ++ [g]) ≠ Qf wx s v * gen g :=
  ⟨transport_step wx s v g, by
    rw [transport_step]; exact g21_left_ne_right _ (g21_det_Qf wx s v) g⟩

/-- **The two actions side by side.** On the same append of `g`, the receiver's
    presented history `M_O` continues by the right action `M ↦ Mg`, the relative
    matrix `Q_f` by the left action `Q ↦ g⁻¹Q`, and the right action applied to
    `Q_f` gives a different matrix. -/
theorem g21_two_actions (wx : Word) (s : Bool) (v : Word) (g : Bool) :
    G (receiverWord wx s (v ++ [g])) = G (receiverWord wx s v) * gen g ∧
    Qf wx s (v ++ [g]) = inv2 (gen g) * Qf wx s v ∧
    Qf wx s (v ++ [g]) ≠ Qf wx s v * gen g := by
  refine ⟨?_, g21_transport_not_right_action wx s v g⟩
  unfold receiverWord
  rw [← List.append_assoc, G_snoc]

#print axioms g21_sq_nonneg
#print axioms g21_left_ne_right
#print axioms g21_det_A
#print axioms g21_det_Qf
#print axioms g21_transport_not_right_action
#print axioms g21_two_actions

end G2_21
end Gaps
end RatioSpace
