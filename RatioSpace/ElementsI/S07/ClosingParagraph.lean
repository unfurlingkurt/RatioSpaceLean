/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S06.State
import RatioSpace.ElementsI.S00.Minimal
import RatioSpace.ElementsI.S07.RelativeEncounterMatrix
/-!
  Gap G1-12 — Elements I §7, Proposition 7.2, closing paragraph.

  **Book statement (v0.22), after the proof of Proposition 7.2.** Two
  consequences. The synchronized case: if `Q = I` and both histories take the
  same step `g`, then `Q⁺ = I`. The shared step: `Q ↦ g⁻¹ Q g`, "preserving
  every declared conjugacy-invariant reception class".

  **What was missing.** Neither was stated in the Elements I tree. The
  conjugate form is `bilateral_covariance` (`State.lean`) at `gO = gP`.

  **Added.**
  * `g112_shared_step`: `bilateral_covariance` at one step `g`, the conjugate
    form `g⁻¹ Q g`.
  * `g112_synchronized`: `Q = I` and a shared step of determinant one give
    `Q⁺ = I`; `g112_synchronized_observers` is the same for two observers
    continued by one word `u` (through `Minimal.encounter_transport`).
  * `g112_conj_invariant`: the book's clause as stated. Every reading `f` of
    `Q` that is invariant under conjugation by determinant-one matrices takes
    the same value before and after a shared step of determinant one.
  * Two named instances: the determinant (`g112_conj_det`) and the trace
    (`g112_conj_trace`), and any reading built from them (`g112_conj_reading`).
    Trace and determinant do not determine a conjugacy class in `SL(2,ℤ)`
    (`⟨1,1,0,1⟩` and `⟨1,2,0,1⟩` share both and are not conjugate: the gcd of
    the entries of `M - I` differs; a known fact, not proved in this file), so
    the general form is the statement and
    these are examples of it. For an encounter the determinant is `1` on both
    sides already (`G1_11.g111_encounter_det`).
  * Admission is not such a class: `Two.Observer.prop_3_6_changes_admission`
    already shows a shared step `R` taking an admitted `Q` out of `ℳ₊`. That is
    Elements II's statement and is cited here, not repeated.
-/

namespace RatioSpace
namespace Gaps
namespace G1_12

open Mat2 Word Frame Pres

/-- **The shared step.** Both histories advance by the same `g`: `Q ↦ g⁻¹ Q g`. -/
theorem g112_shared_step (MO MP g : Mat2) :
    inv2 (MO * g) * (MP * g) = inv2 g * (inv2 MO * MP) * g :=
  bilateral_covariance MO MP g g

/-- **The synchronized case.** `Q = I` and one shared step of determinant one
    leave `Q⁺ = I`. -/
theorem g112_synchronized (MO MP g : Mat2) (hg : g.det = 1)
    (hQ : inv2 MO * MP = 1) : inv2 (MO * g) * (MP * g) = 1 := by
  rw [g112_shared_step, hQ, mul_assoc', one_mul']
  exact inv2_mul_of_det g hg

/-- The synchronized case for observers: two observers in coincident encounter
    (`Q = I`) continued by the same word stay in coincident encounter. -/
theorem g112_synchronized_observers (O P : Observer) (u : Word)
    (hQ : encounter O P = 1) :
    encounter { O with word := O.word ++ u } { P with word := P.word ++ u } = 1 := by
  rw [Minimal.encounter_transport, hQ, mul_assoc', one_mul']
  exact inv2_mul_of_det _ (det_G u)

/-- **"Preserving every declared conjugacy-invariant reception class."** A
    reading invariant under conjugation by determinant-one matrices is unchanged
    by a shared step of determinant one. -/
theorem g112_conj_invariant {α : Type} (f : Mat2 → α)
    (hf : ∀ h Q : Mat2, h.det = 1 → f (inv2 h * Q * h) = f Q)
    (MO MP g : Mat2) (hg : g.det = 1) :
    f (inv2 (MO * g) * (MP * g)) = f (inv2 MO * MP) := by
  rw [g112_shared_step]
  exact hf g _ hg

/-- The trace of a matrix. -/
def g112Trace (M : Mat2) : ℤ := M.a + M.d

/-- A shared step of determinant one keeps the determinant of `Q`. -/
theorem g112_conj_det (Q g : Mat2) (hg : g.det = 1) :
    (inv2 g * Q * g).det = Q.det := by
  rw [det_mul, det_mul, G1_11.g111_det_inv2, hg, Int.one_mul, Int.mul_one]

/-- A shared step of determinant one keeps the trace of `Q`. -/
theorem g112_conj_trace (Q g : Mat2) (hg : g.det = 1) :
    g112Trace (inv2 g * Q * g) = g112Trace Q := by
  cases Q with | mk a b c d =>
  cases g with | mk p q r s =>
  have hg' : p * s - q * r = 1 := hg
  change (s * a + -q * c) * p + (s * b + -q * d) * r
      + ((-r * a + p * c) * q + (-r * b + p * d) * s) = a + d
  calc (s * a + -q * c) * p + (s * b + -q * d) * r
        + ((-r * a + p * c) * q + (-r * b + p * d) * s)
        = (a + d) * (p * s - q * r) := by ring
    _ = a + d := by rw [hg', Int.mul_one]

/-- **"Preserving every declared conjugacy-invariant reception class"**, for
    classes declared through trace and determinant: any reading of `Q` that is a
    function of those two integers is unchanged by a shared step of determinant
    one. -/
theorem g112_conj_reading {α : Type} (f : ℤ → ℤ → α) (Q g : Mat2) (hg : g.det = 1) :
    f (g112Trace (inv2 g * Q * g)) (inv2 g * Q * g).det = f (g112Trace Q) Q.det := by
  rw [g112_conj_trace Q g hg, g112_conj_det Q g hg]

end G1_12
end Gaps
end RatioSpace
