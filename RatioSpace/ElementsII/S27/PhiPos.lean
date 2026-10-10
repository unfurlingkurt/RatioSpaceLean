/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S05.Zphi
/-!
  Positivity and strict decrease of `φ⁻ⁿ` in `ℤ[φ]`, with no `Classical.choice`.

  Elements I's `Zphi.mul_pos`, and Mathlib's generic `pow_pos`/`sub_pos`,
  reach `Classical.choice` through the ordered-ring hierarchy. Every general
  comparison of golden-ratio powers in §16 (Lemma 16.14's collision clause,
  Theorem 16.11's Step 1 margins) needs `0 < φ⁻ⁿ` for all `n`, so it is proved
  once here from integers alone:

    * the closed form `φ⁻ⁿ = (−1)ⁿF(n+1) + (−1)ⁿ⁺¹F(n)·φ` (`phiNegPow_eq`);
    * its image in `ℤ√5` has components `∓(2F(n+1) − F(n))` and `±F(n)`;
    * Cassini, `F(n+1)² − F(n+1)F(n) − F(n)² = (−1)ⁿ`, makes
      `(2F(n+1) − F(n))² − 5F(n)² = 4(−1)ⁿ`, which is never `0` and has the
      sign that forbids the order `Nonnegg` would need.

  Strict decrease then comes additively: `φ⁻ⁿ = φ⁻⁽ⁿ⁺¹⁾ + φ⁻⁽ⁿ⁺²⁾`.
-/

namespace RatioSpace
namespace Two
namespace PhiPos

open Zphi

theorem cassini (n : ℕ) :
    ((Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib (n + 1) * Nat.fib n - (Nat.fib n : ℤ) ^ 2) =
      (-1) ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 from rfl, Nat.fib_add_two, Nat.cast_add,
      show ((-1 : ℤ)) ^ (k + 1) = (-1) ^ k * (-1) from pow_succ _ _, ← ih]
    ring

theorem fib_le_succ (n : ℕ) : Nat.fib n ≤ Nat.fib (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    change Nat.fib (k + 1) ≤ Nat.fib (k + 2)
    rw [Nat.fib_add_two]; omega

theorem neg_one_pow_cases (n : ℕ) : (-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [pow_succ]
    rcases ih with h | h <;> rw [h] <;> decide

/-- **`0 < φ⁻ⁿ`, for every `n`, from integers.** Writing `L = 2F(n+1) − F(n)`,
    the image of `φ⁻ⁿ` in `ℤ√5` is `(−L, F(n))` for even `n` and `(L, −F(n))` for
    odd `n`, and Cassini gives `L² = 5F(n)² ± 4`: in each case exactly the
    inequality `Nonnegg` would need fails. -/
theorem phiNegPow_pos (n : ℕ) : 0 < phiNegPow n := by
  rw [lt_def, phiNegPow_eq]
  obtain ⟨L, hL⟩ : ∃ L, Nat.fib (n + 1) + Nat.fib (n + 1) = Nat.fib n + L :=
    ⟨_, (Nat.add_sub_cancel' (by have := fib_le_succ n; omega)).symm⟩
  have hLz : (L : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 1) - Nat.fib n := by
    have h := congrArg (fun x : ℕ => (x : ℤ)) hL
    simp only [Nat.cast_add] at h
    omega
  have hgap : (L : ℤ) * L = 5 * ((Nat.fib n : ℤ) * Nat.fib n) + 4 * (-1) ^ n := by
    rw [hLz, ← cassini n]; ring
  have hsucc : (-1 : ℤ) ^ (n + 1) = (-1) ^ n * (-1) := pow_succ _ _
  change ¬ Zsqrtd.Nonnegg 5 1
      (2 * (0 : Zphi).a + (0 : Zphi).b +
        -(2 * ((-1) ^ n * (Nat.fib (n + 1) : ℤ)) + (-1) ^ (n + 1) * (Nat.fib n : ℤ)))
      ((0 : Zphi).b + -((-1) ^ (n + 1) * (Nat.fib n : ℤ)))
  rcases neg_one_pow_cases n with hs | hs
  · have hre : 2 * (0 : Zphi).a + (0 : Zphi).b +
        -(2 * ((-1) ^ n * (Nat.fib (n + 1) : ℤ)) + (-1) ^ (n + 1) * (Nat.fib n : ℤ)) =
          -((L : ℕ) : ℤ) := by
      rw [hsucc, hs, hLz]; change (0 : ℤ) + _ = _; ring
    have him : (0 : Zphi).b + -((-1) ^ (n + 1) * (Nat.fib n : ℤ)) = ((Nat.fib n : ℕ) : ℤ) := by
      rw [hsucc, hs]; change (0 : ℤ) + _ = _; ring
    rw [hre, him, Zsqrtd.nonnegg_neg_pos]
    intro hsq
    unfold Zsqrtd.SqLe at hsq
    have hz := Int.ofNat_le.mpr hsq
    simp only [Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hz
    rw [one_mul, mul_assoc] at hz
    rw [hs] at hgap
    generalize (L : ℤ) * L = v at hz hgap
    generalize (Nat.fib n : ℤ) * Nat.fib n = u at hz hgap
    omega
  · have hre : 2 * (0 : Zphi).a + (0 : Zphi).b +
        -(2 * ((-1) ^ n * (Nat.fib (n + 1) : ℤ)) + (-1) ^ (n + 1) * (Nat.fib n : ℤ)) =
          ((L : ℕ) : ℤ) := by
      rw [hsucc, hs, hLz]; change (0 : ℤ) + _ = _; ring
    have him : (0 : Zphi).b + -((-1) ^ (n + 1) * (Nat.fib n : ℤ)) = -((Nat.fib n : ℕ) : ℤ) := by
      rw [hsucc, hs]; change (0 : ℤ) + _ = _; ring
    rw [hre, him, Zsqrtd.nonnegg_pos_neg]
    intro hsq
    unfold Zsqrtd.SqLe at hsq
    have hz := Int.ofNat_le.mpr hsq
    simp only [Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hz
    rw [one_mul, mul_assoc] at hz
    rw [hs] at hgap
    generalize (L : ℤ) * L = v at hz hgap
    generalize (Nat.fib n : ℤ) * Nat.fib n = u at hz hgap
    omega

/-- `φ⁻ⁿ = φ⁻⁽ⁿ⁺¹⁾ + φ⁻⁽ⁿ⁺²⁾`. -/
theorem phiNegPow_rec (n : ℕ) :
    phiNegPow n = phiNegPow (n + 1) + phiNegPow (n + 2) := by
  have h : phiNegPow (n + 1) + phiNegPow (n + 2) =
      phiNegPow n * (phiNegPow 1 + phiNegPow 2) := by
    unfold phiNegPow; ring
  rw [h, phiNegPow_one_add_two, mul_one]

/-- Strict decrease, additively: the gap is `φ⁻⁽ⁿ⁺²⁾ > 0`. -/
theorem phiNegPow_succ_lt (n : ℕ) : phiNegPow (n + 1) < phiNegPow n :=
  calc phiNegPow (n + 1) < phiNegPow (n + 1) + phiNegPow (n + 2) :=
        lt_add_of_pos_right _ (phiNegPow_pos (n + 2))
    _ = phiNegPow n := (phiNegPow_rec n).symm

theorem phiNegPow_anti_le {m n : ℕ} (h : m ≤ n) : phiNegPow n ≤ phiNegPow m := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans (le_of_lt (phiNegPow_succ_lt _)) ih

theorem phiNegPow_strict {m n : ℕ} (h : m < n) : phiNegPow n < phiNegPow m :=
  lt_of_le_of_lt (phiNegPow_anti_le h) (phiNegPow_succ_lt m)

theorem phiNegPow_inj {m n : ℕ} (heq : phiNegPow m = phiNegPow n) : m = n := by
  rcases Nat.lt_trichotomy m n with h | h | h
  · exact absurd heq (ne_of_gt (phiNegPow_strict h))
  · exact h
  · exact absurd heq.symm (ne_of_gt (phiNegPow_strict h))

#print axioms cassini
#print axioms fib_le_succ
#print axioms phiNegPow_pos
#print axioms phiNegPow_succ_lt
#print axioms phiNegPow_strict
#print axioms phiNegPow_inj

end PhiPos
end Two
end RatioSpace
