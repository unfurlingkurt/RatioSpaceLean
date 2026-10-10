/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S02.Frame
import RatioSpace.ElementsI.S05.Zphi
/-!
  Elements I Def 5.7, "φ = [1;1,1,...]": the walk `R,L,R,L,...` read against
  the exact golden element.

  `Frame.lean`'s `mid_altWord_fib` proves the middles of the walk that never
  closes are the Fibonacci presentations `F(n+2) : F(n+1)`. It says nothing
  about `φ`. `Zphi.lean` has `φ` and says nothing about the walk. This file
  connects the two (audit 2026-09-26, E1-A3).

  The connection is the **contact** of a presentation `p : q` with `φ`, the
  element `p - qφ` of `ℤ[φ]`. It is exact, and no quotient `p / q` is formed:
  `ℤ[φ]` has no fractions, and none are needed: when `q > 0`, as on the walk
  (`q = F(n+1)`), the sign of `p - qφ` is the side of `φ` the presentation
  lies on (`goldenContact_pos_iff`, `goldenContact_neg_iff`).

  What is proved:
  * `goldenContact_altWord`: the contact of the `n`-th middle is
    `(−φ⁻¹)^(n+1)`, exactly.
  * `goldenContact_altWord_signed`: its size is `φ^(−(n+1))`, which strictly
    shrinks with `n` (`phiNegPow_strictAnti`). No limit is taken.
  * `mid_altWord_below` / `mid_altWord_above`: the middles after an even
    number of letters lie below `φ`, after an odd number above it
    (`p < qφ` and `qφ < p` in the `Zphi` order).
  * `mid_altWord_straddle`: any two consecutive middles lie on opposite sides
    of `φ`, stated as a negative product of contacts.

  The reading "the walk converges to `φ`" is not formalised: there is no real
  number here, and no limit (Def 0.2).
-/

namespace RatioSpace
namespace Frame

open Zphi

/-- **The contact of a presentation with `φ`.** For `x = p : q`, the element
    `p - qφ` of `ℤ[φ]`, written as `a + bφ` with `a = p`, `b = -q`. Never zero
    (`goldenContact_ne_zero`): no presentation sits on `φ`. -/
def goldenContact (x : Pres) : Zphi := ⟨x.p, -(x.q : ℤ)⟩

/-- No presentation has contact zero with `φ`, because `1, φ` are independent
    over `ℤ` in `ℤ[φ]` (equality is componentwise) and a presentation is not
    `0 : 0`. -/
theorem goldenContact_ne_zero (x : Pres) : goldenContact x ≠ 0 := by
  intro h
  have ha : (x.p : ℤ) = 0 := congrArg Zphi.a h
  have hb : -(x.q : ℤ) = 0 := congrArg Zphi.b h
  exact x.ne_zero ⟨by exact_mod_cast ha, by omega⟩

/-- The contact is `p - qφ` in the ring, with `p` and `q` as the elements
    `⟨p, 0⟩` and `⟨q, 0⟩` of `ℤ[φ]`. -/
theorem goldenContact_eq (x : Pres) :
    goldenContact x = ⟨x.p, 0⟩ - ⟨x.q, 0⟩ * phi := by
  ext <;> simp [goldenContact, phi]

/-- `(−1)^m` in `ℤ[φ]` is the integer `(−1)^m`. -/
theorem negOne_pow (m : ℕ) : ((-1 : Zphi)) ^ m = ⟨(-1) ^ m, 0⟩ := by
  induction m with
  | zero => rfl
  | succ k ih => rw [pow_succ, ih]; ext <;> simp [pow_succ]

/-- **The audit's fix, first half.** `F(n+2) - F(n+1)φ = (−φ⁻¹)^(n+1)` in
    `ℤ[φ]`, from the closed form for the negative powers (`phiNegPow_eq`). -/
theorem fib_sub_fib_mul_phi (n : ℕ) :
    (⟨Nat.fib (n + 2), -(Nat.fib (n + 1) : ℤ)⟩ : Zphi) = (-phiInv) ^ (n + 1) := by
  rw [neg_pow, ← phiNegPow, phiNegPow_eq, negOne_pow]
  have hs : ((-1 : ℤ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by
    rw [← mul_pow, show ((-1 : ℤ) * -1) = 1 from rfl, one_pow]
  ext
  · simp only [Zphi.mul_a]
    rw [zero_mul, add_zero, ← mul_assoc, hs, one_mul]
  · simp only [Zphi.mul_b]
    rw [zero_mul, zero_mul, add_zero, add_zero, pow_succ (-1 : ℤ) (n + 1), ← mul_assoc,
      ← mul_assoc, hs, one_mul, neg_one_mul]

/-- **The walk against `φ`.** The contact of the middle after `n` letters of
    `R,L,R,L,...` with `φ` is exactly `(−φ⁻¹)^(n+1)`. -/
theorem goldenContact_altWord (n : ℕ) :
    goldenContact (mid (walk empty (altWord n))) = (-phiInv) ^ (n + 1) := by
  obtain ⟨hp, hq, -, -⟩ := mid_altWord_fib n
  rw [← fib_sub_fib_mul_phi n, goldenContact, hp, hq]

/-- **Its size, exactly.** `(−1)^(n+1)` times the contact is `φ^(−(n+1))`.
    That size is positive and strictly decreasing in `n` by the existing
    `phiNegPow_pos` and `phiNegPow_strictAnti`. No limit is taken. -/
theorem goldenContact_altWord_signed (n : ℕ) :
    (-1) ^ (n + 1) * goldenContact (mid (walk empty (altWord n))) = phiNegPow (n + 1) := by
  rw [goldenContact_altWord, phiNegPow, ← mul_pow, neg_one_mul, neg_neg]

/-- Even powers of `−φ⁻¹` are positive, odd ones negative, in the `Zphi`
    order. -/
theorem negPhiInv_pow_even (k : ℕ) : (-phiInv) ^ (2 * k) = phiNegPow (2 * k) := by
  rw [phiNegPow, pow_mul, pow_mul, neg_sq]

theorem negPhiInv_pow_odd (k : ℕ) : (-phiInv) ^ (2 * k + 1) = -phiNegPow (2 * k + 1) := by
  rw [pow_succ, negPhiInv_pow_even, phiNegPow, phiNegPow, pow_succ, mul_neg]

/-- A contact `p - qφ` is positive exactly when `qφ < p`. Routed through
    `Zphi.sub_pos`, which avoids the generic lemma's `Classical.choice`. -/
theorem goldenContact_pos_iff (x : Pres) :
    0 < goldenContact x ↔ (⟨x.q, 0⟩ : Zphi) * phi < ⟨x.p, 0⟩ := by
  rw [goldenContact_eq]; exact Zphi.sub_pos

/-- A contact `p - qφ` is negative exactly when `p < qφ`. -/
theorem goldenContact_neg_iff (x : Pres) :
    goldenContact x < 0 ↔ (⟨x.p, 0⟩ : Zphi) < ⟨x.q, 0⟩ * phi := by
  rw [goldenContact_eq, ← Zphi.sub_pos, zero_sub, neg_sub]
  exact Zphi.sub_pos

/-- **Below `φ` after an even number of letters.** `p < qφ` for the middle
    after `2k` letters: `1:1, 3:2, 8:5, ...`. -/
theorem mid_altWord_below (k : ℕ) :
    (⟨(mid (walk empty (altWord (2 * k)))).p, 0⟩ : Zphi)
      < ⟨(mid (walk empty (altWord (2 * k)))).q, 0⟩ * phi := by
  refine Zphi.sub_pos.mp ?_
  rw [← neg_sub, ← goldenContact_eq, goldenContact_altWord, negPhiInv_pow_odd, neg_neg]
  exact phiNegPow_pos _

/-- **Above `φ` after an odd number of letters.** `qφ < p` for the middle
    after `2k + 1` letters: `2:1, 5:3, 13:8, ...`. -/
theorem mid_altWord_above (k : ℕ) :
    (⟨(mid (walk empty (altWord (2 * k + 1)))).q, 0⟩ : Zphi) * phi
      < ⟨(mid (walk empty (altWord (2 * k + 1)))).p, 0⟩ := by
  rw [← goldenContact_pos_iff, goldenContact_altWord, show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
    negPhiInv_pow_even]
  exact phiNegPow_pos _

/-- **The straddle.** Any two consecutive middles of `R,L,R,L,...` lie on
    opposite sides of `φ`: the product of their contacts is negative, namely
    `−φ^(−(2n+3))`. The sides themselves are `mid_altWord_below` and
    `mid_altWord_above`. -/
theorem mid_altWord_straddle (n : ℕ) :
    goldenContact (mid (walk empty (altWord n)))
      * goldenContact (mid (walk empty (altWord (n + 1)))) = -phiNegPow (2 * (n + 1) + 1) ∧
    goldenContact (mid (walk empty (altWord n)))
      * goldenContact (mid (walk empty (altWord (n + 1)))) < 0 := by
  have e : goldenContact (mid (walk empty (altWord n)))
      * goldenContact (mid (walk empty (altWord (n + 1)))) = -phiNegPow (2 * (n + 1) + 1) := by
    rw [goldenContact_altWord, goldenContact_altWord, ← pow_add,
      show n + 1 + (n + 1 + 1) = 2 * (n + 1) + 1 by ring, negPhiInv_pow_odd]
  exact ⟨e, by rw [e]; exact neg_neg_iff_pos.mpr (phiNegPow_pos _)⟩

/-- Non-vacuity: after four letters the middle is `8:5` and its contact is
    `8 - 5φ = −φ^(−5)`, below `φ`. -/
example : goldenContact (mid (walk empty (altWord 4))) = ⟨8, -5⟩ := by decide

end Frame
end RatioSpace
