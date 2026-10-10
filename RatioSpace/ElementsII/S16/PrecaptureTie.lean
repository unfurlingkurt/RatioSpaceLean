/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.Automorphism
/-!
  Elements II §16, Proposition 16.13, restated (Kurt, 2026-09-15).

  **What 16.13 is.** From any two occurrences `u`, `v` the next comparison is
  one static comparison of four children: `a, b` the children of `u`, `c, d`
  the children of `v`. A support that is not captured (Theorem 16.12) holds a
  child of each parent, so it contains a tied cross pair `a, c`. This file
  proves exactly when two such children tie: their scores on the four-member
  family are equal **iff** the integer depths `t(a,b), t(a,d)` and
  `t(c,b), t(c,d)` form one of three patterns — equal as multisets, or
  `{P, P}` against `{P - 1, P + 2}` either way round.

  No iteration, no enumeration, no word-length bound, no `native_decide`. The
  proof is Lemma 16.14's two-term collision rule, `tEnd_self` and `tEnd_comm`.
-/

namespace RatioSpace
namespace Two
namespace Tie1613

open Zphi

/-- **The integer tie pattern.** The depth pairs `{p, q}` and `{r, s}`, each
    read smaller-first, are equal, or one is `{P, P}` and the other
    `{P - 1, P + 2}`. -/
def Collides (p q r s : ℕ) : Prop :=
  (min p q = min r s ∧ max p q = max r s) ∨
  (∃ P, 1 ≤ P ∧ min r s = P ∧ max r s = P ∧ min p q = P - 1 ∧ max p q = P + 2) ∨
  (∃ P, 1 ≤ P ∧ min p q = P ∧ max p q = P ∧ min r s = P - 1 ∧ max r s = P + 2)

theorem sum_minmax (p q : ℕ) :
    phiNegPow p + phiNegPow q = phiNegPow (min p q) + phiNegPow (max p q) := by
  rcases le_total p q with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, add_comm]

/-- **Two-term sums of negative powers of `φ`, both directions.** Lemma 16.14's
    fourth clause gives `→`; the identity `2φ⁻⁽ᵏ⁺¹⁾ = φ⁻ᵏ + φ⁻⁽ᵏ⁺³⁾` gives `←`. -/
theorem two_term_iff (p q r s : ℕ) :
    phiNegPow p + phiNegPow q = phiNegPow r + phiNegPow s ↔ Collides p q r s := by
  rw [sum_minmax p q, sum_minmax r s]
  constructor
  · intro h
    exact Automorphism.two_term_collision min_le_max min_le_max h
  · rintro (⟨h1, h2⟩ | ⟨P, hP, h1, h2, h3, h4⟩ | ⟨P, hP, h1, h2, h3, h4⟩)
    · rw [h1, h2]
    · rw [h1, h2, h3, h4]
      obtain ⟨k, rfl⟩ : ∃ k, P = k + 1 := ⟨P - 1, by omega⟩
      rw [show k + 1 - 1 = k by omega, show k + 1 + 2 = k + 3 by omega,
        ← (Automorphism.collision_identities k).1, two_mul]
    · rw [h1, h2, h3, h4]
      obtain ⟨k, rfl⟩ : ∃ k, P = k + 1 := ⟨P - 1, by omega⟩
      rw [show k + 1 - 1 = k by omega, show k + 1 + 2 = k + 3 by omega,
        ← (Automorphism.collision_identities k).1, two_mul]

/-- **Proposition 16.13, restated.** In the four-member family `[a, b, c, d]`,
    `a` and `c` receive equal scores exactly when their depths to the other two
    members collide in the integer pattern. Nothing is assumed about the
    addresses: every tie between two children of different parents, at any
    depth and any word length, is of this form. -/
theorem prop_16_13_tie (a b c d : IPres) :
    coherenceOf [a, b, c, d] a = coherenceOf [a, b, c, d] c ↔
      Collides (tEnd a b) (tEnd a d) (tEnd c b) (tEnd c d) := by
  rw [← two_term_iff]
  have ha : coherenceOf [a, b, c, d] a =
      (1 + phiNegPow (tEnd a c)) + (phiNegPow (tEnd a b) + phiNegPow (tEnd a d)) := by
    simp only [coherenceOf, tensions, coherence, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, tEnd_self, phiNegPow_zero]
    abel
  have hc : coherenceOf [a, b, c, d] c =
      (1 + phiNegPow (tEnd a c)) + (phiNegPow (tEnd c b) + phiNegPow (tEnd c d)) := by
    simp only [coherenceOf, tensions, coherence, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, tEnd_self, phiNegPow_zero]
    rw [tEnd_comm c a]
    abel
  rw [ha, hc, add_right_inj]

/-- The admitted family's storage order does not enter (Theorem 8.9): the same
    statement for any listing of the four children. -/
theorem prop_16_13_tie_perm {fam : List IPres} (a b c d : IPres)
    (h : fam.Perm [a, b, c, d]) :
    coherenceOf fam a = coherenceOf fam c ↔
      Collides (tEnd a b) (tEnd a d) (tEnd c b) (tEnd c d) := by
  rw [coherenceOf_perm h, coherenceOf_perm h]
  exact prop_16_13_tie a b c d

#print axioms two_term_iff
#print axioms prop_16_13_tie
#print axioms prop_16_13_tie_perm

end Tie1613
end Two
end RatioSpace
