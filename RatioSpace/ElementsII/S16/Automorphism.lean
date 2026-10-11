/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S08.Coherence
import RatioSpace.ElementsII.S27.PhiPos
/-!
  Elements II §16, Lemma 16.14 — Tension automorphisms force equal coherence values.

  Four clauses: a tension-preserving permutation of the admitted family
  preserves every coherence value; hence it maps the complete maximizer set onto itself;
  in a four-member family, equal tension histograms are always realized by
  such a permutation; and two sums of two negative powers of `φ` coincide only
  when the exponent pairs agree or form `{P, P}` against `{P - 1, P + 2}`.

  The last clause is proved, not enumerated: it needs only the recurrence
  `φ⁻ⁿ = φ⁻⁽ⁿ⁺¹⁾ + φ⁻⁽ⁿ⁺²⁾` and strict decrease, both exact in `ℤ[φ]`.
-/

namespace RatioSpace
namespace Two
namespace Automorphism

open Zphi PhiPos

/-! ## Clause 1 — a tension automorphism preserves every coherence value -/

/-- **Lemma 16.14, first clause.** If `σ` permutes the admitted family and
    preserves every tension on it, then `C(σ y) = C(y)`. The book's proof is a
    reindexing of the sum by `z ↦ σ z`, and so is this one. -/
theorem coherence_invariant (fam : List IPres) (σ : IPres → IPres)
    (hperm : (fam.map σ).Perm fam)
    (ht : ∀ y ∈ fam, ∀ z ∈ fam, tEnd (σ y) (σ z) = tEnd y z)
    {y : IPres} (hy : y ∈ fam) :
    coherenceOf fam (σ y) = coherenceOf fam y := by
  unfold coherenceOf tensions coherence
  have h1 : (((fam.map σ).map (fun z => tEnd (σ y) z)).map phiNegPow).sum =
      ((fam.map (fun z => tEnd (σ y) z)).map phiNegPow).sum :=
    ((hperm.map _).map _).sum_eq
  rw [← h1, List.map_map, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro z hz
  simp only [Function.comp_apply, ht y hy z hz]

/-- **Lemma 16.14, second clause.** Such a `σ` maps the complete maximizer set
    of Definition 8.1 into itself (and, being a permutation of the
    family, onto it). -/
theorem support_invariant (fam : List IPres) (σ : IPres → IPres)
    (hperm : (fam.map σ).Perm fam)
    (ht : ∀ y ∈ fam, ∀ z ∈ fam, tEnd (σ y) (σ z) = tEnd y z)
    {y : IPres} (hy : y ∈ support fam) : σ y ∈ support fam := by
  have hyf : y ∈ fam := support_sub hy
  have hσf : σ y ∈ fam := hperm.subset (List.mem_map_of_mem hyf)
  have hmax := support_maximal hy
  unfold support
  rw [List.mem_filter]
  refine ⟨hσf, ?_⟩
  rw [List.all_eq_true]
  intro z hz
  rw [coherence_invariant fam σ hperm ht hyf]
  exact decide_eq_true (hmax z hz)

/-- **Corollary of clause 1**: two occurrences exchanged by a tension
    automorphism receive equal coherence values. -/
theorem exchanged_equal_coherence (fam : List IPres) (σ : IPres → IPres)
    (hperm : (fam.map σ).Perm fam)
    (ht : ∀ y ∈ fam, ∀ z ∈ fam, tEnd (σ y) (σ z) = tEnd y z)
    {y y' : IPres} (hy : y ∈ fam) (hswap : σ y = y') :
    coherenceOf fam y' = coherenceOf fam y := by
  rw [← hswap]; exact coherence_invariant fam σ hperm ht hy

/-! ## Clause 3 — in a four-member family, equal histograms give an automorphism

    Indexed by `Fin 4` with the two occurrences at positions `0` and `1`; any
    other placement is a relabeling. The tension matrix is symmetric with zero
    diagonal, which is `tEnd_comm`/`tEnd_self`. -/

theorem pair_perm {b c d e : ℕ} (h : [b, c].Perm [d, e]) :
    (b = d ∧ c = e) ∨ (b = e ∧ c = d) := by
  have hb : b ∈ [d, e] := h.subset (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · left; refine ⟨rfl, ?_⟩
    have := (List.Perm.cons_inv h)
    simpa using this
  · right; refine ⟨rfl, ?_⟩
    have h2 : [b, c].Perm [b, d] := h.trans (List.Perm.swap b d [])
    have := List.Perm.cons_inv h2
    simpa using this

/-- The transposition `(0 1)`, as an explicit involution of `Fin 4`. -/
def swap01 : Fin 4 → Fin 4
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 2 | _ => 3

/-- The double transposition `(0 1)(2 3)`. -/
def swap01_23 : Fin 4 → Fin 4
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 3 | _ => 2

theorem swap01_involutive : Function.Involutive swap01 := by
  intro i
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absurd hi (by omega)

theorem swap01_23_involutive : Function.Involutive swap01_23 := by
  intro i
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absurd hi (by omega)

/-- **Lemma 16.14, third clause.** In a four-member family, two occurrences
    with equal tension histograms are exchanged by a tension-preserving
    permutation: `(0 1)` when the cross tensions already match, else
    `(0 1)(2 3)`. The permutation is an explicit involution and each of the
    sixteen tension equalities is a named term, so nothing classical enters. -/
theorem four_member_exchange (T : Fin 4 → Fin 4 → ℕ)
    (hsym : ∀ i j, T i j = T j i) (hdiag : ∀ i, T i i = 0)
    (hhist : (List.ofFn (T 0)).Perm (List.ofFn (T 1))) :
    ∃ σ : Fin 4 → Fin 4, Function.Involutive σ ∧ σ 0 = 1 ∧ σ 1 = 0 ∧
      ∀ i j, T (σ i) (σ j) = T i j := by
  have e0 : List.ofFn (T 0) = [0, T 0 1, T 0 2, T 0 3] := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    change [T 0 0, T 0 1, T 0 2, T 0 3] = _
    rw [hdiag 0]
  have e1 : List.ofFn (T 1) = [T 0 1, 0, T 1 2, T 1 3] := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    change [T 1 0, T 1 1, T 1 2, T 1 3] = _
    rw [hdiag 1, hsym 1 0]
  rw [e0, e1] at hhist
  have h1 : [0, T 0 1, T 0 2, T 0 3].Perm [0, T 0 1, T 1 2, T 1 3] :=
    hhist.trans (List.Perm.swap 0 (T 0 1) _)
  have h2 := List.Perm.cons_inv (List.Perm.cons_inv h1)
  rcases pair_perm h2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨swap01, swap01_involutive, rfl, rfl, ?_⟩
    intro i j
    rcases i with ⟨_ | _ | _ | _ | n, hi⟩ <;> rcases j with ⟨_ | _ | _ | _ | m, hj⟩
    · exact (hdiag 1).trans (hdiag 0).symm
    · exact hsym 1 0
    · exact ha.symm
    · exact hb.symm
    · exact absurd hj (by omega)
    · exact hsym 0 1
    · exact (hdiag 0).trans (hdiag 1).symm
    · exact ha
    · exact hb
    · exact absurd hj (by omega)
    · exact (hsym 2 1).trans (ha.symm.trans (hsym 0 2))
    · exact (hsym 2 0).trans (ha.trans (hsym 1 2))
    · exact rfl
    · exact rfl
    · exact absurd hj (by omega)
    · exact (hsym 3 1).trans (hb.symm.trans (hsym 0 3))
    · exact (hsym 3 0).trans (hb.trans (hsym 1 3))
    · exact rfl
    · exact rfl
    · exact absurd hj (by omega)
    · exact absurd hi (by omega)
    · exact absurd hi (by omega)
    · exact absurd hi (by omega)
    · exact absurd hi (by omega)
    · exact absurd hi (by omega)
  · refine ⟨swap01_23, swap01_23_involutive, rfl, rfl, ?_⟩
    intro i j
    rcases i with ⟨_ | _ | _ | _ | n, hi⟩ <;> rcases j with ⟨_ | _ | _ | _ | m, hj⟩
    · exact (hdiag 1).trans (hdiag 0).symm
    · exact hsym 1 0
    · exact ha.symm
    · exact hb.symm
    · exact absurd hj (by omega)
    · exact hsym 0 1
    · exact (hdiag 0).trans (hdiag 1).symm
    · exact hb
    · exact ha
    · exact absurd hj (by omega)
    · exact (hsym 3 1).trans (ha.symm.trans (hsym 0 2))
    · exact (hsym 3 0).trans (hb.trans (hsym 1 2))
    · exact (hdiag 3).trans (hdiag 2).symm
    · exact hsym 3 2
    · exact absurd hj (by omega)
    · exact (hsym 2 1).trans (hb.symm.trans (hsym 0 3))
    · exact (hsym 2 0).trans (ha.trans (hsym 1 3))
    · exact hsym 2 3
    · exact (hdiag 2).trans (hdiag 3).symm
    · exact absurd hj (by omega)
    · exact absurd hi (by omega)
    · exact absurd hi (by omega)
    · exact absurd hi (by omega)
    · exact absurd hi (by omega)
    · exact absurd hi (by omega)

/-! ## Clause 4 — the two-term collision classification -/

/-- Strict monotonicity of addition in `ℤ[φ]`, straight from the definition of
    the order: `b < c` is `¬ Nonneg (emb b − emb c)` in `ℤ√5`, and adding `a` to
    both sides leaves that difference unchanged. The order-class lemmas
    (`add_lt_add_left`, `lt_of_le_of_ne`) reach `Classical.choice`; this does not. -/
theorem add_lt_add_right_zphi {a b c : Zphi} (h : b < c) : b + a < c + a := by
  change ¬ Zsqrtd.Nonneg (emb (b + a) - emb (c + a))
  have e : emb (b + a) - emb (c + a) = emb b - emb c := by
    rw [emb_add, emb_add]; ring
  rw [e]; exact h

/-- The ordered core: `r ≤ s` and `p < r`. Then `r = s = p + 1` and
    `q = p + 3`. Every step is a case split on `ℕ` or an explicit chain in
    `ℤ[φ]`; no `by_contra`, no `linarith`. -/
theorem collision_ordered {p q r s : ℕ} (hrs : r ≤ s) (hpr : p < r)
    (h : phiNegPow p + phiNegPow q = phiNegPow r + phiNegPow s) :
    r = p + 1 ∧ s = p + 1 ∧ q = p + 3 := by
  have hrec : phiNegPow p = phiNegPow (p + 1) + phiNegPow (p + 2) := phiNegPow_rec p
  -- Step A: r = p + 1.
  have hr : r = p + 1 := by
    rcases Nat.lt_or_ge r (p + 2) with hlt | hr2
    · omega
    · exfalso
      have h1 : phiNegPow r ≤ phiNegPow (p + 2) := phiNegPow_anti_le hr2
      have h2 : phiNegPow s ≤ phiNegPow (p + 2) := phiNegPow_anti_le (le_trans hr2 hrs)
      have hlt : phiNegPow r + phiNegPow s < phiNegPow p + phiNegPow q :=
        calc phiNegPow r + phiNegPow s ≤ phiNegPow (p + 2) + phiNegPow (p + 2) :=
              add_le_add h1 h2
          _ < phiNegPow (p + 1) + phiNegPow (p + 2) :=
              add_lt_add_right_zphi (phiNegPow_succ_lt (p + 1))
          _ = phiNegPow p := hrec.symm
          _ < phiNegPow p + phiNegPow q := lt_add_of_pos_right _ (PhiPos.phiNegPow_pos q)
      exact absurd h (ne_of_gt hlt)
  subst hr
  -- Step B: s = p + 1.
  have hB : phiNegPow (p + 2) + phiNegPow q = phiNegPow s := by
    have h' := h
    rw [hrec, add_assoc] at h'
    exact add_left_cancel h'
  have hs : s = p + 1 := by
    rcases Nat.lt_or_ge s (p + 2) with hlt | hge
    · omega
    · exfalso
      have hle : phiNegPow s ≤ phiNegPow (p + 2) := phiNegPow_anti_le hge
      have hgt : phiNegPow (p + 2) < phiNegPow s := by
        rw [← hB]; exact lt_add_of_pos_right _ (PhiPos.phiNegPow_pos q)
      exact lt_irrefl _ (lt_of_lt_of_le hgt hle)
  subst hs
  -- Step C: q = p + 3.
  have hrec1 : phiNegPow (p + 1) = phiNegPow (p + 2) + phiNegPow (p + 3) := phiNegPow_rec (p + 1)
  have hC : phiNegPow q = phiNegPow (p + 3) := by
    rw [hrec1] at hB
    exact add_left_cancel hB
  exact ⟨rfl, rfl, phiNegPow_inj hC⟩

/-- **Lemma 16.14, fourth clause.** Two sums of two negative powers of `φ`,
    each exponent pair listed in order, coincide only when the pairs are equal
    or one is `{P, P}` and the other `{P - 1, P + 2}`. -/
theorem two_term_collision {p q r s : ℕ} (hpq : p ≤ q) (hrs : r ≤ s)
    (h : phiNegPow p + phiNegPow q = phiNegPow r + phiNegPow s) :
    (p = r ∧ q = s) ∨
    (∃ P, 1 ≤ P ∧ r = P ∧ s = P ∧ p = P - 1 ∧ q = P + 2) ∨
    (∃ P, 1 ≤ P ∧ p = P ∧ q = P ∧ r = P - 1 ∧ s = P + 2) := by
  rcases Nat.lt_trichotomy p r with hlt | heq | hgt
  · obtain ⟨h1, h2, h3⟩ := collision_ordered hrs hlt h
    exact Or.inr (Or.inl ⟨p + 1, by omega, h1, h2, by omega, by omega⟩)
  · subst heq
    have : phiNegPow q = phiNegPow s := add_left_cancel h
    exact Or.inl ⟨rfl, phiNegPow_inj this⟩
  · obtain ⟨h1, h2, h3⟩ := collision_ordered hpq hgt h.symm
    exact Or.inr (Or.inr ⟨r + 1, by omega, h1, h2, by omega, by omega⟩)

/-- The two identities the book names as the source of the collision:
    `2φ⁻⁽ᵖ⁺¹⁾ = φ⁻ᵖ + φ⁻⁽ᵖ⁺³⁾` and `φ⁻⁽ᵖ⁺¹⁾ + φ⁻⁽ᵖ⁺²⁾ = φ⁻ᵖ`. -/
theorem collision_identities (p : ℕ) :
    2 * phiNegPow (p + 1) = phiNegPow p + phiNegPow (p + 3) ∧
    phiNegPow (p + 1) + phiNegPow (p + 2) = phiNegPow p := by
  have a := phiNegPow_rec p
  have b : phiNegPow (p + 1) = phiNegPow (p + 2) + phiNegPow (p + 3) := phiNegPow_rec (p + 1)
  refine ⟨?_, a.symm⟩
  calc 2 * phiNegPow (p + 1) = phiNegPow (p + 1) + phiNegPow (p + 1) := two_mul _
    _ = phiNegPow (p + 1) + (phiNegPow (p + 2) + phiNegPow (p + 3)) := by rw [← b]
    _ = (phiNegPow (p + 1) + phiNegPow (p + 2)) + phiNegPow (p + 3) := (add_assoc _ _ _).symm
    _ = phiNegPow p + phiNegPow (p + 3) := by rw [← a]

#print axioms coherence_invariant
#print axioms support_invariant
#print axioms exchanged_equal_coherence
#print axioms add_lt_add_right_zphi
#print axioms pair_perm
#print axioms swap01_involutive
#print axioms four_member_exchange
#print axioms phiNegPow_rec
#print axioms collision_ordered
#print axioms two_term_collision
#print axioms collision_identities

end Automorphism
end Two
end RatioSpace
