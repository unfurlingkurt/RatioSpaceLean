/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.ClosurePattern
/-!
  Elements II §16 Theorem 16.11, Step 4 — the root chain, for every `k`.

  From the root pair `{LR^k, RL^k}` the four proposals are
  `a = LR^kL = (2k+1):(2k+3)`, `b = LR^{k+1} = (k+2):(k+3)`,
  `c = RL^{k+1}`, `d = RL^kR`, and the book's claim is that the maximizer set
  is exactly `{b, c}` at every `k`.

  **The depths are computed, not bounded.** The book reads them off the
  continued fractions of `(k+2)²:(k+3)²` and `(2k+1)²:(2k+3)²`, which split by
  the parity of `k`. Here the same computation is carried by the Stern–Brocot
  step lemmas of Elements I (`cfNat_sum_add_left`/`_right`): each subtraction
  costs exactly one unit of depth, so a Euclidean quotient `m` costs `m`, and
  the depth is a sum of quotients with no case left to `decide`. The closed
  forms below agree with direct computation for `k < 40`.


  `t(b,c) = k+5`; `t(a,d) = 17j+8` at `k = 2j`, `5j+7` at `k = 2j+1`.
-/
set_option linter.style.show false

namespace RatioSpace
namespace Two
namespace RootChain

open Pres Contrast

/-! ## Depth is unchanged by reduction -/

/-- Reduction divides both entries by their gcd, and the Euclidean expansion
    does not see a common factor (`Contrast.cfNat_mul`). -/
theorem dSB_reduce_eq (A : Pres) (hq : 0 < A.q) : dSB (reduce A) = dSB A := by
  have hg := gcd_pos A
  have hqg : 0 < A.q / Nat.gcd A.p A.q := Nat.div_pos (Nat.gcd_le_right _ hq) hg
  have hp := Nat.div_mul_cancel (Nat.gcd_dvd_left A.p A.q)
  have hq' := Nat.div_mul_cancel (Nat.gcd_dvd_right A.p A.q)
  have e : cfNat A.p A.q = cfNat (A.p / Nat.gcd A.p A.q) (A.q / Nat.gcd A.p A.q) := by
    rw [← cfNat_mul (A.p / Nat.gcd A.p A.q) (A.q / Nat.gcd A.p A.q) _ hqg hg, hp, hq']
  show (cfNat (A.p / Nat.gcd A.p A.q) (A.q / Nat.gcd A.p A.q)).sum - 1
    = (cfNat A.p A.q).sum - 1
  rw [e]

/-- The support tension as a continued-fraction sum on the raw cross-products. -/
theorem tEnd_eq_sum (A B : IPres) :
    tEnd A B = (cfNat (A.p * B.q) (A.q * B.p)).sum - 1 := by
  unfold tEnd
  rw [dSB_reduce_eq _ (Nat.mul_pos A.q_pos B.p_pos)]
  rfl

/-! ## Euclidean quotients cost their size -/

theorem sum_mulR (p q m : ℕ) (hq : q ≠ 0) :
    (cfNat (p + m * q) q).sum = (cfNat p q).sum + m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show p + (m + 1) * q = (p + m * q) + q by ring, cfNat_sum_add_right _ hq, ih]
      omega

theorem sum_mulL (p q m : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) :
    (cfNat p (m * p + q)).sum = (cfNat p q).sum + m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hne : m * p + q ≠ 0 :=
        Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hq) (Nat.le_add_left q (m * p)))
      rw [show (m + 1) * p + q = p + (m * p + q) by ring, cfNat_sum_add_left hp hne, ih]
      omega

theorem sum_one_one : (cfNat 1 1).sum = 1 := by decide
theorem sum_two_one : (cfNat 2 1).sum = 2 := by decide

theorem sum_one_succ (j : ℕ) : (cfNat 1 (j + 1)).sum = j + 1 := by
  rw [show j + 1 = j * 1 + 1 by ring, sum_mulL 1 1 j one_ne_zero one_ne_zero, sum_one_one]
  omega

/-! ## The four proposals from the root pair `{LR^k, RL^k}` -/

/-- `a = LR^kL`. -/
def ra (k : ℕ) : IPres := ⟨2 * k + 1, 2 * k + 3, by omega, by omega⟩
/-- `b = LR^{k+1}`. -/
def rb (k : ℕ) : IPres := ⟨k + 2, k + 3, by omega, by omega⟩
/-- `c = RL^{k+1}`. -/
def rc (k : ℕ) : IPres := ⟨k + 3, k + 2, by omega, by omega⟩
/-- `d = RL^kR`. -/
def rd (k : ℕ) : IPres := ⟨2 * k + 3, 2 * k + 1, by omega, by omega⟩

/-- Parity, choice-free. Mathlib's `Nat.even_or_odd'` reaches `Classical.choice`;
    this does not. -/
theorem parity (k : ℕ) : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩

/-! ## `t(b,c) = k + 5` -/

theorem sum_bc_even (j : ℕ) :
    (cfNat ((2 * j + 2) * (2 * j + 2)) (4 * j + 5)).sum = 2 * j + 5 := by
  rw [show (2 * j + 2) * (2 * j + 2) = (3 * j + 4) + j * (4 * j + 5) by ring,
    sum_mulR _ _ _ (by omega),
    show 4 * j + 5 = 1 * (3 * j + 4) + (j + 1) by ring,
    sum_mulL _ _ _ (by omega) (by omega),
    show 3 * j + 4 = 1 + 3 * (j + 1) by ring,
    sum_mulR _ _ _ (by omega), sum_one_succ]
  omega

theorem sum_bc_odd (j : ℕ) :
    (cfNat ((2 * j + 3) * (2 * j + 3)) (4 * j + 7)).sum = 2 * j + 6 := by
  rw [show (2 * j + 3) * (2 * j + 3) = (j + 2) + (j + 1) * (4 * j + 7) by ring,
    sum_mulR _ _ _ (by omega),
    show 4 * j + 7 = 3 * (j + 2) + (j + 1) by ring,
    sum_mulL _ _ _ (by omega) (by omega),
    show j + 2 = 1 + 1 * (j + 1) by ring,
    sum_mulR _ _ _ (by omega), sum_one_succ]
  omega

theorem t_bc_sum (k : ℕ) :
    tEnd (rb k) (rc k) = (cfNat ((k + 2) * (k + 2)) (2 * k + 5)).sum := by
  rw [tEnd_eq_sum]
  show (cfNat ((k + 2) * (k + 2)) ((k + 3) * (k + 3))).sum - 1 = _
  rw [show (k + 3) * (k + 3) = (k + 2) * (k + 2) + (2 * k + 5) by ring,
    cfNat_sum_add_left (Nat.mul_ne_zero (by omega) (by omega)) (by omega)]
  omega

/-- **`t(b,c) = k + 5`, for every `k`.** -/
theorem t_bc (k : ℕ) : tEnd (rb k) (rc k) = k + 5 := by
  rw [t_bc_sum]
  rcases parity k with ⟨j, rfl | rfl⟩
  · rw [show 2 * j + 2 = 2 * j + 2 from rfl, show 2 * (2 * j) + 5 = 4 * j + 5 by ring,
      sum_bc_even]
  · rw [show 2 * j + 1 + 2 = 2 * j + 3 by ring, show 2 * (2 * j + 1) + 5 = 4 * j + 7 by ring,
      sum_bc_odd]

/-! ## `t(a,d)`, by parity -/

theorem t_ad_sum (k : ℕ) :
    tEnd (ra k) (rd k) = (cfNat ((2 * k + 1) * (2 * k + 1)) (8 * k + 8)).sum := by
  rw [tEnd_eq_sum]
  show (cfNat ((2 * k + 1) * (2 * k + 1)) ((2 * k + 3) * (2 * k + 3))).sum - 1 = _
  rw [show (2 * k + 3) * (2 * k + 3) = (2 * k + 1) * (2 * k + 1) + (8 * k + 8) by ring,
    cfNat_sum_add_left (Nat.mul_ne_zero (by omega) (by omega)) (by omega)]
  omega

/-- **`t(a,d) = 17j + 8` at `k = 2j`.** -/
theorem t_ad_even (j : ℕ) : tEnd (ra (2 * j)) (rd (2 * j)) = 17 * j + 8 := by
  rw [t_ad_sum,
    show (2 * (2 * j) + 1) * (2 * (2 * j) + 1) = 1 + j * (16 * j + 8) by ring,
    show 8 * (2 * j) + 8 = 16 * j + 8 by ring,
    sum_mulR _ _ _ (by omega),
    show 16 * j + 8 = (16 * j + 7) + 1 by ring, sum_one_succ]
  omega

/-- **`t(a,d) = 5j + 7` at `k = 2j + 1`.** -/
theorem t_ad_odd (j : ℕ) : tEnd (ra (2 * j + 1)) (rd (2 * j + 1)) = 5 * j + 7 := by
  rw [t_ad_sum,
    show (2 * (2 * j + 1) + 1) * (2 * (2 * j + 1) + 1) = (8 * j + 9) + j * (16 * j + 16) by ring,
    show 8 * (2 * j + 1) + 8 = 16 * j + 16 by ring,
    sum_mulR _ _ _ (by omega),
    show 16 * j + 16 = 1 * (8 * j + 9) + (8 * j + 7) by ring,
    sum_mulL _ _ _ (by omega) (by omega),
    show 8 * j + 9 = 2 + 1 * (8 * j + 7) by ring,
    sum_mulR _ _ _ (by omega),
    show 8 * j + 7 = (4 * j + 3) * 2 + 1 by ring,
    sum_mulL _ _ _ (by omega) (by omega), sum_two_one]
  omega

/-- **The decisive inequality: `t(b,c) < t(a,d)` at every `k`.** -/
theorem t_bc_lt_ad (k : ℕ) : tEnd (rb k) (rc k) < tEnd (ra k) (rd k) := by
  rw [t_bc]
  rcases parity k with ⟨j, rfl | rfl⟩
  · rw [t_ad_even]; omega
  · rw [t_ad_odd]; omega

/-! ## Side exchange pairs the proposals

  `Inv` sends `a ↔ d` and `b ↔ c`, so Theorem 7.8 gives `t(b,d) = t(a,c)` and
  `t(c,d) = t(a,b)`. Only two cross tensions differ between the pairs, and they
  are the two computed above. -/

theorem inv_ra (k : ℕ) : Inv (ra k) = rd k := rfl
theorem inv_rc (k : ℕ) : Inv (rc k) = rb k := rfl
theorem inv_rb (k : ℕ) : Inv (rb k) = rc k := rfl

theorem t_bd (k : ℕ) : tEnd (rb k) (rd k) = tEnd (ra k) (rc k) := by
  rw [← inv_rc, ← inv_ra, tEnd_side_invariant, tEnd_comm]

theorem t_cd (k : ℕ) : tEnd (rc k) (rd k) = tEnd (ra k) (rb k) := by
  rw [← inv_rb, ← inv_ra, tEnd_side_invariant, tEnd_comm]

/-! ## The four coherence values -/

open Zphi PhiPos Automorphism Beat11

/-- The admitted family at a root-chain step, in the book's order `a, b, c, d`. -/
def fam (k : ℕ) : List IPres := [ra k, rb k, rc k, rd k]

/-- What every coherence value shares: the self-term, `t(a,b)` and `t(a,c)`. -/
def shared (k : ℕ) : Zphi :=
  1 + phiNegPow (tEnd (ra k) (rb k)) + phiNegPow (tEnd (ra k) (rc k))

theorem coherence_a (k : ℕ) :
    coherenceOf (fam k) (ra k) = phiNegPow (tEnd (ra k) (rd k)) + shared k := by
  simp only [fam, shared, coherenceOf, tensions, coherence, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, self_term]
  ring

theorem coherence_b (k : ℕ) :
    coherenceOf (fam k) (rb k) = phiNegPow (tEnd (rb k) (rc k)) + shared k := by
  simp only [fam, shared, coherenceOf, tensions, coherence, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, self_term]
  rw [tEnd_comm (rb k) (ra k), t_bd]
  ring

theorem coherence_c (k : ℕ) :
    coherenceOf (fam k) (rc k) = phiNegPow (tEnd (rb k) (rc k)) + shared k := by
  simp only [fam, shared, coherenceOf, tensions, coherence, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, self_term]
  rw [tEnd_comm (rc k) (ra k), tEnd_comm (rc k) (rb k), t_cd]
  ring

theorem coherence_d (k : ℕ) :
    coherenceOf (fam k) (rd k) = phiNegPow (tEnd (ra k) (rd k)) + shared k := by
  simp only [fam, shared, coherenceOf, tensions, coherence, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, self_term]
  rw [tEnd_comm (rd k) (ra k), tEnd_comm (rd k) (rb k), tEnd_comm (rd k) (rc k), t_bd, t_cd]
  ring

/-- **`C(a) < C(b)`**: the shared terms cancel and `φ^{-t(a,d)} < φ^{-t(b,c)}`. -/
theorem coherence_a_lt_b (k : ℕ) : coherenceOf (fam k) (ra k) < coherenceOf (fam k) (rb k) := by
  rw [coherence_a, coherence_b]
  exact add_lt_add_right_zphi (phiNegPow_strict (t_bc_lt_ad k))

/-! ## Step 4: the maximizer set is exactly `{LR^{k+1}, RL^{k+1}}` -/

theorem mem_fam {k : ℕ} {z : IPres} (hz : z ∈ fam k) :
    z = ra k ∨ z = rb k ∨ z = rc k ∨ z = rd k := by
  simpa [fam] using hz

/-- **Theorem 16.11, Step 4, for every `k`.** Definition 8.1's support
    over the root chain's four proposals is `[LR^{k+1}, RL^{k+1}]`. -/
theorem step4_support (k : ℕ) : support (fam k) = [rb k, rc k] := by
  have hab := coherence_a_lt_b k
  have hbc : coherenceOf (fam k) (rb k) = coherenceOf (fam k) (rc k) := by
    rw [coherence_b, coherence_c]
  have had : coherenceOf (fam k) (ra k) = coherenceOf (fam k) (rd k) := by
    rw [coherence_a, coherence_d]
  have top : ∀ y, coherenceOf (fam k) y = coherenceOf (fam k) (rb k) →
      (fam k).all (fun z => decide (coherenceOf (fam k) z ≤ coherenceOf (fam k) y)) = true := by
    intro y hy
    refine List.all_eq_true.mpr (fun z hz => decide_eq_true ?_)
    rw [hy]
    rcases mem_fam hz with rfl | rfl | rfl | rfl
    · exact le_of_lt hab
    · exact le_refl _
    · exact le_of_eq hbc.symm
    · exact le_of_lt (had ▸ hab)
  have low : ∀ y, coherenceOf (fam k) y = coherenceOf (fam k) (ra k) →
      (fam k).all (fun z => decide (coherenceOf (fam k) z ≤ coherenceOf (fam k) y)) = false := by
    intro y hy
    cases h : (fam k).all (fun z => decide (coherenceOf (fam k) z ≤ coherenceOf (fam k) y))
    · rfl
    · have hle := of_decide_eq_true (List.all_eq_true.mp h (rb k) (by simp [fam]))
      rw [hy] at hle
      exact absurd hle (not_le_of_lt_zphi hab)
  have pa := low (ra k) rfl
  have pd := low (rd k) had.symm
  have pb := top (rb k) rfl
  have pc := top (rc k) hbc.symm
  show List.filter (fun y => (fam k).all
      (fun z => decide (coherenceOf (fam k) z ≤ coherenceOf (fam k) y)))
      [ra k, rb k, rc k, rd k] = [rb k, rc k]
  simp only [List.filter_cons, List.filter_nil, pa, pb, pc, pd, Bool.false_eq_true,
    if_true, if_false]

/-! ## The four proposals are the book's words -/

open Frame

theorem r_replicate_true (k : ℕ) (w : Word) :
    (r (List.replicate k true ++ w)).p = (r w).p + k * (r w).q ∧
      (r (List.replicate k true ++ w)).q = (r w).q := by
  induction k with
  | zero => simp
  | succ k ih =>
      obtain ⟨h1, h2⟩ := r_cons_true (List.replicate k true ++ w)
      refine ⟨?_, ?_⟩
      · show (r (true :: (List.replicate k true ++ w))).p = _
        rw [h1, ih.1, ih.2]; ring
      · show (r (true :: (List.replicate k true ++ w))).q = _
        rw [h2, ih.2]

theorem r_replicate_false (k : ℕ) (w : Word) :
    (r (List.replicate k false ++ w)).p = (r w).p ∧
      (r (List.replicate k false ++ w)).q = (r w).q + k * (r w).p := by
  induction k with
  | zero => simp
  | succ k ih =>
      obtain ⟨h1, h2⟩ := r_cons_false (List.replicate k false ++ w)
      refine ⟨?_, ?_⟩
      · show (r (false :: (List.replicate k false ++ w))).p = _
        rw [h1, ih.1]
      · show (r (false :: (List.replicate k false ++ w))).q = _
        rw [h2, ih.1, ih.2]; ring

/-- `a = LR^kL` addresses `(2k+1):(2k+3)`. -/
theorem addr_a (k : ℕ) :
    (r (false :: (List.replicate k true ++ [false]))).p = (ra k).p ∧
      (r (false :: (List.replicate k true ++ [false]))).q = (ra k).q := by
  obtain ⟨h1, h2⟩ := r_cons_false (List.replicate k true ++ [false])
  obtain ⟨g1, g2⟩ := r_replicate_true k [false]
  have e1 : (r [false]).p = 1 := by decide
  have e2 : (r [false]).q = 2 := by decide
  rw [h1, h2, g1, g2, e1, e2]
  exact ⟨by show 1 + k * 2 = 2 * k + 1; omega, by show 1 + k * 2 + 2 = 2 * k + 3; omega⟩

/-- `b = LR^{k+1}` addresses `(k+2):(k+3)`. -/
theorem addr_b (k : ℕ) :
    (r (false :: (List.replicate (k + 1) true ++ []))).p = (rb k).p ∧
      (r (false :: (List.replicate (k + 1) true ++ []))).q = (rb k).q := by
  obtain ⟨h1, h2⟩ := r_cons_false (List.replicate (k + 1) true ++ [])
  obtain ⟨g1, g2⟩ := r_replicate_true (k + 1) []
  have e1 : (r []).p = 1 := by decide
  have e2 : (r []).q = 1 := by decide
  rw [h1, h2, g1, g2, e1, e2]
  exact ⟨by show 1 + (k + 1) * 1 = k + 2; omega, by show 1 + (k + 1) * 1 + 1 = k + 3; omega⟩

/-- `c = RL^{k+1}` addresses `(k+3):(k+2)`. -/
theorem addr_c (k : ℕ) :
    (r (true :: (List.replicate (k + 1) false ++ []))).p = (rc k).p ∧
      (r (true :: (List.replicate (k + 1) false ++ []))).q = (rc k).q := by
  obtain ⟨h1, h2⟩ := r_cons_true (List.replicate (k + 1) false ++ [])
  obtain ⟨g1, g2⟩ := r_replicate_false (k + 1) []
  have e1 : (r []).p = 1 := by decide
  have e2 : (r []).q = 1 := by decide
  rw [h1, h2, g1, g2, e1, e2]
  exact ⟨by show 1 + (1 + (k + 1) * 1) = k + 3; omega, by show 1 + (k + 1) * 1 = k + 2; omega⟩

/-- `d = RL^kR` addresses `(2k+3):(2k+1)`. -/
theorem addr_d (k : ℕ) :
    (r (true :: (List.replicate k false ++ [true]))).p = (rd k).p ∧
      (r (true :: (List.replicate k false ++ [true]))).q = (rd k).q := by
  obtain ⟨h1, h2⟩ := r_cons_true (List.replicate k false ++ [true])
  obtain ⟨g1, g2⟩ := r_replicate_false k [true]
  have e1 : (r [true]).p = 2 := by decide
  have e2 : (r [true]).q = 1 := by decide
  rw [h1, h2, g1, g2, e1, e2]
  exact ⟨by show 2 + (1 + k * 2) = 2 * k + 3; omega, by show 1 + k * 2 = 2 * k + 1; omega⟩


end RootChain
end Two
end RatioSpace
