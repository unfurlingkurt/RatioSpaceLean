/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S04.Composition
import RatioSpace.ElementsI.S02.Frame
import RatioSpace.ElementsI.S05.Depth
/-!
  Elements II §16 Lemma 16.10 — Contrast offset inside one frame family.

  **The boxed identity, with its sign.** Lemma 16.10 states
  `r_F(v) ⊗ r_F(v') = N:(N−Δ)` for
  `Δ = ab'-a'b` the determinant contact of the two canonical addresses. The
  identity holds for any positively oriented unimodular frame
  and any two coefficient pairs. Checked here from the frame's
  own contact equation: the two products of the contrast
  differ by exactly `Δ · (F.plus.p·F.minus.q − F.plus.q·F.minus.p)`, and
  Definition 2.2's contact pins that factor at `1`, not `0` or `−1`, so the
  sign is fixed by the contact and is not a convention.
  `contrast_offset` below
  is the identity, proved in general; `book_sign_fails` is one
  concrete instance where the opposite sign `N+Δ` does not hold, so the sign
  does not rest on the algebra alone.

  **Scope.** The boxed identity, the "self-contained integer algebra"
  half of Lemma 16.10, comes first. The depth-bound corollary
  (`⌊N/Δ⌋ − 1 ≤ t_O(...) ≤ ⌊N/Δ⌋ + Δ − 1` for `Δ > 0`, needing `Depth.lean`'s
  Stern–Brocot depth and a floor/gcd argument) follows it.

  **What `combo`/`comboI` are, and what they are not.** The lemma's own proof
  reduces `r_F(v)` to `M_F(a,b) = a•C₊+b•C₋` via `r_F(v)` being the mediant of
  `F·v` and `(a,b) = G(v)(1,1)`. That reduction is not re-derived here — it is
  matrix algebra already available from `Walk.lean`'s `G` and `Frame.matrix`,
  and connecting it is bookkeeping, not content this lemma
  adds. What is stated and proved here is the algebraic identity itself, for
  arbitrary positive coefficient pairs `(a,b)`, `(a',b')`, which is exactly
  what the boxed formula asserts once `r_F(v)`, `r_F(v')` are unfolded.
-/
-- `show` is used below to unfold `cfFuel`'s `if` into a shape the rewrites can
-- see. `change` cannot: the branches carry placeholders it will not synthesise.
set_option linter.style.show false

namespace RatioSpace
namespace Two
namespace Contrast

open Frame Pres RatioSpace

/-! ## Two facts contact already forces -/

/-- Contact forces `F.plus.p > 0`: if it were `0`, `Contact`'s left side would
    be `0` while its right side is at least `1`. -/
theorem plus_p_pos (F : Frame) : 0 < F.plus.p := by
  have hc : F.plus.p * F.minus.q = F.plus.q * F.minus.p + 1 := F.contact
  rcases Nat.eq_zero_or_pos F.plus.p with h0 | hpos
  · exfalso; simp [h0] at hc
  · exact hpos

/-- Contact forces `F.minus.q > 0`, symmetrically. -/
theorem minus_q_pos (F : Frame) : 0 < F.minus.q := by
  have hc : F.plus.p * F.minus.q = F.plus.q * F.minus.p + 1 := F.contact
  rcases Nat.eq_zero_or_pos F.minus.q with h0 | hpos
  · exfalso; simp [h0] at hc
  · exact hpos

/-! ## Definition — the coefficient combination `a•C₊+b•C₋` -/

/-- **`M_F(a,b) = a•C₊+b•C₋`, as an `IPres`.** This is `r_F(v)` exactly when
    `(a,b)` is `r(v)`'s own pair (the lemma's own reduction, not re-derived
    here — see the file header). Positivity of both components needs only
    `a,b > 0` and `plus_p_pos`/`minus_q_pos` above, for any frame at all,
    including `Frame.empty` itself. -/
def comboI (F : Frame) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : IPres :=
  ⟨a * F.plus.p + b * F.minus.p, a * F.plus.q + b * F.minus.q,
    by have h1 : 0 < a * F.plus.p := Nat.mul_pos ha (plus_p_pos F); omega,
    by have h1 : 0 < b * F.minus.q := Nat.mul_pos hb (minus_q_pos F); omega⟩

@[simp] theorem comboI_p (F : Frame) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (comboI F a b ha hb).p = a * F.plus.p + b * F.minus.p := rfl

@[simp] theorem comboI_q (F : Frame) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (comboI F a b ha hb).q = a * F.plus.q + b * F.minus.q := rfl

/-! ## Lemma 16.10, boxed identity -/

/-- **Lemma 16.10, the boxed identity.** `r_F(v) ⊗ r_F(v') = N:(N-Δ)`, stated
    additively as `N = M + Δ` to stay inside `ℕ`/`ℤ` without truncated
    subtraction, where `M` is the contrast's own second component. The opposite
    sign `N:(N+Δ)` is not generally true (`book_sign_fails` below), and `Δ` here
    is exactly the book's
    `Δ(r(v),r(v')) = ab'-a'b`. -/
theorem contrast_offset (F : Frame) (a b a' b' : ℕ)
    (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b') :
    ((IPres.otimes (comboI F a b ha hb) (comboI F a' b' ha' hb')).p : ℤ)
      = ((IPres.otimes (comboI F a b ha hb) (comboI F a' b' ha' hb')).q : ℤ)
        + ((a : ℤ) * b' - (a' : ℤ) * b) := by
  have hc : (F.plus.p : ℤ) * F.minus.q = (F.plus.q : ℤ) * F.minus.p + 1 := by
    exact_mod_cast F.contact
  simp only [IPres.otimes_p, IPres.otimes_q, comboI_p, comboI_q]
  push_cast
  -- The difference between the two products is exactly `Δ` times the frame's
  -- own determinant contact, a pure `ring` identity; substituting `hc` pins
  -- that factor at `1`. No `linear_combination`/`linarith`: both route
  -- integer equalities through generic ordered-field machinery that pulls
  -- `Classical.choice` for no framework reason, exactly the pattern the three
  -- earlier occurrences in this tree share.
  have hring :
      ((a:ℤ) * F.plus.p + b * F.minus.p) * (a' * F.plus.q + b' * F.minus.q)
        - ((a:ℤ) * F.plus.q + b * F.minus.q) * (a' * F.plus.p + b' * F.minus.p)
      = ((a:ℤ) * b' - a' * b) * (F.plus.p * F.minus.q - F.plus.q * F.minus.p) := by
    ring
  have hfactor : (F.plus.p : ℤ) * F.minus.q - F.plus.q * F.minus.p = 1 := by omega
  rw [hfactor, mul_one] at hring
  omega

/-- **The opposite sign fails.** At `F = Frame.empty`, `(a,b)=(1,1)`,
    `(a',b')=(1,2)`: `Δ = 1·2-1·1 = 1`, `N = 1·2 = 2`, and the actual second
    component is `1`, not `N+Δ = 3`. `contrast_offset` above gives the reason:
    `N = M + Δ`, so `M = N - Δ = 1`, matching this computation exactly. -/
theorem book_sign_fails :
    (IPres.otimes (comboI Frame.empty 1 1 (by decide) (by decide))
      (comboI Frame.empty 1 2 (by decide) (by decide))).q ≠ 2 + 1 := by
  decide


/-! ## Lemma 16.10's depth-bound corollary — the divisor locus

The book states, for `Δ > 0`,
`⌊N/Δ⌋ − 1 ≤ t_O ≤ ⌊N/Δ⌋ + Δ − 1`, with `t_O` the Stern–Brocot depth of the
reduced contrast `N:(N−Δ)`, and the lower bound attained when `Δ ∣ N`.

**Without the `− 1` the lower bound fails, and the failure locus is exact.**
Over every `0 < Δ < N < 900` (403,651 cases) the bound `⌊N/Δ⌋ ≤ t_O` fails on
exactly the pairs with `Δ ∣ N`, 5,350 of them and no others, where it is short
by exactly one.

This section proves the divisor case, which is the whole failure locus. If
`N = k·Δ` then `N : (N−Δ)` is `kΔ : (k−1)Δ`, whose canonical continued
fraction is `[1, k−1]`, so `t_O = k − 1 = ⌊N/Δ⌋ − 1` **exactly** — not a bound
but an identity. The general lower bound is a separate induction on the
Euclidean recursion, `contrast_depth_lower` below.
-/

/-- The contrast presentation `N : (N − Δ)` for `0 < Δ < N`. -/
def contrastPres (N D : ℕ) (h : 0 < D) (h2 : D < N) : Pres :=
  ⟨N, N - D, by omega⟩

/-- The Euclidean expansion is invariant under scaling both arguments by a
    positive factor. Needed because the contrast on the divisor locus is
    `kΔ : (k−1)Δ`, and the depth is read off the unscaled `k : (k−1)`.
    Strong induction on the second argument, which is what the recursion
    descends on. -/
theorem cfFuel_mul : ∀ q n m p D, 0 < q → 0 < D → q * D ≤ n → q ≤ m →
    Pres.cfFuel n (p * D) (q * D) = Pres.cfFuel m p q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro n m p D hq hD hn hm
    · have hqD1 : 1 ≤ q * D := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))
      have hn1 : 1 ≤ n := le_trans hqD1 hn
      have hm1 : 1 ≤ m := by omega
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hqD : ¬(q * D = 0) := Nat.mul_ne_zero (by omega) (by omega)
      have hdiv : (p * D) / (q * D) = p / q := Nat.mul_div_mul_right _ _ hD
      have hmod : (p * D) % (q * D) = (p % q) * D := Nat.mul_mod_mul_right _ _ _
      show (if q * D = 0 then _ else _) = (if q = 0 then _ else _)
      rw [if_neg hqD, if_neg (by omega : ¬(q = 0)), hdiv, hmod]
      rcases Nat.eq_zero_or_pos (p % q) with h0 | h0
      · rw [h0, Nat.zero_mul, if_pos rfl, if_pos rfl]
      · have h0' : ¬(p % q = 0) := by omega
        have hzero : ¬((p % q) * D = 0) := Nat.mul_ne_zero h0' (by omega)
        rw [if_neg hzero, if_neg h0']
        have hlt : p % q < q := Nat.mod_lt _ hq
        have hle : (p % q) * D ≤ n := by
          have hstep : (p % q) * D < q * D :=
            Nat.mul_lt_mul_of_lt_of_le hlt (le_refl D) (by omega)
          omega
        rw [ih (p % q) hlt n m q D h0 hD hle (by omega)]

/-- `cfNat` scales. -/
theorem cfNat_mul (p q D : ℕ) (hq : 0 < q) (hD : 0 < D) :
    Pres.cfNat (p * D) (q * D) = Pres.cfNat p q :=
  cfFuel_mul q (q * D) q p D hq hD (le_refl _) (le_refl _)

/-- The Euclidean expansion of `k : (k−1)` sums to `k`, for `k ≥ 2`.

    The list is **not** uniform in `k`: at `k = 2` it is `[2]`, because
    `2 % 1 = 0` terminates at once, and at `k ≥ 3` it is `[1, k−1]`. Both sum
    to `k`, and the sum is what the depth reads, so the statement is on the
    sum. Stated on the list it is false at `k = 2` — the kind of thing a
    general claim checked at one instance would miss. -/
theorem cfSum_succ_pred (k : ℕ) (hk : 2 ≤ k) :
    (Pres.cfNat k (k - 1)).sum = k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  cases m with
  | zero => decide
  | succ n =>
      have hd : (n + 3) / (n + 2) = 1 := by
        rw [show n + 3 = 1 + (n + 2) * 1 by ring,
            Nat.add_mul_div_left _ _ (by omega : 0 < n + 2),
            Nat.div_eq_of_lt (by omega)]
      have hr : (n + 3) % (n + 2) = 1 := by
        rw [show n + 3 = 1 + 1 * (n + 2) by ring, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (by omega)
      show (Pres.cfFuel (n + 2) (n + 3) (n + 2)).sum = n + 3
      unfold Pres.cfFuel
      rw [if_neg (by omega : ¬(n + 2 = 0)), if_neg (by rw [hr]; omega), hd, hr]
      show 1 + (Pres.cfFuel (n + 1) (n + 2) 1).sum = n + 3
      cases n with
      | zero => decide
      | succ j =>
          unfold Pres.cfFuel
          rw [if_neg (by omega : ¬(1:ℕ) = 0), if_pos (Nat.mod_one _)]
          simp
          omega

/-- **Lemma 16.10's corollary on the divisor locus, exactly.**

    When `Δ ∣ N` the contrast depth is `N/Δ − 1`: one *below* `⌊N/Δ⌋`, so the
    book's lower bound `⌊N/Δ⌋ − 1` is attained. An identity, not a bound, and by
    the exhaustive check recorded above this is the entire set on which
    `⌊N/Δ⌋ ≤ t_O` fails. -/
theorem contrast_depth_of_dvd (D k : ℕ) (hD : 0 < D) (hk : 2 ≤ k) :
    Pres.dSB (contrastPres (k * D) D hD
      (by have : 1 * D < k * D :=
            Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl D) (by omega)
          omega)) = (k * D) / D - 1 := by
  have hsub : k * D - D = (k - 1) * D := by
    cases k with
    | zero => omega
    | succ m => rw [Nat.succ_sub_one, Nat.succ_mul, Nat.add_sub_cancel]
  have hdiv : k * D / D = k := Nat.mul_div_cancel _ hD
  show (Pres.cfNat (k * D) (k * D - D)).sum - 1 = _
  rw [hsub, cfNat_mul _ _ _ (by omega) hD, cfSum_succ_pred k hk, hdiv]

/-! ### The two bounds themselves, proved rather than checked

  The bounds hold on the exhaustive check over `0 < Δ < N < 900`. An
  exhaustive check over a window is not a theorem, and the shape it shows, a
  shortfall of exactly one on exactly the divisor locus, is what these proofs
  have to reproduce for every `N`.

  Both reduce to two facts about the Euclidean expansion: its quotient sum
  never exceeds the numerator, and never exceeds
  `⌊p/q⌋ + q`. Both rest on `add_le_mul_succ`, which is the whole arithmetic
  content: `a + y ≤ a·y + 1` whenever both are positive, sharp at `a = 1` and
  at `y = 1`.

  **Everything below is stated on `N = Δ + M`, not on `N − Δ`.** Truncated
  subtraction hides `N` inside the second component, so every rewrite of `N`
  reaches into it; carrying `M` explicitly is what makes the two regimes
  (`M < Δ` and `Δ < M`) separate cleanly.
-/

/-- `a + y ≤ a·y + 1` for `0 < a`, `0 < y`. Equality at `a = 1` and at
    `y = 1`, which is where both contrast bounds are attained. -/
theorem add_le_mul_succ (a y : ℕ) (ha : 0 < a) (hy : 0 < y) :
    a + y ≤ a * y + 1 := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  have h : (a + 1) * (y + 1) + 1 = (a + 1 + (y + 1)) + a * y := by ring
  rw [h]
  exact Nat.le_add_right _ _

/-- The quotient sum never exceeds the numerator, for `0 < q ≤ p`. Strong
    induction on `q`, which is what the recursion descends on. Sharp: `p:1`
    expands to `[p]`. -/
theorem cfNat_sum_le : ∀ q p, 0 < q → q ≤ p → (Pres.cfNat p q).sum ≤ p := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro p hq hqp
    have hqne : q ≠ 0 := by omega
    by_cases hmod : p % q = 0
    · rw [Pres.cfNat_of_dvd hqne hmod]
      simpa using Nat.div_le_self p q
    · rw [Pres.cfNat_cons hqne hmod]
      have hlt : p % q < q := Nat.mod_lt _ hq
      have hr1 : 0 < p % q := Nat.one_le_iff_ne_zero.mpr hmod
      have hrec : (Pres.cfNat q (p % q)).sum ≤ q :=
        ih (p % q) hlt q hr1 (by omega)
      have hd : 0 < p / q := Nat.div_pos hqp hq
      have hkey : p / q + q ≤ q * (p / q) + 1 := by
        have h := add_le_mul_succ (p / q) q hd hq
        rw [Nat.mul_comm] at h
        exact h
      simp only [List.sum_cons]
      calc p / q + (Pres.cfNat q (p % q)).sum
          ≤ p / q + q := Nat.add_le_add_left hrec _
        _ ≤ q * (p / q) + 1 := hkey
        _ ≤ q * (p / q) + p % q := Nat.add_le_add_left hr1 _
        _ = p := Nat.div_add_mod p q

/-- The quotient sum never exceeds `⌊p/q⌋ + q`: the head contributes `⌊p/q⌋`
    and the whole tail is an expansion of `q : (p mod q)`, which
    `cfNat_sum_le` caps at `q`. -/
theorem cfNat_sum_le_div_add (p q : ℕ) (hq : 0 < q) :
    (Pres.cfNat p q).sum ≤ p / q + q := by
  have hqne : q ≠ 0 := by omega
  by_cases hmod : p % q = 0
  · rw [Pres.cfNat_of_dvd hqne hmod]
    simp only [List.sum_cons, List.sum_nil]
    exact Nat.add_le_add_left (Nat.zero_le q) _
  · rw [Pres.cfNat_cons hqne hmod]
    have hlt : p % q < q := Nat.mod_lt _ hq
    have hrec : (Pres.cfNat q (p % q)).sum ≤ q :=
      cfNat_sum_le (p % q) q (Nat.one_le_iff_ne_zero.mpr hmod) (by omega)
    simp only [List.sum_cons]
    exact Nat.add_le_add_left hrec _

/-- The quotient sum is at least the leading quotient. -/
theorem cfNat_div_le_sum (p q : ℕ) (hq : 0 < q) :
    p / q ≤ (Pres.cfNat p q).sum := by
  have hqne : q ≠ 0 := by omega
  by_cases hmod : p % q = 0
  · rw [Pres.cfNat_of_dvd hqne hmod]
    simp
  · rw [Pres.cfNat_cons hqne hmod]
    simp only [List.sum_cons]
    exact Nat.le_add_right _ _

/-- Above the diagonal (`Δ < M`, i.e. `N > 2Δ`) the contrast's own first
    Euclidean step is forced: quotient `1`, remainder exactly `Δ`. This is why
    both bounds reduce to a statement about `M : Δ`. -/
theorem contrast_first_step (D M : ℕ) (hD : 0 < D) (hDM : D < M) :
    Pres.cfNat (D + M) M = 1 :: Pres.cfNat M D := by
  have hmod : (D + M) % M = D := by
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hDM
  have hdiv : (D + M) / M = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [Pres.cfNat_cons (by omega) (by rw [hmod]; omega), hmod, hdiv]

/-- **Lemma 16.10's corollary, lower bound.**

    `⌊N/Δ⌋ − 1 ≤ d_SB(N : (N−Δ))` for every `0 < Δ < N`, with no bound on `N`.
    The bound `⌊N/Δ⌋ ≤ d_SB` fails exactly on the divisor locus
    (`contrast_depth_of_dvd`, where the depth is `N/Δ − 1` on the nose). The
    `− 1` is therefore sharp, and this says the bound holds for every `N`,
    which the exhaustive check could only observe on its window. -/
theorem contrast_depth_lower (N D : ℕ) (hD : 0 < D) (hDN : D < N) :
    N / D - 1 ≤ Pres.dSB (contrastPres N D hD hDN) := by
  obtain ⟨M, hM⟩ : ∃ M', N - D = M' := ⟨_, rfl⟩
  have hMpos : 0 < M := by omega
  have hNM : N = D + M := by omega
  have key : N / D ≤ (Pres.cfNat N M).sum := by
    rcases Nat.lt_trichotomy M D with h | h | h
    · -- below the diagonal `⌊N/Δ⌋ = 1`, and the expansion is never empty
      have h1 : N / D = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [h1]
      exact Pres.cfNat_sum_pos M N (by omega)
    · -- on the diagonal the contrast is `2Δ : Δ`, expansion `[2]`, exactly `N/Δ`
      have hmod : N % M = 0 := by rw [hNM, Nat.add_mod_right, h, Nat.mod_self]
      rw [Pres.cfNat_of_dvd (by omega) hmod]
      simp only [List.sum_cons, List.sum_nil, h]
      omega
    · -- above the diagonal, one forced step down to `M : Δ`
      have hrec : M / D ≤ (Pres.cfNat M D).sum := cfNat_div_le_sum _ _ hD
      rw [hNM, contrast_first_step D M hD h]
      simp only [List.sum_cons]
      rw [Nat.add_div_left M hD]
      omega
  show N / D - 1 ≤ (Pres.cfNat N (N - D)).sum - 1
  rw [hM]
  exact Nat.sub_le_sub_right key 1

/-- **The upper bound, and it is sharp.**

    `t_O + 1 ≤ ⌊N/Δ⌋ + Δ`, i.e. `t_O ≤ ⌊N/Δ⌋ + Δ − 1`, the bound Lemma 16.10
    states for `Δ > 0`. The looser `⌊N/Δ⌋ + Δ` never uses its extra unit, and
    the tight form is
    attained at `N = Δ + 1`, where the expansion is the single term `[Δ+1]`.

    **Theorem 16.11 needs the tight form.** Step 1 there needs
    `3A/56 − 1 ≥ 10` to carry `t₁₄ + 2 ≤ min(t₁₃,t₂₃,t₂₄)`, and the smallest
    integer `A` satisfying that is exactly **206**, the threshold 16.11
    states. Under the looser bound the requirement is `≥ 11`, which 206 fails
    and 224 would meet. -/
theorem contrast_depth_upper_tight (N D : ℕ) (hD : 0 < D) (hDN : D < N) :
    Pres.dSB (contrastPres N D hD hDN) + 1 ≤ N / D + D := by
  obtain ⟨M, hM⟩ : ∃ M', N - D = M' := ⟨_, rfl⟩
  have hMpos : 0 < M := by omega
  have hNM : N = D + M := by omega
  have key : (Pres.cfNat N M).sum ≤ N / D + D := by
    rcases Nat.lt_trichotomy M D with h | h | h
    · have h1 : N / D = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      rcases Nat.eq_or_lt_of_le hMpos with hM1 | hM1
      · have hmod : N % M = 0 := by rw [← hM1]; exact Nat.mod_one _
        rw [Pres.cfNat_of_dvd (by omega) hmod, List.sum_cons, List.sum_nil,
            ← hM1, Nat.div_one]
        omega
      · have hstep : (Pres.cfNat N M).sum ≤ N / M + M :=
          cfNat_sum_le_div_add _ _ hMpos
        have hNMdiv : N / M = D / M + 1 := by
          rw [hNM, Nat.add_div_right _ hMpos]
        have hq : 0 < D / M := Nat.div_pos (by omega) hMpos
        have hself : D / M * M ≤ D := Nat.div_mul_le_self D M
        have hkey : D / M + M ≤ D := by
          rcases Nat.eq_or_lt_of_le hq with hq1 | hq2
          · omega
          · have h2 : 2 ≤ D / M := by omega
            have hM2 : 2 ≤ M := by omega
            have hMle : 1 * M ≤ D / M * M := Nat.mul_le_mul_right M (by omega)
            rw [Nat.one_mul] at hMle
            have hsplit : D / M * M = (D / M - 1) * M + M := by
              rw [Nat.sub_mul, Nat.one_mul]
              omega
            have hgrow : 2 * (D / M - 1) ≤ (D / M - 1) * M := by
              rw [Nat.mul_comm]
              exact Nat.mul_le_mul_left _ hM2
            omega
        omega
    · have hmod : N % M = 0 := by rw [hNM, Nat.add_mod_right, h, Nat.mod_self]
      rw [Pres.cfNat_of_dvd (by omega) hmod, List.sum_cons, List.sum_nil, h]
      omega
    · have hrec : (Pres.cfNat M D).sum ≤ M / D + D :=
        cfNat_sum_le_div_add _ _ hD
      rw [hNM, contrast_first_step D M hD h, List.sum_cons,
          Nat.add_div_left M hD]
      omega
  have hpos : 0 < (Pres.cfNat N M).sum := Pres.cfNat_sum_pos _ _ (by omega)
  show (Pres.cfNat N (N - D)).sum - 1 + 1 ≤ N / D + D
  rw [hM]; omega

/-- The looser upper bound `⌊N/Δ⌋ + Δ`, a corollary of the tight one. -/
theorem contrast_depth_upper (N D : ℕ) (hD : 0 < D) (hDN : D < N) :
    Pres.dSB (contrastPres N D hD hDN) ≤ N / D + D := by
  have h := contrast_depth_upper_tight N D hD hDN
  omega

end Contrast
end Two
end RatioSpace
