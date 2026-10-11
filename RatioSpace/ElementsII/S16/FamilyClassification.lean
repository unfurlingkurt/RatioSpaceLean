/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.ClosurePatternLink
import RatioSpace.ElementsII.S16.RootChain
/-!
  Elements II §16 Theorem 16.11, Step 2 — the `|D| ≤ 20` family `RⁿL`, for
  every `n`, and its mirror `LⁿR`.

  **Book statement.** For `F = RⁿL`, `C₊ = (n+1):1`, `C₋ = n:1`, the six
  tensions are the depths of `20n+5:20n+8`, `20n+5:20n+12`, `16n+4:16n+12`,
  `25n+10:25n+15`, `20n+8:20n+15`, `20n+12:20n+15`; `t₁₄ = 2n+2`, `t₂₃ = 5n+2`,
  and each remaining tension is `⌊N/k⌋` plus a term depending only on `N mod k`.
  For `n ≥ 13` the maximizer set lies in `{g₁, g₄}`, decided by `t₂₄ − t₁₃` and
  then `t₃₄ − t₁₂`, both periodic of period 21; it is a singleton except at
  `n ≡ 3 (mod 21)`, where it is the cousin pair `{RⁿLLL, RⁿLRR}`, and at `n = 0`.
  Side covariance gives `LⁿR`.

  **Computed before written.** With the kernel's definitions (depth of the
  reduced contrast as a quotient sum less one, exact sign in `ℤ[φ]`,
  re-implemented as in `elements_ii_axiom_ii1.py`) for `0 ≤ n < 1680`: every
  claim above holds. The book's contrasts are the tree's,
  in the tree's orientation. `t₂₄ − t₁₃` depends only on `n mod 7`
  (`3, −4, 2, 0, −2, 5, −1`) and `t₃₄ − t₁₂` only on `n mod 3` (`0, 2, 5`), so
  the period 21 is `7 · 3`, and the tie is exactly where both vanish. The
  exceptions are the same for every `n ≥ 1`, not only `n ≥ 13`: `n = 1, …, 12`
  follow the mod-21 pattern, including the tie at `n = 3`. `n = 0` has
  maximizer set `{g₁, g₃}`. No book statement was found false.

  **How.** One lemma, `tEnd_offset`, is the book's sentence: if the contrast is
  `N : N + k` then `t = ⌊N/k⌋ + cs (N mod k) k`, where `cs r k` is the
  Euclidean-quotient sum of `r:k` (RootChain's `sum_mulR`: a quotient `m` costs
  `m`). Residues pin `cs` to a constant, `omega` does the rest. The coherence value
  comparisons are three `ℤ[φ]` lemmas: two-deeper (Step 1's), one-and-two
  deeper, and equal-first-then-strict. No threshold is injected: the proof
  needs `n ≥ 2` for the elimination of `g₂, g₃` and does `n = 1` by hand,
  where `g₂` beats `g₁` but not `g₄`.

  **Built.** Closed forms of all six tensions for every `n` (floor form, and
  `20j + c` per residue); the two period-21 differences; the support for every
  `n ≥ 1` (`step2_family_LL`, `step2_family_RR`, `step2_family_tie`,
  `step2_family_support`, `step2_family_sub`); `n = 0`; the frames are the words
  (`walk_RnL`, `walk_LnR`); the mirror `LⁿR`; the bridge to `axiomSelect` at
  a sibling step (`sibling_step_RnL_*`, `sibling_step_LnR_*`); and, 2026-09-13
  23:30, the six `advanceCarrier` restatements of those sibling-step theorems
  (`advanceCarrier_active_RnL_*`, `advanceCarrier_active_LnR_*`). All on
  `tEnd`, `coherenceOf` and Definition 8.1's `support`. None uses
  `Classical.choice`.

  **Not built here.** The 527 non-generic frames of Step 2 outside these two
  families; Step 3 (cousin steps, built in `Step3Cousin.lean`); and the
  induction assembling clauses 1-4.
-/
set_option linter.style.show false

namespace RatioSpace
namespace Two
namespace Step2Family

open Pres Contrast Zphi PhiPos Automorphism Beat11

/-! ## The frames -/

/-- The frame of `RⁿL`: `C₊ = (n+1):1`, `C₋ = n:1`. -/
def Frn (n : ℕ) : Frame :=
  ⟨⟨n + 1, 1, fun h => Nat.succ_ne_zero n h.1⟩, ⟨n, 1, fun h => one_ne_zero h.2⟩,
    by show (n + 1) * 1 = 1 * n + 1; rw [Nat.mul_one, Nat.one_mul]⟩

/-- The frame of `LⁿR`: `C₊ = 1:n`, `C₋ = 1:(n+1)`. -/
def Fm (n : ℕ) : Frame :=
  ⟨⟨1, n, fun h => one_ne_zero h.1⟩, ⟨1, n + 1, fun h => Nat.succ_ne_zero n h.2⟩,
    by show 1 * (n + 1) = n * 1 + 1; rw [Nat.mul_one, Nat.one_mul]⟩

/-! ## One lemma for every tension: `t = ⌊N/k⌋ + cs (N mod k) k` -/

/-- The Euclidean-quotient sum of `r:k`, the book's "term depending only on
    `N mod k`". -/
def cs (r k : ℕ) : ℕ := (cfNat r k).sum

/-- **The book's tension form.** If `A ⊗ B = N : (N + k)` unreduced, then
    `t(A,B) = ⌊N/k⌋ + cs (N mod k) k`: one unit for the subtraction of `N`, then
    the quotient `⌊N/k⌋` costs itself, and what is left is `r:k`. -/
theorem tEnd_offset (A B : IPres) (N k : ℕ) (hN : 0 < N) (hk : 0 < k)
    (h1 : A.p * B.q = N) (h2 : A.q * B.p = N + k) :
    tEnd A B = N / k + cs (N % k) k := by
  rw [RootChain.tEnd_eq_sum, h1, h2, cfNat_sum_add_left (by omega) (by omega)]
  have e := RootChain.sum_mulR (N % k) k (N / k) (by omega)
  rw [show N % k + N / k * k = N by rw [Nat.mul_comm]; exact Nat.mod_add_div N k] at e
  unfold cs
  omega

/-! ### The six tensions of `RⁿL`, every `n` -/

/-- `t12`: the contrast is `20 * n + 5 : 20 * n + 5 + 3`. -/
theorem t12_eq (n : ℕ) :
    tEnd (gLL (Frn n)) (gLR (Frn n)) = (20 * n + 5) / 3 + cs ((20 * n + 5) % 3) 3 :=
  tEnd_offset _ _ _ _ (by omega) (by decide)
    (by show (1 * (n + 1) + 3 * n) * (2 * 1 + 3 * 1) = _; ring)
    (by show (1 * 1 + 3 * 1) * (2 * (n + 1) + 3 * n) = _; ring)

/-- `t13`: the contrast is `20 * n + 5 : 20 * n + 5 + 7`. -/
theorem t13_eq (n : ℕ) :
    tEnd (gLL (Frn n)) (gRL (Frn n)) = (20 * n + 5) / 7 + cs ((20 * n + 5) % 7) 7 :=
  tEnd_offset _ _ _ _ (by omega) (by decide)
    (by show (1 * (n + 1) + 3 * n) * (3 * 1 + 2 * 1) = _; ring)
    (by show (1 * 1 + 3 * 1) * (3 * (n + 1) + 2 * n) = _; ring)

/-- `t14`: the contrast is `16 * n + 4 : 16 * n + 4 + 8`. -/
theorem t14_eq (n : ℕ) :
    tEnd (gLL (Frn n)) (gRR (Frn n)) = (16 * n + 4) / 8 + cs ((16 * n + 4) % 8) 8 :=
  tEnd_offset _ _ _ _ (by omega) (by decide)
    (by show (1 * (n + 1) + 3 * n) * (3 * 1 + 1 * 1) = _; ring)
    (by show (1 * 1 + 3 * 1) * (3 * (n + 1) + 1 * n) = _; ring)

/-- `t23`: the contrast is `25 * n + 10 : 25 * n + 10 + 5`. -/
theorem t23_eq (n : ℕ) :
    tEnd (gLR (Frn n)) (gRL (Frn n)) = (25 * n + 10) / 5 + cs ((25 * n + 10) % 5) 5 :=
  tEnd_offset _ _ _ _ (by omega) (by decide)
    (by show (2 * (n + 1) + 3 * n) * (3 * 1 + 2 * 1) = _; ring)
    (by show (2 * 1 + 3 * 1) * (3 * (n + 1) + 2 * n) = _; ring)

/-- `t24`: the contrast is `20 * n + 8 : 20 * n + 8 + 7`. -/
theorem t24_eq (n : ℕ) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) = (20 * n + 8) / 7 + cs ((20 * n + 8) % 7) 7 :=
  tEnd_offset _ _ _ _ (by omega) (by decide)
    (by show (2 * (n + 1) + 3 * n) * (3 * 1 + 1 * 1) = _; ring)
    (by show (2 * 1 + 3 * 1) * (3 * (n + 1) + 1 * n) = _; ring)

/-- `t34`: the contrast is `20 * n + 12 : 20 * n + 12 + 3`. -/
theorem t34_eq (n : ℕ) :
    tEnd (gRL (Frn n)) (gRR (Frn n)) = (20 * n + 12) / 3 + cs ((20 * n + 12) % 3) 3 :=
  tEnd_offset _ _ _ _ (by omega) (by decide)
    (by show (3 * (n + 1) + 2 * n) * (3 * 1 + 1 * 1) = _; ring)
    (by show (3 * 1 + 2 * 1) * (3 * (n + 1) + 1 * n) = _; ring)

/-! ### The Euclidean tails that occur -/

theorem cs_0_3 : cs 0 3 = 0 := by decide
theorem cs_1_3 : cs 1 3 = 3 := by decide
theorem cs_2_3 : cs 2 3 = 3 := by decide
theorem cs_0_7 : cs 0 7 = 0 := by decide
theorem cs_1_7 : cs 1 7 = 7 := by decide
theorem cs_2_7 : cs 2 7 = 5 := by decide
theorem cs_3_7 : cs 3 7 = 5 := by decide
theorem cs_4_7 : cs 4 7 = 5 := by decide
theorem cs_5_7 : cs 5 7 = 5 := by decide
theorem cs_6_7 : cs 6 7 = 7 := by decide
theorem cs_4_8 : cs 4 8 = 2 := by decide
theorem cs_0_5 : cs 0 5 = 0 := by decide

/-- **`t₁₄ = 2n + 2`, for every `n`.** -/
theorem t14_closed (n : ℕ) : tEnd (gLL (Frn n)) (gRR (Frn n)) = 2 * n + 2 := by
  rw [t14_eq, show (16 * n + 4) % 8 = 4 by omega, cs_4_8]
  omega

/-- **`t₂₃ = 5n + 2`, for every `n`.** -/
theorem t23_closed (n : ℕ) : tEnd (gLR (Frn n)) (gRL (Frn n)) = 5 * n + 2 := by
  rw [t23_eq, show (25 * n + 10) % 5 = 0 by omega, cs_0_5]
  omega

/-! ### The four remaining tensions, by residue -/

theorem t13_mod7_0 (n : ℕ) (h : n % 7 = 0) :
    tEnd (gLL (Frn n)) (gRL (Frn n)) = (20 * n + 5) / 7 + 5 := by
  rw [t13_eq, show (20 * n + 5) % 7 = 5 by omega, cs_5_7]

theorem t13_mod7_1 (n : ℕ) (h : n % 7 = 1) :
    tEnd (gLL (Frn n)) (gRL (Frn n)) = (20 * n + 5) / 7 + 5 := by
  rw [t13_eq, show (20 * n + 5) % 7 = 4 by omega, cs_4_7]

theorem t13_mod7_2 (n : ℕ) (h : n % 7 = 2) :
    tEnd (gLL (Frn n)) (gRL (Frn n)) = (20 * n + 5) / 7 + 5 := by
  rw [t13_eq, show (20 * n + 5) % 7 = 3 by omega, cs_3_7]

theorem t13_mod7_3 (n : ℕ) (h : n % 7 = 3) :
    tEnd (gLL (Frn n)) (gRL (Frn n)) = (20 * n + 5) / 7 + 5 := by
  rw [t13_eq, show (20 * n + 5) % 7 = 2 by omega, cs_2_7]

theorem t13_mod7_4 (n : ℕ) (h : n % 7 = 4) :
    tEnd (gLL (Frn n)) (gRL (Frn n)) = (20 * n + 5) / 7 + 7 := by
  rw [t13_eq, show (20 * n + 5) % 7 = 1 by omega, cs_1_7]

theorem t13_mod7_5 (n : ℕ) (h : n % 7 = 5) :
    tEnd (gLL (Frn n)) (gRL (Frn n)) = (20 * n + 5) / 7 + 0 := by
  rw [t13_eq, show (20 * n + 5) % 7 = 0 by omega, cs_0_7]

theorem t13_mod7_6 (n : ℕ) (h : n % 7 = 6) :
    tEnd (gLL (Frn n)) (gRL (Frn n)) = (20 * n + 5) / 7 + 7 := by
  rw [t13_eq, show (20 * n + 5) % 7 = 6 by omega, cs_6_7]

theorem t24_mod7_0 (n : ℕ) (h : n % 7 = 0) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) = (20 * n + 8) / 7 + 7 := by
  rw [t24_eq, show (20 * n + 8) % 7 = 1 by omega, cs_1_7]

theorem t24_mod7_1 (n : ℕ) (h : n % 7 = 1) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) = (20 * n + 8) / 7 + 0 := by
  rw [t24_eq, show (20 * n + 8) % 7 = 0 by omega, cs_0_7]

theorem t24_mod7_2 (n : ℕ) (h : n % 7 = 2) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) = (20 * n + 8) / 7 + 7 := by
  rw [t24_eq, show (20 * n + 8) % 7 = 6 by omega, cs_6_7]

theorem t24_mod7_3 (n : ℕ) (h : n % 7 = 3) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) = (20 * n + 8) / 7 + 5 := by
  rw [t24_eq, show (20 * n + 8) % 7 = 5 by omega, cs_5_7]

theorem t24_mod7_4 (n : ℕ) (h : n % 7 = 4) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) = (20 * n + 8) / 7 + 5 := by
  rw [t24_eq, show (20 * n + 8) % 7 = 4 by omega, cs_4_7]

theorem t24_mod7_5 (n : ℕ) (h : n % 7 = 5) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) = (20 * n + 8) / 7 + 5 := by
  rw [t24_eq, show (20 * n + 8) % 7 = 3 by omega, cs_3_7]

theorem t24_mod7_6 (n : ℕ) (h : n % 7 = 6) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) = (20 * n + 8) / 7 + 5 := by
  rw [t24_eq, show (20 * n + 8) % 7 = 2 by omega, cs_2_7]

theorem t12_mod3_0 (n : ℕ) (h : n % 3 = 0) :
    tEnd (gLL (Frn n)) (gLR (Frn n)) = (20 * n + 5) / 3 + 3 := by
  rw [t12_eq, show (20 * n + 5) % 3 = 2 by omega, cs_2_3]

theorem t12_mod3_1 (n : ℕ) (h : n % 3 = 1) :
    tEnd (gLL (Frn n)) (gLR (Frn n)) = (20 * n + 5) / 3 + 3 := by
  rw [t12_eq, show (20 * n + 5) % 3 = 1 by omega, cs_1_3]

theorem t12_mod3_2 (n : ℕ) (h : n % 3 = 2) :
    tEnd (gLL (Frn n)) (gLR (Frn n)) = (20 * n + 5) / 3 + 0 := by
  rw [t12_eq, show (20 * n + 5) % 3 = 0 by omega, cs_0_3]

theorem t34_mod3_0 (n : ℕ) (h : n % 3 = 0) :
    tEnd (gRL (Frn n)) (gRR (Frn n)) = (20 * n + 12) / 3 + 0 := by
  rw [t34_eq, show (20 * n + 12) % 3 = 0 by omega, cs_0_3]

theorem t34_mod3_1 (n : ℕ) (h : n % 3 = 1) :
    tEnd (gRL (Frn n)) (gRR (Frn n)) = (20 * n + 12) / 3 + 3 := by
  rw [t34_eq, show (20 * n + 12) % 3 = 2 by omega, cs_2_3]

theorem t34_mod3_2 (n : ℕ) (h : n % 3 = 2) :
    tEnd (gRL (Frn n)) (gRR (Frn n)) = (20 * n + 12) / 3 + 3 := by
  rw [t34_eq, show (20 * n + 12) % 3 = 1 by omega, cs_1_3]

/-! ### Closed forms `20j + c` on each residue class -/

theorem t12_at_3j0 (j : ℕ) :
    tEnd (gLL (Frn (3 * j + 0))) (gLR (Frn (3 * j + 0))) = 20 * j + 4 := by
  rw [t12_mod3_0 _ (by omega)]
  omega

theorem t12_at_3j1 (j : ℕ) :
    tEnd (gLL (Frn (3 * j + 1))) (gLR (Frn (3 * j + 1))) = 20 * j + 11 := by
  rw [t12_mod3_1 _ (by omega)]
  omega

theorem t12_at_3j2 (j : ℕ) :
    tEnd (gLL (Frn (3 * j + 2))) (gLR (Frn (3 * j + 2))) = 20 * j + 15 := by
  rw [t12_mod3_2 _ (by omega)]
  omega

theorem t13_at_7j0 (j : ℕ) :
    tEnd (gLL (Frn (7 * j + 0))) (gRL (Frn (7 * j + 0))) = 20 * j + 5 := by
  rw [t13_mod7_0 _ (by omega)]
  omega

theorem t13_at_7j1 (j : ℕ) :
    tEnd (gLL (Frn (7 * j + 1))) (gRL (Frn (7 * j + 1))) = 20 * j + 8 := by
  rw [t13_mod7_1 _ (by omega)]
  omega

theorem t13_at_7j2 (j : ℕ) :
    tEnd (gLL (Frn (7 * j + 2))) (gRL (Frn (7 * j + 2))) = 20 * j + 11 := by
  rw [t13_mod7_2 _ (by omega)]
  omega

theorem t13_at_7j3 (j : ℕ) :
    tEnd (gLL (Frn (7 * j + 3))) (gRL (Frn (7 * j + 3))) = 20 * j + 14 := by
  rw [t13_mod7_3 _ (by omega)]
  omega

theorem t13_at_7j4 (j : ℕ) :
    tEnd (gLL (Frn (7 * j + 4))) (gRL (Frn (7 * j + 4))) = 20 * j + 19 := by
  rw [t13_mod7_4 _ (by omega)]
  omega

theorem t13_at_7j5 (j : ℕ) :
    tEnd (gLL (Frn (7 * j + 5))) (gRL (Frn (7 * j + 5))) = 20 * j + 15 := by
  rw [t13_mod7_5 _ (by omega)]
  omega

theorem t13_at_7j6 (j : ℕ) :
    tEnd (gLL (Frn (7 * j + 6))) (gRL (Frn (7 * j + 6))) = 20 * j + 24 := by
  rw [t13_mod7_6 _ (by omega)]
  omega

theorem t24_at_7j0 (j : ℕ) :
    tEnd (gLR (Frn (7 * j + 0))) (gRR (Frn (7 * j + 0))) = 20 * j + 8 := by
  rw [t24_mod7_0 _ (by omega)]
  omega

theorem t24_at_7j1 (j : ℕ) :
    tEnd (gLR (Frn (7 * j + 1))) (gRR (Frn (7 * j + 1))) = 20 * j + 4 := by
  rw [t24_mod7_1 _ (by omega)]
  omega

theorem t24_at_7j2 (j : ℕ) :
    tEnd (gLR (Frn (7 * j + 2))) (gRR (Frn (7 * j + 2))) = 20 * j + 13 := by
  rw [t24_mod7_2 _ (by omega)]
  omega

theorem t24_at_7j3 (j : ℕ) :
    tEnd (gLR (Frn (7 * j + 3))) (gRR (Frn (7 * j + 3))) = 20 * j + 14 := by
  rw [t24_mod7_3 _ (by omega)]
  omega

theorem t24_at_7j4 (j : ℕ) :
    tEnd (gLR (Frn (7 * j + 4))) (gRR (Frn (7 * j + 4))) = 20 * j + 17 := by
  rw [t24_mod7_4 _ (by omega)]
  omega

theorem t24_at_7j5 (j : ℕ) :
    tEnd (gLR (Frn (7 * j + 5))) (gRR (Frn (7 * j + 5))) = 20 * j + 20 := by
  rw [t24_mod7_5 _ (by omega)]
  omega

theorem t24_at_7j6 (j : ℕ) :
    tEnd (gLR (Frn (7 * j + 6))) (gRR (Frn (7 * j + 6))) = 20 * j + 23 := by
  rw [t24_mod7_6 _ (by omega)]
  omega

theorem t34_at_3j0 (j : ℕ) :
    tEnd (gRL (Frn (3 * j + 0))) (gRR (Frn (3 * j + 0))) = 20 * j + 4 := by
  rw [t34_mod3_0 _ (by omega)]
  omega

theorem t34_at_3j1 (j : ℕ) :
    tEnd (gRL (Frn (3 * j + 1))) (gRR (Frn (3 * j + 1))) = 20 * j + 13 := by
  rw [t34_mod3_1 _ (by omega)]
  omega

theorem t34_at_3j2 (j : ℕ) :
    tEnd (gRL (Frn (3 * j + 2))) (gRR (Frn (3 * j + 2))) = 20 * j + 20 := by
  rw [t34_mod3_2 _ (by omega)]
  omega

/-! ### The two differences Step 2 decides on, period 7 and period 3 -/

theorem d24_13_mod7_0 (n : ℕ) (h : n % 7 = 0) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) = tEnd (gLL (Frn n)) (gRL (Frn n)) + 3 := by
  rw [t24_mod7_0 n h, t13_mod7_0 n h]
  omega

theorem d24_13_mod7_1 (n : ℕ) (h : n % 7 = 1) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) + 4 = tEnd (gLL (Frn n)) (gRL (Frn n)) := by
  rw [t24_mod7_1 n h, t13_mod7_1 n h]
  omega

theorem d24_13_mod7_2 (n : ℕ) (h : n % 7 = 2) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) = tEnd (gLL (Frn n)) (gRL (Frn n)) + 2 := by
  rw [t24_mod7_2 n h, t13_mod7_2 n h]
  omega

theorem d24_13_mod7_3 (n : ℕ) (h : n % 7 = 3) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) = tEnd (gLL (Frn n)) (gRL (Frn n)) := by
  rw [t24_mod7_3 n h, t13_mod7_3 n h]
  omega

theorem d24_13_mod7_4 (n : ℕ) (h : n % 7 = 4) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) + 2 = tEnd (gLL (Frn n)) (gRL (Frn n)) := by
  rw [t24_mod7_4 n h, t13_mod7_4 n h]
  omega

theorem d24_13_mod7_5 (n : ℕ) (h : n % 7 = 5) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) = tEnd (gLL (Frn n)) (gRL (Frn n)) + 5 := by
  rw [t24_mod7_5 n h, t13_mod7_5 n h]
  omega

theorem d24_13_mod7_6 (n : ℕ) (h : n % 7 = 6) :
    tEnd (gLR (Frn n)) (gRR (Frn n)) + 1 = tEnd (gLL (Frn n)) (gRL (Frn n)) := by
  rw [t24_mod7_6 n h, t13_mod7_6 n h]
  omega

theorem d34_12_mod3_0 (n : ℕ) (h : n % 3 = 0) :
    tEnd (gRL (Frn n)) (gRR (Frn n)) = tEnd (gLL (Frn n)) (gLR (Frn n)) := by
  rw [t34_mod3_0 n h, t12_mod3_0 n h]
  omega

theorem d34_12_mod3_1 (n : ℕ) (h : n % 3 = 1) :
    tEnd (gRL (Frn n)) (gRR (Frn n)) = tEnd (gLL (Frn n)) (gLR (Frn n)) + 2 := by
  rw [t34_mod3_1 n h, t12_mod3_1 n h]
  omega

theorem d34_12_mod3_2 (n : ℕ) (h : n % 3 = 2) :
    tEnd (gRL (Frn n)) (gRR (Frn n)) = tEnd (gLL (Frn n)) (gLR (Frn n)) + 5 := by
  rw [t34_mod3_2 n h, t12_mod3_2 n h]
  omega

/-! ## Coherence comparisons on any frame, from tension inequalities -/

/-- `φ⁻ᶜ + φ⁻ᵈ < φ⁻ᵃ + φ⁻ᵇ` once `d ≥ b + 1` and `c ≥ b + 2`:
    `φ⁻⁽ᵇ⁺²⁾ + φ⁻⁽ᵇ⁺¹⁾ = φ⁻ᵇ`. -/
theorem sum_lt_of_one_two {a b c d : ℕ} (hd : b + 1 ≤ d) (hc : b + 2 ≤ c) :
    phiNegPow c + phiNegPow d < phiNegPow a + phiNegPow b :=
  calc phiNegPow c + phiNegPow d ≤ phiNegPow (b + 2) + phiNegPow (b + 1) :=
        add_le_add (phiNegPow_anti_le hc) (phiNegPow_anti_le hd)
    _ = phiNegPow b := (add_comm _ _).trans (phiNegPow_rec b).symm
    _ < phiNegPow b + phiNegPow a := lt_add_of_pos_right _ (PhiPos.phiNegPow_pos a)
    _ = phiNegPow a + phiNegPow b := add_comm _ _

section coherences

variable (F : Frame)

/-- `g₂` loses to `g₁` and `g₃` to `g₄` once `t₁₄ + 2 ≤ t₁₃, t₂₃, t₂₄`. -/
theorem lose_LR_RL (m13 : tEnd (gLL (F)) (gRR (F)) + 2 ≤ tEnd (gLL (F)) (gRL (F)))
    (m23 : tEnd (gLL (F)) (gRR (F)) + 2 ≤ tEnd (gLR (F)) (gRL (F)))
    (m24 : tEnd (gLL (F)) (gRR (F)) + 2 ≤ tEnd (gLR (F)) (gRR (F))) :
    coherenceOf (grand (F)) (gLR (F)) < coherenceOf (grand (F)) (gLL (F)) ∧
    coherenceOf (grand (F)) (gRL (F)) < coherenceOf (grand (F)) (gRR (F)) := by
  refine ⟨?_, ?_⟩
  · rw [coherence_LR, coherence_LL]
    exact add_lt_add_right_zphi (sum_lt_of_two_deeper m23 m24)
  · rw [coherence_RL, coherence_RR]
    exact add_lt_add_right_zphi (sum_lt_of_two_deeper m13 m23)

/-- `g₃` loses to `g₄` once `t₁₄ + 2 ≤ t₁₃, t₂₃`; `t₂₄` is not needed. -/
theorem RL_lt_RR (m13 : tEnd (gLL (F)) (gRR (F)) + 2 ≤ tEnd (gLL (F)) (gRL (F)))
    (m23 : tEnd (gLL (F)) (gRR (F)) + 2 ≤ tEnd (gLR (F)) (gRL (F))) :
    coherenceOf (grand (F)) (gRL (F)) < coherenceOf (grand (F)) (gRR (F)) := by
  rw [coherence_RL, coherence_RR]
  exact add_lt_add_right_zphi (sum_lt_of_two_deeper m13 m23)

/-- `g₂` loses to `g₄` once `t₁₄ + 2 ≤ t₁₂, t₂₃`. -/
theorem LR_lt_RR (m12 : tEnd (gLL (F)) (gRR (F)) + 2 ≤ tEnd (gLL (F)) (gLR (F)))
    (m23 : tEnd (gLL (F)) (gRR (F)) + 2 ≤ tEnd (gLR (F)) (gRL (F))) :
    coherenceOf (grand (F)) (gLR (F)) < coherenceOf (grand (F)) (gRR (F)) := by
  rw [coherence_LR, coherence_RR]
  have h := add_lt_add_right_zphi (a := phiNegPow 0 + phiNegPow (tEnd (gLR (F)) (gRR (F))))
    (sum_lt_of_two_deeper (v := tEnd (gRL (F)) (gRR (F))) m12 m23)
  calc _ = (phiNegPow (tEnd (gLL (F)) (gLR (F))) + phiNegPow (tEnd (gLR (F)) (gRL (F))))
          + (phiNegPow 0 + phiNegPow (tEnd (gLR (F)) (gRR (F)))) := by ring
    _ < _ := h
    _ = _ := by ring

/-- **The first difference decides.** `t₂₄ ≥ t₁₃ + 1` and `t₃₄ ≥ t₁₃ + 2`
    give `C(g₄) < C(g₁)`. -/
theorem RR_lt_LL_of_deeper (h1 : tEnd (gLL (F)) (gRL (F)) + 1 ≤ tEnd (gLR (F)) (gRR (F)))
    (h2 : tEnd (gLL (F)) (gRL (F)) + 2 ≤ tEnd (gRL (F)) (gRR (F))) :
    coherenceOf (grand (F)) (gRR (F)) < coherenceOf (grand (F)) (gLL (F)) := by
  rw [coherence_RR', coherence_LL']
  exact add_lt_add_right_zphi (sum_lt_of_one_two h1 h2)

/-- The mirror: `t₁₃ ≥ t₂₄ + 1` and `t₁₂ ≥ t₂₄ + 2` give `C(g₁) < C(g₄)`. -/
theorem LL_lt_RR_of_deeper (h1 : tEnd (gLR (F)) (gRR (F)) + 1 ≤ tEnd (gLL (F)) (gRL (F)))
    (h2 : tEnd (gLR (F)) (gRR (F)) + 2 ≤ tEnd (gLL (F)) (gLR (F))) :
    coherenceOf (grand (F)) (gLL (F)) < coherenceOf (grand (F)) (gRR (F)) := by
  rw [coherence_RR', coherence_LL']
  exact add_lt_add_right_zphi (sum_lt_of_one_two h1 h2)

/-- **Then the second.** `t₁₃ = t₂₄` and `t₁₂ < t₃₄` give `C(g₄) < C(g₁)`. -/
theorem RR_lt_LL_of_eq (h1 : tEnd (gLL (F)) (gRL (F)) = tEnd (gLR (F)) (gRR (F)))
    (h2 : tEnd (gLL (F)) (gLR (F)) < tEnd (gRL (F)) (gRR (F))) :
    coherenceOf (grand (F)) (gRR (F)) < coherenceOf (grand (F)) (gLL (F)) := by
  rw [coherence_RR', coherence_LL', h1]
  exact add_lt_add_right_zphi (add_lt_add_right_zphi (phiNegPow_strict h2))

/-- **Both differences vanish: an exact tie.** -/
theorem LL_eq_RR (h1 : tEnd (gLL (F)) (gRL (F)) = tEnd (gLR (F)) (gRR (F)))
    (h2 : tEnd (gLL (F)) (gLR (F)) = tEnd (gRL (F)) (gRR (F))) :
    coherenceOf (grand (F)) (gLL (F)) = coherenceOf (grand (F)) (gRR (F)) := by
  rw [coherence_RR', coherence_LL', h1, h2]

/-! ## The three support shapes, on Definition 8.1's `support` -/

theorem support_LL_of (h2 : coherenceOf (grand (F)) (gLR (F)) < coherenceOf (grand (F)) (gLL (F)))
    (h3 : coherenceOf (grand (F)) (gRL (F)) < coherenceOf (grand (F)) (gLL (F))) (h4 :
      coherenceOf (grand (F)) (gRR (F)) < coherenceOf (grand (F)) (gLL (F))) :
    support (grand F) = [gLL F] := by
  refine support_grand_eq ?_ h2 h3 h4
  intro z hz
  rcases mem_grand hz with rfl | rfl | rfl | rfl
  · exact le_refl _
  · exact le_of_lt h2
  · exact le_of_lt h3
  · exact le_of_lt h4

/-- `selPred` fails on anything strictly beaten by a family member. -/
theorem not_sel {w z : IPres} (hz : z ∈ grand F)
    (h : coherenceOf (grand F) w < coherenceOf (grand F) z) : ¬ (selPred F w = true) :=
  fun hs => not_le_of_lt_zphi h (of_decide_eq_true (List.all_eq_true.mp hs z hz))

theorem gLR_mem : gLR F ∈ grand F := List.Mem.tail _ (List.Mem.head _)
theorem gRL_mem : gRL F ∈ grand F := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem support_RR_of (h1 : coherenceOf (grand (F)) (gLL (F)) < coherenceOf (grand (F)) (gRR (F)))
    (h2 : coherenceOf (grand (F)) (gLR (F)) < coherenceOf (grand (F)) (gRR (F))) (h3 :
      coherenceOf (grand (F)) (gRL (F)) < coherenceOf (grand (F)) (gRR (F))) :
    support (grand F) = [gRR F] := by
  have top : selPred F (gRR F) = true := by
    refine List.all_eq_true.mpr (fun z hz => decide_eq_true ?_)
    rcases mem_grand hz with rfl | rfl | rfl | rfl
    · exact le_of_lt h1
    · exact le_of_lt h2
    · exact le_of_lt h3
    · exact le_refl _
  unfold support
  show List.filter (selPred F) (gLL F :: gLR F :: gRL F :: gRR F :: []) = _
  rw [List.filter_cons_of_neg (p := selPred F) (not_sel F (gRR_mem F) h1),
    List.filter_cons_of_neg (p := selPred F) (not_sel F (gRR_mem F) h2),
    List.filter_cons_of_neg (p := selPred F) (not_sel F (gRR_mem F) h3),
    List.filter_cons_of_pos (p := selPred F) top]
  rfl

/-- **The cousin pair.** `C(g₁) = C(g₄)` above the other two: the support is
    `[g₁, g₄]`, both kept, no tie broken. -/
theorem support_tie_of (h2 : coherenceOf (grand (F)) (gLR (F)) < coherenceOf (grand (F)) (gLL (F)))
    (h3 : coherenceOf (grand (F)) (gRL (F)) < coherenceOf (grand (F)) (gLL (F))) (heq :
      coherenceOf (grand (F)) (gLL (F)) = coherenceOf (grand (F)) (gRR (F))) :
    support (grand F) = [gLL F, gRR F] := by
  have top : ∀ y, coherenceOf (grand F) y = coherenceOf (grand (F)) (gLL (F)) → selPred F y =
    true := by
    intro y hy
    refine List.all_eq_true.mpr (fun z hz => decide_eq_true ?_)
    rw [hy]
    rcases mem_grand hz with rfl | rfl | rfl | rfl
    · exact le_refl _
    · exact le_of_lt h2
    · exact le_of_lt h3
    · exact le_of_eq heq.symm
  unfold support
  show List.filter (selPred F) (gLL F :: gLR F :: gRL F :: gRR F :: []) = _
  rw [List.filter_cons_of_pos (p := selPred F) (top _ rfl),
    List.filter_cons_of_neg (p := selPred F) (not_sel F (gLL_mem F) h2),
    List.filter_cons_of_neg (p := selPred F) (not_sel F (gLL_mem F) h3),
    List.filter_cons_of_pos (p := selPred F) (top _ heq.symm)]
  rfl

end coherences

/-! ## `RⁿL`: the coherence value order, residue by residue -/

theorem order_mod7_0 (n : ℕ) (hn : 2 ≤ n) (h : n % 7 = 0) :
    coherenceOf (grand (Frn n)) (gLR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRL (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) := by
  have e12 := t12_eq n
  have e34 := t34_eq n
  have e14 := t14_closed n
  have e23 := t23_closed n
  have e13 := t13_mod7_0 n h
  have e24 := t24_mod7_0 n h
  obtain ⟨h21, h34⟩ := lose_LR_RL (Frn n) (by omega) (by omega) (by omega)
  have h41 := RR_lt_LL_of_deeper (Frn n) (by omega) (by omega)
  exact ⟨h21, lt_trans h34 h41, h41⟩

theorem order_mod7_1 (n : ℕ) (hn : 2 ≤ n) (h : n % 7 = 1) :
    coherenceOf (grand (Frn n)) (gLL (Frn n)) < coherenceOf (grand (Frn n)) (gRR (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gLR (Frn n)) < coherenceOf (grand (Frn n)) (gRR (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRL (Frn n)) < coherenceOf (grand (Frn n)) (gRR (Frn n)) := by
  have e12 := t12_eq n
  have e34 := t34_eq n
  have e14 := t14_closed n
  have e23 := t23_closed n
  have e13 := t13_mod7_1 n h
  have e24 := t24_mod7_1 n h
  obtain ⟨h21, h34⟩ := lose_LR_RL (Frn n) (by omega) (by omega) (by omega)
  have h14 := LL_lt_RR_of_deeper (Frn n) (by omega) (by omega)
  exact ⟨h14, lt_trans h21 h14, h34⟩

theorem order_mod7_2 (n : ℕ) (h : n % 7 = 2) :
    coherenceOf (grand (Frn n)) (gLR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRL (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) := by
  have e12 := t12_eq n
  have e34 := t34_eq n
  have e14 := t14_closed n
  have e23 := t23_closed n
  have e13 := t13_mod7_2 n h
  have e24 := t24_mod7_2 n h
  obtain ⟨h21, h34⟩ := lose_LR_RL (Frn n) (by omega) (by omega) (by omega)
  have h41 := RR_lt_LL_of_deeper (Frn n) (by omega) (by omega)
  exact ⟨h21, lt_trans h34 h41, h41⟩

theorem order_mod7_4 (n : ℕ) (h : n % 7 = 4) :
    coherenceOf (grand (Frn n)) (gLL (Frn n)) < coherenceOf (grand (Frn n)) (gRR (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gLR (Frn n)) < coherenceOf (grand (Frn n)) (gRR (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRL (Frn n)) < coherenceOf (grand (Frn n)) (gRR (Frn n)) := by
  have e12 := t12_eq n
  have e34 := t34_eq n
  have e14 := t14_closed n
  have e23 := t23_closed n
  have e13 := t13_mod7_4 n h
  have e24 := t24_mod7_4 n h
  obtain ⟨h21, h34⟩ := lose_LR_RL (Frn n) (by omega) (by omega) (by omega)
  have h14 := LL_lt_RR_of_deeper (Frn n) (by omega) (by omega)
  exact ⟨h14, lt_trans h21 h14, h34⟩

theorem order_mod7_5 (n : ℕ) (h : n % 7 = 5) :
    coherenceOf (grand (Frn n)) (gLR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRL (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) := by
  have e12 := t12_eq n
  have e34 := t34_eq n
  have e14 := t14_closed n
  have e23 := t23_closed n
  have e13 := t13_mod7_5 n h
  have e24 := t24_mod7_5 n h
  obtain ⟨h21, h34⟩ := lose_LR_RL (Frn n) (by omega) (by omega) (by omega)
  have h41 := RR_lt_LL_of_deeper (Frn n) (by omega) (by omega)
  exact ⟨h21, lt_trans h34 h41, h41⟩

theorem order_mod7_6 (n : ℕ) (h : n % 7 = 6) :
    coherenceOf (grand (Frn n)) (gLL (Frn n)) < coherenceOf (grand (Frn n)) (gRR (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gLR (Frn n)) < coherenceOf (grand (Frn n)) (gRR (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRL (Frn n)) < coherenceOf (grand (Frn n)) (gRR (Frn n)) := by
  have e12 := t12_eq n
  have e34 := t34_eq n
  have e14 := t14_closed n
  have e23 := t23_closed n
  have e13 := t13_mod7_6 n h
  have e24 := t24_mod7_6 n h
  obtain ⟨h21, h34⟩ := lose_LR_RL (Frn n) (by omega) (by omega) (by omega)
  have h14 := LL_lt_RR_of_deeper (Frn n) (by omega) (by omega)
  exact ⟨h14, lt_trans h21 h14, h34⟩

theorem order_mod7_3_mod3_1 (n : ℕ) (h : n % 7 = 3) (h3 : n % 3 = 1) :
    coherenceOf (grand (Frn n)) (gLR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRL (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) := by
  have e12 := t12_eq n
  have e34 := t34_eq n
  have e14 := t14_closed n
  have e23 := t23_closed n
  have e13 := t13_mod7_3 n h
  have e24 := t24_mod7_3 n h
  have f12 := t12_mod3_1 n h3
  have f34 := t34_mod3_1 n h3
  obtain ⟨h21, h34⟩ := lose_LR_RL (Frn n) (by omega) (by omega) (by omega)
  have h41 := RR_lt_LL_of_eq (Frn n) (by omega) (by omega)
  exact ⟨h21, lt_trans h34 h41, h41⟩

theorem order_mod7_3_mod3_2 (n : ℕ) (h : n % 7 = 3) (h3 : n % 3 = 2) :
    coherenceOf (grand (Frn n)) (gLR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRL (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) := by
  have e12 := t12_eq n
  have e34 := t34_eq n
  have e14 := t14_closed n
  have e23 := t23_closed n
  have e13 := t13_mod7_3 n h
  have e24 := t24_mod7_3 n h
  have f12 := t12_mod3_2 n h3
  have f34 := t34_mod3_2 n h3
  obtain ⟨h21, h34⟩ := lose_LR_RL (Frn n) (by omega) (by omega) (by omega)
  have h41 := RR_lt_LL_of_eq (Frn n) (by omega) (by omega)
  exact ⟨h21, lt_trans h34 h41, h41⟩

theorem order_tie (n : ℕ) (h : n % 21 = 3) :
    coherenceOf (grand (Frn n)) (gLR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRL (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gLL (Frn n)) = coherenceOf (grand (Frn n)) (gRR (Frn n)) := by
  have e12 := t12_eq n
  have e34 := t34_eq n
  have e14 := t14_closed n
  have e23 := t23_closed n
  have e13 := t13_mod7_3 n (by omega)
  have e24 := t24_mod7_3 n (by omega)
  have f12 := t12_mod3_0 n (by omega)
  have f34 := t34_mod3_0 n (by omega)
  obtain ⟨h21, h34⟩ := lose_LR_RL (Frn n) (by omega) (by omega) (by omega)
  have heq := LL_eq_RR (Frn n) (by omega) (by omega)
  exact ⟨h21, lt_of_lt_of_eq h34 heq.symm, heq⟩

/-- `n = 1`: `g₂` beats `g₁` here (`t₁₃ = 8 > t₂₃ = 7`), so the elimination
    runs against `g₄` directly. -/
theorem order_one :
    coherenceOf (grand (Frn 1)) (gLL (Frn 1)) < coherenceOf (grand (Frn 1)) (gRR (Frn 1)) ∧
      coherenceOf (grand (Frn 1)) (gLR (Frn 1)) < coherenceOf (grand (Frn 1)) (gRR (Frn 1)) ∧
      coherenceOf (grand (Frn 1)) (gRL (Frn 1)) < coherenceOf (grand (Frn 1)) (gRR (Frn 1)) := by
  have e12 := t12_mod3_1 1 rfl
  have e13 := t13_mod7_1 1 rfl
  have e24 := t24_mod7_1 1 rfl
  have e34 := t34_mod3_1 1 rfl
  have e14 := t14_closed 1
  have e23 := t23_closed 1
  have h14 := LL_lt_RR_of_deeper (Frn 1) (by omega) (by omega)
  have h24 := LR_lt_RR (Frn 1) (by omega) (by omega)
  have h34 := RL_lt_RR (Frn 1) (by omega) (by omega)
  exact ⟨h14, h24, h34⟩

/-- The residues where `g₁` wins, as the book reads them mod 21. -/
theorem order_LL (n : ℕ) (hn : 1 ≤ n)
    (h : n % 21 = 0 ∨ n % 21 = 2 ∨ n % 21 = 5 ∨ n % 21 = 7 ∨ n % 21 = 9 ∨ n % 21 = 10 ∨ n % 21 =
      12 ∨ n % 21 = 14 ∨ n % 21 = 16 ∨ n % 21 = 17 ∨ n % 21 = 19) :
    coherenceOf (grand (Frn n)) (gLR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRL (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRR (Frn n)) < coherenceOf (grand (Frn n)) (gLL (Frn n)) := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · exact order_mod7_0 n (by omega) (by omega)
  · exact order_mod7_2 n (by omega)
  · exact order_mod7_5 n (by omega)
  · exact order_mod7_0 n (by omega) (by omega)
  · exact order_mod7_2 n (by omega)
  · exact order_mod7_3_mod3_1 n (by omega) (by omega)
  · exact order_mod7_5 n (by omega)
  · exact order_mod7_0 n (by omega) (by omega)
  · exact order_mod7_2 n (by omega)
  · exact order_mod7_3_mod3_2 n (by omega) (by omega)
  · exact order_mod7_5 n (by omega)

/-- The residues where `g₄` wins. -/
theorem order_RR (n : ℕ) (hn : 1 ≤ n)
    (h : n % 21 = 1 ∨ n % 21 = 4 ∨ n % 21 = 6 ∨ n % 21 = 8 ∨ n % 21 = 11 ∨ n % 21 = 13 ∨ n % 21
      = 15 ∨ n % 21 = 18 ∨ n % 21 = 20) :
    coherenceOf (grand (Frn n)) (gLL (Frn n)) < coherenceOf (grand (Frn n)) (gRR (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gLR (Frn n)) < coherenceOf (grand (Frn n)) (gRR (Frn n)) ∧
      coherenceOf (grand (Frn n)) (gRL (Frn n)) < coherenceOf (grand (Frn n)) (gRR (Frn n)) := by
  rcases h with h | h | h | h | h | h | h | h | h
  · rcases Nat.lt_or_ge n 2 with h1 | h1
    · have e : n = 1 := by omega
      subst e
      exact order_one
    · exact order_mod7_1 n h1 (by omega)
  · exact order_mod7_4 n (by omega)
  · exact order_mod7_6 n (by omega)
  · rcases Nat.lt_or_ge n 2 with h1 | h1
    · have e : n = 1 := by omega
      subst e
      exact order_one
    · exact order_mod7_1 n h1 (by omega)
  · exact order_mod7_4 n (by omega)
  · exact order_mod7_6 n (by omega)
  · rcases Nat.lt_or_ge n 2 with h1 | h1
    · have e : n = 1 := by omega
      subst e
      exact order_one
    · exact order_mod7_1 n h1 (by omega)
  · exact order_mod7_4 n (by omega)
  · exact order_mod7_6 n (by omega)

/-! ## Theorem 16.11, Step 2, the family `RⁿL` -/

/-- **`g₁ = RⁿLLL` is the unique maximizer** on eleven residues mod 21. -/
theorem step2_family_LL (n : ℕ) (hn : 1 ≤ n)
    (h : n % 21 = 0 ∨ n % 21 = 2 ∨ n % 21 = 5 ∨ n % 21 = 7 ∨ n % 21 = 9 ∨ n % 21 = 10 ∨ n % 21 =
      12 ∨ n % 21 = 14 ∨ n % 21 = 16 ∨ n % 21 = 17 ∨ n % 21 = 19) :
    support (grand (Frn n)) = [gLL (Frn n)] := by
  obtain ⟨h2, h3, h4⟩ := order_LL n hn h
  exact support_LL_of _ h2 h3 h4

/-- **`g₄ = RⁿLRR` is the unique maximizer** on the other nine singleton
    residues. -/
theorem step2_family_RR (n : ℕ) (hn : 1 ≤ n)
    (h : n % 21 = 1 ∨ n % 21 = 4 ∨ n % 21 = 6 ∨ n % 21 = 8 ∨ n % 21 = 11 ∨ n % 21 = 13 ∨ n % 21
      = 15 ∨ n % 21 = 18 ∨ n % 21 = 20) :
    support (grand (Frn n)) = [gRR (Frn n)] := by
  obtain ⟨h1, h2, h3⟩ := order_RR n hn h
  exact support_RR_of _ h1 h2 h3

/-- **At `n ≡ 3 (mod 21)` the maximizer set is the cousin pair
    `{RⁿLLL, RⁿLRR}`.** -/
theorem step2_family_tie (n : ℕ) (h : n % 21 = 3) :
    support (grand (Frn n)) = [gLL (Frn n), gRR (Frn n)] := by
  obtain ⟨h2, h3, heq⟩ := order_tie n h
  exact support_tie_of _ h2 h3 heq

theorem res21 (n : ℕ) : n % 21 = 0 ∨ n % 21 = 1 ∨ n % 21 = 2 ∨ n % 21 = 3 ∨ n % 21 = 4 ∨ n % 21
  = 5 ∨ n % 21 = 6 ∨ n % 21 = 7 ∨ n % 21 = 8 ∨ n % 21 = 9 ∨ n % 21 = 10 ∨ n % 21 = 11 ∨ n % 21 =
  12 ∨ n % 21 = 13 ∨ n % 21 = 14 ∨ n % 21 = 15 ∨ n % 21 = 16 ∨ n % 21 = 17 ∨ n % 21 = 18 ∨ n %
  21 = 19 ∨ n % 21 = 20 := by
  have h := Nat.mod_lt n (show 0 < 21 by decide)
  rcases hr : n % 21 with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    | _ | _ | _ | k
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    rfl)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    rfl))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl rfl)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl rfl))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl rfl)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))))))))))))
  · omega

/-- **Theorem 16.11, Step 2, as the book states it** (and for every `n ≥ 1`,
    not only `n ≥ 13`): off `n ≡ 3 (mod 21)` the maximizer set is a singleton,
    `g₁` or `g₄`. -/
theorem step2_family_support (n : ℕ) (hn : 1 ≤ n) (h : n % 21 ≠ 3) :
    support (grand (Frn n)) = [gLL (Frn n)] ∨ support (grand (Frn n)) = [gRR (Frn n)] := by
  rcases res21 n with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    | h | h
  · exact Or.inl (step2_family_LL n hn (by omega))
  · exact Or.inr (step2_family_RR n hn (by omega))
  · exact Or.inl (step2_family_LL n hn (by omega))
  · exact absurd h (by omega)
  · exact Or.inr (step2_family_RR n hn (by omega))
  · exact Or.inl (step2_family_LL n hn (by omega))
  · exact Or.inr (step2_family_RR n hn (by omega))
  · exact Or.inl (step2_family_LL n hn (by omega))
  · exact Or.inr (step2_family_RR n hn (by omega))
  · exact Or.inl (step2_family_LL n hn (by omega))
  · exact Or.inl (step2_family_LL n hn (by omega))
  · exact Or.inr (step2_family_RR n hn (by omega))
  · exact Or.inl (step2_family_LL n hn (by omega))
  · exact Or.inr (step2_family_RR n hn (by omega))
  · exact Or.inl (step2_family_LL n hn (by omega))
  · exact Or.inr (step2_family_RR n hn (by omega))
  · exact Or.inl (step2_family_LL n hn (by omega))
  · exact Or.inl (step2_family_LL n hn (by omega))
  · exact Or.inr (step2_family_RR n hn (by omega))
  · exact Or.inl (step2_family_LL n hn (by omega))
  · exact Or.inr (step2_family_RR n hn (by omega))

/-- **The maximizer set lies in `{g₁, g₄}`**, for every `n ≥ 1`. -/
theorem step2_family_sub (n : ℕ) (hn : 1 ≤ n) :
    ∀ y ∈ support (grand (Frn n)), y = gLL (Frn n) ∨ y = gRR (Frn n) := by
  intro y hy
  rcases Nat.decEq (n % 21) 3 with h | h
  · rcases step2_family_support n hn h with e | e <;> rw [e] at hy <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    · exact Or.inl hy
    · exact Or.inr hy
  · rw [step2_family_tie n h] at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    exact hy

/-- **`n = 0`, the frame of `L`**: the maximizer set is `{g₁, g₃}`. -/
theorem step2_family_zero :
    support (grand (Frn 0)) = [gLL (Frn 0), gRL (Frn 0)] := by
  decide

/-! ## The mirror `LⁿR`, by side covariance

  `Inv` exchanges `gLL (Fm n) ↔ gRR (Frn n)` and `gLR (Fm n) ↔ gRL (Frn n)`,
  so each tension of `LⁿR` is a tension of `RⁿL` with the indices reversed
  (Theorem 7.8's content; here each is recomputed from `tEnd_offset`, which is
  shorter than transporting through `Inv`). -/

theorem tm12 (n : ℕ) : tEnd (gLL (Fm n)) (gLR (Fm n)) = tEnd (gRL (Frn n)) (gRR (Frn n)) :=
  (tEnd_offset _ _ (20 * n + 12) 3 (by omega) (by decide)
    (by show (1 * 1 + 3 * 1) * (2 * n + 3 * (n + 1)) = _; ring)
    (by show (1 * n + 3 * (n + 1)) * (2 * 1 + 3 * 1) = _; ring)).trans (t34_eq n).symm

theorem tm13 (n : ℕ) : tEnd (gLL (Fm n)) (gRL (Fm n)) = tEnd (gLR (Frn n)) (gRR (Frn n)) :=
  (tEnd_offset _ _ (20 * n + 8) 7 (by omega) (by decide)
    (by show (1 * 1 + 3 * 1) * (3 * n + 2 * (n + 1)) = _; ring)
    (by show (1 * n + 3 * (n + 1)) * (3 * 1 + 2 * 1) = _; ring)).trans (t24_eq n).symm

theorem tm14 (n : ℕ) : tEnd (gLL (Fm n)) (gRR (Fm n)) = tEnd (gLL (Frn n)) (gRR (Frn n)) :=
  (tEnd_offset _ _ (16 * n + 4) 8 (by omega) (by decide)
    (by show (1 * 1 + 3 * 1) * (3 * n + 1 * (n + 1)) = _; ring)
    (by show (1 * n + 3 * (n + 1)) * (3 * 1 + 1 * 1) = _; ring)).trans (t14_eq n).symm

theorem tm23 (n : ℕ) : tEnd (gLR (Fm n)) (gRL (Fm n)) = tEnd (gLR (Frn n)) (gRL (Frn n)) :=
  (tEnd_offset _ _ (25 * n + 10) 5 (by omega) (by decide)
    (by show (2 * 1 + 3 * 1) * (3 * n + 2 * (n + 1)) = _; ring)
    (by show (2 * n + 3 * (n + 1)) * (3 * 1 + 2 * 1) = _; ring)).trans (t23_eq n).symm

theorem tm24 (n : ℕ) : tEnd (gLR (Fm n)) (gRR (Fm n)) = tEnd (gLL (Frn n)) (gRL (Frn n)) :=
  (tEnd_offset _ _ (20 * n + 5) 7 (by omega) (by decide)
    (by show (2 * 1 + 3 * 1) * (3 * n + 1 * (n + 1)) = _; ring)
    (by show (2 * n + 3 * (n + 1)) * (3 * 1 + 1 * 1) = _; ring)).trans (t13_eq n).symm

theorem tm34 (n : ℕ) : tEnd (gRL (Fm n)) (gRR (Fm n)) = tEnd (gLL (Frn n)) (gLR (Frn n)) :=
  (tEnd_offset _ _ (20 * n + 5) 3 (by omega) (by decide)
    (by show (3 * 1 + 2 * 1) * (3 * n + 1 * (n + 1)) = _; ring)
    (by show (3 * n + 2 * (n + 1)) * (3 * 1 + 1 * 1) = _; ring)).trans (t12_eq n).symm

theorem mC1 (n : ℕ) : coherenceOf (grand (Fm n)) (gLL (Fm n)) = coherenceOf (grand (Frn n)) (gRR
  (Frn n)) := by
  rw [coherence_LL', coherence_RR', tm12, tm13, tm14]

theorem mC2 (n : ℕ) : coherenceOf (grand (Fm n)) (gLR (Fm n)) = coherenceOf (grand (Frn n)) (gRL
  (Frn n)) := by
  rw [coherence_LR, coherence_RL, tm23, tm24, tm12]; ring

theorem mC3 (n : ℕ) : coherenceOf (grand (Fm n)) (gRL (Fm n)) = coherenceOf (grand (Frn n)) (gLR
  (Frn n)) := by
  rw [coherence_RL, coherence_LR, tm13, tm23, tm34]; ring

theorem mC4 (n : ℕ) : coherenceOf (grand (Fm n)) (gRR (Fm n)) = coherenceOf (grand (Frn n)) (gLL
  (Frn n)) := by
  rw [coherence_RR', coherence_LL', tm34, tm24, tm14]

theorem order_mirror_RR (n : ℕ) (hn : 1 ≤ n)
    (h : n % 21 = 0 ∨ n % 21 = 2 ∨ n % 21 = 5 ∨ n % 21 = 7 ∨ n % 21 = 9 ∨ n % 21 = 10 ∨ n % 21 =
      12 ∨ n % 21 = 14 ∨ n % 21 = 16 ∨ n % 21 = 17 ∨ n % 21 = 19) :
    coherenceOf (grand (Fm n)) (gLL (Fm n)) < coherenceOf (grand (Fm n)) (gRR (Fm n)) ∧
      coherenceOf (grand (Fm n)) (gLR (Fm n)) < coherenceOf (grand (Fm n)) (gRR (Fm n)) ∧
      coherenceOf (grand (Fm n)) (gRL (Fm n)) < coherenceOf (grand (Fm n)) (gRR (Fm n)) := by
  obtain ⟨h2, h3, h4⟩ := order_LL n hn h
  exact ⟨by rw [mC1, mC4]; exact h4, by rw [mC2, mC4]; exact h3, by rw [mC3, mC4]; exact h2⟩

theorem order_mirror_LL (n : ℕ) (hn : 1 ≤ n)
    (h : n % 21 = 1 ∨ n % 21 = 4 ∨ n % 21 = 6 ∨ n % 21 = 8 ∨ n % 21 = 11 ∨ n % 21 = 13 ∨ n % 21
      = 15 ∨ n % 21 = 18 ∨ n % 21 = 20) :
    coherenceOf (grand (Fm n)) (gLR (Fm n)) < coherenceOf (grand (Fm n)) (gLL (Fm n)) ∧
      coherenceOf (grand (Fm n)) (gRL (Fm n)) < coherenceOf (grand (Fm n)) (gLL (Fm n)) ∧
      coherenceOf (grand (Fm n)) (gRR (Fm n)) < coherenceOf (grand (Fm n)) (gLL (Fm n)) := by
  obtain ⟨h1, h2, h3⟩ := order_RR n hn h
  exact ⟨by rw [mC2, mC1]; exact h3, by rw [mC3, mC1]; exact h2, by rw [mC4, mC1]; exact h1⟩

theorem order_mirror_tie (n : ℕ) (h : n % 21 = 3) :
    coherenceOf (grand (Fm n)) (gLR (Fm n)) < coherenceOf (grand (Fm n)) (gLL (Fm n)) ∧
      coherenceOf (grand (Fm n)) (gRL (Fm n)) < coherenceOf (grand (Fm n)) (gLL (Fm n)) ∧
      coherenceOf (grand (Fm n)) (gLL (Fm n)) = coherenceOf (grand (Fm n)) (gRR (Fm n)) := by
  obtain ⟨h2, h3, heq⟩ := order_tie n h
  exact ⟨by rw [mC2, mC1]; exact lt_of_lt_of_eq h3 heq,
    by rw [mC3, mC1]; exact lt_of_lt_of_eq h2 heq, by rw [mC1, mC4]; exact heq.symm⟩

/-- **Mirror of `step2_family_LL`: `g₄ = LⁿRRR` is the unique maximizer.** -/
theorem step2_mirror_RR (n : ℕ) (hn : 1 ≤ n)
    (h : n % 21 = 0 ∨ n % 21 = 2 ∨ n % 21 = 5 ∨ n % 21 = 7 ∨ n % 21 = 9 ∨ n % 21 = 10 ∨ n % 21 =
      12 ∨ n % 21 = 14 ∨ n % 21 = 16 ∨ n % 21 = 17 ∨ n % 21 = 19) :
    support (grand (Fm n)) = [gRR (Fm n)] := by
  obtain ⟨h1, h2, h3⟩ := order_mirror_RR n hn h
  exact support_RR_of _ h1 h2 h3

/-- **Mirror of `step2_family_RR`: `g₁ = LⁿRLL` is the unique maximizer.** -/
theorem step2_mirror_LL (n : ℕ) (hn : 1 ≤ n)
    (h : n % 21 = 1 ∨ n % 21 = 4 ∨ n % 21 = 6 ∨ n % 21 = 8 ∨ n % 21 = 11 ∨ n % 21 = 13 ∨ n % 21
      = 15 ∨ n % 21 = 18 ∨ n % 21 = 20) :
    support (grand (Fm n)) = [gLL (Fm n)] := by
  obtain ⟨h2, h3, h4⟩ := order_mirror_LL n hn h
  exact support_LL_of _ h2 h3 h4

/-- **Mirror of the tie: at `n ≡ 3 (mod 21)` the maximizer set of `LⁿR` is the
    cousin pair `{LⁿRLL, LⁿRRR}`.** -/
theorem step2_mirror_tie (n : ℕ) (h : n % 21 = 3) :
    support (grand (Fm n)) = [gLL (Fm n), gRR (Fm n)] := by
  obtain ⟨h2, h3, heq⟩ := order_mirror_tie n h
  exact support_tie_of _ h2 h3 heq

/-- `n = 0` mirrored, the frame of `R`: `{g₂, g₄}`. -/
theorem step2_mirror_zero :
    support (grand (Fm 0)) = [gLR (Fm 0), gRR (Fm 0)] := by
  decide

/-! ## The frames are the words `RⁿL` and `LⁿR` -/

open Frame in
theorem frame_eq {F G : Frame} (h1 : F.plus.p = G.plus.p) (h2 : F.plus.q = G.plus.q)
    (h3 : F.minus.p = G.minus.p) (h4 : F.minus.q = G.minus.q) : F = G := by
  obtain ⟨⟨a, b, _⟩, ⟨c, d, _⟩, _⟩ := F
  obtain ⟨⟨a', b', _⟩, ⟨c', d', _⟩, _⟩ := G
  change a = a' at h1
  change b = b' at h2
  change c = c' at h3
  change d = d' at h4
  subst h1 h2 h3 h4
  rfl

theorem walk_Rpow (n : ℕ) :
    (Frame.walk Frame.empty (List.replicate n true)).plus.p = 1 ∧
      (Frame.walk Frame.empty (List.replicate n true)).plus.q = 0 ∧
      (Frame.walk Frame.empty (List.replicate n true)).minus.p = n ∧
      (Frame.walk Frame.empty (List.replicate n true)).minus.q = 1 := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ k ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      rw [List.replicate_succ', Frame.walk_append]
      refine ⟨h1, h2, ?_, ?_⟩
      · show (Frame.walk Frame.empty (List.replicate k true)).plus.p
          + (Frame.walk Frame.empty (List.replicate k true)).minus.p = k + 1
        rw [h1, h3, Nat.add_comm]
      · show (Frame.walk Frame.empty (List.replicate k true)).plus.q
          + (Frame.walk Frame.empty (List.replicate k true)).minus.q = 1
        rw [h2, h4]

theorem walk_Lpow (n : ℕ) :
    (Frame.walk Frame.empty (List.replicate n false)).plus.p = 1 ∧
      (Frame.walk Frame.empty (List.replicate n false)).plus.q = n ∧
      (Frame.walk Frame.empty (List.replicate n false)).minus.p = 0 ∧
      (Frame.walk Frame.empty (List.replicate n false)).minus.q = 1 := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ k ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      rw [List.replicate_succ', Frame.walk_append]
      refine ⟨?_, ?_, h3, h4⟩
      · show (Frame.walk Frame.empty (List.replicate k false)).plus.p
          + (Frame.walk Frame.empty (List.replicate k false)).minus.p = 1
        rw [h1, h3]
      · show (Frame.walk Frame.empty (List.replicate k false)).plus.q
          + (Frame.walk Frame.empty (List.replicate k false)).minus.q = k + 1
        rw [h2, h4]

/-- **`Frn n` is the frame the tree walks to on `RⁿL`.** -/
theorem walk_RnL (n : ℕ) :
    Frame.walk Frame.empty (List.replicate n true ++ [false]) = Frn n := by
  obtain ⟨h1, h2, h3, h4⟩ := walk_Rpow n
  rw [Frame.walk_append]
  apply frame_eq
  · show (Frame.walk Frame.empty (List.replicate n true)).plus.p
      + (Frame.walk Frame.empty (List.replicate n true)).minus.p = n + 1
    rw [h1, h3, Nat.add_comm]
  · show (Frame.walk Frame.empty (List.replicate n true)).plus.q
      + (Frame.walk Frame.empty (List.replicate n true)).minus.q = 1
    rw [h2, h4]
  · exact h3
  · exact h4

/-- **`Fm n` is the frame the tree walks to on `LⁿR`.** -/
theorem walk_LnR (n : ℕ) :
    Frame.walk Frame.empty (List.replicate n false ++ [true]) = Fm n := by
  obtain ⟨h1, h2, h3, h4⟩ := walk_Lpow n
  rw [Frame.walk_append]
  apply frame_eq
  · exact h1
  · exact h2
  · show (Frame.walk Frame.empty (List.replicate n false)).plus.p
      + (Frame.walk Frame.empty (List.replicate n false)).minus.p = 1
    rw [h1, h3]
  · show (Frame.walk Frame.empty (List.replicate n false)).plus.q
      + (Frame.walk Frame.empty (List.replicate n false)).minus.q = n + 1
    rw [h2, h4]

/-! ## The bridge: one tick of `axiomSelect` at a sibling step

  In `Beat11Bridge`'s setting (observer `ε`, the active family is exactly the
  sibling pair `yL, yR` in that order), when the core `y`'s full word is `RⁿL`
  or `LⁿR` the selection is computed. -/

section bridge

open Mat2 Word Pres RatioSpace Advance Accumulation RootOrbit Beat Beat11Bridge

variable {archive : List Core} {active : List QuestionId} {c : Core}
  {sL sR : ℕ} {pL pR : Provenance} (s : ℕ) (p : Provenance)

theorem sibling_step_RnL_LL (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : c.seed.word ++ c.relWord = List.replicate n true ++ [false]) (hn : 1 ≤ n)
    (h : n % 21 = 0 ∨ n % 21 = 2 ∨ n % 21 = 5 ∨ n % 21 = 7 ∨ n % 21 = 9 ∨ n % 21 = 10 ∨ n % 21 =
      12 ∨ n % 21 = 14 ∨ n % 21 = 16 ∨ n % 21 = 17 ∨ n % 21 = 19) :
    axiomSelect 1 s p (proposals archive active) = [(gcore c false false sL pL s p).id] := by
  have hF : frameEps c = Frn n := by
    show Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
    rw [hw, walk_RnL]
  obtain ⟨h2, h3, h4⟩ := order_LL n hn h
  have top : selPred (Frn n) (gLL (Frn n)) = true := by
    refine selPred_true_of_max _ (fun z hz => ?_)
    rcases mem_grand hz with rfl | rfl | rfl | rfl
    · exact le_refl _
    · exact le_of_lt h2
    · exact le_of_lt h3
    · exact le_of_lt h4
  rw [sibling_axiomSelect s p hsib, hF, top, selPred_false_of_lt _ (gLL_mem _) h2,
    selPred_false_of_lt _ (gLL_mem _) h3, selPred_false_of_lt _ (gLL_mem _) h4]
  rfl

theorem sibling_step_RnL_RR (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : c.seed.word ++ c.relWord = List.replicate n true ++ [false]) (hn : 1 ≤ n)
    (h : n % 21 = 1 ∨ n % 21 = 4 ∨ n % 21 = 6 ∨ n % 21 = 8 ∨ n % 21 = 11 ∨ n % 21 = 13 ∨ n % 21
      = 15 ∨ n % 21 = 18 ∨ n % 21 = 20) :
    axiomSelect 1 s p (proposals archive active) = [(gcore c true true sR pR s p).id] := by
  have hF : frameEps c = Frn n := by
    show Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
    rw [hw, walk_RnL]
  obtain ⟨h1, h2, h3⟩ := order_RR n hn h
  have top : selPred (Frn n) (gRR (Frn n)) = true := by
    refine selPred_true_of_max _ (fun z hz => ?_)
    rcases mem_grand hz with rfl | rfl | rfl | rfl
    · exact le_of_lt h1
    · exact le_of_lt h2
    · exact le_of_lt h3
    · exact le_refl _
  rw [sibling_axiomSelect s p hsib, hF, top, selPred_false_of_lt _ (gRR_mem _) h1,
    selPred_false_of_lt _ (gRR_mem _) h2, selPred_false_of_lt _ (gRR_mem _) h3]
  rfl

theorem sibling_step_RnL_tie (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : c.seed.word ++ c.relWord = List.replicate n true ++ [false]) (h : n % 21 = 3) :
    axiomSelect 1 s p (proposals archive active) = [(gcore c false false sL pL s p).id, (gcore c
      true true sR pR s p).id] := by
  have hF : frameEps c = Frn n := by
    show Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
    rw [hw, walk_RnL]
  obtain ⟨h2, h3, heq⟩ := order_tie n h
  have top : ∀ y, coherenceOf (grand (Frn n)) y = coherenceOf (grand (Frn n)) (gLL (Frn n)) →
      selPred (Frn n) y = true := by
    intro y hy
    refine selPred_true_of_max _ (fun z hz => ?_)
    rw [hy]
    rcases mem_grand hz with rfl | rfl | rfl | rfl
    · exact le_refl _
    · exact le_of_lt h2
    · exact le_of_lt h3
    · exact le_of_eq heq.symm
  rw [sibling_axiomSelect s p hsib, hF, top _ rfl, top _ heq.symm,
    selPred_false_of_lt _ (gLL_mem _) h2, selPred_false_of_lt _ (gLL_mem _) h3]
  rfl

theorem sibling_step_LnR_RR (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : c.seed.word ++ c.relWord = List.replicate n false ++ [true]) (hn : 1 ≤ n)
    (h : n % 21 = 0 ∨ n % 21 = 2 ∨ n % 21 = 5 ∨ n % 21 = 7 ∨ n % 21 = 9 ∨ n % 21 = 10 ∨ n % 21 =
      12 ∨ n % 21 = 14 ∨ n % 21 = 16 ∨ n % 21 = 17 ∨ n % 21 = 19) :
    axiomSelect 1 s p (proposals archive active) = [(gcore c true true sR pR s p).id] := by
  have hF : frameEps c = Fm n := by
    show Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
    rw [hw, walk_LnR]
  obtain ⟨h1, h2, h3⟩ := order_mirror_RR n hn h
  have top : selPred (Fm n) (gRR (Fm n)) = true := by
    refine selPred_true_of_max _ (fun z hz => ?_)
    rcases mem_grand hz with rfl | rfl | rfl | rfl
    · exact le_of_lt h1
    · exact le_of_lt h2
    · exact le_of_lt h3
    · exact le_refl _
  rw [sibling_axiomSelect s p hsib, hF, top, selPred_false_of_lt _ (gRR_mem _) h1,
    selPred_false_of_lt _ (gRR_mem _) h2, selPred_false_of_lt _ (gRR_mem _) h3]
  rfl

theorem sibling_step_LnR_LL (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : c.seed.word ++ c.relWord = List.replicate n false ++ [true]) (hn : 1 ≤ n)
    (h : n % 21 = 1 ∨ n % 21 = 4 ∨ n % 21 = 6 ∨ n % 21 = 8 ∨ n % 21 = 11 ∨ n % 21 = 13 ∨ n % 21
      = 15 ∨ n % 21 = 18 ∨ n % 21 = 20) :
    axiomSelect 1 s p (proposals archive active) = [(gcore c false false sL pL s p).id] := by
  have hF : frameEps c = Fm n := by
    show Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
    rw [hw, walk_LnR]
  obtain ⟨h2, h3, h4⟩ := order_mirror_LL n hn h
  have top : selPred (Fm n) (gLL (Fm n)) = true := by
    refine selPred_true_of_max _ (fun z hz => ?_)
    rcases mem_grand hz with rfl | rfl | rfl | rfl
    · exact le_refl _
    · exact le_of_lt h2
    · exact le_of_lt h3
    · exact le_of_lt h4
  rw [sibling_axiomSelect s p hsib, hF, top, selPred_false_of_lt _ (gLL_mem _) h2,
    selPred_false_of_lt _ (gLL_mem _) h3, selPred_false_of_lt _ (gLL_mem _) h4]
  rfl

theorem sibling_step_LnR_tie (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : c.seed.word ++ c.relWord = List.replicate n false ++ [true]) (h : n % 21 = 3) :
    axiomSelect 1 s p (proposals archive active) = [(gcore c false false sL pL s p).id, (gcore c
      true true sR pR s p).id] := by
  have hF : frameEps c = Fm n := by
    show Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
    rw [hw, walk_LnR]
  obtain ⟨h2, h3, heq⟩ := order_mirror_tie n h
  have top : ∀ y, coherenceOf (grand (Fm n)) y = coherenceOf (grand (Fm n)) (gLL (Fm n)) →
      selPred (Fm n) y = true := by
    intro y hy
    refine selPred_true_of_max _ (fun z hz => ?_)
    rw [hy]
    rcases mem_grand hz with rfl | rfl | rfl | rfl
    · exact le_refl _
    · exact le_of_lt h2
    · exact le_of_lt h3
    · exact le_of_eq heq.symm
  rw [sibling_axiomSelect s p hsib, hF, top _ rfl, top _ heq.symm,
    selPred_false_of_lt _ (gLL_mem _) h2, selPred_false_of_lt _ (gLL_mem _) h3]
  rfl

end bridge

/-! ## The bridge on the tick carrier `advanceCarrier` returns

  The `advanceCarrier` restatement of each `sibling_step_*` theorem above, in
  `RootChainCarrier`/`Beat11Bridge`'s own style: a lawful carrier sitting at
  observer `ε` whose active family is the sibling pair `[childCore c false sL
  pL, childCore c true sR pR]`, one tick under `axiomSelect`. -/

section carrier

open Mat2 Word Pres RatioSpace Advance Accumulation RootOrbit Beat Beat11Bridge

variable {Aux : Type} {h : ℕ}

/-- **Step 2 on the tick carrier, `RⁿL` at the maximizing corner `g₁`.** -/
theorem advanceCarrier_active_RnL_LL (X : TickCarrier Aux h) (hlaw : Lawful X)
    (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux)) (hsel : _) (hfresh : _)
    {c : Core} {sL sR : ℕ} {pL pR : Provenance} (hMO : X.observer.matrix = 1)
    (hsib : X.archive.filter (fun d => d.id ∈ X.active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : c.seed.word ++ c.relWord = List.replicate n true ++ [false]) (hn : 1 ≤ n)
    (hres : n % 21 = 0 ∨ n % 21 = 2 ∨ n % 21 = 5 ∨ n % 21 = 7 ∨ n % 21 = 9 ∨ n % 21 = 10 ∨
      n % 21 = 12 ∨ n % 21 = 14 ∨ n % 21 = 16 ∨ n % 21 = 17 ∨ n % 21 = 19) :
    (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active
      = [(gcore c false false sL pL s p).id] := by
  show axiomSelect X.observer.matrix s p (proposals X.archive X.active) = _
  rw [hMO]
  exact sibling_step_RnL_LL s p hsib n hw hn hres

/-- **Step 2 on the tick carrier, `RⁿL` at the maximizing corner `g₄`.** -/
theorem advanceCarrier_active_RnL_RR (X : TickCarrier Aux h) (hlaw : Lawful X)
    (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux)) (hsel : _) (hfresh : _)
    {c : Core} {sL sR : ℕ} {pL pR : Provenance} (hMO : X.observer.matrix = 1)
    (hsib : X.archive.filter (fun d => d.id ∈ X.active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : c.seed.word ++ c.relWord = List.replicate n true ++ [false]) (hn : 1 ≤ n)
    (hres : n % 21 = 1 ∨ n % 21 = 4 ∨ n % 21 = 6 ∨ n % 21 = 8 ∨ n % 21 = 11 ∨
      n % 21 = 13 ∨ n % 21 = 15 ∨ n % 21 = 18 ∨ n % 21 = 20) :
    (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active
      = [(gcore c true true sR pR s p).id] := by
  show axiomSelect X.observer.matrix s p (proposals X.archive X.active) = _
  rw [hMO]
  exact sibling_step_RnL_RR s p hsib n hw hn hres

/-- **Step 2 on the tick carrier, `RⁿL` at the cousin tie, `n ≡ 3 (mod 21)`.** -/
theorem advanceCarrier_active_RnL_tie (X : TickCarrier Aux h) (hlaw : Lawful X)
    (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux)) (hsel : _) (hfresh : _)
    {c : Core} {sL sR : ℕ} {pL pR : Provenance} (hMO : X.observer.matrix = 1)
    (hsib : X.archive.filter (fun d => d.id ∈ X.active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : c.seed.word ++ c.relWord = List.replicate n true ++ [false])
    (hres : n % 21 = 3) :
    (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active
      = [(gcore c false false sL pL s p).id, (gcore c true true sR pR s p).id] := by
  show axiomSelect X.observer.matrix s p (proposals X.archive X.active) = _
  rw [hMO]
  exact sibling_step_RnL_tie s p hsib n hw hres

/-- **Step 2 on the tick carrier, `LⁿR`, the mirror of `advanceCarrier_active_RnL_RR`.** -/
theorem advanceCarrier_active_LnR_RR (X : TickCarrier Aux h) (hlaw : Lawful X)
    (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux)) (hsel : _) (hfresh : _)
    {c : Core} {sL sR : ℕ} {pL pR : Provenance} (hMO : X.observer.matrix = 1)
    (hsib : X.archive.filter (fun d => d.id ∈ X.active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : c.seed.word ++ c.relWord = List.replicate n false ++ [true]) (hn : 1 ≤ n)
    (hres : n % 21 = 0 ∨ n % 21 = 2 ∨ n % 21 = 5 ∨ n % 21 = 7 ∨ n % 21 = 9 ∨ n % 21 = 10 ∨
      n % 21 = 12 ∨ n % 21 = 14 ∨ n % 21 = 16 ∨ n % 21 = 17 ∨ n % 21 = 19) :
    (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active
      = [(gcore c true true sR pR s p).id] := by
  show axiomSelect X.observer.matrix s p (proposals X.archive X.active) = _
  rw [hMO]
  exact sibling_step_LnR_RR s p hsib n hw hn hres

/-- **Step 2 on the tick carrier, `LⁿR`, the mirror of `advanceCarrier_active_RnL_LL`.** -/
theorem advanceCarrier_active_LnR_LL (X : TickCarrier Aux h) (hlaw : Lawful X)
    (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux)) (hsel : _) (hfresh : _)
    {c : Core} {sL sR : ℕ} {pL pR : Provenance} (hMO : X.observer.matrix = 1)
    (hsib : X.archive.filter (fun d => d.id ∈ X.active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : c.seed.word ++ c.relWord = List.replicate n false ++ [true]) (hn : 1 ≤ n)
    (hres : n % 21 = 1 ∨ n % 21 = 4 ∨ n % 21 = 6 ∨ n % 21 = 8 ∨ n % 21 = 11 ∨
      n % 21 = 13 ∨ n % 21 = 15 ∨ n % 21 = 18 ∨ n % 21 = 20) :
    (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active
      = [(gcore c false false sL pL s p).id] := by
  show axiomSelect X.observer.matrix s p (proposals X.archive X.active) = _
  rw [hMO]
  exact sibling_step_LnR_LL s p hsib n hw hn hres

/-- **Step 2 on the tick carrier, `LⁿR`, the mirror of `advanceCarrier_active_RnL_tie`.** -/
theorem advanceCarrier_active_LnR_tie (X : TickCarrier Aux h) (hlaw : Lawful X)
    (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux)) (hsel : _) (hfresh : _)
    {c : Core} {sL sR : ℕ} {pL pR : Provenance} (hMO : X.observer.matrix = 1)
    (hsib : X.archive.filter (fun d => d.id ∈ X.active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : c.seed.word ++ c.relWord = List.replicate n false ++ [true])
    (hres : n % 21 = 3) :
    (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active
      = [(gcore c false false sL pL s p).id, (gcore c true true sR pR s p).id] := by
  show axiomSelect X.observer.matrix s p (proposals X.archive X.active) = _
  rw [hMO]
  exact sibling_step_LnR_tie s p hsib n hw hres

end carrier

/-! ## Proposition 16.15, item 4: the certificate for the tie family

`σ = (yLL yRR)(yLR yRL)` on the four grandchildren of `y = RⁿL` is the reversal
of `grand`. The book says it is an automorphism *exactly because* the tie is
`t₁₂ = t₃₄`, `t₁₃ = t₂₄`, and checks the first sixty members; here it is every
member. -/

section certificate

/-- **The two equalities the tie is**, at every `n ≡ 3 (mod 21)`. -/
theorem tie_equalities (n : ℕ) (h : n % 21 = 3) :
    tEnd (gLL (Frn n)) (gLR (Frn n)) = tEnd (gRL (Frn n)) (gRR (Frn n)) ∧
      tEnd (gLL (Frn n)) (gRL (Frn n)) = tEnd (gLR (Frn n)) (gRR (Frn n)) := by
  refine ⟨?_, ?_⟩
  · rw [t12_mod3_0 n (by omega), t34_mod3_0 n (by omega)]
    omega
  · rw [t13_mod7_3 n (by omega), t24_mod7_3 n (by omega)]
    omega

/-- **Proposition 16.15(4), for every member of the family.** Relabelling the
    grandchildren of `RⁿL`, `n ≡ 3 (mod 21)`, by `σ = (yLL yRR)(yLR yRL)`
    reproduces the whole tension matrix. -/
theorem cert_RnL (n : ℕ) (h : n % 21 = 3) :
    (grand (Frn n)).reverse.map (tensions (grand (Frn n)).reverse)
      = (grand (Frn n)).map (tensions (grand (Frn n))) := by
  obtain ⟨e1, e2⟩ := tie_equalities n h
  show [[tEnd (gRR (Frn n)) (gRR (Frn n)), tEnd (gRR (Frn n)) (gRL (Frn n)),
          tEnd (gRR (Frn n)) (gLR (Frn n)), tEnd (gRR (Frn n)) (gLL (Frn n))],
        [tEnd (gRL (Frn n)) (gRR (Frn n)), tEnd (gRL (Frn n)) (gRL (Frn n)),
          tEnd (gRL (Frn n)) (gLR (Frn n)), tEnd (gRL (Frn n)) (gLL (Frn n))],
        [tEnd (gLR (Frn n)) (gRR (Frn n)), tEnd (gLR (Frn n)) (gRL (Frn n)),
          tEnd (gLR (Frn n)) (gLR (Frn n)), tEnd (gLR (Frn n)) (gLL (Frn n))],
        [tEnd (gLL (Frn n)) (gRR (Frn n)), tEnd (gLL (Frn n)) (gRL (Frn n)),
          tEnd (gLL (Frn n)) (gLR (Frn n)), tEnd (gLL (Frn n)) (gLL (Frn n))]] =
      [[tEnd (gLL (Frn n)) (gLL (Frn n)), tEnd (gLL (Frn n)) (gLR (Frn n)),
          tEnd (gLL (Frn n)) (gRL (Frn n)), tEnd (gLL (Frn n)) (gRR (Frn n))],
        [tEnd (gLR (Frn n)) (gLL (Frn n)), tEnd (gLR (Frn n)) (gLR (Frn n)),
          tEnd (gLR (Frn n)) (gRL (Frn n)), tEnd (gLR (Frn n)) (gRR (Frn n))],
        [tEnd (gRL (Frn n)) (gLL (Frn n)), tEnd (gRL (Frn n)) (gLR (Frn n)),
          tEnd (gRL (Frn n)) (gRL (Frn n)), tEnd (gRL (Frn n)) (gRR (Frn n))],
        [tEnd (gRR (Frn n)) (gLL (Frn n)), tEnd (gRR (Frn n)) (gLR (Frn n)),
          tEnd (gRR (Frn n)) (gRL (Frn n)), tEnd (gRR (Frn n)) (gRR (Frn n))]]
  rw [tEnd_comm (gRR (Frn n)) (gRL (Frn n)), tEnd_comm (gRR (Frn n)) (gLR (Frn n)),
    tEnd_comm (gRR (Frn n)) (gLL (Frn n)), tEnd_comm (gRL (Frn n)) (gLR (Frn n)),
    tEnd_comm (gRL (Frn n)) (gLL (Frn n)), tEnd_comm (gLR (Frn n)) (gLL (Frn n)), e1, e2,
    tEnd_self, tEnd_self, tEnd_self, tEnd_self]

/-- The certificate is an involution that fixes the tie: `σ` exchanges the two
    retained occurrences, and they carry equal coherence values. -/
theorem cert_RnL_tie (n : ℕ) (h : n % 21 = 3) :
    (grand (Frn n)).reverse.reverse = grand (Frn n) ∧
      support (grand (Frn n)) = [gLL (Frn n), gRR (Frn n)] ∧
      coherenceOf (grand (Frn n)) (gLL (Frn n)) = coherenceOf (grand (Frn n)) (gRR (Frn n)) :=
  ⟨List.reverse_reverse _, step2_family_tie n h, (order_tie n h).2.2⟩

end certificate

end Step2Family
end Two
end RatioSpace
