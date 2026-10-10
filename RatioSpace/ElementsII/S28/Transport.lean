/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S03.Braid
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
/-!
  Elements II §28 (partial) — the Dedekind-Rademacher transport coordinate.

  This file exists to close divergence D-01 (`research/lean-support/DIVERGENCE.md`),
  not to build §28 in full. §28 is far ahead of this tree's own front (currently
  §15), and its surrounding apparatus (`siblingRelation`, `winding`, Chamber's
  `A_R`/`A_L`) is not yet in place here. What D-01 named as owed is narrower:
  Def 28.2's Rademacher function, in exact-integer form, and Prop 28.3.

  **The book's claim, Def 28.2:** for `c ≠ 0`,
  `Φ_Rad(Q) = (a+d)/c - 12·sgn(c)·s_D(a,|c|)`, with `s_D` the classical Dedekind
  sum; for `c = 0`, `Φ_Rad(Q) = b/d`. The book states the value is an integer.

  **What a naive Lean transcription gets wrong.** `(a+d)/c` under `Int` division
  and dropping the Dedekind term agrees with the book on 320 of 564 SL(2,Z)
  witnesses structurally (the correction is genuinely zero) and 54 more by
  accident (the floor absorbs a proper fraction), and disagrees on the other
  190 — every disagreement traced to the missing term, none to the division.
  `research/experiments/rademacher_divergence_locus.py` and
  `dedekind_negation_sign.py` carry the exact counts.

  **The integer-only replacement**, with `k = |c|`, `S` the doubled Dedekind sum
  cleared of denominators:

      S(a,k)      = Σ_{r=1}^{k-1} (2r-k)·(2·(a·r mod k)-k)
      Φ_Rad(Q)    = sgn(c)·(k·(a+d) - 3·S(a,k)) / k²

  verified equal to the book's formula on all 564 witnesses, `k² ∣ (k(a+d) - 3S)`
  in every case — that divisibility is the book's integrality claim, in exact
  integer form.

  **The sign correction this file's proof depends on.** `S` is *antisymmetric*
  in `a`: `S(-a,k) = -S(a,k)`. An earlier reading of this fact (in Legion's tree,
  corrected there 2026-08-29) claimed the opposite — symmetric, "verified over
  564 matrices" — which was never actually checked and is false: over
  `1 ≤ k < 60, |a| ≤ 40` the symmetric reading holds in zero non-vacuous cases,
  antisymmetric in 4014. Prop 28.3 (`Φ_Rad(-Q) = Φ_Rad(Q)`) is true, and only
  because two of the three sign flips under negation land in the numerator and
  cancel — it needs the antisymmetric reading, not the symmetric one.

  Dependencies: `RatioSpace.Braid` for `Mat2` only. No other Elements II
  machinery, and no import of Legion's `Two/Transport.lean` — this is an
  independent formalisation of the same divergence repair, reusing the already
  worked-out arithmetic (DIVERGENCE.md) and Legion's proof route as a reference,
  checked fresh by this tree's own kernel.
-/

namespace RatioSpace
namespace Two

open RatioSpace Mat2

/-! ## Definition 28.2 — the Dedekind-Rademacher transport coordinate -/

/-- A finite integer sum `f 0 + f 1 + ... + f (n-1)`, by recursion on `n`: exact, computable,
    and free of `Finset` (whose `range` carries `Classical.choice` in this Mathlib). -/
def isum (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => isum f n + f n

@[simp] theorem isum_zero (f : ℕ → ℤ) : isum f 0 = 0 := rfl
@[simp] theorem isum_succ (f : ℕ → ℤ) (n : ℕ) : isum f (n + 1) = isum f n + f n := rfl

/-- Peeling the first term instead of the last. -/
theorem isum_succ_left (f : ℕ → ℤ) (n : ℕ) :
    isum f (n + 1) = f 0 + isum (fun i => f (i + 1)) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [isum_succ, ih, isum_succ]; ring

theorem isum_congr {f g : ℕ → ℤ} (n : ℕ) (h : ∀ i < n, f i = g i) : isum f n = isum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [isum_succ, isum_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem isum_neg (f : ℕ → ℤ) (n : ℕ) : isum (fun i => -f i) n = - isum f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [isum_succ, isum_succ, ih]; ring

/-- **Reflection.** Summing `f` over `0..n-1` is summing `f (n-1-i)` over the same range. -/
theorem isum_reflect (f : ℕ → ℤ) (n : ℕ) : isum f n = isum (fun i => f (n - 1 - i)) n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [isum_succ_left, isum_succ]
    have h1 : isum (fun i => f (i + 1)) n = isum (fun i => f (n + 1 - 1 - i)) n := by
      rw [ih (fun i => f (i + 1))]
      exact isum_congr n (fun i hi => by congr 1; omega)
    rw [h1]
    have h2 : f 0 = f (n + 1 - 1 - n) := by congr 1; omega
    rw [h2]; ring

/-- The integer Dedekind sum, `12·k²·s_D(a,k)` cleared of denominators: exact
    integer arithmetic, no division, no rationals, no `Finset`. -/
def dedekindSumInt (a : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 0
  else isum (fun i =>
    let r : ℤ := (i : ℤ) + 1
    (2 * r - k) * (2 * ((a * r) % (k : ℤ)) - k)) (k - 1)

/-- **Definition 28.2**, integer-only form. For `c ≠ 0`,
    `Φ_Rad(Q) = sgn(c)·(k·(a+d) - 3·S(a,k)) / k²`, `k = |c|`; the division is
    exact, `k² ∣ (k(a+d) - 3S)`, which is the book's integrality claim. For
    `c = 0`, `Φ_Rad(Q) = b/d`, exact for `det = 1` since that forces `d = ±1`. -/
def phiRad (Q : Mat2) : ℤ :=
  if Q.c = 0 then
    if Q.d ≠ 0 then Q.b / Q.d else 0
  else
    let k := Q.c.natAbs
    let sgnC : ℤ := if Q.c > 0 then 1 else -1
    let s := dedekindSumInt Q.a k
    sgnC * ((k : ℤ) * (Q.a + Q.d) - 3 * s) / ((k : ℤ) * k)

/-- The route correction sign, `sgn(c · tr(Q))`, the third term of the
    decomposition §28 states elsewhere; recorded here since it costs nothing
    once `phiRad` exists. -/
def routeCorrection (Q : Mat2) : ℤ :=
  let c := Q.c
  let tr := Q.a + Q.d
  if c * tr > 0 then 1
  else if c * tr < 0 then -1
  else 0

/-- The homogeneous Rademacher symbol. -/
def psiRad (Q : Mat2) : ℤ := phiRad Q - 3 * routeCorrection Q

/-! ## Proposition 28.3 — central lift invariance -/

/-- The integer Dedekind sum is **anti**symmetric in its first argument. The
    pairing `r ↔ k-r` on `Finset.range (k-1)` sends `2r-k ↦ -(2r-k)` and fixes
    `(a·r) mod k` (since `(-a)(k-r) ≡ a·r mod k`), so it negates each term
    rather than preserving it. Verified over `1 ≤ k < 60, |a| ≤ 40`:
    `dedekind_negation_sign.py`. -/
theorem dedekindSumInt_neg (a : ℤ) (k : ℕ) :
    dedekindSumInt (-a) k = - dedekindSumInt a k := by
  unfold dedekindSumInt
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, if_false]
    rw [← isum_neg, isum_reflect]
    refine isum_congr (k - 1) ?_
    intro i hik
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hcast : ((k - 1 - 1 - i : ℕ) : ℤ) + 1 = (k : ℤ) - ((i : ℤ) + 1) := by
      have : i + 2 ≤ k := by omega
      omega
    change (2 * (((k - 1 - 1 - i : ℕ) : ℤ) + 1) - k) *
        (2 * ((-a * (((k - 1 - 1 - i : ℕ) : ℤ) + 1)) % (k : ℤ)) - k)
      = -((2 * ((i : ℤ) + 1) - k) * (2 * ((a * ((i : ℤ) + 1)) % (k : ℤ)) - k))
    rw [hcast]
    have hmod : (-a * ((k : ℤ) - ((i : ℤ) + 1))) % (k : ℤ)
        = (a * ((i : ℤ) + 1)) % (k : ℤ) := by
      have hre : -a * ((k : ℤ) - ((i : ℤ) + 1)) = a * ((i : ℤ) + 1) + (-a) * (k : ℤ) := by
        ring
      rw [hre, Int.add_mul_emod_self_right]
    rw [hmod]
    ring

@[simp] theorem negMat2_a (Q : Mat2) : (-Q).a = -Q.a := rfl
@[simp] theorem negMat2_b (Q : Mat2) : (-Q).b = -Q.b := rfl
@[simp] theorem negMat2_c (Q : Mat2) : (-Q).c = -Q.c := rfl
@[simp] theorem negMat2_d (Q : Mat2) : (-Q).d = -Q.d := rfl

/-- **Proposition 28.3.** `Φ_Rad(-Q) = Φ_Rad(Q)`, on the book's own domain
    (`det Q = 1`). Negating `Q` flips `sgn(c)`, flips `a+d`, and *negates* `S`
    by `dedekindSumInt_neg`; two of the three sign changes sit in the numerator
    and cancel.

    **The determinant hypothesis is load-bearing, not bookkeeping.** Without it
    the `c = 0` branch's `Int` division breaks the identity, witnessed exactly
    below: `phiRad`'s `c = 0` case is only exact when `d ∣ b`, and `det = 1`
    with `c = 0` forces `a·d = 1`, hence `d = ±1`, hence exactness. -/
theorem phiRad_neg_invariant (Q : Mat2) (hdet : Q.det = 1) :
    phiRad (-Q) = phiRad Q := by
  unfold phiRad
  by_cases hc : Q.c = 0
  · have had : Q.a * Q.d = 1 := by
      have : Q.det = Q.a * Q.d - Q.b * Q.c := rfl
      rw [hc, mul_zero, sub_zero] at this
      omega
    -- 2026-09-22: `|d| = 1` from `|d|·|a| = 1` in `ℕ`, then `d = ±1` by `Int.natAbs_eq`; the
    -- Mathlib lemma `Int.eq_one_or_neg_one_of_mul_eq_one` reaches `Classical.choice`.
    have hab : Q.d.natAbs * Q.a.natAbs = 1 := by
      rw [← Int.natAbs_mul, mul_comm, had]; rfl
    have hd1 : Q.d.natAbs = 1 := Nat.eq_one_of_mul_eq_one_right hab
    have h1 : (1 : ℤ) ≠ 0 := by decide
    have h1' : (-1 : ℤ) ≠ 0 := by decide
    -- `simp only` with the two literal facts supplied: the generic `one_ne_zero` instance on `ℤ`
    -- (`Int.instNeZeroOfNatOfNat`) reaches `Classical.choice`.
    rcases Int.natAbs_eq Q.d with hd | hd <;> rw [hd1] at hd <;>
      simp only [negMat2_c, negMat2_d, negMat2_b, hc, hd, Nat.cast_one, neg_zero, ↓reduceIte,
        Int.reduceNeg, ne_eq, h1, h1', not_false_eq_true, Int.ediv_neg, Int.ediv_one, neg_neg]
  · have hk : (-Q.c).natAbs = Q.c.natAbs := by simp
    have hs : dedekindSumInt (-Q.a) (Q.c.natAbs) = - dedekindSumInt Q.a (Q.c.natAbs) :=
      dedekindSumInt_neg Q.a _
    simp only [negMat2_a, negMat2_b, negMat2_c, negMat2_d, neg_eq_zero, hc, if_false, hk, hs]
    rcases lt_trichotomy Q.c 0 with h | h | h
    · simp only [if_pos (show -Q.c > 0 by omega), if_neg (show ¬ Q.c > 0 by omega)]; ring_nf
    · exact absurd h hc
    · simp only [if_neg (show ¬ -Q.c > 0 by omega), if_pos (show Q.c > 0 by omega)]; ring_nf

/-- The hypothesis is necessary, not defensive: an exact counterexample off the
    book's own domain (`det = 2 ≠ 1`), witnessed by `decide` rather than argued. -/
theorem phiRad_neg_invariant_needs_det :
    phiRad (-(⟨0, 1, 0, 2⟩ : Mat2)) ≠ phiRad (⟨0, 1, 0, 2⟩ : Mat2) := by decide

/-! ## Boundary Statement — the decomposition is definitional -/

/-- The class coordinate's three-term decomposition is `rfl`: nothing beyond
    unfolding `psiRad`'s own definition is needed for it. -/
theorem psiRad_decomposition (Q : Mat2) :
    psiRad Q = phiRad Q - 3 * routeCorrection Q := rfl

end Two
end RatioSpace
