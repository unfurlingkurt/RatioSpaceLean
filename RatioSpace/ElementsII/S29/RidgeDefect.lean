/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S27.Chamber
import RatioSpace.ElementsII.S10.Causal
import RatioSpace.ElementsII.S28.Transport
/-!
  Elements II §29 — Exact golden-ridge defects.

  Eight items. §27 (`Chamber.lean`) builds the right form
  `N p q = p² − pq − q²`, its sign flip under `advR`, its non-vanishing on a
  nonzero tail, and the bridge `0 < p − qφ ⇔ 0 < N`. This file does not copy any
  of that: `DR` *is* `N`, and the side readings are §27's bridges read at the
  book's §29 names. What is new here is the left form `D_L`, the general mirror
  sign laws over all integer columns and all powers, the Fibonacci weave, the
  `(RL)^r` strobe with its retained `R`-emission relation, and the gathering.

  Substrate discipline. The book writes `D_R(p,q)/q² = (x − φ)(x + φ⁻¹)` with
  `x = p/q`. Nothing is divided here: the statement carried is the `ℤ[φ]`
  factorisation `D_R(p,q) = (p − qφ)(p + qφ⁻¹)`, whose `q²`-scaled shadow is the
  book's line. "Growing" in Prop 29.6 is carried as strict increase plus the
  explicit lower bound `r + 1 ≤ tr`, not as a limit.
-/

namespace RatioSpace
namespace Two
namespace RidgeDefect

open Mat2 Word Zphi
open Chamber (N Nc bridge bridge_neg N_ne_zero)

/-! ## Definition 29.1 — Right and left quadratic ridge defects -/

/-- **Definition 29.1.** The right ridge defect `D_R(p,q) = p² − pq − q²`.
    It is §27's conserved form `N`, named at its §29 reading, not a second copy. -/
def DR (p q : ℤ) : ℤ := N p q

/-- **Definition 29.1.** The left ridge defect `D_L(p,q) = p² + pq − q²`. -/
def DL (p q : ℤ) : ℤ := p * p + p * q - q * q

theorem def_29_1 (p q : ℤ) :
    DR p q = p * p - p * q - q * q ∧ DL p q = p * p + p * q - q * q := ⟨rfl, rfl⟩

/-- `D_L` is `D_R` read after the parity exchange, with a sign. -/
theorem DL_eq_neg_DR_swap (p q : ℤ) : DL p q = - DR q p := by
  unfold DL DR N; ring

/-- `D_L(p,q) = D_R(p + q, q)`: the left form is the right form one column over.
    This is what lets §27's right bridge read the left ridge. -/
theorem DL_eq_DR_shift (p q : ℤ) : DL p q = DR (p + q) q := by
  unfold DL DR N; ring

/-- The two forms read on `ℤ[φ]` columns, for the naming clause. -/
def DRz (x y : Zphi) : Zphi := x * x - x * y - y * y

def DLz (x y : Zphi) : Zphi := x * x + x * y - y * y

/-- On rational columns the `ℤ[φ]` forms are the integer defects. -/
theorem DRz_int (p q : ℤ) : DRz ⟨p, 0⟩ ⟨q, 0⟩ = ⟨DR p q, 0⟩ := by
  apply Zphi.ext
  · change p * p + 0 * 0 - (p * q + 0 * 0) - (q * q + 0 * 0) = p * p - p * q - q * q
    ring
  · change p * 0 + 0 * p + 0 * 0 - (p * 0 + 0 * q + 0 * 0) - (q * 0 + 0 * q + 0 * 0) = 0
    ring

theorem DLz_int (p q : ℤ) : DLz ⟨p, 0⟩ ⟨q, 0⟩ = ⟨DL p q, 0⟩ := by
  apply Zphi.ext
  · change p * p + 0 * 0 + (p * q + 0 * 0) - (q * q + 0 * 0) = p * p + p * q - q * q
    ring
  · change p * 0 + 0 * p + 0 * 0 + (p * 0 + 0 * q + 0 * 0) - (q * 0 + 0 * q + 0 * 0) = 0
    ring

/-- **Definition 29.1, why "ridge".** The zeros of the two forms on the positive
    projective line `x : 1` of `ℤ[φ]` are exactly the golden ridges of
    Theorem 27.3: `D_R(x,1) = 0 ⇔ x = φ` and `D_L(x,1) = 0 ⇔ x = φ⁻¹`, for `x > 0`. -/
theorem ridge_zeros (x : Zphi) (hx : 0 < x) :
    (DRz x 1 = 0 ↔ x = phi) ∧ (DLz x 1 = 0 ↔ x = phiInv) := by
  refine ⟨⟨fun h => ?_, fun h => by rw [h]; decide⟩, ⟨fun h => ?_, fun h => by rw [h]; decide⟩⟩
  · have e : x * x = (x * x - x * 1 - 1 * 1) + (x + 1) := by ring
    exact Chamber.ridgeR_unique x hx (by rw [e]; unfold DRz at h; rw [h, zero_add])
  · have e : x * x + x = (x * x + x * 1 - 1 * 1) + 1 := by ring
    exact Chamber.ridgeL_unique x hx (by rw [e]; unfold DLz at h; rw [h, zero_add])

/-- `D_R(x,y) = (x − φy)(x + φ⁻¹y)` on `ℤ[φ]` columns. -/
theorem DRz_factor (x y : Zphi) : DRz x y = (x - phi * y) * (x + phiInv * y) := by
  unfold DRz; rw [phiInv_eq_phi_sub_one]
  calc x * x - x * y - y * y = x * x - x * y - (phi * phi - phi) * (y * y) := by
        rw [phi_sq]; ring
    _ = (x - phi * y) * (x + (phi - 1) * y) := by ring

/-- `D_L(x,y) = (x − φ⁻¹y)(x + φy)` on `ℤ[φ]` columns. -/
theorem DLz_factor (x y : Zphi) : DLz x y = (x - phiInv * y) * (x + phi * y) := by
  unfold DLz; rw [phiInv_eq_phi_sub_one]
  calc x * x + x * y - y * y = x * x + x * y - (phi * phi - phi) * (y * y) := by
        rw [phi_sq]; ring
    _ = (x - (phi - 1) * y) * (x + phi * y) := by ring

/-- **Definition 29.1, why "ridge", on the projective line.** For a positive
    column `(x, y)` of `ℤ[φ]`, `D_R(x,y) = 0 ⇔ x = φy` and `D_L(x,y) = 0 ⇔ x = φ⁻¹y`.
    `ridge_zeros` is the chart `y = 1`. -/
theorem ridge_zeros_proj (x y : Zphi) (hx : 0 < x) (hy : 0 < y) :
    (DRz x y = 0 ↔ x = phi * y) ∧ (DLz x y = 0 ↔ x = phiInv * y) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [DRz_factor] at h
    rcases mul_eq_zero_split h with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 (ne_of_gt (add_pos hx (mul_pos phiInv_pos hy)))
  · rw [DRz_factor, h, sub_self, zero_mul]
  · rw [DLz_factor] at h
    rcases mul_eq_zero_split h with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 (ne_of_gt (add_pos hx (mul_pos (by decide : (0 : Zphi) < phi) hy)))
  · rw [DLz_factor, h, sub_self, zero_mul]

/-! ## Proposition 29.2 — Exact side reading of the defects -/

/-- The right displacement `p − qφ` is the `ℤ[φ]` element `⟨p, −q⟩`. -/
theorem dispR_eq (p q : ℤ) : (⟨p, 0⟩ : Zphi) - ⟨q, 0⟩ * phi = ⟨p, -q⟩ := by
  apply Zphi.ext
  · change p - (q * 0 + 0 * 1) = p; ring
  · change 0 - (q * 1 + 0 * 0 + 0 * 1) = -q; ring

/-- The left displacement `p − qφ⁻¹` is the `ℤ[φ]` element `⟨p + q, −q⟩`
    (§27's `defectL`). -/
theorem dispL_eq (p q : ℤ) : (⟨p, 0⟩ : Zphi) - ⟨q, 0⟩ * phiInv = ⟨p + q, -q⟩ := by
  apply Zphi.ext
  · change p - (q * -1 + 0 * 1) = p + q; ring
  · change 0 - (q * 1 + 0 * -1 + 0 * 1) = -q; ring

/-- **Proposition 29.2, the factorisations**, with the `q²` cleared rather than
    divided: `D_R(p,q) = (p − qφ)(p + qφ⁻¹)` and `D_L(p,q) = (p − qφ⁻¹)(p + qφ)` in
    `ℤ[φ]`, for every integer column. -/
theorem prop_29_2_factor (p q : ℤ) :
    (⟨DR p q, 0⟩ : Zphi) = ((⟨p, 0⟩ : Zphi) - ⟨q, 0⟩ * phi) * (⟨p, 0⟩ + ⟨q, 0⟩ * phiInv) ∧
    (⟨DL p q, 0⟩ : Zphi) = ((⟨p, 0⟩ : Zphi) - ⟨q, 0⟩ * phiInv) * (⟨p, 0⟩ + ⟨q, 0⟩ * phi) := by
  refine ⟨Zphi.ext ?_ ?_, Zphi.ext ?_ ?_⟩
  · change p * p - p * q - q * q =
      (p - (q * 0 + 0 * 1)) * (p + (q * -1 + 0 * 1)) +
      (0 - (q * 1 + 0 * 0 + 0 * 1)) * (0 + (q * 1 + 0 * -1 + 0 * 1))
    ring
  · change (0 : ℤ) =
      (p - (q * 0 + 0 * 1)) * (0 + (q * 1 + 0 * -1 + 0 * 1)) +
      (0 - (q * 1 + 0 * 0 + 0 * 1)) * (p + (q * -1 + 0 * 1)) +
      (0 - (q * 1 + 0 * 0 + 0 * 1)) * (0 + (q * 1 + 0 * -1 + 0 * 1))
    ring
  · change p * p + p * q - q * q =
      (p - (q * -1 + 0 * 1)) * (p + (q * 0 + 0 * 1)) +
      (0 - (q * 1 + 0 * -1 + 0 * 1)) * (0 + (q * 1 + 0 * 0 + 0 * 1))
    ring
  · change (0 : ℤ) =
      (p - (q * -1 + 0 * 1)) * (0 + (q * 1 + 0 * 0 + 0 * 1)) +
      (0 - (q * 1 + 0 * -1 + 0 * 1)) * (p + (q * 0 + 0 * 1)) +
      (0 - (q * 1 + 0 * -1 + 0 * 1)) * (0 + (q * 1 + 0 * 0 + 0 * 1))
    ring

/-- **Proposition 29.2, right sign reading.** For `p ≥ 0`, `q > 0`:
    `D_R(p,q)` is positive, negative, or (never) zero exactly as `p − qφ` is.
    This is `sgn D_R = sgn(x − φ)` with the positive factor `q` not divided out.
    The order on `ℤ[φ]` is decided through `ℤ√5` (§27's `bridge`); no decimal. -/
theorem side_R (p q : ℕ) (hq : 0 < q) :
    ((0 : Zphi) < ⟨(p : ℤ), 0⟩ - ⟨(q : ℤ), 0⟩ * phi ↔ 0 < DR p q) ∧
    ((⟨(p : ℤ), 0⟩ : Zphi) - ⟨(q : ℤ), 0⟩ * phi < 0 ↔ DR p q < 0) ∧
    DR p q ≠ 0 := by
  rw [dispR_eq]
  exact ⟨bridge p q, bridge_neg p q hq, N_ne_zero _ _ (by omega)⟩

/-- **Proposition 29.2, left sign reading.** For `p ≥ 0`, `q > 0`:
    `sgn D_L(p,q) = sgn(p − qφ⁻¹)`. Carried by the right bridge at `(p + q, q)`
    through `D_L(p,q) = D_R(p + q, q)`. -/
theorem side_L (p q : ℕ) (hq : 0 < q) :
    ((0 : Zphi) < ⟨(p : ℤ), 0⟩ - ⟨(q : ℤ), 0⟩ * phiInv ↔ 0 < DL p q) ∧
    ((⟨(p : ℤ), 0⟩ : Zphi) - ⟨(q : ℤ), 0⟩ * phiInv < 0 ↔ DL p q < 0) ∧
    DL p q ≠ 0 := by
  rw [dispL_eq, DL_eq_DR_shift]
  have h1 := bridge (p + q) q
  have h2 := bridge_neg (p + q) q hq
  rw [Int.natCast_add] at h1 h2
  exact ⟨h1, h2, N_ne_zero _ _ (by omega)⟩

/-! ## Theorem 29.3 — Sign alternation and square invariance -/

/-- **Theorem 29.3.** `D_R(p + q, p) = −D_R(p,q)`, every integer column. -/
theorem DR_mirror (p q : ℤ) : DR (p + q) p = - DR p q := by
  unfold DR N; ring

/-- **Theorem 29.3.** `D_L(q, p + q) = −D_L(p,q)`, every integer column. -/
theorem DL_mirror (p q : ℤ) : DL q (p + q) = - DL p q := by
  unfold DL; ring

theorem mulVec_mul (M K : Mat2) (v : ℤ × ℤ) :
    Mirror.mulVec (M * K) v = Mirror.mulVec M (Mirror.mulVec K v) := by
  obtain ⟨p, q⟩ := v
  change ((M.a * K.a + M.b * K.c) * p + (M.a * K.b + M.b * K.d) * q,
        (M.c * K.a + M.d * K.c) * p + (M.c * K.b + M.d * K.d) * q) =
       (M.a * (K.a * p + K.b * q) + M.b * (K.c * p + K.d * q),
        M.c * (K.a * p + K.b * q) + M.d * (K.c * p + K.d * q))
  rw [Prod.mk.injEq]
  exact ⟨by ring, by ring⟩

theorem mulVec_one (v : ℤ × ℤ) : Mirror.mulVec 1 v = v := by
  obtain ⟨p, q⟩ := v
  change (1 * p + 0 * q, 0 * p + 1 * q) = (p, q)
  rw [Prod.mk.injEq]
  exact ⟨by ring, by ring⟩

/-- **Corollary 27.4, the `n`-step bridge.** `𝖠_Rⁿ v` is the right trajectory:
    the book's `x(𝖠_Rⁿ v)` is `x(trajR v n)`, on which `Chamber` states the
    attraction. -/
theorem trajR_is_power (v : ℕ × ℕ) :
    ∀ n, Mirror.mulVec (matPow Mirror.AR n) ((v.1 : ℤ), (v.2 : ℤ)) =
      (((Mirror.trajR v n).1 : ℤ), ((Mirror.trajR v n).2 : ℤ))
  | 0 => mulVec_one _
  | n + 1 => by
    change Mirror.mulVec (Mirror.AR * matPow Mirror.AR n) _ = _
    rw [mulVec_mul, trajR_is_power v n]
    exact Mirror.AR_acts_as_advR (Mirror.trajR v n)

/-- **Corollary 27.4, the `n`-step bridge, left.** `𝖠_Lⁿ v` is the left trajectory. -/
theorem trajL_is_power (v : ℕ × ℕ) :
    ∀ n, Mirror.mulVec (matPow Mirror.AL n) ((v.1 : ℤ), (v.2 : ℤ)) =
      (((Mirror.trajL v n).1 : ℤ), ((Mirror.trajL v n).2 : ℤ))
  | 0 => mulVec_one _
  | n + 1 => by
    change Mirror.mulVec (Mirror.AL * matPow Mirror.AL n) _ = _
    rw [mulVec_mul, trajL_is_power v n]
    exact Mirror.AL_acts_as_advL (Mirror.trajL v n)

/-- `D_R` of a column, `D_L` of a column. -/
def DRv (v : ℤ × ℤ) : ℤ := DR v.1 v.2

def DLv (v : ℤ × ℤ) : ℤ := DL v.1 v.2

/-- **Theorem 29.3.** `D_R(𝖠_R v) = −D_R(v)` and `D_L(𝖠_L v) = −D_L(v)`. -/
theorem thm_29_3_one (v : ℤ × ℤ) :
    DRv (Mirror.mulVec Mirror.AR v) = - DRv v ∧ DLv (Mirror.mulVec Mirror.AL v) = - DLv v := by
  obtain ⟨p, q⟩ := v
  unfold DRv DLv
  rw [Mirror.AR_column, Mirror.AL_column]
  exact ⟨DR_mirror p q, DL_mirror p q⟩

/-- **Theorem 29.3.** `D_R(𝖠_Rⁿ v) = (−1)ⁿ D_R(v)`, every integer column, every `n`. -/
theorem DR_AR_pow (v : ℤ × ℤ) : ∀ n, DRv (Mirror.mulVec (matPow Mirror.AR n) v) = (-1) ^ n * DRv v
  | 0 => by
    change DRv (Mirror.mulVec 1 v) = 1 * DRv v
    rw [mulVec_one, Int.one_mul]
  | n + 1 => by
    change DRv (Mirror.mulVec (Mirror.AR * matPow Mirror.AR n) v) = _
    rw [mulVec_mul, (thm_29_3_one _).1, DR_AR_pow v n, pow_succ]; ring

/-- **Theorem 29.3.** `D_L(𝖠_Lⁿ v) = (−1)ⁿ D_L(v)`. -/
theorem DL_AL_pow (v : ℤ × ℤ) : ∀ n, DLv (Mirror.mulVec (matPow Mirror.AL n) v) = (-1) ^ n * DLv v
  | 0 => by
    change DLv (Mirror.mulVec 1 v) = 1 * DLv v
    rw [mulVec_one, Int.one_mul]
  | n + 1 => by
    change DLv (Mirror.mulVec (Mirror.AL * matPow Mirror.AL n) v) = _
    rw [mulVec_mul, (thm_29_3_one _).2, DL_AL_pow v n, pow_succ]; ring

theorem sq_neg_one_pow (n : ℕ) (x : ℤ) : ((-1) ^ n * x) ^ 2 = x ^ 2 := by
  rcases PhiPos.neg_one_pow_cases n with h | h <;> rw [h] <;> ring

/-- **Theorem 29.3, square invariance.** `D_R(𝖠_Rⁿ v)² = D_R(v)²` and
    `D_L(𝖠_Lⁿ v)² = D_L(v)²`. -/
theorem thm_29_3_square (v : ℤ × ℤ) (n : ℕ) :
    DRv (Mirror.mulVec (matPow Mirror.AR n) v) ^ 2 = DRv v ^ 2 ∧
    DLv (Mirror.mulVec (matPow Mirror.AL n) v) ^ 2 = DLv v ^ 2 := by
  rw [DR_AR_pow, DL_AL_pow]
  exact ⟨sq_neg_one_pow n _, sq_neg_one_pow n _⟩

/-- The two-step skeleton carries the defect itself, not only its square:
    `D_R((RL) v) = D_R(v)` and `D_L((LR) v) = D_L(v)`, since `𝖠_R² = RL`,
    `𝖠_L² = LR` (Proposition 26.2). -/
theorem skeleton_invariance (v : ℤ × ℤ) :
    DRv (Mirror.mulVec (R * L) v) = DRv v ∧ DLv (Mirror.mulVec (L * R) v) = DLv v := by
  rw [← Mirror.squares.1, ← Mirror.squares.2, mulVec_mul, mulVec_mul, (thm_29_3_one _).1,
    (thm_29_3_one _).1, (thm_29_3_one _).2, (thm_29_3_one _).2, neg_neg, neg_neg]
  exact ⟨rfl, rfl⟩

/-- Theorem 29.3 on the natural trajectories of §26: `D_L` alternates along
    `trajL` (the right half is §27's `Nc_trajR`). -/
theorem DL_trajL (v : ℕ × ℕ) :
    ∀ n, DL (Mirror.trajL v n).1 (Mirror.trajL v n).2 = (-1) ^ n * DL v.1 v.2
  | 0 => by rw [pow_zero, Int.one_mul]; rfl
  | n + 1 => by
    change DL (Mirror.advL (Mirror.trajL v n)).1 (Mirror.advL (Mirror.trajL v n)).2 = _
    change DL ((Mirror.trajL v n).2 : ℤ) (((Mirror.trajL v n).1 + (Mirror.trajL v n).2 : ℕ) : ℤ) = _
    rw [Int.natCast_add, DL_mirror, DL_trajL v n, pow_succ]; ring

/-! ## Corollary 29.4 — Minimal nonzero integer defect class -/

/-- **Corollary 29.4.** Neither defect vanishes on a column with nonzero tail
    (the book asks `p, q > 0`; only `q ≠ 0` is used). `4D_R = (2p − q)² − 5q²` and
    `5` is not a square: this is the integer form of "φ is irrational". -/
theorem DR_ne_zero (p q : ℤ) (hq : q ≠ 0) : DR p q ≠ 0 := N_ne_zero p q hq

theorem DL_ne_zero (p q : ℤ) (hq : q ≠ 0) : DL p q ≠ 0 := by
  rw [DL_eq_DR_shift]; exact N_ne_zero _ _ hq

theorem one_le_sq_of_ne_zero (x : ℤ) (hx : x ≠ 0) : 1 ≤ x * x := by
  rcases Int.lt_trichotomy x 0 with h | h | h
  · have e : x * x = (-x) * (-x) := by ring
    rw [e]
    have h1 : 1 ≤ -x := by omega
    have := Int.mul_le_mul h1 h1 (by decide) (by omega)
    omega
  · exact absurd h hx
  · have h1 : 1 ≤ x := h
    have := Int.mul_le_mul h1 h1 (by decide) (by omega)
    omega

/-- **Corollary 29.4.** `|D_R| ≥ 1` and `|D_L| ≥ 1` on every column with nonzero
    tail, read both as `natAbs` and as the square; and the bound is attained,
    at `1:1`, so `|D| = 1` is the least nonzero class. -/
theorem cor_29_4 :
    (∀ p q : ℤ, q ≠ 0 →
      1 ≤ (DR p q).natAbs ∧ 1 ≤ (DL p q).natAbs ∧
      1 ≤ DR p q * DR p q ∧ 1 ≤ DL p q * DL p q) ∧
    DR 1 1 = -1 ∧ DL 1 1 = 1 := by
  refine ⟨fun p q hq => ?_, by decide, by decide⟩
  exact ⟨Int.natAbs_pos.mpr (DR_ne_zero p q hq), Int.natAbs_pos.mpr (DL_ne_zero p q hq),
    one_le_sq_of_ne_zero _ (DR_ne_zero p q hq), one_le_sq_of_ne_zero _ (DL_ne_zero p q hq)⟩

/-- **Corollary 29.4, orbit form.** A column in the minimal class keeps its whole
    mirror orbit there: `D(v)² = 1 ⇒ D(𝖠ⁿ v)² = 1` for every `n`. -/
theorem minimal_class_orbit (v : ℤ × ℤ) :
    (DRv v ^ 2 = 1 → ∀ n, DRv (Mirror.mulVec (matPow Mirror.AR n) v) ^ 2 = 1) ∧
    (DLv v ^ 2 = 1 → ∀ n, DLv (Mirror.mulVec (matPow Mirror.AL n) v) ^ 2 = 1) :=
  ⟨fun h n => (thm_29_3_square v n).1.trans h, fun h n => (thm_29_3_square v n).2.trans h⟩

/-! ## Theorem 29.5 — Fibonacci orbit is the minimal golden weave -/

/-- **Theorem 29.5.** `D_R(F_{n+2}, F_{n+1}) = (−1)ⁿ⁺¹` and
    `D_L(F_{n+1}, F_{n+2}) = (−1)ⁿ`, for every `n`. The book's proof, as written:
    Corollary 26.4 gives the columns, Theorem 29.3 flips the defect each advance,
    and `D_R(1,1) = −1`, `D_L(1,1) = 1` start it. -/
theorem thm_29_5 (n : ℕ) :
    DR (Mirror.F (n + 2)) (Mirror.F (n + 1)) = (-1) ^ (n + 1) ∧
    DL (Mirror.F (n + 1)) (Mirror.F (n + 2)) = (-1) ^ n := by
  have hR := DR_AR_pow (1, 1) n
  have hL := DL_AL_pow (1, 1) n
  rw [(Mirror.orbit_from_one n).1] at hR
  rw [(Mirror.orbit_from_one n).2] at hL
  refine ⟨hR.trans ?_, hL.trans ?_⟩
  · change (-1) ^ n * DR 1 1 = _
    rw [pow_succ, show DR 1 1 = -1 by decide]
  · change (-1) ^ n * DL 1 1 = _
    rw [show DL 1 1 = 1 by decide, Int.mul_one]

/-- The same fact is Cassini's identity (`PhiPos.cassini`), read one column
    earlier: `D_R(F_{n+1}, F_n) = (−1)ⁿ`. -/
theorem cassini_is_weave (n : ℕ) : DR (Mirror.F (n + 1)) (Mirror.F n) = (-1) ^ n := by
  rw [← PhiPos.cassini n]
  unfold DR N; ring

/-- **Theorem 29.5, the minimal class.** `D_R² = D_L² = 1` along both orbits. -/
theorem fib_minimal (n : ℕ) :
    DR (Mirror.F (n + 2)) (Mirror.F (n + 1)) ^ 2 = 1 ∧
    DL (Mirror.F (n + 1)) (Mirror.F (n + 2)) ^ 2 = 1 := by
  rw [(thm_29_5 n).1, (thm_29_5 n).2]
  exact ⟨by rw [← Int.mul_one ((-1) ^ (n + 1)), sq_neg_one_pow]; rfl,
    by rw [← Int.mul_one ((-1) ^ n), sq_neg_one_pow]; rfl⟩

theorem fib_succ_pos (n : ℕ) : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (Nat.succ_pos n)

/-- **Theorem 29.5, the sides.** `F_{n+2} − F_{n+1}φ` is above zero exactly when
    `(−1)ⁿ⁺¹ = 1`, and `F_{n+1} − F_{n+2}φ⁻¹` exactly when `(−1)ⁿ = 1`; the other
    parity is strictly below, never on the ridge. -/
theorem fib_sides (n : ℕ) :
    ((0 : Zphi) < ⟨Mirror.F (n + 2), 0⟩ - ⟨Mirror.F (n + 1), 0⟩ * phi ↔ (-1 : ℤ) ^ (n + 1) = 1) ∧
    ((⟨Mirror.F (n + 2), 0⟩ : Zphi) - ⟨Mirror.F (n + 1), 0⟩ * phi < 0 ↔ (-1 : ℤ) ^ (n + 1) = -1) ∧
    ((0 : Zphi) < ⟨Mirror.F (n + 1), 0⟩ - ⟨Mirror.F (n + 2), 0⟩ * phiInv ↔ (-1 : ℤ) ^ n = 1) ∧
    ((⟨Mirror.F (n + 1), 0⟩ : Zphi) - ⟨Mirror.F (n + 2), 0⟩ * phiInv < 0 ↔ (-1 : ℤ) ^ n = -1) := by
  obtain ⟨r1, r2, -⟩ := side_R (Nat.fib (n + 2)) (Nat.fib (n + 1)) (fib_succ_pos n)
  obtain ⟨l1, l2, -⟩ := side_L (Nat.fib (n + 1)) (Nat.fib (n + 2)) (fib_succ_pos (n + 1))
  refine ⟨r1.trans ?_, r2.trans ?_, l1.trans ?_, l2.trans ?_⟩ <;>
    [rw [(thm_29_5 n).1]; rw [(thm_29_5 n).1]; rw [(thm_29_5 n).2]; rw [(thm_29_5 n).2]] <;>
    [rcases PhiPos.neg_one_pow_cases (n + 1) with h | h;
     rcases PhiPos.neg_one_pow_cases (n + 1) with h | h;
     rcases PhiPos.neg_one_pow_cases n with h | h;
     rcases PhiPos.neg_one_pow_cases n with h | h] <;>
    rw [h] <;> exact ⟨fun k => by omega, fun k => by omega⟩

/-- **Theorem 29.5, alternation at every advance.** The right rational value is
    above `φ` at step `n` exactly when it is below at step `n + 1`; likewise left. -/
theorem fib_alternates (n : ℕ) :
    ((0 : Zphi) < ⟨Mirror.F (n + 2), 0⟩ - ⟨Mirror.F (n + 1), 0⟩ * phi ↔
      (⟨Mirror.F (n + 3), 0⟩ : Zphi) - ⟨Mirror.F (n + 2), 0⟩ * phi < 0) ∧
    ((0 : Zphi) < ⟨Mirror.F (n + 1), 0⟩ - ⟨Mirror.F (n + 2), 0⟩ * phiInv ↔
      (⟨Mirror.F (n + 2), 0⟩ : Zphi) - ⟨Mirror.F (n + 3), 0⟩ * phiInv < 0) := by
  have e1 : (-1 : ℤ) ^ (n + 2) = (-1) ^ (n + 1) * -1 := pow_succ _ _
  have e0 : (-1 : ℤ) ^ (n + 1) = (-1) ^ n * -1 := pow_succ _ _
  rw [(fib_sides n).1, (fib_sides (n + 1)).2.1, (fib_sides n).2.2.1, (fib_sides (n + 1)).2.2.2,
    e1, e0]
  rcases PhiPos.neg_one_pow_cases n with h | h <;> rw [h] <;> decide

/-! ## Proposition 29.6 — One skeleton, renewed class, and growing separation -/

/-- The positive word `(RL)^r`, built by appending, so `G` peels from the right. -/
def rlWord : ℕ → Word
  | 0 => []
  | r + 1 => rlWord r ++ [true, false]

theorem G_rlWord : ∀ r, G (rlWord r) = matPow (R * L) r
  | 0 => rfl
  | r + 1 => by
    change G (rlWord r ++ [true, false]) = _
    rw [G_append, G_rlWord r, Mirror.mpow_succ_right]
    rfl

/-- **Definition 28.1 at `s = R`.** `Q_R(v) = G(v)⁻¹ A_R`, with `A_R = R⁻¹L`
    (§10's `A true`) and the inverse the determinant-one adjugate (§11's `Two.Q`). -/
def QR (v : Word) : Mat2 := Two.Q (G v) (A true)

theorem QR_det (v : Word) : (QR v).det = 1 := by
  unfold QR Two.Q
  rw [det_mul, show (A true).det = 1 by decide]
  have h := det_G v
  generalize G v = M at h
  cases M with | mk a b c d =>
  change (d * a - -b * -c) * 1 = 1
  have h' : a * d - b * c = 1 := h
  calc (d * a - -b * -c) * 1 = a * d - b * c := by ring
    _ = 1 := h'

/-- **Proposition 29.6 (Theorem 28.9's first display).**
    `Q_R((RL)^r) = [[−F_{2r}, −F_{2r+1}], [F_{2r+1}, F_{2r+2}]]`, every `r`. -/
theorem QR_strobe : ∀ r : ℕ,
    QR (rlWord r) = ⟨-Mirror.F (2 * r), -Mirror.F (2 * r + 1), Mirror.F (2 * r + 1),
      Mirror.F (2 * r + 2)⟩
  | 0 => by decide
  | r + 1 => by
    have step : QR (rlWord (r + 1)) = inv2 (R * L) * QR (rlWord r) := by
      change inv2 (G (rlWord r ++ [true, false])) * A true = inv2 (R * L) * (inv2 (G (rlWord r))
        * A true)
      rw [G_append, inv2_mul, Mat2.mul_assoc']
      rfl
    rw [step, QR_strobe r, show inv2 (R * L) = ⟨1, -1, -1, 2⟩ by decide]
    have h2 : Mirror.F (2 * r + 2) = Mirror.F (2 * r + 1) + Mirror.F (2 * r) := Mirror.F_rec (2 * r)
    have h3 : Mirror.F (2 * r + 3) = Mirror.F (2 * r + 2) + Mirror.F (2 * r + 1) :=
      Mirror.F_rec (2 * r + 1)
    have h4 : Mirror.F (2 * r + 4) = Mirror.F (2 * r + 3) + Mirror.F (2 * r + 2) :=
      Mirror.F_rec (2 * r + 2)
    change (⟨1 * -Mirror.F (2 * r) + -1 * Mirror.F (2 * r + 1),
      1 * -Mirror.F (2 * r + 1) + -1 * Mirror.F (2 * r + 2),
      -1 * -Mirror.F (2 * r) + 2 * Mirror.F (2 * r + 1),
      -1 * -Mirror.F (2 * r + 1) + 2 * Mirror.F (2 * r + 2)⟩ : Mat2) =
      ⟨-Mirror.F (2 * r + 2), -Mirror.F (2 * r + 3), Mirror.F (2 * r + 3), Mirror.F (2 * r + 4)⟩
    rw [Mat2.mk.injEq]
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- The trace of `Q_R((RL)^r)` is `F_{2r+1}`. -/
theorem QR_strobe_trace (r : ℕ) :
    (QR (rlWord r)).a + (QR (rlWord r)).d = Mirror.F (2 * r + 1) := by
  rw [QR_strobe]
  change -Mirror.F (2 * r) + Mirror.F (2 * r + 2) = Mirror.F (2 * r + 1)
  have h2 : Mirror.F (2 * r + 2) = Mirror.F (2 * r + 1) + Mirror.F (2 * r) := Mirror.F_rec (2 * r)
  omega

/-- The route correction at every even strobe is `+1`: lower-left `F_{2r+1} > 0`
    and trace `F_{2r+1} > 0`. -/
theorem QR_strobe_route (r : ℕ) : routeCorrection (QR (rlWord r)) = 1 := by
  have ht := QR_strobe_trace r
  have hc : (QR (rlWord r)).c = Mirror.F (2 * r + 1) := by rw [QR_strobe]
  have hpos : (0 : ℤ) < Mirror.F (2 * r + 1) := Int.ofNat_lt.mpr (fib_succ_pos (2 * r))
  unfold routeCorrection
  change (if (QR (rlWord r)).c * ((QR (rlWord r)).a + (QR (rlWord r)).d) > 0 then (1 : ℤ)
    else if (QR (rlWord r)).c * ((QR (rlWord r)).a + (QR (rlWord r)).d) < 0 then -1 else 0) = 1
  rw [ht, hc, if_pos (Int.mul_pos hpos hpos)]

/-- The Dedekind sum of Definition 28.2, cleared of denominators exactly as in
    `Transport.dedekindSumInt` (`S(a,k) = Σ_{r=1}^{k-1} (2r − k)(2(a·r mod k) − k)`,
    which is `4k²·s_D(a,k)`), but summed by structural recursion.

    **Why a second carrier.** `Transport.phiRad` sums over `Finset.range`, and
    the *definition* `Finset.range` depends on `Classical.choice` (measured:
    `#print axioms Finset.range`). Every theorem that so much as mentions
    `Transport.phiRad` or `Transport.psiRad` therefore prints `Classical.choice`,
    whatever its proof. The integer formula below is the same one, term for term;
    only the summation carrier differs. An agreement theorem with
    `Transport.phiRad` cannot be stated choice-free for the same reason, so none is
    stated. `routeCorrection` (§28's `σ_Rad`) is choice-free and is used as is. -/
def dsumRec (a : ℤ) (k : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => dsumRec a k n + (2 * ((n : ℤ) + 1) - k) * (2 * ((a * ((n : ℤ) + 1)) % (k : ℤ)) - k)

def dedekindRec (a : ℤ) (k : ℕ) : ℤ := if k = 0 then 0 else dsumRec a k (k - 1)

/-- **Definition 28.2's `Φ_Rad`**, the integer-only form of `Transport.phiRad`,
    over the recursive sum. -/
def phiRadE (Q : Mat2) : ℤ :=
  if Q.c = 0 then
    if Q.d ≠ 0 then Q.b / Q.d else 0
  else
    let k := Q.c.natAbs
    let sgnC : ℤ := if Q.c > 0 then 1 else -1
    let s := dedekindRec Q.a k
    sgnC * ((k : ℤ) * (Q.a + Q.d) - 3 * s) / ((k : ℤ) * k)

/-- **Definition 28.2's `Ψ_Rad = Φ_Rad − 3σ_Rad`.** -/
def psiRadE (Q : Mat2) : ℤ := phiRadE Q - 3 * routeCorrection Q

/-- **Proposition 29.6, the class coordinate.** Given the transport value
    `Φ_Rad(Q_R((RL)^r)) = 1` (Theorem 28.9's table, §28), the homogeneous class is
    `Ψ_Rad = Φ_Rad − 3σ_Rad = 1 − 3 = −2`. The `σ_Rad = +1` half is proved above;
    the `Φ_Rad = 1` half is §28's and is carried here as the hypothesis `hΦ`. -/
theorem QR_strobe_class (r : ℕ) (hΦ : phiRadE (QR (rlWord r)) = 1) :
    psiRadE (QR (rlWord r)) = -2 := by
  change phiRadE (QR (rlWord r)) - 3 * routeCorrection (QR (rlWord r)) = -2
  rw [hΦ, QR_strobe_route]; rfl

/-- `Φ_Rad = 1`, hence `Ψ_Rad = −2`, checked by the kernel on the first strobes
    from the recursive-sum `phiRadE` (no hypothesis). -/
theorem QR_strobe_class_witness :
    phiRadE (QR (rlWord 0)) = 1 ∧ phiRadE (QR (rlWord 1)) = 1 ∧
    phiRadE (QR (rlWord 2)) = 1 ∧ phiRadE (QR (rlWord 3)) = 1 ∧
    phiRadE (QR (rlWord 4)) = 1 ∧
    psiRadE (QR (rlWord 0)) = -2 ∧ psiRadE (QR (rlWord 1)) = -2 ∧
    psiRadE (QR (rlWord 2)) = -2 ∧ psiRadE (QR (rlWord 3)) = -2 ∧
    psiRadE (QR (rlWord 4)) = -2 := by
  decide

theorem F_step (n : ℕ) : Mirror.F n < Mirror.F (n + 2) ∨ n = 0 := by
  rcases n with _ | n
  · exact Or.inr rfl
  · left
    have h' : Mirror.F (n + 3) = Mirror.F (n + 2) + Mirror.F (n + 1) := Mirror.F_rec (n + 1)
    have hp : (0 : ℤ) < Mirror.F (n + 2) := Int.ofNat_lt.mpr (fib_succ_pos (n + 1))
    change Mirror.F (n + 1) < Mirror.F (n + 3)
    omega

/-- **Proposition 29.6, growing separation, exact form.** The trace strictly
    increases from strobe to strobe and is at least `r + 1`; each entry's absolute
    value strictly increases. "Grows without bound" is the lower bound, not a limit. -/
theorem strobe_growth (r : ℕ) :
    Mirror.F (2 * r + 1) < Mirror.F (2 * (r + 1) + 1) ∧
    (r : ℤ) + 1 ≤ Mirror.F (2 * r + 1) ∧
    Mirror.F (2 * r) < Mirror.F (2 * (r + 1)) ∧
    Mirror.F (2 * r + 2) < Mirror.F (2 * (r + 1) + 2) := by
  have g1 : Mirror.F (2 * r + 1) < Mirror.F (2 * r + 3) :=
    (F_step (2 * r + 1)).resolve_right (by omega)
  have g2 : Mirror.F (2 * r + 2) < Mirror.F (2 * r + 4) :=
    (F_step (2 * r + 2)).resolve_right (by omega)
  have g0 : Mirror.F (2 * r) < Mirror.F (2 * r + 2) := by
    rcases F_step (2 * r) with h | h
    · exact h
    · have hr : r = 0 := by omega
      subst hr; decide
  have lower : ∀ s : ℕ, (s : ℤ) + 1 ≤ Mirror.F (2 * s + 1) := by
    intro s
    induction s with
    | zero => decide
    | succ s ih =>
      have hs : Mirror.F (2 * s + 1) < Mirror.F (2 * s + 3) :=
        (F_step (2 * s + 1)).resolve_right (by omega)
      change ((s + 1 : ℕ) : ℤ) + 1 ≤ Mirror.F (2 * s + 3)
      rw [Int.natCast_add]
      have e : ((1 : ℕ) : ℤ) = 1 := rfl
      omega
  exact ⟨g1, lower r, g0, g2⟩

/-- The strobe relative matrices never repeat. -/
theorem strobe_distinct (m n : ℕ) (hmn : m ≠ n) : QR (rlWord m) ≠ QR (rlWord n) := by
  intro h
  have ht : (QR (rlWord m)).a + (QR (rlWord m)).d = (QR (rlWord n)).a + (QR (rlWord n)).d := by
    rw [h]
  rw [QR_strobe_trace, QR_strobe_trace] at ht
  have mono : ∀ a d : ℕ, Mirror.F (2 * a + 1) < Mirror.F (2 * (a + d + 1) + 1) := by
    intro a d
    induction d with
    | zero => exact (strobe_growth a).1
    | succ d ih => exact lt_trans ih (strobe_growth (a + d + 1)).1
  rcases Nat.lt_or_gt_of_ne hmn with k | k
  · obtain ⟨d, rfl⟩ : ∃ d, n = m + d + 1 := ⟨n - m - 1, by omega⟩
    have := mono m d; omega
  · obtain ⟨d, rfl⟩ : ∃ d, m = n + d + 1 := ⟨m - n - 1, by omega⟩
    have := mono n d; omega

/-- **Proposition 29.6.** At every even right-mirror strobe: `𝖠_R^{2r} = (RL)^r`;
    `𝖠_R^{2r}(1,1)ᵀ = (F_{2r+2}, F_{2r+1})ᵀ` with `D_R = −1`;
    `tr Q_R((RL)^r) = F_{2r+1}`, the column's second coordinate; `σ_Rad = +1`;
    `Ψ_Rad = −2` given §28's `Φ_Rad = 1`; and the trace strictly grows, bounded
    below by `r + 1`. -/
theorem prop_29_6 (r : ℕ) (hΦ : phiRadE (QR (rlWord r)) = 1) :
    matPow Mirror.AR (2 * r) = matPow (R * L) r ∧
    Mirror.mulVec (matPow Mirror.AR (2 * r)) (1, 1) = (Mirror.F (2 * r + 2), Mirror.F (2 * r + 1)) ∧
    DR (Mirror.F (2 * r + 2)) (Mirror.F (2 * r + 1)) = -1 ∧
    (QR (rlWord r)).a + (QR (rlWord r)).d =
      (Mirror.mulVec (matPow Mirror.AR (2 * r)) (1, 1)).2 ∧
    routeCorrection (QR (rlWord r)) = 1 ∧
    psiRadE (QR (rlWord r)) = -2 ∧
    (QR (rlWord r)).a + (QR (rlWord r)).d < (QR (rlWord (r + 1))).a + (QR (rlWord (r + 1))).d ∧
    (r : ℤ) + 1 ≤ (QR (rlWord r)).a + (QR (rlWord r)).d := by
  have hcol := (Mirror.orbit_from_one (2 * r)).1
  refine ⟨Mirror.AR_pow_even r, hcol, ?_, ?_, QR_strobe_route r, QR_strobe_class r hΦ, ?_, ?_⟩
  · rw [(thm_29_5 (2 * r)).1, pow_succ, pow_mul, show ((-1 : ℤ) ^ 2) = 1 by decide, one_pow,
      Int.one_mul]
  · rw [hcol, QR_strobe_trace]
  · rw [QR_strobe_trace, QR_strobe_trace]; exact (strobe_growth r).1
  · rw [QR_strobe_trace]; exact (strobe_growth r).2.1

/-! ## Separation Rule 29.7 — Quadratic defect is an arithmetic invariant of the mirror recurrence

    The sentences `D² ≠ energy`, `tr Q ≠ mass` name objects (energy, mass) that
    have no representation anywhere in this tree, so they are prose here, carried
    by absence: `DR`, `DL : ℤ → ℤ → ℤ` and `routeCorrection`, `psiRadE : Mat2 → ℤ`
    carry no units field and no dimensional map.

    What *is* formalisable is the internal half: the squared defect and the trace
    are different exact data on the same recurrence. Along the strobes `D_R² = 1`
    (right, `(RL)^r`) and `D_L² = 1` (left, `(LR)^r`) throughout while the trace
    takes distinct values, so no function of either squared defect returns the
    trace. -/

/-- **Separation Rule 29.7, exact witness.** No function of `D_R²` recovers
    `tr Q_R((RL)^r)` along the strobes. -/
theorem trace_not_function_of_defect_sq :
    ¬ ∃ f : ℤ → ℤ, ∀ r : ℕ,
      f (DR (Mirror.F (2 * r + 2)) (Mirror.F (2 * r + 1)) ^ 2) =
        (QR (rlWord r)).a + (QR (rlWord r)).d := by
  rintro ⟨f, hf⟩
  have h0 := hf 0
  have h1 := hf 1
  rw [(fib_minimal (2 * 0)).1, QR_strobe_trace] at h0
  rw [(fib_minimal (2 * 1)).1, QR_strobe_trace] at h1
  rw [h0] at h1
  exact absurd h1 (by decide)

/-- The positive word `(LR)^r`, built by appending, the left strobe word. -/
def lrWord : ℕ → Word
  | 0 => []
  | r + 1 => lrWord r ++ [false, true]

theorem G_lrWord : ∀ r, G (lrWord r) = matPow (L * R) r
  | 0 => rfl
  | r + 1 => by
    change G (lrWord r ++ [false, true]) = _
    rw [G_append, G_lrWord r, Mirror.mpow_succ_right]
    rfl

/-- **Definition 28.1 at `s = L`.** `Q_L(v) = G(v)⁻¹ A_L`, with `A_L = L⁻¹R`
    (§10's `A false`). -/
def QL (v : Word) : Mat2 := Two.Q (G v) (A false)

/-- **Separation Rule 29.7, exact witness, left.** No function of `D_L²` recovers
    `tr Q_L((LR)^r)` along the left strobes `𝖠_L^{2r}(1,1)ᵀ = (F_{2r+1}, F_{2r+2})ᵀ`:
    `D_L² = 1` there (Theorem 29.5), while the trace is `1` at `r = 0` and `2` at `r = 1`. -/
theorem trace_not_function_of_defectL_sq :
    ¬ ∃ f : ℤ → ℤ, ∀ r : ℕ,
      f (DL (Mirror.F (2 * r + 1)) (Mirror.F (2 * r + 2)) ^ 2) =
        (QL (lrWord r)).a + (QL (lrWord r)).d := by
  rintro ⟨f, hf⟩
  have h0 := hf 0
  have h1 := hf 1
  rw [(fib_minimal (2 * 0)).2, show (QL (lrWord 0)).a + (QL (lrWord 0)).d = 1 by decide] at h0
  rw [(fib_minimal (2 * 1)).2, show (QL (lrWord 1)).a + (QL (lrWord 1)).d = 2 by decide] at h1
  rw [h0] at h1
  exact absurd h1 (by decide)

/-! ## Boundary Statement 29.8 -/

/-- **Boundary Statement 29.8, strict left alternation.** From a positive start,
    the left defect at step `n` is positive exactly when the defect after the next
    left advance is strictly negative (`< 0`, not merely `¬ 0 <`). Composes §27's
    `alternation_L` with `side_L`: the left defect is `D_L` read through
    `dispL_eq`, and `D_L ≠ 0` on a positive tail. -/
theorem alternation_L_strict (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) (n : ℕ) :
    (0 : Zphi) < Chamber.defectL (Mirror.trajL v n) ↔
      Chamber.defectL (Mirror.trajL v (n + 1)) < 0 := by
  have hq : 0 < (Mirror.trajL v (n + 1)).2 := by
    rw [Mirror.trajL_mirror]
    exact (Mirror.trajR_pos v.swap ⟨hv.2, hv.1⟩ (n + 1)).1
  have hS := side_L (Mirror.trajL v (n + 1)).1 (Mirror.trajL v (n + 1)).2 hq
  rw [dispL_eq] at hS
  have hpos : (0 : Zphi) < Chamber.defectL (Mirror.trajL v (n + 1)) ↔
      0 < DL (Mirror.trajL v (n + 1)).1 (Mirror.trajL v (n + 1)).2 := hS.1
  have hneg : Chamber.defectL (Mirror.trajL v (n + 1)) < 0 ↔
      DL (Mirror.trajL v (n + 1)).1 (Mirror.trajL v (n + 1)).2 < 0 := hS.2.1
  rw [Chamber.alternation_L v hv n, hpos, hneg]
  have hne := hS.2.2
  exact ⟨fun h => by
    rcases Int.lt_trichotomy (DL (Mirror.trajL v (n + 1)).1 (Mirror.trajL v (n + 1)).2) 0
      with k | k | k
    · exact k
    · exact absurd k hne
    · exact absurd k h, fun h h' => by omega⟩

/-- **Boundary Statement 29.8, for every positive rational state.** Rational state
    → alternating ridge side → invariant nonzero defect square: along the right
    trajectory from any positive `v`, the right displacement changes side at each
    advance (§27's `alternation_R`), the defect is `(−1)ⁿ D_R(v)`, its square is
    `D_R(v)²`, and that square is at least `1`. Left mirror likewise. -/
theorem boundary_29_8 (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) (n : ℕ) :
    ((0 : Zphi) < Chamber.defectR (Mirror.trajR v n) ↔ Chamber.defectR (Mirror.trajR v (n + 1))
      < 0) ∧
    ((0 : Zphi) < Chamber.defectL (Mirror.trajL v n) ↔ Chamber.defectL (Mirror.trajL v (n + 1))
      < 0) ∧
    DR (Mirror.trajR v n).1 (Mirror.trajR v n).2 = (-1) ^ n * DR v.1 v.2 ∧
    DL (Mirror.trajL v n).1 (Mirror.trajL v n).2 = (-1) ^ n * DL v.1 v.2 ∧
    DR (Mirror.trajR v n).1 (Mirror.trajR v n).2 ^ 2 = DR v.1 v.2 ^ 2 ∧
    DL (Mirror.trajL v n).1 (Mirror.trajL v n).2 ^ 2 = DL v.1 v.2 ^ 2 ∧
    1 ≤ DR v.1 v.2 * DR v.1 v.2 ∧ 1 ≤ DL v.1 v.2 * DL v.1 v.2 := by
  have hq : (v.2 : ℤ) ≠ 0 := by omega
  have hR : DR (Mirror.trajR v n).1 (Mirror.trajR v n).2 = (-1) ^ n * DR v.1 v.2 :=
    Chamber.Nc_trajR v n
  refine ⟨Chamber.alternation_R v hv n, alternation_L_strict v hv n, hR, DL_trajL v n,
    by rw [hR]; exact sq_neg_one_pow n _, by rw [DL_trajL]; exact sq_neg_one_pow n _,
    (cor_29_4.1 _ _ hq).2.2.1, (cor_29_4.1 _ _ hq).2.2.2⟩

/-- **Boundary Statement 29.8, the `1:1` certificate and the skeleton.** The
    Fibonacci orbit sits in the least class `D_R, D_L = ±1`; the same two-step
    skeleton `(RL)^r` carries a strictly growing relative trace and route
    correction `+1`; and, given §28's transport value, the renewed class `−2`. -/
theorem boundary_29_8_orbit (hΦ : ∀ r, phiRadE (QR (rlWord r)) = 1) :
    (∀ n, DR (Mirror.F (n + 2)) (Mirror.F (n + 1)) ^ 2 = 1 ∧
      DL (Mirror.F (n + 1)) (Mirror.F (n + 2)) ^ 2 = 1) ∧
    (∀ r, psiRadE (QR (rlWord r)) = -2) ∧
    (∀ m n, m ≠ n → QR (rlWord m) ≠ QR (rlWord n)) ∧
    (∀ r, (QR (rlWord r)).a + (QR (rlWord r)).d <
      (QR (rlWord (r + 1))).a + (QR (rlWord (r + 1))).d) :=
  ⟨fib_minimal, fun r => QR_strobe_class r (hΦ r), strobe_distinct,
    fun r => (prop_29_6 r (hΦ r)).2.2.2.2.2.2.1⟩

#print axioms def_29_1
#print axioms DL_eq_neg_DR_swap
#print axioms DL_eq_DR_shift
#print axioms DRz_int
#print axioms DLz_int
#print axioms ridge_zeros
#print axioms DRz_factor
#print axioms DLz_factor
#print axioms ridge_zeros_proj
#print axioms dispR_eq
#print axioms dispL_eq
#print axioms prop_29_2_factor
#print axioms side_R
#print axioms side_L
#print axioms DR_mirror
#print axioms DL_mirror
#print axioms mulVec_mul
#print axioms mulVec_one
#print axioms thm_29_3_one
#print axioms DR_AR_pow
#print axioms DL_AL_pow
#print axioms sq_neg_one_pow
#print axioms thm_29_3_square
#print axioms skeleton_invariance
#print axioms DL_trajL
#print axioms DR_ne_zero
#print axioms DL_ne_zero
#print axioms one_le_sq_of_ne_zero
#print axioms cor_29_4
#print axioms minimal_class_orbit
#print axioms thm_29_5
#print axioms cassini_is_weave
#print axioms fib_minimal
#print axioms fib_succ_pos
#print axioms fib_sides
#print axioms fib_alternates
#print axioms G_rlWord
#print axioms QR_det
#print axioms QR_strobe
#print axioms QR_strobe_trace
#print axioms QR_strobe_route
#print axioms QR_strobe_class
#print axioms QR_strobe_class_witness
#print axioms F_step
#print axioms strobe_growth
#print axioms strobe_distinct
#print axioms prop_29_6
#print axioms trace_not_function_of_defect_sq
#print axioms G_lrWord
#print axioms trace_not_function_of_defectL_sq
#print axioms alternation_L_strict
#print axioms boundary_29_8
#print axioms boundary_29_8_orbit
#print axioms trajR_is_power
#print axioms trajL_is_power

end RidgeDefect
end Two
end RatioSpace
