/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S26.Mirror
import RatioSpace.ElementsII.S27.PhiPos
import RatioSpace.ElementsII.S13.SideExchange
import RatioSpace.ElementsII.S28.Transport
/-!
  Elements II §27 — Two chambers and the parity membrane.

  The book writes `x(v) = p/q ∈ ℚ>0` and the maps `f_R(x) = 1 + 1/x`,
  `f_L(x) = 1/(1+x)`. None of that is a point here. A ratio is its column
  `(p, q)`; two columns name the same ratio when `p·q' = p'·q` (`ProjEq`);
  "`x > 1`" is `q < p`; `f_R`, `f_L` are `advR`, `advL` from §26, and the
  theorems below show they respect `ProjEq`, which is what makes them maps on
  ratios at all.

  The golden ridges live in `ℤ[φ]` (`Zphi`), as columns `(φ, 1)` and `(φ⁻¹, 1)`.
  The book's "converges to φ" (Corollary 27.4) is an analytic sentence and so a
  shadow: its exact integer form is built here as
    * the conserved form `N(p,q) = p² − pq − q²`, which flips sign at every
      advance and is never zero on a column with positive tail, and
    * the ridge defect `p − qφ ∈ ℤ[φ]`, whose sign is the sign of `N`, and which
      is multiplied by exactly `−φ⁻¹` at every advance, so after `n` advances it
      is `(−φ⁻¹)ⁿ` times the initial defect, `φ⁻ⁿ` positive and strictly
      decreasing (`PhiPos`).
  No limit is taken, no real number appears, nothing is divided.

  **Choice discipline.** `Zphi`'s generic `mul_pos` carries `Classical.choice`
  (via `IsStrictOrderedRing.of_mul_pos`), so every order fact about `ℤ[φ]` below
  is decided from integers through `Zsqrtd.Nonnegg`, following `PhiPos`.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Two
namespace Chamber

open Mirror Zphi

/-! ## Definition 27.1 — Projective chambers and membrane -/

/-- The three sides of the parity membrane. -/
inductive Side
  | right
  | left
  | membrane
  deriving DecidableEq, Repr

/-- **Definition 27.1.** The chamber of a column, by integer comparison only:
    `p/q > 1` is `q < p`, `p/q < 1` is `p < q`, the membrane is `p = q`. -/
def chamber (v : ℕ × ℕ) : Side :=
  if v.2 < v.1 then .right else if v.1 < v.2 then .left else .membrane

/-- Two columns present the same ratio: `p·q' = p'·q`. -/
def ProjEq (v w : ℕ × ℕ) : Prop := v.1 * w.2 = w.1 * v.2

theorem projEq_symm {v w : ℕ × ℕ} (h : ProjEq v w) : ProjEq w v := h.symm

theorem chamber_right {v : ℕ × ℕ} (h : v.2 < v.1) : chamber v = .right := if_pos h

theorem chamber_left {v : ℕ × ℕ} (h : v.1 < v.2) : chamber v = .left := by
  unfold chamber
  rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt h)), if_pos h]

theorem chamber_membrane {v : ℕ × ℕ} (h : v.1 = v.2) : chamber v = .membrane := by
  unfold chamber
  rw [if_neg (by rw [h]; exact Nat.lt_irrefl _), if_neg (by rw [h]; exact Nat.lt_irrefl _)]

theorem chamber_right_iff (v : ℕ × ℕ) : chamber v = .right ↔ v.2 < v.1 := by
  refine ⟨fun h => ?_, chamber_right⟩
  rcases Nat.lt_trichotomy v.2 v.1 with h' | h' | h'
  · exact h'
  · rw [chamber_membrane h'.symm] at h; exact absurd h (by decide)
  · rw [chamber_left h'] at h; exact absurd h (by decide)

theorem chamber_left_iff (v : ℕ × ℕ) : chamber v = .left ↔ v.1 < v.2 := by
  refine ⟨fun h => ?_, chamber_left⟩
  rcases Nat.lt_trichotomy v.2 v.1 with h' | h' | h'
  · rw [chamber_right h'] at h; exact absurd h (by decide)
  · rw [chamber_membrane h'.symm] at h; exact absurd h (by decide)
  · exact h'

theorem chamber_membrane_iff (v : ℕ × ℕ) : chamber v = .membrane ↔ v.1 = v.2 := by
  refine ⟨fun h => ?_, chamber_membrane⟩
  rcases Nat.lt_trichotomy v.2 v.1 with h' | h' | h'
  · rw [chamber_right h'] at h; exact absurd h (by decide)
  · exact h'.symm
  · rw [chamber_left h'] at h; exact absurd h (by decide)

/-- `q < p` transfers across a projective equality when the target tail is positive. -/
theorem right_transfer {v w : ℕ × ℕ} (hw : 0 < w.2) (h : ProjEq v w)
    (hr : v.2 < v.1) : w.2 < w.1 := by
  rcases Nat.lt_or_ge w.2 w.1 with h' | h'
  · exact h'
  · exfalso
    have h1 : v.2 * w.2 < v.1 * w.2 := Nat.mul_lt_mul_of_pos_right hr hw
    have h2 : w.1 * v.2 ≤ w.2 * v.2 := Nat.mul_le_mul_right _ h'
    have h3 : v.1 * w.2 = w.1 * v.2 := h
    rw [h3, Nat.mul_comm v.2 w.2] at h1
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 h2)

theorem left_transfer {v w : ℕ × ℕ} (hw : 0 < w.2) (h : ProjEq v w)
    (hl : v.1 < v.2) : w.1 < w.2 := by
  rcases Nat.lt_or_ge w.1 w.2 with h' | h'
  · exact h'
  · exfalso
    have h1 : v.1 * w.2 < v.2 * w.2 := Nat.mul_lt_mul_of_pos_right hl hw
    have h2 : w.2 * v.2 ≤ w.1 * v.2 := Nat.mul_le_mul_right _ h'
    have h3 : v.1 * w.2 = w.1 * v.2 := h
    rw [h3, Nat.mul_comm v.2 w.2] at h1
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 h2)

/-- **Definition 27.1, well-definedness.** The chamber is a property of the
    ratio, not of the column presenting it: projectively equal columns with
    positive tails lie in the same chamber. -/
theorem chamber_projEq {v w : ℕ × ℕ} (hv : 0 < v.2) (hw : 0 < w.2) (h : ProjEq v w) :
    chamber v = chamber w := by
  rcases Nat.lt_trichotomy v.2 v.1 with h' | h' | h'
  · rw [chamber_right h', chamber_right (right_transfer hw h h')]
  · rcases Nat.lt_trichotomy w.2 w.1 with k | k | k
    · exact absurd h' (Nat.ne_of_lt (right_transfer hv (projEq_symm h) k))
    · rw [chamber_membrane h'.symm, chamber_membrane k.symm]
    · exact absurd h'.symm (Nat.ne_of_lt (left_transfer hv (projEq_symm h) k))
  · rw [chamber_left h', chamber_left (left_transfer hw h h')]

/-- **Definition 27.1.** The projective maps are well defined on ratios:
    `advR` (the column form of `f_R(x) = 1 + 1/x`) respects `ProjEq`. -/
theorem advR_projEq {v w : ℕ × ℕ} (h : ProjEq v w) : ProjEq (advR v) (advR w) := by
  have h3 : v.1 * w.2 = w.1 * v.2 := h
  change (v.1 + v.2) * w.1 = (w.1 + w.2) * v.1
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm v.2 w.1, ← h3, Nat.mul_comm v.1 w.1,
    Nat.mul_comm w.2 v.1]

/-- `advL` (the column form of `f_L(x) = 1/(1+x)`) respects `ProjEq`. -/
theorem advL_projEq {v w : ℕ × ℕ} (h : ProjEq v w) : ProjEq (advL v) (advL w) := by
  have h3 : v.1 * w.2 = w.1 * v.2 := h
  change v.2 * (w.1 + w.2) = w.2 * (v.1 + v.2)
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm v.2 w.1, ← h3, Nat.mul_comm v.1 w.2,
    Nat.mul_comm v.2 w.2]

/-- Coordinate exchange respects `ProjEq`. -/
theorem swap_projEq {v w : ℕ × ℕ} (h : ProjEq v w) : ProjEq v.swap w.swap := by
  have h3 : v.1 * w.2 = w.1 * v.2 := h
  change v.2 * w.1 = w.2 * v.1
  rw [Nat.mul_comm v.2 w.1, ← h3, Nat.mul_comm]

/-! ## Theorem 27.2 — Exact chamber separation -/

/-- Parity on sides. -/
def Side.flip : Side → Side
  | .right => .left
  | .left => .right
  | .membrane => .membrane

theorem Side.flip_flip (s : Side) : s.flip.flip = s := by cases s <;> rfl

/-- **Theorem 27.2.** `f_R(x) > 1` for every positive ratio: the right advance
    lands in the right chamber whenever the tail is positive. -/
theorem advR_right (v : ℕ × ℕ) (hq : 0 < v.2) : chamber (advR v) = .right :=
  chamber_right (Nat.lt_add_of_pos_right hq)

/-- **Theorem 27.2.** `0 < f_L(x)`: the left advance has positive head
    whenever the tail is positive, since `(advL v).1 = v.2`. -/
theorem advL_pos (v : ℕ × ℕ) (hq : 0 < v.2) : 0 < (advL v).1 := hq

/-- **Theorem 27.2.** `f_L(x) < 1`: the left advance lands in the left
    chamber whenever the head is positive. With `advL_pos`, `0 < f_L(x) < 1`. -/
theorem advL_left (v : ℕ × ℕ) (hp : 0 < v.1) : chamber (advL v) = .left := by
  apply chamber_left
  change v.2 < v.1 + v.2
  rw [Nat.add_comm]; exact Nat.lt_add_of_pos_right hp

/-- **Theorem 27.2.** Parity `x ↦ x⁻¹` is coordinate exchange: it exchanges the
    two chambers and fixes the membrane. -/
theorem chamber_swap (v : ℕ × ℕ) : chamber v.swap = (chamber v).flip := by
  rcases Nat.lt_trichotomy v.2 v.1 with h | h | h
  · rw [chamber_right h, chamber_left (show v.swap.1 < v.swap.2 from h)]; rfl
  · rw [chamber_membrane h.symm, chamber_membrane (show v.swap.1 = v.swap.2 from h)]; rfl
  · rw [chamber_left h, chamber_right (show v.swap.2 < v.swap.1 from h)]; rfl

/-- **Theorem 27.2.** Exchange "fixes exactly `p = q`": a column is projectively
    fixed by parity iff it lies on the membrane. -/
theorem projEq_swap_iff (v : ℕ × ℕ) : ProjEq v v.swap ↔ v.1 = v.2 := by
  change v.1 * v.1 = v.2 * v.2 ↔ v.1 = v.2
  exact Nat.mul_self_inj

/-- **Theorem 27.2.** The membrane is a separator, not a stationary state: no
    positive membrane column is projectively fixed by either advance. -/
theorem membrane_not_fixed (v : ℕ × ℕ) (hq : 0 < v.2) (hm : v.1 = v.2) :
    ¬ ProjEq (advR v) v ∧ ¬ ProjEq (advL v) v := by
  have hp : 0 < v.1 := hm ▸ hq
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := chamber_projEq (show 0 < (advR v).2 from hp) hq h
    rw [advR_right v hq, chamber_membrane hm] at this
    exact absurd this (by decide)
  · have := chamber_projEq (show 0 < (advL v).2 from Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _)) hq h
    rw [advL_left v hp, chamber_membrane hm] at this
    exact absurd this (by decide)

/-- The book's witnesses: `f_R(1) = 2`, `f_L(1) = 1/2`. -/
theorem membrane_moves : advR (1, 1) = (2, 1) ∧ advL (1, 1) = (1, 2) := ⟨rfl, rfl⟩

/-! ## Theorem 27.3 — The two exact golden projective ridges

    Columns over `ℤ[φ]`. The advances are the same formulas. -/

/-- Right advance on a `ℤ[φ]` column. -/
def zadvR (v : Zphi × Zphi) : Zphi × Zphi := (v.1 + v.2, v.1)

/-- Left advance on a `ℤ[φ]` column. -/
def zadvL (v : Zphi × Zphi) : Zphi × Zphi := (v.2, v.1 + v.2)

/-- Projective equality of `ℤ[φ]` columns. -/
def ZProjEq (v w : Zphi × Zphi) : Prop := v.1 * w.2 = w.1 * v.2

/-- **Theorem 27.3.** `(φ, 1)` is projectively fixed by the right advance. -/
theorem ridgeR_fixed : ZProjEq (zadvR (phi, 1)) (phi, 1) := by unfold ZProjEq; decide

/-- **Theorem 27.3.** `(φ⁻¹, 1)` is projectively fixed by the left advance. -/
theorem ridgeL_fixed : ZProjEq (zadvL (phiInv, 1)) (phiInv, 1) := by unfold ZProjEq; decide

/-- **Theorem 27.3.** Parity exchanges the ridges: the exchanged column `(1, φ)`
    presents the same ratio as `(φ⁻¹, 1)`; and `φ⁻¹ = φ − 1` in `ℤ[φ]`. -/
theorem ridges_exchanged :
    ZProjEq (phi, 1).swap (phiInv, 1) ∧ phi * phiInv = 1 ∧ phiInv = phi - 1 :=
  ⟨by unfold ZProjEq; decide, by decide, by decide⟩

/-- Parity conjugates the advances, over `ℤ[φ]`: `zadvL v = (zadvR v.swap).swap`. -/
theorem zadvL_mirror (v : Zphi × Zphi) : zadvL v = (zadvR v.swap).swap := by
  change (v.2, v.1 + v.2) = (v.2, v.2 + v.1)
  rw [add_comm]

/-- **Theorem 27.3, exchange in general.** Any column projectively fixed by the
    right advance has its exchanged column projectively fixed by the left one. -/
theorem fixedR_swap_fixedL (v : Zphi × Zphi) (h : ZProjEq (zadvR v) v) :
    ZProjEq (zadvL v.swap) v.swap := by
  have h3 : (v.1 + v.2) * v.2 = v.1 * v.1 := h
  change v.1 * v.1 = v.2 * (v.2 + v.1)
  rw [← h3]; ring

/-- The componentwise content of `x·x = x + 1`. -/
theorem ridgeR_components (a b : ℤ) (h : (⟨a, b⟩ : Zphi) * ⟨a, b⟩ = ⟨a, b⟩ + 1) :
    a * a + b * b = a + 1 ∧ b * (2 * a + b - 1) = 0 := by
  have ha : a * a + b * b = a + 1 := congrArg Zphi.a h
  have hb : a * b + b * a + b * b = b + 0 := congrArg Zphi.b h
  refine ⟨ha, ?_⟩
  have e : b * (2 * a + b - 1) = (a * b + b * a + b * b) - (b + 0) := by ring
  rw [e, hb, Int.sub_self]

/-- `a² = a + 1` has no integer solution: it would give `(2a − 1)² = 5·1·1`. -/
theorem no_int_root_R (a : ℤ) (h : a * a = a + 1) : False := by
  have e : (2 * a - 1) * (2 * a - 1) = ((5 : ℕ) : ℤ) * 1 * 1 := by
    have : (2 * a - 1) * (2 * a - 1) = 4 * (a * a) - 4 * a + 1 := by ring
    rw [this, h]; push_cast; ring
  exact absurd (Zsqrtd.divides_sq_eq_zero_z e).2 (by decide)

/-- `a² + a = 1` has no integer solution: it would give `(2a + 1)² = 5·1·1`. -/
theorem no_int_root_L (a : ℤ) (h : a * a + a = 1) : False := by
  have e : (2 * a + 1) * (2 * a + 1) = ((5 : ℕ) : ℤ) * 1 * 1 := by
    have : (2 * a + 1) * (2 * a + 1) = 4 * (a * a + a) + 1 := by ring
    rw [this, h]; rfl
  exact absurd (Zsqrtd.divides_sq_eq_zero_z e).2 (by decide)

/-- **Theorem 27.3, uniqueness (right).** The only positive `x ∈ ℤ[φ]` with
    `x² = x + 1` is `φ`. The other root `1 − φ` is excluded by the exact order. -/
theorem ridgeR_unique (x : Zphi) (hx : 0 < x) (h : x * x = x + 1) : x = phi := by
  obtain ⟨a, b⟩ := x
  obtain ⟨ha, hb⟩ := ridgeR_components a b h
  rcases Int.mul_eq_zero.mp hb with h0 | h1
  · subst h0
    exact (no_int_root_R a (by have := ha; rw [Int.mul_zero, Int.add_zero] at this; exact this)).elim
  · have hb' : b = 1 - 2 * a := by omega
    subst hb'
    have key : 5 * (a * (a - 1)) = (a * a + (1 - 2 * a) * (1 - 2 * a)) - (a + 1) := by ring
    rw [ha, Int.sub_self] at key
    have hz : a * (a - 1) = 0 := by omega
    rcases Int.mul_eq_zero.mp hz with ha0 | ha1
    · subst ha0; rfl
    · have : a = 1 := by omega
      subst this
      exact absurd hx (by decide)

/-- **Theorem 27.3, uniqueness (left).** The only positive `x ∈ ℤ[φ]` with
    `x² + x = 1` is `φ⁻¹`. The other root `−φ` is excluded by the exact order. -/
theorem ridgeL_unique (x : Zphi) (hx : 0 < x) (h : x * x + x = 1) : x = phiInv := by
  obtain ⟨a, b⟩ := x
  have ha : a * a + b * b + a = 1 := congrArg Zphi.a h
  have hb0 : a * b + b * a + b * b + b = 0 := congrArg Zphi.b h
  have hb : b * (2 * a + b + 1) = 0 := by
    have e : b * (2 * a + b + 1) = a * b + b * a + b * b + b := by ring
    rw [e, hb0]
  rcases Int.mul_eq_zero.mp hb with h0 | h1
  · subst h0
    exact (no_int_root_L a (by have := ha; rw [Int.mul_zero, Int.add_zero] at this; exact this)).elim
  · have hb' : b = -1 - 2 * a := by omega
    subst hb'
    have key : 5 * (a * (a + 1)) = (a * a + (-1 - 2 * a) * (-1 - 2 * a) + a) - 1 := by ring
    rw [ha, Int.sub_self] at key
    have hz : a * (a + 1) = 0 := by omega
    rcases Int.mul_eq_zero.mp hz with ha0 | ha1
    · subst ha0
      exact absurd hx (by decide)
    · have : a = -1 := by omega
      subst this
      rfl

/-- A fixed column `(x, 1)` of the right advance is exactly a root of `x² = x + 1`. -/
theorem fixedR_iff (x : Zphi) : ZProjEq (zadvR (x, 1)) (x, 1) ↔ x * x = x + 1 := by
  change (x + 1) * 1 = x * x ↔ _
  rw [mul_one]; exact ⟨Eq.symm, Eq.symm⟩

/-- A fixed column `(x, 1)` of the left advance is exactly a root of `x² + x = 1`. -/
theorem fixedL_iff (x : Zphi) : ZProjEq (zadvL (x, 1)) (x, 1) ↔ x * x + x = 1 := by
  change 1 * 1 = x * (x + 1) ↔ _
  rw [mul_one, mul_add, mul_one]; exact ⟨Eq.symm, Eq.symm⟩

/-- **Theorem 27.3, uniqueness on the ratio (right).** Every positive column
    `(a, b)` of `ℤ[φ]` projectively fixed by the right advance presents the ratio
    of `(φ, 1)`. Through `(a − bφ)(a + bφ⁻¹) = a² − ab − b²`; the second factor
    is positive. At `b = 1` this is `ridgeR_unique` read through `fixedR_iff`
    (projectively fixed at `(x, 1)` iff `x` solves the fixed-point equation). -/
theorem ridgeR_unique_proj (v : Zphi × Zphi) (h1 : 0 < v.1) (h2 : 0 < v.2)
    (h : ZProjEq (zadvR v) v) : ZProjEq v (phi, 1) := by
  obtain ⟨a, b⟩ := v
  have h3 : (a + b) * b = a * a := h
  have hf : (a - phi * b) * (a + phiInv * b) = 0 := by
    rw [phiInv_eq_phi_sub_one]
    calc (a - phi * b) * (a + (phi - 1) * b) = a * a - a * b - (phi * phi - phi) * (b * b) := by ring
      _ = 0 := by rw [phi_sq, ← h3]; ring
  change a * 1 = phi * b
  rw [mul_one]
  rcases mul_eq_zero_split hf with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 (ne_of_gt (add_pos h1 (Zphi.mul_pos _ _ phiInv_pos h2)))

/-- **Theorem 27.3, uniqueness on the ratio (left).** Every positive column
    `(a, b)` of `ℤ[φ]` projectively fixed by the left advance presents the ratio
    of `(φ⁻¹, 1)`. Through `(a − bφ⁻¹)(a + bφ) = a² + ab − b²`; the second factor
    is positive. At `b = 1` this is `ridgeL_unique` read through `fixedL_iff`
    (projectively fixed at `(x, 1)` iff `x` solves the fixed-point equation). -/
theorem ridgeL_unique_proj (v : Zphi × Zphi) (h1 : 0 < v.1) (h2 : 0 < v.2)
    (h : ZProjEq (zadvL v) v) : ZProjEq v (phiInv, 1) := by
  obtain ⟨a, b⟩ := v
  have h3 : b * b = a * (a + b) := h
  have hf : (a - phiInv * b) * (a + phi * b) = 0 := by
    rw [phiInv_eq_phi_sub_one]
    calc (a - (phi - 1) * b) * (a + phi * b) = a * a + a * b - (phi * phi - phi) * (b * b) := by ring
      _ = 0 := by rw [phi_sq, h3]; ring
  change a * 1 = phiInv * b
  rw [mul_one]
  rcases mul_eq_zero_split hf with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 (ne_of_gt (add_pos h1 (Zphi.mul_pos _ _ (by decide : (0 : Zphi) < phi) h2)))

/-- A rational column, read inside `ℤ[φ]`. -/
def ratCol (v : ℕ × ℕ) : Zphi × Zphi := (⟨v.1, 0⟩, ⟨v.2, 0⟩)

/-- **Theorem 27.3, closing sentence.** The ridges are not rational substrate
    presentations: no column with positive tail is projectively equal to `(φ, 1)`
    or to `(φ⁻¹, 1)`. The `φ`-component forces the tail to vanish. -/
theorem ridges_not_rational (v : ℕ × ℕ) (hq : 0 < v.2) :
    ¬ ZProjEq (ratCol v) (phi, 1) ∧ ¬ ZProjEq (ratCol v) (phiInv, 1) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hb : (v.1 : ℤ) * 0 + 0 * 1 + 0 * 0 = 0 * 0 + 1 * (v.2 : ℤ) + 1 * 0 :=
      congrArg Zphi.b h
    omega
  · have hb : (v.1 : ℤ) * 0 + 0 * 1 + 0 * 0 = -1 * 0 + 1 * (v.2 : ℤ) + 1 * 0 :=
      congrArg Zphi.b h
    omega

/-! ## Corollary 27.4 — Exact attraction with alternating side

    The book's "converges" is the shadow of the exact statements below. -/

/-- The conserved quadratic form `N(p,q) = p² − pq − q²`. -/
def N (p q : ℤ) : ℤ := p * p - p * q - q * q

/-- `N` of a natural column. -/
def Nc (v : ℕ × ℕ) : ℤ := N v.1 v.2

/-- **Corollary 27.4.** One right advance negates `N`. -/
theorem Nc_advR (v : ℕ × ℕ) : Nc (advR v) = - Nc v := by
  change N (((v.1 + v.2 : ℕ)) : ℤ) (v.1 : ℤ) = - N v.1 v.2
  rw [Int.natCast_add]; unfold N; ring

/-- Along the right trajectory, `N = (−1)ⁿ N(v)`. -/
theorem Nc_trajR (v : ℕ × ℕ) : ∀ n, Nc (trajR v n) = (-1) ^ n * Nc v
  | 0 => by rw [pow_zero, Int.one_mul]; rfl
  | n + 1 => by
    change Nc (advR (trajR v n)) = _
    rw [Nc_advR, Nc_trajR v n, pow_succ]; ring

/-- **`N` never vanishes on a positive tail.** `4N = (2p − q)² − 5q²`, and `5` is
    not a square. -/
theorem N_ne_zero (p q : ℤ) (hq : q ≠ 0) : N p q ≠ 0 := by
  intro h
  have e : (2 * p - q) * (2 * p - q) = ((5 : ℕ) : ℤ) * q * q := by
    have : (2 * p - q) * (2 * p - q) = 4 * N p q + 5 * q * q := by unfold N; ring
    rw [this, h]; push_cast; ring
  exact hq (Zsqrtd.divides_sq_eq_zero_z e).2

/-- The right ridge defect `p − qφ ∈ ℤ[φ]`: positive exactly when `p/q` lies
    above `φ`. -/
def defectR (v : ℕ × ℕ) : Zphi := ⟨v.1, -(v.2 : ℤ)⟩

/-- **The bridge.** `p − qφ > 0` in `ℤ[φ]` iff `N(p,q) > 0`. The order is decided
    through `ℤ√5`: the image of `p − qφ` is `(2p − q) − q√5`, and
    `4N = (2p − q)² − 5q²`. -/
theorem bridge (p q : ℕ) : (0 : Zphi) < ⟨p, -(q : ℤ)⟩ ↔ 0 < N p q := by
  rw [lt_def]
  change ¬ Zsqrtd.Nonnegg 5 1 (2 * (0 : Zphi).a + (0 : Zphi).b + -(2 * (p : ℤ) + -(q : ℤ)))
      ((0 : Zphi).b + -(-(q : ℤ))) ↔ _
  have h4 : 4 * N p q = (2 * (p : ℤ) - q) * (2 * (p : ℤ) - q) - 5 * ((q : ℤ) * q) := by
    unfold N; ring
  have him : (0 : Zphi).b + -(-(q : ℤ)) = ((q : ℕ) : ℤ) := by
    change (0 : ℤ) + _ = _; ring
  rcases Nat.lt_or_ge (p + p) q with hlt | hge
  · -- `2p < q`: the image has both components nonnegative, so it is not positive;
    -- and `(2p − q)² < q² ≤ 5q²`, so `N < 0`.
    obtain ⟨m, hm⟩ : ∃ m, q = p + p + m := ⟨q - (p + p), by omega⟩
    have hre : 2 * (0 : Zphi).a + (0 : Zphi).b + -(2 * (p : ℤ) + -(q : ℤ)) = ((m : ℕ) : ℤ) := by
      change 2 * (0 : ℤ) + 0 + _ = _; rw [hm]; push_cast; ring
    rw [hre, him]
    refine ⟨fun h => absurd trivial h, fun h => ?_⟩
    exfalso
    have hmq : m * m ≤ q * q := Nat.mul_self_le_mul_self (by omega)
    have hmz : ((m : ℤ)) * m ≤ (q : ℤ) * q := by
      rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Int.ofNat_le.mpr hmq
    have hsq : (2 * (p : ℤ) - q) * (2 * (p : ℤ) - q) = (m : ℤ) * m := by
      rw [hm]; push_cast; ring
    rw [hsq] at h4
    have hq0 : (0 : ℤ) ≤ (q : ℤ) * q := by
      rw [← Int.natCast_mul]; exact Int.natCast_nonneg _
    generalize (m : ℤ) * m = u at h4 hmz
    generalize (q : ℤ) * q = w at h4 hmz hq0
    omega
  · -- `q ≤ 2p`: the image is `(m, −q)` with `m = 2p − q ≥ 0`, positive iff `5q² < m²`.
    obtain ⟨m, hm⟩ : ∃ m, p + p = q + m := ⟨p + p - q, by omega⟩
    have hre : 2 * (0 : Zphi).a + (0 : Zphi).b + -(2 * (p : ℤ) + -(q : ℤ)) = -((m : ℕ) : ℤ) := by
      have hmz : ((p : ℤ) + p) = q + m := by
        rw [← Int.natCast_add, ← Int.natCast_add, hm]
      change 2 * (0 : ℤ) + 0 + _ = _; omega
    rw [hre, him, Zsqrtd.nonnegg_neg_pos]
    unfold Zsqrtd.SqLe
    have hsq : (2 * (p : ℤ) - q) * (2 * (p : ℤ) - q) = (m : ℤ) * m := by
      have hmz : ((p : ℤ) + p) = q + m := by
        rw [← Int.natCast_add, ← Int.natCast_add, hm]
      have : 2 * (p : ℤ) - q = m := by omega
      rw [this]
    rw [hsq] at h4
    have hc : (1 * m * m ≤ 5 * q * q) ↔ ((m : ℤ) * m ≤ 5 * ((q : ℤ) * q)) := by
      rw [Nat.one_mul, Nat.mul_assoc, ← Int.ofNat_le, Int.natCast_mul, Int.natCast_mul,
        Int.natCast_mul]
      exact Iff.rfl
    rw [hc]
    generalize (m : ℤ) * m = u at h4
    generalize (q : ℤ) * q = w at h4
    constructor
    · intro h
      rcases Int.lt_or_le (5 * w) u with k | k
      · omega
      · exact absurd k h
    · intro h hle
      omega

/-- Below the ridge: `p − qφ < 0` iff `N(p,q) < 0`, for a positive tail. -/
theorem bridge_neg (p q : ℕ) (hq : 0 < q) : (⟨p, -(q : ℤ)⟩ : Zphi) < 0 ↔ N p q < 0 := by
  have hN := N_ne_zero p q (by omega)
  constructor
  · intro h
    rcases Int.lt_trichotomy (N p q) 0 with k | k | k
    · exact k
    · exact absurd k hN
    · exact absurd ((bridge p q).mpr k) (lt_asymm h)
  · intro h
    rcases lt_trichotomy (⟨p, -(q : ℤ)⟩ : Zphi) 0 with k | k | k
    · exact k
    · exfalso
      have hb : -(q : ℤ) = 0 := congrArg Zphi.b k
      omega
    · exfalso
      have := (bridge p q).mp k
      omega

/-- **Corollary 27.4, strict side alternation, for every positive start** (the
    book proves it only for the `1:1` orbit and defers to §29). Each right advance
    carries a column strictly across the ridge `φ`. -/
theorem alternation_R (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) (n : ℕ) :
    (0 : Zphi) < defectR (trajR v n) ↔ defectR (trajR v (n + 1)) < 0 := by
  have hpos := trajR_pos v hv (n + 1)
  unfold defectR
  rw [bridge, bridge_neg _ _ hpos.2]
  change 0 < Nc (trajR v n) ↔ Nc (advR (trajR v n)) < 0
  rw [Nc_advR]
  exact ⟨fun h => by omega, fun h => by omega⟩

/-- **The exact contraction.** One right advance multiplies the ridge defect by
    exactly `−φ⁻¹`: `(p + q) − pφ = (1 − φ)(p − qφ)`. -/
theorem defectR_advR (v : ℕ × ℕ) : defectR (advR v) = (-phiInv) * defectR v := by
  apply Zphi.ext
  · change (((v.1 + v.2 : ℕ)) : ℤ) = -(-1) * (v.1 : ℤ) + -(1 : ℤ) * -(v.2 : ℤ)
    rw [Int.natCast_add]; ring
  · change -((v.1 : ℕ) : ℤ) = -(-1) * -(v.2 : ℤ) + -(1 : ℤ) * (v.1 : ℤ) + -(1 : ℤ) * -(v.2 : ℤ)
    ring

/-- **Corollary 27.4, exact form of "converges to φ".** After `n` right advances
    the ridge defect is `(−1)ⁿ φ⁻ⁿ` times the initial one. With `φ⁻ⁿ > 0` strictly
    decreasing (`PhiPos.phiNegPow_pos`, `PhiPos.phiNegPow_strict`), this is the
    integer statement whose shadow is the limit. -/
theorem defectR_trajR (v : ℕ × ℕ) :
    ∀ n, defectR (trajR v n) = (-1) ^ n * phiNegPow n * defectR v
  | 0 => by change defectR v = 1 * 1 * defectR v; rw [one_mul, one_mul]
  | n + 1 => by
    change defectR (advR (trajR v n)) = _
    rw [defectR_advR, defectR_trajR v n]
    unfold phiNegPow
    rw [pow_succ, pow_succ]; ring

/-- **Corollary 27.4, the contraction gathered.** For every `n`: the defect after
    `n` right advances is `(−1)ⁿφ⁻ⁿ` times the initial one, the scale `φ⁻ⁿ` is
    positive, and the next scale is strictly smaller. This, and not a limit, is
    what the book's "converges to φ" carries. -/
theorem contraction_R (v : ℕ × ℕ) (n : ℕ) :
    defectR (trajR v n) = (-1) ^ n * phiNegPow n * defectR v ∧
    0 < phiNegPow n ∧ phiNegPow (n + 1) < phiNegPow n :=
  ⟨defectR_trajR v n, PhiPos.phiNegPow_pos n, PhiPos.phiNegPow_strict (Nat.lt_succ_self n)⟩

/-- The left ridge defect `p − qφ⁻¹ = (p + q) − qφ ∈ ℤ[φ]`. -/
def defectL (v : ℕ × ℕ) : Zphi := ⟨v.1 + v.2, -(v.2 : ℤ)⟩

/-- `p − qφ⁻¹ > 0` iff `N(q, p) < 0`: the left bridge is the right bridge at
    `(p + q, q)`, since `N(p + q, q) = −N(q, p)`. -/
theorem bridgeL (v : ℕ × ℕ) : (0 : Zphi) < defectL v ↔ Nc v.swap < 0 := by
  have h := bridge (v.1 + v.2) v.2
  rw [Int.natCast_add] at h
  unfold defectL
  rw [h]
  have e : N ((v.1 : ℤ) + v.2) v.2 = - Nc v.swap := by
    change _ = - N v.2 v.1; unfold N; ring
  rw [e]; exact ⟨fun h => by omega, fun h => by omega⟩

/-- One left advance multiplies the left defect by the same `−φ⁻¹`. -/
theorem defectL_advL (v : ℕ × ℕ) : defectL (advL v) = (-phiInv) * defectL v := by
  apply Zphi.ext
  · change (v.2 : ℤ) + (((v.1 + v.2 : ℕ)) : ℤ) =
      -(-1) * ((v.1 : ℤ) + v.2) + -(1 : ℤ) * -(v.2 : ℤ)
    rw [Int.natCast_add]; ring
  · change -(((v.1 + v.2 : ℕ)) : ℤ) =
      -(-1) * -(v.2 : ℤ) + -(1 : ℤ) * ((v.1 : ℤ) + v.2) + -(1 : ℤ) * -(v.2 : ℤ)
    rw [Int.natCast_add]; ring

/-- **Corollary 27.4, left.** After `n` left advances the left defect is
    `(−1)ⁿ φ⁻ⁿ` times the initial one. -/
theorem defectL_trajL (v : ℕ × ℕ) :
    ∀ n, defectL (trajL v n) = (-1) ^ n * phiNegPow n * defectL v
  | 0 => by change defectL v = 1 * 1 * defectL v; rw [one_mul, one_mul]
  | n + 1 => by
    change defectL (advL (trajL v n)) = _
    rw [defectL_advL, defectL_trajL v n]
    unfold phiNegPow
    rw [pow_succ, pow_succ]; ring

/-- **Corollary 27.4, left alternation, for every positive start**, via
    `trajL_mirror`: the exchanged left trajectory is the right one. -/
theorem alternation_L (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) (n : ℕ) :
    (0 : Zphi) < defectL (trajL v n) ↔ ¬ (0 : Zphi) < defectL (trajL v (n + 1)) := by
  rw [bridgeL, bridgeL, trajL_mirror, trajL_mirror, Prod.swap_swap, Prod.swap_swap]
  change Nc (trajR v.swap n) < 0 ↔ ¬ Nc (advR (trajR v.swap n)) < 0
  have hpos := trajR_pos v.swap ⟨hv.2, hv.1⟩ n
  have hN := N_ne_zero (trajR v.swap n).1 (trajR v.swap n).2
    (by omega)
  rw [Nc_advR]
  change N _ _ < 0 ↔ ¬ -N _ _ < 0
  exact ⟨fun h h' => by omega, fun h => by
    rcases Int.lt_trichotomy (N (trajR v.swap n).1 (trajR v.swap n).2) 0 with k | k | k
    · exact k
    · exact absurd k hN
    · exact absurd (by omega) h⟩

/-- An order fact in `ℤ[φ]` read off integers: `x ≤ y` when the image of `y − x`
    in `ℤ√5`, `u + w√5` with `u = 2(y.a − x.a) + (y.b − x.b)`, `w = y.b − x.b`,
    has `u ≥ 0` and, if `w < 0`, `5w² ≤ u²`. -/
theorem le_of_int {x y : Zphi} (h1 : 0 ≤ 2 * (y.a - x.a) + (y.b - x.b))
    (h2 : y.b - x.b < 0 →
      5 * ((y.b - x.b) * (y.b - x.b)) ≤ (2 * (y.a - x.a) + (y.b - x.b)) * (2 * (y.a - x.a) + (y.b - x.b))) :
    x ≤ y := by
  rw [le_def]
  change Zsqrtd.Nonnegg 5 1 (2 * y.a + y.b + -(2 * x.a + x.b)) (y.b + -x.b)
  have e1 : 2 * y.a + y.b + -(2 * x.a + x.b) = 2 * (y.a - x.a) + (y.b - x.b) := by ring
  have e2 : y.b + -x.b = y.b - x.b := by ring
  rw [e1, e2]
  generalize 2 * (y.a - x.a) + (y.b - x.b) = u at h1 h2
  generalize y.b - x.b = w at h2
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h1
  rcases w with k | k
  · trivial
  · have h := h2 (Int.negSucc_lt_zero k)
    change Zsqrtd.SqLe (k + 1) 5 m 1
    unfold Zsqrtd.SqLe
    have hk : Int.negSucc k * Int.negSucc k = ((k + 1 : ℕ) : ℤ) * ((k + 1 : ℕ) : ℤ) := by
      rw [Int.negSucc_eq]; push_cast; ring
    rw [hk] at h
    have e5 : ((5 * (k + 1) * (k + 1) : ℕ) : ℤ) = 5 * (((k + 1 : ℕ) : ℤ) * ((k + 1 : ℕ) : ℤ)) := by
      push_cast; ring
    have em : ((1 * m * m : ℕ) : ℤ) = (m : ℤ) * (m : ℤ) := by push_cast; ring
    exact Int.ofNat_le.mp (by rw [e5, em]; exact h)

/-- Integers sit in `ℤ[φ]` in order. -/
theorem int_le {j k : ℤ} (h : j ≤ k) : (⟨j, 0⟩ : Zphi) ≤ ⟨k, 0⟩ :=
  le_of_int (by change 0 ≤ 2 * (k - j) + (0 - 0); omega) (fun h' => absurd h' (by change ¬ (0 : ℤ) - 0 < 0; omega))

/-- Non-strict monotonicity of multiplication by a nonnegative element, from the
    strict instance field (no generic ordered-semiring route). -/
theorem zphi_mul_le_mul_right {x y z : Zphi} (h : x ≤ y) (hz : 0 ≤ z) : x * z ≤ y * z := by
  rcases Decidable.lt_or_eq_of_le hz with hz | hz
  · rcases Decidable.lt_or_eq_of_le h with h | h
    · exact le_of_lt (mul_lt_mul_of_pos_right h hz)
    · rw [h]
  · rw [← hz, mul_zero, mul_zero]

/-- The right ridge defect times `p + qφ⁻¹ = (p − q) + qφ` is `N(p,q)`. -/
theorem defectR_mul_conj (v : ℕ × ℕ) :
    defectR v * ⟨(v.1 : ℤ) - v.2, v.2⟩ = ⟨Nc v, 0⟩ := by
  apply Zphi.ext
  · change (v.1 : ℤ) * ((v.1 : ℤ) - v.2) + -(v.2 : ℤ) * v.2 = N v.1 v.2
    unfold N; ring
  · change (v.1 : ℤ) * v.2 + -(v.2 : ℤ) * ((v.1 : ℤ) - v.2) + -(v.2 : ℤ) * v.2 = 0
    ring

/-- `5d² ≤ u²` from `3|d| ≤ u`, for negative `d`, by integers. -/
theorem sq_bound {u d : ℤ} (hd : d < 0) (hu : 3 * -d ≤ u) : 5 * (d * d) ≤ u * u := by
  have h := Int.mul_le_mul hu hu (by omega) (by omega)
  have e : 3 * -d * (3 * -d) = 9 * (d * d) := by ring
  have hn : 0 ≤ d * d := by
    have : d * d = -d * -d := by ring
    rw [this]; exact Int.mul_nonneg (by omega) (by omega)
  rw [e] at h
  generalize d * d = s at h hn
  generalize u * u = t at h
  omega

/-- Every integer lies between `−t` and `t` for some natural `t`. -/
theorem int_bound (x : ℤ) : ∃ t : ℕ, x ≤ t ∧ -x ≤ t := by
  rcases x with n | n
  · exact ⟨n, Int.le_refl _, by change -(n : ℤ) ≤ n; omega⟩
  · exact ⟨n + 1, by rw [Int.negSucc_eq]; omega, by rw [Int.negSucc_eq]; push_cast; omega⟩

/-- **`ℤ[φ]` is archimedean over the naturals**, from integers: for `ε > 0` and any
    natural `c` there is a natural `m` with `c < εm`. The conjugate
    `ε' = (a + b) − bφ` has `εε' = a² + ab − b² = N(a + b, b)`, a nonzero integer,
    and `−T < ε' < T` for `T = s + 2t + 1` with `|a + b| ≤ s`, `|b| ≤ t`;
    so `εT > ε·(±ε') ≥ 1`. -/
theorem archimedean (ε : Zphi) (hε : 0 < ε) (c : ℕ) :
    ∃ m : ℕ, (⟨c, 0⟩ : Zphi) < ε * ⟨m, 0⟩ := by
  obtain ⟨a, b⟩ := ε
  obtain ⟨s, hs1, hs2⟩ := int_bound (a + b)
  obtain ⟨t, ht1, ht2⟩ := int_bound b
  have hK : (⟨a, b⟩ : Zphi) * ⟨a + b, -b⟩ = ⟨N (a + b) b, 0⟩ := by
    apply Zphi.ext
    · change a * (a + b) + b * -b = N (a + b) b; unfold N; ring
    · change a * -b + b * (a + b) + b * -b = 0; ring
  have hKne : N (a + b) b ≠ 0 := by
    by_cases hb : b = 0
    · subst hb
      intro h0
      have ha : a * a = 0 := by unfold N at h0; rw [← h0]; ring
      have ha0 : a = 0 := by
        rcases Int.mul_eq_zero.mp ha with h | h <;> exact h
      subst ha0; exact lt_irrefl _ hε
    · exact N_ne_zero (a + b) b hb
  have hup : (⟨a + b, -b⟩ : Zphi) < ⟨((s + 2 * t + 1 : ℕ) : ℤ), 0⟩ := by
    refine lt_of_le_of_ne (le_of_int ?_ ?_) ?_
    · change 0 ≤ 2 * (((s + 2 * t + 1 : ℕ) : ℤ) - (a + b)) + (0 - -b); push_cast; omega
    · intro hw
      exact sq_bound hw (by push_cast; omega)
    · intro h
      have h1 : a + b = ((s + 2 * t + 1 : ℕ) : ℤ) := congrArg Zphi.a h
      have h2 : -b = 0 := congrArg Zphi.b h
      push_cast at h1; omega
  have hlo : -(⟨a + b, -b⟩ : Zphi) < ⟨((s + 2 * t + 1 : ℕ) : ℤ), 0⟩ := by
    refine lt_of_le_of_ne (le_of_int ?_ ?_) ?_
    · change 0 ≤ 2 * (((s + 2 * t + 1 : ℕ) : ℤ) - -(a + b)) + (0 - - -b); push_cast; omega
    · intro hw
      exact sq_bound hw (by push_cast; change 3 * -(0 - - -b) ≤ 2 * (_ - -(a + b)) + (0 - - -b); omega)
    · intro h
      have h1 : -(a + b) = ((s + 2 * t + 1 : ℕ) : ℤ) := congrArg Zphi.a h
      have h2 : - -b = 0 := congrArg Zphi.b h
      push_cast at h1; omega
  have hone : (1 : Zphi) < ⟨a, b⟩ * ⟨((s + 2 * t + 1 : ℕ) : ℤ), 0⟩ := by
    rcases lt_or_ge 0 (N (a + b) b) with hk | hk
    · have he : (0 : Zphi) < ⟨a + b, -b⟩ := by
        rcases lt_or_ge 0 (⟨a + b, -b⟩ : Zphi) with h | h
        · exact h
        · exfalso
          have h1 : (⟨a + b, -b⟩ : Zphi) * ⟨a, b⟩ ≤ 0 * ⟨a, b⟩ := zphi_mul_le_mul_right h (le_of_lt hε)
          rw [mul_comm, hK, zero_mul] at h1
          exact absurd (le_trans (int_le (show (1 : ℤ) ≤ N (a + b) b by omega)) h1) (by decide)
      calc (1 : Zphi) = ⟨1, 0⟩ := rfl
        _ ≤ ⟨N (a + b) b, 0⟩ := int_le (by omega)
        _ = ⟨a, b⟩ * ⟨a + b, -b⟩ := hK.symm
        _ < _ := mul_lt_mul_of_pos_left hup hε
    · have hk' : N (a + b) b < 0 := lt_of_le_of_ne hk hKne
      have he : (0 : Zphi) < -⟨a + b, -b⟩ := by
        rcases lt_or_ge 0 (-(⟨a + b, -b⟩ : Zphi)) with h | h
        · exact h
        · exfalso
          have h1 : -(⟨a + b, -b⟩ : Zphi) * ⟨a, b⟩ ≤ 0 * ⟨a, b⟩ := zphi_mul_le_mul_right h (le_of_lt hε)
          rw [mul_comm, mul_neg, hK, zero_mul] at h1
          exact absurd (le_trans (int_le (show (1 : ℤ) ≤ -N (a + b) b by omega)) h1) (by decide)
      calc (1 : Zphi) = ⟨1, 0⟩ := rfl
        _ ≤ ⟨-N (a + b) b, 0⟩ := int_le (by omega)
        _ = ⟨a, b⟩ * -⟨a + b, -b⟩ := by rw [mul_neg, hK]; rfl
        _ < _ := mul_lt_mul_of_pos_left hlo hε
  refine ⟨(c + 1) * (s + 2 * t + 1), ?_⟩
  have hsplit : (⟨a, b⟩ : Zphi) * ⟨(((c + 1) * (s + 2 * t + 1) : ℕ) : ℤ), 0⟩ =
      ⟨((c + 1 : ℕ) : ℤ), 0⟩ * (⟨a, b⟩ * ⟨((s + 2 * t + 1 : ℕ) : ℤ), 0⟩) := by
    apply Zphi.ext
    · change a * _ + b * 0 = ((c + 1 : ℕ) : ℤ) * (a * _ + b * 0) + 0 * (a * 0 + b * _ + b * 0)
      push_cast; ring
    · change a * 0 + b * _ + b * 0 = ((c + 1 : ℕ) : ℤ) * (a * 0 + b * _ + b * 0) + 0 * (a * _ + b * 0) + 0 * (a * 0 + b * _ + b * 0)
      push_cast; ring
  rw [hsplit]
  have hc1 : (0 : Zphi) < ⟨((c + 1 : ℕ) : ℤ), 0⟩ := by
    refine lt_of_le_of_ne (int_le (by omega)) ?_
    intro h; have h1 : (0 : ℤ) = ((c + 1 : ℕ) : ℤ) := congrArg Zphi.a h; omega
  calc (⟨c, 0⟩ : Zphi) < ⟨((c + 1 : ℕ) : ℤ), 0⟩ := by
        refine lt_of_le_of_ne (int_le (by omega)) ?_
        intro h; have h1 : (c : ℤ) = ((c + 1 : ℕ) : ℤ) := congrArg Zphi.a h; omega
    _ = ⟨((c + 1 : ℕ) : ℤ), 0⟩ * 1 := (mul_one _).symm
    _ < _ := mul_lt_mul_of_pos_left hone hc1

/-- The other half of reading order off integers: `x ≤ y` when
    `u = 2(y.a − x.a) + (y.b − x.b) ≤ 0`, `w = y.b − x.b ≥ 0` and `u² ≤ 5w²`. -/
theorem le_of_int' {x y : Zphi} (h1 : 2 * (y.a - x.a) + (y.b - x.b) ≤ 0) (h2 : 0 ≤ y.b - x.b)
    (h3 : (2 * (y.a - x.a) + (y.b - x.b)) * (2 * (y.a - x.a) + (y.b - x.b)) ≤
      5 * ((y.b - x.b) * (y.b - x.b))) :
    x ≤ y := by
  rw [le_def]
  change Zsqrtd.Nonnegg 5 1 (2 * y.a + y.b + -(2 * x.a + x.b)) (y.b + -x.b)
  have e1 : 2 * y.a + y.b + -(2 * x.a + x.b) = 2 * (y.a - x.a) + (y.b - x.b) := by ring
  have e2 : y.b + -x.b = y.b - x.b := by ring
  rw [e1, e2]
  generalize 2 * (y.a - x.a) + (y.b - x.b) = u at h1 h3
  generalize y.b - x.b = w at h2 h3
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le h2
  rcases u with k | k
  · trivial
  · change Zsqrtd.SqLe (k + 1) 1 j 5
    unfold Zsqrtd.SqLe
    have hk : Int.negSucc k * Int.negSucc k = ((k + 1 : ℕ) : ℤ) * ((k + 1 : ℕ) : ℤ) := by
      rw [Int.negSucc_eq]; push_cast; ring
    rw [hk] at h3
    have e5 : ((1 * (k + 1) * (k + 1) : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) * ((k + 1 : ℕ) : ℤ) := by
      push_cast; ring
    have ej : ((5 * j * j : ℕ) : ℤ) = 5 * ((j : ℤ) * (j : ℤ)) := by push_cast; ring
    exact Int.ofNat_le.mp (by rw [e5, ej]; exact h3)

/-- After `n` right advances from a positive start, the head is at least `n + 1`. -/
theorem trajR_fst_ge (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) : ∀ n, n + 1 ≤ (trajR v n).1
  | 0 => hv.1
  | n + 1 => by
    have ih := trajR_fst_ge v hv n
    have hq := (trajR_pos v hv n).2
    change n + 1 + 1 ≤ (trajR v n).1 + (trajR v n).2
    omega

/-- `p + qφ⁻¹ = (p − q) + qφ` is at least `p`. -/
theorem conj_ge (v : ℕ × ℕ) : (⟨v.1, 0⟩ : Zphi) ≤ ⟨(v.1 : ℤ) - v.2, v.2⟩ :=
  le_of_int' (by change 2 * ((v.1 : ℤ) - v.2 - v.1) + ((v.2 : ℤ) - 0) ≤ 0; omega)
    (by change 0 ≤ (v.2 : ℤ) - 0; omega)
    (by
      change (2 * ((v.1 : ℤ) - v.2 - v.1) + ((v.2 : ℤ) - 0)) * (2 * ((v.1 : ℤ) - v.2 - v.1) + ((v.2 : ℤ) - 0)) ≤
        5 * (((v.2 : ℤ) - 0) * ((v.2 : ℤ) - 0))
      have e : (2 * ((v.1 : ℤ) - v.2 - v.1) + ((v.2 : ℤ) - 0)) * (2 * ((v.1 : ℤ) - v.2 - v.1) + ((v.2 : ℤ) - 0)) =
          (v.2 : ℤ) * v.2 := by ring
      have e' : 5 * (((v.2 : ℤ) - 0) * ((v.2 : ℤ) - 0)) = 5 * ((v.2 : ℤ) * v.2) := by ring
      have hn : 0 ≤ (v.2 : ℤ) * v.2 := Int.mul_nonneg (by omega) (by omega)
      rw [e, e']; generalize (v.2 : ℤ) * v.2 = s at hn ⊢; omega)

/-- The bound behind "converges": if `x · P = k` with `k ≤ c < εm ≤ εP`, then `x < ε`. -/
theorem lt_of_mul_conj {x P ε : Zphi} {k c : ℤ} {m : ℕ} (hε : 0 < ε) (hx : x * P = ⟨k, 0⟩)
    (hk : k ≤ c) (hm : (⟨c, 0⟩ : Zphi) < ε * ⟨m, 0⟩) (hP : (⟨m, 0⟩ : Zphi) ≤ P) : x < ε := by
  rcases lt_or_ge x ε with h | h
  · exact h
  · exfalso
    have hP0 : (0 : Zphi) ≤ P := le_trans (int_le (Int.natCast_nonneg m)) hP
    have h1 : ε * P ≤ x * P := zphi_mul_le_mul_right h hP0
    have h2 : ε * ⟨m, 0⟩ ≤ ε * P := by
      rw [mul_comm ε, mul_comm ε]; exact zphi_mul_le_mul_right hP (le_of_lt hε)
    rw [hx] at h1
    exact lt_irrefl _ (lt_of_lt_of_le hm (le_trans h2 (le_trans h1 (int_le hk))))

/-- **Corollary 27.4, "converges to φ", as an order statement in `ℤ[φ]`.** For a
    positive start and any positive `ε ∈ ℤ[φ]`, from some advance on the ridge
    defect `p − qφ` lies strictly between `−ε` and `ε`. No limit and no real
    number: `ℤ[φ]`'s own order, decided from integers (`archimedean`,
    `defectR_mul_conj`, the conserved `|N|`). -/
theorem defectR_eventually_small (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) (ε : Zphi) (hε : 0 < ε) :
    ∃ M, ∀ n, M ≤ n → -ε < defectR (trajR v n) ∧ defectR (trajR v n) < ε := by
  obtain ⟨c, hc1, hc2⟩ := int_bound (Nc v)
  obtain ⟨m, hm⟩ := archimedean ε hε c
  refine ⟨m, fun n hn => ?_⟩
  have hp : m ≤ (trajR v n).1 := le_trans (by omega) (trajR_fst_ge v hv n)
  have hP : (⟨m, 0⟩ : Zphi) ≤ ⟨((trajR v n).1 : ℤ) - (trajR v n).2, (trajR v n).2⟩ :=
    le_trans (int_le (by omega)) (conj_ge (trajR v n))
  have hNb : Nc (trajR v n) ≤ c ∧ -Nc (trajR v n) ≤ c := by
    rw [Nc_trajR v n]
    rcases PhiPos.neg_one_pow_cases n with h | h <;> rw [h]
    · rw [Int.one_mul]; exact ⟨hc1, hc2⟩
    · rw [Int.neg_one_mul, Int.neg_neg]; exact ⟨hc2, hc1⟩
  have hup := lt_of_mul_conj hε (defectR_mul_conj (trajR v n)) hNb.1 hm hP
  have hneg : -defectR (trajR v n) * ⟨((trajR v n).1 : ℤ) - (trajR v n).2, (trajR v n).2⟩ =
      ⟨-Nc (trajR v n), 0⟩ := by
    rw [neg_mul, defectR_mul_conj]; rfl
  have hlo := lt_of_mul_conj hε hneg hNb.2 hm hP
  refine ⟨?_, hup⟩
  rw [← Zphi.sub_pos] at hlo ⊢
  have e : defectR (trajR v n) - -ε = ε - -defectR (trajR v n) := by ring
  rw [e]; exact hlo

/-- The left defect of an exchanged column is the right defect one advance on. -/
theorem defectL_swap (w : ℕ × ℕ) : defectL w.swap = defectR (advR w) := by
  apply Zphi.ext
  · change ((w.2 : ℤ) + w.1) = (((w.1 + w.2 : ℕ)) : ℤ)
    rw [Int.natCast_add, Int.add_comm]
  · rfl

/-- **Corollary 27.4, left, "converges to φ⁻¹"**, by side exchange: the left
    defect `p − qφ⁻¹` eventually lies strictly between `−ε` and `ε`. -/
theorem defectL_eventually_small (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) (ε : Zphi) (hε : 0 < ε) :
    ∃ M, ∀ n, M ≤ n → -ε < defectL (trajL v n) ∧ defectL (trajL v n) < ε := by
  obtain ⟨M, hM⟩ := defectR_eventually_small v.swap ⟨hv.2, hv.1⟩ ε hε
  refine ⟨M, fun n hn => ?_⟩
  rw [trajL_mirror, defectL_swap]
  exact hM (n + 1) (by omega)

/-! ## Separation Rule 27.5 — Four operations that remain different -/

/-- **Separation Rule 27.5.** Exact witnesses separating `P`, the mirror advances,
    `−I` and word reversal:
    `det P = −1`, `P² = I`; `det 𝖠_R = −1`; `det(−I) = 1`; `−I` commutes with `R`
    and `L` while `P` does not; `−I ≠ P`, `−I ≠ 𝖠_R`, `P ≠ 𝖠_R`; reversal and
    side exchange differ on `[L, R, R]`, already as words and again under `G`. -/
theorem four_operations :
    SideExchange.P.det = -1 ∧ SideExchange.P * SideExchange.P = 1 ∧
    AR.det = -1 ∧ AL.det = -1 ∧
    (matNeg 1).det = 1 ∧
    matNeg 1 * Mat2.R = Mat2.R * matNeg 1 ∧ matNeg 1 * Mat2.L = Mat2.L * matNeg 1 ∧
    SideExchange.P * Mat2.R ≠ Mat2.R * SideExchange.P ∧
    SideExchange.P * Mat2.L ≠ Mat2.L * SideExchange.P ∧
    matNeg 1 ≠ SideExchange.P ∧ matNeg 1 ≠ AR ∧ SideExchange.P ≠ AR ∧
    ([false, true, true] : Word).reverse ≠ SideExchange.mirrorWord [false, true, true] ∧
    Word.G ([false, true, true] : Word).reverse ≠
      Word.G (SideExchange.mirrorWord [false, true, true]) := by
  decide

/-- The reserved chamber coordinate `Φ_ch = x − x⁻¹`, as its integer
    presentation `(p² − q², pq)`: numerator and denominator, never divided.
    It has type `ℕ × ℕ → ℤ × ℤ`; the §28 transport function `Two.phiRad` has type
    `Mat2 → ℤ`, so the two cannot be confused by the checker. -/
def phiCh (v : ℕ × ℕ) : ℤ × ℤ := ((v.1 : ℤ) * v.1 - (v.2 : ℤ) * v.2, (v.1 : ℤ) * v.2)

/-- `Φ_ch` is antisymmetric under parity. -/
theorem phiCh_swap (v : ℕ × ℕ) : phiCh v.swap = (-(phiCh v).1, (phiCh v).2) := by
  change ((v.2 : ℤ) * v.2 - (v.1 : ℤ) * v.1, (v.2 : ℤ) * v.1) = _
  rw [Prod.mk.injEq]
  exact ⟨by change _ = -((v.1 : ℤ) * v.1 - (v.2 : ℤ) * v.2); ring, Int.mul_comm _ _⟩

/-- `Φ_ch` vanishes exactly on the membrane. -/
theorem phiCh_zero_iff (v : ℕ × ℕ) : (phiCh v).1 = 0 ↔ v.1 = v.2 := by
  change (v.1 : ℤ) * v.1 - (v.2 : ℤ) * v.2 = 0 ↔ _
  constructor
  · intro h
    have h' : ((v.1 * v.1 : ℕ) : ℤ) = ((v.2 * v.2 : ℕ) : ℤ) := by push_cast; omega
    exact Nat.mul_self_inj.mp (Int.ofNat.inj h')
  · intro h; rw [h]; exact Int.sub_self _

/-- The sign of `Φ_ch` reads the chamber: positive exactly in the right chamber. -/
theorem phiCh_pos_iff (v : ℕ × ℕ) : 0 < (phiCh v).1 ↔ chamber v = .right := by
  rw [chamber_right_iff]
  change 0 < (v.1 : ℤ) * v.1 - (v.2 : ℤ) * v.2 ↔ _
  constructor
  · intro h
    rcases Nat.lt_or_ge v.2 v.1 with k | k
    · exact k
    · exfalso
      have := Nat.mul_self_le_mul_self k
      have hz : ((v.1 : ℤ) * v.1) ≤ (v.2 : ℤ) * v.2 := by
        rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Int.ofNat_le.mpr this
      omega
  · intro h
    have := Nat.mul_self_lt_mul_self h
    have hz : ((v.2 : ℤ) * v.2) < (v.1 : ℤ) * v.1 := by
      rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Int.ofNat_lt.mpr this
    omega

/-- **Separation Rule 27.5, the rest of the table.** Word inversion is not side
    exchange: on `[L, R, R]` the inverse `inv2 (G w)` (the adjugate, a two-sided
    inverse at `det = 1`) differs from `G` of the mirrored word. The mirror advances
    are not inverse traversal: neither `𝖠_R` nor `𝖠_L` undoes `R` or `L` from
    either side, and neither undoes the other. "Not crystallization" stays a type
    fact, as at Separation Rule 26.6: `AR`, `AL : Mat2`, while `crystallize`
    (Definition 17.6) acts on tick carriers. -/
theorem four_operations_rest :
    Word.G [false, true, true] * Mat2.inv2 (Word.G [false, true, true]) = 1 ∧
    Mat2.inv2 (Word.G [false, true, true]) * Word.G [false, true, true] = 1 ∧
    Mat2.inv2 (Word.G [false, true, true]) ≠ Word.G (SideExchange.mirrorWord [false, true, true]) ∧
    AR * Mat2.R ≠ 1 ∧ Mat2.R * AR ≠ 1 ∧ AR * Mat2.L ≠ 1 ∧ Mat2.L * AR ≠ 1 ∧
    AL * Mat2.L ≠ 1 ∧ Mat2.L * AL ≠ 1 ∧ AL * Mat2.R ≠ 1 ∧ Mat2.R * AL ≠ 1 ∧
    AR * AL ≠ 1 ∧ AL * AR ≠ 1 := by
  decide

/-- **Separation Rule 27.5, "`Φ_ch` is not `Φ_Rad`".** Read on the same word, the
    two disagree in kind: the word `RL` and its side exchange `LR` carry the columns
    `(3, 2)` and `(2, 3)` (`G w` applied to `(1, 1)`), whose `Φ_ch` are `(5, 6)` and
    `(−5, 6)`, opposite and nonzero, while `Φ_Rad` of the two matrices is `3` for
    both. So `Φ_ch` is not read from `Φ_Rad`. "Not the encoded field `φ_t^(E)`"
    stays carried by absence: the tree has no encoded numerical field. -/
theorem phiCh_not_phiRad :
    mulVec (Word.G [true, false]) (1, 1) = (3, 2) ∧
    mulVec (Word.G (SideExchange.mirrorWord [true, false])) (1, 1) = (2, 3) ∧
    phiCh (3, 2) = (5, 6) ∧ phiCh (2, 3) = (-5, 6) ∧
    phiRad (Word.G [true, false]) = 3 ∧ phiRad (Word.G (SideExchange.mirrorWord [true, false])) = 3 := by
  decide

/-! ## Boundary Statement 27.6 -/

/-- **Boundary Statement 27.6.** Two chambers exchanged by parity around a
    parity-fixed membrane; two golden ridges, each the unique positive fixed ratio
    of its advance, exchanged by `x ↦ x⁻¹`, neither a rational column. -/
theorem boundary_27_6 :
    (∀ v, chamber v.swap = (chamber v).flip) ∧
    (∀ v, ProjEq v v.swap ↔ v.1 = v.2) ∧
    ZProjEq (zadvR (phi, 1)) (phi, 1) ∧ ZProjEq (zadvL (phiInv, 1)) (phiInv, 1) ∧
    (∀ v : Zphi × Zphi, 0 < v.1 → 0 < v.2 → ZProjEq (zadvR v) v → ZProjEq v (phi, 1)) ∧
    (∀ v : Zphi × Zphi, 0 < v.1 → 0 < v.2 → ZProjEq (zadvL v) v → ZProjEq v (phiInv, 1)) ∧
    ZProjEq (phi, 1).swap (phiInv, 1) ∧
    (∀ v : ℕ × ℕ, 0 < v.2 → ¬ ZProjEq (ratCol v) (phi, 1) ∧ ¬ ZProjEq (ratCol v) (phiInv, 1)) :=
  ⟨chamber_swap, projEq_swap_iff, ridgeR_fixed, ridgeL_fixed,
    ridgeR_unique_proj, ridgeL_unique_proj,
    ridges_exchanged.1, ridges_not_rational⟩

#print axioms projEq_symm
#print axioms chamber_right
#print axioms chamber_left
#print axioms chamber_membrane
#print axioms right_transfer
#print axioms left_transfer
#print axioms ridgeR_components
#print axioms no_int_root_R
#print axioms no_int_root_L
#print axioms contraction_R
#print axioms chamber_right_iff
#print axioms chamber_left_iff
#print axioms chamber_membrane_iff
#print axioms chamber_projEq
#print axioms advR_projEq
#print axioms advL_projEq
#print axioms swap_projEq
#print axioms Side.flip_flip
#print axioms advR_right
#print axioms advL_left
#print axioms chamber_swap
#print axioms projEq_swap_iff
#print axioms membrane_not_fixed
#print axioms membrane_moves
#print axioms ridgeR_fixed
#print axioms ridgeL_fixed
#print axioms ridges_exchanged
#print axioms zadvL_mirror
#print axioms fixedR_swap_fixedL
#print axioms ridgeR_unique
#print axioms ridgeL_unique
#print axioms fixedR_iff
#print axioms fixedL_iff
#print axioms ridgeR_unique_proj
#print axioms ridgeL_unique_proj
#print axioms ridges_not_rational
#print axioms Nc_advR
#print axioms Nc_trajR
#print axioms N_ne_zero
#print axioms bridge
#print axioms bridge_neg
#print axioms alternation_R
#print axioms defectR_advR
#print axioms defectR_trajR
#print axioms bridgeL
#print axioms defectL_advL
#print axioms defectL_trajL
#print axioms alternation_L
#print axioms four_operations
#print axioms phiCh_swap
#print axioms phiCh_zero_iff
#print axioms phiCh_pos_iff
#print axioms four_operations_rest
#print axioms phiCh_not_phiRad
#print axioms boundary_27_6
#print axioms le_of_int
#print axioms le_of_int'
#print axioms int_le
#print axioms zphi_mul_le_mul_right
#print axioms defectR_mul_conj
#print axioms sq_bound
#print axioms int_bound
#print axioms archimedean
#print axioms trajR_fst_ge
#print axioms conj_ge
#print axioms lt_of_mul_conj
#print axioms defectR_eventually_small
#print axioms defectL_swap
#print axioms defectL_eventually_small

end Chamber
end Two
end RatioSpace
