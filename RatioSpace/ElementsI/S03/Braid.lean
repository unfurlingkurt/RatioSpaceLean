/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-!
  The frame group braids, and the full twist is the minus identity.

  Machine-checked support for the frame group of Elements I, §2 and §3. Everything here

  is an exact statement about integer matrices, so it is decidable and the proofs
  are the computation itself rather than an argument about it.

  What is proved below:
    * `sigma_1 = R` and `sigma_2 = L⁻¹` satisfy the Artin braid relation,
    * the half twist `Δ` squares to `-1` and is of order 4,
    * `L` and `R` do NOT braid, so the relation genuinely needs the inverse,
    * `det` is multiplicative and every generator sits on the `det = 1` shell.

  What is NOT proved here, and is standard literature rather than ours:
  that `B₃ → SL(2,ℤ)` is surjective with kernel `⟨Δ⁴⟩`, and that
  `SL(2,ℝ) = Spin(2,1)⁺`. Those are cited, not reproved.
-/

namespace RatioSpace

/-- A 2×2 integer matrix, written out, so that every claim below reduces. -/
structure Mat2 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq, Repr

namespace Mat2

def mul (M N : Mat2) : Mat2 :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
   M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩

instance : Mul Mat2 := ⟨mul⟩
instance : One Mat2 := ⟨⟨1, 0, 0, 1⟩⟩
instance : Neg Mat2 := ⟨fun M => ⟨-M.a, -M.b, -M.c, -M.d⟩⟩

def det (M : Mat2) : ℤ := M.a * M.d - M.b * M.c

@[simp] theorem det_mul (M N : Mat2) : (M * N).det = M.det * N.det := by
  cases M with | mk a b c d =>
  cases N with | mk e f g h =>
  change (a * e + b * g) * (c * f + d * h) - (a * f + b * h) * (c * e + d * g)
     = (a * d - b * c) * (e * h - f * g)
  ring

/-- The two walk steps of Elements I, as matrices. -/
def L : Mat2 := ⟨1, 0, 1, 1⟩
def R : Mat2 := ⟨1, 1, 0, 1⟩
/-- `L⁻¹`. The braid relation needs it; the positive walk never produces it. -/
def Linv : Mat2 := ⟨1, 0, -1, 1⟩

theorem L_mul_Linv : L * Linv = 1 := by decide
theorem Linv_mul_L : Linv * L = 1 := by decide

/-! ### The braid generators -/

/-- `σ₁`, the first braid generator. -/
def s₁ : Mat2 := R
/-- `σ₂`, the second. -/
def s₂ : Mat2 := Linv

/-- **The Artin braid relation holds in the frame group.** -/
theorem braid : s₁ * s₂ * s₁ = s₂ * s₁ * s₂ := by decide

/-- **`L` and `R` do not braid.** The relation is not a property of the walk
    alphabet; it appears only once a generator is inverted. -/
theorem not_braid_LR : L * R * L ≠ R * L * R := by decide

/-! ### The twist -/

/-- The half twist `Δ = σ₁σ₂σ₁`. -/
def Δ : Mat2 := s₁ * s₂ * s₁

theorem Δ_eq : Δ = ⟨0, 1, -1, 0⟩ := by decide

/-- **The full twist is the minus identity.** `Δ * Δ = -1`, and that identity is
    all that is proved here. Cited reading, not proved in this file: `-1` is the
    nontrivial element of the kernel of `SL(2,ℤ) → PSL(2,ℤ)`, and the spinor
    comparison reads the full twist through it. -/
theorem full_twist : Δ * Δ = -1 := by decide

/-- Two full twists close. `Δ` has order 4. -/
theorem Δ_pow_four : Δ * Δ * Δ * Δ = 1 := by decide

theorem Δ_ne_one : Δ ≠ 1 := by decide
theorem Δsq_ne_one : Δ * Δ ≠ 1 := by decide

/-! ### Everything sits on the contact shell -/

@[simp] theorem det_L : L.det = 1 := by decide
@[simp] theorem det_R : R.det = 1 := by decide
@[simp] theorem det_Linv : Linv.det = 1 := by decide
@[simp] theorem det_Δ : Δ.det = 1 := by decide

/-- **Definition 3.9.** The side-exchange matrix `P`, the exchange of the frame's
    two members. `det = -1`: it is **not** in
    `SL(2,ℤ)`, and it reverses the contact invariant. -/
def P : Mat2 := ⟨0, 1, 1, 0⟩

theorem det_P : P.det = -1 := by decide
theorem P_involutive : P * P = 1 := by decide

/-- **Exchange reverses contact.** For every frame `M`, swapping its two rows
    (left multiplication by `P`) negates the determinant. This is the sign, and
    it is forced. -/
theorem exchange_flips_det (M : Mat2) : (P * M).det = -M.det := by
  rw [det_mul, det_P]; ring

end Mat2
end RatioSpace
