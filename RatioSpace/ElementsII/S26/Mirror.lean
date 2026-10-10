/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S09.Admission
import RatioSpace.ElementsII.S08.Coherence
/-!
  Elements II §26 — Mirror advances and their positive two-step skeletons.

  One positive generator followed by the parity exchange of Elements I gives an
  orientation-reversing advance. Its square is back in the positive monoid
  (`RL` or `LR`), its powers are Fibonacci matrices, and its column orbit carries
  the previous head as its tail, so the exact state is two-component and never
  recurs.

  **Nothing new is assumed.** `R`, `L`, `P` are Elements I's matrices; the
  Fibonacci numbers are Mathlib's `Nat.fib` with the recurrence already restated
  in `Two/Coherence.lean`.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Two
namespace Mirror

open Mat2 Word

/-! ## Definition 26.1 — Orientation-reversing mirror advances -/

/-- `𝖠_R = R𝖯`. -/
def AR : Mat2 := R * Mat2.P

/-- `𝖠_L = L𝖯`. -/
def AL : Mat2 := L * Mat2.P

/-- **Definition 26.1.** `𝖯² = I`, `𝖯R = L𝖯`, `𝖯L = R𝖯`, and the two forms and
    entries of each mirror advance. -/
theorem def_26_1 :
    Mat2.P * Mat2.P = 1 ∧ Mat2.P * R = L * Mat2.P ∧ Mat2.P * L = R * Mat2.P ∧
    AR = Mat2.P * L ∧ AR = ⟨1, 1, 1, 0⟩ ∧ AL = Mat2.P * R ∧ AL = ⟨0, 1, 1, 1⟩ := by decide

theorem det_mirror : AR.det = -1 ∧ AL.det = -1 := by decide

/-- Determinant `−1`: neither mirror advance is a positive word. -/
theorem mirror_not_positive : AR ∉ Mplus ∧ AL ∉ Mplus := by
  refine ⟨fun ⟨w, hw⟩ => ?_, fun ⟨w, hw⟩ => ?_⟩
  · have h := det_G w; rw [hw, det_mirror.1] at h; exact absurd h (by decide)
  · have h := det_G w; rw [hw, det_mirror.2] at h; exact absurd h (by decide)

/-- A matrix acting on a column presentation `(p, q)ᵀ`. -/
def mulVec (M : Mat2) (v : ℤ × ℤ) : ℤ × ℤ := (M.a * v.1 + M.b * v.2, M.c * v.1 + M.d * v.2)

/-- `𝖠_R (p, q)ᵀ = (p+q, p)ᵀ`. -/
theorem AR_column (p q : ℤ) : mulVec AR (p, q) = (p + q, p) := by
  rw [def_26_1.2.2.2.2.1]
  change (1 * p + 1 * q, 1 * p + 0 * q) = (p + q, p)
  simp only [Int.one_mul, Int.zero_mul, Int.add_zero]

/-- `𝖠_L (p, q)ᵀ = (q, p+q)ᵀ`. -/
theorem AL_column (p q : ℤ) : mulVec AL (p, q) = (q, p + q) := by
  rw [def_26_1.2.2.2.2.2.2]
  change (0 * p + 1 * q, 1 * p + 1 * q) = (q, p + q)
  simp only [Int.one_mul, Int.zero_mul, Int.zero_add]

/-! ## Proposition 26.2 — Parity exchange and positive two-step return -/

theorem parity_exchange : Mat2.P * AR * Mat2.P = AL ∧ Mat2.P * AL * Mat2.P = AR := by decide

/-- `𝖠_R² = RL`, `𝖠_L² = LR`. -/
theorem squares : AR * AR = R * L ∧ AL * AL = L * R := by decide

theorem mpow_add (M : Mat2) (m n : ℕ) : matPow M (m + n) = matPow M m * matPow M n := by
  induction m with
  | zero => rw [Nat.zero_add]; exact (one_mul' _).symm
  | succ m ih =>
    rw [Nat.add_right_comm m 1 n]
    change M * matPow M (m + n) = M * matPow M m * matPow M n
    rw [ih, mul_assoc']

theorem mpow_succ_right (M : Mat2) (n : ℕ) : matPow M (n + 1) = matPow M n * M := by
  rw [mpow_add]
  change matPow M n * (M * 1) = matPow M n * M
  rw [mul_one']

theorem AR_pow_even (r : ℕ) : matPow AR (2 * r) = matPow (R * L) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Nat.mul_succ, Nat.add_comm, mpow_add, ih]
    change AR * (AR * 1) * matPow (R * L) r = R * L * matPow (R * L) r
    rw [mul_one', squares.1]

theorem AL_pow_even (r : ℕ) : matPow AL (2 * r) = matPow (L * R) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Nat.mul_succ, Nat.add_comm, mpow_add, ih]
    change AL * (AL * 1) * matPow (L * R) r = L * R * matPow (L * R) r
    rw [mul_one', squares.2]

/-- **Proposition 26.2, odd powers.** `𝖠_R^{2r+1} = (RL)^r R𝖯`: the parity
    exchange stays explicit. -/
theorem AR_pow_odd (r : ℕ) : matPow AR (2 * r + 1) = matPow (R * L) r * (R * Mat2.P) := by
  rw [mpow_succ_right, AR_pow_even]; rfl

theorem AL_pow_odd (r : ℕ) : matPow AL (2 * r + 1) = matPow (L * R) r * (L * Mat2.P) := by
  rw [mpow_succ_right, AL_pow_even]; rfl

/-! ## Theorem 26.3 — Exact Fibonacci form of every mirror advance -/

/-- `F_n`, read as an integer entry. -/
abbrev F (n : ℕ) : ℤ := (Nat.fib n : ℤ)

theorem F_rec (n : ℕ) : F (n + 2) = F (n + 1) + F n := by
  change ((Nat.fib (n + 2) : ℕ) : ℤ) = _
  rw [fib_rec, Int.natCast_add]

/-- **Theorem 26.3.** `𝖠_R^n = [[F_{n+1}, F_n], [F_n, F_{n−1}]]`, `n ≥ 1`. -/
theorem AR_pow_fib (n : ℕ) : matPow AR (n + 1) = ⟨F (n + 2), F (n + 1), F (n + 1), F n⟩ := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h2 : F (n + 2) = F (n + 1) + F n := F_rec n
    have h3 : F (n + 3) = F (n + 2) + F (n + 1) := F_rec (n + 1)
    change AR * matPow AR (n + 1) = ⟨F (n + 3), F (n + 2), F (n + 2), F (n + 1)⟩
    rw [ih, def_26_1.2.2.2.2.1]
    change (⟨1 * F (n + 2) + 1 * F (n + 1), 1 * F (n + 1) + 1 * F n,
      1 * F (n + 2) + 0 * F (n + 1), 1 * F (n + 1) + 0 * F n⟩ : Mat2) = _
    rw [Mat2.mk.injEq]
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- **Theorem 26.3.** `𝖠_L^n = [[F_{n−1}, F_n], [F_n, F_{n+1}]]`, `n ≥ 1`. -/
theorem AL_pow_fib (n : ℕ) : matPow AL (n + 1) = ⟨F n, F (n + 1), F (n + 1), F (n + 2)⟩ := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h2 : F (n + 2) = F (n + 1) + F n := F_rec n
    have h3 : F (n + 3) = F (n + 2) + F (n + 1) := F_rec (n + 1)
    change AL * matPow AL (n + 1) = ⟨F (n + 1), F (n + 2), F (n + 2), F (n + 3)⟩
    rw [ih, def_26_1.2.2.2.2.2.2]
    change (⟨0 * F n + 1 * F (n + 1), 0 * F (n + 1) + 1 * F (n + 2),
      1 * F n + 1 * F (n + 1), 1 * F (n + 1) + 1 * F (n + 2)⟩ : Mat2) = _
    rw [Mat2.mk.injEq]
    exact ⟨by omega, by omega, by omega, by omega⟩

theorem AR_pow_column (n : ℕ) (p q : ℤ) :
    mulVec (matPow AR (n + 1)) (p, q) = (F (n + 2) * p + F (n + 1) * q, F (n + 1) * p + F n * q) := by
  rw [AR_pow_fib]; rfl

theorem AL_pow_column (n : ℕ) (p q : ℤ) :
    mulVec (matPow AL (n + 1)) (p, q) = (F n * p + F (n + 1) * q, F (n + 1) * p + F (n + 2) * q) := by
  rw [AL_pow_fib]; rfl

/-! ## Corollary 26.4 — The paired orbit from `1:1` -/

/-- **Corollary 26.4.** `𝖠_R^n (1,1)ᵀ = (F_{n+2}, F_{n+1})ᵀ` and
    `𝖠_L^n (1,1)ᵀ = (F_{n+1}, F_{n+2})ᵀ`, exchanged at every depth. -/
theorem orbit_from_one (n : ℕ) :
    mulVec (matPow AR n) (1, 1) = (F (n + 2), F (n + 1)) ∧
    mulVec (matPow AL n) (1, 1) = (F (n + 1), F (n + 2)) := by
  cases n with
  | zero => decide
  | succ n =>
    have h2 : F (n + 2) = F (n + 1) + F n := F_rec n
    have h3 : F (n + 3) = F (n + 2) + F (n + 1) := F_rec (n + 1)
    rw [AR_pow_column, AL_pow_column]
    change (F (n + 2) * 1 + F (n + 1) * 1, F (n + 1) * 1 + F n * 1) = (F (n + 3), F (n + 2)) ∧
      (F n * 1 + F (n + 1) * 1, F (n + 1) * 1 + F (n + 2) * 1) = (F (n + 2), F (n + 3))
    rw [Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

theorem orbit_exchanged (n : ℕ) :
    mulVec (matPow AL n) (1, 1) = (mulVec (matPow AR n) (1, 1)).swap := by
  rw [(orbit_from_one n).1, (orbit_from_one n).2]; rfl

/-! ## Theorem 26.5 — Carried tail and exact nonrecurrence -/

/-- The right advance on a natural column presentation. -/
def advR (v : ℕ × ℕ) : ℕ × ℕ := (v.1 + v.2, v.1)

def advL (v : ℕ × ℕ) : ℕ × ℕ := (v.2, v.1 + v.2)

theorem AR_acts_as_advR (v : ℕ × ℕ) :
    mulVec AR ((v.1 : ℤ), (v.2 : ℤ)) = (((advR v).1 : ℤ), ((advR v).2 : ℤ)) := by
  rw [AR_column]
  change _ = (((v.1 + v.2 : ℕ) : ℤ), (v.1 : ℤ))
  rw [Int.natCast_add]

theorem AL_acts_as_advL (v : ℕ × ℕ) :
    mulVec AL ((v.1 : ℤ), (v.2 : ℤ)) = (((advL v).1 : ℤ), ((advL v).2 : ℤ)) := by
  rw [AL_column]
  change _ = ((v.2 : ℤ), ((v.1 + v.2 : ℕ) : ℤ))
  rw [Int.natCast_add]

def trajR (v : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => v
  | n + 1 => advR (trajR v n)

def trajL (v : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => v
  | n + 1 => advL (trajL v n)

/-- **Theorem 26.5.** `q_{n+1} = p_n`: the tail carries the preceding head. -/
theorem carried_tail (v : ℕ × ℕ) (n : ℕ) : (trajR v (n + 1)).2 = (trajR v n).1 := rfl

/-- **Theorem 26.5.** `p_{n+2} = p_{n+1} + p_n`. -/
theorem head_recurrence (v : ℕ × ℕ) (n : ℕ) :
    (trajR v (n + 2)).1 = (trajR v (n + 1)).1 + (trajR v n).1 := rfl

theorem trajR_pos (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) : ∀ n, 0 < (trajR v n).1 ∧ 0 < (trajR v n).2
  | 0 => hv
  | n + 1 => by
    obtain ⟨h1, -⟩ := trajR_pos v hv n
    exact ⟨Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _), h1⟩

theorem head_strict (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) (n : ℕ) :
    (trajR v n).1 < (trajR v (n + 1)).1 :=
  Nat.lt_add_of_pos_right (trajR_pos v hv n).2

theorem head_mono (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) (m : ℕ) :
    ∀ d, 0 < d → (trajR v m).1 < (trajR v (m + d)).1
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | d + 1, _ => by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; exact head_strict v hv m
    · exact Nat.lt_trans (head_mono v hv m d hd) (head_strict v hv (m + d))

/-- **Theorem 26.5, nonrecurrence.** From a positive presentation, all later
    columns are pairwise distinct. -/
theorem trajR_distinct (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) (m n : ℕ) (hmn : m ≠ n) :
    trajR v m ≠ trajR v n := by
  intro he
  have hf := congrArg Prod.fst he
  rcases Nat.lt_or_gt_of_ne hmn with h | h
  · have hl := head_mono v hv m (n - m) (Nat.sub_pos_of_lt h)
    rw [Nat.add_sub_of_le (Nat.le_of_lt h), ← hf] at hl
    exact Nat.lt_irrefl _ hl
  · have hl := head_mono v hv n (m - n) (Nat.sub_pos_of_lt h)
    rw [Nat.add_sub_of_le (Nat.le_of_lt h), hf] at hl
    exact Nat.lt_irrefl _ hl

/-- The left trajectory is the parity image of the right one. -/
theorem trajL_mirror (v : ℕ × ℕ) : ∀ n, trajL v n = (trajR v.swap n).swap
  | 0 => rfl
  | n + 1 => by
    change advL (trajL v n) = (advR (trajR v.swap n)).swap
    rw [trajL_mirror v n]
    change ((trajR v.swap n).1, (trajR v.swap n).2 + (trajR v.swap n).1) =
      ((trajR v.swap n).1, (trajR v.swap n).1 + (trajR v.swap n).2)
    rw [Nat.add_comm]

/-- **Theorem 26.5, side mirror.** `p'_{n+1} = q'_n`: the left trajectory's tail
    carries the preceding head. -/
theorem left_carried_tail (v : ℕ × ℕ) (n : ℕ) : (trajL v (n + 1)).1 = (trajL v n).2 := by
  simp only [trajL_mirror]; rfl

/-- **Theorem 26.5, side mirror.** `q'_{n+2} = q'_{n+1} + q'_n`: the left trajectory's
    second coordinate carries the recurrence. -/
theorem left_head_recurrence (v : ℕ × ℕ) (n : ℕ) :
    (trajL v (n + 2)).2 = (trajL v (n + 1)).2 + (trajL v n).2 := by
  simp only [trajL_mirror]; rfl

/-- **Theorem 26.5, side mirror.** The left trajectory's columns are pairwise
    distinct (its recurrence is `left_carried_tail`, `left_head_recurrence`). -/
theorem trajL_distinct (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) (m n : ℕ) (hmn : m ≠ n) :
    trajL v m ≠ trajL v n := by
  intro he
  rw [trajL_mirror, trajL_mirror] at he
  exact trajR_distinct v.swap ⟨hv.2, hv.1⟩ m n hmn (by
    have := congrArg Prod.swap he
    exact this)

/-! ## Separation Rule 26.6 — Mirror advance exposes a recurrence of the generator grammar

    `AR`, `AL : Mat2` are matrices; the one-tick construction of §11 is a map on
    tick carriers. The types differ, so no mirror advance is a tick. What needs a
    witness is the second sentence: only the two-step skeleton is positive. -/

theorem RL_mem : R * L ∈ Mplus := ⟨[true, false], by decide⟩

theorem LR_mem : L * R ∈ Mplus := ⟨[false, true], by decide⟩

theorem mpow_mem {M : Mat2} (hM : M ∈ Mplus) : ∀ r, matPow M r ∈ Mplus
  | 0 => one_mem_Mplus
  | r + 1 => mul_mem_Mplus hM (mpow_mem hM r)

theorem det_mpow_one {M : Mat2} (hM : M.det = 1) : ∀ r, (matPow M r).det = 1
  | 0 => by change (1 : Mat2).det = 1; decide
  | r + 1 => by
    change (M * matPow M r).det = 1
    rw [det_mul, hM, det_mpow_one hM r]; rfl

/-- **Separation Rule 26.6.** Every even mirror power is positive; every odd one
    is not. `𝖠_R² = RL` does not make one mirror tick a positive event. -/
theorem skeleton_only (r : ℕ) :
    matPow AR (2 * r) ∈ Mplus ∧ matPow AL (2 * r) ∈ Mplus ∧
    matPow AR (2 * r + 1) ∉ Mplus ∧ matPow AL (2 * r + 1) ∉ Mplus := by
  refine ⟨AR_pow_even r ▸ mpow_mem RL_mem r, AL_pow_even r ▸ mpow_mem LR_mem r,
    fun ⟨w, hw⟩ => ?_, fun ⟨w, hw⟩ => ?_⟩
  · have h := det_G w
    rw [hw, AR_pow_odd, det_mul, det_mpow_one (by decide) r] at h
    exact absurd h (by decide)
  · have h := det_G w
    rw [hw, AL_pow_odd, det_mul, det_mpow_one (by decide) r] at h
    exact absurd h (by decide)

/-! ## Boundary Statement 26.7 -/

/-- **Boundary Statement 26.7, right hand.** Mirrored successor off the positive
    monoid, the two-step continuation back on it, a Fibonacci head, and no
    recurrence. The left hand is `native_recurrence_family_L`. -/
theorem native_recurrence_family (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) :
    AR ∉ Mplus ∧ AR * AR ∈ Mplus ∧
    (∀ n, (trajR v (n + 2)).1 = (trajR v (n + 1)).1 + (trajR v n).1) ∧
    (∀ m n, m ≠ n → trajR v m ≠ trajR v n) :=
  ⟨mirror_not_positive.1, squares.1 ▸ RL_mem, head_recurrence v, trajR_distinct v hv⟩

/-- **Boundary Statement 26.7, left hand.** `𝖠_L` is off the positive monoid,
    `𝖠_L² = LR` is on it, the left head (second coordinate) is Fibonacci-recursive,
    and the left trajectory does not recur. -/
theorem native_recurrence_family_L (v : ℕ × ℕ) (hv : 0 < v.1 ∧ 0 < v.2) :
    AL ∉ Mplus ∧ AL * AL ∈ Mplus ∧
    (∀ n, (trajL v (n + 2)).2 = (trajL v (n + 1)).2 + (trajL v n).2) ∧
    (∀ m n, m ≠ n → trajL v m ≠ trajL v n) :=
  ⟨mirror_not_positive.2, squares.2 ▸ LR_mem, left_head_recurrence v, trajL_distinct v hv⟩

/-- **Boundary Statement 26.7, "its exact state is two-component"**, read as the
    paragraph after Theorem 26.5 reads it: a projection retaining only the head is
    not a first-order state. For each hand, no map `f` gives the next head from the
    current head alone on every positive trajectory: the right heads `(trajR (1,1) 2).1`
    and `(trajR (1,2) 1).1` are both `3`, their successors are `5` and `4`; the left
    heads `(trajL (1,1) 2).2` and `(trajL (2,1) 1).2` are both `3`, their successors
    `5` and `4`. The pair itself is first-order (`advR`, `advL`), its tail carrying
    the preceding head (`carried_tail`, `left_carried_tail`). -/
theorem head_not_first_order :
    (¬ ∃ f : ℕ → ℕ, ∀ v : ℕ × ℕ, 0 < v.1 → 0 < v.2 → ∀ n,
        (trajR v (n + 1)).1 = f (trajR v n).1) ∧
    (¬ ∃ f : ℕ → ℕ, ∀ v : ℕ × ℕ, 0 < v.1 → 0 < v.2 → ∀ n,
        (trajL v (n + 1)).2 = f (trajL v n).2) := by
  refine ⟨fun ⟨f, hf⟩ => ?_, fun ⟨f, hf⟩ => ?_⟩
  · have h1 : 5 = f 3 := hf (1, 1) (by decide) (by decide) 2
    have h2 : 4 = f 3 := hf (1, 2) (by decide) (by decide) 1
    exact absurd (h1.trans h2.symm) (by decide)
  · have h1 : 5 = f 3 := hf (1, 1) (by decide) (by decide) 2
    have h2 : 4 = f 3 := hf (2, 1) (by decide) (by decide) 1
    exact absurd (h1.trans h2.symm) (by decide)

#print axioms def_26_1
#print axioms mirror_not_positive
#print axioms AR_column
#print axioms AL_column
#print axioms parity_exchange
#print axioms squares
#print axioms AR_pow_even
#print axioms AL_pow_even
#print axioms AR_pow_odd
#print axioms AL_pow_odd
#print axioms AR_pow_fib
#print axioms AL_pow_fib
#print axioms AR_pow_column
#print axioms AL_pow_column
#print axioms orbit_from_one
#print axioms orbit_exchanged
#print axioms AR_acts_as_advR
#print axioms AL_acts_as_advL
#print axioms carried_tail
#print axioms head_recurrence
#print axioms trajR_distinct
#print axioms trajL_mirror
#print axioms left_carried_tail
#print axioms left_head_recurrence
#print axioms trajL_distinct
#print axioms skeleton_only
#print axioms native_recurrence_family
#print axioms native_recurrence_family_L
#print axioms head_not_first_order

end Mirror
end Two
end RatioSpace
