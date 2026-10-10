/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.Contrast
import RatioSpace.ElementsII.S16.Automorphism
/-!
  Elements II §16 Theorem 16.11 — support bound and beat of lone-seed questions.

  **Steps 1 and 2 consume Lemma 16.10 and its depth corollary**, both of which
  are now built (`Two/Contrast.lean`). This file starts at the algebraic core
  of the proof: the four grandchildren of a frame, their six pairwise
  determinant contacts, and the five exact identities the proof's inequality
  argument runs on.

  **Correction 15 does not break the proof, and that was checked before
  anything here was written.** The book displays the pairwise contrasts as
  `N_ij : N_ij + k_ij`; the identity that holds is `N_ij : N_ij − k_ij`. Step 1
  reads only the *tension bounds*, which take `|k_ij|`, and correction 16
  weakens the lower bound by one. Over the 1,694 frames satisfying Step 1's
  three inequalities the margin in `t₁₄ + 2 ≤ min(t₁₃, t₂₃, t₂₄)` is never
  below **4**, where the argument needs 2; and over the 1,056 of those with
  `D ≥ 21` the two uniqueness inequalities hold with slack 4 and 48. So the
  correction costs one and the proof had four to spare.

  The five identities below are pure ring identities in the four frame entries
  and hold with no unimodularity hypothesis at all, which is why they are
  stated over `ℤ` without one.

  **Orientation, settled on the built objects (2026-09-13).** In the tree's
  `otimes g_i g_j` order with `i < j` the contrast is `N_ij : (N_ij + k_ij)`,
  since `a_i b_j − a_j b_i = −k_ij`. So 16.11's display is right as written,
  correction 15 is the signed form of the same identity, and the tensions
  satisfy the book's unweakened bounds `⌊N/k⌋ ≤ t ≤ ⌊N/k⌋ + k`
  (`grand_tension_bounds`). No constant in Step 1 needed changing. Under the
  weakest pairing (lower bound less one, upper `+k`) the thresholds 206 and 440
  still give the margin 2 exactly, so Step 1 does not depend on which bound
  variant is in force.

  **Step 1 is proved in general, on `tEnd`, `coherenceOf` and `support`.**
  `step1_support_sub`: under the three thresholds (`Generic F`) the maximizer set
  of the four grandchildren lies in `{g₁, g₄}`. `step1_unique_pos` /
  `step1_unique_neg`: with `D ≥ 21` it is exactly `[g₁]`, with `D ≤ −21` exactly
  `[g₄]` (`Dq_pos_nat`/`Dq_neg_nat` convert the book's `ℤ` form of `D`).
  None of the new theorems uses `Classical.choice`.

  **What remains between this and the theorem's statement:**
  1. *The occurrence-to-frame reduction.* The grandchildren here are
     `comboI F (a,b)`, i.e. `M_F(a,b)`. That the observer-local relation of the
     occurrence `yLL` is `M_{F_y}(1,3)` (etc.) is Lemma 16.10's `r_F(v) = M_F(a,b)`
     reduction, not yet connected (`Contrast.lean` header).
  2. *The family.* That at a sibling step `{yL, yR}` with all children admitted
     the admitted family `A_{j+1}` is exactly `grand F_y`, in some order
     (`support_perm_mem` absorbs the order).
  3. *Step 2* (the 527 non-generic frames and the `|D| ≤ 20` families
     `RⁿL`, `LⁿR`, period 21), *Step 3* (cousin steps), and the induction that
     assembles clauses 1-4 of the theorem.
-/

namespace RatioSpace
namespace Two
namespace Beat11

/-- The four grandchildren's coefficient pairs, in the book's order
    `g₁ = yLL, g₂ = yLR, g₃ = yRL, g₄ = yRR`. -/
def ab : Fin 4 → ℤ × ℤ
  | 0 => (1, 3)
  | 1 => (2, 3)
  | 2 => (3, 2)
  | 3 => (3, 1)

/-- `n_i = a_i·p₁ + b_i·p₀`. -/
def num (p₁ p₀ : ℤ) (i : Fin 4) : ℤ := (ab i).1 * p₁ + (ab i).2 * p₀

/-- `d_i = a_i·q₁ + b_i·q₀`. -/
def den (q₁ q₀ : ℤ) (i : Fin 4) : ℤ := (ab i).1 * q₁ + (ab i).2 * q₀

/-- `N_ij = n_i·d_j`, for `i < j`. -/
def N (p₁ q₁ p₀ q₀ : ℤ) (i j : Fin 4) : ℤ := num p₁ p₀ i * den q₁ q₀ j

/-- `D = p₁q₁ − p₀q₀`, the quantity Step 1 splits the sector on. -/
def Dq (p₁ q₁ p₀ q₀ : ℤ) : ℤ := p₁ * q₁ - p₀ * q₀

variable (p₁ q₁ p₀ q₀ : ℤ)

theorem id_13_14 :
    8 * N p₁ q₁ p₀ q₀ 0 2 - 7 * N p₁ q₁ p₀ q₀ 0 3
      = 3 * (p₁ + 3 * p₀) * (q₁ + 3 * q₀) := by
  simp only [N, num, den, ab]; ring

theorem id_24_14 :
    8 * N p₁ q₁ p₀ q₀ 1 3 - 7 * N p₁ q₁ p₀ q₀ 0 3
      = 3 * (3 * p₁ + p₀) * (3 * q₁ + q₀) := by
  simp only [N, num, den, ab]; ring

theorem id_23_14 :
    8 * N p₁ q₁ p₀ q₀ 1 2 - 5 * N p₁ q₁ p₀ q₀ 0 3
      = 33 * p₁ * q₁ + 27 * p₁ * q₀ + 27 * p₀ * q₁ + 33 * p₀ * q₀ := by
  simp only [N, num, den, ab]; ring

theorem id_24_13 :
    N p₁ q₁ p₀ q₀ 1 3 - N p₁ q₁ p₀ q₀ 0 2 = 3 * Dq p₁ q₁ p₀ q₀ := by
  simp only [N, num, den, ab, Dq]; ring

theorem id_34_12 :
    N p₁ q₁ p₀ q₀ 2 3 - N p₁ q₁ p₀ q₀ 0 1 = 7 * Dq p₁ q₁ p₀ q₀ := by
  simp only [N, num, den, ab, Dq]; ring

/-! ## Step 1's margin, from the identities and the corrected bounds

The book derives `t₁₄ + 2 ≤ min(t₁₃, t₂₃, t₂₄)` under three thresholds. Each
case is the same shape: an exact identity `c₁·N_ij − c₂·N₁₄ = c₃·X` with a
lower bound on `X`, the corrected lower bound on `t_ij`, and the tightened
upper bound on `t₁₄`.

`step_margin` is that shape once, as pure arithmetic on the four numbers, so
the three cases are three instances of one lemma rather than three proofs.
-/

/-- **Step 1's margin, in one lemma.**

    Given `c₁·A = c₂·B + c₃·X` with `X` above a threshold, the corrected lower
    bound `A/k₁ ≤ t + 1`, and the tightened upper bound `u + 1 ≤ B/k₂ + k₂`,
    the gap `u + 2 ≤ t` follows. -/
theorem step_margin (A B X t u : ℕ)
    (hid : 8 * A = 7 * B + 3 * X) (hX : 206 ≤ X)
    (hlow : A / 7 ≤ t + 1) (hup : u + 1 ≤ B / 8 + 8) :
    u + 2 ≤ t := by
  omega

/-- The `t₂₃` case: identity `8N₂₃ − 5N₁₄ = C`, threshold `440`, divisor `5`. -/
theorem step_margin_23 (A B X t u : ℕ)
    (hid : 8 * A = 5 * B + X) (hX : 440 ≤ X)
    (hlow : A / 5 ≤ t + 1) (hup : u + 1 ≤ B / 8 + 8) :
    u + 2 ≤ t := by
  omega

/-! ## Step 1 in general: from the frame to the maximizer set

Four layers, each proved for every frame:

* **tensions**: `tEnd g_i g_j` is pinned between `⌊N_ij/k_ij⌋` and
  `⌊N_ij/k_ij⌋ + k_ij`, on the tree's own `tEnd`, reduction included;
* **margins**: pure `omega` on those bounds and the identities;
* **ℤ[φ] comparisons**: two sums of negative golden powers, from `PhiPos` alone;
* **scores and support**: `coherenceOf` on the four grandchildren, and
  Construction Axiom II.1's `support` itself.

**Orientation.** In the tree's `otimes g_i g_j` order with `i < j`, the
contrast is `N_ij : (N_ij + k_ij)`, because `a_i b_j − a_j b_i = −k_ij < 0` for
these four coefficient pairs. That is the book's display in 16.11, and the
tension bounds are the book's own `⌊N/k⌋ ≤ t ≤ ⌊N/k⌋ + k` (`tEnd_bounds`).
Correction 15's `N − Δ` is the same identity read with `Δ` signed, so there is
no conflict. The margin lemmas below still take the weaker pair
`⌊N/k⌋ ≤ t + 1`, `t ≤ ⌊N/k⌋ + k`, and hold: with the thresholds 206 and 440 the
floor gaps are at least 11 (checked exhaustively before writing, then proved by
`omega`), which is exactly the 2 needed plus the 9 the two slacks eat.
-/

open Contrast Zphi PhiPos Automorphism

/-! ### Tensions on the actual `tEnd` -/

/-- **The depth bounds on `tEnd` itself.** If `A ⊗ B = P : (P + k)` as an
    unreduced presentation, then `⌊P/k⌋ ≤ tEnd A B ≤ ⌊P/k⌋ + k`. Reduction is
    absorbed by `cfNat_mul`, the order swap by `cfNat_sum_swap`, and the bounds
    are Lemma 16.10's corollary on `contrastPres (P + k) k`. -/
theorem tEnd_bounds (A B : IPres) (P k : ℕ) (hk : 0 < k)
    (hp : (IPres.otimes A B).p = P) (hq : (IPres.otimes A B).q = P + k) :
    P / k ≤ tEnd A B ∧ tEnd A B ≤ P / k + k := by
  have hP : 0 < P := hp ▸ (IPres.otimes A B).p_pos
  have e1 : tEnd A B = (Pres.cfNat
      ((IPres.otimes A B).p / Nat.gcd (IPres.otimes A B).p (IPres.otimes A B).q)
      ((IPres.otimes A B).q / Nat.gcd (IPres.otimes A B).p (IPres.otimes A B).q)).sum
        - 1 := rfl
  rw [hp, hq] at e1
  have hg : 0 < Nat.gcd P (P + k) := Nat.gcd_pos_of_pos_left _ hP
  have hdp : P / Nat.gcd P (P + k) * Nat.gcd P (P + k) = P :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hdq : (P + k) / Nat.gcd P (P + k) * Nat.gcd P (P + k) = P + k :=
    Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hqpos : 0 < (P + k) / Nat.gcd P (P + k) :=
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hg
  have e2 : Pres.cfNat (P / Nat.gcd P (P + k)) ((P + k) / Nat.gcd P (P + k))
      = Pres.cfNat P (P + k) := by
    rw [← cfNat_mul (P / Nat.gcd P (P + k)) ((P + k) / Nat.gcd P (P + k))
      (Nat.gcd P (P + k)) hqpos hg, hdp, hdq]
  have e3 : (Pres.cfNat P (P + k)).sum = (Pres.cfNat (P + k) P).sum :=
    Pres.cfNat_sum_swap hP (by omega)
  have h2 : k < P + k := by omega
  have key : tEnd A B = Pres.dSB (contrastPres (P + k) k hk h2) := by
    rw [e1, e2, e3]
    change _ = (Pres.cfNat (P + k) (P + k - k)).sum - 1
    rw [Nat.add_sub_cancel]
  have lo := contrast_depth_lower (P + k) k hk h2
  have hi := contrast_depth_upper_tight (P + k) k hk h2
  rw [Nat.add_div_right P hk] at lo hi
  rw [key]
  exact ⟨by omega, by omega⟩

/-- Lemma 16.10's offset, in the orientation 16.11 reads: when
    `a'b = ab' + k`, the contrast of `M_F(a,b)` against `M_F(a',b')` has second
    component `N + k`. -/
theorem combo_contrast_q (F : Frame) (a b a' b' k : ℕ)
    (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (hk : (a' : ℤ) * b = a * b' + k) :
    (IPres.otimes (comboI F a b ha hb) (comboI F a' b' ha' hb')).q
      = (IPres.otimes (comboI F a b ha hb) (comboI F a' b' ha' hb')).p + k := by
  have h := contrast_offset F a b a' b' ha hb ha' hb'
  omega

/-- The four grandchildren of an occurrence with frame `F`, as the
    coefficient combinations `M_F(a_i,b_i)` of Lemma 16.10. -/
def gLL (F : Frame) : IPres := comboI F 1 3 (by decide) (by decide)
def gLR (F : Frame) : IPres := comboI F 2 3 (by decide) (by decide)
def gRL (F : Frame) : IPres := comboI F 3 2 (by decide) (by decide)
def gRR (F : Frame) : IPres := comboI F 3 1 (by decide) (by decide)

/-- The admitted family of a sibling step: the four grandchildren, in order. -/
def grand (F : Frame) : List IPres := [gLL F, gLR F, gRL F, gRR F]

/-- `N_ij = n_i·d_j` over `ℕ`, on the frame's own entries. -/
def Nn (F : Frame) (a b a' b' : ℕ) : ℕ :=
  (a * F.plus.p + b * F.minus.p) * (a' * F.plus.q + b' * F.minus.q)

/-- The six tension bounds of 16.11, on the tree's `tEnd`. -/
theorem grand_tension_bounds (F : Frame) :
    (Nn F 1 3 2 3 / 3 ≤ tEnd (gLL F) (gLR F) ∧ tEnd (gLL F) (gLR F) ≤ Nn F 1 3 2 3 / 3 + 3) ∧
    (Nn F 1 3 3 2 / 7 ≤ tEnd (gLL F) (gRL F) ∧ tEnd (gLL F) (gRL F) ≤ Nn F 1 3 3 2 / 7 + 7) ∧
    (Nn F 1 3 3 1 / 8 ≤ tEnd (gLL F) (gRR F) ∧ tEnd (gLL F) (gRR F) ≤ Nn F 1 3 3 1 / 8 + 8) ∧
    (Nn F 2 3 3 2 / 5 ≤ tEnd (gLR F) (gRL F) ∧ tEnd (gLR F) (gRL F) ≤ Nn F 2 3 3 2 / 5 + 5) ∧
    (Nn F 2 3 3 1 / 7 ≤ tEnd (gLR F) (gRR F) ∧ tEnd (gLR F) (gRR F) ≤ Nn F 2 3 3 1 / 7 + 7) ∧
    (Nn F 3 2 3 1 / 3 ≤ tEnd (gRL F) (gRR F) ∧ tEnd (gRL F) (gRR F) ≤ Nn F 3 2 3 1 / 3 + 3) :=
  ⟨tEnd_bounds _ _ _ 3 (by decide) rfl (combo_contrast_q F 1 3 2 3 3 _ _ _ _ (by decide)),
   tEnd_bounds _ _ _ 7 (by decide) rfl (combo_contrast_q F 1 3 3 2 7 _ _ _ _ (by decide)),
   tEnd_bounds _ _ _ 8 (by decide) rfl (combo_contrast_q F 1 3 3 1 8 _ _ _ _ (by decide)),
   tEnd_bounds _ _ _ 5 (by decide) rfl (combo_contrast_q F 2 3 3 2 5 _ _ _ _ (by decide)),
   tEnd_bounds _ _ _ 7 (by decide) rfl (combo_contrast_q F 2 3 3 1 7 _ _ _ _ (by decide)),
   tEnd_bounds _ _ _ 3 (by decide) rfl (combo_contrast_q F 3 2 3 1 3 _ _ _ _ (by decide))⟩

/-! ### Margins, as integer arithmetic -/

/-- **Step 1's margin**, `t₁₄ + 2 ≤ min(t₁₃, t₂₃, t₂₄)`, from the three
    identities, the three thresholds, the weakened lower bounds and the
    untightened upper bound. -/
theorem step1_margins (N13 N14 N23 N24 X Y Z t13 t14 t23 t24 : ℕ)
    (h13 : 8 * N13 = 7 * N14 + 3 * X) (h24 : 8 * N24 = 7 * N14 + 3 * Y)
    (h23 : 8 * N23 = 5 * N14 + Z) (hX : 206 ≤ X) (hY : 206 ≤ Y) (hZ : 440 ≤ Z)
    (l13 : N13 / 7 ≤ t13 + 1) (l23 : N23 / 5 ≤ t23 + 1) (l24 : N24 / 7 ≤ t24 + 1)
    (u14 : t14 ≤ N14 / 8 + 8) :
    t14 + 2 ≤ t13 ∧ t14 + 2 ≤ t23 ∧ t14 + 2 ≤ t24 :=
  -- One `omega` per conjunct: `omega` on a conjunction negates it through a
  -- classical `¬(A ∧ B)` step and pulls `Classical.choice`.
  ⟨by omega, by omega, by omega⟩

/-- **The uniqueness margins**, `t₁₃ + 1 ≤ t₂₄` and `t₁₂ + 1 ≤ t₃₄`, when
    `D ≥ 21`, stated additively (`N₂₄ − N₁₃ = 3D`, `N₃₄ − N₁₂ = 7D`). -/
theorem step1_margins_D (N12 N13 N24 N34 P1 P0 t12 t13 t24 t34 : ℕ)
    (h1 : N24 + 3 * P0 = N13 + 3 * P1) (h2 : N34 + 7 * P0 = N12 + 7 * P1)
    (hD : P0 + 21 ≤ P1)
    (l24 : N24 / 7 ≤ t24 + 1) (u13 : t13 ≤ N13 / 7 + 7)
    (l34 : N34 / 3 ≤ t34 + 1) (u12 : t12 ≤ N12 / 3 + 3) :
    t13 + 1 ≤ t24 ∧ t12 + 1 ≤ t34 :=
  ⟨by omega, by omega⟩

/-! ### The two golden comparisons, choice-free -/

/-- `φ⁻ᵇ + φ⁻ᶜ < φ⁻ᵘ + φ⁻ᵛ` whenever `u + 2 ≤ b, c`: the book's
    `φ^{−t₁₄}(1 − 2φ^{−2}) > 0`, run additively as
    `2φ⁻⁽ᵘ⁺²⁾ < φ⁻⁽ᵘ⁺¹⁾ + φ⁻⁽ᵘ⁺²⁾ = φ⁻ᵘ`. -/
theorem sum_lt_of_two_deeper {u v b c : ℕ} (hb : u + 2 ≤ b) (hc : u + 2 ≤ c) :
    phiNegPow b + phiNegPow c < phiNegPow u + phiNegPow v :=
  calc phiNegPow b + phiNegPow c ≤ phiNegPow (u + 2) + phiNegPow (u + 2) :=
        add_le_add (phiNegPow_anti_le hb) (phiNegPow_anti_le hc)
    _ < phiNegPow (u + 1) + phiNegPow (u + 2) :=
        add_lt_add_right_zphi (phiNegPow_succ_lt (u + 1))
    _ = phiNegPow u := (phiNegPow_rec u).symm
    _ < phiNegPow u + phiNegPow v := lt_add_of_pos_right _ (PhiPos.phiNegPow_pos v)

/-- `φ⁻ᵇ + φ⁻ᵈ < φ⁻ᵃ + φ⁻ᶜ` whenever `a < b` and `c < d`. -/
theorem sum_lt_of_both_deeper {a b c d : ℕ} (hab : a < b) (hcd : c < d) :
    phiNegPow b + phiNegPow d < phiNegPow a + phiNegPow c :=
  calc phiNegPow b + phiNegPow d < phiNegPow a + phiNegPow d :=
        add_lt_add_right_zphi (phiNegPow_strict hab)
    _ = phiNegPow d + phiNegPow a := add_comm _ _
    _ < phiNegPow c + phiNegPow a := add_lt_add_right_zphi (phiNegPow_strict hcd)
    _ = phiNegPow a + phiNegPow c := add_comm _ _

/-! ### Scores on the four grandchildren -/

section scores

variable (F : Frame)

theorem score_LL : coherenceOf (grand F) (gLL F) =
    (phiNegPow (tEnd (gLL F) (gRR F)) + phiNegPow (tEnd (gLL F) (gRL F))) + (phiNegPow 0 +
      phiNegPow (tEnd (gLL F) (gLR F))) := by
  change phiNegPow (tEnd (gLL F) (gLL F)) + (phiNegPow (tEnd (gLL F) (gLR F)) + (phiNegPow (tEnd
    (gLL F) (gRL F))
    + (phiNegPow (tEnd (gLL F) (gRR F)) + 0))) = _
  rw [tEnd_self]; ring

theorem score_LR : coherenceOf (grand F) (gLR F) =
    (phiNegPow (tEnd (gLR F) (gRL F)) + phiNegPow (tEnd (gLR F) (gRR F))) + (phiNegPow 0 +
      phiNegPow (tEnd (gLL F) (gLR F))) := by
  change phiNegPow (tEnd (gLR F) (gLL F)) + (phiNegPow (tEnd (gLR F) (gLR F))
    + (phiNegPow (tEnd (gLR F) (gRL F)) + (phiNegPow (tEnd (gLR F) (gRR F)) + 0))) = _
  rw [tEnd_self, tEnd_comm (gLR F) (gLL F)]; ring

theorem score_RL : coherenceOf (grand F) (gRL F) =
    (phiNegPow (tEnd (gLL F) (gRL F)) + phiNegPow (tEnd (gLR F) (gRL F))) + (phiNegPow 0 +
      phiNegPow (tEnd (gRL F) (gRR F))) := by
  change phiNegPow (tEnd (gRL F) (gLL F)) + (phiNegPow (tEnd (gRL F) (gLR F))
    + (phiNegPow (tEnd (gRL F) (gRL F)) + (phiNegPow (tEnd (gRL F) (gRR F)) + 0))) = _
  rw [tEnd_self, tEnd_comm (gRL F) (gLL F), tEnd_comm (gRL F) (gLR F)]; ring

theorem score_RR : coherenceOf (grand F) (gRR F) =
    (phiNegPow (tEnd (gLL F) (gRR F)) + phiNegPow (tEnd (gLR F) (gRR F))) + (phiNegPow 0 +
      phiNegPow (tEnd (gRL F) (gRR F))) := by
  change phiNegPow (tEnd (gRR F) (gLL F)) + (phiNegPow (tEnd (gRR F) (gLR F))
    + (phiNegPow (tEnd (gRR F) (gRL F)) + (phiNegPow (tEnd (gRR F) (gRR F)) + 0))) = _
  rw [tEnd_self, tEnd_comm (gRR F) (gLL F), tEnd_comm (gRR F) (gLR F),
    tEnd_comm (gRR F) (gRL F)]; ring

/-- `C(g₁)` against `C(g₄)` share `1 + φ^{−t₁₄}`; the rest is `t₁₂,t₁₃` against
    `t₃₄,t₂₄`. -/
theorem score_LL' : coherenceOf (grand F) (gLL F) =
    (phiNegPow (tEnd (gLL F) (gLR F)) + phiNegPow (tEnd (gLL F) (gRL F))) + (phiNegPow 0 +
      phiNegPow (tEnd (gLL F) (gRR F))) := by
  rw [score_LL]; ring

theorem score_RR' : coherenceOf (grand F) (gRR F) =
    (phiNegPow (tEnd (gRL F) (gRR F)) + phiNegPow (tEnd (gLR F) (gRR F))) + (phiNegPow 0 +
      phiNegPow (tEnd (gLL F) (gRR F))) := by
  rw [score_RR]; ring

theorem score_RL' : coherenceOf (grand F) (gRL F) =
    (phiNegPow (tEnd (gLL F) (gRL F)) + phiNegPow (tEnd (gLR F) (gRL F))) + (phiNegPow 0 +
      phiNegPow (tEnd (gRL F) (gRR F))) :=
  score_RL F

end scores

/-! ### Theorem 16.11, Step 1 -/

/-- The three thresholds of Step 1, as the book writes them, on the frame's
    entries `p₁ = F.plus.p`, `q₁ = F.plus.q`, `p₀ = F.minus.p`, `q₀ = F.minus.q`. -/
structure Generic (F : Frame) : Prop where
  hA : 206 ≤ (F.plus.p + 3 * F.minus.p) * (F.plus.q + 3 * F.minus.q)
  hB : 206 ≤ (3 * F.plus.p + F.minus.p) * (3 * F.plus.q + F.minus.q)
  hC : 440 ≤ 33 * F.plus.p * F.plus.q + 27 * F.plus.p * F.minus.q
    + 27 * F.minus.p * F.plus.q + 33 * F.minus.p * F.minus.q

/-- **Step 1's margin on the actual tensions.** -/
theorem step1_tension_margin (F : Frame) (hg : Generic F) :
    tEnd (gLL F) (gRR F) + 2 ≤ tEnd (gLL F) (gRL F) ∧
    tEnd (gLL F) (gRR F) + 2 ≤ tEnd (gLR F) (gRL F) ∧
    tEnd (gLL F) (gRR F) + 2 ≤ tEnd (gLR F) (gRR F) := by
  obtain ⟨_, ⟨l13, _⟩, ⟨_, u14⟩, ⟨l23, _⟩, ⟨l24, _⟩, _⟩ := grand_tension_bounds F
  refine step1_margins (Nn F 1 3 3 2) (Nn F 1 3 3 1) (Nn F 2 3 3 2) (Nn F 2 3 3 1)
    _ _ _ _ _ _ _ ?_ ?_ ?_ hg.hA hg.hB hg.hC (by omega) (by omega) (by omega) u14
  · unfold Nn; ring
  · unfold Nn; ring
  · unfold Nn; ring

/-- **The uniqueness margins on the actual tensions**, for `D ≥ 21`. -/
theorem step1_tension_margin_pos (F : Frame)
    (hD : F.minus.p * F.minus.q + 21 ≤ F.plus.p * F.plus.q) :
    tEnd (gLL F) (gRL F) + 1 ≤ tEnd (gLR F) (gRR F) ∧
    tEnd (gLL F) (gLR F) + 1 ≤ tEnd (gRL F) (gRR F) := by
  obtain ⟨⟨_, u12⟩, ⟨_, u13⟩, _, _, ⟨l24, _⟩, ⟨l34, _⟩⟩ := grand_tension_bounds F
  refine step1_margins_D (Nn F 1 3 2 3) (Nn F 1 3 3 2) (Nn F 2 3 3 1) (Nn F 3 2 3 1)
    (F.plus.p * F.plus.q) (F.minus.p * F.minus.q) _ _ _ _ ?_ ?_ hD
    (by omega) u13 (by omega) u12
  · unfold Nn; ring
  · unfold Nn; ring

/-- **The mirror margins**, for `D ≤ −21`. -/
theorem step1_tension_margin_neg (F : Frame)
    (hD : F.plus.p * F.plus.q + 21 ≤ F.minus.p * F.minus.q) :
    tEnd (gLR F) (gRR F) + 1 ≤ tEnd (gLL F) (gRL F) ∧
    tEnd (gRL F) (gRR F) + 1 ≤ tEnd (gLL F) (gLR F) := by
  obtain ⟨⟨l12, _⟩, ⟨l13, _⟩, _, _, ⟨_, u24⟩, ⟨_, u34⟩⟩ := grand_tension_bounds F
  refine step1_margins_D (Nn F 3 2 3 1) (Nn F 2 3 3 1) (Nn F 1 3 3 2) (Nn F 1 3 2 3)
    (F.minus.p * F.minus.q) (F.plus.p * F.plus.q) _ _ _ _ ?_ ?_ hD
    (by omega) u24 (by omega) u34
  · unfold Nn; ring
  · unfold Nn; ring

/-- **Theorem 16.11, Step 1, first half: the score comparisons.**
    `C(g₂) < C(g₁)` and `C(g₃) < C(g₄)`. -/
theorem step1_scores (F : Frame) (hg : Generic F) :
    coherenceOf (grand F) (gLR F) < coherenceOf (grand F) (gLL F) ∧
    coherenceOf (grand F) (gRL F) < coherenceOf (grand F) (gRR F) := by
  obtain ⟨m13, m23, m24⟩ := step1_tension_margin F hg
  refine ⟨?_, ?_⟩
  · rw [score_LR, score_LL]
    exact add_lt_add_right_zphi (sum_lt_of_two_deeper m23 m24)
  · rw [score_RL, score_RR]
    exact add_lt_add_right_zphi (sum_lt_of_two_deeper m13 m23)

/-- `C(g₄) < C(g₁)` when `D ≥ 21`. -/
theorem step1_scores_pos (F : Frame)
    (hD : F.minus.p * F.minus.q + 21 ≤ F.plus.p * F.plus.q) :
    coherenceOf (grand F) (gRR F) < coherenceOf (grand F) (gLL F) := by
  obtain ⟨m1, m2⟩ := step1_tension_margin_pos F hD
  rw [score_RR', score_LL']
  exact add_lt_add_right_zphi (sum_lt_of_both_deeper m2 m1)

/-- `C(g₁) < C(g₄)` when `D ≤ −21`. -/
theorem step1_scores_neg (F : Frame)
    (hD : F.plus.p * F.plus.q + 21 ≤ F.minus.p * F.minus.q) :
    coherenceOf (grand F) (gLL F) < coherenceOf (grand F) (gRR F) := by
  obtain ⟨m1, m2⟩ := step1_tension_margin_neg F hD
  rw [score_RR', score_LL']
  exact add_lt_add_right_zphi (sum_lt_of_both_deeper m2 m1)

theorem not_le_of_lt_zphi {a b : Zphi} (h : a < b) : ¬ b ≤ a :=
  fun h' => lt_irrefl _ (lt_of_lt_of_le h h')

theorem mem_grand {F : Frame} {y : IPres} (hy : y ∈ grand F) :
    y = gLL F ∨ y = gLR F ∨ y = gRL F ∨ y = gRR F := by
  rcases List.mem_cons.mp hy with h | hy
  · exact Or.inl h
  rcases List.mem_cons.mp hy with h | hy
  · exact Or.inr (Or.inl h)
  rcases List.mem_cons.mp hy with h | hy
  · exact Or.inr (Or.inr (Or.inl h))
  rcases List.mem_cons.mp hy with h | hy
  · exact Or.inr (Or.inr (Or.inr h))
  · cases hy

theorem gLL_mem (F : Frame) : gLL F ∈ grand F := List.Mem.head _
theorem gRR_mem (F : Frame) : gRR F ∈ grand F :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- **Theorem 16.11, Step 1: the maximizer set lies in `{g₁, g₄}`.** Stated on
    Construction Axiom II.1's `support`, not on a proxy. -/
theorem step1_support_sub (F : Frame) (hg : Generic F) :
    ∀ y ∈ support (grand F), y = gLL F ∨ y = gRR F := by
  intro y hy
  obtain ⟨h21, h34⟩ := step1_scores F hg
  have hmax := support_maximal hy
  rcases mem_grand (support_sub hy) with h | h | h | h
  · exact Or.inl h
  · rw [h] at hmax; exact absurd (hmax _ (gLL_mem F)) (not_le_of_lt_zphi h21)
  · rw [h] at hmax; exact absurd (hmax _ (gRR_mem F)) (not_le_of_lt_zphi h34)
  · exact Or.inr h

/-- Construction Axiom II.1's filter predicate on the four grandchildren. -/
def selPred (F : Frame) (y : IPres) : Bool :=
  (grand F).all (fun z => decide (coherenceOf (grand F) z ≤ coherenceOf (grand F) y))

/-- The support of the four grandchildren is exactly `[w]` once `w` strictly
    beats the other three: `support` is a filter, computed here cell by cell. -/
theorem support_grand_eq {F : Frame}
    (hLL : ∀ z ∈ grand F, coherenceOf (grand F) z ≤ coherenceOf (grand F) (gLL F))
    (hLR : coherenceOf (grand F) (gLR F) < coherenceOf (grand F) (gLL F))
    (hRL : coherenceOf (grand F) (gRL F) < coherenceOf (grand F) (gLL F))
    (hRR : coherenceOf (grand F) (gRR F) < coherenceOf (grand F) (gLL F)) :
    support (grand F) = [gLL F] := by
  have neg : ∀ w, coherenceOf (grand F) w < coherenceOf (grand F) (gLL F) →
      ¬ ((grand F).all (fun z => decide (coherenceOf (grand F) z ≤
        coherenceOf (grand F) w)) = true) := fun w hw h =>
    not_le_of_lt_zphi hw (of_decide_eq_true (List.all_eq_true.mp h _ (gLL_mem F)))
  unfold support
  change List.filter (selPred F) (gLL F :: gLR F :: gRL F :: gRR F :: []) = _
  rw [List.filter_cons_of_pos (p := selPred F)
      (List.all_eq_true.mpr (fun z hz => decide_eq_true (hLL z hz))),
    List.filter_cons_of_neg (p := selPred F) (neg _ hLR), List.filter_cons_of_neg (p := selPred
      F) (neg _ hRL),
    List.filter_cons_of_neg (p := selPred F) (neg _ hRR)]
  rfl

/-- **Theorem 16.11, Step 1, `D ≥ 21`: `g₁` is the unique maximizer.** -/
theorem step1_unique_pos (F : Frame) (hg : Generic F)
    (hD : F.minus.p * F.minus.q + 21 ≤ F.plus.p * F.plus.q) :
    support (grand F) = [gLL F] := by
  obtain ⟨h21, h34⟩ := step1_scores F hg
  have h41 := step1_scores_pos F hD
  have h31 := lt_trans h34 h41
  refine support_grand_eq ?_ h21 h31 h41
  intro z hz
  rcases mem_grand hz with rfl | rfl | rfl | rfl
  · exact le_refl _
  · exact le_of_lt h21
  · exact le_of_lt h31
  · exact le_of_lt h41

/-- **Theorem 16.11, Step 1, `D ≤ −21`: `g₄` is the unique maximizer.** -/
theorem step1_unique_neg (F : Frame) (hg : Generic F)
    (hD : F.plus.p * F.plus.q + 21 ≤ F.minus.p * F.minus.q) :
    support (grand F) = [gRR F] := by
  obtain ⟨h21, h34⟩ := step1_scores F hg
  have h14 := step1_scores_neg F hD
  have h24 := lt_trans h21 h14
  have neg : ∀ w, coherenceOf (grand F) w < coherenceOf (grand F) (gRR F) →
      ¬ ((grand F).all (fun z => decide (coherenceOf (grand F) z ≤
        coherenceOf (grand F) w)) = true) := fun w hw h =>
    not_le_of_lt_zphi hw (of_decide_eq_true (List.all_eq_true.mp h _ (gRR_mem F)))
  have hRR : ∀ z ∈ grand F, coherenceOf (grand F) z ≤ coherenceOf (grand F) (gRR F) := by
    intro z hz
    rcases mem_grand hz with rfl | rfl | rfl | rfl
    · exact le_of_lt h14
    · exact le_of_lt h24
    · exact le_of_lt h34
    · exact le_refl _
  unfold support
  change List.filter (selPred F) (gLL F :: gLR F :: gRL F :: gRR F :: []) = _
  rw [List.filter_cons_of_neg (p := selPred F) (neg _ h14), List.filter_cons_of_neg (p :=
    selPred F) (neg _ h24),
    List.filter_cons_of_neg (p := selPred F) (neg _ h34),
    List.filter_cons_of_pos (p := selPred F)
      (List.all_eq_true.mpr (fun z hz => decide_eq_true (hRR z hz)))]
  rfl

/-- `D ≥ 21` in the book's form, over `ℤ`, gives the `ℕ` form used above. -/
theorem Dq_pos_nat (F : Frame)
    (hD : 21 ≤ Dq (F.plus.p : ℤ) F.plus.q F.minus.p F.minus.q) :
    F.minus.p * F.minus.q + 21 ≤ F.plus.p * F.plus.q := by
  unfold Dq at hD
  have h1 := Int.natCast_mul F.plus.p F.plus.q
  have h0 := Int.natCast_mul F.minus.p F.minus.q
  omega

theorem Dq_neg_nat (F : Frame)
    (hD : Dq (F.plus.p : ℤ) F.plus.q F.minus.p F.minus.q ≤ -21) :
    F.plus.p * F.plus.q + 21 ≤ F.minus.p * F.minus.q := by
  unfold Dq at hD
  have h1 := Int.natCast_mul F.plus.p F.plus.q
  have h0 := Int.natCast_mul F.minus.p F.minus.q
  omega

end Beat11
end Two
end RatioSpace
