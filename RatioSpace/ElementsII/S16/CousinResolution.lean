/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.RootChainState
/-!
  Elements II §16 Theorem 16.11, Step 3 — the cousin steps, for every `m`.

  From the cousin pair `{RⁿLLL, RⁿLRR}`, `n = 21m + 3`, the four children are
  `a = RⁿLLLL = (5n+1):5`, `b = RⁿLLLR = (7n+2):7`, `c = RⁿLRRL = (7n+5):7`,
  `d = RⁿLRRR = (5n+4):5`, with coefficient vectors `(1,4), (2,5), (5,2), (4,1)`
  in `F_{RⁿL}` (`ca_combo`..`cd_combo`, through Lemma 16.10's reduction).

  **Computed before writing** (`research/experiments/elements_ii_axiom_ii1.py`
  and `beat_support_bound.advance`, `0 ≤ m < 200`), then proved for every `m`:

  * `t(a,b) = 245m + 40`, `t(a,d) = 35m + 8`, `t(b,c) = 49m + 10`,
    `t(c,d) = 245m + 46`;
  * `t(a,c) = 245j + (12, 65, 96, 135, 175, 217)` and
    `t(b,d) = 245j + (13, 53, 106, 137, 176, 216)` at `m = 6j + i`,
    `i = 0..5`.

  The depths are sums of Euclidean quotients, as in `RootChain.lean`: every
  cross pair is `P : (P + d)` with `d ∈ {3, 15, 21, 18}`, so the depth is `1 +
  ⌊P/d⌋ + depth(P mod d : d)`, and only the last is a closed `decide`.

  **The book, checked.** The outer pair `{a, d}` carries the smallest tension
  (`35m + 8`); the decision is periodic in `m`, with period **6**; every `m`
  gives a singleton. The book does not say which. It is
  `[RⁿLRRR]` at `m ≡ 1, 5 (mod 6)` (`n ≡ 24, 108 mod 126`) and `[RⁿLLLL]`
  otherwise (`step3_cousin_support`). At `i ∈ {0,2,3,4}`, `t(a,c) < t(b,d)` and
  `a` wins by `sum_lt_of_both_deeper`; at `i = 1` the order flips by 12, at
  `i = 5` by exactly 1, and `d` wins, the `i = 5` case through
  `sum_lt_of_near_deep` (`φ⁻⁽ᵘ⁺¹⁾ + φ⁻⁽ᵘ⁺³⁾ < φ⁻ᵘ`). The theorem holds from
  `m = 0`; Step 2 only needs `m ≥ 1`.

  **Built:** the six closed forms; `step3_cousin_support` on Definition
  8.1's `support`; `addr_a`..`addr_d` through `r`; the concrete steps
  `{LLL,LRL} → {LLLR}` and `{RLR,RRR} → {RRRL}` cited from
  `RootOrbit.theorem_16_5_polarized_L/_R`; the mirror family by
  `tEnd_side_invariant` (`step3_mirror_support`, `maddr_*`); the carrier
  bridge `cousin_step` / `advanceCarrier_active_cousin` in
  `RootChainCarrier`'s style.

  **The mirror on the tick carrier, 2026-09-14 00:30 work beat:** its children
  arrive as `mfam` reversed, so the decision is carried across by
  `coherenceOf_perm` (`mfamC`, `mselC`, `mcousin_step`,
  `advanceCarrier_active_mcousin`).

  **Not built here:** the induction that chains Step 2 into this step on one
  carrier (identifier freshness through `advanceCarrier`, as in
  `RootChainCarrier`).

  Every theorem `propext`/`Quot.sound` or less.
-/
set_option linter.style.show false

namespace RatioSpace
namespace Two
namespace Step3Cousin

open Pres Contrast Zphi PhiPos Automorphism Beat11

/-! ## Depth of a near pair -/

/-- If `A ⊗ B = P : (P + d)` and `P = ρ + k·d`, the tension is the depth of
    `ρ : d` plus `k`: one unit for the leading `1`, `k` for the quotient. -/
theorem tEnd_near (A B : IPres) (d k ρ : ℕ) (hd : d ≠ 0)
    (hq : A.q * B.p = A.p * B.q + d) (hp : A.p * B.q = ρ + k * d) :
    tEnd A B = (cfNat ρ d).sum + k := by
  have hA := A.p_pos
  have hB := B.q_pos
  rw [RootChain.tEnd_eq_sum, hq,
    cfNat_sum_add_left (Nat.mul_ne_zero (by omega) (by omega)) hd, hp,
    RootChain.sum_mulR _ _ _ hd]
  omega

/-! ## The four children of the cousin pair `{RⁿLLL, RⁿLRR}`, `n = 21m + 3` -/

/-- `a = RⁿLLLL`: `(5n+1):5`. -/
def ca (m : ℕ) : IPres := ⟨105 * m + 16, 5, by omega, by omega⟩
/-- `b = RⁿLLLR`: `(7n+2):7`. -/
def cb (m : ℕ) : IPres := ⟨147 * m + 23, 7, by omega, by omega⟩
/-- `c = RⁿLRRL`: `(7n+5):7`. -/
def cc (m : ℕ) : IPres := ⟨147 * m + 26, 7, by omega, by omega⟩
/-- `d = RⁿLRRR`: `(5n+4):5`. -/
def cd (m : ℕ) : IPres := ⟨105 * m + 19, 5, by omega, by omega⟩

/-- The admitted family of the cousin step, in the tree's order `a, b, c, d`. -/
def fam (m : ℕ) : List IPres := [ca m, cb m, cc m, cd m]

/-! ## The six tensions, for every `m` -/

theorem t_ab (m : ℕ) : tEnd (ca m) (cb m) = 245 * m + 40 := by
  rw [tEnd_near (ca m) (cb m) 3 (245 * m + 37) 1 (by decide)
    (by show 5 * (147 * m + 23) = (105 * m + 16) * 7 + 3; ring)
    (by show (105 * m + 16) * 7 = 1 + (245 * m + 37) * 3; ring),
    show (cfNat 1 3).sum = 3 by decide]
  omega

/-- **The outer pair: `t(a,d) = 35m + 8`**, the smallest of the six. -/
theorem t_ad (m : ℕ) : tEnd (ca m) (cd m) = 35 * m + 8 := by
  rw [tEnd_near (ca m) (cd m) 15 (35 * m + 5) 5 (by decide)
    (by show 5 * (105 * m + 19) = (105 * m + 16) * 5 + 15; ring)
    (by show (105 * m + 16) * 5 = 5 + (35 * m + 5) * 15; ring),
    show (cfNat 5 15).sum = 3 by decide]
  omega

theorem t_bc (m : ℕ) : tEnd (cb m) (cc m) = 49 * m + 10 := by
  rw [tEnd_near (cb m) (cc m) 21 (49 * m + 7) 14 (by decide)
    (by show 7 * (147 * m + 26) = (147 * m + 23) * 7 + 21; ring)
    (by show (147 * m + 23) * 7 = 14 + (49 * m + 7) * 21; ring),
    show (cfNat 14 21).sum = 3 by decide]
  omega

theorem t_cd (m : ℕ) : tEnd (cc m) (cd m) = 245 * m + 46 := by
  rw [tEnd_near (cc m) (cd m) 3 (245 * m + 43) 1 (by decide)
    (by show 7 * (105 * m + 19) = (147 * m + 26) * 5 + 3; ring)
    (by show (147 * m + 26) * 5 = 1 + (245 * m + 43) * 3; ring),
    show (cfNat 1 3).sum = 3 by decide]
  omega

/-- The offsets of `t(a,c)` and `t(b,d)` by `m mod 6`. -/
def acOff : ℕ → ℕ
  | 0 => 12 | 1 => 65 | 2 => 96 | 3 => 135 | 4 => 175 | _ => 217

def bdOff : ℕ → ℕ
  | 0 => 13 | 1 => 53 | 2 => 106 | 3 => 137 | 4 => 176 | _ => 216

theorem t_ac_res (j i k ρ : ℕ) (h : 735 * i + 112 = ρ + k * 18) :
    tEnd (ca (6 * j + i)) (cc (6 * j + i)) = (cfNat ρ 18).sum + (245 * j + k) :=
  tEnd_near _ _ 18 (245 * j + k) ρ (by decide)
    (by show 5 * (147 * (6 * j + i) + 26) = (105 * (6 * j + i) + 16) * 7 + 18; ring)
    (by show (105 * (6 * j + i) + 16) * 7 = ρ + (245 * j + k) * 18; omega)

theorem t_bd_res (j i k ρ : ℕ) (h : 735 * i + 115 = ρ + k * 18) :
    tEnd (cb (6 * j + i)) (cd (6 * j + i)) = (cfNat ρ 18).sum + (245 * j + k) :=
  tEnd_near _ _ 18 (245 * j + k) ρ (by decide)
    (by show 7 * (105 * (6 * j + i) + 19) = (147 * (6 * j + i) + 23) * 5 + 18; ring)
    (by show (147 * (6 * j + i) + 23) * 5 = ρ + (245 * j + k) * 18; omega)

/-- **`t(a,c)` at `m = 6j + i`.** -/
theorem t_ac_six (j : ℕ) : ∀ i, i < 6 →
    tEnd (ca (6 * j + i)) (cc (6 * j + i)) = 245 * j + acOff i
  | 0, _ => by
      rw [t_ac_res j 0 6 4 rfl, show (cfNat 4 18).sum = 6 by decide]
      change _ = _ + 12
      omega
  | 1, _ => by
      rw [t_ac_res j 1 47 1 rfl, show (cfNat 1 18).sum = 18 by decide]
      change _ = _ + 65
      omega
  | 2, _ => by
      rw [t_ac_res j 2 87 16 rfl, show (cfNat 16 18).sum = 9 by decide]
      change _ = _ + 96
      omega
  | 3, _ => by
      rw [t_ac_res j 3 128 13 rfl, show (cfNat 13 18).sum = 7 by decide]
      change _ = _ + 135
      omega
  | 4, _ => by
      rw [t_ac_res j 4 169 10 rfl, show (cfNat 10 18).sum = 6 by decide]
      change _ = _ + 175
      omega
  | 5, _ => by
      rw [t_ac_res j 5 210 7 rfl, show (cfNat 7 18).sum = 7 by decide]
      change _ = _ + 217
      omega
  | _ + 6, h => absurd h (by omega)

/-- **`t(b,d)` at `m = 6j + i`.** -/
theorem t_bd_six (j : ℕ) : ∀ i, i < 6 →
    tEnd (cb (6 * j + i)) (cd (6 * j + i)) = 245 * j + bdOff i
  | 0, _ => by
      rw [t_bd_res j 0 6 7 rfl, show (cfNat 7 18).sum = 7 by decide]
      change _ = _ + 13
      omega
  | 1, _ => by
      rw [t_bd_res j 1 47 4 rfl, show (cfNat 4 18).sum = 6 by decide]
      change _ = _ + 53
      omega
  | 2, _ => by
      rw [t_bd_res j 2 88 1 rfl, show (cfNat 1 18).sum = 18 by decide]
      change _ = _ + 106
      omega
  | 3, _ => by
      rw [t_bd_res j 3 128 16 rfl, show (cfNat 16 18).sum = 9 by decide]
      change _ = _ + 137
      omega
  | 4, _ => by
      rw [t_bd_res j 4 169 13 rfl, show (cfNat 13 18).sum = 7 by decide]
      change _ = _ + 176
      omega
  | 5, _ => by
      rw [t_bd_res j 5 210 10 rfl, show (cfNat 10 18).sum = 6 by decide]
      change _ = _ + 216
      omega
  | _ + 6, h => absurd h (by omega)

theorem split6 (m : ℕ) : ∃ j i, i < 6 ∧ m = 6 * j + i :=
  ⟨m / 6, m % 6, Nat.mod_lt _ (by decide), (Nat.div_add_mod m 6).symm⟩

theorem t_ac (m : ℕ) : tEnd (ca m) (cc m) = 245 * (m / 6) + acOff (m % 6) := by
  obtain ⟨j, i, hi, rfl⟩ := split6 m
  rw [show (6 * j + i) / 6 = j by omega, show (6 * j + i) % 6 = i by omega]
  exact t_ac_six j i hi

theorem t_bd (m : ℕ) : tEnd (cb m) (cd m) = 245 * (m / 6) + bdOff (m % 6) := by
  obtain ⟨j, i, hi, rfl⟩ := split6 m
  rw [show (6 * j + i) / 6 = j by omega, show (6 * j + i) % 6 = i by omega]
  exact t_bd_six j i hi

/-! ## Coherence values of any four -/

section four

variable (w x y z : IPres)

theorem coherence_w : coherenceOf [w, x, y, z] w =
    1 + phiNegPow (tEnd w x) + phiNegPow (tEnd w y) + phiNegPow (tEnd w z) := by
  simp only [coherenceOf, tensions, coherence, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, self_term]
  ring

theorem coherence_x : coherenceOf [w, x, y, z] x =
    phiNegPow (tEnd w x) + 1 + phiNegPow (tEnd x y) + phiNegPow (tEnd x z) := by
  simp only [coherenceOf, tensions, coherence, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, self_term]
  rw [tEnd_comm x w]
  ring

theorem coherence_y : coherenceOf [w, x, y, z] y =
    phiNegPow (tEnd w y) + phiNegPow (tEnd x y) + 1 + phiNegPow (tEnd y z) := by
  simp only [coherenceOf, tensions, coherence, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, self_term]
  rw [tEnd_comm y w, tEnd_comm y x]
  ring

theorem coherence_z : coherenceOf [w, x, y, z] z =
    phiNegPow (tEnd w z) + phiNegPow (tEnd x z) + phiNegPow (tEnd y z) + 1 := by
  simp only [coherenceOf, tensions, coherence, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, self_term]
  rw [tEnd_comm z w, tEnd_comm z x, tEnd_comm z y]
  ring

theorem lt_x_w
    (h : phiNegPow (tEnd x y) + phiNegPow (tEnd x z) < phiNegPow (tEnd w z) + phiNegPow (tEnd w
      y)) :
    coherenceOf [w, x, y, z] x < coherenceOf [w, x, y, z] w := by
  have e1 : coherenceOf [w, x, y, z] x
      = (phiNegPow (tEnd x y) + phiNegPow (tEnd x z)) + (1 + phiNegPow (tEnd w x)) := by
    rw [coherence_x]; ring
  have e2 : coherenceOf [w, x, y, z] w
      = (phiNegPow (tEnd w z) + phiNegPow (tEnd w y)) + (1 + phiNegPow (tEnd w x)) := by
    rw [coherence_w]; ring
  rw [e1, e2]; exact add_lt_add_right_zphi h

theorem lt_y_w
    (h : phiNegPow (tEnd x y) + phiNegPow (tEnd y z) < phiNegPow (tEnd w z) + phiNegPow (tEnd w
      x)) :
    coherenceOf [w, x, y, z] y < coherenceOf [w, x, y, z] w := by
  have e1 : coherenceOf [w, x, y, z] y
      = (phiNegPow (tEnd x y) + phiNegPow (tEnd y z)) + (1 + phiNegPow (tEnd w y)) := by
    rw [coherence_y]; ring
  have e2 : coherenceOf [w, x, y, z] w
      = (phiNegPow (tEnd w z) + phiNegPow (tEnd w x)) + (1 + phiNegPow (tEnd w y)) := by
    rw [coherence_w]; ring
  rw [e1, e2]; exact add_lt_add_right_zphi h

theorem lt_z_w
    (h : phiNegPow (tEnd x z) + phiNegPow (tEnd y z) < phiNegPow (tEnd w y) + phiNegPow (tEnd w
      x)) :
    coherenceOf [w, x, y, z] z < coherenceOf [w, x, y, z] w := by
  have e1 : coherenceOf [w, x, y, z] z
      = (phiNegPow (tEnd x z) + phiNegPow (tEnd y z)) + (1 + phiNegPow (tEnd w z)) := by
    rw [coherence_z]; ring
  have e2 : coherenceOf [w, x, y, z] w
      = (phiNegPow (tEnd w y) + phiNegPow (tEnd w x)) + (1 + phiNegPow (tEnd w z)) := by
    rw [coherence_w]; ring
  rw [e1, e2]; exact add_lt_add_right_zphi h

theorem lt_w_z
    (h : phiNegPow (tEnd w y) + phiNegPow (tEnd w x) < phiNegPow (tEnd x z) + phiNegPow (tEnd y
      z)) :
    coherenceOf [w, x, y, z] w < coherenceOf [w, x, y, z] z := by
  have e1 : coherenceOf [w, x, y, z] w
      = (phiNegPow (tEnd w y) + phiNegPow (tEnd w x)) + (1 + phiNegPow (tEnd w z)) := by
    rw [coherence_w]; ring
  have e2 : coherenceOf [w, x, y, z] z
      = (phiNegPow (tEnd x z) + phiNegPow (tEnd y z)) + (1 + phiNegPow (tEnd w z)) := by
    rw [coherence_z]; ring
  rw [e1, e2]; exact add_lt_add_right_zphi h

theorem lt_x_z
    (h : phiNegPow (tEnd w x) + phiNegPow (tEnd x y) < phiNegPow (tEnd w z) + phiNegPow (tEnd y
      z)) :
    coherenceOf [w, x, y, z] x < coherenceOf [w, x, y, z] z := by
  have e1 : coherenceOf [w, x, y, z] x
      = (phiNegPow (tEnd w x) + phiNegPow (tEnd x y)) + (1 + phiNegPow (tEnd x z)) := by
    rw [coherence_x]; ring
  have e2 : coherenceOf [w, x, y, z] z
      = (phiNegPow (tEnd w z) + phiNegPow (tEnd y z)) + (1 + phiNegPow (tEnd x z)) := by
    rw [coherence_z]; ring
  rw [e1, e2]; exact add_lt_add_right_zphi h

theorem lt_y_z
    (h : phiNegPow (tEnd w y) + phiNegPow (tEnd x y) < phiNegPow (tEnd w z) + phiNegPow (tEnd x
      z)) :
    coherenceOf [w, x, y, z] y < coherenceOf [w, x, y, z] z := by
  have e1 : coherenceOf [w, x, y, z] y
      = (phiNegPow (tEnd w y) + phiNegPow (tEnd x y)) + (1 + phiNegPow (tEnd y z)) := by
    rw [coherence_y]; ring
  have e2 : coherenceOf [w, x, y, z] z
      = (phiNegPow (tEnd w z) + phiNegPow (tEnd x z)) + (1 + phiNegPow (tEnd y z)) := by
    rw [coherence_z]; ring
  rw [e1, e2]; exact add_lt_add_right_zphi h

/-- Definition 8.1's filter predicate on a four-member family. -/
def sel4 (v : IPres) : Bool :=
  [w, x, y, z].all (fun u => decide (coherenceOf [w, x, y, z] u ≤ coherenceOf [w, x, y, z] v))

theorem sel4_false {v top : IPres} (htop : top ∈ [w, x, y, z])
    (h : coherenceOf [w, x, y, z] v < coherenceOf [w, x, y, z] top) : sel4 w x y z v = false := by
  cases hs : sel4 w x y z v
  · rfl
  · exact absurd (of_decide_eq_true (List.all_eq_true.mp hs top htop)) (not_le_of_lt_zphi h)

theorem sel4_head (hx : coherenceOf [w, x, y, z] x < coherenceOf [w, x, y, z] w)
    (hy : coherenceOf [w, x, y, z] y < coherenceOf [w, x, y, z] w)
    (hz : coherenceOf [w, x, y, z] z < coherenceOf [w, x, y, z] w) :
    sel4 w x y z w = true ∧ sel4 w x y z x = false ∧ sel4 w x y z y = false ∧
      sel4 w x y z z = false := by
  have hw : w ∈ [w, x, y, z] := List.Mem.head _
  refine ⟨List.all_eq_true.mpr (fun u hu => decide_eq_true ?_),
    sel4_false w x y z hw hx, sel4_false w x y z hw hy, sel4_false w x y z hw hz⟩
  rcases List.mem_cons.mp hu with h | hu
  · exact h ▸ le_refl _
  rcases List.mem_cons.mp hu with h | hu
  · rw [h]; exact le_of_lt hx
  rcases List.mem_cons.mp hu with h | hu
  · rw [h]; exact le_of_lt hy
  rcases List.mem_cons.mp hu with h | hu
  · rw [h]; exact le_of_lt hz
  · cases hu

theorem sel4_last (hw : coherenceOf [w, x, y, z] w < coherenceOf [w, x, y, z] z)
    (hx : coherenceOf [w, x, y, z] x < coherenceOf [w, x, y, z] z)
    (hy : coherenceOf [w, x, y, z] y < coherenceOf [w, x, y, z] z) :
    sel4 w x y z w = false ∧ sel4 w x y z x = false ∧ sel4 w x y z y = false ∧
      sel4 w x y z z = true := by
  have hz : z ∈ [w, x, y, z] :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  refine ⟨sel4_false w x y z hz hw, sel4_false w x y z hz hx, sel4_false w x y z hz hy,
    List.all_eq_true.mpr (fun u hu => decide_eq_true ?_)⟩
  rcases List.mem_cons.mp hu with h | hu
  · rw [h]; exact le_of_lt hw
  rcases List.mem_cons.mp hu with h | hu
  · rw [h]; exact le_of_lt hx
  rcases List.mem_cons.mp hu with h | hu
  · rw [h]; exact le_of_lt hy
  rcases List.mem_cons.mp hu with h | hu
  · exact h ▸ le_refl _
  · cases hu

end four

/-- `φ⁻ᵇ + φ⁻ᶜ < φ⁻ᵘ + φ⁻ᵛ` when `b ≥ u + 1` and `c ≥ u + 3`:
    `φ⁻⁽ᵘ⁺¹⁾ + φ⁻⁽ᵘ⁺³⁾ < φ⁻⁽ᵘ⁺¹⁾ + φ⁻⁽ᵘ⁺²⁾ = φ⁻ᵘ`. -/
theorem sum_lt_of_near_deep {u v b c : ℕ} (hb : u + 1 ≤ b) (hc : u + 3 ≤ c) :
    phiNegPow b + phiNegPow c < phiNegPow u + phiNegPow v :=
  calc phiNegPow b + phiNegPow c ≤ phiNegPow (u + 1) + phiNegPow (u + 3) :=
        add_le_add (phiNegPow_anti_le hb) (phiNegPow_anti_le hc)
    _ = phiNegPow (u + 3) + phiNegPow (u + 1) := add_comm _ _
    _ < phiNegPow (u + 2) + phiNegPow (u + 1) :=
        add_lt_add_right_zphi (phiNegPow_succ_lt (u + 2))
    _ = phiNegPow (u + 1) + phiNegPow (u + 2) := add_comm _ _
    _ = phiNegPow u := (phiNegPow_rec u).symm
    _ < phiNegPow u + phiNegPow v := lt_add_of_pos_right _ (PhiPos.phiNegPow_pos v)

/-! ## Step 3: the decision, from the six tensions alone -/

/-- Whether the outer right child `RⁿLRRR` wins: `m ≡ 1` or `5 (mod 6)`. -/
def outerR (m : ℕ) : Bool := m % 6 == 1 || m % 6 == 5

/-- The singleton the cousin step keeps. -/
def winner (m : ℕ) : IPres := bif outerR m then cd m else ca m

/-- **The decision, for any four occurrences carrying the cousin tensions.** -/
theorem sel_of_tensions (w x y z : IPres) (m : ℕ)
    (hwx : tEnd w x = 245 * m + 40) (hwz : tEnd w z = 35 * m + 8)
    (hxy : tEnd x y = 49 * m + 10) (hyz : tEnd y z = 245 * m + 46)
    (hwy : tEnd w y = 245 * (m / 6) + acOff (m % 6))
    (hxz : tEnd x z = 245 * (m / 6) + bdOff (m % 6)) :
    sel4 w x y z w = !outerR m ∧ sel4 w x y z x = false ∧ sel4 w x y z y = false ∧
      sel4 w x y z z = outerR m := by
  obtain ⟨j, i, hi, rfl⟩ := split6 m
  have hd : (6 * j + i) / 6 = j := by omega
  have hm : (6 * j + i) % 6 = i := by omega
  rw [hd, hm] at hwy hxz
  have ho : outerR (6 * j + i) = (i == 1 || i == 5) := by
    show ((6 * j + i) % 6 == 1 || (6 * j + i) % 6 == 5) = _
    rw [hm]
  rw [ho]
  -- The outer left child: `t(w,z) + 2` below `t(x,y)`, `t(x,z)`, `t(y,z)`,
  -- and `t(w,y) < t(x,z)`.
  have head : ∀ (a b : ℕ), tEnd w y = 245 * j + a → tEnd x z = 245 * j + b →
      35 * i + 12 ≤ a → 35 * i + 10 ≤ b → a < b →
      sel4 w x y z w = true ∧ sel4 w x y z x = false ∧ sel4 w x y z y = false ∧
        sel4 w x y z z = false := by
    intro a b ha hb h1 h2 h3
    refine sel4_head w x y z
      (lt_x_w w x y z (sum_lt_of_two_deeper ?_ ?_))
      (lt_y_w w x y z (sum_lt_of_two_deeper ?_ ?_))
      (lt_z_w w x y z (sum_lt_of_both_deeper ?_ ?_))
    · rw [hwz, hxy]; omega
    · rw [hwz, hb]; omega
    · rw [hwz, hxy]; omega
    · rw [hwz, hyz]; omega
    · rw [ha, hb]; omega
    · rw [hwx, hyz]; omega
  -- The outer right child: `t(w,z) + 2` below `t(w,x)`, `t(w,y)`, `t(x,y)`,
  -- `t(x,z) + 1 ≤ t(w,y)` and `t(x,z) + 3 ≤ t(w,x)`.
  have last : ∀ (a b : ℕ), tEnd w y = 245 * j + a → tEnd x z = 245 * j + b →
      35 * i + 10 ≤ a → b + 1 ≤ a → b + 3 ≤ 245 * i + 40 →
      sel4 w x y z w = false ∧ sel4 w x y z x = false ∧ sel4 w x y z y = false ∧
        sel4 w x y z z = true := by
    intro a b ha hb h1 h2 h3
    refine sel4_last w x y z
      (lt_w_z w x y z (sum_lt_of_near_deep ?_ ?_))
      (lt_x_z w x y z (sum_lt_of_two_deeper ?_ ?_))
      (lt_y_z w x y z (sum_lt_of_two_deeper ?_ ?_))
    · rw [ha, hb]; omega
    · rw [hwx, hb]; omega
    · rw [hwz, hwx]; omega
    · rw [hwz, hxy]; omega
    · rw [hwz, ha]; omega
    · rw [hwz, hxy]; omega
  match i, hi with
  | 0, _ => exact head 12 13 hwy hxz (by omega) (by omega) (by omega)
  | 1, _ => exact last 65 53 hwy hxz (by omega) (by omega) (by omega)
  | 2, _ => exact head 96 106 hwy hxz (by omega) (by omega) (by omega)
  | 3, _ => exact head 135 137 hwy hxz (by omega) (by omega) (by omega)
  | 4, _ => exact head 175 176 hwy hxz (by omega) (by omega) (by omega)
  | 5, _ => exact last 217 216 hwy hxz (by omega) (by omega) (by omega)
  | _ + 6, h => exact absurd h (by omega)

/-- The support of a four-member family from its four predicate values. -/
theorem support4_of_sel (w x y z : IPres) (m : ℕ)
    (h : sel4 w x y z w = !outerR m ∧ sel4 w x y z x = false ∧ sel4 w x y z y = false ∧
      sel4 w x y z z = outerR m) :
    support [w, x, y, z] = [bif outerR m then z else w] := by
  obtain ⟨hw, hx, hy, hz⟩ := h
  show List.filter (sel4 w x y z) [w, x, y, z] = _
  cases ho : outerR m
  · rw [ho] at hw hz
    simp only [List.filter_cons, List.filter_nil, hw, hx, hy, hz, Bool.not_false,
      Bool.false_eq_true, if_true, if_false, cond_false]
  · rw [ho] at hw hz
    simp only [List.filter_cons, List.filter_nil, hw, hx, hy, hz, Bool.not_true,
      Bool.false_eq_true, if_true, if_false, cond_true]

/-- **Theorem 16.11, Step 3, for every `m`.** From the cousin pair
    `{RⁿLLL, RⁿLRR}` with `n = 21m + 3`, Definition 8.1's support over
    the four children is the singleton `[RⁿLRRR]` when `m ≡ 1, 5 (mod 6)` and
    `[RⁿLLLL]` otherwise. -/
theorem step3_cousin_support (m : ℕ) : support (fam m) = [winner m] :=
  support4_of_sel _ _ _ _ m
    (sel_of_tensions _ _ _ _ m (t_ab m) (t_ad m) (t_bc m) (t_cd m) (t_ac m) (t_bd m))

/-- The book's sentence, "a singleton in every case". -/
theorem step3_cousin_singleton (m : ℕ) : ∃ v, support (fam m) = [v] :=
  ⟨winner m, step3_cousin_support m⟩

/-! ## The four children are the book's words -/

open Frame

theorem addr_a (m : ℕ) :
    (r (List.replicate (21 * m + 3) true ++ [false, false, false, false])).p = (ca m).p ∧
      (r (List.replicate (21 * m + 3) true ++ [false, false, false, false])).q = (ca m).q := by
  obtain ⟨g1, g2⟩ := RootChain.r_replicate_true (21 * m + 3) [false, false, false, false]
  rw [g1, g2, show (r [false, false, false, false]).p = 1 by decide,
    show (r [false, false, false, false]).q = 5 by decide]
  exact ⟨by show 1 + (21 * m + 3) * 5 = 105 * m + 16; ring, rfl⟩

theorem addr_b (m : ℕ) :
    (r (List.replicate (21 * m + 3) true ++ [false, false, false, true])).p = (cb m).p ∧
      (r (List.replicate (21 * m + 3) true ++ [false, false, false, true])).q = (cb m).q := by
  obtain ⟨g1, g2⟩ := RootChain.r_replicate_true (21 * m + 3) [false, false, false, true]
  rw [g1, g2, show (r [false, false, false, true]).p = 2 by decide,
    show (r [false, false, false, true]).q = 7 by decide]
  exact ⟨by show 2 + (21 * m + 3) * 7 = 147 * m + 23; ring, rfl⟩

theorem addr_c (m : ℕ) :
    (r (List.replicate (21 * m + 3) true ++ [false, true, true, false])).p = (cc m).p ∧
      (r (List.replicate (21 * m + 3) true ++ [false, true, true, false])).q = (cc m).q := by
  obtain ⟨g1, g2⟩ := RootChain.r_replicate_true (21 * m + 3) [false, true, true, false]
  rw [g1, g2, show (r [false, true, true, false]).p = 5 by decide,
    show (r [false, true, true, false]).q = 7 by decide]
  exact ⟨by show 5 + (21 * m + 3) * 7 = 147 * m + 26; ring, rfl⟩

theorem addr_d (m : ℕ) :
    (r (List.replicate (21 * m + 3) true ++ [false, true, true, true])).p = (cd m).p ∧
      (r (List.replicate (21 * m + 3) true ++ [false, true, true, true])).q = (cd m).q := by
  obtain ⟨g1, g2⟩ := RootChain.r_replicate_true (21 * m + 3) [false, true, true, true]
  rw [g1, g2, show (r [false, true, true, true]).p = 4 by decide,
    show (r [false, true, true, true]).q = 5 by decide]
  exact ⟨by show 4 + (21 * m + 3) * 5 = 105 * m + 19; ring, rfl⟩

/-! ## The coefficient vectors `(1,4), (2,5), (5,2), (4,1)` in `F_{RⁿL}` -/

/-- The frame `F_{RⁿL}`, `n = 21m + 3`. -/
def frameRnL (m : ℕ) : Frame := walk empty (List.replicate (21 * m + 3) true ++ [false])

theorem coeff_vectors :
    ((r [false, false, false]).p, (r [false, false, false]).q) = (1, 4) ∧
    ((r [false, false, true]).p, (r [false, false, true]).q) = (2, 5) ∧
    ((r [true, true, false]).p, (r [true, true, false]).q) = (5, 2) ∧
    ((r [true, true, true]).p, (r [true, true, true]).q) = (4, 1) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A child `RⁿL·v` is `M_{F_{RⁿL}}(r(v))`, by Lemma 16.10's reduction. -/
theorem combo_of_addr (m : ℕ) (v : Word) (A : IPres)
    (hA : (r (List.replicate (21 * m + 3) true ++ false :: v)).p = A.p ∧
      (r (List.replicate (21 * m + 3) true ++ false :: v)).q = A.q) :
    comboI (frameRnL m) (r v).p (r v).q (walk_mid_pos empty v).1 (walk_mid_pos empty v).2 = A := by
  have h := Beat11Bridge.lemma_16_10_reduction (frameRnL m) v
  have e : addressed (frameRnL m) v = r (List.replicate (21 * m + 3) true ++ false :: v) := by
    show (List.foldl select (List.foldl select empty (List.replicate (21 * m + 3) true ++
      [false])) v).mid
      = (List.foldl select empty (List.replicate (21 * m + 3) true ++ ([false] ++ v))).mid
    rw [← List.append_assoc,
      List.foldl_append (l := List.replicate (21 * m + 3) true ++ [false]) (l' := v)]
  rw [e] at h
  have h2 : IPres.ofPres? (r (List.replicate (21 * m + 3) true ++ false :: v)) = some A :=
    Beat11Bridge.ofPres?_eq_some (walk_mid_pos empty _) hA.1 hA.2
  exact Option.some.inj (h.symm.trans h2)

theorem ca_combo (m : ℕ) : comboI (frameRnL m) 1 4 (by decide) (by decide) = ca m :=
  combo_of_addr m [false, false, false] (ca m) (addr_a m)
theorem cb_combo (m : ℕ) : comboI (frameRnL m) 2 5 (by decide) (by decide) = cb m :=
  combo_of_addr m [false, false, true] (cb m) (addr_b m)
theorem cc_combo (m : ℕ) : comboI (frameRnL m) 5 2 (by decide) (by decide) = cc m :=
  combo_of_addr m [true, true, false] (cc m) (addr_c m)
theorem cd_combo (m : ℕ) : comboI (frameRnL m) 4 1 (by decide) (by decide) = cd m :=
  combo_of_addr m [true, true, true] (cd m) (addr_d m)

/-! ## The two concrete cousin steps, already certified in `RootOrbit` -/

/-- `{LLL, LRL} → {LLLR}`: `𝒬_L` at ticks 2 and 3. -/
theorem cousin_concrete_L :
    RootOrbit.activeWords RootOrbit.XL2 = [[false, false, false], [false, true, false]] ∧
      RootOrbit.activeWords RootOrbit.XL3 = [[false, false, false, true]] :=
  ⟨RootOrbit.theorem_16_5_polarized_L.2.1, RootOrbit.theorem_16_5_polarized_L.2.2.1⟩

/-- `{RLR, RRR} → {RRRL}`: `𝒬_R` at ticks 2 and 3. -/
theorem cousin_concrete_R :
    RootOrbit.activeWords RootOrbit.XR2 = [[true, false, true], [true, true, true]] ∧
      RootOrbit.activeWords RootOrbit.XR3 = [[true, true, true, false]] :=
  ⟨RootOrbit.theorem_16_5_polarized_R.2.1, RootOrbit.theorem_16_5_polarized_R.2.2.1⟩

/-! ## The mirror family, by side covariance -/

/-- `LⁿRRRR, LⁿRRRL, LⁿRLLR, LⁿRLLL`. -/
def mfam (m : ℕ) : List IPres := [Inv (ca m), Inv (cb m), Inv (cc m), Inv (cd m)]

/-- **Step 3's mirror.** `Inv` preserves every tension (Theorem 7.8), so the
    decision is the same: `[LⁿRLLL]` at `m ≡ 1, 5 (mod 6)`, else `[LⁿRRRR]`. -/
theorem step3_mirror_support (m : ℕ) : support (mfam m) = [Inv (winner m)] := by
  have h := support4_of_sel _ _ _ _ m
    (sel_of_tensions (Inv (ca m)) (Inv (cb m)) (Inv (cc m)) (Inv (cd m)) m
      (by rw [tEnd_side_invariant]; exact t_ab m) (by rw [tEnd_side_invariant]; exact t_ad m)
      (by rw [tEnd_side_invariant]; exact t_bc m) (by rw [tEnd_side_invariant]; exact t_cd m)
      (by rw [tEnd_side_invariant]; exact t_ac m) (by rw [tEnd_side_invariant]; exact t_bd m))
  show _ = [Inv (bif outerR m then cd m else ca m)]
  cases ho : outerR m
  · rw [ho] at h; exact h
  · rw [ho] at h; exact h

theorem maddr_a (m : ℕ) :
    (r (List.replicate (21 * m + 3) false ++ [true, true, true, true])).p = (Inv (ca m)).p ∧
      (r (List.replicate (21 * m + 3) false ++ [true, true, true, true])).q = (Inv (ca m)).q := by
  obtain ⟨g1, g2⟩ := RootChain.r_replicate_false (21 * m + 3) [true, true, true, true]
  rw [g1, g2, show (r [true, true, true, true]).p = 5 by decide,
    show (r [true, true, true, true]).q = 1 by decide]
  exact ⟨rfl, by show 1 + (21 * m + 3) * 5 = 105 * m + 16; ring⟩

theorem maddr_b (m : ℕ) :
    (r (List.replicate (21 * m + 3) false ++ [true, true, true, false])).p = (Inv (cb m)).p ∧
      (r (List.replicate (21 * m + 3) false ++ [true, true, true, false])).q = (Inv (cb m)).q := by
  obtain ⟨g1, g2⟩ := RootChain.r_replicate_false (21 * m + 3) [true, true, true, false]
  rw [g1, g2, show (r [true, true, true, false]).p = 7 by decide,
    show (r [true, true, true, false]).q = 2 by decide]
  exact ⟨rfl, by show 2 + (21 * m + 3) * 7 = 147 * m + 23; ring⟩

theorem maddr_c (m : ℕ) :
    (r (List.replicate (21 * m + 3) false ++ [true, false, false, true])).p = (Inv (cc m)).p ∧
      (r (List.replicate (21 * m + 3) false ++ [true, false, false, true])).q = (Inv (cc m)).q := by
  obtain ⟨g1, g2⟩ := RootChain.r_replicate_false (21 * m + 3) [true, false, false, true]
  rw [g1, g2, show (r [true, false, false, true]).p = 7 by decide,
    show (r [true, false, false, true]).q = 5 by decide]
  exact ⟨rfl, by show 5 + (21 * m + 3) * 7 = 147 * m + 26; ring⟩

theorem maddr_d (m : ℕ) :
    (r (List.replicate (21 * m + 3) false ++ [true, false, false, false])).p = (Inv (cd m)).p ∧
      (r (List.replicate (21 * m + 3) false ++ [true, false, false, false])).q = (Inv (cd m)).q
        := by
  obtain ⟨g1, g2⟩ := RootChain.r_replicate_false (21 * m + 3) [true, false, false, false]
  rw [g1, g2, show (r [true, false, false, false]).p = 5 by decide,
    show (r [true, false, false, false]).q = 4 by decide]
  exact ⟨rfl, by show 4 + (21 * m + 3) * 5 = 105 * m + 19; ring⟩

/-! ## Step 3 on the tick carrier -/

section carrier

open Mat2 Word RatioSpace Advance Accumulation RootOrbit Beat Beat11Bridge RootChainCarrier

variable {x y : Core} {m : ℕ} (s : ℕ) (p : Provenance)

theorem cousin_xL (hx : fullWord x = List.replicate (21 * m + 3) true ++ [false, false, false]) :
    addrOf 1 (childCore x false s p) = some (ca m) := by
  rw [addrOf_child, hx, List.append_assoc]
  exact ofPres?_eq_some (walk_mid_pos empty _) (addr_a m).1 (addr_a m).2

theorem cousin_xR (hx : fullWord x = List.replicate (21 * m + 3) true ++ [false, false, false]) :
    addrOf 1 (childCore x true s p) = some (cb m) := by
  rw [addrOf_child, hx, List.append_assoc]
  exact ofPres?_eq_some (walk_mid_pos empty _) (addr_b m).1 (addr_b m).2

theorem cousin_yL (hy : fullWord y = List.replicate (21 * m + 3) true ++ [false, true, true]) :
    addrOf 1 (childCore y false s p) = some (cc m) := by
  rw [addrOf_child, hy, List.append_assoc]
  exact ofPres?_eq_some (walk_mid_pos empty _) (addr_c m).1 (addr_c m).2

theorem cousin_yR (hy : fullWord y = List.replicate (21 * m + 3) true ++ [false, true, true]) :
    addrOf 1 (childCore y true s p) = some (cd m) := by
  rw [addrOf_child, hy, List.append_assoc]
  exact ofPres?_eq_some (walk_mid_pos empty _) (addr_d m).1 (addr_d m).2

variable {archive : List Core} {active : List QuestionId}

/-- **The admitted family of the cousin step is `fam m`.** -/
theorem cousin_admittedFam (hpair : archive.filter (fun d => d.id ∈ active) = [x, y])
    (hx : fullWord x = List.replicate (21 * m + 3) true ++ [false, false, false])
    (hy : fullWord y = List.replicate (21 * m + 3) true ++ [false, true, true]) :
    admittedFam 1 s p (proposals archive active) = fam m := by
  unfold admittedFam
  rw [root_admittedCores s p hpair, List.filterMap_cons_some (cousin_xL s p hx),
    List.filterMap_cons_some (cousin_xR s p hx), List.filterMap_cons_some (cousin_yL s p hy),
    List.filterMap_cons_some (cousin_yR s p hy)]
  rfl

/-- **Theorem 16.11, Step 3, on the tree.** From the active cousin pair
    `[RⁿLLL, RⁿLRR]`, `n = 21m + 3`, at observer `ε`, the one-tick advance under
    `axiomSelect` keeps exactly one core: `RⁿLRRR` when `m ≡ 1, 5 (mod 6)`,
    `RⁿLLLL` otherwise. -/
theorem cousin_step (hpair : archive.filter (fun d => d.id ∈ active) = [x, y])
    (hx : fullWord x = List.replicate (21 * m + 3) true ++ [false, false, false])
    (hy : fullWord y = List.replicate (21 * m + 3) true ++ [false, true, true]) :
    axiomSelect 1 s p (proposals archive active)
      = [bif outerR m then (childCore y true s p).id else (childCore x false s p).id] := by
  obtain ⟨pa, pb, pc, pd⟩ :=
    sel_of_tensions _ _ _ _ m (t_ab m) (t_ad m) (t_bc m) (t_cd m) (t_ac m) (t_bd m)
  unfold axiomSelect
  simp only []
  rw [root_admittedCores s p hpair, cousin_admittedFam s p hpair hx hy]
  rw [List.filter_cons, List.filter_cons, List.filter_cons, List.filter_cons]
  rw [cousin_xL s p hx, cousin_xR s p hx, cousin_yL s p hy, cousin_yR s p hy]
  dsimp only
  have pb' : (fam m).all (fun z => decide (coherenceOf (fam m) z ≤ coherenceOf (fam m) (cb m)))
      = false := pb
  have pc' : (fam m).all (fun z => decide (coherenceOf (fam m) z ≤ coherenceOf (fam m) (cc m)))
      = false := pc
  cases ho : outerR m
  · rw [ho] at pa pd
    have pa' : (fam m).all (fun z => decide (coherenceOf (fam m) z ≤ coherenceOf (fam m) (ca m)))
        = true := pa
    have pd' : (fam m).all (fun z => decide (coherenceOf (fam m) z ≤ coherenceOf (fam m) (cd m)))
        = false := pd
    simp only [pa', pb', pc', pd', Bool.false_eq_true, decide_false, decide_true, if_true,
      if_false]
    rfl
  · rw [ho] at pa pd
    have pa' : (fam m).all (fun z => decide (coherenceOf (fam m) z ≤ coherenceOf (fam m) (ca m)))
        = false := pa
    have pd' : (fam m).all (fun z => decide (coherenceOf (fam m) z ≤ coherenceOf (fam m) (cd m)))
        = true := pd
    simp only [pa', pb', pc', pd', Bool.false_eq_true, decide_false, decide_true, if_true,
      if_false]
    rfl

/-- The retained core's full word: `RⁿLLLL` or `RⁿLRRR`. -/
theorem cousin_step_words
    (hx : fullWord x = List.replicate (21 * m + 3) true ++ [false, false, false])
    (hy : fullWord y = List.replicate (21 * m + 3) true ++ [false, true, true]) :
    fullWord (childCore x false s p) = List.replicate (21 * m + 3) true ++ [false, false, false,
      false] ∧
      fullWord (childCore y true s p) = List.replicate (21 * m + 3) true ++ [false, true, true,
        true] := by
  rw [child_fullWord, child_fullWord, hx, hy]
  exact ⟨List.append_assoc _ _ _, List.append_assoc _ _ _⟩

/-- **Step 3 on the tick carrier.** If a lawful carrier's observer sits at `ε`
    and its active family is the cousin pair `[RⁿLLL, RⁿLRR]`, `n = 21m + 3`,
    advancing it under `axiomSelect` leaves exactly one core active. -/
theorem advanceCarrier_active_cousin {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) {x y : Core} {m : ℕ}
    (hMO : X.observer.matrix = 1)
    (hpair : X.archive.filter (fun d => d.id ∈ X.active) = [x, y])
    (hx : fullWord x = List.replicate (21 * m + 3) true ++ [false, false, false])
    (hy : fullWord y = List.replicate (21 * m + 3) true ++ [false, true, true]) :
    (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active
      = [bif outerR m then (childCore y true s p).id else (childCore x false s p).id] := by
  show axiomSelect X.observer.matrix s p (proposals X.archive X.active) = _
  rw [hMO]
  exact cousin_step s p hpair hx hy

/-! ### The mirror family on the carrier

The retained pair from `LⁿR` at `n ≡ 3 (mod 21)` is `[LⁿRLL, LⁿRRR]`
(`Step2Family.sibling_step_LnR_tie`), so the carrier proposes the children in
the order `LⁿRLLL, LⁿRLLR, LⁿRRRL, LⁿRRRR`: `mfam` reversed. The coherence value is a sum
over the family (`coherenceOf_perm`, Theorem 8.9), so the decision is
`step3_mirror_support`'s, read in the other order. -/

/-- The mirror children in carrier order. -/
def mfamC (m : ℕ) : List IPres := [Inv (cd m), Inv (cc m), Inv (cb m), Inv (ca m)]

theorem mfamC_perm (m : ℕ) : (mfamC m).Perm (mfam m) :=
  show (mfam m).reverse.Perm (mfam m) from List.reverse_perm _

/-- Definition 8.1's predicate on the carrier-order family is `sel4` on `mfam`. -/
theorem mselC (m : ℕ) (v : IPres) :
    (mfamC m).all (fun z => decide (coherenceOf (mfamC m) z ≤ coherenceOf (mfamC m) v))
      = sel4 (Inv (ca m)) (Inv (cb m)) (Inv (cc m)) (Inv (cd m)) v := by
  have hp := mfamC_perm m
  have hc : ∀ u, coherenceOf (mfamC m) u = coherenceOf (mfam m) u := coherenceOf_perm hp
  show _ = (mfam m).all (fun u => decide (coherenceOf (mfam m) u ≤ coherenceOf (mfam m) v))
  simp only [hc]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun h u hu => h u (hp.mem_iff.mpr hu), fun h u hu => h u (hp.mem_iff.mp hu)⟩

theorem mcousin_xL (hx : fullWord x = List.replicate (21 * m + 3) false ++ [true, false, false]) :
    addrOf 1 (childCore x false s p) = some (Inv (cd m)) := by
  rw [addrOf_child, hx, List.append_assoc]
  exact ofPres?_eq_some (walk_mid_pos empty _) (maddr_d m).1 (maddr_d m).2

theorem mcousin_xR (hx : fullWord x = List.replicate (21 * m + 3) false ++ [true, false, false]) :
    addrOf 1 (childCore x true s p) = some (Inv (cc m)) := by
  rw [addrOf_child, hx, List.append_assoc]
  exact ofPres?_eq_some (walk_mid_pos empty _) (maddr_c m).1 (maddr_c m).2

theorem mcousin_yL (hy : fullWord y = List.replicate (21 * m + 3) false ++ [true, true, true]) :
    addrOf 1 (childCore y false s p) = some (Inv (cb m)) := by
  rw [addrOf_child, hy, List.append_assoc]
  exact ofPres?_eq_some (walk_mid_pos empty _) (maddr_b m).1 (maddr_b m).2

theorem mcousin_yR (hy : fullWord y = List.replicate (21 * m + 3) false ++ [true, true, true]) :
    addrOf 1 (childCore y true s p) = some (Inv (ca m)) := by
  rw [addrOf_child, hy, List.append_assoc]
  exact ofPres?_eq_some (walk_mid_pos empty _) (maddr_a m).1 (maddr_a m).2

/-- **The admitted family of the mirror cousin step is `mfamC m`.** -/
theorem mcousin_admittedFam (hpair : archive.filter (fun d => d.id ∈ active) = [x, y])
    (hx : fullWord x = List.replicate (21 * m + 3) false ++ [true, false, false])
    (hy : fullWord y = List.replicate (21 * m + 3) false ++ [true, true, true]) :
    admittedFam 1 s p (proposals archive active) = mfamC m := by
  unfold admittedFam
  rw [root_admittedCores s p hpair, List.filterMap_cons_some (mcousin_xL s p hx),
    List.filterMap_cons_some (mcousin_xR s p hx), List.filterMap_cons_some (mcousin_yL s p hy),
    List.filterMap_cons_some (mcousin_yR s p hy)]
  rfl

/-- **Theorem 16.11, Step 3's mirror, on the tree.** From the active pair
    `[LⁿRLL, LⁿRRR]`, `n = 21m + 3`, at observer `ε`, the one-tick advance under
    `axiomSelect` keeps exactly one core: `LⁿRLLL` when `m ≡ 1, 5 (mod 6)`,
    `LⁿRRRR` otherwise. -/
theorem mcousin_step (hpair : archive.filter (fun d => d.id ∈ active) = [x, y])
    (hx : fullWord x = List.replicate (21 * m + 3) false ++ [true, false, false])
    (hy : fullWord y = List.replicate (21 * m + 3) false ++ [true, true, true]) :
    axiomSelect 1 s p (proposals archive active)
      = [bif outerR m then (childCore x false s p).id else (childCore y true s p).id] := by
  obtain ⟨pa, pb, pc, pd⟩ :=
    sel_of_tensions (Inv (ca m)) (Inv (cb m)) (Inv (cc m)) (Inv (cd m)) m
      (by rw [tEnd_side_invariant]; exact t_ab m) (by rw [tEnd_side_invariant]; exact t_ad m)
      (by rw [tEnd_side_invariant]; exact t_bc m) (by rw [tEnd_side_invariant]; exact t_cd m)
      (by rw [tEnd_side_invariant]; exact t_ac m) (by rw [tEnd_side_invariant]; exact t_bd m)
  unfold axiomSelect
  simp only []
  rw [root_admittedCores s p hpair, mcousin_admittedFam s p hpair hx hy]
  rw [List.filter_cons, List.filter_cons, List.filter_cons, List.filter_cons]
  rw [mcousin_xL s p hx, mcousin_xR s p hx, mcousin_yL s p hy, mcousin_yR s p hy]
  dsimp only
  simp only [mselC]
  cases ho : outerR m
  · rw [ho] at pa pd
    simp only [pa, pb, pc, pd, Bool.not_false, Bool.false_eq_true, decide_false, decide_true,
      if_true, if_false]
    rfl
  · rw [ho] at pa pd
    simp only [pa, pb, pc, pd, Bool.not_true, Bool.false_eq_true, decide_false, decide_true,
      if_true, if_false]
    rfl

/-- **Step 3's mirror on the tick carrier.** If a lawful carrier's observer sits
    at `ε` and its active family is `[LⁿRLL, LⁿRRR]`, `n = 21m + 3`, advancing it
    under `axiomSelect` leaves exactly one core active. -/
theorem advanceCarrier_active_mcousin {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) {x y : Core} {m : ℕ}
    (hMO : X.observer.matrix = 1)
    (hpair : X.archive.filter (fun d => d.id ∈ X.active) = [x, y])
    (hx : fullWord x = List.replicate (21 * m + 3) false ++ [true, false, false])
    (hy : fullWord y = List.replicate (21 * m + 3) false ++ [true, true, true]) :
    (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active
      = [bif outerR m then (childCore x false s p).id else (childCore y true s p).id] := by
  show axiomSelect X.observer.matrix s p (proposals X.archive X.active) = _
  rw [hMO]
  exact mcousin_step s p hpair hx hy


end carrier

end Step3Cousin
end Two
end RatioSpace
