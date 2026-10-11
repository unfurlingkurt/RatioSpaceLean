/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.FamilyClassification
/-!
  Elements II §16 Theorem 16.11, Step 2 — the finite remainder.

  **Book statement (Step 2, sibling step, remainder).** The frames failing one
  of Step 1's three inequalities have all entries at most 205; there are exactly
  527 of them; direct computation gives a singleton in 522 and the pairs
  `{LR,RL}`, `{LLL,LRL}`, `{RLR,RRR}`, `{RRRLLL,RRRLRR}`, `{LLLRLL,LLLRRR}` at
  the frames of `ε, L, R, RRRL, LLLR`. The frames with `|D| ≤ 20` outside the
  families `RⁿL`, `LⁿR` have every entry at most 41; there are exactly 107,
  entries at most 20, all singletons except the root.

  **Computed before written** (exact-integer mirror of `grand`, `tEnd`,
  `coherenceOf`, `support`, no floats): 527 non-Generic frames, maximum entry
  202, maximum depth 202, maximum tension 607; 522 singletons and exactly the
  five named pairs. With `|D| ≤ 20`, `p₁ ≠ p₀`, `q₁ ≠ q₀`: 107 frames, maximum
  entry 20 (30 of them Generic), every one a singleton except the root. No book
  statement was found false. The entry bound proved here is 40, one better than
  the book's 41.

  **How.** A fuel-bounded tree walk `chkA` stops at Generic frames, which is
  sound because `Generic` is upward closed along the tree (`generic_select`):
  every entry only grows. At each visited frame it reads the four `selPred`
  bits of Definition 8.1's filter and accepts a singleton or one of the
  five named pairs at its own word (`okMask`). The kernel evaluates
  `chkA 210 Frame.empty [] = true` by `decide +kernel` (no `native_decide`);
  `chkA_sound` turns that into the statement for every word. Part (B) is the
  same walk pruned at entry 40, with the bound `bound_nat` proved from
  unimodularity (`p₁ < p₀` or `q₁ > q₀` cases each expand `D` into nonnegative
  products bounded by 20). `count_*` certify 527 / 522 / 107 / entries ≤ 20 on
  the same traversals.

  **Built.**
  * `step2_nongeneric`: every non-Generic tree frame satisfies `Outcome`
    (singleton, or the named pair at `ε, L, R, RRRL, LLLR`).
  * `step2_smallD`: every tree frame with `|D| ≤ 20`, `p₁ ≠ p₀`, `q₁ ≠ q₀`
    satisfies `Outcome` (only the root is a pair).
  * `step2_complete`: every tree frame, assembled from Step 1
    (`step1_unique_pos/neg`), the families (`frn_of`/`fm_of` identify
    `q₁ = q₀` with `RⁿL` and `p₁ = p₀` with `LⁿR`; `step2_family_support`,
    `mirror_support`, the ties) and (A), (B).

  Every theorem `propext`/`Quot.sound` or less.

  **Not built here:** the carrier/`axiomSelect` restatement of
  `step2_complete`, and the induction assembling clauses 1-4.
-/
set_option linter.style.show false

namespace RatioSpace
namespace Two
namespace Step2Remainder

open Beat11

/-! ## Outcomes, read off the filter's four bits -/

/-- The four bits of Definition 8.1's filter on the grandchildren. -/
def mask (F : Frame) : List Bool := (grand F).map (selPred F)

/-- **The book's Step 2 conclusion at the frame reached by `w`**: a singleton,
    or one of the five named pairs at its own frame. -/
def Outcome (w : List Bool) (F : Frame) : Prop :=
  support (grand F) = [gLL F] ∨ support (grand F) = [gLR F] ∨
  support (grand F) = [gRL F] ∨ support (grand F) = [gRR F] ∨
  (w = [] ∧ support (grand F) = [gLR F, gRL F]) ∨
  (w = [false] ∧ support (grand F) = [gLL F, gRL F]) ∨
  (w = [true] ∧ support (grand F) = [gLR F, gRR F]) ∨
  (w = [true, true, true, false] ∧ support (grand F) = [gLL F, gRR F]) ∨
  (w = [false, false, false, true] ∧ support (grand F) = [gLL F, gRR F])

/-- The Boolean form of `Outcome`, on the mask. -/
def okMask (u : List Bool) (m : List Bool) : Bool :=
  decide (m = [true, false, false, false]) || decide (m = [false, true, false, false]) ||
  decide (m = [false, false, true, false]) || decide (m = [false, false, false, true]) ||
  (decide (u = []) && decide (m = [false, true, true, false])) ||
  (decide (u = [false]) && decide (m = [true, false, true, false])) ||
  (decide (u = [true]) && decide (m = [false, true, false, true])) ||
  (decide (u = [true, true, true, false]) && decide (m = [true, false, false, true])) ||
  (decide (u = [false, false, false, true]) && decide (m = [true, false, false, true]))

theorem support_eq_filter (F : Frame) :
    support (grand F) = List.filter (selPred F) [gLL F, gLR F, gRL F, gRR F] := rfl

theorem support_bits {F : Frame} {s1 s2 s3 s4 : Bool} (h : mask F = [s1, s2, s3, s4]) :
    selPred F (gLL F) = s1 ∧ selPred F (gLR F) = s2 ∧ selPred F (gRL F) = s3 ∧
      selPred F (gRR F) = s4 := by
  obtain ⟨h1, h⟩ := List.cons.inj h
  obtain ⟨h2, h⟩ := List.cons.inj h
  obtain ⟨h3, h⟩ := List.cons.inj h
  obtain ⟨h4, _⟩ := List.cons.inj h
  exact ⟨h1, h2, h3, h4⟩

theorem okMask_sound (u : List Bool) (F : Frame) (h : okMask u (mask F) = true) :
    Outcome u F := by
  simp only [okMask, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold Outcome
  rw [support_eq_filter]
  rcases h with ((((((((h | h) | h) | h) | ⟨hu, h⟩) | ⟨hu, h⟩) | ⟨hu, h⟩) | ⟨hu, h⟩) | ⟨hu, h⟩) <;>
    obtain ⟨h1, h2, h3, h4⟩ := support_bits h <;>
    simp only [List.filter, h1, h2, h3, h4]
  · exact Or.inl trivial
  · exact Or.inr (Or.inl trivial)
  · exact Or.inr (Or.inr (Or.inl trivial))
  · exact Or.inr (Or.inr (Or.inr (Or.inl trivial)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, trivial⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, trivial⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, trivial⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, trivial⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hu, trivial⟩)))))))

/-! ## `Generic` is upward closed along the tree -/

theorem generic_mono {F G : Frame} (h1 : F.plus.p ≤ G.plus.p) (h2 : F.plus.q ≤ G.plus.q)
    (h3 : F.minus.p ≤ G.minus.p) (h4 : F.minus.q ≤ G.minus.q) (hg : Generic F) :
    Generic G := by
  refine ⟨le_trans hg.hA (Nat.mul_le_mul (by omega) (by omega)),
    le_trans hg.hB (Nat.mul_le_mul (by omega) (by omega)), ?_⟩
  have a := Nat.mul_le_mul (Nat.mul_le_mul_left 33 h1) h2
  have b := Nat.mul_le_mul (Nat.mul_le_mul_left 27 h1) h4
  have c := Nat.mul_le_mul (Nat.mul_le_mul_left 27 h3) h2
  have d := Nat.mul_le_mul (Nat.mul_le_mul_left 33 h3) h4
  have e := hg.hC
  omega

theorem generic_select (F : Frame) (b : Bool) (hg : Generic F) :
    Generic (Frame.select F b) := by
  cases b
  · exact generic_mono (F := F) (G := Frame.stepL F)
      (show F.plus.p ≤ F.plus.p + F.minus.p by omega)
      (show F.plus.q ≤ F.plus.q + F.minus.q by omega) (le_refl _) (le_refl _) hg
  · exact generic_mono (F := F) (G := Frame.stepR F) (le_refl _) (le_refl _)
      (show F.minus.p ≤ F.plus.p + F.minus.p by omega)
      (show F.minus.q ≤ F.plus.q + F.minus.q by omega) hg

theorem generic_walk : ∀ (w : List Bool) (F : Frame), Generic F → Generic (Frame.walk F w)
  | [], _, h => h
  | b :: w, F, h => generic_walk w (Frame.select F b) (generic_select F b h)

theorem walk_append' (F : Frame) (u w : List Bool) :
    Frame.walk F (u ++ w) = Frame.walk (Frame.walk F u) w :=
  List.foldl_append

/-- `Generic`, as a Boolean. -/
def genB (F : Frame) : Bool :=
  decide (206 ≤ (F.plus.p + 3 * F.minus.p) * (F.plus.q + 3 * F.minus.q)) &&
  decide (206 ≤ (3 * F.plus.p + F.minus.p) * (3 * F.plus.q + F.minus.q)) &&
  decide (440 ≤ 33 * F.plus.p * F.plus.q + 27 * F.plus.p * F.minus.q
    + 27 * F.minus.p * F.plus.q + 33 * F.minus.p * F.minus.q)

theorem generic_of_genB {F : Frame} (h : genB F = true) : Generic F := by
  simp only [genB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem genB_of_generic {F : Frame} (h : Generic F) : genB F = true := by
  simp only [genB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h.hA, h.hB⟩, h.hC⟩

/-! ## (A) The non-Generic frames -/

/-- The tree walk of Step 2: stop at a Generic frame, otherwise check the four
    bits at this frame's own word and descend. -/
def chkA : ℕ → Frame → List Bool → Bool
  | 0, F, _ => genB F
  | n + 1, F, u => genB F || (okMask u (mask F) &&
      chkA n (Frame.stepL F) (u ++ [false]) && chkA n (Frame.stepR F) (u ++ [true]))

theorem chkA_sound : ∀ (w : List Bool) (n : ℕ) (u : List Bool),
    chkA n (Frame.walk Frame.empty u) u = true →
    ¬ Generic (Frame.walk Frame.empty (u ++ w)) →
    Outcome (u ++ w) (Frame.walk Frame.empty (u ++ w)) := by
  intro w
  induction w with
  | nil =>
    intro n u hc hng
    rw [List.append_nil] at hng ⊢
    cases n with
    | zero => exact absurd (generic_of_genB hc) hng
    | succ n =>
      simp only [chkA, Bool.or_eq_true, Bool.and_eq_true] at hc
      rcases hc with hg | ⟨⟨hok, _⟩, _⟩
      · exact absurd (generic_of_genB hg) hng
      · exact okMask_sound _ _ hok
  | cons b w ih =>
    intro n u hc hng
    have hng' : ¬ Generic (Frame.walk Frame.empty u) := fun hg =>
      hng (by rw [walk_append']; exact generic_walk _ _ hg)
    cases n with
    | zero => exact absurd (generic_of_genB hc) hng'
    | succ n =>
      simp only [chkA, Bool.or_eq_true, Bool.and_eq_true] at hc
      rcases hc with hg | ⟨⟨_, hL⟩, hR⟩
      · exact absurd (generic_of_genB hg) hng'
      · have e : u ++ b :: w = (u ++ [b]) ++ w := by rw [List.append_assoc]; rfl
        rw [e] at hng ⊢
        refine ih n (u ++ [b]) ?_ hng
        rw [Frame.walk_append]
        cases b
        · exact hL
        · exact hR

/-- **The kernel's enumeration**: every non-Generic frame of the tree (527 of
    them, depth at most 202) gives a singleton or its named pair. -/
theorem chkA_root : chkA 210 Frame.empty [] = true := by decide +kernel

/-- **Theorem 16.11, Step 2, remainder (A).** At every frame of the tree that
    fails one of Step 1's three inequalities, the maximizer set of the four
    grandchildren is a singleton, except at `ε, L, R, RRRL, LLLR`, where it is
    the book's named pair. -/
theorem step2_nongeneric (w : List Bool) (h : ¬ Generic (Frame.walk Frame.empty w)) :
    Outcome w (Frame.walk Frame.empty w) :=
  chkA_sound w 210 [] chkA_root h

/-! ## (B) `|D| ≤ 20` outside the two families -/

/-- **The book's bound, sharpened to 40.** Unimodularity with `|D| ≤ 20`,
    `p₁ ≠ p₀`, `q₁ ≠ q₀` bounds every entry. -/
theorem bound_nat (p1 q1 p0 q0 : ℕ) (hc : p1 * q0 = q1 * p0 + 1)
    (hD1 : p1 * q1 ≤ p0 * q0 + 20) (hD2 : p0 * q0 ≤ p1 * q1 + 20)
    (hp : p1 ≠ p0) (hq : q1 ≠ q0) :
    p1 ≤ 40 ∧ q1 ≤ 40 ∧ p0 ≤ 40 ∧ q0 ≤ 40 := by
  rcases Nat.lt_or_gt_of_ne hq with hq | hq
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hq
    rcases Nat.lt_or_gt_of_ne hp with hp | hp
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hp
      have x : (p1 + e + 1) * (q1 + d + 1)
          = p1 * q1 + p1 * d + p1 + e * q1 + e * d + e + q1 + d + 1 := by ring
      rw [x] at hD2
      exact ⟨by omega, by omega, by omega, by omega⟩
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hp
      have x : (p0 + e + 1) * (q1 + d + 1)
          = q1 * p0 + p0 * d + p0 + e * q1 + e * d + e + q1 + d + 1 := by ring
      rw [x] at hc
      exact ⟨by omega, by omega, by omega, by omega⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hq
    rcases Nat.lt_or_gt_of_ne hp with hp | hp
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hp
      have x : (q0 + d + 1) * (p1 + e + 1)
          = p1 * q0 + p1 * d + p1 + e * q0 + e * d + e + q0 + d + 1 := by ring
      rw [x] at hc
      exact ⟨by omega, by omega, by omega, by omega⟩
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hp
      have x : (p0 + e + 1) * (q0 + d + 1)
          = p0 * q0 + p0 * d + p0 + e * q0 + e * d + e + q0 + d + 1 := by ring
      rw [x] at hD1
      exact ⟨by omega, by omega, by omega, by omega⟩

/-- The hypotheses of (B) on a frame. -/
structure SmallD (F : Frame) : Prop where
  hD1 : F.plus.p * F.plus.q ≤ F.minus.p * F.minus.q + 20
  hD2 : F.minus.p * F.minus.q ≤ F.plus.p * F.plus.q + 20
  hp : F.plus.p ≠ F.minus.p
  hq : F.plus.q ≠ F.minus.q

/-- All four entries at most 40. -/
def Bounded (F : Frame) : Prop :=
  F.plus.p ≤ 40 ∧ F.plus.q ≤ 40 ∧ F.minus.p ≤ 40 ∧ F.minus.q ≤ 40

theorem bounded_of_smallD {F : Frame} (h : SmallD F) : Bounded F :=
  bound_nat _ _ _ _ F.contact h.hD1 h.hD2 h.hp h.hq

theorem bounded_select {F : Frame} {b : Bool} (h : Bounded (Frame.select F b)) :
    Bounded F := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases b
  · exact ⟨le_trans (Nat.le_add_right _ _) h1, le_trans (Nat.le_add_right _ _) h2, h3, h4⟩
  · exact ⟨h1, h2, le_trans (Nat.le_add_left _ _) h3, le_trans (Nat.le_add_left _ _) h4⟩

theorem bounded_walk : ∀ (w : List Bool) (F : Frame), Bounded (Frame.walk F w) → Bounded F
  | [], _, h => h
  | _ :: w, _, h => bounded_select (bounded_walk w _ h)

def boundB (F : Frame) : Bool :=
  decide (F.plus.p ≤ 40) && decide (F.plus.q ≤ 40) &&
  decide (F.minus.p ≤ 40) && decide (F.minus.q ≤ 40)

def needB (F : Frame) : Bool :=
  decide (F.plus.p * F.plus.q ≤ F.minus.p * F.minus.q + 20) &&
  decide (F.minus.p * F.minus.q ≤ F.plus.p * F.plus.q + 20) &&
  !(decide (F.plus.p = F.minus.p)) && !(decide (F.plus.q = F.minus.q))

theorem boundB_of {F : Frame} (h : Bounded F) : boundB F = true := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [boundB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem needB_of {F : Frame} (h : SmallD F) : needB F = true := by
  simp only [needB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not]
  exact ⟨⟨⟨h.hD1, h.hD2⟩, h.hp⟩, h.hq⟩

/-- The tree walk of (B): prune at entry 40, check the four bits where
    `|D| ≤ 20` off the families. -/
def chkB : ℕ → Frame → List Bool → Bool
  | 0, F, _ => !(boundB F)
  | n + 1, F, u => !(boundB F) || ((!(needB F) || okMask u (mask F)) &&
      chkB n (Frame.stepL F) (u ++ [false]) && chkB n (Frame.stepR F) (u ++ [true]))

theorem chkB_sound : ∀ (w : List Bool) (n : ℕ) (u : List Bool),
    chkB n (Frame.walk Frame.empty u) u = true →
    SmallD (Frame.walk Frame.empty (u ++ w)) →
    Outcome (u ++ w) (Frame.walk Frame.empty (u ++ w)) := by
  intro w
  induction w with
  | nil =>
    intro n u hc hs
    rw [List.append_nil] at hs ⊢
    have hb := boundB_of (bounded_of_smallD hs)
    have hn := needB_of hs
    cases n with
    | zero => simp [chkB, hb] at hc
    | succ n =>
      simp only [chkB, hb, hn, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hc
      exact okMask_sound _ _ hc.1.1
  | cons b w ih =>
    intro n u hc hs
    have hb : boundB (Frame.walk Frame.empty u) = true := boundB_of
      (bounded_walk (b :: w) _ (by rw [← walk_append']; exact bounded_of_smallD hs))
    cases n with
    | zero => simp [chkB, hb] at hc
    | succ n =>
      simp only [chkB, hb, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hc
      obtain ⟨⟨_, hL⟩, hR⟩ := hc
      have e : u ++ b :: w = (u ++ [b]) ++ w := by rw [List.append_assoc]; rfl
      rw [e] at hs ⊢
      refine ih n (u ++ [b]) ?_ hs
      rw [Frame.walk_append]
      cases b
      · exact hL
      · exact hR

/-- **The kernel's enumeration for (B)**: every tree frame with entries at most
    40 and `|D| ≤ 20` off the families (107 of them) gives a singleton, or the
    root's pair. -/
theorem chkB_root : chkB 45 Frame.empty [] = true := by decide +kernel

/-- **Theorem 16.11, Step 2, remainder (B).** At every tree frame with
    `|D| ≤ 20` outside `RⁿL` (`q₁ = q₀`) and `LⁿR` (`p₁ = p₀`), the maximizer set
    is a singleton, except the root's `{LR, RL}`. Generic or not. -/
theorem step2_smallD (w : List Bool) (h : SmallD (Frame.walk Frame.empty w)) :
    Outcome w (Frame.walk Frame.empty w) :=
  chkB_sound w 45 [] chkB_root h

/-! ## (C) Step 2 assembled: every frame of the tree -/

/-- On the unimodular relation, `q₁ = q₀` is the family `RⁿL`. -/
theorem frn_of (F : Frame) (hq : F.plus.q = F.minus.q) : F = Step2Family.Frn F.minus.p := by
  have hc : F.plus.p * F.minus.q = F.plus.q * F.minus.p + 1 := F.contact
  rw [← hq] at hc
  have key : F.plus.p = F.minus.p + 1 ∧ F.plus.q = 1 := by
    generalize F.plus.p = p1 at hc ⊢
    generalize F.minus.p = p0 at hc ⊢
    generalize F.plus.q = q at hc ⊢
    rcases Nat.lt_or_ge p0 p1 with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
      have x : (p0 + d + 1) * q = q * p0 + d * q + q := by ring
      rw [x] at hc
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · subst h0; exfalso; omega
      · have := Nat.le_mul_of_pos_right d h0
        exact ⟨by omega, by omega⟩
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have x : q * (p1 + d) = p1 * q + q * d := by ring
      rw [x] at hc
      exfalso; omega
  exact Step2Family.frame_eq key.1 key.2 rfl (hq.symm.trans key.2)

/-- On the unimodular relation, `p₁ = p₀` is the family `LⁿR`. -/
theorem fm_of (F : Frame) (hp : F.plus.p = F.minus.p) : F = Step2Family.Fm F.plus.q := by
  have hc : F.plus.p * F.minus.q = F.plus.q * F.minus.p + 1 := F.contact
  rw [← hp] at hc
  have key : F.plus.p = 1 ∧ F.minus.q = F.plus.q + 1 := by
    generalize F.plus.p = p at hc ⊢
    generalize F.minus.q = q0 at hc ⊢
    generalize F.plus.q = q1 at hc ⊢
    rcases Nat.lt_or_ge q1 q0 with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
      have x : p * (q1 + d + 1) = q1 * p + p * d + p := by ring
      rw [x] at hc
      rcases Nat.eq_zero_or_pos p with h0 | h0
      · subst h0; exfalso; omega
      · have := Nat.le_mul_of_pos_left d h0
        exact ⟨by omega, by omega⟩
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have x : (q0 + d) * p = p * q0 + d * p := by ring
      rw [x] at hc
      exfalso; omega
  exact Step2Family.frame_eq key.1 rfl (hp.symm.trans key.1) key.2

/-- `step2_family_support` for the mirror `LⁿR`. -/
theorem mirror_support (n : ℕ) (hn : 1 ≤ n) (h : n % 21 ≠ 3) :
    support (grand (Step2Family.Fm n)) = [gLL (Step2Family.Fm n)] ∨
      support (grand (Step2Family.Fm n)) = [gRR (Step2Family.Fm n)] := by
  rcases Step2Family.res21 n with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
    | h' | h' | h' | h' | h' | h' | h' | h' <;>
  first
    | exact absurd h' h
    | exact Or.inl (Step2Family.step2_mirror_LL n hn (by omega))
    | exact Or.inr (Step2Family.step2_mirror_RR n hn (by omega))

/-- Step 2's conclusion extended by the two families' period-21 ties. -/
def Complete (w : List Bool) (F : Frame) : Prop :=
  Outcome w F ∨
  (∃ n, n % 21 = 3 ∧ F = Step2Family.Frn n ∧ support (grand F) = [gLL F, gRR F]) ∨
  (∃ n, n % 21 = 3 ∧ F = Step2Family.Fm n ∧ support (grand F) = [gLL F, gRR F])

/-- **Theorem 16.11, sibling step, for every frame of the tree.** Step 1
    (`Generic`, `|D| ≥ 21`), the families `RⁿL`, `LⁿR` (`Step2Family`), and the
    finite remainder (A) and (B) together: the maximizer set of the four
    grandchildren is a singleton, except at `ε, L, R, RRRL, LLLR` (the named
    pairs) and at `RⁿL`, `LⁿR` with `n ≡ 3 (mod 21)` (the pair `{g₁, g₄}`). -/
theorem step2_complete (w : List Bool) : Complete w (Frame.walk Frame.empty w) := by
  cases hb : genB (Frame.walk Frame.empty w) with
  | false =>
    exact Or.inl (step2_nongeneric w (fun hg => by
      rw [genB_of_generic hg] at hb; exact Bool.noConfusion hb))
  | true =>
    have hg := generic_of_genB hb
    obtain ⟨F, hF⟩ : ∃ F, Frame.walk Frame.empty w = F := ⟨_, rfl⟩
    rw [hF] at hg ⊢
    rcases Nat.lt_or_ge (F.plus.p * F.plus.q) (F.minus.p * F.minus.q + 21) with h1 | h1
    · rcases Nat.lt_or_ge (F.minus.p * F.minus.q) (F.plus.p * F.plus.q + 21) with h2 | h2
      · rcases Nat.decEq F.plus.p F.minus.p with hp | hp
        · rcases Nat.decEq F.plus.q F.minus.q with hq | hq
          · have hs : SmallD F := ⟨by omega, by omega, hp, hq⟩
            have hw := step2_smallD w (by rw [hF]; exact hs)
            rw [hF] at hw
            exact Or.inl hw
          · have e := frn_of F hq
            generalize F.minus.p = n at e
            subst e
            have hn1 : 1 ≤ n := by
              rcases Nat.eq_zero_or_pos n with h0 | h0
              · subst h0; exact absurd hg.hA (by decide)
              · exact h0
            rcases Nat.decEq (n % 21) 3 with h3 | h3
            · rcases Step2Family.step2_family_support n hn1 h3 with e | e
              · exact Or.inl (Or.inl e)
              · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl e))))
            · exact Or.inr (Or.inl ⟨n, h3, rfl, Step2Family.step2_family_tie n h3⟩)
        · have e := fm_of F hp
          generalize F.plus.q = n at e
          subst e
          have hn1 : 1 ≤ n := by
            rcases Nat.eq_zero_or_pos n with h0 | h0
            · subst h0; exact absurd hg.hA (by decide)
            · exact h0
          rcases Nat.decEq (n % 21) 3 with h3 | h3
          · rcases mirror_support n hn1 h3 with e | e
            · exact Or.inl (Or.inl e)
            · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl e))))
          · exact Or.inr (Or.inr ⟨n, h3, rfl, Step2Family.step2_mirror_tie n h3⟩)
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (step1_unique_neg F hg h2)))))
    · exact Or.inl (Or.inl (step1_unique_pos F hg h1))


/-! ## The book's counts, on the same traversals

These do not feed the theorems above; they certify that the walks the kernel
checked are the sets the book counts. -/

/-- Number of non-Generic frames of the tree. -/
def cntNG : ℕ → Frame → ℕ
  | 0, _ => 0
  | n + 1, F => if genB F then 0 else
      1 + cntNG n (Frame.stepL F) + cntNG n (Frame.stepR F)

/-- Number of those whose maximizer set is a singleton. -/
def cntSing : ℕ → Frame → ℕ
  | 0, _ => 0
  | n + 1, F => if genB F then 0 else
      (if (mask F).count true = 1 then 1 else 0) +
        cntSing n (Frame.stepL F) + cntSing n (Frame.stepR F)

/-- Number of tree frames with `|D| ≤ 20` off the families (entries ≤ 40). -/
def cntSmallD : ℕ → Frame → ℕ
  | 0, _ => 0
  | n + 1, F => if boundB F then
      (if needB F then 1 else 0) + cntSmallD n (Frame.stepL F) + cntSmallD n (Frame.stepR F)
    else 0

/-- The same, restricted to entries at most 20. -/
def cntSmallD20 : ℕ → Frame → ℕ
  | 0, _ => 0
  | n + 1, F => if boundB F then
      (if needB F && decide (F.plus.p ≤ 20) && decide (F.plus.q ≤ 20) &&
          decide (F.minus.p ≤ 20) && decide (F.minus.q ≤ 20) then 1 else 0) +
        cntSmallD20 n (Frame.stepL F) + cntSmallD20 n (Frame.stepR F)
    else 0

/-- **527 non-Generic frames**, as the book says. -/
theorem count_nongeneric : cntNG 210 Frame.empty = 527 := by decide +kernel

/-- **522 of them give a singleton**, as the book says. -/
theorem count_singleton : cntSing 210 Frame.empty = 522 := by decide +kernel

/-- **107 frames with `|D| ≤ 20` off the families**, as the book says. -/
theorem count_smallD : cntSmallD 45 Frame.empty = 107 := by decide +kernel

/-- **All 107 have entries at most 20**, as the book says. -/
theorem count_smallD_20 : cntSmallD20 45 Frame.empty = 107 := by decide +kernel

end Step2Remainder
end Two
end RatioSpace
