/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S02.Frame
import RatioSpace.ElementsI.S03.Braid
import Mathlib.Data.List.Induction
import Mathlib.Tactic.LinearCombination
/-!
  Elements I §3 — Generators, typed actions, walks, and choice records.

  Definitions 3.2 through 3.11, Standard Result 3.1 and Proposition 3.2. §2 built
  the frame recursion directly on the pair of presentations; this file builds the
  word, the matrix `G(w)`, and proves they agree — `M_{F·w} = M_F · G(w)` — so the
  two descriptions of a walk are the same object rather than two conventions.

  Three things here are sharper than the prose, and each is noted at its theorem:

    * **Standard Result 3.1 needs no decoder to give uniqueness.** The book proves
      freeness by exhibiting a subtraction algorithm. The frame formulation makes
      the last letter of a word readable off the frame directly — `C₋ ≤ C₊`
      componentwise iff the last step was `L` — and injectivity falls out by
      induction on the reversed word. The exclusion is Def 1.2's `¬(p = 0 ∧ q = 0)`
      doing the work, not the determinant.

    * **Def 3.2's three actions are three named functions.** `forward` and
      `reframe` have one type and are one function (`fun x y => x * y`); they are
      kept apart by name and side of action only, not by the type checker.
      `forward_ne_reframe` swaps the arguments, so it records `LR ≠ RL`.

    * **Def 3.11's eight levels of equality do not stay eight on the tree.** Levels
      2 and 3 coincide for anything a walk addresses, because every addressed
      relation is primitive and proportional primitives are equal
      (`prop_iff_eq_of_primitive`). Level 5 reads the accumulated matrix
      `M_{F_0}G(w)` (Def 3.4); levels 1, 2, 3, 5 are one relation on every pair
      (`matrixEq_iff_presEq`, `levels_one_two_three_five` in `State.lean`), and
      level 4 joins them only for histories with one start frame, by freeness
      (`matrixEq_iff_wordEq`, `levels_one_to_five_of_start_eq`). Level 8
      under `ν` is level 3 on histories (`projectionEq_iff_endpointEq`), so
      it is in the first class too; under a specified projection it depends
      on the map, and one that is not injective on primitives separates it
      from level 3 on the tree (`projectionEqBy_not_endpointEq`). Among
      levels 1 to 5 the only separation on histories is level 4, across
      different start frames (`matrixEq_not_wordEq`, `endpointEq_not_wordEq`).
      The unrooted equality `G(w_X) = G(w_Y)` is `WordMatrixEq`, which is word
      equality (`wordMatrixEq_iff_wordEq`) and is not level 5.
      These levels are formalised on `History`, Def 3.8's minimum record
      `(F₀, w)` (start frame and word, without the additional
      presentation-multiplicity components Def 3.8 allows), and level 1 is
      read on the final frame's boundaries. No level relation is defined on
      Def 6.2 states (`CompleteState`) in the tree. If level 1 on a state read
      its presentation slot rather than its frame, levels 1 and 2 would separate
      there: `nonprimitiveReading` (`State.lean`) holds `2:4` on the frame whose
      mediant is `1:2`. That is a reading, not a theorem.

  Everything is computable. No `sorry`, no `axiom`.
-/

namespace RatioSpace

open Pres

/-! ## Matrix scaffolding

    `Mat2` was written for `Braid.lean`, where every claim was a closed term and
    `decide` finished it. Words are open, so the monoid laws have to be available
    as lemmas. -/

namespace Mat2

theorem ext' {M N : Mat2} (ha : M.a = N.a) (hb : M.b = N.b) (hc : M.c = N.c)
    (hd : M.d = N.d) : M = N := by
  cases M; cases N; simp_all

@[simp] theorem one_a : (1 : Mat2).a = 1 := rfl
@[simp] theorem one_b : (1 : Mat2).b = 0 := rfl
@[simp] theorem one_c : (1 : Mat2).c = 0 := rfl
@[simp] theorem one_d : (1 : Mat2).d = 1 := rfl
@[simp] theorem neg_a (M : Mat2) : (-M).a = -M.a := rfl
@[simp] theorem neg_b (M : Mat2) : (-M).b = -M.b := rfl
@[simp] theorem neg_c (M : Mat2) : (-M).c = -M.c := rfl
@[simp] theorem neg_d (M : Mat2) : (-M).d = -M.d := rfl

theorem mul_def (M N : Mat2) :
    M * N = ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
             M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩ := rfl

@[simp] theorem one_mul' (M : Mat2) : (1 : Mat2) * M = M := by
  apply ext' <;> simp [mul_def]

@[simp] theorem mul_one' (M : Mat2) : M * (1 : Mat2) = M := by
  apply ext' <;> simp [mul_def]

theorem mul_assoc' (M N K : Mat2) : M * N * K = M * (N * K) := by
  apply ext' <;> simp [mul_def] <;> ring

/-- The adjugate. On the determinant-one shell it is the inverse, which is the
    only place it is used below. -/
def inv2 (M : Mat2) : Mat2 := ⟨M.d, -M.b, -M.c, M.a⟩

/-- **Constructive.** Written out entry by entry with `ring` and the determinant
    hypothesis rather than `linarith`, which reaches `Classical.choice` through
    mathlib's ordered-ring automation. -/
theorem mul_inv2_of_det (M : Mat2) (h : M.det = 1) : M * inv2 M = 1 := by
  cases M with | mk a b c d =>
  have h' : a * d - b * c = 1 := h
  refine ext' ?_ ?_ ?_ ?_
  · change a * d + b * -c = 1
    calc a * d + b * -c = a * d - b * c := by ring
      _ = 1 := h'
  · change a * -b + b * a = 0
    ring
  · change c * d + d * -c = 0
    ring
  · change c * -b + d * a = 1
    calc c * -b + d * a = a * d - b * c := by ring
      _ = 1 := h'

theorem inv2_mul_of_det (M : Mat2) (h : M.det = 1) : inv2 M * M = 1 := by
  cases M with | mk a b c d =>
  have h' : a * d - b * c = 1 := h
  refine ext' ?_ ?_ ?_ ?_
  · change d * a + -b * c = 1
    calc d * a + -b * c = a * d - b * c := by ring
      _ = 1 := h'
  · change d * b + -b * d = 0
    ring
  · change -c * a + a * c = 0
    ring
  · change -c * b + a * d = 1
    calc -c * b + a * d = a * d - b * c := by ring
      _ = 1 := h'

/-- Anti-multiplicative, and true without any determinant hypothesis. -/
theorem inv2_mul (M N : Mat2) : inv2 (M * N) = inv2 N * inv2 M := by
  apply ext' <;> simp [mul_def, inv2] <;> ring

end Mat2

open Mat2

/-! ## Definition 3.2 — Typed generator actions

    The prose has to say that the same multiplication symbol means different
    things depending on input type and side of action. Here they are three named
    functions. `forward` and `reframe` share the type `Mat2 → Mat2 → Mat2` and are
    the same function; the separation is by name and side of action only, and the
    type checker does not enforce it. -/

/-- **Definition 3.2, form 1.** Forward continuation: append an event to the
    accumulated history. `G(wg) = G(w)g`, acting on the right. -/
def forward (M g : Mat2) : Mat2 := M * g

/-- **Definition 3.2, form 2.** Prefix, or reframing: place a generator before
    an existing record. `G(gw) = gG(w)`, acting on the left. -/
def reframe (g M : Mat2) : Mat2 := g * M

/-- **Definition 3.2, form 3.** Bilateral encounter transport: the receiving
    history advances by `g_O` and the presented history by `g_P`, two separately
    supplied generators, neither fixed by the other, both acting on the one
    relative record `Q`, so the result depends on both. `Q ↦ g_O⁻¹ Q g_P`. Derived
    from two forward updates in Proposition 7.2; stated here so that it is a
    third named operation from the start. -/
def transport (gO gP Q : Mat2) : Mat2 := inv2 gO * Q * gP

/-- Forward continuation by `R` from `L` is not reframing `L` by `R`: with the
    arguments swapped this is `LR ≠ RL`, order in the product, not a difference
    between two functions (`forward` and `reframe` are the same function). -/
theorem forward_ne_reframe : forward L R ≠ reframe R L := by decide

/-- Transport is not forward continuation here: with a nontrivial receiving
    history it moves the record somewhere `forward L R` does not. -/
theorem transport_ne_forward : transport L R L ≠ forward L R := by decide

/-! ## Definition 3.3 — Word

    `Bool` is the alphabet: `true = R`, `false = L`, matching `Frame.select`. -/

/-- **Definition 3.3.** A finite ordered generator string. -/
abbrev Word := List Bool

namespace Word

/-- The generator named by a letter. -/
def gen (b : Bool) : Mat2 := if b then R else L

@[simp] theorem gen_true : gen true = R := rfl
@[simp] theorem gen_false : gen false = L := rfl

/-- **Definition 3.3.** `G(w) = g₁g₂⋯gₙ`, with `G(ε) = I`. -/
def G : Word → Mat2
  | [] => 1
  | b :: w => gen b * G w

@[simp] theorem G_nil : G [] = 1 := rfl
@[simp] theorem G_cons (b : Bool) (w : Word) : G (b :: w) = gen b * G w := rfl

/-- **Definition 3.3.** `|w| = n`, `|ε| = 0`. This is `List.length`; named so the
    book's symbol has a referent. -/
abbrev len (w : Word) : ℕ := w.length

@[simp] theorem len_nil : len [] = 0 := rfl

theorem G_append (u v : Word) : G (u ++ v) = G u * G v := by
  induction u with
  | nil => simp
  | cons b u ih => simp [ih, Mat2.mul_assoc']

@[simp] theorem G_snoc (w : Word) (b : Bool) : G (w ++ [b]) = G w * gen b := by
  simp [G_append]

/-- **Definition 3.3.** Order is part of the word: `LR ≠ RL`. -/
theorem LR_ne_RL : G [false, true] ≠ G [true, false] := by decide

/-- Every generator, hence every word, sits on the contact shell. -/
@[simp] theorem det_gen (b : Bool) : (gen b).det = 1 := by cases b <;> decide

@[simp] theorem det_G (w : Word) : (G w).det = 1 := by
  induction w with
  | nil => decide
  | cons b w ih => simp [Mat2.det_mul, ih]

end Word

open Word

/-! ## Definition 3.6 — Positive refinement monoid -/

/-- **Definition 3.6.** `ℳ₊ = {G(w) : w ∈ {L,R}*} ⊆ SL(2,ℤ)`. -/
def Mplus : Set Mat2 := Set.range G

theorem det_of_mem_Mplus {M : Mat2} (h : M ∈ Mplus) : M.det = 1 := by
  obtain ⟨w, rfl⟩ := h; simp

theorem one_mem_Mplus : (1 : Mat2) ∈ Mplus := ⟨[], rfl⟩

theorem mul_mem_Mplus {M N : Mat2} (hM : M ∈ Mplus) (hN : N ∈ Mplus) :
    M * N ∈ Mplus := by
  obtain ⟨u, rfl⟩ := hM; obtain ⟨v, rfl⟩ := hN; exact ⟨u ++ v, G_append u v⟩

/-! ## The positive decoder

    Standard Result 3.1 gives uniqueness — `G_inj`, below — and the book's
    §3 writes `dec₊` without constructing it. Elements II Def 3.1 reads
    `a_x = dec₊(Q_{O,x})` and cannot be stated without it, so it is built here,
    where `ℳ₊` is defined.

    The decoder is **total, computable and fuel-driven**, for the reason given
    for `cfFuel`: a well-founded definition is opaque to the
    kernel, and every `decide` downstream would die with it.

    The descent reads the first letter off the matrix rather than off a frame.
    For `N` with nonnegative entries and `det N = 1`, `L·N` has its second row
    dominating its first and `R·N` has its first dominating its second, and the
    two cases are exclusive because a zero row forces `det = 0`. -/

/-- `R⁻¹`. Like `Linv`, it is never produced by a positive walk; the decoder
    uses it to peel a letter, not to extend one. -/
def Rinv : Mat2 := ⟨1, -1, 0, 1⟩

theorem Rinv_mul_R : Rinv * R = 1 := by decide
theorem R_mul_Rinv : R * Rinv = 1 := by decide

/-- `G` of a word beginning `L`, entry by entry. Left multiplication by `L` adds
    the first row to the second. -/
theorem G_cons_false (w : Word) :
    G (false :: w) = ⟨(G w).a, (G w).b, (G w).a + (G w).c, (G w).b + (G w).d⟩ := by
  apply Mat2.ext' <;> simp [Mat2.mul_def, L]

/-- `G` of a word beginning `R`. Left multiplication by `R` adds the second row
    to the first. -/
theorem G_cons_true (w : Word) :
    G (true :: w) = ⟨(G w).a + (G w).c, (G w).b + (G w).d, (G w).c, (G w).d⟩ := by
  apply Mat2.ext' <;> simp [Mat2.mul_def, R]

/-- Every entry of a positive word matrix is nonnegative. -/
def Nonneg (M : Mat2) : Prop := 0 ≤ M.a ∧ 0 ≤ M.b ∧ 0 ≤ M.c ∧ 0 ≤ M.d

theorem nonneg_G (w : Word) : Nonneg (G w) := by
  induction w with
  | nil => exact ⟨by decide, by decide, by decide, by decide⟩
  | cons b w ih =>
      obtain ⟨ha, hb, hc, hd⟩ := ih
      cases b with
      | false =>
          rw [G_cons_false]
          refine ⟨ha, hb, ?_, ?_⟩
          · change (0:ℤ) ≤ (G w).a + (G w).c; omega
          · change (0:ℤ) ≤ (G w).b + (G w).d; omega
      | true =>
          rw [G_cons_true]
          refine ⟨?_, ?_, hc, hd⟩
          · change (0:ℤ) ≤ (G w).a + (G w).c; omega
          · change (0:ℤ) ≤ (G w).b + (G w).d; omega

/-- **No row of a positive word matrix vanishes.** A zero row would make the
    determinant zero, and every `G w` sits at `det = 1`. This is what makes the
    two descent branches exclusive. -/
theorem row1_pos (w : Word) : 1 ≤ (G w).a + (G w).b := by
  induction w with
  | nil => decide
  | cons b w ih =>
      obtain ⟨ha, hb, hc, hd⟩ := nonneg_G w
      cases b with
      | false => rw [G_cons_false]; change 1 ≤ (G w).a + (G w).b; exact ih
      | true =>
          rw [G_cons_true]
          change 1 ≤ (G w).a + (G w).c + ((G w).b + (G w).d)
          omega

theorem row2_pos (w : Word) : 1 ≤ (G w).c + (G w).d := by
  induction w with
  | nil => decide
  | cons b w ih =>
      obtain ⟨ha, hb, hc, hd⟩ := nonneg_G w
      cases b with
      | false =>
          rw [G_cons_false]
          change 1 ≤ (G w).a + (G w).c + ((G w).b + (G w).d)
          omega
      | true => rw [G_cons_true]; change 1 ≤ (G w).c + (G w).d; exact ih

/-- A nonempty positive word is never the identity: the walk does not return. -/
theorem G_cons_ne_one (b : Bool) (w : Word) : G (b :: w) ≠ 1 := by
  obtain ⟨ha, hb, hc, hd⟩ := nonneg_G w
  cases b with
  | false =>
      rw [G_cons_false]
      intro h
      have h1 : (G w).a = 1 := congrArg Mat2.a h
      have h3 : (G w).a + (G w).c = 0 := congrArg Mat2.c h
      omega
  | true =>
      rw [G_cons_true]
      intro h
      have h2 : (G w).b + (G w).d = 0 := congrArg Mat2.b h
      have h4 : (G w).d = 1 := congrArg Mat2.d h
      omega

theorem G_cons_false_dom (w : Word) :
    (G (false :: w)).a ≤ (G (false :: w)).c ∧ (G (false :: w)).b ≤ (G (false :: w)).d := by
  obtain ⟨ha, hb, hc, hd⟩ := nonneg_G w
  rw [G_cons_false]
  refine ⟨?_, ?_⟩
  · change (G w).a ≤ (G w).a + (G w).c; omega
  · change (G w).b ≤ (G w).b + (G w).d; omega

theorem G_cons_true_not_dom (w : Word) :
    ¬ ((G (true :: w)).a ≤ (G (true :: w)).c ∧ (G (true :: w)).b ≤ (G (true :: w)).d) := by
  obtain ⟨ha, hb, hc, hd⟩ := nonneg_G w
  have hdet : (G w).a * (G w).d - (G w).b * (G w).c = 1 := det_G w
  rw [G_cons_true]
  rintro ⟨h1, h2⟩
  have h1' : (G w).a + (G w).c ≤ (G w).c := h1
  have h2' : (G w).b + (G w).d ≤ (G w).d := h2
  have hA : (G w).a = 0 := by omega
  have hB : (G w).b = 0 := by omega
  rw [hA, hB] at hdet
  omega

theorem G_cons_true_dom (w : Word) :
    (G (true :: w)).c ≤ (G (true :: w)).a ∧ (G (true :: w)).d ≤ (G (true :: w)).b := by
  obtain ⟨ha, hb, hc, hd⟩ := nonneg_G w
  rw [G_cons_true]
  refine ⟨?_, ?_⟩
  · change (G w).c ≤ (G w).a + (G w).c; omega
  · change (G w).d ≤ (G w).b + (G w).d; omega

theorem Linv_G_cons_false (w : Word) : Linv * G (false :: w) = G w := by
  rw [G_cons, gen_false, ← Mat2.mul_assoc', Linv_mul_L, Mat2.one_mul']

theorem Rinv_G_cons_true (w : Word) : Rinv * G (true :: w) = G w := by
  rw [G_cons, gen_true, ← Mat2.mul_assoc', Rinv_mul_R, Mat2.one_mul']

/-- **The decoder, with explicit fuel.** `decFuel n M` peels at most `n` letters
    off the left of `M`. Reaching `1` succeeds; running out, or reaching a matrix
    with neither row dominating, fails. -/
def decFuel : ℕ → Mat2 → Option Word
  | 0, M => if M = 1 then some [] else none
  | n + 1, M =>
      if M = 1 then some []
      else if M.a ≤ M.c ∧ M.b ≤ M.d then (decFuel n (Linv * M)).map (fun v => false :: v)
      else if M.c ≤ M.a ∧ M.d ≤ M.b then (decFuel n (Rinv * M)).map (fun v => true :: v)
      else none

/-- **Completeness.** Given enough fuel the decoder returns the word. -/
theorem decFuel_G : ∀ (n : ℕ) (w : Word), w.length ≤ n → decFuel n (G w) = some w := by
  intro n
  induction n with
  | zero =>
      intro w hw
      have hnil : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
      subst hnil
      simp [decFuel]
  | succ n ih =>
      intro w hw
      cases w with
      | nil => simp [decFuel]
      | cons b w =>
          have hlen : w.length ≤ n := by simpa using Nat.le_of_succ_le_succ hw
          cases b with
          | false =>
              simp only [decFuel, if_neg (G_cons_ne_one false w),
                if_pos (G_cons_false_dom w), Linv_G_cons_false, ih w hlen]
              rfl
          | true =>
              simp only [decFuel, if_neg (G_cons_ne_one true w),
                if_neg (G_cons_true_not_dom w), if_pos (G_cons_true_dom w),
                Rinv_G_cons_true, ih w hlen]
              rfl

/-- **Soundness.** Whatever the decoder returns regenerates the matrix. With
    `G_inj` this makes `dec` a two-sided inverse of `G` on `ℳ₊`. -/
theorem decFuel_sound : ∀ (n : ℕ) (M : Mat2) (w : Word), decFuel n M = some w → G w = M := by
  intro n
  induction n with
  | zero =>
      intro M w h
      by_cases hM : M = 1
      · rw [decFuel, if_pos hM] at h
        have hw : w = [] := by simpa using h.symm
        subst hw
        exact G_nil.trans hM.symm
      · rw [decFuel, if_neg hM] at h
        exact absurd h (by simp)
  | succ n ih =>
      intro M w h
      by_cases hM : M = 1
      · rw [decFuel, if_pos hM] at h
        have hw : w = [] := by simpa using h.symm
        subst hw
        exact G_nil.trans hM.symm
      · rw [decFuel, if_neg hM] at h
        by_cases h1 : M.a ≤ M.c ∧ M.b ≤ M.d
        · rw [if_pos h1] at h
          cases hv : decFuel n (Linv * M) with
          | none => rw [hv] at h; simp at h
          | some v =>
              rw [hv] at h
              have hwv : w = false :: v := by simpa using h.symm
              subst hwv
              have hGv : G v = Linv * M := ih _ v hv
              calc G (false :: v) = L * G v := by rw [G_cons, gen_false]
                _ = L * (Linv * M) := by rw [hGv]
                _ = (L * Linv) * M := (Mat2.mul_assoc' _ _ _).symm
                _ = M := by rw [L_mul_Linv, Mat2.one_mul']
        · rw [if_neg h1] at h
          by_cases h2 : M.c ≤ M.a ∧ M.d ≤ M.b
          · rw [if_pos h2] at h
            cases hv : decFuel n (Rinv * M) with
            | none => rw [hv] at h; simp at h
            | some v =>
                rw [hv] at h
                have hwv : w = true :: v := by simpa using h.symm
                subst hwv
                have hGv : G v = Rinv * M := ih _ v hv
                calc G (true :: v) = R * G v := by rw [G_cons, gen_true]
                  _ = R * (Rinv * M) := by rw [hGv]
                  _ = (R * Rinv) * M := (Mat2.mul_assoc' _ _ _).symm
                  _ = M := by rw [R_mul_Rinv, Mat2.one_mul']
          · rw [if_neg h2] at h
            exact absurd h (by simp)

/-- The entry sum of `G w` grows by at least one per letter, because no row of a
    positive word matrix vanishes. This is the fuel bound. -/
theorem two_add_length_le_sum_G (w : Word) :
    (w.length : ℤ) + 2 ≤ (G w).a + (G w).b + (G w).c + (G w).d := by
  induction w with
  | nil => decide
  | cons b w ih =>
      have h1 := row1_pos w
      have h2 := row2_pos w
      have hlen : (((b :: w).length : ℕ) : ℤ) = (w.length : ℤ) + 1 := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      cases b with
      | false =>
          rw [hlen, G_cons_false]
          change (w.length : ℤ) + 1 + 2 ≤
            (G w).a + (G w).b + ((G w).a + (G w).c) + ((G w).b + (G w).d)
          omega
      | true =>
          rw [hlen, G_cons_true]
          change (w.length : ℤ) + 1 + 2 ≤
            ((G w).a + (G w).c) + ((G w).b + (G w).d) + (G w).c + (G w).d
          omega

/-- Fuel read off the matrix itself. -/
def sizeM (M : Mat2) : ℕ := (M.a + M.b + M.c + M.d).toNat

theorem length_le_sizeM_G (w : Word) : w.length ≤ sizeM (G w) := by
  have h := two_add_length_le_sum_G w
  unfold sizeM
  omega

/-! ## Decoder totality — every nonnegative unimodular matrix decodes

    Not only the images of `G`: every nonnegative determinant-one integer
    matrix lies in `ℳ₊` (`mem_Mplus_of_nonneg`). Elements II, Proposition 9.2
    needs this converse, and `ElementsII/S09/Admission.lean` imports it by name.

    **A declared frame decodes by the same theorem.** A *declared* frame's own
    matrix has to decode, or there is no way to read `ψ₁₂` off a start-relative
    `M_τ` without discarding the start. The matrix field and the closure field
    both read the accumulated matrix relative to the declared start, the closure
    field using exactly this. -/

/-- **The dichotomy `decFuel` rests on.** A
    nonnegative determinant-one matrix that is not the identity has comparable
    rows.

    If both comparisons failed, one row would exceed the other in one column
    and trail it in the other; with all entries nonnegative that forces
    `det ≥ b + c + 1`, so `b = c = 0`, so `ad = 1`, so `M = I`. -/
theorem rows_comparable {M : Mat2} (h : Nonneg M) (hd : M.det = 1) (hne : M ≠ 1) :
    (M.a ≤ M.c ∧ M.b ≤ M.d) ∨ (M.c ≤ M.a ∧ M.d ≤ M.b) := by
  -- Explicit monotonicity of integer multiplication rather than `nlinarith`, so this proof,
  -- and the decoder above it, do not reach `Classical.choice`.
  obtain ⟨ha, hb, hc, hd'⟩ := h
  have hdet : M.a * M.d - M.b * M.c = 1 := hd
  rcases le_or_gt M.a M.c with h1 | h1
  · rcases le_or_gt M.b M.d with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exfalso
      -- a ≤ c and d < b with every entry nonnegative: a*d ≤ c*d ≤ c*b, so det ≤ 0.
      have e1 : M.a * M.d ≤ M.c * M.d := Int.mul_le_mul_of_nonneg_right h1 hd'
      have e2 : M.c * M.d ≤ M.c * M.b := Int.mul_le_mul_of_nonneg_left (le_of_lt h2) hc
      have e3 : M.c * M.b = M.b * M.c := Int.mul_comm _ _
      omega
  · rcases le_or_gt M.d M.b with h2 | h2
    · exact Or.inr ⟨le_of_lt h1, h2⟩
    · -- c < a and b < d: a*d ≥ (c+1)*(b+1) = b*c + c + b + 1, so b = c = 0 and a*d = 1.
      have e1 : (M.c + 1) * (M.b + 1) ≤ M.a * (M.b + 1) :=
        Int.mul_le_mul_of_nonneg_right h1 (by omega)
      have e2 : M.a * (M.b + 1) ≤ M.a * M.d := Int.mul_le_mul_of_nonneg_left h2 ha
      have e3 : (M.c + 1) * (M.b + 1) = M.b * M.c + M.c + M.b + 1 := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.one_mul, Int.mul_one, Int.mul_one,
          Int.mul_comm]
        omega
      have hb0 : M.b = 0 := by omega
      have hc0 : M.c = 0 := by omega
      rw [hb0, hc0] at hdet
      have had : M.a * M.d = 1 := by omega
      have ha1 : M.a = 1 := Int.eq_one_of_mul_eq_one_right ha had
      have hd1 : M.d = 1 := Int.eq_one_of_mul_eq_one_left hd' had
      exact absurd (Mat2.ext' ha1 hb0 hc0 hd1) hne

/-- Size strictly drops on each decoding step, because the row being subtracted
    is nonzero: a zero row would make the determinant zero. -/
theorem row_ne_zero_of_det {M : Mat2} (hd : M.det = 1) :
    ¬ (M.a = 0 ∧ M.b = 0) ∧ ¬ (M.c = 0 ∧ M.d = 0) := by
  have hdet : M.a * M.d - M.b * M.c = 1 := hd
  -- `omega` rather than `simp at hdet`, which reaches `Classical.choice`.
  constructor <;> rintro ⟨h1, h2⟩ <;> rw [h1, h2] at hdet <;> omega

/-- `sizeM M ≤ n` read without `Int.toNat`, for a nonnegative `M`. Kept separate
    because `omega` and `simp` on `Int.toNat` reach `Classical.choice` through `Int.toNat_le`. -/
theorem sizeM_le_iff {M : Mat2} (h : Nonneg M) (n : ℕ) :
    sizeM M ≤ n ↔ M.a + M.b + M.c + M.d ≤ (n : ℤ) := by
  unfold sizeM
  have h0 : 0 ≤ M.a + M.b + M.c + M.d := by obtain ⟨ha, hb, hc, hd⟩ := h; omega
  have e := Int.toNat_of_nonneg h0
  constructor
  · intro hle
    have hc : (((M.a + M.b + M.c + M.d).toNat : ℕ) : ℤ) ≤ (n : ℤ) :=
      Int.ofNat_le.mpr hle
    rw [e] at hc; exact hc
  · intro hle
    apply Int.ofNat_le.mp; rw [e]; exact hle

/-- Both rows of a nonnegative determinant-one matrix have a positive entry, stated positively
    (`1 ≤ a + b`, `1 ≤ c + d`) so that `omega` never has to split a negated conjunction, which is
    where `Classical.choice` would enter the decoder. -/
theorem rows_pos_of_nonneg_det {M : Mat2} (h : Nonneg M) (hd : M.det = 1) :
    1 ≤ M.a + M.b ∧ 1 ≤ M.c + M.d := by
  obtain ⟨ha, hb, hc, hd'⟩ := h
  have hdet : M.a * M.d - M.b * M.c = 1 := hd
  constructor
  · rcases le_or_gt (M.a + M.b) 0 with h | h
    · have ha0 : M.a = 0 := by omega
      have hb0 : M.b = 0 := by omega
      rw [ha0, hb0] at hdet; omega
    · omega
  · rcases le_or_gt (M.c + M.d) 0 with h | h
    · have hc0 : M.c = 0 := by omega
      have hd0 : M.d = 0 := by omega
      rw [hc0, hd0] at hdet; omega
    · omega

/-- **The converse of Standard Result 3.1's image statement.** A nonnegative
    determinant-one integer matrix lies in `ℳ₊`. Every `Frame`'s matrix is
    exactly such a matrix (`det_toMat2`, and its entries are `ℕ`-cast), so
    this is what makes a declared origin decodable. -/
theorem mem_Mplus_of_nonneg : ∀ (n : ℕ) (M : Mat2), sizeM M ≤ n →
    Nonneg M → M.det = 1 → M ∈ Mplus := by
  intro n
  induction n with
  | zero =>
      intro M hsz h hd
      by_cases hM : M = 1
      · exact hM ▸ one_mem_Mplus
      · exfalso
        obtain ⟨ha, hb, hc, hd'⟩ := h
        have := rows_pos_of_nonneg_det ⟨ha, hb, hc, hd'⟩ hd
        rw [sizeM_le_iff ⟨ha, hb, hc, hd'⟩] at hsz
        omega
  | succ n ih =>
      intro M hsz h hd
      by_cases hM : M = 1
      · exact hM ▸ one_mem_Mplus
      · obtain ⟨ha, hb, hc, hd'⟩ := h
        have hrows := rows_comparable ⟨ha, hb, hc, hd'⟩ hd hM
        have hnz := rows_pos_of_nonneg_det ⟨ha, hb, hc, hd'⟩ hd
        rcases hrows with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hM' : Nonneg (Linv * M) := by
            refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Linv, Mat2.mul_def] <;> omega
          have hd'' : (Linv * M).det = 1 := by
            rw [Mat2.det_mul, hd, mul_one]; decide
          have hsz' : sizeM (Linv * M) ≤ n := by
            rw [sizeM_le_iff hM']
            rw [sizeM_le_iff ⟨ha, hb, hc, hd'⟩] at hsz
            simp only [Linv, Mat2.mul_def, one_mul, zero_mul, add_zero, neg_mul, Int.reduceNeg]
            omega
          obtain ⟨w, hw⟩ := ih _ hsz' hM' hd''
          refine ⟨false :: w, ?_⟩
          rw [G_cons, gen_false, hw]
          calc L * (Linv * M) = (L * Linv) * M := (Mat2.mul_assoc' _ _ _).symm
            _ = M := by rw [L_mul_Linv, Mat2.one_mul']
        · have hM' : Nonneg (Rinv * M) := by
            refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Rinv, Mat2.mul_def] <;> omega
          have hd'' : (Rinv * M).det = 1 := by
            rw [Mat2.det_mul, hd, mul_one]; decide
          have hsz' : sizeM (Rinv * M) ≤ n := by
            rw [sizeM_le_iff hM']
            rw [sizeM_le_iff ⟨ha, hb, hc, hd'⟩] at hsz
            simp only [Rinv, Mat2.mul_def, one_mul, zero_mul, neg_mul, zero_add, Int.reduceNeg]
            omega
          obtain ⟨w, hw⟩ := ih _ hsz' hM' hd''
          refine ⟨true :: w, ?_⟩
          rw [G_cons, gen_true, hw]
          calc R * (Rinv * M) = (R * Rinv) * M := (Mat2.mul_assoc' _ _ _).symm
            _ = M := by rw [R_mul_Rinv, Mat2.one_mul']

/-- **`dec₊`.** The decoder of Elements II Def 3.1: total, computable, and with
    no fuel argument left to supply. -/
def dec (M : Mat2) : Option Word := decFuel (sizeM M) M

@[simp] theorem dec_G (w : Word) : dec (G w) = some w :=
  decFuel_G _ w (length_le_sizeM_G w)

theorem dec_sound {M : Mat2} {w : Word} (h : dec M = some w) : G w = M :=
  decFuel_sound _ M w h

/-- **Membership in `ℳ₊` is decidable.** The book writes `Dom₊(O)` as a
    set-builder over `Q ∈ ℳ₊` and leaves the test implicit. There is a test, it
    runs, and it is this one. -/
theorem mem_Mplus_iff_dec (M : Mat2) : M ∈ Mplus ↔ (dec M).isSome := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [dec_G]
    rfl
  · intro h
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
    exact ⟨w, dec_sound hw⟩

instance : DecidablePred (· ∈ Mplus) :=
  fun M => decidable_of_iff _ (mem_Mplus_iff_dec M).symm

example : dec (G [true, false, false]) = some [true, false, false] := by decide
example : dec ⟨0, -1, 1, 2⟩ = none := by decide

/-! ## Shared-prefix cancellation

    Elements I Def 3.2 form 3 uses this and does not isolate it; Elements II
    **Import 1.5** imports it by name. -/

/-- **Import 1.5.** Shared-prefix cancellation:
    `(G(u)M_O)⁻¹(G(u)M_P) = M_O⁻¹M_P`. A common history is invisible to the
    relative encounter matrix, exactly and for every prefix. -/
theorem shared_prefix_cancel (u : Word) (MO MP : Mat2) :
    inv2 (G u * MO) * (G u * MP) = inv2 MO * MP := by
  rw [inv2_mul, mul_assoc', ← mul_assoc' (inv2 (G u)) (G u) MP,
    inv2_mul_of_det _ (det_G u), one_mul']

/-- The observer's own walk cancels: meeting `uv` from `u` reads `G(v)`. -/
theorem encounter_shared_prefix (u v : Word) :
    inv2 (G u) * G (u ++ v) = G v := by
  rw [G_append, ← mul_assoc', inv2_mul_of_det _ (det_G u), one_mul']

/-- **The relative matrix is not the whole encounter.** Import 1.5 says so and
    does not prove it; shared-prefix cancellation is what makes it true. An
    observer at `R` meeting `RL` and an observer at `ε` meeting `L` record the
    same `Q`, and no observer can tell the two situations apart from `Q` alone.
    The two word histories, which the complete record retains, do differ. -/
theorem encounter_matrix_loses_history :
    inv2 (G [true]) * G [true, false] = inv2 (G []) * G [false] ∧
    ([true, false] : Word) ≠ ([false] : Word) := by
  refine ⟨by decide, by decide⟩

/-- **Def 3.9's exclusion, proved rather than asserted.** `P ∉ ℳ₊`, because every
    word sits at `det = 1` and `P` sits at `det = -1`. The side exchange is an
    orientation-reversing automorphism of the positive grammar, never an
    admissible forward generator. -/
theorem P_not_mem_Mplus : P ∉ Mplus := fun h => by
  have := det_of_mem_Mplus h
  rw [det_P] at this
  exact absurd this (by decide)

/-! ## Definition 3.4 — Walk, and its agreement with the matrix product -/

namespace Frame

theorem ext' {F K : Frame} (hp : F.plus = K.plus) (hm : F.minus = K.minus) :
    F = K := by
  cases F; cases K; simp_all

/-- The derived frame matrix as a `Mat2`: columns `(C₊, C₋)`. `Frame.matrix`
    already records the same four integers as a pair of columns; this is the same
    notation in the form the generator products need. -/
def toMat2 (F : Frame) : Mat2 := ⟨F.plus.p, F.minus.p, F.plus.q, F.minus.q⟩

@[simp] theorem det_toMat2 (F : Frame) : F.toMat2.det = 1 := by
  have h : Delta F.plus F.minus = 1 := (contact_iff_delta_one _ _).mp F.contact
  change (F.plus.p : ℤ) * F.minus.q - F.minus.p * F.plus.q = 1
  unfold Delta at h
  -- One commutation rather than `linarith` (which reaches `Classical.choice`).
  rw [Int.mul_comm (F.minus.p : ℤ) (F.plus.q : ℤ)]
  exact h

/-- Every frame's matrix is nonnegative: its four entries are `Pres.p`/`Pres.q`
    values, `ℕ`-cast. -/
theorem toMat2_nonneg (F : Frame) : Nonneg F.toMat2 :=
  ⟨Int.natCast_nonneg _, Int.natCast_nonneg _, Int.natCast_nonneg _,
    Int.natCast_nonneg _⟩

/-- **A declared frame decodes.** Not only the frames a walk actually reaches
    — every `Frame` term, because `Contact` already forces a nonnegative
    determinant-one matrix and `mem_Mplus_of_nonneg` (`dec`, above) covers all
    of those. So a declared origin's own matrix is `G` of some word, and
    closure can read the start-relative accumulated matrix without discarding
    the start. -/
theorem toMat2_mem_Mplus (F : Frame) : F.toMat2 ∈ Mplus :=
  mem_Mplus_of_nonneg (sizeM F.toMat2) F.toMat2 le_rfl (toMat2_nonneg F) (det_toMat2 F)

theorem toMat2_isSome_dec (F : Frame) : (dec F.toMat2).isSome := by
  rw [← mem_Mplus_iff_dec]
  exact toMat2_mem_Mplus F

/-- The word a declared frame's matrix decodes to. Total and computable. -/
def toWord (F : Frame) : Word := (dec F.toMat2).get (toMat2_isSome_dec F)

theorem G_toWord (F : Frame) : G F.toWord = F.toMat2 :=
  dec_sound (Option.some_get (toMat2_isSome_dec F)).symm

@[simp] theorem toMat2_empty : empty.toMat2 = 1 := by decide

/-- **Definition 3.1 conformance, `M_F L = M_{F_L}`.** `L = ((1,0),(1,1))` acting
    on the right puts the mediant in the FIRST column. This fixes the
    orientation of `stepL` (Def 2.4) against Def 3.1. -/
@[simp] theorem toMat2_stepL (F : Frame) : (stepL F).toMat2 = F.toMat2 * L := by
  apply Mat2.ext' <;> simp [toMat2, stepL, mid, Pres.mediant, Mat2.mul_def, L]

/-- **Definition 3.1 conformance, `M_F R = M_{F_R}`.** `R = ((1,1),(0,1))` acting
    on the right puts the mediant in the second column. -/
@[simp] theorem toMat2_stepR (F : Frame) : (stepR F).toMat2 = F.toMat2 * R := by
  apply Mat2.ext' <;> simp [toMat2, stepR, mid, Pres.mediant, Mat2.mul_def, R]

@[simp] theorem toMat2_select (F : Frame) (b : Bool) :
    (select F b).toMat2 = F.toMat2 * gen b := by
  cases b <;> simp [select]

/-- **Definition 3.4, and the reason the two descriptions are one object.**
    `M_{F·w} = M_F · G(w)`. §2 grew the walk by rebuilding the pair of
    presentations from the mediant; §3 grows it by multiplying matrices. They
    agree for every frame and every word. -/
theorem toMat2_walk (F : Frame) (w : Word) :
    (walk F w).toMat2 = F.toMat2 * G w := by
  induction w generalizing F with
  | nil => simp [walk]
  | cons b w ih =>
      change (walk (select F b) w).toMat2 = _
      rw [ih, toMat2_select, G_cons, Mat2.mul_assoc']

/-- The canonical case: from the boundary frame the matrix of the walk **is**
    `G(w)`. -/
@[simp] theorem toMat2_walk_empty (w : Word) : (walk empty w).toMat2 = G w := by
  simp [toMat2_walk]

/-- **Definition 3.4.** The walk as the ordered succession of frames, not the
    endpoint alone. Computable, and the list the book means. -/
def walkSeq (F : Frame) : Word → List Frame
  | [] => [F]
  | b :: w => F :: walkSeq (select F b) w

@[simp] theorem walkSeq_length (F : Frame) (w : Word) :
    (walkSeq F w).length = w.length + 1 := by
  induction w generalizing F with
  | nil => rfl
  | cons b w ih => simp [walkSeq, ih]

theorem walkSeq_getLast (F : Frame) (w : Word) :
    (walkSeq F w).getLast (by cases w <;> simp [walkSeq]) = walk F w := by
  induction w generalizing F with
  | nil => rfl
  | cons b w ih =>
      change (F :: walkSeq (select F b) w).getLast _ = walk (select F b) w
      rw [List.getLast_cons (by cases w <;> simp [walkSeq])]
      exact ih (select F b)

/-! ## Definition 3.5 — Addressed relation -/

/-- **Definition 3.5.** `r_F(w) = C₋(w) ⊕ C₊(w)`, the mediant of the final frame.
    Computable; this is `Frame.mid` of the walk's endpoint. -/
def addressed (F : Frame) (w : Word) : Pres := (walk F w).mid

/-- **Definition 3.5.** The canonical instance `r(w) := r_{F_∅}(w)`. -/
def r (w : Word) : Pres := addressed empty w

/-- **Definition 3.5.** `r(ε) = 1:1`. -/
@[simp] theorem r_nil : r [] = ⟨1, 1, by decide⟩ := rfl

example : r [true] = ⟨2, 1, by decide⟩ := rfl
example : r [false] = ⟨1, 2, by decide⟩ := rfl
example : r [true, false, false] = ⟨4, 3, by decide⟩ := rfl

/-- Every addressed relation is primitive: on-tree, `reduce` never fires. -/
theorem r_primitive (w : Word) : Primitive (r w) := walk_mid_primitive empty w

/-! ## Standard Result 3.1 — Positive freeness and unique decoding

    The book decodes by componentwise subtraction. On frames the last letter is
    readable directly, and the exclusion that makes the two cases exclusive is
    Def 1.2's `¬(p = 0 ∧ q = 0)` rather than the determinant. -/

/-- `C₋ ≤ C₊` componentwise. Decidable, and it is exactly the record of which
    child the last step took. -/
def DomL (F : Frame) : Prop := F.minus.p ≤ F.plus.p ∧ F.minus.q ≤ F.plus.q

instance : DecidablePred DomL := fun F => by unfold DomL; infer_instance

theorem domL_stepL (F : Frame) : DomL (stepL F) :=
  ⟨Nat.le_add_left _ _, Nat.le_add_left _ _⟩

theorem not_domL_stepR (F : Frame) : ¬ DomL (stepR F) := by
  rintro ⟨h1, h2⟩
  simp only [stepR, mid, Pres.mediant] at h1 h2
  exact F.minus.ne_zero ⟨by omega, by omega⟩

/-- **The last letter is readable off the frame.** No subtraction, no algorithm. -/
theorem domL_select_iff (F : Frame) (b : Bool) : DomL (select F b) ↔ b = false := by
  cases b
  · simp [select, domL_stepL]
  · simp [select, not_domL_stepR]

theorem stepL_inj {F K : Frame} (h : stepL F = stepL K) : F = K := by
  have h1 := congrArg Frame.plus h
  have h2 := congrArg Frame.minus h
  simp only [stepL] at h1 h2
  have hp := congrArg Pres.p h1
  have hq := congrArg Pres.q h1
  have hp2 := congrArg Pres.p h2
  have hq2 := congrArg Pres.q h2
  simp only [mid, Pres.mediant] at hp hq
  exact ext' (Pres.ext' (by omega) (by omega)) h2

theorem stepR_inj {F K : Frame} (h : stepR F = stepR K) : F = K := by
  have h1 := congrArg Frame.plus h
  have h2 := congrArg Frame.minus h
  simp only [stepR] at h1 h2
  have hp := congrArg Pres.p h2
  have hq := congrArg Pres.q h2
  have hp2 := congrArg Pres.p h1
  have hq2 := congrArg Pres.q h1
  simp only [mid, Pres.mediant] at hp hq
  exact ext' h1 (Pres.ext' (by omega) (by omega))

/-- One step is injective in both arguments at once.

    **Constructive.** The four cases are exhausted directly rather than by
    `by_contra`, because `Bool` equality is decidable and the mixed cases have
    their own witness — `DomL` reads the last letter off the frame. -/
theorem select_inj {F K : Frame} {a b : Bool} (h : select F a = select K b) :
    a = b ∧ F = K := by
  cases a <;> cases b
  · exact ⟨rfl, stepL_inj (by simpa [select] using h)⟩
  · exact absurd ((by simpa [select] using h : stepL F = stepR K) ▸ domL_stepL F)
      (not_domL_stepR K)
  · exact absurd ((by simpa [select] using h : stepR F = stepL K) ▸ domL_stepL K)
      (not_domL_stepR F)
  · exact ⟨rfl, stepR_inj (by simpa [select] using h)⟩

/-- The size of a frame: the sum of its four entries. -/
def size (F : Frame) : ℕ := F.plus.p + F.plus.q + F.minus.p + F.minus.q

theorem pres_size_pos (A : Pres) : 1 ≤ A.p + A.q := by
  rcases Nat.eq_zero_or_pos (A.p + A.q) with h | h
  · exact absurd ⟨by omega, by omega⟩ A.ne_zero
  · exact h

theorem size_select_gt (F : Frame) (b : Bool) : size F < size (select F b) := by
  cases b
  · have := pres_size_pos F.minus
    simp only [select, Bool.false_eq_true, if_false, size, stepL, mid, Pres.mediant]
    omega
  · have := pres_size_pos F.plus
    simp only [select, if_true, size, stepR, mid, Pres.mediant]
    omega

theorem size_walk_ge (F : Frame) (w : Word) : size F + w.length ≤ size (walk F w) := by
  induction w generalizing F with
  | nil => simp [walk]
  | cons b w ih =>
      have h1 := size_select_gt F b
      have h2 := ih (select F b)
      change size F + (w.length + 1) ≤ size (walk (select F b) w)
      omega

/-- One more step at the end of a word is one more `select` on the frame. -/
@[simp] theorem walk_snoc (F : Frame) (w : Word) (b : Bool) :
    walk F (w ++ [b]) = select (walk F w) b := by
  simp [walk, List.foldl_append]

theorem size_lt_of_ne_nil (F : Frame) {w : Word} (hw : w ≠ []) :
    size F < size (walk F w) := by
  cases w with
  | nil => exact absurd rfl hw
  | cons b w =>
      have h1 := size_select_gt F b
      have h2 := size_walk_ge (select F b) w
      change size F < size (walk (select F b) w)
      omega

/-- **Standard Result 3.1, uniqueness half.** The positive walk from any frame is
    injective on words: distinct instruction strings reach distinct frames. This
    is what makes a frame's ancestry recoverable, and it is proved by reading the
    last letter off the frame rather than by running a decoder. -/
theorem walk_inj (F : Frame) {u v : Word} (h : walk F u = walk F v) : u = v := by
  induction u using List.reverseRecOn generalizing v with
  | nil =>
      cases v using List.reverseRecOn with
      | nil => rfl
      | append_singleton v b =>
          exfalso
          have hlt := size_lt_of_ne_nil F (w := v ++ [b]) (by simp)
          rw [← h] at hlt
          simp [walk] at hlt
  | append_singleton u a ih =>
      cases v using List.reverseRecOn with
      | nil =>
          exfalso
          have hlt := size_lt_of_ne_nil F (w := u ++ [a]) (by simp)
          rw [h] at hlt
          simp [walk] at hlt
      | append_singleton v b =>
          rw [walk_snoc, walk_snoc] at h
          obtain ⟨hab, hFK⟩ := select_inj h
          rw [ih hFK, hab]

/-- **Standard Result 3.1, freeness.** `ℳ₊` is free on `L` and `R`: `G` is
    injective, so every positive unimodular matrix carries exactly one word. -/
theorem G_inj {u v : Word} (h : G u = G v) : u = v := by
  refine walk_inj empty ?_
  have hu := toMat2_walk_empty u
  have hv := toMat2_walk_empty v
  have : (walk empty u).toMat2 = (walk empty v).toMat2 := by rw [hu, hv, h]
  cases hw : walk empty u with | mk pu mu cu =>
  cases hz : walk empty v with | mk pv mv cv =>
  rw [hw, hz] at this
  simp only [toMat2] at this
  have h1 := congrArg Mat2.a this
  have h2 := congrArg Mat2.b this
  have h3 := congrArg Mat2.c this
  have h4 := congrArg Mat2.d this
  simp only [] at h1 h2 h3 h4
  exact ext' (Pres.ext' (by exact_mod_cast h1) (by exact_mod_cast h3))
             (Pres.ext' (by exact_mod_cast h2) (by exact_mod_cast h4))

/-! ### Standard Result 3.1, existence half

    The book: "for every fixed oriented Farey frame `F`, a unique positive walk to
    every primitive finite descendant in the open interval between its
    boundaries." Uniqueness is `walk_inj` above with `mid_inj` (`State.lean`);
    the full statement is `existsUnique_addressed_of_between` there. Existence is
    the Stern-Brocot descent: compare `X` with the mediant, stop on equality, else
    step to the child whose interval holds `X`. The descent stops because the two
    determinants `Δ(X, C₋)` and `Δ(C₊, X)` are positive and their sum drops by
    one of them at every step. -/

/-- One letter on the left of a word is one `select` on the starting frame. -/
theorem addressed_cons (F : Frame) (b : Bool) (w : Word) :
    addressed F (b :: w) = addressed (select F b) w := rfl

/-- Inside a frame, `Δ(C₊, X) ≥ 1`, so the descent measure is positive. -/
theorem between_measure_pos (F : Frame) (X : Pres) (h2 : Pres.Lt X F.plus) :
    0 < (X.p * F.minus.q - X.q * F.minus.p) + (X.q * F.plus.p - X.p * F.plus.q) := by
  unfold Pres.Lt at h2
  have c2 := Nat.mul_comm F.plus.p X.q
  omega

/-- The descent, by induction on a bound for `Δ(X, C₋) + Δ(C₊, X)` (stated in
    `ℕ`: both differences are positive, so truncated subtraction is exact). -/
theorem exists_addressed_aux : ∀ (n : ℕ) (F : Frame) (X : Pres), Primitive X →
    Pres.Lt F.minus X → Pres.Lt X F.plus →
    (X.p * F.minus.q - X.q * F.minus.p) + (X.q * F.plus.p - X.p * F.plus.q) ≤ n →
    ∃ w : Word, addressed F w = X := by
  intro n
  induction n with
  | zero =>
      -- `omega` called here, inside the induction, reaches `Classical.choice`;
      -- the same goal as the standalone lemma above is choice-free.
      intro F X _ _ h2 hn
      exact absurd hn (Nat.not_le.mpr (between_measure_pos F X h2))
  | succ n ih =>
      intro F X hX h1 h2 hn
      unfold Pres.Lt at h1 h2
      have c1 := Nat.mul_comm F.minus.p X.q
      have c2 := Nat.mul_comm F.plus.p X.q
      have ep : X.q * F.mid.p = X.q * F.plus.p + X.q * F.minus.p := Nat.mul_add _ _ _
      have eq' : X.p * F.mid.q = X.p * F.plus.q + X.p * F.minus.q := Nat.mul_add _ _ _
      have c3 := Nat.mul_comm F.mid.p X.q
      rcases Nat.lt_trichotomy (X.p * F.mid.q) (F.mid.p * X.q) with hL | hE | hR
      · -- `X ≺ C₋ ⊕ C₊`: `X` lies in `F_L = (C₋ ⊕ C₊, C₋)`, and `Δ(C₊, X)` shrinks.
        obtain ⟨w, hw⟩ := ih (stepL F) X hX h1 hL (by
          change (X.p * F.minus.q - X.q * F.minus.p) + (X.q * F.mid.p - X.p * F.mid.q) ≤ n
          omega)
        exact ⟨false :: w, hw⟩
      · -- `X ~ C₋ ⊕ C₊`, and both are primitive, so `X` is the mediant: the empty word.
        refine ⟨[], (eq_of_prop_of_primitive (mediant_primitive F.contact) hX ?_)⟩
        change F.mid.p * X.q = F.mid.q * X.p
        have c4 := Nat.mul_comm F.mid.q X.p
        omega
      · -- `C₋ ⊕ C₊ ≺ X`: `X` lies in `F_R = (C₊, C₋ ⊕ C₊)`, and `Δ(X, C₋)` shrinks.
        obtain ⟨w, hw⟩ := ih (stepR F) X hX hR h2 (by
          change (X.p * F.mid.q - X.q * F.mid.p) + (X.q * F.plus.p - X.p * F.plus.q) ≤ n
          omega)
        exact ⟨true :: w, hw⟩

/-- **Standard Result 3.1, existence half.** Every primitive presentation strictly
    between a frame's boundaries, `C₋ ≺ X ≺ C₊`, is the addressed relation of a
    positive walk from that frame. "Finite" in the book's statement is not a
    separate hypothesis: `X ≺ C₊` forces `X.q ≠ 0` at `C₊ = 1:0`. -/
theorem exists_addressed_of_between (F : Frame) {X : Pres} (hX : Primitive X)
    (h1 : Pres.Lt F.minus X) (h2 : Pres.Lt X F.plus) :
    ∃ w : Word, addressed F w = X :=
  exists_addressed_aux _ F X hX h1 h2 (Nat.le_refl _)

end Frame

open Frame

/-! ## Definitions 3.7 and 3.8 — Event and history -/

/-- **Definition 3.7.** An elementary refinement event, as an unconstrained
    (frame, word) pair: any frame with any word, with no tie between them in the
    type. The update `(F, w) ↦ (F·g, wg)` is `Event.step`, which moves both
    components together; the tie of the frame to the word is
    `Event.CoherentFrom F₀` (the frame is the walk of the word from a declared
    start frame), preserved by `coherentFrom_step`. -/
structure Event where
  frame : Frame
  word : Word
deriving DecidableEq

namespace Event

def step (e : Event) (b : Bool) : Event := ⟨select e.frame b, e.word ++ [b]⟩

/-- Coherence from the canonical frame `F_∅` only: the frame is the walk of the
    word from `F_∅`. Def 3.7's update acts from any frame; that form is
    `CoherentFrom F₀`, at the end of this file. -/
def Coherent (e : Event) : Prop := e.frame = walk empty e.word

theorem coherent_step {e : Event} (h : Coherent e) (b : Bool) :
    Coherent (e.step b) := by
  change select e.frame b = walk empty (e.word ++ [b])
  rw [h]
  simp [walk, List.foldl_append]

end Event

/-- **Definition 3.8.** A history: the ordered record of the events that made the
    present state available. It retains the word, so it is lossless in the sense
    of Standard Result 3.1 — `walk_inj` says the word is recoverable from the
    frame inside the canonical domain, and `word` retains it unconditionally. -/
structure History where
  start : Frame
  word : Word
deriving DecidableEq

namespace History

def frame (H : History) : Frame := walk H.start H.word
def addressed (H : History) : Pres := Frame.addressed H.start H.word

/-- **The unrooted "world-frame" matrix, Elements II Def 3.3's object — not
    Def 9.3's `M_r`.** `G H.word` alone, with no `H.start` factor.
    Def 3.3 declares `Z_u(M) = G(u)M` and "prefixes the
    corresponding world words" as two faces of one transform, and that pair is
    only self-consistent when `M = G(word)` — `Z_u(G w) = G u * G w = G(u ++
    w)` by `G_append` alone, no assumption about a declared start.
    `ProposalRecord.fullMatrix` (`ElementsII/S04/Cavity.lean`) and the transport
    theorems of `ElementsII/S05/Mediant.lean` are built on exactly this reading
    and would go false under a start-aware one, since `H.start` and `G u` do
    not commute in general. -/
def matrix (H : History) : Mat2 := G H.word

/-- **`M_r`, Def 9.3 and Def 10.1's accumulated matrix.** Taken relative to
    the declared start, the same convention `Observer.matrix` uses:
    `H.start.toMat2 * G H.word`.
    `History.matrix` above is the different, unrooted object Def 3.3 needs;
    this is the one `Q_{O,r} = M_O⁻¹M_r` and `Candidate.matrix` (`Crystal.lean`)
    need, and giving it its own name rather than redefining `matrix` is
    what keeps both books' consumers correct at once. -/
def accumulatedMatrix (H : History) : Mat2 := H.start.toMat2 * G H.word

/-- Distinct histories from the canonical frame reach distinct frames. -/
theorem frame_inj {H K : History} (hs : H.start = K.start)
    (h : H.frame = K.frame) : H.word = K.word := by
  refine walk_inj H.start (h.trans ?_)
  rw [hs]
  rfl

end History

/-! ## Definition 3.9 — Parity shadow and refused alternatives -/

namespace Word

/-- **Definition 3.9.** `L̄ = R`, `R̄ = L`. -/
abbrev bar (b : Bool) : Bool := !b

/-- **Definition 3.9.** The parity shadow `w̄`, same order, every hand exchanged. -/
def shadow (w : Word) : Word := w.map bar

@[simp] theorem shadow_nil : shadow [] = [] := rfl
@[simp] theorem shadow_cons (b : Bool) (w : Word) :
    shadow (b :: w) = bar b :: shadow w := rfl

theorem P_gen_P (b : Bool) : P * gen b * P = gen (bar b) := by
  cases b <;> decide

/-- **Definition 3.9.** `G(w̄) = P G(w) P`. -/
theorem G_shadow (w : Word) : G (shadow w) = P * G w * P := by
  induction w with
  | nil => decide
  | cons b w ih =>
      rw [shadow_cons, G_cons, ih, ← P_gen_P b]
      have hPP : P * P = 1 := P_involutive
      calc P * gen b * P * (P * G w * P)
          = P * gen b * (P * P) * G w * P := by
            simp [Mat2.mul_assoc']
        _ = P * (gen b * G w) * P := by rw [hPP]; simp [Mat2.mul_assoc']
      

/-- **Definition 3.9.** The refused-alternative ledger: at each event, the actual
    prefix followed by the sibling branch not taken. -/
def refused (w : Word) : List Word :=
  (List.range w.length).map (fun k => w.take k ++ [bar (w.getD k false)])

@[simp] theorem refused_length (w : Word) : (refused w).length = w.length := by
  simp [refused]

/-- **Definition 3.9, witness computation.** On `w = LR` the shadow is `RL`,
    one word; the ledger is `[R, LL]`, two words, and neither of them is `RL`.
    This is an example only. What the two records share and what they do not is
    stated in general below: `refused_getLast`, `refused_entry_prefix`,
    `shadow_letter_forgets_prefix`, `refused_eq_iff_shadow_eq`. -/
theorem shadow_ne_refused :
    refused [false, true] = [[true], [false, false]] ∧
    shadow [false, true] = [true, false] := by
  constructor <;> decide

/-- **Definition 3.9.** The `k`-th ledger entry is the actual prefix `u_k`
    followed by the sibling not taken at event `k`. -/
theorem refused_getElem (w : Word) (k : ℕ) (hk : k < (refused w).length) :
    (refused w)[k] = w.take k ++ [bar (w[k]'(by simpa using hk))] := by
  have hk' : k < w.length := by simpa using hk
  simp [refused, List.getElem?_eq_getElem hk']

/-- **Definition 3.9.** The `k`-th letter of the shadow is the `k`-th letter
    exchanged. -/
theorem shadow_getElem (w : Word) (k : ℕ) (hk : k < (shadow w).length) :
    (shadow w)[k] = bar (w[k]'(by simpa [shadow] using hk)) := by
  simp [shadow]

/-- **Definition 3.9, what the two records share.** The last letter of the
    `k`-th ledger entry is the `k`-th letter of the parity shadow: the shadow is
    the ledger with every prefix dropped. -/
theorem refused_getLast (w : Word) (k : ℕ) (hk : k < (refused w).length) :
    ((refused w)[k]).getLast (by simp [refused_getElem]) =
      (shadow w)[k]'(by simpa [shadow] using hk) := by
  simp [refused_getElem, shadow_getElem]

/-- **Definition 3.9, what a ledger entry keeps.** "Its `k`-th entry preserves
    the actual prefix": two words whose `k`-th ledger entries agree agree on
    their first `k + 1` letters. One entry fixes the whole history up to that
    event. -/
theorem refused_entry_prefix {w v : Word} {k : ℕ} (hw : k < w.length) (hv : k < v.length)
    (h : (refused w)[k]'(by simpa using hw) = (refused v)[k]'(by simpa using hv)) :
    w.take (k + 1) = v.take (k + 1) := by
  rw [refused_getElem, refused_getElem] at h
  have hl : (w.take k).length = (v.take k).length := by simp; omega
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  simp only [List.cons.injEq, and_true, Bool.not_inj_iff] at h2
  rw [List.take_add_one, List.take_add_one, h1, List.getElem?_eq_getElem hw,
    List.getElem?_eq_getElem hv]
  simp [h2]

/-- **Definition 3.9, what a shadow letter does not keep.** The matching
    statement for the shadow fails: `LL` and `RL` have the same second shadow
    letter and different first two letters. In general the `k`-th shadow letter
    is `bar w[k]` alone (`shadow_getElem`): the exchanged hand at one event,
    with no prefix. -/
theorem shadow_letter_forgets_prefix :
    (shadow [false, false])[1] = (shadow [true, false])[1] ∧
    ([false, false] : Word).take 2 ≠ ([true, false] : Word).take 2 := by decide

theorem refused_injective : Function.Injective refused := by
  intro w v h
  have hlen : w.length = v.length := by
    rw [← refused_length w, ← refused_length v, h]
  rcases Nat.eq_zero_or_pos w.length with h0 | hpos
  · have : v.length = 0 := hlen ▸ h0
    rw [List.length_eq_zero_iff] at h0 this; rw [h0, this]
  · have hw : w.length - 1 < w.length := by omega
    have hv : w.length - 1 < v.length := by omega
    have := refused_entry_prefix hw hv (by simp only [h])
    rw [Nat.sub_add_cancel hpos, List.take_length, hlen, List.take_length] at this
    exact this

theorem shadow_injective : Function.Injective shadow := by
  intro w v h
  have hss : ∀ u : Word, shadow (shadow u) = u := fun u => by
    induction u with
    | nil => rfl
    | cons b u ih => simp [ih]
  have := congrArg shadow h
  rwa [hss, hss] at this

/-- **Definition 3.9, the whole records.** Taken whole, the ledger and the
    shadow separate exactly the same words: each determines `w`. So "retain
    different information" is proved here entry by entry (`refused_entry_prefix`
    against `shadow_letter_forgets_prefix`), and it does not hold in the sense of
    which words the complete records distinguish. Other readings of the book's
    sentence, such as each ledger entry being readable on its own as an
    address, are not stated here. -/
theorem refused_eq_iff_shadow_eq (w v : Word) :
    refused w = refused v ↔ shadow w = shadow v :=
  ⟨fun h => by rw [refused_injective h], fun h => by rw [shadow_injective h]⟩

/-! ## Proposition 3.2 — Retrospective positive reflection -/

/-- **Proposition 3.2.** `S`, the quarter turn. -/
def S : Mat2 := ⟨0, -1, 1, 0⟩

/-- `S⁻¹` is `Braid.lean`'s half twist `Δ`. The two files use the same
    matrix under different names; this is the identification. -/
theorem S_mul_Δ : S * Δ = 1 := by decide
theorem Δ_mul_S : Δ * S = 1 := by decide
theorem S_eq_neg_Δ : S = -Δ := by decide

/-- **Proposition 3.2.** `S L⁻¹ S⁻¹ = R` and `S R⁻¹ S⁻¹ = L`: conjugation by `S`
    sends each inverse generator to the opposite positive generator. -/
theorem S_conj_gen (b : Bool) : S * inv2 (gen b) * Δ = gen (bar b) := by
  cases b <;> decide

/-- **Definition 3.9 / Proposition 3.2.** `rs(w) = ḡₙ⋯ḡ₁`: reversed and
    side-exchanged. -/
def rs (w : Word) : Word := (shadow w).reverse

@[simp] theorem rs_snoc (w : Word) (b : Bool) : rs (w ++ [b]) = bar b :: rs w := by
  simp [rs, shadow, List.map_append]

/-- **Proposition 3.2, the boxed identity.** `S G(w)⁻¹ S⁻¹ = G(rs(w))`.

    Retrospective reflection is not history erasure: inverse history is received
    as a new positive forward presentation, with reversed order and exchanged
    hand. Both halves of that sentence are in the statement — `reverse` and
    `shadow` — and the result stays inside `ℳ₊`. -/
theorem S_conj_inv_G (w : Word) : S * inv2 (G w) * Δ = G (rs w) := by
  induction w using List.reverseRecOn with
  | nil => decide
  | append_singleton w b ih =>
      rw [G_snoc, Mat2.inv2_mul, rs_snoc, G_cons, ← ih, ← S_conj_gen b]
      have hSΔ : Δ * S = 1 := Δ_mul_S
      calc S * (inv2 (gen b) * inv2 (G w)) * Δ
          = S * inv2 (gen b) * (Δ * S) * inv2 (G w) * Δ := by
            rw [hSΔ]; simp [Mat2.mul_assoc']
        _ = S * inv2 (gen b) * Δ * (S * inv2 (G w) * Δ) := by
            simp [Mat2.mul_assoc']

/-- The reflection lands back in the positive monoid: `rs(w)` is a word. -/
theorem S_conj_inv_G_mem (w : Word) : S * inv2 (G w) * Δ ∈ Mplus :=
  ⟨rs w, (S_conj_inv_G w).symm⟩

/-! ## Definition 3.10 — Central lift sign -/

/-- **Definition 3.10.** `T := R`. -/
abbrev T : Mat2 := R

/-- **Definition 3.10.** `-I = S² = (ST)³`. `Braid.lean` has the first half as
    `full_twist` for `Δ`; this is the book's form, and the `(ST)³` half is
    proved here. -/
theorem neg_one_eq_S_sq : S * S = -1 := by decide

theorem neg_one_eq_ST_cubed : (S * T) * (S * T) * (S * T) = -1 := by decide

/-- **Definition 3.10, centrality.** `-I` commutes with every `2×2` integer
    matrix. This is the theorem behind the word "central"; `full_twist`,
    `neg_one_eq_S_sq` and `neg_one_eq_ST_cubed` only say what `-I` equals. -/
theorem neg_one_central (M : Mat2) : (-1 : Mat2) * M = M * (-1 : Mat2) := by
  cases M with
  | mk a b c d =>
    change Mat2.mul ⟨-1, -0, -0, -1⟩ ⟨a, b, c, d⟩ = Mat2.mul ⟨a, b, c, d⟩ ⟨-1, -0, -0, -1⟩
    simp only [Mat2.mul, Mat2.mk.injEq]
    refine ⟨by ring, by ring, by ring, by ring⟩

/-- **Definition 3.10.** Conjugation by the central lift `-I` fixes `L` and `R`:
    it does not exchange hands, where conjugation by `P` does (`P_gen_P`, the
    shadow) and conjugation by `S` does on inverses (`S_conj_gen`, `rs`). That
    the sign it carries is the one discarded by `SL(2,ℤ) → PSL(2,ℤ)` is the
    book's reading and is not stated here. -/
theorem central_lift_fixes_gen (b : Bool) :
    (-1 : Mat2) * gen b * (-1 : Mat2) = gen b := by cases b <;> decide

/-- **Definition 3.10, the three word-valued records.** On `w = LR`: the
    shadow is `RL`, the reversal is `RL`, and `rs` is `LR` again; on `LL` the
    shadow and the reversal differ. So `shadow`, `reverse` and `rs` are pairwise
    distinct functions even where two of them agree on an argument
    (`word_records_pairwise_ne`). The other two of the book's five records are
    not separated by a theorem here. The refused ledger has a different type
    (`List Word`, not `Word`); against the shadow it differs entry by entry
    (`refused_entry_prefix` against `shadow_letter_forgets_prefix`), while as a
    whole record it separates the same words (`refused_eq_iff_shadow_eq`). The
    central sign `-I` is a matrix, not a word map; `central_lift_fixes_gen`
    contrasts it with the two hand-exchanging records only, through `P_gen_P`
    (the shadow) and `S_conj_gen` (`rs`). -/
theorem records_distinct :
    shadow [false, true] = [true, false] ∧
    (List.reverse [false, true] : Word) = [true, false] ∧
    rs [false, true] = [false, true] ∧
    shadow [false, false] ≠ (List.reverse [false, false] : Word) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **Definition 3.10.** The three word-valued records are pairwise distinct
    functions, read off the witnesses of `records_distinct`. -/
theorem word_records_pairwise_ne :
    (shadow : Word → Word) ≠ List.reverse ∧ (shadow : Word → Word) ≠ rs ∧
    (List.reverse : Word → Word) ≠ rs := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact absurd (congrFun h [false, false]) (by decide)
  · exact absurd (congrFun h [false, true]) (by decide)
  · exact absurd (congrFun h [false, true]) (by decide)

end Word

/-! ## Definition 3.11 — Levels of equality

    Eight relations, not four. Each is a named `Prop` on history-bearing states,
    and none of them is the type's `=`. The book says no implication may be
    reversed without proof; below, the ones that *do* hold on the tree are proved,
    and the ones that fail have witnesses. -/

open Word

namespace History

variable (X Y : History)

/-- 1. **Presentation equality.** The integer pairs of the state's frame agree
       component by component. -/
def PresEq : Prop := X.frame.plus = Y.frame.plus ∧ X.frame.minus = Y.frame.minus

/-- 2. **Value equality.** The addressed presentations are proportionally
       equivalent. -/
def ValueEq : Prop := X.addressed ~ Y.addressed

/-- 3. **Endpoint equality.** The selected addressed relations agree. -/
def EndpointEq : Prop := X.addressed = Y.addressed

/-- 4. **Word equality.** The ordered generator strings agree. -/
def WordEq : Prop := X.word = Y.word

/-- 5. **Matrix equality.** The accumulated matrices agree. The accumulated
       matrix is Def 3.4's `M_{F_n} = M_{F_0} G(w)`, read from the history's
       declared start: `History.accumulatedMatrix`, not the unrooted
       `History.matrix = G(w)`; `X.matrix = Y.matrix` is `WordMatrixEq`
       below. -/
def MatrixEq : Prop := X.accumulatedMatrix = Y.accumulatedMatrix

/-- The unrooted matrix equality `G(w_X) = G(w_Y)`, which drops the start
    frame. It is only word equality under another name (`wordMatrixEq_iff_wordEq`); it is not the
    book's level 5 (`wordMatrixEq_not_matrixEq`). -/
def WordMatrixEq : Prop := X.matrix = Y.matrix

/-- 6. **Closure equality**, relative to a stated closure map. The book requires
       the map to be named; here it is a parameter, so an unstated closure cannot
       be appealed to. This form is a closure map on accumulated matrices, so it
       reads `accumulatedMatrix` as level 5 does; a closure on
       histories or words (Def 8.2: "The domain must be stated") is
       `ClosureEqBy`. -/
def ClosureEq (κ : Mat2 → Mat2) : Prop := κ X.accumulatedMatrix = κ Y.accumulatedMatrix

/-- 6, **with the closure's domain stated as histories.** The book's closure
    maps may be taken on histories, words or accumulated matrices, and the
    domain must be stated. `ClosureEq κ` is this with `κ` taken on the
    accumulated matrix (`closureEq_eq_closureEqBy`); a word-level closure is
    `κ ∘ History.word`. -/
def ClosureEqBy {K : Type} (κ : History → K) : Prop := κ X = κ Y

theorem closureEq_eq_closureEqBy (κ : Mat2 → Mat2) :
    X.ClosureEq Y κ = X.ClosureEqBy Y (fun H => κ H.accumulatedMatrix) := rfl

/-- 7. **Reception equality**, relative to a specified observer. Same discipline:
       the observer is an argument. -/
def ReceptionEq {α : Type} (obs : History → α) : Prop := obs X = obs Y

/-- 8. **Projection equality.** A specified projection reads both the same way.
       The canonical one is Def 1.7, and it is the only `ℚ` in this file. -/
def ProjectionEq : Prop := nu X.addressed = nu Y.addressed

/-- 8, **parametrised.** The book's level 8 is "a specified projection maps both
    to the same reading". Same discipline as levels 6 and 7: the projection is
    an argument. `ProjectionEq` is this at `ν` (`projectionEq_eq_projectionEqBy_nu`). -/
def ProjectionEqBy {α : Type} (π : Pres → α) : Prop := π X.addressed = π Y.addressed

theorem projectionEq_eq_projectionEqBy_nu : X.ProjectionEq Y = X.ProjectionEqBy Y nu := rfl

end History

/-- Two proportional primitive presentations are equal. Standard, and it is the
    lemma that collapses levels 2 and 3 on the tree. -/
theorem prop_iff_eq_of_primitive {A B : Pres} (hA : Primitive A) (hB : Primitive B)
    (h : A ~ B) : A = B :=
  Pres.eq_of_prop_of_primitive hA hB h

namespace History

/-- Every addressed relation is primitive, whatever frame the history started in:
    on-tree, `reduce` never fires. -/
theorem addressed_primitive (H : History) : Primitive H.addressed :=
  walk_mid_primitive H.start H.word

/-- **Levels 2 and 3 coincide on the tree.** Every addressed relation is
    primitive, so proportional equivalence of two addressed relations is already
    structural equality. The book's warning that value equality is weaker than
    endpoint equality is a statement about the projection layer, not about
    anything a walk can reach — and it needs no hypothesis on the starting frame. -/
theorem valueEq_iff_endpointEq {X Y : History} : X.ValueEq Y ↔ X.EndpointEq Y := by
  constructor
  · exact fun h =>
      prop_iff_eq_of_primitive (addressed_primitive X) (addressed_primitive Y) h
  · intro h
    change X.addressed ~ Y.addressed
    rw [h]
    exact Pres.prop_refl _

/-- **The unrooted matrix equality is word equality**, by freeness of `G`
    (Standard Result 3.1). It says nothing about the book's level 5, whose
    matrix carries the start frame. -/
theorem wordMatrixEq_iff_wordEq {X Y : History} : X.WordMatrixEq Y ↔ X.WordEq Y :=
  ⟨fun h => Frame.G_inj h, fun h => by
    change G X.word = G Y.word
    rw [show X.word = Y.word from h]⟩

/-- The accumulated matrix is the final frame's matrix: Def 3.4's
    `M_{F_n} = M_{F_0} G(w)`, by `toMat2_walk`. -/
theorem accumulatedMatrix_eq_frame_toMat2 (H : History) :
    H.accumulatedMatrix = H.frame.toMat2 :=
  (Frame.toMat2_walk H.start H.word).symm

/-- A frame is recovered from its matrix: the four entries are the two
    boundaries' components. -/
theorem _root_.RatioSpace.Frame.toMat2_injective {F K : Frame}
    (h : F.toMat2 = K.toMat2) : F = K := by
  have ha := congrArg Mat2.a h
  have hb := congrArg Mat2.b h
  have hc := congrArg Mat2.c h
  have hd := congrArg Mat2.d h
  simp only [Frame.toMat2, Nat.cast_inj] at ha hb hc hd
  exact Frame.ext' (Pres.ext' ha hc) (Pres.ext' hb hd)

/-- **Levels 1 and 5 coincide on every pair of histories**, whatever their
    start frames. The accumulated matrix is the final frame's matrix, and a
    frame is its two boundaries' integer pairs, so equal accumulated matrices
    are equal presentations and conversely. -/
theorem matrixEq_iff_presEq {X Y : History} : X.MatrixEq Y ↔ X.PresEq Y := by
  unfold MatrixEq PresEq
  rw [accumulatedMatrix_eq_frame_toMat2, accumulatedMatrix_eq_frame_toMat2]
  constructor
  · intro h
    have hF := Frame.toMat2_injective h
    exact ⟨congrArg Frame.plus hF, congrArg Frame.minus hF⟩
  · rintro ⟨hp, hm⟩
    rw [Frame.ext' hp hm]

/-- **Levels 4 and 5 coincide for histories with one start frame**, by
    freeness (Standard Result 3.1, through `walk_inj`). The shared start is a
    hypothesis, not a convenience: without it level 5 does not imply level 4
    (`matrixEq_not_wordEq`). -/
theorem matrixEq_iff_wordEq {X Y : History} (hs : X.start = Y.start) :
    X.MatrixEq Y ↔ X.WordEq Y := by
  unfold MatrixEq WordEq
  rw [accumulatedMatrix_eq_frame_toMat2, accumulatedMatrix_eq_frame_toMat2]
  constructor
  · intro h
    exact History.frame_inj hs (Frame.toMat2_injective h)
  · intro h
    change (walk X.start X.word).toMat2 = (walk Y.start Y.word).toMat2
    rw [hs, h]

/-- **Level 5 does not imply level 4** once the start frame may vary.
    `(F_R, ε)` and `(F_∅, R)` have the same accumulated matrix `R` and
    different words; it is the pair `endpointEq_not_wordEq` uses. -/
theorem matrixEq_not_wordEq :
    (History.mk (Frame.stepR Frame.empty) []).MatrixEq (History.mk Frame.empty [true])
      ∧ ¬ (History.mk (Frame.stepR Frame.empty) []).WordEq (History.mk Frame.empty [true]) := by
  unfold MatrixEq WordEq
  refine ⟨by decide, by decide⟩

/-- **The unrooted matrix equality does not give level 5.** `(F_R, R)` and
    `(F_∅, R)` have the same word, so the same `G(w)`, and different
    accumulated matrices `R²` and `R`. -/
theorem wordMatrixEq_not_matrixEq :
    (History.mk (Frame.stepR Frame.empty) [true]).WordMatrixEq (History.mk Frame.empty [true])
      ∧ ¬ (History.mk (Frame.stepR Frame.empty) [true]).MatrixEq
          (History.mk Frame.empty [true]) := by
  unfold WordMatrixEq MatrixEq
  refine ⟨by decide, by decide⟩

/-- **`ν` is not injective on presentations.** `ν` identifies `1:2` and `2:4`,
    two different presentations. This is a fact about presentations, not about
    histories: `2:4` is not primitive, so no walk addresses it, and on histories
    levels 8 and 3 coincide under `ν` (`projectionEq_iff_endpointEq`). The
    separation of level 8 from level 3 on the tree needs a specified projection
    (`projectionEqBy_not_endpointEq`). -/
theorem nu_not_injective_on_pres :
    nu Pres.oneTwo = nu Pres.twoFour ∧ Pres.oneTwo ≠ Pres.twoFour :=
  ⟨Pres.nu_of_prop Pres.oneTwo_prop_twoFour, Pres.oneTwo_ne_twoFour⟩

/-- **Under `ν`, levels 8 and 3 coincide on histories.** Addressed relations are
    primitive and `ν` is injective on primitives, so the separation above is
    between presentations, never between two history-bearing states. -/
theorem projectionEq_iff_endpointEq {X Y : History} : X.ProjectionEq Y ↔ X.EndpointEq Y :=
  ⟨fun h => Pres.nu_injective_on_primitive (addressed_primitive X) (addressed_primitive Y) h,
   fun h => by
    change nu X.addressed = nu Y.addressed
    rw [show X.addressed = Y.addressed from h]⟩

/-- The same coincidence for any specified projection injective on primitives. -/
theorem projectionEqBy_iff_endpointEq_of_injective {X Y : History} {α : Type}
    {π : Pres → α} (hπ : ∀ A B, Primitive A → Primitive B → π A = π B → A = B) :
    X.ProjectionEqBy Y π ↔ X.EndpointEq Y :=
  ⟨fun h => hπ _ _ (addressed_primitive X) (addressed_primitive Y) h,
   fun h => by
    change π X.addressed = π Y.addressed
    rw [show X.addressed = Y.addressed from h]⟩

/-- **Level 8 under a non-injective projection does not imply level 3 on
    histories.** Reading only the first component, the empty word (`1:1`) and
    `[false]` (`1:2`) from `F_∅` read the same and address different relations.
    So level 8 can separate from level 3 when the specified projection
    forgets something the tree distinguishes. -/
theorem projectionEqBy_not_endpointEq :
    (History.mk Frame.empty []).ProjectionEqBy (History.mk Frame.empty [false]) Pres.p
      ∧ ¬ (History.mk Frame.empty []).EndpointEq (History.mk Frame.empty [false]) := by
  unfold ProjectionEqBy EndpointEq
  refine ⟨by decide, by decide⟩

/-- **Level 3 does not imply level 4** for arbitrary starting frames: two
    different words can address the same relation from different frames. The
    canonical-domain hypothesis in Standard Result 3.1 is doing real work. -/
theorem endpointEq_not_wordEq :
    (History.mk (Frame.stepR Frame.empty) []).addressed
      = (History.mk Frame.empty [true]).addressed
    ∧ ([] : Word) ≠ [true] := by
  refine ⟨by decide, by decide⟩

end History

/-! ## Definition 3.7 from a declared frame

    `Event.Coherent` above reads coherence against `F_∅` only:
    `e.frame = walk empty e.word`. Def 3.7's update `(F, w) ↦ (F·g, wg)` is
    stated for any frame `F`, and `Event.step` already acts on any frame; only
    the invariant was tied to the canonical start. `CoherentFrom F₀` reads it
    against a declared start frame `F₀`, and `Coherent` is the case
    `F₀ = F_∅` (`coherent_iff_coherentFrom_empty`). That the start frame is
    fixed by the event, and the tie to `SubstrateState`'s declared origin, are
    in `State.lean` (`Event.coherentFrom_start_unique`,
    `SubstrateState.toEvent_coherentFrom`), where `Frame.walk_left_inj` is. -/

namespace Event

/-- **Definition 3.7's coherence, from a declared start frame.** The frame
    component of the event is the walk of its word from `F₀`. -/
def CoherentFrom (F₀ : Frame) (e : Event) : Prop := e.frame = walk F₀ e.word

/-- `Coherent` is `CoherentFrom` at the canonical frame `F_∅`. -/
theorem coherent_iff_coherentFrom_empty {e : Event} :
    Coherent e ↔ CoherentFrom Frame.empty e := Iff.rfl

/-- The event that has made no update yet is coherent from its own frame. -/
theorem coherentFrom_nil (F₀ : Frame) : CoherentFrom F₀ ⟨F₀, []⟩ := rfl

/-- **Def 3.7's update preserves coherence from any start frame.**
    `coherent_step` is the case `F₀ = F_∅`. -/
theorem coherentFrom_step {F₀ : Frame} {e : Event} (h : CoherentFrom F₀ e)
    (b : Bool) : CoherentFrom F₀ (e.step b) := by
  change select e.frame b = walk F₀ (e.word ++ [b])
  rw [h, walk_snoc]

/-- The event reached from `(F₀, ε)` by Def 3.7's update, one letter of `w`
    at a time. -/
def run (F₀ : Frame) (w : Word) : Event := w.foldl step ⟨F₀, []⟩

theorem run_eq (F₀ : Frame) (w : Word) : run F₀ w = ⟨walk F₀ w, w⟩ := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b ih =>
      unfold run at ih ⊢
      rw [List.foldl_append, ih]
      change (⟨select (walk F₀ w) b, w ++ [b]⟩ : Event) = ⟨walk F₀ (w ++ [b]), w ++ [b]⟩
      rw [walk_snoc]

/-- **The events coherent from `F₀` are exactly the runs of Def 3.7's update
    from `(F₀, ε)`.** -/
theorem coherentFrom_iff_eq_run {F₀ : Frame} {e : Event} :
    CoherentFrom F₀ e ↔ e = run F₀ e.word := by
  obtain ⟨F, w⟩ := e
  rw [run_eq]
  constructor
  · intro h
    change F = walk F₀ w at h
    rw [h]
  · intro h
    exact congrArg Event.frame h

/-- An event coherent from `F₀` is Def 3.8's history `(F₀, w)` read at its
    frame. -/
theorem coherentFrom_iff_history_frame {F₀ : Frame} {e : Event} :
    CoherentFrom F₀ e ↔ e.frame = (History.mk F₀ e.word).frame := Iff.rfl

/-- **`Coherent` is strictly narrower than Def 3.7.** The event `(F_R, ε)` is
    coherent from its own frame `F_R` and not from `F_∅`. -/
theorem coherentFrom_not_coherent :
    CoherentFrom (stepR Frame.empty) ⟨stepR Frame.empty, []⟩
      ∧ ¬ Coherent ⟨stepR Frame.empty, []⟩ := by
  refine ⟨rfl, ?_⟩
  unfold Coherent
  decide

end Event

end RatioSpace
