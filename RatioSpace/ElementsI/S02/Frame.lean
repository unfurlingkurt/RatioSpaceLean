/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S01.Pres
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-!
  Elements I §2 — Contact, frame, triad, and inherited construction.

  Definitions 2.1 through 2.5 and Proposition 2.1, built the way the book builds
  them: **a frame is an ordered pair of presentations in contact, and the matrix
  is derived notation.** Def 2.2 says so directly. The previous version of this
  file made the four integers primitive and recovered the pair afterwards, which
  keeps the value and drops the relation that produced it.

  Two consequences of putting the pair first, and they are the reason for it:

    * Contact is no longer a theorem, it is a field. `det_walk` used to prove
      that no word of steps can break contact. Now no term of type `Frame` can
      be written that does not have it, so the walk cannot break what it cannot
      construct. The old theorem survives below as a one-line corollary.

    * `stepL` and `stepR` were interchanged relative to Def 2.4 and Def 3.1.
      `M_F L` puts the mediant in the FIRST column, the `C₊` column, so
      `F_L = (C₋ ⊕ C₊, C₋)`. The old `stepL` overwrote the second column, which
      is `F_R`. Corrected here to the book's convention. The Def 3.1 check,
      `M_F L = M_{F_L}` and `M_F R = M_{F_R}` with the matrices `L` and `R`
      themselves, is `Frame.toMat2_stepL` / `Frame.toMat2_stepR` in `Walk.lean`
      (it needs `Mat2` and `Frame.toMat2`, which this file does not import). `stepL_matrix` and
      `stepR_matrix` below only unfold the child frame's four entries.

  Everything is ℕ-valued and division-free. Contact is stated as
  `p₊ q₋ = q₊ p₋ + 1` rather than as a subtraction, so no truncation and no cast
  is needed to say it. The signed `Δ` of Def 2.1 is kept over ℤ, where it belongs,
  and the two are reconciled in `contact_iff_delta_one`.

  The book's `⊕` is spelled `Pres.mediant` here rather than given notation, since
  `⊕` is already mathlib's disjoint sum and a clash on the mixing operation is
  the last place to want one.
-/

namespace RatioSpace

open Pres

/-! ## Definition 2.1 — Determinant contact -/

/-- **Definition 2.1.** The signed determinant of two presentations,
    `Δ(A,B) = ad − bc` for `A = a:b` and `B = c:d`. Signed, so it lives over `ℤ`;
    this is the one place a negative number is meaningful, because it is exactly
    what orientation means. -/
def Delta (A B : Pres) : ℤ := (A.p : ℤ) * B.q - (A.q : ℤ) * B.p

/-- **Definition 2.1.** Primitive Farey contact: an exact adjacency relation, not
    a distance. It does not presuppose a background line. -/
def PrimitiveContact (A B : Pres) : Prop := Delta A B = 1 ∨ Delta A B = -1

/-- **Positively oriented** contact, the `Δ = +1` half. Stated additively, so it
    is a statement about `ℕ` with no subtraction anywhere in it. -/
def Contact (A B : Pres) : Prop := A.p * B.q = A.q * B.p + 1

instance : DecidableRel Contact := fun A B => by unfold Contact; infer_instance

theorem contact_iff_delta_one (A B : Pres) : Contact A B ↔ Delta A B = 1 := by
  -- 2026-09-22: `omega` over the cast equation in place of `push_cast`/`linarith`/`exact_mod_cast`,
  -- which reached `Classical.choice`; this lemma sits under every frame determinant.
  unfold Contact Delta
  constructor
  · intro h
    have h' : ((A.p * B.q : ℕ) : ℤ) = ((A.q * B.p + 1 : ℕ) : ℤ) := congrArg (Nat.cast : ℕ → ℤ) h
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h'
    omega
  · intro h
    have h' : ((A.p * B.q : ℕ) : ℤ) = ((A.q * B.p + 1 : ℕ) : ℤ) := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      omega
    exact Int.natCast_inj.mp h'

theorem contact_primitive {A B : Pres} (h : Contact A B) : PrimitiveContact A B :=
  Or.inl ((contact_iff_delta_one A B).mp h)

/-- **The column order is not cosmetic.** Reversing it reverses orientation:
    `Δ(B,A) = −Δ(A,B)`. This is the whole content of the remark after Def 2.2. -/
theorem delta_swap (A B : Pres) : Delta B A = -Delta A B := by
  unfold Delta; ring

/-- A swapped pair sits at `−1`, so it is in primitive Farey contact but is not a
    positively oriented frame. Orientation is real, and it is one bit. -/
theorem contact_swap_neg {A B : Pres} (h : Contact A B) : Delta B A = -1 := by
  rw [delta_swap, (contact_iff_delta_one A B).mp h]

/-- **Definition 2.2's hypothesis, order plus adjacency, is exactly `Contact`.**
    The book assumes "`C₋ ≺ C₊` Farey-adjacent" and concludes `det M_F = 1`. Here
    `Contact A B` (`Δ(A,B) = +1`) holds exactly when `B ≺ A` (Def 1.6) and the two
    are in primitive Farey contact (`Δ = ±1`, Def 2.1): adjacency fixes `|Δ| = 1`
    and the order fixes its sign. So the determinant field of `Frame` says no more
    and no less than the book's hypothesis. Elements I gap G1-01. -/
theorem contact_iff_lt_primitiveContact (A B : Pres) :
    Contact A B ↔ (Pres.Lt B A ∧ PrimitiveContact A B) := by
  constructor
  · intro h
    refine ⟨?_, contact_primitive h⟩
    unfold Contact at h
    unfold Pres.Lt
    rw [Nat.mul_comm B.p A.q]
    omega
  · rintro ⟨hlt, hpc⟩
    unfold Pres.Lt at hlt
    have hlt' : ((B.p * A.q : ℕ) : ℤ) < ((A.p * B.q : ℕ) : ℤ) := Int.ofNat_lt.mpr hlt
    simp only [Nat.cast_mul] at hlt'
    refine (contact_iff_delta_one A B).mpr ?_
    unfold PrimitiveContact Delta at *
    rcases hpc with h | h
    · exact h
    · exfalso
      rw [Int.mul_comm (B.p : ℤ) (A.q : ℤ)] at hlt'
      omega

/-- The order half on its own: in positively oriented contact the second
    boundary precedes the first. -/
theorem Contact.lt {A B : Pres} (h : Contact A B) : Pres.Lt B A :=
  ((contact_iff_lt_primitiveContact A B).mp h).1

/-! ## Definition 2.3 — Mediant inheritance -/

/-- **Definition 2.3.** `A ⊕ B = (a+c):(b+d)`. Not an arithmetic mean: no
    division by two occurs, and it inherits both components of both parents. -/
def Pres.mediant (A B : Pres) : Pres :=
  ⟨A.p + B.p, A.q + B.q, by rintro ⟨h1, h2⟩; exact A.ne_zero ⟨by omega, by omega⟩⟩

@[simp] theorem mediant_p (A B : Pres) : (Pres.mediant A B).p = A.p + B.p := rfl
@[simp] theorem mediant_q (A B : Pres) : (Pres.mediant A B).q = A.q + B.q := rfl

/-- **Proposition 2.1, left half.** Contact is inherited: `Δ(C₊, C) = 1`, where
    `C` is the mediant. -/
theorem contact_mediant_right {A B : Pres} (h : Contact A B) :
    Contact A (Pres.mediant A B) := by
  have hc : A.p * B.q = A.q * B.p + 1 := h
  change A.p * (A.q + B.q) = A.q * (A.p + B.p) + 1
  calc A.p * (A.q + B.q) = A.p * A.q + A.p * B.q := by ring
    _ = A.p * A.q + (A.q * B.p + 1) := by rw [hc]
    _ = A.q * (A.p + B.p) + 1 := by ring

/-- **Proposition 2.1, right half.** Contact is inherited: `Δ(C, C₋) = 1`. -/
theorem contact_mediant_left {A B : Pres} (h : Contact A B) :
    Contact (Pres.mediant A B) B := by
  have hc : A.p * B.q = A.q * B.p + 1 := h
  change (A.p + B.p) * B.q = (A.q + B.q) * B.p + 1
  calc (A.p + B.p) * B.q = A.p * B.q + B.p * B.q := by ring
    _ = (A.q * B.p + 1) + B.p * B.q := by rw [hc]
    _ = (A.q + B.q) * B.p + 1 := by ring

/-- **The mediant of a contact pair is primitive.** Nothing to reduce, so
    `reduce` is a no-op on-tree and a declared projection off it. The witness is
    exact: `d(a+c) − c(b+d) = ad − bc = 1`, so any common divisor divides `1`. -/
theorem mediant_primitive {A B : Pres} (h : Contact A B) :
    Primitive (Pres.mediant A B) := by
  have hc : A.p * B.q = A.q * B.p + 1 := h
  change Nat.gcd (A.p + B.p) (A.q + B.q) = 1
  have h1 : Nat.gcd (A.p + B.p) (A.q + B.q) ∣ (A.p + B.p) := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (A.p + B.p) (A.q + B.q) ∣ (A.q + B.q) := Nat.gcd_dvd_right _ _
  have key : B.q * (A.p + B.p) = B.p * (A.q + B.q) + 1 := by
    calc B.q * (A.p + B.p) = A.p * B.q + B.p * B.q := by ring
      _ = (A.q * B.p + 1) + B.p * B.q := by rw [hc]
      _ = B.p * (A.q + B.q) + 1 := by ring
  have hd1 : Nat.gcd (A.p + B.p) (A.q + B.q) ∣ B.p * (A.q + B.q) + 1 :=
    key ▸ h1.mul_left B.q
  have hd2 : Nat.gcd (A.p + B.p) (A.q + B.q) ∣ B.p * (A.q + B.q) := h2.mul_left B.p
  exact Nat.dvd_one.mp ((Nat.dvd_add_right hd2).mp hd1)

/-- **The mediant of a contact pair is interior, not only primitive.** Both
    components are strictly positive: contact reads `A.p * B.q = A.q * B.p +
    1`, so `A.p = 0 ∧ B.p = 0` forces `0 = 1` on that equation, and the `q`
    case is symmetric. `mediant_primitive` above is the coprimality half of
    the same pair; this is the positivity half. Depth.lean's `ip` witnesses
    stand in for it today by naming presentations directly, because this fact
    did not yet exist — the comment there says so. -/
theorem mediant_pos {A B : Pres} (h : Contact A B) :
    0 < (Pres.mediant A B).p ∧ 0 < (Pres.mediant A B).q := by
  have hc : A.p * B.q = A.q * B.p + 1 := h
  refine ⟨?_, ?_⟩
  · rw [mediant_p]
    rcases Nat.eq_zero_or_pos (A.p + B.p) with h0 | hpos
    · exfalso
      have hA : A.p = 0 := by omega
      have hB : B.p = 0 := by omega
      simp [hA, hB] at hc
    · exact hpos
  · rw [mediant_q]
    rcases Nat.eq_zero_or_pos (A.q + B.q) with h0 | hpos
    · exfalso
      have hA : A.q = 0 := by omega
      have hB : B.q = 0 := by omega
      simp [hA, hB] at hc
    · exact hpos

/-! ## Definition 2.2 — Positively oriented unimodular frame -/

/-- **Definition 2.2.** A frame is the ordered pair `F = (C₊, C₋)` of
    Farey-adjacent boundaries, written in right-left column order, together with
    the fact that they are in positively oriented contact.

    **Contact is a field, not a theorem.** There is no term of this type that is
    out of contact, so nothing downstream has to prove that a construction stayed
    on the tree; it could not have left it. -/
structure Frame where
  plus : Pres
  minus : Pres
  contact : Contact plus minus
deriving DecidableEq

namespace Frame

/-- The derived frame matrix `M_F`, columns `(C₊, C₋)`, read off the pair. This
    is notation for the state and never the state itself. -/
def matrix (F : Frame) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((F.plus.p, F.plus.q), (F.minus.p, F.minus.q))

/-- `det M_F = p₊q₋ − p₋q₊`, which is `Δ(C₊, C₋)`. -/
def det (F : Frame) : ℤ := Delta F.plus F.minus

/-- **`M_F ∈ SL(2,ℤ)`, and it holds by construction.** Def 2.2's determinant
    condition is discharged from the type's own field, not proved about it. -/
@[simp] theorem det_eq_one (F : Frame) : F.det = 1 :=
  (contact_iff_delta_one _ _).mp F.contact

/-- **Definition 2.2, the ordering stated for every frame: `C₋ ≺ C₊`.** Read
    off the contact field by `contact_iff_lt_primitiveContact`. -/
theorem minus_lt_plus (F : Frame) : Pres.Lt F.minus F.plus := F.contact.lt

/-- **Definition 2.2's boundaries are Farey-adjacent:** `Δ(C₊, C₋) = ±1`. -/
theorem boundaries_adjacent (F : Frame) : PrimitiveContact F.plus F.minus :=
  contact_primitive F.contact

/-- **Definition 2.2, both directions.** A pair of presentations carries a frame
    exactly when it satisfies the book's hypothesis, `C₋ ≺ C₊` and Farey-adjacent.
    Nothing is lost or added by making contact the field. -/
theorem mk_iff (A B : Pres) :
    (∃ F : Frame, F.plus = A ∧ F.minus = B) ↔ (Pres.Lt B A ∧ PrimitiveContact A B) := by
  rw [← contact_iff_lt_primitiveContact]
  constructor
  · rintro ⟨F, rfl, rfl⟩; exact F.contact
  · intro h; exact ⟨⟨A, B, h⟩, rfl, rfl⟩

/-- **Definition 2.2.** The canonical boundary frame `F_∅ = (1:0, 0:1)`, whose
    matrix is the identity. -/
def empty : Frame := ⟨⟨1, 0, by decide⟩, ⟨0, 1, by decide⟩, by decide⟩

@[simp] theorem empty_matrix : empty.matrix = ((1, 0), (0, 1)) := rfl

/-- At the canonical frame the ordering reads `0:1 ≺ 1:0`. -/
theorem empty_minus_lt_plus : Pres.Lt empty.minus empty.plus := by decide

/-! ### Definition 2.4 — the relational triad and its two child frames -/

/-- The generated middle relation of the triad. The book writes it `C₋ ⊕ C₊`;
    the mediant adds componentwise, so taking the parents in the other order is
    the same presentation and this is the form the contact lemmas are stated in. -/
def mid (F : Frame) : Pres := Pres.mediant F.plus F.minus

/-- **Definition 2.4.** `𝔗(C₊, C₋) = (C₋, C₋ ⊕ C₊, C₊)`. Two inherited
    directions sharing one generated middle relation. -/
def triad (F : Frame) : Pres × Pres × Pres := (F.minus, F.mid, F.plus)

/-- **Definition 2.4.** `F_L = (C₋ ⊕ C₊, C₋)`: the mediant becomes the new `C₊`.
    Its contact is Proposition 2.1's right half. -/
def stepL (F : Frame) : Frame :=
  ⟨F.mid, F.minus, contact_mediant_left F.contact⟩

/-- **Definition 2.4.** `F_R = (C₊, C₋ ⊕ C₊)`: the mediant becomes the new `C₋`.
    Its contact is Proposition 2.1's left half. -/
def stepR (F : Frame) : Frame :=
  ⟨F.plus, F.mid, contact_mediant_right F.contact⟩

/-- The four entries of `F_L`'s matrix, by unfolding (`rfl`): the mediant sits
    in the FIRST column. The matrix `L` does not appear here. The Definition 3.1
    conformance `M_F L = M_{F_L}` is `Frame.toMat2_stepL` in `Walk.lean`
    (audit E1-A6). -/
@[simp] theorem stepL_matrix (F : Frame) :
    (stepL F).matrix =
      ((((F.plus.p + F.minus.p : ℕ) : ℤ), ((F.plus.q + F.minus.q : ℕ) : ℤ)),
       ((F.minus.p : ℤ), (F.minus.q : ℤ))) := rfl

/-- The four entries of `F_R`'s matrix, by unfolding (`rfl`): the mediant sits
    in the second column. The matrix `R` does not appear here. The Definition 3.1
    conformance `M_F R = M_{F_R}` is `Frame.toMat2_stepR` in `Walk.lean`
    (audit E1-A6). -/
@[simp] theorem stepR_matrix (F : Frame) :
    (stepR F).matrix =
      (((F.plus.p : ℤ), (F.plus.q : ℤ)),
       (((F.plus.p + F.minus.p : ℕ) : ℤ), ((F.plus.q + F.minus.q : ℕ) : ℤ))) := rfl

/-- **Definition 2.5 — side selection.** A directed continuation carries one
    child, never both. The triad holds both; a walk letter chooses. -/
def select (F : Frame) (right : Bool) : Frame := if right then stepR F else stepL F

/-- A walk: a word of side selections, folded from the left, oldest first. -/
def walk (F : Frame) (w : List Bool) : Frame := w.foldl select F

/-- **Contact is a walk invariant.** This was the load-bearing theorem of the old
    file, proved by induction over the word. With the pair primitive it is a
    corollary of the type: every `Frame` is in contact, and `walk` returns a
    `Frame`. The induction is gone because there is nothing left to induct on. -/
theorem det_walk (F : Frame) (w : List Bool) : (walk F w).det = 1 :=
  det_eq_one _

/-- Every relation reached by a walk is primitive: on-tree, `reduce` never fires. -/
theorem walk_mid_primitive (F : Frame) (w : List Bool) : Primitive (walk F w).mid :=
  mediant_primitive (walk F w).contact

/-- Every relation reached by a walk is interior — not a boundary anchor, even
    though the two frame components it is built from may themselves be one. -/
theorem walk_mid_pos (F : Frame) (w : List Bool) :
    0 < (walk F w).mid.p ∧ 0 < (walk F w).mid.q :=
  mediant_pos (walk F w).contact

/-- **A walk one step longer is one more `select` on the walk so far.** Plain
    unfolding of `foldl` over `++`, kept as a named lemma because D-06's
    Fibonacci-mediant theorem below needs to peel one letter at a time from a
    word built by appending, not by consing. -/
theorem walk_append (F : Frame) (w : List Bool) (x : Bool) :
    walk F (w ++ [x]) = select (walk F w) x := by
  simp [walk, List.foldl_append]

/-! ### The first levels, checked by the compiler

    `F_∅ = (1:0, 0:1)` has middle `1:1`, and its two children are the two halves
    of the Stern-Brocot tree. These reduce, so they are computed rather than
    asserted — which is the standard set for the whole series. -/

example : empty.mid = ⟨1, 1, by decide⟩ := rfl
example : (stepL empty).matrix = ((1, 1), (0, 1)) := rfl
example : (stepR empty).matrix = ((1, 0), (1, 1)) := rfl

/-- Three `R` steps hold `C₊ = 1:0` and push `C₋` up through `1:1, 2:1, 3:1`.
    Three `L` steps hold `C₋ = 0:1` and push `C₊` down through `1:1, 1:2, 1:3`.
    The walk is the address; nothing is being approximated. -/
example : (walk empty [true, true, true]).minus = ⟨3, 1, by decide⟩ := rfl
example : (walk empty [true, true, true]).plus = ⟨1, 0, by decide⟩ := rfl
example : (walk empty [false, false, false]).plus = ⟨1, 3, by decide⟩ := rfl
example : (walk empty [false, false, false]).mid = ⟨1, 4, by decide⟩ := rfl

/-- `RLL` lands on the frame `(3:2, 1:1)` with middle `4:3`; `LLR` lands on
    `(1:2, 1:3)` with middle `2:5`. One `R` and two `L`s either way, and the two
    relations have nothing in common. The word is ordered, and the order is the
    data: a frame is its ancestry, not a value that ancestry happened to reach. -/
example : (walk empty [true, false, false]).mid = ⟨4, 3, by decide⟩ := rfl
example : (walk empty [false, false, true]).mid = ⟨2, 5, by decide⟩ := rfl

/-- `L` and `R` are genuinely different continuations, which is Def 2.5's point:
    one reception cannot contain both sides at once. -/
example : stepL empty ≠ stepR empty := by decide

/-! ### Definition 5.7's continued-fraction clause — the walk that never closes

    D-06 (`research/lean-support/DIVERGENCE.md`). Def 5.7 names `φ = [1;1,1,...]`
    in the continued-fraction completion. The substrate object under that
    sentence is not a limit: it is the word `RLRLRL...`, which never closes,
    walked from `F_∅` by Def 2.4's own mediant construction, and its successive
    middles are consecutive Fibonacci ratios. Nothing here is converged to;
    every step is an exact presentation, forever. -/

/-- The word `R,L,R,L,...`, built by appending one more alternating letter at a
    time so induction can peel it from the end via `walk_append`. Element `n`
    (0-indexed) is `R` on even `n`, `L` on odd `n`, so the walk opens `R` and
    then strictly alternates. -/
def altWord : ℕ → List Bool
  | 0 => []
  | n + 1 => altWord n ++ [n % 2 == 0]

@[simp] theorem altWord_zero : altWord 0 = [] := rfl

theorem altWord_succ (n : ℕ) : altWord (n + 1) = altWord n ++ [n % 2 == 0] := rfl

/-- One more letter of `altWord` is one more `select`, by `walk_append`. -/
theorem walk_altWord_succ (n : ℕ) :
    walk empty (altWord (n + 1)) = select (walk empty (altWord n)) (n % 2 == 0) := by
  rw [altWord_succ, walk_append]

/-- **The recurrence.** Two more letters of `altWord` always land the middle on
    the mediant of the two middles before it — regardless of whether those two
    letters were `R,L` or `L,R`, because whichever of `plus`/`minus` is held
    fixed by the first of the pair is exactly the middle reached one step
    earlier. This is Def 2.4's construction read twice in a row; no case of it
    is a limit. -/
theorem mid_altWord_recurrence (n : ℕ) :
    mid (walk empty (altWord (n + 2)))
      = Pres.mediant (mid (walk empty (altWord (n + 1)))) (mid (walk empty (altWord n))) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · -- n even: letter n is R, letter (n+1) is L
    -- (`rw; decide` rather than `simp`, which pulls `Classical.choice` in
    -- through its `Bool`-equation simp set on this particular goal shape.)
    have he0 : (n % 2 == 0) = true := by rw [h]; decide
    have he1 : ((n + 1) % 2 == 0) = false := by
      have h1 : (n + 1) % 2 = 1 := by omega
      rw [h1]; decide
    have e1 : walk empty (altWord (n + 1)) = select (walk empty (altWord n)) true := by
      rw [walk_altWord_succ, he0]
    have e2 : walk empty (altWord (n + 2)) = select (walk empty (altWord (n + 1))) false := by
      rw [walk_altWord_succ, he1]
    rw [e2, e1]
    -- `select _ true = stepR _`, `select _ false = stepL _`, both `rfl`, and
    -- `stepL (stepR F)` reaches its middle by exactly the mediant on the right
    -- of the goal, with no swap needed — this is the `R,L` order.
    rfl
  · -- n odd: letter n is L, letter (n+1) is R
    have he0 : (n % 2 == 0) = false := by rw [h]; decide
    have he1 : ((n + 1) % 2 == 0) = true := by
      have h1 : (n + 1) % 2 = 0 := by omega
      rw [h1]; decide
    have e1 : walk empty (altWord (n + 1)) = select (walk empty (altWord n)) false := by
      rw [walk_altWord_succ, he0]
    have e2 : walk empty (altWord (n + 2)) = select (walk empty (altWord (n + 1))) true := by
      rw [walk_altWord_succ, he1]
    rw [e2, e1]
    -- `stepR (stepL F)` reaches the same middle with the two arguments
    -- reversed — the `L,R` order — so this direction genuinely needs mediant's
    -- commutativity, not just unfolding.
    apply Pres.ext' <;> simp [select, mid, stepR, stepL, mediant_p, mediant_q] <;> ring

/-- **The closed form.** The walk's middle after `n` letters of `RLRLRL...` is
    the presentation of consecutive Fibonacci numbers, `F(n+2) : F(n+1)`. Stated
    componentwise, since building the `Pres` back up from two `Nat`s would need
    a fresh `ne_zero` proof this equation does not otherwise need. -/
theorem mid_altWord_fib (n : ℕ) :
    (mid (walk empty (altWord n))).p = Nat.fib (n + 2) ∧
    (mid (walk empty (altWord n))).q = Nat.fib (n + 1) ∧
    (mid (walk empty (altWord (n + 1)))).p = Nat.fib (n + 3) ∧
    (mid (walk empty (altWord (n + 1)))).q = Nat.fib (n + 2) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  | succ k ih =>
    have hp1 : (mid (walk empty (altWord (k + 1)))).p = Nat.fib (k + 3) := ih.2.2.1
    have hq1 : (mid (walk empty (altWord (k + 1)))).q = Nat.fib (k + 2) := ih.2.2.2
    have hp0 : (mid (walk empty (altWord k))).p = Nat.fib (k + 2) := ih.1
    have hq0 : (mid (walk empty (altWord k))).q = Nat.fib (k + 1) := ih.2.1
    have hrec := mid_altWord_recurrence k
    have expandP : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) :=
      Nat.fib_add_two (n := k + 2)
    have expandQ : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) :=
      Nat.fib_add_two (n := k + 1)
    refine ⟨hp1, hq1, ?_, ?_⟩
    · have hstep : (mid (walk empty (altWord (k + 2)))).p
          = (mid (walk empty (altWord (k + 1)))).p + (mid (walk empty (altWord k))).p :=
        congrArg Pres.p hrec
      change (mid (walk empty (altWord (k + 2)))).p = Nat.fib (k + 4)
      rw [hstep, hp1, hp0, expandP]; ring
    · have hstep : (mid (walk empty (altWord (k + 2)))).q
          = (mid (walk empty (altWord (k + 1)))).q + (mid (walk empty (altWord k))).q :=
        congrArg Pres.q hrec
      change (mid (walk empty (altWord (k + 2)))).q = Nat.fib (k + 3)
      rw [hstep, hq1, hq0, expandQ]; ring

/-- **Non-vacuity, and the sanity check on the direction of the alternation.**
    `RLRL` (four letters) lands the middle on `8:5`, the sixth and fifth
    Fibonacci numbers, exactly as `mid_altWord_fib` predicts, and never on a
    decimal approximation of `φ ≈ 1.618`. -/
example : mid (walk empty (altWord 4)) = ⟨8, 5, by decide⟩ := by
  have h := mid_altWord_fib 4
  exact Pres.ext' (h.1.trans (by decide)) (h.2.1.trans (by decide))

end Frame
end RatioSpace
