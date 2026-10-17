/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S02.Temporal
/-!
  Elements II §3 — Observer localization and common-prefix covariance.

  Definition 3.1 through Proposition 3.6. The section says that an observer can
  read an occurrence as a word in its own chart, and that a history shared by the
  whole system is invisible to that reading.

  Four things here are sharper than the prose, and each is noted at its theorem:

    * **Def 3.1 uses the decoder of Elements I, Standard Result 3.1.** The book
      writes `a_x = dec₊(Q_{O,x})`; the uniqueness half of that result is
      `G_inj`, and the decoder is built in
      `Walk.lean` — total, computable, fuel-driven — and with it **membership in

      `ℳ₊` is decidable**, so `Dom₊(O)` is a test that runs rather than a
      set-builder that is asserted.

    * **The distinction Def 3.1 draws in prose has an exact form.** The book warns
      that `λ_O(x) = r(a_x)` is not the world-frame `r_{F_O}(a_x)`, "the latter
      retains the observer frame as world data". What the latter *is*, exactly,
      is the occurrence's own world address: `r_{F_O}(a_x) = r(w_x)`. Evaluating
      the local word in the world chart undoes the localization completely, and
      returns the thing the observer was supposed to have factored out.

    * **Theorem 3.4's "consequently" is functional dependence, not three further
      arguments.** The book proves `Q_{Z_uO,Z_ux} = Q_{O,x}` and then says the
      admission, the decoded word and the local relation follow. In Lean each of
      those is literally a function of `Q`, so each consequence is one `rw`. The
      content of the section is one equation; the covariance of everything
      downstream is free, and would stay free for any future reading built on
      `Q`.

    * **Prop 3.6's "can change positive admission" has a witness, and the witness
      is the same letter on both sides.** Observer and occurrence at `ε` and `L`
      have `Q = L ∈ ℳ₊`. Advance both by `R` — the same generator, not opposite
      ones — and the encounter matrix leaves `ℳ₊` outright. So the failure is not
      about divergent motion; a common *left* prefix cancels and a common *right*
      step does not, and the asymmetry is the whole distinction between Def 3.3
      and Def 3.2 form 3.

  Everything is computable. No `sorry`, no `axiom`.
-/

namespace RatioSpace
namespace Two

open Mat2 Word Frame Pres

/-! ## Definition 3.1 — Positive observer domain

    `Q_{O,x} = M_O⁻¹M_x`, and the observer admits `x` when that matrix is a
    positive word. `dec` from `Walk.lean` decides it and returns the word. -/

/-- **Definition 3.1.** The encounter matrix of an observer-occurrence pair.
    This is Elements I Def 3.2 form 3 with both arguments named, and Elements II
    Import 1.5 is the statement that a shared prefix cancels out of it. -/
def Q (MO Mx : Mat2) : Mat2 := inv2 MO * Mx

@[simp] theorem Q_def (MO Mx : Mat2) : Q MO Mx = inv2 MO * Mx := rfl

/-- The boundary observer reads the world as it is. -/
@[simp] theorem Q_one (M : Mat2) : Q 1 M = M := by
  rw [Q, show inv2 (1 : Mat2) = 1 from by decide, Mat2.one_mul']

/-- **Definition 3.1.** `Dom₊(O)`, as a predicate on the occurrence's matrix. -/
def DomPlus (MO Mx : Mat2) : Prop := Q MO Mx ∈ Mplus

/-- **The domain is decidable**, because the decoder is total and computable.
    The book's set-builder does not say this and does not need to; the Lean
    cannot state `Dom₊` as a runnable test without it. -/
instance (MO Mx : Mat2) : Decidable (DomPlus MO Mx) :=
  decidable_of_iff _ (mem_Mplus_iff_dec (Q MO Mx)).symm

/-- **Definition 3.1.** The observer-local word `a_x = dec₊(Q_{O,x})`, defined
    exactly when the observer admits `x`. -/
def localWord (MO Mx : Mat2) : Option Word := dec (Q MO Mx)

/-- **Definition 3.1.** The observer-local addressed relation
    `λ_O(x) = r(a_x)`, evaluated in the normalized chart whose identity frame
    sits at `O`. `Frame.r` walks from `Frame.empty`, which *is* that chart. -/
def lambda (MO Mx : Mat2) : Option Pres := (localWord MO Mx).map r

theorem localWord_eq (MO Mx : Mat2) {a : Word} (h : Q MO Mx = G a) :
    localWord MO Mx = some a := by
  rw [localWord, h, dec_G]

theorem lambda_eq (MO Mx : Mat2) {a : Word} (h : Q MO Mx = G a) :
    lambda MO Mx = some (r a) := by
  rw [lambda, localWord_eq MO Mx h]; rfl

/-- An observer at `ε` reads every positive occurrence as itself: the canonical
    chart is the world chart only for the boundary observer. -/
@[simp] theorem localWord_one (w : Word) : localWord 1 (G w) = some w := by
  rw [localWord, Q_one, dec_G]

/-! ### The local chart is not the world chart

    Def 3.1's warning, made exact. -/

/-- Walking a prefix and then continuing is walking the concatenation. -/
theorem addressed_walk (F : Frame) (u v : Word) :
    addressed (walk F u) v = addressed F (u ++ v) := by
  simp [addressed, walk, List.foldl_append]

/-- **What the world-frame reading actually returns.** `r_{F_O}(a_x)` is not
    merely "the local word with observer data retained": it is the occurrence's
    own world address `r(w_x)`. Evaluating the local word in the world chart
    undoes the localization exactly. -/
theorem world_chart_returns_world_address (wO a : Word) :
    addressed (walk empty wO) a = r (wO ++ a) :=
  addressed_walk empty wO a

/-- And the two readings differ, so the warning is not decoration. Observer at
    `R`, occurrence at `RL`: the local relation is `1:2` and the world-frame
    evaluation of the same local word is `3:2`, which is the occurrence's own
    address. -/
theorem lambda_ne_world_chart :
    (r [false]).p ≠ (addressed (walk empty [true]) [false]).p := by decide

/-! ## Proposition 3.2 — Positive localization is exact suffix recovery -/

/-- **Proposition 3.2, matrix half.** If the encounter matrix is `G a`, the
    occurrence's matrix is the observer's followed by `a`. Needs `det M_O = 1`,
    which every frame and every positive word already satisfies. -/
theorem prop_3_2_matrix {MO Mx : Mat2} (hO : MO.det = 1) {a : Word}
    (h : Q MO Mx = G a) : Mx = MO * G a := by
  rw [← h, Q, ← Mat2.mul_assoc', mul_inv2_of_det MO hO, Mat2.one_mul']

/-- **Proposition 3.2, word half.** For positive word records the recovery is
    literal concatenation: `w_x = w_O a_x`. This is the matrix half followed by
    positive freeness, and freeness is the only place uniqueness enters. -/
theorem prop_3_2_word {wO wx a : Word} (h : Q (G wO) (G wx) = G a) :
    wx = wO ++ a := by
  have hM : G wx = G wO * G a := prop_3_2_matrix (det_G wO) h
  exact G_inj (hM.trans (G_append wO a).symm)

/-- The converse, which the book uses silently: a suffix *is* what the observer
    reads. Together with 3.2 this makes `a ↦ w_O a` a bijection from words onto
    the observer's positive domain. -/
theorem encounter_of_suffix (wO a : Word) : Q (G wO) (G (wO ++ a)) = G a :=
  encounter_shared_prefix wO a

theorem localWord_of_suffix (wO a : Word) : localWord (G wO) (G (wO ++ a)) = some a :=
  localWord_eq _ _ (encounter_of_suffix wO a)

/-! ## Definition 3.3 — Common-prefix transport -/

/-- **Definition 3.3.** `Z_u(M) = G(u)M`, left multiplication by a positive
    prefix. This is Elements I Def 3.2 form 2, `reframe`, with a word in place of
    a single generator; it is deliberately *not* `forward`. -/
def Z (u : Word) (M : Mat2) : Mat2 := G u * M

@[simp] theorem Z_def (u : Word) (M : Mat2) : Z u M = G u * M := rfl

/-- **Definition 3.3, the word half.** `Z_u` "also prefixes the corresponding
    world words", and the two halves agree. -/
@[simp] theorem Z_G (u w : Word) : Z u (G w) = G (u ++ w) := (G_append u w).symm

/-- `Z` is an action of the free monoid: prefixing by `u` then by `v` is
    prefixing by `vu`, in that order, and the empty prefix does nothing. -/
@[simp] theorem Z_nil (M : Mat2) : Z [] M = M := by simp [Z]

theorem Z_Z (u v : Word) (M : Mat2) : Z u (Z v M) = Z (u ++ v) M := by
  simp [Z, G_append, Mat2.mul_assoc']

/-! ## Theorem 3.4 — Common-prefix localization covariance -/

/-- **Theorem 3.4.** A history shared by the observer and the occurrence is
    invisible to the encounter matrix. One line, and it is Import 1.5. -/
theorem thm_3_4 (u : Word) (MO Mx : Mat2) : Q (Z u MO) (Z u Mx) = Q MO Mx :=
  shared_prefix_cancel u MO Mx

/-- **Theorem 3.4's first consequence**, `a_{Z_ux} = a_x`. In the book this is a
    separate sentence; here it is one rewrite, because the decoded word is a
    function of `Q` and of nothing else. -/
@[simp] theorem thm_3_4_localWord (u : Word) (MO Mx : Mat2) :
    localWord (Z u MO) (Z u Mx) = localWord MO Mx := by
  rw [localWord, localWord, thm_3_4]

/-- **Theorem 3.4's second consequence**, `λ_{Z_uO}(Z_ux) = λ_O(x)`. -/
@[simp] theorem thm_3_4_lambda (u : Word) (MO Mx : Mat2) :
    lambda (Z u MO) (Z u Mx) = lambda MO Mx := by
  rw [lambda, lambda, thm_3_4_localWord]

/-- **Theorem 3.4's third consequence**, invariance of positive admission. -/
theorem thm_3_4_domain (u : Word) (MO Mx : Mat2) :
    DomPlus (Z u MO) (Z u Mx) ↔ DomPlus MO Mx := by
  rw [DomPlus, DomPlus, thm_3_4]

/-- **The general form, which is what the section actually establishes.** Every
    reading that factors through the encounter matrix is common-prefix
    covariant, for free and in advance. The three consequences above are this
    theorem at three choices of `f`; any later reading of `Q` inherits it
    without a new argument. -/
theorem prefix_covariance {α : Type} (f : Mat2 → α) (u : Word) (MO Mx : Mat2) :
    f (Q (Z u MO) (Z u Mx)) = f (Q MO Mx) := by rw [thm_3_4]

/-! ## Proposition 3.5 — Prefix transport commutes with forward generation -/

/-- **Proposition 3.5.** `Z_u(M_xg) = Z_u(M_x)g`. Associativity, and the typed
    roles are what the statement is for: `G(u)` reframes on the left, `g` extends
    the history on the right, and the two never compete for the same slot. -/
theorem prop_3_5 (u : Word) (Mx : Mat2) (b : Bool) :
    Z u (forward Mx (gen b)) = forward (Z u Mx) (gen b) :=
  (Mat2.mul_assoc' (G u) Mx (gen b)).symm

/-- The same statement on words, where the two roles are visibly different
    operations on a list rather than the same multiplication twice. -/
theorem prop_3_5_word (u w : Word) (b : Bool) :
    Z u (G (w ++ [b])) = forward (Z u (G w)) (gen b) := by
  simp [forward, G_append, Mat2.mul_assoc']

/-- Prop 3.5 says the two roles *commute*; it does not say they are the same
    operation, and Elements I's `forward_ne_reframe` is the witness that they are
    not. Recorded here because the proposition is easy to read as the stronger
    claim. -/
theorem prop_3_5_roles_distinct : forward L R ≠ reframe R L := forward_ne_reframe

/-! ## Proposition 3.6 — Bilateral transport remains distinct -/

/-- **Proposition 3.6.** Advance of the observer by `g_O` and of the occurrence
    by `g_x`, two separately supplied steps with neither fixed by the other,
    conjugates the encounter matrix: `Q⁺ = g_O⁻¹Qg_x`. That is Elements I Def 3.2
    form 3, `transport`, and it holds with no determinant hypothesis at all. Both
    steps act on the one encounter matrix, and they may be chosen equal:
    `prop_3_6_changes_admission` below is that case. -/
theorem prop_3_6 (gO gx MO Mx : Mat2) :
    Q (forward MO gO) (forward Mx gx) = transport gO gx (Q MO Mx) := by
  simp [Q, forward, transport, inv2_mul, Mat2.mul_assoc']

/-- **The constructive application, and it is a failure of admission.** The
    observer at `ε` and the occurrence at `L` have `Q = L ∈ ℳ₊`. Advance both by
    the *same* generator `R` and the encounter matrix acquires a negative entry,
    so it is not a positive word and the occurrence has left `Dom₊(O)`.

    A common left prefix cancels; a common right step does not. The asymmetry is
    exactly Def 3.3 against Def 3.2 form 3, and it is why Theorem 3.4 has to name
    the prefix. -/
theorem prop_3_6_changes_admission :
    DomPlus 1 (G [false]) ∧ ¬ DomPlus (forward 1 R) (forward (G [false]) R) := by
  constructor
  · exact ⟨[false], by rw [Q_one]⟩
  · decide

/-- The two transports side by side: shared prefix invariant, bilateral advance
    not. The book's closing sentence, as one statement. -/
theorem covariance_needs_the_prefix :
    (∀ (u : Word) (MO Mx : Mat2), Q (Z u MO) (Z u Mx) = Q MO Mx) ∧
      (∃ MO Mx g : Mat2, Q (forward MO g) (forward Mx g) ≠ Q MO Mx) :=
  ⟨thm_3_4, ⟨1, G [false], R, by decide⟩⟩

end Two
end RatioSpace
