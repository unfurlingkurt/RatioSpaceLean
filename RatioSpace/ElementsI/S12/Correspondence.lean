/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S12.Encoding
import RatioSpace.ElementsI.S10.Crystal
/-!
  Elements I §12 — Definition 12.3, the correspondence obligation.

  **The book's demand, exactly (Elements I, Definition 12.3).** *"To prove that
  a projected numerical update F_num represents the substrate update U, one
  must establish a commuting relation such as E_O ∘ U_Q = F_num ∘ E_O on every
  state in the domain of U_Q, and say what F_num does off that domain, or state
  and prove the exact error or limiting relation that replaces equality."*
  Similarity of vocabulary, for example calling both operations "diffusion",
  "collapse" or "coherence", is not a correspondence proof.

  Two clauses. This file formalises the first: the exact commuting square,
  typed as a structure whose fields **are** the proof. The second clause —
  an error bound or a limiting relation standing in for equality — needs a
  notion of closeness that is not available here under the standing
  constraints (no `Real`), the same reason Def 12.2's field-equation example
  went unformalised. Nothing below claims to cover it.

  **The update is partial.** `𝒰_𝒬` is defined only where the
  forward map is (Def 10.6), and Def 10.4 names two ways it is not. The Lean's
  own recursion `cycle` returns `SubstrateState ⊕ Outcome`. So the square the
  book names is `PartialCorrespondence` below: the square on every state where
  the update returns a state, and a declared statement `Off` of what `F_num`
  does where it returns an outcome instead. `Correspondence`, over a total
  `U`, is the case where the update never fails
  (`partialCorrespondence_total_iff`), and totalising the update
  by "no answer, no change" is exactly the partial square with `Off := StaysPut`
  (`correspondence_stayPut_iff`).

  **Why a structure and not a `theorem`.** The partial `U` of
  `PartialCorrespondence` stands for `𝒰_𝒬`, Def 10.6's complete update
  (`Correspondence`'s total `U` is the case where it never fails), read in Elements I as
  `cycle K B` over two interfaces with only trivial and convention witnesses
  (`identity`, `clear`), none the Elements II update; its literal law is Elements II's
    (`Crystal.lean`'s
  header for `𝔎_𝒞`, the `Assimilation` docstring for `ℬ_𝒬`). So Def 12.3 cannot be a
  theorem about a specific `U`; it is the obligation any *claimed* pairing of
  `U`, an encoding `E`, and a numerical update `F_num` must discharge before
  the claim is entitled to say "represents". `Correspondence` is unconstructible
  for a given triple until someone supplies `commutes` — there is no route to a
  term of this type that is not itself a completed proof of the square.
-/

namespace RatioSpace
namespace Layer

/-! ## Definition 12.3 — Correspondence obligation -/

/-- **Definition 12.3, total case.** `E_O ∘ U_Q = F_num ∘ E_O`,
    read pointwise: encoding the substrate update agrees with numerically
    updating the encoding, for every state. The book's update is partial; the
    book's definition is `PartialCorrespondence` below, and this is its case
    with nothing outside (`partialCorrespondence_total_iff`). The obligation-as-type pattern
      used for `ConstantReading` in §6 —
    `E`, `U` and `F_num` are the terms the claim is about, and `commutes` is the
    claim, typed so it cannot be asserted without being proved. -/
structure Correspondence {F : Type} (E : Encoding F)
    (U : SubstrateState → SubstrateState) (F_num : F → F) where
  /-- the commuting square, for every substrate state -/
  commutes : ∀ S : SubstrateState, E.map (U S) = F_num (E.map S)

/-! ## The negative witness — sharing a name is not sharing a square -/

/-- One tick of substrate advance, extending the retained word by a step.
    Stands for `𝒰_𝒬` exactly as abstractly as Def 10.6 leaves it: nothing here
    claims to be the real law, only something that changes the state the way
    an advance must — the word grows. -/
def stepAdvance (S : SubstrateState) : SubstrateState :=
  { S with word := S.word ++ [true] }

/-- The numerical "advance" that shares the name and does nothing. This is the
    vocabulary trap made into an object: read off the vocabulary alone, "advance"
    paired with "advance" looks like a correspondence. -/
def idAdvance : ClosureState → ClosureState := id

/-- **The square fails, witnessed at the empty state.** `stepAdvance` changes
    the closure record; `idAdvance` by definition does not. Both are exact,
    `decide`-checked, no limiting relation in sight. -/
theorem stepAdvance_idAdvance_disagree_at_empty :
    closureEncoding.reading (stepAdvance ⟨Frame.empty, [], [], []⟩)
      ≠ idAdvance (closureEncoding.reading ⟨Frame.empty, [], [], []⟩) := by decide

/-- **So no `Correspondence` term connects them.** Not because the search for
    one failed, but because the one field such a term would need to supply —
    `commutes`, applied at the empty state — is exactly the previous theorem's
    negation. Sharing a name (both "advance") supplied no such field. -/
theorem no_correspondence_stepAdvance_idAdvance :
    ¬ Correspondence closureEncoding stepAdvance idAdvance := by
  intro H
  exact stepAdvance_idAdvance_disagree_at_empty
    (H.commutes ⟨Frame.empty, [], [], []⟩)

/-- **The type is not vacuous**, so the obstruction above is about this pair and
    not about the structure. The identity substrate update and the identity
    numerical update commute with any encoding, trivially — the honest case
    where "does nothing" is correctly reported as "does nothing" at both
    layers. -/
theorem trivialCorrespondence {F : Type} (E : Encoding F) :
    Correspondence E id id where
  commutes := fun _ => rfl

/-! ## Definition 12.3 over the update the book names: a partial update -/

/-- **Definition 12.3.** The square on every state where the
    update `U` is defined, and a declared statement of what `F_num` does where
    it is not. `U S = Sum.inr o` is Def 10.4's failure `o`; `Off x y o` is the
    claimant's statement about the encoded state `x = E(S)`, the numerical
    update's value `y = F_num(x)` there, and the failure. Both fields are the
    proof; the type has no other constructor.

    The claim is only as strong as the `Off` it names, and `Off` sits in the
    type where anyone can read it: `Off := fun _ _ _ => True` discharges
    `outside` for free and says nothing about `F_num`. `Off` sees the encoding,
    not the state, because the numerical side sees only the encoding; an
    off-domain statement about substrate data the encoding forgets cannot be
    stated here. -/
structure PartialCorrespondence {F : Type} (E : Encoding F)
    (U : SubstrateState → SubstrateState ⊕ Outcome) (F_num : F → F)
    (Off : F → F → Outcome → Prop) where
  /-- the commuting square, on every state where `U` returns a state -/
  commutes : ∀ S T : SubstrateState, U S = Sum.inl T → E.map T = F_num (E.map S)
  /-- what `F_num` does where `U` returns an outcome instead -/
  outside : ∀ (S : SubstrateState) (o : Outcome), U S = Sum.inr o →
    Off (E.map S) (F_num (E.map S)) o

/-- "No answer, no change" on the numerical side: where the substrate update
    fails, `F_num` leaves the encoded state as it was. `cycle`'s docstring
    reads an unresolved cycle this way on the substrate side. -/
def StaysPut {F : Type} (x y : F) (_ : Outcome) : Prop := y = x

/-- A total update, seen as a partial one that never fails. -/
def totalUpdate (U : SubstrateState → SubstrateState) :
    SubstrateState → SubstrateState ⊕ Outcome := fun S => Sum.inl (U S)

/-- **A total update is the case with nothing outside.** For a total `U` the
    partial square, with any off-domain statement at all, is `Correspondence`. -/
theorem partialCorrespondence_total_iff {F : Type} (E : Encoding F)
    (U : SubstrateState → SubstrateState) (F_num : F → F)
    (Off : F → F → Outcome → Prop) :
    Nonempty (PartialCorrespondence E (totalUpdate U) F_num Off) ↔
      Nonempty (Correspondence E U F_num) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨⟨fun S => H.commutes S (U S) rfl⟩⟩
  · rintro ⟨H⟩
    refine ⟨⟨fun S T h => ?_, fun S o h => ?_⟩⟩
    · cases h
      exact H.commutes S
    · cases h

/-- The partial update made total by "no answer, no change": where `U` fails,
    the state stays. -/
def stayPut (U : SubstrateState → SubstrateState ⊕ Outcome) :
    SubstrateState → SubstrateState :=
  fun S => Sum.elim id (fun _ => S) (U S)

/-- **The total square on the totalised update is one choice of `Off`.**
    `Correspondence` applied to "no answer, no change" holds exactly when the
    partial square holds and `F_num` also stays put wherever `U` fails. Other
    totalisations carry other `Off`s (`correspondence_fallback_iff`); an `Off`
    that is not of such a form has no total statement. -/
theorem correspondence_stayPut_iff {F : Type} (E : Encoding F)
    (U : SubstrateState → SubstrateState ⊕ Outcome) (F_num : F → F) :
    Nonempty (Correspondence E (stayPut U) F_num) ↔
      Nonempty (PartialCorrespondence E U F_num StaysPut) := by
  constructor
  · rintro ⟨H⟩
    refine ⟨⟨fun S T h => ?_, fun S o h => ?_⟩⟩
    · have := H.commutes S
      simp only [stayPut, h, Sum.elim_inl, id] at this
      exact this
    · have := H.commutes S
      simp only [stayPut, h, Sum.elim_inr] at this
      exact this.symm
  · rintro ⟨H⟩
    refine ⟨⟨fun S => ?_⟩⟩
    rcases h : U S with T | o
    · simp only [stayPut, h, Sum.elim_inl, id]
      exact H.commutes S T h
    · simp only [stayPut, h, Sum.elim_inr]
      exact (H.outside S o h).symm

/-- The partial update made total by a fixed fallback state `S₀`. -/
def fallback (S₀ : SubstrateState) (U : SubstrateState → SubstrateState ⊕ Outcome) :
    SubstrateState → SubstrateState :=
  fun S => Sum.elim id (fun _ => S₀) (U S)

/-- **A second totalisation, a second `Off`.** The total square on the update
    that falls back to `S₀` is the partial square with "`F_num` sends every
    failing state to the encoding of `S₀`". -/
theorem correspondence_fallback_iff {F : Type} (E : Encoding F) (S₀ : SubstrateState)
    (U : SubstrateState → SubstrateState ⊕ Outcome) (F_num : F → F) :
    Nonempty (Correspondence E (fallback S₀ U) F_num) ↔
      Nonempty (PartialCorrespondence E U F_num (fun _ y _ => y = E.map S₀)) := by
  constructor
  · rintro ⟨H⟩
    refine ⟨⟨fun S T h => ?_, fun S o h => ?_⟩⟩
    · have := H.commutes S
      simp only [fallback, h, Sum.elim_inl, id] at this
      exact this
    · have := H.commutes S
      simp only [fallback, h, Sum.elim_inr] at this
      exact this.symm
  · rintro ⟨H⟩
    refine ⟨⟨fun S => ?_⟩⟩
    rcases h : U S with T | o
    · simp only [fallback, h, Sum.elim_inl, id]
      exact H.commutes S T h
    · simp only [fallback, h, Sum.elim_inr]
      exact (H.outside S o h).symm

end Layer

/-! ## Where `cycle` is defined -/

/-- **`cycle` returns a state exactly when the crystallization resolves.** -/
theorem cycle_defined_iff (K : Crystallization) (B : Assimilation)
    (S : SubstrateState) (X : Ensemble) :
    (∃ T, cycle K B S X = Sum.inl T) ↔ ∃ A, K.cryst X = Outcome.resolved A := by
  unfold cycle
  constructor
  · rintro ⟨T, hT⟩
    split at hT
    · exact ⟨_, by assumption⟩
    · cases hT
  · rintro ⟨A, hA⟩
    rw [hA]
    exact ⟨_, rfl⟩

/-- **And returns the failure, unchanged, when it does not.** -/
theorem cycle_undefined_iff (K : Crystallization) (B : Assimilation)
    (S : SubstrateState) (X : Ensemble) (o : Outcome) :
    cycle K B S X = Sum.inr o ↔ K.cryst X = o ∧ ∀ A, o ≠ Outcome.resolved A := by
  unfold cycle
  constructor
  · intro h
    split at h
    · cases h
    · rename_i o' ho
      cases h
      exact ⟨rfl, fun A hA => ho A hA⟩
  · rintro ⟨h, ho⟩
    subst h
    split
    · rename_i A hA
      exact absurd hA (ho A)
    · rfl

/-- **For one declared question the domain is all states or none.** In the Lean
    the ensemble `X` is an argument of `cycle`, not built from the state, so
    whether the update is defined at `S` does not depend on `S`. For a question
    `Q` the ensemble is `initialEnsemble Q` (Def 10.1), built from
    the question and not from the state. Forming the question from the state
    is Elements II's construction. -/
theorem cycle_domain_ignores_state (K : Crystallization) (B : Assimilation)
    (X : Ensemble) (S S' : SubstrateState) :
    (∃ T, cycle K B S X = Sum.inl T) ↔ (∃ T, cycle K B S' X = Sum.inl T) := by
  rw [cycle_defined_iff, cycle_defined_iff]

end RatioSpace
