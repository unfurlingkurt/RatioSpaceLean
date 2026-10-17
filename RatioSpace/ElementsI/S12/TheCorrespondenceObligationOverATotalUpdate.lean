/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S12.Correspondence
import RatioSpace.ElementsI.S10.ReturnAssimilation
/-!
  Elements I §12, Definition 12.3, the correspondence obligation over a total
  update.

  **Book statement (v0.25, E1-43).** "One must establish a commuting relation
  such as `E_O ∘ 𝒰_𝒬 = F_num ∘ E_O` on every state where `𝒰_𝒬` is defined, and
  say what `F_num` does where it is not, or state and prove the exact error or
  limiting relation that replaces equality."

  **The update is partial.** `Correspondence` takes `U : SubstrateState →
  SubstrateState`. The book's `𝒰_𝒬` is partial (Defs 10.4, 10.6), and the
  Lean's `cycle` returns `SubstrateState ⊕ Outcome`, so the square for the
  update the definition names is stated over a partial update.

  **In `Correspondence.lean`.** `PartialCorrespondence E U F_num Off`
  over `U : SubstrateState → SubstrateState ⊕ Outcome`: the square on every
  state where `U` returns a state, and `Off` stating what `F_num` does where it
  returns a failure. `partialCorrespondence_total_iff`: for a total update this
  is `Correspondence`. `correspondence_stayPut_iff`: the total
  square on the update made total by "no answer, no change" is the partial
  square with `Off := StaysPut`, and `correspondence_fallback_iff`: falling
  back to a fixed state carries its own `Off`. `cycle_defined_iff`, `cycle_undefined_iff`:
  where `cycle` is defined. `cycle_domain_ignores_state`: for one declared
  question the domain is all states or none, since the Lean's `cycle` takes the
  ensemble as an argument.

  **Added here.** The square stated for `cycle` itself, at a resolving and at
  a failing question. `update K B Q` runs `cycle` from Def 10.1's initial
  ensemble `initialEnsemble Q`, so each witness is at a `Question` and not at
  a bare ensemble.
  * `g123_square_on_resolving_question`: identity crystallization, the append
    assimilation, the question `resolving` (root frame, depth 1, active family
    `[⟨∅, L⟩]`, no predicates), whose initial ensemble is one record
    (`g123_resolving_ensemble`): `cycle` is defined everywhere and the closure
    encoding commutes with the identity numerical update.
  * `g123_empty_question_undefined`: at `emptyQuestion` (empty active family,
    so `S₀ = ∅`) `cycle` returns the `empty` failure at every state.
  * `g123_stays_put_at_empty_question`: there the square is vacuous and the
    off-domain statement `StaysPut` holds for the identity numerical update.
  * `g123_off_domain_clause_bites`: a numerical update that moves the root's
    closure record has the vacuous square and still fails the partial
    correspondence at the empty question, on the `outside` field alone.
-/

namespace RatioSpace

namespace Gaps.G1_23

open Layer Gaps.G1_18

/-- `𝒰_𝒬` for the question `Q`: one cycle of the recursion, started from
    Def 10.1's initial ensemble `initialEnsemble Q`. -/
def update (K : Crystallization) (B : Assimilation) (Q : Question) :
    SubstrateState → SubstrateState ⊕ Outcome :=
  fun S => cycle K B S (initialEnsemble Q)

/-- The history `⟨∅, L⟩`. -/
def lHist : History := ⟨Frame.empty, [false]⟩

/-- A question from the root frame at depth 1, active family `[⟨∅, L⟩]`, no
    predicates. Its active cavity is the one history. -/
def resolving : Question := ⟨⟨Frame.empty, [], 0⟩, Frame.empty, 1, [lHist], []⟩

/-- Its one initial record, `Ξ_{τ,0}(⟨∅, L⟩)` against `[⟨∅, L⟩]`. -/
def resolvingAnswer : Answer := initialRecord resolving lHist

theorem g123_resolving_ensemble : initialEnsemble resolving = [resolvingAnswer] := by
  decide

theorem g123_resolving_resolves :
    g118_idCryst.crystQ resolving = Outcome.resolved resolvingAnswer := by
  rw [Crystallization.crystQ_eq, g123_resolving_ensemble]
  exact one_record_resolves _

set_option linter.defProp false in
/-- **The square, stated for `cycle` itself.** Every state is in the domain,
    and appending the answer to the history leaves the closure record, so the
    closure encoding commutes with the identity numerical update. -/
def g123_square_on_resolving_question :
    PartialCorrespondence closureEncoding
      (update g118_idCryst g118_appendWord resolving) id StaysPut where
  commutes := by
    intro S T h
    rw [update, cycle_assimilates_the_answer _ _ _ _ g123_resolving_resolves] at h
    cases h
    rfl
  outside := by
    intro S o h
    rw [update, cycle_assimilates_the_answer _ _ _ _ g123_resolving_resolves] at h
    cases h

/-- A question with an empty active family. Its active cavity is empty, and so
    is its initial ensemble. -/
def emptyQuestion : Question := ⟨⟨Frame.empty, [], 0⟩, Frame.empty, 1, [], []⟩

/-- **At the empty question the update is nowhere defined:** every state
    returns Def 10.4's `|S₇| = 0` failure (`crystQ_of_S0_nil`, for any
    advance). -/
theorem g123_empty_question_undefined (B : Assimilation) (S : SubstrateState) :
    update g118_idCryst B emptyQuestion S = Sum.inr Outcome.empty :=
  (cycle_undefined_iff _ _ _ _ _).2
    ⟨Crystallization.crystQ_of_S0_nil _ rfl, fun _ h => Outcome.noConfusion h⟩

set_option linter.defProp false in
/-- There the square says nothing, and the off-domain statement carries the
    whole claim: the identity numerical update stays put. -/
def g123_stays_put_at_empty_question (B : Assimilation) :
    PartialCorrespondence closureEncoding (update g118_idCryst B emptyQuestion) id StaysPut where
  commutes := by
    intro S T h
    rw [g123_empty_question_undefined] at h
    cases h
  outside := fun _ _ _ => rfl

/-- The root state with the one-step word `R`. -/
def stepped : SubstrateState := ⟨Frame.empty, [true], [], []⟩

/-- A numerical update that sends every record to the closure of `R`. -/
def jumpToR : ClosureState → ClosureState := fun _ => closureOfState stepped

/-- **The off-domain clause bites.** At the empty question the square holds
    for every numerical update, since there is no state in the domain. The
    partial correspondence with `StaysPut` still fails for `jumpToR`, on the
    `outside` field at the root state: `jumpToR` moves the root's closure
    record. -/
theorem g123_off_domain_clause_bites (B : Assimilation) :
    (∀ S T, update g118_idCryst B emptyQuestion S = Sum.inl T →
        closureEncoding.map T = jumpToR (closureEncoding.map S)) ∧
    ¬ Nonempty (PartialCorrespondence closureEncoding
        (update g118_idCryst B emptyQuestion) jumpToR StaysPut) := by
  refine ⟨fun S T h => ?_, ?_⟩
  · rw [g123_empty_question_undefined] at h
    cases h
  · rintro ⟨H⟩
    have h := H.outside g118_state Outcome.empty (g123_empty_question_undefined B _)
    unfold StaysPut at h
    revert h
    decide

end Gaps.G1_23

end RatioSpace
