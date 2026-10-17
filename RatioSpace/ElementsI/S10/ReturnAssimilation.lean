/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S10.Crystal
/-!
  Gap G1-18 — Elements I §10, Definition 10.6, return assimilation: the history
  update the carrier assumed.

  **Book statement.** `ℬ_𝒬 : (S_τ, Â_{τ+1}) ↦ S_{τ+1}` "propagates the resolved
  record through the retained stack and updates the observer and active
  context", and "the literal state-update formula for `ℬ_𝒬` remains part of the
  *Elements II* construction".

  **The carrier.** The rule
  `(assimilate S A).history = S.history ++ [A.word]` is not a field of
  `Assimilation` (`Crystal.lean`). Elements I states no such formula. Elements II
  Definition 19.5 appends a different record,
  `H_{τ+1} = H_τ ‖ (C^cyc_𝒬(x*), A^occ_τ, A^occ_{τ+1})`, and sets
  `w_{τ+1} = w_{x*}`. So the rule is a hypothesis the book does not state and
  the Elements II map does not satisfy as written. In `Crystal.lean`,
  `cycle_assimilates_the_answer`: a resolved cycle returns `B.assimilate S A`,
  with no claim about what that is.

  **Added here.**
  * `g118_AppendsWord B`: the append rule, as a named convention an assimilation may
    or may not satisfy (the positive-walk reading).
  * `g118_cycle_records_the_answer`: under that convention, a resolved cycle grows
    the history by the answer's word.
  * `g118_appendWord`: an assimilation satisfying it, so the convention is
    consistent with the carrier.
  * `g118_appendEmpty`: an assimilation that appends the empty word instead,
    and `g118_appendEmpty_not_appends`: it does not satisfy the convention. So
    the carrier does not force a history formula. (The assimilation that changes
    nothing is ruled out by the carrier's `changes` field, Def 10.8.)
  * `g118_carrier_leaves_history_open`: one crystallization, one state, one
    resolved answer, two assimilations, two different next histories.

  **Not done here.** Definition 10.6 also says the return pass updates the
  observer. `SubstrateState` has no observer field; the state's `origin` and
  `word` are the retained walk. Whether that walk is the observer the book
  means (Elements II 19.5 adopts `w_{x*}` as the next observer word) is not
  settled by this file.
-/
namespace RatioSpace

namespace Gaps.G1_18

/-- **The append convention.** The history grows by the answer's word and by
    nothing else. Elements I does not state it; Elements II Definition 19.5
    appends a cycle certificate and two occurrence families instead. -/
def g118_AppendsWord (B : Assimilation) : Prop :=
  ∀ S A, (B.assimilate S A).history = S.history ++ [A.word]

/-- Under the append convention, a resolved cycle grows the history by the
    answer's word. -/
theorem g118_cycle_records_the_answer (K : Crystallization) (B : Assimilation)
    (hB : g118_AppendsWord B) (S : SubstrateState) (X : Ensemble) {A : Answer}
    (h : K.cryst X = Outcome.resolved A) :
    ∃ T, cycle K B S X = Sum.inl T ∧ T.history = S.history ++ [A.word] :=
  ⟨B.assimilate S A, cycle_assimilates_the_answer K B S X h, hB S A⟩

/-- An assimilation that appends the answer's word and changes nothing else. -/
def g118_appendWord : Assimilation where
  assimilate S A := { S with history := S.history ++ [A.word] }
  changes S A h := by
    have h2 := congrArg (fun T : SubstrateState => T.history.length) h
    change (S.history ++ [A.word]).length = S.history.length at h2
    rw [List.length_append, List.length_singleton] at h2
    exact Nat.succ_ne_self _ h2

theorem g118_appendWord_appends : g118_AppendsWord g118_appendWord :=
  fun _ _ => rfl

/-- An assimilation that appends the empty word, whatever the answer. -/
def g118_appendEmpty : Assimilation where
  assimilate S _ := { S with history := S.history ++ [[]] }
  changes S _ h := by
    have h2 := congrArg (fun T : SubstrateState => T.history.length) h
    change (S.history ++ [[]]).length = S.history.length at h2
    rw [List.length_append, List.length_singleton] at h2
    exact Nat.succ_ne_self _ h2

/-- The root state with empty word, family and history. -/
def g118_state : SubstrateState := ⟨Frame.empty, [], [], []⟩

/-- The answer with history `⟨∅, L⟩` and empty readings. -/
def g118_answer : Answer := ⟨⟨Frame.empty, [false]⟩, [], []⟩

/-- **The carrier does not force the append rule.** -/
theorem g118_appendEmpty_not_appends : ¬ g118_AppendsWord g118_appendEmpty := by
  intro h
  have := h g118_state g118_answer
  revert this
  decide

/-- The crystallization whose advance is the identity,
    `Crystallization.identity`. -/
def g118_idCryst : Crystallization := Crystallization.identity

/-- **Definition 10.6 leaves the history update open.** One crystallization,
    one state, one ensemble resolving to one answer, two assimilations, two
    different next histories. -/
theorem g118_carrier_leaves_history_open :
    ∃ (K : Crystallization) (B B' : Assimilation) (S : SubstrateState)
      (X : Ensemble) (A : Answer),
      K.cryst X = Outcome.resolved A ∧
      cycle K B S X = Sum.inl (B.assimilate S A) ∧
      cycle K B' S X = Sum.inl (B'.assimilate S A) ∧
      (B.assimilate S A).history ≠ (B'.assimilate S A).history :=
  ⟨g118_idCryst, g118_appendWord, g118_appendEmpty, g118_state, [g118_answer], g118_answer,
   by decide, cycle_assimilates_the_answer _ _ _ _ (by decide),
   cycle_assimilates_the_answer _ _ _ _ (by decide), by decide⟩

end Gaps.G1_18

end RatioSpace
