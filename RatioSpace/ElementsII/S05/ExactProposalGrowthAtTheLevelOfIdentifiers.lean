/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S05.Mediant
/-!
  Gap G2-05 — Elements II Corollary 5.5, exact proposal growth, at the level of
  identifiers.

  `proposalFamily_length` counts list positions. The book's `S_j × {L,R}` is a
  product of occurrences, and "no proposal is merged" says the `2|S_j|` children
  carry `2|S_j|` distinct stable identifiers. Proposition 5.4
  (`QuestionId.child_inj`) is the step; this file composes it over the family.

  Hypothesis carried: each parent's identifier is its own tag, `x.id =
  (proposal x.seedId x.seed x.relWord).id`. `ProposalRecord` is a structure with
  free fields, and `proposalFamily` builds children from `(seedId, relWord)`,
  not from `id`; a record whose `id` field disagrees with its own tag is not an
  occurrence of Definition 4.2. Every record `proposal` builds satisfies it by
  `rfl` (`proposal_tagged`).
-/

namespace RatioSpace
namespace Gaps

open RatioSpace.Two

/-- A proposal record is **tagged** when its identifier is the one Definition
    4.1 assigns to its seed and relative word. -/
def Tagged (x : ProposalRecord) : Prop :=
  x.id = (proposal x.seedId x.seed x.relWord).id

/-- Every record built by `proposal` is tagged. -/
theorem proposal_tagged (id0 : QuestionId) (seed : History) (v : Word) :
    Tagged (proposal id0 seed v) := rfl

/-- **Corollary 5.5, identifiers.** The identifiers of `P_{j+1}(S_j)` are
    exactly `ids(S_j) × {L,R}`: each parent identifier followed by its `L`-child
    and `R`-child identifiers. -/
theorem proposalFamily_ids (S : List ProposalRecord) (hS : ∀ x ∈ S, Tagged x) :
    (proposalFamily S).map ProposalRecord.id =
      (S.map ProposalRecord.id).flatMap fun i => [i.child false, i.child true] := by
  induction S with
  | nil => simp [proposalFamily]
  | cons x xs ih =>
      have hx : Tagged x := hS x (List.mem_cons_self)
      have hxs : ∀ y ∈ xs, Tagged y := fun y hy => hS y (List.mem_cons_of_mem _ hy)
      have ih' := ih hxs
      simp only [proposalFamily, List.flatMap_cons, List.map_append, List.map_cons,
        List.map_nil] at ih' ⊢
      rw [ih']
      unfold Tagged at hx
      rw [hx, childProposal_id, childProposal_id]

/-- **Corollary 5.5, no merging.** If the active support carries distinct
    identifiers, so does its complete proposal family. Proposition 5.4
    (`QuestionId.child_inj`) is the step: children of distinct parents are
    distinct, and the two children of one parent differ in their hand. -/
theorem proposalFamily_ids_nodup (S : List ProposalRecord) (hS : ∀ x ∈ S, Tagged x)
    (hnodup : (S.map ProposalRecord.id).Nodup) :
    ((proposalFamily S).map ProposalRecord.id).Nodup := by
  rw [proposalFamily_ids S hS, List.nodup_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    intro h
    have h' : i.child false = i.child true := List.mem_singleton.mp h
    exact Bool.false_ne_true (QuestionId.child_inj h').2
  · refine hnodup.imp fun {i j} hij => ?_
    intro a ha hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with h | h <;>
      exact hij (QuestionId.child_inj h).1

/-- **Corollary 5.5, as a count of distinct identifiers.** Removing repeated
    identifiers from the family removes nothing: the distinct stable identifiers
    proposed number exactly `2|S_j|`. -/
theorem proposalFamily_ids_dedup_length (S : List ProposalRecord) (hS : ∀ x ∈ S, Tagged x)
    (hnodup : (S.map ProposalRecord.id).Nodup) :
    ((proposalFamily S).map ProposalRecord.id).dedup.length = 2 * S.length := by
  rw [List.dedup_eq_self.mpr (proposalFamily_ids_nodup S hS hnodup), List.length_map,
    proposalFamily_length]

/-- The children are again tagged, so the statement iterates tick by tick. -/
theorem proposalFamily_tagged (S : List ProposalRecord) :
    ∀ y ∈ proposalFamily S, Tagged y := by
  intro y hy
  simp only [proposalFamily, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hy
  rcases hy with ⟨x, -, h | h⟩ <;> subst h <;> rfl

#print axioms Tagged
#print axioms proposal_tagged
#print axioms proposalFamily_ids
#print axioms proposalFamily_ids_nodup
#print axioms proposalFamily_ids_dedup_length
#print axioms proposalFamily_tagged

end Gaps
end RatioSpace
