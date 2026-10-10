/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S05.Mediant
/-!
  Gap G2-06 — Elements II Proposition 5.7, proposal covariance under a common
  prefix, as the family equality `P_{j+1}(Z_u S_j) = Z_u P_{j+1}(S_j)`.

  `Two/Mediant.lean` proves the covariance at one occurrence
  (`transportProposal_child`, `childProposal_transport_comm`), with the transport
  acting on the tuple `(u, id0, seed, v)`. This file supplies the missing action
  on a `ProposalRecord` itself, `transportRecord`, and proves the book's
  equality over the whole family, then reads it componentwise: identifiers are
  carried unchanged, world words gain `u` on the left, world matrices move by
  `Z_u`.

  The transport re-derives a record from its retained `(seedId, seed, relWord)`
  with the seed transported by `transportSeed`, exactly as `transportProposal`
  does. It cannot be defined field by field: the reached frame and the address
  depend on the seed's start and word jointly, not on the old frame alone.
-/

namespace RatioSpace
namespace Gaps

open RatioSpace.Two Word Mat2

/-- **Support for 5.7.** `Z_u` acting on a proposal record: transport its seed
    by `u` and re-derive the record at the same seed identifier and relative
    word. -/
def transportRecord (u : Word) (x : ProposalRecord) : ProposalRecord :=
  proposal x.seedId (transportSeed u x.seed) x.relWord

/-- On a record built by `proposal`, `transportRecord` is `Mediant.lean`'s
    `transportProposal`. -/
theorem transportRecord_proposal (u : Word) (id0 : QuestionId) (seed : History) (v : Word) :
    transportRecord u (proposal id0 seed v) = transportProposal u id0 seed v := rfl

/-- A record is **generated** when every field is the one `proposal` derives
    from its own seed identifier, seed and relative word. -/
def Generated (x : ProposalRecord) : Prop :=
  x = proposal x.seedId x.seed x.relWord

theorem proposal_generated (id0 : QuestionId) (seed : History) (v : Word) :
    Generated (proposal id0 seed v) := rfl

/-- Every member of a complete proposal family is generated. -/
theorem proposalFamily_generated (S : List ProposalRecord) :
    ∀ y ∈ proposalFamily S, Generated y := by
  intro y hy
  simp only [proposalFamily, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hy
  rcases hy with ⟨x, -, h | h⟩ <;> subst h <;> rfl

/-- **Proposition 5.7.** `P_{j+1}(Z_u S_j) = Z_u P_{j+1}(S_j)`, as one equation
    of lists: proposing from the transported support gives the transported
    proposal family, occurrence for occurrence and in the same order. No
    hypothesis on `S`. -/
theorem proposalFamily_transport (u : Word) (S : List ProposalRecord) :
    proposalFamily (S.map (transportRecord u)) = (proposalFamily S).map (transportRecord u) := by
  induction S with
  | nil => rfl
  | cons x xs ih =>
      simp only [proposalFamily, List.map_cons, List.flatMap_cons, List.map_append,
        List.map_nil] at ih ⊢
      rw [ih]
      rfl

/-- Transport leaves the stable identifier of a generated record unchanged:
    the occurrence tags are carried with their seeds. -/
theorem transportRecord_id {x : ProposalRecord} (hx : Generated x) (u : Word) :
    (transportRecord u x).id = x.id := by
  rw [hx]; rfl

/-- Transport prefixes the world word of a generated record by `u`. -/
theorem transportRecord_fullWord {x : ProposalRecord} (hx : Generated x) (u : Word) :
    (transportRecord u x).fullWord = u ++ x.fullWord := by
  rw [hx]
  simp [transportRecord, proposal, transportSeed, List.append_assoc]

/-- Transport moves the world matrix of a generated record by `Z_u`;
    `Mediant.lean`'s `transportProposal_fullMatrix`, read on the record. -/
theorem transportRecord_fullMatrix {x : ProposalRecord} (hx : Generated x) (u : Word) :
    (transportRecord u x).fullMatrix = Z u x.fullMatrix := by
  rw [hx]
  exact transportProposal_fullMatrix u x.seedId x.seed x.relWord

/-- **Proposition 5.7, identifiers.** The transported family carries exactly
    the identifiers of the untransported one. -/
theorem proposalFamily_transport_ids (u : Word) (S : List ProposalRecord) :
    (proposalFamily (S.map (transportRecord u))).map ProposalRecord.id =
      (proposalFamily S).map ProposalRecord.id := by
  rw [proposalFamily_transport, List.map_map]
  exact List.map_congr_left fun y hy =>
    transportRecord_id (proposalFamily_generated S y hy) u

/-- **Proposition 5.7, world matrices.** `Z_u(M_x g) = Z_u(M_x) g` over the
    whole family: the matrices proposed from the transported support are the
    `Z_u`-images of the matrices proposed from the original support. -/
theorem proposalFamily_transport_fullMatrix (u : Word) (S : List ProposalRecord) :
    (proposalFamily (S.map (transportRecord u))).map ProposalRecord.fullMatrix =
      (proposalFamily S).map (fun y => Z u y.fullMatrix) := by
  rw [proposalFamily_transport, List.map_map]
  exact List.map_congr_left fun y hy =>
    transportRecord_fullMatrix (proposalFamily_generated S y hy) u

/-- **Proposition 5.7, world words.** Every proposed world word from the
    transported support is `u` followed by the corresponding original one. -/
theorem proposalFamily_transport_fullWord (u : Word) (S : List ProposalRecord) :
    (proposalFamily (S.map (transportRecord u))).map ProposalRecord.fullWord =
      (proposalFamily S).map (fun y => u ++ y.fullWord) := by
  rw [proposalFamily_transport, List.map_map]
  exact List.map_congr_left fun y hy =>
    transportRecord_fullWord (proposalFamily_generated S y hy) u

#print axioms transportRecord
#print axioms transportRecord_proposal
#print axioms Generated
#print axioms proposal_generated
#print axioms proposalFamily_generated
#print axioms proposalFamily_transport
#print axioms transportRecord_id
#print axioms transportRecord_fullWord
#print axioms transportRecord_fullMatrix
#print axioms proposalFamily_transport_ids
#print axioms proposalFamily_transport_fullMatrix
#print axioms proposalFamily_transport_fullWord

end Gaps
end RatioSpace
