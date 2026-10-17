/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S22.Face
/-!
  Elements II Corollary 10.8, causal pairing is recordable without becoming a
  face.

  Book statement (Elements II, Corollary 10.8): "Every tagged local sibling pair
  has one exact oriented quarter-turn reception in the direction fixed by the
  designated hand. This reception certificate may be appended to the causal-pair
  record while both raw child histories remain distinct. Attaching a received
  edge or face requires, beyond the certificate, a unique committed lineage,
  joint admission at the event, and the later recording rule. Thus sibling
  relation → reception certificate ⇏ committed face."

  `Causal.lean` carries only `causalRecord_children_distinct`. This file
  states the corollary whole: the certificate as an appendable field of the
  record, the three attachment preconditions read off Theorem 22.6's certificate
  and Construction Axiom II.2, and the non-implication as three exact witnesses,
  one per precondition, each on the record's own identifiers with the other two
  preconditions holding.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_08

open RatioSpace.Two RatioSpace.Two.Face RatioSpace.Two.Terminal

/-! ## The reception certificate -/

/-- **One exact quarter-turn reception, in the direction fixed by the hand.**
    `J_S(A_g) = {j_g}` for either designated hand. -/
theorem reception_phases (g : Bool) : admittedPhases Squarter 4 (A g) = [jPhase g] := by
  cases g <;> decide

/-- The admitted phase is exactly `j_g` and nothing else. -/
theorem reception_unique (g : Bool) (k : Fin 4) :
    k ∈ admittedPhases Squarter 4 (A g) ↔ k = jPhase g := by
  rw [reception_phases]
  exact List.mem_singleton

/-- **Sibling relation → reception certificate.** For every tagged sibling pair
    the relative matrix from the designated child to its sibling is `A_g`, and
    `A_g` has the one admitted phase `j_g`. -/
theorem sibling_relation_certified (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    Two.Q (childProposal id0 seed v g).fullMatrix
        (childProposal id0 seed v (oppositeHand g)).fullMatrix = A g ∧
      admittedPhases Squarter 4 (A g) = [jPhase g] :=
  ⟨childProposal_sibling_matrix id0 seed v g, reception_phases g⟩

/-- **The causal-pair record with its reception certificate appended.** The
    record is kept whole; the certificate is the phase together with the proof
    that it is the only admitted phase of the record's own `A_g`. No face,
    edge or attachment field exists. -/
structure CertifiedRecord where
  record : CausalRecord
  phase : Fin 4
  certified : admittedPhases Squarter 4 (A record.hand) = [phase]

/-- Appending the certificate to a record. -/
def certify (r : CausalRecord) : CertifiedRecord :=
  ⟨r, jPhase r.hand, reception_phases r.hand⟩

/-- Appending changes nothing in the record. -/
theorem certify_record (r : CausalRecord) : (certify r).record = r := rfl

/-- **The certificate is determined by the record.** Any certified form of `r`
    carries the phase `j_g` of `r`'s hand. -/
theorem certified_phase_eq (r : CausalRecord) (C : CertifiedRecord) (h : C.record = r) :
    C.phase = jPhase r.hand := by
  have hc := C.certified
  rw [h, reception_phases] at hc
  exact (List.cons.inj hc).1.symm

/-- **Both raw child histories remain distinct after the append.** -/
theorem certify_children_distinct (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    (certify (causalRecord id0 seed v g)).record.childId ≠
      (certify (causalRecord id0 seed v g)).record.siblingId :=
  causalRecord_children_distinct id0 seed v g

/-! ## The three attachment preconditions -/

/-- **A unique committed lineage** through the parent and the designated child:
    the parent is lineage entry `j`, the terminal support is a singleton, and
    the designated child is entry `j+1`. -/
def CommittedLineage (i : EligInput) : Prop :=
  i.lin[i.j]? = some i.x ∧ i.status = TermStatus.singleton ∧ i.lin[i.j + 1]? = some i.idS

/-- **Actual joint admission at the event**: both children admitted. -/
def JointAdmission (i : EligInput) : Prop :=
  cond i.s i.idBar i.idS ∈ i.admitted ∧ cond i.s i.idS i.idBar ∈ i.admitted

/-- **The recording rule**: the append writes to the certificate's own target. -/
def RecordingRule (i : EligInput) : Prop := i.target = i.certTarget

/-- **Theorem 22.6's certificate is exactly the three preconditions**, because
    its reception clause always holds (`reception_phases`). -/
theorem faceCert_iff (i : EligInput) :
    FaceCert i ↔ CommittedLineage i ∧ JointAdmission i ∧ RecordingRule i := by
  constructor
  · rintro ⟨h1, h2, ⟨h3, h4⟩, _, h5⟩
    exact ⟨⟨h1, h3, h4⟩, h2, h5⟩
  · rintro ⟨⟨h1, h3, h4⟩, h2, h5⟩
    exact ⟨h1, h2, ⟨h3, h4⟩, reception_phases i.s, h5⟩

/-- **Attachment additionally requires all three.** A packet attached by
    Construction Axiom II.2 has a committed lineage, joint admission and a
    lossless recording target. -/
theorem attach_requires {Aux Cert RawAux EvalAux : Type} {h : ℕ}
    (ps : List (FElig Aux Cert RawAux EvalAux h)) (p : FElig Aux Cert RawAux EvalAux h)
    (hp : p ∈ ps) (ha : attach p ∈ receivedFaces ps) :
    CommittedLineage p.input ∧ JointAdmission p.input ∧ RecordingRule p.input := by
  have h1 := (attached_iff ps p hp).mp ha
  rw [p.elig_eq] at h1
  exact (faceCert_iff _).mp ((face_selection _).mpr h1)

/-- And nothing more is required: with the three, the packet is attached. -/
theorem attach_of_preconditions {Aux Cert RawAux EvalAux : Type} {h : ℕ}
    (ps : List (FElig Aux Cert RawAux EvalAux h)) (p : FElig Aux Cert RawAux EvalAux h)
    (hp : p ∈ ps)
    (h3 : CommittedLineage p.input ∧ JointAdmission p.input ∧ RecordingRule p.input) :
    attach p ∈ receivedFaces ps := by
  apply (attached_iff ps p hp).mpr
  rw [p.elig_eq]
  exact (face_selection _).mp ((faceCert_iff _).mpr h3)

/-! ## Reception certificate ⇏ committed face

    Three packets on the record's own identifiers. In each, the certificate
    holds and exactly one precondition is missing while the other two hold, so
    no single precondition is supplied by the certificate together with the
    other two. -/

/-- The packet with no committed lineage. -/
def inputNoLineage (r : CausalRecord) : EligInput where
  lin := []
  admitted := [r.childId, r.siblingId]
  status := TermStatus.singleton
  target := r.childId
  certTarget := r.childId
  j := 0
  x := r.parentId
  s := r.hand
  idS := r.childId
  idBar := r.siblingId

/-- The packet with no joint admission. -/
def inputNoAdmission (r : CausalRecord) : EligInput where
  lin := [r.parentId, r.childId]
  admitted := []
  status := TermStatus.singleton
  target := r.childId
  certTarget := r.childId
  j := 0
  x := r.parentId
  s := r.hand
  idS := r.childId
  idBar := r.siblingId

/-- The packet whose recording target is not the certificate's. -/
def inputNoRecording (r : CausalRecord) : EligInput where
  lin := [r.parentId, r.childId]
  admitted := [r.childId, r.siblingId]
  status := TermStatus.singleton
  target := r.childId
  certTarget := r.siblingId
  j := 0
  x := r.parentId
  s := r.hand
  idS := r.childId
  idBar := r.siblingId

theorem jointAdmission_both (r : CausalRecord) (lin : List QuestionId) (st : TermStatus)
    (t t' : QuestionId) (j : ℕ) :
    JointAdmission ⟨lin, [r.childId, r.siblingId], st, t, t', j, r.parentId, r.hand,
      r.childId, r.siblingId⟩ := by
  cases r.hand <;> simp [JointAdmission]

/-- **Certificate without a committed lineage: no face.** -/
theorem no_face_without_lineage (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    let r := causalRecord id0 seed v g
    let i := inputNoLineage r
    (certify r).phase = jPhase i.s ∧ JointAdmission i ∧ RecordingRule i ∧
      ¬ CommittedLineage i ∧ ¬ FaceCert i := by
  intro r i
  refine ⟨rfl, jointAdmission_both r _ _ _ _ _, rfl, ?_, ?_⟩
  · intro h
    exact absurd h.1 (by simp [i, inputNoLineage])
  · intro h
    exact absurd h.parent_on_lineage (by simp [i, inputNoLineage])

/-- **Certificate without joint admission: no face.** -/
theorem no_face_without_admission (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    let r := causalRecord id0 seed v g
    let i := inputNoAdmission r
    (certify r).phase = jPhase i.s ∧ CommittedLineage i ∧ RecordingRule i ∧
      ¬ JointAdmission i ∧ ¬ FaceCert i := by
  intro r i
  refine ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl, ?_, ?_⟩
  · intro h
    exact nomatch h.1
  · intro h
    exact nomatch h.jointly_admitted.1

/-- **Certificate without the recording rule: no face.** The two targets differ
    because the two children's identifiers differ (`certify_children_distinct`). -/
theorem no_face_without_recording (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    let r := causalRecord id0 seed v g
    let i := inputNoRecording r
    (certify r).phase = jPhase i.s ∧ CommittedLineage i ∧ JointAdmission i ∧
      ¬ RecordingRule i ∧ ¬ FaceCert i := by
  intro r i
  have hne := causalRecord_children_distinct id0 seed v g
  refine ⟨rfl, ⟨rfl, rfl, rfl⟩, jointAdmission_both r _ _ _ _ _, hne, ?_⟩
  intro h
  exact hne h.recorded

/-- **Corollary 10.8, boxed.** Every tagged sibling pair's record carries its
    reception certificate with the children distinct, and for the same record
    there is an eligibility packet on its identifiers, certificate holding, with
    no committed face. -/
theorem corollary_10_8 (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    (certify (causalRecord id0 seed v g)).record.childId ≠
        (certify (causalRecord id0 seed v g)).record.siblingId ∧
      admittedPhases Squarter 4 (A g) = [(certify (causalRecord id0 seed v g)).phase] ∧
      ∃ i : EligInput, i.x = (causalRecord id0 seed v g).parentId ∧
        i.idS = (causalRecord id0 seed v g).childId ∧
        i.idBar = (causalRecord id0 seed v g).siblingId ∧ i.s = g ∧
        eRecv i.s = true ∧ ¬ FaceCert i :=
  ⟨certify_children_distinct id0 seed v g, reception_phases g,
    inputNoAdmission (causalRecord id0 seed v g), rfl, rfl, rfl, rfl, eRecv_true g,
    (no_face_without_admission id0 seed v g).2.2.2.2⟩

#print axioms reception_phases
#print axioms reception_unique
#print axioms sibling_relation_certified
#print axioms CertifiedRecord
#print axioms certify
#print axioms certify_record
#print axioms certified_phase_eq
#print axioms certify_children_distinct
#print axioms CommittedLineage
#print axioms JointAdmission
#print axioms RecordingRule
#print axioms faceCert_iff
#print axioms attach_requires
#print axioms attach_of_preconditions
#print axioms inputNoLineage
#print axioms inputNoAdmission
#print axioms inputNoRecording
#print axioms jointAdmission_both
#print axioms no_face_without_lineage
#print axioms no_face_without_admission
#print axioms no_face_without_recording
#print axioms corollary_10_8

end G2_08
end Gaps
end RatioSpace
