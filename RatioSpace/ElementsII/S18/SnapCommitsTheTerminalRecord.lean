/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S22.Face
import RatioSpace.ElementsII.S18.Snap
/-!
  Elements II §18, Separation Rule 18.4, Snap is not return
  assimilation.

  **Book statement.** *"The coherent snap determines which complete terminal
  record is committed. It does not yet replace the observer, alter the active
  state, form the next question, or attach a received face. Those are
  differently typed operations."*

  **The other clauses.** Observer, question and active state are
  `snap_forms_no_new_observer`, `snap_forms_no_new_question`,
  `snap_alters_no_active_state` (`Snap.lean`). `Report` has no face field.

  **The face clause.** Attachment (Construction Axiom II.2, `Face.receivedFaces`) is
  decided by each packet's eligibility vector. Every packet carries a cycle
  certificate, and the certificate carries a snap (`CycleCertificate.snapped`).
  * `receivedFaces_replace_snap`: replacing the snap inside every packet's
    certificate by any other snap changes the attached faces only in that
    slot; which packets attach is unchanged.
  * `snap_attaches_no_face`: in particular the number of attached faces is the
    same for every choice of snap, and a packet list with no all-ones
    eligibility attaches no face whatever snap it carries.
  So the snap decides no attachment: that is the differently typed operation.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_18

open RatioSpace.Two RatioSpace.Two.Terminal RatioSpace.Two.Return RatioSpace.Two.Face

variable {Aux Cert RawAux EvalAux : Type} {h : ℕ}

/-- A packet with the snap inside its cycle certificate replaced. -/
def withSnap (sn : Cand EvalAux × Report RawAux EvalAux h) (pk : FElig Aux Cert RawAux EvalAux h) :
    FElig Aux Cert RawAux EvalAux h :=
  { pk with cycle := { pk.cycle with snapped := sn } }

/-- **Separation Rule 18.4, the face clause.** Attaching received faces
    commutes with replacing the snap: the faces attached from packets carrying
    the snap `sn` are exactly the faces attached from the original packets,
    with `sn` put in the snap slot. -/
theorem receivedFaces_replace_snap (sn : Cand EvalAux × Report RawAux EvalAux h)
    (ps : List (FElig Aux Cert RawAux EvalAux h)) :
    receivedFaces (ps.map (withSnap sn))
      = (receivedFaces ps).map (fun f => attach (withSnap sn f.packet)) := by
  unfold receivedFaces
  rw [List.filter_map, List.map_map, List.map_map]
  rfl

/-- A packet list none of whose eligibility vectors is all ones attaches no
    face. -/
theorem receivedFaces_none_eligible (ps : List (FElig Aux Cert RawAux EvalAux h))
    (hne : ∀ pk ∈ ps, pk.elig.all = false) : receivedFaces ps = [] := by
  induction ps with
  | nil => rfl
  | cons pk ps ih =>
    have h1 : pk.elig.all = false := hne pk (List.Mem.head _)
    have h2 := ih (fun q hq => hne q (List.Mem.tail _ hq))
    unfold receivedFaces at h2 ⊢
    rw [List.filter_cons_of_neg (by rw [h1]; exact Bool.false_ne_true)]
    exact h2

/-- **The snap attaches no face.** For any two snaps, packets carrying either
    attach the same number of faces; and packets none of whose eligibility
    vectors is all ones attach nothing, whatever snap they carry. -/
theorem snap_attaches_no_face (sn sn' : Cand EvalAux × Report RawAux EvalAux h)
    (ps : List (FElig Aux Cert RawAux EvalAux h)) :
    (receivedFaces (ps.map (withSnap sn))).length = (receivedFaces (ps.map (withSnap sn'))).length ∧
      ((∀ pk ∈ ps, pk.elig.all = false) → receivedFaces (ps.map (withSnap sn)) = []) := by
  refine ⟨?_, ?_⟩
  · rw [receivedFaces_replace_snap, receivedFaces_replace_snap, List.length_map, List.length_map]
  · intro hne
    rw [receivedFaces_replace_snap, receivedFaces_none_eligible ps hne]
    rfl

#print axioms receivedFaces_replace_snap
#print axioms receivedFaces_none_eligible
#print axioms snap_attaches_no_face

end G2_18
end Gaps
end RatioSpace
