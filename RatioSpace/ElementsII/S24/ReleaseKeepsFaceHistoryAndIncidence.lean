/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S24.Lifecycle
import RatioSpace.ElementsII.S15.Accumulation
/-!
  Elements II §24, Theorem 24.14, Release keeps face
  history and incidence.

  **Book statement.** *"A release transition changes only the active retained
  view of a face. It does not delete or alter: the immutable entry face record;
  the parent, selected child, or refused child occurrence; either raw boundary
  edge or the received sibling shortcut; the admission, eligibility, snap,
  cycle, lift, or holonomy records; any earlier renewal transport or lifecycle
  event; or the archival vertex, edge, boundary, or incidence maps of
  Definition 23.4. The complete pre-release face and the exact reason for
  release remain recoverable."* Proof: *"... it contains no deletion or
  replacement operation on 𝖥_{τ+1}, Inc_V, Inc_E, Bd, the occurrence archive,
  or the cycle trace. Theorem 23.7 therefore continues to recover every exact
  preimage, and the failed-gate set recovers the release reason."*

  **The full archive.** `Archive` holds face records and the two lifecycle
  ledgers only; the occurrence archive, the event ledger, the cycle trace and
  the recorded state history (Definition 23.5) are added below, and Theorem 23.7
  is re-invoked after a release.

  **Contents.**
  * `FullArchive`: the lifecycle `Archive` together with the recorded state
    `RecState` whose history carries the face ledger (Definitions 22.4, 23.5),
    and the complete carrier trace `(𝔛_{τ,0}, …, 𝔛_{τ,n})` of Definition 15.1,
    each carrier holding its occurrence archive `ℋ_j` and event ledger `ℰ_j`.
  * `applyReleaseFull`: Definition 24.12's release on the full archive.
  * `release_deletes_nothing_full`: face records, `incV`, `incE`, `bd`, the
    recorded state (operative part and history), the carrier trace, and so the
    occurrence archive and event ledger at every trace position, are equal
    before and after; a trace equal to `Accumulation.trace pol X0 _ n _` stays
    equal to it; the lifecycle ledger and release list are prefix-kept and the
    last release names the failed gates.
  * `release_preserves_preimages`: Theorem 23.7 (`face_preimages`) re-invoked
    on the post-release archive: every entry face record present before release
    is present after, is found under its own key, and all of Theorem 23.7's
    preimages are recovered from it and the post-release recorded state.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_27

open RatioSpace.Mat2 RatioSpace.Two RatioSpace.Two.Face RatioSpace.Two.Incidence RatioSpace.Two.Lifecycle

variable {Aux Cert RawAux EvalAux Prov Renew Op P Y TAux : Type} {h hT : ℕ}

/-- The archival state Theorem 24.14's proof names: face records and lifecycle
    ledgers (`arch`), the recorded state whose history holds the face ledger,
    and the complete carrier trace, each carrier with its occurrence archive
    and event ledger. -/
structure FullArchive (Aux Cert RawAux EvalAux : Type) (h : ℕ) (Prov Renew Op P Y TAux : Type) (hT : ℕ) where
  arch : Archive (FaceRec Aux Cert RawAux EvalAux h Prov Renew) P Y
  state : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
  cycTrace : List (TickCarrier TAux hT)

/-- Definition 24.12's release on the full archive. -/
def applyReleaseFull (ar : FullArchive Aux Cert RawAux EvalAux h Prov Renew Op P Y TAux hT)
    (e : LifeEvt P Y) (rel : ReleaseRec P) : FullArchive Aux Cert RawAux EvalAux h Prov Renew Op P Y TAux hT :=
  { ar with arch := applyRelease ar.arch e rel }

/-- **Theorem 24.14, with the occurrence archive and cycle trace.** -/
theorem release_deletes_nothing_full (ar : FullArchive Aux Cert RawAux EvalAux h Prov Renew Op P Y TAux hT)
    (e : LifeEvt P Y) (fid : FaceId) (n : ℕ) (g : Gates) (Z : P) (v : QuestionId) (eu : UEdge) :
    let ar' := applyReleaseFull ar e (releaseRec fid n g Z)
    ar'.arch.faces = ar.arch.faces ∧
    incV ar'.arch.faces v = incV ar.arch.faces v ∧ incE ar'.arch.faces eu = incE ar.arch.faces eu ∧
    (∀ fid', bd ar'.arch.faces fid' = bd ar.arch.faces fid') ∧
    ar'.state.op = ar.state.op ∧ ar'.state.hist = ar.state.hist ∧
    ar'.cycTrace = ar.cycTrace ∧
    ar'.cycTrace.map (·.archive) = ar.cycTrace.map (·.archive) ∧
    ar'.cycTrace.map (·.ledger) = ar.cycTrace.map (·.ledger) ∧
    ar.arch.lifeLedger <+: ar'.arch.lifeLedger ∧ ar.arch.releases <+: ar'.arch.releases ∧
    ar'.arch.releases.getLast? = some ⟨fid, n, g.fail, Z⟩ := by
  intro ar'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := release_deletes_nothing ar.arch e fid n g Z v eu
  exact ⟨h1, h2, h3, h4, rfl, rfl, rfl, rfl, rfl, h5, h6, h7⟩

/-- A release does not replace the cycle trace: if the stored trace is the
    trace of Definition 15.1, it still is. -/
theorem release_keeps_trace (ar : FullArchive Aux Cert RawAux EvalAux h Prov Renew Op P Y TAux hT)
    (e : LifeEvt P Y) (rel : ReleaseRec P) (pol : Accumulation.Policy TAux hT) (X0 : TickCarrier TAux hT)
    (hX0 : Two.Accumulation.Seeded X0) (m : ℕ) (hm : m ≤ hT) (ht : ar.cycTrace = Accumulation.trace pol X0 hX0 m hm) :
    (applyReleaseFull ar e rel).cycTrace = Accumulation.trace pol X0 hX0 m hm := ht

/-- **Theorem 24.14, "Theorem 23.7 therefore continues to recover every exact
    preimage".** An entry face record present before the release is present
    after it, is found under its own key exactly as before, and Theorem 23.7's
    preimages (parent and both children, both raw edges, the received shortcut
    and its inverse orientation, shortcut and cycle certificates, lift status,
    and the prior history kept by recording) are recovered from the
    post-release archive and recorded state. -/
theorem release_preserves_preimages (ar : FullArchive Aux Cert RawAux EvalAux h Prov Renew Op P Y TAux hT)
    (e : LifeEvt P Y) (rel : ReleaseRec P) (p : FElig Aux Cert RawAux EvalAux h) (hwk : WellKeyed p.input)
    (t : QuestionId) (pv : Prov) (hmem : entryRec (Renew := Renew) p t pv ∈ ar.arch.faces)
    (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) :
    let ar' := applyReleaseFull ar e rel
    let r := entryRec (Renew := Renew) p t pv
    r ∈ ar'.arch.faces ∧
    ar'.arch.faces.find? (fun x => decide (x.id = r.id)) = ar.arch.faces.find? (fun x => decide (x.id = r.id)) ∧
    (r.id.v0 = p.input.x ∧ r.id.v1 = p.input.x.child p.input.s ∧ r.id.v2 = p.input.x.child (!p.input.s)) ∧
    (r.e0.ty = .raw ∧ r.e0.src = p.input.x ∧ r.e2.ty = .raw ∧ r.e2.dst = p.input.x) ∧
    (r.e1.ty = .received ∧ inv2 (A p.input.s) = A (!p.input.s)) ∧
    r.packet.shortcut = p.shortcut ∧ r.packet.cycle = p.cycle ∧ r.packet.lift = p.lift ∧
    ar'.state.hist <+: (recordFace ar'.state t L).hist := by
  intro ar' r
  exact ⟨hmem, rfl, face_preimages p hwk t pv ar'.state L⟩

#print axioms release_deletes_nothing_full
#print axioms release_keeps_trace
#print axioms release_preserves_preimages

end G2_27
end Gaps
end RatioSpace
