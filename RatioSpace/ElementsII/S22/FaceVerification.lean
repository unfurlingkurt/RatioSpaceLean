/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S22.Face
import RatioSpace.ElementsII.S16.LoneSeed
/-!
  Elements II §22, Proposition 22.10 — Canonical seven-tick face regression.

  Everything here is read off the seven concrete traces `RootOrbit.lean` and
  `LoneSeed.lean` already run. Nothing is re-stated from the book's table:

  * **The committed lineage** is derived from the terminal support itself: when
    `S_7` is one occurrence `x*`, `Lin(x*)` is the list of prefixes of its
    relative word (Definition 4.1: deleting the final generator is the parent),
    and `lineage_grounded_*` checks that list against the archive's own stored
    `parent` pointers and against the active support at every tick.
  * **Joint admission at event `j+1`** is read from the admitted family the
    trace's own selection rule ran over, *before* coherence selection:
    `admittedCoresSide … gammaSideL` at event 1 of `𝒬_ε^L` (Definition 16.7's
    predicate is part of admission there) and `admittedCores` at every other
    event, applied to `proposals X_j.archive X_j.active`. That is admission
    exposed separately from retention (`activeWords`), which is what `eAdm`
    reads.
  * **The recording entry** is the proposition's own hypothesis ("equip … with
    the lossless face-recording capability"): the socket target `t` is left
    universally quantified and the append writes to it, so no target constant
    is supplied from outside the structure.
-/
set_option linter.style.longLine false
set_option maxRecDepth 200000

namespace RatioSpace
namespace Two
namespace FaceRegression

open Mat2 Word Frame Pres RatioSpace Advance Accumulation RootOrbit LoneSeed Terminal Face

/-! ## The event data, independent of the socket target -/

/-- One lineage event `j+1`: the lineage, the admitted family at that event,
    the terminal status, the parent `x_j`, and the committed hand `s`. -/
structure Event where
  lin : List QuestionId
  admitted : List QuestionId
  status : TermStatus
  j : ℕ
  x : QuestionId
  s : Bool

/-- The eligibility input of Definition 22.5 for the event, at socket target `t`. -/
def Event.toInput (e : Event) (t : QuestionId) : EligInput where
  lin := e.lin
  admitted := e.admitted
  status := e.status
  target := t
  certTarget := t
  j := e.j
  x := e.x
  s := e.s
  idS := e.x.child e.s
  idBar := e.x.child (!e.s)

/-- The eligibility vector with the recording entry already one. -/
def Event.vec (e : Event) : Eligibility where
  lin := eLin e.lin e.j e.x
  adm := eAdm e.admitted (cond e.s (e.x.child (!e.s)) (e.x.child e.s))
    (cond e.s (e.x.child e.s) (e.x.child (!e.s)))
  snap := eSnap e.status e.lin e.j (e.x.child e.s)
  recv := eRecv e.s
  record := true

/-- With the lossless capability equipped (the append writes to its own
    target), the vector of Definition 22.5 is `Event.vec`, for every target. -/
theorem Event.toInput_vector (e : Event) (t : QuestionId) : (e.toInput t).vector = e.vec := by
  change Eligibility.mk _ _ _ _ (eRecord t t) = _
  unfold eRecord
  rw [decide_eq_true rfl]
  rfl

/-- `Lin(x*)`: the prefixes of the terminal occurrence's relative word. -/
def linOf (x : QuestionId) : List QuestionId :=
  (List.range (x.rel.length + 1)).map fun k => { x with rel := x.rel.take k }

/-- The committed lineage exists exactly on the singleton stratum. -/
def terminalLin {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) : List QuestionId :=
  match X.active with
  | [x] => linOf x
  | _ => []

/-- The events of a lineage: one per consecutive pair `(x_j, x_{j+1})`, with
    the committed hand read off as whether `x_{j+1}` is `x_j`'s `R` child. -/
def events (lin : List QuestionId) (adms : List (List QuestionId)) (status : TermStatus) : List Event :=
  ((List.range adms.length).zip ((lin.zip lin.tail).zip adms)).map fun p =>
    { lin := lin, admitted := p.2.2, status := status, j := p.1, x := p.2.1.1,
      s := decide (p.2.1.2 = p.2.1.1.child true) }

/-- Construction Axiom II.2 applied to the events: the ones with all five entries one. -/
def attached (es : List Event) : List Event := es.filter fun e => e.vec.all

def attachedEvents (es : List Event) : List ℕ := (attached es).map fun e => e.j + 1
def attachedHands (es : List Event) : List Bool := (attached es).map Event.s
def attachedPhases (es : List Event) : List (Fin 4) := (attachedHands es).map jPhase

/-- The archive's own parent pointer for an identifier. -/
def parentIn (arch : List Core) (i : QuestionId) : Option QuestionId :=
  (arch.find? fun c => decide (c.id = i)).bind Core.parent

/-- Every lineage step is a stored parent pointer. -/
def parentsOk (arch : List Core) (lin : List QuestionId) : Bool :=
  (lin.zip lin.tail).all fun p => decide (parentIn arch p.2 = some p.1)

/-- Every lineage member was active at its own tick. -/
def activeOk (Xs : List (TickCarrier Unit hQ)) (lin : List QuestionId) : Bool :=
  (Xs.zip lin).all fun p => decide (p.2 ∈ p.1.active)

/-! ## Linking to Theorem 22.8 through the packet type -/

/-- The committed-parent, snap, reception and recording entries all one. -/
def Event.fixedOk (e : Event) : Bool := e.vec.lin && e.vec.snap && e.vec.recv && e.vec.record

/-- **Theorem 22.8 at these events.** For any complete packets whose inputs are
    exactly the events' inputs (at any socket target), and any further
    candidates failing lineage or snap, the attached-face count is the number
    of jointly admitted events. The packet's shortcut, boundary, reception,
    lift and cycle-certificate components do not enter the count. -/
theorem count_from_events {Aux Cert RawAux EvalAux : Type} {h : ℕ} (es : List Event) (t : QuestionId)
    (hes : es.all Event.fixedOk = true)
    (committed others : List (FElig Aux Cert RawAux EvalAux h))
    (hmap : committed.map (fun p => p.input) = es.map (fun e => e.toInput t))
    (ho : ∀ p ∈ others, (p.elig.lin && p.elig.snap) = false) :
    (receivedFaces (committed ++ others)).length = es.countP (fun e => e.vec.adm) := by
  have hc : ∀ p ∈ committed,
      p.elig.lin = true ∧ p.elig.snap = true ∧ p.elig.recv = true ∧ p.elig.record = true := by
    intro p hp
    have hmem : p.input ∈ es.map (fun e => e.toInput t) := hmap ▸ List.mem_map_of_mem hp
    obtain ⟨e, he, hei⟩ := List.mem_map.mp hmem
    have hok : e.fixedOk = true := List.all_eq_true.mp hes e he
    rw [p.elig_eq, ← hei, Event.toInput_vector]
    unfold Event.fixedOk at hok
    revert hok
    generalize e.vec.lin = a; generalize e.vec.snap = b; generalize e.vec.recv = c
    generalize e.vec.record = d
    revert a b c d; decide
  rw [(face_count committed others hc ho).1]
  have key : ∀ (cs : List (FElig Aux Cert RawAux EvalAux h)) (fs : List Event),
      cs.map (fun p => p.input) = fs.map (fun e => e.toInput t) →
      cs.countP (fun p => p.elig.adm) = fs.countP (fun e => e.vec.adm) := by
    intro cs
    induction cs with
    | nil =>
      intro fs hfs
      cases fs with
      | nil => rfl
      | cons _ _ => exact absurd hfs (by simp)
    | cons p cs ih =>
      intro fs hfs
      cases fs with
      | nil => exact absurd hfs (by simp)
      | cons e fs =>
        simp only [List.map_cons, List.cons.injEq] at hfs
        have hadm : p.elig.adm = e.vec.adm := by
          rw [p.elig_eq, hfs.1, Event.toInput_vector]
        simp only [List.countP_cons, hadm, ih fs hfs.2]
  exact key committed es hmap

/-- **The lift entry.** Every attached face built from packets carrying the
    undeclared sibling lift status carries exactly `notEvaluated`. -/
theorem prop_22_10_lift_not_evaluated {Aux Cert RawAux EvalAux : Type} {h : ℕ}
    (ps : List (FElig Aux Cert RawAux EvalAux h)) (hl : ∀ p ∈ ps, p.lift = liftStatus none) :
    ∀ f ∈ receivedFaces ps, f.packet.lift = LiftStatus.notEvaluated := by
  intro f hf
  unfold receivedFaces at hf
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
  exact hl p (List.mem_of_mem_filter hp)

/-! ## Items 1 and 2 — the unresolved questions attach nothing -/

/-- **Proposition 22.10, item 1.** `𝒬_ε` terminates on an unresolved
    occurrence pair, has no committed lineage, and by Corollary 22.9 attaches no
    face from any packet family carrying its terminal status. -/
theorem prop_22_10_root_none {Aux Cert RawAux EvalAux : Type} {h : ℕ} :
    termStatus Xeps7.active.length = TermStatus.unresolvedMultiple ∧
    terminalLin Xeps7 = [] ∧
    ∀ ps : List (FElig Aux Cert RawAux EvalAux h),
      (∀ p ∈ ps, p.input.status = termStatus Xeps7.active.length) → receivedFaces ps = [] := by
  have hs : termStatus Xeps7.active.length = TermStatus.unresolvedMultiple := by decide
  refine ⟨hs, by decide, fun ps hps => no_face_unless_singleton ps ?_⟩
  intro p hp h1
  rw [hps p hp, hs] at h1
  exact TermStatus.noConfusion h1

/-- The terminal support of `𝒬_L` is the archived sibling pair beneath `LLRRRR`
    (relative to the seed `L`). -/
def parentQL : QuestionId := ⟨0, 0, 0, [false, false, true, true, true, true]⟩
def parentQR : QuestionId := ⟨0, 0, 0, [true, true, false, false, false, false]⟩

/-- **Proposition 22.10, item 2, `𝒬_L`.** Unresolved occurrence pair, no
    lineage, no face; the pair is the two children of one parent and both
    remain in the archive. -/
theorem prop_22_10_QL_none {Aux Cert RawAux EvalAux : Type} {h : ℕ} :
    termStatus XL7.active.length = TermStatus.unresolvedMultiple ∧
    terminalLin XL7 = [] ∧
    XL7.active = [parentQL.child false, parentQL.child true] ∧
    (∀ i ∈ XL7.active, i ∈ archIds XL7.archive) ∧
    ∀ ps : List (FElig Aux Cert RawAux EvalAux h),
      (∀ p ∈ ps, p.input.status = termStatus XL7.active.length) → receivedFaces ps = [] := by
  have hs : termStatus XL7.active.length = TermStatus.unresolvedMultiple := by decide
  refine ⟨hs, by decide, by decide, XL7.active_sub_archive, fun ps hps => no_face_unless_singleton ps ?_⟩
  intro p hp h1
  rw [hps p hp, hs] at h1
  exact TermStatus.noConfusion h1

/-- **Proposition 22.10, item 2, `𝒬_R`.** -/
theorem prop_22_10_QR_none {Aux Cert RawAux EvalAux : Type} {h : ℕ} :
    termStatus XR7.active.length = TermStatus.unresolvedMultiple ∧
    terminalLin XR7 = [] ∧
    XR7.active = [parentQR.child false, parentQR.child true] ∧
    (∀ i ∈ XR7.active, i ∈ archIds XR7.archive) ∧
    ∀ ps : List (FElig Aux Cert RawAux EvalAux h),
      (∀ p ∈ ps, p.input.status = termStatus XR7.active.length) → receivedFaces ps = [] := by
  have hs : termStatus XR7.active.length = TermStatus.unresolvedMultiple := by decide
  refine ⟨hs, by decide, by decide, XR7.active_sub_archive, fun ps hps => no_face_unless_singleton ps ?_⟩
  intro p hp h1
  rw [hps p hp, hs] at h1
  exact TermStatus.noConfusion h1

/-! ## Items 3 and 4 — the side-selected root questions -/

def ids (cs : List Core) : List QuestionId := cs.map Core.id

/-- Admission at events 1..7 of `𝒬_ε^L`, before coherence selection. -/
def admSideL : List (List QuestionId) :=
  [ids (admittedCoresSide MOeps 1 seed164Prov gammaSideL props0eps),
   ids (admittedCores MOeps 2 seed164Prov propsSideL1eps),
   ids (admittedCores MOeps 3 seed164Prov propsSideL2eps),
   ids (admittedCores MOeps 4 seed164Prov propsSideL3eps),
   ids (admittedCores MOeps 5 seed164Prov propsSideL4eps),
   ids (admittedCores MOeps 6 seed164Prov propsSideL5eps),
   ids (admittedCores MOeps 7 seed164Prov propsSideL6eps)]

def linSideL : List QuestionId := terminalLin XepsSideL7
def statusSideL : TermStatus := termStatus XepsSideL7.active.length
def eventsSideL : List Event := events linSideL admSideL statusSideL

def admSideR : List (List QuestionId) :=
  [ids (admittedCoresSide MOeps 1 seed164Prov gammaSideR props0eps),
   ids (admittedCores MOeps 2 seed164Prov propsSideR1eps),
   ids (admittedCores MOeps 3 seed164Prov propsSideR2eps),
   ids (admittedCores MOeps 4 seed164Prov propsSideR3eps),
   ids (admittedCores MOeps 5 seed164Prov propsSideR4eps),
   ids (admittedCores MOeps 6 seed164Prov propsSideR5eps),
   ids (admittedCores MOeps 7 seed164Prov propsSideR6eps)]

def linSideR : List QuestionId := terminalLin XepsSideR7
def statusSideR : TermStatus := termStatus XepsSideR7.active.length
def eventsSideR : List Event := events linSideR admSideR statusSideR

/-- The lineage is the archive's own parent chain, and each member was active
    at its tick (tick 0 is `Xeps0`, the side trace's own start). -/
theorem lineage_grounded_side :
    parentsOk XepsSideL7.archive linSideL = true ∧
    activeOk [Xeps0, XepsSideL1, XepsSideL2, XepsSideL3, XepsSideL4, XepsSideL5, XepsSideL6, XepsSideL7] linSideL = true ∧
    parentsOk XepsSideR7.archive linSideR = true ∧
    activeOk [Xeps0, XepsSideR1, XepsSideR2, XepsSideR3, XepsSideR4, XepsSideR5, XepsSideR6, XepsSideR7] linSideR = true := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **Event 1 of `𝒬_ε^L`: `εR` was proposed and refused before admission.** -/
theorem sideL_event1_refused :
    seed164Id.child true ∈ props0eps.map (fun p => (childCore p.1 p.2 1 seed164Prov).id) ∧
    seed164Id.child true ∉ admSideL.head! ∧
    seed164Id.child false ∈ admSideL.head! := by
  refine ⟨by decide, by decide, by decide⟩

theorem sideR_event1_refused :
    seed164Id.child false ∈ props0eps.map (fun p => (childCore p.1 p.2 1 seed164Prov).id) ∧
    seed164Id.child false ∉ admSideR.head! ∧
    seed164Id.child true ∈ admSideR.head! := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Proposition 22.10, item 3, `𝒬_ε^L`.** Singleton terminal; committed
    lineage `(ε, L, LL, LLL, LLLR, LLLRR, LLLRRR, LLLRRRR)`; joint admission
    fails only at event 1; the other four entries are one at every event; the
    attached events are `2..7`; the hands are `(L,L,R,R,R,R)`, which is the
    terminal word with the selection hand removed; the phases are
    `(1,1,3,3,3,3)`. -/
theorem prop_22_10_sideL :
    statusSideL = TermStatus.singleton ∧
    linSideL.map QuestionId.rel =
      [[], [false], [false, false], [false, false, false], [false, false, false, true],
       [false, false, false, true, true], [false, false, false, true, true, true],
       [false, false, false, true, true, true, true]] ∧
    eventsSideL.map (fun e => e.vec.adm) = [false, true, true, true, true, true, true] ∧
    eventsSideL.all Event.fixedOk = true ∧
    attachedEvents eventsSideL = [2, 3, 4, 5, 6, 7] ∧
    attachedHands eventsSideL = [false, false, true, true, true, true] ∧
    attachedHands eventsSideL = (activeWords XepsSideL7).head!.drop 1 ∧
    attachedPhases eventsSideL = [1, 1, 3, 3, 3, 3] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Proposition 22.10, item 4, `𝒬_ε^R`**, decided independently. -/
theorem prop_22_10_sideR :
    statusSideR = TermStatus.singleton ∧
    linSideR.map QuestionId.rel =
      [[], [true], [true, true], [true, true, true], [true, true, true, false],
       [true, true, true, false, false], [true, true, true, false, false, false],
       [true, true, true, false, false, false, false]] ∧
    eventsSideR.map (fun e => e.vec.adm) = [false, true, true, true, true, true, true] ∧
    eventsSideR.all Event.fixedOk = true ∧
    attachedEvents eventsSideR = [2, 3, 4, 5, 6, 7] ∧
    attachedHands eventsSideR = [true, true, false, false, false, false] ∧
    attachedHands eventsSideR = (activeWords XepsSideR7).head!.drop 1 ∧
    attachedPhases eventsSideR = [3, 3, 1, 1, 1, 1] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Six faces each, through Theorem 22.8's packet count.** -/
theorem prop_22_10_side_counts {Aux Cert RawAux EvalAux : Type} {h : ℕ} (t : QuestionId)
    (cL oL cR oR : List (FElig Aux Cert RawAux EvalAux h))
    (hL : cL.map (fun p => p.input) = eventsSideL.map (fun e => e.toInput t))
    (hoL : ∀ p ∈ oL, (p.elig.lin && p.elig.snap) = false)
    (hR : cR.map (fun p => p.input) = eventsSideR.map (fun e => e.toInput t))
    (hoR : ∀ p ∈ oR, (p.elig.lin && p.elig.snap) = false) :
    (receivedFaces (cL ++ oL)).length = 6 ∧ (receivedFaces (cR ++ oR)).length = 6 := by
  refine ⟨?_, ?_⟩
  · rw [count_from_events eventsSideL t prop_22_10_sideL.2.2.2.1 cL oL hL hoL]; decide
  · rw [count_from_events eventsSideR t prop_22_10_sideR.2.2.2.1 cR oR hR hoR]; decide

/-! ## Items 5 and 6 — the face-bearing lone-seed questions -/

def admLL : List (List QuestionId) :=
  [ids (admittedCores MOLL 1 seed164Prov props0LL),
   ids (admittedCores MOLL 2 seed164Prov props1LL),
   ids (admittedCores MOLL 3 seed164Prov props2LL),
   ids (admittedCores MOLL 4 seed164Prov props3LL),
   ids (admittedCores MOLL 5 seed164Prov props4LL),
   ids (admittedCores MOLL 6 seed164Prov props5LL),
   ids (admittedCores MOLL 7 seed164Prov props6LL)]

def linLL : List QuestionId := terminalLin XLL7
def statusLL : TermStatus := termStatus XLL7.active.length
def eventsLL : List Event := events linLL admLL statusLL

def admRR : List (List QuestionId) :=
  [ids (admittedCores MORR 1 seed164Prov props0RR),
   ids (admittedCores MORR 2 seed164Prov props1RR),
   ids (admittedCores MORR 3 seed164Prov props2RR),
   ids (admittedCores MORR 4 seed164Prov props3RR),
   ids (admittedCores MORR 5 seed164Prov props4RR),
   ids (admittedCores MORR 6 seed164Prov props5RR),
   ids (admittedCores MORR 7 seed164Prov props6RR)]

def linRR : List QuestionId := terminalLin XRR7
def statusRR : TermStatus := termStatus XRR7.active.length
def eventsRR : List Event := events linRR admRR statusRR

theorem lineage_grounded_lone :
    parentsOk XLL7.archive linLL = true ∧
    activeOk [XLL0, XLL1, XLL2, XLL3, XLL4, XLL5, XLL6, XLL7] linLL = true ∧
    parentsOk XRR7.archive linRR = true ∧
    activeOk [XRR0, XRR1, XRR2, XRR3, XRR4, XRR5, XRR6, XRR7] linRR = true := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **Proposition 22.10, item 5, `𝒬_LL`.** Singleton terminal; both children of
    the committed parent admitted at all seven events; attached events `1..7`;
    hands `(L,R,R,R,R,R,R)`, which is the terminal word after the seed `LL`;
    phases `(1,3,3,3,3,3,3)`. -/
theorem prop_22_10_LL :
    statusLL = TermStatus.singleton ∧
    eventsLL.map (fun e => e.vec.adm) = [true, true, true, true, true, true, true] ∧
    eventsLL.all Event.fixedOk = true ∧
    attachedEvents eventsLL = [1, 2, 3, 4, 5, 6, 7] ∧
    attachedHands eventsLL = [false, true, true, true, true, true, true] ∧
    activeWords XLL7 = [[false, false] ++ attachedHands eventsLL] ∧
    attachedPhases eventsLL = [1, 3, 3, 3, 3, 3, 3] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Proposition 22.10, item 6, `𝒬_RR`**, decided independently. -/
theorem prop_22_10_RR :
    statusRR = TermStatus.singleton ∧
    eventsRR.map (fun e => e.vec.adm) = [true, true, true, true, true, true, true] ∧
    eventsRR.all Event.fixedOk = true ∧
    attachedEvents eventsRR = [1, 2, 3, 4, 5, 6, 7] ∧
    attachedHands eventsRR = [true, false, false, false, false, false, false] ∧
    activeWords XRR7 = [[true, true] ++ attachedHands eventsRR] ∧
    attachedPhases eventsRR = [3, 1, 1, 1, 1, 1, 1] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Seven faces each, through Theorem 22.8's packet count.** -/
theorem prop_22_10_lone_counts {Aux Cert RawAux EvalAux : Type} {h : ℕ} (t : QuestionId)
    (cL oL cR oR : List (FElig Aux Cert RawAux EvalAux h))
    (hL : cL.map (fun p => p.input) = eventsLL.map (fun e => e.toInput t))
    (hoL : ∀ p ∈ oL, (p.elig.lin && p.elig.snap) = false)
    (hR : cR.map (fun p => p.input) = eventsRR.map (fun e => e.toInput t))
    (hoR : ∀ p ∈ oR, (p.elig.lin && p.elig.snap) = false) :
    (receivedFaces (cL ++ oL)).length = 7 ∧ (receivedFaces (cR ++ oR)).length = 7 := by
  refine ⟨?_, ?_⟩
  · rw [count_from_events eventsLL t prop_22_10_LL.2.2.1 cL oL hL hoL]; decide
  · rw [count_from_events eventsRR t prop_22_10_RR.2.2.1 cR oR hR hoR]; decide

/-- **Theorem 22.6 at every attached event**: each attached event carries a
    committed projective face certificate at any socket target. -/
theorem attached_have_certificates (t : QuestionId) :
    ∀ e ∈ attached eventsSideL ++ attached eventsSideR ++ attached eventsLL ++ attached eventsRR,
      FaceCert (e.toInput t) := by
  intro e he
  rw [face_selection, Event.toInput_vector]
  have hall : ∀ es : List Event, ∀ e ∈ attached es, e.vec.all = true :=
    fun _ _ he => (List.mem_filter.mp he).2
  simp only [List.mem_append] at he
  rcases he with ((h1 | h2) | h3) | h4
  · exact hall _ e h1
  · exact hall _ e h2
  · exact hall _ e h3
  · exact hall _ e h4

#print axioms Event.toInput_vector
#print axioms count_from_events
#print axioms prop_22_10_lift_not_evaluated
#print axioms prop_22_10_root_none
#print axioms prop_22_10_QL_none
#print axioms prop_22_10_QR_none
#print axioms lineage_grounded_side
#print axioms sideL_event1_refused
#print axioms sideR_event1_refused
#print axioms prop_22_10_sideL
#print axioms prop_22_10_sideR
#print axioms prop_22_10_side_counts
#print axioms lineage_grounded_lone
#print axioms prop_22_10_LL
#print axioms prop_22_10_RR
#print axioms prop_22_10_lone_counts
#print axioms attached_have_certificates

end FaceRegression
end Two
end RatioSpace
