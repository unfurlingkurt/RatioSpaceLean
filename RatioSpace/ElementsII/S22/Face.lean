/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S21.Shortcut
import RatioSpace.ElementsII.S19.Return
/-!
  Elements II §22 — Temporal sibling-face selection.

  §21 produced every candidate sibling shortcut and proved none of them is an
  edge. §22 says exactly which ones become received triangular faces: those
  whose five eligibility entries all equal one (Theorem 22.6), attached by one
  construction axiom (II.2).

  **The separation the book insists on is enforced by the file, not by prose.**
  Theorem 22.6 characterizes eligibility; Construction Axiom II.2 adopts
  attachment. `receivedFaces` is declared *after* `face_selection` below, and
  Lean forbids forward references, so the selection theorem cannot depend on
  the attachment law: Separation Rule 22.12 is a fact about declaration order.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Two
namespace Face

open Mat2 Word Frame Pres RatioSpace SideExchange Advance Observer Shortcut Return Terminal

/-! ## Definition 22.1 — Candidate triangular boundary -/

/-- `e^raw_{x,s} = (ι_x → ι_{xs}; s)`. -/
structure RawEdgeRec where
  src : QuestionId
  dst : QuestionId
  hand : Bool
deriving DecidableEq

/-- `e^sib_{x,s} = (ι_{xs} → ι_{xs̄}; A_s)`, the candidate received edge. -/
structure SibEdgeRec where
  src : QuestionId
  dst : QuestionId
  mat : Mat2

/-- **Definition 22.1.** `∂Δ_{j+1}(x;s) = (e^raw_{x,s}, e^sib_{x,s}, (e^raw_{x,s̄})⁻¹)`.
    The third edge is stored as recorded and traversed backwards. A boundary
    packet, not an attached cell. -/
structure Boundary where
  raw : RawEdgeRec
  sib : SibEdgeRec
  rawBarReversed : RawEdgeRec

def boundary (x idS idBar : QuestionId) (s : Bool) : Boundary where
  raw := ⟨x, idS, s⟩
  sib := ⟨idS, idBar, A s⟩
  rawBarReversed := ⟨x, idBar, !s⟩

/-- The three edges compose into a closed loop at `ι_x`. -/
theorem boundary_is_loop (x idS idBar : QuestionId) (s : Bool) :
    (boundary x idS idBar s).raw.dst = (boundary x idS idBar s).sib.src ∧
    (boundary x idS idBar s).sib.dst = (boundary x idS idBar s).rawBarReversed.dst ∧
    (boundary x idS idBar s).rawBarReversed.src = (boundary x idS idBar s).raw.src :=
  ⟨rfl, rfl, rfl⟩

/-- `Lift_sib(x;s)` is evaluated on the complete encounter by Definition 9.15,
    and with no declared sibling lift predicate it is `notEvaluated`, which is
    not the same output as an unresolved lift. It is deliberately not a function
    of `A_s`: Theorem 9.14 shows the lift bit separates what projective data
    cannot. -/
theorem lift_sib_undeclared_and_not_projective :
    liftStatus none = LiftStatus.notEvaluated ∧
    (liftBit L L ≠ liftBit L (matNeg L) ∧ projClass (matNeg L) = projClass L) :=
  ⟨rfl, lift_separates_what_projective_cannot⟩

/-! ## Proposition 22.2 — Projective closure and central lifted holonomy -/

/-- `Ã_s^(ℓ) = (−I)^ℓ A_s`. -/
def liftedA (s ℓ : Bool) : Mat2 := cond ℓ (matNeg (A s)) (A s)

/-- **Proposition 22.2.** Around the unlifted boundary the product is `I`; on
    lift sheet `ℓ` it is `(−I)^ℓ`. Decided for both hands and both sheets. -/
theorem boundary_holonomy (s ℓ : Bool) :
    Word.gen s * A s * inv2 (Word.gen (!s)) = 1 ∧
    Word.gen s * liftedA s ℓ * inv2 (Word.gen (!s)) = cond ℓ (matNeg 1) 1 := by
  cases s <;> cases ℓ <;> exact ⟨by decide, by decide⟩

/-- **Closure in `PSL(2,ℤ)` on either sheet**: both holonomies have the
    projective class of `I`. -/
theorem boundary_projectively_closed (s ℓ : Bool) :
    projClass (Word.gen s * liftedA s ℓ * inv2 (Word.gen (!s))) = projClass 1 := by
  rw [(boundary_holonomy s ℓ).2]
  cases ℓ
  · rfl
  · exact projClass_neg 1

/-- The recorded full-matrix holonomy is read from the lift status: `I` for
    determined-0, `−I` for determined-1, and unevaluated or unresolved for
    anything else, without touching projective closure. -/
def recordedHolonomy : LiftStatus → Option Mat2
  | .determined false => some 1
  | .determined true => some (matNeg 1)
  | _ => none

theorem recordedHolonomy_matches (s ℓ : Bool) :
    recordedHolonomy (.determined ℓ) = some (Word.gen s * liftedA s ℓ * inv2 (Word.gen (!s))) := by
  rw [(boundary_holonomy s ℓ).2]; cases ℓ <;> rfl

theorem recordedHolonomy_unevaluated :
    recordedHolonomy .notEvaluated = none ∧ recordedHolonomy .unresolvedNone = none ∧
    recordedHolonomy .unresolvedMultiple = none := ⟨rfl, rfl, rfl⟩

/-! ## Definition 22.3 — Quarter-turn sibling-reception certificate -/

/-- `j_L = 1`, `j_R = 3`: an admission phase, not a tick. -/
def jPhase : Bool → Fin 4
  | false => 1
  | true => 3

/-- **Definition 22.3.** `SibRec(x;s) = (ι_{xs}, ι_{xs̄}, A_s, J_S(A_s), j_s, S^{j_s}A_s, dec₊(S^{j_s}A_s))`. -/
structure SibRec where
  idS : QuestionId
  idBar : QuestionId
  mat : Mat2
  phases : List (Fin 4)
  phase : Fin 4
  rotated : Mat2
  decoded : Option Word

def sibRec (idS idBar : QuestionId) (s : Bool) : SibRec where
  idS := idS
  idBar := idBar
  mat := A s
  phases := admittedPhases Squarter 4 (A s)
  phase := jPhase s
  rotated := matPow Squarter (jPhase s).val * A s
  decoded := dec (matPow Squarter (jPhase s).val * A s)

/-- **A finite exact certificate with one admitted phase**: `J_S(A_s) = {j_s}`,
    `S^{j_s}A_s = s`, and it decodes to the one-letter word `s`. -/
theorem sibRec_certificate (idS idBar : QuestionId) (s : Bool) :
    (sibRec idS idBar s).phases = [jPhase s] ∧
    (sibRec idS idBar s).rotated = Word.gen s ∧
    (sibRec idS idBar s).decoded = some [s] := by
  cases s <;> refine ⟨?_, ?_, ?_⟩ <;> dsimp only [sibRec] <;> decide

/-! ## Definition 22.4 — Lossless face-recording capability -/

/-- The post-cycle state as the append sees it: every operative component
    bundled in `op`, and the appendable received history `hist`. -/
structure RecState (Op Z : Type) where
  op : Op
  hist : List (QuestionId × Z)

/-- **Definition 22.4.** `FaceAppend(S_{τ+1}, Z)`: append `(ι_target, Z)` to the history. -/
def faceAppend {Op Z : Type} (st : RecState Op Z) (target : QuestionId) (z : Z) : RecState Op Z :=
  { st with hist := st.hist ++ [(target, z)] }

/-- The five conditions of losslessness. -/
structure Lossless {Op Z : Type} (st st' : RecState Op Z) (target certTarget : QuestionId) (z : Z) : Prop where
  target_eq : target = certTarget
  op_unchanged : st'.op = st.op
  prefix_kept : st.hist <+: st'.hist
  appended : st'.hist.getLast? = some (target, z)
  recoverable : ∀ {α : Type} (f : Op → α), f st'.op = f st.op

/-- **The append is lossless exactly when it writes to the certificate's own
    target**: every other condition holds by construction. -/
theorem faceAppend_lossless_iff {Op Z : Type} (st : RecState Op Z) (target certTarget : QuestionId) (z : Z) :
    Lossless st (faceAppend st target z) target certTarget z ↔ target = certTarget := by
  constructor
  · exact fun h => h.target_eq
  · intro ht
    exact ⟨ht, rfl, List.prefix_append _ _, by simp [faceAppend], fun _ => rfl⟩

/-! ## Definition 22.5 — Temporal face-eligibility packet -/

/-- `e_lin = 1 ⟺ x = x_j` in the committed lineage. -/
def eLin (lin : List QuestionId) (j : ℕ) (x : QuestionId) : Bool := decide (lin[j]? = some x)

/-- `e_adm = 1 ⟺` both children admitted at event `j+1`. -/
def eAdm (admitted : List QuestionId) (idL idR : QuestionId) : Bool :=
  decide (idL ∈ admitted) && decide (idR ∈ admitted)

/-- `e_snap = 1 ⟺ S_h = {x*}` and `xs = x_{j+1}`. -/
def eSnap (status : TermStatus) (lin : List QuestionId) (j : ℕ) (idS : QuestionId) : Bool :=
  decide (status = TermStatus.singleton) && decide (lin[j + 1]? = some idS)

/-- `e_recv = 1 ⟺ J_S(A_s) = {j_s}`. -/
def eRecv (s : Bool) : Bool := decide (admittedPhases Squarter 4 (A s) = [jPhase s])

/-- `e_record = 1 ⟺` the append is lossless, which is exactly the target test. -/
def eRecord (target certTarget : QuestionId) : Bool := decide (target = certTarget)

/-- The eligibility vector `e_{j+1}(x;s) ∈ {0,1}⁵`. -/
structure Eligibility where
  lin : Bool
  adm : Bool
  snap : Bool
  recv : Bool
  record : Bool
deriving DecidableEq

def Eligibility.all (e : Eligibility) : Bool := e.lin && e.adm && e.snap && e.recv && e.record

/-- The inputs every entry reads. -/
structure EligInput where
  lin : List QuestionId
  admitted : List QuestionId
  status : TermStatus
  target : QuestionId
  certTarget : QuestionId
  j : ℕ
  x : QuestionId
  s : Bool
  idS : QuestionId
  idBar : QuestionId

def EligInput.vector (i : EligInput) : Eligibility where
  lin := eLin i.lin i.j i.x
  adm := eAdm i.admitted (cond i.s i.idBar i.idS) (cond i.s i.idS i.idBar)
  snap := eSnap i.status i.lin i.j i.idS
  recv := eRecv i.s
  record := eRecord i.target i.certTarget

/-- **Definition 22.5, the complete packet** `FElig_{j+1}(x;s)`. -/
structure FElig (Aux Cert RawAux EvalAux : Type) (h : ℕ) where
  input : EligInput
  shortcut : OrientedShortcut Aux Cert
  bdry : Boundary
  sib : SibRec
  lift : LiftStatus
  cycle : CycleCertificate RawAux EvalAux h
  elig : Eligibility
  elig_eq : elig = input.vector

/-- The sibling-reception entry is always one: Proposition 10.7 for both hands. -/
theorem eRecv_true (s : Bool) : eRecv s = true := by cases s <;> decide

/-! ## Theorem 22.6 — Temporal face-selection theorem -/

/-- **A well-typed committed projective face certificate**: the five facts a
    face rule needs, as propositions. -/
structure FaceCert (i : EligInput) : Prop where
  parent_on_lineage : i.lin[i.j]? = some i.x
  jointly_admitted : cond i.s i.idBar i.idS ∈ i.admitted ∧ cond i.s i.idS i.idBar ∈ i.admitted
  committed : i.status = TermStatus.singleton ∧ i.lin[i.j + 1]? = some i.idS
  received : admittedPhases Squarter 4 (A i.s) = [jPhase i.s]
  recorded : i.target = i.certTarget

/-- **Theorem 22.6.** A candidate supports a committed projective face
    certificate if and only if all five entries equal one. -/
theorem face_selection (i : EligInput) : FaceCert i ↔ i.vector.all = true := by
  simp only [EligInput.vector, Eligibility.all, eLin, eAdm, eSnap, eRecv, eRecord,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩

/-- **Theorem 22.6, uniqueness.** When it exists the certificate is unique, and
    so is every component it names: the lineage entry, the one admitted phase,
    and the sibling of a well-formed parent's designated child. -/
theorem face_certificate_unique (i : EligInput) (c c' : FaceCert i) : c = c' := rfl

theorem face_components_unique (c : Core) (hc : c.WellFormed) (s : Bool) (e : ℕ) (pv : Provenance) :
    (∀ k ∈ admittedPhases Squarter 4 (A s), k = jPhase s) ∧
    (childCore c (!s) e pv).id = c.id.child (!s) ∧
    (∀ (lin : List QuestionId) (j : ℕ) (x x' : QuestionId),
        lin[j]? = some x → lin[j]? = some x' → x = x') := by
  refine ⟨?_, childCore_id c hc (!s) e pv, ?_⟩
  · intro k hk
    have := (sibRec_certificate c.id c.id s).1
    simp only [sibRec] at this
    rw [this] at hk
    simpa using hk
  · intro lin j x x' h h'
    rw [h] at h'; exact Option.some.inj h'

/-! ## Construction Axiom II.2 — Attachment of eligible committed sibling faces

    Declared *after* Theorem 22.6: the selection theorem cannot reference it. -/

/-- A received projective triadic face: the eligibility packet it came from,
    retained whole. `Face` attaches; it does not identify or delete the three
    occurrence histories on the boundary, and it does not choose a lift. -/
structure ReceivedFace (Aux Cert RawAux EvalAux : Type) (h : ℕ) where
  packet : FElig Aux Cert RawAux EvalAux h

def attach {Aux Cert RawAux EvalAux : Type} {h : ℕ} (p : FElig Aux Cert RawAux EvalAux h) :
    ReceivedFace Aux Cert RawAux EvalAux h := ⟨p⟩

/-- **Construction Axiom II.2.** `F^recv_{τ+1} = {Face(FElig) : e = (1,1,1,1,1)}`. -/
def receivedFaces {Aux Cert RawAux EvalAux : Type} {h : ℕ} (ps : List (FElig Aux Cert RawAux EvalAux h)) :
    List (ReceivedFace Aux Cert RawAux EvalAux h) :=
  (ps.filter (fun p => p.elig.all)).map attach

/-- Every eligible packet is attached, and no ineligible one. -/
theorem attached_iff {Aux Cert RawAux EvalAux : Type} {h : ℕ} (ps : List (FElig Aux Cert RawAux EvalAux h))
    (p : FElig Aux Cert RawAux EvalAux h) (hp : p ∈ ps) :
    attach p ∈ receivedFaces ps ↔ p.elig.all = true := by
  unfold receivedFaces
  constructor
  · intro hm
    obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hm
    have : q = p := by cases q; cases p; simp only [attach, ReceivedFace.mk.injEq] at hqp; exact hqp
    subst this
    exact (List.mem_filter.mp hq).2
  · intro ha
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hp, ha⟩)

/-- The face retains its lift status exactly, whatever it is. -/
theorem attach_retains {Aux Cert RawAux EvalAux : Type} {h : ℕ} (p : FElig Aux Cert RawAux EvalAux h) :
    (attach p).packet = p ∧ (attach p).packet.lift = p.lift := ⟨rfl, rfl⟩

/-! ## Corollary 22.7 — Universal sibling emission at the choice event -/

/-- **Corollary 22.7.** `Q_s(ε) = A_s`, independent of prefix and event;
    `Q_s̄(ε) = Q_s(ε)⁻¹`; `𝖯Q_s(ε)𝖯 = Q_s̄(ε)`; phases `1` and `3`. -/
theorem universal_emission (c : Core) (s : Bool) (entry : ℕ) (prov : Provenance) :
    Q (childCore c s entry prov).fullMatrix (childCore c (!s) entry prov).fullMatrix = A s ∧
    A (!s) = inv2 (A s) ∧
    SideExchange.P * A s * SideExchange.P = A (!s) ∧
    admittedPhases Squarter 4 (A false) = [jPhase false] ∧
    admittedPhases Squarter 4 (A true) = [jPhase true] :=
  ⟨shortcut_matrix c s entry prov, (side_exchange_shortcut_matrix s).2,
    (side_exchange_shortcut_matrix s).1, J_S_AL, J_S_AR⟩

/-! ## Theorem 22.8 — Exact attached-face count on the compatible singleton domain -/

/-- `List.filter_eq_nil_iff` carries `Classical.choice`; this direction does not. -/
theorem filter_eq_nil_of {α : Type} (f : α → Bool) :
    ∀ l : List α, (∀ p ∈ l, f p = false) → l.filter f = []
  | [], _ => rfl
  | a :: l, hl => by
    have ha : f a = false := hl a (List.Mem.head l)
    simp only [List.filter, ha]
    exact filter_eq_nil_of f l (fun p hp => hl p (List.Mem.tail a hp))

/-- **Theorem 22.8.** On the compatible singleton domain, one committed packet per
    lineage event has its lineage, snap, reception and recording entries equal to
    one, and every other candidate fails lineage or snap. Then the attached faces
    number exactly the events with both children admitted, and at most `h`. -/
theorem face_count {Aux Cert RawAux EvalAux : Type} {h : ℕ}
    (committed others : List (FElig Aux Cert RawAux EvalAux h))
    (hc : ∀ p ∈ committed, p.elig.lin = true ∧ p.elig.snap = true ∧ p.elig.recv = true ∧ p.elig.record = true)
    (ho : ∀ p ∈ others, (p.elig.lin && p.elig.snap) = false) :
    (receivedFaces (committed ++ others)).length = committed.countP (fun p => p.elig.adm) ∧
    (receivedFaces (committed ++ others)).length ≤ committed.length := by
  have hothers : others.filter (fun p => p.elig.all) = [] := by
    apply filter_eq_nil_of
    intro p hp
    have hls := ho p hp
    unfold Eligibility.all
    revert hls
    generalize p.elig.lin = a; generalize p.elig.adm = b; generalize p.elig.snap = c
    generalize p.elig.recv = d; generalize p.elig.record = e
    revert a b c d e; decide
  have hcomm : committed.filter (fun p => p.elig.all) = committed.filter (fun p => p.elig.adm) := by
    apply List.filter_congr
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hc p hp
    unfold Eligibility.all
    rw [h1, h2, h3, h4]
    generalize p.elig.adm = b
    revert b; decide
  have hlen : (receivedFaces (committed ++ others)).length = committed.countP (fun p => p.elig.adm) := by
    unfold receivedFaces
    rw [List.length_map, List.filter_append, hothers, List.append_nil, hcomm, List.countP_eq_length_filter]
  exact ⟨hlen, hlen ▸ List.countP_le_length⟩

/-! ## Corollary 22.9 — Empty and unresolved cycles have an empty attached-face family -/

theorem eSnap_false_of_not_singleton {status : TermStatus} (hs : status ≠ TermStatus.singleton)
    (lin : List QuestionId) (j : ℕ) (idS : QuestionId) : eSnap status lin j idS = false := by
  unfold eSnap; rw [decide_eq_false hs, Bool.false_and]

/-- **Corollary 22.9.** If the terminal report is not an occurrence singleton, no
    packet is eligible and no face is attached. -/
theorem no_face_unless_singleton {Aux Cert RawAux EvalAux : Type} {h : ℕ}
    (ps : List (FElig Aux Cert RawAux EvalAux h))
    (hs : ∀ p ∈ ps, p.input.status ≠ TermStatus.singleton) :
    receivedFaces ps = [] := by
  unfold receivedFaces
  rw [List.map_eq_nil_iff]
  apply filter_eq_nil_of
  intro p hp
  rw [p.elig_eq]
  change (eLin p.input.lin p.input.j p.input.x && eAdm p.input.admitted _ _ &&
      eSnap p.input.status p.input.lin p.input.j p.input.idS && eRecv p.input.s &&
      eRecord p.input.target p.input.certTarget) = false
  rw [eSnap_false_of_not_singleton (hs p hp)]
  generalize eLin p.input.lin p.input.j p.input.x = a
  generalize eAdm p.input.admitted _ _ = b
  generalize eRecv p.input.s = d
  generalize eRecord p.input.target p.input.certTarget = e
  revert a b d e; decide

/-! ## Theorem 22.11 — Prefix and side covariance of face selection -/

/-- `decide` respects `↔`, through the `Decidable` instances alone. -/
theorem dec_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q :=
  if hp : p then by rw [decide_eq_true hp, decide_eq_true (h.mp hp)]
  else by rw [decide_eq_false hp, decide_eq_false (fun hq => hp (h.mpr hq))]


/-- **Theorem 22.11.** Any injective relabeling of stable identifiers, which is
    what prefix transport and side exchange both are on identifiers, preserves
    the lineage, admission, snap and recording entries occurrence for
    occurrence. The reception entry is one on both hands, and the side exchange
    swaps phases `1` and `3`. -/
theorem eligibility_covariant (σ : QuestionId → QuestionId) (hσ : Function.Injective σ)
    (lin admitted : List QuestionId) (status : TermStatus) (j : ℕ) (x idL idR idS t t' : QuestionId) :
    eLin (lin.map σ) j (σ x) = eLin lin j x ∧
    eAdm (admitted.map σ) (σ idL) (σ idR) = eAdm admitted idL idR ∧
    eSnap status (lin.map σ) j (σ idS) = eSnap status lin j idS ∧
    eRecord (σ t) (σ t') = eRecord t t' := by
  have hopt : ∀ (k : ℕ) (y : QuestionId), ((lin.map σ)[k]? = some (σ y)) ↔ (lin[k]? = some y) := by
    intro k y
    rw [List.getElem?_map]
    constructor
    · intro hm
      cases hl : lin[k]? with
      | none => simp [hl] at hm
      | some z => simp only [hl, Option.map_some, Option.some.injEq] at hm; rw [hσ hm]
    · intro hm; simp [hm]
  have hmem : ∀ y, σ y ∈ admitted.map σ ↔ y ∈ admitted := fun y => by
    constructor
    · intro hm; obtain ⟨z, hz, hzy⟩ := List.mem_map.mp hm; rwa [← hσ hzy]
    · exact List.mem_map_of_mem
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [eLin]; exact dec_congr (hopt j x)
  · simp only [eAdm]; rw [dec_congr (hmem idL), dec_congr (hmem idR)]
  · simp only [eSnap]; rw [dec_congr (hopt (j + 1) idS)]
  · simp only [eRecord]; exact dec_congr ⟨fun h => hσ h, fun h => h ▸ rfl⟩

theorem side_exchange_phases_and_holonomy :
    jPhase (!false) = 3 ∧ jPhase (!true) = 1 ∧ eRecv true = eRecv false ∧
    SideExchange.P * matNeg 1 * SideExchange.P = matNeg 1 :=
  ⟨rfl, rfl, by decide, by decide⟩

/-! ## Separation Rule 22.12 — Eligibility is proved; attachment is adopted

    `face_selection` (Theorem 22.6) is a theorem about `EligInput.vector` and
    `FaceCert`. `receivedFaces` (Construction Axiom II.2) is a definition
    declared after it. Lean does not permit forward references, so the theorem
    cannot use the attachment law, and nothing about matrix closure is used to
    disguise attachment as a consequence. -/

#print axioms boundary_is_loop
#print axioms lift_sib_undeclared_and_not_projective
#print axioms boundary_holonomy
#print axioms boundary_projectively_closed
#print axioms recordedHolonomy_matches
#print axioms sibRec_certificate
#print axioms faceAppend_lossless_iff
#print axioms eRecv_true
#print axioms face_selection
#print axioms face_certificate_unique
#print axioms face_components_unique
#print axioms attached_iff
#print axioms attach_retains
#print axioms universal_emission
#print axioms face_count
#print axioms no_face_unless_singleton
#print axioms eligibility_covariant
#print axioms side_exchange_phases_and_holonomy

end Face
end Two
end RatioSpace
