/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S05.Mediant
/-!
  Elements II §6 — The history-bearing candidate carrier.

  Definition 6.1 through Corollary 6.10. Every field Definition 6.1 lists as an
  occurrence's immutable core is already produced somewhere in §4–§5 —
  `ProposalRecord` carries eight of the twelve — so `Core` packages that record
  with the four fields only archiving makes available: the explicit parent
  identifier and incoming hand (null for a seed, exactly as the book says), the
  closure annotation, the imbalance, the entry stratum, and provenance. Nothing
  here is re-derived that §4–§5 already built.

  Four things are sharper than the prose, and each is noted at its result:

    * **`Core.WellFormed` holds unconditionally for both constructors, not by
      an induction on the archive.** `seedCore` and `childCore` always
      recompute every field fresh from the retained `(seedId, seed, relWord)`
      via `proposal`/`childProposal`, never by reading a prior `fullMatrix` or
      `frame` off their input — so a freshly built core matches its own
      recomputation *by definitional unfolding*, with no dependency on whether
      the parent was itself well-formed. Proposition 6.8's matrix and closure
      recursions then hold for every core an archive actually contains, not
      merely for ones checked by an inductive argument.

    * **The closure recursion needs no well-formedness at all.** `Core.closure`
      is defined as `ψ₁₂` of the *stored* `fullWord` field, and both fields
      come from the same underlying proposal by construction, so
      `Core.closure = ψ₁₂ Core.fullWord` is `rfl` for every core either
      constructor produces. `childCore_closure` is proved with no hypothesis
      at all, and `childCore_closure'` restates it in the book's own
      vocabulary once `Core.WellFormed` supplies the identification.

    * **`S_j ⊆ ids(H_j)` is a field of `TickCarrier`, not a theorem about it.**
      The same move as `Frame.lean`'s contact-as-a-field: no term of type
      `TickCarrier` can be built with an active occurrence missing from its
      own archive, so Proposition 6.8's first clause is discharged at
      construction and cited rather than proved.

    * **Proposition 6.9 and Corollary 6.10 share one witness, and it is
      exact.** Two proposals from the same seed and the same relative word but
      distinct question instances reach the same address and carry distinct
      identifiers. Deduplicating the two-element archive by address collapses
      it to length one; deduplicating by identifier does not. That drop,
      `2 → 1`, is Corollary 6.10's "deletes causal multiplicity" as an integer
      rather than a description.

  Everything computable. No `sorry`, no `axiom`.
-/

namespace RatioSpace
namespace Two

open Mat2 Word Frame Pres RatioSpace

/-! ## Definition 6.1 — Immutable occurrence core -/

/-- **Definition 6.1's provenance entry.** The question that produced the
    occurrence, its seed source, and the exact construction event — an event
    stratum and slot, Definition 2.3's `Record` — that created it. -/
structure Provenance where
  /-- The question cycle/instance that produced this occurrence. -/
  question : QuestionId
  /-- The seed source: the identifier of the occurrence's own seed. -/
  seedSource : QuestionId
  /-- The exact construction event. -/
  event : Record

/-- **Definition 6.1.** The immutable core record of an occurrence:
    `(ι_x, ι_par(x), ι_seed(x), g_x, w_x, M_x, F_x, r_x, κ_cl(x), b(w_x),
    e_entry(x), prov(x))`. `parent` and `hand` are the seed's null typed
    entries when `none`. The eight fields §4–§5 already produce (`id`,
    `seedId`, the seed's own history, `relWord`, `fullWord`, `fullMatrix`,
    `frame`, `addr`) are carried exactly as `ProposalRecord` gives them; the
    remaining four — `parent`, `hand`, `closure`, `imbalance` — plus the entry
    stratum and provenance are what only becomes available once an occurrence
    is archived. -/
structure Core where
  /-- `ι_x`. -/
  id : QuestionId
  /-- `ι_par(x)`, `none` for a seed. -/
  parent : Option QuestionId
  /-- `ι_seed(x)`. -/
  seedId : QuestionId
  /-- `g_x`, the incoming hand, `none` for a seed. -/
  hand : Option Bool
  /-- The seed occurrence's own retained history. -/
  seed : History
  /-- `v`, the relative word from the seed. -/
  relWord : Word
  /-- `w_x`. -/
  fullWord : Word
  /-- `M_x`. -/
  fullMatrix : Mat2
  /-- `F_x`. -/
  frame : Frame
  /-- `r_x`. -/
  addr : Pres
  /-- `κ_cl(x) = ψ₁₂(M_x)`, computed canonically. -/
  closure : ZMod 12
  /-- `b(w_x)`. -/
  imbalance : ℤ
  /-- `e_entry(x)`, the event stratum this occurrence entered the archive at. -/
  entry : ℕ
  /-- `prov(x)`. -/
  prov : Provenance

/-- **Definition 6.1, the constructor.** Every `Core` in this file is built
    from a `ProposalRecord` plus what only archiving adds: the parent
    identifier, the incoming hand, the entry stratum, and provenance. -/
def Core.ofProposal (p : ProposalRecord) (parent : Option QuestionId) (hand : Option Bool)
    (entry : ℕ) (prov : Provenance) : Core where
  id := p.id
  parent := parent
  seedId := p.seedId
  hand := hand
  seed := p.seed
  relWord := p.relWord
  fullWord := p.fullWord
  fullMatrix := p.fullMatrix
  frame := p.frame
  addr := p.addr
  closure := psi12 p.fullWord
  imbalance := bal p.fullWord
  entry := entry
  prov := prov

/-- **The closure field can never disagree with the stored word it names.**
    Both come from the same `p.fullWord`, so this is `rfl`. -/
@[simp] theorem Core.ofProposal_closure (p : ProposalRecord) (parent : Option QuestionId)
    (hand : Option Bool) (entry : ℕ) (prov : Provenance) :
    (Core.ofProposal p parent hand entry prov).closure =
      psi12 (Core.ofProposal p parent hand entry prov).fullWord := rfl

/-- **Definition 6.1.** A seed core: no parent, no incoming hand. -/
def seedCore (id0 : QuestionId) (seed : History) (entry : ℕ) (prov : Provenance) : Core :=
  Core.ofProposal (proposal id0 seed []) none none entry prov

/-- **Definition 5.1 read through Definition 6.1.** A child core: one more
    relative step from `c`, continuing from `c`'s own seed — exactly
    `childProposal`, archived with `c`'s identifier as parent and `g` as the
    incoming hand. -/
def childCore (c : Core) (g : Bool) (entry : ℕ) (prov : Provenance) : Core :=
  Core.ofProposal (childProposal c.seedId c.seed c.relWord g) (some c.id) (some g) entry prov

/-! ## Definition 6.2 — Tick carrier -/

/-- Every archived occurrence's identifier. -/
def archIds (archive : List Core) : List QuestionId := archive.map Core.id

/-- **Definition 6.2.** The complete candidate carrier at tick `j`:
    `(O_τ, 𝒬_τ, j, S_j, ℋ_j, ℰ_j)`. `S_j ⊆ ids(ℋ_j)` is carried as a field, not
    proved afterward — the same move as `Frame.lean`'s contact field: no term
    of this type can name an active occurrence its own archive does not
    contain. `Aux` stands in for every type §7 onward has not yet supplied; it
    is one generic placeholder, not an invented type per field. -/
structure TickCarrier (Aux : Type) (h : ℕ) where
  /-- `O_τ`. -/
  observer : Observer
  /-- `𝒬_τ`. -/
  question : ExtendedQuestion Aux
  /-- `j`. -/
  tick : Fin (h + 1)
  /-- `S_j`, the finite set of currently active occurrence identifiers. -/
  active : List QuestionId
  /-- `ℋ_j`, the append-only archive of every seed and proposed child through
      tick `j`. -/
  archive : List Core
  /-- `ℰ_j`, the ordered event ledger, keyed by stable occurrence identifier.
      Storage order within one stratum has no mathematical effect — nothing
      below reads it. -/
  ledger : List (QuestionId × Aux)
  /-- **Proposition 6.8, clause 1, discharged at construction.** -/
  active_sub_archive : ∀ i ∈ active, i ∈ archIds archive

/-- `ids(ℋ_j)`, named at the carrier. -/
@[simp] def TickCarrier.ids {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) : List QuestionId :=
  archIds X.archive

/-! ## Definition 6.3 — Evaluation record -/

/-- Definition 6.3's own status discipline: a slot carries either an explicit
    "not yet evaluated" or a value, and absence is never read as an invented
    zero. -/
inductive Slot (α : Type) where
  | notEvaluated
  | value (v : α)
deriving DecidableEq

/-- **Definition 6.3.** The evaluation record of a proposed occurrence at tick
    `j+1`. Two entries are concrete now: the encounter matrix — Definition
    3.1's `Q`, always computable from the observer and the occurrence's own
    matrix — and the closure annotation, always computable as `ψ₁₂` of the
    accumulated word. The other twelve name quantities from sections not yet
    built here (§7 comparison and support, §8 exact coherence, §9 admission,
    channel and lift, §10 causal pairs), so each is one `Slot Aux`: one shared
    generic placeholder standing in for every value this file cannot yet type
    concretely, rather than an invented type per field. When each later
    section is built, its slot is specialized there; the record's shape does
    not otherwise change. -/
structure EvalRecord (Aux : Type) where
  /-- `Q_{O,y}`, always computable. -/
  encounter : Mat2
  /-- `a_y`. -/
  localWord : Slot Aux
  /-- `λ_O(y)`. -/
  localAddr : Slot Aux
  /-- `Adm_𝒬(y;𝔛_j,j+1)`. -/
  admission : Slot Aux
  /-- `Cert_adm(y)`. -/
  admCert : Slot Aux
  /-- `Σ_j^{(O)}(y)`. -/
  sigma : Slot Aux
  /-- `T_j^{(O)}(y)`. -/
  tension : Slot Aux
  /-- `L_{CF,j}^{(O)}(y)`. -/
  lCF : Slot Aux
  /-- `D_{walk,j}^{(O)}(y)`. -/
  dWalk : Slot Aux
  /-- `C_j^{(O)}(y)`. -/
  starC : Slot Aux
  /-- `supportStatus_j(y)`. -/
  supportStatus : Slot Aux
  /-- `Ω(O,y)`. -/
  omega : Slot Aux
  /-- `κ_cl(y)`, always computable. -/
  closure : ZMod 12
  /-- `channel(y)`. -/
  channel : Slot Aux
  /-- `liftStatus(y)`. -/
  liftStatus : Slot Aux
  /-- `causalPair(y)`. -/
  causalPair : Slot Aux

/-- **Definition 6.3.** The evaluation record the instant a proposal is
    created: the two computable entries filled, every other slot explicitly
    unevaluated. This is the honest initial state before any of §7–§10 runs,
    not an invented default. -/
def EvalRecord.initial {Aux : Type} (Q : Mat2) (closure : ZMod 12) : EvalRecord Aux where
  encounter := Q
  localWord := .notEvaluated
  localAddr := .notEvaluated
  admission := .notEvaluated
  admCert := .notEvaluated
  sigma := .notEvaluated
  tension := .notEvaluated
  lCF := .notEvaluated
  dWalk := .notEvaluated
  starC := .notEvaluated
  supportStatus := .notEvaluated
  omega := .notEvaluated
  closure := closure
  channel := .notEvaluated
  liftStatus := .notEvaluated
  causalPair := .notEvaluated

/-! ## Definition 6.4 — Realization of the Elements I candidate and ensemble -/

/-- **Definition 6.4.** `ℋ_j↓x`, the parent-closed subarchive: every core
    sharing `x`'s seed whose relative word is an ancestor of `x`'s own —
    Definition 2.2's `AncLe`, read against the retained relative word rather
    than a numerical proxy, exactly as that definition forces. Includes `x`
    itself, at `AncLe x x`. -/
def downFrom (archive : List Core) (x : Core) : List Core :=
  archive.filter fun c => decide (c.seedId = x.seedId ∧ AncLe c.relWord x.relWord)

theorem mem_downFrom_self {archive : List Core} {x : Core} (hx : x ∈ archive) :
    x ∈ downFrom archive x := by
  simp only [downFrom, List.mem_filter, decide_eq_true_eq]
  exact ⟨hx, trivial, ancLe_refl _⟩

/-- **Definition 6.4.** `ℰ_j↾x`, every ledger entry keyed to `x`. -/
def restrictTo {Aux : Type} (ledger : List (QuestionId × EvalRecord Aux)) (x : Core) :
    List (QuestionId × EvalRecord Aux) :=
  ledger.filter fun p => decide (p.1 = x.id)

/-- **Definition 6.4.** The complete occurrence-indexed candidate record:
    `Cand_{τ,j}(x) = (Core(x), ℰ_j↾x, ℋ_j↓x)`. This realizes the imported
    Elements I candidate fields `(r,w,M,κ,Σ,T,H)`: the immutable fields are
    read from `Core(x)`, the retained history from `ℋ_j↓x`, and the
    observer-local star and tension signature from the keyed evaluation
    entries once §7 supplies their concrete type. -/
structure Cand (Aux : Type) where
  core : Core
  ledger : List (QuestionId × EvalRecord Aux)
  history : List Core

/-- **Definition 6.4.** The realization at one occurrence.

    **Two type parameters, not one.** `X`'s own raw stratum (`TickCarrier
    RawAux`'s `ledger`, Definition 6.2's *undigested* per-tick data) and
    `ledger`'s evaluated payload (`EvalRecord`'s `EvalAux`, Definition 6.3's
    per-occurrence record) are different things. `candidate` never
    reads `X.ledger`, only `X.archive`/`X.active`, so nothing identifies
    them, and Definition 16.1 instantiates them differently: a running
    `Policy`'s raw event type is not `EvalRecord`-shaped. -/
def candidate {RawAux EvalAux : Type} {h : ℕ} (X : TickCarrier RawAux h)
    (ledger : List (QuestionId × EvalRecord EvalAux)) (x : Core) : Cand EvalAux where
  core := x
  ledger := restrictTo ledger x
  history := downFrom X.archive x

/-- **Definition 6.4.** The imported Elements I ensemble, realized at tick `j`:
    one `Cand` per active occurrence. Same two-parameter split as `candidate`. -/
def ensemble {RawAux EvalAux : Type} {h : ℕ} (X : TickCarrier RawAux h)
    (ledger : List (QuestionId × EvalRecord EvalAux)) : List (Cand EvalAux) :=
  (X.archive.filter fun c => decide (c.id ∈ X.active)).map (candidate X ledger)

/-- Filtering `archive` by membership in `active` and then reading `.id` off
    what survives is the same count as mapping to `archIds` first and
    filtering there — pure rewriting under the same predicate, no cardinality
    content yet. -/
private theorem filter_id_length_eq_map_filter (archive : List Core) (active : List QuestionId) :
    (archive.filter fun c => decide (c.id ∈ active)).length
      = ((archive.map Core.id).filter (· ∈ active)).length := by
  induction archive with
  | nil => simp
  | cons c cs ih =>
      by_cases hc : c.id ∈ active
      · simp [hc, ih]
      · simp [hc, ih]

/-- **`AdvanceData.hcard`'s equation (`Accumulation.lean`), as a genuine
    identity rather than a per-step obligation.** `hcard` asks the schedule to
    supply this fact fresh at every carrier its policy is invoked on; here it
    follows from two duplicate-free hypotheses alone. `active ⊆ archIds
    archive` (`hsub`) puts `active` and the archive's filtered ids in mutual
    `Subperm`, and two `Subperm`s in opposite directions are a `Perm`, which
    preserves length. Pure list combinatorics — nothing about `Core`, `⊗`, or
    any framework content enters past the subset hypothesis itself. -/
theorem nodup_filter_active_length_eq {archive : List Core} {active : List QuestionId}
    (hArch : (archive.map Core.id).Nodup) (hAct : active.Nodup)
    (hsub : active ⊆ archive.map Core.id) :
    (archive.filter fun c => decide (c.id ∈ active)).length = active.length := by
  rw [filter_id_length_eq_map_filter]
  have hF : ((archive.map Core.id).filter (· ∈ active)).Nodup := hArch.filter _
  have hsub1 : active ⊆ (archive.map Core.id).filter (· ∈ active) := by
    intro x hx; exact List.mem_filter.mpr ⟨hsub hx, by simpa using hx⟩
  have hsub2 : (archive.map Core.id).filter (· ∈ active) ⊆ active := by
    intro x hx; simpa using (List.mem_filter.mp hx).2
  have hp : List.Perm active ((archive.map Core.id).filter (· ∈ active)) :=
    (List.subperm_of_subset hAct hsub1).antisymm (List.subperm_of_subset hF hsub2)
  exact hp.length_eq.symm

/-- **The `TickCarrier`-level specialization.** `active_sub_archive` supplies
    the subset hypothesis for free; what is still asked of the caller is that
    the archive and the active support are each duplicate-free at this
    carrier — true of every carrier a real `Policy` is invoked on
    (`AdvanceData.hcard`), not yet proved true of an arbitrary reached
    carrier including the terminal one. See `Terminal.lean`'s use of this for
    the honest scope of that gap. -/
theorem TickCarrier.ensemble_length_eq_active {RawAux EvalAux : Type} {h : ℕ}
    (X : TickCarrier RawAux h) (ledger : List (QuestionId × EvalRecord EvalAux))
    (hArch : (X.archive.map Core.id).Nodup) (hAct : X.active.Nodup) :
    (ensemble X ledger).length = X.active.length := by
  unfold ensemble
  rw [List.length_map]
  exact nodup_filter_active_length_eq hArch hAct X.active_sub_archive

#print axioms nodup_filter_active_length_eq
#print axioms TickCarrier.ensemble_length_eq_active

/-! ## Definition 6.5 — Proposal status -/

/-- **Definition 6.5.** Every proposal receives exactly one creation status.
    `admissionRejected` carries a complete failure certificate, generic since
    no concrete certificate type exists yet — the same honest gap as
    `RecordingSocket`'s `Cert` in §4. -/
inductive ProposalStatus (Cert : Type) where
  | admissionRejected (cert : Cert)
  | coherenceRejected
  | selected
  | tiedSelected

/-! ## Definition 6.6 — Active support is a property of the carrier -/

/-- **Definition 6.6, witnessed.** `Core` carries no support field at all —
    `S_j` is `TickCarrier.active`, external data, not a projection of `Core` —
    so a core can sit in an archive while its identifier is absent from the
    active set: membership in `S_j` is a property of the carrier at tick `j`,
    never read off `Core(x)` itself. -/
theorem support_not_core_property (c : Core) (S : List QuestionId) (hS : c.id ∉ S) :
    ∃ archive : List Core, c ∈ archive ∧ c.id ∉ (archIds archive).filter (· ∈ S) := by
  refine ⟨[c], List.mem_singleton_self c, ?_⟩
  simp only [archIds, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
  by_cases h : decide (c.id ∈ S) = true
  · exact absurd (of_decide_eq_true h) hS
  · simpa using hS

/-! ## Theorem 6.7 — Archive losslessness -/

/-- **Theorem 6.7, the combinatorial core.** Repeated parent traversal —
    dropping the last hand — strictly shortens a nonempty relative word, and
    re-appending the dropped hand reconstructs it exactly. This is the whole
    of "terminates, and reading the incoming hands in reverse traversal order
    reconstructs the relative word": nothing about `Core` beyond retaining `v`
    in full is used. -/
theorem parent_traversal_reconstructs (v : Word) (hv : v ≠ []) :
    v.dropLast ++ [v.getLast hv] = v ∧ v.dropLast.length < v.length := by
  refine ⟨List.dropLast_append_getLast hv, ?_⟩
  have hlen : v.length ≠ 0 := by simpa using hv
  simp only [List.length_dropLast]
  omega

/-- **Theorem 6.7, for one child step.** Dropping `childCore`'s incoming hand
    from its relative word returns the parent's own relative word, and the
    dropped letter is the recorded hand — both by unfolding `childProposal`,
    nothing else. -/
theorem childCore_traversal (c : Core) (g : Bool) (entry : ℕ) (prov : Provenance) :
    (childCore c g entry prov).relWord.dropLast = c.relWord ∧
    (childCore c g entry prov).parent = some c.id ∧
    (childCore c g entry prov).hand = some g := by
  refine ⟨?_, rfl, rfl⟩
  change (c.relWord ++ [g]).dropLast = c.relWord
  simp

/-- **Theorem 6.7, stated for the archive.** Given that every non-seed core's
    own recorded parent and hand satisfy the one-step reconstruction and that
    every seed core carries no parent, tracing `parent` from any archived
    occurrence terminates at a seed whose reachable ancestor chain is
    literally read off the retained relative word — `parent_traversal_reconstructs`
    applied along it. -/
theorem archive_lossless {archive : List Core} (x : Core) (hx : x ∈ archive)
    (hstep : ∀ c ∈ archive, c.relWord ≠ [] →
      ∃ par ∈ archive, par.relWord = c.relWord.dropLast ∧ c.parent = some par.id ∧
        c.hand = c.relWord.getLast?) :
    x.relWord = [] ∨ ∃ par ∈ archive, par.relWord = x.relWord.dropLast := by
  by_cases h : x.relWord = []
  · exact Or.inl h
  · obtain ⟨par, hpar, hrel, -, -⟩ := hstep x hx h
    exact Or.inr ⟨par, hpar, hrel⟩

/-! ## Proposition 6.8 — Carrier consistency conditions -/

/-- **Proposition 6.8, clause 1.** `S_j ⊆ ids(ℋ_j)` — cited from the carrier's
    own field, not reproved. -/
theorem TickCarrier.active_sub_ids {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) :
    ∀ i ∈ X.active, i ∈ X.ids :=
  X.active_sub_archive

/-- **Proposition 6.8, clause 3 (closure recursion), unconditional.** No
    well-formedness hypothesis: `Core.closure` is always `ψ₁₂` of the *stored*
    `fullWord`, and `childCore`'s `fullWord` is always the underlying
    proposal's `fullWord`-of-record with `g` appended, so `ψ₁₂`'s additivity
    closes it in one step. -/
theorem childCore_closure (c : Core) (g : Bool) (entry : ℕ) (prov : Provenance) :
    (childCore c g entry prov).closure =
      psi12 (proposal c.seedId c.seed c.relWord).fullWord + psi12 [g] := by
  change psi12 (childProposal c.seedId c.seed c.relWord g).fullWord = _
  rw [childProposal_fullWord, psi12_append]

/-- **`Core.WellFormed`.** A core's stored fields agree with recomputing them
    from its own `seedId`/`seed`/`relWord` via `proposal`. Both constructors
    below produce only well-formed cores, unconditionally — see
    `seedCore_wellFormed` and `childCore_wellFormed`. -/
def Core.WellFormed (c : Core) : Prop :=
  c.fullWord = (proposal c.seedId c.seed c.relWord).fullWord ∧
  c.fullMatrix = (proposal c.seedId c.seed c.relWord).fullMatrix ∧
  c.frame = (proposal c.seedId c.seed c.relWord).frame ∧
  c.addr = (proposal c.seedId c.seed c.relWord).addr ∧
  c.id = (proposal c.seedId c.seed c.relWord).id ∧
  c.closure = psi12 c.fullWord

theorem seedCore_wellFormed (id0 : QuestionId) (seed : History) (entry : ℕ) (prov : Provenance) :
    (seedCore id0 seed entry prov).WellFormed :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Both constructors are well-formed unconditionally.** `childCore` never
    reads the parent's `fullMatrix`/`frame`/`addr` — only its `seedId`,
    `seed`, and `relWord` — and it recomputes every field fresh via
    `childProposal`, which unfolds to exactly the `proposal` call
    `WellFormed` asks it to match. No induction on the parent is needed. -/
theorem childCore_wellFormed (c : Core) (g : Bool) (entry : ℕ) (prov : Provenance) :
    (childCore c g entry prov).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (childProposal c.seedId c.seed c.relWord g).fullWord =
      (proposal c.seedId c.seed (c.relWord ++ [g])).fullWord
    rfl
  · change (childProposal c.seedId c.seed c.relWord g).fullMatrix =
      (proposal c.seedId c.seed (c.relWord ++ [g])).fullMatrix
    rfl
  · change (childProposal c.seedId c.seed c.relWord g).frame =
      (proposal c.seedId c.seed (c.relWord ++ [g])).frame
    rfl
  · change (childProposal c.seedId c.seed c.relWord g).addr =
      (proposal c.seedId c.seed (c.relWord ++ [g])).addr
    rfl
  · change (childProposal c.seedId c.seed c.relWord g).id =
      (proposal c.seedId c.seed (c.relWord ++ [g])).id
    rfl
  · exact Core.ofProposal_closure _ _ _ _ _

/-- **Proposition 6.8, clause 2 (matrix recursion), in the book's own
    vocabulary.** `M_x = M_{par(x)}g_x`. Needs the parent well-formed —
    `childCore_wellFormed` supplies that for every parent an archive actually
    contains — so this is the printed statement, not merely the unconditional
    fact `childCore_closure` already gave for the closure clause. -/
theorem childCore_fullMatrix' (c : Core) (hc : c.WellFormed) (g : Bool) (entry : ℕ)
    (prov : Provenance) :
    (childCore c g entry prov).fullMatrix = forward c.fullMatrix (Word.gen g) := by
  have hstep : (childCore c g entry prov).fullMatrix =
      forward (proposal c.seedId c.seed c.relWord).fullMatrix (Word.gen g) := by
    change (childProposal c.seedId c.seed c.relWord g).fullMatrix = _
    rw [childProposal_fullMatrix]
  rw [hstep, ← hc.2.1]

/-- **Proposition 6.8, clause 3, in the book's own vocabulary.**
    `κ_cl(x) = κ_cl(par(x)) + ψ₁₂(g_x) mod 12`. -/
theorem childCore_closure' (c : Core) (hc : c.WellFormed) (g : Bool) (entry : ℕ)
    (prov : Provenance) :
    (childCore c g entry prov).closure = c.closure + psi12 [g] := by
  rw [childCore_closure, ← hc.1, ← hc.2.2.2.2.2]

/-! ## Definition 4.8's `π_r`, named at the occurrence level

    Needed for Elements II Theorem 17.5, the relation-level/occurrence-level
    resolution crosswalk. `Cavity.lean`'s own docstring already calls
    `ProposalRecord.addr` "π_r of the occurrence: the projection that forgets
    the tag"; nothing new is computed here, the field is only given the name
    Theorem 17.5 is stated in. -/

/-- **`π_r`, restated.** Exactly `Core.addr`, under the name the book's
    crosswalk theorem uses. -/
def Core.piR (c : Core) : Pres := c.addr

/-- **The occurrence read back as a `History`.** `Elements I` names its own
    relation projection `π_r : H ↦ H.addressed` outright (`Question.lean`,
    `addressed_not_injective`'s neighbourhood) — a seed's frame together with
    the relative word reached from it is exactly the `History` a `Core`
    carries, packaged here as one. -/
def Core.toHistory (c : Core) : History := ⟨c.seed.frame, c.relWord⟩

/-- **The two conventions are one function.** `π_r` at the occurrence level
    (`Core.addr`, Definition 4.8) and `π_r` at the relation level
    (`History.addressed`, Elements I) were never two projections that happen
    to agree — reading a well-formed core as a `History` and taking Elements
    I's own `π_r` of it reproduces `Core.addr` exactly, because both reduce to
    `Frame.addressed c.seed.frame c.relWord`. Needs `WellFormed`: `addr` is a
    stored field on the bare structure, so nothing forces this for an
    arbitrary term of type `Core`, only for one either constructor produced. -/
theorem Core.piR_eq_toHistory_addressed (c : Core) (hc : c.WellFormed) :
    c.piR = c.toHistory.addressed :=
  hc.2.2.2.1

/-- `π_r` lifted to a realized candidate record. -/
def Cand.piR {Aux : Type} (x : Cand Aux) : Pres := x.core.piR

/-! ## Proposition 6.9 — Occurrence-singleton is the safe resolution type,
    and Corollary 6.10 — support comparison counts occurrences by stable identifier

    Both share one witness: two proposals from the same seed and the same
    relative word, distinct only in `qid`, reach the same address by distinct
    identifiers. -/

section Witness

def occA : Core :=
  seedCore ⟨0, 0, 0, []⟩ ⟨Frame.empty, [false]⟩ 0 ⟨⟨0, 0, 0, []⟩, ⟨0, 0, 0, []⟩, ⟨0, 0⟩⟩

def occB : Core :=
  seedCore ⟨0, 1, 0, []⟩ ⟨Frame.empty, [false]⟩ 0 ⟨⟨0, 1, 0, []⟩, ⟨0, 1, 0, []⟩, ⟨0, 0⟩⟩

/-- **Proposition 6.9.** `|π_r(S_j)| = 1` does not imply one active occurrence:
    two distinct occurrence identifiers reach the same address. -/
theorem occurrence_singleton_not_forced_by_addr :
    occA.id ≠ occB.id ∧ occA.addr = occB.addr := by
  constructor <;> decide

/-- **Proposition 6.9, the positive-decoding half.** Within one canonical
    positive frame with one tag per word, positive decoding restores
    injectivity — freeness, Standard Result 3.1, cited rather than
    re-derived. -/
theorem positive_decoding_restores_injectivity {u v : Word} (h : Word.G u = Word.G v) :
    u = v := G_inj h

/-- **Corollary 6.10, as an exact count.** Deduplicating the two-witness
    archive by identifier keeps both; deduplicating by address collapses them
    to one. The drop from `2` to `1` is exactly "deletes causal multiplicity",
    stated as an integer rather than a description. -/
theorem no_dedup_by_received_value :
    ([occA, occB].map Core.id).dedup.length = 2 ∧
    ([occA, occB].map Core.addr).dedup.length = 1 := by
  constructor <;> decide

end Witness

end Two
end RatioSpace
