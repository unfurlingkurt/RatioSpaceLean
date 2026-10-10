/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S03.Observer
import RatioSpace.ElementsI.S09.Question
/-!
  Elements II §4 — Finite question cavities.

  Definition 4.1 through Proposition 4.11. Elements I §9 (`Question.lean`) typed
  a question as relation-valued: `S₀` filters a family of `History`, which
  carries only the accumulated matrix. This section is the extension the book's
  own Import 1.6 promised — occurrence-valued: every candidate now carries a
  stable identity that survives even when its relation, matrix, or output
  coincides with another candidate's.

  **Scope of this file.** Definitions 4.1, 4.2, 4.4, 4.5, 4.6, 4.7, 4.8, 4.9 and
  Propositions 4.10, 4.11 are built. Definition 4.3's *tick* context variant is
  not: it is typed against "a complete carrier of the form given in Definition
  6.2", and Definition 6.2 is §6, not yet built (`state/todos.md` task 8, "then
  §4–§7"). Rather than invent that carrier's shape ahead of the book supplying
  it, `OccPred` is generic in the context type `C`. The *initialization* variant
  — everything Definition 4.8 actually needs, since seed admission is tested at
  event position `0` against `𝔦_τ` and never against a tick carrier — is given
  as `InitContext` and used throughout. The question-typed form of Definition
  4.3, with both variants (`PredContext`), event positions in `{0,…,h_𝒬}` and a
  declared `Bool_Γ` (`PredicateData`), is in `Two/Support.lean`.

  Three things here are sharper than the prose, and each is noted at its result:

    * **Definition 4.2's two descriptions of the accumulated word are proved
      equal, not merely asserted.** The book writes `w₀v` and `M₀G(v)` as
      parallel entries in one tuple; nothing in the prose says the second is the
      matrix of the first. `fullMatrix_eq_G_fullWord` is that theorem, and it
      is exactly `Word.G_append` read through the seed's own matrix identity —
      the same shape as `Frame.toMat2_walk` in `Walk.lean`, which did the same
      job for the frame description a section earlier.
    * **Proposition 4.10 is an exact count, not a bound.** The book's `|S₀|∑2ʲ`
      is stated as "at most". `fullPropDomain_card` gives it as an equality,
      because `wordsUpTo` (Elements I §9) already counts every word of length
      `≤ D` exactly, with no double-counting to bound away.
    * **Definition 4.8's conditional — `π_r(S̃₀) = S₀` when predicates are exact
      lifts — is stated and proved as a real conditional, not summarized.**
      `S0tilde_eq_S0_of_lift` takes the book's own hypothesis (occurrence
      predicates factor through the relation-level ones) and delivers the
      relation-valued Elements I answer as a corollary, rather than asserting
      the two constructions merely resemble each other.

  Everything computable. No `sorry`, no `axiom`.
-/

namespace RatioSpace
namespace Two

open Mat2 Word Frame Pres RatioSpace

/-! ## Definition 4.1 — Stable question and seed identifiers

    `ι(τ,𝗾,ι₀,v) = (τ,𝗾,ι₀,v)`. Not a scalar label assigned after evolution: the
    identifier *is* the retained occurrence address, and appending a generator to
    `v` is the whole of what "child identifier" means. -/

/-- **Definition 4.1.** A stable question/seed identifier: a question cycle, a
    question instance, a seed, and the descendant word relative to that seed. -/
structure QuestionId where
  /-- `τ`, the question cycle. -/
  cycle : ℕ
  /-- `𝗾`, the question instance. -/
  qid : ℕ
  /-- `ι₀`, the seed identifier. -/
  seed : ℕ
  /-- `v`, the descendant word relative to the seed. -/
  rel : Word
deriving DecidableEq

namespace QuestionId

/-- Appending a generator gives the child identifier: `ι(τ,𝗾,ι₀,v)g = ι(τ,𝗾,ι₀,vg)`. -/
def child (i : QuestionId) (g : Bool) : QuestionId := { i with rel := i.rel ++ [g] }

/-- Deleting the final generator gives the parent identifier, for `v ≠ ε`. -/
def parent (i : QuestionId) : QuestionId := { i with rel := i.rel.dropLast }

@[simp] theorem parent_child (i : QuestionId) (g : Bool) : (i.child g).parent = i := by
  simp [child, parent]

end QuestionId

/-! ## Definition 4.2 — Finite proposal domain -/

/-- **Definition 4.2.** A finite descendant proposal record: the occurrence
    identifier, the seed identifier, the relative word, the seed occurrence
    itself, the accumulated word and matrix, the reached frame, and the
    addressed relation — all at relative word `v` from the seed's own frame. -/
structure ProposalRecord where
  /-- `ι(τ,𝗾,ι₀,v)`. -/
  id : QuestionId
  /-- `ι₀`. -/
  seedId : QuestionId
  /-- `v`. -/
  relWord : Word
  /-- The seed occurrence: retained word, and the frame it is currently at,
      both derived the same way Elements I's `History` already derives them. -/
  seed : History
  /-- `w₀v`. -/
  fullWord : Word
  /-- `M₀G(v)`. -/
  fullMatrix : Mat2
  /-- `F₀·v`. -/
  frame : Frame
  /-- `r_{F₀}(v)`, the relative-word address from the seed's own frame. This is
      `π_r` of the occurrence: the projection that forgets the tag. -/
  addr : Pres

/-- **Definition 4.2.** The proposal record at relative word `v` from a tagged
    seed occurrence. `F₀ = seed.frame`, the frame the seed already occupies —
    continuation is *from there*, not from the canonical root a second time. -/
def proposal (id0 : QuestionId) (seed : History) (v : Word) : ProposalRecord where
  id := { id0 with rel := v }
  seedId := id0
  relWord := v
  seed := seed
  fullWord := seed.word ++ v
  fullMatrix := seed.matrix * Word.G v
  frame := Frame.walk seed.frame v
  addr := Frame.addressed seed.frame v

/-- **Sharper than the prose.** The tuple's two descriptions of the accumulated
    state agree: `M₀G(v)` really is the matrix of `w₀v`, not a parallel entry
    that happens to carry the same name. Exactly `Word.G_append` composed with
    the definition of a history's own matrix. -/
theorem fullMatrix_eq_G_fullWord (id0 : QuestionId) (seed : History) (v : Word) :
    (proposal id0 seed v).fullMatrix = Word.G (proposal id0 seed v).fullWord := by
  simp [proposal, History.matrix, Word.G_append]

/-- At `v = ε` the proposal's address is the seed's own address: continuing zero
    steps reaches nowhere new. `Frame.walk _ [] = _` unfolds `List.foldl` on the
    empty list, and `History.frame` is exactly the base this walk continues from. -/
@[simp] theorem addr_proposal_nil (id0 : QuestionId) (seed : History) :
    (proposal id0 seed []).addr = seed.addressed := by
  simp [proposal, History.addressed, History.frame, Frame.addressed, Frame.walk]

/-- **Definition 4.2.** The finite proposal domain from one seed, to depth `D`:
    every relative word of length at most `D`, reusing Elements I §9's
    `wordsUpTo` rather than re-deriving the same finite branching. -/
def propDomain (id0 : QuestionId) (seed : History) (D : ℕ) : List ProposalRecord :=
  (wordsUpTo D).map (proposal id0 seed)

theorem propDomain_length (id0 : QuestionId) (seed : History) (D : ℕ) :
    (propDomain id0 seed D).length = (wordsUpTo D).length := by
  simp [propDomain]

/-- **Definition 4.2.** The complete question domain: the union over every seed
    in the active context, each to the declared horizon. -/
def fullPropDomain (seeds : List (QuestionId × History)) (D : ℕ) : List ProposalRecord :=
  seeds.flatMap fun p => propDomain p.1 p.2 D

/-! ## Proposition 4.10 — Finiteness of the question domain -/

/-- **Proposition 4.10, as an exact count rather than a bound.** The book states
    "at most `|S₀|∑ⱼ2ʲ`". Here `wordsUpTo D` (Elements I §9) already enumerates
    every word of length `≤ D` exactly once — that *is* `∑_{j=0}^{D}2ʲ`, since
    `allWords_card` gives `2ʲ` at each length — so `fullPropDomain` is not merely
    bounded by the product, it equals it. -/
theorem fullPropDomain_card (seeds : List (QuestionId × History)) (D : ℕ) :
    (fullPropDomain seeds D).length = seeds.length * (wordsUpTo D).length := by
  induction seeds with
  | nil => simp [fullPropDomain]
  | cons p ps ih =>
      simp only [fullPropDomain, List.flatMap_cons, List.length_append, propDomain_length,
        List.length_cons] at *
      rw [ih]; ring

/-- Restated with Definition 9.2's exact word count, so the whole bound is two
    equalities away from `2^(D+1)`, never a truncated subtraction. -/
theorem fullPropDomain_card' (seeds : List (QuestionId × History)) (D : ℕ) :
    (fullPropDomain seeds D).length + seeds.length = seeds.length * 2 ^ (D + 1) := by
  have h := fullPropDomain_card seeds D
  have hw := wordsUpTo_card D
  rw [h]
  have : seeds.length * (wordsUpTo D).length + seeds.length =
      seeds.length * ((wordsUpTo D).length + 1) := by ring
  rw [this, hw]

/-! ## Receiver Declaration 4.6 — The seven-tick specialization

    Stated ahead of Definitions 4.4–4.5 because `ExtendedQuestion` names it. The
    foundational results below are proved for arbitrary finite horizon; this is
    the one number the distinguished RatioSpace question cycle declares. No claim
    that seven is a raw word period, a universal closure order, or a consequence
    of a later physical scale is made by fixing it. -/

/-- **Receiver Declaration 4.6.** `h_𝒬 = 7`. -/
def sevenTickHorizon : ℕ := 7

/-! ## Definition 4.4 — Recording-socket declaration

    Pure data, typed and not implemented: "this section types the socket; the
    return map later supplies the certificate." `Cert` is generic because no
    resolution-certificate type exists yet in this project — it is supplied by
    the return/resolution machinery of later sections, not invented here. -/

/-- **Definition 4.4.** A recording socket: a target address, a declared
    operation for installing a later certificate there, and a retention
    predicate over prior records. -/
structure RecordingSocket (Cert : Type) where
  /-- `ι_target`, a stable address in the receiving state. -/
  target : QuestionId
  /-- `splice_𝒬`, the declared operation installing a later resolution
      certificate at `target`. -/
  splice : Cert → Cert
  /-- `retain_𝒬` — `true` for a prior record that stays active, `false` for one
      that becomes archival. -/
  retain : QuestionId → Bool

/-! ## Definition 4.5 — Extended finite question -/

/-- **Definition 4.5.** `𝒬 = (O; C₋,C₊; N; 𝐀; Γ; h_𝒬; σ_𝒬)`. Elements I §9's
    `Question` already carries the first five entries — `O`, the Farey-adjacent
    frame, `N`, `𝐀`, `Γ` — so this extends it with the two constructive
    enrichments rather than restating the shared interface. -/
structure ExtendedQuestion (Cert : Type) extends Question where
  /-- `h_𝒬`, the finite construction horizon. -/
  horizon : ℕ
  /-- `σ_𝒬`, the recording-socket declaration. -/
  socket : RecordingSocket Cert

/-- The distinguished RatioSpace instance: any extended question whose horizon is
    the receiver declaration. Stated as a `Prop` rather than baked into the
    structure, since the foundational results hold for every finite horizon and
    only the physical reading singles out seven. -/
def ExtendedQuestion.isReceiverInstance {Cert : Type} (Q : ExtendedQuestion Cert) : Prop :=
  Q.horizon = sevenTickHorizon

/-! ## Definition 4.3 — Exact predicate family (initialization variant)

    `γ : Prop_𝒬 × 𝔠_𝒬 × {0,…,h_𝒬} → {0,1}`, generic in the context type. Only the
    `initialization` branch of `𝔠_𝒬` is instantiated below, as `InitContext`. -/

/-- **Definition 4.3, generic form.** An occurrence-level admissibility
    predicate, generic in the context type `C`, used here with `InitContext`.
    The question-typed form is `QPred` in `Two/Support.lean`. -/
abbrev OccPred (C : Type) := ProposalRecord → C → ℕ → Bool

/-! ## Definition 4.7 — Support-free initialization context -/

/-- **Definition 4.7.** `𝔦_τ = (O_τ, 𝒬_τ, 𝐀, ℋ_seed, ℰ_init)`, with no support
    slot. `seedArchive` carries one tagged seed occurrence per member of `𝐀`,
    covering the retained word, derived matrix, derived frame and derived
    address that Definition 6.1's occurrence core specifies; the closure record,
    imbalance, entry event and provenance fields Definition 6.1 also names await
    §6 itself (task 8) and are not modelled here. -/
structure InitContext (Cert : Type) where
  /-- `O_τ`. -/
  observer : Observer
  /-- `𝒬_τ`. -/
  question : ExtendedQuestion Cert
  /-- `𝐀`, the active relational family. -/
  active : ActiveFamily
  /-- `ℋ_seed`, one tagged seed occurrence per member of `𝐀`. -/
  seedArchive : List (QuestionId × History)
  /-- `ℰ_init`, the initial event annotations: *"only exact annotations
      available before support selection"* (Definition 4.7; Definition 4.3's
      `initialization` variant lists them as "initial event annotations").
      Typed as `TickCarrier.ledger` is (`ℰ_j`, Definition 6.2): a list keyed by
      stable occurrence identifier, over the same annotation type `Cert` that
      the `tick` variant of `PredContext` uses. The default, the empty list, is
      a choice of this file; the book does not fix one. -/
  initLedger : List (QuestionId × Cert) := []

/-! ## Definition 4.9 — Cavity boundary and horizon safety -/

/-- **Definition 4.9.** `γ_∂(y;𝔠,k) = 1 ⟺ π_r(y) ∈ 𝒞(F_𝒬,N)`. The context and
    event position are carried only because every predicate shares Definition
    4.3's type; the boundary predicate itself ignores both. -/
def boundary {C : Type} (F : Frame) (N : ℕ) : OccPred C :=
  fun y _ _ => decide (y.addr ∈ RatioSpace.cavity F N)

/-- A question is **continuation-safe** when every proposal reachable through
    `h_𝒬`, from every declared seed, satisfies the boundary predicate. -/
def continuationSafe (F : Frame) (N : ℕ) (seeds : List (QuestionId × History))
    (h : ℕ) : Prop :=
  ∀ y ∈ fullPropDomain seeds h, y.addr ∈ RatioSpace.cavity F N

/-- A question is **boundary-active** when some reachable proposal may fail it.
    Both are lawful (Definition 4.9); this is exactly the negation. -/
def boundaryActive (F : Frame) (N : ℕ) (seeds : List (QuestionId × History))
    (h : ℕ) : Prop :=
  ¬ continuationSafe F N seeds h

/-! ## Definition 4.8 — Occurrence-valued initial cavity -/

/-- **Definition 4.8.** `S̃₀(𝒬) = {x ∈ 𝐀 : r_x ∈ 𝒞(F_𝒬,N), Pred_Γ(x;𝔦_τ,0) = 1}`,
    with each seed evaluated as its own relative-empty-word proposal record.
    Support is occurrence-valued from here on. -/
def S0tilde {Cert : Type} (F : Frame) (N : ℕ) (preds : List (OccPred (InitContext Cert)))
    (ctx : InitContext Cert) (seeds : List (QuestionId × History)) : List ProposalRecord :=
  (seeds.map fun p => proposal p.1 p.2 []).filter fun y =>
    boundary F N y ctx 0 && preds.all fun γ => γ y ctx 0

/-- The occurrence tag forgotten: `π_r` applied to a member of `S̃₀`. -/
def forgetTag (y : ProposalRecord) : Pres := y.addr

/-- Membership in `S̃₀`, spelled out — the occurrence-valued analogue of
    Elements I §9's `mem_S0`. -/
theorem mem_S0tilde {Cert : Type} (F : Frame) (N : ℕ)
    (preds : List (OccPred (InitContext Cert))) (ctx : InitContext Cert)
    (seeds : List (QuestionId × History)) {y : ProposalRecord} :
    y ∈ S0tilde F N preds ctx seeds ↔
      (∃ p ∈ seeds, y = proposal p.1 p.2 []) ∧
      y.addr ∈ RatioSpace.cavity F N ∧
      (∀ γ ∈ preds, γ y ctx 0 = true) := by
  simp only [S0tilde, List.mem_filter, List.mem_map, Bool.and_eq_true, List.all_eq_true,
    boundary, decide_eq_true_eq]
  tauto

/-- **Definition 4.8's own "exact lift" hypothesis, made a function rather than
    a side condition.** An occurrence predicate that reads only the seed history
    and ignores the occurrence tag entirely. -/
def liftPred {Cert : Type} (γ : Pred) : OccPred (InitContext Cert) :=
  fun y ctx _ => γ y.seed ctx.observer ctx.active

/-- **Definition 4.8's conditional, proved as a real conditional.** When every
    declared predicate is such a lift, and the initialization context's active
    family really is the seed archive's own histories (Definition 4.7's `𝐀`, read
    off `ℋ_seed`), a seed's occurrence-valued proposal record enters `S̃₀` exactly
    when the seed's own history enters the corresponding Elements I `S₀`. When a
    predicate is *not* a lift — when it reads occurrence history the
    relation-level predicate cannot see — no such iff is claimed, matching the
    book's own "occurrence-refined extension" clause. -/
theorem mem_S0tilde_iff_mem_S0 {Cert : Type} (F : Frame) (N : ℕ) (relPreds : List Pred)
    (ctx : InitContext Cert) (seeds : List (QuestionId × History))
    (hactive : ctx.active = seeds.map Prod.snd)
    {p : QuestionId × History} (hp : p ∈ seeds) :
    proposal p.1 p.2 [] ∈ S0tilde F N (relPreds.map liftPred) ctx seeds ↔
      p.2 ∈ RatioSpace.S0
        { receiver := ctx.observer, frame := F, depth := N,
          active := ctx.active, preds := relPreds } := by
  rw [mem_S0tilde]
  simp only [RatioSpace.S0, RatioSpace.Adm, List.mem_filter, decide_eq_true_eq,
    List.all_eq_true, List.mem_map, addr_proposal_nil, hactive]
  constructor
  · rintro ⟨-, hcav, hpred⟩
    refine ⟨⟨⟨p, hp, rfl⟩, fun γ hγ => ?_⟩, hcav⟩
    simpa [liftPred, proposal, hactive] using hpred (liftPred γ) ⟨γ, hγ, rfl⟩
  · rintro ⟨⟨hmem, hpred⟩, hcav⟩
    refine ⟨⟨p, hp, rfl⟩, hcav, fun γ hγ => ?_⟩
    obtain ⟨γ', hγ', rfl⟩ := hγ
    simpa [liftPred, proposal, hactive] using hpred γ' hγ'

/-! ## Proposition 4.11 — A question bounds its support, which may be empty, single, or plural -/

section Example

/-- Two seeds, the two children of the canonical frame, no predicates declared. -/
def sampleSeeds : List (QuestionId × History) :=
  [(⟨0, 0, 0, []⟩, ⟨Frame.empty, [false]⟩), (⟨0, 0, 1, []⟩, ⟨Frame.empty, [true]⟩)]

def sampleObserver : Observer := ⟨Frame.empty, [], 1⟩

def sampleExtQ : ExtendedQuestion Unit where
  receiver := sampleObserver
  frame := Frame.empty
  depth := 1
  active := []
  preds := []
  horizon := sevenTickHorizon
  socket := { target := ⟨0, 0, 0, []⟩, splice := id, retain := fun _ => true }

def sampleCtx : InitContext Unit where
  observer := sampleObserver
  question := sampleExtQ
  active := []
  seedArchive := sampleSeeds

/-- **Proposition 4.11, with a witness.** Both seeds survive `S̃₀` — no predicate
    was declared to exclude either — and they address *different* relations. The
    question type bounds the lawful family; it does not pick a survivor from it. -/
theorem question_bounds_not_forces :
    (S0tilde Frame.empty 1 [] sampleCtx sampleSeeds).length = 2 ∧
    ((S0tilde Frame.empty 1 [] sampleCtx sampleSeeds).map ProposalRecord.addr) =
      [(proposal (⟨0, 0, 0, []⟩ : QuestionId) ⟨Frame.empty, [false]⟩ []).addr,
       (proposal (⟨0, 0, 1, []⟩ : QuestionId) ⟨Frame.empty, [true]⟩ []).addr] ∧
    (proposal (⟨0, 0, 0, []⟩ : QuestionId) ⟨Frame.empty, [false]⟩ []).addr ≠
      (proposal (⟨0, 0, 1, []⟩ : QuestionId) ⟨Frame.empty, [true]⟩ []).addr := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Example

end Two
end RatioSpace
