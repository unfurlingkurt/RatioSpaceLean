/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S15.Accumulation
/-!
  Elements II §17 — terminal status, the lossless report, and the resolution
  crosswalk. Ten items, stated together rather than one per session.

  §17 is almost entirely definitional: three of its ten items are definitions,
  one is a trichotomy that is `Finset` cardinality, and four are corollaries
  saying that certain repairs are *not* available. Written as a block, the only
  content that needs real proof is Theorem 17.3 and the crosswalk 17.5.
-/

namespace RatioSpace
namespace Two
namespace Terminal

open Accumulation

/-- **Definition 17.1 — terminal status.** Trichotomy on the terminal support,
    taken in stable occurrence identifiers with **no** projection to a reduced
    value, closure class or channel value first. -/
inductive TermStatus where
  | empty
  | singleton
  | unresolvedMultiple
deriving DecidableEq, Repr

/-- The status of a terminal support, read off its occurrence cardinality. -/
def termStatus (n : ℕ) : TermStatus :=
  match n with
  | 0 => .empty
  | 1 => .singleton
  | _ => .unresolvedMultiple

/-- **Theorem 17.3 — exact terminal trichotomy.** Every finite cycle returns
    exactly one of the three statuses. The book's proof is that every finite
    set has exactly one of the cardinalities zero, one, or more than one; in
    type theory that is definitional, and the content is that the status is a
    *function of the cardinality alone* — no other datum enters. -/
theorem termStatus_trichotomy (n : ℕ) :
    (termStatus n = .empty ∧ n = 0)
    ∨ (termStatus n = .singleton ∧ n = 1)
    ∨ (termStatus n = .unresolvedMultiple ∧ 2 ≤ n) := by
  match n with
  | 0 => exact Or.inl ⟨rfl, rfl⟩
  | 1 => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | (k+2) => exact Or.inr (Or.inr ⟨rfl, by omega⟩)

/-- The three cases are mutually exclusive: no cardinality yields two statuses. -/
theorem termStatus_exclusive (n : ℕ) :
    ¬(termStatus n = .empty ∧ termStatus n = .singleton) ∧
    ¬(termStatus n = .singleton ∧ termStatus n = .unresolvedMultiple) ∧
    ¬(termStatus n = .empty ∧ termStatus n = .unresolvedMultiple) := by
  match n with
  | 0 => exact ⟨by simp [termStatus], by simp [termStatus], by simp [termStatus]⟩
  | 1 => exact ⟨by simp [termStatus], by simp [termStatus], by simp [termStatus]⟩
  | (k+2) => exact ⟨by simp [termStatus], by simp [termStatus], by simp [termStatus]⟩

/-- **Definition 17.4 — occurrence-level terminal resolution.** Defined
    **exactly** on the singleton stratum and undefined on the other two. The
    partiality is the content: `Option` records that `empty` and
    `unresolved-multiple` have no resolution rather than a default one. -/
def resolveOcc {α : Type} (S : List α) : Option α :=
  match S with
  | [x] => some x
  | _ => none

/-- `resolveOcc` is defined exactly on the singleton stratum. -/
theorem resolveOcc_iff_singleton {α : Type} (S : List α) :
    (resolveOcc S).isSome = true ↔ termStatus S.length = .singleton := by
  match S with
  | [] => simp [resolveOcc, termStatus]
  | [_] => simp [resolveOcc, termStatus]
  | (_ :: _ :: _) => simp [resolveOcc, termStatus]

/-- **Corollary 17.8 — crystallization is a partial map.** There is no function
    from terminal supports to occurrences total on all three strata: `empty`
    has nothing to return. Stated as the non-existence of a total section. -/
theorem no_total_resolution {α : Type} :
    ¬ ∃ f : List α → α, ∀ S, resolveOcc S = some (f S) := by
  rintro ⟨f, hf⟩
  have := hf []
  simp [resolveOcc] at this

/-- **Corollary 17.9 — no repair after an exact terminal tie.** A tie is
    `unresolved-multiple`, and `resolveOcc` is `none` there: nothing downstream
    recovers a winner, because none was recorded. -/
theorem no_repair_after_tie {α : Type} (S : List α)
    (h : termStatus S.length = .unresolvedMultiple) :
    resolveOcc S = none := by
  match S with
  | [] => simp [termStatus] at h
  | [_] => simp [termStatus] at h
  | (_ :: _ :: _) => rfl

/-- **Corollary 17.10 — empty support remains empty within the fixed cycle.**
    Nothing in the terminal report re-populates an empty support. -/
theorem empty_stays_empty {α : Type} (S : List α)
    (h : termStatus S.length = .empty) : S = [] ∧ resolveOcc S = none := by
  match S with
  | [] => exact ⟨rfl, rfl⟩
  | [_] => simp [termStatus] at h
  | (_ :: _ :: _) => simp [termStatus] at h

/-! ## Definition 17.2 — Lossless terminal report

The seven-tuple `(q, τ, h, TermStatus(𝔛_{τ,h}), S_h, TCmp_𝒬^{(h)}, Trace_𝒬^{(h)})`.
Every field on the right of `q`/`τ`/`h` is already built: `TermStatus` above,
`S_h` is the terminal carrier's own `active`, `TCmp` is Definition 16.1
(`Accumulation.TCmp`), and the trace is Definition 15.1 (`Accumulation.trace`
at `n := h`). The report adds no new apparatus — it is the point where the
book's own claim that "the report is produced in all three terminal cases"
becomes checkable: `Report.of` is total on every `Policy`, no case split on
`TermStatus` anywhere in its construction. -/
structure Report (RawAux EvalAux : Type) (h : ℕ) where
  /-- `𝒬`, read from the terminal carrier itself, not supplied separately —
      Definition 16.4's own finding that no tick ever rewrites `question`
      makes the terminal value the one value there is. -/
  q : ExtendedQuestion RawAux
  /-- `τ`, likewise read from the terminal carrier. -/
  observer : Observer
  horizon : ℕ
  status : TermStatus
  Sh : List QuestionId
  cmp : TCmp RawAux EvalAux h
  trace : List (TickCarrier RawAux h)

/-- **Definition 17.2, the report assembled**, `h > 0` case (the only case
    every `Policy` in this tree instantiates; `EvTerm`'s own account already
    names the `h = 0` case as a genuine gap, not one this definition can paper
    over). -/
def Report.of {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) : Report RawAux EvalAux h where
  q := (Term pol X0 hX0).question
  observer := (Term pol X0 hX0).observer
  horizon := h
  status := termStatus (Term pol X0 hX0).active.length
  Sh := (Term pol X0 hX0).active
  cmp := TCmp.of pol X0 hX0 hh evalLedger
  trace := Accumulation.trace pol X0 hX0 h (le_refl h)

/-- **Definition 17.2's record, with the evaluated ledger no longer a
    hypothesis** — the same move `TCmp.ofAssembled` already made for
    Definition 16.1's own record. -/
def Report.ofAssembled {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (hh : 0 < h) : Report Aux EvalValue h :=
  Report.of pol X0 hX0 hh (assembleLedger (Term pol X0 hX0))

/-- The report's own horizon field agrees with the index it was built at. -/
@[simp] theorem Report.of_horizon {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    (Report.of pol X0 hX0 hh evalLedger).horizon = h := rfl

/-- The report's support is the terminal carrier's own active support, not
    some other tick's. -/
@[simp] theorem Report.of_Sh {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    (Report.of pol X0 hX0 hh evalLedger).Sh = (Term pol X0 hX0).active := rfl

/-- The report's status is `termStatus` read off that same support, by
    construction rather than by a further case split. -/
@[simp] theorem Report.of_status {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    (Report.of pol X0 hX0 hh evalLedger).status =
      termStatus (Report.of pol X0 hX0 hh evalLedger).Sh.length := rfl

/-! ## Theorem 17.5 — Relation-level and occurrence-level resolution crosswalk

The book states two things. The first — under injectivity of `π_r` on `S_7`,
occurrence resolution agrees with Elements I's own `resolve` (`Crystal.lean`)
on the projected relation set, and the surviving `Cand` realizes the Elements
I record — needs a `Cand → Candidate` reading this tree does not yet build:
`Candidate.star`/`.signature` are bare `List IPres`/`List ℕ`, keyed by
position against Elements I's `ActiveFamily.relations` (each member's own
self-address, `History.addressedI`), while `Cand`'s evaluated `sigma`/
`tension` slots (`Accumulation.lean`'s `EvalRecord.assemble`) are keyed lists
against `activeFamily`, the *observer-decoded* local addresses (`localOf`,
Definition 3.1's `λ` applied to `Q_{O,y}`). Those are two different families
in general, not the same list under two names — nothing in this tree
identifies them, and Theorem 17.5's first clause needs that identification or
an explicit translation between the two, not merely a `Prod.snd` on the keyed
form. That is the actual remaining content, sharper than "bridging content
this tree does not carry at all."

The second clause needs none of that, and is built below. -/

/-- **Theorem 17.5, second clause.** *"If several occurrence identifiers
    occupy one relation fiber, the projection does not determine which
    complete history-bearing record should be returned."* More occurrences
    than one stays unresolved regardless of what `π_r` does to them — the
    hypothesis `|π_r(S_h)| = 1` is carried in the statement and never read in
    the proof, because `resolveOcc` matches on `S`'s own length and inspects
    no candidate's relation at all. Same shape of finding as Definition
    10.9's determinism contract (`Crystal.lean`): a condition the book states
    alongside a mechanism that does not consult it. -/
theorem occurrence_multiple_stays_unresolved {Aux : Type} (S : List (Cand Aux))
    (_hpi : (S.map Cand.piR).dedup.length = 1) (hocc : 1 < S.length) :
    resolveOcc S = none := by
  match S, hocc with
  | [], h => simp at h
  | [_], h => simp at h
  | _ :: _ :: _, _ => rfl

#print axioms occurrence_multiple_stays_unresolved

/-! ## Definition 17.6 — General-horizon crystallization map

The book's codomain is `Cand_{τ,h}(x*)`, a candidate record, not the bare
identifier `resolveOcc` returns on `Sh`. `crystallize` composes `resolveOcc`
with `ensemble` directly, so it reads a `Cand` off the singleton stratum with
no intermediate identifier lookup. `Carrier.lean`'s
`TickCarrier.ensemble_length_eq_active` is what makes `ensemble`'s stratum
agree with `Sh`'s: **conditional** on the terminal carrier's archive and
active support both being duplicate-free. `crystallize_isSome_iff_singleton`
below states that condition at the terminal carrier, the honest scope when it
was written; `crystallize_isSome_iff_singleton_of_carrierInv` discharges it
from a hypothesis on the tick-zero carrier instead, via the schedule-length
induction (`Accumulation.lean`'s `CarrierInv`/`iterate_carrierInv`) that was
the genuine remaining gap. -/

/-- **Definition 17.6.** The crystallization map, defined exactly on the
    singleton stratum, at the `Cand` codomain the book states. -/
def crystallize {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (_hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) : Option (Cand EvalAux) :=
  resolveOcc (ensemble (Term pol X0 hX0) evalLedger)

/-- **Theorem 17.7, the iff-direction — `resolveOcc_iff_singleton` restated
    at the `Cand` codomain and matched against the report's own `status`
    field.** Needs the terminal carrier's archive and active support to be
    duplicate-free, stated here exactly as a hypothesis on that carrier — the
    honest scope the moment this theorem was first built, since nothing before
    it asked whether an *iterated* carrier keeps either property.
    `crystallize_isSome_iff_singleton_of_carrierInv`, below, discharges both
    hypotheses from a check on the tick-zero carrier instead. The
    sufficient-condition clause this theorem's account still owes — connecting
    `Coherence.lean`'s `support` to a unique strict maximizer — is untouched by
    this pass. -/
theorem crystallize_isSome_iff_singleton {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux))
    (hArch : ((Term pol X0 hX0).archive.map Core.id).Nodup)
    (hAct : (Term pol X0 hX0).active.Nodup) :
    (crystallize pol X0 hX0 hh evalLedger).isSome = true
      ↔ (Report.of pol X0 hX0 hh evalLedger).status = .singleton := by
  unfold crystallize
  rw [resolveOcc_iff_singleton,
      TickCarrier.ensemble_length_eq_active _ _ hArch hAct,
      Report.of_status, Report.of_Sh]

#print axioms crystallize_isSome_iff_singleton

/-- **Theorem 17.7's iff-direction, unconditional at last** — the schedule-
    length induction the account above named as the genuine gap,
    `Accumulation.lean`'s `iterate_carrierInv`, closes it. What is asked of the
    caller shifts from an unverifiable fact about the terminal carrier (reached
    after up to `h` policy-dependent steps) to a checkable fact about the
    tick-zero carrier actually supplied: `CarrierInv X0`, duplicate-free
    identifiers and well-formed cores at the seed archive, duplicate-free seed
    active support. Every real genesis carrier this tree builds (`Qeps`/`QL`/
    `QR`'s three seeds, `sevenTickHorizon`) satisfies this trivially — a
    handful of `seedCore` values with distinct identifiers is exactly the case
    `CarrierInv` was written to cover for free. -/
theorem crystallize_isSome_iff_singleton_of_carrierInv {RawAux EvalAux : Type} {h : ℕ}
    (pol : Policy RawAux h) (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) (hinv0 : CarrierInv X0) :
    (crystallize pol X0 hX0 hh evalLedger).isSome = true
      ↔ (Report.of pol X0 hX0 hh evalLedger).status = .singleton := by
  have hinv : CarrierInv (Term pol X0 hX0) := iterate_carrierInv pol X0 hX0 hinv0 h (le_refl h)
  exact crystallize_isSome_iff_singleton pol X0 hX0 hh evalLedger hinv.1 hinv.2.2

#print axioms crystallize_isSome_iff_singleton_of_carrierInv


/-! ## Theorem 17.5's first clause — the crosswalk, built

The account above named the obstruction and stopped there: `activeFamily`'s
keys are observer-decoded local addresses, Elements I's are each member's own
self-address, and nothing in this tree identified them. They are related
exactly, and by apparatus already here — Definition 3.5's own composition law
(`Observer.lean`'s `addressed_walk`), applied twice.

The translation is a **rebase**. Elements I's key is the Elements II *local
word* evaluated at the observer's frame instead of at `F_∅`. What
`activeFamily` drops is therefore not information about the occurrence; it is
the base frame its local word is read in. That is why `activeFamilyWords`,
built for Definition 7.4's unrelated `D_walk` reason, already carries
everything the crosswalk needs while `activeFamily` alone does not.

Two independent side conditions make the two families literally equal, and
both are the same phenomenon entering from opposite ends — a nonempty prefix
between the reading frame and `F_∅`. The observer contributes one (`w_O`);
the occurrence's own declared seed start contributes the other. Each has a
witness that it bites: `Observer.lean`'s `lambda_ne_world_chart` for the
observer, `piR_ne_r_fullWord_of_shifted_seed` below for the seed. -/

/-- **`π_r` from the occurrence's own stored word**, the `w_O = ε` case named
    on its own because the family statement below is stated at it. -/
theorem piR_eq_addressed_fullWord (c : Core) (hc : c.WellFormed) :
    c.piR = Frame.addressed c.seed.start c.fullWord := by
  have hfw : c.seed.word ++ c.relWord = c.fullWord := hc.1.symm
  rw [Core.piR, hc.2.2.2.1]
  change Frame.addressed (History.frame c.seed) c.relWord = _
  rw [History.frame, addressed_walk, hfw]

/-- **The rebase, general in the observer.** For any positive observer
    `G(w_O)` that admits `c`, `π_r(c)` is the observer-local word `a`
    evaluated at the observer's frame, taken from the occurrence's own
    declared seed start. No new arithmetic: Definition 3.5's composition law
    strips the seed's frame and inserts the observer's. -/
theorem piR_eq_addressed_localWord {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (c : Core) (hc : c.WellFormed) (wO a : Word)
    (hO : X.observer.matrix = Word.G wO)
    (ha : localWord X.observer.matrix c.fullMatrix = some a) :
    c.piR = Frame.addressed (Frame.walk c.seed.start wO) a := by
  have hfm : c.fullMatrix = Word.G c.fullWord := by
    rw [hc.2.1, fullMatrix_eq_G_fullWord, ← hc.1]
  have hQ : Q (Word.G wO) (Word.G c.fullWord) = Word.G a :=
    (dec_sound (by rw [← hO, ← hfm]; exact ha)).symm
  rw [piR_eq_addressed_fullWord c hc, prop_3_2_word hQ, addressed_walk]

/-- **The two keys coincide, exactly here.** At the boundary observer and a
    canonically-started seed, `localOf` returns `π_r` on the nose — and it
    returns it, never `none`: the second failure mode `localOf`'s own
    docstring hedges as "not expected to bite in practice" is provably
    vacuous, because every address it can produce is a walked mediant and
    `Frame.walk_mid_pos` makes those interior unconditionally. -/
theorem localOf_toPres_eq_piR {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (c : Core) (hc : c.WellFormed) (hO : X.observer.matrix = 1)
    (hstart : c.seed.start = Frame.empty) :
    (localOf X c).map IPres.toPres = some c.piR := by
  have hfm : c.fullMatrix = Word.G c.fullWord := by
    rw [hc.2.1, fullMatrix_eq_G_fullWord, ← hc.1]
  have hpi : c.piR = Frame.r c.fullWord := by
    rw [piR_eq_addressed_fullWord c hc, hstart]; rfl
  have hint : c.piR.Interior := by
    rw [piR_eq_addressed_fullWord c hc]; exact Frame.walk_mid_pos _ _
  have hl : lambda X.observer.matrix c.fullMatrix = some c.piR := by
    rw [lambda, localWord, hO, hfm, Q_one, dec_G, hpi]; rfl
  rw [localOf, hl]
  change Option.map IPres.toPres (IPres.ofPres? c.piR) = some c.piR
  rw [show IPres.ofPres? c.piR = some ⟨c.piR.p, c.piR.q, hint.1, hint.2⟩ from dif_pos hint]
  rfl

/-- **The seed condition bites**, and it is the same phenomenon as the
    observer's read from the other end. A seed whose declared start is one
    step off `F_∅` addresses `3:2` while the canonical reading of its own
    stored word gives `1:2` — the identical pair `lambda_ne_world_chart`
    exhibits for the observer, now on a `Core` this tree's own constructor
    produces. -/
theorem piR_ne_r_fullWord_of_shifted_seed :
    ∃ c : Core, c.WellFormed ∧ c.piR ≠ Frame.r c.fullWord := by
  refine ⟨seedCore ⟨0, 0, 0, []⟩ ⟨Frame.walk Frame.empty [true], [false]⟩ 0
      ⟨⟨0, 0, 0, []⟩, ⟨0, 0, 0, []⟩, ⟨0, 0⟩⟩,
    seedCore_wellFormed _ _ _ _, ?_⟩
  decide

/-- **Theorem 17.5's first clause, at the family level.** Under the two
    conditions, `activeFamily` and Elements I's `ActiveFamily.relations` are
    not two lists that happen to agree entrywise — they are one list, read
    through `IPres.toPres`, with the same length and the same order, so
    Elements I's positional keying of `Candidate.star`/`.signature` transfers
    to `Cand`'s evaluated `sigma`/`tension` slots without a translation step
    at the call site. Off those conditions the rebase above is what a call
    site must apply, and `activeFamilyWords` is what it must apply it to. -/
theorem activeFamily_toPres_eq_piR_map {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hO : X.observer.matrix = 1)
    (hwf : ∀ c ∈ X.archive, c.WellFormed ∧ c.seed.start = Frame.empty) :
    (activeFamily X).map IPres.toPres
      = (X.archive.filter fun c => decide (c.id ∈ X.active)).map Core.piR := by
  unfold activeFamily
  rw [List.map_filterMap]
  have key : ∀ c ∈ X.archive.filter (fun c => decide (c.id ∈ X.active)),
      (localOf X c).map IPres.toPres = some c.piR := by
    intro c hc
    have h' := hwf c (List.mem_of_mem_filter hc)
    exact localOf_toPres_eq_piR X c h'.1 hO h'.2
  generalize X.archive.filter (fun c => decide (c.id ∈ X.active)) = L at key
  induction L with
  | nil => rfl
  | cons a t ih =>
    rw [List.filterMap_cons, key a (by simp),
        List.map_cons, ih (fun c hc => key c (List.mem_cons_of_mem a hc))]

#print axioms piR_eq_addressed_localWord
#print axioms localOf_toPres_eq_piR
#print axioms activeFamily_toPres_eq_piR_map

end Terminal
end Two
end RatioSpace
