/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S19.Return
/-!
  **§20 — The complete question update.**

  Eight items, all rows empty before today. This file carries the first three:
  the forward resolution map, the partial complete update, and the tagged cycle
  outcome with its total evaluator.

  **Almost nothing here is new.** 20.1 is initialize, iterate, report, snap — and
  all four already exist (`Cavity.InitContext`/`S0tilde` for Definitions 4.7/4.8,
  `Accumulation.Term`, `Terminal.Report.of`, `Snap.snap`). 20.3's three branches
  are exactly `Terminal.TermStatus`'s three constructors, in the book's own order.

  **One modelling decision, made rather than guessed.** The book's `S_τ` is "a
  valid complete state", and `Two/` has no single state record. The outcome type
  is therefore **parameterised over the state**, the way this tree already
  parameterises over `Aux`/`RawAux`/`EvalAux`. That is faithful: 20.4, 20.5 and
  20.6 are statements about *which branch* is returned and *what it carries*,
  never about a state's internals.
-/

namespace RatioSpace
namespace Two
namespace Cycle

open Mat2 Word Frame Pres RatioSpace Advance Accumulation Terminal Snap Return

/-! ## Definition 20.1 — Forward resolution map -/

/-- **Definition 20.1.** `F^(h)_𝒬(S_τ) = Snap_𝒬(R^(h)_𝒬)`, where the report is
    formed from `𝔎^h_𝒞(Init_𝒬(S_τ))`.

    Every stage is already built and this composes them: `Term` is `iterate` at
    the horizon, so `𝔎^h ∘ Init` is what the policy and tick-zero carrier
    supply; `Report.of` forms `R^(h)`; `snap` commits on the singleton stratum.
    Partial for exactly one reason — the snap is. -/
def forwardResolution {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    Option (Cand EvalAux × Report RawAux EvalAux h) :=
  snap pol X0 hX0 hh evalLedger

/-- The forward map is defined exactly where the snap is, hence exactly on the
    singleton stratum. Nothing new is refused and nothing new is admitted. -/
@[simp] theorem forwardResolution_isSome {RawAux EvalAux : Type} {h : ℕ}
    (pol : Policy RawAux h) (X0 : TickCarrier RawAux h) (hX0 : Seeded X0)
    (hh : 0 < h) (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    (forwardResolution pol X0 hX0 hh evalLedger).isSome
      = (crystallize pol X0 hX0 hh evalLedger).isSome :=
  snap_isSome_iff pol X0 hX0 hh evalLedger

/-! ## Definition 20.2 — Partial complete update

    `𝒰_𝒬 = B^obs_𝒬 ∘ (id, F_𝒬)`: run the forward map, then adopt. It is partial
    because `F_𝒬` is, and for no other reason — adoption itself is total on the
    compatible domain, which is what Definition 19.4 fixes in advance. -/

/-- **Definition 20.2.** The state after the update, given the return map as the
    adoption step. `adopt` stands for `B^obs_𝒬`, whose components are §19's four
    assignments; it is taken as a parameter because the state type is. -/
def completeUpdate {σ RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux))
    (source : σ) (adopt : σ → Cand EvalAux → σ) : Option σ :=
  (forwardResolution pol X0 hX0 hh evalLedger).map (fun p => adopt source p.1)

/-- The update is defined exactly where the forward map is. Adoption adds no
    further failure mode of its own. -/
@[simp] theorem completeUpdate_isSome {σ RawAux EvalAux : Type} {h : ℕ}
    (pol : Policy RawAux h) (X0 : TickCarrier RawAux h) (hX0 : Seeded X0)
    (hh : 0 < h) (evalLedger : List (QuestionId × EvalRecord EvalAux))
    (source : σ) (adopt : σ → Cand EvalAux → σ) :
    (completeUpdate pol X0 hX0 hh evalLedger source adopt).isSome
      = (forwardResolution pol X0 hX0 hh evalLedger).isSome := by
  unfold completeUpdate
  cases forwardResolution pol X0 hX0 hh evalLedger <;> rfl

/-! ## Definition 20.3 — Total tagged cycle evaluation -/

/-- **Definition 20.3.** `𝔜_𝒬 = Assimilated(S_{τ+1}, C^cyc) ⊔ Empty(S_τ, R) ⊔
    Unresolved(S_τ, R)`.

    **Lawful nonresolution without making `𝒰_𝒬` artificially total.** Each
    non-assimilated branch carries the *unchanged source state* together with the
    complete report — so a cycle that does not resolve still returns evidence,
    never a bare null. That is Corollary 20.6, and it is visible in the
    constructors rather than needing a proof. -/
inductive CycleOutcome (σ RawAux EvalAux : Type) (h : ℕ) where
  /-- `S_7 = {x*}`: one valid next state and one cycle certificate. -/
  | assimilated (next : σ) (cert : CycleCertificate RawAux EvalAux h)
  /-- `S_7 = ∅`: the source state, unchanged, and the complete report. -/
  | empty (source : σ) (report : Report RawAux EvalAux h)
  /-- `|S_7|_occ > 1`: the source state, unchanged, and the complete report. -/
  | unresolved (source : σ) (report : Report RawAux EvalAux h)

/-- **Definition 20.3, the total evaluator.** `Cycle_𝒬(S_τ)` dispatches on the
    terminal support's status, which is `Terminal.termStatus` — the three cases
    of the book's brace are that trichotomy, in its own order. Total by
    construction: `TermStatus` has three constructors and each has a branch. -/
def cycle {σ RawAux EvalAux : Type} {h : ℕ}
    (source : σ) (report : Report RawAux EvalAux h)
    (assimilate : σ × CycleCertificate RawAux EvalAux h) :
    CycleOutcome σ RawAux EvalAux h :=
  match report.status with
  | .singleton => .assimilated assimilate.1 assimilate.2
  | .empty => .empty source report
  | .unresolvedMultiple => .unresolved source report

/-- The assimilated branch is taken **exactly** on the singleton stratum. This is
    the dispatch stated as an iff, and it is what Corollary 20.5 needs. -/
@[simp] theorem cycle_assimilated_iff {σ RawAux EvalAux : Type} {h : ℕ}
    (source : σ) (report : Report RawAux EvalAux h)
    (assimilate : σ × CycleCertificate RawAux EvalAux h) :
    (∃ s c, cycle source report assimilate = .assimilated s c)
      ↔ report.status = .singleton := by
  unfold cycle
  cases hs : report.status with
  | empty => simp
  | singleton => exact ⟨fun _ => rfl, fun _ => ⟨_, _, rfl⟩⟩
  | unresolvedMultiple => simp

/-! ## Theorem 20.4 — Determinism and typedness of the complete cycle -/

/-- **Theorem 20.4.** *"On its compatible input type, `Cycle_𝒬` returns exactly
    one tagged outcome."*

    **Same shape as Proposition 11.7, and worth saying so.** In a total type
    theory `cycle` is a function, so "exactly one output" is free and a theorem
    asserting it would say nothing. The book's proof spends its length elsewhere:
    Theorem 15.2 gives one terminal carrier, Theorem 17.3 assigns it one of three
    *mutually exclusive* statuses, and each status has exactly one branch.

    So the honest content is the trichotomy being exhaustive and exclusive —
    already `termStatus_trichotomy` and `termStatus_exclusive` — plus the fact
    that the dispatch consumes it without a default case. That second half is
    what is stated here: every status lands in its own named branch. -/
theorem cycle_dispatch_total {σ RawAux EvalAux : Type} {h : ℕ}
    (source : σ) (report : Report RawAux EvalAux h)
    (assimilate : σ × CycleCertificate RawAux EvalAux h) :
    (report.status = .singleton ∧
      cycle source report assimilate = .assimilated assimilate.1 assimilate.2) ∨
    (report.status = .empty ∧
      cycle source report assimilate = .empty source report) ∨
    (report.status = .unresolvedMultiple ∧
      cycle source report assimilate = .unresolved source report) := by
  unfold cycle
  cases hs : report.status with
  | singleton => exact Or.inl ⟨rfl, rfl⟩
  | empty => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | unresolvedMultiple => exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- **20.4's typedness half.** *"Its `Assimilated` branch contains one valid next
    state; its other two branches contain the unchanged source state together
    with one complete exact terminal report."*

    The non-assimilated branches return the source **unchanged** — not a repaired
    state, not a default. That is carried by the constructors and is `rfl`. -/
theorem cycle_nonassimilated_preserves_source {σ RawAux EvalAux : Type} {h : ℕ}
    (source : σ) (report : Report RawAux EvalAux h)
    (assimilate : σ × CycleCertificate RawAux EvalAux h)
    (hs : report.status ≠ .singleton) :
    cycle source report assimilate = .empty source report ∨
      cycle source report assimilate = .unresolved source report := by
  unfold cycle
  cases h' : report.status with
  | singleton => exact absurd h' hs
  | empty => exact Or.inl (rfl)
  | unresolvedMultiple => exact Or.inr (rfl)

/-! ## Corollary 20.5 — Exact observer-replacement domain -/

/-- **Corollary 20.5.** *"The observer is replaced if and only if the terminal
    support is an occurrence singleton... Empty support, relation-only uniqueness
    with occurrence multiplicity, and exact multiple support do not replace the
    observer."*

    Definition 19.5 is the only observer-replacement operation in the complete
    update, and 20.2 restricts its domain to the assimilated branch. So the
    replacement domain is exactly `cycle_assimilated_iff`'s, and the negative
    half is the contrapositive: off the singleton stratum the source survives
    untouched, which is the theorem above. -/
theorem observer_replaced_iff_singleton {σ RawAux EvalAux : Type} {h : ℕ}
    (source : σ) (report : Report RawAux EvalAux h)
    (assimilate : σ × CycleCertificate RawAux EvalAux h) :
    (∃ s c, cycle source report assimilate = .assimilated s c)
      ↔ report.status = .singleton :=
  cycle_assimilated_iff source report assimilate

/-! ## Corollary 20.6 — The cycle preserves evidence in every terminal case -/

/-- **Corollary 20.6.** *"No terminal outcome is represented by a bare null value
    or by an erasure of the evaluated cycle."*

    Immediate from the three constructors, exactly as the book says: the
    assimilated branch carries a complete cycle certificate, and each other
    branch carries a complete terminal report. There is no fourth constructor and
    no constructor carrying nothing — which is why this is a statement about the
    *type*, not about any particular run. -/
theorem cycle_carries_evidence {σ RawAux EvalAux : Type} {h : ℕ}
    (y : CycleOutcome σ RawAux EvalAux h) :
    (∃ s c, y = .assimilated s c) ∨
    (∃ s r, y = .empty s r) ∨
    (∃ s r, y = .unresolved s r) := by
  cases y with
  | assimilated s c => exact Or.inl ⟨s, c, rfl⟩
  | empty s r => exact Or.inr (Or.inl ⟨s, r, rfl⟩)
  | unresolved s r => exact Or.inr (Or.inr ⟨s, r, rfl⟩)

/-! ## Separation Rule 20.7 — A later question is new exact data

    *"The complete update does not automatically extend the old horizon or
    recycle the old question."*

    A typing separation, and the type already carries it: `cycle` returns a
    `CycleOutcome`, and **no constructor of it contains an `ExtendedQuestion`.**
    A next question is therefore not producible from a cycle outcome — forming
    one requires data this type does not hold, which is precisely the book's
    "must be declared by that question". The same applies after an empty or
    unresolved cycle: those branches carry the report, not a new horizon.

    Stated as a fact about the constructors rather than a theorem, because the
    absence of a field is not something a proposition can assert about itself. -/

/-! ## Boundary Statement 20.8

    *"The exact temporal engine is now complete through one question cycle."*

    The chain the book boxes is now assembled end to end, and every arrow is a
    built object:

        S_τ --Init--> 𝔛_{τ,0} --𝔎^h--> 𝔛_{τ,h} --TermStatus--> R^(h)
        R^(h) --Snap (|S|=1)--> Â_{τ+1} --B^obs--> S_{τ+1}

    `Init` is `Cavity.InitContext`/`S0tilde` (Definitions 4.7/4.8), `𝔎^h` is
    `Accumulation.Term`, `TermStatus` is `Terminal.termStatus`, `R^(h)` is
    `Report.of`, `Snap` is `Snap.snap`, and `B^obs` is §19's four assignments.

    *"The same construction returns exact `empty` and `unresolved-multiple`
    reports without hidden repair"* — `cycle_nonassimilated_preserves_source`.

    The negative half — that the engine has **not** attached sibling shortcuts as
    received faces, recorded incidence, renewed a received identity, or asserted
    a shell or physical projection — is checked by a comment-stripped scan of
    this file and its import closure, not by a grep that would count this
    paragraph. -/

end Cycle
end Two
end RatioSpace
