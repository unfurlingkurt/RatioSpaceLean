/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S11.Advance
/-!
  Gap G2-12 · Elements II Definition 11.6, the one-tick advance.

  **Book statement.** "Let `ΔE_{j+1}` be the event stratum containing: 1. the tick
  marker `(τ, j → j+1)`; 2. the complete parent-support and proposal identifiers;
  3. every admission certificate; 4. every applicable comparison package; 5. the
  exact support `S_{j+1}` and every creation status; 6. every native annotation
  package; and 7. explicit empty-family records whenever no proposal or no
  admitted occurrence exists. Set `E_{j+1} = E_j ⌢ ΔE_{j+1}`."

  **What was missing.** Two things, both in `Two/Advance.lean`.

  (a) `Δ` is a caller-supplied `List (QuestionId × Aux)`. `advanceCarrier` appends
  whatever it is handed, so the seven enumerated contents are not enforced: `Δ = []`
  type-checks and the tick then writes no stratum at all.

  (b) `hfresh` — Lemma 12.1 — enters `advanceCarrier` and `TickStep` as a
  hypothesis. Its ingredients are proved (`child_id_inj`, `child_rel_length`,
  `child_ne_of_length_le`), but nothing derives the hypothesis itself from a
  property of the carrier, so every caller must supply it by hand.

  **Built here.** For (b): the length invariant Lemma 12.1 is actually about
  (`Stratified`), freshness derived from it rather than assumed, and its
  preservation on the archive under one advance. For (a): the stratum's
  enforceable clauses as a predicate on the `Δ` that is already there — no new
  ledger type — with the teeth shown both ways: a recording stratum is never
  empty even when nothing was proposed and nothing admitted (clause 7), the empty
  `Δ` never records, a `Δ` carrying only the marker does not record when the
  support is nonempty, and the recorded stratum is exactly the segment the advance
  appends, so no required identifier lands in an earlier stratum.
  Clauses 3, 4, 6 and the creation statuses of clause 5 are typed over `Aux` and
  are not reachable from this file; what is enforced is their keying, which is.
  No existing declaration is changed.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_12

open RatioSpace.Two RatioSpace.Two.Advance

/-! ## (b) Lemma 12.1 as a property of the carrier, not a hypothesis -/

/-- **Lemma 12.1's own content.** "Every archived occurrence created no later than
    tick `j` has a relative continuation word of length at most `j`, whereas a
    proposal at the current advance has length `j+1`." Stated as an invariant of
    the carrier: every archived identifier is at most at the tick, and every
    active occurrence is exactly at it. -/
def Stratified {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) : Prop :=
  (∀ x ∈ X.archive, x.id.rel.length ≤ (X.tick : ℕ)) ∧
  (∀ c ∈ X.archive, c.id ∈ X.active → c.relWord.length = (X.tick : ℕ))

/-- A child core's identifier is one generator longer than its parent's relative
    word. -/
theorem childCore_id_rel_length (c : Core) (g : Bool) (entry : ℕ) (prov : Provenance) :
    (childCore c g entry prov).id.rel.length = c.relWord.length + 1 := by
  simp [childCore, Core.ofProposal, childProposal, proposal]

/-- The proposing parent is archived and active. -/
theorem proposals_parent {archive : List Core} {active : List QuestionId}
    {p : Core × Bool} (hp : p ∈ proposals archive active) :
    p.1 ∈ archive ∧ p.1.id ∈ active := by
  unfold proposals at hp
  obtain ⟨c, hc, hmem⟩ := List.mem_flatMap.mp hp
  obtain ⟨hcA, hcAct⟩ := List.mem_filter.mp hc
  have : p.1 = c := by
    rcases List.mem_cons.mp hmem with h | h
    · exact congrArg Prod.fst h
    · rcases List.mem_cons.mp h with h' | h'
      · exact congrArg Prod.fst h'
      · exact absurd h' (by simp)
  subst this
  exact ⟨hcA, by simpa using hcAct⟩

/-- **Lemma 12.1, discharged.** On a stratified carrier every identifier this tick
    proposes is fresh. `hfresh` need not be assumed: it follows from the lengths.
    This is the hypothesis `advanceCarrier` and `TickStep` take, now a theorem. -/
theorem fresh_of_stratified {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hS : Stratified X) (stratum : ℕ) (prov : Provenance) :
    ∀ p ∈ proposals X.archive X.active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive := by
  intro p hp hmem
  obtain ⟨hpA, hpAct⟩ := proposals_parent hp
  obtain ⟨x, hxA, hxid⟩ := List.mem_map.mp hmem
  have hlenX : x.id.rel.length ≤ (X.tick : ℕ) := hS.1 x hxA
  have hlenP : p.1.relWord.length = (X.tick : ℕ) := hS.2 p.1 hpA hpAct
  have hchild : (childCore p.1 p.2 stratum prov).id.rel.length = (X.tick : ℕ) + 1 := by
    rw [childCore_id_rel_length, hlenP]
  rw [← hxid] at hchild
  omega

/-- **The invariant survives the archive update.** Every core in the advanced
    archive is at most at tick `j+1`: the old ones were at most at `j`, and the
    new ones are exactly at `j+1`. So the first clause of `Stratified` is never
    re-assumed at the next tick either. -/
theorem stratified_archive_step {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hS : Stratified X) (stratum : ℕ) (prov : Provenance) :
    ∀ x ∈ advanceArchive X.archive X.active stratum prov,
      x.id.rel.length ≤ (X.tick : ℕ) + 1 := by
  intro x hx
  unfold advanceArchive keyedUnion at hx
  rcases List.mem_append.mp hx with hL | hR
  · exact Nat.le_succ_of_le (hS.1 x hL)
  · obtain ⟨hy, -⟩ := List.mem_filter.mp hR
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hpA, hpAct⟩ := proposals_parent hp
    rw [childCore_id_rel_length, hS.2 p.1 hpA hpAct]

/-! ## (a) The event stratum's enforceable contents -/

/-- **Definition 11.6's stratum, as a condition on the `Δ` already there.** The
    clauses this file can reach: 1, the tick marker; 2, the complete parent
    support and every proposal identifier; 5, the exact support `S_{j+1}`.
    Clauses 3, 4, 6 and the creation statuses are `Aux`-typed records; what is
    enforced of them is their keying, which is the same membership condition. -/
def RecordsStratum {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (select : List (Core × Bool) → List QuestionId) (stratum : ℕ) (prov : Provenance)
    (marker : QuestionId) (Δ : List (QuestionId × Aux)) : Prop :=
  marker ∈ Δ.map Prod.fst ∧
  (∀ i ∈ X.active, i ∈ Δ.map Prod.fst) ∧
  (∀ p ∈ proposals X.archive X.active,
    (childCore p.1 p.2 stratum prov).id ∈ Δ.map Prod.fst) ∧
  (∀ i ∈ select (proposals X.archive X.active), i ∈ Δ.map Prod.fst)

/-- **Clause 7, with the teeth it was written for.** A stratum that records is
    never empty, *including* the tick at which nothing was proposed and nothing
    admitted: the tick marker is a record in its own right. Absence of a record is
    not a record of absence. -/
theorem recordsStratum_nonempty {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (select : List (Core × Bool) → List QuestionId) (stratum : ℕ) (prov : Provenance)
    (marker : QuestionId) (Δ : List (QuestionId × Aux))
    (hR : RecordsStratum X select stratum prov marker Δ) : Δ ≠ [] := by
  intro h0
  rw [h0] at hR
  simpa using hR.1

/-- **The empty stratum never records.** This is the `Δ` the caller could supply
    before: a tick that wrote nothing at all. -/
theorem empty_not_records {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (select : List (Core × Bool) → List QuestionId) (stratum : ℕ) (prov : Provenance)
    (marker : QuestionId) : ¬ RecordsStratum X select stratum prov marker ([] : List (QuestionId × Aux)) :=
  fun hR => recordsStratum_nonempty X select stratum prov marker [] hR rfl

/-- **The marker alone does not record either.** With an active occurrence, a
    stratum carrying only the tick marker fails clause 2. -/
theorem marker_only_not_records {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (select : List (Core × Bool) → List QuestionId) (stratum : ℕ) (prov : Provenance)
    (marker : QuestionId) (a : Aux) (i : QuestionId) (hi : i ∈ X.active) (hne : i ≠ marker) :
    ¬ RecordsStratum X select stratum prov marker [(marker, a)] := by
  intro hR
  have := hR.2.1 i hi
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at this
  exact hne this

/-- **A recording stratum exists**, so the predicate is not vacuous: list the
    marker, the parent support, every proposal identifier and the selected
    support, each keyed to a supplied annotation. -/
def canonicalDelta {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (select : List (Core × Bool) → List QuestionId) (stratum : ℕ) (prov : Provenance)
    (marker : QuestionId) (a : Aux) : List (QuestionId × Aux) :=
  ((marker :: X.active) ++
    ((proposals X.archive X.active).map (fun p => (childCore p.1 p.2 stratum prov).id)) ++
    select (proposals X.archive X.active)).map (fun i => (i, a))

theorem canonicalDelta_records {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (select : List (Core × Bool) → List QuestionId) (stratum : ℕ) (prov : Provenance)
    (marker : QuestionId) (a : Aux) :
    RecordsStratum X select stratum prov marker (canonicalDelta X select stratum prov marker a) := by
  have hmap : ∀ i : QuestionId,
      i ∈ ((marker :: X.active) ++
        ((proposals X.archive X.active).map (fun p => (childCore p.1 p.2 stratum prov).id)) ++
        select (proposals X.archive X.active)) →
      i ∈ (canonicalDelta X select stratum prov marker a).map Prod.fst := by
    intro i hi
    unfold canonicalDelta
    rw [List.map_map]
    simpa using hi
  refine ⟨hmap marker (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))),
    ?_, ?_, ?_⟩
  · intro i hi
    exact hmap i (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ hi)))
  · intro q hq
    exact hmap _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hq)))
  · intro i hi
    exact hmap i (List.mem_append_right _ hi)

/-- **The recorded stratum is the segment the advance appends.** `E_{j+1} = E_j ⌢
    ΔE_{j+1}`: dropping the old ledger from the new one returns exactly `Δ`, so
    every identifier `RecordsStratum` requires is in *this* stratum and none of
    them was borrowed from an earlier one. -/
theorem advanceCarrier_stratum {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) :
    (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).ledger.drop X.ledger.length = Δ := by
  change (append X.ledger Δ).drop X.ledger.length = Δ
  unfold append
  simp

/-- **The ledger strictly grows at a recording tick.** Together with the prefix
    theorem this is `E_{j+1} = E_j ⌢ ΔE_{j+1}` with `ΔE_{j+1}` genuinely there:
    no tick writes an invisible stratum. -/
theorem ledger_strictly_grows {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (marker : QuestionId) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _)
    (hR : RecordsStratum X select stratum prov marker Δ) :
    X.ledger.length < (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).ledger.length := by
  have hne := recordsStratum_nonempty X select stratum prov marker Δ hR
  change X.ledger.length < (append X.ledger Δ).length
  unfold append
  rw [List.length_append]
  have : 0 < Δ.length := List.length_pos_iff.mpr hne
  omega

/-! ## The repair `RecordsStratum` was left naming: a recording variant

    **Why `advanceCarrier` itself is untouched.** `Δ` there is a bare argument
    used by every existing caller across this tree; requiring `RecordsStratum`
    on it would change the signature and every call site for a property most
    callers never needed proved. `advanceCarrierRecording` takes the same
    inputs plus one more proof obligation, `hR`, and is definitionally
    `advanceCarrier` — so every fact already proved about `advanceCarrier`
    (its `active_sub_archive` field, `advanceCarrier_stratum`) transfers for
    free, and clause 7's teeth (`recordsStratum_nonempty`) now apply to any
    tick built this way rather than to a hand-checked `Δ`. -/

/-- **The recording variant of Definition 11.6.** Same map as `advanceCarrier`,
    with the caller additionally required to prove the `Δ` they supply actually
    records the stratum Definition 11.6 lists — the repair `RecordsStratum` was
    built to enforce and that `advanceCarrier` alone cannot, since `Δ` there is
    an unconstrained argument. -/
def advanceCarrierRecording {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (marker : QuestionId)
    (Δ : List (QuestionId × Aux))
    (hsel : ∀ i ∈ select (proposals X.archive X.active),
      ∃ p ∈ proposals X.archive X.active, (childCore p.1 p.2 stratum prov).id = i)
    (hfresh : ∀ p ∈ proposals X.archive X.active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive)
    (_hR : RecordsStratum X select stratum prov marker Δ) :
    TickCarrier Aux h :=
  advanceCarrier X hlaw select stratum prov Δ hsel hfresh

/-- The recording variant appends exactly `Δ`, inherited from `advanceCarrier`
    with no new proof. -/
theorem advanceCarrierRecording_stratum {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (marker : QuestionId)
    (Δ : List (QuestionId × Aux)) (hsel : _) (hfresh : _)
    (hR : RecordsStratum X select stratum prov marker Δ) :
    (advanceCarrierRecording X hlaw select stratum prov marker Δ hsel hfresh hR).ledger.drop
        X.ledger.length = Δ :=
  advanceCarrier_stratum X hlaw select stratum prov Δ hsel hfresh

/-- **Clause 7 with teeth, now automatic.** Every tick built through the
    recording variant strictly grows the ledger — not merely a hand-checked
    `Δ` as `ledger_strictly_grows` needed, but every `Δ` the type accepts,
    because `hR` is a field of the call rather than a side condition someone
    might forget to supply. -/
theorem advanceCarrierRecording_grows {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (marker : QuestionId)
    (Δ : List (QuestionId × Aux)) (hsel : _) (hfresh : _)
    (hR : RecordsStratum X select stratum prov marker Δ) :
    X.ledger.length <
      (advanceCarrierRecording X hlaw select stratum prov marker Δ hsel hfresh hR).ledger.length :=
  ledger_strictly_grows X hlaw select stratum prov marker Δ hsel hfresh hR

/-- **The variant is not vacuous.** `canonicalDelta` supplies a `Δ` and its own
    proof of `RecordsStratum`, so the recording variant has a real call at
    every carrier, not only a type that happens to be inhabited by hypothesis. -/
def advanceCarrierRecordingCanonical {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (marker : QuestionId) (a : Aux)
    (hsel : ∀ i ∈ select (proposals X.archive X.active),
      ∃ p ∈ proposals X.archive X.active, (childCore p.1 p.2 stratum prov).id = i)
    (hfresh : ∀ p ∈ proposals X.archive X.active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive) :
    TickCarrier Aux h :=
  advanceCarrierRecording X hlaw select stratum prov marker
    (canonicalDelta X select stratum prov marker a) hsel hfresh
    (canonicalDelta_records X select stratum prov marker a)

#print axioms advanceCarrierRecording
#print axioms advanceCarrierRecording_stratum
#print axioms advanceCarrierRecording_grows
#print axioms advanceCarrierRecordingCanonical

#print axioms Stratified
#print axioms childCore_id_rel_length
#print axioms proposals_parent
#print axioms fresh_of_stratified
#print axioms stratified_archive_step
#print axioms RecordsStratum
#print axioms recordsStratum_nonempty
#print axioms empty_not_records
#print axioms marker_only_not_records
#print axioms canonicalDelta
#print axioms canonicalDelta_records
#print axioms advanceCarrier_stratum
#print axioms ledger_strictly_grows

end G2_12
end Gaps
end RatioSpace
