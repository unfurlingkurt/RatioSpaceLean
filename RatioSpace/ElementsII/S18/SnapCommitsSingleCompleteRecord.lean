/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S18.Snap
import RatioSpace.ElementsII.S16.CrystallizationPattern
import RatioSpace.ElementsII.S14.Conservation
/-!
  Gap G2-16 — Elements II §18, Theorem 18.2, Snap commits one complete record.

  **Book statement.** *"A coherent snap is a function on the singleton terminal
  stratum and commits exactly one complete occurrence record. It does not
  reduce the answer to `π_r(x*)`, `C_{h-1}^{(O)}(x*)`, a closure class, or any
  other partial reading."*

  **What was missing.** `snap_isSome_iff` is hypothesis-free but only says the
  snap is defined where `crystallize` is; that this is the singleton stratum
  needed `Nodup` at the terminal carrier. The negative clause had a witness for
  the closure class only.

  **Built here.**
  * `snap_some_singleton`: with **no hypothesis**, a defined snap sits on a
    terminal support whose archive filter is one core `x`, and it commits
    exactly `candidate (Term) evalLedger x` with the whole report.
  * `snap_some_one_identifier`: under `CarrierInv X0` (the book's standing
    identifier discipline, Lemma 12.1, which a bare `TickCarrier` does not
    carry) the terminal support is exactly the one identifier `x.id`.
  * `snap_isSome_iff_singleton_of_carrierInv`: the snap is defined exactly on
    the singleton status, from a tick-zero hypothesis.
  * `piR_is_not_the_record`: two committed candidate records with one relation
    `π_r` and different identifiers, for every seed history.
  * `score_is_not_the_record`: two occurrences with one coherence score
    `C^{(O)}` and different identifiers, at every singleton whose two children
    are admitted (Corollary 8.11's family).
  * `closure_is_not_the_record`: the closure-class witness restated at the
    candidate record.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_16

open Mat2 Word Frame Pres RatioSpace RatioSpace.Two RatioSpace.Two.Advance
  RatioSpace.Two.Accumulation RatioSpace.Two.Terminal RatioSpace.Two.Snap
  RatioSpace.Two.RootOrbit RatioSpace.Two.Beat

/-! ## The singleton stratum, positive half -/

/-- `resolveOcc` returns `x` only from the list `[x]`. -/
theorem resolveOcc_eq_some {α : Type} {S : List α} {x : α} (h : resolveOcc S = some x) :
    S = [x] := by
  match S, h with
  | [y], h =>
    simp only [resolveOcc, Option.some.injEq] at h
    rw [h]

/-- **Theorem 18.2, "a function on the singleton terminal stratum" and
    "exactly one complete occurrence record", with no hypothesis.** If the snap
    commits `p`, then the terminal carrier's archive, filtered by its active
    support, is one core `x`; the first component is `x`'s complete candidate
    record (Definition 6.4: core, keyed ledger entries, parent-closed archive)
    and the second is the whole report (Definition 17.2). -/
theorem snap_some_singleton {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux))
    {p : Cand EvalAux × Report RawAux EvalAux h}
    (hp : snap pol X0 hX0 hh evalLedger = some p) :
    ∃ x : Core, (Term pol X0 hX0).archive.filter (fun c => decide (c.id ∈ (Term pol X0 hX0).active)) = [x] ∧
      p.1 = candidate (Term pol X0 hX0) evalLedger x ∧
      p.2 = Report.of pol X0 hX0 hh evalLedger := by
  have h2 := snap_retains_report pol X0 hX0 hh evalLedger hp
  unfold snap at hp
  cases hc : crystallize pol X0 hX0 hh evalLedger with
  | none => rw [hc] at hp; exact absurd hp (by simp)
  | some y =>
    rw [hc] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    have hens : ensemble (Term pol X0 hX0) evalLedger = [y] := resolveOcc_eq_some hc
    unfold ensemble at hens
    generalize hL : (Term pol X0 hX0).archive.filter
      (fun c => decide (c.id ∈ (Term pol X0 hX0).active)) = L at hens
    match L, hens with
    | [x], hens =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hens
      exact ⟨x, rfl, by rw [← hp, ← hens], h2⟩

/-- **"A singleton occurrence support contains one stable identifier."** Under
    the tick-zero invariant, the terminal active support of a defined snap is
    exactly `[x.id]`. -/
theorem snap_some_one_identifier {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) (hinv0 : CarrierInv X0)
    {p : Cand EvalAux × Report RawAux EvalAux h}
    (hp : snap pol X0 hX0 hh evalLedger = some p) :
    ∃ x : Core, (Term pol X0 hX0).active = [x.id] ∧ x ∈ (Term pol X0 hX0).archive ∧
      p.1 = candidate (Term pol X0 hX0) evalLedger x := by
  obtain ⟨x, hx, h1, _⟩ := snap_some_singleton pol X0 hX0 hh evalLedger hp
  have hinv : CarrierInv (Term pol X0 hX0) := iterate_carrierInv pol X0 hX0 hinv0 h (le_refl h)
  have hlen : (Term pol X0 hX0).active.length = 1 := by
    have e := TickCarrier.ensemble_length_eq_active (Term pol X0 hX0) evalLedger hinv.1 hinv.2.2
    unfold ensemble at e
    rw [hx] at e
    exact e.symm
  have hxmem : x ∈ (Term pol X0 hX0).archive.filter
      (fun c => decide (c.id ∈ (Term pol X0 hX0).active)) := by
    rw [hx]; exact List.Mem.head _
  have hxa := (List.mem_filter.mp hxmem)
  have hid : x.id ∈ (Term pol X0 hX0).active := of_decide_eq_true hxa.2
  refine ⟨x, ?_, hxa.1, h1⟩
  cases hA : (Term pol X0 hX0).active with
  | nil => rw [hA] at hlen; exact absurd hlen (by decide)
  | cons i t =>
    cases t with
    | nil =>
      rw [hA] at hid
      cases hid with
      | head => rfl
      | tail _ h => cases h
    | cons j t' => rw [hA] at hlen; exact absurd (congrArg Nat.pred hlen) (Nat.succ_ne_zero _)

/-- **Theorem 18.2, definedness on the singleton status**, from the tick-zero
    invariant rather than a hypothesis on the terminal carrier. -/
theorem snap_isSome_iff_singleton_of_carrierInv {RawAux EvalAux : Type} {h : ℕ}
    (pol : Policy RawAux h) (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) (hinv0 : CarrierInv X0) :
    (snap pol X0 hX0 hh evalLedger).isSome = true
      ↔ (Report.of pol X0 hX0 hh evalLedger).status = .singleton := by
  rw [snap_isSome_iff]
  exact crystallize_isSome_iff_singleton_of_carrierInv pol X0 hX0 hh evalLedger hinv0

/-! ## The negative half: no partial reading is the record -/

/-- **Not `π_r(x*)`.** For every seed history, two seed occurrences under seed
    identifiers with different seed tags have the same relation projection and
    different complete candidate records, on any carrier and any ledger. A snap
    that committed `π_r` could not say which record it committed. -/
theorem piR_is_not_the_record {RawAux EvalAux : Type} {h : ℕ} (X : TickCarrier RawAux h)
    (ledger : List (QuestionId × EvalRecord EvalAux)) (seed : History) (e : ℕ)
    (pv : Provenance) (i j : QuestionId) (hij : i.seed ≠ j.seed) :
    (candidate X ledger (seedCore i seed e pv)).piR = (candidate X ledger (seedCore j seed e pv)).piR ∧
      candidate X ledger (seedCore i seed e pv) ≠ candidate X ledger (seedCore j seed e pv) := by
  refine ⟨rfl, fun hc => hij ?_⟩
  have hcore := congrArg (fun c : Cand EvalAux => c.core.id.seed) hc
  exact hcore

/-- **Not `C^{(O)}(x*)`.** At every singleton support whose two children are
    admitted and addressed, at any observer, the two children carry the same
    coherence score in the admitted family they are compared in, and they are
    different occurrences. The score does not name the occurrence. -/
theorem score_is_not_the_record {MO : Mat2} {stratum : ℕ} {prov : Provenance}
    {archive : List Core} {active : List QuestionId} {c : Core} (hc : c.WellFormed)
    (hone : archive.filter (fun d => d.id ∈ active) = [c])
    (hadm : ∀ b : Bool, negLoad (Q MO (childCore c b stratum prov).fullMatrix) = 0)
    {yF yT : IPres}
    (hF : addrOf MO (childCore c false stratum prov) = some yF)
    (hT : addrOf MO (childCore c true stratum prov) = some yT) :
    coherenceOf (admittedFam MO stratum prov (proposals archive active)) yF
        = coherenceOf (admittedFam MO stratum prov (proposals archive active)) yT ∧
      (childCore c false stratum prov).id ≠ (childCore c true stratum prov).id := by
  obtain ⟨_, hfam, _, _⟩ := lone_seed_keeps_both hone hadm hF hT
  refine ⟨?_, ?_⟩
  · rw [hfam]
    exact pair_scores_equal yF yT
  · intro hid
    rw [childCore_id c hc, childCore_id c hc] at hid
    exact absurd (child_id_inj hid).2 (by decide)

/-- **Not a closure class**, at the candidate record: for every seed history,
    the two occurrences `RL` and `LR` below one seed share `ψ₁₂` and differ in
    identifier. -/
theorem closure_is_not_the_record (id0 : QuestionId) (seed : History) :
    psi12 (proposal id0 seed [true, false]).fullWord = psi12 (proposal id0 seed [false, true]).fullWord ∧
      (proposal id0 seed [true, false]).id ≠ (proposal id0 seed [false, true]).id :=
  closure_class_is_not_the_record id0 seed

#print axioms resolveOcc_eq_some
#print axioms snap_some_singleton
#print axioms snap_some_one_identifier
#print axioms snap_isSome_iff_singleton_of_carrierInv
#print axioms piR_is_not_the_record
#print axioms score_is_not_the_record
#print axioms closure_is_not_the_record

end G2_16
end Gaps
end RatioSpace
