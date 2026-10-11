/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.RootOrbit
/-!
  Elements II §15, Definition 15.1's schedule, built from the book's own
  selection rule.

  Definition 8.1: form both child proposals of every active
  occurrence, admit on the direct-positive chart, and keep the complete set of
  exact coherence maximizers. `RootOrbit.axiomSelect` is that rule for one
  tick, in the regime of Definition 16.4 and Theorem 16.11: direct-positive
  admission, no declared predicates (`preds := []`) and no cavity-boundary
  term (`RootOrbit.lean`'s header). The seven-tick tables of Theorem 16.5 are
  computed with it. For a question whose cavity actually gates admission this
  is not the complete rule; that regime needs Definition 4.9's boundary test
  in the selector. `axiomPolicyAt` applies it at every carrier the book's
  dynamics reach, at
  stratum `j + 1` for tick `j` and with no event delta, exactly as the
  concrete runs in `RootOrbit.lean` do. Every obligation `AdvanceData` asks is
  discharged here, from the rule and from the run invariant: `hsel` by
  `axiomSelect_hsel`, `hfresh` by Lemma 12.1 (`RunInv.hfresh`), `hcard` by
  retained occurrence identity (`RunInv.hcard`), `hgrow` because the rule only
  filters the `2|S_j|` proposals, `hselNodup` because distinct proposals have
  distinct child identifiers (`proposals_childCore_id_nodup`).

  `axiomPolicy_XL7` (and the `ε`, `R` companions): the general iterate of this
  schedule from Definition 16.4's seed carriers is, carrier for carrier, the
  seven-tick run whose support table Theorem 16.5 certifies. So the general
  §15-§20 theorems stated over `Policy` apply to the book's run.
-/

namespace RatioSpace
namespace Two
namespace AxiomPolicy

open Mat2 Word Frame Pres RatioSpace Advance Accumulation RootOrbit

/-- `axiomSelect` never returns more identifiers than it was given proposals. -/
theorem axiomSelect_length_le (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (props : List (Core × Bool)) :
    (axiomSelect MO stratum prov props).length ≤ props.length := by
  unfold axiomSelect admittedCores
  simp only [List.length_map]
  exact ((List.length_filter_le _ _).trans (List.length_filter_le _ _)).trans
    (List.length_map _).le

/-- `axiomSelect`'s identifiers are a sublist of the proposals' child identifiers. -/
theorem axiomSelect_sublist (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (props : List (Core × Bool)) :
    (axiomSelect MO stratum prov props).Sublist
      (props.map (fun p => (childCore p.1 p.2 stratum prov).id)) := by
  have e : props.map (fun p => (childCore p.1 p.2 stratum prov).id) =
      (props.map (fun p => childCore p.1 p.2 stratum prov)).map Core.id := by
    rw [List.map_map]; rfl
  rw [e]
  exact (List.filter_sublist.trans List.filter_sublist).map Core.id

/-- **Definition 8.1 as a schedule**, under direct-positive admission
    with no cavity-boundary term (the regime of Definition 16.4 and Theorem
    16.11), at any question type and horizon, with every child stamped with
    provenance `prov`. Provenance enters no comparison. -/
def axiomPolicyAt (Aux : Type) (h : ℕ) (prov : Provenance) : Policy Aux h := fun X _ hX =>
  { select := axiomSelect X.observer.matrix ((X.tick : ℕ) + 1) prov
    stratum := (X.tick : ℕ) + 1
    prov := prov
    Δ := []
    hsel := axiomSelect_hsel _ _ _ _
    hfresh := hX.hfresh _ _
    hgrow := by
      have := axiomSelect_length_le X.observer.matrix ((X.tick : ℕ) + 1) prov
        (proposals X.archive X.active)
      rw [proposals_two, hX.hcard] at this
      exact this
    hcard := hX.hcard
    hselNodup :=
      (proposals_childCore_id_nodup hX.1.1 hX.1.2.1 _ prov).sublist
        (axiomSelect_sublist _ _ _ _) }

/-- **The book's schedule for Definition 16.4's questions**: Definition 8.1
     at the seven-tick horizon, children stamped with the seed's own
    provenance, as in `RootOrbit.lean`. -/
def axiomPolicy : Policy Unit hQ := axiomPolicyAt Unit hQ seed164Prov

/-- Standing guard (audit rule 1): the schedule type the general theorems range
    over is inhabited by the book's own rule. -/
example : Nonempty (Policy Unit hQ) := ⟨axiomPolicy⟩

/-- **Definition 16.4's seed carriers are valid tick-zero carriers.** -/
theorem X0_seeded (w : Word) : Seeded (X0 w) :=
  seeded_of_seeds (X0 w) rfl (List.nodup_singleton _)
    (fun c hc => by
      rw [List.mem_singleton.mp hc]; exact seedCore_wellFormed _ _ _ _)
    (fun c hc => by rw [List.mem_singleton.mp hc]; rfl)
    (List.nodup_singleton _)

/-- Two advances agree when their carriers, selectors, strata, provenances and
    deltas agree; the proof arguments are irrelevant. -/
theorem advanceCarrier_congr {Aux : Type} {h : ℕ} {X Y : TickCarrier Aux h} (hXY : X = Y)
    {hlX : Lawful X} {hlY : Lawful Y} {s₁ s₂ : List (Core × Bool) → List QuestionId}
    (hs : s₁ = s₂) {t₁ t₂ : ℕ} (ht : t₁ = t₂) {p₁ p₂ : Provenance} (hp : p₁ = p₂)
    {d₁ d₂ : List (QuestionId × Aux)} (hd : d₁ = d₂)
    {hsel₁ : ∀ i ∈ s₁ (proposals X.archive X.active),
      ∃ p ∈ proposals X.archive X.active, (childCore p.1 p.2 t₁ p₁).id = i}
    {hfr₁ : ∀ p ∈ proposals X.archive X.active, (childCore p.1 p.2 t₁ p₁).id ∉ archIds X.archive}
    {hsel₂ : ∀ i ∈ s₂ (proposals Y.archive Y.active),
      ∃ p ∈ proposals Y.archive Y.active, (childCore p.1 p.2 t₂ p₂).id = i}
    {hfr₂ : ∀ p ∈ proposals Y.archive Y.active, (childCore p.1 p.2 t₂ p₂).id ∉ archIds Y.archive} :
    advanceCarrier X hlX s₁ t₁ p₁ d₁ hsel₁ hfr₁ = advanceCarrier Y hlY s₂ t₂ p₂ d₂ hsel₂ hfr₂ := by
  subst hXY hs ht hp hd; rfl

/-- The observer is carried unchanged along a schedule. -/
theorem iterate_observer {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) : (iterate pol X0 hX0 n hn).observer = X0.observer := by
  induction n with
  | zero => rfl
  | succ k ih => rw [iterate_succ]; exact ih (Nat.le_of_succ_le hn)

/-- **One tick of the book's schedule**, read as the concrete advance
    `RootOrbit.lean` writes: once the iterate at `n` is a given carrier `Y`,
    the iterate at `n + 1` is `Y` advanced by `axiomSelect` at the seed's
    observer, stratum `n + 1`, provenance `seed164Prov`, no event delta. -/
theorem axiomPolicy_step (X0 : TickCarrier Unit hQ) (hs : Seeded X0) (n : ℕ) (hn : n + 1 ≤ hQ)
    (Y : TickCarrier Unit hQ) (hY : iterate axiomPolicy X0 hs n (Nat.le_of_succ_le hn) = Y)
    (hlY : Lawful Y) (sel : List (Core × Bool) → List QuestionId)
    (hsel_eq : sel = axiomSelect X0.observer.matrix (n + 1) seed164Prov)
    (hselY : ∀ i ∈ sel (proposals Y.archive Y.active),
      ∃ p ∈ proposals Y.archive Y.active, (childCore p.1 p.2 (n + 1) seed164Prov).id = i)
    (hfrY : ∀ p ∈ proposals Y.archive Y.active,
      (childCore p.1 p.2 (n + 1) seed164Prov).id ∉ archIds Y.archive) :
    iterate axiomPolicy X0 hs (n + 1) hn = advanceCarrier Y hlY sel (n + 1) seed164Prov [] hselY
      hfrY := by
  rw [iterate_succ]
  have ht := iterate_tick axiomPolicy X0 hs n (Nat.le_of_succ_le hn)
  have ho := iterate_observer axiomPolicy X0 hs n (Nat.le_of_succ_le hn)
  refine advanceCarrier_congr hY ?_ ?_ rfl rfl
  · change axiomSelect (iterate axiomPolicy X0 hs n _).observer.matrix
      (((iterate axiomPolicy X0 hs n _).tick : ℕ) + 1) seed164Prov = sel
    rw [ho, ht, hsel_eq]
  · change ((iterate axiomPolicy X0 hs n _).tick : ℕ) + 1 = n + 1
    rw [ht]

/-- **The general iterate of the book's schedule is, tick for tick, the run of
    `𝒬_L`** whose table Theorem 16.5 certifies (`theorem_16_5_polarized_L`). -/
theorem axiomPolicy_trace_L :
    iterate axiomPolicy (X0 [false]) (X0_seeded _) 1 (by decide) = XL1 ∧
    iterate axiomPolicy (X0 [false]) (X0_seeded _) 2 (by decide) = XL2 ∧
    iterate axiomPolicy (X0 [false]) (X0_seeded _) 3 (by decide) = XL3 ∧
    iterate axiomPolicy (X0 [false]) (X0_seeded _) 4 (by decide) = XL4 ∧
    iterate axiomPolicy (X0 [false]) (X0_seeded _) 5 (by decide) = XL5 ∧
    iterate axiomPolicy (X0 [false]) (X0_seeded _) 6 (by decide) = XL6 ∧
    iterate axiomPolicy (X0 [false]) (X0_seeded _) 7 (by decide) = XL7 := by
  have e1 := axiomPolicy_step (X0 [false]) (X0_seeded _) 0 (by decide) XL0 rfl hlaw0L sel1L rfl
    hsel0L hfresh0L
  have e2 := axiomPolicy_step (X0 [false]) (X0_seeded _) 1 (by decide) XL1 e1 hlaw1L sel2L rfl
    hsel1L hfresh1L
  have e3 := axiomPolicy_step (X0 [false]) (X0_seeded _) 2 (by decide) XL2 e2 hlaw2L sel3L rfl
    hsel2L hfresh2L
  have e4 := axiomPolicy_step (X0 [false]) (X0_seeded _) 3 (by decide) XL3 e3 hlaw3L sel4L rfl
    hsel3L hfresh3L
  have e5 := axiomPolicy_step (X0 [false]) (X0_seeded _) 4 (by decide) XL4 e4 hlaw4L sel5L rfl
    hsel4L hfresh4L
  have e6 := axiomPolicy_step (X0 [false]) (X0_seeded _) 5 (by decide) XL5 e5 hlaw5L sel6L rfl
    hsel5L hfresh5L
  have e7 := axiomPolicy_step (X0 [false]) (X0_seeded _) 6 (by decide) XL6 e6 hlaw6L sel7L rfl
    hsel6L hfresh6L
  exact ⟨e1, e2, e3, e4, e5, e6, e7⟩

/-- The same for `𝒬_ε` (`theorem_16_5_root`). -/
theorem axiomPolicy_trace_eps :
    iterate axiomPolicy (X0 []) (X0_seeded _) 1 (by decide) = Xeps1 ∧
    iterate axiomPolicy (X0 []) (X0_seeded _) 2 (by decide) = Xeps2 ∧
    iterate axiomPolicy (X0 []) (X0_seeded _) 3 (by decide) = Xeps3 ∧
    iterate axiomPolicy (X0 []) (X0_seeded _) 4 (by decide) = Xeps4 ∧
    iterate axiomPolicy (X0 []) (X0_seeded _) 5 (by decide) = Xeps5 ∧
    iterate axiomPolicy (X0 []) (X0_seeded _) 6 (by decide) = Xeps6 ∧
    iterate axiomPolicy (X0 []) (X0_seeded _) 7 (by decide) = Xeps7 := by
  have e1 := axiomPolicy_step (X0 []) (X0_seeded _) 0 (by decide) Xeps0 rfl hlaw0eps sel1eps rfl
    hsel0eps hfresh0eps
  have e2 := axiomPolicy_step (X0 []) (X0_seeded _) 1 (by decide) Xeps1 e1 hlaw1eps sel2eps rfl
    hsel1eps hfresh1eps
  have e3 := axiomPolicy_step (X0 []) (X0_seeded _) 2 (by decide) Xeps2 e2 hlaw2eps sel3eps rfl
    hsel2eps hfresh2eps
  have e4 := axiomPolicy_step (X0 []) (X0_seeded _) 3 (by decide) Xeps3 e3 hlaw3eps sel4eps rfl
    hsel3eps hfresh3eps
  have e5 := axiomPolicy_step (X0 []) (X0_seeded _) 4 (by decide) Xeps4 e4 hlaw4eps sel5eps rfl
    hsel4eps hfresh4eps
  have e6 := axiomPolicy_step (X0 []) (X0_seeded _) 5 (by decide) Xeps5 e5 hlaw5eps sel6eps rfl
    hsel5eps hfresh5eps
  have e7 := axiomPolicy_step (X0 []) (X0_seeded _) 6 (by decide) Xeps6 e6 hlaw6eps sel7eps rfl
    hsel6eps hfresh6eps
  exact ⟨e1, e2, e3, e4, e5, e6, e7⟩

/-- The same for `𝒬_R` (`theorem_16_5_polarized_R`). -/
theorem axiomPolicy_trace_R :
    iterate axiomPolicy (X0 [true]) (X0_seeded _) 1 (by decide) = XR1 ∧
    iterate axiomPolicy (X0 [true]) (X0_seeded _) 2 (by decide) = XR2 ∧
    iterate axiomPolicy (X0 [true]) (X0_seeded _) 3 (by decide) = XR3 ∧
    iterate axiomPolicy (X0 [true]) (X0_seeded _) 4 (by decide) = XR4 ∧
    iterate axiomPolicy (X0 [true]) (X0_seeded _) 5 (by decide) = XR5 ∧
    iterate axiomPolicy (X0 [true]) (X0_seeded _) 6 (by decide) = XR6 ∧
    iterate axiomPolicy (X0 [true]) (X0_seeded _) 7 (by decide) = XR7 := by
  have e1 := axiomPolicy_step (X0 [true]) (X0_seeded _) 0 (by decide) XR0 rfl hlaw0R sel1R rfl
    hsel0R hfresh0R
  have e2 := axiomPolicy_step (X0 [true]) (X0_seeded _) 1 (by decide) XR1 e1 hlaw1R sel2R rfl
    hsel1R hfresh1R
  have e3 := axiomPolicy_step (X0 [true]) (X0_seeded _) 2 (by decide) XR2 e2 hlaw2R sel3R rfl
    hsel2R hfresh2R
  have e4 := axiomPolicy_step (X0 [true]) (X0_seeded _) 3 (by decide) XR3 e3 hlaw3R sel4R rfl
    hsel3R hfresh3R
  have e5 := axiomPolicy_step (X0 [true]) (X0_seeded _) 4 (by decide) XR4 e4 hlaw4R sel5R rfl
    hsel4R hfresh4R
  have e6 := axiomPolicy_step (X0 [true]) (X0_seeded _) 5 (by decide) XR5 e5 hlaw5R sel6R rfl
    hsel5R hfresh5R
  have e7 := axiomPolicy_step (X0 [true]) (X0_seeded _) 6 (by decide) XR6 e6 hlaw6R sel7R rfl
    hsel6R hfresh6R
  exact ⟨e1, e2, e3, e4, e5, e6, e7⟩

/-- **The terminal carrier of the general engine, run by the book's rule from
    the `𝒬_L` seed, is `XL7`.** `Term` is the iterate at the horizon `hQ = 7`. -/
theorem axiomPolicy_XL7 : Term axiomPolicy (X0 [false]) (X0_seeded _) = XL7 :=
  axiomPolicy_trace_L.2.2.2.2.2.2

theorem axiomPolicy_Xeps7 : Term axiomPolicy (X0 []) (X0_seeded _) = Xeps7 :=
  axiomPolicy_trace_eps.2.2.2.2.2.2

theorem axiomPolicy_XR7 : Term axiomPolicy (X0 [true]) (X0_seeded _) = XR7 :=
  axiomPolicy_trace_R.2.2.2.2.2.2

/-- **Theorem 16.5's `𝒬_L` table on the general engine**: the active words of
    the book's schedule at ticks 1 to 7 are those of the certified run, so
    `theorem_16_5_polarized_L` reads off the general iterate unchanged. -/
theorem theorem_16_5_polarized_L_on_policy :
    activeWords (iterate axiomPolicy (X0 [false]) (X0_seeded _) 1 (by decide)) = activeWords XL1 ∧
    activeWords (iterate axiomPolicy (X0 [false]) (X0_seeded _) 2 (by decide)) = activeWords XL2 ∧
    activeWords (iterate axiomPolicy (X0 [false]) (X0_seeded _) 3 (by decide)) = activeWords XL3 ∧
    activeWords (iterate axiomPolicy (X0 [false]) (X0_seeded _) 4 (by decide)) = activeWords XL4 ∧
    activeWords (iterate axiomPolicy (X0 [false]) (X0_seeded _) 5 (by decide)) = activeWords XL5 ∧
    activeWords (iterate axiomPolicy (X0 [false]) (X0_seeded _) 6 (by decide)) = activeWords XL6 ∧
    activeWords (iterate axiomPolicy (X0 [false]) (X0_seeded _) 7 (by decide)) = activeWords XL7
      := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := axiomPolicy_trace_L
  rw [e1, e2, e3, e4, e5, e6, e7]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms axiomSelect_length_le
#print axioms axiomSelect_sublist
#print axioms axiomPolicyAt
#print axioms axiomPolicy
#print axioms X0_seeded
#print axioms axiomPolicy_XL7
#print axioms axiomPolicy_Xeps7
#print axioms axiomPolicy_XR7
#print axioms advanceCarrier_congr
#print axioms iterate_observer
#print axioms axiomPolicy_step
#print axioms axiomPolicy_trace_L
#print axioms axiomPolicy_trace_eps
#print axioms axiomPolicy_trace_R
#print axioms theorem_16_5_polarized_L_on_policy

end AxiomPolicy
end Two
end RatioSpace
