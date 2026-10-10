/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S12.NewProposalIdentifiersAreLawfulAndDisjoint
/-!
  Gap G2-14 · Elements II Theorem 12.4, one-tick well-typedness.

  The book's proof opens: "The proposal length satisfies `j+1 ≤ h_𝒬`, so each
  proposal lies in the finite whole-cycle proposal domain of Definition 4.2."
  `proposals` was never related to `fullPropDomain`. This file relates them, on
  the carrier invariant of G2-13 together with the one fact a seed lineage never
  changes (every archived core carries a seed of the active context), and then
  assembles Theorem 12.4's conclusions for the advance with Lemma 12.1
  discharged. No existing declaration is changed.
-/

namespace RatioSpace
namespace Gaps
namespace G2_14

open RatioSpace.Two RatioSpace.Two.Advance RatioSpace.Two.Accumulation RatioSpace.Gaps.G2_13

/-- **`Seeds(𝐀)` carries the archive.** Every archived core's seed identifier and
    seed history is one of the active context's seeds. -/
def SeedsCarry {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (seeds : List (QuestionId × History)) : Prop :=
  ∀ c ∈ X.archive, (c.seedId, c.seed) ∈ seeds

/-- A child keeps its parent's seed identifier. -/
theorem childCore_seedId (c : Core) (g : Bool) (e : ℕ) (pv : Provenance) :
    (childCore c g e pv).seedId = c.seedId := rfl

/-- A child keeps its parent's seed history. -/
theorem childCore_seed (c : Core) (g : Bool) (e : ℕ) (pv : Provenance) :
    (childCore c g e pv).seed = c.seed := rfl

/-- One more letter on a relative word of length below the depth lands in the
    seed's proposal domain. -/
theorem childProposal_mem_propDomain (id0 : QuestionId) (seed : History) (v : Word)
    (g : Bool) (D : ℕ) (hv : v.length + 1 ≤ D) :
    childProposal id0 seed v g ∈ propDomain id0 seed D :=
  List.mem_map.mpr
    ⟨v ++ [g],
      mem_wordsUpTo.mpr (by
        rw [List.length_append, List.length_singleton]
        exact hv),
      rfl⟩

/-- **Theorem 12.4, first step.** On a lawful carrier satisfying Lemma 12.1's
    invariant whose archive is carried by `seeds`, the proposal record named by
    every proposal `(x, g)` lies in `Prop_𝒬 = fullPropDomain seeds h`. -/
theorem proposal_mem_fullPropDomain {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (hX : TickLengthInv X) {seeds : List (QuestionId × History)}
    (hS : SeedsCarry X seeds) :
    ∀ p ∈ proposals X.archive X.active,
      childProposal p.1.seedId p.1.seed p.1.relWord p.2 ∈ fullPropDomain seeds h := by
  intro p hp
  obtain ⟨hmem, hact⟩ := mem_proposals_parent hp
  have hlen : p.1.relWord.length + 1 ≤ h := by
    have h1 := hX.2 _ hact
    rw [wellFormed_id_rel (hX.1 _ hmem).1] at h1
    have h2 : (X.tick : ℕ) < h := hlaw
    omega
  exact List.mem_flatMap.mpr
    ⟨(p.1.seedId, p.1.seed), hS _ hmem, childProposal_mem_propDomain _ _ _ _ _ hlen⟩

/-- **The archived core of every proposal is the core of a member of `Prop_𝒬`.** -/
theorem proposal_core_of_fullPropDomain {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (hX : TickLengthInv X) {seeds : List (QuestionId × History)}
    (hS : SeedsCarry X seeds) (stratum : ℕ) (prov : Provenance) :
    ∀ p ∈ proposals X.archive X.active, ∃ y ∈ fullPropDomain seeds h,
      childCore p.1 p.2 stratum prov = Core.ofProposal y (some p.1.id) (some p.2) stratum prov :=
  fun p hp => ⟨_, proposal_mem_fullPropDomain X hlaw hX hS p hp, rfl⟩

/-- One tick keeps the archive carried by the same seeds. -/
theorem seedsCarry_advanceCarrier {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : ∀ i ∈ select (proposals X.archive X.active),
      ∃ p ∈ proposals X.archive X.active, (childCore p.1 p.2 stratum prov).id = i)
    (hfresh : ∀ p ∈ proposals X.archive X.active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive)
    {seeds : List (QuestionId × History)} (hS : SeedsCarry X seeds) :
    SeedsCarry (advanceCarrier X hlaw select stratum prov Δ hsel hfresh) seeds := by
  intro c hc
  change c ∈ advanceArchive X.archive X.active stratum prov at hc
  unfold advanceArchive keyedUnion at hc
  rcases List.mem_append.mp hc with hm | hm
  · exact hS c hm
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hm).1
    exact hS p.1 (mem_proposals_parent hp).1

/-- A seed archive is carried by its seeds. -/
theorem seedsCarry_of_seedCores {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (seeds : List (QuestionId × History)) (entry : ℕ) (prov : Provenance)
    (hA : X.archive = seeds.map (fun s => seedCore s.1 s.2 entry prov)) :
    SeedsCarry X seeds := by
  intro c hc
  rw [hA] at hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
  exact hs

/-- Every carrier a schedule reaches is carried by the tick-zero seeds. -/
theorem iterate_seedsCarry {Aux : Type} {h : ℕ} (pol : Policy Aux h)
    (X0 : TickCarrier Aux h) (hX0 : Seeded X0) {seeds : List (QuestionId × History)}
    (hS0 : SeedsCarry X0 seeds) (n : ℕ) (hn : n ≤ h) :
    SeedsCarry (iterate pol X0 hX0 n hn) seeds := by
  induction n with
  | zero => simpa using hS0
  | succ k ih =>
      rw [iterate_succ]
      exact seedsCarry_advanceCarrier _ _ _ _ _ _ _ _ (ih (Nat.le_of_succ_le hn))

/-- **Theorem 12.4, assembled.** For a lawful carrier satisfying Lemma 12.1's
    invariant, with an archive keyed once per identifier and carried by `seeds`,
    the advance (Lemma 12.1 discharged) has tick `j+1`, the same observer and
    question, every proposal in `Prop_𝒬`, `S_{j+1} ⊆ ids(ℋ_{j+1})`, an archive
    still keyed once per identifier, and again satisfies both invariants, so it
    lies in the domain of the next tick's hypotheses. -/
theorem theorem_12_4 {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) (hlaw : Lawful X)
    (hX : TickLengthInv X) (hnodup : (X.archive.map Core.id).Nodup)
    {seeds : List (QuestionId × History)} (hS : SeedsCarry X seeds)
    (select : List (Core × Bool) → List QuestionId) (stratum : ℕ) (prov : Provenance)
    (Δ : List (QuestionId × Aux))
    (hsel : ∀ i ∈ select (proposals X.archive X.active),
      ∃ p ∈ proposals X.archive X.active, (childCore p.1 p.2 stratum prov).id = i) :
    ((advanceCarrierOfInv X hlaw hX select stratum prov Δ hsel).tick : ℕ) = (X.tick : ℕ) + 1 ∧
    (advanceCarrierOfInv X hlaw hX select stratum prov Δ hsel).observer = X.observer ∧
    (advanceCarrierOfInv X hlaw hX select stratum prov Δ hsel).question = X.question ∧
    (∀ p ∈ proposals X.archive X.active,
      childProposal p.1.seedId p.1.seed p.1.relWord p.2 ∈ fullPropDomain seeds h) ∧
    (∀ i ∈ (advanceCarrierOfInv X hlaw hX select stratum prov Δ hsel).active,
      i ∈ archIds (advanceCarrierOfInv X hlaw hX select stratum prov Δ hsel).archive) ∧
    ((advanceCarrierOfInv X hlaw hX select stratum prov Δ hsel).archive.map Core.id).Nodup ∧
    TickLengthInv (advanceCarrierOfInv X hlaw hX select stratum prov Δ hsel) ∧
    SeedsCarry (advanceCarrierOfInv X hlaw hX select stratum prov Δ hsel) seeds :=
  ⟨rfl, rfl, rfl, proposal_mem_fullPropDomain X hlaw hX hS,
    (advanceCarrierOfInv X hlaw hX select stratum prov Δ hsel).active_sub_archive,
    advanceArchive_nodup hnodup (fun c hc => (hX.1 c hc).1),
    tickLengthInv_advanceCarrier X hlaw select stratum prov Δ hsel _ hX,
    seedsCarry_advanceCarrier X hlaw select stratum prov Δ hsel _ hS⟩

#print axioms SeedsCarry
#print axioms childCore_seedId
#print axioms childCore_seed
#print axioms childProposal_mem_propDomain
#print axioms proposal_mem_fullPropDomain
#print axioms proposal_core_of_fullPropDomain
#print axioms seedsCarry_advanceCarrier
#print axioms seedsCarry_of_seedCores
#print axioms iterate_seedsCarry
#print axioms theorem_12_4

end G2_14
end Gaps
end RatioSpace
