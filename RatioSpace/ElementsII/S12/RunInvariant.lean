/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S14.Conservation
/-!
  Lemma 12.1's invariant, at the level of one carrier, placed below
  `Accumulation.lean` so that §15's schedule can be asked to act only on
  carriers that satisfy it.

  Elements II builds every carrier from the seed by lawful ticks (Definition
  15.1: the iterate starts from "the valid tick-zero carrier constructed from
  the support-free initialization context of Section 4"). Two facts about such
  carriers are derived in the book rather than assumed: new proposal
  identifiers are fresh (Lemma 12.1), and each active identifier tags one
  archived occurrence (occurrence identity is retained, Corollary 6.10, and the
  archive is keyed, Definition 11.6). `TickLengthInv` is the book's own proof
  invariant for the first. `hcard_of_nodup` below derives the second from
  duplicate-free archive and support.

  The declarations live in the `Gaps.G2_13` namespace. The schedule-level
  consequences (`iterate_tickLengthInv`, `iterate_hfresh`) are in
  `NewProposalIdentifiersAreLawfulAndDisjoint.lean`.
-/
set_option linter.style.show false

namespace RatioSpace
namespace Gaps
namespace G2_13

open RatioSpace.Two RatioSpace.Two.Advance
/-- **Lemma 12.1's invariant.** Every archived core is well-formed and its
    identifier's relative word is no longer than the tick; every active
    identifier's relative word has length exactly the tick. -/
def TickLengthInv {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) : Prop :=
  (∀ c ∈ X.archive, c.WellFormed ∧ c.id.rel.length ≤ (X.tick : ℕ)) ∧
  (∀ i ∈ X.active, i.rel.length = (X.tick : ℕ))

/-- A well-formed core's identifier carries its own relative word. -/
theorem wellFormed_id_rel {c : Core} (hc : c.WellFormed) : c.id.rel = c.relWord := by
  rw [hc.2.2.2.2.1]; rfl

/-- A proposal's parent is archived and active. -/
theorem mem_proposals_parent {archive : List Core} {active : List QuestionId}
    {p : Core × Bool} (hp : p ∈ proposals archive active) :
    p.1 ∈ archive ∧ p.1.id ∈ active := by
  unfold proposals at hp
  obtain ⟨c, hc, hpc⟩ := List.mem_flatMap.mp hp
  have hc' := List.mem_filter.mp hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl <;> exact ⟨hc'.1, by simpa using hc'.2⟩

/-- **"A proposal at the current advance has length `j+1` from its seed."** -/
theorem proposal_child_rel_length {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hX : TickLengthInv X) {p : Core × Bool} (hp : p ∈ proposals X.archive X.active)
    (stratum : ℕ) (prov : Provenance) :
    (childCore p.1 p.2 stratum prov).id.rel.length = (X.tick : ℕ) + 1 := by
  obtain ⟨hmem, hact⟩ := mem_proposals_parent hp
  rw [childCore_id p.1 (hX.1 _ hmem).1, child_rel_length, hX.2 _ hact]

/-- **Lemma 12.1, disjointness from the existing archive, discharged.** Under the
    invariant, no proposal identifier is already archived: this is `hfresh`. -/
theorem hfresh_of_tickLengthInv {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hX : TickLengthInv X) (stratum : ℕ) (prov : Provenance) :
    ∀ p ∈ proposals X.archive X.active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive := by
  intro p hp hmem
  obtain ⟨c, hc, hcid⟩ := List.mem_map.mp hmem
  have h1 := proposal_child_rel_length X hX hp stratum prov
  have h2 := (hX.1 c hc).2
  rw [hcid] at h2
  omega

/-- **Lemma 12.1, whole.** On a carrier satisfying the invariant whose archive
    keys each identifier once: every proposal core is well-formed, none of its
    identifiers is already archived, and distinct proposals have distinct
    identifiers. -/
theorem lemma_12_1 {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) (hX : TickLengthInv X)
    (hnodup : (X.archive.map Core.id).Nodup) (stratum : ℕ) (prov : Provenance) :
    (∀ p ∈ proposals X.archive X.active,
        (childCore p.1 p.2 stratum prov).WellFormed ∧
        (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive) ∧
    ((proposals X.archive X.active).map
        (fun p => (childCore p.1 p.2 stratum prov).id)).Nodup :=
  ⟨fun p hp => ⟨childCore_wellFormed _ _ _ _, hfresh_of_tickLengthInv X hX stratum prov p hp⟩,
    proposals_childCore_id_nodup hnodup (fun c hc => (hX.1 c hc).1) stratum prov⟩

/-- **The one-tick advance with Lemma 12.1 discharged.** `advanceCarrier` with its
    `hfresh` argument supplied by the invariant rather than by the caller. -/
def advanceCarrierOfInv {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) (hlaw : Lawful X)
    (hX : TickLengthInv X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : ∀ i ∈ select (proposals X.archive X.active),
      ∃ p ∈ proposals X.archive X.active, (childCore p.1 p.2 stratum prov).id = i) :
    TickCarrier Aux h :=
  advanceCarrier X hlaw select stratum prov Δ hsel (hfresh_of_tickLengthInv X hX stratum prov)

/-- **One tick preserves the invariant**, whatever proof of `hfresh` was used. -/
theorem tickLengthInv_advanceCarrier {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : ∀ i ∈ select (proposals X.archive X.active),
      ∃ p ∈ proposals X.archive X.active, (childCore p.1 p.2 stratum prov).id = i)
    (hfresh : ∀ p ∈ proposals X.archive X.active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive)
    (hX : TickLengthInv X) :
    TickLengthInv (advanceCarrier X hlaw select stratum prov Δ hsel hfresh) := by
  refine ⟨?_, ?_⟩
  · intro c hc
    change c ∈ advanceArchive X.archive X.active stratum prov at hc
    show c.WellFormed ∧ c.id.rel.length ≤ (X.tick : ℕ) + 1
    unfold advanceArchive keyedUnion at hc
    rcases List.mem_append.mp hc with hmem | hmem
    · exact ⟨(hX.1 c hmem).1, by have := (hX.1 c hmem).2; omega⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hmem).1
      exact ⟨childCore_wellFormed _ _ _ _, (proposal_child_rel_length X hX hp stratum prov).le⟩
  · intro i hi
    change i ∈ select (proposals X.archive X.active) at hi
    show i.rel.length = (X.tick : ℕ) + 1
    obtain ⟨p, hp, rfl⟩ := hsel i hi
    exact proposal_child_rel_length X hX hp stratum prov

/-- **The invariant at a seed carrier.** At tick `0`, an archive of well-formed
    cores with empty relative words (seeds) satisfies it; the active clause
    follows from `active_sub_archive`. -/
theorem tickLengthInv_of_seeds {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (h0 : (X.tick : ℕ) = 0) (hwf : ∀ c ∈ X.archive, c.WellFormed)
    (hseed : ∀ c ∈ X.archive, c.relWord = []) : TickLengthInv X := by
  refine ⟨fun c hc => ⟨hwf c hc, ?_⟩, fun i hi => ?_⟩
  · rw [h0, wellFormed_id_rel (hwf c hc), hseed c hc]; rfl
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (X.active_sub_archive i hi)
    rw [h0, wellFormed_id_rel (hwf c hc), hseed c hc]; rfl


/-! ## The same invariant on bare archive/support lists

    `Step5Induction.run` iterates the archive and active support without a
    carrier around them; Theorem 16.11 needs Lemma 12.1 there too. -/

/-- **Lemma 12.1's invariant on lists, at depth `ℓ`.** Every archived core is
    well-formed with relative word no longer than `ℓ`; every active identifier
    has relative word of length exactly `ℓ`. `TickLengthInv X` is this at
    `ℓ = X.tick`. -/
def DepthInv (archive : List Core) (active : List QuestionId) (ℓ : ℕ) : Prop :=
  (∀ c ∈ archive, c.WellFormed ∧ c.id.rel.length ≤ ℓ) ∧ (∀ i ∈ active, i.rel.length = ℓ)

theorem tickLengthInv_iff_depthInv {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) :
    TickLengthInv X ↔ DepthInv X.archive X.active X.tick := Iff.rfl

/-- A proposal at depth `ℓ` has a child at depth `ℓ + 1`. -/
theorem depthInv_child_rel_length {archive : List Core} {active : List QuestionId} {ℓ : ℕ}
    (hX : DepthInv archive active ℓ) {p : Core × Bool} (hp : p ∈ proposals archive active)
    (stratum : ℕ) (prov : Provenance) :
    (childCore p.1 p.2 stratum prov).id.rel.length = ℓ + 1 := by
  obtain ⟨hmem, hact⟩ := mem_proposals_parent hp
  rw [childCore_id p.1 (hX.1 _ hmem).1, child_rel_length, hX.2 _ hact]

/-- **Lemma 12.1 on lists.** No proposal identifier is already archived. -/
theorem hfresh_of_depthInv {archive : List Core} {active : List QuestionId} {ℓ : ℕ}
    (hX : DepthInv archive active ℓ) (stratum : ℕ) (prov : Provenance) :
    ∀ p ∈ proposals archive active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds archive := by
  intro p hp hmem
  obtain ⟨c, hc, hcid⟩ := List.mem_map.mp hmem
  have h1 := depthInv_child_rel_length hX hp stratum prov
  have h2 := (hX.1 c hc).2
  rw [hcid] at h2
  omega

/-- **One advance of the archive and support keeps the invariant, one level
    deeper**, for any support that picks children of the proposals. -/
theorem depthInv_step {archive : List Core} {active : List QuestionId} {ℓ : ℕ}
    (hX : DepthInv archive active ℓ) (stratum : ℕ) (prov : Provenance)
    (next : List QuestionId)
    (hnext : ∀ i ∈ next, ∃ p ∈ proposals archive active,
      (childCore p.1 p.2 stratum prov).id = i) :
    DepthInv (advanceArchive archive active stratum prov) next (ℓ + 1) := by
  refine ⟨?_, ?_⟩
  · intro c hc
    unfold advanceArchive keyedUnion at hc
    rcases List.mem_append.mp hc with hmem | hmem
    · exact ⟨(hX.1 c hmem).1, by have := (hX.1 c hmem).2; omega⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hmem).1
      exact ⟨childCore_wellFormed _ _ _ _, (depthInv_child_rel_length hX hp stratum prov).le⟩
  · intro i hi
    obtain ⟨p, hp, rfl⟩ := hnext i hi
    exact depthInv_child_rel_length hX hp stratum prov

/-- **A seed archive is at depth `0`.** Well-formed cores with empty relative
    words, and a support drawn from their identifiers. -/
theorem depthInv_of_seeds {archive : List Core} {active : List QuestionId}
    (hwf : ∀ c ∈ archive, c.WellFormed) (hseed : ∀ c ∈ archive, c.relWord = [])
    (hsub : ∀ i ∈ active, i ∈ archIds archive) : DepthInv archive active 0 := by
  refine ⟨fun c hc => ⟨hwf c hc, ?_⟩, fun i hi => ?_⟩
  · rw [wellFormed_id_rel (hwf c hc), hseed c hc]; rfl
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (hsub i hi)
    rw [wellFormed_id_rel (hwf c hc), hseed c hc]; rfl

/-! ## Each active identifier tags one archived occurrence -/

/-- **`|S_j|` counted in the archive is `|S_j|`**, on a carrier whose archive
    identifiers and support are duplicate-free: the filter of the archive by
    the support lists exactly the support's occurrences, once each. This is
    `AdvanceData.hcard`, derived rather than asked. -/
theorem hcard_of_nodup {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (harch : (X.archive.map Core.id).Nodup) (hact : X.active.Nodup) :
    (X.archive.filter (fun c => c.id ∈ X.active)).length = X.active.length := by
  have hnd : ((X.archive.filter (fun c => c.id ∈ X.active)).map Core.id).Nodup := by
    rw [filter_id_eq_map_filter]; exact harch.filter _
  have h1 : ((X.archive.filter (fun c => c.id ∈ X.active)).map Core.id) ⊆ X.active := by
    intro i hi
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hi
    simpa using (List.mem_filter.mp hc).2
  have h2 : X.active ⊆ ((X.archive.filter (fun c => c.id ∈ X.active)).map Core.id) := by
    intro i hi
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (X.active_sub_archive i hi)
    exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, by simpa using hi⟩, rfl⟩
  have := (hnd.subperm h1).length_le
  have := (hact.subperm h2).length_le
  rw [List.length_map] at *
  omega

#print axioms TickLengthInv
#print axioms wellFormed_id_rel
#print axioms mem_proposals_parent
#print axioms proposal_child_rel_length
#print axioms hfresh_of_tickLengthInv
#print axioms lemma_12_1
#print axioms advanceCarrierOfInv
#print axioms tickLengthInv_advanceCarrier
#print axioms tickLengthInv_of_seeds
#print axioms depthInv_child_rel_length
#print axioms hfresh_of_depthInv
#print axioms depthInv_step
#print axioms depthInv_of_seeds
#print axioms hcard_of_nodup

end G2_13
end Gaps
end RatioSpace
