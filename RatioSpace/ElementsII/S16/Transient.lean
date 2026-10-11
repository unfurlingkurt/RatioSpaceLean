/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.RootOrbit
/-!
  Elements II §16 Proposition 16.13 — Ties before capture: the displayed
  instances (the general tie criterion is `Tie1613.prop_16_13_tie`).

  **What is built: the four displayed instances, each one advance from a
  multi-seed ensemble at observer `ε`, run through the same `advanceCarrier`
  and `axiomSelect` as `Two/RootOrbit.lean`.** For each instance the file
  decides the next support's words (in the kernel's list order, read off the
  run before being stated), the admitted family's addresses, its full tension
  matrix, every member's exact `Zphi` coherence value, the sorted tension histograms,
  and the strict comparisons against every rejected member.

  **The multi-seed form used.** The tree has no multi-seed constructor:
  `canonicalQuestion` and `X0` take one seed word. Definition 4.8's `S0tilde`
  already fixes the honest shape of an ensemble at tick 0: a list of
  `(QuestionId × History)` seeds, each read as its own relative-empty
  proposal record. `ensCores` below is exactly that list archived as seed
  cores, each seed under its own seed identifier `⟨0, 0, k, []⟩`, and `E0`
  is the tick-0 carrier whose active list is every one of them. The question
  record is `canonicalQuestion []` with its `active` field replaced by the
  ensemble's histories; nothing downstream reads that field
  (`RootOrbit.lean`'s header). Children are then built by `childCore`
  from each seed's own `seedId` and `seed`, so the child `LL` of the seed `L`
  and the seed `LL` itself are different occurrences with different
  identifiers, which instance 3 needs. `ens_archive_is_S0tilde_ids` checks
  that the archived identifiers are exactly Definition 4.8's proposal
  identifiers.

  **Not built, and named.** The proposition's enumerations (2,092,036 pairs
  to length 10, the random samples, the 39,711 triples, and the rest) are
  not kernel-checkable without `native_decide`, which is not used. The
  Remark's open question is not touched.
-/
set_option linter.style.longLine false
set_option maxRecDepth 200000

namespace RatioSpace
namespace Two
namespace Transient

open Mat2 Word Frame Pres RatioSpace RatioSpace.Zphi Advance Accumulation RootOrbit

/-! ## The tick-zero ensemble carrier -/

/-- The `k`-th seed's identifier. `ensSeedId 0 = seed164Id`. -/
def ensSeedId (k : ℕ) : QuestionId := ⟨0, 0, k, []⟩

/-- Definition 4.8's seed list for an ensemble of words over the canonical
    frame: one `(identifier, history)` pair per word, distinct identifiers. -/
def ensSeeds : ℕ → List Word → List (QuestionId × History)
  | _, [] => []
  | k, w :: ws => (ensSeedId k, ⟨Frame.empty, w⟩) :: ensSeeds (k + 1) ws

/-- The ensemble's seeds, archived as seed cores (Definition 6.1). -/
def ensCores (ws : List Word) : List Core :=
  (ensSeeds 0 ws).map (fun p => seedCore p.1 p.2 0 ⟨seed164Id, p.1, ⟨0, 0⟩⟩)

/-- The ensemble question: Definition 16.4's record with the ensemble's
    histories as its active field. -/
def ensQuestion (ws : List Word) : ExtendedQuestion Unit :=
  { canonicalQuestion [] with active := ws.map (fun w => ⟨Frame.empty, w⟩) }

/-- **The tick-zero carrier of an ensemble.** Every seed archived, every seed
    active, empty ledger, observer `ε`. -/
def E0 (ws : List Word) : TickCarrier Unit hQ where
  observer := observer164
  question := ensQuestion ws
  tick := ⟨0, by decide⟩
  active := archIds (ensCores ws)
  archive := ensCores ws
  ledger := []
  active_sub_archive := fun _ hi => hi

/-- **The archived identifiers are Definition 4.8's.** Each seed core carries
    the identifier of its own relative-empty proposal record, the objects
    `S0tilde` filters. -/
theorem ens_archive_is_S0tilde_ids (ws : List Word) :
    archIds (E0 ws).archive = (ensSeeds 0 ws).map (fun p => (proposal p.1 p.2 []).id) := by
  simp only [E0, ensCores, archIds, List.map_map]
  rfl

/-! ## Instance 1 — `{LLRRLL, LRRLLL}`: a four-member support -/

def W1 : List Word := [[false, false, true, true, false, false], [false, true, true, false, false, false]]
def X1 : TickCarrier Unit hQ := E0 W1
def MO1 : Mat2 := X1.observer.matrix
theorem hlaw1 : Lawful X1 := by decide
def props1 : List (Core × Bool) := proposals X1.archive X1.active
def sel1 : List (Core × Bool) → List QuestionId := axiomSelect MO1 1 seed164Prov
theorem hsel1 : ∀ i ∈ sel1 props1, ∃ p ∈ props1, (childCore p.1 p.2 1 seed164Prov).id = i :=
  axiomSelect_hsel MO1 1 seed164Prov props1
theorem hfresh1 : ∀ p ∈ props1, (childCore p.1 p.2 1 seed164Prov).id ∉ archIds X1.archive := by
  decide
def X1' : TickCarrier Unit hQ := advanceCarrier X1 hlaw1 sel1 1 seed164Prov [] hsel1 hfresh1
def fam1 : List IPres := admittedFam MO1 1 seed164Prov props1

/-- **Proposition 16.13, instance 1.** The next support has four members,
    both sibling pairs: `LLRRLLL, LLRRLLR, LRRLLLL, LRRLLLR`. All four
    tension rows have histogram `{0,13,26,87}` and all four coherence value exactly
    `-1100087778365905889 + 679891637638491098φ`. -/
theorem prop_16_13_i :
    activeWords X1' =
      [[false, false, true, true, false, false, false], [false, false, true, true, false, false, true],
       [false, true, true, false, false, false, false], [false, true, true, false, false, false, true]] ∧
    fam1.map (fun y => (y.p, y.q)) = [(9, 22), (12, 29), (11, 16), (16, 23)] ∧
    fam1.map (tensions fam1) =
      [[0, 87, 13, 26], [87, 0, 26, 13], [13, 26, 0, 87], [26, 13, 87, 0]] ∧
    (fam1.map (tensions fam1)).map (List.insertionSort (· ≤ ·)) =
      [[0, 13, 26, 87], [0, 13, 26, 87], [0, 13, 26, 87], [0, 13, 26, 87]] ∧
    fam1.map (coherenceOf fam1) =
      [(⟨-1100087778365905889, 679891637638491098⟩ : Zphi), ⟨-1100087778365905889, 679891637638491098⟩,
       ⟨-1100087778365905889, 679891637638491098⟩, ⟨-1100087778365905889, 679891637638491098⟩] ∧
    (support fam1).length = 4 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Instance 2 — `{LRL, LLLLR}`: a cross pair -/

def W2 : List Word := [[false, true, false], [false, false, false, false, true]]
def X2 : TickCarrier Unit hQ := E0 W2
def MO2 : Mat2 := X2.observer.matrix
theorem hlaw2 : Lawful X2 := by decide
def props2 : List (Core × Bool) := proposals X2.archive X2.active
def sel2 : List (Core × Bool) → List QuestionId := axiomSelect MO2 1 seed164Prov
theorem hsel2 : ∀ i ∈ sel2 props2, ∃ p ∈ props2, (childCore p.1 p.2 1 seed164Prov).id = i :=
  axiomSelect_hsel MO2 1 seed164Prov props2
theorem hfresh2 : ∀ p ∈ props2, (childCore p.1 p.2 1 seed164Prov).id ∉ archIds X2.archive := by
  decide
def X2' : TickCarrier Unit hQ := advanceCarrier X2 hlaw2 sel2 1 seed164Prov [] hsel2 hfresh2
def fam2 : List IPres := admittedFam MO2 1 seed164Prov props2

/-- **Proposition 16.13, instance 2.** The next support is the cross pair,
    in kernel order `[LRLL, LLLLRL]` (the book writes `{LLLLRL, LRLL}`), one
    child from each seed. The selected pair shares histogram `{0,4,13,13}`
    and coherence value `-748 + 463φ`; the rejected pair `LRLR, LLLLRR` shares
    `{0,9,13,13}` and `-808 + 500φ`. -/
theorem prop_16_13_ii :
    activeWords X2' = [[false, true, false, false], [false, false, false, false, true, false]] ∧
    fam2.map (fun y => (y.p, y.q)) = [(4, 7), (5, 8), (3, 14), (3, 13)] ∧
    fam2.map (tensions fam2) =
      [[0, 13, 4, 13], [13, 0, 13, 9], [4, 13, 0, 13], [13, 9, 13, 0]] ∧
    (fam2.map (tensions fam2)).map (List.insertionSort (· ≤ ·)) =
      [[0, 4, 13, 13], [0, 9, 13, 13], [0, 4, 13, 13], [0, 9, 13, 13]] ∧
    fam2.map (coherenceOf fam2) =
      [(⟨-748, 463⟩ : Zphi), ⟨-808, 500⟩, ⟨-748, 463⟩, ⟨-808, 500⟩] ∧
    (support fam2).map (fun y => (y.p, y.q)) = [(4, 7), (3, 14)] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Instance 2's selected coherence value strictly exceeds its rejected coherence value. -/
theorem prop_16_13_ii_strict : (⟨-808, 500⟩ : Zphi) < (⟨-748, 463⟩ : Zphi) := by decide

/-! ## Instance 3 — `{L, LL, LLL}`: three occurrences at `-1 + 2φ` -/

def W3 : List Word := [[false], [false, false], [false, false, false]]
def X3 : TickCarrier Unit hQ := E0 W3
def MO3 : Mat2 := X3.observer.matrix
theorem hlaw3 : Lawful X3 := by decide
def props3 : List (Core × Bool) := proposals X3.archive X3.active
def sel3 : List (Core × Bool) → List QuestionId := axiomSelect MO3 1 seed164Prov
theorem hsel3 : ∀ i ∈ sel3 props3, ∃ p ∈ props3, (childCore p.1 p.2 1 seed164Prov).id = i :=
  axiomSelect_hsel MO3 1 seed164Prov props3
theorem hfresh3 : ∀ p ∈ props3, (childCore p.1 p.2 1 seed164Prov).id ∉ archIds X3.archive := by
  decide
def X3' : TickCarrier Unit hQ := advanceCarrier X3 hlaw3 sel3 1 seed164Prov [] hsel3 hfresh3
def fam3 : List IPres := admittedFam MO3 1 seed164Prov props3

/-- **Proposition 16.13, instance 3, exactly the book's values.** Admitted
    family `[LL, LR, LLL, LLR, LLLL, LLLR]` (children of `L`, then `LL`, then
    `LLL`). The next support, in kernel order, is `[LL, LR, LLR]` (the book
    writes `{LL, LLR, LR}`), with histograms `{0,1,3,3,5,6}`,
    `{0,1,3,4,4,5}`, `{0,1,3,4,4,5}` and common coherence value `-1 + 2φ`. -/
theorem prop_16_13_iii :
    activeWords X3' = [[false, false], [false, true], [false, false, true]] ∧
    fam3.map (fun y => (y.p, y.q)) = [(1, 3), (2, 3), (1, 4), (2, 5), (1, 5), (2, 7)] ∧
    fam3.map (tensions fam3) =
      [[0, 1, 3, 5, 3, 6], [1, 0, 4, 3, 5, 4], [3, 4, 0, 4, 4, 7],
       [5, 3, 4, 0, 1, 4], [3, 5, 4, 1, 0, 5], [6, 4, 7, 4, 5, 0]] ∧
    (fam3.map (tensions fam3)).map (List.insertionSort (· ≤ ·)) =
      [[0, 1, 3, 3, 5, 6], [0, 1, 3, 4, 4, 5], [0, 3, 4, 4, 4, 7],
       [0, 1, 3, 4, 4, 5], [0, 1, 3, 4, 5, 5], [0, 4, 4, 5, 6, 7]] ∧
    fam3.map (coherenceOf fam3) =
      [(⟨-1, 2⟩ : Zphi), ⟨-1, 2⟩, ⟨-8, 6⟩, ⟨-1, 2⟩, ⟨-14, 10⟩, ⟨-5, 4⟩] ∧
    (support fam3).map (fun y => (y.p, y.q)) = [(1, 3), (2, 3), (2, 5)] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Instance 3: `-1 + 2φ` strictly exceeds each of the three rejected coherence values. -/
theorem prop_16_13_iii_strict :
    (⟨-8, 6⟩ : Zphi) < (⟨-1, 2⟩ : Zphi) ∧ (⟨-14, 10⟩ : Zphi) < (⟨-1, 2⟩ : Zphi) ∧
    (⟨-5, 4⟩ : Zphi) < (⟨-1, 2⟩ : Zphi) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## Instance 4 — `{L, LLR}`: a sibling pair at `26 - 15φ` from distinct histograms -/

def W4 : List Word := [[false], [false, false, true]]
def X4 : TickCarrier Unit hQ := E0 W4
def MO4 : Mat2 := X4.observer.matrix
theorem hlaw4 : Lawful X4 := by decide
def props4 : List (Core × Bool) := proposals X4.archive X4.active
def sel4 : List (Core × Bool) → List QuestionId := axiomSelect MO4 1 seed164Prov
theorem hsel4 : ∀ i ∈ sel4 props4, ∃ p ∈ props4, (childCore p.1 p.2 1 seed164Prov).id = i :=
  axiomSelect_hsel MO4 1 seed164Prov props4
theorem hfresh4 : ∀ p ∈ props4, (childCore p.1 p.2 1 seed164Prov).id ∉ archIds X4.archive := by
  decide
def X4' : TickCarrier Unit hQ := advanceCarrier X4 hlaw4 sel4 1 seed164Prov [] hsel4 hfresh4
def fam4 : List IPres := admittedFam MO4 1 seed164Prov props4

/-- **Proposition 16.13, instance 4, exactly the book's values.** Admitted
    family `[LL, LR, LLRL, LLRR]`. The next support is the sibling pair
    `[LL, LR]`, whose histograms `{0,1,5,8}` and `{0,1,6,6}` differ and whose
    coherence values are both exactly `26 - 15φ`: the `{p,p}` against `{p-1,p+2}`
    collision with `p = 6` (Lemma 16.14's Bergman–Parry clause), since the
    shared terms `0, 1` cancel. -/
theorem prop_16_13_iv :
    activeWords X4' = [[false, false], [false, true]] ∧
    fam4.map (fun y => (y.p, y.q)) = [(1, 3), (2, 3), (3, 8), (3, 7)] ∧
    fam4.map (tensions fam4) =
      [[0, 1, 8, 5], [1, 0, 6, 6], [8, 6, 0, 7], [5, 6, 7, 0]] ∧
    (fam4.map (tensions fam4)).map (List.insertionSort (· ≤ ·)) =
      [[0, 1, 5, 8], [0, 1, 6, 6], [0, 6, 7, 8], [0, 5, 6, 7]] ∧
    fam4.map (coherenceOf fam4) =
      [(⟨26, -15⟩ : Zphi), ⟨26, -15⟩, ⟨27, -16⟩, ⟨-15, 10⟩] ∧
    (support fam4).map (fun y => (y.p, y.q)) = [(1, 3), (2, 3)] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Instance 4: `26 - 15φ` strictly exceeds both rejected coherence values. -/
theorem prop_16_13_iv_strict :
    (⟨27, -16⟩ : Zphi) < (⟨26, -15⟩ : Zphi) ∧ (⟨-15, 10⟩ : Zphi) < (⟨26, -15⟩ : Zphi) := by
  refine ⟨by decide, by decide⟩

/-- **The collision behind instance 4, as exact arithmetic.** `φ⁻⁵ + φ⁻⁸ =
    φ⁻⁶ + φ⁻⁶`, the pattern `{p-1,p+2}` against `{p,p}` at `p = 6`. -/
theorem prop_16_13_iv_collision : phiNegPow 5 + phiNegPow 8 = phiNegPow 6 + phiNegPow 6 := by
  decide

#print axioms ens_archive_is_S0tilde_ids
#print axioms prop_16_13_i
#print axioms prop_16_13_ii
#print axioms prop_16_13_ii_strict
#print axioms prop_16_13_iii
#print axioms prop_16_13_iii_strict
#print axioms prop_16_13_iv
#print axioms prop_16_13_iv_strict
#print axioms prop_16_13_iv_collision

end Transient
end Two
end RatioSpace
