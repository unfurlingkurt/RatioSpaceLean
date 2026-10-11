/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.Anchored
/-!
  Elements II §16, Remark 16.18: anchored profiles keep ties.

  The remark says that under an anchored comparison profile (Definition 8.1's
  extended profile, `Anchored.anchoredSelect`) "ties are relocated, not
  removed". `Anchored.lean` decides the collapses of `𝒬_L`, `𝒬_R`, `𝒬_LL`
  and the unchanged root runs; this file decides one anchored tie for each
  profile, so the clause is a statement about named declarations:

  * **Seed anchor, a tie at another question.** The lone-seed question `𝒬_RL`
    (seed word `RL`) under the seed anchor is a singleton at ticks 1 to 4
    (the ray `RL^k`) and at tick 5 retains the pair `{RL^6, RL^5 R}` with equal
    anchored coherence values (`remark_16_18_seed_anchor_tie_RL`). The root question
    under the seed anchor also keeps its pair at tick 7
    (`remark_16_18_seed_anchor_tie_root`).
  * **Support anchor, the root tie is kept.** The root question under the
    current-support profile retains the pair `{LR^6, RL^6}` at tick 7 with
    equal anchored coherence values (`remark_16_18_support_anchor_tie_root`).

  What this file does not state: that under the support profile a tie occurs
  at any question other than the root. A script scan of all seeds of length at
  most 7 over 7 ticks finds none (only the root pair appears), so for that
  profile the statement decided here is the root tie kept, not a tie at
  another question.
-/

set_option maxRecDepth 200000

namespace RatioSpace
namespace Gaps
namespace R16_18

open Mat2 Word Frame Pres RatioSpace RatioSpace.Zphi RatioSpace.Two RatioSpace.Two.Advance
  RatioSpace.Two.Accumulation RatioSpace.Two.RootOrbit RatioSpace.Two.Anchored

/-! ## `𝒬_RL` under the seed anchor, ticks 0 through 5 -/

/-- `𝒬_RL`'s tick-zero carrier: the lone seed with word `RL`. -/
def XAT0 : TickCarrier Unit hQ := X0 [true, false]
def MOAT : Mat2 := XAT0.observer.matrix

theorem hlaw0AT : Lawful XAT0 := by decide
def props0AT : List (Core × Bool) := proposals XAT0.archive XAT0.active
def sel1AT : List (Core × Bool) → List QuestionId :=
  anchoredSelect MOAT 1 seed164Prov (seedAnchors MOAT XAT0)
theorem hsel0AT : ∀ i ∈ sel1AT props0AT, ∃ p ∈ props0AT,
    (childCore p.1 p.2 1 seed164Prov).id = i :=
  anchoredSelect_hsel MOAT 1 seed164Prov _ props0AT
theorem hfresh0AT : ∀ p ∈ props0AT,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XAT0.archive := by decide
def XAT1 : TickCarrier Unit hQ :=
  advanceCarrier XAT0 hlaw0AT sel1AT 1 seed164Prov [] hsel0AT hfresh0AT

theorem hlaw1AT : Lawful XAT1 := by decide
def props1AT : List (Core × Bool) := proposals XAT1.archive XAT1.active
def sel2AT : List (Core × Bool) → List QuestionId :=
  anchoredSelect MOAT 2 seed164Prov (seedAnchors MOAT XAT0)
theorem hsel1AT : ∀ i ∈ sel2AT props1AT, ∃ p ∈ props1AT,
    (childCore p.1 p.2 2 seed164Prov).id = i :=
  anchoredSelect_hsel MOAT 2 seed164Prov _ props1AT
theorem hfresh1AT : ∀ p ∈ props1AT,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XAT1.archive := by decide
def XAT2 : TickCarrier Unit hQ :=
  advanceCarrier XAT1 hlaw1AT sel2AT 2 seed164Prov [] hsel1AT hfresh1AT

theorem hlaw2AT : Lawful XAT2 := by decide
def props2AT : List (Core × Bool) := proposals XAT2.archive XAT2.active
def sel3AT : List (Core × Bool) → List QuestionId :=
  anchoredSelect MOAT 3 seed164Prov (seedAnchors MOAT XAT0)
theorem hsel2AT : ∀ i ∈ sel3AT props2AT, ∃ p ∈ props2AT,
    (childCore p.1 p.2 3 seed164Prov).id = i :=
  anchoredSelect_hsel MOAT 3 seed164Prov _ props2AT
theorem hfresh2AT : ∀ p ∈ props2AT,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XAT2.archive := by decide
def XAT3 : TickCarrier Unit hQ :=
  advanceCarrier XAT2 hlaw2AT sel3AT 3 seed164Prov [] hsel2AT hfresh2AT

theorem hlaw3AT : Lawful XAT3 := by decide
def props3AT : List (Core × Bool) := proposals XAT3.archive XAT3.active
def sel4AT : List (Core × Bool) → List QuestionId :=
  anchoredSelect MOAT 4 seed164Prov (seedAnchors MOAT XAT0)
theorem hsel3AT : ∀ i ∈ sel4AT props3AT, ∃ p ∈ props3AT,
    (childCore p.1 p.2 4 seed164Prov).id = i :=
  anchoredSelect_hsel MOAT 4 seed164Prov _ props3AT
theorem hfresh3AT : ∀ p ∈ props3AT,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XAT3.archive := by decide
def XAT4 : TickCarrier Unit hQ :=
  advanceCarrier XAT3 hlaw3AT sel4AT 4 seed164Prov [] hsel3AT hfresh3AT

theorem hlaw4AT : Lawful XAT4 := by decide
def props4AT : List (Core × Bool) := proposals XAT4.archive XAT4.active
def sel5AT : List (Core × Bool) → List QuestionId :=
  anchoredSelect MOAT 5 seed164Prov (seedAnchors MOAT XAT0)
theorem hsel4AT : ∀ i ∈ sel5AT props4AT, ∃ p ∈ props4AT,
    (childCore p.1 p.2 5 seed164Prov).id = i :=
  anchoredSelect_hsel MOAT 5 seed164Prov _ props4AT
theorem hfresh4AT : ∀ p ∈ props4AT,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XAT4.archive := by decide
def XAT5 : TickCarrier Unit hQ :=
  advanceCarrier XAT4 hlaw4AT sel5AT 5 seed164Prov [] hsel4AT hfresh4AT

/-! ## The decided ties -/

/-- **Remark 16.18, seed anchor: a tie at the question `𝒬_RL`.** Singletons
    `RL^2 … RL^5` at ticks 1 to 4 (the ray of the last hand), then at tick 5
    the pair `{RL^6, RL^5 R}`; the admitted family at that advance has two
    members and both have the anchored coherence value `3524613 - 2178330φ`, so both
    are maximizers and both are retained. -/
theorem remark_16_18_seed_anchor_tie_RL :
    activeWords XAT1 = [true :: List.replicate 2 false] ∧
    activeWords XAT2 = [true :: List.replicate 3 false] ∧
    activeWords XAT3 = [true :: List.replicate 4 false] ∧
    activeWords XAT4 = [true :: List.replicate 5 false] ∧
    activeWords XAT5 =
      [true :: List.replicate 6 false, true :: (List.replicate 5 false ++ [true])] ∧
    (admittedFam MOAT 5 seed164Prov props4AT).map
        (coherenceOf (admittedFam MOAT 5 seed164Prov props4AT ++ seedAnchors MOAT XAT0)) =
      [(⟨3524613, -2178330⟩ : Zphi), ⟨3524613, -2178330⟩] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Remark 16.18, seed anchor: the root tie is kept at tick 7.** The four
    admitted grandchildren are `LR^5 L`, `LR^6`, `RL^6`, `RL^5 R`; with the seed
    as anchor the middle two have the equal anchored coherence value
    `3524880 - 2178495φ`, above the outer two, and they are the support. -/
theorem remark_16_18_seed_anchor_tie_root :
    (admittedCores MOAE 7 seed164Prov props6AE).map Core.fullWord =
      [false :: List.replicate 5 true ++ [false], false :: List.replicate 6 true,
       true :: List.replicate 6 false, true :: (List.replicate 5 false ++ [true])] ∧
    (admittedFam MOAE 7 seed164Prov props6AE).map
        (coherenceOf (admittedFam MOAE 7 seed164Prov props6AE ++ seedAnchors MOAE XAE0)) =
      [(⟨3522207, -2176843⟩ : Zphi), ⟨3524880, -2178495⟩, ⟨3524880, -2178495⟩,
        ⟨3522207, -2176843⟩] ∧
    activeWords XAE7 = [false :: List.replicate 6 true, true :: List.replicate 6 false] := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Remark 16.18, support anchor: the root tie is kept at tick 7.** Same four
    admitted grandchildren; with the current support as anchors the middle two
    have the equal anchored coherence value `7782266947 - 4809705482φ`, the outer two
    `-8944394320269147 + 5527939698707846φ`, and the middle two are the
    support. -/
theorem remark_16_18_support_anchor_tie_root :
    (admittedCores MOBE 7 seed164Prov props6BE).map Core.fullWord =
      [false :: List.replicate 5 true ++ [false], false :: List.replicate 6 true,
       true :: List.replicate 6 false, true :: (List.replicate 5 false ++ [true])] ∧
    (admittedFam MOBE 7 seed164Prov props6BE).map
        (coherenceOf (admittedFam MOBE 7 seed164Prov props6BE ++ supportAnchors MOBE XBE6)) =
      [(⟨-8944394320269147, 5527939698707846⟩ : Zphi), ⟨7782266947, -4809705482⟩,
        ⟨7782266947, -4809705482⟩, ⟨-8944394320269147, 5527939698707846⟩] ∧
    activeWords XBE7 = [false :: List.replicate 6 true, true :: List.replicate 6 false] := by
  refine ⟨by decide, by decide, by decide⟩

#print axioms remark_16_18_seed_anchor_tie_RL
#print axioms remark_16_18_seed_anchor_tie_root
#print axioms remark_16_18_support_anchor_tie_root

end R16_18
end Gaps
end RatioSpace
