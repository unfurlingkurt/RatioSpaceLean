/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.RootOrbit
/-!
  Elements II §16, Remark 16.18 — Anchored comparison profiles.

  Definition 8.1: "If a later receiver is intended to coherence value additional
  retained anchors, those anchors must enter as explicitly tagged occurrences
  in a declared extended comparison profile."
  `anchoredSelect` is `RootOrbit.axiomSelect` with the coherence values taken over the
  admitted family *plus* the declared anchors, and the maximum taken over the
  admitted family only: anchors are compared against, never selected.
-/
set_option linter.style.longLine false
set_option maxRecDepth 200000

namespace RatioSpace
namespace Two
namespace Anchored

open Mat2 Word Frame Pres RatioSpace RatioSpace.Zphi Advance Accumulation RootOrbit

/-- **The declared extended profile.** Coherence values over `fam ++ anchors`; the
    maximizer test ranges over the admitted family `fam` alone. -/
def anchoredSelect (MO : Mat2) (stratum : ℕ) (prov : Provenance) (anchors : List IPres) :
    List (Core × Bool) → List QuestionId :=
  fun props =>
    let admitted := admittedCores MO stratum prov props
    let fam := admittedFam MO stratum prov props
    let prof := fam ++ anchors
    (admitted.filter (fun c =>
      match addrOf MO c with
      | some y => decide (fam.all (fun z => coherenceOf prof z ≤ coherenceOf prof y))
      | none => false)).map Core.id

/-- With no anchors the extended profile is the base profile, exactly. -/
theorem anchoredSelect_nil (MO : Mat2) (stratum : ℕ) (prov : Provenance) :
    anchoredSelect MO stratum prov [] = axiomSelect MO stratum prov := by
  funext props
  simp only [anchoredSelect, axiomSelect, List.append_nil]
  try rfl

theorem anchoredSelect_hsel (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (anchors : List IPres) (props : List (Core × Bool)) :
    ∀ i ∈ anchoredSelect MO stratum prov anchors props,
      ∃ p ∈ props, (childCore p.1 p.2 stratum prov).id = i := by
  intro i hi
  unfold anchoredSelect at hi
  simp only [List.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  have hc1 : c ∈ admittedCores MO stratum prov props := List.mem_of_mem_filter hc
  unfold admittedCores at hc1
  have hc2 : c ∈ props.map (fun p => childCore p.1 p.2 stratum prov) :=
    List.mem_of_mem_filter hc1
  simp only [List.mem_map] at hc2
  obtain ⟨p, hp, rfl⟩ := hc2
  exact ⟨p, hp, rfl⟩

/-- The seed occurrence as anchor: the addressed seed of a tick-zero carrier. -/
def seedAnchors {h : ℕ} (MO : Mat2) (X : TickCarrier Unit h) : List IPres :=
  X.archive.filterMap (addrOf MO)

/-- The current support as anchors. -/
def supportAnchors {h : ℕ} (MO : Mat2) (X : TickCarrier Unit h) : List IPres :=
  (X.archive.filter (fun c => c.id ∈ X.active)).filterMap (addrOf MO)

def XAE0 : TickCarrier Unit hQ := X0 []
def MOAE : Mat2 := XAE0.observer.matrix
theorem hlaw0AE : Lawful XAE0 := by decide
def props0AE : List (Core × Bool) := proposals XAE0.archive XAE0.active
def sel1AE : List (Core × Bool) → List QuestionId := anchoredSelect MOAE 1 seed164Prov (seedAnchors MOAE XAE0)
theorem hsel0AE : ∀ i ∈ sel1AE props0AE, ∃ p ∈ props0AE,
    (childCore p.1 p.2 1 seed164Prov).id = i := anchoredSelect_hsel MOAE 1 seed164Prov _ props0AE
theorem hfresh0AE : ∀ p ∈ props0AE,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XAE0.archive := by decide
def XAE1 : TickCarrier Unit hQ :=
  advanceCarrier XAE0 hlaw0AE sel1AE 1 seed164Prov [] hsel0AE hfresh0AE
theorem hlaw1AE : Lawful XAE1 := by decide
def props1AE : List (Core × Bool) := proposals XAE1.archive XAE1.active
def sel2AE : List (Core × Bool) → List QuestionId := anchoredSelect MOAE 2 seed164Prov (seedAnchors MOAE XAE0)
theorem hsel1AE : ∀ i ∈ sel2AE props1AE, ∃ p ∈ props1AE,
    (childCore p.1 p.2 2 seed164Prov).id = i := anchoredSelect_hsel MOAE 2 seed164Prov _ props1AE
theorem hfresh1AE : ∀ p ∈ props1AE,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XAE1.archive := by decide
def XAE2 : TickCarrier Unit hQ :=
  advanceCarrier XAE1 hlaw1AE sel2AE 2 seed164Prov [] hsel1AE hfresh1AE
theorem hlaw2AE : Lawful XAE2 := by decide
def props2AE : List (Core × Bool) := proposals XAE2.archive XAE2.active
def sel3AE : List (Core × Bool) → List QuestionId := anchoredSelect MOAE 3 seed164Prov (seedAnchors MOAE XAE0)
theorem hsel2AE : ∀ i ∈ sel3AE props2AE, ∃ p ∈ props2AE,
    (childCore p.1 p.2 3 seed164Prov).id = i := anchoredSelect_hsel MOAE 3 seed164Prov _ props2AE
theorem hfresh2AE : ∀ p ∈ props2AE,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XAE2.archive := by decide
def XAE3 : TickCarrier Unit hQ :=
  advanceCarrier XAE2 hlaw2AE sel3AE 3 seed164Prov [] hsel2AE hfresh2AE
theorem hlaw3AE : Lawful XAE3 := by decide
def props3AE : List (Core × Bool) := proposals XAE3.archive XAE3.active
def sel4AE : List (Core × Bool) → List QuestionId := anchoredSelect MOAE 4 seed164Prov (seedAnchors MOAE XAE0)
theorem hsel3AE : ∀ i ∈ sel4AE props3AE, ∃ p ∈ props3AE,
    (childCore p.1 p.2 4 seed164Prov).id = i := anchoredSelect_hsel MOAE 4 seed164Prov _ props3AE
theorem hfresh3AE : ∀ p ∈ props3AE,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XAE3.archive := by decide
def XAE4 : TickCarrier Unit hQ :=
  advanceCarrier XAE3 hlaw3AE sel4AE 4 seed164Prov [] hsel3AE hfresh3AE
theorem hlaw4AE : Lawful XAE4 := by decide
def props4AE : List (Core × Bool) := proposals XAE4.archive XAE4.active
def sel5AE : List (Core × Bool) → List QuestionId := anchoredSelect MOAE 5 seed164Prov (seedAnchors MOAE XAE0)
theorem hsel4AE : ∀ i ∈ sel5AE props4AE, ∃ p ∈ props4AE,
    (childCore p.1 p.2 5 seed164Prov).id = i := anchoredSelect_hsel MOAE 5 seed164Prov _ props4AE
theorem hfresh4AE : ∀ p ∈ props4AE,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XAE4.archive := by decide
def XAE5 : TickCarrier Unit hQ :=
  advanceCarrier XAE4 hlaw4AE sel5AE 5 seed164Prov [] hsel4AE hfresh4AE
theorem hlaw5AE : Lawful XAE5 := by decide
def props5AE : List (Core × Bool) := proposals XAE5.archive XAE5.active
def sel6AE : List (Core × Bool) → List QuestionId := anchoredSelect MOAE 6 seed164Prov (seedAnchors MOAE XAE0)
theorem hsel5AE : ∀ i ∈ sel6AE props5AE, ∃ p ∈ props5AE,
    (childCore p.1 p.2 6 seed164Prov).id = i := anchoredSelect_hsel MOAE 6 seed164Prov _ props5AE
theorem hfresh5AE : ∀ p ∈ props5AE,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XAE5.archive := by decide
def XAE6 : TickCarrier Unit hQ :=
  advanceCarrier XAE5 hlaw5AE sel6AE 6 seed164Prov [] hsel5AE hfresh5AE
theorem hlaw6AE : Lawful XAE6 := by decide
def props6AE : List (Core × Bool) := proposals XAE6.archive XAE6.active
def sel7AE : List (Core × Bool) → List QuestionId := anchoredSelect MOAE 7 seed164Prov (seedAnchors MOAE XAE0)
theorem hsel6AE : ∀ i ∈ sel7AE props6AE, ∃ p ∈ props6AE,
    (childCore p.1 p.2 7 seed164Prov).id = i := anchoredSelect_hsel MOAE 7 seed164Prov _ props6AE
theorem hfresh6AE : ∀ p ∈ props6AE,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XAE6.archive := by decide
def XAE7 : TickCarrier Unit hQ :=
  advanceCarrier XAE6 hlaw6AE sel7AE 7 seed164Prov [] hsel6AE hfresh6AE

def XAL0 : TickCarrier Unit hQ := X0 [false]
def MOAL : Mat2 := XAL0.observer.matrix
theorem hlaw0AL : Lawful XAL0 := by decide
def props0AL : List (Core × Bool) := proposals XAL0.archive XAL0.active
def sel1AL : List (Core × Bool) → List QuestionId := anchoredSelect MOAL 1 seed164Prov (seedAnchors MOAL XAL0)
theorem hsel0AL : ∀ i ∈ sel1AL props0AL, ∃ p ∈ props0AL,
    (childCore p.1 p.2 1 seed164Prov).id = i := anchoredSelect_hsel MOAL 1 seed164Prov _ props0AL
theorem hfresh0AL : ∀ p ∈ props0AL,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XAL0.archive := by decide
def XAL1 : TickCarrier Unit hQ :=
  advanceCarrier XAL0 hlaw0AL sel1AL 1 seed164Prov [] hsel0AL hfresh0AL
theorem hlaw1AL : Lawful XAL1 := by decide
def props1AL : List (Core × Bool) := proposals XAL1.archive XAL1.active
def sel2AL : List (Core × Bool) → List QuestionId := anchoredSelect MOAL 2 seed164Prov (seedAnchors MOAL XAL0)
theorem hsel1AL : ∀ i ∈ sel2AL props1AL, ∃ p ∈ props1AL,
    (childCore p.1 p.2 2 seed164Prov).id = i := anchoredSelect_hsel MOAL 2 seed164Prov _ props1AL
theorem hfresh1AL : ∀ p ∈ props1AL,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XAL1.archive := by decide
def XAL2 : TickCarrier Unit hQ :=
  advanceCarrier XAL1 hlaw1AL sel2AL 2 seed164Prov [] hsel1AL hfresh1AL
theorem hlaw2AL : Lawful XAL2 := by decide
def props2AL : List (Core × Bool) := proposals XAL2.archive XAL2.active
def sel3AL : List (Core × Bool) → List QuestionId := anchoredSelect MOAL 3 seed164Prov (seedAnchors MOAL XAL0)
theorem hsel2AL : ∀ i ∈ sel3AL props2AL, ∃ p ∈ props2AL,
    (childCore p.1 p.2 3 seed164Prov).id = i := anchoredSelect_hsel MOAL 3 seed164Prov _ props2AL
theorem hfresh2AL : ∀ p ∈ props2AL,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XAL2.archive := by decide
def XAL3 : TickCarrier Unit hQ :=
  advanceCarrier XAL2 hlaw2AL sel3AL 3 seed164Prov [] hsel2AL hfresh2AL
theorem hlaw3AL : Lawful XAL3 := by decide
def props3AL : List (Core × Bool) := proposals XAL3.archive XAL3.active
def sel4AL : List (Core × Bool) → List QuestionId := anchoredSelect MOAL 4 seed164Prov (seedAnchors MOAL XAL0)
theorem hsel3AL : ∀ i ∈ sel4AL props3AL, ∃ p ∈ props3AL,
    (childCore p.1 p.2 4 seed164Prov).id = i := anchoredSelect_hsel MOAL 4 seed164Prov _ props3AL
theorem hfresh3AL : ∀ p ∈ props3AL,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XAL3.archive := by decide
def XAL4 : TickCarrier Unit hQ :=
  advanceCarrier XAL3 hlaw3AL sel4AL 4 seed164Prov [] hsel3AL hfresh3AL
theorem hlaw4AL : Lawful XAL4 := by decide
def props4AL : List (Core × Bool) := proposals XAL4.archive XAL4.active
def sel5AL : List (Core × Bool) → List QuestionId := anchoredSelect MOAL 5 seed164Prov (seedAnchors MOAL XAL0)
theorem hsel4AL : ∀ i ∈ sel5AL props4AL, ∃ p ∈ props4AL,
    (childCore p.1 p.2 5 seed164Prov).id = i := anchoredSelect_hsel MOAL 5 seed164Prov _ props4AL
theorem hfresh4AL : ∀ p ∈ props4AL,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XAL4.archive := by decide
def XAL5 : TickCarrier Unit hQ :=
  advanceCarrier XAL4 hlaw4AL sel5AL 5 seed164Prov [] hsel4AL hfresh4AL
theorem hlaw5AL : Lawful XAL5 := by decide
def props5AL : List (Core × Bool) := proposals XAL5.archive XAL5.active
def sel6AL : List (Core × Bool) → List QuestionId := anchoredSelect MOAL 6 seed164Prov (seedAnchors MOAL XAL0)
theorem hsel5AL : ∀ i ∈ sel6AL props5AL, ∃ p ∈ props5AL,
    (childCore p.1 p.2 6 seed164Prov).id = i := anchoredSelect_hsel MOAL 6 seed164Prov _ props5AL
theorem hfresh5AL : ∀ p ∈ props5AL,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XAL5.archive := by decide
def XAL6 : TickCarrier Unit hQ :=
  advanceCarrier XAL5 hlaw5AL sel6AL 6 seed164Prov [] hsel5AL hfresh5AL
theorem hlaw6AL : Lawful XAL6 := by decide
def props6AL : List (Core × Bool) := proposals XAL6.archive XAL6.active
def sel7AL : List (Core × Bool) → List QuestionId := anchoredSelect MOAL 7 seed164Prov (seedAnchors MOAL XAL0)
theorem hsel6AL : ∀ i ∈ sel7AL props6AL, ∃ p ∈ props6AL,
    (childCore p.1 p.2 7 seed164Prov).id = i := anchoredSelect_hsel MOAL 7 seed164Prov _ props6AL
theorem hfresh6AL : ∀ p ∈ props6AL,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XAL6.archive := by decide
def XAL7 : TickCarrier Unit hQ :=
  advanceCarrier XAL6 hlaw6AL sel7AL 7 seed164Prov [] hsel6AL hfresh6AL

def XAR0 : TickCarrier Unit hQ := X0 [true]
def MOAR : Mat2 := XAR0.observer.matrix
theorem hlaw0AR : Lawful XAR0 := by decide
def props0AR : List (Core × Bool) := proposals XAR0.archive XAR0.active
def sel1AR : List (Core × Bool) → List QuestionId := anchoredSelect MOAR 1 seed164Prov (seedAnchors MOAR XAR0)
theorem hsel0AR : ∀ i ∈ sel1AR props0AR, ∃ p ∈ props0AR,
    (childCore p.1 p.2 1 seed164Prov).id = i := anchoredSelect_hsel MOAR 1 seed164Prov _ props0AR
theorem hfresh0AR : ∀ p ∈ props0AR,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XAR0.archive := by decide
def XAR1 : TickCarrier Unit hQ :=
  advanceCarrier XAR0 hlaw0AR sel1AR 1 seed164Prov [] hsel0AR hfresh0AR
theorem hlaw1AR : Lawful XAR1 := by decide
def props1AR : List (Core × Bool) := proposals XAR1.archive XAR1.active
def sel2AR : List (Core × Bool) → List QuestionId := anchoredSelect MOAR 2 seed164Prov (seedAnchors MOAR XAR0)
theorem hsel1AR : ∀ i ∈ sel2AR props1AR, ∃ p ∈ props1AR,
    (childCore p.1 p.2 2 seed164Prov).id = i := anchoredSelect_hsel MOAR 2 seed164Prov _ props1AR
theorem hfresh1AR : ∀ p ∈ props1AR,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XAR1.archive := by decide
def XAR2 : TickCarrier Unit hQ :=
  advanceCarrier XAR1 hlaw1AR sel2AR 2 seed164Prov [] hsel1AR hfresh1AR
theorem hlaw2AR : Lawful XAR2 := by decide
def props2AR : List (Core × Bool) := proposals XAR2.archive XAR2.active
def sel3AR : List (Core × Bool) → List QuestionId := anchoredSelect MOAR 3 seed164Prov (seedAnchors MOAR XAR0)
theorem hsel2AR : ∀ i ∈ sel3AR props2AR, ∃ p ∈ props2AR,
    (childCore p.1 p.2 3 seed164Prov).id = i := anchoredSelect_hsel MOAR 3 seed164Prov _ props2AR
theorem hfresh2AR : ∀ p ∈ props2AR,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XAR2.archive := by decide
def XAR3 : TickCarrier Unit hQ :=
  advanceCarrier XAR2 hlaw2AR sel3AR 3 seed164Prov [] hsel2AR hfresh2AR
theorem hlaw3AR : Lawful XAR3 := by decide
def props3AR : List (Core × Bool) := proposals XAR3.archive XAR3.active
def sel4AR : List (Core × Bool) → List QuestionId := anchoredSelect MOAR 4 seed164Prov (seedAnchors MOAR XAR0)
theorem hsel3AR : ∀ i ∈ sel4AR props3AR, ∃ p ∈ props3AR,
    (childCore p.1 p.2 4 seed164Prov).id = i := anchoredSelect_hsel MOAR 4 seed164Prov _ props3AR
theorem hfresh3AR : ∀ p ∈ props3AR,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XAR3.archive := by decide
def XAR4 : TickCarrier Unit hQ :=
  advanceCarrier XAR3 hlaw3AR sel4AR 4 seed164Prov [] hsel3AR hfresh3AR
theorem hlaw4AR : Lawful XAR4 := by decide
def props4AR : List (Core × Bool) := proposals XAR4.archive XAR4.active
def sel5AR : List (Core × Bool) → List QuestionId := anchoredSelect MOAR 5 seed164Prov (seedAnchors MOAR XAR0)
theorem hsel4AR : ∀ i ∈ sel5AR props4AR, ∃ p ∈ props4AR,
    (childCore p.1 p.2 5 seed164Prov).id = i := anchoredSelect_hsel MOAR 5 seed164Prov _ props4AR
theorem hfresh4AR : ∀ p ∈ props4AR,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XAR4.archive := by decide
def XAR5 : TickCarrier Unit hQ :=
  advanceCarrier XAR4 hlaw4AR sel5AR 5 seed164Prov [] hsel4AR hfresh4AR
theorem hlaw5AR : Lawful XAR5 := by decide
def props5AR : List (Core × Bool) := proposals XAR5.archive XAR5.active
def sel6AR : List (Core × Bool) → List QuestionId := anchoredSelect MOAR 6 seed164Prov (seedAnchors MOAR XAR0)
theorem hsel5AR : ∀ i ∈ sel6AR props5AR, ∃ p ∈ props5AR,
    (childCore p.1 p.2 6 seed164Prov).id = i := anchoredSelect_hsel MOAR 6 seed164Prov _ props5AR
theorem hfresh5AR : ∀ p ∈ props5AR,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XAR5.archive := by decide
def XAR6 : TickCarrier Unit hQ :=
  advanceCarrier XAR5 hlaw5AR sel6AR 6 seed164Prov [] hsel5AR hfresh5AR
theorem hlaw6AR : Lawful XAR6 := by decide
def props6AR : List (Core × Bool) := proposals XAR6.archive XAR6.active
def sel7AR : List (Core × Bool) → List QuestionId := anchoredSelect MOAR 7 seed164Prov (seedAnchors MOAR XAR0)
theorem hsel6AR : ∀ i ∈ sel7AR props6AR, ∃ p ∈ props6AR,
    (childCore p.1 p.2 7 seed164Prov).id = i := anchoredSelect_hsel MOAR 7 seed164Prov _ props6AR
theorem hfresh6AR : ∀ p ∈ props6AR,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XAR6.archive := by decide
def XAR7 : TickCarrier Unit hQ :=
  advanceCarrier XAR6 hlaw6AR sel7AR 7 seed164Prov [] hsel6AR hfresh6AR

def XALL0 : TickCarrier Unit hQ := X0 [false, false]
def MOALL : Mat2 := XALL0.observer.matrix
theorem hlaw0ALL : Lawful XALL0 := by decide
def props0ALL : List (Core × Bool) := proposals XALL0.archive XALL0.active
def sel1ALL : List (Core × Bool) → List QuestionId := anchoredSelect MOALL 1 seed164Prov (seedAnchors MOALL XALL0)
theorem hsel0ALL : ∀ i ∈ sel1ALL props0ALL, ∃ p ∈ props0ALL,
    (childCore p.1 p.2 1 seed164Prov).id = i := anchoredSelect_hsel MOALL 1 seed164Prov _ props0ALL
theorem hfresh0ALL : ∀ p ∈ props0ALL,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XALL0.archive := by decide
def XALL1 : TickCarrier Unit hQ :=
  advanceCarrier XALL0 hlaw0ALL sel1ALL 1 seed164Prov [] hsel0ALL hfresh0ALL
theorem hlaw1ALL : Lawful XALL1 := by decide
def props1ALL : List (Core × Bool) := proposals XALL1.archive XALL1.active
def sel2ALL : List (Core × Bool) → List QuestionId := anchoredSelect MOALL 2 seed164Prov (seedAnchors MOALL XALL0)
theorem hsel1ALL : ∀ i ∈ sel2ALL props1ALL, ∃ p ∈ props1ALL,
    (childCore p.1 p.2 2 seed164Prov).id = i := anchoredSelect_hsel MOALL 2 seed164Prov _ props1ALL
theorem hfresh1ALL : ∀ p ∈ props1ALL,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XALL1.archive := by decide
def XALL2 : TickCarrier Unit hQ :=
  advanceCarrier XALL1 hlaw1ALL sel2ALL 2 seed164Prov [] hsel1ALL hfresh1ALL
theorem hlaw2ALL : Lawful XALL2 := by decide
def props2ALL : List (Core × Bool) := proposals XALL2.archive XALL2.active
def sel3ALL : List (Core × Bool) → List QuestionId := anchoredSelect MOALL 3 seed164Prov (seedAnchors MOALL XALL0)
theorem hsel2ALL : ∀ i ∈ sel3ALL props2ALL, ∃ p ∈ props2ALL,
    (childCore p.1 p.2 3 seed164Prov).id = i := anchoredSelect_hsel MOALL 3 seed164Prov _ props2ALL
theorem hfresh2ALL : ∀ p ∈ props2ALL,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XALL2.archive := by decide
def XALL3 : TickCarrier Unit hQ :=
  advanceCarrier XALL2 hlaw2ALL sel3ALL 3 seed164Prov [] hsel2ALL hfresh2ALL
theorem hlaw3ALL : Lawful XALL3 := by decide
def props3ALL : List (Core × Bool) := proposals XALL3.archive XALL3.active
def sel4ALL : List (Core × Bool) → List QuestionId := anchoredSelect MOALL 4 seed164Prov (seedAnchors MOALL XALL0)
theorem hsel3ALL : ∀ i ∈ sel4ALL props3ALL, ∃ p ∈ props3ALL,
    (childCore p.1 p.2 4 seed164Prov).id = i := anchoredSelect_hsel MOALL 4 seed164Prov _ props3ALL
theorem hfresh3ALL : ∀ p ∈ props3ALL,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XALL3.archive := by decide
def XALL4 : TickCarrier Unit hQ :=
  advanceCarrier XALL3 hlaw3ALL sel4ALL 4 seed164Prov [] hsel3ALL hfresh3ALL
theorem hlaw4ALL : Lawful XALL4 := by decide
def props4ALL : List (Core × Bool) := proposals XALL4.archive XALL4.active
def sel5ALL : List (Core × Bool) → List QuestionId := anchoredSelect MOALL 5 seed164Prov (seedAnchors MOALL XALL0)
theorem hsel4ALL : ∀ i ∈ sel5ALL props4ALL, ∃ p ∈ props4ALL,
    (childCore p.1 p.2 5 seed164Prov).id = i := anchoredSelect_hsel MOALL 5 seed164Prov _ props4ALL
theorem hfresh4ALL : ∀ p ∈ props4ALL,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XALL4.archive := by decide
def XALL5 : TickCarrier Unit hQ :=
  advanceCarrier XALL4 hlaw4ALL sel5ALL 5 seed164Prov [] hsel4ALL hfresh4ALL
theorem hlaw5ALL : Lawful XALL5 := by decide
def props5ALL : List (Core × Bool) := proposals XALL5.archive XALL5.active
def sel6ALL : List (Core × Bool) → List QuestionId := anchoredSelect MOALL 6 seed164Prov (seedAnchors MOALL XALL0)
theorem hsel5ALL : ∀ i ∈ sel6ALL props5ALL, ∃ p ∈ props5ALL,
    (childCore p.1 p.2 6 seed164Prov).id = i := anchoredSelect_hsel MOALL 6 seed164Prov _ props5ALL
theorem hfresh5ALL : ∀ p ∈ props5ALL,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XALL5.archive := by decide
def XALL6 : TickCarrier Unit hQ :=
  advanceCarrier XALL5 hlaw5ALL sel6ALL 6 seed164Prov [] hsel5ALL hfresh5ALL
theorem hlaw6ALL : Lawful XALL6 := by decide
def props6ALL : List (Core × Bool) := proposals XALL6.archive XALL6.active
def sel7ALL : List (Core × Bool) → List QuestionId := anchoredSelect MOALL 7 seed164Prov (seedAnchors MOALL XALL0)
theorem hsel6ALL : ∀ i ∈ sel7ALL props6ALL, ∃ p ∈ props6ALL,
    (childCore p.1 p.2 7 seed164Prov).id = i := anchoredSelect_hsel MOALL 7 seed164Prov _ props6ALL
theorem hfresh6ALL : ∀ p ∈ props6ALL,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XALL6.archive := by decide
def XALL7 : TickCarrier Unit hQ :=
  advanceCarrier XALL6 hlaw6ALL sel7ALL 7 seed164Prov [] hsel6ALL hfresh6ALL

def XBE0 : TickCarrier Unit hQ := X0 []
def MOBE : Mat2 := XBE0.observer.matrix
theorem hlaw0BE : Lawful XBE0 := by decide
def props0BE : List (Core × Bool) := proposals XBE0.archive XBE0.active
def sel1BE : List (Core × Bool) → List QuestionId := anchoredSelect MOBE 1 seed164Prov (supportAnchors MOBE XBE0)
theorem hsel0BE : ∀ i ∈ sel1BE props0BE, ∃ p ∈ props0BE,
    (childCore p.1 p.2 1 seed164Prov).id = i := anchoredSelect_hsel MOBE 1 seed164Prov _ props0BE
theorem hfresh0BE : ∀ p ∈ props0BE,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XBE0.archive := by decide
def XBE1 : TickCarrier Unit hQ :=
  advanceCarrier XBE0 hlaw0BE sel1BE 1 seed164Prov [] hsel0BE hfresh0BE
theorem hlaw1BE : Lawful XBE1 := by decide
def props1BE : List (Core × Bool) := proposals XBE1.archive XBE1.active
def sel2BE : List (Core × Bool) → List QuestionId := anchoredSelect MOBE 2 seed164Prov (supportAnchors MOBE XBE1)
theorem hsel1BE : ∀ i ∈ sel2BE props1BE, ∃ p ∈ props1BE,
    (childCore p.1 p.2 2 seed164Prov).id = i := anchoredSelect_hsel MOBE 2 seed164Prov _ props1BE
theorem hfresh1BE : ∀ p ∈ props1BE,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XBE1.archive := by decide
def XBE2 : TickCarrier Unit hQ :=
  advanceCarrier XBE1 hlaw1BE sel2BE 2 seed164Prov [] hsel1BE hfresh1BE
theorem hlaw2BE : Lawful XBE2 := by decide
def props2BE : List (Core × Bool) := proposals XBE2.archive XBE2.active
def sel3BE : List (Core × Bool) → List QuestionId := anchoredSelect MOBE 3 seed164Prov (supportAnchors MOBE XBE2)
theorem hsel2BE : ∀ i ∈ sel3BE props2BE, ∃ p ∈ props2BE,
    (childCore p.1 p.2 3 seed164Prov).id = i := anchoredSelect_hsel MOBE 3 seed164Prov _ props2BE
theorem hfresh2BE : ∀ p ∈ props2BE,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XBE2.archive := by decide
def XBE3 : TickCarrier Unit hQ :=
  advanceCarrier XBE2 hlaw2BE sel3BE 3 seed164Prov [] hsel2BE hfresh2BE
theorem hlaw3BE : Lawful XBE3 := by decide
def props3BE : List (Core × Bool) := proposals XBE3.archive XBE3.active
def sel4BE : List (Core × Bool) → List QuestionId := anchoredSelect MOBE 4 seed164Prov (supportAnchors MOBE XBE3)
theorem hsel3BE : ∀ i ∈ sel4BE props3BE, ∃ p ∈ props3BE,
    (childCore p.1 p.2 4 seed164Prov).id = i := anchoredSelect_hsel MOBE 4 seed164Prov _ props3BE
theorem hfresh3BE : ∀ p ∈ props3BE,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XBE3.archive := by decide
def XBE4 : TickCarrier Unit hQ :=
  advanceCarrier XBE3 hlaw3BE sel4BE 4 seed164Prov [] hsel3BE hfresh3BE
theorem hlaw4BE : Lawful XBE4 := by decide
def props4BE : List (Core × Bool) := proposals XBE4.archive XBE4.active
def sel5BE : List (Core × Bool) → List QuestionId := anchoredSelect MOBE 5 seed164Prov (supportAnchors MOBE XBE4)
theorem hsel4BE : ∀ i ∈ sel5BE props4BE, ∃ p ∈ props4BE,
    (childCore p.1 p.2 5 seed164Prov).id = i := anchoredSelect_hsel MOBE 5 seed164Prov _ props4BE
theorem hfresh4BE : ∀ p ∈ props4BE,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XBE4.archive := by decide
def XBE5 : TickCarrier Unit hQ :=
  advanceCarrier XBE4 hlaw4BE sel5BE 5 seed164Prov [] hsel4BE hfresh4BE
theorem hlaw5BE : Lawful XBE5 := by decide
def props5BE : List (Core × Bool) := proposals XBE5.archive XBE5.active
def sel6BE : List (Core × Bool) → List QuestionId := anchoredSelect MOBE 6 seed164Prov (supportAnchors MOBE XBE5)
theorem hsel5BE : ∀ i ∈ sel6BE props5BE, ∃ p ∈ props5BE,
    (childCore p.1 p.2 6 seed164Prov).id = i := anchoredSelect_hsel MOBE 6 seed164Prov _ props5BE
theorem hfresh5BE : ∀ p ∈ props5BE,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XBE5.archive := by decide
def XBE6 : TickCarrier Unit hQ :=
  advanceCarrier XBE5 hlaw5BE sel6BE 6 seed164Prov [] hsel5BE hfresh5BE
theorem hlaw6BE : Lawful XBE6 := by decide
def props6BE : List (Core × Bool) := proposals XBE6.archive XBE6.active
def sel7BE : List (Core × Bool) → List QuestionId := anchoredSelect MOBE 7 seed164Prov (supportAnchors MOBE XBE6)
theorem hsel6BE : ∀ i ∈ sel7BE props6BE, ∃ p ∈ props6BE,
    (childCore p.1 p.2 7 seed164Prov).id = i := anchoredSelect_hsel MOBE 7 seed164Prov _ props6BE
theorem hfresh6BE : ∀ p ∈ props6BE,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XBE6.archive := by decide
def XBE7 : TickCarrier Unit hQ :=
  advanceCarrier XBE6 hlaw6BE sel7BE 7 seed164Prov [] hsel6BE hfresh6BE

def XBL0 : TickCarrier Unit hQ := X0 [false]
def MOBL : Mat2 := XBL0.observer.matrix
theorem hlaw0BL : Lawful XBL0 := by decide
def props0BL : List (Core × Bool) := proposals XBL0.archive XBL0.active
def sel1BL : List (Core × Bool) → List QuestionId := anchoredSelect MOBL 1 seed164Prov (supportAnchors MOBL XBL0)
theorem hsel0BL : ∀ i ∈ sel1BL props0BL, ∃ p ∈ props0BL,
    (childCore p.1 p.2 1 seed164Prov).id = i := anchoredSelect_hsel MOBL 1 seed164Prov _ props0BL
theorem hfresh0BL : ∀ p ∈ props0BL,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XBL0.archive := by decide
def XBL1 : TickCarrier Unit hQ :=
  advanceCarrier XBL0 hlaw0BL sel1BL 1 seed164Prov [] hsel0BL hfresh0BL
theorem hlaw1BL : Lawful XBL1 := by decide
def props1BL : List (Core × Bool) := proposals XBL1.archive XBL1.active
def sel2BL : List (Core × Bool) → List QuestionId := anchoredSelect MOBL 2 seed164Prov (supportAnchors MOBL XBL1)
theorem hsel1BL : ∀ i ∈ sel2BL props1BL, ∃ p ∈ props1BL,
    (childCore p.1 p.2 2 seed164Prov).id = i := anchoredSelect_hsel MOBL 2 seed164Prov _ props1BL
theorem hfresh1BL : ∀ p ∈ props1BL,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XBL1.archive := by decide
def XBL2 : TickCarrier Unit hQ :=
  advanceCarrier XBL1 hlaw1BL sel2BL 2 seed164Prov [] hsel1BL hfresh1BL
theorem hlaw2BL : Lawful XBL2 := by decide
def props2BL : List (Core × Bool) := proposals XBL2.archive XBL2.active
def sel3BL : List (Core × Bool) → List QuestionId := anchoredSelect MOBL 3 seed164Prov (supportAnchors MOBL XBL2)
theorem hsel2BL : ∀ i ∈ sel3BL props2BL, ∃ p ∈ props2BL,
    (childCore p.1 p.2 3 seed164Prov).id = i := anchoredSelect_hsel MOBL 3 seed164Prov _ props2BL
theorem hfresh2BL : ∀ p ∈ props2BL,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XBL2.archive := by decide
def XBL3 : TickCarrier Unit hQ :=
  advanceCarrier XBL2 hlaw2BL sel3BL 3 seed164Prov [] hsel2BL hfresh2BL
theorem hlaw3BL : Lawful XBL3 := by decide
def props3BL : List (Core × Bool) := proposals XBL3.archive XBL3.active
def sel4BL : List (Core × Bool) → List QuestionId := anchoredSelect MOBL 4 seed164Prov (supportAnchors MOBL XBL3)
theorem hsel3BL : ∀ i ∈ sel4BL props3BL, ∃ p ∈ props3BL,
    (childCore p.1 p.2 4 seed164Prov).id = i := anchoredSelect_hsel MOBL 4 seed164Prov _ props3BL
theorem hfresh3BL : ∀ p ∈ props3BL,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XBL3.archive := by decide
def XBL4 : TickCarrier Unit hQ :=
  advanceCarrier XBL3 hlaw3BL sel4BL 4 seed164Prov [] hsel3BL hfresh3BL
theorem hlaw4BL : Lawful XBL4 := by decide
def props4BL : List (Core × Bool) := proposals XBL4.archive XBL4.active
def sel5BL : List (Core × Bool) → List QuestionId := anchoredSelect MOBL 5 seed164Prov (supportAnchors MOBL XBL4)
theorem hsel4BL : ∀ i ∈ sel5BL props4BL, ∃ p ∈ props4BL,
    (childCore p.1 p.2 5 seed164Prov).id = i := anchoredSelect_hsel MOBL 5 seed164Prov _ props4BL
theorem hfresh4BL : ∀ p ∈ props4BL,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XBL4.archive := by decide
def XBL5 : TickCarrier Unit hQ :=
  advanceCarrier XBL4 hlaw4BL sel5BL 5 seed164Prov [] hsel4BL hfresh4BL
theorem hlaw5BL : Lawful XBL5 := by decide
def props5BL : List (Core × Bool) := proposals XBL5.archive XBL5.active
def sel6BL : List (Core × Bool) → List QuestionId := anchoredSelect MOBL 6 seed164Prov (supportAnchors MOBL XBL5)
theorem hsel5BL : ∀ i ∈ sel6BL props5BL, ∃ p ∈ props5BL,
    (childCore p.1 p.2 6 seed164Prov).id = i := anchoredSelect_hsel MOBL 6 seed164Prov _ props5BL
theorem hfresh5BL : ∀ p ∈ props5BL,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XBL5.archive := by decide
def XBL6 : TickCarrier Unit hQ :=
  advanceCarrier XBL5 hlaw5BL sel6BL 6 seed164Prov [] hsel5BL hfresh5BL
theorem hlaw6BL : Lawful XBL6 := by decide
def props6BL : List (Core × Bool) := proposals XBL6.archive XBL6.active
def sel7BL : List (Core × Bool) → List QuestionId := anchoredSelect MOBL 7 seed164Prov (supportAnchors MOBL XBL6)
theorem hsel6BL : ∀ i ∈ sel7BL props6BL, ∃ p ∈ props6BL,
    (childCore p.1 p.2 7 seed164Prov).id = i := anchoredSelect_hsel MOBL 7 seed164Prov _ props6BL
theorem hfresh6BL : ∀ p ∈ props6BL,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XBL6.archive := by decide
def XBL7 : TickCarrier Unit hQ :=
  advanceCarrier XBL6 hlaw6BL sel7BL 7 seed164Prov [] hsel6BL hfresh6BL

def XBR0 : TickCarrier Unit hQ := X0 [true]
def MOBR : Mat2 := XBR0.observer.matrix
theorem hlaw0BR : Lawful XBR0 := by decide
def props0BR : List (Core × Bool) := proposals XBR0.archive XBR0.active
def sel1BR : List (Core × Bool) → List QuestionId := anchoredSelect MOBR 1 seed164Prov (supportAnchors MOBR XBR0)
theorem hsel0BR : ∀ i ∈ sel1BR props0BR, ∃ p ∈ props0BR,
    (childCore p.1 p.2 1 seed164Prov).id = i := anchoredSelect_hsel MOBR 1 seed164Prov _ props0BR
theorem hfresh0BR : ∀ p ∈ props0BR,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XBR0.archive := by decide
def XBR1 : TickCarrier Unit hQ :=
  advanceCarrier XBR0 hlaw0BR sel1BR 1 seed164Prov [] hsel0BR hfresh0BR
theorem hlaw1BR : Lawful XBR1 := by decide
def props1BR : List (Core × Bool) := proposals XBR1.archive XBR1.active
def sel2BR : List (Core × Bool) → List QuestionId := anchoredSelect MOBR 2 seed164Prov (supportAnchors MOBR XBR1)
theorem hsel1BR : ∀ i ∈ sel2BR props1BR, ∃ p ∈ props1BR,
    (childCore p.1 p.2 2 seed164Prov).id = i := anchoredSelect_hsel MOBR 2 seed164Prov _ props1BR
theorem hfresh1BR : ∀ p ∈ props1BR,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XBR1.archive := by decide
def XBR2 : TickCarrier Unit hQ :=
  advanceCarrier XBR1 hlaw1BR sel2BR 2 seed164Prov [] hsel1BR hfresh1BR
theorem hlaw2BR : Lawful XBR2 := by decide
def props2BR : List (Core × Bool) := proposals XBR2.archive XBR2.active
def sel3BR : List (Core × Bool) → List QuestionId := anchoredSelect MOBR 3 seed164Prov (supportAnchors MOBR XBR2)
theorem hsel2BR : ∀ i ∈ sel3BR props2BR, ∃ p ∈ props2BR,
    (childCore p.1 p.2 3 seed164Prov).id = i := anchoredSelect_hsel MOBR 3 seed164Prov _ props2BR
theorem hfresh2BR : ∀ p ∈ props2BR,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XBR2.archive := by decide
def XBR3 : TickCarrier Unit hQ :=
  advanceCarrier XBR2 hlaw2BR sel3BR 3 seed164Prov [] hsel2BR hfresh2BR
theorem hlaw3BR : Lawful XBR3 := by decide
def props3BR : List (Core × Bool) := proposals XBR3.archive XBR3.active
def sel4BR : List (Core × Bool) → List QuestionId := anchoredSelect MOBR 4 seed164Prov (supportAnchors MOBR XBR3)
theorem hsel3BR : ∀ i ∈ sel4BR props3BR, ∃ p ∈ props3BR,
    (childCore p.1 p.2 4 seed164Prov).id = i := anchoredSelect_hsel MOBR 4 seed164Prov _ props3BR
theorem hfresh3BR : ∀ p ∈ props3BR,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XBR3.archive := by decide
def XBR4 : TickCarrier Unit hQ :=
  advanceCarrier XBR3 hlaw3BR sel4BR 4 seed164Prov [] hsel3BR hfresh3BR
theorem hlaw4BR : Lawful XBR4 := by decide
def props4BR : List (Core × Bool) := proposals XBR4.archive XBR4.active
def sel5BR : List (Core × Bool) → List QuestionId := anchoredSelect MOBR 5 seed164Prov (supportAnchors MOBR XBR4)
theorem hsel4BR : ∀ i ∈ sel5BR props4BR, ∃ p ∈ props4BR,
    (childCore p.1 p.2 5 seed164Prov).id = i := anchoredSelect_hsel MOBR 5 seed164Prov _ props4BR
theorem hfresh4BR : ∀ p ∈ props4BR,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XBR4.archive := by decide
def XBR5 : TickCarrier Unit hQ :=
  advanceCarrier XBR4 hlaw4BR sel5BR 5 seed164Prov [] hsel4BR hfresh4BR
theorem hlaw5BR : Lawful XBR5 := by decide
def props5BR : List (Core × Bool) := proposals XBR5.archive XBR5.active
def sel6BR : List (Core × Bool) → List QuestionId := anchoredSelect MOBR 6 seed164Prov (supportAnchors MOBR XBR5)
theorem hsel5BR : ∀ i ∈ sel6BR props5BR, ∃ p ∈ props5BR,
    (childCore p.1 p.2 6 seed164Prov).id = i := anchoredSelect_hsel MOBR 6 seed164Prov _ props5BR
theorem hfresh5BR : ∀ p ∈ props5BR,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XBR5.archive := by decide
def XBR6 : TickCarrier Unit hQ :=
  advanceCarrier XBR5 hlaw5BR sel6BR 6 seed164Prov [] hsel5BR hfresh5BR
theorem hlaw6BR : Lawful XBR6 := by decide
def props6BR : List (Core × Bool) := proposals XBR6.archive XBR6.active
def sel7BR : List (Core × Bool) → List QuestionId := anchoredSelect MOBR 7 seed164Prov (supportAnchors MOBR XBR6)
theorem hsel6BR : ∀ i ∈ sel7BR props6BR, ∃ p ∈ props6BR,
    (childCore p.1 p.2 7 seed164Prov).id = i := anchoredSelect_hsel MOBR 7 seed164Prov _ props6BR
theorem hfresh6BR : ∀ p ∈ props6BR,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XBR6.archive := by decide
def XBR7 : TickCarrier Unit hQ :=
  advanceCarrier XBR6 hlaw6BR sel7BR 7 seed164Prov [] hsel6BR hfresh6BR

def XBLL0 : TickCarrier Unit hQ := X0 [false, false]
def MOBLL : Mat2 := XBLL0.observer.matrix
theorem hlaw0BLL : Lawful XBLL0 := by decide
def props0BLL : List (Core × Bool) := proposals XBLL0.archive XBLL0.active
def sel1BLL : List (Core × Bool) → List QuestionId := anchoredSelect MOBLL 1 seed164Prov (supportAnchors MOBLL XBLL0)
theorem hsel0BLL : ∀ i ∈ sel1BLL props0BLL, ∃ p ∈ props0BLL,
    (childCore p.1 p.2 1 seed164Prov).id = i := anchoredSelect_hsel MOBLL 1 seed164Prov _ props0BLL
theorem hfresh0BLL : ∀ p ∈ props0BLL,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XBLL0.archive := by decide
def XBLL1 : TickCarrier Unit hQ :=
  advanceCarrier XBLL0 hlaw0BLL sel1BLL 1 seed164Prov [] hsel0BLL hfresh0BLL
theorem hlaw1BLL : Lawful XBLL1 := by decide
def props1BLL : List (Core × Bool) := proposals XBLL1.archive XBLL1.active
def sel2BLL : List (Core × Bool) → List QuestionId := anchoredSelect MOBLL 2 seed164Prov (supportAnchors MOBLL XBLL1)
theorem hsel1BLL : ∀ i ∈ sel2BLL props1BLL, ∃ p ∈ props1BLL,
    (childCore p.1 p.2 2 seed164Prov).id = i := anchoredSelect_hsel MOBLL 2 seed164Prov _ props1BLL
theorem hfresh1BLL : ∀ p ∈ props1BLL,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XBLL1.archive := by decide
def XBLL2 : TickCarrier Unit hQ :=
  advanceCarrier XBLL1 hlaw1BLL sel2BLL 2 seed164Prov [] hsel1BLL hfresh1BLL
theorem hlaw2BLL : Lawful XBLL2 := by decide
def props2BLL : List (Core × Bool) := proposals XBLL2.archive XBLL2.active
def sel3BLL : List (Core × Bool) → List QuestionId := anchoredSelect MOBLL 3 seed164Prov (supportAnchors MOBLL XBLL2)
theorem hsel2BLL : ∀ i ∈ sel3BLL props2BLL, ∃ p ∈ props2BLL,
    (childCore p.1 p.2 3 seed164Prov).id = i := anchoredSelect_hsel MOBLL 3 seed164Prov _ props2BLL
theorem hfresh2BLL : ∀ p ∈ props2BLL,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XBLL2.archive := by decide
def XBLL3 : TickCarrier Unit hQ :=
  advanceCarrier XBLL2 hlaw2BLL sel3BLL 3 seed164Prov [] hsel2BLL hfresh2BLL
theorem hlaw3BLL : Lawful XBLL3 := by decide
def props3BLL : List (Core × Bool) := proposals XBLL3.archive XBLL3.active
def sel4BLL : List (Core × Bool) → List QuestionId := anchoredSelect MOBLL 4 seed164Prov (supportAnchors MOBLL XBLL3)
theorem hsel3BLL : ∀ i ∈ sel4BLL props3BLL, ∃ p ∈ props3BLL,
    (childCore p.1 p.2 4 seed164Prov).id = i := anchoredSelect_hsel MOBLL 4 seed164Prov _ props3BLL
theorem hfresh3BLL : ∀ p ∈ props3BLL,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XBLL3.archive := by decide
def XBLL4 : TickCarrier Unit hQ :=
  advanceCarrier XBLL3 hlaw3BLL sel4BLL 4 seed164Prov [] hsel3BLL hfresh3BLL
theorem hlaw4BLL : Lawful XBLL4 := by decide
def props4BLL : List (Core × Bool) := proposals XBLL4.archive XBLL4.active
def sel5BLL : List (Core × Bool) → List QuestionId := anchoredSelect MOBLL 5 seed164Prov (supportAnchors MOBLL XBLL4)
theorem hsel4BLL : ∀ i ∈ sel5BLL props4BLL, ∃ p ∈ props4BLL,
    (childCore p.1 p.2 5 seed164Prov).id = i := anchoredSelect_hsel MOBLL 5 seed164Prov _ props4BLL
theorem hfresh4BLL : ∀ p ∈ props4BLL,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XBLL4.archive := by decide
def XBLL5 : TickCarrier Unit hQ :=
  advanceCarrier XBLL4 hlaw4BLL sel5BLL 5 seed164Prov [] hsel4BLL hfresh4BLL
theorem hlaw5BLL : Lawful XBLL5 := by decide
def props5BLL : List (Core × Bool) := proposals XBLL5.archive XBLL5.active
def sel6BLL : List (Core × Bool) → List QuestionId := anchoredSelect MOBLL 6 seed164Prov (supportAnchors MOBLL XBLL5)
theorem hsel5BLL : ∀ i ∈ sel6BLL props5BLL, ∃ p ∈ props5BLL,
    (childCore p.1 p.2 6 seed164Prov).id = i := anchoredSelect_hsel MOBLL 6 seed164Prov _ props5BLL
theorem hfresh5BLL : ∀ p ∈ props5BLL,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XBLL5.archive := by decide
def XBLL6 : TickCarrier Unit hQ :=
  advanceCarrier XBLL5 hlaw5BLL sel6BLL 6 seed164Prov [] hsel5BLL hfresh5BLL
theorem hlaw6BLL : Lawful XBLL6 := by decide
def props6BLL : List (Core × Bool) := proposals XBLL6.archive XBLL6.active
def sel7BLL : List (Core × Bool) → List QuestionId := anchoredSelect MOBLL 7 seed164Prov (supportAnchors MOBLL XBLL6)
theorem hsel6BLL : ∀ i ∈ sel7BLL props6BLL, ∃ p ∈ props6BLL,
    (childCore p.1 p.2 7 seed164Prov).id = i := anchoredSelect_hsel MOBLL 7 seed164Prov _ props6BLL
theorem hfresh6BLL : ∀ p ∈ props6BLL,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XBLL6.archive := by decide
def XBLL7 : TickCarrier Unit hQ :=
  advanceCarrier XBLL6 hlaw6BLL sel7BLL 7 seed164Prov [] hsel6BLL hfresh6BLL

def XCSL1 : TickCarrier Unit hQ := XepsSideL1
theorem hlaw1CSL : Lawful XCSL1 := hlawSideL1eps
def props1CSL : List (Core × Bool) := proposals XCSL1.archive XCSL1.active
def sel2CSL : List (Core × Bool) → List QuestionId := anchoredSelect MOeps 2 seed164Prov (seedAnchors MOeps Xeps0)
theorem hsel1CSL : ∀ i ∈ sel2CSL props1CSL, ∃ p ∈ props1CSL,
    (childCore p.1 p.2 2 seed164Prov).id = i := anchoredSelect_hsel MOeps 2 seed164Prov _ props1CSL
theorem hfresh1CSL : ∀ p ∈ props1CSL,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XCSL1.archive := by decide
def XCSL2 : TickCarrier Unit hQ :=
  advanceCarrier XCSL1 hlaw1CSL sel2CSL 2 seed164Prov [] hsel1CSL hfresh1CSL
theorem hlaw2CSL : Lawful XCSL2 := by decide
def props2CSL : List (Core × Bool) := proposals XCSL2.archive XCSL2.active
def sel3CSL : List (Core × Bool) → List QuestionId := anchoredSelect MOeps 3 seed164Prov (seedAnchors MOeps Xeps0)
theorem hsel2CSL : ∀ i ∈ sel3CSL props2CSL, ∃ p ∈ props2CSL,
    (childCore p.1 p.2 3 seed164Prov).id = i := anchoredSelect_hsel MOeps 3 seed164Prov _ props2CSL
theorem hfresh2CSL : ∀ p ∈ props2CSL,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XCSL2.archive := by decide
def XCSL3 : TickCarrier Unit hQ :=
  advanceCarrier XCSL2 hlaw2CSL sel3CSL 3 seed164Prov [] hsel2CSL hfresh2CSL
theorem hlaw3CSL : Lawful XCSL3 := by decide
def props3CSL : List (Core × Bool) := proposals XCSL3.archive XCSL3.active
def sel4CSL : List (Core × Bool) → List QuestionId := anchoredSelect MOeps 4 seed164Prov (seedAnchors MOeps Xeps0)
theorem hsel3CSL : ∀ i ∈ sel4CSL props3CSL, ∃ p ∈ props3CSL,
    (childCore p.1 p.2 4 seed164Prov).id = i := anchoredSelect_hsel MOeps 4 seed164Prov _ props3CSL
theorem hfresh3CSL : ∀ p ∈ props3CSL,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XCSL3.archive := by decide
def XCSL4 : TickCarrier Unit hQ :=
  advanceCarrier XCSL3 hlaw3CSL sel4CSL 4 seed164Prov [] hsel3CSL hfresh3CSL
theorem hlaw4CSL : Lawful XCSL4 := by decide
def props4CSL : List (Core × Bool) := proposals XCSL4.archive XCSL4.active
def sel5CSL : List (Core × Bool) → List QuestionId := anchoredSelect MOeps 5 seed164Prov (seedAnchors MOeps Xeps0)
theorem hsel4CSL : ∀ i ∈ sel5CSL props4CSL, ∃ p ∈ props4CSL,
    (childCore p.1 p.2 5 seed164Prov).id = i := anchoredSelect_hsel MOeps 5 seed164Prov _ props4CSL
theorem hfresh4CSL : ∀ p ∈ props4CSL,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XCSL4.archive := by decide
def XCSL5 : TickCarrier Unit hQ :=
  advanceCarrier XCSL4 hlaw4CSL sel5CSL 5 seed164Prov [] hsel4CSL hfresh4CSL
theorem hlaw5CSL : Lawful XCSL5 := by decide
def props5CSL : List (Core × Bool) := proposals XCSL5.archive XCSL5.active
def sel6CSL : List (Core × Bool) → List QuestionId := anchoredSelect MOeps 6 seed164Prov (seedAnchors MOeps Xeps0)
theorem hsel5CSL : ∀ i ∈ sel6CSL props5CSL, ∃ p ∈ props5CSL,
    (childCore p.1 p.2 6 seed164Prov).id = i := anchoredSelect_hsel MOeps 6 seed164Prov _ props5CSL
theorem hfresh5CSL : ∀ p ∈ props5CSL,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XCSL5.archive := by decide
def XCSL6 : TickCarrier Unit hQ :=
  advanceCarrier XCSL5 hlaw5CSL sel6CSL 6 seed164Prov [] hsel5CSL hfresh5CSL
theorem hlaw6CSL : Lawful XCSL6 := by decide
def props6CSL : List (Core × Bool) := proposals XCSL6.archive XCSL6.active
def sel7CSL : List (Core × Bool) → List QuestionId := anchoredSelect MOeps 7 seed164Prov (seedAnchors MOeps Xeps0)
theorem hsel6CSL : ∀ i ∈ sel7CSL props6CSL, ∃ p ∈ props6CSL,
    (childCore p.1 p.2 7 seed164Prov).id = i := anchoredSelect_hsel MOeps 7 seed164Prov _ props6CSL
theorem hfresh6CSL : ∀ p ∈ props6CSL,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XCSL6.archive := by decide
def XCSL7 : TickCarrier Unit hQ :=
  advanceCarrier XCSL6 hlaw6CSL sel7CSL 7 seed164Prov [] hsel6CSL hfresh6CSL

def XDSL1 : TickCarrier Unit hQ := XepsSideL1
theorem hlaw1DSL : Lawful XDSL1 := hlawSideL1eps
def props1DSL : List (Core × Bool) := proposals XDSL1.archive XDSL1.active
def sel2DSL : List (Core × Bool) → List QuestionId := anchoredSelect MOeps 2 seed164Prov (supportAnchors MOeps XDSL1)
theorem hsel1DSL : ∀ i ∈ sel2DSL props1DSL, ∃ p ∈ props1DSL,
    (childCore p.1 p.2 2 seed164Prov).id = i := anchoredSelect_hsel MOeps 2 seed164Prov _ props1DSL
theorem hfresh1DSL : ∀ p ∈ props1DSL,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XDSL1.archive := by decide
def XDSL2 : TickCarrier Unit hQ :=
  advanceCarrier XDSL1 hlaw1DSL sel2DSL 2 seed164Prov [] hsel1DSL hfresh1DSL
theorem hlaw2DSL : Lawful XDSL2 := by decide
def props2DSL : List (Core × Bool) := proposals XDSL2.archive XDSL2.active
def sel3DSL : List (Core × Bool) → List QuestionId := anchoredSelect MOeps 3 seed164Prov (supportAnchors MOeps XDSL2)
theorem hsel2DSL : ∀ i ∈ sel3DSL props2DSL, ∃ p ∈ props2DSL,
    (childCore p.1 p.2 3 seed164Prov).id = i := anchoredSelect_hsel MOeps 3 seed164Prov _ props2DSL
theorem hfresh2DSL : ∀ p ∈ props2DSL,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XDSL2.archive := by decide
def XDSL3 : TickCarrier Unit hQ :=
  advanceCarrier XDSL2 hlaw2DSL sel3DSL 3 seed164Prov [] hsel2DSL hfresh2DSL
theorem hlaw3DSL : Lawful XDSL3 := by decide
def props3DSL : List (Core × Bool) := proposals XDSL3.archive XDSL3.active
def sel4DSL : List (Core × Bool) → List QuestionId := anchoredSelect MOeps 4 seed164Prov (supportAnchors MOeps XDSL3)
theorem hsel3DSL : ∀ i ∈ sel4DSL props3DSL, ∃ p ∈ props3DSL,
    (childCore p.1 p.2 4 seed164Prov).id = i := anchoredSelect_hsel MOeps 4 seed164Prov _ props3DSL
theorem hfresh3DSL : ∀ p ∈ props3DSL,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XDSL3.archive := by decide
def XDSL4 : TickCarrier Unit hQ :=
  advanceCarrier XDSL3 hlaw3DSL sel4DSL 4 seed164Prov [] hsel3DSL hfresh3DSL
theorem hlaw4DSL : Lawful XDSL4 := by decide
def props4DSL : List (Core × Bool) := proposals XDSL4.archive XDSL4.active
def sel5DSL : List (Core × Bool) → List QuestionId := anchoredSelect MOeps 5 seed164Prov (supportAnchors MOeps XDSL4)
theorem hsel4DSL : ∀ i ∈ sel5DSL props4DSL, ∃ p ∈ props4DSL,
    (childCore p.1 p.2 5 seed164Prov).id = i := anchoredSelect_hsel MOeps 5 seed164Prov _ props4DSL
theorem hfresh4DSL : ∀ p ∈ props4DSL,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XDSL4.archive := by decide
def XDSL5 : TickCarrier Unit hQ :=
  advanceCarrier XDSL4 hlaw4DSL sel5DSL 5 seed164Prov [] hsel4DSL hfresh4DSL
theorem hlaw5DSL : Lawful XDSL5 := by decide
def props5DSL : List (Core × Bool) := proposals XDSL5.archive XDSL5.active
def sel6DSL : List (Core × Bool) → List QuestionId := anchoredSelect MOeps 6 seed164Prov (supportAnchors MOeps XDSL5)
theorem hsel5DSL : ∀ i ∈ sel6DSL props5DSL, ∃ p ∈ props5DSL,
    (childCore p.1 p.2 6 seed164Prov).id = i := anchoredSelect_hsel MOeps 6 seed164Prov _ props5DSL
theorem hfresh5DSL : ∀ p ∈ props5DSL,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XDSL5.archive := by decide
def XDSL6 : TickCarrier Unit hQ :=
  advanceCarrier XDSL5 hlaw5DSL sel6DSL 6 seed164Prov [] hsel5DSL hfresh5DSL
theorem hlaw6DSL : Lawful XDSL6 := by decide
def props6DSL : List (Core × Bool) := proposals XDSL6.archive XDSL6.active
def sel7DSL : List (Core × Bool) → List QuestionId := anchoredSelect MOeps 7 seed164Prov (supportAnchors MOeps XDSL6)
theorem hsel6DSL : ∀ i ∈ sel7DSL props6DSL, ∃ p ∈ props6DSL,
    (childCore p.1 p.2 7 seed164Prov).id = i := anchoredSelect_hsel MOeps 7 seed164Prov _ props6DSL
theorem hfresh6DSL : ∀ p ∈ props6DSL,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XDSL6.archive := by decide
def XDSL7 : TickCarrier Unit hQ :=
  advanceCarrier XDSL6 hlaw6DSL sel7DSL 7 seed164Prov [] hsel6DSL hfresh6DSL

/-! ## Remark 16.18 — the computed profiles

    Every value below is computed from the run it states. -/

/-- **The base profile is the empty-anchor case of the extended one**, which is
    the book's boxed sentence read as an equation: anchoring is an admissible
    alternative profile, not an omitted term of the base profile. -/
example : anchoredSelect MOeps 1 seed164Prov [] = axiomSelect MOeps 1 seed164Prov :=
  anchoredSelect_nil _ _ _

/-- **Seed as anchor: the root question is unchanged**, tick for tick equal to
    Theorem 16.5's own trace — the anchor `ε` contributes one equal term to every
    candidate at a tick. -/
theorem remark_16_18_seed_root_unchanged :
    activeWords XAE1 = activeWords Xeps1 ∧
    activeWords XAE2 = activeWords Xeps2 ∧
    activeWords XAE3 = activeWords Xeps3 ∧
    activeWords XAE4 = activeWords Xeps4 ∧
    activeWords XAE5 = activeWords Xeps5 ∧
    activeWords XAE6 = activeWords Xeps6 ∧
    activeWords XAE7 = activeWords Xeps7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Seed as anchor: the side-selected root is unchanged**, equal to Theorem
    16.8's trace from tick 2 on (tick 1 is the side selection itself, one
    admitted candidate, so no profile can move it). -/
theorem remark_16_18_seed_side_unchanged :
    activeWords XCSL2 = activeWords XepsSideL2 ∧
    activeWords XCSL3 = activeWords XepsSideL3 ∧
    activeWords XCSL4 = activeWords XepsSideL4 ∧
    activeWords XCSL5 = activeWords XepsSideL5 ∧
    activeWords XCSL6 = activeWords XepsSideL6 ∧
    activeWords XCSL7 = activeWords XepsSideL7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Seed as anchor: `𝒬_L ↦ L⁸`**, the forced first-tick pair lost, riding
    the ray of its last hand. -/
theorem remark_16_18_seed_QL :
    activeWords XAL1 = [List.replicate 2 false] ∧
    activeWords XAL2 = [List.replicate 3 false] ∧
    activeWords XAL3 = [List.replicate 4 false] ∧
    activeWords XAL4 = [List.replicate 5 false] ∧
    activeWords XAL5 = [List.replicate 6 false] ∧
    activeWords XAL6 = [List.replicate 7 false] ∧
    activeWords XAL7 = [List.replicate 8 false] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Seed as anchor: `𝒬_R ↦ R⁸`.** -/
theorem remark_16_18_seed_QR :
    activeWords XAR1 = [List.replicate 2 true] ∧
    activeWords XAR2 = [List.replicate 3 true] ∧
    activeWords XAR3 = [List.replicate 4 true] ∧
    activeWords XAR4 = [List.replicate 5 true] ∧
    activeWords XAR5 = [List.replicate 6 true] ∧
    activeWords XAR6 = [List.replicate 7 true] ∧
    activeWords XAR7 = [List.replicate 8 true] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Seed as anchor: `𝒬_LL ↦ L⁹`.** -/
theorem remark_16_18_seed_QLL :
    activeWords XALL1 = [List.replicate 3 false] ∧
    activeWords XALL2 = [List.replicate 4 false] ∧
    activeWords XALL3 = [List.replicate 5 false] ∧
    activeWords XALL4 = [List.replicate 6 false] ∧
    activeWords XALL5 = [List.replicate 7 false] ∧
    activeWords XALL6 = [List.replicate 8 false] ∧
    activeWords XALL7 = [List.replicate 9 false] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Current support as anchors: the same collapse on the lone seeds.** -/
theorem remark_16_18_support_lone_seeds :
    activeWords XBL1 = [List.replicate 2 false] ∧
    activeWords XBL2 = [List.replicate 3 false] ∧
    activeWords XBL3 = [List.replicate 4 false] ∧
    activeWords XBL4 = [List.replicate 5 false] ∧
    activeWords XBL5 = [List.replicate 6 false] ∧
    activeWords XBL6 = [List.replicate 7 false] ∧
    activeWords XBL7 = [List.replicate 8 false] ∧
    activeWords XBR1 = [List.replicate 2 true] ∧
    activeWords XBR2 = [List.replicate 3 true] ∧
    activeWords XBR3 = [List.replicate 4 true] ∧
    activeWords XBR4 = [List.replicate 5 true] ∧
    activeWords XBR5 = [List.replicate 6 true] ∧
    activeWords XBR6 = [List.replicate 7 true] ∧
    activeWords XBR7 = [List.replicate 8 true] ∧
    activeWords XBLL1 = [List.replicate 3 false] ∧
    activeWords XBLL2 = [List.replicate 4 false] ∧
    activeWords XBLL3 = [List.replicate 5 false] ∧
    activeWords XBLL4 = [List.replicate 6 false] ∧
    activeWords XBLL5 = [List.replicate 7 false] ∧
    activeWords XBLL6 = [List.replicate 8 false] ∧
    activeWords XBLL7 = [List.replicate 9 false] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Current support as anchors: the side-selected root collapses too,
    `𝒬_ε^L ↦ L⁷`** — the one the seed anchor left alone. -/
theorem remark_16_18_support_side_collapses :
    activeWords XDSL1 = [List.replicate 1 false] ∧
    activeWords XDSL2 = [List.replicate 2 false] ∧
    activeWords XDSL3 = [List.replicate 3 false] ∧
    activeWords XDSL4 = [List.replicate 4 false] ∧
    activeWords XDSL5 = [List.replicate 5 false] ∧
    activeWords XDSL6 = [List.replicate 6 false] ∧
    activeWords XDSL7 = [List.replicate 7 false] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Current support as anchors, on the root: unchanged.** Computed, and not
    a claim the book makes in words; recorded because the root is side-symmetric
    and Theorem 16.2 already forbids it a singleton under any side-equivariant
    profile, which this profile is. -/
theorem remark_16_18_support_root_unchanged :
    activeWords XBE1 = activeWords Xeps1 ∧
    activeWords XBE2 = activeWords Xeps2 ∧
    activeWords XBE3 = activeWords Xeps3 ∧
    activeWords XBE4 = activeWords Xeps4 ∧
    activeWords XBE5 = activeWords Xeps5 ∧
    activeWords XBE6 = activeWords Xeps6 ∧
    activeWords XBE7 = activeWords Xeps7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

#print axioms anchoredSelect_nil
#print axioms remark_16_18_seed_root_unchanged
#print axioms remark_16_18_seed_side_unchanged
#print axioms remark_16_18_seed_QL
#print axioms remark_16_18_seed_QR
#print axioms remark_16_18_seed_QLL
#print axioms remark_16_18_support_lone_seeds
#print axioms remark_16_18_support_side_collapses
#print axioms remark_16_18_support_root_unchanged

end Anchored
end Two
end RatioSpace
