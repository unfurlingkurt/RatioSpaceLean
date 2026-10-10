/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.RootOrbit
/-!
  Elements II §16, Definition 16.16 and Theorem 16.17 — the face-bearing
  lone-seed questions `𝒬_LL` and `𝒬_RR`, closed at the declared horizon.

  Same construction as `RootOrbit.lean`: seven concrete `advanceCarrier`
  calls per question, `hsel`/`hfresh` discharged by `decide` on each step's
  closed data. Values are read off the run before being asserted.
-/
set_option linter.style.longLine false
set_option maxRecDepth 200000

namespace RatioSpace
namespace Two
namespace LoneSeed

open Mat2 Word Frame Pres RatioSpace RatioSpace.Zphi Advance Accumulation RootOrbit

/-- `𝒬_{LL}`'s tick-zero carrier (Definition 16.16). -/
def XLL0 : TickCarrier Unit hQ := X0 [false, false]
def MOLL : Mat2 := XLL0.observer.matrix
theorem hlaw0LL : Lawful XLL0 := by decide
def props0LL : List (Core × Bool) := proposals XLL0.archive XLL0.active
def sel1LL : List (Core × Bool) → List QuestionId := axiomSelect MOLL 1 seed164Prov
theorem hsel0LL : ∀ i ∈ sel1LL props0LL, ∃ p ∈ props0LL,
    (childCore p.1 p.2 1 seed164Prov).id = i := axiomSelect_hsel MOLL 1 seed164Prov props0LL
theorem hfresh0LL : ∀ p ∈ props0LL,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XLL0.archive := by decide
def XLL1 : TickCarrier Unit hQ :=
  advanceCarrier XLL0 hlaw0LL sel1LL 1 seed164Prov [] hsel0LL hfresh0LL
theorem hlaw1LL : Lawful XLL1 := by decide
def props1LL : List (Core × Bool) := proposals XLL1.archive XLL1.active
def sel2LL : List (Core × Bool) → List QuestionId := axiomSelect MOLL 2 seed164Prov
theorem hsel1LL : ∀ i ∈ sel2LL props1LL, ∃ p ∈ props1LL,
    (childCore p.1 p.2 2 seed164Prov).id = i := axiomSelect_hsel MOLL 2 seed164Prov props1LL
theorem hfresh1LL : ∀ p ∈ props1LL,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XLL1.archive := by decide
def XLL2 : TickCarrier Unit hQ :=
  advanceCarrier XLL1 hlaw1LL sel2LL 2 seed164Prov [] hsel1LL hfresh1LL
theorem hlaw2LL : Lawful XLL2 := by decide
def props2LL : List (Core × Bool) := proposals XLL2.archive XLL2.active
def sel3LL : List (Core × Bool) → List QuestionId := axiomSelect MOLL 3 seed164Prov
theorem hsel2LL : ∀ i ∈ sel3LL props2LL, ∃ p ∈ props2LL,
    (childCore p.1 p.2 3 seed164Prov).id = i := axiomSelect_hsel MOLL 3 seed164Prov props2LL
theorem hfresh2LL : ∀ p ∈ props2LL,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XLL2.archive := by decide
def XLL3 : TickCarrier Unit hQ :=
  advanceCarrier XLL2 hlaw2LL sel3LL 3 seed164Prov [] hsel2LL hfresh2LL
theorem hlaw3LL : Lawful XLL3 := by decide
def props3LL : List (Core × Bool) := proposals XLL3.archive XLL3.active
def sel4LL : List (Core × Bool) → List QuestionId := axiomSelect MOLL 4 seed164Prov
theorem hsel3LL : ∀ i ∈ sel4LL props3LL, ∃ p ∈ props3LL,
    (childCore p.1 p.2 4 seed164Prov).id = i := axiomSelect_hsel MOLL 4 seed164Prov props3LL
theorem hfresh3LL : ∀ p ∈ props3LL,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XLL3.archive := by decide
def XLL4 : TickCarrier Unit hQ :=
  advanceCarrier XLL3 hlaw3LL sel4LL 4 seed164Prov [] hsel3LL hfresh3LL
theorem hlaw4LL : Lawful XLL4 := by decide
def props4LL : List (Core × Bool) := proposals XLL4.archive XLL4.active
def sel5LL : List (Core × Bool) → List QuestionId := axiomSelect MOLL 5 seed164Prov
theorem hsel4LL : ∀ i ∈ sel5LL props4LL, ∃ p ∈ props4LL,
    (childCore p.1 p.2 5 seed164Prov).id = i := axiomSelect_hsel MOLL 5 seed164Prov props4LL
theorem hfresh4LL : ∀ p ∈ props4LL,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XLL4.archive := by decide
def XLL5 : TickCarrier Unit hQ :=
  advanceCarrier XLL4 hlaw4LL sel5LL 5 seed164Prov [] hsel4LL hfresh4LL
theorem hlaw5LL : Lawful XLL5 := by decide
def props5LL : List (Core × Bool) := proposals XLL5.archive XLL5.active
def sel6LL : List (Core × Bool) → List QuestionId := axiomSelect MOLL 6 seed164Prov
theorem hsel5LL : ∀ i ∈ sel6LL props5LL, ∃ p ∈ props5LL,
    (childCore p.1 p.2 6 seed164Prov).id = i := axiomSelect_hsel MOLL 6 seed164Prov props5LL
theorem hfresh5LL : ∀ p ∈ props5LL,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XLL5.archive := by decide
def XLL6 : TickCarrier Unit hQ :=
  advanceCarrier XLL5 hlaw5LL sel6LL 6 seed164Prov [] hsel5LL hfresh5LL
theorem hlaw6LL : Lawful XLL6 := by decide
def props6LL : List (Core × Bool) := proposals XLL6.archive XLL6.active
def sel7LL : List (Core × Bool) → List QuestionId := axiomSelect MOLL 7 seed164Prov
theorem hsel6LL : ∀ i ∈ sel7LL props6LL, ∃ p ∈ props6LL,
    (childCore p.1 p.2 7 seed164Prov).id = i := axiomSelect_hsel MOLL 7 seed164Prov props6LL
theorem hfresh6LL : ∀ p ∈ props6LL,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XLL6.archive := by decide
def XLL7 : TickCarrier Unit hQ :=
  advanceCarrier XLL6 hlaw6LL sel7LL 7 seed164Prov [] hsel6LL hfresh6LL
def props6famLL : List IPres := admittedFam MOLL 7 seed164Prov props6LL

/-- `𝒬_{RR}`'s tick-zero carrier (Definition 16.16). -/
def XRR0 : TickCarrier Unit hQ := X0 [true, true]
def MORR : Mat2 := XRR0.observer.matrix
theorem hlaw0RR : Lawful XRR0 := by decide
def props0RR : List (Core × Bool) := proposals XRR0.archive XRR0.active
def sel1RR : List (Core × Bool) → List QuestionId := axiomSelect MORR 1 seed164Prov
theorem hsel0RR : ∀ i ∈ sel1RR props0RR, ∃ p ∈ props0RR,
    (childCore p.1 p.2 1 seed164Prov).id = i := axiomSelect_hsel MORR 1 seed164Prov props0RR
theorem hfresh0RR : ∀ p ∈ props0RR,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XRR0.archive := by decide
def XRR1 : TickCarrier Unit hQ :=
  advanceCarrier XRR0 hlaw0RR sel1RR 1 seed164Prov [] hsel0RR hfresh0RR
theorem hlaw1RR : Lawful XRR1 := by decide
def props1RR : List (Core × Bool) := proposals XRR1.archive XRR1.active
def sel2RR : List (Core × Bool) → List QuestionId := axiomSelect MORR 2 seed164Prov
theorem hsel1RR : ∀ i ∈ sel2RR props1RR, ∃ p ∈ props1RR,
    (childCore p.1 p.2 2 seed164Prov).id = i := axiomSelect_hsel MORR 2 seed164Prov props1RR
theorem hfresh1RR : ∀ p ∈ props1RR,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XRR1.archive := by decide
def XRR2 : TickCarrier Unit hQ :=
  advanceCarrier XRR1 hlaw1RR sel2RR 2 seed164Prov [] hsel1RR hfresh1RR
theorem hlaw2RR : Lawful XRR2 := by decide
def props2RR : List (Core × Bool) := proposals XRR2.archive XRR2.active
def sel3RR : List (Core × Bool) → List QuestionId := axiomSelect MORR 3 seed164Prov
theorem hsel2RR : ∀ i ∈ sel3RR props2RR, ∃ p ∈ props2RR,
    (childCore p.1 p.2 3 seed164Prov).id = i := axiomSelect_hsel MORR 3 seed164Prov props2RR
theorem hfresh2RR : ∀ p ∈ props2RR,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XRR2.archive := by decide
def XRR3 : TickCarrier Unit hQ :=
  advanceCarrier XRR2 hlaw2RR sel3RR 3 seed164Prov [] hsel2RR hfresh2RR
theorem hlaw3RR : Lawful XRR3 := by decide
def props3RR : List (Core × Bool) := proposals XRR3.archive XRR3.active
def sel4RR : List (Core × Bool) → List QuestionId := axiomSelect MORR 4 seed164Prov
theorem hsel3RR : ∀ i ∈ sel4RR props3RR, ∃ p ∈ props3RR,
    (childCore p.1 p.2 4 seed164Prov).id = i := axiomSelect_hsel MORR 4 seed164Prov props3RR
theorem hfresh3RR : ∀ p ∈ props3RR,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XRR3.archive := by decide
def XRR4 : TickCarrier Unit hQ :=
  advanceCarrier XRR3 hlaw3RR sel4RR 4 seed164Prov [] hsel3RR hfresh3RR
theorem hlaw4RR : Lawful XRR4 := by decide
def props4RR : List (Core × Bool) := proposals XRR4.archive XRR4.active
def sel5RR : List (Core × Bool) → List QuestionId := axiomSelect MORR 5 seed164Prov
theorem hsel4RR : ∀ i ∈ sel5RR props4RR, ∃ p ∈ props4RR,
    (childCore p.1 p.2 5 seed164Prov).id = i := axiomSelect_hsel MORR 5 seed164Prov props4RR
theorem hfresh4RR : ∀ p ∈ props4RR,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XRR4.archive := by decide
def XRR5 : TickCarrier Unit hQ :=
  advanceCarrier XRR4 hlaw4RR sel5RR 5 seed164Prov [] hsel4RR hfresh4RR
theorem hlaw5RR : Lawful XRR5 := by decide
def props5RR : List (Core × Bool) := proposals XRR5.archive XRR5.active
def sel6RR : List (Core × Bool) → List QuestionId := axiomSelect MORR 6 seed164Prov
theorem hsel5RR : ∀ i ∈ sel6RR props5RR, ∃ p ∈ props5RR,
    (childCore p.1 p.2 6 seed164Prov).id = i := axiomSelect_hsel MORR 6 seed164Prov props5RR
theorem hfresh5RR : ∀ p ∈ props5RR,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XRR5.archive := by decide
def XRR6 : TickCarrier Unit hQ :=
  advanceCarrier XRR5 hlaw5RR sel6RR 6 seed164Prov [] hsel5RR hfresh5RR
theorem hlaw6RR : Lawful XRR6 := by decide
def props6RR : List (Core × Bool) := proposals XRR6.archive XRR6.active
def sel7RR : List (Core × Bool) → List QuestionId := axiomSelect MORR 7 seed164Prov
theorem hsel6RR : ∀ i ∈ sel7RR props6RR, ∃ p ∈ props6RR,
    (childCore p.1 p.2 7 seed164Prov).id = i := axiomSelect_hsel MORR 7 seed164Prov props6RR
theorem hfresh6RR : ∀ p ∈ props6RR,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XRR6.archive := by decide
def XRR7 : TickCarrier Unit hQ :=
  advanceCarrier XRR6 hlaw6RR sel7RR 7 seed164Prov [] hsel6RR hfresh6RR
def props6famRR : List IPres := admittedFam MORR 7 seed164Prov props6RR

/-! ## Definition 16.16 — the two questions

    `𝒬_LL` and `𝒬_RR` are Definition 16.4's questions with seed `LL`/`RR`: the
    same `canonicalQuestion` with a different seed word and nothing else. -/

theorem def_16_16_LL : XLL0.question = canonicalQuestion [false, false] := rfl
theorem def_16_16_RR : XRR0.question = canonicalQuestion [true, true] := rfl

/-! ## Theorem 16.17 — seven-tick closure of `𝒬_LL` and `𝒬_RR` -/

/-- **Theorem 16.17, the support table for `𝒬_LL`**, ticks 1–7, exactly the
    book's. Closes on the occurrence singleton `LLLRRRRRR`. -/
theorem theorem_16_17_LL :
    activeWords XLL1 = [[false, false, false], [false, false, true]] ∧
    activeWords XLL2 = [[false, false, false, true]] ∧
    activeWords XLL3 = [[false, false, false, true, false], [false, false, false, true, true]] ∧
    activeWords XLL4 = [[false, false, false, true, false, false], [false, false, false, true, true, true]] ∧
    activeWords XLL5 = [[false, false, false, true, true, true, true]] ∧
    activeWords XLL6 = [[false, false, false, true, true, true, true, false], [false, false, false, true, true, true, true, true]] ∧
    activeWords XLL7 = [[false, false, false, true, true, true, true, true, true]] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Side `R`**, decided independently rather than mirrored: a decided trace is
    the stronger witness that the kernel itself is side-symmetric. -/
theorem theorem_16_17_RR :
    activeWords XRR1 = [[true, true, false], [true, true, true]] ∧
    activeWords XRR2 = [[true, true, true, false]] ∧
    activeWords XRR3 = [[true, true, true, false, false], [true, true, true, false, true]] ∧
    activeWords XRR4 = [[true, true, true, false, false, false], [true, true, true, false, true, true]] ∧
    activeWords XRR5 = [[true, true, true, false, false, false, false]] ∧
    activeWords XRR6 = [[true, true, true, false, false, false, false, false], [true, true, true, false, false, false, false, true]] ∧
    activeWords XRR7 = [[true, true, true, false, false, false, false, false, false]] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The `λ_O` column for `𝒬_LL`**, `1:3` at the seed through `7:22`. -/
theorem theorem_16_17_LL_addressed :
    addressedList [[false, false]] = [(⟨1, 3, by decide⟩ : Pres)] ∧
    addressedList (activeWords XLL1) = [(⟨1, 4, by decide⟩ : Pres), ⟨2, 5, by decide⟩] ∧
    addressedList (activeWords XLL2) = [(⟨2, 7, by decide⟩ : Pres)] ∧
    addressedList (activeWords XLL3) = [(⟨3, 11, by decide⟩ : Pres), ⟨3, 10, by decide⟩] ∧
    addressedList (activeWords XLL4) = [(⟨4, 15, by decide⟩ : Pres), ⟨4, 13, by decide⟩] ∧
    addressedList (activeWords XLL5) = [(⟨5, 16, by decide⟩ : Pres)] ∧
    addressedList (activeWords XLL6) = [(⟨9, 29, by decide⟩ : Pres), ⟨6, 19, by decide⟩] ∧
    addressedList (activeWords XLL7) = [(⟨7, 22, by decide⟩ : Pres)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The `λ_O` column for `𝒬_RR`**, the reciprocals, `22:7` at tick 7. -/
theorem theorem_16_17_RR_addressed :
    addressedList (activeWords XRR1) = [(⟨5, 2, by decide⟩ : Pres), ⟨4, 1, by decide⟩] ∧
    addressedList (activeWords XRR2) = [(⟨7, 2, by decide⟩ : Pres)] ∧
    addressedList (activeWords XRR3) = [(⟨10, 3, by decide⟩ : Pres), ⟨11, 3, by decide⟩] ∧
    addressedList (activeWords XRR4) = [(⟨13, 4, by decide⟩ : Pres), ⟨15, 4, by decide⟩] ∧
    addressedList (activeWords XRR5) = [(⟨16, 5, by decide⟩ : Pres)] ∧
    addressedList (activeWords XRR6) = [(⟨19, 6, by decide⟩ : Pres), ⟨29, 9, by decide⟩] ∧
    addressedList (activeWords XRR7) = [(⟨22, 7, by decide⟩ : Pres)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The terminal admitted family and certificates for `𝒬_LL`**: addresses
    `13:42, 14:45, 11:35, 7:22`, the tension matrix (each row's multiset is the
    book's histogram), and all eight 41-digit score coefficients. -/
theorem theorem_16_17_LL_terminal :
    props6famLL.map (fun y => (y.p, y.q)) = [(13, 42), (14, 45), (11, 35), (7, 22)] ∧
    props6famLL.map (tensions props6famLL) =
      [[0, 195, 65, 39], [195, 0, 98, 44], [65, 98, 0, 83], [39, 44, 83, 0]] ∧
    props6famLL.map (coherenceOf props6famLL) =
      [(⟨-40934782466626840596168753000739520615589, 25299086886458645685589389199911422076481⟩ : Zphi), (⟨-40934782466626840595949829977125838173950, 25299086886458645685454087330398270498148⟩ : Zphi), (⟨218762467412848766651, -135202640323931812987⟩ : Zphi), (⟨-160500642783798072, 99194852456592750⟩ : Zphi)] := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The three strict comparisons.** The book certifies each sign with Lemma
    8.6's `(s, b)` pair; `decidableLT` decides the same comparison directly. -/
theorem theorem_16_17_LL_selected_strict :
    (⟨-40934782466626840596168753000739520615589, 25299086886458645685589389199911422076481⟩ : Zphi) < (⟨-160500642783798072, 99194852456592750⟩ : Zphi) ∧ (⟨-40934782466626840595949829977125838173950, 25299086886458645685454087330398270498148⟩ : Zphi) < (⟨-160500642783798072, 99194852456592750⟩ : Zphi) ∧ (⟨218762467412848766651, -135202640323931812987⟩ : Zphi) < (⟨-160500642783798072, 99194852456592750⟩ : Zphi) := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The `𝒬_RR` family, same score multiset**, in exactly reversed order. -/
theorem theorem_16_17_RR_terminal :
    props6famRR.map (fun y => (y.p, y.q)) = [(22, 7), (35, 11), (45, 14), (42, 13)] ∧
    props6famRR.map (tensions props6famRR) =
      [[0, 83, 44, 39], [83, 0, 98, 65], [44, 98, 0, 195], [39, 65, 195, 0]] ∧
    props6famRR.map (coherenceOf props6famRR) =
      [(⟨-160500642783798072, 99194852456592750⟩ : Zphi), (⟨218762467412848766651, -135202640323931812987⟩ : Zphi), (⟨-40934782466626840595949829977125838173950, 25299086886458645685454087330398270498148⟩ : Zphi), (⟨-40934782466626840596168753000739520615589, 25299086886458645685589389199911422076481⟩ : Zphi)] := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The closure itself, as Construction Axiom II.1's output**: the support of
    each terminal family is exactly the selected occurrence. -/
theorem theorem_16_17_LL_closes :
    (support props6famLL).map (fun y => (y.p, y.q)) = [(7, 22)] := by decide
theorem theorem_16_17_RR_closes :
    (support props6famRR).map (fun y => (y.p, y.q)) = [(22, 7)] := by decide

#print axioms def_16_16_LL
#print axioms def_16_16_RR
#print axioms theorem_16_17_LL
#print axioms theorem_16_17_RR
#print axioms theorem_16_17_LL_addressed
#print axioms theorem_16_17_RR_addressed
#print axioms theorem_16_17_LL_terminal
#print axioms theorem_16_17_LL_selected_strict
#print axioms theorem_16_17_RR_terminal
#print axioms theorem_16_17_LL_closes
#print axioms theorem_16_17_RR_closes

end LoneSeed
end Two
end RatioSpace
