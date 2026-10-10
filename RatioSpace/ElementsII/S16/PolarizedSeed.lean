/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.RootOrbit
/-!
  Elements II §16, Proposition 16.9(ii) — the two named lone-seed closing
  instances not already in the tree: the length-4 polarized seeds `LLLR` and
  `RRRL`, closed at the declared horizon `h_Q=7` on the occurrence singletons
  `LLLRRRRRRRR`/`RRRLLLLLLLL`, addressed `9:28`/`28:9`.

  `research/experiments/lone_seed_beat.py`'s exhaustive 1023-seed, 13-tick run
  confirms Proposition 16.9(ii) exactly for every seed of length 0 through 9,
  including that these two close at tick **7**, not tick 9 — `9:28` is the
  terminal ADDRESS `λ_O`, not a tick count, exactly as `LL`'s own `7:22` is an
  address at the same tick 7. Both seeds close one tick "late" relative to the
  generic even-tick pattern for the same reason `LL`/`RR` do: exactly one
  pair-preserving advance (here the very first, `1→2`, versus `LL`'s `3→4`)
  flips the singleton/pair parity once, so the closing tick is odd instead of
  even, and it is still the declared horizon `7` — the seed word being two
  letters longer than `LL` changes nothing about the tick count, only the
  word length reached by then (`LLLRRRRRRRR` is 11 letters where `LL`'s
  closing word `LLLRRRRRR` is 9).

  Same construction as `LoneSeed.lean`/`RootOrbit.lean`: seven concrete
  `advanceCarrier` calls per question, `hsel`/`hfresh` discharged by `decide`
  on each step's closed data. Values are read off the run before being
  asserted (`lone_seed_beat.py`'s own trace for seed `LLLR`, cross-checked
  against `RRRL` by decided Lean computation, not by mirroring).
-/
set_option linter.style.longLine false
set_option maxRecDepth 800000

namespace RatioSpace
namespace Two
namespace LoneSeed916

open Mat2 Word Frame Pres RatioSpace RatioSpace.Zphi Advance Accumulation RootOrbit

/-- `𝒬_{LLLR}`'s tick-zero carrier (Definition 16.4's construction, seed
    `LLLR`). -/
def XLLLR0 : TickCarrier Unit hQ := X0 [false, false, false, true]
def MOLLLR : Mat2 := XLLLR0.observer.matrix
theorem hlaw0LLLR : Lawful XLLLR0 := by decide
def props0LLLR : List (Core × Bool) := proposals XLLLR0.archive XLLLR0.active
def sel1LLLR : List (Core × Bool) → List QuestionId := axiomSelect MOLLLR 1 seed164Prov
theorem hsel0LLLR : ∀ i ∈ sel1LLLR props0LLLR, ∃ p ∈ props0LLLR,
    (childCore p.1 p.2 1 seed164Prov).id = i := axiomSelect_hsel MOLLLR 1 seed164Prov props0LLLR
theorem hfresh0LLLR : ∀ p ∈ props0LLLR,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XLLLR0.archive := by decide
def XLLLR1 : TickCarrier Unit hQ :=
  advanceCarrier XLLLR0 hlaw0LLLR sel1LLLR 1 seed164Prov [] hsel0LLLR hfresh0LLLR
theorem hlaw1LLLR : Lawful XLLLR1 := by decide
def props1LLLR : List (Core × Bool) := proposals XLLLR1.archive XLLLR1.active
def sel2LLLR : List (Core × Bool) → List QuestionId := axiomSelect MOLLLR 2 seed164Prov
theorem hsel1LLLR : ∀ i ∈ sel2LLLR props1LLLR, ∃ p ∈ props1LLLR,
    (childCore p.1 p.2 2 seed164Prov).id = i := axiomSelect_hsel MOLLLR 2 seed164Prov props1LLLR
theorem hfresh1LLLR : ∀ p ∈ props1LLLR,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XLLLR1.archive := by decide
def XLLLR2 : TickCarrier Unit hQ :=
  advanceCarrier XLLLR1 hlaw1LLLR sel2LLLR 2 seed164Prov [] hsel1LLLR hfresh1LLLR
theorem hlaw2LLLR : Lawful XLLLR2 := by decide
def props2LLLR : List (Core × Bool) := proposals XLLLR2.archive XLLLR2.active
def sel3LLLR : List (Core × Bool) → List QuestionId := axiomSelect MOLLLR 3 seed164Prov
theorem hsel2LLLR : ∀ i ∈ sel3LLLR props2LLLR, ∃ p ∈ props2LLLR,
    (childCore p.1 p.2 3 seed164Prov).id = i := axiomSelect_hsel MOLLLR 3 seed164Prov props2LLLR
theorem hfresh2LLLR : ∀ p ∈ props2LLLR,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XLLLR2.archive := by decide
def XLLLR3 : TickCarrier Unit hQ :=
  advanceCarrier XLLLR2 hlaw2LLLR sel3LLLR 3 seed164Prov [] hsel2LLLR hfresh2LLLR
theorem hlaw3LLLR : Lawful XLLLR3 := by decide
def props3LLLR : List (Core × Bool) := proposals XLLLR3.archive XLLLR3.active
def sel4LLLR : List (Core × Bool) → List QuestionId := axiomSelect MOLLLR 4 seed164Prov
theorem hsel3LLLR : ∀ i ∈ sel4LLLR props3LLLR, ∃ p ∈ props3LLLR,
    (childCore p.1 p.2 4 seed164Prov).id = i := axiomSelect_hsel MOLLLR 4 seed164Prov props3LLLR
theorem hfresh3LLLR : ∀ p ∈ props3LLLR,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XLLLR3.archive := by decide
def XLLLR4 : TickCarrier Unit hQ :=
  advanceCarrier XLLLR3 hlaw3LLLR sel4LLLR 4 seed164Prov [] hsel3LLLR hfresh3LLLR
theorem hlaw4LLLR : Lawful XLLLR4 := by decide
def props4LLLR : List (Core × Bool) := proposals XLLLR4.archive XLLLR4.active
def sel5LLLR : List (Core × Bool) → List QuestionId := axiomSelect MOLLLR 5 seed164Prov
theorem hsel4LLLR : ∀ i ∈ sel5LLLR props4LLLR, ∃ p ∈ props4LLLR,
    (childCore p.1 p.2 5 seed164Prov).id = i := axiomSelect_hsel MOLLLR 5 seed164Prov props4LLLR
theorem hfresh4LLLR : ∀ p ∈ props4LLLR,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XLLLR4.archive := by decide
def XLLLR5 : TickCarrier Unit hQ :=
  advanceCarrier XLLLR4 hlaw4LLLR sel5LLLR 5 seed164Prov [] hsel4LLLR hfresh4LLLR
theorem hlaw5LLLR : Lawful XLLLR5 := by decide
def props5LLLR : List (Core × Bool) := proposals XLLLR5.archive XLLLR5.active
def sel6LLLR : List (Core × Bool) → List QuestionId := axiomSelect MOLLLR 6 seed164Prov
theorem hsel5LLLR : ∀ i ∈ sel6LLLR props5LLLR, ∃ p ∈ props5LLLR,
    (childCore p.1 p.2 6 seed164Prov).id = i := axiomSelect_hsel MOLLLR 6 seed164Prov props5LLLR
theorem hfresh5LLLR : ∀ p ∈ props5LLLR,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XLLLR5.archive := by decide
def XLLLR6 : TickCarrier Unit hQ :=
  advanceCarrier XLLLR5 hlaw5LLLR sel6LLLR 6 seed164Prov [] hsel5LLLR hfresh5LLLR
theorem hlaw6LLLR : Lawful XLLLR6 := by decide
def props6LLLR : List (Core × Bool) := proposals XLLLR6.archive XLLLR6.active
def sel7LLLR : List (Core × Bool) → List QuestionId := axiomSelect MOLLLR 7 seed164Prov
theorem hsel6LLLR : ∀ i ∈ sel7LLLR props6LLLR, ∃ p ∈ props6LLLR,
    (childCore p.1 p.2 7 seed164Prov).id = i := axiomSelect_hsel MOLLLR 7 seed164Prov props6LLLR
theorem hfresh6LLLR : ∀ p ∈ props6LLLR,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XLLLR6.archive := by decide
def XLLLR7 : TickCarrier Unit hQ :=
  advanceCarrier XLLLR6 hlaw6LLLR sel7LLLR 7 seed164Prov [] hsel6LLLR hfresh6LLLR

/-- `𝒬_{RRRL}`'s tick-zero carrier, the side mirror. -/
def XRRRL0 : TickCarrier Unit hQ := X0 [true, true, true, false]
def MORRRL : Mat2 := XRRRL0.observer.matrix
theorem hlaw0RRRL : Lawful XRRRL0 := by decide
def props0RRRL : List (Core × Bool) := proposals XRRRL0.archive XRRRL0.active
def sel1RRRL : List (Core × Bool) → List QuestionId := axiomSelect MORRRL 1 seed164Prov
theorem hsel0RRRL : ∀ i ∈ sel1RRRL props0RRRL, ∃ p ∈ props0RRRL,
    (childCore p.1 p.2 1 seed164Prov).id = i := axiomSelect_hsel MORRRL 1 seed164Prov props0RRRL
theorem hfresh0RRRL : ∀ p ∈ props0RRRL,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XRRRL0.archive := by decide
def XRRRL1 : TickCarrier Unit hQ :=
  advanceCarrier XRRRL0 hlaw0RRRL sel1RRRL 1 seed164Prov [] hsel0RRRL hfresh0RRRL
theorem hlaw1RRRL : Lawful XRRRL1 := by decide
def props1RRRL : List (Core × Bool) := proposals XRRRL1.archive XRRRL1.active
def sel2RRRL : List (Core × Bool) → List QuestionId := axiomSelect MORRRL 2 seed164Prov
theorem hsel1RRRL : ∀ i ∈ sel2RRRL props1RRRL, ∃ p ∈ props1RRRL,
    (childCore p.1 p.2 2 seed164Prov).id = i := axiomSelect_hsel MORRRL 2 seed164Prov props1RRRL
theorem hfresh1RRRL : ∀ p ∈ props1RRRL,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XRRRL1.archive := by decide
def XRRRL2 : TickCarrier Unit hQ :=
  advanceCarrier XRRRL1 hlaw1RRRL sel2RRRL 2 seed164Prov [] hsel1RRRL hfresh1RRRL
theorem hlaw2RRRL : Lawful XRRRL2 := by decide
def props2RRRL : List (Core × Bool) := proposals XRRRL2.archive XRRRL2.active
def sel3RRRL : List (Core × Bool) → List QuestionId := axiomSelect MORRRL 3 seed164Prov
theorem hsel2RRRL : ∀ i ∈ sel3RRRL props2RRRL, ∃ p ∈ props2RRRL,
    (childCore p.1 p.2 3 seed164Prov).id = i := axiomSelect_hsel MORRRL 3 seed164Prov props2RRRL
theorem hfresh2RRRL : ∀ p ∈ props2RRRL,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XRRRL2.archive := by decide
def XRRRL3 : TickCarrier Unit hQ :=
  advanceCarrier XRRRL2 hlaw2RRRL sel3RRRL 3 seed164Prov [] hsel2RRRL hfresh2RRRL
theorem hlaw3RRRL : Lawful XRRRL3 := by decide
def props3RRRL : List (Core × Bool) := proposals XRRRL3.archive XRRRL3.active
def sel4RRRL : List (Core × Bool) → List QuestionId := axiomSelect MORRRL 4 seed164Prov
theorem hsel3RRRL : ∀ i ∈ sel4RRRL props3RRRL, ∃ p ∈ props3RRRL,
    (childCore p.1 p.2 4 seed164Prov).id = i := axiomSelect_hsel MORRRL 4 seed164Prov props3RRRL
theorem hfresh3RRRL : ∀ p ∈ props3RRRL,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XRRRL3.archive := by decide
def XRRRL4 : TickCarrier Unit hQ :=
  advanceCarrier XRRRL3 hlaw3RRRL sel4RRRL 4 seed164Prov [] hsel3RRRL hfresh3RRRL
theorem hlaw4RRRL : Lawful XRRRL4 := by decide
def props4RRRL : List (Core × Bool) := proposals XRRRL4.archive XRRRL4.active
def sel5RRRL : List (Core × Bool) → List QuestionId := axiomSelect MORRRL 5 seed164Prov
theorem hsel4RRRL : ∀ i ∈ sel5RRRL props4RRRL, ∃ p ∈ props4RRRL,
    (childCore p.1 p.2 5 seed164Prov).id = i := axiomSelect_hsel MORRRL 5 seed164Prov props4RRRL
theorem hfresh4RRRL : ∀ p ∈ props4RRRL,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XRRRL4.archive := by decide
def XRRRL5 : TickCarrier Unit hQ :=
  advanceCarrier XRRRL4 hlaw4RRRL sel5RRRL 5 seed164Prov [] hsel4RRRL hfresh4RRRL
theorem hlaw5RRRL : Lawful XRRRL5 := by decide
def props5RRRL : List (Core × Bool) := proposals XRRRL5.archive XRRRL5.active
def sel6RRRL : List (Core × Bool) → List QuestionId := axiomSelect MORRRL 6 seed164Prov
theorem hsel5RRRL : ∀ i ∈ sel6RRRL props5RRRL, ∃ p ∈ props5RRRL,
    (childCore p.1 p.2 6 seed164Prov).id = i := axiomSelect_hsel MORRRL 6 seed164Prov props5RRRL
theorem hfresh5RRRL : ∀ p ∈ props5RRRL,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XRRRL5.archive := by decide
def XRRRL6 : TickCarrier Unit hQ :=
  advanceCarrier XRRRL5 hlaw5RRRL sel6RRRL 6 seed164Prov [] hsel5RRRL hfresh5RRRL
theorem hlaw6RRRL : Lawful XRRRL6 := by decide
def props6RRRL : List (Core × Bool) := proposals XRRRL6.archive XRRRL6.active
def sel7RRRL : List (Core × Bool) → List QuestionId := axiomSelect MORRRL 7 seed164Prov
theorem hsel6RRRL : ∀ i ∈ sel7RRRL props6RRRL, ∃ p ∈ props6RRRL,
    (childCore p.1 p.2 7 seed164Prov).id = i := axiomSelect_hsel MORRRL 7 seed164Prov props6RRRL
theorem hfresh6RRRL : ∀ p ∈ props6RRRL,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XRRRL6.archive := by decide
def XRRRL7 : TickCarrier Unit hQ :=
  advanceCarrier XRRRL6 hlaw6RRRL sel7RRRL 7 seed164Prov [] hsel6RRRL hfresh6RRRL

/-! ## Proposition 16.9(ii) — seven-tick closure of the seeds `LLLR`/`RRRL`

    Matches `LoneSeed.lean`'s `theorem_16_17_LL`/`_RR` pattern exactly: the
    full tick 1–7 support table, closing on the occurrence singleton at
    tick 7. -/

/-- **The support table for `𝒬_{LLLR}`**, ticks 1–7, exactly `lone_seed_beat.py`'s
    trace for the seed `LLLR`. Closes on the occurrence singleton
    `LLLRRRRRRRR`. -/
theorem prop_16_9_ii_LLLR :
    activeWords XLLLR1 =
      [[false, false, false, true, false], [false, false, false, true, true]] ∧
    activeWords XLLLR2 =
      [[false, false, false, true, false, false], [false, false, false, true, true, true]] ∧
    activeWords XLLLR3 = [[false, false, false, true, true, true, true]] ∧
    activeWords XLLLR4 =
      [[false, false, false, true, true, true, true, false],
       [false, false, false, true, true, true, true, true]] ∧
    activeWords XLLLR5 = [[false, false, false, true, true, true, true, true, true]] ∧
    activeWords XLLLR6 =
      [[false, false, false, true, true, true, true, true, true, false],
       [false, false, false, true, true, true, true, true, true, true]] ∧
    activeWords XLLLR7 =
      [[false, false, false, true, true, true, true, true, true, true, true]] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The side mirror**, decided independently rather than mirrored — the same
    discipline `theorem_16_17_RR` uses relative to `_LL`. -/
theorem prop_16_9_ii_RRRL :
    activeWords XRRRL1 =
      [[true, true, true, false, false], [true, true, true, false, true]] ∧
    activeWords XRRRL2 =
      [[true, true, true, false, false, false], [true, true, true, false, true, true]] ∧
    activeWords XRRRL3 = [[true, true, true, false, false, false, false]] ∧
    activeWords XRRRL4 =
      [[true, true, true, false, false, false, false, false],
       [true, true, true, false, false, false, false, true]] ∧
    activeWords XRRRL5 = [[true, true, true, false, false, false, false, false, false]] ∧
    activeWords XRRRL6 =
      [[true, true, true, false, false, false, false, false, false, false],
       [true, true, true, false, false, false, false, false, false, true]] ∧
    activeWords XRRRL7 =
      [[true, true, true, false, false, false, false, false, false, false, false]] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The closing address**: `λ_O` of `𝒬_{LLLR}`'s tick-7 singleton is
    exactly `9:28`, matching the book's displayed value for this instance. -/
theorem prop_16_9_ii_LLLR_addressed :
    addressedList (activeWords XLLLR7) = [(⟨9, 28, by decide⟩ : Pres)] := by decide

/-- **The mirror address**, `28:9`. -/
theorem prop_16_9_ii_RRRL_addressed :
    addressedList (activeWords XRRRL7) = [(⟨28, 9, by decide⟩ : Pres)] := by decide

#print axioms prop_16_9_ii_LLLR
#print axioms prop_16_9_ii_RRRL
#print axioms prop_16_9_ii_LLLR_addressed
#print axioms prop_16_9_ii_RRRL_addressed

end LoneSeed916
end Two
end RatioSpace
