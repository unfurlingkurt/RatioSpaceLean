/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.PrecaptureTie
/-!
  Elements II §16, Proposition 16.13 (restated): one witness for each branch of
  the tie pattern, on the real addresses of the words.

  Words read `false = L`, `true = R`, as `Walk.r`. Each block proves the four
  addresses are the children of the named pair, the four depths, and the
  pattern, and so (by `prop_16_13_tie`) the equal scores.

  1. `{LRL, LLLLR}`: `a = LLLLRL`, `b = LLLLRR`, `c = LRLL`, `d = LRLR`,
     depths `13, 13` against `13, 13` (sibling depths equal).
  2. `{LRL, RRRRLL}`: `a = LRLR`, `b = LRLL`, `c = RRRRLLL`, `d = RRRRLLR`,
     depths `13, 31` against `13, 31` (sibling depths `13` and `31` differ).
  3. `{LLR, L⁸}`: `a = L⁹`, `b = L⁸R`, `c = LLRL`, `d = LLRR`,
     depths `8, 8` against `10, 7` (the golden collision, `P = 8`).
-/

namespace RatioSpace
namespace Two
namespace Tie1613

open Frame

/-! ## Witness 1 — sibling depths equal -/

def w1a : IPres := ⟨3, 14, by decide, by decide⟩
def w1b : IPres := ⟨3, 13, by decide, by decide⟩
def w1c : IPres := ⟨4, 7, by decide, by decide⟩
def w1d : IPres := ⟨5, 8, by decide, by decide⟩

theorem w1_addr :
    (r [false, false, false, false, true, false]).p = w1a.p ∧
    (r [false, false, false, false, true, false]).q = w1a.q ∧
    (r [false, false, false, false, true, true]).p = w1b.p ∧
    (r [false, false, false, false, true, true]).q = w1b.q ∧
    (r [false, true, false, false]).p = w1c.p ∧
    (r [false, true, false, false]).q = w1c.q ∧
    (r [false, true, false, true]).p = w1d.p ∧
    (r [false, true, false, true]).q = w1d.q := by decide

theorem w1_depths :
    tEnd w1a w1b = 13 ∧ tEnd w1a w1d = 13 ∧ tEnd w1c w1b = 13 ∧ tEnd w1c w1d = 13 := by
  decide

theorem w1_tie : coherenceOf [w1a, w1b, w1c, w1d] w1a = coherenceOf [w1a, w1b, w1c, w1d] w1c := by
  rw [prop_16_13_tie]
  obtain ⟨h1, h2, h3, h4⟩ := w1_depths
  rw [h1, h2, h3, h4]
  exact Or.inl ⟨rfl, rfl⟩

/-! ## Witness 2 — the winners see the two siblings alike -/

def w2a : IPres := ⟨5, 8, by decide, by decide⟩
def w2b : IPres := ⟨4, 7, by decide, by decide⟩
def w2c : IPres := ⟨17, 4, by decide, by decide⟩
def w2d : IPres := ⟨22, 5, by decide, by decide⟩

theorem w2_addr :
    (r [false, true, false, true]).p = w2a.p ∧
    (r [false, true, false, true]).q = w2a.q ∧
    (r [false, true, false, false]).p = w2b.p ∧
    (r [false, true, false, false]).q = w2b.q ∧
    (r [true, true, true, true, false, false, false]).p = w2c.p ∧
    (r [true, true, true, true, false, false, false]).q = w2c.q ∧
    (r [true, true, true, true, false, false, true]).p = w2d.p ∧
    (r [true, true, true, true, false, false, true]).q = w2d.q := by decide

theorem w2_depths :
    tEnd w2a w2b = 13 ∧ tEnd w2a w2d = 31 ∧ tEnd w2c w2b = 13 ∧ tEnd w2c w2d = 31 := by
  decide

theorem w2_sibling_depths_differ : tEnd w2a w2b ≠ tEnd w2c w2d := by
  obtain ⟨h1, -, -, h4⟩ := w2_depths
  rw [h1, h4]; decide

theorem w2_tie : coherenceOf [w2a, w2b, w2c, w2d] w2a = coherenceOf [w2a, w2b, w2c, w2d] w2c := by
  rw [prop_16_13_tie]
  obtain ⟨h1, h2, h3, h4⟩ := w2_depths
  rw [h1, h2, h3, h4]
  exact Or.inl ⟨rfl, rfl⟩

/-! ## Witness 3 — the golden collision `{8, 8}` against `{7, 10}` -/

def w3a : IPres := ⟨1, 10, by decide, by decide⟩
def w3b : IPres := ⟨2, 17, by decide, by decide⟩
def w3c : IPres := ⟨3, 8, by decide, by decide⟩
def w3d : IPres := ⟨3, 7, by decide, by decide⟩

theorem w3_addr :
    (r (List.replicate 9 false)).p = w3a.p ∧
    (r (List.replicate 9 false)).q = w3a.q ∧
    (r (List.replicate 8 false ++ [true])).p = w3b.p ∧
    (r (List.replicate 8 false ++ [true])).q = w3b.q ∧
    (r [false, false, true, false]).p = w3c.p ∧
    (r [false, false, true, false]).q = w3c.q ∧
    (r [false, false, true, true]).p = w3d.p ∧
    (r [false, false, true, true]).q = w3d.q := by decide

theorem w3_depths :
    tEnd w3a w3b = 8 ∧ tEnd w3a w3d = 8 ∧ tEnd w3c w3b = 10 ∧ tEnd w3c w3d = 7 := by
  decide

theorem w3_tie : coherenceOf [w3a, w3b, w3c, w3d] w3a = coherenceOf [w3a, w3b, w3c, w3d] w3c := by
  rw [prop_16_13_tie]
  obtain ⟨h1, h2, h3, h4⟩ := w3_depths
  rw [h1, h2, h3, h4]
  exact Or.inr (Or.inr ⟨8, by decide, by decide, by decide, by decide, by decide⟩)

#print axioms w1_addr
#print axioms w1_tie
#print axioms w2_addr
#print axioms w2_sibling_depths_differ
#print axioms w2_tie
#print axioms w3_addr
#print axioms w3_tie

end Tie1613
end Two
end RatioSpace
