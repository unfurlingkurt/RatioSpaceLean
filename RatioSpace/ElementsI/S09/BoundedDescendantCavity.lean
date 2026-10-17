/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S06.State
/-!
  Elements I §9, Definition 9.2, bounded descendant cavity.

  **Book statement.** `𝒞(F,N) = {r_F(w) : |w| ≤ N}`, and it is finite.
  Distinct words address distinct relations (Standard Result 3.1), so the
  count is exact: `|𝒞(F,N)| + 1 = 2^(N+1)`.

  **The count as the size of a set.** `cavity_card_le` (`Question.lean`) counts
  the entries of the list `cavity F N`, one per word. The book's `|𝒞(F,N)|` is
  the size of a set, so the count is the book's only once no relation is listed
  twice.

  **Proved here.**
  * `g115_allWords_nodup`, `g115_wordsUpTo_nodup`: no word is listed twice.
  * `g115_cavity_nodup`: no relation is listed twice. Two words of the cavity
    with the same addressed relation are the same word (`Frame.addressed_inj`,
    Standard Result 3.1's uniqueness half, every frame).
  * `g115_cavitySet`, `g115_mem_cavitySet`, `g115_cavitySet_card`: the cavity
    as a finite set, with the set count `|𝒞(F,N)| + 1 = 2^(N+1)`, written
    additively because ℕ subtraction truncates. The set is built with
    `Finset.mk` from the no-repeat proof: Mathlib's `List.toFinset` carries
    `Classical.choice` in its own definition, so the form
    `(cavity F N).toFinset.card` does not meet the tree's standard.

    Membership is read on the underlying multiset for the same reason
    (`Finset` membership goes through `SetLike`).
  * `g115_mem_cavity_unique`: every member of the cavity has exactly one word of
    length at most `N` addressing it.
-/
namespace RatioSpace

open Word Frame Pres

namespace Gaps.G1_15

/-- Appending one letter is injective in the prefix and in the letter. -/
private theorem append_letter_inj {u v : Word} {a b : Bool}
    (h : u ++ [a] = v ++ [b]) : u = v ∧ a = b := by
  have h' := List.append_inj' h rfl
  refine ⟨h'.1, ?_⟩
  have := h'.2
  injection this

/-- The two children of a word. -/
private def kids (w : Word) : List Word := [w ++ [false], w ++ [true]]

private theorem mem_kids {w x : Word} : x ∈ kids w ↔ x = w ++ [false] ∨ x = w ++ [true] := by
  simp only [kids, List.mem_cons, List.not_mem_nil, or_false]

private theorem mem_flatMap_kids {l : List Word} {x : Word} :
    x ∈ l.flatMap kids ↔ ∃ w ∈ l, x ∈ kids w := List.mem_flatMap

/-- Children of a duplicate-free list of words are duplicate-free. -/
private theorem nodup_flatMap_kids : ∀ l : List Word, l.Nodup → (l.flatMap kids).Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
      have ha : a ∉ t := (List.nodup_cons.mp h).1
      have ht := nodup_flatMap_kids t (List.nodup_cons.mp h).2
      rw [List.flatMap_cons]
      change ((a ++ [false]) :: (a ++ [true]) :: t.flatMap kids).Nodup
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, ht⟩⟩
      · intro hm
        rcases List.mem_cons.mp hm with he | hm
        · exact absurd (append_letter_inj he).2 (by decide)
        · obtain ⟨w, hw, hx⟩ := mem_flatMap_kids.mp hm
          rcases mem_kids.mp hx with he | he <;>
            exact ha ((append_letter_inj he).1 ▸ hw)
      · intro hm
        obtain ⟨w, hw, hx⟩ := mem_flatMap_kids.mp hm
        rcases mem_kids.mp hx with he | he <;>
          exact ha ((append_letter_inj he).1 ▸ hw)

/-- **No word of length `n` is listed twice.** -/
theorem g115_allWords_nodup : ∀ n : ℕ, (allWords n).Nodup := by
  intro n
  induction n with
  | zero => exact List.nodup_singleton _
  | succ n ih => exact nodup_flatMap_kids (allWords n) ih

/-- **No word of length at most `N` is listed twice.** Words from different
    lengths differ by length. -/
theorem g115_wordsUpTo_nodup : ∀ N : ℕ, (wordsUpTo N).Nodup := by
  intro N
  induction N with
  | zero => exact g115_allWords_nodup 0
  | succ N ih =>
      have hsplit : wordsUpTo (N + 1) = wordsUpTo N ++ allWords (N + 1) := by
        simp only [wordsUpTo, List.range_succ, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [hsplit]
      refine List.nodup_append.mpr ⟨ih, g115_allWords_nodup (N + 1), ?_⟩
      intro u hu v hv huv
      subst huv
      have h1 := mem_wordsUpTo.mp hu
      have h2 := allWords_length (N + 1) u hv
      omega

/-- **No relation of the cavity is listed twice.** Two words with the same
    addressed relation are the same word (`Frame.addressed_inj`). -/
theorem g115_cavity_nodup (F : Frame) (N : ℕ) : (cavity F N).Nodup :=
  List.Nodup.map (fun _ _ h => Frame.addressed_inj F h) (g115_wordsUpTo_nodup N)

/-- **Definition 9.2 as a set.** The cavity with its repeat-freeness is a finite
    set. Built directly with `Finset.mk` because Mathlib's `List.toFinset` reaches
    `Classical.choice` in its own definition (through `List.nodup_dedup`). -/
def g115_cavitySet (F : Frame) (N : ℕ) : Finset Pres :=
  ⟨(cavity F N : Multiset Pres), g115_cavity_nodup F N⟩

/-- Membership, read on the set's underlying multiset. Mathlib's `r ∈ s` for a
    `Finset` goes through `SetLike` (`Finset.instSetLike`), which reaches
    `Classical.choice`; the multiset reading is the same membership without it. -/
theorem g115_mem_cavitySet {F : Frame} {N : ℕ} {r : Pres} :
    r ∈ (g115_cavitySet F N).val ↔ ∃ w : Word, w.length ≤ N ∧ Frame.addressed F w = r :=
  mem_cavity

/-- **Definition 9.2, the book's count, as the size of a set.**
    `|𝒞(F,N)| + 1 = 2^(N+1)`. -/
theorem g115_cavitySet_card (F : Frame) (N : ℕ) :
    (g115_cavitySet F N).card + 1 = 2 ^ (N + 1) :=
  cavity_card_le F N

/-- At `N = 3` the set has fifteen relations, the fifteen `Question.lean`'s
    depth-3 evaluation lists in tree order. -/
example : (g115_cavitySet Frame.empty 3).card = 15 := by
  have := g115_cavitySet_card Frame.empty 3
  omega

/-- Every member of the cavity has exactly one word of length at most `N`
    addressing it. -/
theorem g115_mem_cavity_unique {F : Frame} {N : ℕ} {r : Pres} (hr : r ∈ cavity F N) :
    ∃ w : Word, (w.length ≤ N ∧ Frame.addressed F w = r) ∧
      ∀ v : Word, v.length ≤ N ∧ Frame.addressed F v = r → v = w := by
  obtain ⟨w, hw, hwr⟩ := mem_cavity.mp hr
  exact ⟨w, ⟨hw, hwr⟩, fun v hv => Frame.addressed_inj F (hv.2.trans hwr.symm)⟩

end Gaps.G1_15

end RatioSpace
