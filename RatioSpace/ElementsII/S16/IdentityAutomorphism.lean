/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.Transient
import RatioSpace.ElementsII.S16.Automorphism
/-!
  Elements II Proposition 16.15 — on the two ensemble degeneracies of
  Proposition 16.13(3), the only tension-preserving permutation of the admitted
  family is the identity.

  `Two/Automorphism.lean`'s `coherence_invariant` already reindexes a coherence
  coherence value along a tension automorphism. This file isolates the permutation step as
  `tensions_invariant`, enumerates the two degenerate families `fam3` and `fam4`
  of `Two/Transient.lean` by their tension histograms, and reads off that a
  tension-preserving permutation fixes each member: the shared histogram of the
  one degenerate pair (`LR`, `LLR` in `fam3`) is still broken by a third
  occurrence's tension against the pair, so no genuine swap survives.
-/
set_option maxRecDepth 200000

namespace RatioSpace.Two.IdentityAutomorphism

open RatioSpace RatioSpace.Two RatioSpace.Two.Transient

/-- A choice-free canonical form for a list of tension values: the count of each
    value in `0, 1, ..., 19` (every tension in `fam3`/`fam4` is below this
    bound). Permutation-equal lists have equal count signatures, by
    `List.Perm.count_eq`, which stays within `propext`/`Quot.sound`. This is the
    sorted-list route the task calls for, taken through counts rather than
    `insertionSort` (whose Mathlib lemmas pull in `Classical.choice` in this
    toolchain) and without deciding `Perm` directly (whose `List.decidablePerm`
    instance likewise pulls in choice here). -/
def countSig (l : List ℕ) : List ℕ := (List.range 20).map (fun v => l.count v)

/-- Permutation-equal lists of naturals have equal count signatures. -/
theorem perm_countSig {l₁ l₂ : List ℕ} (hp : l₁.Perm l₂) : countSig l₁ = countSig l₂ := by
  unfold countSig
  apply List.map_congr_left
  intro v _
  exact hp.count_eq v

/-! ## Statement 8 — a tension automorphism permutes the tension list -/

/-- **Lemma 16.14's permutation step.** If `σ` permutes the family and preserves
    every tension on it, then the tension list of `σ y` is a permutation of the
    tension list of `y`. This is the `hperm.map` reindexing inside
    `coherence_invariant`, before `coherence` is applied. -/
theorem tensions_invariant (fam : List IPres) (σ : IPres → IPres)
    (hperm : (fam.map σ).Perm fam)
    (ht : ∀ y ∈ fam, ∀ z ∈ fam, tEnd (σ y) (σ z) = tEnd y z)
    {y : IPres} (hy : y ∈ fam) :
    (tensions fam (σ y)).Perm (tensions fam y) := by
  have hmap : ((fam.map σ).map (fun z => tEnd (σ y) z)).Perm
      (fam.map (fun z => tEnd (σ y) z)) := hperm.map _
  have hrewrite : (fam.map σ).map (fun z => tEnd (σ y) z) = tensions fam y := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro z hz
    simpa using ht y hy z hz
  rw [hrewrite] at hmap
  exact hmap.symm

/-! ## Statement 9 — the three distinguished members of `fam3` -/

/-- `LL`, the first member of `fam3`: the mediant `1{:}3`. -/
def LL : IPres := ⟨1, 3, by decide, by decide⟩
/-- `LR`, the second member of `fam3`: `2{:}3`. -/
def LR : IPres := ⟨2, 3, by decide, by decide⟩
/-- `LLR`, the fourth member of `fam3`: `2{:}5`, the occurrence that shares
    `LR`'s sorted tension histogram. -/
def LLR : IPres := ⟨2, 5, by decide, by decide⟩

/-- **Proposition 16.15, the `fam3` histogram classes.** Two members of `fam3`
    with permutation-equal tension lists are either equal, or the one degenerate
    pair `{LR, LLR}`. Decided on the count signatures (`countSig`), bridged from
    the `Perm` hypothesis by `perm_countSig`; report form: count signatures, not
    `Perm`-by-`decide` (which carries `Classical.choice` here). -/
theorem fam3_perm_classes : ∀ y ∈ fam3, ∀ y' ∈ fam3,
    (tensions fam3 y').Perm (tensions fam3 y) →
      y' = y ∨ (y = LR ∧ y' = LLR) ∨ (y = LLR ∧ y' = LR) := by
  intro y hy y' hy' hp
  have hsig : countSig (tensions fam3 y') = countSig (tensions fam3 y) :=
    perm_countSig hp
  revert hsig
  fin_cases hy <;> fin_cases hy' <;>
    (intro hsig; first
      | (left; rfl)
      | (right; left; exact ⟨rfl, rfl⟩)
      | (right; right; exact ⟨rfl, rfl⟩)
      | (exfalso; revert hsig; decide))

/-! ## Statement 10 — `fam4` has no histogram collision -/

/-- **Proposition 16.15, the `fam4` histogram classes.** In `fam4` the count
    signatures are pairwise distinct, so permutation-equal tension lists force
    equality. Same count-signature route as `fam3_perm_classes`. -/
theorem fam4_perm_classes : ∀ y ∈ fam4, ∀ y' ∈ fam4,
    (tensions fam4 y').Perm (tensions fam4 y) → y' = y := by
  intro y hy y' hy' hp
  have hsig : countSig (tensions fam4 y') = countSig (tensions fam4 y) :=
    perm_countSig hp
  revert hsig
  fin_cases hy <;> fin_cases hy' <;>
    (intro hsig; first | rfl | (exfalso; revert hsig; decide))

/-! ## Statement 11 — the only tension automorphism of `fam3` is the identity -/

/-- **Proposition 16.15 for `fam3`.** A permutation of `fam3` preserving every
    tension fixes every member. `σ` maps `fam3` into itself (`hperm.subset`); by
    `fam3_perm_classes` and `tensions_invariant`, `σ y` is either `y` or the
    partner of the one degenerate pair; a genuine swap of `LR` and `LLR` would
    make `tEnd LL (σ LR) = tEnd LL LR`, i.e. `tEnd LL LLR = tEnd LL LR`, and
    `decide` shows these are `5` and `1`, so no swap survives. -/
theorem fam3_aut_trivial (σ : IPres → IPres)
    (hperm : (fam3.map σ).Perm fam3)
    (ht : ∀ y ∈ fam3, ∀ z ∈ fam3, tEnd (σ y) (σ z) = tEnd y z) :
    ∀ y ∈ fam3, σ y = y := by
  -- `σ` sends every member of `fam3` back into `fam3`.
  have hmem : ∀ y ∈ fam3, σ y ∈ fam3 := fun y hy =>
    hperm.subset (List.mem_map_of_mem hy)
  -- `LL` is fixed: its tension class is a singleton.
  have hLL_mem : LL ∈ fam3 := by decide
  have hLR_mem : LR ∈ fam3 := by decide
  have hLLR_mem : LLR ∈ fam3 := by decide
  have hLL : σ LL = LL := by
    have hcl := fam3_perm_classes LL hLL_mem (σ LL) (hmem LL hLL_mem)
      (tensions_invariant fam3 σ hperm ht hLL_mem)
    rcases hcl with h | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
  intro y hy
  have hcl := fam3_perm_classes y hy (σ y) (hmem y hy)
    (tensions_invariant fam3 σ hperm ht hy)
  rcases hcl with h | ⟨hyLR, hσLLR⟩ | ⟨hyLLR, hσLR⟩
  · exact h
  · -- `y = LR`, `σ y = LLR`: contradicts preservation of `tEnd LL ·`.
    exfalso
    have hkey : tEnd (σ LL) (σ y) = tEnd LL y := ht LL hLL_mem y hy
    rw [hLL, hσLLR, hyLR] at hkey
    revert hkey; decide
  · -- `y = LLR`, `σ y = LR`: the mirror contradiction.
    exfalso
    have hkey : tEnd (σ LL) (σ y) = tEnd LL y := ht LL hLL_mem y hy
    rw [hLL, hσLR, hyLLR] at hkey
    revert hkey; decide

/-! ## Statement 12 — the only tension automorphism of `fam4` is the identity -/

/-- **Proposition 16.15 for `fam4`.** A permutation of `fam4` preserving every
    tension fixes every member, directly from `tensions_invariant` and
    `fam4_perm_classes` (no degenerate pair to rule out). -/
theorem fam4_aut_trivial (σ : IPres → IPres)
    (hperm : (fam4.map σ).Perm fam4)
    (ht : ∀ y ∈ fam4, ∀ z ∈ fam4, tEnd (σ y) (σ z) = tEnd y z) :
    ∀ y ∈ fam4, σ y = y := by
  intro y hy
  have hmem : σ y ∈ fam4 := hperm.subset (List.mem_map_of_mem hy)
  exact fam4_perm_classes y hy (σ y) hmem (tensions_invariant fam4 σ hperm ht hy)

#print axioms perm_countSig
#print axioms tensions_invariant
#print axioms fam3_perm_classes
#print axioms fam4_perm_classes
#print axioms fam3_aut_trivial
#print axioms fam4_aut_trivial

end RatioSpace.Two.IdentityAutomorphism
