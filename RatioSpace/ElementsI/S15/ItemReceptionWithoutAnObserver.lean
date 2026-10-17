/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S15.Sufficiency
/-!
  Elements I §15, Definition 15.1 item 4, reception without an
  observer.

  **Book statement.** "RatioSpace is generatively sufficient for a target
  domain `𝒟` when the following have been constructed: … 4. observer-relative
  reception maps reproducing the target's accessible quantities; and 5. a
  proof that the relevant target equations or outcomes are recovered under
  the declared projection."

  **Reception reads an encounter.** A single map `SubstrateState → D.Reading`
  has no observer, and `closureOfState`, Definition 12.1's first arrow, is not
  a reception in Definition 11.1's sense (a reception reads an encounter record
  `𝖤_{O,P}`).

  **In `Sufficiency.lean`.** Item 4 is a declared, non-empty list of
  observers and an observer-indexed reception family (`ObsReception`);
  the encoded state enters each encounter as a presented state
  (`presentedState`, Definition 7.2). Item 5 holds at every declared observer.
  The one-map form is `GenerativelySufficientOnState`, and each declared observer
  gives one (`GenerativelySufficient.toOnState`). The word witness reads the
  presented closure `κ_P` of the encounter (`wordByClosureSufficientAt`; the
  word domain proper reads the word, `wordSufficientAt`).

  **Added here.** Item 4 is observer-relative in fact, not only in type. The
  target is `L`/`R` words read as their accumulated matrix `G(w)`. The
  reception reads the relative matrix `Q_{O,P} = M_O⁻¹ M_P` and nothing else.
  * `g126_sufficient_at_root`: with the observer at the root declared, all five
    items hold.
  * `g126_fails_at_R`: the same reception at an observer one `R` step away
    does not recover the target: at the empty word it reads `R⁻¹`, not `I`.
    So no sufficiency term can declare that observer with this reception and
    this encoding.
  * `g126_toOnState_root`: at the root the one-map form is recovered, and
    its map is `G` of the retained word.
-/

namespace RatioSpace

namespace Gaps.G1_26

open Layer

/-- Words read as their accumulated matrix. -/
def matrixDomain : Domain where
  History := Word
  Transition := Bool
  Reading := Mat2
  Quantity := Mat2
  step := fun b w => w ++ [b]
  same := fun u v => u = v
  same_equiv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  project := id
  observe := Word.G

/-- The reception that declares the relative matrix and reads nothing else,
    the same at every capacity. -/
def relativeFamily : ObsReception (fun _ => Mat2) :=
  ObsReception.const
    { mask := Mask.onlyRelative
      read := EncounterRecord.relative
      honest := fun _ _ h => h.2.2.1 rfl }

/-- An observer at the root, and one a single `R` step away. -/
def atRoot : Observer := ⟨Frame.empty, [], 0⟩
def atR : Observer := ⟨Frame.empty, [true], 0⟩

theorem g126_observers_distinct : atRoot ≠ atR := by decide

/-- At the root, the relative matrix of the encoded word is `G(w)`. -/
theorem g126_root_reads_G (w : Word) :
    relativeFamily.receive atRoot (presentedState (wordEncode w)) = Word.G w := by
  change encounter atRoot ⟨Frame.empty, w, 0⟩ = Word.G w
  simp only [encounter, Observer.matrix, atRoot, Frame.toMat2_empty, Word.G_nil,
    Mat2.one_mul']
  have : Mat2.inv2 (1 : Mat2) = 1 := by decide
  rw [this, Mat2.one_mul']

/-- **All five items, with the observer at the root declared.** -/
def g126_sufficient_at_root : GenerativelySufficient matrixDomain where
  encode := wordEncode
  realize := fun t => ⟨wordRealize t, fun _ => rfl⟩
  identify :=
    ⟨fun S T => S = T, fun u v => by
      constructor
      · intro h; exact congrArg wordEncode h
      · intro h; exact congrArg SubstrateState.word h⟩
  equiv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  observers := [atRoot]
  nonempty := ⟨atRoot, List.mem_singleton_self _⟩
  reception := relativeFamily
  recovers := by
    intro O hO w
    rw [List.mem_singleton.mp hO]
    exact g126_root_reads_G w

/-- **The same reception at `R` does not recover the target.** At the empty
    word it reads `R⁻¹`, and the target says `I`. -/
theorem g126_R_misreads_empty :
    matrixDomain.project (relativeFamily.receive atR (presentedState (wordEncode [])))
      ≠ matrixDomain.observe [] := by
  change encounter atR ⟨Frame.empty, [], 0⟩ ≠ Word.G []
  decide

/-- **So recovery is a fact about the observer, not about the map alone**: no
    sufficiency term with this encoding and this reception can declare the
    observer at `R`. -/
theorem g126_fails_at_R (G : GenerativelySufficient matrixDomain)
    (he : G.encode = wordEncode) (hr : G.reception = relativeFamily) :
    atR ∉ G.observers := by
  intro hO
  have := G.recovers atR hO []
  rw [he, hr] at this
  exact g126_R_misreads_empty this

/-- At the root, the one-map form is recovered, and its map on encoded
    states is `G` of the retained word. -/
theorem g126_toOnState_root (w : Word) :
    (g126_sufficient_at_root.toOnState atRoot (List.mem_singleton_self _)).receive
      (wordEncode w) = Word.G w :=
  g126_root_reads_G w

end Gaps.G1_26

end RatioSpace
