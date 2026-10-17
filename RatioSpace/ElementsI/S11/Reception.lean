/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S11.Perspective
/-!
  Elements I §11, Definition 11.1, reception, with the observer as index.

  **Book statement.** "A reception map is an observer-conditioned exact map
  `𝓡_O : 𝖤_{O,P} → Y_O` from the complete encounter record to a receiving
  space `Y_O`." The input contains `O` through `Q_{O,P}` and the
  retained records `w_O, κ_O, H_O`; "a reception that also depends on the
  observer's declared capacity `η_O` (Definition 7.1), a datum of the observer
  outside `𝖤_{O,P}`, depends on it through the index `O` of `𝓡_O`."
  Reading A: the reception reads the record only. Reading B: it also reads
  `η_O`, through the index.

  **The bare reception.** `Reception Y` (`Perspective.lean`) has no observer
  parameter and one receiving space, and `honest` confines `read` to the seven
  fields of `EncounterRecord`. `EncounterRecord.of O P` does not contain
  `O.eta`. So no bare `Reception` can depend on the observer's declared
  capacity: it realizes reading A, not reading B.

  **The indexed reception.** `ObsReception Y` (`Perspective.lean`): a family
  `(eta : ℕ) → Reception (Y eta)` indexed by the capacity alone, and
  `ObsReception.receive R O P = (R.at_ O.eta).read (EncounterRecord.of O P)`
  into `Y_O = Y O.eta`. What the record holds about `O` (`w_O`, `κ_O`,
  `Q_{O,P}`, and `H_O` only as the word, the declaration `H_O = (w_O)` of
  Elements I, Definition 7.4) is read there, so `η_O`
  is the only thing that passes through the index, which is reading
  B; indexing by the whole observer would let a blank-mask member read `w_O`
  through the index. `ObsReception.receive_honest` is the declaration
  obligation for the composite. `Reception` is the member at one
  capacity. The Lean states both readings.

  **Proved here.**
  * `g120_record_omits_capacity`: two observers that differ only in `eta`
    produce the same encounter record with any presented state.
  * `g120_plain_reception_blind_to_capacity`: hence every bare `Reception`
    reads them the same. This is the limit of the bare form, as a theorem.
  * `g120_reading_A_blind_to_capacity`: the same for a constant family
    (a constant family is reading A; the converse is not claimed).
  * `truncatedReception`, `g120_indexed_reception_sees_capacity`: an honest
    family (each member reads only the presented word) whose output differs for
    two observers that differ only in `eta`. Reading B is expressible.
  * `g120_family_reads_only_record_and_capacity`: the blank-mask case of
    `ObsReception.receive_honest`; a family whose member declares nothing gives
    two observers with one capacity the same output, from any presented
    states. Nothing leaks through the index but the capacity.
-/
namespace RatioSpace

namespace Gaps.G1_20

/-- Two observers with the same start and word and different capacities. -/
def lowCap : Observer := ⟨Frame.empty, [true], 0⟩
def highCap : Observer := ⟨Frame.empty, [true], 2⟩

/-- A presented state with a two-letter word. -/
def presented : Observer := ⟨Frame.empty, [true, false], 0⟩

/-- The record does not contain the capacity: observers that differ only in
    `eta` give the same record with every presented state. -/
theorem g120_record_omits_capacity (O O' P : Observer)
    (hs : O.start = O'.start) (hw : O.word = O'.word) :
    EncounterRecord.of O P = EncounterRecord.of O' P := by
  obtain ⟨s, w, e⟩ := O
  obtain ⟨s', w', e'⟩ := O'
  simp only at hs hw
  subst hs hw
  rfl

/-- **The bare form is blind.** A bare reception cannot see the capacity. -/
theorem g120_plain_reception_blind_to_capacity {Y : Type} (R : Reception Y)
    (O O' P : Observer) (hs : O.start = O'.start) (hw : O.word = O'.word) :
    R.read (EncounterRecord.of O P) = R.read (EncounterRecord.of O' P) := by
  rw [g120_record_omits_capacity O O' P hs hw]

/-- Reading A, as a family, is blind to the capacity for the same reason. -/
theorem g120_reading_A_blind_to_capacity {Y : Type} (R : Reception Y)
    (O O' P : Observer) (hs : O.start = O'.start) (hw : O.word = O'.word) :
    (ObsReception.const R).receive O P = (ObsReception.const R).receive O' P :=
  g120_plain_reception_blind_to_capacity R O O' P hs hw

/-- At capacity `η`, read the presented word up to `η` letters. Each
    member declares the presented word and reads nothing else. A witness that
    capacity dependence is expressible, not a claim about what the book's
    capacity does. -/
def truncatedReception : ObsReception (fun _ => Word) where
  at_ eta :=
    { mask := Mask.onlyPresentedWord
      read := fun E => E.presentedWord.take eta
      honest := by intro E F h; simp only [h.2.1 rfl] }

/-- **Reading B is expressible.** An honest observer-indexed reception tells
    apart two observers that differ only in capacity, with one presented
    state. -/
theorem g120_indexed_reception_sees_capacity :
    lowCap.start = highCap.start ∧ lowCap.word = highCap.word ∧
    truncatedReception.receive lowCap presented ≠
      truncatedReception.receive highCap presented := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- **No leak through the index.** With the blank mask, an observer-indexed
    reception depends on nothing but the capacity: two observers with one
    capacity receive the same from any two presented states. -/
theorem g120_family_reads_only_record_and_capacity {Y : ℕ → Type}
    (R : ObsReception Y) (O O' P P' : Observer) (he : O.eta = O'.eta)
    (hb : (R.at_ O.eta).mask = Mask.blank) :
    he ▸ R.receive O P = R.receive O' P' := by
  refine R.receive_honest O O' P P' he ?_
  rw [hb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hc <;> exact absurd hc (by decide)

end Gaps.G1_20

end RatioSpace
