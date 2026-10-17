/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.WordDynamics
import RatioSpace.ElementsII.S16.Capture
/-!
  Elements II §16, Theorem 16.12, item 3 — in the book's own form, on words.

  *"If `S_j` is invariant under side exchange, so is every later support, and
  no later support is an occurrence singleton."*

  `Capture.theorem_16_12_item3` proves this over a general `Policy`, with two
  hypotheses the book does not state: the archive is mirror-invariant at tick
  `j`, and the policy is `PolicySideRobust`. The route to the book's form is a
  mirror-equivariance lemma for `wordStep`, built here. At observer `ε` a run's active words after
  tick `j` are `wIter` of its words at `j` (`act_words_shift`), and `wordStep`
  commutes with the exchange up to storage order, because the exchange inverts
  every `ε`-address (`rI_mirror`) and the coherence value is invariant under a complete
  side exchange (`coherenceOf_side_invariant`, from Theorem 7.8's tension
  invariance). Neither the
  archive nor a policy hypothesis enters: on a rooted run at `ε` the words at
  `j + i` are `wIter i` of the words at `j` (`act_words_shift`), a statement with
  no archive in it.

  Every theorem `propext`/`Quot.sound` or less.
-/

namespace RatioSpace
namespace Two
namespace CaptureWords

open Mat2 Word Frame Pres RatioSpace Advance Accumulation RootOrbit Beat Beat11Bridge
  RootChainCarrier Step5Beat Step5Induction Step5Words SideExchange

/-! ## The exchange inverts every `ε`-address -/

/-- The empty frame is fixed by the exchange. -/
theorem empty_mirror : Frame.mirror Frame.empty = Frame.empty := rfl

/-- `r(w̄) = r(w)⁻¹`. -/
theorem r_mirror (w : Word) : r (mirrorWord w) = recip (r w) := by
  have h := addressed_mirror Frame.empty w
  rw [empty_mirror] at h
  exact h

/-- The `ε`-address of a mirrored word is the inverse presentation. -/
theorem rI_mirror (w : Word) : rI (mirrorWord w) = Inv (rI w) := by
  have h := r_mirror w
  have hp : (r (mirrorWord w)).p = (r w).q := by rw [h]; rfl
  have hq : (r (mirrorWord w)).q = (r w).p := by rw [h]; rfl
  unfold rI Inv IPres.inv
  simp only [hp, hq]

/-! ## One tick on words commutes with the exchange -/

/-- The exchange swaps each sibling pair, so the children of mirrored words are
    the mirrored children, up to storage order. -/
theorem childWords_mirror : ∀ ws : List Word,
    (childWords (ws.map mirrorWord)).Perm ((childWords ws).map mirrorWord)
  | [] => List.Perm.refl _
  | w :: ws => by
    have ih := childWords_mirror ws
    simp only [childWords, List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
    simp only [mirrorWord_append, mirrorWord_singleton, Bool.not_false, Bool.not_true,
      List.cons_append, List.nil_append, List.map_nil]
    exact ((ih.cons _).cons _).trans (List.Perm.swap _ _ _)

/-- Children respect storage order. -/
theorem childWords_perm {ws ws' : List Word} (h : ws.Perm ws') :
    (childWords ws).Perm (childWords ws') := by
  unfold childWords
  exact h.flatMap_right _

/-- The filter reads its family only up to storage order. -/
theorem keepW_perm {ws ws' : List Word} (h : ws.Perm ws') (w : Word) :
    keepW ws w = keepW ws' w := by
  have hL : ((childWords ws).map rI).Perm ((childWords ws').map rI) :=
    (childWords_perm h).map _
  unfold keepW
  simp only [List.all_eq_true, hL.mem_iff, coherenceOf_perm hL]

/-- The filter is invariant under the complete exchange
    (`coherenceOf_side_invariant`). -/
theorem keepW_mirror (ws : List Word) (w : Word) :
    keepW (ws.map mirrorWord) (mirrorWord w) = keepW ws w := by
  have hL : ((childWords (ws.map mirrorWord)).map rI).Perm (((childWords ws).map rI).map Inv) := by
    have := (childWords_mirror ws).map rI
    simpa [List.map_map, Function.comp_def, rI_mirror] using this
  unfold keepW
  simp only [decide_eq_decide, List.all_eq_true, hL.mem_iff, coherenceOf_perm hL, rI_mirror,
    coherenceOf_side_invariant]
  constructor
  · intro H z hz
    have := H (Inv z) (List.mem_map_of_mem hz)
    rwa [coherenceOf_side_invariant] at this
  · intro H z hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    rw [coherenceOf_side_invariant]
    exact H z' hz'

/-- `wordStep` respects storage order. -/
theorem wordStep_perm {ws ws' : List Word} (h : ws.Perm ws') :
    (wordStep ws).Perm (wordStep ws') := by
  unfold wordStep
  have e : keepW ws = keepW ws' := funext (keepW_perm h)
  rw [e]
  exact (childWords_perm h).filter _

/-- **One tick on words commutes with the side exchange**, up to storage order. -/
theorem wordStep_mirror (ws : List Word) :
    (wordStep (ws.map mirrorWord)).Perm ((wordStep ws).map mirrorWord) := by
  unfold wordStep
  refine ((childWords_mirror ws).filter _).trans ?_
  rw [List.filter_map]
  have e : (keepW (ws.map mirrorWord) ∘ mirrorWord) = keepW ws :=
    funext (keepW_mirror ws)
  rw [e]

/-- Invariance under the exchange survives one tick. -/
theorem wordStep_invariant {ws : List Word} (h : (ws.map mirrorWord).Perm ws) :
    ((wordStep ws).map mirrorWord).Perm (wordStep ws) :=
  (wordStep_mirror ws).symm.trans (wordStep_perm h)

/-- Invariance under the exchange survives every number of ticks. -/
theorem wIter_invariant {ws : List Word} (h : (ws.map mirrorWord).Perm ws) :
    ∀ i, ((wIter i ws).map mirrorWord).Perm (wIter i ws)
  | 0 => h
  | i + 1 => wordStep_invariant (wIter_invariant h i)

/-- Every word a tick produces is a child, so it is nonempty. -/
theorem wordStep_ne_nil {ws : List Word} {w : Word} (hw : w ∈ wordStep ws) : w ≠ [] := by
  unfold wordStep childWords at hw
  obtain ⟨x, -, hx⟩ := List.mem_flatMap.mp (List.mem_filter.mp hw).1
  rcases List.mem_pair.mp hx with rfl | rfl <;> simp

/-- An exchange-invariant word list after at least one tick is never a singleton. -/
theorem wIter_succ_ne_one {ws : List Word} (h : (ws.map mirrorWord).Perm ws) (i : ℕ) :
    (wIter (i + 1) ws).length ≠ 1 :=
  no_singleton_fixed_setwise mirrorWord _
    (fun _ hw => Capture.mirrorWord_ne_self_of_ne_nil (wordStep_ne_nil hw))
    (wIter_invariant h (i + 1))

/-! ## Theorem 16.12, item 3, on a run -/

section run

variable {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ} {pv : ℕ → Provenance}

/-- **Theorem 16.12, item 3, in the book's form.** If the support's words at
    tick `j` are carried to themselves by the side exchange, up to storage
    order, so are the words at every later tick, and no later support is an
    occurrence singleton. The hypothesis is on words: the next tick's words are
    a function of the current words alone (`nextCores_words`,
    `act_words_shift`). NOT PROVED here: that `Capture`'s identifier-level
    invariance implies this word-level one. The conclusion's invariance is
    likewise on words; the no-singleton clause is on occurrences (`act`'s
    length). No archive hypothesis and no policy hypothesis: the run is
    `act`, Definition 8.1 at `ε`, and the stated hypotheses are
    those of items 1 and 2 (a rooted start, well-formed with distinct
    identifiers). -/
theorem theorem_16_12_item3
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0) (j : ℕ)
    (hj : (((act A0 S0 st pv j).map fullWord).map mirrorWord).Perm
      ((act A0 S0 st pv j).map fullWord)) (i : ℕ) :
    (((act A0 S0 st pv (j + i)).map fullWord).map mirrorWord).Perm
        ((act A0 S0 st pv (j + i)).map fullWord) ∧
      (act A0 S0 st pv (j + (i + 1))).length ≠ 1 := by
  refine ⟨?_, ?_⟩
  · rw [act_words_shift hnd0 hwf0 hroot j i]
    exact wIter_invariant hj i
  · have h := act_words_shift (st := st) (pv := pv) hnd0 hwf0 hroot j (i + 1)
    have hlen := congrArg List.length h
    rw [List.length_map] at hlen
    rw [hlen]
    exact wIter_succ_ne_one hj i

end run

end CaptureWords
end Two
end RatioSpace
