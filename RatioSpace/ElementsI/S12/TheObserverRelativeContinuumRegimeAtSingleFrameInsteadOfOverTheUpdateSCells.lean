/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S12.Continuum
import RatioSpace.ElementsI.S12.TheCorrespondenceObligationOverATotalUpdate
/-!
  Gap G1-24 — Elements I §12, Definition 12.5, the observer-relative continuum
  regime at one frame instead of over the update's cells.

  **Book statement.** "A continuum regime is reached for observer `O` when
  `Res_O(F_n) = 0` for the distinct cells relevant to the update. [...] The
  substrate has not become continuous. Its exact cells have become unresolved
  by the chosen reception."

  **What was wrong.** `ContinuumRegime Res F` was the predicate at one frame,
  and its docstring said that matched the book. The quantifier over the
  update's cells, and which cells those are, were not stated.

  **Changed (`Continuum.lean`).** `ContinuumRegimeOn Res cells`: `Res` reads
  `false` on every cell of a declared list. `ContinuumRegime` is kept as the
  one-cell case (`continuumRegimeOn_singleton_iff`). Which cells are relevant is
  declared, not derived: `trajectoryCells U n S`, the cells of `n` steps of the
  partial update `U` (Def 12.3's type) from `S`, stopping at the first failure,
  and `UpdateContinuumRegime Res U n S` over them. `continuumRegimeOn_congr`:
  the regime depends only on which cells are listed, so "distinct" changes
  nothing. `continuumRegimeOn_nil`: an empty list is a regime for every
  receiver, and `trajectoryCells` is never empty.

  **Added here** (witnesses rebuilt 2026-09-29, audit E1-B10). The first
  version used `widthReceiver N`, resolving a cell when `q₋q₊ ≤ N`, with no
  reception behind it; no reception can be behind it
  (`no_boundary_reading_realizes_width_one`, `Continuum.lean`), so it is
  removed, with `g124_L_ray_regime`. The receiver is now
  `capacityResolution (capObserver N)`: a boundary is received when its
  denominator is at most the observer's capacity `η_O = N`.
  * `g124_L_ray_recip`: the cell `L^k` from `F_∅` has `q₋q₊ = k`;
    `g124_L_ray_distinct`: those cells are distinct frames with distinct
    boundaries. Kept from the first version as substrate facts; they are no
    longer regime witnesses (at `η_O ≥ 1` every `L^k` is resolved through
    `0:1`).
  * `g124_quantifier_bites`: at capacity `1`, one `L` step from `LR` lands in
    `LRL`, which is unresolved, so the one-frame predicate holds there, and the
    regime over the update still fails, on the start cell.
  * `g124_regime_persists`: for every `N` and every side, once the start cell
    is unresolved the regime holds over every number of steps.
  * `g124_failing_update_regime`: at G1-23's empty question the update fails
    at every state, so for any number of steps the regime is the one-frame
    predicate at the state's own cell.
-/

namespace RatioSpace

namespace Gaps.G1_24

open Layer Gaps.G1_18

/-- One side selection as an update: append `b` to the retained word. Defined
    at every state. -/
def stepUpdate (b : Bool) : SubstrateState → SubstrateState ⊕ Outcome :=
  fun S => .inl { S with word := S.word ++ [b] }

theorem stepUpdate_frame (b : Bool) (S : SubstrateState) :
    ({ S with word := S.word ++ [b] } : SubstrateState).frame = Frame.select S.frame b := by
  simp [SubstrateState.frame, Frame.walk, List.foldl_append]

/-- The state at `L^k` from `F_∅`. -/
def lState (k : ℕ) : SubstrateState := ⟨Frame.empty, List.replicate k false, [], []⟩

theorem g124_L_ray_q (k : ℕ) :
    (lState k).frame.plus.q = k ∧ (lState k).frame.minus.q = 1 := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have h : (lState (k + 1)).frame = Frame.stepL (lState k).frame := by
      simp [lState, SubstrateState.frame, Frame.walk, List.replicate_succ',
        List.foldl_append, Frame.select]
    rw [h]
    exact ⟨by simp [Frame.stepL, Frame.mid, Pres.mediant, ih.1, ih.2], ih.2⟩

/-- **The cell `L^k` has `q₋q₊ = k`.** -/
theorem g124_L_ray_recip (k : ℕ) : cellWidthRecip (lState k).frame = k := by
  simp [cellWidthRecip, (g124_L_ray_q k).1, (g124_L_ray_q k).2]

theorem stepUpdate_L_lState (k : ℕ) : stepUpdate false (lState k) = .inl (lState (k + 1)) := by
  simp [stepUpdate, lState, List.replicate_succ']

/-- An observer at the start frame with capacity `N`. -/
def capObserver (N : ℕ) : Observer := ⟨Frame.empty, [], N⟩

/-- The state at the walk `w` from `F_∅`. -/
def wState (w : Word) : SubstrateState := ⟨Frame.empty, w, [], []⟩

theorem stepUpdate_wState (b : Bool) (w : Word) :
    stepUpdate b (wState w) = .inl (wState (w ++ [b])) := rfl

/-- **The quantifier bites.** At capacity `1`, one `L` step from the cell `LR`
    (`1:1 | 1:2`, resolved through `1:1`) lands in `LRL` (`2:3 | 1:2`), which
    the observer does not resolve: the one-frame predicate holds at the new
    cell, and the regime over the update fails on the start cell. (Before audit
    E1-B10 this was stated for a width threshold `q₋q₊ ≤ N` with no reception
    behind it; `no_boundary_reading_realizes_width_one` shows no reception is
    behind it.) -/
theorem g124_quantifier_bites :
    ContinuumRegime (capacityResolution (capObserver 1)) (wState [false, true, false]).frame
    ∧ ¬ UpdateContinuumRegime (capacityResolution (capObserver 1)) (stepUpdate false) 1
        (wState [false, true]) := by
  refine ⟨by decide, fun h => ?_⟩
  have := h.start
  revert this
  decide

/-- **Once unresolved, the regime holds over every number of side
    selections.** For every capacity `N`, every side `b` and every state whose
    cell the observer does not resolve, every cell of `n` steps of appending
    `b` is unresolved (`capacityResolution_select`). -/
theorem g124_regime_persists (N : ℕ) (b : Bool) (S : SubstrateState)
    (hS : ContinuumRegime (capacityResolution (capObserver N)) S.frame) (n : ℕ) :
    UpdateContinuumRegime (capacityResolution (capObserver N)) (stepUpdate b) n S := by
  induction n generalizing S with
  | zero => exact (updateContinuumRegime_zero_iff _ _ _).mpr hS
  | succ n ih =>
    rw [updateContinuumRegime_succ_defined _ _ _
      (show stepUpdate b S = .inl { S with word := S.word ++ [b] } from rfl)]
    refine ⟨hS, ih _ ?_⟩
    rw [stepUpdate_frame]
    exact capacityResolution_select _ _ _ hS

/-- **The cells of the `L` ray are distinct.** Different depths have different
    `q₋q₊`, and in each cell the two boundaries are different presentations.
    (Until audit E1-B10 these were the cells of `widthReceiver`'s regime. Under
    `capacityResolution` with `η_O ≥ 1` every `L^k` is resolved, through its
    lower boundary `0:1`; the substrate-side fact stated here is unchanged.) -/
theorem g124_L_ray_distinct (k k' : ℕ) (h : k ≠ k') :
    (lState k).frame ≠ (lState k').frame
    ∧ (lState k).frame.plus ≠ (lState k).frame.minus := by
  refine ⟨fun he => h ?_, fun he => ?_⟩
  · rw [← g124_L_ray_recip k, ← g124_L_ray_recip k', he]
  · have := (lState k).frame.det_eq_one
    rw [Frame.det, Delta, he, mul_comm ((lState k).frame.minus.q : ℤ), sub_self] at this
    exact absurd this (by decide)

/-- **A failing update.** At G1-23's empty question the update fails at every
    state, so only the start cell is relevant, for any number of steps. -/
theorem g124_failing_update_regime {O : Observer} (Res : CellResolution O) (B : Assimilation)
    (n : ℕ)
    (S : SubstrateState) :
    UpdateContinuumRegime Res (Gaps.G1_23.update g118_idCryst B Gaps.G1_23.emptyQuestion) n S
      ↔ ContinuumRegime Res S.frame := by
  cases n with
  | zero => exact updateContinuumRegime_zero_iff _ _ _
  | succ n =>
    exact updateContinuumRegime_succ_undefined _ _ _
      (Gaps.G1_23.g123_empty_question_undefined B S)

end Gaps.G1_24

end RatioSpace
