/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S09.Question
/-!
  Gap G1-16 — Elements I §9, Definition 9.3, active question cavity:
  directional admission read off a family member.

  **Book statement.** "When forward reachability is required, one of the
  predicates is the directional-admission condition `Q_{O,r} ∈ ℳ₊`", with
  `Q_{O,r} = M_O⁻¹ M_r` and, by correction E1-34, `M_r = M_{F₀,r} G(w_r)`, the
  candidate's matrix read against its own declared initial frame.

  **What was missing.** `Pred` (`Question.lean`) is generic, and
  `forwardAdmissible` takes two `Observer`s, not a member of the active family.
  The D-16 note on `encounter` named the bridge, `History.accumulatedMatrix`,
  and said no predicate this concrete existed.

  **Added.**
  * `g116_encounter`: `Q_{O,r} = M_O⁻¹ M_r` for `r : History`, with `M_r` the
    rooted `accumulatedMatrix` (E1-34), not the unrooted `History.matrix`.
  * `g116_forwardPred : Pred`: the directional-admission predicate, a `Bool`
    decided by `dec`. `g116_forwardPred_iff`: it is `true` exactly when
    `Q_{O,r} ∈ ℳ₊`, in the shape of `forwardAdmissible_iff`.
  * `g116_forwardPred_observer`: on a member that is an observer's own history
    it is Definition 7.5's `forwardAdmissible`, by definition.
  * `g116_removes_a_member`: a question in which the predicate removes a
    member of the active family that the cavity alone keeps. Receiver: `L`
    from the root. Family: `LR` and `R`, both from the root, both in the depth-2
    cavity. `LR` is reached from the receiver by `R` and survives; `R` is not
    reached and is removed.
  * `g116_start_matters`: two members with the same (empty) word and different
    declared starts get different answers, so the predicate reads the start
    (D-16); the unrooted `History.matrix` would give both the same.
-/
namespace RatioSpace

open Mat2 Word Frame Pres

namespace Gaps.G1_16

/-- **Definition 9.3.** `Q_{O,r} = M_O⁻¹ M_r` for a member `r` of the active
    family, `M_r` read against `r`'s declared initial frame (E1-34, D-16). -/
def g116_encounter (O : Observer) (r : History) : Mat2 :=
  inv2 O.matrix * r.accumulatedMatrix

/-- **Definition 9.3.** The directional-admission predicate `Q_{O,r} ∈ ℳ₊`, as
    one of the exact predicates `γ_j(r; O_τ, 𝒜_τ)`. It ignores the family. -/
def g116_forwardPred : Pred :=
  fun r O _ => (dec (g116_encounter O r)).isSome

theorem g116_forwardPred_iff (r : History) (O : Observer) (A : ActiveFamily) :
    g116_forwardPred r O A = true ↔ g116_encounter O r ∈ Mplus :=
  (mem_Mplus_iff_dec _).symm

/-- On an observer's own history the predicate is Definition 7.5's forward
    admission: `accumulatedMatrix` of `P.history` is `P.matrix`. -/
theorem g116_forwardPred_observer (O P : Observer) (A : ActiveFamily) :
    g116_forwardPred P.history O A = forwardAdmissible O P := rfl

/-- The receiver: the word `L` from the canonical frame. -/
def g116_receiver : Observer := ⟨Frame.empty, [false], 1⟩

/-- A question at depth 2 from the canonical frame whose only predicate is
    directional admission. The family: `LR` and `R`, both from the root. -/
def g116_question : Question where
  receiver := g116_receiver
  frame := Frame.empty
  depth := 2
  active := [⟨Frame.empty, [false, true]⟩, ⟨Frame.empty, [true]⟩]
  preds := [g116_forwardPred]

/-- **The predicate removes a member.** Without it both members survive `S₀`
    (both lie in the cavity). With it, `LR` survives (`Q = G(R)`) and `R` is
    removed: `Q_{O,R} = G(L)⁻¹ G(R)` is not positive. -/
theorem g116_removes_a_member :
    S0 { g116_question with preds := [] } =
      [⟨Frame.empty, [false, true]⟩, ⟨Frame.empty, [true]⟩] ∧
    S0 g116_question = [⟨Frame.empty, [false, true]⟩] ∧
    g116_encounter g116_receiver ⟨Frame.empty, [false, true]⟩ = G [true] ∧
    g116_encounter g116_receiver ⟨Frame.empty, [true]⟩ ∉ Mplus := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rw [mem_Mplus_iff_dec]
  decide

/-- **The start is read.** Same empty word, different declared starts, one
    receiver `L`. The member starting at `L·∅` sits at the receiver's own frame,
    `Q = 1`, admitted. The member starting at `R·∅` gives `Q = [[1,1],[-1,0]]`,
    which has a negative entry, not admitted. Their unrooted
    `History.matrix` values are equal (`G []`), so a predicate on
    `History.matrix` could not tell them apart. -/
theorem g116_start_matters :
    g116_forwardPred ⟨Frame.stepL Frame.empty, []⟩ g116_receiver [] = true ∧
    g116_forwardPred ⟨Frame.stepR Frame.empty, []⟩ g116_receiver [] = false ∧
    (⟨Frame.stepL Frame.empty, []⟩ : History).matrix =
      (⟨Frame.stepR Frame.empty, []⟩ : History).matrix := by
  refine ⟨by decide, by decide, rfl⟩

end Gaps.G1_16

end RatioSpace
