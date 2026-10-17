/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S15.Sufficiency
/-!
  Elements I §11, Definition 11.6, joint relational
  reconstruction: one record, not one per observer.

  **Book statement.** "Given observers `O_1, …, O_n`, define the joint
  perspective map `𝒥(P) = (𝒫_{O_1}(P), …, 𝒫_{O_n}(P))`. The family of
  perspectives is reconstructively sufficient on a class `𝒞` when
  `𝒥(P) = 𝒥(P') ⇒ P ≡_𝒞 P'`."

  **One encounter per observer.** The book's map takes one encounter per
  observer, `𝖤_{O_i,P}`, with one presented state `P`, and sufficiency is over
  presented states. A map of every perspective over one `EncounterRecord` is
  the book's map only when the observers coincide.

  **In `Perspective.lean`.** `Viewpoint` (an observer with its perspective, receiving and
  reading spaces per observer), `Viewpoint.read V P = 𝒫_O(𝖤_{O,P})`,
  `joint Vs P : (i : Fin n) → (Vs i).Z`, and
  `ReconstructivelySufficient Vs K C` over presented states in a declared
  class `K` with declared equivalence `C`. `Viewpoint.ofFamily` takes the
  viewpoint at `O` from an observer-indexed reception. The one-record
  form is `jointOnRecord` / `SufficientOnRecord` with its three
  witnesses. `RelationallyComplete` (Def 15.2, `Sufficiency.lean`) is stated
  with `ReconstructivelySufficient`.

  **Added here.** One projection, the bottom row of the relative matrix
  `Q_{O,P}`, placed at two distinct observers: `ε` and `L`.
  * `g121_observers_distinct`: the two observers differ.
  * `g121_pair_sufficient`: jointly they determine the presented state's
    accumulated transform `M_P`, for every presented state.
  * `g121_at_root_alone_insufficient`, `g121_at_L_alone_insufficient`: each
    alone does not, with presented states in hand (`ε` against `R`; `L`
    against `LR`).
  * `g121_one_record_is_the_coincident_case`: with every observer equal,
    `joint` reads the one record `𝖤_{O,P}`, which is the one-record form.
-/
namespace RatioSpace

namespace Gaps.G1_21

/-- The bottom row of `Q_{O,P}`. Declares the relative matrix and reads
    nothing else. -/
def bottomRow : Perspective Mat2 (ℤ × ℤ) where
  reception :=
    { mask := Mask.onlyRelative
      read := EncounterRecord.relative
      honest := by intro E F h; exact h.2.2.1 rfl }
  projection := ⟨fun M => (M.c, M.d)⟩

/-- An observer at the root, and one a single `L` step away. -/
def atRoot : Observer := ⟨Frame.empty, [], 0⟩
def atL : Observer := ⟨Frame.empty, [false], 0⟩

/-- The bottom-row perspective placed at `O`. -/
def viewAt (O : Observer) : Viewpoint := ⟨O, Mat2, ℤ × ℤ, bottomRow⟩

/-- One perspective, two observers. -/
def pair : Fin 2 → Viewpoint
  | 0 => viewAt atRoot
  | 1 => viewAt atL

def onlyRoot : Fin 1 → Viewpoint := fun _ => viewAt atRoot
def onlyL : Fin 1 → Viewpoint := fun _ => viewAt atL

/-- The declared equivalence: same accumulated transform `M_P`. -/
def sameTransform (P P' : Observer) : Prop := P.matrix = P'.matrix

theorem g121_observers_distinct : atRoot ≠ atL := by decide

theorem inv_root : Mat2.inv2 atRoot.matrix = ⟨1, 0, 0, 1⟩ := by decide
theorem inv_L : Mat2.inv2 atL.matrix = ⟨1, 0, -1, 1⟩ := by decide

/-- The reading at `O` is the bottom row of `Q_{O,P} = M_O⁻¹ M_P`. -/
theorem read_bottomRow (O P : Observer) :
    (viewAt O).read P =
      ((Mat2.inv2 O.matrix * P.matrix).c, (Mat2.inv2 O.matrix * P.matrix).d) := rfl

/-- **Two observers, one projection, jointly sufficient** on every presented
    state for the accumulated transform. -/
theorem g121_pair_sufficient :
    ReconstructivelySufficient pair (fun _ => True) sameTransform := by
  refine ⟨⟨fun _ _ => rfl, fun _ _ _ _ h => h.symm, fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂⟩, ?_⟩
  intro P P' _ _ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  change (viewAt atRoot).read P = (viewAt atRoot).read P' at h0
  change (viewAt atL).read P = (viewAt atL).read P' at h1
  rw [read_bottomRow, read_bottomRow, inv_root] at h0
  rw [read_bottomRow, read_bottomRow, inv_L] at h1
  unfold sameTransform
  generalize P.matrix = M at h0 h1
  generalize P'.matrix = M' at h0 h1
  obtain ⟨a, b, c, d⟩ := M
  obtain ⟨a', b', c', d'⟩ := M'
  have hc : 0 * a + 1 * c = 0 * a' + 1 * c' := congrArg Prod.fst h0
  have hd : 0 * b + 1 * d = 0 * b' + 1 * d' := congrArg Prod.snd h0
  have ha : -1 * a + 1 * c = -1 * a' + 1 * c' := congrArg Prod.fst h1
  have hb : -1 * b + 1 * d = -1 * b' + 1 * d' := congrArg Prod.snd h1
  simp only [Int.zero_mul, Int.one_mul, Int.zero_add] at hc hd
  subst hc hd
  simp only [Int.one_mul, Int.neg_one_mul] at ha hb
  have ha' : a = a' := by
    have := congrArg (· - c) ha
    simp only [Int.add_sub_cancel] at this
    exact Int.neg_inj.mp this
  have hb' : b = b' := by
    have := congrArg (· - d) hb
    simp only [Int.add_sub_cancel] at this
    exact Int.neg_inj.mp this
  subst ha' hb'
  rfl

/-- At the root alone: `ε` and `R` have one bottom row and different
    transforms. -/
theorem g121_at_root_alone_insufficient :
    ¬ ReconstructivelySufficient onlyRoot (fun _ => True) sameTransform := by
  intro hs
  have h := hs.2 ⟨Frame.empty, [], 0⟩ ⟨Frame.empty, [true], 0⟩ trivial trivial (by
    funext i
    change (viewAt _).read _ = (viewAt _).read _
    rfl)
  exact absurd h (by unfold sameTransform; decide)

/-- At `L` alone: `L` and `LR` have one bottom row of `Q` and different
    transforms. -/
theorem g121_at_L_alone_insufficient :
    ¬ ReconstructivelySufficient onlyL (fun _ => True) sameTransform := by
  intro hs
  have h := hs.2 ⟨Frame.empty, [false], 0⟩ ⟨Frame.empty, [false, true], 0⟩ trivial trivial (by
    funext i
    change (viewAt _).read _ = (viewAt _).read _
    rfl)
  exact absurd h (by unfold sameTransform; decide)

/-- **The one-record form is the coincident case.** When every observer is `O`,
    each coordinate of `𝒥(P)` is its perspective applied to the one record
    `𝖤_{O,P}`. -/
theorem g121_one_record_is_the_coincident_case {n : ℕ} (Vs : Fin n → Viewpoint)
    (O : Observer) (hO : ∀ i, (Vs i).observer = O) (P : Observer) (i : Fin n) :
    joint Vs P i = (Vs i).persp.apply (EncounterRecord.of O P) := by
  simp only [joint, Viewpoint.read, hO]

end Gaps.G1_21

end RatioSpace
