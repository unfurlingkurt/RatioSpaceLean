/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S05.Depth
import RatioSpace.ElementsI.S05.Zphi
/-!
  Elements I §5.8-5.9, the bridge module — D-07 and D-08
  (`research/lean-support/DIVERGENCE.md`).

  `Depth.lean` and `Zphi.lean` do not import each other, by design (see
  the header of `Depth.lean`): the continued-fraction depth coordinates on one
  side, the exact golden ring on the other. Def 5.8 and 5.9 sit at their
  junction and neither file alone can state them, because the book's objects
  are a *candidate against a shared active family* — `Depth.lean` has the
  candidate and family (`tensionSignature`), `Zphi.lean` has only the raw
  integer list the fold consumes (`coherence`, and `SignatureSumDegenerate`,
  formerly `Degenerate`).

  Tali's sweep found the consequence exactly: `coherence` and the old
  `Degenerate` type an already-computed signature, not the candidate and
  family that produced it, so `local_min_ne_global_max` and
  `book_degeneracy`/`degeneracy_one_four` are algebraic witnesses over
  abstract lists, not yet geometric ones. This file supplies the missing
  geometric layer without touching the fold: `globalCoherence` and
  `CoherenceDegenerate` are Def 5.8 and Def 5.9 themselves, stated on real
  `IPres` candidates against a real shared family, built from
  `Depth.lean`'s `tensionSignature` and `Zphi.lean`'s `coherence`.
-/

namespace RatioSpace
namespace Pres

open RatioSpace.Zphi

/-- **Definition 5.8, in full — global φ-coherence of a candidate against a
    shared active family.** `C_φ(r) = ∑ φ^(−T_end(r, rᵢ))`, `r` and the family
    both real `IPres` objects, not an asserted integer list. D-07's repair:
    `Zphi.coherence` stays the fold; this closes the domain gap the row
    named, `tensionSignature r fam` supplying exactly the signature the fold
    was missing a proof of. -/
def globalCoherence (r : IPres) (fam : List IPres) : Zphi :=
  coherence (tensionSignature r fam)

@[simp] theorem globalCoherence_def (r : IPres) (fam : List IPres) :
    globalCoherence r fam = coherence (tensionSignature r fam) := rfl

/-- **Definition 5.9, in full — coherence degeneracy of two candidates against
    one shared family.** D-08's repair: the old `Degenerate` (now
    `Zphi.SignatureSumDegenerate`) compared raw lists with no family in the
    type, so `book_degeneracy : Degenerate [1,2] [0]` could name lists of
    unequal length, which under one fixed family cannot happen. Here the
    family is a genuine argument shared by both sides, so every instance of
    this relation is, by construction, two signatures against one family. -/
def CoherenceDegenerate (r s : IPres) (fam : List IPres) : Prop :=
  globalCoherence r fam = globalCoherence s fam

instance (r s : IPres) (fam : List IPres) :
    Decidable (CoherenceDegenerate r s fam) := by
  unfold CoherenceDegenerate; infer_instance

/-! ### The geometric separation witness

`Zphi.lean`'s `local_min_ne_global_max` makes its point on the asserted lists
`[1, 10]` and `[2, 2]`. Here the same divergence is exhibited for two real
candidates against one real shared family: minimizing the local tension to
one anchor and maximizing the coherence sum over the whole family are not the
same objective. -/

/-- One shared active family, two members: `1:1` and `1:9`. -/
def sepFam : List IPres :=
  [ip 1 1 (by decide) (by decide), ip 1 9 (by decide) (by decide)]

/-- The candidate with the smaller local tension: `T_end` to the family is
    `[1, 5]`, so the minimum single tension is `1`. -/
def sepLocalWinner : IPres := ip 1 2 (by decide) (by decide)

/-- The candidate with the larger local tension but the larger global
    coherence: `T_end` to the family is `[2, 2]`, matching the book's own
    two-anchor tie shape, minimum single tension `2`. -/
def sepCoherenceWinner : IPres := ip 1 3 (by decide) (by decide)

theorem sepLocalWinner_signature :
    tensionSignature sepLocalWinner sepFam = [1, 5] := by decide

theorem sepCoherenceWinner_signature :
    tensionSignature sepCoherenceWinner sepFam = [2, 2] := by decide

/-- **The exact gap.** Not compared numerically: the difference between the
    two global coherences is identified as `φ^(−6)`. Kept separate from
    `coherence_witness_separates` below on purpose — see the note there. -/
theorem coherence_gap_is_phiNegPow_six :
    globalCoherence sepCoherenceWinner sepFam
      - globalCoherence sepLocalWinner sepFam = phiNegPow 6 := by
  simp only [globalCoherence_def, sepLocalWinner_signature, sepCoherenceWinner_signature]
  decide

/-- **The geometric witness itself.** The candidate that wins on local
    tension (`1 < 2`) loses on global coherence. Same shape as
    `Zphi.coherence_one_ten_lt_two_two`, now with `r`, `s` and the family all
    real `IPres` objects rather than asserted lists. **Proved by `decide`
    directly, not via `coherence_gap_is_phiNegPow_six` and `sub_pos`.** When
    this was written (2026-08-25) the `sub_pos` route picked up
    `Classical.choice` through `Zphi`'s order instances. Those instances are
    choice-free since 2026-09-22 (`Zphi.mul_pos` through `Zsqrtd`,
    `IsStrictOrderedRing` built field by field): `linearOrder`, `Zphi.mul_pos`,
    `Zphi.sub_pos`, `phiNegPow_strictAnti`, `coherence_lt_of_lt`,
    `coherence_one_ten_lt_two_two` and `local_min_ne_global_max` are all
    `[propext, Quot.sound]` (`#print axioms`, 2026-10-01). Mathlib's generic
    `sub_pos` is `[propext]` by itself, but at `Zphi` it picks up choice
    through the derived `AddRightStrictMono` instance
    (`IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`): the gap route
    written with it carries choice, written with `Zphi.sub_pos` it does not.
    `SignatureSumDegenerate` is fully decidable, so `<` is too, and `decide`
    needs neither. -/
theorem coherence_witness_separates :
    globalCoherence sepLocalWinner sepFam < globalCoherence sepCoherenceWinner sepFam := by
  simp only [globalCoherence_def, sepLocalWinner_signature, sepCoherenceWinner_signature]
  decide

/-- **The full separation, in the book's own vocabulary.** The local minimum
    tension of `sepLocalWinner`'s signature is strictly the smaller one, and
    yet its global coherence is strictly the smaller one too — the two
    objectives of Def 5.8 disagree on this real family, exactly as
    `local_min_ne_global_max` claimed abstractly. -/
theorem local_min_ne_global_max_geometric :
    (tensionSignature sepLocalWinner sepFam).min? = some 1 ∧
    (tensionSignature sepCoherenceWinner sepFam).min? = some 2 ∧
    (1 : ℕ) < 2 ∧
    globalCoherence sepLocalWinner sepFam < globalCoherence sepCoherenceWinner sepFam :=
  ⟨by rw [sepLocalWinner_signature]; decide,
   by rw [sepCoherenceWinner_signature]; decide,
   by decide, coherence_witness_separates⟩

/-! ### Geometric tie witnesses for Definition 5.9

`CoherenceDegenerate` is decidable, and until now no instance of it was in the
tree (Lean gap G1-07). Below are two ties, each two real candidates against one
real shared family. In both the candidates are not proportionally equivalent and
their signatures are not permutations of each other, so neither tie is the
trivial one a reordering of the family would give. Found by exact search over
components up to `7` with integer arithmetic in `ℤ[φ]`. The non-permutation
claims are proved by a count that differs, not by `decide` on `List.Perm`,
whose decision procedure reaches `Classical.choice`. -/

/-- The first shared family: `1:2` and `2:1`. -/
def tieFam : List IPres :=
  [ip 1 2 (by decide) (by decide), ip 2 1 (by decide) (by decide)]

theorem tie_one_one_signature :
    tensionSignature (ip 1 1 (by decide) (by decide)) tieFam = [1, 1] := by decide

theorem tie_one_two_signature :
    tensionSignature (ip 1 2 (by decide) (by decide)) tieFam = [0, 3] := by decide

/-- **Definition 5.9, exercised.** Against `(1:2, 2:1)`, `1:1` has signature
    `[1, 1]` and `1:2` has `[0, 3]`, and the two coherences are equal:
    `2φ⁻¹ = 1 + φ⁻³`. The candidates are not proportionally equivalent
    (`1·2 ≠ 1·1`), and `[1, 1]` is not a permutation of `[0, 3]`. -/
theorem coherenceDegenerate_one_one_one_two :
    CoherenceDegenerate (ip 1 1 (by decide) (by decide)) (ip 1 2 (by decide) (by decide))
      tieFam ∧
    ¬ Prop' (ip 1 1 (by decide) (by decide)).toPres (ip 1 2 (by decide) (by decide)).toPres ∧
    ¬ ([1, 1] : List ℕ).Perm [0, 3] :=
  ⟨by decide, by decide, fun h => absurd (h.count_eq 0) (by decide)⟩

/-- The second shared family: `1:2` and `3:2`. Neither candidate below is a
    member of it. -/
def tieFam₂ : List IPres :=
  [ip 1 2 (by decide) (by decide), ip 3 2 (by decide) (by decide)]

theorem tie_one_three_signature :
    tensionSignature (ip 1 3 (by decide) (by decide)) tieFam₂ = [2, 5] := by decide

theorem tie_two_one_signature :
    tensionSignature (ip 2 1 (by decide) (by decide)) tieFam₂ = [3, 3] := by decide

/-- **A tie with neither candidate in the family.** Against `(1:2, 3:2)`,
    `1:3` has signature `[2, 5]` and `2:1` has `[3, 3]`, and
    `φ⁻² + φ⁻⁵ = 2φ⁻³`. -/
theorem coherenceDegenerate_one_three_two_one :
    CoherenceDegenerate (ip 1 3 (by decide) (by decide)) (ip 2 1 (by decide) (by decide))
      tieFam₂ ∧
    ¬ Prop' (ip 1 3 (by decide) (by decide)).toPres (ip 2 1 (by decide) (by decide)).toPres ∧
    ¬ ([2, 5] : List ℕ).Perm [3, 3] ∧
    ip 1 3 (by decide) (by decide) ∉ tieFam₂ ∧ ip 2 1 (by decide) (by decide) ∉ tieFam₂ :=
  ⟨by decide, by decide, fun h => absurd (h.count_eq 3) (by decide), by decide, by decide⟩

end Pres
end RatioSpace
