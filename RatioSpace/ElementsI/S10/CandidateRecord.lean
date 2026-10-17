/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S10.Crystal
/-!
  Gap G1-17 — Elements I §10, Definition 10.1, candidate record: the star and
  the signature tied to the active family.

  **Book statement.** The candidate carries "the complete composition star" and
  "the ordered tension signature", `Σ_τ(r)` and `𝐓_τ(r)`: the star of Definition
  4.4 and the signature of Definition 5.6, both of `r` against `𝒜_τ`.

  **The carrier.** `Candidate` (`Crystal.lean`) stores `star : List IPres`
  and `signature : List ℕ` as free fields. Nothing in the type ties them to a family:
  `relation_does_not_determine_candidate` fills both with `[]`, which is the
  right star and signature only against the empty family.

  **Added.**
  * `g117_Consistent C A`: `C.star = star r A.relations` and
    `C.signature = A.tensionSignature r`, with `r = C.history.addressedI`.
    Decidable.
  * `g117_ofFamily H A`: the constructor from a history and a family.
    `g117_ofFamily_consistent`: it satisfies the predicate.
    `g117_consistent_iff`: a candidate is consistent with `A` exactly when it is
    `g117_ofFamily C.history A`. So against a fixed family the record is a
    function of the history, and the two stored fields carry no freedom.
  * `g117_consistent_ext`: two candidates consistent with the same family are
    equal iff their histories are.
  * `g117_free_fields_inconsistent`: the free-field witness of
    `relation_does_not_determine_candidate` is not consistent with the one-member
    family `[L]`: its star and signature are `[]`, the family's have length 1.
  * `g117_initialRecord_eq`, `g117_initialEnsemble_eq`,
    `g117_initialEnsemble_consistent`: Def 10.1's
    initial record `initialRecord Q r` (`Crystal.lean`) is `g117_ofFamily r
    Q.active`, and every record of `initialEnsemble Q` is consistent with the
    question's active family.
  * `g117_relation_does_not_determine_consistent`: the book's "not merely a
    reduced fraction" still holds with the fields tied: two candidates, both
    consistent with `[L]`, one relation, different records.
-/
namespace RatioSpace

open Pres

namespace Gaps.G1_17

/-- **Definition 10.1, the family-relative fields.** The stored star and
    signature are Definition 4.4's star and Definition 5.6's signature of the
    candidate's relation against the active family. -/
def g117_Consistent (C : Candidate) (A : ActiveFamily) : Prop :=
  C.star = IPres.star C.history.addressedI A.relations ∧
  C.signature = A.tensionSignature C.history.addressedI

instance (C : Candidate) (A : ActiveFamily) : Decidable (g117_Consistent C A) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Definition 10.1, as a constructor.** The candidate record of a history
    against an active family. -/
def g117_ofFamily (H : History) (A : ActiveFamily) : Candidate :=
  ⟨H, IPres.star H.addressedI A.relations, A.tensionSignature H.addressedI⟩

theorem g117_ofFamily_consistent (H : History) (A : ActiveFamily) :
    g117_Consistent (g117_ofFamily H A) A :=
  ⟨rfl, rfl⟩

@[simp] theorem g117_ofFamily_history (H : History) (A : ActiveFamily) :
    (g117_ofFamily H A).history = H := rfl

/-- Against a fixed family the consistent record is the constructor's, so it
    is a function of the history alone. -/
theorem g117_consistent_iff (C : Candidate) (A : ActiveFamily) :
    g117_Consistent C A ↔ C = g117_ofFamily C.history A := by
  obtain ⟨H, s, t⟩ := C
  constructor
  · rintro ⟨hs, ht⟩
    simp only at hs ht
    subst hs ht
    rfl
  · intro h
    rw [h]
    exact g117_ofFamily_consistent H A

/-- Two candidates consistent with the same family are equal exactly when
    their histories are. -/
theorem g117_consistent_ext {C D : Candidate} {A : ActiveFamily}
    (hC : g117_Consistent C A) (hD : g117_Consistent D A) :
    C = D ↔ C.history = D.history := by
  constructor
  · intro h; rw [h]
  · intro h
    rw [(g117_consistent_iff C A).1 hC, (g117_consistent_iff D A).1 hD, h]

/-- **Definition 10.1's initial record is this constructor.** `initialRecord Q r`
    (`Crystal.lean`) is `g117_ofFamily r Q.active`, by `rfl`. -/
theorem g117_initialRecord_eq (Q : Question) (r : History) :
    initialRecord Q r = g117_ofFamily r Q.active := rfl

/-- The initial ensemble is Def 10.1's set of records of `S₀(𝒬_τ)` against
    `𝒜_τ`. -/
theorem g117_initialEnsemble_eq (Q : Question) :
    initialEnsemble Q = ((S0 Q).map fun r => g117_ofFamily r Q.active).dedup := rfl

/-- Every record in the initial ensemble is consistent with the question's
    active family: its star and signature are the book's, not free. -/
theorem g117_initialEnsemble_consistent (Q : Question) :
    ∀ C ∈ initialEnsemble Q, g117_Consistent C Q.active := by
  intro C hC
  obtain ⟨r, _, rfl⟩ := mem_initialEnsemble.1 hC
  exact g117_ofFamily_consistent r Q.active

/-- The one-member family `[L]`, from the root. -/
def g117_family : ActiveFamily := [⟨Frame.empty, [false]⟩]

/-- **The free fields are free.** The first witness of
    `relation_does_not_determine_candidate` stores `[]` for both fields; against
    `[L]` the star and signature have one entry each, so it is not a record of
    that family. -/
theorem g117_free_fields_inconsistent :
    ¬ g117_Consistent ⟨⟨Frame.empty, [false]⟩, [], []⟩ g117_family := by
  decide

/-- **"Not merely a reduced fraction", with the fields tied.** Two candidates,
    both consistent with `[L]`, carrying the same relation, and different. -/
theorem g117_relation_does_not_determine_consistent :
    ∃ C D : Candidate, g117_Consistent C g117_family ∧ g117_Consistent D g117_family ∧
      C ≠ D ∧ C.relation = D.relation :=
  ⟨g117_ofFamily ⟨Frame.empty, [false]⟩ g117_family,
   g117_ofFamily ⟨Frame.walk Frame.empty [false], []⟩ g117_family,
   g117_ofFamily_consistent _ _, g117_ofFamily_consistent _ _,
   by decide, by decide⟩

end Gaps.G1_17

end RatioSpace
