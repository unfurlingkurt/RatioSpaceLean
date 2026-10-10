/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S17.Terminal
import RatioSpace.ElementsII.S08.Coherence
/-!
  Gap G2-04 — Elements II Proposition 4.11, a question bounds but does not force
  an answer.

  `Two/Cavity.lean`'s `question_bounds_not_forces` is one instance of the
  initial clause (two seeds, depth 1, no predicates, both survive). The book's
  proof is general: for every finite tagged proposal family `B` the membership
  predicate `γ_B` is exact. This file builds `γ_B` and proves both clauses from
  it, for arbitrary data:

    * **initial:** adjoining `γ_B` to any declared predicate family cuts the
      initial support `S̃₀` down to exactly `B`, for every duplicate-free `B`
      inside it; with `B = ∅` the initial support is empty whatever the rest of
      the question is, so no question type forces a singleton;
    * **terminal:** at any tick, in particular the terminal tick `h`, adjoining
      `γ_B` to the declared admission predicate makes the admitted family
      exactly `B`, and Construction Axiom II.1 then returns `B`'s receptions
      whole whenever `|B| < 3` (Corollary 8.12, `rejection_needs_three`). So
      `B = ∅`, one occurrence, two occurrences give the terminal statuses
      `empty`, `singleton`, `unresolved-multiple`, and the status is read off
      `|B|` alone.
-/

namespace RatioSpace
namespace Gaps

open RatioSpace.Two RatioSpace.Two.Terminal

-- Every field of a proposal record has decidable equality, so membership in a
-- finite family of records is decidable.
deriving instance DecidableEq for RatioSpace.Two.ProposalRecord

/-! ## `γ_B`, the membership predicate -/

/-- **Proposition 4.11's `γ_B`** at Definition 4.3's occurrence-predicate type:
    `1` on members of `B`, `0` off it, ignoring context and event position. -/
def gammaB {C : Type} (B : List ProposalRecord) : OccPred C :=
  fun y _ _ => decide (y ∈ B)

/-- `γ_B` is exact: it is `1` exactly on `B`. -/
theorem gammaB_eq_true_iff {C : Type} (B : List ProposalRecord) (y : ProposalRecord) (c : C)
    (k : ℕ) : gammaB B y c k = true ↔ y ∈ B := by
  simp [gammaB]

/-- A filter by membership in a duplicate-free family `B` contained in a
    duplicate-free list is a permutation of `B`. -/
theorem filter_mem_perm {α : Type} [DecidableEq α] {L B : List α} (hL : L.Nodup)
    (hB : B.Nodup) (hBL : B ⊆ L) : (L.filter fun y => decide (y ∈ B)).Perm B := by
  have hF : (L.filter fun y => decide (y ∈ B)).Nodup := hL.filter _
  have h1 : (L.filter fun y => decide (y ∈ B)) ⊆ B := fun y hy => by
    simpa using (List.mem_filter.mp hy).2
  have h2 : B ⊆ (L.filter fun y => decide (y ∈ B)) := fun y hy =>
    List.mem_filter.mpr ⟨hBL hy, by simpa using hy⟩
  exact (List.subperm_of_subset hF h1).antisymm (List.subperm_of_subset hB h2)

/-! ## The initial clause -/

/-- Adjoining `γ_B` to a declared predicate family filters the initial support
    by membership in `B`. -/
theorem S0tilde_gammaB {Cert : Type} (F : Frame) (N : ℕ)
    (preds : List (OccPred (InitContext Cert))) (ctx : InitContext Cert)
    (seeds : List (QuestionId × History)) (B : List ProposalRecord) :
    S0tilde F N (preds ++ [gammaB B]) ctx seeds =
      (S0tilde F N preds ctx seeds).filter fun y => decide (y ∈ B) := by
  unfold S0tilde
  rw [List.filter_filter]
  apply List.filter_congr
  intro y _
  by_cases hy : y ∈ B <;> simp [gammaB, hy, List.all_append]

/-- **Proposition 4.11, initial clause, general.** For every question and every
    duplicate-free family `B` of seed records inside its initial support, the
    question with `γ_B` adjoined has initial support exactly `B`. -/
theorem S0tilde_gammaB_perm {Cert : Type} (F : Frame) (N : ℕ)
    (preds : List (OccPred (InitContext Cert))) (ctx : InitContext Cert)
    (seeds : List (QuestionId × History)) {B : List ProposalRecord}
    (hS : (S0tilde F N preds ctx seeds).Nodup) (hB : B.Nodup)
    (hBS : B ⊆ S0tilde F N preds ctx seeds) :
    (S0tilde F N (preds ++ [gammaB B]) ctx seeds).Perm B := by
  rw [S0tilde_gammaB]
  exact filter_mem_perm hS hB hBS

/-- The initial support's size is then `|B|`: no seed, one seed, or several. -/
theorem S0tilde_gammaB_length {Cert : Type} (F : Frame) (N : ℕ)
    (preds : List (OccPred (InitContext Cert))) (ctx : InitContext Cert)
    (seeds : List (QuestionId × History)) {B : List ProposalRecord}
    (hS : (S0tilde F N preds ctx seeds).Nodup) (hB : B.Nodup)
    (hBS : B ⊆ S0tilde F N preds ctx seeds) :
    (S0tilde F N (preds ++ [gammaB B]) ctx seeds).length = B.length :=
  (S0tilde_gammaB_perm F N preds ctx seeds hS hB hBS).length_eq

/-- `γ_∅` empties the initial support of every question. -/
theorem S0tilde_gammaB_nil {Cert : Type} (F : Frame) (N : ℕ)
    (preds : List (OccPred (InitContext Cert))) (ctx : InitContext Cert)
    (seeds : List (QuestionId × History)) :
    S0tilde F N (preds ++ [gammaB []]) ctx seeds = [] := by
  rw [S0tilde_gammaB]
  simp

/-- **Proposition 4.11, initial clause, the negation the book states.** For any
    frame, depth, context and seeds, the extended question type does not imply
    a singleton initial support: some exact predicate family gives another
    size. -/
theorem initial_support_not_forced {Cert : Type} (F : Frame) (N : ℕ) (ctx : InitContext Cert)
    (seeds : List (QuestionId × History)) :
    ¬ ∀ preds : List (OccPred (InitContext Cert)), (S0tilde F N preds ctx seeds).length = 1 := by
  intro h
  have h0 := h ([] ++ [gammaB []])
  rw [S0tilde_gammaB_nil] at h0
  simp at h0

/-! ## The terminal clause -/

/-- Adjoining `γ_B` to the declared admission predicate filters the admitted
    family (Definition 7.1) by membership in `B`, at any tick. -/
theorem admitted_gammaB (MO : Mat2) (pred : ProposalRecord → Bool) (P : List ProposalRecord)
    (B : List ProposalRecord) :
    Two.admitted MO (fun y => pred y && decide (y ∈ B)) P =
      (Two.admitted MO pred P).filter fun y => decide (y ∈ B) := by
  unfold Two.admitted
  rw [List.filter_filter]
  apply List.filter_congr
  intro y _
  by_cases hy : y ∈ B <;> simp [hy]

/-- **Proposition 4.11, terminal clause, general.** At any tick, in particular
    the terminal one, let `f` read each admitted occurrence as the relation
    Construction Axiom II.1 compares. For every duplicate-free family `B` of
    admitted occurrences with `|B| < 3`, the support selected from the
    `γ_B`-admitted family has exactly `|B|` members, so its terminal status is
    `termStatus |B|`. -/
theorem support_gammaB_length (MO : Mat2) (pred : ProposalRecord → Bool)
    (P : List ProposalRecord) (f : ProposalRecord → IPres) {B : List ProposalRecord}
    (hA : (Two.admitted MO pred P).Nodup) (hB : B.Nodup)
    (hBA : B ⊆ Two.admitted MO pred P) (h3 : B.length < 3) :
    (support ((Two.admitted MO (fun y => pred y && decide (y ∈ B)) P).map f)).length =
      B.length := by
  have hperm : (Two.admitted MO (fun y => pred y && decide (y ∈ B)) P).Perm B := by
    rw [admitted_gammaB]
    exact filter_mem_perm hA hB hBA
  have hlen : ((Two.admitted MO (fun y => pred y && decide (y ∈ B)) P).map f).length =
      B.length := by
    rw [List.length_map, hperm.length_eq]
  rw [rejection_needs_three (by omega), hlen]

theorem terminal_status_gammaB (MO : Mat2) (pred : ProposalRecord → Bool)
    (P : List ProposalRecord) (f : ProposalRecord → IPres) {B : List ProposalRecord}
    (hA : (Two.admitted MO pred P).Nodup) (hB : B.Nodup)
    (hBA : B ⊆ Two.admitted MO pred P) (h3 : B.length < 3) :
    termStatus
        (support ((Two.admitted MO (fun y => pred y && decide (y ∈ B)) P).map f)).length =
      termStatus B.length := by
  rw [support_gammaB_length MO pred P f hA hB hBA h3]

/-- `γ_∅` makes the terminal status `empty` for every proposal family, observer
    chart, declared predicate and reading. -/
theorem terminal_status_gammaB_nil (MO : Mat2) (pred : ProposalRecord → Bool)
    (P : List ProposalRecord) (f : ProposalRecord → IPres) :
    termStatus
        (support ((Two.admitted MO (fun y => pred y && decide (y ∈ ([] : List _))) P).map
          f)).length = .empty := by
  rw [admitted_gammaB]
  simp [termStatus]

/-- **Proposition 4.11, terminal clause, the negation the book states.** For any
    terminal proposal family, chart and reading, the declared admission
    predicate does not force a singleton terminal status. -/
theorem terminal_support_not_forced (MO : Mat2) (P : List ProposalRecord)
    (f : ProposalRecord → IPres) :
    ¬ ∀ pred : ProposalRecord → Bool,
      termStatus (support ((Two.admitted MO pred P).map f)).length = .singleton := by
  intro h
  have h0 := h (fun y => (fun _ => true) y && decide (y ∈ ([] : List ProposalRecord)))
  rw [terminal_status_gammaB_nil] at h0
  exact absurd h0 (by decide)

#print axioms gammaB
#print axioms gammaB_eq_true_iff
#print axioms filter_mem_perm
#print axioms S0tilde_gammaB
#print axioms S0tilde_gammaB_perm
#print axioms S0tilde_gammaB_length
#print axioms S0tilde_gammaB_nil
#print axioms initial_support_not_forced
#print axioms admitted_gammaB
#print axioms support_gammaB_length
#print axioms terminal_status_gammaB
#print axioms terminal_status_gammaB_nil
#print axioms terminal_support_not_forced

end Gaps
end RatioSpace
