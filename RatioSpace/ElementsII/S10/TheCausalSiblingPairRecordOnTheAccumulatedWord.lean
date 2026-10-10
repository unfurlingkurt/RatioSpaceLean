/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S10.Causal
import RatioSpace.ElementsII.S06.State
/-!
  Gap G2-07 · Elements II Definition 10.4, the causal sibling-pair record on the
  accumulated word.

  The book's record is `CF(x;g) = (ι_x, ι_{xg}, ι_{xḡ}, W(w_{xg}), F(w_{xg}), g, ḡ,
  pairStatus)`, and `w_{xg}` is the accumulated word of the child (Definition 5.1:
  `w_y = w_x g`, with `w_x = w₀v` by Definition 4.2). `Causal.lean`'s
  `causalRecord` builds `W` and `F` on the relative word `v ++ [g]`. This file adds
  the record on the accumulated word, proves what it is, and states exactly where
  and by how much the two records differ. No existing declaration is changed.
-/

namespace RatioSpace
namespace Gaps
namespace G2_07

open RatioSpace.Two Word

/-- **Definition 10.4, on the accumulated word.** Same identifiers, hands and
    status as `causalRecord`; the `W` and `F` fields are taken on the child's
    accumulated word `w_{xg} = w₀vg`, as the book writes them. -/
def causalRecordAcc (id0 : QuestionId) (seed : History) (v : Word) (g : Bool)
    (status : PairStatus := .proposed) : CausalRecord where
  parentId := (proposal id0 seed v).id
  childId := (childProposal id0 seed v g).id
  siblingId := (siblingAlt id0 seed v g).id
  wField := Two.W (childProposal id0 seed v g).fullWord
  fField := Two.F (childProposal id0 seed v g).fullWord
  hand := g
  oppHand := oppositeHand g
  status := status

/-- The child's accumulated word, in the `u ++ [g]` shape `W` is stated on. -/
theorem childProposal_fullWord_snoc (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    (childProposal id0 seed v g).fullWord = (seed.word ++ v) ++ [g] := by
  simp [childProposal, proposal, List.append_assoc]

/-- **`W(w_{xg}) = w_{xḡ}`.** The `W` field is exactly the sibling's accumulated
    word: the terminal hand is exchanged and the complete parent history kept. -/
theorem causalRecordAcc_wField_eq_sibling (id0 : QuestionId) (seed : History) (v : Word)
    (g : Bool) (st : PairStatus) :
    (causalRecordAcc id0 seed v g st).wField = (siblingAlt id0 seed v g).fullWord := by
  simp only [causalRecordAcc, siblingAlt]
  rw [childProposal_fullWord_snoc, childProposal_fullWord_snoc, Two.W_append]

/-- **The `W` field on the accumulated word is the relative one behind the seed
    word.** `W` only touches the last hand, so the seed's retained word `w₀`
    passes through unchanged. -/
theorem causalRecordAcc_wField_eq_prefix (id0 : QuestionId) (seed : History) (v : Word)
    (g : Bool) (st : PairStatus) :
    (causalRecordAcc id0 seed v g st).wField =
      seed.word ++ (causalRecord id0 seed v g st).wField := by
  simp only [causalRecordAcc, causalRecord]
  rw [childProposal_fullWord_snoc, Two.W_append, Two.W_append, List.append_assoc]

/-- **`F(w_{xg})` when the seed word is nonempty.** `F` exchanges the first hand
    of the accumulated word, which is the seed word's first hand, and keeps
    everything after it, including the relative word and the new hand. -/
theorem causalRecordAcc_fField_cons (id0 : QuestionId) (seed : History) (v : Word)
    (g : Bool) (st : PairStatus) {b : Bool} {rest : Word} (hs : seed.word = b :: rest) :
    (causalRecordAcc id0 seed v g st).fField = bar b :: (rest ++ v ++ [g]) := by
  simp only [causalRecordAcc]
  rw [childProposal_fullWord_snoc, hs]
  simpa [List.append_assoc] using Two.F_cons b (rest ++ (v ++ [g]))

/-- **When the seed word is empty the two records coincide**, every field. -/
theorem causalRecordAcc_eq_causalRecord_of_nil (id0 : QuestionId) (seed : History) (v : Word)
    (g : Bool) (st : PairStatus) (hs : seed.word = []) :
    causalRecordAcc id0 seed v g st = causalRecord id0 seed v g st := by
  have hw : (childProposal id0 seed v g).fullWord = v ++ [g] := by
    rw [childProposal_fullWord_snoc, hs, List.nil_append]
  simp only [causalRecordAcc, causalRecord, hw]

/-- `rs` keeps word length. -/
theorem rs_length (w : Word) : (rs w).length = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      have hrs : rs (b :: w) = rs w ++ [bar b] := by simp [rs, shadow]
      rw [hrs, List.length_append, ih]; rfl

/-- `W` keeps the length of a nonempty word. -/
theorem W_length_snoc (u : Word) (g : Bool) : (Two.W (u ++ [g])).length = (u ++ [g]).length := by
  rw [Two.W_append, List.length_append, List.length_append]; rfl

/-- `F` keeps the length of a nonempty word. -/
theorem F_length_cons (b : Bool) (rest : Word) : (Two.F (b :: rest)).length = (b :: rest).length
  := by
  rw [Two.F_cons]; rfl

/-- **Both word fields of the accumulated record are longer than the relative
    record's by exactly the seed word's length.** -/
theorem causalRecordAcc_fields_length (id0 : QuestionId) (seed : History) (v : Word)
    (g : Bool) (st : PairStatus) :
    (causalRecordAcc id0 seed v g st).wField.length =
        seed.word.length + (causalRecord id0 seed v g st).wField.length ∧
    (causalRecordAcc id0 seed v g st).fField.length =
        seed.word.length + (causalRecord id0 seed v g st).fField.length := by
  have hacc : (childProposal id0 seed v g).fullWord = (seed.word ++ v) ++ [g] :=
    childProposal_fullWord_snoc id0 seed v g
  have hF : ∀ w : Word, w ≠ [] → (Two.F w).length = w.length := by
    intro w hw
    cases w with
    | nil => exact absurd rfl hw
    | cons b rest => exact F_length_cons b rest
  have hne1 : (seed.word ++ v) ++ [g] ≠ [] := by simp
  have hne2 : v ++ [g] ≠ [] := by simp
  refine ⟨?_, ?_⟩
  · change (Two.W (childProposal id0 seed v g).fullWord).length = _ + (Two.W (v ++ [g])).length
    rw [hacc, W_length_snoc, W_length_snoc]
    simp only [List.length_append]
    omega
  · change (Two.F (childProposal id0 seed v g).fullWord).length = _ + (Two.F (v ++ [g])).length
    rw [hacc, hF _ hne1, hF _ hne2]
    simp only [List.length_append]
    omega

/-- **The relative record is the book's record only at an empty seed word.** -/
theorem causalRecordAcc_ne_causalRecord_of_ne_nil (id0 : QuestionId) (seed : History)
    (v : Word) (g : Bool) (st : PairStatus) (hs : seed.word ≠ []) :
    (causalRecordAcc id0 seed v g st).wField ≠ (causalRecord id0 seed v g st).wField ∧
    (causalRecordAcc id0 seed v g st).fField ≠ (causalRecord id0 seed v g st).fField := by
  have hlen := causalRecordAcc_fields_length id0 seed v g st
  have hpos : 0 < seed.word.length := by
    cases hw : seed.word with
    | nil => exact absurd hw hs
    | cons b rest => exact Nat.succ_pos _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg List.length h; omega
  · have := congrArg List.length h; omega

/-- **`W` and `F` are two presentations of one exact causal pair.** Each field,
    read back through its own involution, returns the child's accumulated word;
    neither carries anything the other does not. -/
theorem causalRecordAcc_presentations (id0 : QuestionId) (seed : History) (v : Word)
    (g : Bool) (st : PairStatus) :
    Two.W (causalRecordAcc id0 seed v g st).wField = (childProposal id0 seed v g).fullWord ∧
    Two.F (causalRecordAcc id0 seed v g st).fField = (childProposal id0 seed v g).fullWord := by
  have hne : (childProposal id0 seed v g).fullWord ≠ [] := by
    rw [childProposal_fullWord_snoc]; simp
  exact ⟨Two.W_involutive hne, Two.F_involutive hne⟩

/-- **Definition 10.4 read off an archived child core**, on the accumulated word:
    the counterpart of `Accumulation.causalPairOf`. -/
def causalPairOfAcc (c : Core) : Option CausalRecord :=
  c.hand.map fun g => causalRecordAcc c.seedId c.seed c.relWord.dropLast g

/-- At a child core the record is the parent's split record on the accumulated
    word. -/
theorem causalPairOfAcc_childCore (c : Core) (g : Bool) (entry : ℕ) (prov : Provenance) :
    causalPairOfAcc (childCore c g entry prov) =
      some (causalRecordAcc c.seedId c.seed c.relWord g) := by
  simp [causalPairOfAcc, childCore, Core.ofProposal, childProposal, proposal]

/-- At a child core of a well-formed parent the record names the parent, the
    child and the sibling by their archived identifiers, and its `W` field is the
    archived sibling's accumulated word. -/
theorem causalPairOfAcc_childCore_fields (c : Core) (hc : c.WellFormed) (g : Bool)
    (entry : ℕ) (prov : Provenance) :
    ∃ r, causalPairOfAcc (childCore c g entry prov) = some r ∧
      r.parentId = c.id ∧
      r.childId = (childCore c g entry prov).id ∧
      r.siblingId = (childCore c (!g) entry prov).id ∧
      r.wField = (childCore c (!g) entry prov).fullWord ∧
      r.status = .proposed := by
  refine ⟨_, causalPairOfAcc_childCore c g entry prov, ?_, rfl, rfl, ?_, rfl⟩
  · exact hc.2.2.2.2.1.symm
  · exact causalRecordAcc_wField_eq_sibling c.seedId c.seed c.relWord g .proposed

#print axioms causalRecordAcc
#print axioms childProposal_fullWord_snoc
#print axioms causalRecordAcc_wField_eq_sibling
#print axioms causalRecordAcc_wField_eq_prefix
#print axioms causalRecordAcc_fField_cons
#print axioms causalRecordAcc_eq_causalRecord_of_nil
#print axioms rs_length
#print axioms W_length_snoc
#print axioms F_length_cons
#print axioms causalRecordAcc_fields_length
#print axioms causalRecordAcc_ne_causalRecord_of_ne_nil
#print axioms causalRecordAcc_presentations
#print axioms causalPairOfAcc
#print axioms causalPairOfAcc_childCore
#print axioms causalPairOfAcc_childCore_fields

end G2_07
end Gaps
end RatioSpace
