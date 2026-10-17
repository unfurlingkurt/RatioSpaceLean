/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S04.Cavity
/-!
  Elements II §5 — Candidate generation by mediant inheritance.

  Definition 5.1 through Proposition 5.7. Every field the book lists as
  "inherited data" of a child proposal (`ι_y`, `w_y`, `M_y`, `F_y`, `r_y`,
  `par(y)`) is a theorem about one construction here, `childProposal`, rather
  than six separate assignments: extend the relative word by one letter and
  re-derive everything from §4's `proposal`.

  Two things are sharper than the prose, and each is noted at its theorem:

    * **Proposition 5.3 needs no new proof.** `Frame.stepL` and `Frame.stepR`
      already *are* Def 2.4's two child frames, `(C₋⊕C₊,C₋)` and `(C₊,C₋⊕C₊)`,
      established in `Frame.lean` on `Pres`. This section's
      Prop 5.3 is `childProposal_frame_stepL/R`, which says a proposal's reached
      frame is exactly that stepped frame, and cites those definitions rather
      than reproving the mediant arithmetic.
    * **Proposition 5.4 is proved at the identifier level, once, for any two
      proposals from any two parents.** `QuestionId.child_inj` uses
      `List.append_inj'` on the retained relative word; `childProposal_inj`
      restates it in this file's vocabulary. The book's "distinct parents have
      disjoint child occurrences" is the contrapositive.
    * **Proposition 5.7 transports the *world*-anchored fields only.**
      `transportSeed` prefixes a seed's own retained word by `u`, changing
      `fullWord`, `fullMatrix` and `frame` — genuinely, not merely notationally,
      since `Z_u` moves the whole configuration's reference point — while
      leaving the occurrence identifier and relative word untouched, matching
      the book's own distinction between world and local data. The covariance
      is then Observer.lean's Proposition 3.5, cited rather than re-derived.

  Everything computable. No `sorry`, no `axiom`.
-/

namespace RatioSpace
namespace Two

open Mat2 Word Frame Pres RatioSpace

/-! ## Definition 5.1 — Active occurrence and child proposal -/

/-- **Definition 5.1.** The child proposal of `id0`'s occurrence at relative
    word `v` from `seed`, by hand `g`: one more relative step, continuing from
    the same seed. `y = xg` where `x = proposal id0 seed v`. -/
def childProposal (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    ProposalRecord :=
  proposal id0 seed (v ++ [g])

/-- `ι_y = ι_x g`. -/
theorem childProposal_id (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    (childProposal id0 seed v g).id = (proposal id0 seed v).id.child g := by
  simp [childProposal, proposal, QuestionId.child]

/-- `par(y) = x`, read at the identifier level: deleting the last generator of
    the child's identifier returns the parent's. -/
theorem childProposal_parent (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    (childProposal id0 seed v g).id.parent = (proposal id0 seed v).id := by
  rw [childProposal_id, QuestionId.parent_child]

/-- `w_y = w_x g`. -/
theorem childProposal_fullWord (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    (childProposal id0 seed v g).fullWord = (proposal id0 seed v).fullWord ++ [g] := by
  simp [childProposal, proposal, List.append_assoc]

/-- `M_y = M_x g` — the accumulated matrix advances by right-multiplying the one
    new generator. Exactly `Word.G_snoc` read through `proposal`'s own matrix
    field. -/
theorem childProposal_fullMatrix (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    (childProposal id0 seed v g).fullMatrix =
      forward (proposal id0 seed v).fullMatrix (Word.gen g) := by
  simp [childProposal, proposal, forward, Word.G_snoc, Mat2.mul_assoc']

/-- `F_y = F_x·g`: one more fold of `select`. -/
theorem childProposal_frame (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    (childProposal id0 seed v g).frame =
      Frame.select (proposal id0 seed v).frame g := by
  simp [childProposal, proposal, Frame.walk, List.foldl_append]

/-- `r_y = r_{F_x}(g)`: the address reached from the parent's own frame by the
    one new hand. -/
theorem childProposal_addr (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    (childProposal id0 seed v g).addr =
      Frame.addressed (proposal id0 seed v).frame [g] := by
  simp [childProposal, proposal, Frame.addressed, Frame.walk, List.foldl_append]

/-! ## Proposition 5.3 — Child generation is mediant inheritance -/

/-- **Proposition 5.3, hand `L`.** `F_x·L = (C₋⊕C₊,C₋)`, Def 2.4's `stepL`.
    That `stepL` is the product with `L` is `Frame.toMat2_stepL`, cited here
    rather than reproduced. -/
theorem childProposal_frame_stepL (id0 : QuestionId) (seed : History) (v : Word) :
    (childProposal id0 seed v false).frame = Frame.stepL (proposal id0 seed v).frame := by
  simp [childProposal_frame, Frame.select]

/-- **Proposition 5.3, hand `R`.** `F_x·R = (C₊,C₋⊕C₊)`, Def 2.4's `stepR`. -/
theorem childProposal_frame_stepR (id0 : QuestionId) (seed : History) (v : Word) :
    (childProposal id0 seed v true).frame = Frame.stepR (proposal id0 seed v).frame := by
  simp [childProposal_frame, Frame.select]

/-! ## Definition 5.2 — Complete proposal family -/

/-- **Definition 5.2.** `P_{j+1}(S_j) = S_j × {L,R}`. The active occurrence set
    is a list of proposal records (Elements II §4's occurrence type); each
    parent contributes exactly its two children, both proposed before any
    admission or coherence comparison. -/
def proposalFamily (S : List ProposalRecord) : List ProposalRecord :=
  S.flatMap fun x => [childProposal x.seedId x.seed x.relWord false,
                       childProposal x.seedId x.seed x.relWord true]

/-! ## Corollary 5.5 — Exact proposal growth -/

/-- **Corollary 5.5.** `|P_{j+1}(S_j)| = 2|S_j|`. No merging: `proposalFamily`
    contributes exactly two list entries per parent, full stop. -/
theorem proposalFamily_length (S : List ProposalRecord) :
    (proposalFamily S).length = 2 * S.length := by
  induction S with
  | nil => simp [proposalFamily]
  | cons x xs ih => simp [proposalFamily, List.flatMap_cons]; omega

/-! ## Proposition 5.4 — Distinct parents have disjoint child occurrences -/

/-- **Proposition 5.4, at the identifier level.** `ι_x g = ι_y h ⟹ ι_x = ι_y
    ∧ g = h`. The identifier retains the seed and the full relative word, so
    equality of the extended words forces equality of the last letter and of
    the prefix left by deleting it — `List.append_inj'` on a length-one
    suffix. -/
theorem QuestionId.child_inj {i j : QuestionId} {g h : Bool}
    (heq : i.child g = j.child h) : i = j ∧ g = h := by
  simp only [QuestionId.child, QuestionId.mk.injEq] at heq
  obtain ⟨hc, hq, hs, hrel⟩ := heq
  obtain ⟨hr, hgh⟩ := List.append_inj' hrel (by simp)
  refine ⟨?_, by simpa using hgh⟩
  cases i; cases j
  simp_all

/-- **Proposition 5.4, restated for proposals.** If two child proposals carry
    the same occurrence identifier, their parents' identifiers agree and so do
    the hands that reached them. -/
theorem childProposal_inj {id0 id0' : QuestionId} {seed seed' : History}
    {v v' : Word} {g h : Bool}
    (heq : (childProposal id0 seed v g).id = (childProposal id0' seed' v' h).id) :
    (proposal id0 seed v).id = (proposal id0' seed' v').id ∧ g = h := by
  rw [childProposal_id, childProposal_id] at heq
  exact QuestionId.child_inj heq

/-! ## Definition 5.6 — Sibling pair and provisional alternative -/

/-- **Definition 5.6.** The opposite hand, `L̄ = R`, `R̄ = L` — Definition 3.9's
    `Word.bar`, read on one letter rather than a whole word. -/
abbrev oppositeHand (g : Bool) : Bool := !g

@[simp] theorem oppositeHand_invol (g : Bool) : oppositeHand (oppositeHand g) = g := by
  cases g <;> rfl

theorem oppositeHand_ne (g : Bool) : oppositeHand g ≠ g := by cases g <;> decide

/-- **Definition 5.6.** The sibling pair of a parent: its two proposals,
    neither yet called selected or refused. That distinction belongs to a
    later committed lineage and is not written here. -/
def siblingPair (id0 : QuestionId) (seed : History) (v : Word) :
    ProposalRecord × ProposalRecord :=
  (childProposal id0 seed v false, childProposal id0 seed v true)

/-- **Definition 5.6.** The sibling alternative of a proposal reached by hand
    `g`: same parent, the opposite hand. -/
def siblingAlt (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    ProposalRecord :=
  childProposal id0 seed v (oppositeHand g)

/-- The sibling alternative of the sibling alternative is the original hand's
    proposal: `Word.bar` is an involution, transported through `childProposal`. -/
@[simp] theorem siblingAlt_siblingAlt (id0 : QuestionId) (seed : History) (v : Word)
    (g : Bool) :
    siblingAlt id0 seed v (oppositeHand g) = childProposal id0 seed v g := by
  simp [siblingAlt]

/-! ## Proposition 5.7 — Proposal covariance under a common prefix -/

/-- **Support for 5.7.** Transporting a seed occurrence by a common prefix `u`:
    the retained word gains `u` on the left, exactly Definition 3.3's "also
    prefixes the corresponding world words". The starting frame is untouched;
    only the word grows, so the *reached* frame genuinely moves — `Z_u` moves
    the whole configuration's reference point, it does not relabel in place. -/
def transportSeed (u : Word) (seed : History) : History :=
  ⟨seed.start, u ++ seed.word⟩

/-- **Support for 5.7.** Transporting a proposal by `u`: re-derive it from the
    transported seed, at the same relative word. The occurrence identifier and
    relative word are untouched — they are local data — while `fullWord`,
    `fullMatrix` and `frame` move with the seed. -/
def transportProposal (u : Word) (id0 : QuestionId) (seed : History) (v : Word) :
    ProposalRecord :=
  proposal id0 (transportSeed u seed) v

/-- Transport commutes with child generation definitionally: both sides are
    `proposal id0 (transportSeed u seed) (v ++ [g])`. -/
theorem transportProposal_child (u : Word) (id0 : QuestionId) (seed : History)
    (v : Word) (g : Bool) :
    transportProposal u id0 seed (v ++ [g]) =
      childProposal id0 (transportSeed u seed) v g := rfl

/-- Transporting a proposal's world matrix is exactly `Z_u`. -/
theorem transportProposal_fullMatrix (u : Word) (id0 : QuestionId) (seed : History)
    (v : Word) :
    (transportProposal u id0 seed v).fullMatrix = Z u (proposal id0 seed v).fullMatrix := by
  simp [transportProposal, proposal, transportSeed, History.matrix, Z, Word.G_append,
    Mat2.mul_assoc']

/-- **Proposition 5.7.** `P_{j+1}(Z_uS_j) = Z_uP_{j+1}(S_j)`, read at one
    occurrence: transporting a parent by `u` and then taking its child by `g`
    reaches the same world matrix as taking the child first and transporting
    the result. This is Proposition 3.5 — `Z_u(M_xg) = Z_u(M_x)g` — cited, not
    re-derived: the two roles never compete for the same slot, so they
    commute for the reason associativity always does. -/
theorem childProposal_transport_comm (u : Word) (id0 : QuestionId) (seed : History)
    (v : Word) (g : Bool) :
    (transportProposal u id0 seed (v ++ [g])).fullMatrix =
      Z u (childProposal id0 seed v g).fullMatrix := by
  simp [transportProposal, childProposal, proposal, transportSeed, History.matrix, Z,
    Word.G_append, Mat2.mul_assoc']

end Two
end RatioSpace
