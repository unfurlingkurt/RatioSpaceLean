/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S05.Mediant
import RatioSpace.ElementsII.S09.Admission
/-!
  Elements II §10 — Causal sibling-pair records (W/F).

  Definitions 10.1 through 10.9 and Boundary Statement 10.10. This section adds
  no new selector and no new occurrence type: it names two presentations of the
  one exact fact a sibling split already carries — which hand was taken and
  which was not — and proves that naming it does not smuggle in a resolution.

  Two things sharper than the prose, each noted at its theorem:

    * **`W` and `F` are total, the book's restriction to nonempty words is
      recovered as a hypothesis, not built into the type.** `W` and `F` are
      built on `List.dropLast`/`List.getLastD` and `rs`/`shadow` respectively,
      each already primitive in `Walk.lean`. The involutions
      (`W² = id`, `F² = id`) are proved only on nonempty words, matching
      Definition 10.1's own scope, rather than weakened to hold vacuously
      everywhere by an arbitrary default.
    * **Theorem 10.6 needs no fresh matrix lemma.** `Mat2.inv2_mul` (the
      adjugate reverses order under multiplication, unconditionally) plus
      `Mat2.inv2_mul_of_det` (already built for Standard Result 3.1) give the
      cancellation directly: `(M_x s)⁻¹(M_x s̄) = s⁻¹M_x⁻¹M_xs̄ = s⁻¹s̄`, exactly
      the book's "direct cancellation," with no new arithmetic fact required.

  Everything computable. No `sorry`, no `axiom`, no `Classical.choice`.
-/

namespace RatioSpace
namespace Two

open Mat2 Word Frame Pres RatioSpace

/-! ## Definition 10.1 — Terminal sibling involution -/

/-- **Definition 10.1.** `W(ug) = u ḡ`: flip the terminal hand, keep the
    parent prefix. Total by construction (`getLastD` supplies a default on
    `[]`), but the book's identity and involution are only claimed — and only
    proved below — for nonempty words, exactly Definition 10.1's own scope. -/
def W (w : Word) : Word := w.dropLast ++ [bar (w.getLastD false)]

/-- The defining equation, stated the way every proof below needs it: as a
    rewrite on the `u ++ [g]` shape rather than on `dropLast`/`getLastD`. -/
@[simp] theorem W_append (u : Word) (g : Bool) : W (u ++ [g]) = u ++ [bar g] := by
  simp [W]

/-- **Definition 10.1, "it is an involution": `W²(w) = w`.** Stated with the
    book's own hypothesis, `w` nonempty — `W` does not fix `[]`, since flipping
    a hand that is not there instead appends one, and no involution claim was
    ever made about that case. -/
theorem W_involutive {w : Word} (hw : w ≠ []) : W (W w) = w := by
  obtain ⟨u, g, rfl⟩ := (List.eq_nil_or_concat w).resolve_left hw
  simp

/-! ## Definition 10.2 / Proposition 10.3 — Retrospective causal presentation -/

/-- **Definition 10.2.** `F = rs ∘ W ∘ rs`. Built from the definition exactly
    as the book states it, not from Proposition 10.3's closed form — that form
    is a theorem below (`F_cons`), not the definition. -/
def F (w : Word) : Word := rs (W (rs w))

/-- `shadow` is its own inverse: flipping every hand twice restores the word.
    Not in `Walk.lean` because nothing there needed it; §10 is the first
    section to compose `rs` with itself. -/
theorem shadow_shadow (w : Word) : shadow (shadow w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [shadow_cons, ih]

/-- `shadow` commutes with `reverse`, since both act pointwise/positionally
    with no interaction. -/
theorem shadow_reverse (w : Word) : shadow w.reverse = (shadow w).reverse := by
  simp [shadow, List.map_reverse]

/-- **`rs` is an involution**, from the two facts above: reversing twice and
    shadowing twice each cancel, and they do not interfere. -/
theorem rs_rs (w : Word) : rs (rs w) = w := by
  unfold rs
  rw [shadow_reverse, List.reverse_reverse]
  exact shadow_shadow w

/-- **Proposition 10.3, exact form.** `F(w₁w₂⋯wₙ) = w̄₁w₂⋯wₙ`: only the first
    hand changes, the suffix is untouched. The book's proof reduces this to
    two applications of `rs`'s own definition; here it reduces to `rs_snoc`
    (already built for Proposition 3.2) plus `rs_rs`. -/
theorem F_cons (g : Bool) (rest : Word) : F (g :: rest) = bar g :: rest := by
  have hrs : rs (g :: rest) = rs rest ++ [bar g] := by simp [rs, shadow]
  simp [F, hrs, W_append, rs_snoc, rs_rs]

theorem rs_ne_nil {w : Word} (hw : w ≠ []) : rs w ≠ [] := by
  simp only [rs, shadow, ne_eq, List.reverse_eq_nil_iff, List.map_eq_nil_iff]
  exact hw

/-- `F` inherits its involution from `W`'s, conjugated by `rs`'s own. -/
theorem F_involutive {w : Word} (hw : w ≠ []) : F (F w) = w := by
  simp only [F, rs_rs]
  rw [W_involutive (rs_ne_nil hw), rs_rs]

/-! ## Definition 10.4 — Causal sibling-pair record -/

/-- **Definition 10.4's own vocabulary**, no more: `proposed` until a
    singleton terminal lineage commits one child, at which point that child's
    status may become `selected` and its sibling's `refused` relative to that
    lineage; `archival` if no unique lineage is ever committed, with no
    terminal direction retroactively assigned. Four states, none of them a
    resolver — nothing here decides which child a lineage takes. -/
inductive PairStatus where
  | proposed
  | selected
  | refused
  | archival
deriving DecidableEq

/-- **Definition 10.4.** The causal sibling-pair record: the parent's
    identifier, both children's identifiers, the `W`/`F` presentations of the
    hand at which they split, the hand and its opposite, and the pair's own
    status. Exactly the book's eight-tuple, in one structure rather than a
    tuple, so each field is named rather than positional. -/
structure CausalRecord where
  /-- `ι_x`. -/
  parentId : QuestionId
  /-- `ι_{xg}`. -/
  childId : QuestionId
  /-- `ι_{xḡ}`. -/
  siblingId : QuestionId
  /-- `W(w_xg)`. -/
  wField : Word
  /-- `F(w_xg)`. -/
  fField : Word
  /-- `g`. -/
  hand : Bool
  /-- `ḡ`. -/
  oppHand : Bool
  status : PairStatus

/-- **Definition 10.4.** The record for a designated-hand split of the
    occurrence at relative word `v` from `seed`. `w_xg` is `v ++ [g]`, the
    relative word up to and including the split, matching `childProposal`'s
    own reading of "one more relative step." Status defaults to `proposed`,
    the book's own initial value. -/
def causalRecord (id0 : QuestionId) (seed : History) (v : Word) (g : Bool)
    (status : PairStatus := .proposed) : CausalRecord where
  parentId := (proposal id0 seed v).id
  childId := (childProposal id0 seed v g).id
  siblingId := (siblingAlt id0 seed v g).id
  wField := W (v ++ [g])
  fField := F (v ++ [g])
  hand := g
  oppHand := oppositeHand g
  status := status

/-! ## Definition 10.5 — Oriented sibling relation -/

/-- **Definition 10.5.** `A_s = s⁻¹s̄`, the signed sibling relation attached to
    a designated hand `s`. -/
def A (s : Bool) : Mat2 := inv2 (Word.gen s) * Word.gen (oppositeHand s)

/-- The book's explicit value, `A_L = [[1,1],[-1,0]]` (`false` is `L` under
    `Word.gen`'s convention). -/
theorem A_false_eq : A false = ⟨1, 1, -1, 0⟩ := by decide

/-- `A_R = [[0,-1],[1,1]]`. -/
theorem A_true_eq : A true = ⟨0, -1, 1, 1⟩ := by decide

/-- **`A_L = A_R⁻¹`**, read for either hand: `A_s̄ = (A_s)⁻¹`. Checked, not
    derived symbolically — both sides are closed terms once `s` is fixed. -/
theorem A_inv (s : Bool) : A (oppositeHand s) = inv2 (A s) := by
  cases s <;> decide

/-! ## Theorem 10.6 — Prefix-independent sibling relation -/

/-- **Theorem 10.6.** For a parent of matrix `Mx` (determinant one, as every
    accumulated matrix in this tree is), the relative matrix from the
    designated-hand child to its sibling is `A_s`, independent of `Mx`. The
    book's "direct cancellation" is exactly `Mat2.inv2_mul` (order-reversal,
    unconditional) composed with `Mat2.inv2_mul_of_det` (already built for
    Standard Result 3.1) — no new matrix fact needed. -/
theorem sibling_matrix_prefix_indep (Mx : Mat2) (hMx : Mx.det = 1) (s : Bool) :
    Two.Q (Mx * Word.gen s) (Mx * Word.gen (oppositeHand s)) = A s := by
  simp only [Two.Q, A, inv2_mul, Mat2.mul_assoc']
  rw [← Mat2.mul_assoc' (inv2 Mx) Mx (Word.gen (oppositeHand s)),
      inv2_mul_of_det Mx hMx, Mat2.one_mul']

/-- Restated at the proposal level: the relative matrix between a designated
    child and its sibling alternative is `A_s`, for any seed and any relative
    word — the parent's own matrix cancels regardless of how it was reached. -/
theorem childProposal_sibling_matrix (id0 : QuestionId) (seed : History) (v : Word)
    (g : Bool) :
    Two.Q (childProposal id0 seed v g).fullMatrix
      (childProposal id0 seed v (oppositeHand g)).fullMatrix = A g := by
  have hdet : (proposal id0 seed v).fullMatrix.det = 1 := by
    rw [fullMatrix_eq_G_fullWord]; exact det_G _
  have hL : (childProposal id0 seed v g).fullMatrix =
      (proposal id0 seed v).fullMatrix * Word.gen g :=
    childProposal_fullMatrix id0 seed v g
  have hR : (childProposal id0 seed v (oppositeHand g)).fullMatrix =
      (proposal id0 seed v).fullMatrix * Word.gen (oppositeHand g) :=
    childProposal_fullMatrix id0 seed v (oppositeHand g)
  rw [hL, hR]
  exact sibling_matrix_prefix_indep _ hdet g

/-! ## Proposition 10.7 — Unique quarter-turn reception of the sibling relation -/

/-- **Proposition 10.7.** `S·A_L = L`. -/
theorem S_AL : Squarter * A false = L := by decide

/-- **Proposition 10.7.** `S³·A_R = R`. -/
theorem S3_AR : matPow Squarter 3 * A true = R := by decide

/-- **Proposition 10.7.** `J_S(A_L) = {1}`: the quarter turn admits `A_L` at
    phase 1 and no other, using Definition 9.4's own `admittedPhases`. -/
theorem J_S_AL : admittedPhases Squarter 4 (A false) = [(1 : Fin 4)] := by decide

/-- **Proposition 10.7.** `J_S(A_R) = {3}`. -/
theorem J_S_AR : admittedPhases Squarter 4 (A true) = [(3 : Fin 4)] := by decide

/-! ## Corollary 10.8 — Causal pairing is recorded as a reception certificate -/

/-- **Corollary 10.8's real content.** The reception certificate
    (`J_S(A_g)` is always a determined singleton, Proposition 10.7) coexists
    with the two child identifiers staying distinct — the certificate never
    collapses them. `CausalRecord` itself carries no attachment or face
    field at all, the same "witnessed by absence" move as Definition 6.6's
    `support_not_core_property`: nothing in the type could assert a committed
    face even if this theorem failed. -/
theorem causalRecord_children_distinct (id0 : QuestionId) (seed : History) (v : Word)
    (g : Bool) :
    (childProposal id0 seed v g).id ≠ (siblingAlt id0 seed v g).id := by
  simp only [siblingAlt]
  intro h
  rw [childProposal_id, childProposal_id] at h
  exact oppositeHand_ne g (QuestionId.child_inj h).2.symm

/-! ## Proposition 10.9 — Causal annotations advance beside the retained ancestry -/

/-- **Definition 10.9's `σ(g)`**: the signed step a single generator
    contributes to `bal`, i.e. `bal` evaluated on the one-letter word. -/
def sigma (g : Bool) : ℤ := bal [g]

/-- **Proposition 10.9, the imbalance clause.** `b(w_y) = b(w_x) + σ(g)`.
    Word imbalance is additive under concatenation (`bal_append`, already
    built for §8); the child's full word is the parent's with one generator
    appended (`childProposal_fullWord`). -/
theorem childProposal_bal (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    bal (childProposal id0 seed v g).fullWord =
      bal (proposal id0 seed v).fullWord + sigma g := by
  rw [childProposal_fullWord, bal_append]; rfl

/-- **Proposition 10.9, the closure clause.** `κ_cl(y) = κ_cl(x) + ψ₁₂(g) (mod
    12)`. `ψ₁₂` is a homomorphism (`psi12_append`, already built for §8) for
    the same reason `bal` is additive — it is literally `bal` cast into
    `ZMod 12`. -/
theorem childProposal_closure (id0 : QuestionId) (seed : History) (v : Word) (g : Bool) :
    psi12 (childProposal id0 seed v g).fullWord =
      psi12 (proposal id0 seed v).fullWord + psi12 [g] := by
  rw [childProposal_fullWord, psi12_append]

/- **Proposition 10.9, "none replaces..."** The parent's own record
   (`proposal id0 seed v`) is untouched by forming `childProposal`: nothing
   above mutates it, only reads it, so the parent link and the parent's own
   `w_x`/`M_x`/identifier survive by construction rather than by a separate
   non-interference lemma. -/

/-! ## Boundary Statement 10.10

    No formal content — a summary sentence naming the six-stage pipeline
    Sections 0 through 10 have now typed, and a forward pointer to Section 11's
    one-tick map. Nothing to state or prove here that isn't already true of
    the pieces cited: tagged proposal (§4), observer localization (§3), exact
    admission (§9), endpoint-contrast star (§7), exact global support (§8),
    lossless causal record (§10, this file). -/

end Two
end RatioSpace
