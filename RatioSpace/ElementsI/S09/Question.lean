/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S08.Winding
import RatioSpace.ElementsI.S05.Depth
/-!
  Elements I §9 — Question, cavity, and answer-space.

  Definition 9.1 through Definition 9.4, with the two Elements I types §9 names
  and does not itself construct: the observer of Def 7.1 and the active
  relational family of Def 6.3.

  **Why this section.** Elements II Import 1.6 is titled "Winding,
  closure, received attachment, **and questions**", and its fourth clause reads

      An *Elements I* question has the form 𝒬_τ = (O_τ; C₋,C₊; N; 𝒜_τ; Γ_τ)
      and bounds a finite descendant cavity.

  `bal` and `psi12` build the first two clauses. This file builds the question
  tuple, and Elements II §4, "Finite question cavities", is the extension of
  exactly this interface. An import is built when every symbol in it is built.

  Three things here are sharper than the prose, and each is noted at its result:

    * **Def 9.2's "it is finite" has an exact count, and it needs no subtraction.**
      The cavity of depth `N` carries `|𝒞(F,N)| + 1 = 2^(N+1)` words. Stated that
      way rather than as `2^(N+1) − 1` because ℕ subtraction truncates, and the
      framework's own discipline prefers the relation that holds outright to the
      value that holds conditionally.

    * **Def 9.3's intersection is between two different types, and the resolution
      is forced.** The book writes `S₀ = 𝒞(F,N) ∩ Adm(O,𝒜,Γ)`. But `𝒞(F,N)` is a
      set of *presentations* and `Adm` is a subset of the active family, whose
      members the very next sentence says carry an accumulated matrix `M_r`.
      Taking the intersection literally at the presentation level would discard
      that matrix — the ancestry — and then Def 9.3's own admission predicate
      `Q_{O,r} ∈ ℳ₊` could not be evaluated on the result. So `S₀` retains the
      history and the cavity acts as a filter on it. Keep the relation, not the
      value.

    * **Def 9.4 is a separation, and it has a witness.** "The question determines
      the admissible answer-space; it does not determine which candidate
      survives." The exact form is a question whose `S₀` holds two candidates
      with *distinct* addressed relations, so the map `𝒬 ↦ S₀(𝒬)` cannot be
      read as picking one.

  Everything is computable: `S₀` is a filter that runs, not a set-builder that is
  asserted. `Dom₊` is decidable because `dec` exists. No `sorry`, no `axiom`.
-/

namespace RatioSpace

open Mat2 Word Frame Pres

/-! ## Definition 7.1 — Observer

    A history-bearing receiving state of the same kind as any other substrate
    state. `O = (w_O, M_O, κ_O, η_O)`: the start frame and the word are retained,
    and the matrix `M_O` and the closure record `κ_O` are recovered from start
    and word rather than stored beside them. The history `H_O` and the active
    family are not carried: `Observer` has no field for either, and
    `EncounterRecord.history_not_read_from_the_observer` (`State.lean`) proves
    the history slot is not a function of it.
    So `Observer` is not a lossless compression of a substrate state. -/

/-- **Definition 7.1.** An observer: its declared initial frame, its retained
    generator word, and its declared resolution capacity `η_O`. -/
structure Observer where
  start : Frame
  word : Word
  eta : ℕ
deriving DecidableEq

namespace Observer

/-- `M_O`, the accumulated frame transform, taken relative to the observer's
    declared initial frame — Def 7.1 says the walk is "the ordered frame history
    encoded by `w_O` relative to its declared initial frame", so `start` is part
    of the transform, not incidental to it.

    The start is read, not discarded: `G O.word` alone would give two observers
    with different declared starts and the same word the same matrix, the same
    encounter and the same closure. `SubstrateState.matrix` (`State.lean`) reads
    the start the same way. -/
def matrix (O : Observer) : Mat2 := O.start.toMat2 * G O.word

/-- `κ_O`, the declared closure record of Def 8.4, read against the declared
    start.

    `ClosureState.of` carries the start through, as `matrix` above does;
    `ClosureState.ofWord O.word` would read the start as `∅`. -/
def closure (O : Observer) : ClosureState := ClosureState.of O.start O.word

/-- The observer read as a history. "Observer" and "presented" are directional
    roles in an encounter (Def 7.2), not two different kinds of thing, and this
    is the whole content of that remark. -/
def history (O : Observer) : History := ⟨O.start, O.word⟩

/-- **Not a general fact, and kept honest about it.** `History.matrix` (Def 3.3,
    Elements II's unrooted "world-frame" reading, `Walk.lean`) and
    `Observer.matrix` (Def 7.1, the declared-start reading) agree
    only when the declared start is the canonical frame: `Observer.matrix` does
    not factor through `History.matrix` in general. The declared-start reading
    of a history has its own name (`History.accumulatedMatrix`, below), and
    `History.matrix` is the unrooted field that Def 3.3's transport machinery in
    `ElementsII/S04/Cavity.lean` and `ElementsII/S05/Mediant.lean` needs, which
    this theorem contrasts against. -/
theorem matrix_ne_history_matrix_in_general :
    ∃ O : Observer, O.history.matrix ≠ O.matrix :=
  ⟨⟨Frame.stepL Frame.empty, [], 1⟩, by decide⟩

/-- **The declared-start reading of a history.** `History.accumulatedMatrix`, unlike
    plain `History.matrix` above, agrees with `Observer.matrix` on every
    observer, not merely by example: both sides unfold to
    `start.toMat2 * G word` for the same `start`, `word`, so this is `rfl`, not
    a computation. This is the equality `Candidate.matrix` (`Crystal.lean`)
    relies on when a candidate's history happens to be an observer's own. -/
theorem history_accumulatedMatrix_eq_matrix (O : Observer) :
    O.history.accumulatedMatrix = O.matrix := rfl

end Observer

/-! ## Definition 6.3 — Active relational family

    `𝒜_τ = (r₁,…,r_m)`, the finite ordered collection of relations participating
    in the present update. Ordered and finite, so a `List`; and each member is a
    `History` rather than a `Pres` because Def 9.3 evaluates `M_r` on it. -/

/-- **Definition 6.3.** The active relational family. -/
abbrev ActiveFamily := List History

/-! ### The bridge from Definition 6.3 to Definition 5.6

    `𝒜_τ`'s carrier here is `List History`, richer than the book's raw relation
    list on purpose: Def 9.3 later reads the accumulated matrix off each
    member, which a bare `Pres` cannot carry. But Def 5.6's tension signature
    (`Pres.tensionSignature`, `Depth.lean`) is built over `List IPres`, and
    nothing before this line named the map between the two carriers. This is
    that declaration, not a change to either type.

    The reading is total, not partial: every member's addressed presentation
    is interior. `History.addressed` is a walked mediant, and
    `Frame.walk_mid_pos` (`Frame.lean`) proves any walked mediant has both
    components positive. -/

/-- The addressed reading of a history, typed as the interior presentation it
    always is. -/
def History.addressedI (H : History) : IPres :=
  ⟨H.addressed.p, H.addressed.q,
    (Frame.walk_mid_pos H.start H.word).1, (Frame.walk_mid_pos H.start H.word).2⟩

@[simp] theorem History.addressedI_toPres (H : History) :
    H.addressedI.toPres = H.addressed := rfl

/-- **The bridge itself.** The active family, read as the `List IPres` that
    `Pres.tensionSignature` consumes, with no reduction and no loss: composing
    with `IPres.toPres` recovers `List.map History.addressed` exactly. -/
def ActiveFamily.relations (A : ActiveFamily) : List IPres :=
  A.map History.addressedI

@[simp] theorem ActiveFamily.relations_toPres (A : ActiveFamily) :
    A.relations.map IPres.toPres = A.map History.addressed := by
  simp [ActiveFamily.relations, Function.comp]

/-- **Definition 5.6, read against Definition 6.3's family.** The ordered
    tension signature of a candidate against the active family, through the
    bridge above. -/
def ActiveFamily.tensionSignature (A : ActiveFamily) (r : IPres) : List ℕ :=
  Pres.tensionSignature r A.relations

@[simp] theorem ActiveFamily.tensionSignature_length (A : ActiveFamily) (r : IPres) :
    (A.tensionSignature r).length = A.length := by
  simp [ActiveFamily.tensionSignature, ActiveFamily.relations]

/-! ## Definitions 7.3 and 7.5 — encounter and directional admission -/

/-- **Definition 7.3.** `Q_{O,P} = M_O⁻¹ M_P`, for an observer and a presented
    state — Def 7.2 says `Presented := Observer`, the same type under a
    directional name, so both arguments are `Observer`.

    Both declared start frames enter the computation: `Observer.matrix`, taken
    on both sides, carries `start`. Def 9.3's `Q_{O,r}` for `r` ranging over the
    active family (`List History`) is a related but separate use. A predicate
    evaluating `Q_{O,r}` for `r : History` in an `ActiveFamily` reads
    `r.accumulatedMatrix` (`Walk.lean`), not `r.matrix`: the same
    start-relative reading `Observer.matrix` uses, under its own name so that
    the unrooted use of plain `History.matrix` in `ElementsII/S04/Cavity.lean`
    stays correct. The first such predicate is `Gaps.G1_16.g116_forwardPred`,
    which reads `r.accumulatedMatrix`. -/
def encounter (O P : Observer) : Mat2 := inv2 O.matrix * P.matrix

/-- **Definition 7.5.** Forward admission: `Q_{O,P} ∈ ℳ₊`. A `Bool`, because
    `dec` decides it. -/
def forwardAdmissible (O P : Observer) : Bool :=
  (dec (encounter O P)).isSome

theorem forwardAdmissible_iff (O P : Observer) :
    forwardAdmissible O P = true ↔ encounter O P ∈ Mplus :=
  (mem_Mplus_iff_dec _).symm

/-- `S ∉ ℳ₊`: the matrix `S`, of determinant `1`, is not positive. This is
    not the witness of Def 7.5's closing paragraph (contact states that two
    frames meet unimodularly, admission that one is reachable from the other
    through the permitted directed grammar): `S` is the encounter of no two
    observers (`Gaps.G1_10.g110_S_not_encounter`). The
    witness is `Gaps.G1_10.g110_contact_without_admission`, two observers
    whose encounter has determinant one and neither of which is forward
    admissible to the other. -/
theorem admission_is_not_contact : S ∉ Mplus := by
  rintro ⟨w, hw⟩
  have h := nonneg_G w
  rw [hw] at h
  exact absurd h.2.1 (by decide)

/-! ## Definition 9.1 — Question -/

/-- A single exact admissibility predicate `γ_j(r; O_τ, 𝒜_τ)`. It is a `Bool` by
    Def 9.3's requirement that "every other predicate must likewise be given by
    an exact rule rather than a tolerance or heuristic ranking." A predicate
    valued in anything but a decided answer is not one of these. -/
abbrev Pred := History → Observer → ActiveFamily → Bool

/-- **Definition 9.1.** A question: the complete set of boundaries and
    admissibility conditions that determine which distinctions are jointly
    available for resolution.

    `𝒬_τ = (O_τ; C₋,C₊; N; 𝒜_τ; Γ_τ)`. The Farey adjacency `C₋ ≺ C₊` is not a
    side condition here: `Frame` carries `Contact` in its own type, so a question
    cannot be formed across anchors that do not meet unimodularly. -/
structure Question where
  /-- `O_τ`, the receiving history. -/
  receiver : Observer
  /-- `F = (C₊, C₋)`, the Farey-adjacent anchors, positively oriented. -/
  frame : Frame
  /-- `N`, the finite relational resolution depth. -/
  depth : ℕ
  /-- `𝒜_τ`, the finite active relational family. -/
  active : ActiveFamily
  /-- `Γ_τ = (γ₁,…,γ_k)`, the finite ordered family of exact predicates. -/
  preds : List Pred

/-! ## Definition 9.2 — Bounded descendant cavity -/

/-- Every word of length at most `N`. -/
def wordsUpTo (N : ℕ) : List Word := (List.range (N + 1)).flatMap allWords

/-- **Definition 9.2.** `𝒞(F,N) = {r_F(w) : |w| ≤ N}`. -/
def cavity (F : Frame) (N : ℕ) : List Pres := (wordsUpTo N).map (Frame.addressed F)

private theorem length_flatMap_two (l : List Word) :
    (l.flatMap fun w => [w ++ [false], w ++ [true]]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      simp only [List.length_cons, List.length_nil, List.length_cons]
      omega

/-- `|allWords n| = 2^n`. The branching is exactly binary because the grammar has
    exactly two generators. -/
theorem allWords_card : ∀ n : ℕ, (allWords n).length = 2 ^ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((allWords n).flatMap fun w => [w ++ [false], w ++ [true]]).length = 2 ^ (n + 1)
      rw [length_flatMap_two, ih, Nat.pow_succ]
      omega

/-- **Definition 9.2's finiteness, made exact.** Written `+ 1 = 2^(N+1)` rather
    than `= 2^(N+1) − 1` because subtraction on ℕ truncates and this identity
    holds outright. -/
theorem wordsUpTo_card : ∀ N : ℕ, (wordsUpTo N).length + 1 = 2 ^ (N + 1) := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih =>
      have hsplit : wordsUpTo (N + 1) = wordsUpTo N ++ allWords (N + 1) := by
        simp [wordsUpTo, List.range_succ, List.flatMap_append]
      have hpow : (2 : ℕ) ^ (N + 1 + 1) = 2 ^ (N + 1) + 2 ^ (N + 1) := by
        rw [Nat.pow_succ]; omega
      rw [hsplit, List.length_append, allWords_card]
      omega

theorem mem_wordsUpTo {N : ℕ} {w : Word} : w ∈ wordsUpTo N ↔ w.length ≤ N := by
  constructor
  · intro h
    simp only [wordsUpTo, List.mem_flatMap, List.mem_range] at h
    obtain ⟨n, hn, hw⟩ := h
    rw [allWords_length n w hw]
    omega
  · intro h
    simp only [wordsUpTo, List.mem_flatMap, List.mem_range]
    exact ⟨w.length, by omega, mem_allWords w⟩

theorem mem_cavity {F : Frame} {N : ℕ} {r : Pres} :
    r ∈ cavity F N ↔ ∃ w : Word, w.length ≤ N ∧ Frame.addressed F w = r := by
  simp only [cavity, List.mem_map]
  constructor
  · rintro ⟨w, hw, hr⟩
    exact ⟨w, mem_wordsUpTo.mp hw, hr⟩
  · rintro ⟨w, hw, hr⟩
    exact ⟨w, mem_wordsUpTo.mpr hw, hr⟩

/-- The cavity is bounded by the resolution depth and by nothing else. Def 9.3's
    closing remark — "the open interval between two rational anchors contains
    infinitely many rational values, but a question cavity is finite" — is this
    count. It counts list entries; that no relation is listed twice, so this is
    also the set count, is `Gaps.G1_15.g115_cavity_nodup`. -/
theorem cavity_card_le (F : Frame) (N : ℕ) : (cavity F N).length + 1 = 2 ^ (N + 1) := by
  rw [cavity, List.length_map]
  exact wordsUpTo_card N

/-! ## Definition 9.3 — Active question cavity -/

/-- **Definition 9.3.** `Adm(O_τ, 𝒜_τ, Γ_τ) = {r ∈ 𝒜_τ : γⱼ(r; O_τ, 𝒜_τ) = 1 ∀ j}`.
    Every predicate is exact, so this is a filter that runs. -/
def Adm (Q : Question) : ActiveFamily :=
  Q.active.filter fun r => Q.preds.all fun γ => γ r Q.receiver Q.active

/-- **Definition 9.3.** `S₀(𝒬_τ) = 𝒞(F,N) ∩ Adm(O_τ, 𝒜_τ, Γ_τ)`.

    The intersection is taken on the active family and the cavity acts as the
    filter, not the other way round: the members must keep their accumulated
    matrices, because Def 9.3's own directional-admission predicate reads
    `Q_{O,r} = M_O⁻¹M_r` off them. Intersecting at the presentation level would
    strip the ancestry and leave the predicate unevaluable. -/
def S0 (Q : Question) : ActiveFamily :=
  (Adm Q).filter fun r => decide (r.addressed ∈ cavity Q.frame Q.depth)

theorem S0_sublist_Adm (Q : Question) : List.Sublist (S0 Q) (Adm Q) := List.filter_sublist

theorem Adm_sublist_active (Q : Question) : List.Sublist (Adm Q) Q.active := List.filter_sublist

theorem S0_sublist_active (Q : Question) : List.Sublist (S0 Q) Q.active :=
  (S0_sublist_Adm Q).trans (Adm_sublist_active Q)

/-- Membership in the active question cavity, spelled out. Three conditions:
    the candidate is in the declared active family, it passes every predicate in
    `Γ_τ`, and its relation is reachable from the frame within the declared
    resolution depth. -/
theorem mem_S0 {Q : Question} {r : History} :
    r ∈ S0 Q ↔
      r ∈ Q.active ∧
      (∀ γ ∈ Q.preds, γ r Q.receiver Q.active = true) ∧
      (∃ w : Word, w.length ≤ Q.depth ∧ Frame.addressed Q.frame w = r.addressed) := by
  simp only [S0, Adm, List.mem_filter, decide_eq_true_eq, List.all_eq_true, mem_cavity]
  tauto

/-- The answer-space is finite, and bounded twice over: by the declared active
    context and by the resolution depth. -/
theorem S0_length_le_active (Q : Question) : (S0 Q).length ≤ Q.active.length :=
  (S0_sublist_active Q).length_le

/-! ## Definition 9.4 — The question bounds the answer-space, and resolution selects within it -/

/-- A question with no predicates at all, at depth 1, whose active family is the
    two children of the canonical frame. The receiver sits at the empty word. -/
def twoChildren : Question where
  receiver := ⟨Frame.empty, [], 1⟩
  frame := Frame.empty
  depth := 1
  active := [⟨Frame.empty, [false]⟩, ⟨Frame.empty, [true]⟩]
  preds := []

/-- **Definition 9.4, as a separation rather than a caution.** The question forms
    a cavity in which an answer can become determinate; it does not manufacture
    the answer. Here both children survive `S₀` and they address *different*
    relations, so `𝒬 ↦ S₀(𝒬)` cannot be read as selecting one. Whatever picks a
    survivor is the later resolution dynamics, and it is not this map. -/
theorem question_does_not_force :
    S0 twoChildren = twoChildren.active ∧
    (S0 twoChildren).length = 2 ∧
    Frame.addressed Frame.empty [false] ≠ Frame.addressed Frame.empty [true] := by
  refine ⟨by decide, by decide, by decide⟩

/-- And the bound is not vacuous in the other direction: raising the resolution
    depth cannot rescue a candidate that the active family never declared. The
    cavity at depth 3 holds fifteen relations; `S₀` still holds two, because
    `𝒜_τ` has two members. "All-to-all composition means all-to-all over this
    declared family" (Def 6.3), and this is that sentence with a number in it. -/
theorem depth_does_not_widen_the_family :
    (cavity Frame.empty 3).length = 15 ∧
    (S0 { twoChildren with depth := 3 }).length = 2 := by
  constructor
  · decide
  · decide

/-! ### Def 9.4, sharpened: the survivors need not even differ as relations -/

/-- Two histories at the **same address** with different ancestry. One arrives at
    the left child by taking the step; the other simply starts there, carrying no
    word. `History` records `start` as well as `word`, so the relation projection
    `π_r : H ↦ H.addressed` is already non-injective in *Elements I*. -/
def sameRelationTwice : Question where
  receiver := ⟨Frame.empty, [], 1⟩
  frame := Frame.empty
  depth := 1
  active := [⟨Frame.empty, [false]⟩, ⟨Frame.walk Frame.empty [false], []⟩]
  preds := []

/-- **Definition 9.4, with the witness the book's own sentence needs.**

    `question_does_not_force` above puts two survivors in `S₀` addressing `1:2`
    and `2:1`, and a reader may fairly shrug: of course a question does not choose
    between two *different* relations. This is the case that answers them. Both
    survivors carry the **same** addressed relation and differ only in the history
    that produced it, so `𝒬 ↦ S₀(𝒬)` fails to select even when the relation layer
    cannot tell its options apart.

    This is Elements II Corollary 6.10 — support comparison counts occurrences by stable
    identifier — one
    book early and machine-checked rather than declared, and it is what makes
    Elements II Theorem 17.5's *unresolved-multiple* branch non-vacuous: several
    occurrences really can occupy one relation fiber.

    Freeness does not rescue it. `History.frame_inj` restores injectivity only
    from a **fixed** start frame, which is exactly the book's own "positive
    decoding restores injectivity" on its restricted domain. The start frame is a
    field, so the multiplicity is native to Elements I rather than imported. -/
theorem question_does_not_force_same_relation :
    S0 sameRelationTwice = sameRelationTwice.active ∧
    (S0 sameRelationTwice).length = 2 ∧
    (⟨Frame.empty, [false]⟩ : History) ≠ ⟨Frame.walk Frame.empty [false], []⟩ ∧
    History.addressed ⟨Frame.empty, [false]⟩
      = History.addressed ⟨Frame.walk Frame.empty [false], []⟩ := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The relation projection is not injective, stated on its own. Two distinct
    histories, one address. Nothing about the cavity is involved. -/
theorem addressed_not_injective :
    ∃ H K : History, H ≠ K ∧ H.addressed = K.addressed :=
  ⟨⟨Frame.empty, [false]⟩, ⟨Frame.walk Frame.empty [false], []⟩,
   by decide, by decide⟩

end RatioSpace
