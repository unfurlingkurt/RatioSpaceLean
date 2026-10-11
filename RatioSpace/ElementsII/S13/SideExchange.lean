/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S11.Advance
import RatioSpace.ElementsII.S15.Accumulation
/-!
  **§13 — The carrier-level side-exchange action.**

  `Advance.lean`'s §13 scoping note says the proposal-generation halves of
  Theorems 13.2 and 13.3 are provable there, and that assembling the *entire*
  statements "needs the carrier advance rather than the archive advance".
  `Accumulation.lean`'s Theorem 15.5 note is blunter: a `TickCarrier`-level
  side-exchange action "is not built anywhere in this tree, and nothing since
  has supplied it". The same absence is what blocks Theorem 16.2 and
  Corollary 16.3.

  This file supplies it.

  **Why it was not obvious.** The naive side exchange — swap a frame's two
  columns — is not an operation on frames at all. `Contact A B` is
  `A.p * B.q = A.q * B.p + 1`; swapping gives `A.q * B.p = A.p * B.q + 1`, and
  the two together force `1 = -1`. `P` has determinant `-1`, so the exchange is
  **orientation-reversing** and cannot be a frame endomorphism. It acts by
  conjugation instead, and `P² = 1` is what makes that an involution.
-/

namespace RatioSpace
namespace Two
namespace SideExchange

open Mat2 Word

/-! ## The exchange matrix -/

/-- `P`, the hand-exchange matrix. -/
def P : Mat2 := ⟨0, 1, 1, 0⟩

@[simp] theorem P_mul_P : P * P = 1 := by decide

/-- **The exchange reverses orientation**, which is the whole reason it cannot
    act on a frame by swapping its columns: every `Frame` carries `Δ = +1` as a
    field, and no `det = -1` map can preserve that. -/
@[simp] theorem det_P : P.det = -1 := by decide

/-- Conjugation by `P` sends each generator to the other. This is the exchange,
    stated on the one object it genuinely acts on. -/
theorem gen_not (b : Bool) : gen (!b) = P * gen b * P := by
  cases b <;> decide

/-! ## The action on words -/

/-- Flip every hand label in a word. -/
def mirrorWord (w : Word) : Word := w.map not

@[simp] theorem mirrorWord_nil : mirrorWord [] = [] := rfl

@[simp] theorem mirrorWord_cons (b : Bool) (w : Word) :
    mirrorWord (b :: w) = (!b) :: mirrorWord w := rfl

@[simp] theorem mirrorWord_involutive (w : Word) : mirrorWord (mirrorWord w) = w := by
  simp [mirrorWord, List.map_map, Function.comp_def]

@[simp] theorem mirrorWord_length (w : Word) : (mirrorWord w).length = w.length := by
  simp [mirrorWord]

/-- Conjugation by `P` is multiplicative, which is the whole reason the exchange
    survives composition of ticks. -/
theorem ext' {M N : Mat2} (ha : M.a = N.a) (hb : M.b = N.b)
    (hc : M.c = N.c) (hd : M.d = N.d) : M = N := by
  cases M; cases N; simp_all

@[simp] theorem mul_a (M N : Mat2) : (M * N).a = M.a * N.a + M.b * N.c := rfl
@[simp] theorem mul_b (M N : Mat2) : (M * N).b = M.a * N.b + M.b * N.d := rfl
@[simp] theorem mul_c (M N : Mat2) : (M * N).c = M.c * N.a + M.d * N.c := rfl
@[simp] theorem mul_d (M N : Mat2) : (M * N).d = M.c * N.b + M.d * N.d := rfl

theorem conj_mul (M N : Mat2) : (P * M * P) * (P * N * P) = P * (M * N) * P :=
  ext' (by simp [P]; ring) (by simp [P]; ring) (by simp [P]; ring) (by simp [P]; ring)

/-- Conjugating twice returns the matrix, which is `P² = 1` in usable form. -/
@[simp] theorem conj_conj (M : Mat2) : P * (P * M * P) * P = M := by
  apply ext' <;> simp [P]

/-- **The conjugation law.** Mirroring a word conjugates its matrix by `P`. This
    is the exact sense in which side exchange acts on the accumulated transform,
    and it is why the action is available at the carrier at all. -/
theorem G_mirrorWord (w : Word) : G (mirrorWord w) = P * G w * P := by
  induction w with
  | nil => simp [mirrorWord]
  | cons b v ih =>
      rw [mirrorWord_cons, G_cons, ih, gen_not, G_cons, conj_mul]

/-- The exchange is an involution on matrices in the conjugated sense. -/
theorem G_mirrorWord_involutive (w : Word) :
    G (mirrorWord (mirrorWord w)) = G w := by
  simp

/-! ## The action on a frame

    **Correction, 2026-09-12, same day as the first draft.** The first version of
    this file mirrored a `Core`'s `fullWord` with `{ c with ... }` and left
    `fullMatrix`, `addr`, `closure` and `imbalance` untouched. Those are derived
    fields — `Core.ofProposal_closure` states `closure = psi12 fullWord` as
    `rfl` — so that version broke its own invariant. It was incoherent and is
    replaced here.

    The obstruction found at the top of this file also has a resolution. Swapping
    a frame's two columns fails because contact is oriented. **Reciprocating both
    entries and then swapping them succeeds**, because reciprocation reverses the
    determinant a second time and the two reversals cancel:

        Δ(recip B, recip A) = B.q·A.p − B.p·A.q = A.p·B.q − A.q·B.p = Δ(A, B)

    So the exchange *is* an action on frames, just not the naive one. -/

/-- `p:q ↦ q:p`. Reciprocation, the reflection Elements I names on `IPres`
    (`Composition.lean`'s `IPres.inv`), here on a bare presentation. -/
def recip (A : Pres) : Pres :=
  ⟨A.q, A.p, by intro h; exact A.ne_zero ⟨h.2, h.1⟩⟩

@[simp] theorem recip_p (A : Pres) : (recip A).p = A.q := rfl
@[simp] theorem recip_q (A : Pres) : (recip A).q = A.p := rfl

@[simp] theorem recip_involutive (A : Pres) : recip (recip A) = A := rfl

/-- **Side exchange on a frame: reciprocate both entries and swap them.**
    Contact is preserved, so this is a genuine endomorphism of `Frame` where the
    naive column swap was not. -/
def Frame.mirror (F : Frame) : Frame where
  plus := recip F.minus
  minus := recip F.plus
  contact := by
    have h := F.contact
    unfold Contact at h ⊢
    simp only [recip_p, recip_q]
    rw [Nat.mul_comm F.minus.q F.plus.p, Nat.mul_comm F.minus.p F.plus.q]
    exact h

@[simp] theorem Frame.mirror_involutive (F : Frame) : Frame.mirror (Frame.mirror F) = F := by
  cases F; rfl

@[simp] theorem mirrorWord_append (u v : Word) :
    mirrorWord (u ++ v) = mirrorWord u ++ mirrorWord v := by
  simp [mirrorWord]

@[simp] theorem mirrorWord_singleton (g : Bool) : mirrorWord [g] = [!g] := rfl

/-! ## The exchange commutes with the walk, and swaps the two inheritances

    This is the mathematical core of §13. Reciprocating-and-swapping a frame
    turns a left inheritance into a right one: the mediant of the reciprocals is
    the reciprocal of the mediant, so `stepR ∘ mirror = mirror ∘ stepL`. The
    exchange does not merely relabel the hands, it exchanges which inheritance
    the frame *takes*, which is why Corollary 13.4 can say the law has no
    preferred hand. -/

theorem Frame.ext' {F F' : Frame} (hp : F.plus = F'.plus) (hm : F.minus = F'.minus) :
    F = F' := by
  cases F; cases F'; simp_all

/-- The mediant of the reciprocals is the reciprocal of the mediant. -/
@[simp] theorem mid_mirror (F : Frame) : Frame.mid (Frame.mirror F) = recip (Frame.mid F) := by
  cases F with
  | mk plus minus contact =>
      cases plus; cases minus
      simp only [Frame.mid, Pres.mediant, Frame.mirror, recip, Pres.mk.injEq]
      exact ⟨Nat.add_comm _ _, Nat.add_comm _ _⟩

/-- **The exchange swaps the two inheritances.** A right step after the exchange
    is the exchange after a left step. -/
theorem stepR_mirror (F : Frame) :
    Frame.stepR (Frame.mirror F) = Frame.mirror (Frame.stepL F) := by
  apply Frame.ext'
  · rfl
  · change Frame.mid (Frame.mirror F) = recip (Frame.stepL F).plus
    rw [mid_mirror]
    rfl

theorem stepL_mirror (F : Frame) :
    Frame.stepL (Frame.mirror F) = Frame.mirror (Frame.stepR F) := by
  apply Frame.ext'
  · change Frame.mid (Frame.mirror F) = recip (Frame.stepR F).minus
    rw [mid_mirror]
    rfl
  · rfl

/-- Selection is equivariant once the hand is flipped. -/
theorem select_mirror (F : Frame) (b : Bool) :
    Frame.select (Frame.mirror F) (!b) = Frame.mirror (Frame.select F b) := by
  cases b
  · simpa [Frame.select] using stepR_mirror F
  · simpa [Frame.select] using stepL_mirror F

/-- **The walk is equivariant under the exchange.** Mirroring the frame and the
    word and then walking reaches the mirror of where the original walk reached. -/
theorem walk_mirror (F : Frame) (w : Word) :
    Frame.walk (Frame.mirror F) (mirrorWord w) = Frame.mirror (Frame.walk F w) := by
  induction w generalizing F with
  | nil => rfl
  | cons b v ih =>
      change Frame.walk (Frame.select (Frame.mirror F) (!b)) (mirrorWord v) = _
      rw [select_mirror, ih]
      rfl

/-- The address reciprocates. -/
theorem addressed_mirror (F : Frame) (w : Word) :
    Frame.addressed (Frame.mirror F) (mirrorWord w) = recip (Frame.addressed F w) := by
  unfold Frame.addressed
  rw [walk_mirror, mid_mirror]

/-! ## The action on a retained history -/

/-- Side exchange on a seed's own history: its declared frame reciprocates-and-
    swaps, its word mirrors. -/
def History.mirror (H : History) : History :=
  { start := Frame.mirror H.start, word := mirrorWord H.word }

@[simp] theorem History.mirror_start (H : History) :
    (History.mirror H).start = Frame.mirror H.start := rfl

@[simp] theorem History.mirror_word (H : History) :
    (History.mirror H).word = mirrorWord H.word := rfl

@[simp] theorem History.mirror_frame (H : History) :
    (History.mirror H).frame = Frame.mirror H.frame :=
  walk_mirror H.start H.word

@[simp] theorem History.mirror_matrix (H : History) :
    (History.mirror H).matrix = P * H.matrix * P :=
  G_mirrorWord H.word

@[simp] theorem History.mirror_involutive (H : History) :
    History.mirror (History.mirror H) = H := by
  cases H; simp [History.mirror]

/-! ## The exchange negates the winding record -/

@[simp] theorem count_mirrorWord_true (w : Word) :
    (mirrorWord w).count true = w.count false := by
  induction w with
  | nil => rfl
  | cons b v ih => cases b <;> simp [mirrorWord] at ih ⊢ <;> omega

@[simp] theorem count_mirrorWord_false (w : Word) :
    (mirrorWord w).count false = w.count true := by
  induction w with
  | nil => rfl
  | cons b v ih => cases b <;> simp [mirrorWord] at ih ⊢ <;> omega

/-- **The imbalance is odd under the exchange.** `b(mirror w) = −b(w)`: swapping
    the hands swaps the two counts, so the winding record changes sign rather
    than staying put. This is what forces `closure` and `imbalance` to move when
    a core is mirrored. -/
@[simp] theorem bal_mirrorWord (w : Word) : bal (mirrorWord w) = - bal w := by
  unfold bal
  simp only [count_mirrorWord_true, count_mirrorWord_false]
  omega

@[simp] theorem bal_append (u w : Word) : bal (u ++ w) = bal u + bal w := by
  unfold bal
  simp only [List.count_append]
  push_cast
  ring

@[simp] theorem psi12_append (u w : Word) : psi12 (u ++ w) = psi12 u + psi12 w := by
  unfold psi12
  rw [bal_append]
  push_cast
  ring

@[simp] theorem psi12_mirrorWord (w : Word) : psi12 (mirrorWord w) = - psi12 w := by
  unfold psi12
  rw [bal_mirrorWord]
  push_cast
  ring

/-! ## The action on an archived occurrence

    **Second correction, 2026-09-12.** The previous draft of this section said
    "identifiers do not move", borrowing the reading `Advance.lean` gives for
    *prefix* transport. That is false for side exchange, and the reason is in
    `Cavity.lean`: `QuestionId` carries a `rel : Word` field, and
    `proposal` sets `id := { id0 with rel := v }`. **The identifier contains the
    relative word.** Mirroring the word while holding the identifier fixed
    breaks the correspondence between an occurrence and its own name.

    Prefix transport and side exchange differ here precisely because transport
    prepends to the *seed's* word and leaves `rel` alone, while the exchange
    rewrites `rel` itself.

    So identifiers move, the active list moves with them, and
    `active_sub_archive` stops being `rfl` and becomes a proof.

    Every field moves by its own law: the word mirrors, the identifier's `rel`
    mirrors, the matrix conjugates by `P`, the frame reciprocates-and-swaps, the
    address reciprocates, and the two winding records negate. -/

/-- Side exchange on an identifier: the descendant word it carries mirrors. -/
def QuestionId.mirror (i : QuestionId) : QuestionId := { i with rel := mirrorWord i.rel }

@[simp] theorem QuestionId.mirror_involutive (i : QuestionId) :
    QuestionId.mirror (QuestionId.mirror i) = i := by
  cases i; simp [QuestionId.mirror]

@[simp] theorem QuestionId.mirror_comp_self :
    QuestionId.mirror ∘ QuestionId.mirror = id := by
  funext i; simp

def Core.mirror (c : Core) : Core where
  id := QuestionId.mirror c.id
  parent := c.parent.map QuestionId.mirror
  seedId := QuestionId.mirror c.seedId
  hand := c.hand.map not
  seed := History.mirror c.seed
  relWord := mirrorWord c.relWord
  fullWord := mirrorWord c.fullWord
  fullMatrix := P * c.fullMatrix * P
  frame := Frame.mirror c.frame
  addr := recip c.addr
  closure := - c.closure
  imbalance := - c.imbalance
  entry := c.entry
  prov := c.prov

@[simp] theorem Core.mirror_id (c : Core) :
    (Core.mirror c).id = QuestionId.mirror c.id := rfl

/-- **The mirror keeps the invariant the first draft broke.** If a core's stored
    closure is the winding of its stored word, that is still true of its mirror,
    because both sides negate. -/
theorem Core.mirror_closure_coherent (c : Core) (hc : c.closure = psi12 c.fullWord) :
    (Core.mirror c).closure = psi12 (Core.mirror c).fullWord := by
  change - c.closure = psi12 (mirrorWord c.fullWord)
  rw [psi12_mirrorWord, hc]

theorem Core.mirror_imbalance_coherent (c : Core) (hc : c.imbalance = bal c.fullWord) :
    (Core.mirror c).imbalance = bal (Core.mirror c).fullWord := by
  change - c.imbalance = bal (mirrorWord c.fullWord)
  rw [bal_mirrorWord, hc]

@[simp] theorem Core.mirror_involutive (c : Core) : Core.mirror (Core.mirror c) = c := by
  cases c with
  | mk id parent seedId hand seed relWord fullWord fullMatrix frame addr closure imbalance entry
    prov =>
      cases seed
      simp only [Core.mirror, mirrorWord_involutive, Frame.mirror_involutive,
        recip_involutive, neg_neg, Option.map_map, QuestionId.mirror_involutive,
        History.mirror_involutive]
      cases hand <;> simp [QuestionId.mirror_comp_self]

/-! ## Theorem 13.3 at the occurrence

    Taking a child after the exchange, **with the hand flipped**, is the exchange
    of the child. The hand flip is not bookkeeping: `stepR ∘ mirror = mirror ∘
    stepL` above says the exchange genuinely swaps which inheritance is taken, so
    the child on the other side is the one that corresponds. -/

theorem childCore_mirror (c : Core) (g : Bool) (entry : ℕ) (prov : Provenance) :
    childCore (Core.mirror c) (!g) entry prov = Core.mirror (childCore c g entry prov) := by
  cases c with
  | mk id parent seedId hand seed relWord fullWord fullMatrix frame addr closure imbalance e pv =>
      have hfold : mirrorWord relWord ++ [!g] = mirrorWord (relWord ++ [g]) := by simp
      simp only [childCore, childProposal, proposal, Core.ofProposal, Core.mirror,
        QuestionId.mirror, History.mirror_word, History.mirror_frame, History.mirror_matrix,
        Core.mk.injEq, Option.map_some]
      and_intros <;> first
        | trivial
        | rfl
        | (rw [hfold, G_mirrorWord]; exact conj_mul _ _)
        | (rw [hfold]; exact walk_mirror _ _)
        | (rw [hfold]; exact addressed_mirror _ _)
        | (rw [hfold, ← mirrorWord_append]; exact psi12_mirrorWord _)
        | (rw [hfold, ← mirrorWord_append]; exact bal_mirrorWord _)
        | simp

/-! ## The action on the carrier -/

def mirrorArchive (archive : List Core) : List Core := archive.map Core.mirror

/-- Mirroring the archive mirrors every identifier in it. Where the previous
    draft claimed the identifier list was *unchanged*, it is relabelled. -/
@[simp] theorem archIds_mirrorArchive (archive : List Core) :
    archIds (mirrorArchive archive) = (archIds archive).map QuestionId.mirror := by
  simp [archIds, mirrorArchive, List.map_map, Function.comp_def]

/-! ## Theorem 13.3 on the proposal family

    **And here the read has to be named.** The two routes do not give the same
    list. Mirroring flips each hand, so the pair `[(c, L), (c, R)]` comes back as
    `[(c', R), (c', L)]`: the same two proposals in the other order. The families
    agree as families and differ as lists.

    That is not a defect to be smoothed over with a stronger tactic. It is
    Theorem 12.7's content arriving exactly where 12.7 said it would — the tick
    is independent of the order proposals are enumerated in, so an enumeration
    difference is invisible to everything downstream and must not be stated as
    equality. `List.Perm` is the read. -/

theorem QuestionId.mirror_injective {i j : QuestionId}
    (h : QuestionId.mirror i = QuestionId.mirror j) : i = j := by
  have := congrArg QuestionId.mirror h
  simpa using this

theorem mem_active_mirror {i : QuestionId} {active : List QuestionId} :
    QuestionId.mirror i ∈ active.map QuestionId.mirror ↔ i ∈ active := by
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ := List.mem_map.mp h
    exact QuestionId.mirror_injective hji ▸ hj
  · intro h; exact List.mem_map_of_mem h

/-- Filtering after a map is mapping after a filter, when the two predicates
    agree along the map. Stated once here rather than fought with in place. -/
theorem filter_map_comm {α β : Type} (f : α → β) (p : β → Bool) (q : α → Bool)
    (h : ∀ a, p (f a) = q a) (l : List α) :
    (l.map f).filter p = (l.filter q).map f := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, List.filter_cons, h a]
      cases hq : q a <;> simp [ih]

/-- The active occurrences of the mirrored archive are the mirrors of the active
    occurrences: relabelling both sides selects the same cores. -/
theorem filter_mirrorArchive (archive : List Core) (active : List QuestionId) :
    (mirrorArchive archive).filter (fun c => c.id ∈ active.map QuestionId.mirror) =
      (archive.filter (fun c => c.id ∈ active)).map Core.mirror :=
  filter_map_comm Core.mirror _ _
    (fun c => by
      simp only [Core.mirror_id]
      exact decide_eq_decide.mpr mem_active_mirror) archive

/-- **Theorem 13.3, the generation half, at the carrier.** The proposal family of
    the exchanged carrier is the exchange of the proposal family — as a family.
    The two lists are permutations, not equals, because each hand pair comes back
    reversed. -/
theorem proposals_mirror_perm (archive : List Core) (active : List QuestionId) :
    (Advance.proposals (mirrorArchive archive) (active.map QuestionId.mirror)).Perm
      ((Advance.proposals archive active).map (fun p => (Core.mirror p.1, !p.2))) := by
  unfold Advance.proposals
  rw [filter_mirrorArchive]
  induction archive.filter (fun c => c.id ∈ active) with
  | nil => simp
  | cons c l ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      refine List.Perm.append ?_ ih
      exact List.Perm.swap _ _ _


/-! ## Theorem 13.3 on the archive advance -/

/-- Mirroring distributes over the keyed union. The filter's predicate agrees
    along the exchange because identifiers are relabelled on both sides and the
    relabelling is injective. -/
theorem mirrorArchive_keyedUnion (H H' : List Core) :
    mirrorArchive (Advance.keyedUnion H H') =
      Advance.keyedUnion (mirrorArchive H) (mirrorArchive H') := by
  unfold Advance.keyedUnion
  rw [mirrorArchive, List.map_append]
  congr 1
  refine (filter_map_comm Core.mirror _ _ ?_ H').symm
  intro c
  have hiff : (Core.mirror c).id ∈ archIds (mirrorArchive H) ↔ c.id ∈ archIds H := by
    rw [Core.mirror_id, archIds_mirrorArchive]
    exact mem_active_mirror
  simp only [decide_not]
  exact congrArg (! ·) (decide_eq_decide.mpr hiff)

/-- The children of the mirrored proposals are the mirrors of the children.
    `childCore_mirror` lifted through the list. -/
theorem map_childCore_mirror (ps : List (Core × Bool)) (stratum : ℕ) (prov : Provenance) :
    (ps.map (fun p => (Core.mirror p.1, !p.2))).map
        (fun p => childCore p.1 p.2 stratum prov) =
      (ps.map (fun p => childCore p.1 p.2 stratum prov)).map Core.mirror := by
  induction ps with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, ih]
      exact congrArg (· :: _) (childCore_mirror a.1 a.2 stratum prov)

/-- The keyed union respects permutation of the incoming children: the archive
    on the left is untouched, and the filter is pointwise. -/
theorem keyedUnion_perm_right {H L L' : List Core} (h : L.Perm L') :
    (Advance.keyedUnion H L).Perm (Advance.keyedUnion H L') := by
  unfold Advance.keyedUnion
  exact List.Perm.append_left H (List.Perm.filter _ h)

/-- **Theorem 13.3 on the archive advance.** Advancing the exchanged archive
    gives the exchange of the advanced archive, as a family. Still a permutation
    rather than an equality, inherited from the proposal family: the hands come
    back in the other order and nothing downstream can see it. -/
theorem advanceArchive_mirror_perm (archive : List Core) (active : List QuestionId)
    (stratum : ℕ) (prov : Provenance) :
    (Advance.advanceArchive (mirrorArchive archive)
        (active.map QuestionId.mirror) stratum prov).Perm
      (mirrorArchive (Advance.advanceArchive archive active stratum prov)) := by
  unfold Advance.advanceArchive
  rw [mirrorArchive_keyedUnion]
  refine keyedUnion_perm_right ?_
  have h1 := (proposals_mirror_perm archive active).map
    (fun p => childCore p.1 p.2 stratum prov)
  rw [map_childCore_mirror] at h1
  simpa [mirrorArchive] using h1

/-- **The carrier-level side-exchange action.** All six components, which is what
    Theorem 13.3's boxed statement names on its left side and what nothing in
    this tree previously supplied. -/
def TickCarrier.mirror {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) :
    TickCarrier Aux h where
  observer := { X.observer with
    start := Frame.mirror X.observer.start
    word := mirrorWord X.observer.word }
  question := X.question
  tick := X.tick
  active := X.active.map QuestionId.mirror
  archive := mirrorArchive X.archive
  ledger := X.ledger
  active_sub_archive := by
    intro i hi
    rw [archIds_mirrorArchive]
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact List.mem_map_of_mem (X.active_sub_archive j hj)

@[simp] theorem TickCarrier.mirror_tick {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) :
    (TickCarrier.mirror X).tick = X.tick := rfl

@[simp] theorem TickCarrier.mirror_active {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) :
    (TickCarrier.mirror X).active = X.active.map QuestionId.mirror := rfl

/-! ## Theorem 13.3 at the carrier, stated componentwise

    **Deliberately not one structure equality.** The six components do not agree
    under the same read: the archive agrees *up to permutation*, while the tick
    and the ledger agree on the nose. Collapsing that into a single `=` would
    freeze two different relations into one and hide which is which — the error
    this file was corrected for once already.

    The selector's equivariance is a hypothesis and has to be. Definition
    8.1 supplies the support and this file does not get to assume it has
    no preferred hand; `hsel_equiv` is exactly the assumption that it does not,
    and Corollary 13.4 is what makes that assumption reasonable rather than
    free. -/

theorem advanceCarrier_mirror_componentwise {Aux : Type} {h : ℕ}
    (X : TickCarrier Aux h) (hlaw : Advance.Lawful X)
    (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel hsel') (hfresh hfresh')
    (hsel_equiv : select (Advance.proposals (mirrorArchive X.archive)
        ((X.active).map QuestionId.mirror))
      = (select (Advance.proposals X.archive X.active)).map QuestionId.mirror) :
    -- the archive, up to permutation
    ((Advance.advanceCarrier (TickCarrier.mirror X) hlaw select stratum prov Δ
        hsel' hfresh').archive).Perm
      ((TickCarrier.mirror (Advance.advanceCarrier X hlaw select stratum prov Δ
        hsel hfresh)).archive)
    -- the tick, exactly
    ∧ (Advance.advanceCarrier (TickCarrier.mirror X) hlaw select stratum prov Δ
        hsel' hfresh').tick
      = (TickCarrier.mirror (Advance.advanceCarrier X hlaw select stratum prov Δ
        hsel hfresh)).tick
    -- the active set, exactly, given an equivariant selector
    ∧ (Advance.advanceCarrier (TickCarrier.mirror X) hlaw select stratum prov Δ
        hsel' hfresh').active
      = (TickCarrier.mirror (Advance.advanceCarrier X hlaw select stratum prov Δ
        hsel hfresh)).active
    -- the ledger, exactly: the exchange writes nothing
    ∧ (Advance.advanceCarrier (TickCarrier.mirror X) hlaw select stratum prov Δ
        hsel' hfresh').ledger
      = (TickCarrier.mirror (Advance.advanceCarrier X hlaw select stratum prov Δ
        hsel hfresh)).ledger := by
  refine ⟨?_, rfl, ?_, rfl⟩
  · exact advanceArchive_mirror_perm X.archive X.active stratum prov
  · exact hsel_equiv

/-! ## Definition 13.1's other half: the carrier-level prefix transport `Z_u`

    Definition 13.1 declares **two** carrier actions, not one: transport by `Z_u`
    for a common positive prefix, and transport by `P` with `L ↔ R` exchanged.
    Everything above builds the `P` half. This builds the `Z_u` half, which
    `Accumulation.lean`'s own note records as absent from this tree.

    **The two are not the same shape, and the difference is the thing to keep.**
    `Two/Mediant.lean` says of prefix transport that "the occurrence identifier
    and relative word are untouched — they are local data". That is true of
    `Z_u` and *false* of `P`: the identifier carries `rel`, and the exchange
    rewrites `rel` while a prefix prepends to the seed's word instead. Reading
    the one off the other is precisely the error corrected earlier in this file.

    The visible consequence: `active_sub_archive` is free here, because
    identifiers do not move, where the exchange had to prove it. -/

/-- Prefix transport on one archived occurrence: the seed's word gains the
    prefix, and nothing local moves. -/
def Core.transport (u : Word) (c : Core) : Core :=
  { c with
    seed := transportSeed u c.seed
    fullWord := u ++ c.fullWord
    fullMatrix := Z u c.fullMatrix
    frame := Frame.walk (transportSeed u c.seed).frame c.relWord
    addr := Frame.addressed (transportSeed u c.seed).frame c.relWord
    closure := psi12 u + c.closure
    imbalance := bal u + c.imbalance }

/-- **The identifier is inert under prefix transport**, in exact contrast with
    the exchange, where it moves. -/
@[simp] theorem Core.transport_id (u : Word) (c : Core) :
    (Core.transport u c).id = c.id := rfl

@[simp] theorem Core.transport_relWord (u : Word) (c : Core) :
    (Core.transport u c).relWord = c.relWord := rfl

/-- **A core's stored frame is only guaranteed to be the walk its own seed and
    relative word name when the core was built coherently**, by `Core.ofProposal`.
    It is not a field law, so the identity below has to ask for it.

    This is the same shape as `Core.mirror_closure_coherent`: a derived field
    moves by a law, and a law that recomputes rather than transforms needs the
    stored value to have agreed in the first place. Unlike `fullMatrix`, this one
    cannot be routed through the stored value — the transported frame is the walk
    from the *seed's start* with the prefix prepended, which is not a function of
    the old frame alone. -/
def Core.FrameCoherent (c : Core) : Prop :=
  c.frame = Frame.walk c.seed.frame c.relWord ∧
    c.addr = Frame.addressed c.seed.frame c.relWord

/-- **The transported closure and imbalance move by their own laws**, so the
    invariants survive exactly as they do under the exchange. Prepending `u`
    shifts the winding record by `u`'s own winding; it does not leave it alone,
    which is what a `{ c with ... }` that touched only `fullWord` would have
    claimed. -/
theorem Core.transport_closure_coherent (u : Word) (c : Core)
    (hc : c.closure = psi12 c.fullWord) :
    (Core.transport u c).closure = psi12 (Core.transport u c).fullWord := by
  change psi12 u + c.closure = psi12 (u ++ c.fullWord)
  rw [psi12_append, hc]

theorem Core.transport_imbalance_coherent (u : Word) (c : Core)
    (hc : c.imbalance = bal c.fullWord) :
    (Core.transport u c).imbalance = bal (Core.transport u c).fullWord := by
  change bal u + c.imbalance = bal (u ++ c.fullWord)
  rw [bal_append, hc]

theorem Core.transport_nil (c : Core) (hc : Core.FrameCoherent c) :
    Core.transport [] c = c := by
  cases c with
  | mk id parent seedId hand seed relWord fullWord fullMatrix frame addr cl imb e pv =>
      cases seed
      obtain ⟨hf, ha⟩ := hc
      simp only [Core.transport, transportSeed, List.nil_append, Core.mk.injEq]
      and_intros <;> first
        | rfl
        | simp [Z]
        | exact hf.symm
        | exact ha.symm

def transportArchive (u : Word) (archive : List Core) : List Core :=
  archive.map (Core.transport u)

@[simp] theorem archIds_transportArchive (u : Word) (archive : List Core) :
    archIds (transportArchive u archive) = archIds archive := by
  simp [archIds, transportArchive, List.map_map, Function.comp_def]

/-- **Definition 13.1, the `Z_u` half, at the carrier.** All six components, and
    `active_sub_archive` comes for free because identifiers are local data that
    a prefix does not touch. -/
def TickCarrier.transport {Aux : Type} {h : ℕ} (u : Word) (X : TickCarrier Aux h) :
    TickCarrier Aux h where
  observer := { X.observer with word := u ++ X.observer.word }
  question := X.question
  tick := X.tick
  active := X.active
  archive := transportArchive u X.archive
  ledger := X.ledger
  active_sub_archive := by
    intro i hi
    rw [archIds_transportArchive]
    exact X.active_sub_archive i hi

@[simp] theorem TickCarrier.transport_active {Aux : Type} {h : ℕ}
    (u : Word) (X : TickCarrier Aux h) :
    (TickCarrier.transport u X).active = X.active := rfl

@[simp] theorem TickCarrier.transport_ledger {Aux : Type} {h : ℕ}
    (u : Word) (X : TickCarrier Aux h) :
    (TickCarrier.transport u X).ledger = X.ledger := rfl

/-- The empty prefix acts trivially **on a coherently-built archive**, so this is
    a genuine action of words on carriers rather than a family of unrelated maps.
    The hypothesis is the one `Core.transport_nil` needs, asked pointwise. -/
theorem TickCarrier.transport_nil {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hco : ∀ c ∈ X.archive, Core.FrameCoherent c) :
    (TickCarrier.transport [] X).archive = X.archive := by
  change transportArchive [] X.archive = X.archive
  unfold transportArchive
  rw [List.map_congr_left (fun c hc => Core.transport_nil c (hco c hc))]
  exact List.map_id _

/-- Prefix transport preserves lawfulness, as the exchange does. -/
theorem transport_lawful {Aux : Type} {h : ℕ} (u : Word) (X : TickCarrier Aux h)
    (hlaw : Advance.Lawful X) : Advance.Lawful (TickCarrier.transport u X) := hlaw

/-! ## Theorem 13.2 at the occurrence, over the whole core

    `Advance.lean`'s `childCore_transport_fullMatrix` proves this for the
    **matrix field only**, and against a different notion of transported core
    (`{ c with seed := transportSeed u c.seed }`, which leaves every derived
    field at its stored value). This states it for all fourteen fields against
    `Core.transport`, which reconciles the two: on the child, both agree,
    because `Core.ofProposal` recomputes every derived field from the seed
    regardless of what the parent stored. -/

theorem childCore_transport (u : Word) (c : Core) (g : Bool)
    (stratum : ℕ) (prov : Provenance) :
    childCore (Core.transport u c) g stratum prov
      = Core.transport u (childCore c g stratum prov) := by
  cases c with
  | mk id parent seedId hand seed relWord fullWord fullMatrix frame addr cl imb e pv =>
      cases seed
      simp only [childCore, childProposal, proposal, Core.ofProposal, Core.transport,
        transportSeed, History.matrix, History.frame, Core.mk.injEq]
      -- One comprehensive `simp` rather than a `first` chain: an alternative that
      -- makes progress without closing is a success, so `first` commits to it and
      -- the stronger alternative never runs.
      and_intros <;> first
        | rfl
        | simp [List.append_assoc, Word.G_append, Z, Mat2.mul_assoc',
            psi12_append, bal_append]

/-! ## Proposition 13.5, the base-cycle clause

    *"During the base question cycle the observer is fixed, so a proposal
    `y = xg` satisfies `Q_{O,y} = Q_{O,x} g`."*

    The observer being fixed is the whole hypothesis: the encounter is
    `Q MO Mx = M_O⁻¹ M_x`, and a child multiplies `M_x` on the right, which the
    observer's inverse on the left never touches. The second clause of 13.5,
    observer and presented histories advanced by separately supplied `g_O`, `g_P`,
    is `Observer.prop_3_6` and is not restated here. -/

/-- `G` of a one-letter word is that letter's generator. Both sides compute. -/
@[simp] theorem G_singleton (g : Bool) : Word.G [g] = gen g := by
  cases g <;> decide

theorem encounter_child (MO : Mat2) (c : Core) (g : Bool)
    (stratum : ℕ) (prov : Provenance)
    (hw : c.fullWord = c.seed.word ++ c.relWord) :
    Q MO (childCore c g stratum prov).fullMatrix
      = forward (Q MO (Word.G c.fullWord)) (gen g) := by
  simp only [childCore, childProposal, proposal, Core.ofProposal, History.matrix,
    hw, Q, forward, Word.G_append, Mat2.mul_assoc', G_singleton]

/-! ### Which equality, and what the round trip does not say

    **Kurt, 2026-09-12: "two equal things are one frozen thing in the math."**
    The `=` below is Lean's structural equality, which in the settled vocabulary
    of `Logic.lean` is `E_pres`, the finest of the declared reads. Stated bare,
    `mirror (mirror X) = X` reads as *the double exchange leaves nothing*, and
    that is stronger than what is true here.

    What is true is that the **presentation** returns. What is not true is that
    nothing happened: `mirror` writes no event, so the two exchanges leave no
    trace in the ledger and the return is **projected, not lifted** — the same
    distinction Theorem 14 already carries, where a zero phase held in every
    modulus while the matrix never returned.

    `mirror_ledger` is the witness: the exchange is silent on `ℰ_j`. A reader
    holding only the returned carrier cannot tell one exchange-pair from none,
    and that is a property of this action, not of the occurrence's history. -/

/-- **The exchange writes nothing.** This is what makes the round trip below a
    projected return rather than a lifted one. -/
@[simp] theorem TickCarrier.mirror_ledger {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) :
    (TickCarrier.mirror X).ledger = X.ledger := rfl

/-- The archive returns **under `E_pres`** after two exchanges. The action is an
    involution on presentations; it is not a claim that the exchange is
    unrecorded-because-inconsequential, only that it is unrecorded. -/
theorem TickCarrier.mirror_archive_returns_pres {Aux : Type} {h : ℕ}
    (X : TickCarrier Aux h) :
    (TickCarrier.mirror (TickCarrier.mirror X)).archive = X.archive := by
  simp [TickCarrier.mirror, mirrorArchive, List.map_map, Function.comp_def]

@[deprecated TickCarrier.mirror_archive_returns_pres (since := "2026-09-12")]
theorem TickCarrier.mirror_involutive {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) :
    (TickCarrier.mirror (TickCarrier.mirror X)).archive = X.archive :=
  TickCarrier.mirror_archive_returns_pres X

/-- The exchange preserves lawfulness, so it maps `𝔈_𝒬^{<h}` to itself. -/
theorem mirror_lawful {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Advance.Lawful X) : Advance.Lawful (TickCarrier.mirror X) := hlaw

/-! ## Theorem 15.5's side-exchange box, at the carrier, at every tick

    `Accumulation.lean`'s note on Theorem 15.5 records that its side-exchange
    half "stops at the proposal-generation level" because **no `TickCarrier`-level
    `P` action exists in this tree**. That was true when it was written and is no
    longer: `TickCarrier.mirror` is built above.

    So the statement can be lifted from "both hands are proposed at every tick"
    to the advance itself at every tick. No induction is needed — the one-tick
    result holds at each carrier a trace visits, which is what the boxed
    statement quantifies over. -/

theorem trace_mirror_advance_perm {Aux : Type} {h : ℕ}
    (pol : Accumulation.Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Accumulation.Seeded X0) (n : ℕ) (hn : n ≤ h)
    (stratum : ℕ) (prov : Provenance) :
    (Advance.advanceArchive
        (mirrorArchive (Accumulation.iterate pol X0 hX0 n hn).archive)
        (((Accumulation.iterate pol X0 hX0 n hn).active).map QuestionId.mirror)
        stratum prov).Perm
      (mirrorArchive (Advance.advanceArchive
        (Accumulation.iterate pol X0 hX0 n hn).archive
        (Accumulation.iterate pol X0 hX0 n hn).active stratum prov)) :=
  advanceArchive_mirror_perm _ _ _ _

/-! ## Theorem 16.2 — Iterated parity obstruction

    The payoff of the carrier-level action. The book's proof is two sentences:
    *"Theorem 15.5 makes every carrier in the trace side-exchange invariant. In
    particular `S_h = P S_h`."* Then a support fixed setwise by an action with no
    fixed occurrences cannot be a singleton.

    Both hypotheses are the book's own and neither is smuggled: invariance of the
    terminal support, and `P` acting without fixed occurrences on it. The second
    is genuinely needed — `QuestionId.mirror` is *not* fixed-point-free in
    general, since an identifier whose relative word is empty is its own mirror.
    That is exactly why the book states it as a hypothesis. -/

/-- A fixed-point-free involution cannot fix a singleton setwise. The parity
    argument, with nothing about carriers in it. -/
theorem no_singleton_fixed_setwise {α : Type} (σ : α → α)
    (S : List α) (hfree : ∀ a ∈ S, σ a ≠ a)
    (hperm : (S.map σ).Perm S) : S.length ≠ 1 := by
  intro hlen
  match S, hlen with
  | [a], _ =>
      have : σ a = a := by
        have h := hperm.mem_iff (a := σ a)
        have hmem : σ a ∈ [σ a] := by simp
        exact List.mem_singleton.mp (h.mp hmem)
      exact hfree a (by simp) this

/-- **Theorem 16.2.** If the terminal support is invariant under the side
    exchange and the exchange has no fixed occurrence on it, the support is not a
    singleton: `|S_h| ≠ 1`. -/
theorem iterated_parity_obstruction (S : List QuestionId)
    (hfree : ∀ i ∈ S, QuestionId.mirror i ≠ i)
    (hperm : (S.map QuestionId.mirror).Perm S) : S.length ≠ 1 :=
  no_singleton_fixed_setwise QuestionId.mirror S hfree hperm

/-- **Corollary 16.3 — Under a side-equivariant law, uniqueness requires asymmetry or a fixed
    occurrence.** Stated as
    the contrapositive, which is what the book's prose amounts to: if a
    side-symmetric complete input *does* yield a unique answer, then some
    terminal occurrence is fixed by the declared side action. Uniqueness must be
    bought, either with an asymmetry or with a fixed occurrence. -/
theorem no_side_equivariant_singleton (S : List QuestionId)
    (hperm : (S.map QuestionId.mirror).Perm S) (hlen : S.length = 1) :
    ∃ i ∈ S, QuestionId.mirror i = i := by
  by_contra hcon
  push Not at hcon
  exact iterated_parity_obstruction S hcon hperm hlen

/-! ## Theorem 7.8, first step: the occurrence-level side exchange of the local relation

    Elements II Theorem 7.8 begins: for an observer `O` and `y ∈ Dom₊(O)`,
    `λ_{𝖯O}(𝖯y) = Inv(λ_O(y))`. The side exchange of a record carries its
    matrix to `P M P` (`Core.mirror` stores exactly this as `fullMatrix`), so
    `Q_{𝖯O,𝖯y} = P Q_{O,y} P`, the local word is mirrored (`G_mirrorWord` and
    `G_inj`), and the address of the mirrored word is the reciprocal
    (`addressed_mirror` at the empty frame, Proposition 7.11). -/

/-- The adjugate commutes with conjugation by `P`: `inv2 (P M P) = P (inv2 M) P`. -/
theorem inv2_conj (M : Mat2) : inv2 (P * M * P) = P * inv2 M * P := by
  apply ext' <;> simp [P, inv2]

/-- **`Q_{𝖯O,𝖯y} = P Q_{O,y} P`.** Needs no determinant hypothesis. -/
theorem Q_conj (MO Mx : Mat2) : Q (P * MO * P) (P * Mx * P) = P * Q MO Mx * P := by
  rw [Q_def, Q_def, inv2_conj, conj_mul]

/-- The side exchange sends the canonical chart to itself. -/
theorem Frame.mirror_empty : Frame.mirror Frame.empty = Frame.empty := rfl

/-- **The local word is mirrored.** `a_{𝖯y} = \overline{a_y}` for the observer
    `𝖯O`, including that one side decodes exactly when the other does. -/
theorem localWord_side_exchange (MO Mx : Mat2) :
    localWord (P * MO * P) (P * Mx * P) = (localWord MO Mx).map mirrorWord := by
  rw [localWord, localWord, Q_conj]
  cases h : dec (Q MO Mx) with
  | some w =>
      have hG : G w = Q MO Mx := dec_sound h
      rw [← hG, ← G_mirrorWord, dec_G]
      rfl
  | none =>
      cases h' : dec (P * Q MO Mx * P) with
      | none => rfl
      | some v =>
          have hv : G v = P * Q MO Mx * P := dec_sound h'
          have : Q MO Mx = G (mirrorWord v) := by
            rw [G_mirrorWord, hv, conj_conj]
          rw [this, dec_G] at h
          cases h

/-- **Domain exchange.** `𝖯y ∈ Dom₊(𝖯O)` exactly when `y ∈ Dom₊(O)`. -/
theorem domPlus_side_exchange (MO Mx : Mat2) :
    DomPlus (P * MO * P) (P * Mx * P) ↔ DomPlus MO Mx := by
  unfold DomPlus
  rw [mem_Mplus_iff_dec, mem_Mplus_iff_dec, ← localWord, ← localWord,
    localWord_side_exchange]
  cases localWord MO Mx <;> simp

/-- The address of a mirrored word is the reciprocal of the address
    (Proposition 7.11 at the canonical frame, `P F_∅ = F_∅`). -/
theorem r_mirrorWord (w : Word) : Frame.r (mirrorWord w) = recip (Frame.r w) := by
  have h := addressed_mirror Frame.empty w
  rw [Frame.mirror_empty] at h
  exact h

/-- **Elements II Theorem 7.8, first step (occurrence level).** For an observer
    matrix `M_O` and an occurrence matrix `M_y`, the local relation of the
    side-exchanged occurrence for the side-exchanged observer is the reciprocal
    of the original, `λ_{𝖯O}(𝖯y) = Inv(λ_O(y))`, as an equality of `Option`
    (both undefined together). `𝖯` acts on a matrix as `M ↦ P M P`, which is
    the `fullMatrix` of `Core.mirror` (`Core.mirror_fullMatrix`). -/
theorem lambda_side_exchange (MO Mx : Mat2) :
    lambda (P * MO * P) (P * Mx * P) = (lambda MO Mx).map recip := by
  rw [lambda, lambda, localWord_side_exchange]
  cases localWord MO Mx with
  | none => rfl
  | some w => exact congrArg some (r_mirrorWord w)

@[simp] theorem Core.mirror_fullMatrix (c : Core) :
    (Core.mirror c).fullMatrix = P * c.fullMatrix * P := rfl

/-- The same statement for archived occurrences: the mirrored `Core` read from
    the mirrored observer. -/
theorem lambda_core_mirror (MO : Mat2) (c : Core) :
    lambda (P * MO * P) (Core.mirror c).fullMatrix = (lambda MO c.fullMatrix).map recip :=
  lambda_side_exchange MO c.fullMatrix

/-- `recip` on a presentation is `Inv` on the interior presentation it carries. -/
theorem ofPres?_recip (A : Pres) :
    IPres.ofPres? (recip A) = (IPres.ofPres? A).map Inv := by
  unfold IPres.ofPres?
  by_cases h : A.Interior
  · have h' : (recip A).Interior := ⟨h.2, h.1⟩
    simp [h, h']
    rfl
  · have h' : ¬ (recip A).Interior := fun hh => h ⟨hh.2, hh.1⟩
    simp [h, h']

/-- **Definition 7.3 at occurrence level.** `t_O(y,z)` read from matrices: the
    reduced Stern-Brocot depth of the contrast of the two observer-local
    relations, defined when both occurrences are in `Dom₊(O)` and decode to
    interior presentations. -/
def tEndLocal (MO My Mz : Mat2) : Option ℕ :=
  (lambda MO My).bind fun a => (lambda MO Mz).bind fun b =>
    (IPres.ofPres? a).bind fun A => (IPres.ofPres? b).map fun B => tEnd A B

/-- **Elements II Theorem 7.8 (occurrence level).**
    `T_{end,𝖯O}(𝖯y, 𝖯z) = T_{end,O}(y, z)`, with both sides defined together. -/
theorem tEndLocal_side_exchange (MO My Mz : Mat2) :
    tEndLocal (P * MO * P) (P * My * P) (P * Mz * P) = tEndLocal MO My Mz := by
  unfold tEndLocal
  rw [lambda_side_exchange, lambda_side_exchange]
  cases lambda MO My with
  | none => rfl
  | some a =>
    cases lambda MO Mz with
    | none => rfl
    | some b =>
      simp only [Option.map_some, Option.bind_some, ofPres?_recip]
      cases IPres.ofPres? a with
      | none => rfl
      | some A =>
        cases IPres.ofPres? b with
        | none => rfl
        | some B => simp [tEnd_side_invariant]

/-- The same statement for archived occurrences. -/
theorem tEndLocal_core_mirror (MO : Mat2) (c d : Core) :
    tEndLocal (P * MO * P) (Core.mirror c).fullMatrix (Core.mirror d).fullMatrix
      = tEndLocal MO c.fullMatrix d.fullMatrix :=
  tEndLocal_side_exchange MO c.fullMatrix d.fullMatrix

end SideExchange
end Two
end RatioSpace
