/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S09.Question
/-!
  Elements I §6 — State, active context, and the refusal to define an object.

  §6.3 (the active relational family) was built in `Question.lean`, because
  Def 9.3 evaluates it. This file holds the rest.

  **Def 6.1 says more than it knows, and less than it says.** The book's reason
  for making the frame the minimal state is that a scalar ratio does not carry
  "the lawful mediant continuation available between its boundaries", which reads
  as though the frame held information the ratio does not. It does not. The
  mediant map is *injective*: a reduced ratio determines its frame uniquely, so
  the two carry exactly the same information. What the frame carries and the
  ratio does not is the continuation *presented*, which is a claim about type
  rather than about content — and that is the stronger and more defensible
  version of the same sentence.

  Found by enumeration first: 231 frames with entries under 14 have 231 distinct
  mediants, no collisions, and no non-reduced pair is any frame's mediant.
-/

namespace RatioSpace
namespace Frame

/-! ## Definition 6.1 — Minimal local substrate state -/

/-- The contact relation, rearranged into the form the uniqueness argument uses.
    `p₊ · q = q₊ · p + 1`, where `(p,q)` is the mediant. Pure `ring` from
    `Contact`, with no subtraction anywhere, which is why it is stated this way
    rather than as a determinant. -/
theorem plus_mid_contact (F : Frame) :
    F.plus.p * F.mid.q = F.plus.q * F.mid.p + 1 := by
  have h : F.plus.p * F.minus.q = F.plus.q * F.minus.p + 1 := F.contact
  change F.plus.p * (F.plus.q + F.minus.q) = F.plus.q * (F.plus.p + F.minus.p) + 1
  calc F.plus.p * (F.plus.q + F.minus.q)
      = F.plus.p * F.plus.q + F.plus.p * F.minus.q := by ring
    _ = F.plus.p * F.plus.q + (F.plus.q * F.minus.p + 1) := by rw [h]
    _ = F.plus.q * (F.plus.p + F.minus.p) + 1 := by ring

/-- A frame's mediant is never `0:0`, so the denominators below are real. -/
theorem mid_p_pos_or_q_pos (F : Frame) : 0 < F.mid.p ∨ 0 < F.mid.q := by
  rcases Nat.eq_zero_or_pos F.mid.p with hp | hp
  · right
    have h := plus_mid_contact F
    rcases Nat.eq_zero_or_pos F.mid.q with hq | hq
    · rw [hp, hq] at h; simp at h
    · exact hq
  · exact Or.inl hp

/-- The uniqueness argument, with the larger numerator named. Applied twice, once
    each way round, which is cheaper than a `wlog`. -/
private theorem mid_inj_aux {a b a' b' c c' p q : ℕ}
    (e1 : a * q = b * p + 1) (e2 : a' * q = b' * p + 1)
    (hp : a + c = p) (hp' : a' + c' = p) (hle : a' ≤ a) : a = a' ∧ b = b' := by
  have hppos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · exfalso
      have ha0 : a = 0 := by omega
      rw [ha0, h0] at e1; simp at e1
    · exact h0
  -- `p` and `q` are coprime because `a q − b p = 1`
  have hcop : Nat.Coprime p q := by
    have hg1 : Nat.gcd p q ∣ b * p := Dvd.dvd.mul_left (Nat.gcd_dvd_left p q) b
    have hg2 : Nat.gcd p q ∣ a * q := Dvd.dvd.mul_left (Nat.gcd_dvd_right p q) a
    -- `gcd ∣ a q = b p + 1` and `gcd ∣ b p`, so `gcd ∣ 1`. Stated additively
    -- rather than with `a q − b p`, so no subtraction enters the argument.
    have hg2' : Nat.gcd p q ∣ b * p + 1 := e1 ▸ hg2
    exact Nat.dvd_one.mp ((Nat.dvd_add_right hg1).mp hg2')
  -- `b' ≤ b` follows from `a' ≤ a`, so both differences live in `ℕ`
  have hble : b' ≤ b := by
    by_contra hcon
    have : b < b' := by omega
    have : a * q < a' * q := by
      have : b * p + 1 < b' * p + 1 := by
        have := Nat.mul_lt_mul_of_lt_of_le this (le_refl p) hppos
        omega
      omega
    have : a < a' := by
      by_contra hc2
      have : a' ≤ a := by omega
      exact absurd (Nat.mul_le_mul_right q this) (by omega)
    omega
  -- `(a − a') q = (b − b') p`
  have hdiff : (a - a') * q = (b - b') * p := by
    rw [Nat.sub_mul, Nat.sub_mul]; omega
  have hpd : p ∣ (a - a') * q := ⟨b - b', by rw [hdiff, Nat.mul_comm]⟩
  have hdvd : p ∣ (a - a') := hcop.dvd_of_dvd_mul_right hpd
  -- and `a − a' ≤ p`, so it is `0` or `p`; `p` forces `a' = 0`, which `e2` forbids
  have hbound : a - a' ≤ p := by omega
  have hzero : a - a' = 0 := by
    rcases hdvd with ⟨k, hk⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk, hk0, Nat.mul_zero]
    · exfalso
      have : p ≤ a - a' := by rw [hk]; exact Nat.le_mul_of_pos_right p hk0
      have hap : a - a' = p := by omega
      have ha'0 : a' = 0 := by omega
      rw [ha'0, Nat.zero_mul] at e2
      omega
  have haa : a = a' := by omega
  refine ⟨haa, ?_⟩
  have : (b - b') * p = 0 := by rw [← hdiff, haa]; simp
  rcases Nat.mul_eq_zero.mp this with h | h
  · omega
  · omega

/-- **Definition 6.1, as the theorem the book's sentence needs.**

    The mediant determines the frame. Two frames with the same addressed relation
    are the same frame, so the frame is not extra data beside the ratio; it is
    the same data in a form that presents its own continuation.

    This is the Stern-Brocot / Farey neighbour uniqueness theorem, **standard**
    and borrowed. What is new here is only its use: it turns Def 6.1's "not an
    isolated scalar ratio" from a claim about information into a claim about
    type, which is the version that survives contact with the arithmetic. -/
theorem mid_inj {F G : Frame} (h : F.mid = G.mid) : F = G := by
  have e1 := plus_mid_contact F
  have e2 := plus_mid_contact G
  rw [h] at e1
  have hp : F.plus.p + F.minus.p = G.mid.p := congrArg Pres.p h
  have hp' : G.plus.p + G.minus.p = G.mid.p := rfl
  obtain ⟨ha, hb⟩ :=
    if hle : G.plus.p ≤ F.plus.p then
      mid_inj_aux e1 e2 hp hp' hle
    else by
      have hle' : F.plus.p ≤ G.plus.p := by omega
      obtain ⟨x, y⟩ := mid_inj_aux e2 e1 hp' hp hle'
      exact ⟨x.symm, y.symm⟩
  have hq : F.plus.q + F.minus.q = G.mid.q := congrArg Pres.q h
  have hcp : F.minus.p = G.minus.p := by omega
  have hcq : F.minus.q = G.minus.q := by
    have : G.plus.q + G.minus.q = G.mid.q := rfl
    omega
  obtain ⟨⟨_, _, _⟩, ⟨_, _, _⟩, _⟩ := F
  obtain ⟨⟨_, _, _⟩, ⟨_, _, _⟩, _⟩ := G
  simp_all

/-- The origin-side companion of `Frame.walk_inj`. That theorem recovers the
    *word* from the endpoint; this one recovers the *origin*, so the pair
    `(origin, word)` is jointly recoverable from the frame it walks to. Needed by
    `SubstrateState.toComplete_inj` below, which is Def 6.2's own losslessness
    condition. Constructive, by `select_inj`; no decoder is run. -/
theorem walk_left_inj {F K : Frame} {w : Word} (h : walk F w = walk K w) :
    F = K := by
  induction w generalizing F K with
  | nil => simpa [walk] using h
  | cons b w ih =>
      have h' : walk (select F b) w = walk (select K b) w := by
        simpa [walk] using h
      exact (select_inj (ih h')).2

/-! ### The decoder finding 3 of Tali's 2026-08-26 12:38 review names

    `toComplete_inj` above is injectivity: agreeing on all seven slots forces
    agreeing on the four stored ones. It names no way back from a
    `CompleteState` to the `SubstrateState` it came from, and no statement of
    what a `CompleteState` must satisfy to be reachable at all. Both are built
    here, from the frame and the word alone — the two fields the compression
    already keeps, so no new data is smuggled in to make it work.

    `unselect` inverts `select` one step, checked rather than assumed: the two
    ordering guards make the natural-number subtraction underneath exact, so
    `unselect_some` holds for every input, not only the ones a real walk
    produces. That is what lets `unwalk` characterize the image rather than
    merely decode the cases it was built to expect. -/

/-- **The computable inverse of `select`, one step.** `right = true` undoes
    `stepR`, `right = false` undoes `stepL`. Total, and honest about failure:
    an input that is not genuinely the image of a `select` step fails one of
    the guards and returns `none` rather than a wrong `Frame`. -/
def unselect (F : Frame) : Bool → Option Frame
  | true =>
      if _hle : F.plus.p ≤ F.minus.p ∧ F.plus.q ≤ F.minus.q then
        if hnz : ¬(F.minus.p - F.plus.p = 0 ∧ F.minus.q - F.plus.q = 0) then
          let minus' : Pres := ⟨F.minus.p - F.plus.p, F.minus.q - F.plus.q, hnz⟩
          if hc : Contact F.plus minus' then some ⟨F.plus, minus', hc⟩ else none
        else none
      else none
  | false =>
      if _hle : F.minus.p ≤ F.plus.p ∧ F.minus.q ≤ F.plus.q then
        if hnz : ¬(F.plus.p - F.minus.p = 0 ∧ F.plus.q - F.minus.q = 0) then
          let plus' : Pres := ⟨F.plus.p - F.minus.p, F.plus.q - F.minus.q, hnz⟩
          if hc : Contact plus' F.minus then some ⟨plus', F.minus, hc⟩ else none
        else none
      else none

/-- **Completeness.** Applied to a genuine step, `unselect` always succeeds and
    always returns the frame the step was taken from. -/
theorem unselect_select (F : Frame) (b : Bool) : unselect (select F b) b = some F := by
  cases b
  · change unselect (stepL F) false = some F
    have hp : (stepL F).plus.p - (stepL F).minus.p = F.plus.p := by
      simp only [stepL, mid, Pres.mediant]; omega
    have hq : (stepL F).plus.q - (stepL F).minus.q = F.plus.q := by
      simp only [stepL, mid, Pres.mediant]; omega
    have hle : (stepL F).minus.p ≤ (stepL F).plus.p ∧ (stepL F).minus.q ≤ (stepL F).plus.q :=
      ⟨by simp only [stepL, mid, Pres.mediant]; omega,
       by simp only [stepL, mid, Pres.mediant]; omega⟩
    have hnz : ¬((stepL F).plus.p - (stepL F).minus.p = 0 ∧
        (stepL F).plus.q - (stepL F).minus.q = 0) := by
      rw [hp, hq]; exact F.plus.ne_zero
    have hc : Contact
        (⟨(stepL F).plus.p - (stepL F).minus.p, (stepL F).plus.q - (stepL F).minus.q, hnz⟩
          : Pres)
        (stepL F).minus := by
      have hplus :
          (⟨(stepL F).plus.p - (stepL F).minus.p, (stepL F).plus.q - (stepL F).minus.q, hnz⟩
            : Pres) = F.plus := Pres.ext' hp hq
      rw [hplus]; exact F.contact
    simp only [unselect]
    rw [dif_pos hle, dif_pos hnz, dif_pos hc]
    congr 1
    apply Frame.ext'
    · exact Pres.ext' hp hq
    · rfl
  · change unselect (stepR F) true = some F
    have hp : (stepR F).minus.p - (stepR F).plus.p = F.minus.p := by
      simp only [stepR, mid, Pres.mediant]; omega
    have hq : (stepR F).minus.q - (stepR F).plus.q = F.minus.q := by
      simp only [stepR, mid, Pres.mediant]; omega
    have hle : (stepR F).plus.p ≤ (stepR F).minus.p ∧ (stepR F).plus.q ≤ (stepR F).minus.q :=
      ⟨by simp only [stepR, mid, Pres.mediant]; omega,
       by simp only [stepR, mid, Pres.mediant]; omega⟩
    have hnz : ¬((stepR F).minus.p - (stepR F).plus.p = 0 ∧
        (stepR F).minus.q - (stepR F).plus.q = 0) := by
      rw [hp, hq]; exact F.minus.ne_zero
    have hc : Contact (stepR F).plus
        (⟨(stepR F).minus.p - (stepR F).plus.p, (stepR F).minus.q - (stepR F).plus.q, hnz⟩
          : Pres) := by
      have hminus :
          (⟨(stepR F).minus.p - (stepR F).plus.p, (stepR F).minus.q - (stepR F).plus.q, hnz⟩
            : Pres) = F.minus := Pres.ext' hp hq
      rw [hminus]; exact F.contact
    simp only [unselect]
    rw [dif_pos hle, dif_pos hnz, dif_pos hc]
    congr 1
    apply Frame.ext'
    · rfl
    · exact Pres.ext' hp hq

/-- **Soundness.** `unselect` never returns a wrong answer: whatever it
    succeeds on, applying `select` with the same bit to the result gives back
    exactly the frame it was called on. This is the half `unselect_select`
    does not give — that theorem starts from a genuine step, this one starts
    from an arbitrary success. -/
theorem unselect_some {F G : Frame} {b : Bool} (h : unselect F b = some G) :
    select G b = F := by
  cases b
  · simp only [unselect] at h
    split_ifs at h with hle hnz
    have hG :
        G = ⟨⟨F.plus.p - F.minus.p, F.plus.q - F.minus.q, hnz⟩, F.minus, by assumption⟩ :=
      (Option.some.inj h).symm
    subst hG
    apply Frame.ext' (F := stepL _)
    · change mid _ = F.plus
      simp only [mid, Pres.mediant]
      exact Pres.ext' (by dsimp only; omega) (by dsimp only; omega)
    · rfl
  · simp only [unselect] at h
    split_ifs at h with hle hnz
    have hG :
        G = ⟨F.plus, ⟨F.minus.p - F.plus.p, F.minus.q - F.plus.q, hnz⟩, by assumption⟩ :=
      (Option.some.inj h).symm
    subst hG
    apply Frame.ext' (F := stepR _)
    · rfl
    · change mid _ = F.minus
      simp only [mid, Pres.mediant]
      exact Pres.ext' (by dsimp only; omega) (by dsimp only; omega)

/-- **The decoder.** Recovers a frame's `word`-many-steps ancestor by peeling
    the word one letter at a time, front first, undoing the matching step of
    `walk`'s own left-to-right fold. `Option`, honestly: given an endpoint and
    a word that did not produce it, this fails rather than guesses. -/
def unwalk : Frame → Word → Option Frame
  | R, [] => some R
  | R, b :: w => (unwalk R w).bind (fun G => unselect G b)

/-- **Completeness of the decoder.** Walk out by `w`, decode by `w`, and the
    origin you started from is exactly what comes back. -/
theorem unwalk_walk (F : Frame) (w : Word) : unwalk (walk F w) w = some F := by
  induction w generalizing F with
  | nil => rfl
  | cons b w ih =>
      change (unwalk (walk (select F b) w) w).bind (fun G => unselect G b) = some F
      rw [ih (select F b)]
      exact unselect_select F b

/-- **Soundness of the decoder.** Whatever `unwalk` succeeds on, walking the
    answer back out by the same word reproduces exactly the frame it was
    asked to decode — so a `decode` failure is never a false negative dressed
    as one, and a `decode` success is never a wrong answer. Together with
    `unwalk_walk` this makes `unwalk R w = some F ↔ walk F w = R`: `unwalk` on
    a fixed word is a genuine inverse of `walk _ w`, not merely a best guess. -/
theorem unwalk_some {R F : Frame} {w : Word} (h : unwalk R w = some F) :
    walk F w = R := by
  induction w generalizing R F with
  | nil => cases h; rfl
  | cons b w ih =>
      simp only [unwalk, Option.bind_eq_some_iff] at h
      obtain ⟨G, hG, hF⟩ := h
      change walk (select F b) w = R
      rw [unselect_some hF]
      exact ih hG

/-- **Standard Result 3.1, uniqueness half, for every frame.** The addressed
    relation determines the word: `mid_inj` recovers the final frame, `walk_inj`
    the word. -/
theorem addressed_inj (F : Frame) {u v : Word} (h : addressed F u = addressed F v) :
    u = v :=
  walk_inj F (mid_inj h)

/-- **Standard Result 3.1, as the book states it.** For every frame `F`, every
    primitive presentation in the open interval `C₋ ≺ X ≺ C₊` is reached by
    exactly one positive walk. Existence is `exists_addressed_of_between`
    (`Walk.lean`); uniqueness is `addressed_inj`. -/
theorem existsUnique_addressed_of_between (F : Frame) {X : Pres} (hX : Pres.Primitive X)
    (h1 : Pres.Lt F.minus X) (h2 : Pres.Lt X F.plus) :
    ∃! w : Word, addressed F w = X := by
  obtain ⟨w, hw⟩ := exists_addressed_of_between F hX h1 h2
  exact ⟨w, hw, fun v hv => addressed_inj F (hv.trans hw.symm)⟩

end Frame


/-! ## Definition 6.2 — Complete history-bearing state

  `S_τ = (P_τ, F_τ, w_τ, M_τ, κ_τ, 𝒜_τ, H_τ)`. Seven components, and the book
  adds that the tuple is a type declaration: a representation may compress it
  losslessly. It can, and by a lot. Four of the seven are **derived** from the
  declared origin and the retained word, so storing them would be storing the
  same fact twice, which is the shape of error the framework warns about
  everywhere else. -/

/-- **Definition 6.2, the positive-walk specialization.** Only what is not
    derivable is a field. Its image inside the book's seven-slot record is
    `toComplete`'s, which is proper: see `no_substrate_state_reads_nonprimitively`
    below, and `CompleteState` for the uncompressed declaration. -/
structure SubstrateState where
  /-- the declared origin frame -/
  origin : Frame
  /-- `w_τ`, the retained generator word -/
  word : Word
  /-- `𝒜_τ`, the finite active relational family -/
  active : ActiveFamily
  /-- `H_τ`, the append-only exact history -/
  history : List Word
deriving DecidableEq

namespace SubstrateState

/-- `F_τ`, the active ordered frame. -/
def frame (S : SubstrateState) : Frame := Frame.walk S.origin S.word
/-- `P_τ`, the exact current presentation. -/
def presentation (S : SubstrateState) : Pres := S.frame.mid
/-- `M_τ`, the accumulated transform. -/
def matrix (S : SubstrateState) : Mat2 := S.origin.toMat2 * Word.G S.word
/-- `κ_τ`, the closure record of Def 8.4, read against the declared origin.

    **D-14, repaired 2026-08-26.** Was `ClosureState.ofWord S.word`, silently
    reading the origin as `∅` — the same defect D-12 fixed at `Observer.matrix`,
    here at the closure field. Def 8.4 says `κ_τ = c(M_τ)` and Def 6.2/7.1 take
    `M_τ` relative to the declared origin, which `ClosureState.of` now is. -/
def closure (S : SubstrateState) : ClosureState := ClosureState.of S.origin S.word

/-- **The book's own caveat, as a theorem.** "A representation may compress
    losslessly" is true here and the compression is four of seven: the
    presentation, frame, matrix and closure record are functions of the origin
    and the word, so two states agreeing on the stored fields agree on all
    seven. Storing the derived four would let them disagree, which is the only
    way this record can become internally inconsistent. -/
theorem derived_are_determined (S T : SubstrateState)
    (ho : S.origin = T.origin) (hw : S.word = T.word) :
    S.frame = T.frame ∧ S.presentation = T.presentation ∧
    S.matrix = T.matrix ∧ S.closure = T.closure := by
  have hf : S.frame = T.frame := by unfold frame; rw [ho, hw]
  refine ⟨hf, ?_, ?_, ?_⟩
  · unfold presentation; rw [hf]
  · unfold matrix; rw [ho, hw]
  · unfold closure; rw [ho, hw]

/-- And the presentation is not an independent coordinate either: by `mid_inj`
    it determines the frame it came from. -/
theorem presentation_determines_frame (S T : SubstrateState)
    (h : S.presentation = T.presentation) : S.frame = T.frame :=
  Frame.mid_inj h

end SubstrateState


/-! ### Divergence D-09 — the seven slots the book declares, and what the
    four-field record is a specialization of

  `SubstrateState` above is a compression, and the book licenses compression
  *conditionally*: "A representation may compress components only after proving
  that the compression is lossless for the operations being performed." Until
  2026-08-26 this file asserted the compression and never wrote the thing being
  compressed, so `derived_are_determined` proved internal determinism of the
  four-field record rather than losslessness against the seven-slot one.

  Both halves are now here. `CompleteState` is Def 6.2 as declared;
  `toComplete_inj` is the losslessness the book asks for; and
  `nonprimitiveReading` is a consistent complete state **no** `SubstrateState`
  reaches, which is why the four-field record is named a specialization rather
  than a representation of the whole state space.

  Two slots stay type parameters, because the book leaves them open. `κ_τ` is the
  *declared* closure record, not a computed one. `H_τ` "contains any additional
  composition, return, or circulation history required by the update law", which
  is whatever that law needs and not a fixed type.

  The tuple carries no origin slot. The book puts the initial frame in the
  declared convention instead (Def 7.1: "relative to its declared initial
  frame"), so the one worked example it gives is stated here against a
  declared origin, as `WalkConsistentFrom`, rather than smuggled in as an
  eighth field. -/

/-- **Definition 6.2, uncompressed.** All seven slots, as declared. -/
structure CompleteState (K Hist : Type) where
  /-- `P_τ`, the exact current presentation. *Exact*, so not required primitive:
      the book never states `P_τ = F_τ.mid`, and §1's type separation depends on
      the presentation layer retaining nonprimitive multiplicity. -/
  presentation : Pres
  /-- `F_τ`, the active ordered frame. -/
  frame : Frame
  /-- `w_τ`, the retained generator word or equivalent lossless walk record. -/
  word : Word
  /-- `M_τ`, the accumulated unimodular frame transform. -/
  matrix : Mat2
  /-- `κ_τ`, the *declared* closure record. -/
  closure : K
  /-- `𝒜_τ`, the finite ordered active relational family. -/
  active : ActiveFamily
  /-- `H_τ`, the additional history the update law requires. -/
  history : Hist
deriving DecidableEq

namespace CompleteState

/-- **The one relation Def 6.2 gives as its own worked example, not the whole
    of "the consistency relations imposed by its construction."** The book's
    clause reads *"the components of a valid state must satisfy the
    consistency relations imposed by its construction; for example, `M_τ`
    must be the accumulated matrix of the retained walk in the declared frame
    convention"* — construction-relative, with one named example. The second
    conjunct here is that example; the first is `F_τ`'s own analogue, what
    calling `w_τ` a *lossless walk record* means. It states nothing about
    `P_τ`, `κ_τ`, `𝒜_τ` or `H_τ`, and nothing about *Elements II* Def 19.5's
    later "adopted continuation" construction — Thm 19.6 there says
    presentation, frame, word, matrix, closure, active family and history all
    describe one consistent adopted continuation, which is a different,
    richer construction with its own consistency relations, not a completion
    of this one.

    **Repairs finding 1 of Tali's 2026-08-26 12:38 review** (hop 2,
    `DIVERGENCE.md` D-09): the prior name and docstring called this "the
    consistency relations Def 6.2 imposes," full stop, which reads as the
    definitive set when the book's own text is explicitly one worked example
    under a construction-relative clause. Named for the one construction it
    actually checks rather than claiming the completeness the book itself
    does not claim. -/
def WalkConsistentFrom {K Hist : Type} (origin : Frame) (S : CompleteState K Hist) :
    Prop :=
  S.frame = Frame.walk origin S.word ∧
    S.matrix = origin.toMat2 * Word.G S.word

end CompleteState

namespace SubstrateState

/-- The compression, written out: the four stored fields fill all seven slots. -/
def toComplete (S : SubstrateState) : CompleteState ClosureState (List Word) where
  presentation := S.presentation
  frame := S.frame
  word := S.word
  matrix := S.matrix
  closure := S.closure
  active := S.active
  history := S.history

/-- It satisfies `WalkConsistentFrom` by construction, from the origin it
    declares. Both clauses are `rfl`: that is what makes the derived fields
    derived. -/
theorem toComplete_consistent (S : SubstrateState) :
    S.toComplete.WalkConsistentFrom S.origin := ⟨rfl, rfl⟩

/-- **The book's stated condition for compressing at all, discharged.**
    Distinct four-field records give distinct seven-field records, so storing
    four loses nothing the seven slots held. Note what carries the proof: the
    origin is not stored in `CompleteState` either, and is recovered from the
    frame and the word by `Frame.walk_left_inj`.

    With `derived_are_determined` this is the round trip. That theorem: agreeing
    on the stored fields forces agreement on the derived ones. This one: agreeing
    on all seven forces agreement on the stored ones. -/
theorem toComplete_inj {S T : SubstrateState} (h : S.toComplete = T.toComplete) :
    S = T := by
  obtain ⟨o₁, w₁, a₁, hist₁⟩ := S
  obtain ⟨o₂, w₂, a₂, hist₂⟩ := T
  have hw : w₁ = w₂ := congrArg CompleteState.word h
  have ha : a₁ = a₂ := congrArg CompleteState.active h
  have hh : hist₁ = hist₂ := congrArg CompleteState.history h
  have hf : Frame.walk o₁ w₁ = Frame.walk o₂ w₂ := congrArg CompleteState.frame h
  subst hw; subst ha; subst hh
  have ho : o₁ = o₂ := Frame.walk_left_inj hf
  subst ho
  rfl

end SubstrateState

/-! ### D-09 finding 3, the rest of it — a decoder wired to `SubstrateState`,
    and the characterization of its image

  `Frame.unwalk` above recovers an origin from a frame and a word. Finding 3
  asked for three things: "no decoder, no characterization of the valid
  image, no preservation of the operations." The decoder is `Frame.unwalk`,
  and it is checked, not merely invoked: `toSubstrate?` reassembles the
  candidate `SubstrateState` and rejects it unless recompressing reproduces
  every field of the `CompleteState` it started from, so a `some` answer is a
  verified witness and not a guess from two recovered fields alone.

  **The third clause closes below**, after `substrate_presentation_is_the_
  frame_mediant`. The citation two beats ago — "the update law belongs to
  Def 7.1" — was wrong and is corrected here rather than carried forward:
  Def 7.1 is *Observer*, not an update law. What closes below is
  preservation of Def 3.7's elementary refinement event, `(F,w) ↦ (F·g, wg)`,
  built as `Event`/`Event.step` in `Walk.lean`; whether Def 6.2's update law
  means this event or the general state transition is open (E1-20). -/

/-- **The decoder, checked.** Recovers the origin from `S.frame` and `S.word`
    alone, reassembles the candidate `SubstrateState`, and returns it only if
    recompressing gives back exactly `S` — every field, not only the two the
    decoder read. `none` otherwise, honestly: either the frame/word pair has
    no origin (`Frame.unwalk` fails) or the reassembled candidate is not
    consistent with the rest of `S`. -/
def CompleteState.toSubstrate? (S : CompleteState ClosureState (List Word)) :
    Option SubstrateState :=
  match Frame.unwalk S.frame S.word with
  | none => none
  | some origin =>
      if (⟨origin, S.word, S.active, S.history⟩ : SubstrateState).toComplete = S then
        some ⟨origin, S.word, S.active, S.history⟩
      else none

/-- **Soundness.** Whatever the decoder returns decompresses back to exactly
    the `CompleteState` it was asked to decode. No false positive: a `some`
    answer is never a wrong `SubstrateState`. -/
theorem CompleteState.toSubstrate?_some {S : CompleteState ClosureState (List Word)}
    {T : SubstrateState} (h : S.toSubstrate? = some T) : T.toComplete = S := by
  unfold CompleteState.toSubstrate? at h
  split at h
  · cases h
  · split_ifs at h with heq
    · cases h; exact heq

/-- **Completeness, on the genuine image.** Every `SubstrateState`, compressed
    and then decoded, comes back unchanged — the round trip the book's
    "may compress losslessly" licenses. `Frame.unwalk_walk` recovers the
    origin exactly, and the reassembled candidate is `S` itself, so the check
    inside `toSubstrate?` passes by `rfl`. -/
theorem CompleteState.toSubstrate?_toComplete (S : SubstrateState) :
    S.toComplete.toSubstrate? = some S := by
  unfold CompleteState.toSubstrate? SubstrateState.toComplete SubstrateState.frame
  rw [Frame.unwalk_walk]
  simp

/-- **The characterization finding 3 named.** A `CompleteState` is in the
    image of `SubstrateState.toComplete` — is a genuine positive-walk state
    under some declared origin — exactly when the checked decoder succeeds.
    Not "the frame decodes": the full record, since `toSubstrate?` verifies
    every field before returning `some`. -/
theorem CompleteState.toSubstrate?_isSome_iff
    (S : CompleteState ClosureState (List Word)) :
    S.toSubstrate?.isSome ↔ ∃ T : SubstrateState, T.toComplete = S := by
  constructor
  · intro h
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp h
    exact ⟨T, CompleteState.toSubstrate?_some hT⟩
  · rintro ⟨T, rfl⟩
    rw [CompleteState.toSubstrate?_toComplete]
    exact Option.isSome_some

/-- The frame one `stepL` from `F_∅`, whose own mediant is `1:2` — the
    frame `nonprimitiveReading` below declares as its origin, so the witness
    pairs `2:4` with the frame that actually addresses the reduced relation it
    is nonprimitive against. -/
def frameOneTwo : Frame := Frame.walk Frame.empty [false]

example : frameOneTwo.mid = Pres.oneTwo := rfl

/-- **And the compression is not onto, and the witness now survives every
    clause `WalkConsistentFrom` states, not only the ones it happens to
    check.**

    **Repairs finding 2 of Tali's 2026-08-26 12:38 review** (hop 2,
    `DIVERGENCE.md` D-09). The prior witness paired `2:4` with `Frame.empty`,
    whose own addressed mediant is `1:1` — `WalkConsistentFrom` passed only
    because it states nothing about the presentation slot at all, which made
    the properness theorem below pass by a clause it never exercised. This
    one pairs `2:4` with `frameOneTwo`, whose own addressed mediant *is* the
    same reduced relation, `1:2` — same reduced relation as `2:4`,
    nonprimitive presentation, declared as its own origin with the empty
    word, so both `WalkConsistentFrom` clauses still discharge by `rfl`. -/
def nonprimitiveReading : CompleteState ClosureState (List Word) where
  presentation := Pres.twoFour
  frame := frameOneTwo
  word := []
  matrix := frameOneTwo.toMat2
  closure := ClosureState.ofWord []
  active := []
  history := []

theorem nonprimitiveReading_consistent :
    nonprimitiveReading.WalkConsistentFrom frameOneTwo :=
  ⟨rfl, by simp [nonprimitiveReading]⟩

/-- **The locus of D-09, as a theorem.** Every `SubstrateState` presentation is
    the mediant of a walked frame, hence primitive; `2:4` is not. So the
    four-field record's image inside Def 6.2's state space is proper, and the
    right name for it is the positive-walk specialization. The book's `P_τ` slot
    is exact, and §1 spent its whole length establishing that `1:2 ≠ 2:4`. -/
theorem no_substrate_state_reads_nonprimitively (S : SubstrateState) :
    S.toComplete ≠ nonprimitiveReading := by
  intro h
  have hP : S.presentation = Pres.twoFour :=
    congrArg CompleteState.presentation h
  have hprim : Pres.Primitive S.presentation :=
    Frame.walk_mid_primitive S.origin S.word
  rw [hP] at hprim
  exact Pres.twoFour_not_primitive hprim

/-- The same gap, stated the way the repair reads it. In Def 6.2's
    `CompleteState` the presentation slot is not determined by the frame: the
    type declares no relation between them, and `nonprimitiveReading` pairs `2:4`
    with the frame whose mediant is `1:2` (the two still reduce to the same
    relation there). In `SubstrateState` the presentation is the frame's mediant,
    and by `presentation_determines_frame` it determines the frame in turn. -/
theorem substrate_presentation_is_the_frame_mediant (S : SubstrateState) :
    S.toComplete.presentation = S.toComplete.frame.mid := rfl

/-! ### D-09 finding 3, the third clause — preservation under Def 3.7's event

  Def 3.7's elementary refinement event moves two parts, `F_τ` and `w_τ`.
  `P_τ` and `M_τ` are discharged separately: `toComplete_consistent` gives the
  `M_τ` clause, `substrate_presentation_is_the_frame_mediant` gives `P_τ`'s.
  What is proved below is preservation of Def 3.7's elementary refinement
  event; whether Def 6.2's update law means this event or the general state
  transition is open (E1-20). -/

/-- The `(frame, word)` pair a `SubstrateState` presents to Def 3.7's event —
    the same projection `CompleteState.toEvent` below takes off the
    uncompressed record, so the two are comparable at all. -/
def SubstrateState.toEvent (S : SubstrateState) : Event := ⟨S.frame, S.word⟩

/-- The same projection off the seven-slot record. -/
def CompleteState.toEvent {K Hist : Type} (S : CompleteState K Hist) : Event :=
  ⟨S.frame, S.word⟩

/-- Compression commutes with the projection: reading the event off a
    compressed record and reading it off its decompression agree, because
    `toComplete` carries `frame` and `word` through unchanged. -/
theorem SubstrateState.toComplete_toEvent (S : SubstrateState) :
    S.toComplete.toEvent = S.toEvent := rfl

/-- **Def 3.7's own operation, run on the compressed record**: extend the
    retained word by one generator. `frame`, `presentation`, `matrix` and
    `closure` all move because they are `def`s of `origin` and `word`, not
    stored fields — there is nothing else for this to touch. -/
def SubstrateState.event (S : SubstrateState) (g : Bool) : SubstrateState :=
  { S with word := S.word ++ [g] }

/-- **Preservation, the third clause finding 3 asked for.** Stepping the
    compressed record and reading off its event agrees with reading the event
    off the compressed record and stepping *that* — Def 3.7's `(F,w) ↦
    (F·g,wg)`, applied on either side of compression, lands in the same
    place. The only fact this needs is `Frame.walk_snoc`, already built for
    Standard Result 3.1; nothing here is new arithmetic, only the missing
    link between it and `SubstrateState`. -/
theorem SubstrateState.toComplete_event (S : SubstrateState) (g : Bool) :
    (S.event g).toComplete.toEvent = S.toComplete.toEvent.step g := by
  rw [SubstrateState.toComplete_toEvent, SubstrateState.toComplete_toEvent]
  change (⟨(S.event g).frame, (S.event g).word⟩ : Event) = S.toEvent.step g
  unfold SubstrateState.toEvent SubstrateState.event SubstrateState.frame Event.step
  congr 1
  exact Frame.walk_snoc S.origin S.word g

/-! **D-09 closed.** All three of finding 3's clauses now hold: the checked
    decoder (`toSubstrate?`), the characterization of the valid image
    (`toSubstrate?_isSome_iff`), and preservation of Def 3.7's elementary
    refinement event (`toComplete_event`, immediately above); whether Def
    6.2's update law means this event or the general state transition is
    open (E1-20). Nothing wider is claimed: `𝒜_τ` and `H_τ` are not moved by
    `event`. -/


/-! ## Definition 6.4 — Object, and why this file does not build one

  The book refuses to define an object as a primitive, and says an object may be
  defined *once* recurrence and reception exist, as a stable equivalence class
  reconstructed from a **sufficient** family of relational histories, with
  stability and sufficiency **proved for the relevant domain**.

  **Divergence D-11.** An earlier version of this file made that refusal typed by
  declaring `structure Object` immediately, with `sufficient := witnesses ≠ []`.
  That compiles a witness the book withholds: a singleton family containing the
  *empty* history, with a constant reader, satisfies `stable` by `rfl` and
  `sufficient` because the list is nonempty — an object at witness count `1`
  where the book says the word is still informal shorthand, because recurrence
  and reception do not exist yet and no domain-specific sufficiency predicate has
  been stated. Nonemptiness is not sufficiency; it only looks like it once no
  domain is named to be sufficient *for*.

  **What the structure actually is, kept and renamed rather than deleted:** a
  family of histories that all read the same, which is real content — it is the
  premise recurrence and reception will act on, not the conclusion Def 6.4 gates.
  `Object` itself stays unbuilt until three things exist: a recurrence operation,
  a reception map, and a declared equivalence relation on relational histories
  with a domain-specific `Sufficient` predicate and a stability theorem proved
  against it — not merely typed as a field. -/

/-- **Not Definition 6.4.** A family of histories with a reading that is constant
    across it, and a proof the family is nonempty. `witnesses` is the family;
    `read` is the reconstruction; `stable` says the reading agrees on every
    member. Renamed from `Object` (divergence D-11): nonemptiness is not the
    book's sufficiency, and this structure carries no recurrence, no reception,
    and no domain, so it cannot stand in for Def 6.4's object. -/
structure ConstantReading where
  witnesses : ActiveFamily
  read : History → Pres
  stable : ∀ r ∈ witnesses, ∀ s ∈ witnesses, read r = read s
  sufficient : witnesses ≠ []

namespace ConstantReading

/-- The reading of a `ConstantReading`, which exists because the family does
    not. -/
def value (O : ConstantReading) : Pres := O.read (O.witnesses.head O.sufficient)

/-- No reading over an empty family, so "reconstructed from a nonempty family"
    cannot be satisfied vacuously. This is weaker than the book's sufficiency
    and is not offered as it. -/
theorem no_reading_without_witnesses (O : ConstantReading) : O.witnesses ≠ [] :=
  O.sufficient

/-- Every witness reads the same, which is what makes it a constant reading
    rather than a choice among readings. -/
theorem all_witnesses_agree (O : ConstantReading) {r : History} (hr : r ∈ O.witnesses) :
    O.read r = O.value :=
  O.stable r hr _ (List.head_mem O.sufficient)

end ConstantReading

/-! ## §7 — Presented state, the encounter record, and bilateral covariance -/

/-- **Definition 7.2.** A presented state is the history-bearing state entering
    relation with an observer. It is **the same type**, and that is the content:
    "observer" and "presented" name directional roles in an encounter, not two
    different ontological substances. An abbreviation rather than a new
    structure, so the identity is enforced by the elaborator and cannot drift. -/
abbrev Presented := Observer

/-- **Definition 7.4.** The complete encounter record. The relative matrix is not
    automatically the whole encounter, so both words are retained: distinct word
    presentations can become equal after group relations, and `Q` alone cannot
    tell those cases apart. `encounter_matrix_loses_history` in `Walk.lean` is
    the witness that this retention is necessary rather than cautious. -/
structure EncounterRecord where
  observerWord : Word
  presentedWord : Word
  relative : Mat2
  observerClosure : ClosureState
  presentedClosure : ClosureState
  observerHistory : List Word
  presentedHistory : List Word

namespace EncounterRecord

/-- The record built from two states, with `Q = M_O⁻¹ M_P`.

    **The history slots (audit E1-B4, 2026-09-28).** Definition 7.1's observer
    tuple is `(w_O, M_O, κ_O, η_O)`: it has no `H_O`, and neither does
    `Observer`. So this constructor has nothing to put in the history slots but
    the word, and it declares `H_O := [w_O]`, `H_P := [w_P]`. A mask that
    declares the history slots and reads through `of` therefore reads only the
    two words again. Reception (`ObsReception.receive`, `Perspective.lean`) reads
    through `of`, so this is the declaration in force there. The history
    Definition 7.4 means is the observer's own `H_τ` as a substrate state
    (Definition 6.2, "any additional composition, return, or circulation
    history", which Definition 7.1's "of the same mathematical kind as other
    substrate states" gives it): `ofStates` below carries it, `ofHist` takes it
    declared, `of_eq_ofHist` places this constructor among them, and
    `history_not_read_from_the_observer` proves the slots are not a function of
    the observer tuple.

    **D-14, fixed here.** `relative` read `inv2 (G O.word) * G P.word`, the
    same defect D-13 fixed at `encounter` — this constructor never picked the
    fix up. It now calls `encounter` directly rather than recomputing it, and
    the closure fields carry the declared start the way `Observer.closure`
    does. On `Frame.empty` starts (every existing example in this file) the
    values are unchanged, since `Observer.matrix`/`Observer.closure` already
    reduce to the pre-fix reading there. -/
def of (O P : Observer) : EncounterRecord :=
  { observerWord := O.word, presentedWord := P.word
    relative := encounter O P
    observerClosure := O.closure
    presentedClosure := P.closure
    observerHistory := [O.word], presentedHistory := [P.word] }

/-- **Definition 7.4 with the history slots declared.** The five slots
    Definition 7.1 supplies are read from the two observers; `H_O` and `H_P` are
    supplied, since Definition 7.1's tuple has none. -/
def ofHist (O P : Observer) (HO HP : List Word) : EncounterRecord :=
  { observerWord := O.word, presentedWord := P.word
    relative := encounter O P
    observerClosure := O.closure
    presentedClosure := P.closure
    observerHistory := HO, presentedHistory := HP }

/-- `of` is `ofHist` with each word declared as its own one-entry history. -/
theorem of_eq_ofHist (O P : Observer) : of O P = ofHist O P [O.word] [P.word] := rfl

/-- **Definition 7.4 read from two substrate states (Definition 6.2).** Every
    slot is the state's own: `w_τ`, `M_τ`, `κ_τ`, and `H_τ` for the history. -/
def ofStates (SO SP : SubstrateState) : EncounterRecord :=
  { observerWord := SO.word, presentedWord := SP.word
    relative := Mat2.inv2 SO.matrix * SP.matrix
    observerClosure := SO.closure
    presentedClosure := SP.closure
    observerHistory := SO.history, presentedHistory := SP.history }

/-- **The state record is the declared record.** Reading each state as an
    observer with the same declared start and word (any capacity `η`, which the
    record does not contain), `ofStates` is `ofHist` with the states' `H_τ`. -/
theorem ofStates_eq_ofHist (SO SP : SubstrateState) (ηO ηP : ℕ) :
    ofStates SO SP
      = ofHist ⟨SO.origin, SO.word, ηO⟩ ⟨SP.origin, SP.word, ηP⟩ SO.history SP.history :=
  rfl

/-- **And `of` is the state record when each state's history is its word**
    (the converse is `ofStates_eq_of_iff`). -/
theorem ofStates_eq_of (SO SP : SubstrateState) (ηO ηP : ℕ)
    (hO : SO.history = [SO.word]) (hP : SP.history = [SP.word]) :
    ofStates SO SP = of ⟨SO.origin, SO.word, ηO⟩ ⟨SP.origin, SP.word, ηP⟩ := by
  rw [ofStates_eq_ofHist SO SP ηO ηP, hO, hP]; rfl

/-- **`of` is the state record exactly when each state's history is its word.** -/
theorem ofStates_eq_of_iff (SO SP : SubstrateState) (ηO ηP : ℕ) :
    ofStates SO SP = of ⟨SO.origin, SO.word, ηO⟩ ⟨SP.origin, SP.word, ηP⟩
      ↔ SO.history = [SO.word] ∧ SP.history = [SP.word] :=
  ⟨fun h => ⟨congrArg observerHistory h, congrArg presentedHistory h⟩,
   fun ⟨hO, hP⟩ => ofStates_eq_of SO SP ηO ηP hO hP⟩

/-- **The history slots are not read from the observer tuple.** No function of
    the two observers `(w, M, κ, η)` gives the record of every pair of states
    that present them: two states with the same start and word and different
    `H_τ` present the same observer and have different records. So `H_O` in
    Definition 7.4 is information Definition 7.1's tuple does not hold, and a
    constructor from observers alone (`of`) can only declare it. -/
theorem history_not_read_from_the_observer :
    ¬ ∃ f : Observer → Observer → EncounterRecord,
        ∀ (SO SP : SubstrateState) (ηO ηP : ℕ),
          f ⟨SO.origin, SO.word, ηO⟩ ⟨SP.origin, SP.word, ηP⟩ = ofStates SO SP := by
  rintro ⟨f, hf⟩
  have h₁ := hf ⟨Frame.empty, [], [], []⟩ ⟨Frame.empty, [], [], []⟩ 1 1
  have h₂ := hf ⟨Frame.empty, [], [], [[true]]⟩ ⟨Frame.empty, [], [], []⟩ 1 1
  have := congrArg observerHistory (h₁.symm.trans h₂)
  simp [ofStates] at this

/-- **The record separates what the relative matrix cannot.** Observer at `R`
    meeting `RL`, and observer at `ε` meeting `L`, share one `Q` and differ in
    the record. This is Def 7.4's reason, with the two objects in hand. -/
theorem record_separates_what_Q_merges :
    (of ⟨Frame.empty, [true], 1⟩ ⟨Frame.empty, [true, false], 1⟩).relative
      = (of ⟨Frame.empty, [], 1⟩ ⟨Frame.empty, [false], 1⟩).relative ∧
    (of ⟨Frame.empty, [true], 1⟩ ⟨Frame.empty, [true, false], 1⟩)
      ≠ (of ⟨Frame.empty, [], 1⟩ ⟨Frame.empty, [false], 1⟩) := by
  constructor
  · change encounter ⟨Frame.empty, [true], 1⟩ ⟨Frame.empty, [true, false], 1⟩
      = encounter ⟨Frame.empty, [], 1⟩ ⟨Frame.empty, [false], 1⟩
    simp only [encounter, Observer.matrix, Frame.toMat2_empty, Mat2.one_mul']
    exact encounter_matrix_loses_history.1
  · intro h
    have := congrArg observerWord h
    simp [of] at this

end EncounterRecord

/-- **Proposition 7.2 — bilateral encounter covariance.**
    `Q⁺ = g_O⁻¹ Q g_P`. When the receiving and presented histories each take a
    forward step, `g_O` and `g_P`, supplied as separate arguments so that neither
    step is fixed by the other, the encounter transforms on both sides at once.
    The two steps are coupled through the one encounter matrix both act on, and
    nothing prevents choosing them equal. The observer's step acts by its
    inverse on the left and the presented step acts on the right, which is Rule
    0.4's typed action: these are not two notations for one multiplication. -/
theorem bilateral_covariance (MO MP gO gP : Mat2) :
    Mat2.inv2 (MO * gO) * (MP * gP)
      = Mat2.inv2 gO * (Mat2.inv2 MO * MP) * gP := by
  rw [Mat2.inv2_mul, Mat2.mul_assoc', Mat2.mul_assoc', Mat2.mul_assoc']

namespace History

/-- **Def 3.11, levels 3 and 4 for histories with one start frame.** The
    addressed relation determines the word from a given frame
    (`Frame.addressed_inj`). It sits here, not in `Walk.lean`, because
    `mid_inj` is proved in this file. Without the shared start it fails
    (`endpointEq_not_wordEq`). -/
theorem endpointEq_iff_wordEq_of_start_eq {X Y : History} (hs : X.start = Y.start) :
    X.EndpointEq Y ↔ X.WordEq Y := by
  unfold EndpointEq WordEq addressed
  rw [hs]
  exact ⟨fun h => Frame.addressed_inj Y.start h, fun h => by rw [h]⟩

/-- **Def 3.11, levels 3 and 1 on every pair of histories.** The addressed
    relation is the final frame's mediant, and the mediant determines the frame
    (`Frame.mid_inj`), so equal addressed relations are equal presentations,
    whatever the start frames. -/
theorem endpointEq_iff_presEq {X Y : History} : X.EndpointEq Y ↔ X.PresEq Y := by
  constructor
  · intro h
    have hF : X.frame = Y.frame := Frame.mid_inj h
    exact ⟨congrArg Frame.plus hF, congrArg Frame.minus hF⟩
  · rintro ⟨hp, hm⟩
    change X.frame.mid = Y.frame.mid
    rw [Frame.ext' hp hm]

/-- **Def 3.11, levels 3 and 5 on every pair of histories**, through level 1
    (`endpointEq_iff_presEq`, `matrixEq_iff_presEq`). No shared start. -/
theorem endpointEq_iff_matrixEq {X Y : History} : X.EndpointEq Y ↔ X.MatrixEq Y :=
  endpointEq_iff_presEq.trans matrixEq_iff_presEq.symm

/-- **Def 3.11: levels 1, 2, 3 and 5 are one relation on every pair of
    histories**, whatever their start frames (audit E1-A1 verifier, 2026-09-29).
    Presentation, value, endpoint and matrix equality all say the final frame
    is the same frame. Of the first five levels only word equality (level 4)
    separates, and only once the start frame may vary (`matrixEq_not_wordEq`,
    `endpointEq_not_wordEq`). -/
theorem levels_one_two_three_five {X Y : History} :
    (X.PresEq Y ↔ X.ValueEq Y) ∧ (X.ValueEq Y ↔ X.EndpointEq Y) ∧
      (X.EndpointEq Y ↔ X.MatrixEq Y) :=
  ⟨endpointEq_iff_presEq.symm.trans valueEq_iff_endpointEq.symm,
    valueEq_iff_endpointEq, endpointEq_iff_matrixEq⟩

/-- **Def 3.11: with one start frame, levels 1 to 5 are one relation**
    (audit E1-A1, 2026-09-29). Levels 1, 2, 3 and 5 are one relation on every
    pair (`levels_one_two_three_five`); the shared start is needed only to
    bring in level 4, word equality. So in the canonical domain (start `F_∅`)
    none of the first five levels separates from another. -/
theorem levels_one_to_five_of_start_eq {X Y : History} (hs : X.start = Y.start) :
    (X.PresEq Y ↔ X.MatrixEq Y) ∧ (X.MatrixEq Y ↔ X.WordEq Y) ∧
      (X.WordEq Y ↔ X.EndpointEq Y) ∧ (X.EndpointEq Y ↔ X.ValueEq Y) :=
  ⟨matrixEq_iff_presEq.symm, matrixEq_iff_wordEq hs,
    (endpointEq_iff_wordEq_of_start_eq hs).symm, valueEq_iff_endpointEq.symm⟩

end History

/-! ### Definition 3.7 from a declared frame, on the substrate state

    Audit E1-A16 (2026-10-01): `Event.Coherent` reads coherence against `F_∅`
    only; `Event.CoherentFrom` (`Walk.lean`) reads it against a declared start
    frame. A substrate state walks from its declared origin (D-14), so its
    event is coherent from that origin, and from `F_∅` only when the origin is
    `F_∅`. -/

/-- **A coherent event fixes its start frame.** By `Frame.walk_left_inj`,
    two start frames that walk the same word to the same frame are one frame,
    so `(F₀, w)` is recoverable from the event. -/
theorem Event.coherentFrom_start_unique {F₀ F₁ : Frame} {e : Event}
    (h₀ : e.CoherentFrom F₀) (h₁ : e.CoherentFrom F₁) : F₀ = F₁ :=
  Frame.walk_left_inj (h₀.symm.trans h₁)

/-- **A substrate state's event is coherent from its declared origin.** -/
theorem SubstrateState.toEvent_coherentFrom (S : SubstrateState) :
    S.toEvent.CoherentFrom S.origin := rfl

/-- **A substrate state's event is coherent from `F_∅` exactly when its
    origin is `F_∅`.** So the canonical-frame `Coherent` does not cover the
    substrate states with a declared origin. -/
theorem SubstrateState.toEvent_coherent_iff (S : SubstrateState) :
    S.toEvent.Coherent ↔ S.origin = Frame.empty := by
  rw [Event.coherent_iff_coherentFrom_empty]
  constructor
  · intro h
    exact Event.coherentFrom_start_unique S.toEvent_coherentFrom h
  · intro h
    rw [← h]
    exact S.toEvent_coherentFrom

end RatioSpace
