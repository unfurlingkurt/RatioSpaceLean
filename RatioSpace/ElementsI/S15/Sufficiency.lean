/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S12.Correspondence
/-!
  Elements I §15 — What a universality claim is.

  The last three numbered items of Elements I. The book (v0.25, Definition 15.3)
  states the claim exactly: *"A universal generative claim over a stated class
  𝒦 of admissible mechanics is the statement: for every mechanics 𝒟 in 𝒦, items
  1 to 5 of Definition 15.1 are constructed for 𝒟, and the family of perspectives
  formed by the observers declared in item 4, each with its reception and the
  identity projection, is complete for 𝒟 (Definition 15.2)."*

  So this file types the obligation and stops. Def 15.1 is five items because
  the book lists five things that must be constructed (eight fields: item 3 is
  the relation with its agreement and its equivalence proof, audit finding
  E1-B8; item 4 is the declared observers, their non-emptiness and the
  reception family, gap G1-26), and nobody should be able to claim sufficiency
  for a domain while supplying four of them. Item 2's realization is built from
  Definition 3.2's actions on a state (`TypedAction`), not any map that commutes
  with the encoding, which a coding construction supplies for free (audit W3,
  2026-10-01; `flipDomain_not_sufficient`). Def 15.2 is
  already built and is not rebuilt here; it is restated at a domain for Def
  15.3 (`CompleteFor`, gap G1-27). Def 15.3 is a `Prop` that is defined and
  deliberately left unproved; a beat that proves it has proved something else.

  **Three findings**: the first two about direction, the third about what a domain reads.

  First, **Def 15.1's encoding is not a Def 12.2 encoding, and they point
  opposite ways.** Def 12.2's `E_O : 𝔖 → 𝓕_O` runs substrate → field, out of the
  substrate and into a reading. Def 15.1's runs target → substrate, into the
  substrate from outside. Both obligations are the same commuting square from Def
  12.3, and that is why `Correspondence` cannot be reused verbatim here: its `E`
  is typed as a map out of `SubstrateState`. The square is shared; the arrow is
  reversed. The book never says this and the two definitions read as though they
  were about the same map.

  Second, and this is the one with teeth: **generative sufficiency forbids the
  encoding from merging two histories the target can tell apart.** It falls
  straight out of the fifth obligation at any one declared observer (item 4
  says there is one), needs no further hypothesis, and is
  `encode_cannot_merge_the_distinguishable` below. The book asserts the spirit of
  this in prose; here it is a consequence of the typed obligation rather than a
  further requirement anyone has to remember to impose.

  Third (gap G1-27): **what decides the claim at a domain is its declared
  `Reading`.** Completeness is asked of the sufficiency term's own receptions,
  which land in the domain's declared `Reading`; item 5 constrains only their
  projection. `wordDomain`, the `L`/`R` words read as words (the reading is the
  presented word, the quantity its closure record, `same` equality), meets both
  halves (`universal_claim_holds_on_the_word_domain`). `wordByClosureDomain` is
  the same target declared with the closure record as its reading: there the
  projection is injective, the receptions are pinned to the quantity and
  completeness is `observe` separating `same`
  (`complete_iff_of_project_injective`), and the closure record does not
  separate words (`wordByClosureDomain_not_complete`). That declaration says
  every distinct word is different while reading only what cannot tell the
  empty word from `R^12`; Def 15.2 refuses it, as it should. The domain that
  identifies words by their closure record meets both halves
  (`universal_claim_holds_on_the_closure_domain`).
-/

namespace RatioSpace
namespace Layer

/-! ## The target, as data

  Def 15.1 quantifies over "a target domain `𝒟`" without saying what one is, so
  the first job is to write down the least that has to be true of a domain for
  the five obligations to be statable about it. Everything here is the target's
  own, named in the target's own terms: RatioSpace appears nowhere in it. -/

/-- **A target domain.** The five obligations of Def 15.1 each speak about one
    of these fields, which is the check that nothing has been smuggled in: a
    domain declares its histories, its primitive transitions, what it treats as
    the same, what its receptions can read, and the outcome its declared
    projection yields. -/
structure Domain where
  /-- the target's admissible distinction histories -/
  History : Type
  /-- its primitive transitions, as an index -/
  Transition : Type
  /-- what its receptions can read: the space they land in -/
  Reading : Type
  /-- the outcome its declared projection yields -/
  Quantity : Type
  /-- how a primitive transition acts on a history -/
  step : Transition → History → History
  /-- the equivalence the target itself declares, Def 15.1's third obligation -/
  same : History → History → Prop
  /-- it is an equivalence relation: Def 15.2's "the target's declared
      equivalence" (audit finding E1-B8) -/
  same_equiv : Equivalence same
  /-- the target's declared projection, which Def 15.1's fifth obligation names -/
  project : Reading → Quantity
  /-- what the target says the answer is -/
  observe : History → Quantity

/-! ## Definition 15.1 — generative sufficiency -/

/-- **An encoded state as a presented state (Definition 7.2).** Item 4 of
    Definition 15.1 asks for reception maps, and a reception (Definition 11.1)
    reads an encounter `𝖤_{O,P}` with a presented state `P`, which is an
    `Observer` (`Presented`). The encoded `SubstrateState` enters the encounter
    as the history-bearing state with its declared origin and its retained
    word. Its capacity is set to `0`, and nothing reads it:
    `presentedState_record_capacity_free` shows the encounter record does not
    depend on the presented state's capacity. The active family and `H_τ` of
    the substrate state do not enter the record, whose history fields are the
    two words (`EncounterRecord.of`). -/
def presentedState (S : SubstrateState) : Presented := ⟨S.origin, S.word, 0⟩

/-- The capacity given to `presentedState` carries nothing: the record of an
    encounter never reads the presented state's capacity. -/
theorem presentedState_record_capacity_free (O : Observer) (s : Frame) (w : Word)
    (e e' : ℕ) : EncounterRecord.of O ⟨s, w, e⟩ = EncounterRecord.of O ⟨s, w, e'⟩ := rfl

/-- The presented state carries the substrate state's closure. -/
theorem presentedState_closure (S : SubstrateState) :
    (presentedState S).closure = S.closure := rfl

/-! ## Item 2's actions: Definition 3.2 on a substrate state (audit W3)

  Item 2 asks for *"an exact RatioSpace realization"*, so the realization is
  built from RatioSpace's own operations on a state, not from any map that
  commutes with the encoding. Until audit W3 (2026-10-01) the field took any
  `SubstrateState → SubstrateState` commuting with the encoding, and for any
  domain whose histories code into words and decode back, decode, step,
  re-encode is such a map (`coding_has_a_commuting_map`), whatever the
  transition does.

  The operations are Definition 3.2's typed actions as they act on one state:
  **forward continuation** appends a generator to the retained word (Def 3.7's
  event, `SubstrateState.event`; on the word's matrix it is `forward`,
  `M ↦ Mg`, and the active frame takes one more step), and **prefix or
  reframing** places a generator before the retained word (`G(gw) = gG(w)`;
  on the word's matrix it is `reframe`, `M ↦ gM`).
  The third form, bilateral encounter transport, acts on the relative record
  of two histories (Def 7.3), not on one state, so it is not an action here.
  Neither action touches the declared origin, the active family or `H_τ`. A
  realization is a finite list of actions, run first to last; one list per
  primitive transition, the same at every history: the one-list form of
  item 2's "realization of every primitive target transition" (E1-48). The
  history-dependent form (a list that is a function of the history) gives the
  same conclusion around a cycle, by the same count of generators
  (`Layer.history_dependent_cycle_is_empty`), so the form of item 2 does not matter. -/

/-- **Definition 3.2's two single-state actions**, as data: forward
    continuation by a generator and prefix (reframing) by a generator. -/
inductive TypedAction where
  /-- forward continuation by `g`: `w ↦ wg` -/
  | forward (g : Bool)
  /-- prefix or reframing by `g`: `w ↦ gw` -/
  | reframe (g : Bool)
deriving DecidableEq

namespace TypedAction

/-- One action on a substrate state. Forward continuation is Def 3.7's event
    `SubstrateState.event`; reframing prefixes the retained word. -/
def act : TypedAction → SubstrateState → SubstrateState
  | forward g, S => S.event g
  | reframe g, S => { S with word := g :: S.word }

/-- A list of actions, run first to last. -/
def run (as : List TypedAction) (S : SubstrateState) : SubstrateState :=
  as.foldl (fun S a => a.act S) S

@[simp] theorem run_nil (S : SubstrateState) : run [] S = S := rfl

@[simp] theorem run_cons (a : TypedAction) (as : List TypedAction) (S : SubstrateState) :
    run (a :: as) S = run as (a.act S) := rfl

/-- **Forward continuation is Def 3.2's `forward`** on the retained word's
    matrix: `G(wg) = G(w)g`. -/
theorem act_forward_G (g : Bool) (S : SubstrateState) :
    Word.G ((forward g).act S).word = RatioSpace.forward (Word.G S.word) (Word.gen g) :=
  Word.G_snoc S.word g

/-- **Reframing is Def 3.2's `reframe`** on the retained word's matrix:
    `G(gw) = gG(w)`. On the accumulated transform `M_τ = M_{F₀}G(w)` it gives
    `M_{F₀} g G(w)`, which is not `g M_τ` in general; it is when `M_{F₀}`
    commutes with `g`, at the root origin for one. The prefix is placed
    before the retained record, not before the origin. -/
theorem act_reframe_G (g : Bool) (S : SubstrateState) :
    Word.G ((reframe g).act S).word = RatioSpace.reframe (Word.gen g) (Word.G S.word) :=
  Word.G_cons g S.word

/-- **Forward continuation moves the frame by one step**: the active frame of
    the result is the active frame's child on side `g` (`walk_snoc`). -/
theorem act_forward_frame (g : Bool) (S : SubstrateState) :
    ((forward g).act S).frame = Frame.select S.frame g :=
  Frame.walk_snoc S.origin S.word g

/-- The letters a list of actions places before the word, outermost first. -/
def pre : List TypedAction → Word
  | [] => []
  | forward _ :: as => pre as
  | reframe g :: as => pre as ++ [g]

/-- The letters a list of actions places after the word, in order. -/
def suf : List TypedAction → Word
  | [] => []
  | forward g :: as => g :: suf as
  | reframe _ :: as => suf as

/-- **What a run does, exactly.** It keeps the origin, the active family and
    `H_τ`, and sends the retained word `w` to `pre ++ w ++ suf`, with both
    letters fixed by the list and not by the state. -/
theorem run_eq (as : List TypedAction) (S : SubstrateState) :
    run as S = { S with word := pre as ++ S.word ++ suf as } := by
  induction as generalizing S with
  | nil => simp [pre, suf]
  | cons a as ih =>
    cases a with
    | forward g =>
      rw [run_cons, ih]
      simp [act, SubstrateState.event, pre, suf]
    | reframe g =>
      rw [run_cons, ih]
      simp [act, pre, suf]

theorem pre_length_add_suf_length (as : List TypedAction) :
    (pre as).length + (suf as).length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases a <;> simp [pre, suf] <;> omega

/-- **Every action adds one letter.** -/
theorem run_word_length (as : List TypedAction) (S : SubstrateState) :
    (run as S).word.length = S.word.length + as.length := by
  rw [run_eq]
  simp only [List.length_append]
  have := pre_length_add_suf_length as
  omega

end TypedAction

/-- **Definition 15.1.** *"RatioSpace is generatively sufficient for a target
    domain `𝒟` when the following have been constructed."* Five items, in the
    book's order.

    Items 2 and 3 carry their proofs, because the book's wording is "an
    **exact** realization" and "an **explicit** equivalence relation": a map
    without its exactness proof is not the thing Def 15.1 asks for. `realize`
    and `identify` carry the square and the agreement with `D.same` in their
    types; item 3's equivalence proof is the next field, `equiv` (audit E1-B8),
    and like every field it cannot be omitted from a term of this type.

    `realize` is Def 12.3's commuting square, once per primitive transition, with
    the arrow reversed: see this file's header. The update on the RatioSpace
    side is built from Definition 3.2's actions (`TypedAction`), one list per
    transition (audit W3), so it keeps the origin, the active family and
    `H_τ` and sends the retained word `w` to `pre ++ w ++ suf`
    (`TypedAction.run_eq`). The square is equality, which is what "exact"
    is read as; Def 12.3's other option, a stated error or limiting relation,
    is not taken. One consequence: a transition that returns some history to
    itself after one or more steps leaves every outcome unchanged
    (`GenerativelySufficient.observe_step_of_cycle`). So a two-state flip has
    no sufficiency term (`flipDomain_not_sufficient`), and the same flips
    declared as a history, counted, have one (`toggleSufficient`).

    **Item 4 (gap G1-26).** *"observer-relative reception maps reproducing the
    target's accessible quantities"*: plural and observer-relative. It is a
    declared, non-empty list of observers with an observer-indexed reception
    family (Definition 11.1, `ObsReception`), each observer receiving its own
    encounter `𝖤_{O,P}` with the encoded state presented (`presentedState`).
    **Item 5** is then stated at every declared observer: each one's reception,
    under the target's declared projection, recovers the target's outcome.
    Recovery at each observer is a declared reading of "reproducing the
    target's accessible quantities"; recovery from the joint of the readings
    is Def 15.2's business, not this item's. The pre-G1-26 form, one map on
    states with no observer, is `GenerativelySufficientOnState` below, and every
    declared observer gives one (`toOnState`).

    The receiving space is `D.Reading` at every capacity, where Definition 11.1
    writes `Y_O`. That is forced here by the domain's one declared projection
    `D.project : D.Reading → D.Quantity`; a domain with a projection per
    receiving space would need `Y_O` to vary. -/
structure GenerativelySufficient (D : Domain) where
  /-- **1.** an encoding of every admissible target distinction history into a
      RatioSpace state -/
  encode : D.History → SubstrateState
  /-- **2.** an exact RatioSpace realization of every primitive target
      transition: a list of Definition 3.2's actions (`TypedAction`), one per
      transition, carrying its own commuting square (audit W3: was any map on
      states commuting with the encoding) -/
  realize : ∀ t : D.Transition,
    { as : List TypedAction //
        ∀ h : D.History, encode (D.step t h) = TypedAction.run as (encode h) }
  /-- **3.** an explicit equivalence relation identifying the presentations the
      target treats as the same, carrying its own agreement with `D.same` -/
  identify :
    { C : SubstrateState → SubstrateState → Prop //
        ∀ h h' : D.History, D.same h h' ↔ C (encode h) (encode h') }
  /-- **3, continued.** the relation is an equivalence relation, as the book's
      "explicit equivalence relation" says; before audit finding E1-B8 any
      relation agreeing with `D.same` on encoded states was accepted, an
      irreflexive one included -/
  equiv : Equivalence identify.1
  /-- **4a.** the observers whose receptions are declared -/
  observers : List Observer
  /-- **4b.** at least one: with none, item 5 would hold of anything -/
  nonempty : ∃ O, O ∈ observers
  /-- **4c.** the observer-relative reception maps, Def 11.1's layer: the
      member at each observer's capacity reads that observer's encounter -/
  reception : ObsReception (fun _ => D.Reading)
  /-- **5.** at every declared observer, the target's outcomes are recovered
      under the declared projection, Def 11.2's layer -/
  recovers : ∀ O ∈ observers, ∀ h : D.History,
    D.project (reception.receive O (presentedState (encode h))) = D.observe h

/-- **The pre-G1-26 form of Definition 15.1**, kept under its own name: item 4
    as one map on substrate states, with no observer and no encounter. It is
    what one declared observer's reception becomes once the observer is fixed
    (`GenerativelySufficient.toOnState`). -/
structure GenerativelySufficientOnState (D : Domain) where
  encode : D.History → SubstrateState
  realize : ∀ t : D.Transition,
    { as : List TypedAction //
        ∀ h : D.History, encode (D.step t h) = TypedAction.run as (encode h) }
  identify :
    { C : SubstrateState → SubstrateState → Prop //
        ∀ h h' : D.History, D.same h h' ↔ C (encode h) (encode h') }
  equiv : Equivalence identify.1
  receive : SubstrateState → D.Reading
  recovers : ∀ h : D.History, D.project (receive (encode h)) = D.observe h

namespace GenerativelySufficient

variable {D : Domain} (G : GenerativelySufficient D)

/-- **Item 3 is an equivalence on every encoded state.** Every state is
    identified with itself, so no term of Def 15.1 carries an irreflexive
    relation such as `fun _ _ => False` (audit finding E1-B8: before the
    `equiv` field, such a term compiled). -/
theorem identify_refl (S : SubstrateState) : G.identify.1 S S := G.equiv.refl S

include G in
/-- Through `identify`, the term's equivalence gives the domain's
    reflexivity at every history, independently of `D.same_equiv`. -/
theorem same_refl (h : D.History) : D.same h h :=
  (G.identify.2 h h).mpr (G.identify_refl _)

/-- The realization of a transition, as a map on states: its actions run. -/
def realizeMap (t : D.Transition) : SubstrateState → SubstrateState :=
  TypedAction.run (G.realize t).1

/-- **The second obligation is a commuting square, stated in the open.** Nothing
    new is proved — the square is the second component of the field — but Def
    15.1 never uses the word "square" and Def 12.3 never mentions §15, so this
    is where the two are said to be one thing. -/
theorem realize_commutes (t : D.Transition) (h : D.History) :
    G.encode (D.step t h) = G.realizeMap t (G.encode h) :=
  (G.realize t).2 h

/-- **The declared equivalence is decided by the encoded states.** The third
    obligation is an `↔`, so sufficiency does not merely require the encoding to
    respect `D.same`, it requires the encoding to reflect it as well: nothing may
    be identified in RatioSpace that the target keeps apart. -/
theorem same_iff_identified (h h' : D.History) :
    D.same h h' ↔ (G.identify.1) (G.encode h) (G.encode h') :=
  G.identify.2 h h'

/-- **Sufficiency forbids merging what the target can distinguish.**

    If the encoding sends two histories to the same substrate state, the target
    must read the same quantity off both. Equivalently, and this is the useful
    direction: **an encoding that collapses two histories the target reads
    differently cannot be extended to a generative sufficiency term at all**, no
    matter what reception or projection is chosen afterwards.

    It costs one rewrite at any declared observer, which item 4's non-emptiness
    supplies, because the fifth obligation already routes `observe` through
    `encode`. That is the point: the constraint is a consequence of the
    typed obligation rather than a sixth thing to remember. -/
theorem encode_cannot_merge_the_distinguishable {h h' : D.History}
    (hyp : G.encode h = G.encode h') : D.observe h = D.observe h' := by
  obtain ⟨O, hO⟩ := G.nonempty
  rw [← G.recovers O hO h, ← G.recovers O hO h', hyp]

/-- The contrapositive, which is the form a counterexample takes. -/
theorem distinguishable_forces_distinct_encodings {h h' : D.History}
    (hyp : D.observe h ≠ D.observe h') : G.encode h ≠ G.encode h' :=
  fun heq => hyp (G.encode_cannot_merge_the_distinguishable heq)

/-! ### What the typed realization forces (audit W3) -/

/-- **Each transition is one fixed two-sided word action on the encoding**
    (a prefix and a suffix; not Def 3.2's bilateral transport).
    There are words `p` and `s`, fixed by the transition, with
    `encode (step t h)` keeping `encode h`'s origin, active family and `H_τ`
    and retaining `p ++ w ++ s` where `encode h` retains `w`, at every
    history `h`. -/
theorem encode_step_eq (t : D.Transition) :
    ∃ p s : Word, ∀ h : D.History,
      G.encode (D.step t h) = { G.encode h with word := p ++ (G.encode h).word ++ s } :=
  ⟨TypedAction.pre (G.realize t).1, TypedAction.suf (G.realize t).1, fun h =>
    ((G.realize t).2 h).trans (TypedAction.run_eq _ _)⟩

/-- **Each transition lengthens every encoded word by the same amount**, the
    number of its actions. -/
theorem encode_step_length (t : D.Transition) (h : D.History) :
    (G.encode (D.step t h)).word.length = (G.encode h).word.length + (G.realize t).1.length := by
  rw [(G.realize t).2 h]
  exact TypedAction.run_word_length _ _

/-- **`n` steps of a transition lengthen every encoded word by `n` times its
    action count.** -/
theorem encode_iterate_length (t : D.Transition) (n : ℕ) (h : D.History) :
    (G.encode ((D.step t)^[n] h)).word.length =
      (G.encode h).word.length + n * (G.realize t).1.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', G.encode_step_length, ih, Nat.succ_mul]
    omega

/-- **A transition with a cycle is realized by no action.** If the transition
    returns some history to itself after `n + 1` steps (a fixed point is
    `n = 0`), the encoded word there grows by `n + 1` times the action count
    and comes back, so the list is empty. -/
theorem realize_nil_of_cycle (t : D.Transition) (n : ℕ) {h : D.History}
    (hc : (D.step t)^[n + 1] h = h) : (G.realize t).1 = [] := by
  have h1 := G.encode_iterate_length t (n + 1) h
  rw [hc] at h1
  have h0 : (n + 1) * (G.realize t).1.length = 0 := by omega
  rcases Nat.mul_eq_zero.mp h0 with h2 | h2
  · omega
  · exact List.length_eq_zero_iff.mp h2

/-- The two-step case of `realize_nil_of_cycle`. -/
theorem realize_nil_of_two_cycle (t : D.Transition) {h : D.History}
    (hc : D.step t (D.step t h) = h) : (G.realize t).1 = [] :=
  G.realize_nil_of_cycle t 1 hc

include G in
/-- **So a transition with a cycle anywhere moves no outcome anywhere**: with
    no action, `encode (step t h) = encode h` at every history, and
    `encode_cannot_merge_the_distinguishable` does the rest. This is the cost
    of an exact square built from typed actions. A two-state flip has no
    sufficiency term (`flipDomain_not_sufficient`); the same flips declared as
    a history, counted, have one (`toggleSufficient`). -/
theorem observe_step_of_cycle (t : D.Transition) (n : ℕ) {h₀ : D.History}
    (hc : (D.step t)^[n + 1] h₀ = h₀) (h : D.History) :
    D.observe (D.step t h) = D.observe h := by
  apply G.encode_cannot_merge_the_distinguishable
  rw [G.realize_commutes, realizeMap, G.realize_nil_of_cycle t n hc, TypedAction.run_nil]

include G in
/-- The two-step case of `observe_step_of_cycle`. -/
theorem observe_step_of_two_cycle (t : D.Transition) {h₀ : D.History}
    (hc : D.step t (D.step t h₀) = h₀) (h : D.History) :
    D.observe (D.step t h) = D.observe h :=
  G.observe_step_of_cycle t 1 hc h

/-- **One declared observer, fixed, gives the pre-G1-26 form.** Its reception
    of the encoded state, as a map on states, is the old item 4. -/
def toOnState (O : Observer) (hO : O ∈ G.observers) : GenerativelySufficientOnState D where
  encode := G.encode
  realize := G.realize
  identify := G.identify
  equiv := G.equiv
  receive := fun S => G.reception.receive O (presentedState S)
  recovers := G.recovers O hO

end GenerativelySufficient

/-! ## The type is not vacuous

  A structure nobody can instantiate would make Def 15.1 unfalsifiable rather
  than demanding, so §15 needs a domain with a sufficiency term. The free
  `L`/`R` word domain has one: each target transition is realized by one
  forward continuation (`wordRealize`, `wordSufficient_realize`), Def 3.2's
  own action. Since audit W3 a realization must be a list of typed actions,
  and a decode-step-re-encode map is refused where it is not one
  (`flipDomain_not_sufficient`). -/

/-- **The word domain declared with a lossy reading**: histories are `L`/`R`
    words, transitions the two generators, `same` is equality of words, and
    both the reading and the outcome are the closure record. It meets Def 15.1
    and is mis-declared for Def 15.3: it keeps apart words its reading cannot
    tell apart (`wordByClosureDomain_not_complete`). Built 2026-08-24 as
    `wordDomain`; renamed for its reading when the word domain proper was made
    to read the word (G1-27 follow-up, 2026-09-27). -/
def wordByClosureDomain : Domain where
  History := Word
  Transition := Bool
  Reading := ClosureState
  Quantity := ClosureState
  step := fun b w => w ++ [b]
  same := fun u v => u = v
  same_equiv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  project := id
  observe := fun w => ClosureState.ofWord w

/-- The encoding: a word becomes the state that retains it, from the empty
    origin, with nothing active and nothing archived. -/
def wordEncode (w : Word) : SubstrateState := ⟨Frame.empty, w, [], []⟩

/-- The realization of the generator `b`: one forward continuation by `b`,
    which appends it to the retained word (until audit W3 this was the map on
    states itself, `S ↦ S` with `b` appended; it is now the action that map
    runs). Named separately, with `b : Bool` explicit, because writing it
    inline leaves the generator at type `wordByClosureDomain.Transition`. -/
def wordRealize (b : Bool) : List TypedAction := [TypedAction.forward b]

/-- Running `wordRealize b` is appending `b` to the retained word, Def 3.7's
    event. -/
theorem run_wordRealize (b : Bool) (S : SubstrateState) :
    TypedAction.run (wordRealize b) S = S.event b := rfl

/-- The reception that declares the presented closure and reads nothing
    else. -/
def presentedClosureReception : Reception ClosureState where
  mask := { Mask.blank with presentedClosure := true }
  read := EncounterRecord.presentedClosure
  honest := fun _ _ h => h.2.2.2.2.1 rfl

/-- **`wordByClosureDomain` is generatively sufficient**, all five obligations supplied,
    with any non-empty list of declared observers.

    The transition realization is one forward continuation by the generator
    (`wordRealize`), and its square is `rfl`: appending to the target's word
    and appending to the retained word are the same operation. The
    equivalence is equality of encoded states, which reflects and preserves
    `same`. Item 4 is the same reception at every capacity (reading A of
    E1-39), declaring the presented closure `κ_P` of the encounter and nothing
    else, so every observer recovers the target's closure
    record. That this is so for every observer is a fact about this reception,
    not about item 4: `Gaps/G1_26.lean` has a reception that recovers at one
    observer and not at another. -/
def wordByClosureSufficientAt (Os : List Observer) (hOs : ∃ O, O ∈ Os) :
    GenerativelySufficient wordByClosureDomain where
  encode := wordEncode
  realize := fun t => ⟨wordRealize t, fun _ => rfl⟩
  identify :=
    ⟨fun S T => S = T, fun u v => by
      constructor
      · intro h; exact congrArg wordEncode h
      · intro h; exact congrArg SubstrateState.word h⟩
  equiv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  observers := Os
  nonempty := hOs
  reception := ObsReception.const presentedClosureReception
  recovers := fun _ _ w => ClosureState.of_empty w

/-- The witness with one observer at the root. -/
def wordByClosureSufficient : GenerativelySufficient wordByClosureDomain :=
  wordByClosureSufficientAt [⟨Frame.empty, [], 0⟩] ⟨_, List.mem_singleton_self _⟩

/-- The pre-G1-26 witness: the reception is Def 12.1's Arrow 1 on states, and
    the recovery is `rfl` because `SubstrateState.closure` is `ofWord` of the
    retained word. -/
def wordByClosureSufficientOnState : GenerativelySufficientOnState wordByClosureDomain where
  encode := wordEncode
  realize := fun t => ⟨wordRealize t, fun _ => rfl⟩
  identify :=
    ⟨fun S T => S = T, fun u v => by
      constructor
      · intro h; exact congrArg wordEncode h
      · intro h; exact congrArg SubstrateState.word h⟩
  equiv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  receive := closureOfState
  recovers := fun _ => rfl

/-- **The word domain**: histories are `L`/`R` words, transitions the two
    generators, `same` is equality of words, the reading is the word itself and
    the outcome its closure record, reached by the declared projection
    `ClosureState.ofWord`. Everything but the reading is `wordByClosureDomain`'s
    (`wordDomain_eq_but_reading`). -/
def wordDomain : Domain :=
  { wordByClosureDomain with Reading := Word, project := ClosureState.ofWord }

/-- The two word domains differ in the declared reading and the projection out
    of it, and in nothing else. -/
theorem wordDomain_eq_but_reading :
    wordDomain.History = wordByClosureDomain.History ∧
    wordDomain.Quantity = wordByClosureDomain.Quantity ∧
    wordDomain.Reading = Word ∧ wordByClosureDomain.Reading = ClosureState :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The reception that declares the presented word and reads nothing else. -/
def presentedWordReception : Reception Word where
  mask := { Mask.blank with presentedWord := true }
  read := EncounterRecord.presentedWord
  honest := fun _ _ h => h.2.1 rfl

/-- **`wordDomain` is generatively sufficient**, all five obligations supplied,
    with any non-empty list of declared observers. Items 1 to 3 are the closure
    witness's: the same encoding, the same realization (one forward
    continuation, square `rfl`), the same equivalence (equality of encoded
    states). Item 4 reads the presented word of each observer's encounter;
    item 5 projects it to its closure record, which is the target's outcome. -/
def wordSufficientAt (Os : List Observer) (hOs : ∃ O, O ∈ Os) :
    GenerativelySufficient wordDomain where
  encode := wordEncode
  realize := fun t => ⟨wordRealize t, fun _ => rfl⟩
  identify :=
    ⟨fun S T => S = T, fun (u v : Word) => by
      constructor
      · intro h; exact congrArg wordEncode h
      · intro h; exact congrArg SubstrateState.word h⟩
  equiv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  observers := Os
  nonempty := hOs
  reception := ObsReception.const presentedWordReception
  recovers := fun _ _ _ => rfl

/-- The witness with one observer at the root. -/
def wordSufficient : GenerativelySufficient wordDomain :=
  wordSufficientAt [⟨Frame.empty, [], 0⟩] ⟨_, List.mem_singleton_self _⟩

/-- **The word witnesses realize each generator by one forward continuation**
    (audit W3): the realization item 2 carries is Def 3.2's action, not a map
    chosen to commute. -/
theorem wordSufficient_realize (b : Bool) :
    (wordSufficient.realize b).1 = [TypedAction.forward b] ∧
    (wordByClosureSufficient.realize b).1 = [TypedAction.forward b] :=
  ⟨rfl, rfl⟩

/-! ### The coding trick, refused (audit W3)

  The commuting-map half of the auditor's construction: a domain whose
  histories code into words and
  decode back has, for every transition, a map on states commuting with the
  encoding (decode, step, re-encode; `coding_has_a_commuting_map`).
  `flipDomain` is one such domain: two states and one transition that flips
  them. That map exists (`flip_has_a_commuting_map`), and before W3 it was an
  admissible item 2. Now the flip has no sufficiency term
  (`flipDomain_not_sufficient`): its typed realization would have to be empty,
  and the empty list does not flip. The
  same mechanics declared by its histories, the count of flips with the
  parity as the outcome, is sufficient (`toggleSufficient`). -/

/-- **Two states and a flip**: histories `Bool`, one transition `not`, `same`
    equality, the state read and observed as itself. -/
def flipDomain : Domain where
  History := Bool
  Transition := Unit
  Reading := Bool
  Quantity := Bool
  step := fun _ b => !b
  same := fun a b => a = b
  same_equiv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  project := id
  observe := id

/-- **The general coding construction** (the commuting-map half of audit W3's
    compiled counterexample to the unconstrained field). If the target's histories code into
      words and
    decode back, the map that reads the retained word, decodes, steps and
    re-encodes commutes with the encoding at every transition. It is a map on
    states; it is not a list of typed actions, and since W3 item 2 asks for
    one. -/
theorem coding_has_a_commuting_map (D : Domain) (code : D.History → Word)
    (decode : Word → D.History) (hd : ∀ h, decode (code h) = h) (t : D.Transition) :
    ∃ U : SubstrateState → SubstrateState,
      ∀ h : D.History, wordEncode (code (D.step t h)) = U (wordEncode (code h)) :=
  ⟨fun S => wordEncode (code (D.step t (decode S.word))), fun h => by
    change _ = wordEncode (code (D.step t (decode (code h))))
    rw [hd]⟩

/-- The coding: `false` as the empty word, `true` as `R`. -/
def flipEncode (b : Bool) : SubstrateState := wordEncode (if b then [true] else [])

/-- **A map commuting with the encoding exists**: read the retained word,
    flip, re-encode, the construction of `coding_has_a_commuting_map`
    (decode `[] ↦ false`, `[R] ↦ true`), proved directly. It was
    an admissible item 2 before audit W3. -/
theorem flip_has_a_commuting_map :
    ∃ U : SubstrateState → SubstrateState,
      ∀ b : flipDomain.History, flipEncode (flipDomain.step () b) = U (flipEncode b) :=
  ⟨fun S => flipEncode (S.word == []), fun b => by cases b <;> rfl⟩

/-- **No typed realization of the flip, so no sufficiency term.** The flip
    returns every state to itself in two steps, so its action list is empty
    (`realize_nil_of_two_cycle`) and the flip would move no outcome
    (`observe_step_of_two_cycle`); it moves every one. -/
theorem flipDomain_not_sufficient : IsEmpty (GenerativelySufficient flipDomain) :=
  ⟨fun G => by
    have : (!false) = false := G.observe_step_of_two_cycle () (h₀ := false) rfl false
    exact Bool.noConfusion this⟩

/-- **The flip declared by its histories**: a history is the number of flips
    so far, the transition adds one, `same` is equality, the reading is the
    retained word and the outcome its length mod 2, the current state. -/
def toggleDomain : Domain where
  History := ℕ
  Transition := Unit
  Reading := Word
  Quantity := ℕ
  step := fun _ n => n + 1
  same := fun a b => a = b
  same_equiv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  project := fun w => w.length % 2
  observe := fun n => n % 2

/-- **`toggleDomain` is generatively sufficient**: `n` flips are encoded as
    `Rⁿ`, the flip is one forward continuation by `R`, and the presented word's
    length mod 2 is the state. -/
def toggleSufficient : GenerativelySufficient toggleDomain where
  encode := fun n => wordEncode (List.replicate n true)
  realize := fun _ => ⟨wordRealize true, fun (n : ℕ) => by
    rw [run_wordRealize]
    change wordEncode (List.replicate (n + 1) true) =
      { wordEncode (List.replicate n true) with word := List.replicate n true ++ [true] }
    rw [List.replicate_succ']
    rfl⟩
  identify :=
    ⟨fun S T => S = T, fun (m n : ℕ) => by
      constructor
      · intro h
        change m = n at h
        subst h
        rfl
      · intro h
        have := congrArg (fun S => S.word.length) h
        simp only [wordEncode, List.length_replicate] at this
        exact this⟩
  equiv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  observers := [⟨Frame.empty, [], 0⟩]
  nonempty := ⟨_, List.mem_singleton_self _⟩
  reception := ObsReception.const presentedWordReception
  recovers := fun _ _ (n : ℕ) => by
    change (List.replicate n true).length % 2 = n % 2
    rw [List.length_replicate]

/-! ## Definition 15.2 — already built, and not rebuilt

  Def 15.2 is *"a family of relations is complete for a target class when its
  joint reception map is injective up to the target's declared equivalence."*
  That is `ReconstructivelySufficient` in `Perspective.lean`, built for Def 11.6
  on 2026-08-22 and restated by gap G1-21 (2026-09-26) over observer-perspective
  pairs, one encounter per observer, with the class `K` and the declared
  equivalence `C` over presented states exactly as §15.2 needs. §11.6 and §15.2
  are one predicate under two names, so this
  section is an alias and the record of that fact. -/

/-- **Definition 15.2**, as the name §15 uses. Definitionally `Def 11.6`: the
    joint map over observer-perspective pairs, each reading its own encounter
    with the presented state, injective up to the declared equivalence on the
    declared class (repointed with gap G1-21 from the one-record form). See
    `Gaps/G1_21.lean` for a family of two observers that is complete where
    neither alone is. -/
abbrev RelationallyComplete {n : ℕ} (Vs : Fin n → Viewpoint)
    (K : Observer → Prop) (C : Observer → Observer → Prop) : Prop :=
  ReconstructivelySufficient Vs K C

/-- The alias is not a new definition, and the checker agrees. -/
theorem relationally_complete_eq_11_6 {n : ℕ} (Vs : Fin n → Viewpoint)
    (K : Observer → Prop) (C : Observer → Observer → Prop) :
    RelationallyComplete Vs K C = ReconstructivelySufficient Vs K C := rfl

/-! ## Definition 15.2 for a domain (gap G1-27)

  Def 15.3 asks that relational completeness hold for each admissible
  mechanics, so Def 15.2 has to be read at a domain. The class is the encoded
  histories presented to the family (`presentedState (G.encode h)`), and the
  equivalence is the target's own `D.same`. Stated on histories:
  `𝒥(enc h) = 𝒥(enc h') ⇒ h ≡_𝒟 h'`. `completeFor_iff` shows this is
  `RelationallyComplete` itself, over the encoded class with the target's
  equivalence carried to presented states. -/

namespace GenerativelySufficient

variable {D : Domain} (G : GenerativelySufficient D)

/-- **Definition 15.2 at a domain.** The family `Vs` is complete for `D` under
    the encoding of `G` when equal joint readings of two encoded histories force
    the target to treat them as the same. Applied to `G.family` the readings are
    receptions, before projection ("joint reception map"); after projection,
    item 5 would make every observer's reading `D.observe` and the family would
    do no work. -/
def CompleteFor {n : ℕ} (Vs : Fin n → Viewpoint) : Prop :=
  ∀ h h' : D.History,
    joint Vs (presentedState (G.encode h)) = joint Vs (presentedState (G.encode h')) →
      D.same h h'

/-- The declared class: the presented states that encode a target history.
    It is the image of `G.encode`, so it depends on the sufficiency term, which
    Def 15.3 chooses after the domain. -/
def encodedClass (P : Presented) : Prop := ∃ h : D.History, P = presentedState (G.encode h)

/-- The target's declared equivalence carried to presented states: every pair
    of histories they encode is one the target treats as the same. `D.same` is
    an equivalence relation (`Domain.same_equiv`), and this one is symmetric,
    but it is reflexive on an encoded presented state only if every pair of
    histories encoded to it is one the target identifies (`presentedState`
    drops the active family and `H_τ`, so the encoding can merge there), and
    outside the encoded class it holds vacuously and is not transitive. So it
    is an equivalence on the encoded class exactly when completeness gives it
    one: `completeFor_iff` derives `EquivOn` from `CompleteFor`. -/
def declaredEquiv (P P' : Presented) : Prop :=
  ∀ h h' : D.History, P = presentedState (G.encode h) →
    P' = presentedState (G.encode h') → D.same h h'

/-- **`CompleteFor` is Definition 15.2**, the joint map injective up to the
    declared equivalence on the declared class, with the class and the
    equivalence the domain's. Since audit finding E1-B8 the right side also
    asks that the carried equivalence be one on the class (`EquivOn`); that
    half is not an extra assumption, it follows from completeness and
    `D.same_equiv`: two histories encoded to one presented state have equal
    joint readings, so completeness identifies them (reflexivity), and
    symmetry and transitivity are `D.same`'s, through a history encoded to
    the middle state. -/
theorem completeFor_iff {n : ℕ} (Vs : Fin n → Viewpoint) :
    G.CompleteFor Vs ↔ RelationallyComplete Vs G.encodedClass G.declaredEquiv := by
  constructor
  · intro hc
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rintro P ⟨h₀, rfl⟩ h h' hP hP'
      apply hc h h'
      rw [← hP, ← hP']
    · intro P P' _ _ hPP' h h' hP hP'
      exact D.same_equiv.symm (hPP' h' h hP' hP)
    · rintro P P' P'' _ ⟨h₁, hP₁⟩ _ h₁₂ h₂₃ h h'' hP hP''
      exact D.same_equiv.trans (h₁₂ h h₁ hP hP₁) (h₂₃ h₁ h'' hP₁ hP'')
    · rintro P P' ⟨h₀, rfl⟩ ⟨h₁, rfl⟩ hj h h' hP hP'
      rw [hP, hP'] at hj
      exact hc h h' hj
  · intro hr h h' hj
    exact hr.2 _ _ ⟨h, rfl⟩ ⟨h', rfl⟩ hj h h' rfl rfl

/-- **The family item 4 declares.** Each declared observer with its reception
    (Def 11.1), as a viewpoint reading into `D.Reading` (`Viewpoint.ofFamily`,
    identity projection): the joint of these is the term's own joint reception
    map. -/
def family : Fin G.observers.length → Viewpoint :=
  fun i => Viewpoint.ofFamily G.reception (fun _ => ⟨id⟩) (G.observers.get i)

/-- **Where the projection is injective the family does no work.** Item 5
    pins every declared observer's reception to the target's outcome, so
    completeness at the term's own family is `D.observe` separating `D.same`,
    for every term. (Adversarial review of G1-27.) -/
theorem complete_iff_of_project_injective (hp : Function.Injective D.project) :
    G.CompleteFor G.family ↔ ∀ h h', D.observe h = D.observe h' → D.same h h' := by
  constructor
  · intro hc h h' ho
    apply hc
    funext i
    apply hp
    have a := G.recovers _ (G.observers.get_mem i) h
    have b := G.recovers _ (G.observers.get_mem i) h'
    exact a.trans (ho.trans b.symm)
  · intro hs h h' hj
    obtain ⟨O, hO⟩ := G.nonempty
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hO
    apply hs
    rw [← G.recovers _ (G.observers.get_mem i) h, ← G.recovers _ (G.observers.get_mem i) h']
    exact congrArg D.project (congrFun hj i)

/-- **A family chosen apart from item 4 makes completeness a fact about the
    encoding alone.** Any family reading the presented word is complete as soon
    as the encoded words separate the target's equivalence, whatever the
    domain can read. This is why Def 15.3 asks it of `G.family`
    (adversarial review of G1-27). -/
theorem completeFor_presentedWord (hw : ∀ h h', (G.encode h).word = (G.encode h').word →
    D.same h h') {n : ℕ} (Vs : Fin n → Viewpoint) (i : Fin n)
    (hi : ∀ P P', (Vs i).read P = (Vs i).read P' ↔ P.word = P'.word) :
    G.CompleteFor Vs := by
  intro h h' hj
  exact hw h h' ((hi _ _).mp (congrFun hj i))

end GenerativelySufficient

/-! ## Definition 15.3 — the universal claim, defined and left unproved -/

/-- **Definition 15.3.** *"A universal RatioSpace claim is the assertion that
    generative sufficiency and relational completeness hold for every finitely
    distinguishable admissible mechanics under consideration."*

    `Admissible` is "the mechanics under consideration"; "finitely
    distinguishable" has no counterpart here and is left to it. The
    completeness half is Def 15.2 at the domain (`CompleteFor`, which is
    `RelationallyComplete` by `completeFor_iff`) asked of the sufficiency
    term's own receptions (`G.family`, gap G1-27): the relations that
    reproduce the target's quantities must, jointly, tell apart what the
    target keeps apart. What those receptions may read is bounded by the
    domain's declared `Reading`, not its `Quantity`: item 5 constrains only
    their projection. A family chosen separately would be bounded by nothing
    the domain declares (`completeFor_presentedWord`). So the claim is only as
    strong as each domain's declared `Reading`, as it is only as strong as the
    admissible class: a domain whose reading carries enough of the presented
    word passes (`Gaps/G1_27.lean`, `g127_rich_claim`).

    **A definition, with each instance its own construction.** The book states
    the claim (Definition 15.3) and leaves its proof for any class to the
    constructions of Definition 15.1. -/
def UniversalGenerativeClaim (Admissible : Domain → Prop) : Prop :=
  ∀ D : Domain, Admissible D → ∃ G : GenerativelySufficient D, G.CompleteFor G.family

/-- **The pre-G1-27 form**, kept under its own name: completeness as an
    arbitrary predicate, tied to nothing in Def 15.2. The pre-G1-27 word-domain
    theorem took it `True`: `universal_claim_over_holds_on_wordByClosureDomain`. -/
def UniversalGenerativeClaimOver
    (Admissible : Domain → Prop)
    (Complete : ∀ D : Domain, GenerativelySufficient D → Prop) : Prop :=
  ∀ D : Domain, Admissible D → ∃ G : GenerativelySufficient D, Complete D G

/-- The claim is the old form with `Complete` fixed to Def 15.2 at the term's
    own family. -/
theorem universalGenerativeClaim_eq_over (Admissible : Domain → Prop) :
    UniversalGenerativeClaim Admissible =
      UniversalGenerativeClaimOver Admissible (fun _ G => G.CompleteFor G.family) := rfl

/-- **The claim is exactly as strong as `Admissible`, and no stronger.**

    Take the empty class of admissible mechanics and the whole thing is provable
    in one line, with no encoding, no correspondence and no reconstruction
    result anywhere in sight. So the content of a universal claim lives entirely
    in which mechanics are declared admissible, and a stated universality with a
    vague class attached says nothing at all.

    This is the book's *"not a slogan"* warning with a proof attached, and it is
    the reason Def 15.3 is a definition rather than a theorem. -/
theorem universal_claim_is_only_as_strong_as_its_class :
    UniversalGenerativeClaim (fun _ => False) := by
  intro _ h
  exact absurd h not_false

/-! ### Read by its closure record the word domain fails it; read as words, or
    with closure-record identity, it meets it -/

/-- **The word domain read by its closure record is not complete, for any
    sufficiency term.** Item 5 forces every declared observer's reading of an
    encoded word to be its closure record, and the domain declares words equal only when they
    are equal: the empty word and `R^12` have one closure record. The
    domain's accessible quantity does not separate its declared equivalence.
    (Adversarial review of G1-27.) -/
theorem wordByClosureDomain_not_complete (G : GenerativelySufficient wordByClosureDomain) :
    ¬ G.CompleteFor G.family := by
  intro h
  have := h [] (List.replicate 12 true) (by
    funext i
    have h1 := G.recovers _ (G.observers.get_mem i) []
    have h2 := G.recovers _ (G.observers.get_mem i) (List.replicate 12 true)
    change G.reception.receive _ _ = G.reception.receive _ _
    exact h1.trans ((show ClosureState.ofWord [] =
      ClosureState.ofWord (List.replicate 12 true) from rfl).trans h2.symm))
  change ([] : Word) = List.replicate 12 true at this
  exact absurd this (by decide)

/-- So the claim over the closure-read word domain alone is false. -/
theorem universal_claim_fails_on_wordByClosureDomain :
    ¬ UniversalGenerativeClaim (fun D => D = wordByClosureDomain) := by
  intro hc
  obtain ⟨G, hG⟩ := hc wordByClosureDomain rfl
  exact wordByClosureDomain_not_complete G hG

/-- The target that treats two words as the same when it cannot read them
    apart: the closure-read word domain with `same` the equality of closure
    records. Its
    projection is the identity, so completeness holds for every term by
    `complete_iff_of_project_injective`: this is the trivial case, a witness
    that the claim can be met on an inhabited class and nothing deeper. -/
def closureDomain : Domain :=
  { wordByClosureDomain with
    same := fun u v => ClosureState.ofWord u = ClosureState.ofWord v
    same_equiv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩ }

/-- **`closureDomain` is generatively sufficient**, with any non-empty list of
    declared observers: the word witness with the equivalence identifying
    encoded states by their closure record. -/
def closureSufficientAt (Os : List Observer) (hOs : ∃ O, O ∈ Os) :
    GenerativelySufficient closureDomain where
  encode := wordEncode
  realize := fun t => ⟨wordRealize t, fun _ => rfl⟩
  identify :=
    ⟨fun S T => S.closure = T.closure, fun (u v : Word) => by
      change ClosureState.ofWord u = ClosureState.ofWord v ↔
        ClosureState.of Frame.empty u = ClosureState.of Frame.empty v
      rw [ClosureState.of_empty, ClosureState.of_empty]⟩
  equiv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  observers := Os
  nonempty := hOs
  reception := ObsReception.const presentedClosureReception
  recovers := fun _ _ w => ClosureState.of_empty w

/-- The witness with one observer at the root. -/
def closureSufficient : GenerativelySufficient closureDomain :=
  closureSufficientAt [⟨Frame.empty, [], 0⟩] ⟨_, List.mem_singleton_self _⟩

/-- **`closureDomain` is complete for its own receptions**, at any non-empty
    list of declared observers: each reads the closure record, and the target
    identifies exactly what shares one. -/
theorem closureSufficientAt_complete (Os : List Observer) (hOs : ∃ O, O ∈ Os) :
    (closureSufficientAt Os hOs).CompleteFor (closureSufficientAt Os hOs).family := by
  intro (u : Word) (v : Word) hj
  obtain ⟨O, hO⟩ := hOs
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hO
  have := congrFun hj i
  change ClosureState.of Frame.empty u = ClosureState.of Frame.empty v at this
  rw [ClosureState.of_empty, ClosureState.of_empty] at this
  exact this

/-- **The claim holds on the closure domain**, both halves supplied from one
    term: sufficiency by `closureSufficient`, completeness by its own
    receptions. One domain is not universality; the empty-class theorem above
    shows the quantifier can dodge the work, and this shows it can do it. -/
theorem universal_claim_holds_on_the_closure_domain :
    UniversalGenerativeClaim (fun D => D = closureDomain) := by
  intro D hD
  subst hD
  exact ⟨closureSufficient, closureSufficientAt_complete _ _⟩

/-- **The word domain is complete for its own receptions**, at any non-empty
    list of declared observers: each reads the presented word, which is the
    encoded word, and the target identifies exactly equal words. -/
theorem wordSufficientAt_complete (Os : List Observer) (hOs : ∃ O, O ∈ Os) :
    (wordSufficientAt Os hOs).CompleteFor (wordSufficientAt Os hOs).family := by
  intro (u : Word) (v : Word) hj
  obtain ⟨O, hO⟩ := hOs
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hO
  exact congrFun hj i

/-- **The claim holds on the word domain**, words read as words, both halves from one term.
    An easy case, like `closureDomain`: the reading is the word, so completeness is one step. -/
theorem universal_claim_holds_on_the_word_domain :
    UniversalGenerativeClaim (fun D => D = wordDomain) := by
  intro D hD
  subst hD
  exact ⟨wordSufficient, wordSufficientAt_complete _ _⟩

/-- The pre-G1-27 statement on the closure-read word domain, with completeness taken
    `True`. Under Def 15.2 it fails (`universal_claim_fails_on_wordByClosureDomain`). -/
theorem universal_claim_over_holds_on_wordByClosureDomain :
    UniversalGenerativeClaimOver (fun D => D = wordByClosureDomain) (fun _ _ => True) := by
  intro D hD
  subst hD
  exact ⟨wordByClosureSufficient, trivial⟩

/-- **A cycle forces every realizing sequence to be empty, even when the
    sequence may depend on the history.** If each target step is realized at
    history `h` by a list of typed actions `seq h` (any function of `h`), and
    the target returns `h` to itself after `n` steps, then every sequence used
    on the way is empty: each action adds one letter
    (`TypedAction.run_word_length`), and the word comes back to its length. -/
theorem history_dependent_cycle_is_empty {H : Type} (step : H → H)
    (enc : H → SubstrateState) (seq : H → List TypedAction)
    (hcomm : ∀ h, enc (step h) = TypedAction.run (seq h) (enc h))
    (n : ℕ) (h : H) (hc : step^[n] h = h) :
    ∀ i < n, seq (step^[i] h) = [] := by
  have key : ∀ k, (enc (step^[k] h)).word.length
      = (enc h).word.length + ((List.range k).map (fun i => (seq (step^[i] h)).length)).sum := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', hcomm, TypedAction.run_word_length, ih,
        List.range_succ, List.map_append, List.sum_append]
      simp
      omega
  have hsum := key n
  rw [hc] at hsum
  have h0 : ((List.range n).map (fun i => (seq (step^[i] h)).length)).sum = 0 := by omega
  intro i hi
  have hmem : (seq (step^[i] h)).length ∈ (List.range n).map (fun i => (seq (step^[i] h)).length) :=
    List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  have hle := List.le_sum_of_mem hmem
  exact List.eq_nil_of_length_eq_zero (by omega)

#print axioms history_dependent_cycle_is_empty

end Layer
end RatioSpace
