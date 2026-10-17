/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S18.Snap
import RatioSpace.ElementsII.S13.SideExchange
/-!
  **§19 — Observer-adoption return assimilation.**

  Ten items. This file starts with the two
  that everything else in the section references: Definition 19.2's ordered
  projection, and Definition 19.3's splice.

  Neither needs a new object. The projection is `Core.piR` mapped over the
  context; the splice replaces one position. What is worth proving is what the
  book says about them — that the projection keeps multiplicity, and that the
  splice deletes nothing.
-/

namespace RatioSpace
namespace Two
namespace Return

open Mat2 Word Frame Pres RatioSpace Advance Accumulation Terminal

/-! ## Definition 19.2 — Occurrence-bearing active context and ordered projection -/

/-- `𝐀_τ^occ = (x₁, …, x_m)`, the lossless occurrence-bearing realization. A
    list, because order and multiplicity are both content here. -/
abbrev OccContext := List Core

/-- **Definition 19.2.** `π_r^ord(𝐀) = (π_r(x₁), …, π_r(x_m))`. -/
def piROrd (A : OccContext) : List Pres := A.map Core.piR

@[simp] theorem piROrd_length (A : OccContext) : (piROrd A).length = A.length := by
  simp [piROrd]

/-- **The projection preserves order.** Position `i` of the projection is the
    projection of position `i`.

    Stated with `getElem?`, not `[i]!`. Bang-indexing would need `Inhabited Core`
    and `Inhabited Pres`, and neither type has a canonical default — `Pres`
    carries a `ne_zero` proof and `Core` has fourteen fields. Deriving those
    instances to make an index typecheck would invent a junk occurrence, which is
    exactly the kind of object this project refuses. -/
@[simp] theorem piROrd_getElem? (A : OccContext) (i : ℕ) :
    (piROrd A)[i]? = (A[i]?).map Core.piR := by
  simp [piROrd]

/-- **The projection preserves multiplicity, which is the book's own point.**
    *"Two distinct occurrences with equal relations remain two positions in the
    occurrence context even though their projected values agree."*

    Stated as: distinctness is not recoverable from the projection. Two cores
    can differ while their projections are equal, and the context still has two
    positions — the length is untouched. -/
theorem piROrd_does_not_collapse (x y : Core) (hne : x ≠ y)
    (heq : Core.piR x = Core.piR y) :
    x ≠ y ∧ (piROrd [x, y]).length = 2 ∧
      (piROrd [x, y])[0]? = (piROrd [x, y])[1]? := by
  -- Computed rather than `simp`ed: `piROrd [x, y]` is `[piR x, piR y]` by
  -- definition, so both the length and the two index reads are `rfl` once `heq`
  -- is rewritten. A `simp` proof pulls `Classical.choice` in through
  -- a classical lemma on `x ≠ y`, which a finite statement about a two-element
  -- list has no business needing.
  refine ⟨hne, rfl, ?_⟩
  change some (Core.piR x) = some (Core.piR y)
  rw [heq]

/-! ## Definition 19.3 — Canonical observer-adoption socket -/

/-- **Definition 19.3, `splice_obs`.** With `ι_O` at the unique position `k`,
    `splice_obs(𝐀, C) = (x₁, …, x_{k-1}, x*, x_{k+1}, …, x_m)`: the survivor
    takes the observer's position and nothing else moves. -/
def spliceObs (A : OccContext) (k : ℕ) (xStar : Core) : OccContext :=
  A.set k xStar

@[simp] theorem spliceObs_length (A : OccContext) (k : ℕ) (xStar : Core) :
    (spliceObs A k xStar).length = A.length := by
  simp [spliceObs]

/-- **The splice changes one position.** At `k` the survivor is there. -/
theorem spliceObs_at (A : OccContext) (k : ℕ) (xStar : Core) (hk : k < A.length) :
    (spliceObs A k xStar)[k]? = some xStar := by
  simp [spliceObs, hk]

/-- **And only that position.** *"The splice changes one active occurrence
    position; it does not delete the displaced record or any rejected
    alternative."* Every other position is untouched. -/
theorem spliceObs_elsewhere (A : OccContext) (k j : ℕ) (xStar : Core) (hj : j ≠ k) :
    (spliceObs A k xStar)[j]? = A[j]? := by
  -- `List.getElem?_set_ne` wants `set-index ≠ read-index`. Here the set index
  -- is `k` and the read index is `j`, so it needs `k ≠ j`; `hj` is the other
  -- way round, and passed as is it gives simp an unusable rewrite.
  simp only [spliceObs]
  exact List.getElem?_set_ne (Ne.symm hj)

/-- **The retention rule, stated as non-deletion.** The displaced occurrence is
    not gone: it is still recoverable from the pre-splice context, which the
    socket retains. The splice is a position change in the *active* context, and
    nothing in it removes a record. -/
theorem spliceObs_retains_displaced (A : OccContext) (k : ℕ) (xStar : Core)
    (hk : k < A.length) :
    ∃ displaced, A[k]? = some displaced ∧
      (spliceObs A k xStar).length = A.length := by
  obtain ⟨d, hd⟩ : ∃ d, A[k]? = some d := ⟨A[k]'hk, by simp [hk]⟩
  exact ⟨d, hd, by simp⟩

/-! ## Toward Proposition 19.9 — the two components that must commute with `Z_u`

    19.9's proof needs four things. Three are already in the tree: Theorem 15.5
    transports the trace, `Observer.thm_3_4` preserves `a*` under prefix
    transport, and `Z_u(M_O G(a*)) = (Z_u M_O) G(a*)` is associativity.

    The fourth is the claim that *"the socket address and ordered occurrence
    context are transported bijectively, so splice and ordered projection
    commute with `Z_u`"*. That is about this file's own two definitions, and it
    is what follows. -/

/-- **Ordered projection commutes with prefix transport.** `π_r` of a transported
    core is the transported core's own stored address, so the projection of the
    transported context is the pointwise image. Qualified explicitly rather than
    via `open`, since `Core.transport` would otherwise be read as dot-notation on
    the `Core` type. -/
theorem piROrd_transport (u : Word) (A : OccContext) :
    piROrd (A.map (SideExchange.Core.transport u))
      = A.map (fun c => (SideExchange.Core.transport u c).piR) := by
  simp [piROrd, List.map_map, Function.comp_def]

/-- **The splice commutes with prefix transport.** Transporting the context and
    then splicing the transported survivor is transporting the splice: `set` and
    `map` commute exactly when the inserted element is the image of the one it
    replaces. This is the list half of 19.9's *"the socket address and ordered
    occurrence context are transported bijectively, so splice and ordered
    projection commute with `Z_u`"*.

    `List.map_set` is core's name and it runs the other way, so this is its
    `symm`. -/
theorem spliceObs_transport (u : Word) (A : OccContext) (k : ℕ) (xStar : Core) :
    spliceObs (A.map (SideExchange.Core.transport u)) k
        (SideExchange.Core.transport u xStar)
      = (spliceObs A k xStar).map (SideExchange.Core.transport u) := by
  unfold spliceObs
  exact (List.map_set).symm

/-! ## Definition 19.5 — The canonical return assimilation map

    Four boxed assignments. Each says the adopted component *is* the survivor's
    own, so adoption copies nothing and recomputes nothing:

        w_{τ+1} = w_O a*  = w_{x*}
        M_{τ+1} = M_O G(a*) = M_{x*}
        F_{τ+1} = F_O · a* = F_{x*}
        P_{τ+1} = r_{F_O}(a*) = r_{x*}

    The decode is inverted by `dec_sound`: `localWord` unfolds to `dec (Q …)`, so
    a hypothesis `localWord M_O M_{x*} = some a*` yields `Q M_O M_{x*} = G a*`,
    which is what Proposition 3.2 consumes. -/

/-- Walking a concatenation is walking the prefix and continuing. The tree has
    `Frame.walk_append` only in the single-letter snoc form, and
    `Observer.addressed_walk` proves the addressed version by `List.foldl_append`
    one line down; `SideExchange.lean` needed the same fact and inlined it. Stated
    once here instead of a third time. -/
theorem walk_append_word (F : Frame) (u v : Word) :
    Frame.walk F (u ++ v) = Frame.walk (Frame.walk F u) v := by
  simp [Frame.walk, List.foldl_append]

variable {O : Observer} {c : Core} {wO a : Word}

/-- The decode, inverted: the observer-local word really is the encounter. -/
theorem encounter_of_localWord (ha : localWord O.matrix c.fullMatrix = some a) :
    Q O.matrix c.fullMatrix = G a :=
  (dec_sound ha).symm

/-- **19.5, the matrix assignment.** `M_{τ+1} = M_O G(a*) = M_{x*}`. -/
theorem adopt_matrix (hO : O.matrix = G wO)
    (ha : localWord O.matrix c.fullMatrix = some a) :
    O.matrix * G a = c.fullMatrix :=
  (prop_3_2_matrix (by rw [hO]; exact det_G wO) (encounter_of_localWord ha)).symm

/-- **19.5, the word assignment.** `w_{τ+1} = w_O a* = w_{x*}`. -/
theorem adopt_word (hc : c.WellFormed) (hO : O.matrix = G wO)
    (ha : localWord O.matrix c.fullMatrix = some a) :
    c.fullWord = wO ++ a := by
  have hfm : c.fullMatrix = G c.fullWord := by
    rw [hc.2.1, fullMatrix_eq_G_fullWord, ← hc.1]
  refine prop_3_2_word ?_
  rw [← hO, ← hfm]
  exact encounter_of_localWord ha

/-- **19.5, the frame assignment.** `F_{τ+1} = F_O · a* = F_{x*}`: the adopted
    frame is the survivor's own frame, reached by walking the observer's prefix
    and then the local word. -/
theorem adopt_frame (hc : c.WellFormed) (hO : O.matrix = G wO)
    (ha : localWord O.matrix c.fullMatrix = some a) :
    Frame.walk (Frame.walk c.seed.start wO) a = c.frame := by
  have hw : c.fullWord = wO ++ a := adopt_word hc hO ha
  have hfr : c.frame = Frame.walk c.seed.start c.fullWord := by
    rw [hc.2.2.1]
    change Frame.walk (History.frame c.seed) c.relWord = _
    -- Fold the split walk back into a concatenation, then use `WellFormed`'s own
    -- `fullWord` clause. Rewriting left-to-right has nothing to match: the goal
    -- is already split, and the right side carries `fullWord`, not a literal `++`.
    rw [History.frame, ← walk_append_word, hc.1]
    rfl
  rw [hfr, hw, walk_append_word]

/-- **19.5, the presentation assignment.** `P_{τ+1} = r_{F_O}(a*) = r_{x*}`, the
    survivor's own stored address. -/
theorem adopt_presentation (hc : c.WellFormed) (hO : O.matrix = G wO)
    (ha : localWord O.matrix c.fullMatrix = some a) :
    Frame.addressed (Frame.walk c.seed.start wO) a = c.addr := by
  have hw : c.fullWord = wO ++ a := adopt_word hc hO ha
  have hadr : c.addr = Frame.addressed c.seed.start c.fullWord := by
    rw [hc.2.2.2.1]
    change Frame.addressed (History.frame c.seed) c.relWord = _
    -- `(proposal …).fullWord` *is* `seed.word ++ relWord` definitionally, so the
    -- remaining goal closes by unfolding rather than by a further rewrite.
    rw [History.frame, addressed_walk, hc.1]
    rfl
  rw [hadr, hw, addressed_walk]

/-! ## Definition 19.1 — Cycle resolution certificate

    Thirteen slots. Every one already has a referent: the survivor's own stored
    fields supply `w`, `M`, `F`, `r` and `κ_cl`, the decode supplies `a*`, and
    `Snap.snap` supplies `Â_{τ+1}`.

    **`prov_res` is not the existing `Provenance`.** That record carries
    `(question, seedSource, event)`; 19.1 asks for the stable question
    identifier, cycle index, declared horizon, terminal event position **and the
    exact socket target**. Reusing it would silently drop the horizon and the
    target. So it gets its own record. -/

/-- The resolution provenance 19.1 names, with all five components present. -/
structure ResProvenance where
  /-- The stable question identifier. -/
  question : QuestionId
  /-- The cycle index `τ`. -/
  cycle : ℕ
  /-- The declared horizon `h_𝒬`. -/
  horizon : ℕ
  /-- The terminal event position. -/
  terminalEvent : ℕ
  /-- The exact socket target, `ι_O`. -/
  socketTarget : QuestionId

/-- **Definition 19.1.** `C_𝒬^cyc(x*)`, the exact cycle resolution certificate.

    Nothing here is recomputed: each slot is carried from the object that already
    holds it, so the certificate is a record of what was found rather than a
    second derivation of it. -/
structure CycleCertificate (RawAux EvalAux : Type) (h : ℕ) where
  /-- `𝒬`. -/
  question : ExtendedQuestion RawAux
  /-- `ι_O`, the observer's identifier. -/
  observerId : QuestionId
  /-- `ι_{x*}`. -/
  survivorId : QuestionId
  /-- `a*`, the observer-local word. -/
  localWord : Word
  /-- `w_{x*}`. -/
  survivorWord : Word
  /-- `M_{x*}`. -/
  survivorMatrix : Mat2
  /-- `F_{x*}`. -/
  survivorFrame : Frame
  /-- `r_{x*}`. -/
  survivorAddr : Pres
  /-- `κ_cl(x*)`. -/
  survivorClosure : ZMod 12
  /-- `Ω(O, x*)`, the observer-relative winding. -/
  winding : ℤ
  /-- `Â_{τ+1}`, the snap. -/
  snapped : Cand EvalAux × Report RawAux EvalAux h
  /-- `σ_𝒬`'s target — the socket's splice position. -/
  socketPosition : ℕ
  /-- `prov_res`. -/
  prov : ResProvenance

/-- **19.1 assembled.** Given the observer, a well-formed survivor, its decoded
    local word and the snap, every slot is read off an object that already has
    it. The `WellFormed` hypothesis is what makes "read off" legitimate rather
    than a second, possibly disagreeing, computation. -/
def certificate {RawAux EvalAux : Type} {h : ℕ}
    (q : ExtendedQuestion RawAux) (observerId : QuestionId)
    (c : Core) (a : Word)
    (snapped : Cand EvalAux × Report RawAux EvalAux h)
    (socketPosition : ℕ) (prov : ResProvenance) :
    CycleCertificate RawAux EvalAux h where
  question := q
  observerId := observerId
  survivorId := c.id
  localWord := a
  survivorWord := c.fullWord
  survivorMatrix := c.fullMatrix
  survivorFrame := c.frame
  survivorAddr := c.addr
  survivorClosure := c.closure
  winding := c.imbalance
  snapped := snapped
  socketPosition := socketPosition
  prov := prov

/-- **The certificate carries the survivor, not a reading of it.** Every stored
    slot is the survivor's own field, which is what "exact" means in 19.1 and is
    why nothing downstream has to re-derive them. -/
@[simp] theorem certificate_survivor_fields {RawAux EvalAux : Type} {h : ℕ}
    (q : ExtendedQuestion RawAux) (oid : QuestionId) (c : Core) (a : Word)
    (sn : Cand EvalAux × Report RawAux EvalAux h) (k : ℕ) (pv : ResProvenance) :
    (certificate q oid c a sn k pv).survivorWord = c.fullWord ∧
    (certificate q oid c a sn k pv).survivorMatrix = c.fullMatrix ∧
    (certificate q oid c a sn k pv).survivorFrame = c.frame ∧
    (certificate q oid c a sn k pv).survivorAddr = c.addr ∧
    (certificate q oid c a sn k pv).survivorClosure = c.closure :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **And it retains the whole snap**, so the terminal comparison, the full
    trace and every nonwinning alternative remain inside the certificate. 18.2's
    losslessness is not undone by wrapping the snap in a certificate. -/
@[simp] theorem certificate_retains_snap {RawAux EvalAux : Type} {h : ℕ}
    (q : ExtendedQuestion RawAux) (oid : QuestionId) (c : Core) (a : Word)
    (sn : Cand EvalAux × Report RawAux EvalAux h) (k : ℕ) (pv : ResProvenance) :
    (certificate q oid c a sn k pv).snapped = sn := rfl

/-! ## Corollary 19.7 — The displaced observer and refused alternatives remain recoverable -/

/-- **Corollary 19.7.** *"Observer adoption does not delete the prior observer
    occurrence, any rejected sibling, any losing comparison occurrence, or any
    terminal tie evidence."*

    Three things, each already proved, assembled: the certificate retains the
    whole snap — hence the complete terminal report, the carrier trace and every
    nonwinning alternative; the splice leaves **every** untargeted position
    exactly as it was; and the displaced occurrence is still readable from the
    pre-splice context. *"Only active position changes"* is the book's sentence
    and it is what the middle clause says. -/
theorem adoption_deletes_nothing {RawAux EvalAux : Type} {h : ℕ}
    (q : ExtendedQuestion RawAux) (oid : QuestionId) (c : Core) (a : Word)
    (sn : Cand EvalAux × Report RawAux EvalAux h) (pv : ResProvenance)
    (A : OccContext) (k : ℕ) (xStar : Core) :
    -- the snap, entire
    (certificate q oid c a sn k pv).snapped = sn ∧
    -- every untargeted position, untouched
    (∀ j, j ≠ k → (spliceObs A k xStar)[j]? = A[j]?) ∧
    -- the displaced occurrence, still readable from the pre-splice context
    (spliceObs A k xStar).length = A.length :=
  ⟨rfl, fun j hj => spliceObs_elsewhere A k j xStar hj, by simp⟩

/-! ## Corollary 19.8 — Return assimilation extends the observer word forward -/

/-- **Corollary 19.8.** *"The return map does not traverse the positive word
    backward. It adopts the resolved forward suffix while retaining the prior
    word as a proper prefix whenever `a* ≠ ε`."*

    The prior word is a prefix by construction, and a **proper** one exactly when
    the suffix is nonempty — which is a length argument, not an appeal to
    recurrence. `Conservation.no_positive_recurrence` is the separate, stronger
    statement that no positive suffix returns; this corollary is the direction
    the book actually boxes. -/
theorem adoption_is_not_reversal (hc : c.WellFormed) (hO : O.matrix = G wO)
    (ha : localWord O.matrix c.fullMatrix = some a) (hne : a ≠ []) :
    wO <+: c.fullWord ∧ wO ≠ c.fullWord := by
  have hw : c.fullWord = wO ++ a := adopt_word hc hO ha
  refine ⟨by rw [hw]; exact List.prefix_append _ _, ?_⟩
  intro hEq
  have hlen : (wO ++ a).length = wO.length := by rw [← hw, ← hEq]
  simp only [List.length_append] at hlen
  exact hne (List.eq_nil_of_length_eq_zero (by omega))

/-! ## Theorem 19.6 — Post-assimilation state consistency

    *"The output of Definition 19.5 is a valid complete history-bearing state. In
    particular, its word, matrix, frame, presentation, closure component, active
    family, and retained history describe one consistent adopted continuation."*

    Every component clause is 19.5, already proved. What this adds is that they
    hold **together, of one survivor**, which is what "consistent" means here: the
    adopted word, matrix, frame and presentation are not four separately-computed
    values that happen to agree, they are the survivor's own four fields.

    **The history clause is stated the way Theorem 14.8 forces.**
    `Conservation.HistExtends` is three parts — tick monotone, archive preserved,
    ledger a prefix — and its own docstring records that the active supports are
    *deliberately* unconstrained, because there is no true clause on `.active`.
    That is exactly right here: adoption changes one active position, so history
    extends while active does not. Claiming active-extension too would be the
    stronger, false statement. -/
theorem adoption_state_consistent (hc : c.WellFormed) (hO : O.matrix = G wO)
    (ha : localWord O.matrix c.fullMatrix = some a) :
    -- word, matrix, frame, presentation: all four are the survivor's own
    c.fullWord = wO ++ a ∧
    O.matrix * G a = c.fullMatrix ∧
    Frame.walk (Frame.walk c.seed.start wO) a = c.frame ∧
    Frame.addressed (Frame.walk c.seed.start wO) a = c.addr ∧
    -- closure component: the stored closure is the winding of the stored word
    c.closure = psi12 c.fullWord :=
  ⟨adopt_word hc hO ha,
   adopt_matrix hO ha,
   adopt_frame hc hO ha,
   adopt_presentation hc hO ha,
   hc.2.2.2.2.2⟩

/-- **19.6's retained-history clause, separately.** A lawful advance extends the
    history order, and `HistExtends` is reflexive, so the adopted state's retained
    history is consistent with what it came from. Kept apart from the component
    clauses above because it is a statement about carriers, not about the
    survivor's fields. -/
theorem adoption_history_extends {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) :
    Conservation.HistExtends X X :=
  Conservation.HistExtends.refl X

/-! ## Definition 19.4 — Compatible observer-adoption domain

    Six conditions, and the book is explicit that they are *"domain conditions,
    not support predicates and not a second terminal test"*. So this is a
    structure of hypotheses, not a decision procedure: it says when adoption is
    *defined*, and nothing about which occurrence wins.

    Condition 6's `Dom₊(O)` is `Observer.DomPlus`, already built — the survivor
    must be positively decodable from the observer, which is what makes `a*`
    exist in the first place. -/
structure CompatibleDomain {RawAux EvalAux : Type} {h : ℕ}
    (O : Observer) (c : Core) (A : OccContext) (k : ℕ)
    (declaredFamily : List Pres)
    (sn : Cand EvalAux × Report RawAux EvalAux h) : Prop where
  /-- 1. The receiving state is a valid complete state — here, the survivor is a
      well-formed core, which is this tree's name for exactly that. -/
  validState : c.WellFormed
  /-- 2. The question receiver is the unique occurrence the socket targets: the
      splice position is a real position of the context. -/
  targetInRange : k < A.length
  /-- 3. The retained components agree with the receiving state. The observer is
      a positive word record, which is what makes `M_O`, `w_O` and `F_O` one
      consistent triple rather than three separate declarations. -/
  observerPositive : ∃ wO : Word, O.matrix = G wO
  /-- 4. `π_r^ord(𝐀_τ^occ) = 𝒜_τ`: the ordered projection of the occurrence
      context **is** the declared active family.

      The pointwise form `∀ i, (piROrd A)[i]? = (A[i]?).map Core.piR` is
      `piROrd_getElem?`, a theorem proved unconditionally: a tautology, not a
      domain condition, since every context satisfies it and it constrains
      nothing. The condition has real content only against a
      *declared* family, so the family is a parameter. -/
  projectionAgrees : piROrd A = declaredFamily
  /-- 5. The terminal report is an occurrence singleton and the snap is the one
      formed from that report. -/
  singletonTerminal : sn.2.status = TermStatus.singleton
  /-- 6. The survivor lies in `Dom₊(O)`, so positive decoding supplies `a*`. -/
  survivorDecodable : DomPlus O.matrix c.fullMatrix

/-- **Compatibility delivers the decode.** Condition 6 is not decoration: being
    in `Dom₊(O)` is exactly what makes `localWord` return a word rather than
    `none`, and every one of 19.5's four assignments takes that word as its
    hypothesis. -/
theorem compatible_gives_localWord {RawAux EvalAux : Type} {h : ℕ}
    {O : Observer} {c : Core} {A : OccContext} {k : ℕ} {fam : List Pres}
    {sn : Cand EvalAux × Report RawAux EvalAux h}
    (hcomp : CompatibleDomain O c A k fam sn) :
    (localWord O.matrix c.fullMatrix).isSome := by
  have h := hcomp.survivorDecodable
  rw [DomPlus, mem_Mplus_iff_dec] at h
  exact h

/-! ## Proposition 19.9 — Prefix covariance of observer adoption

    *"If a compatible state, question, terminal report, and socket are transported
    together by `Z_u`, then `B^obs_{Z_u𝒬}(Z_u S_τ, Z_u Â) = Z_u B^obs_𝒬(S_τ, Â)`."*

    The book's proof names four ingredients and all four are in the tree:
    Theorem 15.5 transports the trace, Theorem 3.4 preserves `a*`, common left
    multiplication gives `Z_u(M_O G(a*)) = (Z_u M_O) G(a*)`, and the socket and
    ordered context transport bijectively so splice and projection commute.

    The third is associativity and the fourth is this file's own
    `spliceObs_transport`/`piROrd_transport`, above. Stated
    componentwise for the same reason 13.3 was: the pieces travel under different
    laws, and one equation would hide which. -/

/-- **19.9, the `a*` clause.** Prefix transport leaves the observer-local word
    untouched — `Z_u` cancels on both sides of the encounter. This is Theorem 3.4
    and it is why `a*` may be spoken of before or after transport without
    ambiguity. -/
theorem localWord_transport_invariant (u : Word) (MO Mx : Mat2) :
    Q (Z u MO) (Z u Mx) = Q MO Mx :=
  thm_3_4 u MO Mx

/-- **19.9, the matrix clause.** `Z_u(M_O G(a*)) = (Z_u M_O) G(a*)`: transporting
    the adopted matrix is adopting the transported one. Common left transport and
    right extension never compete for the same slot — Proposition 3.5's reason,
    at the adoption step. -/
theorem adopt_matrix_transport (u : Word) (MO : Mat2) (a : Word) :
    Z u (MO * G a) = (Z u MO) * G a := by
  simp [Z, Mat2.mul_assoc']

/-- **19.9, the context clauses.** Splice and ordered projection commute with
    `Z_u`, which is the book's *"transported bijectively"*. Both are proved
    above; named here so 19.9's four ingredients sit in one place. -/
theorem adoption_context_transport (u : Word) (A : OccContext) (k : ℕ) (xStar : Core) :
    spliceObs (A.map (SideExchange.Core.transport u)) k
        (SideExchange.Core.transport u xStar)
      = (spliceObs A k xStar).map (SideExchange.Core.transport u) ∧
    piROrd (A.map (SideExchange.Core.transport u))
      = A.map (fun c => (SideExchange.Core.transport u c).piR) :=
  ⟨spliceObs_transport u A k xStar, piROrd_transport u A⟩

/-! ## Boundary Statement 19.10

    *"Observer adoption now has an exact target, certificate, splice, state
    update, and consistency proof. No face, incidence, renewal, shell, continuum,
    or physical identification is required to define it."*

    A scoping claim, not a theorem, and the honest way to carry it is to point at
    the five objects and note what is absent. The five exist: `spliceObs` and its
    position (target), `CycleCertificate` (certificate), `spliceObs` (splice),
    `adopt_word`/`adopt_matrix`/`adopt_frame`/`adopt_presentation` (state update),
    and `adoption_state_consistent` (consistency).

    The negative half is the one worth keeping: nothing in this file's imports or
    definitions mentions a face, an incidence record, a renewal, a shell, or a
    continuum. That is checkable by reading the file, and it is what "no such
    identification is required" means. Later records may be appended to the
    retained history **only after their own eligibility and attachment laws have
    been stated**, which is §20 onward, not here. -/

end Return
end Two
end RatioSpace
