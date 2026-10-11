/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S10.Causal
import RatioSpace.ElementsII.S08.Coherence
import RatioSpace.ElementsII.S07.Support
/-!
  Elements II §11 — The one-tick advance `𝔎_𝒞`.

  **The first section of Elements II that assembles rather than adds.** Every
prior section contributes one typed ingredient; §11 contributes none, and
instead claims that the ingredients compose into a single operation which is a
function. Elements I's construction obligations name it first: *"the literal
one-tick map `𝔎_𝒞`, including its domain, codomain, carrier, update formula,
and retained invariants."* All five are here.

**The subscript is not the cavity.** Definition 11.1: `𝒞` is the complete exact
constructive context — the observer, the extended question, the direct positive
observer chart, the endpoint-contrast convention, and Definition 8.1 —
and the book says outright it *"is not the two-argument cavity `𝒞(F_𝒬,N)`"*.
Nothing in this file refers to `Cavity`.

**What §6 already got right, and this file therefore does not redo.**
`Carrier.lean` supplies `Slot`, whose `notEvaluated` is a distinct constructor
rather than an `Option` whose `none` doubles as failure — which is exactly the
distinction Definitions 11.4 and 11.5 each insist on. It supplies
`ProposalStatus` with `tiedSelected` already present. `Coherence.lean` supplies
`support`, Definition 8.1 as a *filter*, so the maximizer set is
already a set and no tie is ever broken. Three of §11's four traps were
disarmed before §11 was reached; scoping note in
`research/lean-support/def-11-1-to-11-8-the-one-tick-advance.md`.
-/

namespace RatioSpace
namespace Two
namespace Advance

open Mat2 Word Frame Pres RatioSpace

/-! ## Definition 11.1 — Lawful advancing domain -/

/-- **Definition 11.1.** `𝔈_𝒬^{<h} = ⨆_{j=0}^{h_𝒬 - 1} 𝔈_{𝒬,j}`.

    A carrier is in the lawful advancing domain exactly when its tick is
    *strictly* below the horizon. The book is explicit that a carrier at
    `j = h_𝒬` is a **terminal** carrier for the current question cycle and that
    `𝔎_𝒞` is not applied to it "until a later construction has either resolved
    and assimilated the cycle or formed a new question".

    `TickCarrier`'s tick is a `Fin (h+1)`, so `h` itself is representable and
    the exclusion is a real hypothesis rather than a type-level accident. -/
def Lawful {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) : Prop :=
  (X.tick : ℕ) < h

instance {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) : Decidable (Lawful X) :=
  inferInstanceAs (Decidable ((X.tick : ℕ) < h))

/-- **Definition 11.1, the terminal case.** At the horizon the domain excludes
    the carrier, and this is the only reason it does. -/
theorem not_lawful_at_horizon {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (ht : (X.tick : ℕ) = h) : ¬ Lawful X := by
  simp [Lawful, ht]

/-- **Definition 11.1, the empty case.** *"If `h_𝒬 = 0`, this domain is empty."*
    Not a convention: with `h = 0` the tick is forced to `0` and cannot be
    strictly below it. -/
theorem lawful_empty_of_horizon_zero {Aux : Type} (X : TickCarrier Aux 0) :
    ¬ Lawful X := by
  have : (X.tick : ℕ) < 1 := X.tick.isLt
  simp [Lawful]

/-! ## Definition 11.2 — Keyed archive union and event append -/

/-- **Definition 11.2, the side condition.** `ℋ ⊔_ι ℋ'` is *"defined only when
    one identifier does not name two different immutable cores."*

    This is the content of the definition, not a technicality. A total union
    that silently prefers one side would prove nothing precisely where an
    archive corrupts. -/
def KeyedCompatible (H H' : List Core) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H', x.id = y.id → x = y

/-- **Definition 11.2.** Union by stable occurrence identifier: everything in
    `H`, together with those members of `H'` whose identifier `H` does not
    already carry. Under `KeyedCompatible` the discarded duplicates are equal
    to what was kept, which is the next theorem. -/
def keyedUnion (H H' : List Core) : List Core :=
  H ++ H'.filter (fun y => ¬ (y.id ∈ archIds H))

/-- Union is lossless on the left. -/
theorem mem_keyedUnion_left {H H' : List Core} {x : Core} (hx : x ∈ H) :
    x ∈ keyedUnion H H' :=
  List.mem_append_left _ hx

/-- **The side condition doing its work.** Under `KeyedCompatible`, nothing in
    `H'` is lost: a member either survives the filter, or its identifier was
    already present and the core carrying that identifier is *equal* to it. -/
theorem mem_keyedUnion_right {H H' : List Core} (hc : KeyedCompatible H H')
    {y : Core} (hy : y ∈ H') : y ∈ keyedUnion H H' := by
  by_cases hid : y.id ∈ archIds H
  · obtain ⟨x, hxH, hxid⟩ := List.mem_map.mp hid
    have hxy : x = y := hc x hxH y hy hxid
    exact List.mem_append_left _ (hxy ▸ hxH)
  · refine List.mem_append_right _ ?_
    exact List.mem_filter.mpr ⟨hy, by simpa using hid⟩

/-- **Definition 11.2, temporal append.** *"The append places the entire stratum
    after every event in `ℰ_j`."* Storage order **within** the stratum has no
    mathematical effect, and nothing in this file reads it. -/
def append {Aux : Type} (ledger stratum : List (QuestionId × Aux)) :
    List (QuestionId × Aux) :=
  ledger ++ stratum

/-- Append is append: every prior event keeps its position ahead of the new
    stratum, which is the whole of the ordering claim. -/
theorem append_preserves_prefix {Aux : Type}
    (ledger stratum : List (QuestionId × Aux)) :
    ledger <+: append ledger stratum :=
  ⟨stratum, rfl⟩

/-! ## Definition 11.3 — Complete admission certificate -/

/-- **Definition 11.3.** The exact set of blocking reasons.

    The book gives three, each with an *"precisely when"*: boundary-rejected iff
    `γ_∂ = 0`, outside-direct-positive-chart iff `Neg(Q_{O,y}) > 0`, and
    predicate-composition-rejected iff `Pred_Γ = 0`. They are independent, so
    all three can hold at once and the record must be able to say so. This is a
    *set* of reasons, never a first reason and never a message. -/
inductive FailReason where
  | boundaryRejected
  | outsideDirectPositiveChart
  | predicateCompositionRejected
deriving DecidableEq, Repr

/-- **Definition 11.3.** `Adm_𝒬(y) = 1` exactly when `Neg(Q_{O,y}) = 0` **and**
    `Pred_Γ(y) = 1`. The cavity boundary stays a mandatory conjunct by
    Definition 4.9, carried inside `pred`. -/
def admits (negLoadY : ℤ) (pred : Bool) : Bool :=
  decide (negLoadY = 0) && pred

/-- **Definition 11.3.** The exact blocking set, computed rather than asserted,
    so that `Fail = ∅ ↔ admitted` is a theorem below and not a convention. -/
def failReasons (boundary : Bool) (negLoadY : ℤ) (pred : Bool) : List FailReason :=
  (if boundary then [] else [FailReason.boundaryRejected]) ++
  (if negLoadY = 0 then [] else [FailReason.outsideDirectPositiveChart]) ++
  (if pred then [] else [FailReason.predicateCompositionRejected])

/-- **Definition 11.3, the six-slot certificate.** Every component the book
    lists is retained, including the raw predicate vector `g_Γ(y)` *and* its
    declared Boolean reading. Keeping both is the point: the vector is evidence,
    the Boolean is the reading of it, and Definition 4.3 fixes the reading. -/
structure AdmCert (Aux : Type) where
  /-- `Q_{O,y}`. -/
  encounter : Mat2
  /-- `Neg(Q_{O,y})`. -/
  negLoad : ℤ
  /-- `g_Γ(y)`, the retained certificate vector. -/
  gamma : List Aux
  /-- `Pred_Γ(y;𝔛_j,j+1)`, the declared Boolean reading. -/
  pred : Bool
  /-- `Adm_𝒬(y;𝔛_j,j+1)`. -/
  adm : Bool
  /-- `Fail_adm(y)`, the exact set of blocking reasons. -/
  fail : List FailReason

/-- **The certificate's two halves cannot disagree**, when built from the same
    inputs: the blocking set is empty exactly when admission holds. The cavity
    boundary is inside `pred`, per Definition 4.9. -/
theorem failReasons_nil_iff_admits (negLoadY : ℤ) (pred : Bool) :
    failReasons true negLoadY pred = [] ↔ admits negLoadY pred = true := by
  by_cases h : negLoadY = 0 <;> by_cases hp : pred <;> simp [failReasons, admits, h, hp]

/-- Each reason appears **precisely when** its own condition fails, independently
    of the other two. Stated for the chart condition; the other two are the same
    `simp`. -/
theorem chart_reason_mem_iff (boundary : Bool) (negLoadY : ℤ) (pred : Bool) :
    FailReason.outsideDirectPositiveChart ∈ failReasons boundary negLoadY pred ↔
      negLoadY ≠ 0 := by
  by_cases h : negLoadY = 0 <;> by_cases hb : boundary <;> by_cases hp : pred <;>
    simp [failReasons, h, hb, hp]

/-! ## Definition 11.4 — Comparison package and support status -/

/-- **Definition 11.4.** The seven-slot comparison package. Each slot is a
    `Slot`, so *"not-applicable-by-admission"* is representable as itself: the
    book is explicit that for a proposal outside `A_{j+1}` **"no zero coherence value or
    empty star is invented for it"**, and `Slot.notEvaluated` is that, rather
    than an `Option` whose `none` also means "computed, and empty". -/
structure CmpPackage (Aux : Type) where
  /-- `Σ_j^{(O)}(y)`, the ordered composition star. -/
  star : Slot Aux
  /-- `T_j^{(O)}(y)`, the tension signature. -/
  tension : Slot Aux
  /-- `L_{CF,j}^{(O)}(y)`. -/
  cfLength : Slot Aux
  /-- `D_{walk,j}^{(O)}(y)`. -/
  walkDepth : Slot Aux
  /-- `C_j^{(O)}(y) = c_0 + c_1 φ`, the coherence value. -/
  coherence : Slot Zphi
  /-- `c_{0,y}`, the first integer of Theorem 8.5's certificate. -/
  c0 : Slot ℤ
  /-- `c_{1,y}`, the second. -/
  c1 : Slot ℤ

/-- **Definition 11.4, for a proposal outside the admitted family.** Every slot
    is `notEvaluated`. Nothing is defaulted to zero. -/
def CmpPackage.notApplicable {Aux : Type} : CmpPackage Aux where
  star := .notEvaluated
  tension := .notEvaluated
  cfLength := .notEvaluated
  walkDepth := .notEvaluated
  coherence := .notEvaluated
  c0 := .notEvaluated
  c1 := .notEvaluated

/-- **Definition 11.4, the creation status.** `S_{j+1}` is a *list*, because
    Definition 8.1 returns the complete maximizer set and `tiedSelected`
    is a real case. A function returning one winner would have imported the
    choice the definition refuses to make. -/
def statusOf {Aux Cert : Type} [DecidableEq Aux]
    (cert : Cert) (admitted support : List Aux) (y : Aux) : ProposalStatus Cert :=
  if y ∉ admitted then .admissionRejected cert
  else if y ∉ support then .coherenceRejected
  else if support.length = 1 then .selected
  else .tiedSelected

/-- **Definition 11.4: the four cases are mutually exclusive and exhaustive.**
    Exhaustive is immediate from the definition being total; the content is
    exclusivity, and it holds because the three tests are nested. Stated as the
    two facts that actually get used: a rejected proposal is not in the support,
    and a selected one is. -/
theorem statusOf_selected_mem {Aux Cert : Type} [DecidableEq Aux]
    (cert : Cert) (admitted support : List Aux) (y : Aux)
    (h : statusOf cert admitted support y = .selected) : y ∈ support := by
  unfold statusOf at h
  by_cases h1 : y ∉ admitted
  · simp [h1] at h
  · by_cases h2 : y ∉ support
    · simp [h1, h2] at h
    · simpa using h2

/-- A tie is still a member of the support, and there is more than one. -/
theorem statusOf_tied_mem {Aux Cert : Type} [DecidableEq Aux]
    (cert : Cert) (admitted support : List Aux) (y : Aux)
    (h : statusOf cert admitted support y = .tiedSelected) :
    y ∈ support ∧ support.length ≠ 1 := by
  unfold statusOf at h
  by_cases h1 : y ∉ admitted
  · simp [h1] at h
  · by_cases h2 : y ∉ support
    · simp [h1, h2] at h
    · by_cases h3 : support.length = 1
      · simp [h1, h2, h3] at h
      · exact ⟨by simpa using h2, h3⟩

/-! ## Definition 11.5 — Native annotation package -/

/-- **Definition 11.5.** Five slots, of which two are *mandatory accumulators*
    with exact laws and three are evaluated only when the receiver data declares
    them. `channel` and `lift` are `Slot`s for the same reason as §11.4's: the
    book says "otherwise the corresponding slot is not-evaluated", and that is
    not the same as an empty answer. -/
structure NativeAnn (Aux : Type) where
  /-- `Ω(O,y)`, mandatory. -/
  winding : ℤ
  /-- `κ_cl(y)`, mandatory. -/
  closure : ZMod 12
  /-- `channel(y)`. -/
  channel : Slot Aux
  /-- `liftStatus(y)`. -/
  lift : Slot Aux
  /-- `CF(x;g)`. -/
  cf : Slot Aux

/-- **Definition 11.5's two accumulator laws**, as the constructor. `Ω` adds the
    hand's sign and `κ_cl` adds its twelve-class contribution mod 12; both are
    increments on the parent's value, never recomputed from scratch. -/
def NativeAnn.ofChild {Aux : Type} (parentWinding : ℤ) (parentClosure : ZMod 12)
    (g : Bool) : NativeAnn Aux where
  winding := parentWinding + (if g then 1 else -1)
  closure := parentClosure + psi12 [g]
  channel := .notEvaluated
  lift := .notEvaluated
  cf := .notEvaluated

/-- **Definition 11.5, `Ω(O,y) = Ω(O,x) + σ(g)`.** -/
@[simp] theorem NativeAnn.ofChild_winding {Aux : Type} (pw : ℤ) (pc : ZMod 12) (g : Bool) :
    (NativeAnn.ofChild (Aux := Aux) pw pc g).winding = pw + (if g then 1 else -1) := rfl

/-- **Definition 11.5, `κ_cl(y) = κ_cl(x) + ψ₁₂(g) mod 12`.** -/
@[simp] theorem NativeAnn.ofChild_closure {Aux : Type} (pw : ℤ) (pc : ZMod 12) (g : Bool) :
    (NativeAnn.ofChild (Aux := Aux) pw pc g).closure = pc + psi12 [g] := rfl

/-! ## Definition 11.6 — The one-tick advance -/

/-- **Definition 11.6.** `P_{j+1}(S_j) = S_j × {L,R}`: every active occurrence
    proposes exactly two tagged children, and nothing else proposes. -/
def proposals (archive : List Core) (active : List QuestionId) : List (Core × Bool) :=
  (archive.filter (fun c => c.id ∈ active)).flatMap
    (fun c => [(c, false), (c, true)])

/-- Exactly two proposals per active occurrence, which is the arity Proposition
    11.7's determinacy argument opens with. -/
theorem proposals_two (archive : List Core) (active : List QuestionId) :
    (proposals archive active).length =
      2 * (archive.filter (fun c => c.id ∈ active)).length := by
  unfold proposals
  induction archive.filter (fun c => c.id ∈ active) with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]; omega

/-- **Definition 11.6.** The one-tick advance `𝔎_𝒞`, on the archive and ledger
    components. The tick itself advances by `Temporal.advance` under the lawful
    hypothesis, and the support is Definition 8.1's filter, both of
    which already exist; what this file adds is the archive and ledger update
    and the statement that the whole thing is one function.

    `ΔE_{j+1}` is supplied by the caller because its entries are the records of
    Definitions 11.3–11.5, which are typed over `Aux`. -/
def advanceArchive (archive : List Core) (active : List QuestionId) (stratum : ℕ)
    (prov : Provenance) : List Core :=
  keyedUnion archive
    ((proposals archive active).map (fun p => childCore p.1 p.2 stratum prov))

/-- **Definition 11.6: the archive only grows.** *"Support selection does not
    delete"* is Remark 8.2 for the support; this is the same fact for the
    archive under the advance, and it is what makes `ℋ` append-only. -/
theorem advanceArchive_lossless {archive : List Core} {active : List QuestionId}
    {stratum : ℕ} {prov : Provenance} {x : Core} (hx : x ∈ archive) :
    x ∈ advanceArchive archive active stratum prov :=
  mem_keyedUnion_left hx

/-! ## Proposition 11.7 — Functional determinacy of one tick -/

/-- **Proposition 11.7.** *"A valid carrier in `𝔈_𝒬^{<h}` has exactly one output
    under `𝔎_𝒞`."*

    In a total dependent type theory the *shape* of this is free: `advanceArchive`
    is a function, so equal inputs give equal outputs by `rfl`. That freeness is
    exactly why stating it here would be worthless, and why the book's proof
    spends its length elsewhere — on the claim that **no component required a
    choice**. The load-bearing sentence is *"Definition 8.1 returns the
    complete maximizer set and supplies no secondary choice."*

    So the honest Lean content of 11.7 is choice-freeness, discharged by
    `#print axioms` reporting no `Classical.choice`, not by a theorem. An
    `advanceArchive X = advanceArchive X := rfl` would be a theorem that says
    nothing, and writing one to have something to point at is the failure this
    project's own standard names.

    What *is* stated here is the part that is not free. Definition 11.6 archives
    **every proposal**, not every admitted one and not every selected one:
    `ℋ_{j+1} = ℋ_j ⊔_ι {Core(y) : y ∈ P_{j+1}(S_j)}`. So the archive update is
    independent of admission, of coherence, and of whether the support was a
    tie. That independence is what makes ties harmless, and it is the reason
    Prop 11.7's determinacy survives Definition 8.1 returning a set. -/
theorem child_archived_regardless_of_selection
    {archive : List Core} {active : List QuestionId} {stratum : ℕ} {prov : Provenance}
    {p : Core × Bool} (hp : p ∈ proposals archive active)
    (hfresh : (childCore p.1 p.2 stratum prov).id ∉ archIds archive) :
    childCore p.1 p.2 stratum prov ∈ advanceArchive archive active stratum prov := by
  refine List.mem_append_right _ (List.mem_filter.mpr ⟨?_, by simpa using hfresh⟩)
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

/-! ## §12 — Well-typedness, growth, and enumeration independence

    §12 proves things *about* the map §11 built rather than adding to it. Four
    of its eight items are statements about `advanceArchive` and `proposals`
    directly, and those are what this section proves. The rest (12.3–12.5, 12.8)
    quantify over machinery from §4 and §7 that is not built here yet. -/

/-- **Lemma 12.1, first half.** *"Two different parent-hand pairs cannot yield
    one identifier."* The child identifier appends the hand to the parent's
    relative word, so this is injectivity of `·.rel ++ [g]` in both arguments. -/
theorem child_id_inj {i i' : QuestionId} {g g' : Bool}
    (h : i.child g = i'.child g') : i = i' ∧ g = g' := by
  cases i; cases i'
  simp only [QuestionId.child, QuestionId.mk.injEq] at h
  obtain ⟨hc, hq, hs, hr⟩ := h
  obtain ⟨hrel, hg⟩ := List.append_inj' hr rfl
  simp_all

/-- **Lemma 12.1, second half.** *"Every archived occurrence created no later
    than tick `j` has a relative continuation word of length at most `j`,
    whereas a proposal at the current advance has length `j+1`."*

    Length is the whole argument, and it is why the archive union is disjoint
    rather than merely assumed to be. Stated as the arithmetic fact it is: a
    child's relative word is strictly longer than its parent's, so a proposal
    cannot equal any identifier already present at a shorter length. -/
theorem child_rel_length (i : QuestionId) (g : Bool) :
    (i.child g).rel.length = i.rel.length + 1 := by
  simp [QuestionId.child]

/-- **Lemma 12.1, the disjointness it buys.** An identifier whose relative word
    is no longer than `j` is not a proposal identifier from a parent at `j`. -/
theorem child_ne_of_length_le {i p : QuestionId} {g : Bool} {j : ℕ}
    (hp : p.rel.length = j) (hi : i.rel.length ≤ j) : i ≠ p.child g := by
  intro h
  have := congrArg (fun q => q.rel.length) h
  simp [child_rel_length, hp] at this
  omega

/-- **Corollary 12.2.** `|ℋ_{j+1}| = |ℋ_j| + 2|S_j|`, *"counting all proposals,
    including admission and coherence rejections."*

    Lemma 12.1 is what makes the union disjoint; here it is the hypothesis, so
    the corollary states exactly what it depends on. The count is `2|S_j|` and
    not `|A_{j+1}|`: **the archive grows by every proposal, and rejection does
    not shrink it.** That is the same fact `child_archived_regardless_of_selection`
    states occurrence-wise, now as a cardinality. -/
theorem archive_growth (archive : List Core) (active : List QuestionId)
    (stratum : ℕ) (prov : Provenance)
    (hfresh : ∀ p ∈ proposals archive active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds archive) :
    (advanceArchive archive active stratum prov).length =
      archive.length + 2 * (archive.filter (fun c => c.id ∈ active)).length := by
  unfold advanceArchive keyedUnion
  rw [List.length_append, List.filter_eq_self.mpr, List.length_map, proposals_two]
  intro y hy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
  simpa using hfresh p hp

/-- **Theorem 12.7.** *"Permuting the storage order of a valid carrier, its
    proposal records, or any occurrence-keyed records within one event stratum
    ... does not change the mathematical output."*

    This is the theorem that makes `Definition 11.2`'s comment true. That
    definition says the stratum's *"internal storage order has no mathematical
    effect"*, and `TickCarrier.ledger`'s docstring says the same of the ledger.
    Both were comments; nothing enforced them. Here it is for the proposal
    family, which is the one §12 actually needs: permuting the archive permutes
    the proposals and changes nothing else.

    The book's own caveat is the interesting half and it is preserved by the
    statement rather than added to it: *"Duplicating an identifier is not a
    permutation and violates the carrier type."* `List.Perm` cannot duplicate,
    so the hypothesis is exactly the book's. -/
theorem proposals_perm {archive archive' : List Core} (active : List QuestionId)
    (h : archive.Perm archive') :
    (proposals archive active).Perm (proposals archive' active) := by
  unfold proposals
  exact (h.filter _).flatMap_right _

/-- **Theorem 12.7, the consequence that is actually used.** The number of
    proposals is enumeration-independent, so Corollary 12.2's count is a fact
    about the carrier and not about how its archive happened to be stored. -/
theorem proposals_length_perm {archive archive' : List Core} (active : List QuestionId)
    (h : archive.Perm archive') :
    (proposals archive active).length = (proposals archive' active).length :=
  (proposals_perm active h).length_eq

/-! ### 12.3, 12.5 and 12.6, on the machinery §7 and §8 already supply

    An earlier draft of this file's scoping note said 12.3–12.5 and 12.8
    *"quantify over §4 and §7 machinery not built here yet."* That was asserted
    without looking. `Cavity.lean` is §4 and `Support.lean` is §7; both are
    built, and three of the four items were reachable the whole time. Recorded
    because the note was wrong in the direction that costs most: it made four
    items look blocked when nothing blocked them. -/

/-- **Lemma 12.3.** *"Every occurrence entering an observer-local composition
    star has one decoded positive word ... No occurrence lacking those operands
    enters a base comparison package."*

    Definition 7.1 filters on reachability *and* the declared predicate, and
    `reachable` is exactly "positive decoding from `O`'s chart succeeds". So the
    operand a comparison package needs is not merely available for an admitted
    occurrence, it is what admission tested. The lemma is that these are one
    condition rather than two that happen to coincide. -/
theorem admitted_has_operand {MO : Mat2} {pred : ProposalRecord → Bool}
    {P : List ProposalRecord} {y : ProposalRecord} (hy : y ∈ admitted MO pred P) :
    (localWord MO y.fullMatrix).isSome := by
  simpa [reachable] using (admitted_both hy).1

/-- **Lemma 12.3, the contrapositive the book states.** An occurrence without
    the decoded operand is not admitted, so it cannot reach a comparison
    package — and by Definition 11.4 it carries `CmpPackage.notApplicable`,
    not an invented coherence value. -/
theorem no_operand_not_admitted {MO : Mat2} {pred : ProposalRecord → Bool}
    {P : List ProposalRecord} {y : ProposalRecord}
    (h : (localWord MO y.fullMatrix).isSome = false) : y ∉ admitted MO pred P :=
  fun hy => by simp [admitted_has_operand hy] at h

/-- **Theorem 12.5.** *"Every application of `𝔎_𝒞` terminates after finitely
    many exact operations."*

    Carried by the types rather than argued: every family here is a `List`, so
    finiteness is a fact to state where the book's proof states a bound. The
    bound worth naming is the book's own — the admitted family never exceeds
    the proposal family, which Corollary 12.2 counts as `2|S_j|`. -/
theorem admitted_length_le (MO : Mat2) (pred : ProposalRecord → Bool)
    (P : List ProposalRecord) : (admitted MO pred P).length ≤ P.length :=
  List.length_filter_le _ _

/-- **Theorem 12.6, the substrate claim underneath it.** *"No floating
    approximation to `φ`, tolerance, mean, probability, or normalized weight
    enters the result."* The tie is decided on two integers, so an exact tie is
    an exact integer equality and never a tolerance. §8 proves it; naming it at
    §12 is what makes the sentence checkable rather than aspirational. -/
theorem tie_has_integer_witness (fam : List IPres) (y z : IPres) :
    coherenceOf fam y = coherenceOf fam z
      ↔ c0 (tensions fam y) = c0 (tensions fam z)
        ∧ c1 (tensions fam y) = c1 (tensions fam z) :=
  tie_is_integral fam y z

/-- **Theorem 12.7, the half that was missing.** `proposals_perm` showed the
    proposal family is enumeration-independent; §8's `support_perm_mem` shows
    the support is. Together they cover the two components that could plausibly
    have depended on storage order, and neither does. -/
theorem support_enumeration_independent {fam fam' : List IPres}
    (h : fam.Perm fam') (y : IPres) : y ∈ support fam ↔ y ∈ support fam' :=
  support_perm_mem h y

/-! ## §13 — Covariance of the complete tick

    §13 asks whether the one-tick law has a preferred position or a preferred
    hand. Both answers are no, and the second is the one that matters to the
    framework: Corollary 13.4 says the law *cannot* select one member of a
    mirror pair from the labels `L` and `R` alone.

    What is provable in this file is the proposal-generation half of each. The
    admission and comparison halves live in §7 and §8 and are already proved
    there (Thm 7.8, Thm 8.13, Cor 8.14); assembling them into the full carrier
    statement is 13.2 and 13.3 entire, which needs the carrier advance rather
    than the archive advance. -/

/-- **Theorem 13.2, at the occurrence.** Transporting a core's seed by a common
    prefix `u` and then taking its child reaches `Z_u` of the untransported
    child. Proposition 3.5's `Z_u(M_x g) = Z_u(M_x) g`, at the archive layer.

    The identifier and relative word do not move, and that is the content
    rather than an omission: they are local data, so transport acts on where
    the occurrence sits and not on which occurrence it is. -/
theorem childCore_transport_fullMatrix (u : Word) (c : Core) (g : Bool)
    (stratum : ℕ) (prov : Provenance) :
    (childCore { c with seed := transportSeed u c.seed } g stratum prov).fullMatrix
      = Z u (childCore c g stratum prov).fullMatrix := by
  simp only [childCore, Core.ofProposal, ← transportProposal_child]
  exact childProposal_transport_comm u c.seedId c.seed c.relWord g

/-- **Theorem 13.3 / Corollary 13.4, the generation half.** Swapping the hand on
    every proposal permutes the proposal family.

    This is the exact sense in which the labels carry no preference: `proposals`
    emits `(c, L)` and `(c, R)` for each active occurrence, so the hand-swap is
    a bijection of the family onto itself. Whatever asymmetry a tick exhibits,
    it did not come from here. -/
theorem proposals_hand_swap (archive : List Core) (active : List QuestionId) :
    ((proposals archive active).map (fun p => (p.1, !p.2))).Perm
      (proposals archive active) := by
  unfold proposals
  induction archive.filter (fun c => c.id ∈ active) with
  | nil => simp
  | cons a l ih =>
      simp only [List.flatMap_cons, List.map_append]
      exact (List.Perm.append (by simp [List.Perm.swap]) ih)

/-- **Corollary 13.4, stated the way it is used.** Both hands are proposed for
    every active occurrence, always. *"The one-tick law cannot select one member
    of a fixed-point-free mirror pair merely from the labels `L` and `R`."*

    So a one-sided outcome is evidence about the question data, the observer
    record, or a later exact comparison — never about the labels. That is the
    book's own list of the four things a one-sided outcome may be carried by,
    and this theorem is what removes the fifth possibility. -/
theorem both_hands_proposed {archive : List Core} {active : List QuestionId}
    {c : Core} (hc : c ∈ archive.filter (fun x => x.id ∈ active)) (g : Bool) :
    (c, g) ∈ proposals archive active := by
  unfold proposals
  refine List.mem_flatMap.mpr ⟨c, hc, ?_⟩
  cases g <;> simp

/-! ## Definition 11.6, on the whole carrier

    `advanceArchive` moves the archive. This moves all six components, which is
    what 12.4, 12.8, 13.2 and 13.3 each need and none of them could reach.

    **The selector is a parameter, and that is faithful rather than a
    concession.** Definition 11.4 takes `S_{j+1}` from Definition 8.1
    applied to `A_{j+1}`, and `A_{j+1}` is Definition 7.1's family, filtered on
    the observer's **declared** predicate `Pred_Γ`. The book requires that
    predicate to be declared and refuses to assume one, so a carrier advance
    that manufactured its own would be inventing the question. What is *not* a
    parameter is the obligation: whatever the selector returns must consist of
    identifiers the archive actually holds, and that is discharged here rather
    than assumed. -/

/-- **Definition 11.6, the complete map `𝔎_𝒞`.** All six components.

    `select` is Definition 8.1 composed with Definitions 11.3–11.5,
    supplied by the caller because the declared predicate is the observer's.
    `hsel` is the only thing asked of it: it proposes from among the proposals.
    `hfresh` is Lemma 12.1, which is a theorem about identifier lengths rather
    than an assumption, and is passed in because this file does not carry the
    tick data that proves it. -/
def advanceCarrier {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X)
    (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance)
    (Δ : List (QuestionId × Aux))
    (hsel : ∀ i ∈ select (proposals X.archive X.active),
      ∃ p ∈ proposals X.archive X.active, (childCore p.1 p.2 stratum prov).id = i)
    (hfresh : ∀ p ∈ proposals X.archive X.active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive) :
    TickCarrier Aux h where
  observer := X.observer
  question := X.question
  tick := ⟨(X.tick : ℕ) + 1, by
    have hj : (X.tick : ℕ) < h := hlaw
    omega⟩
  active := select (proposals X.archive X.active)
  archive := advanceArchive X.archive X.active stratum prov
  ledger := append X.ledger Δ
  active_sub_archive := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := hsel i hi
    exact List.mem_map_of_mem (child_archived_regardless_of_selection hp (hfresh p hp))

/-- **Theorem 12.4, one-tick well-typedness.** *"If `𝔛_{τ,j} ∈ 𝔈_𝒬^{<h}` then
    `𝔎_𝒞(𝔛_{τ,j}) ∈ 𝔈_{𝒬,j+1}`."*

    The `∈ 𝔈_{𝒬,j+1}` half is carried by the type: `advanceCarrier` returns a
    `TickCarrier`, and its `active_sub_archive` obligation — Proposition 6.8,
    clause 1 — is discharged in the definition rather than assumed. What is left
    to state is the tick, and that it is `j+1` exactly. -/
@[simp] theorem advanceCarrier_tick {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) :
    ((advanceCarrier X hlaw select stratum prov Δ hsel hfresh).tick : ℕ)
      = (X.tick : ℕ) + 1 := rfl

/-- **Theorem 12.4, the part that is not free.** The observer and the extended
    question are *unchanged* by one tick. Definition 11.6 writes `O_τ` and `𝒬_τ`
    into the output unaltered, and Separation Rule 11.8 is why: proposal,
    admission, comparison and archiving are internal operations of one advance,
    so the tick may not quietly redeclare the question it is answering. -/
@[simp] theorem advanceCarrier_question {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) :
    (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).question = X.question ∧
    (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).observer = X.observer :=
  ⟨rfl, rfl⟩

/-- **Corollary 12.8, the archive half.** *"An exact deterministic advance
    within the complete Elements I ensemble type."* Every occurrence the carrier
    held, it still holds: one tick is monotone on the archive, so no advance can
    lose an occurrence recorded by an earlier one. -/
theorem advanceCarrier_archive_monotone {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) {x : Core} (hx : x ∈ X.archive) :
    x ∈ (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).archive :=
  advanceArchive_lossless hx

/-- **Corollary 12.8, the ledger half.** The prior ledger is a prefix of the
    new one, so the event record is append-only across the advance and not only
    within one stratum. -/
theorem advanceCarrier_ledger_prefix {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) :
    X.ledger <+: (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).ledger :=
  append_preserves_prefix _ _

/-! ## Duplicate-freedom survives one tick

    Theorem 17.7's iff-direction (`Terminal.lean`) needed the terminal
    carrier's archive and active support both duplicate-free, and named the
    gap as a schedule-length induction, not local wiring. The induction itself
    belongs in `Accumulation.lean`, where `Policy`/`iterate` live; what this
    file supplies is the one-step preservation lemma it inducts on. Well-
    formedness of the archive turns out to be the missing ingredient, not
    duplicate-freedom of the archive itself — that one is unconditional,
    `childCore_wellFormed`, and it is what makes the new children's own
    identifiers computable from their parents' at all. -/

/-- **A well-formed parent's identity determines its children's.** `childCore`
    always recomputes the id from `(seedId, relWord)` alone (`childProposal_id`
    composed with the definition of `proposal`), and well-formedness is exactly
    `c.id` agreeing with that recomputation for `c` itself. -/
theorem childCore_id (c : Core) (hc : c.WellFormed) (g : Bool) (entry : ℕ)
    (prov : Provenance) :
    (childCore c g entry prov).id = c.id.child g := by
  have h5 : c.id = (proposal c.seedId c.seed c.relWord).id := hc.2.2.2.2.1
  change (childProposal c.seedId c.seed c.relWord g).id = c.id.child g
  rw [childProposal_id, h5]

/-- **Two children collide only if their parents do, by the same hand.** Needs
    both parents well-formed; nothing else — the framework content is entirely
    in `child_id_inj`, already proved for Lemma 12.1. -/
theorem childCore_id_inj {c c' : Core} (hc : c.WellFormed) (hc' : c'.WellFormed)
    {g g' : Bool} {entry entry' : ℕ} {prov prov' : Provenance}
    (h : (childCore c g entry prov).id = (childCore c' g' entry' prov').id) :
    c.id = c'.id ∧ g = g' := by
  rw [childCore_id c hc, childCore_id c' hc'] at h
  exact child_id_inj h

/-- **Well-formedness survives the advance.** Every core `advanceArchive` adds
    is a `childCore` of some core already in the archive, well-formed
    unconditionally (`childCore_wellFormed`, no hypothesis on the parent);
    every core it keeps was already well-formed. -/
theorem advanceArchive_wellFormed {archive : List Core} {active : List QuestionId}
    {stratum : ℕ} {prov : Provenance} (hwf : ∀ c ∈ archive, c.WellFormed) :
    ∀ c ∈ advanceArchive archive active stratum prov, c.WellFormed := by
  intro c hc
  unfold advanceArchive keyedUnion at hc
  rcases List.mem_append.mp hc with h | h
  · exact hwf c h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_filter.mp h).1
    exact childCore_wellFormed p.1 p.2 stratum prov

/-- **New children never collide with each other**, given their parents come
    from a duplicate-free, well-formed list. The archive's own `Nodup` is what
    rules out two *different* parents sharing an identifier; well-formedness is
    what makes "different parents" and "different child identifiers" the same
    fact, via `childCore_id_inj`. -/
theorem flatMap_childCore_id_nodup {L : List Core} (hnodup : (L.map Core.id).Nodup)
    (hwf : ∀ c ∈ L, c.WellFormed) (stratum : ℕ) (prov : Provenance) :
    ((L.flatMap (fun c => [(c, false), (c, true)])).map
      (fun p => (childCore p.1 p.2 stratum prov).id)).Nodup := by
  induction L with
  | nil => simp
  | cons c cs ih =>
      rw [List.map_cons, List.nodup_cons] at hnodup
      obtain ⟨hcNotMem, hcsNodup⟩ := hnodup
      have hcWF : c.WellFormed := hwf c List.mem_cons_self
      have hcsWF : ∀ c' ∈ cs, c'.WellFormed :=
        fun c' hc' => hwf c' (List.mem_cons_of_mem _ hc')
      have IH := ih hcsNodup hcsWF
      have hne : (childCore c false stratum prov).id ≠ (childCore c true stratum prov).id := by
        rw [childCore_id c hcWF, childCore_id c hcWF]
        simp [QuestionId.child]
      have hdisj : ∀ g : Bool, (childCore c g stratum prov).id ∉
          (cs.flatMap (fun c' => [(c', false), (c', true)])).map
            (fun p => (childCore p.1 p.2 stratum prov).id) := by
        intro g hmem
        obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hmem
        obtain ⟨c', hc', hp'⟩ := List.mem_flatMap.mp hp
        have hc'WF : c'.WellFormed := hcsWF c' hc'
        have heq : c.id = c'.id := by
          have hh : (childCore c g stratum prov).id = (childCore p.1 p.2 stratum prov).id := by
            rw [hpeq]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · exact (childCore_id_inj hcWF hc'WF hh).1
          · exact (childCore_id_inj hcWF hc'WF hh).1
        exact hcNotMem (heq ▸ List.mem_map_of_mem (f := Core.id) hc')
      have step : ((c :: cs).flatMap (fun c' => [(c', false), (c', true)])).map
            (fun p => (childCore p.1 p.2 stratum prov).id)
          = (childCore c false stratum prov).id ::
            (childCore c true stratum prov).id ::
            (cs.flatMap (fun c' => [(c', false), (c', true)])).map
              (fun p => (childCore p.1 p.2 stratum prov).id) := by
        simp [List.flatMap_cons]
      rw [step, List.nodup_cons, List.nodup_cons]
      refine ⟨?_, hdisj true, IH⟩
      simp only [List.mem_cons]
      rintro (h | h)
      · exact hne h
      · exact hdisj false h

/-- Filtering `archive` by active membership and then reading `.id` off what
    survives is the same list as mapping to `archIds` first and filtering
    there — the map-level strengthening of `filter_id_length_eq_map_filter`
    (`Carrier.lean`), by the same induction. -/
theorem filter_id_eq_map_filter (archive : List Core) (active : List QuestionId) :
    (archive.filter fun c => decide (c.id ∈ active)).map Core.id
      = (archive.map Core.id).filter (fun i => decide (i ∈ active)) := by
  induction archive with
  | nil => simp
  | cons c cs ih =>
      by_cases hc : decide (c.id ∈ active) = true <;> simp [hc, ih]

/-- **The new part of the advance is itself duplicate-free**, restated at
    `proposals`/`advanceArchive`'s own shape rather than the generic flatMap
    above. -/
theorem proposals_childCore_id_nodup {archive : List Core} {active : List QuestionId}
    (hnodup : (archive.map Core.id).Nodup) (hwf : ∀ c ∈ archive, c.WellFormed)
    (stratum : ℕ) (prov : Provenance) :
    ((proposals archive active).map (fun p => (childCore p.1 p.2 stratum prov).id)).Nodup := by
  unfold proposals
  have hLnodup : ((archive.filter fun c => decide (c.id ∈ active)).map Core.id).Nodup := by
    rw [filter_id_eq_map_filter]; exact hnodup.filter _
  have hLwf : ∀ c ∈ archive.filter fun c => decide (c.id ∈ active), c.WellFormed :=
    fun c hc => hwf c (List.mem_filter.mp hc).1
  exact flatMap_childCore_id_nodup hLnodup hLwf stratum prov

/-- **`advanceArchive` keeps the archive duplicate-free.** The old part is
    duplicate-free by hypothesis; the new part is duplicate-free by
    `proposals_childCore_id_nodup`; and `keyedUnion`'s own filter is exactly
    what makes the two parts disjoint, with no further hypothesis needed. -/
theorem advanceArchive_nodup {archive : List Core} {active : List QuestionId}
    {stratum : ℕ} {prov : Provenance} (hnodup : (archive.map Core.id).Nodup)
    (hwf : ∀ c ∈ archive, c.WellFormed) :
    ((advanceArchive archive active stratum prov).map Core.id).Nodup := by
  unfold advanceArchive keyedUnion
  rw [List.map_append, List.nodup_append]
  set newPart := (proposals archive active).map (fun p => childCore p.1 p.2 stratum prov)
    with hnewPartDef
  have hnewPartId : newPart.map Core.id =
      (proposals archive active).map (fun p => (childCore p.1 p.2 stratum prov).id) := by
    simp [hnewPartDef, List.map_map, Function.comp]
  have hnewPartNodup : (newPart.map Core.id).Nodup := by
    rw [hnewPartId]; exact proposals_childCore_id_nodup hnodup hwf stratum prov
  have hsub : (newPart.filter (fun y => ¬ (y.id ∈ archIds archive))).Sublist newPart :=
    List.filter_sublist
  have hfreshNodup :
      ((newPart.filter (fun y => ¬ (y.id ∈ archIds archive))).map Core.id).Nodup :=
    List.Nodup.sublist (hsub.map _) hnewPartNodup
  refine ⟨hnodup, hfreshNodup, ?_⟩
  intro x hx y hy hxy
  subst hxy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
  exact of_decide_eq_true (List.mem_filter.mp hz).2 hx

#print axioms advanceArchive_wellFormed
#print axioms advanceArchive_nodup

end Advance
end Two
end RatioSpace
