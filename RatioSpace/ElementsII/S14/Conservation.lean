/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S11.Advance
/-!
  Elements II §14 — History and closure conservation.

  **§14 adds no machinery. It says what the machinery already forbids.** Every
statement here is about `𝔎_𝒞`, which §11 built and §12/§13 typed; §14's whole
content is that the map is append-only, that the exact history is recoverable
from what it stored, and that the two mandatory accumulators of Definition 11.5
never drift from the words they annotate.

**The identifier is why 14.4 is almost free.** Definition 4.1 made
`ι(τ,𝗾,ι₀,v)` carry `v` itself rather than a scalar label assigned afterward,
so "repeated parent traversal recovers one unique seed and one unique relative
continuation word" is a statement about `List.dropLast`, and the world word and
matrix fall out by `rfl`. That is not a shortcut. It is the payment for a
decision taken ten sections earlier, and it is worth saying out loud that a
label-based identifier would have made 14.4 the hardest theorem in the volume.

**One finding, in 14.8.** The book says neither `S_j ⊆ S_{j+1}` nor
`S_{j+1} ⊆ S_j` *is required*. Under Lemma 12.1 the two supports are in fact
**disjoint**: Construction Axiom II.1 selects from newly admitted child
occurrences, every child identifier is fresh against the archive, and the
carrier's own `active_sub_archive` field puts `S_j` inside that archive. So both
inclusions fail outright whenever both supports are nonempty, rather than merely
failing to be guaranteed. `support_disjoint` below.
-/

namespace RatioSpace
namespace Two
namespace Conservation

open Mat2 Word Frame Pres RatioSpace Advance

/-! ## Definition 14.1 — History-extension order -/

/-- **Definition 14.1.** `𝔛_{τ,j} ⪯_hist 𝔛_{τ,k}` when `j ≤ k`, every immutable
    core in `ℋ_j` occurs unchanged in `ℋ_k`, and `ℰ_j` is an initial sequence of
    `ℰ_k`.

    *"Occurs unchanged"* needs no separate clause here. `Core` is a value type,
    so `c ∈ Y.archive` for the very same `c` already says the core is present
    **and** that no field of it was rewritten; a version that stored mutable
    cells would have needed the extra hypothesis and this one does not.

    **The active supports are deliberately unconstrained**, which is the book's
    own emphasis and the whole point of Theorem 14.8: there is no clause on
    `.active` because there is no true one. -/
def HistExtends {Aux : Type} {h : ℕ} (X Y : TickCarrier Aux h) : Prop :=
  (X.tick : ℕ) ≤ (Y.tick : ℕ) ∧
  (∀ c ∈ X.archive, c ∈ Y.archive) ∧
  X.ledger <+: Y.ledger

/-- `⪯_hist` is reflexive. -/
theorem HistExtends.refl {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) :
    HistExtends X X :=
  ⟨le_refl _, fun _ hc => hc, List.prefix_refl _⟩

/-- `⪯_hist` is transitive, which is what lets Theorems 14.4 and 14.5 say
    *"after one or more ticks"* rather than after exactly one. -/
theorem HistExtends.trans {Aux : Type} {h : ℕ} {X Y Z : TickCarrier Aux h}
    (hxy : HistExtends X Y) (hyz : HistExtends Y Z) : HistExtends X Z :=
  ⟨le_trans hxy.1 hyz.1,
   fun c hc => hyz.2.1 c (hxy.2.1 c hc),
   hxy.2.2.trans hyz.2.2⟩

/-! ## Theorem 14.2 — Append-only archive and ledger -/

/-- **Theorem 14.2, the boxed statement.** *"Every lawful one-tick advance
    satisfies `𝔛_{τ,j} ⪯_hist 𝔎_𝒞(𝔛_{τ,j})`."*

    All three clauses were already separately available — the tick from
    Theorem 12.4, the archive from Corollary 12.8's first half, the ledger from
    its second. §14's contribution is that they are the three clauses of one
    order relation, so they compose across ticks. -/
theorem advance_histExtends {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) :
    HistExtends X (advanceCarrier X hlaw select stratum prov Δ hsel hfresh) :=
  ⟨by rw [advanceCarrier_tick]; omega,
   fun _ hc => advanceCarrier_archive_monotone X hlaw select stratum prov Δ hsel hfresh hc,
   advanceCarrier_ledger_prefix X hlaw select stratum prov Δ hsel hfresh⟩

/-- **Theorem 14.2, the explicit ledger form.** *"`ℰ_{j+1} = ℰ_j ⌢ Δℰ_{j+1}`."*
    Not merely a prefix: the new ledger **is** the old one with exactly one
    stratum appended, and nothing was interleaved into it. -/
@[simp] theorem advance_ledger_eq {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) :
    (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).ledger = X.ledger ++ Δ := rfl

/-! ## Corollary 14.3 — Rejected proposals remain recoverable -/

/-- **Corollary 14.3.** *"Every admission-rejected and coherence-rejected
    proposal remains recoverable with its exact parent, incoming hand, signed
    relative matrix, failed conditions, and creation status."*

    Three of the five are read off the archived core and are the first three
    conjuncts. The last two are events, and they are recoverable by Theorem 14.2
    rather than by anything stated here: `Δℰ_{j+1}` carries the certificate and
    the status, and the ledger is append-only.

    **The hypothesis is not admission and not selection.** It is `hp`, which
    only says the proposal was proposed. That is the sharp reading of the
    corollary: `advanceArchive` never consults admission, so a rejected
    proposal is archived by the same step and the same clause as an accepted
    one. -/
theorem rejection_not_erasure {archive : List Core} {active : List QuestionId}
    {stratum : ℕ} {prov : Provenance} {p : Core × Bool}
    (hp : p ∈ proposals archive active)
    (hfresh : (childCore p.1 p.2 stratum prov).id ∉ archIds archive) :
    childCore p.1 p.2 stratum prov ∈ advanceArchive archive active stratum prov ∧
    (childCore p.1 p.2 stratum prov).parent = some p.1.id ∧
    (childCore p.1 p.2 stratum prov).hand = some p.2 :=
  ⟨child_archived_regardless_of_selection hp hfresh, rfl, rfl⟩

/-- **Corollary 14.3, the signed relative matrix.** The fourth retained item.
    The archived child's matrix is the parent's own accumulated matrix with the
    incoming hand's generator on the right, so the rejected proposal keeps the
    exact signed step that produced it and not a recomputation. -/
theorem child_fullMatrix (c : Core) (g : Bool) (entry : ℕ) (prov : Provenance) :
    (childCore c g entry prov).fullMatrix = c.seed.matrix * Word.G c.relWord * gen g := by
  simp only [childCore, childProposal, proposal, Core.ofProposal, Word.G_snoc]
  rw [Mat2.mul_assoc']

/-! ## Theorem 14.4 — Exact ancestry recovery after one or more ticks -/

/-- The seed identifier of an occurrence identifier: the same question cycle,
    question instance and seed, with the relative word emptied. -/
def seedIdOf (i : QuestionId) : QuestionId := { i with rel := [] }

/-- **The lineage has one seed, not one seed per traversal.** Taking a child
    never changes which seed the identifier names, so every occurrence on a
    descendant chain returns the same value here. This is the uniqueness half of
    14.4's *"one unique seed"*, and it is `rfl` because Definition 4.1 stored the
    seed as a field rather than deriving it. -/
@[simp] theorem seedIdOf_child (i : QuestionId) (g : Bool) :
    seedIdOf (i.child g) = seedIdOf i := rfl

/-- Iterating `dropLast` at least as many times as the list is long empties it.
    The termination argument of 14.4's proof — *"parent traversal strictly
    shortens the finite relative word and therefore reaches a seed"* — in the
    one form it actually takes. -/
theorem dropLast_iterate_nil : ∀ (n : ℕ) (l : Word), l.length ≤ n →
    List.dropLast^[n] l = []
  | 0, l, h => List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
  | n + 1, l, h => by
      rw [Function.iterate_succ_apply]
      refine dropLast_iterate_nil n l.dropLast ?_
      have := List.length_dropLast (xs := l)
      omega

/-- Parent traversal acts on the relative word and on nothing else. -/
theorem parent_iterate (n : ℕ) (i : QuestionId) :
    QuestionId.parent^[n] i = { i with rel := List.dropLast^[n] i.rel } := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
      rfl

/-- **Theorem 14.4, the traversal half.** *"Repeated parent traversal recovers
    one unique seed."* Exactly `|v_y|` steps, and the seed it reaches is
    `seedIdOf`, which `seedIdOf_child` already showed is constant along the
    lineage. -/
theorem ancestry_reaches_seed (i : QuestionId) :
    QuestionId.parent^[i.rel.length] i = seedIdOf i := by
  rw [parent_iterate, dropLast_iterate_nil _ _ (le_refl _)]
  rfl

/-- **Theorem 14.4, the reconstruction half.** *"The archive determines
    `w_y = w_{seed(y)} v_y` and `M_y = M_{seed(y)} G(v_y)`."*

    `v_y` is not searched for: it is `y.id.rel`, the relative word the
    identifier has carried since Definition 4.1. Both equations are therefore
    `rfl`, and the honest report is that 14.4's difficulty was spent in §4 and
    not here. -/
theorem ancestry_recovers (id0 : QuestionId) (seed : History) (v : Word) :
    (proposal id0 seed v).fullWord = seed.word ++ (proposal id0 seed v).id.rel ∧
    (proposal id0 seed v).fullMatrix = seed.matrix * Word.G (proposal id0 seed v).id.rel :=
  ⟨rfl, rfl⟩

/-- **Theorem 14.4, the uniqueness of the path.** *"Lemma 12.1 prevents
    identifier collisions, so the path is unique."* Restated where 14.4 uses it:
    two parent-hand pairs that produce one identifier were the same pair, so
    there is no second lineage into an archived occurrence. -/
theorem lineage_unique {i i' : QuestionId} {g g' : Bool}
    (h : i.child g = i'.child g') : i = i' ∧ g = g' :=
  child_id_inj h

/-! ## Theorem 14.5 — Accumulated winding and closure conservation -/

/-- Definition 11.5's two accumulators, iterated along a descendant segment.
    Each step is exactly `NativeAnn.ofChild`, so this is the book's own
    increment repeated and not a second formula for the same quantity.

    The three optional slots reset to `notEvaluated` at every step, which is
    Definition 11.5's own scoping: `channel`, `lift` and `CF` are evaluated per
    occurrence when the receiver data declares them, and an accumulator that
    carried them forward would be inventing reception the observer did not
    declare. -/
def annAlong {Aux : Type} (a : NativeAnn Aux) : Word → NativeAnn Aux
  | [] => a
  | g :: v => annAlong (NativeAnn.ofChild a.winding a.closure g) v

/-- **Theorem 14.5, first box.** `Ω(O,y) = Ω(O,x) + b(v)`. *"Definition 11.5
    adds `σ(g_i)` at each child event. Summing the first recurrence gives
    `b(v)`."* -/
theorem annAlong_winding {Aux : Type} (a : NativeAnn Aux) (v : Word) :
    (annAlong a v).winding = a.winding + bal v := by
  induction v generalizing a with
  | nil => simp [annAlong]
  | cons g v ih =>
      rw [annAlong, ih]
      cases g <;> simp [NativeAnn.ofChild, bal_true, bal_false] <;> ring

/-- **Theorem 14.5, second box, in word form.**
    `κ_cl(y) = κ_cl(x) + ψ₁₂(v) mod 12`. -/
theorem annAlong_closure {Aux : Type} (a : NativeAnn Aux) (v : Word) :
    (annAlong a v).closure = a.closure + psi12 v := by
  induction v generalizing a with
  | nil => simp [annAlong]
  | cons g v ih =>
      rw [annAlong, ih]
      rw [psi12_cons]
      cases g <;> simp [NativeAnn.ofChild, psi12_R, psi12_L] <;> ring

/-- **Theorem 14.5, second box, in the form the book actually writes it.**
    `κ_cl(y) = κ_cl(x) + ψ₁₂(G(v)) mod 12`, with `ψ₁₂` applied to the **matrix**
    of the descendant segment rather than to its word.

    The book's proof cites *"the homomorphism property of `ψ₁₂`"*, and that
    property is a declared receiver hypothesis, not a Lean `axiom`: `Closure12`
    carries it, `Closure12.map_G` discharges the agreement, and any `A` whatever
    gives the same value (one is built, `Closure12.congruence`, E1-B11). So the word form above
      and the matrix form here are
    one statement, and the accumulator never needed to see a matrix. -/
theorem annAlong_closure_matrix {Aux : Type} (A : Closure12) (a : NativeAnn Aux)
    (v : Word) : (annAlong a v).closure = a.closure + A.psi (Word.G v) := by
  rw [annAlong_closure, A.map_G]

/-- **Theorem 14.5, what "conservation" means.** The accumulated value and the
    value recomputed from the exact world word never drift.

    This is the load-bearing direction and the reason the theorem is called
    conservation rather than additivity: Definition 11.5 forbids recomputing
    `Ω` and `κ_cl` from scratch, so a Lean tree that only proved `bal (u ++ v) =
    bal u + bal v` would have proved a fact about words while leaving the
    carrier's stored annotation unaudited. Here the annotation is the subject
    and the word is the check. -/
theorem conservation {Aux : Type} (id0 : QuestionId) (seed : History) (u v : Word)
    (a : NativeAnn Aux)
    (hw : a.winding = bal (proposal id0 seed u).fullWord)
    (hc : a.closure = psi12 (proposal id0 seed u).fullWord) :
    (annAlong a v).winding = bal (proposal id0 seed (u ++ v)).fullWord ∧
    (annAlong a v).closure = psi12 (proposal id0 seed (u ++ v)).fullWord := by
  constructor
  · rw [annAlong_winding, hw]
    change bal (seed.word ++ u) + bal v = bal (seed.word ++ (u ++ v))
    rw [← List.append_assoc, bal_append, bal_append, bal_append]
  · rw [annAlong_closure, hc]
    change psi12 (seed.word ++ u) + psi12 v = psi12 (seed.word ++ (u ++ v))
    rw [← List.append_assoc, psi12_append, psi12_append, psi12_append]

/-! ## Corollary 14.6 — Finite-character equality keeps its preimages -/

/-- **Corollary 14.6, the collapse.** *"Such a character may map distinct words
    or signed matrices to the same finite value."* A witness, since the
    corollary is false without one: `RL` and `LR` share both retained finite
    characters and are still distinct words with distinct matrices.

    That `G` separates them is the point. The character loses the distinction;
    the substrate the character was computed from does not. -/
theorem character_collapses :
    ∃ u v : Word, u ≠ v ∧ bal u = bal v ∧ psi12 u = psi12 v ∧ Word.G u ≠ Word.G v := by
  refine ⟨[true, false], [false, true], by decide, by decide, by decide, ?_⟩
  intro hG
  exact absurd (Frame.G_inj hG) (by decide)

/-- **Corollary 14.6, at the archived occurrence.** *"Theorem 14.4 retains the
    stable identifiers, exact parent chains, words, and matrices from which both
    values were computed. Governing Rule 0.3 therefore preserves the distinct
    preimages."*

    Two occurrences from one seed with equal closure class, equal winding, and
    unequal identifier, word and matrix. The equal characters are the reception;
    the unequal fields are what the archive kept. -/
theorem closure_equal_occurrences_distinct (id0 : QuestionId) (seed : History) :
    psi12 (proposal id0 seed [true, false]).fullWord
        = psi12 (proposal id0 seed [false, true]).fullWord ∧
    bal (proposal id0 seed [true, false]).fullWord
        = bal (proposal id0 seed [false, true]).fullWord ∧
    (proposal id0 seed [true, false]).id ≠ (proposal id0 seed [false, true]).id ∧
    (proposal id0 seed [true, false]).fullWord
        ≠ (proposal id0 seed [false, true]).fullWord := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change psi12 (seed.word ++ [true, false]) = psi12 (seed.word ++ [false, true])
    rw [psi12_append, psi12_append]
    congr 1
  · change bal (seed.word ++ [true, false]) = bal (seed.word ++ [false, true])
    rw [bal_append, bal_append]
    congr 1
  · intro h
    have : ([true, false] : Word) = [false, true] := congrArg QuestionId.rel h
    exact absurd this (by decide)
  · change seed.word ++ [true, false] ≠ seed.word ++ [false, true]
    intro h
    exact absurd (List.append_cancel_left h) (by decide)

/-! ## Theorem 14.7 — Every strict descendant differs from its ancestor in word and matrix -/

/-- **Theorem 14.7, boxed.** *"If `y` is a strict descendant of `x`, then
    `w_y ≠ w_x` and `M_y ≠ M_x`."*

    The word half is a length count. The matrix half is Elements I's positive
    freeness — Standard Result 3.1's uniqueness, `G_inj` — and nothing weaker
    would do: `G` being a homomorphism gives `M_x G(v) = M_x` only when `G(v) =
    1`, and it is injectivity that forbids a nonempty positive word from
    reaching the identity. -/
theorem no_positive_recurrence {w v : Word} (hv : v ≠ []) :
    w ++ v ≠ w ∧ Word.G w * Word.G v ≠ Word.G w := by
  constructor
  · intro h
    exact hv (List.append_cancel_left (h.trans (List.append_nil w).symm))
  · intro h
    rw [← Word.G_append] at h
    have hw := Frame.G_inj h
    exact hv (List.append_cancel_left (hw.trans (List.append_nil w).symm))

/-- **Theorem 14.7, the local chart clause.** *"If both occurrences lie in the
    same direct positive observer chart, their local positive words and local
    matrices also differ."* Same statement with the observer-local word in place
    of the world word: positive freeness is chart-independent, so the argument
    does not repeat, it applies. -/
theorem no_positive_recurrence_local {a v : Word} (hv : v ≠ []) :
    a ++ v ≠ a ∧ Word.G a * Word.G v ≠ Word.G a :=
  no_positive_recurrence hv

/-- **Theorem 14.7, the sentence after the proof.** *"A later equality under
    closure, channel reception, face reception, or renewal can only be equality
    under that declared receiving map."* Stated as the implication it is: any
    character at all that equates an occurrence with a strict descendant is
    equating things whose exact words differ, so the equality is the map's and
    not the history's. -/
theorem later_equality_is_the_receivers {C : Word → ZMod 12} {w v : Word}
    (hv : v ≠ []) (heq : C (w ++ v) = C w) : w ++ v ≠ w ∧ C (w ++ v) = C w :=
  ⟨(no_positive_recurrence hv).1, heq⟩

/-! ## Theorem 14.8 — Active support and archived existence remain separate -/

/-- **Theorem 14.8, the inclusion that does hold.** `S_{j+1} ⊆ ids(ℋ_{j+1})`.
    Carried by the carrier type since Definition 6.2 rather than proved after
    the fact: no term of `TickCarrier` can name an active occurrence its own
    archive does not hold. -/
theorem support_sub_archive {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) :
    ∀ i ∈ X.active, i ∈ archIds X.archive :=
  X.active_sub_archive

/-- **Theorem 14.8, sharper than the book states it.** The book says neither
    `S_j ⊆ S_{j+1}` nor `S_{j+1} ⊆ S_j` *is required*. In this construction they
    are **disjoint**.

    The reason is the one the book's own proof gives, followed one step further:
    Construction Axiom II.1 selects from newly admitted **child** occurrences,
    Lemma 12.1 makes every child identifier fresh against `ℋ_j`, and
    `active_sub_archive` puts `S_j` inside `ℋ_j`. A new support member is
    therefore not merely un-guaranteed to be an old one, it cannot be one.

    Not a correction. The book's weaker claim is what §14 needs, and a
    disjointness clause in Definition 14.1 would have been wrong for a different
    reason — the order is about the archive, and the support is the component it
    deliberately says nothing about. -/
theorem support_disjoint {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : ∀ i ∈ select (proposals X.archive X.active),
      ∃ p ∈ proposals X.archive X.active, (childCore p.1 p.2 stratum prov).id = i)
    (hfresh : ∀ p ∈ proposals X.archive X.active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive) :
    ∀ i ∈ (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).active,
      i ∉ X.active := by
  intro i hi hold
  obtain ⟨p, hp, rfl⟩ := hsel i hi
  exact hfresh p hp (X.active_sub_archive _ hold)

/-- **Theorem 14.8, the book's own two failures**, read off disjointness. As
    soon as both supports are inhabited, both inclusions are false — so the
    absence of a support clause in Definition 14.1 is forced and not a
    convenience. -/
theorem support_neither_nested {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _)
    (hold : X.active ≠ [])
    (hnew : (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).active ≠ []) :
    ¬ (∀ i ∈ X.active, i ∈ (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).active) ∧
    ¬ (∀ i ∈ (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).active,
        i ∈ X.active) := by
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hold
  obtain ⟨i', hi'⟩ := List.exists_mem_of_ne_nil _ hnew
  constructor
  · intro hsub
    exact support_disjoint X hlaw select stratum prov Δ hsel hfresh i (hsub i hi) hi
  · intro hsub
    exact support_disjoint X hlaw select stratum prov Δ hsel hfresh i' hi' (hsub i' hi')

/-! ## Corollary 14.9 — Later release keeps exact history -/

/-- **Corollary 14.9, the operation the corollary quantifies over.** *"Any later
    operation that releases an occurrence, edge, face, or received identity from
    active reception while preserving the carrier laws of this Element."*

    Every such operation has this shape and no other: change `S`, append to
    `ℰ`, touch nothing else. It is a definition rather than a hypothesis because
    the corollary's content is that the type admits no wider shape — the archive
    is not a parameter here, and a release that wanted to remove a core would
    have to be a different function into a different type. -/
def release {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (newActive : List QuestionId)
    (hsub : ∀ i ∈ newActive, i ∈ archIds X.archive)
    (Δ : List (QuestionId × Aux)) : TickCarrier Aux h :=
  { X with active := newActive, ledger := append X.ledger Δ, active_sub_archive := hsub }

/-- **Corollary 14.9.** *"Its occurrence core, attaching certificate, and prior
    reception events remain archival."* The archive is not merely preserved up
    to membership: it is the identical list, by `rfl`. -/
@[simp] theorem release_archive {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (newActive : List QuestionId) (hsub : _) (Δ : List (QuestionId × Aux)) :
    (release X newActive hsub Δ).archive = X.archive := rfl

/-- **Corollary 14.9, in the order of Definition 14.1.** *"A later status change
    can therefore be represented only by an appended event; deletion would
    violate the carrier type."* -/
theorem release_histExtends {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (newActive : List QuestionId) (hsub : _) (Δ : List (QuestionId × Aux)) :
    HistExtends X (release X newActive hsub Δ) :=
  ⟨le_refl _, fun _ hc => hc, append_preserves_prefix _ _⟩

/-! ## Boundary Statement 14.10 -/

/-- **Boundary Statement 14.10.** *"The temporal engine now has a literal
    one-tick map and a complete proof envelope."*

    The four clauses are the ones §14 is responsible for: the advance is an
    extension in the history order, the tick is `j+1` exactly, the observer and
    the extended question are unchanged, and release adds no exception. The
    other properties the statement lists — finite termination, integer-exact
    comparison, common-prefix covariance, side-exchange covariance, bilateral
    encounter transport — are Theorem 12.5, Theorem 12.6, Theorem 13.2,
    Theorem 13.3 and §13's transport, already proved and not restated here.

    *"No terminal singleton, coherent snap, observer adoption, face attachment,
    or renewal has been presumed."* Nothing in this file mentions any of them,
    and that absence is the claim. -/
theorem boundary_14_10 {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) :
    HistExtends X (advanceCarrier X hlaw select stratum prov Δ hsel hfresh) ∧
    ((advanceCarrier X hlaw select stratum prov Δ hsel hfresh).tick : ℕ)
      = (X.tick : ℕ) + 1 ∧
    (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).observer = X.observer ∧
    (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).question = X.question :=
  ⟨advance_histExtends X hlaw select stratum prov Δ hsel hfresh, rfl, rfl, rfl⟩

end Conservation
end Two
end RatioSpace
