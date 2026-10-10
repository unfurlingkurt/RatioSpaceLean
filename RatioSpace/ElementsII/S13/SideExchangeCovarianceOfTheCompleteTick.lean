/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S13.SideExchange
import RatioSpace.ElementsII.S10.Causal
/-!
  Gap G2-15 · Elements II Theorem 13.3, side-exchange covariance of the
  complete tick.

  **Book statement.** "If the entire observer-question-cavity system and all
  declared predicates are side-exchanged, then `𝔎_{PC}(P𝔛_{τ,j}) = P 𝔎_C(𝔛_{τ,j})`."
  Its proof names two steps this tree did not state:

  (a) "Theorem 8.13 then transports the complete support set." Lean-side, the
  carrier advance takes the selector as a parameter, so
  `advanceCarrier_mirror_componentwise` (`Two/SideExchange.lean`) carries
  `hsel_equiv` as a hypothesis about *that mirrored carrier* and never discharges
  it. Nothing said which selectors satisfy it, and nothing said any did.

  (b) "The maps `W` and `F` commute with complete hand exchange, and the oriented
  sibling relation `A_g` is carried to `A_ḡ`." True by the definitions in
  `Two/Causal.lean`, but no declaration states either half.

  **Built here.**

  For (a), the missing equality. `proposals_mirror_perm` records the proposal
  family of the exchanged carrier as a *permutation* of the exchange of the
  proposal family, because it reads the exchange with the hand-flipping action
  `(c,g) ↦ (P c, ḡ)` — the book's own reading, "the two proposals `xL, xR` are
  carried bijectively to `(Px)R, (Px)L`". Under the hand-*preserving*
  relabelling `(c,g) ↦ (P c, g)` the same fact is an **equality on the nose**
  (`proposals_mirrorArchive`), because `proposals` regenerates the two hand
  labels from the parent rather than transporting them. Both reads are true of
  the same object and neither replaces the other; the permutation is the one that
  matches the book's sentence, and the equality is the one that discharges
  `hsel_equiv`. That equality turns the hypothesis into a *local* condition on
  the selector (`ParentEquivariant`) with no mirrored carrier in it, and the
  condition is then shown non-vacuous and not free: a nonempty selector satisfies
  it (`selectParents`), and a selector naming a fixed occurrence regardless of
  the carrier does not (`selectFixed_not_parentEquivariant`) — which is
  Corollary 13.4's "a fixed occurrence" escape clause, at the selector.

  **What is not claimed.** `Two/SideExchange.lean`'s note that the selector's
  equivariance "is a hypothesis and has to be" stands. Construction Axiom II.1
  supplies the support filter and this file still does not get to assume it is
  parent-equivariant; what changes is that the assumption is now stated about the
  selector alone and is known to be satisfiable. No existing declaration is
  changed and no existing statement is weakened.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_15

open RatioSpace.Word RatioSpace.Two RatioSpace.Two.Advance RatioSpace.Two.SideExchange

/-! ## (a) The proposal family under the hand-preserving relabelling -/

/-- The hand-preserving read of the side action on one proposal: the parent is
    exchanged, the hand label is not. Distinct from `proposals_mirror_perm`'s
    `(c,g) ↦ (P c, ḡ)` and not a substitute for it. -/
def relabel (p : Core × Bool) : Core × Bool := (Core.mirror p.1, p.2)

/-- **The equality `proposals_mirror_perm` leaves as a permutation.** Read with
    the hand-preserving relabelling, the proposal family of the exchanged carrier
    is the relabelled proposal family exactly — no permutation — because
    `Advance.proposals` builds `[(c,L),(c,R)]` from the parent it is looking at
    and so writes the two labels in the same order on both routes. -/
theorem proposals_mirrorArchive (archive : List Core) (active : List QuestionId) :
    Advance.proposals (mirrorArchive archive) (active.map QuestionId.mirror)
      = (Advance.proposals archive active).map relabel := by
  unfold Advance.proposals
  rw [filter_mirrorArchive]
  induction archive.filter (fun c => c.id ∈ active) with
  | nil => rfl
  | cons c l ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append, ih, relabel]
      simp

/-! ## (a) The selector condition, and what discharges `hsel_equiv` -/

/-- **The local condition on a selector.** It carries the exchange of the parents
    to the relabelling of the identifiers it returns. No mirrored carrier appears:
    this is a property of `select` alone, which is what `hsel_equiv` was not. -/
def ParentEquivariant (select : List (Core × Bool) → List QuestionId) : Prop :=
  ∀ ps : List (Core × Bool),
    select (ps.map relabel) = (select ps).map QuestionId.mirror

/-- **`hsel_equiv` discharged.** A parent-equivariant selector satisfies
    Theorem 13.3's selector hypothesis at every carrier. -/
theorem hsel_equiv_of_parentEquivariant
    {select : List (Core × Bool) → List QuestionId}
    (h : ParentEquivariant select) (archive : List Core) (active : List QuestionId) :
    select (Advance.proposals (mirrorArchive archive) (active.map QuestionId.mirror))
      = (select (Advance.proposals archive active)).map QuestionId.mirror := by
  rw [proposals_mirrorArchive]
  exact h _

/-- **Theorem 13.3 at the carrier with no selector hypothesis.** Exactly
    `advanceCarrier_mirror_componentwise`, with `hsel_equiv` replaced by the
    local condition. The existing theorem is untouched and still the general
    statement; this is the instance the book's proof is entitled to. -/
theorem advanceCarrier_mirror_componentwise_of_parentEquivariant
    {Aux : Type} {h : ℕ}
    (X : TickCarrier Aux h) (hlaw : Advance.Lawful X)
    (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel hsel') (hfresh hfresh')
    (hE : ParentEquivariant select) :
    ((Advance.advanceCarrier (TickCarrier.mirror X) hlaw select stratum prov Δ
        hsel' hfresh').archive).Perm
      ((TickCarrier.mirror (Advance.advanceCarrier X hlaw select stratum prov Δ
        hsel hfresh)).archive)
    ∧ (Advance.advanceCarrier (TickCarrier.mirror X) hlaw select stratum prov Δ
        hsel' hfresh').tick
      = (TickCarrier.mirror (Advance.advanceCarrier X hlaw select stratum prov Δ
        hsel hfresh)).tick
    ∧ (Advance.advanceCarrier (TickCarrier.mirror X) hlaw select stratum prov Δ
        hsel' hfresh').active
      = (TickCarrier.mirror (Advance.advanceCarrier X hlaw select stratum prov Δ
        hsel hfresh)).active
    ∧ (Advance.advanceCarrier (TickCarrier.mirror X) hlaw select stratum prov Δ
        hsel' hfresh').ledger
      = (TickCarrier.mirror (Advance.advanceCarrier X hlaw select stratum prov Δ
        hsel hfresh)).ledger :=
  advanceCarrier_mirror_componentwise X hlaw select stratum prov Δ hsel hsel'
    hfresh hfresh' (hsel_equiv_of_parentEquivariant hE X.archive X.active)

/-! ## (a) The condition has teeth on both sides -/

/-- Any selector that reads each proposal's parent through a mirror-equivariant
    function of the parent alone is parent-equivariant. -/
theorem parentEquivariant_of_parentwise (f : Core → QuestionId)
    (hf : ∀ c, f (Core.mirror c) = QuestionId.mirror (f c)) :
    ParentEquivariant (fun ps => ps.map (fun p => f p.1)) := by
  intro ps
  simp [List.map_map, Function.comp_def, relabel, hf]

/-- **A nonempty witness.** The selector returning every proposing parent's
    identifier. Not the empty selector, which satisfies the condition vacuously. -/
def selectParents (ps : List (Core × Bool)) : List QuestionId := ps.map (fun p => p.1.id)

theorem selectParents_parentEquivariant : ParentEquivariant selectParents :=
  parentEquivariant_of_parentwise (fun c => c.id) (fun c => Core.mirror_id c)

/-- The witness is not degenerate: a carrier with one active archived occurrence
    has a nonempty selection. So `hsel_equiv` is satisfiable by a selector that
    actually selects. -/
theorem selectParents_ne_nil {archive : List Core} {active : List QuestionId}
    {c : Core} (hc : c ∈ archive) (ha : c.id ∈ active) :
    selectParents (Advance.proposals archive active) ≠ [] := by
  intro hnil
  have hmem : c ∈ archive.filter (fun c => c.id ∈ active) :=
    List.mem_filter.mpr ⟨hc, by simpa using ha⟩
  obtain ⟨u, v, hsplit⟩ := List.append_of_mem hmem
  rw [selectParents, Advance.proposals, hsplit] at hnil
  simp at hnil

/-- **And the condition is not free.** A selector that names one fixed occurrence
    whatever the carrier is fails it, because the exchanged run must return the
    relabelled identifier and this one returns the same one. Corollary 13.4's
    "a fixed occurrence" clause, read at the selector. -/
def selectFixed (i : QuestionId) (_ : List (Core × Bool)) : List QuestionId := [i]

theorem selectFixed_not_parentEquivariant :
    ¬ ParentEquivariant (selectFixed ⟨0, 0, 0, [false]⟩) := by
  intro h
  have := h []
  simp [selectFixed, QuestionId.mirror, mirrorWord] at this

/-! ## (b) `W`, `F` and `A_g` under complete hand exchange -/

/-- **`W` commutes with hand exchange**, on the nonempty words Definition 10.1
    scopes itself to. `W` flips the terminal hand and the exchange flips every
    hand, and the two flips at the last letter cancel in either order. Not stated
    on `[]`, where `W` appends a hand rather than flipping one and no commutation
    holds. -/
theorem mirrorWord_W {w : Word} (hw : w ≠ []) :
    mirrorWord (W w) = W (mirrorWord w) := by
  obtain ⟨u, g, rfl⟩ := (List.eq_nil_or_concat w).resolve_left hw
  simp [W_append, mirrorWord_append]

/-- The side exchange on words and §3's `shadow` are the same map, by the
    definitions: both send every hand to its opposite. Stated because the proof
    below moves between the two names. Not a new fact. -/
theorem mirrorWord_eq_shadow (w : Word) : mirrorWord w = shadow w := rfl

/-- The exchange commutes with `rs`: reversal does not see a letterwise flip, and
    flipping twice returns. Both sides are `w.reverse`. -/
theorem mirrorWord_rs (w : Word) : mirrorWord (rs w) = rs (mirrorWord w) := by
  simp [mirrorWord, rs, shadow, List.map_reverse, List.map_map, Function.comp_def]

/-- **`F` commutes with hand exchange**, same scope. `F = rs ∘ W ∘ rs` and the
    exchange commutes with `rs`, so this is `mirrorWord_W` conjugated. -/
theorem mirrorWord_F {w : Word} (hw : w ≠ []) :
    mirrorWord (F w) = F (mirrorWord w) := by
  unfold F
  rw [mirrorWord_rs, mirrorWord_W (rs_ne_nil hw), mirrorWord_rs]

/-- **`A_g` is carried to `A_ḡ`.** The oriented sibling relation of Definition
    10.5 conjugated by the exchange `P` is the opposite hand's: `P A_g P = A_ḡ`.
    Both sides are closed terms once the hand is fixed, so this is checked, not
    derived symbolically — the same read `A_false_eq` and `A_inv` already take. -/
theorem A_conj_P (g : Bool) : P * A g * P = A (!g) := by
  cases g <;> rfl

/-- The same fact as the book's sentence reads it: the exchange carries the
    relation attached to `g` to the relation attached to `ḡ`, and doing it twice
    returns. -/
theorem A_conj_P_involutive (g : Bool) : P * (P * A g * P) * P = A g := by
  rw [A_conj_P, A_conj_P, Bool.not_not]

/-! ## (c) The support filter as the selector: Construction Axiom II.1 at the carrier (2026-09-22)

`Two/SideExchange.lean`'s note says Construction Axiom II.1 supplies the support filter and this
file "does not get to assume it is parent-equivariant". Here the filter is built as a selector on
proposals (`selectSupport`), with `A_{j+1}` instantiated as every proposal whose child has an
interior address: Definition 7.1 with the declared predicate `Pred_Γ` everywhere true and the
observer chart the canonical world chart (the score reads `Core.addr`, not the observer-local
`λ_O(y)` of Definition 3.1; the book names that caveat itself). An arbitrary declared predicate
would need its own side-transport, which is Definition 13.1's equation
`γ_i^P(Py; P𝔠, k) = γ_i(y; 𝔠, k)` and Theorem 13.3's own hypothesis, not proved here. On that
instance the question is settled in the form the book states it: the axiom's `ArgMax` is "the
complete set of exact maximizers", a set, so the selector is parent-equivariant **up to
permutation** of its output (`selectSupport_relabel`), and Theorem 13.3 holds at the carrier for
it with the active set equal up to permutation (`advanceCarrier_mirror_support`). Exact list
equality (`ParentEquivariant`) is not available for this selector and should not be expected:
the exchange flips the hand, `proposals` lists the two children of a parent in a fixed hand
order, so whenever both children of a parent tie (Corollary 8.11, `pair_support`) the mirrored
output lists the same set in the other order; and Theorem 8.9 declares storage order to carry
no mathematical content, so exact list equality is not a property the book asks any selector
to have. -/

/-- The child a proposal generates at the tick's stratum and provenance. -/
def propChild (stratum : ℕ) (prov : Provenance) (p : Core × Bool) : Core :=
  childCore p.1 p.2 stratum prov

/-- Its identifier, the entry the selector returns. -/
def childId (stratum : ℕ) (prov : Provenance) (p : Core × Bool) : QuestionId :=
  (propChild stratum prov p).id

/-- Its interior address, when it has one (`ofPres?` fails only on boundary anchors). -/
def propAddr? (stratum : ℕ) (prov : Provenance) (p : Core × Bool) : Option IPres :=
  IPres.ofPres? (propChild stratum prov p).addr

/-- The comparison profile: the generated children's addresses, one per proposal, multiplicity
    kept (Definition 8.1: "each tagged occurrence contributes exactly once"). Definition 7.1's
    `A_{j+1}` is the *admitted* generated occurrences; here every proposal with an interior
    address stands in for it (declared predicate everywhere true, positivity read as
    interiority). -/
def supportFamily (stratum : ℕ) (prov : Provenance) (ps : List (Core × Bool)) : List IPres :=
  ps.filterMap (propAddr? stratum prov)

/-- Whether a proposal's child is an exact maximizer over a profile. -/
def supportPred (stratum : ℕ) (prov : Provenance) (fam : List IPres) (p : Core × Bool) : Bool :=
  match propAddr? stratum prov p with
  | some a => decide (a ∈ support fam)
  | none => false

/-- **Construction Axiom II.1 as a selector, on the profile above.** The children whose address
    is an exact maximizer of the coherence score over the profile; ties kept, nothing chosen among
    them. -/
def selectSupport (stratum : ℕ) (prov : Provenance) (ps : List (Core × Bool)) : List QuestionId :=
  (ps.filter (supportPred stratum prov (supportFamily stratum prov ps))).map (childId stratum prov)

/-- Every identifier the support selector returns is the child of one of the proposals: the
    `hsel` hypothesis `advanceCarrier` asks for, discharged for this selector. -/
theorem selectSupport_hsel (stratum : ℕ) (prov : Provenance) (ps : List (Core × Bool)) :
    ∀ i ∈ selectSupport stratum prov ps, ∃ p ∈ ps, (childCore p.1 p.2 stratum prov).id = i := by
  intro i hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  exact ⟨p, List.mem_of_mem_filter hp, rfl⟩

/-- The hand-flipping read of one proposal. -/
def flipHand (p : Core × Bool) : Core × Bool := (p.1, !p.2)

/-- The child of a relabelled proposal is the mirror of the child of the hand-flipped one
    (`childCore_mirror`). -/
theorem propChild_relabel (stratum : ℕ) (prov : Provenance) (p : Core × Bool) :
    propChild stratum prov (relabel p) = Core.mirror (propChild stratum prov (flipHand p)) := by
  unfold propChild relabel flipHand
  have := childCore_mirror p.1 (!p.2) stratum prov
  rw [Bool.not_not] at this
  exact this

theorem childId_relabel (stratum : ℕ) (prov : Provenance) (p : Core × Bool) :
    childId stratum prov (relabel p) = QuestionId.mirror (childId stratum prov (flipHand p)) := by
  unfold childId
  rw [propChild_relabel]
  rfl

/-- `ofPres?` commutes with the reciprocal: the interior is symmetric. -/
theorem ofPres?_recip (A : Pres) : IPres.ofPres? (recip A) = (IPres.ofPres? A).map IPres.inv := by
  by_cases h : A.Interior
  · have h' : (recip A).Interior := ⟨h.2, h.1⟩
    unfold IPres.ofPres?
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ (recip A).Interior := fun hh => h ⟨hh.2, hh.1⟩
    unfold IPres.ofPres?
    rw [dif_neg h', dif_neg h]
    rfl

theorem propAddr?_relabel (stratum : ℕ) (prov : Provenance) (p : Core × Bool) :
    propAddr? stratum prov (relabel p) = (propAddr? stratum prov (flipHand p)).map Two.Inv := by
  unfold propAddr?
  rw [propChild_relabel]
  exact ofPres?_recip _

/-- The profile of the relabelled family is the mirror of the profile of the hand-flipped one. -/
theorem supportFamily_relabel (stratum : ℕ) (prov : Provenance) (ps : List (Core × Bool)) :
    supportFamily stratum prov (ps.map relabel) =
      (supportFamily stratum prov (ps.map flipHand)).map Two.Inv := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    unfold supportFamily at ih ⊢
    rw [List.map_cons, List.map_cons, List.filterMap_cons, List.filterMap_cons,
      propAddr?_relabel, ih]
    cases propAddr? stratum prov (flipHand p) <;> rfl

/-- Flipping every hand permutes the proposal family: each parent proposes both hands. -/
theorem proposals_flipHand_perm (archive : List Core) (active : List QuestionId) :
    ((Advance.proposals archive active).map flipHand).Perm (Advance.proposals archive active) := by
  unfold Advance.proposals
  induction archive.filter (fun c => c.id ∈ active) with
  | nil => exact List.Perm.refl _
  | cons c l ih =>
    rw [List.flatMap_cons, List.map_append]
    exact List.Perm.append (List.Perm.swap (c, false) (c, true) []) ih

/-- The maximizer test transports through the exchange, pointwise, against a profile that is
    a permutation of the original: Theorem 8.13's side half (`support_side_covariant`) and the
    profile's permutation invariance (`support_perm_mem`). -/
theorem supportPred_relabel (stratum : ℕ) (prov : Provenance) (ps : List (Core × Bool))
    (hperm : (ps.map flipHand).Perm ps) (p : Core × Bool) :
    supportPred stratum prov (supportFamily stratum prov (ps.map relabel)) (relabel p) =
      supportPred stratum prov (supportFamily stratum prov ps) (flipHand p) := by
  unfold supportPred
  rw [propAddr?_relabel, supportFamily_relabel]
  cases propAddr? stratum prov (flipHand p) with
  | none => rfl
  | some a =>
    change decide (Two.Inv a ∈ support ((supportFamily stratum prov (ps.map flipHand)).map Two.Inv))
      = decide (a ∈ support (supportFamily stratum prov ps))
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, support_side_covariant]
    exact support_perm_mem (hperm.filterMap _) a

/-- **The support selector is parent-equivariant up to permutation.** On any proposal family
    closed under hand flipping (every `proposals`, by `proposals_flipHand_perm`), the exchange
    carries the selected set to the mirror of the selected set. -/
theorem selectSupport_relabel (stratum : ℕ) (prov : Provenance) (ps : List (Core × Bool))
    (hperm : (ps.map flipHand).Perm ps) :
    (selectSupport stratum prov (ps.map relabel)).Perm
      ((selectSupport stratum prov ps).map QuestionId.mirror) := by
  unfold selectSupport
  have hL : ((ps.map relabel).filter
        (supportPred stratum prov (supportFamily stratum prov (ps.map relabel)))).map
        (childId stratum prov) =
      (((ps.map flipHand).filter (supportPred stratum prov (supportFamily stratum prov ps))).map
        (childId stratum prov)).map QuestionId.mirror := by
    rw [List.filter_map, List.filter_map, List.map_map, List.map_map, List.map_map]
    have hf : ps.filter
          (supportPred stratum prov (supportFamily stratum prov (ps.map relabel)) ∘ relabel) =
        ps.filter (supportPred stratum prov (supportFamily stratum prov ps) ∘ flipHand) :=
      List.filter_congr (fun p _ => supportPred_relabel stratum prov ps hperm p)
    rw [hf]
    apply List.map_congr_left
    intro p _
    exact childId_relabel stratum prov p
  rw [hL]
  exact ((hperm.filter _).map _).map _

/-- **Theorem 13.3 at the carrier for Construction Axiom II.1's own selector.** Archive and
    active set equal up to permutation, tick and ledger exactly; no selector hypothesis, since
    `selectSupport_hsel` supplies `hsel`. Up to permutation is the book's statement: the active
    support is a set of maximizers. -/
theorem advanceCarrier_mirror_support {Aux : Type} {h : ℕ}
    (X : TickCarrier Aux h) (hlaw : Advance.Lawful X)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hfresh : ∀ p ∈ Advance.proposals X.archive X.active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive)
    (hfresh' : ∀ p ∈ Advance.proposals (TickCarrier.mirror X).archive (TickCarrier.mirror X).active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds (TickCarrier.mirror X).archive) :
    ((Advance.advanceCarrier (TickCarrier.mirror X) hlaw (selectSupport stratum prov) stratum prov Δ
        (selectSupport_hsel stratum prov _) hfresh').archive).Perm
      ((TickCarrier.mirror (Advance.advanceCarrier X hlaw (selectSupport stratum prov) stratum prov Δ
        (selectSupport_hsel stratum prov _) hfresh)).archive)
    ∧ (Advance.advanceCarrier (TickCarrier.mirror X) hlaw (selectSupport stratum prov) stratum prov Δ
        (selectSupport_hsel stratum prov _) hfresh').tick
      = (TickCarrier.mirror (Advance.advanceCarrier X hlaw (selectSupport stratum prov) stratum prov Δ
        (selectSupport_hsel stratum prov _) hfresh)).tick
    ∧ ((Advance.advanceCarrier (TickCarrier.mirror X) hlaw (selectSupport stratum prov) stratum prov Δ
        (selectSupport_hsel stratum prov _) hfresh').active).Perm
      ((TickCarrier.mirror (Advance.advanceCarrier X hlaw (selectSupport stratum prov) stratum prov Δ
        (selectSupport_hsel stratum prov _) hfresh)).active)
    ∧ (Advance.advanceCarrier (TickCarrier.mirror X) hlaw (selectSupport stratum prov) stratum prov Δ
        (selectSupport_hsel stratum prov _) hfresh').ledger
      = (TickCarrier.mirror (Advance.advanceCarrier X hlaw (selectSupport stratum prov) stratum prov Δ
        (selectSupport_hsel stratum prov _) hfresh)).ledger := by
  refine ⟨advanceArchive_mirror_perm X.archive X.active stratum prov, rfl, ?_, rfl⟩
  change (selectSupport stratum prov
      (Advance.proposals (mirrorArchive X.archive) (X.active.map QuestionId.mirror))).Perm
    ((selectSupport stratum prov (Advance.proposals X.archive X.active)).map QuestionId.mirror)
  rw [proposals_mirrorArchive]
  exact selectSupport_relabel stratum prov _ (proposals_flipHand_perm X.archive X.active)

#print axioms selectSupport
#print axioms selectSupport_hsel
#print axioms propChild_relabel
#print axioms ofPres?_recip
#print axioms supportFamily_relabel
#print axioms proposals_flipHand_perm
#print axioms supportPred_relabel
#print axioms selectSupport_relabel
#print axioms advanceCarrier_mirror_support

end G2_15
end Gaps
end RatioSpace
