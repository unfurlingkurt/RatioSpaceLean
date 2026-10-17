/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.RootOrbit
/-!
  Elements II §16 Proposition 16.9 — The crystallization beat.

  **Part (i) is the general half and it is the only part of 16.9 that is a
  theorem about every question rather than a finite verification.** It says
  Definition 8.1 cannot discriminate below three admitted occurrences, so a lone
  seed's first advance always keeps both children, and a beat therefore
  exists at all: singleton, pair, singleton, pair, until something with three
  or more admitted children breaks step.

  Elements II's Corollaries 8.11 and 8.12 already say this about `support`.
  Here it is said about `axiomSelect`, the concrete rule Theorem 16.5 and
  Theorem 16.8 actually ran, because `axiomSelect` inlines the maximality
  test rather than calling `support`, and a fact proved of `support` is not
  automatically a fact about the rule the traces used.

  **What `axiomSelect` may still drop, and it is not coherence.** A core whose
  address does not resolve to an interior positive presentation is filtered
  out before any coherence value is compared. Below three admitted occurrences that is
  the *only* thing dropped, and the theorem says so in that form rather than
  claiming nothing is dropped at all.

  **Part (iv)'s last sentence, built.** *"The two constructions are the same
  kernel on the same words displaced by one tick."* `RootOrbit.lean`'s
  account of Theorem 16.8 deliberately declined to state any equality between
  the side-selected trace and the polarized trace, having checked each
  independently. Proposition 16.9(iv) is the book asserting that equality, so
  it is stated and decided here: six equalities per side, `S_k(𝒬_ε^L) =
  S_{k-1}(𝒬_L)` for `k = 2 … 7`.

  **Not stated here.** Parts (ii)
  and (iii) are exact finite verifications over 1023 lone seeds through tick
  12 and over 560 two- and three-member ensembles through tick 9. Neither is
  a `decide` this kernel can carry: Theorem 16.5's seven concrete ticks on
  one seed are already the file's heaviest computation, and (ii) is that
  computation 1023 times over, twelve ticks deep. The route is an exact
  integer enumeration outside Lean with the trace certificates re-checked
  here on the rows it flags, not a `native_decide`.

  **Part (iv)'s `h = 8` clause is built, and it needed the horizon out of the
  type.** `Lawful` is `tick < h`, so tick 8 is not a carrier of
  `TickCarrier Unit hQ` at all; `X0h` takes the declared horizon as a
  parameter and `𝒬_L`/`𝒬_R` are rebuilt at horizon 8 from the seed. Ticks 1
  through 7 come out identical to `theorem_16_5_polarized_L`/`_R`, decided
  again rather than assumed, which is the check that the declared horizon is
  inert. Tick 8 closes on `LLLRRRRRR` / `RRRLLLLLL`, addressed `7:22` /
  `22:7` — the value part (ii) displays for the seed `LL` at `h = 7`, reached
  here from `𝒬_L` one tick later.
-/

namespace RatioSpace
namespace Two
namespace Beat

open Mat2 Word Frame Pres RatioSpace RatioSpace.Zphi Advance Accumulation RootOrbit

/-! ## Part (i) — Definition 8.1 cannot discriminate below three -/

/-- Every address that resolves out of an admitted core is a member of the
    family Definition 8.1 compares against. -/
theorem mem_admittedFam {MO : Mat2} {stratum : ℕ} {prov : Provenance}
    {props : List (Core × Bool)} {c : Core} {y : IPres}
    (hc : c ∈ admittedCores MO stratum prov props)
    (hy : addrOf MO c = some y) :
    y ∈ admittedFam MO stratum prov props :=
  List.mem_filterMap.mpr ⟨c, hc, hy⟩

/-- **Corollary 8.11 and Corollary 8.12, as a statement about coherence values.** With
    at most two members in the admitted family every member's coherence value is
    maximal, so no member can be rejected for failing to maximise. The
    two-member case is Theorem 8.10's exact degeneracy (`pair_coherence_equal`);
    the one-member case is reflexivity. -/
theorem all_maximal_of_le_two (fam : List IPres) (h : fam.length ≤ 2)
    (y : IPres) (hy : y ∈ fam) :
    ∀ z ∈ fam, coherenceOf fam z ≤ coherenceOf fam y := by
  match fam, h, hy with
  | [], _, hy => cases hy
  | [u], _, hy =>
      intro z hz
      simp only [List.mem_singleton] at hy hz
      subst hy; subst hz
      exact le_refl _
  | [u, v], _, hy =>
      intro z hz
      have huv : coherenceOf [u, v] u = coherenceOf [u, v] v := pair_coherence_equal u v
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy hz
      rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
      exacts [le_refl _, le_of_eq huv.symm, le_of_eq huv, le_refl _]
  | _ :: _ :: _ :: _, h, _ =>
      simp only [List.length_cons] at h
      omega

/-- **Proposition 16.9(i), clause 3 — "coherence rejection requires
    `|A_{j+1}| ≥ 3`", at the rule the traces ran.** Below three admitted
    occurrences every admitted core with a resolving address is selected. -/
theorem selected_of_addressed {MO : Mat2} {stratum : ℕ} {prov : Provenance}
    {props : List (Core × Bool)}
    (h : (admittedFam MO stratum prov props).length ≤ 2)
    {c : Core} (hc : c ∈ admittedCores MO stratum prov props)
    {y : IPres} (hy : addrOf MO c = some y) :
    c.id ∈ axiomSelect MO stratum prov props := by
  have hmem : y ∈ admittedFam MO stratum prov props := mem_admittedFam hc hy
  have hmax := all_maximal_of_le_two _ h y hmem
  refine List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, ?_⟩, rfl⟩
  simp only [hy, decide_eq_true_eq, List.all_eq_true]
  intro z hz
  exact hmax z hz

/-- **Proposition 16.9(i), clauses 1 and 2 — the lone seed's advance never
    discriminates.** Stated at an arbitrary stratum, so it is clause 2 (every
    singleton `S_j` whose two children are admitted is followed by
    `|S_{j+1}| = 2`) and clause 1 (`j = 0`) at once. -/
theorem lone_seed_keeps_both {MO : Mat2} {stratum : ℕ} {prov : Provenance}
    {archive : List Core} {active : List QuestionId} {c : Core}
    (hone : archive.filter (fun d => d.id ∈ active) = [c])
    (hadm : ∀ b : Bool, negLoad (Q MO (childCore c b stratum prov).fullMatrix) = 0)
    {yF yT : IPres}
    (hF : addrOf MO (childCore c false stratum prov) = some yF)
    (hT : addrOf MO (childCore c true stratum prov) = some yT) :
    admittedCores MO stratum prov (proposals archive active) =
      [childCore c false stratum prov, childCore c true stratum prov] ∧
    admittedFam MO stratum prov (proposals archive active) = [yF, yT] ∧
    (childCore c false stratum prov).id ∈
      axiomSelect MO stratum prov (proposals archive active) ∧
    (childCore c true stratum prov).id ∈
      axiomSelect MO stratum prov (proposals archive active) := by
  have hprops : proposals archive active = [(c, false), (c, true)] := by
    unfold proposals
    rw [hone]
    simp
  have hcores : admittedCores MO stratum prov (proposals archive active) =
      [childCore c false stratum prov, childCore c true stratum prov] := by
    unfold admittedCores
    rw [hprops]
    simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
    simp only [decide_eq_true_eq]
    rw [if_pos (by exact hadm false), if_pos (by exact hadm true)]
  have hfam : admittedFam MO stratum prov (proposals archive active) = [yF, yT] := by
    unfold admittedFam
    rw [hcores]
    simp [hF, hT]
  have hlen : (admittedFam MO stratum prov (proposals archive active)).length ≤ 2 := by
    rw [hfam]; simp
  refine ⟨hcores, hfam, ?_, ?_⟩
  · exact selected_of_addressed hlen (by rw [hcores]; simp) hF
  · exact selected_of_addressed hlen (by rw [hcores]; simp) hT

/-- **Proposition 16.9(i), clause 4 — the bound is sharp, witnessed rather
    than asserted.** The root question's tick-7 advance runs on a support of
    two occurrences, admits four children, and rejects two of them. So an
    advance from a support of at least two admitted occurrences *can*
    discriminate, which is the clause's own word. The four coherence values are
    Proposition 16.6's certificates. -/
theorem discrimination_needs_three :
    (admittedFam MOeps 7 seed164Prov props6eps).length = 4 ∧
    (axiomSelect MOeps 7 seed164Prov props6eps).length = 2 := by
  refine ⟨by decide, by decide⟩

/-! ## Part (iv) — the beat at the declared horizon -/

/-- **Proposition 16.9(iv), the horizon reading, on the three built
    questions.** `h_𝒬 = 7` is odd. The lone-seed genesis questions close at
    tick 6 and tie at tick 7; the side-selected root closes at tick 7. Both
    halves are read off the traces Theorem 16.5 and Theorem 16.8 already
    certified against the book's table. -/
theorem prop_16_9_iv_horizon :
    (activeWords XL6).length = 1 ∧ (activeWords XL7).length = 2 ∧
    (activeWords XR6).length = 1 ∧ (activeWords XR7).length = 2 ∧
    (activeWords XepsSideL7).length = 1 ∧
    (activeWords XepsSideR7).length = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Proposition 16.9(iv), last sentence.** *"The two constructions are the
    same kernel on the same words displaced by one tick."* Six equalities per
    side. `RootOrbit.lean` checked the two traces independently and
    deliberately stated no equality between them; the book asserts it, so it
    is decided here rather than inferred from the two tables matching by
    eye. -/
theorem prop_16_9_iv_displacement_L :
    activeWords XepsSideL2 = activeWords XL1 ∧
    activeWords XepsSideL3 = activeWords XL2 ∧
    activeWords XepsSideL4 = activeWords XL3 ∧
    activeWords XepsSideL5 = activeWords XL4 ∧
    activeWords XepsSideL6 = activeWords XL5 ∧
    activeWords XepsSideL7 = activeWords XL6 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The mirror of `prop_16_9_iv_displacement_L`, decided independently. -/
theorem prop_16_9_iv_displacement_R :
    activeWords XepsSideR2 = activeWords XR1 ∧
    activeWords XepsSideR3 = activeWords XR2 ∧
    activeWords XepsSideR4 = activeWords XR3 ∧
    activeWords XepsSideR5 = activeWords XR4 ∧
    activeWords XepsSideR6 = activeWords XR5 ∧
    activeWords XepsSideR7 = activeWords XR6 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩


/-! ## Part (iv), the `h = 8` clause -/

/-- **Definition 16.4's seed at an arbitrary declared horizon.** `X0` fixes
    `h = h_𝒬 = 7`, and `Lawful` is exactly `tick < h`, so tick 8 is not a
    carrier of that type at all: the horizon is in the type. Proposition
    16.9(iv) reads `𝒬_L` and `𝒬_R` at `h = 6` and `h = 8` as well as at the
    declared 7, so the same questions are needed at horizon 8. Nothing else
    moves — the observer, the extended question, the seed core and every
    selection rule below are horizon-independent — which is itself the
    content of the clause: the beat is a property of the words, not of where
    the question was declared to stop. -/
def X0h (h : ℕ) (w : Word) : TickCarrier Unit h where
  observer := observer164
  question := canonicalQuestion w
  tick := ⟨0, Nat.succ_pos h⟩
  active := [seed164Id]
  archive := [seedCore seed164Id ⟨Frame.empty, w⟩ 0 seed164Prov]
  ledger := []
  active_sub_archive := by
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    simp only [archIds, List.map_cons, List.map_nil, List.mem_singleton]
    rfl

/-- The generalisation adds nothing at the declared horizon. -/
theorem X0h_hQ (w : Word) : X0h hQ w = X0 w := rfl

def YL0 : TickCarrier Unit 8 := X0h 8 [false]
def MOL8 : Mat2 := (YL0).observer.matrix
theorem hlawY0L : Lawful YL0 := by decide
def propsY0L : List (Core × Bool) := proposals (YL0).archive (YL0).active
def selY1L : List (Core × Bool) → List QuestionId := axiomSelect MOL8 1 seed164Prov
theorem hselY0L : ∀ i ∈ selY1L propsY0L, ∃ p ∈ propsY0L,
    (childCore p.1 p.2 1 seed164Prov).id = i :=
  axiomSelect_hsel MOL8 1 seed164Prov propsY0L
theorem hfreshY0L : ∀ p ∈ propsY0L,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds (YL0).archive := by decide
def YL1 : TickCarrier Unit 8 :=
  advanceCarrier YL0 hlawY0L selY1L 1 seed164Prov [] hselY0L hfreshY0L

theorem hlawY1L : Lawful YL1 := by decide
def propsY1L : List (Core × Bool) := proposals (YL1).archive (YL1).active
def selY2L : List (Core × Bool) → List QuestionId := axiomSelect MOL8 2 seed164Prov
theorem hselY1L : ∀ i ∈ selY2L propsY1L, ∃ p ∈ propsY1L,
    (childCore p.1 p.2 2 seed164Prov).id = i :=
  axiomSelect_hsel MOL8 2 seed164Prov propsY1L
theorem hfreshY1L : ∀ p ∈ propsY1L,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds (YL1).archive := by decide
def YL2 : TickCarrier Unit 8 :=
  advanceCarrier YL1 hlawY1L selY2L 2 seed164Prov [] hselY1L hfreshY1L

theorem hlawY2L : Lawful YL2 := by decide
def propsY2L : List (Core × Bool) := proposals (YL2).archive (YL2).active
def selY3L : List (Core × Bool) → List QuestionId := axiomSelect MOL8 3 seed164Prov
theorem hselY2L : ∀ i ∈ selY3L propsY2L, ∃ p ∈ propsY2L,
    (childCore p.1 p.2 3 seed164Prov).id = i :=
  axiomSelect_hsel MOL8 3 seed164Prov propsY2L
theorem hfreshY2L : ∀ p ∈ propsY2L,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds (YL2).archive := by decide
def YL3 : TickCarrier Unit 8 :=
  advanceCarrier YL2 hlawY2L selY3L 3 seed164Prov [] hselY2L hfreshY2L

theorem hlawY3L : Lawful YL3 := by decide
def propsY3L : List (Core × Bool) := proposals (YL3).archive (YL3).active
def selY4L : List (Core × Bool) → List QuestionId := axiomSelect MOL8 4 seed164Prov
theorem hselY3L : ∀ i ∈ selY4L propsY3L, ∃ p ∈ propsY3L,
    (childCore p.1 p.2 4 seed164Prov).id = i :=
  axiomSelect_hsel MOL8 4 seed164Prov propsY3L
theorem hfreshY3L : ∀ p ∈ propsY3L,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds (YL3).archive := by decide
def YL4 : TickCarrier Unit 8 :=
  advanceCarrier YL3 hlawY3L selY4L 4 seed164Prov [] hselY3L hfreshY3L

theorem hlawY4L : Lawful YL4 := by decide
def propsY4L : List (Core × Bool) := proposals (YL4).archive (YL4).active
def selY5L : List (Core × Bool) → List QuestionId := axiomSelect MOL8 5 seed164Prov
theorem hselY4L : ∀ i ∈ selY5L propsY4L, ∃ p ∈ propsY4L,
    (childCore p.1 p.2 5 seed164Prov).id = i :=
  axiomSelect_hsel MOL8 5 seed164Prov propsY4L
theorem hfreshY4L : ∀ p ∈ propsY4L,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds (YL4).archive := by decide
def YL5 : TickCarrier Unit 8 :=
  advanceCarrier YL4 hlawY4L selY5L 5 seed164Prov [] hselY4L hfreshY4L

theorem hlawY5L : Lawful YL5 := by decide
def propsY5L : List (Core × Bool) := proposals (YL5).archive (YL5).active
def selY6L : List (Core × Bool) → List QuestionId := axiomSelect MOL8 6 seed164Prov
theorem hselY5L : ∀ i ∈ selY6L propsY5L, ∃ p ∈ propsY5L,
    (childCore p.1 p.2 6 seed164Prov).id = i :=
  axiomSelect_hsel MOL8 6 seed164Prov propsY5L
theorem hfreshY5L : ∀ p ∈ propsY5L,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds (YL5).archive := by decide
def YL6 : TickCarrier Unit 8 :=
  advanceCarrier YL5 hlawY5L selY6L 6 seed164Prov [] hselY5L hfreshY5L

theorem hlawY6L : Lawful YL6 := by decide
def propsY6L : List (Core × Bool) := proposals (YL6).archive (YL6).active
def selY7L : List (Core × Bool) → List QuestionId := axiomSelect MOL8 7 seed164Prov
theorem hselY6L : ∀ i ∈ selY7L propsY6L, ∃ p ∈ propsY6L,
    (childCore p.1 p.2 7 seed164Prov).id = i :=
  axiomSelect_hsel MOL8 7 seed164Prov propsY6L
theorem hfreshY6L : ∀ p ∈ propsY6L,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds (YL6).archive := by decide
def YL7 : TickCarrier Unit 8 :=
  advanceCarrier YL6 hlawY6L selY7L 7 seed164Prov [] hselY6L hfreshY6L

theorem hlawY7L : Lawful YL7 := by decide
def propsY7L : List (Core × Bool) := proposals (YL7).archive (YL7).active
def selY8L : List (Core × Bool) → List QuestionId := axiomSelect MOL8 8 seed164Prov
theorem hselY7L : ∀ i ∈ selY8L propsY7L, ∃ p ∈ propsY7L,
    (childCore p.1 p.2 8 seed164Prov).id = i :=
  axiomSelect_hsel MOL8 8 seed164Prov propsY7L
theorem hfreshY7L : ∀ p ∈ propsY7L,
    (childCore p.1 p.2 8 seed164Prov).id ∉ archIds (YL7).archive := by decide
def YL8 : TickCarrier Unit 8 :=
  advanceCarrier YL7 hlawY7L selY8L 8 seed164Prov [] hselY7L hfreshY7L

def YR0 : TickCarrier Unit 8 := X0h 8 [true]
def MOR8 : Mat2 := (YR0).observer.matrix
theorem hlawY0R : Lawful YR0 := by decide
def propsY0R : List (Core × Bool) := proposals (YR0).archive (YR0).active
def selY1R : List (Core × Bool) → List QuestionId := axiomSelect MOR8 1 seed164Prov
theorem hselY0R : ∀ i ∈ selY1R propsY0R, ∃ p ∈ propsY0R,
    (childCore p.1 p.2 1 seed164Prov).id = i :=
  axiomSelect_hsel MOR8 1 seed164Prov propsY0R
theorem hfreshY0R : ∀ p ∈ propsY0R,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds (YR0).archive := by decide
def YR1 : TickCarrier Unit 8 :=
  advanceCarrier YR0 hlawY0R selY1R 1 seed164Prov [] hselY0R hfreshY0R

theorem hlawY1R : Lawful YR1 := by decide
def propsY1R : List (Core × Bool) := proposals (YR1).archive (YR1).active
def selY2R : List (Core × Bool) → List QuestionId := axiomSelect MOR8 2 seed164Prov
theorem hselY1R : ∀ i ∈ selY2R propsY1R, ∃ p ∈ propsY1R,
    (childCore p.1 p.2 2 seed164Prov).id = i :=
  axiomSelect_hsel MOR8 2 seed164Prov propsY1R
theorem hfreshY1R : ∀ p ∈ propsY1R,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds (YR1).archive := by decide
def YR2 : TickCarrier Unit 8 :=
  advanceCarrier YR1 hlawY1R selY2R 2 seed164Prov [] hselY1R hfreshY1R

theorem hlawY2R : Lawful YR2 := by decide
def propsY2R : List (Core × Bool) := proposals (YR2).archive (YR2).active
def selY3R : List (Core × Bool) → List QuestionId := axiomSelect MOR8 3 seed164Prov
theorem hselY2R : ∀ i ∈ selY3R propsY2R, ∃ p ∈ propsY2R,
    (childCore p.1 p.2 3 seed164Prov).id = i :=
  axiomSelect_hsel MOR8 3 seed164Prov propsY2R
theorem hfreshY2R : ∀ p ∈ propsY2R,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds (YR2).archive := by decide
def YR3 : TickCarrier Unit 8 :=
  advanceCarrier YR2 hlawY2R selY3R 3 seed164Prov [] hselY2R hfreshY2R

theorem hlawY3R : Lawful YR3 := by decide
def propsY3R : List (Core × Bool) := proposals (YR3).archive (YR3).active
def selY4R : List (Core × Bool) → List QuestionId := axiomSelect MOR8 4 seed164Prov
theorem hselY3R : ∀ i ∈ selY4R propsY3R, ∃ p ∈ propsY3R,
    (childCore p.1 p.2 4 seed164Prov).id = i :=
  axiomSelect_hsel MOR8 4 seed164Prov propsY3R
theorem hfreshY3R : ∀ p ∈ propsY3R,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds (YR3).archive := by decide
def YR4 : TickCarrier Unit 8 :=
  advanceCarrier YR3 hlawY3R selY4R 4 seed164Prov [] hselY3R hfreshY3R

theorem hlawY4R : Lawful YR4 := by decide
def propsY4R : List (Core × Bool) := proposals (YR4).archive (YR4).active
def selY5R : List (Core × Bool) → List QuestionId := axiomSelect MOR8 5 seed164Prov
theorem hselY4R : ∀ i ∈ selY5R propsY4R, ∃ p ∈ propsY4R,
    (childCore p.1 p.2 5 seed164Prov).id = i :=
  axiomSelect_hsel MOR8 5 seed164Prov propsY4R
theorem hfreshY4R : ∀ p ∈ propsY4R,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds (YR4).archive := by decide
def YR5 : TickCarrier Unit 8 :=
  advanceCarrier YR4 hlawY4R selY5R 5 seed164Prov [] hselY4R hfreshY4R

theorem hlawY5R : Lawful YR5 := by decide
def propsY5R : List (Core × Bool) := proposals (YR5).archive (YR5).active
def selY6R : List (Core × Bool) → List QuestionId := axiomSelect MOR8 6 seed164Prov
theorem hselY5R : ∀ i ∈ selY6R propsY5R, ∃ p ∈ propsY5R,
    (childCore p.1 p.2 6 seed164Prov).id = i :=
  axiomSelect_hsel MOR8 6 seed164Prov propsY5R
theorem hfreshY5R : ∀ p ∈ propsY5R,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds (YR5).archive := by decide
def YR6 : TickCarrier Unit 8 :=
  advanceCarrier YR5 hlawY5R selY6R 6 seed164Prov [] hselY5R hfreshY5R

theorem hlawY6R : Lawful YR6 := by decide
def propsY6R : List (Core × Bool) := proposals (YR6).archive (YR6).active
def selY7R : List (Core × Bool) → List QuestionId := axiomSelect MOR8 7 seed164Prov
theorem hselY6R : ∀ i ∈ selY7R propsY6R, ∃ p ∈ propsY6R,
    (childCore p.1 p.2 7 seed164Prov).id = i :=
  axiomSelect_hsel MOR8 7 seed164Prov propsY6R
theorem hfreshY6R : ∀ p ∈ propsY6R,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds (YR6).archive := by decide
def YR7 : TickCarrier Unit 8 :=
  advanceCarrier YR6 hlawY6R selY7R 7 seed164Prov [] hselY6R hfreshY6R

theorem hlawY7R : Lawful YR7 := by decide
def propsY7R : List (Core × Bool) := proposals (YR7).archive (YR7).active
def selY8R : List (Core × Bool) → List QuestionId := axiomSelect MOR8 8 seed164Prov
theorem hselY7R : ∀ i ∈ selY8R propsY7R, ∃ p ∈ propsY7R,
    (childCore p.1 p.2 8 seed164Prov).id = i :=
  axiomSelect_hsel MOR8 8 seed164Prov propsY7R
theorem hfreshY7R : ∀ p ∈ propsY7R,
    (childCore p.1 p.2 8 seed164Prov).id ∉ archIds (YR7).archive := by decide
def YR8 : TickCarrier Unit 8 :=
  advanceCarrier YR7 hlawY7R selY8R 8 seed164Prov [] hselY7R hfreshY7R

set_option maxRecDepth 8000 in
/-- **Proposition 16.9(iv), the `h = 8` clause, run.** `𝒬_L` and `𝒬_R` at
    declared horizon 8: the support is a singleton at tick 6, a pair at
    tick 7, and a singleton again at tick 8. So each closes at 6 and at 8 and
    ties at 7, which is the book's own sentence, and the beat is even.

    The first seven ticks reproduce `theorem_16_5_polarized_L`/`_R` exactly,
    which is not assumed here: `Y_L` is a different Lean term from `X_L` (a
    different horizon lives in the type) and the table is decided again from
    the seed. That the two agree is the check that the declared horizon is
    inert, and it is stated as an equality below rather than left to the eye. -/
theorem prop_16_9_iv_horizon_eight :
    (activeWords YL6).length = 1 ∧ (activeWords YL7).length = 2 ∧
    (activeWords YL8).length = 1 ∧
    (activeWords YR6).length = 1 ∧ (activeWords YR7).length = 2 ∧
    (activeWords YR8).length = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **The declared horizon is inert through tick 7.** Same words, same order,
    at `h = 8` as at `h = h_𝒬 = 7`. -/
theorem horizon_inert :
    activeWords YL1 = activeWords XL1 ∧ activeWords YL2 = activeWords XL2 ∧
    activeWords YL3 = activeWords XL3 ∧ activeWords YL4 = activeWords XL4 ∧
    activeWords YL5 = activeWords XL5 ∧ activeWords YL6 = activeWords XL6 ∧
    activeWords YL7 = activeWords XL7 ∧
    activeWords YR7 = activeWords XR7 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

set_option maxRecDepth 8000 in
/-- **The tick-8 closing occurrences, and one point of contact with part
    (ii).** `𝒬_L` closes on `LLLRRRRRR` and `𝒬_R` on its mirror, addressed
    `7:22` and `22:7`.

    Part (ii) lists `LL` among the four lone seeds of length at most 9 that
    close at the declared horizon `h = 7`, and displays its closing occurrence
    as `LLLRRRRRR`, `7:22`. `𝒬_L`'s tick 8 is a different question at a
    different tick, and it arrives at the same nine-letter word and the same
    addressed relation — the book's own value, reached from the other side.
    That is one row of (ii) corroborated, not (ii): the other 1022 seeds are
    untouched here. -/
theorem tick_eight_closing_words :
    activeWords YL8 = [[false, false, false, true, true, true, true, true, true]] ∧
    activeWords YR8 = [[true, true, true, false, false, false, false, false, false]] ∧
    (addressedList (activeWords YL8)).map (fun r => (r.p, r.q)) = [(7, 22)] ∧
    (addressedList (activeWords YR8)).map (fun r => (r.p, r.q)) = [(22, 7)] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

#print axioms mem_admittedFam
#print axioms all_maximal_of_le_two
#print axioms selected_of_addressed
#print axioms lone_seed_keeps_both
#print axioms prop_16_9_iv_displacement_L
#print axioms prop_16_9_iv_horizon_eight
#print axioms tick_eight_closing_words

end Beat
end Two
end RatioSpace
