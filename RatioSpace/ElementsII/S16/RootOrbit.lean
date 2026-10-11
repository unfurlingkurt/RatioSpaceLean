/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S15.Accumulation
/-!
  Elements II §16 Theorem 16.5 — Exact root and polarized seed orbits.

  **The exact seven-tick support table, for all three of Definition 16.4's
  canonical questions, certified against the book's own table.** Theorem 16.5
  also states an extension of the root's pattern to tick 40, tie certificates
  at every four-member row (Theorem 8.5's `c0`/`c1`), and a claim verified
  through `h = 12` — that further content is not attempted here and is the
  next move, not a silent gap: see the closing remark.

  **The one genuine engineering decision made here.** `advanceCarrier` only
  asks two obligations, `hsel` and `hfresh` — the extra `hgrow`/`hcard` that
  `Policy`/`iterate` (`Accumulation.lean`) demand exist to support the general
  theory (Corollary 15.3's archive-size bound), which Theorem 16.5 does not
  need. So this file chains seven concrete `advanceCarrier` calls directly per
  question rather than building a `Policy` term, and discharges `hsel`/
  `hfresh` at each step by `decide` over the fully concrete finite data that
  step already has — no generic invariant proof over an arbitrary schedule is
  needed, because every step here is one fixed, closed computation, not a
  universal claim about every reachable carrier.

  The same runs are also the general engine's: `AxiomPolicy.lean` builds this
  file's selection rule as a `Policy` (`axiomPolicy`) and proves its iterate
  from each seed carrier equals the chains below tick for tick
  (`axiomPolicy_trace_L`/`_eps`/`_R`).

  **The admission reading, checked by running it rather than assumed.**
  Definition 16.4's own account already found that nothing downstream reads
  `question.depth`, so no cavity-boundary infrastructure (Definition 4.9's
  `γ_∂`) gates these running ticks in this tree, and `preds := []` makes
  predicate composition vacuous. So `axiomSelect` below applies only the two
  checks that remain live: `Neg(Q_{O,y}) = 0` (direct-positive chart) and
  Definition 8.1's `support` filter (`Coherence.lean`). Every one of
  the three traces below reproduces the book's table exactly under that
  reading alone, with no proposal ever failing the direct-positive test — so
  the coherence filter is doing every rejection the table shows, exactly as
  the book's own proof of Theorem 16.5 reads it: *"form both child proposals
  of every active occurrence, retain all of them, and apply Definition
  8.1 to the complete admitted family."* Had a cavity bound genuinely
  gated these ticks, the traces below would have diverged from the table
  instead of matching it tick for tick; they do not, so this reading is
  confirmed rather than merely convenient.
-/

namespace RatioSpace
namespace Two
namespace RootOrbit

open Mat2 Word Frame Pres RatioSpace RatioSpace.Zphi Advance Accumulation

/-! ## The concrete one-tick selection rule -/

/-- The direct-positive-admitted children of one tick's proposals, before the
    coherence filter — exposed on its own so the exact-tie certificates
    (Theorem 16.5's proof, Proposition 16.6) can name the family Definition
    8.1 actually chooses among, rather than re-deriving it. -/
def admittedCores (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (props : List (Core × Bool)) : List Core :=
  (props.map (fun p => childCore p.1 p.2 stratum prov)).filter
    (fun c => decide (negLoad (Q MO c.fullMatrix) = 0))

/-- One admitted child's address, when it resolves to an interior positive
    presentation. -/
def addrOf (MO : Mat2) (c : Core) : Option IPres :=
  (lambda MO c.fullMatrix).bind IPres.ofPres?

/-- **The admitted family Definition 8.1's `ArgMax` runs over** —
    `admittedCores`, addressed. -/
def admittedFam (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (props : List (Core × Bool)) : List IPres :=
  (admittedCores MO stratum prov props).filterMap (addrOf MO)

/-- **Definition 8.1, made concrete for one tick.** Every proposal is
    built to a child `Core`; the direct-positive chart test (`Neg(Q_{O,y}) =
    0`) admits or rejects it; `support` (`Coherence.lean`) keeps the complete
    coherence-maximal subset of whatever survives. No cavity-boundary term:
    see the file header. -/
def axiomSelect (MO : Mat2) (stratum : ℕ) (prov : Provenance) :
    List (Core × Bool) → List QuestionId :=
  fun props =>
    let admitted := admittedCores MO stratum prov props
    let fam := admittedFam MO stratum prov props
    (admitted.filter (fun c =>
      match addrOf MO c with
      | some y => decide (fam.all (fun z => coherenceOf fam z ≤ coherenceOf fam y))
      | none => false)).map Core.id

/-- **`hsel`, discharged generically for `axiomSelect` at any tick.** Every
    identifier `axiomSelect` returns is a filtered child's own identifier, and
    every filtered child came from `props.map (childCore · · stratum prov)` —
    list-lemma chasing, no arithmetic. -/
theorem axiomSelect_hsel (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (props : List (Core × Bool)) :
    ∀ i ∈ axiomSelect MO stratum prov props,
      ∃ p ∈ props, (childCore p.1 p.2 stratum prov).id = i := by
  intro i hi
  unfold axiomSelect at hi
  simp only [List.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  have hc1 : c ∈ admittedCores MO stratum prov props := List.mem_of_mem_filter hc
  unfold admittedCores at hc1
  have hc2 : c ∈ props.map (fun p => childCore p.1 p.2 stratum prov) :=
    List.mem_of_mem_filter hc1
  simp only [List.mem_map] at hc2
  obtain ⟨p, hp, rfl⟩ := hc2
  exact ⟨p, hp, rfl⟩

/-! ## Definition 16.4's seed, instantiated as a tick-zero carrier -/

/-- The one seed's provenance: its own question/seed source, event `(0,0)`. -/
def seed164Prov : Provenance := ⟨seed164Id, seed164Id, ⟨0, 0⟩⟩

/-- **The tick-zero carrier for one of Definition 16.4's three questions**,
    built from its own seed word `w ∈ {ε, [L], [R]}`. One archived core, one
    active identifier, empty ledger. -/
def X0 (w : Word) : TickCarrier Unit hQ where
  observer := observer164
  question := canonicalQuestion w
  tick := ⟨0, by decide⟩
  active := [seed164Id]
  archive := [seedCore seed164Id ⟨Frame.empty, w⟩ 0 seed164Prov]
  ledger := []
  active_sub_archive := by
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    simp only [archIds, List.map_cons, List.map_nil, List.mem_singleton]
    rfl

theorem X0_tick (w : Word) : ((X0 w).tick : ℕ) = 0 := rfl

/-- `𝒬_ε`'s tick-zero carrier. -/
def Xeps0 : TickCarrier Unit hQ := X0 []

/-! ## The concrete tick-zero-through-tick-seven trace, for each of the three questions -/
def MOeps : Mat2 := Xeps0.observer.matrix

theorem hlaw0eps : Lawful Xeps0 := by decide
def props0eps : List (Core × Bool) := proposals Xeps0.archive Xeps0.active

def sel1eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 1 seed164Prov

theorem hsel0eps : ∀ i ∈ sel1eps props0eps, ∃ p ∈ props0eps,
    (childCore p.1 p.2 1 seed164Prov).id = i := axiomSelect_hsel MOeps 1 seed164Prov props0eps
theorem hfresh0eps : ∀ p ∈ props0eps,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds Xeps0.archive := by
  decide

def Xeps1 : TickCarrier Unit hQ :=
  advanceCarrier Xeps0 hlaw0eps sel1eps 1 seed164Prov [] hsel0eps hfresh0eps


theorem hlaw1eps : Lawful Xeps1 := by decide
def props1eps : List (Core × Bool) := proposals Xeps1.archive Xeps1.active
def sel2eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 2 seed164Prov
theorem hsel1eps : ∀ i ∈ sel2eps props1eps, ∃ p ∈ props1eps,
    (childCore p.1 p.2 2 seed164Prov).id = i := axiomSelect_hsel MOeps 2 seed164Prov props1eps
theorem hfresh1eps : ∀ p ∈ props1eps,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds Xeps1.archive := by
  decide

def Xeps2 : TickCarrier Unit hQ :=
  advanceCarrier Xeps1 hlaw1eps sel2eps 2 seed164Prov [] hsel1eps hfresh1eps


theorem hlaw2eps : Lawful Xeps2 := by decide
def props2eps : List (Core × Bool) := proposals Xeps2.archive Xeps2.active
def sel3eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 3 seed164Prov
theorem hsel2eps : ∀ i ∈ sel3eps props2eps, ∃ p ∈ props2eps,
    (childCore p.1 p.2 3 seed164Prov).id = i := axiomSelect_hsel MOeps 3 seed164Prov props2eps
theorem hfresh2eps : ∀ p ∈ props2eps,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds Xeps2.archive := by
  decide
def Xeps3 : TickCarrier Unit hQ :=
  advanceCarrier Xeps2 hlaw2eps sel3eps 3 seed164Prov [] hsel2eps hfresh2eps

theorem hlaw3eps : Lawful Xeps3 := by decide
def props3eps : List (Core × Bool) := proposals Xeps3.archive Xeps3.active
def sel4eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 4 seed164Prov
theorem hsel3eps : ∀ i ∈ sel4eps props3eps, ∃ p ∈ props3eps,
    (childCore p.1 p.2 4 seed164Prov).id = i := axiomSelect_hsel MOeps 4 seed164Prov props3eps
theorem hfresh3eps : ∀ p ∈ props3eps,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds Xeps3.archive := by
  decide
def Xeps4 : TickCarrier Unit hQ :=
  advanceCarrier Xeps3 hlaw3eps sel4eps 4 seed164Prov [] hsel3eps hfresh3eps

theorem hlaw4eps : Lawful Xeps4 := by decide
def props4eps : List (Core × Bool) := proposals Xeps4.archive Xeps4.active
def sel5eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 5 seed164Prov
theorem hsel4eps : ∀ i ∈ sel5eps props4eps, ∃ p ∈ props4eps,
    (childCore p.1 p.2 5 seed164Prov).id = i := axiomSelect_hsel MOeps 5 seed164Prov props4eps
theorem hfresh4eps : ∀ p ∈ props4eps,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds Xeps4.archive := by
  decide
def Xeps5 : TickCarrier Unit hQ :=
  advanceCarrier Xeps4 hlaw4eps sel5eps 5 seed164Prov [] hsel4eps hfresh4eps

theorem hlaw5eps : Lawful Xeps5 := by decide
def props5eps : List (Core × Bool) := proposals Xeps5.archive Xeps5.active
def sel6eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 6 seed164Prov
theorem hsel5eps : ∀ i ∈ sel6eps props5eps, ∃ p ∈ props5eps,
    (childCore p.1 p.2 6 seed164Prov).id = i := axiomSelect_hsel MOeps 6 seed164Prov props5eps
theorem hfresh5eps : ∀ p ∈ props5eps,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds Xeps5.archive := by
  decide
def Xeps6 : TickCarrier Unit hQ :=
  advanceCarrier Xeps5 hlaw5eps sel6eps 6 seed164Prov [] hsel5eps hfresh5eps

theorem hlaw6eps : Lawful Xeps6 := by decide
def props6eps : List (Core × Bool) := proposals Xeps6.archive Xeps6.active
def sel7eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 7 seed164Prov
theorem hsel6eps : ∀ i ∈ sel7eps props6eps, ∃ p ∈ props6eps,
    (childCore p.1 p.2 7 seed164Prov).id = i := axiomSelect_hsel MOeps 7 seed164Prov props6eps
theorem hfresh6eps : ∀ p ∈ props6eps,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds Xeps6.archive := by
  decide
def Xeps7 : TickCarrier Unit hQ :=
  advanceCarrier Xeps6 hlaw6eps sel7eps 7 seed164Prov [] hsel6eps hfresh6eps

/-- `𝒬_L`'s tick-zero carrier. -/
def XL0 : TickCarrier Unit hQ := X0 [false]
def MOL : Mat2 := XL0.observer.matrix
theorem hlaw0L : Lawful XL0 := by decide
def props0L : List (Core × Bool) := proposals XL0.archive XL0.active
def sel1L : List (Core × Bool) → List QuestionId := axiomSelect MOL 1 seed164Prov
theorem hsel0L : ∀ i ∈ sel1L props0L, ∃ p ∈ props0L,
    (childCore p.1 p.2 1 seed164Prov).id = i := axiomSelect_hsel MOL 1 seed164Prov props0L
theorem hfresh0L : ∀ p ∈ props0L,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XL0.archive := by
  decide
def XL1 : TickCarrier Unit hQ := advanceCarrier XL0 hlaw0L sel1L 1 seed164Prov [] hsel0L hfresh0L

theorem hlaw1L : Lawful XL1 := by decide
def props1L : List (Core × Bool) := proposals XL1.archive XL1.active
def sel2L : List (Core × Bool) → List QuestionId := axiomSelect MOL 2 seed164Prov
theorem hsel1L : ∀ i ∈ sel2L props1L, ∃ p ∈ props1L,
    (childCore p.1 p.2 2 seed164Prov).id = i := axiomSelect_hsel MOL 2 seed164Prov props1L
theorem hfresh1L : ∀ p ∈ props1L,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XL1.archive := by
  decide
def XL2 : TickCarrier Unit hQ := advanceCarrier XL1 hlaw1L sel2L 2 seed164Prov [] hsel1L hfresh1L

theorem hlaw2L : Lawful XL2 := by decide
def props2L : List (Core × Bool) := proposals XL2.archive XL2.active
def sel3L : List (Core × Bool) → List QuestionId := axiomSelect MOL 3 seed164Prov
theorem hsel2L : ∀ i ∈ sel3L props2L, ∃ p ∈ props2L,
    (childCore p.1 p.2 3 seed164Prov).id = i := axiomSelect_hsel MOL 3 seed164Prov props2L
theorem hfresh2L : ∀ p ∈ props2L,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XL2.archive := by
  decide
def XL3 : TickCarrier Unit hQ := advanceCarrier XL2 hlaw2L sel3L 3 seed164Prov [] hsel2L hfresh2L

theorem hlaw3L : Lawful XL3 := by decide
def props3L : List (Core × Bool) := proposals XL3.archive XL3.active
def sel4L : List (Core × Bool) → List QuestionId := axiomSelect MOL 4 seed164Prov
theorem hsel3L : ∀ i ∈ sel4L props3L, ∃ p ∈ props3L,
    (childCore p.1 p.2 4 seed164Prov).id = i := axiomSelect_hsel MOL 4 seed164Prov props3L
theorem hfresh3L : ∀ p ∈ props3L,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XL3.archive := by
  decide
def XL4 : TickCarrier Unit hQ := advanceCarrier XL3 hlaw3L sel4L 4 seed164Prov [] hsel3L hfresh3L

theorem hlaw4L : Lawful XL4 := by decide
def props4L : List (Core × Bool) := proposals XL4.archive XL4.active
def sel5L : List (Core × Bool) → List QuestionId := axiomSelect MOL 5 seed164Prov
theorem hsel4L : ∀ i ∈ sel5L props4L, ∃ p ∈ props4L,
    (childCore p.1 p.2 5 seed164Prov).id = i := axiomSelect_hsel MOL 5 seed164Prov props4L
theorem hfresh4L : ∀ p ∈ props4L,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XL4.archive := by
  decide
def XL5 : TickCarrier Unit hQ := advanceCarrier XL4 hlaw4L sel5L 5 seed164Prov [] hsel4L hfresh4L

theorem hlaw5L : Lawful XL5 := by decide
def props5L : List (Core × Bool) := proposals XL5.archive XL5.active
def sel6L : List (Core × Bool) → List QuestionId := axiomSelect MOL 6 seed164Prov
theorem hsel5L : ∀ i ∈ sel6L props5L, ∃ p ∈ props5L,
    (childCore p.1 p.2 6 seed164Prov).id = i := axiomSelect_hsel MOL 6 seed164Prov props5L
theorem hfresh5L : ∀ p ∈ props5L,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XL5.archive := by
  decide
def XL6 : TickCarrier Unit hQ := advanceCarrier XL5 hlaw5L sel6L 6 seed164Prov [] hsel5L hfresh5L

theorem hlaw6L : Lawful XL6 := by decide
def props6L : List (Core × Bool) := proposals XL6.archive XL6.active
def sel7L : List (Core × Bool) → List QuestionId := axiomSelect MOL 7 seed164Prov
theorem hsel6L : ∀ i ∈ sel7L props6L, ∃ p ∈ props6L,
    (childCore p.1 p.2 7 seed164Prov).id = i := axiomSelect_hsel MOL 7 seed164Prov props6L
theorem hfresh6L : ∀ p ∈ props6L,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XL6.archive := by
  decide
def XL7 : TickCarrier Unit hQ := advanceCarrier XL6 hlaw6L sel7L 7 seed164Prov [] hsel6L hfresh6L

/-- `𝒬_R`'s tick-zero carrier. -/
def XR0 : TickCarrier Unit hQ := X0 [true]
def MOR : Mat2 := XR0.observer.matrix
theorem hlaw0R : Lawful XR0 := by decide
def props0R : List (Core × Bool) := proposals XR0.archive XR0.active
def sel1R : List (Core × Bool) → List QuestionId := axiomSelect MOR 1 seed164Prov
theorem hsel0R : ∀ i ∈ sel1R props0R, ∃ p ∈ props0R,
    (childCore p.1 p.2 1 seed164Prov).id = i := axiomSelect_hsel MOR 1 seed164Prov props0R
theorem hfresh0R : ∀ p ∈ props0R,
    (childCore p.1 p.2 1 seed164Prov).id ∉ archIds XR0.archive := by
  decide
def XR1 : TickCarrier Unit hQ := advanceCarrier XR0 hlaw0R sel1R 1 seed164Prov [] hsel0R hfresh0R

theorem hlaw1R : Lawful XR1 := by decide
def props1R : List (Core × Bool) := proposals XR1.archive XR1.active
def sel2R : List (Core × Bool) → List QuestionId := axiomSelect MOR 2 seed164Prov
theorem hsel1R : ∀ i ∈ sel2R props1R, ∃ p ∈ props1R,
    (childCore p.1 p.2 2 seed164Prov).id = i := axiomSelect_hsel MOR 2 seed164Prov props1R
theorem hfresh1R : ∀ p ∈ props1R,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XR1.archive := by
  decide
def XR2 : TickCarrier Unit hQ := advanceCarrier XR1 hlaw1R sel2R 2 seed164Prov [] hsel1R hfresh1R

theorem hlaw2R : Lawful XR2 := by decide
def props2R : List (Core × Bool) := proposals XR2.archive XR2.active
def sel3R : List (Core × Bool) → List QuestionId := axiomSelect MOR 3 seed164Prov
theorem hsel2R : ∀ i ∈ sel3R props2R, ∃ p ∈ props2R,
    (childCore p.1 p.2 3 seed164Prov).id = i := axiomSelect_hsel MOR 3 seed164Prov props2R
theorem hfresh2R : ∀ p ∈ props2R,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XR2.archive := by
  decide
def XR3 : TickCarrier Unit hQ := advanceCarrier XR2 hlaw2R sel3R 3 seed164Prov [] hsel2R hfresh2R

theorem hlaw3R : Lawful XR3 := by decide
def props3R : List (Core × Bool) := proposals XR3.archive XR3.active
def sel4R : List (Core × Bool) → List QuestionId := axiomSelect MOR 4 seed164Prov
theorem hsel3R : ∀ i ∈ sel4R props3R, ∃ p ∈ props3R,
    (childCore p.1 p.2 4 seed164Prov).id = i := axiomSelect_hsel MOR 4 seed164Prov props3R
theorem hfresh3R : ∀ p ∈ props3R,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XR3.archive := by
  decide
def XR4 : TickCarrier Unit hQ := advanceCarrier XR3 hlaw3R sel4R 4 seed164Prov [] hsel3R hfresh3R

theorem hlaw4R : Lawful XR4 := by decide
def props4R : List (Core × Bool) := proposals XR4.archive XR4.active
def sel5R : List (Core × Bool) → List QuestionId := axiomSelect MOR 5 seed164Prov
theorem hsel4R : ∀ i ∈ sel5R props4R, ∃ p ∈ props4R,
    (childCore p.1 p.2 5 seed164Prov).id = i := axiomSelect_hsel MOR 5 seed164Prov props4R
theorem hfresh4R : ∀ p ∈ props4R,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XR4.archive := by
  decide
def XR5 : TickCarrier Unit hQ := advanceCarrier XR4 hlaw4R sel5R 5 seed164Prov [] hsel4R hfresh4R

theorem hlaw5R : Lawful XR5 := by decide
def props5R : List (Core × Bool) := proposals XR5.archive XR5.active
def sel6R : List (Core × Bool) → List QuestionId := axiomSelect MOR 6 seed164Prov
theorem hsel5R : ∀ i ∈ sel6R props5R, ∃ p ∈ props5R,
    (childCore p.1 p.2 6 seed164Prov).id = i := axiomSelect_hsel MOR 6 seed164Prov props5R
theorem hfresh5R : ∀ p ∈ props5R,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XR5.archive := by
  decide
def XR6 : TickCarrier Unit hQ := advanceCarrier XR5 hlaw5R sel6R 6 seed164Prov [] hsel5R hfresh5R

theorem hlaw6R : Lawful XR6 := by decide
def props6R : List (Core × Bool) := proposals XR6.archive XR6.active
def sel7R : List (Core × Bool) → List QuestionId := axiomSelect MOR 7 seed164Prov
theorem hsel6R : ∀ i ∈ sel7R props6R, ∃ p ∈ props6R,
    (childCore p.1 p.2 7 seed164Prov).id = i := axiomSelect_hsel MOR 7 seed164Prov props6R
theorem hfresh6R : ∀ p ∈ props6R,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XR6.archive := by
  decide
def XR7 : TickCarrier Unit hQ := advanceCarrier XR6 hlaw6R sel7R 7 seed164Prov [] hsel6R hfresh6R

/-! ## Theorem 16.5 — the exact support table, certified

    `false = L`, `true = R`, matching `Word`'s own convention (`Frame.stepL`/
    `stepR`) everywhere in this tree. Each list is the active support's own
    full words, in the order `axiomSelect`'s filter naturally produces —
    the same list Corollary 6.10 already insists is not deduplicated, so an
    ordered-list equality is a faithful (if slightly stronger) reading of the
    book's set notation, not a weaker one: it also pins down that no member is
    silently repeated or dropped. -/

/-- The active support of one carrier, read off as the archived occurrences'
    own full words — exactly what Theorem 16.5's table lists at each tick. -/
def activeWords {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) : List Word :=
  (X.archive.filter (fun c => c.id ∈ X.active)).map Core.fullWord

/-- **Theorem 16.5, the root question `𝒬_ε`, ticks 1 through 7, exactly as the
    book's table gives them.** `Sj(𝒬_ε) = {LRᵏ, RLᵏ}` for `k = j - 1`, `j ≥ 1` —
    checked by running the schedule, not read off the closed form; the closed
    form is a corollary of this, not yet stated separately. -/
theorem theorem_16_5_root :
    activeWords Xeps1 = [[false], [true]] ∧
    activeWords Xeps2 = [[false, true], [true, false]] ∧
    activeWords Xeps3 = [[false, true, true], [true, false, false]] ∧
    activeWords Xeps4 = [[false, true, true, true], [true, false, false, false]] ∧
    activeWords Xeps5 =
      [[false, true, true, true, true], [true, false, false, false, false]] ∧
    activeWords Xeps6 =
      [[false, true, true, true, true, true], [true, false, false, false, false, false]] ∧
    activeWords Xeps7 =
      [[false, true, true, true, true, true, true],
       [true, false, false, false, false, false, false]] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Theorem 16.5, the polarized question `𝒬_L`, ticks 1 through 7.**
    Collapses to an occurrence singleton at ticks 3 and 6, exactly where the
    book's table says it does — a genuine strict-maximizer computation
    (Theorem 8.5's certificate), not the free two-candidate case. -/
theorem theorem_16_5_polarized_L :
    activeWords XL1 = [[false, false], [false, true]] ∧
    activeWords XL2 = [[false, false, false], [false, true, false]] ∧
    activeWords XL3 = [[false, false, false, true]] ∧
    activeWords XL4 = [[false, false, false, true, false], [false, false, false, true, true]] ∧
    activeWords XL5 =
      [[false, false, false, true, false, false], [false, false, false, true, true, true]] ∧
    activeWords XL6 = [[false, false, false, true, true, true, true]] ∧
    activeWords XL7 =
      [[false, false, false, true, true, true, true, false],
       [false, false, false, true, true, true, true, true]] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Theorem 16.5, the polarized question `𝒬_R`, ticks 1 through 7** — the
    side mirror of `theorem_16_5_polarized_L`, checked independently rather
    than derived from it (no side-exchange action on `TickCarrier` exists in
    this tree yet; Theorem 15.5's own account already flags that gap). -/
theorem theorem_16_5_polarized_R :
    activeWords XR1 = [[true, false], [true, true]] ∧
    activeWords XR2 = [[true, false, true], [true, true, true]] ∧
    activeWords XR3 = [[true, true, true, false]] ∧
    activeWords XR4 = [[true, true, true, false, false], [true, true, true, false, true]] ∧
    activeWords XR5 =
      [[true, true, true, false, false, false], [true, true, true, false, true, true]] ∧
    activeWords XR6 = [[true, true, true, false, false, false, false]] ∧
    activeWords XR7 =
      [[true, true, true, false, false, false, false, false],
       [true, true, true, false, false, false, false, true]] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Theorem 16.5's proof, the exact-tie certificates

    The book's own proof of Theorem 16.5 names two four-member admitted
    families where Definition 8.1 retains a tied pair whole rather
    than picking a strict maximizer: the advance `1→2` and the advance `4→5`
    of `𝒬_L` (and, by side-exchange covariance, `𝒬_R`). Each pair shares a
    tension histogram — the book is explicit that they do **not** share the
    keyed Definition 7.4 signature underneath it, only its unordered sum —
    and Theorem 8.5's `c0`/`c1` certificate (`Coherence.lean`) makes the
    common coherence value exact rather than merely decidable-equal. All four values
    below check against the book's own displayed histograms and coherence values
    (`RatioSpace_Elements_II_v0.22`, Theorem 16.5's proof paragraph). -/

/-- **The advance `1→2` of `𝒬_L`.** Admitted family `[LLL, LLR, LRL, LRR]`
    (`admittedFam` in that order). `LLL`/`LRL` (indices 0, 2) share histogram
    `{0,2,4,5}` and coherence value `φ`; `LLR`/`LRR` (indices 1, 3) share `{0,2,4,8}`
    and coherence value `42 - 25φ`. The first pair is coherence-maximal, which is why
    `theorem_16_5_polarized_L` already gives `S_2(𝒬_L) = {LLL, LRL}`. -/
theorem tie_1_2_L :
    (admittedFam MOL 2 seed164Prov props1L).map
        (tensions (admittedFam MOL 2 seed164Prov props1L)) =
      [[0, 4, 5, 2], [4, 0, 2, 8], [5, 2, 0, 4], [2, 8, 4, 0]] ∧
    (admittedFam MOL 2 seed164Prov props1L).map
        (coherenceOf (admittedFam MOL 2 seed164Prov props1L)) =
      [(⟨0, 1⟩ : Zphi), ⟨42, -25⟩, ⟨0, 1⟩, ⟨42, -25⟩] := by
  refine ⟨by decide, by decide⟩

/-- **The advance `4→5` of `𝒬_L`.** Admitted family
    `[LLLRLL, LLLRLR, LLLRRL, LLLRRR]`. `LLLRLL`/`LLLRRR` (indices 0, 3)
    share histogram `{0,8,14,24}` and coherence value `75670 - 46766φ`; `LLLRLR`/
    `LLLRRL` (indices 1, 2) share `{0,14,17,24}` and coherence value
    `73052 - 45148φ`. The first pair is coherence-maximal, matching
    `theorem_16_5_polarized_L`'s `S_5(𝒬_L) = {LLLRLL, LLLRRR}`. -/
theorem tie_4_5_L :
    (admittedFam MOL 5 seed164Prov props4L).map
        (tensions (admittedFam MOL 5 seed164Prov props4L)) =
      [[0, 24, 14, 8], [24, 0, 17, 14], [14, 17, 0, 24], [8, 14, 24, 0]] ∧
    (admittedFam MOL 5 seed164Prov props4L).map
        (coherenceOf (admittedFam MOL 5 seed164Prov props4L)) =
      [(⟨75670, -46766⟩ : Zphi), ⟨73052, -45148⟩, ⟨73052, -45148⟩, ⟨75670, -46766⟩] := by
  refine ⟨by decide, by decide⟩

/-! ## The terminal exact tie, `Q_L` and `Q_R` at tick 7

    Theorem 16.5's own text: the two polarized questions terminate
    unresolved-multiple, `{LLLRRRRL, LLLRRRRR}` and its side mirror, "whose
    two members have the common coherence value `1 + φ⁻⁵⁷`." Tick 7's admitted family
    is a genuine two-candidate case — Theorem 8.10's free retention, not
    Theorem 8.5's tie-break — and needs no trace beyond what
    `theorem_16_5_polarized_L`/`_R` already build: `XL6`/`XR6` are each an
    occurrence singleton, so `props6L`/`props6R` propose exactly the two
    children `coherenceOf_pair` reads directly. -/

/-- **The terminal coherence value of `𝒬_L`'s tick-7 pair is exactly `1 + φ⁻⁵⁷`.**
    `phiNegPow 57`'s own certificate (`golden_negative_power`) gives
    `⟨1 - Fib 58, Fib 57⟩ = ⟨-591286729878, 365435296162⟩`, which is what
    `decide` finds both members of the admitted family scoring. -/
theorem terminal_tie_L :
    (admittedFam MOL 7 seed164Prov props6L).map
        (tensions (admittedFam MOL 7 seed164Prov props6L)) = [[0, 57], [57, 0]] ∧
    (admittedFam MOL 7 seed164Prov props6L).map
        (coherenceOf (admittedFam MOL 7 seed164Prov props6L)) =
      [1 + phiNegPow 57, 1 + phiNegPow 57] := by
  refine ⟨by decide, by decide⟩

/-- **The side mirror**, checked independently rather than derived from
    `terminal_tie_L` — same reason `theorem_16_5_polarized_R` is independent
    of `_polarized_L`: no side-exchange action on `TickCarrier` exists in
    this tree yet. -/
theorem terminal_tie_R :
    (admittedFam MOR 7 seed164Prov props6R).map
        (tensions (admittedFam MOR 7 seed164Prov props6R)) = [[0, 57], [57, 0]] ∧
    (admittedFam MOR 7 seed164Prov props6R).map
        (coherenceOf (admittedFam MOR 7 seed164Prov props6R)) =
      [1 + phiNegPow 57, 1 + phiNegPow 57] := by
  refine ⟨by decide, by decide⟩

/-! ## Proposition 16.6, the root row

    The polarized rows are already certified above: `terminal_tie_L`/
    `terminal_tie_R` give exactly the book's `\{0,57\}` histogram and
    `1 + φ⁻⁵⁷` coherence value for both tables' two tied-selected occurrences. The root
    row is the one the book's own proof of Theorem 16.5 defers to Proposition
    16.6 rather than settling inline — *"the exact comparison confirms which
    pair"* — because it is a genuine four-member family with two rejected
    members, not a two-member free retention. `props6eps`'s admitted family
    already carries all four: no new selection machinery, the same
    `admittedFam`/`tensions`/`coherenceOf` this file has used throughout. -/

/-- **Proposition 16.6, the root row.** `admittedFam MOeps 7 seed164Prov
    props6eps` is exactly the book's four occurrences in the book's own order
    — `LRRRRRL` (`11:13`), `LRRRRRR` (`7:8`), `RLLLLLL` (`8:7`), `RLLLLLR`
    (`13:11`) — with tensions `\{0,12,17,32\}` for the two coherence-rejected
    members and `\{0,10,12,32\}` for the two tied-selected members, scoring
    `3522228 - 2176856φ` and `3524901 - 2178508φ` respectively. Checked
    against the book's own displayed table before writing anything;
    `theorem_16_5_root`'s `Xeps7` equality is the corollary that `ArgMax`
    actually keeps the second pair, not the first. -/
theorem prop_16_6_root :
    (admittedFam MOeps 7 seed164Prov props6eps).map (fun y => (y.p, y.q)) =
      [(11, 13), (7, 8), (8, 7), (13, 11)] ∧
    (admittedFam MOeps 7 seed164Prov props6eps).map
        (tensions (admittedFam MOeps 7 seed164Prov props6eps)) =
      [[0, 32, 12, 17], [32, 0, 10, 12], [12, 10, 0, 32], [17, 12, 32, 0]] ∧
    (admittedFam MOeps 7 seed164Prov props6eps).map
        (coherenceOf (admittedFam MOeps 7 seed164Prov props6eps)) =
      [(⟨3522228, -2176856⟩ : Zphi), ⟨3524901, -2178508⟩,
       ⟨3524901, -2178508⟩, ⟨3522228, -2176856⟩] := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The root's selected coherence value strictly exceeds its rejected coherence value.** The
    book states the same fact as `2673 - 1652φ > 0` (the difference of the two
    values above) and certifies its sign through Lemma 8.6's `(s, b)` pair,
    `s = 2(2673) - 1652 = 3694`, `s² - 5(1652)² = 116 > 0`. `decidableLT`
    (`Zphi.lean`) decides the same comparison directly on the two coherence
    values themselves, with no intermediate difference term — a sharper route
    to the identical fact, not a different one: `Zphi.lt_def` unfolds to the
    same embedding Lemma 8.6's own proof runs on. -/
theorem prop_16_6_root_selected_gt_rejected :
    (⟨3522228, -2176856⟩ : Zphi) < (⟨3524901, -2178508⟩ : Zphi) := by decide

#print axioms prop_16_6_root
#print axioms prop_16_6_root_selected_gt_rejected

/-! ## Definition 16.7 — Side-selected root questions

    `γ_side` is "a total exact map of the type fixed in Definition 4.3"
    (`OccPred`, `ProposalRecord → C → ℕ → Bool`) that reads only the
    proposal identifier and the event position. Every proposal identifier
    this construction ever compares is a child built by `childCore p.1 p.2
    stratum prov`, so the two fields `γ_side` needs — which hand produced the
    proposal, and which event — are exactly `p.2` and `stratum`, already
    present at the point `axiomSelect` filters, so this construction reads
    them there directly rather than through `QPred` (`Support.lean`). -/

/-- **Definition 16.7's admission machinery, generalizing `axiomSelect` by one
    more filter rather than replacing it.** `reject stratum g = true` removes
    a would-be child of hand `g` at event `stratum` before the direct-positive
    and coherence tests ever see it — the same "declared predicate gates a
    proposal before comparison" shape Definition 11.3's `Pred_Γ` names, made
    concrete for this one construction the way `axiomSelect` already made
    Definition 8.1 concrete. -/
def admittedCoresSide (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (reject : ℕ → Bool → Bool) (props : List (Core × Bool)) : List Core :=
  ((props.filter (fun p => !reject stratum p.2)).map
      (fun p => childCore p.1 p.2 stratum prov)).filter
    (fun c => decide (negLoad (Q MO c.fullMatrix) = 0))

/-- **The admitted family `axiomSelectSide`'s `ArgMax` runs over.** -/
def admittedFamSide (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (reject : ℕ → Bool → Bool) (props : List (Core × Bool)) : List IPres :=
  (admittedCoresSide MO stratum prov reject props).filterMap (addrOf MO)

/-- **Definition 8.1, made concrete for one tick under Definition
    16.7's extra predicate.** Identical to `axiomSelect` past the point
    `admittedCoresSide` has already removed the rejected hand. -/
def axiomSelectSide (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (reject : ℕ → Bool → Bool) : List (Core × Bool) → List QuestionId :=
  fun props =>
    let admitted := admittedCoresSide MO stratum prov reject props
    let fam := admittedFamSide MO stratum prov reject props
    (admitted.filter (fun c =>
      match addrOf MO c with
      | some y => decide (fam.all (fun z => coherenceOf fam z ≤ coherenceOf fam y))
      | none => false)).map Core.id

/-- **`reject := fun _ _ => false` reproduces `axiomSelect` exactly, not
    merely something equally permissive.** The same discipline as
    `assembleWith_none_eq_assemble` (`Accumulation.lean`): generalizing the
    selection rule to carry a rejection predicate changed nothing about its
    old behaviour at the trivial predicate, checked rather than assumed. -/
theorem admittedCoresSide_false_eq (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (props : List (Core × Bool)) :
    admittedCoresSide MO stratum prov (fun _ _ => false) props =
      admittedCores MO stratum prov props := by
  simp [admittedCoresSide, admittedCores]

theorem axiomSelectSide_false_eq (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (props : List (Core × Bool)) :
    axiomSelectSide MO stratum prov (fun _ _ => false) props =
      axiomSelect MO stratum prov props := by
  unfold axiomSelectSide axiomSelect admittedFamSide admittedFam
  rw [admittedCoresSide_false_eq]

/-- **`hsel`, discharged generically for `axiomSelectSide` at any tick** — the
    same list-lemma chase as `axiomSelect_hsel`, through one extra `filter`
    that only removes candidates, never introduces one. -/
theorem axiomSelectSide_hsel (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (reject : ℕ → Bool → Bool) (props : List (Core × Bool)) :
    ∀ i ∈ axiomSelectSide MO stratum prov reject props,
      ∃ p ∈ props, (childCore p.1 p.2 stratum prov).id = i := by
  intro i hi
  unfold axiomSelectSide at hi
  simp only [List.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  have hc1 : c ∈ admittedCoresSide MO stratum prov reject props := List.mem_of_mem_filter hc
  unfold admittedCoresSide at hc1
  have hc2 : c ∈ (props.filter (fun p => !reject stratum p.2)).map
      (fun p => childCore p.1 p.2 stratum prov) := List.mem_of_mem_filter hc1
  simp only [List.mem_map] at hc2
  obtain ⟨p, hp, rfl⟩ := hc2
  exact ⟨p, List.mem_of_mem_filter hp, rfl⟩

/-- **Definition 16.7.** `γ_side^L(y;𝔠,k) = 0 ⟺ k = 1 ∧ y = εR` — reject the
    right child of the root, and only it, and only at the first event.
    `g = true` is `R` throughout this tree (`Word`'s own convention, restated
    in the header of Theorem 16.5's support table). -/
def gammaSideL : ℕ → Bool → Bool := fun k g => decide (k = 1) && g

/-- **Definition 16.7's mirror**, `γ_side^R`, with `εL` in place of `εR`. -/
def gammaSideR : ℕ → Bool → Bool := fun k g => decide (k = 1) && !g

/-- **"Transported by side exchange to its mirror," checked rather than
    stated**: `γ_side^R` at hand `g` is exactly `γ_side^L` at the flipped
    hand, for every event. -/
theorem gammaSideR_eq_mirror (k : ℕ) (g : Bool) : gammaSideR k g = gammaSideL k !g := by
  cases g <;> rfl

/-- **"All other entries are those of Definition 16.4."** `Q_ε^L`/`Q_ε^R`
    share `Q_ε`'s own `ExtendedQuestion` record exactly — this tree's
    occurrence-level predicates are always threaded as function arguments
    external to the record (`Cavity.lean`'s `S0tilde` already established
    this for Definition 4.8), so Definition 16.7 needing "one additional
    exact admissibility predicate" changes which selection rule a tick is
    run under, `axiomSelectSide` in place of `axiomSelect`, and changes
    nothing about the question record itself: `rfl`, not an assumption. -/
def QepsSideL : ExtendedQuestion Unit := Qeps
def QepsSideR : ExtendedQuestion Unit := Qeps

theorem QepsSideL_eq_Qeps : QepsSideL = Qeps := rfl
theorem QepsSideR_eq_Qeps : QepsSideR = Qeps := rfl

/-! ## Definition 16.7's mechanism, checked at the first event

    "At the first continuation the receiving family contains one child frame
    and not the other." The full seven-tick trace is Theorem 16.8 and is the
    next move (below); what belongs to Definition 16.7 itself is that the
    predicate actually forces this at tick 1, run rather than assumed. Ticks
    2 through 7 revert to plain `axiomSelect` — the book's own "admission at
    every event other than the first is direct-positive admission inside the
    fixed cavity" — so this is `Xeps0` advanced once under `axiomSelectSide`
    and nothing past it. -/

def selSideL1eps : List (Core × Bool) → List QuestionId :=
  axiomSelectSide MOeps 1 seed164Prov gammaSideL

theorem hselSideL0eps : ∀ i ∈ selSideL1eps props0eps, ∃ p ∈ props0eps,
    (childCore p.1 p.2 1 seed164Prov).id = i :=
  axiomSelectSide_hsel MOeps 1 seed164Prov gammaSideL props0eps

/-- The root question's tick-1 carrier under `γ_side^L`: reuses `hfresh0eps`
    unchanged, since freshness never depended on which selection rule chose
    the survivors, only on which archive they are checked against. -/
def XepsSideL1 : TickCarrier Unit hQ :=
  advanceCarrier Xeps0 hlaw0eps selSideL1eps 1 seed164Prov [] hselSideL0eps hfresh0eps

/-- **The mechanism does what Definition 16.7 claims.** Under ordinary
    `axiomSelect`, tick 1 of `𝒬_ε` ties and keeps both children
    (`theorem_16_5_root`'s first conjunct, `[[false],[true]]`). Under
    `γ_side^L`, `εR` never reaches the coherence comparison at all, and the
    support is the occurrence singleton `εL` — exactly Theorem 16.8's own
    row `S_1(𝒬_ε^L) = \{L\}`. -/
theorem xepsSideL1_active : activeWords XepsSideL1 = [[false]] := by decide

def selSideR1eps : List (Core × Bool) → List QuestionId :=
  axiomSelectSide MOeps 1 seed164Prov gammaSideR

theorem hselSideR0eps : ∀ i ∈ selSideR1eps props0eps, ∃ p ∈ props0eps,
    (childCore p.1 p.2 1 seed164Prov).id = i :=
  axiomSelectSide_hsel MOeps 1 seed164Prov gammaSideR props0eps

def XepsSideR1 : TickCarrier Unit hQ :=
  advanceCarrier Xeps0 hlaw0eps selSideR1eps 1 seed164Prov [] hselSideR0eps hfresh0eps

/-- **The side mirror**, checked independently — `εL` never reaches the
    comparison under `γ_side^R`, matching Theorem 16.8's `S_1(𝒬_ε^R) = \{R\}`. -/
theorem xepsSideR1_active : activeWords XepsSideR1 = [[true]] := by decide

#print axioms xepsSideL1_active
#print axioms xepsSideR1_active

/-! ## Theorem 16.8 — the full seven-tick trace

    Ticks 2 through 7 chained under plain `axiomSelect` from `XepsSideL1`/
    `XepsSideR1`, the same repetitive `advanceCarrier` pattern `Xeps1`–`Xeps7`
    above already runs. **Run before being asserted**: the chain was built as
    a scratch probe first (ticks 2–7, both sides) and only written up once
    the printed output matched. It closes on the mirror pair `LLLRRRR`/
    `RRRLLLL` — the singleton rows `theorem_16_5_polarized_L`/`_R` already
    reach at their own tick 6, not a new computation. The reason is exact,
    not coincidental: `XepsSideL1` and `XL0` differ only in *how* the L child
    survived tick 1 (a rejected sibling versus a one-member seed), and once
    that sibling is gone, ticks 2 onward run the identical `axiomSelect`
    schedule from an identical one-member archive, so `XepsSideL_{k}` and
    `XL_{k-1}` are the same carrier from tick 2 on. The addressed form
    (`5:16`/`16:5`) is left for the same next pass as `History.addressed`
    below — not computed here. -/

theorem hlawSideL1eps : Lawful XepsSideL1 := by decide
def propsSideL1eps : List (Core × Bool) := proposals XepsSideL1.archive XepsSideL1.active
def selSideL2eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 2 seed164Prov
theorem hselSideL1eps : ∀ i ∈ selSideL2eps propsSideL1eps, ∃ p ∈ propsSideL1eps,
    (childCore p.1 p.2 2 seed164Prov).id = i := axiomSelect_hsel MOeps 2 seed164Prov propsSideL1eps
theorem hfreshSideL1eps : ∀ p ∈ propsSideL1eps,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XepsSideL1.archive := by decide
def XepsSideL2 : TickCarrier Unit hQ :=
  advanceCarrier XepsSideL1 hlawSideL1eps selSideL2eps 2 seed164Prov []
    hselSideL1eps hfreshSideL1eps

theorem hlawSideL2eps : Lawful XepsSideL2 := by decide
def propsSideL2eps : List (Core × Bool) := proposals XepsSideL2.archive XepsSideL2.active
def selSideL3eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 3 seed164Prov
theorem hselSideL2eps : ∀ i ∈ selSideL3eps propsSideL2eps, ∃ p ∈ propsSideL2eps,
    (childCore p.1 p.2 3 seed164Prov).id = i := axiomSelect_hsel MOeps 3 seed164Prov propsSideL2eps
theorem hfreshSideL2eps : ∀ p ∈ propsSideL2eps,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XepsSideL2.archive := by decide
def XepsSideL3 : TickCarrier Unit hQ :=
  advanceCarrier XepsSideL2 hlawSideL2eps selSideL3eps 3 seed164Prov []
    hselSideL2eps hfreshSideL2eps

theorem hlawSideL3eps : Lawful XepsSideL3 := by decide
def propsSideL3eps : List (Core × Bool) := proposals XepsSideL3.archive XepsSideL3.active
def selSideL4eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 4 seed164Prov
theorem hselSideL3eps : ∀ i ∈ selSideL4eps propsSideL3eps, ∃ p ∈ propsSideL3eps,
    (childCore p.1 p.2 4 seed164Prov).id = i := axiomSelect_hsel MOeps 4 seed164Prov propsSideL3eps
theorem hfreshSideL3eps : ∀ p ∈ propsSideL3eps,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XepsSideL3.archive := by decide
def XepsSideL4 : TickCarrier Unit hQ :=
  advanceCarrier XepsSideL3 hlawSideL3eps selSideL4eps 4 seed164Prov []
    hselSideL3eps hfreshSideL3eps

theorem hlawSideL4eps : Lawful XepsSideL4 := by decide
def propsSideL4eps : List (Core × Bool) := proposals XepsSideL4.archive XepsSideL4.active
def selSideL5eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 5 seed164Prov
theorem hselSideL4eps : ∀ i ∈ selSideL5eps propsSideL4eps, ∃ p ∈ propsSideL4eps,
    (childCore p.1 p.2 5 seed164Prov).id = i := axiomSelect_hsel MOeps 5 seed164Prov propsSideL4eps
theorem hfreshSideL4eps : ∀ p ∈ propsSideL4eps,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XepsSideL4.archive := by decide
def XepsSideL5 : TickCarrier Unit hQ :=
  advanceCarrier XepsSideL4 hlawSideL4eps selSideL5eps 5 seed164Prov []
    hselSideL4eps hfreshSideL4eps

theorem hlawSideL5eps : Lawful XepsSideL5 := by decide
def propsSideL5eps : List (Core × Bool) := proposals XepsSideL5.archive XepsSideL5.active
def selSideL6eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 6 seed164Prov
theorem hselSideL5eps : ∀ i ∈ selSideL6eps propsSideL5eps, ∃ p ∈ propsSideL5eps,
    (childCore p.1 p.2 6 seed164Prov).id = i := axiomSelect_hsel MOeps 6 seed164Prov propsSideL5eps
theorem hfreshSideL5eps : ∀ p ∈ propsSideL5eps,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XepsSideL5.archive := by decide
def XepsSideL6 : TickCarrier Unit hQ :=
  advanceCarrier XepsSideL5 hlawSideL5eps selSideL6eps 6 seed164Prov []
    hselSideL5eps hfreshSideL5eps

theorem hlawSideL6eps : Lawful XepsSideL6 := by decide
def propsSideL6eps : List (Core × Bool) := proposals XepsSideL6.archive XepsSideL6.active
def selSideL7eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 7 seed164Prov
theorem hselSideL6eps : ∀ i ∈ selSideL7eps propsSideL6eps, ∃ p ∈ propsSideL6eps,
    (childCore p.1 p.2 7 seed164Prov).id = i := axiomSelect_hsel MOeps 7 seed164Prov propsSideL6eps
theorem hfreshSideL6eps : ∀ p ∈ propsSideL6eps,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XepsSideL6.archive := by decide
def XepsSideL7 : TickCarrier Unit hQ :=
  advanceCarrier XepsSideL6 hlawSideL6eps selSideL7eps 7 seed164Prov []
    hselSideL6eps hfreshSideL6eps

/-- **Theorem 16.8, side `L`, all seven ticks**, matching the book's own
    `S_j(𝒬_ε^L)` table: tick 1 is the singleton the admission predicate
    forces (`xepsSideL1_active`), and ticks 2–7 reproduce
    `theorem_16_5_polarized_L`'s own `S_1`–`S_6` exactly — checked here
    independently, not cited, since `XepsSideL_{k}` and `XL_{k-1}` are
    different Lean terms even though they compute the same value. -/
theorem theorem_16_8_L :
    activeWords XepsSideL1 = [[false]] ∧
    activeWords XepsSideL2 = [[false, false], [false, true]] ∧
    activeWords XepsSideL3 = [[false, false, false], [false, true, false]] ∧
    activeWords XepsSideL4 = [[false, false, false, true]] ∧
    activeWords XepsSideL5 =
      [[false, false, false, true, false], [false, false, false, true, true]] ∧
    activeWords XepsSideL6 =
      [[false, false, false, true, false, false], [false, false, false, true, true, true]] ∧
    activeWords XepsSideL7 = [[false, false, false, true, true, true, true]] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

def selSideR2eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 2 seed164Prov
theorem hlawSideR1eps : Lawful XepsSideR1 := by decide
def propsSideR1eps : List (Core × Bool) := proposals XepsSideR1.archive XepsSideR1.active
theorem hselSideR1eps : ∀ i ∈ selSideR2eps propsSideR1eps, ∃ p ∈ propsSideR1eps,
    (childCore p.1 p.2 2 seed164Prov).id = i := axiomSelect_hsel MOeps 2 seed164Prov propsSideR1eps
theorem hfreshSideR1eps : ∀ p ∈ propsSideR1eps,
    (childCore p.1 p.2 2 seed164Prov).id ∉ archIds XepsSideR1.archive := by decide
def XepsSideR2 : TickCarrier Unit hQ :=
  advanceCarrier XepsSideR1 hlawSideR1eps selSideR2eps 2 seed164Prov []
    hselSideR1eps hfreshSideR1eps

theorem hlawSideR2eps : Lawful XepsSideR2 := by decide
def propsSideR2eps : List (Core × Bool) := proposals XepsSideR2.archive XepsSideR2.active
def selSideR3eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 3 seed164Prov
theorem hselSideR2eps : ∀ i ∈ selSideR3eps propsSideR2eps, ∃ p ∈ propsSideR2eps,
    (childCore p.1 p.2 3 seed164Prov).id = i := axiomSelect_hsel MOeps 3 seed164Prov propsSideR2eps
theorem hfreshSideR2eps : ∀ p ∈ propsSideR2eps,
    (childCore p.1 p.2 3 seed164Prov).id ∉ archIds XepsSideR2.archive := by decide
def XepsSideR3 : TickCarrier Unit hQ :=
  advanceCarrier XepsSideR2 hlawSideR2eps selSideR3eps 3 seed164Prov []
    hselSideR2eps hfreshSideR2eps

theorem hlawSideR3eps : Lawful XepsSideR3 := by decide
def propsSideR3eps : List (Core × Bool) := proposals XepsSideR3.archive XepsSideR3.active
def selSideR4eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 4 seed164Prov
theorem hselSideR3eps : ∀ i ∈ selSideR4eps propsSideR3eps, ∃ p ∈ propsSideR3eps,
    (childCore p.1 p.2 4 seed164Prov).id = i := axiomSelect_hsel MOeps 4 seed164Prov propsSideR3eps
theorem hfreshSideR3eps : ∀ p ∈ propsSideR3eps,
    (childCore p.1 p.2 4 seed164Prov).id ∉ archIds XepsSideR3.archive := by decide
def XepsSideR4 : TickCarrier Unit hQ :=
  advanceCarrier XepsSideR3 hlawSideR3eps selSideR4eps 4 seed164Prov []
    hselSideR3eps hfreshSideR3eps

theorem hlawSideR4eps : Lawful XepsSideR4 := by decide
def propsSideR4eps : List (Core × Bool) := proposals XepsSideR4.archive XepsSideR4.active
def selSideR5eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 5 seed164Prov
theorem hselSideR4eps : ∀ i ∈ selSideR5eps propsSideR4eps, ∃ p ∈ propsSideR4eps,
    (childCore p.1 p.2 5 seed164Prov).id = i := axiomSelect_hsel MOeps 5 seed164Prov propsSideR4eps
theorem hfreshSideR4eps : ∀ p ∈ propsSideR4eps,
    (childCore p.1 p.2 5 seed164Prov).id ∉ archIds XepsSideR4.archive := by decide
def XepsSideR5 : TickCarrier Unit hQ :=
  advanceCarrier XepsSideR4 hlawSideR4eps selSideR5eps 5 seed164Prov []
    hselSideR4eps hfreshSideR4eps

theorem hlawSideR5eps : Lawful XepsSideR5 := by decide
def propsSideR5eps : List (Core × Bool) := proposals XepsSideR5.archive XepsSideR5.active
def selSideR6eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 6 seed164Prov
theorem hselSideR5eps : ∀ i ∈ selSideR6eps propsSideR5eps, ∃ p ∈ propsSideR5eps,
    (childCore p.1 p.2 6 seed164Prov).id = i := axiomSelect_hsel MOeps 6 seed164Prov propsSideR5eps
theorem hfreshSideR5eps : ∀ p ∈ propsSideR5eps,
    (childCore p.1 p.2 6 seed164Prov).id ∉ archIds XepsSideR5.archive := by decide
def XepsSideR6 : TickCarrier Unit hQ :=
  advanceCarrier XepsSideR5 hlawSideR5eps selSideR6eps 6 seed164Prov []
    hselSideR5eps hfreshSideR5eps

theorem hlawSideR6eps : Lawful XepsSideR6 := by decide
def propsSideR6eps : List (Core × Bool) := proposals XepsSideR6.archive XepsSideR6.active
def selSideR7eps : List (Core × Bool) → List QuestionId := axiomSelect MOeps 7 seed164Prov
theorem hselSideR6eps : ∀ i ∈ selSideR7eps propsSideR6eps, ∃ p ∈ propsSideR6eps,
    (childCore p.1 p.2 7 seed164Prov).id = i := axiomSelect_hsel MOeps 7 seed164Prov propsSideR6eps
theorem hfreshSideR6eps : ∀ p ∈ propsSideR6eps,
    (childCore p.1 p.2 7 seed164Prov).id ∉ archIds XepsSideR6.archive := by decide
def XepsSideR7 : TickCarrier Unit hQ :=
  advanceCarrier XepsSideR6 hlawSideR6eps selSideR7eps 7 seed164Prov []
    hselSideR6eps hfreshSideR6eps

/-- **Theorem 16.8, side `R`, all seven ticks** — the side mirror, checked
    independently rather than derived, for the same reason
    `theorem_16_5_polarized_R` is independent of `_polarized_L`: no
    side-exchange action on `TickCarrier` exists in this tree yet. -/
theorem theorem_16_8_R :
    activeWords XepsSideR1 = [[true]] ∧
    activeWords XepsSideR2 = [[true, false], [true, true]] ∧
    activeWords XepsSideR3 = [[true, false, true], [true, true, true]] ∧
    activeWords XepsSideR4 = [[true, true, true, false]] ∧
    activeWords XepsSideR5 =
      [[true, true, true, false, false], [true, true, true, false, true]] ∧
    activeWords XepsSideR6 =
      [[true, true, true, false, false, false], [true, true, true, false, true, true]] ∧
    activeWords XepsSideR7 = [[true, true, true, false, false, false, false]] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

#print axioms theorem_16_8_L
#print axioms theorem_16_8_R

/-! ## The addressed-relation corollaries Theorem 16.5 and 16.8 both owe

    `History.addressed`, already built (`Walk.lean`) and already used for the
    three seeds (`seed_addressed_eps`/`_L`/`_R`, `Accumulation.lean`), applied
    along the same seven traces `theorem_16_5_root`/`_polarized_L`/`_polarized_R`
    and `theorem_16_8_L`/`_R` already certified. No new machinery: `addressedList`
    is one `List.map` of a function the tree has had since `Two/§1`. -/

/-- One presentation per active word, in the same list order `activeWords`
    already fixes — the ordered reading Theorem 16.5's own table comment
    insists on, not a set. -/
def addressedList (ws : List Word) : List Pres :=
  ws.map (fun w => History.addressed ⟨Frame.empty, w⟩)

/-- **Theorem 16.5's root addressed-relation claim, ticks 1 through 7**:
    `S_j(𝒬_ε) = \{j{:}(j{+}1), (j{+}1){:}j\}`, exactly as the book states it,
    checked against `theorem_16_5_root`'s own seven traces rather than a
    closed-form induction — the book's own extension to tick 40 is not
    attempted here, named below. -/
theorem theorem_16_5_root_addressed :
    addressedList (activeWords Xeps1) = [(⟨1, 2, by decide⟩ : Pres), ⟨2, 1, by decide⟩] ∧
    addressedList (activeWords Xeps2) = [(⟨2, 3, by decide⟩ : Pres), ⟨3, 2, by decide⟩] ∧
    addressedList (activeWords Xeps3) = [(⟨3, 4, by decide⟩ : Pres), ⟨4, 3, by decide⟩] ∧
    addressedList (activeWords Xeps4) = [(⟨4, 5, by decide⟩ : Pres), ⟨5, 4, by decide⟩] ∧
    addressedList (activeWords Xeps5) = [(⟨5, 6, by decide⟩ : Pres), ⟨6, 5, by decide⟩] ∧
    addressedList (activeWords Xeps6) = [(⟨6, 7, by decide⟩ : Pres), ⟨7, 6, by decide⟩] ∧
    addressedList (activeWords Xeps7) =
      [(⟨7, 8, by decide⟩ : Pres), ⟨8, 7, by decide⟩] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Theorem 16.5's polarized chain for `𝒬_L`**, the seed (`XL0`, i.e.
    `seed_addressed_L`'s own `1{:}2`) through tick 7: `1{:}2 → \{1{:}3,2{:}3\}
    → \{1{:}4,3{:}5\} → 2{:}7 → \{3{:}11,3{:}10\} → \{4{:}15,4{:}13\} → 5{:}16
    → \{9{:}29,6{:}19\}`, the book's own displayed chain, term for term. -/
theorem theorem_16_5_polarized_L_addressed :
    addressedList (activeWords XL0) = [(⟨1, 2, by decide⟩ : Pres)] ∧
    addressedList (activeWords XL1) = [(⟨1, 3, by decide⟩ : Pres), ⟨2, 3, by decide⟩] ∧
    addressedList (activeWords XL2) = [(⟨1, 4, by decide⟩ : Pres), ⟨3, 5, by decide⟩] ∧
    addressedList (activeWords XL3) = [(⟨2, 7, by decide⟩ : Pres)] ∧
    addressedList (activeWords XL4) = [(⟨3, 11, by decide⟩ : Pres), ⟨3, 10, by decide⟩] ∧
    addressedList (activeWords XL5) = [(⟨4, 15, by decide⟩ : Pres), ⟨4, 13, by decide⟩] ∧
    addressedList (activeWords XL6) = [(⟨5, 16, by decide⟩ : Pres)] ∧
    addressedList (activeWords XL7) =
      [(⟨9, 29, by decide⟩ : Pres), ⟨6, 19, by decide⟩] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Theorem 16.5's polarized chain for `𝒬_R`**, checked independently of
    `_polarized_L` for the same reason `theorem_16_5_polarized_R` is: no
    side-exchange action on `TickCarrier` exists in this tree. The values are
    the book's own "and their reciprocals," at the list order this tree's
    `activeWords` actually produces — not assumed to mirror `_L`'s order,
    read off `#eval` first. -/
theorem theorem_16_5_polarized_R_addressed :
    addressedList (activeWords XR0) = [(⟨2, 1, by decide⟩ : Pres)] ∧
    addressedList (activeWords XR1) = [(⟨3, 2, by decide⟩ : Pres), ⟨3, 1, by decide⟩] ∧
    addressedList (activeWords XR2) = [(⟨5, 3, by decide⟩ : Pres), ⟨4, 1, by decide⟩] ∧
    addressedList (activeWords XR3) = [(⟨7, 2, by decide⟩ : Pres)] ∧
    addressedList (activeWords XR4) = [(⟨10, 3, by decide⟩ : Pres), ⟨11, 3, by decide⟩] ∧
    addressedList (activeWords XR5) = [(⟨13, 4, by decide⟩ : Pres), ⟨15, 4, by decide⟩] ∧
    addressedList (activeWords XR6) = [(⟨16, 5, by decide⟩ : Pres)] ∧
    addressedList (activeWords XR7) =
      [(⟨19, 6, by decide⟩ : Pres), ⟨29, 9, by decide⟩] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Theorem 16.8's own addressed-relation table, side `L`.** Ticks 2–7
    reproduce `theorem_16_5_polarized_L_addressed`'s own `XL1`–`XL6` values —
    the same fact `theorem_16_8_L` already found for `activeWords`, carried
    through `History.addressed` — checked here independently rather than
    cited, matching the file's standing practice for the two side traces. -/
theorem theorem_16_8_L_addressed :
    addressedList (activeWords XepsSideL1) = [(⟨1, 2, by decide⟩ : Pres)] ∧
    addressedList (activeWords XepsSideL2) =
      [(⟨1, 3, by decide⟩ : Pres), ⟨2, 3, by decide⟩] ∧
    addressedList (activeWords XepsSideL3) =
      [(⟨1, 4, by decide⟩ : Pres), ⟨3, 5, by decide⟩] ∧
    addressedList (activeWords XepsSideL4) = [(⟨2, 7, by decide⟩ : Pres)] ∧
    addressedList (activeWords XepsSideL5) =
      [(⟨3, 11, by decide⟩ : Pres), ⟨3, 10, by decide⟩] ∧
    addressedList (activeWords XepsSideL6) =
      [(⟨4, 15, by decide⟩ : Pres), ⟨4, 13, by decide⟩] ∧
    addressedList (activeWords XepsSideL7) = [(⟨5, 16, by decide⟩ : Pres)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Theorem 16.8's own addressed-relation table, side `R`** — the boxed
    closing pair `5{:}16 ↔ 16{:}5` is `theorem_16_5_polarized_L_addressed`'s
    tick-6 value on one side and this theorem's tick-7 value on the other,
    the two sides of the same mirror the support tables already close on. -/
theorem theorem_16_8_R_addressed :
    addressedList (activeWords XepsSideR1) = [(⟨2, 1, by decide⟩ : Pres)] ∧
    addressedList (activeWords XepsSideR2) =
      [(⟨3, 2, by decide⟩ : Pres), ⟨3, 1, by decide⟩] ∧
    addressedList (activeWords XepsSideR3) =
      [(⟨5, 3, by decide⟩ : Pres), ⟨4, 1, by decide⟩] ∧
    addressedList (activeWords XepsSideR4) = [(⟨7, 2, by decide⟩ : Pres)] ∧
    addressedList (activeWords XepsSideR5) =
      [(⟨10, 3, by decide⟩ : Pres), ⟨11, 3, by decide⟩] ∧
    addressedList (activeWords XepsSideR6) =
      [(⟨13, 4, by decide⟩ : Pres), ⟨15, 4, by decide⟩] ∧
    addressedList (activeWords XepsSideR7) = [(⟨16, 5, by decide⟩ : Pres)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

#print axioms theorem_16_5_root_addressed
#print axioms theorem_16_5_polarized_L_addressed
#print axioms theorem_16_5_polarized_R_addressed
#print axioms theorem_16_8_L_addressed
#print axioms theorem_16_8_R_addressed

/-! ## What Theorem 16.5 and 16.8 also claim, beyond this file's seven ticks

    This file's traces are typed at `hQ = 7` and stop at tick 7. What lies
    beyond them is proved elsewhere, or is not built:

    * **The extension to tick 40** is proved at every tick, not only to 40, by
      `RootChain.step4_support` (Theorem 16.11, Step 4, for every `k`): the
      support over the root chain's four proposals is `[LR^{k+1}, RL^{k+1}]`.
    * **The verification through `h = 12`** is proved at every horizon, not only
      to 12, by `Gaps.T16_5_polarized.polarized_L_support_card` and
      `polarized_R_support_card`: the polarized supports are singletons exactly
      at `h = 3` and at even `h ≥ 6`.
    * **Theorem 16.2 itself** (the general forcing argument, all rows, not just
      the terminal one) stays blocked on the missing `TickCarrier`-level
      side-exchange action — Theorem 15.5's own already-flagged gap, unrelated
      to `prop_16_6_root` above, which needed no side-exchange machinery
      because it is one fixed four-member computation, not a claim about every
      row. -/

end RootOrbit
end Two
end RatioSpace
