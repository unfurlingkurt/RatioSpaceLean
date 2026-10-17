/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.CrystallizationPattern
import RatioSpace.ElementsII.S06.State
import RatioSpace.ElementsII.S14.Conservation
import RatioSpace.ElementsII.S08.Coherence
import RatioSpace.ElementsII.S11.Advance
import RatioSpace.ElementsII.S17.Terminal
import RatioSpace.ElementsII.S23.Incidence
import RatioSpace.ElementsII.S09.Admission
import RatioSpace.ElementsII.S28.RadTransport
import RatioSpace.ElementsII.S29.RidgeDefect
import RatioSpace.ElementsII.S27.Chamber
import RatioSpace.ElementsII.S24.Lifecycle
import RatioSpace.ElementsII.S25.Shell
import RatioSpace.ElementsII.S18.Snap
import RatioSpace.ElementsII.S22.Face
import RatioSpace.ElementsII.S15.Accumulation
/-!
  Elements II §32 — Failure modes and retired formulations.

  Three items: Ledger 32.1, Separation Rule 32.2, Boundary Statement 32.3.

  **What is built.**
  * 32.1: `Excluded` (formulation, exact failure, retained replacement) keyed by
    `ExRow`, the book's twenty-one rows in order. The value is in the witnesses:
    each row with a Lean witness has a theorem `rowNN_…` whose statement is the
    exact integer or list fact that breaks the excluded substitution, almost
    always a theorem already built in §§6–29 and cited, not reproved.
    `ExRow.evidence` classifies each row, and `witnessed_of_evidence` makes the
    classification checked: every row not marked `recordOnly` produces its
    witness term.
  * 32.2: `retire` moves an entry from the live list to the retired list and
    deletes nothing. Membership is preserved, the total count is preserved, and
    the live list only loses the retired entry. Retiring all twenty-one rows
    keeps all twenty-one, in order.
  * 32.3: `NamedEquality` (domain, receiver, quotient, the two retained
    preimages, and the agreement proof), and the drift guard as exact
    witnesses: equal `ψ₁₂` on distinct words with distinct matrices, and on
    distinct occurrence records with distinct identifiers.

  **What is not built.** Rows 8, 16, 20 and 21 keep their record entry with no
  Lean witness. Row 8 is an equation between objects the checker already
  types differently (`ℕ × ℕ → ℤ × ℤ` against `Mat2 → ℤ`), so there is no
  well-typed proposition to refute; `row08_types` records the two types. Rows
  16, 20, 21 name an energy map, a plot and a field equation, none of which
  exists in the tree to be refuted. Row 2 has a witness of the replacement
  (one law, iterated, runs an eighth tick identically) rather than a
  refutation of the excluded pipeline.

  Choice discipline: `List.erase`/`List.perm_cons_erase` pull in
  `Classical.choice` (measured), so `retire` uses its own `dropOne`.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Two
namespace Retired

/-! ## Ledger 32.1 — Excluded substitutions: the witnesses -/

/-- A law that keeps at least one child for every active parent cannot shrink
    the support: `|S| ≤ |⋃ f(s)|` whenever every `f s` is nonempty. -/
theorem length_le_flatMap {α β : Type} (f : α → List β) (hf : ∀ a, f a ≠ []) :
    ∀ l : List α, l.length ≤ (l.flatMap f).length
  | [] => Nat.zero_le _
  | a :: l => by
    have h1 : 1 ≤ (f a).length := by
      cases hfa : f a with
      | nil => exact absurd hfa (hf a)
      | cons b bs => exact Nat.succ_le_succ (Nat.zero_le _)
    have h2 := length_le_flatMap f hf l
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    omega

/-- **Row 1**, *retain at least one child per active parent*. On `𝒬_L` at
    declared horizon 8 the support is a pair at tick 7 and a singleton at tick 8
    (Proposition 16.9(iv)). No child-per-parent rule produces tick 8 from tick 7. -/
theorem row01_support_contracts :
    (RootOrbit.activeWords Beat.YL7).length = 2 ∧ (RootOrbit.activeWords Beat.YL8).length = 1 ∧
    ¬ ∃ f : Word → List Word, (∀ w, f w ≠ []) ∧
        RootOrbit.activeWords Beat.YL8 = (RootOrbit.activeWords Beat.YL7).flatMap f := by
  obtain ⟨-, h7, h8, -, -, -⟩ := Beat.prop_16_9_iv_horizon_eight
  refine ⟨h7, h8, ?_⟩
  rintro ⟨f, hf, heq⟩
  have h := length_le_flatMap f hf (RootOrbit.activeWords Beat.YL7)
  rw [← heq, h7, h8] at h
  omega

/-- **Row 2**, *seven named workflow filters* (replacement witness). The same
    kernel at declared horizon 8 reproduces the seven-tick words exactly and
    then runs an eighth tick: one law iterated, with no label per tick. -/
theorem row02_one_law_iterated :
    RootOrbit.activeWords Beat.YL7 = RootOrbit.activeWords RootOrbit.XL7 ∧
    (RootOrbit.activeWords Beat.YL8).length = 1 :=
  ⟨Beat.horizon_inert.2.2.2.2.2.2.1, Beat.prop_16_9_iv_horizon_eight.2.2.1⟩

/-- **Row 3**, *projected-value singleton equals occurrence singleton*. Two
    distinct occurrence identifiers reach one address (Proposition 6.9). -/
theorem row03_projected_singleton :
    occA.id ≠ occB.id ∧ occA.addr = occB.addr :=
  occurrence_singleton_not_forced_by_addr

/-- **Row 4**, *stable-sort or list-order tie repair*. For any two distinct
    presentations the head of the list depends on storage order while the
    support does not, and the pair is its own support: the order is an
    undeclared choice and the tie is an unresolved multiple. -/
theorem row04_order_is_not_a_tiebreak (x y : IPres) (hxy : x ≠ y) :
    [x, y].head? ≠ [y, x].head? ∧
    (∀ z, z ∈ support [x, y] ↔ z ∈ support [y, x]) ∧
    support [x, y] = [x, y] ∧
    Terminal.termStatus (support [x, y]).length = .unresolvedMultiple := by
  refine ⟨fun h => hxy (Option.some.inj h),
    fun z => Advance.support_enumeration_independent (List.Perm.swap y x []) z,
    pair_support x y, ?_⟩
  rw [pair_support]; rfl

/-- **Row 5**, *endpoint-only candidate record*. Keyed by identifier the two
    witnesses stay two; keyed by the endpoint address they collapse to one
    (Corollary 6.10). -/
theorem row05_endpoint_record_deletes_multiplicity :
    ([occA, occB].map Core.id).dedup.length = 2 ∧
    ([occA, occB].map Core.addr).dedup.length = 1 :=
  no_dedup_by_received_value

/-- A candidate whose terminal report is empty: its sibling reception entry is
    one, its snap entry is zero. -/
def row06Input : Face.EligInput :=
  ⟨[], [], .empty, Shell.iWit, Shell.iWit, 0, Shell.iWit, true, Shell.iWit, Shell.iWit⟩

/-- **Row 6**, *generated sibling equals received edge equals attached face*.
    First identification: a raw ancestry edge is never the same edge as a
    received one, whatever its endpoints (§23). Second identification: on
    `row06Input` the sibling reception entry is one while the eligibility
    vector is not all ones, so there is no committed face certificate
    (Theorem 22.6), and Construction Axiom II.2 attaches no packet built on it,
    from any candidate list that contains it. -/
theorem row06_three_operations :
    (type_of% @Incidence.raw_not_received) ∧
    (row06Input.vector.recv = true ∧ row06Input.vector.all = false ∧
      ¬ Face.FaceCert row06Input ∧
      ∀ {Aux Cert RawAux EvalAux : Type} {h : ℕ} (ps : List (Face.FElig Aux Cert RawAux EvalAux h))
        (p : Face.FElig Aux Cert RawAux EvalAux h),
        p ∈ ps → p.input = row06Input → Face.attach p ∉ Face.receivedFaces ps) := by
  have hall : row06Input.vector.all = false := by decide
  refine ⟨Incidence.raw_not_received, by decide, hall, fun hc => ?_, ?_⟩
  · rw [(Face.face_selection _).mp hc] at hall; exact Bool.noConfusion hall
  · intro Aux Cert RawAux EvalAux h ps p hps hp hm
    have ha := (Face.attached_iff ps p hps).mp hm
    rw [p.elig_eq, hp, hall] at ha
    exact Bool.noConfusion ha

/-- **Row 7**, *positive admission equals Rademacher reception*. The projective
    class, which is all the positive admission reads, identifies `L` and `−L`;
    the lift bit of the signed matrix separates them (Theorem 9.14). -/
theorem row07_projective_is_not_signed : type_of% @lift_separates_what_projective_cannot :=
  lift_separates_what_projective_cannot

/-- **Row 8**, *`Φ_ch = Φ_Rad = φ_t^(E)`* (record only). The checker already
    refuses the equation: the chamber coordinate and the transport cocycle have
    different types, and no `φ_t^(E)` exists. This records the two types. -/
def row08_types : (ℕ × ℕ → ℤ × ℤ) × (Mat2 → ℤ) := (Chamber.phiCh, RadTransport.phiRadC)

/-- **Row 9**, *`κ_cl = σ_Rad`*. On the same continuation word, neither is a
    function of the other: `ψ₁₂` agrees on `ε` and `R¹²` while the route sign is
    `1` against `−1`; the route sign agrees on `vPlus 0` and `vPlus 1` while
    `ψ₁₂` is `11` against `0`. -/
theorem row09_closure_is_not_route_sign :
    (Word.psi12 ([] : Word) = Word.psi12 (List.replicate 12 true) ∧
      routeCorrection (RadTransport.Qs true []) ≠
        routeCorrection (RadTransport.Qs true (List.replicate 12 true))) ∧
    (routeCorrection (RadTransport.Qs true (RadTransport.vPlus 0)) =
        routeCorrection (RadTransport.Qs true (RadTransport.vPlus 1)) ∧
      Word.psi12 (RadTransport.vPlus 0) ≠ Word.psi12 (RadTransport.vPlus 1)) := by
  decide

/-- **Row 10**, *`j_s = [Φ_Rad]₂₄`*. The quarter-turn admission phase of an
    `R`-emission is `3` whatever follows, while the transport residue reads
    `1`, `0`, `13` (Separation 28.11). -/
theorem row10_admission_is_not_transport : type_of% @RadTransport.sep_phases :=
  RadTransport.sep_phases

/-- **Row 11**, *`h_𝒬 = 7` equals the three-position elliptic scan*. The horizon
    is seven ticks; the scan has three positions whose exact lift orders are
    `6, 4, 3`, and seven is none of them. The scan is indexed by causal
    retention position `m = 1 + |v|` (Proposition 28.10): the elliptic
    positions are `m = 1, 2, 3` (`v = ε, R, R²`), and at retention position
    `m = h_𝒬 = 7` (`v = R⁶`) the ray matrix has trace `−5`, is hyperbolic,
    and has no finite lift order. -/
theorem row11_horizon_is_not_scan :
    Accumulation.hQ = 7 ∧ (type_of% @RadTransport.ray_elliptic_orders) ∧
    ([6, 4, 3] : List ℕ).length = 3 ∧ 7 ∉ ([6, 4, 3] : List ℕ) ∧
    (1 + (List.replicate (Accumulation.hQ - 1) true).length = Accumulation.hQ ∧
      RadTransport.trace (RadTransport.Qs true (List.replicate (Accumulation.hQ - 1) true)) = -5 ∧
      ∀ k, matPow (RadTransport.Qs true (List.replicate (Accumulation.hQ - 1) true)) (k + 1) ≠ 1) :=
  ⟨rfl, RadTransport.ray_elliptic_orders, rfl, by decide,
    ⟨by decide, by decide, (RadTransport.ray_hyperbolic 7 (by decide)).2.1⟩⟩

/-- **Row 12**, *finite route census proves old-past path independence*. Opposite
    routes reach arbitrarily far in either winding (Theorem 28.7), and at `m = 3`
    they return the transport value without returning the class or the matrix. -/
theorem row12_route_dependence :
    (type_of% @RadTransport.opposite_routes_unbounded) ∧
    (type_of% @RadTransport.transport_return_not_class_return) :=
  ⟨RadTransport.opposite_routes_unbounded, RadTransport.transport_return_not_class_return⟩

/-- **Row 13**, *the tuple with `tr Q` is period two on the alternating route*.
    The even-strobe trace is `F_{2r+1}`: `1` at `r = 0`, `2` at `r = 1`, and the
    strobe matrices never repeat (Proposition 29.6). -/
theorem row13_trace_not_period_two :
    RadTransport.trace (RidgeDefect.QR (RidgeDefect.rlWord 0)) = 1 ∧
    RadTransport.trace (RidgeDefect.QR (RidgeDefect.rlWord 1)) = 2 ∧
    ∀ m n : ℕ, m ≠ n → RidgeDefect.QR (RidgeDefect.rlWord m) ≠ RidgeDefect.QR (RidgeDefect.rlWord n) :=
  ⟨by decide, by decide, RidgeDefect.strobe_distinct⟩

/-- **Row 14**, *received phase recurrence equals exact history recurrence*.
    `ψ₁₂` returns at `R¹²`; the word and the relative matrix do not; and under
    repeated renewal every exact word and matrix is new (Theorem 24.7). -/
theorem row14_phase_return_is_not_history_return :
    Word.psi12 ([] : Word) = Word.psi12 (List.replicate 12 true) ∧
    ([] : Word) ≠ List.replicate 12 true ∧
    RadTransport.Qs true [] ≠ RadTransport.Qs true (List.replicate 12 true) ∧
    (type_of% @Lifecycle.renewal_no_recurrence) :=
  ⟨by decide, by decide, RadTransport.received_equality_not_matrix_return true (by decide),
    Lifecycle.renewal_no_recurrence⟩

/-- `x² − 3x + 1` has no integer root. -/
theorem no_int_root_three (x : ℤ) : x * x - 3 * x + 1 ≠ 0 := by
  rcases Int.lt_or_le x 1 with h | h
  · have h1 : 0 ≤ (-x) * (-x) := Int.mul_nonneg (by omega) (by omega)
    have e : (-x) * (-x) = x * x := by ring
    omega
  · rcases Int.lt_or_le x 3 with h' | h'
    · rcases (by omega : x = 1 ∨ x = 2) with rfl | rfl <;> decide
    · have h1 : x * 3 ≤ x * x := Int.mul_le_mul_of_nonneg_left h' (by omega)
      omega

/-- **Row 15**, *trace is already impedance or mass*. `R·L` has trace `3`; its
    expanding multiplier is a root of `x² − 3x + 1`, which has no integer root,
    so the trace is not the multiplier, let alone a calibrated mass. The general
    statement for every `t ≥ 3`, rational roots included, is Proposition 30.2
    (`ElementsII/S30/Obligations.lean`). -/
theorem row15_trace_is_not_the_multiplier :
    RadTransport.trace (Mat2.R * Mat2.L) = 3 ∧ (Mat2.R * Mat2.L).det = 1 ∧
    ∀ x : ℤ, x * x - 3 * x + 1 ≠ 0 :=
  ⟨by decide, by decide, no_int_root_three⟩

/-- **Row 17**, *`𝖯`, reversal, inverse traversal and `−I` are one mirror*.
    Separation Rule 27.5's exact witnesses. -/
theorem row17_four_operations : type_of% @Chamber.four_operations :=
  Chamber.four_operations

/-- **Row 18**, *equal `ψ₁₂` values create an attaching edge*. Equality of a
    character is reflexive, so the rule would put a loop at every occurrence;
    no face edge is a loop (§23). And equal `ψ₁₂` already holds between two
    distinct occurrence records from one seed (Theorem 18.2). -/
theorem row18_equal_character_is_not_incidence :
    (¬ ∀ (i i' : QuestionId) (j : ℕ), j < i.rel.length →
        Word.psi12 i.rel = Word.psi12 i'.rel →
        ∃ e ∈ Incidence.lineFaceE i j, e.a = i ∧ e.b = i') ∧
    (type_of% @Snap.closure_class_is_not_the_record) := by
  refine ⟨fun h => ?_, Snap.closure_class_is_not_the_record⟩
  obtain ⟨e, he, ha, hb⟩ := h Shell.iWit Shell.iWit 0 (by decide) rfl
  exact Incidence.edge_endpoints_ne Shell.iWit 0 (by decide) e he (ha.trans hb.symm)

/-- **Row 19**, *local projective face closure proves a shell*. Three lineage
    faces: every face closes projectively (Proposition 22.2), every received
    edge has incidence one, `c_2E` and `c_link` fail (Theorem 25.8). -/
theorem row19_local_closure_is_not_a_shell :
    (type_of% @Shell.lineage_witness) ∧ (type_of% @Face.boundary_projectively_closed) :=
  ⟨Shell.lineage_witness, Face.boundary_projectively_closed⟩

/-! ## Ledger 32.1 — the record -/

/-- The twenty-one rows of Ledger 32.1, in the book's order. -/
inductive ExRow where
  | r01 | r02 | r03 | r04 | r05 | r06 | r07
  | r08 | r09 | r10 | r11 | r12 | r13 | r14
  | r15 | r16 | r17 | r18 | r19 | r20 | r21
  deriving DecidableEq, Repr

/-- **Ledger 32.1.** One excluded substitution: the formulation, its exact
    failure, and the retained replacement. -/
structure Excluded where
  row : ExRow
  formulation : String
  failure : String
  replacement : String
  deriving DecidableEq, Repr

/-- **Ledger 32.1, the table.** -/
def ledger : List Excluded :=
  [ ⟨.r01, "retain at least one child per active parent",
      "|S_{j+1}| >= |S_j|, so multiple support cannot contract to a singleton",
      "global occurrence-counted comparison (Definition 8.1)"⟩
  , ⟨.r02, "seven named workflow filters",
      "executes seven different labels once rather than one temporal law seven times",
      "K_C^7"⟩
  , ⟨.r03, "projected-value singleton equals occurrence singleton",
      "distinct histories may share one projected relation",
      "resolution is occurrence-keyed; relation resolution requires an injective fiber"⟩
  , ⟨.r04, "stable-sort or list-order tie repair",
      "inserts an undeclared asymmetric choice",
      "exact unresolved-multiple terminal status"⟩
  , ⟨.r05, "endpoint-only candidate record",
      "deletes path, parent, refusal, and causal multiplicity",
      "immutable occurrence core plus append-only archive and event ledger"⟩
  , ⟨.r06, "generated sibling equals received edge equals attached face",
      "collapses three distinct operations",
      "generation, reception, and Construction Axiom II.2 remain separate"⟩
  , ⟨.r07, "positive admission equals Rademacher reception",
      "one decodes a positive presentation; the other reads a signed relative matrix",
      "separate admission and transport receivers"⟩
  , ⟨.r08, "Phi_ch = Phi_Rad = phi_t^(E)",
      "conflates a projected chamber coordinate, integer cocycle, and encoded field",
      "qualified notation and explicit bridge maps"⟩
  , ⟨.r09, "kappa_cl = sigma_Rad",
      "conflates a declared closure record with a sign of c tr Q",
      "independently retained coordinates"⟩
  , ⟨.r10, "j_s = [Phi_Rad]_24",
      "conflates quarter-turn admission with transport residue",
      "separate phase types and an open crosswalk obligation"⟩
  , ⟨.r11, "h_Q = 7 equals the three-position elliptic scan",
      "conflates construction ticks with causal retention depth",
      "separately named horizons and indices"⟩
  , ⟨.r12, "finite route census proves old-past path independence",
      "extrapolates a bounded enumeration into a universal theorem",
      "explicit arbitrary-depth opposite-route families in Theorem 28.7"⟩
  , ⟨.r13, "(Phi_Rad, tr Q, sigma_Rad, Psi_Rad) is period two on the alternating route",
      "the even trace is F_{2r+1} and changes with r",
      "the periodic receiver is (Phi_Rad, sigma_Rad, Psi_Rad); trace remains exact growing data"⟩
  , ⟨.r14, "received phase recurrence equals exact history recurrence",
      "contradicts positive freeness and the changing matrices",
      "renewal is equality only under a declared receiver"⟩
  , ⟨.r15, "trace is already impedance or mass",
      "omits the expanding multiplier, representation, dimensions, and calibration",
      "exact trace first; multiplier and physical map downstream"⟩
  , ⟨.r16, "D_R^2 or D_L^2 is energy",
      "reinterprets an arithmetic invariant without an energy map",
      "quadratic ridge defect only"⟩
  , ⟨.r17, "P, reversal, inverse traversal, and -I are one mirror",
      "collapses operations with different determinants and action types",
      "four separately typed operations"⟩
  , ⟨.r18, "equal psi_12 values create an attaching edge",
      "equality of a finite character does not provide incidence",
      "explicit sibling reception, eligibility, attachment, and source retention"⟩
  , ⟨.r19, "local projective face closure proves a shell",
      "boundary product does not supply two-face edge incidence or cyclic links",
      "Section 25 shell certificate"⟩
  , ⟨.r20, "a plotted ring or denominator threshold proves continuum onset",
      "a visualization or affine scale is not a substrate theorem",
      "explicit exact-to-field correspondence"⟩
  , ⟨.r21, "a field equation chooses substrate survivors",
      "reverses the declared layer order",
      "exact substrate update first, projection second"⟩ ]

def allRows : List ExRow :=
  [.r01, .r02, .r03, .r04, .r05, .r06, .r07, .r08, .r09, .r10, .r11,
   .r12, .r13, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21]

/-- Twenty-one rows, keyed in order, and every row names a replacement. -/
theorem ledger_shape :
    ledger.length = 21 ∧ ledger.map (·.row) = allRows ∧ allRows.Nodup ∧
    ∀ e ∈ ledger, e.replacement ≠ "" := by
  decide

/-- What the tree holds against each row. -/
inductive Evidence where
  /-- An exact witness breaks the excluded identification. -/
  | refuted
  /-- An exact witness breaks one of the identifications the row names. -/
  | partialWitness
  /-- An exact witness of the retained replacement, not a refutation. -/
  | replacement
  /-- The record entry stands; nothing in the tree to refute. -/
  | recordOnly
  deriving DecidableEq, Repr

def ExRow.evidence : ExRow → Evidence
  | .r01 => .refuted | .r02 => .replacement | .r03 => .refuted | .r04 => .refuted
  | .r05 => .refuted | .r06 => .refuted | .r07 => .refuted | .r08 => .recordOnly
  | .r09 => .refuted | .r10 => .refuted | .r11 => .refuted | .r12 => .refuted
  | .r13 => .refuted | .r14 => .refuted | .r15 => .refuted | .r16 => .recordOnly
  | .r17 => .refuted | .r18 => .refuted | .r19 => .refuted | .r20 => .recordOnly
  | .r21 => .recordOnly

/-- A row is witnessed when its witness theorem is supplied. The constructor
    argument types are the witness statements themselves. -/
inductive Witnessed : ExRow → Prop where
  | r01 : type_of% @row01_support_contracts → Witnessed .r01
  | r02 : type_of% @row02_one_law_iterated → Witnessed .r02
  | r03 : type_of% @row03_projected_singleton → Witnessed .r03
  | r04 : type_of% @row04_order_is_not_a_tiebreak → Witnessed .r04
  | r05 : type_of% @row05_endpoint_record_deletes_multiplicity → Witnessed .r05
  | r06 : type_of% @row06_three_operations → Witnessed .r06
  | r07 : type_of% @row07_projective_is_not_signed → Witnessed .r07
  | r09 : type_of% @row09_closure_is_not_route_sign → Witnessed .r09
  | r10 : type_of% @row10_admission_is_not_transport → Witnessed .r10
  | r11 : type_of% @row11_horizon_is_not_scan → Witnessed .r11
  | r12 : type_of% @row12_route_dependence → Witnessed .r12
  | r13 : type_of% @row13_trace_not_period_two → Witnessed .r13
  | r14 : type_of% @row14_phase_return_is_not_history_return → Witnessed .r14
  | r15 : type_of% @row15_trace_is_not_the_multiplier → Witnessed .r15
  | r17 : type_of% @row17_four_operations → Witnessed .r17
  | r18 : type_of% @row18_equal_character_is_not_incidence → Witnessed .r18
  | r19 : type_of% @row19_local_closure_is_not_a_shell → Witnessed .r19

/-- **Ledger 32.1, checked.** Every row not marked `recordOnly` is witnessed. -/
theorem witnessed_of_evidence : ∀ r : ExRow, r.evidence ≠ .recordOnly → Witnessed r
  | .r01, _ => .r01 row01_support_contracts
  | .r02, _ => .r02 row02_one_law_iterated
  | .r03, _ => .r03 row03_projected_singleton
  | .r04, _ => .r04 row04_order_is_not_a_tiebreak
  | .r05, _ => .r05 row05_endpoint_record_deletes_multiplicity
  | .r06, _ => .r06 row06_three_operations
  | .r07, _ => .r07 row07_projective_is_not_signed
  | .r08, h => absurd rfl h
  | .r09, _ => .r09 row09_closure_is_not_route_sign
  | .r10, _ => .r10 row10_admission_is_not_transport
  | .r11, _ => .r11 row11_horizon_is_not_scan
  | .r12, _ => .r12 row12_route_dependence
  | .r13, _ => .r13 row13_trace_not_period_two
  | .r14, _ => .r14 row14_phase_return_is_not_history_return
  | .r15, _ => .r15 row15_trace_is_not_the_multiplier
  | .r16, h => absurd rfl h
  | .r17, _ => .r17 row17_four_operations
  | .r18, _ => .r18 row18_equal_character_is_not_incidence
  | .r19, _ => .r19 row19_local_closure_is_not_a_shell
  | .r20, h => absurd rfl h
  | .r21, h => absurd rfl h

/-- The count: sixteen refuted, no partial, one replacement witness, four
    record-only. -/
theorem evidence_counts :
    (allRows.filter (fun r => r.evidence == .refuted)).length = 16 ∧
    (allRows.filter (fun r => r.evidence == .partialWitness)).length = 0 ∧
    (allRows.filter (fun r => r.evidence == .replacement)).length = 1 ∧
    allRows.filter (fun r => r.evidence == .recordOnly) = [.r08, .r16, .r20, .r21] := by
  decide

/-! ## Separation Rule 32.2 — Corrections preserve provenance -/

section Retire
variable {α : Type} [DecidableEq α]

/-- Remove the first occurrence of `x`, and nothing else. -/
def dropOne (x : α) : List α → List α
  | [] => []
  | a :: l => if a = x then l else a :: dropOne x l

theorem mem_dropOne_of_ne (x y : α) (hy : y ≠ x) : ∀ l : List α, y ∈ l → y ∈ dropOne x l
  | [], h => nomatch h
  | a :: l, h => by
    change y ∈ (if a = x then l else a :: dropOne x l)
    by_cases ha : a = x
    · rw [if_pos ha]
      rcases List.mem_cons.mp h with e | e
      · exact absurd (e.trans ha) hy
      · exact e
    · rw [if_neg ha]
      rcases List.mem_cons.mp h with e | e
      · rw [e]; exact List.Mem.head _
      · exact List.Mem.tail _ (mem_dropOne_of_ne x y hy l e)

theorem mem_of_mem_dropOne (x y : α) : ∀ l : List α, y ∈ dropOne x l → y ∈ l
  | [], h => nomatch h
  | a :: l, h => by
    change y ∈ (if a = x then l else a :: dropOne x l) at h
    by_cases ha : a = x
    · rw [if_pos ha] at h; exact List.Mem.tail _ h
    · rw [if_neg ha] at h
      rcases List.mem_cons.mp h with e | e
      · rw [e]; exact List.Mem.head _
      · exact List.Mem.tail _ (mem_of_mem_dropOne x y l e)

theorem length_dropOne (x : α) : ∀ l : List α, x ∈ l → (dropOne x l).length + 1 = l.length
  | [], h => nomatch h
  | a :: l, h => by
    change (if a = x then l else a :: dropOne x l).length + 1 = l.length + 1
    by_cases ha : a = x
    · rw [if_pos ha]
    · rw [if_neg ha]
      have hl : x ∈ l := by
        rcases List.mem_cons.mp h with e | e
        · exact absurd e.symm ha
        · exact e
      change (dropOne x l).length + 1 + 1 = l.length + 1
      rw [length_dropOne x l hl]

/-- A standing ledger: live formulations and retired ones. -/
structure Standing (α : Type) where
  live : List α
  retired : List α

/-- **Separation Rule 32.2.** Retiring `x` removes it from the live list and
    appends it to the retired list. -/
def retire (b : Standing α) (x : α) : Standing α := ⟨dropOne x b.live, b.retired ++ [x]⟩

/-- **Separation Rule 32.2.** Retiring deletes no record: everything that was
    live or retired is still live or retired, the retired entry is on the
    retired list, the live list only lost entries it had, and when `x` was live
    the total count is unchanged. -/
theorem retire_preserves (b : Standing α) (x : α) :
    (∀ y, y ∈ b.live ∨ y ∈ b.retired → y ∈ (retire b x).live ∨ y ∈ (retire b x).retired) ∧
    x ∈ (retire b x).retired ∧
    (∀ y ∈ (retire b x).live, y ∈ b.live) ∧
    (x ∈ b.live → (retire b x).live.length + (retire b x).retired.length =
      b.live.length + b.retired.length) := by
  refine ⟨fun y hy => ?_, List.mem_append.mpr (Or.inr (List.Mem.head [])),
    fun y hy => mem_of_mem_dropOne x y b.live hy, fun hx => ?_⟩
  · by_cases hyx : y = x
    · rw [hyx]; exact Or.inr (List.mem_append.mpr (Or.inr (List.Mem.head [])))
    · rcases hy with h | h
      · exact Or.inl (mem_dropOne_of_ne x y hyx b.live h)
      · exact Or.inr (List.mem_append.mpr (Or.inl h))
  · change (dropOne x b.live).length + (b.retired ++ [x]).length = b.live.length + b.retired.length
    rw [List.length_append]
    have := length_dropOne x b.live hx
    change (dropOne x b.live).length + (b.retired.length + 1) = _
    omega

def retireAll (b : Standing α) : List α → Standing α
  | [] => b
  | x :: xs => retireAll (retire b x) xs

theorem retireAll_preserves : ∀ (xs : List α) (b : Standing α) (y : α),
    y ∈ b.live ∨ y ∈ b.retired → y ∈ (retireAll b xs).live ∨ y ∈ (retireAll b xs).retired
  | [], _, _, h => h
  | x :: xs, b, y, h => retireAll_preserves xs (retire b x) y ((retire_preserves b x).1 y h)

end Retire

/-- **Separation Rule 32.2, on Ledger 32.1.** Retiring all twenty-one
    formulations leaves none live and keeps all twenty-one, in order, on the
    retired list. -/
theorem ledger_retired_whole :
    (retireAll ⟨ledger, []⟩ ledger).live = [] ∧ (retireAll ⟨ledger, []⟩ ledger).retired = ledger := by
  decide

/-! ## Boundary Statement 32.3 -/

/-- **Boundary Statement 32.3.** An equality that names what it is: the domain
    `D`, the receiver, the quotient `Q` it lands in, and the two retained
    preimages it compares. -/
structure NamedEquality (D Q : Type) where
  receiver : D → Q
  left : D
  right : D
  agree : receiver left = receiver right

/-- **Boundary Statement 32.3.** Same value under one map does not give the same
    exact record. On words: `ψ₁₂` agrees on two distinct words whose matrices
    differ. On records: `ψ₁₂` of the full word agrees on two occurrence records
    from one seed whose identifiers differ (Theorem 18.2). So no named equality
    under a receiver licenses equality of its preimages. -/
theorem boundary_32_3 :
    (∃ e : NamedEquality Word (ZMod 12),
      e.receiver = Word.psi12 ∧ e.left ≠ e.right ∧ Word.G e.left ≠ Word.G e.right) ∧
    (∀ (id0 : QuestionId) (seed : History), ∃ e : NamedEquality ProposalRecord (ZMod 12),
      e.left = proposal id0 seed [true, false] ∧ e.right = proposal id0 seed [false, true] ∧
      e.left.id ≠ e.right.id) ∧
    ¬ (∀ e : NamedEquality Word (ZMod 12), e.left = e.right) := by
  obtain ⟨u, v, huv, -, hpsi, hG⟩ := Conservation.character_collapses
  refine ⟨⟨⟨Word.psi12, u, v, hpsi⟩, rfl, huv, hG⟩, fun id0 seed => ?_,
    fun h => huv (h ⟨Word.psi12, u, v, hpsi⟩)⟩
  exact ⟨⟨fun r => Word.psi12 r.fullWord, proposal id0 seed [true, false],
    proposal id0 seed [false, true], (Snap.closure_class_is_not_the_record id0 seed).1⟩,
    rfl, rfl, (Snap.closure_class_is_not_the_record id0 seed).2⟩

end Retired
end Two
end RatioSpace
