/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S20.Cycle
import RatioSpace.ElementsII.S17.Terminal
import RatioSpace.ElementsII.S18.Snap
import RatioSpace.ElementsII.S22.Face
import RatioSpace.ElementsII.S24.Lifecycle
import RatioSpace.ElementsII.S25.Shell
import RatioSpace.ElementsII.S26.Mirror
import RatioSpace.ElementsII.S27.Chamber
import RatioSpace.ElementsII.S29.RidgeDefect
import RatioSpace.ElementsII.S28.RadTransport
import RatioSpace.ElementsII.S15.Accumulation
import RatioSpace.ElementsII.S11.Advance
/-!
  Elements II §30 — Projection obligations opened by the recurrence.

  Five items: Definition 30.1, Proposition 30.2, Theorem 30.3, Separation Rule
  30.4, Boundary Statement 30.5.

  **What is built.**
  * 30.1: `ProjOb` as a typed record over four finite inductive columns (exact
    source data, requested target, missing construction, downstream owner) and
    the book's nine rows. The record has no field of function type, and the
    checker certifies it: `ProjOb` derives `DecidableEq`, which no record
    carrying a map `ℤ → ℤ` could. Listing an obligation declares no map.
  * 30.2: Cayley–Hamilton on `SL(2,ℤ)` entrywise, so the expanding multiplier is
    the root of `x² − t x + 1`. For every integer `t ≥ 3` the discriminant
    `t² − 4` is not a square (`(t−1)² < t² − 4 < t²`), and `x² − t x + 1` has no
    root `p/q` at all, stated without division as
    `p² − t p q + q² ≠ 0` for `q ≠ 0` (Vieta descent). So the multiplier is not an
    integer and not a rational, and there is no integer value of it to read as
    a mass. The file carries no calibration constant and declares none.
  * 30.3: `EngineClauses`, a record whose fields are *literally the statements*
    (`type_of%`) of the already-built theorems for clauses 1–8. None of those
    files imports this one, so none can mention `ProjOb`.
    The converse clause is an exact witness: two integer charts on the relative
    matrix, both invariant under the side exchange and both strictly increasing
    along the `(RL)^r` strobe, disagree on `R·L`. The recurrence data do not fix
    the calibration.
  * 30.4: `Correspondence` (encoding `E`, domain, closure of the domain, and a
    commutation proof). Two witnesses that resemblance does not supply one:
    `RL` and `LR` share trace and determinant, the identity identification does
    not commute, and the explicit exchange `P` does; `𝖠_R` (Fibonacci growth) and
    the order-six return `Q_R(ε)` share trace `1`, and *no* invertible integer
    linear encoding intertwines them. The rule as the book states it is
    `CorrespondenceRule`: at a stated tolerance (`exact`, or an error budget in
    `ℕ` fixed in the claim's type), an encoding, any declared domain (no
    closure), and a commutation or controlled-error theorem
    (`CorrespondenceTheorem`), with retained and discarded distinctions read
    off `E`.
  * 30.5: the division as a sum type with lossless projections to each side,
    instantiated on the four recurrence results and the nine obligations.

  **What is not built.** No obligation is discharged here: no crosswalk, no
  geodesic reading, no encoding, no mass chart. That is the section's content.

  Choice discipline: `nlinarith`, `linear_combination` and Mathlib's list
  `erase`/`perm` lemmas pull in `Classical.choice` (measured), so the arithmetic
  below uses core `Int` order lemmas, `ring` and `omega` only.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Two
namespace Obligations

/-! ## Definition 30.1 — Downstream obligation record -/

/-- The exact source data column of Definition 30.1. Each constructor names
    data already built in §§11–29. -/
inductive ExactDatum where
  | phiRad24 | psiRad | psi12
  | balancedPeriodicWords | sigmaRad
  | archiveAge | winding | lift | trace | renewal | ridgeDefect
  | chamberPair | parityExchange
  | hyperbolicRelMatrix
  | retainedAlternatives | jointTrails | renewalClass
  | activeFaceExports | shellCertificates
  | completedProjection
  deriving DecidableEq, Repr

/-- The requested target column of Definition 30.1. -/
inductive Target where
  | phaseClosureCrosswalk
  | classRenewingPeriods
  | geodesicCrossingReading
  | numericalContinuumState
  | chamberPotential
  | impedanceMassChart
  | exchangeExclusionSectors
  | persistentGlobalShells
  | empiricalIdentification
  deriving DecidableEq, Repr

/-- The missing construction or proof column of Definition 30.1. -/
inductive Missing where
  | map | kernel | liftDependence | factorOfTwo
  | correctionSignClassification
  | orientedGeodesics | equivalenceProof
  | encodingE | commutationTheorem
  | representation | domain | noSubstrateFeedback
  | expandingMultiplier | dimensionfulCalibratedMap
  | jointContinuationLaw | exchangeLaw
  | multiCycleFamilies | downstreamHypotheses
  | observables | calibration | forbiddenChannels | comparisonProtocol
  deriving DecidableEq, Repr

/-- The downstream owner column of Definition 30.1. -/
inductive Owner where
  | rademacherCompanion
  | recurrenceProgram
  | modularGeometricCompanion
  | substrateToField
  | massImpedanceProjection
  | fermionBosonProgram
  | globalRenewalShell
  | applicationPapers
  deriving DecidableEq, Repr

/-- **Definition 30.1.** `ProjOb = (exact source data, requested target type,
    missing map or theorem, downstream owner)`.

    Every field is finite data. There is no field of function type, so a
    `ProjOb` cannot carry the map it asks for: listing an obligation does not
    declare its map, assume its existence, or supply its interpretation. -/
structure ProjOb where
  source : List ExactDatum
  target : Target
  missing : List Missing
  owner : Owner
  deriving DecidableEq, Repr

/-- **Definition 30.1, the no-map certificate.** `ProjOb` has decidable equality,
    derived field by field. A record with a field of type `ℤ → ℤ` has no such
    derivation, so this instance is the checker's statement that the record
    holds no map. -/
def projOb_decidableEq : DecidableEq ProjOb := inferInstance

/-- **Definition 30.1, the table.** The nine obligations opened by the final
    recurrence block, in the book's order. -/
def obligations : List ProjOb :=
  [ ⟨[.phiRad24, .psiRad, .psi12], .phaseClosureCrosswalk,
      [.map, .kernel, .liftDependence, .factorOfTwo], .rademacherCompanion⟩
  , ⟨[.balancedPeriodicWords, .sigmaRad], .classRenewingPeriods,
      [.correctionSignClassification], .recurrenceProgram⟩
  , ⟨[.sigmaRad], .geodesicCrossingReading,
      [.orientedGeodesics, .equivalenceProof], .modularGeometricCompanion⟩
  , ⟨[.archiveAge, .winding, .lift, .trace, .renewal, .ridgeDefect], .numericalContinuumState,
      [.encodingE, .commutationTheorem], .substrateToField⟩
  , ⟨[.chamberPair, .parityExchange], .chamberPotential,
      [.representation, .domain, .noSubstrateFeedback], .substrateToField⟩
  , ⟨[.hyperbolicRelMatrix], .impedanceMassChart,
      [.expandingMultiplier, .dimensionfulCalibratedMap], .massImpedanceProjection⟩
  , ⟨[.retainedAlternatives, .jointTrails, .lift, .renewalClass], .exchangeExclusionSectors,
      [.jointContinuationLaw, .exchangeLaw], .fermionBosonProgram⟩
  , ⟨[.activeFaceExports, .shellCertificates], .persistentGlobalShells,
      [.multiCycleFamilies, .downstreamHypotheses], .globalRenewalShell⟩
  , ⟨[.completedProjection], .empiricalIdentification,
      [.observables, .calibration, .forbiddenChannels, .comparisonProtocol], .applicationPapers⟩ ]

theorem obligations_length : obligations.length = 9 := rfl

/-- **Definition 30.1, the owner column**, in order. -/
theorem owner_column :
    obligations.map (·.owner) =
      [.rademacherCompanion, .recurrenceProgram, .modularGeometricCompanion,
       .substrateToField, .substrateToField, .massImpedanceProjection,
       .fermionBosonProgram, .globalRenewalShell, .applicationPapers] := rfl

/-- The nine requested targets are pairwise distinct, and every row names at
    least one missing construction: no row is an obligation already met. -/
theorem targets_distinct_and_open :
    (obligations.map (·.target)).Nodup ∧ ∀ o ∈ obligations, o.missing ≠ [] := by
  decide

/-- The Substrate-to-Field Correspondence owns exactly two rows (the encoding
    `E` and the chamber potential); every other owner owns one. -/
theorem substrateToField_rows :
    (obligations.filter (fun o => o.owner == .substrateToField)).length = 2 := rfl

/-! ## Proposition 30.2 — The exact multiplier is a dimensionless quadratic irrational -/

/-- **Proposition 30.2, Cayley–Hamilton.** For `det Q = 1` and `t = tr Q`,
    `Q² = tQ − I`, entry by entry. So the expanding multiplier of a hyperbolic
    `Q` is a root of `x² − t x + 1`, and it is fixed by the integer `t`. -/
theorem cayley_hamilton (Q : Mat2) (h : Q.det = 1) :
    Q * Q = ⟨RadTransport.trace Q * Q.a - 1, RadTransport.trace Q * Q.b,
             RadTransport.trace Q * Q.c, RadTransport.trace Q * Q.d - 1⟩ := by
  obtain ⟨a, b, c, d⟩ := Q
  have h' : a * d - b * c = 1 := h
  change (⟨a * a + b * c, a * b + b * d, c * a + d * c, c * b + d * d⟩ : Mat2) =
    ⟨(a + d) * a - 1, (a + d) * b, (a + d) * c, (a + d) * d - 1⟩
  have e1 : (a + d) * a = a * a + a * d := by ring
  have e2 : (a + d) * d = a * d + d * d := by ring
  have e3 : c * b = b * c := Int.mul_comm c b
  rw [Mat2.mk.injEq, e1, e2, e3]
  exact ⟨by omega, by ring, by ring, by omega⟩

/-- **Proposition 30.2, the discriminant.** For every integer `t ≥ 3`, `t² − 4`
    is not a perfect square, because `(t − 1)² < t² − 4 < t²`. -/
theorem disc_not_square (t : ℤ) (ht : 3 ≤ t) (s : ℤ) : s * s ≠ t * t - 4 := by
  have key : ∀ u : ℤ, 0 ≤ u → u * u ≠ t * t - 4 := by
    intro u hu
    rcases Int.lt_or_le u t with hlt | hge
    · have hle : u ≤ t - 1 := by omega
      have h1 : u * u ≤ (t - 1) * (t - 1) := Int.mul_le_mul hle hle hu (by omega)
      have e : (t - 1) * (t - 1) = t * t - 2 * t + 1 := by ring
      omega
    · have h1 : t * t ≤ u * u := Int.mul_le_mul hge hge (by omega) hu
      omega
  rcases Int.lt_or_le s 0 with hs | hs
  · have e : s * s = (-s) * (-s) := by ring
    rw [e]; exact key (-s) (by omega)
  · exact key s hs

/-- The descent step on positive pairs. If `p, q > 0` and
    `p² − t p q + q² = 0` then either `(q, p)` (when `p < q`) or the Vieta jump
    `(q, t q − p)` (when `p > q`, and then `0 < tq − p < q`) is a solution with a
    strictly smaller second coordinate; `p = q` forces `t = 2`. -/
theorem pos_descent (t : ℤ) (ht : 3 ≤ t) :
    ∀ n : ℕ, ∀ p q : ℤ, q.natAbs ≤ n → 0 < q → 0 < p → p * p - t * p * q + q * q ≠ 0
  | 0, _, q, hn, hq, _ => by omega
  | n + 1, p, q, hn, hq, hp => by
    intro E
    rcases Int.lt_trichotomy p q with hlt | heq | hgt
    · have e : q * q - t * q * p + p * p = p * p - t * p * q + q * q := by ring
      exact pos_descent t ht n q p (by omega) hp hq (by rw [e]; exact E)
    · subst heq
      have e : p * p - t * p * p + p * p = (2 - t) * (p * p) := by ring
      have hneg : (2 - t) * (p * p) < 0 :=
        Int.mul_neg_of_neg_of_pos (by omega) (Int.mul_pos hp hp)
      rw [e] at E
      omega
    · have hpr : p * (t * q - p) = q * q := by
        have e : p * (t * q - p) = t * p * q - p * p := by ring
        rw [e]; omega
      have hqq : 0 < q * q := Int.mul_pos hq hq
      have hr0 : 0 < t * q - p := by
        rcases Int.lt_or_le 0 (t * q - p) with h | h
        · exact h
        · have h1 : p * (t * q - p) ≤ p * 0 := Int.mul_le_mul_of_nonneg_left h (by omega)
          have e0 : p * 0 = 0 := Int.mul_zero p
          omega
      have hrq : t * q - p < q := by
        rcases Int.lt_or_le (t * q - p) q with h | h
        · exact h
        · have h1 : p * q ≤ p * (t * q - p) := Int.mul_le_mul_of_nonneg_left h (by omega)
          have h2 : q * q < p * q := Int.mul_lt_mul_of_pos_right hgt hq
          omega
      have e : q * q - t * q * (t * q - p) + (t * q - p) * (t * q - p)
          = p * p - t * p * q + q * q := by ring
      exact pos_descent t ht n q (t * q - p) (by omega) hr0 hq (by rw [e]; exact E)

/-- Opposite signs cannot solve `p² − t p q + q² = 0` with `q ≠ 0`: the left side
    is `p² + q² + t·|pq| > 0`. -/
theorem mixed_sign_ne (t : ℤ) (ht : 3 ≤ t) (p q : ℤ) (hq : 0 < q * q) (hpp : 0 ≤ p * p)
    (hpq : p * q ≤ 0) : p * p - t * p * q + q * q ≠ 0 := by
  have e : p * p - t * p * q + q * q = p * p + q * q - t * (p * q) := by ring
  have h1 : t * (p * q) ≤ t * 0 := Int.mul_le_mul_of_nonneg_left hpq (by omega)
  have e0 : t * 0 = 0 := Int.mul_zero t
  omega

/-- **Proposition 30.2, no rational multiplier.** For every integer `t ≥ 3`,
    `x² − t x + 1` has no root `p/q`. Written without division:
    `p² − t p q + q² ≠ 0` whenever `q ≠ 0`. With `q = 1` this is "no integer
    multiplier". -/
theorem no_rational_root (t : ℤ) (ht : 3 ≤ t) (p q : ℤ) (hq : q ≠ 0) :
    p * p - t * p * q + q * q ≠ 0 := by
  rcases Int.lt_trichotomy 0 q with hq0 | hq0 | hq0
  · have hqq : 0 < q * q := Int.mul_pos hq0 hq0
    rcases Int.lt_trichotomy 0 p with hp0 | hp0 | hp0
    · exact pos_descent t ht q.natAbs p q (Nat.le_refl _) hq0 hp0
    · subst hp0
      exact mixed_sign_ne t ht 0 q hqq (by decide) (Int.le_of_eq (Int.zero_mul q))
    · exact mixed_sign_ne t ht p q hqq (Int.le_of_lt (Int.mul_pos_of_neg_of_neg hp0 hp0))
        (Int.le_of_lt (Int.mul_neg_of_neg_of_pos hp0 hq0))
  · exact absurd hq0.symm hq
  · have hqq : 0 < q * q := Int.mul_pos_of_neg_of_neg hq0 hq0
    rcases Int.lt_trichotomy 0 p with hp0 | hp0 | hp0
    · exact mixed_sign_ne t ht p q hqq (Int.le_of_lt (Int.mul_pos hp0 hp0))
        (Int.le_of_lt (Int.mul_neg_of_pos_of_neg hp0 hq0))
    · subst hp0
      exact mixed_sign_ne t ht 0 q hqq (by decide) (Int.le_of_eq (Int.zero_mul q))
    · have e : (-p) * (-p) - t * (-p) * (-q) + (-q) * (-q) = p * p - t * p * q + q * q := by ring
      rw [← e]
      exact pos_descent t ht (-q).natAbs (-p) (-q) (Nat.le_refl _) (by omega) (by omega)

/-- **Proposition 30.2.** For every `Q ∈ SL(2,ℤ)` with `t = tr Q ≥ 3` (the
    integer form of `t > 2`): `Q² = tQ − I`, the discriminant `t² − 4` is not a
    square, and the multiplier root of `x² − t x + 1` is not rational.

    **Not a mass map.** The exact multiplier is determined by `Q` as the
    irrational root of an integer polynomial. This file carries no unit, no
    dimension and no calibration constant, and it declares none: neither `t`
    nor the multiplier is a mass, energy, distance or frequency here. That map
    is row 6 of `obligations`, owned by the mass/impedance projection. -/
theorem prop_30_2 (Q : Mat2) (hdet : Q.det = 1) (ht : 3 ≤ RadTransport.trace Q) :
    Q * Q = ⟨RadTransport.trace Q * Q.a - 1, RadTransport.trace Q * Q.b,
             RadTransport.trace Q * Q.c, RadTransport.trace Q * Q.d - 1⟩ ∧
    (∀ s : ℤ, s * s ≠ RadTransport.trace Q * RadTransport.trace Q - 4) ∧
    (∀ p q : ℤ, q ≠ 0 → p * p - RadTransport.trace Q * p * q + q * q ≠ 0) :=
  ⟨cayley_hamilton Q hdet, disc_not_square _ ht, fun p q hq => no_rational_root _ ht p q hq⟩

/-- **Proposition 30.2, the witness.** `R·L = 𝖠_R²` has determinant `1` and
    trace `3`; `(RL)² = 3·RL − I`; its multiplier is the root of `x² − 3x + 1`,
    discriminant `5`, not rational. Row 6's source datum is this matrix. -/
theorem prop_30_2_witness :
    Mirror.AR * Mirror.AR = Mat2.R * Mat2.L ∧
    (Mat2.R * Mat2.L).det = 1 ∧ RadTransport.trace (Mat2.R * Mat2.L) = 3 ∧
    (Mat2.R * Mat2.L) * (Mat2.R * Mat2.L) = ⟨3 * 2 - 1, 3 * 1, 3 * 1, 3 * 1 - 1⟩ ∧
    (∀ p q : ℤ, q ≠ 0 → p * p - 3 * p * q + q * q ≠ 0) :=
  ⟨Mirror.squares.1, by decide, by decide, by decide,
    fun p q hq => no_rational_root 3 (by decide) p q hq⟩

/-! ## Theorem 30.3 — The temporal engine and the recurrences are proved upstream of every obligation -/

/-- **Theorem 30.3, clauses 1–8.** Each field's type is *the statement* of an
    already-built theorem, read off the declaration by `type_of%`, not
    retyped. None of those statements mentions `ProjOb`, a field coordinate, a
    unit, a physical label, a geodesic crossing, an exchange law or a global
    shell, and none of their files imports this one.

    1. one-tick map, append-only across the advance: Corollary 12.8;
    2. iteration to the declared horizon: Corollary 15.7;
    3. terminal trichotomy and its dispatch: Theorems 17.3 and 20.4;
    4. snap and observer adoption: Theorem 18.2 and Definition 20.2;
    5. sibling emission for eligible faces: Corollary 22.7;
    6. renewal and release: Theorems 24.7 and 24.14;
    7. export of active and archival ledgers: Theorem 25.3;
    8. mirror (26.3), chamber (27.4), Rademacher (28.7), golden ridge (29.3). -/
structure EngineClauses : Prop where
  oneTick : type_of% @Advance.advanceCarrier_ledger_prefix
  horizon : type_of% @Accumulation.sevenfold_terminal_carrier
  trichotomy : type_of% @Terminal.termStatus_trichotomy
  dispatch : type_of% @Cycle.cycle_dispatch_total
  snap : type_of% @Snap.snap_isSome_iff
  adoption : type_of% @Cycle.completeUpdate_isSome
  siblingEmission : type_of% @Face.universal_emission
  renewal : type_of% @Lifecycle.renewal_no_recurrence
  release : type_of% @Lifecycle.release_deletes_nothing
  exportLedgers : type_of% @Shell.shellIn_recoverable
  mirror : type_of% @Mirror.AR_pow_fib
  chamber : type_of% @Chamber.alternation_R
  rademacher : type_of% @RadTransport.opposite_routes_unbounded
  ridge : type_of% @RidgeDefect.thm_29_3_square

/-- The eight clauses hold, each by the cited theorem and nothing else. -/
theorem engineClauses : EngineClauses :=
  ⟨@Advance.advanceCarrier_ledger_prefix, @Accumulation.sevenfold_terminal_carrier,
   @Terminal.termStatus_trichotomy, @Cycle.cycle_dispatch_total, @Snap.snap_isSome_iff,
   @Cycle.completeUpdate_isSome, @Face.universal_emission, @Lifecycle.renewal_no_recurrence,
   @Lifecycle.release_deletes_nothing, @Shell.shellIn_recoverable, @Mirror.AR_pow_fib,
   @Chamber.alternation_R, @RadTransport.opposite_routes_unbounded, @RidgeDefect.thm_29_3_square⟩

/-- A candidate integer chart on relative matrices: `k · tr Q`. Nothing here
    says any `k` is physical; the family exists to show the data do not pick one. -/
def chart (k : ℤ) (Q : Mat2) : ℤ := k * RadTransport.trace Q

theorem trace_side_exchange (Q : Mat2) :
    RadTransport.trace (SideExchange.P * Q * SideExchange.P) = RadTransport.trace Q := by
  obtain ⟨a, b, c, d⟩ := Q
  change (0 * a + 1 * c) * 0 + (0 * b + 1 * d) * 1 + ((1 * a + 0 * c) * 1 + (1 * b + 0 * d) * 0) = a + d
  omega

/-- **Theorem 30.3, the converse.** Completion of the recurrence does not prove
    a listed projection. Witness for row 6: every chart `k · tr` with `k > 0` is
    invariant under the side exchange and strictly increasing along the strobe
    `Q_R((RL)^r)` (trace `F_{2r+1}`, Proposition 29.6), yet `k = 1` and `k = 2`
    disagree on `R·L`. The exact relations checked here fix the trace; they do
    not fix a calibration. -/
theorem thm_30_3 :
    EngineClauses ∧
    (∀ k : ℤ, ∀ Q : Mat2, chart k (SideExchange.P * Q * SideExchange.P) = chart k Q) ∧
    (∀ k : ℤ, 0 < k → ∀ r : ℕ,
      chart k (RidgeDefect.QR (RidgeDefect.rlWord r)) <
        chart k (RidgeDefect.QR (RidgeDefect.rlWord (r + 1)))) ∧
    chart 1 (Mat2.R * Mat2.L) ≠ chart 2 (Mat2.R * Mat2.L) := by
  refine ⟨engineClauses, fun k Q => ?_, fun k hk r => ?_, by decide⟩
  · unfold chart; rw [trace_side_exchange]
  · unfold chart
    have h0 : RadTransport.trace (RidgeDefect.QR (RidgeDefect.rlWord r)) = Mirror.F (2 * r + 1) :=
      RidgeDefect.QR_strobe_trace r
    have h1 : RadTransport.trace (RidgeDefect.QR (RidgeDefect.rlWord (r + 1))) =
        Mirror.F (2 * (r + 1) + 1) := RidgeDefect.QR_strobe_trace (r + 1)
    rw [h0, h1]
    exact Int.mul_lt_mul_of_pos_left (RidgeDefect.strobe_growth r).1 hk

/-! ## Separation Rule 30.4 — Correspondence requires an explicit map -/

/-- **Separation Rule 30.4.** What authorizes correspondence: an explicit
    encoding `E`, its domain (closed under the substrate update), and a
    commutation theorem on that domain. -/
structure Correspondence (S T : Type) (stepS : S → S) (stepT : T → T) where
  E : S → T
  domain : S → Prop
  domain_closed : ∀ s, domain s → domain (stepS s)
  commutes : ∀ s, domain s → E (stepS s) = stepT (E s)

/-- The distinctions a correspondence discards: distinct sources with one image.
    The retained ones are the complement. Both are read off `E`, never assumed. -/
def Correspondence.discards {S T : Type} {stepS : S → S} {stepT : T → T}
    (C : Correspondence S T stepS stepT) (s s' : S) : Prop :=
  s ≠ s' ∧ C.E s = C.E s'

/-- The exchange intertwines `RL` with `LR` on integer columns. -/
theorem exchange_intertwines (v : ℤ × ℤ) :
    Mirror.mulVec SideExchange.P (Mirror.mulVec (Mat2.R * Mat2.L) v) =
      Mirror.mulVec (Mat2.L * Mat2.R) (Mirror.mulVec SideExchange.P v) := by
  obtain ⟨x, y⟩ := v
  rw [show Mat2.R * Mat2.L = ⟨2, 1, 1, 1⟩ by decide, show Mat2.L * Mat2.R = ⟨1, 1, 1, 2⟩ by decide]
  change ((0 : ℤ) * (2 * x + 1 * y) + 1 * (1 * x + 1 * y), (1 : ℤ) * (2 * x + 1 * y) + 0 * (1 * x + 1 * y)) =
    ((1 : ℤ) * (0 * x + 1 * y) + 1 * (1 * x + 0 * y), (1 : ℤ) * (0 * x + 1 * y) + 2 * (1 * x + 0 * y))
  rw [Prod.mk.injEq]
  exact ⟨by omega, by omega⟩

/-- The explicit correspondence `RL ⟶ LR` with `E = P` on all columns. -/
def rlToLr : Correspondence (ℤ × ℤ) (ℤ × ℤ) (Mirror.mulVec (Mat2.R * Mat2.L))
    (Mirror.mulVec (Mat2.L * Mat2.R)) where
  E := Mirror.mulVec SideExchange.P
  domain := fun _ => True
  domain_closed := fun _ _ => trivial
  commutes := fun v _ => exchange_intertwines v

/-- **Separation Rule 30.4, first witness.** `RL` and `LR` resemble each other
    exactly (equal trace `3`, equal determinant `1`, both Fibonacci), and the
    identity identification is still not a correspondence: it fails on `(1,0)`.
    A correspondence exists, `rlToLr`, and it is the explicit `E = P`, not the
    resemblance. -/
theorem resemblance_not_identity :
    RadTransport.trace (Mat2.R * Mat2.L) = RadTransport.trace (Mat2.L * Mat2.R) ∧
    (Mat2.R * Mat2.L).det = (Mat2.L * Mat2.R).det ∧
    Mirror.mulVec (Mat2.R * Mat2.L) (1, 0) ≠ Mirror.mulVec (Mat2.L * Mat2.R) (1, 0) ∧
    rlToLr.E (1, 0) = (0, 1) := by
  decide

/-- **Separation Rule 30.4, second witness.** Equal trace is not even enough for
    an encoding to exist. `𝖠_R` (Fibonacci growth, `det −1`, Theorem 26.3) and
    `Q_R(ε)` (the order-six return, `det 1`, 28.13 scan) both have trace `1`, and
    no integer matrix `E` with `det E ≠ 0` satisfies `E·𝖠_R = Q_R(ε)·E`: taking
    determinants gives `−det E = det E`. -/
theorem equal_trace_no_linear_encoding :
    RadTransport.trace Mirror.AR = RadTransport.trace (RadTransport.Qs true []) ∧
    matPow (RadTransport.Qs true []) 6 = 1 ∧
    ∀ E : Mat2, E.det ≠ 0 → E * Mirror.AR ≠ RadTransport.Qs true [] * E := by
  refine ⟨by decide, RadTransport.ray_elliptic_orders.1.1, fun E hE h => hE ?_⟩
  have hd := congrArg Mat2.det h
  rw [Mat2.det_mul, Mat2.det_mul, show Mirror.AR.det = -1 by decide,
    show (RadTransport.Qs true []).det = 1 by decide] at hd
  omega

/-- A declared error budget for Separation Rule 30.4's controlled-error branch: an
    error `dist` on targets, zero exactly on equal targets, and a bound per
    source. The error is a natural number: the tree has no reals, so a
    real-valued closeness or a limiting relation (Def 12.3's second clause) is
    not modelled. -/
structure ErrorBudget (S T : Type) where
  dist : T → T → ℕ
  dist_eq_zero : ∀ a b, dist a b = 0 ↔ a = b
  bound : S → ℕ

/-- The tolerance a correspondence claim states before its theorem: `exact`
    (commutation) or `within B` (controlled error, budget `B`). -/
inductive Tolerance (S T : Type) where
  | exact
  | within (B : ErrorBudget S T)

/-- **Separation Rule 30.4, the authorizing theorem.** At tolerance `exact`, the
    commutation square `E (stepS s) = stepT (E s)` on the domain. At tolerance
    `within B`, the controlled-error inequality
    `B.dist (E (stepS s)) (stepT (E s)) ≤ B.bound s` on the domain.
    NOT CONSTRAINED: which budgets count as controlled. The budget is part of the
    claim's type, fixed before `E`, so at one stated budget the theorem excludes
    encodings (`within_excludes`); over all budgets every encoding meets some
    budget (`every_encoding_meets_some_budget`). -/
def CorrespondenceTheorem {S T : Type} (stepS : S → S) (stepT : T → T)
    (E : S → T) (domain : S → Prop) : Tolerance S T → Prop
  | .exact => ∀ s, domain s → E (stepS s) = stepT (E s)
  | .within B => ∀ s, domain s → B.dist (E (stepS s)) (stepT (E s)) ≤ B.bound s

/-- **Separation Rule 30.4, as the book states it**, at a stated tolerance: an
    explicit encoding `E`, its domain, and a commutation or controlled-error
    theorem on that domain. The domain is any declared predicate; unlike
    `Correspondence`, it is not required to be closed under `stepS`. The retained
    and discarded distinctions are `CorrespondenceRule.retains` and
    `CorrespondenceRule.discards`, read off `E`. -/
structure CorrespondenceRule (S T : Type) (stepS : S → S) (stepT : T → T)
    (tol : Tolerance S T) where
  E : S → T
  domain : S → Prop
  authorized : CorrespondenceTheorem stepS stepT E domain tol

/-- The distinctions a correspondence discards: distinct sources with one image. -/
def CorrespondenceRule.discards {S T : Type} {stepS : S → S} {stepT : T → T}
    {tol : Tolerance S T} (C : CorrespondenceRule S T stepS stepT tol) (s s' : S) : Prop :=
  s ≠ s' ∧ C.E s = C.E s'

/-- The distinctions a correspondence retains: distinct sources with distinct images. -/
def CorrespondenceRule.retains {S T : Type} {stepS : S → S} {stepT : T → T}
    {tol : Tolerance S T} (C : CorrespondenceRule S T stepS stepT tol) (s s' : S) : Prop :=
  s ≠ s' ∧ C.E s ≠ C.E s'

/-- A distinction is retained exactly when it is a distinction and not discarded. -/
theorem CorrespondenceRule.retains_iff {S T : Type} {stepS : S → S} {stepT : T → T}
    {tol : Tolerance S T} (C : CorrespondenceRule S T stepS stepT tol) (s s' : S) :
    C.retains s s' ↔ s ≠ s' ∧ ¬ C.discards s s' :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, fun ⟨_, h⟩ => h2 h⟩, fun ⟨h1, h2⟩ => ⟨h1, fun h => h2 ⟨h1, h⟩⟩⟩

/-- No distinction is both retained and discarded. -/
theorem CorrespondenceRule.not_retains_and_discards {S T : Type} {stepS : S → S}
    {stepT : T → T} {tol : Tolerance S T} (C : CorrespondenceRule S T stepS stepT tol)
    (s s' : S) : ¬ (C.retains s s' ∧ C.discards s s') :=
  fun ⟨⟨_, h⟩, ⟨_, h'⟩⟩ => h h'

/-- `Correspondence` (closed domain, commutation) gives a `CorrespondenceRule` at
    tolerance `exact`, with the same `E` and domain. -/
def Correspondence.toRule {S T : Type} {stepS : S → S} {stepT : T → T}
    (C : Correspondence S T stepS stepT) : CorrespondenceRule S T stepS stepT .exact :=
  ⟨C.E, C.domain, C.commutes⟩

/-- With every bound zero, the controlled-error theorem is exactly the commutation
    square. -/
theorem within_zero_iff {S T : Type} (stepS : S → S) (stepT : T → T) (E : S → T)
    (domain : S → Prop) (B : ErrorBudget S T) (h0 : ∀ s, B.bound s = 0) :
    CorrespondenceTheorem stepS stepT E domain (.within B) ↔
      CorrespondenceTheorem stepS stepT E domain .exact :=
  ⟨fun h s hs => (B.dist_eq_zero _ _).mp (Nat.le_zero.mp (h0 s ▸ h s hs)),
   fun h s hs => (h0 s).symm ▸ Nat.le_zero.mpr ((B.dist_eq_zero _ _).mpr (h s hs))⟩

set_option linter.unusedVariables false in
/-- Integer columns' error `|a − b|` with bound `1` everywhere. -/
def unitBudget : ErrorBudget ℤ ℤ where
  dist a b := (a - b).natAbs
  dist_eq_zero a b := Int.natAbs_eq_zero.trans Int.sub_eq_zero
  bound _ := 1

/-- Guard: at the stated budget `unitBudget`, the identity encoding of `id` into
    `x ↦ x + 2` is excluded on the all-integers domain (at `0` the error is `2 > 1`). -/
theorem within_excludes :
    ¬ CorrespondenceTheorem (id : ℤ → ℤ) (· + 2) id (fun _ => True) (.within unitBudget) := by
  intro h
  exact absurd (h 0 trivial) (by decide)

set_option linter.unusedDecidableInType false in
/-- The trivial inhabitant, named: on a target with decidable equality, every
    encoding meets some budget (`0/1` error, bound equal to the error). So a
    controlled-error claim says something only through the budget it states. -/
theorem every_encoding_meets_some_budget
    {S T : Type} [DecidableEq T] (stepS : S → S)
    (stepT : T → T) (E : S → T) (domain : S → Prop) :
    ∃ B : ErrorBudget S T, CorrespondenceTheorem stepS stepT E domain (.within B) :=
  ⟨⟨fun a b => if a = b then 0 else 1, fun a b => by by_cases h : a = b <;> simp [h],
    fun s => if E (stepS s) = stepT (E s) then 0 else 1⟩, fun _ _ => Nat.le_refl _⟩

/-! ## Boundary Statement 30.5 -/

/-- **Boundary Statement 30.5, the left side.** The native recurrence results
    of §§26–29, named. -/
inductive RecurrenceResult where
  | mirrorFibonacci
  | chamberAlternation
  | rademacherOppositeRoutes
  | ridgeSquareInvariance
  deriving DecidableEq, Repr

/-- The statement each left-side entry stands for, read off the built theorem.
    Only the left side has a `statement`: an obligation is not a conclusion. -/
def RecurrenceResult.statement : RecurrenceResult → Prop
  | .mirrorFibonacci => type_of% @Mirror.AR_pow_fib
  | .chamberAlternation => type_of% @Chamber.alternation_R
  | .rademacherOppositeRoutes => type_of% @RadTransport.opposite_routes_unbounded
  | .ridgeSquareInvariance => type_of% @RidgeDefect.thm_29_3_square

theorem RecurrenceResult.holds : ∀ r : RecurrenceResult, r.statement
  | .mirrorFibonacci => @Mirror.AR_pow_fib
  | .chamberAlternation => @Chamber.alternation_R
  | .rademacherOppositeRoutes => @RadTransport.opposite_routes_unbounded
  | .ridgeSquareInvariance => @RidgeDefect.thm_29_3_square

def recurrenceResults : List RecurrenceResult :=
  [.mirrorFibonacci, .chamberAlternation, .rademacherOppositeRoutes, .ridgeSquareInvariance]

/-- **Boundary Statement 30.5, the division.** One entry is exactly one of an
    exact result or a declared obligation. -/
inductive Division (A B : Type) where
  | exact (a : A)
  | obligation (b : B)
  deriving DecidableEq, Repr

def Division.left? {A B : Type} : Division A B → Option A
  | .exact a => some a
  | .obligation _ => none

def Division.right? {A B : Type} : Division A B → Option B
  | .exact _ => none
  | .obligation b => some b

/-- No entry is on both sides. -/
theorem Division.not_both {A B : Type} (x : Division A B) :
    ¬ (x.left?.isSome = true ∧ x.right?.isSome = true) := by
  cases x <;> simp only [Division.left?, Division.right?, Option.isSome, Bool.false_eq_true,
    and_false, false_and, not_false_eq_true]

def divide {A B : Type} (as : List A) (bs : List B) : List (Division A B) :=
  as.map .exact ++ bs.map .obligation

/-- The left projection recovers the exact results, in order. -/
theorem filterMap_left {A B : Type} (bs : List B) :
    ∀ as : List A, (divide as bs).filterMap Division.left? = as
  | [] => by
    change (bs.map Division.obligation).filterMap Division.left? = []
    induction bs with
    | nil => rfl
    | cons b bs ih => exact ih
  | a :: as => congrArg (a :: ·) (filterMap_left bs as)

/-- The right projection recovers the obligations, in order. -/
theorem filterMap_right {A B : Type} (bs : List B) :
    ∀ as : List A, (divide as bs).filterMap Division.right? = bs
  | [] => by
    change (bs.map Division.obligation).filterMap Division.right? = bs
    induction bs with
    | nil => rfl
    | cons b bs ih => exact congrArg (b :: ·) ih
  | _ :: as => filterMap_right bs as

/-- **Boundary Statement 30.5.** The native recurrence block ends in a lossless
    division `exact recurrence results | declared downstream projection
    obligations`: both sides are recovered whole and in order from the one
    ledger, the left side holds at the scope proved in §§26–29, and the right
    side is the ordered list of Definition 30.1, carrying no statement. -/
theorem boundary_30_5 :
    (divide recurrenceResults obligations).filterMap Division.left? = recurrenceResults ∧
    (divide recurrenceResults obligations).filterMap Division.right? = obligations ∧
    (divide recurrenceResults obligations).length = 13 ∧
    (∀ r ∈ recurrenceResults, r.statement) :=
  ⟨filterMap_left _ _, filterMap_right _ _, rfl, fun r _ => r.holds⟩

/-- **Theorem 30.3 item 8 and Boundary Statement 30.5, the Rademacher clause with
    its values.** `EngineClauses.rademacher` and `RecurrenceResult.rademacherOppositeRoutes`
    cite `opposite_routes_unbounded`, which states only the winding bounds of
    Theorem 28.7. The recurrence values `σ_Rad`, `Φ_Rad`, `Ψ_Rad` are proved only
    under `RadCocycle`, so this clause carries them conditionally: each field has
    type `RadCocycle → …`. It states nothing about whether `RadCocycle` holds. -/
structure RademacherClause : Prop where
  /-- Theorem 28.7, for every `m ≥ 3`: lengths, balances, `σ_Rad`, `Φ_Rad`, `Ψ_Rad`. -/
  oppositeRoutes : type_of% @RadTransport.opposite_routes
  /-- Theorem 28.9, the table: `Φ_Rad`, trace, `σ_Rad`, `Ψ_Rad` on the alternating words. -/
  alternatingTable : type_of% @RadTransport.alternating_table

/-- The Rademacher clause holds, each field by the cited theorem and nothing else. -/
theorem rademacherClause : RademacherClause :=
  ⟨@RadTransport.opposite_routes, @RadTransport.alternating_table⟩

/-! ## Theorem 30.3, items 2 and 5 at the book's scope, and the converse row by row -/

/-- **Theorem 30.3, items 2 and 5, at the book's scope.** `EngineClauses.horizon`
    is Corollary 15.7, the seven-tick horizon only. Item 2 says "iterate it
    through the declared horizon", any declared `h`: the field `horizon` is
    Definition 15.1's iterate reaching tick `h` at every `h`. Item 5 says "select
    and record eligible sibling faces"; `EngineClauses.siblingEmission` is the
    emission matrices of Corollary 22.7. The fields below are the selection
    theorem (22.6), the attachment of exactly the eligible packets (II.2), and the
    recording of the attached ledger (23.11), each read off by `type_of%`. -/
structure EngineScope : Prop where
  /-- Item 2: at every declared horizon `h`, the iterate reaches tick `h`. -/
  horizon : ∀ {Aux : Type} {h : ℕ} (pol : Accumulation.Policy Aux h)
    (X0 : TickCarrier Aux h) (hX0 : Accumulation.Seeded X0),
    ((Accumulation.iterate pol X0 hX0 h (Nat.le_refl h)).tick : ℕ) = h
  /-- Item 5, select: Theorem 22.6. -/
  faceSelection : type_of% @Face.face_selection
  /-- Item 5, attach exactly the eligible packets: Construction Axiom II.2. -/
  attachEligible : type_of% @Face.attached_iff
  /-- Item 5, record: Boundary Statement 23.11 (`recordFace`, Definition 23.5). -/
  recordEligible : type_of% @Incidence.cycle_exports_face_ledger

/-- Items 2 and 5 hold, each by the cited theorem and nothing else. -/
theorem engineScope : EngineScope :=
  ⟨fun pol X0 hX0 => Accumulation.iterate_tick pol X0 hX0 _ (Nat.le_refl _),
   @Face.face_selection, @Face.attached_iff, @Incidence.cycle_exports_face_ledger⟩

/-- Row 1 candidate crosswalk `[Φ_Rad]₂₄ → ψ₁₂`: `n ↦ k·n mod 12`. -/
def crosswalk (k n : ℤ) : ℤ := (k * n) % 12

/-- Row 3 candidate reading of `σ_Rad` as a crossing orientation: `σ ↦ ε·σ`. -/
def crossingReading (ε σ : ℤ) : ℤ := ε * σ

/-- Row 4 candidate encodings of a column: the identity and the negation. -/
def encodePos (v : ℤ × ℤ) : ℤ × ℤ := v
def encodeNeg (v : ℤ × ℤ) : ℤ × ℤ := (-v.1, -v.2)

theorem mulVec_neg (M : Mat2) (v : ℤ × ℤ) :
    Mirror.mulVec M (encodeNeg v) = encodeNeg (Mirror.mulVec M v) := by
  obtain ⟨x, y⟩ := v
  change (M.a * -x + M.b * -y, M.c * -x + M.d * -y) = (-(M.a * x + M.b * y), -(M.c * x + M.d * y))
  rw [Prod.mk.injEq]
  constructor <;> ring

/-- Row 4: the identity encoding of the mirror update `𝖠_R` on columns. -/
def mirrorPos : Correspondence (ℤ × ℤ) (ℤ × ℤ) (Mirror.mulVec Mirror.AR) (Mirror.mulVec Mirror.AR) where
  E := encodePos
  domain := fun _ => True
  domain_closed := fun _ _ => trivial
  commutes := fun _ _ => rfl

/-- Row 4: the negation encoding of the same update. -/
def mirrorNeg : Correspondence (ℤ × ℤ) (ℤ × ℤ) (Mirror.mulVec Mirror.AR) (Mirror.mulVec Mirror.AR) where
  E := encodeNeg
  domain := fun _ => True
  domain_closed := fun _ _ => trivial
  commutes := fun v _ => (mulVec_neg Mirror.AR v).symm

/-- Row 5 candidate potentials on chamber pairs: `k·(p² − q²)`, the first
    component of `Φ_ch` scaled by `k`. -/
def chamberPotential (k : ℤ) (v : ℕ × ℕ) : ℤ := k * (Chamber.phiCh v).1

/-- Row 9 candidate calibrations of an exact integer value: `x ↦ k·x`. -/
def calibrate (k x : ℤ) : ℤ := k * x

/-- Row 2: the length-six balanced words `R L L L R R` and `(R L)³`. -/
def wordA : Word := [true, false, false, false, true, true]
def wordB : Word := [true, false, true, false, true, false]

/-- **Theorem 30.3, the converse, rows 1–5 and 7–9.** For each row, the exact
    data Elements II proves do not fix the requested construction: two
    candidates of the row's shape both satisfy the stated exact relation and
    still differ (rows 1–5, 7, 9), or the Elements II theorem shows the data
    stop short of the target (row 8). Row 6 is `thm_30_3`. Nothing here says any
    candidate is the right one.

    1. Two crosswalks `n ↦ k·n mod 12` (`k = 1, 2`), each well defined on
       `[Φ_Rad]₂₄` and additive mod 12, differ at `1`: the factor of two is open.
    2. `R L L L R R` and `(R L)³` are both balanced (Theorem 28.8's hypothesis)
       and of length six, start from the same matrix `Q_R(ε)`, and `σ_Rad` repeats
       after one period for the second and changes sign for the first: balance
       and period length do not classify the correction-sign recurrence.
    3. Two readings `σ ↦ ±σ` of `σ_Rad` as a crossing orientation, both odd and
       injective on `{−1, 0, 1}`, differ at `1`: no orientation is fixed.
    4. Two encodings of columns, `E = id` and `E = −id`, are each a
       `Correspondence` for the mirror update `𝖠_R` (commuting on every column)
       and each preserves the ridge defect `D_R`, and they differ at `(1, 0)`.
    5. Two potentials `k·(p² − q²)` (`k = 1, 2`) on chamber pairs, each odd under
       the parity exchange `(p,q) ↦ (q,p)` and zero on the membrane `p = q`
       (`k = 1` is zero only there), differ at `(2, 1)`.
    7. The side exchange `P` is an involution, and both of its sectors are
       inhabited by integer matrices: `P·I·P = I` and `P·D·P = −D` for
       `D = diag(1, −1)`. The exchange does not choose a symmetric or an
       antisymmetric sector.
    8. Theorem 23.8: on any family of one lineage's faces, every edge has
       incidence one, so no closed shell. This covers one lineage only; it
       states nothing about the multi-cycle families the row asks for.
    9. Two calibrations `x ↦ k·x` (`k = 1, 2`), each zero at zero and strictly
       increasing, differ at `1`: the exact value carries no unit. -/
theorem thm_30_3_converse :
    -- row 1
    ((∀ k ∈ [(1 : ℤ), 2], ∀ m n : ℤ, crosswalk k (n + 24) = crosswalk k n ∧
        crosswalk k (m + n) = (crosswalk k m + crosswalk k n) % 12) ∧
      crosswalk 1 1 ≠ crosswalk 2 1) ∧
    -- row 2
    (Word.bal wordA = 0 ∧ Word.bal wordB = 0 ∧ wordA.length = wordB.length ∧
      RadTransport.Qs true (RadTransport.wpow wordA 0) = RadTransport.Qs true (RadTransport.wpow wordB 0) ∧
      routeCorrection (RadTransport.Qs true (RadTransport.wpow wordB 1)) =
        routeCorrection (RadTransport.Qs true (RadTransport.wpow wordB 0)) ∧
      routeCorrection (RadTransport.Qs true (RadTransport.wpow wordA 1)) =
        - routeCorrection (RadTransport.Qs true (RadTransport.wpow wordA 0)) ∧
      routeCorrection (RadTransport.Qs true (RadTransport.wpow wordA 0)) ≠ 0) ∧
    -- row 3
    ((∀ ε ∈ [(1 : ℤ), -1], ∀ σ : ℤ, crossingReading ε (-σ) = - crossingReading ε σ) ∧
      (∀ ε ∈ [(1 : ℤ), -1], ∀ σ ∈ [(-1 : ℤ), 0, 1], ∀ τ ∈ [(-1 : ℤ), 0, 1],
        crossingReading ε σ = crossingReading ε τ → σ = τ) ∧
      crossingReading 1 1 ≠ crossingReading (-1) 1) ∧
    -- row 4
    ((∀ v : ℤ × ℤ, RidgeDefect.DRv (mirrorPos.E v) = RidgeDefect.DRv v ∧
        RidgeDefect.DRv (mirrorNeg.E v) = RidgeDefect.DRv v) ∧
      mirrorPos.E (1, 0) ≠ mirrorNeg.E (1, 0)) ∧
    -- row 5
    ((∀ k ∈ [(1 : ℤ), 2], ∀ v : ℕ × ℕ, chamberPotential k v.swap = - chamberPotential k v ∧
        (v.1 = v.2 → chamberPotential k v = 0)) ∧
      (∀ v : ℕ × ℕ, chamberPotential 1 v = 0 → v.1 = v.2) ∧
      chamberPotential 1 (2, 1) ≠ chamberPotential 2 (2, 1)) ∧
    -- row 7
    (SideExchange.P * SideExchange.P = 1 ∧
      SideExchange.P * 1 * SideExchange.P = 1 ∧
      SideExchange.P * ⟨1, 0, 0, -1⟩ * SideExchange.P = ⟨-1, 0, 0, 1⟩ ∧
      (⟨1, 0, 0, -1⟩ : Mat2) ≠ ⟨-1, 0, 0, 1⟩) ∧
    -- row 8
    (∀ (i : QuestionId) (evs : List ℕ), evs.Nodup → (∀ j ∈ evs, j < i.rel.length) →
      ∀ j ∈ evs, ∀ e ∈ Incidence.lineFaceE i j, (Incidence.lineIncE i evs e).length = 1) ∧
    -- row 9
    ((∀ k ∈ [(1 : ℤ), 2], calibrate k 0 = 0 ∧ ∀ x y : ℤ, x < y → calibrate k x < calibrate k y) ∧
      calibrate 1 1 ≠ calibrate 2 1) := by
  refine ⟨⟨?_, by decide⟩, by decide, ⟨?_, ?_, by decide⟩, ⟨?_, by decide⟩, ⟨?_, ?_, by decide⟩,
    by decide, fun i evs hnd hlt => Incidence.lineage_not_closed i evs hnd hlt, ⟨?_, by decide⟩⟩
  · intro k hk m n
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    unfold crosswalk
    rcases hk with rfl | rfl <;> constructor <;> omega
  · intro ε hε σ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hε
    unfold crossingReading
    rcases hε with rfl | rfl <;> omega
  · intro ε hε σ hσ τ hτ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hε hσ hτ
    unfold crossingReading
    rcases hε with rfl | rfl <;> omega
  · intro v
    obtain ⟨x, y⟩ := v
    refine ⟨rfl, ?_⟩
    change RidgeDefect.DR (-x) (-y) = RidgeDefect.DR x y
    unfold RidgeDefect.DR Chamber.N
    ring
  · intro k hk v
    obtain ⟨p, q⟩ := v
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    unfold chamberPotential Chamber.phiCh
    refine ⟨?_, fun h => ?_⟩
    · change k * ((q : ℤ) * q - (p : ℤ) * p) = -(k * ((p : ℤ) * p - (q : ℤ) * q))
      ring
    · simp only at h
      subst h
      change k * ((p : ℤ) * p - (p : ℤ) * p) = 0
      rw [Int.sub_self, Int.mul_zero]
  · intro v h
    obtain ⟨p, q⟩ := v
    unfold chamberPotential Chamber.phiCh at h
    change p = q
    have h' : ((p : ℤ) - q) * ((p : ℤ) + q) = 0 := by
      have : (1 : ℤ) * ((p : ℤ) * p - (q : ℤ) * q) = 0 := h
      rw [← this]; ring
    rcases Int.mul_eq_zero.mp h' with h1 | h1 <;> omega
  · intro k hk
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    unfold calibrate
    rcases hk with rfl | rfl <;> exact ⟨by omega, fun x y hxy => by omega⟩

end Obligations
end Two
end RatioSpace
