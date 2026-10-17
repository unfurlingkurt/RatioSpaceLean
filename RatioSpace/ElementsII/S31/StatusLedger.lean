/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S02.Frame
import RatioSpace.ElementsI.S04.Composition
import RatioSpace.ElementsI.S05.Zphi
import RatioSpace.ElementsI.S03.Walk
import RatioSpace.ElementsI.S08.Winding
import RatioSpace.ElementsI.S12.Correspondence
import RatioSpace.ElementsII.S02.Temporal
import RatioSpace.ElementsII.S03.Observer
import RatioSpace.ElementsII.S06.State
import RatioSpace.ElementsII.S08.Coherence
import RatioSpace.ElementsII.S09.Admission
import RatioSpace.ElementsII.S10.Causal
import RatioSpace.ElementsII.S14.Conservation
import RatioSpace.ElementsII.S13.SideExchange
import RatioSpace.ElementsII.S15.Accumulation
import RatioSpace.ElementsII.S16.RootOrbit
import RatioSpace.ElementsII.S17.Terminal
import RatioSpace.ElementsII.S16.LoneSeed
import RatioSpace.ElementsII.S18.Snap
import RatioSpace.ElementsII.S19.Return
import RatioSpace.ElementsII.S22.Face
import RatioSpace.ElementsII.S23.Incidence
import RatioSpace.ElementsII.S24.Lifecycle
import RatioSpace.ElementsII.S25.Shell
import RatioSpace.ElementsII.S26.Mirror
import RatioSpace.ElementsII.S27.Chamber
import RatioSpace.ElementsII.S28.RadTransport
import RatioSpace.ElementsII.S29.RidgeDefect
import RatioSpace.ElementsII.S30.Obligations
import RatioSpace.ElementsII.S16.Transient
import RatioSpace.ElementsII.S16.PrecaptureTie
/-!
  Elements II §31 — Theorem-status ledger.

  The book's §31 is a ledger: seven statuses (31.1), five tables (31.2–31.6), a
  closure theorem (31.7) and a five-way boundary (31.8). A ledger of labels would
  be a second copy of the book's prose. This file makes the ledger carry proofs.

  **What a row carries is decided by its status, in the type.** `Witness s` is
  indexed by the status `s`:

  * a **derived** row can only be built from a closed proof term, and the term
    cited is an existing theorem constant of this library (31.4);
  * a **conditional** row is also a proof term, of a statement whose hypotheses
    are the book's receiver / lift / socket / quotient data (31.5);
  * an **imported** row is either a proof term already in the library, or, for
    the classical Dedekind–Rademacher identities, the exact hypothesis structure
    (`RadCocycle ∧ RadConj`) that every consumer takes as an explicit argument
    and that this library does not prove (31.2, row 7);
  * a **declared** row (construction axiom or receiver declaration) carries the
    declaration the tree actually uses: the selector `axiomSelect`, the
    constructor `receivedFaces`, the constant `hQ`, the structures `Retention`
    and `Reception`, the socket domain and splice (31.3);
  * an **open** row carries nothing: `Witness .openDownstream` has exactly one
    inhabitant, so an open item cannot be an argument to anything (31.6).

  **What Theorem 31.7 says here.** Every row's claim holds (`Witness.holds`);
  every derived row of 31.4 except §30 bears a closed proof term; every
  conditional row bears one; every open row is the unique empty witness; the
  Rademacher identities enter the §28 row only as an explicit antecedent; and
  exactly rows 2–3, 15–17, 24 and 25 carry scope-column parts (imported,
  derived instance, conditional, conditional), each bearing a proof term. The
  dependency part, "no item of 31.5/31.6 is silently used", is carried by the
  construction rather than by a sentence: each cited proof is a closed constant,
  so its statement lists every hypothesis it uses, and open rows have no content
  to supply.

  **The scope column of 31.4.** Every 31.4 row has status `.derived` and its
  `wit` is the derived part. The row also carries `scope`, the book's scope
  column verbatim, and `parts`, the pieces of the range the scope column types
  otherwise, each an `Entry` with its own status and witness:

  * 2–3, "derived/imported as labeled": Proposition 3.6 (bilateral transport,
    book status "Imported result with constructive application") is an
    `.imported` part carrying `prop_3_6` and `prop_3_6_changes_admission`;
  * 15–17, "ensemble transients are derived instances with stated scope":
    Proposition 16.13 is a `.derivedInstance` part carrying
    `Transient.prop_16_13_i` to `_iv`, one per named seed instance;
  * 24, "covariance is conditional on receiver data": Proposition 24.18 is a
    `.conditional` part carrying `Lifecycle.covariance_conditional`, whose
    statement takes the domain, reception and gate preservation as hypotheses;
  * 25, "shell application is conditional": Corollary 25.11 is a
    `.conditional` part carrying `Shell.cor_25_11` (certificate all ones, and
    `D = 12`, as antecedents) and `Shell.cor_25_11_continuation` (a
    `ContinuationPreserves` hypothesis).

  Every other row has no parts. The other qualifiers in the scope column
  ("derived; support by Definition 8.1", "on the singleton return
  domain", "derived from the imported classical identities", and so on) are
  recorded in `scope` as text only; they name which declarations or imports a
  derivation uses, and the cited proof terms carry those uses in their
  statements (for §28, `row28_claim`). The parts are not rows of the combined
  ledger, so the counts of Theorem 31.7 and Boundary Statement 31.8 are the
  book's row counts.

  **The §30 row.** In `ledger31_4` the §30 row is marked `elsewhere`, and
  `thm_31_7` names it as the only row without a proof term there. Its proof term
  is `Obligations.thm_30_3`; `Obligations.lean` does not import this file, so it
  is imported here, and `row30` is that row carrying `thm_30_3`
  (`ledger31_4_proved`, `ledger31_4_proved_bearsProof`).

  **What is not built.** The Rademacher receiver-profile row (31.3 item 7) records the five
  integer readings built in `RadTransport` (Φ, Φ mod 24, σ, Ψ, trace); the lift
  coordinate of that tuple is the §9 `liftBit`, not repeated here. Theorem 31.7's
  sentence about Sections 0–10 fixing the grammar is prose about the book's
  order and has no Lean content beyond the rows.
-/
set_option linter.style.longLine false
namespace RatioSpace
namespace Two
namespace StatusLedger

/-! ## Definition 31.1 — Status vocabulary -/

/-- **Definition 31.1.** The seven status types of a formal result. -/
inductive Status where
  | imported
  | constructionAxiom
  | receiverDeclaration
  | derived
  | derivedInstance
  | conditional
  | openDownstream
  deriving DecidableEq, Repr

/-- The seven statuses, once each. -/
def allStatuses : List Status :=
  [.imported, .constructionAxiom, .receiverDeclaration, .derived, .derivedInstance,
    .conditional, .openDownstream]

/-- The seven statuses are pairwise distinct. -/
theorem allStatuses_nodup : allStatuses.Nodup := by decide

/-- Every status is on the list, so the vocabulary is exactly seven. -/
theorem mem_allStatuses (s : Status) : s ∈ allStatuses := by cases s <;> decide

theorem allStatuses_length : allStatuses.length = 7 := rfl

/-! ## Witnesses: what a row carries, by status -/

/-- Lift a `Type`-valued declaration into the witness universe. -/
def up {T : Type} (v : T) : ULift.{1} T := ULift.up v

/-- **What a row of the ledger carries.** Indexed by status, so a derived row
    cannot be built without a proof term and an open row cannot carry one. -/
inductive Witness : Status → Type 2 where
  /-- Imported, and already proved in this library. -/
  | importedProof (stmt : Prop) (pf : stmt) : Witness .imported
  /-- Imported standard mathematics the library does not prove: `H` is exactly
      the hypothesis its consumers take as an argument. Asserts nothing. -/
  | carried (H : Prop) : Witness .imported
  /-- Construction axiom: the adopted construction itself. -/
  | adopted {T : Type 1} (val : T) : Witness .constructionAxiom
  /-- Receiver declaration: the data, or the structure of data, a receiver supplies. -/
  | supplied {T : Type 1} (val : T) : Witness .receiverDeclaration
  /-- Derived: a closed proof term. -/
  | derived (stmt : Prop) (pf : stmt) : Witness .derived
  /-- Derived instance: a closed proof term for a named input family. -/
  | inst (stmt : Prop) (pf : stmt) : Witness .derivedInstance
  /-- Derived, but built in a file this one does not import (§30 only). -/
  | elsewhere : Witness .derived
  /-- Conditional: a closed proof term of the statement with its hypotheses. -/
  | conditional (stmt : Prop) (pf : stmt) : Witness .conditional
  /-- Open or downstream: nothing. -/
  | nothing : Witness .openDownstream

namespace Witness

/-- The proposition the row puts on the table. Declared, carried, elsewhere and
    open rows assert nothing. -/
def claim : {s : Status} → Witness s → Prop
  | _, importedProof p _ => p
  | _, carried _ => True
  | _, adopted _ => True
  | _, supplied _ => True
  | _, derived p _ => p
  | _, inst p _ => p
  | _, elsewhere => True
  | _, conditional p _ => p
  | _, nothing => True

/-- Whether the row bears a proof term. -/
def bearsProof : {s : Status} → Witness s → Bool
  | _, importedProof _ _ => true
  | _, derived _ _ => true
  | _, inst _ _ => true
  | _, conditional _ _ => true
  | _, _ => false

/-- **Every row's claim holds**, by the proof term it carries. -/
theorem holds : {s : Status} → (w : Witness s) → w.claim
  | _, importedProof _ h => h
  | _, carried _ => trivial
  | _, adopted _ => trivial
  | _, supplied _ => trivial
  | _, derived _ h => h
  | _, inst _ h => h
  | _, elsewhere => trivial
  | _, conditional _ h => h
  | _, nothing => trivial

/-- An open row is the unique empty witness: it has no content to supply. -/
theorem open_eq_nothing (w : Witness .openDownstream) : w = nothing := by
  cases w; rfl

/-- A conditional row always bears its proof term. -/
theorem conditional_bearsProof (w : Witness .conditional) : w.bearsProof = true := by
  cases w; rfl

/-- A derived row bears a proof term unless it is the `elsewhere` marker. -/
theorem derived_bearsProof (w : Witness .derived) : w.bearsProof = true ∨ w = elsewhere := by
  cases w
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A declared row never bears a proof term: a declaration is not a theorem. -/
theorem declared_not_proof (w : Witness .constructionAxiom) (w' : Witness .receiverDeclaration) :
    w.bearsProof = false ∧ w'.bearsProof = false := by
  cases w; cases w'; exact ⟨rfl, rfl⟩

end Witness

/-- A row of a ledger whose status is fixed by its type. -/
structure Row (s : Status) where
  label : String
  wit : Witness s

/-- A row of the combined ledger. -/
structure Entry where
  label : String
  status : Status
  wit : Witness status

def Row.toEntry {s : Status} (r : Row s) : Entry := ⟨r.label, s, r.wit⟩

/-- A section-range row of Ledger 31.4: the derived family (`status`, `wit`),
    the book's scope column verbatim (`scope`), and the parts of the range that
    the scope column types otherwise (`parts`: imported, derived instance or
    conditional), each with its own status and witness. -/
structure FamilyRow where
  sections : String
  status : Status
  wit : Witness status
  scope : String
  parts : List Entry

def FamilyRow.toEntry (r : FamilyRow) : Entry := ⟨r.sections, r.status, r.wit⟩

open Mat2 Word Frame Pres RatioSpace

/-! ## Ledger 31.2 — Imported and frozen inputs -/

/-- **Ledger 31.2.** Seven imported families. Six are proof terms already in the
    library; the Dedekind–Rademacher identities are carried as the exact
    hypothesis structure §28 takes. -/
def ledger31_2 : List (Row .imported) :=
  [ ⟨"presentations, frames, mediants, positive words, typed actions",
      .importedProof _ (And.intro Frame.walk_append Frame.walk_mid_primitive)⟩,
    ⟨"directional composition, endpoint tension, exact golden element",
      .importedProof _ (And.intro @IPres.otimes_swap Zphi.phi_sq)⟩,
    ⟨"observer-relative encounter Q = M_O⁻¹ M_P",
      .importedProof (∀ MO MP : Mat2, Q MO MP = inv2 MO * MP) (fun _ _ => rfl)⟩,
    ⟨"positive decoding and free-monoid nonreturn",
      .importedProof _ (And.intro @G_inj G_cons_ne_one)⟩,
    ⟨"canonical twelve-class closure character psi12",
      .importedProof _ Word.psi12_append⟩,
    ⟨"central lift distinction Q vs -Q",
      .importedProof _ lift_separates_what_projective_cannot⟩,
    ⟨"Dedekind–Rademacher function and symbol (Def 28.2, Prop 28.3)",
      .carried (RadTransport.RadCocycle ∧ RadTransport.RadConj)⟩ ]

/-! ## Ledger 31.3 — Declared construction and receiver data -/

/-- **Ledger 31.3.** Six declarations, each the object the tree uses. The support law is
    Definition 8.1 (`support`, `axiomSelect`), a definition, so it has no row in Ledger 31.3. -/
def ledger31_3 : List Entry :=
  [ ⟨"Receiver Declaration 15.6: h_Q = 7",
      .receiverDeclaration, .supplied (up Accumulation.hQ)⟩,
    ⟨"observer-adoption socket: singleton return domain and lossless splice",
      .receiverDeclaration, .supplied (@Return.CompatibleDomain, up Return.spliceObs)⟩,
    ⟨"Construction Axiom II.2: every eligible certificate attached, no other",
      .constructionAxiom, .adopted @Face.receivedFaces⟩,
    ⟨"retention declaration Θ",
      .receiverDeclaration, .supplied @Lifecycle.Retention⟩,
    ⟨"global attaching reception Γ",
      .receiverDeclaration, .supplied @Shell.Reception⟩,
    ⟨"Rademacher receiver profile: Φ, Φ mod 24, σ, Ψ, trace",
      .receiverDeclaration,
      .supplied (up (RadTransport.phiRadC, RadTransport.phiRadC24, routeCorrection,
        RadTransport.psiRadC, RadTransport.trace))⟩ ]

/-- Receiver Declaration 15.6 is the number seven, and nothing derives it. -/
theorem hQ_eq_seven : Accumulation.hQ = 7 := rfl

/-! ## Ledger 31.4 — Derived theorem families -/

/-- A derived 31.4 row with its scope column and the parts typed otherwise. -/
def fam (sections : String) (w : Witness .derived) (scope : String)
    (parts : List Entry := []) : FamilyRow :=
  ⟨sections, .derived, w, scope, parts⟩

/-- **Ledger 31.4.** Fifteen section ranges. Each derived witness is a closed
    proof term of a built theorem from that range; `scope` is the book's scope
    column; rows 2–3, 15–17, 24 and 25 carry the imported, derived-instance and
    conditional parts that column names, each with its own proof term. -/
def ledger31_4 : List FamilyRow :=
  [ fam "2–3" (.derived _ (And.intro thm_2_4 thm_3_4)) "derived/imported as labeled"
      [⟨"Prop 3.6 bilateral transport (imported result with constructive application)",
        .imported, .importedProof _ (And.intro prop_3_6 prop_3_6_changes_admission)⟩],
    fam "4–6" (.derived _ @archive_lossless) "derived",
    fam "7–8" (.derived _ support_side_covariant) "derived; support by Definition 8.1",
    fam "9–10" (.derived _ (And.intro statuses_are_independent causalRecord_children_distinct))
      "derived",
    fam "11–14" (.derived _
      (And.intro @Conservation.no_positive_recurrence SideExchange.advanceArchive_mirror_perm))
      "derived; support by Definition 8.1",
    fam "15–17" (.derived _ (And.intro Terminal.termStatus_trichotomy (And.intro LoneSeed.theorem_16_17_LL Tie1613.prop_16_13_tie)))
      "derived, support by Definition 8.1, with the horizon declaration; ensemble transients are derived instances with stated scope"
      [⟨"Prop 16.13 ties before capture: four named seed instances",
        .derivedInstance, .inst _ (And.intro Transient.prop_16_13_i (And.intro Transient.prop_16_13_ii
          (And.intro Transient.prop_16_13_iii Transient.prop_16_13_iv)))⟩],
    fam "18–20" (.derived _ @Snap.snap_isSome_iff) "derived on the singleton return domain; support by Definition 8.1",
    fam "21–22" (.derived _ Face.universal_emission) "derived; support by Definition 8.1; attachment consequences use II.2",
    fam "23" (.derived _ Incidence.lineage_not_closed) "derived from II.2 where attached faces are used",
    fam "24" (.derived _ @Lifecycle.release_deletes_nothing)
      "derived; covariance is conditional on receiver data"
      [⟨"Prop 24.18 covariance of renewal and release, on equivariant receiver data",
        .conditional, .conditional _ @Lifecycle.covariance_conditional⟩],
    fam "25" (.derived _ (And.intro @Shell.one_lineage_fails_shell @Shell.shellIn_recoverable))
      "derived; support by Definition 8.1; shell application is conditional"
      [⟨"Cor 25.11 downstream renewal-shell applicability, on the certificate, D = 12 and a preserving continuation",
        .conditional, .conditional _ (And.intro @Shell.cor_25_11 @Shell.cor_25_11_continuation)⟩],
    fam "26–27" (.derived _ (And.intro Mirror.AR_pow_fib Chamber.ridges_exchanged)) "derived",
    fam "28" (.derived _ RadTransport.transport) "derived from the imported classical identities",
    fam "29" (.derived _ RidgeDefect.thm_29_3_square) "derived",
    -- §30 (derived scope result) is marked `elsewhere` in this row; its proof
    -- term `Obligations.thm_30_3` is carried by `row30` below.
    fam "30" .elsewhere "derived scope result" ]

/-- The parts of Ledger 31.4 that its scope column types other than derived. -/
def scopedParts : List Entry := ledger31_4.flatMap (·.parts)

/-- The §28 row's claim is Theorem 28.5 with the classical identities as an
    explicit antecedent: the carried import of 31.2 enters here and nowhere
    silently. -/
theorem row28_claim :
    (ledger31_4[12]'(by decide)).wit.claim =
      ∀ (_ : RadTransport.RadCocycle) (s : Bool) (v : Word),
        RadTransport.phiRadC (RadTransport.Qs s v) = RadTransport.eps s - bal v := rfl

/-- **Ledger 31.4, the §30 row with its proof term.** Theorem 30.3 is a derived
    scope result, proved by `Obligations.thm_30_3`. -/
def row30 : FamilyRow := fam "30" (.derived _ Obligations.thm_30_3) "derived scope result"

/-- The §30 row's claim is the statement of `Obligations.thm_30_3`. -/
theorem row30_claim :
    row30.wit.claim =
      (Obligations.EngineClauses ∧
        (∀ k : ℤ, ∀ Q : Mat2,
          Obligations.chart k (SideExchange.P * Q * SideExchange.P) = Obligations.chart k Q) ∧
        (∀ k : ℤ, 0 < k → ∀ r : ℕ,
          Obligations.chart k (RidgeDefect.QR (RidgeDefect.rlWord r)) <
            Obligations.chart k (RidgeDefect.QR (RidgeDefect.rlWord (r + 1)))) ∧
        Obligations.chart 1 (Mat2.R * Mat2.L) ≠ Obligations.chart 2 (Mat2.R * Mat2.L)) := rfl

/-- **Ledger 31.4 with every row proved:** `ledger31_4` with its `elsewhere`
    §30 row replaced by `row30`. -/
def ledger31_4_proved : List FamilyRow := ledger31_4.dropLast ++ [row30]

/-- Every row of `ledger31_4_proved` bears a closed proof term, its claim holds,
    and it differs from `ledger31_4` only in the §30 row. -/
theorem ledger31_4_proved_bearsProof :
    ledger31_4_proved.length = 15 ∧
    ledger31_4_proved.all (fun r => r.wit.bearsProof) = true ∧
    (∀ r ∈ ledger31_4_proved, r.wit.claim) ∧
    ledger31_4_proved.map (·.sections) = ledger31_4.map (·.sections) ∧
    ledger31_4_proved.dropLast = ledger31_4.dropLast :=
  ⟨rfl, rfl, fun r _ => r.wit.holds, rfl, rfl⟩

/-! ## Ledger 31.5 — Conditional results -/

/-- **Ledger 31.5.** Nine conditional results, each a proof term whose
    statement carries its domain as hypotheses. -/
def ledger31_5 : List (Row .conditional) :=
  [ ⟨"resolves exactly when terminal support is singleton",
      .conditional _ @Terminal.resolveOcc_iff_singleton⟩,
    ⟨"holonomy is determined only when exactly one lift sheet is coherent",
      .conditional _ Incidence.holSL_tag⟩,
    ⟨"renewal only relative to a receiver reading the same declared identity",
      .conditional _ @Lifecycle.renewal_identity_only⟩,
    ⟨"release on a failed gate; later readability does not readmit",
      .conditional _ Lifecycle.no_readmission⟩,
    ⟨"lifecycle covariance requires equivariant receiver data",
      .conditional _ @Lifecycle.covariance_conditional⟩,
    ⟨"shell input only after an admissible Γ and all five certificate entries pass",
      .conditional _ @Shell.receivedShellInput_iff⟩,
    ⟨"sphere-shell criterion additionally requires total defect twelve",
      .conditional _ @Shell.cor_25_11⟩,
    ⟨"balanced period renews Ψ only where σ also repeats",
      .conditional _ RadTransport.balanced_class_iff⟩,
    ⟨"interpretation only through a verified correspondence map",
      .conditional _ (And.intro @Layer.Correspondence.commutes @Layer.trivialCorrespondence)⟩ ]

/-! ## Ledger 31.6 — Open but nonblocking obligations -/

/-- An open item: a label, and the only witness its status admits. -/
def openItem (label : String) : Row .openDownstream := ⟨label, .nothing⟩

/-- **Ledger 31.6.** Fourteen open items. Typed `Row .openDownstream`, so no
    other status and no content is possible. -/
def ledger31_6 : List (Row .openDownstream) :=
  [ openItem "a theorem uniquely forcing h_Q = 7",
    openItem "classification of resolving cavities under narrower admissibility",
    openItem "additional exact charts for nonpositive encounter comparison",
    openItem "general central-lift selection with no lift field or predicate",
    openItem "general laws for socket release, re-admission and new face attachment",
    openItem "first shell-nucleating multi-cycle question families and receptions",
    openItem "exact crosswalk between [Φ_Rad]_24 and psi12",
    openItem "classification of σ_Rad for all balanced periodic words",
    openItem "a geometric side or crossing interpretation of σ_Rad",
    openItem "an exact-to-field encoding with a commutation or error theorem",
    openItem "joint continuation, exchange, exclusion and transfer laws",
    openItem "native fermion/boson placement after those laws",
    openItem "impedance-to-mass and every dimensionful projection",
    openItem "physical, biological or cosmological identification" ]

/-- The combined ledger, in book order. -/
def combined : List Entry :=
  ledger31_2.map Row.toEntry ++ ledger31_3 ++ ledger31_4.map FamilyRow.toEntry ++
    ledger31_5.map Row.toEntry ++ ledger31_6.map Row.toEntry

/-! ## Theorem 31.7 — Status and dependency closure -/

/-- **Theorem 31.7.** (1) The five ledgers have the book's sizes. (2) Every row's
    claim holds. (3) Every row of 31.4 bears a closed proof term except §30,
    which is built elsewhere. (4) Every conditional row bears its proof term.
    (5) Every open row is the empty witness. (6) No declared row bears a proof
    term: declarations are not converted into theorems. (7) The scope column of
    31.4: exactly rows 2–3, 15–17, 24 and 25 carry parts typed other than
    derived, imported, derived instance, conditional and conditional
    respectively; each part bears a proof term and its claim holds. -/
theorem thm_31_7 :
    (ledger31_2.length = 7 ∧ ledger31_3.length = 6 ∧ ledger31_4.length = 15 ∧
      ledger31_5.length = 9 ∧ ledger31_6.length = 14) ∧
    (∀ e ∈ combined, e.wit.claim) ∧
    ((ledger31_4.filter (fun r => !r.wit.bearsProof)).map (·.sections) = ["30"]) ∧
    (ledger31_4.all (fun r => r.status == .derived) = true) ∧
    (ledger31_5.all (·.wit.bearsProof) = true) ∧
    (∀ r ∈ ledger31_6, r.wit = .nothing) ∧
    (ledger31_3.all (fun e => !e.wit.bearsProof) = true) ∧
    (ledger31_2.map (·.wit.bearsProof) = [true, true, true, true, true, true, false]) ∧
    ((ledger31_4.filter (fun r => !r.parts.isEmpty)).map (fun r => (r.sections, r.parts.map (·.status))) =
      [("2–3", [.imported]), ("15–17", [.derivedInstance]), ("24", [.conditional]),
        ("25", [.conditional])] ∧
      scopedParts.all (·.wit.bearsProof) = true ∧ (∀ e ∈ scopedParts, e.wit.claim)) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun e _ => e.wit.holds, rfl, rfl, rfl,
    fun r _ => r.wit.open_eq_nothing, rfl, rfl, ⟨rfl, rfl, fun e _ => e.wit.holds⟩⟩

/-! ## Boundary Statement 31.8 — The five-way partition -/

/-- The five boxed classes of Boundary Statement 31.8. -/
inductive Class5 where
  | imported
  | declared
  | derived
  | conditional
  | openDownstream
  deriving DecidableEq, Repr

/-- The seven statuses read onto the five classes. -/
def Status.cls : Status → Class5
  | .imported => .imported
  | .constructionAxiom => .declared
  | .receiverDeclaration => .declared
  | .derived => .derived
  | .derivedInstance => .derived
  | .conditional => .conditional
  | .openDownstream => .openDownstream

/-- The status map is surjective onto the five classes. -/
theorem cls_surjective (c : Class5) : ∃ s : Status, s.cls = c := by
  cases c
  · exact ⟨.imported, rfl⟩
  · exact ⟨.constructionAxiom, rfl⟩
  · exact ⟨.derived, rfl⟩
  · exact ⟨.conditional, rfl⟩
  · exact ⟨.openDownstream, rfl⟩

/-- The fibres: declared and derived each merge two statuses, the rest one. -/
theorem cls_fibres :
    allStatuses.map Status.cls =
      [.imported, .declared, .declared, .derived, .derived, .conditional, .openDownstream] := rfl

/-- **Boundary Statement 31.8.** The combined ledger splits into the five classes
    with exactly the book's five ledgers as the parts: 7 imported, 6 declared,
    15 derived, 9 conditional, 14 open, 51 rows, no row in two classes (each row
    has one status, and `cls` is a function). -/
theorem boundary_31_8 :
    combined.length = 51 ∧
    combined.map (·.status.cls) =
      List.replicate 7 .imported ++ List.replicate 6 .declared ++ List.replicate 15 .derived ++
        List.replicate 9 .conditional ++ List.replicate 14 .openDownstream ∧
    (∀ e ∈ combined, ∀ c₁ c₂ : Class5, e.status.cls = c₁ → e.status.cls = c₂ → c₁ = c₂) :=
  ⟨rfl, rfl, fun _ _ _ _ h₁ h₂ => h₁ ▸ h₂⟩

end StatusLedger
end Two
end RatioSpace
