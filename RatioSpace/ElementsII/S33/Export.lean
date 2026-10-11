/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S30.Obligations
import RatioSpace.ElementsII.S31.StatusLedger
import RatioSpace.ElementsII.S32.ExcludedFormulations
import RatioSpace.ElementsII.S16.Capture
import RatioSpace.ElementsII.S16.WordDynamics
import RatioSpace.ElementsII.S16.CaptureWords
import RatioSpace.ElementsII.S16.SeedClassification
import RatioSpace.ElementsII.S15.AxiomPolicy
import RatioSpace.ElementsII.S22.FaceVerification
/-!
  Elements II §33 — Next-paper interface.

  Five items: Definition 33.1, Theorem 33.2, Corollary 33.3, Definition 33.4,
  Boundary Statement 33.5.

  **What is built.**
  * 33.1: `ElemIIOut`, the eight-component packet over the tree's own types:
    the face-bearing state `RecState Op (List FaceRec)` (23.5), the tagged cycle
    outcome `CycleOutcome` (20.3, which carries the certificate `C^cyc` on the
    assimilated branch and the complete report otherwise), the archival face
    family, the retention declaration with the lifecycle ledger and release
    records (24.10–24.12), the recurrence ledger `RecLedger`, the §30 obligation
    family and the §31 status ledger. `ShellIn` (25.2) is not stored a second
    time: `ElemIIOut.shell` computes it from the packet by `Shell.shellIn`, so
    its state and archive *are* the packet's (`rfl`). The recurrence ledger is a
    record whose fields are literally the statements (`type_of%`) of the built
    §§26–29 theorems, and it recovers the left side of Boundary 30.5. Components
    7 and 8 are pinned to `Obligations.obligations` and `StatusLedger.combined`
    by equality fields. "Stable references to source records" is typed: every
    archived face is a member of a list appended to the state's recorded history.
    The components are tied by fields: on the assimilated branch of the cycle
    outcome the face state is `Incidence.recordFace` of the next state (read
    through the packet's map `recOf`, since the cycle's state type is generic)
    with the cycle's ledger at its target (`face_tie`), and every lifecycle event
    and release record names an archived face (`life_in_arch`, `rel_in_arch`).
    `def_33_1` states the ties.
  * 33.1 at Proposition 22.10: `exportLL` and `exportRR`, packets for the two
    face-bearing lone-seed questions with every component computed in the tree
    (`exportLL_packet`, `exportRR_packet`, `certQ_survivor`): the run is the
    book's schedule `AxiomPolicy.axiomPolicy` from the seed carrier and is the
    certified run (`axiomPolicy_XLL7`, `axiomPolicy_XRR7`); the cycle outcome is
    the question's `Cycle.cycle`, assimilated, with `C^cyc` over the question's
    own snap; the archive is the ledger of the packets built at exactly the
    events of Proposition 22.10 items 5 and 6, seven faces at events `1..7`,
    each carrying the certificate.
  * 33.1 at the side-selected roots: `exportSideL` and `exportSideR`, packets
    for `𝒬_ε^L`, `𝒬_ε^R` (Proposition 22.10 items 3 and 4) by the same
    construction (`exportSideL_packet`, `exportSideR_packet`,
    `certQ_survivor_side`). Definition 16.7's side predicate is a schedule:
    `sidePolicyAt` is `RootOrbit.axiomSelectSide` applied at every reached
    carrier, a `Policy` with every `AdvanceData` obligation discharged, and its
    run from the root seed carrier is Theorem 16.8's run
    (`sidePolicyL_XepsSideL7`, `sidePolicyR_XepsSideR7`). Six faces each, at
    events `2..7`.
  * 33.2: each downstream stage's input is a record built from a projection of
    the packet plus that stage's own declared datum (a reception `Γ`, the
    classical cocycle hypothesis, an encoding `E`, a joint-continuation law).
    Sufficiency is by construction (`rfl`) plus what each stage computes: the
    shell certificate factors through the active face map (Theorem 25.10); the
    Rademacher reading `Φ(Q_s(v)) = ε_s − bal v` follows from the packet's
    ledger and the stage's hypothesis; the field and exchange stages receive
    exactly their obligation rows. Applications cannot be formed without a
    passed shell certificate, an admissible reception and an encoding, and no
    application input exists over a one-lineage export under `Γ_id` (25.8).
    Noncircularity cites Theorem 30.3 (the engine clauses hold with no `ProjOb`
    or stage datum in their statements) and Ledger 31.4's §28 row (the classical
    identity enters only as an explicit antecedent).
  * 33.3: `Discharge`, a record of the built theorems for O1–O6, and
    `UniquenessAsBuilt` for the central uniqueness question. The open rows of
    Ledger 31.6 are the empty witness and enter neither record.
  * 33.4: `Stage` in book order with ranks, the obligation rows partitioned
    across the five stages, the typed dependencies respecting the order, and
    the parallel clause: the shell track reads only the active face map, the
    Rademacher track only the carried-history view, and neither takes the
    other's declared datum.
  * 33.5: the packet built from any cycle's data with components 6–8 the built
    objects; the downstream shell handoff passes and fails through declared
    receptions (25.13); nothing is inserted backward: a `ProjOb` carries no map
    (30.1) and no named equality identifies its preimages (32.3); and no stage
    datum changes the packet a stage reads.

  **What is not built.**
  * (Closed 2026-09-14.) Theorem 16.11(4) and Theorem 16.12 items 1 and 2 were
    not in the tree when this file was written; `UniquenessAsBuilt` now carries
    them (`Step5Induction.clauses_1_2`, `clause_4`, `Step5Seed.no_root_of_seed`,
    `Step5Words.theorem_16_12_item1`/`_item2` and their `_governed` forms). They
    ask the run to start where the book's dynamics start (`Rooted`); freshness
    (Lemma 12.1) is then derived (`Step5Induction.run_hfresh`), not assumed.
    Item 3 keeps its archive-invariance hypothesis.
  * Concrete packets exist for the four face-bearing questions of Proposition
    22.10 (`𝒬_ε^L`, `𝒬_ε^R`, `𝒬_LL`, `𝒬_RR`). The unresolved questions (items 1
    and 2) have an empty attached-face family (Corollary 22.9) and no packet here.
  * The retention `Θ` of the concrete packets is supplied, not derived, and
    that is the book's own structure: Ledger 31.3 item 5 lists the retention
    declaration among the "adopted or supplied data rather than derived
    universal laws", and Definition 24.10 calls it "exact receiver data", so
    `ElemIIOut_{𝒬,Θ,n}` is indexed by a declared `Θ`. What is particular here
    is the choice: the packets use one declaration, `retainAll` (every gate
    one, unit packets, no receiver reading); a receiver with another `Θ` gets
    another lifecycle ledger from the same faces. Also fixed here: the lifecycle ledger
    is one entry evaluation per face at stratum `1` and there is no release;
    the operative component of the next state is the terminal carrier, with
    observer adoption carried by the certificate (no carrier-level adoption
    map exists, Definition 20.2 takes it as a parameter); the splice position is
    `0` (the canonical socket declares `splice := id`); the ledger is recorded
    at the question's socket target `seed164Id` with the cycle's resolution
    provenance. The concrete packets are not run through the shell stage here.
  * The parallel clause of 33.4 is about views, not raw storage: the active face
    map is itself computed from the lifecycle ledger (`Shell.activeAt`), so both
    tracks share that source record. "Neither track replaces the other" is
    stated as non-determination both ways (`neither_replaces_33_4`).
  * The stage-to-owner assignment for the recurrence, modular-geometric and
    mass/impedance rows is read from 33.4's prose (number-theoretic development
    and interpretive comparisons to the Rademacher companion; units and scales
    to the field correspondence).

  Choice discipline: no `simp`, `nlinarith` or list-erase lemmas; proofs are
  `rfl`, `decide`, `rw` and the cited theorems.
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace RatioSpace
namespace Two
namespace Export

open Mat2 Word

/-! ## Definition 33.1 — Complete Elements II export -/

/-- **Definition 33.1, component 6.** `𝔑_nat`, the exact recurrence ledger. Each
    field's type is the statement of a built theorem, read off by `type_of%`:
    mirror powers (26.3), chamber ridges and alternation (27.3, 27.4), the
    Rademacher transport with the classical cocycle as antecedent (28.5), the
    opposite routes (28.7), the alternating and side-mirrored scans and the
    elliptic ray orders (§28), the Fibonacci strobe trace and the ridge-defect
    square invariance (29.3, 29.6). -/
structure RecLedger : Prop where
  mirrorR : type_of% @Mirror.AR_pow_fib
  mirrorL : type_of% @Mirror.AL_pow_fib
  ridges : type_of% @Chamber.ridges_exchanged
  alternationR : type_of% @Chamber.alternation_R
  alternationL : type_of% @Chamber.alternation_L
  radTransport : type_of% @RadTransport.transport
  radRoutes : type_of% @RadTransport.opposite_routes_unbounded
  alternatingScan : type_of% @RadTransport.alternating_table
  sideMirrorScan : type_of% @RadTransport.side_mirror
  ellipticScan : type_of% @RadTransport.ray_elliptic_orders
  fibonacciStrobe : type_of% @RidgeDefect.QR_strobe_trace
  ridgeDefect : type_of% @RidgeDefect.thm_29_3_square

/-- The recurrence ledger holds, each field by the cited theorem. -/
theorem recLedger : RecLedger :=
  ⟨@Mirror.AR_pow_fib, @Mirror.AL_pow_fib, @Chamber.ridges_exchanged, @Chamber.alternation_R,
   @Chamber.alternation_L, @RadTransport.transport, @RadTransport.opposite_routes_unbounded,
   @RadTransport.alternating_table, @RadTransport.side_mirror, @RadTransport.ray_elliptic_orders,
   @RidgeDefect.QR_strobe_trace, @RidgeDefect.thm_29_3_square⟩

/-- The ledger recovers the left side of Boundary Statement 30.5: every named
    recurrence result is one of its fields. -/
theorem RecLedger.results (L : RecLedger) : ∀ r : Obligations.RecurrenceResult, r.statement
  | .mirrorFibonacci => L.mirrorR
  | .chamberAlternation => L.alternationR
  | .rademacherOppositeRoutes => L.radRoutes
  | .ridgeSquareInvariance => L.ridgeDefect

/-- **Definition 33.1.** `ElemIIOut_{𝒬,Θ,n}`.

    1. `faceState`: `S^face_{τ+1}`, the state with the incidence ledger appended
       (Definition 23.5, `Incidence.recordFace`);
    2. `cycle`: the terminal, snap and adoption record, as the tagged outcome of
       Definition 20.3 (certificate on the assimilated branch, complete report
       on the other two);
    3. `archFaces`: `𝔏^arch_{≤n}`, the archival face family, whose incidence is
       computed by `Incidence.incV`/`incE`;
    4. `theta`, `lifeLedger`, `releases`: `𝔇^face_{Θ,≤n}`, the retention
       declaration, the renewal/retention ledger and the release records;
    5. `ShellIn_{Θ,n}`: computed, `ElemIIOut.shell`, from `n`, the entry strata
       `entry` and the retention compatibility `compat`;
    6. `recurrence`: `𝔑_nat`;
    7. `obligations`: `𝔓_ob`, pinned to Definition 30.1's table;
    8. `status`: `𝔗_stat`, pinned to the combined §31 ledger.

    `arch_recorded` is the stable-reference clause: every archived face record
    is a member of a face ledger appended to the state's recorded history.

    **The components are tied.**
    * `face_tie` (item 1): on the assimilated branch of `cycle`, with next state
      `x`, `faceState` is `Incidence.recordFace (recOf x) target ledger`, the
      face-recorded state of that next state with this cycle's incidence ledger
      `ledger` appended at `target` (Definition 23.5). The cycle's state type
      `σ` is generic in the tree (`Cycle.lean`'s modelling decision), so the map
      `recOf : σ → RecState …` reading a cycle state as the state the append
      sees is a component of the packet; the tie is only as strong as that map,
      and it constrains nothing on the empty and unresolved branches (no face
      attaches there, Corollary 22.9).
    * `life_in_arch`, `rel_in_arch` (item 4 over item 3): every lifecycle event,
      by its key and by its own face field, and every release record names a
      face identifier of `archFaces`. -/
structure ElemIIOut (Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St : Type) (h : ℕ) : Type 2 where
  faceState : Face.RecState Op (List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew))
  cycle : Cycle.CycleOutcome σ RawAux EvalAux h
  recOf : σ → Face.RecState Op (List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew))
  target : QuestionId
  ledger : List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew)
  face_tie : ∀ x k, cycle = .assimilated x k → faceState = Incidence.recordFace (recOf x) target ledger
  archFaces : List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew)
  arch_recorded : ∀ r ∈ archFaces, ∃ p ∈ faceState.hist, r ∈ p.2
  theta : Lifecycle.Retention P Y Ph St
  lifeLedger : Lifecycle.LifeLedger P Y
  life_in_arch : ∀ ev ∈ lifeLedger, ev.1.1 ∈ archFaces.map (·.id) ∧ ev.2.fid ∈ archFaces.map (·.id)
  releases : List (Lifecycle.ReleaseRec P)
  rel_in_arch : ∀ r ∈ releases, r.fid ∈ archFaces.map (·.id)
  n : ℕ
  entry : Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew → ℕ
  compat : Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool
  recurrence : RecLedger
  obligations : List Obligations.ProjOb
  obligations_eq : obligations = Obligations.obligations
  status : List StatusLedger.Entry
  status_eq : status = StatusLedger.combined

namespace ElemIIOut

variable {Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St : Type} {h : ℕ}
variable (X : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)

/-- The archive of Definition 24.12, assembled from components 3 and 4. -/
def archive : Lifecycle.Archive (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew) P Y :=
  ⟨X.archFaces, X.lifeLedger, X.releases⟩

/-- **Definition 33.1, component 5.** `ShellIn_{Θ,n}` of Definition 25.2, computed
    from the packet by the export map itself. -/
def shell : Shell.ShellIn (Face.RecState Op (List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    Aux Cert RawAux EvalAux Prov Renew P Y Ph St h :=
  Shell.shellIn X.faceState X.theta X.archive X.entry X.compat X.n

theorem shell_faceState : X.shell.faceState = X.faceState := rfl
theorem shell_theta : X.shell.theta = X.theta := rfl
theorem shell_archive : X.shell.archive = X.archive := rfl
theorem archive_components :
    X.archive.faces = X.archFaces ∧ X.archive.lifeLedger = X.lifeLedger ∧
      X.archive.releases = X.releases := ⟨rfl, rfl, rfl⟩

theorem obligations_length : X.obligations.length = 9 := by
  rw [X.obligations_eq]; rfl

theorem status_length : X.status.length = 51 := by
  rw [X.status_eq]; exact StatusLedger.boundary_31_8.1

end ElemIIOut

section Def331
variable {Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St : Type} {h : ℕ}

/-- **Definition 33.1, stable references.** The shell interface carries the
    packet's own state and archive unchanged; its archival family is the
    stratum-`n` restriction of component 3 and its active map a sublist of that;
    active incidence is the incidence of the active map (25.1); every archived
    face is referenced in the recorded state history; components 7 and 8 are the
    §30 and §31 families; component 6 recovers every recurrence result of
    Boundary 30.5; on the assimilated branch with next state `x` the face state
    is `recordFace (recOf x)`, the face-recorded state of the next state read
    through the packet's map `recOf`, whose last history entry is the packet's
    `ledger` at the packet's `target` (in a general packet `recOf`, `target` and
    `ledger` are fields; the concrete packets below fix them to the question's
    own); and every lifecycle event and release record names an
    archived face. The packet is an interface, not a quotient. -/
theorem def_33_1 (X : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (hnd : (X.archFaces.map (·.id)).Nodup) :
    X.shell.faceState = X.faceState ∧ X.shell.archive = X.archive ∧
    X.shell.arch = Shell.archAt X.archFaces X.entry X.n ∧
    X.shell.actMap.Sublist X.shell.arch ∧ X.shell.arch.Sublist X.archFaces ∧
    (∀ v, X.shell.incVAct v = Incidence.incV X.shell.actMap v) ∧
    (∀ u, X.shell.incEAct u = Incidence.incE X.shell.actMap u) ∧
    (∀ r ∈ X.archFaces, ∃ p ∈ X.faceState.hist, r ∈ p.2) ∧
    X.obligations = Obligations.obligations ∧ X.status = StatusLedger.combined ∧
    (∀ r : Obligations.RecurrenceResult, r.statement) ∧
    (∀ x k, X.cycle = .assimilated x k →
      X.faceState = Incidence.recordFace (X.recOf x) X.target X.ledger ∧
      X.faceState.op = (X.recOf x).op ∧
      X.faceState.hist = (X.recOf x).hist ++ [(X.target, X.ledger)]) ∧
    (∀ ev ∈ X.lifeLedger, ev.1.1 ∈ X.archFaces.map (·.id) ∧ ev.2.fid ∈ X.archFaces.map (·.id)) ∧
    (∀ r ∈ X.releases, r.fid ∈ X.archFaces.map (·.id)) :=
  ⟨rfl, rfl, rfl, List.filter_sublist, List.filter_sublist,
   fun v => (Shell.active_incidence X.archive X.entry X.compat X.n hnd v ⟨.raw, v, v⟩).1,
   fun u => (Shell.active_incidence X.archive X.entry X.compat X.n hnd ⟨0, 0, 0, []⟩ u).2,
   X.arch_recorded, X.obligations_eq, X.status_eq, X.recurrence.results,
   fun x k hc => by
     have he := X.face_tie x k hc
     refine ⟨he, ?_, ?_⟩ <;> rw [he] <;> rfl,
   X.life_in_arch, X.rel_in_arch⟩

/-- The packet assembled from one cycle's data. Components 6–8 are not inputs:
    they are the built recurrence ledger, obligation table and status ledger.
    The archival family is every face ledger the state has recorded. The ties
    are hypotheses: on the assimilated branch `S` is the next state's
    face-recorded state (`hS`), and the lifecycle ledger and release records
    name only recorded faces (`hD`, `hrel`). -/
def ofState (S : Face.RecState Op (List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (c : Cycle.CycleOutcome σ RawAux EvalAux h) (Θ : Lifecycle.Retention P Y Ph St)
    (D : Lifecycle.LifeLedger P Y) (rel : List (Lifecycle.ReleaseRec P)) (n : ℕ)
    (entry : Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew → ℕ)
    (compat : Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool)
    (recOf : σ → Face.RecState Op (List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (t : QuestionId) (L : List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hS : ∀ x k, c = .assimilated x k → S = Incidence.recordFace (recOf x) t L)
    (hD : ∀ ev ∈ D, ev.1.1 ∈ (S.hist.flatMap Prod.snd).map (·.id) ∧
      ev.2.fid ∈ (S.hist.flatMap Prod.snd).map (·.id))
    (hrel : ∀ r ∈ rel, r.fid ∈ (S.hist.flatMap Prod.snd).map (·.id)) :
    ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h where
  faceState := S
  cycle := c
  recOf := recOf
  target := t
  ledger := L
  face_tie := hS
  archFaces := S.hist.flatMap Prod.snd
  arch_recorded := fun _ hr => List.mem_flatMap.mp hr
  theta := Θ
  lifeLedger := D
  life_in_arch := hD
  releases := rel
  rel_in_arch := hrel
  n := n
  entry := entry
  compat := compat
  recurrence := recLedger
  obligations := Obligations.obligations
  obligations_eq := rfl
  status := StatusLedger.combined
  status_eq := rfl

end Def331

/-! ## Theorem 33.2 — Sufficiency and noncircularity of the downstream interface -/

/-- The five declared next stages of Theorem 33.2, in the order Definition 33.4
    recommends. -/
inductive Stage where
  | shellTheorem
  | rademacher
  | fieldCorrespondence
  | exchange
  | applications
  deriving DecidableEq, Repr

/-- The §30 owners each stage takes up. The three companion rows (class-renewing
    periods, geodesic reading of `σ_Rad`) go with the Rademacher companion's
    "full number-theoretic development and interpretive comparisons"; the
    mass/impedance row goes with the field correspondence's "units and physical
    scales" (33.4). -/
def Stage.owners : Stage → List Obligations.Owner
  | .shellTheorem => [.globalRenewalShell]
  | .rademacher => [.rademacherCompanion, .recurrenceProgram, .modularGeometricCompanion]
  | .fieldCorrespondence => [.substrateToField, .massImpedanceProjection]
  | .exchange => [.fermionBosonProgram]
  | .applications => [.applicationPapers]

/-- The obligation rows a stage receives. -/
def rowsFor (s : Stage) (obs : List Obligations.ProjOb) : List Obligations.ProjOb :=
  obs.filter fun o => decide (o.owner ∈ s.owners)

section Stages
variable {Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St : Type} {h : ℕ}

/-- **Theorem 33.2(1).** Input of the Global Renewal-Shell Theorem: `ShellIn_{Θ,n}`
    (active incidence, and through `FaceRec` the orientation, lift and holonomy
    records) and a global attaching reception `Γ`, which the stage declares and
    which is admissible (Definition 25.4) on the prequotient faces of the active
    map. -/
structure ShellStageIn (Op Aux Cert RawAux EvalAux Prov Renew P Y Ph St : Type) (h : ℕ) (V E F : Type)
    [DecidableEq V] [DecidableEq E] [DecidableEq F] where
  shell : Shell.ShellIn (Face.RecState Op (List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    Aux Cert RawAux EvalAux Prov Renew P Y Ph St h
  gamma : Shell.Reception QuestionId Incidence.OEdge Incidence.FaceId V E F
  admissible : Shell.Admissible gamma Shell.oedges (shell.actMap.map Shell.FaceRec.pre)

/-- The received complex: `Γ` applied to the prequotient faces of the active map,
    each retaining its whole record as its source fibre. -/
def ShellStageIn.complex {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F] (I : ShellStageIn Op Aux Cert RawAux EvalAux Prov Renew P Y Ph St h V E F) :
    Shell.Cx V E F :=
  I.gamma.complex (I.shell.actMap.map Shell.FaceRec.pre)

/-- The finite shell certificate, with the active records as source. -/
def ShellStageIn.cert {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F]
    (I : ShellStageIn Op Aux Cert RawAux EvalAux Prov Renew P Y Ph St h V E F) :
    Shell.ShellCert V F (List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew)) :=
  I.complex.cert I.shell.actMap

/-- The shell stage's input: the packet's `ShellIn` and the stage's admissible `Γ`. -/
def shellStage {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F] (X : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (Γ : Shell.Reception QuestionId Incidence.OEdge Incidence.FaceId V E F)
    (hΓ : Shell.Admissible Γ Shell.oedges (X.shell.actMap.map Shell.FaceRec.pre)) :
    ShellStageIn Op Aux Cert RawAux EvalAux Prov Renew P Y Ph St h V E F :=
  ⟨X.shell, Γ, hΓ⟩

/-- **Theorem 33.2(2).** Input of the Rademacher retention companion: the
    receiver-relative carried history (lifecycle ledger with its transported
    packets, release records, archive strata, export stratum), the recurrence
    ledger, and the classical Dedekind–Rademacher cocycle, which the stage
    declares (Ledger 31.2, row 7). -/
structure RadStageIn (P Y : Type) where
  lifeLedger : Lifecycle.LifeLedger P Y
  releases : List (Lifecycle.ReleaseRec P)
  strata : List ℕ
  n : ℕ
  recurrence : RecLedger
  cocycle : RadTransport.RadCocycle

def radStage (X : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (H : RadTransport.RadCocycle) : RadStageIn P Y :=
  ⟨X.lifeLedger, X.releases, X.archFaces.map X.entry, X.n, X.recurrence, H⟩

/-- The Rademacher reading `(Φ, σ, Ψ)` of the relative matrix `Q_s(v)` of a
    sibling emission `s` continued along `v`. -/
def RadStageIn.reading (_I : RadStageIn P Y) (s : Bool) (v : Word) : ℤ × ℤ × ℤ :=
  RadTransport.receiver (RadTransport.Qs s v)

/-- **Theorem 33.2(3).** Input of the Substrate-to-Field Correspondence: the
    exact update, the chamber recurrence, the lifecycle coordinates, the shell
    interface, the distinctions its encoding must preserve or project away (its
    obligation rows, each with its exact source column), and the encoding `E`,
    which the stage declares and Elements II does not construct. -/
structure FieldStageIn (Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St : Type) (h : ℕ)
    (S T : Type) (stepS : S → S) (stepT : T → T) where
  update : Cycle.CycleOutcome σ RawAux EvalAux h
  recurrence : RecLedger
  lifeLedger : Lifecycle.LifeLedger P Y
  shell : Shell.ShellIn (Face.RecState Op (List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    Aux Cert RawAux EvalAux Prov Renew P Y Ph St h
  distinctions : List Obligations.ProjOb
  encoding : Obligations.Correspondence S T stepS stepT

def fieldStage {S T : Type} {stepS : S → S} {stepT : T → T}
    (X : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (C : Obligations.Correspondence S T stepS stepT) :
    FieldStageIn Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h S T stepS stepT :=
  ⟨X.cycle, X.recurrence, X.lifeLedger, X.shell, rowsFor .fieldCorrespondence X.obligations, C⟩

/-- **Theorem 33.2(4).** Input of the renewal/exchange and fermion/boson program:
    occurrence identities with selected and refused alternatives (the cycle
    outcome), the face records (hand, parity, lift, holonomy, renewal and release
    fields), the lifecycle ledger (renewal class), the still-open
    joint-continuation rows, and the stage's declared law. -/
structure ExchangeStageIn (σ Aux Cert RawAux EvalAux Prov Renew P Y : Type) (h : ℕ) (Law : Type) where
  update : Cycle.CycleOutcome σ RawAux EvalAux h
  faces : List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew)
  lifeLedger : Lifecycle.LifeLedger P Y
  openRows : List Obligations.ProjOb
  law : Law

def exchangeStage {Law : Type} (X : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h) (law : Law) :
    ExchangeStageIn σ Aux Cert RawAux EvalAux Prov Renew P Y h Law :=
  ⟨X.cycle, X.archFaces, X.lifeLedger, rowsFor .exchange X.obligations, law⟩

/-- **Theorem 33.2(5).** Input of an application paper: only a construction that
    has passed its exact substrate certificate (the reception is admissible on
    the source fibres, carried by the shell-stage input, `AppStageIn.substrate`),
    its shell certificate (all five entries one) and its projection certificate
    (an explicit encoding with its commutation proof). -/
structure AppStageIn (Op Aux Cert RawAux EvalAux Prov Renew P Y Ph St : Type) (h : ℕ) (V E F : Type)
    [DecidableEq V] [DecidableEq E] [DecidableEq F] (S T : Type) (stepS : S → S) (stepT : T → T) where
  stage : ShellStageIn Op Aux Cert RawAux EvalAux Prov Renew P Y Ph St h V E F
  shellPassed : stage.complex.ClosedShellInput
  encoding : Obligations.Correspondence S T stepS stepT
  openRows : List Obligations.ProjOb

/-- An application input's reception is admissible on the source fibres: the
    substrate certificate is the shell-stage input's own. -/
theorem AppStageIn.substrate {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F]
    {S T : Type} {stepS : S → S} {stepT : T → T}
    (I : AppStageIn Op Aux Cert RawAux EvalAux Prov Renew P Y Ph St h V E F S T stepS stepT) :
    Shell.Admissible I.stage.gamma Shell.oedges (I.stage.shell.actMap.map Shell.FaceRec.pre) :=
  I.stage.admissible

/-- An application input carries a well-typed input to the Global Renewal-Shell
    Theorem: the application stage consumes the shell stage's output. -/
def AppStageIn.toShellInput {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F]
    {S T : Type} {stepS : S → S} {stepT : T → T}
    (I : AppStageIn Op Aux Cert RawAux EvalAux Prov Renew P Y Ph St h V E F S T stepS stepT) :
    Shell.ShellInput V E F :=
  ⟨I.stage.complex, I.shellPassed⟩

/-- **Theorem 33.2(1), what the shell stage computes.** Its input is the packet's
    `ShellIn` and its own `Γ`; its certificate is a function of the active face
    map and `Γ` alone (Theorem 25.10), so two packets with the same active map
    hand it the same certificate; and the active records are retained whole as
    the received source family. -/
theorem thm_33_2_shell {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F]
    (X X' : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (Γ : Shell.Reception QuestionId Incidence.OEdge Incidence.FaceId V E F)
    (hΓ : Shell.Admissible Γ Shell.oedges (X.shell.actMap.map Shell.FaceRec.pre))
    (hΓ' : Shell.Admissible Γ Shell.oedges (X'.shell.actMap.map Shell.FaceRec.pre))
    (hact : X.shell.actMap = X'.shell.actMap) :
    (shellStage X Γ hΓ).shell = X.shell ∧ (shellStage X Γ hΓ).gamma = Γ ∧
    (shellStage X Γ hΓ).cert = (shellStage X' Γ hΓ').cert ∧
    (X.shell.actMap.map Shell.FaceRec.pre).map Shell.PFace.record = X.shell.actMap ∧
    (shellStage X Γ hΓ).complex.faces = X.shell.actMap.map (Γ.face ∘ Shell.FaceRec.pre) := by
  obtain ⟨-, hrec, hfaces⟩ := Shell.handoff_complete X.shell X'.shell hact Γ ()
  refine ⟨rfl, rfl, ?_, hrec, hfaces⟩
  change (Γ.complex (X.shell.actMap.map Shell.FaceRec.pre)).cert X.shell.actMap =
    (Γ.complex (X'.shell.actMap.map Shell.FaceRec.pre)).cert X'.shell.actMap
  rw [hact]

/-- **Theorem 33.2(2), what the Rademacher stage computes.** Its history and
    strata are the packet's; from the packet's recurrence ledger and its own
    cocycle hypothesis it reads `Φ(Q_s(v)) = ε_s − bal v` on every sibling
    emission and continuation, and the side mirror negates `Φ` and `Ψ`. -/
theorem thm_33_2_rademacher (X : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (H : RadTransport.RadCocycle) :
    (radStage X H).lifeLedger = X.lifeLedger ∧ (radStage X H).releases = X.releases ∧
    (radStage X H).strata = X.archFaces.map X.entry ∧
    (∀ s v, RadTransport.phiRadC (RadTransport.Qs s v) = RadTransport.eps s - bal v) ∧
    (∀ v, ((radStage X H).reading false (Word.shadow v)).1 =
      - ((radStage X H).reading true v).1) :=
  ⟨rfl, rfl, rfl, fun s v => (radStage X H).recurrence.radTransport (radStage X H).cocycle s v,
   fun v => ((radStage X H).recurrence.sideMirrorScan (radStage X H).cocycle v).1⟩

/-- **Theorem 33.2(3), what the field stage receives.** The packet's update,
    shell interface and lifecycle ledger, its own encoding, and exactly three
    obligation rows: the numerical continuum state, the chamber potential and the
    impedance/mass chart, with their exact source columns. -/
theorem thm_33_2_field {S T : Type} {stepS : S → S} {stepT : T → T}
    (X : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (C : Obligations.Correspondence S T stepS stepT) :
    (fieldStage X C).shell = X.shell ∧ (fieldStage X C).lifeLedger = X.lifeLedger ∧
    (fieldStage X C).encoding = C ∧
    (fieldStage X C).distinctions.map (·.target) =
      [.numericalContinuumState, .chamberPotential, .impedanceMassChart] ∧
    (fieldStage X C).distinctions.map (·.source) =
      [[.archiveAge, .winding, .lift, .trace, .renewal, .ridgeDefect],
       [.chamberPair, .parityExchange], [.hyperbolicRelMatrix]] := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩ <;>
  · change (rowsFor .fieldCorrespondence X.obligations).map _ = _
    rw [X.obligations_eq]; rfl

/-- **Theorem 33.2(4), what the exchange stage receives.** The packet's cycle
    outcome, face records and lifecycle ledger, its own law, and the one
    exchange row, whose missing constructions are the joint-continuation and
    exchange laws. -/
theorem thm_33_2_exchange {Law : Type} (X : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (law : Law) :
    (exchangeStage X law).faces = X.archFaces ∧ (exchangeStage X law).law = law ∧
    (exchangeStage X law).openRows.map (·.missing) = [[.jointContinuationLaw, .exchangeLaw]] ∧
    (exchangeStage X law).openRows.map (·.source) =
      [[.retainedAlternatives, .jointTrails, .lift, .renewalClass]] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;>
  · change (rowsFor .exchange X.obligations).map _ = _
    rw [X.obligations_eq]; rfl

/-- **Theorem 33.2(5), exactly.** No application input exists over a packet
    whose active family is a nonempty one-lineage ledger read through `Γ_id`:
    Theorem 25.8 refutes the shell certificate the input would have to carry. -/
theorem thm_33_2_applications {S T : Type} {stepS : S → S} {stepT : T → T}
    (X : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h) (i : QuestionId)
    (hL : ∀ r ∈ X.shell.actMap, Shell.LineShaped i r) (hnd : (X.shell.actMap.map Shell.evJ).Nodup)
    (hne : X.shell.actMap ≠ [])
    (I : AppStageIn Op Aux Cert RawAux EvalAux Prov Renew P Y Ph St h QuestionId Incidence.UEdge Incidence.FaceId
      S T stepS stepT)
    (hI : I.stage = shellStage X (Shell.Gid (X.shell.actMap.map Shell.FaceRec.pre))
      (Shell.gid_lineage_admissible i X.shell.actMap hL hnd)) : False := by
  have hfail := (Shell.one_lineage_fails_shell i X.shell.actMap hL hnd hne).2.2.2.1
  rw [Shell.recvId_eq] at hfail
  have hp := I.shellPassed
  rw [hI] at hp
  exact hfail hp

/-- **Theorem 33.2, noncircularity.** The engine clauses (one-tick map, horizon,
    terminal trichotomy and dispatch, snap and adoption, sibling emission,
    renewal and release, export, mirror, chamber, Rademacher routes, ridge)
    hold as stated, with no `ProjOb`, reception, encoding or law in any
    statement (Theorem 30.3, compiled before any stage input existed); and the
    classical cocycle, the Rademacher stage's declared datum, enters Ledger
    31.4's §28 row only as an explicit antecedent. -/
theorem thm_33_2_noncircular :
    Obligations.EngineClauses ∧
    (StatusLedger.ledger31_4[12]'(by decide)).wit.claim =
      ∀ (_ : RadTransport.RadCocycle) (s : Bool) (v : Word),
        RadTransport.phiRadC (RadTransport.Qs s v) = RadTransport.eps s - bal v :=
  ⟨Obligations.thm_30_3.1, StatusLedger.row28_claim⟩

/-- **Theorem 33.2, no feedback.** Whatever datum a stage declares, the packet
    projection it receives is the same: no stage datum reaches back into the
    packet. -/
theorem stage_data_do_not_feed_back {V E F S T S' T' Law : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F]
    {stepS : S → S} {stepT : T → T} {stepS' : S' → S'} {stepT' : T' → T'}
    (X : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (Γ Γ' : Shell.Reception QuestionId Incidence.OEdge Incidence.FaceId V E F)
    (hΓ : Shell.Admissible Γ Shell.oedges (X.shell.actMap.map Shell.FaceRec.pre))
    (hΓ' : Shell.Admissible Γ' Shell.oedges (X.shell.actMap.map Shell.FaceRec.pre))
    (H H' : RadTransport.RadCocycle)
    (C : Obligations.Correspondence S T stepS stepT) (C' : Obligations.Correspondence S' T' stepS' stepT')
    (law law' : Law) :
    (shellStage X Γ hΓ).shell = (shellStage X Γ' hΓ').shell ∧
    radStage X H = radStage X H' ∧
    (fieldStage X C).shell = (fieldStage X C').shell ∧
    (fieldStage X C).distinctions = (fieldStage X C').distinctions ∧
    (fieldStage X C).update = (fieldStage X C').update ∧
    (exchangeStage X law).faces = (exchangeStage X law').faces ∧
    (exchangeStage X law).openRows = (exchangeStage X law').openRows :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Stages

/-! ## Corollary 33.3 — Completion at the declared Elements II scope -/

/-- **Corollary 33.3, the six obligations of Elements I §17.** Each field's type
    is the statement of a built theorem.

    * O1, the one-tick map and its retained invariants: the ledger is a
      prefix across the advance (Corollary 12.8), no nonempty positive
      continuation returns (§14), the archive update is side-exchange covariant
      (13.3). The support selector is Definition 8.1.
    * O2, the observer-local operand and the tension convention: the local word
      of Definition 3.1 is prefix invariant (3.4), Definition 7.3's tension is
      Elements I's `T_end` by `rfl`, and it is side invariant (7.8).
    * O3, accumulation, tick-seven closure and the tie: the sevenfold carrier
      (15.7), Theorem 16.2, Theorems 16.8 and 16.17 on both sides, Theorem
      16.12 item 3, and the terminal trichotomy of Definition 17.1 (17.3).
    * O4, return assimilation: Definition 19.5's four assignments with 19.6,
      the dispatch (20.4), the replacement domain (20.5), evidence (20.6).
    * O5, temporal face selection: universal emission (22.7), Proposition 22.10
      on the root, both side-selected roots and both lone seeds, and one lineage
      supplies incidence one (§23).
    * O6, mirror advances and chambers: Theorem 26.3 on both hands, Theorem
      27.3's ridge exchange, Corollary 27.4 on both sides. -/
structure Discharge : Prop where
  o1_tick : type_of% @Advance.advanceCarrier_ledger_prefix
  o1_noReturn : type_of% @Conservation.no_positive_recurrence
  o1_covariance : type_of% @SideExchange.advanceArchive_mirror_perm
  o2_operand : type_of% @thm_3_4_localWord
  o2_tension : type_of% @tEnd_eq_Tend
  o2_sideInvariant : type_of% @tEnd_side_invariant
  o3_horizon : type_of% @Accumulation.sevenfold_terminal_carrier
  o3_obstruction_16_2 : type_of% @SideExchange.iterated_parity_obstruction
  o3_root_16_8_L : type_of% @RootOrbit.theorem_16_8_L
  o3_root_16_8_R : type_of% @RootOrbit.theorem_16_8_R
  o3_lone_16_17_LL : type_of% @LoneSeed.theorem_16_17_LL
  o3_lone_16_17_RR : type_of% @LoneSeed.theorem_16_17_RR
  o3_capture_16_12_item3 : type_of% @Capture.theorem_16_12_item3
  o3_status_17 : type_of% @Terminal.termStatus_trichotomy
  o4_adoption_19_5 : type_of% @Return.adoption_state_consistent
  o4_dispatch_20_4 : type_of% @Cycle.cycle_dispatch_total
  o4_replacement_20_5 : type_of% @Cycle.observer_replaced_iff_singleton
  o4_evidence_20_6 : type_of% @Cycle.cycle_carries_evidence
  o5_emission_22_7 : type_of% @Face.universal_emission
  o5_root_22_10 : type_of% @FaceRegression.prop_22_10_root_none
  o5_sideL_22_10 : type_of% @FaceRegression.prop_22_10_sideL
  o5_sideR_22_10 : type_of% @FaceRegression.prop_22_10_sideR
  o5_LL_22_10 : type_of% @FaceRegression.prop_22_10_LL
  o5_RR_22_10 : type_of% @FaceRegression.prop_22_10_RR
  o5_incidence_23 : type_of% @Incidence.lineage_not_closed
  o6_mirrorR : type_of% @Mirror.AR_pow_fib
  o6_mirrorL : type_of% @Mirror.AL_pow_fib
  o6_ridges : type_of% @Chamber.ridges_exchanged
  o6_alternationR : type_of% @Chamber.alternation_R
  o6_alternationL : type_of% @Chamber.alternation_L

theorem discharge : Discharge :=
  ⟨@Advance.advanceCarrier_ledger_prefix, @Conservation.no_positive_recurrence,
   @SideExchange.advanceArchive_mirror_perm, @thm_3_4_localWord, @tEnd_eq_Tend, @tEnd_side_invariant,
   @Accumulation.sevenfold_terminal_carrier, @SideExchange.iterated_parity_obstruction,
   @RootOrbit.theorem_16_8_L, @RootOrbit.theorem_16_8_R, @LoneSeed.theorem_16_17_LL,
   @LoneSeed.theorem_16_17_RR, @Capture.theorem_16_12_item3, @Terminal.termStatus_trichotomy,
   @Return.adoption_state_consistent, @Cycle.cycle_dispatch_total, @Cycle.observer_replaced_iff_singleton,
   @Cycle.cycle_carries_evidence, @Face.universal_emission, @FaceRegression.prop_22_10_root_none,
   @FaceRegression.prop_22_10_sideL, @FaceRegression.prop_22_10_sideR, @FaceRegression.prop_22_10_LL,
   @FaceRegression.prop_22_10_RR, @Incidence.lineage_not_closed, @Mirror.AR_pow_fib, @Mirror.AL_pow_fib,
   @Chamber.ridges_exchanged, @Chamber.alternation_R, @Chamber.alternation_L⟩

/-- **Corollary 33.3, the central uniqueness question, as built.** The book
    answers it by four theorems. What the tree carries:

    * the permanent side-symmetric obstruction, Theorem 16.2, in full;
    * the closed named instances, Theorems 16.8 and 16.17, on both sides;
    * for lone-seed questions in general, Theorem 16.11: the forms and the
      bound `|S_j| ∈ {1, 2}` at every tick, the parity criterion `|S_j| = 1`
      iff `j ≡ n_j (mod 2)`, and root pairs only for the seed `ε`;
    * for initial ensembles, Theorem 16.12: capture into the lone-seed regime
      from a singleton or a sibling pair at any tick (items 1 and 2, with the
      bound carried over), and item 3 twice: over a side-robust policy with an
      archive-invariance hypothesis the book does not name
      (`Capture.theorem_16_12_item3`), and in the book's form on a rooted run
      at `ε`, with neither hypothesis (`CaptureWords.theorem_16_12_item3`).

    Theorems 16.11 and 16.12 items 1–2 ask only that each run start where the
    book's dynamics start (`Step5Induction.Rooted`; a lone seed is rooted);
    identifier freshness (Lemma 12.1) is derived along the run. -/
structure UniquenessAsBuilt : Prop where
  obstruction : type_of% @SideExchange.iterated_parity_obstruction
  rootL : type_of% @RootOrbit.theorem_16_8_L
  rootR : type_of% @RootOrbit.theorem_16_8_R
  loneLL : type_of% @LoneSeed.theorem_16_17_LL
  loneRR : type_of% @LoneSeed.theorem_16_17_RR
  ensembleItem3 : type_of% @Capture.theorem_16_12_item3
  loneSeedForms : type_of% @Step5Induction.clauses_1_2
  loneSeedBeat : type_of% @Step5Induction.clause_4
  loneSeedRoot : type_of% @Step5Seed.no_root_of_seed
  ensembleItem1 : type_of% @Step5Words.theorem_16_12_item1
  ensembleItem2 : type_of% @Step5Words.theorem_16_12_item2
  ensembleItem1Bound : type_of% @Step5Words.theorem_16_12_item1_governed
  ensembleItem2Bound : type_of% @Step5Words.theorem_16_12_item2_governed
  ensembleItem3Book : type_of% @CaptureWords.theorem_16_12_item3

/-- **Corollary 33.3.** The six obligations are discharged by built theorems; the
    uniqueness question is answered as far as `UniquenessAsBuilt` records;
    Definition 8.1 is a definition, so Ledger 31.3 has six declared rows; and the fourteen open rows of Ledger 31.6 are the empty witness, so
    they are no premise of either record and do not make the construction
    incomplete. -/
theorem cor_33_3 :
    Discharge ∧ UniquenessAsBuilt ∧
    StatusLedger.ledger31_3.length = 6 ∧
    StatusLedger.ledger31_6.length = 14 ∧
    (∀ r ∈ StatusLedger.ledger31_6, r.wit = .nothing) :=
  ⟨discharge,
   ⟨@SideExchange.iterated_parity_obstruction, @RootOrbit.theorem_16_8_L, @RootOrbit.theorem_16_8_R,
    @LoneSeed.theorem_16_17_LL, @LoneSeed.theorem_16_17_RR, @Capture.theorem_16_12_item3,
    @Step5Induction.clauses_1_2, @Step5Induction.clause_4, @Step5Seed.no_root_of_seed,
    @Step5Words.theorem_16_12_item1, @Step5Words.theorem_16_12_item2,
    @Step5Words.theorem_16_12_item1_governed, @Step5Words.theorem_16_12_item2_governed,
    @CaptureWords.theorem_16_12_item3⟩,
   rfl, rfl, StatusLedger.thm_31_7.2.2.2.2.2.1⟩

/-! ## Definition 33.4 — Downstream authority order -/

/-- **Definition 33.4.** The recommended dependency order. -/
def authorityOrder : List Stage :=
  [.shellTheorem, .rademacher, .fieldCorrespondence, .exchange, .applications]

def Stage.rank : Stage → Fin 5
  | .shellTheorem => 0
  | .rademacher => 1
  | .fieldCorrespondence => 2
  | .exchange => 3
  | .applications => 4

/-- The stages whose output an input type contains: an application input
    contains a shell-stage input with its passed certificate and an encoding
    (`AppStageIn.toShellInput`, `AppStageIn.encoding`). No other stage input
    contains another stage's output or datum. -/
def Stage.needs : Stage → List Stage
  | .applications => [.shellTheorem, .fieldCorrespondence]
  | _ => []

/-- **Definition 33.4.** The order lists each stage once in rank order; the nine
    obligation rows fall to exactly one stage each (1, 3, 3, 1, 1); and every
    typed dependency points to an earlier stage. -/
theorem def_33_4 :
    authorityOrder.map Stage.rank = [0, 1, 2, 3, 4] ∧
    authorityOrder.Nodup ∧ (∀ s : Stage, s ∈ authorityOrder) ∧
    (∀ o ∈ Obligations.obligations,
      (authorityOrder.filter fun s => decide (o.owner ∈ s.owners)).length = 1) ∧
    authorityOrder.map (fun s => (rowsFor s Obligations.obligations).length) = [1, 3, 3, 1, 1] ∧
    (∀ s ∈ authorityOrder, ∀ t ∈ s.needs, t.rank < s.rank) := by
  refine ⟨rfl, by decide, fun s => ?_, by decide, rfl, by decide⟩
  cases s <;> decide

section Parallel
variable {Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St : Type} {h : ℕ}

/-- **Definition 33.4, the parallel clause.** The shell track reads the global
    incidence view: its certificate is fixed by the active face map, whatever
    the carried histories. The Rademacher track reads the carried-history view:
    its input is fixed by the lifecycle ledger, releases, strata and stratum,
    whatever the reception. Neither input type holds the other stage's datum
    (`shellStage` takes no cocycle, `radStage` no reception), so neither waits on
    the other. Both views are computed from the one lifecycle ledger: the active
    map is its `activeAt` restriction. -/
theorem parallel_33_4 {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F]
    (X X' : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (Γ : Shell.Reception QuestionId Incidence.OEdge Incidence.FaceId V E F)
    (hΓ : Shell.Admissible Γ Shell.oedges (X.shell.actMap.map Shell.FaceRec.pre))
    (hΓ' : Shell.Admissible Γ Shell.oedges (X'.shell.actMap.map Shell.FaceRec.pre))
    (H : RadTransport.RadCocycle) :
    (X.shell.actMap = X'.shell.actMap → (shellStage X Γ hΓ).cert = (shellStage X' Γ hΓ').cert) ∧
    (X.lifeLedger = X'.lifeLedger → X.releases = X'.releases →
      X.archFaces.map X.entry = X'.archFaces.map X'.entry → X.n = X'.n →
      radStage X H = radStage X' H) := by
  refine ⟨fun hact => (thm_33_2_shell X X' Γ hΓ hΓ' hact).2.2.1, fun h1 h2 h3 h4 => ?_⟩
  change (⟨X.lifeLedger, X.releases, X.archFaces.map X.entry, X.n, X.recurrence, H⟩ : RadStageIn P Y) =
    ⟨X'.lifeLedger, X'.releases, X'.archFaces.map X'.entry, X'.n, X'.recurrence, H⟩
  rw [h1, h2, h3, h4]

/-- **Definition 33.4, "Neither track replaces the other."** The shell certificate
    does not determine the Rademacher input, and the Rademacher input does not
    determine the shell certificate.
    1. The shell certificate does not determine the Rademacher input: a packet
       that differs from `X` only in its release records (which, by the packet's
       tie, name archived faces) has the same active face map, hence the same
       certificate, and a different Rademacher input.
    2. The Rademacher input does not determine the shell certificate: a packet
       that differs from `X` only in declaring no face retention-compatible has
       the same Rademacher input and, when `X`'s active map is non-empty, a
       different certificate (its source is the active map, now empty). The
       admissibility of `Γ` on the empty face list is taken as a hypothesis. -/
theorem neither_replaces_33_4 {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F]
    (X : ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (Γ : Shell.Reception QuestionId Incidence.OEdge Incidence.FaceId V E F)
    (hΓ : Shell.Admissible Γ Shell.oedges (X.shell.actMap.map Shell.FaceRec.pre))
    (H : RadTransport.RadCocycle) :
    (∀ (rel : List (Lifecycle.ReleaseRec P)) (hrel : ∀ r ∈ rel, r.fid ∈ X.archFaces.map (·.id)),
      rel ≠ X.releases →
      (shellStage { X with releases := rel, rel_in_arch := hrel } Γ hΓ).cert = (shellStage X Γ hΓ).cert ∧
      radStage { X with releases := rel, rel_in_arch := hrel } H ≠ radStage X H) ∧
    (X.shell.actMap ≠ [] →
      ∀ hΓ0 : Shell.Admissible Γ Shell.oedges
        (({ X with compat := fun _ => false } :
          ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h).shell.actMap.map
            Shell.FaceRec.pre),
      radStage { X with compat := fun _ => false } H = radStage X H ∧
      (shellStage { X with compat := fun _ => false } Γ hΓ0).cert ≠ (shellStage X Γ hΓ).cert) := by
  refine ⟨fun rel _ hrel => ⟨rfl, fun he => hrel (congrArg RadStageIn.releases he)⟩,
    fun hne hΓ0 => ⟨rfl, fun he => hne ?_⟩⟩
  have h0 : ∀ (p : Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool)
      (l : List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew)),
      l.filter (fun r => false && p r) = [] := by
    intro p l
    induction l with
    | nil => rfl
    | cons _ _ ih => exact ih
  exact (congrArg Shell.ShellCert.src he).symm.trans (h0 _ _)

end Parallel

/-! ## Boundary Statement 33.5 — End of the Elements II construction -/

section Boundary
variable {Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St : Type} {h : ℕ}

/-- **Boundary Statement 33.5.**

    1. *Elements II constructs.* From any cycle's state, outcome, retention
       declaration, lifecycle ledger and releases, tied as `ofState` requires,
       the packet is built (for `𝒬_LL` and `𝒬_RR` concretely: `exportLL`,
       `exportRR`); its
       components 6–8 are the built recurrence ledger, obligation table and
       status ledger; its shell interface carries that state and archive.
    2. *The Renewal-Shell Theorem receives `ShellIn`.* The finite certificate
       passes through an admissible declared reception (a sphere-shell input),
       fails through another, and the native one-lineage export fails it
       (Boundary 25.13).
    3. *Nothing is inserted backward.* An obligation record carries no map (it
       has decidable equality, Definition 30.1), and equality under a receiver
       never identifies the retained preimages (Boundary 32.3): a projection
       states what it forgets. -/
theorem boundary_33_5
    (S : Face.RecState Op (List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (c : Cycle.CycleOutcome σ RawAux EvalAux h) (Θ : Lifecycle.Retention P Y Ph St)
    (D : Lifecycle.LifeLedger P Y) (rel : List (Lifecycle.ReleaseRec P)) (n : ℕ)
    (entry : Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew → ℕ)
    (compat : Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool)
    (recOf : σ → Face.RecState Op (List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (t : QuestionId) (L : List (Incidence.FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hS : ∀ x k, c = .assimilated x k → S = Incidence.recordFace (recOf x) t L)
    (hD : ∀ ev ∈ D, ev.1.1 ∈ (S.hist.flatMap Prod.snd).map (·.id) ∧
      ev.2.fid ∈ (S.hist.flatMap Prod.snd).map (·.id))
    (hrel : ∀ r ∈ rel, r.fid ∈ (S.hist.flatMap Prod.snd).map (·.id)) :
    ((ofState S c Θ D rel n entry compat recOf t L hS hD hrel).obligations = Obligations.obligations ∧
      (ofState S c Θ D rel n entry compat recOf t L hS hD hrel).status = StatusLedger.combined ∧
      (ofState S c Θ D rel n entry compat recOf t L hS hD hrel).archFaces = S.hist.flatMap Prod.snd ∧
      (ofState S c Θ D rel n entry compat recOf t L hS hD hrel).cycle = c ∧
      (ofState S c Θ D rel n entry compat recOf t L hS hD hrel).shell.faceState = S ∧
      (ofState S c Θ D rel n entry compat recOf t L hS hD hrel).shell.archive = ⟨S.hist.flatMap Prod.snd, D, rel⟩) ∧
    ((Shell.Admissible (Shell.Reception.ofMaps Shell.glueV Shell.glueE id Shell.preTetra) Shell.pairEdges Shell.preTetra ∧
        ((Shell.Reception.ofMaps Shell.glueV Shell.glueE id Shell.preTetra).complex Shell.preTetra).SphereShellInput) ∧
      (Shell.Admissible (Shell.Reception.ofMaps Shell.glueV Shell.glueE id Shell.preTwisted) Shell.pairEdges Shell.preTwisted ∧
        ¬ ((Shell.Reception.ofMaps Shell.glueV Shell.glueE id Shell.preTwisted).complex Shell.preTwisted).ClosedShellInput) ∧
      ¬ (Shell.lineCx Shell.iWit [0, 1, 2]).ClosedShellInput) ∧
    Nonempty (DecidableEq Obligations.ProjOb) ∧
    ¬ (∀ e : Retired.NamedEquality Word (ZMod 12), e.left = e.right) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, Shell.boundary_25_13, ⟨Obligations.projOb_decidableEq⟩,
   Retired.boundary_32_3.2.2⟩

end Boundary

/-! ## Definition 33.1 at the face-bearing questions of Proposition 22.10

    Boundary 33.5 hands Elements III "the canonical face-bearing exports of
    Proposition 22.10". For the two lone-seed questions `𝒬_LL` and `𝒬_RR` and
    the two side-selected roots `𝒬_ε^L`, `𝒬_ε^R` the packet is built here with
    every component a value computed in the tree: the run is the book's
    schedule `AxiomPolicy.axiomPolicy` from Definition 16.16's seed carrier
    (`axiomPolicy_XLL7`, `axiomPolicy_XRR7`), or for the side-selected roots
    the side schedule `sidePolicyL`/`sidePolicyR` from the root seed carrier
    (`sidePolicyL_XepsSideL7`, `sidePolicyR_XepsSideR7`), the report is
    `Report.ofAssembled`, the snap is the unique candidate of the terminal
    ensemble, the certificate is `Return.certificate` over that snap, and the
    face records are `Incidence.ledgerOf` over the attached packets of
    `FaceRegression.eventsLL`/`eventsRR`/`eventsSideL`/`eventsSideR`. The
    retention `Θ` is a receiver declaration (Definition 24.10, Ledger 31.3
    item 5), supplied as `retainAll`. -/

section Concrete

open Accumulation Terminal Advance RootOrbit LoneSeed AxiomPolicy FaceRegression

/-- **`𝒬_LL` on the general engine.** The book's schedule from the `LL` seed
    carrier is, tick for tick, the run of `LoneSeed.lean`. -/
theorem axiomPolicy_XLL7 : Term axiomPolicy (X0 [false, false]) (X0_seeded _) = XLL7 := by
  have e1 := axiomPolicy_step (X0 [false, false]) (X0_seeded _) 0 (by decide) XLL0 rfl hlaw0LL sel1LL rfl hsel0LL hfresh0LL
  have e2 := axiomPolicy_step (X0 [false, false]) (X0_seeded _) 1 (by decide) XLL1 e1 hlaw1LL sel2LL rfl hsel1LL hfresh1LL
  have e3 := axiomPolicy_step (X0 [false, false]) (X0_seeded _) 2 (by decide) XLL2 e2 hlaw2LL sel3LL rfl hsel2LL hfresh2LL
  have e4 := axiomPolicy_step (X0 [false, false]) (X0_seeded _) 3 (by decide) XLL3 e3 hlaw3LL sel4LL rfl hsel3LL hfresh3LL
  have e5 := axiomPolicy_step (X0 [false, false]) (X0_seeded _) 4 (by decide) XLL4 e4 hlaw4LL sel5LL rfl hsel4LL hfresh4LL
  have e6 := axiomPolicy_step (X0 [false, false]) (X0_seeded _) 5 (by decide) XLL5 e5 hlaw5LL sel6LL rfl hsel5LL hfresh5LL
  exact axiomPolicy_step (X0 [false, false]) (X0_seeded _) 6 (by decide) XLL6 e6 hlaw6LL sel7LL rfl hsel6LL hfresh6LL

/-- **`𝒬_RR` on the general engine.** -/
theorem axiomPolicy_XRR7 : Term axiomPolicy (X0 [true, true]) (X0_seeded _) = XRR7 := by
  have e1 := axiomPolicy_step (X0 [true, true]) (X0_seeded _) 0 (by decide) XRR0 rfl hlaw0RR sel1RR rfl hsel0RR hfresh0RR
  have e2 := axiomPolicy_step (X0 [true, true]) (X0_seeded _) 1 (by decide) XRR1 e1 hlaw1RR sel2RR rfl hsel1RR hfresh1RR
  have e3 := axiomPolicy_step (X0 [true, true]) (X0_seeded _) 2 (by decide) XRR2 e2 hlaw2RR sel3RR rfl hsel2RR hfresh2RR
  have e4 := axiomPolicy_step (X0 [true, true]) (X0_seeded _) 3 (by decide) XRR3 e3 hlaw3RR sel4RR rfl hsel3RR hfresh3RR
  have e5 := axiomPolicy_step (X0 [true, true]) (X0_seeded _) 4 (by decide) XRR4 e4 hlaw4RR sel5RR rfl hsel4RR hfresh4RR
  have e6 := axiomPolicy_step (X0 [true, true]) (X0_seeded _) 5 (by decide) XRR5 e5 hlaw5RR sel6RR rfl hsel5RR hfresh5RR
  exact axiomPolicy_step (X0 [true, true]) (X0_seeded _) 6 (by decide) XRR6 e6 hlaw6RR sel7RR rfl hsel6RR hfresh6RR

/-! ### The side-selected roots as a schedule

    Definition 16.7 adds one exact admissibility predicate `γ_side` to `Γ`;
    everything else is Definition 16.4. `RootOrbit.axiomSelectSide` is
    Definition 8.1 with that predicate applied before the
    direct-positive test, at any stratum. Applied at every reached carrier,
    exactly as `axiomPolicyAt` applies `axiomSelect`, it is a `Policy`: every
    obligation of `AdvanceData` is discharged the same way, because the side
    filter only removes proposals. The predicate is identically `false` away
    from event 1 (`gammaSideL_off`, `gammaSideR_off`), so from tick 2 on the
    schedule is `axiomSelect` itself, which is the book's "admission at every
    event other than the first is direct-positive admission". -/

/-- `axiomSelectSide`'s identifiers are a sublist of the proposals' child
    identifiers. -/
theorem axiomSelectSide_sublist (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (reject : ℕ → Bool → Bool) (props : List (Core × Bool)) :
    (axiomSelectSide MO stratum prov reject props).Sublist
      (props.map (fun p => (childCore p.1 p.2 stratum prov).id)) := by
  have e : props.map (fun p => (childCore p.1 p.2 stratum prov).id) =
      (props.map (fun p => childCore p.1 p.2 stratum prov)).map Core.id := by
    rw [List.map_map]; rfl
  rw [e]
  unfold axiomSelectSide admittedCoresSide
  exact ((List.filter_sublist.trans List.filter_sublist).trans
    (List.filter_sublist.map _)).map Core.id

/-- **Definition 8.1 under Definition 16.7's side predicate, as a
    schedule.** The same fields as `axiomPolicyAt`, with `axiomSelectSide` in
    place of `axiomSelect`. -/
def sidePolicyAt (Aux : Type) (h : ℕ) (prov : Provenance) (reject : ℕ → Bool → Bool) :
    Policy Aux h := fun X _ hX =>
  { select := axiomSelectSide X.observer.matrix ((X.tick : ℕ) + 1) prov reject
    stratum := (X.tick : ℕ) + 1
    prov := prov
    Δ := []
    hsel := axiomSelectSide_hsel _ _ _ _ _
    hfresh := hX.hfresh _ _
    hgrow := by
      have := (axiomSelectSide_sublist X.observer.matrix ((X.tick : ℕ) + 1) prov reject
        (proposals X.archive X.active)).length_le
      rw [List.length_map, proposals_two, hX.hcard] at this
      exact this
    hcard := hX.hcard
    hselNodup :=
      (proposals_childCore_id_nodup hX.1.1 hX.1.2.1 _ prov).sublist
        (axiomSelectSide_sublist _ _ _ _ _) }

/-- **The schedule of `𝒬_ε^L`** (Definition 16.7, `γ_side^L`). -/
def sidePolicyL : Policy Unit hQ := sidePolicyAt Unit hQ seed164Prov gammaSideL
/-- **The schedule of `𝒬_ε^R`** (Definition 16.7, `γ_side^R`). -/
def sidePolicyR : Policy Unit hQ := sidePolicyAt Unit hQ seed164Prov gammaSideR

/-- A rejection predicate that is off at a stratum leaves `axiomSelect`
    unchanged there. -/
theorem axiomSelectSide_off (MO : Mat2) (stratum : ℕ) (prov : Provenance)
    (reject : ℕ → Bool → Bool) (hoff : ∀ g, reject stratum g = false) :
    axiomSelectSide MO stratum prov reject = axiomSelect MO stratum prov := by
  have e : reject stratum = fun _ => false := funext hoff
  funext props
  rw [← axiomSelectSide_false_eq]
  unfold axiomSelectSide admittedFamSide admittedCoresSide
  rw [e]

/-- `γ_side^L` refuses nothing away from event 1. -/
theorem gammaSideL_off (k : ℕ) (hk : k ≠ 1) (g : Bool) : gammaSideL k g = false := by
  change (decide (k = 1) && g) = false
  rw [decide_eq_false hk]
  rfl

/-- `γ_side^R` refuses nothing away from event 1. -/
theorem gammaSideR_off (k : ℕ) (hk : k ≠ 1) (g : Bool) : gammaSideR k g = false := by
  change (decide (k = 1) && !g) = false
  rw [decide_eq_false hk]
  rfl

/-- **One tick of a side schedule**, read as the concrete advance
    `RootOrbit.lean` writes (the companion of `axiomPolicy_step`). -/
theorem sidePolicy_step (reject : ℕ → Bool → Bool) (X0 : TickCarrier Unit hQ) (hs : Seeded X0)
    (n : ℕ) (hn : n + 1 ≤ hQ) (Y : TickCarrier Unit hQ)
    (hY : iterate (sidePolicyAt Unit hQ seed164Prov reject) X0 hs n (Nat.le_of_succ_le hn) = Y)
    (hlY : Lawful Y) (sel : List (Core × Bool) → List QuestionId)
    (hsel_eq : sel = axiomSelectSide X0.observer.matrix (n + 1) seed164Prov reject)
    (hselY : ∀ i ∈ sel (proposals Y.archive Y.active),
      ∃ p ∈ proposals Y.archive Y.active, (childCore p.1 p.2 (n + 1) seed164Prov).id = i)
    (hfrY : ∀ p ∈ proposals Y.archive Y.active,
      (childCore p.1 p.2 (n + 1) seed164Prov).id ∉ archIds Y.archive) :
    iterate (sidePolicyAt Unit hQ seed164Prov reject) X0 hs (n + 1) hn =
      advanceCarrier Y hlY sel (n + 1) seed164Prov [] hselY hfrY := by
  rw [iterate_succ]
  have ht := iterate_tick (sidePolicyAt Unit hQ seed164Prov reject) X0 hs n (Nat.le_of_succ_le hn)
  have ho := iterate_observer (sidePolicyAt Unit hQ seed164Prov reject) X0 hs n (Nat.le_of_succ_le hn)
  refine advanceCarrier_congr hY ?_ ?_ rfl rfl
  · change axiomSelectSide (iterate (sidePolicyAt Unit hQ seed164Prov reject) X0 hs n _).observer.matrix
      (((iterate (sidePolicyAt Unit hQ seed164Prov reject) X0 hs n _).tick : ℕ) + 1) seed164Prov reject = sel
    rw [ho, ht, hsel_eq]
  · change ((iterate (sidePolicyAt Unit hQ seed164Prov reject) X0 hs n _).tick : ℕ) + 1 = n + 1
    rw [ht]

/-- **`𝒬_ε^L` on the general engine.** The side schedule from the root seed
    carrier is, tick for tick, Theorem 16.8's run `XepsSideL1..7`. -/
theorem sidePolicyL_XepsSideL7 : Term sidePolicyL (X0 []) (X0_seeded _) = XepsSideL7 := by
  have e1 := sidePolicy_step gammaSideL (X0 []) (X0_seeded _) 0 (by decide) Xeps0 rfl hlaw0eps selSideL1eps rfl hselSideL0eps hfresh0eps
  have e2 := sidePolicy_step gammaSideL (X0 []) (X0_seeded _) 1 (by decide) XepsSideL1 e1 hlawSideL1eps selSideL2eps
    (axiomSelectSide_off _ _ _ _ (gammaSideL_off 2 (by decide))).symm hselSideL1eps hfreshSideL1eps
  have e3 := sidePolicy_step gammaSideL (X0 []) (X0_seeded _) 2 (by decide) XepsSideL2 e2 hlawSideL2eps selSideL3eps
    (axiomSelectSide_off _ _ _ _ (gammaSideL_off 3 (by decide))).symm hselSideL2eps hfreshSideL2eps
  have e4 := sidePolicy_step gammaSideL (X0 []) (X0_seeded _) 3 (by decide) XepsSideL3 e3 hlawSideL3eps selSideL4eps
    (axiomSelectSide_off _ _ _ _ (gammaSideL_off 4 (by decide))).symm hselSideL3eps hfreshSideL3eps
  have e5 := sidePolicy_step gammaSideL (X0 []) (X0_seeded _) 4 (by decide) XepsSideL4 e4 hlawSideL4eps selSideL5eps
    (axiomSelectSide_off _ _ _ _ (gammaSideL_off 5 (by decide))).symm hselSideL4eps hfreshSideL4eps
  have e6 := sidePolicy_step gammaSideL (X0 []) (X0_seeded _) 5 (by decide) XepsSideL5 e5 hlawSideL5eps selSideL6eps
    (axiomSelectSide_off _ _ _ _ (gammaSideL_off 6 (by decide))).symm hselSideL5eps hfreshSideL5eps
  exact sidePolicy_step gammaSideL (X0 []) (X0_seeded _) 6 (by decide) XepsSideL6 e6 hlawSideL6eps selSideL7eps
    (axiomSelectSide_off _ _ _ _ (gammaSideL_off 7 (by decide))).symm hselSideL6eps hfreshSideL6eps

/-- **`𝒬_ε^R` on the general engine.** -/
theorem sidePolicyR_XepsSideR7 : Term sidePolicyR (X0 []) (X0_seeded _) = XepsSideR7 := by
  have e1 := sidePolicy_step gammaSideR (X0 []) (X0_seeded _) 0 (by decide) Xeps0 rfl hlaw0eps selSideR1eps rfl hselSideR0eps hfresh0eps
  have e2 := sidePolicy_step gammaSideR (X0 []) (X0_seeded _) 1 (by decide) XepsSideR1 e1 hlawSideR1eps selSideR2eps
    (axiomSelectSide_off _ _ _ _ (gammaSideR_off 2 (by decide))).symm hselSideR1eps hfreshSideR1eps
  have e3 := sidePolicy_step gammaSideR (X0 []) (X0_seeded _) 2 (by decide) XepsSideR2 e2 hlawSideR2eps selSideR3eps
    (axiomSelectSide_off _ _ _ _ (gammaSideR_off 3 (by decide))).symm hselSideR2eps hfreshSideR2eps
  have e4 := sidePolicy_step gammaSideR (X0 []) (X0_seeded _) 3 (by decide) XepsSideR3 e3 hlawSideR3eps selSideR4eps
    (axiomSelectSide_off _ _ _ _ (gammaSideR_off 4 (by decide))).symm hselSideR3eps hfreshSideR3eps
  have e5 := sidePolicy_step gammaSideR (X0 []) (X0_seeded _) 4 (by decide) XepsSideR4 e4 hlawSideR4eps selSideR5eps
    (axiomSelectSide_off _ _ _ _ (gammaSideR_off 5 (by decide))).symm hselSideR4eps hfreshSideR4eps
  have e6 := sidePolicy_step gammaSideR (X0 []) (X0_seeded _) 5 (by decide) XepsSideR5 e5 hlawSideR5eps selSideR6eps
    (axiomSelectSide_off _ _ _ _ (gammaSideR_off 6 (by decide))).symm hselSideR5eps hfreshSideR5eps
  exact sidePolicy_step gammaSideR (X0 []) (X0_seeded _) 6 (by decide) XepsSideR6 e6 hlawSideR6eps selSideR7eps
    (axiomSelectSide_off _ _ _ _ (gammaSideR_off 7 (by decide))).symm hselSideR6eps hfreshSideR6eps

theorem hQ_pos : 0 < hQ := by decide

/-- The face record type of the concrete packets: unit raw and admission
    payloads, `EvalValue` evaluation records, the seven-tick horizon, the
    cycle's resolution provenance as the recording provenance, no renewal
    transport yet. -/
abbrev FR := Incidence.FaceRec Unit Unit Unit EvalValue hQ Return.ResProvenance Unit

/-- The state the append sees: the operative component is the terminal
    carrier. -/
abbrev St := Face.RecState (TickCarrier Unit hQ) (List FR)

/-- The single element of a one-element list (`d` otherwise). -/
def oneOf {α : Type} (d : α) : List α → α
  | [x] => x
  | _ => d

theorem oneOf_spec {α : Type} (d : α) : ∀ l : List α, l.length = 1 → l = [oneOf d l]
  | [_], _ => rfl
  | [], hl => absurd hl Nat.zero_ne_one
  | _ :: _ :: _, hl => absurd (Nat.succ.inj hl) (Nat.succ_ne_zero _)

/-- The terminal carrier of the question seeded by `w` under the schedule `pol`
    (the book's `axiomPolicy` for Definition 16.4's questions, `sidePolicyL`/`R`
    for Definition 16.7's). -/
def TQ (pol : Policy Unit hQ) (w : Word) : TickCarrier Unit hQ := Term pol (X0 w) (X0_seeded w)

/-- Its evaluated ledger and complete report (Definition 17.2). -/
def ledgerQ (pol : Policy Unit hQ) (w : Word) : List (QuestionId × EvalRecord EvalValue) := assembleLedger (TQ pol w)
def reportQ (pol : Policy Unit hQ) (w : Word) : Report Unit EvalValue hQ := Report.of pol (X0 w) (X0_seeded w) hQ_pos (ledgerQ pol w)

/-- The committed candidate: the one member of the terminal ensemble. -/
def candQ (pol : Policy Unit hQ) (w : Word) : Cand EvalValue :=
  oneOf (candidate (TQ pol w) (ledgerQ pol w) (seedCore seed164Id ⟨Frame.empty, w⟩ 0 seed164Prov))
    (ensemble (TQ pol w) (ledgerQ pol w))

/-- The socket target of Definition 16.4's questions, `ι_O`. -/
def targetQ (w : Word) : QuestionId := (canonicalQuestion w).socket.target

/-- The resolution provenance (19.1): question identifier, cycle `0`, horizon,
    terminal event, socket target. -/
def provQ (w : Word) : Return.ResProvenance := ⟨seed164Id, 0, hQ, hQ, targetQ w⟩

/-- The observer-local word of the survivor (Definition 3.1). -/
def localQ (pol : Policy Unit hQ) (w : Word) : Word := (localWord (X0 w).observer.matrix (candQ pol w).core.fullMatrix).getD []

/-- **`C^cyc`** (Definition 19.1), over the question's own snap. The canonical
    socket declares `splice := id`, so the splice position is `0`. -/
def certQ (pol : Policy Unit hQ) (w : Word) : Return.CycleCertificate Unit EvalValue hQ :=
  Return.certificate (reportQ pol w).q (targetQ w) (candQ pol w).core (localQ pol w) (candQ pol w, reportQ pol w) 0 (provQ w)

/-- Definition 11.3's certificate for a proposed child under direct-positive
    admission with no declared predicate and no cavity-boundary term (the
    regime of `RootOrbit.admittedCores`). -/
def admCertOf (MO : Mat2) (y : Core) : AdmCert Unit where
  encounter := Q MO y.fullMatrix
  negLoad := negLoad (Q MO y.fullMatrix)
  gamma := []
  pred := true
  adm := admits (negLoad (Q MO y.fullMatrix)) true
  fail := failReasons true (negLoad (Q MO y.fullMatrix)) true

/-- Definition 6.5's creation status, read from the next tick's support and the
    admitted family. -/
def propStatus (act adm : List QuestionId) (y : QuestionId) : ProposalStatus Unit :=
  if y ∈ act then (if act.length = 1 then .selected else .tiedSelected)
  else if y ∈ adm then .coherenceRejected else .admissionRejected ()

/-- The archived parent occurrence `x_j` of an event. -/
def parentQ (pol : Policy Unit hQ) (w : Word) (x : QuestionId) : Core :=
  ((TQ pol w).archive.find? fun c => decide (c.id = x)).getD (seedCore seed164Id ⟨Frame.empty, w⟩ 0 seed164Prov)

/-- **Definition 22.5's packet at one event**, with every component read from
    the run: the event's eligibility input at the question's socket target, the
    oriented shortcut over the archived pair (21.1), the boundary and sibling
    records (22.1, 22.3), the undeclared lift status, and the cycle certificate.
    `acts` lists the supports at ticks `1..7`. -/
def pktQ (pol : Policy Unit hQ) (w : Word) (acts : List (List QuestionId)) (e : FaceRegression.Event) : Face.FElig Unit Unit Unit EvalValue hQ where
  input := e.toInput (targetQ w)
  shortcut := Shortcut.shortcut
    (Shortcut.pairOf (parentQ pol w e.x) (e.j + 1) seed164Prov
      (admCertOf (X0 w).observer.matrix (childCore (parentQ pol w e.x) false (e.j + 1) seed164Prov))
      (admCertOf (X0 w).observer.matrix (childCore (parentQ pol w e.x) true (e.j + 1) seed164Prov))
      (propStatus (acts.getD e.j []) e.admitted (childCore (parentQ pol w e.x) false (e.j + 1) seed164Prov).id)
      (propStatus (acts.getD e.j []) e.admitted (childCore (parentQ pol w e.x) true (e.j + 1) seed164Prov).id))
    e.s
  bdry := Face.boundary e.x (e.x.child e.s) (e.x.child (!e.s)) e.s
  sib := Face.sibRec (e.x.child e.s) (e.x.child (!e.s)) e.s
  lift := liftStatus none
  cycle := certQ pol w
  elig := (e.toInput (targetQ w)).vector
  elig_eq := rfl

/-- The incidence ledger `𝖥_{τ+1}` (Definition 23.4): one entry record per
    attached packet (Construction Axiom II.2). -/
def ledgerFacesQ (pol : Policy Unit hQ) (w : Word) (acts : List (List QuestionId)) (es : List FaceRegression.Event) : List FR :=
  Incidence.ledgerOf (Face.receivedFaces (es.map (pktQ pol w acts))) (targetQ w) (provQ w)

/-- The source state `S_τ` and the next state `S_{τ+1}`. The operative component
    of the next state is the terminal carrier; observer adoption is recorded in
    the certificate (the tree's adoption step, Definition 20.2's `adopt`, is a
    parameter over a generic state, so no carrier-level adoption map exists). -/
def sourceQ (w : Word) : St := ⟨X0 w, []⟩
def nextQ (pol : Policy Unit hQ) (w : Word) : St := ⟨TQ pol w, []⟩

/-- A declared retention that keeps every face: every gate one, a unit packet,
    an unevaluated reading. Declared, as the book has it: Definition 24.10's
    `Θ` is "exact receiver data" and Ledger 31.3 item 5 lists it among the
    supplied, not derived, data. `retainAll` is one particular declaration,
    chosen for the concrete packets; it is not derived from the questions. -/
def retainAll : Lifecycle.Retention Unit Unit Unit Unit where
  recv := ⟨fun _ => true, fun _ => .notEvaluated, fun _ => false, []⟩
  sock := fun _ _ _ => true
  chiAdm := fun _ => true
  theta := fun _ => ()
  window := fun _ => true
  chiLift := fun _ => true
  chiRead := fun _ _ _ _ => true

/-- One lifecycle evaluation per face at the read stratum `n` (Definitions
    24.11 and 24.12): the gate vector of `Θ`, the transition from no prior
    status with no receiver advance. -/
def entryEvals (Θ : Lifecycle.Retention Unit Unit Unit Unit) (fs : List FR) (n : ℕ) :
    Lifecycle.LifeLedger Unit Unit :=
  fs.map fun r =>
    ((r.id, 0, n),
     ⟨r.id, 0, n, Lifecycle.aArch n n, (), Θ.recv.recv (),
      Lifecycle.gateVector Θ r.id () () () r.packet.lift n n,
      Lifecycle.step [] (Lifecycle.gateVector Θ r.id () () () r.packet.lift n n) false⟩)

theorem entryEvals_in (Θ : Lifecycle.Retention Unit Unit Unit Unit) (fs : List FR) (n : ℕ) :
    ∀ ev ∈ entryEvals Θ fs n, ev.1.1 ∈ fs.map (·.id) ∧ ev.2.fid ∈ fs.map (·.id) := by
  intro ev hev
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hev
  exact ⟨List.mem_map_of_mem hr, List.mem_map_of_mem hr⟩

/-- **Definition 33.1 at a question run by the schedule `pol`.** The packet built
    by `ofState`: face state the next state with this cycle's ledger recorded
    at the socket target, cycle outcome assimilated with `C^cyc`, archival
    family every recorded face, one entry evaluation per face at stratum `1`
    under `retainAll`, no release, every face retention-compatible and entered
    at stratum `1`. -/
def exportQ (pol : Policy Unit hQ) (w : Word) (acts : List (List QuestionId)) (es : List FaceRegression.Event) :
    ElemIIOut (TickCarrier Unit hQ) St Unit Unit Unit EvalValue Return.ResProvenance Unit Unit Unit Unit Unit hQ :=
  ofState (Incidence.recordFace (nextQ pol w) (targetQ w) (ledgerFacesQ pol w acts es))
    (.assimilated (nextQ pol w) (certQ pol w)) retainAll
    (entryEvals retainAll ((Incidence.recordFace (nextQ pol w) (targetQ w) (ledgerFacesQ pol w acts es)).hist.flatMap Prod.snd) 1)
    [] 1 (fun _ => 1) (fun _ => true) id (targetQ w) (ledgerFacesQ pol w acts es)
    (fun x k hc => by
      obtain ⟨rfl, -⟩ := Cycle.CycleOutcome.assimilated.inj hc
      rfl)
    (entryEvals_in _ _ _) (fun _ hr => nomatch hr)

/-- The supports of `𝒬_LL` and `𝒬_RR` at ticks `1..7`. -/
def actsLL : List (List QuestionId) := [XLL1.active, XLL2.active, XLL3.active, XLL4.active, XLL5.active, XLL6.active, XLL7.active]
def actsRR : List (List QuestionId) := [XRR1.active, XRR2.active, XRR3.active, XRR4.active, XRR5.active, XRR6.active, XRR7.active]

/-- **The export packet of `𝒬_LL`.** -/
def exportLL := exportQ axiomPolicy [false, false] actsLL eventsLL
/-- **The export packet of `𝒬_RR`.** -/
def exportRR := exportQ axiomPolicy [true, true] actsRR eventsRR

/-- The attached packets' inputs are the attached events' inputs. -/
theorem received_inputs (pol : Policy Unit hQ) (w : Word) (acts : List (List QuestionId)) :
    ∀ es : List FaceRegression.Event, (Face.receivedFaces (es.map (pktQ pol w acts))).map (·.packet.input) =
      (attached es).map (·.toInput (targetQ w))
  | [] => rfl
  | e :: es => by
    have ih := received_inputs pol w acts es
    have hall : (pktQ pol w acts e).elig.all = e.vec.all := by
      change (e.toInput (targetQ w)).vector.all = e.vec.all
      rw [Event.toInput_vector]
    unfold Face.receivedFaces at ih ⊢
    unfold attached at ih ⊢
    rw [List.map_cons, List.filter_cons, List.filter_cons, hall]
    cases e.vec.all
    · exact ih
    · change (pktQ pol w acts e).input :: _ = e.toInput (targetQ w) :: _
      rw [← ih]
      rfl

/-- Every recorded face of a ledger built by `ledgerFacesQ` carries the cycle
    certificate and the socket target. -/
theorem ledgerFacesQ_cert (pol : Policy Unit hQ) (w : Word) (acts : List (List QuestionId)) (es : List FaceRegression.Event) :
    ∀ r ∈ ledgerFacesQ pol w acts es, r.packet.cycle = certQ pol w ∧ r.target = targetQ w ∧ r.prov = provQ w := by
  intro r hr
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hp).1
  exact ⟨rfl, rfl, rfl⟩

/-- The archival family of `exportQ` is this cycle's ledger. -/
theorem exportQ_archFaces (pol : Policy Unit hQ) (w : Word) (acts : List (List QuestionId)) (es : List FaceRegression.Event) :
    (exportQ pol w acts es).archFaces = ledgerFacesQ pol w acts es := by
  change [(targetQ w, ledgerFacesQ pol w acts es)].flatMap Prod.snd = _
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The face events of the archival family are the attached events. -/
theorem exportQ_events (pol : Policy Unit hQ) (w : Word) (acts : List (List QuestionId)) (es : List FaceRegression.Event) :
    (exportQ pol w acts es).archFaces.map (·.id.event) = attachedEvents es := by
  rw [exportQ_archFaces]
  unfold ledgerFacesQ Incidence.ledgerOf attachedEvents
  rw [List.map_map]
  have h := congrArg (List.map fun i : Face.EligInput => i.j + 1) (received_inputs pol w acts es)
  rw [List.map_map, List.map_map] at h
  exact h

theorem some_getD {α : Type} (d : α) : ∀ o : Option α, o.isSome = true → o = some (o.getD d)
  | some _, _ => rfl

set_option maxRecDepth 200000 in
/-- **The certificates name the run's survivor and its decoded local word.**
    For `𝒬_LL` and `𝒬_RR` the certificate's survivor is the one occurrence of
    the terminal support of the certified run, and the observer-local word of
    Definition 3.1 is defined on it (so `localQ` is that word, not the
    fallback). -/
theorem certQ_survivor :
    [(certQ axiomPolicy [false, false]).survivorId] = XLL7.active ∧
    localWord (X0 [false, false]).observer.matrix (candQ axiomPolicy [false, false]).core.fullMatrix =
      some (localQ axiomPolicy [false, false]) ∧
    [(certQ axiomPolicy [true, true]).survivorId] = XRR7.active ∧
    localWord (X0 [true, true]).observer.matrix (candQ axiomPolicy [true, true]).core.fullMatrix =
      some (localQ axiomPolicy [true, true]) := by
  refine ⟨?_, some_getD _ _ ?_, ?_, some_getD _ _ ?_⟩
  · unfold certQ Return.certificate candQ ledgerQ TQ
    rw [axiomPolicy_XLL7]
    decide
  · unfold candQ ledgerQ TQ
    rw [axiomPolicy_XLL7]
    decide
  · unfold certQ Return.certificate candQ ledgerQ TQ
    rw [axiomPolicy_XRR7]
    decide
  · unfold candQ ledgerQ TQ
    rw [axiomPolicy_XRR7]
    decide

set_option maxRecDepth 200000 in
/-- **The same for the side-selected roots** `𝒬_ε^L`, `𝒬_ε^R` under their
    side schedules. -/
theorem certQ_survivor_side :
    [(certQ sidePolicyL []).survivorId] = XepsSideL7.active ∧
    localWord (X0 []).observer.matrix (candQ sidePolicyL []).core.fullMatrix =
      some (localQ sidePolicyL []) ∧
    [(certQ sidePolicyR []).survivorId] = XepsSideR7.active ∧
    localWord (X0 []).observer.matrix (candQ sidePolicyR []).core.fullMatrix =
      some (localQ sidePolicyR []) := by
  refine ⟨?_, some_getD _ _ ?_, ?_, some_getD _ _ ?_⟩
  · unfold certQ Return.certificate candQ ledgerQ TQ
    rw [sidePolicyL_XepsSideL7]
    decide
  · unfold candQ ledgerQ TQ
    rw [sidePolicyL_XepsSideL7]
    decide
  · unfold certQ Return.certificate candQ ledgerQ TQ
    rw [sidePolicyR_XepsSideR7]
    decide
  · unfold candQ ledgerQ TQ
    rw [sidePolicyR_XepsSideR7]
    decide

/-- The snap of a question whose terminal ensemble has one member commits that
    member with the complete report (Definition 18.1). -/
theorem snapQ (pol : Policy Unit hQ) (w : Word) (hlen : (ensemble (TQ pol w) (ledgerQ pol w)).length = 1) :
    Snap.snap pol (X0 w) (X0_seeded w) hQ_pos (ledgerQ pol w) = some (candQ pol w, reportQ pol w) := by
  change Option.map _ (resolveOcc (ensemble (TQ pol w) (ledgerQ pol w))) = _
  rw [oneOf_spec _ _ hlen]
  rfl

set_option maxRecDepth 200000 in
/-- **Definition 33.1 is a packet for `𝒬_LL`.**
    1. its cycle outcome is the question's total cycle evaluation (Definition
       20.3) on the book's schedule, and it is assimilated with `C^cyc`;
    2. the report is the question's (Definition 17.2), singleton, with the
       support of the certified run `XLL7`;
    3. the certificate's snap is the question's snap (Definition 18.1);
    4. the face state is the next state with this ledger recorded at the
       socket target (Definition 23.5), and the archive is that ledger;
    5. the ledger's packets are built at exactly the events of Proposition
       22.10 item 5, its faces are those of the attached events `1..7`, seven of
       them, and each carries the certificate, the target and the provenance;
    6. every lifecycle event names an archived face and nothing is released. -/
theorem exportLL_packet :
    exportLL.cycle = Cycle.cycle (sourceQ [false, false]) (reportQ axiomPolicy [false, false])
      (nextQ axiomPolicy [false, false], certQ axiomPolicy [false, false]) ∧
    exportLL.cycle = .assimilated (nextQ axiomPolicy [false, false]) (certQ axiomPolicy [false, false]) ∧
    (reportQ axiomPolicy [false, false]).status = TermStatus.singleton ∧
    (reportQ axiomPolicy [false, false]).Sh = XLL7.active ∧
    Snap.snap axiomPolicy (X0 [false, false]) (X0_seeded _) hQ_pos (ledgerQ axiomPolicy [false, false]) =
      some (certQ axiomPolicy [false, false]).snapped ∧
    exportLL.faceState = Incidence.recordFace (nextQ axiomPolicy [false, false]) (targetQ [false, false]) exportLL.ledger ∧
    exportLL.archFaces = exportLL.ledger ∧
    (eventsLL.map (pktQ axiomPolicy [false, false] actsLL)).map (·.input) = eventsLL.map (·.toInput (targetQ [false, false])) ∧
    exportLL.archFaces.map (·.id.event) = attachedEvents eventsLL ∧
    attachedEvents eventsLL = [1, 2, 3, 4, 5, 6, 7] ∧
    exportLL.archFaces.length = 7 ∧
    (∀ r ∈ exportLL.archFaces, r.packet.cycle = certQ axiomPolicy [false, false] ∧
      r.target = targetQ [false, false] ∧ r.prov = provQ [false, false]) ∧
    (∀ ev ∈ exportLL.lifeLedger, ev.1.1 ∈ exportLL.archFaces.map (·.id)) ∧
    exportLL.releases = [] := by
  have hst : (reportQ axiomPolicy [false, false]).status = TermStatus.singleton := by
    change termStatus (Term axiomPolicy (X0 [false, false]) (X0_seeded _)).active.length = _
    rw [axiomPolicy_XLL7]
    exact prop_22_10_LL.1
  have hlen : (ensemble (TQ axiomPolicy [false, false]) (ledgerQ axiomPolicy [false, false])).length = 1 := by
    unfold ledgerQ TQ
    rw [axiomPolicy_XLL7]
    decide
  have hev : exportLL.archFaces.map (·.id.event) = attachedEvents eventsLL := exportQ_events _ _ _ _
  have hlen7 : exportLL.archFaces.length = 7 := by
    rw [← List.length_map (f := fun r : FR => r.id.event), hev, prop_22_10_LL.2.2.2.1]
    rfl
  refine ⟨?_, rfl, hst, ?_, snapQ _ _ hlen, rfl, exportQ_archFaces _ _ _ _, ?_, hev,
    prop_22_10_LL.2.2.2.1, hlen7, ?_, fun ev hev' => (exportLL.life_in_arch ev hev').1, rfl⟩
  · show _ = Cycle.cycle _ _ _
    unfold Cycle.cycle
    rw [hst]
    rfl
  · change (Term axiomPolicy (X0 [false, false]) (X0_seeded _)).active = _
    rw [axiomPolicy_XLL7]
  · rw [List.map_map]; rfl
  · unfold exportLL
    rw [exportQ_archFaces]
    exact ledgerFacesQ_cert _ _ _ _

set_option maxRecDepth 200000 in
/-- **Definition 33.1 is a packet for `𝒬_RR`**, the same clauses, with
    Proposition 22.10 item 6. -/
theorem exportRR_packet :
    exportRR.cycle = Cycle.cycle (sourceQ [true, true]) (reportQ axiomPolicy [true, true])
      (nextQ axiomPolicy [true, true], certQ axiomPolicy [true, true]) ∧
    exportRR.cycle = .assimilated (nextQ axiomPolicy [true, true]) (certQ axiomPolicy [true, true]) ∧
    (reportQ axiomPolicy [true, true]).status = TermStatus.singleton ∧
    (reportQ axiomPolicy [true, true]).Sh = XRR7.active ∧
    Snap.snap axiomPolicy (X0 [true, true]) (X0_seeded _) hQ_pos (ledgerQ axiomPolicy [true, true]) =
      some (certQ axiomPolicy [true, true]).snapped ∧
    exportRR.faceState = Incidence.recordFace (nextQ axiomPolicy [true, true]) (targetQ [true, true]) exportRR.ledger ∧
    exportRR.archFaces = exportRR.ledger ∧
    (eventsRR.map (pktQ axiomPolicy [true, true] actsRR)).map (·.input) = eventsRR.map (·.toInput (targetQ [true, true])) ∧
    exportRR.archFaces.map (·.id.event) = attachedEvents eventsRR ∧
    attachedEvents eventsRR = [1, 2, 3, 4, 5, 6, 7] ∧
    exportRR.archFaces.length = 7 ∧
    (∀ r ∈ exportRR.archFaces, r.packet.cycle = certQ axiomPolicy [true, true] ∧
      r.target = targetQ [true, true] ∧ r.prov = provQ [true, true]) ∧
    (∀ ev ∈ exportRR.lifeLedger, ev.1.1 ∈ exportRR.archFaces.map (·.id)) ∧
    exportRR.releases = [] := by
  have hst : (reportQ axiomPolicy [true, true]).status = TermStatus.singleton := by
    change termStatus (Term axiomPolicy (X0 [true, true]) (X0_seeded _)).active.length = _
    rw [axiomPolicy_XRR7]
    exact prop_22_10_RR.1
  have hlen : (ensemble (TQ axiomPolicy [true, true]) (ledgerQ axiomPolicy [true, true])).length = 1 := by
    unfold ledgerQ TQ
    rw [axiomPolicy_XRR7]
    decide
  have hev : exportRR.archFaces.map (·.id.event) = attachedEvents eventsRR := exportQ_events _ _ _ _
  have hlen7 : exportRR.archFaces.length = 7 := by
    rw [← List.length_map (f := fun r : FR => r.id.event), hev, prop_22_10_RR.2.2.2.1]
    rfl
  refine ⟨?_, rfl, hst, ?_, snapQ _ _ hlen, rfl, exportQ_archFaces _ _ _ _, ?_, hev,
    prop_22_10_RR.2.2.2.1, hlen7, ?_, fun ev hev' => (exportRR.life_in_arch ev hev').1, rfl⟩
  · show _ = Cycle.cycle _ _ _
    unfold Cycle.cycle
    rw [hst]
    rfl
  · change (Term axiomPolicy (X0 [true, true]) (X0_seeded _)).active = _
    rw [axiomPolicy_XRR7]
  · rw [List.map_map]; rfl
  · unfold exportRR
    rw [exportQ_archFaces]
    exact ledgerFacesQ_cert _ _ _ _

/-- The supports of `𝒬_ε^L` and `𝒬_ε^R` at ticks `1..7` (Theorem 16.8). -/
def actsSideL : List (List QuestionId) :=
  [XepsSideL1.active, XepsSideL2.active, XepsSideL3.active, XepsSideL4.active,
   XepsSideL5.active, XepsSideL6.active, XepsSideL7.active]
def actsSideR : List (List QuestionId) :=
  [XepsSideR1.active, XepsSideR2.active, XepsSideR3.active, XepsSideR4.active,
   XepsSideR5.active, XepsSideR6.active, XepsSideR7.active]

/-- **The export packet of `𝒬_ε^L`**: the same construction as `exportLL`, on
    the root seed carrier under the side schedule `sidePolicyL`. -/
def exportSideL := exportQ sidePolicyL [] actsSideL eventsSideL
/-- **The export packet of `𝒬_ε^R`.** -/
def exportSideR := exportQ sidePolicyR [] actsSideR eventsSideR

set_option maxRecDepth 200000 in
/-- **Definition 33.1 is a packet for `𝒬_ε^L`** (Proposition 22.10 item 3),
    the same clauses as `exportLL_packet`, on the side schedule `sidePolicyL`:
    the cycle outcome is the question's total cycle evaluation, assimilated
    with `C^cyc`; the report is singleton with the support of Theorem 16.8's
    run `XepsSideL7`; the certificate's snap is the question's snap; the face state is
    the next state with this ledger recorded at the socket target; the ledger's
    packets are built at exactly the events of item 3, its faces are those of
    the attached events `2..7` (event 1 refused one hand, so no face), six of
    them, each carrying the certificate, the target and the provenance; every
    lifecycle event names an archived face and nothing is released. -/
theorem exportSideL_packet :
    exportSideL.cycle = Cycle.cycle (sourceQ []) (reportQ sidePolicyL [])
      (nextQ sidePolicyL [], certQ sidePolicyL []) ∧
    exportSideL.cycle = .assimilated (nextQ sidePolicyL []) (certQ sidePolicyL []) ∧
    (reportQ sidePolicyL []).status = TermStatus.singleton ∧
    (reportQ sidePolicyL []).Sh = XepsSideL7.active ∧
    Snap.snap sidePolicyL (X0 []) (X0_seeded _) hQ_pos (ledgerQ sidePolicyL []) =
      some (certQ sidePolicyL []).snapped ∧
    exportSideL.faceState = Incidence.recordFace (nextQ sidePolicyL []) (targetQ []) exportSideL.ledger ∧
    exportSideL.archFaces = exportSideL.ledger ∧
    (eventsSideL.map (pktQ sidePolicyL [] actsSideL)).map (·.input) = eventsSideL.map (·.toInput (targetQ [])) ∧
    exportSideL.archFaces.map (·.id.event) = attachedEvents eventsSideL ∧
    attachedEvents eventsSideL = [2, 3, 4, 5, 6, 7] ∧
    exportSideL.archFaces.length = 6 ∧
    (∀ r ∈ exportSideL.archFaces, r.packet.cycle = certQ sidePolicyL [] ∧
      r.target = targetQ [] ∧ r.prov = provQ []) ∧
    (∀ ev ∈ exportSideL.lifeLedger, ev.1.1 ∈ exportSideL.archFaces.map (·.id)) ∧
    exportSideL.releases = [] := by
  have hst : (reportQ sidePolicyL []).status = TermStatus.singleton := by
    change termStatus (Term sidePolicyL (X0 []) (X0_seeded _)).active.length = _
    rw [sidePolicyL_XepsSideL7]
    exact prop_22_10_sideL.1
  have hlen : (ensemble (TQ sidePolicyL []) (ledgerQ sidePolicyL [])).length = 1 := by
    unfold ledgerQ TQ
    rw [sidePolicyL_XepsSideL7]
    decide
  have hev : exportSideL.archFaces.map (·.id.event) = attachedEvents eventsSideL := exportQ_events _ _ _ _
  have hlen6 : exportSideL.archFaces.length = 6 := by
    rw [← List.length_map (f := fun r : FR => r.id.event), hev, prop_22_10_sideL.2.2.2.2.1]
    rfl
  refine ⟨?_, rfl, hst, ?_, snapQ _ _ hlen, rfl, exportQ_archFaces _ _ _ _, ?_, hev,
    prop_22_10_sideL.2.2.2.2.1, hlen6, ?_, fun ev hev' => (exportSideL.life_in_arch ev hev').1, rfl⟩
  · show _ = Cycle.cycle _ _ _
    unfold Cycle.cycle
    rw [hst]
    rfl
  · change (Term sidePolicyL (X0 []) (X0_seeded _)).active = _
    rw [sidePolicyL_XepsSideL7]
  · rw [List.map_map]; rfl
  · unfold exportSideL
    rw [exportQ_archFaces]
    exact ledgerFacesQ_cert _ _ _ _

set_option maxRecDepth 200000 in
/-- **Definition 33.1 is a packet for `𝒬_ε^R`** (Proposition 22.10 item 4),
    the same clauses as `exportLL_packet`, on the side schedule `sidePolicyR`:
    the cycle outcome is the question's total cycle evaluation, assimilated
    with `C^cyc`; the report is singleton with the support of Theorem 16.8's
    run `XepsSideR7`; the certificate's snap is the question's snap; the face state is
    the next state with this ledger recorded at the socket target; the ledger's
    packets are built at exactly the events of item 4, its faces are those of
    the attached events `2..7` (event 1 refused one hand, so no face), six of
    them, each carrying the certificate, the target and the provenance; every
    lifecycle event names an archived face and nothing is released. -/
theorem exportSideR_packet :
    exportSideR.cycle = Cycle.cycle (sourceQ []) (reportQ sidePolicyR [])
      (nextQ sidePolicyR [], certQ sidePolicyR []) ∧
    exportSideR.cycle = .assimilated (nextQ sidePolicyR []) (certQ sidePolicyR []) ∧
    (reportQ sidePolicyR []).status = TermStatus.singleton ∧
    (reportQ sidePolicyR []).Sh = XepsSideR7.active ∧
    Snap.snap sidePolicyR (X0 []) (X0_seeded _) hQ_pos (ledgerQ sidePolicyR []) =
      some (certQ sidePolicyR []).snapped ∧
    exportSideR.faceState = Incidence.recordFace (nextQ sidePolicyR []) (targetQ []) exportSideR.ledger ∧
    exportSideR.archFaces = exportSideR.ledger ∧
    (eventsSideR.map (pktQ sidePolicyR [] actsSideR)).map (·.input) = eventsSideR.map (·.toInput (targetQ [])) ∧
    exportSideR.archFaces.map (·.id.event) = attachedEvents eventsSideR ∧
    attachedEvents eventsSideR = [2, 3, 4, 5, 6, 7] ∧
    exportSideR.archFaces.length = 6 ∧
    (∀ r ∈ exportSideR.archFaces, r.packet.cycle = certQ sidePolicyR [] ∧
      r.target = targetQ [] ∧ r.prov = provQ []) ∧
    (∀ ev ∈ exportSideR.lifeLedger, ev.1.1 ∈ exportSideR.archFaces.map (·.id)) ∧
    exportSideR.releases = [] := by
  have hst : (reportQ sidePolicyR []).status = TermStatus.singleton := by
    change termStatus (Term sidePolicyR (X0 []) (X0_seeded _)).active.length = _
    rw [sidePolicyR_XepsSideR7]
    exact prop_22_10_sideR.1
  have hlen : (ensemble (TQ sidePolicyR []) (ledgerQ sidePolicyR [])).length = 1 := by
    unfold ledgerQ TQ
    rw [sidePolicyR_XepsSideR7]
    decide
  have hev : exportSideR.archFaces.map (·.id.event) = attachedEvents eventsSideR := exportQ_events _ _ _ _
  have hlen6 : exportSideR.archFaces.length = 6 := by
    rw [← List.length_map (f := fun r : FR => r.id.event), hev, prop_22_10_sideR.2.2.2.2.1]
    rfl
  refine ⟨?_, rfl, hst, ?_, snapQ _ _ hlen, rfl, exportQ_archFaces _ _ _ _, ?_, hev,
    prop_22_10_sideR.2.2.2.2.1, hlen6, ?_, fun ev hev' => (exportSideR.life_in_arch ev hev').1, rfl⟩
  · show _ = Cycle.cycle _ _ _
    unfold Cycle.cycle
    rw [hst]
    rfl
  · change (Term sidePolicyR (X0 []) (X0_seeded _)).active = _
    rw [sidePolicyR_XepsSideR7]
  · rw [List.map_map]; rfl
  · unfold exportSideR
    rw [exportQ_archFaces]
    exact ledgerFacesQ_cert _ _ _ _

end Concrete

end Export
end Two
end RatioSpace
