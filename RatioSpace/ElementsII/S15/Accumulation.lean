/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S12.RunInvariant
/-!
  Elements II §15 — Finite accumulation and the seven-tick specialization.

  **The one real engineering decision in this file, made explicit up front.**
  `advanceCarrier` (§11) is a single step: it takes an explicit selector,
  stratum, provenance and event delta for *that* tick, plus two proof
  obligations tied to that specific choice. "The finite iterate" of Definition
  15.1 needs one such choice *per tick*, and each tick's choice depends on the
  carrier the previous ticks actually reached — a schedule, not a fixed
  parameter reused `n` times.

  The book's own account of this file suggested a dependent sequence
  `(n : ℕ) → (hn : n < h) → AdvanceData ... (iterate n hn)`, built by
  well-founded recursion. What is built here instead is a **policy**:
  `Policy Aux h := (X : TickCarrier Aux h) → Lawful X → AdvanceData Aux h X`,
  a single total function from *any* lawful carrier to the advance data for
  its next tick. This is not a narrowing. A policy is at least as general as
  the dependent sequence — the reached carrier already carries its own tick
  number as a field, so indexing by the carrier subsumes indexing by `n` — and
  it turns the recursion that builds `iterate` into a plain structural
  recursion on `n` (`Nat.rec`), which unfolds by `rfl` at each step. The
  dependent-sequence shape would have needed the same content threaded through
  a manual well-founded fixpoint for no additional generality. Recorded here
  because the task brief asked for either the suggested shape or a documented,
  honest deviation, and this is the deviation: same content, a cleaner
  recursion.

  **Two further obligations were added to the per-step data, and both are
  genuine new content, not restatements.** `advanceCarrier`'s own `select` is
  a bare function with no cardinality bound — Advance.lean's own comment says
  the selector "is a parameter, and that is faithful" — so nothing in §11–§14
  forces `|S_{j+1}| ≤ 2|S_j|` (Theorem 8.8's growth bound, at the level
  `Coherence.lean` builds it, is a fact about `List IPres`, a different type
  from the `List QuestionId` this file's carriers use for `active`). Corollary
  15.3 needs that bound at *this* level, so `AdvanceData.hgrow` states it as an
  obligation on the selector, exactly the translation Theorem 8.8's own proof
  shape licenses. Symmetrically, Corollary 12.2's `|ℋ_{j+1}| = |ℋ_j| + 2|S_j|`
  is proved in `Advance.lean` (`archive_growth`) with `|S_j|` read as
  `(archive.filter (fun c => c.id ∈ active)).length`, the exact count of
  archived cores an active identifier tags — not `active.length` itself,
  unless every active identifier tags exactly one archived core. `TickCarrier`
  never asserts that (unlike `active_sub_archive`, which *is* a field).
  `AdvanceData.hcard` names it. Both are natural, expected properties of any
  advance actually built from Construction Axiom II.1 and Definition 7.1; they
  were simply never needed as hypotheses before this section, because nothing
  before §15 asked for arithmetic in `|S_j|` itself rather than in
  `|P_{j+1}|` or `|ℋ_j|`.

  **Theorem 15.5's carrier-level covariance is not built, and is not invented
  here either.** §13's own scoping note in `Advance.lean` says outright that
  assembling the archive/proposal-level covariance facts into a full
  `TickCarrier`-level `Z_u`/`P` action is future work needing "the carrier
  advance rather than the archive advance" — and grepping this tree for any
  definition of a prefix-transport or side-exchange action *on* `TickCarrier`
  finds none. So 15.5 below proves the sharpest true statement the existing
  machinery supports: prefix-transport covariance at the occurrence level
  (which, via `transportProposal_fullMatrix`, already holds at *arbitrary*
  descendant depth, not merely after one tick — sharper than the boxed
  statement, not weaker), and side-exchange neutrality of proposal generation
  at every tick the trace visits. Flagged rather than papered over.
-/

namespace RatioSpace
namespace Two
namespace Accumulation

open Mat2 Word Frame Pres RatioSpace Advance Conservation

/-! ## Definition 15.1 — Finite iterate and complete carrier trace -/

/-- **Definition 15.1, the per-tick data `𝔎_𝒞` actually needs.**
    `advanceCarrier`'s six explicit parameters and two proof obligations,
    bundled so a schedule can supply one packet per tick. `hgrow` and `hcard`
    are not part of `advanceCarrier` itself; they are the extra content
    Corollary 15.3 needs and this file's header explains. -/
structure AdvanceData (Aux : Type) (h : ℕ) (X : TickCarrier Aux h) where
  /-- Construction Axiom II.1 composed with Definitions 11.3–11.5, supplied by
      the caller because the declared predicate is the observer's own. -/
  select : List (Core × Bool) → List QuestionId
  /-- The event stratum this tick writes. -/
  stratum : ℕ
  /-- The provenance every child proposed at this tick receives. -/
  prov : Provenance
  /-- `Δℰ_{j+1}`, this tick's event delta. -/
  Δ : List (QuestionId × Aux)
  /-- `select` proposes only from among the tick's actual proposals. -/
  hsel : ∀ i ∈ select (proposals X.archive X.active),
    ∃ p ∈ proposals X.archive X.active, (childCore p.1 p.2 stratum prov).id = i
  /-- Lemma 12.1: every child identifier this tick creates is fresh. -/
  hfresh : ∀ p ∈ proposals X.archive X.active,
    (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive
  /-- Theorem 8.8's growth bound, translated to this level: the new support
      never exceeds twice the old one. Not implied by `hsel`/`hfresh`, which
      say nothing about cardinality. -/
  hgrow : (select (proposals X.archive X.active)).length ≤ 2 * X.active.length
  /-- Every active identifier tags exactly one archived core — the reading of
      `S_j` as a genuine finite *set* that Corollary 12.2's count silently
      assumes. Not a `TickCarrier` field, so it is asked here. -/
  hcard : (X.archive.filter (fun c => c.id ∈ X.active)).length = X.active.length
  /-- **The one obligation Theorem 17.7's iff-direction was still missing**
      (`Terminal.lean`, `Two/Carrier.lean`'s `ensemble_length_eq_active`). Every
      other field of this structure already forces the archive to stay
      duplicate-free at the next tick (`Advance.lean`'s `advanceArchive_nodup`,
      using well-formedness alone) — the active support has no such automatic
      guarantee, because `select` is a bare function on proposals with no
      cardinality or distinctness constraint of its own. Construction Axiom
      II.1 already returns a *set*, so any advance actually built from it
      satisfies this without effort; it was simply never asked for before
      nothing needed arithmetic in `|S_{j+1}|` itself. -/
  hselNodup : (select (proposals X.archive X.active)).Nodup

/-- **The three-part invariant an iterate needs.** The archive's identifiers
    stay duplicate-free, every archived core stays well-formed (needed for the
    first clause to propagate at all — `Advance.lean`'s `advanceArchive_nodup`
    and `advanceArchive_wellFormed`), and the active support stays
    duplicate-free (`AdvanceData.hselNodup`, the one clause with no automatic
    guarantee). -/
def CarrierInv {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) : Prop :=
  (X.archive.map Core.id).Nodup ∧ (∀ c ∈ X.archive, c.WellFormed) ∧ X.active.Nodup

/-- **One tick preserves the invariant.** Archive duplicate-freedom and
    well-formedness come from `Advance.lean`'s two preservation lemmas, needing
    nothing new; the active support's duplicate-freedom is exactly
    `AdvanceData.hselNodup`, read off directly since `advanceCarrier`'s own
    `active` field is `D.select (proposals X.archive X.active)` by
    definition. -/
theorem advanceCarrier_carrierInv {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (D : AdvanceData Aux h X) (hinv : CarrierInv X) :
    CarrierInv (advanceCarrier X hlaw D.select D.stratum D.prov D.Δ D.hsel D.hfresh) := by
  obtain ⟨hnodup, hwf, hact⟩ := hinv
  exact ⟨advanceArchive_nodup hnodup hwf, advanceArchive_wellFormed hwf, D.hselNodup⟩

/-- **The carriers the book's dynamics reach.** Definition 15.1 starts every
    iterate from "the valid tick-zero carrier constructed from the support-free
    initialization context of Section 4" and reaches every later carrier by
    lawful ticks. Every such carrier has a duplicate-free, well-formed archive
    and a duplicate-free support (`CarrierInv`: occurrence identity is retained,
    Corollary 6.10, and the archive is keyed, Definition 11.6), and Lemma
    12.1's depth invariant (`TickLengthInv`: archived words no longer than the
    tick, active words exactly the tick). A carrier whose active list repeats
    one identifier, or whose support sits at mixed depths, is a well-typed
    `TickCarrier` that no run from a seed produces. -/
def RunInv {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) : Prop :=
  CarrierInv X ∧ Gaps.G2_13.TickLengthInv X

/-- **A valid tick-zero carrier**: tick zero, and the run invariant, which at
    tick zero says the archive holds seeds only (`seeded_of_seeds`).

    Some theorems stated before this definition existed still take
    `hinv0 : CarrierInv X0` or `hinv0 : TickLengthInv X0` beside `hX0`
    (`iterate_carrierInv`, `G2_13.iterate_tickLengthInv`,
    `Terminal.crystallize_isSome_iff_singleton_of_carrierInv`, the `G2_16` and
    `G2_17` snap theorems). `hX0.2.1` and `hX0.2.2` supply them; they are kept
    only so no existing signature changes, and ask nothing beyond `Seeded`. -/
def Seeded {Aux : Type} {h : ℕ} (X0 : TickCarrier Aux h) : Prop :=
  (X0.tick : ℕ) = 0 ∧ RunInv X0

/-- **One tick preserves the run invariant.** `CarrierInv` by
    `advanceCarrier_carrierInv`; Lemma 12.1's invariant by
    `tickLengthInv_advanceCarrier`, whatever proof of freshness was used. -/
theorem advanceCarrier_runInv {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (D : AdvanceData Aux h X) (hinv : RunInv X) :
    RunInv (advanceCarrier X hlaw D.select D.stratum D.prov D.Δ D.hsel D.hfresh) :=
  ⟨advanceCarrier_carrierInv X hlaw D hinv.1,
    Gaps.G2_13.tickLengthInv_advanceCarrier X hlaw _ _ _ _ _ _ hinv.2⟩

/-- **A seed archive at tick zero is a valid tick-zero carrier.** Duplicate-free
    well-formed cores with empty relative words, and a duplicate-free support. -/
theorem seeded_of_seeds {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (h0 : (X.tick : ℕ) = 0) (hnd : (X.archive.map Core.id).Nodup)
    (hwf : ∀ c ∈ X.archive, c.WellFormed) (hseed : ∀ c ∈ X.archive, c.relWord = [])
    (hact : X.active.Nodup) : Seeded X :=
  ⟨h0, ⟨hnd, hwf, hact⟩, Gaps.G2_13.tickLengthInv_of_seeds X h0 hwf hseed⟩

/-- **On a reached carrier, `hcard` is a theorem.** -/
theorem RunInv.hcard {Aux : Type} {h : ℕ} {X : TickCarrier Aux h} (hX : RunInv X) :
    (X.archive.filter (fun c => c.id ∈ X.active)).length = X.active.length :=
  Gaps.G2_13.hcard_of_nodup X hX.1.1 hX.1.2.2

/-- **On a reached carrier, `hfresh` is a theorem** (Lemma 12.1), for every
    stratum and provenance. -/
theorem RunInv.hfresh {Aux : Type} {h : ℕ} {X : TickCarrier Aux h} (hX : RunInv X)
    (stratum : ℕ) (prov : Provenance) :
    ∀ p ∈ proposals X.archive X.active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive :=
  Gaps.G2_13.hfresh_of_tickLengthInv X hX.2 stratum prov

/-- **Definition 15.1, a schedule.** One `AdvanceData` for every lawful carrier
    the book's dynamics reach (`RunInv`), not merely for `n` values
    `0, ..., h_𝒬 - 1`: the carrier a schedule reaches already carries its own
    tick, so indexing by the carrier is at least as general as indexing by `n`,
    and it is what makes `iterate` below a plain structural recursion.

    Asking for `AdvanceData` at *every* lawful `TickCarrier` (the earlier form
    of this definition) asked for it at carriers no run produces, such as one
    whose support lists one identifier twice; `hcard` fails there, so that type
    was empty (audit 2026-09-26, E2-D1). Restricted to reached carriers it is
    inhabited: `emptyPolicy` below, and Construction Axiom II.1 itself
    (`AxiomPolicy.axiomPolicy`). -/
def Policy (Aux : Type) (h : ℕ) : Type :=
  (X : TickCarrier Aux h) → Lawful X → RunInv X → AdvanceData Aux h X

/-- **A schedule exists at every question and horizon**: the one that retains
    no support. It is not the book's rule; it is here so that the type every
    general §15-§20 theorem quantifies over is shown inhabited in the file that
    defines it. The book's rule is `AxiomPolicy.axiomPolicy`. -/
def emptyPolicy (Aux : Type) (h : ℕ) : Policy Aux h := fun X _ hX =>
  { select := fun _ => []
    stratum := (X.tick : ℕ) + 1
    prov := ⟨⟨0, 0, 0, []⟩, ⟨0, 0, 0, []⟩, ⟨0, 0⟩⟩
    Δ := []
    hsel := fun _ hi => absurd hi List.not_mem_nil
    hfresh := hX.hfresh _ _
    hgrow := Nat.zero_le _
    hcard := hX.hcard
    hselNodup := List.nodup_nil }

/-- Standing guard (audit rule 1): the schedule type is inhabited. -/
example (Aux : Type) (h : ℕ) : Nonempty (Policy Aux h) := ⟨emptyPolicy Aux h⟩

/-- **Definition 15.1, the finite iterate, bundled with the proof that it
    reaches tick `n`.** Structural recursion on `n`: the base case is the
    given tick-zero carrier, and the successor case advances the previous
    carrier by whatever the policy supplies at it, using that its tick is
    `n < h` — which the bundled proof at the previous step already gives. -/
def iterateWithTick {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) :
    (n : ℕ) → n ≤ h → {X : TickCarrier Aux h // (X.tick : ℕ) = n ∧ RunInv X}
  | 0, _ => ⟨X0, hX0.1, hX0.2⟩
  | n + 1, hn =>
      let prev := iterateWithTick pol X0 hX0 n (Nat.le_of_succ_le hn)
      have hlaw : Lawful prev.1 := by
        unfold Lawful
        rw [prev.2.1]
        omega
      let D := pol prev.1 hlaw prev.2.2
      ⟨advanceCarrier prev.1 hlaw D.select D.stratum D.prov D.Δ D.hsel D.hfresh,
        by rw [advanceCarrier_tick, prev.2.1], advanceCarrier_runInv prev.1 hlaw D prev.2.2⟩

/-- **Definition 15.1, `𝔎_𝒞^n(𝔛_{τ,0})`.** The finite iterate as a plain
    function of `n ≤ h_𝒬`. -/
def iterate {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) : TickCarrier Aux h :=
  (iterateWithTick pol X0 hX0 n hn).1

/-- The iterate at `n` really has tick `n`. -/
theorem iterate_tick {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) :
    ((iterate pol X0 hX0 n hn).tick : ℕ) = n :=
  (iterateWithTick pol X0 hX0 n hn).2.1

/-- **Every carrier a schedule reaches is one the book's dynamics reach.** -/
theorem iterate_runInv {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) : RunInv (iterate pol X0 hX0 n hn) :=
  (iterateWithTick pol X0 hX0 n hn).2.2

@[simp] theorem iterate_zero {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (hn : (0 : ℕ) ≤ h) : iterate pol X0 hX0 0 hn = X0 := rfl

/-- A lawful carrier is exactly what the previous tick's iterate is, one step
    below the horizon. -/
theorem iterate_lawful {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n + 1 ≤ h) :
    Lawful (iterate pol X0 hX0 n (Nat.le_of_succ_le hn)) := by
  unfold Lawful
  rw [iterate_tick]
  omega

/-- The policy's own choice at the carrier `iterate n` reached along this
    particular schedule, named once so `iterate_succ` and everything after it
    can cite it rather than re-applying `pol`. -/
def stepData {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n + 1 ≤ h) :
    AdvanceData Aux h (iterate pol X0 hX0 n (Nat.le_of_succ_le hn)) :=
  pol (iterate pol X0 hX0 n (Nat.le_of_succ_le hn)) (iterate_lawful pol X0 hX0 n hn)
    (iterate_runInv pol X0 hX0 n (Nat.le_of_succ_le hn))

/-- **Definition 15.1, `𝔎_𝒞^{n+1}(𝔛_{τ,0}) = 𝔎_𝒞(𝔎_𝒞^n(𝔛_{τ,0}))`, made
    literal.** Holds by `rfl`: proofs of `Lawful` are interchangeable by
    `Prop` proof irrelevance, so the policy's internal choice inside
    `iterateWithTick` and `stepData`'s named copy of it are the same term. -/
theorem iterate_succ {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n + 1 ≤ h) :
    iterate pol X0 hX0 (n + 1) hn =
      advanceCarrier (iterate pol X0 hX0 n (Nat.le_of_succ_le hn)) (iterate_lawful pol X0 hX0 n hn)
        (stepData pol X0 hX0 n hn).select (stepData pol X0 hX0 n hn).stratum
        (stepData pol X0 hX0 n hn).prov (stepData pol X0 hX0 n hn).Δ
        (stepData pol X0 hX0 n hn).hsel (stepData pol X0 hX0 n hn).hfresh := rfl

/-- **Definition 15.1, the complete carrier trace `Trace_𝒬^{(n)}`.** The finite
    sequence `(𝔛_{τ,0}, ..., 𝔛_{τ,n})`, each entry a complete `TickCarrier` —
    so the active support, occurrence archive and event ledger at every
    position are retained by construction, and nothing further is owed here
    for that clause of Definition 15.1. -/
def trace {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) : List (TickCarrier Aux h) :=
  List.ofFn (fun k : Fin (n + 1) => iterate pol X0 hX0 k.1 (le_trans (Nat.le_of_lt_succ k.2) hn))

/-- `Trace_𝒬^{(n)}` has exactly `n + 1` entries, `𝔛_{τ,0}` through `𝔛_{τ,n}`. -/
theorem trace_length {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) :
    (trace pol X0 hX0 n hn).length = n + 1 :=
  List.length_ofFn

/-! ## Duplicate-freedom along a whole schedule

    The genuine gap Theorem 17.7's iff-direction (`Terminal.lean`) named: it
    needed the *terminal* carrier's archive and active support both
    duplicate-free, proved there only as a hypothesis on whichever carrier was
    supplied, because nothing before asked whether an *iterated* carrier keeps
    either property. `CarrierInv` is the invariant that answers it, carried
    from the tick-zero carrier forward by `iterate_carrierInv` rather than
    assumed at the far end of a schedule no one can inspect in the abstract. -/

/-- **The invariant holds at every tick a schedule reaches**, given it holds at
    tick zero — the schedule-length induction `research/lean-support/README.md`
    named as the remaining gap, threading `hselNodup` (and, unexpectedly,
    well-formedness rather than `hcard`) forward from `X0` instead of asking
    for it at the terminal carrier directly. -/
theorem iterate_carrierInv {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (hinv0 : CarrierInv X0) (n : ℕ) (hn : n ≤ h) :
    CarrierInv (iterate pol X0 hX0 n hn) := by
  induction n with
  | zero => simpa using hinv0
  | succ k ih =>
      rw [iterate_succ]
      exact advanceCarrier_carrierInv _ (iterate_lawful pol X0 hX0 k hn) (stepData pol X0 hX0 k hn)
        (ih (Nat.le_of_succ_le hn))

#print axioms iterate_carrierInv

/-! ## Theorem 15.2 — General finite accumulation -/

/-- **Theorem 15.2.** *"For every valid tick-zero carrier and every `n`
    satisfying `0 ≤ n ≤ h_𝒬`, the iterate `𝔎_𝒞^n(𝔛_{τ,0})` exists uniquely and
    belongs to `𝔈_{𝒬,n}`."*

    Existence is `iterate` being total on `{n // n ≤ h}` — it is a function
    defined for every such `n`, with no partiality. Uniqueness needs no
    separate proof: `iterate` is a function of `pol`, `X0`, `hX0` and `n`, and
    a function gives one output on one input by the meaning of "function" in a
    total dependent type theory, exactly the freeness the account of
    Proposition 11.7 already named for one step. What is left to state is
    membership: `𝔈_{𝒬,n}` is exactly the carriers with tick `n`, which
    `iterate_tick` gives. The base case, `n = 0`, is `iterate_zero` together
    with the hypothesis `hX0` that `X0` is already a valid tick-zero carrier;
    the inductive step is `iterate_succ` composed with Theorem 12.4
    (`advanceCarrier_tick`), already proved and cited rather than repeated. -/
theorem finite_accumulation {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) :
    ((iterate pol X0 hX0 n hn).tick : ℕ) = n :=
  iterate_tick pol X0 hX0 n hn

/-! ## Corollary 15.3 — Exact accumulated archive size and finite bounds -/

/-- The archive length reached at tick `n` along one schedule. -/
def archLen {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) : ℕ :=
  (iterate pol X0 hX0 n hn).archive.length

/-- The active-support length reached at tick `n` along one schedule. -/
def activeLen {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) : ℕ :=
  (iterate pol X0 hX0 n hn).active.length

/-- `Σ_{j=0}^{n-1} |S_j|`, a `ℕ`-recursive sum matching how `S_j` is typed
    here (`List QuestionId`, so a length, not a `Finset` cardinality). -/
def sumActiveLen {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) : (n : ℕ) → n ≤ h → ℕ
  | 0, _ => 0
  | k + 1, hk =>
      sumActiveLen pol X0 hX0 k (Nat.le_of_succ_le hk)
        + activeLen pol X0 hX0 k (Nat.le_of_succ_le hk)

/-- `sumActiveLen`'s own successor equation, isolated so later proofs rewrite
    with it directly instead of a blanket `unfold` (which gets stuck on the
    recursive call's own non-literal argument). -/
theorem sumActiveLen_succ {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n + 1 ≤ h) :
    sumActiveLen pol X0 hX0 (n + 1) hn
      = sumActiveLen pol X0 hX0 n (Nat.le_of_succ_le hn)
        + activeLen pol X0 hX0 n (Nat.le_of_succ_le hn) := rfl

/-- **Corollary 12.2, at one step of the schedule, exactly.** `AdvanceData`'s
    `hcard` is exactly what turns `archive_growth`'s
    `(archive.filter (· ∈ active)).length` into `active.length`. -/
theorem step_archive_length {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (D : AdvanceData Aux h X) :
    (advanceArchive X.archive X.active D.stratum D.prov).length
      = X.archive.length + 2 * X.active.length := by
  rw [archive_growth X.archive X.active D.stratum D.prov D.hfresh, D.hcard]

/-- The archive half of `step_archive_length`, read at the whole carrier. -/
theorem step_archive_length' {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) (hlaw : Lawful X)
    (D : AdvanceData Aux h X) :
    (advanceCarrier X hlaw D.select D.stratum D.prov D.Δ D.hsel D.hfresh).archive.length
      = X.archive.length + 2 * X.active.length :=
  step_archive_length X D

/-- **`AdvanceData.hgrow`, at the whole carrier.** The support half of
    Theorem 8.8's growth bound, translated to this level, read off the
    advance directly. -/
theorem step_active_length_bound {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) (hlaw : Lawful X)
    (D : AdvanceData Aux h X) :
    (advanceCarrier X hlaw D.select D.stratum D.prov D.Δ D.hsel D.hfresh).active.length
      ≤ 2 * X.active.length :=
  D.hgrow

/-- The archive-length recursion along one schedule: `|ℋ_{j+1}| = |ℋ_j| +
    2|S_j|`, Corollary 12.2 pushed through `iterate`. -/
theorem archLen_succ {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n + 1 ≤ h) :
    archLen pol X0 hX0 (n + 1) hn
      = archLen pol X0 hX0 n (Nat.le_of_succ_le hn)
        + 2 * activeLen pol X0 hX0 n (Nat.le_of_succ_le hn) := by
  unfold archLen activeLen
  rw [iterate_succ pol X0 hX0 n hn]
  exact step_archive_length' _ (iterate_lawful pol X0 hX0 n hn) (stepData pol X0 hX0 n hn)

/-- The active-length bound along one schedule: `|S_{j+1}| ≤ 2|S_j|`. -/
theorem activeLen_succ_le {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n + 1 ≤ h) :
    activeLen pol X0 hX0 (n + 1) hn ≤ 2 * activeLen pol X0 hX0 n (Nat.le_of_succ_le hn) := by
  unfold activeLen
  rw [iterate_succ pol X0 hX0 n hn]
  exact step_active_length_bound _ (iterate_lawful pol X0 hX0 n hn) (stepData pol X0 hX0 n hn)

/-- **Corollary 15.3, first display.** `|ℋ_n| = |ℋ_0| + 2·Σ_{j=0}^{n-1}|S_j|`,
    the empty sum at `n = 0` being `sumActiveLen`'s own base case. -/
theorem archLen_telescopes {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) :
    ∀ (n : ℕ) (hn : n ≤ h),
      archLen pol X0 hX0 n hn
        = archLen pol X0 hX0 0 (Nat.zero_le h) + 2 * sumActiveLen pol X0 hX0 n hn
  | 0, hn => by simp [sumActiveLen]
  | k + 1, hn => by
      have hk : k ≤ h := Nat.le_of_succ_le hn
      have ih := archLen_telescopes pol X0 hX0 k hk
      rw [archLen_succ pol X0 hX0 k hn, ih, sumActiveLen_succ]
      ring

/-- **Theorem 8.8's bound, iterated**: `|S_n| ≤ 2^n|S_0|`. -/
theorem activeLen_le_geom {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) :
    ∀ (n : ℕ) (hn : n ≤ h),
      activeLen pol X0 hX0 n hn ≤ 2 ^ n * activeLen pol X0 hX0 0 (Nat.zero_le h)
  | 0, hn => by simp
  | k + 1, hn => by
      have hk : k ≤ h := Nat.le_of_succ_le hn
      have hstep := activeLen_succ_le pol X0 hX0 k hn
      have ih := activeLen_le_geom pol X0 hX0 k hk
      calc activeLen pol X0 hX0 (k + 1) hn
          ≤ 2 * activeLen pol X0 hX0 k hk := hstep
        _ ≤ 2 * (2 ^ k * activeLen pol X0 hX0 0 (Nat.zero_le h)) := by omega
        _ = 2 ^ (k + 1) * activeLen pol X0 hX0 0 (Nat.zero_le h) := by ring

/-- The finite geometric sum bound on the telescoped total:
    `Σ_{j=0}^{n-1}|S_j| ≤ |S_0|(2^n − 1)`. -/
theorem sumActiveLen_le_geom {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) :
    ∀ (n : ℕ) (hn : n ≤ h),
      sumActiveLen pol X0 hX0 n hn ≤ activeLen pol X0 hX0 0 (Nat.zero_le h) * (2 ^ n - 1)
  | 0, hn => by simp [sumActiveLen]
  | k + 1, hn => by
      have hk : k ≤ h := Nat.le_of_succ_le hn
      have ih := sumActiveLen_le_geom pol X0 hX0 k hk
      have hg := activeLen_le_geom pol X0 hX0 k hk
      have hpow : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
      have hsplit : (2 : ℕ) ^ (k + 1) - 1 = (2 ^ k - 1) + 2 ^ k := by
        have : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by ring
        omega
      rw [sumActiveLen_succ, hsplit]
      calc sumActiveLen pol X0 hX0 k hk + activeLen pol X0 hX0 k hk
          ≤ activeLen pol X0 hX0 0 (Nat.zero_le h) * (2 ^ k - 1)
              + 2 ^ k * activeLen pol X0 hX0 0 (Nat.zero_le h) := Nat.add_le_add ih hg
        _ = activeLen pol X0 hX0 0 (Nat.zero_le h) * ((2 ^ k - 1) + 2 ^ k) := by ring

/-- **Corollary 15.3, second display, assembled.**
    `|ℋ_n| ≤ |ℋ_0| + 2|S_0|(2^n − 1)`. -/
theorem archLen_le_geom_bound {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) :
    archLen pol X0 hX0 n hn
      ≤ archLen pol X0 hX0 0 (Nat.zero_le h)
        + 2 * activeLen pol X0 hX0 0 (Nat.zero_le h) * (2 ^ n - 1) := by
  rw [archLen_telescopes pol X0 hX0 n hn]
  have hsum := sumActiveLen_le_geom pol X0 hX0 n hn
  have h2 : 2 * sumActiveLen pol X0 hX0 n hn
      ≤ 2 * (activeLen pol X0 hX0 0 (Nat.zero_le h) * (2 ^ n - 1)) := by omega
  calc archLen pol X0 hX0 0 (Nat.zero_le h) + 2 * sumActiveLen pol X0 hX0 n hn
      ≤ archLen pol X0 hX0 0 (Nat.zero_le h)
        + 2 * (activeLen pol X0 hX0 0 (Nat.zero_le h) * (2 ^ n - 1)) := by omega
    _ = archLen pol X0 hX0 0 (Nat.zero_le h)
        + 2 * activeLen pol X0 hX0 0 (Nat.zero_le h) * (2 ^ n - 1) := by ring

/-! ## Theorem 15.4 — Iterated exactness and history conservation

    Five clauses. Only the second needs new proof: the rest are already
    proved, at a level general enough that restating them "at the trace" is a
    citation under universal quantification, not a re-derivation. Each is kept
    as its own theorem — conjoining five statements about different ambient
    types (an arbitrary comparison family, archive membership at tick `n`, an
    arbitrary `NativeAnn`/word pair, an arbitrary word) into one `∧` would
    force an artificial common type rather than state each at its natural
    generality, so none is. -/

/-- **Theorem 15.4, clause 1.** *"Every support decision has a finite integer
    and Boolean witness."* Exactly `tie_has_integer_witness` (Theorem 12.6,
    itself Theorem 8.5's certificate), restated under this section's name
    because it governs every tick's support decision along the trace, not
    only one. No new content: the fact never referred to a specific tick. -/
theorem trace_support_decision_witness (fam : List IPres) (y z : IPres) :
    coherenceOf fam y = coherenceOf fam z
      ↔ c0 (tensions fam y) = c0 (tensions fam z)
        ∧ c1 (tensions fam y) = c1 (tensions fam z) :=
  tie_has_integer_witness fam y z

/-- **Theorem 15.4, clause 2, the one real induction in this section.**
    *"The occurrence archives and event ledgers form an increasing chain
    under `⪯_hist`: `𝔛_{τ,0} ⪯_hist 𝔛_{τ,1} ⪯_hist ... ⪯_hist 𝔛_{τ,n}`."*
    Built from `advance_histExtends` (Theorem 14.2) at each tick and
    `HistExtends.trans` composing them along the schedule — literally
    "transitivity of archive inclusion and initial-sequence extension gives
    the displayed history chain," the book's own proof, run once per gap
    rather than assumed. -/
theorem iterate_succ_histExtends {Aux : Type} {h : ℕ} (pol : Policy Aux h)
    (X0 : TickCarrier Aux h) (hX0 : Seeded X0) (n : ℕ) (hn : n + 1 ≤ h) :
    HistExtends (iterate pol X0 hX0 n (Nat.le_of_succ_le hn)) (iterate pol X0 hX0 (n + 1) hn) := by
  rw [iterate_succ pol X0 hX0 n hn]
  exact advance_histExtends (iterate pol X0 hX0 n (Nat.le_of_succ_le hn))
    (iterate_lawful pol X0 hX0 n hn)
    (stepData pol X0 hX0 n hn).select (stepData pol X0 hX0 n hn).stratum
    (stepData pol X0 hX0 n hn).prov (stepData pol X0 hX0 n hn).Δ
    (stepData pol X0 hX0 n hn).hsel (stepData pol X0 hX0 n hn).hfresh

/-- **Theorem 15.4, clause 2, assembled: the whole chain, any two positions.**
    Subsumes the displayed `𝔛_{τ,0} ⪯_hist ... ⪯_hist 𝔛_{τ,n}` — instantiate
    at consecutive `m` to read off any one arrow of it. -/
theorem iterate_histExtends {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (m : ℕ) (hm : m ≤ h) :
    ∀ (n : ℕ) (hn : n ≤ h), m ≤ n →
      HistExtends (iterate pol X0 hX0 m hm) (iterate pol X0 hX0 n hn)
  | 0, _, hmn => by
      have : m = 0 := Nat.le_zero.mp hmn
      subst this
      exact HistExtends.refl _
  | k + 1, hn, hmn => by
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · have hmk : m ≤ k := Nat.lt_succ_iff.mp hlt
        exact (iterate_histExtends pol X0 hX0 m hm k (Nat.le_of_succ_le hn) hmk).trans
          (iterate_succ_histExtends pol X0 hX0 k hn)
      · have heq : m = k + 1 := le_antisymm hmn hge
        subst heq
        exact HistExtends.refl _

/-- **Theorem 15.4, clause 3.** *"Every archived occurrence retains one exact
    ancestry to a seed."* `ancestry_reaches_seed` (Theorem 14.4) is a fact
    about `QuestionId` alone — it does not read which carrier archived the
    identifier — so restating it "for every `c` in `(iterate n).archive`" adds
    a membership binder and nothing else. Nearly free, in the sense §14's own
    account already gave Theorem 14.4 itself. -/
theorem trace_ancestry {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) :
    ∀ c ∈ (iterate pol X0 hX0 n hn).archive,
      QuestionId.parent^[c.id.rel.length] c.id = seedIdOf c.id :=
  fun c _ => ancestry_reaches_seed c.id

/-- **Theorem 15.4, clause 4.** *"Winding and the canonical twelve-class
    closure component accumulate by the exact formulas of Theorem 14.5."*
    `conservation` again does not read which schedule produced `u` or `v`, so
    this is the same citation as clause 3: the no-drift statement already
    holds along any descendant continuation, including every one this
    section's trace visits. -/
theorem trace_winding_closure_conservation {Aux : Type} (id0 : QuestionId) (seed : History)
    (u v : Word) (a : NativeAnn Aux) (hw : a.winding = bal (proposal id0 seed u).fullWord)
    (hc : a.closure = psi12 (proposal id0 seed u).fullWord) :
    (annAlong a v).winding = bal (proposal id0 seed (u ++ v)).fullWord ∧
    (annAlong a v).closure = psi12 (proposal id0 seed (u ++ v)).fullWord :=
  conservation id0 seed u v a hw hc

/-- **Theorem 15.4, clause 5.** *"No strict descendant is equal to its
    ancestor as a positive word or exact accumulated matrix."* Exactly
    `no_positive_recurrence` (Theorem 14.7), which already quantifies over any
    ancestor word `w` and any nonempty continuation `v` — so it already covers
    every ancestor/descendant pair this section's trace could ever produce,
    at any pair of tick positions, not only adjacent ones. -/
theorem trace_no_recurrence {w v : Word} (hv : v ≠ []) :
    w ++ v ≠ w ∧ Word.G w * Word.G v ≠ Word.G w :=
  no_positive_recurrence hv

/-! ## Theorem 15.5 — Covariance of every finite iterate -/

/-- **Theorem 15.5, first box (common positive prefix transport), and sharper
    than the boxed statement.** `𝔎_{Z_u𝒞}^n(Z_u𝔛_{τ,0}) = Z_u𝔎_𝒞^n(𝔛_{τ,0})`
    is a claim about the occurrence reached after `n` ticks along one
    descendant word `v`. `transportProposal_fullMatrix` (built for
    Proposition 5.7, cited again at Theorem 13.2) already proves the
    corresponding occurrence-level identity for **every** word `v`, not only
    those of length `≤ h_𝒬` reached by a lawful schedule — no induction on `n`
    needed, because the underlying fact was never bounded by the horizon in
    the first place. -/
theorem trace_prefix_covariance (u : Word) (id0 : QuestionId) (seed : History) (v : Word) :
    (proposal id0 (transportSeed u seed) v).fullMatrix = Z u (proposal id0 seed v).fullMatrix :=
  transportProposal_fullMatrix u id0 seed v

/-- **Theorem 15.5, second box (complete side exchange).**

    **Superseded 2026-09-12.** This docstring used to say that a
    `TickCarrier`-level side-exchange action `P` "is not built anywhere in this
    tree, and nothing since has supplied it". That was true when written and is
    no longer: `Two/SideExchange.lean` builds `TickCarrier.mirror` over all six
    components, and `trace_mirror_advance_perm` there lifts this box from
    proposal generation to **the advance itself, at every tick a trace visits**.

    What remains true and is kept here: both hands are proposed for every active
    occurrence, at every tick, so no one-sided outcome anywhere in the trace can
    be blamed on the hand labels. That is the statement below; the stronger one
    lives with the action it needs. -/
theorem trace_both_hands_proposed {Aux : Type} {h : ℕ} (pol : Policy Aux h)
    (X0 : TickCarrier Aux h) (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) {c : Core}
    (hc : c ∈ (iterate pol X0 hX0 n hn).archive.filter
      (fun x => x.id ∈ (iterate pol X0 hX0 n hn).active)) (g : Bool) :
    (c, g) ∈ proposals (iterate pol X0 hX0 n hn).archive (iterate pol X0 hX0 n hn).active :=
  both_hands_proposed hc g

/-- **Theorem 15.5, second box, the permutation form**, at every tick: hand
    swap permutes each tick's own proposal family, so no tick's generation
    step could have preferred a hand even in principle. -/
theorem trace_hand_swap {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (n : ℕ) (hn : n ≤ h) :
    ((proposals (iterate pol X0 hX0 n hn).archive (iterate pol X0 hX0 n hn).active).map
        (fun p => (p.1, !p.2))).Perm
      (proposals (iterate pol X0 hX0 n hn).archive (iterate pol X0 hX0 n hn).active) :=
  proposals_hand_swap _ _

/-! ## Receiver Declaration 15.6 — Distinguished construction horizon -/

/-- **Receiver Declaration 15.6.** `h_𝒬 = 7`. Not a second declaration of the
    horizon: `sevenTickHorizon` is `Cavity.lean`'s own constant for Receiver
    Declaration 4.6, and this section's horizon is the same number for the
    same reason, so it is reused rather than redeclared. -/
def hQ : ℕ := sevenTickHorizon

/-! ## Corollary 15.7 — The sevenfold terminal carrier -/

/-- **Corollary 15.7.** *"`𝔛_{τ,7} = 𝔎_𝒞^7(𝔛_{τ,0}) ∈ 𝔈_{𝒬,7}` is a unique,
    finite, integer-exact, history-bearing terminal carrier."* Exactly
    Theorem 15.2 at `n = h_𝒬`, and the proof line the book gives — "set `n=7`
    in Theorems 15.2 and 15.4" — is the whole content: no new lemma, only an
    instantiation. -/
theorem sevenfold_terminal_carrier {Aux : Type} (pol : Policy Aux hQ) (X0 : TickCarrier Aux hQ)
    (hX0 : Seeded X0) :
    ((iterate pol X0 hX0 hQ (le_refl hQ)).tick : ℕ) = hQ :=
  iterate_tick pol X0 hX0 hQ (le_refl hQ)

/-! ## Separation Rule 15.8 — The horizon is a stopping position -/

/-- **Separation Rule 15.8.** *"It is not a claim that `𝔛_{τ,7} = 𝔛_{τ,0}`,
    nor is it a fixed-point assertion."* Checked rather than asserted: the two
    carriers' tick fields differ (`7 ≠ 0`), so no schedule under any policy
    can reach `X0` again at the declared horizon. The rule's other clause,
    *"Theorem 14.7 forbids exact positive return along any nonempty descendant
    lineage,"* is `trace_no_recurrence` above, cited rather than reproved
    here — the same theorem discharges Theorem 15.4's clause 5 and this
    rule's own forbidding clause, because the book cites Theorem 14.7 for
    both. -/
theorem terminal_ne_initial {Aux : Type} (pol : Policy Aux hQ) (X0 : TickCarrier Aux hQ)
    (hX0 : Seeded X0) :
    iterate pol X0 hX0 hQ (le_refl hQ) ≠ X0 := by
  intro heq
  have h1 : ((iterate pol X0 hX0 hQ (le_refl hQ)).tick : ℕ) = hQ :=
    iterate_tick pol X0 hX0 hQ (le_refl hQ)
  rw [heq, hX0.1] at h1
  simp [hQ, sevenTickHorizon] at h1

/-! ## §16 Definition 16.1 — Terminal carrier and terminal comparison record

Stated for an arbitrary declared horizon `h`, matching the book's own
generality (`"for a question of arbitrary finite horizon h = h_𝒬"`) rather than
fixing `h := hQ` — the fixed instance is `sevenfold_terminal_carrier` above. -/

/-- **Definition 16.1, `Term_𝒬(𝔛_{τ,0}) = 𝔎_𝒞^h(𝔛_{τ,0}) = 𝔛_{τ,h}`.** Reuses
    `iterate` at `n := h`; no new recursion is needed because `iterate` is
    already total on every `n ≤ h`. -/
def Term {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) : TickCarrier Aux h :=
  iterate pol X0 hX0 h (le_refl h)

/-- `Term` really reaches tick `h`, so it is a genuine terminal carrier and not
    an arbitrary one reused under the name. -/
theorem Term_tick {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) : ((Term pol X0 hX0).tick : ℕ) = h :=
  iterate_tick pol X0 hX0 h (le_refl h)

/-- **Definition 16.1, the terminal evidence stratum `EvTerm_𝒬^{(h)}`, the
    `h > 0` case: `Δℰ_h`.** The last tick's own event delta — the stratum
    `stepData` names at `n := h - 1`, the step that produces `Term` itself.

    **The `h = 0` case is not built.** The book reads `EvTerm_𝒬^{(0)} = ℰ_0`,
    *"the exact initialized support and its seed-admission record."* No
    `SeedAdmissionRecord`-shaped type exists anywhere in this tree — nothing
    before §16 needed one, and the book's schedule is instantiated at
    `hQ = sevenTickHorizon = 7 > 0` (`AxiomPolicy.axiomPolicy`). Left as a genuine gap
    rather than papered over with the wrong branch's data. -/
def EvTerm {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (hh : 0 < h) : List (QuestionId × Aux) :=
  (stepData pol X0 hX0 (h - 1) (by omega)).Δ

/-- **Definition 16.1, the exact terminal comparison record
    `TCmp_𝒬^{(h)} = (h, S_h, EvTerm_𝒬^{(h)}, {Cand_{τ,h}(x) : x ∈ S_h})`,**
    `h > 0` case.

    **Two type parameters, not one — the same split just made in `candidate`/
    `ensemble` (`Carrier.lean`, Definition 6.4).** `evTerm`'s content is
    `EvTerm`'s raw stratum, `Δℰ_h`, typed at whatever `Aux` a real running
    `Policy` actually uses for its per-tick event data; `cand`'s content is
    `Cand EvalAux`, the *evaluated* Definition 6.3 record `assembleLedger`
    below produces. A single shared `Aux` forced these to be the same type,
    which is exactly why the 23:30 pass could not wire `Cand`/`ensemble` to a
    real `Policy` without inventing a raw event type that was secretly
    `EvalRecord`-shaped. Neither `Policy`/`AdvanceData`/`TickCarrier` nor
    `EvTerm` needed to change: none of them ever reads the evaluated ledger,
    so nothing about `Aux`'s existing meaning there was wrong, only `TCmp`'s
    reuse of one binder for two different things. -/
structure TCmp (RawAux EvalAux : Type) (h : ℕ) where
  horizon : ℕ
  Sh : List QuestionId
  evTerm : List (QuestionId × RawAux)
  cand : List (Cand EvalAux)

/-- **Definition 16.1's record, assembled**, `h > 0` case. `evalLedger` is
    still an explicit parameter — `TCmp.of` does not decide how it was built —
    but `TCmp.ofAssembled` below supplies it for real, from `assembleLedger`,
    rather than leaving it a hypothesis. -/
def TCmp.of {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h) (X0 : TickCarrier RawAux h)
    (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) : TCmp RawAux EvalAux h where
  horizon := h
  Sh := (Term pol X0 hX0).active
  evTerm := EvTerm pol X0 hX0 hh
  cand := ensemble (Term pol X0 hX0) evalLedger

/-- The record's own horizon field agrees with the index it was built at,
    `rfl` — a check that the constructor did not transpose `h` with something
    else. -/
@[simp] theorem TCmp.of_horizon {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    (TCmp.of pol X0 hX0 hh evalLedger).horizon = h := rfl

/-- The record's support really is the terminal carrier's own active support,
    `rfl`: the record does not silently read some other tick's `S_j`. -/
@[simp] theorem TCmp.of_Sh {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    (TCmp.of pol X0 hX0 hh evalLedger).Sh = (Term pol X0 hX0).active := rfl

/-! ## Assembling Definition 6.3's evaluated ledger from §7–§10

    The 23:30 pass's own finding, closed here (01:30 pass) for nine of
    `EvalRecord`'s fourteen `Slot Aux` fields, then a tenth (05:30 pass,
    `dWalk`): `TickCarrier.ledger`/`AdvanceData.Δ` stay at the raw stratum
    (nothing about that was wrong), and what was missing was a function
    reading a `Core`'s own stored fields plus the carrier's declared observer
    against §7–§10's now-built comparison, coherence, admission and
    causal-pair machinery. Four slots stay `.notEvaluated`, and each is left
    for a named reason rather than papered over — see `EvalRecord.assemble`. -/

/-- **Definition 9.4/9.8's channel reading, with `Fin k` erased to a raw
    phase index.** `EvalValue` is deliberately closed and non-parametric, the
    same reason every other slot in this file stores `ℕ`/`ℤ` rather than a
    dependent type (`natSig` holds `ℕ`, not `Fin k`). Three cases, not four:
    there is no separate "not declared" case here, because that is
    `EvalRecord.channel`'s own `.notEvaluated` one level up, in
    `EvalRecord.assembleWith`. -/
inductive ChanReading where
  | noAdmission
  | resolved (phase : ℕ) (word : Word)
  | unresolvedMultiple
deriving DecidableEq

/-- One sum type standing in for `EvalRecord`'s shared `Aux` parameter, now
    that §7–§10 exist and nine slots have a genuine value to carry. One
    constructor per **kind** of value, not one per field: `tension` and `lCF`
    both produce `List (IPres × ℕ)` and share `natSig`, since which `EvalRecord`
    field holds a value is what names its meaning, not which constructor built
    it — the same reading `Slot`'s own docstring already gives `Aux`.

    **Three more constructors, added when `admission`/`channel`/`liftStatus`
    close.** `admCert` carries Definition 11.3's certificate fields directly
    (`negLoad`, the retained vector as `List Bool`, the Boolean reading, the
    admission bit, the exact blocking set) rather than the existing `AdmCert
    Aux` wrapper from `Advance.lean`: `AdmCert`'s own `gamma : List Aux` would
    need `Aux := EvalValue`, a self-reference bought for no content this file
    needs, when `AdmCert` already exists under its own name for §11 call
    sites that want the wrapped structure. `admission` itself needs no new
    constructor — its value is a `Bool`, exactly `inSupp`'s kind. -/
inductive EvalValue where
  | word (w : Word)
  | pres (p : Pres)
  | pairSig (l : List (IPres × IPres))
  | natSig (l : List (IPres × ℕ))
  | coh (z : Zphi)
  | inSupp (b : Bool)
  | wind (n : ℤ)
  | causal (c : Option CausalRecord)
  | admCert (negLoad : ℤ) (gamma : List Bool) (pred adm : Bool) (fail : List Advance.FailReason)
  | chanReading (r : ChanReading)
  | liftResult (s : LiftStatus)

/-- The occurrence's own observer-local interior address, `some` exactly when
    the observer admits it (`Q_{O,x} ∈ ℳ₊`) and the address lands off the
    `0:1`/`1:0` boundary. Every occurrence a real walk actually reaches is
    interior (`Frame.walk_mid_pos`), so the second condition is not expected
    to bite in practice; it is still checked rather than assumed, the same
    discipline `IPres.ofPres?` itself is built for. -/
def localOf {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) (c : Core) : Option IPres :=
  (lambda X.observer.matrix c.fullMatrix).bind IPres.ofPres?

/-- **The `fam : List IPres` §7's and §8's comparison functions are stated
    against**, read off one tick: every currently active occurrence's own
    local address, silently absent when the observer does not admit it or it
    lands on the boundary — the same "witnessed by absence" move `EvalRecord`
    itself already makes for a slot with no value, not an invented default.
    Includes the occurrence being scored against itself; `tEnd_self`/
    `self_term` already make that entry inert (`tEnd y y = 0`,
    `φ⁻⁰ = 1`), so nothing downstream needs it excluded by hand. -/
def activeFamily {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) : List IPres :=
  (X.archive.filter fun c => decide (c.id ∈ X.active)).filterMap (localOf X)

/-- **Definition 7.4's `D_walk` family.** `dwalk` is stated on the observer-
    local *words* `a_z`, not on the decoded `IPres` addresses every other
    signature in this file is keyed by — the gap the 01:30 pass named.
    `localOf` and `localWord` factor through the same `lambda := localWord.map
    r`, so wherever `localOf X c` is `some`, `localWord` for that same `c` is
    `some` too (`activeFamilyWords_map_fst` below); no separate admission test
    is needed, only carrying the word alongside the address instead of
    discarding it. -/
def activeFamilyWords {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) : List (IPres × Word) :=
  (X.archive.filter fun c => decide (c.id ∈ X.active)).filterMap fun c =>
    match localOf X c, localWord X.observer.matrix c.fullMatrix with
    | some y, some w => some (y, w)
    | _, _ => none

/-- The two families carry identical keys: `localOf` never returns `some`
    where `localWord` returns `none`, since `localOf` is `localWord.map r`
    then `IPres.ofPres?`. So pairing the word in costs no entries against
    `activeFamily`. -/
theorem activeFamilyWords_map_fst {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) :
    (activeFamilyWords X).map Prod.fst = activeFamily X := by
  unfold activeFamilyWords activeFamily
  rw [List.map_filterMap]
  apply List.filterMap_congr
  intro c _
  cases hw : localWord X.observer.matrix c.fullMatrix with
  | none =>
    have : localOf X c = none := by
      simp [localOf, lambda, hw]
    simp [this]
  | some w =>
    cases localOf X c with
    | none => simp
    | some y => simp

/-- **Definition 7.4, the keyed `D_walk` signature.** `D_{walk,j}^{(O)}(y) =
    (z ↦ d_walk(a_y,a_z))`, keys retained, exactly the same shape as
    `tensionSignature` and `cfSignature` one section up. -/
def dWalkSignature (famW : List (IPres × Word)) (yWord : Word) : List (IPres × ℕ) :=
  famW.map (fun zw => (zw.1, dwalk yWord zw.2))

/-- **Definition 10.4's sibling-pair record, read off a `Core`'s own stored
    fields alone.** `childCore_traversal` already proves `x.relWord.dropLast`
    is the parent's own relative word for any child `x` this tree builds, so
    the split point `causalRecord` needs is exactly what `x` already carries;
    no archive lookup, no extra declared apparatus. A seed core (`hand =
    none`) has no split to record, `none`, the same absence-not-invention
    reading Definition 6.6 already uses. -/
def causalPairOf (c : Core) : Option CausalRecord :=
  c.hand.map fun g => causalRecord c.seedId c.seed c.relWord.dropLast g

/-! ## The three remaining slots' declared apparatus

    `admission`/`admCert`, `channel`, `liftStatus` all name apparatus the book
    itself calls *declared*, not apparatus this tree invents on their behalf:
    2427–2429 of the v0.22 text, *"A finite-channel record is evaluated only
    when that channel belongs to the receiver data. A lift record is
    evaluated only when a sign-sensitive lift predicate has been declared.
    Otherwise the corresponding slot is `not-evaluated`."* Each structure
    below is exactly one piece of declared apparatus, taken as an explicit
    parameter to `EvalRecord.assembleWith`; supplying `none` for any of them
    reproduces `EvalRecord.assemble`'s own `.notEvaluated` reading exactly,
    not a weaker approximation of it (`assembleWith_none_eq_assemble`,
    below `assembleWith` itself). -/

/-- Definition 4.9/11.3's admission apparatus: `boundary` is the cavity
    boundary predicate `γ_∂`, `pred` is Definition 4.3's declared Boolean
    reading `Pred_Γ`, and `gammaVec` is the retained certificate vector
    `g_Γ` — all three per-occurrence, via the occurrence's own encounter
    matrix `Q_{O,y}`. -/
structure AdmissionDecl where
  boundary : Mat2 → Bool
  pred : Mat2 → Bool
  gammaVec : Mat2 → List Bool

/-- Definition 9.4's declared finite channel: the channel matrix and its
    declared phase count. -/
structure ChannelDecl where
  chan : Mat2
  k : ℕ

/-- Definition 9.15's declared sign-sensitive lift predicate `χ`, per
    occurrence via its own encounter matrix — `liftStatus`'s existing
    `Option (Bool → Bool)` argument is exactly `χ` at one fixed occurrence,
    so this is `χ` before that fixing. -/
structure LiftDecl where
  chi : Mat2 → Bool → Bool

/-- **Definition 9.4/9.8's channel reading, built from the already-proved
    `decodedChannel`/`chanStatus` rather than reimplemented.** `resolved`
    exactly when `decodedChannel` decodes one admitted phase;
    `unresolvedMultiple` only from `chanStatus`'s own third case;
    `noAdmission` otherwise — which also covers the case `decodedChannel`
    silently drops, an admitted phase whose rotated matrix fails to decode
    (`dec` returning `none`), correctly folded into "no usable admission"
    rather than invented as a fourth case. -/
def channelReading (C : Mat2) (k : ℕ) (Q : Mat2) : ChanReading :=
  match decodedChannel C k Q with
  | some (j, w) => .resolved j.val w
  | none =>
      match chanStatus C k Q with
      | .unresolvedMultiple => .unresolvedMultiple
      | _ => .noAdmission

/-- **Whenever the channel genuinely resolves, `channelReading` reconstructs
    the same rotated matrix `decoded_reconstructs` already proves for
    `decodedChannel` — this is not a second, independent computation that
    happens to agree, it is read straight off the proved one.** -/
theorem channelReading_resolved_reconstructs {C Q : Mat2} {k : ℕ} {j : Fin k}
    {w : Word} (h : decodedChannel C k Q = some (j, w)) :
    channelReading C k Q = .resolved j.val w ∧ matPow C j.val * Q = G w :=
  ⟨by unfold channelReading; rw [h], decoded_reconstructs h⟩

/-- **Definition 6.3, assembled at one occurrence.** Ten of fourteen `Slot`
    fields filled from `X`'s own observer and `c`'s own stored fields, no
    further declared apparatus:

    * `localWord`/`localAddr` — Definition 3.1's decoder, direct.
    * `sigma`/`tension`/`lCF` — Definition 7.4's three signatures against
      `activeFamily X`, once `c`'s own local address exists.
    * `dWalk` — Definition 7.4's fourth signature, `D_walk`, against
      `activeFamilyWords X` and `c`'s own local **word**; the 01:30 pass's
      gap (`activeFamily` kept only the decoded address) closes by pairing
      the word alongside it rather than by any new decoding.
    * `starC`/`supportStatus` — Definition 8.1's exact coherence and
      Construction Axiom II.1's support test, same family.
    * `omega` — Definition 9.x's winding, `X.observer.word` against `c`'s own
      `fullWord`; always defined, no family needed.
    * `causalPair` — `causalPairOf`; always defined, `none` at a seed.

    **Four stay `.notEvaluated`, and each for a different named reason, not
    one blanket gap:**

    * `admission`/`admCert` — Definition 7.1's own text calls the admission
      predicate `Pred_Γ` *declared*, and nothing in `Observer` or
      `TickCarrier` carries one; `admCert`'s certificate type was never built
      anywhere in this tree, the same honest gap `RecordingSocket.Cert` names
      at §4.
    * `channel`/`liftStatus` — both need a declared channel matrix and phase
      count (§9), and `liftStatus` additionally a declared central lift
      selection — which Elements II's own §31.3 open list names as
      unresolved *at the book level*, "general central-lift selection when no
      lift field or predicate is supplied." Not this tree's gap to close
      unattended.

    **All three are filled by `EvalRecord.assembleWith` below, when the
    caller supplies the declared apparatus each one names.** §31.3's open
    list is about central lift *selection* specifically — choosing a
    representative when none is supplied — not about `liftStatus` itself,
    which Definition 9.15 states relative to a `χ` the caller declares; that
    was always a per-instantiation question, not a gap in this tree. -/
def EvalRecord.assemble {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) (c : Core) :
    EvalRecord EvalValue :=
  let MO := X.observer.matrix
  let fam := activeFamily X
  let famW := activeFamilyWords X
  { EvalRecord.initial (Q MO c.fullMatrix) c.closure with
    localWord :=
      match localWord MO c.fullMatrix with
      | some w => .value (.word w)
      | none => .notEvaluated
    localAddr :=
      match lambda MO c.fullMatrix with
      | some p => .value (.pres p)
      | none => .notEvaluated
    sigma :=
      match localOf X c with
      | some y => .value (.pairSig (star fam y))
      | none => .notEvaluated
    tension :=
      match localOf X c with
      | some y => .value (.natSig (tensionSignature fam y))
      | none => .notEvaluated
    lCF :=
      match localOf X c with
      | some y => .value (.natSig (cfSignature fam y))
      | none => .notEvaluated
    dWalk :=
      match localWord MO c.fullMatrix with
      | some w => .value (.natSig (dWalkSignature famW w))
      | none => .notEvaluated
    starC :=
      match localOf X c with
      | some y => .value (.coh (coherenceOf fam y))
      | none => .notEvaluated
    supportStatus :=
      match localOf X c with
      | some y => .value (.inSupp (decide (y ∈ support fam)))
      | none => .notEvaluated
    omega := .value (.wind (winding X.observer.word c.fullWord))
    causalPair := .value (.causal (causalPairOf c)) }

/-- **Definition 6.3's ledger, assembled for every currently active occurrence
    at once** — exactly the shape `ensemble`/`TCmp.of` want as `evalLedger`. -/
def assembleLedger {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) :
    List (QuestionId × EvalRecord EvalValue) :=
  (X.archive.filter fun c => decide (c.id ∈ X.active)).map fun c => (c.id, EvalRecord.assemble X c)

/-- **Definition 6.3, all fourteen `Slot` fields, `EvalRecord.assemble`
    generalized over the three pieces of declared apparatus it left
    `.notEvaluated`.** Each of `adm`/`chanD`/`liftD` is `Option`al on exactly
    the axis the book itself declares optional; `none` for all three
    reproduces `EvalRecord.assemble` exactly (`assembleWith_none_eq_assemble`).
    `admission` reuses `inSupp`'s `Bool` kind rather than a new constructor,
    since which field holds a value is what names its meaning, not which
    constructor built it — `EvalValue`'s own docstring's rule, applied once
    more. -/
def EvalRecord.assembleWith {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) (c : Core)
    (adm : Option AdmissionDecl) (chanD : Option ChannelDecl) (liftD : Option LiftDecl) :
    EvalRecord EvalValue :=
  let base := EvalRecord.assemble X c
  let Qenc := base.encounter
  { base with
    admission :=
      match adm with
      | some d => .value (.inSupp (admits (negLoad Qenc) (d.pred Qenc)))
      | none => .notEvaluated
    admCert :=
      match adm with
      | some d => .value (.admCert (negLoad Qenc) (d.gammaVec Qenc) (d.pred Qenc)
          (admits (negLoad Qenc) (d.pred Qenc))
          (failReasons (d.boundary Qenc) (negLoad Qenc) (d.pred Qenc)))
      | none => .notEvaluated
    channel :=
      match chanD with
      | some d => .value (.chanReading (channelReading d.chan d.k Qenc))
      | none => .notEvaluated
    liftStatus :=
      match liftD with
      | some d => .value (.liftResult (liftStatus (some (d.chi Qenc))))
      | none => .notEvaluated }

/-- **Supplying no declared apparatus reproduces `EvalRecord.assemble`
    exactly, not merely something equally uninformative.** The four fields
    `assembleWith` touches are already `.notEvaluated` in `base`, so the
    structure update with `none` for all three changes nothing — `rfl`, the
    cheapest possible confirmation that generalizing the function did not
    silently change its own default behaviour. -/
theorem assembleWith_none_eq_assemble {Aux : Type} {h : ℕ} (X : TickCarrier Aux h) (c : Core) :
    EvalRecord.assembleWith X c none none none = EvalRecord.assemble X c := rfl

/-- **Definition 6.3's ledger, all fourteen slots, for every currently active
    occurrence at once** — the `assembleWith` counterpart to `assembleLedger`. -/
def assembleLedgerWith {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (adm : Option AdmissionDecl) (chanD : Option ChannelDecl) (liftD : Option LiftDecl) :
    List (QuestionId × EvalRecord EvalValue) :=
  (X.archive.filter fun c => decide (c.id ∈ X.active)).map fun c =>
    (c.id, EvalRecord.assembleWith X c adm chanD liftD)

/-- **Definition 16.1's record, with the evaluated ledger no longer a
    hypothesis.** `TCmp.of`'s `evalLedger` parameter is now `assembleLedger`
    applied to the terminal carrier itself — real data computed from the
    schedule that reached it, not supplied from outside. -/
def TCmp.ofAssembled {Aux : Type} {h : ℕ} (pol : Policy Aux h) (X0 : TickCarrier Aux h)
    (hX0 : Seeded X0) (hh : 0 < h) : TCmp Aux EvalValue h :=
  TCmp.of pol X0 hX0 hh (assembleLedger (Term pol X0 hX0))

/-! ## §16 Definition 16.4 — Canonical three-seed regression questions

Three base questions differing only in the one seed occurrence's own
relative word — `ε`, `L`, `R` — with the observer fixed at the canonical
frame's empty word throughout (condition 1). The reached seed states are
exactly the genesis states of the positive grammar the book names: the
canonical mediant `1{:}1` (the empty word) and the two states `1{:}2`,
`2{:}1` reached from it by one side selection, Elements I Definition 2.5.
`seed_addressed_eps`/`_L`/`_R` below check the modelling against that claim
rather than assume it.

**Condition 4, the base occurrence-counted comparison profile of
Construction Axiom II.1, is not a field here.** It names which comparison
rule governs the ticks these questions seed, not a datum the `Question`
record itself carries — that rule is `Coherence.lean`'s `support`, already
built, and it is supplied when (not if) one of these three seeds a running
`Policy`, not at this static definition.

**One field the book's own six conditions do not pin down: `depth` (`N`,
the cavity bound).** Nothing in this tree reads `TickCarrier.question.depth`
— `advanceCarrier` (`Advance.lean`) carries `question` through unchanged
(`question := X.question`) and never inspects it, the same species of
unwired passthrough §16.1's own account found at `Cand`/`ensemble`. Set to
`sevenTickHorizon` here, matching `horizon`, as a placeholder with no
computational effect anywhere in this tree yet — not a book divergence,
since the book names no value for it either. -/

/-- The one seed's own identifier, fixed and arbitrary: Definition 16.4
    declares exactly one seed per question and names no other. -/
def seed164Id : QuestionId := ⟨0, 0, 0, []⟩

/-- **Condition 1.** The canonical observer, at the empty word over the
    canonical frame. -/
def observer164 : Observer := ⟨Frame.empty, [], 1⟩

/-- **Definition 16.4**, one question per seed word `w ∈ {ε, L, R}`.
    Condition 2 is the seed's own relative word; condition 3 is `preds :=
    []`, since the only two admission checks the book names — direct-
    positive and the fixed cavity condition — live in §11's tick-advance
    machinery (`Advance.lean`'s `admits`/`failReasons`) rather than in
    `Question.preds`; condition 5 is `horizon`; condition 6 is a fixed
    socket, transported unchanged by `advanceCarrier` and read by nothing
    downstream yet (`splice := id`, `retain := fun _ => true`). -/
def canonicalQuestion (w : Word) : ExtendedQuestion Unit where
  receiver := observer164
  frame := Frame.empty
  depth := sevenTickHorizon
  active := [⟨Frame.empty, w⟩]
  preds := []
  horizon := sevenTickHorizon
  socket := { target := seed164Id, splice := id, retain := fun _ => true }

/-- `𝒬_ε`. -/
def Qeps : ExtendedQuestion Unit := canonicalQuestion []

/-- `𝒬_L`. -/
def QL : ExtendedQuestion Unit := canonicalQuestion [false]

/-- `𝒬_R`. -/
def QR : ExtendedQuestion Unit := canonicalQuestion [true]

/-- The three questions are pairwise distinct — three different seed words,
    checked on the one field that varies rather than on the whole structure
    (`ExtendedQuestion` carries function fields in `socket`, so it has no
    `DecidableEq` instance to `decide` against directly). -/
theorem Qeps_ne_QL : Qeps.active ≠ QL.active := by decide

theorem Qeps_ne_QR : Qeps.active ≠ QR.active := by decide

theorem QL_ne_QR : QL.active ≠ QR.active := by decide

/-- **The genesis-state claim in Definition 16.4's closing paragraph,
    checked rather than assumed.** `𝒬_ε`'s one seed addresses the canonical
    mediant `1{:}1`; `𝒬_L` and `𝒬_R`'s address the two states reached from
    it by one side selection, `1{:}2` and `2{:}1` — `Frame.stepL`/`stepR`
    (Elements I Definition 2.4/2.5) at `Frame.empty`, computed, not cited. -/
theorem seed_addressed_eps :
    History.addressed ⟨Frame.empty, []⟩ = (⟨1, 1, by decide⟩ : Pres) := rfl

theorem seed_addressed_L :
    History.addressed ⟨Frame.empty, [false]⟩ = (⟨1, 2, by decide⟩ : Pres) := rfl

theorem seed_addressed_R :
    History.addressed ⟨Frame.empty, [true]⟩ = (⟨2, 1, by decide⟩ : Pres) := rfl

end Accumulation
end Two
end RatioSpace
