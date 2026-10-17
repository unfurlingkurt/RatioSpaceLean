/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S17.Terminal
/-!
  Elements II Definition 4.7, support-free initialization context.

  `Cavity.lean`'s `InitContext` carries `seedArchive : List (QuestionId ×
  History)`, which holds the seed identifier and retained history but not the
  immutable seed core Definition 4.7 names (closure record, imbalance, entry
  event, provenance, null parent and hand); it carries `ℰ_init` as
  `initLedger`. Nor does it tie `𝐀` to the archive:
  `mem_S0tilde_iff_mem_S0` has to assume `ctx.active = seeds.map Prod.snd`.

  This file builds the faithful context, `SeedInitContext`, on §6's `Core`, and
  ties it to the existing one both ways:

    * `toInitContext` forgets it to `InitContext`, and `ofInitContext` lifts
      every `InitContext` that satisfies the book's conditions back, with
      `toInitContext_ofInitContext` the round trip (for a context with no
      initial annotations), and `toInitContextWith_ofInitContext` the round trip
      that keeps `ℰ_init`, which `InitContext` carries;
    * Definition 4.8's seed-by-seed iff holds with the `hactive` hypothesis
      discharged by the context's own field;
    * adding a support and the tick-zero admission stratum gives a tick-zero
      `TickCarrier` whose `CarrierInv` is proved, so Theorem 17.7's
      iff-direction holds for every schedule started from Definition 4.7.
-/

namespace RatioSpace
namespace Gaps

open Mat2 Word Frame Pres RatioSpace RatioSpace.Two RatioSpace.Two.Accumulation

/-- **Definition 4.7.** `𝔦_τ = (O_τ, 𝒬_τ, 𝐀, ℋ_seed, ℰ_init)`, with no support
    slot. The seed archive holds §6's immutable cores, each a seed core (null
    parent and incoming hand, empty relative word, closure, imbalance, entry
    event and provenance carried); there is one core for every member of `𝐀`,
    in order; the stable seed identifiers are distinct (Definition 4.1).
    `ℰ_init` is a list keyed by occurrence identifier over a declared annotation
    type `Ann`, the same shape as `TickCarrier.ledger`. -/
structure SeedInitContext (Cert Ann : Type) where
  /-- `O_τ`. -/
  observer : Observer
  /-- `𝒬_τ`. -/
  question : ExtendedQuestion Cert
  /-- `𝐀`, the active relational family. -/
  active : ActiveFamily
  /-- `ℋ_seed`, one immutable seed core per member of `𝐀`. -/
  seedArchive : List Core
  /-- `ℰ_init`, the exact annotations available before support selection. -/
  initLedger : List (QuestionId × Ann)
  /-- Every archived core is a seed core: parent and hand null, relative word
      empty, every derived field recomputed from its seed. -/
  seed_core : ∀ c ∈ seedArchive, c = seedCore c.seedId c.seed c.entry c.prov
  /-- One core for every seed in `𝐀`. -/
  one_core_per_seed : active = seedArchive.map Core.seed
  /-- Stable seed identifiers distinguish the seed occurrences. -/
  seed_ids_nodup : (seedArchive.map Core.id).Nodup

namespace SeedInitContext

variable {Cert Ann : Type} (X : SeedInitContext Cert Ann)

/-- The tagged seeds, in the shape `S0tilde` reads. -/
def seeds : List (QuestionId × History) :=
  X.seedArchive.map fun c => (c.seedId, c.seed)

/-- Forget the cores and the ledger: the existing `InitContext`. Its `ℰ_init`
    is typed over `Cert`, not `Ann`, so it gets the default, the empty list;
    `toInitContextWith` keeps the ledger when `Ann = Cert`. -/
def toInitContext : InitContext Cert where
  observer := X.observer
  question := X.question
  active := X.active
  seedArchive := X.seeds

/-- Forget the cores and keep `ℰ_init`, for a context whose annotation type is
    `Cert`, the type `InitContext`'s ledger uses. -/
def toInitContextWith (X : SeedInitContext Cert Cert) : InitContext Cert where
  observer := X.observer
  question := X.question
  active := X.active
  seedArchive := X.seeds
  initLedger := X.initLedger

theorem seedArchive_length : X.seedArchive.length = X.active.length := by
  rw [X.one_core_per_seed, List.length_map]

variable {X}

theorem seed_parent {c : Core} (hc : c ∈ X.seedArchive) : c.parent = none := by
  rw [X.seed_core c hc]; rfl

theorem seed_hand {c : Core} (hc : c ∈ X.seedArchive) : c.hand = none := by
  rw [X.seed_core c hc]; rfl

theorem seed_relWord {c : Core} (hc : c ∈ X.seedArchive) : c.relWord = [] := by
  rw [X.seed_core c hc]; rfl

theorem seed_id {c : Core} (hc : c ∈ X.seedArchive) :
    c.id = (proposal c.seedId c.seed []).id := by
  rw [X.seed_core c hc]; rfl

theorem seed_closure {c : Core} (hc : c ∈ X.seedArchive) : c.closure = psi12 c.fullWord := by
  rw [X.seed_core c hc]; rfl

theorem seed_imbalance {c : Core} (hc : c ∈ X.seedArchive) : c.imbalance = bal c.fullWord := by
  rw [X.seed_core c hc]; rfl

theorem seed_wellFormed {c : Core} (hc : c ∈ X.seedArchive) : c.WellFormed := by
  rw [X.seed_core c hc]; exact seedCore_wellFormed _ _ _ _

variable (X)

/-- The hypothesis `mem_S0tilde_iff_mem_S0` asks for, as a theorem. -/
theorem toInitContext_active : X.toInitContext.active = X.seeds.map Prod.snd := by
  change X.active = _
  rw [X.one_core_per_seed]
  simp [seeds, List.map_map, Function.comp_def]

/-- **Definition 4.8's seed-by-seed iff, hypothesis discharged.** For every seed
    core of the context, its relative-empty-word record lies in `S̃₀` under
    lifted predicates exactly when its retained history lies in Elements I's
    `S₀`. -/
theorem mem_S0tilde_iff_mem_S0' (F : Frame) (N : ℕ) (relPreds : List Pred) {c : Core}
    (hc : c ∈ X.seedArchive) :
    proposal c.seedId c.seed [] ∈ S0tilde F N (relPreds.map liftPred) X.toInitContext X.seeds ↔
      c.seed ∈ RatioSpace.S0
        { receiver := X.observer, frame := F, depth := N, active := X.active,
          preds := relPreds } :=
  RatioSpace.Two.mem_S0tilde_iff_mem_S0 F N relPreds X.toInitContext X.seeds
    X.toInitContext_active (p := (c.seedId, c.seed)) (List.mem_map_of_mem hc)

/-- The seeds' relative-empty-word records carry exactly the archive's
    identifiers. -/
theorem seed_record_ids :
    (X.seeds.map fun p => proposal p.1 p.2 []).map ProposalRecord.id =
      X.seedArchive.map Core.id := by
  simp only [seeds, List.map_map]
  exact List.map_congr_left fun c hc => (seed_id hc).symm

/-- `S̃₀`'s identifiers are a sublist of the seed archive's. -/
theorem S0tilde_ids_sublist (F : Frame) (N : ℕ) (preds : List (OccPred (InitContext Cert))) :
    List.Sublist ((S0tilde F N preds X.toInitContext X.seeds).map ProposalRecord.id)
      (X.seedArchive.map Core.id) := by
  rw [← X.seed_record_ids]
  exact List.Sublist.map ProposalRecord.id List.filter_sublist

/-- **The tick-zero carrier Definition 4.7 initializes.** The context has no
    support slot; the support `S̃₀` is computed by Definition 4.8 and the
    tick-zero admission stratum is supplied, appended after `ℰ_init`. -/
def toTick0 {Aux : Type} (X : SeedInitContext Aux Aux) (h : ℕ) (F : Frame) (N : ℕ)
    (preds : List (OccPred (InitContext Aux))) (adm : List (QuestionId × Aux)) :
    TickCarrier Aux h where
  observer := X.observer
  question := X.question
  tick := 0
  active := (S0tilde F N preds X.toInitContext X.seeds).map ProposalRecord.id
  archive := X.seedArchive
  ledger := X.initLedger ++ adm
  active_sub_archive := fun _ hi => (X.S0tilde_ids_sublist F N preds).subset hi

theorem toTick0_tick {Aux : Type} (X : SeedInitContext Aux Aux) (h : ℕ) (F : Frame) (N : ℕ)
    (preds : List (OccPred (InitContext Aux))) (adm : List (QuestionId × Aux)) :
    ((X.toTick0 h F N preds adm).tick : ℕ) = 0 := rfl

/-- **The tick-zero carrier satisfies `CarrierInv`**, from the context's own
    fields: distinct seed identifiers, well-formed seed cores, and a
    duplicate-free `S̃₀`. -/
theorem toTick0_carrierInv {Aux : Type} (X : SeedInitContext Aux Aux) (h : ℕ) (F : Frame)
    (N : ℕ) (preds : List (OccPred (InitContext Aux))) (adm : List (QuestionId × Aux)) :
    CarrierInv (X.toTick0 h F N preds adm) := by
  unfold CarrierInv
  exact ⟨X.seed_ids_nodup, fun _ hc => seed_wellFormed hc,
    (X.S0tilde_ids_sublist F N preds).nodup X.seed_ids_nodup⟩

/-- **The tick-zero carrier Definition 4.7 initializes is a valid start for a
    schedule** (`Seeded`): tick zero, `CarrierInv`, and Lemma 12.1's invariant,
    which at tick zero holds because every archived core is a seed. -/
theorem toTick0_seeded {Aux : Type} (X : SeedInitContext Aux Aux) (h : ℕ) (F : Frame)
    (N : ℕ) (preds : List (OccPred (InitContext Aux))) (adm : List (QuestionId × Aux)) :
    Seeded (X.toTick0 h F N preds adm) :=
  ⟨rfl, toTick0_carrierInv X h F N preds adm,
    Gaps.G2_13.tickLengthInv_of_seeds _ rfl (fun _ hc => seed_wellFormed hc)
      (fun _ hc => X.seed_relWord hc)⟩

/-- **Theorem 17.7's iff-direction for every schedule started from Definition
    4.7.** The tick-zero hypothesis of
    `crystallize_isSome_iff_singleton_of_carrierInv` is discharged. -/
theorem crystallize_isSome_iff_singleton_of_init {Aux EvalAux : Type} (X : SeedInitContext Aux Aux)
    (h : ℕ) (F : Frame) (N : ℕ) (preds : List (OccPred (InitContext Aux)))
    (adm : List (QuestionId × Aux)) (pol : Policy Aux h) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    (Terminal.crystallize pol (X.toTick0 h F N preds adm) (toTick0_seeded X h F N preds adm) hh
        evalLedger).isSome = true ↔
      (Terminal.Report.of pol (X.toTick0 h F N preds adm) (toTick0_seeded X h F N preds adm) hh
        evalLedger).status = .singleton :=
  Terminal.crystallize_isSome_iff_singleton_of_carrierInv pol _ _ hh evalLedger
    (X.toTick0_carrierInv h F N preds adm)

end SeedInitContext

/-- **Every `InitContext` meeting Definition 4.7's conditions lifts.** Given
    that `𝐀` is the archive's histories and that the seeds' identifiers are
    distinct, archive each seed as a seed core entering at `entry` with
    provenance `prov`, and supply `ℰ_init`. -/
def ofInitContext {Cert Ann : Type} (ctx : InitContext Cert)
    (hact : ctx.active = ctx.seedArchive.map Prod.snd)
    (hnodup : (ctx.seedArchive.map fun p => (proposal p.1 p.2 []).id).Nodup)
    (entry : ℕ) (prov : QuestionId × History → Provenance)
    (initLedger : List (QuestionId × Ann)) : SeedInitContext Cert Ann where
  observer := ctx.observer
  question := ctx.question
  active := ctx.active
  seedArchive := ctx.seedArchive.map fun p => seedCore p.1 p.2 entry (prov p)
  initLedger := initLedger
  seed_core := by
    intro c hc
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hc
    rfl
  one_core_per_seed := by
    rw [hact, List.map_map]; rfl
  seed_ids_nodup := by
    rw [List.map_map]; exact hnodup

/-- The round trip: lifting and forgetting returns the original context, for a
    context with no initial annotations (`toInitContext` forgets `ℰ_init`). -/
theorem toInitContext_ofInitContext {Cert Ann : Type} (ctx : InitContext Cert)
    (hact : ctx.active = ctx.seedArchive.map Prod.snd)
    (hnodup : (ctx.seedArchive.map fun p => (proposal p.1 p.2 []).id).Nodup)
    (entry : ℕ) (prov : QuestionId × History → Provenance)
    (initLedger : List (QuestionId × Ann)) (hled : ctx.initLedger = []) :
    (ofInitContext (Ann := Ann) ctx hact hnodup entry prov initLedger).toInitContext = ctx := by
  obtain ⟨o, q, a, sa, l⟩ := ctx
  subst hled
  simp only [SeedInitContext.toInitContext, SeedInitContext.seeds, ofInitContext, List.map_map]
  congr 1
  exact (List.map_congr_left (g := id) fun _ _ => rfl).trans (List.map_id _)

/-- **The round trip with `ℰ_init`.** Lifting a context with its own initial
    annotations and forgetting only the cores returns the original context,
    annotations included. -/
theorem toInitContextWith_ofInitContext {Cert : Type} (ctx : InitContext Cert)
    (hact : ctx.active = ctx.seedArchive.map Prod.snd)
    (hnodup : (ctx.seedArchive.map fun p => (proposal p.1 p.2 []).id).Nodup)
    (entry : ℕ) (prov : QuestionId × History → Provenance) :
    (ofInitContext (Ann := Cert) ctx hact hnodup entry prov ctx.initLedger).toInitContextWith
      = ctx := by
  obtain ⟨o, q, a, sa, l⟩ := ctx
  simp only [SeedInitContext.toInitContextWith, SeedInitContext.seeds, ofInitContext, List.map_map]
  congr 1
  exact (List.map_congr_left (g := id) fun _ _ => rfl).trans (List.map_id _)

#print axioms SeedInitContext
#print axioms SeedInitContext.seeds
#print axioms SeedInitContext.toInitContext
#print axioms SeedInitContext.seedArchive_length
#print axioms SeedInitContext.seed_parent
#print axioms SeedInitContext.seed_hand
#print axioms SeedInitContext.seed_relWord
#print axioms SeedInitContext.toTick0_seeded
#print axioms SeedInitContext.seed_id
#print axioms SeedInitContext.seed_closure
#print axioms SeedInitContext.seed_imbalance
#print axioms SeedInitContext.seed_wellFormed
#print axioms SeedInitContext.toInitContext_active
#print axioms SeedInitContext.mem_S0tilde_iff_mem_S0'
#print axioms SeedInitContext.seed_record_ids
#print axioms SeedInitContext.S0tilde_ids_sublist
#print axioms SeedInitContext.toTick0
#print axioms SeedInitContext.toTick0_tick
#print axioms SeedInitContext.toTick0_carrierInv
#print axioms SeedInitContext.crystallize_isSome_iff_singleton_of_init
#print axioms ofInitContext
#print axioms toInitContext_ofInitContext
#print axioms SeedInitContext.toInitContextWith
#print axioms toInitContextWith_ofInitContext

end Gaps
end RatioSpace
