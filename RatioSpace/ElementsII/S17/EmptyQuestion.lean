/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S15.AxiomPolicy
import RatioSpace.ElementsII.S04.SupportFreeInitializationContext
import RatioSpace.ElementsII.S04.AQuestionBoundsItsSupport
/-!
  Gap G2-04 (empty question) — Elements II Corollary 17.8, an exact predicate
  can block every proposal and carry empty support through a whole run.

  `Gaps/G2_04.lean`'s `S0tilde_gammaB_nil` already proves that adjoining the
  empty membership predicate `gammaB []` to any declared predicate family
  empties the initial support `S̃₀`. This file carries that fact forward: an
  empty active support stays empty under every lawful advance, hence under
  every schedule, so the tick-zero carrier built from `gammaB []` reaches a
  terminal report whose status is `empty`. The concrete witness is the
  seven-tick question of the root seed under the predicate that admits nothing.
-/
namespace RatioSpace.Two.EmptyQuestion

open RatioSpace RatioSpace.Two RatioSpace.Two.Advance RatioSpace.Two.Accumulation
open RatioSpace.Two.Terminal RatioSpace.Gaps RatioSpace.Two.RootOrbit RatioSpace.Two.AxiomPolicy

/-! ## Statement 1 — no proposal from an empty active support -/

/-- **Definition 11.6 at empty support.** With no active occurrence, the
    one-tick proposal family is empty: every proposal is tagged to a member of
    the active list, and there are none. Induction on the archive, no
    `List.filter_eq_nil_iff` (which carries `Classical.choice`). -/
theorem proposals_nil (archive : List Core) : proposals archive [] = [] := by
  unfold proposals
  induction archive with
  | nil => rfl
  | cons a l ih =>
      by_cases ha : a.id ∈ ([] : List QuestionId)
      · exact absurd ha List.not_mem_nil
      · rw [List.filter_cons_of_neg (by simp [ha])]
        exact ih

/-! ## Statement 2 — a lawful advance keeps empty support empty -/

/-- **An empty active support stays empty under one lawful advance.** The new
    active list is `select (proposals X.archive X.active)`; with `X.active = []`
    the proposals are empty (`proposals_nil`), so `hsel` forces every member of
    the selection to come from the empty proposal family, which is impossible.
    Hence the selection is empty. -/
theorem advanceCarrier_active_nil {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X)
    (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : ∀ i ∈ select (proposals X.archive X.active),
      ∃ p ∈ proposals X.archive X.active, (childCore p.1 p.2 stratum prov).id = i)
    (hfresh : ∀ p ∈ proposals X.archive X.active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive)
    (h0 : X.active = []) :
    (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).active = [] := by
  change select (proposals X.archive X.active) = []
  rcases hsel' : select (proposals X.archive X.active) with _ | ⟨i, rest⟩
  · rfl
  · exfalso
    have hi : i ∈ select (proposals X.archive X.active) := by
      rw [hsel']; exact List.mem_cons_self
    obtain ⟨p, hp, _⟩ := hsel i hi
    rw [h0, proposals_nil] at hp
    exact absurd hp List.not_mem_nil

/-! ## Statement 3 — empty support survives every schedule -/

/-- **An empty active support stays empty along a whole schedule.** Induction on
    the tick count `n`: the base case is the given tick-zero carrier, which is
    empty by hypothesis; the successor case is one lawful advance of the
    previous carrier, which is empty by the induction hypothesis, so
    `advanceCarrier_active_nil` applies. -/
theorem iterate_active_nil {Aux : Type} {h : ℕ} (pol : Policy Aux h)
    (X0 : TickCarrier Aux h) (hX0 : Seeded X0) (h0 : X0.active = [])
    (n : ℕ) (hn : n ≤ h) : (iterate pol X0 hX0 n hn).active = [] := by
  induction n with
  | zero => rw [iterate_zero]; exact h0
  | succ k ih =>
      rw [iterate_succ]
      exact advanceCarrier_active_nil _ _ _ _ _ _ _ _ (ih (Nat.le_of_succ_le hn))

/-! ## Statement 4 — `gammaB []` empties the tick-zero carrier's support -/

/-- **The tick-zero carrier built from `gammaB []` has empty active support.**
    `toTick0`'s active list is the identifiers of `S̃₀`; adjoining `gammaB []`
    to the declared predicates empties `S̃₀` by `S0tilde_gammaB_nil`, so the
    list of its identifiers is empty. -/
theorem toTick0_gammaB_nil_active {Aux : Type} (X : SeedInitContext Aux Aux) (h : ℕ)
    (F : Frame) (N : ℕ) (preds : List (OccPred (InitContext Aux)))
    (adm : List (QuestionId × Aux)) :
    (X.toTick0 h F N (preds ++ [gammaB []]) adm).active = [] := by
  change (S0tilde F N (preds ++ [gammaB []]) X.toInitContext X.seeds).map
      ProposalRecord.id = []
  rw [S0tilde_gammaB_nil F N preds X.toInitContext X.seeds]
  rfl

/-! ## Statement 5 — the terminal report is `empty` -/

/-- **Corollary 17.8, carried to the terminal report.** For every schedule and
    every positive horizon, the question with `gammaB []` adjoined reaches a
    terminal report whose status is `empty`: the terminal carrier `Term` is the
    iterate at the horizon, whose active support is empty by `iterate_active_nil`
    (its tick-zero support is empty by `toTick0_gammaB_nil_active`), so the
    report's status is `termStatus 0 = empty`. -/
theorem gammaB_nil_report_empty {Aux EvalAux : Type} (X : SeedInitContext Aux Aux)
    (F : Frame) (N : ℕ) (preds : List (OccPred (InitContext Aux)))
    (adm : List (QuestionId × Aux)) (h : ℕ) (pol : Policy Aux h) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    (Report.of pol (X.toTick0 h F N (preds ++ [gammaB []]) adm)
      (X.toTick0_seeded h F N (preds ++ [gammaB []]) adm) hh evalLedger).status = .empty := by
  rw [Report.of_status, Report.of_Sh]
  have hterm : (Term pol (X.toTick0 h F N (preds ++ [gammaB []]) adm)
      (X.toTick0_seeded h F N (preds ++ [gammaB []]) adm)).active = [] := by
    unfold Term
    exact iterate_active_nil pol _ _
      (toTick0_gammaB_nil_active X h F N preds adm) h (le_refl h)
  rw [hterm]
  rfl

/-! ## Statement 6 — the concrete empty-question seed context -/

/-- **The root seed's support-free initialization context** (Definition 4.7):
    the canonical observer, the canonical seed question, the one root-seed
    active family, and its one immutable seed core, with the three structural
    fields closed exactly as `ofInitContext` closes them. -/
def emptySeedCtx : SeedInitContext Unit Unit where
  observer := observer164
  question := canonicalQuestion []
  active := [⟨Frame.empty, []⟩]
  seedArchive := [seedCore seed164Id ⟨Frame.empty, []⟩ 0 seed164Prov]
  initLedger := []
  seed_core := by
    intro c hc
    rw [List.mem_singleton.mp hc]
    rfl
  one_core_per_seed := rfl
  seed_ids_nodup := List.nodup_singleton _

/-! ## Statement 7 — the concrete seven-tick empty question -/

/-- **Corollary 17.8, the concrete witness.** The seven-tick question of the
    root seed, run under Definition 8.1 with the predicate that admits
    nothing (`gammaB []`), has terminal status `empty` at horizon 7. An instance
    of `gammaB_nil_report_empty` at the concrete context. -/
theorem emptyQuestion_report_empty :
    (Report.of axiomPolicy
      (emptySeedCtx.toTick0 hQ Frame.empty sevenTickHorizon ([] ++ [gammaB []]) [])
      (emptySeedCtx.toTick0_seeded hQ Frame.empty sevenTickHorizon ([] ++ [gammaB []]) [])
      (by decide) ([] : List (QuestionId × EvalRecord Unit))).status = .empty :=
  gammaB_nil_report_empty emptySeedCtx Frame.empty sevenTickHorizon [] [] hQ axiomPolicy
    (by decide) []

#print axioms proposals_nil
#print axioms advanceCarrier_active_nil
#print axioms iterate_active_nil
#print axioms toTick0_gammaB_nil_active
#print axioms gammaB_nil_report_empty
#print axioms emptySeedCtx
#print axioms emptyQuestion_report_empty

end RatioSpace.Two.EmptyQuestion
