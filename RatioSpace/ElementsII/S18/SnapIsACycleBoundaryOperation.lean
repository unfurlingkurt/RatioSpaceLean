/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S18.Snap
import RatioSpace.ElementsII.S16.CrystallizationPattern
import RatioSpace.ElementsII.S16.RootChainState
/-!
  Elements II §18, Theorem 18.3, Snap is a cycle-boundary
  operation, outside the domain of the one-tick map.

  **Book statement.** *"The existence of a coherent snap does not imply
  `𝔎_𝒞(𝔛_{τ,h}) = 𝔛_{τ,h}` or that the unique occurrence would remain unique
  under an unrestricted extra tick. Proof. The one-tick map is not defined on
  the terminal carrier of the current question by Definition 11.1. Even after a
  new question authorizes a further advance, Corollary 8.11 shows that a
  singleton whose two children are admitted reopens to an exact pair."*

  **The two clauses.** The first clause is `Snap.terminal_not_lawful`. The
  second is composed here; `pair_support` and `lone_seed_keeps_both` are its
  core.

  **Contents.**
  * `singleton_reopens_to_pair`: on any lawful carrier, at any observer, with
    any horizon, a singleton support whose two children are admitted and
    addressed advances under Definition 8.1 to exactly the two
    children's identifiers.
  * `snap_then_reopens`: a defined snap, and any carrier a new question poses
    on the same archive and active support that may advance (so the unique
    occurrence's children are admitted), gives a next support of two
    identifiers: the unique occurrence does not remain unique.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_17

open Mat2 Word Frame Pres RatioSpace RatioSpace.Two RatioSpace.Two.Advance
  RatioSpace.Two.Accumulation RatioSpace.Two.Terminal RatioSpace.Two.Snap
  RatioSpace.Two.RootOrbit RatioSpace.Two.Beat RatioSpace.Two.RootChainCarrier

/-- **Corollary 8.11 on the selection**, exactly: both children and nothing
    else. -/
theorem axiomSelect_single_pair {MO : Mat2} {stratum : ℕ} {prov : Provenance}
    {archive : List Core} {active : List QuestionId} {c : Core} (hc : c.WellFormed)
    (hone : archive.filter (fun d => d.id ∈ active) = [c])
    (hadm : ∀ b : Bool, negLoad (Q MO (childCore c b stratum prov).fullMatrix) = 0)
    {yF yT : IPres}
    (hF : addrOf MO (childCore c false stratum prov) = some yF)
    (hT : addrOf MO (childCore c true stratum prov) = some yT) :
    axiomSelect MO stratum prov (proposals archive active)
      = [(childCore c false stratum prov).id, (childCore c true stratum prov).id] := by
  obtain ⟨hcores, _, m1, m2⟩ := lone_seed_keeps_both hone hadm hF hT
  have hne : (childCore c false stratum prov).id ≠ (childCore c true stratum prov).id := by
    intro hid
    rw [childCore_id c hc, childCore_id c hc] at hid
    exact absurd (child_id_inj hid).2 (by decide)
  rw [axiomSelect_eq, hcores] at m1 m2 ⊢
  cases ha : keepPred MO stratum prov (proposals archive active) (childCore c false stratum prov) <;>
    cases hb : keepPred MO stratum prov (proposals archive active) (childCore c true stratum prov) <;>
    simp only [List.filter_cons, List.filter_nil, ha, hb, if_true, if_false, Bool.false_eq_true,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at m1 m2 ⊢
  all_goals first | exact absurd m1 hne | exact absurd m2 (Ne.symm hne)

/-- **Theorem 18.3, second clause.** Any lawful carrier whose active support is
    one well-formed core with both children admitted and addressed at the
    carrier's observer advances to an exact pair: the two children. -/
theorem singleton_reopens_to_pair {Aux : Type} {h : ℕ} (Y : TickCarrier Aux h) (hlaw : Lawful Y)
    (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux)) (hsel : _) (hfresh : _)
    {c : Core} (hc : c.WellFormed)
    (hone : Y.archive.filter (fun d => d.id ∈ Y.active) = [c])
    (hadm : ∀ b : Bool, negLoad (Q Y.observer.matrix (childCore c b s p).fullMatrix) = 0)
    {yF yT : IPres}
    (hF : addrOf Y.observer.matrix (childCore c false s p) = some yF)
    (hT : addrOf Y.observer.matrix (childCore c true s p) = some yT) :
    (advanceCarrier Y hlaw (axiomSelect Y.observer.matrix s p) s p Δ hsel hfresh).active
      = [(childCore c false s p).id, (childCore c true s p).id] :=
  axiomSelect_single_pair hc hone hadm hF hT

/-- **Theorem 18.3, composed.** A defined snap leaves one occurrence `x` at the
    horizon. If a new question poses a lawful carrier `Y` (any horizon, any
    auxiliary type) on the same archive and the same active support, under the
    tick-zero invariant, and `x`'s two children are admitted and addressed at
    `Y`'s observer, then one further advance has two active identifiers, not
    one. -/
theorem snap_then_reopens {RawAux EvalAux Aux : Type} {h h' : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) (hinv0 : CarrierInv X0)
    {pr : Cand EvalAux × Report RawAux EvalAux h}
    (hp : snap pol X0 hX0 hh evalLedger = some pr)
    (Y : TickCarrier Aux h') (hlaw : Lawful Y)
    (hYa : Y.archive = (Term pol X0 hX0).archive) (hYs : Y.active = (Term pol X0 hX0).active)
    (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux)) (hsel : _) (hfresh : _)
    (hadm : ∀ x ∈ (Term pol X0 hX0).archive, ∀ b : Bool,
      negLoad (Q Y.observer.matrix (childCore x b s p).fullMatrix) = 0)
    (haddr : ∀ x ∈ (Term pol X0 hX0).archive, ∀ b : Bool,
      ∃ y, addrOf Y.observer.matrix (childCore x b s p) = some y) :
    (advanceCarrier Y hlaw (axiomSelect Y.observer.matrix s p) s p Δ hsel hfresh).active.length = 2 ∧
      (Term pol X0 hX0).active.length = 1 := by
  have hinv : CarrierInv (Term pol X0 hX0) := iterate_carrierInv pol X0 hX0 hinv0 h (le_refl h)
  have hsome : (snap pol X0 hX0 hh evalLedger).isSome = true := by rw [hp]; rfl
  have hstat := (snap_isSome_iff pol X0 hX0 hh evalLedger) ▸ hsome
  have hst : termStatus (Term pol X0 hX0).active.length = .singleton :=
    (crystallize_isSome_iff_singleton pol X0 hX0 hh evalLedger hinv.1 hinv.2.2).mp hstat
  have hlen1 : (Term pol X0 hX0).active.length = 1 := by
    generalize hk : (Term pol X0 hX0).active.length = k at hst ⊢
    rcases k with _ | _ | k
    · exact absurd (show TermStatus.empty = .singleton from hst) (by decide)
    · rfl
    · exact absurd (show TermStatus.unresolvedMultiple = .singleton from hst) (by decide)
  unfold crystallize at hstat
  have hlenE := TickCarrier.ensemble_length_eq_active (Term pol X0 hX0) evalLedger hinv.1 hinv.2.2
  unfold ensemble at hlenE
  rw [List.length_map, hlen1] at hlenE
  obtain ⟨x, hx⟩ : ∃ x, (Term pol X0 hX0).archive.filter
      (fun d => decide (d.id ∈ (Term pol X0 hX0).active)) = [x] := by
    generalize (Term pol X0 hX0).archive.filter
      (fun d => decide (d.id ∈ (Term pol X0 hX0).active)) = L at hlenE ⊢
    rcases L with _ | ⟨x, _ | ⟨y, t⟩⟩
    · exact absurd hlenE (by decide)
    · exact ⟨x, rfl⟩
    · exact absurd (Nat.succ.inj hlenE) (Nat.succ_ne_zero _)
  have hxmem : x ∈ (Term pol X0 hX0).archive :=
    (List.mem_filter.mp (by rw [hx]; exact List.Mem.head _)).1
  have hone : Y.archive.filter (fun d => d.id ∈ Y.active) = [x] := by
    rw [hYa, hYs]; exact hx
  obtain ⟨yF, hF⟩ := haddr x hxmem false
  obtain ⟨yT, hT⟩ := haddr x hxmem true
  refine ⟨?_, hlen1⟩
  rw [singleton_reopens_to_pair Y hlaw s p Δ hsel hfresh (hinv.2.1 x hxmem) hone
    (hadm x hxmem) hF hT]
  rfl

#print axioms axiomSelect_single_pair
#print axioms singleton_reopens_to_pair
#print axioms snap_then_reopens

end G2_17
end Gaps
end RatioSpace
