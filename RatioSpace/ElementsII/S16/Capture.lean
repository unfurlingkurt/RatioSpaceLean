/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S13.SideExchange
import RatioSpace.ElementsII.S16.RootOrbit
/-!
  Elements II §16 Theorem 16.12 — Capture of initial ensembles by the
  lone-seed regime.

  **What this file builds.**

  Item 3 (side-exchange invariance persists, and no later support is a
  singleton) is built in full, as a genuine theorem over any `Policy` (a schedule on the
    carriers a run
  from a seed reaches; the book's rule is one, `AxiomPolicy.axiomPolicy`)
  satisfying the two properties any Definition-8.1-style selector
  actually has: it respects `List.Perm` of its own input, and it is
  self-equivariant under the carrier-level side exchange in exactly the shape
  `SideExchange.lean`'s own `hsel_equiv` already uses. Given those, and given
  the active support at some tick `j` is invariant under the exchange (as a
  `List.Perm`, the same read Theorem 16.2 uses) — and, honestly, given the
  *archive* is invariant too, a hypothesis the book's own item 3 does not name
  but the induction genuinely needs, since Definition 11.6 archives every
  proposal regardless of selection, so the archive's own invariance has to be
  carried forward alongside the active support's — every later tick's active
  support is invariant, and (Theorem 16.2) none of them is a singleton.

  **Items 1 and 2 are built in `WordDynamics.lean`:** the
  "tick-`i` support of the lone-seed question with seed `x`" is `wIter i [x]`,
  one tick of Definition 8.1 on words, and `nextCores_words` proves the
  tick map agrees with it (`theorem_16_12_item1`, `_item2`, `_item1_governed`,
  `_item1_beat`).

  This file builds the exact word-level fact their proof invokes: `childCore`'s four
  "world" fields (`fullWord`, `fullMatrix`, `frame`, `addr`) and its two
  derived fields (`closure`, `imbalance`) are functions of the parent's own
  `(seed, relWord)` pair and the hand alone — never of `id`, `seedId`,
  `parent`, the entry stratum, or the provenance. That is the Lean content of
  "two questions whose current supports carry the same words ... produce the
  same proposal words ... the stable identifiers differ in their question and
  seed tags but enter no comparison," and it is exactly Proposition 11.7's own
  comment (`Advance.lean`) read at *two different* identifiers rather than
  one.

  Proposition 16.13 is in `Transient.lean`.
-/

namespace RatioSpace
namespace Two
namespace Capture

open Mat2 Word Frame Pres RatioSpace Advance Accumulation SideExchange RootOrbit

/-! ## Item 3, first half: no later support is a singleton

    Purely structural, and needs no invariance hypothesis by itself: every
    identifier `advanceCarrier` places in the next active support is, by
    `hsel`, the identifier of some proposal's child — and a child's own
    relative word is its parent's with one hand appended (Lemma 12.1's own
    `child_rel_length`), so it is never `[]`. An identifier whose relative
    word is `[]` is the only kind the exchange can fix (`QuestionId.mirror`
    only touches `rel`, and flipping every bit of a nonempty word always
    changes it), so nothing in a support reached by at least one tick can be
    fixed by the exchange. -/

/-- `mirrorWord` never fixes a nonempty word: flipping every bit changes the
    first one. -/
theorem mirrorWord_ne_self_of_ne_nil : ∀ {w : Word}, w ≠ [] → mirrorWord w ≠ w
  | [], h => absurd rfl h
  | b :: t, _ => by
      rw [mirrorWord_cons]
      intro heq
      have hb : (!b) = b := (List.cons.injEq _ _ _ _).mp heq |>.1
      cases b <;> simp at hb

/-- **The exchange's only possible fixed identifiers are the ones with empty
    relative word** — exactly the tick-zero seed, never a proposed child. -/
theorem QuestionId.mirror_ne_self_of_rel_ne_nil {i : QuestionId} (h : i.rel ≠ []) :
    QuestionId.mirror i ≠ i := by
  intro heq
  apply mirrorWord_ne_self_of_ne_nil h
  have hr : (QuestionId.mirror i).rel = i.rel := by rw [heq]
  simpa [QuestionId.mirror] using hr

/-- A child's own identifier carries its parent's relative word with the hand
    appended — `rfl`, since `childCore`/`childProposal`/`proposal` build `.id`
    from `{ id0 with rel := v ++ [g] }` with no reference to well-formedness. -/
theorem childCore_id_rel (c : Core) (g : Bool) (entry : ℕ) (prov : Provenance) :
    (childCore c g entry prov).id.rel = c.relWord ++ [g] := rfl

theorem childCore_id_rel_ne_nil (c : Core) (g : Bool) (entry : ℕ) (prov : Provenance) :
    (childCore c g entry prov).id.rel ≠ [] := by
  rw [childCore_id_rel]
  simp

/-- **Every occurrence reached by one more tick has a nonempty relative word,
    unconditionally.** No invariance hypothesis, no policy hypothesis: this is
    `hsel` plus `childCore_id_rel_ne_nil`. -/
theorem active_rel_ne_nil_of_advance {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId)
    (stratum : ℕ) (prov : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : ∀ i ∈ select (proposals X.archive X.active),
      ∃ p ∈ proposals X.archive X.active, (childCore p.1 p.2 stratum prov).id = i)
    (hfresh : ∀ p ∈ proposals X.archive X.active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds X.archive) :
    ∀ i ∈ (advanceCarrier X hlaw select stratum prov Δ hsel hfresh).active, i.rel ≠ [] := by
  intro i hi
  have hi' : i ∈ select (proposals X.archive X.active) := hi
  obtain ⟨p, _, hpeq⟩ := hsel i hi'
  rw [← hpeq]
  exact childCore_id_rel_ne_nil p.1 p.2 stratum prov

/-! ## Perm-congruence infrastructure for the invariance-persistence half -/

/-- `proposals` reads its `active` argument only through membership, so a
    `List.Perm`-related `active` gives the *same* proposal list, not merely a
    permuted one. -/
theorem proposals_active_perm_congr (archive : List Core) {active active' : List QuestionId}
    (h : active.Perm active') :
    proposals archive active = proposals archive active' := by
  unfold proposals
  congr 1
  apply List.filter_congr
  intro c _
  exact decide_eq_decide.mpr h.mem_iff

/-- `keyedUnion`, permuted in both arguments at once — `keyedUnion_perm_right`
    (`SideExchange.lean`) generalized to move the first argument too. -/
theorem keyedUnion_perm {H H' L L' : List Core} (hH : H.Perm H') (hL : L.Perm L') :
    (keyedUnion H L).Perm (keyedUnion H' L') := by
  unfold keyedUnion
  have hids : (archIds H).Perm (archIds H') := hH.map _
  have hfilter_eq : L.filter (fun y => ¬ (y.id ∈ archIds H))
      = L.filter (fun y => ¬ (y.id ∈ archIds H')) := by
    apply List.filter_congr
    intro y _
    simp only [decide_not]
    exact congrArg (! ·) (decide_eq_decide.mpr hids.mem_iff)
  rw [hfilter_eq]
  exact List.Perm.append hH (hL.filter _)

/-- `advanceArchive`, permuted congruently in both arguments. -/
theorem advanceArchive_perm_congr {archive archive' : List Core} {active active' : List QuestionId}
    (hA : archive.Perm archive') (hS : active.Perm active') (stratum : ℕ) (prov : Provenance) :
    (advanceArchive archive active stratum prov).Perm
      (advanceArchive archive' active' stratum prov) := by
  unfold advanceArchive
  have hprop : (proposals archive active).Perm (proposals archive' active') := by
    rw [proposals_active_perm_congr archive hS]
    exact proposals_perm active' hA
  exact keyedUnion_perm hA (hprop.map _)

/-- **One tick preserves archive-level side-exchange invariance**, given the
    active support is invariant too — `advanceArchive_mirror_perm` (Theorem
    13.3) is unconditional, and this supplies the missing congruence to read
    it at a *fixed* archive/active pair rather than across the mirror map. -/
theorem archive_mirror_invariant_step {archive : List Core} {active : List QuestionId}
    (hArch : (mirrorArchive archive).Perm archive)
    (hAct : (active.map QuestionId.mirror).Perm active)
    (stratum : ℕ) (prov : Provenance) :
    (mirrorArchive (advanceArchive archive active stratum prov)).Perm
      (advanceArchive archive active stratum prov) := by
  have h1 := advanceArchive_mirror_perm archive active stratum prov
  have h2 : (advanceArchive (mirrorArchive archive) (active.map QuestionId.mirror) stratum
    prov).Perm
      (advanceArchive archive active stratum prov) :=
    advanceArchive_perm_congr hArch hAct stratum prov
  exact h1.symm.trans h2

/-- **One tick preserves active-support invariance**, given the selector is
    Perm-invariant and mirror-equivariant *at this step's own input* (the
    latter is exactly `advanceCarrier_mirror_componentwise`'s `hsel_equiv`,
    read at one fixed archive/active pair instead of across two carriers). -/
theorem active_mirror_invariant_step {archive : List Core} {active : List QuestionId}
    {select : List (Core × Bool) → List QuestionId}
    (hEquiv : select (proposals (mirrorArchive archive) (active.map QuestionId.mirror))
        = (select (proposals archive active)).map QuestionId.mirror)
    (hSelPerm : ∀ {P P' : List (Core × Bool)}, P.Perm P' → (select P).Perm (select P'))
    (hArch : (mirrorArchive archive).Perm archive)
    (hAct : (active.map QuestionId.mirror).Perm active) :
    ((select (proposals archive active)).map QuestionId.mirror).Perm
      (select (proposals archive active)) := by
  have hQ : (proposals (mirrorArchive archive) (active.map QuestionId.mirror)).Perm
      (proposals archive active) := by
    rw [proposals_active_perm_congr (mirrorArchive archive) hAct]
    exact proposals_perm active hArch
  have h1 := hSelPerm hQ
  rw [hEquiv] at h1
  exact h1

/-! ## The Policy-level property, and its persistence along a whole schedule -/

/-- **A Policy with no preferred side.** At every lawful carrier it might be
    asked to advance, its selector respects `List.Perm` of its own input list,
    and it is equivariant under the carrier-level side exchange in exactly
    `hsel_equiv`'s own shape. Asked only at carriers a run reaches
    (`RunInv`), where the policy is defined. Both are true of any selector actually built
    from Definition 8.1 over a mirror-fixed observer — nothing here
    invents them: the second is the hypothesis
    `advanceCarrier_mirror_componentwise` already carries, and the first is
    the same enumeration-independence Theorem 12.7 already proves for
    `axiomSelect`-shaped selectors (`support_perm_mem`/`proposals_perm`),
    named as a hypothesis on the general `Policy` rather than reproved at a
    concrete instance in this file. -/
def PolicySideRobust {Aux : Type} {h : ℕ} (pol : Policy Aux h) : Prop :=
  ∀ (X : TickCarrier Aux h) (hlaw : Lawful X) (hinv : RunInv X),
    (∀ {P P' : List (Core × Bool)}, P.Perm P' →
        ((pol X hlaw hinv).select P).Perm ((pol X hlaw hinv).select P')) ∧
    (pol X hlaw hinv).select (proposals (mirrorArchive X.archive) (X.active.map QuestionId.mirror))
      = ((pol X hlaw hinv).select (proposals X.archive X.active)).map QuestionId.mirror

/-- **Invariance, once reached, persists at every later tick a schedule
    visits.** Both the archive's and the active support's, carried together
    because one step's proof of either needs both at the step before. -/
theorem invariance_persists {Aux : Type} {h : ℕ} (pol : Policy Aux h)
    (hRobust : PolicySideRobust pol) (X0 : TickCarrier Aux h) (hX0 : Seeded X0)
    (j : ℕ) (hj : j ≤ h)
    (hArchj : (mirrorArchive (iterate pol X0 hX0 j hj).archive).Perm
      (iterate pol X0 hX0 j hj).archive)
    (hActj : ((iterate pol X0 hX0 j hj).active.map QuestionId.mirror).Perm
      (iterate pol X0 hX0 j hj).active) :
    ∀ (i : ℕ) (hji : j + i ≤ h),
      (mirrorArchive (iterate pol X0 hX0 (j + i) hji).archive).Perm
        (iterate pol X0 hX0 (j + i) hji).archive ∧
      ((iterate pol X0 hX0 (j + i) hji).active.map QuestionId.mirror).Perm
        (iterate pol X0 hX0 (j + i) hji).active
  | 0, hji => ⟨hArchj, hActj⟩
  | i + 1, hji => by
      have hji' : j + i ≤ h := by omega
      have IH := invariance_persists pol hRobust X0 hX0 j hj hArchj hActj i hji'
      have hjii : j + i + 1 ≤ h := hji
      have hstep := iterate_succ pol X0 hX0 (j + i) hjii
      have hlaw : Lawful (iterate pol X0 hX0 (j + i) hji') := iterate_lawful pol X0 hX0 (j + i) hjii
      obtain ⟨hSelPerm, hEquiv⟩ :=
        hRobust (iterate pol X0 hX0 (j + i) hji') hlaw (iterate_runInv pol X0 hX0 (j + i) hji')
      have e : iterate pol X0 hX0 (j + (i + 1)) hji = iterate pol X0 hX0 (j + i + 1) hjii := rfl
      rw [e, hstep]
      constructor
      · exact archive_mirror_invariant_step IH.1 IH.2 _ _
      · exact active_mirror_invariant_step hEquiv (fun hp => hSelPerm hp) IH.1 IH.2

/-- **Theorem 16.12, item 3.** If the active support at tick `j` is invariant
    under the side exchange, so is every support at a later tick `j+(i+1)`,
    and none of them is a singleton. The archive-invariance hypothesis is the
    one addition to the book's own statement: the induction that carries the
    active support's invariance forward needs it at every step, since
    Definition 11.6 archives both children of every active occurrence
    regardless of which the selector keeps. -/
theorem theorem_16_12_item3 {Aux : Type} {h : ℕ} (pol : Policy Aux h)
    (hRobust : PolicySideRobust pol) (X0 : TickCarrier Aux h) (hX0 : Seeded X0)
    (j : ℕ) (hj : j ≤ h)
    (hArchj : (mirrorArchive (iterate pol X0 hX0 j hj).archive).Perm
      (iterate pol X0 hX0 j hj).archive)
    (hActj : ((iterate pol X0 hX0 j hj).active.map QuestionId.mirror).Perm
      (iterate pol X0 hX0 j hj).active)
    (i : ℕ) (hji : j + (i + 1) ≤ h) :
    (((iterate pol X0 hX0 (j + (i + 1)) hji).active.map QuestionId.mirror).Perm
        (iterate pol X0 hX0 (j + (i + 1)) hji).active) ∧
    (iterate pol X0 hX0 (j + (i + 1)) hji).active.length ≠ 1 := by
  have hinv := invariance_persists pol hRobust X0 hX0 j hj hArchj hActj (i + 1) hji
  refine ⟨hinv.2, ?_⟩
  have hji' : j + i ≤ h := by omega
  have hjii : j + i + 1 ≤ h := hji
  have hstep := iterate_succ pol X0 hX0 (j + i) hjii
  have hlaw : Lawful (iterate pol X0 hX0 (j + i) hji') := iterate_lawful pol X0 hX0 (j + i) hjii
  have hfree : ∀ x ∈ (iterate pol X0 hX0 (j + (i + 1)) hji).active, QuestionId.mirror x ≠ x := by
    intro x hx
    have e : iterate pol X0 hX0 (j + (i + 1)) hji = iterate pol X0 hX0 (j + i + 1) hjii := rfl
    rw [e, hstep] at hx
    exact QuestionId.mirror_ne_self_of_rel_ne_nil
      (active_rel_ne_nil_of_advance _ hlaw _ _ _ _ _ _ x hx)
  exact iterated_parity_obstruction _ hfree hinv.2

/-! ## Items 1 and 2's word-level determinacy lemma

    Definition 11.6's proposal step routes every occurrence through
    `childCore c g entry prov := Core.ofProposal (childProposal c.seedId c.seed
    c.relWord g) (some c.id) (some g) entry prov`, and `childProposal id0 seed
    v g := proposal id0 seed (v ++ [g])`. Every one of `proposal`'s six fields
    except `.id` and `.seedId` is a function of `(seed, v)` alone: `fullWord :=
    seed.word ++ v`, `fullMatrix := seed.matrix * Word.G v`, `frame :=
    Frame.walk seed.frame v`, `addr := Frame.addressed seed.frame v`, and
    `Core.ofProposal` derives `closure`/`imbalance` from that same `fullWord`.
    So a child's own "word content" never reads the parent's stable
    identifier, its seed identifier, its entry stratum, or its provenance —
    exactly "the stable identifiers differ in their question and seed tags
    but enter no comparison," stated at two parents rather than asserted
    of one. -/

/-- **The word-level determinacy of one tick, at the child.** Two parent
    cores agreeing on `(seed, relWord)` produce children (by the same hand,
    however differently tagged, entered, or provenanced) that agree on every
    field the tick's downstream comparisons can read. -/
theorem childCore_word_congr {c c' : Core} (hseed : c.seed = c'.seed)
    (hrel : c.relWord = c'.relWord) (g : Bool) (stratum stratum' : ℕ)
    (prov prov' : Provenance) :
    (childCore c g stratum prov).fullWord = (childCore c' g stratum' prov').fullWord ∧
    (childCore c g stratum prov).fullMatrix = (childCore c' g stratum' prov').fullMatrix ∧
    (childCore c g stratum prov).frame = (childCore c' g stratum' prov').frame ∧
    (childCore c g stratum prov).addr = (childCore c' g stratum' prov').addr ∧
    (childCore c g stratum prov).closure = (childCore c' g stratum' prov').closure ∧
    (childCore c g stratum prov).imbalance = (childCore c' g stratum' prov').imbalance := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [childCore, childProposal, proposal, Core.ofProposal, hseed, hrel]

/-- **The address a child's tick-comparison reads is fixed by its matrix
    alone**, so `childCore_word_congr`'s `fullMatrix` clause already decides
    it: two word-agreeing children resolve to the same address under the same
    observer, never merely a resembling one. -/
theorem addrOf_congr_of_fullMatrix_eq {MO : Mat2} {c c' : Core} (h : c.fullMatrix = c'.fullMatrix) :
    RootOrbit.addrOf MO c = RootOrbit.addrOf MO c' := by
  unfold RootOrbit.addrOf
  rw [h]

/-- **The direct-positive admission test itself is a function of the matrix
    alone.** Two word-agreeing children are admitted or rejected together,
    under the same observer — the first half of "the same tensions, the same
    certificates, the same maximizer words," at one occurrence. -/
theorem admittedCore_test_congr {MO : Mat2} {c c' : Core} (h : c.fullMatrix = c'.fullMatrix) :
    decide (negLoad (Q MO c.fullMatrix) = 0) = decide (negLoad (Q MO c'.fullMatrix) = 0) := by
  rw [h]

end Capture
end Two
end RatioSpace
