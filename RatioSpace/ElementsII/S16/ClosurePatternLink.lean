/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.ClosurePattern
import RatioSpace.ElementsII.S16.CrystallizationPattern
/-!
  Elements II §16 Theorem 16.11: the bridge from Step 1's coefficient
  combinations to the tree's one-tick support.

  `Two/Beat11.lean` proved Step 1 on `grand F = [M_F(1,3), M_F(2,3), M_F(3,2),
  M_F(3,1)]`, which are coefficient combinations and not occurrences. Its header
  names two gaps. This file closes both at a sibling step, at observer `ε`.

  **(a) Lemma 16.10's reduction, in general.** For every frame `F` and every
  positive word `v`, `r_F(v) = M_F(a,b)` with `a:b = r(v)`: the relation `v`
  addresses below `F` is the coefficient combination whose pair is `v`'s own
  canonical address (`lemma_16_10_reduction`). The proof is the book's, read on
  the pair rather than on the matrix: every frame the walk reaches is linear in
  the two endpoints of `F`, with the coefficients of the same walk from `F_∅`
  (`walk_linear`). At depth two the four canonical addresses are `1:3, 2:3,
  3:2, 3:1`, so `r_F(LL) = gLL F` and so on (`addressed_LL` ... `addressed_RR`).

  **(b) The admitted family and the support, at a sibling step.** Let the
  active cores be the sibling pair `yL, yR` of one core `y`, and let the
  observer be `ε` (`MO = 1`, which is `RootOrbit.MOeps`). Then one advance
  under `axiomSelect`:
  * admits exactly the four grandchildren, in the order `yLL, yLR, yRL, yRR`
    (`sibling_admittedCores`); direct-positive admission never rejects, since
    every accumulated matrix is `G` of a word;
  * addresses them to exactly `grand F_y` (`sibling_admittedFam`), where
    `F_y = walk F_∅ (w₀ v)` is the frame of `y` in the observer's chart;
  * selects exactly the grandchildren whose address lies in
    `support (grand F_y)` (`sibling_axiomSelect`, a closed form).

  **The bridge (`sibling_step_generic`, `sibling_step_pos`,
  `sibling_step_neg`).** If `F_y` is `Generic`, every identifier selected is
  `yLL` or `yRR`; with `D ≥ 21` the selection is exactly `[yLL]`, with
  `D ≤ −21` exactly `[yRR]`. `advanceCarrier_active_*` state the same on the
  carrier `advanceCarrier` returns, since its `active` field is the selection.

  **Two hypotheses the book leaves implicit, both stated rather than assumed.**
  1. *The sibling pair is the whole active family, in that order.* This is the
     same `archive.filter (· ∈ active) = [...]` form `Beat.lone_seed_keeps_both`
     uses. The reversed order `[yR, yL]` is not covered by these statements; the
     family is then a permutation of `grand F_y` and `support_perm_mem` gives
     the same support, but the closed form of `axiomSelect` would list the
     identifiers in the other order.
  2. *`F_y` is the frame of the occurrence's word from `F_∅`.* `History.matrix`
     is `G word` with no start factor, so at observer `ε` the local address of
     a grandchild is `r(w₀ v g₁ g₂)` whatever the seed's declared start. When
     the seed starts at `F_∅`, as in every question built so far, this is the
     core's own `frame` field (`frame_eq_of_start_empty`).

  **Not built here.** Step 2 (the 527 non-generic frames and the `|D| ≤ 20`
  families), Step 3 (cousin steps), observers other than `ε`, and the induction
  assembling clauses 1-4 of the theorem. No book statement was found false in
  this pass.

  None of the theorems below uses `Classical.choice` (checked with
  `#print axioms` in a probe importing this module). `negLoad_zero_iff_nonneg`
  does carry choice, so admission is proved here directly on `G w`.
-/
-- `show` unfolds `walk`/`addressed`/`advanceCarrier` into the shape the
-- rewrites act on, as in `Two/Contrast.lean`.
set_option linter.style.show false

namespace RatioSpace
namespace Two
namespace Beat11Bridge

open Mat2 Word Frame Pres RatioSpace Advance Accumulation RootOrbit Beat Beat11 Contrast

/-! ## (a) Lemma 16.10's reduction `r_F(v) = M_F(a,b)` -/

/-- **Every frame a walk reaches is linear in the two endpoints it started
    from**, with the coefficients of the same walk from `F_∅`. Snoc induction:
    `stepL`/`stepR` add the two columns, and so do the coefficients. -/
theorem walk_linear (F : Frame) (v : Word) :
    (walk F v).plus.p = (walk empty v).plus.p * F.plus.p + (walk empty v).plus.q * F.minus.p ∧
    (walk F v).plus.q = (walk empty v).plus.p * F.plus.q + (walk empty v).plus.q * F.minus.q ∧
    (walk F v).minus.p = (walk empty v).minus.p * F.plus.p + (walk empty v).minus.q * F.minus.p ∧
    (walk F v).minus.q = (walk empty v).minus.p * F.plus.q + (walk empty v).minus.q * F.minus.q
      := by
  induction v using List.reverseRecOn with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · show F.plus.p = 1 * F.plus.p + 0 * F.minus.p
        rw [Nat.one_mul, Nat.zero_mul, Nat.add_zero]
      · show F.plus.q = 1 * F.plus.q + 0 * F.minus.q
        rw [Nat.one_mul, Nat.zero_mul, Nat.add_zero]
      · show F.minus.p = 0 * F.plus.p + 1 * F.minus.p
        rw [Nat.one_mul, Nat.zero_mul, Nat.zero_add]
      · show F.minus.q = 0 * F.plus.q + 1 * F.minus.q
        rw [Nat.one_mul, Nat.zero_mul, Nat.zero_add]
  | append_singleton w b ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      rw [walk_snoc, walk_snoc]
      cases b
      · refine ⟨?_, ?_, ?_, ?_⟩
        · show (walk F w).plus.p + (walk F w).minus.p
            = ((walk empty w).plus.p + (walk empty w).minus.p) * F.plus.p
              + ((walk empty w).plus.q + (walk empty w).minus.q) * F.minus.p
          rw [h1, h3]; ring
        · show (walk F w).plus.q + (walk F w).minus.q
            = ((walk empty w).plus.p + (walk empty w).minus.p) * F.plus.q
              + ((walk empty w).plus.q + (walk empty w).minus.q) * F.minus.q
          rw [h2, h4]; ring
        · exact h3
        · exact h4
      · refine ⟨?_, ?_, ?_, ?_⟩
        · exact h1
        · exact h2
        · show (walk F w).plus.p + (walk F w).minus.p
            = ((walk empty w).plus.p + (walk empty w).minus.p) * F.plus.p
              + ((walk empty w).plus.q + (walk empty w).minus.q) * F.minus.p
          rw [h1, h3]; ring
        · show (walk F w).plus.q + (walk F w).minus.q
            = ((walk empty w).plus.p + (walk empty w).minus.p) * F.plus.q
              + ((walk empty w).plus.q + (walk empty w).minus.q) * F.minus.q
          rw [h2, h4]; ring

/-- `r_F(v)`'s first component is `a·p₊ + b·p₋`, `a:b = r(v)`. -/
theorem addressed_p (F : Frame) (v : Word) :
    (addressed F v).p = (r v).p * F.plus.p + (r v).q * F.minus.p := by
  obtain ⟨h1, _, h3, _⟩ := walk_linear F v
  show (walk F v).plus.p + (walk F v).minus.p
    = ((walk empty v).plus.p + (walk empty v).minus.p) * F.plus.p
      + ((walk empty v).plus.q + (walk empty v).minus.q) * F.minus.p
  rw [h1, h3]; ring

/-- `r_F(v)`'s second component is `a·q₊ + b·q₋`, `a:b = r(v)`. -/
theorem addressed_q (F : Frame) (v : Word) :
    (addressed F v).q = (r v).p * F.plus.q + (r v).q * F.minus.q := by
  obtain ⟨_, h2, _, h4⟩ := walk_linear F v
  show (walk F v).plus.q + (walk F v).minus.q
    = ((walk empty v).plus.p + (walk empty v).minus.p) * F.plus.q
      + ((walk empty v).plus.q + (walk empty v).minus.q) * F.minus.q
  rw [h2, h4]; ring

/-- `ofPres?` on an interior presentation with known components, without the
    `split`/`simp` route. -/
theorem ofPres?_eq_some {A : Pres} {B : IPres} (hA : A.Interior)
    (hp : A.p = B.p) (hq : A.q = B.q) : IPres.ofPres? A = some B := by
  unfold IPres.ofPres?
  rw [dif_pos hA]
  exact congrArg some (IPres.eq_of hp hq)

/-- **Lemma 16.10's reduction.** For every frame `F` and every positive word
    `v`, the relation `v` addresses in `F` is the coefficient combination
    `M_F(a,b) = a•C₊ + b•C₋` with `a:b = r(v)`, `v`'s canonical address. -/
theorem lemma_16_10_reduction (F : Frame) (v : Word) :
    IPres.ofPres? (addressed F v)
      = some (comboI F (r v).p (r v).q (walk_mid_pos empty v).1 (walk_mid_pos empty v).2) :=
  ofPres?_eq_some (walk_mid_pos F v) (addressed_p F v) (addressed_q F v)

/-- The four canonical grandchild addresses `1:3, 2:3, 3:2, 3:1`. -/
theorem r_grand :
    ((r [false, false]).p, (r [false, false]).q) = (1, 3) ∧
    ((r [false, true]).p, (r [false, true]).q) = (2, 3) ∧
    ((r [true, false]).p, (r [true, false]).q) = (3, 2) ∧
    ((r [true, true]).p, (r [true, true]).q) = (3, 1) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem addressed_LL (F : Frame) : IPres.ofPres? (addressed F [false, false]) = some (gLL F) :=
  ofPres?_eq_some (walk_mid_pos F _) (addressed_p F _) (addressed_q F _)

theorem addressed_LR (F : Frame) : IPres.ofPres? (addressed F [false, true]) = some (gLR F) :=
  ofPres?_eq_some (walk_mid_pos F _) (addressed_p F _) (addressed_q F _)

theorem addressed_RL (F : Frame) : IPres.ofPres? (addressed F [true, false]) = some (gRL F) :=
  ofPres?_eq_some (walk_mid_pos F _) (addressed_p F _) (addressed_q F _)

theorem addressed_RR (F : Frame) : IPres.ofPres? (addressed F [true, true]) = some (gRR F) :=
  ofPres?_eq_some (walk_mid_pos F _) (addressed_p F _) (addressed_q F _)

/-! ## (b) The sibling step at observer `ε` -/

/-- The frame of core `y` read in the observer-`ε` chart: the walk of its full
    word from `F_∅`. -/
def frameEps (c : Core) : Frame := walk empty (c.seed.word ++ c.relWord)

/-- When the seed's declared start is `F_∅`, `frameEps` is the core's own
    `frame` field. -/
theorem frame_eq_of_start_empty (id0 : QuestionId) (seed : History) (v : Word)
    (parent : Option QuestionId) (hand : Option Bool) (e : ℕ) (prov : Provenance)
    (hs : seed.start = empty) :
    (Core.ofProposal (proposal id0 seed v) parent hand e prov).frame
      = frameEps (Core.ofProposal (proposal id0 seed v) parent hand e prov) := by
  show walk (walk seed.start seed.word) v = walk empty (seed.word ++ v)
  rw [hs]
  simp only [walk, List.foldl_append]

/-- The grandchild core `y g₁ g₂`, built at the tick's stratum and provenance
    from the sibling built at its own. -/
def gcore (c : Core) (g₁ g₂ : Bool) (s₁ : ℕ) (p₁ : Provenance) (s : ℕ) (p : Provenance) : Core :=
  childCore (childCore c g₁ s₁ p₁) g₂ s p

/-- A grandchild's accumulated matrix is `G` of its full word. -/
theorem gcore_fullMatrix (c : Core) (g₁ g₂ : Bool) (s₁ : ℕ) (p₁ : Provenance) (s : ℕ)
    (p : Provenance) :
    (gcore c g₁ g₂ s₁ p₁ s p).fullMatrix = G ((c.seed.word ++ c.relWord) ++ [g₁, g₂]) := by
  show G c.seed.word * G ((c.relWord ++ [g₁]) ++ [g₂]) = _
  rw [← G_append, List.append_assoc, List.append_assoc]
  rfl

/-- `Neg(G w) = 0`, proved on the entries, not through
    `negLoad_zero_iff_nonneg` (which carries `Classical.choice`). -/
theorem negLoad_G (w : Word) : negLoad (G w) = 0 := by
  obtain ⟨ha, hb, hc, hd⟩ := nonneg_G w
  unfold negLoad
  rw [max_eq_left (by omega : (-(G w).a) ≤ 0), max_eq_left (by omega : (-(G w).b) ≤ 0),
    max_eq_left (by omega : (-(G w).c) ≤ 0), max_eq_left (by omega : (-(G w).d) ≤ 0)]
  rfl

/-- Every grandchild is direct-positively admitted at observer `ε`. -/
theorem gcore_admitted (c : Core) (g₁ g₂ : Bool) (s₁ : ℕ) (p₁ : Provenance) (s : ℕ)
    (p : Provenance) :
    decide (negLoad (Q 1 (gcore c g₁ g₂ s₁ p₁ s p).fullMatrix) = 0) = true := by
  rw [Q_one, gcore_fullMatrix, negLoad_G]
  rfl

/-- **A grandchild's observer-`ε` address is `r_{F_y}(g₁g₂)`.** -/
theorem addrOf_gcore (c : Core) (g₁ g₂ : Bool) (s₁ : ℕ) (p₁ : Provenance) (s : ℕ)
    (p : Provenance) :
    addrOf 1 (gcore c g₁ g₂ s₁ p₁ s p) = IPres.ofPres? (addressed (frameEps c) [g₁, g₂]) := by
  have hQ : Q 1 (gcore c g₁ g₂ s₁ p₁ s p).fullMatrix
      = G ((c.seed.word ++ c.relWord) ++ [g₁, g₂]) := by
    rw [Q_one, gcore_fullMatrix]
  unfold addrOf
  rw [lambda_eq 1 _ hQ]
  show IPres.ofPres? (addressed empty _) = _
  rw [← addressed_walk]
  rfl

theorem addrOf_LL (c : Core) (s₁ : ℕ) (p₁ : Provenance) (s : ℕ) (p : Provenance) :
    addrOf 1 (gcore c false false s₁ p₁ s p) = some (gLL (frameEps c)) := by
  rw [addrOf_gcore, addressed_LL]

theorem addrOf_LR (c : Core) (s₁ : ℕ) (p₁ : Provenance) (s : ℕ) (p : Provenance) :
    addrOf 1 (gcore c false true s₁ p₁ s p) = some (gLR (frameEps c)) := by
  rw [addrOf_gcore, addressed_LR]

theorem addrOf_RL (c : Core) (s₁ : ℕ) (p₁ : Provenance) (s : ℕ) (p : Provenance) :
    addrOf 1 (gcore c true false s₁ p₁ s p) = some (gRL (frameEps c)) := by
  rw [addrOf_gcore, addressed_RL]

theorem addrOf_RR (c : Core) (s₁ : ℕ) (p₁ : Provenance) (s : ℕ) (p : Provenance) :
    addrOf 1 (gcore c true true s₁ p₁ s p) = some (gRR (frameEps c)) := by
  rw [addrOf_gcore, addressed_RR]

section sibling

variable {archive : List Core} {active : List QuestionId} {c : Core}
  {sL sR : ℕ} {pL pR : Provenance} (s : ℕ) (p : Provenance)

/-- The sibling pair proposes the four grandchild pairs, in order. -/
theorem sibling_proposals
    (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) :
    proposals archive active =
      [(childCore c false sL pL, false), (childCore c false sL pL, true),
       (childCore c true sR pR, false), (childCore c true sR pR, true)] := by
  unfold proposals
  rw [hsib]
  rfl

/-- **(b), admission.** At observer `ε` the admitted cores of a sibling step
    are exactly the four grandchildren, in the order `yLL, yLR, yRL, yRR`. -/
theorem sibling_admittedCores
    (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) :
    admittedCores 1 s p (proposals archive active) =
      [gcore c false false sL pL s p, gcore c false true sL pL s p,
       gcore c true false sR pR s p, gcore c true true sR pR s p] := by
  unfold admittedCores
  rw [sibling_proposals hsib]
  show List.filter _ [gcore c false false sL pL s p, gcore c false true sL pL s p,
       gcore c true false sR pR s p, gcore c true true sR pR s p] = _
  refine List.filter_eq_self.mpr (fun d hd => ?_)
  rcases List.mem_cons.mp hd with rfl | hd
  · exact gcore_admitted c false false sL pL s p
  rcases List.mem_cons.mp hd with rfl | hd
  · exact gcore_admitted c false true sL pL s p
  rcases List.mem_cons.mp hd with rfl | hd
  · exact gcore_admitted c true false sR pR s p
  rcases List.mem_cons.mp hd with rfl | hd
  · exact gcore_admitted c true true sR pR s p
  · cases hd

/-- **(b), the family.** The admitted family Definition 8.1 compares
    is exactly `grand F_y`. -/
theorem sibling_admittedFam
    (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) :
    admittedFam 1 s p (proposals archive active) = grand (frameEps c) := by
  unfold admittedFam
  rw [sibling_admittedCores s p hsib, List.filterMap_cons_some (addrOf_LL c sL pL s p),
    List.filterMap_cons_some (addrOf_LR c sL pL s p),
    List.filterMap_cons_some (addrOf_RL c sR pR s p),
    List.filterMap_cons_some (addrOf_RR c sR pR s p)]
  rfl

/-- `selPred` is membership in the support, on the family. -/
theorem selPred_iff (F : Frame) {y : IPres} (hy : y ∈ grand F) :
    selPred F y = true ↔ y ∈ support (grand F) := by
  constructor
  · intro h; exact List.mem_filter.mpr ⟨hy, h⟩
  · intro h; exact (List.mem_filter.mp h).2

/-- **(b), the selection, in closed form.** `axiomSelect` at a sibling step
    keeps exactly the grandchildren whose address passes Definition 8.1
    's filter on `grand F_y`, in the order `yLL, yLR, yRL, yRR`. -/
theorem sibling_axiomSelect
    (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) :
    axiomSelect 1 s p (proposals archive active) =
      ((if selPred (frameEps c) (gLL (frameEps c)) = true
          then [(gcore c false false sL pL s p).id] else []) ++
       (if selPred (frameEps c) (gLR (frameEps c)) = true
          then [(gcore c false true sL pL s p).id] else []) ++
       (if selPred (frameEps c) (gRL (frameEps c)) = true
          then [(gcore c true false sR pR s p).id] else []) ++
       (if selPred (frameEps c) (gRR (frameEps c)) = true
          then [(gcore c true true sR pR s p).id] else [])) := by
  unfold axiomSelect
  simp only []
  rw [sibling_admittedCores s p hsib, sibling_admittedFam s p hsib]
  rw [List.filter_cons, List.filter_cons, List.filter_cons, List.filter_cons]
  rw [addrOf_LL, addrOf_LR, addrOf_RL, addrOf_RR]
  dsimp only
  simp only [show (grand (frameEps c)).all (fun z => decide (coherenceOf (grand (frameEps c)) z
        ≤ coherenceOf (grand (frameEps c)) (gLL (frameEps c))))
      = selPred (frameEps c) (gLL (frameEps c)) from rfl,
    show (grand (frameEps c)).all (fun z => decide (coherenceOf (grand (frameEps c)) z
        ≤ coherenceOf (grand (frameEps c)) (gLR (frameEps c))))
      = selPred (frameEps c) (gLR (frameEps c)) from rfl,
    show (grand (frameEps c)).all (fun z => decide (coherenceOf (grand (frameEps c)) z
        ≤ coherenceOf (grand (frameEps c)) (gRL (frameEps c))))
      = selPred (frameEps c) (gRL (frameEps c)) from rfl,
    show (grand (frameEps c)).all (fun z => decide (coherenceOf (grand (frameEps c)) z
        ≤ coherenceOf (grand (frameEps c)) (gRR (frameEps c))))
      = selPred (frameEps c) (gRR (frameEps c)) from rfl]
  cases selPred (frameEps c) (gLL (frameEps c)) <;>
  cases selPred (frameEps c) (gLR (frameEps c)) <;>
  cases selPred (frameEps c) (gRL (frameEps c)) <;>
  cases selPred (frameEps c) (gRR (frameEps c)) <;> rfl

/-- `selPred` fails on anything strictly beaten by a family member. -/
theorem selPred_false_of_lt (F : Frame) {w z : IPres} (hz : z ∈ grand F)
    (h : coherenceOf (grand F) w < coherenceOf (grand F) z) : selPred F w = false := by
  cases hs : selPred F w
  · rfl
  · exact absurd (of_decide_eq_true (List.all_eq_true.mp hs z hz)) (not_le_of_lt_zphi h)

/-- `selPred` holds on anything that beats or ties every family member. -/
theorem selPred_true_of_max (F : Frame) {y : IPres}
    (h : ∀ z ∈ grand F, coherenceOf (grand F) z ≤ coherenceOf (grand F) y) :
    selPred F y = true :=
  List.all_eq_true.mpr (fun z hz => decide_eq_true (h z hz))

/-- **Theorem 16.11, Step 1, on the tree: a generic sibling step.** From the
    sibling pair of an occurrence whose frame is `Generic`, every identifier the
    one-tick advance selects is `yLL` or `yRR`. -/
theorem sibling_step_generic
    (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR])
    (hg : Generic (frameEps c)) :
    ∀ i ∈ axiomSelect 1 s p (proposals archive active),
      i = (gcore c false false sL pL s p).id ∨ i = (gcore c true true sR pR s p).id := by
  obtain ⟨h21, h34⟩ := step1_coherence (frameEps c) hg
  have hLR : selPred (frameEps c) (gLR (frameEps c)) = false :=
    selPred_false_of_lt _ (gLL_mem _) h21
  have hRL : selPred (frameEps c) (gRL (frameEps c)) = false :=
    selPred_false_of_lt _ (gRR_mem _) h34
  intro i hi
  rw [sibling_axiomSelect s p hsib, hLR, hRL] at hi
  revert hi
  cases selPred (frameEps c) (gLL (frameEps c)) <;>
  cases selPred (frameEps c) (gRR (frameEps c))
  · intro hi; cases hi
  · intro hi
    exact Or.inr (List.mem_singleton.mp hi)
  · intro hi
    exact Or.inl (List.mem_singleton.mp hi)
  · intro hi
    rcases List.mem_cons.mp hi with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)

/-- **Theorem 16.11, Step 1, on the tree, `D ≥ 21`.** The one-tick advance of a
    generic sibling pair selects exactly `[yLL]`. -/
theorem sibling_step_pos
    (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR])
    (hg : Generic (frameEps c))
    (hD : (frameEps c).minus.p * (frameEps c).minus.q + 21
      ≤ (frameEps c).plus.p * (frameEps c).plus.q) :
    axiomSelect 1 s p (proposals archive active) = [(gcore c false false sL pL s p).id] := by
  obtain ⟨h21, h34⟩ := step1_coherence (frameEps c) hg
  have h41 := step1_coherence_pos (frameEps c) hD
  have h31 := lt_trans h34 h41
  have hLL : selPred (frameEps c) (gLL (frameEps c)) = true := by
    refine selPred_true_of_max _ (fun z hz => ?_)
    rcases mem_grand hz with rfl | rfl | rfl | rfl
    · exact le_refl _
    · exact le_of_lt h21
    · exact le_of_lt h31
    · exact le_of_lt h41
  rw [sibling_axiomSelect s p hsib, hLL, selPred_false_of_lt _ (gLL_mem _) h21,
    selPred_false_of_lt _ (gLL_mem _) h31, selPred_false_of_lt _ (gLL_mem _) h41]
  rfl

/-- **Theorem 16.11, Step 1, on the tree, `D ≤ −21`.** The one-tick advance of a
    generic sibling pair selects exactly `[yRR]`. -/
theorem sibling_step_neg
    (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR])
    (hg : Generic (frameEps c))
    (hD : (frameEps c).plus.p * (frameEps c).plus.q + 21
      ≤ (frameEps c).minus.p * (frameEps c).minus.q) :
    axiomSelect 1 s p (proposals archive active) = [(gcore c true true sR pR s p).id] := by
  obtain ⟨h21, h34⟩ := step1_coherence (frameEps c) hg
  have h14 := step1_coherence_neg (frameEps c) hD
  have h24 := lt_trans h21 h14
  have hRR : selPred (frameEps c) (gRR (frameEps c)) = true := by
    refine selPred_true_of_max _ (fun z hz => ?_)
    rcases mem_grand hz with rfl | rfl | rfl | rfl
    · exact le_of_lt h14
    · exact le_of_lt h24
    · exact le_of_lt h34
    · exact le_refl _
  rw [sibling_axiomSelect s p hsib, hRR, selPred_false_of_lt _ (gRR_mem _) h14,
    selPred_false_of_lt _ (gRR_mem _) h24, selPred_false_of_lt _ (gRR_mem _) h34]
  rfl

end sibling

/-! ### On the carrier `advanceCarrier` returns -/

/-- **The bridge on the tick carrier, `D ≥ 21`.** If a lawful carrier's
    observer sits at `ε` and its active cores are the sibling pair of `y`,
    advancing it under `axiomSelect` leaves exactly `[yLL]` active. -/
theorem advanceCarrier_active_pos {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) {c : Core} {sL sR : ℕ} {pL pR : Provenance}
    (hMO : X.observer.matrix = 1)
    (hsib : X.archive.filter (fun d => d.id ∈ X.active)
      = [childCore c false sL pL, childCore c true sR pR])
    (hg : Generic (frameEps c))
    (hD : (frameEps c).minus.p * (frameEps c).minus.q + 21
      ≤ (frameEps c).plus.p * (frameEps c).plus.q) :
    (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active
      = [(gcore c false false sL pL s p).id] := by
  show axiomSelect X.observer.matrix s p (proposals X.archive X.active) = _
  rw [hMO]
  exact sibling_step_pos s p hsib hg hD

/-- **The bridge on the tick carrier, `D ≤ −21`.** -/
theorem advanceCarrier_active_neg {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) {c : Core} {sL sR : ℕ} {pL pR : Provenance}
    (hMO : X.observer.matrix = 1)
    (hsib : X.archive.filter (fun d => d.id ∈ X.active)
      = [childCore c false sL pL, childCore c true sR pR])
    (hg : Generic (frameEps c))
    (hD : (frameEps c).plus.p * (frameEps c).plus.q + 21
      ≤ (frameEps c).minus.p * (frameEps c).minus.q) :
    (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active
      = [(gcore c true true sR pR s p).id] := by
  show axiomSelect X.observer.matrix s p (proposals X.archive X.active) = _
  rw [hMO]
  exact sibling_step_neg s p hsib hg hD

/-- **The bridge on the tick carrier, generic sector.** -/
theorem advanceCarrier_active_generic {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) {c : Core} {sL sR : ℕ} {pL pR : Provenance}
    (hMO : X.observer.matrix = 1)
    (hsib : X.archive.filter (fun d => d.id ∈ X.active)
      = [childCore c false sL pL, childCore c true sR pR])
    (hg : Generic (frameEps c)) :
    ∀ i ∈ (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active,
      i = (gcore c false false sL pL s p).id ∨ i = (gcore c true true sR pR s p).id := by
  intro i hi
  have hi' : i ∈ axiomSelect 1 s p (proposals X.archive X.active) := by
    have e : (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active
        = axiomSelect X.observer.matrix s p (proposals X.archive X.active) := rfl
    rw [e, hMO] at hi
    exact hi
  exact sibling_step_generic s p hsib hg i hi'

/-- The observer of Definition 16.4's questions sits at `ε`. -/
theorem observer164_matrix : observer164.matrix = 1 := by decide

end Beat11Bridge
end Two
end RatioSpace
