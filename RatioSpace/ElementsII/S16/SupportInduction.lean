/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.ParityPattern
import RatioSpace.ElementsII.S16.CousinResolution
/-!
  Elements II §16, Theorem 16.11, Step 5 — the induction, clauses 1 and 2.

  `Shape` lists the forms of clause 2 on the active cores, each carrying the
  words, well-formedness and distinct identifiers the next step needs.
  `shape_step`: one tick of the tick map at observer `ε` sends a `Shape` to a
  `Shape`, using every arrow of the book's Step 5 as built in
  `RootChainCarrier`, `Step3Cousin` and `Step5Beat`. `clauses_1_2`: along any
  run starting from a `Shape` (a lone seed is `Shape.single`), every tick's
  active cores are one of the forms, hence one or two of them.

  Freshness (Lemma 12.1) is derived, not assumed: a run that starts where the
  book's dynamics start (`Rooted`: every archived word no deeper than the
  active ones, which all sit at one depth; a lone seed is depth `0`) keeps that
  shape one level deeper at every tick (`run_depthInv`), and on such a run no
  proposal identifier is already archived (`run_hfresh`). Every theorem
  `propext`/`Quot.sound` or less.
-/
set_option linter.style.show false

namespace RatioSpace
namespace Two
namespace Step5Induction

open Mat2 Word Frame Pres RatioSpace Advance Accumulation RootOrbit Beat Beat11 Beat11Bridge
  RootChainCarrier Contrast Step5Beat

/-- **The forms of Theorem 16.11(2)**, on the active cores. -/
inductive Shape : List Core → Prop
  | single (g : Core) (hwf : g.WellFormed) : Shape [g]
  | sibling (c : Core) (sL sR : ℕ) (pL pR : Provenance) (hwf : c.WellFormed) :
      Shape [childCore c false sL pL, childCore c true sR pR]
  | root (k : ℕ) (x y : Core) (hx : fullWord x = false :: List.replicate k true)
      (hy : fullWord y = true :: List.replicate k false) (hwfx : x.WellFormed)
      (hwfy : y.WellFormed) (hxy : x.id ≠ y.id) : Shape [x, y]
  | cousinL (x y : Core) (hx : fullWord x = [false, false, false])
      (hy : fullWord y = [false, true, false]) (hwfx : x.WellFormed) (hwfy : y.WellFormed)
      (hxy : x.id ≠ y.id) : Shape [x, y]
  | cousinR (x y : Core) (hx : fullWord x = [true, false, true])
      (hy : fullWord y = [true, true, true]) (hwfx : x.WellFormed) (hwfy : y.WellFormed)
      (hxy : x.id ≠ y.id) : Shape [x, y]
  | cousin (m : ℕ) (x y : Core)
      (hx : fullWord x = List.replicate (21 * m + 3) true ++ [false, false, false])
      (hy : fullWord y = List.replicate (21 * m + 3) true ++ [false, true, true])
      (hwfx : x.WellFormed) (hwfy : y.WellFormed) (hxy : x.id ≠ y.id) : Shape [x, y]
  | mcousin (m : ℕ) (x y : Core)
      (hx : fullWord x = List.replicate (21 * m + 3) false ++ [true, false, false])
      (hy : fullWord y = List.replicate (21 * m + 3) false ++ [true, true, true])
      (hwfx : x.WellFormed) (hwfy : y.WellFormed) (hxy : x.id ≠ y.id) : Shape [x, y]

/-- **Clause 1.** Every form has one or two occurrences. -/
theorem shape_card {L : List Core} (h : Shape L) : L.length = 1 ∨ L.length = 2 := by
  cases h
  · exact Or.inl rfl
  all_goals exact Or.inr rfl

/-- Two grandchildren of one well-formed core share an identifier only if they
    share both hands. -/
theorem gcore_id_inj {c : Core} (hc : c.WellFormed) {g₁ g₂ h₁ h₂ : Bool} {s₁ s₂ : ℕ}
    {p₁ p₂ : Provenance} (s : ℕ) (p : Provenance)
    (h : (gcore c g₁ g₂ s₁ p₁ s p).id = (gcore c h₁ h₂ s₂ p₂ s p).id) : g₁ = h₁ ∧ g₂ = h₂ := by
  have e1 := childCore_id (childCore c g₁ s₁ p₁) (childCore_wellFormed _ _ _ _) g₂ s p
  have e2 := childCore_id (childCore c h₁ s₂ p₂) (childCore_wellFormed _ _ _ _) h₂ s p
  unfold gcore at h
  rw [e1, e2, childCore_id c hc, childCore_id c hc] at h
  obtain ⟨h', hg⟩ := child_id_inj h
  exact ⟨(child_id_inj h').2, hg⟩

theorem gcore_ne_of_left {c : Core} (hc : c.WellFormed) {g₂ h₂ : Bool} {s₁ s₂ : ℕ}
    {p₁ p₂ : Provenance} (s : ℕ) (p : Provenance) :
    (gcore c false g₂ s₁ p₁ s p).id ≠ (gcore c true h₂ s₂ p₂ s p).id :=
  fun h => absurd (gcore_id_inj hc s p h).1 (by decide)

/-- **One tick sends a form to a form.** -/
theorem shape_step {archive : List Core} {active : List QuestionId} (s : ℕ) (p : Provenance)
    (hnd : (archive.map Core.id).Nodup) (hwf : ∀ d ∈ archive, d.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hS : Shape (archive.filter (fun d => d.id ∈ active))) :
    Shape (nextCores archive active s p) := by
  generalize hL : archive.filter (fun d => d.id ∈ active) = L at hS
  cases hS with
  | single g hg =>
    have e : nextCores archive active s p = [childCore g false s p, childCore g true s p] := by
      unfold nextCores
      rw [single_step s p hL]
      exact single_next_pair s p hg hL hfresh
    rw [e]
    exact Shape.sibling g s s p p hg
  | sibling c sL sR pL pR hc =>
    rcases sibling_step_shape s p hnd hwf hfresh hL with
      h | h | h | h | ⟨hw, h⟩ | ⟨hw, h⟩ | ⟨hw, h⟩ | ⟨hw, h⟩ <;> rw [h]
    · exact Shape.single _ (childCore_wellFormed _ _ _ _)
    · exact Shape.single _ (childCore_wellFormed _ _ _ _)
    · exact Shape.single _ (childCore_wellFormed _ _ _ _)
    · exact Shape.single _ (childCore_wellFormed _ _ _ _)
    · refine Shape.root 1 _ _ ?_ ?_ (childCore_wellFormed _ _ _ _) (childCore_wellFormed _ _ _ _)
        (gcore_ne_of_left hc s p)
      · rw [gcore_fullWord, hw]; rfl
      · rw [gcore_fullWord, hw]; rfl
    · refine Shape.cousinL _ _ ?_ ?_ (childCore_wellFormed _ _ _ _) (childCore_wellFormed _ _ _ _)
        (gcore_ne_of_left hc s p)
      · rw [gcore_fullWord, hw]; rfl
      · rw [gcore_fullWord, hw]; rfl
    · refine Shape.cousinR _ _ ?_ ?_ (childCore_wellFormed _ _ _ _) (childCore_wellFormed _ _ _ _)
        (gcore_ne_of_left hc s p)
      · rw [gcore_fullWord, hw]; rfl
      · rw [gcore_fullWord, hw]; rfl
    · rcases hw with hw | hw | ⟨n, hn, hF⟩ | ⟨n, hn, hF⟩
      · refine Shape.cousin 0 _ _ ?_ ?_ (childCore_wellFormed _ _ _ _)
          (childCore_wellFormed _ _ _ _) (gcore_ne_of_left hc s p)
        · rw [gcore_fullWord, hw]; rfl
        · rw [gcore_fullWord, hw]; rfl
      · refine Shape.mcousin 0 _ _ ?_ ?_ (childCore_wellFormed _ _ _ _)
          (childCore_wellFormed _ _ _ _) (gcore_ne_of_left hc s p)
        · rw [gcore_fullWord, hw]; rfl
        · rw [gcore_fullWord, hw]; rfl
      · obtain ⟨m, e1, e2⟩ := family_pair_words_RnL s p hn hF sL sR pL pR
        exact Shape.cousin m _ _ e1 e2 (childCore_wellFormed _ _ _ _)
          (childCore_wellFormed _ _ _ _) (gcore_ne_of_left hc s p)
      · obtain ⟨m, e1, e2⟩ := family_pair_words_LnR s p hn hF sL sR pL pR
        exact Shape.mcousin m _ _ e1 e2 (childCore_wellFormed _ _ _ _)
          (childCore_wellFormed _ _ _ _) (gcore_ne_of_left hc s p)
  | root k x y hx hy hwx hwy hxy =>
    have e : nextCores archive active s p = [childCore x true s p, childCore y false s p] := by
      unfold nextCores
      rw [RootChainCarrier.root_step s p hL hx hy]
      exact root_next_pair s p hwx hwy hxy hL hfresh
    obtain ⟨w1, w2⟩ := root_step_words s p hx hy
    rw [e]
    exact Shape.root (k + 1) _ _ w1 w2 (childCore_wellFormed _ _ _ _)
      (childCore_wellFormed _ _ _ _) (four_ids_distinct s p hwx hwy hxy).2.2.2.1
  | cousinL x y hx hy hwx hwy hxy =>
    rw [cousinL_next s p hnd hwf hfresh hL hx hy]
    exact Shape.single _ (childCore_wellFormed _ _ _ _)
  | cousinR x y hx hy hwx hwy hxy =>
    rw [cousinR_next s p hnd hwf hfresh hL hx hy]
    exact Shape.single _ (childCore_wellFormed _ _ _ _)
  | cousin m x y hx hy hwx hwy hxy =>
    have hsel := Step3Cousin.cousin_step s p hL hx hy
    cases ho : Step3Cousin.outerR m
    · have e : nextCores archive active s p = [childCore x false s p] := by
        unfold nextCores
        rw [hsel, ho]
        exact pair_next_xL s p hwx hwy hxy hL hfresh
      rw [e]
      exact Shape.single _ (childCore_wellFormed _ _ _ _)
    · have e : nextCores archive active s p = [childCore y true s p] := by
        unfold nextCores
        rw [hsel, ho]
        exact pair_next_yR s p hwx hwy hxy hL hfresh
      rw [e]
      exact Shape.single _ (childCore_wellFormed _ _ _ _)
  | mcousin m x y hx hy hwx hwy hxy =>
    have hsel := Step3Cousin.mcousin_step s p hL hx hy
    cases ho : Step3Cousin.outerR m
    · have e : nextCores archive active s p = [childCore y true s p] := by
        unfold nextCores
        rw [hsel, ho]
        exact pair_next_yR s p hwx hwy hxy hL hfresh
      rw [e]
      exact Shape.single _ (childCore_wellFormed _ _ _ _)
    · have e : nextCores archive active s p = [childCore x false s p] := by
        unfold nextCores
        rw [hsel, ho]
        exact pair_next_xL s p hwx hwy hxy hL hfresh
      rw [e]
      exact Shape.single _ (childCore_wellFormed _ _ _ _)

/-! ## Every tick -/

/-- **The tick map at observer `ε`, iterated.** Archive and active support at
    every tick; the stratum and provenance each tick writes are supplied. These
    are exactly `advanceCarrier`'s `archive` and `active` fields under
    `axiomSelect`. -/
def run (A0 : List Core) (S0 : List QuestionId) (st : ℕ → ℕ) (pv : ℕ → Provenance) :
    ℕ → List Core × List QuestionId
  | 0 => (A0, S0)
  | j + 1 =>
    ((advanceArchive (run A0 S0 st pv j).1 (run A0 S0 st pv j).2 (st j) (pv j)),
      axiomSelect 1 (st j) (pv j) (proposals (run A0 S0 st pv j).1 (run A0 S0 st pv j).2))

/-- The archive stays duplicate-free and well-formed along the run. -/
theorem run_inv {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ} {pv : ℕ → Provenance}
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed) :
    ∀ j, ((run A0 S0 st pv j).1.map Core.id).Nodup ∧ ∀ d ∈ (run A0 S0 st pv j).1, d.WellFormed
  | 0 => ⟨hnd0, hwf0⟩
  | j + 1 => by
    obtain ⟨hnd, hwf⟩ := run_inv hnd0 hwf0 j
    exact ⟨advanceArchive_nodup hnd hwf, advanceArchive_wellFormed hwf⟩

/-- **Where a run can start.** The archive and support of a carrier the book's
    dynamics reach: some depth `ℓ` with every archived core well-formed and no
    deeper than `ℓ`, and every active identifier exactly at `ℓ` (Lemma 12.1's
    invariant, `Gaps.G2_13.DepthInv`). A lone seed is `ℓ = 0`
    (`rooted_of_seeds`); every tick of a run from a rooted start is rooted
    again (`run_depthInv`). -/
def Rooted (A0 : List Core) (S0 : List QuestionId) : Prop :=
  ∃ ℓ, Gaps.G2_13.DepthInv A0 S0 ℓ

/-- A seed archive (well-formed cores with empty relative words) with support
    drawn from it is rooted. -/
theorem rooted_of_seeds {A0 : List Core} {S0 : List QuestionId}
    (hwf0 : ∀ d ∈ A0, d.WellFormed) (hseed : ∀ d ∈ A0, d.relWord = [])
    (hsub : ∀ i ∈ S0, i ∈ archIds A0) : Rooted A0 S0 :=
  ⟨0, Gaps.G2_13.depthInv_of_seeds hwf0 hseed hsub⟩

/-- **Lemma 12.1's invariant along the run**, one level deeper per tick. -/
theorem run_depthInv {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ}
    {pv : ℕ → Provenance} {ℓ : ℕ} (h0 : Gaps.G2_13.DepthInv A0 S0 ℓ) :
    ∀ j, Gaps.G2_13.DepthInv (run A0 S0 st pv j).1 (run A0 S0 st pv j).2 (ℓ + j)
  | 0 => h0
  | j + 1 =>
    Gaps.G2_13.depthInv_step (run_depthInv h0 j) (st j) (pv j) _
      (axiomSelect_hsel 1 (st j) (pv j) _)

/-- **Lemma 12.1 at every tick of a rooted run**: freshness is a theorem about
    the run, not a hypothesis on it. -/
theorem run_hfresh {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ}
    {pv : ℕ → Provenance} (hroot : Rooted A0 S0) :
    ∀ j, ∀ q ∈ proposals (run A0 S0 st pv j).1 (run A0 S0 st pv j).2,
      (childCore q.1 q.2 (st j) (pv j)).id ∉ archIds (run A0 S0 st pv j).1 := by
  obtain ⟨ℓ, h0⟩ := hroot
  intro j
  exact Gaps.G2_13.hfresh_of_depthInv (run_depthInv h0 j) (st j) (pv j)

/-- **Every tick of a rooted run is itself a rooted start**, so a second run
    begun from the state some run reached (as Theorem 16.12 reads it) is
    covered. -/
theorem rooted_run {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ}
    {pv : ℕ → Provenance} (hroot : Rooted A0 S0) (j : ℕ) :
    Rooted (run A0 S0 st pv j).1 (run A0 S0 st pv j).2 := by
  obtain ⟨ℓ, h0⟩ := hroot
  exact ⟨ℓ + j, run_depthInv h0 j⟩

/-- **A valid tick-zero carrier is a rooted start**, at depth `0`. -/
theorem rooted_of_seeded {Aux : Type} {h : ℕ} {X : TickCarrier Aux h} (hX : Seeded X) :
    Rooted X.archive X.active := by
  refine ⟨0, ?_⟩
  have e := hX.1
  have ht := hX.2.2
  unfold Gaps.G2_13.TickLengthInv at ht
  rw [e] at ht
  exact ht

/-- **Theorem 16.11, clauses 1 and 2, at every tick.** Along any run at
    observer `ε` starting from one of the forms (a lone seed is
    `Shape.single`) where the book's dynamics can start (`Rooted`; freshness,
    Lemma 12.1, is then `run_hfresh`), every
    tick's active cores are a singleton, a sibling pair, a root pair
    `{LR^k, RL^k}`, or one of the cousin pairs `{LLL, LRL}`, `{RLR, RRR}`,
    `{RⁿLLL, RⁿLRR}`, `{LⁿRRR, LⁿRLL}` with `n ≡ 3 (mod 21)`; so one or two. -/
theorem clauses_1_2 {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ} {pv : ℕ → Provenance}
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hS0 : Shape (A0.filter (fun d => d.id ∈ S0)))
    (hroot : Rooted A0 S0) :
    ∀ j, Shape ((run A0 S0 st pv j).1.filter (fun d => d.id ∈ (run A0 S0 st pv j).2)) ∧
      (((run A0 S0 st pv j).1.filter (fun d => d.id ∈ (run A0 S0 st pv j).2)).length = 1 ∨
        ((run A0 S0 st pv j).1.filter (fun d => d.id ∈ (run A0 S0 st pv j).2)).length = 2) := by
  intro j
  have hS : Shape ((run A0 S0 st pv j).1.filter (fun d => d.id ∈ (run A0 S0 st pv j).2)) := by
    induction j with
    | zero => exact hS0
    | succ k ih =>
      obtain ⟨hnd, hwf⟩ := run_inv (S0 := S0) (st := st) (pv := pv) hnd0 hwf0 k
      exact shape_step (st k) (pv k) hnd hwf ((run_hfresh (st := st) (pv := pv) hroot) k) ih
  exact ⟨hS, shape_card hS⟩

/-! ## Clause 4: the singleton beat -/

/-- A singleton is always followed by exactly two cores (Corollary 8.11). -/
theorem single_next_len {archive : List Core} {active : List QuestionId} (s : ℕ) (p : Provenance)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hS : Shape (archive.filter (fun d => d.id ∈ active)))
    (h1 : (archive.filter (fun d => d.id ∈ active)).length = 1) :
    (nextCores archive active s p).length = 2 := by
  generalize hL : archive.filter (fun d => d.id ∈ active) = L at hS h1
  cases hS
  case single g hg =>
    have e : nextCores archive active s p = [childCore g false s p, childCore g true s p] := by
      unfold nextCores
      rw [single_step s p hL]
      exact single_next_pair s p hg hL hfresh
    rw [e]
    rfl
  all_goals (simp only [List.length_cons, List.length_nil] at h1; omega)

/-- The active cores at tick `j` of a run. -/
def act (A0 : List Core) (S0 : List QuestionId) (st : ℕ → ℕ) (pv : ℕ → Provenance) (j : ℕ) :
    List Core :=
  (run A0 S0 st pv j).1.filter (fun d => d.id ∈ (run A0 S0 st pv j).2)

/-- `n_j`: the number of advances before tick `j` that keep a pair a pair. -/
def npres (A0 : List Core) (S0 : List QuestionId) (st : ℕ → ℕ) (pv : ℕ → Provenance) : ℕ → ℕ
  | 0 => 0
  | j + 1 => npres A0 S0 st pv j +
      if (act A0 S0 st pv j).length = 2 ∧ (act A0 S0 st pv (j + 1)).length = 2 then 1 else 0

/-- **Theorem 16.11, clause 4.** From a lone seed, `|S_j| = 1` exactly when
    `j ≡ n_j (mod 2)`. Clause 1 and "a singleton is followed by a pair" force
    it: the beat is arithmetic once the support never leaves `{1, 2}`. -/
theorem clause_4 {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ} {pv : ℕ → Provenance}
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hS0 : Shape (A0.filter (fun d => d.id ∈ S0)))
    (hroot : Rooted A0 S0)
    (h0 : (A0.filter (fun d => d.id ∈ S0)).length = 1) :
    ∀ j, ((act A0 S0 st pv j).length = 1 ↔ j % 2 = npres A0 S0 st pv j % 2) := by
  intro j
  induction j with
  | zero => exact ⟨fun _ => rfl, fun _ => h0⟩
  | succ k ih =>
    have ck : (act A0 S0 st pv k).length = 1 ∨ (act A0 S0 st pv k).length = 2 :=
      (clauses_1_2 hnd0 hwf0 hS0 hroot k).2
    have ck1 : (act A0 S0 st pv (k + 1)).length = 1 ∨ (act A0 S0 st pv (k + 1)).length = 2 :=
      (clauses_1_2 hnd0 hwf0 hS0 hroot (k + 1)).2
    have hsn : (act A0 S0 st pv k).length = 1 → (act A0 S0 st pv (k + 1)).length = 2 := by
      intro h1
      obtain ⟨hnd, hwf⟩ := run_inv (S0 := S0) (st := st) (pv := pv) hnd0 hwf0 k
      exact single_next_len (st k) (pv k) ((run_hfresh (st := st) (pv := pv) hroot) k)
        (clauses_1_2 hnd0 hwf0 hS0 hroot k).1 h1
    show _ ↔ (k + 1) % 2 = (npres A0 S0 st pv k +
      if (act A0 S0 st pv k).length = 2 ∧ (act A0 S0 st pv (k + 1)).length = 2 then 1 else 0) % 2
    rcases ck with hk | hk <;> rcases ck1 with hk1 | hk1
    · exact absurd (hsn hk) (by rw [hk1]; decide)
    · rw [if_neg (fun h => by omega)]
      have e := ih.mp hk
      constructor
      · intro h; omega
      · intro h; omega
    · rw [if_neg (fun h => by omega)]
      have e : ¬ (k % 2 = npres A0 S0 st pv k % 2) := fun h => by have := ih.mpr h; omega
      exact ⟨fun _ => by omega, fun _ => hk1⟩
    · rw [if_pos ⟨hk, hk1⟩]
      have e : ¬ (k % 2 = npres A0 S0 st pv k % 2) := fun h => by have := ih.mpr h; omega
      constructor
      · intro h; omega
      · intro h; omega

#print axioms run_depthInv
#print axioms run_hfresh
#print axioms rooted_of_seeds
#print axioms rooted_run
#print axioms rooted_of_seeded

end Step5Induction
end Two
end RatioSpace
