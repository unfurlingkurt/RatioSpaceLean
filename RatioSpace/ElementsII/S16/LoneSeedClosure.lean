/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.SupportInduction
/-!
  Elements II §16, Proposition 16.9(ii) (ledger item E2-75).

  **Book statement.** Every lone seed `RⁿL` and `LⁿR`
  with `n ≡ 3 (mod 21)` closes at `h = 7`: its only pair-preserving advance
  before tick 7 is `1 → 2`, because Theorem 16.11's Step 3 resolves the cousin
  pair to a singleton at tick 3 and every later singleton extends `RⁿLLLL`,
  `RⁿLRRR` or their mirrors, which is none of the listed parents `ε`, `L`, `R`,
  `RᵏL`, `LᵏR`.

  **Composition.** Over `Step5Induction.run`/`act`/`npres` (the tick map at
  observer `ε`, from a rooted start, freshness derived by `run_hfresh`, exactly
  as `clause_4`):

  * tick 0 → 1: `single_step`, `single_next_pair` (Corollary 8.11);
  * tick 1 → 2: `Step2Family.sibling_step_RnL_tie` (Step 2's tie), kept pair
    by `pair_next_xLyR`;
  * tick 2 → 3: `Step3Cousin.cousin_step` (Step 3), one core by
    `pair_next_xL`/`pair_next_yR`;
  * ticks 3 → 4, 5 → 6: `single_step` again;
  * ticks 4 → 5, 6 → 7: `Step5Beat.sibling_step_shape`, whose only
    pair-keeping cases are the parents `ε`, `L`, `R`, `RRRL`, `LLLR`, `RᵏL`,
    `LᵏR` (`k ≡ 3 mod 21`). A word `Rⁿ L u` with `u` nonempty and `n ≥ 1` is
    none of them (`ext_ne_RkL`, `ext_ne_LkR`), so the step keeps one core.

  No census, no range: `n` is any natural with `n % 21 = 3`.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_58

open Mat2 Word Frame Pres RatioSpace RatioSpace.Two RatioSpace.Two.Advance
  RatioSpace.Two.Accumulation RatioSpace.Two.RootOrbit RatioSpace.Two.Beat11Bridge
  RatioSpace.Two.RootChainCarrier RatioSpace.Two.Step5Beat RatioSpace.Two.Step5Induction

/-! ## Words: a proper extension of `RⁿL` is no parent that keeps a pair -/

/-- `Rⁿ L u` with `u` nonempty is never `Rᵏ L`. -/
theorem ext_ne_RkL : ∀ (n k : ℕ) (u : List Bool), u ≠ [] →
    List.replicate n true ++ (false :: u) ≠ List.replicate k true ++ [false]
  | 0, 0, u, hu, h => hu (by simpa using h)
  | 0, k + 1, u, _, h => by simp [List.replicate_succ] at h
  | n + 1, 0, u, _, h => by simp [List.replicate_succ] at h
  | n + 1, k + 1, u, hu, h => ext_ne_RkL n k u hu (by simpa [List.replicate_succ] using h)

/-- `Rⁿ L u` with `n ≥ 1` is never `Lᵏ R`. -/
theorem ext_ne_LkR (n k : ℕ) (hn : 1 ≤ n) (u : List Bool) :
    List.replicate n true ++ (false :: u) ≠ List.replicate k false ++ [true] := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  intro h
  cases k with
  | zero =>
    have := congrArg List.length h
    simp at this
    omega
  | succ k => simp [List.replicate_succ] at h

/-- The mirror: `Lⁿ R u` with `u` nonempty is never `Lᵏ R`. -/
theorem mext_ne_LkR : ∀ (n k : ℕ) (u : List Bool), u ≠ [] →
    List.replicate n false ++ (true :: u) ≠ List.replicate k false ++ [true]
  | 0, 0, u, hu, h => hu (by simpa using h)
  | 0, k + 1, u, _, h => by simp [List.replicate_succ] at h
  | n + 1, 0, u, _, h => by simp [List.replicate_succ] at h
  | n + 1, k + 1, u, hu, h => mext_ne_LkR n k u hu (by simpa [List.replicate_succ] using h)

/-- The mirror: `Lⁿ R u` with `n ≥ 1` is never `Rᵏ L`. -/
theorem mext_ne_RkL (n k : ℕ) (hn : 1 ≤ n) (u : List Bool) :
    List.replicate n false ++ (true :: u) ≠ List.replicate k true ++ [false] := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  intro h
  cases k with
  | zero =>
    have := congrArg List.length h
    simp at this
    omega
  | succ k => simp [List.replicate_succ] at h

/-- `w` properly extends `RⁿL`. -/
def ExtR (n : ℕ) (w : Word) : Prop := ∃ u : List Bool, u ≠ [] ∧ w = List.replicate n true ++ (false :: u)

/-- `w` properly extends `LⁿR`. -/
def ExtL (n : ℕ) (w : Word) : Prop := ∃ u : List Bool, u ≠ [] ∧ w = List.replicate n false ++ (true :: u)

/-! ## One tick at a time -/

section tick

variable {archive : List Core} {active : List QuestionId} (s : ℕ) (p : Provenance)

/-- A singleton is followed by its two children (Corollary 8.11), at `ε`. -/
theorem single_next {g : Core} (hg : g.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hL : archive.filter (fun d => d.id ∈ active) = [g]) :
    nextCores archive active s p = [childCore g false s p, childCore g true s p] := by
  unfold nextCores
  rw [single_step s p hL]
  exact single_next_pair s p hg hL hfresh

/-- Two children of one well-formed core have distinct identifiers. -/
theorem sibling_ids_ne {c : Core} (hc : c.WellFormed) (sL sR : ℕ) (pL pR : Provenance) :
    (childCore c false sL pL).id ≠ (childCore c true sR pR).id := by
  intro h
  rw [childCore_id c hc, childCore_id c hc] at h
  exact absurd (child_id_inj h).2 (by decide)

/-- **Step 2 at the sibling pair under `RⁿL`, `n ≡ 3 (mod 21)`**: the outer
    pair `{RⁿLLL, RⁿLRR}` is kept. -/
theorem tie_next_RnL {c : Core} (hc : c.WellFormed) {sL sR : ℕ} {pL pR : Provenance}
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hL : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : fullWord c = List.replicate n true ++ [false]) (hn : n % 21 = 3) :
    nextCores archive active s p = [gcore c false false sL pL s p, gcore c true true sR pR s p] := by
  unfold nextCores
  rw [Step2Family.sibling_step_RnL_tie s p hL n hw hn]
  exact pair_next_xLyR s p (childCore_wellFormed _ _ _ _) (childCore_wellFormed _ _ _ _)
    (sibling_ids_ne hc sL sR pL pR) hL hfresh

/-- The mirror, `LⁿR`. -/
theorem tie_next_LnR {c : Core} (hc : c.WellFormed) {sL sR : ℕ} {pL pR : Provenance}
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hL : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) (n : ℕ)
    (hw : fullWord c = List.replicate n false ++ [true]) (hn : n % 21 = 3) :
    nextCores archive active s p = [gcore c false false sL pL s p, gcore c true true sR pR s p] := by
  unfold nextCores
  rw [Step2Family.sibling_step_LnR_tie s p hL n hw hn]
  exact pair_next_xLyR s p (childCore_wellFormed _ _ _ _) (childCore_wellFormed _ _ _ _)
    (sibling_ids_ne hc sL sR pL pR) hL hfresh

/-- **Step 3 at the cousin pair `{RⁿLLL, RⁿLRR}`**: one core, and its word
    properly extends `RⁿL`. -/
theorem cousin_next_RnL {c : Core} (hc : c.WellFormed) {s₁ : ℕ} {p₁ : Provenance}
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    {n : ℕ} (hw : fullWord c = List.replicate n true ++ [false]) (hn : n % 21 = 3)
    {s₀ : ℕ} {p₀ : Provenance}
    (hL : archive.filter (fun d => d.id ∈ active)
      = [gcore c false false s₀ p₀ s₁ p₁, gcore c true true s₀ p₀ s₁ p₁]) :
    ∃ d, nextCores archive active s p = [d] ∧ d.WellFormed ∧ ExtR n (fullWord d) := by
  have hF : frameEps c = Step2Family.Frn n := by
    change Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
    rw [show c.seed.word ++ c.relWord = fullWord c from rfl, hw, Step2Family.walk_RnL]
  obtain ⟨m, hx, hy⟩ := family_pair_words_RnL s₁ p₁ hn hF s₀ s₀ p₀ p₀
  have hxy := gcore_ne_of_left hc (s₁ := s₀) (s₂ := s₀) (p₁ := p₀) (p₂ := p₀)
    (g₂ := false) (h₂ := true) s₁ p₁
  have hsel := Step3Cousin.cousin_step s p hL hx hy
  cases ho : Step3Cousin.outerR m
  · refine ⟨childCore (gcore c false false s₀ p₀ s₁ p₁) false s p, ?_, childCore_wellFormed _ _ _ _,
      [false, false, false], by simp, ?_⟩
    · unfold nextCores
      rw [hsel, ho]
      exact pair_next_xL s p (childCore_wellFormed _ _ _ _) (childCore_wellFormed _ _ _ _) hxy hL hfresh
    · rw [child_fullWord, gcore_fullWord, show c.seed.word ++ c.relWord = fullWord c from rfl, hw]
      simp
  · refine ⟨childCore (gcore c true true s₀ p₀ s₁ p₁) true s p, ?_, childCore_wellFormed _ _ _ _,
      [true, true, true], by simp, ?_⟩
    · unfold nextCores
      rw [hsel, ho]
      exact pair_next_yR s p (childCore_wellFormed _ _ _ _) (childCore_wellFormed _ _ _ _) hxy hL hfresh
    · rw [child_fullWord, gcore_fullWord, show c.seed.word ++ c.relWord = fullWord c from rfl, hw]
      simp

/-- The mirror: Step 3 at `{LⁿRRR, LⁿRLL}`. -/
theorem cousin_next_LnR {c : Core} (hc : c.WellFormed) {s₁ : ℕ} {p₁ : Provenance}
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    {n : ℕ} (hw : fullWord c = List.replicate n false ++ [true]) (hn : n % 21 = 3)
    {s₀ : ℕ} {p₀ : Provenance}
    (hL : archive.filter (fun d => d.id ∈ active)
      = [gcore c false false s₀ p₀ s₁ p₁, gcore c true true s₀ p₀ s₁ p₁]) :
    ∃ d, nextCores archive active s p = [d] ∧ d.WellFormed ∧ ExtL n (fullWord d) := by
  have hF : frameEps c = Step2Family.Fm n := by
    change Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
    rw [show c.seed.word ++ c.relWord = fullWord c from rfl, hw, Step2Family.walk_LnR]
  obtain ⟨m, hx, hy⟩ := family_pair_words_LnR s₁ p₁ hn hF s₀ s₀ p₀ p₀
  have hxy := gcore_ne_of_left hc (s₁ := s₀) (s₂ := s₀) (p₁ := p₀) (p₂ := p₀)
    (g₂ := false) (h₂ := true) s₁ p₁
  have hsel := Step3Cousin.mcousin_step s p hL hx hy
  cases ho : Step3Cousin.outerR m
  · refine ⟨childCore (gcore c true true s₀ p₀ s₁ p₁) true s p, ?_, childCore_wellFormed _ _ _ _,
      [true, true, true], by simp, ?_⟩
    · unfold nextCores
      rw [hsel, ho]
      exact pair_next_yR s p (childCore_wellFormed _ _ _ _) (childCore_wellFormed _ _ _ _) hxy hL hfresh
    · rw [child_fullWord, gcore_fullWord, show c.seed.word ++ c.relWord = fullWord c from rfl, hw]
      simp
  · refine ⟨childCore (gcore c false false s₀ p₀ s₁ p₁) false s p, ?_, childCore_wellFormed _ _ _ _,
      [false, false, false], by simp, ?_⟩
    · unfold nextCores
      rw [hsel, ho]
      exact pair_next_xL s p (childCore_wellFormed _ _ _ _) (childCore_wellFormed _ _ _ _) hxy hL hfresh
    · rw [child_fullWord, gcore_fullWord, show c.seed.word ++ c.relWord = fullWord c from rfl, hw]
      simp

/-- **A sibling step under a proper extension of `RⁿL` keeps one core**, and
    its word still properly extends `RⁿL`: the parent is none of the words at
    which `sibling_step_shape` keeps a pair. -/
theorem ext_sibling_next_R {c : Core} {sL sR : ℕ} {pL pR : Provenance}
    (hnd : (archive.map Core.id).Nodup) (hwf : ∀ d ∈ archive, d.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hL : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR])
    {n : ℕ} (hn : 1 ≤ n) (hext : ExtR n (fullWord c)) :
    ∃ d, nextCores archive active s p = [d] ∧ d.WellFormed ∧ ExtR n (fullWord d) := by
  obtain ⟨u, hu, hcw⟩ := hext
  have hcw' : c.seed.word ++ c.relWord = List.replicate n true ++ (false :: u) := hcw
  have grow : ∀ a b sa pa, ExtR n (fullWord (gcore c a b sa pa s p)) := by
    intro a b sa pa
    refine ⟨u ++ [a, b], by simp, ?_⟩
    rw [gcore_fullWord, hcw']
    simp
  rcases sibling_step_shape s p hnd hwf hfresh hL with
    h | h | h | h | ⟨hw, _⟩ | ⟨hw, _⟩ | ⟨hw, _⟩ | ⟨hw, _⟩
  · exact ⟨_, h, childCore_wellFormed _ _ _ _, grow _ _ _ _⟩
  · exact ⟨_, h, childCore_wellFormed _ _ _ _, grow _ _ _ _⟩
  · exact ⟨_, h, childCore_wellFormed _ _ _ _, grow _ _ _ _⟩
  · exact ⟨_, h, childCore_wellFormed _ _ _ _, grow _ _ _ _⟩
  · rw [hcw'] at hw
    simp at hw
  · exact absurd (hcw'.symm.trans hw) (ext_ne_RkL n 0 u hu)
  · exact absurd (hcw'.symm.trans hw) (ext_ne_LkR n 0 hn u)
  · rcases hw with hw | hw | ⟨k, _, hF⟩ | ⟨k, _, hF⟩
    · exact absurd (hcw'.symm.trans hw) (ext_ne_RkL n 3 u hu)
    · exact absurd (hcw'.symm.trans hw) (ext_ne_LkR n 3 hn u)
    · exact absurd (hcw'.symm.trans (family_word_RnL hF)) (ext_ne_RkL n k u hu)
    · exact absurd (hcw'.symm.trans (family_word_LnR hF)) (ext_ne_LkR n k hn u)

/-- The mirror: under a proper extension of `LⁿR`. -/
theorem ext_sibling_next_L {c : Core} {sL sR : ℕ} {pL pR : Provenance}
    (hnd : (archive.map Core.id).Nodup) (hwf : ∀ d ∈ archive, d.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hL : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR])
    {n : ℕ} (hn : 1 ≤ n) (hext : ExtL n (fullWord c)) :
    ∃ d, nextCores archive active s p = [d] ∧ d.WellFormed ∧ ExtL n (fullWord d) := by
  obtain ⟨u, hu, hcw⟩ := hext
  have hcw' : c.seed.word ++ c.relWord = List.replicate n false ++ (true :: u) := hcw
  have grow : ∀ a b sa pa, ExtL n (fullWord (gcore c a b sa pa s p)) := by
    intro a b sa pa
    refine ⟨u ++ [a, b], by simp, ?_⟩
    rw [gcore_fullWord, hcw']
    simp
  rcases sibling_step_shape s p hnd hwf hfresh hL with
    h | h | h | h | ⟨hw, _⟩ | ⟨hw, _⟩ | ⟨hw, _⟩ | ⟨hw, _⟩
  · exact ⟨_, h, childCore_wellFormed _ _ _ _, grow _ _ _ _⟩
  · exact ⟨_, h, childCore_wellFormed _ _ _ _, grow _ _ _ _⟩
  · exact ⟨_, h, childCore_wellFormed _ _ _ _, grow _ _ _ _⟩
  · exact ⟨_, h, childCore_wellFormed _ _ _ _, grow _ _ _ _⟩
  · rw [hcw'] at hw
    simp at hw
  · exact absurd (hcw'.symm.trans hw) (mext_ne_RkL n 0 hn u)
  · exact absurd (hcw'.symm.trans hw) (mext_ne_LkR n 0 u hu)
  · rcases hw with hw | hw | ⟨k, _, hF⟩ | ⟨k, _, hF⟩
    · exact absurd (hcw'.symm.trans hw) (mext_ne_RkL n 3 hn u)
    · exact absurd (hcw'.symm.trans hw) (mext_ne_LkR n 3 u hu)
    · exact absurd (hcw'.symm.trans (family_word_RnL hF)) (mext_ne_RkL n k hn u)
    · exact absurd (hcw'.symm.trans (family_word_LnR hF)) (mext_ne_LkR n k u hu)

end tick

/-! ## Along the run -/

section run

variable {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ} {pv : ℕ → Provenance}

/-- The support table and the count of pair-preserving advances determine each
    other through tick seven; the arithmetic, stated once for both sides. -/
theorem table_npres
    (l0 : (act A0 S0 st pv 0).length = 1) (l1 : (act A0 S0 st pv 1).length = 2)
    (l2 : (act A0 S0 st pv 2).length = 2) (l3 : (act A0 S0 st pv 3).length = 1)
    (l4 : (act A0 S0 st pv 4).length = 2) (l5 : (act A0 S0 st pv 5).length = 1)
    (l6 : (act A0 S0 st pv 6).length = 2) (l7 : (act A0 S0 st pv 7).length = 1) :
    npres A0 S0 st pv 7 = 1 ∧
      ∀ j, j < 7 → ((act A0 S0 st pv j).length = 2 ∧ (act A0 S0 st pv (j + 1)).length = 2 ↔ j = 1) := by
  refine ⟨?_, ?_⟩
  · simp only [npres, l0, l1, l2, l3, l4, l5, l6, l7]
    decide
  · intro j hj
    match j, hj with
    | 0, _ => simp [l0, l1]
    | 1, _ => simp [l1, l2]
    | 2, _ => simp [l2, l3]
    | 3, _ => simp [l3, l4]
    | 4, _ => simp [l4, l5]
    | 5, _ => simp [l5, l6]
    | 6, _ => simp [l6, l7]
    | j + 7, hj => exact absurd hj (by omega)

/-- **Proposition 16.9(ii), `RⁿL`.** A lone seed with word `RⁿL`, `n ≡ 3 (mod 21)`, at
    observer `ε`, with fresh identifiers at every tick (Lemma 12.1): the
    support sizes through tick seven are `1, 2, 2, 1, 2, 1, 2, 1`, so it closes
    on an occurrence singleton at `h = 7`; exactly one advance before tick 7
    keeps a pair a pair, and it is `1 → 2`. -/
theorem lone_seed_RnL_closes_at_seven
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0)
    {g : Core} (h0 : A0.filter (fun d => d.id ∈ S0) = [g])
    {n : ℕ} (hw : fullWord g = List.replicate n true ++ [false]) (hn : n % 21 = 3) :
    (act A0 S0 st pv 1).length = 2 ∧ (act A0 S0 st pv 2).length = 2 ∧
    (act A0 S0 st pv 3).length = 1 ∧ (act A0 S0 st pv 4).length = 2 ∧
    (act A0 S0 st pv 5).length = 1 ∧ (act A0 S0 st pv 6).length = 2 ∧
    (act A0 S0 st pv 7).length = 1 ∧ npres A0 S0 st pv 7 = 1 ∧
    ∀ j, j < 7 → ((act A0 S0 st pv j).length = 2 ∧ (act A0 S0 st pv (j + 1)).length = 2 ↔ j = 1) := by
  have hn1 : 1 ≤ n := by omega
  have hg : g.WellFormed :=
    hwf0 g (List.mem_of_mem_filter (by rw [h0]; exact List.Mem.head _))
  have inv := run_inv (S0 := S0) (st := st) (pv := pv) hnd0 hwf0
  have e1 : act A0 S0 st pv 1 = [childCore g false (st 0) (pv 0), childCore g true (st 0) (pv 0)] :=
    single_next (st 0) (pv 0) hg ((run_hfresh (st := st) (pv := pv) hroot) 0) h0
  have e2 : act A0 S0 st pv 2 = [gcore g false false (st 0) (pv 0) (st 1) (pv 1),
      gcore g true true (st 0) (pv 0) (st 1) (pv 1)] :=
    tie_next_RnL (st 1) (pv 1) hg ((run_hfresh (st := st) (pv := pv) hroot) 1) e1 n hw hn
  obtain ⟨d3, e3, hd3, x3⟩ := cousin_next_RnL (st 2) (pv 2) hg ((run_hfresh (st := st) (pv := pv) hroot) 2) hw hn e2
  have e4 : act A0 S0 st pv 4 = [childCore d3 false (st 3) (pv 3), childCore d3 true (st 3) (pv 3)] :=
    single_next (st 3) (pv 3) hd3 ((run_hfresh (st := st) (pv := pv) hroot) 3) e3
  obtain ⟨d5, e5, hd5, x5⟩ :=
    ext_sibling_next_R (st 4) (pv 4) (inv 4).1 (inv 4).2 ((run_hfresh (st := st) (pv := pv) hroot) 4) e4 hn1 x3
  have e6 : act A0 S0 st pv 6 = [childCore d5 false (st 5) (pv 5), childCore d5 true (st 5) (pv 5)] :=
    single_next (st 5) (pv 5) hd5 ((run_hfresh (st := st) (pv := pv) hroot) 5) e5
  obtain ⟨d7, e7, _, _⟩ :=
    ext_sibling_next_R (st 6) (pv 6) (inv 6).1 (inv 6).2 ((run_hfresh (st := st) (pv := pv) hroot) 6) e6 hn1 x5
  have l0 : (act A0 S0 st pv 0).length = 1 := by
    change (A0.filter (fun d => d.id ∈ S0)).length = 1
    rw [h0]; rfl
  have l1 : (act A0 S0 st pv 1).length = 2 := by rw [e1]; rfl
  have l2 : (act A0 S0 st pv 2).length = 2 := by rw [e2]; rfl
  have l3 : (act A0 S0 st pv 3).length = 1 := congrArg List.length e3
  have l4 : (act A0 S0 st pv 4).length = 2 := by rw [e4]; rfl
  have l5 : (act A0 S0 st pv 5).length = 1 := congrArg List.length e5
  have l6 : (act A0 S0 st pv 6).length = 2 := by rw [e6]; rfl
  have l7 : (act A0 S0 st pv 7).length = 1 := congrArg List.length e7
  obtain ⟨hp, hj⟩ := table_npres l0 l1 l2 l3 l4 l5 l6 l7
  exact ⟨l1, l2, l3, l4, l5, l6, l7, hp, hj⟩

/-- **Proposition 16.9(ii), `LⁿR`**, the mirror, proved on its own words rather than by
    mirroring. -/
theorem lone_seed_LnR_closes_at_seven
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0)
    {g : Core} (h0 : A0.filter (fun d => d.id ∈ S0) = [g])
    {n : ℕ} (hw : fullWord g = List.replicate n false ++ [true]) (hn : n % 21 = 3) :
    (act A0 S0 st pv 1).length = 2 ∧ (act A0 S0 st pv 2).length = 2 ∧
    (act A0 S0 st pv 3).length = 1 ∧ (act A0 S0 st pv 4).length = 2 ∧
    (act A0 S0 st pv 5).length = 1 ∧ (act A0 S0 st pv 6).length = 2 ∧
    (act A0 S0 st pv 7).length = 1 ∧ npres A0 S0 st pv 7 = 1 ∧
    ∀ j, j < 7 → ((act A0 S0 st pv j).length = 2 ∧ (act A0 S0 st pv (j + 1)).length = 2 ↔ j = 1) := by
  have hn1 : 1 ≤ n := by omega
  have hg : g.WellFormed :=
    hwf0 g (List.mem_of_mem_filter (by rw [h0]; exact List.Mem.head _))
  have inv := run_inv (S0 := S0) (st := st) (pv := pv) hnd0 hwf0
  have e1 : act A0 S0 st pv 1 = [childCore g false (st 0) (pv 0), childCore g true (st 0) (pv 0)] :=
    single_next (st 0) (pv 0) hg ((run_hfresh (st := st) (pv := pv) hroot) 0) h0
  have e2 : act A0 S0 st pv 2 = [gcore g false false (st 0) (pv 0) (st 1) (pv 1),
      gcore g true true (st 0) (pv 0) (st 1) (pv 1)] :=
    tie_next_LnR (st 1) (pv 1) hg ((run_hfresh (st := st) (pv := pv) hroot) 1) e1 n hw hn
  obtain ⟨d3, e3, hd3, x3⟩ := cousin_next_LnR (st 2) (pv 2) hg ((run_hfresh (st := st) (pv := pv) hroot) 2) hw hn e2
  have e4 : act A0 S0 st pv 4 = [childCore d3 false (st 3) (pv 3), childCore d3 true (st 3) (pv 3)] :=
    single_next (st 3) (pv 3) hd3 ((run_hfresh (st := st) (pv := pv) hroot) 3) e3
  obtain ⟨d5, e5, hd5, x5⟩ :=
    ext_sibling_next_L (st 4) (pv 4) (inv 4).1 (inv 4).2 ((run_hfresh (st := st) (pv := pv) hroot) 4) e4 hn1 x3
  have e6 : act A0 S0 st pv 6 = [childCore d5 false (st 5) (pv 5), childCore d5 true (st 5) (pv 5)] :=
    single_next (st 5) (pv 5) hd5 ((run_hfresh (st := st) (pv := pv) hroot) 5) e5
  obtain ⟨d7, e7, _, _⟩ :=
    ext_sibling_next_L (st 6) (pv 6) (inv 6).1 (inv 6).2 ((run_hfresh (st := st) (pv := pv) hroot) 6) e6 hn1 x5
  have l0 : (act A0 S0 st pv 0).length = 1 := by
    change (A0.filter (fun d => d.id ∈ S0)).length = 1
    rw [h0]; rfl
  have l1 : (act A0 S0 st pv 1).length = 2 := by rw [e1]; rfl
  have l2 : (act A0 S0 st pv 2).length = 2 := by rw [e2]; rfl
  have l3 : (act A0 S0 st pv 3).length = 1 := congrArg List.length e3
  have l4 : (act A0 S0 st pv 4).length = 2 := by rw [e4]; rfl
  have l5 : (act A0 S0 st pv 5).length = 1 := congrArg List.length e5
  have l6 : (act A0 S0 st pv 6).length = 2 := by rw [e6]; rfl
  have l7 : (act A0 S0 st pv 7).length = 1 := congrArg List.length e7
  obtain ⟨hp, hj⟩ := table_npres l0 l1 l2 l3 l4 l5 l6 l7
  exact ⟨l1, l2, l3, l4, l5, l6, l7, hp, hj⟩

end run

#print axioms ext_ne_RkL
#print axioms ext_ne_LkR
#print axioms mext_ne_LkR
#print axioms mext_ne_RkL
#print axioms single_next
#print axioms sibling_ids_ne
#print axioms tie_next_RnL
#print axioms tie_next_LnR
#print axioms cousin_next_RnL
#print axioms cousin_next_LnR
#print axioms ext_sibling_next_R
#print axioms ext_sibling_next_L
#print axioms table_npres
#print axioms lone_seed_RnL_closes_at_seven
#print axioms lone_seed_LnR_closes_at_seven

end G2_58
end Gaps
end RatioSpace
