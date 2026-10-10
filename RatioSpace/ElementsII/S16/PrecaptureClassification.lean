/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.SupportInduction
/-!
  Elements II §16, Theorem 16.11, clause 3 — the pair-preserving advances.

  *"in each of them the two retained occurrences have identical tension
  histograms and distinct keyed signatures."*

  One pattern carries every case: in the admitted family, the second retained
  occurrence's tension row is the first one's row **reversed**, so the
  histograms agree (`List.reverse_perm`); and the two rows differ at the first
  occurrence's own key, where one reads `0` and the other a positive tension,
  so the keyed signatures differ.

  * the root chain, every `k`: rows of `LR^{k+1}`, `RL^{k+1}` in `fam k`, by
    side exchange (`RootChain.t_bd`, `t_cd`); the sibling step at `ε` is its
    `k = 0` member (`grand_empty_eq_fam0`);
  * `RⁿL`, `n ≡ 3 (mod 21)`: rows of `yLL`, `yRR`, by `t₁₂ = t₃₄`, `t₁₃ = t₂₄`;
  * `LⁿR`, the same, through `Step2Family.tm12`–`tm34`;
  * `{LL, LR} → {LLL, LRL}` and its mirror: rows evaluated, and each is a
    half-rotation of the other.

  Every theorem `propext`/`Quot.sound` or less.
-/
set_option linter.style.show false

namespace RatioSpace
namespace Two
namespace Step5Clause3

open Pres Contrast Zphi Beat11

/-- The outer pair of a four-member family: row `d` is row `a` reversed. -/
theorem outer_rows_reverse (a b c d : IPres) (h1 : tEnd a b = tEnd c d)
    (h2 : tEnd a c = tEnd b d) :
    tensions [a, b, c, d] d = (tensions [a, b, c, d] a).reverse := by
  show [tEnd d a, tEnd d b, tEnd d c, tEnd d d] = [tEnd a d, tEnd a c, tEnd a b, tEnd a a]
  rw [tEnd_self d, tEnd_self a, tEnd_comm d a, tEnd_comm d b, tEnd_comm d c, h1, h2]

/-- The inner pair of a four-member family: row `c` is row `b` reversed. -/
theorem inner_rows_reverse (a b c d : IPres) (h1 : tEnd b a = tEnd c d)
    (h2 : tEnd b d = tEnd c a) :
    tensions [a, b, c, d] c = (tensions [a, b, c, d] b).reverse := by
  show [tEnd c a, tEnd c b, tEnd c c, tEnd c d] = [tEnd b d, tEnd b c, tEnd b b, tEnd b a]
  rw [tEnd_self c, tEnd_self b, tEnd_comm c b, h2, h1]

/-- A keyed signature determines its tension row. -/
theorem sig_snd (fam : List IPres) (y : IPres) :
    (tensionSignature fam y).map Prod.snd = tensions fam y := by
  unfold tensionSignature tensions
  rw [List.map_map]
  rfl

theorem sig_ne_of_rows_ne {fam : List IPres} {y y' : IPres}
    (h : tensions fam y ≠ tensions fam y') : tensionSignature fam y ≠ tensionSignature fam y' :=
  fun he => h (by rw [← sig_snd, ← sig_snd, he])

/-! ## The root chain, every `k` -/

/-- **Clause 3 on the root chain.** In `fam k` the retained `LR^{k+1}` and
    `RL^{k+1}` have identical tension histograms and distinct keyed signatures. -/
theorem clause3_root (k : ℕ) :
    (tensions (RootChain.fam k) (RootChain.rb k)).Perm (tensions (RootChain.fam k) (RootChain.rc
      k)) ∧
      tensionSignature (RootChain.fam k) (RootChain.rb k)
        ≠ tensionSignature (RootChain.fam k) (RootChain.rc k) := by
  have hrev : tensions (RootChain.fam k) (RootChain.rc k)
      = (tensions (RootChain.fam k) (RootChain.rb k)).reverse :=
    inner_rows_reverse _ _ _ _
      (by rw [tEnd_comm, ← RootChain.t_cd])
      (by rw [RootChain.t_bd, tEnd_comm])
  refine ⟨by rw [hrev]; exact (List.reverse_perm _).symm, sig_ne_of_rows_ne ?_⟩
  intro h
  have h2 := (List.cons.inj (List.cons.inj h).2).1
  change tEnd (RootChain.rb k) (RootChain.rb k) = tEnd (RootChain.rc k) (RootChain.rb k) at h2
  rw [tEnd_self, tEnd_comm, RootChain.t_bc] at h2
  omega

/-- The sibling step at `ε` compares exactly the root chain's `k = 0` family. -/
theorem grand_empty_eq_fam0 : grand Frame.empty = RootChain.fam 0 := by decide +kernel

/-! ## The tie families -/

/-- **Clause 3 on `RⁿL`, `n ≡ 3 (mod 21)`.** -/
theorem clause3_RnL (n : ℕ) (hn : n % 21 = 3) :
    (tensions (grand (Step2Family.Frn n)) (gLL (Step2Family.Frn n))).Perm
        (tensions (grand (Step2Family.Frn n)) (gRR (Step2Family.Frn n))) ∧
      tensionSignature (grand (Step2Family.Frn n)) (gLL (Step2Family.Frn n))
        ≠ tensionSignature (grand (Step2Family.Frn n)) (gRR (Step2Family.Frn n)) := by
  obtain ⟨e1, e2⟩ := Step2Family.tie_equalities n hn
  have hrev := outer_rows_reverse (gLL (Step2Family.Frn n)) (gLR (Step2Family.Frn n))
    (gRL (Step2Family.Frn n)) (gRR (Step2Family.Frn n)) e1 e2
  refine ⟨by
    show (tensions [_, _, _, _] _).Perm (tensions [_, _, _, _] _)
    rw [hrev]; exact (List.reverse_perm _).symm, sig_ne_of_rows_ne ?_⟩
  intro h
  have h1 := (List.cons.inj h).1
  change tEnd (gLL (Step2Family.Frn n)) (gLL (Step2Family.Frn n))
    = tEnd (gRR (Step2Family.Frn n)) (gLL (Step2Family.Frn n)) at h1
  rw [tEnd_self, tEnd_comm, Step2Family.t14_closed] at h1
  omega

/-- **Clause 3 on `LⁿR`, `n ≡ 3 (mod 21)`**, through the mirror tensions. -/
theorem clause3_LnR (n : ℕ) (hn : n % 21 = 3) :
    (tensions (grand (Step2Family.Fm n)) (gLL (Step2Family.Fm n))).Perm
        (tensions (grand (Step2Family.Fm n)) (gRR (Step2Family.Fm n))) ∧
      tensionSignature (grand (Step2Family.Fm n)) (gLL (Step2Family.Fm n))
        ≠ tensionSignature (grand (Step2Family.Fm n)) (gRR (Step2Family.Fm n)) := by
  obtain ⟨e1, e2⟩ := Step2Family.tie_equalities n hn
  have f1 : tEnd (gLL (Step2Family.Fm n)) (gLR (Step2Family.Fm n))
      = tEnd (gRL (Step2Family.Fm n)) (gRR (Step2Family.Fm n)) := by
    rw [Step2Family.tm12, Step2Family.tm34, e1]
  have f2 : tEnd (gLL (Step2Family.Fm n)) (gRL (Step2Family.Fm n))
      = tEnd (gLR (Step2Family.Fm n)) (gRR (Step2Family.Fm n)) := by
    rw [Step2Family.tm13, Step2Family.tm24, e2]
  have hrev := outer_rows_reverse (gLL (Step2Family.Fm n)) (gLR (Step2Family.Fm n))
    (gRL (Step2Family.Fm n)) (gRR (Step2Family.Fm n)) f1 f2
  refine ⟨by
    show (tensions [_, _, _, _] _).Perm (tensions [_, _, _, _] _)
    rw [hrev]; exact (List.reverse_perm _).symm, sig_ne_of_rows_ne ?_⟩
  intro h
  have h1 := (List.cons.inj h).1
  change tEnd (gLL (Step2Family.Fm n)) (gLL (Step2Family.Fm n))
    = tEnd (gRR (Step2Family.Fm n)) (gLL (Step2Family.Fm n)) at h1
  rw [tEnd_self, tEnd_comm, Step2Family.tm14, Step2Family.t14_closed] at h1
  omega

/-! ## The two fixed configurations -/

/-- The two rows at `y = L`, evaluated. -/
theorem rows_L :
    tensions (grand (Frame.walk Frame.empty [false])) (gLL (Frame.walk Frame.empty [false]))
        = [0, 4, 5, 2] ∧
      tensions (grand (Frame.walk Frame.empty [false])) (gRL (Frame.walk Frame.empty [false]))
        = [5, 2, 0, 4] :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- The two rows at `y = R`, evaluated. -/
theorem rows_R :
    tensions (grand (Frame.walk Frame.empty [true])) (gLR (Frame.walk Frame.empty [true]))
        = [4, 0, 2, 5] ∧
      tensions (grand (Frame.walk Frame.empty [true])) (gRR (Frame.walk Frame.empty [true]))
        = [2, 5, 4, 0] :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **Clause 3 on `{LL, LR} → {LLL, LRL}`.** The two rows are half-rotations of
    each other. Deciding `List.Perm` directly reaches `Classical.choice`; the
    rotation does not. -/
theorem clause3_L :
    (tensions (grand (Frame.walk Frame.empty [false])) (gLL (Frame.walk Frame.empty [false]))).Perm
        (tensions (grand (Frame.walk Frame.empty [false])) (gRL (Frame.walk Frame.empty [false]))) ∧
      tensionSignature (grand (Frame.walk Frame.empty [false])) (gLL (Frame.walk Frame.empty
        [false]))
        ≠ tensionSignature (grand (Frame.walk Frame.empty [false]))
            (gRL (Frame.walk Frame.empty [false])) := by
  obtain ⟨r1, r2⟩ := rows_L
  refine ⟨by rw [r1, r2]; exact List.perm_append_comm (l₁ := [0, 4]) (l₂ := [5, 2]),
    sig_ne_of_rows_ne ?_⟩
  rw [r1, r2]
  intro h
  exact absurd (List.cons.inj h).1 (by decide)

/-- **Clause 3 on the mirror `{RL, RR} → {RLR, RRR}`.** -/
theorem clause3_R :
    (tensions (grand (Frame.walk Frame.empty [true])) (gLR (Frame.walk Frame.empty [true]))).Perm
        (tensions (grand (Frame.walk Frame.empty [true])) (gRR (Frame.walk Frame.empty [true]))) ∧
      tensionSignature (grand (Frame.walk Frame.empty [true])) (gLR (Frame.walk Frame.empty [true]))
        ≠ tensionSignature (grand (Frame.walk Frame.empty [true]))
            (gRR (Frame.walk Frame.empty [true])) := by
  obtain ⟨r1, r2⟩ := rows_R
  refine ⟨by rw [r1, r2]; exact List.perm_append_comm (l₁ := [4, 0]) (l₂ := [2, 5]),
    sig_ne_of_rows_ne ?_⟩
  rw [r1, r2]
  intro h
  exact absurd (List.cons.inj h).1 (by decide)

/-! ## Clause 3 along a run -/

section run

open Mat2 Word Frame RatioSpace Advance Accumulation RootOrbit Beat Beat11Bridge RootChainCarrier
  Step5Beat Step5Induction

theorem len_one_ne_two {u : Core} (h : [u].length = 2) : False := by
  simp only [List.length_cons, List.length_nil] at h
  omega

/-- **Theorem 16.11, clause 3, at one tick.** If a form has two active cores and
    the next tick does too, the two retained cores' addresses have identical
    tension histograms and distinct keyed signatures in the admitted family
    they were compared in. -/
theorem clause3_step {archive : List Core} {active : List QuestionId} (s : ℕ) (p : Provenance)
    (hnd : (archive.map Core.id).Nodup) (hwf : ∀ d ∈ archive, d.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hS : Shape (archive.filter (fun d => d.id ∈ active)))
    (h2 : (archive.filter (fun d => d.id ∈ active)).length = 2)
    (h2' : (nextCores archive active s p).length = 2) :
    ∃ u v : Core, ∃ y y' : IPres, nextCores archive active s p = [u, v] ∧
      addrOf 1 u = some y ∧ addrOf 1 v = some y' ∧
      (tensions (admittedFam 1 s p (proposals archive active)) y).Perm
        (tensions (admittedFam 1 s p (proposals archive active)) y') ∧
      tensionSignature (admittedFam 1 s p (proposals archive active)) y
        ≠ tensionSignature (admittedFam 1 s p (proposals archive active)) y' := by
  generalize hL : archive.filter (fun d => d.id ∈ active) = L at hS h2
  cases hS
  case single g hg => exact absurd h2 len_one_ne_two
  case sibling c sL sR pL pR hc =>
    have hA := sibling_admittedFam s p hL
    rcases sibling_step_shape s p hnd hwf hfresh hL with
      h | h | h | h | ⟨hw, h⟩ | ⟨hw, h⟩ | ⟨hw, h⟩ | ⟨hw, h⟩
    · exact absurd (h ▸ h2') len_one_ne_two
    · exact absurd (h ▸ h2') len_one_ne_two
    · exact absurd (h ▸ h2') len_one_ne_two
    · exact absurd (h ▸ h2') len_one_ne_two
    · have hF : frameEps c = Frame.empty := by
        show Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
        rw [hw]
        rfl
      refine ⟨_, _, _, _, h, addrOf_LR c sL pL s p, addrOf_RL c sR pR s p, ?_⟩
      rw [hA, hF, grand_empty_eq_fam0]
      exact clause3_root 0
    · have hF : frameEps c = Frame.walk Frame.empty [false] := by
        show Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
        rw [hw]
      refine ⟨_, _, _, _, h, addrOf_LL c sL pL s p, addrOf_RL c sR pR s p, ?_⟩
      rw [hA, hF]
      exact clause3_L
    · have hF : frameEps c = Frame.walk Frame.empty [true] := by
        show Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
        rw [hw]
      refine ⟨_, _, _, _, h, addrOf_LR c sL pL s p, addrOf_RR c sR pR s p, ?_⟩
      rw [hA, hF]
      exact clause3_R
    · refine ⟨_, _, _, _, h, addrOf_LL c sL pL s p, addrOf_RR c sR pR s p, ?_⟩
      rw [hA]
      rcases hw with hw | hw | ⟨n, hn, hF⟩ | ⟨n, hn, hF⟩
      · have hF : frameEps c = Step2Family.Frn 3 := by
          show Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
          rw [hw]
          exact Step2Family.walk_RnL 3
        rw [hF]
        exact clause3_RnL 3 rfl
      · have hF : frameEps c = Step2Family.Fm 3 := by
          show Frame.walk Frame.empty (c.seed.word ++ c.relWord) = _
          rw [hw]
          exact Step2Family.walk_LnR 3
        rw [hF]
        exact clause3_LnR 3 rfl
      · rw [hF]
        exact clause3_RnL n hn
      · rw [hF]
        exact clause3_LnR n hn
  case root k x y hx hy hwx hwy hxy =>
    have e : nextCores archive active s p = [childCore x true s p, childCore y false s p] := by
      unfold nextCores
      rw [RootChainCarrier.root_step s p hL hx hy]
      exact root_next_pair s p hwx hwy hxy hL hfresh
    refine ⟨_, _, _, _, e, addr_xR s p hx, addr_yL s p hy, ?_⟩
    rw [root_admittedFam s p hL hx hy]
    exact clause3_root k
  case cousinL x y hx hy _ _ _ =>
    rw [cousinL_next s p hnd hwf hfresh hL hx hy] at h2'
    exact absurd h2' len_one_ne_two
  case cousinR x y hx hy _ _ _ =>
    rw [cousinR_next s p hnd hwf hfresh hL hx hy] at h2'
    exact absurd h2' len_one_ne_two
  case cousin m x y hx hy hwx hwy hxy =>
    have hsel := Step3Cousin.cousin_step s p hL hx hy
    cases ho : Step3Cousin.outerR m
    · have e : nextCores archive active s p = [childCore x false s p] := by
        unfold nextCores
        rw [hsel, ho]
        exact pair_next_xL s p hwx hwy hxy hL hfresh
      exact absurd (e ▸ h2') len_one_ne_two
    · have e : nextCores archive active s p = [childCore y true s p] := by
        unfold nextCores
        rw [hsel, ho]
        exact pair_next_yR s p hwx hwy hxy hL hfresh
      exact absurd (e ▸ h2') len_one_ne_two
  case mcousin m x y hx hy hwx hwy hxy =>
    have hsel := Step3Cousin.mcousin_step s p hL hx hy
    cases ho : Step3Cousin.outerR m
    · have e : nextCores archive active s p = [childCore y true s p] := by
        unfold nextCores
        rw [hsel, ho]
        exact pair_next_yR s p hwx hwy hxy hL hfresh
      exact absurd (e ▸ h2') len_one_ne_two
    · have e : nextCores archive active s p = [childCore x false s p] := by
        unfold nextCores
        rw [hsel, ho]
        exact pair_next_xL s p hwx hwy hxy hL hfresh
      exact absurd (e ▸ h2') len_one_ne_two

/-- **Theorem 16.11, clause 3, along a run.** At every tick where the support
    has two occurrences and so does the next, the two retained occurrences have
    identical tension histograms and distinct keyed signatures in the admitted
    family they were compared in. -/
theorem clause_3 {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ} {pv : ℕ → Provenance}
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hS0 : Shape (A0.filter (fun d => d.id ∈ S0)))
    (hroot : Rooted A0 S0)
    (j : ℕ) (h2 : (act A0 S0 st pv j).length = 2) (h2' : (act A0 S0 st pv (j + 1)).length = 2) :
    ∃ u v : Core, ∃ y y' : IPres, act A0 S0 st pv (j + 1) = [u, v] ∧
      addrOf 1 u = some y ∧ addrOf 1 v = some y' ∧
      (tensions (admittedFam 1 (st j) (pv j) (proposals (run A0 S0 st pv j).1 (run A0 S0 st pv
        j).2))
          y).Perm
        (tensions (admittedFam 1 (st j) (pv j) (proposals (run A0 S0 st pv j).1
          (run A0 S0 st pv j).2)) y') ∧
      tensionSignature (admittedFam 1 (st j) (pv j) (proposals (run A0 S0 st pv j).1
          (run A0 S0 st pv j).2)) y
        ≠ tensionSignature (admittedFam 1 (st j) (pv j) (proposals (run A0 S0 st pv j).1
          (run A0 S0 st pv j).2)) y' := by
  obtain ⟨hnd, hwf⟩ := run_inv (S0 := S0) (st := st) (pv := pv) hnd0 hwf0 j
  exact clause3_step (st j) (pv j) hnd hwf ((run_hfresh (st := st) (pv := pv) hroot) j)
    (clauses_1_2 hnd0 hwf0 hS0 hroot j).1 h2 h2'

/-- **Theorem 16.11, clause 3, the list.** An advance that keeps a pair a pair
    starts from a root pair `{LR^k, RL^k}` (the root chain; the sibling pair at
    `ε` is its `k = 0` member), or from the sibling pair under `L` or `R`
    (`{LL, LR} → {LLL, LRL}` and its mirror), or from the sibling pair under
    `RⁿL` or `LⁿR` with `n ≡ 3 (mod 21)`. Nothing else. -/
theorem clause3_list {archive : List Core} {active : List QuestionId} (s : ℕ) (p : Provenance)
    (hnd : (archive.map Core.id).Nodup) (hwf : ∀ d ∈ archive, d.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hS : Shape (archive.filter (fun d => d.id ∈ active)))
    (h2 : (archive.filter (fun d => d.id ∈ active)).length = 2)
    (h2' : (nextCores archive active s p).length = 2) :
    (∃ k : ℕ, ∃ x y : Core, archive.filter (fun d => d.id ∈ active) = [x, y] ∧
      fullWord x = false :: List.replicate k true ∧ fullWord y = true :: List.replicate k false) ∨
    (∃ c : Core, ∃ sL sR : ℕ, ∃ pL pR : Provenance,
      archive.filter (fun d => d.id ∈ active) = [childCore c false sL pL, childCore c true sR pR] ∧
      (c.seed.word ++ c.relWord = [false] ∨ c.seed.word ++ c.relWord = [true] ∨
        ∃ n, n % 21 = 3 ∧ (c.seed.word ++ c.relWord = List.replicate n true ++ [false] ∨
          c.seed.word ++ c.relWord = List.replicate n false ++ [true]))) := by
  generalize hL : archive.filter (fun d => d.id ∈ active) = L at hS h2
  cases hS
  case single g hg => exact absurd h2 len_one_ne_two
  case sibling c sL sR pL pR hc =>
    rcases sibling_step_shape s p hnd hwf hfresh hL with
      h | h | h | h | ⟨hw, _⟩ | ⟨hw, _⟩ | ⟨hw, _⟩ | ⟨hw, _⟩
    · exact absurd (h ▸ h2') len_one_ne_two
    · exact absurd (h ▸ h2') len_one_ne_two
    · exact absurd (h ▸ h2') len_one_ne_two
    · exact absurd (h ▸ h2') len_one_ne_two
    · refine Or.inl ⟨0, _, _, rfl, ?_, ?_⟩
      · rw [child_fullWord]
        show c.seed.word ++ c.relWord ++ [false] = _
        rw [hw]
        rfl
      · rw [child_fullWord]
        show c.seed.word ++ c.relWord ++ [true] = _
        rw [hw]
        rfl
    · exact Or.inr ⟨c, sL, sR, pL, pR, rfl, Or.inl hw⟩
    · exact Or.inr ⟨c, sL, sR, pL, pR, rfl, Or.inr (Or.inl hw)⟩
    · rcases hw with hw | hw | ⟨n, hn, hF⟩ | ⟨n, hn, hF⟩
      · exact Or.inr ⟨c, sL, sR, pL, pR, rfl, Or.inr (Or.inr ⟨3, rfl, Or.inl hw⟩)⟩
      · exact Or.inr ⟨c, sL, sR, pL, pR, rfl, Or.inr (Or.inr ⟨3, rfl, Or.inr hw⟩)⟩
      · exact Or.inr ⟨c, sL, sR, pL, pR, rfl,
          Or.inr (Or.inr ⟨n, hn, Or.inl (family_word_RnL hF)⟩)⟩
      · exact Or.inr ⟨c, sL, sR, pL, pR, rfl,
          Or.inr (Or.inr ⟨n, hn, Or.inr (family_word_LnR hF)⟩)⟩
  case root k x y hx hy _ _ _ => exact Or.inl ⟨k, x, y, rfl, hx, hy⟩
  case cousinL x y hx hy _ _ _ =>
    rw [cousinL_next s p hnd hwf hfresh hL hx hy] at h2'
    exact absurd h2' len_one_ne_two
  case cousinR x y hx hy _ _ _ =>
    rw [cousinR_next s p hnd hwf hfresh hL hx hy] at h2'
    exact absurd h2' len_one_ne_two
  case cousin m x y hx hy hwx hwy hxy =>
    have hsel := Step3Cousin.cousin_step s p hL hx hy
    cases ho : Step3Cousin.outerR m
    · have e : nextCores archive active s p = [childCore x false s p] := by
        unfold nextCores
        rw [hsel, ho]
        exact pair_next_xL s p hwx hwy hxy hL hfresh
      exact absurd (e ▸ h2') len_one_ne_two
    · have e : nextCores archive active s p = [childCore y true s p] := by
        unfold nextCores
        rw [hsel, ho]
        exact pair_next_yR s p hwx hwy hxy hL hfresh
      exact absurd (e ▸ h2') len_one_ne_two
  case mcousin m x y hx hy hwx hwy hxy =>
    have hsel := Step3Cousin.mcousin_step s p hL hx hy
    cases ho : Step3Cousin.outerR m
    · have e : nextCores archive active s p = [childCore y true s p] := by
        unfold nextCores
        rw [hsel, ho]
        exact pair_next_yR s p hwx hwy hxy hL hfresh
      exact absurd (e ▸ h2') len_one_ne_two
    · have e : nextCores archive active s p = [childCore x false s p] := by
        unfold nextCores
        rw [hsel, ho]
        exact pair_next_xL s p hwx hwy hxy hL hfresh
      exact absurd (e ▸ h2') len_one_ne_two

end run

end Step5Clause3
end Two
end RatioSpace
