/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.FiniteRemainder
import RatioSpace.ElementsII.S16.RootChainState
/-!
  Elements II §16, Theorem 16.11, Step 5 — the induction, on the tick carrier.

  What this file builds (2026-09-14, 00:30 work beat).

  * `grand_distinct`: the four grandchild addresses `g₁ … g₄` of any frame are
    pairwise distinct. Contact (`p₁q₀ = q₁p₀ + 1`) is what forbids the two
    coincidences the coefficients allow.
  * `keep_LL` … `keep_RR`: at a sibling step, Definition 8.1's filter
    on each grandchild *core* is `selPred` on its address in `grand F_y`.
  * `sibling_next_cores`: the next active cores after a sibling step, read off
    the next archive (`RootChainCarrier.next_filter_eq_kept`), are the four
    grandchild cores guarded by `selPred`, in order.

  Every theorem `propext`/`Quot.sound` or less.
-/
set_option linter.style.show false

namespace RatioSpace
namespace Two
namespace Step5Beat

open Mat2 Word Frame Pres RatioSpace Advance Accumulation RootOrbit Beat Beat11 Beat11Bridge
  RootChainCarrier Contrast

/-! ## The four grandchild addresses are distinct -/

/-- **`g₁ … g₄` are pairwise distinct, at every frame.** Two coincidences are
    excluded by positivity (`p₊ > 0`, `q₋ > 0`); the other four would force
    `P` and `Q` proportional, which contact forbids: it would read `a = a + 1`. -/
theorem grand_distinct (F : Frame) :
    gLL F ≠ gLR F ∧ gLL F ≠ gRL F ∧ gLL F ≠ gRR F ∧ gLR F ≠ gRL F ∧ gLR F ≠ gRR F ∧
      gRL F ≠ gRR F := by
  have hc : F.plus.p * F.minus.q = F.plus.q * F.minus.p + 1 := F.contact
  have h1 := plus_p_pos F
  have h2 := minus_q_pos F
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hp : 1 * F.plus.p + 3 * F.minus.p = 2 * F.plus.p + 3 * F.minus.p := congrArg IPres.p h
    omega
  · intro h
    have hp : 1 * F.plus.p + 3 * F.minus.p = 3 * F.plus.p + 2 * F.minus.p := congrArg IPres.p h
    have hq : 1 * F.plus.q + 3 * F.minus.q = 3 * F.plus.q + 2 * F.minus.q := congrArg IPres.q h
    rw [show F.minus.p = 2 * F.plus.p by omega, show F.minus.q = 2 * F.plus.q by omega] at hc
    have e : F.plus.p * (2 * F.plus.q) = F.plus.q * (2 * F.plus.p) := by ring
    rw [e] at hc
    exact Nat.succ_ne_self _ hc.symm
  · intro h
    have hp : 1 * F.plus.p + 3 * F.minus.p = 3 * F.plus.p + 1 * F.minus.p := congrArg IPres.p h
    have hq : 1 * F.plus.q + 3 * F.minus.q = 3 * F.plus.q + 1 * F.minus.q := congrArg IPres.q h
    rw [show F.minus.p = F.plus.p by omega, show F.minus.q = F.plus.q by omega] at hc
    have e : F.plus.p * F.plus.q = F.plus.q * F.plus.p := Nat.mul_comm _ _
    rw [e] at hc
    exact Nat.succ_ne_self _ hc.symm
  · intro h
    have hp : 2 * F.plus.p + 3 * F.minus.p = 3 * F.plus.p + 2 * F.minus.p := congrArg IPres.p h
    have hq : 2 * F.plus.q + 3 * F.minus.q = 3 * F.plus.q + 2 * F.minus.q := congrArg IPres.q h
    rw [show F.minus.p = F.plus.p by omega, show F.minus.q = F.plus.q by omega] at hc
    have e : F.plus.p * F.plus.q = F.plus.q * F.plus.p := Nat.mul_comm _ _
    rw [e] at hc
    exact Nat.succ_ne_self _ hc.symm
  · intro h
    have hp : 2 * F.plus.p + 3 * F.minus.p = 3 * F.plus.p + 1 * F.minus.p := congrArg IPres.p h
    have hq : 2 * F.plus.q + 3 * F.minus.q = 3 * F.plus.q + 1 * F.minus.q := congrArg IPres.q h
    rw [show F.plus.p = 2 * F.minus.p by omega, show F.plus.q = 2 * F.minus.q by omega] at hc
    have e : 2 * F.minus.p * F.minus.q = 2 * F.minus.q * F.minus.p := by ring
    rw [e] at hc
    exact Nat.succ_ne_self _ hc.symm
  · intro h
    have hq : 3 * F.plus.q + 2 * F.minus.q = 3 * F.plus.q + 1 * F.minus.q := congrArg IPres.q h
    omega

/-! ## At a sibling step, Definition 8.1 on the cores is `selPred` on the addresses -/

section sibling

variable {archive : List Core} {active : List QuestionId} {c : Core}
  {sL sR : ℕ} {pL pR : Provenance} (s : ℕ) (p : Provenance)

theorem keep_LL (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) :
    keepPred 1 s p (proposals archive active) (gcore c false false sL pL s p)
      = selPred (frameEps c) (gLL (frameEps c)) := by
  unfold keepPred
  rw [addrOf_LL, sibling_admittedFam s p hsib]
  show decide (selPred (frameEps c) (gLL (frameEps c)) = true) = _
  cases selPred (frameEps c) (gLL (frameEps c)) <;> rfl

theorem keep_LR (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) :
    keepPred 1 s p (proposals archive active) (gcore c false true sL pL s p)
      = selPred (frameEps c) (gLR (frameEps c)) := by
  unfold keepPred
  rw [addrOf_LR, sibling_admittedFam s p hsib]
  show decide (selPred (frameEps c) (gLR (frameEps c)) = true) = _
  cases selPred (frameEps c) (gLR (frameEps c)) <;> rfl

theorem keep_RL (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) :
    keepPred 1 s p (proposals archive active) (gcore c true false sR pR s p)
      = selPred (frameEps c) (gRL (frameEps c)) := by
  unfold keepPred
  rw [addrOf_RL, sibling_admittedFam s p hsib]
  show decide (selPred (frameEps c) (gRL (frameEps c)) = true) = _
  cases selPred (frameEps c) (gRL (frameEps c)) <;> rfl

theorem keep_RR (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) :
    keepPred 1 s p (proposals archive active) (gcore c true true sR pR s p)
      = selPred (frameEps c) (gRR (frameEps c)) := by
  unfold keepPred
  rw [addrOf_RR, sibling_admittedFam s p hsib]
  show decide (selPred (frameEps c) (gRR (frameEps c)) = true) = _
  cases selPred (frameEps c) (gRR (frameEps c)) <;> rfl

/-- **The next active cores after a sibling step**, read off the next archive:
    the four grandchild cores, each kept exactly when its address passes
    Definition 8.1 on `grand F_y`. -/
theorem sibling_next_cores (hnd : (archive.map Core.id).Nodup)
    (hwf : ∀ d ∈ archive, d.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) :
    (advanceArchive archive active s p).filter
        (fun d => d.id ∈ axiomSelect 1 s p (proposals archive active))
      = [gcore c false false sL pL s p, gcore c false true sL pL s p,
          gcore c true false sR pR s p, gcore c true true sR pR s p].filter
          (fun g => (keepPred 1 s p (proposals archive active)) g) := by
  rw [next_filter_eq_kept s p hnd hwf hfresh, sibling_proposals hsib]
  rfl

end sibling

/-! ## The shape of every sibling step (Theorem 16.11, clauses 1 and 2) -/

/-- A four-member filter, as four guarded singletons. -/
theorem filter4 {α : Type} (P : α → Bool) (a b c d : α) :
    [a, b, c, d].filter P
      = (bif P a then [a] else []) ++ (bif P b then [b] else []) ++
          (bif P c then [c] else []) ++ (bif P d then [d] else []) := by
  cases ha : P a <;> cases hb : P b <;> cases hc : P c <;> cases hd : P d <;>
    simp only [List.filter, ha, hb, hc, hd, cond_true, cond_false, List.nil_append,
      List.cons_append, List.append_nil]

theorem sel_true {F : Frame} {y : IPres} (h : y ∈ support (grand F)) : selPred F y = true :=
  (List.mem_filter.mp h).2

theorem sel_false {F : Frame} {y : IPres} (hy : y ∈ grand F) (h : y ∉ support (grand F)) :
    selPred F y = false := by
  cases hs : selPred F y
  · rfl
  · exact absurd (List.mem_filter.mpr ⟨hy, hs⟩) h

theorem nm1 {y a : IPres} (h : y ≠ a) : y ∉ [a] := fun hm => h (List.mem_singleton.mp hm)

theorem nm2 {y a b : IPres} (h1 : y ≠ a) (h2 : y ≠ b) : y ∉ [a, b] := fun hm => by
  rcases List.mem_cons.mp hm with h | h
  · exact h1 h
  · exact h2 (List.mem_singleton.mp h)

/-- The active cores one tick on, read off the next archive. -/
def nextCores (archive : List Core) (active : List QuestionId) (s : ℕ) (p : Provenance) :
    List Core :=
  (advanceArchive archive active s p).filter
    (fun d => d.id ∈ axiomSelect 1 s p (proposals archive active))

section shape

variable {archive : List Core} {active : List QuestionId} {c : Core}
  {sL sR : ℕ} {pL pR : Provenance} (s : ℕ) (p : Provenance)

/-- **Theorem 16.11, clause 2 at every sibling step, on the tick carrier.** From
    a sibling pair `[yL, yR]` at observer `ε`, the next active cores are one
    grandchild; or the named pair at `y = ε` (`[LR, RL]`), `y = L` (`[LLL, LRL]`)
    or `y = R` (`[RLR, RRR]`); or the outer pair `[yLL, yRR]`, which happens
    only at `y = RRRL`, `y = LLLR`, and on `RⁿL`, `LⁿR` with `n ≡ 3 (mod 21)`.
    No sibling pair of grandchildren is ever kept. -/
theorem sibling_step_shape (hnd : (archive.map Core.id).Nodup)
    (hwf : ∀ d ∈ archive, d.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) :
    nextCores archive active s p = [gcore c false false sL pL s p] ∨
    nextCores archive active s p = [gcore c false true sL pL s p] ∨
    nextCores archive active s p = [gcore c true false sR pR s p] ∨
    nextCores archive active s p = [gcore c true true sR pR s p] ∨
    (c.seed.word ++ c.relWord = [] ∧
      nextCores archive active s p = [gcore c false true sL pL s p, gcore c true false sR pR s p]) ∨
    (c.seed.word ++ c.relWord = [false] ∧
      nextCores archive active s p = [gcore c false false sL pL s p, gcore c true false sR pR s
        p]) ∨
    (c.seed.word ++ c.relWord = [true] ∧
      nextCores archive active s p = [gcore c false true sL pL s p, gcore c true true sR pR s p]) ∨
    ((c.seed.word ++ c.relWord = [true, true, true, false] ∨
        c.seed.word ++ c.relWord = [false, false, false, true] ∨
        (∃ n, n % 21 = 3 ∧ frameEps c = Step2Family.Frn n) ∨
        (∃ n, n % 21 = 3 ∧ frameEps c = Step2Family.Fm n)) ∧
      nextCores archive active s p = [gcore c false false sL pL s p, gcore c true true sR pR s
        p]) := by
  have hK : nextCores archive active s p
      = (bif selPred (frameEps c) (gLL (frameEps c)) then [gcore c false false sL pL s p] else
        []) ++
        (bif selPred (frameEps c) (gLR (frameEps c)) then [gcore c false true sL pL s p] else []) ++
        (bif selPred (frameEps c) (gRL (frameEps c)) then [gcore c true false sR pR s p] else []) ++
        (bif selPred (frameEps c) (gRR (frameEps c)) then [gcore c true true sR pR s p] else [])
          := by
    unfold nextCores
    rw [sibling_next_cores s p hnd hwf hfresh hsib, filter4, keep_LL s p hsib, keep_LR s p hsib,
      keep_RL s p hsib, keep_RR s p hsib]
  obtain ⟨d12, d13, d14, d23, d24, d34⟩ := grand_distinct (frameEps c)
  have m1 : gLL (frameEps c) ∈ grand (frameEps c) := List.Mem.head _
  have m2 : gLR (frameEps c) ∈ grand (frameEps c) := List.Mem.tail _ (List.Mem.head _)
  have m3 : gRL (frameEps c) ∈ grand (frameEps c) :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have m4 : gRR (frameEps c) ∈ grand (frameEps c) :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hc : Step2Remainder.Complete (c.seed.word ++ c.relWord) (frameEps c) :=
    Step2Remainder.step2_complete (c.seed.word ++ c.relWord)
  rw [hK]
  rcases hc with ho | ⟨n, hn, hF, hs⟩ | ⟨n, hn, hF, hs⟩
  · rcases ho with hs | hs | hs | hs | ⟨hw, hs⟩ | ⟨hw, hs⟩ | ⟨hw, hs⟩ | ⟨hw, hs⟩ | ⟨hw, hs⟩
    · refine Or.inl ?_
      rw [sel_true (by rw [hs]; exact List.Mem.head _),
        sel_false m2 (by rw [hs]; exact nm1 d12.symm),
        sel_false m3 (by rw [hs]; exact nm1 d13.symm),
        sel_false m4 (by rw [hs]; exact nm1 d14.symm)]
      rfl
    · refine Or.inr (Or.inl ?_)
      rw [sel_false m1 (by rw [hs]; exact nm1 d12),
        sel_true (by rw [hs]; exact List.Mem.head _),
        sel_false m3 (by rw [hs]; exact nm1 d23.symm),
        sel_false m4 (by rw [hs]; exact nm1 d24.symm)]
      rfl
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [sel_false m1 (by rw [hs]; exact nm1 d13), sel_false m2 (by rw [hs]; exact nm1 d23),
        sel_true (by rw [hs]; exact List.Mem.head _), sel_false m4 (by rw [hs]; exact nm1 d34.symm)]
      rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      rw [sel_false m1 (by rw [hs]; exact nm1 d14), sel_false m2 (by rw [hs]; exact nm1 d24),
        sel_false m3 (by rw [hs]; exact nm1 d34), sel_true (by rw [hs]; exact List.Mem.head _)]
      rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hw, ?_⟩))))
      rw [sel_false m1 (by rw [hs]; exact nm2 d12 d13),
        sel_true (by rw [hs]; exact List.Mem.head _),
        sel_true (by rw [hs]; exact List.Mem.tail _ (List.Mem.head _)),
        sel_false m4 (by rw [hs]; exact nm2 d24.symm d34.symm)]
      rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hw, ?_⟩)))))
      rw [sel_true (by rw [hs]; exact List.Mem.head _),
        sel_false m2 (by rw [hs]; exact nm2 d12.symm d23),
        sel_true (by rw [hs]; exact List.Mem.tail _ (List.Mem.head _)),
        sel_false m4 (by rw [hs]; exact nm2 d14.symm d34.symm)]
      rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hw, ?_⟩))))))
      rw [sel_false m1 (by rw [hs]; exact nm2 d12 d14),
        sel_true (by rw [hs]; exact List.Mem.head _),
        sel_false m3 (by rw [hs]; exact nm2 d23.symm d34),
        sel_true (by rw [hs]; exact List.Mem.tail _ (List.Mem.head _))]
      rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl hw, ?_⟩))))))
      rw [sel_true (by rw [hs]; exact List.Mem.head _),
        sel_false m2 (by rw [hs]; exact nm2 d12.symm d24),
        sel_false m3 (by rw [hs]; exact nm2 d13.symm d34),
        sel_true (by rw [hs]; exact List.Mem.tail _ (List.Mem.head _))]
      rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inl hw), ?_⟩))))))
      rw [sel_true (by rw [hs]; exact List.Mem.head _),
        sel_false m2 (by rw [hs]; exact nm2 d12.symm d24),
        sel_false m3 (by rw [hs]; exact nm2 d13.symm d34),
        sel_true (by rw [hs]; exact List.Mem.tail _ (List.Mem.head _))]
      rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨Or.inr (Or.inr (Or.inl ⟨n, hn, hF⟩)), ?_⟩))))))
    rw [sel_true (by rw [hs]; exact List.Mem.head _),
      sel_false m2 (by rw [hs]; exact nm2 d12.symm d24),
      sel_false m3 (by rw [hs]; exact nm2 d13.symm d34),
      sel_true (by rw [hs]; exact List.Mem.tail _ (List.Mem.head _))]
    rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨Or.inr (Or.inr (Or.inr ⟨n, hn, hF⟩)), ?_⟩))))))
    rw [sel_true (by rw [hs]; exact List.Mem.head _),
      sel_false m2 (by rw [hs]; exact nm2 d12.symm d24),
      sel_false m3 (by rw [hs]; exact nm2 d13.symm d34),
      sel_true (by rw [hs]; exact List.Mem.tail _ (List.Mem.head _))]
    rfl

/-- **Theorem 16.11, clause 1, at every sibling step.** One or two cores. -/
theorem sibling_step_card (hnd : (archive.map Core.id).Nodup)
    (hwf : ∀ d ∈ archive, d.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hsib : archive.filter (fun d => d.id ∈ active)
      = [childCore c false sL pL, childCore c true sR pR]) :
    (nextCores archive active s p).length = 1 ∨ (nextCores archive active s p).length = 2 := by
  rcases sibling_step_shape s p hnd hwf hfresh hsib with h | h | h | h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
    ⟨_, h⟩ <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

end shape

/-! ## The named pairs carried into Steps 3 and 4 -/

section pairs

variable {x y : Core} {c : Core} {archive : List Core} {active : List QuestionId}
  (s : ℕ) (p : Provenance)

/-- A grandchild's word is its grandparent's word and the two hands. -/
theorem gcore_fullWord (c : Core) (g₁ g₂ : Bool) (s₁ : ℕ) (p₁ : Provenance) :
    fullWord (gcore c g₁ g₂ s₁ p₁ s p) = c.seed.word ++ c.relWord ++ [g₁, g₂] := by
  show fullWord (childCore (childCore c g₁ s₁ p₁) g₂ s p) = _
  rw [child_fullWord, child_fullWord]
  exact (List.append_assoc (c.seed.word ++ c.relWord) [g₁] [g₂]).trans rfl

/-- **A frame names its word** (`walk_inj`): the frame of `RⁿL` is only `RⁿL`'s. -/
theorem family_word_RnL {n : ℕ} (hF : frameEps c = Step2Family.Frn n) :
    c.seed.word ++ c.relWord = List.replicate n true ++ [false] :=
  walk_inj Frame.empty
    (show walk empty (c.seed.word ++ c.relWord) = walk empty (List.replicate n true ++ [false]) from
      hF.trans (Step2Family.walk_RnL n).symm)

theorem family_word_LnR {n : ℕ} (hF : frameEps c = Step2Family.Fm n) :
    c.seed.word ++ c.relWord = List.replicate n false ++ [true] :=
  walk_inj Frame.empty
    (show walk empty (c.seed.word ++ c.relWord) = walk empty (List.replicate n false ++ [true]) from
      hF.trans (Step2Family.walk_LnR n).symm)

/-- **The outer pair on `RⁿL`, `n ≡ 3 (mod 21)`, is Step 3's cousin pair**: its
    words are exactly `Step3Cousin.cousin_step`'s hypotheses at `m = n / 21`. -/
theorem family_pair_words_RnL {n : ℕ} (hn : n % 21 = 3) (hF : frameEps c = Step2Family.Frn n)
    (sL sR : ℕ) (pL pR : Provenance) :
    ∃ m, fullWord (gcore c false false sL pL s p)
        = List.replicate (21 * m + 3) true ++ [false, false, false] ∧
      fullWord (gcore c true true sR pR s p)
        = List.replicate (21 * m + 3) true ++ [false, true, true] := by
  have hw := family_word_RnL hF
  obtain ⟨m, rfl⟩ : ∃ m, n = 21 * m + 3 := ⟨n / 21, by omega⟩
  refine ⟨m, ?_, ?_⟩
  · rw [gcore_fullWord, hw]
    exact (List.append_assoc _ [false] [false, false]).trans rfl
  · rw [gcore_fullWord, hw]
    exact (List.append_assoc _ [false] [true, true]).trans rfl

/-- The mirror: the outer pair on `LⁿR` is `Step3Cousin.mcousin_step`'s pair. -/
theorem family_pair_words_LnR {n : ℕ} (hn : n % 21 = 3) (hF : frameEps c = Step2Family.Fm n)
    (sL sR : ℕ) (pL pR : Provenance) :
    ∃ m, fullWord (gcore c false false sL pL s p)
        = List.replicate (21 * m + 3) false ++ [true, false, false] ∧
      fullWord (gcore c true true sR pR s p)
        = List.replicate (21 * m + 3) false ++ [true, true, true] := by
  have hw := family_word_LnR hF
  obtain ⟨m, rfl⟩ : ∃ m, n = 21 * m + 3 := ⟨n / 21, by omega⟩
  refine ⟨m, ?_, ?_⟩
  · rw [gcore_fullWord, hw]
    exact (List.append_assoc _ [true] [false, false]).trans rfl
  · rw [gcore_fullWord, hw]
    exact (List.append_assoc _ [true] [true, true]).trans rfl

/-- At `ε` the admitted family of any pair is its four children's addresses. -/
theorem pair_admittedFam (hpair : archive.filter (fun d => d.id ∈ active) = [x, y]) :
    admittedFam 1 s p (proposals archive active)
      = [rI (fullWord x ++ [false]), rI (fullWord x ++ [true]),
          rI (fullWord y ++ [false]), rI (fullWord y ++ [true])] := by
  unfold admittedFam
  rw [admittedCores_eps, root_proposals hpair]
  show List.filterMap (addrOf 1)
    [childCore x false s p, childCore x true s p, childCore y false s p, childCore y true s p] = _
  rw [List.filterMap_cons_some (addrOf_child_some s p x false),
    List.filterMap_cons_some (addrOf_child_some s p x true),
    List.filterMap_cons_some (addrOf_child_some s p y false),
    List.filterMap_cons_some (addrOf_child_some s p y true)]
  rfl

/-- Definition 8.1's filter on one child, with its address resolved. -/
theorem keep_child (z : Core) (g : Bool) (props : List (Core × Bool)) :
    keepPred 1 s p props (childCore z g s p)
      = decide ((admittedFam 1 s p props).all (fun u =>
          coherenceOf (admittedFam 1 s p props) u
            ≤ coherenceOf (admittedFam 1 s p props) (rI (fullWord z ++ [g])))) := by
  unfold keepPred
  rw [addrOf_child_some s p z g]

/-- The children of a pair, as `next_filter_eq_kept` lists them. -/
theorem pair_children (hpair : archive.filter (fun d => d.id ∈ active) = [x, y]) :
    (proposals archive active).map (fun q => childCore q.1 q.2 s p)
      = [childCore x false s p, childCore x true s p, childCore y false s p,
          childCore y true s p] := by
  rw [root_proposals hpair]
  rfl

/-- **Step 3 at `L` on the carrier.** From `[LLL, LRL]` at `ε`, the next active
    cores are exactly `[LLLR]`. -/
theorem cousinL_next (hnd : (archive.map Core.id).Nodup) (hwf : ∀ d ∈ archive, d.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hpair : archive.filter (fun d => d.id ∈ active) = [x, y])
    (hx : fullWord x = [false, false, false]) (hy : fullWord y = [false, true, false]) :
    nextCores archive active s p = [childCore x true s p] := by
  have b1 : keepPred 1 s p (proposals archive active) (childCore x false s p) = false := by
    rw [keep_child, pair_admittedFam s p hpair, hx, hy]; decide +kernel
  have b2 : keepPred 1 s p (proposals archive active) (childCore x true s p) = true := by
    rw [keep_child, pair_admittedFam s p hpair, hx, hy]; decide +kernel
  have b3 : keepPred 1 s p (proposals archive active) (childCore y false s p) = false := by
    rw [keep_child, pair_admittedFam s p hpair, hx, hy]; decide +kernel
  have b4 : keepPred 1 s p (proposals archive active) (childCore y true s p) = false := by
    rw [keep_child, pair_admittedFam s p hpair, hx, hy]; decide +kernel
  unfold nextCores
  rw [next_filter_eq_kept s p hnd hwf hfresh, pair_children s p hpair, filter4, b1, b2, b3, b4]
  all_goals rfl

/-- **Step 3 at `R` on the carrier.** From `[RLR, RRR]` at `ε`, the next active
    cores are exactly `[RRRL]`. -/
theorem cousinR_next (hnd : (archive.map Core.id).Nodup) (hwf : ∀ d ∈ archive, d.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hpair : archive.filter (fun d => d.id ∈ active) = [x, y])
    (hx : fullWord x = [true, false, true]) (hy : fullWord y = [true, true, true]) :
    nextCores archive active s p = [childCore y false s p] := by
  have b1 : keepPred 1 s p (proposals archive active) (childCore x false s p) = false := by
    rw [keep_child, pair_admittedFam s p hpair, hx, hy]; decide +kernel
  have b2 : keepPred 1 s p (proposals archive active) (childCore x true s p) = false := by
    rw [keep_child, pair_admittedFam s p hpair, hx, hy]; decide +kernel
  have b3 : keepPred 1 s p (proposals archive active) (childCore y false s p) = true := by
    rw [keep_child, pair_admittedFam s p hpair, hx, hy]; decide +kernel
  have b4 : keepPred 1 s p (proposals archive active) (childCore y true s p) = false := by
    rw [keep_child, pair_admittedFam s p hpair, hx, hy]; decide +kernel
  unfold nextCores
  rw [next_filter_eq_kept s p hnd hwf hfresh, pair_children s p hpair, filter4, b1, b2, b3, b4]
  all_goals rfl

end pairs

end Step5Beat
end Two
end RatioSpace
