/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.PrecaptureClassification
/-!
  Elements II §16, Theorem 16.11, clause 2 — root pairs occur only for the
  seed `ε`.

  A seed word is a prefix of every later active word: every next active core is
  a child of a current one (`next_filter_eq_kept`), and a child's word is its
  parent's with one hand appended. A root pair `{LR^k, RL^k}` has words
  beginning with different letters, so no nonempty prefix is common to both.

  Every theorem `propext`/`Quot.sound` or less.
-/
set_option linter.style.show false

namespace RatioSpace
namespace Two
namespace Step5Seed

open Mat2 Word Frame Pres RatioSpace Advance Accumulation RootOrbit Beat Beat11Bridge
  RootChainCarrier Step5Beat Step5Induction

/-- **One tick keeps a common prefix.** -/
theorem prefix_step {archive : List Core} {active : List QuestionId} (s : ℕ) (p : Provenance)
    (hnd : (archive.map Core.id).Nodup) (hwf : ∀ d ∈ archive, d.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (x : Word) (hx : ∀ d ∈ archive.filter (fun d => d.id ∈ active), ∃ t, x ++ t = fullWord d) :
    ∀ d ∈ nextCores archive active s p, ∃ t, x ++ t = fullWord d := by
  intro d hd
  unfold nextCores at hd
  rw [next_filter_eq_kept s p hnd hwf hfresh] at hd
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hd).1
  obtain ⟨c, hc, hqc⟩ := List.mem_flatMap.mp hq
  have hq1 : q.1 = c := by
    rcases List.mem_cons.mp hqc with h | h
    · rw [h]
    · rw [List.mem_singleton.mp h]
  obtain ⟨t, ht⟩ := hx c hc
  refine ⟨t ++ [q.2], ?_⟩
  rw [child_fullWord, hq1, ← ht, List.append_assoc]

/-- **A seed word is a prefix of every active word at every tick.** -/
theorem prefix_run {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ} {pv : ℕ → Provenance}
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0)
    (x : Word) (hx0 : ∀ d ∈ act A0 S0 st pv 0, ∃ t, x ++ t = fullWord d) :
    ∀ j, ∀ d ∈ act A0 S0 st pv j, ∃ t, x ++ t = fullWord d
  | 0 => hx0
  | j + 1 => by
    obtain ⟨hnd, hwf⟩ := run_inv (S0 := S0) (st := st) (pv := pv) hnd0 hwf0 j
    exact prefix_step (st j) (pv j) hnd hwf ((run_hfresh (st := st) (pv := pv) hroot) j) x
      (prefix_run hnd0 hwf0 hroot x hx0 j)

/-- **Theorem 16.11(2): root pairs occur only for the seed `ε`.** If every
    tick-0 active word extends a nonempty word `x` (a lone seed with word `x`),
    no tick's support is a root pair `{LR^k, RL^k}`. -/
theorem no_root_of_seed {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ}
    {pv : ℕ → Provenance}
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0)
    (x : Word) (hne : x ≠ []) (hx0 : ∀ d ∈ act A0 S0 st pv 0, ∃ t, x ++ t = fullWord d)
    (j k : ℕ) (u v : Core) (huv : act A0 S0 st pv j = [u, v])
    (hu : fullWord u = false :: List.replicate k true)
    (hv : fullWord v = true :: List.replicate k false) : False := by
  have hpre := prefix_run hnd0 hwf0 hroot x hx0 j
  obtain ⟨t, ht⟩ := hpre u (by rw [huv]; exact List.Mem.head _)
  obtain ⟨t', ht'⟩ := hpre v (by rw [huv]; exact List.Mem.tail _ (List.Mem.head _))
  cases x with
  | nil => exact hne rfl
  | cons a x' =>
    rw [hu] at ht
    rw [hv] at ht'
    have ha : a = false := (List.cons.inj ht).1
    have ha' : a = true := (List.cons.inj ht').1
    rw [ha] at ha'
    exact Bool.false_ne_true ha'

end Step5Seed
end Two
end RatioSpace
