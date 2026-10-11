/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.LoneSeedClosure
import RatioSpace.ElementsII.S16.CrystallizationPattern
/-!
  Elements II §16, Theorem 16.5 and Proposition 16.9(ii): the polarized
  questions `𝒬_L` and `𝒬_R` close on an occurrence singleton at the horizon
  `3` and at every even horizon `h ≥ 6`, with no range.

  **Book statement (v0.25 text of the round-2 revision of Theorem 16.5).** The
  polarized questions close on an occurrence singleton at the horizon `3` and
  at every even horizon `h ≥ 6`: `𝒬_L` closes at `h = 6` on `LLLRRRR`
  (`5:16`) and at `h = 8` on `LLLRRRRRR` (`7:22`); `𝒬_R` closes on the side
  mirrors.

  **Composition.** The tick map at observer `ε` from the seed `L` (resp. `R`)
  is `Step5Induction.run`, with stratum `j + 1` at tick `j` and the seed
  provenance (`polAct`). Ticks `0` through `6` are the seven concrete
  carriers `XL0 … XL6` (`polAct_words_L`, by `rfl`: `run` unfolds to the same
  `advanceArchive` and `axiomSelect` terms that `advanceCarrier` stores), so
  their support sizes are `RootOrbit.theorem_16_5_polarized_L`. From tick `6`
  on, the support is a singleton whose word properly extends `LLL` followed by
  `R` (`ExtL 3`): `G2_58.single_next` gives its sibling pair at tick `7`, and
  `G2_58.ext_sibling_next_L` (a proper extension of `LⁿR` is none of the
  parents at which `Step5Beat.sibling_step_shape` keeps a pair) gives a new
  singleton, again in `ExtL 3`. So the support alternates singleton, pair from
  tick `6` on: singletons exactly at `6, 8, 10, …`.

  The horizon enters only through the type of the carrier: `Beat.horizon_inert`
  and `polAct_words_YL8` record that the run agrees with the carriers built at
  declared horizon `8`.
-/

set_option linter.style.show false

namespace RatioSpace
namespace Gaps
namespace T16_5_polarized

open Mat2 Word Frame Pres RatioSpace RatioSpace.Two RatioSpace.Two.Advance
  RatioSpace.Two.Accumulation RatioSpace.Two.RootOrbit RatioSpace.Two.Beat11Bridge
  RatioSpace.Two.RootChainCarrier RatioSpace.Two.Step5Beat RatioSpace.Two.Step5Induction
  RatioSpace.Gaps.G2_58

/-! ## The run of the polarized question -/

/-- **The active cores at tick `j` of the question with seed word `w`**, from
    the tick-zero carrier `X0 w`: `Step5Induction.act` with the stratum `j + 1`
    and the seed provenance at tick `j`, exactly the schedule of
    `RootOrbit`'s concrete carriers. `polAct [false]` is `𝒬_L`, `polAct [true]`
    is `𝒬_R`. -/
def polAct (w : Word) (j : ℕ) : List Core :=
  act (X0 w).archive (X0 w).active (fun k => k + 1) (fun _ => seed164Prov) j

/-- The tick-zero start of a lone seed is a valid start of the run. -/
theorem polStart_wf (w : Word) :
    ((X0 w).archive.map Core.id).Nodup ∧ (∀ d ∈ (X0 w).archive, d.WellFormed) ∧
    Rooted (X0 w).archive (X0 w).active := by
  refine ⟨by simp [X0], ?_, ?_⟩
  · intro d hd
    have hd' : d = seedCore seed164Id ⟨Frame.empty, w⟩ 0 seed164Prov := by
      simpa [X0] using hd
    rw [hd']
    exact seedCore_wellFormed _ _ _ _
  · refine rooted_of_seeds ?_ ?_ ?_
    · intro d hd
      have hd' : d = seedCore seed164Id ⟨Frame.empty, w⟩ 0 seed164Prov := by
        simpa [X0] using hd
      rw [hd']
      exact seedCore_wellFormed _ _ _ _
    · intro d hd
      have hd' : d = seedCore seed164Id ⟨Frame.empty, w⟩ 0 seed164Prov := by
        simpa [X0] using hd
      rw [hd']
      rfl
    · intro i hi
      simp only [X0, List.mem_singleton] at hi
      subst hi
      simp only [archIds, X0, List.map_cons, List.map_nil, List.mem_singleton]
      rfl

/-! ## The first six ticks are the concrete carriers -/

/-- **Ticks 1 through 7 of the run from `L` are the carriers `XL1 … XL7`.** -/
theorem polAct_words_L :
    (polAct [false] 1).map fullWord = activeWords XL1 ∧
    (polAct [false] 2).map fullWord = activeWords XL2 ∧
    (polAct [false] 3).map fullWord = activeWords XL3 ∧
    (polAct [false] 4).map fullWord = activeWords XL4 ∧
    (polAct [false] 5).map fullWord = activeWords XL5 ∧
    (polAct [false] 6).map fullWord = activeWords XL6 ∧
    (polAct [false] 7).map fullWord = activeWords XL7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Ticks 1 through 7 of the run from `R` are the carriers `XR1 … XR7`.** -/
theorem polAct_words_R :
    (polAct [true] 1).map fullWord = activeWords XR1 ∧
    (polAct [true] 2).map fullWord = activeWords XR2 ∧
    (polAct [true] 3).map fullWord = activeWords XR3 ∧
    (polAct [true] 4).map fullWord = activeWords XR4 ∧
    (polAct [true] 5).map fullWord = activeWords XR5 ∧
    (polAct [true] 6).map fullWord = activeWords XR6 ∧
    (polAct [true] 7).map fullWord = activeWords XR7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The run from `L` agrees with the carriers built at declared horizon `8`
    (`Beat.YL6 … YL8`), so the horizon is inert. -/
theorem polAct_words_YL8 :
    (polAct [false] 6).map fullWord = activeWords Beat.YL6 ∧
    (polAct [false] 7).map fullWord = activeWords Beat.YL7 ∧
    (polAct [false] 8).map fullWord = activeWords Beat.YL8 :=
  ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The run from `R` agrees with the carriers built at declared horizon `8`. -/
theorem polAct_words_YR8 :
    (polAct [true] 6).map fullWord = activeWords Beat.YR6 ∧
    (polAct [true] 7).map fullWord = activeWords Beat.YR7 ∧
    (polAct [true] 8).map fullWord = activeWords Beat.YR8 :=
  ⟨rfl, rfl, rfl⟩

/-! ## From tick 6 on: singleton, pair, singleton, pair -/

section tail

variable {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ} {pv : ℕ → Provenance}

/-- **The tail on the `L` side.** If tick 6 is a singleton `{d}` whose word
    properly extends `LLLR` (`ExtL 3`), then at every `i` tick `6 + 2 i` is a
    singleton with a word that properly extends `LLLR` and tick `7 + 2 i` is a
    sibling pair. Nothing is assumed about the schedule `st`, `pv` beyond the
    start being a valid one. -/
theorem tail_L (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0) {d : Core} (h6 : act A0 S0 st pv 6 = [d]) (hd : d.WellFormed)
    (hx : ExtL 3 (fullWord d)) :
    ∀ i, ∃ e, act A0 S0 st pv (6 + 2 * i) = [e] ∧ e.WellFormed ∧ ExtL 3 (fullWord e) ∧
      (act A0 S0 st pv (6 + 2 * i + 1)).length = 2
  | 0 => ⟨d, h6, hd, hx, by
      rw [show (act A0 S0 st pv (6 + 2 * 0 + 1)) = _ from single_next (st 6) (pv 6) hd
        ((run_hfresh (st := st) (pv := pv) hroot) 6) h6]
      rfl⟩
  | i + 1 => by
    obtain ⟨e, he, hwe, hxe, _⟩ := tail_L hnd0 hwf0 hroot h6 hd hx i
    have inv := run_inv (S0 := S0) (st := st) (pv := pv) hnd0 hwf0
    have e1 : act A0 S0 st pv (6 + 2 * i + 1) =
        [childCore e false (st (6 + 2 * i)) (pv (6 + 2 * i)),
         childCore e true (st (6 + 2 * i)) (pv (6 + 2 * i))] :=
      single_next (st (6 + 2 * i)) (pv (6 + 2 * i)) hwe
        ((run_hfresh (st := st) (pv := pv) hroot) (6 + 2 * i)) he
    obtain ⟨d', e2, hd', x2⟩ :=
      ext_sibling_next_L (st (6 + 2 * i + 1)) (pv (6 + 2 * i + 1))
        (inv (6 + 2 * i + 1)).1 (inv (6 + 2 * i + 1)).2
        ((run_hfresh (st := st) (pv := pv) hroot) (6 + 2 * i + 1)) e1 (by omega) hxe
    have e3 : act A0 S0 st pv (6 + 2 * (i + 1)) = [d'] := e2
    refine ⟨d', e3, hd', x2, ?_⟩
    rw [show (act A0 S0 st pv (6 + 2 * (i + 1) + 1)) = _ from single_next (st (6 + 2 * (i + 1)))
      (pv (6 + 2 * (i + 1))) hd' ((run_hfresh (st := st) (pv := pv) hroot) (6 + 2 * (i + 1))) e3]
    rfl

/-- **The tail on the `R` side**, on its own words (`ExtR 3`). -/
theorem tail_R (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0) {d : Core} (h6 : act A0 S0 st pv 6 = [d]) (hd : d.WellFormed)
    (hx : ExtR 3 (fullWord d)) :
    ∀ i, ∃ e, act A0 S0 st pv (6 + 2 * i) = [e] ∧ e.WellFormed ∧ ExtR 3 (fullWord e) ∧
      (act A0 S0 st pv (6 + 2 * i + 1)).length = 2
  | 0 => ⟨d, h6, hd, hx, by
      rw [show (act A0 S0 st pv (6 + 2 * 0 + 1)) = _ from single_next (st 6) (pv 6) hd
        ((run_hfresh (st := st) (pv := pv) hroot) 6) h6]
      rfl⟩
  | i + 1 => by
    obtain ⟨e, he, hwe, hxe, _⟩ := tail_R hnd0 hwf0 hroot h6 hd hx i
    have inv := run_inv (S0 := S0) (st := st) (pv := pv) hnd0 hwf0
    have e1 : act A0 S0 st pv (6 + 2 * i + 1) =
        [childCore e false (st (6 + 2 * i)) (pv (6 + 2 * i)),
         childCore e true (st (6 + 2 * i)) (pv (6 + 2 * i))] :=
      single_next (st (6 + 2 * i)) (pv (6 + 2 * i)) hwe
        ((run_hfresh (st := st) (pv := pv) hroot) (6 + 2 * i)) he
    obtain ⟨d', e2, hd', x2⟩ :=
      ext_sibling_next_R (st (6 + 2 * i + 1)) (pv (6 + 2 * i + 1))
        (inv (6 + 2 * i + 1)).1 (inv (6 + 2 * i + 1)).2
        ((run_hfresh (st := st) (pv := pv) hroot) (6 + 2 * i + 1)) e1 (by omega) hxe
    have e3 : act A0 S0 st pv (6 + 2 * (i + 1)) = [d'] := e2
    refine ⟨d', e3, hd', x2, ?_⟩
    rw [show (act A0 S0 st pv (6 + 2 * (i + 1) + 1)) = _ from single_next (st (6 + 2 * (i + 1)))
      (pv (6 + 2 * (i + 1))) hd' ((run_hfresh (st := st) (pv := pv) hroot) (6 + 2 * (i + 1))) e3]
    rfl

end tail

/-- A list whose word map is a singleton is a singleton. -/
theorem single_of_words {l : List Core} {w : Word} (h : l.map fullWord = [w]) :
    ∃ d, l = [d] ∧ fullWord d = w := by
  match l, h with
  | [d], h => exact ⟨d, rfl, by simpa using h⟩

/-! ## The theorem -/

/-- **Theorem 16.5, the polarized question `𝒬_L`, at every horizon.** The
    occurrence support of `𝒬_L` at horizon `h ≥ 1` has one member when `h = 3`
    or `h` is even and at least `6`, and two members otherwise. No range: the
    tail from tick `6` is `tail_L`. -/
theorem polarized_L_support_card (h : ℕ) (h1 : 1 ≤ h) :
    (polAct [false] h).length = if (h = 3 ∨ (6 ≤ h ∧ h % 2 = 0)) then 1 else 2 := by
  obtain ⟨hnd0, hwf0, hroot⟩ := polStart_wf [false]
  obtain ⟨c1, c2, c3, c4, c5, c6, _⟩ := polAct_words_L
  obtain ⟨t1, t2, t3, t4, t5, t6, _⟩ := theorem_16_5_polarized_L
  have l1 : (polAct [false] 1).length = 2 := by simpa using congrArg List.length (c1.trans t1)
  have l2 : (polAct [false] 2).length = 2 := by simpa using congrArg List.length (c2.trans t2)
  have l3 : (polAct [false] 3).length = 1 := by simpa using congrArg List.length (c3.trans t3)
  have l4 : (polAct [false] 4).length = 2 := by simpa using congrArg List.length (c4.trans t4)
  have l5 : (polAct [false] 5).length = 2 := by simpa using congrArg List.length (c5.trans t5)
  by_cases hh : h ≤ 5
  · obtain rfl | rfl | rfl | rfl | rfl : h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 := by omega
    · rw [l1]; decide
    · rw [l2]; decide
    · rw [l3]; decide
    · rw [l4]; decide
    · rw [l5]; decide
  · obtain ⟨d, hd6, hdw⟩ := single_of_words (c6.trans t6)
    have hdmem : d ∈ (run (X0 [false]).archive (X0 [false]).active (fun k => k + 1)
        (fun _ => seed164Prov) 6).1 := by
      have : d ∈ polAct [false] 6 := by rw [hd6]; exact List.Mem.head _
      exact (List.mem_filter.mp this).1
    have hdwf : d.WellFormed :=
      (run_inv (S0 := (X0 [false]).active) (st := fun k => k + 1) (pv := fun _ => seed164Prov)
        hnd0 hwf0 6).2 d hdmem
    have hx : ExtL 3 (fullWord d) := ⟨[true, true, true], by decide, by rw [hdw]; rfl⟩
    obtain ⟨i, hi⟩ : ∃ i, h = 6 + 2 * i ∨ h = 6 + 2 * i + 1 := ⟨(h - 6) / 2, by omega⟩
    obtain ⟨e, he, _, _, hl⟩ := tail_L (st := fun k => k + 1) (pv := fun _ => seed164Prov)
      hnd0 hwf0 hroot (show act (X0 [false]).archive (X0 [false]).active (fun k => k + 1)
        (fun _ => seed164Prov) 6 = [d] from hd6) hdwf hx i
    rcases hi with rfl | rfl
    · have : (polAct [false] (6 + 2 * i)).length = 1 := by
        rw [show polAct [false] (6 + 2 * i) = [e] from he]
        rfl
      rw [this, if_pos (Or.inr ⟨by omega, by omega⟩)]
    · rw [show (polAct [false] (6 + 2 * i + 1)).length = 2 from hl, if_neg]
      omega

theorem polarized_L_singleton_iff (h : ℕ) (h1 : 1 ≤ h) :
    (polAct [false] h).length = 1 ↔ (h = 3 ∨ (6 ≤ h ∧ h % 2 = 0)) := by
  rw [polarized_L_support_card h h1]
  by_cases hc : (h = 3 ∨ (6 ≤ h ∧ h % 2 = 0))
  · simp [hc]
  · simp [hc]

/-- **Theorem 16.5, the polarized question `𝒬_R`, at every horizon.** The
    occurrence support of `𝒬_R` at horizon `h ≥ 1` has one member when `h = 3`
    or `h` is even and at least `6`, and two members otherwise. No range: the
    tail from tick `6` is `tail_R`. -/
theorem polarized_R_support_card (h : ℕ) (h1 : 1 ≤ h) :
    (polAct [true] h).length = if (h = 3 ∨ (6 ≤ h ∧ h % 2 = 0)) then 1 else 2 := by
  obtain ⟨hnd0, hwf0, hroot⟩ := polStart_wf [true]
  obtain ⟨c1, c2, c3, c4, c5, c6, _⟩ := polAct_words_R
  obtain ⟨t1, t2, t3, t4, t5, t6, _⟩ := theorem_16_5_polarized_R
  have l1 : (polAct [true] 1).length = 2 := by simpa using congrArg List.length (c1.trans t1)
  have l2 : (polAct [true] 2).length = 2 := by simpa using congrArg List.length (c2.trans t2)
  have l3 : (polAct [true] 3).length = 1 := by simpa using congrArg List.length (c3.trans t3)
  have l4 : (polAct [true] 4).length = 2 := by simpa using congrArg List.length (c4.trans t4)
  have l5 : (polAct [true] 5).length = 2 := by simpa using congrArg List.length (c5.trans t5)
  by_cases hh : h ≤ 5
  · obtain rfl | rfl | rfl | rfl | rfl : h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 := by omega
    · rw [l1]; decide
    · rw [l2]; decide
    · rw [l3]; decide
    · rw [l4]; decide
    · rw [l5]; decide
  · obtain ⟨d, hd6, hdw⟩ := single_of_words (c6.trans t6)
    have hdmem : d ∈ (run (X0 [true]).archive (X0 [true]).active (fun k => k + 1)
        (fun _ => seed164Prov) 6).1 := by
      have : d ∈ polAct [true] 6 := by rw [hd6]; exact List.Mem.head _
      exact (List.mem_filter.mp this).1
    have hdwf : d.WellFormed :=
      (run_inv (S0 := (X0 [true]).active) (st := fun k => k + 1) (pv := fun _ => seed164Prov)
        hnd0 hwf0 6).2 d hdmem
    have hx : ExtR 3 (fullWord d) := ⟨[false, false, false], by decide, by rw [hdw]; rfl⟩
    obtain ⟨i, hi⟩ : ∃ i, h = 6 + 2 * i ∨ h = 6 + 2 * i + 1 := ⟨(h - 6) / 2, by omega⟩
    obtain ⟨e, he, _, _, hl⟩ := tail_R (st := fun k => k + 1) (pv := fun _ => seed164Prov)
      hnd0 hwf0 hroot (show act (X0 [true]).archive (X0 [true]).active (fun k => k + 1)
        (fun _ => seed164Prov) 6 = [d] from hd6) hdwf hx i
    rcases hi with rfl | rfl
    · have : (polAct [true] (6 + 2 * i)).length = 1 := by
        rw [show polAct [true] (6 + 2 * i) = [e] from he]
        rfl
      rw [this, if_pos (Or.inr ⟨by omega, by omega⟩)]
    · rw [show (polAct [true] (6 + 2 * i + 1)).length = 2 from hl, if_neg]
      omega

theorem polarized_R_singleton_iff (h : ℕ) (h1 : 1 ≤ h) :
    (polAct [true] h).length = 1 ↔ (h = 3 ∨ (6 ≤ h ∧ h % 2 = 0)) := by
  rw [polarized_R_support_card h h1]
  by_cases hc : (h = 3 ∨ (6 ≤ h ∧ h % 2 = 0))
  · simp [hc]
  · simp [hc]

/-! ## The advance `2 → 3` of the polarized questions -/

/-- **The advance `2→3` of `𝒬_L`.** The proposals, in the order of the
    admitted family, are `LLLL`, `LLLR`, `LRLL`, `LRLR`. Their tension
    histograms, sorted, are `{0,5,8,10}`, `{0,1,5,9}`, `{0,1,8,13}`,
    `{0,9,10,13}`; the histogram of `LLLR` is termwise below the other three.
    The coherence values are `116 - 71φ`, `-63 + 40φ`, `-343 + 213φ`, `-342 + 212φ`; the
    second is the strict maximum, which is `S_3(𝒬_L) = {LLLR}` of
    `theorem_16_5_polarized_L`. -/
theorem advance_2_3_L :
    (admittedCores MOL 3 seed164Prov props2L).map Core.fullWord =
      [[false, false, false, false], [false, false, false, true],
       [false, true, false, false], [false, true, false, true]] ∧
    (admittedFam MOL 3 seed164Prov props2L).map
        (tensions (admittedFam MOL 3 seed164Prov props2L)) =
      [[0, 5, 8, 10], [5, 0, 1, 9], [8, 1, 0, 13], [10, 9, 13, 0]] ∧
    (admittedFam MOL 3 seed164Prov props2L).map
        (coherenceOf (admittedFam MOL 3 seed164Prov props2L)) =
      [(⟨116, -71⟩ : Zphi), ⟨-63, 40⟩, ⟨-343, 213⟩, ⟨-342, 212⟩] ∧
    activeWords XL3 = [[false, false, false, true]] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The side mirror**, checked independently of `advance_2_3_L`. The family
    order is `RLRL`, `RLRR`, `RRRL`, `RRRR`, so the histograms and coherence values of
    `advance_2_3_L` come in the reverse order and the unique maximizer `RRRL`
    (coherence value `-63 + 40φ`) is the third member. -/
theorem advance_2_3_R :
    (admittedCores MOR 3 seed164Prov props2R).map Core.fullWord =
      [[true, false, true, false], [true, false, true, true],
       [true, true, true, false], [true, true, true, true]] ∧
    (admittedFam MOR 3 seed164Prov props2R).map
        (tensions (admittedFam MOR 3 seed164Prov props2R)) =
      [[0, 13, 9, 10], [13, 0, 1, 8], [9, 1, 0, 5], [10, 8, 5, 0]] ∧
    (admittedFam MOR 3 seed164Prov props2R).map
        (coherenceOf (admittedFam MOR 3 seed164Prov props2R)) =
      [(⟨-342, 212⟩ : Zphi), ⟨-343, 213⟩, ⟨-63, 40⟩, ⟨116, -71⟩] ∧
    activeWords XR3 = [[true, true, true, false]] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## The closing words at horizons 6 and 8 -/

/-- **`𝒬_L` closes at `h = 6` on `LLLRRRR` (`5:16`) and at `h = 8` on
    `LLLRRRRRR` (`7:22`).** The words and addresses are the run's occurrences
    at those horizons, identified with the carriers `XL6` and `Beat.YL8`
    (`polAct_words_L`, `polAct_words_YL8`); the values are
    `theorem_16_5_polarized_L(_addressed)` and `Beat.tick_eight_closing_words`. -/
theorem polarized_L_closing_words :
    (polAct [false] 6).map fullWord = [[false, false, false, true, true, true, true]] ∧
    (polAct [false] 8).map fullWord =
      [[false, false, false, true, true, true, true, true, true]] ∧
    addressedList ((polAct [false] 6).map fullWord) = [(⟨5, 16, by decide⟩ : Pres)] ∧
    (addressedList ((polAct [false] 8).map fullWord)).map (fun r => (r.p, r.q)) = [(7, 22)] := by
  have c6 := polAct_words_L.2.2.2.2.2.1
  have y8 := polAct_words_YL8.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [c6]; exact theorem_16_5_polarized_L.2.2.2.2.2.1
  · rw [y8]; exact Beat.tick_eight_closing_words.1
  · rw [c6]; exact theorem_16_5_polarized_L_addressed.2.2.2.2.2.2.1
  · rw [y8]; exact Beat.tick_eight_closing_words.2.2.1

/-- **`𝒬_R` closes at `h = 6` on `RRRLLLL` (`16:5`) and at `h = 8` on
    `RRRLLLLLL` (`22:7`)**, the side mirrors, from the independent `R`
    traces. -/
theorem polarized_R_closing_words :
    (polAct [true] 6).map fullWord = [[true, true, true, false, false, false, false]] ∧
    (polAct [true] 8).map fullWord =
      [[true, true, true, false, false, false, false, false, false]] ∧
    addressedList ((polAct [true] 6).map fullWord) = [(⟨16, 5, by decide⟩ : Pres)] ∧
    (addressedList ((polAct [true] 8).map fullWord)).map (fun r => (r.p, r.q)) = [(22, 7)] := by
  have c6 := polAct_words_R.2.2.2.2.2.1
  have y8 := polAct_words_YR8.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [c6]; exact theorem_16_5_polarized_R.2.2.2.2.2.1
  · rw [y8]; exact Beat.tick_eight_closing_words.2.1
  · rw [c6]; exact theorem_16_5_polarized_R_addressed.2.2.2.2.2.2.1
  · rw [y8]; exact Beat.tick_eight_closing_words.2.2.2

#print axioms polStart_wf
#print axioms polAct_words_L
#print axioms polAct_words_R
#print axioms polAct_words_YL8
#print axioms polAct_words_YR8
#print axioms tail_L
#print axioms tail_R
#print axioms single_of_words
#print axioms polarized_L_support_card
#print axioms polarized_L_singleton_iff
#print axioms polarized_R_support_card
#print axioms polarized_R_singleton_iff
#print axioms advance_2_3_L
#print axioms advance_2_3_R
#print axioms polarized_L_closing_words
#print axioms polarized_R_closing_words

end T16_5_polarized
end Gaps
end RatioSpace
