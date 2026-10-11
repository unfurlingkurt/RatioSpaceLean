/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.PrecaptureClassification
/-!
  Elements II §16, Theorem 16.12, items 1 and 2 — capture, on words.

  *"Two questions whose current supports carry the same words therefore
  produce, tick by tick, the same proposal words, the same tensions, the same
  certificates, and the same maximizer words; the stable identifiers differ in
  their question and seed tags but enter no comparison."*

  `Capture.lean` built the one-occurrence form of that sentence and named the
  missing piece: a function for "the tick-`i` support of the lone-seed question
  with seed `x`". It is `wIter i [x]`, where `wordStep` is one tick of
  Definition 8.1 at `ε` read entirely off words. `nextCores_words`
  proves the tick map on cores and `wordStep` on words agree, so any run's
  active words are `wIter` of its words at any earlier tick. Items 1 and 2
  follow.

  Every theorem `propext`/`Quot.sound` or less.
-/
set_option linter.style.show false

namespace RatioSpace
namespace Two
namespace Step5Words

open Mat2 Word Frame Pres RatioSpace Advance Accumulation RootOrbit Beat Beat11Bridge
  RootChainCarrier Step5Beat Step5Induction

/-- Filtering commutes with a map when the predicates agree through it. -/
theorem filter_map_comm {α β : Type} (f : α → β) (P : α → Bool) (Q : β → Bool) :
    ∀ (l : List α), (∀ a ∈ l, P a = Q (f a)) → (l.filter P).map f = (l.map f).filter Q
  | [], _ => rfl
  | a :: l, h => by
    have ih := filter_map_comm f P Q l (fun b hb => h b (List.Mem.tail _ hb))
    have ha := h a (List.Mem.head _)
    cases hPa : P a with
    | true =>
      rw [List.filter_cons_of_pos (p := P) (a := a) hPa, List.map_cons, List.map_cons,
        List.filter_cons_of_pos (p := Q) (a := f a) (by rw [← ha]; exact hPa), ih]
    | false =>
      rw [List.filter_cons_of_neg (p := P) (a := a) (by rw [hPa]; exact Bool.false_ne_true),
        List.map_cons,
        List.filter_cons_of_neg (p := Q) (a := f a) (by rw [← ha, hPa]; exact
          Bool.false_ne_true), ih]

/-- The children's words of a list of words, in proposal order. -/
def childWords (ws : List Word) : List Word := ws.flatMap (fun w => [w ++ [false], w ++ [true]])

/-- Definition 8.1's filter at `ε`, on a child word, against the
    children of `ws`. -/
def keepW (ws : List Word) (w : Word) : Bool :=
  decide (((childWords ws).map rI).all (fun z =>
    coherenceOf ((childWords ws).map rI) z ≤ coherenceOf ((childWords ws).map rI) (rI w)))

/-- **One tick on words.** Definition 8.1 at `ε`, on the children of
    the given words, read entirely off the words. -/
def wordStep (ws : List Word) : List Word := (childWords ws).filter (keepW ws)

theorem map_map' {α β γ : Type} (g : β → γ) (f : α → β) :
    ∀ l : List α, List.map g (List.map f l) = List.map (fun x => g (f x)) l
  | [] => rfl
  | a :: l => by
    show g (f a) :: List.map g (List.map f l) = g (f a) :: List.map (fun x => g (f x)) l
    rw [map_map' g f l]

/-- `i` ticks on words. -/
def wIter : ℕ → List Word → List Word
  | 0, ws => ws
  | i + 1, ws => wordStep (wIter i ws)

theorem wIter_succ' : ∀ (i : ℕ) (ws : List Word), wIter i (wordStep ws) = wIter (i + 1) ws
  | 0, _ => rfl
  | i + 1, ws => by
    show wordStep (wIter i (wordStep ws)) = wordStep (wIter (i + 1) ws)
    rw [wIter_succ' i ws]

section tick

variable {archive : List Core} {active : List QuestionId} (s : ℕ) (p : Provenance)

theorem children_words : ∀ (L : List Core),
    ((L.flatMap (fun c => [(c, false), (c, true)])).map (fun q => childCore q.1 q.2 s p)).map
      fullWord = childWords (L.map fullWord)
  | [] => rfl
  | c :: cs => by
    show (([(c, false), (c, true)] ++ cs.flatMap (fun c => [(c, false), (c, true)])).map
        (fun q => childCore q.1 q.2 s p)).map fullWord
      = [fullWord c ++ [false], fullWord c ++ [true]] ++ childWords (cs.map fullWord)
    rw [List.map_append, List.map_append, children_words cs]
    show [fullWord (childCore c false s p), fullWord (childCore c true s p)] ++ _ = _
    rw [child_fullWord, child_fullWord]

theorem filterMap_addr_children : ∀ (props : List (Core × Bool)),
    (props.map (fun q => childCore q.1 q.2 s p)).filterMap (addrOf 1)
      = (props.map (fun q => childCore q.1 q.2 s p)).map (fun c => rI (fullWord c))
  | [] => rfl
  | q :: qs => by
    rw [List.map_cons, List.filterMap_cons_some (addrOf_child_some s p q.1 q.2), List.map_cons,
      filterMap_addr_children qs, child_fullWord]

/-- The admitted family at `ε`, read off the active words. -/
theorem admittedFam_words :
    admittedFam 1 s p (proposals archive active)
      = (childWords ((archive.filter (fun d => d.id ∈ active)).map fullWord)).map rI := by
  unfold admittedFam
  rw [admittedCores_eps, filterMap_addr_children, ← children_words s p, map_map' rI fullWord]
  rfl

/-- **Word-level determinacy of one tick.** The next active cores' words are
    `wordStep` of the current active cores' words. -/
theorem nextCores_words (hnd : (archive.map Core.id).Nodup) (hwf : ∀ d ∈ archive, d.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive) :
    (nextCores archive active s p).map fullWord
      = wordStep ((archive.filter (fun d => d.id ∈ active)).map fullWord) := by
  unfold nextCores
  rw [next_filter_eq_kept s p hnd hwf hfresh]
  have hagree : ∀ c ∈ (proposals archive active).map (fun q => childCore q.1 q.2 s p),
      keepPred 1 s p (proposals archive active) c
        = keepW ((archive.filter (fun d => d.id ∈ active)).map fullWord) (fullWord c) := by
    intro c hc
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hc
    rw [keep_child, admittedFam_words, child_fullWord]
    all_goals rfl
  rw [filter_map_comm fullWord (keepPred 1 s p (proposals archive active))
    (keepW ((archive.filter (fun d => d.id ∈ active)).map fullWord))
    ((proposals archive active).map (fun q => childCore q.1 q.2 s p)) hagree]
  show List.filter (keepW ((archive.filter (fun d => d.id ∈ active)).map fullWord))
      (List.map fullWord (List.map (fun q => childCore q.1 q.2 s p)
        ((archive.filter (fun d => d.id ∈ active)).flatMap (fun c => [(c, false), (c, true)])))) = _
  rw [children_words]
  rfl

end tick

/-! ## Along a run -/

section run

variable {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ} {pv : ℕ → Provenance}

theorem act_words (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0) (j : ℕ) :
    (act A0 S0 st pv (j + 1)).map fullWord = wordStep ((act A0 S0 st pv j).map fullWord) := by
  obtain ⟨hnd, hwf⟩ := run_inv (S0 := S0) (st := st) (pv := pv) hnd0 hwf0 j
  exact nextCores_words (st j) (pv j) hnd hwf ((run_hfresh (st := st) (pv := pv) hroot) j)

/-- A run's active words `i` ticks after tick `j` are `wIter i` of its words at `j`. -/
theorem act_words_shift (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0) (j : ℕ) :
    ∀ i, (act A0 S0 st pv (j + i)).map fullWord = wIter i ((act A0 S0 st pv j).map fullWord)
  | 0 => rfl
  | i + 1 => by
    show (act A0 S0 st pv ((j + i) + 1)).map fullWord = wordStep (wIter i _)
    rw [act_words hnd0 hwf0 hroot (j + i), act_words_shift hnd0 hwf0 hroot j i]

end run

/-- A singleton's two children tie exactly, so `wordStep` keeps both. -/
theorem wordStep_single (x : Word) : wordStep [x] = [x ++ [false], x ++ [true]] := by
  have heq := pair_coherence_equal (rI (x ++ [false])) (rI (x ++ [true]))
  have top : ∀ w, coherenceOf [rI (x ++ [false]), rI (x ++ [true])] (rI w)
      = coherenceOf [rI (x ++ [false]), rI (x ++ [true])] (rI (x ++ [false])) →
      decide ([rI (x ++ [false]), rI (x ++ [true])].all (fun z =>
        coherenceOf [rI (x ++ [false]), rI (x ++ [true])] z
          ≤ coherenceOf [rI (x ++ [false]), rI (x ++ [true])] (rI w))) = true := by
    intro w hw
    apply decide_eq_true
    refine List.all_eq_true.mpr (fun z hz => decide_eq_true ?_)
    rw [hw]
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_refl _
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_of_eq heq.symm
    · cases hz
  refine List.filter_eq_self.mpr (fun w hw => ?_)
  rcases List.mem_cons.mp hw with rfl | hw
  · exact top _ rfl
  rcases List.mem_cons.mp hw with rfl | hw
  · exact top _ heq.symm
  · cases hw

/-! ## Theorem 16.12, items 1 and 2 -/

section capture

variable {A0 : List Core} {S0 : List QuestionId} {st : ℕ → ℕ} {pv : ℕ → Provenance}
  {B0 : List Core} {T0 : List QuestionId} {st' : ℕ → ℕ} {pv' : ℕ → Provenance}

/-- **Theorem 16.12, item 1.** If a run's support at tick `j` is one occurrence
    with word `x`, and a second run is the lone-seed question with seed `x`
    (its tick-0 support is one occurrence with word `x`), then for every `i`
    the words of the first run at `j + i` are the words of the lone-seed
    question at `i`. Identifiers, strata and provenance never enter. -/
theorem theorem_16_12_item1
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0)
    (hnd0' : (B0.map Core.id).Nodup) (hwf0' : ∀ d ∈ B0, d.WellFormed)
    (hroot' : Rooted B0 T0)
    (j : ℕ) (x : Word) (hj : (act A0 S0 st pv j).map fullWord = [x])
    (h0 : (act B0 T0 st' pv' 0).map fullWord = [x]) (i : ℕ) :
    (act A0 S0 st pv (j + i)).map fullWord = (act B0 T0 st' pv' i).map fullWord := by
  rw [act_words_shift hnd0 hwf0 hroot j i, hj]
  have h := act_words_shift (st := st') (pv := pv') hnd0' hwf0' hroot' 0 i
  rw [Nat.zero_add] at h
  rw [h, h0]

/-- **Theorem 16.12, item 2.** If the support at tick `j` is the sibling pair
    `{xL, xR}`, the words at `j + i` are the lone-seed question's words at
    `i + 1`. -/
theorem theorem_16_12_item2
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0)
    (hnd0' : (B0.map Core.id).Nodup) (hwf0' : ∀ d ∈ B0, d.WellFormed)
    (hroot' : Rooted B0 T0)
    (j : ℕ) (x : Word) (hj : (act A0 S0 st pv j).map fullWord = [x ++ [false], x ++ [true]])
    (h0 : (act B0 T0 st' pv' 0).map fullWord = [x]) (i : ℕ) :
    (act A0 S0 st pv (j + i)).map fullWord = (act B0 T0 st' pv' (i + 1)).map fullWord := by
  rw [act_words_shift hnd0 hwf0 hroot j i, hj, ← wordStep_single, wIter_succ']
  have h := act_words_shift (st := st') (pv := pv') hnd0' hwf0' hroot' 0 (i + 1)
  rw [Nat.zero_add] at h
  rw [h, h0]

/-- **Theorem 16.12, item 1, the consequence.** *"Theorem 16.11 therefore
    governs every later tick, with `|S_{j+i}| ≤ 2`."* The words agree, so the
    lengths do, and the lone-seed run has clause 1. -/
theorem theorem_16_12_item1_governed
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0)
    (hnd0' : (B0.map Core.id).Nodup) (hwf0' : ∀ d ∈ B0, d.WellFormed)
    (hroot' : Rooted B0 T0)
    (hS0' : Shape (B0.filter (fun d => d.id ∈ T0)))
    (j : ℕ) (x : Word) (hj : (act A0 S0 st pv j).map fullWord = [x])
    (h0 : (act B0 T0 st' pv' 0).map fullWord = [x]) (i : ℕ) :
    (act A0 S0 st pv (j + i)).length = 1 ∨ (act A0 S0 st pv (j + i)).length = 2 := by
  have h := congrArg List.length
    (theorem_16_12_item1 hnd0 hwf0 hroot hnd0' hwf0' hroot' j x hj h0 i)
  rw [List.length_map, List.length_map] at h
  rw [h]
  exact (clauses_1_2 hnd0' hwf0' hS0' hroot' i).2

/-- **Theorem 16.12, item 1, the beat.** *"and the singleton beat of Theorem
    16.11(4) counted from tick `j`."* -/
theorem theorem_16_12_item1_beat
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0)
    (hnd0' : (B0.map Core.id).Nodup) (hwf0' : ∀ d ∈ B0, d.WellFormed)
    (hroot' : Rooted B0 T0)
    (hS0' : Shape (B0.filter (fun d => d.id ∈ T0)))
    (h0len : (B0.filter (fun d => d.id ∈ T0)).length = 1)
    (j : ℕ) (x : Word) (hj : (act A0 S0 st pv j).map fullWord = [x])
    (h0 : (act B0 T0 st' pv' 0).map fullWord = [x]) (i : ℕ) :
    (act A0 S0 st pv (j + i)).length = 1 ↔ i % 2 = npres B0 T0 st' pv' i % 2 := by
  have h := congrArg List.length
    (theorem_16_12_item1 hnd0 hwf0 hroot hnd0' hwf0' hroot' j x hj h0 i)
  rw [List.length_map, List.length_map] at h
  rw [h]
  exact clause_4 hnd0' hwf0' hS0' hroot' h0len i

/-- **Theorem 16.12, item 2, the consequence.** From a sibling pair at tick `j`,
    `|S_{j+i}|` is the lone-seed question's `|S_{i+1}|`, so it is governed by
    Theorem 16.11 too. -/
theorem theorem_16_12_item2_governed
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0)
    (hnd0' : (B0.map Core.id).Nodup) (hwf0' : ∀ d ∈ B0, d.WellFormed)
    (hroot' : Rooted B0 T0)
    (hS0' : Shape (B0.filter (fun d => d.id ∈ T0)))
    (j : ℕ) (x : Word) (hj : (act A0 S0 st pv j).map fullWord = [x ++ [false], x ++ [true]])
    (h0 : (act B0 T0 st' pv' 0).map fullWord = [x]) (i : ℕ) :
    (act A0 S0 st pv (j + i)).length = 1 ∨ (act A0 S0 st pv (j + i)).length = 2 := by
  have h := congrArg List.length
    (theorem_16_12_item2 hnd0 hwf0 hroot hnd0' hwf0' hroot' j x hj h0 i)
  rw [List.length_map, List.length_map] at h
  rw [h]
  exact (clauses_1_2 hnd0' hwf0' hS0' hroot' (i + 1)).2

/-- **Theorem 16.12, item 2, the beat**, read one tick later on the lone-seed
    question. -/
theorem theorem_16_12_item2_beat
    (hnd0 : (A0.map Core.id).Nodup) (hwf0 : ∀ d ∈ A0, d.WellFormed)
    (hroot : Rooted A0 S0)
    (hnd0' : (B0.map Core.id).Nodup) (hwf0' : ∀ d ∈ B0, d.WellFormed)
    (hroot' : Rooted B0 T0)
    (hS0' : Shape (B0.filter (fun d => d.id ∈ T0)))
    (h0len : (B0.filter (fun d => d.id ∈ T0)).length = 1)
    (j : ℕ) (x : Word) (hj : (act A0 S0 st pv j).map fullWord = [x ++ [false], x ++ [true]])
    (h0 : (act B0 T0 st' pv' 0).map fullWord = [x]) (i : ℕ) :
    (act A0 S0 st pv (j + i)).length = 1 ↔ (i + 1) % 2 = npres B0 T0 st' pv' (i + 1) % 2 := by
  have h := congrArg List.length
    (theorem_16_12_item2 hnd0 hwf0 hroot hnd0' hwf0' hroot' j x hj h0 i)
  rw [List.length_map, List.length_map] at h
  rw [h]
  exact clause_4 hnd0' hwf0' hS0' hroot' h0len (i + 1)

end capture

end Step5Words
end Two
end RatioSpace
