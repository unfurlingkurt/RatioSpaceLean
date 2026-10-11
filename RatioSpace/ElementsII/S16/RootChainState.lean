/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.ClosurePatternLink
import RatioSpace.ElementsII.S16.RootChain
/-!
  Elements II §16 Theorem 16.11, Step 4 on the tick carrier.

  `Two/RootChain.lean` proved Step 4 on the admitted family: `support (fam k)
  = [rb k, rc k]`. This file carries it through the tree's one-tick advance,
  as `Two/Beat11Bridge.lean` did for Step 1.

  Let the active cores be `x, y`, in that order, with full words `LR^k` and
  `RL^k`, and let the observer sit at `ε`. Then one advance under
  `axiomSelect`:
  * admits all four children, in the order `xL, xR, yL, yR`
    (`root_admittedCores`), since every accumulated matrix is `G` of a word;
  * addresses them to exactly `fam k = [a, b, c, d]` (`root_admittedFam`),
    because `xL = LR^kL`, `xR = LR^{k+1}`, `yL = RL^{k+1}`, `yR = RL^kR`;
  * selects exactly `[xR, yL]` (`root_step`), which is `{LR^{k+1}, RL^{k+1}}`.

  `root_step_words` records that the two retained cores have full words
  `LR^{k+1}` and `RL^{k+1}`, so the hypotheses of `root_step` hold again at
  `k+1` for the next pair. `advanceCarrier_active_root` states the step on the
  carrier `advanceCarrier` returns.

  **One hypothesis the book leaves implicit, stated rather than assumed:** the
  pair is the whole active family in the order `[LR^k, RL^k]`, the same
  `archive.filter (· ∈ active)` form as `Beat11Bridge.sibling_*`.

  **Re-establishment built 2026-09-14, 00:30 work beat:** the next carrier's
  archive filter is again `[xR, yL]` (`advanceArchive_filter_children`,
  `root_next_pair`, `advanceCarrier_root_chain`). Freshness is not a gap: it is
  `advanceCarrier`'s own `hfresh`, supplied at every tick, and together with
  well-formed parents with distinct identifiers it is all the step needs.
  The same re-establishment for every other kept pattern Steps 1–3 produce
  (`pair_next_xL`, `pair_next_yR`, `pair_next_xLyR`), and Corollary 8.11 on the
  carrier, a singleton opening its sibling pair (`single_step`,
  `advanceCarrier_single_chain`). And the general form that makes the
  pattern-by-pattern lemmas special cases: for any active family at `ε`, the
  next archive filtered by what `axiomSelect` returned is exactly the admitted
  children Definition 8.1 kept (`next_filter_eq_kept`).

  Every theorem `propext`/`Quot.sound` or less.
-/
set_option linter.style.show false

namespace RatioSpace
namespace Two
namespace RootChainCarrier

open Mat2 Word Frame Pres RatioSpace Advance Accumulation RootOrbit Beat Beat11 Contrast
  Beat11Bridge RootChain

/-- The full word of a core. -/
def fullWord (c : Core) : Word := c.seed.word ++ c.relWord

/-- A child's accumulated matrix is `G` of its full word. -/
theorem child_fullMatrix (c : Core) (g : Bool) (s : ℕ) (p : Provenance) :
    (childCore c g s p).fullMatrix = G (fullWord c ++ [g]) := by
  show G c.seed.word * G (c.relWord ++ [g]) = _
  rw [← G_append, fullWord, List.append_assoc]

theorem child_fullWord (c : Core) (g : Bool) (s : ℕ) (p : Provenance) :
    fullWord (childCore c g s p) = fullWord c ++ [g] := by
  show c.seed.word ++ (c.relWord ++ [g]) = _
  rw [fullWord, List.append_assoc]

/-- Every child is direct-positively admitted at observer `ε`. -/
theorem child_admitted (c : Core) (g : Bool) (s : ℕ) (p : Provenance) :
    decide (negLoad (Q 1 (childCore c g s p).fullMatrix) = 0) = true := by
  rw [Q_one, child_fullMatrix, negLoad_G]
  rfl

/-- At observer `ε` a child's address is `r` of its full word. -/
theorem addrOf_child (c : Core) (g : Bool) (s : ℕ) (p : Provenance) :
    addrOf 1 (childCore c g s p) = IPres.ofPres? (r (fullWord c ++ [g])) := by
  have hQ : Q 1 (childCore c g s p).fullMatrix = G (fullWord c ++ [g]) := by
    rw [Q_one, child_fullMatrix]
  unfold addrOf
  rw [lambda_eq 1 _ hQ]
  rfl

theorem replicate_snoc (k : ℕ) (b : Bool) :
    List.replicate k b ++ [b] = List.replicate (k + 1) b ++ [] := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (b :: ·) ih

section root

variable {x y : Core} {k : ℕ} (s : ℕ) (p : Provenance)

theorem addr_xL (hx : fullWord x = false :: List.replicate k true) :
    addrOf 1 (childCore x false s p) = some (ra k) := by
  rw [addrOf_child, hx]
  exact ofPres?_eq_some (walk_mid_pos empty _) (addr_a k).1 (addr_a k).2

theorem addr_xR (hx : fullWord x = false :: List.replicate k true) :
    addrOf 1 (childCore x true s p) = some (rb k) := by
  rw [addrOf_child, hx]
  show IPres.ofPres? (r (false :: (List.replicate k true ++ [true]))) = _
  rw [replicate_snoc]
  exact ofPres?_eq_some (walk_mid_pos empty _) (addr_b k).1 (addr_b k).2

theorem addr_yL (hy : fullWord y = true :: List.replicate k false) :
    addrOf 1 (childCore y false s p) = some (rc k) := by
  rw [addrOf_child, hy]
  show IPres.ofPres? (r (true :: (List.replicate k false ++ [false]))) = _
  rw [replicate_snoc]
  exact ofPres?_eq_some (walk_mid_pos empty _) (addr_c k).1 (addr_c k).2

theorem addr_yR (hy : fullWord y = true :: List.replicate k false) :
    addrOf 1 (childCore y true s p) = some (rd k) := by
  rw [addrOf_child, hy]
  exact ofPres?_eq_some (walk_mid_pos empty _) (addr_d k).1 (addr_d k).2

variable {archive : List Core} {active : List QuestionId}

/-- The root pair proposes its four children, in order. -/
theorem root_proposals (hpair : archive.filter (fun d => d.id ∈ active) = [x, y]) :
    proposals archive active = [(x, false), (x, true), (y, false), (y, true)] := by
  unfold proposals
  rw [hpair]
  rfl

/-- At observer `ε` the admitted cores are all four children. -/
theorem root_admittedCores (hpair : archive.filter (fun d => d.id ∈ active) = [x, y]) :
    admittedCores 1 s p (proposals archive active) =
      [childCore x false s p, childCore x true s p,
       childCore y false s p, childCore y true s p] := by
  unfold admittedCores
  rw [root_proposals hpair]
  show List.filter _ [childCore x false s p, childCore x true s p,
       childCore y false s p, childCore y true s p] = _
  refine List.filter_eq_self.mpr (fun d hd => ?_)
  rcases List.mem_cons.mp hd with rfl | hd
  · exact child_admitted x false s p
  rcases List.mem_cons.mp hd with rfl | hd
  · exact child_admitted x true s p
  rcases List.mem_cons.mp hd with rfl | hd
  · exact child_admitted y false s p
  rcases List.mem_cons.mp hd with rfl | hd
  · exact child_admitted y true s p
  · cases hd

/-- **The admitted family is `fam k`**, the four words `LR^kL, LR^{k+1},
    RL^{k+1}, RL^kR`. -/
theorem root_admittedFam (hpair : archive.filter (fun d => d.id ∈ active) = [x, y])
    (hx : fullWord x = false :: List.replicate k true)
    (hy : fullWord y = true :: List.replicate k false) :
    admittedFam 1 s p (proposals archive active) = fam k := by
  unfold admittedFam
  rw [root_admittedCores s p hpair, List.filterMap_cons_some (addr_xL s p hx),
    List.filterMap_cons_some (addr_xR s p hx), List.filterMap_cons_some (addr_yL s p hy),
    List.filterMap_cons_some (addr_yR s p hy)]
  rfl

/-- The maximality test on `fam k`, one value per member. -/
theorem fam_pred (k : ℕ) :
    (fam k).all (fun z => decide (coherenceOf (fam k) z ≤ coherenceOf (fam k) (ra k))) = false ∧
    (fam k).all (fun z => decide (coherenceOf (fam k) z ≤ coherenceOf (fam k) (rb k))) = true ∧
    (fam k).all (fun z => decide (coherenceOf (fam k) z ≤ coherenceOf (fam k) (rc k))) = true ∧
    (fam k).all (fun z => decide (coherenceOf (fam k) z ≤ coherenceOf (fam k) (rd k))) = false := by
  have hab := coherence_a_lt_b k
  have hbc : coherenceOf (fam k) (rb k) = coherenceOf (fam k) (rc k) := by
    rw [coherence_b, coherence_c]
  have had : coherenceOf (fam k) (ra k) = coherenceOf (fam k) (rd k) := by
    rw [coherence_a, coherence_d]
  have top : ∀ w, coherenceOf (fam k) w = coherenceOf (fam k) (rb k) →
      (fam k).all (fun z => decide (coherenceOf (fam k) z ≤ coherenceOf (fam k) w)) = true := by
    intro w hw
    refine List.all_eq_true.mpr (fun z hz => decide_eq_true ?_)
    rw [hw]
    rcases mem_fam hz with rfl | rfl | rfl | rfl
    · exact le_of_lt hab
    · exact le_refl _
    · exact le_of_eq hbc.symm
    · exact le_of_lt (had ▸ hab)
  have low : ∀ w, coherenceOf (fam k) w = coherenceOf (fam k) (ra k) →
      (fam k).all (fun z => decide (coherenceOf (fam k) z ≤ coherenceOf (fam k) w)) = false := by
    intro w hw
    cases h : (fam k).all (fun z => decide (coherenceOf (fam k) z ≤ coherenceOf (fam k) w))
    · rfl
    · have hle := of_decide_eq_true (List.all_eq_true.mp h (rb k) (by simp [fam]))
      rw [hw] at hle
      exact absurd hle (not_le_of_lt_zphi hab)
  exact ⟨low (ra k) rfl, top (rb k) rfl, top (rc k) hbc.symm, low (rd k) had.symm⟩

/-- **Theorem 16.11, Step 4, on the tree.** From the active pair
    `[LR^k, RL^k]` at observer `ε`, the one-tick advance under `axiomSelect`
    keeps exactly `[LR^{k+1}, RL^{k+1}]`, for every `k`. -/
theorem root_step (hpair : archive.filter (fun d => d.id ∈ active) = [x, y])
    (hx : fullWord x = false :: List.replicate k true)
    (hy : fullWord y = true :: List.replicate k false) :
    axiomSelect 1 s p (proposals archive active)
      = [(childCore x true s p).id, (childCore y false s p).id] := by
  obtain ⟨pa, pb, pc, pd⟩ := fam_pred k
  unfold axiomSelect
  simp only []
  rw [root_admittedCores s p hpair, root_admittedFam s p hpair hx hy]
  rw [List.filter_cons, List.filter_cons, List.filter_cons, List.filter_cons]
  rw [addr_xL s p hx, addr_xR s p hx, addr_yL s p hy, addr_yR s p hy]
  dsimp only
  simp only [pa, pb, pc, pd, Bool.false_eq_true, decide_false, decide_true, if_true, if_false]
    ; rfl

/-- The two retained cores are again a root pair, one letter deeper. -/
theorem root_step_words
    (hx : fullWord x = false :: List.replicate k true)
    (hy : fullWord y = true :: List.replicate k false) :
    fullWord (childCore x true s p) = false :: List.replicate (k + 1) true ∧
      fullWord (childCore y false s p) = true :: List.replicate (k + 1) false := by
  rw [child_fullWord, child_fullWord, hx, hy]
  exact ⟨congrArg (false :: ·) ((replicate_snoc k true).trans (List.append_nil _)),
    congrArg (true :: ·) ((replicate_snoc k false).trans (List.append_nil _))⟩

end root

/-- **Step 4 on the tick carrier.** If a lawful carrier's observer sits at `ε`
    and its active family is the root pair `[LR^k, RL^k]`, advancing it under
    `axiomSelect` leaves exactly `[LR^{k+1}, RL^{k+1}]` active. -/
theorem advanceCarrier_active_root {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (s : ℕ) (p : Provenance) (Δ : List (QuestionId × Aux))
    (hsel : _) (hfresh : _) {x y : Core} {k : ℕ}
    (hMO : X.observer.matrix = 1)
    (hpair : X.archive.filter (fun d => d.id ∈ X.active) = [x, y])
    (hx : fullWord x = false :: List.replicate k true)
    (hy : fullWord y = true :: List.replicate k false) :
    (advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh).active
      = [(childCore x true s p).id, (childCore y false s p).id] := by
  show axiomSelect X.observer.matrix s p (proposals X.archive X.active) = _
  rw [hMO]
  exact root_step s p hpair hx hy

/-! ## Step 5's re-establishment: the next carrier's pair, read off its archive

Every step theorem above takes the active family as
`archive.filter (· ∈ active) = [x, y]`. For the steps to chain on one carrier
that hypothesis has to hold again one tick later. It does, from Lemma 12.1's
freshness (`hfresh`, which `advanceCarrier` already demands) and well-formed
parents with distinct identifiers: nothing further. -/

/-- `List.filter_eq_nil_iff` carries `Classical.choice`; this direction, by
    induction, carries no axioms. -/
theorem filter_eq_nil' {α : Type} (f : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, f a = false) → l.filter f = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons_of_neg (p := f) (a := a)
      (by rw [h a (List.Mem.head _)]; exact Bool.false_ne_true)]
    exact filter_eq_nil' f l (fun b hb => h b (List.Mem.tail _ hb))

/-- **The advanced archive, filtered by identifiers the selector kept, is the
    kept children in proposal order.** The old archive contributes nothing,
    because a fresh identifier is not an old one; the new part is every child,
    because every child is fresh. -/
theorem advanceArchive_filter_children {archive : List Core} {active sel : List QuestionId}
    {s : ℕ} {p : Provenance}
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive)
    (hsel : ∀ i ∈ sel, i ∉ archIds archive) :
    (advanceArchive archive active s p).filter (fun d => d.id ∈ sel)
      = ((proposals archive active).map (fun q => childCore q.1 q.2 s p)).filter
          (fun d => d.id ∈ sel) := by
  unfold advanceArchive keyedUnion
  rw [List.filter_append]
  have hold : archive.filter (fun d => d.id ∈ sel) = [] :=
    filter_eq_nil' _ archive (fun c hc => decide_eq_false (fun hin => hsel c.id hin
      (List.mem_map_of_mem hc)))
  have hnew : ((proposals archive active).map (fun q => childCore q.1 q.2 s p)).filter
      (fun y => ¬ (y.id ∈ archIds archive))
        = (proposals archive active).map (fun q => childCore q.1 q.2 s p) := by
    refine List.filter_eq_self.mpr (fun d hd => ?_)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
    exact decide_eq_true (hfresh q hq)
  rw [hold, hnew, List.nil_append]

section chain

variable {x y : Core} {archive : List Core} {active : List QuestionId} (s : ℕ) (p : Provenance)

/-- **The root pair re-established.** From `[x, y]` = `[LR^k, RL^k]` (any
    well-formed pair with distinct identifiers), after one tick the archive
    filtered by `[xR, yL]`'s identifiers is exactly `[xR, yL]`. -/
theorem root_next_pair (hwfx : x.WellFormed) (hwfy : y.WellFormed) (hxy : x.id ≠ y.id)
    (hpair : archive.filter (fun d => d.id ∈ active) = [x, y])
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive) :
    (advanceArchive archive active s p).filter
        (fun d => d.id ∈ [(childCore x true s p).id, (childCore y false s p).id])
      = [childCore x true s p, childCore y false s p] := by
  have hP := root_proposals hpair
  have hsel : ∀ i ∈ [(childCore x true s p).id, (childCore y false s p).id],
      i ∉ archIds archive := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hfresh (x, true) (by rw [hP]; exact List.Mem.tail _ (List.Mem.head _))
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hfresh (y, false) (by rw [hP]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head
      _)))
    · cases hi
  rw [advanceArchive_filter_children hfresh hsel, hP]
  have n1 : x.id.child false ≠ x.id.child true := fun h => absurd (child_id_inj h).2 (by decide)
  have n2 : x.id.child false ≠ y.id.child false := fun h => hxy (child_id_inj h).1
  have n4 : y.id.child true ≠ x.id.child true := fun h => hxy (child_id_inj h).1.symm
  have n5 : y.id.child true ≠ y.id.child false := fun h => absurd (child_id_inj h).2 (by decide)
  have mno : ∀ {a b c : QuestionId}, a ≠ b → a ≠ c → a ∉ [b, c] := by
    intro a b c h1 h2 hm
    cases hm with
    | head => exact h1 rfl
    | tail _ hm =>
      cases hm with
      | head => exact h2 rfl
      | tail _ hm => cases hm
  have ix := childCore_id x hwfx
  have iy := childCore_id y hwfy
  let L := [(childCore x true s p).id, (childCore y false s p).id]
  have hxL : ¬ (childCore x false s p).id ∈ L := by
    show ¬ _ ∈ [_, _]
    rw [ix false s p, ix true s p, iy false s p]; exact mno n1 n2
  have hyR : ¬ (childCore y true s p).id ∈ L := by
    show ¬ _ ∈ [_, _]
    rw [iy true s p, ix true s p, iy false s p]; exact mno n4 n5
  have hxR : (childCore x true s p).id ∈ L := List.Mem.head _
  have hyL : (childCore y false s p).id ∈ L := List.Mem.tail _ (List.Mem.head _)
  show List.filter (fun d => decide (d.id ∈ L))
    [childCore x false s p, childCore x true s p, childCore y false s p, childCore y true s p] = _
  rw [List.filter_cons_of_neg (p := fun d => decide (d.id ∈ L)) (a := childCore x false s p)
      (fun hm => hxL (of_decide_eq_true hm)),
    List.filter_cons_of_pos (p := fun d => decide (d.id ∈ L)) (a := childCore x true s p)
      (decide_eq_true hxR),
    List.filter_cons_of_pos (p := fun d => decide (d.id ∈ L)) (a := childCore y false s p)
      (decide_eq_true hyL),
    List.filter_cons_of_neg (p := fun d => decide (d.id ∈ L)) (a := childCore y true s p)
      (fun hm => hyR (of_decide_eq_true hm))]
  rfl

/-- **Step 4, chained.** Advancing a lawful carrier at observer `ε` whose active
    pair is `[LR^k, RL^k]` gives a carrier whose active pair, read off its own
    archive, is `[LR^{k+1}, RL^{k+1}]`, with both words, well-formedness and
    distinct identifiers holding again: every hypothesis of
    `advanceCarrier_active_root` at `k + 1` except the next tick's freshness,
    which `advanceCarrier` asks of its caller at every tick. -/
theorem advanceCarrier_root_chain {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (Δ : List (QuestionId × Aux)) (hsel : _) (hfresh : _) {k : ℕ}
    (hMO : X.observer.matrix = 1) (hwfx : x.WellFormed) (hwfy : y.WellFormed) (hxy : x.id ≠ y.id)
    (hpair : X.archive.filter (fun d => d.id ∈ X.active) = [x, y])
    (hx : fullWord x = false :: List.replicate k true)
    (hy : fullWord y = true :: List.replicate k false) :
    let X' := advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh
    X'.observer.matrix = 1 ∧
      X'.archive.filter (fun d => d.id ∈ X'.active)
        = [childCore x true s p, childCore y false s p] ∧
      fullWord (childCore x true s p) = false :: List.replicate (k + 1) true ∧
      fullWord (childCore y false s p) = true :: List.replicate (k + 1) false ∧
      (childCore x true s p).WellFormed ∧ (childCore y false s p).WellFormed ∧
      (childCore x true s p).id ≠ (childCore y false s p).id := by
  intro X'
  have hact : X'.active = [(childCore x true s p).id, (childCore y false s p).id] :=
    advanceCarrier_active_root X hlaw s p Δ hsel hfresh hMO hpair hx hy
  have hw := root_step_words s p hx hy
  refine ⟨hMO, ?_, hw.1, hw.2, childCore_wellFormed _ _ _ _, childCore_wellFormed _ _ _ _, ?_⟩
  · rw [hact]
    exact root_next_pair s p hwfx hwfy hxy hpair hfresh
  · rw [childCore_id x hwfx, childCore_id y hwfy]
    exact fun h => hxy (child_id_inj h).1

/-! ### The same re-establishment for every kept pattern Steps 1–3 and Cor 8.11 produce -/

theorem idFilter_pos {c : Core} {L : List QuestionId} (h : c.id ∈ L) (l : List Core) :
    (c :: l).filter (fun d => decide (d.id ∈ L)) = c :: l.filter (fun d => decide (d.id ∈ L)) :=
  List.filter_cons_of_pos (p := fun d => decide (d.id ∈ L)) (a := c) (decide_eq_true h)

theorem idFilter_neg {c : Core} {L : List QuestionId} (h : c.id ∉ L) (l : List Core) :
    (c :: l).filter (fun d => decide (d.id ∈ L)) = l.filter (fun d => decide (d.id ∈ L)) :=
  List.filter_cons_of_neg (p := fun d => decide (d.id ∈ L)) (a := c)
    (fun hm => h (of_decide_eq_true hm))

theorem not_mem_one {a b : QuestionId} (h : a ≠ b) : a ∉ [b] := by
  intro hm
  cases hm with
  | head => exact h rfl
  | tail _ hm => cases hm

theorem not_mem_two {a b c : QuestionId} (h1 : a ≠ b) (h2 : a ≠ c) : a ∉ [b, c] := by
  intro hm
  cases hm with
  | head => exact h1 rfl
  | tail _ hm =>
    cases hm with
    | head => exact h2 rfl
    | tail _ hm => cases hm

/-- **The four children of a well-formed pair with distinct identifiers have
    four distinct identifiers** (Lemma 12.1, `child_id_inj`). -/
theorem four_ids_distinct (hwfx : x.WellFormed) (hwfy : y.WellFormed) (hxy : x.id ≠ y.id) :
    (childCore x false s p).id ≠ (childCore x true s p).id ∧
      (childCore x false s p).id ≠ (childCore y false s p).id ∧
      (childCore x false s p).id ≠ (childCore y true s p).id ∧
      (childCore x true s p).id ≠ (childCore y false s p).id ∧
      (childCore x true s p).id ≠ (childCore y true s p).id ∧
      (childCore y false s p).id ≠ (childCore y true s p).id := by
  rw [childCore_id x hwfx false, childCore_id x hwfx true, childCore_id y hwfy false,
    childCore_id y hwfy true]
  exact ⟨fun h => absurd (child_id_inj h).2 (by decide), fun h => hxy (child_id_inj h).1,
    fun h => hxy (child_id_inj h).1, fun h => hxy (child_id_inj h).1,
    fun h => hxy (child_id_inj h).1, fun h => absurd (child_id_inj h).2 (by decide)⟩

/-- Kept `[xL]` from the pair `[x, y]` (Step 1 or 2 toward `g₁`, Step 3's outer left). -/
theorem pair_next_xL (hwfx : x.WellFormed) (hwfy : y.WellFormed) (hxy : x.id ≠ y.id)
    (hpair : archive.filter (fun d => d.id ∈ active) = [x, y])
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive) :
    (advanceArchive archive active s p).filter (fun d => d.id ∈ [(childCore x false s p).id])
      = [childCore x false s p] := by
  have hP := root_proposals hpair
  have hsel : ∀ i ∈ [(childCore x false s p).id], i ∉ archIds archive := by
    intro i hi
    cases hi with
    | head => exact hfresh (x, false) (by rw [hP]; exact List.Mem.head _)
    | tail _ hi => cases hi
  rw [advanceArchive_filter_children hfresh hsel, hP]
  obtain ⟨d1, d2, d3, _, _, _⟩ := four_ids_distinct s p hwfx hwfy hxy
  have k1 : (childCore x false s p).id ∈ [(childCore x false s p).id] := List.Mem.head _
  have k2 : (childCore x true s p).id ∉ [(childCore x false s p).id] := not_mem_one d1.symm
  have k3 : (childCore y false s p).id ∉ [(childCore x false s p).id] := not_mem_one d2.symm
  have k4 : (childCore y true s p).id ∉ [(childCore x false s p).id] := not_mem_one d3.symm
  show List.filter (fun d => decide (d.id ∈ [(childCore x false s p).id]))
    [childCore x false s p, childCore x true s p, childCore y false s p, childCore y true s p] = _
  rw [idFilter_pos k1, idFilter_neg k2, idFilter_neg k3, idFilter_neg k4]
  rfl

/-- Kept `[yR]` from the pair `[x, y]` (toward `g₄`, Step 3's outer right). -/
theorem pair_next_yR (hwfx : x.WellFormed) (hwfy : y.WellFormed) (hxy : x.id ≠ y.id)
    (hpair : archive.filter (fun d => d.id ∈ active) = [x, y])
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive) :
    (advanceArchive archive active s p).filter (fun d => d.id ∈ [(childCore y true s p).id])
      = [childCore y true s p] := by
  have hP := root_proposals hpair
  have hsel : ∀ i ∈ [(childCore y true s p).id], i ∉ archIds archive := by
    intro i hi
    cases hi with
    | head => exact hfresh (y, true) (by
        rw [hP]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    | tail _ hi => cases hi
  rw [advanceArchive_filter_children hfresh hsel, hP]
  obtain ⟨_, _, d3, _, d5, d6⟩ := four_ids_distinct s p hwfx hwfy hxy
  have k1 : (childCore x false s p).id ∉ [(childCore y true s p).id] := not_mem_one d3
  have k2 : (childCore x true s p).id ∉ [(childCore y true s p).id] := not_mem_one d5
  have k3 : (childCore y false s p).id ∉ [(childCore y true s p).id] := not_mem_one d6
  have k4 : (childCore y true s p).id ∈ [(childCore y true s p).id] := List.Mem.head _
  show List.filter (fun d => decide (d.id ∈ [(childCore y true s p).id]))
    [childCore x false s p, childCore x true s p, childCore y false s p, childCore y true s p] = _
  rw [idFilter_neg k1, idFilter_neg k2, idFilter_neg k3, idFilter_pos k4]
  rfl

/-- Kept the cousin pair `[xL, yR]` (Step 2's tie at `n ≡ 3 (mod 21)`). -/
theorem pair_next_xLyR (hwfx : x.WellFormed) (hwfy : y.WellFormed) (hxy : x.id ≠ y.id)
    (hpair : archive.filter (fun d => d.id ∈ active) = [x, y])
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive) :
    (advanceArchive archive active s p).filter
        (fun d => d.id ∈ [(childCore x false s p).id, (childCore y true s p).id])
      = [childCore x false s p, childCore y true s p] := by
  have hP := root_proposals hpair
  have hsel : ∀ i ∈ [(childCore x false s p).id, (childCore y true s p).id],
      i ∉ archIds archive := by
    intro i hi
    cases hi with
    | head => exact hfresh (x, false) (by rw [hP]; exact List.Mem.head _)
    | tail _ hi =>
      cases hi with
      | head => exact hfresh (y, true) (by
          rw [hP]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      | tail _ hi => cases hi
  rw [advanceArchive_filter_children hfresh hsel, hP]
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := four_ids_distinct s p hwfx hwfy hxy
  have k1 : (childCore x false s p).id ∈ [(childCore x false s p).id, (childCore y true s p).id] :=
    List.Mem.head _
  have k2 : (childCore x true s p).id ∉ [(childCore x false s p).id, (childCore y true s p).id] :=
    not_mem_two d1.symm d5
  have k3 : (childCore y false s p).id ∉ [(childCore x false s p).id, (childCore y true s p).id] :=
    not_mem_two d2.symm d6
  have k4 : (childCore y true s p).id ∈ [(childCore x false s p).id, (childCore y true s p).id] :=
    List.Mem.tail _ (List.Mem.head _)
  show List.filter (fun d => decide (d.id ∈ [(childCore x false s p).id, (childCore y true s
    p).id]))
    [childCore x false s p, childCore x true s p, childCore y false s p, childCore y true s p] = _
  rw [idFilter_pos k1, idFilter_neg k2, idFilter_neg k3, idFilter_pos k4]
  rfl

/-- A singleton's proposals: both hands of its one core. -/
theorem single_proposals {g : Core} (hsing : archive.filter (fun d => d.id ∈ active) = [g]) :
    proposals archive active = [(g, false), (g, true)] := by
  unfold proposals
  rw [hsing]
  rfl

set_option linter.unusedVariables false in
/-- Kept both children of a singleton `[g]` (Corollary 8.11): the sibling pair. -/
theorem single_next_pair {g : Core} (hwf : g.WellFormed)
    (hsing : archive.filter (fun d => d.id ∈ active) = [g])
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive) :
    (advanceArchive archive active s p).filter
        (fun d => d.id ∈ [(childCore g false s p).id, (childCore g true s p).id])
      = [childCore g false s p, childCore g true s p] := by
  have hP := single_proposals hsing
  have hsel : ∀ i ∈ [(childCore g false s p).id, (childCore g true s p).id],
      i ∉ archIds archive := by
    intro i hi
    cases hi with
    | head => exact hfresh (g, false) (by rw [hP]; exact List.Mem.head _)
    | tail _ hi =>
      cases hi with
      | head => exact hfresh (g, true) (by rw [hP]; exact List.Mem.tail _ (List.Mem.head _))
      | tail _ hi => cases hi
  rw [advanceArchive_filter_children hfresh hsel, hP]
  have k1 : (childCore g false s p).id ∈ [(childCore g false s p).id, (childCore g true s p).id] :=
    List.Mem.head _
  have k2 : (childCore g true s p).id ∈ [(childCore g false s p).id, (childCore g true s p).id] :=
    List.Mem.tail _ (List.Mem.head _)
  show List.filter (fun d => decide (d.id ∈ [(childCore g false s p).id, (childCore g true s
    p).id]))
    [childCore g false s p, childCore g true s p] = _
  rw [idFilter_pos k1, idFilter_pos k2]
  rfl

/-- The sibling pair a singleton opens has distinct identifiers. -/
theorem single_children_distinct {g : Core} (hwf : g.WellFormed) :
    (childCore g false s p).id ≠ (childCore g true s p).id := by
  rw [childCore_id g hwf false, childCore_id g hwf true]
  exact fun h => absurd (child_id_inj h).2 (by decide)

/-! ### Corollary 8.11 on the carrier: a singleton opens its sibling pair -/

/-- The observer-`ε` address of any child, as an `IPres`. -/
def rI (w : Word) : IPres :=
  ⟨(r w).p, (r w).q, (walk_mid_pos empty w).1, (walk_mid_pos empty w).2⟩

theorem addrOf_child_some (c : Core) (g : Bool) :
    addrOf 1 (childCore c g s p) = some (rI (fullWord c ++ [g])) := by
  rw [addrOf_child]
  exact ofPres?_eq_some (walk_mid_pos empty _) rfl rfl

/-- **Corollary 8.11, on the tree.** From a singleton active family `[g]` at
    observer `ε`, the one-tick advance under `axiomSelect` keeps both children:
    two admitted occurrences tie exactly (Theorem 8.10), so nothing is rejected. -/
theorem single_step {g : Core} (hsing : archive.filter (fun d => d.id ∈ active) = [g]) :
    axiomSelect 1 s p (proposals archive active)
      = [(childCore g false s p).id, (childCore g true s p).id] := by
  have hC : admittedCores 1 s p (proposals archive active)
      = [childCore g false s p, childCore g true s p] := by
    unfold admittedCores
    rw [single_proposals hsing]
    show List.filter _ [childCore g false s p, childCore g true s p] = _
    refine List.filter_eq_self.mpr (fun d hd => ?_)
    rcases List.mem_cons.mp hd with rfl | hd
    · exact child_admitted g false s p
    rcases List.mem_cons.mp hd with rfl | hd
    · exact child_admitted g true s p
    · cases hd
  have hF : admittedFam 1 s p (proposals archive active)
      = [rI (fullWord g ++ [false]), rI (fullWord g ++ [true])] := by
    unfold admittedFam
    rw [hC, List.filterMap_cons_some (addrOf_child_some s p g false),
      List.filterMap_cons_some (addrOf_child_some s p g true)]
    rfl
  have heq := pair_coherence_equal (rI (fullWord g ++ [false])) (rI (fullWord g ++ [true]))
  have top : ∀ w, coherenceOf [rI (fullWord g ++ [false]), rI (fullWord g ++ [true])] w
      = coherenceOf [rI (fullWord g ++ [false]), rI (fullWord g ++ [true])]
          (rI (fullWord g ++ [false])) →
      [rI (fullWord g ++ [false]), rI (fullWord g ++ [true])].all (fun z =>
        decide (coherenceOf [rI (fullWord g ++ [false]), rI (fullWord g ++ [true])] z
          ≤ coherenceOf [rI (fullWord g ++ [false]), rI (fullWord g ++ [true])] w)) = true := by
    intro w hw
    refine List.all_eq_true.mpr (fun z hz => decide_eq_true ?_)
    rw [hw]
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_refl _
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_of_eq heq.symm
    · cases hz
  have pa := top (rI (fullWord g ++ [false])) rfl
  have pb := top (rI (fullWord g ++ [true])) heq.symm
  unfold axiomSelect
  simp only []
  rw [hC, hF]
  rw [List.filter_cons, List.filter_cons]
  rw [addrOf_child_some s p g false, addrOf_child_some s p g true]
  dsimp only
  simp only [pa, pb, decide_true, if_true]
  rfl

/-- **Corollary 8.11 on the tick carrier, chained.** A lawful carrier at `ε`
    whose active family is the singleton `[g]` advances to a carrier whose
    active family, read off its own archive, is the sibling pair
    `[gL, gR]`: the hypothesis every sibling step theorem takes. -/
theorem advanceCarrier_single_chain {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hlaw : Lawful X) (Δ : List (QuestionId × Aux)) (hsel : _) (hfresh : _) {g : Core}
    (hMO : X.observer.matrix = 1) (hwf : g.WellFormed)
    (hsing : X.archive.filter (fun d => d.id ∈ X.active) = [g]) :
    let X' := advanceCarrier X hlaw (axiomSelect X.observer.matrix s p) s p Δ hsel hfresh
    X'.active = [(childCore g false s p).id, (childCore g true s p).id] ∧
      X'.observer.matrix = 1 ∧
      X'.archive.filter (fun d => d.id ∈ X'.active)
        = [childCore g false s p, childCore g true s p] ∧
      (childCore g false s p).WellFormed ∧ (childCore g true s p).WellFormed ∧
      (childCore g false s p).id ≠ (childCore g true s p).id := by
  intro X'
  have hact : X'.active = [(childCore g false s p).id, (childCore g true s p).id] := by
    show axiomSelect X.observer.matrix s p (proposals X.archive X.active) = _
    rw [hMO]
    exact single_step s p hsing
  refine ⟨hact, hMO, ?_, childCore_wellFormed _ _ _ _, childCore_wellFormed _ _ _ _,
    single_children_distinct s p hwf⟩
  rw [hact]
  exact single_next_pair s p hwf hsing hfresh

/-! ### The general re-establishment: whatever Definition 8.1 keeps

One statement for every kept pattern at once. `axiomSelect` is by definition
`(admittedCores.filter keepPred).map Core.id`; at `ε` every child is admitted;
the children's identifiers are duplicate-free (`proposals_childCore_id_nodup`).
So the next archive, filtered by the identifiers `axiomSelect` returned, is the
admitted children `keepPred` kept, in proposal order, whatever the family. -/

/-- The predicate `axiomSelect` filters the admitted cores on. -/
def keepPred (MO : Mat2) (stratum : ℕ) (prov : Provenance) (props : List (Core × Bool)) :
    Core → Bool :=
  fun c =>
    match addrOf MO c with
    | some y => decide ((admittedFam MO stratum prov props).all (fun z =>
        coherenceOf (admittedFam MO stratum prov props) z
          ≤ coherenceOf (admittedFam MO stratum prov props) y))
    | none => false

theorem axiomSelect_eq (MO : Mat2) (stratum : ℕ) (prov : Provenance) (props : List (Core × Bool)) :
    axiomSelect MO stratum prov props
      = ((admittedCores MO stratum prov props).filter (keepPred MO stratum prov props)).map
          Core.id := rfl

/-- At observer `ε` every proposed child is admitted. -/
theorem admittedCores_eps (stratum : ℕ) (prov : Provenance) (props : List (Core × Bool)) :
    admittedCores 1 stratum prov props = props.map (fun q => childCore q.1 q.2 stratum prov) := by
  unfold admittedCores
  refine List.filter_eq_self.mpr (fun d hd => ?_)
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
  exact child_admitted q.1 q.2 stratum prov

/-- With duplicate-free identifiers, an identifier is among the kept ones exactly
    when its core was kept. By hand, choice-free. -/
theorem mem_ids_filter_iff (P : Core → Bool) :
    ∀ (L : List Core), (L.map Core.id).Nodup → ∀ d ∈ L,
      (d.id ∈ (L.filter P).map Core.id ↔ P d = true)
  | [], _, d, hd => by cases hd
  | a :: t, hnd, d, hd => by
    have hnd' := List.nodup_cons.mp hnd
    have sub : ∀ i, i ∈ (t.filter P).map Core.id → i ∈ t.map Core.id := by
      intro i hi
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
      exact List.mem_map_of_mem (List.mem_filter.mp he).1
    cases hd with
    | head =>
      cases hPa : P a with
      | true =>
        rw [List.filter_cons_of_pos (p := P) (a := a) hPa, List.map_cons]
        exact ⟨fun _ => rfl, fun _ => List.Mem.head _⟩
      | false =>
        rw [List.filter_cons_of_neg (p := P) (a := a) (by rw [hPa]; exact Bool.false_ne_true)]
        exact ⟨fun hm => absurd (sub _ hm) hnd'.1, fun h => absurd h Bool.false_ne_true⟩
    | tail _ hdt =>
      have ih := mem_ids_filter_iff P t hnd'.2 d hdt
      have hne : d.id ≠ a.id := fun h => hnd'.1 (h ▸ List.mem_map_of_mem hdt)
      cases hPa : P a with
      | true =>
        rw [List.filter_cons_of_pos (p := P) (a := a) hPa, List.map_cons]
        constructor
        · intro hm
          rcases List.mem_cons.mp hm with h | hm
          · exact absurd h hne
          · exact ih.mp hm
        · intro h
          exact List.Mem.tail _ (ih.mpr h)
      | false =>
        rw [List.filter_cons_of_neg (p := P) (a := a) (by rw [hPa]; exact Bool.false_ne_true)]
        exact ih

/-- **Filtering by the kept identifiers recovers the kept cores**, when
    identifiers are duplicate-free. -/
theorem filter_ids_of_filter (P : Core → Bool) :
    ∀ (L : List Core), (L.map Core.id).Nodup →
      L.filter (fun d => decide (d.id ∈ (L.filter P).map Core.id)) = L.filter P := by
  intro L hnd
  have key := mem_ids_filter_iff P L hnd
  generalize hK : (L.filter P).map Core.id = K at key
  clear hK
  induction L with
  | nil => rfl
  | cons a t ih =>
    have hnd' := List.nodup_cons.mp hnd
    have ih' := ih hnd'.2 (fun d hd => key d (List.Mem.tail _ hd))
    cases hPa : P a with
    | true =>
      rw [List.filter_cons_of_pos (p := fun d => decide (d.id ∈ K)) (a := a)
          (decide_eq_true ((key a (List.Mem.head _)).mpr hPa)),
        List.filter_cons_of_pos (p := P) (a := a) hPa, ih']
    | false =>
      rw [List.filter_cons_of_neg (p := fun d => decide (d.id ∈ K)) (a := a)
          (fun hm => absurd ((key a (List.Mem.head _)).mp (of_decide_eq_true hm))
            (by rw [hPa]; exact Bool.false_ne_true)),
        List.filter_cons_of_neg (p := P) (a := a) (by rw [hPa]; exact Bool.false_ne_true), ih']

/-- **Step 5's engine, for any active family at observer `ε`.** With a
    duplicate-free, well-formed archive and fresh proposals, the next archive
    filtered by what `axiomSelect` returned is exactly the children
    Definition 8.1 kept, in proposal order. -/
theorem next_filter_eq_kept {archive : List Core} {active : List QuestionId}
    (hnd : (archive.map Core.id).Nodup) (hwf : ∀ c ∈ archive, c.WellFormed)
    (hfresh : ∀ q ∈ proposals archive active, (childCore q.1 q.2 s p).id ∉ archIds archive) :
    (advanceArchive archive active s p).filter
        (fun d => d.id ∈ axiomSelect 1 s p (proposals archive active))
      = ((proposals archive active).map (fun q => childCore q.1 q.2 s p)).filter
          (keepPred 1 s p (proposals archive active)) := by
  have hsel : ∀ i ∈ axiomSelect 1 s p (proposals archive active), i ∉ archIds archive := by
    intro i hi
    rw [axiomSelect_eq, admittedCores_eps] at hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_filter.mp he).1
    exact hfresh q hq
  rw [advanceArchive_filter_children hfresh hsel, axiomSelect_eq, admittedCores_eps]
  apply filter_ids_of_filter
  rw [List.map_map]
  exact proposals_childCore_id_nodup hnd hwf s p

end chain

end RootChainCarrier
end Two
end RatioSpace
