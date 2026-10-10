/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S24.Lifecycle
import RatioSpace.ElementsII.S22.FaceVerification
/-!
  Elements II §25 — Interface to the Global Renewal-Shell Theorem.

  §23 recorded faces with incidence; §24 gave them a lifecycle. §25 exports the
  active family losslessly, passes it through a *declared* global attaching
  reception Γ, and computes a finite shell certificate on the received complex.
  The section's theorem (25.8) is negative: one committed lineage under the
  identity reception never passes the two-face edge test.

  **What is declared, not derived.** The reception Γ is declared data (its maps
  are parameters; only the identity reception is built here). The zero-defect
  valence `6` and the sphere total `12` are the book's own declared constants of
  the downstream triadic shell grammar (Definition 25.5, 25.6): they are named
  constants below, not derived from anything in this file.

  **Unordered edge keys without a quotient.** A received edge key must support
  `=`; `UEdge.same` is a relation. `canon` picks the endpoint order by an exact
  lexicographic comparison of the stable identifiers and `canon_eq_iff` proves
  `canon e = canon e' ↔ e.same e'`, so the key is exactly `Und` and nothing else.
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace RatioSpace
namespace Two
namespace Shell

open Mat2 Word Frame Pres RatioSpace SideExchange Advance Observer Shortcut Return Terminal Face Incidence Lifecycle

/-! ## Finite list tools (choice-free) -/

section Finite
variable {α : Type} [DecidableEq α]

/-- Duplicate-free image of a list. -/
def nub : List α → List α
  | [] => []
  | a :: l => if a ∈ l then nub l else a :: nub l

theorem mem_nub (x : α) : ∀ l : List α, x ∈ nub l ↔ x ∈ l
  | [] => Iff.rfl
  | a :: l => by
    change x ∈ (if a ∈ l then nub l else a :: nub l) ↔ x ∈ a :: l
    by_cases ha : a ∈ l
    · rw [if_pos ha, mem_nub x l, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun e => e ▸ ha) id⟩
    · rw [if_neg ha, List.mem_cons, List.mem_cons, mem_nub x l]

theorem nodup_nub : ∀ l : List α, (nub l).Nodup
  | [] => List.Pairwise.nil
  | a :: l => by
    change (if a ∈ l then nub l else a :: nub l).Nodup
    by_cases ha : a ∈ l
    · rw [if_pos ha]; exact nodup_nub l
    · rw [if_neg ha]; exact List.nodup_cons.mpr ⟨fun h => ha ((mem_nub a l).mp h), nodup_nub l⟩

/-- Multiplicity of `x` in a list. -/
def cnt (x : α) : List α → ℕ
  | [] => 0
  | a :: l => (if a = x then 1 else 0) + cnt x l

def sumN : List ℕ → ℕ
  | [] => 0
  | a :: l => a + sumN l

def sumZ : List ℤ → ℤ
  | [] => 0
  | a :: l => a + sumZ l

theorem cnt_of_not_mem (x : α) : ∀ l : List α, x ∉ l → cnt x l = 0
  | [], _ => rfl
  | a :: l, h => by
    have hax : a ≠ x := fun e => h (e ▸ List.Mem.head l)
    change (if a = x then 1 else 0) + cnt x l = 0
    rw [if_neg hax, cnt_of_not_mem x l (fun hm => h (List.Mem.tail a hm))]

theorem cnt_of_nodup_mem (x : α) : ∀ l : List α, l.Nodup → x ∈ l → cnt x l = 1
  | [], _, h => nomatch h
  | a :: l, hnd, h => by
    obtain ⟨hal, hl⟩ := List.nodup_cons.mp hnd
    change (if a = x then 1 else 0) + cnt x l = 1
    by_cases hax : a = x
    · subst hax; rw [if_pos rfl, cnt_of_not_mem a l hal]
    · rw [if_neg hax]
      have hxl : x ∈ l := by
        cases h with
        | head => exact absurd rfl hax
        | tail _ h' => exact h'
      rw [cnt_of_nodup_mem x l hl hxl]

set_option linter.unusedDecidableInType false in
theorem sumN_add (f g : α → ℕ) : ∀ L : List α,
    sumN (L.map fun v => f v + g v) = sumN (L.map f) + sumN (L.map g)
  | [] => rfl
  | a :: l => by
    change f a + g a + sumN (l.map fun v => f v + g v) = f a + sumN (l.map f) + (g a + sumN (l.map g))
    rw [sumN_add f g l]; omega

theorem sumN_indicator (a : α) : ∀ L : List α, sumN (L.map fun v => if a = v then 1 else 0) = cnt a L
  | [] => rfl
  | b :: l => by
    change (if a = b then 1 else 0) + sumN (l.map fun v => if a = v then 1 else 0) = (if b = a then 1 else 0) + cnt a l
    rw [sumN_indicator a l]
    by_cases h : a = b
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun e => h e.symm)]

/-- **Every occurrence is counted once**: summing multiplicities over the
    duplicate-free image gives the length. -/
theorem sum_cnt_nub : ∀ C : List α, sumN ((nub C).map fun v => cnt v C) = C.length
  | [] => rfl
  | a :: l => by
    have hsplit : ∀ L : List α,
        sumN (L.map fun v => cnt v (a :: l)) = cnt a L + sumN (L.map fun v => cnt v l) := by
      intro L
      change sumN (L.map fun v => (if a = v then 1 else 0) + cnt v l) = _
      rw [sumN_add, sumN_indicator]
    change sumN ((if a ∈ l then nub l else a :: nub l).map fun v => cnt v (a :: l)) = l.length + 1
    by_cases ha : a ∈ l
    · rw [if_pos ha, hsplit, cnt_of_nodup_mem a _ (nodup_nub l) ((mem_nub a l).mpr ha), sum_cnt_nub l]
      omega
    · rw [if_neg ha]
      change cnt a (a :: l) + sumN ((nub l).map fun v => cnt v (a :: l)) = l.length + 1
      rw [hsplit, cnt_of_not_mem a _ (fun h => ha ((mem_nub a l).mp h)), sum_cnt_nub l]
      change (if a = a then 1 else 0) + cnt a l + (0 + l.length) = l.length + 1
      rw [if_pos rfl, cnt_of_not_mem a l ha]; omega

theorem sumZ_six_sub (C : List α) : ∀ L : List α,
    sumZ (L.map fun v => (6 : ℤ) - (cnt v C : ℤ)) = 6 * (L.length : ℤ) - (sumN (L.map fun v => cnt v C) : ℤ)
  | [] => rfl
  | a :: l => by
    change 6 - (cnt a C : ℤ) + sumZ (l.map fun v => (6 : ℤ) - (cnt v C : ℤ)) =
      6 * ((l.length + 1 : ℕ) : ℤ) - ((cnt a C + sumN (l.map fun v => cnt v C) : ℕ) : ℤ)
    rw [sumZ_six_sub C l]; omega

omit [DecidableEq α] in
/-- `List.Nodup` of an image separates the preimages it contains. -/
theorem eq_of_map_nodup {β : Type} (k : β → α) : ∀ l : List β, (l.map k).Nodup →
    ∀ a ∈ l, ∀ b ∈ l, k a = k b → a = b
  | [], _, a, ha, _, _, _ => nomatch ha
  | c :: t, hnd, a, ha, b, hb, hk => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hc, ht⟩ := hnd
    cases ha with
    | head =>
      cases hb with
      | head => rfl
      | tail _ hb' => exact absurd (hk ▸ List.mem_map_of_mem hb') hc
    | tail _ ha' =>
      cases hb with
      | head => exact absurd (hk.symm ▸ List.mem_map_of_mem ha') hc
      | tail _ hb' => exact eq_of_map_nodup k t ht a ha' b hb' hk

theorem find?_of_unique {β : Type} (p : β → Bool) (f : β) :
    ∀ l : List β, f ∈ l → p f = true → (∀ g ∈ l, p g = true → g = f) → l.find? p = some f
  | [], h, _, _ => nomatch h
  | c :: t, hf, hp, hu => by
    cases hpc : p c
    · rw [List.find?_cons_of_neg (by rw [hpc]; exact Bool.false_ne_true)]
      have hft : f ∈ t := by
        cases hf with
        | head => rw [hp] at hpc; exact nomatch hpc
        | tail _ h' => exact h'
      exact find?_of_unique p f t hft hp (fun g hg => hu g (List.Mem.tail c hg))
    · rw [List.find?_cons_of_pos hpc, hu c (List.Mem.head t) hpc]

theorem countP_le_of {β : Type} (p q : β → Bool) : ∀ l : List β,
    (∀ x ∈ l, p x = true → q x = true) → l.countP p ≤ l.countP q
  | [], _ => Nat.le_refl 0
  | a :: l, h => by
    have ih := countP_le_of p q l (fun x hx => h x (List.Mem.tail a hx))
    cases hp : p a <;> cases hq : q a
    · rw [List.countP_cons_of_neg (by rw [hp]; exact Bool.false_ne_true),
        List.countP_cons_of_neg (by rw [hq]; exact Bool.false_ne_true)]; exact ih
    · rw [List.countP_cons_of_neg (by rw [hp]; exact Bool.false_ne_true), List.countP_cons_of_pos hq]; omega
    · rw [h a (List.Mem.head l) hp] at hq; exact nomatch hq
    · rw [List.countP_cons_of_pos hp, List.countP_cons_of_pos hq]; omega

theorem countP_lt_of {β : Type} (p q : β → Bool) : ∀ l : List β,
    (∀ x ∈ l, p x = true → q x = true) → ∀ y ∈ l, p y = false → q y = true → l.countP p < l.countP q
  | [], _, _, hy, _, _ => nomatch hy
  | a :: l, h, y, hy, hpy, hqy => by
    have hle := countP_le_of p q l (fun x hx => h x (List.Mem.tail a hx))
    cases hy with
    | head =>
      rw [List.countP_cons_of_neg (by rw [hpy]; exact Bool.false_ne_true), List.countP_cons_of_pos hqy]; omega
    | tail _ hy' =>
      have ih := countP_lt_of p q l (fun x hx => h x (List.Mem.tail a hx)) y hy' hpy hqy
      cases hp : p a <;> cases hq : q a
      · rw [List.countP_cons_of_neg (by rw [hp]; exact Bool.false_ne_true),
          List.countP_cons_of_neg (by rw [hq]; exact Bool.false_ne_true)]; exact ih
      · rw [List.countP_cons_of_neg (by rw [hp]; exact Bool.false_ne_true), List.countP_cons_of_pos hq]; omega
      · rw [h a (List.Mem.head l) hp] at hq; exact nomatch hq
      · rw [List.countP_cons_of_pos hp, List.countP_cons_of_pos hq]; omega

theorem countP_pos_of {β : Type} (p : β → Bool) : ∀ l : List β, ∀ y ∈ l, p y = true → 0 < l.countP p
  | [], _, hy, _ => nomatch hy
  | a :: l, y, hy, hpy => by
    cases hp : p a
    · rw [List.countP_cons_of_neg (by rw [hp]; exact Bool.false_ne_true)]
      cases hy with
      | head => rw [hpy] at hp; exact nomatch hp
      | tail _ hy' => exact countP_pos_of p l y hy' hpy
    · rw [List.countP_cons_of_pos hp]; omega

theorem exists_of_all_false {β : Type} (p : β → Bool) : ∀ l : List β, l.all p = false → ∃ x ∈ l, p x = false
  | [], h => nomatch h
  | a :: l, h => by
    cases hp : p a
    · exact ⟨a, List.Mem.head l, hp⟩
    · rw [List.all_cons, hp, Bool.true_and] at h
      obtain ⟨x, hx, hpx⟩ := exists_of_all_false p l h
      exact ⟨x, List.Mem.tail a hx, hpx⟩

end Finite

/-! ## Finite graphs: an exact connectedness decision

    Used twice by the certificate: for the incidence graph `𝖡(K)` and for each
    vertex link `Lk(v)`. The decision is a closure iterated `|nodes|` times; the
    theorem `connB_iff` proves it agrees with the propositional definition (one
    connected component: nonempty, every two nodes joined by a walk through
    nodes). -/

structure Graph (α : Type) where
  nodes : List α
  edges : List (α × α)

namespace Graph

variable {α : Type} [DecidableEq α] (g : Graph α)

/-- Adjacency, undirected: some recorded graph edge joins the two nodes. -/
def adj (a b : α) : Bool :=
  g.edges.any fun p => (decide (p.1 = a) && decide (p.2 = b)) || (decide (p.1 = b) && decide (p.2 = a))

theorem adj_symm (a b : α) : g.adj a b = g.adj b a := by
  unfold adj; congr 1; funext p; rw [Bool.or_comm]

/-- A walk through nodes of the graph. -/
inductive Walk : α → α → Prop
  | refl (a : α) : Walk a a
  | step {a b c : α} : Walk a b → c ∈ g.nodes → g.adj b c = true → Walk a c

/-- **One connected component.** -/
def Connected : Prop := g.nodes ≠ [] ∧ ∀ x ∈ g.nodes, ∀ y ∈ g.nodes, g.Walk x y

variable {g}

theorem Walk.trans {a b c : α} (w1 : g.Walk a b) (w2 : g.Walk b c) : g.Walk a c := by
  induction w2 with
  | refl => exact w1
  | step _ hc hadj ih => exact Walk.step ih hc hadj

theorem Walk.end_mem {a b : α} (ha : a ∈ g.nodes) (w : g.Walk a b) : b ∈ g.nodes := by
  induction w with
  | refl => exact ha
  | step _ hc _ _ => exact hc

theorem Walk.symm {a b : α} (ha : a ∈ g.nodes) (w : g.Walk a b) : g.Walk b a := by
  induction w with
  | refl => exact Walk.refl _
  | @step b0 c w0 _ hadj ih =>
    have hb0 : b0 ∈ g.nodes := w0.end_mem ha
    exact Walk.trans (Walk.step (Walk.refl c) hb0 (by rw [adj_symm]; exact hadj)) ih

variable (g)

def grow (R : List α) : List α :=
  g.nodes.filter fun x => decide (x ∈ R) || R.any fun y => g.adj y x

def reach (r : α) : ℕ → List α
  | 0 => g.nodes.filter fun x => decide (x = r)
  | k + 1 => g.grow (reach r k)

/-- **The decision.** -/
def connB : Bool :=
  match g.nodes with
  | [] => false
  | r :: _ => g.nodes.all fun x => decide (x ∈ g.reach r g.nodes.length)

variable {g}

theorem mem_grow (R : List α) (x : α) :
    x ∈ g.grow R ↔ x ∈ g.nodes ∧ (x ∈ R ∨ ∃ y ∈ R, g.adj y x = true) := by
  unfold grow
  rw [List.mem_filter, Bool.or_eq_true, decide_eq_true_iff, List.any_eq_true]

theorem reach_sub (r : α) : ∀ k, ∀ x ∈ g.reach r k, x ∈ g.nodes
  | 0, _, hx => (List.mem_filter.mp hx).1
  | _ + 1, x, hx => ((mem_grow _ x).mp hx).1

theorem reach_sound (r : α) : ∀ k, ∀ x ∈ g.reach r k, g.Walk r x
  | 0, x, hx => by
    have := of_decide_eq_true (List.mem_filter.mp hx).2
    subst this; exact Walk.refl x
  | k + 1, x, hx => by
    obtain ⟨hn, hR | ⟨y, hy, hadj⟩⟩ := (mem_grow _ x).mp hx
    · exact reach_sound r k x hR
    · exact Walk.step (reach_sound r k y hy) hn hadj

theorem reach_mono (r : α) (k : ℕ) (x : α) (hx : x ∈ g.reach r k) : x ∈ g.reach r (k + 1) :=
  (mem_grow _ x).mpr ⟨reach_sub r k x hx, Or.inl hx⟩

theorem reach_mono_le (r : α) (j : ℕ) (x : α) (hx : x ∈ g.reach r j) : ∀ m, x ∈ g.reach r (j + m)
  | 0 => hx
  | m + 1 => reach_mono r (j + m) x (reach_mono_le r j x hx m)

def Closed (g : Graph α) (r : α) (k : ℕ) : Prop := ∀ x, x ∈ g.reach r (k + 1) → x ∈ g.reach r k

theorem closed_complete (r : α) (hr : r ∈ g.nodes) (k : ℕ) (hc : g.Closed r k) :
    ∀ x, g.Walk r x → x ∈ g.reach r k := by
  intro x w
  induction w with
  | refl =>
    have h0 : r ∈ g.reach r 0 := List.mem_filter.mpr ⟨hr, decide_eq_true rfl⟩
    have := reach_mono_le r 0 r h0 k
    rwa [Nat.zero_add] at this
  | step _ hcn hadj ih => exact hc _ ((mem_grow _ _).mpr ⟨hcn, Or.inr ⟨_, ih, hadj⟩⟩)

theorem closed_or_count (r : α) (hr : r ∈ g.nodes) : ∀ k,
    (∃ j, j ≤ k ∧ g.Closed r j) ∨ k + 1 ≤ g.nodes.countP (fun x => decide (x ∈ g.reach r k))
  | 0 => by
    right
    exact countP_pos_of _ g.nodes r hr (decide_eq_true (List.mem_filter.mpr ⟨hr, decide_eq_true rfl⟩))
  | k + 1 => by
    rcases closed_or_count r hr k with ⟨j, hj, hc⟩ | hcount
    · exact Or.inl ⟨j, Nat.le_succ_of_le hj, hc⟩
    · cases hb : g.nodes.all (fun x => !(decide (x ∈ g.reach r (k + 1))) || decide (x ∈ g.reach r k))
      · right
        obtain ⟨y, hy, hpy⟩ := exists_of_all_false _ _ hb
        have h1 : decide (y ∈ g.reach r (k + 1)) = true := by
          cases h : decide (y ∈ g.reach r (k + 1))
          · rw [h] at hpy; exact nomatch hpy
          · rfl
        have h2 : decide (y ∈ g.reach r k) = false := by
          cases h : decide (y ∈ g.reach r k)
          · rfl
          · rw [h, Bool.or_true] at hpy; exact nomatch hpy
        have hlt := countP_lt_of (fun x => decide (x ∈ g.reach r k)) (fun x => decide (x ∈ g.reach r (k + 1)))
          g.nodes (fun x _ hx => decide_eq_true (reach_mono r k x (of_decide_eq_true hx))) y hy h2 h1
        omega
      · left
        refine ⟨k, Nat.le_succ k, fun x hx => ?_⟩
        have := List.all_eq_true.mp hb x (reach_sub r (k + 1) x hx)
        rw [decide_eq_true hx, Bool.not_true, Bool.false_or] at this
        exact of_decide_eq_true this

/-- **The connectedness decision is exact.** -/
theorem connB_iff : g.connB = true ↔ g.Connected := by
  cases hn : g.nodes with
  | nil =>
    have hb : g.connB = false := by unfold connB; rw [hn]
    rw [hb]
    exact ⟨(fun h => nomatch h), fun h => absurd hn h.1⟩
  | cons r t =>
    have hr : r ∈ g.nodes := hn ▸ List.Mem.head t
    have hb : g.connB = g.nodes.all (fun x => decide (x ∈ g.reach r g.nodes.length)) := by
      unfold connB; rw [hn]
    rw [hb]
    constructor
    · intro h
      have hw : ∀ x ∈ g.nodes, g.Walk r x := fun x hx =>
        reach_sound r _ x (of_decide_eq_true (List.all_eq_true.mp h x hx))
      refine ⟨fun h0 => List.cons_ne_nil r t (hn.symm.trans h0), fun x hx y hy => ?_⟩
      exact Walk.trans ((hw x hx).symm hr) (hw y hy)
    · rintro ⟨-, hc⟩
      apply List.all_eq_true.mpr
      intro x hx
      apply decide_eq_true
      rcases closed_or_count r hr g.nodes.length with ⟨j, hj, hcl⟩ | hcount
      · have hxj := closed_complete r hr j hcl x (hc r hr x hx)
        have := reach_mono_le r j x hxj (g.nodes.length - j)
        rwa [Nat.add_sub_of_le hj] at this
      · exact absurd (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hcount) (Nat.not_lt.mpr (List.countP_le_length))

theorem not_isEmpty_iff {β : Type} (l : List β) : (!l.isEmpty) = true ↔ l ≠ [] := by
  cases l with
  | nil => exact ⟨(fun h => nomatch h), fun h => absurd rfl h⟩
  | cons a l => exact ⟨fun _ => List.cons_ne_nil a l, fun _ => rfl⟩

variable (g)

/-- Degree with multiplicity: a loop counts twice. -/
def deg (x : α) : ℕ := g.edges.countP (fun p => decide (p.1 = x)) + g.edges.countP (fun p => decide (p.2 = x))

/-- **One finite cycle**, as Proposition 25.7 tests it: a nonempty connected
    multigraph every node of which has degree two. -/
def IsCycle : Prop := g.edges ≠ [] ∧ g.Connected ∧ ∀ x ∈ g.nodes, g.deg x = 2

def cycleB : Bool := !g.edges.isEmpty && g.connB && g.nodes.all fun x => decide (g.deg x = 2)

theorem cycleB_iff : g.cycleB = true ↔ g.IsCycle := by
  unfold cycleB IsCycle
  rw [Bool.and_eq_true, Bool.and_eq_true, connB_iff, List.all_eq_true, not_isEmpty_iff]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, fun x hx => of_decide_eq_true (h3 x hx)⟩,
    fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, fun x hx => decide_eq_true (h3 x hx)⟩⟩

end Graph

/-! ## Definition 25.5 — Received triadic interface complex -/

/-- A received oriented edge: its undirected received key `Und(q_E e⃗)` and its
    received endpoints. -/
structure ROEdge (V E : Type) where
  key : E
  src : V
  dst : V
deriving DecidableEq

def ROEdge.rev {V E : Type} (o : ROEdge V E) : ROEdge V E := ⟨o.key, o.dst, o.src⟩

/-- A received face: its received key, ordered vertices, ordered boundary. -/
structure TFace (V E F : Type) where
  key : F
  v0 : V
  v1 : V
  v2 : V
  b0 : ROEdge V E
  b1 : ROEdge V E
  b2 : ROEdge V E

/-- **Definition 25.5.** `K = (V_Γ, E_Γ, F_Γ, Bd_Γ, Inc_V, Inc_E)`, all read off the
    received face positions (the source ledger `Src_Γ` is carried by the
    reception, Definition 25.4). -/
structure Cx (V E F : Type) where
  faces : List (TFace V E F)

section Complex
variable {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F]

def TFace.verts (f : TFace V E F) : List V := [f.v0, f.v1, f.v2]
def TFace.bd (f : TFace V E F) : List (ROEdge V E) := [f.b0, f.b1, f.b2]
def TFace.bkeys (f : TFace V E F) : List E := f.bd.map ROEdge.key

variable (K : Cx V E F)

/-- Every face corner, with multiplicity by face-boundary position. -/
def Cx.corners : List V := K.faces.flatMap TFace.verts
def Cx.VG : List V := nub K.corners
def Cx.EG : List E := nub (K.faces.flatMap TFace.bkeys)
def Cx.FG : List F := nub (K.faces.map TFace.key)

/-- `Inc_{V,Γ}(v)`, by received face positions. -/
def Cx.incV (v : V) : List F := (K.faces.filter fun f => decide (v ∈ f.verts)).map TFace.key

/-- `Inc_{E,Γ}(e)`, by received face positions. -/
def Cx.incE (e : E) : List F := (K.faces.filter fun f => f.bkeys.any fun k => decide (k = e)).map TFace.key

/-- `Bd_Γ`. -/
def Cx.bdG (k : F) : Option (ROEdge V E × ROEdge V E × ROEdge V E) :=
  (K.faces.find? fun f => decide (f.key = k)).map fun f => (f.b0, f.b1, f.b2)

/-- `d_Γ(v)`: incident triadic face corners, with multiplicity. -/
def Cx.d (v : V) : ℕ := cnt v K.corners

/-- **The book's declared zero-defect valence** of the downstream triadic shell
    grammar (Definition 25.5). Declared, not derived. -/
def zeroDefectValence : ℤ := 6

/-- **The book's declared sphere-shell total** (Definition 25.6). Declared, not derived. -/
def sphereDefect : ℤ := 12

/-- `δ_Γ(v) = 6 − d_Γ(v)`. -/
def Cx.delta (v : V) : ℤ := zeroDefectValence - (K.d v : ℤ)

/-- `D_Γ = Σ_{v ∈ V_Γ} δ_Γ(v)`. -/
def Cx.D : ℤ := sumZ (K.VG.map K.delta)

set_option linter.unusedDecidableInType false in
theorem corners_length : ∀ fs : List (TFace V E F),
    (fs.flatMap TFace.verts).length = 3 * fs.length
  | [] => rfl
  | f :: fs => by
    rw [List.flatMap_cons, List.length_append, corners_length fs, List.length_cons]
    change 3 + 3 * fs.length = 3 * (fs.length + 1)
    omega

set_option linter.unusedDecidableInType false in
/-- **The total defect is an exact integer count of positions**:
    `D_Γ = 6·|V_Γ| − 3·(number of face positions)`. No angle or metric enters. -/
theorem D_eq :
    K.D = 6 * (K.VG.length : ℤ) - 3 * (K.faces.length : ℤ) := by
  unfold Cx.D Cx.delta Cx.d zeroDefectValence Cx.VG
  rw [sumZ_six_sub, sum_cnt_nub]
  unfold Cx.corners
  rw [corners_length]
  omega

/-! ## Definition 25.6 — Exact shell certificate -/

/-- `c_nonempty`. -/
def Cx.cNonempty : Bool := !K.faces.isEmpty

set_option linter.unusedDecidableInType false in
theorem cNonempty_iff :
    K.cNonempty = true ↔ K.faces ≠ [] := Graph.not_isEmpty_iff _

/-- The incidence graph `𝖡(K)`: nodes are received vertices, edges and faces;
    graph edges record boundary incidence (face–edge) and endpoint incidence
    (edge–vertex). -/
inductive Node (V E F : Type) where
  | v : V → Node V E F
  | e : E → Node V E F
  | f : F → Node V E F
deriving DecidableEq

def Cx.B : Graph (Node V E F) where
  nodes := K.VG.map Node.v ++ K.EG.map Node.e ++ K.FG.map Node.f
  edges := K.faces.flatMap fun f => f.bd.flatMap fun o =>
    [(Node.f f.key, Node.e o.key), (Node.e o.key, Node.v o.src), (Node.e o.key, Node.v o.dst)]

/-- `c_conn`. -/
def Cx.cConn : Bool := K.B.connB

theorem cConn_iff : K.cConn = true ↔ K.B.Connected := Graph.connB_iff

/-- `c_2E`. -/
def Cx.c2E : Bool := K.EG.all fun e => decide ((K.incE e).length = 2)

set_option linter.unusedDecidableInType false in
theorem c2E_iff :
    K.c2E = true ↔ ∀ e ∈ K.EG, (K.incE e).length = 2 := by
  unfold Cx.c2E
  rw [List.all_eq_true]
  exact ⟨fun h e he => of_decide_eq_true (h e he), fun h e he => decide_eq_true (h e he)⟩

/-- The link corners of `f` at `v`: one link edge between the two other boundary
    positions of each corner at `v`, multiplicity retained. -/
def TFace.linkAt (f : TFace V E F) (v : V) : List (V × V) :=
  (if f.v0 = v then [(f.v1, f.v2)] else []) ++ (if f.v1 = v then [(f.v2, f.v0)] else []) ++
    (if f.v2 = v then [(f.v0, f.v1)] else [])

/-- `Lk_Γ(v)`. -/
def Cx.Lk (v : V) : Graph V where
  edges := K.faces.flatMap fun f => f.linkAt v
  nodes := nub ((K.faces.flatMap fun f => f.linkAt v).flatMap fun p => [p.1, p.2])

/-- `c_link`. -/
def Cx.cLink : Bool := K.VG.all fun v => (K.Lk v).cycleB

set_option linter.unusedDecidableInType false in
theorem cLink_iff :
    K.cLink = true ↔ ∀ v ∈ K.VG, (K.Lk v).IsCycle := by
  unfold Cx.cLink
  rw [List.all_eq_true]
  exact ⟨fun h v hv => (Graph.cycleB_iff _).mp (h v hv), fun h v hv => (Graph.cycleB_iff _).mpr (h v hv)⟩

/-- Boundary occurrences tagged by their received face key (a face position under
    face-key separation, Definition 25.4 (5)). -/
def Cx.occs : List (F × ROEdge V E) := K.faces.flatMap fun f => f.bd.map fun o => (f.key, o)

/-- The book's orientation condition: two distinct face positions sharing an
    edge traverse it in opposite directions. -/
def Cx.OriCompat : Prop :=
  ∀ a ∈ K.occs, ∀ b ∈ K.occs, a.1 ≠ b.1 → a.2.key = b.2.key → a.2.src = b.2.dst ∧ a.2.dst = b.2.src

/-- `c_ori`. -/
def Cx.cOri : Bool :=
  K.occs.all fun a => K.occs.all fun b =>
    decide (a.1 = b.1) || decide (a.2.key ≠ b.2.key) || decide (a.2.src = b.2.dst ∧ a.2.dst = b.2.src)

theorem cOri_iff : K.cOri = true ↔ K.OriCompat := by
  unfold Cx.cOri Cx.OriCompat
  constructor
  · intro h a ha b hb hne hk
    have := List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb
    rw [Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff] at this
    rcases this with (h1 | h2) | h3
    · exact absurd h1 hne
    · exact absurd hk h2
    · exact h3
  · intro h
    apply List.all_eq_true.mpr
    intro a ha
    apply List.all_eq_true.mpr
    intro b hb
    rw [Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
    by_cases h1 : a.1 = b.1
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : a.2.key = b.2.key
      · exact Or.inr (h a ha b hb h1 h2)
      · exact Or.inl (Or.inr h2)

/-- `𝐜_sh ∈ {0,1}⁵`. -/
structure CSh where
  nonempty : Bool
  conn : Bool
  twoE : Bool
  link : Bool
  ori : Bool
deriving DecidableEq

def Cx.csh : CSh := ⟨K.cNonempty, K.cConn, K.c2E, K.cLink, K.cOri⟩

def allOnes : CSh := ⟨true, true, true, true, true⟩

/-- **Definition 25.6.** The complete certificate. The source ledger `Src_Γ` is
    passed in from the reception. -/
structure ShellCert (V F S : Type) where
  c : CSh
  nV : ℕ
  nE : ℕ
  nF : ℕ
  d : List (V × ℕ)
  delta : List (V × ℤ)
  D : ℤ
  src : S

def Cx.cert {S : Type} (src : S) : ShellCert V F S :=
  ⟨K.csh, K.VG.length, K.EG.length, K.FG.length, K.VG.map (fun v => (v, K.d v)),
    K.VG.map (fun v => (v, K.delta v)), K.D, src⟩

/-- A **closed orientable triadic shell input**. -/
def Cx.ClosedShellInput : Prop := K.csh = allOnes

/-- A **sphere-shell input**. -/
def Cx.SphereShellInput : Prop := K.ClosedShellInput ∧ K.D = sphereDefect

instance : Decidable K.ClosedShellInput := by unfold Cx.ClosedShellInput; exact inferInstance
instance : Decidable K.SphereShellInput := by unfold Cx.SphereShellInput; exact inferInstance

/-! ## Proposition 25.7 — The shell certificate is finite and exact -/

/-- **Proposition 25.7.** Each Boolean entry agrees with the book's proposition,
    the defect total is an exact integer count, and both shell-input typings are
    decidable. -/
theorem closed_iff : K.ClosedShellInput ↔
    K.faces ≠ [] ∧ K.B.Connected ∧ (∀ e ∈ K.EG, (K.incE e).length = 2) ∧
      (∀ v ∈ K.VG, (K.Lk v).IsCycle) ∧ K.OriCompat := by
  unfold Cx.ClosedShellInput Cx.csh allOnes
  rw [CSh.mk.injEq, ← cNonempty_iff, ← cConn_iff, ← c2E_iff, ← cLink_iff, ← cOri_iff]

theorem cert_exact {S : Type} (src : S) :
    (K.cNonempty = true ↔ K.faces ≠ []) ∧ (K.cConn = true ↔ K.B.Connected) ∧
    (K.c2E = true ↔ ∀ e ∈ K.EG, (K.incE e).length = 2) ∧
    (K.cLink = true ↔ ∀ v ∈ K.VG, (K.Lk v).IsCycle) ∧ (K.cOri = true ↔ K.OriCompat) ∧
    (K.cert src).D = 6 * ((K.cert src).nV : ℤ) - 3 * (K.faces.length : ℤ) ∧
    (K.ClosedShellInput ↔ (K.cert src).c = allOnes) :=
  ⟨cNonempty_iff K, cConn_iff K, c2E_iff K, cLink_iff K, cOri_iff K, D_eq K, Iff.rfl⟩

end Complex

/-! ## Unordered stable edge keys (no quotient) -/

def bleW : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: m => (!a && b) || (decide (a = b) && bleW l m)

theorem bleW_total : ∀ l m : List Bool, bleW l m = true ∨ bleW m l = true
  | [], _ => Or.inl rfl
  | _ :: _, [] => Or.inr rfl
  | a :: l, b :: m => by
    cases a <;> cases b
    · exact bleW_total l m
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact bleW_total l m

theorem bleW_antisymm : ∀ l m : List Bool, bleW l m = true → bleW m l = true → l = m
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | a :: l, b :: m, h1, h2 => by
    cases a <;> cases b
    · exact congrArg (false :: ·) (bleW_antisymm l m h1 h2)
    · exact nomatch h2
    · exact nomatch h1
    · exact congrArg (true :: ·) (bleW_antisymm l m h1 h2)

def natLex (a b : ℕ) (r : Bool) : Bool := decide (a < b) || (decide (a = b) && r)

theorem natLex_total (a b : ℕ) (r r' : Bool) (h : r = true ∨ r' = true) :
    natLex a b r = true ∨ natLex b a r' = true := by
  unfold natLex
  rcases Nat.lt_trichotomy a b with h1 | h1 | h1
  · left; rw [decide_eq_true h1]; rfl
  · subst h1; rw [decide_eq_false (Nat.lt_irrefl a), decide_eq_true rfl]; exact h
  · right; rw [decide_eq_true h1]; rfl

theorem natLex_antisymm (a b : ℕ) (r r' : Bool) (h1 : natLex a b r = true) (h2 : natLex b a r' = true) :
    a = b ∧ r = true ∧ r' = true := by
  unfold natLex at h1 h2
  rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h1 h2
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exact ⟨e1, h1, h2⟩

/-- Exact lexicographic comparison of stable identifiers. -/
def qle (x y : QuestionId) : Bool :=
  natLex x.cycle y.cycle (natLex x.qid y.qid (natLex x.seed y.seed (bleW x.rel y.rel)))

theorem qle_total (x y : QuestionId) : qle x y = true ∨ qle y x = true :=
  natLex_total _ _ _ _ (natLex_total _ _ _ _ (natLex_total _ _ _ _ (bleW_total _ _)))

theorem qle_antisymm (x y : QuestionId) (h1 : qle x y = true) (h2 : qle y x = true) : x = y := by
  obtain ⟨c, h1, h2⟩ := natLex_antisymm _ _ _ _ h1 h2
  obtain ⟨q, h1, h2⟩ := natLex_antisymm _ _ _ _ h1 h2
  obtain ⟨s, h1, h2⟩ := natLex_antisymm _ _ _ _ h1 h2
  have r := bleW_antisymm _ _ h1 h2
  cases x; cases y
  simp only [QuestionId.mk.injEq]
  exact ⟨c, q, s, r⟩

deriving instance DecidableEq for UEdge

/-- The normal form of an undirected key: same type, same endpoint set, endpoints
    in `qle` order. -/
def canon (e : UEdge) : UEdge := if qle e.a e.b = true then e else ⟨e.ty, e.b, e.a⟩

theorem same_trans {e e' e'' : UEdge} (h1 : e.same e') (h2 : e'.same e'') : e.same e'' := by
  obtain ⟨t1, (⟨a1, b1⟩ | ⟨a1, b1⟩)⟩ := h1 <;> obtain ⟨t2, (⟨a2, b2⟩ | ⟨a2, b2⟩)⟩ := h2
  · exact ⟨t1.trans t2, Or.inl ⟨a1.trans a2, b1.trans b2⟩⟩
  · exact ⟨t1.trans t2, Or.inr ⟨a1.trans a2, b1.trans b2⟩⟩
  · exact ⟨t1.trans t2, Or.inr ⟨a1.trans b2, b1.trans a2⟩⟩
  · exact ⟨t1.trans t2, Or.inl ⟨a1.trans b2, b1.trans a2⟩⟩

theorem canon_same (e : UEdge) : (canon e).same e := by
  unfold canon
  split
  · exact same_refl e
  · exact ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩

/-- **The received undirected key is exactly `Und`.** -/
theorem canon_eq_iff (e e' : UEdge) : canon e = canon e' ↔ e.same e' := by
  constructor
  · intro h
    have h1 := UEdge.same_symm (canon_same e)
    rw [h] at h1
    exact same_trans h1 (canon_same e')
  · rintro ⟨ht, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩
    · obtain ⟨t, a, b⟩ := e; obtain ⟨t', a', b'⟩ := e'
      simp only at ht ha hb; subst ht ha hb; rfl
    · obtain ⟨t, a, b⟩ := e; obtain ⟨t', a', b'⟩ := e'
      simp only at ht ha hb; subst ht ha hb
      unfold canon
      cases hab : qle a b <;> cases hba : qle b a
      · rcases qle_total a b with h | h
        · rw [hab] at h; exact nomatch h
        · rw [hba] at h; exact nomatch h
      · simp only [Bool.false_eq_true, ite_false, ite_true]
      · simp only [Bool.false_eq_true, ite_false, ite_true]
      · have := qle_antisymm a b hab hba
        subst this; rfl

theorem canon_swap (t : EdgeType) (a b : QuestionId) : canon ⟨t, b, a⟩ = canon ⟨t, a, b⟩ :=
  (canon_eq_iff _ _).mpr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩

/-! ## Definition 25.4 — Declared global attaching reception -/

/-- An exported prequotient face: key, ordered vertices, ordered oriented
    boundary, and the whole retained record. -/
structure PFace (Vp Ep Fp R : Type) where
  key : Fp
  v0 : Vp
  v1 : Vp
  v2 : Vp
  e0 : Ep
  e1 : Ep
  e2 : Ep
  record : R

def PFace.edges {Vp Ep Fp R : Type} (f : PFace Vp Ep Fp R) : List Ep := [f.e0, f.e1, f.e2]

/-- Endpoints and reversal of prequotient oriented edges. -/
structure PreEdges (Vp Ep : Type) where
  src : Ep → Vp
  dst : Ep → Vp
  rev : Ep → Ep

/-- **Definition 25.4.** `Γ = (q_V, q_E, q_F, src_V, src_E, src_F)`. Declared data. -/
structure Reception (Vp Ep Fp V E F : Type) where
  qV : Vp → V
  qE : Ep → ROEdge V E
  qF : Fp → F
  srcV : V → List Vp
  srcE : E → List Ep
  srcF : F → List Fp

section Reception
variable {Vp Ep Fp R V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F]

def Reception.face (Γ : Reception Vp Ep Fp V E F) (f : PFace Vp Ep Fp R) : TFace V E F :=
  ⟨Γ.qF f.key, Γ.qV f.v0, Γ.qV f.v1, Γ.qV f.v2, Γ.qE f.e0, Γ.qE f.e1, Γ.qE f.e2⟩

/-- **Definition 25.5**, from an export and a reception: `K_{Θ,n}^Γ`. -/
def Reception.complex (Γ : Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R)) : Cx V E F :=
  ⟨fs.map Γ.face⟩

def preV (fs : List (PFace Vp Ep Fp R)) : List Vp := fs.flatMap fun f => [f.v0, f.v1, f.v2]
def preE (fs : List (PFace Vp Ep Fp R)) : List Ep := fs.flatMap PFace.edges
def preF (fs : List (PFace Vp Ep Fp R)) : List Fp := fs.map PFace.key

/-- **Definition 25.4, admissibility**: the seven exact conditions. Condition 7 is
    stated as recoverability through the source maps of every received face and
    boundary incidence; the certificates themselves ride in `PFace.record`. -/
structure Admissible (Γ : Reception Vp Ep Fp V E F) (pe : PreEdges Vp Ep) (fs : List (PFace Vp Ep Fp R)) : Prop where
  endpoint : ∀ f ∈ fs, ∀ e ∈ f.edges, (Γ.qE e).src = Γ.qV (pe.src e) ∧ (Γ.qE e).dst = Γ.qV (pe.dst e)
  orientation : ∀ f ∈ fs, ∀ e ∈ f.edges, Γ.qE (pe.rev e) = (Γ.qE e).rev
  nondegenerate : ∀ f ∈ fs, [Γ.qV f.v0, Γ.qV f.v1, Γ.qV f.v2].Nodup ∧
    [(Γ.qE f.e0).key, (Γ.qE f.e1).key, (Γ.qE f.e2).key].Nodup
  boundary : ∀ f ∈ fs, (Γ.complex fs).bdG (Γ.qF f.key) = some (Γ.qE f.e0, Γ.qE f.e1, Γ.qE f.e2)
  separation : ∀ f ∈ fs, ∀ f' ∈ fs, Γ.qF f.key = Γ.qF f'.key → f.key = f'.key
  losslessV : ∀ w x, x ∈ Γ.srcV w ↔ x ∈ preV fs ∧ Γ.qV x = w
  losslessE : ∀ k x, x ∈ Γ.srcE k ↔ x ∈ preE fs ∧ (Γ.qE x).key = k
  losslessF : ∀ k x, x ∈ Γ.srcF k ↔ x ∈ preF fs ∧ Γ.qF x = k
  retention : ∀ f ∈ fs, f.key ∈ Γ.srcF (Γ.qF f.key) ∧ ∀ e ∈ f.edges, e ∈ Γ.srcE (Γ.qE e).key

/-- A reception from declared maps, with the complete finite source fibers. -/
def Reception.ofMaps (qV : Vp → V) (qE : Ep → ROEdge V E) (qF : Fp → F) (fs : List (PFace Vp Ep Fp R)) :
    Reception Vp Ep Fp V E F :=
  ⟨qV, qE, qF, fun w => (preV fs).filter fun x => decide (qV x = w),
    fun k => (preE fs).filter fun x => decide ((qE x).key = k),
    fun k => (preF fs).filter fun x => decide (qF x = k)⟩

/-- **Condition 6 holds for complete fibers.** -/
theorem ofMaps_lossless (qV : Vp → V) (qE : Ep → ROEdge V E) (qF : Fp → F) (fs : List (PFace Vp Ep Fp R)) :
    let Γ := Reception.ofMaps qV qE qF fs
    (∀ w x, x ∈ Γ.srcV w ↔ x ∈ preV fs ∧ Γ.qV x = w) ∧
    (∀ k x, x ∈ Γ.srcE k ↔ x ∈ preE fs ∧ (Γ.qE x).key = k) ∧
    (∀ k x, x ∈ Γ.srcF k ↔ x ∈ preF fs ∧ Γ.qF x = k) := by
  refine ⟨fun w x => ?_, fun k x => ?_, fun k x => ?_⟩ <;>
    exact List.mem_filter.trans (and_congr Iff.rfl decide_eq_true_iff)

set_option linter.unusedDecidableInType false in
/-- **Condition 7 from condition 6.** -/
theorem retention_of_lossless
    (Γ : Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R))
    (hE : ∀ k x, x ∈ Γ.srcE k ↔ x ∈ preE fs ∧ (Γ.qE x).key = k)
    (hF : ∀ k x, x ∈ Γ.srcF k ↔ x ∈ preF fs ∧ Γ.qF x = k) :
    ∀ f ∈ fs, f.key ∈ Γ.srcF (Γ.qF f.key) ∧ ∀ e ∈ f.edges, e ∈ Γ.srcE (Γ.qE e).key :=
  fun f hf => ⟨(hF _ _).mpr ⟨List.mem_map_of_mem hf, rfl⟩,
    fun e he => (hE (Γ.qE e).key e).mpr ⟨List.mem_flatMap.mpr ⟨f, hf, he⟩, rfl⟩⟩

set_option linter.unusedDecidableInType false in
/-- **Condition 4 from separation** on a family with distinct prequotient keys
    (Theorem 23.6). -/
theorem boundary_of_separation
    (Γ : Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R))
    (hnd : (fs.map PFace.key).Nodup)
    (hsep : ∀ f ∈ fs, ∀ f' ∈ fs, Γ.qF f.key = Γ.qF f'.key → f.key = f'.key) :
    ∀ f ∈ fs, (Γ.complex fs).bdG (Γ.qF f.key) = some (Γ.qE f.e0, Γ.qE f.e1, Γ.qE f.e2) := by
  intro f hf
  unfold Cx.bdG Reception.complex
  rw [List.find?_map, find?_of_unique ((fun g : TFace V E F => decide (g.key = Γ.qF f.key)) ∘ Γ.face) f fs hf (decide_eq_true rfl)
    (fun g hg hp => eq_of_map_nodup PFace.key fs hnd g hg f hf (hsep g hg f hf (of_decide_eq_true hp)))]
  rfl

/-- **Ledger 31.5, item 6**: a received face family `fs` becomes a shell input
    through `Γ` when `Γ` is admissible on it (Definition 25.4) and the received
    complex passes all five shell-certificate entries (Definition 25.6). -/
def ReceivedShellInput (Γ : Reception Vp Ep Fp V E F) (pe : PreEdges Vp Ep) (fs : List (PFace Vp Ep Fp R)) : Prop :=
  Admissible Γ pe fs ∧ (Γ.complex fs).ClosedShellInput

/-- **Ledger 31.5, item 6.** A received face family is a shell input exactly when
    `Γ` is admissible and the five certificate entries of the received complex
    (nonempty, connected, two faces per edge, cyclic links, orientation) pass. -/
theorem receivedShellInput_iff (Γ : Reception Vp Ep Fp V E F) (pe : PreEdges Vp Ep) (fs : List (PFace Vp Ep Fp R)) :
    ReceivedShellInput Γ pe fs ↔ Admissible Γ pe fs ∧
      ((Γ.complex fs).faces ≠ [] ∧ (Γ.complex fs).B.Connected ∧
        (∀ e ∈ (Γ.complex fs).EG, ((Γ.complex fs).incE e).length = 2) ∧
        (∀ v ∈ (Γ.complex fs).VG, ((Γ.complex fs).Lk v).IsCycle) ∧ (Γ.complex fs).OriCompat) :=
  and_congr Iff.rfl (closed_iff _)

end Reception

/-! ## The identity reception `Γ_id` on stable keys -/

section Identity
variable {Aux Cert RawAux EvalAux Prov Renew : Type} {h : ℕ}

def FaceRec.pre (r : FaceRec Aux Cert RawAux EvalAux h Prov Renew) :
    PFace QuestionId OEdge FaceId (FaceRec Aux Cert RawAux EvalAux h Prov Renew) :=
  ⟨r.id, r.id.v0, r.id.v1, r.id.v2, r.e0, r.e1, r.e2, r⟩

def labelInv : EdgeLabel → EdgeLabel
  | .gen s => .genInv s
  | .genInv s => .gen s
  | .mat M => .mat (inv2 M)

/-- Reversing a prequotient oriented edge. -/
def orev (e : OEdge) : OEdge := ⟨e.ty, e.dst, e.src, labelInv e.label⟩

def oedges : PreEdges QuestionId OEdge := ⟨OEdge.src, OEdge.dst, orev⟩

/-- `q_E` of the identity reception: the undirected key is `Und`, the endpoints
    are the recorded ones. -/
def qEid (e : OEdge) : ROEdge QuestionId UEdge := ⟨canon (und e), e.src, e.dst⟩

/-- **`Γ_id`**: identity on occurrence vertices and face keys, `Und` on typed edges. -/
def Gid (fs : List (PFace QuestionId OEdge FaceId (FaceRec Aux Cert RawAux EvalAux h Prov Renew))) :
    Reception QuestionId OEdge FaceId QuestionId UEdge FaceId :=
  Reception.ofMaps id qEid id fs

def gidFace (r : FaceRec Aux Cert RawAux EvalAux h Prov Renew) : TFace QuestionId UEdge FaceId :=
  ⟨r.id, r.id.v0, r.id.v1, r.id.v2, qEid r.e0, qEid r.e1, qEid r.e2⟩

/-- The received complex of a face ledger under `Γ_id`. -/
def recvId (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) : Cx QuestionId UEdge FaceId :=
  ⟨L.map gidFace⟩

theorem recvId_eq (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) :
    recvId L = (Gid (L.map FaceRec.pre)).complex (L.map FaceRec.pre) := by
  unfold recvId Reception.complex
  rw [List.map_map]
  rfl

/-- **`Γ_id` is admissible** on any face ledger with distinct stable face keys
    (Theorem 23.6) whose faces are triadically nondegenerate. Conditions 1, 2, 5,
    6, 7 hold for every ledger; 4 needs the distinct keys; 3 is the hypothesis. -/
theorem gid_admissible (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hnd : (L.map (·.id)).Nodup)
    (hnondeg : ∀ r ∈ L, [r.id.v0, r.id.v1, r.id.v2].Nodup ∧
      [canon (und r.e0), canon (und r.e1), canon (und r.e2)].Nodup) :
    Admissible (Gid (L.map FaceRec.pre)) oedges (L.map FaceRec.pre) := by
  obtain ⟨hV, hE, hF⟩ := ofMaps_lossless id qEid id (L.map FaceRec.pre)
  have hsep : ∀ f ∈ L.map FaceRec.pre, ∀ f' ∈ L.map FaceRec.pre,
      (Gid (L.map FaceRec.pre)).qF f.key = (Gid (L.map FaceRec.pre)).qF f'.key → f.key = f'.key :=
    fun _ _ _ _ he => he
  have hkeys : ((L.map FaceRec.pre).map PFace.key).Nodup := by rw [List.map_map]; exact hnd
  refine ⟨fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ e _ => ?_, fun f hf => ?_,
    boundary_of_separation _ _ hkeys hsep, hsep, hV, hE, hF, retention_of_lossless _ _ hE hF⟩
  · change (⟨canon ⟨e.ty, e.dst, e.src⟩, e.dst, e.src⟩ : ROEdge QuestionId UEdge) = ⟨canon ⟨e.ty, e.src, e.dst⟩, e.dst, e.src⟩
    rw [canon_swap]
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
    exact hnondeg r hr

end Identity

/-! ## Theorem 25.8 — The native one-lineage export fails the shell certificate -/

/-- The stable key of the lineage face at event `j+1`. -/
def lineKey (i : QuestionId) (j : ℕ) : FaceId :=
  ⟨i.qid, i.cycle, j + 1, linV i j, linV i (j + 1), counterSibling i j⟩

/-- The lineage face at event `j+1`, received under `Γ_id`. -/
def lineFace (i : QuestionId) (j : ℕ) : TFace QuestionId UEdge FaceId :=
  ⟨lineKey i j, linV i j, linV i (j + 1), counterSibling i j,
    ⟨canon ⟨.raw, linV i j, linV i (j + 1)⟩, linV i j, linV i (j + 1)⟩,
    ⟨canon ⟨.received, linV i (j + 1), counterSibling i j⟩, linV i (j + 1), counterSibling i j⟩,
    ⟨canon ⟨.raw, counterSibling i j, linV i j⟩, counterSibling i j, linV i j⟩⟩

def lineCx (i : QuestionId) (evs : List ℕ) : Cx QuestionId UEdge FaceId := ⟨evs.map (lineFace i)⟩

/-- Received incidence of the lineage complex is §23's lineage incidence, for any
    edge: the canonical key identifies exactly what `UEdge.same` identifies. -/
theorem line_incE (i : QuestionId) (evs : List ℕ) (e : UEdge) :
    (lineCx i evs).incE (canon e) = (lineIncE i evs e).map (lineKey i) := by
  unfold Cx.incE lineCx lineIncE
  rw [List.filter_map, List.map_map]
  refine congrArg₂ List.map rfl (List.filter_congr fun j _ => ?_)
  change ((lineFaceE i j).map canon).any (fun k => decide (k = canon e)) = (lineFaceE i j).any fun e' => decide (e.same e')
  rw [List.any_map]
  exact congrArg (List.any (lineFaceE i j)) (funext fun e' =>
    dec_congr ((canon_eq_iff e' e).trans ⟨UEdge.same_symm, UEdge.same_symm⟩))

/-- **Theorem 25.8, incidence one**, over any Nodup subfamily of one lineage's
    events: every received edge has exactly one incident face. -/
theorem line_every_edge_once (i : QuestionId) (evs : List ℕ) (hnd : evs.Nodup)
    (hlt : ∀ j ∈ evs, j < i.rel.length) :
    ∀ k ∈ (lineCx i evs).EG, ((lineCx i evs).incE k).length = 1 := by
  intro k hk
  unfold Cx.EG at hk
  obtain ⟨f, hf, hkf⟩ := List.mem_flatMap.mp ((mem_nub _ _).mp hk)
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (show k ∈ (lineFaceE i j).map canon from hkf)
  rw [line_incE, List.length_map, lineage_incidence_one i evs hnd hlt j hj e he]
  rfl

theorem line_c2E_false (i : QuestionId) (evs : List ℕ) (hnd : evs.Nodup)
    (hlt : ∀ j ∈ evs, j < i.rel.length) (hne : evs ≠ []) : (lineCx i evs).c2E = false := by
  cases evs with
  | nil => exact absurd rfl hne
  | cons j t =>
    have hk : canon ⟨.raw, linV i j, linV i (j + 1)⟩ ∈ (lineCx i (j :: t)).EG :=
      (mem_nub _ _).mpr (List.mem_flatMap.mpr ⟨lineFace i j, List.Mem.head _, List.Mem.head _⟩)
    cases hc : (lineCx i (j :: t)).c2E
    · rfl
    · have h2 := (c2E_iff _).mp hc _ hk
      rw [line_every_edge_once i (j :: t) hnd hlt _ hk] at h2
      exact absurd h2 (by decide)

theorem not_closed_of_c2E {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F] (K : Cx V E F)
    (h : K.c2E = false) : ¬ K.ClosedShellInput := fun hc => by
  have h2 : K.c2E = true := congrArg CSh.twoE hc
  rw [h] at h2; exact nomatch h2

/-- The committed child at event `j+1` is the lineage entry `x_{j+1}`. -/
theorem child_linV (i : QuestionId) (j : ℕ) (hj : j < i.rel.length) :
    (linV i j).child (i.rel.getD j false) = linV i (j + 1) := by
  simp only [linV, QuestionId.child, QuestionId.mk.injEq, true_and]
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, getD_of_lt _ j hj false]

/-- **Triadic nondegeneracy (25.4 (3)) on lineage faces** under `Γ_id`. -/
theorem lineFace_nondegenerate (i : QuestionId) (j : ℕ) (hj : j < i.rel.length) :
    [linV i j, linV i (j + 1), counterSibling i j].Nodup ∧
    [canon ⟨.raw, linV i j, linV i (j + 1)⟩, canon ⟨.received, linV i (j + 1), counterSibling i j⟩,
      canon ⟨.raw, counterSibling i j, linV i j⟩].Nodup := by
  have l0 := rel_len_linV i j
  have l1 := rel_len_linV i (j + 1)
  have l2 := rel_len_cs i j
  have n01 : linV i j ≠ linV i (j + 1) := fun he => by have := lenEq he; omega
  have n02 : linV i j ≠ counterSibling i j := fun he => by have := lenEq he; omega
  have n12 := linV_ne_cs i j hj
  have nodup3 : ∀ {β : Type} (a b c : β), a ≠ b → a ≠ c → b ≠ c → [a, b, c].Nodup := by
    intro β a b c hab hac hbc
    refine List.nodup_cons.mpr ⟨fun hm => ?_, List.nodup_cons.mpr ⟨fun hm => ?_, List.nodup_cons.mpr ⟨(fun hm => nomatch hm), List.Pairwise.nil⟩⟩⟩
    · rcases List.mem_cons.mp hm with e | hm
      · exact hab e
      · exact hac (List.mem_singleton.mp hm)
    · exact hbc (List.mem_singleton.mp hm)
  refine ⟨nodup3 _ _ _ n01 n02 n12, nodup3 _ _ _ ?_ ?_ ?_⟩
  · exact fun he => raw_not_received _ _ _ _ ((canon_eq_iff _ _).mp he)
  · intro he
    obtain ⟨-, (⟨ha, -⟩ | ⟨-, hb⟩)⟩ := (canon_eq_iff _ _).mp he
    · exact n02 ha
    · exact n12 hb
  · exact fun he => raw_not_received _ _ _ _ (UEdge.same_symm ((canon_eq_iff _ _).mp he))

section Lineage
variable {Aux Cert RawAux EvalAux Prov Renew : Type} {h : ℕ}

/-- A face record attached from the committed lineage ending at `i`: its packet
    is stably keyed at parent `x_j` with the lineage's next hand, and its key and
    boundary are the entry ones (Definition 23.3; renewal and release change
    neither). -/
structure LineShaped (i : QuestionId) (r : FaceRec Aux Cert RawAux EvalAux h Prov Renew) : Prop where
  wk : WellKeyed r.packet.input
  hx : r.packet.input.x = linV i r.packet.input.j
  hs : r.packet.input.s = i.rel.getD r.packet.input.j false
  hj : r.packet.input.j < i.rel.length
  hid : r.id = faceIdOf r.packet.input
  he0 : r.e0 = edge0 r.packet.input
  he1 : r.e1 = edge1 r.packet.input
  he2 : r.e2 = edge2 r.packet.input

def evJ (r : FaceRec Aux Cert RawAux EvalAux h Prov Renew) : ℕ := r.packet.input.j

theorem entryRec_shaped (i : QuestionId) (p : FElig Aux Cert RawAux EvalAux h) (t : QuestionId) (pv : Prov)
    (hwk : WellKeyed p.input) (hx : p.input.x = linV i p.input.j) (hs : p.input.s = i.rel.getD p.input.j false)
    (hj : p.input.j < i.rel.length) : LineShaped i (entryRec (Renew := Renew) p t pv) :=
  ⟨hwk, hx, hs, hj, rfl, rfl, rfl, rfl⟩

theorem shaped_face {i : QuestionId} {r : FaceRec Aux Cert RawAux EvalAux h Prov Renew} (hr : LineShaped i r) :
    gidFace r = lineFace i (evJ r) := by
  obtain ⟨⟨hS, hB⟩, hx, hs, hj, hid, h0, h1, h2⟩ := hr
  have eS : r.packet.input.idS = linV i (r.packet.input.j + 1) := by
    rw [hS, hs, hx]; exact child_linV i _ hj
  have eB : r.packet.input.idBar = counterSibling i r.packet.input.j := by
    rw [hB, hs, hx]; rfl
  unfold gidFace lineFace lineKey evJ
  rw [hid, h0, h1, h2]
  unfold faceIdOf edge0 edge1 edge2 qEid und
  rw [eS, eB, hx]
  rfl

theorem recvId_lineage (i : QuestionId) (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hL : ∀ r ∈ L, LineShaped i r) : recvId L = lineCx i (L.map evJ) := by
  unfold recvId lineCx
  rw [List.map_map]
  exact congrArg Cx.mk (List.map_congr_left fun r hr => shaped_face (hL r hr))

theorem lineKey_injective (i : QuestionId) : Function.Injective (lineKey i) := fun j j' he => by
  have := congrArg FaceId.event he
  simp only [lineKey] at this
  omega

/-- **`Γ_id` is admissible on a one-lineage ledger** with one face per event. -/
theorem gid_lineage_admissible (i : QuestionId) (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hL : ∀ r ∈ L, LineShaped i r) (hnd : (L.map evJ).Nodup) :
    Admissible (Gid (L.map FaceRec.pre)) oedges (L.map FaceRec.pre) := by
  apply gid_admissible
  · have : L.map (·.id) = (L.map evJ).map (lineKey i) := by
      rw [List.map_map]
      exact List.map_congr_left fun r hr => congrArg TFace.key (shaped_face (hL r hr))
    rw [this]
    exact nodup_map_inj _ (lineKey_injective i) _ hnd
  · intro r hr
    have hf := shaped_face (hL r hr)
    have hv : [r.id.v0, r.id.v1, r.id.v2] = [linV i (evJ r), linV i (evJ r + 1), counterSibling i (evJ r)] := by
      rw [show r.id.v0 = _ from congrArg TFace.v0 hf, show r.id.v1 = _ from congrArg TFace.v1 hf,
        show r.id.v2 = _ from congrArg TFace.v2 hf]; rfl
    have he : [canon (und r.e0), canon (und r.e1), canon (und r.e2)] =
        [canon ⟨.raw, linV i (evJ r), linV i (evJ r + 1)⟩, canon ⟨.received, linV i (evJ r + 1), counterSibling i (evJ r)⟩,
          canon ⟨.raw, counterSibling i (evJ r), linV i (evJ r)⟩] := by
      rw [show canon (und r.e0) = _ from congrArg (fun f => f.b0.key) hf,
        show canon (und r.e1) = _ from congrArg (fun f => f.b1.key) hf,
        show canon (und r.e2) = _ from congrArg (fun f => f.b2.key) hf]; rfl
    rw [hv, he]
    exact lineFace_nondegenerate i (evJ r) (hL r hr).hj

/-- **Theorem 25.8.** Let the active family be faces attached from one committed
    terminal lineage (one per event), received under `Γ_id`, which is admissible
    for it. If the family is nonempty, every received edge has exactly one
    incident face, `c_2E = 0`, and the complex is not a closed orientable triadic
    shell input — although every individual face closes projectively
    (Proposition 22.2). -/
theorem one_lineage_fails_shell (i : QuestionId) (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hL : ∀ r ∈ L, LineShaped i r) (hnd : (L.map evJ).Nodup) (hne : L ≠ []) :
    Admissible (Gid (L.map FaceRec.pre)) oedges (L.map FaceRec.pre) ∧
    (∀ k ∈ (recvId L).EG, ((recvId L).incE k).length = 1) ∧
    (recvId L).c2E = false ∧ ¬ (recvId L).ClosedShellInput ∧
    (∀ s ℓ : Bool, projClass (Word.gen s * liftedA s ℓ * inv2 (Word.gen (!s))) = projClass 1) := by
  have hlt : ∀ j ∈ L.map evJ, j < i.rel.length := fun j hj => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hj
    exact (hL r hr).hj
  have hne' : L.map evJ ≠ [] := fun he => hne (List.map_eq_nil_iff.mp he)
  have hc := line_c2E_false i _ hnd hlt hne'
  rw [recvId_lineage i L hL]
  exact ⟨gid_lineage_admissible i L hL hnd, line_every_edge_once i _ hnd hlt, hc,
    not_closed_of_c2E _ hc, boundary_projectively_closed⟩

/-- **Release cannot supply a second incidence** (Corollary 25.9, last clause):
    any sublist of a one-lineage family, in particular any active restriction,
    still has every received edge at incidence one. -/
theorem sublist_every_edge_once (i : QuestionId) (L L' : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hL : ∀ r ∈ L, LineShaped i r) (hnd : (L.map evJ).Nodup) (hsub : List.Sublist L' L) :
    (∀ k ∈ (recvId L').EG, ((recvId L').incE k).length = 1) ∧ (L' ≠ [] → (recvId L').c2E = false) := by
  have hL' : ∀ r ∈ L', LineShaped i r := fun r hr => hL r (hsub.subset hr)
  have hnd' : (L'.map evJ).Nodup := hnd.sublist (hsub.map evJ)
  have hlt : ∀ j ∈ L'.map evJ, j < i.rel.length := fun j hj => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hj
    exact (hL' r hr).hj
  rw [recvId_lineage i L' hL']
  exact ⟨line_every_edge_once i _ hnd' hlt,
    fun hne => line_c2E_false i _ hnd' hlt (fun he => hne (List.map_eq_nil_iff.mp he))⟩

end Lineage

/-! ### A computed instance: three lineage faces under `Γ_id` -/

def iWit : QuestionId := ⟨0, 0, 0, [false, true, true]⟩

theorem lineage_witness :
    (lineCx iWit [0, 1, 2]).c2E = false ∧
    ((lineCx iWit [0, 1, 2]).EG.map fun k => ((lineCx iWit [0, 1, 2]).incE k).length) = [1, 1, 1, 1, 1, 1, 1, 1, 1] ∧
    (lineCx iWit [0, 1, 2]).cLink = false ∧ (lineCx iWit [0, 1, 2]).cNonempty = true := by
  decide

/-! ## Exact witnesses on small keyed complexes -/

def ek (a b : ℕ) : ℕ × ℕ := (min a b, max a b)

def tri (k a b c : ℕ) : TFace ℕ (ℕ × ℕ) ℕ :=
  ⟨k, a, b, c, ⟨ek a b, a, b⟩, ⟨ek b c, b, c⟩, ⟨ek c a, c, a⟩⟩

/-- The boundary of a tetrahedron, coherently oriented. -/
def tetra : Cx ℕ (ℕ × ℕ) ℕ := ⟨[tri 0 0 1 2, tri 1 0 3 1, tri 2 1 3 2, tri 3 2 3 0]⟩

/-- The same four faces with one boundary traversed backwards. -/
def tetraTwisted : Cx ℕ (ℕ × ℕ) ℕ := ⟨[tri 0 0 2 1, tri 1 0 3 1, tri 2 1 3 2, tri 3 2 3 0]⟩

/-- Two retained faces sharing one vertex. -/
def bowtie : Cx ℕ (ℕ × ℕ) ℕ := ⟨[tri 0 0 1 2, tri 1 0 3 4]⟩

def oneFace : Cx ℕ (ℕ × ℕ) ℕ := ⟨[tri 0 0 1 2]⟩

set_option maxRecDepth 100000

/-- **The certificate is satisfiable**: a sphere-shell input exists. -/
theorem tetra_sphere : tetra.csh = allOnes ∧ tetra.D = sphereDefect := by decide

theorem tetraTwisted_cert : tetraTwisted.csh = ⟨true, true, true, true, false⟩ ∧ tetraTwisted.D = sphereDefect := by
  decide

theorem bowtie_cert : bowtie.csh = ⟨true, true, false, false, true⟩ := by decide

theorem oneFace_cert : oneFace.csh = ⟨true, true, false, false, true⟩ := by decide

/-! ## Definition 25.1 — Accumulated archival and active face families -/

section Active
variable {Aux Cert RawAux EvalAux Prov Renew P Y : Type} {h : ℕ}

/-- `𝔏^arch_{≤n}`: every face record entered by stratum `n` (the entry stratum is
    the face's `k_f`, Definition 24.1, supplied as `entry`). -/
def archAt (faces : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) (entry : FaceRec Aux Cert RawAux EvalAux h Prov Renew → ℕ)
    (n : ℕ) : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew) :=
  faces.filter fun r => decide (entry r ≤ n)

/-- The lifecycle evaluations of `ι_f` whose read stratum is `n`. -/
def evalsAt (D : LifeLedger P Y) (fid : FaceId) (n : ℕ) : LifeLedger P Y :=
  D.filter fun ev => decide (ev.1.1 = fid) && decide (ev.1.2.2 = n)

/-- **Export-ready for `Θ`**: every retention-compatible face entered by `n` has
    exactly one lifecycle evaluation read at `n`. Retention compatibility is the
    declaration's (`compat`). -/
def exportReady (ar : Archive (FaceRec Aux Cert RawAux EvalAux h Prov Renew) P Y)
    (entry : FaceRec Aux Cert RawAux EvalAux h Prov Renew → ℕ) (compat : FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool)
    (n : ℕ) : Bool :=
  (archAt ar.faces entry n).all fun r => !compat r || decide ((evalsAt ar.lifeLedger r.id n).length = 1)

/-- `Active_Θ(f; n)`, read from the unique evaluation at `n`. -/
def activeAt (D : LifeLedger P Y) (fid : FaceId) (n : ℕ) : Bool :=
  match evalsAt D fid n with
  | [ev] => active ev.2.stat
  | _ => false

/-- `𝖥^actMap_{Θ,n}`: the exact restriction of the archival map. -/
def actFaces (ar : Archive (FaceRec Aux Cert RawAux EvalAux h Prov Renew) P Y)
    (entry : FaceRec Aux Cert RawAux EvalAux h Prov Renew → ℕ) (compat : FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool)
    (n : ℕ) : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew) :=
  (archAt ar.faces entry n).filter fun r => compat r && activeAt ar.lifeLedger r.id n

/-- `Inc^act_V(v) = Inc^arch_V(v) ∩ 𝖥^act`. -/
def incVAct (arch : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) (keys : List FaceId) (v : QuestionId) : List FaceId :=
  (incV arch v).filter fun k => decide (k ∈ keys)

/-- `Inc^act_E(e) = Inc^arch_E(e) ∩ 𝖥^act`. -/
def incEAct (arch : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) (keys : List FaceId) (e : UEdge) : List FaceId :=
  (incE arch e).filter fun k => decide (k ∈ keys)

/-- The archival boundary map restricted to active keys. -/
def bdAct (arch : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) (keys : List FaceId) (fid : FaceId) :
    Option (OEdge × OEdge × OEdge) :=
  if fid ∈ keys then bd arch fid else none

/-- At an export-ready stratum every compatible entered face has one current
    lifecycle read `m_f(n)`, and `Active_Θ(f;n)` is its status. -/
theorem ready_unique_read (ar : Archive (FaceRec Aux Cert RawAux EvalAux h Prov Renew) P Y)
    (entry : FaceRec Aux Cert RawAux EvalAux h Prov Renew → ℕ) (compat : FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool)
    (n : ℕ) (hready : exportReady ar entry compat n = true)
    (r : FaceRec Aux Cert RawAux EvalAux h Prov Renew) (hr : r ∈ archAt ar.faces entry n) (hc : compat r = true) :
    ∃ ev, evalsAt ar.lifeLedger r.id n = [ev] ∧ activeAt ar.lifeLedger r.id n = active ev.2.stat := by
  have hall := List.all_eq_true.mp hready r hr
  rw [hc, Bool.not_true, Bool.false_or] at hall
  have hl := of_decide_eq_true hall
  cases hE : evalsAt ar.lifeLedger r.id n with
  | nil => rw [hE] at hl; exact nomatch hl
  | cons ev t =>
    cases t with
    | nil => exact ⟨ev, rfl, by unfold activeAt; rw [hE]⟩
    | cons _ _ => rw [hE] at hl; simp only [List.length_cons] at hl; exfalso; omega

/-- Intersecting archival incidence with the keys of a restricted family is the
    incidence of that family, when stable keys are distinct (Theorem 23.6). -/
theorem filter_keys_eq (arch : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) (hnd : (arch.map (·.id)).Nodup)
    (q p : FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool) :
    ((arch.filter p).map (·.id)).filter (fun k => decide (k ∈ (arch.filter q).map (·.id))) =
      ((arch.filter q).filter p).map (·.id) := by
  rw [List.filter_map, List.filter_filter, List.filter_filter]
  refine congrArg (List.map _) (List.filter_congr fun r hr => ?_)
  have hk : decide (r.id ∈ (arch.filter q).map (·.id)) = q r := by
    cases hq : q r
    · apply decide_eq_false
      intro hm
      obtain ⟨r', hr', he⟩ := List.mem_map.mp hm
      have hr'a := List.mem_filter.mp hr'
      rw [eq_of_map_nodup (·.id) arch hnd r' hr'a.1 r hr he, hq] at hr'a
      exact nomatch hr'a.2
    · exact decide_eq_true (List.mem_map_of_mem (List.mem_filter.mpr ⟨hr, hq⟩))
  change (decide (r.id ∈ (arch.filter q).map (·.id)) && p r) = (p r && q r)
  rw [hk, Bool.and_comm]

/-- **Definition 25.1, active incidence.** On the archival family at `n`, the
    boxed intersections are the vertex and edge incidence of the active family. -/
theorem active_incidence (ar : Archive (FaceRec Aux Cert RawAux EvalAux h Prov Renew) P Y)
    (entry : FaceRec Aux Cert RawAux EvalAux h Prov Renew → ℕ) (compat : FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool)
    (n : ℕ) (hnd : (ar.faces.map (·.id)).Nodup) (v : QuestionId) (e : UEdge) :
    incVAct (archAt ar.faces entry n) ((actFaces ar entry compat n).map (·.id)) v = incV (actFaces ar entry compat n) v ∧
    incEAct (archAt ar.faces entry n) ((actFaces ar entry compat n).map (·.id)) e = incE (actFaces ar entry compat n) e := by
  have hnd' : ((archAt ar.faces entry n).map (·.id)).Nodup := hnd.sublist (List.filter_sublist.map _)
  exact ⟨filter_keys_eq _ hnd' _ _, filter_keys_eq _ hnd' _ _⟩

/-- Filtering is a view: the active family is a sublist of the archival family,
    which is a sublist of the stored faces; and release does not change the
    archival family at any stratum. -/
theorem active_is_view (ar : Archive (FaceRec Aux Cert RawAux EvalAux h Prov Renew) P Y)
    (entry : FaceRec Aux Cert RawAux EvalAux h Prov Renew → ℕ) (compat : FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool)
    (n : ℕ) (e : LifeEvt P Y) (rel : ReleaseRec P) :
    List.Sublist (actFaces ar entry compat n) (archAt ar.faces entry n) ∧
    List.Sublist (archAt ar.faces entry n) ar.faces ∧
    archAt (applyRelease ar e rel).faces entry n = archAt ar.faces entry n :=
  ⟨List.filter_sublist, List.filter_sublist, rfl⟩

/-! ## Definition 25.2 — Lossless shell-interface export -/

/-- **Definition 25.2.** `ShellIn_{Θ,n}`. The archive (face records, lifecycle
    ledger, release records) is included whole. -/
structure ShellIn (S Aux Cert RawAux EvalAux Prov Renew P Y Ph St : Type) (h : ℕ) where
  faceState : S
  theta : Retention P Y Ph St
  archive : Archive (FaceRec Aux Cert RawAux EvalAux h Prov Renew) P Y
  n : ℕ
  arch : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)
  actMap : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)
  incVAct : QuestionId → List FaceId
  incEAct : UEdge → List FaceId
  bdAct : FaceId → Option (OEdge × OEdge × OEdge)

def shellIn {S Ph St : Type} (Sf : S) (Θ : Retention P Y Ph St) (ar : Archive (FaceRec Aux Cert RawAux EvalAux h Prov Renew) P Y)
    (entry : FaceRec Aux Cert RawAux EvalAux h Prov Renew → ℕ) (compat : FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool)
    (n : ℕ) : ShellIn S Aux Cert RawAux EvalAux Prov Renew P Y Ph St h :=
  ⟨Sf, Θ, ar, n, archAt ar.faces entry n, actFaces ar entry compat n,
    incVAct (archAt ar.faces entry n) ((actFaces ar entry compat n).map (·.id)),
    incEAct (archAt ar.faces entry n) ((actFaces ar entry compat n).map (·.id)),
    bdAct (archAt ar.faces entry n) ((actFaces ar entry compat n).map (·.id))⟩

/-! ## Theorem 25.3 — Finiteness, exactness, and recoverability of the export -/

/-- **Theorem 25.3.** Every component is a finite list or a function computed by
    finite filters from it. From the export one recovers the archive whole
    (every active and released face record, the lifecycle ledger, every release
    record with its failed-gate set), the prequotient incidence of the archival
    family, and the active incidence as the incidence of the active family. A
    further release leaves the archival family and every earlier release record
    in place (Theorem 24.14). -/
theorem shellIn_recoverable {S Ph St : Type} (Sf : S) (Θ : Retention P Y Ph St)
    (ar : Archive (FaceRec Aux Cert RawAux EvalAux h Prov Renew) P Y)
    (entry : FaceRec Aux Cert RawAux EvalAux h Prov Renew → ℕ) (compat : FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool)
    (n : ℕ) (hnd : (ar.faces.map (·.id)).Nodup) (e : LifeEvt P Y) (fid : FaceId) (m : ℕ) (g : Gates) (Z : P) :
    let X := shellIn Sf Θ ar entry compat n
    X.archive = ar ∧ List.Sublist X.actMap X.arch ∧ List.Sublist X.arch ar.faces ∧
    (∀ v, X.incVAct v = incV X.actMap v) ∧ (∀ u, X.incEAct u = incE X.actMap u) ∧
    (∀ v, incV X.arch v = incV (archAt ar.faces entry n) v) ∧
    (shellIn Sf Θ (applyRelease ar e (releaseRec fid m g Z)) entry compat n).arch = X.arch ∧
    ar.releases.Sublist (applyRelease ar e (releaseRec fid m g Z)).releases ∧
    (applyRelease ar e (releaseRec fid m g Z)).releases.getLast? = some ⟨fid, m, g.fail, Z⟩ := by
  intro X
  obtain ⟨-, -, -, -, -, hrel, hlast⟩ := release_deletes_nothing ar e fid m g Z (⟨0, 0, 0, []⟩ : QuestionId) ⟨.raw, ⟨0, 0, 0, []⟩, ⟨0, 0, 0, []⟩⟩
  exact ⟨rfl, List.filter_sublist, List.filter_sublist,
    fun v => (active_incidence ar entry compat n hnd v ⟨.raw, v, v⟩).1,
    fun u => (active_incidence ar entry compat n hnd ⟨0, 0, 0, []⟩ u).2, fun _ => rfl, rfl, hrel.sublist, hlast⟩

end Active

/-! ## Corollary 25.9 — Canonical seven-tick exports fail the shell certificate under the identity reception -/

section Canonical
variable {Aux Cert RawAux EvalAux Prov Renew : Type} {h : ℕ}

/-- An event of a Prop. 22.10 trace sits on the lineage ending at `i`. -/
def shapeB (i : QuestionId) (e : FaceRegression.Event) : Bool :=
  decide (e.x = linV i e.j) && decide (e.s = i.rel.getD e.j false) && decide (e.j < i.rel.length)

/-- The ledger recorded from a trace's attached packets is a one-lineage ledger
    with one face per event. -/
theorem trace_ledger_shaped (i : QuestionId) (es : List FaceRegression.Event) (t : QuestionId) (pv : Prov)
    (hsh : es.all (shapeB i) = true) (hnd : (es.map FaceRegression.Event.j).Nodup)
    (c o : List (FElig Aux Cert RawAux EvalAux h))
    (hmap : c.map (fun p => p.input) = es.map (fun e => e.toInput t))
    (ho : ∀ p ∈ o, (p.elig.lin && p.elig.snap) = false) :
    (∀ r ∈ ledgerOf (Renew := Renew) (receivedFaces (c ++ o)) t pv, LineShaped i r) ∧
    ((ledgerOf (Renew := Renew) (receivedFaces (c ++ o)) t pv).map evJ).Nodup := by
  have hoff : o.filter (fun p => p.elig.all) = [] := by
    apply filter_eq_nil_of
    intro p hp
    have hls := ho p hp
    unfold Eligibility.all
    revert hls
    generalize p.elig.lin = a; generalize p.elig.adm = b; generalize p.elig.snap = c'
    generalize p.elig.recv = d; generalize p.elig.record = e
    revert a b c' d e; decide
  have hL : ledgerOf (Renew := Renew) (receivedFaces (c ++ o)) t pv =
      (c.filter (fun p => p.elig.all)).map (fun p => entryRec p t pv) := by
    unfold ledgerOf receivedFaces
    rw [List.filter_append, hoff, List.append_nil, List.map_map]
    rfl
  rw [hL]
  constructor
  · intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have hpc := (List.mem_filter.mp hp).1
    have hmem : p.input ∈ es.map (fun e => e.toInput t) := hmap ▸ List.mem_map_of_mem hpc
    obtain ⟨e, he, hei⟩ := List.mem_map.mp hmem
    have hs := List.all_eq_true.mp hsh e he
    unfold shapeB at hs
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff] at hs
    obtain ⟨⟨h1, h2⟩, h3⟩ := hs
    apply entryRec_shaped
    · rw [← hei]; exact ⟨rfl, rfl⟩
    · rw [← hei]; exact h1
    · rw [← hei]; exact h2
    · rw [← hei]; exact h3
  · have hc : c.map (fun p => p.input.j) = es.map FaceRegression.Event.j := by
      have := congrArg (List.map EligInput.j) hmap
      rw [List.map_map, List.map_map] at this
      exact this
    rw [← hc] at hnd
    have hsub : List.Sublist ((c.filter (fun p => p.elig.all)).map (fun p : FElig Aux Cert RawAux EvalAux h => p.input.j))
        (c.map (fun p : FElig Aux Cert RawAux EvalAux h => p.input.j)) := List.filter_sublist.map _
    rw [List.map_map]
    exact hnd.sublist hsub

/-- The terminal occurrences `x*` of the four singleton traces. -/
def xSideL : QuestionId := RootOrbit.XepsSideL7.active.headD ⟨0, 0, 0, []⟩
def xSideR : QuestionId := RootOrbit.XepsSideR7.active.headD ⟨0, 0, 0, []⟩
def xLL : QuestionId := LoneSeed.XLL7.active.headD ⟨0, 0, 0, []⟩
def xRR : QuestionId := LoneSeed.XRR7.active.headD ⟨0, 0, 0, []⟩

set_option maxRecDepth 200000 in
/-- Every event of the four singleton traces sits on its terminal lineage, one
    event per depth. Decided on the traces themselves. -/
theorem traces_on_lineage :
    FaceRegression.eventsSideL.all (shapeB xSideL) = true ∧ (FaceRegression.eventsSideL.map FaceRegression.Event.j).Nodup ∧
    FaceRegression.eventsSideR.all (shapeB xSideR) = true ∧ (FaceRegression.eventsSideR.map FaceRegression.Event.j).Nodup ∧
    FaceRegression.eventsLL.all (shapeB xLL) = true ∧ (FaceRegression.eventsLL.map FaceRegression.Event.j).Nodup ∧
    FaceRegression.eventsRR.all (shapeB xRR) = true ∧ (FaceRegression.eventsRR.map FaceRegression.Event.j).Nodup := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Corollary 25.9, item 1.** The unresolved root and the unresolved polarized
    questions export no committed face: the received complex of their ledger is
    empty and `c_nonempty = 0` (Proposition 22.10). -/
theorem cor_25_9_unresolved (t : QuestionId) (pv : Prov) (ps : List (FElig Aux Cert RawAux EvalAux h)) :
    ((∀ p ∈ ps, p.input.status = termStatus RootOrbit.Xeps7.active.length) →
      (recvId (ledgerOf (Renew := Renew) (receivedFaces ps) t pv)).cNonempty = false) ∧
    ((∀ p ∈ ps, p.input.status = termStatus RootOrbit.XL7.active.length) →
      (recvId (ledgerOf (Renew := Renew) (receivedFaces ps) t pv)).cNonempty = false) ∧
    ((∀ p ∈ ps, p.input.status = termStatus RootOrbit.XR7.active.length) →
      (recvId (ledgerOf (Renew := Renew) (receivedFaces ps) t pv)).cNonempty = false) := by
  refine ⟨fun hps => ?_, fun hps => ?_, fun hps => ?_⟩
  · rw [FaceRegression.prop_22_10_root_none.2.2 ps hps]; rfl
  · rw [FaceRegression.prop_22_10_QL_none.2.2.2.2 ps hps]; rfl
  · rw [FaceRegression.prop_22_10_QR_none.2.2.2.2 ps hps]; rfl

/-- **Corollary 25.9, items 2–3, side-selected root.** Six faces each
    (Proposition 22.10), and under `Γ_id` every received edge has incidence one,
    `c_2E = 0`, no closed shell input (Theorem 25.8). -/
theorem cor_25_9_side (t : QuestionId) (pv : Prov) (cL oL cR oR : List (FElig Aux Cert RawAux EvalAux h))
    (hL : cL.map (fun p => p.input) = FaceRegression.eventsSideL.map (fun e => e.toInput t))
    (hoL : ∀ p ∈ oL, (p.elig.lin && p.elig.snap) = false)
    (hR : cR.map (fun p => p.input) = FaceRegression.eventsSideR.map (fun e => e.toInput t))
    (hoR : ∀ p ∈ oR, (p.elig.lin && p.elig.snap) = false) :
    let LL := ledgerOf (Renew := Renew) (receivedFaces (cL ++ oL)) t pv
    let LR := ledgerOf (Renew := Renew) (receivedFaces (cR ++ oR)) t pv
    LL.length = 6 ∧ LR.length = 6 ∧
    (∀ k ∈ (recvId LL).EG, ((recvId LL).incE k).length = 1) ∧ (recvId LL).c2E = false ∧ ¬ (recvId LL).ClosedShellInput ∧
    (∀ k ∈ (recvId LR).EG, ((recvId LR).incE k).length = 1) ∧ (recvId LR).c2E = false ∧ ¬ (recvId LR).ClosedShellInput := by
  intro LL LR
  obtain ⟨nL, nR⟩ := FaceRegression.prop_22_10_side_counts t cL oL cR oR hL hoL hR hoR
  obtain ⟨sL, dL, sR, dR, -⟩ := traces_on_lineage
  have lenL : LL.length = 6 := by change (List.map _ _).length = 6; rw [List.length_map]; exact nL
  have lenR : LR.length = 6 := by change (List.map _ _).length = 6; rw [List.length_map]; exact nR
  obtain ⟨shL, ndL⟩ := trace_ledger_shaped (Renew := Renew) xSideL _ t pv sL dL cL oL hL hoL
  obtain ⟨shR, ndR⟩ := trace_ledger_shaped (Renew := Renew) xSideR _ t pv sR dR cR oR hR hoR
  obtain ⟨-, a1, a2, a3, -⟩ := one_lineage_fails_shell xSideL LL shL ndL (fun he => by rw [he] at lenL; exact nomatch lenL)
  obtain ⟨-, b1, b2, b3, -⟩ := one_lineage_fails_shell xSideR LR shR ndR (fun he => by rw [he] at lenR; exact nomatch lenR)
  exact ⟨lenL, lenR, a1, a2, a3, b1, b2, b3⟩

/-- **Corollary 25.9, items 2–3, face-bearing lone seeds.** Seven faces each, and
    the same obstruction. -/
theorem cor_25_9_lone (t : QuestionId) (pv : Prov) (cL oL cR oR : List (FElig Aux Cert RawAux EvalAux h))
    (hL : cL.map (fun p => p.input) = FaceRegression.eventsLL.map (fun e => e.toInput t))
    (hoL : ∀ p ∈ oL, (p.elig.lin && p.elig.snap) = false)
    (hR : cR.map (fun p => p.input) = FaceRegression.eventsRR.map (fun e => e.toInput t))
    (hoR : ∀ p ∈ oR, (p.elig.lin && p.elig.snap) = false) :
    let LL := ledgerOf (Renew := Renew) (receivedFaces (cL ++ oL)) t pv
    let LR := ledgerOf (Renew := Renew) (receivedFaces (cR ++ oR)) t pv
    LL.length = 7 ∧ LR.length = 7 ∧
    (∀ k ∈ (recvId LL).EG, ((recvId LL).incE k).length = 1) ∧ (recvId LL).c2E = false ∧ ¬ (recvId LL).ClosedShellInput ∧
    (∀ k ∈ (recvId LR).EG, ((recvId LR).incE k).length = 1) ∧ (recvId LR).c2E = false ∧ ¬ (recvId LR).ClosedShellInput := by
  intro LL LR
  obtain ⟨nL, nR⟩ := FaceRegression.prop_22_10_lone_counts t cL oL cR oR hL hoL hR hoR
  obtain ⟨-, -, -, -, sL, dL, sR, dR⟩ := traces_on_lineage
  have lenL : LL.length = 7 := by change (List.map _ _).length = 7; rw [List.length_map]; exact nL
  have lenR : LR.length = 7 := by change (List.map _ _).length = 7; rw [List.length_map]; exact nR
  obtain ⟨shL, ndL⟩ := trace_ledger_shaped (Renew := Renew) xLL _ t pv sL dL cL oL hL hoL
  obtain ⟨shR, ndR⟩ := trace_ledger_shaped (Renew := Renew) xRR _ t pv sR dR cR oR hR hoR
  obtain ⟨-, a1, a2, a3, -⟩ := one_lineage_fails_shell xLL LL shL ndL (fun he => by rw [he] at lenL; exact nomatch lenL)
  obtain ⟨-, b1, b2, b3, -⟩ := one_lineage_fails_shell xRR LR shR ndR (fun he => by rw [he] at lenR; exact nomatch lenR)
  exact ⟨lenL, lenR, a1, a2, a3, b1, b2, b3⟩

/-- **Corollary 25.9, release clause.** Any active restriction of such a ledger
    (a sublist) keeps every received edge at incidence one. -/
theorem cor_25_9_release (i : QuestionId) (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hL : ∀ r ∈ L, LineShaped i r) (hnd : (L.map evJ).Nodup) (q : FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool) :
    (∀ k ∈ (recvId (L.filter q)).EG, ((recvId (L.filter q)).incE k).length = 1) ∧
    (L.filter q ≠ [] → (recvId (L.filter q)).c2E = false) :=
  sublist_every_edge_once i L _ hL hnd List.filter_sublist

end Canonical

/-! ## A declared attaching reception that identifies: four disjoint triangles glued -/

/-- Twelve prequotient occurrence vertices, glued to the four tetrahedron vertices. -/
def glueV (x : ℕ) : ℕ := [0, 1, 2, 0, 3, 1, 1, 3, 2, 2, 3, 0].getD x 0

def glueE (e : ℕ × ℕ) : ROEdge ℕ (ℕ × ℕ) := ⟨ek (glueV e.1) (glueV e.2), glueV e.1, glueV e.2⟩

def pairEdges : PreEdges ℕ (ℕ × ℕ) := ⟨Prod.fst, Prod.snd, Prod.swap⟩

def pTri (k a b c : ℕ) : PFace ℕ (ℕ × ℕ) ℕ Unit := ⟨k, a, b, c, (a, b), (b, c), (c, a), ()⟩

def preTetra : List (PFace ℕ (ℕ × ℕ) ℕ Unit) := [pTri 0 0 1 2, pTri 1 3 4 5, pTri 2 6 7 8, pTri 3 9 10 11]
def preTwisted : List (PFace ℕ (ℕ × ℕ) ℕ Unit) := [pTri 0 0 2 1, pTri 1 3 4 5, pTri 2 6 7 8, pTri 3 9 10 11]

theorem ek_comm (a b : ℕ) : ek a b = ek b a := by
  unfold ek; rw [Nat.min_comm, Nat.max_comm]

theorem glue_admissible (fs : List (PFace ℕ (ℕ × ℕ) ℕ Unit)) (hnd : (fs.map PFace.key).Nodup)
    (hnondeg : ∀ f ∈ fs, [glueV f.v0, glueV f.v1, glueV f.v2].Nodup ∧
      [(glueE f.e0).key, (glueE f.e1).key, (glueE f.e2).key].Nodup) :
    Admissible (Reception.ofMaps glueV glueE id fs) pairEdges fs := by
  obtain ⟨hV, hE, hF⟩ := ofMaps_lossless glueV glueE id fs
  have hsep : ∀ f ∈ fs, ∀ f' ∈ fs, (Reception.ofMaps glueV glueE id fs).qF f.key =
      (Reception.ofMaps glueV glueE id fs).qF f'.key → f.key = f'.key := fun _ _ _ _ he => he
  refine ⟨fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ e _ => ?_, hnondeg, boundary_of_separation _ _ hnd hsep, hsep,
    hV, hE, hF, retention_of_lossless _ _ hE hF⟩
  change (⟨ek (glueV e.2) (glueV e.1), glueV e.2, glueV e.1⟩ : ROEdge ℕ (ℕ × ℕ)) = ⟨ek (glueV e.1) (glueV e.2), glueV e.2, glueV e.1⟩
  rw [ek_comm]

theorem glue_tetra : (Reception.ofMaps glueV glueE id preTetra).complex preTetra = tetra := rfl
theorem glue_twisted : (Reception.ofMaps glueV glueE id preTwisted).complex preTwisted = tetraTwisted := rfl

theorem glue_admissible_tetra : Admissible (Reception.ofMaps glueV glueE id preTetra) pairEdges preTetra :=
  glue_admissible _ (by decide) (by decide)

theorem glue_admissible_twisted : Admissible (Reception.ofMaps glueV glueE id preTwisted) pairEdges preTwisted :=
  glue_admissible _ (by decide) (by decide)

/-! ## Theorem 25.10 — Exact handoff to global shell analysis -/

section Handoff
variable {Aux Cert RawAux EvalAux Prov Renew P Y Ph St S V E F Src : Type} {h : ℕ}
  [DecidableEq V] [DecidableEq E] [DecidableEq F]

/-- **Theorem 25.10.** Given an export and a reception, the certificate is a
    function of the export's active face map and the reception's maps alone: two
    exports with the same active family give the same certificate, however their
    other archival or lifecycle records differ. The active records are retained
    whole in the received source family (local projective and lift records,
    renewal and release fields ride in `FaceRec`). -/
theorem handoff_complete (X X' : ShellIn S Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (hact : X.actMap = X'.actMap) (Γ : Reception QuestionId OEdge FaceId V E F) (src : Src) :
    (Γ.complex (X.actMap.map FaceRec.pre)).cert src = (Γ.complex (X'.actMap.map FaceRec.pre)).cert src ∧
    (X.actMap.map FaceRec.pre).map PFace.record = X.actMap ∧
    (Γ.complex (X.actMap.map FaceRec.pre)).faces = X.actMap.map (Γ.face ∘ FaceRec.pre) := by
  refine ⟨by rw [hact], ?_, by unfold Reception.complex; rw [List.map_map]⟩
  rw [List.map_map]
  exact List.map_id' X.actMap

end Handoff

/-! ## Corollary 25.11 — Conditional downstream renewal-shell applicability -/

/-- A well-typed input to the Global Renewal-Shell Theorem. -/
def ShellInput (V E F : Type) [DecidableEq V] [DecidableEq E] [DecidableEq F] : Type :=
  { K : Cx V E F // K.ClosedShellInput }

/-- A well-typed input to its sphere-shell criterion. -/
def SphereInput (V E F : Type) [DecidableEq V] [DecidableEq E] [DecidableEq F] : Type :=
  { K : Cx V E F // K.SphereShellInput }

/-- **Corollary 25.11**, first two sentences (typing). `𝐜_sh = (1,1,1,1,1)` types
    a shell input; adding `D_Γ = 12` types a sphere-shell input, which is in
    particular a shell input. The continuation clause is `cor_25_11_continuation`
    below. The downstream classification and persistence theorems are not stated
    in Elements II and are not asserted here. -/
def SphereInput.toShellInput {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F]
    (K : SphereInput V E F) : ShellInput V E F := ⟨K.1, K.2.1⟩

theorem cor_25_11 {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F] (K : Cx V E F) :
    (K.csh = allOnes → K.ClosedShellInput) ∧ (K.csh = allOnes → K.D = sphereDefect → K.SphereShellInput) :=
  ⟨id, fun h1 h2 => ⟨h1, h2⟩⟩

/-- The typing is inhabited, through an admissible declared reception. -/
def tetraInput : SphereInput ℕ (ℕ × ℕ) ℕ :=
  ⟨(Reception.ofMaps glueV glueE id preTetra).complex preTetra, by rw [glue_tetra]; exact tetra_sphere⟩

/-! ## Corollary 25.11, continuation clause -/

section Continuation
variable {V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F]

/-- The three graph edges that one tagged boundary occurrence puts in `𝖡(K)`. -/
def occEdges (a : F × ROEdge V E) : List (Node V E F × Node V E F) :=
  [(Node.f a.1, Node.e a.2.key), (Node.e a.2.key, Node.v a.2.src), (Node.e a.2.key, Node.v a.2.dst)]

set_option linter.unusedDecidableInType false in
theorem occs_length : ∀ fs : List (TFace V E F),
    (Cx.occs ⟨fs⟩).length = 3 * fs.length
  | [] => rfl
  | f :: fs => by
    have ih := occs_length fs
    unfold Cx.occs at ih ⊢
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    change 3 + 3 * fs.length = 3 * (fs.length + 1)
    omega

set_option linter.unusedDecidableInType false in
theorem B_edges_eq : ∀ fs : List (TFace V E F),
    fs.flatMap (fun f => f.bd.flatMap fun o =>
      [(Node.f f.key, Node.e o.key), (Node.e o.key, Node.v o.src), (Node.e o.key, Node.v o.dst)]) =
    (fs.flatMap fun f => f.bd.map fun o => (f.key, o)).flatMap occEdges
  | [] => rfl
  | f :: fs => by
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_append, B_edges_eq fs]
    rfl

theorem isEmpty_congr {α : Type} : ∀ l l' : List α, l.length = l'.length → l.isEmpty = l'.isEmpty
  | [], [], _ => rfl
  | _ :: _, _ :: _, _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- `𝖡(K)` is a function of the received key sets and the tagged boundary occurrences. -/
theorem B_eq (K : Cx V E F) :
    K.B = ⟨K.VG.map Node.v ++ K.EG.map Node.e ++ K.FG.map Node.f, K.occs.flatMap occEdges⟩ := by
  unfold Cx.B Cx.occs
  rw [B_edges_eq]

/-- **Corollary 25.11, the preserved data.** What a later continuation must keep
    of the received complex: the **active incidence** `(V_Γ, E_Γ, F_Γ, Inc_V,
    Inc_E)` of Definition 25.5, the **orientation**, read as the boundary
    occurrences with their direction and face tag (`occs`, what `c_ori` reads),
    and the **closure kernel**. The book does not define "closure kernel"; it is
    read here as the vertex links `Lk_Γ(v)`, the data `c_link` closes. -/
structure Preserves (K K' : Cx V E F) : Prop where
  incidence : K'.VG = K.VG ∧ K'.EG = K.EG ∧ K'.FG = K.FG ∧
    (∀ v, K'.incV v = K.incV v) ∧ ∀ e, K'.incE e = K.incE e
  orientation : K'.occs = K.occs
  closure : ∀ v, K'.Lk v = K.Lk v

/-- **Corollary 25.11, the continuation.** A later continuation takes the export
    `fs` received by `Γ` to the export `fs'` received by `Γ'`. It preserves the
    declared global attaching reception, active incidence, orientation and closure
    kernel when `Γ' = Γ` and the received complexes satisfy `Preserves`. No
    lawfulness is assumed: the theorem below holds for every such pair. -/
def ContinuationPreserves {Vp Ep Fp R : Type} (Γ Γ' : Reception Vp Ep Fp V E F)
    (fs fs' : List (PFace Vp Ep Fp R)) : Prop :=
  Γ' = Γ ∧ Preserves (Γ.complex fs) (Γ'.complex fs')

/-- Preservation keeps all five certificate entries and the total defect. -/
theorem Preserves.csh_D {K K' : Cx V E F} (hp : Preserves K K') : K'.csh = K.csh ∧ K'.D = K.D := by
  obtain ⟨⟨hV, hE, hF, -, hIE⟩, hocc, hLk⟩ := hp
  have hlen : K'.faces.length = K.faces.length := by
    have h1 := occs_length K.faces
    have h2 := occs_length K'.faces
    have h3 : (Cx.occs ⟨K'.faces⟩).length = (Cx.occs ⟨K.faces⟩).length := by
      change K'.occs.length = K.occs.length
      rw [hocc]
    omega
  have hne : K'.cNonempty = K.cNonempty := by
    unfold Cx.cNonempty
    rw [isEmpty_congr _ _ hlen]
  refine ⟨?_, by rw [D_eq, D_eq, hV, hlen]⟩
  unfold Cx.csh Cx.cConn Cx.c2E Cx.cLink Cx.cOri
  rw [hne, B_eq K', B_eq K, hV, hE, hF, hocc]
  simp only [hIE, hLk]

/-- **Corollary 25.11, continuation clause.** If a later continuation preserves
    the declared global attaching reception, active incidence, orientation and
    closure kernel, the continued received complex is a shell input exactly when
    the earlier one is, and a sphere-shell input exactly when the earlier one is:
    the input typing of the downstream covariant-persistence theorem carries
    through. That theorem, and the renewal it decides, are downstream and are not
    stated here. -/
theorem cor_25_11_continuation {Vp Ep Fp R : Type} (Γ Γ' : Reception Vp Ep Fp V E F)
    (fs fs' : List (PFace Vp Ep Fp R)) (hc : ContinuationPreserves Γ Γ' fs fs') :
    (Γ'.complex fs').csh = (Γ.complex fs).csh ∧ (Γ'.complex fs').D = (Γ.complex fs).D ∧
    ((Γ'.complex fs').ClosedShellInput ↔ (Γ.complex fs).ClosedShellInput) ∧
    ((Γ'.complex fs').SphereShellInput ↔ (Γ.complex fs).SphereShellInput) := by
  obtain ⟨hc, hD⟩ := hc.2.csh_D
  refine ⟨hc, hD, ?_, ?_⟩
  · unfold Cx.ClosedShellInput; rw [hc]
  · unfold Cx.SphereShellInput Cx.ClosedShellInput; rw [hc, hD]

end Continuation

/-! ## Separation Rule 25.12 — Local faces, retained complexes, and shells -/

/-- **Separation Rule 25.12**, each prohibited implication refuted by an exact
    witness:
    1. a projectively closed face without two-face incidence (one face: every face
       closes, Proposition 22.2, and `c_2E = 0`);
    2. several retained faces without cyclic links (two faces on one vertex);
    3. an admissible declared attaching quotient, genuinely identifying twelve
       occurrence vertices to four, whose certificate fails;
    4. `D_Γ = 12` with a manifold entry failing (the twisted tetrahedron);
    5. a received reading renewing along `u^r` while the exact history words and
       matrices stay pairwise distinct (Theorem 24.7). -/
theorem separation_25_12 :
    ((∀ s ℓ : Bool, projClass (Word.gen s * liftedA s ℓ * inv2 (Word.gen (!s))) = projClass 1) ∧ oneFace.c2E = false) ∧
    (bowtie.faces.length = 2 ∧ bowtie.cLink = false) ∧
    (Admissible (Reception.ofMaps glueV glueE id preTwisted) pairEdges preTwisted ∧
      preV preTwisted ≠ ((Reception.ofMaps glueV glueE id preTwisted).complex preTwisted).VG ∧
      ¬ ((Reception.ofMaps glueV glueE id preTwisted).complex preTwisted).ClosedShellInput) ∧
    (tetraTwisted.D = sphereDefect ∧ ¬ tetraTwisted.ClosedShellInput) := by
  refine ⟨⟨boundary_projectively_closed, by decide⟩, ⟨rfl, by decide⟩, ⟨glue_admissible_twisted, ?_, ?_⟩, ⟨by decide, by decide⟩⟩
  · rw [glue_twisted]; decide
  · rw [glue_twisted]; decide

theorem separation_25_12_renewal {V E F : Type} (κ : Word → Cx V E F) (w u : Word) (hu : u ≠ [])
    (hren : ∀ r, κ (w ++ wpow u r) = κ w) (r t : ℕ) (hrt : r ≠ t) :
    κ (w ++ wpow u r) = κ (w ++ wpow u t) ∧ w ++ wpow u r ≠ w ++ wpow u t ∧ G (w ++ wpow u r) ≠ G (w ++ wpow u t) := by
  obtain ⟨hw, hm⟩ := renewal_no_recurrence w u hu r t hrt
  refine ⟨(hren r).trans (hren t).symm, hw, ?_⟩
  rw [G_append, G_append]; exact hm

/-! ## Boundary Statement 25.13 -/

/-- **Boundary Statement 25.13.** The last arrow is a finite exact certificate
    (Proposition 25.7). It can pass through an admissible declared reception (the
    glued tetrahedron, a sphere-shell input) and it can fail through one (the
    twisted gluing); the native one-lineage export under `Γ_id` fails it (the
    computed instance, and Theorem 25.8 in general). Which families and receptions
    first pass is downstream and not asserted. -/
theorem boundary_25_13 :
    (Admissible (Reception.ofMaps glueV glueE id preTetra) pairEdges preTetra ∧
      ((Reception.ofMaps glueV glueE id preTetra).complex preTetra).SphereShellInput) ∧
    (Admissible (Reception.ofMaps glueV glueE id preTwisted) pairEdges preTwisted ∧
      ¬ ((Reception.ofMaps glueV glueE id preTwisted).complex preTwisted).ClosedShellInput) ∧
    ¬ (lineCx iWit [0, 1, 2]).ClosedShellInput :=
  ⟨⟨glue_admissible_tetra, tetraInput.2⟩, ⟨glue_admissible_twisted, separation_25_12.2.2.1.2.2⟩,
    not_closed_of_c2E _ lineage_witness.1⟩

/-! ## Corollary 25.11 — the closure kernel read on `V_Γ` -/

section LinksOnVG
variable {V E F : Type} [DecidableEq V]

/-- Off the received vertices the link is the empty graph: a vertex that is no
    face corner contributes no link edge and no link node. -/
theorem Lk_eq_empty_of_not_mem_VG (K : Cx V E F) {v : V} (hv : v ∉ K.VG) :
    K.Lk v = { nodes := [], edges := [] } := by
  have hf : ∀ f ∈ K.faces, f.linkAt v = [] := by
    intro f hf
    have hc : ∀ u ∈ f.verts, u ≠ v := fun u hu h =>
      hv ((mem_nub v _).mpr (List.mem_flatMap.mpr ⟨f, hf, h ▸ hu⟩))
    have h0 := hc f.v0 (by simp [TFace.verts])
    have h1 := hc f.v1 (by simp [TFace.verts])
    have h2 := hc f.v2 (by simp [TFace.verts])
    unfold TFace.linkAt
    rw [if_neg h0, if_neg h1, if_neg h2]
    rfl
  have he : (K.faces.flatMap fun f => f.linkAt v) = [] :=
    List.flatMap_eq_nil_iff.mpr hf
  unfold Cx.Lk
  rw [he]
  rfl

/-- **Corollary 25.11, the closure kernel on `V_Γ`.** When the received vertex
    set is preserved, preserving every vertex link (`Preserves.closure`, `∀ v`)
    is the same as preserving the links `Lk_Γ(v)` for `v ∈ V_Γ`, the book's
    reading: off `V_Γ` both links are empty. -/
theorem closure_iff_on_VG {K K' : Cx V E F} (hV : K'.VG = K.VG) :
    (∀ v, K'.Lk v = K.Lk v) ↔ ∀ v ∈ K.VG, K'.Lk v = K.Lk v := by
  refine ⟨fun h v _ => h v, fun h v => ?_⟩
  by_cases hv : v ∈ K.VG
  · exact h v hv
  · have hv' : v ∉ K'.VG := hV ▸ hv
    rw [Lk_eq_empty_of_not_mem_VG K hv, Lk_eq_empty_of_not_mem_VG K' hv']

end LinksOnVG


#print axioms RatioSpace.Two.Shell.mem_nub
#print axioms RatioSpace.Two.Shell.nodup_nub
#print axioms RatioSpace.Two.Shell.cnt_of_not_mem
#print axioms RatioSpace.Two.Shell.cnt_of_nodup_mem
#print axioms RatioSpace.Two.Shell.sumN_add
#print axioms RatioSpace.Two.Shell.sumN_indicator
#print axioms RatioSpace.Two.Shell.sum_cnt_nub
#print axioms RatioSpace.Two.Shell.sumZ_six_sub
#print axioms RatioSpace.Two.Shell.eq_of_map_nodup
#print axioms RatioSpace.Two.Shell.find?_of_unique
#print axioms RatioSpace.Two.Shell.countP_le_of
#print axioms RatioSpace.Two.Shell.countP_lt_of
#print axioms RatioSpace.Two.Shell.countP_pos_of
#print axioms RatioSpace.Two.Shell.exists_of_all_false
#print axioms RatioSpace.Two.Shell.Graph.adj_symm
#print axioms RatioSpace.Two.Shell.Graph.Walk.trans
#print axioms RatioSpace.Two.Shell.Graph.Walk.end_mem
#print axioms RatioSpace.Two.Shell.Graph.Walk.symm
#print axioms RatioSpace.Two.Shell.Graph.mem_grow
#print axioms RatioSpace.Two.Shell.Graph.reach_sub
#print axioms RatioSpace.Two.Shell.Graph.reach_sound
#print axioms RatioSpace.Two.Shell.Graph.reach_mono
#print axioms RatioSpace.Two.Shell.Graph.reach_mono_le
#print axioms RatioSpace.Two.Shell.Graph.closed_complete
#print axioms RatioSpace.Two.Shell.Graph.closed_or_count
#print axioms RatioSpace.Two.Shell.Graph.connB_iff
#print axioms RatioSpace.Two.Shell.Graph.not_isEmpty_iff
#print axioms RatioSpace.Two.Shell.Graph.cycleB_iff
#print axioms RatioSpace.Two.Shell.corners_length
#print axioms RatioSpace.Two.Shell.D_eq
#print axioms RatioSpace.Two.Shell.cNonempty_iff
#print axioms RatioSpace.Two.Shell.cConn_iff
#print axioms RatioSpace.Two.Shell.c2E_iff
#print axioms RatioSpace.Two.Shell.cLink_iff
#print axioms RatioSpace.Two.Shell.cOri_iff
#print axioms RatioSpace.Two.Shell.closed_iff
#print axioms RatioSpace.Two.Shell.cert_exact
#print axioms RatioSpace.Two.Shell.bleW_total
#print axioms RatioSpace.Two.Shell.bleW_antisymm
#print axioms RatioSpace.Two.Shell.natLex_total
#print axioms RatioSpace.Two.Shell.natLex_antisymm
#print axioms RatioSpace.Two.Shell.qle_total
#print axioms RatioSpace.Two.Shell.qle_antisymm
#print axioms RatioSpace.Two.Shell.same_trans
#print axioms RatioSpace.Two.Shell.canon_same
#print axioms RatioSpace.Two.Shell.canon_eq_iff
#print axioms RatioSpace.Two.Shell.canon_swap
#print axioms RatioSpace.Two.Shell.ofMaps_lossless
#print axioms RatioSpace.Two.Shell.retention_of_lossless
#print axioms RatioSpace.Two.Shell.boundary_of_separation
#print axioms RatioSpace.Two.Shell.recvId_eq
#print axioms RatioSpace.Two.Shell.gid_admissible
#print axioms RatioSpace.Two.Shell.line_incE
#print axioms RatioSpace.Two.Shell.line_every_edge_once
#print axioms RatioSpace.Two.Shell.line_c2E_false
#print axioms RatioSpace.Two.Shell.not_closed_of_c2E
#print axioms RatioSpace.Two.Shell.child_linV
#print axioms RatioSpace.Two.Shell.lineFace_nondegenerate
#print axioms RatioSpace.Two.Shell.entryRec_shaped
#print axioms RatioSpace.Two.Shell.shaped_face
#print axioms RatioSpace.Two.Shell.recvId_lineage
#print axioms RatioSpace.Two.Shell.lineKey_injective
#print axioms RatioSpace.Two.Shell.gid_lineage_admissible
#print axioms RatioSpace.Two.Shell.one_lineage_fails_shell
#print axioms RatioSpace.Two.Shell.sublist_every_edge_once
#print axioms RatioSpace.Two.Shell.lineage_witness
#print axioms RatioSpace.Two.Shell.tetra_sphere
#print axioms RatioSpace.Two.Shell.tetraTwisted_cert
#print axioms RatioSpace.Two.Shell.bowtie_cert
#print axioms RatioSpace.Two.Shell.oneFace_cert
#print axioms RatioSpace.Two.Shell.ready_unique_read
#print axioms RatioSpace.Two.Shell.filter_keys_eq
#print axioms RatioSpace.Two.Shell.active_incidence
#print axioms RatioSpace.Two.Shell.active_is_view
#print axioms RatioSpace.Two.Shell.shellIn_recoverable
#print axioms RatioSpace.Two.Shell.trace_ledger_shaped
#print axioms RatioSpace.Two.Shell.traces_on_lineage
#print axioms RatioSpace.Two.Shell.cor_25_9_unresolved
#print axioms RatioSpace.Two.Shell.cor_25_9_side
#print axioms RatioSpace.Two.Shell.cor_25_9_lone
#print axioms RatioSpace.Two.Shell.cor_25_9_release
#print axioms RatioSpace.Two.Shell.ek_comm
#print axioms RatioSpace.Two.Shell.glue_admissible
#print axioms RatioSpace.Two.Shell.glue_tetra
#print axioms RatioSpace.Two.Shell.glue_twisted
#print axioms RatioSpace.Two.Shell.glue_admissible_tetra
#print axioms RatioSpace.Two.Shell.glue_admissible_twisted
#print axioms RatioSpace.Two.Shell.handoff_complete
#print axioms RatioSpace.Two.Shell.cor_25_11
#print axioms RatioSpace.Two.Shell.receivedShellInput_iff
#print axioms RatioSpace.Two.Shell.occs_length
#print axioms RatioSpace.Two.Shell.B_edges_eq
#print axioms RatioSpace.Two.Shell.isEmpty_congr
#print axioms RatioSpace.Two.Shell.B_eq
#print axioms RatioSpace.Two.Shell.Preserves.csh_D
#print axioms RatioSpace.Two.Shell.cor_25_11_continuation
#print axioms RatioSpace.Two.Shell.separation_25_12
#print axioms RatioSpace.Two.Shell.separation_25_12_renewal
#print axioms RatioSpace.Two.Shell.boundary_25_13
#print axioms RatioSpace.Two.Shell.Lk_eq_empty_of_not_mem_VG
#print axioms RatioSpace.Two.Shell.closure_iff_on_VG

end Shell
end Two
end RatioSpace
