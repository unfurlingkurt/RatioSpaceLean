/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S03.Walk
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
/-!
  Elements I §8 — Winding and closure.

  Definitions 8.1 through 8.4, Proposition 8.1 and Standard Result 8.2. This is
  the section Elements II's Import 1.6 depends on: imbalance, acyclicity and
  `ψ₁₂`.

  Five things here are sharper than the prose, and each is noted at its theorem:

    * **On bare words read from `F_∅`, the three forms of closure are two.** Def
      8.2 warns that a word return, a matrix return and a quotient return are
      different. On bare words two of them are the same: freeness makes
      `G u = G v` equivalent to `u = v`, so the word-level and matrix-level
      closures are one relation. The quotient level is strictly coarser, with a
      witness. Def 8.2 names histories and accumulated matrices; on histories
      `(F₀, w)` word return and accumulated-matrix return differ inside `ℳ₊`
      (`matrixEq_not_wordEq`, `Walk.lean`).

    * **Siblings never share a closure residue.** Def 8.3 says equality of a
      closure residue does not by itself attach a sibling edge. For siblings the
      residues are never equal: they differ by exactly `2`, and `2 ≠ 0` in
      `ℤ/12ℤ`. So the caution is not about a coincidence to be ruled out, it is
      about a coincidence that cannot happen.

    * **Standard Result 8.2 splits into a character and a derivation.** The
      book imports the abelianization `SL(2,ℤ)_ab ≅ ℤ/12ℤ` from Serre. What it
      reads off is a character: a map additive on the unimodular shell with
      `ψ₁₂(T) = 1`. `Closure12` is that character, not the isomorphism, and it
      is inhabited: `Closure12.congruence` is built here, through
      `SL(2,ℤ/4) × SL(2,ℤ/3)`, and checked on finite tables.
      Every exact value the book reads off it, `ψ₁₂(S) = 9`,
      `ψ₁₂(-I) = 6`, `ψ₁₂(ST) = 10`, `ψ₁₂((ST)³) = 6`, `ψ₁₂((ST)⁶) = 0`,
      `ψ₁₂(L) = 11`, and `ψ₁₂(G(w)) ≡ b(w)`, is *proved* for every such
      character rather than quoted alongside it. The isomorphism itself (that
      the character's kernel is the commutator subgroup) is not stated; no
      value the book reads needs it.

    * **The reading is unique on the positive monoid.** `map_G` says any two
      closure readings satisfying the hypothesis agree on all of `ℳ₊`. The book
      fixes `ψ₁₂` by a convention; the convention turns out to determine it.

    * **Def 8.3's three definitions are declared data** (`ReceivedClosure`,
      `ReceivedEdge`, `ReceivedCell`). The sibling triangle is a cell once its
      edge is attached (`siblingCell`) and only then (`siblingTriangle_needs_edge`);
      the twelve-class closure, once declared, joins `LR` and `RL` and never a
      sibling pair (`psi12Closure_edges`).

  Everything is computable. No `sorry`, no `axiom`.
-/

namespace RatioSpace

open Mat2 Word Frame

namespace Word

/-! ## Definition 8.1 — Word imbalance -/

/-- **Definition 8.1.** `b(w) = #R(w) − #L(w)`. A property of the chosen word. -/
def bal (w : Word) : ℤ := (w.count true : ℤ) - (w.count false : ℤ)

@[simp] theorem bal_nil : bal [] = 0 := by simp [bal]

theorem bal_cons (b : Bool) (w : Word) :
    bal (b :: w) = (if b then (1 : ℤ) else -1) + bal w := by
  cases b <;> simp [bal] <;> ring

@[simp] theorem bal_true (w : Word) : bal (true :: w) = 1 + bal w := by
  simp [bal_cons]

@[simp] theorem bal_false (w : Word) : bal (false :: w) = -1 + bal w := by
  simp [bal_cons]

/-- Imbalance is additive along concatenation. -/
theorem bal_append (u v : Word) : bal (u ++ v) = bal u + bal v := by
  simp [bal, List.count_append]; ring

theorem bal_snoc (w : Word) (b : Bool) :
    bal (w ++ [b]) = bal w + (if b then (1 : ℤ) else -1) := by
  cases b <;> simp [bal_append, bal_cons]

/-- **The book's caution does not bite on `ℳ₊`.** Def 8.1 warns that imbalance is
    presentation-level and "not automatically a group invariant under arbitrary
    changes of word presentation". Inside the positive monoid there are no
    arbitrary changes of presentation: freeness leaves one word per matrix, so
    imbalance *is* a matrix invariant there. The warning is about presentations
    that leave `ℳ₊`, and this is where it starts to apply. -/
theorem bal_of_G_eq {u v : Word} (h : G u = G v) : bal u = bal v := by
  rw [G_inj h]

/-- **Two siblings differ in imbalance by exactly two.** Used twice below. -/
theorem bal_sibling (u : Word) :
    bal (u ++ [true]) - bal (u ++ [false]) = 2 := by
  simp [bal_snoc]

/-! ## Definition 8.2 / Standard Result 8.2 — the twelve-class closure on words

    `ψ₁₂` restricted to the positive monoid needs no imported theorem: it is the
    imbalance read modulo twelve, and it is computable. -/

/-- **Standard Result 8.2, positive half.** `ψ₁₂(G(w)) = b(w) mod 12`, taken here
    as the definition on words and recovered from the abelianization below. -/
def psi12 (w : Word) : ZMod 12 := (bal w : ZMod 12)

@[simp] theorem psi12_nil : psi12 [] = 0 := by simp [psi12]

theorem psi12_append (u v : Word) : psi12 (u ++ v) = psi12 u + psi12 v := by
  simp [psi12, bal_append]

theorem psi12_cons (b : Bool) (w : Word) :
    psi12 (b :: w) = (if b then (1 : ZMod 12) else 11) + psi12 w := by
  have h11 : ((-1 : ℤ) : ZMod 12) = 11 := by decide +kernel
  cases b
  · simp only [psi12, bal_false, Bool.false_eq_true, ↓reduceIte, Int.cast_add, h11]
  · simp only [psi12, bal_true, ↓reduceIte, Int.cast_add, Int.cast_one]

@[simp] theorem psi12_R : psi12 [true] = 1 := by decide +kernel

@[simp] theorem psi12_L : psi12 [false] = 11 := by decide +kernel

/-- `ψ₁₂(L) = −1`, the book's own form of the same value. -/
theorem psi12_L_neg : psi12 [false] = -1 := by decide +kernel

/-! ## Proposition 8.1 — Raw positive ancestry is acyclic -/

/-- **Proposition 8.1.** The raw ancestry edge: one continuation generator. -/
def Anc (u v : Word) : Prop := ∃ b : Bool, v = u ++ [b]

instance : DecidableRel Anc := fun u v => by
  unfold Anc; infer_instance

theorem anc_length {u v : Word} (h : Anc u v) : v.length = u.length + 1 := by
  obtain ⟨b, rfl⟩ := h; simp

/-- **Every nonroot word has exactly one immediate prefix.** The book's proof
    leans on this and does not state it. -/
theorem anc_parent_unique {u u' v : Word} (h : Anc u v) (h' : Anc u' v) : u = u' := by
  obtain ⟨b, rfl⟩ := h
  obtain ⟨b', hb⟩ := h'
  have := congrArg List.dropLast hb
  simpa using this

theorem anc_irrefl (w : Word) : ¬ Anc w w := by
  intro h; have := anc_length h; omega

/-- Reachability in raw ancestry implies the prefix relation. The converse is
    `isPrefix_reflTransGen`; both together are `reflTransGen_iff_isPrefix`. -/
theorem reflTransGen_isPrefix {u v : Word} (h : Relation.ReflTransGen Anc u v) :
    u <+: v := by
  induction h with
  | refl => exact List.prefix_rfl
  | tail _ hst ih =>
      obtain ⟨b, rfl⟩ := hst
      exact ih.trans (List.prefix_append _ _)

/-- The other direction: every prefix is reached by raw ancestry. -/
theorem isPrefix_reflTransGen {u v : Word} (h : u <+: v) :
    Relation.ReflTransGen Anc u v := by
  obtain ⟨t, rfl⟩ := h
  induction t using List.reverseRecOn with
  | nil => simpa using Relation.ReflTransGen.refl
  | append_singleton t b ih =>
      exact ih.tail ⟨b, by simp⟩

/-- **Reachability in raw ancestry is exactly the prefix relation**, both directions. -/
theorem reflTransGen_iff_isPrefix {u v : Word} :
    Relation.ReflTransGen Anc u v ↔ u <+: v :=
  ⟨reflTransGen_isPrefix, isPrefix_reflTransGen⟩

/-- **Rooted.** Every word is reached from the empty word `ε` by raw ancestry. -/
theorem root_reaches (v : Word) : Relation.ReflTransGen Anc [] v :=
  isPrefix_reflTransGen (List.nil_prefix)

/-- **Every nonroot word has a parent.** With `anc_parent_unique`, exactly one; the
    root has none (`not_anc_root`). -/
theorem anc_parent_exists {v : Word} (hv : v ≠ []) : ∃ u, Anc u v :=
  ⟨v.dropLast, v.getLast hv, (List.dropLast_append_getLast hv).symm⟩

theorem not_anc_root (u : Word) : ¬ Anc u [] := by
  rintro ⟨b, h⟩
  cases u <;> cases h

/-- **Binary.** The children of `u` are exactly `u ++ [false]` and `u ++ [true]`,
    and they are two. -/
theorem anc_children (u v : Word) : Anc u v ↔ v = u ++ [false] ∨ v = u ++ [true] := by
  constructor
  · rintro ⟨b, rfl⟩; cases b <;> simp
  · rintro (rfl | rfl)
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

theorem children_ne (u : Word) : u ++ [false] ≠ u ++ [true] := by simp

/-- **Proposition 8.1, the tree stated whole.** The raw positive ancestry graph is a
    rooted binary tree: the root `ε` has no parent, every other word has exactly one,
    every word is reached from `ε`, every word has exactly two children, and they are
    distinct. Acyclicity is `acyclic` below. -/
theorem rooted_binary_tree :
    (∀ u, ¬ Anc u []) ∧
    (∀ v, v ≠ [] → ∃! u, Anc u v) ∧
    (∀ v, Relation.ReflTransGen Anc [] v) ∧
    (∀ u v, Anc u v ↔ v = u ++ [false] ∨ v = u ++ [true]) ∧
    (∀ u, u ++ [false] ≠ u ++ [true]) := by
  refine ⟨not_anc_root, fun v hv => ?_, root_reaches, anc_children, children_ne⟩
  obtain ⟨u, hu⟩ := anc_parent_exists hv
  exact ⟨u, hu, fun u' hu' => anc_parent_unique hu' hu⟩

theorem transGen_length {u v : Word} (h : Relation.TransGen Anc u v) :
    u.length < v.length := by
  induction h with
  | single hst => have := anc_length hst; omega
  | tail _ hst ih => have := anc_length hst; omega

/-- **Proposition 8.1.** No native cycle: the raw positive ancestry graph is a
    rooted binary tree, so no word reaches itself. -/
theorem acyclic (w : Word) : ¬ Relation.TransGen Anc w w := by
  intro h; have := transGen_length h; omega

/-! ## Definition 8.3 — Received closure and attached cells -/

/-- **Definition 8.3.** The sibling edge `uL ↔ uR` is not a raw edge, and neither
    sibling reaches the other. This is the exact content of "continuation
    generates exact ancestry, reception may close that ancestry": the triangle
    has no third side until one is attached. -/
theorem sibling_not_reachable (u : Word) :
    ¬ Relation.ReflTransGen Anc (u ++ [false]) (u ++ [true]) := by
  intro h
  have hp := reflTransGen_isPrefix h
  have hlen : (u ++ [false]).length = (u ++ [true]).length := by simp
  have := hp.eq_of_length hlen
  simp at this

/-- **Sharper than the book.** Def 8.3 says equality of a closure residue does
    not by itself attach the sibling edge. For siblings the residues are never
    equal at all: they differ by exactly `2`, and `2 ≠ 0` in `ℤ/12ℤ`. So no
    reception rule can ever be tempted by a residue coincidence between
    siblings — there are none. -/
theorem psi12_sibling_ne (u : Word) :
    psi12 (u ++ [true]) ≠ psi12 (u ++ [false]) := by
  intro h
  have hb : bal (u ++ [true]) = bal (u ++ [false]) + 2 := by
    have := bal_sibling u; omega
  simp only [psi12, hb] at h
  push_cast at h
  -- `x + 2 = x` in `ZMod 12` forces `2 = 0`, refuted by reading `ZMod.val`;
  -- no `decide`.
  have h2 : (2 : ZMod 12) = 0 := by linear_combination h
  have h3 : (2 : ZMod 12).val = (0 : ZMod 12).val := congrArg ZMod.val h2
  change 2 = 0 at h3
  exact absurd h3 (by omega)

/-- **And the converse witness.** Two words that are not siblings, are not
    reachable from each other, carry different matrices, and share a residue.
    Residue equality holds without attaching anything. -/
theorem residue_eq_without_edge :
    psi12 [false, true] = psi12 [true, false] ∧
    G [false, true] ≠ G [true, false] ∧
    ¬ Relation.ReflTransGen Anc [false, true] [true, false] := by
  refine ⟨by decide +kernel, LR_ne_RL, ?_⟩
  intro h
  have hp := reflTransGen_isPrefix h
  have := hp.eq_of_length (by simp)
  simp at this

/-! ### Definition 8.3, the three definitions

    The book defines three things: a received closure, a received closure edge and
    a received closure cell. All three are declared data. Nothing below derives an
    edge or a cell from a residue; each one is attached by an explicit relation. -/

/-- **Definition 8.3, received closure.** A declared equivalence `∼_Λ` on words,
    the vertex set of Prop 8.1. The relation is a field: a received closure exists only when one is
    declared. The quotient is `Quot rel`; the words themselves are untouched, so
    both identified histories stay in the complete record (`received_retains`). -/
structure ReceivedClosure where
  rel : Word → Word → Prop
  equiv : Equivalence rel

/-- **Definition 8.3, received closure edge.** A relation admitted by `adm`
    between two distinct histories that no raw parent-child edge joins, in either
    direction. -/
def ReceivedEdge (adm : Word → Word → Prop) (u v : Word) : Prop :=
  adm u v ∧ u ≠ v ∧ ¬ Anc u v ∧ ¬ Anc v u

/-- One side of a boundary: a raw continuation edge in either orientation, or a
    received closure edge in either orientation. -/
def CellStep (adm : Word → Word → Prop) (u v : Word) : Prop :=
  Anc u v ∨ Anc v u ∨ ReceivedEdge adm u v ∨ ReceivedEdge adm v u

/-- **Definition 8.3, received closure cell.** An explicitly attached finite
    boundary cycle made from raw continuation edges and received closure edges:
    at least three distinct histories, each joined to the next and the last to the
    first. The cell is a record, so it is attached by being given. -/
structure ReceivedCell (adm : Word → Word → Prop) where
  boundary : List Word
  three_le : 3 ≤ boundary.length
  nodup : boundary.Nodup
  closed : List.IsChain (CellStep adm) (boundary ++ boundary.take 1)

/-- **Retention.** Identifying two histories in the receiving quotient does not
    make them equal as histories: both remain in the complete record. -/
theorem received_retains (Λ : ReceivedClosure) {u v : Word} (huv : u ≠ v)
    (h : Λ.rel u v) : Quot.mk Λ.rel u = Quot.mk Λ.rel v ∧ u ≠ v :=
  ⟨Quot.sound h, huv⟩

/-- The attaching relation for the sibling edge `uL ↔ uR` beneath `u`. -/
def siblingAttach (u : Word) (a b : Word) : Prop :=
  a = u ++ [false] ∧ b = u ++ [true]

/-- Siblings are never joined by a raw edge in either direction. -/
theorem not_anc_sibling (u : Word) :
    ¬ Anc (u ++ [false]) (u ++ [true]) ∧ ¬ Anc (u ++ [true]) (u ++ [false]) := by
  constructor <;> intro h <;> have := anc_length h <;>
    simp only [List.length_append, List.length_singleton] at this <;> omega

/-- The admitted sibling edge is a received closure edge. -/
theorem siblingAttach_edge (u : Word) :
    ReceivedEdge (siblingAttach u) (u ++ [false]) (u ++ [true]) :=
  ⟨⟨rfl, rfl⟩, children_ne u, (not_anc_sibling u).1, (not_anc_sibling u).2⟩

/-- **Definition 8.3, the book's triangle.** Once the sibling edge is attached,
    the raw edges `u → uL`, `u → uR` and the received edge `uL ↔ uR` bound a cell,
    beneath every prefix `u`. Without the attachment the third side is not there
    (`sibling_not_reachable`). -/
def siblingCell (u : Word) : ReceivedCell (siblingAttach u) where
  boundary := [u, u ++ [false], u ++ [true]]
  three_le := Nat.le_refl _
  nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
    refine ⟨?_, children_ne u⟩
    rintro (h | h) <;> have := congrArg List.length h <;>
      simp only [List.length_append, List.length_singleton] at this <;> omega
  closed := by
    simp only [List.cons_append, List.take_succ_cons, List.take_zero, List.nil_append,
      List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨Or.inl ⟨false, rfl⟩, Or.inr (Or.inr (Or.inl (siblingAttach_edge u))),
      Or.inr (Or.inl ⟨true, rfl⟩)⟩

/-- **"Only after" the sibling edge is attached.** Any cell whose boundary is the
    sibling triangle `[u, uL, uR]` has the sibling edge admitted, in one
    orientation or the other: raw edges alone never close it. -/
theorem siblingTriangle_needs_edge {adm : Word → Word → Prop} (c : ReceivedCell adm)
    (u : Word) (hb : c.boundary = [u, u ++ [false], u ++ [true]]) :
    adm (u ++ [false]) (u ++ [true]) ∨ adm (u ++ [true]) (u ++ [false]) := by
  have hc := c.closed
  rw [hb] at hc
  simp only [List.cons_append, List.take_succ_cons, List.take_zero, List.nil_append,
    List.isChain_cons_cons] at hc
  obtain ⟨-, h, -⟩ := hc
  rcases h with h | h | h | h
  · exact absurd h (not_anc_sibling u).1
  · exact absurd h (not_anc_sibling u).2
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- **A received closure from the twelve-class reading.** Declaring `∼` as equal
    `ψ₁₂` is an equivalence on histories, so it is a received closure once declared. -/
def psi12Closure : ReceivedClosure where
  rel u v := psi12 u = psi12 v
  equiv := ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

/-- **The twelve-class closure, both ways.** Declared, it identifies `LR` and `RL`,
    which stay distinct in the record and are joined by a received closure edge.
    It never admits a sibling edge, so this closure attaches no sibling triangle. -/
theorem psi12Closure_edges :
    Quot.mk psi12Closure.rel [false, true] = Quot.mk psi12Closure.rel [true, false] ∧
    ([false, true] : Word) ≠ [true, false] ∧
    ReceivedEdge psi12Closure.rel [false, true] [true, false] ∧
    ∀ u, ¬ ReceivedEdge psi12Closure.rel (u ++ [false]) (u ++ [true]) := by
  have hne : ([false, true] : Word) ≠ [true, false] := by simp
  have hanc : ∀ a b : Word, a.length = b.length → ¬ Anc a b := fun a b hl h => by
    have := anc_length h; omega
  refine ⟨(received_retains psi12Closure hne residue_eq_without_edge.1).1, hne,
    ⟨residue_eq_without_edge.1, hne, hanc _ _ rfl, hanc _ _ rfl⟩, fun u h => ?_⟩
  exact psi12_sibling_ne u h.1.symm

end Word

open Word

/-! ## Definition 8.2 — Closure maps, and how many of them there really are -/

/-- **Definition 8.2.** A closure map with its domain stated as a type. The
    definition's whole content is that the domain is declared, so it is a field
    of the structure rather than a convention. -/
structure ClosureMap (H K : Type) where
  kappa : H → K

/-- Word-level return. -/
def wordClosure : ClosureMap Word Word := ⟨id⟩

/-- Matrix-level return on bare words: `G(w)`, read from `F_∅`, no start frame. -/
def matrixClosure : ClosureMap Word Mat2 := ⟨G⟩

/-- Quotient-level return. -/
def quotientClosure : ClosureMap Word (ZMod 12) := ⟨psi12⟩

/-- **On bare words read from `F_∅`, the word return and the matrix return are one
    relation.** The book lists three forms of closure and says they differ. On
    bare words two of the three coincide, by freeness of `G` on the positive
    monoid, and only the quotient level is genuinely coarser. This is not Def
    8.2's history domain: on histories `(F₀, w)` with the accumulated matrix,
    word return and matrix return differ inside `ℳ₊` (`matrixEq_not_wordEq`,
    `Walk.lean`). Off `ℳ₊` the book's three-way warning stands. -/
theorem wordClosure_iff_matrixClosure (u v : Word) :
    wordClosure.kappa u = wordClosure.kappa v ↔
      matrixClosure.kappa u = matrixClosure.kappa v :=
  ⟨fun h => by simp [matrixClosure, show u = v from h],
   fun h => G_inj h⟩

/-- And the quotient level is strictly coarser than both. -/
theorem quotientClosure_strictly_coarser :
    quotientClosure.kappa [false, true] = quotientClosure.kappa [true, false] ∧
    matrixClosure.kappa [false, true] ≠ matrixClosure.kappa [true, false] :=
  ⟨by decide +kernel, LR_ne_RL⟩

/-! ## Standard Result 8.2 — the canonical twelve-class matrix closure

    `SL(2,ℤ)_ab ≅ ℤ/12ℤ` is Serre 1973, chap. VII sec. 1, and is not reproved
    here. The book uses it for one thing: a twelve-class character with
    `ψ₁₂(T) = 1`. That character is a **structure**, never a Lean `axiom`, and
    one is constructed below (`Closure12.congruence`), so no theorem stated for
    every `Closure12` rests on trust. Everything the book reads off is derived
    from the structure's two laws. -/

/-- **Standard Result 8.2, the character.** A twelve-class closure reading:
    additive on the unimodular shell, normalised by `ψ₁₂(T) = 1`.

    This is a character of `SL(2,ℤ)`, not the isomorphism `SL(2,ℤ)_ab ≅ ℤ/12ℤ`:
    it does not say the kernel is the commutator subgroup, and nothing below
    needs that. It is inhabited by `Closure12.congruence` (below). Two such
    characters agree on `ℳ₊` (`map_G`); agreement on all of `SL(2,ℤ)` would need
    `S` and `T` to generate it, which is not stated here. -/
structure Closure12 where
  psi : Mat2 → ZMod 12
  map_mul : ∀ {M N : Mat2}, M.det = 1 → N.det = 1 → psi (M * N) = psi M + psi N
  map_T : psi T = 1

namespace Closure12

variable (A : Closure12)

theorem map_one : A.psi 1 = 0 := by
  have h := A.map_mul (M := 1) (N := 1) (by decide) (by decide)
  rw [one_mul'] at h
  linear_combination -h

theorem map_inv {M N : Mat2} (hM : M.det = 1) (hN : N.det = 1) (h : M * N = 1) :
    A.psi N = - A.psi M := by
  have hmn := A.map_mul hM hN
  rw [h, A.map_one] at hmn
  linear_combination -hmn

/-- **`ψ₁₂(S) = 9`, derived.** The book gives the derivation in prose — `2s =
    3(s+t)` with `t = 1` — from `S² = (ST)³`. Here the group relation is checked
    on the matrices by `decide` and the residue arithmetic is finished by
    exhausting `ℤ/12ℤ`. -/
theorem map_S : A.psi S = 9 := by
  have hS : S.det = 1 := by decide
  have hT : T.det = 1 := by decide
  have hST : (S * T).det = 1 := by decide
  have hSTST : ((S * T) * (S * T)).det = 1 := by decide
  have heq : S * S = (S * T) * (S * T) * (S * T) := by decide
  have h1 : A.psi S + A.psi S = A.psi ((S * T) * (S * T) * (S * T)) := by
    rw [← A.map_mul hS hS, heq]
  rw [A.map_mul hSTST hST, A.map_mul hST hST, A.map_mul hS hT, A.map_T] at h1
  -- `2s = 3s + 3` in `ZMod 12` gives `s = -3 = 9` by a ring identity and kernel
  -- evaluation; `decide` over all of `ZMod 12` reaches `Classical.choice` through the
  -- `Fintype (ZMod 12)` instance (its decidable equality is axiom-free).
  have hs : A.psi S = -3 := by linear_combination -h1
  rw [hs]; rfl

/-- `ψ₁₂(−I) = ψ₁₂(S²) = 6`. -/
theorem map_neg_one : A.psi (-1) = 6 := by
  have hS : S.det = 1 := by decide
  have h : A.psi (S * S) = A.psi S + A.psi S := A.map_mul hS hS
  rw [neg_one_eq_S_sq, A.map_S] at h
  rw [h]; rfl

/-- `ψ₁₂(ST) = 10`. -/
theorem map_ST : A.psi (S * T) = 10 := by
  have hS : S.det = 1 := by decide
  have hT : T.det = 1 := by decide
  rw [A.map_mul hS hT, A.map_S, A.map_T]; rfl

/-- **`ψ₁₂((ST)³) = 6`.** The book lists it among the useful exact values; it is
    `ψ₁₂(−I)`, since `(ST)³ = −I` (`neg_one_eq_ST_cubed`). -/
theorem map_ST_cubed : A.psi ((S * T) * (S * T) * (S * T)) = 6 := by
  rw [neg_one_eq_ST_cubed, A.map_neg_one]

/-- **`ψ₁₂((ST)⁶) = 0`.** Twice `ψ₁₂((ST)³)`, and `6 + 6 = 0` in `ℤ/12ℤ`. -/
theorem map_ST_sixth :
    A.psi (((S * T) * (S * T) * (S * T)) * ((S * T) * (S * T) * (S * T))) = 0 := by
  have h : ((S * T) * (S * T) * (S * T)).det = 1 := by decide
  rw [A.map_mul h h, A.map_ST_cubed]; rfl

/-- `ψ₁₂(R) = 1`, since `T := R`. -/
theorem map_R : A.psi R = 1 := A.map_T

/-- **`ψ₁₂(L) = 11`, derived.** The book asserts `L = S T⁻¹ S⁻¹` and reads the
    value off it. The matrix identity is checked here rather than assumed. -/
theorem map_L : A.psi L = 11 := by
  have hS : S.det = 1 := by decide
  have hT : T.det = 1 := by decide
  have hTi : (inv2 T).det = 1 := by decide
  have hSi : (inv2 S).det = 1 := by decide
  have hSTi : (S * inv2 T).det = 1 := by decide
  have hL : L = S * inv2 T * inv2 S := by decide
  have hTinv : A.psi (inv2 T) = - A.psi T := A.map_inv hT hTi (by decide)
  have hSinv : A.psi (inv2 S) = - A.psi S := A.map_inv hS hSi (by decide)
  rw [hL, A.map_mul hSTi hSi, A.map_mul hS hTi, hTinv, hSinv, A.map_T]
  ring_nf
  decide +kernel

/-- **Standard Result 8.2's conclusion, proved.** `ψ₁₂(G(w)) ≡ b(w) (mod 12)`
    for every positive word.

    This is what Elements II Import 1.6 consumes, and it is also a uniqueness
    statement the book does not make: any two closure readings satisfying the
    hypothesis agree on the whole of `ℳ₊`. The convention `ψ₁₂(T) = 1` does not
    merely name a value, it determines the map on the positive monoid. -/
theorem map_G (w : Word) : A.psi (G w) = psi12 w := by
  induction w with
  | nil => simpa using A.map_one
  | cons b w ih =>
      have hb : (gen b).det = 1 := by cases b <;> decide
      rw [G_cons, A.map_mul hb (det_G w), ih, psi12_cons]
      cases b
      · rw [gen_false, A.map_L]; simp
      · rw [gen_true, A.map_R]; simp

end Closure12

/-! ## Standard Result 8.2 — a twelve-class character, constructed

    The character is read through reduction mod 4 and mod 3. `SL(2,ℤ/4)` (48
    elements) carries a character to `ℤ/4` with `T ↦ 1`, and `SL(2,ℤ/3)` (24
    elements) one to `ℤ/3` with `T ↦ 1`; both are written out as tables and
    their additivity is checked on every pair by the kernel. Recombined by
    `ℤ/12 ≅ ℤ/4 × ℤ/3` (`x ↦ 9x`, `y ↦ 4y`), they give a `Closure12`. -/

namespace Mat2

/-- Entrywise residue modulo `n`. -/
def redMod (n : ℤ) (M : Mat2) : Mat2 := ⟨M.a % n, M.b % n, M.c % n, M.d % n⟩

/-- Residues of a sum of products are the residues of the residues'. -/
theorem emod_mul_add (n a b c d : ℤ) :
    (a * b + c * d) % n = (a % n * (b % n) + c % n * (d % n)) % n := by
  rw [Int.add_emod, Int.mul_emod a b, Int.mul_emod c d]
  conv_rhs => rw [Int.add_emod, Int.mul_emod (a % n), Int.mul_emod (c % n)]
  simp only [Int.emod_emod]

/-- The same for a difference, which is the determinant. -/
theorem emod_mul_sub (n a b c d : ℤ) :
    (a * b - c * d) % n = (a % n * (b % n) - c % n * (d % n)) % n := by
  rw [Int.sub_emod, Int.mul_emod a b, Int.mul_emod c d]
  conv_rhs => rw [Int.sub_emod, Int.mul_emod (a % n), Int.mul_emod (c % n)]
  simp only [Int.emod_emod]

theorem redMod_mul (n : ℤ) (M N : Mat2) :
    redMod n (M * N) = redMod n (redMod n M * redMod n N) := by
  cases M with | mk a b c d =>
  cases N with | mk e f g h =>
  change Mat2.mk ((a * e + b * g) % n) ((a * f + b * h) % n) ((c * e + d * g) % n)
      ((c * f + d * h) % n) =
    Mat2.mk ((a % n * (e % n) + b % n * (g % n)) % n) ((a % n * (f % n) + b % n * (h % n)) % n)
      ((c % n * (e % n) + d % n * (g % n)) % n) ((c % n * (f % n) + d % n * (h % n)) % n)
  rw [emod_mul_add n a e b g, emod_mul_add n a f b h, emod_mul_add n c e d g,
    emod_mul_add n c f d h]

theorem redMod_det (n : ℤ) (M : Mat2) : (redMod n M).det % n = M.det % n := by
  cases M with | mk a b c d =>
  exact (emod_mul_sub n a d b c).symm

end Mat2

namespace Closure12

/-- The value a finite table gives a residue matrix (`0` off the table). -/
def tableValue (tab : List (Mat2 × ℕ)) (M : Mat2) : ℕ :=
  ((tab.find? (fun p => p.1 == M)).map Prod.snd).getD 0

/-- The residue matrices a table covers. -/
def tableKeys (tab : List (Mat2 × ℕ)) : List Mat2 := tab.map Prod.fst

/-- Every determinant-one residue matrix mod `n` is covered by `tab`. -/
def TableComplete (n : ℕ) (tab : List (Mat2 × ℕ)) : Bool :=
  (List.range n).all fun a => (List.range n).all fun b =>
    (List.range n).all fun c => (List.range n).all fun d =>
      (((a : ℤ) * d - b * c) % n != 1) || (tableKeys tab).contains ⟨a, b, c, d⟩

/-- `tab` is additive mod `n` on every pair of covered matrices. -/
def TableAdditive (n : ℕ) (tab : List (Mat2 × ℕ)) : Bool :=
  (tableKeys tab).all fun P => (tableKeys tab).all fun Q =>
    tableValue tab (Mat2.redMod n (P * Q)) == (tableValue tab P + tableValue tab Q) % n

/-- The character `SL(2,ℤ/4) → ℤ/4` with `T ↦ 1` (and `S ↦ 1`), all 48 elements. -/
def tab4 : List (Mat2 × ℕ) :=
  [(⟨0, 1, 3, 0⟩, 3),
   (⟨0, 1, 3, 1⟩, 2),
   (⟨0, 1, 3, 2⟩, 1),
   (⟨0, 1, 3, 3⟩, 0),
   (⟨0, 3, 1, 0⟩, 1),
   (⟨0, 3, 1, 1⟩, 2),
   (⟨0, 3, 1, 2⟩, 3),
   (⟨0, 3, 1, 3⟩, 0),
   (⟨1, 0, 0, 1⟩, 0),
   (⟨1, 0, 1, 1⟩, 3),
   (⟨1, 0, 2, 1⟩, 2),
   (⟨1, 0, 3, 1⟩, 1),
   (⟨1, 1, 0, 1⟩, 1),
   (⟨1, 1, 1, 2⟩, 0),
   (⟨1, 1, 2, 3⟩, 3),
   (⟨1, 1, 3, 0⟩, 2),
   (⟨1, 2, 0, 1⟩, 2),
   (⟨1, 2, 1, 3⟩, 1),
   (⟨1, 2, 2, 1⟩, 0),
   (⟨1, 2, 3, 3⟩, 3),
   (⟨1, 3, 0, 1⟩, 3),
   (⟨1, 3, 1, 0⟩, 2),
   (⟨1, 3, 2, 3⟩, 1),
   (⟨1, 3, 3, 2⟩, 0),
   (⟨2, 1, 1, 1⟩, 0),
   (⟨2, 1, 1, 3⟩, 2),
   (⟨2, 1, 3, 0⟩, 1),
   (⟨2, 1, 3, 2⟩, 3),
   (⟨2, 3, 1, 0⟩, 3),
   (⟨2, 3, 1, 2⟩, 1),
   (⟨2, 3, 3, 1⟩, 0),
   (⟨2, 3, 3, 3⟩, 2),
   (⟨3, 0, 0, 3⟩, 2),
   (⟨3, 0, 1, 3⟩, 3),
   (⟨3, 0, 2, 3⟩, 0),
   (⟨3, 0, 3, 3⟩, 1),
   (⟨3, 1, 0, 3⟩, 1),
   (⟨3, 1, 1, 2⟩, 2),
   (⟨3, 1, 2, 1⟩, 3),
   (⟨3, 1, 3, 0⟩, 0),
   (⟨3, 2, 0, 3⟩, 0),
   (⟨3, 2, 1, 1⟩, 1),
   (⟨3, 2, 2, 3⟩, 2),
   (⟨3, 2, 3, 1⟩, 3),
   (⟨3, 3, 0, 3⟩, 3),
   (⟨3, 3, 1, 0⟩, 0),
   (⟨3, 3, 2, 1⟩, 1),
   (⟨3, 3, 3, 2⟩, 2)]

/-- The character `SL(2,ℤ/3) → ℤ/3` with `T ↦ 1` (and `S ↦ 0`), all 24 elements. -/
def tab3 : List (Mat2 × ℕ) :=
  [(⟨0, 1, 2, 0⟩, 0),
   (⟨0, 1, 2, 1⟩, 2),
   (⟨0, 1, 2, 2⟩, 1),
   (⟨0, 2, 1, 0⟩, 0),
   (⟨0, 2, 1, 1⟩, 1),
   (⟨0, 2, 1, 2⟩, 2),
   (⟨1, 0, 0, 1⟩, 0),
   (⟨1, 0, 1, 1⟩, 2),
   (⟨1, 0, 2, 1⟩, 1),
   (⟨1, 1, 0, 1⟩, 1),
   (⟨1, 1, 1, 2⟩, 0),
   (⟨1, 1, 2, 0⟩, 2),
   (⟨1, 2, 0, 1⟩, 2),
   (⟨1, 2, 1, 0⟩, 1),
   (⟨1, 2, 2, 2⟩, 0),
   (⟨2, 0, 0, 2⟩, 0),
   (⟨2, 0, 1, 2⟩, 1),
   (⟨2, 0, 2, 2⟩, 2),
   (⟨2, 1, 0, 2⟩, 2),
   (⟨2, 1, 1, 1⟩, 0),
   (⟨2, 1, 2, 0⟩, 1),
   (⟨2, 2, 0, 2⟩, 1),
   (⟨2, 2, 1, 0⟩, 2),
   (⟨2, 2, 2, 1⟩, 0)]

theorem tab4_complete : TableComplete 4 tab4 = true := by decide +kernel
theorem tab3_complete : TableComplete 3 tab3 = true := by decide +kernel
theorem tab4_additive : TableAdditive 4 tab4 = true := by decide +kernel
theorem tab3_additive : TableAdditive 3 tab3 = true := by decide +kernel

/-- A residue mod `n` is one of `0, …, n-1`. -/
theorem emod_mem_range {n : ℕ} (hn : 0 < n) (x : ℤ) :
    ∃ k ∈ List.range n, x % (n : ℤ) = (k : ℤ) := by
  have h0 := Int.emod_nonneg x (by omega : (n : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos x (by omega : (0 : ℤ) < n)
  have hk : (((x % (n : ℤ)).toNat : ℕ) : ℤ) = x % (n : ℤ) := Int.toNat_of_nonneg h0
  refine ⟨(x % (n : ℤ)).toNat, ?_, hk.symm⟩
  rw [List.mem_range]
  exact Int.ofNat_lt.mp (hk ▸ h1)

/-- A determinant-one matrix reduces to a covered residue matrix. -/
theorem redMod_mem {n : ℕ} {tab : List (Mat2 × ℕ)} (hn : 1 < n)
    (hc : TableComplete n tab = true) {M : Mat2} (hM : M.det = 1) :
    Mat2.redMod n M ∈ tableKeys tab := by
  obtain ⟨a, ha, hax⟩ := emod_mem_range (n := n) (by omega) M.a
  obtain ⟨b, hb, hbx⟩ := emod_mem_range (n := n) (by omega) M.b
  obtain ⟨c, hc3, hcx⟩ := emod_mem_range (n := n) (by omega) M.c
  obtain ⟨d, hd, hdx⟩ := emod_mem_range (n := n) (by omega) M.d
  have hdet := Mat2.redMod_det n M
  have hred : Mat2.redMod n M = ⟨a, b, c, d⟩ := by
    simp only [Mat2.redMod, hax, hbx, hcx, hdx]
  rw [hred] at hdet ⊢
  simp only [TableComplete, List.all_eq_true] at hc
  have h := hc a ha b hb c hc3 d hd
  rw [hM] at hdet
  have h1 : ((a : ℤ) * d - b * c) % n = 1 := by
    change ((a : ℤ) * d - b * c) % n = 1 % n at hdet
    rw [hdet]; exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [h1, bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at h
  exact h

/-- A complete additive table gives a character on the unimodular shell. -/
theorem tableValue_mul {n : ℕ} {tab : List (Mat2 × ℕ)} (hn : 1 < n)
    (hc : TableComplete n tab = true) (ha : TableAdditive n tab = true) {M N : Mat2}
    (hM : M.det = 1) (hN : N.det = 1) :
    tableValue tab (Mat2.redMod n (M * N)) =
      (tableValue tab (Mat2.redMod n M) + tableValue tab (Mat2.redMod n N)) % n := by
  rw [Mat2.redMod_mul]
  simp only [TableAdditive, List.all_eq_true, beq_iff_eq] at ha
  exact ha _ (redMod_mem hn hc hM) _ (redMod_mem hn hc hN)

/-- Recombination: `k·((x+y) mod m) = k·x + k·y` in `ℤ/12` when `k·m ≡ 0`. -/
theorem cast_mod_add (k m x y : ℕ) (hk : ((k * m : ℕ) : ZMod 12) = 0) :
    (k : ZMod 12) * (((x + y) % m : ℕ) : ZMod 12) = k * x + k * y := by
  have h := Nat.div_add_mod (x + y) m
  have hc : ((m * ((x + y) / m) + (x + y) % m : ℕ) : ZMod 12) = ((x + y : ℕ) : ZMod 12) := by
    rw [h]
  simp only [Nat.cast_add, Nat.cast_mul] at hc hk
  linear_combination (k : ZMod 12) * hc - (((x + y) / m : ℕ) : ZMod 12) * hk

/-- **Standard Result 8.2's character, constructed.** `ψ(M) = 9·χ₄(M mod 4) +
    4·χ₃(M mod 3)`. Additive on the unimodular shell and `ψ(T) = 1`, so every
    theorem stated for an arbitrary `Closure12` holds of it, and none of them is
    conditional on an unbuilt hypothesis. -/
def congruence : Closure12 where
  psi M := 9 * (tableValue tab4 (Mat2.redMod 4 M) : ZMod 12) +
    4 * (tableValue tab3 (Mat2.redMod 3 M) : ZMod 12)
  map_mul {M N} hM hN := by
    have h4 := tableValue_mul (n := 4) (by decide) tab4_complete tab4_additive hM hN
    have h3 := tableValue_mul (n := 3) (by decide) tab3_complete tab3_additive hM hN
    have e4 := cast_mod_add 9 4 (tableValue tab4 (Mat2.redMod 4 M))
      (tableValue tab4 (Mat2.redMod 4 N)) rfl
    have e3 := cast_mod_add 4 3 (tableValue tab3 (Mat2.redMod 3 M))
      (tableValue tab3 (Mat2.redMod 3 N)) rfl
    simp only [Nat.cast_ofNat] at e4 e3
    simp only [Nat.cast_ofNat] at h4 h3
    rw [h4, h3, e4, e3]
    ring
  map_T := rfl

instance : Nonempty Closure12 := ⟨congruence⟩

/-- The constructed character reads the positive walk as `ψ₁₂`, by `map_G`. -/
theorem congruence_G (w : Word) : congruence.psi (G w) = psi12 w := congruence.map_G w

end Closure12

/-! ## Definition 8.4 — Closure state -/

/-- **Definition 8.4.** The book's line is *"the closure
    component of a state is the residue of its matrix"*: `κ_τ = c(M_τ)`. That
    sentence separates an input (`M_τ`, exact, substrate, declared
    elsewhere: `SubstrateState.matrix`, `Observer.matrix`, and
    `History.matrix`) from an output (`κ_τ`, the twelve-class reading `c`
    produces from it).

    `ClosureState` holds only `κ`, Def 8.4's output. The matrix
    that feeds it is not re-derived here, since it lives on the object
    that owns the word, and `four_records` below is the standing witness
    that this map loses information. -/
structure ClosureState where
  residue : ZMod 12
deriving DecidableEq, Repr

/-- The closure state of a positive word. Computable end to end. -/
def ClosureState.ofWord (w : Word) : ClosureState := ⟨psi12 w⟩

/-- **Definition 8.4, read against the declared start frame.** `κ_τ = c(M_τ)`
    and Def 6.2/7.1 take `M_τ` relative to the declared origin, not to `∅`:
    `M = origin.toMat2 * G w = G(origin.toWord ++ w)`, by `G_append` and
    `Frame.G_toWord`, so the residue read here is `c` applied to that
    start-aware matrix, via `psi12`'s agreement with any `Closure12.psi ∘ G`
    (`map_G`).

    `ClosureState.ofWord w` is this with `origin` the canonical frame `∅`
    (`ClosureState.of_empty`); every call site that owns a declared origin
    calls `of`. -/
def ClosureState.of (origin : Frame) (w : Word) : ClosureState :=
  ClosureState.ofWord (origin.toWord ++ w)

/-- **`of` agrees with `ofWord` from the empty origin.** `ofWord` is the
    special case where the declared origin is the canonical frame. -/
@[simp] theorem ClosureState.of_empty (w : Word) :
    ClosureState.of Frame.empty w = ClosureState.ofWord w := by
  unfold ClosureState.of
  congr 1

/-- **Def 8.4's four records, as types; on `ℳ₊` three grades:
    residue < imbalance < word = matrix (`G_inj`).** Two separations, with
    exact witnesses, and one coincidence.

    * residue equal, integer imbalance different: `ε` against `R¹²`;
    * imbalance equal, matrix different: `LR` against `RL`;
    * matrix and word do not separate on `ℳ₊`: `G` is injective (`G_inj`). -/
theorem four_records :
    psi12 [] = psi12 (List.replicate 12 true) ∧
    bal [] ≠ bal (List.replicate 12 true) ∧
    bal [false, true] = bal [true, false] ∧
    G [false, true] ≠ G [true, false] ∧
    (∀ u v : Word, G u = G v → u = v) := by
  refine ⟨by decide +kernel, by decide, by decide, LR_ne_RL, fun _ _ h => G_inj h⟩

end RatioSpace
