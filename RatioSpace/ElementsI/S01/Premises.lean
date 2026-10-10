/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S02.Frame
import RatioSpace.ElementsI.S04.Composition
/-!
  **Elements I §1-3 as the nonlogical premises of T_RS.**

  `Logic.lean` fixes the logic: ordinary classical first-order logic over an
  exact inherited construction. This file fixes the *language*. It states §1-3 of
  Elements I as a first-order theory over a frozen signature, so that a book
  statement is a sentence with its premises named rather than a Lean theorem
  that happens to sit near the construction.

  The discipline that makes this worth doing: **nothing below may look inside a
  presentation.** There is no `.p` and no `.q` in any theorem of this file. A
  proof that needs them is a proof that the signature is too small, and the
  correct response to one is to say which symbol is missing, not to add it.

  What the exercise found, and it is the point of the file:

    * **Proposition 2.1 is not about numerators and denominators.** Contact is
      inherited because `Δ` is additive in each argument over `⊕` and vanishes
      on a repeated argument. The book proves it by expanding `a(b+d) − b(a+c)`;
      in the frozen language it is two rewrites and needs no components at all.

    * **The remark after Definition 1.6 is the same fact.** "Neither `A ≺ B` nor
      `B ≺ A` exactly when `A ∼ B`" is antisymmetry of `Δ` and trichotomy on `ℤ`.
      Order, proportional equivalence and contact are three readings of one
      symbol.

    * **Contact is a walk invariant in the theory, not only in the type.**
      `Frame.lean` gets `det_walk` free by making contact a field of the
      structure. Here there is no structure to hide it in, so it is proved by
      induction from the premises (Walk's four and three of Contact's five),
      which is the version a book can cite.

  The last section is the model. `Pres` and `Frame` are shown to satisfy every
  premise, which is what makes the theory consistent: it has one.

  No `axiom`, no `sorry`. Everything is `Prop`-valued over `ℤ`.
-/

namespace RatioSpace
namespace Premises

/-! ## The frozen signature

Two nonlogical symbols carry §1 and §2: the signed determinant of Definition 2.1
and the mediant of Definition 2.3. Everything else in those sections is defined
from them.

Definition 1.2's sort is `Pt`, left abstract on purpose — the components are
exactly what must not be reachable. Definition 3.3's word sort is *not* a free
parameter: "a finite ordered string over `{L, R}`" is the free monoid on two
generators, so it is `List Bool` here and nothing is being assumed by writing it
that way. -/

/-- **The theory of Elements I §1-3, part one: presentations in contact.**

Four premises, each traceable to a numbered definition:

* `delta_self` — Definition 2.1. A presentation is in no contrast with itself.
* `delta_swap` — Definition 2.2's remark that column order is not cosmetic.
* `delta_mediant_right`, `delta_mediant_left` — Definition 2.3. The mediant
  inherits both components of both parents, and this is the whole of what that
  means at the level of `Δ`: the contrast against a mediant is the sum of the
  contrasts against its parents.
* `mediant_comm` — Definition 2.3. Componentwise inheritance is symmetric in the
  parents; Definition 3.5 writes `C₋ ⊕ C₊` and Definition 2.4 writes `C₋ ⊕ C₊`
  for the same relation as Definition 2.3's `A ⊕ B`, which is only coherent if
  this holds. -/
class Contact (Pt : Type) where
  /-- Definition 2.1 — the signed determinant `Δ(A,B)`. -/
  delta : Pt → Pt → ℤ
  /-- Definition 2.3 — the mediant `A ⊕ B`. -/
  mediant : Pt → Pt → Pt
  delta_self : ∀ A, delta A A = 0
  delta_swap : ∀ A B, delta B A = -delta A B
  delta_mediant_right : ∀ A B C, delta A (mediant B C) = delta A B + delta A C
  delta_mediant_left : ∀ A B C, delta (mediant A B) C = delta A C + delta B C
  mediant_comm : ∀ A B, mediant A B = mediant B A

namespace Contact

variable {Pt : Type} [Contact Pt]

/-- **Definition 1.4 — proportional equivalence**, `p:q ∼ r:s ⟺ ps = qr`.
    In the frozen language that is exactly the vanishing of the contrast. -/
def Equiv (A B : Pt) : Prop := delta A B = 0

/-- **Definition 1.6 — exact relational order**, `p:q ≺ r:s ⟺ ps < rq`.
    Division-free in the book and symbol-free here. -/
def Lt (A B : Pt) : Prop := delta A B < 0

/-- **Definition 2.1 — primitive Farey contact**, `|Δ(A,B)| = 1`. -/
def Adjacent (A B : Pt) : Prop := delta A B = 1 ∨ delta A B = -1

/-- **Definition 2.2 — positively oriented contact.** The `+1` half. -/
def Pos (A B : Pt) : Prop := delta A B = 1

/-! ### Definition 1.4 is an equivalence relation, from `delta_self` and
`delta_swap` alone. -/

theorem equiv_refl (A : Pt) : Equiv A A := delta_self A

theorem equiv_symm {A B : Pt} (h : Equiv A B) : Equiv B A := by
  unfold Equiv at *; rw [delta_swap, h]; ring

/-! ### The remark after Definition 1.6

The book observes that the equality induced by the value order is proportional
equivalence and not presentation equality. Here that is trichotomy on `ℤ`. -/

theorem not_lt_not_gt_iff_equiv (A B : Pt) :
    (¬ Lt A B ∧ ¬ Lt B A) ↔ Equiv A B := by
  unfold Lt Equiv
  rw [delta_swap A B]
  constructor
  · rintro ⟨h1, h2⟩
    have ha : 0 ≤ delta A B := Int.not_lt.mp h1
    have hb : delta A B ≤ 0 := Int.not_lt.mp (by simpa using h2)
    exact Int.le_antisymm hb ha
  · intro h
    rw [h]
    exact ⟨Int.lt_irrefl 0, by simp⟩

/-- Identity implies equivalence. That the converse fails, so equivalence is
    strictly coarser than identity, is shown in the `Pres` model by
    `p11_equiv_p22` with `p11_ne_p22` below (audit E1-A9). No statement about what sentences
      over `Δ` and `⊕` can
    separate is made here. -/
theorem equiv_of_eq {A B : Pt} (h : A = B) : Equiv A B := h ▸ equiv_refl A

/-! ### Proposition 2.1 — contact is inherited

The prediction this file was written to test. The book's proof expands
`a(b+d) − b(a+c) = ad − bc`. The premises give it without components. -/

/-- **Proposition 2.1, general form.** Not just for contact pairs: the contrast
    between a parent and the mediant *is* the contrast between the parents,
    whatever its value. Contact being inherited is the case `Δ = 1`. -/
theorem delta_parent_mediant (A B : Pt) :
    delta A (mediant A B) = delta A B := by
  rw [delta_mediant_right, delta_self]; ring

theorem delta_mediant_parent (A B : Pt) :
    delta (mediant A B) B = delta A B := by
  rw [delta_mediant_left, delta_self]; ring

/-- **The exact obstruction to quotienting by Definition 1.4.** Composing two
    presentations against a common `B` shifts their contrast by exactly the
    difference of their contrasts against `B`:

      `Δ(A ⊕ B, A' ⊕ B) = Δ(A, B) − Δ(A', B)`.

    Four premises, no components, no hypothesis on `A` and `A'`. Every statement
    below about the mediant failing to descend is this identity read at
    `Δ(A, A') = 0`. -/
theorem delta_mediant_right_cancel (A A' B : Pt) :
    delta (mediant A B) (mediant A' B)
      = delta A A' + (delta A B - delta A' B) := by
  rw [delta_mediant_left, delta_mediant_right, delta_mediant_right,
      delta_self, delta_swap B A']
  ring

/-- **Proportional equivalence is a congruence for `⊕` exactly when the two
    presentations have the same contrast against what they are composed with.**
    Not a counterexample yet — the theory's statement of *what would have to be
    true*. Definition 1.4 says nothing about `Δ(·, B)`, which is why the
    condition is not automatic. -/
theorem equiv_mediant_iff {A A' : Pt} (h : Equiv A A') (B : Pt) :
    Equiv (mediant A B) (mediant A' B) ↔ delta A B = delta A' B := by
  unfold Equiv at *
  rw [delta_mediant_right_cancel, h, zero_add, sub_eq_zero]

/-- **Proposition 2.1.** One parent frame generates two lawful child frames
    without importing a coordinate interpolation rule. -/
theorem contact_inherited {A B : Pt} (h : Pos A B) :
    Pos A (mediant A B) ∧ Pos (mediant A B) B := by
  exact ⟨(delta_parent_mediant A B).trans h, (delta_mediant_parent A B).trans h⟩

/-- The mediant lies strictly between its parents in the order of Definition 1.6,
    whenever the parents are in positively oriented contact. The book uses this
    constantly and states it nowhere; in the frozen language it is one line, and
    it is the reason a walk is a nested sequence of intervals. -/
theorem mediant_between {A B : Pt} (h : Pos A B) :
    Lt (mediant A B) A ∧ Lt B (mediant A B) := by
  constructor
  · unfold Lt
    rw [delta_swap A (mediant A B), delta_parent_mediant, h]
    omega
  · unfold Lt
    rw [delta_swap (mediant A B) B, delta_mediant_parent, h]
    omega

/-! ### §10 — the contact graph, and whether its path metric is derived

Definition 2.1's `Adjacent` is already a relation on presentations. Received as
a symmetric adjacency it is a graph, and the object §10 and §19.6 ask for is the
graph's own path metric: the least number of contact edges joining two
presentations.

**Nothing below adds to the signature.** `Path` is an inductive family built
from `Adjacent`, which is built from `delta`. There is no new primitive and no
fifth axiom, which is where this parts company with `⊗` in §4.

**But the four axioms are not the whole obligation, and here they are not the
binding one.** A path metric only exists where the graph is connected, and on
presentations it is not: `contact_shares_no_factor` below shows a presentation
whose components share a factor is in contact with nothing at all. So the four
axioms are stated on `IsDist`, the predicate "`n` is *a* least path length",
rather than on a total function that has nothing to return. -/

/-- Adjacency is symmetric, from `delta_swap` alone. This is the whole content
    of "received as a symmetric adjacency": no orientation is discarded that
    was not already recoverable. -/
theorem adjacent_symm {A B : Pt} (h : Adjacent A B) : Adjacent B A := by
  rcases h with h | h
  · right; rw [delta_swap, h]
  · left; rw [delta_swap, h]; ring

/-- A walk of exactly `n` contact edges from `A` to `B`. -/
inductive Path : ℕ → Pt → Pt → Prop
  | refl (A : Pt) : Path 0 A A
  | step {n : ℕ} {A B C : Pt} : Path n A B → Adjacent B C → Path (n + 1) A C

/-- Extending a path at the front rather than the back. -/
theorem path_cons {n : ℕ} {A B C : Pt} (hab : Adjacent A B) (h : Path n B C) :
    Path (n + 1) A C := by
  induction h with
  | refl X => exact Path.step (Path.refl A) hab
  | step _ hadj ih => exact Path.step (ih hab) hadj

/-- **Symmetry.** A theorem, not a field: it reduces to `adjacent_symm`, which
    reduces to `delta_swap`. -/
theorem path_symm {n : ℕ} {A B : Pt} (h : Path n A B) : Path n B A := by
  induction h with
  | refl X => exact Path.refl X
  | step _ hadj ih => exact path_cons (adjacent_symm hadj) ih

/-- **Concatenation**, the exact additive form the triangle inequality is read
    off. Lengths add; only taking minima turns `=` into `≤`. -/
theorem path_trans {m n : ℕ} {A B C : Pt} (h₁ : Path m A B) (h₂ : Path n B C) :
    Path (m + n) A C := by
  induction h₂ with
  | refl X => simpa using h₁
  | step _ hadj ih => exact Path.step (ih h₁) hadj

/-- **Separation, the exact half.** A path of no edges joins nothing but a
    presentation to itself. -/
theorem path_zero {A B : Pt} (h : Path 0 A B) : A = B := by
  cases h with
  | refl => rfl

/-- `n` is *a* least contact path length between `A` and `B`. Stated as a
    predicate because on presentations there need not be one: see
    `Premises.contact_shares_no_factor`. -/
def IsDist (n : ℕ) (A B : Pt) : Prop := Path n A B ∧ ∀ m, Path m A B → n ≤ m

/-- The least length is unique when it exists, so "the" distance is legitimate
    wherever the graph is connected. -/
theorem isDist_unique {m n : ℕ} {A B : Pt} (hm : IsDist m A B)
    (hn : IsDist n A B) : m = n :=
  Nat.le_antisymm (hm.2 n hn.1) (hn.2 m hm.1)

/-- **Axiom 1 — identity.** -/
theorem isDist_self (A : Pt) : IsDist 0 A A :=
  ⟨Path.refl A, fun m _ => Nat.zero_le m⟩

/-- **Axiom 2 — symmetry.** -/
theorem isDist_symm {n : ℕ} {A B : Pt} (h : IsDist n A B) : IsDist n B A :=
  ⟨path_symm h.1, fun m hm => h.2 m (path_symm hm)⟩

/-- **Axiom 3 — separation**, both directions. -/
theorem isDist_zero_iff {A B : Pt} : IsDist 0 A B ↔ A = B := by
  constructor
  · intro h; exact path_zero h.1
  · rintro rfl; exact isDist_self A

/-- **Axiom 4 — the triangle inequality.** The minimum over `A → C` is at most
    the length of the concatenated route through `B`, which is exactly what
    `path_trans` supplies. No minimality of the two legs is used beyond their
    being realised, so this is the weakest form that is still the axiom. -/
theorem isDist_triangle {a b c : ℕ} {A B C : Pt} (hab : IsDist a A B)
    (hbc : IsDist b B C) (hac : IsDist c A C) : c ≤ a + b :=
  hac.2 (a + b) (path_trans hab.1 hbc.1)

/-- **The four axioms of §19.6, together.** All four are theorems over the
    frozen signature; none is a declared field. -/
theorem isDist_is_metric :
    (∀ A : Pt, IsDist 0 A A) ∧
    (∀ (n : ℕ) (A B : Pt), IsDist n A B → IsDist n B A) ∧
    (∀ A B : Pt, IsDist 0 A B ↔ A = B) ∧
    (∀ (a b c : ℕ) (A B C : Pt), IsDist a A B → IsDist b B C → IsDist c A C →
      c ≤ a + b) :=
  ⟨isDist_self, fun _ _ _ => isDist_symm, fun _ _ => isDist_zero_iff,
    fun _ _ _ _ _ _ => isDist_triangle⟩

end Contact

/-! ## Definitions 2.2, 2.4, 3.4 and 3.5 — frames, triads, walks

The second half of the signature. A frame is an ordered pair of presentations,
`Definition 2.2`, and the two children of `Definition 2.4` are its only lawful
continuations. -/

open _root_.RatioSpace.Premises.Contact

/-- **The theory of Elements I §1-3, part two: the frame and its continuations.**

`stepL` and `stepR` are the two child frames of Definition 2.4, characterised by
what they do to the two boundaries and by nothing else. Definition 3.1's matrices
`L` and `R` are a *representation* of these, not their definition, which is why
no matrix appears in this class. -/
class Walk (Fr : Type) (Pt : outParam Type) [Contact Pt] where
  /-- Definition 2.2 — the `C₊` boundary, the first matrix column. -/
  plus : Fr → Pt
  /-- Definition 2.2 — the `C₋` boundary, the second matrix column. -/
  minus : Fr → Pt
  /-- Definition 2.4 — `F_L = (C₋ ⊕ C₊, C₋)`. -/
  stepL : Fr → Fr
  /-- Definition 2.4 — `F_R = (C₊, C₋ ⊕ C₊)`. -/
  stepR : Fr → Fr
  plus_stepL : ∀ F, plus (stepL F) = mediant (plus F) (minus F)
  minus_stepL : ∀ F, minus (stepL F) = minus F
  plus_stepR : ∀ F, plus (stepR F) = plus F
  minus_stepR : ∀ F, minus (stepR F) = mediant (plus F) (minus F)

namespace Walk

variable {Fr Pt : Type} [Contact Pt] [Walk Fr Pt]

/-- **Definition 2.2 — the frame condition**, `det M_F = 1`, said without a
    matrix. Carried as a hypothesis rather than a field, so that the theorems
    below are about words preserving it. -/
def Oriented (F : Fr) : Prop := Pos (plus F) (minus F)

/-- **Definition 2.4 — the relational triad** `𝔗(C₊, C₋) = (C₋, C₋ ⊕ C₊, C₊)`. -/
def triad (F : Fr) : Pt × Pt × Pt := (minus F, mediant (minus F) (plus F), plus F)

/-- **Definition 3.5 — the addressed relation** `r_F(w) = C₋(w) ⊕ C₊(w)`,
    at the frame itself. The walk is applied first. -/
def addr (F : Fr) : Pt := mediant (minus F) (plus F)

/-- **Definition 2.5 — side selection.** The triad holds both continuations; a
    directed continuation carries one. -/
def select (F : Fr) (right : Bool) : Fr := if right then stepR F else stepL F

/-- **Definition 3.4 — the walk.** A word is folded from the left, oldest event
    first, which is Definition 3.2's forward continuation `G(wg) = G(w)g`. -/
def walk (F : Fr) (w : List Bool) : Fr := w.foldl select F

@[simp] theorem walk_nil (F : Fr) : walk F ([] : List Bool) = F := rfl

@[simp] theorem walk_cons (F : Fr) (b : Bool) (w : List Bool) :
    walk F (b :: w) = walk (select F b) w := rfl

/-! ### Contact survives one step, then every step

`Frame.lean` gets this by making contact a field, so no term of the type can be
out of contact. That is the right move for the construction and the wrong move
for a book: it makes the load-bearing fact invisible. Here it is proved. -/

theorem oriented_stepL {F : Fr} (h : Oriented F) : Oriented (stepL F) := by
  unfold Oriented Pos at *
  rw [plus_stepL, minus_stepL]
  exact (delta_mediant_parent (plus F) (minus F)).trans h

theorem oriented_stepR {F : Fr} (h : Oriented F) : Oriented (stepR F) := by
  unfold Oriented Pos at *
  rw [plus_stepR, minus_stepR]
  exact (delta_parent_mediant (plus F) (minus F)).trans h

theorem oriented_select {F : Fr} (h : Oriented F) (b : Bool) :
    Oriented (select F b) := by
  cases b
  · exact oriented_stepL h
  · exact oriented_stepR h

/-- **The walk cannot leave the tree.** Definition 3.4 preserves Definition 2.2's
    frame condition, for every word, by induction on the word and from three
    of the five premises of `Contact` (`delta_self`, `delta_mediant_right`,
    `delta_mediant_left`) plus the four of `Walk`. Nothing else is used. -/
theorem oriented_walk {F : Fr} (h : Oriented F) (w : List Bool) :
    Oriented (walk F w) := by
  induction w generalizing F with
  | nil => exact h
  | cons b w ih => exact ih (oriented_select h b)

/-- **Definition 3.5.** The
    relation addressed by a walk is strictly inside its own frame: the two
    boundaries are always in contact around it. This is the interval-nesting
    statement the book uses without stating. -/
theorem addr_between {F : Fr} (h : Oriented F) :
    Lt (addr F) (plus F) ∧ Lt (minus F) (addr F) := by
  unfold addr
  rw [mediant_comm (minus F) (plus F)]
  exact mediant_between h

end Walk

/-! ## The model

Everything above is a theory. This is what shows it has one, and therefore that
the premises are consistent: the construction of `Pres.lean` and `Frame.lean`
satisfies every one of them.

Each premise discharges by `push_cast` and `ring` on the components — which is
allowed *here*, because this is the interpretation and not a theorem of the
theory. It is the one place components are in scope. -/

instance : Contact Pres where
  delta := Delta
  mediant := Pres.mediant
  delta_self A := by unfold Delta; ring
  delta_swap := RatioSpace.delta_swap
  delta_mediant_right A B C := by unfold Delta Pres.mediant; push_cast; ring
  delta_mediant_left A B C := by unfold Delta Pres.mediant; push_cast; ring
  mediant_comm A B := by
    unfold Pres.mediant
    congr 1 <;> omega

instance : Walk Frame Pres where
  plus := Frame.plus
  minus := Frame.minus
  stepL := Frame.stepL
  stepR := Frame.stepR
  plus_stepL _ := rfl
  minus_stepL _ := rfl
  plus_stepR _ := rfl
  minus_stepR _ := rfl

/-- Every `Frame` satisfies Definition 2.2's condition, so the hypothesis the
    abstract theorems carry is discharged once and for all in the model. -/
theorem frame_oriented (F : Frame) : Walk.Oriented F :=
  (contact_iff_delta_one _ _).mp F.contact

/-- **`det_walk`, obtained from the theory rather than from the type.** The
    concrete statement of `Frame.lean` now has a proof that never mentions a
    numerator: it is `oriented_walk` at the instance. -/
theorem det_walk_from_premises (F : Frame) (w : List Bool) :
    Delta (Frame.walk F w).plus (Frame.walk F w).minus = 1 := by
  have hsel : ∀ (G : Frame) (b : Bool), Walk.select G b = Frame.select G b := by
    intro G b; cases b <;> rfl
  have hwalk : ∀ (w : List Bool) (G : Frame), Walk.walk G w = Frame.walk G w := by
    intro w
    induction w with
    | nil => intro G; rfl
    | cons b w ih =>
      intro G
      have hstep : Frame.walk G (b :: w) = Frame.walk (Frame.select G b) w := rfl
      rw [Walk.walk_cons, hstep, hsel G b]
      exact ih _
  have := Walk.oriented_walk (frame_oriented F) w
  rw [hwalk] at this
  exact this

/-- **Proposition 2.1 for the construction, proved in the theory.** The book's
    componentwise calculation is not needed; this is `contact_inherited`
    instantiated at `Pres`. -/
theorem prop_2_1 {A B : Pres} (h : Delta A B = 1) :
    Delta A (Pres.mediant A B) = 1 ∧ Delta (Pres.mediant A B) B = 1 :=
  Contact.contact_inherited (Pt := Pres) h

/-! ## §4 — does directional composition fit the frozen signature?

**No, on two counts, and this section names both rather than adding either
quietly.**

**First, `⊗` needs primitives §1-3 never declared.** `Definition 4.1` sets
`A ⊗ B := (A.p·B.q) : (A.q·B.p)`, a new *point*, not a scalar — and `delta`
returns only the *difference* of those two products (`Delta A B = A.p·B.q −
A.q·B.p`), never either one on its own, while `mediant` is their *sum*
(`A.p+B.p : A.q+B.q`), a different combination entirely. No term built from
`delta` and `mediant` alone reaches `A.p·B.q` as a component of anything: the
signature is short an operation, not merely a lemma. So `⊗`, `Inv`, and the
identity `I_r` are added below exactly as `Closure12` was added in `Winding.lean`
— **declared fields of a new class, not a Lean `axiom`, and not derived from
`Contact`.**

**Second, `⊗`'s own domain is not `Pt`.** `Composition.lean`'s finding that
`Definition 1.2`'s boundary anchors leave `⊗` outside the presentation domain
holds here unchanged: the class below is generic in `Pt`, but Elements I
instantiates it at `IPres`, not at `Pres`, the sort `Walk` uses. One frozen
theory, two different carriers for two different sections of the same book —
worth naming, since nothing in the abstract theory forces `Pt`'s meaning to
stay fixed across sections.

**What the exercise found beyond the negative result.** Declaring `otimes`,
`inv` and `Ir` still leaves the new primitives disconnected from the old ones —
`Composition`'s first four axioms mention no `delta` at all. Checking whether
the model relates them anyway turns up an identity the book states nowhere:
`Δ(A, B) = Δ(A ⊗ B, I_r)`. Two presentations' contact reads off the contact of
their composition against the identity. It costs one extra axiom
(`delta_otimes_unit`, not derivable from the other four — nothing above
relates `otimes` to `delta` at all without it), and it is *not* about
components once assumed: `otimes_lt_iff`, `otimes_equiv_iff` and
`otimes_pos_iff` below recover Definition 1.6's order, Definition 1.4's
equivalence and Definition 2.2's positive contact from it, symbol-free, same
discipline as the rest of this file. -/

/-- **The theory of Elements I §4.** Three new primitives beyond `Contact`'s
    two — `otimes` (Definition 4.1), `inv` (Definition 4.2), and the identity
    `Ir` (Proposition 4.1) — plus one axiom tying the new primitives to the old:
    a pair's contact is its composition's contact against the identity. The
    first four axioms are Proposition 4.1's first three identities and
    Definition 4.2's involution, restated abstractly; the existence witnesses
    for Propositions 4.2 and 4.3 (non-commutativity, non-associativity) are not
    restated here, because they are facts about particular elements of a
    particular model, not sentences the theory itself proves. -/
class Composition (Pt : Type) [Contact Pt] where
  /-- Definition 4.1 — directional composition. -/
  otimes : Pt → Pt → Pt
  /-- Definition 4.2 — relational inversion. -/
  inv : Pt → Pt
  /-- Proposition 4.1's identity element. -/
  Ir : Pt
  otimes_Ir : ∀ A, otimes A Ir = A
  Ir_otimes : ∀ A, otimes Ir A = inv A
  inv_inv : ∀ A, inv (inv A) = A
  otimes_swap : ∀ A B, otimes B A = inv (otimes A B)
  /-- Not in the book's own statement of Definition 4.1 — found by asking
      whether `otimes` and `delta` interact at all, and they do. -/
  delta_otimes_unit : ∀ A B, delta A B = delta (otimes A B) Ir

namespace Composition

variable {Pt : Type} [Contact Pt] [Composition Pt]

/-- Definition 1.6's order, read off the composition against the identity. -/
theorem otimes_lt_iff {A B : Pt} : Lt A B ↔ Lt (otimes A B) Ir := by
  unfold Lt; rw [delta_otimes_unit]

/-- Definition 1.4's proportional equivalence, same reading. -/
theorem otimes_equiv_iff {A B : Pt} :
    Contact.Equiv A B ↔ Contact.Equiv (otimes A B) Ir := by
  unfold Contact.Equiv; rw [delta_otimes_unit]

/-- Definition 2.2's positively oriented contact, same reading. -/
theorem otimes_pos_iff {A B : Pt} : Pos A B ↔ Pos (otimes A B) Ir := by
  unfold Pos; rw [delta_otimes_unit]

end Composition

/-! ## The §4 model

`IPres` needs its own `Contact` instance first — it is a different sort from
`Pres`, not a theorem about `Pres` — built from the same `delta`/`mediant`
formulas with the interior positivity carried in the type instead of proved
per pair. Then `Composition.lean`'s already-built `otimes`/`inv`/`Ir` and their
four identities discharge the first four fields unchanged, and
`delta_otimes_unit` is the one genuinely new obligation: unfold three
component-level definitions and close by `ring`, the only place in this
section a `.p` or `.q` appears. -/

/-- Definition 2.1's determinant, restated on `IPres`. Same formula as `Delta`
    on `Pres` — `IPres` is a different type, not a refinement proof, so the
    definition repeats rather than lifts. -/
def IPres.delta (A B : IPres) : ℤ := (A.p : ℤ) * B.q - (A.q : ℤ) * B.p

/-- Definition 2.3's mediant, restated on `IPres`: the sum of two interior
    presentations is interior, so `⊕` needs no side condition here either. -/
def IPres.mediant (A B : IPres) : IPres :=
  ⟨A.p + B.p, A.q + B.q, by have := A.p_pos; have := B.p_pos; omega,
    by have := A.q_pos; have := B.q_pos; omega⟩

@[simp] theorem IPres.mediant_p (A B : IPres) : (IPres.mediant A B).p = A.p + B.p := rfl
@[simp] theorem IPres.mediant_q (A B : IPres) : (IPres.mediant A B).q = A.q + B.q := rfl

instance : Contact IPres where
  delta := IPres.delta
  mediant := IPres.mediant
  delta_self A := by unfold IPres.delta; ring
  delta_swap A B := by unfold IPres.delta; ring
  delta_mediant_right A B C := by
    unfold IPres.delta; simp only [IPres.mediant_p, IPres.mediant_q]; push_cast; ring
  delta_mediant_left A B C := by
    unfold IPres.delta; simp only [IPres.mediant_p, IPres.mediant_q]; push_cast; ring
  mediant_comm A B := IPres.eq_of (by simp; omega) (by simp; omega)

instance : Composition IPres where
  otimes := IPres.otimes
  inv := IPres.inv
  Ir := IPres.Ir
  otimes_Ir := IPres.otimes_Ir
  Ir_otimes := IPres.Ir_otimes
  inv_inv := IPres.inv_inv
  otimes_swap := IPres.otimes_swap
  delta_otimes_unit A B := by
    change IPres.delta A B = IPres.delta (IPres.otimes A B) IPres.Ir
    unfold IPres.delta IPres.otimes IPres.Ir
    push_cast
    ring

/-- **The point of the exercise, for the construction.** Contact between two
    interior presentations is exactly contact between their composition and
    the relational identity — proved here from the model, and, via
    `Composition.otimes_pos_iff`, a theorem of the abstract theory for any
    type satisfying both classes. -/
theorem delta_eq_delta_otimes_Ir (A B : IPres) :
    IPres.delta A B = IPres.delta (IPres.otimes A B) IPres.Ir :=
  Composition.delta_otimes_unit (Pt := IPres) A B

/-! ## §10 in the model — the contact graph is not connected

The four axioms above are theorems of the theory. Whether any pair of
presentations has a distance at all is a question about the model, and the
answer is no.

`Δ(B, A)` is `B.p·A.q − B.q·A.p`. If `A`'s two components share a factor `g`,
every `Δ(B, A)` is a multiple of `g` and so is never `±1`. **A presentation
whose components share a factor is in contact with nothing.** It is an isolated
vertex, and no path of any length reaches it.

The sharpest case is `2:2`. Definition 1.4 already proves `2:2` proportionally
equivalent to `1:1` — `Δ(1:1, 2:2) = 0` — and the two sit at no finite contact
distance whatever. So the contact graph does not see proportional equivalence. -/

/-- `1:1`. -/
def p11 : Pres := ⟨1, 1, by decide⟩

/-- `2:2`, proportionally equivalent to `1:1` and adjacent to nothing. -/
def p22 : Pres := ⟨2, 2, by decide⟩

/-- Definition 1.4 does hold between them. -/
theorem p11_equiv_p22 : Contact.Equiv p11 p22 := by
  change Delta p11 p22 = 0
  unfold Delta p11 p22
  decide

/-- Definition 1.3 does not: they are different presentations. -/
theorem p11_ne_p22 : p11 ≠ p22 := by decide

/-- **Nothing is in contact with `2:2`.** `Δ(B, 2:2) = 2·B.p − 2·B.q` is even,
    so it is never `±1`. The shared factor, not the value, is what isolates it. -/
theorem contact_shares_no_factor (B : Pres) : ¬ Contact.Adjacent B p22 := by
  intro h
  have hd : Contact.delta B p22 = 2 * (B.p : ℤ) - 2 * (B.q : ℤ) := by
    change Delta B p22 = _
    unfold Delta p22
    push_cast
    ring
  rcases h with h | h <;> rw [hd] at h <;> omega

/-- Every contact path into `2:2` is the empty one, so nothing else reaches it. -/
theorem path_to_p22 {n : ℕ} {A : Pres} (h : Contact.Path n A p22) : A = p22 := by
  cases h with
  | refl => rfl
  | step _ hadj => exact absurd hadj (contact_shares_no_factor _)

/-- **The path metric is not total on presentations.** `1:1` and `2:2` are
    distinct, proportionally equivalent, and joined by no contact path of any
    length. There is therefore no `n` with `IsDist n (1:1) (2:2)`, and the four
    axioms above are being asked of an object that here does not exist. -/
theorem no_distance_p11_p22 : ¬ ∃ n : ℕ, Contact.IsDist n p11 p22 := by
  rintro ⟨n, hn, -⟩
  exact p11_ne_p22 (path_to_p22 hn)

/-! ### §10's second option costs the mediant

The section above leaves a choice: state `d_G` with a coprimality qualifier
inside the statement, or state it on the quotient by Definition 1.4 and make the
reduction map explicit. The second is only safe if the rest of Elements I can
still operate on the quotient, and it cannot: **`⊕` does not descend.**

`equiv_mediant_iff` gives the condition — the two presentations must have equal
contrast against `B` — and Definition 1.4 does not supply it. What follows are
the witnesses, and the point of having two is which one the framework depends
on. -/

/-- `1:2`, the presentation composed against. -/
def p12 : Pres := ⟨1, 2, by decide⟩

/-- **The interior witness.** `1:1 ~ 2:2` by Definition 1.4, but composing each
    with `1:2` gives `2:3` and `3:4`, and `Δ(2:3, 3:4) = −1 ≠ 0`. Every
    component here is nonzero, so this is not about Definition 1.2's boundary
    anchors: the failure is in the interior, where §10's isolated vertices are. -/
theorem mediant_not_congruence :
    Contact.Equiv p11 p22 ∧
      ¬ Contact.Equiv (Contact.mediant p11 p12) (Contact.mediant p22 p12) := by
  refine ⟨p11_equiv_p22, ?_⟩
  change ¬ Delta (Pres.mediant p11 p12) (Pres.mediant p22 p12) = 0
  unfold Delta Pres.mediant p11 p22 p12
  decide

/-- The same fact read through `equiv_mediant_iff`: the contrasts against `1:2`
    differ, `Δ(1:1, 1:2) = 1` against `Δ(2:2, 1:2) = 2`. The shared factor that
    isolates `2:2` in the contact graph is the same factor that scales its
    contrast, so the two §10 findings have one cause. -/
theorem contrast_not_equal_p12 :
    Contact.delta p11 p12 ≠ Contact.delta p22 p12 := by
  change Delta p11 p12 ≠ Delta p22 p12
  unfold Delta p11 p22 p12
  decide

/-- `1:0` and `2:0`, the briefing's own witness. Definition 1.2 admits both:
    `ne_zero` forbids only `0:0`. -/
def p10 : Pres := ⟨1, 0, by decide⟩
/-- `2:0`, proportionally equivalent to `1:0`. -/
def p20 : Pres := ⟨2, 0, by decide⟩
/-- `0:1`, the anchor composed against. -/
def p01 : Pres := ⟨0, 1, by decide⟩

/-- **The degenerate witness**, recorded because it is the one the correction
    arrived with and it is *weaker*: `1:0 ~ 2:0`, and composing each with `0:1`
    gives `1:1` and `2:1`. True, but a reader can dismiss it as an artifact of
    the anchors. `mediant_not_congruence` is the one that cannot be dismissed. -/
theorem mediant_not_congruence_anchors :
    Contact.Equiv p10 p20 ∧
      ¬ Contact.Equiv (Contact.mediant p10 p01) (Contact.mediant p20 p01) := by
  constructor
  · change Delta p10 p20 = 0
    unfold Delta p10 p20; decide
  · change ¬ Delta (Pres.mediant p10 p01) (Pres.mediant p20 p01) = 0
    unfold Delta Pres.mediant p10 p20 p01
    decide

/-- **The reduction map is not a `⊕`-homomorphism**, stated as the general
    sentence rather than a pair of witnesses. There is no way to define the
    mediant on Definition 1.4's classes so that it agrees with the mediant on
    presentations: a well-defined `⊕` on the quotient would force
    `Δ(A ⊕ B, A' ⊕ B) = 0` whenever `Δ(A, A') = 0`, and `1:1`, `2:2`, `1:2`
    refute it. Making the reduction map explicit does not repair this; the map
    is explicit here and still does not commute with Definition 2.3. -/
theorem no_mediant_on_quotient :
    ¬ ∀ A A' B : Pres, Contact.Equiv A A' →
        Contact.Equiv (Contact.mediant A B) (Contact.mediant A' B) := by
  intro h
  exact mediant_not_congruence.2 (h p11 p22 p12 mediant_not_congruence.1)

end Premises
end RatioSpace
