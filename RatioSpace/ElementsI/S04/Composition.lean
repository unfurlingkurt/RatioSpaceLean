/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S01.Pres
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
/-!
  Elements I §4 — Directional composition.

  Definitions 4.1 through 4.4 and Propositions 4.1 through 4.3.

  **The one structural finding, and it forces the type.** The ledger proposed

      def otimes (A B : Pres) : Pres := ⟨A.p * B.q, A.q * B.p⟩

  and that does not typecheck, for a reason that is not a technicality. Take
  `A = B = 0:1`, both admitted by Def 1.2 as orientation anchors. Then
  `A.p * B.q = 0` and `A.q * B.p = 0`, and `0:0` is excluded from `Pres` by
  Def 1.2's own side condition. The same happens at `1:0 ⊗ 1:0`. So `⊗` is not
  total on the boundary presentations, while on the interior both cross-products
  are positive and `⊗` is total (`otimes_interior`). The interior restriction is
  sufficient, not necessary: `1:0 ⊗ 1:1 = 1:0` is a presentation.
  `otimes_leaves_domain_on_boundary` below is the exact witness.

  Following constraint 1 — the type forbids the case that must not occur, rather
  than a hypothesis promising it will not — the interior domain becomes a type,
  `IPres`, and `⊗` is total on it. This is the same move that made contact a
  field of `Frame` in §2, and it pays the same way: no interiority hypothesis
  propagates through Prop 4.3, Def 4.3 or Def 4.4, and no side condition has to
  be rechecked when compositions are iterated.

  **Two places where the formalisation is strictly sharper than the prose**, both
  noted at their statements:

    * Prop 4.1's last identity is stated in the book after reduction,
      `ρ(B ⊗ A) = ρ(Inv(A ⊗ B))`. It holds before reduction, as an equality of
      presentations. `otimes_swap` proves the stronger form; the book's is a
      corollary. Reduction is not needed and, by Def 1.5, is lossy, so not
      needing it is worth recording.

    * Def 4.3 says `Pow₂(A) ≠ A ⊗ A` "except in trivial cases".
      `pow_two_eq_otimes_self_iff` says exactly which: `A.p = A.q`, and nothing
      else. The exception set is one value class, the diagonal (infinitely many
      presentations `n:n`), not a vague reservation.

  Everything is ℕ-valued, computable, and decidable. `ℚ` appears only in
  `realize_otimes`, which is the projection-layer half of Def 4.1 and is marked
  as such.
-/

namespace RatioSpace

/-! ## The interior presentation domain

    Def 1.2 names `𝒫⁺ = {p:q | p, q ∈ ℕ₊}` and admits `0:1` and `1:0` as
    orientation anchors outside it. §4 works entirely inside `𝒫⁺`. -/

/-- **Definition 1.2 — interior presentation**, as a predicate on `Pres`. -/
def Pres.Interior (A : Pres) : Prop := 0 < A.p ∧ 0 < A.q

instance : DecidablePred Pres.Interior := fun A => by unfold Pres.Interior; infer_instance

/-- Componentwise equality decides equality of presentations. Def 1.3 in the form
    the proofs below need; the `ne_zero` field carries no information. -/
theorem Pres.eq_of {A B : Pres} (hp : A.p = B.p) (hq : A.q = B.q) : A = B := by
  cases A; cases B; cases hp; cases hq; rfl

/-- **The interior presentation domain `𝒫⁺` as a type.** Constraint 1: a term of
    this type cannot be a boundary anchor, so `⊗` needs no side condition. -/
structure IPres where
  p : ℕ
  q : ℕ
  p_pos : 0 < p
  q_pos : 0 < q
deriving DecidableEq

namespace IPres

/-- Componentwise equality decides equality. The proof fields carry no
    information, by proof irrelevance. -/
theorem eq_of {A B : IPres} (hp : A.p = B.p) (hq : A.q = B.q) : A = B := by
  cases A; cases B; cases hp; cases hq; rfl

/-- Every interior presentation is a presentation. -/
def toPres (A : IPres) : Pres :=
  ⟨A.p, A.q, by rintro ⟨h, _⟩; exact absurd h A.p_pos.ne'⟩

instance : Coe IPres Pres := ⟨toPres⟩

@[simp] theorem toPres_p (A : IPres) : (toPres A).p = A.p := rfl
@[simp] theorem toPres_q (A : IPres) : (toPres A).q = A.q := rfl

theorem toPres_interior (A : IPres) : (toPres A).Interior := ⟨A.p_pos, A.q_pos⟩

/-- **The interior domain's own decoder.** Every presentation either witnesses
    its own membership in `𝒫⁺` or does not, decidably (`Pres.Interior` already
    has a `DecidablePred` instance), and this returns the witness when it
    exists. Built for Elements II §16's occurrence-family assembly, which needs
    to turn an observer's decoded local address (`Option Pres`) into the
    `IPres` §7's and §8's comparison functions are stated over — but the fact
    is purely about §4's own domain and belongs here, not in `Two/`. -/
def ofPres? (A : Pres) : Option IPres :=
  if h : A.Interior then some ⟨A.p, A.q, h.1, h.2⟩ else none

/-- `ofPres?` never invents an interior presentation: it succeeds exactly on
    `A.Interior`, and produces the componentwise-equal witness when it does. -/
theorem ofPres?_some_iff {A : Pres} {B : IPres} :
    ofPres? A = some B ↔ A.Interior ∧ A.p = B.p ∧ A.q = B.q := by
  unfold ofPres?
  split
  · rename_i h
    constructor
    · rintro ⟨⟩; exact ⟨h, rfl, rfl⟩
    · rintro ⟨_, hp, hq⟩; exact congrArg some (eq_of hp hq)
  · rename_i h
    constructor
    · intro hc; exact absurd hc (by simp)
    · rintro ⟨hA, _, _⟩; exact absurd hA h

/-- The boundary presentations decode to nothing: `IPres` excludes exactly what
    Def 1.2 admits as the two orientation anchors and nothing else. -/
theorem ofPres?_none_iff {A : Pres} : ofPres? A = none ↔ ¬ A.Interior := by
  unfold ofPres?; split <;> simp_all

/-! ## Definition 4.1 — Directional composition -/

/-- **Definition 4.1.** `A ⊗ B = (ad):(bc)` for `A = a:b`, `B = c:d`.
    Compares `A` **relative to** `B`; the argument order is meaningful. The
    cross-products are performed on the integer presentations, not on any
    realization of them. -/
def otimes (A B : IPres) : IPres :=
  ⟨A.p * B.q, A.q * B.p, Nat.mul_pos A.p_pos B.q_pos, Nat.mul_pos A.q_pos B.p_pos⟩

@[simp] theorem otimes_p (A B : IPres) : (otimes A B).p = A.p * B.q := rfl
@[simp] theorem otimes_q (A B : IPres) : (otimes A B).q = A.q * B.p := rfl

/-- **Why Def 4.1 is restricted to `𝒫⁺`.** At `A = B = 0:1`, both admitted by
    Def 1.2, the cross-products are `0` and `0`, and `0:0` is not a presentation.
    `⊗` does not merely behave badly on the boundary anchors, it leaves the
    presentation domain. This is the exact witness. -/
theorem otimes_leaves_domain_on_boundary :
    ∃ A B : Pres, A.p * B.q = 0 ∧ A.q * B.p = 0 :=
  ⟨⟨0, 1, by decide⟩, ⟨0, 1, by decide⟩, by decide, by decide⟩

/-- **Definition 4.1, interior closure.** On interior presentations both
    cross-products are positive, so the product is always a presentation: the
    pair `(ad, bc)` is never `(0, 0)`. This is the converse direction of
    `otimes_leaves_domain_on_boundary`, which exhibits one boundary pair
    (`A = B = 0:1`) where both cross-products vanish; the product is not total on
    the boundary presentations and is total on the interior ones. -/
theorem otimes_cross_pos {A B : Pres} (hA : A.Interior) (hB : B.Interior) :
    0 < A.p * B.q ∧ 0 < A.q * B.p :=
  ⟨Nat.mul_pos hA.1 hB.2, Nat.mul_pos hA.2 hB.1⟩

/-- On interior presentations the cross-products form an interior presentation. -/
theorem otimes_interior (A B : IPres) : (toPres (otimes A B)).Interior :=
  toPres_interior _

/-! ## Definition 4.2 — Relational inversion -/

/-- **Definition 4.2.** `Inv(a:b) = b:a`. -/
def inv (A : IPres) : IPres := ⟨A.q, A.p, A.q_pos, A.p_pos⟩

@[simp] theorem inv_p (A : IPres) : (inv A).p = A.q := rfl
@[simp] theorem inv_q (A : IPres) : (inv A).q = A.p := rfl

theorem inv_inv (A : IPres) : inv (inv A) = A := by cases A; rfl

/-! ## Proposition 4.1 — Basic composition identities -/

/-- The relational identity `I_r = 1:1`. -/
def Ir : IPres := ⟨1, 1, by decide, by decide⟩

/-- **Proposition 4.1, first identity.** `A ⊗ I_r = A`. -/
theorem otimes_Ir (A : IPres) : otimes A Ir = A :=
  eq_of (by simp [Ir]) (by simp [Ir])

/-- **Proposition 4.1, second identity.** `I_r ⊗ A = Inv(A)`. The identity on the
    right is *not* an identity on the left: composing against `1:1` from the left
    inverts. This asymmetry is Prop 4.2 already visible in the unit. -/
theorem Ir_otimes (A : IPres) : otimes Ir A = inv A :=
  eq_of (by simp [Ir]) (by simp [Ir])

/-- **Proposition 4.1, third identity.** `A ⊗ A = ab:ab`. -/
theorem otimes_self (A : IPres) : otimes A A = ⟨A.p * A.q, A.q * A.p,
    Nat.mul_pos A.p_pos A.q_pos, Nat.mul_pos A.q_pos A.p_pos⟩ := rfl

/-- **Proposition 4.1, third identity, reduced.** `ρ(A ⊗ A) = 1:1`.
    Self-comparison carries no relational content *after reduction* — but note
    that `A ⊗ A = ab:ab` is not `1:1` as a presentation. Def 1.3 keeps them
    apart, and the scale `ab` is exactly what Def 1.5 discards. -/
theorem reduce_otimes_self (A : IPres) :
    Pres.reduce (toPres (otimes A A)) = toPres Ir := by
  have hpos : 0 < A.p * A.q := Nat.mul_pos A.p_pos A.q_pos
  have hgcd : Nat.gcd (A.p * A.q) (A.q * A.p) = A.p * A.q := by
    rw [Nat.mul_comm A.q A.p, Nat.gcd_self]
  refine Pres.eq_of ?_ ?_
  · change (A.p * A.q) / Nat.gcd (A.p * A.q) (A.q * A.p) = 1
    rw [hgcd, Nat.div_self hpos]
  · change (A.q * A.p) / Nat.gcd (A.p * A.q) (A.q * A.p) = 1
    rw [hgcd, Nat.mul_comm A.q A.p, Nat.div_self hpos]

/-- **Proposition 4.1, fourth identity — and sharper than the book states it.**
    The book gives `ρ(B ⊗ A) = ρ(Inv(A ⊗ B))`, after reduction. It holds
    *before* reduction, as an equality of presentations:

        B ⊗ A = Inv(A ⊗ B).

    Reversing the direction of comparison is relational inversion exactly, with
    no scale discarded. Since Def 1.5 reduction is many-to-one and lossy, an
    identity that survives without it is a stronger statement about the
    substrate, and this one does. -/
theorem otimes_swap (A B : IPres) : otimes B A = inv (otimes A B) :=
  eq_of (by simp [Nat.mul_comm]) (by simp [Nat.mul_comm])

/-- The book's form of Prop 4.1's fourth identity, now a corollary. -/
theorem reduce_otimes_swap (A B : IPres) :
    Pres.reduce (toPres (otimes B A)) = Pres.reduce (toPres (inv (otimes A B))) := by
  rw [otimes_swap]

/-! ## Proposition 4.2 — Directional composition is noncommutative -/

def threeTwo : IPres := ⟨3, 2, by decide, by decide⟩
def fiveThree : IPres := ⟨5, 3, by decide, by decide⟩

/-- The book's witnesses, computed: `(3:2) ⊗ (5:3) = 9:10`. -/
theorem otimes_threeTwo_fiveThree : otimes threeTwo fiveThree = ⟨9, 10, by decide, by decide⟩ := by
  decide

/-- And `(5:3) ⊗ (3:2) = 10:9`. -/
theorem otimes_fiveThree_threeTwo : otimes fiveThree threeTwo = ⟨10, 9, by decide, by decide⟩ := by
  decide

/-- **Proposition 4.2.** `⊗` is noncommutative. -/
theorem otimes_not_comm : ∃ A B : IPres, otimes A B ≠ otimes B A :=
  ⟨threeTwo, fiveThree, by decide⟩

/-- Non-commutativity is not an artefact of Def 1.3's strictness: the two orders
    are not even proportionally equivalent, so they differ as *values* too.
    `9 · 9 = 81`, `10 · 10 = 100`. -/
theorem otimes_not_comm_value :
    ∃ A B : IPres, ¬ Pres.Prop' (toPres (otimes A B)) (toPres (otimes B A)) :=
  ⟨threeTwo, fiveThree, by decide⟩

/-! ## Proposition 4.3 — Directional composition is nonassociative -/

def twoOne : IPres := ⟨2, 1, by decide, by decide⟩
def threeOne : IPres := ⟨3, 1, by decide, by decide⟩
def fiveOne : IPres := ⟨5, 1, by decide, by decide⟩

/-- `(A ⊗ B) ⊗ C = 2:15` for the book's witnesses. -/
theorem otimes_left_assoc_witness :
    otimes (otimes twoOne threeOne) fiveOne = ⟨2, 15, by decide, by decide⟩ := by decide

/-- `A ⊗ (B ⊗ C) = 10:3` for the same witnesses. -/
theorem otimes_right_assoc_witness :
    otimes twoOne (otimes threeOne fiveOne) = ⟨10, 3, by decide, by decide⟩ := by decide

/-- **Proposition 4.3.** `⊗` is nonassociative. Parentheses are mandatory; the
    grouping records the order in which successive comparisons were made. -/
theorem otimes_not_assoc :
    ∃ A B C : IPres, otimes (otimes A B) C ≠ otimes A (otimes B C) :=
  ⟨twoOne, threeOne, fiveOne, by decide⟩

/-- Again not an artefact of presentation-strictness: `2:15` and `10:3` are not
    proportionally equivalent either. `2 · 3 = 6`, `15 · 10 = 150`. -/
theorem otimes_not_assoc_value :
    ∃ A B C : IPres,
      ¬ Pres.Prop' (toPres (otimes (otimes A B) C)) (toPres (otimes A (otimes B C))) :=
  ⟨twoOne, threeOne, fiveOne, by decide⟩

/-! ## Definition 4.3 — Componentwise power -/

/-- **Definition 4.3.** `Pow_n(a:b) = aⁿ:bⁿ`. A *separate derived map*, and the
    warning attached to it in the book is that `⊗` must never be used for this. -/
def pow (n : ℕ) (A : IPres) : IPres :=
  ⟨A.p ^ n, A.q ^ n, Nat.pow_pos A.p_pos, Nat.pow_pos A.q_pos⟩

@[simp] theorem pow_p (n : ℕ) (A : IPres) : (pow n A).p = A.p ^ n := rfl
@[simp] theorem pow_q (n : ℕ) (A : IPres) : (pow n A).q = A.q ^ n := rfl

/-- **Definition 4.3, made exact.** The book says `Pow₂(A) ≠ A ⊗ A` "except in
    trivial cases". The exception set is exactly `{A : A.p = A.q}`, and nothing
    wider. So the two maps agree only on the diagonal, where `A ⊗ A` has already
    reduced to `1:1` — they never agree anywhere the composition carries
    content. -/
theorem pow_two_eq_otimes_self_iff (A : IPres) : pow 2 A = otimes A A ↔ A.p = A.q := by
  constructor
  · intro h
    have hp : A.p ^ 2 = A.p * A.q := congrArg IPres.p h
    rw [Nat.pow_two] at hp
    exact Nat.eq_of_mul_eq_mul_left A.p_pos hp
  · intro h
    refine eq_of ?_ ?_
    · change A.p ^ 2 = A.p * A.q
      rw [h, Nat.pow_two]
    · change A.q ^ 2 = A.q * A.p
      rw [← h, Nat.pow_two]

/-- **Definition 4.3, proportional form.** `Pow₂(A) ~ A ⊗ A` exactly when
    `A.p = A.q`. The cross-product of `a²:b²` with `ab:ab` is
    `a²·ab − b²·ab = ab(a − b)(a + b)`, which for `a, b > 0` vanishes only at
    `a = b`. The hypotheses are exactly those of the type `IPres` (`a, b > 0`):
    `A ⊗ A` is not a presentation on the boundary (`otimes_leaves_domain_on_boundary`),
    so the statement is on interior presentations only. For `a ≠ b` the two
    are therefore different presentations and also not proportionally
    equivalent. -/
theorem pow_two_prop_otimes_self_iff (A : IPres) :
    Pres.Prop' (toPres (pow 2 A)) (toPres (otimes A A)) ↔ A.p = A.q := by
  constructor
  · intro h
    have h1 : A.p ^ 2 * (A.q * A.p) = A.q ^ 2 * (A.p * A.q) := h
    have h2 : (A.p * A.q) * (A.p * A.p) = (A.p * A.q) * (A.q * A.q) := by
      calc (A.p * A.q) * (A.p * A.p) = A.p ^ 2 * (A.q * A.p) := by ring
        _ = A.q ^ 2 * (A.p * A.q) := h1
        _ = (A.p * A.q) * (A.q * A.q) := by ring
    have h3 : A.p * A.p = A.q * A.q :=
      Nat.eq_of_mul_eq_mul_left (Nat.mul_pos A.p_pos A.q_pos) h2
    exact Nat.mul_self_inj.mp h3
  · intro h
    have h' : A.q = A.p := h.symm
    change A.p ^ 2 * (A.q * A.p) = A.q ^ 2 * (A.p * A.q)
    rw [h']

/-- The separation is concrete: `Pow₂(2:1) = 4:1` while `(2:1) ⊗ (2:1) = 2:2`. -/
theorem pow_two_ne_otimes_self_witness : pow 2 twoOne ≠ otimes twoOne twoOne := by decide

/-- They are not proportionally equivalent either. `4 · 2 = 8`, `1 · 2 = 2`. -/
theorem pow_two_not_prop_otimes_self_witness :
    ¬ Pres.Prop' (toPres (pow 2 twoOne)) (toPres (otimes twoOne twoOne)) := by decide

/-! ## Definition 4.4 — Composition star -/

/-- **Definition 4.4.** For a finite ordered active relational family
    `𝒜_τ = (r₁, …, r_m)`, the composition star centred on `r` is
    `Σ_τ(r) = (r ⊗ r₁, …, r ⊗ r_m)`.

    A `List`, not a `Finset` and not a `Multiset`: the book says the order and
    all of the entries are retained, and a scalar summary of the star is not the
    star. The type is the place to enforce that. -/
def star (r : IPres) (fam : List IPres) : List IPres := fam.map (otimes r)

/-- The star is as long as the family: nothing is dropped. -/
@[simp] theorem star_length (r : IPres) (fam : List IPres) :
    (star r fam).length = fam.length := by simp [star]

/-- Position is preserved: the `i`-th entry of the star is `r ⊗` the `i`-th
    member of the family. The star is indexed by the family, not summarised
    over it. -/
theorem star_getElem? (r : IPres) (fam : List IPres) (i : ℕ) :
    (star r fam)[i]? = (fam[i]?).map (otimes r) := by
  simp [star]

/-- **Nothing in the star collapses.** `r ⊗ ·` is injective, so distinct members
    of the active family give distinct entries. The star is a faithful record of
    the family as seen from `r`, which is what makes "a scalar summary is not
    the star" a statement about lost information rather than about taste. -/
theorem otimes_left_injective (r : IPres) : Function.Injective (otimes r) := by
  intro A B h
  have hp : r.p * A.q = r.p * B.q := congrArg IPres.p h
  have hq : r.q * A.p = r.q * B.p := congrArg IPres.q h
  exact eq_of (Nat.eq_of_mul_eq_mul_left r.q_pos hq)
    (Nat.eq_of_mul_eq_mul_left r.p_pos hp)

/-- The star, computed. Centre `2:1`, family `(3:1, 5:1)`. -/
example : star twoOne [threeOne, fiveOne] = [⟨2, 3, by decide, by decide⟩,
    ⟨2, 5, by decide, by decide⟩] := by decide

/-! ## The projection layer

    Def 4.1's second half: under the rational reading `Pres.realize`, which is
    Def 1.7's `ν` on the interior (`Pres.nu_eq_finite_of_q_ne_zero`; every
    `IPres` has `q > 0`), `⊗` reads as division. **This is the only `ℚ` in §4**, and the
      direction of
    the statement matters — the substrate operation is the cross-product, and
    division is what a receiver sees, not what the substrate does. -/

/-- **Definition 4.1, projection layer.** `realize (A ⊗ B) = realize A / realize B`.
    Stated on `Pres.realize`, which is `ν` on the interior
    (`Pres.nu_eq_finite_of_q_ne_zero`); not stated on `ν` itself. -/
theorem realize_otimes (A B : IPres) :
    Pres.realize (toPres (otimes A B))
      = Pres.realize (toPres A) / Pres.realize (toPres B) := by
  have hAq : (A.q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr A.q_pos.ne'
  have hBp : (B.p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr B.p_pos.ne'
  have hBq : (B.q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr B.q_pos.ne'
  simp only [Pres.realize_eq_div]
  change ((A.p * B.q : ℕ) : ℚ) / ((A.q * B.p : ℕ) : ℚ)
      = ((A.p : ℕ) : ℚ) / ((A.q : ℕ) : ℚ) / (((B.p : ℕ) : ℚ) / ((B.q : ℕ) : ℚ))
  push_cast
  field_simp

end IPres
end RatioSpace
