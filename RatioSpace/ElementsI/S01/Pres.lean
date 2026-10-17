/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-!
  Elements I §1 — Distinction, presentation, and relational value.

  Definitions 1.2 through 1.7, complete, with the discipline of §0 built into the
  types rather than stated beside them:

    * Def 0.2  no `Real`, no `Float`. `ℚ` enters only through Def 1.7's `realize`, and is marked.
    * Def 0.3  equality is STRUCTURAL. There is deliberately no `Setoid` instance
               and no quotient. Proportional equivalence is a named relation and
               can never be mistaken for `=`.
    * Def 0.4  every relation here is decidable, so "exact" is a property the
               compiler checks rather than a promise the prose makes.
    * Def 0.5  no `axiom`, no `sorry`.

  Everything is computable.
-/

namespace RatioSpace

/-- **Definition 1.2 — Exact presentation.** An ordered pair, not a quotient and
    not a number. The colon denotes ordered relation; it is not division. -/
structure Pres where
  p : ℕ
  q : ℕ
  ne_zero : ¬(p = 0 ∧ q = 0)
deriving DecidableEq

namespace Pres

/-- **Definition 1.3 — Presentation equality.** Componentwise, and it is the
    type's own `=` (decided by the `DecidableEq Pres` derived above): two
    presentations are equal exactly when their components are equal. The whole
    point is that `1:2 ≠ 2:4`. -/
theorem eq_iff {A B : Pres} : A = B ↔ A.p = B.p ∧ A.q = B.q :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨hp, hq⟩ => by cases A; cases B; simp_all⟩

/-- **Definition 1.4 — Proportional equivalence.** A *declared* relation. -/
def Prop' (A B : Pres) : Prop := A.p * B.q = A.q * B.p

@[inherit_doc] infix:50 " ~ " => Prop'

instance : DecidableRel Prop' := fun A B => by unfold Prop'; infer_instance

theorem prop_refl (A : Pres) : A ~ A := by unfold Prop'; ring

theorem prop_symm {A B : Pres} (h : A ~ B) : B ~ A := by
  unfold Prop' at *
  rw [Nat.mul_comm B.p A.q, Nat.mul_comm B.q A.p]
  exact h.symm

theorem prop_trans {A B C : Pres} (hAB : A ~ B) (hBC : B ~ C) : A ~ C := by
  unfold Prop' at *
  rcases Nat.eq_zero_or_pos B.q with hq | hq
  · -- B.q = 0, so B.p ≠ 0, which forces A.q = 0 and C.q = 0
    have hp : B.p ≠ 0 := by
      intro h; exact B.ne_zero ⟨h, hq⟩
    have hAq : A.q = 0 := by
      rw [hq, Nat.mul_zero] at hAB
      rcases Nat.mul_eq_zero.mp hAB.symm with h | h
      · exact h
      · exact absurd h hp
    have hCq : C.q = 0 := by
      rw [hq, Nat.zero_mul] at hBC
      rcases Nat.mul_eq_zero.mp hBC with h | h
      · exact absurd h hp
      · exact h
    rw [hAq, hCq]; ring
  · -- B.q > 0, cancel it
    have key : B.q * (A.p * C.q) = B.q * (A.q * C.p) := by
      calc B.q * (A.p * C.q) = (A.p * B.q) * C.q := by ring
        _ = (A.q * B.p) * C.q := by rw [hAB]
        _ = A.q * (B.p * C.q) := by ring
        _ = A.q * (B.q * C.p) := by rw [hBC]
        _ = B.q * (A.q * C.p) := by ring
    exact Nat.eq_of_mul_eq_mul_left hq key

theorem prop_equivalence : Equivalence Prop' :=
  ⟨prop_refl, prop_symm, prop_trans⟩

/-- **Definition 1.5 — Primitive presentation.** -/
def Primitive (A : Pres) : Prop := Nat.gcd A.p A.q = 1

instance : DecidablePred Primitive := fun A => by unfold Primitive; infer_instance

/-- **Definition 1.5 — Reduction.** Many-to-one, and therefore a *declared* map
    off the tree rather than a harmless normalisation. -/
def reduce (A : Pres) : Pres :=
  ⟨A.p / Nat.gcd A.p A.q, A.q / Nat.gcd A.p A.q, by
    rintro ⟨h1, h2⟩
    have hp : A.p = 0 := by
      have h := Nat.div_mul_cancel (Nat.gcd_dvd_left A.p A.q)
      rw [h1, Nat.zero_mul] at h; exact h.symm
    have hq : A.q = 0 := by
      have h := Nat.div_mul_cancel (Nat.gcd_dvd_right A.p A.q)
      rw [h2, Nat.zero_mul] at h; exact h.symm
    exact A.ne_zero ⟨hp, hq⟩⟩

theorem gcd_pos (A : Pres) : 0 < Nat.gcd A.p A.q := by
  rcases Nat.eq_zero_or_pos (Nat.gcd A.p A.q) with h | h
  · exact absurd (And.intro (Nat.eq_zero_of_gcd_eq_zero_left h)
      (Nat.eq_zero_of_gcd_eq_zero_right h)) A.ne_zero
  · exact h

/-- Reduction lands in the primitive presentations. -/
theorem reduce_primitive (A : Pres) : Primitive (reduce A) :=
  Nat.coprime_div_gcd_div_gcd (gcd_pos A)

/-- A reduced presentation is proportionally equivalent to what it came from,
    which is exactly why reduction is lossy: it changes the presentation while
    preserving the value. -/
theorem reduce_prop (A : Pres) : reduce A ~ A := by
  change A.p / Nat.gcd A.p A.q * A.q = A.q / Nat.gcd A.p A.q * A.p
  have hp := Nat.div_mul_cancel (Nat.gcd_dvd_left A.p A.q)
  have hq := Nat.div_mul_cancel (Nat.gcd_dvd_right A.p A.q)
  calc A.p / Nat.gcd A.p A.q * A.q
      = A.p / Nat.gcd A.p A.q * (A.q / Nat.gcd A.p A.q * Nat.gcd A.p A.q) := by rw [hq]
    _ = A.q / Nat.gcd A.p A.q * (A.p / Nat.gcd A.p A.q * Nat.gcd A.p A.q) := by ring
    _ = A.q / Nat.gcd A.p A.q * A.p := by rw [hp]

/-- **Definition 1.6 — Exact relational order.** Division-free by construction. -/
def Lt (A B : Pres) : Prop := A.p * B.q < B.p * A.q

instance : DecidableRel Lt := fun A B => by unfold Lt; infer_instance

theorem lt_irrefl (A : Pres) : ¬ Lt A A := by unfold Lt; omega

/-- **Definition 1.6's second sentence, which is the point of the definition.**

    > For positive second components, neither `p:q ≺ r:s` nor `r:s ≺ p:q` holds
    > exactly when `p:q ∼ r:s`. Thus the equality induced by this value order is
    > proportional equivalence, not presentation equality.

    Irreflexivity of `Lt` (`lt_irrefl`) is a much weaker fact and does not
    imply it.

    **Proved without the positivity hypothesis, which is a strengthening.** The
    book restricts to positive second components; on ℕ the equivalence is
    trichotomy and needs no restriction, so the hypothesis is doing interpretive
    work (making `≺` readable as a *value* order) rather than logical work. The
    hypothesised form is `incomparable_iff_prop_of_pos` below, stated so the
    numbered item is present in the book's own shape as well.

    **Standard, borrowed.** Trichotomy on ℕ. The content is that the framework's
    division-free order induces *proportional equivalence* and not presentation
    equality, which `prop_ne_eq` witnesses. -/
theorem incomparable_iff_prop (A B : Pres) :
    (¬ Lt A B ∧ ¬ Lt B A) ↔ A ~ B := by
  unfold Lt Prop'
  constructor
  · rintro ⟨h₁, h₂⟩
    have hp : A.p * B.q = B.p * A.q := by omega
    calc A.p * B.q = B.p * A.q := hp
      _ = A.q * B.p := by ring
  · intro h
    have hp : A.p * B.q = B.p * A.q := by
      calc A.p * B.q = A.q * B.p := h
        _ = B.p * A.q := by ring
    exact ⟨by omega, by omega⟩

/-- Definition 1.6 in the book's own hypothesised shape, so the numbered item is
    represented as stated and not only in the stronger form above. -/
theorem incomparable_iff_prop_of_pos {A B : Pres} (_hA : 0 < A.q) (_hB : 0 < B.q) :
    (¬ Lt A B ∧ ¬ Lt B A) ↔ A ~ B :=
  incomparable_iff_prop A B

/-- **Definition 1.7 — Exact rational realization.** THE PROJECTION LAYER.
    `ℚ` enters Elements I only through this `realize`, and nothing upstream of it
    may mention `ℚ`. It does not recover the presentation it came from.

    **Written without division, and that is not a stylistic choice.** The
    obvious rendering `(A.p : ℚ) / (A.q : ℚ)` routes through `Rat.normalize`,
    which carries `Classical.choice` — in core Lean, with no Mathlib imported,
    checked. So every constant mentioning such a `realize` would inherit choice,
    and the import is unearned: `normalize`'s entire job is to reduce a fraction,
    and `reduce` has already done exactly that, exactly, on ℕ, with
    `reduce_primitive` in hand.

    `Rat.mk'` takes the numerator, the denominator, and the two obligations
    directly. Both are discharged from our own reduction. Nothing is
    approximated and the map is the same map.

    **The `q = 0` case** (the book's codomain is the Def 1.7 block below).
    Def 1.7's codomain is `ℚ≥0 ∪ {∞}` and ℚ has no `∞`, so the improper
    presentation is sent to `0`, as `p / 0 = 0` in Lean; here it is visible in
    the code. -/
def realize (A : Pres) : ℚ :=
  let R := reduce A
  if h : R.q = 0 then Rat.mk' 0 1 (by decide) (by decide)
  else Rat.mk' (R.p : ℤ) R.q h (by
        have hp : Nat.gcd R.p R.q = 1 := reduce_primitive A
        change Nat.Coprime ((R.p : ℤ)).natAbs R.q
        simpa [Nat.Coprime] using hp)

/-- `reduce` kills the denominator exactly when it was already dead. Needed to
    see that the `q = 0` case in `realize` fires on the same inputs that the
    division `p / q` sends to `0`. -/
theorem reduce_q_eq_zero_iff (A : Pres) : (reduce A).q = 0 ↔ A.q = 0 := by
  constructor
  · intro h
    have hd := Nat.div_mul_cancel (Nat.gcd_dvd_right A.p A.q)
    change A.q / Nat.gcd A.p A.q = 0 at h
    rw [h, Nat.zero_mul] at hd; exact hd.symm
  · intro h
    change A.q / Nat.gcd A.p A.q = 0
    simp [h]

/-- A rational built by `Rat.mk'` is the division it looks like. Pure plumbing
    between the choice-free construction and Mathlib's division. -/
theorem mk'_eq_div (n : ℤ) (d : ℕ) (h : d ≠ 0) (c : n.natAbs.Coprime d) :
    (Rat.mk' n d h c) = (n : ℚ) / (d : ℚ) :=
  (Rat.num_div_den (Rat.mk' n d h c)).symm

/-- **`realize` never produces a negative rational.** `reduce`'s numerator is a
    cast from `ℕ`, so unlike a general `Rat.mk'` there is no sign to lose. This
    is what lets `ProjValue.finite`'s carrier be Def 1.7's own `ℚ≥0`, not all of
    `ℚ`. -/
theorem realize_nonneg (A : Pres) : 0 ≤ realize A := by
  dsimp only [realize]
  split
  · decide
  · apply Rat.num_nonneg.mp
    change (0 : ℤ) ≤ ((A.reduce.p : ℕ) : ℤ)
    exact Int.natCast_nonneg _

/-- **The bridge, and the whole point of keeping it separate.** `realize` *is*
    `p/q`, so nothing about Def 1.7 has changed. But this equation is stated in
    Mathlib's division and therefore carries `Classical.choice`, while
    `realize` itself does not. Anything that only needs the coordinate stays
    choice-free; only what genuinely reasons about division pays, and it pays
    here, visibly, in one named lemma. -/
theorem realize_eq_div (A : Pres) : realize A = (A.p : ℚ) / (A.q : ℚ) := by
  have hprop : (reduce A).p * A.q = (reduce A).q * A.p := reduce_prop A
  dsimp only [realize]
  split
  · rename_i h
    have hq : A.q = 0 := (reduce_q_eq_zero_iff A).mp h
    rw [mk'_eq_div]; simp [hq]
  · rename_i h
    have hAq : A.q ≠ 0 := fun hz => h ((reduce_q_eq_zero_iff A).mpr hz)
    rw [mk'_eq_div]
    rw [div_eq_div_iff (by exact_mod_cast Nat.cast_ne_zero.mpr h)
        (by exact_mod_cast Nat.cast_ne_zero.mpr hAq)]
    rw [mul_comm ((A.p : ℚ)) _]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hprop

/-! ### Definition 1.7 — exact rational realization, on the codomain the book gives it

    `realize` above lands in `ℚ`, which has no `∞`, so it sends the improper
    presentation to `0` and thereby reads the two orientation anchors of Def 1.2
    the same way. **The book reads them apart**: Def 1.7's codomain is
    `ℚ≥0 ∪ {∞}`, and `ν(1:0) = ∞` while `ν(0:1) = 0`.

    The codomain is written as a named two-constructor type rather than as
    `Option ℚ`. `Option`'s `none` reads as *absence of a value*; the book's `∞`
    is the reading of a real, distinguishable anchor, and `1:0` is a presentation
    as legitimate as any other. The constructor is therefore named for the
    boundary it reads, and `nu_atBoundary_iff` says exactly which presentations
    reach it.

    Def 1.7 is written on the class `[p:q]`, so `ν` must be constant on
    proportional equivalence. That is `nu_of_prop`, proved without building a
    quotient type: `reduce` is a normal form for `~`, which is
    `reduce_eq_of_prop`. -/

/-- **Definition 1.7's codomain.** `ℚ≥0 ∪ {∞}`. The finite carrier is the
    nonnegative rationals themselves, not all of `ℚ`, so no negative finite
    reading can be formed.
    `Repr` is dropped rather than derived here: nothing downstream prints a
    `ProjValue`, and a manual instance would be new surface for no user. -/
inductive ProjValue where
  /-- A finite reading on the conventional rational line, carrying its own
      nonnegativity witness. -/
  | finite (v : {q : ℚ // 0 ≤ q}) : ProjValue
  /-- The reading of the improper presentation `p:0`, the book's `∞`. -/
  | atBoundary : ProjValue
deriving DecidableEq

/-- Componentwise extensionality for `Pres`. The `ne_zero` field is a `Prop`, so
    it carries no data to match. -/
theorem ext' {A B : Pres} (hp : A.p = B.p) (hq : A.q = B.q) : A = B := by
  cases A; cases B; simp_all

/-- **Two primitive proportional presentations are the same presentation.**
    Standard: coprimality turns the cross-product equation into mutual
    divisibility. -/
theorem eq_of_prop_of_primitive {A B : Pres} (hA : Primitive A) (hB : Primitive B)
    (h : A ~ B) : A = B := by
  have hcop : Nat.Coprime A.p A.q := hA
  have hcop' : Nat.Coprime B.p B.q := hB
  have hmul : A.p * B.q = A.q * B.p := h
  have hmul2 : B.q * A.p = B.p * A.q := by
    rw [Nat.mul_comm B.q A.p, hmul, Nat.mul_comm]
  have hp : A.p = B.p :=
    Nat.dvd_antisymm
      (Nat.Coprime.dvd_of_dvd_mul_left hcop ⟨B.q, hmul.symm⟩)
      (Nat.Coprime.dvd_of_dvd_mul_left hcop' ⟨A.q, hmul2⟩)
  have hq : A.q = B.q :=
    Nat.dvd_antisymm
      (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm ⟨B.p, hmul⟩)
      (Nat.Coprime.dvd_of_dvd_mul_left hcop'.symm ⟨A.p, hmul2.symm⟩)
  exact ext' hp hq

/-- **`reduce` is a normal form for `~`.** This is what lets Def 1.7 be written
    on the class `[p:q]` without a quotient type: the class has a computable
    canonical representative, and it is a presentation like any other. -/
theorem reduce_eq_of_prop {A B : Pres} (h : A ~ B) : reduce A = reduce B :=
  eq_of_prop_of_primitive (reduce_primitive A) (reduce_primitive B)
    (prop_trans (reduce_prop A) (prop_trans h (prop_symm (reduce_prop B))))

/-- `realize` only ever sees `reduce`, so it inherits the normal form. -/
theorem realize_of_prop {A B : Pres} (h : A ~ B) : realize A = realize B := by
  have hred : reduce A = reduce B := reduce_eq_of_prop h
  unfold realize
  simp only [hred]

/-- **Definition 1.7 — exact rational realization.** `ν([p:q]) = p/q`, on the
    book's own codomain. -/
def nu (A : Pres) : ProjValue :=
  if A.q = 0 then ProjValue.atBoundary
  else ProjValue.finite ⟨realize A, realize_nonneg A⟩

/-- `ν` reaches the boundary reading on exactly the improper presentations. -/
theorem nu_atBoundary_iff (A : Pres) : nu A = ProjValue.atBoundary ↔ A.q = 0 := by
  unfold nu; split <;> simp_all

/-- On every proper presentation `ν` is the finite coordinate, unchanged. So
    nothing that already reasoned through `realize` on the interior has moved. -/
theorem nu_eq_finite_of_q_ne_zero {A : Pres} (h : A.q ≠ 0) :
    nu A = ProjValue.finite ⟨realize A, realize_nonneg A⟩ := by
  unfold nu; simp [h]

/-- **`ν` is a function of the class, not of the presentation.** This is the
    content of the book's bracket. -/
theorem nu_of_prop {A B : Pres} (h : A ~ B) : nu A = nu B := by
  have hmul : A.p * B.q = A.q * B.p := h
  by_cases hA : A.q = 0
  · have hAp : A.p ≠ 0 := fun hz => A.ne_zero ⟨hz, hA⟩
    have hBq : B.q = 0 := by
      rw [hA, Nat.zero_mul] at hmul
      rcases Nat.mul_eq_zero.mp hmul with h' | h'
      · exact absurd h' hAp
      · exact h'
    unfold nu; simp [hA, hBq]
  · have hBq : B.q ≠ 0 := by
      intro hz
      rw [hz, Nat.mul_zero] at hmul
      rcases Nat.mul_eq_zero.mp hmul.symm with h' | h'
      · exact absurd h' hA
      · exact B.ne_zero ⟨h', hz⟩
    rw [nu_eq_finite_of_q_ne_zero hA, nu_eq_finite_of_q_ne_zero hBq]
    congr 1
    exact Subtype.ext (realize_of_prop h)

/-- On proper presentations, `realize` determines the reduced presentation:
    `Rat.mk'` of a reduced pair is the rational's own numerator and denominator. -/
theorem reduce_eq_of_realize_eq {A B : Pres} (hA : A.q ≠ 0) (hB : B.q ≠ 0)
    (h : realize A = realize B) : reduce A = reduce B := by
  have hA' : (reduce A).q ≠ 0 := fun hz => hA ((reduce_q_eq_zero_iff A).mp hz)
  have hB' : (reduce B).q ≠ 0 := fun hz => hB ((reduce_q_eq_zero_iff B).mp hz)
  unfold realize at h
  simp only [hA', hB', dite_false] at h
  have hn := congrArg Rat.num h
  have hd := congrArg Rat.den h
  simp only at hn hd
  exact ext' (by exact_mod_cast hn) hd

/-- **The converse of `nu_of_prop`.** Two presentations `ν` reads the same are
    proportionally equivalent: the boundary reading forces both second
    components to zero, and a finite reading fixes the reduced pair. -/
theorem prop_of_nu_eq {A B : Pres} (h : nu A = nu B) : A ~ B := by
  by_cases hA : A.q = 0
  · have hB : B.q = 0 := (nu_atBoundary_iff B).mp (h ▸ (nu_atBoundary_iff A).mpr hA)
    change A.p * B.q = A.q * B.p
    rw [hA, hB, Nat.mul_zero, Nat.zero_mul]
  · have hB : B.q ≠ 0 := fun hB =>
      hA ((nu_atBoundary_iff A).mp (h.trans ((nu_atBoundary_iff B).mpr hB)))
    rw [nu_eq_finite_of_q_ne_zero hA, nu_eq_finite_of_q_ne_zero hB] at h
    have hr : realize A = realize B := congrArg Subtype.val (ProjValue.finite.inj h)
    have hred := reduce_eq_of_realize_eq hA hB hr
    exact prop_trans (prop_symm (reduce_prop A)) (hred ▸ reduce_prop B)

/-- **`ν` reads exactly the class.** Def 1.7's bracket, both directions. -/
theorem nu_eq_iff_prop {A B : Pres} : nu A = nu B ↔ A ~ B :=
  ⟨prop_of_nu_eq, nu_of_prop⟩

/-- **`ν` is injective on primitive presentations.** Every class has one
    primitive member, so on primitives reading the same is being the same. -/
theorem nu_injective_on_primitive {A B : Pres} (hA : Primitive A) (hB : Primitive B)
    (h : nu A = nu B) : A = B :=
  eq_of_prop_of_primitive hA hB (prop_of_nu_eq h)

/-! #### The two orientation anchors, separated

    `F_∅ = (1:0, 0:1)` is the canonical frame of Def 2.2 precisely because its
    two endpoints are not the same thing. Under `realize` they are read the
    same. Under `ν` they are not. -/

/-- The left orientation anchor, `1:0`. -/
def anchorBoundary : Pres := ⟨1, 0, by decide⟩

/-- The right orientation anchor, `0:1`. -/
def anchorZero : Pres := ⟨0, 1, by decide⟩

theorem nu_anchorBoundary : nu anchorBoundary = ProjValue.atBoundary := by decide

theorem nu_anchorZero :
    nu anchorZero = ProjValue.finite ⟨realize anchorZero, realize_nonneg anchorZero⟩ :=
  nu_eq_finite_of_q_ne_zero (by decide)

/-- **The anchors separated, as a compiled witness.** The anchors are not proportionally
    equivalent, `realize` reads them identically anyway, and `ν` does not. -/
theorem nu_separates_the_anchors :
    ¬ (anchorBoundary ~ anchorZero)
      ∧ realize anchorBoundary = realize anchorZero
      ∧ nu anchorBoundary ≠ nu anchorZero := by
  refine ⟨by decide, by decide, ?_⟩
  rw [nu_anchorBoundary, nu_anchorZero]
  exact fun h => ProjValue.noConfusion h

/-- The whole improper family reads as the boundary, and the whole zero family
    reads as `0`. There is no third case: `ne_zero` forbids `0:0`. -/
theorem nu_boundary_family (p : ℕ) (h : ¬(p = 0 ∧ (0:ℕ) = 0)) :
    nu ⟨p, 0, h⟩ = ProjValue.atBoundary := by
  rw [nu_atBoundary_iff]


/-! ### The separation, made concrete

    These are the examples from the book, and they are the whole reason the
    types are arranged this way. -/

def oneTwo : Pres := ⟨1, 2, by decide⟩
def twoFour : Pres := ⟨2, 4, by decide⟩

/-- `1:2 ≠ 2:4` as presentations. Definition 1.3. -/
theorem oneTwo_ne_twoFour : oneTwo ≠ twoFour := by decide

/-- `1:2 ~ 2:4` as values. Definition 1.4. **Both are true at once, and keeping
    them apart is what the type system is for.** -/
theorem oneTwo_prop_twoFour : oneTwo ~ twoFour := by decide

/-- **And the induced equality is not presentation equality.** `1:2` and `2:4`
    are incomparable under `≺`, hence equal as values, and remain distinct
    presentations. This is the separation Definition 1.6's last sentence
    asserts, as a compiled witness rather than as prose. -/
theorem prop_ne_eq :
    (¬ Lt oneTwo twoFour ∧ ¬ Lt twoFour oneTwo) ∧ oneTwo ~ twoFour
      ∧ oneTwo ≠ twoFour := by
  refine ⟨?_, oneTwo_prop_twoFour, by decide⟩
  exact (incomparable_iff_prop oneTwo twoFour).mpr oneTwo_prop_twoFour


/-- `1:2` is primitive, `2:4` is not. -/
theorem oneTwo_primitive : Primitive oneTwo := by decide
theorem twoFour_not_primitive : ¬ Primitive twoFour := by decide

/-- Reduction really does collapse the distinction. -/
theorem reduce_twoFour : reduce twoFour = oneTwo := by decide

/-- A primitive presentation is its own reduction. -/
theorem reduce_of_primitive {A : Pres} (hA : Primitive A) : reduce A = A :=
  eq_of_prop_of_primitive (reduce_primitive A) hA (reduce_prop A)

/-- **`reduce` is idempotent.** Definition 1.5. -/
theorem reduce_reduce (A : Pres) : reduce (reduce A) = reduce A :=
  reduce_of_primitive (reduce_primitive A)

/-- **`reduce` is many-to-one.** `1:2` and `2:4` are different presentations
    with the same reduction. -/
theorem reduce_not_injective : ¬ Function.Injective reduce := fun h =>
  (by decide : oneTwo ≠ twoFour)
    (h ((reduce_of_primitive oneTwo_primitive).trans reduce_twoFour.symm))

end Pres
end RatioSpace
