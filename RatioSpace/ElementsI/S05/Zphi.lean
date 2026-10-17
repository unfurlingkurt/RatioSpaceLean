/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-!
  Elements I §5.7-5.9 — the exact golden element, as its own ring.

  Def 5.7, verbatim: *"At the substrate level, powers of φ are handled
  symbolically in the exact algebraic ring determined by φ² − φ − 1 = 0.
  Decimal approximations are display values only."*

  That is a specification, not a hint, and it is the single most important type
  decision in Elements I. `Real.goldenRatio` is not available here and never was:
  Def 0.2 admits no `Real` anywhere in Elements I or II.

  So `ℤ[φ]` is a bespoke `structure Zphi where a b : ℤ`, read as `a + bφ`, with
  multiplication reducing by `φ² = φ + 1`. Equality is componentwise and
  therefore decidable, which is what makes Def 5.9's tie relation a computation
  rather than a promise.

  This is the reason this file needs no localisation:
  **φ is a unit in `ℤ[φ]`**, with `φ⁻¹ = φ − 1`, since `φ(φ−1) = φ² − φ = 1`.
  Every negative power of φ therefore stays inside the ring, so Def 5.8's
  `∑ φ^(−T)` has carrier `ℤ[φ]` itself. No symbolic-exponent carrier, no
  fraction field, no quotient.

  The order at the bottom is what makes Def 5.8's own sentence — *"No
  floating-point evaluation is required to compare two such values"* — a theorem
  instead of a remark. It is pulled back from mathlib's `ℤ[√5]` through the
  exact injective doubling `a + bφ ↦ (2a + b) + b√5`, so comparison is an
  integer decision procedure that runs.
-/

namespace RatioSpace

/-- **Definition 5.7 — Exact golden element.** An element of `ℤ[φ]`, written
    `a + bφ`. Not a real number, not an approximation, and not a primitive
    rational presentation. -/
structure Zphi where
  a : ℤ
  b : ℤ
deriving DecidableEq

namespace Zphi

@[ext] theorem ext : ∀ {x y : Zphi}, x.a = y.a → x.b = y.b → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

instance : Zero Zphi := ⟨⟨0, 0⟩⟩
instance : One Zphi := ⟨⟨1, 0⟩⟩
instance : Add Zphi := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg Zphi := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub Zphi := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩

/-- Multiplication, with the single reduction `φ² = φ + 1` folded in. -/
instance : Mul Zphi :=
  ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

@[simp] theorem zero_a : (0 : Zphi).a = 0 := rfl
@[simp] theorem zero_b : (0 : Zphi).b = 0 := rfl
@[simp] theorem one_a : (1 : Zphi).a = 1 := rfl
@[simp] theorem one_b : (1 : Zphi).b = 0 := rfl
@[simp] theorem add_a (x y : Zphi) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : Zphi) : (x + y).b = x.b + y.b := rfl
@[simp] theorem neg_a (x : Zphi) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : Zphi) : (-x).b = -x.b := rfl
@[simp] theorem sub_a (x y : Zphi) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : Zphi) : (x - y).b = x.b - y.b := rfl
@[simp] theorem mul_a (x y : Zphi) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem mul_b (x y : Zphi) :
    (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

instance commRing : CommRing Zphi where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (-·)
  sub := (· - ·)
  nsmul := @nsmulRec Zphi ⟨0⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec Zphi ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec Zphi ⟨0⟩ ⟨(· + ·)⟩)
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  neg_add_cancel := by intros; ext <;> simp
  mul_comm := by intros; ext <;> simp <;> ring
  sub_eq_add_neg := by intros; ext <;> simp <;> ring

instance : Nontrivial Zphi := ⟨⟨0, 1, by decide⟩⟩

/-- Display only. Def 5.7 is explicit that decimal approximations are display
    values; this one is not even decimal, it prints the exact pair as `a + bφ`,
    so nothing that reaches the eye has left the ring. -/
instance : Repr Zphi where
  reprPrec z _ :=
    if z.b = 0 then repr z.a
    else if z.a = 0 then (if z.b = 1 then "φ" else s!"{z.b}φ")
    else if z.b > 0 then s!"{z.a} + {if z.b = 1 then "" else toString z.b}φ"
    else s!"{z.a} - {if z.b = -1 then "" else toString (-z.b)}φ"

/-- The golden element itself, `φ = 0 + 1·φ`. -/
def phi : Zphi := ⟨0, 1⟩

/-- **The defining relation, machine-checked.** `φ² = φ + 1`. Everything in this
    file is a consequence of this one line. -/
theorem phi_sq : phi * phi = phi + 1 := by decide

/-- `φ⁻¹ = φ − 1`. This is a *definition inside the ring*, not a localisation:
    `ℤ[φ]` already contains it. -/
def phiInv : Zphi := ⟨-1, 1⟩

theorem phiInv_eq_phi_sub_one : phiInv = phi - 1 := by decide

/-- **φ is a unit.** This is the whole reason Def 5.8 needs no fraction field. -/
@[simp] theorem phi_mul_phiInv : phi * phiInv = 1 := by decide

@[simp] theorem phiInv_mul_phi : phiInv * phi = 1 := by decide

/-- `φ⁻ᵀ` for a nonnegative integer depth `T`, exactly, inside `ℤ[φ]`. This is
    the term Def 5.8 sums. -/
def phiNegPow (T : ℕ) : Zphi := phiInv ^ T

@[simp] theorem phiNegPow_zero : phiNegPow 0 = 1 := rfl

@[simp] theorem phiPow_mul_phiNegPow (T : ℕ) : phi ^ T * phiNegPow T = 1 := by
  rw [phiNegPow, ← mul_pow, phi_mul_phiInv, one_pow]

/-- **Closed form for the positive powers.** `φ^(n+1) = F(n) + F(n+1)·φ`.
    Standard (the Fibonacci–`ℤ[φ]` correspondence is classical); recorded here
    because it is what lets a coherence value be *computed* rather than unfolded
    step by step. -/
theorem phi_pow_succ (n : ℕ) : phi ^ (n + 1) = ⟨Nat.fib n, Nat.fib (n + 1)⟩ := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [pow_succ, ih]
    ext
    · simp [phi]
    · simp [phi, Nat.fib_add_two]

/-- **Closed form for the negative powers**, the ones Def 5.8 actually uses.
    `φ^(−n) = (−1)ⁿ F(n+1) + (−1)^(n+1) F(n)·φ`, exactly, with no division. -/
theorem phiNegPow_eq (n : ℕ) :
    phiNegPow n = ⟨(-1) ^ n * Nat.fib (n + 1), (-1) ^ (n + 1) * Nat.fib n⟩ := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [phiNegPow, pow_succ, ← phiNegPow, ih]
    ext
    · simp [phiInv, Nat.fib_add_two, pow_succ]
      ring
    · simp [phiInv, pow_succ]

/-- **Definition 5.8 — Global φ-coherence.** `C_φ(r) = ∑ φ^(−T_end(r, rᵢ))`
    over the finite active family. The list is the ordered tension signature of
    Def 5.6; the order is not used by the sum, and that is exactly the
    information `C_φ` discards. -/
def coherence (T : List ℕ) : Zphi := (T.map phiNegPow).sum

@[simp] theorem coherence_nil : coherence [] = 0 := rfl

@[simp] theorem coherence_cons (T : ℕ) (Ts : List ℕ) :
    coherence (T :: Ts) = phiNegPow T + coherence Ts := rfl

theorem coherence_append (Ts Ss : List ℕ) :
    coherence (Ts ++ Ss) = coherence Ts + coherence Ss := by
  simp [coherence, List.map_append, List.sum_append]

/-- **Not Definition 5.9.** Two raw signature lists tie under the coherence
    fold. The degeneracy relation of Elements I, Definition 5.9 has three
    inputs in substance — candidates `r`, `s`, and the family they share — and
    every book instance implies this list equality under substitution, but the
    converse does not hold and this relation also classifies list pairs
    arising from no candidates and no common family at all.
    `CoherenceDegenerate` (`Coherence.lean`) is Def 5.9 itself; this is the helper it is
    built from. Because equality in `ℤ[φ]` is componentwise, it is decidable,
    and the instance below is what makes that claim inspectable. -/
def SignatureSumDegenerate (Ts Ss : List ℕ) : Prop := coherence Ts = coherence Ss

instance (Ts Ss : List ℕ) : Decidable (SignatureSumDegenerate Ts Ss) := by
  unfold SignatureSumDegenerate; infer_instance

/-- **The book's own witness that `C_φ` is not injective:** `1 = φ⁻¹ + φ⁻²`. -/
theorem phiNegPow_one_add_two : phiNegPow 1 + phiNegPow 2 = 1 := by decide

/-- The same fact as a signature-sum tie: a single anchor at depth 0 and a
    two-anchor family at depths 1 and 2 have equal coherence, so the scalar
    has compressed two different contribution patterns. **Not yet a witness of
    Def 5.9**: this pair has unequal length, which under one fixed
    family cannot happen; `CoherenceDegenerate` (`Coherence.lean`) carries the family that
    makes the comparison meaningful. -/
theorem book_degeneracy : SignatureSumDegenerate [1, 2] [0] := by decide

/-- A second, sharper tie the book does not name: depths `[1, 4]` and
    `[2, 2]` also agree. Two anchors, same count, different signatures — the
    cardinality one fixed family requires, still with no family attached. -/
theorem degeneracy_one_four : SignatureSumDegenerate [1, 4] [2, 2] := by decide

/-! ### The exact order

Def 5.8 says two coherence values can be compared with no floating-point
evaluation. That is an order claim, so it is discharged here as one.

The order is pulled back from mathlib's `ℤ[√5]` along `a + bφ ↦ (2a + b) + b√5`,
which is exactly `z ↦ 2z` under the (never-constructed) real embedding. The map
is injective and additive but deliberately *not* a ring map — the factor of two
is precisely what makes `ℤ[φ]` strictly larger than `ℤ[√5]`, and it is carried
explicitly in `emb_mul` rather than hidden. -/

/-- `ℤ[√5]`. -/
abbrev Z5 : Type := Zsqrtd ((5 : ℕ) : ℤ)

instance : Zsqrtd.Nonsquare 5 :=
  ⟨fun n => by
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | (k + 3) => have h : 3 * 3 ≤ (k + 3) * (k + 3) := Nat.mul_le_mul (by omega) (by omega)
                 omega⟩

/-- The exact doubling `z ↦ 2z`, landing in `ℤ[√5]`. -/
def emb (z : Zphi) : Z5 := ⟨2 * z.a + z.b, z.b⟩

theorem emb_injective : Function.Injective emb := by
  intro x y h
  have h1 : 2 * x.a + x.b = 2 * y.a + y.b := congrArg Zsqrtd.re h
  have h2 : x.b = y.b := congrArg Zsqrtd.im h
  ext
  · omega
  · omega

@[simp] theorem emb_zero : emb 0 = 0 := rfl

theorem emb_add (x y : Zphi) : emb (x + y) = emb x + emb y := by
  ext
  · simp [emb]; ring
  · simp [emb]

/-- The doubling made explicit: `emb` is not multiplicative, and the discrepancy
    is exactly the factor of two. -/
theorem emb_mul (x y : Zphi) : emb x * emb y = 2 * emb (x * y) := by
  ext <;> (simp [emb, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring)

instance instLEZphi : LE Zphi := ⟨fun x y => emb x ≤ emb y⟩
instance instLTZphi : LT Zphi := ⟨fun x y => emb x < emb y⟩

theorem le_def {x y : Zphi} : x ≤ y ↔ emb x ≤ emb y := Iff.rfl
theorem lt_def {x y : Zphi} : x < y ↔ emb x < emb y := Iff.rfl

instance decidableLE : DecidableLE Zphi :=
  fun _ _ => decidable_of_iff _ le_def.symm

instance decidableLT : DecidableLT Zphi :=
  fun _ _ => decidable_of_iff _ lt_def.symm

instance linearOrder : LinearOrder Zphi where
  le := instLEZphi.le
  lt := instLTZphi.lt
  le_refl x := le_refl (emb x)
  le_trans _ _ _ h₁ h₂ := le_trans (a := emb _) h₁ h₂
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge (a := emb _)
  le_antisymm _ _ h₁ h₂ := emb_injective (le_antisymm h₁ h₂)
  le_total x y := le_total (emb x) (emb y)
  toDecidableLE := decidableLE
  toDecidableLT := decidableLT
  toDecidableEq := inferInstance

instance : IsOrderedAddMonoid Zphi where
  add_le_add_left a b hab c := by
    have h : emb a ≤ emb b := le_def.mp hab
    refine le_def.mpr ?_
    rw [emb_add, emb_add]
    exact add_le_add_left h _

instance : ZeroLEOneClass Zphi := ⟨by decide⟩

/-- Positivity is closed under multiplication, routed through `ℤ[√5]`'s own
    decidable primitives (`Zsqrtd.mul_nonneg`, its zero-divisor lemma) rather
    than mathlib's generic ordered-ring `mul_pos`, which is where
    `Classical.choice` enters.
    The factor of two in `emb_mul` is removed by the order itself: if `w < 0`
    then `2w = w + w < 0`. -/
protected theorem mul_pos (x y : Zphi) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  rw [lt_def, emb_zero] at hx hy ⊢
  have hprod : (0 : Z5) ≤ 2 * emb (x * y) := by
    rw [← emb_mul]; exact Zsqrtd.mul_nonneg _ _ hx.le hy.le
  have hle : (0 : Z5) ≤ emb (x * y) := by
    by_cases h : (0 : Z5) ≤ emb (x * y)
    · exact h
    · have hneg : emb (x * y) < 0 := lt_of_not_ge h
      have h2 : 2 * emb (x * y) < 0 := by rw [two_mul]; exact add_neg hneg hneg
      exact absurd hprod (not_le_of_gt h2)
  have hne : emb (x * y) ≠ 0 := by
    intro h0
    have h00 : emb x * emb y = 0 := by rw [emb_mul, h0, mul_zero]
    rcases Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero h00 with h | h
    · exact (ne_of_gt hx) h
    · exact (ne_of_gt hy) h
  exact lt_of_le_of_ne hle (Ne.symm hne)

theorem emb_add_sub_add (a b c : Zphi) : emb (a + c) - emb (a + b) = emb c - emb b := by
  ext
  · simp [emb]; ring
  · simp [emb]

theorem emb_zero_sub_sub (x y : Zphi) : emb 0 - emb (y - x) = emb x - emb y := by
  ext
  · simp [emb]; ring
  · simp [emb]

/-- `sub_pos` at `ℤ[φ]`, read off `Zsqrtd.Nonneg` directly. The generic lemma
    goes through the ordered-group API and carries `Classical.choice`. -/
protected theorem sub_pos {x y : Zphi} : 0 < y - x ↔ x < y := by
  change ¬ Zsqrtd.Nonneg (emb 0 - emb (y - x)) ↔ ¬ Zsqrtd.Nonneg (emb x - emb y)
  rw [emb_zero_sub_sub]

protected theorem le_of_add_le_add_left (a b c : Zphi) (h : a + b ≤ a + c) : b ≤ c := by
  change Zsqrtd.Nonneg (emb c - emb b)
  rw [← emb_add_sub_add a]
  exact h

/-- Built field by field rather than by `IsStrictOrderedRing.of_mul_pos`, whose
    `simpa`/`sub_pos` route and the derived cancellative-monoid instance both
    carry `Classical.choice`. Every field here reduces to `Zsqrtd.Nonneg`. -/
instance : IsStrictOrderedRing Zphi where
  le_of_add_le_add_left := Zphi.le_of_add_le_add_left
  mul_lt_mul_of_pos_left a ha b c hbc := by
    have h := Zphi.mul_pos a (c - b) ha (Zphi.sub_pos.mpr hbc)
    rw [mul_sub] at h
    exact Zphi.sub_pos.mp h
  mul_lt_mul_of_pos_right a ha b c hbc := by
    have h := Zphi.mul_pos (c - b) a (Zphi.sub_pos.mpr hbc) ha
    rw [sub_mul] at h
    exact Zphi.sub_pos.mp h

theorem phiInv_pos : 0 < phiInv := by decide

theorem phiInv_lt_one : phiInv < 1 := by decide

theorem one_lt_phi : 1 < phi := by decide

theorem phiNegPow_pos (T : ℕ) : 0 < phiNegPow T := pow_pos phiInv_pos T

/-- **Def 5.8's ordering claim, as a theorem.** *"Because shorter contrast depth
    contributes a larger term, `C_φ` is a coherence quantity to maximize."* The
    comparison is an exact integer decision; nothing is evaluated numerically. -/
theorem phiNegPow_strictAnti : StrictAnti phiNegPow :=
  pow_right_strictAnti₀ phiInv_pos phiInv_lt_one

/-- Shortening one anchor's contrast depth strictly increases global coherence.
    This is what "maximize" means, stated over the family rather than the term. -/
theorem coherence_lt_of_lt (pre suf : List ℕ) {S T : ℕ} (h : S < T) :
    coherence (pre ++ T :: suf) < coherence (pre ++ S :: suf) := by
  have h₁ : phiNegPow T < phiNegPow S := phiNegPow_strictAnti h
  rw [coherence_append, coherence_append, coherence_cons, coherence_cons, ← Zphi.sub_pos]
  have hd : coherence pre + (phiNegPow S + coherence suf) -
      (coherence pre + (phiNegPow T + coherence suf)) = phiNegPow S - phiNegPow T := by ring
  rw [hd]
  exact Zphi.sub_pos.mpr h₁

/-- **The two objectives are not the same one.** Def 5.8: *"minimize one local
    tension"* and *"maximize the complete global coherence"* are not generally
    equivalent when several anchors are present. Here is the witness. Candidate
    `r` holds the strictly smaller local tension, and candidate `s` holds the
    strictly greater global coherence. Both facts are decided exactly.
    **The witness is algebraic, not yet geometric**:
    `[1, 10]` and `[2, 2]` are asserted as signatures, with no proof that
    either arises from a real candidate against a real shared family. `Coherence.lean`
    restates this separation for two genuine `IPres` candidates against one
    common family, `coherence_witness_separates`. -/
theorem coherence_one_ten_lt_two_two : coherence [1, 10] < coherence [2, 2] := by
  -- The gap is not compared numerically. It is *identified*: it is `4φ⁻⁷`,
  -- and `φ⁻⁷` is positive because `φ⁻¹` is.
  have h : coherence [2, 2] - coherence [1, 10] = 4 * phiNegPow 7 := by decide
  have hp : (0 : Zphi) < coherence [2, 2] - coherence [1, 10] := by
    rw [h]; exact Zphi.mul_pos 4 _ (by decide) (phiNegPow_pos 7)
  exact Zphi.sub_pos.mp hp

theorem local_min_ne_global_max :
    ([1, 10] : List ℕ).min? = some 1 ∧
    ([2, 2] : List ℕ).min? = some 2 ∧
    1 < 2 ∧
    coherence [1, 10] < coherence [2, 2] :=
  ⟨by decide, by decide, by decide, coherence_one_ten_lt_two_two⟩

/-! ### Definition 5.7's recursive map, its fixed point and its tangent slope (the book's
  "derivative")

    Def 5.7: *"The recursive map `f(x) = 1 + 1/x` has the positive fixed
    point `φ`, with exact derivative at the fixed point `f'(φ) = -φ^(-2)`."*

    Each clause is stated:

    * the map, `recMap u = 1 + u⁻¹` on the units of `ℤ[φ]` (`ℤ[φ]` is not a
      field, so `1/x` is read where it exists, at a unit);
    * the fixed point, `recMap_phi` (`f(φ) = φ`, from `phi_fixed_point`:
      `1 + φ⁻¹ = φ`), and its uniqueness among positive units,
      `recMap_fixed_pos` (the only other fixed point is `1 - φ = -φ⁻¹ < 0`,
      `recMap_fixed_iff`);
    * a tangent slope (uniqueness not stated): the exact slope
      identity `f(u) - f(v) = -u⁻¹v⁻¹ · (u - v)` for every pair of units
      (`recMap_sub`), whose coefficient `recSlope u v = -u⁻¹v⁻¹` at `u = v = φ`
      is `-φ⁻² = φ - 2` (`recSlope_phi`); and the tangent form
      `f(u) = f(v) + s(v, v)(u - v) + v⁻²u⁻¹(u - v)²` (`recMap_tangent`, at `φ`
      `recMap_tangent_phi`), which is what makes `s(v, v)` a tangent slope
      (uniqueness not stated).

    What is not formalised: the analytic derivative, the limit of the difference
    quotient over the reals. Def 0.2 admits no `Real`, and none is needed to
    state the value: the slope coefficient on the diagonal is a tangent slope
    (uniqueness not stated), and here it is an element of `ℤ[φ]` with integer
    coefficients `(-2, 1)`. Def 5.7's close types the fixed point as *"a derived
    completion structure, not an additional freely chosen substrate
    coordinate"*; nothing here makes it a substrate coordinate. Elements II
    Theorem 27.3 meets the same root on columns (`Two.Chamber.ridgeR_fixed`,
    `ridgeR_unique`); Elements I does not import it. -/

/-- `φ⁻² = 2 - φ`, from `φ⁻¹ = φ - 1` squared and reduced by `φ² = φ + 1`. -/
theorem phiNegPow_two_eq : phiNegPow 2 = 2 - phi := by decide

/-- `φ - 2 = -φ⁻²`: the ring identity, and nothing more. The tangent slope at `φ`,
    which stands for the book's derivative, is `recSlope_phi`. -/
theorem phiNegPow_two_eq_neg : phi - 2 = -phiNegPow 2 := by decide

/-- **The fixed-point equation**, `1 + φ⁻¹ = φ`. -/
theorem phi_fixed_point : 1 + phiInv = phi := by decide

/-- `φ` as a unit of `ℤ[φ]`, with inverse `phiInv`. -/
def phiUnit : Zphiˣ := ⟨phi, phiInv, phi_mul_phiInv, phiInv_mul_phi⟩

@[simp] theorem phiUnit_val : (phiUnit : Zphi) = phi := rfl

@[simp] theorem phiUnit_inv_val : ((phiUnit⁻¹ : Zphiˣ) : Zphi) = phiInv := rfl

/-- **Definition 5.7's recursive map** `f(x) = 1 + 1/x`, on the units of `ℤ[φ]`,
    where `1/x` exists. -/
def recMap (u : Zphiˣ) : Zphi := 1 + ((u⁻¹ : Zphiˣ) : Zphi)

/-- **`φ` is a fixed point of `f`.** -/
theorem recMap_phi : recMap phiUnit = phi := phi_fixed_point

/-- A unit is fixed by `f` exactly when it is a root of `x² - x - 1`. -/
theorem recMap_eq_self_iff (u : Zphiˣ) :
    recMap u = u ↔ (u : Zphi) * u = u + 1 := by
  have h1 : (u : Zphi) * ((u⁻¹ : Zphiˣ) : Zphi) = 1 := u.mul_inv
  unfold recMap
  constructor
  · intro h
    calc (u : Zphi) * u = u * (1 + ((u⁻¹ : Zphiˣ) : Zphi)) := by rw [h]
      _ = u + u * ((u⁻¹ : Zphiˣ) : Zphi) := by ring
      _ = u + 1 := by rw [h1]
  · intro h
    calc 1 + ((u⁻¹ : Zphiˣ) : Zphi)
        = (u : Zphi) * ((u⁻¹ : Zphiˣ) : Zphi) + ((u⁻¹ : Zphiˣ) : Zphi) := by rw [h1]
      _ = ((u⁻¹ : Zphiˣ) : Zphi) * (u + 1) := by ring
      _ = ((u⁻¹ : Zphiˣ) : Zphi) * (u * u) := by rw [h]
      _ = ((u : Zphi) * ((u⁻¹ : Zphiˣ) : Zphi)) * u := by ring
      _ = u := by rw [h1, one_mul]

/-- `x² - x - 1 = (x - φ)(x - (1 - φ))` in `ℤ[φ]`: the two roots are `φ` and
    its conjugate `1 - φ = -φ⁻¹`. -/
theorem golden_poly_factor (x : Zphi) :
    x * x - x - 1 = (x - phi) * (x - (1 - phi)) := by
  calc x * x - x - 1 = x * x - x - (phi * phi - phi) := by rw [phi_sq]; ring
    _ = (x - phi) * (x - (1 - phi)) := by ring

/-- `ℤ[φ]` has no zero divisors, read through `emb` from `ℤ[√5]`'s own lemma
    (the generic `mul_eq_zero` at `ℤ[φ]` carries `Classical.choice`; this does
    not). -/
theorem mul_eq_zero_split {x y : Zphi} (h : x * y = 0) :
    x = 0 ∨ y = 0 := by
  have h' : emb x * emb y = 0 := by rw [emb_mul, h]; rfl
  rcases Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero h' with h0 | h0
  · exact Or.inl (emb_injective (h0.trans emb_zero.symm))
  · exact Or.inr (emb_injective (h0.trans emb_zero.symm))

/-- The conjugate root is negative: `1 - φ < 0`. -/
theorem one_sub_phi_neg : 1 - phi < 0 := by decide

/-- **The fixed points of `f`.** A unit is fixed by `f` exactly when it is `φ`
    or `1 - φ`. -/
theorem recMap_fixed_iff (u : Zphiˣ) :
    recMap u = u ↔ (u : Zphi) = phi ∨ (u : Zphi) = 1 - phi := by
  rw [recMap_eq_self_iff]
  constructor
  · intro h
    have h0 : ((u : Zphi) - phi) * ((u : Zphi) - (1 - phi)) = 0 := by
      rw [← golden_poly_factor, h]; ring
    rcases mul_eq_zero_split h0 with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (sub_eq_zero.mp h')
  · rintro (h | h)
    · rw [h]; exact phi_sq
    · rw [h]; decide

/-- **`φ` is the positive fixed point of `f`**, and the only one. -/
theorem recMap_fixed_pos (u : Zphiˣ) (hf : recMap u = u) (hpos : 0 < (u : Zphi)) :
    (u : Zphi) = phi := by
  rcases (recMap_fixed_iff u).mp hf with h | h
  · exact h
  · exact absurd (h ▸ hpos) (lt_asymm one_sub_phi_neg)

/-- The slope of `f` between two units: `-u⁻¹v⁻¹`. -/
def recSlope (u v : Zphiˣ) : Zphi := -(((u⁻¹ : Zphiˣ) : Zphi) * ((v⁻¹ : Zphiˣ) : Zphi))

/-- **The exact slope identity of `f`.** `f(u) - f(v) = -u⁻¹v⁻¹ · (u - v)` for
    every pair of units, with no limit and no division. -/
theorem recMap_sub (u v : Zphiˣ) :
    recMap u - recMap v = recSlope u v * ((u : Zphi) - v) := by
  have hu : (u : Zphi) * ((u⁻¹ : Zphiˣ) : Zphi) = 1 := u.mul_inv
  have hv : (v : Zphi) * ((v⁻¹ : Zphiˣ) : Zphi) = 1 := v.mul_inv
  unfold recMap recSlope
  calc 1 + ((u⁻¹ : Zphiˣ) : Zphi) - (1 + ((v⁻¹ : Zphiˣ) : Zphi))
      = ((u⁻¹ : Zphiˣ) : Zphi) * 1 - ((v⁻¹ : Zphiˣ) : Zphi) * 1 := by ring
    _ = ((u⁻¹ : Zphiˣ) : Zphi) * ((v : Zphi) * ((v⁻¹ : Zphiˣ) : Zphi))
        - ((v⁻¹ : Zphiˣ) : Zphi) * ((u : Zphi) * ((u⁻¹ : Zphiˣ) : Zphi)) := by
          rw [hu, hv]
    _ = -(((u⁻¹ : Zphiˣ) : Zphi) * ((v⁻¹ : Zphiˣ) : Zphi)) * ((u : Zphi) - v) := by ring

/-- **`f` is its tangent line plus a square.** For every pair of units,
    `f(u) = f(v) + s(v, v) · (u - v) + v⁻²u⁻¹ · (u - v)²`, exactly, where
    `s = recSlope`. The error of the line through `f(v)` with slope `s(v, v)`
    is divisible by `(u - v)²`: `s(v, v)` is a tangent slope of the rational
    map `f` at `v`, no limit (its uniqueness is not in the tree). -/
theorem recMap_tangent (u v : Zphiˣ) :
    recMap u - recMap v - recSlope v v * ((u : Zphi) - v)
      = ((v⁻¹ : Zphiˣ) : Zphi) * ((v⁻¹ : Zphiˣ) : Zphi) * ((u⁻¹ : Zphiˣ) : Zphi)
          * (((u : Zphi) - v) * ((u : Zphi) - v)) := by
  have hu : (u : Zphi) * ((u⁻¹ : Zphiˣ) : Zphi) = 1 := u.mul_inv
  have hv : (v : Zphi) * ((v⁻¹ : Zphiˣ) : Zphi) = 1 := v.mul_inv
  calc recMap u - recMap v - recSlope v v * ((u : Zphi) - v)
      = (recSlope u v - recSlope v v) * ((u : Zphi) - v) := by rw [recMap_sub]; ring
    _ = ((v⁻¹ : Zphiˣ) : Zphi)
          * (((v⁻¹ : Zphiˣ) : Zphi) * 1 - ((u⁻¹ : Zphiˣ) : Zphi) * 1)
          * ((u : Zphi) - v) := by unfold recSlope; ring
    _ = ((v⁻¹ : Zphiˣ) : Zphi)
          * (((v⁻¹ : Zphiˣ) : Zphi) * ((u : Zphi) * ((u⁻¹ : Zphiˣ) : Zphi))
            - ((u⁻¹ : Zphiˣ) : Zphi) * ((v : Zphi) * ((v⁻¹ : Zphiˣ) : Zphi)))
          * ((u : Zphi) - v) := by rw [hu, hv]
    _ = ((v⁻¹ : Zphiˣ) : Zphi) * ((v⁻¹ : Zphiˣ) : Zphi) * ((u⁻¹ : Zphiˣ) : Zphi)
          * (((u : Zphi) - v) * ((u : Zphi) - v)) := by ring

/-- **Definition 5.7's tangent slope at the fixed point** (the book's "derivative";
    the analytic derivative is not formalised). The slope of `f` on the
    diagonal at `φ` is `-φ⁻² = φ - 2`, an element of `ℤ[φ]` with integer
    coefficients `(-2, 1)`. It is a tangent slope (uniqueness not stated) of `f`
    at `φ` in the sense `recMap_tangent` proves (`f(u) - f(φ) - s(φ, φ)(u - φ)`
    is `φ⁻²u⁻¹(u - φ)²`); the analytic limit over the reals is not
    formalised. -/
theorem recSlope_phi : recSlope phiUnit phiUnit = -phiNegPow 2 ∧
    recSlope phiUnit phiUnit = phi - 2 := by
  constructor <;> decide

/-- **The tangent at the fixed point**, `recMap_tangent` at `v = φ`:
    `f(u) - φ - (φ - 2)(u - φ) = φ⁻²u⁻¹(u - φ)²` for every unit `u`. -/
theorem recMap_tangent_phi (u : Zphiˣ) :
    recMap u - phi - (phi - 2) * ((u : Zphi) - phi)
      = phiNegPow 2 * ((u⁻¹ : Zphiˣ) : Zphi) * (((u : Zphi) - phi) * ((u : Zphi) - phi)) := by
  have h := recMap_tangent u phiUnit
  rw [recMap_phi, recSlope_phi.2, phiUnit_val, phiUnit_inv_val] at h
  rw [h, show phiNegPow 2 = phiInv * phiInv by decide]

end Zphi

end RatioSpace
