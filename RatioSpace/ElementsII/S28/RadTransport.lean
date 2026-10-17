/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S28.Transport
import RatioSpace.ElementsII.S26.Mirror
import RatioSpace.ElementsII.S10.Causal
import RatioSpace.ElementsII.S02.Temporal
import RatioSpace.ElementsII.S24.Lifecycle
/-!
  Elements II §28 — Phase transport, route correction, and carried memory (all 12 items).

  **Why a second Rademacher definition lives here.** `Transport.lean`'s `dedekindSumInt`
  sums over `Finset.range`, and `Finset.range` itself depends on `Classical.choice`. So every
  theorem whose *statement* names `dedekindSumInt`, `phiRad` or `psiRad` reports choice,
  including Transport.lean's own `phiRad_neg_invariant`. This file therefore works with
  `phiRadC`/`psiRadC`: the same formula (`phiRad`'s body with `dedekindSumInt` replaced by
  `dsum`, the identical summand by structural recursion). No theorem here states an equality
  with Transport's `phiRad`/`psiRad`, since any such statement would print choice. The
  equality `phiRad Q = phiRadC Q` holds (`Finset.sum_range_succ` induction) and is left
  unstated for exactly that reason. `routeCorrection` is Transport's own and is clean.

  **Imported results are hypotheses.** Proposition 28.3's cocycle and conjugacy invariance are
  `RadCocycle` and `RadConj` (the `Closure12` form; unlike `Closure12`, which has a
    `Nonempty` instance, these have no instance). Central invariance of `Φ` and `Ψ` is
  derived. Exact instances of both laws are proved by `decide` as consistency witnesses.

  Conventions: `true = R`, `false = L`; the winding `b(v) = #R − #L` is Elements I/II's `bal`;
  `ε_s = eps s = bal [s] = sigma s` (Prop 10.9's step); `A s` is Definition 10.5's sibling relation.
-/
set_option linter.style.longLine false

namespace RatioSpace.Two
namespace RadTransport
open Mat2 Word

def sumTo (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_congr {f g : ℕ → ℤ} : ∀ n, (∀ i, i < n → f i = g i) → sumTo f n = sumTo g n
  | 0, _ => rfl
  | n + 1, h => by
    change sumTo f n + f n = sumTo g n + g n
    rw [sumTo_congr n (fun i hi => h i (by omega)), h n (by omega)]

theorem sumTo_shift (f : ℕ → ℤ) : ∀ n, sumTo f (n + 1) = f 0 + sumTo (fun i => f (i + 1)) n
  | 0 => by change 0 + f 0 = f 0 + 0; omega
  | n + 1 => by
    change sumTo f (n + 1) + f (n + 1) = f 0 + (sumTo (fun i => f (i + 1)) n + f (n + 1))
    rw [sumTo_shift f n]; omega

theorem sumTo_reflect (f : ℕ → ℤ) : ∀ n, sumTo f n = sumTo (fun i => f (n - 1 - i)) n
  | 0 => rfl
  | n + 1 => by
    rw [sumTo_shift (fun i => f (n + 1 - 1 - i)) n]
    have h1 : sumTo (fun i => f (n + 1 - 1 - (i + 1))) n = sumTo (fun i => f (n - 1 - i)) n :=
      sumTo_congr n (fun i _ => by
        show f (n + 1 - 1 - (i + 1)) = f (n - 1 - i)
        rw [show n + 1 - 1 - (i + 1) = n - 1 - i by omega])
    change sumTo f n + f n = f (n + 1 - 1 - 0) + sumTo (fun i => f (n + 1 - 1 - (i + 1))) n
    rw [h1, ← sumTo_reflect f n, show n + 1 - 1 - 0 = n by omega]
    omega

theorem sumTo_neg (f : ℕ → ℤ) : ∀ n, sumTo (fun i => - f i) n = - sumTo f n
  | 0 => rfl
  | n + 1 => by
    change sumTo (fun i => - f i) n + - f n = -(sumTo f n + f n)
    rw [sumTo_neg f n]; omega

def dTerm (a : ℤ) (k : ℕ) (i : ℕ) : ℤ :=
  (2 * ((i : ℤ) + 1) - k) * (2 * ((a * ((i : ℤ) + 1)) % (k : ℤ)) - k)

def dsum (a : ℤ) (k : ℕ) : ℤ := if k = 0 then 0 else sumTo (dTerm a k) (k - 1)

theorem dTerm_reflect (a : ℤ) (k i : ℕ) (hi : i < k - 1) :
    dTerm (-a) k (k - 1 - 1 - i) = - dTerm a k i := by
  unfold dTerm
  have hc : ((k - 1 - 1 - i : ℕ) : ℤ) + 1 = (k : ℤ) - ((i : ℤ) + 1) := by omega
  rw [hc]
  have hmod : (-a * ((k : ℤ) - ((i : ℤ) + 1))) % (k : ℤ) = (a * ((i : ℤ) + 1)) % (k : ℤ) := by
    rw [show -a * ((k : ℤ) - ((i : ℤ) + 1)) = a * ((i : ℤ) + 1) + (-a) * (k : ℤ) by ring,
      Int.add_mul_emod_self_right]
  rw [hmod]; ring

theorem dsum_neg (a : ℤ) (k : ℕ) : dsum (-a) k = - dsum a k := by
  unfold dsum
  split
  · rfl
  · rw [sumTo_reflect (dTerm (-a) k), ← sumTo_neg]
    exact sumTo_congr _ (fun i hi => dTerm_reflect a k i hi)

def phiRadC (Q : Mat2) : ℤ :=
  if Q.c = 0 then
    if Q.d ≠ 0 then Q.b / Q.d else 0
  else
    let k := Q.c.natAbs
    let sgnC : ℤ := if Q.c > 0 then 1 else -1
    sgnC * ((k : ℤ) * (Q.a + Q.d) - 3 * dsum Q.a k) / ((k : ℤ) * k)

def psiRadC (Q : Mat2) : ℤ := phiRadC Q - 3 * routeCorrection Q

/-! ## Definition 28.2: the value is an integer (determinant one)

`k² ∣ k·(a+d) − 3·dsum a k` whenever `a·d ≡ 1 (mod k)`. Multiplication by `a` permutes the
residues `1..k−1` (inverse: multiplication by `d`), so `Σ r = Σ x` and `Σ r² = Σ x²` for
`r = a·x mod k`; writing `r = a·x − k·q` and clearing the two closed sums gives the divisibility. -/

theorem sumTo_update (F F' : ℕ → ℤ) (j : ℕ) : ∀ n, j < n → (∀ i, i < n → i ≠ j → F i = F' i) →
    sumTo F n + F' j = sumTo F' n + F j
  | 0, hj, _ => absurd hj (Nat.not_lt_zero _)
  | n + 1, hj, h => by
    change sumTo F n + F n + F' j = sumTo F' n + F' n + F j
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [h n (by omega) (by omega)]
      have := sumTo_update F F' j n hj (fun i hi hij => h i (by omega) hij)
      omega
    · subst hj
      rw [sumTo_congr j (fun i hi => h i (by omega) (by omega))]
      omega

theorem sumTo_perm (f : ℕ → ℤ) : ∀ (n : ℕ) (g h : ℕ → ℕ), (∀ i, i < n → g i < n) →
    (∀ i, i < n → h i < n) → (∀ i, i < n → h (g i) = i) → (∀ i, i < n → g (h i) = i) →
    sumTo (fun i => f (g i)) n = sumTo f n
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, g, h, hg, hh, hhg, hgh => by
    change sumTo (fun i => f (g i)) n + f (g n) = sumTo f n + f n
    let j := h n
    have hj : j < n + 1 := hh n (by omega)
    have hgj : g j = n := hgh n (by omega)
    let g' : ℕ → ℕ := fun i => if i = j then g n else g i
    let h' : ℕ → ℕ := fun y => if y = g n then j else h y
    have ih := sumTo_perm f n g' h'
      (fun i hi => by
        change (if i = j then g n else g i) < n
        split
        · rename_i hij
          have := hg n (by omega)
          have : g n ≠ n := fun e => by
            have := hhg n (by omega); rw [e] at this; omega
          omega
        · rename_i hij
          have := hg i (by omega)
          have : g i ≠ n := fun e => by
            have := hhg i (by omega); rw [e] at this; exact hij this.symm
          omega)
      (fun y hy => by
        change (if y = g n then j else h y) < n
        split
        · rename_i hyg
          have : j ≠ n := fun e => by
            have := hgj; rw [e] at this; omega
          omega
        · rename_i hyg
          have := hh y (by omega)
          have : h y ≠ n := fun e => by
            have := hgh y (by omega); rw [e] at this; exact hyg this.symm
          omega)
      (fun i hi => by
        change (if (if i = j then g n else g i) = g n then j else h (if i = j then g n else g i)) = i
        by_cases hij : i = j
        · rw [if_pos hij, if_pos rfl, hij]
        · rw [if_neg hij]
          have : g i ≠ g n := fun e => by
            have h1 := hhg i (by omega); have h2 := hhg n (by omega); rw [e] at h1; omega
          rw [if_neg this, hhg i (by omega)])
      (fun y hy => by
        change (if (if y = g n then j else h y) = j then g n else g (if y = g n then j else h y)) = y
        by_cases hyg : y = g n
        · rw [if_pos hyg, if_pos rfl, hyg]
        · rw [if_neg hyg]
          have : h y ≠ j := fun e => by
            have h1 := hgh y (by omega); rw [e, hgj] at h1; omega
          rw [if_neg this, hgh y (by omega)])
    rw [← ih]
    by_cases hjn : j = n
    · have : g n = n := by have h0 := hgj; rw [hjn] at h0; exact h0
      rw [this]
      congr 1
      exact sumTo_congr n (fun i hi => by
        change f (g i) = f (if i = j then g n else g i)
        rw [if_neg (by omega)])
    · have := sumTo_update (fun i => f (g i)) (fun i => f (g' i)) j n (by omega)
        (fun i hi hij => by change f (g i) = f (if i = j then g n else g i); rw [if_neg hij])
      have e1 : g' j = g n := if_pos rfl
      rw [e1, hgj] at this
      omega

theorem sumTo_lin (f g h : ℕ → ℤ) (c1 c2 c3 c4 : ℤ) : ∀ n,
    sumTo (fun i => c1 * f i + c2 * g i + c3 * h i + c4) n =
      c1 * sumTo f n + c2 * sumTo g n + c3 * sumTo h n + c4 * n
  | 0 => by simp [sumTo]
  | n + 1 => by
    simp only [sumTo]; rw [sumTo_lin f g h c1 c2 c3 c4 n]; push_cast; ring

theorem sumTo_id : ∀ n, 2 * sumTo (fun i => (i : ℤ) + 1) n = (n : ℤ) * (n + 1)
  | 0 => by simp [sumTo]
  | n + 1 => by
    simp only [sumTo]; rw [mul_add, sumTo_id n]; push_cast; ring

theorem sumTo_sq : ∀ n, 6 * sumTo (fun i => ((i : ℤ) + 1) * ((i : ℤ) + 1)) n =
    (n : ℤ) * (n + 1) * (2 * n + 1)
  | 0 => by simp [sumTo]
  | n + 1 => by
    simp only [sumTo]; rw [mul_add, sumTo_sq n]; push_cast; ring

/-- The residue `a·x mod k` is never `0` for `1 ≤ x < k` when `a` has an inverse mod `k`. -/
theorem res_pos (a d e : ℤ) (k : ℕ) (had : a * d = 1 + k * e) (x : ℤ) (hx0 : 0 < x)
    (hxk : x < k) : 0 < (a * x) % (k : ℤ) := by
  have hk : (0 : ℤ) < k := by omega
  have h0 := Int.emod_nonneg (a * x) (by omega : (k : ℤ) ≠ 0)
  by_cases h : (a * x) % (k : ℤ) = 0
  · exfalso
    have hd : (k : ℤ) ∣ a * x := Int.dvd_of_emod_eq_zero h
    have hd2 : (k : ℤ) ∣ d * (a * x) - k * (e * x) := dvd_sub (dvd_mul_of_dvd_right hd d) (dvd_mul_right _ _)
    have : d * (a * x) - k * (e * x) = x := by
      rw [show d * (a * x) = (a * d) * x by ring, had]; ring
    rw [this] at hd2
    have := Int.le_of_dvd hx0 hd2
    omega
  · omega

theorem res_inv (a d e : ℤ) (k : ℕ) (had : a * d = 1 + k * e) (x : ℤ) (hx0 : 0 < x)
    (hxk : x < k) : (d * ((a * x) % (k : ℤ))) % (k : ℤ) = x := by
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod,
    show d * (a * x) = x + k * (e * x) by rw [show d * (a * x) = (a * d) * x by ring, had]; ring,
    Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by omega) hxk

/-- Multiplication by a unit permutes the nonzero residues mod `k`. -/
theorem sumTo_res_perm (a d e : ℤ) (k : ℕ) (had : a * d = 1 + k * e) (f : ℤ → ℤ) :
    sumTo (fun i => f ((a * ((i : ℤ) + 1)) % (k : ℤ))) (k - 1) =
      sumTo (fun i => f ((i : ℤ) + 1)) (k - 1) := by
  have hda : d * a = 1 + k * e := by rw [mul_comm]; exact had
  let g : ℕ → ℕ := fun i => ((a * ((i : ℤ) + 1)) % (k : ℤ)).toNat - 1
  let h : ℕ → ℕ := fun i => ((d * ((i : ℤ) + 1)) % (k : ℤ)).toNat - 1
  have hgv : ∀ i, i < k - 1 → ((g i : ℕ) : ℤ) + 1 = (a * ((i : ℤ) + 1)) % (k : ℤ) := fun i hi => by
    have := res_pos a d e k had ((i : ℤ) + 1) (by omega) (by omega)
    change (((a * ((i : ℤ) + 1)) % (k : ℤ)).toNat - 1 : ℕ) + (1 : ℤ) = _
    omega
  have hhv : ∀ i, i < k - 1 → ((h i : ℕ) : ℤ) + 1 = (d * ((i : ℤ) + 1)) % (k : ℤ) := fun i hi => by
    have := res_pos d a e k hda ((i : ℤ) + 1) (by omega) (by omega)
    change (((d * ((i : ℤ) + 1)) % (k : ℤ)).toNat - 1 : ℕ) + (1 : ℤ) = _
    omega
  have hgl : ∀ i, i < k - 1 → g i < k - 1 := fun i hi => by
    have h1 := hgv i hi
    have := Int.emod_lt_of_pos (a * ((i : ℤ) + 1)) (by omega : (0 : ℤ) < k)
    omega
  have hhl : ∀ i, i < k - 1 → h i < k - 1 := fun i hi => by
    have h1 := hhv i hi
    have := Int.emod_lt_of_pos (d * ((i : ℤ) + 1)) (by omega : (0 : ℤ) < k)
    omega
  rw [← sumTo_perm (fun y => f ((y : ℤ) + 1)) (k - 1) g h hgl hhl
    (fun i hi => by
      have h1 := hhv (g i) (hgl i hi)
      rw [hgv i hi, res_inv a d e k had _ (by omega) (by omega)] at h1
      omega)
    (fun i hi => by
      have h1 := hgv (h i) (hhl i hi)
      rw [hhv i hi, res_inv d a e k hda _ (by omega) (by omega)] at h1
      omega)]
  exact sumTo_congr _ (fun i hi => by show _ = f (((g i : ℕ) : ℤ) + 1); rw [hgv i hi])

/-- **Definition 28.2, "this value is an integer".** If `a·d ≡ 1 (mod k)`, then
    `k² ∣ k·(a+d) − 3·dsum a k`. -/
theorem dsum_dvd (a d e : ℤ) (k : ℕ) (hk : 0 < k) (had : a * d = 1 + k * e) :
    ((k : ℤ) * k) ∣ (k : ℤ) * (a + d) - 3 * dsum a k := by
  let n := k - 1
  have hn : (n : ℤ) = k - 1 := by omega
  let x : ℕ → ℤ := fun i => (i : ℤ) + 1
  let r : ℕ → ℤ := fun i => (a * x i) % (k : ℤ)
  let q : ℕ → ℤ := fun i => (a * x i) / (k : ℤ)
  have hrq : ∀ i, r i = a * x i - k * q i := fun i => Int.emod_def _ _
  let X := sumTo x n
  let X2 := sumTo (fun i => x i * x i) n
  let R := sumTo r n
  let R2 := sumTo (fun i => r i * r i) n
  let T := sumTo (fun i => x i * r i) n
  let U := sumTo (fun i => x i * q i) n
  let W := sumTo (fun i => q i * q i) n
  have hd : dsum a k = 4 * T + (-2 * k) * X + (-2 * k) * R + (k : ℤ) * k * n := by
    unfold dsum; rw [if_neg (by omega)]
    rw [← sumTo_lin]
    exact sumTo_congr _ (fun i _ => by unfold dTerm; ring)
  have h1 : R = X := sumTo_res_perm a d e k had id
  have h2 : 2 * X = (n : ℤ) * (n + 1) := sumTo_id n
  have h3 : 6 * X2 = (n : ℤ) * (n + 1) * (2 * n + 1) := sumTo_sq n
  have h4 : R2 = X2 := sumTo_res_perm a d e k had (fun y => y * y)
  have h5 : T = a * X2 + (-k) * U + 0 * X + 0 * (n : ℤ) := by
    rw [← sumTo_lin]
    exact sumTo_congr _ (fun i _ => by show x i * r i = _; rw [hrq]; ring)
  have h6 : R2 = (a * a) * X2 + (-2 * a * k) * U + ((k : ℤ) * k) * W + 0 * (n : ℤ) := by
    rw [← sumTo_lin]
    exact sumTo_congr _ (fun i _ => by show r i * r i = _; rw [hrq]; ring)
  rw [hn] at h2 h3 hd
  have hd0 : dsum a k - (4 * T + (-2 * k) * X + (-2 * k) * R + (k : ℤ) * k * (k - 1)) = 0 := by
    rw [hd]; ring
  have h10 : R - X = 0 := by rw [h1]; ring
  have h20 : 2 * X - ((k : ℤ) - 1) * ((k - 1) + 1) = 0 := by rw [h2]; ring
  have h30 : 6 * X2 - ((k : ℤ) - 1) * ((k - 1) + 1) * (2 * (k - 1) + 1) = 0 := by rw [h3]; ring
  have h40 : R2 - X2 = 0 := by rw [h4]; ring
  have h50 : T - (a * X2 + (-k) * U + 0 * X + 0 * ((k : ℤ) - 1)) = 0 := by rw [h5]; ring
  have h60 : R2 - ((a * a) * X2 + (-2 * a * k) * U + ((k : ℤ) * k) * W + 0 * ((k : ℤ) - 1)) = 0 := by
    rw [h6]; ring
  have h70 : a * d - (1 + k * e) = 0 := by rw [had]; ring
  refine ⟨-(2 * k - 3) * (a + d) + a * e * ((k - 1) * (2 * k - 1)) - 12 * e * U + 6 * d * W
    + 3 * (k - 1), ?_⟩
  calc (k : ℤ) * (a + d) - 3 * dsum a k
      = (k : ℤ) * k * (-(2 * k - 3) * (a + d) + a * e * ((k - 1) * (2 * k - 1)) - 12 * e * U
          + 6 * d * W + 3 * (k - 1))
        + ((-3) * (dsum a k - (4 * T + (-2 * k) * X + (-2 * k) * R + (k : ℤ) * k * (k - 1)))
          - 12 * (T - (a * X2 + (-k) * U + 0 * X + 0 * ((k : ℤ) - 1))) + 6 * k * (R - X)
          + 6 * k * (2 * X - ((k : ℤ) - 1) * ((k - 1) + 1))
          + (-2 * a + d * (a * a - 1)) * (6 * X2 - ((k : ℤ) - 1) * ((k - 1) + 1) * (2 * (k - 1) + 1))
          - 6 * d * (R2 - X2)
          + 6 * d * (R2 - ((a * a) * X2 + (-2 * a * k) * U + ((k : ℤ) * k) * W + 0 * ((k : ℤ) - 1)))
          + (-12 * k * U + a * k * ((k - 1) * (2 * k - 1))) * (a * d - (1 + k * e))) := by ring
    _ = (k : ℤ) * k * (-(2 * k - 3) * (a + d) + a * e * ((k - 1) * (2 * k - 1)) - 12 * e * U
          + 6 * d * W + 3 * (k - 1)) := by
        rw [hd0, h10, h20, h30, h40, h50, h60, h70]; ring

/-- **Definition 28.2, "this value is an integer"**, for `Q` of determinant `1` with `c ≠ 0`,
    `k = |c|`: `k²` divides the numerator `k·(a+d) − 3·dsum a k`, so `phiRadC`'s `Int.ediv`
    is exact: `phiRadC Q · k² = sgn(c)·(k·(a+d) − 3·dsum a k)`. -/
theorem phiRadC_integer (Q : Mat2) (hdet : Q.det = 1) (hc : Q.c ≠ 0) :
    ((Q.c.natAbs : ℤ) * Q.c.natAbs) ∣ (Q.c.natAbs : ℤ) * (Q.a + Q.d) - 3 * dsum Q.a Q.c.natAbs ∧
    phiRadC Q * ((Q.c.natAbs : ℤ) * Q.c.natAbs) =
      (if Q.c > 0 then 1 else -1) * ((Q.c.natAbs : ℤ) * (Q.a + Q.d) - 3 * dsum Q.a Q.c.natAbs) := by
  have hdet' : Q.a * Q.d - Q.b * Q.c = 1 := hdet
  have hdvd : ((Q.c.natAbs : ℤ) * Q.c.natAbs) ∣
      (Q.c.natAbs : ℤ) * (Q.a + Q.d) - 3 * dsum Q.a Q.c.natAbs := by
    rcases Int.natAbs_eq Q.c with h | h
    · exact dsum_dvd Q.a Q.d Q.b _ (by omega) (by rw [← h, ← hdet']; ring)
    · exact dsum_dvd Q.a Q.d (-Q.b) _ (by omega) (by
        rw [show ((Q.c.natAbs : ℕ) : ℤ) = - Q.c by omega, ← hdet']; ring)
  refine ⟨hdvd, ?_⟩
  unfold phiRadC
  rw [if_neg hc]
  change (if Q.c > 0 then 1 else -1) * ((Q.c.natAbs : ℤ) * (Q.a + Q.d) - 3 * dsum Q.a Q.c.natAbs) /
      ((Q.c.natAbs : ℤ) * Q.c.natAbs) * ((Q.c.natAbs : ℤ) * Q.c.natAbs) = _
  rw [Int.mul_ediv_assoc _ hdvd, mul_assoc, Int.ediv_mul_cancel hdvd]

/-! ## Definition 28.2: `dsum` is the Dedekind sum, scaled by `4k²`

The book's Dedekind sum is `s_D(a,k) = Σ_{r=1}^{k−1} ((r/k))((a·r/k))` with the sawtooth
`((x)) = x − ⌊x⌋ − 1/2` for `x ∉ ℤ` and `((x)) = 0` for `x ∈ ℤ`. Lean's `ℚ` cannot carry this
choice-free: core's own `Rat.add_comm`, `Rat.mul_comm` and `Rat.floor_add_intCast` already print
`Classical.choice` (toolchain v4.33.0), so any `ℚ`-valued statement would. The sawtooth is
therefore kept as an exact fraction with denominator `2k`: for `x = p/k` (`k > 0`),
`2k·((p/k)) = sawScaled p k`, where `p / k` (`Int.ediv`) is `⌊p/k⌋` (`ediv_is_floor`), and
`4k²·s_D(a,k) = sDScaled a k`. -/

/-- The sawtooth at `x = p/k`, times `2k`: `0` if `k ∣ p`, otherwise
    `2·(p − k·⌊p/k⌋) − k = 2k·(p/k − ⌊p/k⌋ − 1/2)`. -/
def sawScaled (p : ℤ) (k : ℕ) : ℤ := if p % (k : ℤ) = 0 then 0 else 2 * (p - k * (p / k)) - k

/-- `Σ_{r=1}^{k−1} (2k·((r/k)))·(2k·((a·r/k)))`, i.e. `4k²·s_D(a,k)`; index `i = r − 1`. -/
def sDScaled (a : ℤ) (k : ℕ) : ℤ :=
  sumTo (fun i => sawScaled ((i : ℤ) + 1) k * sawScaled (a * ((i : ℤ) + 1)) k) (k - 1)

/-- For `k > 0`, `Int.ediv` is the floor: `k·(p/k) ≤ p < k·(p/k) + k`. -/
theorem ediv_is_floor (p : ℤ) (k : ℕ) (hk : 0 < k) :
    (k : ℤ) * (p / k) ≤ p ∧ p < (k : ℤ) * (p / k) + k := by
  have h0 := Int.emod_nonneg p (by omega : (k : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos p (by omega : (0 : ℤ) < k)
  have h2 := Int.emod_def p (k : ℤ)
  constructor <;> omega

/-- **Definition 28.2, `dsum` is the Dedekind sum.** For every `a` and `k`,
    `dsum a k = sDScaled a k`, i.e. `dsum a k = 4k²·s_D(a,k)` with `s_D` taken with the
    sawtooth (`((x)) = 0` at integers). No coprimality is needed: where `k ∣ a·r` the sawtooth
    factor is `0` while `dTerm` is `−k·(2r − k)`, and these terms cancel in pairs under
    `r ↦ k − r`. -/
theorem dsum_eq_sD (a : ℤ) (k : ℕ) : dsum a k = sDScaled a k := by
  unfold dsum sDScaled
  by_cases hk : k = 0
  · subst hk; rfl
  rw [if_neg hk]
  let h : ℕ → ℤ := fun i =>
    if (a * ((i : ℤ) + 1)) % (k : ℤ) = 0 then -(k : ℤ) * (2 * ((i : ℤ) + 1) - k) else 0
  have hterm : ∀ i, i < k - 1 → dTerm a k i =
      1 * (sawScaled ((i : ℤ) + 1) k * sawScaled (a * ((i : ℤ) + 1)) k) + 1 * h i
        + 0 * h i + 0 := by
    intro i hi
    have h1 : sawScaled ((i : ℤ) + 1) k = 2 * ((i : ℤ) + 1) - k := by
      have hm : ((i : ℤ) + 1) % (k : ℤ) = (i : ℤ) + 1 := Int.emod_eq_of_lt (by omega) (by omega)
      unfold sawScaled
      rw [if_neg (by omega), ← Int.emod_def, hm]
    rw [h1]
    unfold dTerm sawScaled
    change _ = _ + 1 * (if (a * ((i : ℤ) + 1)) % (k : ℤ) = 0 then
      -(k : ℤ) * (2 * ((i : ℤ) + 1) - k) else 0) + _ + _
    by_cases hz : (a * ((i : ℤ) + 1)) % (k : ℤ) = 0
    · rw [if_pos hz, if_pos hz, hz]; ring
    · rw [if_neg hz, if_neg hz, ← Int.emod_def]; ring
  have hz : sumTo h (k - 1) = 0 := by
    have r := sumTo_reflect h (k - 1)
    have hc : sumTo (fun i => h (k - 1 - 1 - i)) (k - 1) = sumTo (fun i => - h i) (k - 1) :=
      sumTo_congr _ (fun i hi => by
        have hc : ((k - 1 - 1 - i : ℕ) : ℤ) + 1 = (k : ℤ) - ((i : ℤ) + 1) := by omega
        have hmod : (a * ((k : ℤ) - ((i : ℤ) + 1))) % (k : ℤ) = 0 ↔
            (a * ((i : ℤ) + 1)) % (k : ℤ) = 0 := by
          rw [show a * ((k : ℤ) - ((i : ℤ) + 1)) = -(a * ((i : ℤ) + 1)) + a * (k : ℤ) by ring,
            Int.add_mul_emod_self_right, ← Int.dvd_iff_emod_eq_zero, ← Int.dvd_iff_emod_eq_zero,
            Int.dvd_neg]
        change (if (a * (((k - 1 - 1 - i : ℕ) : ℤ) + 1)) % (k : ℤ) = 0 then
          -(k : ℤ) * (2 * (((k - 1 - 1 - i : ℕ) : ℤ) + 1) - k) else 0) =
          -(if (a * ((i : ℤ) + 1)) % (k : ℤ) = 0 then -(k : ℤ) * (2 * ((i : ℤ) + 1) - k) else 0)
        rw [hc]
        by_cases hd : (a * ((i : ℤ) + 1)) % (k : ℤ) = 0
        · rw [if_pos (hmod.mpr hd), if_pos hd]; ring
        · rw [if_neg (fun h' => hd (hmod.mp h')), if_neg hd]; ring)
    rw [hc, sumTo_neg] at r
    omega
  rw [sumTo_congr _ hterm, sumTo_lin, hz]
  ring

/-- Instances: `s_D(1,3) = 1/18` and `s_D(2,5) = 0`, scaled by `4k²` (`36·1/18 = 2`). -/
example : sDScaled 1 3 = 2 ∧ dsum 1 3 = 2 ∧ sDScaled 2 5 = 0 := by decide

def sgnInt (n : ℤ) : ℤ := if 0 < n then 1 else if n < 0 then -1 else 0

theorem sgnInt_zero : sgnInt 0 = 0 := rfl
theorem sgnInt_of_pos {n : ℤ} (h : 0 < n) : sgnInt n = 1 := by unfold sgnInt; rw [if_pos h]
theorem sgnInt_of_neg {n : ℤ} (h : n < 0) : sgnInt n = -1 := by
  unfold sgnInt; rw [if_neg (fun h' => by omega), if_pos h]

theorem routeCorrection_eq_sgn (Q : Mat2) : routeCorrection Q = sgnInt (Q.c * (Q.a + Q.d)) := rfl

theorem sgnInt_mul_of_pos_right {x y : ℤ} (hy : 0 < y) : sgnInt (x * y) = sgnInt x := by
  rcases Int.lt_trichotomy x 0 with h | h | h
  · rw [sgnInt_of_neg h, sgnInt_of_neg (Int.mul_neg_of_neg_of_pos h hy)]
  · rw [h, Int.zero_mul]
  · rw [sgnInt_of_pos h, sgnInt_of_pos (Int.mul_pos h hy)]

theorem sgnInt_mul_of_neg_right {x y : ℤ} (hy : y < 0) : sgnInt (x * y) = - sgnInt x := by
  rcases Int.lt_trichotomy x 0 with h | h | h
  · rw [sgnInt_of_neg h, sgnInt_of_pos (Int.mul_pos_of_neg_of_neg h hy)]; rfl
  · rw [h, Int.zero_mul]; rfl
  · rw [sgnInt_of_pos h, sgnInt_of_neg (Int.mul_neg_of_pos_of_neg h hy)]

theorem sgnInt_mul_of_pos_left {x y : ℤ} (hx : 0 < x) : sgnInt (x * y) = sgnInt y := by
  rw [Int.mul_comm]; exact sgnInt_mul_of_pos_right hx

theorem sgnInt_mul_of_neg_left {x y : ℤ} (hx : x < 0) : sgnInt (x * y) = - sgnInt y := by
  rw [Int.mul_comm]; exact sgnInt_mul_of_neg_right hx

/-! ## Definition 28.1 -/

def eps (s : Bool) : ℤ := if s then 1 else -1

theorem eps_eq_bal (s : Bool) : eps s = bal [s] := by cases s <;> decide

theorem eps_eq_sigma (s : Bool) : eps s = sigma s := eps_eq_bal s

def Qs (s : Bool) (v : Word) : Mat2 := inv2 (G v) * A s

theorem Qs_nil (s : Bool) : Qs s [] = A s := by cases s <;> decide

theorem det_A (s : Bool) : (A s).det = 1 := by cases s <;> decide

theorem det_inv2' (M : Mat2) : (inv2 M).det = M.det := by
  cases M with
  | mk a b c d => change d * a - -b * -c = a * d - b * c; ring

theorem det_Qs (s : Bool) (v : Word) : (Qs s v).det = 1 := by
  unfold Qs; rw [det_mul, det_inv2', det_G, det_A]; rfl

theorem Qs_snoc (s : Bool) (v : Word) (b : Bool) :
    Qs s (v ++ [b]) = inv2 (gen b) * Qs s v := by
  unfold Qs; rw [G_snoc, inv2_mul, mul_assoc']

/-! ## 28.3 -/

structure RadCocycle : Prop where
  cocycle : ∀ X Y : Mat2, X.det = 1 → Y.det = 1 →
    phiRadC (X * Y) = phiRadC X + phiRadC Y - 3 * sgnInt (X.c * Y.c * (X * Y).c)

structure RadConj : Prop where
  conj : ∀ Z Q : Mat2, Z.det = 1 → Q.det = 1 → psiRadC (inv2 Z * Q * Z) = psiRadC Q

theorem d_unit {a d : ℤ} (h : a * d = 1) : d = 1 ∨ d = -1 := by
  have h1 : a.natAbs * d.natAbs = 1 := by rw [← Int.natAbs_mul, h]; rfl
  have h2 : d.natAbs = 1 := Nat.eq_one_of_mul_eq_one_left h1
  rcases Int.natAbs_eq d with h3 | h3
  · left; rw [h3, h2]; rfl
  · right; rw [h3, h2]; rfl

theorem phiRadC_neg (Q : Mat2) (hdet : Q.det = 1) : phiRadC (-Q) = phiRadC Q := by
  unfold phiRadC
  rcases Int.lt_trichotomy Q.c 0 with hc | hc | hc
  · have hc' : Q.c ≠ 0 := fun h => by omega
    have hn : (-Q).c ≠ 0 := fun h => by simp only [neg_c] at h; omega
    rw [if_neg hc', if_neg hn]
    simp only [neg_a, neg_c, neg_d, Int.natAbs_neg, dsum_neg]
    rw [if_pos (show -Q.c > 0 by omega), if_neg (show ¬ Q.c > 0 by omega)]
    congr 1; ring
  · have had : Q.a * Q.d = 1 := by
      have : Q.a * Q.d - Q.b * Q.c = 1 := hdet
      rw [hc, Int.mul_zero, Int.sub_zero] at this; exact this
    have hn : (-Q).c = 0 := by simp only [neg_c, hc]; rfl
    rw [if_pos hc, if_pos hn]
    rcases d_unit had with hd | hd
    · simp only [neg_b, neg_d, hd]
      rw [if_pos (by decide : (-1:ℤ) ≠ 0), if_pos (by decide : (1:ℤ) ≠ 0), Int.ediv_neg,
        Int.ediv_one, Int.ediv_one, Int.neg_neg]
    · simp only [neg_b, neg_d, hd, Int.neg_neg]
      rw [if_pos (by decide : (1:ℤ) ≠ 0), if_pos (by decide : (-1:ℤ) ≠ 0), Int.ediv_neg,
        Int.ediv_one, Int.ediv_one]
  · have hc' : Q.c ≠ 0 := fun h => by omega
    have hn : (-Q).c ≠ 0 := fun h => by simp only [neg_c] at h; omega
    rw [if_neg hc', if_neg hn]
    simp only [neg_a, neg_c, neg_d, Int.natAbs_neg, dsum_neg]
    rw [if_neg (show ¬ -Q.c > 0 by omega), if_pos (show Q.c > 0 by omega)]
    congr 1; ring

theorem routeCorrection_neg' (Q : Mat2) : routeCorrection (-Q) = routeCorrection Q := by
  rw [routeCorrection_eq_sgn, routeCorrection_eq_sgn]
  simp only [neg_a, neg_c, neg_d]
  rw [show -Q.c * (-Q.a + -Q.d) = Q.c * (Q.a + Q.d) by ring]

theorem psiRadC_neg (Q : Mat2) (hdet : Q.det = 1) : psiRadC (-Q) = psiRadC Q := by
  unfold psiRadC; rw [phiRadC_neg Q hdet, routeCorrection_neg']

/-- **Proposition 28.3**, read on a retained relation: under the imported conjugacy law, `Ψ`
    of `Q_s(v)` is unchanged by any change of frame `Z ∈ SL(2,ℤ)`, and so is its decomposition. -/
theorem class_coordinate (HC : RadConj) (Z : Mat2) (hZ : Z.det = 1) (s : Bool) (v : Word) :
    psiRadC (inv2 Z * Qs s v * Z) = psiRadC (Qs s v) :=
  HC.conj Z (Qs s v) hZ (det_Qs s v)

/-! ## 28.4 -/

theorem G_a_pos : ∀ v : Word, 1 ≤ (G v).a
  | [] => by decide
  | false :: w => by rw [G_cons_false]; exact G_a_pos w
  | true :: w => by
    rw [G_cons_true]
    have h1 := G_a_pos w
    have h2 := (nonneg_G w).2.2.1
    change 1 ≤ (G w).a + (G w).c; omega

theorem G_d_pos : ∀ v : Word, 1 ≤ (G v).d
  | [] => by decide
  | true :: w => by rw [G_cons_true]; exact G_d_pos w
  | false :: w => by
    rw [G_cons_false]
    have h1 := G_d_pos w
    have h2 := (nonneg_G w).2.1
    change 1 ≤ (G w).b + (G w).d; omega

theorem Qs_true_explicit (v : Word) :
    Qs true v = ⟨-(G v).b, -((G v).b + (G v).d), (G v).a, (G v).a + (G v).c⟩ := by
  unfold Qs; rw [A_true_eq, mul_def]
  apply ext' <;> dsimp only [inv2] <;> ring

theorem Qs_false_explicit (v : Word) :
    Qs false v = ⟨(G v).b + (G v).d, (G v).d, -((G v).a + (G v).c), -(G v).c⟩ := by
  unfold Qs; rw [A_false_eq, mul_def]
  apply ext' <;> dsimp only [inv2] <;> ring

theorem Qs_true_c_pos (v : Word) : 0 < (Qs true v).c := by
  rw [Qs_true_explicit]; change 0 < (G v).a; have := G_a_pos v; omega

theorem Qs_false_c_neg (v : Word) : (Qs false v).c < 0 := by
  rw [Qs_false_explicit]; change -((G v).a + (G v).c) < 0
  have := G_a_pos v; have := (nonneg_G v).2.2.1; omega

theorem Linv_mul_c (M : Mat2) : (Linv * M).c = M.c - M.a := by
  change -1 * M.a + 1 * M.c = M.c - M.a; ring

theorem Linv_Qs_true_c_pos (v : Word) : 0 < (Linv * Qs true v).c := by
  rw [Linv_mul_c, Qs_true_explicit]; change 0 < (G v).a - -(G v).b
  have := G_a_pos v; have := (nonneg_G v).2.1; omega

theorem Linv_Qs_false_c_neg (v : Word) : (Linv * Qs false v).c < 0 := by
  rw [Linv_mul_c, Qs_false_explicit]; change -((G v).a + (G v).c) - ((G v).b + (G v).d) < 0
  have := G_a_pos v; obtain ⟨h1, h2, h3, h4⟩ := nonneg_G v; omega

theorem Qs_Linv_same_sign (s : Bool) (v : Word) :
    sgnInt (Linv * Qs s v).c = sgnInt (Qs s v).c ∧ sgnInt (Qs s v).c ≠ 0 := by
  cases s
  · rw [sgnInt_of_neg (Linv_Qs_false_c_neg v), sgnInt_of_neg (Qs_false_c_neg v)]; decide
  · rw [sgnInt_of_pos (Linv_Qs_true_c_pos v), sgnInt_of_pos (Qs_true_c_pos v)]; decide

theorem Linv_triple (s : Bool) (v : Word) :
    sgnInt (Linv.c * (Qs s v).c * (Linv * Qs s v).c) = -1 := by
  cases s
  · rw [sgnInt_mul_of_neg_right (Linv_Qs_false_c_neg v), sgnInt_mul_of_neg_right (Qs_false_c_neg v)]; decide
  · rw [sgnInt_mul_of_pos_right (Linv_Qs_true_c_pos v), sgnInt_mul_of_pos_right (Qs_true_c_pos v)]; decide

/-! ## 28.5 -/

theorem phiRadC_A (s : Bool) : phiRadC (A s) = eps s := by cases s <;> decide
theorem phiRadC_Rinv : phiRadC Rinv = -1 := by decide
theorem phiRadC_Linv : phiRadC Linv = -2 := by decide

theorem transport (H : RadCocycle) (s : Bool) (v : Word) :
    phiRadC (Qs s v) = eps s - bal v := by
  induction v using List.reverseRecOn with
  | nil => rw [Qs_nil, phiRadC_A, bal_nil]; omega
  | append_singleton v b ih =>
    have hdetY := det_Qs s v
    rw [Qs_snoc]
    cases b with
    | true =>
      have hb : bal (v ++ [true]) = bal v + 1 := by rw [bal_snoc]; rfl
      have hX : inv2 (gen true) = Rinv := by decide
      rw [hX, H.cocycle _ _ (by decide) hdetY, ih, phiRadC_Rinv, hb,
        show Rinv.c = 0 from rfl, Int.zero_mul, Int.zero_mul, sgnInt_zero]
      omega
    | false =>
      have hb : bal (v ++ [false]) = bal v - 1 := by rw [bal_snoc]; rfl
      have hX : inv2 (gen false) = Linv := by decide
      rw [hX, H.cocycle _ _ (by decide) hdetY, ih, phiRadC_Linv, hb, Linv_triple]
      omega

/-! ## 28.6 -/

theorem class_decomposition (H : RadCocycle) (s : Bool) (v : Word) :
    psiRadC (Qs s v) = eps s - bal v - 3 * routeCorrection (Qs s v) := by
  unfold psiRadC; rw [transport H]

theorem equal_hand_winding_equal_phi (H : RadCocycle) (s : Bool) {u v : Word}
    (h : bal u = bal v) : phiRadC (Qs s u) = phiRadC (Qs s v) := by
  rw [transport H, transport H, h]

theorem hand_winding_not_force_psi :
    len [true, true, true, false] = len [false, true, true, true] ∧
    bal [true, true, true, false] = bal [false, true, true, true] ∧
    psiRadC (Qs true [true, true, true, false]) ≠ psiRadC (Qs true [false, true, true, true]) := by
  decide

/-! ## 28.7 -/

theorem Qs_true_of_G {v : Word} {α β γ δ : ℤ} (h : G v = ⟨α, β, γ, δ⟩) :
    Qs true v = ⟨-β, -(β + δ), α, α + γ⟩ := by rw [Qs_true_explicit, h]

theorem Qs_false_of_G {v : Word} {α β γ δ : ℤ} (h : G v = ⟨α, β, γ, δ⟩) :
    Qs false v = ⟨β + δ, δ, -(α + γ), -γ⟩ := by rw [Qs_false_explicit, h]

theorem routeCorrection_mk_of_c_pos {a b c d : ℤ} (hc : 0 < c) :
    routeCorrection ⟨a, b, c, d⟩ = sgnInt (a + d) := sgnInt_mul_of_pos_left hc

theorem routeCorrection_mk_of_c_neg {a b c d : ℤ} (hc : c < 0) :
    routeCorrection ⟨a, b, c, d⟩ = - sgnInt (a + d) := sgnInt_mul_of_neg_left hc

theorem G_replicate_true : ∀ m : ℕ, G (List.replicate m true) = ⟨1, m, 0, 1⟩
  | 0 => rfl
  | m + 1 => by
    rw [List.replicate_succ, G_cons_true, G_replicate_true m]
    apply ext' <;> dsimp only <;> omega

theorem G_replicate_false : ∀ m : ℕ, G (List.replicate m false) = ⟨1, 0, m, 1⟩
  | 0 => rfl
  | m + 1 => by
    rw [List.replicate_succ, G_cons_false, G_replicate_false m]
    apply ext' <;> dsimp only <;> omega

theorem bal_replicate_true : ∀ m : ℕ, bal (List.replicate m true) = m
  | 0 => rfl
  | m + 1 => by rw [List.replicate_succ, bal_true, bal_replicate_true m]; omega

theorem bal_replicate_false : ∀ m : ℕ, bal (List.replicate m false) = -(m : ℤ)
  | 0 => rfl
  | m + 1 => by rw [List.replicate_succ, bal_false, bal_replicate_false m]; omega

/-- `v_m^{(+)} = R^m L`. -/
def vPlus (m : ℕ) : Word := List.replicate m true ++ [false]
/-- `v_m^{(-)} = L R^m`. -/
def vMinus (m : ℕ) : Word := false :: List.replicate m true
/-- `u_m^{(+)} = L^m R^3`. -/
def uPlus (m : ℕ) : Word := List.replicate m false ++ [true, true, true]
/-- `u_m^{(-)} = R L^m R^2`. -/
def uMinus (m : ℕ) : Word := true :: (List.replicate m false ++ [true, true])

theorem G_vPlus (m : ℕ) : G (vPlus m) = ⟨m + 1, m, 1, 1⟩ := by
  unfold vPlus; rw [G_snoc, G_replicate_true, gen_false, mul_def]
  apply ext' <;> dsimp only [L] <;> ring

theorem G_vMinus (m : ℕ) : G (vMinus m) = ⟨1, m, 1, m + 1⟩ := by
  unfold vMinus; rw [G_cons_false, G_replicate_true]
  apply ext' <;> dsimp only; ring

theorem G_uPlus (m : ℕ) : G (uPlus m) = ⟨1, 3, m, 3 * m + 1⟩ := by
  unfold uPlus; rw [G_append, G_replicate_false, mul_def, show G [true, true, true] = ⟨1, 3, 0, 1⟩ by decide]
  apply ext' <;> dsimp only <;> ring

theorem G_uMinus (m : ℕ) : G (uMinus m) = ⟨m + 1, 2 * m + 3, m, 2 * m + 1⟩ := by
  unfold uMinus; rw [G_cons_true, G_append, G_replicate_false, mul_def,
    show G [true, true] = ⟨1, 2, 0, 1⟩ by decide]
  apply ext' <;> dsimp only <;> ring

theorem len_vPlus (m : ℕ) : len (vPlus m) = m + 1 := by
  unfold vPlus; rw [len, List.length_append, List.length_replicate]; rfl
theorem len_vMinus (m : ℕ) : len (vMinus m) = m + 1 := by
  unfold vMinus; rw [len, List.length_cons, List.length_replicate]
theorem len_uPlus (m : ℕ) : len (uPlus m) = m + 3 := by
  unfold uPlus; rw [len, List.length_append, List.length_replicate]; rfl
theorem len_uMinus (m : ℕ) : len (uMinus m) = m + 3 := by
  unfold uMinus; rw [len, List.length_cons, List.length_append, List.length_replicate]; rfl

theorem bal_vPlus (m : ℕ) : bal (vPlus m) = (m : ℤ) - 1 := by
  unfold vPlus; rw [bal_append, bal_replicate_true]; rfl
theorem bal_vMinus (m : ℕ) : bal (vMinus m) = (m : ℤ) - 1 := by
  unfold vMinus; rw [bal_false, bal_replicate_true]; omega
theorem bal_uPlus (m : ℕ) : bal (uPlus m) = 3 - (m : ℤ) := by
  unfold uPlus; rw [bal_append, bal_replicate_false, show bal [true, true, true] = 3 by decide]; omega
theorem bal_uMinus (m : ℕ) : bal (uMinus m) = 3 - (m : ℤ) := by
  unfold uMinus; rw [bal_true, bal_append, bal_replicate_false, show bal [true, true] = 2 by decide]; omega

theorem sigma_vPlus (m : ℕ) : routeCorrection (Qs true (vPlus m)) = 1 := by
  rw [Qs_true_of_G (G_vPlus m), routeCorrection_mk_of_c_pos (by omega)]
  exact sgnInt_of_pos (by omega)
theorem sigma_vMinus (m : ℕ) (hm : 3 ≤ m) : routeCorrection (Qs true (vMinus m)) = -1 := by
  rw [Qs_true_of_G (G_vMinus m), routeCorrection_mk_of_c_pos (by omega)]
  exact sgnInt_of_neg (by omega)
theorem sigma_uPlus (m : ℕ) (hm : 3 ≤ m) : routeCorrection (Qs true (uPlus m)) = 1 := by
  rw [Qs_true_of_G (G_uPlus m), routeCorrection_mk_of_c_pos (by decide)]
  exact sgnInt_of_pos (by omega)
theorem sigma_uMinus (m : ℕ) : routeCorrection (Qs true (uMinus m)) = -1 := by
  rw [Qs_true_of_G (G_uMinus m), routeCorrection_mk_of_c_pos (by omega)]
  exact sgnInt_of_neg (by omega)

/-- **Theorem 28.7**, for every `m ≥ 3`. -/
theorem opposite_routes (H : RadCocycle) (m : ℕ) (hm : 3 ≤ m) :
    (len (vPlus m) = m + 1 ∧ len (vMinus m) = m + 1 ∧
      bal (vPlus m) = (m : ℤ) - 1 ∧ bal (vMinus m) = (m : ℤ) - 1 ∧
      routeCorrection (Qs true (vPlus m)) = 1 ∧ routeCorrection (Qs true (vMinus m)) = -1 ∧
      phiRadC (Qs true (vPlus m)) = 2 - m ∧ phiRadC (Qs true (vMinus m)) = 2 - m ∧
      psiRadC (Qs true (vPlus m)) = -(m : ℤ) - 1 ∧ psiRadC (Qs true (vMinus m)) = 5 - m) ∧
    (len (uPlus m) = m + 3 ∧ len (uMinus m) = m + 3 ∧
      bal (uPlus m) = 3 - (m : ℤ) ∧ bal (uMinus m) = 3 - (m : ℤ) ∧
      routeCorrection (Qs true (uPlus m)) = 1 ∧ routeCorrection (Qs true (uMinus m)) = -1 ∧
      phiRadC (Qs true (uPlus m)) = m - 2 ∧ phiRadC (Qs true (uMinus m)) = m - 2 ∧
      psiRadC (Qs true (uPlus m)) = (m : ℤ) - 5 ∧ psiRadC (Qs true (uMinus m)) = m + 1) := by
  have e1 : eps true = 1 := rfl
  refine ⟨⟨len_vPlus m, len_vMinus m, bal_vPlus m, bal_vMinus m, sigma_vPlus m, sigma_vMinus m hm,
    ?_, ?_, ?_, ?_⟩, ⟨len_uPlus m, len_uMinus m, bal_uPlus m, bal_uMinus m, sigma_uPlus m hm,
    sigma_uMinus m, ?_, ?_, ?_, ?_⟩⟩
  · rw [transport H, bal_vPlus, e1]; omega
  · rw [transport H, bal_vMinus, e1]; omega
  · unfold psiRadC; rw [transport H, bal_vPlus, sigma_vPlus, e1]; omega
  · unfold psiRadC; rw [transport H, bal_vMinus, sigma_vMinus m hm, e1]; omega
  · rw [transport H, bal_uPlus, e1]; omega
  · rw [transport H, bal_uMinus, e1]; omega
  · unfold psiRadC; rw [transport H, bal_uPlus, sigma_uPlus m hm, e1]; omega
  · unfold psiRadC; rw [transport H, bal_uMinus, sigma_uMinus, e1]; omega

/-- **Theorem 28.7**, the paragraph after the proof: each pair has equal causal
    continuation depth, and under synchronized one-continuation-per-stratum lifecycle
    reads it has equal archive age in the sense of Definition 24.1.

    The synchronized read is taken as stated here: both receiver trails enter at one
    common face-entry stratum `k`, and each continuation of a trail occupies one
    stratum, so a trail `w` is read at stratum `k + len w`. That read is at `n ≥ k`,
    the range where Definition 24.1 defines `a_arch` (first conjunct of each family),
    and the two archive ages `Lifecycle.aArch k (k + len w)` of a pair are equal, with
    value the common depth (`m + 1` and `m + 3`). This theorem does not build the
    extended ledger of Definition 24.1 or derive the synchronization; it states the
    book's conditional sentence under that reading. -/
theorem opposite_routes_equal_age (m k : ℕ) :
    (k ≤ k + len (vPlus m) ∧ k ≤ k + len (vMinus m) ∧
      Lifecycle.aArch k (k + len (vPlus m)) = Lifecycle.aArch k (k + len (vMinus m)) ∧
      Lifecycle.aArch k (k + len (vPlus m)) = m + 1) ∧
    (k ≤ k + len (uPlus m) ∧ k ≤ k + len (uMinus m) ∧
      Lifecycle.aArch k (k + len (uPlus m)) = Lifecycle.aArch k (k + len (uMinus m)) ∧
      Lifecycle.aArch k (k + len (uPlus m)) = m + 3) := by
  unfold Lifecycle.aArch
  rw [len_vPlus, len_vMinus, len_uPlus, len_uMinus]
  exact ⟨⟨by omega, by omega, rfl, by omega⟩, ⟨by omega, by omega, rfl, by omega⟩⟩

/-- **Theorem 28.7**, "arbitrarily far in either winding direction". -/
theorem opposite_routes_unbounded (N : ℤ) :
    (∃ m : ℕ, 3 ≤ m ∧ N < bal (vPlus m)) ∧ (∃ m : ℕ, 3 ≤ m ∧ bal (uPlus m) < N) := by
  constructor
  · rcases Int.lt_trichotomy N 0 with h | h | h
    · exact ⟨3, by omega, by rw [bal_vPlus]; omega⟩
    · exact ⟨3, by omega, by rw [bal_vPlus]; omega⟩
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt h)
      exact ⟨n + 3, by omega, by rw [bal_vPlus]; omega⟩
  · rcases Int.lt_trichotomy N 0 with h | h | h
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -N by omega)
      exact ⟨n + 4, by omega, by rw [bal_uPlus]; omega⟩
    · exact ⟨4, by omega, by rw [bal_uPlus]; omega⟩
    · exact ⟨3, by omega, by rw [bal_uPlus]; omega⟩

/-! ## 28.8 -/

/-- `w^r`. -/
def wpow (w : Word) : ℕ → Word
  | 0 => []
  | r + 1 => wpow w r ++ w

theorem bal_wpow (w : Word) (hw : bal w = 0) : ∀ r, bal (wpow w r) = 0
  | 0 => rfl
  | r + 1 => by change bal (wpow w r ++ w) = 0; rw [bal_append, bal_wpow w hw r, hw]; rfl

theorem len_wpow (w : Word) : ∀ r, len (wpow w r) = r * len w
  | 0 => by change 0 = 0 * _; rw [Nat.zero_mul]
  | r + 1 => by
    change (wpow w r ++ w).length = (r + 1) * w.length
    rw [List.length_append, Nat.succ_mul]
    have h := len_wpow w r
    exact congrArg (· + w.length) h

theorem wpow_add (w : Word) (r : ℕ) : ∀ d, wpow w (r + d) = wpow w r ++ wpow w d
  | 0 => by change wpow w r = wpow w r ++ []; rw [List.append_nil]
  | d + 1 => by
    change wpow w (r + d) ++ w = wpow w r ++ (wpow w d ++ w)
    rw [wpow_add w r d, List.append_assoc]

theorem len_wpow_succ_pos (w : Word) (hw : w ≠ []) (d : ℕ) : 1 ≤ (wpow w (d + 1)).length := by
  change 1 ≤ (wpow w d ++ w).length
  rw [List.length_append]
  cases w with
  | nil => exact absurd rfl hw
  | cons b w' => rw [List.length_cons]; omega

theorem wpow_ne (w : Word) (hw : w ≠ []) {r t : ℕ} (hrt : r ≠ t) (u : Word) :
    wpow w r ++ u ≠ wpow w t ++ u := by
  intro h
  have hl := congrArg List.length h
  rw [List.length_append, List.length_append] at hl
  rcases Nat.lt_or_gt_of_ne hrt with hlt | hlt
  · obtain ⟨d, rfl⟩ : ∃ d, t = r + (d + 1) := ⟨t - r - 1, by omega⟩
    rw [wpow_add, List.length_append] at hl
    have := len_wpow_succ_pos w hw d; omega
  · obtain ⟨d, rfl⟩ : ∃ d, r = t + (d + 1) := ⟨r - t - 1, by omega⟩
    rw [wpow_add, List.length_append] at hl
    have := len_wpow_succ_pos w hw d; omega

theorem inv2_inv2 (M : Mat2) : inv2 (inv2 M) = M := by
  cases M with
  | mk a b c d => apply ext' <;> dsimp only [inv2] <;> omega

/-- Distinct continuations give distinct retained relations. -/
theorem Qs_inj {s : Bool} {u v : Word} (h : Qs s u = Qs s v) : u = v := by
  have h1 : inv2 (G u) = inv2 (G v) := by
    have h' := congrArg (· * inv2 (A s)) h
    simp only [Qs, mul_assoc', mul_inv2_of_det (A s) (det_A s), mul_one'] at h'
    exact h'
  have h2 : G u = G v := by rw [← inv2_inv2 (G u), h1, inv2_inv2]
  exact Frame.G_inj h2

/-- Theorem 2.4 carried to the retained relation: no nonempty continuation returns it. -/
theorem no_relation_return (s : Bool) (x u : Word) (hu : u ≠ []) : Qs s (x ++ u) ≠ Qs s x :=
  fun h => no_raw_word_return x u hu (Qs_inj h)

def phiRadC24 (Q : Mat2) : ZMod 24 := (phiRadC Q : ZMod 24)

theorem balanced_transport (H : RadCocycle) (s : Bool) (w : Word) (hw : bal w = 0) (r j : ℕ) :
    phiRadC (Qs s (wpow w r ++ w.take j)) = eps s - bal (w.take j) := by
  rw [transport H, bal_append, bal_wpow w hw r]; omega

theorem balanced_residue (H : RadCocycle) (s : Bool) (w : Word) (hw : bal w = 0) (r t j : ℕ) :
    phiRadC24 (Qs s (wpow w r ++ w.take j)) = phiRadC24 (Qs s (wpow w t ++ w.take j)) := by
  unfold phiRadC24; rw [balanced_transport H s w hw r j, balanced_transport H s w hw t j]

theorem balanced_class_iff (H : RadCocycle) (s : Bool) (w : Word) (hw : bal w = 0) (r t j : ℕ) :
    psiRadC (Qs s (wpow w r ++ w.take j)) = psiRadC (Qs s (wpow w t ++ w.take j)) ↔
      routeCorrection (Qs s (wpow w r ++ w.take j)) = routeCorrection (Qs s (wpow w t ++ w.take j)) := by
  unfold psiRadC
  rw [balanced_transport H s w hw r j, balanced_transport H s w hw t j]
  constructor <;> intro h <;> omega

theorem balanced_no_return (s : Bool) (w : Word) (hw : w ≠ []) {r t : ℕ} (hrt : r ≠ t) (j : ℕ) :
    wpow w r ++ w.take j ≠ wpow w t ++ w.take j ∧
    Qs s (wpow w r ++ w.take j) ≠ Qs s (wpow w t ++ w.take j) :=
  ⟨wpow_ne w hw hrt _, fun h => wpow_ne w hw hrt _ (Qs_inj h)⟩

/-- **Theorem 28.8.** -/
theorem balanced_period (H : RadCocycle) (s : Bool) (w : Word) (hne : w ≠ []) (hw : bal w = 0)
    (j : ℕ) :
    (∀ r, phiRadC (Qs s (wpow w r ++ w.take j)) = eps s - bal (w.take j)) ∧
    (∀ r t, phiRadC24 (Qs s (wpow w r ++ w.take j)) = phiRadC24 (Qs s (wpow w t ++ w.take j))) ∧
    (∀ r t, psiRadC (Qs s (wpow w r ++ w.take j)) = psiRadC (Qs s (wpow w t ++ w.take j)) ↔
      routeCorrection (Qs s (wpow w r ++ w.take j)) = routeCorrection (Qs s (wpow w t ++ w.take j))) ∧
    (∀ r t, r ≠ t → wpow w r ++ w.take j ≠ wpow w t ++ w.take j ∧
      Qs s (wpow w r ++ w.take j) ≠ Qs s (wpow w t ++ w.take j)) :=
  ⟨fun r => balanced_transport H s w hw r j, fun r t => balanced_residue H s w hw r t j,
    fun r t => balanced_class_iff H s w hw r t j, fun _ _ hrt => balanced_no_return s w hne hrt j⟩

/-! ## 28.9 -/

theorem G_RL : G [true, false] = ⟨2, 1, 1, 1⟩ := by decide

/-- `RL = 𝖠_R²`, so `(RL)^r = 𝖠_R^{2r}` (Theorem 26.3's family). -/
theorem G_alt_mirror (r : ℕ) : G (wpow [true, false] r) = matPow Mirror.AR (2 * r) := by
  rw [Mirror.AR_pow_even]
  induction r with
  | zero => rfl
  | succ r ih =>
    change G (wpow [true, false] r ++ [true, false]) = R * L * matPow (R * L) r
    have hc : ∀ n, matPow (R * L) n * (R * L) = R * L * matPow (R * L) n := by
      intro n; rw [← Mirror.mpow_succ_right]; rfl
    rw [G_append, ih, show G [true, false] = R * L by decide, hc]

theorem G_alt (r : ℕ) :
    G (wpow [true, false] r) =
      ⟨Mirror.F (2 * r + 1), Mirror.F (2 * r), Mirror.F (2 * r), Mirror.F (2 * r + 1) - Mirror.F (2 * r)⟩ := by
  induction r with
  | zero => decide
  | succ r ih =>
    have h3 : Mirror.F (2 * r + 2) = Mirror.F (2 * r + 1) + Mirror.F (2 * r) := Mirror.F_rec (2 * r)
    have h4 : Mirror.F (2 * r + 3) = Mirror.F (2 * r + 2) + Mirror.F (2 * r + 1) := Mirror.F_rec (2 * r + 1)
    rw [show 2 * (r + 1) + 1 = 2 * r + 3 by ring, show 2 * (r + 1) = 2 * r + 2 by ring]
    change G (wpow [true, false] r ++ [true, false]) = _
    rw [G_append, ih, G_RL, mul_def]
    apply ext' <;> dsimp only <;> omega

theorem F_pos (n : ℕ) : 0 < Mirror.F (n + 1) := by
  have : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (Nat.succ_pos n)
  change (0 : ℤ) < ((Nat.fib (n + 1) : ℕ) : ℤ)
  omega

theorem Qs_alt_even (r : ℕ) :
    Qs true (wpow [true, false] r) =
      ⟨-Mirror.F (2 * r), -Mirror.F (2 * r + 1), Mirror.F (2 * r + 1), Mirror.F (2 * r + 2)⟩ := by
  have h3 : Mirror.F (2 * r + 2) = Mirror.F (2 * r + 1) + Mirror.F (2 * r) := Mirror.F_rec (2 * r)
  rw [Qs_true_of_G (G_alt r)]
  apply ext' <;> dsimp only <;> omega

theorem Qs_alt_odd (r : ℕ) :
    Qs true (wpow [true, false] r ++ [true]) =
      ⟨-Mirror.F (2 * r + 2), -Mirror.F (2 * r + 3), Mirror.F (2 * r + 1), Mirror.F (2 * r + 2)⟩ := by
  have h3 : Mirror.F (2 * r + 2) = Mirror.F (2 * r + 1) + Mirror.F (2 * r) := Mirror.F_rec (2 * r)
  have h4 : Mirror.F (2 * r + 3) = Mirror.F (2 * r + 2) + Mirror.F (2 * r + 1) := Mirror.F_rec (2 * r + 1)
  rw [Qs_true_explicit, G_snoc, G_alt, gen_true, mul_def]
  apply ext' <;> dsimp only [R] <;> omega

def trace (Q : Mat2) : ℤ := Q.a + Q.d

theorem sq_of_trace_zero (Q : Mat2) (htr : trace Q = 0) (hdet : Q.det = 1) : Q * Q = -1 := by
  cases Q with
  | mk a b c d =>
    change a + d = 0 at htr
    change a * d - b * c = 1 at hdet
    obtain rfl : d = -a := by omega
    have e1 : a * -a = -(a * a) := by ring
    rw [e1] at hdet
    refine ext' ?_ ?_ ?_ ?_
    · change a * a + b * c = -1; omega
    · change a * b + b * -a = -0; ring
    · change c * a + -a * c = -0; ring
    · change c * b + -a * -a = -1
      have e2 : c * b = b * c := by ring
      have e3 : -a * -a = a * a := by ring
      rw [e2, e3]; omega

def receiver (Q : Mat2) : ℤ × ℤ × ℤ := (phiRadC Q, routeCorrection Q, psiRadC Q)

theorem bal_alt_even (r : ℕ) : bal (wpow [true, false] r) = 0 := bal_wpow _ (by decide) r
theorem bal_alt_odd (r : ℕ) : bal (wpow [true, false] r ++ [true]) = 1 := by
  rw [bal_append, bal_alt_even]; decide

theorem trace_alt_even (r : ℕ) : trace (Qs true (wpow [true, false] r)) = Mirror.F (2 * r + 1) := by
  have h3 : Mirror.F (2 * r + 2) = Mirror.F (2 * r + 1) + Mirror.F (2 * r) := Mirror.F_rec (2 * r)
  rw [Qs_alt_even]; change -Mirror.F (2 * r) + Mirror.F (2 * r + 2) = _; omega

theorem trace_alt_odd (r : ℕ) : trace (Qs true (wpow [true, false] r ++ [true])) = 0 := by
  rw [Qs_alt_odd]; change -Mirror.F (2 * r + 2) + Mirror.F (2 * r + 2) = 0; omega

theorem sigma_alt_even (r : ℕ) : routeCorrection (Qs true (wpow [true, false] r)) = 1 := by
  have h3 : Mirror.F (2 * r + 2) = Mirror.F (2 * r + 1) + Mirror.F (2 * r) := Mirror.F_rec (2 * r)
  have hp := F_pos (2 * r)
  rw [Qs_alt_even, routeCorrection_mk_of_c_pos hp]
  exact sgnInt_of_pos (by omega)

theorem sigma_alt_odd (r : ℕ) : routeCorrection (Qs true (wpow [true, false] r ++ [true])) = 0 := by
  rw [Qs_alt_odd, routeCorrection_mk_of_c_pos (F_pos (2 * r))]
  rw [show -Mirror.F (2 * r + 2) + Mirror.F (2 * r + 2) = 0 by omega]; rfl

/-- **Theorem 28.9, the table.** -/
theorem alternating_table (H : RadCocycle) (r : ℕ) :
    (bal (wpow [true, false] r) = 0 ∧ phiRadC (Qs true (wpow [true, false] r)) = 1 ∧
      trace (Qs true (wpow [true, false] r)) = Mirror.F (2 * r + 1) ∧
      routeCorrection (Qs true (wpow [true, false] r)) = 1 ∧
      psiRadC (Qs true (wpow [true, false] r)) = -2) ∧
    (bal (wpow [true, false] r ++ [true]) = 1 ∧ phiRadC (Qs true (wpow [true, false] r ++ [true])) = 0 ∧
      trace (Qs true (wpow [true, false] r ++ [true])) = 0 ∧
      routeCorrection (Qs true (wpow [true, false] r ++ [true])) = 0 ∧
      psiRadC (Qs true (wpow [true, false] r ++ [true])) = 0) := by
  have e1 : eps true = 1 := rfl
  refine ⟨⟨bal_alt_even r, ?_, trace_alt_even r, sigma_alt_even r, ?_⟩,
    ⟨bal_alt_odd r, ?_, trace_alt_odd r, sigma_alt_odd r, ?_⟩⟩
  · rw [transport H, bal_alt_even, e1]; rfl
  · unfold psiRadC; rw [transport H, bal_alt_even, sigma_alt_even, e1]; rfl
  · rw [transport H, bal_alt_odd, e1]; rfl
  · unfold psiRadC; rw [transport H, bal_alt_odd, sigma_alt_odd, e1]; rfl

theorem alternating_receiver (H : RadCocycle) (r : ℕ) :
    receiver (Qs true (wpow [true, false] r)) = (1, 1, -2) ∧
    receiver (Qs true (wpow [true, false] r ++ [true])) = (0, 0, 0) := by
  obtain ⟨⟨-, h1, -, h2, h3⟩, ⟨-, h4, -, h5, h6⟩⟩ := alternating_table H r
  exact ⟨by rw [receiver, h1, h2, h3], by rw [receiver, h4, h5, h6]⟩

theorem alt_odd_sq (r : ℕ) :
    Qs true (wpow [true, false] r ++ [true]) * Qs true (wpow [true, false] r ++ [true]) = -1 :=
  sq_of_trace_zero _ (trace_alt_odd r) (det_Qs _ _)

/-- The alternating continuation after `n` hands: `ε, R, RL, RLR, …`. -/
def altWord (n : ℕ) : Word := wpow [true, false] (n / 2) ++ (if n % 2 = 1 then [true] else [])

theorem len_altWord (n : ℕ) : len (altWord n) = n := by
  unfold altWord
  have h := len_wpow [true, false] (n / 2)
  simp only [len] at h
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hn | hn
  · rw [if_neg (show ¬ (n % 2 = 1) by omega), List.append_nil, len, h]; change n / 2 * 2 = n; omega
  · rw [if_pos hn, len, List.length_append, h]; change n / 2 * 2 + 1 = n; omega

theorem altWord_receiver (H : RadCocycle) (n : ℕ) :
    receiver (Qs true (altWord n)) = if n % 2 = 1 then (0, 0, 0) else (1, 1, -2) := by
  unfold altWord
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hn | hn
  · have hn' : ¬ (n % 2 = 1) := by omega
    rw [if_neg hn', List.append_nil, if_neg hn']; exact (alternating_receiver H _).1
  · rw [if_pos hn, if_pos hn]; exact (alternating_receiver H _).2

/-- **Theorem 28.9.** The receiver `(Φ, σ, Ψ)` has exact period two. -/
theorem altWord_period_two (H : RadCocycle) (n : ℕ) :
    receiver (Qs true (altWord (n + 2))) = receiver (Qs true (altWord n)) := by
  rw [altWord_receiver H, altWord_receiver H, show (n + 2) % 2 = n % 2 by omega]

/-- **Theorem 28.9.** The full relative matrices never repeat. -/
theorem altWord_no_matrix_return {n k : ℕ} (h : n ≠ k) : Qs true (altWord n) ≠ Qs true (altWord k) := by
  intro he
  have := congrArg len (Qs_inj he)
  rw [len_altWord, len_altWord] at this
  exact h this

theorem alt_trace_step (r : ℕ) : Mirror.F (2 * r + 1) < Mirror.F (2 * (r + 1) + 1) := by
  have h4 : Mirror.F (2 * r + 3) = Mirror.F (2 * r + 2) + Mirror.F (2 * r + 1) := Mirror.F_rec (2 * r + 1)
  have hp : 0 < Mirror.F (2 * r + 2) := F_pos (2 * r + 1)
  change Mirror.F (2 * r + 1) < Mirror.F (2 * r + 3)
  omega

/-- **Theorem 28.9.** The even-position traces `F₁, F₃, F₅, …` strictly grow. -/
theorem alt_trace_strict (r : ℕ) : ∀ d, trace (Qs true (wpow [true, false] r)) <
    trace (Qs true (wpow [true, false] (r + (d + 1))))
  | 0 => by rw [trace_alt_even, trace_alt_even]; exact alt_trace_step r
  | d + 1 => by
    have ih := alt_trace_strict r d
    rw [trace_alt_even, trace_alt_even] at *
    exact Int.lt_trans ih (alt_trace_step (r + (d + 1)))

/-! ## Side exchange: the `L`-emission mirror -/

theorem G_shadow_explicit (v : Word) :
    G (shadow v) = ⟨(G v).d, (G v).c, (G v).b, (G v).a⟩ := by
  rw [G_shadow, mul_def, mul_def]
  apply ext' <;> dsimp only [Mat2.P] <;> ring

theorem bal_shadow : ∀ v : Word, bal (shadow v) = - bal v
  | [] => rfl
  | true :: w => by
    change bal (false :: shadow w) = - bal (true :: w)
    rw [bal_false, bal_true, bal_shadow w]; omega
  | false :: w => by
    change bal (true :: shadow w) = - bal (false :: w)
    rw [bal_false, bal_true, bal_shadow w]; omega

theorem sigma_side_mirror (v : Word) :
    routeCorrection (Qs false (shadow v)) = - routeCorrection (Qs true v) := by
  rw [Qs_false_explicit, G_shadow_explicit, Qs_true_explicit]
  have ha := G_a_pos v; have hd := G_d_pos v
  obtain ⟨h1, h2, h3, h4⟩ := nonneg_G v
  dsimp only
  rw [routeCorrection_mk_of_c_neg (by omega), routeCorrection_mk_of_c_pos (by omega)]
  exact congrArg (fun z => - sgnInt z) (by ring)

/-- The side mirror negates transport and class: `Φ(Q_L(v̄)) = −Φ(Q_R(v))`, `Ψ(Q_L(v̄)) = −Ψ(Q_R(v))`. -/
theorem side_mirror (H : RadCocycle) (v : Word) :
    phiRadC (Qs false (shadow v)) = - phiRadC (Qs true v) ∧
    psiRadC (Qs false (shadow v)) = - psiRadC (Qs true v) := by
  have e1 : eps true = 1 := rfl
  have e2 : eps false = -1 := rfl
  constructor
  · rw [transport H, transport H, bal_shadow, e1, e2]; omega
  · unfold psiRadC; rw [transport H, transport H, bal_shadow, sigma_side_mirror, e1, e2]; omega

theorem shadow_alt (r : ℕ) : shadow (wpow [true, false] r) = wpow [false, true] r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change List.map bar (wpow [true, false] r ++ [true, false]) = wpow [false, true] r ++ [false, true]
    rw [List.map_append]
    exact congrArg (· ++ [false, true]) ih

theorem shadow_replicate (n : ℕ) : shadow (List.replicate n true) = List.replicate n false := by
  change List.map bar (List.replicate n true) = _
  rw [List.map_replicate]; rfl

/-- **Theorem 28.9, side mirror** (`L`-emission, word `LR`): negated coordinates. -/
theorem alternating_mirror (H : RadCocycle) (r : ℕ) :
    phiRadC (Qs false (wpow [false, true] r)) = -1 ∧ psiRadC (Qs false (wpow [false, true] r)) = 2 ∧
    phiRadC (Qs false (wpow [false, true] r ++ [false])) = 0 ∧
    psiRadC (Qs false (wpow [false, true] r ++ [false])) = 0 := by
  obtain ⟨⟨-, h1, -, -, h2⟩, ⟨-, h3, -, -, h4⟩⟩ := alternating_table H r
  have m1 := side_mirror H (wpow [true, false] r)
  have m2 := side_mirror H (wpow [true, false] r ++ [true])
  rw [shadow_alt] at m1
  have hs : shadow (wpow [true, false] r ++ [true]) = wpow [false, true] r ++ [false] := by
    change List.map bar (wpow [true, false] r ++ [true]) = _
    rw [List.map_append]; exact congrArg (· ++ [false]) (shadow_alt r)
  rw [hs] at m2
  rw [h1] at m1; rw [h2] at m1; rw [h3] at m2; rw [h4] at m2
  exact ⟨m1.1, m1.2, m2.1, m2.2⟩

/-! ## 28.10 -/

theorem matPow_Rinv : ∀ m : ℕ, matPow Rinv m = ⟨1, -(m : ℤ), 0, 1⟩
  | 0 => by decide
  | m + 1 => by
    change Rinv * matPow Rinv m = _
    rw [matPow_Rinv m, mul_def]
    apply ext' <;> dsimp only [Rinv] <;> omega

theorem ray_matrix (m : ℕ) (hm : 1 ≤ m) :
    Qs true (List.replicate (m - 1) true) = ⟨1 - m, -(m : ℤ), 1, 1⟩ ∧
    Qs true (List.replicate (m - 1) true) = matPow Rinv m * L := by
  have h1 : Qs true (List.replicate (m - 1) true) = ⟨1 - m, -(m : ℤ), 1, 1⟩ := by
    rw [Qs_true_of_G (G_replicate_true _)]
    apply ext' <;> dsimp only <;> omega
  refine ⟨h1, ?_⟩
  rw [h1, matPow_Rinv, mul_def]
  apply ext' <;> dsimp only [L] <;> omega

theorem ray_trace (m : ℕ) (hm : 1 ≤ m) : trace (Qs true (List.replicate (m - 1) true)) = 2 - m := by
  rw [(ray_matrix m hm).1]; change 1 - (m : ℤ) + 1 = 2 - m; omega

/-- Definition 28.2 alone: the ray matrix has `c = 1`, so the Dedekind sum is empty and
    `Φ = tr = 2 − m`. No `RadCocycle`. -/
theorem ray_phi (m : ℕ) (hm : 1 ≤ m) :
    phiRadC (Qs true (List.replicate (m - 1) true)) = 2 - m := by
  rw [(ray_matrix m hm).1]
  change (1 * ((1 : ℕ) * (1 - (m : ℤ) + 1) - 3 * dsum (1 - m) 1) / ((1 : ℕ) * (1 : ℕ)) : ℤ) = 2 - m
  have : dsum (1 - (m : ℤ)) 1 = 0 := rfl
  rw [this]; omega

theorem ray_psi (m : ℕ) (hm : 1 ≤ m) :
    psiRadC (Qs true (List.replicate (m - 1) true)) = 2 - m - 3 * sgnInt (2 - m) := by
  unfold psiRadC
  rw [ray_phi m hm, (ray_matrix m hm).1, routeCorrection_mk_of_c_pos (by decide),
    show (1 : ℤ) - m + 1 = 2 - m by omega]

/-- The finite scan rows `m = 1, 2, 3, 4`: trace and class value, computed without any hypothesis. -/
theorem ray_scan_small :
    (trace (Qs true []) = 1 ∧ psiRadC (Qs true []) = -2) ∧
    (trace (Qs true [true]) = 0 ∧ psiRadC (Qs true [true]) = 0) ∧
    (trace (Qs true [true, true]) = -1 ∧ psiRadC (Qs true [true, true]) = 2) ∧
    (trace (Qs true [true, true, true]) = -2 ∧ psiRadC (Qs true [true, true, true]) = 1) := by
  decide

/-- Elliptic lift orders `6, 4, 3` at `m = 1, 2, 3`: least positive power equal to `I`. -/
theorem ray_elliptic_orders :
    (matPow (Qs true []) 6 = 1 ∧ ∀ k, k < 6 → 0 < k → matPow (Qs true []) k ≠ 1) ∧
    (matPow (Qs true [true]) 4 = 1 ∧ ∀ k, k < 4 → 0 < k → matPow (Qs true [true]) k ≠ 1) ∧
    (matPow (Qs true [true, true]) 3 = 1 ∧ ∀ k, k < 3 → 0 < k → matPow (Qs true [true, true]) k ≠ 1) := by
  decide

def parI (k : ℕ) : Mat2 := ⟨1 + 2 * (k : ℤ), 4 * (k : ℤ), -(k : ℤ), 1 - 2 * (k : ℤ)⟩

theorem parabolic_pow : ∀ k, matPow ⟨-3, -4, 1, 1⟩ k = parI k ∨ matPow ⟨-3, -4, 1, 1⟩ k = -(parI k)
  | 0 => Or.inl (by decide)
  | k + 1 => by
    rcases parabolic_pow k with h | h
    · right
      change (⟨-3, -4, 1, 1⟩ : Mat2) * matPow ⟨-3, -4, 1, 1⟩ k = _
      rw [h]; unfold parI
      apply ext' <;> simp only [mul_def, neg_a, neg_b, neg_c, neg_d] <;> omega
    · left
      change (⟨-3, -4, 1, 1⟩ : Mat2) * matPow ⟨-3, -4, 1, 1⟩ k = _
      rw [h]; unfold parI
      apply ext' <;> simp only [mul_def, neg_a, neg_b, neg_c, neg_d] <;> omega

/-- `m = 4`: parabolic, infinite lift order. -/
theorem ray_parabolic : Qs true [true, true, true] = ⟨-3, -4, 1, 1⟩ ∧
    ∀ k, matPow (Qs true [true, true, true]) (k + 1) ≠ 1 := by
  have hQ : Qs true [true, true, true] = ⟨-3, -4, 1, 1⟩ := by decide
  refine ⟨hQ, fun k h => ?_⟩
  rw [hQ] at h
  rcases parabolic_pow (k + 1) with h' | h' <;> rw [h'] at h <;> have hc := congrArg Mat2.c h
  · change -((k + 1 : ℕ) : ℤ) = 0 at hc; omega
  · change - -((k + 1 : ℕ) : ℤ) = 0 at hc; omega

def chebU (T : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => T * chebU T (k + 1) - chebU T k

theorem chebU_grow (T : ℤ) (hT : 3 ≤ T) : ∀ k, 0 ≤ chebU T k ∧ chebU T k < chebU T (k + 1)
  | 0 => by change (0 : ℤ) ≤ 0 ∧ (0 : ℤ) < 1; exact ⟨Int.le_refl 0, by decide⟩
  | k + 1 => by
    obtain ⟨h0, h1⟩ := chebU_grow T hT k
    have hm : 3 * chebU T (k + 1) ≤ T * chebU T (k + 1) :=
      Int.mul_le_mul_of_nonneg_right hT (by omega)
    change 0 ≤ chebU T (k + 1) ∧ chebU T (k + 1) < T * chebU T (k + 1) - chebU T k
    exact ⟨Int.le_of_lt (Int.lt_of_le_of_lt h0 h1), Decidable.byContradiction fun hn => by omega⟩

theorem matPow_cheb (M : Mat2) (hdet : M.a * M.d - M.b * M.c = 1) : ∀ k, matPow M (k + 1) =
    ⟨chebU (trace M) (k + 1) * M.a - chebU (trace M) k, chebU (trace M) (k + 1) * M.b,
     chebU (trace M) (k + 1) * M.c, chebU (trace M) (k + 1) * M.d - chebU (trace M) k⟩
  | 0 => by
    change M * 1 = _
    rw [mul_one']
    have h1 : chebU (trace M) 1 = 1 := rfl
    have h0 : chebU (trace M) 0 = 0 := rfl
    rw [h1, h0]
    apply ext' <;> dsimp only <;> ring
  | k + 1 => by
    change M * matPow M (k + 1) = _
    have hu : chebU (trace M) (k + 1 + 1) =
        (M.a + M.d) * chebU (trace M) (k + 1) - chebU (trace M) k := rfl
    rw [matPow_cheb M hdet k, mul_def, hu]
    apply ext' <;> dsimp only
    · refine Int.sub_eq_zero.mp (Eq.trans (?_ : _ = chebU (trace M) (k + 1) * (1 - (M.a * M.d - M.b * M.c))) (by rw [hdet]; ring))
      ring
    · ring
    · ring
    · refine Int.sub_eq_zero.mp (Eq.trans (?_ : _ = chebU (trace M) (k + 1) * (1 - (M.a * M.d - M.b * M.c))) (by rw [hdet]; ring))
      ring

theorem matPow_neg (M : Mat2) : ∀ k, matPow (-M) k = matPow M k ∨ matPow (-M) k = -(matPow M k)
  | 0 => Or.inl rfl
  | k + 1 => by
    rcases matPow_neg M k with h | h
    · right
      change -M * matPow (-M) k = -(M * matPow M k)
      rw [h]; apply ext' <;> simp only [mul_def, neg_a, neg_b, neg_c, neg_d] <;> ring
    · left
      change -M * matPow (-M) k = M * matPow M k
      rw [h]; apply ext' <;> simp only [mul_def, neg_a, neg_b, neg_c, neg_d] <;> ring

/-- A determinant-one matrix with `c = 1` and trace `≤ −3` has no positive power equal to `I`. -/
theorem hyperbolic_infinite_order (Q : Mat2) (hdet : Q.det = 1) (hc : Q.c = 1)
    (htr : trace Q ≤ -3) : ∀ k, matPow Q (k + 1) ≠ 1 := by
  intro k h
  have hM : (-Q).a * (-Q).d - (-Q).b * (-Q).c = 1 := by
    have e : -Q.a * -Q.d - -Q.b * -Q.c = Q.a * Q.d - Q.b * Q.c := by ring
    change -Q.a * -Q.d - -Q.b * -Q.c = 1
    rw [e]; exact hdet
  have hT : 3 ≤ trace (-Q) := by
    have : Q.a + Q.d ≤ -3 := htr
    change 3 ≤ -Q.a + -Q.d; omega
  have hcheb := matPow_cheb (-Q) hM k
  have hg := chebU_grow (trace (-Q)) hT k
  rcases matPow_neg Q (k + 1) with h' | h'
  · rw [h, hcheb] at h'
    have hc' := congrArg Mat2.c h'
    change chebU (trace (-Q)) (k + 1) * -Q.c = 0 at hc'
    rw [hc, Int.mul_neg, Int.mul_one] at hc'; omega
  · rw [h, hcheb] at h'
    have hc' := congrArg Mat2.c h'
    change chebU (trace (-Q)) (k + 1) * -Q.c = -0 at hc'
    rw [hc, Int.mul_neg, Int.mul_one] at hc'; omega

/-- `m ≥ 5`: hyperbolic (`|tr| > 2`), infinite lift order, `Ψ = 5 − m`. -/
theorem ray_hyperbolic (m : ℕ) (hm : 5 ≤ m) :
    trace (Qs true (List.replicate (m - 1) true)) < -2 ∧
    (∀ k, matPow (Qs true (List.replicate (m - 1) true)) (k + 1) ≠ 1) ∧
    psiRadC (Qs true (List.replicate (m - 1) true)) = 5 - m := by
  have ht := ray_trace m (by omega)
  refine ⟨by omega, hyperbolic_infinite_order _ (det_Qs _ _)
    (by rw [(ray_matrix m (by omega)).1]) (by omega), ?_⟩
  rw [ray_psi m (by omega), sgnInt_of_neg (by omega)]; omega

/-- **Proposition 28.10**, side mirror: the `L`-emission ray negates `Φ` and `Ψ`. -/
theorem ray_mirror (H : RadCocycle) (n : ℕ) :
    phiRadC (Qs false (List.replicate n false)) = - phiRadC (Qs true (List.replicate n true)) ∧
    psiRadC (Qs false (List.replicate n false)) = - psiRadC (Qs true (List.replicate n true)) := by
  rw [← shadow_replicate]; exact side_mirror H _

/-! ## 28.3 instances and witnesses -/

def cocycleDefect (X Y : Mat2) : ℤ :=
  phiRadC (X * Y) - (phiRadC X + phiRadC Y - 3 * sgnInt (X.c * Y.c * (X * Y).c))

/-- Theorem 28.9's `Φ = 1` at `r = 0,1,2,3` with no hypothesis: direct evaluation of the
    Dedekind sum (`c = 1, 2, 5, 13`). The all-`r` statement is `alternating_table`, from `RadCocycle`. -/
theorem alternating_phi_instances :
    phiRadC (Qs true (wpow [true, false] 0)) = 1 ∧ phiRadC (Qs true (wpow [true, false] 1)) = 1 ∧
    phiRadC (Qs true (wpow [true, false] 2)) = 1 ∧ phiRadC (Qs true (wpow [true, false] 3)) = 1 := by
  decide

/-- Exact instances of the imported cocycle law on `phiRadC` as defined: witnesses that the
    hypothesis is consistent with the definition, not the law. -/
theorem cocycle_instances :
    cocycleDefect Linv (A true) = 0 ∧ cocycleDefect Linv ⟨2, 1, 1, 1⟩ = 0 ∧
    cocycleDefect Squarter ⟨5, 3, 13, 8⟩ = 0 ∧ cocycleDefect Linv ⟨1, 0, 2, 1⟩ = 0 ∧
    cocycleDefect ⟨2, 1, 1, 1⟩ ⟨1, 1, 1, 2⟩ = 0 := by
  decide

/-- Exact instance of the imported conjugacy law, and the witness that `Φ` itself is
    frame-sensitive: conjugating `RL` by `L` moves `Φ` from `3` to `−3` and fixes `Ψ`. -/
theorem conj_instance_and_frame_sensitivity :
    psiRadC (inv2 L * ⟨2, 1, 1, 1⟩ * L) = psiRadC ⟨2, 1, 1, 1⟩ ∧
    phiRadC ⟨2, 1, 1, 1⟩ = 3 ∧ phiRadC (inv2 L * ⟨2, 1, 1, 1⟩ * L) = -3 := by
  decide

/-- Central invariance is not a lift detector: `Q` and `−Q` share `Φ` and `Ψ`. -/
theorem central_sheet_invisible :
    phiRadC (-(A true)) = phiRadC (A true) ∧ psiRadC (-(A true)) = psiRadC (A true) ∧
    -(A true) ≠ A true :=
  ⟨phiRadC_neg _ (det_A true), psiRadC_neg _ (det_A true), by decide⟩

/-! ## 28.11 -/

/-- The quarter-turn admission phase of an `R`-emission is `3` whatever follows; the
    transport residue moves (`1`, then `0`, then `13` at `R¹²`); `ψ₁₂` of the continuation
    returns at `R¹²` while the residue does not. Three readings, three codomains
    (`Fin 4`, `ZMod 24`, `ZMod 12`). This witnesses three of the six ordered pairs:
    `[Φ]₂₄` and `ψ₁₂` are not read from `j_s`, and `[Φ]₂₄` is not read from `ψ₁₂`.
    The other three are `sep_phases_rest`; the coupling is `psi12_from_hand_and_phi24`. -/
theorem sep_phases :
    admittedPhases Squarter 4 (A true) = [(3 : Fin 4)] ∧
    phiRadC24 (Qs true []) = 1 ∧ phiRadC24 (Qs true [true]) = 0 ∧
    phiRadC24 (Qs true (List.replicate 12 true)) = 13 ∧
    psi12 ([] : Word) = 0 ∧ psi12 [true] = 1 ∧ psi12 (List.replicate 12 true) = 0 ∧
    (psi12 ([] : Word) = psi12 (List.replicate 12 true) ∧
      phiRadC24 (Qs true []) ≠ phiRadC24 (Qs true (List.replicate 12 true))) := by
  refine ⟨J_S_AR, ?_⟩
  decide

/-- The other three ordered pairs of Separation Rule 28.11. `Q_R(ε)` and `Q_L(L²)` share
    `[Φ]₂₄ = 1` and have `j_s = 3, 1` and `ψ₁₂ = 0, 10`, so neither `j_s` nor `ψ₁₂` is read
    from `[Φ]₂₄`. `Q_R(ε)` and `Q_L(ε)` share `ψ₁₂ = 0` (the same continuation `ε`) and have
    `j_s = 3, 1`, so `j_s` is not read from `ψ₁₂`. -/
theorem sep_phases_rest :
    admittedPhases Squarter 4 (A true) = [(3 : Fin 4)] ∧
    admittedPhases Squarter 4 (A false) = [(1 : Fin 4)] ∧
    phiRadC24 (Qs true []) = 1 ∧ phiRadC24 (Qs false [false, false]) = 1 ∧
    psi12 ([] : Word) = 0 ∧ psi12 [false, false] = 10 := by
  refine ⟨J_S_AR, J_S_AL, ?_⟩
  decide

/-- **Separation Rule 28.11, the coupling.** Under the imported cocycle law, the closure
    character of the continuation is the hand's sign minus the transport residue read
    modulo twelve: `ψ₁₂(v) = [ε_s]₁₂ − [Φ_Rad(Q_s(v))]₁₂`. -/
theorem psi12_from_hand_and_phi24 (H : RadCocycle) (s : Bool) (v : Word) :
    psi12 v = (eps s : ZMod 12) -
      ZMod.castHom (by decide : 12 ∣ 24) (ZMod 12) (phiRadC24 (Qs s v)) := by
  unfold phiRadC24
  rw [map_intCast, transport H s v]
  unfold psi12
  push_cast
  ring

/-- Transport return without class return (Theorem 28.7 at `m = 3`), and no matrix return. -/
theorem transport_return_not_class_return :
    phiRadC (Qs true (vPlus 3)) = phiRadC (Qs true (vMinus 3)) ∧
    psiRadC (Qs true (vPlus 3)) ≠ psiRadC (Qs true (vMinus 3)) ∧
    Qs true (vPlus 3) ≠ Qs true (vMinus 3) := by
  decide

/-- Class return by cancellation: `Ψ` equal while both `Φ` and `σ` changed. -/
theorem class_return_by_cancellation :
    psiRadC (Qs true []) = psiRadC (Qs true (vMinus 7)) ∧
    phiRadC (Qs true []) ≠ phiRadC (Qs true (vMinus 7)) ∧
    routeCorrection (Qs true []) ≠ routeCorrection (Qs true (vMinus 7)) := by
  decide

/-- Neither received equality implies exact matrix return. -/
theorem received_equality_not_matrix_return (s : Bool) {u v : Word} (h : u ≠ v) :
    Qs s u ≠ Qs s v :=
  fun he => h (Qs_inj he)

/-! ## 28.12 -/

/-- **Boundary Statement 28.12.** -/
theorem carried_memory (H : RadCocycle) :
    (∀ s v, psiRadC (Qs s v) = eps s - bal v - 3 * routeCorrection (Qs s v)) ∧
    (∀ s w, w ≠ [] → bal w = 0 → ∀ r j,
      phiRadC (Qs s (wpow w r ++ w.take j)) = eps s - bal (w.take j) ∧
      Qs s (wpow w (r + 1) ++ w.take j) ≠ Qs s (wpow w r ++ w.take j)) ∧
    (∀ n, receiver (Qs true (altWord (n + 2))) = receiver (Qs true (altWord n)) ∧
      Qs true (altWord (n + 2)) ≠ Qs true (altWord n)) ∧
    (∀ m, 1 ≤ m → psiRadC (Qs true (List.replicate (m - 1) true)) = 2 - m - 3 * sgnInt (2 - m)) :=
  ⟨class_decomposition H,
    fun s w hne hw r j => ⟨balanced_transport H s w hw r j,
      (balanced_no_return s w hne (by omega) j).2⟩,
    fun n => ⟨altWord_period_two H n, altWord_no_matrix_return (by omega)⟩,
    fun m hm => ray_psi m hm⟩


#print axioms sumTo_congr
#print axioms sumTo_shift
#print axioms sumTo_reflect
#print axioms sumTo_neg
#print axioms dTerm_reflect
#print axioms dsum_neg
#print axioms ediv_is_floor
#print axioms dsum_eq_sD
#print axioms sgnInt_zero
#print axioms sgnInt_of_pos
#print axioms sgnInt_of_neg
#print axioms routeCorrection_eq_sgn
#print axioms sgnInt_mul_of_pos_right
#print axioms sgnInt_mul_of_neg_right
#print axioms sgnInt_mul_of_pos_left
#print axioms sgnInt_mul_of_neg_left
#print axioms eps_eq_bal
#print axioms eps_eq_sigma
#print axioms Qs_nil
#print axioms det_A
#print axioms det_inv2'
#print axioms det_Qs
#print axioms Qs_snoc
#print axioms d_unit
#print axioms phiRadC_neg
#print axioms routeCorrection_neg'
#print axioms psiRadC_neg
#print axioms class_coordinate
#print axioms G_a_pos
#print axioms G_d_pos
#print axioms Qs_true_explicit
#print axioms Qs_false_explicit
#print axioms Qs_true_c_pos
#print axioms Qs_false_c_neg
#print axioms Linv_mul_c
#print axioms Linv_Qs_true_c_pos
#print axioms Linv_Qs_false_c_neg
#print axioms Qs_Linv_same_sign
#print axioms Linv_triple
#print axioms phiRadC_A
#print axioms phiRadC_Rinv
#print axioms phiRadC_Linv
#print axioms transport
#print axioms class_decomposition
#print axioms equal_hand_winding_equal_phi
#print axioms hand_winding_not_force_psi
#print axioms Qs_true_of_G
#print axioms Qs_false_of_G
#print axioms routeCorrection_mk_of_c_pos
#print axioms routeCorrection_mk_of_c_neg
#print axioms G_replicate_true
#print axioms G_replicate_false
#print axioms bal_replicate_true
#print axioms bal_replicate_false
#print axioms G_vPlus
#print axioms G_vMinus
#print axioms G_uPlus
#print axioms G_uMinus
#print axioms len_vPlus
#print axioms len_vMinus
#print axioms len_uPlus
#print axioms len_uMinus
#print axioms bal_vPlus
#print axioms bal_vMinus
#print axioms bal_uPlus
#print axioms bal_uMinus
#print axioms sigma_vPlus
#print axioms sigma_vMinus
#print axioms sigma_uPlus
#print axioms sigma_uMinus
#print axioms opposite_routes
#print axioms opposite_routes_unbounded
#print axioms opposite_routes_equal_age
#print axioms bal_wpow
#print axioms len_wpow
#print axioms wpow_add
#print axioms len_wpow_succ_pos
#print axioms wpow_ne
#print axioms inv2_inv2
#print axioms Qs_inj
#print axioms no_relation_return
#print axioms balanced_transport
#print axioms balanced_residue
#print axioms balanced_class_iff
#print axioms balanced_no_return
#print axioms balanced_period
#print axioms G_RL
#print axioms G_alt_mirror
#print axioms G_alt
#print axioms F_pos
#print axioms Qs_alt_even
#print axioms Qs_alt_odd
#print axioms sq_of_trace_zero
#print axioms bal_alt_even
#print axioms bal_alt_odd
#print axioms trace_alt_even
#print axioms trace_alt_odd
#print axioms sigma_alt_even
#print axioms sigma_alt_odd
#print axioms alternating_table
#print axioms alternating_receiver
#print axioms alt_odd_sq
#print axioms len_altWord
#print axioms altWord_receiver
#print axioms altWord_period_two
#print axioms altWord_no_matrix_return
#print axioms alt_trace_step
#print axioms alt_trace_strict
#print axioms G_shadow_explicit
#print axioms bal_shadow
#print axioms sigma_side_mirror
#print axioms side_mirror
#print axioms shadow_alt
#print axioms shadow_replicate
#print axioms alternating_mirror
#print axioms matPow_Rinv
#print axioms ray_matrix
#print axioms ray_trace
#print axioms ray_phi
#print axioms ray_psi
#print axioms ray_scan_small
#print axioms ray_elliptic_orders
#print axioms parabolic_pow
#print axioms ray_parabolic
#print axioms chebU_grow
#print axioms matPow_cheb
#print axioms matPow_neg
#print axioms hyperbolic_infinite_order
#print axioms ray_hyperbolic
#print axioms ray_mirror
#print axioms alternating_phi_instances
#print axioms cocycle_instances
#print axioms conj_instance_and_frame_sensitivity
#print axioms central_sheet_invisible
#print axioms sep_phases
#print axioms sep_phases_rest
#print axioms psi12_from_hand_and_phi24
#print axioms transport_return_not_class_return
#print axioms class_return_by_cancellation
#print axioms received_equality_not_matrix_return
#print axioms carried_memory

end RadTransport
end RatioSpace.Two
