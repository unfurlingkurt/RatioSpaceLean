/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S03.Walk
import RatioSpace.ElementsI.S04.Composition
/-!
  Elements I §5.1–5.6 — Continued fractions, the two depth coordinates,
  endpoint contrast, walk distance, and the tension signature.

  This is the first half of §5. The second half (`Zphi.lean`, Def 5.7–5.9)
  neither imports this file nor is imported by it; the two meet only at the
  section boundary, in `Coherence.lean`, which imports both.

  Three things govern the shape of this file.

    * **The expansion has to run, not merely typecheck.** Def 5.1's Euclidean
      recursion decreases in the *second* argument, which Lean's structural
      checker does not see, so the usual move is well-founded recursion — and a
      well-founded definition is opaque to the kernel, which kills `decide` and
      with it every exact finite check below. `cfFuel` carries an explicit fuel
      argument instead, so the recursion is structural and reduces. `cfFuel_ext`
      says any sufficient fuel gives the same list, so the fuel is bookkeeping
      and not a parameter of the definition.

    * **The two lengths of Def 5.2 and Def 5.3 are different integers, and the
      book says so in its own worked example.** `lCF_three_two` … `dSB_four_three`
      are that example, checked. `lCF` is *not* invariant under `p:q ↦ q:p` and
      `dSB` is; `dSB_swap` is what makes Def 5.4's symmetry true, and the book
      names exactly that reason.

    * **Def 5.5's claim that `T_end` and `d_walk` "answer different questions"
      is a two-sided non-substitution claim: on pairs of addressed relations
      neither quantity is a function of the other. It is witnessed both ways
      here.** One pair of contrasts with equal `T_end` and unequal `d_walk`,
      one with equal `d_walk` and unequal `T_end`, stated on the addressed
      relations themselves at `Frame.Tend_eq_dwalk_ne_addressed` and
      `Frame.dwalk_eq_Tend_ne_addressed`. Either alone would leave the
      weaker reading that one refines the other. The two stay coupled: both are
      read off the same addressed relations, and measured from the root, `d_walk`
      from `ε` and `T_end` against `1:1` are both the length of the word.

  Everything is ℕ-valued. `dSB` uses truncated subtraction, which is honest
  only because `cfNat_sum_pos` says the sum it subtracts from is at least one on
  the whole domain of Def 5.1; that lemma is not decoration.
-/

namespace RatioSpace
namespace Pres

/-! ## Definition 5.1 — Canonical finite continued fraction -/

/-- The Euclidean expansion, with fuel so that the recursion is structural and
    the kernel can evaluate it. The invariant maintained by `cfNat` is
    `q ≤ fuel`, and `cfFuel_ext` says any fuel meeting it gives the same list. -/
def cfFuel : ℕ → ℕ → ℕ → List ℕ
  | 0, p, _ => [p]
  | n + 1, p, q =>
      if q = 0 then [p]
      else if p % q = 0 then [p / q]
      else (p / q) :: cfFuel n q (p % q)

/-- **Definition 5.1.** The canonical finite continued fraction of `p:q`, as the
    list `[a₀, a₁, …, a_m]`. Fuel `q` is always sufficient because the second
    argument strictly decreases. -/
def cfNat (p q : ℕ) : List ℕ := cfFuel q p q

/-- **Definition 5.1's total extension.** Book-faithful on the positive
    primitive domain (see `PPres.cf` below for the restricted definition
    proper); total on all of `Pres` beyond it, where the book asserts
    nothing. -/
def cf (A : Pres) : List ℕ := cfNat A.p A.q

/-- Any two sufficient fuels agree. Proved by strong induction on `q`, which is
    what the recursion actually descends on. -/
theorem cfFuel_ext : ∀ q n m p, q ≤ n → q ≤ m → cfFuel n p q = cfFuel m p q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro n m p hn hm
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      cases n <;> cases m <;> simp [cfFuel]
    · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hqne : q ≠ 0 := by omega
      have hlt : p % q < q := Nat.mod_lt _ hq
      by_cases hmod : p % q = 0
      · simp [cfFuel, hqne, hmod]
      · simp only [cfFuel, if_neg hqne, if_neg hmod]
        exact congrArg _ (ih (p % q) hlt n m q (by omega) (by omega))

theorem cfFuel_eq_cfNat {n p q : ℕ} (h : q ≤ n) : cfFuel n p q = cfNat p q :=
  cfFuel_ext q n q p h le_rfl

/-! ### The unfolding rules -/

@[simp] theorem cfNat_zero (p : ℕ) : cfNat p 0 = [p] := by simp [cfNat, cfFuel]

theorem cfNat_of_dvd {p q : ℕ} (hq : q ≠ 0) (h : p % q = 0) : cfNat p q = [p / q] := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp [cfNat, cfFuel, h]

theorem cfNat_cons {p q : ℕ} (hq : q ≠ 0) (h : p % q ≠ 0) :
    cfNat p q = (p / q) :: cfNat q (p % q) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hlt : p % (q + 1) < q + 1 := Nat.mod_lt _ (Nat.succ_pos q)
  simp only [cfNat, cfFuel, if_neg hq, if_neg h]
  exact congrArg _ (cfFuel_eq_cfNat (by omega))

theorem cfNat_ne_nil (p q : ℕ) : cfNat p q ≠ [] := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · simp [hq]
  · by_cases h : p % q = 0
    · simp [cfNat_of_dvd (by omega) h]
    · simp [cfNat_cons (by omega) h]

/-- **The reciprocal step, and it is the whole reason Def 5.4 is symmetric.**
    For a strictly smaller numerator the expansion simply gains a leading `0`,
    which changes the block count of Def 5.2 and changes nothing about the depth
    of Def 5.3. -/
theorem cfNat_of_lt {p q : ℕ} (hp : 0 < p) (h : p < q) : cfNat p q = 0 :: cfNat q p := by
  have hq : q ≠ 0 := by omega
  have hdiv : p / q = 0 := Nat.div_eq_of_lt h
  have hmod : p % q = p := Nat.mod_eq_of_lt h
  rw [cfNat_cons hq (by omega), hdiv, hmod]

/-! ### The uniqueness clause, `a_m ≥ 2` when `m ≥ 1` -/

/-- **Definition 5.1's final condition.** Whenever the expansion has more than
    one term, its last term is at least two. This is what removes the duplicate
    representation ending in `1`, and the Euclidean recursion delivers it rather
    than needing it imposed. Stated with `getLast?` so that no proof of
    non-emptiness has to be threaded through the induction. -/
theorem cfNat_getLast?_ge_two :
    ∀ q p a, 1 < (cfNat p q).length → (cfNat p q).getLast? = some a → 2 ≤ a := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro p a hlen hlast
    rcases Nat.eq_zero_or_pos q with hq | hq
    · rw [hq, cfNat_zero] at hlen
      simp only [List.length_cons, List.length_nil] at hlen; omega
    have hqne : q ≠ 0 := by omega
    by_cases hmod : p % q = 0
    · rw [cfNat_of_dvd hqne hmod] at hlen
      simp only [List.length_cons, List.length_nil] at hlen; omega
    have hlt : p % q < q := Nat.mod_lt _ hq
    have hdne : p % q ≠ 0 := hmod
    obtain ⟨b, L, hbL⟩ : ∃ b L, cfNat q (p % q) = b :: L := by
      match hcf : cfNat q (p % q) with
      | [] => exact absurd hcf (cfNat_ne_nil _ _)
      | b :: L => exact ⟨b, L, rfl⟩
    have hrec : cfNat p q = (p / q) :: b :: L := by rw [cfNat_cons hqne hmod, hbL]
    have hL : (cfNat p q).getLast? = (cfNat q (p % q)).getLast? := by
      rw [hrec, hbL, List.getLast?_cons_cons]
    by_cases hmod2 : q % (p % q) = 0
    · have hterm := cfNat_of_dvd hdne hmod2
      rw [hL, hterm] at hlast
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      have hdvd : (p % q) ∣ q := Nat.dvd_of_mod_eq_zero hmod2
      have hk : q / (p % q) * (p % q) = q := Nat.div_mul_cancel hdvd
      -- if the quotient were `≤ 1` then `q ≤ p % q`, and `p % q < q`
      rcases Nat.lt_or_ge (q / (p % q)) 2 with hc | hc
      · exfalso
        have hle : q / (p % q) * (p % q) ≤ 1 * (p % q) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.one_mul] at hle
        omega
      · exact hc
    · have h2 : 1 < (cfNat q (p % q)).length := by
        rw [cfNat_cons hdne hmod2]
        have hpos : 0 < (cfNat (p % q) (q % (p % q))).length :=
          List.length_pos_iff.mpr (cfNat_ne_nil (p % q) (q % (p % q)))
        simp only [List.length_cons]
        omega
      exact ih (p % q) hlt q a h2 (hL ▸ hlast)

/-! ## Definition 5.2 — Continued-fraction block length -/

/-- **Definition 5.2's total extension.** `ℓ_CF(p:q) = m + 1`: the number of
    Euclidean division stages. Restricted definition proper: `PPres.lCF`. -/
def lCF (A : Pres) : ℕ := (cf A).length

/-! ## Definition 5.3 — Stern-Brocot address depth -/

/-- The sum `∑ aᵢ`, which is one more than the depth. Kept separate so that the
    truncated subtraction in `dSB` is only ever performed where
    `cfNat_sum_pos` applies. -/
def cfSum (A : Pres) : ℕ := (cf A).sum

theorem cfNat_sum_pos : ∀ q p, 0 < p → 0 < (cfNat p q).sum := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro p hp
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; simpa using hp
    have hqne : q ≠ 0 := by omega
    by_cases hmod : p % q = 0
    · rw [cfNat_of_dvd hqne hmod]
      have : 0 < p / q := Nat.div_pos (Nat.le_of_dvd hp (Nat.dvd_of_mod_eq_zero hmod)) hq
      simpa using this
    · rw [cfNat_cons hqne hmod]
      have h1 : 0 < (cfNat q (p % q)).sum := ih (p % q) (Nat.mod_lt _ hq) q hq
      simp only [List.sum_cons]
      exact Nat.lt_of_lt_of_le h1 (Nat.le_add_left _ _)

/-- The truncated subtraction in `dSB` is honest: on Def 5.1's own domain the
    sum it subtracts from is at least one. -/
theorem cfSum_pos {A : Pres} (hp : 0 < A.p) : 0 < cfSum A := cfNat_sum_pos A.q A.p hp

/-- **Definition 5.3's total extension.** `d_SB(p:q) = (∑ aᵢ) − 1`: the number
    of elementary `L`/`R` refinements from the root. On the boundary this
    invents a depth for an improper presentation — `dSB (p:0) = p - 1` — which
    the book does not define; restricted definition proper: `PPres.dSB`. -/
def dSB (A : Pres) : ℕ := cfSum A - 1

/-- `d_SB(1:1) = 0`, the book's own anchor. -/
theorem dSB_one_one : dSB ⟨1, 1, by decide⟩ = 0 := by decide

/-! ### The book's own separation of the two lengths

  `3:2 = [1;2]` and `4:3 = [1;3]` have equal block length and unequal depth. A
  procedure sorting only by `ℓ_CF` treats these two relations as equally deep. -/

theorem cf_three_two : cf ⟨3, 2, by decide⟩ = [1, 2] := by decide
theorem cf_four_three : cf ⟨4, 3, by decide⟩ = [1, 3] := by decide

theorem lCF_three_two : lCF ⟨3, 2, by decide⟩ = 2 := by decide
theorem lCF_four_three : lCF ⟨4, 3, by decide⟩ = 2 := by decide
theorem dSB_three_two : dSB ⟨3, 2, by decide⟩ = 2 := by decide
theorem dSB_four_three : dSB ⟨4, 3, by decide⟩ = 3 := by decide

/-- **The two lengths are not interchangeable**, stated as the book states it:
    equal block length, unequal depth, on one exhibited pair. -/
theorem lCF_ne_dSB_witness :
    lCF ⟨3, 2, by decide⟩ = lCF ⟨4, 3, by decide⟩ ∧
      dSB ⟨3, 2, by decide⟩ ≠ dSB ⟨4, 3, by decide⟩ := by decide

/-! ### Depth is reciprocal-invariant, block length is not -/

/-- **`∑ aᵢ` is invariant under `p:q ↦ q:p`.** The reciprocal expansion differs
    by a leading `0`, which the sum does not see. -/
theorem cfNat_sum_swap {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (cfNat p q).sum = (cfNat q p).sum := by
  rcases Nat.lt_trichotomy p q with h | h | h
  · rw [cfNat_of_lt hp h]; simp
  · subst h; rfl
  · rw [cfNat_of_lt hq h]; simp

/-- **Definition 5.4's stated reason, as a theorem.** Reciprocal Stern-Brocot
    addresses have equal primitive depth. -/
theorem dSB_swap {A B : Pres} (hA : 0 < A.p) (hB : 0 < A.q)
    (hp : B.p = A.q) (hq : B.q = A.p) : dSB A = dSB B := by
  unfold dSB cfSum cf
  rw [hp, hq]
  exact congrArg (· - 1) (cfNat_sum_swap hA hB)

/-! ### One Euclidean step is one letter

  The two arithmetic facts the general depth theorem runs on. Both say the same
  thing from opposite sides: adding one component of a ratio to the other adds
  exactly one to the continued-fraction sum, because it adds exactly one to the
  leading quotient and leaves the remainder alone. -/

/-- `p:q ↦ (p+q):q` adds one to the sum. The leading quotient rises by one and
    the Euclidean remainder is untouched, so the whole tail is shared. -/
theorem cfNat_sum_add_right (p : ℕ) {q : ℕ} (hq : q ≠ 0) :
    (cfNat (p + q) q).sum = (cfNat p q).sum + 1 := by
  have hpos : 0 < q := Nat.pos_of_ne_zero hq
  have hdiv : (p + q) / q = p / q + 1 := Nat.add_div_right p hpos
  have hmod : (p + q) % q = p % q := Nat.add_mod_right p q
  by_cases h : p % q = 0
  · rw [cfNat_of_dvd hq (by rw [hmod]; exact h), cfNat_of_dvd hq h, hdiv]
    simp
  · rw [cfNat_cons hq (by rw [hmod]; exact h), cfNat_cons hq h, hdiv, hmod]
    simp only [List.sum_cons]
    omega

/-- `p:q ↦ p:(p+q)` likewise. It routes through the reciprocal step: the
    expansion gains a leading zero, which is why this is the same fact as the
    one above and not a second one. -/
theorem cfNat_sum_add_left {p q : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) :
    (cfNat p (p + q)).sum = (cfNat p q).sum + 1 := by
  have hlt : p < p + q := by omega
  rw [cfNat_of_lt (Nat.pos_of_ne_zero hp) hlt]
  have h1 : (cfNat (q + p) p).sum = (cfNat q p).sum + 1 := cfNat_sum_add_right q hp
  have h2 : (cfNat q p).sum = (cfNat p q).sum :=
    cfNat_sum_swap (Nat.pos_of_ne_zero hq) (Nat.pos_of_ne_zero hp)
  rw [show p + q = q + p from Nat.add_comm p q]
  simp only [List.sum_cons, Nat.zero_add]
  rw [h1, h2]

/-- And `ℓ_CF` is **not** reciprocal-invariant, which is why Def 5.4 is stated
    with `d_SB` and could not have been stated with `ℓ_CF`. -/
theorem lCF_not_swap_invariant :
    lCF ⟨1, 2, by decide⟩ ≠ lCF ⟨2, 1, by decide⟩ := by decide

/-! ## Definition 5.4 — Endpoint contrast depth -/

open IPres in
/-- **Definition 5.4.** `T_end(A,B) = d_SB(ρ(A ⊗ B))`. An exact endpoint
    tension. It is not asserted to be a complete metric on history-bearing
    states, and Def 5.5 is the reason. -/
def Tend (A B : IPres) : ℕ := dSB (Pres.reduce (IPres.toPres (IPres.otimes A B)))

theorem reduce_p_pos {A : Pres} (h : 0 < A.p) : 0 < (Pres.reduce A).p :=
  Nat.div_pos (Nat.le_of_dvd h (Nat.gcd_dvd_left A.p A.q)) (gcd_pos A)

theorem reduce_q_pos {A : Pres} (h : 0 < A.q) : 0 < (Pres.reduce A).q :=
  Nat.div_pos (Nat.le_of_dvd h (Nat.gcd_dvd_right A.p A.q)) (gcd_pos A)

/-- **`T_end(A,A) = 0`.** `A ⊗ A = ab:ab` reduces to `1:1`, whose depth is the
    root's. -/
theorem Tend_self (A : IPres) : Tend A A = 0 := by
  unfold Tend
  rw [IPres.reduce_otimes_self A]
  decide

/-- **`T_end(A,B) = T_end(B,A)`.** The book's reason exactly: `B ⊗ A` is the
    inverse of `A ⊗ B` before any reduction, and reciprocal addresses have equal
    primitive depth. -/
theorem Tend_comm (A B : IPres) : Tend A B = Tend B A := by
  unfold Tend
  have hswap := IPres.otimes_swap A B
  have hp : (IPres.otimes A B).p = A.p * B.q := rfl
  have hq : (IPres.otimes A B).q = A.q * B.p := rfl
  refine (dSB_swap (A := Pres.reduce (IPres.toPres (IPres.otimes A B)))
    (B := Pres.reduce (IPres.toPres (IPres.otimes B A)))
    (reduce_p_pos (IPres.otimes A B).p_pos)
    (reduce_q_pos (IPres.otimes A B).q_pos) ?_ ?_)
  · change (IPres.otimes B A).p / Nat.gcd (IPres.otimes B A).p (IPres.otimes B A).q
      = (IPres.otimes A B).q / Nat.gcd (IPres.otimes A B).p (IPres.otimes A B).q
    rw [hswap]
    change (IPres.otimes A B).q / Nat.gcd (IPres.otimes A B).q (IPres.otimes A B).p = _
    rw [Nat.gcd_comm]
  · change (IPres.otimes B A).q / Nat.gcd (IPres.otimes B A).p (IPres.otimes B A).q
      = (IPres.otimes A B).p / Nat.gcd (IPres.otimes A B).p (IPres.otimes A B).q
    rw [hswap]
    change (IPres.otimes A B).p / Nat.gcd (IPres.otimes A B).q (IPres.otimes A B).p = _
    rw [Nat.gcd_comm]

/-! ### Definition 5.5's hedge, settled

  `Tend_self` and `Tend_comm` above are two of the four metric axioms.
  Def 5.4's own comment declines to call `T_end` a metric and points at Def 5.5
  for the reason. The missing axiom is the triangle inequality, and it is not
  merely unproved: it is false, at the smallest components there are.

  The witness is the reciprocal pair around the root. `A = 1:2` and `C = 2:1`
  are each one step from `B = 1:1`, and `T_end` reads them three apart, because
  `T_end(A,B)` is the Stern-Brocot depth of the reduced value quotient and
  depth is not subadditive under multiplication of rationals: the quotient
  `(A/B)·(B/C)` composes two depth-1 addresses into a depth-3 one.

  This is what stops `T_end` being read as a distance. It is an exact contact
  quantity — an endpoint tension, which is what Def 5.4 calls it — and a
  metric on the same fabric has to be built as a path count through the
  relations tension licenses, not read off the tension itself. -/

/-- **`T_end` violates the triangle inequality.** The exact witness:
    `A = 1:2`, `B = 1:1`, `C = 2:1`, where `T_end(A,C) = 3` and
    `T_end(A,B) = T_end(B,C) = 1`. -/
theorem Tend_not_triangle :
    ∃ A B C : IPres, Tend A B + Tend B C < Tend A C :=
  ⟨⟨1, 2, by decide, by decide⟩, ⟨1, 1, by decide, by decide⟩,
   ⟨2, 1, by decide, by decide⟩, by decide⟩

/-- The witness's three values, named, so the failure is legible and not just
    existentially asserted. -/
theorem Tend_witness_values :
    Tend ⟨1, 2, by decide, by decide⟩ ⟨1, 1, by decide, by decide⟩ = 1 ∧
    Tend ⟨1, 1, by decide, by decide⟩ ⟨2, 1, by decide, by decide⟩ = 1 ∧
    Tend ⟨1, 2, by decide, by decide⟩ ⟨2, 1, by decide, by decide⟩ = 3 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The failure is not an edge case.** A second witness sharing `A = 1:2`
    and `B = 1:1` with the first, with `C = 3:1` and excess 2, twice the first's:
    `T_end(A,C) = 5` against `T_end(A,B) + T_end(B,C) = 3`. -/
theorem Tend_not_triangle_again :
    Tend ⟨1, 2, by decide, by decide⟩ ⟨1, 1, by decide, by decide⟩ +
      Tend ⟨1, 1, by decide, by decide⟩ ⟨3, 1, by decide, by decide⟩ = 3 ∧
    Tend ⟨1, 2, by decide, by decide⟩ ⟨3, 1, by decide, by decide⟩ = 5 := by
  refine ⟨by decide, by decide⟩

/-! ### Definitions 5.1-5.3, restricted to the book's own domain

  The book states Def 5.1-5.3 for positive primitive ratios only —
  `{A : Pres | A.p > 0, A.q > 0, gcd A.p A.q = 1}` — but `cf`, `lCF` and `dSB`
  above are total on all of `Pres`, so they also answer on the boundary and on
  unreduced presentations, where the book asserts nothing. The totality is not
  harmless there: `cf (p:0) = [p]` and `dSB (p:0) = p - 1` invent a
  Stern-Brocot depth for an improper presentation out of an arbitrary
  numerator. `cfFuel`/`cfNat` stay total by design — they are the executable
  Euclidean helper, not the numbered definitions — and `cf`/`lCF`/`dSB` above
  are the total extensions of Definitions 5.1-5.3. The numbered definitions
  are restricted here, to `PPres`. -/

/-- **The domain of Definitions 5.1-5.3.** A positive presentation in lowest
    terms: `IPres`, Def 1.2's interior domain already built in §4, bundled with
    Def 1.5's `Primitive` witness. Not an invented restriction — `reduce`
    always lands here for every interior presentation (`ofInterior` below), so
    this is the book's own "reduced ratio," not a type built to make one
    theorem true. -/
structure PPres where
  toIPres : IPres
  prim : Primitive toIPres.toPres
deriving DecidableEq

/-! ### Definition 5.1's evaluator and canonical uniqueness

  `cf`/`PPres.cf` above emit the Euclidean coefficient list, and
  `cfNat_getLast?_ge_two` proves only its terminal condition. Definition 5.1
  claims more than that: the list is *the* canonical one, which needs an exact
  evaluator, the full legality invariant, exact componentwise reconstruction,
  and uniqueness against every other legal list with the same value. All four
  are below, over ℕ throughout — no `Real`, no `Float`, no approximate
  division, and the reconstruction is componentwise rather than proportional,
  so no rational projection enters the statement. -/


/-- Exact evaluation of a finite simple continued fraction.  The empty-list
    value is only a total executable extension; canonical lists are nonempty. -/
def evalCF : List ℕ → ℕ × ℕ
  | [] => (1, 0)
  | a :: tail =>
      let r := evalCF tail
      (a * r.1 + r.2, r.1)

/-- The positive tail of a canonical finite simple continued fraction.  Its
    last coefficient is at least two; all earlier coefficients are positive. -/
inductive CanonicalCFTail : List ℕ → Prop
  | singleton (a : ℕ) (h : 2 ≤ a) : CanonicalCFTail [a]
  | cons (a : ℕ) (h : 0 < a) {b : ℕ} {tail : List ℕ}
      (ht : CanonicalCFTail (b :: tail)) : CanonicalCFTail (a :: b :: tail)

/-- A legal canonical finite simple continued fraction: the initial coefficient
    may be zero; each later coefficient is positive; when present, the final
    coefficient is at least two. -/
inductive CanonicalCF : List ℕ → Prop
  | singleton (a : ℕ) : CanonicalCF [a]
  | cons (a : ℕ) {b : ℕ} {tail : List ℕ}
      (ht : CanonicalCFTail (b :: tail)) : CanonicalCF (a :: b :: tail)

theorem CanonicalCFTail.prepend {xs : List ℕ} (h : CanonicalCFTail xs)
    (a : ℕ) (ha : 0 < a) : CanonicalCFTail (a :: xs) := by
  cases h with
  | singleton z hz => exact .cons a ha (.singleton z hz)
  | cons z hz ht => exact .cons a ha (.cons z hz ht)

theorem CanonicalCF.ofTail {xs : List ℕ} (h : CanonicalCFTail xs) (a : ℕ) :
    CanonicalCF (a :: xs) := by
  cases h with
  | singleton z hz => exact .cons a (.singleton z hz)
  | cons z hz ht => exact .cons a (.cons z hz ht)

instance (xs : List ℕ) : Decidable (CanonicalCFTail xs) := by
  induction xs with
  | nil => exact isFalse (by intro h; cases h)
  | cons a tail ih =>
      cases tail with
      | nil =>
          exact if h : 2 ≤ a then isTrue (.singleton a h) else
            isFalse (by intro hc; cases hc; exact h ‹2 ≤ a›)
      | cons b tail =>
          exact if ha : 0 < a then
            if ht : CanonicalCFTail (b :: tail) then
              isTrue (.cons a ha ht)
            else isFalse (by intro hc; cases hc; exact ht ‹CanonicalCFTail (b :: tail)›)
          else isFalse (by intro hc; cases hc; exact ha ‹0 < a›)

instance (xs : List ℕ) : Decidable (CanonicalCF xs) := by
  induction xs with
  | nil => exact isFalse (by intro h; cases h)
  | cons a tail ih =>
      cases tail with
      | nil => exact isTrue (.singleton a)
      | cons b tail =>
          exact if ht : CanonicalCFTail (b :: tail) then
            isTrue (.cons a ht)
          else isFalse (by intro hc; cases hc; exact ht ‹CanonicalCFTail (b :: tail)›)

structure CanonicalTailFacts (xs : List ℕ) : Prop where
  denominator_pos : 0 < (evalCF xs).2
  denominator_lt_numerator : (evalCF xs).2 < (evalCF xs).1
  primitive : Nat.gcd (evalCF xs).1 (evalCF xs).2 = 1
  decoded : cfNat (evalCF xs).1 (evalCF xs).2 = xs

theorem CanonicalCFTail.facts {xs : List ℕ} (h : CanonicalCFTail xs) :
    CanonicalTailFacts xs := by
  induction h with
  | singleton a ha =>
      refine ⟨by simp [evalCF], by simp [evalCF]; omega, ?_, ?_⟩
      · simp [evalCF]
      · rw [show evalCF [a] = (a, 1) by simp [evalCF]]
        simpa using cfNat_of_dvd (p := a) (q := 1) (by decide) (Nat.mod_one a)
  | @cons a ha b tail ht ih =>
      rcases ih with ⟨hq, hqp, hprim, hdecode⟩
      let p := (evalCF (b :: tail)).1
      let q := (evalCF (b :: tail)).2
      have hp : 0 < p := by dsimp [p]; omega
      have hmod : (a * p + q) % p = q := by
        calc
          (a * p + q) % p = (q + p * a) % p := by rw [Nat.mul_comm, Nat.add_comm]
          _ = q % p := Nat.add_mul_mod_self_left q p a
          _ = q := Nat.mod_eq_of_lt hqp
      have hdiv : (a * p + q) / p = a := by
        calc
          (a * p + q) / p = (q + p * a) / p := by rw [Nat.mul_comm, Nat.add_comm]
          _ = q / p + a := Nat.add_mul_div_left q a hp
          _ = a := by rw [Nat.div_eq_of_lt hqp, Nat.zero_add]
      refine ⟨?_, ?_, ?_, ?_⟩
      · change 0 < p
        exact hp
      · change p < a * p + q
        calc
          p ≤ a * p := Nat.le_mul_of_pos_left p ha
          _ < a * p + q := Nat.lt_add_of_pos_right hq
      · change Nat.gcd (a * p + q) p = 1
        calc
          Nat.gcd (a * p + q) p = Nat.gcd p (a * p + q) := Nat.gcd_comm _ _
          _ = Nat.gcd ((a * p + q) % p) p := Nat.gcd_rec p (a * p + q)
          _ = Nat.gcd q p := by rw [hmod]
          _ = Nat.gcd p q := Nat.gcd_comm _ _
          _ = 1 := hprim
      · change cfNat (a * p + q) p = a :: b :: tail
        rw [cfNat_cons hp.ne' (by rw [hmod]; exact hq.ne'), hdiv, hmod, hdecode]

theorem CanonicalCF.decoded {xs : List ℕ} (h : CanonicalCF xs) :
    cfNat (evalCF xs).1 (evalCF xs).2 = xs := by
  cases h with
  | singleton a =>
      rw [show evalCF [a] = (a, 1) by simp [evalCF]]
      simpa using cfNat_of_dvd (p := a) (q := 1) (by decide) (Nat.mod_one a)
  | @cons a b tail ht =>
      rcases ht.facts with ⟨hq, hqp, _, hdecode⟩
      let p := (evalCF (b :: tail)).1
      let q := (evalCF (b :: tail)).2
      have hp : 0 < p := by dsimp [p]; omega
      have hmod : (a * p + q) % p = q := by
        calc
          (a * p + q) % p = (q + p * a) % p := by rw [Nat.mul_comm, Nat.add_comm]
          _ = q % p := Nat.add_mul_mod_self_left q p a
          _ = q := Nat.mod_eq_of_lt hqp
      have hdiv : (a * p + q) / p = a := by
        calc
          (a * p + q) / p = (q + p * a) / p := by rw [Nat.mul_comm, Nat.add_comm]
          _ = q / p + a := Nat.add_mul_div_left q a hp
          _ = a := by rw [Nat.div_eq_of_lt hqp, Nat.zero_add]
      change cfNat (a * p + q) p = a :: b :: tail
      rw [cfNat_cons hp.ne' (by rw [hmod]; exact hq.ne'), hdiv, hmod, hdecode]

/-- Euclid's expansion of a ratio strictly greater than one is exactly a
    canonical positive tail. -/
theorem CanonicalCFTail.ofCFNat : ∀ q p : ℕ, 0 < q → q < p → CanonicalCFTail (cfNat p q) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
      intro p hq hqp
      by_cases hmod : p % q = 0
      · rw [cfNat_of_dvd hq.ne' hmod]
        apply CanonicalCFTail.singleton
        have hdvd : q ∣ p := Nat.dvd_of_mod_eq_zero hmod
        have hk : p / q * q = p := Nat.div_mul_cancel hdvd
        rcases Nat.lt_or_ge (p / q) 2 with hsmall | hlarge
        · exfalso
          have hle : p / q * q ≤ 1 * q := Nat.mul_le_mul_right q (by omega)
          rw [Nat.one_mul, hk] at hle
          omega
        · exact hlarge
      · rw [cfNat_cons hq.ne' hmod]
        exact (ih (p % q) (Nat.mod_lt p hq) q (Nat.zero_lt_of_ne_zero hmod)
          (Nat.mod_lt p hq)).prepend (p / q) (Nat.div_pos (Nat.le_of_lt hqp) hq)

/-- The Euclidean coefficient list satisfies the complete canonical legality
    invariant, not only the final-coefficient fragment. -/
theorem cfNat_canonical {p q : ℕ} (hq : 0 < q) : CanonicalCF (cfNat p q) := by
  by_cases hmod : p % q = 0
  · rw [cfNat_of_dvd hq.ne' hmod]
    exact CanonicalCF.singleton _
  · rw [cfNat_cons hq.ne' hmod]
    exact CanonicalCF.ofTail (CanonicalCFTail.ofCFNat (p % q) q
      (Nat.zero_lt_of_ne_zero hmod) (Nat.mod_lt p hq)) _

/-- Evaluation is a left inverse of Euclidean expansion on positive primitive
    pairs.  The equality is componentwise, so no proportional quotient or
    rational projection enters the statement. -/
theorem evalCF_cfNat_eq : ∀ q p : ℕ, 0 < p → 0 < q → Nat.gcd p q = 1 →
    evalCF (cfNat p q) = (p, q) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
      intro p hp hq hprim
      by_cases hmod : p % q = 0
      · have hdvd : q ∣ p := Nat.dvd_of_mod_eq_zero hmod
        have hgcd : Nat.gcd p q = q := Nat.gcd_eq_right_iff_dvd.mpr hdvd
        have hq_one : q = 1 := by omega
        subst q
        rw [cfNat_of_dvd (by decide) (Nat.mod_one p)]
        simp [evalCF]
      · have hr_pos : 0 < p % q := Nat.zero_lt_of_ne_zero hmod
        have hr_lt : p % q < q := Nat.mod_lt p hq
        have hprim' : Nat.gcd q (p % q) = 1 := by
          calc
            Nat.gcd q (p % q) = Nat.gcd (p % q) q := Nat.gcd_comm _ _
            _ = Nat.gcd q p := (Nat.gcd_rec q p).symm
            _ = Nat.gcd p q := Nat.gcd_comm _ _
            _ = 1 := hprim
        have hrec := ih (p % q) hr_lt q hq hr_pos hprim'
        rw [cfNat_cons hq.ne' hmod]
        simp only [evalCF, hrec]
        apply Prod.ext
        · rw [Nat.mul_comm]
          exact Nat.div_add_mod p q
        · rfl

/-! #### The legality predicate is doing work

  Uniqueness is only worth stating if some other list evaluates to the same
  exact pair, and one always does: appending a final `1` to a list whose last
  coefficient is reduced by one gives the classic second expansion. `[3,7,15,1]`
  evaluates to exactly `355:113`, and `CanonicalCF` rejects it. Without these
  the uniqueness theorem could hold vacuously. -/

/-- The classic non-canonical competitor: same exact value, final coefficient 1. -/
theorem competitor_same_value : evalCF [3, 7, 15, 1] = (355, 113) := by decide

/-- And it is rejected, so `cf_unique` is not vacuous. -/
theorem competitor_is_illegal : ¬ CanonicalCF [3, 7, 15, 1] := by decide

/-- The emitted list is legal, so the predicate is not empty either. -/
theorem emitted_is_legal : CanonicalCF [3, 7, 16] := by decide

/-- A noninitial zero is rejected. -/
theorem zero_inside_illegal : ¬ CanonicalCF [1, 0, 2] := by decide

/-- The initial coefficient may be zero. `1:137` is the extreme low-alternation
    address `L^136`, a single uninterrupted run, and its canonical list is two
    entries long. -/
theorem cfNat_one_137 : cfNat 1 137 = [0, 137] := by decide
theorem canonical_one_137 : CanonicalCF [0, 137] := by decide
theorem evalCF_one_137 : evalCF [0, 137] = (1, 137) := by decide

/-- **The all-ones truncation of `[1;1,1,...]` is not canonical**, and this is
    the reading the legality predicate exists to catch. Every finite truncation
    ends in `1`, where `CanonicalCFTail` requires at least `2`. The value is a
    genuine consecutive Fibonacci pair either way, so the two lists below are a
    second competitor pair — and unlike `[3,7,15,1]` this one is not
    manufactured, it is the naive reading of the book's own notation for phi. -/
theorem ones_truncation_eval : evalCF [1, 1, 1, 1, 1] = (8, 5) := by decide
theorem ones_truncation_illegal : ¬ CanonicalCF [1, 1, 1, 1, 1] := by decide

/-- The canonical list for the same Fibonacci ratio ends in `2`, and it is what
    `cfNat` emits. The final entry moves at every stage and never settles, which
    is the walk-never-closes fact stated in coefficients rather than in `L`/`R`. -/
theorem fib_canonical_eval : evalCF [1, 1, 1, 2] = (8, 5) := by decide
theorem fib_canonical_legal : CanonicalCF [1, 1, 1, 2] := by decide
theorem cfNat_eight_five : cfNat 8 5 = [1, 1, 1, 2] := by decide
theorem cfNat_thirteen_eight : cfNat 13 8 = [1, 1, 1, 1, 2] := by decide


namespace PPres

/-- Every term of the restricted domain is a presentation. -/
def toPres (A : PPres) : Pres := A.toIPres.toPres

theorem toPres_p_pos (A : PPres) : 0 < A.toPres.p := A.toIPres.p_pos
theorem toPres_q_pos (A : PPres) : 0 < A.toPres.q := A.toIPres.q_pos

/-- **Definition 5.1**, on its own domain. -/
def cf (A : PPres) : List ℕ := Pres.cf A.toPres

/-- **Definition 5.2**, on its own domain. -/
def lCF (A : PPres) : ℕ := Pres.lCF A.toPres

/-- **Definition 5.3**, on its own domain. -/
def dSB (A : PPres) : ℕ := Pres.dSB A.toPres

/-- **The constructor.** Every interior presentation lifts to `PPres` by
    reduction, and the lift is exactly `reduce`: this is the sense in which
    the restricted domain is the book's domain and not a narrower invention. -/
def ofInterior (A : Pres) (h : A.Interior) : PPres :=
  ⟨⟨(reduce A).p, (reduce A).q, reduce_p_pos h.1, reduce_q_pos h.2⟩, reduce_primitive A⟩

/-- **What totality was hiding.** No `PPres` term has `toPres.q = 0` or
    `toPres.p = 0` — `toPres_p_pos`/`toPres_q_pos` above forbid it directly —
    so the boundary presentation `p:0` that `Pres.dSB` answers on is simply not
    askable of this type. The invented depth `p - 1` of `Pres.dSB (p:0)` cannot
    be reproduced here because there is no `A : PPres` to reproduce it on. -/
theorem toPres_not_boundary (A : PPres) : A.toPres.p ≠ 0 ∧ A.toPres.q ≠ 0 :=
  ⟨Nat.pos_iff_ne_zero.mp (toPres_p_pos A), Nat.pos_iff_ne_zero.mp (toPres_q_pos A)⟩

/-- The book's own anchor, on the restricted domain. -/
def oneOne : PPres := ⟨⟨1, 1, by decide, by decide⟩, by decide⟩

theorem dSB_one_one : dSB oneOne = 0 := by decide

/-- The book's own separating pair, `3:2` and `4:3` — both already positive
    and primitive, so the restriction changes nothing about either witness,
    only what the type admits beyond them. -/
def threeTwo : PPres := ⟨⟨3, 2, by decide, by decide⟩, by decide⟩
def fourThree : PPres := ⟨⟨4, 3, by decide, by decide⟩, by decide⟩

theorem cf_threeTwo : cf threeTwo = [1, 2] := by decide
theorem cf_fourThree : cf fourThree = [1, 3] := by decide

theorem lCF_ne_dSB_witness :
    lCF threeTwo = lCF fourThree ∧ dSB threeTwo ≠ dSB fourThree := by decide

/-! #### Definition 5.1's three book-facing theorems, on `PPres` -/

/-- Definition 5.1's coefficient legality, on the book's positive primitive
    domain. -/
theorem cf_canonical (A : PPres) : CanonicalCF (cf A) :=
  cfNat_canonical (toPres_q_pos A)

/-- Definition 5.1's exact value equation.  Evaluating the emitted coefficients
    reconstructs the presentation itself. -/
theorem evalCF_cf (A : PPres) : evalCF (cf A) = (A.toPres.p, A.toPres.q) :=
  evalCF_cfNat_eq A.toPres.q A.toPres.p (toPres_p_pos A) (toPres_q_pos A) A.prim

/-- Definition 5.1's canonical uniqueness.  Any legal coefficient list with
    the same exact presentation is the Euclidean list emitted by `cf`. -/
theorem cf_unique (A : PPres) (xs : List ℕ) (hlegal : CanonicalCF xs)
    (heval : evalCF xs = (A.toPres.p, A.toPres.q)) : xs = cf A := by
  have hdecoded := hlegal.decoded
  rw [heval] at hdecoded
  exact hdecoded.symm

/-- An executable round-trip witness independent of the earlier coefficient
    examples. -/
theorem evalCF_355_113 : evalCF (cfNat 355 113) = (355, 113) := by decide

def threeFiftyFiveOneThirteen : PPres :=
  ⟨⟨355, 113, by decide, by decide⟩, by decide⟩

theorem cf_threeFiftyFiveOneThirteen : cf threeFiftyFiveOneThirteen = [3, 7, 16] := by decide

/-- A concrete uniqueness harness: no second legal canonical list evaluates to
    the exact primitive presentation `355:113`. -/
theorem unique_355_113 (xs : List ℕ) (hlegal : CanonicalCF xs)
    (heval : evalCF xs = (355, 113)) : xs = [3, 7, 16] := by
  rw [← cf_threeFiftyFiveOneThirteen]
  exact cf_unique threeFiftyFiveOneThirteen xs hlegal heval

end PPres

end Pres

/-! ## Definition 5.5 — Walk distance -/

namespace Word

/-- The longest common prefix of two words. Purely combinatorial, computable,
    and it is the only thing in §5 that reads ancestry rather than endpoints. -/
def lcp : Word → Word → Word
  | [], _ => []
  | _, [] => []
  | a :: u, b :: v => if a = b then a :: lcp u v else []

/-- **`lcp u v` is a genuine prefix of `u`.** The witness `r` with
    `u = lcp u v ++ r` is what both the length bound and the separation lemma
    below reduce to, built once by explicit rewriting rather than through
    `simp`/`omega`, so that the lemma uses no `Classical.choice`: the
    mathematics needs none. -/
theorem lcp_prefix_left : ∀ u v : Word, ∃ r, u = lcp u v ++ r
  | [], v => ⟨[], rfl⟩
  | a :: u, [] => ⟨a :: u, rfl⟩
  | a :: u, b :: v => by
      by_cases h : a = b
      · obtain ⟨r, hr⟩ := lcp_prefix_left u v
        refine ⟨r, ?_⟩
        rw [show lcp (a :: u) (b :: v) = a :: lcp u v from if_pos h,
            List.cons_append, ← hr]
      · refine ⟨a :: u, ?_⟩
        rw [show lcp (a :: u) (b :: v) = [] from if_neg h, List.nil_append]

/-- The same fact on the right, by the same explicit-rewrite route. -/
theorem lcp_prefix_right : ∀ u v : Word, ∃ r, v = lcp u v ++ r
  | [], [] => ⟨[], rfl⟩
  | [], b :: v => ⟨b :: v, rfl⟩
  | a :: u, [] => ⟨[], rfl⟩
  | a :: u, b :: v => by
      by_cases h : a = b
      · obtain ⟨r, hr⟩ := lcp_prefix_right u v
        refine ⟨r, ?_⟩
        rw [show lcp (a :: u) (b :: v) = a :: lcp u v from if_pos h,
            List.cons_append, ← hr, h]
      · refine ⟨b :: v, ?_⟩
        rw [show lcp (a :: u) (b :: v) = [] from if_neg h, List.nil_append]

theorem lcp_length_le_left (u v : Word) : (lcp u v).length ≤ u.length := by
  obtain ⟨r, hr⟩ := lcp_prefix_left u v
  calc (lcp u v).length ≤ (lcp u v).length + r.length := Nat.le_add_right _ _
    _ = u.length := by rw [← List.length_append, ← hr]

theorem lcp_length_le_right (u v : Word) : (lcp u v).length ≤ v.length := by
  obtain ⟨r, hr⟩ := lcp_prefix_right u v
  calc (lcp u v).length ≤ (lcp u v).length + r.length := Nat.le_add_right _ _
    _ = v.length := by rw [← List.length_append, ← hr]

theorem lcp_comm : ∀ u v : Word, lcp u v = lcp v u
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: u, b :: v => by
      by_cases h : a = b
      · subst h; simp [lcp, lcp_comm u v]
      · simp [lcp, h, Ne.symm h]

theorem lcp_self : ∀ u : Word, lcp u u = u
  | [] => rfl
  | a :: u => by simp [lcp, lcp_self u]

/-- **Definition 5.5.** `d_walk(u,v) = |u| + |v| − 2|lcp(u,v)|`, the exact tree
    distance. The subtraction is total because the prefix is bounded by both
    lengths. -/
def dwalk (u v : Word) : ℕ := u.length + v.length - 2 * (lcp u v).length

theorem dwalk_self (u : Word) : dwalk u u = 0 := by
  simp [dwalk, lcp_self]
  omega

theorem dwalk_comm (u v : Word) : dwalk u v = dwalk v u := by
  simp [dwalk, lcp_comm u v]
  omega

/-- **Measured from the root, walk distance is word length.** The root half of
    the coupling with `T_end`; the endpoint half is
    `Frame.Tend_root_eq_length`. Rewritten by hand, no automation, so it uses no
    axioms. -/
theorem dwalk_root (w : Word) : dwalk [] w = w.length := by
  change [].length + w.length - 2 * ([] : Word).length = w.length
  rw [List.length_nil, Nat.zero_add, Nat.mul_zero, Nat.sub_zero]

/-- **`lcp` is ultrametric.** The shared prefix of the outer pair is at least
    as long as the shorter of the two shared prefixes through any third word —
    exactly the fact that makes `lcp` read a tree rather than an arbitrary
    pairing. Proved by the same three-way structural recursion `lcp` itself
    uses, not assumed. -/
theorem lcp_ultrametric :
    ∀ u v w : Word, min (lcp u v).length (lcp v w).length ≤ (lcp u w).length
  | [], _, _ => by simp [lcp]
  | _ :: _, [], _ => by simp [lcp]
  | _ :: _, _ :: _, [] => by simp [lcp]
  | a :: p, b :: q, c :: r => by
      by_cases hab : a = b
      · by_cases hbc : b = c
        · have hac : a = c := hab.trans hbc
          simp only [lcp, if_pos hab, if_pos hbc, if_pos hac, List.length_cons]
          have := lcp_ultrametric p q r
          omega
        · simp [lcp, hbc]
      · simp [lcp, hab]

/-- **`d_walk` satisfies the triangle inequality.** Where `T_end` fails this
    exactly (`Tend_not_triangle`), the word metric holds it because it is a
    genuine tree distance: `lcp_ultrametric` bounds the middle term below by
    the smaller of the two flanking prefixes, and the rest is arithmetic on
    lengths already bounded by `lcp_length_le_left`/`lcp_length_le_right`. -/
theorem dwalk_triangle (u v w : Word) :
    dwalk u w ≤ dwalk u v + dwalk v w := by
  have h1 := lcp_length_le_left u v
  have h2 := lcp_length_le_right u v
  have h3 := lcp_length_le_left v w
  have h4 := lcp_length_le_right v w
  have h5 := lcp_ultrametric u v w
  unfold dwalk
  omega

/-- **`d_walk` separates points.** Zero distance forces equal words, so the
    fourth metric axiom is not vacuous: `d_walk` cannot collapse two distinct
    addresses to coincidence the way `T_end` need not distinguish them. -/
theorem dwalk_eq_zero_iff (u v : Word) : dwalk u v = 0 ↔ u = v := by
  constructor
  · intro h
    obtain ⟨r1, hr1⟩ := lcp_prefix_left u v
    obtain ⟨r2, hr2⟩ := lcp_prefix_right u v
    have hu : u.length = (lcp u v).length + r1.length := by
      have := congrArg List.length hr1
      rwa [List.length_append] at this
    have hv : v.length = (lcp u v).length + r2.length := by
      have := congrArg List.length hr2
      rwa [List.length_append] at this
    have hsum : u.length + v.length ≤ 2 * (lcp u v).length := by
      unfold dwalk at h; omega
    have hr1z : r1.length = 0 := by omega
    have hr2z : r2.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp hr1z, List.append_nil] at hr1
    rw [List.length_eq_zero_iff.mp hr2z, List.append_nil] at hr2
    exact hr1.trans hr2.symm
  · intro h; subst h; exact dwalk_self u

/-- **`d_walk` is a metric on `Word`, packaged.** All four axioms, none
    declared: identity (`dwalk_self`), symmetry (`dwalk_comm`), separation
    (`dwalk_eq_zero_iff`), and the triangle inequality (`dwalk_triangle`),
    every one a theorem about the tree already built rather than a field
    asserted of a new structure. This is what `T_end` (`Tend_not_triangle`)
    is not: a distance derived
    from the relations the walk already licenses, with no new primitive. -/
theorem dwalk_is_metric :
    (∀ u : Word, dwalk u u = 0) ∧
    (∀ u v : Word, dwalk u v = dwalk v u) ∧
    (∀ u v : Word, dwalk u v = 0 ↔ u = v) ∧
    (∀ u v w : Word, dwalk u w ≤ dwalk u v + dwalk v w) :=
  ⟨dwalk_self, dwalk_comm, dwalk_eq_zero_iff, dwalk_triangle⟩

end Word

namespace Pres

/-! ### `T_end` and `d_walk` answer different questions, both ways

  Def 5.5 says `d_walk` retains ancestry an endpoint contrast may discard. Read
  alone that is compatible with `d_walk` refining `T_end`. It does not: on pairs
  of addressed relations neither is a function of the other, and each of the two
  witnesses below is one direction of that.

  The candidates are addressed relations `r(w)` of Def 3.5, so both coordinates
  are being read off the same objects, and they are coupled there: measured from
  the root, both are the length of the word. That coupling is proved for every
  word at `Frame.root_coupling`. -/

/-- An interior presentation from its two positive coordinates, which is what `⊗`
    needs. The two witnesses below state their pairs as literals so the kernel
    decides them; that the literals are the addressed relations `r(ε)`, `r(L)`,
    `r(LL)`, `r(LLL)` is proved in `Frame` (`addressedIPres_nil` to
    `addressedIPres_LLL`), where `r_pos` builds `r(w)` as an `IPres`, and the
    witnesses are restated there on `r(w)` itself (`Frame.Tend_eq_dwalk_ne_addressed`,
    `Frame.dwalk_eq_Tend_ne_addressed`). -/
def ip (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : IPres := ⟨a, b, ha, hb⟩

/-- **Equal endpoint contrast, unequal walk distance.**
    `r(ε) = 1:1`, `r(L) = 1:2`, `r(LLL) = 1:4`. Both contrasts have
    `T_end = 1`; the walk distances are `1` and `2`. Ancestry survives in the
    second coordinate and is gone from the first. The literals are proved to be
    these addressed relations at `Frame.addressedIPres_nil`, `_L`, `_LLL`. -/
theorem Tend_eq_dwalk_ne :
    Tend (ip 1 1 (by decide) (by decide)) (ip 1 2 (by decide) (by decide))
      = Tend (ip 1 2 (by decide) (by decide)) (ip 1 4 (by decide) (by decide))
    ∧ Word.dwalk [] [false] ≠ Word.dwalk [false] [false, false, false] := by
  decide

/-- **Equal walk distance, unequal endpoint contrast.** The other direction, so
    neither coordinate refines the other.
    `r(L) = 1:2`, `r(LL) = 1:3`; both pairs sit at walk distance `1`, and the
    endpoint contrasts are `1` and `2`. The literals are proved to be these
    addressed relations at `Frame.addressedIPres_nil`, `_L`, `_LL`. -/
theorem dwalk_eq_Tend_ne :
    Word.dwalk [] [false] = Word.dwalk [false] [false, false]
    ∧ Tend (ip 1 1 (by decide) (by decide)) (ip 1 2 (by decide) (by decide))
      ≠ Tend (ip 1 2 (by decide) (by decide)) (ip 1 3 (by decide) (by decide)) := by
  decide

/-! ## Definition 5.6 — Tension signature -/

/-- **Definition 5.6.** The ordered tension signature of a candidate against an
    active family. The full signature is primary: it records which contrast
    belongs to which active relation. -/
def tensionSignature (r : IPres) (fam : List IPres) : List ℕ :=
  fam.map (fun rᵢ => Tend r rᵢ)

@[simp] theorem tensionSignature_length (r : IPres) (fam : List IPres) :
    (tensionSignature r fam).length = fam.length := by
  simp [tensionSignature]

/-- **The ordering is load-bearing.** Two candidates against one active family
    whose signatures are permutations of each other and are not equal. Any
    permutation-invariant summary, such as a sorted or multiset summary,
    identifies these two candidates; the ordered signature separates them. -/
theorem tensionSignature_order_matters :
    tensionSignature (ip 1 1 (by decide) (by decide))
        [ip 1 1 (by decide) (by decide), ip 1 2 (by decide) (by decide)] = [0, 1]
    ∧ tensionSignature (ip 1 2 (by decide) (by decide))
        [ip 1 1 (by decide) (by decide), ip 1 2 (by decide) (by decide)] = [1, 0] := by
  decide

/-- **The signature does not separate candidates.** `1:2` and `2:1` are
    distinct presentations, and against the family `[1:1]` they produce the
    identical tension signature: `Tend_comm` reads `T_end(2:1,1:1)` as
    `T_end(1:1,2:1)`, and that value already equals `T_end(1:2,1:1)`
    (`Tend_witness_values`). The ordered signature is primary over any scalar
    summary — that is Def 5.6's own point, and Def 5.9's coherence degeneracy
    is stated against it — but primary is not injective: distinct candidates
    can still fill every coordinate the same way. -/
theorem tensionSignature_not_injective :
    ip 1 2 (by decide) (by decide) ≠ ip 2 1 (by decide) (by decide)
    ∧ tensionSignature (ip 1 2 (by decide) (by decide))
        [ip 1 1 (by decide) (by decide)]
      = tensionSignature (ip 2 1 (by decide) (by decide))
        [ip 1 1 (by decide) (by decide)] := by
  decide

end Pres

/-! ## The prize: `d_SB(r(w)) = |w|`

  Definition 5.3 defines depth arithmetically, from the continued fraction.
  Definition 3.5 addresses a relation by a word of `L`/`R` refinements. That
  these two integers coincide is the statement that ties the two coordinate
  systems of Elements I together, and it is the theorem §5 is really for.

  **Proved in general** at `dSB_addressed_eq_length` below. The
  finite check to length six is kept beneath it because it *executes*, where the
  general theorem is one the kernel can only be convinced of.

  The proof does not need the run-length correspondence (decompose a word into
  alternating runs, then show `G` of that decomposition carries the
  continued-fraction convergents as its columns). Prepending a letter
  left-multiplies the word matrix by a generator; a generator adds one row to the
  other; the addressed relation is the column sum. So one letter at the front of
  the word is exactly one subtractive Euclidean step on the address, and that
  step adds exactly one to `∑ aᵢ`. The induction runs from the front and never
  decomposes anything. -/

namespace Frame

/-- All words of a given length, oldest letter first. -/
def allWords : ℕ → List Word
  | 0 => [[]]
  | n + 1 => (allWords n).flatMap fun w => [w ++ [false], w ++ [true]]

theorem allWords_length : ∀ n, ∀ w ∈ allWords n, w.length = n := by
  intro n
  induction n with
  | zero =>
      intro w hw
      simp only [allWords, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw; rfl
  | succ n ih =>
      intro w hw
      simp only [allWords, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      obtain ⟨u, hu, hw⟩ := hw
      rcases hw with h | h <;> subst h <;> simp [ih u hu]

/-- …and it enumerates *every* word of that length, so the finite check below is
    a check over all of them and not over a sample. -/
theorem mem_allWords : ∀ w : Word, w ∈ allWords w.length := by
  intro w
  induction w using List.reverseRecOn with
  | nil => simp [allWords]
  | append_singleton u b ih =>
      simp only [List.length_append, List.length_cons, List.length_nil, allWords,
        List.mem_flatMap, List.mem_cons]
      exact ⟨u, ih, by cases b <;> simp⟩

/-- **`d_SB(r(w)) = |w|` for every word of length at most six.** Exact, finite,
    and kernel-checked: 127 words, no exception. Kept because it executes: it is
    the statement one can watch the kernel evaluate, where the general theorem
    below is one it can only be convinced of. -/
theorem dSB_addressed_eq_length_le_six :
    ((List.range 7).flatMap allWords).all
      (fun w => decide (Pres.dSB (r w) = w.length)) = true := by
  decide

/-! ### Prepending a letter, entry by entry

  The route to the general theorem. Run-length decomposition is not needed. **One subtractive Euclid
  step on the addressed relation is exactly deleting the first letter of the
  word**, so the induction runs from the front and the arithmetic step is a
  single Euclidean division.

  The reason is `G_cons`: prepending a letter *left*-multiplies by a generator,
  and a generator adds one row of the matrix to the other. The addressed relation
  is the column sum, so adding a row to the other row adds one component of the
  address to the other. That is the definition of a subtractive step. -/

/-- The addressed relation, read off the word matrix: it is the column sum. -/
theorem r_eq_colsum (w : Word) :
    ((r w).p : ℤ) = (Word.G w).a + (Word.G w).b ∧
    ((r w).q : ℤ) = (Word.G w).c + (Word.G w).d := by
  have h := toMat2_walk_empty w
  have ha := congrArg Mat2.a h
  have hb := congrArg Mat2.b h
  have hc := congrArg Mat2.c h
  have hd := congrArg Mat2.d h
  simp only [toMat2] at ha hb hc hd
  refine ⟨?_, ?_⟩
  · change ((Pres.mediant (walk empty w).plus (walk empty w).minus).p : ℤ) = _
    rw [mediant_p]; push_cast; rw [ha, hb]
  · change ((Pres.mediant (walk empty w).plus (walk empty w).minus).q : ℤ) = _
    rw [mediant_q]; push_cast; rw [hc, hd]

/-- Prepending `L` fixes the numerator and adds it to the denominator. -/
theorem r_cons_false (w : Word) :
    (r (false :: w)).p = (r w).p ∧ (r (false :: w)).q = (r w).p + (r w).q := by
  obtain ⟨h1, h2⟩ := r_eq_colsum w
  obtain ⟨k1, k2⟩ := r_eq_colsum (false :: w)
  rw [G_cons_false] at k1 k2
  simp only at k1 k2
  constructor
  · have : ((r (false :: w)).p : ℤ) = ((r w).p : ℤ) := by rw [k1, h1]
    exact_mod_cast this
  · have : ((r (false :: w)).q : ℤ) = ((r w).p : ℤ) + ((r w).q : ℤ) := by
      rw [k2, h1, h2]; ring
    exact_mod_cast this

/-- Prepending `R` fixes the denominator and adds it to the numerator. -/
theorem r_cons_true (w : Word) :
    (r (true :: w)).p = (r w).p + (r w).q ∧ (r (true :: w)).q = (r w).q := by
  obtain ⟨h1, h2⟩ := r_eq_colsum w
  obtain ⟨k1, k2⟩ := r_eq_colsum (true :: w)
  rw [G_cons_true] at k1 k2
  simp only at k1 k2
  constructor
  · have : ((r (true :: w)).p : ℤ) = ((r w).p : ℤ) + ((r w).q : ℤ) := by
      rw [k1, h1, h2]; ring
    exact_mod_cast this
  · have : ((r (true :: w)).q : ℤ) = ((r w).q : ℤ) := by rw [k2, h2]
    exact_mod_cast this

/-- Every addressed relation on the tree is a genuine positive ratio. Needed
    because the Euclidean lemmas below are false at zero. -/
theorem r_pos (w : Word) : 0 < (r w).p ∧ 0 < (r w).q := by
  induction w with
  | nil => exact ⟨Nat.one_pos, Nat.one_pos⟩
  | cons b v ih =>
      obtain ⟨hp, hq⟩ := ih
      cases b
      · obtain ⟨h1, h2⟩ := r_cons_false v
        exact ⟨by omega, by omega⟩
      · obtain ⟨h1, h2⟩ := r_cons_true v
        exact ⟨by omega, by omega⟩

/-! ### The prize, closed -/

/-- The Stern-Brocot sum along a walk is the number of letters, plus one. -/
theorem cfSum_r (w : Word) : Pres.cfSum (r w) = w.length + 1 := by
  induction w with
  | nil => decide
  | cons b v ih =>
      obtain ⟨hp, hq⟩ := r_pos v
      have hiv : (Pres.cfNat (r v).p (r v).q).sum = v.length + 1 := ih
      cases b
      · obtain ⟨k1, k2⟩ := r_cons_false v
        change (Pres.cfNat (r (false :: v)).p (r (false :: v)).q).sum = _
        rw [k1, k2, Pres.cfNat_sum_add_left (by omega) (by omega), hiv]
        simp [List.length_cons]
      · obtain ⟨k1, k2⟩ := r_cons_true v
        change (Pres.cfNat (r (true :: v)).p (r (true :: v)).q).sum = _
        rw [k1, k2, Pres.cfNat_sum_add_right (r v).p (by omega), hiv]
        simp [List.length_cons]

/-- **`d_SB(r(w)) = |w|`, in general.**

    The arithmetic depth of Definition 5.3 and the walk length of Definition 3.5
    are the same integer, for every word, without bound. **The two coordinate
    systems of Elements I are one object.**

    Run-length decomposition is not needed and no matrix factorisation is
    either. Prepending
    a letter *left*-multiplies the word matrix by a generator (`G_cons`), a
    generator adds one row of that matrix to the other, and the addressed
    relation is the column sum — so prepending a letter adds one component of the
    address to the other. That is precisely one subtractive Euclidean step, which
    adds exactly one to the continued-fraction sum. The induction therefore runs
    from the front of the word and each step is a single Euclidean division.

    One trap is avoided rather than solved: the
    subtractive descent on the number pair really does *not* follow the
    Stern-Brocot parent, and `2:3 ↦ 2:1` while `2:3`'s parent is `1:2`. It never
    has to. Only the count is claimed, and the count is what a letter costs. -/
theorem dSB_addressed_eq_length (w : Word) : Pres.dSB (r w) = w.length := by
  unfold Pres.dSB
  rw [cfSum_r]
  omega

/-- The same statement as the book writes it: depth counts letters. -/
theorem depth_is_walk_length (w : Word) : Pres.dSB (Frame.addressed empty w) = w.length :=
  dSB_addressed_eq_length w

/-- **Measured from the root, endpoint contrast is word length.** Against the
    root `1:1`, `⊗` turns `r(w) = p:q` into `q:p`; that is already reduced
    because `r(w)` is primitive, and reciprocal depth is depth, which is `|w|`. -/
theorem Tend_root_eq_length (w : Word) :
    Pres.Tend (Pres.ip 1 1 Nat.one_pos Nat.one_pos)
      (Pres.ip (r w).p (r w).q (r_pos w).1 (r_pos w).2) = w.length := by
  have hg : Nat.gcd (1 * (r w).q) (1 * (r w).p) = 1 := by
    rw [Nat.one_mul, Nat.one_mul, Nat.gcd_comm]; exact r_primitive w
  have hp : (r w).p = (Pres.reduce (IPres.toPres (IPres.otimes
      (Pres.ip 1 1 Nat.one_pos Nat.one_pos)
      (Pres.ip (r w).p (r w).q (r_pos w).1 (r_pos w).2)))).q := by
    change _ = 1 * (r w).p / Nat.gcd (1 * (r w).q) (1 * (r w).p)
    rw [hg, Nat.div_one, Nat.one_mul]
  have hq : (r w).q = (Pres.reduce (IPres.toPres (IPres.otimes
      (Pres.ip 1 1 Nat.one_pos Nat.one_pos)
      (Pres.ip (r w).p (r w).q (r_pos w).1 (r_pos w).2)))).p := by
    change _ = 1 * (r w).q / Nat.gcd (1 * (r w).q) (1 * (r w).p)
    rw [hg, Nat.div_one, Nat.one_mul]
  unfold Pres.Tend
  rw [← Pres.dSB_swap (r_pos w).1 (r_pos w).2 hq.symm hp.symm]
  exact dSB_addressed_eq_length w

/-- **Definition 5.5, the coupling that does hold.** `Tend_eq_dwalk_ne`
    and `dwalk_eq_Tend_ne` (on `r(w)` itself: `Tend_eq_dwalk_ne_addressed`,
    `dwalk_eq_Tend_ne_addressed`, below) show neither quantity determines the other on pairs
    of addressed relations. From the root they agree: both are the length of the
    word, for every word. -/
theorem root_coupling (w : Word) :
    Word.dwalk [] w = w.length ∧
    Pres.Tend (Pres.ip 1 1 Nat.one_pos Nat.one_pos)
      (Pres.ip (r w).p (r w).q (r_pos w).1 (r_pos w).2) = w.length :=
  ⟨Word.dwalk_root w, Tend_root_eq_length w⟩


/-! ### The Def 5.5 witnesses on the addressed relations themselves -/

/-- `r(w)` as an interior presentation: every addressed relation has both
    coordinates positive (`r_pos`). -/
def addressedIPres (w : Word) : IPres :=
  Pres.ip (r w).p (r w).q (r_pos w).1 (r_pos w).2

/-- `r(ε) = 1:1`. -/
theorem addressedIPres_nil :
    addressedIPres [] = Pres.ip 1 1 (by decide) (by decide) := by decide

/-- `r(L) = 1:2`. -/
theorem addressedIPres_L :
    addressedIPres [false] = Pres.ip 1 2 (by decide) (by decide) := by decide

/-- `r(LL) = 1:3`. -/
theorem addressedIPres_LL :
    addressedIPres [false, false] = Pres.ip 1 3 (by decide) (by decide) := by decide

/-- `r(LLL) = 1:4`. -/
theorem addressedIPres_LLL :
    addressedIPres [false, false, false] = Pres.ip 1 4 (by decide) (by decide) := by
  decide

/-- **Equal endpoint contrast, unequal walk distance, on `r(w)`.** The pairs
    `(r(ε), r(L))` and `(r(L), r(LLL))` have the same `T_end`; the words have
    walk distances `1` and `2`. `Pres.Tend_eq_dwalk_ne` with its literals
    identified as these addressed relations. -/
theorem Tend_eq_dwalk_ne_addressed :
    Pres.Tend (addressedIPres []) (addressedIPres [false])
      = Pres.Tend (addressedIPres [false]) (addressedIPres [false, false, false])
    ∧ Word.dwalk [] [false] ≠ Word.dwalk [false] [false, false, false] := by
  rw [addressedIPres_nil, addressedIPres_L, addressedIPres_LLL]
  exact Pres.Tend_eq_dwalk_ne

/-- **Equal walk distance, unequal endpoint contrast, on `r(w)`.** The pairs
    `(r(ε), r(L))` and `(r(L), r(LL))` are both at walk distance `1`; their
    `T_end` differ. `Pres.dwalk_eq_Tend_ne` with its literals identified. -/
theorem dwalk_eq_Tend_ne_addressed :
    Word.dwalk [] [false] = Word.dwalk [false] [false, false]
    ∧ Pres.Tend (addressedIPres []) (addressedIPres [false])
      ≠ Pres.Tend (addressedIPres [false]) (addressedIPres [false, false]) := by
  rw [addressedIPres_nil, addressedIPres_L, addressedIPres_LL]
  exact Pres.dwalk_eq_Tend_ne

end Frame

end RatioSpace
