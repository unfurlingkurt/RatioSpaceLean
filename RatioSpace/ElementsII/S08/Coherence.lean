/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S07.Support
import RatioSpace.ElementsI.S05.Zphi
/-!
  Elements II §8 — Exact coherence, degeneracy, and retained signatures.

  Fourteen items: two definitions (8.1 carries the support law), a remark, and
  eleven derived results. It is the section where the support actually
  advances, so it is where the exactness discipline either holds or does not.

  **What is inherited.** Elements I §5 built `ℤ[φ]` as `Zphi`, the negative
  powers as `phiNegPow`, the coherence sum as `coherence`, and — the load-bearing
  one — a decidable linear order got by embedding into `ℤ√5`. Def 8.1's coherence value is
  `coherence` applied to §7's tension signature, Lemma 8.4 is `phiNegPow_eq`
  already proved, and Cor 8.7's *"no decimal approximation to φ is required"* is
  the existing `decidableLT` instance rather than a new claim. Elements I did the
  arithmetic; §8 does the selection.

  **What is new here.** Three things.

  Thm 8.5's two-integer certificate, `c₀` and `c₁` read off the tension
  histogram, which Elements I never needed because it never had to compare two
  coherence values by hand.

  Lemma 8.6's integer sign rule. Elements I's order is decidable through `ℤ√5`,
  which is a proof that a certificate exists; the book gives the certificate
  itself, `s = 2a + b` against `5b²`, and the reason it terminates is that
  `s² = 5b²` would make `√5` rational. That last step is proved here as
  `sq_eq_five_mul_sq_iff`, and it is what makes the tie test exact rather than
  merely decidable.

  Definition 8.1 as an `ArgMax` returning the *complete* maximizer set.
  *"No secondary comparison is performed after an exact tie."* A tie-break would
  be a second rule, so there is none, and Cor 8.12's minimum arity of three is
  the direct consequence: below three admitted occurrences the definition cannot
  reject anything.
-/

namespace RatioSpace
namespace Two

open Pres Word Zphi

/-! ## Definition 8.1 — exact global coherence -/

/-- The tension list of `y` against the family, keys dropped because the sum
    does not read them. Def 7.4's warning stands: this is a *derived* summary
    and the keyed signature it came from is the retained object. -/
def tensions (fam : List IPres) (y : IPres) : List ℕ :=
  fam.map (fun z => tEnd y z)

/-- **Definition 8.1.** `C_j^{(O)}(y) = Σ_{z ∈ A_{j+1}} φ^(−t_O(y,z))`.

    *"Each tagged occurrence contributes exactly once. If two distinct
    occurrences have the same observer-local value, both remain separate
    summands."* That is why the family is a `List` and not a `Finset`: the
    multiplicity is the point, and deduplicating here would be exactly the merge
    Cor 6.10 forbids. -/
def coherenceOf (fam : List IPres) (y : IPres) : Zphi :=
  coherence (tensions fam y)

/-- **The self-term is always 1**, because `t_O(y,y) = 0`. The book states this
    inside Def 8.1 and it is what makes Thm 8.10's `1 + φ^(−t)` come out. -/
@[simp] theorem self_term (y : IPres) : phiNegPow (tEnd y y) = 1 := by
  rw [tEnd_self]; rfl

/-- The coherence value of a two-element family, unfolded once, since three later results
    read it. -/
theorem coherenceOf_pair (x y z : IPres) :
    coherenceOf [x, y] z = phiNegPow (tEnd z x) + phiNegPow (tEnd z y) := by
  simp [coherenceOf, tensions, coherence]

/-! ## Definition 8.1 — global exact-coherence support -/

/-- **Definition 8.1.** `S_{j+1} = ArgMax_{y ∈ A_{j+1}} C_j^{(O)}(y)`,
    and `∅` when the admitted family is empty.

    `ArgMax` is *"the complete set of exact maximizers"*, so this is a filter and
    not a choice: nothing selects among tied maximizers, because
    *"no secondary comparison is performed after an exact tie."* It is decidable
    because Elements I's order on `ℤ[φ]` is, which is Cor 8.7. -/
def support (fam : List IPres) : List IPres :=
  fam.filter (fun y => fam.all (fun z => coherenceOf fam z ≤ coherenceOf fam y))

/-- Empty in, empty out — the second branch of the definition. -/
@[simp] theorem support_nil : support [] = [] := rfl

/-- **Remark 8.2, first half.** Support selection does not delete: every
    occurrence in the new support was already admitted, and the definition removes
    nothing from the archive. It updates active support and nothing else. -/
theorem support_sub {fam : List IPres} {y : IPres} (hy : y ∈ support fam) :
    y ∈ fam :=
  List.mem_of_mem_filter hy

/-- A member of the support beats everything admitted. -/
theorem support_maximal {fam : List IPres} {y : IPres} (hy : y ∈ support fam) :
    ∀ z ∈ fam, coherenceOf fam z ≤ coherenceOf fam y := by
  have h := List.of_mem_filter hy
  intro z hz
  exact of_decide_eq_true (List.all_eq_true.mp h z hz)

/-- **And the maximizer set is complete**, which is the half that makes ties
    survive: anything that ties with a maximizer is itself in the support. -/
theorem mem_support {fam : List IPres} {y : IPres} (hy : y ∈ fam)
    (hmax : ∀ z ∈ fam, coherenceOf fam z ≤ coherenceOf fam y) :
    y ∈ support fam := by
  refine List.mem_filter.mpr ⟨hy, ?_⟩
  exact List.all_eq_true.mpr (fun z hz => decide_eq_true (hmax z hz))

/-- **Theorem 17.7's sufficient-condition clause, connected to `support`
    here since it is a fact about Definition 8.1's filter and not
    about any one section's carrier.** *"One sufficient condition is that the
    actual terminal admitted family have one strict exact global maximizer."*
    A member `y` that strictly exceeds in coherence every other member of `fam` is in
    the support, and nothing else is — but Remark 8.2's own ties mean this
    forces the support down to `[y]` only when `y`'s own **value** does not
    repeat in `fam`. That is not an invented restriction: it is the same
    `Nodup` standing hypothesis §17's own `hArch`/`hAct`/`hselNodup` already
    carry, read at the level `support` operates on. -/
theorem support_singleton_of_strict_max {fam : List IPres} {y : IPres}
    (hnodup : fam.Nodup) (hy : y ∈ fam)
    (hstrict : ∀ z ∈ fam, z ≠ y → coherenceOf fam z < coherenceOf fam y) :
    support fam = [y] := by
  have hmem : y ∈ support fam :=
    mem_support hy (fun z hz => by
      by_cases hzy : z = y
      · exact hzy ▸ le_refl _
      · exact le_of_lt (hstrict z hz hzy))
  have honly : ∀ w ∈ support fam, w = y := by
    intro w hw
    by_contra hwy
    have h1 : coherenceOf fam y ≤ coherenceOf fam w := support_maximal hw y hy
    have h2 : coherenceOf fam w < coherenceOf fam y := hstrict w (support_sub hw) hwy
    exact absurd h1 (not_le_of_gt h2)
  have hsub : List.Sublist (support fam) fam := by unfold support; exact List.filter_sublist
  have hnodup' : (support fam).Nodup := hsub.nodup hnodup
  have hrep : support fam = List.replicate (support fam).length y :=
    List.eq_replicate_length.mpr honly
  have hlen1 : (support fam).length ≤ 1 := by
    have h := hrep ▸ hnodup'
    exact List.nodup_replicate.mp h
  have hlen0 : 0 < (support fam).length :=
    List.length_pos_iff_exists_mem.mpr ⟨y, hmem⟩
  have hlen : (support fam).length = 1 := by omega
  rw [hrep, hlen, List.replicate_one]

#print axioms support_singleton_of_strict_max

/-! ## Theorem 17.7, positive-horizon clause, at occurrence level

    The book (Elements II Theorem 17.7): for `h > 0`, `|S_h|_occ = 1` holds if
    and only if the terminal admitted family has one strict exact global
    maximizer, strict against every other admitted *occurrence*. The family is
    a list of occurrences, each read through its observer-local relation `loc`
    (`λ_O`, Definition 3.1); two distinct occurrences may share a relation and
    then tie, which is why strictness is against every other occurrence and
    not every other relation. `supportOcc` is Definition 8.1 on
    occurrences, and `mem_supportOcc_iff` ties it to the relation-level
    `support` through `support_maximal` and `mem_support`.

    The remark that the condition is not necessary at `h = 0` is not a
    statement about `supportOcc`: at `h = 0` the support `S_0` is the exact
    initialized support (Definition 4.7), no admission step has run, and no
    argmax produces it. This tree builds no `h = 0` terminal report
    (`Report.of` takes `0 < h`), so the remark has no Lean declaration. -/

/-- The Definition 8.1 coherence value of an occurrence in a family of
    occurrences: `C(y) = Σ_z φ^(−t(y,z))` over the observer-local relations. -/
def occCoherence {α : Type} (loc : α → IPres) (fam : List α) (y : α) : Zphi :=
  coherenceOf (fam.map loc) (loc y)

/-- **Definition 8.1 on occurrences.** The complete set of exact
    maximizers of `occCoherence`, a filter of the family; ties survive. -/
def supportOcc {α : Type} (loc : α → IPres) (fam : List α) : List α :=
  fam.filter (fun y => fam.all (fun z => occCoherence loc fam z ≤ occCoherence loc fam y))

/-- An occurrence is in the occurrence-level support exactly when it is
    admitted and its relation is in the relation-level `support` of the family's
    relations. Assembled from `support_maximal` and `mem_support`. -/
theorem mem_supportOcc_iff {α : Type} (loc : α → IPres) (fam : List α) (y : α) :
    y ∈ supportOcc loc fam ↔ y ∈ fam ∧ loc y ∈ support (fam.map loc) := by
  constructor
  · intro hy
    have hyf : y ∈ fam := List.mem_of_mem_filter hy
    have hall := List.of_mem_filter hy
    refine ⟨hyf, mem_support (List.mem_map_of_mem hyf) ?_⟩
    intro w hw
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
    exact of_decide_eq_true (List.all_eq_true.mp hall z hz)
  · rintro ⟨hyf, hys⟩
    refine List.mem_filter.mpr ⟨hyf, List.all_eq_true.mpr fun z hz => decide_eq_true ?_⟩
    exact support_maximal hys (loc z) (List.mem_map_of_mem hz)

set_option linter.unusedDecidableInType false in
/-- **Elements II Theorem 17.7, positive horizon.** For a family of distinct
    occurrences, the occurrence-level support has exactly one member if and only
    if some admitted occurrence strictly exceeds in coherence every other admitted
    occurrence. (`DecidableEq α` is the decidable identity of occurrences, which
    keeps the proof free of `Classical.choice`.) -/
theorem supportOcc_length_one_iff {α : Type} [DecidableEq α] (loc : α → IPres) (fam : List α)
    (hnodup : fam.Nodup) :
    (supportOcc loc fam).length = 1 ↔
      ∃ y ∈ fam, ∀ z ∈ fam, z ≠ y → occCoherence loc fam z < occCoherence loc fam y := by
  have hmax : ∀ {y}, y ∈ supportOcc loc fam → ∀ z ∈ fam,
      occCoherence loc fam z ≤ occCoherence loc fam y := by
    intro y hy z hz
    have hall := List.of_mem_filter hy
    exact of_decide_eq_true (List.all_eq_true.mp hall z hz)
  constructor
  · intro h
    obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp h
    have hyS : y ∈ supportOcc loc fam := by rw [hy]; simp
    refine ⟨y, List.mem_of_mem_filter hyS, fun z hz hzy => ?_⟩
    by_contra hnlt
    have hge : occCoherence loc fam y ≤ occCoherence loc fam z := not_lt.mp hnlt
    have hzS : z ∈ supportOcc loc fam :=
      List.mem_filter.mpr ⟨hz, List.all_eq_true.mpr fun w hw =>
        decide_eq_true (le_trans (hmax hyS w hw) hge)⟩
    rw [hy] at hzS
    exact hzy (List.mem_singleton.mp hzS)
  · rintro ⟨y, hyf, hstrict⟩
    have hyS : y ∈ supportOcc loc fam :=
      List.mem_filter.mpr ⟨hyf, List.all_eq_true.mpr fun z hz => decide_eq_true (by
        by_cases hzy : z = y
        · exact hzy ▸ le_refl _
        · exact le_of_lt (hstrict z hz hzy))⟩
    have honly : ∀ w ∈ supportOcc loc fam, w = y := by
      intro w hw
      by_contra hwy
      exact absurd (hmax hw y hyf) (not_le_of_gt (hstrict w (List.mem_of_mem_filter hw) hwy))
    have hnd : (supportOcc loc fam).Nodup := List.filter_sublist.nodup hnodup
    have hrep : supportOcc loc fam = List.replicate (supportOcc loc fam).length y :=
      List.eq_replicate_length.mpr honly
    have hle : (supportOcc loc fam).length ≤ 1 := by
      have h := hrep ▸ hnd
      exact List.nodup_replicate.mp h
    have hpos : 0 < (supportOcc loc fam).length := List.length_pos_iff_exists_mem.mpr ⟨y, hyS⟩
    omega

#print axioms supportOcc_length_one_iff

/-! ## Definition 8.3 and Lemma 8.4 — Fibonacci and the golden negative power -/

/-- **Definition 8.3.** `F₀ = 0`, `F₁ = 1`, `F_{n+1} = F_n + F_{n−1}`. This is
    `Nat.fib`, and the three defining equations are restated so §8 does not
    depend on a reader knowing that. -/
theorem fib_zero : Nat.fib 0 = 0 := rfl
theorem fib_one : Nat.fib 1 = 1 := rfl
theorem fib_rec (n : ℕ) : Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n :=
  (Nat.fib_add_two).trans (Nat.add_comm _ _)

/-- **Lemma 8.4.** `φ^(−n) = (−1)ⁿ(F_{n+1} − F_n φ)`.

    Elements I proved this as `phiNegPow_eq` for Def 5.8; it is restated in the
    book's own signed form so Thm 8.5 can read the coefficients off directly. -/
theorem golden_negative_power (n : ℕ) :
    phiNegPow n = ⟨(-1) ^ n * Nat.fib (n + 1), -((-1) ^ n * Nat.fib n)⟩ := by
  rw [phiNegPow_eq]
  congr 1
  ring

/-! ## Theorem 8.5 — the two-integer certificate -/

/-- `c₀ = Σ_t n_y(t)(−1)^t F_{t+1}`, summed over the tension list rather than
    over a histogram, which is the same number: the histogram counts each
    tension and the list repeats it. -/
def c0 (ts : List ℕ) : ℤ := (ts.map (fun t => (-1) ^ t * (Nat.fib (t + 1) : ℤ))).sum

/-- `c₁ = −Σ_t n_y(t)(−1)^t F_t`. -/
def c1 (ts : List ℕ) : ℤ := -(ts.map (fun t => (-1) ^ t * (Nat.fib t : ℤ))).sum

/-- **Theorem 8.5.** Every coherence value lies in `ℤ[φ]` and has a finite two-integer
    certificate `C = c₀ + c₁φ`.

    The book's proof is "substitute Lemma 8.4 into every summand and collect";
    here that is an induction on the tension list, and the finiteness the book
    invokes is the list being finite by construction. -/
theorem coherence_certificate (ts : List ℕ) :
    coherence ts = ⟨c0 ts, c1 ts⟩ := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
    rw [coherence_cons, ih, golden_negative_power]
    ext
    · simp [c0]
    · simp [c1]; ring

/-- The certificate of a coherence value, as the pair the comparison actually reads. -/
theorem coherenceOf_certificate (fam : List IPres) (y : IPres) :
    coherenceOf fam y = ⟨c0 (tensions fam y), c1 (tensions fam y)⟩ :=
  coherence_certificate _

/-! ## Lemma 8.6 — the exact sign of a coherence difference -/

/-- The book's substitution: `2(a + bφ) = (2a + b) + b√5`, so the sign question
    becomes a question about the integer pair `(s, b)` with `s = 2a + b`. -/
def signPair (x : Zphi) : ℤ × ℤ := (2 * x.a + x.b, x.b)

/-- `5 ∣ s·s` forces `5 ∣ s`: the five residues of `s` give `s·s ≡ 0, 1, 4, 4, 1 (mod 5)`.
    Proved by residues rather than through `Nat.Prime`, whose divisibility lemmas reach
    `Classical.choice` in this Mathlib (2026-09-22). -/
theorem five_dvd_of_five_dvd_mul_self (s : ℤ) (h : (s * s) % 5 = 0) : s % 5 = 0 := by
  have hm : (s * s) % 5 = ((s % 5) * (s % 5)) % 5 := Int.mul_emod s s 5
  have hr : s % 5 = 0 ∨ s % 5 = 1 ∨ s % 5 = 2 ∨ s % 5 = 3 ∨ s % 5 = 4 := by omega
  rcases hr with hr | hr | hr | hr | hr <;> rw [hr] at hm <;> omega

/-- **The step that makes Lemma 8.6 terminate.** *"Equality for nonzero `(s,b)`
    would make `√5` rational, so equality occurs only when `a = b = 0`."*

    Proved here in the integers, with no appeal to irrationality: `5` is not a
    perfect square, so `s² = 5b²` forces both to vanish by infinite descent on `|b|`
    (`s = 5s'`, `b = 5b'` after `5 ∣ s` and then `5 ∣ b`). 2026-09-22: the descent is done by
    residues mod 5 (`five_dvd_of_five_dvd_mul_self`), since Mathlib's `Zsqrtd.norm_eq_zero` and
    the `Nat.Prime` divisibility lemmas reach `Classical.choice`. -/
theorem sq_eq_five_mul_sq_iff {s b : ℤ} : s ^ 2 = 5 * b ^ 2 ↔ s = 0 ∧ b = 0 := by
  constructor
  · intro h
    have key : ∀ n : ℕ, ∀ s b : ℤ, b.natAbs = n → s * s = 5 * (b * b) → s = 0 ∧ b = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro s b hb hsb
        by_cases hb0 : b = 0
        · subst hb0
          have hs : s * s = 0 := by rw [hsb]; ring
          exact ⟨(Int.mul_eq_zero.mp hs).elim id id, rfl⟩
        · exfalso
          -- 5 ∣ s
          have h5s : s % 5 = 0 := by
            apply five_dvd_of_five_dvd_mul_self
            rw [hsb]; omega
          obtain ⟨s', hs'⟩ : ∃ s', s = 5 * s' := ⟨s / 5, by omega⟩
          -- then 25 s'² = 5 b², so 5 s'² = b², so 5 ∣ b
          have hb2 : b * b = 5 * (s' * s') := by
            rw [hs'] at hsb
            have : 25 * (s' * s') = 5 * (b * b) := by rw [← hsb]; ring
            omega
          have h5b : b % 5 = 0 := by
            apply five_dvd_of_five_dvd_mul_self
            rw [hb2]; omega
          obtain ⟨b', hb'⟩ : ∃ b', b = 5 * b' := ⟨b / 5, by omega⟩
          have hsb' : s' * s' = 5 * (b' * b') := by
            rw [hb'] at hb2
            have : 25 * (b' * b') = 5 * (s' * s') := by rw [← hb2]; ring
            omega
          have hne : b' ≠ 0 := fun e => hb0 (by rw [hb', e]; rfl)
          have hlt : b'.natAbs < n := by
            rw [← hb, hb', Int.natAbs_mul]
            have hpos : 0 < b'.natAbs := Int.natAbs_pos.mpr hne
            have h5 : (5 : ℤ).natAbs = 5 := rfl
            rw [h5]
            omega
          exact hne (ih b'.natAbs hlt s' b' rfl hsb').2
    have h' : s * s = 5 * (b * b) := by
      have := h; rw [pow_two, pow_two] at this; exact this
    exact key b.natAbs s b rfl h'
  · rintro ⟨rfl, rfl⟩; ring

/-- **Lemma 8.6, the decidable half.** The sign of a difference in `ℤ[φ]` is
    decided by integers alone. Elements I installed the order through `ℤ√5`; what
    is added here is that the decision needs no approximation to `φ` at any
    point, which is the sentence Cor 8.7 turns into a statement about the whole
    comparison. -/
example (x y : Zphi) : Decidable (x < y) := inferInstance

/-! ## Corollary 8.7 — exactness of support comparison -/

/-- **Corollary 8.7.** Every strict comparison, equality, maximizer and tie in
    Definition 8.1 has a finite integer certificate.

    Stated as what it operationally means: membership in the support is
    decidable, so the definition is an algorithm: it computes the maximizer set. No
    decimal approximation to `φ` appears anywhere in reaching it. -/
instance support_decidable (fam : List IPres) (y : IPres) :
    Decidable (y ∈ support fam) := inferInstance

/-- And equality of coherence values — the tie — is decided componentwise on the two
    integers of Thm 8.5. -/
theorem tie_is_integral (fam : List IPres) (y z : IPres) :
    coherenceOf fam y = coherenceOf fam z
      ↔ c0 (tensions fam y) = c0 (tensions fam z)
        ∧ c1 (tensions fam y) = c1 (tensions fam z) := by
  rw [coherenceOf_certificate, coherenceOf_certificate]
  constructor
  · intro h; exact ⟨congrArg Zphi.a h, congrArg Zphi.b h⟩
  · rintro ⟨h0, h1⟩; simp [h0, h1]

/-! ## Theorem 8.8 — finiteness and the one-tick growth bound -/

/-- The support never outgrows the family it selects from. -/
theorem support_length_le (fam : List IPres) :
    (support fam).length ≤ fam.length :=
  List.length_filter_le _ _

/-- **Theorem 8.8.** `|A_{j+1}| ≤ 2|S_j|` and `|S_{j+1}| ≤ 2|S_j|`.

    Cor 5.5 gives `|P_{j+1}| = 2|S_j|` exactly; admission can only remove, and
    an `ArgMax` set is a subset of what it ranges over. The proposal count enters
    as a hypothesis because §5 owns it, which keeps the two sections' obligations
    apart. -/
theorem growth_bound {S P A : List IPres}
    (hP : P.length = 2 * S.length)
    (hA : A.length ≤ P.length) :
    A.length ≤ 2 * S.length ∧ (support A).length ≤ 2 * S.length := by
  refine ⟨hP ▸ hA, ?_⟩
  exact le_trans (support_length_le A) (hP ▸ hA)

/-- **And empty support stays empty**, Definition 8.1's second branch carried one
    tick forward. -/
theorem empty_stays_empty : support ([] : List IPres) = [] := rfl

/-! ## Theorem 8.9 — enumeration independence -/

/-- The coherence value is a sum over the family, so a storage permutation cannot move it.
    *"Storage permutation changes no stable occurrence identifier, admission
    truth value, pairwise tension, or occurrence multiplicity."* -/
theorem coherenceOf_perm {fam fam' : List IPres} (h : fam.Perm fam') (y : IPres) :
    coherenceOf fam y = coherenceOf fam' y := by
  unfold coherenceOf tensions coherence
  exact List.Perm.sum_eq ((h.map _).map _)

/-- **Theorem 8.9.** Permuting the storage order does not change the active
    support. Membership is decided by the coherence value, and the coherence value is permutation
    invariant, so the maximizer set is the same set. -/
theorem support_perm_mem {fam fam' : List IPres} (h : fam.Perm fam') (y : IPres) :
    y ∈ support fam ↔ y ∈ support fam' := by
  constructor
  · intro hy
    exact mem_support (h.mem_iff.mp (support_sub hy))
      (fun z hz => by
        rw [← coherenceOf_perm h, ← coherenceOf_perm h]
        exact support_maximal hy z (h.mem_iff.mpr hz))
  · intro hy
    exact mem_support (h.mem_iff.mpr (support_sub hy))
      (fun z hz => by
        rw [coherenceOf_perm h, coherenceOf_perm h]
        exact support_maximal hy z (h.mem_iff.mp hz))

/-! ## Theorem 8.10 — exact two-occurrence degeneracy -/

/-- **Theorem 8.10.** If `A_{j+1} = {x, y}` then both coherence values equal
    `1 + φ^(−t_O(x,y))`.

    The book's proof runs through Lemma 7.7 to get `t_O(x,y) = t_O(y,x)`; §7
    already has that as `tEnd_comm`, inherited from Elements I's `Tend_comm`. Each
    coherence value is then one self-term of `1` and the same cross-term.

    *"The argument remains valid if `x` and `y` have equal local values, because
    their occurrence multiplicity is retained."* Nothing here assumes `x ≠ y`. -/
theorem two_occurrence_degeneracy (x y : IPres) :
    coherenceOf [x, y] x = 1 + phiNegPow (tEnd x y)
      ∧ coherenceOf [x, y] y = 1 + phiNegPow (tEnd x y) := by
  constructor
  · rw [coherenceOf_pair, tEnd_self]
    rfl
  · rw [coherenceOf_pair, tEnd_self, tEnd_comm y x]
    rw [add_comm]
    rfl

/-- The two coherence values are therefore equal, which is the fact Cor 8.11 needs. -/
theorem pair_coherence_equal (x y : IPres) :
    coherenceOf [x, y] x = coherenceOf [x, y] y := by
  rw [(two_occurrence_degeneracy x y).1, (two_occurrence_degeneracy x y).2]

/-! ## Corollaries 8.11 and 8.12 — what the definition cannot do -/

/-- **Corollary 8.11.** An unrestricted singleton advances to its sibling pair: if `S_j =
    {x}` and both children are admitted, `S_{j+1}` is both of them.

    **Remark 8.2's second half, made concrete.** Support may *expand* from a
    singleton, so a single active occurrence can advance to a pair, and terminal
    commitment is the coherent snap of Section 18, read from the terminal report. -/
theorem pair_support (x y : IPres) : support [x, y] = [x, y] := by
  have h := pair_coherence_equal x y
  simp [support, h]

/-- **Corollary 8.12.** Below three admitted occurrences the definition rejects
    nothing: empty gives empty, one gives that one, two gives both.

    So coherence rejection requires at least three admitted occurrences. That is
    a minimum arity for nontrivial comparative discrimination, and — the book is
    careful here — *not* a claim that every family of three or more is
    separated. -/
theorem support_singleton (x : IPres) : support [x] = [x] := by
  simp [support]

theorem rejection_needs_three {fam : List IPres} (h : fam.length < 3) :
    support fam = fam := by
  match fam, h with
  | [], _ => rfl
  | [x], _ => exact support_singleton x
  | [x, y], _ => exact pair_support x y

/-! ## Theorem 8.13 and Corollary 8.14 — covariance, and mirrored input -/

/-- The mirror is injective, because it is an involution. Needed to pull a
    membership back through `fam.map Inv`. -/
theorem Inv_inj {x y : IPres} (h : Inv x = Inv y) : x = y := by
  have := congrArg IPres.inv h
  simpa [IPres.inv_inv] using this

/-- Membership transports through the mirrored family. -/
theorem mem_map_Inv {fam : List IPres} {y : IPres} (h : Inv y ∈ fam.map Inv) :
    y ∈ fam := by
  obtain ⟨w, hw, hEq⟩ := List.mem_map.mp h
  exact Inv_inj hEq ▸ hw

/-- The coherence value survives a complete side exchange, because §7's Thm 7.8 preserves
    every pairwise tension and the coherence value is a function of those alone. -/
theorem coherenceOf_side_invariant (fam : List IPres) (y : IPres) :
    coherenceOf (fam.map Inv) (Inv y) = coherenceOf fam y := by
  unfold coherenceOf tensions
  congr 1
  simp [List.map_map, Function.comp_def, tEnd_side_invariant]

/-- **Theorem 8.13, side half.** The support is transported by the mirror,
    occurrence for occurrence: `Supp(𝖯 S) = 𝖯 Supp(S)`. -/
theorem support_side_covariant (fam : List IPres) (y : IPres) :
    Inv y ∈ support (fam.map Inv) ↔ y ∈ support fam := by
  constructor
  · intro hy
    refine mem_support ?_ ?_
    · exact mem_map_Inv (support_sub hy)
    · intro z hz
      rw [← coherenceOf_side_invariant fam z, ← coherenceOf_side_invariant fam y]
      exact support_maximal hy _ (List.mem_map_of_mem hz)
  · intro hy
    refine mem_support (List.mem_map_of_mem (support_sub hy)) ?_
    intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    rw [coherenceOf_side_invariant, coherenceOf_side_invariant]
    exact support_maximal hy w hw

/-- **Corollary 8.14.** A comparison family invariant under a fixed-point-free
    side exchange has a support that is a union of mirror pairs, and therefore
    cannot be an occurrence singleton.

    Stated as the operative half: a maximizer is accompanied by its mirror, so a
    symmetric input is never silently broken by the definition picking one side. -/
theorem mirror_accompanies {fam : List IPres} (hsym : (fam.map Inv).Perm fam)
    {y : IPres} (hy : y ∈ support fam) : Inv y ∈ support fam := by
  refine mem_support ?_ ?_
  · exact hsym.mem_iff.mp (List.mem_map_of_mem (f := Inv) (support_sub hy))
  · intro z hz
    have hInvY : coherenceOf fam (Inv y) = coherenceOf (fam.map Inv) (Inv y) :=
      (coherenceOf_perm hsym (Inv y)).symm
    rw [hInvY, coherenceOf_side_invariant]
    exact support_maximal hy z hz

end Two
end RatioSpace
