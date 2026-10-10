/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S08.Coherence
/-!
  Elements II §9 — Admission, reception channels, winding, and lift coherence.

  Sixteen items. The section that separates four decisions the framework is
  forever at risk of collapsing into one: is this occurrence admitted, in which
  channel phase, with what winding, on which lift sheet. Cor 9.16 exists to say
  none of the four supplies another.

  **The gap this section found, and it was upstream.** Prop 9.2 is *"Neg(Q) = 0 ⟺
  Q ∈ ℳ₊"*, and the book calls it a *"Derived result from the imported
  positive-decoding theorem."* Elements I's Lean had one direction of that
  import, `nonneg_G`, and not the other: its own ledger row for Standard Result
  3.1 said, in as many words, **"No decoder."** So the whole admission layer of
  Elements II was resting on a converse nobody had built.

  It was found here, as `mem_Mplus_of_nonneg`, and the argument is short once
  the right dichotomy is seen: for a nonnegative determinant-one matrix other
  than the identity, the two rows are comparable. If they were not — say
  `a > c` and `d > b` — then `det ≥ b + c + 1`, forcing `b = c = 0` and hence
  `M = I`. That is the whole obstruction, and `decFuel`'s case split was
  already written to exploit it; nothing had proved it could not get stuck.

  **Migrated to Elements I, 2026-08-26.** `RatioSpace.rows_comparable` and
  `RatioSpace.mem_Mplus_of_nonneg` now live in `Walk.lean` beside `dec`, where
  the gap actually was; this file imports them by name. Correction 21 closed.
-/

namespace RatioSpace
namespace Two

open Pres Word Mat2

/-- Iterated left multiplication, since `Mat2` carries no `Monoid.npow`. -/
def matPow (M : Mat2) : ℕ → Mat2
  | 0 => 1
  | n + 1 => M * matPow M n

/-- The central sign, written out because `Mat2` carries no `Neg`. -/
def matNeg (M : Mat2) : Mat2 := ⟨-M.a, -M.b, -M.c, -M.d⟩

/-! ## The missing import: nonnegative and determinant one implies decodable

    **Migrated to Elements I, 2026-08-26 (correction 21 closed).** This file's
    own docstring said the theorem belonged in `Walk.lean` beside `dec`, since
    the gap was Standard Result 3.1's, not Prop 9.2's. `RatioSpace.Nonneg`,
    `RatioSpace.rows_comparable`, `RatioSpace.row_ne_zero_of_det`, and
    `RatioSpace.mem_Mplus_of_nonneg` now live there, unchanged, and are visible
    here by name through the enclosing `RatioSpace` namespace. -/

/-! ## Definition 9.1 — oriented negativity load -/

/-- **Definition 9.1.** `Neg(Q) = Σ max(0, −q_ij)`, a nonnegative integer
    recording whether the oriented matrix contains a negative entry.

    *"It is an admission certificate, not the endpoint support tension of
    Section 7."* Two integers attached to the same occurrence, measuring
    different things; §7's `tEnd` is about a pair of relations, this is about one
    matrix. -/
def negLoad (Q : Mat2) : ℤ :=
  max 0 (-Q.a) + max 0 (-Q.b) + max 0 (-Q.c) + max 0 (-Q.d)

@[simp] theorem negLoad_nonneg (Q : Mat2) : 0 ≤ negLoad Q := by
  unfold negLoad
  have := le_max_left (0 : ℤ) (-Q.a)
  have := le_max_left (0 : ℤ) (-Q.b)
  have := le_max_left (0 : ℤ) (-Q.c)
  have := le_max_left (0 : ℤ) (-Q.d)
  omega

/-- `max 0 (−x) = 0` exactly when `0 ≤ x`. Proved from `Int.max_eq_left` and `le_max_right`
    (2026-09-22) so that nothing here reaches `Classical.choice`. -/
theorem max_zero_neg_eq_zero_iff (x : ℤ) : max 0 (-x) = 0 ↔ 0 ≤ x := by
  constructor
  · intro h; have := le_max_right (0 : ℤ) (-x); omega
  · intro h; exact Int.max_eq_left (by omega)

/-- The load vanishes exactly on nonnegative matrices, which is the arithmetic
    half of Prop 9.2 and is worth having separately because §9 uses it twice. -/
theorem negLoad_zero_iff_nonneg (Q : Mat2) : negLoad Q = 0 ↔ Nonneg Q := by
  unfold negLoad Nonneg
  have h1 := max_zero_neg_eq_zero_iff Q.a
  have h2 := max_zero_neg_eq_zero_iff Q.b
  have h3 := max_zero_neg_eq_zero_iff Q.c
  have h4 := max_zero_neg_eq_zero_iff Q.d
  have l1 := le_max_left (0 : ℤ) (-Q.a)
  have l2 := le_max_left (0 : ℤ) (-Q.b)
  have l3 := le_max_left (0 : ℤ) (-Q.c)
  have l4 := le_max_left (0 : ℤ) (-Q.d)
  constructor
  · intro h; exact ⟨h1.mp (by omega), h2.mp (by omega), h3.mp (by omega), h4.mp (by omega)⟩
  · rintro ⟨ha, hb, hc, hd⟩; rw [h1.mpr ha, h2.mpr hb, h3.mpr hc, h4.mpr hd]; rfl

/-! ## Proposition 9.2 — direct positive admission -/

/-- **Proposition 9.2.** `Neg(Q) = 0 ⟺ Q ∈ ℳ₊`, for `Q` of determinant one.

    Both directions now exist: the easy one is Elements I's `nonneg_G`, the hard
    one is `mem_Mplus_of_nonneg`, migrated to Elements I's `Walk.lean` on
    2026-08-26 (correction 21). -/
theorem direct_admission {Q : Mat2} (hd : Q.det = 1) :
    negLoad Q = 0 ↔ Q ∈ Mplus := by
  rw [negLoad_zero_iff_nonneg]
  constructor
  · intro h; exact mem_Mplus_of_nonneg (sizeM Q) Q le_rfl h hd
  · rintro ⟨w, rfl⟩; exact nonneg_G w

/-! ## Definition 9.3 — projective positive-cone defect -/

/-- `n₊(Q)`, the count of strictly positive entries. Zeros count for neither. -/
def posCount (Q : Mat2) : ℕ :=
  (if 0 < Q.a then 1 else 0) + (if 0 < Q.b then 1 else 0)
    + (if 0 < Q.c then 1 else 0) + (if 0 < Q.d then 1 else 0)

/-- `n₋(Q)`, the count of strictly negative entries. -/
def negCount (Q : Mat2) : ℕ :=
  (if Q.a < 0 then 1 else 0) + (if Q.b < 0 then 1 else 0)
    + (if Q.c < 0 then 1 else 0) + (if Q.d < 0 then 1 else 0)

/-- **Definition 9.3.** `d₊(Q) = min(n₊, n₋)`, the projective positive-cone
    defect. -/
def coneDefect (Q : Mat2) : ℕ := min (posCount Q) (negCount Q)

/-- **And unlike `Neg`, it is invariant under `Q ↦ −Q`**, which is the whole
    reason the book defines a second certificate rather than reusing the first:
    `Neg` sees the lift, `d₊` sees only the projective class. -/
theorem coneDefect_neg (Q : Mat2) : coneDefect (matNeg Q) = coneDefect Q := by
  unfold coneDefect posCount negCount matNeg
  simp only [neg_pos, neg_lt_zero]
  exact Nat.min_comm _ _

/-- `Neg`, by contrast, is *not* invariant under the central sign, so the two
    certificates genuinely differ. `L` has load zero and `−L` does not. -/
theorem negLoad_not_projective : negLoad L ≠ negLoad (matNeg L) := by decide

/-! ## Definitions 9.4 to 9.6 — finite reception channels -/

/-- The admitted phase set `J_G(Q) = {j : G^j Q ∈ ℳ₊}`, over a declared finite
    order `k`. Phases are carried as a list over `Fin k` so the status below can
    be read off its length. Membership in `ℳ₊` is decided by positive decoding
    (`mem_Mplus_iff_dec`); at determinant one it agrees with `Neg = 0`
    (`direct_admission`), and at determinant `−1` it is the book's set: `P` has
    `Neg(P) = 0` and is not in `ℳ₊` (2026-10-09, revision run list item 2; the
    filter was `negLoad (matPow C j.val * Q) = 0` until then). -/
def admittedPhases (C : Mat2) (k : ℕ) (Q : Mat2) : List (Fin k) :=
  (List.finRange k).filter (fun j => decide (matPow C j.val * Q ∈ Mplus))

/-- **Regression, Definition 9.4 at determinant `−1`.** With channel `P`, order
    two and `Q = 1`: phase `0` is `1 ∈ ℳ₊`, phase `1` is `P ∉ ℳ₊`, so the admitted
    set is `[0]` and the status is resolved at phase `0`. The former `Neg`-filter
    returned `[0, 1]` here. -/
theorem admittedPhases_P_two_one : admittedPhases P 2 1 = [0] := by decide

theorem negLoad_P_zero_not_Mplus : negLoad P = 0 ∧ P ∉ Mplus :=
  ⟨by decide, P_not_mem_Mplus⟩

/-- **Definition 9.4's exact status**, three cases and no fourth. `no-admission`
    and `unresolved multiple` are *outputs*, not failures to be repaired. -/
inductive ChanStatus (k : ℕ) where
  | noAdmission : ChanStatus k
  | resolved : Fin k → ChanStatus k
  | unresolvedMultiple : ChanStatus k
deriving DecidableEq

def chanStatus (C : Mat2) (k : ℕ) (Q : Mat2) : ChanStatus k :=
  match admittedPhases C k Q with
  | [] => ChanStatus.noAdmission
  | [j] => ChanStatus.resolved j
  | _ => ChanStatus.unresolvedMultiple

/-- **Definition 9.5.** A finite channel is positive-cone separating when
    distinct phases never both admit. Stated directly on the phase set, which is
    the form Prop 9.6 uses. -/
def Separating (C : Mat2) (k : ℕ) : Prop :=
  ∀ (Q : Mat2), Q.det = 1 → ∀ i j : Fin k,
    Nonneg (matPow C i.val * Q) → Nonneg (matPow C j.val * Q) → i = j

/-- **Proposition 9.6.** In a separating channel at most one phase is admitted.
    The book's proof, unchanged: two distinct admitted phases would put `Q` in
    two disjoint preimages of the positive cone. -/
theorem phases_le_one {C : Mat2} {k : ℕ} (hsep : Separating C k)
    {Q : Mat2} (hd : Q.det = 1) :
    (admittedPhases C k Q).length ≤ 1 := by
  rcases hl : admittedPhases C k Q with _ | ⟨i, rest⟩
  · simp
  · rcases rest with _ | ⟨j, rest'⟩
    · simp
    · exfalso
      have hnd : (admittedPhases C k Q).Nodup :=
        (List.nodup_finRange k).filter _
      rw [hl] at hnd
      have hij : i ≠ j := by
        intro h; exact (List.nodup_cons.mp hnd).1 (by simp [h])
      have hmem : ∀ x ∈ admittedPhases C k Q,
          Nonneg (matPow C x.val * Q) := by
        intro x hx
        have := List.of_mem_filter hx
        obtain ⟨w, hw⟩ := of_decide_eq_true this
        rw [← hw]; exact nonneg_G w
      exact hij (hsep Q hd i j (hmem i (by rw [hl]; simp))
        (hmem j (by rw [hl]; simp)))

/-! ## Theorem 9.7 — quarter-turn separation -/

/-- The modular quarter turn `S = [[0,−1],[1,0]]`, with `S² = −I` and `S⁴ = I`. -/
def Squarter : Mat2 := ⟨0, -1, 1, 0⟩

theorem Squarter_sq : matPow Squarter 2 = matNeg 1 := by decide
theorem Squarter_four : matPow Squarter 4 = 1 := by decide

/-- The four left rotations of `Q`, written out. The book's row pairs
    `(r₁,r₂)`, `(−r₂,r₁)`, `(−r₁,−r₂)`, `(r₂,−r₁)`. -/
theorem rotations (Q : Mat2) :
    matPow Squarter 0 * Q = Q
    ∧ matPow Squarter 1 * Q = ⟨-Q.c, -Q.d, Q.a, Q.b⟩
    ∧ matPow Squarter 2 * Q = ⟨-Q.a, -Q.b, -Q.c, -Q.d⟩
    ∧ matPow Squarter 3 * Q = ⟨Q.c, Q.d, -Q.a, -Q.b⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · apply Mat2.ext' <;> simp [matPow, Squarter, Mat2.mul_def]

/-- **A row cannot be both componentwise nonnegative and componentwise
    nonpositive without vanishing.** The step the book's proof turns on. -/
theorem row_vanishes {x y : ℤ} (h1 : 0 ≤ x) (h2 : 0 ≤ y)
    (h3 : 0 ≤ -x) (h4 : 0 ≤ -y) : x = 0 ∧ y = 0 :=
  ⟨by omega, by omega⟩

/-- **Theorem 9.7.** The quarter turn is positive-cone separating, so at most
    one phase is ever admitted.

    The book's proof exactly: if two distinct rotations were both componentwise
    nonnegative, either a nonzero row would have to be both nonnegative and
    nonpositive, forcing it to vanish, or both rows would vanish. Either way
    `det Q = 0`, contradicting `det Q = 1`. -/
theorem quarter_turn_separating : Separating Squarter 4 := by
  intro Q hd i j hi hj
  have hrot := rotations Q
  have hdet : Q.a * Q.d - Q.b * Q.c = 1 := hd
  -- Every phase forces a sign pattern; two distinct ones force a zero row.
  -- 2026-09-22: the four phases by `rcases` on the `Fin 4` values (the overflow cases close by
  -- `omega`) in place of `fin_cases`, which reaches `Classical.choice` through `Fintype`.
  rcases i with ⟨_ | _ | _ | _ | i, hi'⟩ <;> rcases j with ⟨_ | _ | _ | _ | j, hj'⟩ <;>
    first
      | rfl
      | (exfalso; omega)
      | (exfalso
         simp only [hrot.1, hrot.2.1, hrot.2.2.1, hrot.2.2.2, Nonneg] at hi hj
         obtain ⟨ha1, hb1, hc1, hd1⟩ := hi
         obtain ⟨ha2, hb2, hc2, hd2⟩ := hj
         simp at ha1 hb1 hc1 hd1 ha2 hb2 hc2 hd2
         -- 2026-09-22: two distinct phases force a whole row to vanish, and a vanishing row
         -- makes the determinant zero; `omega` on the sign facts in place of `nlinarith`.
         first
           | (have e1 : Q.a = 0 := by omega
              have e2 : Q.b = 0 := by omega
              rw [e1, e2] at hdet; omega)
           | (have e1 : Q.c = 0 := by omega
              have e2 : Q.d = 0 := by omega
              rw [e1, e2] at hdet; omega))

/-! ## Definitions 9.8 and 9.9 — the decoded channel presentation and the receiver -/

/-- **Definition 9.8.** When exactly one phase is admitted, `W_G(Q) = G^{j_G}Q`
    lies in `ℳ₊`, `ω_G(Q)` is its positive decoding, and `λ_G(Q)` is the relation
    that word addresses.

    Returned as an `Option` over the phase together with the word, because
    *"the phase `j_G` remains part of the reception certificate."* Dropping `j`
    and keeping only `ω` would be exactly the substitution the definition
    forbids: `ω_G(Q)` is **not** an alternative word history for the unrotated
    `Q`. -/
def decodedChannel (C : Mat2) (k : ℕ) (Q : Mat2) : Option (Fin k × Word) :=
  match admittedPhases C k Q with
  | [j] => (dec (matPow C j.val * Q)).map (fun w => (j, w))
  | _ => none

/-- The channel-local relation, `λ_G(Q) = r(ω_G(Q))`, with the phase kept. -/
def channelRelation (C : Mat2) (k : ℕ) (Q : Mat2) : Option (Fin k × Pres) :=
  (decodedChannel C k Q).map (fun p => (p.1, Frame.r p.2))

/-- **The decoded word really is the rotated matrix**, so the certificate is
    checkable rather than declared: whatever `decodedChannel` returns, the phase
    and the word reconstruct `G^j Q` exactly. The phase is returned alongside
    because *"`ω_G(Q)` is not an alternative word history for the unrotated
    matrix `Q`"* — without `j` the word addresses a different matrix. -/
theorem decoded_reconstructs {C : Mat2} {k : ℕ} {Q : Mat2}
    {j : Fin k} {w : Word} (h : decodedChannel C k Q = some (j, w)) :
    matPow C j.val * Q = G w := by
  unfold decodedChannel at h
  split at h
  · rename_i i heq
    rcases hdec : dec (matPow C i.val * Q) with _ | v
    · rw [hdec] at h; simp at h
    · rw [hdec] at h
      have hpair : (i, v) = (j, w) := by
        simpa using h
      obtain ⟨hj, hw⟩ := Prod.mk.injEq i v j w ▸ hpair
      subst hj; subst hw
      exact (dec_sound hdec).symm
  · simp at h

/-- **Definition 9.9.** A receiver profile is `Λ = (G, I_Λ)`, and its reception
    operator has three exact outputs.

    `⊥` and `Unresolved` are **outputs**, not failures: *"No-admission and
    nonseparation are exact outputs. Neither is repaired by choosing the first
    channel phase."* The `Unresolved` branch therefore carries every admitted
    phase with its reading, rather than a selection. -/
inductive Reception (k : ℕ) (Y : Type) where
  | bot : Reception k Y
  | resolved : Fin k → Y → Reception k Y
  | unresolved : List (Fin k × Y) → Reception k Y

/-- The receiver profile: a channel and a declared exact retained-reading map on
    decoded positive words. -/
structure Profile (k : ℕ) (Y : Type) where
  chan : Mat2
  read : Word → Y

/-- `ℛ_Λ(Q)`, all three branches, with no branch allowed to borrow another's
    answer. -/
def Profile.receive {k : ℕ} {Y : Type} (Λ : Profile k Y) (Q : Mat2) :
    Reception k Y :=
  match admittedPhases Λ.chan k Q with
  | [] => Reception.bot
  | [j] =>
      match dec (matPow Λ.chan j.val * Q) with
      | some w => Reception.resolved j (Λ.read w)
      | none => Reception.bot
  | js =>
      Reception.unresolved (js.filterMap (fun j =>
        (dec (matPow Λ.chan j.val * Q)).map (fun w => (j, Λ.read w))))

/-- **No-admission is an output.** An empty phase set gives `⊥` and nothing
    else; there is no first-phase fallback anywhere in the definition. -/
theorem receive_bot {k : ℕ} {Y : Type} (Λ : Profile k Y) (Q : Mat2)
    (h : admittedPhases Λ.chan k Q = []) : Λ.receive Q = Reception.bot := by
  unfold Profile.receive
  rw [h]

/-! ## Base-Channel Rule 9.10 -/

/-- **Base-Channel Rule 9.10.** The base comparison family of §7 uses *direct*
    oriented admission, `Neg(Q_{O,y}) = 0`. A nontrivial finite channel is an
    additional reception record and does not replace the direct chart.

    Stated as the equality it licenses: §7's `reachable` and §9's direct
    admission are the same test, so nothing in the base kernel is reading a
    channel. -/
theorem base_kernel_is_direct {MO : Mat2} {y : ProposalRecord}
    (hd : (Q MO y.fullMatrix).det = 1) :
    reachable MO y = true ↔ negLoad (Q MO y.fullMatrix) = 0 := by
  unfold reachable
  rw [direct_admission hd, mem_Mplus_iff_dec]
  unfold localWord
  constructor <;> intro h <;> exact h

/-- **And the rule's boxed separation: one admitted phase of one occurrence does
    not give one surviving occurrence.**

    Channel resolution ranges over phases of a single matrix; temporal support
    ranges over occurrences. Cor 8.11 already supplies the witness — a pair of
    admitted occurrences both survive — so a resolved channel phase is
    compatible with support of size two. The two resolutions are different
    questions and neither answers the other. -/
theorem phase_resolution_is_not_support_resolution (x y : IPres) :
    (support [x, y]).length = 2 := by
  rw [pair_support]
  rfl

/-! ## Definitions 9.11 to 9.12 — observer-relative winding -/

/-- **Definition 9.11.** `Ω(O,x) = b(w_x) − b(w_O)`, the observer-relative
    winding, an integer. -/
def winding (wO wx : Word) : ℤ := bal wx - bal wO

/-- **Additivity**, the book's second display: when `w_x = w_O a_x`, the relative
    winding is the winding of the local word alone. -/
theorem winding_suffix (wO a : Word) : winding wO (wO ++ a) = bal a := by
  unfold winding
  rw [bal_append]
  ring

/-- **The child rule**, `σ(L) = −1` and `σ(R) = +1`. Extending by one generator
    moves the winding by exactly one, in the direction of the side. -/
theorem winding_child (wO wx : Word) (g : Bool) :
    winding wO (wx ++ [g]) = winding wO wx + (if g then 1 else -1) := by
  -- 2026-09-22: through `bal_snoc` and `omega`; the earlier `simp [bal] <;> ring` reached
  -- `Classical.choice`.
  unfold winding
  rw [bal_snoc]
  omega

/-- **Proposition 9.12.** In the direct positive observer chart,
    `ψ₁₂(Q_{O,x}) ≡ Ω(O,x) (mod 12)`.

    Positive localization gives `Q_{O,x} = G(a_x)`, Elements I's closure theorem
    gives `ψ₁₂(G(a_x)) = ψ₁₂(a_x)`, and Def 9.11's additivity gives
    `b(a_x) = Ω(O,x)`. -/
theorem closure_is_winding_mod_twelve (A : Closure12) (wO a : Word) :
    A.psi (Q (G wO) (G (wO ++ a))) = ((winding wO (wO ++ a) : ℤ) : ZMod 12) := by
  rw [encounter_of_suffix, A.map_G, winding_suffix]
  rfl

/-- **Four different records, and the book says so.** The integer winding, its
    residue mod twelve, the channel phase and the complete relative matrix are
    not interchangeable: the residue loses the integer, witnessed by two words
    whose windings differ by twelve. -/
theorem residue_loses_the_integer :
    winding [] (List.replicate 12 true) ≠ winding [] []
      ∧ ((winding [] (List.replicate 12 true) : ℤ) : ZMod 12)
        = ((winding [] [] : ℤ) : ZMod 12) := by
  constructor
  · decide
  · decide

/-! ## Definitions 9.13 to 9.15 — projective class and the central lift -/

/-- **Definition 9.13.** The projective quotient identifies `Q` with `−Q`.
    Represented as the pair a reception can actually see: everything invariant
    under the central sign. `coneDefect` is one such invariant, by
    `coneDefect_neg`. -/
def projClass (Q : Mat2) : ℕ × ℕ := (coneDefect Q, coneDefect (matNeg Q))

@[simp] theorem projClass_neg (Q : Mat2) : projClass (matNeg Q) = projClass Q := by
  unfold projClass
  rw [coneDefect_neg]
  congr 1
  unfold matNeg coneDefect posCount negCount
  simp

/-- **Definition 9.13's lift record.** Relative to a declared representative,
    `Q = (−I)^ℓ Q̂` with `ℓ ∈ ℤ₂`. The bit is *relative to that declaration*:
    changing the representative changes the label, which is why it is carried
    rather than computed. -/
def liftBit (rep Q : Mat2) : Option Bool :=
  if Q = rep then some false else if Q = matNeg rep then some true else none

/-- Both sheets are labelled, and differently, so the bit is doing work. -/
theorem liftBit_of_rep (rep : Mat2) (h : rep ≠ matNeg rep) :
    liftBit rep rep = some false ∧ liftBit rep (matNeg rep) = some true := by
  unfold liftBit
  refine ⟨by simp, ?_⟩
  rw [if_neg (fun hEq => h hEq.symm), if_pos rfl]

/-- **Theorem 9.14.** No function of the projective class alone can distinguish
    `Q` from `−Q`.

    Stated the way it is used: any reading that factors through `projClass`
    agrees on the two sheets. The proof is one rewrite, and that is the point —
    the theorem is true by construction of the quotient, which is exactly why
    the book has to say it out loud rather than leave it implicit. -/
theorem projective_cannot_see_the_lift {Y : Type} (f : ℕ × ℕ → Y) (Q : Mat2) :
    f (projClass (matNeg Q)) = f (projClass Q) := by
  rw [projClass_neg]

/-- **And the lift bit genuinely separates them**, so 9.14 is a real
    obstruction rather than a statement about an empty distinction. -/
theorem lift_separates_what_projective_cannot :
    liftBit L L ≠ liftBit L (matNeg L)
      ∧ projClass (matNeg L) = projClass L := by
  refine ⟨by decide, projClass_neg L⟩

/-- **Definition 9.15.** The five-valued lift status. A singleton coherent-sheet
    set gives `determined ℓ`; empty and two-sheet sets give their own outputs;
    no declared predicate gives `notEvaluated`.

    Five constructors and not four: *"The projective positive-cone condition
    alone does not supply `χ_lift`."* `notEvaluated` is the status of an
    occurrence nobody asked the question about, and collapsing it into
    `unresolvedNone` would report an unasked question as a failed one. -/
inductive LiftStatus where
  | notEvaluated : LiftStatus
  | unresolvedNone : LiftStatus
  | unresolvedMultiple : LiftStatus
  | determined : Bool → LiftStatus
deriving DecidableEq

/-- The coherent-sheet set of a declared sign-sensitive predicate, read into the
    status. -/
def liftStatus (χ : Option (Bool → Bool)) : LiftStatus :=
  match χ with
  | none => LiftStatus.notEvaluated
  | some pred =>
      match pred false, pred true with
      | false, false => LiftStatus.unresolvedNone
      | true, false => LiftStatus.determined false
      | false, true => LiftStatus.determined true
      | true, true => LiftStatus.unresolvedMultiple

/-- **Not-evaluated is not unresolved-none.** The distinction the fifth
    constructor exists for. -/
theorem notEvaluated_ne_unresolvedNone :
    liftStatus none ≠ liftStatus (some (fun _ => false)) := by decide

/-! ## Corollary 9.16 — admission, support, and lift are separate decisions -/

/-- **Corollary 9.16.** *"An occurrence may be directly admitted but later
    coherence-rejected; channel-admitted with a resolved phase while temporal
    support remains multiple; projectively admitted while its central lift
    remains unresolved; or fully archived after admission refusal. No one of
    these statuses supplies another without its defining map."*

    Each separation is witnessed by an object already built rather than
    asserted:

    * a resolved channel phase alongside multiple surviving occurrences is
      `phase_resolution_is_not_support_resolution`;
    * a projective class that cannot see the lift is
      `lift_separates_what_projective_cannot`;
    * an unasked lift question distinct from a failed one is
      `notEvaluated_ne_unresolvedNone`;
    * and the two admission certificates differ at all is
      `negLoad_not_projective`.

    Collected here so the corollary is a theorem with four components rather
    than a paragraph. What the components prove is non-substitution: a lift bit
    and a negative load that differ where the projective class does not, two
    lift-status values that are distinct, and a support of two presentations, so
    no one of these statuses is computed from another's value. They are not
    uncoupled: all are decisions about the same occurrence, and the lift status
    is read from the same encounter the admission reads. The four separations are
    not the book's four clauses one for one. The name `statuses_are_independent`
    is kept for compatibility (gap G2-57). -/
theorem statuses_are_independent :
    (∃ x y : IPres, (support [x, y]).length = 2)
    ∧ (liftBit L L ≠ liftBit L (matNeg L) ∧ projClass (matNeg L) = projClass L)
    ∧ liftStatus none ≠ liftStatus (some (fun _ => false))
    ∧ negLoad L ≠ negLoad (matNeg L) := by
  refine ⟨?_, lift_separates_what_projective_cannot,
    notEvaluated_ne_unresolvedNone, negLoad_not_projective⟩
  exact ⟨⟨1, 1, by decide, by decide⟩, ⟨1, 2, by decide, by decide⟩,
    phase_resolution_is_not_support_resolution _ _⟩

end Two
end RatioSpace
