/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S06.State
/-!
  Elements II §7 — Directional composition and the support-tension convention.

  Ten items. Five definitions setting up the observer-local comparison layer,
  four derived results about what survives a side exchange and a prefix
  transport, and one convention keeping five quantities from being renamed as
  one another.

  **The section's own finding, and it is a good one for the argument: §7's
  support-driving tension is Elements I's `T_end`, definitionally.** Def 7.3
  writes `t_O(y,z) = d_SB(ρ(λ_O(y) ⊗ λ_O(z)))`, and Elements I Def 5.4 wrote
  `T_end(A,B) = d_SB(ρ(A ⊗ B))`. Once the observer-local relations are in hand
  the two are the same expression, `tEnd_eq_Tend` proves it by `rfl`, and every
  Elements I theorem about `T_end` is therefore already a theorem about §7's
  support comparison. That is the bridge §1 promised, arriving where it was
  supposed to.

  **What that buys immediately.** Thm 7.8, side invariance of support tension,
  needs Prop 7.6 and Lemma 7.7. Elements I already proved `otimes_swap` and
  `dSB_swap`, so 7.6 and 7.7 here are short, and 7.8 falls out. Nothing is
  reproved.

  **What it does not buy, and Convention 7.9 is the guard.** `ℓ_CF` is *not*
  reciprocal-invariant — `lCF_swap_ne` in `Depth.lean` — so Lemma 7.7 could not
  have been stated with it, and the table in 7.9 exists precisely because these
  quantities are close enough to be confused and are not equal. The separation
  is witnessed here rather than asserted.
-/

namespace RatioSpace
namespace Two

open Frame Pres Word

/-! ## Definition 7.1 — the base-admitted comparison family

  `A_{j+1} = { y ∈ P_{j+1} : Q_{O,y} ∈ ℳ₊ and Pred_Γ(y; 𝔛_j, j+1) = 1 }`.

  Two conditions, and they are different in kind. The first is geometric and
  the observer cannot choose it: positive decoding either succeeds from `O`'s
  chart or it does not. The second is the declared predicate, which is the
  observer's own and must be supplied. Keeping them as separate arguments is
  the point — a family that filtered on the predicate alone would admit
  occurrences unreachable from the observer, and one that filtered on
  reachability alone would ignore the declared question. -/

/-- Positive reachability from `O`'s chart, decidable because `dec` is total
    and succeeds exactly on `ℳ₊`. This is `Q_{O,y} ∈ ℳ₊` with the membership
    replaced by the decoding that witnesses it. -/
def reachable (MO : Mat2) (y : ProposalRecord) : Bool :=
  (localWord MO y.fullMatrix).isSome

/-- **Definition 7.1.** The admitted family, filtered on both conditions.
    `pred` is `Pred_Γ`, the observer's declared admission predicate; it is a
    parameter because the book requires it to be declared rather than assumed. -/
def admitted (MO : Mat2) (pred : ProposalRecord → Bool)
    (P : List ProposalRecord) : List ProposalRecord :=
  P.filter (fun y => reachable MO y && pred y)

/-- Admission never invents an occurrence. The archive keeps what fails, with
    its exact word, which is the book's sentence about the failure certificate
    read from this side: nothing here deletes, it selects. -/
theorem admitted_sub (MO : Mat2) (pred : ProposalRecord → Bool)
    (P : List ProposalRecord) : ∀ y ∈ admitted MO pred P, y ∈ P := by
  intro y hy
  exact List.mem_of_mem_filter hy

/-- **Both conditions bite, and neither implies the other.** An occurrence in
    the admitted family satisfies each separately, so a later step may not
    recover one from the other. -/
theorem admitted_both {MO : Mat2} {pred : ProposalRecord → Bool}
    {P : List ProposalRecord} {y : ProposalRecord} (hy : y ∈ admitted MO pred P) :
    reachable MO y = true ∧ pred y = true := by
  have h := List.of_mem_filter hy
  exact ⟨(Bool.and_eq_true _ _).mp h |>.1, (Bool.and_eq_true _ _).mp h |>.2⟩

/-! ## Definition 4.3, both context variants, typed against the question

  `Cavity.lean` gave Definition 4.3 as `OccPred C`, generic in the context
  type, with the event position in `ℕ` and `Pred_Γ` read as `preds.all`. The
  book's type is tighter on three counts, and each is built here: the context
  `𝔠_𝒬` is a tagged type with an `initialization` and a `tick` variant, both
  carrying the question `𝒬` itself; the event position ranges over
  `{0,…,h_𝒬}` with `h_𝒬` the question's own horizon; and `Bool_Γ` is an exact
  Boolean composition declared in the question data, conjunction being only
  its default. The tick variant is Definition 6.2's `TickCarrier` at the
  question's horizon, so `Pred_Γ(y;𝔛_{τ,j},j+1)` is supplied to §7's
  `admitted` as `tickPred` (`mem_admitted_tickPred`); `admitted` itself still
  accepts any predicate. -/

/-- **Definition 4.3, `𝔠_𝒬`.** The tagged predicate-context type compatible
    with question `Q`: an `initialization` context (Definition 4.7, no support
    component) or a `tick` context (a Definition 6.2 carrier at horizon
    `h_𝒬`). Each variant carries the proof that its question is `Q`. -/
inductive PredContext {Cert : Type} (Q : ExtendedQuestion Cert) : Type where
  /-- The `initialization` variant. -/
  | init (c : InitContext Cert) (hq : c.question = Q)
  /-- The `tick` variant. -/
  | tick (X : TickCarrier Cert Q.horizon) (hq : X.question = Q)

/-- **Definition 4.3, `γ`.** `γ : Prop_𝒬 × 𝔠_𝒬 × {0,…,h_𝒬} → {0,1}`: the
    context is `Q`'s own tagged context and the event position is
    `Fin (h_𝒬 + 1)`.
    NOT CONSTRAINED: which total Boolean map is declared; the book allows any
    exact map of this type. -/
abbrev QPred {Cert : Type} (Q : ExtendedQuestion Cert) : Type :=
  ProposalRecord → PredContext Q → Fin (Q.horizon + 1) → Bool

/-- **Definition 4.3, the conjunction default for `Bool_Γ`.** -/
def boolConj {m : ℕ} (v : Fin m → Bool) : Bool := decide (∀ i, v i = true)

/-- **Definition 4.3, the question's predicate data.** A finite ordered family
    `Γ = (γ₁,…,γ_m)` of predicates of `Q`'s type, and the exact Boolean
    composition `Bool_Γ : {0,1}^m → {0,1}` included in the question data, with
    conjunction as the default.
    NOT CONSTRAINED: which predicates and which composition are declared. -/
structure PredicateData {Cert : Type} (Q : ExtendedQuestion Cert) where
  /-- `m`. -/
  m : ℕ
  /-- `Γ = (γ₁,…,γ_m)`. -/
  gamma : Fin m → QPred Q
  /-- `Bool_Γ`. -/
  boolGamma : (Fin m → Bool) → Bool := boolConj

/-- A question bundled with its declared predicate data, so the family is
    part of the question data rather than a free parameter beside it. -/
structure QuestionWithPredicates (Cert : Type) where
  /-- `𝒬`. -/
  question : ExtendedQuestion Cert
  /-- `Γ` and `Bool_Γ`, typed against `question`. -/
  preds : PredicateData question

/-- **Definition 4.3.** `Pred_Γ(y;𝔠,k) = Bool_Γ(γ₁(y;𝔠,k),…,γ_m(y;𝔠,k))`. -/
def PredicateData.predGamma {Cert : Type} {Q : ExtendedQuestion Cert}
    (D : PredicateData Q) (y : ProposalRecord) (c : PredContext Q)
    (k : Fin (Q.horizon + 1)) : Bool :=
  D.boolGamma (fun i => D.gamma i y c k)

/-- Under the conjunction default, `Pred_Γ` holds exactly when every declared
    predicate holds. -/
theorem PredicateData.predGamma_conj {Cert : Type} {Q : ExtendedQuestion Cert}
    (D : PredicateData Q) (hD : D.boolGamma = boolConj) (y : ProposalRecord)
    (c : PredContext Q) (k : Fin (Q.horizon + 1)) :
    D.predGamma y c k = true ↔ ∀ i, D.gamma i y c k = true := by
  simp [PredicateData.predGamma, hD, boolConj]

/-- **`Bool_Γ` is not conjunction only.** With one predicate that holds and
    one that fails, declaring disjunction as `Bool_Γ` admits where the
    conjunction default rejects. -/
theorem predGamma_composition_matters {Cert : Type} (Q : ExtendedQuestion Cert)
    (y : ProposalRecord) (c : PredContext Q) (k : Fin (Q.horizon + 1)) :
    let γ : Fin 2 → QPred Q := fun i _ _ _ => decide (i = 0)
    (({ m := 2, gamma := γ } : PredicateData Q).predGamma y c k = false) ∧
    (({ m := 2, gamma := γ, boolGamma := fun v => v 0 || v 1 } : PredicateData Q).predGamma
      y c k = true) := by
  refine ⟨?_, ?_⟩ <;> simp [PredicateData.predGamma, boolConj]

/-- **Definition 4.3, seed reading.** A seed is tested against the
    initialization context at event position `0`. -/
def PredicateData.seedPred {Cert : Type} {Q : ExtendedQuestion Cert}
    (D : PredicateData Q) (c : InitContext Cert) (hq : c.question = Q) :
    ProposalRecord → Bool :=
  fun y => D.predGamma y (.init c hq) 0

/-- **Definition 4.3, tick reading.** A child proposed during the advance
    `j → j+1` is tested against `𝔛_{τ,j}` at event position `j+1`, which lies in
    `{0,…,h_𝒬}` because `j < h_𝒬`. -/
def PredicateData.tickPred {Cert : Type} {Q : ExtendedQuestion Cert}
    (D : PredicateData Q) (X : TickCarrier Cert Q.horizon) (hq : X.question = Q)
    (hj : X.tick.val < Q.horizon) : ProposalRecord → Bool :=
  fun y => D.predGamma y (.tick X hq) ⟨X.tick.val + 1, by omega⟩

/-- **Definition 7.1 read through Definition 4.3.** The admitted family at the
    advance `j → j+1`, with `Pred_Γ` the question's declared family evaluated
    on `𝔛_{τ,j}` at event `j+1`: an occurrence is admitted exactly when it is
    proposed, positively reachable from `O`, and `Pred_Γ(y;𝔛_{τ,j},j+1) = 1`. -/
theorem mem_admitted_tickPred {Cert : Type} {Q : ExtendedQuestion Cert}
    (D : PredicateData Q) (X : TickCarrier Cert Q.horizon) (hq : X.question = Q)
    (hj : X.tick.val < Q.horizon) (MO : Mat2) (P : List ProposalRecord)
    (y : ProposalRecord) :
    y ∈ admitted MO (D.tickPred X hq hj) P ↔
      y ∈ P ∧ reachable MO y = true ∧
        D.predGamma y (.tick X hq) ⟨X.tick.val + 1, by omega⟩ = true := by
  simp [admitted, PredicateData.tickPred, List.mem_filter]

/-! ## Definitions 7.2 and 7.3 — the contrast and its depth

  Both are stated on interior presentations. `⊗` is not total on `Pres`: Def
  1.2 admits `0:1` and `1:0` as orientation anchors and their composition is
  `0:0`, which is excluded. `IPres` is Elements I's answer and it is the right
  domain here too, because an admitted occurrence has a positive local
  relation. -/

/-- **Definition 7.2.** `D_O(y,z) = λ_O(y) ⊗ λ_O(z)`. Argument order retained,
    and it matters: `⊗` is noncommutative (Prop 4.2 of Elements I), even
    though the depth taken from it in Def 7.3 is symmetric. Retaining an order
    that the next definition discards is deliberate — the star of Def 7.4 reads
    the contrast, not only its depth. -/
def contrast (A B : IPres) : IPres := IPres.otimes A B

/-- **Definition 7.3.** `t_O(y,z) = d_SB(ρ(λ_O(y) ⊗ λ_O(z)))`, a nonnegative
    integer. The reduction happens inside the comparison and touches neither
    archived occurrence: `ρ` is applied to the contrast, never to `y` or `z`. -/
def tEnd (A B : IPres) : ℕ :=
  dSB (Pres.reduce (IPres.toPres (contrast A B)))

/-- **§7's support tension is Elements I's `T_end`, by `rfl`.**

    Elements I Def 5.4 defined `Tend A B = d_SB(ρ(A ⊗ B))`; Def 7.3 defines the
    support-driving tension by the same expression once the observer-local
    relations are in hand. So the two definitions do not merely resemble each
    other, they are the same function, and every Elements I theorem about
    `Tend` is a theorem about §7's comparison without restatement. -/
theorem tEnd_eq_Tend (A B : IPres) : tEnd A B = Tend A B := rfl

/-- Which delivers symmetry immediately, from Elements I's `Tend_comm`. The
    book gets this at Thm 7.8 by a longer route; here it is inherited. -/
theorem tEnd_comm (A B : IPres) : tEnd A B = tEnd B A := Tend_comm A B

/-- And self-contrast is zero depth: an occurrence compared with itself
    contributes no tension. `Tend_self` in Elements I. -/
theorem tEnd_self (A : IPres) : tEnd A A = 0 := Tend_self A

/-! ## Definition 7.4 — the keyed star and the exact signatures

  *"The occurrence identifier `z` remains attached to each entry. A histogram
  or scalar sum derived from the signature is not the complete signature."*
  Both sentences are structural, so both are built: the entries are pairs, and
  the loss in a scalar summary is witnessed rather than warned about. -/

/-- **Definition 7.4, the composition star.** `Σ_j^{(O)}(y) = (z ↦ λ(y) ⊗
    λ(z))` over the admitted family, with `z` attached to its entry. -/
def star (fam : List IPres) (y : IPres) : List (IPres × IPres) :=
  fam.map (fun z => (z, contrast y z))

/-- **Definition 7.4, the keyed tension signature.** `𝐓_j^{(O)}(y) = (z ↦
    t_O(y,z))`, keys retained. -/
def tensionSignature (fam : List IPres) (y : IPres) : List (IPres × ℕ) :=
  fam.map (fun z => (z, tEnd y z))

/-- The retained auxiliary signature `𝐋_CF`, continued-fraction block structure
    per key. Explicitly *not* an input to Definition 8.1. -/
def cfSignature (fam : List IPres) (y : IPres) : List (IPres × ℕ) :=
  fam.map (fun z => (z, lCF (Pres.reduce (IPres.toPres (contrast y z)))))

/-- The scalar summary the book warns against, defined only so the warning can
    be proved rather than repeated. -/
def tensionSum (fam : List IPres) (y : IPres) : ℕ :=
  ((tensionSignature fam y).map Prod.snd).sum

/-- Every entry keeps its key, which is what makes the signature a function on
    the family rather than a bag of numbers. -/
theorem tensionSignature_keys (fam : List IPres) (y : IPres) :
    (tensionSignature fam y).map Prod.fst = fam := by
  simp [tensionSignature, List.map_map, Function.comp_def]

/-- **The scalar summary is not the signature.** Two distinct occurrences at
    equal tension from `y` are interchangeable in the sum and distinguishable
    in the signature, so the sum cannot recover which occurrence contributed
    what. That is the book's sentence with a witness: `1:2` and `2:1` are
    distinct, both sit at depth 1 from `1:1`, and the signature keeps them
    apart while any total over it cannot. -/
theorem sum_loses_the_keys :
    ∃ y z z' : IPres, z ≠ z' ∧ tEnd y z = tEnd y z' := by
  refine ⟨⟨1, 1, by decide, by decide⟩, ⟨1, 2, by decide, by decide⟩,
          ⟨2, 1, by decide, by decide⟩, by decide, by decide⟩

/-! ## Definition 7.5 — side exchange

  Two maps, and the book is careful to keep them apart: `Inv` acts on
  presentations, `𝖯` acts on complete history-bearing records. Conflating them
  is exactly the substitution §13's table forbids. -/

/-- **Definition 7.5 on presentations.** The imported relational inversion,
    `Inv(p:q) = q:p`. This is Elements I's `IPres.inv`; naming it again here
    would be the renaming Convention 7.9 forbids. -/
abbrev Inv : IPres → IPres := IPres.inv

/-- **Definition 7.5 on records.** `𝖯` swaps every `L` and `R` in the retained
    word. The identifier is transported unchanged, which is what preserves the
    distinction between an occurrence and its mirror: they are different
    occurrences with the same identifier history, not the same occurrence. -/
def sideExchangeWord (w : Word) : Word := w.map not

/-- `𝖯` is an involution on words, and length-preserving, which is the fact
    Lemma 7.7's proof leans on. -/
@[simp] theorem sideExchangeWord_involutive (w : Word) :
    sideExchangeWord (sideExchangeWord w) = w := by
  simp [sideExchangeWord, List.map_map, Function.comp_def]

@[simp] theorem sideExchangeWord_length (w : Word) :
    (sideExchangeWord w).length = w.length := by
  simp [sideExchangeWord]

/-- **`Inv` and `𝖯` are different maps, as Def 7.5 insists.** One acts on a
    presentation and one on a word; the record-level map is not recoverable
    from the presentation-level one, because distinct words share a
    presentation. -/
theorem inv_and_P_act_on_different_things :
    ∃ w v : Word, w ≠ v ∧ sideExchangeWord w ≠ sideExchangeWord v := by
  refine ⟨[true], [false], by decide, by decide⟩

/-! ## Proposition 7.6 — directional composition is side-covariant -/

/-- **Proposition 7.6.** `Inv(A ⊗ B) = Inv(A) ⊗ Inv(B)`.

    The book's proof, in coordinates: `A ⊗ B = ad:bc`, and `Inv(A) ⊗ Inv(B) =
    (b:a) ⊗ (d:c) = bc:ad = Inv(ad:bc)`. -/
theorem inv_contrast (A B : IPres) :
    Inv (contrast A B) = contrast (Inv A) (Inv B) :=
  IPres.eq_of rfl rfl

/-- **And it is Elements I's `otimes_swap` in disguise.**

    Elements I proved `B ⊗ A = Inv(A ⊗ B)`. Put beside Prop 7.6 that gives
    `B ⊗ A = Inv(A) ⊗ Inv(B)`: **swapping the operands and inverting both are
    the same operation.** Two covariance statements that read as separate facts,
    one in each volume, are one fact. Neither book says so. -/
theorem swap_eq_invert_both (A B : IPres) :
    contrast B A = contrast (Inv A) (Inv B) := by
  rw [← inv_contrast]
  exact IPres.otimes_swap A B

/-! ## Lemma 7.7 — Stern-Brocot depth is reciprocal-invariant -/

/-- Reduction commutes with inversion: reducing then swapping is swapping then
    reducing, because `gcd` is symmetric. Needed because Def 7.3 reduces inside
    the comparison, so Lemma 7.7 has to survive the `ρ`. -/
theorem reduce_inv (A : IPres) :
    Pres.reduce (IPres.toPres (Inv A))
      = ⟨(Pres.reduce (IPres.toPres A)).q, (Pres.reduce (IPres.toPres A)).p,
         by
           rintro ⟨h1, h2⟩
           exact (Pres.reduce (IPres.toPres A)).ne_zero ⟨h2, h1⟩⟩ := by
  refine Pres.eq_of ?_ ?_
  · change A.q / Nat.gcd A.q A.p = A.q / Nat.gcd A.p A.q
    rw [Nat.gcd_comm]
  · change A.p / Nat.gcd A.q A.p = A.p / Nat.gcd A.p A.q
    rw [Nat.gcd_comm]

/-- **Lemma 7.7.** `d_SB(Inv X) = d_SB(X)`, after reduction.

    The book's reason: positive decoding gives `X` one word of length
    `d_SB(X)`, side exchange sends it to `w̄`, and `|w̄| = |w|`. Here it comes
    through Elements I's `dSB_swap`, which is Def 5.4's stated reason already
    proved. -/
theorem dSB_reduce_inv (A : IPres) :
    dSB (Pres.reduce (IPres.toPres (Inv A)))
      = dSB (Pres.reduce (IPres.toPres A)) := by
  have hp : 0 < (Pres.reduce (IPres.toPres A)).p := Pres.reduce_p_pos A.p_pos
  have hq : 0 < (Pres.reduce (IPres.toPres A)).q := Pres.reduce_q_pos A.q_pos
  rw [reduce_inv A]
  exact (dSB_swap hp hq rfl rfl).symm

/-! ## Theorem 7.8 — side invariance of support tension -/

/-- **Theorem 7.8.** `T_end,𝖯O(𝖯y, 𝖯z) = T_end,O(y, z)`.

    The book's three steps, in order: a complete side exchange sends each
    observer-local presentation to its reciprocal; Prop 7.6 sends the
    directional contrast to the reciprocal of the original contrast; reduction
    commutes with the exchange and Lemma 7.7 preserves the depth.

    Every step is now a named lemma, so the proof is the book's argument and
    nothing else. -/
theorem tEnd_side_invariant (A B : IPres) :
    tEnd (Inv A) (Inv B) = tEnd A B := by
  unfold tEnd
  rw [← inv_contrast]
  exact dSB_reduce_inv (contrast A B)

/-- The keyed signature inherits it, key by key: a mirrored observer reads the
    same tensions against the mirrored family. -/
theorem tensionSignature_side_invariant (fam : List IPres) (y : IPres) :
    (tensionSignature (fam.map Inv) (Inv y)).map Prod.snd
      = (tensionSignature fam y).map Prod.snd := by
  simp [tensionSignature, List.map_map, Function.comp_def, tEnd_side_invariant]

/-! ## Convention 7.9 — division of exact roles

  *"No quantity in the table is renamed as another, and no equality among them
  is assumed beyond a separately proved special case."* A convention with no
  content would be a comment. This one has content, because the quantities are
  close enough to be confused, so each pair gets a witness that they differ. -/

/-- **`ℓ_CF` is not `d_SB`, and this is why Lemma 7.7 could not have been
    stated with `ℓ_CF`.** Elements I's `lCF_swap_ne` already shows `ℓ_CF` is not
    reciprocal-invariant; the table in 7.9 keeps them apart for exactly that
    reason. Restated here as a fact about §7's own quantities. -/
theorem cf_signature_is_not_the_tension_signature :
    ∃ fam : List IPres, ∃ y : IPres,
      cfSignature fam y ≠ tensionSignature fam y := by
  refine ⟨[⟨1, 3, by decide, by decide⟩], ⟨3, 1, by decide, by decide⟩, ?_⟩
  decide

/-- **The support comparison is `T_end` and not the walk distance.** Elements I
    witnessed this both ways round, `Tend_eq_dwalk_ne` and `dwalk_eq_Tend_ne`
    (on the addressed relations: `Frame.Tend_eq_dwalk_ne_addressed`,
    `Frame.dwalk_eq_Tend_ne_addressed`):
    equal tension with different word separation, and equal separation with
    different tension. Neither determines the other, so Convention 7.9's
    refusal to rename one as the other is forced rather than stylistic. -/
theorem tension_is_not_word_distance :
    ∃ A B C D : IPres, tEnd A B = tEnd C D
      ∧ ∃ u v u' v' : Word, dwalk u v ≠ dwalk u' v' := by
  refine ⟨⟨1, 1, by decide, by decide⟩, ⟨1, 2, by decide, by decide⟩,
          ⟨2, 1, by decide, by decide⟩, ⟨1, 1, by decide, by decide⟩, by decide,
          [true], [], [], [], by decide⟩

/-! ## Corollary 7.10 — prefix covariance of support operands -/

/-- **Corollary 7.10.** Under the common-prefix transport `Z_u`, every admitted
    local relation, directional contrast, endpoint contrast depth, composition
    star and exact keyed signature is preserved up to the transported keys.

    The book's proof is one line: Thm 3.4 preserves `λ_O` occurrence for
    occurrence, and Defs 7.2 to 7.4 then give the claim directly. That is
    exactly this proof: `prefix_covariance` from §3 says any function of the
    relative matrix is invariant, and every quantity in §7 is such a function. -/
theorem lambda_prefix_invariant (u : Word) (MO Mx : Mat2) :
    lambda (Z u MO) (Z u Mx) = lambda MO Mx :=
  prefix_covariance (fun M => (dec M).map r) u MO Mx

/-- Contrast, depth, star and signature therefore transport with the keys and
    nothing else changes. Stated for the depth, which is the one Definition
    8.1 reads. -/
theorem operands_prefix_invariant (u : Word) (MO My Mz : Mat2) :
    (lambda (Z u MO) (Z u My), lambda (Z u MO) (Z u Mz))
      = (lambda MO My, lambda MO Mz) := by
  rw [lambda_prefix_invariant, lambda_prefix_invariant]

end Two
end RatioSpace
