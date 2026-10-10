/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S11.Advance
/-!
  Gap G2-10 · Elements II Definition 11.3, the complete admission certificate.

  `Advance.lean` states `Fail = ∅ ↔ admitted` only at `boundary = true`, gives the
  "precisely when" iff for the chart reason only, and `AdmCert` has no slot for
  the decoded word `a_y`, the local relation `λ_O(y)`, or the status
  no-direct-positive-admission. This file adds:

  * the two missing "precisely when" iffs (boundary, predicate);
  * the `Fail = ∅ ↔ Adm = 1` iff at every boundary value, under Definition 4.9's
    mandatory conjunct, with a witness that the conjunct is what makes it true;
  * the complete certificate, built from the observer and occurrence matrices,
    with the direct-chart slot that carries `(a_y, λ_O(y))` exactly when
    admission is `1` and the named status otherwise;
  * the tie to Definition 7.1: the certificate's admission bit is membership in
    `Support.admitted`, so `A_{j+1}` is the family the certificates certify.
-/

namespace RatioSpace
namespace Gaps
namespace G2_10

open RatioSpace.Two RatioSpace.Two.Advance Mat2 Word

/-! ## The three reasons, each precisely when -/

/-- **Definition 11.3: boundary-rejected precisely when `γ_∂ = 0`.** -/
theorem boundaryRejected_mem_iff (b : Bool) (n : ℤ) (p : Bool) :
    FailReason.boundaryRejected ∈ failReasons b n p ↔ b = false := by
  by_cases h : n = 0 <;> cases b <;> cases p <;> simp [failReasons, h]

/-- **Definition 11.3: predicate-composition-rejected precisely when
    `Pred_Γ = 0`.** -/
theorem predicateRejected_mem_iff (b : Bool) (n : ℤ) (p : Bool) :
    FailReason.predicateCompositionRejected ∈ failReasons b n p ↔ p = false := by
  by_cases h : n = 0 <;> cases b <;> cases p <;> simp [failReasons, h]

/-- **Definition 11.3: outside-direct-positive-chart precisely when
    `Neg(Q_{O,y}) > 0`**, stated on the load itself rather than as `≠ 0`. -/
theorem chartRejected_mem_iff_pos (b : Bool) (Q : Mat2) (p : Bool) :
    FailReason.outsideDirectPositiveChart ∈ failReasons b (negLoad Q) p ↔ 0 < negLoad Q := by
  rw [chart_reason_mem_iff]
  have h0 := negLoad_nonneg Q
  exact ⟨fun h => Int.lt_iff_le_and_ne.mpr ⟨h0, Ne.symm h⟩, fun h => Int.ne_of_gt h⟩

/-! ## Definition 4.9's mandatory conjunct -/

/-- **Definition 4.9.** `Pred_Γ` carries the boundary predicate as a mandatory
    conjunct of whatever declared Boolean composition `rest` the other components
    receive. -/
def predWithBoundary (boundary rest : Bool) : Bool := boundary && rest

/-- **`Fail = ∅ ↔ Adm = 1` at every boundary value**, given only that a failed
    boundary forces a failed predicate (Definition 4.9's conjunct). -/
theorem failReasons_nil_iff_admits_of_conjunct (b : Bool) (n : ℤ) (p : Bool)
    (hconj : b = false → p = false) : failReasons b n p = [] ↔ admits n p = true := by
  cases b <;> cases p <;> by_cases h : n = 0 <;> simp_all [failReasons, admits]

/-- The iff, with the conjunct built in. -/
theorem failReasons_nil_iff_admits_conj (b : Bool) (n : ℤ) (rest : Bool) :
    failReasons b n (predWithBoundary b rest) = [] ↔
      admits n (predWithBoundary b rest) = true :=
  failReasons_nil_iff_admits_of_conjunct b n _ (fun hb => by simp [predWithBoundary, hb])

/-- **The conjunct is load-bearing.** Without it the two halves of the
    certificate disagree: boundary failed, chart and predicate passed, a
    nonempty blocking set, and admission `1`. This is why
    `failReasons_nil_iff_admits` had to be stated at `boundary = true`. -/
theorem failReasons_admits_disagree_without_conjunct :
    failReasons false 0 true ≠ [] ∧ admits 0 true = true := by
  simp [failReasons, admits]

/-! ## The complete certificate -/

/-- **Definition 11.3's direct-chart slots.** Either the decoded positive word
    `a_y` together with `λ_O(y) = r(a_y)`, or the exact status
    no-direct-positive-admission. A signed matrix has no constructor here, so
    none can be supplied to `r` in their place. -/
inductive DirectChartSlot where
  | decoded (a : Word) (lam : Pres)
  | noDirectPositiveAdmission

/-- **Definition 11.3, the complete admission certificate**, with the boundary
    value and the direct-chart slots that `AdmCert` omits. -/
structure AdmCertComplete (Aux : Type) extends AdmCert Aux where
  /-- `γ_∂(y)`, retained so the boundary reason can be read off. -/
  boundary : Bool
  /-- `(a_y, λ_O(y))` or no-direct-positive-admission. -/
  direct : DirectChartSlot

/-- The direct-chart slots: decode only when admission is `1`. -/
def directSlot (Q : Mat2) (adm : Bool) : DirectChartSlot :=
  if adm then
    match dec Q with
    | some a => .decoded a (Frame.r a)
    | none => .noDirectPositiveAdmission
  else .noDirectPositiveAdmission

/-- **Definition 11.3, computed.** From the observer matrix `M_O`, the
    occurrence matrix `M_y`, the boundary value, the retained predicate vector,
    and the declared Boolean composition of the non-boundary components. -/
def admCertOf {Aux : Type} (MO My : Mat2) (boundary : Bool) (gamma : List Aux) (rest : Bool) :
    AdmCertComplete Aux where
  encounter := Two.Q MO My
  negLoad := negLoad (Two.Q MO My)
  gamma := gamma
  pred := predWithBoundary boundary rest
  adm := admits (negLoad (Two.Q MO My)) (predWithBoundary boundary rest)
  fail := failReasons boundary (negLoad (Two.Q MO My)) (predWithBoundary boundary rest)
  boundary := boundary
  direct := directSlot (Two.Q MO My)
    (admits (negLoad (Two.Q MO My)) (predWithBoundary boundary rest))

/-- **The certificate's halves agree at every boundary value.** -/
theorem admCertOf_fail_nil_iff {Aux : Type} (MO My : Mat2) (b : Bool) (γ : List Aux)
    (rest : Bool) :
    (admCertOf MO My b γ rest).fail = [] ↔ (admCertOf MO My b γ rest).adm = true :=
  failReasons_nil_iff_admits_conj b _ rest

/-- **Each blocking reason precisely when its condition fails**, on the complete
    certificate. -/
theorem admCertOf_reasons {Aux : Type} (MO My : Mat2) (b : Bool) (γ : List Aux) (rest : Bool) :
    let C := admCertOf MO My b γ rest
    (FailReason.boundaryRejected ∈ C.fail ↔ C.boundary = false) ∧
    (FailReason.outsideDirectPositiveChart ∈ C.fail ↔ 0 < C.negLoad) ∧
    (FailReason.predicateCompositionRejected ∈ C.fail ↔ C.pred = false) :=
  ⟨boundaryRejected_mem_iff _ _ _, chartRejected_mem_iff_pos _ _ _,
    predicateRejected_mem_iff _ _ _⟩

/-- The encounter of two determinant-one matrices has determinant one. -/
theorem det_Q_of_det {MO My : Mat2} (hO : MO.det = 1) (hy : My.det = 1) :
    (Two.Q MO My).det = 1 := by
  have hinv : (inv2 MO).det = MO.det := by
    simp only [inv2, Mat2.det]; ring
  rw [Two.Q_def, Mat2.det_mul, hinv, hO, hy]; rfl

/-- On determinant one, a vanishing load and a successful positive decoding are
    the same condition (Proposition 9.2 read through the decoder). -/
theorem negLoad_zero_iff_dec_isSome {Q : Mat2} (hd : Q.det = 1) :
    negLoad Q = 0 ↔ (dec Q).isSome = true := by
  rw [direct_admission hd, mem_Mplus_iff_dec]

/-- **When admission is `1`, positive decoding supplies `a_y` and
    `λ_O(y) = r(a_y)`**: the slot holds the decoded word of the encounter, and
    it is the observer-local word and relation of Definition 3.1. -/
theorem admCertOf_direct_of_adm {Aux : Type} {MO My : Mat2} (hd : (Two.Q MO My).det = 1)
    (b : Bool) (γ : List Aux) (rest : Bool) (hadm : (admCertOf MO My b γ rest).adm = true) :
    ∃ a, Word.G a = Two.Q MO My ∧
      (admCertOf MO My b γ rest).direct = .decoded a (Frame.r a) ∧
      localWord MO My = some a ∧ lambda MO My = some (Frame.r a) := by
  have hn : negLoad (Two.Q MO My) = 0 := by
    have h := hadm
    simp only [admCertOf, admits, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  obtain ⟨a, ha⟩ := (direct_admission hd).mp hn
  refine ⟨a, ha, ?_, localWord_eq MO My ha.symm, lambda_eq MO My ha.symm⟩
  have hadm' : admits (negLoad (Two.Q MO My)) (predWithBoundary b rest) = true := hadm
  change directSlot (Two.Q MO My) (admits (negLoad (Two.Q MO My)) (predWithBoundary b rest)) = _
  rw [hadm']
  simp only [directSlot, if_true, ← ha, dec_G]

/-- **When admission is `0`, the slots carry no-direct-positive-admission.** -/
theorem admCertOf_direct_of_not_adm {Aux : Type} (MO My : Mat2) (b : Bool) (γ : List Aux)
    (rest : Bool) (hadm : (admCertOf MO My b γ rest).adm = false) :
    (admCertOf MO My b γ rest).direct = .noDirectPositiveAdmission := by
  have hadm' : admits (negLoad (Two.Q MO My)) (predWithBoundary b rest) = false := hadm
  simp only [admCertOf, directSlot, hadm', Bool.false_eq_true, if_false]

/-- **The admission bit is Definition 7.1's test.** For a proposal record, the
    certificate admits exactly when the observer reaches the proposal by positive
    decoding and the declared predicate (boundary conjunct included) holds. -/
theorem admCertOf_adm_eq_reachable {Aux : Type} {MO : Mat2} (hO : MO.det = 1)
    (y : ProposalRecord) (hy : y.fullMatrix.det = 1) (b : Bool) (γ : List Aux) (rest : Bool) :
    (admCertOf MO y.fullMatrix b γ rest).adm = (reachable MO y && predWithBoundary b rest) := by
  have hd := det_Q_of_det hO hy
  have hiff := negLoad_zero_iff_dec_isSome hd
  have hb : decide (negLoad (Two.Q MO y.fullMatrix) = 0) = (dec (Two.Q MO y.fullMatrix)).isSome
    := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]; exact hiff
  change (decide (negLoad (Two.Q MO y.fullMatrix) = 0) && predWithBoundary b rest) =
    ((localWord MO y.fullMatrix).isSome && predWithBoundary b rest)
  rw [hb]; rfl

/-- Every record built by `proposal` has determinant one, so the equation holds
    for every proposal record with no further hypothesis. -/
theorem admCertOf_adm_eq_reachable_proposal {Aux : Type} {MO : Mat2} (hO : MO.det = 1)
    (id0 : QuestionId) (seed : History) (v : Word) (b : Bool) (γ : List Aux) (rest : Bool) :
    (admCertOf MO (proposal id0 seed v).fullMatrix b γ rest).adm =
      (reachable MO (proposal id0 seed v) && predWithBoundary b rest) :=
  admCertOf_adm_eq_reachable hO _ (by rw [fullMatrix_eq_G_fullWord]; exact det_G _) b γ rest

/-- **Definition 11.3's closing sentence: `A_{j+1}` is the family of Section 7.**
    With the declared predicate `pred y = γ_∂(y) ∧ rest(y)`, a proposal lies in
    `Support.admitted` exactly when it lies in the proposal family and its
    complete certificate admits it. -/
theorem mem_admitted_iff_cert {Aux : Type} {MO : Mat2} (hO : MO.det = 1)
    (bd rest : ProposalRecord → Bool) (γ : ProposalRecord → List Aux) (P : List ProposalRecord)
    (hP : ∀ y ∈ P, y.fullMatrix.det = 1) (y : ProposalRecord) :
    y ∈ admitted MO (fun z => predWithBoundary (bd z) (rest z)) P ↔
      y ∈ P ∧ (admCertOf MO y.fullMatrix (bd y) (γ y) (rest y)).adm = true := by
  unfold admitted
  rw [List.mem_filter]
  constructor
  · rintro ⟨hy, hq⟩
    exact ⟨hy, by rw [admCertOf_adm_eq_reachable hO y (hP y hy)]; exact hq⟩
  · rintro ⟨hy, hq⟩
    exact ⟨hy, by rw [admCertOf_adm_eq_reachable hO y (hP y hy)] at hq; exact hq⟩

#print axioms boundaryRejected_mem_iff
#print axioms predicateRejected_mem_iff
#print axioms chartRejected_mem_iff_pos
#print axioms predWithBoundary
#print axioms failReasons_nil_iff_admits_of_conjunct
#print axioms failReasons_nil_iff_admits_conj
#print axioms failReasons_admits_disagree_without_conjunct
#print axioms directSlot
#print axioms admCertOf
#print axioms admCertOf_fail_nil_iff
#print axioms admCertOf_reasons
#print axioms det_Q_of_det
#print axioms negLoad_zero_iff_dec_isSome
#print axioms admCertOf_direct_of_adm
#print axioms admCertOf_direct_of_not_adm
#print axioms admCertOf_adm_eq_reachable
#print axioms admCertOf_adm_eq_reachable_proposal
#print axioms mem_admitted_iff_cert

end G2_10
end Gaps
end RatioSpace
