/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.RootOrbit
/-!
  Elements II §16, Proposition 16.15 — Automorphism certificates for the
  retained ties.

  Every pair-preserving advance of Theorem 16.11(3) is certified by a tension
  automorphism in the sense of Lemma 16.14. Built here: the two named finite
  certificates, decided against the tension matrices `RootOrbit.lean` already
  proved; the root chain's certificate by side exchange (Theorem 7.8,
  `tEnd_side_invariant`) at the terminal tick; and the two ensemble
  degeneracies the book separates from these, as exact `ℤ[φ]` identities.

  The certificate for the whole family `RⁿL`, `n ≡ 3 (mod 21)`, is in
  `FamilyClassification.lean` (`tie_equalities`, `cert_RnL`, `cert_RnL_tie`),
  because it rests on Theorem 16.11 Step 2's tensions, which live there. The
  `n = 3` member is also the second certificate below, read through its mirror.
-/

namespace RatioSpace
namespace Two
namespace TieCertificates

open Zphi RootOrbit

/-- Read a 4×4 tension matrix stored as a list of rows. -/
def at4 (M : List (List ℕ)) (i j : Fin 4) : ℕ := (M[i.val]!)[j.val]!

/-! ## `{LL, LR} → {LLL, LRL}` on the family `[LLL, LLR, LRL, LRR]` -/

/-- The matrix `tie_1_2_L` decided. -/
def M12 : List (List ℕ) := [[0, 4, 5, 2], [4, 0, 2, 8], [5, 2, 0, 4], [2, 8, 4, 0]]

/-- `σ = (LLL LRL)(LLR LRR)`, as indices `(0 2)(1 3)`. -/
def σ12 : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- **Proposition 16.15, first named certificate.** The family is the one
    `𝒬_L` actually compares at its advance `1 → 2`; `σ` is an involution; it
    preserves every tension; and the book's four displayed values are the
    matrix's own entries: `t(LLL,LLR) = t(LRL,LRR) = 4`,
    `t(LLL,LRR) = t(LRL,LLR) = 2`, `t(LLL,LRL) = 5`, `t(LLR,LRR) = 8`. -/
theorem cert_12 :
    (admittedFam MOL 2 seed164Prov props1L).map
        (tensions (admittedFam MOL 2 seed164Prov props1L)) = M12 ∧
    (∀ i, σ12 (σ12 i) = i) ∧
    (∀ i j, at4 M12 (σ12 i) (σ12 j) = at4 M12 i j) ∧
    at4 M12 0 1 = 4 ∧ at4 M12 2 3 = 4 ∧ at4 M12 0 3 = 2 ∧ at4 M12 2 1 = 2 ∧
    at4 M12 0 2 = 5 ∧ at4 M12 1 3 = 8 :=
  ⟨tie_1_2_L.1, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `{LLLRL, LLLRR} → {LLLRLL, LLLRRR}` on `[LLLRLL, LLLRLR, LLLRRL, LLLRRR]` -/

def M45 : List (List ℕ) := [[0, 24, 14, 8], [24, 0, 17, 14], [14, 17, 0, 24], [8, 14, 24, 0]]

/-- `σ = (LLLRLL LLLRRR)(LLLRLR LLLRRL)`, as indices `(0 3)(1 2)`. -/
def σ45 : Fin 4 → Fin 4 := ![3, 2, 1, 0]

/-- **Proposition 16.15, second named certificate**, with the book's values
    `t(LLLRLL,LLLRLR) = t(LLLRRR,LLLRRL) = 24`,
    `t(LLLRLL,LLLRRL) = t(LLLRRR,LLLRLR) = 14`, `t(LLLRLL,LLLRRR) = 8`,
    `t(LLLRLR,LLLRRL) = 17`. -/
theorem cert_45 :
    (admittedFam MOL 5 seed164Prov props4L).map
        (tensions (admittedFam MOL 5 seed164Prov props4L)) = M45 ∧
    (∀ i, σ45 (σ45 i) = i) ∧
    (∀ i j, at4 M45 (σ45 i) (σ45 j) = at4 M45 i j) ∧
    at4 M45 0 1 = 24 ∧ at4 M45 3 2 = 24 ∧ at4 M45 0 2 = 14 ∧ at4 M45 3 1 = 14 ∧
    at4 M45 0 3 = 8 ∧ at4 M45 1 2 = 17 :=
  ⟨tie_4_5_L.1, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The certified pairs really are tied**, read from the coherence values already
    decided: the exchanged occurrences carry equal coherence values in both families. -/
theorem certified_pairs_tie :
    (admittedFam MOL 2 seed164Prov props1L).map
        (coherenceOf (admittedFam MOL 2 seed164Prov props1L)) =
      [(⟨0, 1⟩ : Zphi), ⟨42, -25⟩, ⟨0, 1⟩, ⟨42, -25⟩] ∧
    (admittedFam MOL 5 seed164Prov props4L).map
        (coherenceOf (admittedFam MOL 5 seed164Prov props4L)) =
      [(⟨75670, -46766⟩ : Zphi), ⟨73052, -45148⟩, ⟨73052, -45148⟩, ⟨75670, -46766⟩] :=
  ⟨tie_1_2_L.2, tie_4_5_L.2⟩

/-! ## The root chain, by side exchange -/

/-- **The root chain's certificate is side exchange `𝖯`.** Theorem 7.8 says
    `Inv` preserves every tension; at the root's terminal tick the admitted
    family is closed under `Inv` — its addresses come out exactly reversed. -/
theorem cert_root_tick7 :
    (∀ A B : IPres, tEnd (Inv A) (Inv B) = tEnd A B) ∧
    (admittedFam MOeps 7 seed164Prov props6eps).map (fun y => (y.q, y.p)) =
      ((admittedFam MOeps 7 seed164Prov props6eps).map (fun y => (y.p, y.q))).reverse :=
  ⟨tEnd_side_invariant, by rw [prop_16_6_root.1]; decide⟩

/-! ## The ensemble degeneracies are not of this kind -/

/-- **The two degeneracies of Proposition 16.13, as the book separates them.**
    Their tied occurrences have distinct histograms, so no tension automorphism
    exchanges them; the equal coherence values are `ℤ[φ]` identities between different
    contribution patterns — exactly Lemma 16.14's `{P, P}` against
    `{P - 1, P + 2}`, at `P = 6` and `P = 4`. -/
theorem ensemble_degeneracies :
    phiNegPow 5 + phiNegPow 8 = 2 * phiNegPow 6 ∧
    phiNegPow 3 + phiNegPow 6 = 2 * phiNegPow 4 := by
  refine ⟨by decide, by decide⟩

#print axioms cert_12
#print axioms cert_45
#print axioms certified_pairs_tie
#print axioms cert_root_tick7
#print axioms ensemble_degeneracies

end TieCertificates
end Two
end RatioSpace
