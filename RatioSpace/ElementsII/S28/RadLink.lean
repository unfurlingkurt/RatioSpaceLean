/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S29.RidgeDefect
import RatioSpace.ElementsII.S28.RadTransport
/-!
  Bridge between §28 (`Two/RadTransport.lean`) and §29 (`Two/RidgeDefect.lean`).

  Both files rebuilt `Φ_Rad` without `Finset.range` (which carries
  `Classical.choice`): §28 as `phiRadC` over `sumTo`, §29 as `phiRadE` over
  `dsumRec`. They are the same integer formula, and this file proves it, so there
  is one `Φ_Rad` in the tree, not two.

  With that, §29's Proposition 29.6 no longer needs its carried hypothesis
  `Φ_Rad(Q_R((RL)^r)) = 1`: §28's Theorem 28.9 (`alternating_table`) supplies it
  from Proposition 28.3's cocycle, which is the book's own dependency, and the
  only thing still carried is that imported standard result (`RadCocycle`).
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Two
namespace RadBridge

open Mat2 Word

theorem dsumRec_eq_sumTo (a : ℤ) (k : ℕ) :
    ∀ n, RidgeDefect.dsumRec a k n = RadTransport.sumTo (RadTransport.dTerm a k) n
  | 0 => rfl
  | n + 1 => by
    change RidgeDefect.dsumRec a k n + _ = RadTransport.sumTo (RadTransport.dTerm a k) n + _
    rw [dsumRec_eq_sumTo a k n]
    rfl

theorem dedekindRec_eq_dsum (a : ℤ) (k : ℕ) : RidgeDefect.dedekindRec a k = RadTransport.dsum a k := by
  unfold RidgeDefect.dedekindRec RadTransport.dsum
  rw [dsumRec_eq_sumTo]

/-- **One `Φ_Rad`.** §29's and §28's choice-free forms agree on every matrix. -/
theorem phiRadE_eq_phiRadC (Q : Mat2) : RidgeDefect.phiRadE Q = RadTransport.phiRadC Q := by
  unfold RidgeDefect.phiRadE RadTransport.phiRadC
  simp only [dedekindRec_eq_dsum]

theorem psiRadE_eq_psiRadC (Q : Mat2) : RidgeDefect.psiRadE Q = RadTransport.psiRadC Q := by
  unfold RidgeDefect.psiRadE RadTransport.psiRadC
  rw [phiRadE_eq_phiRadC]

theorem QR_eq_Qs (v : Word) : RidgeDefect.QR v = RadTransport.Qs true v := rfl

theorem rlWord_eq_wpow : ∀ r, RidgeDefect.rlWord r = RadTransport.wpow [true, false] r
  | 0 => rfl
  | r + 1 => by
    change RidgeDefect.rlWord r ++ [true, false] = RadTransport.wpow [true, false] r ++ [true, false]
    rw [rlWord_eq_wpow r]

/-- **Theorem 28.9's transport value, in §29's names.** Discharges §29's `hΦ`
    from Proposition 28.3's imported cocycle. -/
theorem strobe_phi (H : RadTransport.RadCocycle) (r : ℕ) :
    RidgeDefect.phiRadE (RidgeDefect.QR (RidgeDefect.rlWord r)) = 1 := by
  rw [phiRadE_eq_phiRadC, QR_eq_Qs, rlWord_eq_wpow]
  exact (RadTransport.alternating_table H r).1.2.1

/-- **Proposition 29.6, on the book's own dependency.** Every clause, with the
    transport value supplied by §28 rather than assumed. -/
theorem prop_29_6_of_cocycle (H : RadTransport.RadCocycle) (r : ℕ) :
    type_of% (RidgeDefect.prop_29_6 r (strobe_phi H r)) :=
  RidgeDefect.prop_29_6 r (strobe_phi H r)

/-- **Boundary Statement 29.8, orbit half, on the book's own dependency.** -/
theorem boundary_29_8_orbit_of_cocycle (H : RadTransport.RadCocycle) :
    type_of% (RidgeDefect.boundary_29_8_orbit (strobe_phi H)) :=
  RidgeDefect.boundary_29_8_orbit (strobe_phi H)

#print axioms dsumRec_eq_sumTo
#print axioms dedekindRec_eq_dsum
#print axioms phiRadE_eq_phiRadC
#print axioms psiRadE_eq_psiRadC
#print axioms QR_eq_Qs
#print axioms rlWord_eq_wpow
#print axioms strobe_phi
#print axioms prop_29_6_of_cocycle
#print axioms boundary_29_8_orbit_of_cocycle

end RadBridge
end Two
end RatioSpace
