/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S15.Accumulation
/-!
  Elements II Lemma 12.1: new proposal identifiers are lawful and
  disjoint.

  `Advance.lean` proves the arithmetic of the book's length argument
  (`child_rel_length`, `child_ne_of_length_le`) but carries no invariant tying an
  archived occurrence to the tick it was created by, so disjointness of the new
  identifiers from the existing archive stays the hypothesis `hfresh` of
  `advanceCarrier` and `archive_growth`.

  The book's proof names the invariant: "every archived occurrence created no
  later than tick `j` has a relative continuation word of length at most `j`,
  whereas a proposal at the current advance has length `j+1`". This file states
  it (`TickLengthInv`), proves it holds at a seed carrier, proves one tick
  preserves it, proves it along every schedule, and derives `hfresh` from it.
-/

namespace RatioSpace
namespace Gaps
namespace G2_13

open RatioSpace.Two RatioSpace.Two.Advance RatioSpace.Two.Accumulation

/-! The per-carrier content (`TickLengthInv` through
    `tickLengthInv_of_seeds`) is in `ElementsII/S12/RunInvariant.lean`, under
    the same names, so that `Accumulation.lean`'s schedule can require it. -/

/-- **The invariant holds at every tick a schedule reaches**, from the tick-zero
    carrier. -/
theorem iterate_tickLengthInv {Aux : Type} {h : ℕ} (pol : Policy Aux h)
    (X0 : TickCarrier Aux h) (hX0 : Seeded X0) (hinv0 : TickLengthInv X0)
    (n : ℕ) (hn : n ≤ h) : TickLengthInv (iterate pol X0 hX0 n hn) := by
  induction n with
  | zero => simpa using hinv0
  | succ k ih =>
      rw [iterate_succ]
      exact tickLengthInv_advanceCarrier _ _ _ _ _ _ _ _ (ih (Nat.le_of_succ_le hn))

/-- **Along every schedule `hfresh` is a theorem**, not data: at each carrier the
    schedule reaches, every proposal identifier is fresh. -/
theorem iterate_hfresh {Aux : Type} {h : ℕ} (pol : Policy Aux h)
    (X0 : TickCarrier Aux h) (hX0 : Seeded X0) (hinv0 : TickLengthInv X0)
    (n : ℕ) (hn : n ≤ h) (stratum : ℕ) (prov : Provenance) :
    ∀ p ∈ proposals (iterate pol X0 hX0 n hn).archive (iterate pol X0 hX0 n hn).active,
      (childCore p.1 p.2 stratum prov).id ∉ archIds (iterate pol X0 hX0 n hn).archive :=
  hfresh_of_tickLengthInv _ (iterate_tickLengthInv pol X0 hX0 hinv0 n hn) stratum prov

/-- **Corollary 12.2 without `hfresh`.** The archive grows by exactly two cores
    per active archived occurrence, with Lemma 12.1 supplied by the invariant. -/
theorem archive_growth_of_tickLengthInv {Aux : Type} {h : ℕ} (X : TickCarrier Aux h)
    (hX : TickLengthInv X) (stratum : ℕ) (prov : Provenance) :
    (advanceArchive X.archive X.active stratum prov).length =
      X.archive.length + 2 * (X.archive.filter (fun c => c.id ∈ X.active)).length :=
  archive_growth X.archive X.active stratum prov (hfresh_of_tickLengthInv X hX stratum prov)

#print axioms iterate_tickLengthInv
#print axioms iterate_hfresh
#print axioms archive_growth_of_tickLengthInv

end G2_13
end Gaps
end RatioSpace
