/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S10.TheCausalSiblingPairRecordOnTheAccumulatedWord
import RatioSpace.ElementsII.S11.Advance
/-!
  Elements II Definition 11.5, the native annotation package.

  `Advance.NativeAnn.ofChild` leaves the `cf` slot not-evaluated, where the book
  forms `CF(x;g)` at every child event. The slot is typed `Slot Aux`, the same
  `Aux` as the declared channel and lift slots, so the existing structure cannot
  hold a `CausalRecord` there without fixing `Aux` for all three. This file adds
  the package with `cf` mandatory, builds it from the archived parent core and
  the hand, and proves the book's laws for it: both accumulators advance from
  the parent, the causal record names the archived parent, child and sibling,
  and it is formed with status proposed, before any selection.
-/

namespace RatioSpace
namespace Gaps
namespace G2_11

open RatioSpace.Two RatioSpace.Two.Advance Word RatioSpace.Gaps.G2_07

/-- **Definition 11.5, with `CF(x;g)` mandatory.** The two accumulators and the
    causal record are always present; channel and lift stay `Slot`s, evaluated
    only when declared. -/
structure NativeAnnCF (Aux : Type) where
  /-- `Ω(O,y)`. -/
  winding : ℤ
  /-- `κ_cl(y)`. -/
  closure : ZMod 12
  /-- `channel(y)`, not-evaluated unless a receiver profile is declared. -/
  channel : Slot Aux
  /-- `liftStatus(y)`, not-evaluated unless a lift predicate is declared. -/
  lift : Slot Aux
  /-- `CF(x;g)`, formed at every child event. -/
  cf : CausalRecord

/-- `σ(L) = -1`, `σ(R) = +1`. -/
theorem sigma_eq (g : Bool) : sigma g = if g then 1 else -1 := by
  cases g <;> rfl

/-- **Definition 11.5 at the child `y = xg` of the archived core `x = c`.**
    `Ω` is the observer winding of the parent advanced by `σ(g)`, `κ_cl` the
    parent closure advanced by `ψ₁₂(g)`, and `CF(x;g)` the causal record on the
    accumulated word (`causalRecordAcc`). -/
def NativeAnnCF.ofChildCore {Aux : Type} (wO : Word) (c : Core) (g : Bool)
    (channel lift : Slot Aux) : NativeAnnCF Aux where
  winding := Two.winding wO c.fullWord + sigma g
  closure := c.closure + psi12 [g]
  channel := channel
  lift := lift
  cf := causalRecordAcc c.seedId c.seed c.relWord g

/-- Forget the causal record back into `Advance.NativeAnn`. -/
def NativeAnnCF.forget {Aux : Type} (n : NativeAnnCF Aux) : NativeAnn Aux where
  winding := n.winding
  closure := n.closure
  channel := n.channel
  lift := n.lift
  cf := .notEvaluated

/-- **The package extends `NativeAnn.ofChild`**: with channel and lift
    undeclared and the causal record forgotten, it is `ofChild` at the parent's
    observer winding and closure. -/
theorem NativeAnnCF.forget_ofChildCore {Aux : Type} (wO : Word) (c : Core) (g : Bool) :
    (NativeAnnCF.ofChildCore (Aux := Aux) wO c g .notEvaluated .notEvaluated).forget =
      NativeAnn.ofChild (Two.winding wO c.fullWord) c.closure g := by
  simp only [NativeAnnCF.forget, NativeAnnCF.ofChildCore, NativeAnn.ofChild, sigma_eq]

/-- **`Ω(O,y) = Ω(O,x) + σ(g)`, as an accumulation law on the archive.** For a
    well-formed parent the package's winding is the observer winding of the
    archived child's own accumulated word. -/
theorem NativeAnnCF.ofChildCore_winding {Aux : Type} (wO : Word) (c : Core) (hc : c.WellFormed)
    (g : Bool) (ch li : Slot Aux) (entry : ℕ) (prov : Provenance) :
    (NativeAnnCF.ofChildCore wO c g ch li).winding =
      Two.winding wO (childCore c g entry prov).fullWord := by
  have hw : (childCore c g entry prov).fullWord = c.fullWord ++ [g] := by
    change (childProposal c.seedId c.seed c.relWord g).fullWord = _
    rw [childProposal_fullWord, ← hc.1]
  rw [hw, winding_child, NativeAnnCF.ofChildCore, sigma_eq]

/-- **`κ_cl(y) = κ_cl(x) + ψ₁₂(g) mod 12`, as an accumulation law on the
    archive.** For a well-formed parent the package's closure is the archived
    child's own closure. -/
theorem NativeAnnCF.ofChildCore_closure {Aux : Type} (wO : Word) (c : Core) (hc : c.WellFormed)
    (g : Bool) (ch li : Slot Aux) (entry : ℕ) (prov : Provenance) :
    (NativeAnnCF.ofChildCore wO c g ch li).closure = (childCore c g entry prov).closure :=
  (childCore_closure' c hc g entry prov).symm

/-- **`CF(x;g)` is formed at the child event, on the archived identifiers.** Its
    parent, child and sibling are the archived parent and the two archived
    proposals beneath it; its `W` field is the archived sibling's accumulated
    word; its hands are `g` and `ḡ`; its status is proposed. -/
theorem NativeAnnCF.ofChildCore_cf {Aux : Type} (wO : Word) (c : Core) (hc : c.WellFormed)
    (g : Bool) (ch li : Slot Aux) (entry : ℕ) (prov : Provenance) :
    let r := (NativeAnnCF.ofChildCore wO c g ch li).cf
    r.parentId = c.id ∧
    r.childId = (childCore c g entry prov).id ∧
    r.siblingId = (childCore c (!g) entry prov).id ∧
    r.wField = (childCore c (!g) entry prov).fullWord ∧
    r.hand = g ∧ r.oppHand = !g ∧
    r.status = .proposed :=
  ⟨hc.2.2.2.2.1.symm, rfl, rfl,
    causalRecordAcc_wField_eq_sibling c.seedId c.seed c.relWord g .proposed, rfl, rfl, rfl⟩

/-- The package's record is the one read off the archived child core. -/
theorem NativeAnnCF.ofChildCore_cf_eq_causalPairOfAcc {Aux : Type} (wO : Word) (c : Core)
    (g : Bool) (ch li : Slot Aux) (entry : ℕ) (prov : Provenance) :
    causalPairOfAcc (childCore c g entry prov) = some (NativeAnnCF.ofChildCore wO c g ch li).cf :=
  causalPairOfAcc_childCore c g entry prov

/-- **Formed before either proposal is named selected or refused.** The record
    reads only the parent core and the hand: no observer word, no channel or
    lift declaration, and no status enters it. -/
theorem NativeAnnCF.ofChildCore_cf_reads_only_parent_and_hand {Aux Aux' : Type}
    (wO wO' : Word) (c : Core) (g : Bool) (ch li : Slot Aux) (ch' li' : Slot Aux') :
    (NativeAnnCF.ofChildCore wO c g ch li).cf = (NativeAnnCF.ofChildCore wO' c g ch' li').cf :=
  rfl

/-- **The two children's packages present one sibling pair from its two hands.**
    Each names the other as its sibling, beneath the same parent. -/
theorem NativeAnnCF.ofChildCore_cf_siblings {Aux : Type} (wO : Word) (c : Core) (g : Bool)
    (ch li : Slot Aux) :
    (NativeAnnCF.ofChildCore wO c g ch li).cf.siblingId =
        (NativeAnnCF.ofChildCore wO c (!g) ch li).cf.childId ∧
    (NativeAnnCF.ofChildCore wO c (!g) ch li).cf.siblingId =
        (NativeAnnCF.ofChildCore wO c g ch li).cf.childId ∧
    (NativeAnnCF.ofChildCore wO c g ch li).cf.parentId =
        (NativeAnnCF.ofChildCore wO c (!g) ch li).cf.parentId := by
  refine ⟨rfl, ?_, rfl⟩
  simp [NativeAnnCF.ofChildCore, causalRecordAcc, siblingAlt]

#print axioms NativeAnnCF.ofChildCore
#print axioms NativeAnnCF.forget
#print axioms sigma_eq
#print axioms NativeAnnCF.forget_ofChildCore
#print axioms NativeAnnCF.ofChildCore_winding
#print axioms NativeAnnCF.ofChildCore_closure
#print axioms NativeAnnCF.ofChildCore_cf
#print axioms NativeAnnCF.ofChildCore_cf_eq_causalPairOfAcc
#print axioms NativeAnnCF.ofChildCore_cf_reads_only_parent_and_hand
#print axioms NativeAnnCF.ofChildCore_cf_siblings

end G2_11
end Gaps
end RatioSpace
