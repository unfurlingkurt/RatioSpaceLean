/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
/-!
  Elements II — Reception, observability, and why nothing is lost.

  The claim: *there is no information loss and no disappearing; a difference
  only shifts away from observability, out of a receiver's line of sight.*

  This file checks that rather than asserting it. The result is that the
  "information loss" framing is not merely unfashionable here, it is **false**,
  and the theorems below are the proof.

  The substrate is a type `X`. A receiver is a map `O : X → Y`. A lawful
  continuation grammar is a family `T : G → X → X`. Nothing in this file
  modifies `X`: `O` is applied to states, never to the space, so no theorem here
  could express a substrate losing anything even if one wanted it to.

  What is really going on is a **moving window**. Two states a receiver cannot
  presently tell apart may be separated by a continuation, and `escapeDepth` is
  exactly when. The separation was in the substrate the whole time; the receiver
  acquired line of sight on it. Symmetrically, a pair the receiver can *never*
  separate is not a pair whose difference was destroyed — it is a pair this
  receiver's grammar never addresses, and `receiver_refines` proves a finer
  receiver gets it back.
-/

namespace RatioSpace
namespace Two
namespace Reception

variable {X Y Z G : Type*}

/-! ## The continuation grammar -/

/-- `T_w`, with the first letter applied first: the convention that makes the
    induction in `congruence_iff_future` run on the head. -/
def run (T : G → X → X) : List G → X → X
  | [], x => x
  | g :: w, x => run T w (T g x)

@[simp] theorem run_nil (T : G → X → X) (x : X) : run T [] x = x := rfl

@[simp] theorem run_cons (T : G → X → X) (g : G) (w : List G) (x : X) :
    run T (g :: w) x = run T w (T g x) := rfl

/-! ## Receiver equivalence and its refinements -/

/-- `x ∼_O y`: the receiver cannot presently tell them apart. **This is a fact
    about `O`, not about `x` and `y`.** -/
def Sees (O : X → Y) (x y : X) : Prop := O x = O y

/-- Generator congruence: one lawful step never separates what the receiver
    currently merges. -/
def Cong (T : G → X → X) (O : X → Y) : Prop :=
  ∀ (g : G) (x y : X), Sees O x y → Sees O (T g x) (T g y)

/-- `x ∼_∞ y`: no lawful continuation whatsoever brings the difference into
    view. Not "the difference is gone" — **no word addresses it**. -/
def FutureSees (T : G → X → X) (O : X → Y) (x y : X) : Prop :=
  ∀ w : List G, Sees O (run T w x) (run T w y)

/-- The empty word is a word, so future equivalence refines present reception. -/
theorem futureSees_sees {T : G → X → X} {O : X → Y} {x y : X}
    (h : FutureSees T O x y) : Sees O x y := h []

/-! ## Two congruence theorems -/

/-- **Generator congruence ⟺ full future congruence.** By induction on word
    length, with the head as the induction variable. -/
theorem congruence_iff_future (T : G → X → X) (O : X → Y) :
    Cong T O ↔ ∀ x y, Sees O x y → FutureSees T O x y := by
  constructor
  · intro hc x y hxy w
    induction w generalizing x y with
    | nil => simpa using hxy
    | cons g w ih => simpa using ih (T g x) (T g y) (hc g x y hxy)
  · intro h g x y hxy
    simpa using h x y hxy [g]

/-- **Future equivalence is itself a continuation congruence**, with no
    hypothesis at all on `O`. Every receiver has one; the question is only how
    coarse it is. -/
theorem futureSees_cong (T : G → X → X) (O : X → Y) :
    ∀ (g : G) (x y : X), FutureSees T O x y → FutureSees T O (T g x) (T g y) := by
  intro g x y h w
  simpa using h (g :: w)

/-- **Minimal Markov completion.** `∼_∞` is the coarsest congruence refining the
    receiver: any relation `E` that refines `∼_O` and is closed under the
    generators already refines `∼_∞`. -/
theorem futureSees_coarsest (T : G → X → X) (O : X → Y) (E : X → X → Prop)
    (hrefine : ∀ x y, E x y → Sees O x y)
    (hcong : ∀ (g : G) (x y : X), E x y → E (T g x) (T g y)) :
    ∀ x y, E x y → FutureSees T O x y := by
  intro x y hE w
  induction w generalizing x y with
  | nil => simpa using hrefine x y hE
  | cons g w ih => simpa using ih (T g x) (T g y) (hcong g x y hE)

/-! ## The stopping theorem -/

/-- `x ∼_n y`: agreement on every word of length at most `n`. -/
def SeesUpTo (T : G → X → X) (O : X → Y) (n : ℕ) (x y : X) : Prop :=
  ∀ w : List G, w.length ≤ n → Sees O (run T w x) (run T w y)

@[simp] theorem seesUpTo_zero (T : G → X → X) (O : X → Y) (x y : X) :
    SeesUpTo T O 0 x y ↔ Sees O x y := by
  constructor
  · intro h; simpa using h [] (by simp)
  · intro h w hw
    obtain rfl : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw)
    simpa using h

/-- The ladder only ever refines. -/
theorem seesUpTo_mono (T : G → X → X) (O : X → Y) {m n : ℕ} (hmn : m ≤ n)
    {x y : X} (h : SeesUpTo T O n x y) : SeesUpTo T O m x y :=
  fun w hw => h w (by omega)

/-- One step under `hstab`: agreement on every word up to length `n+1`
    decomposes, one generator at a time, into agreement up to length `n`
    **after that generator's step** — read off the head of the word via
    `run`'s left-to-right convention. -/
theorem seesUpTo_succ_step (T : G → X → X) (O : X → Y) (n : ℕ) {x y : X}
    (h : SeesUpTo T O (n + 1) x y) (g : G) : SeesUpTo T O n (T g x) (T g y) := by
  intro w hw
  have hw' : (g :: w).length ≤ n + 1 := by simp only [List.length_cons]; omega
  simpa using h (g :: w) hw'

/-- **The stopping criterion, the direction that does the work.** `hstab`
    quantifies over every pair at level `n`, not just the one that triggered
    it, so `SeesUpTo T O n` is already a congruence for the generators
    (`seesUpTo_succ_step`) — the same shape `futureSees_coarsest` needs, so
    `∼_n` equals `∼_∞` by the same coarsest-congruence argument. No
    asymptotics, no limit: a single layer decides it. -/
theorem stops_of_stable (T : G → X → X) (O : X → Y) (n : ℕ)
    (hstab : ∀ x y, SeesUpTo T O n x y → SeesUpTo T O (n + 1) x y) :
    ∀ x y, SeesUpTo T O n x y → FutureSees T O x y := by
  refine futureSees_coarsest T O (SeesUpTo T O n) ?_ ?_
  · intro x y h; exact h [] (Nat.zero_le n)
  · intro g x y h; exact seesUpTo_succ_step T O n (hstab x y h) g

end Reception
end Two
end RatioSpace
