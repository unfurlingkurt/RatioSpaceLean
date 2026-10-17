/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S24.Lifecycle
/-!
  Elements II Corollary 24.8, received return extends the observer word forward: "If a
  later transported attaching packet returns to an earlier Λ-reception class, the
  history between the two reads is a nonempty positive continuation appended on
  the right, and every earlier event remains in history. The later observer word
  has the earlier observer word as a proper prefix."

  `Lifecycle.lean`'s `return_not_reversal` is the repeated-renewal form `w u^r`
  only; `OneStepRenewal` and `IntervalRenewal` take arbitrary packets `Z` and word
  readings `wO`, with no relation between the continuations at `p` and `q`.

  This file settles which reading the corollary needs, by computing both:
  * **Reading 1** (the receiver's retained continuation only extends, which is what
    Proposition 24.3's "appends one lawful generator" and the corollary's own proof,
    "only right-appended positive continuation", say): the corollary holds for
    one-step and interval renewal. A per-read step form (each read appends one
    generator or none, the `retained-no-advance` case of Definition 24.12) implies
    it.
  * **Reading 2** (a later trail need not extend an earlier one): the corollary's
    prefix sentence is false, by an exact witness of an interval renewal whose
    later observer word does not have the earlier as a prefix.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_23

open RatioSpace.Two RatioSpace.Two.Lifecycle Mat2 Word

/-- **Reading 1.** The retained continuations only extend: `u_f^{[p]}` is a prefix
    of `u_f^{[q]}` whenever `p ≤ q`. -/
def G23Extends (u : ℕ → Word) : Prop := ∀ p q, p ≤ q → u p <+: u q

/-- Each read keeps the trail or appends one lawful generator (Proposition 24.3's
    step; Definition 24.12's `retained-no-advance` is the first disjunct). -/
def G23Steps (u : ℕ → Word) : Prop := ∀ m, u (m + 1) = u m ∨ ∃ g : Bool, u (m + 1) = u m ++ [g]

/-- The step form gives Reading 1. -/
theorem g23_steps_extends (u : ℕ → Word) (h : G23Steps u) : G23Extends u := by
  intro p q hpq
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  clear hpq
  induction d with
  | zero => exact List.prefix_rfl
  | succ d ih =>
    refine ih.trans ?_
    change u (p + d) <+: u (p + d + 1)
    rcases h (p + d) with he | ⟨g, he⟩
    · rw [he]
    · rw [he]; exact List.prefix_append _ _

/-- **Corollary 24.8 for interval renewal, under Reading 1.** If the packets'
    observer words are `w_{xs} v_f^{[0]} u_f^{[m]}` and the trail only extends,
    then an interval renewal from `p` to `q` has: the later observer word equal to
    the earlier followed by a nonempty positive word `d` (no event removed, no
    inverse generator: `d` is a word in `L, R`), the receiver matrix multiplied on
    the right by `G(d)`, the earlier word a proper prefix of the later, the two
    matrices different, the receptions equal, and any word reading that returns
    across the renewal not injective. -/
theorem g23_interval_return_not_reversal {P Y : Type} (Λ : Receiver P Y) (Z : ℕ → P)
    (wO : P → Word) (wx : Word) (s : Bool) (v0 : Word) (u : ℕ → Word) (hu : G23Extends u)
    (hw : ∀ m, wO (Z m) = receiverWord wx s (v0 ++ u m)) (p q : ℕ)
    (hR : IntervalRenewal Λ Z wO p q) :
    (∃ d : Word, d ≠ [] ∧ wO (Z q) = wO (Z p) ++ d ∧ G (wO (Z q)) = G (wO (Z p)) * G d) ∧
    wO (Z p) <+: wO (Z q) ∧ wO (Z q) ≠ wO (Z p) ∧
    G (wO (Z q)) ≠ G (wO (Z p)) ∧
    Λ.recv (Z q) = Λ.recv (Z p) ∧
    ∀ {α : Type} (κ : Word → α), κ (wO (Z q)) = κ (wO (Z p)) → ¬ Function.Injective κ := by
  obtain ⟨hpq, heq, hne⟩ := hR
  obtain ⟨d, hd⟩ := hu p q (Nat.le_of_lt hpq)
  have hqd : wO (Z q) = wO (Z p) ++ d := by
    rw [hw q, hw p, ← hd]
    unfold receiverWord
    rw [List.append_assoc (wx ++ [s]) (v0 ++ u p) d, List.append_assoc v0 (u p) d]
  have hdne : d ≠ [] := by
    rintro rfl
    exact hne (by rw [hqd, List.append_nil])
  refine ⟨⟨d, hdne, hqd, by rw [hqd, G_append]⟩, ⟨d, hqd.symm⟩, hne, ?_, heq.2.2,
    fun κ hκ hinj => hne (hinj hκ)⟩
  rw [hqd]
  exact no_raw_matrix_return _ _ hdne

/-- **Corollary 24.8 for one-step renewal, under Reading 1.** -/
theorem g23_onestep_return_not_reversal {P Y : Type} (Λ : Receiver P Y) (Z : ℕ → P)
    (wO : P → Word) (wx : Word) (s : Bool) (v0 : Word) (u : ℕ → Word) (hu : G23Extends u)
    (hw : ∀ m, wO (Z m) = receiverWord wx s (v0 ++ u m)) (p : ℕ)
    (hR : OneStepRenewal Λ Z wO p) :
    (∃ d : Word, d ≠ [] ∧ wO (Z (p + 1)) = wO (Z p) ++ d ∧ G (wO (Z (p + 1))) = G (wO (Z p)) * G d) ∧
    wO (Z p) <+: wO (Z (p + 1)) ∧ wO (Z (p + 1)) ≠ wO (Z p) ∧
    G (wO (Z (p + 1))) ≠ G (wO (Z p)) ∧
    Λ.recv (Z (p + 1)) = Λ.recv (Z p) ∧
    ∀ {α : Type} (κ : Word → α), κ (wO (Z (p + 1))) = κ (wO (Z p)) → ¬ Function.Injective κ :=
  g23_interval_return_not_reversal Λ Z wO wx s v0 u hu hw p (p + 1) ⟨Nat.lt_succ_self p, hR.1, hR.2⟩

/-- A receiver that reads nothing: every packet readable, one reception. -/
def g23ConstRecv (P : Type) : Receiver P Unit where
  readable := fun _ => true
  recv := fun _ => .value ()
  declaredTag := fun _ => false
  reads := []

/-- The trail of the Reading 2 witness: `ε`, then `L`, then `R`. -/
def g23SwapTrail (m : ℕ) : Word := if m = 1 then [false] else if m = 2 then [true] else []

/-- **Reading 2 breaks the corollary.** With a trail `ε, L, R` that does not extend,
    at any parent word and hand, the packets `w_{xs} u^{[m]}` give an interval
    renewal from `1` to `2` for a declared receiver, and the later observer word
    does not have the earlier as a prefix. So the corollary's prefix sentence holds
    for one-step and interval renewal only under Reading 1. -/
theorem g23_unconstrained_trail_breaks (wx : Word) (s : Bool) :
    g23SwapTrail 0 = [] ∧ ¬ G23Extends g23SwapTrail ∧
    IntervalRenewal (g23ConstRecv Word) (fun m => receiverWord wx s (g23SwapTrail m)) id 1 2 ∧
    ¬ (receiverWord wx s (g23SwapTrail 1) <+: receiverWord wx s (g23SwapTrail 2)) := by
  have hnp : ¬ (receiverWord wx s [false] <+: receiverWord wx s [true]) := by
    rintro ⟨t, ht⟩
    unfold receiverWord at ht
    rw [List.append_assoc] at ht
    exact Bool.noConfusion (List.cons.inj (List.append_cancel_left ht : false :: t = [true])).1
  refine ⟨rfl, fun h => ?_, ⟨by decide, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩, fun he => hnp ?_⟩, hnp⟩
  · obtain ⟨t, ht⟩ := h 1 2 (by decide)
    exact Bool.noConfusion (List.cons.inj (ht : false :: t = [true])).1
  · exact ⟨[], by rw [List.append_nil]; exact he.symm⟩

#print axioms g23_steps_extends
#print axioms g23_interval_return_not_reversal
#print axioms g23_onestep_return_not_reversal
#print axioms g23_unconstrained_trail_breaks

end G2_23
end Gaps
end RatioSpace
