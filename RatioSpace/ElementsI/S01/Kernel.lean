/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S05.Depth
/-!
  **The kernel's fourth rule is not independent.**

  A minimal kernel has four rules:

    K1  exact ordered relational contact exists;
    K2  contact admits the two oriented mediant inheritances L and R;
    K3  successive inheritance acts on the entire inherited occurrence/history;
    K4  reception is a typed map of that exact structure.

  The decisive test for K3: *if the positive L/R action is free, a decoder
  recovers the whole continuation word from the current exact frame, so history
  is not an independent register* (positive-history definability; Elements I,
  Standard Result 3.1 and Definition 3.5).

  **It is a theorem.** `addressed_injective` below, from K1 and K2 alone.

  The mechanism is small. No matrix factorisation and no
  run-length decomposition: prepending a letter adds one component of the
  address to the other (`r_cons_false`, `r_cons_true`), so the two components
  are never equal after any letter, and **which one is larger names the letter.**
  The head is therefore readable off the address, and stripping it is one
  subtraction. History is not stored; it is the address.
-/

namespace RatioSpace
namespace Kernel

open Pres Frame

/-- After any letter the two components differ, and the larger one names the
    letter: `true` raises `p`, `false` raises `q`. -/
theorem head_readable (b : Bool) (w : Word) :
    (b = true → (Frame.r w).q < (Frame.r (b :: w)).p ∧ (Frame.r (b :: w)).q = (Frame.r w).q) ∧
    (b = false → (Frame.r (b :: w)).p < (Frame.r (b :: w)).q) := by
  obtain ⟨hp, hq⟩ := r_pos w
  constructor
  · intro hb; subst hb
    obtain ⟨k1, k2⟩ := r_cons_true w
    exact ⟨by omega, k2⟩
  · intro hb; subst hb
    obtain ⟨k1, k2⟩ := r_cons_false w
    omega

/-- The address of a nonempty word never has equal components; the empty word's
    does. So `p = q` decides emptiness. -/
theorem eq_components_iff_nil (w : Word) : (Frame.r w).p = (Frame.r w).q ↔ w = [] := by
  constructor
  · intro h
    cases w with
    | nil => rfl
    | cons b v =>
        exfalso
        obtain ⟨hp, hq⟩ := r_pos v
        cases b
        · obtain ⟨k1, k2⟩ := r_cons_false v; omega
        · obtain ⟨k1, k2⟩ := r_cons_true v; omega
  · intro h; subst h; rfl

/-- **K3 is derived, not primitive.** The addressed relation is injective on
    words: distinct continuation histories reach distinct exact addresses, so
    the full history is recoverable from the current address and needs no
    separate register.

    This is positive-history definability (Elements I, Standard Result 3.1). -/
theorem addressed_injective : ∀ w v : Word, Frame.r w = Frame.r v → w = v := by
  intro w
  induction w with
  | nil =>
      intro v h
      have : (Frame.r v).p = (Frame.r v).q := by rw [← h]; rfl
      exact ((eq_components_iff_nil v).mp this).symm
  | cons b u ih =>
      intro v h
      cases v with
      | nil =>
          exfalso
          have : (Frame.r (b :: u)).p = (Frame.r (b :: u)).q := by rw [h]; rfl
          exact absurd ((eq_components_iff_nil _).mp this) (by simp)
      | cons c t =>
          obtain ⟨hpu, hqu⟩ := r_pos u
          obtain ⟨hpt, hqt⟩ := r_pos t
          have hbc : b = c := by
            cases b <;> cases c
            · rfl
            · exfalso
              obtain ⟨k1, k2⟩ := r_cons_false u
              obtain ⟨m1, m2⟩ := r_cons_true t
              have e1 : (Frame.r (false :: u)).p = (Frame.r (true :: t)).p := by rw [h]
              have e2 : (Frame.r (false :: u)).q = (Frame.r (true :: t)).q := by rw [h]
              omega
            · exfalso
              obtain ⟨k1, k2⟩ := r_cons_true u
              obtain ⟨m1, m2⟩ := r_cons_false t
              have e1 : (Frame.r (true :: u)).p = (Frame.r (false :: t)).p := by rw [h]
              have e2 : (Frame.r (true :: u)).q = (Frame.r (false :: t)).q := by rw [h]
              omega
            · rfl
          subst hbc
          have hrec : Frame.r u = Frame.r t := by
            cases b
            · obtain ⟨k1, k2⟩ := r_cons_false u
              obtain ⟨m1, m2⟩ := r_cons_false t
              have e1 : (Frame.r (false :: u)).p = (Frame.r (false :: t)).p := by rw [h]
              have e2 : (Frame.r (false :: u)).q = (Frame.r (false :: t)).q := by rw [h]
              have hp : (Frame.r u).p = (Frame.r t).p := by omega
              have hq : (Frame.r u).q = (Frame.r t).q := by omega
              cases hru : Frame.r u; cases hrt : Frame.r t
              rw [hru, hrt] at hp hq
              simp_all
            · obtain ⟨k1, k2⟩ := r_cons_true u
              obtain ⟨m1, m2⟩ := r_cons_true t
              have e1 : (Frame.r (true :: u)).p = (Frame.r (true :: t)).p := by rw [h]
              have e2 : (Frame.r (true :: u)).q = (Frame.r (true :: t)).q := by rw [h]
              have hp : (Frame.r u).p = (Frame.r t).p := by omega
              have hq : (Frame.r u).q = (Frame.r t).q := by omega
              cases hru : Frame.r u; cases hrt : Frame.r t
              rw [hru, hrt] at hp hq
              simp_all
          rw [ih t hrec]

end Kernel
end RatioSpace
