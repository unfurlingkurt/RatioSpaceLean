/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S01.Kernel
/-!
  **The machine.**

  Assembled from pieces already proved elsewhere and never named as one thing.

    * **State** is an exact presentation, the address. Nothing else is kept.
    * **Program** is a word in two instructions, `L` and `R` (`false`, `true`).
    * **Semantics** is inheritance by mediant, as the prepend (Euclidean)
      action: putting `R` in front of a program sends its state `p:q` to
      `(p+q):q`, putting `L` in front sends it to `p:(p+q)`. That is
      `r_cons_true` and `r_cons_false`. So, read as a sequence of operations on
      the state, a program runs from its last letter to its first, the reverse
      of the walk that builds the frame: `run [false, true] = 2:3`, while
      applying `R` to `run [false] = 1:2` gives `3:2`.
    * **Decoding** reads the program back off the final state by subtraction:
      whichever component is larger names the instruction, and the difference
      is the previous state.

  **One theorem carries the whole claim.** `decode_run`: decoding the state a
  program reaches returns the program, exactly. That single statement is
  reversibility (every step can be undone from the state alone) and
  state-equals-history (the full record is recoverable from the current state,
  so no separate memory exists) at once. They were never two facts.

  Everything is computable and runs under `#eval`. Choice-free.
-/

namespace RatioSpace
namespace Machine

open Pres Frame

/-- A program: a word of `L` (`false`) and `R` (`true`) instructions. -/
abbrev Program := Word

/-- Run a program from the empty frame. The result is the whole state. -/
def run (w : Program) : Pres := Frame.r w

/-- Instruction semantics, `R`, as the prepend action: `R` put in front of `w`. -/
theorem run_R (w : Program) :
    (run (true :: w)).p = (run w).p + (run w).q ∧ (run (true :: w)).q = (run w).q :=
  r_cons_true w

/-- Instruction semantics, `L`, as the prepend action: `L` put in front of `w`. -/
theorem run_L (w : Program) :
    (run (false :: w)).p = (run w).p ∧ (run (false :: w)).q = (run w).p + (run w).q :=
  r_cons_false w

/-- Decode by subtraction. Equal components means nothing was run; otherwise
    the larger component names the instruction and the difference is the state
    before it. Fuel bounds the recursion and is never what decides the answer. -/
def decodeFuel : ℕ → ℕ → ℕ → Program
  | 0, _, _ => []
  | n + 1, p, q =>
      if p = q then []
      else if q < p then true :: decodeFuel n (p - q) q
      else false :: decodeFuel n p (q - p)

theorem decodeFuel_run : ∀ (w : Program) (n : ℕ), w.length ≤ n →
    decodeFuel n (run w).p (run w).q = w := by
  intro w
  induction w with
  | nil =>
      intro n _
      cases n with
      | zero => rfl
      | succ n => rfl
  | cons b w ih =>
      intro n hn
      obtain ⟨hp, hq⟩ := r_pos w
      cases n with
      | zero => simp only [List.length_cons] at hn; omega
      | succ n =>
          have hn' : w.length ≤ n := by simp only [List.length_cons] at hn; omega
          cases b with
          | true =>
              obtain ⟨k1, k2⟩ := run_R w
              have hne : (run (true :: w)).p ≠ (run (true :: w)).q := by
                unfold run at *; omega
              have hlt : (run (true :: w)).q < (run (true :: w)).p := by
                unfold run at *; omega
              simp only [decodeFuel]
              rw [if_neg hne, if_pos hlt]
              refine congrArg (List.cons true) ?_
              have hsub : (run (true :: w)).p - (run (true :: w)).q = (run w).p := by
                unfold run at *; omega
              rw [hsub, k2]
              exact ih n hn'
          | false =>
              obtain ⟨k1, k2⟩ := run_L w
              have hne : (run (false :: w)).p ≠ (run (false :: w)).q := by
                unfold run at *; omega
              have hlt : ¬ (run (false :: w)).q < (run (false :: w)).p := by
                unfold run at *; omega
              simp only [decodeFuel]
              rw [if_neg hne, if_neg hlt]
              refine congrArg (List.cons false) ?_
              have hsub : (run (false :: w)).q - (run (false :: w)).p = (run w).q := by
                unfold run at *; omega
              rw [hsub, k1]
              exact ih n hn'

/-- A program is never longer than the sum of its state's components, so the
    natural fuel always suffices. -/
theorem length_le_sum : ∀ w : Program, w.length ≤ (run w).p + (run w).q := by
  intro w
  induction w with
  | nil => exact Nat.zero_le _
  | cons b w ih =>
      obtain ⟨hp, hq⟩ := r_pos w
      cases b
      · obtain ⟨k1, k2⟩ := run_L w
        simp only [List.length_cons]; unfold run at *; omega
      · obtain ⟨k1, k2⟩ := run_R w
        simp only [List.length_cons]; unfold run at *; omega

/-- Decode a state. -/
def decode (A : Pres) : Program := decodeFuel (A.p + A.q) A.p A.q

/-- **The machine theorem.** Decoding the state a program reaches returns the
    program. Reversibility and state-equals-history are this one statement. -/
theorem decode_run (w : Program) : decode (run w) = w :=
  decodeFuel_run w _ (length_le_sum w)

/-- Corollary: distinct programs reach distinct states. Nothing is ever lost,
    so nothing ever needs to be stored. -/
theorem run_injective (u v : Program) (h : run u = run v) : u = v := by
  have := congrArg decode h
  rwa [decode_run, decode_run] at this

/-! ## The answer is already in the state

The frame a program reaches carries a second column, and contact holds by
construction. That column is the solution to `p·x ≡ 1 (mod q)`. No search, no
extra computation: the machine's state after decoding *is* the certificate. -/

/-- The frame the program leaves behind. -/
def frameOf (w : Program) : Frame := Frame.walk Frame.empty w

theorem inverse_in_state (w : Program) :
    (run w).p * (frameOf w).minus.q = (run w).q * (frameOf w).minus.p + 1 := by
  have h := (frameOf w).contact
  unfold Contact at h
  unfold run Frame.r Frame.addressed Frame.mid Pres.mediant frameOf
  dsimp only
  unfold frameOf at h
  rw [Nat.add_mul, Nat.add_mul, h]
  ring

/-- Intended as the modular inverse of `a` mod `b`, read off the state. Unproved:
    no correctness theorem is stated for it here, and it can only be right when
    `Nat.gcd a b = 1` (for `modInv 6 9` it returns `2`, and `6 * 2 = 12 ≡ 3`
    mod `9`). The proved statement is `modInvFast_sound`, about `modInvFast`. -/
def modInv (a b : ℕ) : ℕ := (frameOf (decodeFuel (a + b) a b)).minus.q


/-! ## Run-length instructions

A single-letter program for a real key is longer than the universe is old. One
instruction meaning "do `R` `k` times" fixes that without changing the machine:
`R^k` has a closed form, so it is one step of arithmetic rather than `k` steps
of walking. This is the Euclidean algorithm, stated as this machine. -/

/-- A run: an instruction and a repeat count. -/
abbrev RunI := Bool × ℕ
abbrev RLProgram := List RunI

/-- Unfold a run-length program into single letters. -/
def expand : RLProgram → Program
  | [] => []
  | (b, k) :: rs => List.replicate k b ++ expand rs

/-- The frame's four entries, `(C₊, C₋)` read off componentwise. Plain numbers,
    so a run can be applied in closed form. -/
structure Quad where
  pp : ℕ
  qp : ℕ
  pm : ℕ
  qm : ℕ
deriving DecidableEq, Repr

namespace Quad

def ofFrame (F : Frame) : Quad := ⟨F.plus.p, F.plus.q, F.minus.p, F.minus.q⟩

/-- `R^k`: the mediant lands in `C₋` `k` times, so `C₋ ↦ C₋ + k·C₊`. -/
def R (x : Quad) (k : ℕ) : Quad := ⟨x.pp, x.qp, x.pm + k * x.pp, x.qm + k * x.qp⟩

/-- `L^k`: `C₊ ↦ C₊ + k·C₋`. -/
def L (x : Quad) (k : ℕ) : Quad := ⟨x.pp + k * x.pm, x.qp + k * x.qm, x.pm, x.qm⟩

def run : Quad → RLProgram → Quad
  | x, [] => x
  | x, (b, k) :: rs => run (if b then x.R k else x.L k) rs

/-- Contact, on the four entries. -/
def contact (x : Quad) : Prop := x.pp * x.qm = x.qp * x.pm + 1

end Quad

theorem walk_replicate (F : Frame) (b : Bool) (k : ℕ) :
    Quad.ofFrame (Frame.walk F (List.replicate k b)) =
      (if b then (Quad.ofFrame F).R k else (Quad.ofFrame F).L k) := by
  induction k generalizing F with
  | zero =>
      cases b <;> simp only [Quad.R, Quad.L, Quad.ofFrame, Nat.zero_mul, Nat.add_zero,
        List.replicate_zero, if_true, if_false, Bool.false_eq_true] <;> rfl
  | succ k ih =>
      cases b with
      | true =>
          change Quad.ofFrame (Frame.walk (Frame.stepR F) (List.replicate k true)) = _
          rw [ih (Frame.stepR F)]
          simp only [if_true, Quad.R, Quad.ofFrame, Frame.stepR, Frame.mid, Pres.mediant,
            Quad.mk.injEq]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring
      | false =>
          change Quad.ofFrame (Frame.walk (Frame.stepL F) (List.replicate k false)) = _
          rw [ih (Frame.stepL F)]
          simp only [Bool.false_eq_true, if_false, Quad.L, Quad.ofFrame, Frame.stepL,
            Frame.mid, Pres.mediant, Quad.mk.injEq]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring

/-- **Same machine.** Running a run-length program in closed form gives exactly
    the frame the single-letter machine reaches on its expansion. Nothing is
    approximated and nothing is skipped; the steps are only counted faster. -/
theorem same_machine (rs : RLProgram) (F : Frame) :
    Quad.run (Quad.ofFrame F) rs = Quad.ofFrame (Frame.walk F (expand rs)) := by
  induction rs generalizing F with
  | nil => rfl
  | cons r rs ih =>
      obtain ⟨b, k⟩ := r
      have hw : ∀ (u v : Program) (G : Frame),
          Frame.walk G (u ++ v) = Frame.walk (Frame.walk G u) v := by
        intro u v G; unfold Frame.walk; exact List.foldl_append
      change Quad.run (if b then (Quad.ofFrame F).R k else (Quad.ofFrame F).L k) rs =
        Quad.ofFrame (Frame.walk F (List.replicate k b ++ expand rs))
      rw [hw, ← ih, walk_replicate]

theorem run_contact : ∀ (rs : RLProgram) (x : Quad), x.contact → (Quad.run x rs).contact := by
  intro rs
  induction rs with
  | nil => intro x h; exact h
  | cons r rs ih =>
      intro x h
      obtain ⟨b, k⟩ := r
      apply ih
      unfold Quad.contact at *
      cases b
      · simp only [Bool.false_eq_true, if_false, Quad.L]
        rw [Nat.add_mul, Nat.add_mul, h]; ring
      · simp only [if_true, Quad.R]
        rw [Nat.mul_add, Nat.mul_add, h]; ring

/-- The certificate: in any frame in contact, the mediant's `p` times `C₋.q` is
    one more than a multiple of the mediant's `q`. -/
theorem cert (x : Quad) (hc : x.contact) :
    (x.pp + x.pm) * x.qm = (x.qp + x.qm) * x.pm + 1 := by
  unfold Quad.contact at hc
  rw [Nat.add_mul, Nat.add_mul, hc]; ring

/-- Run-length decode: the whole run of equal instructions at once. -/
def decodeRLFuel : ℕ → ℕ → ℕ → RLProgram
  | 0, _, _ => []
  | n + 1, p, q =>
      if p = q then []
      else if q < p then
        (true, (p - 1) / q) :: decodeRLFuel n (p - (p - 1) / q * q) q
      else
        (false, (q - 1) / p) :: decodeRLFuel n p (q - (q - 1) / p * p)

/-- Fast modular inverse. It returns an answer only after checking the state it
    reached really is `a:b`, and that check is what `modInvFast_sound` needs. -/
def modInvFast (a b : ℕ) : Option ℕ :=
  let x := Quad.run ⟨1, 0, 0, 1⟩ (decodeRLFuel (a + b) a b)
  if x.pp + x.pm = a ∧ x.qp + x.qm = b then some x.qm else none

/-- **Soundness, for every input of every size.** Whatever `modInvFast` returns
    satisfies `a·x = b·y + 1`. Proved from contact alone, so it holds for a
    2048-bit key exactly as it holds for `17:3120`. -/
theorem modInvFast_sound (a b x : ℕ) (h : modInvFast a b = some x) :
    ∃ y, a * x = b * y + 1 := by
  unfold modInvFast at h
  dsimp only at h
  split at h
  · rename_i hc
    obtain ⟨ha, hb⟩ := hc
    injection h with hx
    subst hx
    have key := cert _ (run_contact (decodeRLFuel (a + b) a b) ⟨1, 0, 0, 1⟩ rfl)
    rw [ha, hb] at key
    exact ⟨_, key⟩
  · cases h

end Machine
end RatioSpace
