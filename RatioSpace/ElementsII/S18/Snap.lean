/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S17.Terminal
/-!
  **§18 — The coherent snap.**

  Four items: Definition 18.1, Theorems 18.2 and 18.3, and Separation Rule 18.4.

  Nothing here is a new object. Definition 18.1's boxed pair is
  `(Cand_{τ,h}(x*), R)`, and both components are already built: the survivor
  record is what `crystallize` (Def 17.6) returns, and `R` is Def 17.2's
  `Report`. The snap is their pairing, and it is partial for exactly the reason
  `crystallize` is — the book says outright that the map "is undefined on the
  other two terminal strata".
-/

namespace RatioSpace
namespace Two
namespace Snap

open Mat2 Word Frame Pres RatioSpace Advance Accumulation Terminal

/-! ## Definition 18.1 — Complete coherent snap record -/

/-- **Definition 18.1.** `Snap_𝒬(R) = (Cand_{τ,h}(x*), R)`.

    The first component is the occurrence-indexed realization of the complete
    Elements I survivor record; the second retains the exact terminal
    comparison, the full carrier trace, and **every nonwinning alternative**.
    Partial by construction: `crystallize` is defined exactly on the singleton
    stratum, so the snap is too, with no case split written anywhere. -/
def snap {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    Option (Cand EvalAux × Report RawAux EvalAux h) :=
  (crystallize pol X0 hX0 hh evalLedger).map
    (fun x => (x, Report.of pol X0 hX0 hh evalLedger))

/-! ## Theorem 18.2 — Snap commits one complete record -/

/-- **Theorem 18.2, definedness.** The snap is defined exactly where the
    crystallization is, which is exactly the singleton stratum. `Option.map`
    carries this with no hypotheses at all — in particular none of the `Nodup`
    obligations Theorem 17.7's own statement needs. -/
@[simp] theorem snap_isSome_iff {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    (snap pol X0 hX0 hh evalLedger).isSome
      = (crystallize pol X0 hX0 hh evalLedger).isSome := by
  unfold snap
  cases crystallize pol X0 hX0 hh evalLedger <;> rfl

/-- **Theorem 18.2, "one complete record".** Whatever the snap commits, its
    second component is the *whole* report — the terminal comparison, the full
    trace, and every nonwinning alternative. Nothing is discarded on the way
    out, which is the half of 18.2 that says the answer is not reduced. -/
theorem snap_retains_report {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux))
    {p : Cand EvalAux × Report RawAux EvalAux h}
    (hp : snap pol X0 hX0 hh evalLedger = some p) :
    p.2 = Report.of pol X0 hX0 hh evalLedger := by
  unfold snap at hp
  cases hc : crystallize pol X0 hX0 hh evalLedger with
  | none => rw [hc] at hp; exact absurd hp (by simp)
  | some x =>
      rw [hc] at hp
      simp only [Option.map_some, Option.some.injEq] at hp
      exact (hp ▸ rfl)

/-- **Theorem 18.2, the negative half.** *"It does not reduce the answer to
    `π_r(x*)`, `C^{(O)}_{h-1}(x*)`, a closure class, or any other partial
    reading."*

    A closure class cannot be the committed record, and the witness is already
    in the tree: two occurrences from one seed share a closure class **and** a
    winding while differing in identifier and in word. A snap that committed the
    class would have thrown away what the archive kept. -/
theorem closure_class_is_not_the_record (id0 : QuestionId) (seed : History) :
    psi12 (proposal id0 seed [true, false]).fullWord
        = psi12 (proposal id0 seed [false, true]).fullWord ∧
      (proposal id0 seed [true, false]).id ≠ (proposal id0 seed [false, true]).id := by
  obtain ⟨hpsi, _, hid, _⟩ := Conservation.closure_equal_occurrences_distinct id0 seed
  exact ⟨hpsi, hid⟩

/-! ## Theorem 18.3 — Snap is a cycle-boundary operation, outside the domain of the one-tick map -/

/-- **Theorem 18.3.** The existence of a snap does not give
    `𝔎_𝒞(𝔛_{τ,h}) = 𝔛_{τ,h}`, and the book's first proof sentence is the whole
    reason: *"The one-tick map is not defined on the terminal carrier of the
    current question by Definition 11.1."* The terminal carrier sits at the
    horizon, and `Lawful` is `tick < h`, so the advance cannot be applied to it
    at all — a fixed-point equation about it does not even typecheck as a
    claim about `𝔎_𝒞`. Snap commits a terminal result at the declared boundary;
    it asserts no stationary recurrence. -/
theorem terminal_not_lawful {Aux : Type} {h : ℕ} (pol : Policy Aux h)
    (X0 : TickCarrier Aux h) (hX0 : Seeded X0) :
    ¬ Advance.Lawful (Term pol X0 hX0) :=
  Advance.not_lawful_at_horizon _ (Term_tick pol X0 hX0)

/-! ## Separation Rule 18.4 — Snap commits the terminal record; return assimilation replaces
    the observer -/

/-- **Separation Rule 18.4.** The snap determines *which* complete terminal
    record is committed. It does not replace the observer, alter the active
    state, or form the next question: the report it commits carries the terminal
    carrier's **own** observer and question, unchanged, rather than any new one.
    Both are `rfl`, which is the point — there is no step in the snap where a
    replacement could have been introduced. -/
theorem snap_forms_no_new_observer {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    (Report.of pol X0 hX0 hh evalLedger : Report RawAux EvalAux h).observer
      = (Term pol X0 hX0).observer := rfl

theorem snap_forms_no_new_question {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    (Report.of pol X0 hX0 hh evalLedger : Report RawAux EvalAux h).q
      = (Term pol X0 hX0).question := rfl

/-- And the support it reports is the terminal carrier's own active set, so the
    snap alters no active state either. -/
theorem snap_alters_no_active_state {RawAux EvalAux : Type} {h : ℕ} (pol : Policy RawAux h)
    (X0 : TickCarrier RawAux h) (hX0 : Seeded X0) (hh : 0 < h)
    (evalLedger : List (QuestionId × EvalRecord EvalAux)) :
    (Report.of pol X0 hX0 hh evalLedger : Report RawAux EvalAux h).Sh
      = (Term pol X0 hX0).active := rfl

end Snap
end Two
end RatioSpace
