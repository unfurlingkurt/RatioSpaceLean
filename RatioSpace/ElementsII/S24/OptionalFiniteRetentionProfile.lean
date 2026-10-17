/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S24.Lifecycle
/-!
  Gap G2-28 — Elements II §24, Receiver Declaration 24.16, Optional finite
  retention profile.

  **Book statement.** *"A finite receiver may specialize Θ by declaring:
  H_Θ ∈ ℕ₀, a finite phase set P_Θ, an allowed phase window W_Θ^ph ⊆ P_Θ, an
  allowed lift-status set W_Θ^lift ⊆ 𝖫, and the exact gates
  g_ph = 1 ⟺ θ_Θ(𝖹_f^{[m]}) ∈ W_Θ^ph, g_lift = 1 ⟺ Lift_sib(f) ∈ W_Θ^lift,
  g_read = 1 ⟺ a_arch(f; n_m) ≤ H_Θ."*

  `finiteProfile` (`Lifecycle.lean`) takes the phase datum in an
  arbitrary type `Ph`, in which the finiteness of `P_Θ` is not declared.

  **The declaration.** A record `G2_28.FiniteProfile` whose phase type
  carries an exact finite enumeration (a duplicate-free list containing every
  phase), so `P_Θ` is finite as declared while the phase datum keeps its own
  named type (Definition 24.10: "The datum θ_Θ must be named by type"; a
  closure residue and an admission phase are not one type because both are
  finite). The window `W_Θ^ph` and the lift set `W_Θ^lift` are read off as
  finite lists, and the three gates are proved to be the book's three
  membership / bound tests. The declaration's `Retention` is definitionally the
  existing `finiteProfile`, so every theorem proved there applies unchanged.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_28

open RatioSpace.Two RatioSpace.Two.Incidence RatioSpace.Two.Lifecycle

/-- A declared finite phase set `P_Θ` on the named phase type `Ph`: a
    duplicate-free list that contains every phase. -/
structure FinPhaseSet (Ph : Type) where
  elems : List Ph
  nodup : elems.Nodup
  complete : ∀ p : Ph, p ∈ elems

/-- The lift-status set `𝖫` is finite: its five statuses, listed. -/
def liftElems : List LiftStatus :=
  [.notEvaluated, .unresolvedNone, .unresolvedMultiple, .determined false, .determined true]

theorem liftElems_complete (l : LiftStatus) : l ∈ liftElems := by
  cases l with
  | notEvaluated => simp [liftElems]
  | unresolvedNone => simp [liftElems]
  | unresolvedMultiple => simp [liftElems]
  | determined b => cases b <;> simp [liftElems]

theorem liftElems_nodup : liftElems.Nodup := by decide

/-- **Receiver Declaration 24.16.** The finite retention profile, every datum
    declared: receiver, socket, admission predicate on the whole packet, the
    finite phase set `P_Θ` with its named phase datum and window `W_Θ^ph`, the
    lift window `W_Θ^lift`, and the capacity `H_Θ`. -/
structure FiniteProfile (P Y Ph St : Type) where
  recv : Receiver P Y
  sock : FaceId → St → ℕ → Bool
  chiAdm : P → Bool
  phases : FinPhaseSet Ph
  theta : P → Ph
  window : Ph → Bool
  liftWindow : LiftStatus → Bool
  H : ℕ

variable {P Y Ph St : Type}

/-- `W_Θ^ph ⊆ P_Θ`, as the finite list of allowed phases. -/
def FiniteProfile.W (D : FiniteProfile P Y Ph St) : List Ph := D.phases.elems.filter D.window

/-- `W_Θ^lift ⊆ 𝖫`, as the finite list of allowed lift statuses. -/
def FiniteProfile.WLift (D : FiniteProfile P Y Ph St) : List LiftStatus := liftElems.filter D.liftWindow

theorem FiniteProfile.W_sub (D : FiniteProfile P Y Ph St) : ∀ p ∈ D.W, p ∈ D.phases.elems :=
  fun _ hp => (List.mem_filter.mp hp).1

theorem FiniteProfile.mem_W (D : FiniteProfile P Y Ph St) (p : Ph) : p ∈ D.W ↔ D.window p = true := by
  unfold FiniteProfile.W
  rw [List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨D.phases.complete p, h⟩⟩

theorem FiniteProfile.mem_WLift (D : FiniteProfile P Y Ph St) (l : LiftStatus) :
    l ∈ D.WLift ↔ D.liftWindow l = true := by
  unfold FiniteProfile.WLift
  rw [List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨liftElems_complete l, h⟩⟩

/-- The declaration as a retention declaration `Θ`: exactly `finiteProfile`. -/
def FiniteProfile.toRetention (D : FiniteProfile P Y Ph St) : Retention P Y Ph St :=
  finiteProfile D.recv D.sock D.chiAdm D.theta D.window D.liftWindow D.H

/-- **Receiver Declaration 24.16, the gates.** At every read, for every packet,
    attaching reference, socket state, lift status and strata:
    `g_ph = 1 ⟺ θ_Θ(𝖹) ∈ W_Θ^ph`, `g_lift = 1 ⟺ Lift_sib ∈ W_Θ^lift`,
    `g_read = 1 ⟺ a_arch ≤ H_Θ`; the admission gate is the declared predicate
    on the complete packet and the socket gate is the exact socket predicate of
    Definition 24.10. -/
theorem finiteProfile_gates [DecidableEq Y] (D : FiniteProfile P Y Ph St) (fid : FaceId) (S : St)
    (Z Zatt : P) (lift : LiftStatus) (k n : ℕ) :
    let g := gateVector D.toRetention fid S Z Zatt lift k n
    (g.ph = true ↔ D.theta Z ∈ D.W) ∧
    (g.lift = true ↔ lift ∈ D.WLift) ∧
    (g.read = true ↔ aArch k n ≤ D.H) ∧
    g.adm = D.chiAdm Z ∧ g.socket = D.sock fid S n ∧
    (g.cls = true ↔ D.recv.equiv Z Zatt) := by
  intro g
  refine ⟨(D.mem_W _).symm, (D.mem_WLift _).symm, ?_, rfl, rfl, ?_⟩
  · change decide (aArch k n ≤ D.H) = true ↔ _
    exact decide_eq_true_iff
  · change decide (D.recv.equiv Z Zatt) = true ↔ _
    exact decide_eq_true_iff

/-- The phase set is finite as declared: its enumeration is duplicate-free and
    exhausts the phase type, and the window is a sub-list of it. -/
theorem finiteProfile_phase_finite (D : FiniteProfile P Y Ph St) :
    D.phases.elems.Nodup ∧ (∀ p : Ph, p ∈ D.phases.elems) ∧ (∀ p ∈ D.W, p ∈ D.phases.elems) :=
  ⟨D.phases.nodup, D.phases.complete, D.W_sub⟩

#print axioms liftElems_complete
#print axioms liftElems_nodup
#print axioms FiniteProfile.W_sub
#print axioms FiniteProfile.mem_W
#print axioms FiniteProfile.mem_WLift
#print axioms finiteProfile_gates
#print axioms finiteProfile_phase_finite

end G2_28
end Gaps
end RatioSpace
