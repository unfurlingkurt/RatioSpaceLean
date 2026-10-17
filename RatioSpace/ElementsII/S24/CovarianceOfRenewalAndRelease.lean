/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S24.Lifecycle
/-!
  Elements II §24, Proposition 24.18, Covariance of renewal and
  release.

  **Book statement.** *"Status: Conditional result. Suppose common-prefix
  transport or complete side exchange carries: the face record and stable
  lifecycle keys bijectively; every receiver trail and read stratum to its
  corresponding transported trail and stratum; ℛ_Λ^face equivariantly to the
  transported receiver; and the socket and all four optional gates to predicates
  with the same Boolean values on corresponding packets. Then receiver
  equivalence, renewal status, gate vectors, active status, release events, and
  archive ages are preserved occurrence-for-occurrence."*
  Proof: *"... The hypotheses preserve the reception equality and each gate
  value. Stable bijections preserve entry and read strata, hence their
  difference a_arch. Definition 24.12 then selects the same lifecycle branch,
  with transported keys and records."*

  **Relation to `covariance_conditional`.** `covariance_conditional` assumes the
  transported gate list equal to the original (`gs' = gs`), all six gates and
  every advance bit included, so its lifecycle preservation is `rw [hg]`; its
  age conjunct is `aArch k n = aArch k n`.

  **Contents.** `Transport Θ Θ'` holds the book's four hypotheses and nothing
  more: (1) an injective carrying of face keys; (2) a carrying of receiver
  words, injective, and of strata that keeps every difference `n − k` for
  `k ≤ n`; (3) an equivariant reception (domain carried, values relabelled
  injectively); (4) the socket and the four optional gate predicates take the
  same Boolean value on corresponding data. From these alone:
  * `age_transport`: archive age is carried (`a_arch` of the carried strata is
    the original age);
  * `class_gate_transport`: the class gate is derived from the reception
    hypothesis (via `covariance_conditional`'s equivalence clause);
  * `gateVector_transport`: the whole gate vector is carried, the readability
    gate through the carried age;
  * `advanced_transport`, `bits_transport`: the advance bit of every read,
    computed from the receiver words, is carried, so the whole list of gate
    vectors and advance bits of a read sequence is carried;
  * `covariance_24_18`: receiver equivalence, one-step renewal status, the
    lifecycle status list, the active Booleans, the release count, the release
    record of each read (with carried key and packet, same failed gates), and
    archive ages, all preserved;
  * `key_transport_injective`: the lifecycle key `(ι_f, m, n)` is carried
    injectively.
  The strata hypothesis is needed as stated (Elements II, Proposition 24.18):
  `shift_keeps_diff` shows every uniform shift of strata satisfies it, and
  `doubling_breaks_age` shows an injective, order-preserving relabelling that
  does not keep differences changes the archive age at every `k < n`.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_30

open RatioSpace.Two RatioSpace.Two.Incidence RatioSpace.Two.Lifecycle

variable {P Y Ph St P' Y' Ph' St' : Type}

/-- **Proposition 24.18's hypotheses.** -/
structure Transport (Θ : Retention P Y Ph St) (Θ' : Retention P' Y' Ph' St')
    (wO : P → Word) (wO' : P' → Word) where
  /-- (1) face and lifecycle keys, carried injectively. -/
  σF : FaceId → FaceId
  σF_inj : Function.Injective σF
  /-- the transported packets, socket states and retained lift statuses. -/
  σ : P → P'
  σS : St → St'
  σL : LiftStatus → LiftStatus
  /-- (2) read and entry strata, carried with their differences. -/
  ν : ℕ → ℕ
  ν_diff : ∀ a b, a ≤ b → ν b - ν a = b - a
  /-- (2) receiver trails and words, carried injectively. -/
  σW : Word → Word
  σW_inj : Function.Injective σW
  word : ∀ Z, wO' (σ Z) = σW (wO Z)
  /-- (3) the reception, carried equivariantly. -/
  τ : RecStat Y → RecStat Y'
  τ_inj : Function.Injective τ
  dom : ∀ Z, Θ'.recv.dom (σ Z) ↔ Θ.recv.dom Z
  recv_eq : ∀ Z, Θ'.recv.recv (σ Z) = τ (Θ.recv.recv Z)
  /-- (4) the socket and the four optional gates take equal values on
      corresponding data. -/
  sock : ∀ fid S n, Θ'.sock (σF fid) (σS S) (ν n) = Θ.sock fid S n
  adm : ∀ Z, Θ'.chiAdm (σ Z) = Θ.chiAdm Z
  ph : ∀ Z, Θ'.window (Θ'.theta (σ Z)) = Θ.window (Θ.theta Z)
  lift : ∀ l, Θ'.chiLift (σL l) = Θ.chiLift l
  read : ∀ Z k n a, Θ'.chiRead (σ Z) (ν k) (ν n) a = Θ.chiRead Z k n a

variable {Θ : Retention P Y Ph St} {Θ' : Retention P' Y' Ph' St'} {wO : P → Word} {wO' : P' → Word}

/-- Archive age is carried. -/
theorem age_transport (T : Transport Θ Θ' wO wO') (k n : ℕ) (hkn : k ≤ n) :
    aArch (T.ν k) (T.ν n) = aArch k n := T.ν_diff k n hkn

/-- Receiver equivalence is carried, from hypothesis (3) alone. -/
theorem equiv_transport (T : Transport Θ Θ' wO wO') (Z Z' : P) :
    Θ'.recv.equiv (T.σ Z) (T.σ Z') ↔ Θ.recv.equiv Z Z' :=
  (covariance_conditional Θ.recv Θ'.recv T.σ T.τ T.τ_inj T.dom T.recv_eq Z Z' [] [] rfl 0 0).1

/-- The class gate is derived from the carried reception. -/
theorem class_gate_transport [DecidableEq Y] [DecidableEq Y'] (T : Transport Θ Θ' wO wO') (Z Zatt : P) :
    decide (Θ'.recv.equiv (T.σ Z) (T.σ Zatt)) = decide (Θ.recv.equiv Z Zatt) :=
  decide_eq_decide.mpr (equiv_transport T Z Zatt)

/-- **The gate vector is carried**: class gate from (3), the other five from
    (4), the readability gate through the carried archive age. -/
theorem gateVector_transport [DecidableEq Y] [DecidableEq Y'] (T : Transport Θ Θ' wO wO')
    (fid : FaceId) (S : St) (Z Zatt : P) (lift : LiftStatus) (k n : ℕ) (hkn : k ≤ n) :
    gateVector Θ' (T.σF fid) (T.σS S) (T.σ Z) (T.σ Zatt) (T.σL lift) (T.ν k) (T.ν n) =
    gateVector Θ fid S Z Zatt lift k n := by
  unfold gateVector
  rw [T.sock, T.adm, T.ph, T.lift, age_transport T k n hkn, T.read, class_gate_transport T Z Zatt]

/-- Whether the receiver history advanced between two reads: the receiver words
    differ. -/
def advancedBy (w : P → Word) (Zp Z : P) : Bool := !(decide (w Zp = w Z))

theorem advanced_transport (T : Transport Θ Θ' wO wO') (Zp Z : P) :
    advancedBy wO' (T.σ Zp) (T.σ Z) = advancedBy wO Zp Z := by
  unfold advancedBy
  rw [T.word, T.word]
  congr 1
  exact decide_eq_decide.mpr ⟨fun h => T.σW_inj h, fun h => by rw [h]⟩

/-- One evaluated read: the packet, the socket state and the read stratum. -/
structure Read (P St : Type) where
  Z : P
  S : St
  n : ℕ

def Transport.readMap (T : Transport Θ Θ' wO wO') (r : Read P St) : Read P' St' := ⟨T.σ r.Z, T.σS r.S, T.ν r.n⟩

/-- The gate vectors and advance bits of a read sequence, the advance bit
    computed from the receiver words of consecutive packets. -/
def bits [DecidableEq Y] (Θ : Retention P Y Ph St) (w : P → Word) (fid : FaceId) (Zatt : P)
    (lift : LiftStatus) (k : ℕ) : P → List (Read P St) → List (Gates × Bool)
  | _, [] => []
  | Zp, r :: rs => (gateVector Θ fid r.S r.Z Zatt lift k r.n, advancedBy w Zp r.Z) :: bits Θ w fid Zatt lift k r.Z rs

/-- **The gate-and-advance list is carried**, derived, not assumed. -/
theorem bits_transport [DecidableEq Y] [DecidableEq Y'] (T : Transport Θ Θ' wO wO') (fid : FaceId)
    (Zatt : P) (lift : LiftStatus) (k : ℕ) :
    ∀ (Zp : P) (rs : List (Read P St)), (∀ r ∈ rs, k ≤ r.n) →
      bits Θ' wO' (T.σF fid) (T.σ Zatt) (T.σL lift) (T.ν k) (T.σ Zp) (rs.map T.readMap) =
      bits Θ wO fid Zatt lift k Zp rs
  | _, [], _ => rfl
  | Zp, r :: rs, hk => by
    change (gateVector Θ' (T.σF fid) (T.σS r.S) (T.σ r.Z) (T.σ Zatt) (T.σL lift) (T.ν k) (T.ν r.n),
        advancedBy wO' (T.σ Zp) (T.σ r.Z)) ::
        bits Θ' wO' (T.σF fid) (T.σ Zatt) (T.σL lift) (T.ν k) (T.σ r.Z) (rs.map T.readMap) = _
    rw [gateVector_transport T fid r.S r.Z Zatt lift k r.n (hk r (List.Mem.head rs)),
      advanced_transport T Zp r.Z,
      bits_transport T fid Zatt lift k r.Z rs (fun r' hr' => hk r' (List.Mem.tail r hr'))]
    rfl

/-- Release records, carried by key and packet. -/
def Transport.relMap (T : Transport Θ Θ' wO wO') (rel : ReleaseRec P) : ReleaseRec P' :=
  ⟨T.σF rel.fid, T.ν rel.n, rel.failed, T.σ rel.packet⟩

/-- **Proposition 24.18.** Under the four hypotheses: receiver equivalence and
    one-step renewal status are preserved; for every read sequence from an
    entry at stratum `k` (every read at or after `k`) the lifecycle status list,
    the active Booleans and the release count are preserved; at every read the
    gate vector is preserved and the release record is the carried release
    record; archive age is preserved. -/
theorem covariance_24_18 [DecidableEq Y] [DecidableEq Y'] (T : Transport Θ Θ' wO wO')
    (fid : FaceId) (Zatt Z0 : P) (lift : LiftStatus) (k : ℕ) (rs : List (Read P St))
    (hk : ∀ r ∈ rs, k ≤ r.n) (prior : List LifeStat) :
    (∀ Z Z', Θ'.recv.equiv (T.σ Z) (T.σ Z') ↔ Θ.recv.equiv Z Z') ∧
    (∀ (Zs : ℕ → P) (p : ℕ), OneStepRenewal Θ'.recv (fun i => T.σ (Zs i)) wO' p ↔ OneStepRenewal Θ.recv Zs wO p) ∧
    life prior (bits Θ' wO' (T.σF fid) (T.σ Zatt) (T.σL lift) (T.ν k) (T.σ Z0) (rs.map T.readMap)) =
      life prior (bits Θ wO fid Zatt lift k Z0 rs) ∧
    (life prior (bits Θ' wO' (T.σF fid) (T.σ Zatt) (T.σL lift) (T.ν k) (T.σ Z0) (rs.map T.readMap))).map active =
      (life prior (bits Θ wO fid Zatt lift k Z0 rs)).map active ∧
    countReleased (life prior (bits Θ' wO' (T.σF fid) (T.σ Zatt) (T.σL lift) (T.ν k) (T.σ Z0) (rs.map T.readMap))) =
      countReleased (life prior (bits Θ wO fid Zatt lift k Z0 rs)) ∧
    (∀ r ∈ rs,
      gateVector Θ' (T.σF fid) (T.σS r.S) (T.σ r.Z) (T.σ Zatt) (T.σL lift) (T.ν k) (T.ν r.n) =
        gateVector Θ fid r.S r.Z Zatt lift k r.n ∧
      releaseRec (T.σF fid) (T.ν r.n)
          (gateVector Θ' (T.σF fid) (T.σS r.S) (T.σ r.Z) (T.σ Zatt) (T.σL lift) (T.ν k) (T.ν r.n)) (T.σ r.Z) =
        T.relMap (releaseRec fid r.n (gateVector Θ fid r.S r.Z Zatt lift k r.n) r.Z) ∧
      aArch (T.ν k) (T.ν r.n) = aArch k r.n) := by
  have hb := bits_transport T fid Zatt lift k Z0 rs hk
  refine ⟨equiv_transport T, ?_, by rw [hb], by rw [hb], by rw [hb], ?_⟩
  · intro Zs p
    unfold OneStepRenewal
    rw [equiv_transport T, T.word, T.word]
    exact and_congr_right fun _ => not_congr ⟨fun h => T.σW_inj h, fun h => by rw [h]⟩
  · intro r hr
    have hg := gateVector_transport T fid r.S r.Z Zatt lift k r.n (hk r hr)
    refine ⟨hg, ?_, age_transport T k r.n (hk r hr)⟩
    rw [hg]; rfl

/-- The lifecycle key `(ι_f, m, n)` is carried injectively. -/
theorem key_transport_injective (T : Transport Θ Θ' wO wO') :
    Function.Injective (fun key : FaceId × ℕ × ℕ => (T.σF key.1, key.2.1, T.ν key.2.2)) := by
  rintro ⟨f, m, n⟩ ⟨f', m', n'⟩ he
  simp only [Prod.mk.injEq] at he
  obtain ⟨hf, hm, hn⟩ := he
  have hnn : n = n' := by
    rcases Nat.le_total n n' with h | h
    · have := T.ν_diff n n' h
      rw [hn, Nat.sub_self] at this
      exact Nat.le_antisymm h (Nat.sub_eq_zero_iff_le.mp this.symm)
    · have := T.ν_diff n' n h
      rw [hn, Nat.sub_self] at this
      exact (Nat.le_antisymm h (Nat.sub_eq_zero_iff_le.mp this.symm)).symm
  rw [T.σF_inj hf, hm, hnn]

/-- Every uniform shift of strata keeps differences. -/
theorem shift_keeps_diff (c : ℕ) : ∀ a b : ℕ, a ≤ b → (b + c) - (a + c) = b - a :=
  fun a b _ => Nat.add_sub_add_right b c a

/-- A strictly order-preserving relabelling of strata that does not keep
    differences does not preserve archive age: doubling changes it at every
    `k < n`. -/
theorem doubling_breaks_age (k n : ℕ) (h : k < n) : aArch (2 * k) (2 * n) ≠ aArch k n := by
  unfold aArch
  rw [← Nat.mul_sub_left_distrib, Nat.two_mul]
  exact (Nat.ne_of_lt (Nat.lt_add_of_pos_right (Nat.sub_pos_of_lt h))).symm

/-! ## The book's two transports meet the trail and strata hypotheses -/

/-- Common-prefix transport of receiver words, `w ↦ u w`, is injective. -/
theorem prefix_word_injective (u : Word) : Function.Injective (fun w : Word => u ++ w) :=
  fun _ _ h => List.append_cancel_left h

/-- Complete side exchange of receiver words, `w ↦ mirrorWord w`, is injective. -/
theorem mirrorWord_injective : Function.Injective SideExchange.mirrorWord := by
  intro a b h
  have h' := congrArg (List.map not) h
  simp only [SideExchange.mirrorWord, List.map_map] at h'
  have e : (not ∘ not) = id := funext fun x => by cases x <;> rfl
  rw [e, List.map_id, List.map_id] at h'
  exact h'

/-- Side exchange leaves strata fixed, so it keeps every difference. -/
theorem id_keeps_diff : ∀ a b : ℕ, a ≤ b → id b - id a = b - a := fun _ _ _ => rfl

#print axioms prefix_word_injective
#print axioms mirrorWord_injective
#print axioms id_keeps_diff
#print axioms age_transport
#print axioms equiv_transport
#print axioms class_gate_transport
#print axioms gateVector_transport
#print axioms advanced_transport
#print axioms bits_transport
#print axioms covariance_24_18
#print axioms key_transport_injective
#print axioms shift_keeps_diff
#print axioms doubling_breaks_age

end G2_30
end Gaps
end RatioSpace
