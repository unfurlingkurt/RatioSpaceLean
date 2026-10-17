/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S24.Lifecycle
/-!
  Elements II Definition 24.4, readable domain and receiver equivalence.

  **Book statement.** "Let Λ be a declared receiver for transported attaching
  packets. It consists of: an exact readable domain
  `D_Λ^face ⊆ {𝖹_f^att} ∪ {𝖹_f^{[m]}}`; an exact reception map
  `ℛ_Λ^face : D_Λ^face → Y_Λ`; a declaration of every component of the complete
  packet read by that map. ... For lifecycle retention, the receiver domain must
  contain both the attaching reference and every current packet it evaluates. A
  receiver unable to read the attaching reference does not silently receive the
  face as retained. ... This is equality of a declared received identity. It is
  not equality of face keys, occurrence words, matrices, continuation lengths,
  archive ages, channel phases, lift sheets, or exact histories unless the
  receiver has explicitly retained those data and an injectivity theorem has been
  proved."

  **What `Receiver` alone carries.** `Receiver.reads` (`ElementsII/S24/Lifecycle.lean`)
  is a label: nothing in `Receiver` requires `recv` to factor through the declared
  components, so item 3 and the "not equality of face keys ..." paragraph need
  the predicate below, and `Receiver`'s domain is not restricted to the packets
  of one face.

  **Built here.** Each component's value on either packet kind; the predicate
  `Declared` (the reception agrees on readable packets that agree on the declared
  components) and a constructor whose receivers satisfy it by construction; a
  receiver that reads an undeclared component and fails it; the twelve-class
  receiver as a declared receiver, with two equivalent packets differing in face
  key, receiver word, continuation length, archive age and both matrices; the
  converse, that retaining a component through an injective reading does force
  its equality; the one-face restriction of a receiver's domain; and the class and
  keep gates when the attaching reference is unreadable.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_22

open RatioSpace.Two RatioSpace.Two.Face RatioSpace.Two.Incidence RatioSpace.Two.Lifecycle Mat2 Word Frame

/-! ## Components of the complete packet -/

/-- A component's value, for either packet kind. `absent` where the packet kind
    has no such field: the attaching reference carries no strata or age, the
    current packet no sibling record, and neither Lean packet type carries a
    shortcut matrix separate from its relative matrix. -/
inductive CompVal (Rec Cyc : Type) where
  | fid : FaceId → CompVal Rec Cyc
  | faceRec : Rec → CompVal Rec Cyc
  | pair : ℕ × ℕ → CompVal Rec Cyc
  | nat : ℕ → CompVal Rec Cyc
  | word : Word → CompVal Rec Cyc
  | mat : Mat2 → CompVal Rec Cyc
  | sib : SibRec → CompVal Rec Cyc
  | cyc : Cyc → CompVal Rec Cyc
  | absent : CompVal Rec Cyc

variable {Rec Cyc Y : Type}

/-- The value of component `c` in a packet. -/
def proj : Component → FacePacket Rec Cyc → CompVal Rec Cyc
  | .faceId, .att Z => .fid Z.fid
  | .faceId, .cur Z => .fid Z.fid
  | .faceRec, .att Z => .faceRec Z.faceRec
  | .faceRec, .cur Z => .faceRec Z.faceRec
  | .causal, .att Z => .pair Z.caus
  | .causal, .cur Z => .pair Z.caus
  | .entryStratum, .att _ => .absent
  | .entryStratum, .cur Z => .nat Z.k
  | .readStratum, .att _ => .absent
  | .readStratum, .cur Z => .nat Z.n
  | .archiveAge, .att _ => .absent
  | .archiveAge, .cur Z => .nat Z.age
  | .receiverWord, .att Z => .word Z.wS
  | .receiverWord, .cur Z => .word Z.wO
  | .counterWord, .att Z => .word Z.wBar
  | .counterWord, .cur Z => .word Z.wP
  | .continuation, .att Z => .word Z.cont
  | .continuation, .cur Z => .word Z.v
  | .relMatrix, .att Z => .mat Z.mat
  | .relMatrix, .cur Z => .mat Z.Q
  | .shortcutMatrix, _ => .absent
  | .sibRec, .att Z => .sib Z.sib
  | .sibRec, .cur _ => .absent
  | .cycleCert, .att Z => .cyc Z.cyc
  | .cycleCert, .cur Z => .cyc Z.cyc

/-- The stable face key `ι_f` of either packet kind. -/
def pktFid : FacePacket Rec Cyc → FaceId
  | .att Z => Z.fid
  | .cur Z => Z.fid

/-- Two packets agree on every component in `cs`. -/
def AgreeOn (cs : List Component) (Z Z' : FacePacket Rec Cyc) : Prop := ∀ c ∈ cs, proj c Z = proj c Z'

/-! ## Item 3 enforced: the reception reads only what it declares -/

/-- **Definition 24.4, item 3.** On its readable domain the reception map cannot
    separate two packets that agree on every declared component. -/
def Declared (Λ : Receiver (FacePacket Rec Cyc) Y) : Prop :=
  ∀ Z Z', Λ.readable Z = true → Λ.readable Z' = true → AgreeOn Λ.reads Z Z' → Λ.recv Z = Λ.recv Z'

/-- For a declared receiver, packets in the domain that agree on the declared
    components are equivalent. -/
theorem declared_agree_equiv (Λ : Receiver (FacePacket Rec Cyc) Y) (hD : Declared Λ)
    (Z Z' : FacePacket Rec Cyc) (hZ : Λ.dom Z) (hZ' : Λ.dom Z') (hag : AgreeOn Λ.reads Z Z') :
    Λ.equiv Z Z' :=
  ⟨hZ, hZ', hD Z Z' hZ.1 hZ'.1 hag⟩

/-- The declared components of a packet, every other component masked. -/
def restrictVals (cs : List Component) (Z : FacePacket Rec Cyc) : Component → CompVal Rec Cyc :=
  fun c => if c ∈ cs then proj c Z else .absent

/-- A receiver whose reception is computed from the declared components only. -/
def factorReceiver (readable : FacePacket Rec Cyc → Bool) (cs : List Component)
    (F : (Component → CompVal Rec Cyc) → RecStat Y) (declaredTag : RecStat Y → Bool) :
    Receiver (FacePacket Rec Cyc) Y where
  readable := readable
  recv := fun Z => F (restrictVals cs Z)
  declaredTag := declaredTag
  reads := cs

/-- **Declared by construction.** -/
theorem factorReceiver_declared (readable : FacePacket Rec Cyc → Bool) (cs : List Component)
    (F : (Component → CompVal Rec Cyc) → RecStat Y) (declaredTag : RecStat Y → Bool) :
    Declared (factorReceiver readable cs F declaredTag) := by
  intro Z Z' _ _ hag
  change F (restrictVals cs Z) = F (restrictVals cs Z')
  congr 1
  funext c
  unfold restrictVals
  by_cases hc : c ∈ cs
  · rw [if_pos hc, if_pos hc]; exact hag c hc
  · rw [if_neg hc, if_neg hc]

/-! ## Witness packets -/

def q0 : QuestionId := ⟨0, 0, 0, []⟩
def fidA : FaceId := ⟨0, 0, 0, q0, q0, q0⟩
def fidB : FaceId := ⟨1, 0, 0, q0, q0, q0⟩

theorem fidA_ne_fidB : fidA ≠ fidB := fun h => absurd (congrArg FaceId.q h) (by decide)

/-- A receiver that returns the face key while declaring only the relative matrix. -/
def keyRecv : Receiver (FacePacket Unit Unit) FaceId :=
  ⟨fun _ => true, fun Z => .value (pktFid Z), fun _ => false, [.relMatrix]⟩

/-- **The label alone is not the declaration.** `keyRecv` lists `relMatrix` but
    reads the face key, and `Declared` rejects it: two packets with one relative
    matrix and different keys receive differently. -/
theorem keyRecv_not_declared : ¬ Declared keyRecv := by
  intro hD
  have h := hD (.cur (mkPacket fidA () (0, 1) 0 0 [] false [] ()))
    (.cur (mkPacket fidB () (0, 1) 0 0 [] false [] ())) rfl rfl
    (fun c hc => by simp only [keyRecv, List.mem_singleton] at hc; subst hc; rfl)
  exact fidA_ne_fidB (RecStat.value.inj h)

/-! ## Equivalence is not equality of undeclared data -/

/-- The twelve-class receiver of Proposition 24.9 on both packet kinds, reading the
    relative matrix and nothing else. -/
def closure12Face (χ : Closure12) : Receiver (FacePacket Rec Cyc) (ZMod 12) :=
  factorReceiver (fun _ => true) [.relMatrix]
    (fun vals => match vals .relMatrix with
      | .mat Q => .value (χ.psi Q)
      | _ => .notEvaluated)
    (fun _ => false)

theorem closure12Face_recv_cur (χ : Closure12) (Z : TPacket Rec Cyc) :
    (closure12Face χ).recv (.cur Z) = .value (χ.psi Z.Q) := rfl

theorem g22_inv2_inv2 (M : Mat2) : inv2 (inv2 M) = M := by
  obtain ⟨a, b, c, d⟩ := M
  change (⟨a, - -b, - -c, d⟩ : Mat2) = ⟨a, b, c, d⟩
  rw [Int.neg_neg, Int.neg_neg]

theorem g22_Qf_injective (wx : Word) (s : Bool) {v v' : Word} (h : Qf wx s v = Qf wx s v') : v = v' := by
  rw [transport_Q, transport_Q] at h
  have h2 : inv2 (G v) * Two.A s * inv2 (Two.A s) = inv2 (G v') * Two.A s * inv2 (Two.A s) := by rw [h]
  rw [mul_assoc', mul_assoc', mul_inv2_of_det _ (det_A s), mul_one', mul_one'] at h2
  have h3 := congrArg inv2 h2
  rw [g22_inv2_inv2, g22_inv2_inv2] at h3
  exact G_inj h3

/-- **"Not equality of face keys, occurrence words, matrices, continuation lengths,
    archive ages."** For any closure reading, parent word and hand: the declared
    twelve-class receiver makes two current packets equivalent although their face
    keys, receiver words, receiver matrices, relative matrices, continuation lengths
    (`0` and `2`) and archive ages (`0` and `2`) all differ. -/
theorem equiv_not_equality_of_undeclared (χ : Closure12) (wx : Word) (s : Bool) :
    Declared (closure12Face (Rec := Unit) (Cyc := Unit) χ) ∧
    (closure12Face χ).equiv (.cur (mkPacket fidA () (0, 1) 0 0 wx s [] ()))
      (.cur (mkPacket fidB () (0, 1) 0 2 wx s [false, true] ())) ∧
    fidA ≠ fidB ∧
    receiverWord wx s [] ≠ receiverWord wx s [false, true] ∧
    G (receiverWord wx s []) ≠ G (receiverWord wx s [false, true]) ∧
    Qf wx s [] ≠ Qf wx s [false, true] ∧
    ([] : Word).length ≠ [false, true].length ∧
    aArch 0 0 ≠ aArch 0 2 := by
  have hw : receiverWord wx s [] ≠ receiverWord wx s [false, true] := by
    intro h
    have hl := congrArg List.length h
    simp [receiverWord] at hl
  have hψ := repeated_renewal_witness χ wx s [] 1
  refine ⟨factorReceiver_declared _ _ _ _, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩, fidA_ne_fidB, hw,
    fun h => hw (G_inj h), fun h => absurd (g22_Qf_injective wx s h) (by decide), by decide, by decide⟩
  rw [closure12Face_recv_cur, closure12Face_recv_cur]
  exact congrArg RecStat.value hψ.symm

/-- **"Unless the receiver has explicitly retained those data and an injectivity
    theorem has been proved."** If on its readable domain the reception is an
    injective reading of component `c`, equivalence forces equality of `c`. -/
theorem retained_injective_eq (Λ : Receiver (FacePacket Rec Cyc) Y) (c : Component)
    (e : CompVal Rec Cyc → Y) (he : Function.Injective e)
    (hrecv : ∀ Z, Λ.readable Z = true → Λ.recv Z = .value (e (proj c Z)))
    (Z Z' : FacePacket Rec Cyc) (h : Λ.equiv Z Z') : proj c Z = proj c Z' :=
  he (RecStat.value.inj ((hrecv Z h.1.1).symm.trans (h.2.2.trans (hrecv Z' h.2.1.1))))

/-! ## The domain of one face -/

/-- **Item 1, restricted to one face.** The receiver's domain cut to the packets
    carrying face key `ι`: `D_Λ^face ⊆ {𝖹_f^att} ∪ {𝖹_f^{[m]}}` for that `f`. -/
def onFace (Λ : Receiver (FacePacket Rec Cyc) Y) (ι : FaceId) : Receiver (FacePacket Rec Cyc) Y :=
  { Λ with readable := fun Z => Λ.readable Z && decide (pktFid Z = ι) }

theorem onFace_dom (Λ : Receiver (FacePacket Rec Cyc) Y) (ι : FaceId) (Z : FacePacket Rec Cyc) :
    (onFace Λ ι).dom Z ↔ Λ.dom Z ∧ pktFid Z = ι := by
  change ((Λ.readable Z && decide (pktFid Z = ι)) = true ∧ Λ.outOK (Λ.recv Z) = true) ↔
    (Λ.readable Z = true ∧ Λ.outOK (Λ.recv Z) = true) ∧ pktFid Z = ι
  rw [Bool.and_eq_true, decide_eq_true_iff]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩, fun ⟨⟨a, c⟩, b⟩ => ⟨⟨a, b⟩, c⟩⟩

/-- A packet of another face is outside the restricted domain. -/
theorem onFace_other_outside (Λ : Receiver (FacePacket Rec Cyc) Y) (ι : FaceId)
    (Z : FacePacket Rec Cyc) (h : pktFid Z ≠ ι) : ¬ (onFace Λ ι).dom Z :=
  fun hd => h ((onFace_dom Λ ι Z).mp hd).2

/-- Restricted equivalence is the original equivalence between packets of that face. -/
theorem onFace_equiv (Λ : Receiver (FacePacket Rec Cyc) Y) (ι : FaceId) (Z Z' : FacePacket Rec Cyc) :
    (onFace Λ ι).equiv Z Z' ↔ Λ.equiv Z Z' ∧ pktFid Z = ι ∧ pktFid Z' = ι := by
  change ((onFace Λ ι).dom Z ∧ (onFace Λ ι).dom Z' ∧ Λ.recv Z = Λ.recv Z') ↔ _
  rw [onFace_dom, onFace_dom]
  exact ⟨fun ⟨⟨a, b⟩, ⟨c, d⟩, e⟩ => ⟨⟨a, c, e⟩, b, d⟩, fun ⟨⟨a, c, e⟩, b, d⟩ => ⟨⟨a, b⟩, ⟨c, d⟩, e⟩⟩

/-- Restricting to one face keeps a receiver declared. -/
theorem onFace_declared (Λ : Receiver (FacePacket Rec Cyc) Y) (ι : FaceId) (hD : Declared Λ) :
    Declared (onFace Λ ι) := fun Z Z' hr hr' hag =>
  hD Z Z' ((Bool.and_eq_true _ _).mp hr).1 ((Bool.and_eq_true _ _).mp hr').1 hag

/-! ## An unreadable attaching reference -/

/-- **"A receiver unable to read the attaching reference does not silently receive
    the face as retained."** If the attaching reference is outside the receiver's
    domain, no packet is equivalent to it, and at every read the class gate and the
    keep bit are zero. -/
theorem att_unreadable_not_retained {P Ph St : Type} [DecidableEq Y] (Θ : Retention P Y Ph St)
    (fid : FaceId) (S : St) (Z Zatt : P) (lift : LiftStatus) (k n : ℕ) (h : ¬ Θ.recv.dom Zatt) :
    (∀ Z', ¬ Θ.recv.equiv Z' Zatt) ∧
    (gateVector Θ fid S Z Zatt lift k n).cls = false ∧
    (gateVector Θ fid S Z Zatt lift k n).keep = false := by
  have hne : ∀ Z', ¬ Θ.recv.equiv Z' Zatt := fun Z' he => h he.2.1
  have hc : (gateVector Θ fid S Z Zatt lift k n).cls = false := decide_eq_false (hne Z)
  refine ⟨hne, hc, ?_⟩
  unfold Gates.keep
  rw [hc]
  rfl

#print axioms proj
#print axioms pktFid
#print axioms declared_agree_equiv
#print axioms factorReceiver
#print axioms factorReceiver_declared
#print axioms fidA_ne_fidB
#print axioms keyRecv_not_declared
#print axioms closure12Face
#print axioms closure12Face_recv_cur
#print axioms g22_inv2_inv2
#print axioms g22_Qf_injective
#print axioms equiv_not_equality_of_undeclared
#print axioms retained_injective_eq
#print axioms onFace
#print axioms onFace_dom
#print axioms onFace_other_outside
#print axioms onFace_equiv
#print axioms onFace_declared
#print axioms att_unreadable_not_retained

end G2_22
end Gaps
end RatioSpace
