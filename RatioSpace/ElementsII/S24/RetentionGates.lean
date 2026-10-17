/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S24.Lifecycle
/-!
  Gap G2-26 — Elements II §24, Definitions 24.10 (gate vector), 24.11 (entry
  event), 24.12 (transition).

  **Book statement.** Definition 24.10: *"g_class = 1 ⟺ 𝖹_f^{[m]} ∼_Λ 𝖹_f^att,
  g_socket = 1 ⟺ SockRet(ι_f, 𝖲^face; n_m) = 1, g_adm = χ_adm(𝖹_f^{[m]}),
  g_ph = χ_ph(θ_Θ(𝖹_f^{[m]}), W_Θ^ph), g_lift = χ_lift(Lift_sib(f)),
  g_read = χ_read(𝖹_f^{[m]}, k_f, n_m, a_arch(f; n_m)) ... The entry is
  retention-compatible when 𝐠_Θ(f;0) = (1,1,1,1,1,1)."* (v0.25 paragraph,
  E2-40: the packet feeds four gates, the read stratum two; a change in
  𝖲^face alone moves only g_socket, a change in 𝖹_f^att alone only g_class;
  phase membership does not determine socket retention, archive readability
  does not determine reception equivalence; resolved reception determines the
  lift status only when the receiver declares it, and the twelve-class receiver
  does not.) Definition 24.11: *"For every retention-compatible face f, define
  its immutable entry event 𝖫𝗂𝖿𝖾𝖤𝗏𝗍_{f,0} = (ι_f, k_f, 0, 𝖹_f^{[0]}, 𝖹_f^att,
  ℛ_Λ(𝖹_f^att), ℛ_Λ(𝖹_f^{[0]}), (1,1,1,1,1,1), retained-at-entry)."*
  Definition 24.12: *"Let f be retention-compatible at entry ... At m = 0,
  Active = 1, LifeStat = retained-at-entry ... the status is 'renewed' when the
  receiver history advanced, otherwise 'retained-no-advance'."*

  Each declaration's docstring names the clause it carries.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_26

open RatioSpace.Two RatioSpace.Two.Incidence RatioSpace.Two.Lifecycle

variable {P Y Ph St : Type}

/-! ## Definition 24.10 — invariances, couplings, non-entailments -/

/-- **E2-40: a change in the attaching reference alone moves no gate but
    `g_class`.** -/
theorem att_moves_only_class [DecidableEq Y] (Θ : Retention P Y Ph St) (fid : FaceId) (S : St)
    (Z Zatt Zatt' : P) (lift : LiftStatus) (k n : ℕ) :
    let g := gateVector Θ fid S Z Zatt lift k n
    let g' := gateVector Θ fid S Z Zatt' lift k n
    g.socket = g'.socket ∧ g.adm = g'.adm ∧ g.ph = g'.ph ∧ g.lift = g'.lift ∧ g.read = g'.read :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Phase membership does not determine socket retention.** Whenever the
    declared socket separates two socket states, the two reads have the same
    phase gate (indeed the same class, admission, phase, lift and readability
    gates) and different socket gates. -/
theorem ph_does_not_determine_socket [DecidableEq Y] (Θ : Retention P Y Ph St) (fid : FaceId)
    (S S' : St) (Z Zatt : P) (lift : LiftStatus) (k n : ℕ) (hS : Θ.sock fid S n ≠ Θ.sock fid S' n) :
    (gateVector Θ fid S Z Zatt lift k n).ph = (gateVector Θ fid S' Z Zatt lift k n).ph ∧
    (gateVector Θ fid S Z Zatt lift k n).socket ≠ (gateVector Θ fid S' Z Zatt lift k n).socket :=
  ⟨rfl, hS⟩

/-- **Archive readability does not determine reception equivalence.** Whenever
    the receiver separates two attaching references, the readability gate is
    the same and the class gate differs. -/
theorem read_does_not_determine_class [DecidableEq Y] (Θ : Retention P Y Ph St) (fid : FaceId)
    (S : St) (Z Zatt Zatt' : P) (lift : LiftStatus) (k n : ℕ)
    (hA : decide (Θ.recv.equiv Z Zatt) ≠ decide (Θ.recv.equiv Z Zatt')) :
    (gateVector Θ fid S Z Zatt lift k n).read = (gateVector Θ fid S Z Zatt' lift k n).read ∧
    (gateVector Θ fid S Z Zatt lift k n).cls ≠ (gateVector Θ fid S Z Zatt' lift k n).cls :=
  ⟨rfl, hA⟩

/-- The hypotheses of the two non-entailments are met by a declaration: a
    socket reading the socket state, and a receiver reading the packet. -/
def sepDecl : Retention Bool Bool Bool Bool where
  recv := ⟨fun _ => true, fun Z => .value Z, fun _ => false, [.relMatrix]⟩
  sock := fun _ S _ => S
  chiAdm := fun _ => true
  theta := fun _ => true
  window := fun p => p
  chiLift := fun _ => true
  chiRead := fun _ _ _ _ => true

theorem sepDecl_separates (fid : FaceId) (n : ℕ) :
    sepDecl.sock fid true n ≠ sepDecl.sock fid false n ∧
    decide (sepDecl.recv.equiv true true) ≠ decide (sepDecl.recv.equiv true false) := by
  refine ⟨fun h => absurd (show true = false from h) (by decide), ?_⟩
  decide

/-! ### The book's packet carries `ι_f`, `k_f`, `n_m`, the face record and its lift status -/

/-- What a packet type carries that the gate display reads: face key, entry
    stratum, read stratum, and the retained sibling lift status. -/
structure Carries (P : Type) where
  fid : P → FaceId
  k : P → ℕ
  n : P → ℕ
  lift : P → LiftStatus

/-- For the transported packet `TPacket`, with the lift status read from its
    face record by a declared projection. -/
def tpCarries {Rec Cyc : Type} (liftOf : Rec → LiftStatus) : Carries (TPacket Rec Cyc) :=
  ⟨TPacket.fid, TPacket.k, TPacket.n, fun Z => liftOf Z.faceRec⟩

/-- For a face record of Definition 23.3: its retained lift status. -/
def faceLift {Aux Cert RawAux EvalAux Prov Renew : Type} {h : ℕ}
    (r : FaceRec Aux Cert RawAux EvalAux h Prov Renew) : LiftStatus := r.packet.lift

theorem faceLift_entryRec {Aux Cert RawAux EvalAux Prov Renew : Type} {h : ℕ}
    (p : Face.FElig Aux Cert RawAux EvalAux h) (t : QuestionId) (pv : Prov) :
    faceLift (entryRec (Renew := Renew) p t pv) = p.lift := rfl

/-- **Definition 24.10, the gate vector read off the packet**: face key, lift
    status and both strata come from the packet, as in the book, not as free
    arguments. -/
def gateVectorC [DecidableEq Y] (Θ : Retention P Y Ph St) (C : Carries P) (S : St) (Z Zatt : P) : Gates :=
  gateVector Θ (C.fid Z) S Z Zatt (C.lift Z) (C.k Z) (C.n Z)

/-- On packets built by `mkPacket` from one face record, the lift gate has the
    same value at every read, whatever the read stratum, trail, socket state,
    attaching reference or certificate. (This is Reading 1 of the open lift-gate
    question in E2-40, for packets that carry the one immutable face record; it
    does not decide Reading 2.) -/
theorem lift_gate_same_at_every_read [DecidableEq Y] {Rec Cyc : Type}
    (Θ : Retention (TPacket Rec Cyc) Y Ph St) (liftOf : Rec → LiftStatus) (S S' : St)
    (fid : FaceId) (rec : Rec) (caus : ℕ × ℕ) (k n n' : ℕ) (wx : Word) (s : Bool) (v v' : Word)
    (cyc cyc' : Cyc) (Zatt Zatt' : TPacket Rec Cyc) :
    (gateVectorC Θ (tpCarries liftOf) S (mkPacket fid rec caus k n wx s v cyc) Zatt).lift =
    (gateVectorC Θ (tpCarries liftOf) S' (mkPacket fid rec caus k n' wx s v' cyc') Zatt').lift := rfl

/-- The coupling E2-40 names, in the packet form: for every capacity `H` and
    entry stratum `k`, a declaration whose receiver, admission predicate and
    phase datum read the packet's archive age, whose socket retains through
    `k + H`, and whose readability gate is `a_arch ≤ H`. One step of the packet
    from read stratum `k + H` to `k + H + 1` (the same face, record, trail,
    certificate) moves the class, socket, admission, phase and readability
    gates together from one to zero; the lift gate stays. -/
def ageDecl (H k : ℕ) (W : LiftStatus → Bool) : Retention (TPacket LiftStatus Unit) Bool Bool Unit where
  recv := ⟨fun _ => true, fun Z => .value (decide (Z.age ≤ H)), fun _ => false, [.archiveAge]⟩
  sock := fun _ _ n => decide (n ≤ k + H)
  chiAdm := fun Z => decide (Z.age ≤ H)
  theta := fun Z => decide (Z.age ≤ H)
  window := fun p => p
  chiLift := W
  chiRead := fun _ _ _ a => decide (a ≤ H)

theorem one_packet_step_moves_five_gates (H k : ℕ) (W : LiftStatus → Bool) (l : LiftStatus) (hl : W l = true)
    (fid : FaceId) (caus : ℕ × ℕ) (wx : Word) (s : Bool) (v : Word) :
    let Zatt := mkPacket fid l caus k k wx s [] ()
    gateVectorC (ageDecl H k W) (tpCarries id) () (mkPacket fid l caus k (k + H) wx s v ()) Zatt =
      ⟨true, true, true, true, true, true⟩ ∧
    gateVectorC (ageDecl H k W) (tpCarries id) () (mkPacket fid l caus k (k + H + 1) wx s v ()) Zatt =
      ⟨false, false, false, false, true, false⟩ := by
  intro Zatt
  have e0 : aArch k (k + H) = H := Nat.add_sub_cancel_left k H
  have e1 : aArch k (k + H + 1) = H + 1 := by
    change k + H + 1 - k = H + 1
    rw [Nat.add_assoc]; exact Nat.add_sub_cancel_left k (H + 1)
  have ea : aArch k k = 0 := Nat.sub_self k
  have t0 : decide (H ≤ H) = true := decide_eq_true (Nat.le_refl H)
  have t1 : decide (H + 1 ≤ H) = false := decide_eq_false (Nat.not_succ_le_self H)
  have tz : decide (0 ≤ H) = true := decide_eq_true (Nat.zero_le H)
  have s0 : decide (k + H ≤ k + H) = true := decide_eq_true (Nat.le_refl _)
  have s1 : decide (k + H + 1 ≤ k + H) = false := decide_eq_false (Nat.not_succ_le_self _)
  refine ⟨?_, ?_⟩
  · change Gates.mk (decide ((ageDecl H k W).recv.equiv _ Zatt)) (decide (k + H ≤ k + H))
      (decide (aArch k (k + H) ≤ H)) (decide (aArch k (k + H) ≤ H)) (W l) (decide (aArch k (k + H) ≤ H)) = _
    rw [e0, t0, s0, hl]
    congr 1
    apply decide_eq_true
    refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
    change RecStat.value (decide (aArch k (k + H) ≤ H)) = RecStat.value (decide (aArch k k ≤ H))
    rw [e0, ea, t0, tz]
  · change Gates.mk (decide ((ageDecl H k W).recv.equiv _ Zatt)) (decide (k + H + 1 ≤ k + H))
      (decide (aArch k (k + H + 1) ≤ H)) (decide (aArch k (k + H + 1) ≤ H)) (W l) (decide (aArch k (k + H + 1) ≤ H)) = _
    rw [e1, t1, s1, hl]
    congr 1
    apply decide_eq_false
    rintro ⟨-, -, he⟩
    have : RecStat.value (decide (aArch k (k + H + 1) ≤ H)) = RecStat.value (decide (aArch k k ≤ H)) := he
    rw [e1, ea, t1, tz] at this
    exact nomatch this

/-- **E2-40's couplings in the display form: the packet feeds four gates.** For
    every capacity `H`, a declaration whose receiver, admission predicate,
    phase datum and readability predicate read the packet's archive age, with a
    socket constantly one. For any two packets on either side of `H` and any
    fixed socket state, attaching reference (within `H`), lift status and
    strata, the class, admission, phase and readability gates move together
    from one to zero; the socket and lift gates stay. -/
def pktDecl (H : ℕ) (W : LiftStatus → Bool) : Retention (TPacket LiftStatus Unit) Bool Bool Unit where
  recv := ⟨fun _ => true, fun Z => .value (decide (Z.age ≤ H)), fun _ => false, [.archiveAge]⟩
  sock := fun _ _ _ => true
  chiAdm := fun Z => decide (Z.age ≤ H)
  theta := fun Z => decide (Z.age ≤ H)
  window := fun p => p
  chiLift := W
  chiRead := fun Z _ _ _ => decide (Z.age ≤ H)

theorem packet_alone_moves_four (H : ℕ) (W : LiftStatus → Bool) (fid : FaceId)
    (Z0 Z1 Zatt : TPacket LiftStatus Unit) (l : LiftStatus) (k n : ℕ)
    (h0 : Z0.age ≤ H) (h1 : H < Z1.age) (ha : Zatt.age ≤ H) :
    gateVector (pktDecl H W) fid () Z0 Zatt l k n = ⟨true, true, true, true, W l, true⟩ ∧
    gateVector (pktDecl H W) fid () Z1 Zatt l k n = ⟨false, true, false, false, W l, false⟩ := by
  have t0 : decide (Z0.age ≤ H) = true := decide_eq_true h0
  have t1 : decide (Z1.age ≤ H) = false := decide_eq_false (Nat.not_le_of_gt h1)
  have ta : decide (Zatt.age ≤ H) = true := decide_eq_true ha
  refine ⟨?_, ?_⟩
  · change Gates.mk (decide ((pktDecl H W).recv.equiv Z0 Zatt)) true (decide (Z0.age ≤ H))
      (decide (Z0.age ≤ H)) (W l) (decide (Z0.age ≤ H)) = _
    rw [t0]
    congr 1
    apply decide_eq_true
    refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
    change RecStat.value (decide (Z0.age ≤ H)) = RecStat.value (decide (Zatt.age ≤ H))
    rw [t0, ta]
  · change Gates.mk (decide ((pktDecl H W).recv.equiv Z1 Zatt)) true (decide (Z1.age ≤ H))
      (decide (Z1.age ≤ H)) (W l) (decide (Z1.age ≤ H)) = _
    rw [t1]
    congr 1
    apply decide_eq_false
    rintro ⟨-, -, he⟩
    have : RecStat.value (decide (Z1.age ≤ H)) = RecStat.value (decide (Zatt.age ≤ H)) := he
    rw [t1, ta] at this
    exact nomatch this

/-- **The read stratum feeds two gates.** Under `ageDecl H k W`, with the packet,
    socket state, attaching reference, lift status and entry stratum fixed, a read
    stratum within `k + H` and one beyond it: the socket and readability gates
    move from one to zero together, and the class, admission, phase and lift
    gates are the same at both. -/
theorem stratum_alone_moves_two (H k : ℕ) (W : LiftStatus → Bool) (fid : FaceId)
    (Z Zatt : TPacket LiftStatus Unit) (l : LiftStatus) (n0 n1 : ℕ)
    (h0 : n0 ≤ k + H) (h1 : k + H < n1) :
    let g0 := gateVector (ageDecl H k W) fid () Z Zatt l k n0
    let g1 := gateVector (ageDecl H k W) fid () Z Zatt l k n1
    g0.socket = true ∧ g0.read = true ∧ g1.socket = false ∧ g1.read = false ∧
    g0.cls = g1.cls ∧ g0.adm = g1.adm ∧ g0.ph = g1.ph ∧ g0.lift = g1.lift := by
  intro g0 g1
  refine ⟨decide_eq_true h0, ?_, decide_eq_false (Nat.not_le_of_gt h1), ?_, rfl, rfl, rfl, rfl⟩
  · change decide (n0 - k ≤ H) = true
    exact decide_eq_true (by omega)
  · change decide (n1 - k ≤ H) = false
    exact decide_eq_false (by omega)

/-- **Resolved reception does not determine the lift status for the
    twelve-class receiver of Proposition 24.9**: its reception is unchanged when
    only the packet's face record (which carries the lift status) is replaced. -/
theorem closure_reception_ignores_faceRec {Rec Cyc : Type} (χ : Closure12) (Z : TPacket Rec Cyc) (rec' : Rec) :
    (closureReceiver χ).recv { Z with faceRec := rec' } = (closureReceiver χ).recv Z := rfl

/-! ## Retention compatibility and the entry event (Definitions 24.10, 24.11) -/

def allOne : Gates := ⟨true, true, true, true, true, true⟩

/-- **Definition 24.10.** The entry is retention-compatible when the gate vector
    at the entry read, whose read stratum is the entry stratum, is all one. -/
def RetentionCompatible [DecidableEq Y] (Θ : Retention P Y Ph St) (C : Carries P) (S : St) (Z0 Zatt : P) : Prop :=
  C.n Z0 = C.k Z0 ∧ gateVectorC Θ C S Z0 Zatt = allOne

/-- **Definition 24.11.** The immutable entry event
    `(ι_f, k_f, 0, 𝖹^{[0]}, 𝖹^att, ℛ_Λ(𝖹^att), ℛ_Λ(𝖹^{[0]}), (1,…,1), retained-at-entry)`. -/
structure EntryEvt (P Y : Type) where
  fid : FaceId
  k : ℕ
  m : ℕ
  packet0 : P
  att : P
  recAtt : RecStat Y
  rec0 : RecStat Y
  gates : Gates
  stat : LifeStat

/-- The entry event of a retention-compatible face; the compatibility proof is
    required, so no entry event exists for an incompatible entry. -/
def entryEvt [DecidableEq Y] (Θ : Retention P Y Ph St) (C : Carries P) (S : St) (Z0 Zatt : P)
    (_hc : RetentionCompatible Θ C S Z0 Zatt) : EntryEvt P Y :=
  ⟨C.fid Z0, C.k Z0, 0, Z0, Zatt, Θ.recv.recv Zatt, Θ.recv.recv Z0, allOne, .retainedAtEntry⟩

/-- At a retention-compatible entry the recorded gate vector is the computed one,
    both packets are in the receiver's declared domain, and the two recorded
    receptions `ℛ_Λ(𝖹^att)` and `ℛ_Λ(𝖹^{[0]})` are equal; the archive age at
    entry is zero. -/
theorem entryEvt_spec [DecidableEq Y] (Θ : Retention P Y Ph St) (C : Carries P) (S : St) (Z0 Zatt : P)
    (hc : RetentionCompatible Θ C S Z0 Zatt) :
    let e := entryEvt Θ C S Z0 Zatt hc
    e.gates = gateVectorC Θ C S Z0 Zatt ∧ e.stat = .retainedAtEntry ∧ e.m = 0 ∧
    Θ.recv.dom Z0 ∧ Θ.recv.dom Zatt ∧ e.rec0 = e.recAtt ∧ aArch (C.k Z0) (C.n Z0) = 0 := by
  intro e
  obtain ⟨hn, hg⟩ := hc
  have hcls : (gateVectorC Θ C S Z0 Zatt).cls = true := by rw [hg]; rfl
  have heq : Θ.recv.equiv Z0 Zatt := of_decide_eq_true hcls
  refine ⟨hg.symm, rfl, rfl, heq.1, heq.2.1, heq.2.2, ?_⟩
  rw [hn]; exact aArch_entry _

/-! ## Definition 24.12 — the lifecycle from entry, advance computed from words -/

/-- `step` reads the prior lifecycle only through whether it contains a release. -/
theorem life_congr : ∀ (xs : List (Gates × Bool)) (prior prior' : List LifeStat),
    prior.any isReleased = prior'.any isReleased → life prior xs = life prior' xs
  | [], _, _, _ => rfl
  | (g, adv) :: xs, prior, prior', hp => by
    have hs : step prior g adv = step prior' g adv := by unfold step; rw [hp]
    change step prior g adv :: life (prior ++ [step prior g adv]) xs =
      step prior' g adv :: life (prior' ++ [step prior' g adv]) xs
    rw [hs, life_congr xs (prior ++ [step prior' g adv]) (prior' ++ [step prior' g adv])
      (by rw [List.any_append, List.any_append, hp])]

/-- The receiver history advanced between two reads: the receiver words differ. -/
def advancedBy (w : P → Word) (Zp Z : P) : Bool := !(decide (w Zp = w Z))

/-- Gate vectors and computed advance bits of the reads `(S_m, 𝖹^{[m]})`, each
    compared with the packet of the previous read. -/
def bitsC [DecidableEq Y] (Θ : Retention P Y Ph St) (C : Carries P) (w : P → Word) (Zatt : P) :
    P → List (St × P) → List (Gates × Bool)
  | _, [] => []
  | Zp, (S, Z) :: rs => (gateVectorC Θ C S Z Zatt, advancedBy w Zp Z) :: bitsC Θ C w Zatt Z rs

/-- **Definition 24.12.** The lifecycle of a retention-compatible face through
    its reads: `retained-at-entry` at `m = 0`, then Definition 24.12's branches
    with gate vectors read off the packets and advance bits computed from the
    receiver words. The compatibility proof is required. -/
def lifeFromEntry [DecidableEq Y] (Θ : Retention P Y Ph St) (C : Carries P) (w : P → Word) (S0 : St)
    (Z0 Zatt : P) (_hc : RetentionCompatible Θ C S0 Z0 Zatt) (reads : List (St × P)) : List LifeStat :=
  .retainedAtEntry :: life [.retainedAtEntry] (bitsC Θ C w Zatt Z0 reads)

theorem lifeFromEntry_spec [DecidableEq Y] (Θ : Retention P Y Ph St) (C : Carries P) (w : P → Word)
    (S0 : St) (Z0 Zatt : P) (hc : RetentionCompatible Θ C S0 Z0 Zatt) (reads : List (St × P)) :
    let L := lifeFromEntry Θ C w S0 Z0 Zatt hc reads
    L.head? = some .retainedAtEntry ∧ active .retainedAtEntry = true ∧
    L.tail = life [] (bitsC Θ C w Zatt Z0 reads) ∧ countReleased L ≤ 1 := by
  intro L
  have ht : life [.retainedAtEntry] (bitsC Θ C w Zatt Z0 reads) = life [] (bitsC Θ C w Zatt Z0 reads) :=
    life_congr _ _ _ rfl
  refine ⟨rfl, rfl, ht, ?_⟩
  change countReleased (.retainedAtEntry :: life [.retainedAtEntry] _) ≤ 1
  rw [countReleased_cons_false _ _ rfl]
  exact at_most_one_release _ rfl _

/-- For a face with no prior release, the status is `renewed` exactly when
    every gate is one and the history advanced. -/
theorem step_renewed_iff (prior : List LifeStat) (hp : prior.any isReleased = false) (g : Gates) (adv : Bool) :
    step prior g adv = .renewed ↔ g.keep = true ∧ adv = true := by
  unfold step; rw [hp]
  cases g.keep <;> cases adv <;> simp

/-- **Definition 24.12's `renewed` is Definition 24.6's one-step renewal.** If
    the read `p + 1` keeps every gate and its receiver words advanced over read
    `p`, and read `p`'s class gate is one, then the two packets are
    `Λ`-equivalent (through the attaching reference) and their receiver words
    differ. -/
theorem renewed_is_one_step_renewal [DecidableEq Y] (Θ : Retention P Y Ph St) (C : Carries P) (w : P → Word)
    (Zatt : P) (Zs : ℕ → P) (Ss : ℕ → St) (p : ℕ)
    (hkeep : (gateVectorC Θ C (Ss (p + 1)) (Zs (p + 1)) Zatt).keep = true)
    (hcls : (gateVectorC Θ C (Ss p) (Zs p) Zatt).cls = true)
    (hadv : advancedBy w (Zs p) (Zs (p + 1)) = true) :
    OneStepRenewal Θ.recv Zs w p := by
  have hk := (keep_iff _).mp hkeep
  have h1 : Θ.recv.equiv (Zs (p + 1)) Zatt := of_decide_eq_true (congrArg Gates.cls hk)
  have h0 : Θ.recv.equiv (Zs p) Zatt := of_decide_eq_true hcls
  refine ⟨⟨h1.1, h0.1, h1.2.2.trans h0.2.2.symm⟩, fun he => ?_⟩
  have : decide (w (Zs p) = w (Zs (p + 1))) = true := decide_eq_true he.symm
  unfold advancedBy at hadv
  rw [this] at hadv
  exact nomatch hadv

#print axioms att_moves_only_class
#print axioms ph_does_not_determine_socket
#print axioms read_does_not_determine_class
#print axioms sepDecl_separates
#print axioms faceLift_entryRec
#print axioms lift_gate_same_at_every_read
#print axioms one_packet_step_moves_five_gates
#print axioms packet_alone_moves_four
#print axioms stratum_alone_moves_two
#print axioms closure_reception_ignores_faceRec
#print axioms entryEvt_spec
#print axioms life_congr
#print axioms lifeFromEntry_spec
#print axioms step_renewed_iff
#print axioms renewed_is_one_step_renewal

end G2_26
end Gaps
end RatioSpace
