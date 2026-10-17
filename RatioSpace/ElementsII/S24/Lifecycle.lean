/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S23.Incidence
import RatioSpace.ElementsII.S02.Temporal
import RatioSpace.ElementsI.S08.Winding
/-!
  Elements II §24 — Renewal, retention, and release of an admitted face.

  §23 recorded a face. §24 gives it a lifecycle: the archived sibling relation is
  transported to every later receiver (24.3), a declared receiver may read the
  same identity again (renewal) while exact history never recurs (24.7), a
  declared gate vector decides active retention, and release appends a record and
  deletes nothing (24.14). Once released, a face is not silently readmitted
  (24.15).

  **Every receiver, socket and gate here is declared data, not derived.** The book
  says so (Definition 24.10, Receiver Declaration 24.16), and the file keeps them
  as parameters: no retention horizon, phase window or receiver is chosen by the
  Lean. The one instance (24.9) reads the twelve-class closure through Elements
  I's `Closure12`, a twelve-class character carried as a structure, never an `axiom`,
  and inhabited (`Closure12.congruence`); the theorems hold for every one.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Two
namespace Lifecycle

open Mat2 Word Frame Pres RatioSpace SideExchange Advance Observer Shortcut Return Terminal Face Incidence

/-! ## Definition 24.1 — Causal event, face-entry stratum, and archive age -/

/-- `e_caus(f) = (τ, j+1)`: the event at which both siblings were generated. -/
def causalEvent (i : EligInput) : ℕ × ℕ := (i.x.cycle, i.j + 1)

/-- The two locators, retained separately: neither is a field of the other. -/
structure FaceEntry where
  caus : ℕ × ℕ
  k : ℕ

/-- `a_arch(f; n) = n − k_f`, read only for `n ≥ k_f`. -/
def aArch (k n : ℕ) : ℕ := n - k

theorem aArch_entry (k : ℕ) : aArch k k = 0 := Nat.sub_self k

/-- The causal event does not determine the entry stratum: two entries at one
    causal event, at different strata. -/
theorem causal_not_entry (c : ℕ × ℕ) :
    (⟨c, 0⟩ : FaceEntry).caus = (⟨c, 1⟩ : FaceEntry).caus ∧
    (⟨c, 0⟩ : FaceEntry).k ≠ (⟨c, 1⟩ : FaceEntry).k := ⟨rfl, Nat.zero_ne_one⟩

/-! ## Definition 24.2 — Receiver trail and transported attaching packet -/

/-- `v_f^{[0]} = s_{j+2} ⋯ s_h`, the lineage suffix after the committed child. -/
def suffixAfter (terminal : Word) (j : ℕ) : Word := terminal.drop (j + 1)

/-- `w_{x*} = w_{xs} v_f^{[0]}`. -/
theorem observer_word (terminal : Word) (j : ℕ) :
    terminal = terminal.take (j + 1) ++ suffixAfter terminal j := (List.take_append_drop _ _).symm

/-- `w_{O_f^{[m]}} = w_{xs} v_f^{[m]}`. -/
def receiverWord (wx : Word) (s : Bool) (v : Word) : Word := wx ++ [s] ++ v

/-- `w_{P_f} = w_{x s̄}`. -/
def counterWord (wx : Word) (s : Bool) : Word := wx ++ [!s]

/-- `Q_f^{[m]} = M_{O_f^{[m]}}⁻¹ M_{P_f}`. -/
def Qf (wx : Word) (s : Bool) (v : Word) : Mat2 := inv2 (G (receiverWord wx s v)) * G (counterWord wx s)

/-- **Definition 24.2.** `𝖹_f^{[m]}`: the immutable attaching certificate with the
    later receiver-relative reading. -/
structure TPacket (Rec Cyc : Type) where
  fid : FaceId
  faceRec : Rec
  caus : ℕ × ℕ
  k : ℕ
  n : ℕ
  age : ℕ
  wO : Word
  wP : Word
  v : Word
  Q : Mat2
  cyc : Cyc

def mkPacket {Rec Cyc : Type} (fid : FaceId) (rec : Rec) (caus : ℕ × ℕ) (k n : ℕ)
    (wx : Word) (s : Bool) (v : Word) (cyc : Cyc) : TPacket Rec Cyc :=
  ⟨fid, rec, caus, k, n, aArch k n, receiverWord wx s v, counterWord wx s, v, Qf wx s v, cyc⟩

/-- `𝖹_f^att`: the retained sibling encounter on which attachment was certified. -/
structure AttPacket (Rec Cyc : Type) where
  fid : FaceId
  faceRec : Rec
  caus : ℕ × ℕ
  wS : Word
  wBar : Word
  cont : Word
  mat : Mat2
  sib : SibRec
  cyc : Cyc

def mkAtt {Rec Cyc : Type} (fid : FaceId) (rec : Rec) (caus : ℕ × ℕ) (wx : Word) (s : Bool)
    (sib : SibRec) (cyc : Cyc) : AttPacket Rec Cyc :=
  ⟨fid, rec, caus, wx ++ [s], wx ++ [!s], [], A s, sib, cyc⟩

/-- One readable-domain type for both packet kinds (Definition 24.4, item 1). -/
inductive FacePacket (Rec Cyc : Type) where
  | att : AttPacket Rec Cyc → FacePacket Rec Cyc
  | cur : TPacket Rec Cyc → FacePacket Rec Cyc

/-! ## Proposition 24.3 — Exact transport of the archived sibling relation -/

theorem det_inv2 (M : Mat2) : (inv2 M).det = M.det := by
  change M.d * M.a - (-M.b) * (-M.c) = M.a * M.d - M.b * M.c
  rw [Int.neg_mul_neg, Int.mul_comm M.d M.a]

theorem cancel_left (M X : Mat2) (h : M.det = 1) : inv2 M * (M * X) = X := by
  rw [← mul_assoc', inv2_mul_of_det M h, one_mul']

/-- **Proposition 24.3.** `Q_f^{[m]} = G(v_f^{[m]})⁻¹ A_s`. -/
theorem transport_Q (wx : Word) (s : Bool) (v : Word) : Qf wx s v = inv2 (G v) * A s := by
  unfold Qf receiverWord counterWord
  rw [G_append (wx ++ [s]) v, G_snoc wx s, G_snoc wx (!s), inv2_mul, inv2_mul]
  simp only [mul_assoc']
  rw [cancel_left _ _ (det_G wx)]
  rfl

/-- At the causal sibling event, `Q_f(ε) = A_s`. -/
theorem transport_Q_nil (wx : Word) (s : Bool) : Qf wx s [] = A s := by
  rw [transport_Q, G_nil, show inv2 (1 : Mat2) = 1 from by decide, one_mul']

/-- One lawful generator `g`: `Q_f^{[m+1]} = g⁻¹ Q_f^{[m]}`, a left action. -/
theorem transport_step (wx : Word) (s : Bool) (v : Word) (g : Bool) :
    Qf wx s (v ++ [g]) = inv2 (gen g) * Qf wx s v := by
  rw [transport_Q, transport_Q, G_snoc, inv2_mul, mul_assoc']

/-- The presented history continues by the right action `M ↦ Mg`; receiver
    transport is the left action above. They are different actions. -/
theorem history_right_action (w : Word) (g : Bool) : G (w ++ [g]) = G w * gen g := G_snoc w g

/-! ## Definition 24.4 — Readable domain and receiver equivalence -/

/-- A receiver's output keeps its exact tag; no tag is silently a value. -/
inductive RecStat (Y : Type) where
  | value : Y → RecStat Y
  | bot : RecStat Y
  | unresolved : RecStat Y
  | notEvaluated : RecStat Y
deriving DecidableEq

/-- The packet components a receiver may declare that it reads. -/
inductive Component where
  | faceId | faceRec | causal | entryStratum | readStratum | archiveAge
  | receiverWord | counterWord | continuation | relMatrix | shortcutMatrix | sibRec | cycleCert
deriving DecidableEq

/-- **Definition 24.4.** A declared receiver: readable domain, reception map, which
    non-value tags it declares resolved, and the components it reads. -/
structure Receiver (P Y : Type) where
  readable : P → Bool
  recv : P → RecStat Y
  declaredTag : RecStat Y → Bool
  reads : List Component

variable {P Y : Type}

def Receiver.outOK (Λ : Receiver P Y) : RecStat Y → Bool
  | .value _ => true
  | .bot => Λ.declaredTag .bot
  | .unresolved => Λ.declaredTag .unresolved
  | .notEvaluated => Λ.declaredTag .notEvaluated

def Receiver.dom (Λ : Receiver P Y) (Z : P) : Prop := Λ.readable Z = true ∧ Λ.outOK (Λ.recv Z) = true

/-- `𝖹 ∼_Λ 𝖹' ⟺ ℛ_Λ(𝖹) = ℛ_Λ(𝖹')`, on the declared domain. -/
def Receiver.equiv (Λ : Receiver P Y) (Z Z' : P) : Prop := Λ.dom Z ∧ Λ.dom Z' ∧ Λ.recv Z = Λ.recv Z'

instance (Λ : Receiver P Y) [DecidableEq Y] (Z Z' : P) : Decidable (Λ.equiv Z Z') := by
  unfold Receiver.equiv Receiver.dom; exact inferInstance

/-- An output tag the receiver did not declare is outside its domain. -/
theorem undeclared_tag_outside (Λ : Receiver P Y) (Z : P) (t : RecStat Y) (ht : Λ.recv Z = t)
    (hnv : ∀ y, t ≠ .value y) (hd : Λ.declaredTag t = false) : ¬ Λ.dom Z := by
  rintro ⟨-, h2⟩
  rw [ht] at h2
  cases t with
  | value y => exact hnv y rfl
  | bot => exact Bool.false_ne_true (hd.symm.trans h2)
  | unresolved => exact Bool.false_ne_true (hd.symm.trans h2)
  | notEvaluated => exact Bool.false_ne_true (hd.symm.trans h2)

/-! ## Proposition 24.5 — Receiver equivalence is exact on its declared domain -/

/-- **Proposition 24.5.** An equivalence relation on the declared domain. -/
theorem equiv_on_domain (Λ : Receiver P Y) :
    Equivalence (fun a b : {Z // Λ.dom Z} => Λ.equiv a.1 b.1) :=
  ⟨fun a => ⟨a.2, a.2, rfl⟩, fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩,
    fun ⟨h1, _, h3⟩ ⟨_, h2', h3'⟩ => ⟨h1, h2', h3.trans h3'⟩⟩

/-- Nothing outside the domain is related to anything. -/
theorem outside_unrelated (Λ : Receiver P Y) (Z Z' : P) (h : ¬ Λ.dom Z) : ¬ Λ.equiv Z Z' :=
  fun he => h he.1

/-! ## Definition 24.6 — One-step, interval, and repeated renewal -/

/-- `u^r`. -/
def wpow (u : Word) : ℕ → Word
  | 0 => []
  | r + 1 => wpow u r ++ u

theorem wpow_add (u : Word) (t r : ℕ) : wpow u (t + r) = wpow u t ++ wpow u r := by
  induction r with
  | zero => rw [Nat.add_zero, wpow, List.append_nil]
  | succ r ih => rw [← Nat.add_assoc, wpow, wpow, ih, List.append_assoc]

theorem wpow_ne_nil (u : Word) (hu : u ≠ []) : ∀ r, 1 ≤ r → wpow u r ≠ []
  | 0, h => absurd h (by decide)
  | r + 1, _ => by
    intro he
    have hl := congrArg List.length he
    rw [wpow, List.length_append, List.length_nil] at hl
    exact hu (List.eq_nil_of_length_eq_zero (Decidable.byContradiction fun hne => by omega))

def OneStepRenewal (Λ : Receiver P Y) (Z : ℕ → P) (wO : P → Word) (p : ℕ) : Prop :=
  Λ.equiv (Z (p + 1)) (Z p) ∧ wO (Z (p + 1)) ≠ wO (Z p)

def IntervalRenewal (Λ : Receiver P Y) (Z : ℕ → P) (wO : P → Word) (p q : ℕ) : Prop :=
  p < q ∧ Λ.equiv (Z q) (Z p) ∧ wO (Z q) ≠ wO (Z p)

/-- Repeated renewal under a nonempty `u`, packets indexed by continuation. -/
def RepeatedRenewal (Λ : Receiver P Y) (Zc : Word → P) (v u : Word) : Prop :=
  u ≠ [] ∧ ∀ r, 1 ≤ r → Λ.equiv (Zc (v ++ wpow u r)) (Zc v)

/-- The renewal record keeps the continuation, its matrix, the stratum and the
    age even when the received value repeats. -/
structure RenewalRecord (Y : Type) where
  u : Word
  r : ℕ
  cont : Word
  mat : Mat2
  stratum : ℕ
  age : ℕ
  received : RecStat Y

def renewalRecord (v u : Word) (r k n : ℕ) (y : RecStat Y) : RenewalRecord Y :=
  ⟨u, r, v ++ wpow u r, G (v ++ wpow u r), n, aArch k n, y⟩

/-! ## Theorem 24.7 — Renewal advances exact history through pairwise distinct words and matrices -/

theorem words_gt (w u : Word) (hu : u ≠ []) (t d : ℕ) (hd : 1 ≤ d) :
    w ++ wpow u (t + d) ≠ w ++ wpow u t := by
  rw [wpow_add, ← List.append_assoc]
  exact no_raw_word_return _ _ (wpow_ne_nil u hu d hd)

/-- **Theorem 24.7.** Under repeated renewal all exact receiver words and matrices
    are pairwise distinct. -/
theorem renewal_no_recurrence (w u : Word) (hu : u ≠ []) (r t : ℕ) (hrt : r ≠ t) :
    w ++ wpow u r ≠ w ++ wpow u t ∧ G w * G (wpow u r) ≠ G w * G (wpow u t) := by
  have hw : w ++ wpow u r ≠ w ++ wpow u t := by
    rcases Nat.lt_or_gt_of_ne hrt with h | h
    · have e : r + (t - r) = t := Nat.add_sub_of_le (Nat.le_of_lt h)
      intro heq
      have hg := words_gt w u hu r (t - r) (Nat.sub_pos_of_lt h)
      rw [e] at hg
      exact hg heq.symm
    · have e : t + (r - t) = r := Nat.add_sub_of_le (Nat.le_of_lt h)
      intro heq
      have hg := words_gt w u hu t (r - t) (Nat.sub_pos_of_lt h)
      rw [e] at hg
      exact hg heq
  refine ⟨hw, fun hm => hw (G_inj ?_)⟩
  rw [G_append, G_append]; exact hm

/-- **Consequently renewal is recurrence of received identity only.** -/
theorem renewal_identity_only (Λ : Receiver P Y) (Zc : Word → P) (w u : Word)
    (hR : RepeatedRenewal Λ Zc w u) (r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hrt : r ≠ t) :
    Λ.recv (Zc (w ++ wpow u r)) = Λ.recv (Zc (w ++ wpow u t)) ∧
    w ++ wpow u r ≠ w ++ wpow u t ∧ G (w ++ wpow u r) ≠ G (w ++ wpow u t) := by
  obtain ⟨hu, hrep⟩ := hR
  obtain ⟨hw, hm⟩ := renewal_no_recurrence w u hu r t hrt
  refine ⟨(hrep r hr).2.2.trans (hrep t ht).2.2.symm, hw, ?_⟩
  rw [G_append, G_append]; exact hm

/-! ## Corollary 24.8 — Received return extends the observer word forward -/

/-- **Corollary 24.8.** The later observer word has the earlier as a proper prefix;
    and a reading that returns across it is not injective, so the equality lives
    in the receiver, not in the history. -/
theorem return_not_reversal (w u : Word) (hu : u ≠ []) (r : ℕ) (hr : 1 ≤ r) :
    w <+: w ++ wpow u r ∧ w ++ wpow u r ≠ w ∧
    ∀ {α : Type} (κ : Word → α), κ (w ++ wpow u r) = κ w → ¬ Function.Injective κ :=
  ⟨List.prefix_append _ _, no_raw_word_return w _ (wpow_ne_nil u hu r hr),
    fun κ h => return_forces_noninjective κ (wpow_ne_nil u hu r hr) h⟩

/-! ## Proposition 24.9 — An exact repeated-renewal witness -/

theorem det_A (s : Bool) : (A s).det = 1 := by cases s <;> decide

theorem psi_inv2 (χ : Closure12) (M : Mat2) (h : M.det = 1) : χ.psi (inv2 M) = - χ.psi M :=
  χ.map_inv h (by rw [det_inv2]; exact h) (mul_inv2_of_det M h)

/-- `ψ₁₂(G(v)⁻¹ A_s) = −ψ₁₂(v) + ψ₁₂(A_s)`, for any closure reading. -/
theorem psi_Q (χ : Closure12) (v : Word) (s : Bool) :
    χ.psi (inv2 (G v) * A s) = - psi12 v + χ.psi (A s) := by
  rw [χ.map_mul (by rw [det_inv2]; exact det_G v) (det_A s), psi_inv2 χ _ (det_G v), χ.map_G]

theorem psi12_wpow_LR : ∀ r : ℕ, psi12 (wpow [false, true] r) = 0
  | 0 => by decide +kernel
  | r + 1 => by
    rw [wpow, Word.psi12_append, psi12_wpow_LR r, zero_add]
    decide +kernel

/-- **Proposition 24.9.** For either hand, any trail `v`, and every `r ≥ 1`, the
    twelve-class closure of the transported relation is unchanged by `(LR)^r`,
    while the full receiver words and matrices stay pairwise distinct. -/
theorem repeated_renewal_witness (χ : Closure12) (wx : Word) (s : Bool) (v : Word) (r : ℕ) :
    χ.psi (Qf wx s (v ++ wpow [false, true] r)) = χ.psi (Qf wx s v) := by
  rw [transport_Q, transport_Q, psi_Q, psi_Q, Word.psi12_append, psi12_wpow_LR, add_zero]

theorem repeated_renewal_witness_distinct (v : Word) (r t : ℕ) (hrt : r ≠ t) :
    v ++ wpow [false, true] r ≠ v ++ wpow [false, true] t ∧
    G v * G (wpow [false, true] r) ≠ G v * G (wpow [false, true] t) :=
  renewal_no_recurrence v [false, true] (by decide) r t hrt

/-- The twelve-class receiver on current packets, as a declared `Receiver`: it
    reads the relative matrix and nothing else, and every packet is readable. -/
def closureReceiver {Rec Cyc : Type} (χ : Closure12) : Receiver (TPacket Rec Cyc) (ZMod 12) where
  readable := fun _ => true
  recv := fun Z => .value (χ.psi Z.Q)
  declaredTag := fun _ => false
  reads := [.relMatrix]

/-- The renewal type is nonempty: repeated renewal under `LR` for that receiver. -/
theorem renewal_nonempty {Rec Cyc : Type} (χ : Closure12) (fid : FaceId) (rec : Rec) (caus : ℕ × ℕ)
    (k : ℕ) (wx : Word) (s : Bool) (cyc : Cyc) (v : Word) :
    RepeatedRenewal (closureReceiver (Rec := Rec) (Cyc := Cyc) χ)
      (fun c => mkPacket fid rec caus k (k + c.length) wx s c cyc) v [false, true] := by
  refine ⟨by decide, fun r _ => ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩⟩
  change RecStat.value (χ.psi (Qf wx s (v ++ wpow [false, true] r))) = RecStat.value (χ.psi (Qf wx s v))
  rw [repeated_renewal_witness]

/-! ## Definition 24.10 — Retention declaration and gate vector -/

/-- **Definition 24.10.** `Θ = (Λ, σ_ret, χ_adm, χ_ph, χ_lift, χ_read)`, with the
    phase datum `θ_Θ` named by its own type `Ph`. -/
structure Retention (P Y Ph St : Type) where
  recv : Receiver P Y
  sock : FaceId → St → ℕ → Bool
  chiAdm : P → Bool
  theta : P → Ph
  window : Ph → Bool
  chiLift : LiftStatus → Bool
  chiRead : P → ℕ → ℕ → ℕ → Bool

/-- `𝐠_Θ(f; m) ∈ {0,1}⁶`. -/
structure Gates where
  cls : Bool
  socket : Bool
  adm : Bool
  ph : Bool
  lift : Bool
  read : Bool
deriving DecidableEq

def Gates.keep (g : Gates) : Bool := g.cls && g.socket && g.adm && g.ph && g.lift && g.read

theorem keep_iff (g : Gates) : g.keep = true ↔ g = ⟨true, true, true, true, true, true⟩ := by
  obtain ⟨a, b, c, d, e, f⟩ := g
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

variable {Ph St : Type}

def gateVector [DecidableEq Y] (Θ : Retention P Y Ph St) (fid : FaceId) (S : St) (Z Zatt : P)
    (lift : LiftStatus) (k n : ℕ) : Gates where
  cls := decide (Θ.recv.equiv Z Zatt)
  socket := Θ.sock fid S n
  adm := Θ.chiAdm Z
  ph := Θ.window (Θ.theta Z)
  lift := Θ.chiLift lift
  read := Θ.chiRead Z k n (aArch k n)

/-- **No gate takes another gate's value as its input.** Each gate is computed
    from the arguments `gateVector` lists for it, and those overlap: the packet
    `Z` feeds the class, admission, phase and readability gates, and the read
    stratum `n` feeds the socket and readability gates, so one change of `Z` may
    move four gates together and one change of `n` two. What this theorem proves
    is narrower: a change in the socket state `S` alone leaves the class,
    admission, phase, lift and readability gates fixed. Here the lift status is a
    separate argument; in the book the packet carries it, which adds the lift
    gate to those the packet couples. `gates_independent` names this narrower
    statement. -/
theorem gates_independent [DecidableEq Y] (Θ : Retention P Y Ph St) (fid : FaceId) (S S' : St)
    (Z Zatt : P) (lift : LiftStatus) (k n : ℕ) :
    let g := gateVector Θ fid S Z Zatt lift k n
    let g' := gateVector Θ fid S' Z Zatt lift k n
    g.cls = g'.cls ∧ g.adm = g'.adm ∧ g.ph = g'.ph ∧ g.lift = g'.lift ∧ g.read = g'.read :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Definition 24.11 — Append-only face-lifecycle ledger -/

inductive LifeStat where
  | retainedAtEntry
  | renewed
  | retainedNoAdvance
  | released
  | archivalReadAfterRelease
deriving DecidableEq

inductive GateName where
  | cls | socket | adm | ph | lift | read
deriving DecidableEq

/-- `Fail(𝐠)`: every named gate whose value is zero, in order, none collapsed. -/
def Gates.fail (g : Gates) : List GateName :=
  (if g.cls then [] else [.cls]) ++ (if g.socket then [] else [.socket]) ++
  (if g.adm then [] else [.adm]) ++ (if g.ph then [] else [.ph]) ++
  (if g.lift then [] else [.lift]) ++ (if g.read then [] else [.read])

/-- `𝖫𝗂𝖿𝖾𝖤𝗏𝗍_{f,m}`. -/
structure LifeEvt (P Y : Type) where
  fid : FaceId
  m : ℕ
  n : ℕ
  age : ℕ
  packet : P
  recStat : RecStat Y
  gates : Gates
  stat : LifeStat

/-- The global lifecycle ledger, keyed by `(ι_f, r, n_r)`. -/
abbrev LifeLedger (P Y : Type) := List ((FaceId × ℕ × ℕ) × LifeEvt P Y)

def appendEvt (D : LifeLedger P Y) (e : LifeEvt P Y) : LifeLedger P Y := D ++ [((e.fid, e.m, e.n), e)]

/-- Appending never overwrites: every earlier keyed event survives, in place. -/
theorem appendEvt_keeps (D : LifeLedger P Y) (e : LifeEvt P Y) :
    D <+: appendEvt D e ∧ (appendEvt D e).getLast? = some ((e.fid, e.m, e.n), e) :=
  ⟨List.prefix_append _ _, List.getLast?_concat⟩

/-! ## Definition 24.12 — Lifecycle transition and release -/

def isReleased : LifeStat → Bool
  | .released => true
  | _ => false

/-- **Definition 24.12.** The three branches: prior release; all gates one; some
    gate zero. `advanced` says whether the receiver history moved. -/
def step (prior : List LifeStat) (g : Gates) (advanced : Bool) : LifeStat :=
  if prior.any isReleased then .archivalReadAfterRelease
  else if g.keep then (if advanced then .renewed else .retainedNoAdvance)
  else .released

def active (st : LifeStat) : Bool :=
  match st with
  | .released => false
  | .archivalReadAfterRelease => false
  | _ => true

/-- `Release_Θ(f; m) = (ι_f, n_m, Fail(𝐠), 𝖹_f^{[m]})`. -/
structure ReleaseRec (P : Type) where
  fid : FaceId
  n : ℕ
  failed : List GateName
  packet : P

def releaseRec (fid : FaceId) (n : ℕ) (g : Gates) (Z : P) : ReleaseRec P := ⟨fid, n, g.fail, Z⟩

/-- The lifecycle from entry over a list of reads. -/
def life (prior : List LifeStat) : List (Gates × Bool) → List LifeStat
  | [] => []
  | (g, adv) :: xs => step prior g adv :: life (prior ++ [step prior g adv]) xs

def countReleased (l : List LifeStat) : ℕ := (l.filter isReleased).length

/-! ## Theorem 24.13 — Determinism and typedness of the lifecycle update -/

set_option linter.unusedSimpArgs false in
/-- **Theorem 24.13, exhaustive and exclusive.** Exactly one branch applies. -/
theorem step_cases (prior : List LifeStat) (g : Gates) (adv : Bool) :
    (prior.any isReleased = true ∧ step prior g adv = .archivalReadAfterRelease) ∨
    (prior.any isReleased = false ∧ g.keep = true ∧ (step prior g adv = .renewed ∨ step prior g adv = .retainedNoAdvance)) ∨
    (prior.any isReleased = false ∧ g.keep = false ∧ step prior g adv = .released) := by
  unfold step
  cases hp : prior.any isReleased <;> cases hk : g.keep <;> cases adv <;>
    simp only [hk, ite_true, ite_false] <;> decide

theorem any_append_true (l : List LifeStat) (x : LifeStat) (h : l.any isReleased = true) :
    (l ++ [x]).any isReleased = true := by
  rw [List.any_append, h, Bool.true_or]

theorem life_after_release (prior : List LifeStat) (h : prior.any isReleased = true) :
    ∀ xs, ∀ st ∈ life prior xs, st = .archivalReadAfterRelease
  | [], st, hst => nomatch hst
  | (g, adv) :: xs, st, hst => by
    have hs : step prior g adv = .archivalReadAfterRelease := by unfold step; rw [h]; rfl
    cases hst with
    | head => exact hs
    | tail _ hst' => exact life_after_release _ (any_append_true prior _ h) xs st hst'

theorem countReleased_cons_false (x : LifeStat) (l : List LifeStat) (hx : isReleased x = false) :
    countReleased (x :: l) = countReleased l := by
  unfold countReleased
  rw [List.filter_cons_of_neg (by rw [hx]; exact Bool.false_ne_true)]

theorem countReleased_cons_true (x : LifeStat) (l : List LifeStat) (hx : isReleased x = true) :
    countReleased (x :: l) = countReleased l + 1 := by
  unfold countReleased
  rw [List.filter_cons_of_pos hx, List.length_cons]

theorem countReleased_archival (l : List LifeStat) (h : ∀ st ∈ l, st = .archivalReadAfterRelease) :
    countReleased l = 0 := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [countReleased_cons_false x t (by rw [h x (List.Mem.head t)]; rfl)]
    exact ih (fun st hs => h st (List.Mem.tail x hs))

/-- **Theorem 24.13, at most one release.** From any history with no release,
    the lifecycle attaches at most one first release transition. -/
theorem at_most_one_release (prior : List LifeStat) (h : prior.any isReleased = false) :
    ∀ xs, countReleased (life prior xs) ≤ 1
  | [] => Nat.zero_le 1
  | (g, adv) :: xs => by
    unfold life
    cases hk : g.keep
    · have hs : step prior g adv = .released := by unfold step; rw [h, hk]; rfl
      rw [countReleased_cons_true _ _ (by rw [hs]; rfl), hs,
        countReleased_archival _ (life_after_release _ (by rw [List.any_append, h]; rfl) xs)]
    · have hs : isReleased (step prior g adv) = false := by
        unfold step; rw [h, hk]; cases adv <;> rfl
      have hp : (prior ++ [step prior g adv]).any isReleased = false := by
        rw [List.any_append, h, Bool.false_or, List.any_cons, List.any_nil, hs]; rfl
      rw [countReleased_cons_false _ _ hs]
      exact at_most_one_release _ hp xs

/-! ## Theorem 24.14 — Release keeps face history and incidence -/

/-- The archival state: the face records, and the appended lifecycle ledger. -/
structure Archive (FR P Y : Type) where
  faces : List FR
  lifeLedger : LifeLedger P Y
  releases : List (ReleaseRec P)

def applyRelease {FR : Type} (ar : Archive FR P Y) (e : LifeEvt P Y) (rel : ReleaseRec P) : Archive FR P Y :=
  { ar with lifeLedger := appendEvt ar.lifeLedger e, releases := ar.releases ++ [rel] }

/-- **Theorem 24.14.** Release changes only the appended records: the face records
    (and so every incidence and boundary map of Definition 23.4, which read only
    them) are untouched, every earlier lifecycle event survives, and the failed
    gates and packet are recoverable from the release record. -/
theorem release_deletes_nothing {Aux Cert RawAux EvalAux Prov Renew : Type} {h : ℕ}
    (ar : Archive (FaceRec Aux Cert RawAux EvalAux h Prov Renew) P Y) (e : LifeEvt P Y)
    (fid : FaceId) (n : ℕ) (g : Gates) (Z : P) (v : QuestionId) (eu : UEdge) :
    let ar' := applyRelease ar e (releaseRec fid n g Z)
    ar'.faces = ar.faces ∧
    incV ar'.faces v = incV ar.faces v ∧ incE ar'.faces eu = incE ar.faces eu ∧
    (∀ fid', bd ar'.faces fid' = bd ar.faces fid') ∧
    ar.lifeLedger <+: ar'.lifeLedger ∧ ar.releases <+: ar'.releases ∧
    ar'.releases.getLast? = some ⟨fid, n, g.fail, Z⟩ :=
  ⟨rfl, rfl, rfl, fun _ => rfl, List.prefix_append _ _, List.prefix_append _ _, List.getLast?_concat⟩

/-! ## Corollary 24.15 — After release every later read is archival -/

/-- **Corollary 24.15.** After a release every later read is archival and
    inactive, whatever its gates. -/
theorem no_readmission (prior : List LifeStat) (h : prior.any isReleased = true) (xs : List (Gates × Bool)) :
    ∀ st ∈ life prior xs, st = .archivalReadAfterRelease ∧ active st = false :=
  fun st hst => by
    have := life_after_release prior h xs st hst
    exact ⟨this, by rw [this]; rfl⟩

/-! ## Receiver Declaration 24.16 — Optional finite retention profile -/

/-- **Receiver Declaration 24.16.** A finite capacity `H_Θ`, a phase window and a
    lift window, all declared. Nothing here derives a universal horizon. -/
def finiteProfile (Λ : Receiver P Y) (sock : FaceId → St → ℕ → Bool) (chiAdm : P → Bool)
    (theta : P → Ph) (window : Ph → Bool) (liftWindow : LiftStatus → Bool) (H : ℕ) : Retention P Y Ph St where
  recv := Λ
  sock := sock
  chiAdm := chiAdm
  theta := theta
  window := window
  chiLift := liftWindow
  chiRead := fun _ _ _ age => decide (age ≤ H)

/-! ## Proposition 24.17 — Gate independence and the two-coordinate horizon -/

/-- **Proposition 24.17 (2).** Once archive age exceeds `H`, it does at every later
    stratum. -/
theorem horizon_terminal (k n n' H : ℕ) (hn : H < aArch k n) (hle : n ≤ n') : H < aArch k n' := by
  unfold aArch at *; omega

/-- **(1)** The phase gate may fail and later return: its value is a function of
    the phase datum alone, and a window over `Fin 4` shows both. -/
theorem phase_may_return :
    (fun p : Fin 4 => decide (p = 0)) 1 = false ∧ (fun p : Fin 4 => decide (p = 0)) 0 = true := ⟨rfl, rfl⟩

/-- **(3)** Archive age reads only `(k, n)`: phase, admission, lift and socket are
    not among its arguments, so no change in them changes it. -/
theorem age_reads_only_strata (k n : ℕ) {α : Type} (_other _other' : α) : aArch k n = aArch k n := rfl

set_option linter.unusedDecidableInType false in
/-- **(2) in the profile.** The readability gate of a finite profile, once zero
    by age, stays zero. -/
theorem profile_read_stays_zero [DecidableEq Y]
    (Λ : Receiver P Y) (sock : FaceId → St → ℕ → Bool)
    (chiAdm : P → Bool) (theta : P → Ph) (window : Ph → Bool) (lw : LiftStatus → Bool) (H k n n' : ℕ)
    (Z' : P) (hn : H < aArch k n) (hle : n ≤ n') :
    (finiteProfile Λ sock chiAdm theta window lw H).chiRead Z' k n' (aArch k n') = false := by
  change decide (aArch k n' ≤ H) = false
  exact decide_eq_false (Nat.not_le_of_gt (horizon_terminal k n n' H hn hle))

/-! ## Proposition 24.18 — Covariance of renewal and release -/

/-- **Proposition 24.18 (conditional).** If a transport carries packets so that the
    domain, the reception (up to an injective relabeling of values) and every gate
    are preserved, then receiver equivalence, gate vectors, lifecycle statuses and
    archive ages are preserved. The hypotheses are the book's; covariance is not
    imposed on a receiver that did not declare it. -/
theorem covariance_conditional {P' Y' : Type} (Λ : Receiver P Y) (Λ' : Receiver P' Y')
    (σ : P → P') (τ : RecStat Y → RecStat Y') (hτ : Function.Injective τ)
    (hdom : ∀ Z, Λ'.dom (σ Z) ↔ Λ.dom Z) (hrec : ∀ Z, Λ'.recv (σ Z) = τ (Λ.recv Z))
    (Z Z' : P) (gs gs' : List (Gates × Bool)) (hg : gs' = gs) (k n : ℕ) :
    (Λ'.equiv (σ Z) (σ Z') ↔ Λ.equiv Z Z') ∧ life [] gs' = life [] gs ∧ aArch k n = aArch k n := by
  refine ⟨?_, by rw [hg], rfl⟩
  unfold Receiver.equiv
  rw [hdom, hdom, hrec, hrec]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, hτ c⟩, fun ⟨a, b, c⟩ => ⟨a, b, congrArg τ c⟩⟩

/-! ## Separation Rule 24.19 — Distinct notions of persistence

    Carried by exact witnesses: archival persistence without activity
    (`release_deletes_nothing` with `no_readmission`); the attaching class read
    while inactive (below); received identity renewing through pairwise distinct words and matrices
    (`renewal_identity_only`, `repeated_renewal_witness_distinct`). -/

/-- The class gate can be one while the face is not active: the socket gate alone
    fails. Reading the attaching class is not active retention. -/
theorem class_read_not_active :
    (⟨true, false, true, true, true, true⟩ : Gates).cls = true ∧
    (⟨true, false, true, true, true, true⟩ : Gates).keep = false ∧
    step [] ⟨true, false, true, true, true, true⟩ true = .released ∧
    (⟨true, false, true, true, true, true⟩ : Gates).fail = [.socket] := by decide

/-! ## Boundary Statement 24.20 -/

/-- **Boundary Statement 24.20.** Entry → transported packets (24.3) → declared
    equivalence (24.5) → renewal without recurrence (24.7) or exact failed-gate
    release (24.12) → append-only archival retention (24.14). -/
theorem lifecycle_complete (wx : Word) (s : Bool) (v : Word) (prior : List LifeStat)
    (hp : prior.any isReleased = false) (xs : List (Gates × Bool)) :
    Qf wx s v = inv2 (G v) * A s ∧ Qf wx s [] = A s ∧ countReleased (life prior xs) ≤ 1 :=
  ⟨transport_Q wx s v, transport_Q_nil wx s, at_most_one_release prior hp xs⟩

#print axioms causal_not_entry
#print axioms observer_word
#print axioms transport_Q
#print axioms transport_Q_nil
#print axioms transport_step
#print axioms undeclared_tag_outside
#print axioms equiv_on_domain
#print axioms wpow_ne_nil
#print axioms renewal_no_recurrence
#print axioms renewal_identity_only
#print axioms return_not_reversal
#print axioms psi_Q
#print axioms repeated_renewal_witness
#print axioms repeated_renewal_witness_distinct
#print axioms renewal_nonempty
#print axioms keep_iff
#print axioms gates_independent
#print axioms appendEvt_keeps
#print axioms step_cases
#print axioms at_most_one_release
#print axioms release_deletes_nothing
#print axioms no_readmission
#print axioms horizon_terminal
#print axioms profile_read_stays_zero
#print axioms covariance_conditional
#print axioms class_read_not_active
#print axioms lifecycle_complete

end Lifecycle
end Two
end RatioSpace
