/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S24.Lifecycle
import RatioSpace.ElementsII.S21.Shortcut
/-!
  Elements II Definition 24.2, receiver trail and transported
  attaching packet.

  **Book statement.** "The exact lineage suffix after the committed child is
  `v_f^{[0]} = s_{j+2} ⋯ s_h` ... Hence the observer adopted at the end of the
  question cycle has word `w_{x*} = w_{xs} v_f^{[0]}`. At a later read `m`, let
  `u_f^{[m]} ∈ {L,R}*` be the exact lawful post-entry continuation retained by the
  current receiver, with `u_f^{[0]} = ε`. Define the complete continuation since
  the causal sibling event by `v_f^{[m]} = v_f^{[0]} u_f^{[m]}`. The current
  receiver word and the archived counter-sibling word are
  `w_{O_f^{[m]}} = w_{xs} v_f^{[m]}`, `w_{P_f} = w_{x s̄}`. The corresponding
  relative matrix is `Q_f^{[m]} = M_{O_f^{[m]}}⁻¹ M_{P_f}`. For a read in `𝒢^(n_m)`,
  the complete transported attaching packet is `𝖹_f^{[m]} = (ι_f, FaceRec, e_caus(f),
  k_f, n_m, a_arch(f; n_m), w_{O_f^{[m]}}, w_{P_f}, v_f^{[m]}, Q_f^{[m]}, C^cyc)`."

  **What the base structures leave open.** `observer_word` is `take_append_drop`
  and does not tie `take (j+1)` to
  `w_{xs}`. `TPacket` is a free structure: only `mkPacket` fills it consistently,
  and nothing in it says which `TPacket`s are the packets of a face.

  **Built here.** The trail and complete continuation; the lineage words
  (`w_{xs}` is the committed child `x_{j+1}`, `w_{x s̄}` the counter-sibling, the
  terminal word is `w_{xs} v_f^{[0]}`), tied to a well-keyed eligibility input of
  Definition 22.5; the packet of face `(x*, j)` at trail `u`, with every field
  derived from lineage data; the predicate `IsFacePacket` naming exactly those
  packets, its field relations, and a `TPacket` that is not one. Words are relative
  to the seed, as `QuestionId.rel` is; the seed matrix cancels in `Q_f`.
  Then the receiver side: a decidable form of `IsFacePacket` (nothing is searched
  for, the read stratum and the trail are read off the packet), the restriction of
  a Definition 24.4 receiver to the packets of one face, and the consequence at
  `gateVector` — a read whose current or attaching packet is not `𝖹_f^{[m]}` has
  class gate and keep bit zero. So a packet in `Receiver` or `gateVector` that
  does not come from `mkPacket` is not retained: `gateVector` is as defined, and
  the restriction rides on the receiver it already takes.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_20

open RatioSpace.Two RatioSpace.Two.Face RatioSpace.Two.Incidence RatioSpace.Two.Lifecycle RatioSpace.Two.Shortcut Mat2 Word

/-! ## Receiver trail and complete continuation -/

/-- **Definition 24.2.** `v_f^{[m]} = v_f^{[0]} u_f^{[m]}`, for the lineage word
    `terminal = w_{x*}`, the event index `j`, and the retained trail `u = u_f^{[m]}`. -/
def fullTrail (terminal : Word) (j : ℕ) (u : Word) : Word := suffixAfter terminal j ++ u

/-- `u_f^{[0]} = ε` gives `v_f^{[0]}`. -/
theorem fullTrail_nil (terminal : Word) (j : ℕ) : fullTrail terminal j [] = suffixAfter terminal j :=
  List.append_nil _

/-! ## The lineage words -/

/-- `w_{xs} = w_{x_j} s_{j+1}` is the committed child's word `take (j+1)`. -/
theorem childWord_eq (i : QuestionId) (j : ℕ) (hj : j < i.rel.length) :
    i.rel.take j ++ [i.rel.getD j false] = i.rel.take (j + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, getD_of_lt _ j hj false]

/-- **`w_{x*} = w_{xs} v_f^{[0]}`, tied to the lineage.** The committed child
    `x_{j+1}` has word `w_{x_j} s_{j+1}`, and the terminal word is that child's word
    followed by `v_f^{[0]} = s_{j+2} ⋯ s_h`. -/
theorem observer_word_lineage (i : QuestionId) (j : ℕ) (hj : j < i.rel.length) :
    (linV i (j + 1)).rel = i.rel.take j ++ [i.rel.getD j false] ∧
    i.rel = receiverWord (i.rel.take j) (i.rel.getD j false) (suffixAfter i.rel j) := by
  refine ⟨(childWord_eq i j hj).symm, ?_⟩
  unfold receiverWord suffixAfter
  rw [childWord_eq i j hj, List.take_append_drop]

/-- `w_{P_f} = w_{x s̄}` is the counter-sibling's word. -/
theorem counter_word_lineage (i : QuestionId) (j : ℕ) :
    (counterSibling i j).rel = counterWord (i.rel.take j) (i.rel.getD j false) := rfl

/-- **Tie to Definition 22.5.** For a well-keyed eligibility input whose parent is
    `x_j` on the lineage and whose hand is the lineage's next letter, the selected
    sibling's word is `w_{xs}`, the refused sibling's word is `w_{x s̄}`, and the
    causal event is `(τ, j+1)`. -/
theorem lineage_input_words (inp : EligInput) (hwk : WellKeyed inp) (i : QuestionId) (j : ℕ)
    (hx : inp.x = linV i j) (hs : inp.s = i.rel.getD j false) (hjj : inp.j = j) :
    inp.idS.rel = i.rel.take j ++ [i.rel.getD j false] ∧
    inp.idBar.rel = (counterSibling i j).rel ∧
    causalEvent inp = (i.cycle, j + 1) := by
  obtain ⟨hS, hB⟩ := hwk
  refine ⟨?_, ?_, ?_⟩
  · rw [hS, hx, hs]; rfl
  · rw [hB, hx, hs]; rfl
  · unfold causalEvent; rw [hx, hjj]; rfl

/-! ## The packet of a face -/

/-- **Definition 24.2.** `𝖹_f^{[m]}` for the face at event `j+1` of the lineage
    ending at `i`, entered at stratum `k`, read at stratum `n` with retained trail
    `u`: every word, matrix, locator and age is computed from these data. -/
def lineagePacket {Rec Cyc : Type} (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec)
    (k n : ℕ) (u : Word) (cyc : Cyc) : TPacket Rec Cyc :=
  mkPacket fid rec (i.cycle, j + 1) k n (i.rel.take j) (i.rel.getD j false) (fullTrail i.rel j u) cyc

/-- `w_{O_f^{[m]}} = w_{x*} u_f^{[m]}`. -/
theorem lineagePacket_wO {Rec Cyc : Type} (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec)
    (k n : ℕ) (u : Word) (cyc : Cyc) (hj : j < i.rel.length) :
    (lineagePacket i j fid rec k n u cyc).wO = i.rel ++ u := by
  have h := (observer_word_lineage i j hj).2
  change receiverWord (i.rel.take j) (i.rel.getD j false) (suffixAfter i.rel j ++ u) = i.rel ++ u
  unfold receiverWord at h ⊢
  rw [← List.append_assoc, ← h]

/-- The retained trail is read back off the receiver word. -/
theorem lineagePacket_trail {Rec Cyc : Type} (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec)
    (k n : ℕ) (u : Word) (cyc : Cyc) (hj : j < i.rel.length) :
    (lineagePacket i j fid rec k n u cyc).wO.drop i.rel.length = u := by
  rw [lineagePacket_wO i j fid rec k n u cyc hj, List.drop_left]

/-- Two packets of one face with different trails differ. -/
theorem lineagePacket_trail_injective {Rec Cyc : Type} (i : QuestionId) (j : ℕ) (fid : FaceId)
    (rec : Rec) (k n n' : ℕ) (u u' : Word) (cyc : Cyc) (hj : j < i.rel.length)
    (h : lineagePacket i j fid rec k n u cyc = lineagePacket i j fid rec k n' u' cyc) : u = u' := by
  rw [← lineagePacket_trail i j fid rec k n u cyc hj, h, lineagePacket_trail i j fid rec k n' u' cyc hj]

/-- **Definition 24.2, every field.** The packet's continuation is `v_f^{[0]} u`,
    its receiver word `w_{x*} u`, its counter word the counter-sibling's, its
    causal locator `(τ, j+1)`, its relative matrix both `M_O⁻¹ M_P` and (by
    Proposition 24.3) `G(v)⁻¹ A_s`, and its age `a_arch(k; n)`. -/
theorem lineagePacket_spec {Rec Cyc : Type} (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec)
    (k n : ℕ) (u : Word) (cyc : Cyc) (hj : j < i.rel.length) :
    (lineagePacket i j fid rec k n u cyc).v = suffixAfter i.rel j ++ u ∧
    (lineagePacket i j fid rec k n u cyc).wO = i.rel ++ u ∧
    (lineagePacket i j fid rec k n u cyc).wP = (counterSibling i j).rel ∧
    (lineagePacket i j fid rec k n u cyc).caus = (i.cycle, j + 1) ∧
    (lineagePacket i j fid rec k n u cyc).Q =
      inv2 (G (lineagePacket i j fid rec k n u cyc).wO) * G (lineagePacket i j fid rec k n u cyc).wP ∧
    (lineagePacket i j fid rec k n u cyc).Q =
      inv2 (G (lineagePacket i j fid rec k n u cyc).v) * Two.A (i.rel.getD j false) ∧
    (lineagePacket i j fid rec k n u cyc).age = aArch k n :=
  ⟨rfl, lineagePacket_wO i j fid rec k n u cyc hj, rfl, rfl, rfl, transport_Q _ _ _, rfl⟩

/-- At `u_f^{[0]} = ε` the receiver word is the terminal word `w_{x*}` and the
    continuation is `v_f^{[0]}`. -/
theorem lineagePacket_entry {Rec Cyc : Type} (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec)
    (k n : ℕ) (cyc : Cyc) (hj : j < i.rel.length) :
    (lineagePacket i j fid rec k n [] cyc).wO = i.rel ∧
    (lineagePacket i j fid rec k n [] cyc).v = suffixAfter i.rel j := by
  refine ⟨?_, fullTrail_nil i.rel j⟩
  rw [lineagePacket_wO i j fid rec k n [] cyc hj, List.append_nil]

/-! ## Which `TPacket`s are packets of the face -/

/-- **The packets of one face.** `Z` is `𝖹_f^{[m]}` for the face at event `j+1` of
    the lineage ending at `i`, entered at `k`: some read stratum `n ≥ k` and some
    retained trail `u` produce it. -/
def IsFacePacket {Rec Cyc : Type} (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec) (k : ℕ)
    (cyc : Cyc) (Z : TPacket Rec Cyc) : Prop :=
  ∃ n u, k ≤ n ∧ Z = lineagePacket i j fid rec k n u cyc

/-- **The relations a face packet carries**, which the free structure does not:
    face key, entry stratum `k ≤ n`, `age + k = n` (exact, no truncation), causal
    locator, receiver word `w_{x*}` followed by the trail read off it, continuation
    `v_f^{[0]}` followed by that trail, counter word, and `Q = G(v)⁻¹ A_s`. -/
theorem isFacePacket_fields {Rec Cyc : Type} (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec)
    (k : ℕ) (cyc : Cyc) (Z : TPacket Rec Cyc) (hj : j < i.rel.length)
    (h : IsFacePacket i j fid rec k cyc Z) :
    Z.fid = fid ∧ Z.k = k ∧ Z.k ≤ Z.n ∧ Z.age + Z.k = Z.n ∧ Z.caus = (i.cycle, j + 1) ∧
    Z.wO = i.rel ++ Z.wO.drop i.rel.length ∧
    Z.v = suffixAfter i.rel j ++ Z.wO.drop i.rel.length ∧
    Z.wP = (counterSibling i j).rel ∧
    Z.Q = inv2 (G Z.v) * Two.A (i.rel.getD j false) := by
  obtain ⟨n, u, hkn, rfl⟩ := h
  have hw := lineagePacket_wO i j fid rec k n u cyc hj
  have ht := lineagePacket_trail i j fid rec k n u cyc hj
  refine ⟨rfl, rfl, hkn, ?_, rfl, ?_, ?_, rfl, transport_Q _ _ _⟩
  · change aArch k n + k = n
    unfold aArch; omega
  · rw [ht]; exact hw
  · rw [ht]; rfl

/-- **The free structure admits a non-packet.** For every face datum, the `TPacket`
    that agrees with the entry packet in every field except an empty counter word
    is not a packet of that face: every face packet's counter word ends in `s̄`. -/
theorem free_packet_not_face {Rec Cyc : Type} (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec)
    (k : ℕ) (cyc : Cyc) :
    ¬ IsFacePacket i j fid rec k cyc
      (⟨fid, rec, (i.cycle, j + 1), k, k, 0, i.rel, [], suffixAfter i.rel j,
        Qf (i.rel.take j) (i.rel.getD j false) (suffixAfter i.rel j), cyc⟩ : TPacket Rec Cyc) := by
  rintro ⟨n, u, _, h⟩
  have hl := congrArg (fun Z : TPacket Rec Cyc => Z.wP.length) h
  -- `simp only` with the three length lemmas, then `omega`; the unrestricted `simp`
  -- pulls `min_eq_zero` and `Nat.right_eq_add`, which carry `Classical.choice`.
  simp only [lineagePacket, mkPacket, counterWord, List.length_nil, List.length_append,
    List.length_cons] at hl
  omega

/-! ## The packets that reach a receiver and the gates -/

-- `TPacket` has decidable equality: every field does.
deriving instance DecidableEq for TPacket

/-- **Decidable form of `IsFacePacket`.** Nothing is searched for: the read stratum
    is the packet's own `n` and the retained trail is read off its receiver word. -/
def isFacePacketB {Rec Cyc : Type} [DecidableEq Rec] [DecidableEq Cyc] (i : QuestionId) (j : ℕ)
    (fid : FaceId) (rec : Rec) (k : ℕ) (cyc : Cyc) (Z : TPacket Rec Cyc) : Bool :=
  decide (k ≤ Z.n) && decide (Z = lineagePacket i j fid rec k Z.n (Z.wO.drop i.rel.length) cyc)

theorem isFacePacketB_iff {Rec Cyc : Type} [DecidableEq Rec] [DecidableEq Cyc] (i : QuestionId)
    (j : ℕ) (fid : FaceId) (rec : Rec) (k : ℕ) (cyc : Cyc) (Z : TPacket Rec Cyc)
    (hj : j < i.rel.length) :
    isFacePacketB i j fid rec k cyc Z = true ↔ IsFacePacket i j fid rec k cyc Z := by
  unfold isFacePacketB
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨hk, hZ⟩
    exact ⟨Z.n, Z.wO.drop i.rel.length, hk, hZ⟩
  · rintro ⟨n, u, hkn, rfl⟩
    have hn : (lineagePacket i j fid rec k n u cyc).n = n := rfl
    have ht := lineagePacket_trail i j fid rec k n u cyc hj
    rw [hn, ht]
    exact ⟨hkn, rfl⟩

/-- **The receiver that only reads the packets of its face.** The readable domain of
    Definition 24.4 cut to `{𝖹_f^{[m]}}`, so a `TPacket` that is not `𝖹_f^{[m]}` for
    any read and any trail is outside it. The restriction is a new receiver built
    from the given one. -/
def onFacePackets {Rec Cyc Y : Type} [DecidableEq Rec] [DecidableEq Cyc]
    (Λ : Receiver (TPacket Rec Cyc) Y) (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec)
    (k : ℕ) (cyc : Cyc) : Receiver (TPacket Rec Cyc) Y :=
  { Λ with readable := fun Z => Λ.readable Z && isFacePacketB i j fid rec k cyc Z }

theorem onFacePackets_dom {Rec Cyc Y : Type} [DecidableEq Rec] [DecidableEq Cyc]
    (Λ : Receiver (TPacket Rec Cyc) Y) (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec)
    (k : ℕ) (cyc : Cyc) (Z : TPacket Rec Cyc) (hj : j < i.rel.length) :
    (onFacePackets Λ i j fid rec k cyc).dom Z ↔ Λ.dom Z ∧ IsFacePacket i j fid rec k cyc Z := by
  change ((Λ.readable Z && isFacePacketB i j fid rec k cyc Z) = true ∧ Λ.outOK (Λ.recv Z) = true) ↔ _
  rw [Bool.and_eq_true, isFacePacketB_iff i j fid rec k cyc Z hj]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩, fun ⟨⟨a, c⟩, b⟩ => ⟨⟨a, b⟩, c⟩⟩

/-- **The free structure's non-packet does not reach the restricted receiver.** -/
theorem free_packet_outside {Rec Cyc Y : Type} [DecidableEq Rec] [DecidableEq Cyc]
    (Λ : Receiver (TPacket Rec Cyc) Y) (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec)
    (k : ℕ) (cyc : Cyc) (hj : j < i.rel.length) :
    ¬ (onFacePackets Λ i j fid rec k cyc).dom
      (⟨fid, rec, (i.cycle, j + 1), k, k, 0, i.rel, [], suffixAfter i.rel j,
        Qf (i.rel.take j) (i.rel.getD j false) (suffixAfter i.rel j), cyc⟩ : TPacket Rec Cyc) :=
  fun hd => free_packet_not_face i j fid rec k cyc
    ((onFacePackets_dom Λ i j fid rec k cyc _ hj).mp hd).2

/-- **A packet that is not a packet of the face is not retained.** For a retention
    whose receiver is restricted to the face, the class gate and the keep bit are
    zero at any read whose current or attaching packet is not `𝖹_f^{[m]}`.
    `gateVector` is as defined, and the restriction is
    carried by the receiver it already takes. -/
theorem nonface_not_retained {Rec Cyc Y Ph St : Type} [DecidableEq Rec] [DecidableEq Cyc]
    [DecidableEq Y] (Θ : Retention (TPacket Rec Cyc) Y Ph St)
    (Λ : Receiver (TPacket Rec Cyc) Y) (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec)
    (k : ℕ) (cyc : Cyc) (hΘ : Θ.recv = onFacePackets Λ i j fid rec k cyc)
    (fid' : FaceId) (S : St) (Z Zatt : TPacket Rec Cyc) (lift : LiftStatus) (k' n : ℕ)
    (hj : j < i.rel.length)
    (h : ¬ IsFacePacket i j fid rec k cyc Z ∨ ¬ IsFacePacket i j fid rec k cyc Zatt) :
    (gateVector Θ fid' S Z Zatt lift k' n).cls = false ∧
    (gateVector Θ fid' S Z Zatt lift k' n).keep = false := by
  have hne : ¬ Θ.recv.equiv Z Zatt := by
    rintro ⟨hZ, hZatt, -⟩
    rw [hΘ] at hZ hZatt
    cases h with
    | inl hL => exact hL ((onFacePackets_dom Λ i j fid rec k cyc Z hj).mp hZ).2
    | inr hR => exact hR ((onFacePackets_dom Λ i j fid rec k cyc Zatt hj).mp hZatt).2
  have hc : (gateVector Θ fid' S Z Zatt lift k' n).cls = false := decide_eq_false hne
  refine ⟨hc, ?_⟩
  unfold Gates.keep
  rw [hc]
  rfl

#print axioms isFacePacketB
#print axioms isFacePacketB_iff
#print axioms onFacePackets
#print axioms onFacePackets_dom
#print axioms free_packet_outside
#print axioms nonface_not_retained

#print axioms fullTrail
#print axioms fullTrail_nil
#print axioms childWord_eq
#print axioms observer_word_lineage
#print axioms counter_word_lineage
#print axioms lineage_input_words
#print axioms lineagePacket
#print axioms lineagePacket_wO
#print axioms lineagePacket_trail
#print axioms lineagePacket_trail_injective
#print axioms lineagePacket_spec
#print axioms lineagePacket_entry
#print axioms IsFacePacket
#print axioms isFacePacket_fields
#print axioms free_packet_not_face

end G2_20
end Gaps
end RatioSpace
