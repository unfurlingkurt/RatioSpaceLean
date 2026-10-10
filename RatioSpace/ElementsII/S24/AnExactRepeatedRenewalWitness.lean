/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S24.Lifecycle
/-!
  Gap G2-24 · Elements II Proposition 24.9, an exact repeated-renewal witness:
  "... gives repeated renewal ... while all full matrices and receiver histories
  remain pairwise distinct."

  `Two/Lifecycle.lean`'s `repeated_renewal_witness_distinct` states distinctness for
  the continuation `v(LR)^r` and for `G(v)G((LR)^r)`. The book's receiver histories
  are the receiver words `w_{O} = w_{xs} v (LR)^r`, and its full matrices include
  the receiver matrices `M_O = G(w_{xs} v (LR)^r)` and the transported relative
  matrices `Q_f = G(v(LR)^r)⁻¹ A_s` that the twelve-class receiver reads. This file
  states all of them, over every pair `r ≠ t`, together with the closure equality,
  and on the packets `renewal_nonempty` uses. No existing declaration is changed.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_24

open RatioSpace.Two RatioSpace.Two.Lifecycle RatioSpace.Two.Incidence Mat2 Word Frame

theorem g24_inv2_inv2 (M : Mat2) : inv2 (inv2 M) = M := by
  obtain ⟨a, b, c, d⟩ := M
  change (⟨a, - -b, - -c, d⟩ : Mat2) = ⟨a, b, c, d⟩
  rw [Int.neg_neg, Int.neg_neg]

/-- **The transported relative matrix determines the continuation.** `Q_f` read at
    one sibling hand is injective in the trail: `G(v)⁻¹A_s = G(v')⁻¹A_s` forces
    `v = v'`, by right cancellation of `A_s`, inversion, and positive freeness. -/
theorem g24_Qf_injective (wx : Word) (s : Bool) {v v' : Word} (h : Qf wx s v = Qf wx s v') :
    v = v' := by
  rw [transport_Q, transport_Q] at h
  have h2 : inv2 (G v) * Two.A s * inv2 (Two.A s) = inv2 (G v') * Two.A s * inv2 (Two.A s) := by
    rw [h]
  rw [mul_assoc', mul_assoc', mul_inv2_of_det _ (det_A s), mul_one', mul_one'] at h2
  have h3 := congrArg inv2 h2
  rw [g24_inv2_inv2, g24_inv2_inv2] at h3
  exact G_inj h3

/-- **Proposition 24.9, receiver side, every pair.** For `r ≠ t`, the receiver
    words `w_{xs} v (LR)^r` differ, the receiver matrices differ, the continuations
    and their matrices differ, and the transported relative matrices differ. -/
theorem g24_receiver_histories_distinct (wx : Word) (s : Bool) (v : Word) (r t : ℕ) (hrt : r ≠ t) :
    receiverWord wx s (v ++ wpow [false, true] r) ≠ receiverWord wx s (v ++ wpow [false, true] t) ∧
    G (receiverWord wx s (v ++ wpow [false, true] r)) ≠ G (receiverWord wx s (v ++ wpow [false, true] t)) ∧
    v ++ wpow [false, true] r ≠ v ++ wpow [false, true] t ∧
    G (v ++ wpow [false, true] r) ≠ G (v ++ wpow [false, true] t) ∧
    Qf wx s (v ++ wpow [false, true] r) ≠ Qf wx s (v ++ wpow [false, true] t) := by
  have hw := (renewal_no_recurrence (wx ++ [s] ++ v) [false, true] (by decide) r t hrt).1
  have hc := (repeated_renewal_witness_distinct v r t hrt).1
  have hrw : receiverWord wx s (v ++ wpow [false, true] r) ≠ receiverWord wx s (v ++ wpow [false, true] t) := by
    unfold receiverWord
    rw [← List.append_assoc (wx ++ [s]) v, ← List.append_assoc (wx ++ [s]) v]
    exact hw
  exact ⟨hrw, fun hm => hrw (G_inj hm), hc, fun hm => hc (G_inj hm),
    fun hq => hc (g24_Qf_injective wx s hq)⟩

/-- **Proposition 24.9, whole.** For either hand, any trail `v`, any closure reading
    and every pair `r ≠ t`: the twelve-class receptions agree, and every exact
    datum the receiver does not read differs. -/
theorem g24_repeated_renewal_witness_full (χ : Closure12) (wx : Word) (s : Bool) (v : Word)
    (r t : ℕ) (hrt : r ≠ t) :
    χ.psi (Qf wx s (v ++ wpow [false, true] r)) = χ.psi (Qf wx s (v ++ wpow [false, true] t)) ∧
    receiverWord wx s (v ++ wpow [false, true] r) ≠ receiverWord wx s (v ++ wpow [false, true] t) ∧
    G (receiverWord wx s (v ++ wpow [false, true] r)) ≠ G (receiverWord wx s (v ++ wpow [false, true] t)) ∧
    Qf wx s (v ++ wpow [false, true] r) ≠ Qf wx s (v ++ wpow [false, true] t) := by
  obtain ⟨h1, h2, -, -, h5⟩ := g24_receiver_histories_distinct wx s v r t hrt
  exact ⟨(repeated_renewal_witness χ wx s v r).trans (repeated_renewal_witness χ wx s v t).symm,
    h1, h2, h5⟩

/-- **On the packets.** For the family `renewal_nonempty` exhibits, the declared
    twelve-class receiver returns one reception at `v(LR)^r` and `v(LR)^t`, while
    the packets' receiver words, receiver matrices, relative matrices,
    continuations and archive ages all differ. -/
theorem g24_packets_distinct {Rec Cyc : Type} (χ : Closure12) (fid : FaceId) (rec : Rec)
    (caus : ℕ × ℕ) (k : ℕ) (wx : Word) (s : Bool) (cyc : Cyc) (v : Word) (r t : ℕ) (hrt : r ≠ t) :
    (closureReceiver (Rec := Rec) (Cyc := Cyc) χ).recv
        (mkPacket fid rec caus k (k + (v ++ wpow [false, true] r).length) wx s (v ++ wpow [false, true] r) cyc) =
      (closureReceiver (Rec := Rec) (Cyc := Cyc) χ).recv
        (mkPacket fid rec caus k (k + (v ++ wpow [false, true] t).length) wx s (v ++ wpow [false, true] t) cyc) ∧
    (mkPacket fid rec caus k (k + (v ++ wpow [false, true] r).length) wx s (v ++ wpow [false, true] r) cyc).wO ≠
      (mkPacket fid rec caus k (k + (v ++ wpow [false, true] t).length) wx s (v ++ wpow [false, true] t) cyc).wO ∧
    G (mkPacket fid rec caus k (k + (v ++ wpow [false, true] r).length) wx s (v ++ wpow [false, true] r) cyc).wO ≠
      G (mkPacket fid rec caus k (k + (v ++ wpow [false, true] t).length) wx s (v ++ wpow [false, true] t) cyc).wO ∧
    (mkPacket fid rec caus k (k + (v ++ wpow [false, true] r).length) wx s (v ++ wpow [false, true] r) cyc).Q ≠
      (mkPacket fid rec caus k (k + (v ++ wpow [false, true] t).length) wx s (v ++ wpow [false, true] t) cyc).Q ∧
    (mkPacket fid rec caus k (k + (v ++ wpow [false, true] r).length) wx s (v ++ wpow [false, true] r) cyc).v ≠
      (mkPacket fid rec caus k (k + (v ++ wpow [false, true] t).length) wx s (v ++ wpow [false, true] t) cyc).v := by
  obtain ⟨h1, h2, h3, -, h5⟩ := g24_receiver_histories_distinct wx s v r t hrt
  refine ⟨?_, h1, h2, h5, h3⟩
  change RecStat.value (χ.psi (Qf wx s (v ++ wpow [false, true] r))) =
    RecStat.value (χ.psi (Qf wx s (v ++ wpow [false, true] t)))
  rw [repeated_renewal_witness, repeated_renewal_witness]

#print axioms g24_inv2_inv2
#print axioms g24_Qf_injective
#print axioms g24_receiver_histories_distinct
#print axioms g24_repeated_renewal_witness_full
#print axioms g24_packets_distinct

end G2_24
end Gaps
end RatioSpace
