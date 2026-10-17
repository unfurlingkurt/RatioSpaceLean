/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S24.Lifecycle
/-!
  Elements II §24, Proposition 24.17, "Phase return, archive depth, and the
  two-coordinate horizon" (E2-44).

  **Book statement.** In the finite specialization of Receiver Declaration
  24.16: 1. the phase gate may be zero at one read and one at a later read, if
  the declared phase datum returns to W_Θ^ph, and the face stays released;
  2. once archive age exceeds H_Θ, the readability gate remains zero at every
  later stratum; 3. archive age is determined by the face-entry stratum and the
  read stratum alone, and the coupling runs the other way; 4. failure of any
  active-retention gate leaves the archival face record, its incidence and
  boundary maps, and every earlier lifecycle event unchanged, and the read that
  records the failure appends a lifecycle event and, for a face with no prior
  release, one release record naming every failed gate.

  **Relation to `Lifecycle.lean`.** There (1) `phase_may_return` is a `Fin 4`
  witness, not built on `finiteProfile`, `gateVector` or `life`, and (3)
  `age_reads_only_strata` states `aArch k n = aArch k n`. Item 2 is
  `horizon_terminal` / `profile_read_stays_zero`. Item 4 is tied here to
  `release_deletes_nothing`.

  **In this file.**
  * (1) `phase_gate_returns_face_does_not`: in every finite profile, if the
    phase datum is outside the window at one read and inside at a later one,
    the phase gate is 0 then 1; the face (no prior release) is released at the
    first read and every read after it, the returning one included, is
    archival and inactive (E2-45).
  * (3) `age_determined_by_strata`: on every packet whose age component is its
    archive age, the age is fixed by `(k, n)` alone, whatever the face record
    (which carries the lift status), trail, words, matrix and certificate.
    `strata_move_three_gates` and `adm_agrees_with_read` give the coupling E2-44
    names in the other direction: one step of read stratum moves the socket,
    admission and readability gates and the age together, and a declaration
    may make the admission and readability gates agree at every read.
  * (4) `recordRead` appends the read's lifecycle event and, exactly when
    Definition 24.12 releases, the release record. `gate_failure_record`: a
    read with any gate zero leaves the face records, `incV`, `incE`, `bd` and
    every earlier lifecycle event and release record unchanged; for a face with
    no prior release it appends one release record whose failed-gate list names
    exactly the zero gates (`mem_fail_iff`), and none otherwise.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_29

open RatioSpace.Two RatioSpace.Two.Incidence RatioSpace.Two.Lifecycle

variable {P Y Ph St : Type}

/-! ## Item 1 — the phase gate may return; the face does not -/

theorem keep_false_of_ph (g : Gates) (h : g.ph = false) : g.keep = false := by
  obtain ⟨a, b, c, d, e, f⟩ := g
  cases h; cases a <;> cases b <;> cases c <;> cases e <;> cases f <;> rfl

theorem step_released (prior : List LifeStat) (hp : prior.any isReleased = false) (g : Gates)
    (hk : g.keep = false) (adv : Bool) : step prior g adv = .released := by
  unfold step; rw [hp, hk]; rfl

/-- **Proposition 24.17 (1), read as E2-45.** In the finite profile of Receiver
    Declaration 24.16, for any packets `Z` (phase datum outside `W_Θ^ph`) and a
    later `Z'` (inside), any socket states, lift statuses and strata, and any
    reads `mid` between: the phase gate is zero at the first read and one at the
    later read; the face, with no prior release, is released at the first read,
    and every later read, the returning one included, is archival and inactive. -/
theorem phase_gate_returns_face_does_not [DecidableEq Y] (Λ : Receiver P Y)
    (sock : FaceId → St → ℕ → Bool) (chiAdm : P → Bool) (theta : P → Ph) (window : Ph → Bool)
    (lw : LiftStatus → Bool) (H : ℕ) (fid : FaceId) (S S' : St) (Zatt Z Z' : P)
    (lift lift' : LiftStatus) (k n n' : ℕ)
    (hout : window (theta Z) = false) (hin : window (theta Z') = true)
    (prior : List LifeStat) (hp : prior.any isReleased = false)
    (adv adv' : Bool) (mid : List (Gates × Bool)) :
    (gateVector (finiteProfile Λ sock chiAdm theta window lw H) fid S Z Zatt lift k n).ph = false ∧
    (gateVector (finiteProfile Λ sock chiAdm theta window lw H) fid S' Z' Zatt lift' k n').ph = true ∧
    life prior ((gateVector (finiteProfile Λ sock chiAdm theta window lw H) fid S Z Zatt lift k n, adv) ::
        (mid ++ [(gateVector (finiteProfile Λ sock chiAdm theta window lw H) fid S' Z' Zatt lift' k n', adv')]))
      = .released :: life (prior ++ [.released])
          (mid ++ [(gateVector (finiteProfile Λ sock chiAdm theta window lw H) fid S' Z' Zatt lift' k n', adv')]) ∧
    ∀ st ∈ life (prior ++ [.released])
          (mid ++ [(gateVector (finiteProfile Λ sock chiAdm theta window lw H) fid S' Z' Zatt lift' k n', adv')]),
      st = .archivalReadAfterRelease ∧ active st = false := by
  have hs := step_released prior hp _ (keep_false_of_ph
    (gateVector (finiteProfile Λ sock chiAdm theta window lw H) fid S Z Zatt lift k n) hout) adv
  refine ⟨hout, hin, ?_, ?_⟩
  · change step prior _ adv :: life (prior ++ [step prior _ adv]) _ = _
    rw [hs]
  · exact no_readmission _ (by rw [List.any_append]; simp [isReleased]) _

/-- A declared phase datum that does leave the window and return: the hand of
    the last generator of the receiver trail (`false` for an empty trail), on
    the finite phase set `Bool` with window `{true}`. -/
def lastHand {Rec Cyc : Type} (Z : TPacket Rec Cyc) : Bool := Z.v.getLast?.getD false

/-- The hypotheses of `phase_gate_returns_face_does_not` are met at later reads
    of one face: for every trail `v`, continuing by `L` puts the phase datum
    outside the window, and continuing that by `R` puts it back inside. -/
theorem lastHand_leaves_and_returns {Rec Cyc : Type} (fid : FaceId) (rec : Rec) (caus : ℕ × ℕ)
    (k n n' : ℕ) (wx : Word) (s : Bool) (v : Word) (cyc : Cyc) :
    (fun p : Bool => p) (lastHand (mkPacket fid rec caus k n wx s (v ++ [false]) cyc)) = false ∧
    (fun p : Bool => p) (lastHand (mkPacket fid rec caus k n' wx s (v ++ [false] ++ [true]) cyc)) = true := by
  refine ⟨?_, ?_⟩
  · change (v ++ [false]).getLast?.getD false = false
    rw [List.getLast?_concat]; rfl
  · change (v ++ [false] ++ [true]).getLast?.getD false = true
    rw [List.getLast?_concat]; rfl

/-! ## Item 3 — archive age is fixed by the two strata; the coupling runs back -/

variable {Rec Cyc : Type}

/-- A packet whose archive-age component is `a_arch(k, n)` of its own strata. -/
def WellAged (Z : TPacket Rec Cyc) : Prop := Z.age = aArch Z.k Z.n

theorem mkPacket_wellAged (fid : FaceId) (rec : Rec) (caus : ℕ × ℕ) (k n : ℕ) (wx : Word) (s : Bool)
    (v : Word) (cyc : Cyc) : WellAged (mkPacket fid rec caus k n wx s v cyc) := rfl

/-- **Proposition 24.17 (3), as E2-44 states it.** Two well-aged packets with the
    same face-entry stratum and read stratum have the same archive age, whatever
    else differs between them: face identifier, face record (and so the lift
    status it carries), causal event, words, trail, relative matrix, certificate,
    and so any phase datum or admission status read from them. -/
theorem age_determined_by_strata (Z Z' : TPacket Rec Cyc) (hZ : WellAged Z) (hZ' : WellAged Z')
    (hk : Z.k = Z'.k) (hn : Z.n = Z'.n) : Z.age = Z'.age := by
  rw [hZ, hZ', hk, hn]

/-- **The coupling in the other direction (E2-44).** For every capacity `H` and
    entry stratum `k`, declare the socket to retain through read stratum `k + H`
    and the admission predicate to read the packet's archive age. One step of
    read stratum, `k + H → k + H + 1`, moves the socket, admission and
    readability gates together from one to zero, with the age `H → H + 1`. -/
theorem strata_move_three_gates [DecidableEq Y] (Λ : Receiver (TPacket Rec Cyc) Y)
    (theta : TPacket Rec Cyc → Ph) (window : Ph → Bool) (lw : LiftStatus → Bool) (H k : ℕ)
    (fid : FaceId) (rec : Rec) (caus : ℕ × ℕ) (wx : Word) (s : Bool) (v : Word) (cyc : Cyc)
    (S : St) (Zatt : TPacket Rec Cyc) (lift : LiftStatus) :
    let Θ := finiteProfile Λ (fun _ _ n => decide (n ≤ k + H)) (fun Z => decide (Z.age ≤ H)) theta window lw H
    let Z0 := mkPacket fid rec caus k (k + H) wx s v cyc
    let Z1 := mkPacket fid rec caus k (k + H + 1) wx s v cyc
    let g0 := gateVector Θ fid S Z0 Zatt lift k (k + H)
    let g1 := gateVector Θ fid S Z1 Zatt lift k (k + H + 1)
    Z0.age = H ∧ Z1.age = H + 1 ∧
    g0.socket = true ∧ g0.adm = true ∧ g0.read = true ∧
    g1.socket = false ∧ g1.adm = false ∧ g1.read = false := by
  intro Θ Z0 Z1 g0 g1
  have e0 : aArch k (k + H) = H := Nat.add_sub_cancel_left k H
  have e1 : aArch k (k + H + 1) = H + 1 := by
    change k + H + 1 - k = H + 1
    rw [Nat.add_assoc]; exact Nat.add_sub_cancel_left k (H + 1)
  refine ⟨e0, e1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact decide_eq_true (Nat.le_refl _)
  · change decide (aArch k (k + H) ≤ H) = true; rw [e0]; exact decide_eq_true (Nat.le_refl _)
  · change decide (aArch k (k + H) ≤ H) = true; rw [e0]; exact decide_eq_true (Nat.le_refl _)
  · exact decide_eq_false (Nat.not_succ_le_self _)
  · change decide (aArch k (k + H + 1) ≤ H) = false; rw [e1]; exact decide_eq_false (Nat.not_succ_le_self _)
  · change decide (aArch k (k + H + 1) ≤ H) = false; rw [e1]; exact decide_eq_false (Nat.not_succ_le_self _)

/-- A declaration may make two gates agree at every read: with the admission
    predicate reading archive age against `H`, the admission and readability
    gates of the finite profile are equal on every well-aged packet read at its
    own strata. -/
theorem adm_agrees_with_read [DecidableEq Y] (Λ : Receiver (TPacket Rec Cyc) Y)
    (sock : FaceId → St → ℕ → Bool) (theta : TPacket Rec Cyc → Ph) (window : Ph → Bool)
    (lw : LiftStatus → Bool) (H : ℕ) (fid : FaceId) (S : St) (Z Zatt : TPacket Rec Cyc)
    (lift : LiftStatus) (hZ : WellAged Z) :
    (gateVector (finiteProfile Λ sock (fun Z => decide (Z.age ≤ H)) theta window lw H) fid S Z Zatt lift Z.k Z.n).adm =
    (gateVector (finiteProfile Λ sock (fun Z => decide (Z.age ≤ H)) theta window lw H) fid S Z Zatt lift Z.k Z.n).read := by
  change decide (Z.age ≤ H) = decide (aArch Z.k Z.n ≤ H)
  rw [hZ]

/-! ## Item 4 — a gate failure changes no archival record -/

/-- The value of a named gate. -/
def gateAt (g : Gates) : GateName → Bool
  | .cls => g.cls
  | .socket => g.socket
  | .adm => g.adm
  | .ph => g.ph
  | .lift => g.lift
  | .read => g.read

/-- `Fail(𝐠)` names exactly the zero gates. -/
theorem mem_fail_iff (g : Gates) (gn : GateName) : gn ∈ g.fail ↔ gateAt g gn = false := by
  obtain ⟨a, b, c, d, e, f⟩ := g
  cases gn <;> cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem fail_ne_nil (g : Gates) (hk : g.keep = false) : g.fail ≠ [] := by
  obtain ⟨a, b, c, d, e, f⟩ := g
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> first | decide | exact absurd hk (by decide)

variable {FR : Type}

/-- One evaluated read, recorded as Definitions 24.11 and 24.12 record it: the
    lifecycle event is appended, and the release record is appended exactly
    when the transition is a release. -/
def recordRead (ar : Archive FR P Y) (prior : List LifeStat) (e : LifeEvt P Y) (fid : FaceId) (n : ℕ)
    (g : Gates) (adv : Bool) (Z : P) : Archive FR P Y :=
  if step prior g adv = .released then applyRelease ar e (releaseRec fid n g Z)
  else { ar with lifeLedger := appendEvt ar.lifeLedger e }

/-- **Proposition 24.17 (4), read as E2-45.** A read at which some gate is zero
    leaves the archival face records, their vertex and edge incidence and
    boundary maps, every earlier lifecycle event and every earlier release
    record unchanged, and appends the read's lifecycle event. For a face with no
    prior release it appends exactly one release record, whose failed-gate list
    is nonempty and names exactly the zero gates; for a released face it
    appends no release record. -/
theorem gate_failure_record {Aux Cert RawAux EvalAux Prov Renew : Type} {h : ℕ}
    (ar : Archive (FaceRec Aux Cert RawAux EvalAux h Prov Renew) P Y) (prior : List LifeStat)
    (e : LifeEvt P Y) (fid : FaceId) (n : ℕ) (g : Gates) (hk : g.keep = false) (adv : Bool) (Z : P)
    (v : QuestionId) (eu : UEdge) :
    let ar' := recordRead ar prior e fid n g adv Z
    ar'.faces = ar.faces ∧
    incV ar'.faces v = incV ar.faces v ∧ incE ar'.faces eu = incE ar.faces eu ∧
    (∀ fid', bd ar'.faces fid' = bd ar.faces fid') ∧
    ar'.lifeLedger = appendEvt ar.lifeLedger e ∧ ar.lifeLedger <+: ar'.lifeLedger ∧
    ar.releases <+: ar'.releases ∧
    (prior.any isReleased = false →
      ar'.releases = ar.releases ++ [⟨fid, n, g.fail, Z⟩] ∧ g.fail ≠ [] ∧
      ∀ gn, gn ∈ g.fail ↔ gateAt g gn = false) ∧
    (prior.any isReleased = true → ar'.releases = ar.releases) := by
  intro ar'
  cases hp : prior.any isReleased
  · have hs : step prior g adv = .released := step_released prior hp g hk adv
    have har : ar' = applyRelease ar e (releaseRec fid n g Z) := by
      change recordRead ar prior e fid n g adv Z = _
      unfold recordRead; rw [if_pos hs]
    rw [har]
    obtain ⟨h1, h2, h3, h4, -, h6, -⟩ := release_deletes_nothing ar e fid n g Z v eu
    exact ⟨h1, h2, h3, h4, rfl, List.prefix_append _ _, h6,
      fun _ => ⟨rfl, fail_ne_nil g hk, mem_fail_iff g⟩, fun h => by simp at h⟩
  · have hs : step prior g adv ≠ .released := by
      unfold step; rw [hp]; simp
    have har : ar' = { ar with lifeLedger := appendEvt ar.lifeLedger e } := by
      change recordRead ar prior e fid n g adv Z = _
      unfold recordRead; rw [if_neg hs]
    rw [har]
    exact ⟨rfl, rfl, rfl, fun _ => rfl, rfl, List.prefix_append _ _, List.prefix_refl _,
      fun h => by simp at h, fun _ => rfl⟩

#print axioms keep_false_of_ph
#print axioms step_released
#print axioms phase_gate_returns_face_does_not
#print axioms lastHand_leaves_and_returns
#print axioms mkPacket_wellAged
#print axioms age_determined_by_strata
#print axioms strata_move_three_gates
#print axioms adm_agrees_with_read
#print axioms mem_fail_iff
#print axioms fail_ne_nil
#print axioms gate_failure_record

end G2_29
end Gaps
end RatioSpace
