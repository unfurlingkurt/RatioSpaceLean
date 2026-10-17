/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S24.Lifecycle
import RatioSpace.ElementsII.S24.ReceiverTrailAndTransportedAttachingPacket
import RatioSpace.ElementsII.S24.OptionalFiniteRetentionProfile
import RatioSpace.ElementsII.S24.PhaseReturnHorizon
import RatioSpace.ElementsII.S24.CovarianceOfRenewalAndRelease
/-!
  Elements II Definition 24.1, causal event, face-entry stratum, and
  archive age.

  `Lifecycle.lean` has `aArch k n := n - k` on `ℕ` with no `n ≥ k`, so a read
  before entry gets the age of a read at entry (`aArch 5 3 = 0 = aArch 3 3`), which
  Definition 24.1 ("for a later read in `𝒢^(n)`, where `n ≥ k_f`") and E2-02
  exclude. Its `k` is a free `ℕ`: the extended history ledger `𝒢^(0), 𝒢^(1), …` and
  "the unique extended-history stratum in which `RecordFace_𝒬` first appends the
  incidence-bearing face ledger containing `ι_f`" are not built, and
  `causal_not_entry` separates two fields of a free structure.

  This file builds the ledger, reads `k_f` off it as the first stratum whose
  `RecordFace` append contains `ι_f`, proves that stratum unique and stable under
  every later append, gives archive age as a partial function defined exactly when
  `n ≥ k_f`, relates it to `aArch` and to Definition 2.3's `archiveAge` where they
  agree, and separates the causal event from the entry stratum on ledger data.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_19

open RatioSpace.Two RatioSpace.Two.Face RatioSpace.Two.Incidence RatioSpace.Two.Lifecycle

theorem g19_none_ne_some {α : Type} {a : α} (h : (none : Option α) = some a) : False := nomatch h

/-! ## The extended history ledger -/

/-- One append to a stratum of the extended ledger `𝒢`: a `RecordFace` append of
    an incidence-bearing face ledger (records of type `FR`), or any other declared
    append (cycle boundary, lifecycle record), of type `R`. -/
inductive G19Append (FR R : Type) where
  | recordFace : List FR → G19Append FR R
  | other : R → G19Append FR R

/-- **Definition 24.1.** The extended exact history ledger `𝒢^(0), 𝒢^(1), …`:
    `G[n]` is the stratum `𝒢^(n)`, the appends of one declared operation. -/
abbrev G19Ledger (FR R : Type) := List (List (G19Append FR R))

/-- Whether a stratum carries a `RecordFace` append whose face ledger contains a
    record with identifier `fid`. `idOf` reads a record's identifier. -/
def g19RecordsFace {FR R : Type} (idOf : FR → FaceId) (fid : FaceId)
    (st : List (G19Append FR R)) : Bool :=
  st.any fun a => match a with
    | .recordFace L => L.any fun r => decide (idOf r = fid)
    | .other _ => false

/-- The index of the first entry satisfying `p`, if any. -/
def g19First {α : Type} (p : α → Bool) : List α → Option ℕ
  | [] => none
  | a :: l => if p a then some 0 else (g19First p l).map (· + 1)

/-- The "first" property of an index: `p` holds there and at no earlier index. -/
def G19IsFirst {α : Type} (p : α → Bool) (l : List α) (k : ℕ) : Prop :=
  (∃ a, l[k]? = some a ∧ p a = true) ∧ ∀ i < k, ∀ b, l[i]? = some b → p b = false

theorem g19First_cons_true {α : Type} (p : α → Bool) (a : α) (l : List α) (h : p a = true) :
    g19First p (a :: l) = some 0 := if_pos h

theorem g19First_cons_false {α : Type} (p : α → Bool) (a : α) (l : List α) (h : p a = false) :
    g19First p (a :: l) = (g19First p l).map (· + 1) :=
  if_neg (by rw [h]; exact Bool.false_ne_true)

theorem g19First_eq_some_iff {α : Type} (p : α → Bool) :
    ∀ (l : List α) (k : ℕ), g19First p l = some k ↔ G19IsFirst p l k
  | [], k => ⟨fun h => False.elim <| g19_none_ne_some <| (h : (none : Option ℕ) = some k),
      fun ⟨⟨_, ha, _⟩, _⟩ => by rw [List.getElem?_nil] at ha; exact False.elim <| g19_none_ne_some <| ha⟩
  | a :: l, k => by
    cases hpa : p a with
    | true =>
      rw [g19First_cons_true p a l hpa]
      cases k with
      | zero =>
        exact ⟨fun _ => ⟨⟨a, List.getElem?_cons_zero, hpa⟩, fun i hi => absurd hi (Nat.not_lt_zero i)⟩,
          fun _ => rfl⟩
      | succ k =>
        refine ⟨fun h => absurd (Option.some.inj h) (Nat.succ_ne_zero k).symm, fun ⟨_, hb⟩ => ?_⟩
        exact Bool.noConfusion (hpa.symm.trans (hb 0 (Nat.succ_pos k) a List.getElem?_cons_zero))
    | false =>
      rw [g19First_cons_false p a l hpa]
      cases k with
      | zero =>
        refine ⟨fun h => ?_, fun ⟨⟨b, hb, hpb⟩, _⟩ => ?_⟩
        · cases hf : g19First p l with
          | none => rw [hf] at h; exact False.elim <| g19_none_ne_some <| (h : (none : Option ℕ) = some 0)
          | some k' =>
            rw [hf] at h
            exact absurd (Option.some.inj (h : some (k' + 1) = some 0)) (Nat.succ_ne_zero k')
        · rw [List.getElem?_cons_zero] at hb
          cases Option.some.inj hb
          exact Bool.noConfusion (hpb.symm.trans hpa)
      | succ k =>
        have ih := g19First_eq_some_iff p l k
        refine ⟨fun h => ?_, fun ⟨⟨b, hb, hpb⟩, hbefore⟩ => ?_⟩
        · cases hf : g19First p l with
          | none => rw [hf] at h; exact False.elim <| g19_none_ne_some <| (h : (none : Option ℕ) = some (k + 1))
          | some k' =>
            rw [hf] at h
            have hk : k' = k := Nat.succ.inj (Option.some.inj (h : some (k' + 1) = some (k + 1)))
            subst hk
            obtain ⟨⟨b, hb, hpb⟩, hbefore⟩ := ih.mp hf
            refine ⟨⟨b, by rw [List.getElem?_cons_succ]; exact hb, hpb⟩, fun i hi c hc => ?_⟩
            cases i with
            | zero => rw [List.getElem?_cons_zero] at hc; cases Option.some.inj hc; exact hpa
            | succ i =>
              rw [List.getElem?_cons_succ] at hc
              exact hbefore i (Nat.lt_of_succ_lt_succ hi) c hc
        · have hf : g19First p l = some k :=
            ih.mpr ⟨⟨b, by rw [List.getElem?_cons_succ] at hb; exact hb, hpb⟩,
              fun i hi c hc => hbefore (i + 1) (Nat.succ_lt_succ hi) c
                (by rw [List.getElem?_cons_succ]; exact hc)⟩
          rw [hf]; rfl

/-- **"The unique stratum."** Two indices with the first-append property are equal. -/
theorem g19_isFirst_unique {α : Type} (p : α → Bool) (l : List α) {k k' : ℕ}
    (hk : G19IsFirst p l k) (hk' : G19IsFirst p l k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with h | h | h
  · obtain ⟨⟨a, ha, hpa⟩, -⟩ := hk
    have := hk'.2 k h a ha
    rw [hpa] at this; exact absurd this (by decide)
  · exact h
  · obtain ⟨⟨a, ha, hpa⟩, -⟩ := hk'
    have := hk.2 k' h a ha
    rw [hpa] at this; exact absurd this (by decide)

/-- Appending later strata never moves a first index already present. -/
theorem g19First_append_of_some {α : Type} (p : α → Bool) :
    ∀ (l l' : List α) (k : ℕ), g19First p l = some k → g19First p (l ++ l') = some k
  | [], _, k, h => False.elim <| g19_none_ne_some <| (h : (none : Option ℕ) = some k)
  | a :: l, l', k, h => by
    cases hpa : p a with
    | true =>
      rw [g19First_cons_true p a l hpa] at h
      rw [List.cons_append, g19First_cons_true p a (l ++ l') hpa]; exact h
    | false =>
      rw [g19First_cons_false p a l hpa] at h
      rw [List.cons_append, g19First_cons_false p a (l ++ l') hpa]
      cases hf : g19First p l with
      | none => rw [hf] at h; exact False.elim <| g19_none_ne_some <| (h : (none : Option ℕ) = some k)
      | some k' =>
        rw [hf] at h
        rw [g19First_append_of_some p l l' k' hf]; exact h

/-- If nothing in `l` satisfies `p` and `a` does, the first index of `l ++ [a]`
    is `l.length`. -/
theorem g19First_append_new {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), g19First p l = none → p a = true →
      g19First p (l ++ [a]) = some l.length
  | [], a, _, hpa => by simp [g19First, hpa]
  | b :: l, a, h, hpa => by
    cases hpb : p b with
    | true => simp [g19First, hpb] at h
    | false =>
      simp only [g19First, hpb, Bool.false_eq_true, ite_false, Option.map_eq_none_iff] at h
      simp only [List.cons_append, g19First, hpb, Bool.false_eq_true, ite_false,
        g19First_append_new p l a h hpa, Option.map_some, List.length_cons]

/-! ## The face-entry stratum -/

/-- **Definition 24.1.** `k_f`: the first stratum of `𝒢` in which `RecordFace`
    appends a face ledger containing `ι_f`. `none` if `ι_f` has not entered. -/
def g19EntryStratum {FR R : Type} (idOf : FR → FaceId) (G : G19Ledger FR R) (fid : FaceId) :
    Option ℕ :=
  g19First (g19RecordsFace idOf fid) G

/-- `k_f` is the first recording stratum: recorded there, at no earlier stratum. -/
theorem g19EntryStratum_spec {FR R : Type} (idOf : FR → FaceId) (G : G19Ledger FR R)
    (fid : FaceId) (k : ℕ) :
    g19EntryStratum idOf G fid = some k ↔ G19IsFirst (g19RecordsFace idOf fid) G k :=
  g19First_eq_some_iff _ G k

/-- **"The unique extended-history stratum."** -/
theorem g19EntryStratum_unique {FR R : Type} (idOf : FR → FaceId) (G : G19Ledger FR R)
    (fid : FaceId) {k k' : ℕ} (hk : G19IsFirst (g19RecordsFace idOf fid) G k)
    (hk' : G19IsFirst (g19RecordsFace idOf fid) G k') : k = k' :=
  g19_isFirst_unique _ G hk hk'

/-- **Append-only.** Once `ι_f` has entered at `k_f`, every later stratum
    appended to `𝒢` leaves `k_f` where it is. -/
theorem g19EntryStratum_stable {FR R : Type} (idOf : FR → FaceId) (G G' : G19Ledger FR R)
    (fid : FaceId) (k : ℕ) (h : g19EntryStratum idOf G fid = some k) :
    g19EntryStratum idOf (G ++ G') fid = some k :=
  g19First_append_of_some _ G G' k h

/-- **First append.** If `ι_f` has not entered `𝒢` and the next stratum carries a
    `RecordFace` append containing it, then `k_f` is that stratum's index. -/
theorem g19EntryStratum_recordFace {FR R : Type} (idOf : FR → FaceId) (G : G19Ledger FR R)
    (fid : FaceId) (st : List (G19Append FR R)) (L : List FR) (r : FR)
    (hnew : g19EntryStratum idOf G fid = none) (hst : G19Append.recordFace L ∈ st)
    (hr : r ∈ L) (hid : idOf r = fid) :
    g19EntryStratum idOf (G ++ [st]) fid = some G.length := by
  refine g19First_append_new _ G st hnew ?_
  simp only [g19RecordsFace, List.any_eq_true]
  exact ⟨_, hst, List.any_eq_true.mpr ⟨r, hr, by simp [hid]⟩⟩

/-! ## The ledger read off an actual `recordFace` history

`RecState.hist` (`Face.lean:149`) is already an append-only trace: Definition
22.4's `FaceAppend` (`Face.lean:152`), which is what Definition 23.5's
`recordFace` (`Incidence.lean:209`) calls, pushes `(target, z)` onto `hist` and
changes nothing else, so successive `recordFace` calls occupy successive
positions of `hist` — exactly the book's "successive declared operations occupy
successive strata" for this kind of append. Reading `hist` as a `G19Ledger`, one
stratum per call, ties `g19EntryStratum` to the actual operation Definition 23.5
names instead of a hand-written list. Interleaving with a cycle-boundary or
lifecycle append is the next section: `hist` only ever holds `recordFace`
strata, so `G19Append.other` is never produced here. -/

/-- The extended ledger read off a real `recordFace` history: one stratum per
    entry of `hist`, in call order. -/
def g19LedgerOfHist {FR R : Type} (hist : List (QuestionId × List FR)) : G19Ledger FR R :=
  hist.map (fun p => [G19Append.recordFace p.2])

theorem g19LedgerOfHist_length {FR R : Type} (hist : List (QuestionId × List FR)) :
    (g19LedgerOfHist (R := R) hist).length = hist.length := by
  simp [g19LedgerOfHist]

theorem g19LedgerOfHist_append {FR R : Type} (h h' : List (QuestionId × List FR)) :
    g19LedgerOfHist (R := R) (h ++ h') = g19LedgerOfHist h ++ g19LedgerOfHist h' := by
  simp [g19LedgerOfHist]

/-- A single `recordFace`/`faceAppend` call (Definition 23.5, `Incidence.lean:209`,
    via `Face.lean:152`) extends `g19LedgerOfHist` by exactly one stratum holding
    the appended list, and touches nothing already there. -/
theorem g19LedgerOfHist_faceAppend {Op FR R : Type} (st : RecState Op (List FR))
    (target : QuestionId) (L : List FR) :
    g19LedgerOfHist (R := R) (faceAppend st target L).hist =
      g19LedgerOfHist (R := R) st.hist ++ [[G19Append.recordFace L]] := by
  simp [g19LedgerOfHist, faceAppend]

/-- **Definition 24.1 on the real recording map.** If `ι_f` has not entered the
    ledger read off `st.hist` and `recordFace` now appends a list `L` containing
    a record with that id, the face-entry stratum of the resulting state is
    exactly `st.hist.length`: the position of that call, computed from the
    actual append, not asserted as a free `ℕ`. -/
theorem g19EntryStratum_recordFace_call {Op FR R : Type} (idOf : FR → FaceId)
    (st : RecState Op (List FR)) (target : QuestionId) (L : List FR) (r : FR) (fid : FaceId)
    (hnew : g19EntryStratum idOf (g19LedgerOfHist (R := R) st.hist) fid = none)
    (hr : r ∈ L) (hid : idOf r = fid) :
    g19EntryStratum idOf (g19LedgerOfHist (R := R) (faceAppend st target L).hist) fid
      = some st.hist.length := by
  rw [g19LedgerOfHist_faceAppend, ← g19LedgerOfHist_length (R := R) st.hist]
  exact g19EntryStratum_recordFace idOf (g19LedgerOfHist (R := R) st.hist) fid
    [G19Append.recordFace L] L r hnew (List.mem_singleton_self _) hr hid

/-- **Stability on the real history.** Once `ι_f` has entered at stratum `k` of
    `st.hist`, any further `recordFace` call leaves `k_f` where it is — the
    `g19EntryStratum_stable` guarantee, specialised to the actual append. -/
theorem g19EntryStratum_recordFace_stable {Op FR R : Type} (idOf : FR → FaceId)
    (st : RecState Op (List FR)) (target : QuestionId) (L : List FR) (fid : FaceId) (k : ℕ)
    (h : g19EntryStratum idOf (g19LedgerOfHist (R := R) st.hist) fid = some k) :
    g19EntryStratum idOf (g19LedgerOfHist (R := R) (faceAppend st target L).hist) fid = some k := by
  rw [g19LedgerOfHist_faceAppend]
  exact g19EntryStratum_stable idOf _ [[G19Append.recordFace L]] fid k h

/-! ## Archive age, defined exactly when `n ≥ k_f` -/

/-- **Definition 24.1.** `a_arch(f; n) = n − k_f`, for `n ≥ k_f`; no value otherwise. -/
def g19ArchAge (k n : ℕ) : Option ℕ := if k ≤ n then some (n - k) else none

/-- An age exists exactly for `k ≤ n`, and it is the exact integer `a` with `a + k = n`. -/
theorem g19ArchAge_eq_some_iff (k n a : ℕ) : g19ArchAge k n = some a ↔ k ≤ n ∧ a + k = n := by
  unfold g19ArchAge
  split
  · rename_i h
    refine ⟨fun he => ?_, fun ⟨_, he⟩ => ?_⟩
    · cases Option.some.inj he; exact ⟨h, Nat.sub_add_cancel h⟩
    · rw [← he, Nat.add_sub_cancel]
  · rename_i h
    exact ⟨fun he => False.elim <| g19_none_ne_some <| he, fun ⟨h', _⟩ => absurd h' h⟩

/-- A read before entry has no archive age. -/
theorem g19ArchAge_eq_none_iff (k n : ℕ) : g19ArchAge k n = none ↔ n < k := by
  unfold g19ArchAge
  by_cases h : k ≤ n
  · simp only [h, ite_true, reduceCtorEq, false_iff]; omega
  · simp only [h, ite_false, true_iff]; omega

/-- `a_arch(f; k_f) = 0`. -/
theorem g19ArchAge_entry (k : ℕ) : g19ArchAge k k = some 0 := by
  simp [g19ArchAge]

/-- Where the book defines it, `g19ArchAge` is the existing `aArch`. -/
theorem g19ArchAge_eq_aArch {k n : ℕ} (h : k ≤ n) : g19ArchAge k n = some (aArch k n) := by
  simp [g19ArchAge, aArch, h]

/-- Where the book defines it, archive age is Definition 2.3's `archiveAge` of the
    reading of a record entered at stratum `k`, in any storage slot. -/
theorem g19ArchAge_eq_archiveAge {k n : ℕ} (h : k ≤ n) (slot : ℕ) :
    g19ArchAge k n = some (archiveAge ⟨⟨k, slot⟩, n, h⟩) := by
  simp [g19ArchAge, h]

/-- **The defect, for every pair.** For every `n < k`, `aArch` gives the read before
    entry the age of the read at entry, while the faithful age gives it none. -/
theorem g19_aArch_truncates (k n : ℕ) (h : n < k) :
    aArch k n = aArch k k ∧ g19ArchAge k n = none ∧ g19ArchAge k k = some 0 := by
  refine ⟨?_, (g19ArchAge_eq_none_iff k n).mpr h, g19ArchAge_entry k⟩
  unfold aArch; omega

/-- **Definition 24.1 on the ledger.** The age of `ι_f` at a read in `𝒢^(n)`:
    `k_f` from the ledger, then `n − k_f` for `n ≥ k_f`. -/
def g19FaceAge {FR R : Type} (idOf : FR → FaceId) (G : G19Ledger FR R) (fid : FaceId) (n : ℕ) :
    Option ℕ :=
  (g19EntryStratum idOf G fid).bind fun k => g19ArchAge k n

theorem g19FaceAge_eq_some_iff {FR R : Type} (idOf : FR → FaceId) (G : G19Ledger FR R)
    (fid : FaceId) (n a : ℕ) :
    g19FaceAge idOf G fid n = some a ↔
      ∃ k, g19EntryStratum idOf G fid = some k ∧ k ≤ n ∧ a + k = n := by
  unfold g19FaceAge
  cases hk : g19EntryStratum idOf G fid with
  | none =>
    exact ⟨fun h => False.elim <| g19_none_ne_some <| (h : (none : Option ℕ) = some a),
      fun ⟨_, hk', _⟩ => False.elim <| g19_none_ne_some <| hk'⟩
  | some k =>
    refine ⟨fun h => ⟨k, rfl, (g19ArchAge_eq_some_iff k n a).mp h⟩, fun ⟨k', hk', hle, ha⟩ => ?_⟩
    cases Option.some.inj hk'
    exact (g19ArchAge_eq_some_iff k n a).mpr ⟨hle, ha⟩

/-- A later append never changes the age of an entered face at a given read. -/
theorem g19FaceAge_stable {FR R : Type} (idOf : FR → FaceId) (G G' : G19Ledger FR R)
    (fid : FaceId) (k n : ℕ) (h : g19EntryStratum idOf G fid = some k) :
    g19FaceAge idOf (G ++ G') fid n = g19FaceAge idOf G fid n := by
  unfold g19FaceAge; rw [g19EntryStratum_stable idOf G G' fid k h, h]

/-! ## Causal event and entry stratum, neither inferred from the other -/

/-- **The entry stratum is not read off the causal event.** One eligibility input,
    so one causal event `(τ, j+1)` and one `ι_f`, enters at stratum `0` of one
    ledger and at stratum `1` of another. -/
theorem g19_entry_not_from_causal (i : EligInput) :
    g19EntryStratum (R := Unit) id [[.recordFace [faceIdOf i]]] (faceIdOf i) = some 0 ∧
    g19EntryStratum (R := Unit) id [[], [.recordFace [faceIdOf i]]] (faceIdOf i) = some 1 := by
  simp [g19EntryStratum, g19First, g19RecordsFace]

/-- **The causal event is not read off the entry stratum.** Two inputs with
    different causal events (`j` and `j+1`) enter in one stratum of one ledger. -/
theorem g19_causal_not_from_entry (i : EligInput) :
    causalEvent i ≠ causalEvent { i with j := i.j + 1 } ∧
    g19EntryStratum (R := Unit) id [[.recordFace [faceIdOf i, faceIdOf { i with j := i.j + 1 }]]]
      (faceIdOf i) = some 0 ∧
    g19EntryStratum (R := Unit) id [[.recordFace [faceIdOf i, faceIdOf { i with j := i.j + 1 }]]]
      (faceIdOf { i with j := i.j + 1 }) = some 0 := by
  refine ⟨fun h => absurd (congrArg Prod.snd h) (by change i.j + 1 ≠ i.j + 1 + 1; omega), ?_, ?_⟩
  · simp [g19EntryStratum, g19First, g19RecordsFace]
  · simp [g19EntryStratum, g19First, g19RecordsFace]

/-! ## Interleaving: the ledger of a trace of mixed declared operations

Definition 24.1 assigns "every later cycle-boundary, face-recording, and lifecycle append to
one exact ordered stratum", one declared operation per stratum, in call order, records appended
together sharing a stratum. `g19LedgerOfHist` above only sees `recordFace` calls, because
`RecState.hist` is the face ledger's own trace. Here a trace mixes the two kinds: a
`RecordFace_𝒬` call, which runs Definition 22.4's `faceAppend` on the receiver state, and any
other declared append, which leaves `hist` alone and may put several records into its one
stratum. The ledger of the trace has one stratum per operation of either kind. `k_f` read off it
is stable under later appends of either kind, an `other` append never creates an entry, and a
`recordFace` call that first records `ι_f` enters it at the position of that call in the full
trace. The section after this one grounds the `other` appends in the tree's real lifecycle
ledger (`appendEvt`), and the one after that retains Definition 2.3's temporal strata. -/

/-- One declared operation on the extended ledger: a `RecordFace_𝒬` call, or any other declared
    append, which may put several records into its one stratum. -/
inductive G19Op (FR R : Type) where
  | recordFace : QuestionId → List FR → G19Op FR R
  | other : List R → G19Op FR R

/-- The stratum one operation contributes. -/
def g19StratumOf {FR R : Type} : G19Op FR R → List (G19Append FR R)
  | .recordFace _ L => [G19Append.recordFace L]
  | .other rs => rs.map G19Append.other

/-- The extended ledger of a trace: one stratum per operation, in order. -/
def g19LedgerOfTrace {FR R : Type} (t : List (G19Op FR R)) : G19Ledger FR R :=
  t.map g19StratumOf

theorem g19LedgerOfTrace_length {FR R : Type} (t : List (G19Op FR R)) :
    (g19LedgerOfTrace t).length = t.length := by
  simp [g19LedgerOfTrace]

theorem g19LedgerOfTrace_append {FR R : Type} (t t' : List (G19Op FR R)) :
    g19LedgerOfTrace (t ++ t') = g19LedgerOfTrace t ++ g19LedgerOfTrace t' := by
  simp [g19LedgerOfTrace]

/-- Running a trace on a receiver state: `recordFace` is Definition 23.5's call
    (`faceAppend`, `Face.lean:152`); any other append leaves the face ledger's state alone. -/
def g19RunTrace {Op FR R : Type} (st : RecState Op (List FR)) :
    List (G19Op FR R) → RecState Op (List FR)
  | [] => st
  | .recordFace target L :: t => g19RunTrace (faceAppend st target L) t
  | .other _ :: t => g19RunTrace st t

/-- The `recordFace` entries of a trace, in order: what `hist` will hold. -/
def g19FaceHist {FR R : Type} : List (G19Op FR R) → List (QuestionId × List FR)
  | [] => []
  | .recordFace target L :: t => (target, L) :: g19FaceHist t
  | .other _ :: t => g19FaceHist t

/-- A run appends exactly the trace's `recordFace` entries to `hist`, in order: the
    face ledger's own history is the mixed ledger with the `other` strata removed. -/
theorem g19RunTrace_hist {Op FR R : Type} (st : RecState Op (List FR)) (t : List (G19Op FR R)) :
    (g19RunTrace st t).hist = st.hist ++ g19FaceHist t := by
  induction t generalizing st with
  | nil => simp [g19RunTrace, g19FaceHist]
  | cons op t ih =>
    cases op with
    | recordFace target L => simp [g19RunTrace, g19FaceHist, ih, faceAppend]
    | other rs => simp [g19RunTrace, g19FaceHist, ih]

/-- **"Extending `𝒢` does not ... alter `h_𝒬`."** No operation of a trace touches the operative
    state: `faceAppend` changes only `hist`, and an `other` append changes nothing here. -/
theorem g19RunTrace_op {Op FR R : Type} (st : RecState Op (List FR)) (t : List (G19Op FR R)) :
    (g19RunTrace st t).op = st.op := by
  induction t generalizing st with
  | nil => rfl
  | cons op t ih =>
    cases op with
    | recordFace target L =>
      change (g19RunTrace (faceAppend st target L) t).op = st.op
      rw [ih]; rfl
    | other rs => exact ih st

/-- If nothing in `l` satisfies `p`, the first index in `l ++ l'` is the first index in
    `l'` shifted by `l.length`. -/
theorem g19First_append_none {α : Type} (p : α → Bool) (l l' : List α)
    (h : g19First p l = none) :
    g19First p (l ++ l') = (g19First p l').map (· + l.length) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hpa : p a = false := by
      cases hp : p a
      · rfl
      · exact absurd h (by simp [g19First, hp])
    have hl : g19First p l = none := by
      cases hg : g19First p l with
      | none => rfl
      | some k => simp [g19First, hpa, hg] at h
    rw [List.cons_append, g19First_cons_false p a _ hpa, ih hl, Option.map_map]
    cases g19First p l' with
    | none => rfl
    | some k =>
      simp only [Option.map, Function.comp, List.length_cons, Option.some.injEq]
      omega

/-- A prefix in which `ι_f` never enters shifts `k_f` by its length and nothing else. -/
theorem g19EntryStratum_prefix_none {FR R : Type} (idOf : FR → FaceId) (G G' : G19Ledger FR R)
    (fid : FaceId) (h : g19EntryStratum idOf G fid = none) :
    g19EntryStratum idOf (G ++ G') fid = (g19EntryStratum idOf G' fid).map (· + G.length) :=
  g19First_append_none _ G G' h

/-- An `other` stratum records no face, however many records it holds. -/
theorem g19RecordsFace_other {FR R : Type} (idOf : FR → FaceId) (fid : FaceId) (rs : List R) :
    g19RecordsFace idOf fid (g19StratumOf (FR := FR) (.other rs)) = false := by
  simp [g19StratumOf, g19RecordsFace]

/-- **Cycle-boundary and lifecycle appends never create an entry.** -/
theorem g19EntryStratum_trace_other_none {FR R : Type} (idOf : FR → FaceId)
    (t : List (G19Op FR R)) (fid : FaceId) (rs : List R)
    (h : g19EntryStratum idOf (g19LedgerOfTrace t) fid = none) :
    g19EntryStratum idOf (g19LedgerOfTrace (t ++ [.other rs])) fid = none := by
  rw [g19LedgerOfTrace_append, g19EntryStratum_prefix_none idOf _ _ fid h]
  simp [g19LedgerOfTrace, g19EntryStratum, g19First, g19RecordsFace_other]

/-- **Cycle-boundary and lifecycle appends never move an entry.** -/
theorem g19EntryStratum_trace_other_stable {FR R : Type} (idOf : FR → FaceId)
    (t : List (G19Op FR R)) (fid : FaceId) (rs : List R) (k : ℕ)
    (h : g19EntryStratum idOf (g19LedgerOfTrace t) fid = some k) :
    g19EntryStratum idOf (g19LedgerOfTrace (t ++ [.other rs])) fid = some k := by
  rw [g19LedgerOfTrace_append]
  exact g19EntryStratum_stable idOf _ _ fid k h

/-- **A first `RecordFace` call enters `ι_f` at its position in the full trace**, counting
    the `other` operations before it: `k_f` is a stratum of `𝒢`, not an index into `hist`. -/
theorem g19EntryStratum_trace_recordFace {FR R : Type} (idOf : FR → FaceId)
    (t : List (G19Op FR R)) (fid : FaceId) (target : QuestionId) (L : List FR) (r : FR)
    (hnew : g19EntryStratum idOf (g19LedgerOfTrace t) fid = none) (hr : r ∈ L)
    (hid : idOf r = fid) :
    g19EntryStratum idOf (g19LedgerOfTrace (t ++ [.recordFace target L])) fid = some t.length := by
  rw [g19LedgerOfTrace_append, ← g19LedgerOfTrace_length t]
  exact g19EntryStratum_recordFace idOf _ fid _ L r hnew (List.mem_singleton_self _) hr hid

/-- The number of `other` operations in a trace. -/
def g19OtherCount {FR R : Type} : List (G19Op FR R) → ℕ
  | [] => 0
  | .recordFace _ _ :: t => g19OtherCount t
  | .other _ :: t => g19OtherCount t + 1

/-- A trace is its `recordFace` entries and its `other` operations. -/
theorem g19_length_split {FR R : Type} (t : List (G19Op FR R)) :
    t.length = (g19FaceHist t).length + g19OtherCount t := by
  induction t with
  | nil => rfl
  | cons op t ih =>
    cases op with
    | recordFace target L => simp only [List.length_cons, g19FaceHist, g19OtherCount]; omega
    | other rs => simp only [List.length_cons, g19FaceHist, g19OtherCount]; omega

theorem g19OtherCount_eq_zero_iff {FR R : Type} (t : List (G19Op FR R)) :
    g19OtherCount t = 0 ↔ ∀ op ∈ t, ∃ target L, op = G19Op.recordFace target L := by
  induction t with
  | nil => simp [g19OtherCount]
  | cons op t ih =>
    cases op with
    | recordFace target L => simp [g19OtherCount, ih]
    | other rs => simp [g19OtherCount]

/-- The `hist` index and the trace index of a `recordFace` call agree exactly when no
    `other` operation precedes it. -/
theorem g19FaceHist_length_eq_iff {FR R : Type} (t : List (G19Op FR R)) :
    (g19FaceHist t).length = t.length ↔ ∀ op ∈ t, ∃ target L, op = G19Op.recordFace target L := by
  rw [← g19OtherCount_eq_zero_iff]
  have := g19_length_split t
  constructor <;> intro h <;> omega

theorem g19EntryStratum_hist_of_trace {Op FR R : Type} (idOf : FR → FaceId)
    (st : RecState Op (List FR)) (t : List (G19Op FR R)) (fid : FaceId) (target : QuestionId)
    (L : List FR) (r : FR)
    (hst : g19EntryStratum idOf (g19LedgerOfHist (R := R) st.hist) fid = none)
    (hnew : g19EntryStratum idOf (g19LedgerOfTrace t) fid = none) (hr : r ∈ L)
    (hid : idOf r = fid) :
    g19EntryStratum idOf (g19LedgerOfHist (R := R)
        (g19RunTrace st (t ++ [.recordFace target L])).hist) fid
      = some (st.hist.length + (g19FaceHist t).length) := by
  have hrun : g19RunTrace st (t ++ [.recordFace target L]) =
      faceAppend (g19RunTrace st t) target L := by
    clear hnew hst
    induction t generalizing st with
    | nil => rfl
    | cons op t ih =>
      cases op with
      | recordFace tg L' => exact ih (faceAppend st tg L')
      | other rs => exact ih st
  rw [hrun]
  have hpre : g19EntryStratum idOf (g19LedgerOfHist (R := R) (g19RunTrace st t).hist) fid
      = none := by
    rw [g19RunTrace_hist]
    have hfh : g19EntryStratum idOf (g19LedgerOfHist (R := R) (g19FaceHist t)) fid = none := by
      clear hst hrun
      induction t with
      | nil => rfl
      | cons op t ih =>
        cases op with
        | recordFace tg L' =>
          have h0 : g19RecordsFace idOf fid (g19StratumOf (FR := FR) (R := R)
              (.recordFace tg L')) = false := by
            cases hq : g19RecordsFace idOf fid (g19StratumOf (FR := FR) (R := R)
                (.recordFace tg L'))
            · rfl
            · exact absurd hnew (by
                simp [g19LedgerOfTrace, g19EntryStratum, g19First, hq])
          have hrest : g19EntryStratum idOf (g19LedgerOfTrace t) fid = none := by
            simp only [g19LedgerOfTrace, List.map_cons, g19EntryStratum, g19First, h0,
              Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at hnew
            exact hnew
          simp only [g19FaceHist, g19LedgerOfHist, List.map_cons, g19EntryStratum, g19First]
          have h0' : g19RecordsFace idOf fid
              ([G19Append.recordFace L'] : List (G19Append FR R)) = false := h0
          simp only [h0', Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff]
          exact ih hrest
        | other rs =>
          have hrest : g19EntryStratum idOf (g19LedgerOfTrace t) fid = none := by
            simp only [g19LedgerOfTrace, List.map_cons, g19EntryStratum, g19First,
              g19RecordsFace_other, Bool.false_eq_true, ↓reduceIte,
              Option.map_eq_none_iff] at hnew
            exact hnew
          exact ih hrest
    rw [g19LedgerOfHist_append, g19EntryStratum_prefix_none idOf _ _ fid hst, hfh]
    rfl
  rw [g19EntryStratum_recordFace_call idOf _ target L r fid hpre hr hid, g19RunTrace_hist]
  simp

/-- **The two positions of one call.** From an empty face history, the first `RecordFace` call
    that records `ι_f` enters at stratum `t.length` of `𝒢` and at index `(g19FaceHist t).length`
    of `hist`; the difference is the number of `other` operations before the call
    (`g19_length_split`), and the two agree exactly when that number is zero
    (`g19FaceHist_length_eq_iff`). -/
theorem g19_entry_positions {Op FR R : Type} (idOf : FR → FaceId) (st : RecState Op (List FR))
    (t : List (G19Op FR R)) (fid : FaceId) (target : QuestionId) (L : List FR) (r : FR)
    (hst0 : st.hist = [])
    (hnew : g19EntryStratum idOf (g19LedgerOfTrace t) fid = none) (hr : r ∈ L)
    (hid : idOf r = fid) :
    g19EntryStratum idOf (g19LedgerOfTrace (t ++ [.recordFace target L])) fid
        = some t.length ∧
    g19EntryStratum idOf (g19LedgerOfHist (R := R)
        (g19RunTrace st (t ++ [.recordFace target L])).hist) fid
        = some (g19FaceHist t).length ∧
    t.length = (g19FaceHist t).length + g19OtherCount t := by
  have hst : g19EntryStratum idOf (g19LedgerOfHist (R := R) st.hist) fid = none := by
    rw [hst0]; rfl
  refine ⟨g19EntryStratum_trace_recordFace idOf t fid target L r hnew hr hid, ?_,
    g19_length_split t⟩
  rw [g19EntryStratum_hist_of_trace idOf st t fid target L r hst hnew hr hid, hst0]
  simp

/-! ## The lifecycle ledger: the tree's real producer of `other` appends

`Lifecycle.lean` has the global lifecycle ledger `𝔇` (`LifeLedger`, keyed by `(ι_f, r, n_r)`) and
its one append operation `appendEvt`, which is append-only exactly as `faceAppend` is. A trace
over both ledgers gives `G19Append.other` the grounding `recordFace` has above: a lifecycle
append is one declared operation, occupies one stratum of `𝒢`, and writes one keyed event to
`𝔇`. -/

/-- What one `appendEvt` writes. -/
abbrev G19LifeRec (P Y : Type) := (FaceId × ℕ × ℕ) × LifeEvt P Y

/-- A declared operation on the two real ledgers. -/
inductive G19LifeOp (FR P Y : Type) where
  | recordFace : QuestionId → List FR → G19LifeOp FR P Y
  | lifecycle : LifeEvt P Y → G19LifeOp FR P Y

/-- Its stratum of `𝒢`: a lifecycle append is an `other` stratum holding the keyed event. -/
def g19OpOfLife {FR P Y : Type} : G19LifeOp FR P Y → G19Op FR (G19LifeRec P Y)
  | .recordFace target L => .recordFace target L
  | .lifecycle e => .other [((e.fid, e.m, e.n), e)]

/-- Running a trace on the receiver state and the lifecycle ledger together. -/
def g19RunLife {Op FR P Y : Type} (st : RecState Op (List FR)) (D : LifeLedger P Y) :
    List (G19LifeOp FR P Y) → RecState Op (List FR) × LifeLedger P Y
  | [] => (st, D)
  | .recordFace target L :: t => g19RunLife (faceAppend st target L) D t
  | .lifecycle e :: t => g19RunLife st (appendEvt D e) t

/-- The lifecycle entries of a trace, in order: what `𝔇` will hold. -/
def g19LifeHist {FR P Y : Type} : List (G19LifeOp FR P Y) → LifeLedger P Y
  | [] => []
  | .recordFace _ _ :: t => g19LifeHist t
  | .lifecycle e :: t => ((e.fid, e.m, e.n), e) :: g19LifeHist t

/-- The face ledger after a lifecycle trace is the face ledger of its `recordFace` calls. -/
theorem g19RunLife_hist {Op FR P Y : Type} (st : RecState Op (List FR)) (D : LifeLedger P Y)
    (t : List (G19LifeOp FR P Y)) :
    (g19RunLife st D t).1.hist = st.hist ++ g19FaceHist (t.map g19OpOfLife) := by
  induction t generalizing st D with
  | nil => simp [g19RunLife, g19FaceHist]
  | cons op t ih =>
    cases op with
    | recordFace target L => simp [g19RunLife, g19FaceHist, g19OpOfLife, ih, faceAppend]
    | lifecycle e => simp [g19RunLife, g19FaceHist, g19OpOfLife, ih]

/-- The lifecycle ledger after a trace is `𝔇` followed by the trace's lifecycle events, one
    `appendEvt` each, in call order. -/
theorem g19RunLife_life {Op FR P Y : Type} (st : RecState Op (List FR)) (D : LifeLedger P Y)
    (t : List (G19LifeOp FR P Y)) :
    (g19RunLife st D t).2 = D ++ g19LifeHist t := by
  induction t generalizing st D with
  | nil => simp [g19RunLife, g19LifeHist]
  | cons op t ih =>
    cases op with
    | recordFace target L => simp [g19RunLife, g19LifeHist, ih]
    | lifecycle e => simp [g19RunLife, g19LifeHist, ih, appendEvt]

/-- `h_𝒬` is not altered by a lifecycle trace either. -/
theorem g19RunLife_op {Op FR P Y : Type} (st : RecState Op (List FR)) (D : LifeLedger P Y)
    (t : List (G19LifeOp FR P Y)) : (g19RunLife st D t).1.op = st.op := by
  induction t generalizing st D with
  | nil => rfl
  | cons op t ih =>
    cases op with
    | recordFace target L =>
      change (g19RunLife (faceAppend st target L) D t).1.op = st.op
      rw [ih]; rfl
    | lifecycle e => exact ih st (appendEvt D e)

/-- The extended ledger read off a real lifecycle ledger: one stratum per `appendEvt` call. -/
def g19LedgerOfLife {FR P Y : Type} (D : LifeLedger P Y) : G19Ledger FR (G19LifeRec P Y) :=
  D.map fun e => [G19Append.other e]

/-- **One `appendEvt` call, one stratum**, the analogue of `g19LedgerOfHist_faceAppend`: the
    call extends the ledger by exactly one stratum holding the keyed event it wrote. -/
theorem g19LedgerOfLife_appendEvt {FR P Y : Type} (D : LifeLedger P Y) (e : LifeEvt P Y) :
    g19LedgerOfLife (FR := FR) (appendEvt D e) =
      g19LedgerOfLife D ++ [[G19Append.other ((e.fid, e.m, e.n), e)]] := by
  simp [g19LedgerOfLife, appendEvt]

/-- The lifecycle ledger after a run, read as strata: `𝔇`'s strata followed by one stratum per
    lifecycle event of the trace, in call order. -/
theorem g19LedgerOfLife_run {Op FR P Y : Type} (st : RecState Op (List FR)) (D : LifeLedger P Y)
    (t : List (G19LifeOp FR P Y)) :
    g19LedgerOfLife (FR := FR) (g19RunLife st D t).2 =
      g19LedgerOfLife D ++ g19LedgerOfLife (g19LifeHist t) := by
  rw [g19RunLife_life]
  simp [g19LedgerOfLife]

/-- The lifecycle ledger's own strata never hold a face entry. -/
theorem g19EntryStratum_ledgerOfLife_none {FR P Y : Type} (idOf : FR → FaceId)
    (D : LifeLedger P Y) (fid : FaceId) :
    g19EntryStratum idOf (g19LedgerOfLife (FR := FR) D) fid = none := by
  induction D with
  | nil => rfl
  | cons e D ih =>
    simp only [g19LedgerOfLife, List.map_cons, g19EntryStratum, g19First]
    have h0 : g19RecordsFace idOf fid ([G19Append.other e] : List (G19Append FR (G19LifeRec P Y)))
        = false := by simp [g19RecordsFace]
    simp only [h0, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff]
    simpa [g19LedgerOfLife, g19EntryStratum] using ih

/-- **A lifecycle append never creates or moves a face entry**, on the real ledger pair. -/
theorem g19_life_lifecycle_none {FR P Y : Type} (idOf : FR → FaceId) (t : List (G19LifeOp FR P Y))
    (fid : FaceId) (e : LifeEvt P Y)
    (h : g19EntryStratum idOf (g19LedgerOfTrace (t.map g19OpOfLife)) fid = none) :
    g19EntryStratum idOf (g19LedgerOfTrace ((t ++ [G19LifeOp.lifecycle e]).map g19OpOfLife)) fid
      = none := by
  rw [List.map_append]
  exact g19EntryStratum_trace_other_none idOf _ fid _ h

theorem g19_life_lifecycle_stable {FR P Y : Type} (idOf : FR → FaceId)
    (t : List (G19LifeOp FR P Y)) (fid : FaceId) (e : LifeEvt P Y) (k : ℕ)
    (h : g19EntryStratum idOf (g19LedgerOfTrace (t.map g19OpOfLife)) fid = some k) :
    g19EntryStratum idOf (g19LedgerOfTrace ((t ++ [G19LifeOp.lifecycle e]).map g19OpOfLife)) fid
      = some k := by
  rw [List.map_append]
  exact g19EntryStratum_trace_other_stable idOf _ fid _ k h

/-- **A first `RecordFace` call enters at its stratum of the full trace**, lifecycle appends
    counted. -/
theorem g19_life_recordFace {FR P Y : Type} (idOf : FR → FaceId) (t : List (G19LifeOp FR P Y))
    (fid : FaceId) (target : QuestionId) (L : List FR) (r : FR)
    (hnew : g19EntryStratum idOf (g19LedgerOfTrace (t.map g19OpOfLife)) fid = none)
    (hr : r ∈ L) (hid : idOf r = fid) :
    g19EntryStratum idOf
      (g19LedgerOfTrace ((t ++ [G19LifeOp.recordFace target L]).map g19OpOfLife)) fid
      = some t.length := by
  have hl : (t.map g19OpOfLife).length = t.length := by simp
  rw [List.map_append, ← hl]
  exact g19EntryStratum_trace_recordFace idOf _ fid target L r hnew hr hid

/-! ## A generic face-free prefix (used by the temporal strata below) -/

/-- A prefix of strata made of `other` appends only, one list of records per stratum. -/
def g19TemporalPrefix {FR R : Type} (T : List (List R)) : G19Ledger FR R :=
  T.map (List.map G19Append.other)

theorem g19TemporalPrefix_length {FR R : Type} (T : List (List R)) :
    (g19TemporalPrefix (FR := FR) T).length = T.length := by
  simp [g19TemporalPrefix]

/-- No `other`-only stratum records a face. -/
theorem g19RecordsFace_temporal {FR R : Type} (idOf : FR → FaceId) (fid : FaceId) (st : List R) :
    g19RecordsFace idOf fid (st.map (G19Append.other (FR := FR))) = false := by
  simp [g19RecordsFace]

/-- `ι_f` never enters during a face-free prefix. -/
theorem g19EntryStratum_temporalPrefix_none {FR R : Type} (idOf : FR → FaceId)
    (T : List (List R)) (fid : FaceId) :
    g19EntryStratum idOf (g19TemporalPrefix (FR := FR) T) fid = none := by
  induction T with
  | nil => rfl
  | cons st T ih =>
    simp only [g19TemporalPrefix, List.map_cons, g19EntryStratum, g19First,
      g19RecordsFace_temporal, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff]
    simpa [g19TemporalPrefix, g19EntryStratum] using ih

/-- A face-free prefix shifts every face-entry stratum by its length and changes nothing else. -/
theorem g19EntryStratum_temporalPrefix {FR R : Type} (idOf : FR → FaceId) (T : List (List R))
    (G : G19Ledger FR R) (fid : FaceId) :
    g19EntryStratum idOf (g19TemporalPrefix T ++ G) fid
      = (g19EntryStratum idOf G fid).map (· + T.length) := by
  rw [g19EntryStratum_prefix_none idOf _ G fid (g19EntryStratum_temporalPrefix_none idOf T fid),
    g19TemporalPrefix_length]

/-! ## Definition 2.3's temporal event strata retained as the first strata of `𝒢`

"Obtained by retaining the temporal event strata of Definition 2.3 and assigning every
**later** ... append to one exact ordered stratum": the temporal strata come first and hold
Definition 2.3's records (`Temporal.Record`, one list per stratum, so records of one advance
share a stratum as the book's `slot` says); no `RecordFace` append is among them, because face
recording is a later append. That reading is a definition here, not a theorem: the book fixes
it by the word "later". -/

/-- A record of the extended ledger that is not a face: a retained Definition 2.3 record, or a
    keyed lifecycle event. -/
abbrev G19Other (P Y : Type) := RatioSpace.Two.Record ⊕ G19LifeRec P Y

/-- The retained temporal strata, from a list of Definition 2.3 strata. -/
def g19TemporalStrata {FR P Y : Type} (T : List (List RatioSpace.Two.Record)) :
    G19Ledger FR (G19Other P Y) :=
  T.map (List.map fun c => G19Append.other (Sum.inl c))

theorem g19TemporalStrata_eq_prefix {FR P Y : Type} (T : List (List RatioSpace.Two.Record)) :
    g19TemporalStrata (FR := FR) (P := P) (Y := Y) T =
      g19TemporalPrefix (T.map (List.map Sum.inl)) := by
  simp [g19TemporalStrata, g19TemporalPrefix, List.map_map, Function.comp_def]

theorem g19TemporalStrata_length {FR P Y : Type} (T : List (List RatioSpace.Two.Record)) :
    (g19TemporalStrata (FR := FR) (P := P) (Y := Y) T).length = T.length := by
  simp [g19TemporalStrata]

/-- `ι_f` never enters during the temporal strata. -/
theorem g19EntryStratum_temporalStrata_none {FR P Y : Type} (idOf : FR → FaceId)
    (T : List (List RatioSpace.Two.Record)) (fid : FaceId) :
    g19EntryStratum idOf (g19TemporalStrata (FR := FR) (P := P) (Y := Y) T) fid = none := by
  rw [g19TemporalStrata_eq_prefix]
  exact g19EntryStratum_temporalPrefix_none idOf _ fid

/-- **Retaining the temporal strata shifts every face-entry stratum by their number and
    changes nothing else.** -/
theorem g19EntryStratum_temporalStrata {FR P Y : Type} (idOf : FR → FaceId)
    (T : List (List RatioSpace.Two.Record)) (G : G19Ledger FR (G19Other P Y)) (fid : FaceId) :
    g19EntryStratum idOf (g19TemporalStrata T ++ G) fid
      = (g19EntryStratum idOf G fid).map (· + T.length) := by
  rw [g19TemporalStrata_eq_prefix, g19EntryStratum_temporalPrefix, List.length_map]

/-- A temporal ledger is well formed when every record sits in the stratum its own `stratum`
    field names. -/
abbrev G19TemporalWF (T : List (List RatioSpace.Two.Record)) : Prop :=
  ∀ (k : ℕ) (st : List RatioSpace.Two.Record), T[k]? = some st → ∀ c ∈ st, c.stratum = k

/-- **Extending `𝒢` keeps every temporal stratum in place**: below `T.length` the extended
    ledger reads exactly as the temporal ledger. -/
theorem g19_extension_keeps_strata {FR P Y : Type} (T : List (List RatioSpace.Two.Record))
    (G : G19Ledger FR (G19Other P Y)) (k : ℕ) (hk : k < T.length) :
    (g19TemporalStrata (FR := FR) (P := P) (Y := Y) T ++ G)[k]? = (g19TemporalStrata T)[k]? :=
  List.getElem?_append_left (by rw [g19TemporalStrata_length]; exact hk)

/-- **Extending `𝒢` does not alter a temporal record's age.** A Definition 2.3 record `c` in
    stratum `k` of a well-formed temporal ledger is still found in stratum `k` of the extended
    ledger, whatever `G` was appended, and at any read `n ≥ k` its Definition 24.1 age is
    Definition 2.3's `archiveAge`, computed from `(k, n)` alone. -/
theorem g19_extension_keeps_temporal_age {FR P Y : Type} (T : List (List RatioSpace.Two.Record))
    (G : G19Ledger FR (G19Other P Y)) (hwf : G19TemporalWF T) (k : ℕ)
    (st : List RatioSpace.Two.Record) (hk : T[k]? = some st) (c : RatioSpace.Two.Record)
    (hc : c ∈ st) (n : ℕ) (h : k ≤ n) :
    (∃ st', (g19TemporalStrata (FR := FR) (P := P) (Y := Y) T ++ G)[k]? = some st' ∧
      G19Append.other (Sum.inl c) ∈ st') ∧
    g19ArchAge c.stratum n = some (archiveAge ⟨c, n, by rw [hwf k st hk c hc]; exact h⟩) := by
  have hlt : k < T.length := (List.getElem?_eq_some_iff.mp hk).1
  have e := hwf k st hk c hc
  refine ⟨⟨st.map (fun c => G19Append.other (Sum.inl c)), ?_, List.mem_map.mpr ⟨c, hc, rfl⟩⟩, ?_⟩
  · rw [g19_extension_keeps_strata T G k hlt]
    simp only [g19TemporalStrata, List.getElem?_map, hk, Option.map_some]
  · exact (g19ArchAge_eq_some_iff _ _ _).mpr ⟨by omega, by simp only [archiveAge_def]; omega⟩

/-! ## Readers of `aArch`, through Definition 24.1's age

`Lifecycle.aArch` is the truncated age on `ℕ`. Every site where it
produces a stored value (`mkPacket`, `renewalRecord`, `gateVector`, and through them the face
packets of `G2_20`) is covered by a theorem saying what value Definition 24.1 assigns there, with
the before-entry reading stated where the consumer can be called before entry. The other readers
in the tree are the two horizon lemmas (`horizon_terminal`, `profile_read_stays_zero`), whose
hypothesis is shown to force a read after entry; `G2_28`'s finite-profile gate, where the
before-entry reading is made explicit; `G2_29`'s `WellAged`; and `G2_30`'s `age_transport`, which
`g19_age_transport_all` carries at every pair of strata, before entry as well as after, from
`ν_diff` alone. `age_reads_only_strata` and `covariance_conditional`'s age conjunct are
`aArch k n = aArch k n` and are not readers; G2_22, G2_26 and G2_29's `strata_move_three_gates`
read `aArch` only at `k ≤ n` by construction. -/

/-- `mkPacket`'s age field is the Definition 24.1 age at every read after entry. -/
theorem g19_mkPacket_age {Rec Cyc : Type} (fid : FaceId) (rec : Rec) (caus : ℕ × ℕ) (k n : ℕ)
    (wx : Word) (s : Bool) (v : Word) (cyc : Cyc) (h : k ≤ n) :
    g19ArchAge k n = some (mkPacket fid rec caus k n wx s v cyc).age :=
  g19ArchAge_eq_aArch h

/-- The renewal record's age field (Definition 24.6) is the Definition 24.1 age after entry. -/
theorem g19_renewalRecord_age {Y : Type} (v u : Word) (r k n : ℕ) (y : RecStat Y) (h : k ≤ n) :
    g19ArchAge k n = some (renewalRecord v u r k n y).age :=
  g19ArchAge_eq_aArch h

/-- The readability gate reads the Definition 24.1 age after entry. -/
theorem g19_gateVector_read {P Y Ph St : Type} [DecidableEq Y] (Θ : Retention P Y Ph St)
    (fid : FaceId) (S : St) (Z Zatt : P) (lift : LiftStatus) (k n : ℕ) (h : k ≤ n) :
    ∃ a, g19ArchAge k n = some a ∧
      (gateVector Θ fid S Z Zatt lift k n).read = Θ.chiRead Z k n a :=
  ⟨aArch k n, g19ArchAge_eq_aArch h, rfl⟩

/-- **Before entry the gate reads age `0`, the value Definition 24.1 reserves for a read at
    entry, while Definition 24.1 assigns no age at all.** This is the consumer-side face of
    `g19_aArch_truncates`; a caller must supply `k ≤ n` (as `g19_gateVector_read` does) for the
    gate's reading to be the book's. -/
theorem g19_gateVector_read_before_entry {P Y Ph St : Type} [DecidableEq Y]
    (Θ : Retention P Y Ph St) (fid : FaceId) (S : St) (Z Zatt : P) (lift : LiftStatus)
    (k n : ℕ) (h : n < k) :
    g19ArchAge k n = none ∧
      (gateVector Θ fid S Z Zatt lift k n).read = Θ.chiRead Z k n 0 := by
  refine ⟨(g19ArchAge_eq_none_iff k n).mpr h, ?_⟩
  change Θ.chiRead Z k n (aArch k n) = Θ.chiRead Z k n 0
  rw [show aArch k n = 0 by unfold aArch; omega]

/-- **Every packet of a face carries the Definition 24.1 age.** A `TPacket` that is a packet
    of a face (`G2_20`'s `IsFacePacket`: built by `mkPacket` at a read stratum `n ≥ k`) has
    `g19ArchAge Z.k Z.n = some Z.age`; no hypothesis on the lineage is needed. -/
theorem g19_facePacket_age {Rec Cyc : Type} (i : QuestionId) (j : ℕ) (fid : FaceId) (rec : Rec)
    (k : ℕ) (cyc : Cyc) (Z : TPacket Rec Cyc) (h : G2_20.IsFacePacket i j fid rec k cyc Z) :
    g19ArchAge Z.k Z.n = some Z.age := by
  obtain ⟨n, u, hkn, rfl⟩ := h
  exact g19ArchAge_eq_aArch hkn

/-- `G2_29`'s `WellAged` (age field equals `aArch`) together with `k ≤ n` is exactly
    "the age field is Definition 24.1's age". -/
theorem g19_wellAged_iff {Rec Cyc : Type} (Z : TPacket Rec Cyc) :
    (G2_29.WellAged Z ∧ Z.k ≤ Z.n) ↔ g19ArchAge Z.k Z.n = some Z.age := by
  constructor
  · rintro ⟨hw, hle⟩
    rw [hw]; exact g19ArchAge_eq_aArch hle
  · intro h
    have := (g19ArchAge_eq_some_iff _ _ _).mp h
    exact ⟨by unfold G2_29.WellAged aArch; omega, this.1⟩

/-- **The horizon lemmas read after entry.** The hypothesis `H < aArch k n` of
    `horizon_terminal` and `profile_read_stays_zero` is satisfiable only when `k < n`, so both
    lemmas speak about reads after entry and the age they read is Definition 24.1's. -/
theorem g19_horizon_after_entry (k n H : ℕ) (hn : H < aArch k n) :
    k < n ∧ g19ArchAge k n = some (aArch k n) := by
  have : k < n := by unfold aArch at hn; omega
  exact ⟨this, g19ArchAge_eq_aArch (Nat.le_of_lt this)⟩

/-- `profile_read_stays_zero`, read through Definition 24.1: the later read is after entry and
    the gate is zero at the age Definition 24.1 assigns. -/
theorem g19_profile_read_stays_zero {P Y Ph St : Type} (Λ : Receiver P Y)
    (sock : FaceId → St → ℕ → Bool) (chiAdm : P → Bool) (theta : P → Ph) (window : Ph → Bool)
    (lw : LiftStatus → Bool) (H k n n' : ℕ) (Z' : P) (hn : H < aArch k n) (hle : n ≤ n') :
    ∃ a, g19ArchAge k n' = some a ∧
      (finiteProfile Λ sock chiAdm theta window lw H).chiRead Z' k n' a = false :=
  ⟨aArch k n', g19ArchAge_eq_aArch ((g19_horizon_after_entry k n H hn).1.le.trans hle),
    decide_eq_false (Nat.not_le_of_gt (horizon_terminal k n n' H hn hle))⟩

/-- **`G2_28`'s finite profile, before entry: the readability gate passes.** `aArch k n = 0 ≤ H`
    for `n < k`, so a packet read before its own entry stratum is readable by the finite
    profile, while Definition 24.1 assigns it no age. This is the defect at the consumer
    Receiver Declaration 24.16 names; the profile's gate is the book's only under `k ≤ n`
    (next theorem). -/
theorem g19_finiteProfile_read_before_entry {P Y Ph St : Type} [DecidableEq Y]
    (D : G2_28.FiniteProfile P Y Ph St) (fid : FaceId) (S : St) (Z Zatt : P)
    (lift : LiftStatus) (k n : ℕ) (h : n < k) :
    g19ArchAge k n = none ∧
      (gateVector D.toRetention fid S Z Zatt lift k n).read = true := by
  refine ⟨(g19ArchAge_eq_none_iff k n).mpr h, ?_⟩
  change decide (aArch k n ≤ D.H) = true
  exact decide_eq_true (by unfold aArch; omega)

/-- **`G2_28`'s finite profile, after entry**: `g_read = 1 ⟺ a_arch ≤ H_Θ` with `a_arch` the
    Definition 24.1 age. -/
theorem g19_finiteProfile_read_after_entry {P Y Ph St : Type} [DecidableEq Y]
    (D : G2_28.FiniteProfile P Y Ph St) (fid : FaceId) (S : St) (Z Zatt : P)
    (lift : LiftStatus) (k n : ℕ) (h : k ≤ n) :
    (gateVector D.toRetention fid S Z Zatt lift k n).read = true ↔
      ∃ a, g19ArchAge k n = some a ∧ a ≤ D.H := by
  change decide (aArch k n ≤ D.H) = true ↔ _
  constructor
  · intro hd
    exact ⟨aArch k n, g19ArchAge_eq_aArch h, decide_eq_true_iff.mp hd⟩
  · rintro ⟨a, ha, hle⟩
    have := (g19ArchAge_eq_some_iff k n a).mp ha
    exact decide_eq_true (by unfold aArch; omega)

/-- **`G2_30`'s `age_transport`, after entry.** A transport carries the Definition 24.1 age of
    every read after entry: for `k < n`, `ν_diff` forces `ν k < ν n`, and at `k = n` both ages
    are `0`. -/
theorem g19_age_transport {P Y Ph St P' Y' Ph' St' : Type} {Θ : Retention P Y Ph St}
    {Θ' : Retention P' Y' Ph' St'} {wO : P → Word} {wO' : P' → Word}
    (T : G2_30.Transport Θ Θ' wO wO') (k n : ℕ) (hkn : k ≤ n) :
    g19ArchAge (T.ν k) (T.ν n) = g19ArchAge k n := by
  rcases Nat.eq_or_lt_of_le hkn with rfl | hlt
  · rw [g19ArchAge_entry, g19ArchAge_entry]
  · have hd := T.ν_diff k n hkn
    have hle : T.ν k ≤ T.ν n := by omega
    rw [g19ArchAge_eq_aArch hle, g19ArchAge_eq_aArch hkn, G2_30.age_transport T k n hkn]

/-- `Transport.ν` is strictly monotone: for `a < b`, `ν_diff` gives `ν b − ν a = b − a ≥ 1`. -/
theorem g19_nu_strictMono {P Y Ph St P' Y' Ph' St' : Type} {Θ : Retention P Y Ph St}
    {Θ' : Retention P' Y' Ph' St'} {wO : P → Word} {wO' : P' → Word}
    (T : G2_30.Transport Θ Θ' wO wO') (a b : ℕ) (h : a < b) : T.ν a < T.ν b := by
  have := T.ν_diff a b h.le
  omega

/-- **`G2_30`'s `age_transport`, before entry.** A transport keeps a read before entry before
    entry, from `ν_diff` alone: Definition 24.1 assigns no age on either side. -/
theorem g19_age_transport_before_entry {P Y Ph St P' Y' Ph' St' : Type}
    {Θ : Retention P Y Ph St} {Θ' : Retention P' Y' Ph' St'} {wO : P → Word} {wO' : P' → Word}
    (T : G2_30.Transport Θ Θ' wO wO') (k n : ℕ) (h : n < k) :
    g19ArchAge (T.ν k) (T.ν n) = none ∧ g19ArchAge k n = none :=
  ⟨(g19ArchAge_eq_none_iff _ _).mpr (g19_nu_strictMono T n k h),
    (g19ArchAge_eq_none_iff _ _).mpr h⟩

/-- **`age_transport` at every pair of strata**: the Definition 24.1 age, `some` or `none`, is
    carried by every transport. -/
theorem g19_age_transport_all {P Y Ph St P' Y' Ph' St' : Type} {Θ : Retention P Y Ph St}
    {Θ' : Retention P' Y' Ph' St'} {wO : P → Word} {wO' : P' → Word}
    (T : G2_30.Transport Θ Θ' wO wO') (k n : ℕ) :
    g19ArchAge (T.ν k) (T.ν n) = g19ArchAge k n := by
  rcases Nat.lt_or_ge n k with h | h
  · obtain ⟨h1, h2⟩ := g19_age_transport_before_entry T k n h
    rw [h1, h2]
  · exact g19_age_transport T k n h

#print axioms g19LedgerOfTrace
#print axioms g19RunTrace_hist
#print axioms g19RunTrace_op
#print axioms g19First_append_none
#print axioms g19EntryStratum_prefix_none
#print axioms g19EntryStratum_trace_other_none
#print axioms g19EntryStratum_trace_other_stable
#print axioms g19EntryStratum_trace_recordFace
#print axioms g19_length_split
#print axioms g19OtherCount_eq_zero_iff
#print axioms g19FaceHist_length_eq_iff
#print axioms g19EntryStratum_hist_of_trace
#print axioms g19_entry_positions
#print axioms g19RunLife_hist
#print axioms g19RunLife_life
#print axioms g19RunLife_op
#print axioms g19LedgerOfLife_appendEvt
#print axioms g19_life_lifecycle_none
#print axioms g19_life_lifecycle_stable
#print axioms g19_life_recordFace
#print axioms g19TemporalPrefix
#print axioms g19EntryStratum_temporalPrefix_none
#print axioms g19EntryStratum_temporalPrefix
#print axioms g19TemporalStrata
#print axioms g19EntryStratum_temporalStrata_none
#print axioms g19EntryStratum_temporalStrata
#print axioms g19_extension_keeps_strata
#print axioms g19_extension_keeps_temporal_age
#print axioms g19_mkPacket_age
#print axioms g19_renewalRecord_age
#print axioms g19_gateVector_read
#print axioms g19_gateVector_read_before_entry
#print axioms g19_facePacket_age
#print axioms g19_wellAged_iff
#print axioms g19_horizon_after_entry
#print axioms g19_profile_read_stays_zero
#print axioms g19_finiteProfile_read_before_entry
#print axioms g19_finiteProfile_read_after_entry
#print axioms g19_age_transport
#print axioms g19_nu_strictMono
#print axioms g19_age_transport_before_entry
#print axioms g19_age_transport_all
#print axioms g19LedgerOfLife_run
#print axioms g19EntryStratum_ledgerOfLife_none
#print axioms g19_none_ne_some
#print axioms g19RecordsFace
#print axioms g19First
#print axioms g19First_cons_true
#print axioms g19First_cons_false
#print axioms g19First_eq_some_iff
#print axioms g19_isFirst_unique
#print axioms g19First_append_of_some
#print axioms g19First_append_new
#print axioms g19EntryStratum
#print axioms g19EntryStratum_spec
#print axioms g19EntryStratum_unique
#print axioms g19EntryStratum_stable
#print axioms g19EntryStratum_recordFace
#print axioms g19LedgerOfHist
#print axioms g19LedgerOfHist_length
#print axioms g19LedgerOfHist_faceAppend
#print axioms g19EntryStratum_recordFace_call
#print axioms g19EntryStratum_recordFace_stable
#print axioms g19ArchAge
#print axioms g19ArchAge_eq_some_iff
#print axioms g19ArchAge_eq_none_iff
#print axioms g19ArchAge_entry
#print axioms g19ArchAge_eq_aArch
#print axioms g19ArchAge_eq_archiveAge
#print axioms g19_aArch_truncates
#print axioms g19FaceAge
#print axioms g19FaceAge_eq_some_iff
#print axioms g19FaceAge_stable
#print axioms g19_entry_not_from_causal
#print axioms g19_causal_not_from_entry

end G2_19
end Gaps
end RatioSpace
