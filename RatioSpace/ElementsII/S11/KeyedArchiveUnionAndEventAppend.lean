/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S11.Advance
/-!
  Gap G2-09 · Elements II Definition 11.2, keyed archive union and event append.

  Two things the book says that `Advance.lean` does not state:

  * the event stratum carries **one tick marker** (`append` there is plain list
    concatenation on `QuestionId × Aux`, with no marker);
  * the stratum's **internal storage order has no mathematical effect** (a
    comment there; Theorem 12.7's Lean covers proposals and support only).

  Built here: a tick-marked stratum, a stratified ledger with temporal append,
  the bridge showing the flat ledger `Advance.append` builds is the forgetful
  image of the stratified one, and storage-order independence as theorems about
  every reading that factors through the stratum's marker and its multiset of
  keyed records. Also the keyed-union clauses E2-20 fixes: the side condition is
  vacuous on disjoint archives, and the union loses nothing and invents nothing.
-/

namespace RatioSpace
namespace Gaps
namespace G2_09

open RatioSpace.Two RatioSpace.Two.Advance

/-! ## The keyed union (E2-20's reading) -/

/-- **E2-20: archives with disjoint identifiers satisfy the side condition
    vacuously.** -/
theorem keyedCompatible_of_disjoint {H H' : List Core}
    (hdisj : ∀ x ∈ H, ∀ y ∈ H', x.id ≠ y.id) : KeyedCompatible H H' :=
  fun x hx y hy hxy => absurd hxy (hdisj x hx y hy)

/-- **The union invents nothing**: every member of `H ⊔_ι H'` is a member of `H`
    or of `H'`. No hypothesis. -/
theorem mem_keyedUnion_of {H H' : List Core} {z : Core} (hz : z ∈ keyedUnion H H') :
    z ∈ H ∨ z ∈ H' := by
  rcases List.mem_append.mp hz with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_filter.mp h).1

/-- **Definition 11.2 with E2-20's side condition: lossless and exact.** Under
    `KeyedCompatible`, a core lies in the union exactly when it lies in one of
    the two archives. -/
theorem mem_keyedUnion_iff {H H' : List Core} (hc : KeyedCompatible H H') (z : Core) :
    z ∈ keyedUnion H H' ↔ z ∈ H ∨ z ∈ H' :=
  ⟨mem_keyedUnion_of, fun h => h.elim mem_keyedUnion_left (mem_keyedUnion_right hc)⟩

/-! ## The tick-marked stratum -/

/-- **Definition 11.2's tick marker** `(τ, j → j+1)`. The target tick is not a
    field: it is `src + 1` by construction, so no marker can name a jump. -/
structure TickMarker where
  /-- `τ`, the question cycle. -/
  cycle : ℕ
  /-- `j`, the tick the stratum advances from. -/
  src : ℕ
deriving DecidableEq

/-- The tick the marker advances to, `j + 1`. -/
def TickMarker.tgt (m : TickMarker) : ℕ := m.src + 1

/-- **Definition 11.2's event stratum** `ΔE_{j+1}`: one tick marker together
    with a finite collection of occurrence-keyed records. -/
structure Stratum (R : Type) where
  marker : TickMarker
  records : List (QuestionId × R)

/-- A stratified event ledger `E_j`: its strata, in temporal order. -/
abbrev StratLedger (R : Type) := List (Stratum R)

/-- **Definition 11.2, temporal append** `E_j ⁀ ΔE_{j+1}`: the whole stratum is
    placed after every stratum already in the ledger. -/
def appendStratum {R : Type} (E : StratLedger R) (Δ : Stratum R) : StratLedger R :=
  E ++ [Δ]

/-- Every prior stratum keeps its position. -/
theorem appendStratum_prefix {R : Type} (E : StratLedger R) (Δ : Stratum R) :
    E <+: appendStratum E Δ :=
  ⟨[Δ], rfl⟩

/-- **The entire stratum lands after every prior event**: it is the last stratum,
    and it sits at index `E.length`, past every index of `E`. -/
theorem appendStratum_last {R : Type} (E : StratLedger R) (Δ : Stratum R) :
    (appendStratum E Δ).getLast? = some Δ ∧
    (appendStratum E Δ)[E.length]? = some Δ ∧
    (appendStratum E Δ).length = E.length + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact List.getLast?_concat
  · exact List.getElem?_concat_length
  · simp [appendStratum]

/-- The ledger's markers, in order. -/
def markers {R : Type} (E : StratLedger R) : List TickMarker := E.map Stratum.marker

/-- **Appending a stratum appends exactly its one marker.** -/
theorem markers_appendStratum {R : Type} (E : StratLedger R) (Δ : Stratum R) :
    markers (appendStratum E Δ) = markers E ++ [Δ.marker] := by
  simp [markers, appendStratum]

/-- The flat keyed records of a stratified ledger, strata in order. -/
def flatRecords {R : Type} (E : StratLedger R) : List (QuestionId × R) :=
  E.flatMap Stratum.records

/-- **The bridge to `Advance.append`.** Forgetting the markers, stratified append
    is exactly the flat append `Advance.lean` already performs: the flat ledger
    is the forgetful image of the stratified one. -/
theorem flatRecords_appendStratum {R : Type} (E : StratLedger R) (Δ : Stratum R) :
    flatRecords (appendStratum E Δ) = Advance.append (flatRecords E) Δ.records := by
  simp [flatRecords, appendStratum, Advance.append]

/-- **The carrier's ledger is stratified by `E` and stays so across one tick.**
    If `X.ledger` is the flat image of `E`, then the advanced carrier's ledger,
    built with `Δ := ΔE.records`, is the flat image of `E ⁀ ΔE`. -/
theorem advanceCarrier_ledger_stratified {h : ℕ} {R : Type} (X : TickCarrier R h)
    (hlaw : Lawful X) (select : List (Core × Bool) → List QuestionId) (stratum : ℕ)
    (prov : Provenance) (E : StratLedger R) (ΔE : Stratum R)
    (hsel) (hfresh) (hX : X.ledger = flatRecords E) :
    (advanceCarrier X hlaw select stratum prov ΔE.records hsel hfresh).ledger =
      flatRecords (appendStratum E ΔE) := by
  rw [flatRecords_appendStratum, ← hX]
  rfl

/-! ## Storage order within a stratum has no mathematical effect -/

/-- Two strata that differ at most in the storage order of their records. -/
def Stratum.Reordered {R : Type} (Δ Δ' : Stratum R) : Prop :=
  Δ.marker = Δ'.marker ∧ Δ.records.Perm Δ'.records

/-- **What a stratum says, with storage order forgotten**: its marker and the
    multiset of its keyed records. -/
def Stratum.content {R : Type} (Δ : Stratum R) : TickMarker × Multiset (QuestionId × R) :=
  (Δ.marker, (Δ.records : Multiset (QuestionId × R)))

/-- **Reordering is exactly what `content` cannot see**: two strata have equal
    content if and only if one is a storage reordering of the other. -/
theorem Stratum.content_eq_iff {R : Type} (Δ Δ' : Stratum R) :
    Δ.content = Δ'.content ↔ Δ.Reordered Δ' := by
  simp only [Stratum.content, Prod.mk.injEq, Multiset.coe_eq_coe, Stratum.Reordered]

/-- **Definition 11.2, "its internal storage order has no mathematical effect".**
    Every reading of a stratum that factors through its marker and its multiset
    of keyed records returns the same value on any reordering. -/
theorem Stratum.reading_reorder {R α : Type} (f : TickMarker × Multiset (QuestionId × R) → α)
    {Δ Δ' : Stratum R} (h : Δ.Reordered Δ') : f Δ.content = f Δ'.content := by
  rw [(Stratum.content_eq_iff Δ Δ').mpr h]

/-- The records a stratum keys to one occurrence. -/
def Stratum.keyed {R : Type} (Δ : Stratum R) (i : QuestionId) : List R :=
  (Δ.records.filter (fun p => decide (p.1 = i))).map Prod.snd

/-- **Keyed lookup is storage-order independent**: reordering the stratum
    reorders, and only reorders, what it keys to each occurrence. -/
theorem Stratum.keyed_reorder {R : Type} {Δ Δ' : Stratum R} (h : Δ.Reordered Δ')
    (i : QuestionId) : (Δ.keyed i).Perm (Δ'.keyed i) :=
  (h.2.filter _).map _

/-- Reordering keeps membership of every keyed record. -/
theorem Stratum.mem_records_reorder {R : Type} {Δ Δ' : Stratum R} (h : Δ.Reordered Δ')
    (p : QuestionId × R) : p ∈ Δ.records ↔ p ∈ Δ'.records :=
  h.2.mem_iff

/-- Two ledgers that differ at most in storage order within each stratum. -/
def LedgerReordered {R : Type} (E E' : StratLedger R) : Prop :=
  List.Forall₂ Stratum.Reordered E E'

/-- **Temporal append respects reordering.** Reordering a ledger's strata and the
    appended stratum gives a reordering of the appended ledger. -/
theorem appendStratum_reorder {R : Type} {E E' : StratLedger R} {Δ Δ' : Stratum R}
    (hE : LedgerReordered E E') (hΔ : Δ.Reordered Δ') :
    LedgerReordered (appendStratum E Δ) (appendStratum E' Δ') := by
  unfold LedgerReordered appendStratum
  exact List.rel_append hE (List.Forall₂.cons hΔ List.Forall₂.nil)

/-- **Reordering within strata never moves a marker**: the temporal sequence of
    ticks is unchanged. -/
theorem markers_reorder {R : Type} {E E' : StratLedger R} (h : LedgerReordered E E') :
    markers E = markers E' := by
  induction h with
  | nil => rfl
  | cons hΔ _ ih =>
      simp only [markers, List.map_cons, List.cons.injEq] at ih ⊢
      exact ⟨hΔ.1, ih⟩

/-- **Reordering within strata only reorders the flat ledger.** -/
theorem flatRecords_reorder {R : Type} {E E' : StratLedger R} (h : LedgerReordered E E') :
    (flatRecords E).Perm (flatRecords E') := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons hΔ _ ih =>
      simp only [flatRecords, List.flatMap_cons] at ih ⊢
      exact List.Perm.append hΔ.2 ih

#print axioms keyedCompatible_of_disjoint
#print axioms mem_keyedUnion_of
#print axioms mem_keyedUnion_iff
#print axioms TickMarker.tgt
#print axioms appendStratum
#print axioms appendStratum_prefix
#print axioms appendStratum_last
#print axioms markers_appendStratum
#print axioms flatRecords_appendStratum
#print axioms advanceCarrier_ledger_stratified
#print axioms Stratum.content
#print axioms Stratum.content_eq_iff
#print axioms Stratum.reading_reorder
#print axioms Stratum.keyed
#print axioms Stratum.keyed_reorder
#print axioms Stratum.mem_records_reorder
#print axioms appendStratum_reorder
#print axioms markers_reorder
#print axioms flatRecords_reorder

end G2_09
end Gaps
end RatioSpace
