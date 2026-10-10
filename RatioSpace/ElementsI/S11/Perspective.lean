/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S06.State
/-!
  Elements I §11 — Closure, reception, and projection.

  Definitions 11.1 through 11.6. Six definitions and, on the face of it, no
  theorems: §11 declares maps rather than proving things about them. Two of its
  sentences are load-bearing anyway and are the reason this file is not just
  six structures.

  **Def 11.1 says a reception's formula "must state which parts of the encounter
  it reads and which it does not."** A `read : EncounterRecord → Y` field alone
  cannot state that, so `Reception` carries a `Mask` and a proof that the map is
  blind outside it. The obligation is typed, in the same style as
  `ConstantReading` in §6: a reception that reads an undeclared field is not a
  reception here, it is unconstructible.

  **Def 11.6 says "a single perspective need not be sufficient. Its failure of
  injectivity is the precise sense in which one reception cannot see all
  sides."** That is a separation asserted and, in the manuscript, left
  unexhibited — the same shape as corrections 2 and 16. It is witnessed here
  three times over one encounter record: a single perspective that is
  insufficient, a second that is insufficient in the complementary way, and
  the pair of them that is sufficient, all for one declared equivalence. With
  two distinct observers, one per encounter as the book's map takes them, the
  same shape is `Gaps/G1_21.lean`: one projection at two observers, each
  insufficient, jointly sufficient (gap G1-21).

  **The ℝ boundary, recorded rather than crossed.** Def 11.4 names two maps.
  `ν : [p:q] ↦ p/q ∈ ℚ≥0 ∪ {∞}` is Definition 1.7's `Pres.nu`, into
  `ProjValue`. It is not `Pres.realize`, which sends `1:0` and `0:1` to the
  same rational (`Pres.nu_separates_the_anchors`; gap G1-19).
  `ι : ℚ ↪ ℝ` cannot be written under the standing constraints and is not
  written. Nothing in §11 needs it: the section's actual claim about 11.4 is
  that neither map restores what was discarded, and that is a statement about
  `ν` alone, proved below on `2:4` and `1:2`.
-/

namespace RatioSpace

/-! ## Definition 11.1 — Reception -/

/-- Which components of the encounter record a reception declares it reads.
    Seven flags, one per field of `EncounterRecord`. -/
structure Mask where
  observerWord : Bool
  presentedWord : Bool
  relative : Bool
  observerClosure : Bool
  presentedClosure : Bool
  observerHistory : Bool
  presentedHistory : Bool
deriving DecidableEq

namespace Mask

/-- Two records agree on everything the mask declares. -/
def Agree (m : Mask) (E F : EncounterRecord) : Prop :=
  (m.observerWord = true → E.observerWord = F.observerWord) ∧
  (m.presentedWord = true → E.presentedWord = F.presentedWord) ∧
  (m.relative = true → E.relative = F.relative) ∧
  (m.observerClosure = true → E.observerClosure = F.observerClosure) ∧
  (m.presentedClosure = true → E.presentedClosure = F.presentedClosure) ∧
  (m.observerHistory = true → E.observerHistory = F.observerHistory) ∧
  (m.presentedHistory = true → E.presentedHistory = F.presentedHistory)

theorem agree_refl (m : Mask) (E : EncounterRecord) : m.Agree E E := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro _ <;> rfl

/-- Reads nothing. -/
def blank : Mask := ⟨false, false, false, false, false, false, false⟩

/-- Reads everything, which is what an unrestricted `read` would silently be. -/
def full : Mask := ⟨true, true, true, true, true, true, true⟩

def onlyObserverWord : Mask := { blank with observerWord := true }
def onlyPresentedWord : Mask := { blank with presentedWord := true }
def onlyRelative : Mask := { blank with relative := true }

end Mask

/-- **Definition 11.1, one member.** An exact map from the complete encounter
    record to a receiving space, together with the declaration the book
    requires and the proof that the declaration is honest. The observer
    conditioning, `𝓡_O` with `Y_O`, is the family `ObsReception` below; this
    structure is the reception at one observer.

    `honest` is the whole content. Without it `mask` is documentation; with it,
    the map provably cannot depend on anything it did not declare. -/
structure Reception (Y : Type) where
  mask : Mask
  read : EncounterRecord → Y
  honest : ∀ E F : EncounterRecord, mask.Agree E F → read E = read F

/-- **Definition 11.1, the index.** The book's `𝓡_O : 𝖤_{O,P} → Y_O` is
    conditioned on the observer. A bare `Reception` reads only the seven
    fields of `EncounterRecord`, and `Observer.eta` is not among them, so no
    bare reception can depend on the observer's declared capacity (gap G1-20,
    `Gaps.G1_20.g120_plain_reception_blind_to_capacity`). Everything else
    about `O` that Definition 7.4's record holds is already there: `w_O`, the
    closure `κ_O` (read against the declared start, which it does not store),
    and `Q_{O,P}`. The book's record has no start component either. `H_O` is
    not: `Observer` is Definition 7.1's tuple, which has no `H_O`, and
    `receive` reads `EncounterRecord.of`, which declares `H_O := [w_O]`, so the
    history slot reaches reception only as the word again (audit E1-B4;
    `EncounterRecord.history_not_read_from_the_observer`, `State.lean`).

    So the family is indexed by the capacity and nothing else: E1-39's
    reading B, "depends on it through the index `O` of `𝓡_O`", with `η_O` the
    only thing that passes through the index. Indexing by the whole observer
    would let a member declaring a blank mask read `w_O` through the index,
    which breaks the declaration obligation for the composite map. Here the
    composite depends only on the declared fields and `η_O`
    (`ObsReception.receive_honest`). A family that picks the same member at
    every capacity is reading A. -/
structure ObsReception (Y : ℕ → Type) where
  at_ : (eta : ℕ) → Reception (Y eta)

namespace ObsReception

/-- `𝓡_O` applied to `𝖤_{O,P}`: observer `O` receiving presented state `P`,
    into `Y_O = Y O.eta`. -/
def receive {Y : ℕ → Type} (R : ObsReception Y) (O P : Observer) : Y O.eta :=
  (R.at_ O.eta).read (EncounterRecord.of O P)

/-- **The declaration obligation for the composite.** Two encounters whose
    observers have one capacity, and whose records agree on what that
    capacity's member declares, receive the same. -/
theorem receive_honest {Y : ℕ → Type} (R : ObsReception Y) (O O' P P' : Observer)
    (he : O.eta = O'.eta)
    (h : (R.at_ O.eta).mask.Agree (EncounterRecord.of O P) (EncounterRecord.of O' P')) :
    he ▸ R.receive O P = R.receive O' P' := by
  unfold receive
  obtain ⟨s, w, e⟩ := O
  obtain ⟨s', w', e'⟩ := O'
  simp only at he
  subst he
  exact (R.at_ e).honest _ _ h

/-- Reading A: one reception at every capacity, depending on the observer
    only through the record. -/
def const {Y : Type} (R : Reception Y) : ObsReception (fun _ => Y) := ⟨fun _ => R⟩

theorem const_receive {Y : Type} (R : Reception Y) (O P : Observer) :
    (const R).receive O P = R.read (EncounterRecord.of O P) := rfl

end ObsReception

/-- A reception declaring nothing is a constant, and this is the sharp end of
    Def 11.1: under a blank declaration `honest` forces blindness outright. -/
theorem Reception.blank_is_constant {Y : Type} (R : Reception Y)
    (h : R.mask = Mask.blank) (E F : EncounterRecord) : R.read E = R.read F := by
  refine R.honest E F ?_
  rw [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hc <;> exact absurd hc (by decide)

/-! ## Definition 11.2 — Projection -/

/-- **Definition 11.2.** A declared readout map. Nothing is assumed: not
    linearity, not idempotence, not invertibility, not continuity. The type is
    a bare function, which is precisely the book's point that "projection" here
    does not mean the linear-algebra word. -/
structure Projection (Y Z : Type) where
  readout : Y → Z

namespace Projection

/-- **The observational equivalence every projection defines**, `x ≡ y` iff the
    readouts agree. Stated as a relation with its three properties proved, and
    deliberately **not** registered as a `Setoid`: the standing constraint is
    structural equality with no quotient, and a quotient here would destroy the
    distinctions the projection is being used to measure the loss of. -/
def Equiv {Y Z : Type} (P : Projection Y Z) (x y : Y) : Prop := P.readout x = P.readout y

theorem equiv_refl {Y Z : Type} (P : Projection Y Z) (x : Y) : P.Equiv x x := rfl

theorem equiv_symm {Y Z : Type} (P : Projection Y Z) {x y : Y} (h : P.Equiv x y) :
    P.Equiv y x := h.symm

theorem equiv_trans {Y Z : Type} (P : Projection Y Z) {x y z : Y}
    (h : P.Equiv x y) (k : P.Equiv y z) : P.Equiv x z := h.trans k

end Projection

/-! ## Definition 11.3 — Reduction as the first simple projection -/

/-- **Definition 11.3.** `ρ : p:q ↦ [p:q]`. The simplest projection there is. -/
def reduction : Projection Pres Pres := ⟨Pres.reduce⟩

/-- It identifies proportional presentations and discards the common
    multiplicity, with the book's own pair in hand: `2:4` and `1:2` are
    distinct presentations and one reduced relation. -/
theorem reduction_identifies_proportional :
    reduction.Equiv Pres.twoFour Pres.oneTwo ∧ Pres.twoFour ≠ Pres.oneTwo := by
  refine ⟨?_, by decide⟩
  change Pres.reduce Pres.twoFour = Pres.reduce Pres.oneTwo
  decide

/-! ## Definition 11.4 — Coordinate realization -/

/-- **Definition 11.4.** `ν : [p:q] ↦ p/q ∈ ℚ≥0 ∪ {∞}`, "the exact rational
    realization from Definition 1.7". So it is `Pres.nu`, into `ProjValue`, and
    not `Pres.realize`: `realize` reads `1:0` as `0`, the same rational as
    `0:1`, and Definition 1.7's `ν` keeps them apart
    (`Pres.nu_separates_the_anchors`). Gap G1-19 repointed this from
    `realize` (`Gaps/G1_19.lean`).

    `ι : ℚ ↪ ℝ` is **not** written. It cannot be, under the standing
    constraints, and §11 does not need it: the claim the section actually makes
    about 11.4 is that neither map restores presentation or history, and that
    is a fact about `ν`. -/
def coordinate : Projection Pres Pres.ProjValue := ⟨Pres.nu⟩

/-- **"Neither ν nor ι restores the presentation and history information
    discarded before it."** The `ν` half, as a statement about the projection
    `coordinate` in Def 11.2's sense: `1:2` and `2:4` are distinct
    presentations that `coordinate` reads the same. -/
theorem coordinate_is_applied_after_the_loss :
    coordinate.Equiv Pres.oneTwo Pres.twoFour ∧ Pres.oneTwo ≠ Pres.twoFour :=
  ⟨Pres.nu_of_prop Pres.oneTwo_prop_twoFour, Pres.oneTwo_ne_twoFour⟩

/-! ## Definition 11.5 — Perspective -/

/-- **Definition 11.5.** A perspective is the composite `Π_O ∘ ℛ_O`: a map from
    a relative encounter to an observer-accessible reading. Kept as a pair
    rather than collapsed to one function, because the two halves discard
    different things and §12's layer order distinguishes them. -/
structure Perspective (Y Z : Type) where
  reception : Reception Y
  projection : Projection Y Z

/-- The reading a perspective produces. -/
def Perspective.apply {Y Z : Type} (P : Perspective Y Z) (E : EncounterRecord) : Z :=
  P.projection.readout (P.reception.read E)

/-! ## Definition 11.6 — Joint relational reconstruction -/

/-- One observer with its perspective: the pair `(O_i, 𝒫_{O_i})` of
    Definition 11.6. The perspective is the one at this observer, so a bare
    `Reception` is right here: it is the member of the observer-indexed family
    at `O_i` (`Viewpoint.ofFamily`). Receiving and reading spaces are per
    observer, `Y_{O_i}` and `Z_{O_i}`. -/
structure Viewpoint where
  observer : Observer
  Y : Type
  Z : Type
  persp : Perspective Y Z

/-- `𝒫_{O}(P)`: the viewpoint's perspective applied to its own encounter
    `𝖤_{O,P}` with the presented state `P`. -/
def Viewpoint.read (V : Viewpoint) (P : Observer) : V.Z :=
  V.persp.apply (EncounterRecord.of V.observer P)

/-- The viewpoint at `O` taken from an observer-indexed reception
    (Definition 11.1, `ObsReception`) and a projection per capacity: the
    member at `O.eta` composed with the projection at `O.eta`. -/
def Viewpoint.ofFamily {Y Z : ℕ → Type} (R : ObsReception Y)
    (proj : (eta : ℕ) → Projection (Y eta) (Z eta)) (O : Observer) : Viewpoint :=
  ⟨O, Y O.eta, Z O.eta, ⟨R.at_ O.eta, proj O.eta⟩⟩

theorem Viewpoint.ofFamily_read {Y Z : ℕ → Type} (R : ObsReception Y)
    (proj : (eta : ℕ) → Projection (Y eta) (Z eta)) (O P : Observer) :
    (Viewpoint.ofFamily R proj O).read P = (proj O.eta).readout (R.receive O P) := rfl

/-- **Definition 11.6.** Given observers `O_1, …, O_n` with their
    perspectives, the joint perspective map
    `𝒥(P) = (𝒫_{O_1}(P), …, 𝒫_{O_n}(P))`, each perspective reading its own
    encounter `𝖤_{O_i,P}` with the one presented state `P`. A tuple indexed by
    `Fin n`, since the reading spaces differ by observer. -/
def joint {n : ℕ} (Vs : Fin n → Viewpoint) (P : Observer) : (i : Fin n) → (Vs i).Z :=
  fun i => (Vs i).read P

/-- **An equivalence relation on a class.** `C` is reflexive, symmetric and
    transitive on the members of `K`, and nothing is asked of it outside `K`.
    This is `≡_𝒞` of Definition 11.6: the book's relation is declared for the
    class, and Def 15.2's "target's declared equivalence" is carried to
    presented states only on the encoded class (`Sufficiency.lean`,
    `declaredEquiv`), where outside it the relation is vacuous and not
    transitive (audit finding E1-B8). -/
structure EquivOn {α : Type} (K : α → Prop) (C : α → α → Prop) : Prop where
  refl : ∀ a, K a → C a a
  symm : ∀ a b, K a → K b → C a b → C b a
  trans : ∀ a b c, K a → K b → K c → C a b → C b c → C a c

/-- An equivalence relation is one on every class. -/
theorem EquivOn.of_equivalence {α : Type} {C : α → α → Prop} (hC : Equivalence C)
    (K : α → Prop) : EquivOn K C :=
  ⟨fun a _ => hC.refl a, fun _ _ _ _ h => hC.symm h,
    fun _ _ _ _ _ _ h₁ h₂ => hC.trans h₁ h₂⟩

/-- **Reconstructive sufficiency on a declared class.** `K` is the class
    `𝒞` of presented states and `C` its declared equivalence `≡_𝒞`:
    `𝒥(P) = 𝒥(P') ⇒ P ≡_𝒞 P'` for `P, P'` in the class. Both are parameters,
    because the book's point is that sufficiency is relative to what was
    declared.

    The book says "the exact equivalence relation declared for the domain",
    so the first conjunct asks that `C` be one on the class (`EquivOn`).
    Before audit finding E1-B8 (2026-09-28) any relation was accepted, and an
    irreflexive `C` made the definition's content a different claim. -/
def ReconstructivelySufficient {n : ℕ} (Vs : Fin n → Viewpoint)
    (K : Observer → Prop) (C : Observer → Observer → Prop) : Prop :=
  EquivOn K C ∧ ∀ P P' : Observer, K P → K P' → joint Vs P = joint Vs P' → C P P'

/-- **The audit's counterexample is gone.** An irreflexive relation (here the
    empty one, `fun _ _ => False`) is no declared equivalence on an inhabited
    class, so no family is reconstructively sufficient up to it (audit finding
    E1-B8). -/
theorem not_reconstructivelySufficient_empty {n : ℕ} (Vs : Fin n → Viewpoint)
    {K : Observer → Prop} {P : Observer} (hP : K P) :
    ¬ ReconstructivelySufficient Vs K (fun _ _ => False) :=
  fun h => h.1.refl P hP

/-! ### The one-record form (gap G1-21)

  Before G1-21, `joint` mapped every perspective over one `EncounterRecord`,
  and sufficiency quantified over pairs of records. That is Definition 11.6's
  map only when the observers coincide: several perspectives reading one
  encounter. Kept, renamed, because its witnesses below (two readings of one
  encounter, neither enough alone) still say something true about that case,
  and `Encoding.lean` reads `obsWord`. -/

/-- Several perspectives over one encounter record. -/
def jointOnRecord {Y Z : Type} (Ps : List (Perspective Y Z)) (E : EncounterRecord) : List Z :=
  Ps.map (fun P => P.apply E)

/-- Injectivity of `jointOnRecord` up to an equivalence relation on records
    (the equivalence required since audit finding E1-B8, as for
    `ReconstructivelySufficient`). -/
def SufficientOnRecord {Y Z : Type} (Ps : List (Perspective Y Z))
    (C : EncounterRecord → EncounterRecord → Prop) : Prop :=
  Equivalence C ∧
    ∀ E F : EncounterRecord, jointOnRecord Ps E = jointOnRecord Ps F → C E F

/-! ### The witnesses Def 11.6's last paragraph needs -/

/-- Reads the observer's word and nothing else. -/
def obsWord : Perspective Word Word where
  reception :=
    { mask := Mask.onlyObserverWord
      read := EncounterRecord.observerWord
      honest := by intro E F h; exact h.1 rfl }
  projection := ⟨id⟩

/-- Reads the presented word and nothing else. -/
def presWord : Perspective Word Word where
  reception :=
    { mask := Mask.onlyPresentedWord
      read := EncounterRecord.presentedWord
      honest := by intro E F h; exact h.2.1 rfl }
  projection := ⟨id⟩

/-- The declared equivalence for the witnesses: both words agree. -/
def bothWords (E F : EncounterRecord) : Prop :=
  E.observerWord = F.observerWord ∧ E.presentedWord = F.presentedWord

/-- **Two perspectives over one record are enough for this class.** -/
theorem pair_is_sufficient : SufficientOnRecord [obsWord, presWord] bothWords := by
  refine ⟨⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
    fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩⟩, ?_⟩
  intro E F h
  simp only [jointOnRecord, Perspective.apply, obsWord, presWord, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at h
  exact ⟨h.1, h.2⟩

/-- **And neither one alone is.** The observer half cannot see the presented
    word: two records agreeing on the observer, differing on what was met. -/
theorem obsWord_alone_insufficient : ¬ SufficientOnRecord [obsWord] bothWords := by
  intro hsuf
  have h := hsuf.2 (EncounterRecord.of ⟨Frame.empty, [], 1⟩ ⟨Frame.empty, [], 1⟩)
      (EncounterRecord.of ⟨Frame.empty, [], 1⟩ ⟨Frame.empty, [false], 1⟩)
      (by simp [jointOnRecord, Perspective.apply, obsWord, EncounterRecord.of])
  simp [bothWords, EncounterRecord.of] at h

/-- The complementary failure, so the pair result is not carried by one half. -/
theorem presWord_alone_insufficient : ¬ SufficientOnRecord [presWord] bothWords := by
  intro hsuf
  have h := hsuf.2 (EncounterRecord.of ⟨Frame.empty, [], 1⟩ ⟨Frame.empty, [], 1⟩)
      (EncounterRecord.of ⟨Frame.empty, [false], 1⟩ ⟨Frame.empty, [], 1⟩)
      (by simp [jointOnRecord, Perspective.apply, presWord, EncounterRecord.of])
  simp [bothWords, EncounterRecord.of] at h

end RatioSpace
