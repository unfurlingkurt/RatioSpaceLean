/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S11.Perspective
/-!
  Elements I §12 — Substrate, numerical encoding, and continuum reading.

  Definitions 12.1 and 12.2. Def 12.3 is `Correspondence.lean`; Defs 12.4 and
  12.5 are `Continuum.lean`.

  **The book's chain, and what it is asking for.** Def 12.1 boxes

      substrate history → closure → relative reception → projection → coordinate

  and adds one sentence: *"These arrows are maps, not synonyms."* Formalising
  that sentence means making the layers types rather than headings and the
  arrows maps, then saying at each arrow whether it is injective and whether
  it composes with the one before. An arrow
  that were injective everywhere would be a redundant layer.

  **The box does not compose at closure → reception.**
  Arrows 1, 3 and 4 are maps on their layers, and arrows 2 → 3 → 4 compose:
  that composite is `reading`. Arrow 2 is not a map *from the closure layer*.
  It reads the complete encounter record of Def 7.4, which is built from the two
  observers (the substrate side of the encounter), and the closure records are
  two of its seven components. `closure_pair_does_not_determine_the_record`
  exhibits two observers with one closure record and two encounter records
  against the same presented state, and `record_not_a_function_of_the_closures`
  states the consequence: no map on closure pairs returns the encounter record.
  So `reading` starts at the substrate, and arrow 1 is read off the same
  observer beside the path, not on it. The box gives the order in which the
  layers are read, not a chain in which each layer is computed from the one
  before alone; this is ledger item E1-42 (`CROSSWALK.md`).

  **All four arrows are many-to-one at the declared instances** (arrow 2's
  reception at `obsWord`, arrow 3's projection at `reduction`). The closure
  pair does not determine the whole encounter record, and it does not pin
  down the *matrix* either. **`ClosureState` holds only the residue** Def 8.4
  declares: Def 8.4's own sentence, *"the closure component of a state is
  the residue of its matrix,"* names an output narrower than its input.
  `ofWord_not_inj` is the witness that residue equality does not pin down the
  matrix, and `four_records` (`Winding.lean`) is the witness that arrow 1
  itself is many-to-one, not merely the record built on top of it.

  What is many-to-one at arrow 2 is therefore both the **layer boundary**
  (the closure residue under-determines the encounter record, so arrow 2
  cannot start from the closure layer at all: `record_not_a_function_of_the_closures`)
  and the **mask** (Def
  11.1 makes a reception declare which components it reads; a reception with
  anything less than `Mask.full` is constant along the components outside its
  declaration; `reception_is_constant_along_what_the_mask_excludes`).

  **Arrow 4's fiber is the proportional class.** Arrow 4
  is Def 11.4's `ν`, which is Def 1.7's, on its own codomain `ℚ≥0 ∪ {∞}`
  (`Pres.ProjValue`). Two presentations read the same coordinate exactly when
  they are proportionally equivalent (`coordinate_fiber_is_the_class`), so the
  arrow is many-to-one on `Pres` (`2:4` and `1:2`) and one-to-one on primitive
  presentations. Its fiber is the one arrow 3's `reduction` already collapses:
  after a reducing projection, arrow 4 identifies nothing further. The two
  orientation anchors `1:0` and `0:1` are separated (`∞` and `0`).
  `Pres.realize`, which sends `1:0` to `0`, merges the two anchors; that merge
  is not a fiber of the book's `ν`.

  **On the vocabulary here, which is deliberate.** No arrow here is said to
  "lose" anything. Nothing in this framework is ever removed:
  `2:4` is still a `Pres` and is still distinct from `1:2` by `decide`, and every
  field of every record is still a field. What is true is that some of these maps
  are **many-to-one**, and what a reader holding only the output cannot do is
  vary along the fiber. The fibers here have exact integer coordinates and can be
  named, which is why the theorem names below say `many_to_one` and `fiber`
  rather than `loses`. An absence cannot be asked a question and an
  address can.
-/

namespace RatioSpace
namespace Layer

/-! ## The four arrows, as maps; arrow 2 reads the observers, not the closure layer -/

/-- **Arrow 1**, substrate history → closure, on Def 6.2's complete state. -/
def closureOfState (S : SubstrateState) : ClosureState := S.closure

/-- **Arrow 1** again, on the observer of Def 7.1, which is the side of the
    substrate that enters an encounter. The same map on the retained word. -/
def closureOfObserver (O : Observer) : ClosureState := O.closure

/-- **Arrow 2**, closure → relative reception. Two stages the book writes as one
    arrow: the encounter record of Def 7.4 is formed, then Def 11.1's reception
    reads it. It takes the two observers, not their closure records: the
    encounter record is built from the substrate side of the encounter, and
    `record_not_a_function_of_the_closures` shows it could not be built from
    the closures alone. So this arrow does not compose after arrow 1. -/
def receive {Y : Type} (R : Reception Y) (O P : Observer) : Y :=
  R.read (EncounterRecord.of O P)

/-- **Arrow 3**, relative reception → projection. Def 11.2, nothing assumed. -/
def project {Y : Type} (proj : Projection Y Pres) (y : Y) : Pres := proj.readout y

/-- **Arrow 4**, projection → coordinate reading. Def 11.4's `ν`, which is Def
    1.7's, on the book's codomain `ℚ≥0 ∪ {∞}`: the same map as `coordinate`
    (`Perspective.lean`). -/
def coordinateOf (A : Pres) : Pres.ProjValue := Pres.nu A

/-- **Definition 12.1 — the layer order, read as arrows 2 → 3 → 4.**

    Arrows 2, 3 and 4 run end to end from the substrate side of the encounter
    (the two observers) to the coordinate. Arrow 1 is not on this path: the
    reception reads the whole encounter record, which is not a function of the
    closure records (`record_not_a_function_of_the_closures`), so the book's
    box is the order of the layers, not a four-fold composite. The receiving
    space `Y` is a parameter because Def 11.1 leaves it to the observer; the
    projection is required to land in `Pres` so that arrow 4 has something to
    read. -/
def reading {Y : Type} (R : Reception Y) (proj : Projection Y Pres)
    (O P : Observer) : Pres.ProjValue :=
  coordinateOf (project proj (receive R O P))

/-! ## Arrow 1 is many-to-one, and its fiber has two named directions -/

/-- **The archive is a direction arrow 1 does not vary along.** Two substrate
    states with the same origin and the same retained word, differing in `H_τ`,
    have the same closure record, because the closure record is a function of the
    word alone (Def 8.4).

    `H_τ` is a **field** of both states and is fully present in each. What is
    true is that a reader holding only the closure record cannot tell these two
    apart, and the archive is the coordinate along which it cannot vary. -/
theorem closure_many_to_one_in_the_archive :
    ∃ S T : SubstrateState, S ≠ T ∧ closureOfState S = closureOfState T :=
  ⟨⟨Frame.empty, [], [], []⟩, ⟨Frame.empty, [], [], [[true]]⟩, by decide, rfl⟩

/-- **Arrow 1 varies along the declared origin.** Unlike the archive, the
    origin is one of Def 6.2's four stored fields arrow 1 does vary along,
    since `κ_τ = c(M_τ)` is read against the declared start the way Def 8.4
    says. -/
theorem closure_varies_with_the_declared_origin :
    ∃ S T : SubstrateState, S.origin ≠ T.origin ∧ closureOfState S ≠ closureOfState T :=
  ⟨⟨Frame.empty, [], [], []⟩, ⟨Frame.stepR Frame.empty, [], [], []⟩, by decide, by decide⟩

/-! ## Arrow 2 is many-to-one at the declared instance, and it does not start from the closure layer

  The closure record does not recode the word without collision, and the
  whole encounter is not determined by the closure pair. `closureOfObserver`
  and `EncounterRecord.of` both read the observer's declared start, and with
  the start-aware matrix at every site two observers' closure records can
  agree by cancellation between start and word; Prop 7.1 names why. -/

/-- **The closure record does not determine the word.** Def 8.4's own text,
    *"the closure component of a state is the residue of its matrix"*, names
    an output narrower than the matrix that feeds it, and `ClosureState` holds
    only that output, so `ClosureState.ofWord` is many-to-one, as
    `four_records` witnesses: **not** injective. Same witness pair as
    `quotientClosure_strictly_coarser`, which proves this fact and is not
    re-derived here. -/
theorem ofWord_not_inj :
    ClosureState.ofWord [false, true] = ClosureState.ofWord [true, false] ∧
    ([false, true] : Word) ≠ [true, false] :=
  ⟨by decide +kernel, by decide⟩

/- The closure pair does not pin down the accumulated matrix: a `ClosureState`
   equality is a residue equality alone, and `ofWord_not_inj` above is the
   witness that residue equality does not pin down the matrix. Arrow 2's
   fiber is therefore not narrower than Arrow 1's. -/

/-- **Arrow 2's fiber, named and witnessed.** `O₁` walks `[true, false]` from
    `∅`; `O₂` walks `[false]` from the frame one `R`-step out. Their matrices
    agree (`Frame.G_toWord`/`G_append`), which forces their residues to agree
    too. Their retained words, and
    so their full encounter records, do not. -/
theorem closure_pair_does_not_determine_the_record :
    ∃ O₁ O₂ P : Observer,
      closureOfObserver O₁ = closureOfObserver O₂ ∧
      EncounterRecord.of O₁ P ≠ EncounterRecord.of O₂ P := by
  refine ⟨⟨Frame.empty, [true, false], 1⟩, ⟨Frame.stepR Frame.empty, [false], 1⟩,
    ⟨Frame.empty, [], 1⟩, ?_, ?_⟩
  · change ClosureState.of Frame.empty [true, false]
      = ClosureState.of (Frame.stepR Frame.empty) [false]
    decide
  · intro h
    have := congrArg EncounterRecord.observerWord h
    simp [EncounterRecord.of] at this

/-- **Arrow 2 is not a map from the closure layer.** No function
    of the two closure records returns the encounter record Def 11.1's
    reception reads. This is why `reading` starts at the observers and not at
    `closureOfObserver`: the book's box cannot be run as five layers and four
    arrows composed end to end, only as arrows 2 → 3 → 4 after the substrate. -/
theorem record_not_a_function_of_the_closures :
    ¬ ∃ f : ClosureState → ClosureState → EncounterRecord,
        ∀ O P : Observer,
          f (closureOfObserver O) (closureOfObserver P) = EncounterRecord.of O P := by
  rintro ⟨f, hf⟩
  obtain ⟨O₁, O₂, P, hc, hne⟩ := closure_pair_does_not_determine_the_record
  exact hne (by rw [← hf O₁ P, ← hf O₂ P, hc])

/-- **The mask fiber, alongside the layer's own fiber.** `obsWord`
    declares it reads the observer's word and nothing else, and Def 11.1's
    `honest` field makes that declaration binding. It is therefore **constant
    along the presented word**: two distinct encounter records, one reading.
    Both records are still present and still distinct. -/
theorem reception_is_constant_along_what_the_mask_excludes :
    receive obsWord.reception ⟨Frame.empty, [], 1⟩ ⟨Frame.empty, [], 1⟩
      = receive obsWord.reception ⟨Frame.empty, [], 1⟩ ⟨Frame.empty, [false], 1⟩
    ∧ EncounterRecord.of ⟨Frame.empty, [], 1⟩ ⟨Frame.empty, [], 1⟩
      ≠ EncounterRecord.of ⟨Frame.empty, [], 1⟩ ⟨Frame.empty, [false], 1⟩ := by
  refine ⟨rfl, ?_⟩
  intro h
  have := congrArg EncounterRecord.presentedWord h
  simp [EncounterRecord.of] at this

/-! ## Arrow 3 is many-to-one at the declared instance, and its fiber coordinate is `gcd` -/

/-- **`gcd(p,q)` is the coordinate along which arrow 3 does not vary.** Def
    11.3's reduction sends `2:4` and `1:2` to one reduced relation; the fiber
    over `[1:2]` is `{1:2, 2:4, 3:6, …}`, indexed by `ℕ⁺`, and `gcd` *is* that
    index. Every member of the fiber is a `Pres` and remains `decide`-ably
    distinct from every other.

    Restated here as a fact about the third arrow rather than about the map,
    which is what §12.1 is for. -/
theorem projection_many_to_one_with_gcd_as_fiber_coordinate :
    project reduction Pres.twoFour = project reduction Pres.oneTwo
    ∧ Pres.twoFour ≠ Pres.oneTwo := by
  refine ⟨?_, by decide⟩
  change Pres.reduce Pres.twoFour = Pres.reduce Pres.oneTwo
  decide

/-! ## Arrow 4 is many-to-one exactly along proportional equivalence -/

/-- The improper presentation, `1:0`. Def 1.2 admits it: only `0:0` is excluded. -/
def oneZero : Pres := ⟨1, 0, by decide⟩

/-- Its opposite, `0:1`. -/
def zeroOne : Pres := ⟨0, 1, by decide⟩

/-- **Arrow 4's fiber is the class `[p:q]`.** Def 1.7's bracket: `ν` reads the
    class, nothing finer and nothing coarser. -/
theorem coordinate_fiber_is_the_class {A B : Pres} :
    coordinateOf A = coordinateOf B ↔ A ~ B :=
  Pres.nu_eq_iff_prop

/-- **Arrow 4 is many-to-one on `Pres`.** `2:4` and `1:2` are distinct
    presentations with one coordinate. -/
theorem coordinate_many_to_one :
    coordinateOf Pres.twoFour = coordinateOf Pres.oneTwo
    ∧ Pres.twoFour ≠ Pres.oneTwo :=
  ⟨Pres.nu_of_prop (by decide), by decide⟩

/-- **On primitive presentations arrow 4 is one-to-one.** Every class has one
    primitive member, so the fiber of arrow 4 holds no two primitives. -/
theorem coordinate_injective_on_primitive {A B : Pres}
    (hA : Pres.Primitive A) (hB : Pres.Primitive B)
    (h : coordinateOf A = coordinateOf B) : A = B :=
  Pres.nu_injective_on_primitive hA hB h

/-- **After a reducing projection, arrow 4 identifies nothing further.** Arrow 3
    at `reduction` lands on primitive presentations, and on those arrow 4 is
    one-to-one: the composite's fiber is arrow 3's. -/
theorem coordinate_after_reduction_injective {A B : Pres}
    (h : coordinateOf (project reduction A) = coordinateOf (project reduction B)) :
    project reduction A = project reduction B :=
  coordinate_injective_on_primitive (Pres.reduce_primitive A) (Pres.reduce_primitive B) h

/-- **The two improper endpoints are separated.** `1:0` reads as the boundary
    value (the book's `∞`) and `0:1` as `0`. Both are primitive, and arrow 4
    tells them apart. -/
theorem coordinate_separates_the_improper_endpoints :
    coordinateOf oneZero ≠ coordinateOf zeroOne
    ∧ coordinateOf oneZero = Pres.ProjValue.atBoundary
    ∧ Pres.Primitive oneZero ∧ Pres.Primitive zeroOne := by
  refine ⟨fun h => ?_, by decide, by decide, by decide⟩
  exact absurd (coordinate_fiber_is_the_class.mp h) (by decide)

/-! ## The composite of arrows 2 → 3 → 4 -/

/-- **`reading` identifies, and is not a synonym.** Two encounters that differ
    in what was met read the same coordinate under a perspective that declared
    it does not look there. Both encounters remain, and remain distinct.

    Nothing in this needs arrow 4 to have a non-trivial fiber or arrow 2 to have
    only trivial ones; `reading` is the composite of three maps (arrows 2, 3
    and 4, from the observers), and one non-trivial fiber anywhere survives to
    the end. Arrow 1 is not in this composite: the box does not compose at
    closure → reception (`record_not_a_function_of_the_closures`). What the
    boxed line is, then, is an order of layers each read by a map, rather than
    a list of names for one thing. -/
theorem the_chain_identifies :
    reading obsWord.reception ⟨fun w => Frame.mid (Frame.walk Frame.empty w)⟩
        ⟨Frame.empty, [], 1⟩ ⟨Frame.empty, [], 1⟩
      = reading obsWord.reception ⟨fun w => Frame.mid (Frame.walk Frame.empty w)⟩
        ⟨Frame.empty, [], 1⟩ ⟨Frame.empty, [false], 1⟩ := rfl

/-! ## Definition 12.2 — Numerical encoding

  **`E_O : 𝔖 → 𝓕_O`, and nothing more.** Def 12.2's second display is the
  discrete-time field equation `φ_{t+1} = φ_t + α(Δφ − γ|∇φ|²) + β tanh(φ)
  e^{−|∇φ|}`, which needs `Real`, `tanh` and `exp`, all three excluded by the
  standing constraints — and the book itself classifies it as a *"time-stepped
  projected field update,"* projection-layer content rather than substrate. It
  is **not formalised here.**

  What Def 12.2 states about the encoding itself, before that equation, is only
  that it is a map from the complete substrate state to a computable
  field-representation space the observer has declared. That is the whole
  obligation, and `Encoding` carries exactly it: no honesty proof, no
  correctness condition, because Def 12.2 states none — unlike `Reception`
  (Def 11.1), which the book charges with declaring what it reads. `F` is a
  type parameter rather than a fixed space, the same role `Y` plays in
  `Reception` and `Projection`, because Def 12.2's own subscript on `𝓕_O` says
  the target is the observer's declaration. -/

/-- **Definition 12.2.** A numerical encoding for an observer: a map from the
    complete substrate state to a computable field-representation space the
    observer has declared. -/
structure Encoding (F : Type) where
  map : SubstrateState → F

/-- The reading an encoding produces, spelled out because Def 12.2's own
    notation names it separately: `φ_t^{(E)} = E_O(S_τ)`. -/
def Encoding.reading {F : Type} (E : Encoding F) (S : SubstrateState) : F :=
  E.map S

/-- **Arrow 1 of Def 12.1 is itself a numerical encoding in Def 12.2's sense**,
    with `F := ClosureState`. Def 12.1 named it a layer boundary; Def 12.2
    names the same map an encoding once a receiving field type is declared for
    it. Nothing new is proved — `closureOfState` already exists — but the two
    definitions do not lay two obligations on this map: Def 12.1's first arrow
    and Def 12.2's encoding at `F := ClosureState` are one map, and this, with
    `closureEncoding_reading_eq_arrow1` (`rfl`), is the witness that they
    coincide rather than merely resemble each other. -/
def closureEncoding : Encoding ClosureState := ⟨closureOfState⟩

/-- And it runs: the reading matches Arrow 1 exactly, by `rfl`, so nothing is
    lost going from "arrow" to "encoding." -/
theorem closureEncoding_reading_eq_arrow1 (S : SubstrateState) :
    closureEncoding.reading S = closureOfState S := rfl

end Layer
end RatioSpace
