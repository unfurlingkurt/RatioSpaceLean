/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S02.Frame
import RatioSpace.ElementsI.S10.Crystal
import RatioSpace.ElementsI.S11.Perspective
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
/-!
  Elements I §12 — Definitions 12.4 and 12.5, the last two items in §12.

  **Def 12.4's own instruction, taken literally.** *"The determinant-one
  contact is substrate data. The scalar width is its coordinate
  realization."* Two objects, not one: the integer statement first, division-
  free, straight off `Frame.contact`; the rational statement second, because
  it is a coordinate reading and Def 1.7 is where `ℚ` is allowed to appear.

  **Def 12.5's own instruction.** *"The threshold belongs to the receiving
  layer, not to the substrate contact relation."* So `CellResolution O` is
  built from the observer's reception (Def 11.1) and nothing here derives a
  resolution predicate from the substrate; it
  carries the reception and a proved tie between the predicate and
  distinguishability of the two boundaries in that reception (the section
  header of Def 12.5 below).

  **Def 12.5 is over the update's cells, not one frame.** The book
  reaches the regime when `Res_O(F_n) = 0` "for the distinct cells relevant to
  the update". `ContinuumRegimeOn Res cells` is that quantifier over a declared
  list of cells; `ContinuumRegime Res F`, the predicate at one frame, is the
  one-cell case (`continuumRegimeOn_singleton_iff`). The book does not say
  which cells are relevant. `trajectoryCells U n S` is the declaration made
  here: the cells visited by `n` steps of the partial update `U` from `S`
  (Def 12.3's `SubstrateState → SubstrateState ⊕ Outcome`), stopping at the
  first failure; `updateCells` is one step. A claim may declare another list
  and pass it to `ContinuumRegimeOn` directly. "Distinct" does not change the
  regime: it depends only on which cells are in the list
  (`continuumRegimeOn_congr`).
-/

namespace RatioSpace
namespace Layer

/-! ## Definition 12.4 — Exact Farey cell width

  `δ(F) = p₊/q₊ − p₋/q₋ = 1/(q₋q₊)`, for `p₊q₋ − p₋q₊ = 1`. -/

/-- **The integer form.** The reciprocal of the cell width, straight from the
    two denominators, with no division anywhere. This is what `Frame.contact`
    hands over directly: `p₊q₋ − p₋q₊ = 1` is `Frame.det_eq_one`, and the
    width's reciprocal is just the denominator product that determinant sits
    beside. Total on every `Frame`, including the boundary frame where one
    denominator is `0` — the product is `0` there too, and nothing below
    claims that case has a rational width. -/
def cellWidthRecip (F : Frame) : ℕ := F.plus.q * F.minus.q

/-- **The rational form, conditional on both sides being finite.** Needs
    `Pres.realize_eq_div`, which is stated in Mathlib's division and carries
    `Classical.choice` — `realize` itself does not, `realize_eq_div` does, and
    this theorem inherits it through that bridge alone. The two positivity
    hypotheses are not bookkeeping: without them a boundary is `1:0`, which
    Def 1.7's `ν` reads as `∞`, and the width has no value there
    (`cellWidth_defined_iff`, `cellWidth_undefined_one_step_R`). -/
theorem cellWidth_eq (F : Frame) (hp : 0 < F.plus.q) (hm : 0 < F.minus.q) :
    Pres.realize F.plus - Pres.realize F.minus = 1 / (cellWidthRecip F : ℚ) := by
  have hcontactQ : (F.plus.p : ℚ) * F.minus.q = F.plus.q * F.minus.p + 1 := by
    exact_mod_cast F.contact
  have hpq : (F.plus.q : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hmq : (F.minus.q : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Pres.realize_eq_div, Pres.realize_eq_div, cellWidthRecip]
  push_cast
  field_simp
  linear_combination hcontactQ

/-- **The width has a value exactly when both boundaries read finite.** Under
    Def 1.7's `ν` (codomain `ℚ≥0 ∪ {∞}`), both boundary coordinates are finite
    rationals if and only if both denominators are positive, which are
    `cellWidth_eq`'s hypotheses. The integer `cellWidthRecip` is total. -/
theorem cellWidth_defined_iff (F : Frame) :
    (∃ a b, Pres.nu F.plus = Pres.ProjValue.finite a
        ∧ Pres.nu F.minus = Pres.ProjValue.finite b)
      ↔ 0 < F.plus.q ∧ 0 < F.minus.q := by
  constructor
  · rintro ⟨a, b, ha, hb⟩
    refine ⟨Nat.pos_of_ne_zero fun h => ?_, Nat.pos_of_ne_zero fun h => ?_⟩
    · have := (Pres.nu_atBoundary_iff F.plus).mpr h
      rw [ha] at this; exact Pres.ProjValue.noConfusion this
    · have := (Pres.nu_atBoundary_iff F.minus).mpr h
      rw [hb] at this; exact Pres.ProjValue.noConfusion this
  · rintro ⟨hp, hm⟩
    exact ⟨_, _, Pres.nu_eq_finite_of_q_ne_zero (Nat.pos_iff_ne_zero.mp hp),
      Pres.nu_eq_finite_of_q_ne_zero (Nat.pos_iff_ne_zero.mp hm)⟩

/-- **The hypotheses are load-bearing: one step onto the all-`R` ray the width
    is undefined.** `Frame.stepR Frame.empty` keeps `F.plus = 1:0` and has
    `F.minus = 1:1`; contact holds, `cellWidthRecip` is `0 · 1 = 0`, and the
    upper boundary reads `∞` under `ν`, so there is no rational width.
    Every further `R` step keeps `F.plus = 1:0`.

    Read through `Pres.realize`, which sends `1:0` to `0`, the formula would be
    false here (`0 − 1 ≠ 1/0` under Lean's division by zero). Under the book's
    `ν` the width is not wrong at this frame, it has no value: Elements I,
    Definition 12.4, the frames with boundary `1:0` carry the integer only. -/
theorem cellWidth_undefined_one_step_R :
    Pres.nu (Frame.stepR Frame.empty).plus = Pres.ProjValue.atBoundary
    ∧ (Frame.stepR Frame.empty).minus.q = 1
    ∧ cellWidthRecip (Frame.stepR Frame.empty) = 0
    ∧ ¬ ∃ a b, Pres.nu (Frame.stepR Frame.empty).plus = Pres.ProjValue.finite a
        ∧ Pres.nu (Frame.stepR Frame.empty).minus = Pres.ProjValue.finite b := by
  refine ⟨(Pres.nu_atBoundary_iff _).mpr rfl, rfl, rfl, fun h => ?_⟩
  have := (cellWidth_defined_iff _).mp h
  exact absurd this.1 (by decide)

/-! ## Definition 12.5 — Observer-relative continuum regime

  **Tied to the observer and to reception.** The
  book: *"A cell-resolution predicate for observer `O` is an exact map
  `Res_O(F) ∈ {0,1}`, where (1) means that the two frame boundaries remain
  distinguishable in reception and (0) means that they do not."*
  `CellResolution` is indexed by the
  observer `O` and carries Def 11.1's observer-conditioned reception
  `𝓡_O` (`ObsReception`), a declared presentation of a boundary as a
  presented state, the predicate, and the tie: `resolves F = true` exactly
  when `𝓡_O` receives the two boundaries of `F` differently. So `Res_O` is
  determined by the reception and the declared boundary presentation
  (`CellResolution.resolves_eq`), and a declared
  threshold is a way of computing it, not a second source of it: the book's
  *"a projected implementation may realize this predicate through a declared
  threshold"*.

  **What is declared, because the book does not say it.** How a boundary
  `C ∈ Pres` enters an encounter as a presented state (Def 7.2). The field
  `present : Pres → Observer` is that declaration; `boundaryObserver` below is
  one (the boundary's two integers written into the presented word).

  **A consequence.** Distinguishability of two boundaries is a statement about
  each boundary's reception, so a threshold on the cell as a whole need not be
  one. The width threshold `q₋q₊ ≤ 1` (Def 12.4's integer form) is realized by
  no map on boundaries at all (`no_boundary_reading_realizes_width_one`); the
  threshold that is realized is on the boundaries' own denominators, read
  against the observer's declared capacity `η_O` (Def 7.1), which is the index
  of `𝓡_O` (`capacityResolution`).
-/

/-- **Definition 12.5.** A cell-resolution predicate for observer `O`: an
    exact, computable map from a frame to `Bool`, tied to `O`'s reception.
    `Y`, `reception` and `present` are the receiving layer's declarations;
    `resolves` is the predicate; `tie` is the book's sentence, (1) exactly
    when the two frame boundaries are distinguishable in reception. `decEq`:
    the map is exact, so whether two received values agree is decided. -/
structure CellResolution (O : Observer) where
  Y : ℕ → Type
  decEq : ∀ e, DecidableEq (Y e)
  reception : ObsReception Y
  present : Pres → Observer
  resolves : Frame → Bool
  tie : ∀ F : Frame, resolves F = true ↔
    reception.receive O (present F.minus) ≠ reception.receive O (present F.plus)

namespace CellResolution

variable {O : Observer}

/-- The predicate built from a reception with decidable equality: the one
    realization every `CellResolution` agrees with (`resolves_eq`). -/
def ofReception (O : Observer) {Y : ℕ → Type} [∀ e, DecidableEq (Y e)]
    (R : ObsReception Y) (present : Pres → Observer) : CellResolution O where
  Y := Y
  decEq := inferInstance
  reception := R
  present := present
  resolves F := decide (R.receive O (present F.minus) ≠ R.receive O (present F.plus))
  tie F := by simp

/-- **Reading (0).** `Res_O(F) = 0` exactly when the reception receives the
    two boundaries of `F` the same. -/
theorem resolves_false_iff (Res : CellResolution O) (F : Frame) :
    Res.resolves F = false ↔
      Res.reception.receive O (Res.present F.minus)
        = Res.reception.receive O (Res.present F.plus) := by
  have := Res.decEq O.eta
  rw [← Bool.not_eq_true, Res.tie, Decidable.not_not]

/-- **The predicate is determined by the reception and the boundary
    presentation.** Two cell-resolution
    predicates for `O` with the same reception and the same boundary
    presentation agree on every frame: a threshold that realizes it has no
    freedom left. -/
theorem resolves_eq (Res Res' : CellResolution O) (hY : Res.Y = Res'.Y)
    (hR : HEq Res.reception Res'.reception) (hP : Res.present = Res'.present) :
    Res.resolves = Res'.resolves := by
  obtain ⟨Y, d, R, P, r, t⟩ := Res
  obtain ⟨Y', d', R', P', r', t'⟩ := Res'
  simp only at hY hR hP
  subst hY hP
  cases hR
  funext F
  apply Bool.eq_iff_iff.mpr
  rw [t, t']

end CellResolution

/-- The predicate unresolved at one cell: `Res_O(F) = 0` at a single frame.
    The book's regime is this over the distinct cells relevant to the update,
    which is `ContinuumRegimeOn` below; this is its one-cell case
    (`continuumRegimeOn_singleton_iff`). -/
def ContinuumRegime {O : Observer} (Res : CellResolution O) (F : Frame) : Prop :=
  Res.resolves F = false

instance {O : Observer} (Res : CellResolution O) (F : Frame) :
    Decidable (ContinuumRegime Res F) := by
  unfold ContinuumRegime; infer_instance

/-- **The one-cell regime is indistinguishability in reception.** -/
theorem continuumRegime_iff_same_reception {O : Observer} (Res : CellResolution O)
    (F : Frame) : ContinuumRegime Res F ↔
      Res.reception.receive O (Res.present F.minus)
        = Res.reception.receive O (Res.present F.plus) :=
  Res.resolves_false_iff F

/-! ### A declared boundary presentation -/

/-- A boundary `p:q` written into a presented word: `p` copies of `R`, then
    `q` copies of `L`. A declaration, not the book's. -/
def boundaryWord (C : Pres) : Word := List.replicate C.p true ++ List.replicate C.q false

theorem boundaryWord_count_true (C : Pres) : (boundaryWord C).count true = C.p := by
  simp [boundaryWord, List.count_replicate]

theorem boundaryWord_count_false (C : Pres) : (boundaryWord C).count false = C.q := by
  simp [boundaryWord, List.count_replicate]

theorem boundaryWord_injective : Function.Injective boundaryWord := by
  intro A B h
  have hp := boundaryWord_count_true A
  have hq := boundaryWord_count_false A
  rw [h, boundaryWord_count_true] at hp
  rw [h, boundaryWord_count_false] at hq
  obtain ⟨p, q, _⟩ := A
  obtain ⟨p', q', _⟩ := B
  simp only at hp hq
  subst hp hq
  rfl

/-- The boundary as a presented state: its word is `boundaryWord`, from the
    declared initial frame `F_∅`, capacity `0`. -/
def boundaryObserver (C : Pres) : Observer := ⟨Frame.empty, boundaryWord C, 0⟩

/-- No frame has equal boundaries: contact at a repeated presentation would
    force `0 = 1`. -/
theorem frame_minus_ne_plus (F : Frame) : F.minus ≠ F.plus := by
  intro he
  have := F.det_eq_one
  rw [Frame.det, Delta, he, mul_comm (F.plus.q : ℤ), sub_self] at this
  exact absurd this (by decide)

/-! ### Two receptions at the extremes -/

/-- The reception that declares nothing and receives `()`. -/
def blankReception : ObsReception (fun _ => Unit) :=
  ObsReception.const ⟨Mask.blank, fun _ => (), fun _ _ _ => rfl⟩

/-- The reception that declares the presented word and receives it. -/
def wordReception : ObsReception (fun _ => Word) :=
  ObsReception.const ⟨Mask.onlyPresentedWord, fun E => E.presentedWord,
    fun _ _ h => h.2.1 rfl⟩

/-- A blind receiver: its reception declares nothing, so it receives every
    boundary the same and resolves no cell. -/
def blindReceiver (O : Observer) : CellResolution O :=
  CellResolution.ofReception O blankReception boundaryObserver

/-- A sighted receiver: its reception reads the presented word, which carries
    the boundary exactly, so it resolves every cell. -/
def sightedReceiver (O : Observer) : CellResolution O :=
  CellResolution.ofReception O wordReception boundaryObserver

/-- **The witness that matters.** `blindReceiver O` leaves the boundary
    frame unresolved (the one-cell case, so the regime holds on
    `[Frame.empty]`) while `1:0` and `0:1` remain two distinct, decidable
    presentations — the substrate has not become continuous, and this
    receiver's exact cells have become unresolved by its own reception.
    That is the book's *"the substrate has not become continuous, its exact
    cells have become unresolved"* with an object in hand, and it is available
    for any frame (`frame_minus_ne_plus`). -/
theorem blindReceiver_unresolved_at_distinct_boundaries (O : Observer) :
    ContinuumRegime (blindReceiver O) Frame.empty
    ∧ Frame.empty.plus ≠ Frame.empty.minus := by
  exact ⟨(continuumRegime_iff_same_reception _ _).mpr rfl, by decide⟩

/-- **And it is not vacuous the other way.** The sighted receiver never
    leaves a cell unresolved, so it reaches the regime on no non-empty list of
    cells (`sightedReceiver_no_updateContinuumRegime`) — the predicate
    genuinely varies with the reception. -/
theorem sightedReceiver_never_continuum (O : Observer) (F : Frame) :
    ¬ ContinuumRegime (sightedReceiver O) F := by
  rw [continuumRegime_iff_same_reception]
  intro h
  exact frame_minus_ne_plus F (boundaryWord_injective h)

/-! ### A threshold at the observer's capacity -/

/-- The member at capacity `e`: receive the presented word when it carries at
    most `e` copies of `L` (the boundary's denominator, `boundaryWord_count_false`),
    and nothing otherwise. Reads only the presented word. -/
def capacityReception : ObsReception (fun _ => Option Word) :=
  ⟨fun e => ⟨Mask.onlyPresentedWord,
    fun E => if E.presentedWord.count false ≤ e then some E.presentedWord else none,
    fun E F h => by rw [h.2.1 rfl]⟩⟩

/-- **A declared threshold that realizes Def 12.5.** Observer `O` resolves a
    cell when one of its boundaries has denominator at most `η_O`. The
    threshold is the observer's declared capacity (Def 7.1), the index of
    `𝓡_O` (Def 11.1), so it belongs to the receiving layer, as Def 12.5 says.
    `tie` is proved, not assumed. -/
def capacityResolution (O : Observer) : CellResolution O where
  Y := fun _ => Option Word
  decEq := fun _ => inferInstance
  reception := capacityReception
  present := boundaryObserver
  resolves F := decide (F.minus.q ≤ O.eta ∨ F.plus.q ≤ O.eta)
  tie F := by
    have hne : boundaryWord F.minus ≠ boundaryWord F.plus :=
      fun h => frame_minus_ne_plus F (boundaryWord_injective h)
    simp only [ObsReception.receive, capacityReception, EncounterRecord.of,
      boundaryObserver, boundaryWord_count_false, decide_eq_true_iff]
    by_cases hm : F.minus.q ≤ O.eta <;> by_cases hp : F.plus.q ≤ O.eta <;>
      simp [hm, hp, hne]

/-- `O`'s capacity reception leaves a cell unresolved exactly when both of its
    boundaries have denominator above `η_O`. -/
theorem capacityResolution_regime_iff (O : Observer) (F : Frame) :
    ContinuumRegime (capacityResolution O) F ↔ O.eta < F.minus.q ∧ O.eta < F.plus.q := by
  unfold ContinuumRegime capacityResolution
  simp only [decide_eq_false_iff_not, not_or, Nat.not_le]

/-- **Once unresolved, unresolved below.** If `O`'s capacity reception leaves a
    cell unresolved, it leaves both of its children unresolved: the kept
    boundary is unchanged and the mediant's denominator is the sum. -/
theorem capacityResolution_select (O : Observer) (F : Frame) (b : Bool)
    (h : ContinuumRegime (capacityResolution O) F) :
    ContinuumRegime (capacityResolution O) (Frame.select F b) := by
  rw [capacityResolution_regime_iff] at h ⊢
  obtain ⟨hm, hp⟩ := h
  cases b
  · exact ⟨hm, Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _)⟩
  · exact ⟨Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _), hp⟩

/-- **The width threshold is not a boundary reading.** No map on boundaries, however
    declared, is distinguishing exactly on the cells with `q₋q₊ ≤ 1`: the cells
    `L` (`1:1 | 0:1`, width product `1`), `LL` (`1:2 | 0:1`, `2`) and `LR`
    (`1:1 | 1:2`, `2`) would need `f(0:1) = f(1:2) = f(1:1) ≠ f(0:1)`. So a
    cell-width threshold is a predicate on cells, and Def 12.5's predicate,
    which is distinguishability of the two boundaries in reception, cannot be
    it at `N = 1`. -/
theorem no_boundary_reading_realizes_width_one {Z : Type} (f : Pres → Z) :
    ¬ ∀ F : Frame, (f F.minus ≠ f F.plus ↔ cellWidthRecip F ≤ 1) := by
  intro h
  have hL := (h (Frame.walk Frame.empty [false])).mpr (by decide)
  have hLL : ¬ (f (Frame.walk Frame.empty [false, false]).minus
      ≠ f (Frame.walk Frame.empty [false, false]).plus) :=
    fun hn => absurd ((h _).mp hn) (by decide)
  have hLR : ¬ (f (Frame.walk Frame.empty [false, true]).minus
      ≠ f (Frame.walk Frame.empty [false, true]).plus) :=
    fun hn => absurd ((h _).mp hn) (by decide)
  have e1 : (Frame.walk Frame.empty [false]).minus
      = (Frame.walk Frame.empty [false, false]).minus := by decide
  have e2 : (Frame.walk Frame.empty [false, false]).plus
      = (Frame.walk Frame.empty [false, true]).minus := by decide
  have e3 : (Frame.walk Frame.empty [false, true]).plus
      = (Frame.walk Frame.empty [false]).plus := by decide
  exact hLL fun h1 => hLR fun h2 => hL (by rw [e1, h1, e2, h2, e3])

/-! ## Definition 12.5 over the update's cells -/

/-- **Definition 12.5, the regime.** `Res_O(F) = 0` for every cell in a
    declared list of cells. Which cells are relevant to the update is part of
    the claim; `trajectoryCells` below is one declaration. -/
def ContinuumRegimeOn {O : Observer} (Res : CellResolution O) (cells : List Frame) : Prop :=
  ∀ F ∈ cells, Res.resolves F = false

instance {O : Observer} (Res : CellResolution O) (cells : List Frame) :
    Decidable (ContinuumRegimeOn Res cells) := by
  unfold ContinuumRegimeOn; infer_instance

/-- The one-frame predicate is the regime over one cell. -/
theorem continuumRegimeOn_singleton_iff {O : Observer} (Res : CellResolution O) (F : Frame) :
    ContinuumRegimeOn Res [F] ↔ ContinuumRegime Res F := by
  simp [ContinuumRegimeOn, ContinuumRegime]

/-- The regime over a list is the one-frame predicate at each of its cells. -/
theorem continuumRegimeOn_iff_forall {O : Observer} (Res : CellResolution O) (cells : List Frame) :
    ContinuumRegimeOn Res cells ↔ ∀ F ∈ cells, ContinuumRegime Res F := Iff.rfl

/-- **"Distinct" does not change the regime.** Two lists with the same cells,
    in any order and with any repetition, give the same regime. -/
theorem continuumRegimeOn_congr {O : Observer} (Res : CellResolution O) {cells cells' : List Frame}
    (h : ∀ F, F ∈ cells ↔ F ∈ cells') :
    ContinuumRegimeOn Res cells ↔ ContinuumRegimeOn Res cells' := by
  simp only [ContinuumRegimeOn, h]

/-- The regime on more cells gives it on fewer. -/
theorem ContinuumRegimeOn.mono {O : Observer} {Res : CellResolution O} {cells cells' : List Frame}
    (h : ContinuumRegimeOn Res cells') (hsub : ∀ F ∈ cells, F ∈ cells') :
    ContinuumRegimeOn Res cells := fun F hF => h F (hsub F hF)

theorem continuumRegimeOn_append {O : Observer} (Res : CellResolution O) (A B : List Frame) :
    ContinuumRegimeOn Res (A ++ B) ↔ ContinuumRegimeOn Res A ∧ ContinuumRegimeOn Res B := by
  simp only [ContinuumRegimeOn, List.mem_append]
  exact ⟨fun h => ⟨fun F hF => h F (Or.inl hF), fun F hF => h F (Or.inr hF)⟩,
    fun h F hF => hF.elim (h.1 F) (h.2 F)⟩

/-- **An empty list of cells is a regime for every receiver.** Nothing to
    check. So a claim that the regime is reached must name its cells, and
    `trajectoryCells` never returns the empty list
    (`start_mem_trajectoryCells`). -/
theorem continuumRegimeOn_nil {O : Observer} (Res : CellResolution O) : ContinuumRegimeOn Res [] :=
  fun _ h => nomatch h

/-- **The cells relevant to `n` steps of a partial update.** The cell the state
    sits in (`S.frame`, Def 5.1's `F_τ`), then the cells of each state the
    update returns, for `n` steps, stopping at the first failure: where the
    update returns an `Outcome` there is no next cell. -/
def trajectoryCells (U : SubstrateState → SubstrateState ⊕ Outcome) :
    ℕ → SubstrateState → List Frame
  | 0, S => [S.frame]
  | n + 1, S => S.frame :: match U S with
    | .inl T => trajectoryCells U n T
    | .inr _ => []

/-- One step of the update: the start cell and, where the update is defined,
    the cell it moves to. -/
def updateCells (U : SubstrateState → SubstrateState ⊕ Outcome) (S : SubstrateState) :
    List Frame := trajectoryCells U 1 S

theorem updateCells_defined (U : SubstrateState → SubstrateState ⊕ Outcome)
    {S T : SubstrateState} (h : U S = .inl T) : updateCells U S = [S.frame, T.frame] := by
  simp [updateCells, trajectoryCells, h]

theorem updateCells_undefined (U : SubstrateState → SubstrateState ⊕ Outcome)
    {S : SubstrateState} {o : Outcome} (h : U S = .inr o) : updateCells U S = [S.frame] := by
  simp [updateCells, trajectoryCells, h]

theorem start_mem_trajectoryCells (U : SubstrateState → SubstrateState ⊕ Outcome)
    (n : ℕ) (S : SubstrateState) : S.frame ∈ trajectoryCells U n S := by
  cases n <;> simp [trajectoryCells]

/-- **Definition 12.5 for an update.** The observer's receiver leaves every
    cell of `n` steps of `U` from `S` unresolved. -/
def UpdateContinuumRegime {O : Observer} (Res : CellResolution O)
    (U : SubstrateState → SubstrateState ⊕ Outcome) (n : ℕ) (S : SubstrateState) : Prop :=
  ContinuumRegimeOn Res (trajectoryCells U n S)

instance {O : Observer} (Res : CellResolution O) (U : SubstrateState → SubstrateState ⊕ Outcome)
    (n : ℕ) (S : SubstrateState) : Decidable (UpdateContinuumRegime Res U n S) := by
  unfold UpdateContinuumRegime; infer_instance

/-- **The update's regime includes the start cell.** It is never reached
    while the receiver still resolves the cell the state sits in. -/
theorem UpdateContinuumRegime.start {O : Observer} {Res : CellResolution O}
    {U : SubstrateState → SubstrateState ⊕ Outcome} {n : ℕ} {S : SubstrateState}
    (h : UpdateContinuumRegime Res U n S) : ContinuumRegime Res S.frame :=
  h _ (start_mem_trajectoryCells U n S)

/-- Zero steps is the one-frame predicate at the state's own cell. -/
theorem updateContinuumRegime_zero_iff {O : Observer} (Res : CellResolution O)
    (U : SubstrateState → SubstrateState ⊕ Outcome) (S : SubstrateState) :
    UpdateContinuumRegime Res U 0 S ↔ ContinuumRegime Res S.frame := by
  simp [UpdateContinuumRegime, trajectoryCells, continuumRegimeOn_singleton_iff]

/-- A step that is defined: the regime for `n + 1` steps is the start cell
    and the regime for `n` steps from the next state. -/
theorem updateContinuumRegime_succ_defined {O : Observer} (Res : CellResolution O)
    (U : SubstrateState → SubstrateState ⊕ Outcome) (n : ℕ) {S T : SubstrateState}
    (h : U S = .inl T) :
    UpdateContinuumRegime Res U (n + 1) S ↔
      ContinuumRegime Res S.frame ∧ UpdateContinuumRegime Res U n T := by
  simp only [UpdateContinuumRegime, trajectoryCells, h]
  simp [ContinuumRegimeOn, ContinuumRegime]

/-- A step that fails: only the start cell is relevant. -/
theorem updateContinuumRegime_succ_undefined {O : Observer} (Res : CellResolution O)
    (U : SubstrateState → SubstrateState ⊕ Outcome) (n : ℕ) {S : SubstrateState}
    {o : Outcome} (h : U S = .inr o) :
    UpdateContinuumRegime Res U (n + 1) S ↔ ContinuumRegime Res S.frame := by
  simp only [UpdateContinuumRegime, trajectoryCells, h]
  simp [ContinuumRegimeOn, ContinuumRegime]

/-- The blind receiver reaches the regime over every update, every number of
    steps, from every state. -/
theorem blindReceiver_updateContinuumRegime (O : Observer)
    (U : SubstrateState → SubstrateState ⊕ Outcome) (n : ℕ) (S : SubstrateState) :
    UpdateContinuumRegime (blindReceiver O) U n S := fun F _ =>
  (continuumRegime_iff_same_reception _ F).mpr rfl

/-- The sighted receiver reaches it over none. -/
theorem sightedReceiver_no_updateContinuumRegime (O : Observer)
    (U : SubstrateState → SubstrateState ⊕ Outcome) (n : ℕ) (S : SubstrateState) :
    ¬ UpdateContinuumRegime (sightedReceiver O) U n S := fun h =>
  sightedReceiver_never_continuum O _ h.start

end Layer
end RatioSpace
