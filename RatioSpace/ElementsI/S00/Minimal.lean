/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S09.Question
import RatioSpace.ElementsI.S11.Perspective
/-!
  The Minimal Relational Calculus — v0.1, §12's theorem program, stated in Lean.

  Source: Elements I, §0 (Definitions 0.1 to 0.3). The section marks §1 to §13 in
  this file number the items of the minimal calculus, not the sections of the book.
  Aim: *state the Minimal Relational Calculus in Lean, where nothing is injected.*

  **Nothing is injected here, and that is the point of the file.** Every item of
  §12 is stated over objects that already exist in this tree — `Mat2`, `Word`,
  `G`, `Observer`, `Projection` — and no new primitive, parameter, constant or
  free scale is introduced. If the minimal calculus is really the skeleton of
  Elements I, then writing it down must cost no new machinery. It does not.

  **What the tree already holds.** Five of §12's seven items are proved in
  `Walk.lean` and `Perspective.lean` under other names; they are
  cited here rather than rebuilt, which is the whole content of the claim that
  the calculus is derived language and not a second ontology. The other two
  are proved below, together with one definitional
  restatement:

    * `encounter_transport` — §3's bilateral transport law. `Walk.transport`
      is a definition; this theorem ties it to what happens when
      both endpoints continue.
    * `matrix_extend_ne` — §12's nonreturn result at the occurrence, not just at
      the word. `G_cons_ne_one` says a nonempty word is not the identity; this
      says a continued observer is not the observer it continued from.
    * `id_read_equiv_iff_eq` — definitional, not a third proof: under the
      identity read `∼_id` is equality (`Iff.rfl`). It is not §12's retention
      requirement; the merging read is `encounter_matrix_loses_history`.

  §9's Hutter specialization is deliberately not here: there is no byte read in
  this tree and adding one to state the section would inject exactly what the
  calculus forbids.
-/

namespace RatioSpace
namespace Minimal

open Word

/-! ## §1 — Primitive data

    Occurrences carry an exact presentation; the generator set is `Γ = {L, R}`
    and a continuation is a word in it. Both are `Walk.lean`'s, unchanged:
    `Word.gen false = L`, `Word.gen true = R`, `G` the ordered product. -/

/-- **§1, the typed generator set.** `Γ` is exactly two generators and they are
    the book's, not new ones. -/
theorem gamma_is_L_and_R : gen false = Mat2.L ∧ gen true = Mat2.R := ⟨gen_false, gen_true⟩

/-! ## §2 — Exact presentation, and Construction 3

    `M(ω) ∈ SL(2,ℤ)`, positive continuation acting on the right. -/

/-- **Axiom/Construction 3 — exact relational representation.** Every admitted
    relation has an exact integer representation on the contact shell. Discharged
    by `det_G`: no approximation enters, and `Mat2` is `ℤ`-valued throughout. -/
theorem construction_three_exact_representation (w : Word) : (G w).det = 1 :=
  det_G w

/-- **§2, the directed right action.** Continuation is `M ↦ M · G(u)`, which is
    `Walk.forward`. Stated so the calculus's arrow has a referent here. -/
theorem forward_is_right_multiplication (M : Mat2) (u : Word) :
    forward M (G u) = M * G u := rfl

/-! ## §4 and Construction 2 — Composition

    `ω →u ω' →v ω''` composes to `ω →uv ω''`. -/

/-- **Axiom/Construction 2 — composition.** Discharged by `G_append`. The
    intermediate occurrence stays exact; nothing about the composite forgets it,
    which is §4's remark that code-level factorization is provisional. -/
theorem construction_two_composition (u v : Word) : G (u ++ v) = G u * G v :=
  G_append u v

/-! ## §3 — The relation between two occurrences, and how it transports

    `Q(ω_a, ω_b) :≡ M(ω_a)⁻¹ M(ω_b)`. In this tree that is `encounter`,
    already at Def 7.4. The transport law is `encounter_transport`. -/

/-- **§3's relative relation.** `Q` is `encounter`, definitionally. -/
theorem Q_is_encounter (O P : Observer) :
    encounter O P = Mat2.inv2 O.matrix * P.matrix := rfl

/-- Continuing an observer by `u` multiplies its accumulated transform on the
    right by `G u`. The declared start is carried through: `M_O = M_{F_{0,O}} G(w_O)`
    (Elements I, Definition 7.1). -/
theorem matrix_extend (O : Observer) (u : Word) :
    Observer.matrix { O with word := O.word ++ u } = O.matrix * G u := by
  simp only [Observer.matrix, G_append, Mat2.mul_assoc']

/-- Every observer's accumulated transform sits on the contact shell. -/
theorem det_matrix (O : Observer) : (O.matrix).det = 1 := by
  simp only [Observer.matrix, Mat2.det_mul, Frame.det_toMat2, det_G, one_mul]

/-- **§3, the bilateral transport law.** When both endpoints continue — the
    observer by `u`, the presented by `v` — the relation between them transports
    as `Q ↦ g_a⁻¹ Q g_b`. So encounter transport is not an extra object in the
    ontology. It is the induced change of the relation, forced by the definition
    of `Q` and nothing else.

    This is Elements I, Proposition 7.2 for words, and it is the law the
    definition `Walk.transport` is named for. -/
theorem encounter_transport (O P : Observer) (u v : Word) :
    encounter { O with word := O.word ++ u } { P with word := P.word ++ v }
      = Mat2.inv2 (G u) * encounter O P * G v := by
  rw [encounter, matrix_extend, matrix_extend, Mat2.inv2_mul,
    encounter, Mat2.mul_assoc', Mat2.mul_assoc', Mat2.mul_assoc']

/-- The same statement in `Walk.transport`'s own vocabulary, so the definition
    and the law are visibly the same thing. -/
theorem encounter_transport_is_transport (O P : Observer) (u v : Word) :
    encounter { O with word := O.word ++ u } { P with word := P.word ++ v }
      = transport (G u) (G v) (encounter O P) := by
  rw [encounter_transport, transport]

/-! ## §5 — Same read, distinct occurrence

    A declared read may identify distinct occurrences without collapsing them.
    `Projection.Equiv` is that relation; it is deliberately not a `Setoid` in
    this tree, and that choice is exactly §5's. -/

/-- **§5 / the Definition of `∼_π`.** Two occurrences are indistinguishable under
    a read when their readouts agree, and nothing about that makes them equal. -/
theorem same_read_is_projection_equiv {Y Z : Type} (P : Projection Y Z) (x y : Y) :
    P.Equiv x y ↔ P.readout x = P.readout y := Iff.rfl

/-! ## §12 — Retention requirement

    *Whenever a read identifies distinct exact occurrences, the distinctions
    required for exact reopening remain recoverable from the complete retained
    construction.* Stated here: the identity read is equality (definitional),
    and some strictly coarser read merges distinct histories. -/

/-- **The identity read, definitionally.** Under the identity read `∼_id` is
    equality. This holds by `Iff.rfl`, the definition of `Projection.Equiv`
    unfolded at `id`; it is not a proof of §12's retention requirement. -/
theorem id_read_equiv_iff_eq (u v : Word) :
    (⟨id⟩ : Projection Word Word).Equiv u v ↔ u = v := Iff.rfl

/-- **A coarser read merges.** A coarser read does
    merge distinct histories — the relative encounter matrix identifies an
    observer at `R` meeting `RL` with an observer at `ε` meeting `L`, so this
    `∼_π` is weaker than identity.
    Cited from `encounter_matrix_loses_history`. -/
theorem some_read_merges_distinct_histories :
    ∃ u v : Word, u ≠ v ∧ Mat2.inv2 (G [true]) * G u = Mat2.inv2 (G []) * G v :=
  ⟨[true, false], [false], encounter_matrix_loses_history.2,
    encounter_matrix_loses_history.1⟩

/-! ## §12 — Nonreturn in the positive grammar

    *A nonempty positive continuation does not return to the exact earlier
    occurrence.* The word-level statement is `G_cons_ne_one`. The occurrence-level
    statement is `matrix_extend_ne`. -/


/-- Nonreturn at the word, in the form §12 states it. -/
theorem G_ne_one_of_ne_nil {u : Word} (h : u ≠ []) : G u ≠ 1 := by
  cases u with
  | nil => exact absurd rfl h
  | cons b w => exact G_cons_ne_one b w

/-- **Nonreturn at the occurrence.** Continuing an observer by any nonempty
    positive word lands on a different exact presentation. This is §1's "no
    temporal return is primitive" and §12's nonreturn result, said about the
    occurrence rather than about the word: a later occurrence is not the earlier
    occurrence, and the argument is cancellation on the contact shell, not an
    appeal to the ordering. -/
theorem matrix_extend_ne (O : Observer) {u : Word} (h : u ≠ []) :
    Observer.matrix { O with word := O.word ++ u } ≠ O.matrix := by
  rw [matrix_extend]
  intro heq
  apply G_ne_one_of_ne_nil h
  calc G u
      = (Mat2.inv2 O.matrix * O.matrix) * G u := by
        rw [Mat2.inv2_mul_of_det _ (det_matrix O), Mat2.one_mul']
    _ = Mat2.inv2 O.matrix * (O.matrix * G u) := by rw [Mat2.mul_assoc']
    _ = Mat2.inv2 O.matrix * O.matrix := by rw [heq]
    _ = 1 := Mat2.inv2_mul_of_det _ (det_matrix O)

/-! ## §7 — The minimal substrate statement

    *Occurrence + directed relation + composition.* Everything above is stated
    over `Observer` (occurrence with its retained provenance), `G`/`forward`
    (directed relation) and `G_append` (composition). No fourth primitive is
    used anywhere in this file, and the tree needed no addition to carry it. -/

/-- **§13, the one-line form, as far as it is a mathematical claim.** Sameness is
    sameness-under-a-read and never identity-through-change: reads merge
    (`some_read_merges_distinct_histories`), continuation never returns
    (`matrix_extend_ne`), and the identity read is equality, definitionally
    (`id_read_equiv_iff_eq`). Collected as one statement so
    the three halves are checked to be simultaneously true of the same objects. -/
theorem minimal_substrate_statement :
    (∀ u v : Word, (⟨id⟩ : Projection Word Word).Equiv u v ↔ u = v)
    ∧ (∃ u v : Word, u ≠ v ∧ Mat2.inv2 (G [true]) * G u = Mat2.inv2 (G []) * G v)
    ∧ (∀ (O : Observer) (u : Word), u ≠ [] →
        Observer.matrix { O with word := O.word ++ u } ≠ O.matrix) :=
  ⟨id_read_equiv_iff_eq, some_read_merges_distinct_histories,
    fun O _ h => matrix_extend_ne O h⟩

end Minimal
end RatioSpace
