/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S01.Kernel
/-!
  **The logic spine, machine-checked.**

  Source: *RatioSpace Standard Logic Translation — Completed Proof Program and
  Closure Record v1.0* (Drive, 2026-09-08). That document closes the question of
  which logic RatioSpace needs. The answer is ordinary classical first-order
  logic: RatioSpace supplies the exact inherited construction, and classical
  logic reasons about propositions that faithfully describe it.

  The record's whole force is in a handful of exact statements, and every one of
  them is decidable or elementary. So they are checked here rather than asserted:

    * the record's eight equalities are equality under a declared read
      (`EqUnder`, with `Evalue` stated directly by cross-multiplication),
      which is why (prose, not a theorem) they coexist without
      contradiction; six of the eight reads are defined below (`Epres`,
      `Evalue`, `Eproj`, `Eword`, `Emat`, `Eend`), the other two are not
      formalised here (count corrected 2026-09-30, audit E1-A10);
    * coarsening is always licensed and is a **theorem**, not a convention
      (`eqUnder_factor`) — this is the general form of Step 2F;
    * presentation equality implies value equality (Step 2A);
    * the three refutations, each with the record's own exact witness:
      value ↛ presentation (1:2 vs 2:4), reception ↛ matrix (M vs M·A_k),
      projection ↛ presentation (Step 2B, 2D, 2E);
    * word ↔ matrix in the declared positive domain, with the qualifier
      **kept in the statement** rather than in a remark (Step 2C);
    * retained occurrence-indexed history: consecutive endpoints differ
      (`endpointAt_succ_ne`), so the indexed facts are distinct (Step 3);
    * construction is not implication, because construction is irreflexive and
      implication is reflexive (Step 4);
    * monotonicity of classical consequence (Step 6E);
    * the codon and second-difference derivations (Step 6A, 6B).

  Step 5 asks for a standard classical model of the frozen fragment. It is not
  restated as a theorem: this file *is* one. Every symbol below is interpreted in
  ordinary mathematics, and the interpretation typechecks.

  No axioms beyond `propext`/`Quot.sound`; nothing is `Classical.choice`.
-/

namespace RatioSpace
namespace Logic

open Pres Frame

/-! ## II — The declared equalities are one construction

The record lists eight equality predicates and warns that they must never be
silently substituted. They are not eight primitives. Five of the six defined
here are equality after a declared read (`Evalue` is cross-multiplication), and
the discipline is a consequence of that shape. Six of the
eight reads are defined here; the other two are not formalised in this file. -/

/-- **Equality under a declared read.** `E_read(X,Y)` iff the read agrees. -/
def EqUnder {α β : Type} (f : α → β) (x y : α) : Prop := f x = f y

theorem eqUnder_refl {α β : Type} (f : α → β) (x : α) : EqUnder f x x := rfl

theorem eqUnder_symm {α β : Type} {f : α → β} {x y : α} :
    EqUnder f x y → EqUnder f y x := Eq.symm

theorem eqUnder_trans {α β : Type} {f : α → β} {x y z : α} :
    EqUnder f x y → EqUnder f y z → EqUnder f x z := Eq.trans

/-- **Step 2F, in general form.** If the second read factors through the
    first, the first equality licenses the second. One direction only: the
    converse is not proved here. -/
theorem eqUnder_factor {α β γ : Type} (f : α → β) (h : β → γ) (x y : α) :
    EqUnder f x y → EqUnder (h ∘ f) x y := by
  intro hxy; unfold EqUnder at *; simp [hxy]

/-! ## The reads (six of the record's eight)

Presentation, value, projection, endpoint, word, matrix, closure, reception.
Five of the six defined below are `EqUnder` applied to a read the framework
already defines; `Evalue` is stated directly by cross-multiplication (Def
1.4's `~`). Closure and reception are not defined here. -/

/-- Presentation equality: the identity read. The finest of them. -/
def Epres (A B : Pres) : Prop := EqUnder id A B

/-- Value equality, stated by cross-multiplication rather than as `EqUnder`
    of a read. Def 1.4's `~` is this relation. -/
def Evalue (A B : Pres) : Prop := A.p * B.q = A.q * B.p

/-- Projection equality under the declared ratio-reduction Σ. -/
def Eproj (A B : Pres) : Prop := EqUnder Pres.reduce A B

/-- Ordered-word equality. -/
def Eword (u v : Word) : Prop := EqUnder id u v

/-- Matrix equality on the accumulated positive continuation. -/
def Emat (u v : Word) : Prop := EqUnder (fun w => Frame.matrix (Frame.walk Frame.empty w)) u v

/-- Endpoint equality: the address the walk arrives at. -/
def Eend (u v : Word) : Prop := EqUnder Frame.r u v

/-! ### Step 2A — presentation equality implies value equality -/

theorem pres_imp_value (A B : Pres) : Epres A B → Evalue A B := by
  intro h
  unfold Epres EqUnder id at h
  subst h
  unfold Evalue
  ring

/-! ### Step 2B — and the converse is refuted, by the record's own witness -/

/-- `1:2` and `2:4`. -/
def oneTwo : Pres := ⟨1, 2, by decide⟩
def twoFour : Pres := ⟨2, 4, by decide⟩

theorem value_not_imp_pres : Evalue oneTwo twoFour ∧ ¬ Epres oneTwo twoFour := by
  refine ⟨by unfold Evalue oneTwo twoFour; decide, ?_⟩
  intro h
  have : oneTwo = twoFour := h
  exact absurd this (by decide)

/-! ### Step 2E — projection equality does not imply presentation equality

The same witness serves, because reduction is exactly the declared projection. -/

theorem proj_not_imp_pres : Eproj oneTwo twoFour ∧ ¬ Epres oneTwo twoFour := by
  refine ⟨by unfold Eproj EqUnder oneTwo twoFour; decide, ?_⟩
  intro h
  have : oneTwo = twoFour := h
  exact absurd this (by decide)

/-! ### Step 2D — reception equality does not imply matrix equality

The parabolic fiber. A declared reception `D(M) = M e` cannot see a shear that
fixes `e`, so the same reception occurs over different frames. -/

/-- A 2×2 integer matrix, four components, no `Matrix` machinery needed. -/
structure Mat where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq, Repr

namespace Mat

def mul (M N : Mat) : Mat :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
   M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩

def I : Mat := ⟨1, 0, 0, 1⟩

/-- The parabolic `A_k`, the shear that fixes `e = (1,0)ᵀ`. -/
def A (k : ℤ) : Mat := ⟨1, k, 0, 1⟩

/-- The declared reception read `D(M) = M e`, `e = (1,0)ᵀ`: the first column. -/
def D (M : Mat) : ℤ × ℤ := (M.a, M.c)

end Mat

/-- `A_k` fixes `e` for every `k`. -/
theorem parabolic_fixes (k : ℤ) : Mat.D (Mat.A k) = Mat.D Mat.I := by
  unfold Mat.D Mat.A Mat.I; rfl

/-- **The fiber is exact and it is general in `M` and `k`.** Every frame has a
    whole line of frames it cannot be told apart from under this reception. -/
theorem reception_blind (M : Mat) (k : ℤ) : Mat.D (Mat.mul M (Mat.A k)) = Mat.D M := by
  unfold Mat.D Mat.mul Mat.A
  simp

/-- And the frames genuinely differ, for every nonzero `k`. -/
theorem reception_fiber_nontrivial (k : ℤ) (hk : k ≠ 0) :
    Mat.mul Mat.I (Mat.A k) ≠ Mat.I := by
  intro h
  have : k = 0 := by
    have := congrArg Mat.b h
    simpa [Mat.mul, Mat.A, Mat.I] using this
  exact hk this

/-- **Step 2D.** Reception equality does not imply matrix equality. -/
theorem reception_not_imp_matrix :
    EqUnder Mat.D (Mat.mul Mat.I (Mat.A 1)) Mat.I ∧
      Mat.mul Mat.I (Mat.A 1) ≠ Mat.I := by
  refine ⟨?_, reception_fiber_nontrivial 1 (by decide)⟩
  unfold EqUnder
  exact reception_blind Mat.I 1

/-! ### Step 2C — word ↔ matrix, with the domain qualifier kept

The record insists the equivalence is not global: it holds in the declared
positive refinement domain, where the ordered word and the accumulated
unimodular matrix are exact mutually recoverable encodings. Below, that domain
is the type: `Word` walked from the empty frame. Nothing outside it is claimed. -/

theorem word_iff_matrix (u v : Word) : Eword u v ↔ Emat u v := by
  constructor
  · intro h
    unfold Eword EqUnder id at h
    subst h
    rfl
  · intro h
    unfold Emat EqUnder Frame.matrix at h
    have pext : ∀ X Y : Pres, X.p = Y.p → X.q = Y.q → X = Y := by
      intro X Y h1 h2; cases X; cases Y; simp_all
    have hp : (Frame.walk Frame.empty u).plus = (Frame.walk Frame.empty v).plus := by
      have h1 := congrArg (fun x => x.1.1) h
      have h2 := congrArg (fun x => x.1.2) h
      simp only [Nat.cast_inj] at h1 h2
      exact pext _ _ (by exact_mod_cast h1) (by exact_mod_cast h2)
    have hm : (Frame.walk Frame.empty u).minus = (Frame.walk Frame.empty v).minus := by
      have h1 := congrArg (fun x => x.2.1) h
      have h2 := congrArg (fun x => x.2.2) h
      simp only [Nat.cast_inj] at h1 h2
      exact pext _ _ (by exact_mod_cast h1) (by exact_mod_cast h2)
    have : Frame.r u = Frame.r v := by
      unfold Frame.r Frame.addressed Frame.mid Pres.mediant
      rw [hp, hm]
    exact Kernel.addressed_injective u v this

/-- Endpoint equality is word equality here too, which is `addressed_injective`
    read as a statement about the declared reads: on this domain the endpoint
    read loses nothing. -/
theorem end_iff_word (u v : Word) : Eend u v ↔ Eword u v :=
  ⟨fun h => (Kernel.addressed_injective u v h).symm ▸ rfl,
   fun h => by unfold Eword EqUnder id at h; subst h; rfl⟩

/-! ## III — Step 3: consecutive occurrence-indexed endpoints differ

`endpoint(H_n) = x` and `endpoint(H_{n+1}) = y` with `x ≠ y` is not `P ∧ ¬P`.
The two are different atomic propositions with different occurrence arguments,
and an ordinary structure satisfies both. What is proved below is that the
endpoints at consecutive occurrences differ for every `n` (`endpointAt_succ_ne`);
the satisfiability reading is the prose around it. -/

/-- The occurrence-indexed endpoint read: `n` steps to the right. -/
def endpointAt (n : ℕ) : Pres := Frame.r (List.replicate n true)

theorem endpoints_differ_no_contradiction :
    endpointAt 0 ≠ endpointAt 1 ∧ endpointAt 1 ≠ endpointAt 2 := by
  constructor <;> decide

/-- After `n` right steps from `F_∅` the frame is `(1:0, n:1)`. -/
theorem walk_replicate_true (n : ℕ) :
    (walk empty (List.replicate n true)).plus = ⟨1, 0, by decide⟩ ∧
    (walk empty (List.replicate n true)).minus.p = n ∧
    (walk empty (List.replicate n true)).minus.q = 1 := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [List.replicate_succ', walk_append]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [select, stepR, Frame.mid, Pres.mediant, h1, h2, h3]
    omega

/-- The endpoint after `n` right steps is `(n+1):1`. -/
theorem endpointAt_p (n : ℕ) : (endpointAt n).p = n + 1 := by
  obtain ⟨h1, h2, _⟩ := walk_replicate_true n
  simp [endpointAt, Frame.r, addressed, Frame.mid, Pres.mediant, h1, h2]
  omega

/-- **Step 3.** For every `n` the endpoint at occurrence `n` and at occurrence
    `n + 1` differ, so "the endpoint is `endpointAt n`" and "the endpoint is
    `endpointAt (n+1)`" are distinct facts, each true of its own occurrence.
    (Prose, not proved here: retaining both indexed by occurrence is
    consistent.) (Restated 2026-09-30,
    audit E1-A10: this was the tautology `x = x ∧ y = y`, under the name
    `retained_history_satisfiable`.) -/
theorem endpointAt_succ_ne (n : ℕ) : endpointAt n ≠ endpointAt (n + 1) := fun h => by
  have := congrArg Pres.p h
  rw [endpointAt_p, endpointAt_p] at this
  omega

/-! ## IV — Step 4: construction is not implication

Not a verbal distinction. Implication is reflexive on any proposition: `P → P`.
Lawful construction appends a letter, so it strictly increases the record and
can never relate an occurrence to itself. One is reflexive, the other provably
is not, so they are different relations. -/

/-- Lawful one-step construction: `H_n —U→ H_{n+1}`. -/
def Constructs (u v : Word) : Prop := ∃ b : Bool, v = u ++ [b]

theorem constructs_irrefl (u : Word) : ¬ Constructs u u := by
  rintro ⟨b, hb⟩
  have h := congrArg List.length hb
  rw [List.length_append] at h
  simp only [List.length_cons, List.length_nil] at h
  omega

/-- **Step 4.** Implication is reflexive, construction is irreflexive, so the
    two are not the same relation. (Restated 2026-09-30, audit E1-A10: this
    joined `∀ P, P → P` to one instance `¬ Constructs [] []`; it now states
    both properties of the relations themselves.) -/
theorem construction_ne_implication :
    (∀ P : Prop, P → P) ∧ ∀ u : Word, ¬ Constructs u u :=
  ⟨fun _ h => h, constructs_irrefl⟩

/-- And the converse direction of Step 4: a construction step does not preserve
    the endpoint proposition, so the arrow cannot be read as material
    implication between the descriptions either. -/
theorem construction_moves_endpoint :
    Constructs [] [true] ∧ Frame.r [] ≠ Frame.r [true] :=
  ⟨⟨true, rfl⟩, by decide⟩

/-! ## V — Step 6E: monotonicity of classical consequence

Why historically true occurrence-indexed premises remain available without any
change to classical inference. -/

/-- The ledger `Γ_n`: a finite set of selected propositions. Bookkeeping only,
    and deliberately not identified with the inherited history. -/
def Entails (Γ : List Prop) (φ : Prop) : Prop := (∀ p ∈ Γ, p) → φ

theorem entails_mono (Γ Δ : List Prop) (φ : Prop)
    (hsub : ∀ p ∈ Γ, p ∈ Δ) (h : Entails Γ φ) : Entails Δ φ := by
  intro hΔ
  exact h (fun p hp => hΔ p (hsub p hp))

/-- Step 6F, the part that is proved: whatever is entailed from no premises,
    no record constructs itself. The entailment hypothesis is not used; the
    content is that `Constructs` is irreflexive. The record's wider sentence, that `Entails` and
      `Constructs`
    have no common inhabitant, is prose and is not formalised here.
    (Restated 2026-09-30, audit E1-A10: this joined `Entails [] True` to one
    instance `¬ Constructs [] []` and read the pair as the wider sentence.) -/
theorem theoremhood_constructs_nothing (φ : Prop) (_ : Entails [] φ) :
    ∀ u : Word, ¬ Constructs u u :=
  constructs_irrefl

/-! ## VI — Step 6A and 6B: the two arithmetic derivations

Both are ordinary algebra over the exact relational premises. Included because
the record includes them, and because they are the point at which the framework
says *subtract, do not invent a comparison*. -/

/-- **Step 6A — codon reconstruction.** Any two of `[a | b−a | b]` recover the
    third. -/
theorem codon_reconstruct (a b d : ℤ) (h : d = b - a) : b = a + d ∧ a = b - d := by
  subst h; constructor <;> ring

/-- **Step 6B — recursive subtraction.** The second difference is an algebraic
    consequence of the exact premises. It is not a new substrate operation. -/
theorem second_difference (x₀ x₁ x₂ d₀ d₁ e₀ : ℤ)
    (h0 : d₀ = x₁ - x₀) (h1 : d₁ = x₂ - x₁) (he : e₀ = d₁ - d₀) :
    e₀ = x₂ - 2 * x₁ + x₀ := by
  subst h0; subst h1; subst he; ring

end Logic
end RatioSpace
