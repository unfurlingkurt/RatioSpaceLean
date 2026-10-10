/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S06.State
/-!
  Elements I §10 — Candidate records and the seven-tick crystallization interface.

  **§10 is a contract, not a construction, and the book says so.** Def 10.2 asks
  that "a completed crystallization mechanics must supply one exact deterministic
  advance", and Def 10.9 closes with "this paper fixes that output contract.
  Proving that the actual 𝔎_𝒞 satisfies it … remains part of the Elements II
  construction."

  So the advance enters here as an **interface**: a structure whose fields are
  the obligations, never a Lean `axiom`. It is not taken on trust (nor, since
  audit E1-B11, is §8's `Closure12`, inhabited by `Closure12.congruence`). The fields are
  satisfiable and the carrier is inhabited, trivially: the identity advance
  (`Crystallization.identity`) and the advance that empties every ensemble
  (`Crystallization.clear`) both meet them, and they crystallize the same
  ensemble differently (`Crystallization.carrier_does_not_fix_the_advance`).
  What is withheld is only the Elements II advance `𝔎_𝒞`, the mechanics the book
  defers; nothing in this file assumes it (audit E1-B6 of 2026-09-26, fixed
  2026-09-29).

  The one thing the contract can be held to *here* is its output type, and that
  is what this file makes exact. Def 10.9 requires that seven ticks produce
  "either one exact survivor or an exact unresolved result". Typed correctly,
  that stops being a hope: `Outcome` has exactly three constructors, `resolve` is
  total into it, and the trichotomy is a theorem rather than a promise.
-/

namespace RatioSpace

/-! ## Definition 10.1 — Candidate record -/

/-- **Definition 10.1.** *"The candidate is therefore not merely a reduced
    fraction."* Seven components: the represented relation, its address word,
    accumulated frame, closure record, complete composition star, ordered tension
    signature, and retained history.

    Four of the seven are derived from `history`, exactly as in Def 6.2, so they
    are functions rather than fields. What is stored is the history it came by
    and the two family-relative readings, which depend on the ensemble and cannot
    be recovered from the candidate alone.

    The two readings are stored, not computed, so nothing here ties them to a
    family. The tie is `Gaps.G1_17.g117_Consistent` (Lean gap G1-17): under it,
    `star` is Def 4.4's star and `signature` Def 5.6's signature of the relation
    against the active family, and `g117_ofFamily` builds such a record from a
    history and a family. -/
structure Candidate where
  /-- the retained history, from which address, matrix and closure follow -/
  history : History
  /-- `Σ_τ(r)`, the complete composition star against the active family -/
  star : List IPres
  /-- `T_τ(r)`, the ordered tension signature -/
  signature : List ℕ
deriving DecidableEq

namespace Candidate

/-- `r`, the represented relation. -/
def relation (C : Candidate) : Pres := C.history.addressed
/-- `w_r`, the address word. -/
def word (C : Candidate) : Word := C.history.word
/-- `M_r`, the accumulated frame transform, taken relative to the history's
    declared start — Def 9.3 writes `Q_{O,r} = M_O⁻¹M_r` against `Observer.matrix`
    (D-12, likewise start-relative), and Def 10.1's `M_r` is the same kind of
    object for a candidate.

    **D-16, fixed here.** Was `C.history.matrix`, `G H.word` alone, the same
    defect pre-D-12 `Observer.matrix` had. Not fixed by changing
    `History.matrix` itself: that field turned out to be a different, correctly
    unrooted object Elements II Def 3.3 depends on (`Walk.lean`), not a defect
    to repair. `History.accumulatedMatrix` is the new, separately named
    declared-start reading, and this line now calls it. -/
def matrix (C : Candidate) : Mat2 := C.history.accumulatedMatrix
/-- `κ_r`, the closure record, read against the history's declared start.

    **D-14, fixed here.** Was `ClosureState.ofWord C.history.word`, discarding
    `C.history.start` the way pre-D-12 `Observer.matrix` did. Computed directly
    from `C.history.start`/`C.history.word`, so it never depended on
    `Candidate.matrix` above and needed no further change when D-16 closed. -/
def closure (C : Candidate) : ClosureState :=
  ClosureState.of C.history.start C.history.word

/-- **"Not merely a reduced fraction", with the witness.** Two candidates can
    carry the *same* represented relation and still be different records, because
    the relation projection is not injective on histories. This is the object
    built for Def 9.4 seen from the other side, and it is what makes Def 10.3's
    unique-record clause do work that a singleton support would not do. -/
theorem relation_does_not_determine_candidate :
    ∃ C D : Candidate, C ≠ D ∧ C.relation = D.relation :=
  ⟨⟨⟨Frame.empty, [false]⟩, [], []⟩,
   ⟨⟨Frame.walk Frame.empty [false], []⟩, [], []⟩,
   by decide, by decide⟩

end Candidate

/-! ## Definition 10.3 — Terminal survivor support -/

/-- A history-bearing candidate ensemble, `𝔛`. -/
abbrev Ensemble := List Candidate

/-- **Definition 10.3.** `supp_r(𝔛)`, the represented relation set. Deduplicated,
    because it is a *set* of relations and the book compares its cardinality. -/
def supp (X : Ensemble) : List Pres := (X.map Candidate.relation).dedup

/-- The candidate records carrying a given relation. Def 10.3's unique-record
    condition is a statement about this list, not about `supp`. Deduplicated,
    because the book's ensemble is a set: a record listed twice is one record,
    not two (audit W2 of 2026-10-01, fixed 2026-10-04). Without it the advance
    `fun X => X ++ X`, which `Crystallization.admissible` allows, would turn a
    resolving ensemble into `unresolvedMultiple`. -/
def carriers (X : Ensemble) (r : Pres) : Ensemble :=
  (X.filter fun C => decide (C.relation = r)).dedup

/-! ## Definition 10.1 — The initial candidate ensemble -/

/-- **Definition 10.1.** `Ξ_{τ,0}(r)`, the initial candidate record of `r` against
    the question's active family `𝒜_τ`: the history `r` itself, Def 4.4's star
    and Def 5.6's signature of its relation against `𝒜_τ`. This is
    `Gaps.G1_17.g117_ofFamily r Q.active` (`g117_initialRecord_eq`, by `rfl`),
    written out because that gap file imports this one. -/
def initialRecord (Q : Question) (r : History) : Candidate :=
  ⟨r, IPres.star r.addressedI Q.active.relations, Q.active.tensionSignature r.addressedI⟩

/-- **Definition 10.1.** `𝔛_{τ,0}(𝒬_τ) = {Ξ_{τ,0}(r) | r ∈ S₀(𝒬_τ)}`, the initial
    candidate ensemble, built from the question (audit E1-B5 of 2026-09-26,
    fixed 2026-09-29). Deduplicated because the book's ensemble is a set:
    `S₀` is a filter of the active family, and a history listed twice in `𝒜_τ`
    would otherwise enter as two equal records over one relation. `resolve`
    now also counts a repeated record once, because `carriers` is deduplicated
    (audit W2; witness `duplicate_record_resolves`). -/
def initialEnsemble (Q : Question) : Ensemble :=
  ((S0 Q).map (initialRecord Q)).dedup

/-- `List.subset_dedup` without `Classical.choice`: Mathlib's proof reaches it,
    this one runs on the list's decidable membership. -/
private theorem mem_dedup_of_mem {α : Type} [DecidableEq α] :
    ∀ {l : List α} {a : α}, a ∈ l → a ∈ l.dedup
  | [], _, h => by cases h
  | x :: t, a, h => by
      have ih : ∀ {b}, b ∈ t → b ∈ t.dedup := fun hb => mem_dedup_of_mem hb
      change a ∈ List.pwFilter (· ≠ ·) (x :: t)
      if hx : x ∈ t.dedup then
        have hn : ¬ ∀ b ∈ List.pwFilter (· ≠ ·) t, x ≠ b := fun hall => hall x hx rfl
        rw [List.pwFilter_cons_of_neg hn]
        rcases List.mem_cons.1 h with rfl | ht
        · exact hx
        · exact ih ht
      else
        have hp : ∀ b ∈ List.pwFilter (· ≠ ·) t, x ≠ b := fun b hb hxb => hx (hxb ▸ hb)
        rw [List.pwFilter_cons_of_pos hp]
        rcases List.mem_cons.1 h with rfl | ht
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih ht)

/-- Every initial record comes from a member of `S₀(𝒬_τ)`, and every member of
    `S₀(𝒬_τ)` enters. -/
theorem mem_initialEnsemble {Q : Question} {C : Candidate} :
    C ∈ initialEnsemble Q ↔ ∃ r ∈ S0 Q, initialRecord Q r = C := by
  rw [← List.mem_map]
  exact ⟨fun h => List.dedup_subset _ h, mem_dedup_of_mem⟩

/-- No record is listed twice. -/
theorem initialEnsemble_nodup (Q : Question) : (initialEnsemble Q).Nodup :=
  List.nodup_dedup _

/-- The initial record keeps the history it was built from, so distinct
    members of `S₀` give distinct records. -/
@[simp] theorem initialRecord_history (Q : Question) (r : History) :
    (initialRecord Q r).history = r := rfl

theorem initialRecord_injective (Q : Question) : Function.Injective (initialRecord Q) :=
  fun r s h => by simpa using congrArg Candidate.history h

/-! ## Definition 10.4 — Resolution and crystallization -/

/-- **Definition 10.4's three cases, as a type.** The book writes `resolve` as a
    partial map with an "otherwise, undefined" branch and then names the two ways
    it can fail: `|S₇| = 0` is an inconsistent or over-constrained question, and
    `|S₇| > 1` is unresolved multiplicity.

    Making the failures constructors rather than absence is what turns Def 10.9's
    output contract into something checkable. An `Option` would collapse the two
    failures into one, and the book keeps them apart on purpose. -/
inductive Outcome where
  /-- one relation, carried by exactly one record: the coherent snap -/
  | resolved (C : Candidate) : Outcome
  /-- `|S₇| = 0`: the question is inconsistent or over-constrained -/
  | empty : Outcome
  /-- `|S₇| > 1`, **or** one relation carried by more than one distinct record -/
  | unresolvedMultiple : Outcome
deriving DecidableEq

/-- **Definition 10.4.** Total into `Outcome`, and the totality is the point.

    Note the second branch: a singleton support is **not** sufficient. The
    relation must be carried by exactly one candidate record (distinct records:
    `carriers` is deduplicated, so a record listed twice counts once, as in the
    book's set; witness `duplicate_record_resolves`), which is the
    unique-record condition Def 10.3 states and Def 10.4 reads back. By
    `Candidate.relation_does_not_determine_candidate` that clause is not
    redundant, and dropping it would return one record while silently discarding
    an equally admissible one. -/
def resolve (X : Ensemble) : Outcome :=
  match supp X with
  | [] => Outcome.empty
  | [r] =>
      match carriers X r with
      | [C] => Outcome.resolved C
      | _ => Outcome.unresolvedMultiple
  | _ => Outcome.unresolvedMultiple

/-- **Definition 10.9's output contract, as a theorem.** *"Seven iterations
    produce either one exact survivor or an exact unresolved result."* Every
    ensemble resolves to exactly one of three outcomes, by construction, and
    there is no fourth possibility and no undefined case to fall into. -/
theorem resolve_total (X : Ensemble) :
    (∃ C, resolve X = Outcome.resolved C) ∨
    resolve X = Outcome.empty ∨
    resolve X = Outcome.unresolvedMultiple := by
  rcases h : resolve X with C | _ | _
  · exact Or.inl ⟨C, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- An empty ensemble is the `|S₇| = 0` case, exactly. -/
@[simp] theorem resolve_nil : resolve [] = Outcome.empty := by decide

/-- **And the unique-record clause bites.** Two candidates, one relation between
    them, is `unresolvedMultiple` and not a resolution. Without the clause this
    ensemble would resolve, because its support really is a singleton. -/
theorem two_records_one_relation_does_not_resolve :
    resolve [⟨⟨Frame.empty, [false]⟩, [], []⟩,
             ⟨⟨Frame.walk Frame.empty [false], []⟩, [], []⟩]
      = Outcome.unresolvedMultiple := by decide

/-- **A record listed twice is one record** (audit W2), at one witness `c0`.
    The ensemble is a set in the book; the list `[c0, c0]` resolves to `c0`, as
    `[c0]` does (`one_record_resolves`), and is not `unresolvedMultiple`. -/
theorem duplicate_record_resolves :
    resolve [⟨⟨Frame.empty, [false]⟩, [], []⟩, ⟨⟨Frame.empty, [false]⟩, [], []⟩]
      = Outcome.resolved ⟨⟨Frame.empty, [false]⟩, [], []⟩ := by decide

/-- One record resolves, and returns that record rather than its value. -/
theorem one_record_resolves (C : Candidate) :
    resolve [C] = Outcome.resolved C := by
  -- 2026-09-22: `simp [supp]` went through `List.dedup_cons_of_notMem`, which reaches
  -- `Classical.choice`; `rfl` computes it. The `carriers` step was already clean and is only
  -- tightened.
  have hs : supp [C] = [C.relation] := rfl
  have hc : carriers [C] C.relation = [C] := by
    simp only [carriers, decide_true, List.filter_cons_of_pos, List.filter_nil]
    rfl
  simp only [resolve, hs, hc]

/-! ## Definition 10.2 — The seven-tick interface -/

/-- **Definition 10.2, as an interface.** A completed crystallization
    mechanics supplies the one-tick advance `𝔎_𝒞`; Elements I only declares what
    it must be. **This is never a Lean `axiom`.** Not a trust carrier (nor is §8's `Closure12`,
    built as `Closure12.congruence`, E1-B11): this one is inhabited, trivially, by `identity`
      and `clear`
    below. What Elements I withholds is the Elements II advance, and the two
    fields do not pin it down (`carrier_does_not_fix_the_advance`); every
    other result here holds for all advances.

    The two fields are the whole of what Elements I asks. The advance is a
    function, so it is deterministic by typing rather than by assertion, and it
    introduces no relation absent from its input ensemble. That bound is at the
    relation level only (audit M2): no question is in the type, and a candidate's
    history and readings may be replaced, so seven ticks stay within the relations
    of the starting ensemble (`relations_do_not_grow_iterate`), not within its
    records. -/
structure Crystallization where
  /-- `𝔎_𝒞 : 𝔈 → 𝔈`, one exact deterministic temporal advance -/
  advance : Ensemble → Ensemble
  /-- every output candidate's relation is the relation of some input candidate;
      histories and readings may be replaced -/
  admissible : ∀ X : Ensemble, ∀ C ∈ advance X, ∃ D ∈ X, C.relation = D.relation

namespace Crystallization

variable (K : Crystallization)

/-- `𝔎_𝒞^n`, the advance iterated. -/
def iterate (K : Crystallization) : ℕ → Ensemble → Ensemble
  | 0, X => X
  | n + 1, X => K.advance (K.iterate n X)

/-- **The distinguished horizon.** `h_𝒬 = 7` is a *receiver declaration* in the
    book, not a derived constant, and it is written as a literal here for exactly
    that reason: nothing below proves seven is special, and nothing should. -/
def horizon : ℕ := 7

/-- **Definition 10.4, on an ensemble.** `resolve(𝔎_𝒞⁷(𝔛))`: seven ticks of the
    advance from any ensemble `𝔛`, then resolution. The book's
    `Cryst_𝒞(𝒬_τ)` is this at `𝔛 = 𝔛_{τ,0}(𝒬_τ)`, which is `crystQ` below. -/
def cryst (K : Crystallization) (X : Ensemble) : Outcome :=
  resolve (K.iterate horizon X)

/-- **Definition 10.4.** `Cryst_𝒞(𝒬_τ) = resolve(𝔎_𝒞⁷(𝔛_{τ,0}(𝒬_τ)))`, a function
    of the question: the initial ensemble is `initialEnsemble Q`, built from
    `S₀(𝒬_τ)` (audit E1-B5 of 2026-09-26, fixed 2026-09-29). -/
def crystQ (K : Crystallization) (Q : Question) : Outcome :=
  K.cryst (initialEnsemble Q)

theorem crystQ_eq (Q : Question) :
    K.crystQ Q = resolve (K.iterate horizon (initialEnsemble Q)) := rfl

/-- **Definition 10.4's `|S₇| = 0` reading, at the question.** An empty
    active cavity `S₀(𝒬_τ) = ∅` gives the empty initial ensemble; seven ticks
    of any advance keep it empty (`admissible`), and `Cryst_𝒞(𝒬_τ)` is the
    `|S₇| = 0` case. -/
theorem crystQ_of_S0_nil {Q : Question} (h : S0 Q = []) :
    K.crystQ Q = Outcome.empty := by
  have h0 : initialEnsemble Q = [] := by simp [initialEnsemble, h]
  have hk : ∀ n, K.iterate n [] = [] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change K.advance (K.iterate n []) = []
        rw [ih]
        rcases hX : K.advance [] with _ | ⟨C, _⟩
        · rfl
        · obtain ⟨D, hD, _⟩ := K.admissible [] C (by rw [hX]; exact List.mem_cons_self ..)
          simp at hD
  rw [crystQ_eq, h0, hk]
  exact resolve_nil

/-- **The identity advance.** Every ensemble is left as it is; it invents no
    candidate, so it meets `admissible`. It shows the carrier is inhabited; it
    is not offered as the Elements II advance. -/
def identity : Crystallization := ⟨fun X => X, fun _ C hC => ⟨C, hC, rfl⟩⟩

/-- **The clearing advance.** Every ensemble goes to the empty one; the empty
    ensemble has no candidate to be inadmissible, so it meets `admissible`. -/
def clear : Crystallization := ⟨fun _ => [], fun _ _ hC => nomatch hC⟩

/-- **The carrier does not fix the advance.** One ensemble, one record:
    seven identity ticks resolve it to that record, seven clearing ticks leave
    the `|S₇| = 0` case. So `Crystallization` is inhabited and does not
    determine `𝔎_𝒞`; the advance itself is what Elements II owes (audit E1-B6). -/
theorem carrier_does_not_fix_the_advance (C : Candidate) :
    identity.cryst [C] = Outcome.resolved C ∧ clear.cryst [C] = Outcome.empty :=
  ⟨one_record_resolves C, resolve_nil⟩

/-- **Definition 10.9, discharged for any advance whatsoever.** The determinism
    requirement asks that seven ticks produce one exact survivor or an exact
    unresolved result. It holds for *every* `Crystallization`, because it is a
    statement about the output type rather than about the law.

    That is worth saying plainly: **Elements I's determinism requirement is not a
    constraint on `𝔎_𝒞`.** It is satisfied by typing alone. The real obligation,
    which Def 10.9's own last sentence defers to Elements II, is that the actual
    advance reaches `resolved` for the questions the framework cares about. -/
theorem determinism_contract (X : Ensemble) :
    (∃ C, K.cryst X = Outcome.resolved C) ∨
    K.cryst X = Outcome.empty ∨
    K.cryst X = Outcome.unresolvedMultiple :=
  resolve_total _

/-- One tick never widens the represented relation set. Immediate from
    `admissible`. For any number of ticks see `relations_do_not_grow_iterate`. -/
theorem relations_do_not_grow (X : Ensemble) {C : Candidate}
    (hC : C ∈ K.advance X) : ∃ D ∈ X, C.relation = D.relation :=
  K.admissible X C hC

/-- **`n` ticks never widen the represented relation set** (audit M2). Every
    candidate of `𝔎_𝒞^n(𝔛)` carries the relation of some candidate of `𝔛`; at
    `n = horizon` this is the seven ticks. Relations only: histories and readings
    may be replaced along the way. -/
theorem relations_do_not_grow_iterate (n : ℕ) (X : Ensemble) {C : Candidate}
    (hC : C ∈ K.iterate n X) : ∃ D ∈ X, C.relation = D.relation := by
  induction n generalizing C with
  | zero => exact ⟨C, hC, rfl⟩
  | succ n ih =>
      obtain ⟨E, hE, hCE⟩ := K.admissible _ C hC
      obtain ⟨D, hD, hED⟩ := ih hE
      exact ⟨D, hD, hCE.trans hED⟩

end Crystallization

/-! ## Definitions 10.5 to 10.8 — Snap, answer, and the recursion -/

/-- **Definition 10.5 and 10.7.** The coherent snap and the answer are the same
    object: the complete survivor *record*, not `ρ(r*)`. The book insists on this
    twice, and typing it as `Candidate` rather than `Pres` is the whole content —
    an answer that were a `Pres` would have discarded the history by which it
    became the unique admissible resolution. -/
abbrev Answer := Candidate

/-- **Definition 10.6.** The forward resolution map, partial exactly where
    `resolve` is. Returning `Outcome` rather than `Option Answer` keeps the two
    failure modes apart, which Def 10.4 requires.

    It takes the ensemble the seven ticks start from. The book's `ℱ_𝒬` is
    "induced by `Cryst_𝒞`", so at a question it is read at that question's
    initial ensemble, `forwardResolution_initial` (audit E1-B5). -/
def forwardResolution (K : Crystallization) (X : Ensemble) : Outcome := K.cryst X

/-- At the question's initial ensemble the forward resolution is
    `Cryst_𝒞(𝒬_τ)`. -/
theorem forwardResolution_initial (K : Crystallization) (Q : Question) :
    forwardResolution K (initialEnsemble Q) = K.crystQ Q := rfl

/-- **Definition 10.6, the other half.** Return assimilation propagates the
    answer into the next state. Elements I declares the map and Def 10.6's own
    text says the literal state-update formula "remains part of the Elements II
    construction", so this is a field to be supplied and not a definition.

    The carrier states no update formula, because Elements I states none. An
    earlier field `records` fixed the history update to appending the answer's
    word; Elements I does not say that and Elements II Definition 19.5 appends a
    different record. That rule is now the optional convention
    `Gaps.G1_18.g118_AppendsWord` (Lean gap G1-18).

    What the carrier does state is Definition 10.8's premise, "return
    assimilation changes the receiving state": the field `changes` (audit
    E1-B7 of 2026-09-26, fixed 2026-09-28). Elements I says the state changes and does not say how,
    so the field is an inequality and nothing more. -/
structure Assimilation where
  /-- `ℬ_𝒬 : (S_τ, Â_{τ+1}) ↦ S_{τ+1}` -/
  assimilate : SubstrateState → Answer → SubstrateState
  /-- Def 10.8: "return assimilation changes the receiving state". -/
  changes : ∀ S A, assimilate S A ≠ S

/-- **Definition 10.8 — the question-answer recursion.** One full cycle, when the
    crystallization resolves. It is a partial step and stays partial: an
    unresolved cycle returns no next state at all, only its failure. When it
    resolves, the returned state differs from the received one
    (`cycle_changes_the_state`). That is the book's premise, "return
    assimilation changes the receiving state", and no more: a changed state
    need not change the closure record (G1-23's square).

    `Sum.inr` carries the failure rather than discarding it, so a caller cannot
    mistake an unresolved cycle for a completed one.

    `X` is the seven ticks' start; at a question `𝒬_τ` it is `initialEnsemble Q`,
    and `cycle` resolves exactly when `crystQ K Q` does (`cycle_defined_iff`).
    It takes the ensemble, not the question: the book gives no rule forming
    `𝒬_{τ+1}` from `S_{τ+1}` (`cycle_changes_the_state`). -/
def cycle (K : Crystallization) (B : Assimilation)
    (S : SubstrateState) (X : Ensemble) : SubstrateState ⊕ Outcome :=
  match K.cryst X with
  | Outcome.resolved A => Sum.inl (B.assimilate S A)
  | o => Sum.inr o

/-- **The recursion assimilates the answer exactly when it resolves.** Def
    10.8's "assimilated answers alter the geometry the next question is asked
    in": a resolved cycle returns `ℬ_𝒬(S_τ, Â_{τ+1})`. What the alteration is,
    Elements I leaves to Elements II; under the append convention the history
    grows by the answer's word (`Gaps.G1_18.g118_cycle_records_the_answer`). -/
theorem cycle_assimilates_the_answer (K : Crystallization) (B : Assimilation)
    (S : SubstrateState) (X : Ensemble) {A : Answer}
    (h : K.cryst X = Outcome.resolved A) :
    cycle K B S X = Sum.inl (B.assimilate S A) := by
  unfold cycle
  rw [h]

/-- **A resolved cycle hands the next question a changed state.** Def 10.8's
    "because return assimilation changes the receiving state, the next question
    is formed from a changed geometry": whenever the cycle resolves, the state
    it returns is not the state it received.

    Only the change is stated. The recursion's last arrow `S_{τ+1} ⟶ 𝒬_{τ+1}`
    is not a map in Elements I (Def 9.1 lists what a question is made of and
    gives no rule forming it from a state), so it is not formalized here. -/
theorem cycle_changes_the_state (K : Crystallization) (B : Assimilation)
    (S : SubstrateState) (X : Ensemble) {T : SubstrateState}
    (h : cycle K B S X = Sum.inl T) : T ≠ S := by
  unfold cycle at h
  split at h
  · cases h
    exact B.changes _ _
  · cases h

end RatioSpace
