/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S11.JointRelationalReconstruction
/-!
  Gap G1-27 — Elements I §15, Definition 15.3, the universal generative
  claim: `Complete` was not Definition 15.2.

  **Book statement.** "A universal RatioSpace claim is the assertion that
  generative sufficiency and relational completeness hold for every finitely
  distinguishable admissible mechanics under consideration." Def 15.2: "a
  family of relations is complete for a target class when its joint reception
  map is injective up to the target's declared equivalence."

  **What was wrong.** `UniversalGenerativeClaim` took
  `Complete : ∀ D, GenerativelySufficient D → Prop` as an arbitrary predicate,
  and `universal_claim_holds_on_the_word_domain` (the pre-G1-27 theorem of
  that name, now `universal_claim_over_holds_on_wordByClosureDomain`) took it
  to be `True`, so
  relational completeness was exercised nowhere.

  **Changed (`Sufficiency.lean`).** `GenerativelySufficient.CompleteFor G Vs`:
  Def 15.2 at a domain, equal joint readings of two encoded histories force
  `D.same`; `completeFor_iff`: it is `RelationallyComplete Vs` over the encoded
  class with the target's equivalence carried to presented states.
  `UniversalGenerativeClaim Admissible` asks, at every admissible domain, for
  a sufficiency term complete for its own item-4 receptions (`G.family`). The
  old form is `UniversalGenerativeClaimOver` (`universalGenerativeClaim_eq_over`,
  `rfl`).
  * `wordByClosureDomain_not_complete`, `universal_claim_fails_on_wordByClosureDomain`: the
    closure-read word domain meets Def 15.1 and not Def 15.3, for every sufficiency term:
    its reading (the closure record) reads `ε` and `R^12` alike and
    it declares only equal words the same.
  * `closureDomain` (words the same when their closure records agree):
    `closureSufficient`, `closureSufficientAt_complete`,
    `universal_claim_holds_on_the_closure_domain`.

  **Added here: why the family is the term's own.** A fresh-context verifier
  passed a first version whose family was a free parameter; the adversarial
  reviewer failed it, because a family chosen apart from item 4 is bounded by
  nothing the domain declares (`completeFor_presentedWord`). The term's own
  receptions are bounded by the domain's `Reading`; item 5 constrains only
  their projection to `Quantity`.
  * `g127_presentedWord_complete`: a root observer reading the presented word
    completes the closure-read word domain, which its own receptions cannot.
  * `g127_bottomRow_not_complete`: G1-21's root bottom row does not; the
    choice of family carries content either way.
  * `richWordDomain`, `g127_rich_claim`: the closure-read word domain with its
    reading
    widened to (word, closure record), quantity and `same` unchanged, meets
    the claim. What decides it is the declared `Reading`. (Second adversarial
    review of G1-27.)

  **Follow-up, 2026-09-27.** The witness built 2026-08-24 as `wordDomain` was
  this tree's own, declared with the closure record as its reading and word
  equality as its `same`; it is renamed `wordByClosureDomain` for that
  reading, with its terms and theorems. `wordDomain` now reads the word
  (`Sufficiency.lean`: reading the presented word, quantity its closure
  record, `same` equality) and meets the claim
  (`universal_claim_holds_on_the_word_domain`). Nothing in Def 15.3 failed; a
  declaration that keeps apart what it cannot read did.
-/

namespace RatioSpace

namespace Gaps.G1_27

open Layer

/-- The perspective that declares the presented word and reads it. -/
def presentedWordPerspective : Perspective Word Word where
  reception :=
    { mask := { Mask.blank with presentedWord := true }
      read := EncounterRecord.presentedWord
      honest := fun _ _ h => h.2.1 rfl }
  projection := ⟨id⟩

/-- One root observer reading the presented word: a quantity the closure-read
    word domain does not declare readable (`wordByClosureDomain.Reading` is the
    closure record). -/
def wordFamily : Fin 1 → Viewpoint :=
  fun _ => ⟨⟨Frame.empty, [], 0⟩, Word, Word, presentedWordPerspective⟩

/-- **A free family completes what the domain's receptions cannot.** Against
    `wordByClosureDomain_not_complete`: this is the cheap reading the claim excludes. -/
theorem g127_presentedWord_complete : wordByClosureSufficient.CompleteFor wordFamily :=
  wordByClosureSufficient.completeFor_presentedWord (fun _ _ h => h) wordFamily 0
    (fun _ _ => Iff.rfl)

/-- **Not complete.** With the word encoding, the empty word and `R` give the
    root the same bottom row, and the target keeps them apart. -/
theorem g127_bottomRow_not_complete (G : GenerativelySufficient wordByClosureDomain)
    (hG : G.encode = wordEncode) : ¬ G.CompleteFor G1_21.onlyRoot := by
  intro hc
  have h := hc ([] : Word) [true] (by
    rw [hG]
    funext i
    rfl)
  exact List.cons_ne_nil _ _ h.symm

/-- The closure-read word domain with its reading widened to the word and its closure
    record; the quantity (closure record) and `same` (equality) unchanged. -/
def richWordDomain : Domain :=
  { wordByClosureDomain with Reading := Word × ClosureState, project := Prod.snd }

/-- The reception declaring the presented word and the presented closure. -/
def wordAndClosureReception : Reception (Word × ClosureState) where
  mask := { Mask.blank with presentedWord := true, presentedClosure := true }
  read := fun E => (E.presentedWord, E.presentedClosure)
  honest := fun _ _ h => by
    simp only [Prod.mk.injEq]
    exact ⟨h.2.1 rfl, h.2.2.2.2.1 rfl⟩

def richSufficient : GenerativelySufficient richWordDomain where
  encode := wordEncode
  realize := fun t => ⟨wordRealize t, fun _ => rfl⟩
  identify :=
    ⟨fun S T => S = T, fun (u v : Word) => by
      constructor
      · intro h; exact congrArg wordEncode h
      · intro h; exact congrArg SubstrateState.word h⟩
  equiv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  observers := [⟨Frame.empty, [], 0⟩]
  nonempty := ⟨_, List.mem_singleton_self _⟩
  reception := ObsReception.const wordAndClosureReception
  recovers := fun _ _ w => ClosureState.of_empty w

/-- **Widen the reading and the claim holds**, with words the same only when
    equal: the term's own reception reads the word. -/
theorem g127_rich_claim : UniversalGenerativeClaim (fun D => D = richWordDomain) := by
  intro D hD; subst hD
  refine ⟨richSufficient, ?_⟩
  intro (u : Word) (v : Word) hj
  have := congrFun hj ⟨0, by decide⟩
  exact congrArg Prod.fst this

end Gaps.G1_27

end RatioSpace
