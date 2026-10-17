/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S16.WordDynamics
/-!
  Elements II §16, Proposition 16.9(iii) — Initial ensembles, exact finite
  verification.

  *"For all 105 two-member and 455 three-member initial ensembles drawn from
  the fifteen words of length at most three ... seven ensembles of each size
  are mirror-symmetric and never close."*

  `wordStep` (`WordDynamics.lean`, built for Theorem 16.12) is one tick of
  Definition 8.1 at `ε` read entirely off words, and `nextCores_words` proves
  it agrees with the real carrier tick. That is enough to decide the
  mirror-symmetric clause directly, with no multi-seed carrier construction
  needed at all.

  **Built here: the mirror-symmetric clause, all fourteen named ensembles.**
  Every two-member and three-member mirror-symmetric ensemble from the fifteen
  words of length at most three never reaches an occurrence singleton through
  nine ticks, decided on `wordStep`'s own tick map.

  **Not built, and named.** The proposition's remaining clauses — the exact
  closure counts at each horizon (76/105, 366/455, 20/105, 82/455), the
  accounting of which non-symmetric ensembles fail to close at seven, and the
  offset beat rule over all 558 non-symmetric ensembles that reach a
  singleton — are 560 traces of up to nine ticks each and are not formalised
  here.

  The two degeneracy instances the book's Proposition 16.9(iii) also names —
  `{L, LLR} → {LL, LR}` and `{L, LL, LLL} → {LL, LLR, LR}` — are in the
  tree: `Transient.lean`'s `prop_16_13_iv` and
  `prop_16_13_iii`, built for Proposition 16.13, are exactly these two
  instances against the real carrier, which is a strictly stronger witness
  than a word-level `decide`.
-/
set_option maxRecDepth 200000

namespace RatioSpace
namespace Two
namespace Ensemble169

open Step5Words

/-- Word literals, `true = R`, `false = L` (`Word.gen`, Definition 3.3). -/
def wL : Word := [false]
def wR : Word := [true]
def wLL : Word := [false, false]
def wLR : Word := [false, true]
def wRL : Word := [true, false]
def wRR : Word := [true, true]
def wLLL : Word := [false, false, false]
def wLLR : Word := [false, false, true]
def wLRL : Word := [false, true, false]
def wLRR : Word := [false, true, true]
def wRLL : Word := [true, false, false]
def wRLR : Word := [true, false, true]
def wRRL : Word := [true, true, false]
def wRRR : Word := [true, true, true]

/-- The seven mirror-symmetric two-member ensembles among the `C(15,2) = 105`
    pairs of words of length at most three: flipping every bit (`L ↔ R`)
    swaps each pair into itself, `u ≠ mirror u` since `u ≠ []`. One pair per
    nonempty word up to the pair itself: one at length one, two at length
    two, four at length three; each written here as its own two members. -/
def sym2 : List (List Word) :=
  [[wL, wR], [wLL, wRR], [wLR, wRL], [wLLL, wRRR], [wLLR, wRRL], [wLRL, wRLR],
   [wLRR, wRLL]]

/-- The seven mirror-symmetric three-member ensembles among the `C(15,3) =
    455` triples: a symmetric odd-sized set needs a self-mirror member, and
    `[]` is the only one, so these are exactly `{[], u, mirror u}` for the
    seven pairs above. -/
def sym3 : List (List Word) :=
  [[([] : Word), wL, wR], [([] : Word), wLL, wRR], [([] : Word), wLR, wRL],
   [([] : Word), wLLL, wRRR], [([] : Word), wLLR, wRRL],
   [([] : Word), wLRL, wRLR], [([] : Word), wLRR, wRLL]]

/-- One ensemble's support never collapses to a single occurrence through
    nine ticks of `wordStep`. -/
def neverCloses (ws : List Word) : Bool :=
  (List.range 10).all (fun j => (wIter j ws).length != 1)

/-- **Proposition 16.9(iii), the mirror-symmetric clause, both sizes.** All
    fourteen mirror-symmetric ensembles never close on an occurrence
    singleton through nine ticks. Decided directly on `wordStep`'s word-level
    tick map — the same construction Theorem 16.12 proved agrees with the
    real carrier — with no multi-seed carrier instance needed. -/
theorem sym2_never_closes : sym2.all neverCloses := by decide

theorem sym3_never_closes : sym3.all neverCloses := by decide

#print axioms sym2_never_closes
#print axioms sym3_never_closes

end Ensemble169
end Two
end RatioSpace
