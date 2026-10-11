/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S13.SideExchange
/-!
  Elements II §21 — Candidate sibling shortcuts.

  Every proposal event generates and archives both children of every active
  parent. This section records that pair, reads off the exact relation between
  the two children (`A_s`), and proves the relation is not an edge of raw
  ancestry: generation, reception and attachment stay three different facts.

  Almost nothing here is new machinery. `A_s` and its prefix independence are
  §10 (`Causal.lean`), child disjointness is Proposition 5.4, parent recovery is
  Theorem 6.7, archiving before selection is §11, prefix cancellation is Theorem
  3.4 and the side action is `SideExchange.lean`. What §21 adds is the raw
  ancestry graph and the proof that sibling shortcuts never hide inside it.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Two
namespace Shortcut

open Mat2 Word Frame Pres RatioSpace SideExchange Advance Observer

/-! ## Definition 21.1 — Archived sibling pair at one event -/

/-- **Definition 21.1.** `Pair_{j+1}(x)`: the parent's identifier, both
    children's identifiers, both causal records, both admission certificates and
    both creation statuses. Nine components, each named. -/
structure SiblingPair (Aux Cert : Type) where
  parentId : QuestionId
  idL : QuestionId
  idR : QuestionId
  cfL : CausalRecord
  cfR : CausalRecord
  admL : AdmCert Aux
  admR : AdmCert Aux
  statL : ProposalStatus Cert
  statR : ProposalStatus Cert

/-- The pair generated beneath the archived occurrence `c` at one event. -/
def pairOf {Aux Cert : Type} (c : Core) (entry : ℕ) (prov : Provenance)
    (admL admR : AdmCert Aux) (statL statR : ProposalStatus Cert) : SiblingPair Aux Cert where
  parentId := c.id
  idL := (childCore c false entry prov).id
  idR := (childCore c true entry prov).id
  cfL := causalRecord c.seedId c.seed c.relWord false
  cfR := causalRecord c.seedId c.seed c.relWord true
  admL := admL
  admR := admR
  statL := statL
  statR := statR

/-- **Definition 21.1, the oriented candidate shortcut** `Sh_{j+1}(x;s)`:
    the pair, the designated child, its counter-child, and `A_s = s⁻¹s̄`. The
    designation is an orientation only; nothing here says selected, refused or
    attached. (`false` is `L`.) -/
structure OrientedShortcut (Aux Cert : Type) where
  pair : SiblingPair Aux Cert
  idS : QuestionId
  idBar : QuestionId
  mat : Mat2

def shortcut {Aux Cert : Type} (p : SiblingPair Aux Cert) (s : Bool) : OrientedShortcut Aux Cert where
  pair := p
  idS := cond s p.idR p.idL
  idBar := cond s p.idL p.idR
  mat := A s

/-- The two causal records present one generated pair: for a well-formed parent
    both name the same parent identifier. -/
theorem pairOf_records_share_parent {Aux Cert : Type} (c : Core) (hc : c.WellFormed)
    (entry : ℕ) (prov : Provenance) (admL admR : AdmCert Aux) (statL statR : ProposalStatus Cert) :
    (pairOf c entry prov admL admR statL statR).cfL.parentId = c.id ∧
    (pairOf c entry prov admL admR statL statR).cfR.parentId = c.id :=
  ⟨hc.2.2.2.2.1.symm, hc.2.2.2.2.1.symm⟩

/-- The two orientations carry mutually inverse matrices (Definition 10.5). -/
theorem shortcut_mats_inverse {Aux Cert : Type} (p : SiblingPair Aux Cert) :
    (shortcut p true).mat = inv2 (shortcut p false).mat := by
  change A true = inv2 (A false); decide

/-! ## Definition 21.2 — Raw occurrence-ancestry graph -/

/-- `V_raw = ids(ℋ_h)`. -/
def rawVertices (archive : List Core) : List QuestionId := archIds archive

/-- `E_raw = {(ι_x, ι_y) : y nonseed, x = par(y)}`, keyed by occurrence identity:
    read off each archived core's own parent field, nothing else. -/
def rawEdges (archive : List Core) : List (QuestionId × QuestionId) :=
  archive.filterMap (fun c => c.parent.map (fun p => (p, c.id)))

theorem mem_rawEdges {archive : List Core} {p i : QuestionId} :
    (p, i) ∈ rawEdges archive ↔ ∃ c ∈ archive, c.parent = some p ∧ c.id = i := by
  unfold rawEdges
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, h⟩
    cases hp : c.parent with
    | none => simp [hp] at h
    | some q =>
      simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨c, hc, by rw [hp, h.1], h.2⟩
  · rintro ⟨c, hc, hp, hi⟩
    exact ⟨c, hc, by simp [hp, hi]⟩

/-! ## Theorem 21.3 — Raw ancestry contains no sibling edge or cycle -/

/-- The invariant raw ancestry needs: every recorded parent really is the
    parent, one hand up. -/
def ParentCoherent (archive : List Core) : Prop :=
  ∀ c ∈ archive, ∀ p, c.parent = some p → ∃ g, c.id = p.child g

theorem mem_proposals {archive : List Core} {active : List QuestionId} {c : Core} {g : Bool} :
    (c, g) ∈ proposals archive active ↔ c ∈ archive ∧ c.id ∈ active := by
  unfold proposals
  simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨c', ⟨hc', hid⟩, h⟩
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨hc', hid⟩
  · rintro ⟨hc, hid⟩
    exact ⟨c, ⟨hc, hid⟩, by cases g <;> simp⟩

/-- **A tick-zero archive is parent-coherent**: its seeds carry no parent. -/
theorem parentCoherent_seed (id0 : QuestionId) (seed : History) (entry : ℕ) (prov : Provenance) :
    ParentCoherent [seedCore id0 seed entry prov] := by
  intro c hc p hp
  simp only [List.mem_singleton] at hc
  subst hc
  exact absurd hp (by simp [seedCore, Core.ofProposal])

/-- **The advance preserves it.** Kept cores were coherent already; each new core
    is `childCore q g` of a well-formed archived parent, whose recorded parent is
    `q.id` and whose id is `q.id.child g`. -/
theorem parentCoherent_advance {archive : List Core} {active : List QuestionId}
    {stratum : ℕ} {prov : Provenance}
    (hwf : ∀ c ∈ archive, c.WellFormed) (hpc : ParentCoherent archive) :
    ParentCoherent (advanceArchive archive active stratum prov) := by
  intro c hc p hp
  unfold advanceArchive keyedUnion at hc
  rcases List.mem_append.mp hc with h | h
  · exact hpc c h p hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_filter.mp h).1
    have hq1 : q.1 ∈ archive := (mem_proposals.mp hq).1
    have hpar : (childCore q.1 q.2 stratum prov).parent = some q.1.id :=
      (childCore_traversal q.1 q.2 stratum prov).2.1
    rw [hpar, Option.some.injEq] at hp
    subst hp
    exact ⟨q.2, childCore_id q.1 (hwf q.1 hq1) q.2 stratum prov⟩

/-- Every raw edge goes exactly one hand down. -/
theorem rawEdge_child {archive : List Core} (hpc : ParentCoherent archive)
    {p i : QuestionId} (he : (p, i) ∈ rawEdges archive) : ∃ g, i = p.child g := by
  obtain ⟨c, hc, hp, rfl⟩ := mem_rawEdges.mp he
  exact hpc c hc p hp

theorem rawEdge_depth {archive : List Core} (hpc : ParentCoherent archive)
    {p i : QuestionId} (he : (p, i) ∈ rawEdges archive) :
    i.rel.length = p.rel.length + 1 := by
  obtain ⟨g, rfl⟩ := rawEdge_child hpc he
  simp [QuestionId.child]

/-- **Unique parent**: no vertex has two incoming raw edges. -/
theorem rawEdge_unique_parent {archive : List Core} (hpc : ParentCoherent archive)
    {p p' i : QuestionId} (he : (p, i) ∈ rawEdges archive) (he' : (p', i) ∈ rawEdges archive) :
    p = p' := by
  obtain ⟨g, hg⟩ := rawEdge_child hpc he
  obtain ⟨g', hg'⟩ := rawEdge_child hpc he'
  exact (QuestionId.child_inj (hg.symm.trans hg')).1

/-- A directed path of raw edges from `a` through the list `vs`. -/
def RawPath (archive : List Core) : QuestionId → List QuestionId → Prop
  | _, [] => True
  | a, b :: vs => (a, b) ∈ rawEdges archive ∧ RawPath archive b vs

/-- Along a directed path of raw edges, depth rises by exactly one per edge. -/
theorem rawPath_depth {archive : List Core} (hpc : ParentCoherent archive) :
    ∀ (a : QuestionId) (vs : List QuestionId), RawPath archive a vs →
      ((a :: vs).getLast (by simp)).rel.length = a.rel.length + vs.length
  | a, [], _ => by simp
  | a, b :: vs, h => by
    have ih := rawPath_depth hpc b vs h.2
    have hd := rawEdge_depth hpc h.1
    simp only [List.getLast_cons_cons] at ih ⊢
    rw [ih, hd, List.length_cons]; omega

/-- **Theorem 21.3, no directed cycle.** A nonempty directed path of raw edges
    never returns to its start. -/
theorem rawEdges_acyclic {archive : List Core} (hpc : ParentCoherent archive)
    (a : QuestionId) (vs : List QuestionId) (hne : vs ≠ []) (h : RawPath archive a vs) :
    (a :: vs).getLast (by simp) ≠ a := by
  intro heq
  have hd := rawPath_depth hpc a vs h
  rw [heq] at hd
  have : vs.length ≠ 0 := by simpa using hne
  omega

/-- **Theorem 21.3, no sibling edge.** Neither `(ι_{xL}, ι_{xR})` nor
    `(ι_{xR}, ι_{xL})` is a raw edge: the two siblings have equal depth. -/
theorem no_sibling_edge {archive : List Core} (hpc : ParentCoherent archive) (x : QuestionId) :
    (x.child false, x.child true) ∉ rawEdges archive ∧
    (x.child true, x.child false) ∉ rawEdges archive := by
  refine ⟨fun he => ?_, fun he => ?_⟩ <;>
  · have hd := rawEdge_depth hpc he
    simp only [QuestionId.child, List.length_append, List.length_singleton] at hd
    omega

/-! ## Proposition 21.4 — The candidate shortcut is a relative reception object -/

/-- **Proposition 21.4.** `Q_{xs, xs̄} = M_{xs}⁻¹ M_{xs̄} = A_s`, for every parent,
    seed, prefix, event and provenance: none of them appears on the right. The
    support coherence is not an input at all. -/
theorem shortcut_matrix (c : Core) (s : Bool) (entry : ℕ) (prov : Provenance) :
    Q (childCore c s entry prov).fullMatrix (childCore c (!s) entry prov).fullMatrix = A s :=
  childProposal_sibling_matrix c.seedId c.seed c.relWord s

/-- Independence, stated as independence: two different parents at two
    different events give the same shortcut matrix for the same hand. -/
theorem shortcut_matrix_independent (c c' : Core) (s : Bool) (e e' : ℕ) (pv pv' : Provenance) :
    Q (childCore c s e pv).fullMatrix (childCore c (!s) e pv).fullMatrix =
      Q (childCore c' s e' pv').fullMatrix (childCore c' (!s) e' pv').fullMatrix := by
  rw [shortcut_matrix, shortcut_matrix]

/-! ## Corollary 21.5 — A candidate shortcut leaves raw ancestry unchanged -/

/-- **Corollary 21.5.** The shortcut's two endpoints are not joined by a raw
    edge in either direction, and forming the shortcut record does not change
    `rawEdges`, which reads the archive alone. -/
theorem shortcut_not_raw_edge {Aux Cert : Type} {archive : List Core}
    (hpc : ParentCoherent archive) (c : Core) (hc : c.WellFormed) (entry : ℕ) (prov : Provenance)
    (admL admR : AdmCert Aux) (statL statR : ProposalStatus Cert) (s : Bool) :
    let sh := shortcut (pairOf c entry prov admL admR statL statR) s
    (sh.idS, sh.idBar) ∉ rawEdges archive ∧ (sh.idBar, sh.idS) ∉ rawEdges archive := by
  intro sh
  have hL : (childCore c false entry prov).id = c.id.child false := childCore_id c hc false entry prov
  have hR : (childCore c true entry prov).id = c.id.child true := childCore_id c hc true entry prov
  obtain ⟨h1, h2⟩ := no_sibling_edge hpc c.id
  cases s
  · change ((childCore c false entry prov).id, (childCore c true entry prov).id) ∉ rawEdges archive ∧
        ((childCore c true entry prov).id, (childCore c false entry prov).id) ∉ rawEdges archive
    rw [hL, hR]; exact ⟨h1, h2⟩
  · change ((childCore c true entry prov).id, (childCore c false entry prov).id) ∉ rawEdges archive ∧
        ((childCore c false entry prov).id, (childCore c true entry prov).id) ∉ rawEdges archive
    rw [hL, hR]; exact ⟨h2, h1⟩

/-! ## Theorem 21.6 — Completeness and finite cardinality of candidate shortcuts -/

/-- The unoriented sibling pairs generated at one event, as
    `(ι_x, ι_{xL}, ι_{xR})`, one per active archived parent. -/
def pairsAt (archive : List Core) (active : List QuestionId) (stratum : ℕ) (prov : Provenance) :
    List (QuestionId × QuestionId × QuestionId) :=
  (archive.filter (fun c => c.id ∈ active)).map
    (fun c => (c.id, (childCore c false stratum prov).id, (childCore c true stratum prov).id))

/-- The oriented candidate shortcuts at one event, as `(ι_{xs}, ι_{xs̄}, A_s)`. -/
def orientedAt (archive : List Core) (active : List QuestionId) (stratum : ℕ) (prov : Provenance) :
    List (QuestionId × QuestionId × Mat2) :=
  (archive.filter (fun c => c.id ∈ active)).flatMap
    (fun c => [((childCore c false stratum prov).id, (childCore c true stratum prov).id, A false),
               ((childCore c true stratum prov).id, (childCore c false stratum prov).id, A true)])

theorem pairsAt_length (archive : List Core) (active : List QuestionId) (stratum : ℕ) (prov : Provenance) :
    (pairsAt archive active stratum prov).length = (archive.filter (fun c => c.id ∈ active)).length := by
  simp [pairsAt]

theorem orientedAt_length (archive : List Core) (active : List QuestionId) (stratum : ℕ) (prov : Provenance) :
    (orientedAt archive active stratum prov).length =
      2 * (archive.filter (fun c => c.id ∈ active)).length := by
  unfold orientedAt
  induction archive.filter (fun c => c.id ∈ active) with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]; omega

/-- **Distinct parent–hand pairs give distinct children** (Proposition 5.4), so
    no generated pair is counted twice. -/
theorem children_disjoint {c c' : Core} (hc : c.WellFormed) (hc' : c'.WellFormed)
    {g g' : Bool} {e e' : ℕ} {pv pv' : Provenance}
    (h : (childCore c g e pv).id = (childCore c' g' e' pv').id) : c.id = c'.id ∧ g = g' :=
  childCore_id_inj hc hc' h

/-- `N_pair^(h) = Σ_{j<h} |S_j|` over a trace given event by event, each event
    as its archive, active support and stratum. -/
def nPair (events : List (List Core × List QuestionId × ℕ)) : ℕ :=
  (events.map (fun e => (e.1.filter (fun c => c.id ∈ e.2.1)).length)).sum

/-- **Theorem 21.6.** Over any finite trace, exactly `Σ|S_j|` unoriented pairs
    and exactly `2 Σ|S_j|` oriented shortcuts; both zero at `h = 0`. -/
theorem shortcut_counts (events : List (List Core × List QuestionId × ℕ)) (prov : Provenance) :
    (events.map (fun e => (pairsAt e.1 e.2.1 e.2.2 prov).length)).sum = nPair events ∧
    (events.map (fun e => (orientedAt e.1 e.2.1 e.2.2 prov).length)).sum = 2 * nPair events ∧
    nPair [] = 0 := by
  refine ⟨?_, ?_, rfl⟩
  · induction events with
    | nil => rfl
    | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, pairsAt_length, nPair] at ih ⊢
      try omega
  · induction events with
    | nil => rfl
    | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, orientedAt_length, nPair] at ih ⊢
      try omega

/-! ## Definition 21.7 — Committed terminal lineage -/

/-- **Definition 21.7.** `Lin(x*) = (x_0, …, x_h)`, `x_j = par(x_{j+1})`: the
    `k`-th entry is the terminal identifier with its relative word cut to `k`. -/
def lineage (i : QuestionId) : List QuestionId :=
  (List.range (i.rel.length + 1)).map (fun k => { i with rel := i.rel.take k })

/-- The archived counter-sibling `x_{k+1}^⊥ = x_k s̄_{k+1}`. -/
def counterSibling (i : QuestionId) (k : ℕ) : QuestionId :=
  { i with rel := i.rel.take k ++ [!(i.rel.getD k false)] }

/-- Consecutive lineage entries are parent and child: `par(x_{k+1}) = x_k`. -/
theorem lineage_parent (i : QuestionId) (k : ℕ) (hk : k < i.rel.length) :
    ({ i with rel := i.rel.take (k + 1) } : QuestionId).parent = { i with rel := i.rel.take k } := by
  simp only [QuestionId.parent, QuestionId.mk.injEq, true_and]
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.dropLast_concat]

/-- The counter-sibling is the other child of the same parent. -/
theorem counterSibling_eq (i : QuestionId) (k : ℕ) :
    counterSibling i k = ({ i with rel := i.rel.take k } : QuestionId).child (!(i.rel.getD k false)) := rfl

/-! ## Theorem 21.8 — Uniqueness and recoverability of the committed lineage -/

/-- **Theorem 21.8, uniqueness.** Any two chains that end at the same terminal
    occurrence and obey `x_j = par(x_{j+1})` agree at every position: the parent
    record is a function, so the lineage is determined by its endpoint. -/
theorem lineage_unique (h : ℕ) (x y : ℕ → QuestionId) (hxh : x h = y h)
    (hx : ∀ j < h, x j = (x (j + 1)).parent) (hy : ∀ j < h, y j = (y (j + 1)).parent) :
    ∀ j ≤ h, x j = y j := by
  intro j hj
  obtain ⟨d, rfl⟩ : ∃ d, j = h - d := ⟨h - j, by omega⟩
  induction d with
  | zero => simpa using hxh
  | succ d ih =>
    by_cases hd : d < h
    · have h1 : h - (d + 1) < h := by omega
      have h2 : h - (d + 1) + 1 = h - d := by omega
      rw [hx _ h1, hy _ h1, h2, ih (by omega)]
    · have : h - (d + 1) = h - d := by omega
      rw [this]; exact ih (by omega)

/-- **Theorem 21.8, recoverability, at the event.** An active archived parent
    has both children archived by the advance, before and regardless of
    selection — so the counter-sibling of whichever child the lineage takes is
    in the archive, even if it was rejected. -/
theorem counter_sibling_archived {archive : List Core} {active : List QuestionId}
    {stratum : ℕ} {prov : Provenance} {c : Core} (hc : c ∈ archive) (hact : c.id ∈ active) (g : Bool)
    (hfresh : (childCore c g stratum prov).id ∉ archIds archive) :
    childCore c g stratum prov ∈ advanceArchive archive active stratum prov :=
  child_archived_regardless_of_selection (p := (c, g)) (mem_proposals.mpr ⟨hc, hact⟩) hfresh

/-- **Theorem 21.8, recoverability, afterward.** Nothing archived is ever
    dropped by a later advance, so the counter-sibling survives to the terminal
    archive. -/
theorem archive_monotone {archive : List Core} {active : List QuestionId}
    {stratum : ℕ} {prov : Provenance} {c : Core} (hc : c ∈ archive) :
    c ∈ advanceArchive archive active stratum prov :=
  mem_keyedUnion_left hc

/-! ## Proposition 21.9 — Covariance of the candidate family -/

/-- **Proposition 21.9, prefix transport.** A common prefix cancels from the
    relative matrix, so the shortcut matrix is unchanged (Theorem 3.4). -/
theorem shortcut_prefix_invariant (u : Word) (c : Core) (s : Bool) (entry : ℕ) (prov : Provenance) :
    Q (Z u (childCore c s entry prov).fullMatrix) (Z u (childCore c (!s) entry prov).fullMatrix) = A s := by
  rw [thm_3_4]; exact shortcut_matrix c s entry prov

/-- **Proposition 21.9, side exchange on the matrix.** `𝖯A_s𝖯 = A_s̄ = A_s⁻¹`. -/
theorem side_exchange_shortcut_matrix (s : Bool) :
    SideExchange.P * A s * SideExchange.P = A (!s) ∧ A (!s) = inv2 (A s) := by
  cases s <;> exact ⟨by decide, by decide⟩

/-- **Proposition 21.9, side exchange on the occurrences.** `Sh(x;s) ↦ Sh(𝖯x;s̄)`:
    the exchanged parent's `s̄`-child is the exchange of the `s`-child, and its
    `s`-child is the exchange of the `s̄`-child. -/
theorem side_exchange_shortcut_children (c : Core) (s : Bool) (entry : ℕ) (prov : Provenance) :
    childCore (Core.mirror c) (!s) entry prov = Core.mirror (childCore c s entry prov) ∧
    childCore (Core.mirror c) s entry prov = Core.mirror (childCore c (!s) entry prov) := by
  refine ⟨childCore_mirror c s entry prov, ?_⟩
  have := childCore_mirror c (!s) entry prov
  simpa using this

/-! ## Separation Rule 21.10 — Generation, reception, and attachment

    *"a sibling pair was generated ≠ its shortcut was received ≠ its triangular
    cell was attached."* Carried by the types: `SiblingPair` and
    `OrientedShortcut` are records, `rawEdges` reads only archived parent fields
    (`shortcut_not_raw_edge`), and nothing in this file or its import closure
    declares a received edge, a face or an attachment. That negative claim is
    checked by a comment-stripped scan of the closure, not asserted. -/

#print axioms pairOf_records_share_parent
#print axioms shortcut_mats_inverse
#print axioms mem_rawEdges
#print axioms mem_proposals
#print axioms parentCoherent_seed
#print axioms parentCoherent_advance
#print axioms rawEdge_unique_parent
#print axioms rawPath_depth
#print axioms rawEdges_acyclic
#print axioms no_sibling_edge
#print axioms shortcut_matrix
#print axioms shortcut_matrix_independent
#print axioms shortcut_not_raw_edge
#print axioms pairsAt_length
#print axioms orientedAt_length
#print axioms children_disjoint
#print axioms shortcut_counts
#print axioms lineage_parent
#print axioms lineage_unique
#print axioms counter_sibling_archived
#print axioms archive_monotone
#print axioms shortcut_prefix_invariant
#print axioms side_exchange_shortcut_matrix
#print axioms side_exchange_shortcut_children

end Shortcut
end Two
end RatioSpace
