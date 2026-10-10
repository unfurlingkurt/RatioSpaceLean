/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S25.Shell
/-!
  Gap G2-32 — Elements II §25, Corollary 25.9, Canonical seven-tick cycles do
  not automatically form shells: the "vertex-linked" clause.

  **Book statement (v0.22, item 2).** *"each side-selected root seven-tick
  singleton exports six vertex-linked faces, and each face-bearing singleton
  𝒬_LL, 𝒬_RR exports seven"*. Proof: *"Proposition 22.10 gives the face
  counts, and Theorem 25.8 gives the incidence obstruction."* "Vertex-linked"
  is Theorem 23.8's sense: faces `f_k`, `f_ℓ` of one committed lineage share
  exactly `x_k` when `ℓ = k + 1` and nothing when `ℓ > k + 1`, so the
  event-indexed family is "vertex-linked in a chain".

  **What was missing.** `cor_25_9_side` and `cor_25_9_lone` state the counts
  six and seven and incidence one, not that the recorded faces are
  vertex-linked. `lineage_vertices` (Theorem 23.8, vertices) was not composed
  with `traces_on_lineage` and the attached event lists `2..7` and `1..7`.

  **Built here.**
  * `ledger_evJ`: the event positions of the recorded ledger are exactly the
    attached events of the trace (Construction Axiom II.2's filter), in order,
    for any committed packets carrying the trace and any others that fail the
    lineage or snapshot entry. Nothing about the positions is assumed.
  * `shaped_V`: a one-lineage record's vertex list is Theorem 23.8's
    `lineFaceV i (evJ r)`.
  * `lineage_pair_vertices`: any two records of a one-lineage ledger at event
    positions `j < j'` share a vertex exactly when `j' = j + 1`, and then only
    `x_{j+1}` (Theorem 23.8 lifted from positions to records).
  * `chain_of_consecutive`: if a one-lineage ledger's positions are
    `a, a+1, …, a+n-1`, each record shares exactly `x_{j+1}` with the next and
    no vertex with any record two or more places later: a vertex-linked chain.
  * `cor_25_9_side_linked`, `cor_25_9_lone_linked`: on the recorded ledgers of
    the four singleton traces, positions are book events `2..7` (side) and
    `1..7` (lone), and the ledgers are vertex-linked chains, with the existing
    counts and incidence-one conclusions carried alongside.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_32

open RatioSpace.Two RatioSpace.Two.Face RatioSpace.Two.Incidence RatioSpace.Two.Shell

variable {Aux Cert RawAux EvalAux Prov Renew : Type} {h : ℕ}

/-! ## The recorded positions are the attached events -/

/-- Committed packets carrying the events, filtered by Construction Axiom II.2,
    have the attached events' positions. -/
theorem filter_all_j (t : QuestionId) :
    ∀ (c : List (FElig Aux Cert RawAux EvalAux h)) (es : List FaceRegression.Event),
      c.map (fun p => p.input) = es.map (fun e => e.toInput t) →
      (c.filter (fun p => p.elig.all)).map (fun p => p.input.j) =
        (FaceRegression.attached es).map FaceRegression.Event.j
  | [], [], _ => rfl
  | [], _ :: _, hm => nomatch hm
  | _ :: _, [], hm => nomatch hm
  | p :: c, e :: es, hm => by
    simp only [List.map_cons, List.cons.injEq] at hm
    have hv : p.elig.all = e.vec.all := by rw [p.elig_eq, hm.1, FaceRegression.Event.toInput_vector]
    have hj : p.input.j = e.j := by rw [hm.1]; rfl
    have ih := filter_all_j t c es hm.2
    unfold FaceRegression.attached at ih ⊢
    cases hb : e.vec.all
    · simp only [List.filter_cons, hv, hb]; exact ih
    · simp only [List.filter_cons, hv, hb, if_true, List.map_cons, hj, ih]

/-- **The ledger's event positions.** Recording the received faces of the
    committed packets of a trace, together with any packets failing the lineage
    or snapshot entry, gives one record per attached event, at that event's
    position, in order. -/
theorem ledger_evJ (es : List FaceRegression.Event) (t : QuestionId) (pv : Prov)
    (c o : List (FElig Aux Cert RawAux EvalAux h))
    (hmap : c.map (fun p => p.input) = es.map (fun e => e.toInput t))
    (ho : ∀ p ∈ o, (p.elig.lin && p.elig.snap) = false) :
    (ledgerOf (Renew := Renew) (receivedFaces (c ++ o)) t pv).map evJ =
      (FaceRegression.attached es).map FaceRegression.Event.j := by
  have hoff : o.filter (fun p => p.elig.all) = [] := by
    apply filter_eq_nil_of
    intro p hp
    have hls := ho p hp
    unfold Eligibility.all
    revert hls
    generalize p.elig.lin = a; generalize p.elig.adm = b; generalize p.elig.snap = c'
    generalize p.elig.recv = d; generalize p.elig.record = e
    revert a b c' d e; decide
  have hL : ledgerOf (Renew := Renew) (receivedFaces (c ++ o)) t pv =
      (c.filter (fun p => p.elig.all)).map (fun p => entryRec p t pv) := by
    unfold ledgerOf receivedFaces
    rw [List.filter_append, hoff, List.append_nil, List.map_map]
    rfl
  rw [hL, List.map_map]
  exact filter_all_j t c es hmap

/-! ## Theorem 23.8 on records -/

/-- A one-lineage record's occurrence vertices are `x_j, x_{j+1}, x_j^⊥` at its
    own event position. -/
theorem shaped_V {i : QuestionId} {r : FaceRec Aux Cert RawAux EvalAux h Prov Renew} (hr : LineShaped i r) :
    V r = lineFaceV i (evJ r) := by
  have hf := shaped_face hr
  change [r.id.v0, r.id.v1, r.id.v2] = _
  rw [show r.id.v0 = _ from congrArg TFace.v0 hf, show r.id.v1 = _ from congrArg TFace.v1 hf,
    show r.id.v2 = _ from congrArg TFace.v2 hf]
  rfl

/-- **Theorem 23.8, vertices, on records.** Two records of one lineage at
    positions `j < j'` share a vertex exactly when `j' = j + 1`, and then only
    `x_{j+1}`. -/
theorem lineage_pair_vertices (i : QuestionId) (r r' : FaceRec Aux Cert RawAux EvalAux h Prov Renew)
    (hr : LineShaped i r) (hr' : LineShaped i r') (hlt : evJ r < evJ r') (v : QuestionId) :
    (v ∈ V r ∧ v ∈ V r') ↔ (evJ r' = evJ r + 1 ∧ v = linV i (evJ r + 1)) := by
  rw [shaped_V hr, shaped_V hr']
  exact lineage_vertices i (evJ r) (evJ r') hlt hr'.hj v

/-- **Vertex-linked in a chain.** A one-lineage ledger whose positions are the
    consecutive run `a, a+1, …, a+n-1`: each record shares exactly the committed
    occurrence `x_{j+1}` with the next record, and no vertex with any record two
    or more places later. -/
theorem chain_of_consecutive (i : QuestionId) (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hL : ∀ r ∈ L, LineShaped i r) (a : ℕ) (hpos : L.map evJ = List.range' a L.length) :
    (∀ k (hk : k + 1 < L.length), ∀ v,
      (v ∈ V L[k] ∧ v ∈ V L[k + 1]) ↔ v = linV i (a + k + 1)) ∧
    (∀ k k' (hk : k' < L.length), ∀ (_ : k + 1 < k'), ∀ v, ¬ (v ∈ V L[k] ∧ v ∈ V L[k'])) := by
  have hev : ∀ k (hk : k < L.length), evJ L[k] = a + k := by
    intro k hk
    have := congrArg (fun l => l[k]?) hpos
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some,
      List.getElem?_range' hk, Option.some.injEq] at this
    rw [this]; omega
  refine ⟨fun k hk v => ?_, fun k k' hk hkk v => ?_⟩
  · have hk0 : k < L.length := by omega
    have e0 := hev k hk0
    have e1 := hev (k + 1) hk
    rw [lineage_pair_vertices i _ _ (hL _ (List.getElem_mem hk0)) (hL _ (List.getElem_mem hk)) (by omega) v, e0, e1]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  · have hk0 : k < L.length := by omega
    have e0 := hev k hk0
    have e1 := hev k' hk
    rw [lineage_pair_vertices i _ _ (hL _ (List.getElem_mem hk0)) (hL _ (List.getElem_mem hk)) (by omega) v, e0, e1]
    omega

/-! ## Corollary 25.9, item 2, with the vertex-linked clause -/

set_option maxRecDepth 200000 in
/-- **Corollary 25.9, item 2, side-selected root.** Each recorded ledger has six
    faces, at book events `2..7` (positions `1..6`), linked in a chain: the face at
    book event `k` shares exactly the committed occurrence `x_k` with the face at
    event `k+1` and no vertex with any face two or more places later. Incidence
    one, `c_2E = 0` and no closed shell input, as in `cor_25_9_side`. -/
theorem cor_25_9_side_linked (t : QuestionId) (pv : Prov) (cL oL cR oR : List (FElig Aux Cert RawAux EvalAux h))
    (hL : cL.map (fun p => p.input) = FaceRegression.eventsSideL.map (fun e => e.toInput t))
    (hoL : ∀ p ∈ oL, (p.elig.lin && p.elig.snap) = false)
    (hR : cR.map (fun p => p.input) = FaceRegression.eventsSideR.map (fun e => e.toInput t))
    (hoR : ∀ p ∈ oR, (p.elig.lin && p.elig.snap) = false) :
    let LL := ledgerOf (Renew := Renew) (receivedFaces (cL ++ oL)) t pv
    let LR := ledgerOf (Renew := Renew) (receivedFaces (cR ++ oR)) t pv
    LL.map (fun r => evJ r + 1) = [2, 3, 4, 5, 6, 7] ∧ LR.map (fun r => evJ r + 1) = [2, 3, 4, 5, 6, 7] ∧
    (∀ k (hk : k + 1 < LL.length), ∀ v, (v ∈ V LL[k] ∧ v ∈ V LL[k + 1]) ↔ v = linV xSideL (1 + k + 1)) ∧
    (∀ k k' (hk : k' < LL.length), ∀ (_ : k + 1 < k'), ∀ v, ¬ (v ∈ V LL[k] ∧ v ∈ V LL[k'])) ∧
    (∀ k (hk : k + 1 < LR.length), ∀ v, (v ∈ V LR[k] ∧ v ∈ V LR[k + 1]) ↔ v = linV xSideR (1 + k + 1)) ∧
    (∀ k k' (hk : k' < LR.length), ∀ (_ : k + 1 < k'), ∀ v, ¬ (v ∈ V LR[k] ∧ v ∈ V LR[k'])) ∧
    LL.length = 6 ∧ LR.length = 6 ∧
    (∀ k ∈ (recvId LL).EG, ((recvId LL).incE k).length = 1) ∧ (recvId LL).c2E = false ∧ ¬ (recvId LL).ClosedShellInput ∧
    (∀ k ∈ (recvId LR).EG, ((recvId LR).incE k).length = 1) ∧ (recvId LR).c2E = false ∧ ¬ (recvId LR).ClosedShellInput := by
  intro LL LR
  obtain ⟨lenL, lenR, a1, a2, a3, b1, b2, b3⟩ := cor_25_9_side (Renew := Renew) t pv cL oL cR oR hL hoL hR hoR
  obtain ⟨sL, dL, sR, dR, -⟩ := traces_on_lineage
  obtain ⟨shL, -⟩ := trace_ledger_shaped (Renew := Renew) xSideL _ t pv sL dL cL oL hL hoL
  obtain ⟨shR, -⟩ := trace_ledger_shaped (Renew := Renew) xSideR _ t pv sR dR cR oR hR hoR
  have pL : LL.map evJ = [1, 2, 3, 4, 5, 6] := by
    change (ledgerOf _ _ _).map evJ = _; rw [ledger_evJ _ t pv cL oL hL hoL]; decide
  have pR : LR.map evJ = [1, 2, 3, 4, 5, 6] := by
    change (ledgerOf _ _ _).map evJ = _; rw [ledger_evJ _ t pv cR oR hR hoR]; decide
  have qL : LL.map evJ = List.range' 1 LL.length := by rw [lenL, pL]; rfl
  have qR : LR.map evJ = List.range' 1 LR.length := by rw [lenR, pR]; rfl
  obtain ⟨cL1, cL2⟩ := chain_of_consecutive xSideL LL shL 1 qL
  obtain ⟨cR1, cR2⟩ := chain_of_consecutive xSideR LR shR 1 qR
  refine ⟨?_, ?_, cL1, cL2, cR1, cR2, lenL, lenR, a1, a2, a3, b1, b2, b3⟩
  · rw [show (fun r => evJ r + 1) = (· + 1) ∘ (evJ (Renew := Renew)) from rfl, ← List.map_map, pL]; rfl
  · rw [show (fun r => evJ r + 1) = (· + 1) ∘ (evJ (Renew := Renew)) from rfl, ← List.map_map, pR]; rfl

set_option maxRecDepth 200000 in
/-- **Corollary 25.9, item 2, face-bearing lone seeds.** Each recorded ledger has
    seven faces, at book events `1..7` (positions `0..6`), linked in a chain
    in the same sense. Incidence one, `c_2E = 0` and no closed shell input, as in
    `cor_25_9_lone`. -/
theorem cor_25_9_lone_linked (t : QuestionId) (pv : Prov) (cL oL cR oR : List (FElig Aux Cert RawAux EvalAux h))
    (hL : cL.map (fun p => p.input) = FaceRegression.eventsLL.map (fun e => e.toInput t))
    (hoL : ∀ p ∈ oL, (p.elig.lin && p.elig.snap) = false)
    (hR : cR.map (fun p => p.input) = FaceRegression.eventsRR.map (fun e => e.toInput t))
    (hoR : ∀ p ∈ oR, (p.elig.lin && p.elig.snap) = false) :
    let LL := ledgerOf (Renew := Renew) (receivedFaces (cL ++ oL)) t pv
    let LR := ledgerOf (Renew := Renew) (receivedFaces (cR ++ oR)) t pv
    LL.map (fun r => evJ r + 1) = [1, 2, 3, 4, 5, 6, 7] ∧ LR.map (fun r => evJ r + 1) = [1, 2, 3, 4, 5, 6, 7] ∧
    (∀ k (hk : k + 1 < LL.length), ∀ v, (v ∈ V LL[k] ∧ v ∈ V LL[k + 1]) ↔ v = linV xLL (0 + k + 1)) ∧
    (∀ k k' (hk : k' < LL.length), ∀ (_ : k + 1 < k'), ∀ v, ¬ (v ∈ V LL[k] ∧ v ∈ V LL[k'])) ∧
    (∀ k (hk : k + 1 < LR.length), ∀ v, (v ∈ V LR[k] ∧ v ∈ V LR[k + 1]) ↔ v = linV xRR (0 + k + 1)) ∧
    (∀ k k' (hk : k' < LR.length), ∀ (_ : k + 1 < k'), ∀ v, ¬ (v ∈ V LR[k] ∧ v ∈ V LR[k'])) ∧
    LL.length = 7 ∧ LR.length = 7 ∧
    (∀ k ∈ (recvId LL).EG, ((recvId LL).incE k).length = 1) ∧ (recvId LL).c2E = false ∧ ¬ (recvId LL).ClosedShellInput ∧
    (∀ k ∈ (recvId LR).EG, ((recvId LR).incE k).length = 1) ∧ (recvId LR).c2E = false ∧ ¬ (recvId LR).ClosedShellInput := by
  intro LL LR
  obtain ⟨lenL, lenR, a1, a2, a3, b1, b2, b3⟩ := cor_25_9_lone (Renew := Renew) t pv cL oL cR oR hL hoL hR hoR
  obtain ⟨-, -, -, -, sL, dL, sR, dR⟩ := traces_on_lineage
  obtain ⟨shL, -⟩ := trace_ledger_shaped (Renew := Renew) xLL _ t pv sL dL cL oL hL hoL
  obtain ⟨shR, -⟩ := trace_ledger_shaped (Renew := Renew) xRR _ t pv sR dR cR oR hR hoR
  have pL : LL.map evJ = [0, 1, 2, 3, 4, 5, 6] := by
    change (ledgerOf _ _ _).map evJ = _; rw [ledger_evJ _ t pv cL oL hL hoL]; decide
  have pR : LR.map evJ = [0, 1, 2, 3, 4, 5, 6] := by
    change (ledgerOf _ _ _).map evJ = _; rw [ledger_evJ _ t pv cR oR hR hoR]; decide
  have qL : LL.map evJ = List.range' 0 LL.length := by rw [lenL, pL]; rfl
  have qR : LR.map evJ = List.range' 0 LR.length := by rw [lenR, pR]; rfl
  obtain ⟨cL1, cL2⟩ := chain_of_consecutive xLL LL shL 0 qL
  obtain ⟨cR1, cR2⟩ := chain_of_consecutive xRR LR shR 0 qR
  refine ⟨?_, ?_, cL1, cL2, cR1, cR2, lenL, lenR, a1, a2, a3, b1, b2, b3⟩
  · rw [show (fun r => evJ r + 1) = (· + 1) ∘ (evJ (Renew := Renew)) from rfl, ← List.map_map, pL]; rfl
  · rw [show (fun r => evJ r + 1) = (· + 1) ∘ (evJ (Renew := Renew)) from rfl, ← List.map_map, pR]; rfl

end G2_32
end Gaps
end RatioSpace

#print axioms RatioSpace.Gaps.G2_32.filter_all_j
#print axioms RatioSpace.Gaps.G2_32.ledger_evJ
#print axioms RatioSpace.Gaps.G2_32.shaped_V
#print axioms RatioSpace.Gaps.G2_32.lineage_pair_vertices
#print axioms RatioSpace.Gaps.G2_32.chain_of_consecutive
#print axioms RatioSpace.Gaps.G2_32.cor_25_9_side_linked
#print axioms RatioSpace.Gaps.G2_32.cor_25_9_lone_linked
