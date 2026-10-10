/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S22.Face
/-!
  Elements II §23 — Incidence-carrying face recording.

  §22 attached faces. §23 records each attached face with stable identifiers,
  its oriented boundary, and exact incidence maps, and appends the ledger to the
  history. The one-lineage theorem (23.8) is the section's content: consecutive
  faces share exactly one occurrence, others share none, so every edge has
  incidence one and the family is a vertex-linked chain, never a closed surface.

  **No quotient is taken.** An unordered edge is not a `Sym2`; `UEdge.same` is a
  decidable relation on the recorded endpoints and the edge type, exactly as the
  book's `Und` forgets orientation and nothing else.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Two
namespace Incidence

open Mat2 Word Frame Pres RatioSpace SideExchange Advance Observer Shortcut Return Terminal Face

variable {Aux Cert RawAux EvalAux Prov Renew Op : Type} {h : ℕ}

/-! ## Definition 23.1 — Stable vertex, edge, and face identifiers -/

inductive EdgeType where
  | raw
  | received
deriving DecidableEq

/-- The label an oriented edge carries: a generator, a received matrix, or an
    inverse generator traversed backwards. -/
inductive EdgeLabel where
  | gen : Bool → EdgeLabel
  | mat : Mat2 → EdgeLabel
  | genInv : Bool → EdgeLabel

structure OEdge where
  ty : EdgeType
  src : QuestionId
  dst : QuestionId
  label : EdgeLabel

/-- `Und(e⃗) = (edgeType, {v_a, v_b})`, kept as the recorded pair. -/
structure UEdge where
  ty : EdgeType
  a : QuestionId
  b : QuestionId

def und (e : OEdge) : UEdge := ⟨e.ty, e.src, e.dst⟩

/-- Equality of undirected keys: same type, same endpoint set. -/
def UEdge.same (e e' : UEdge) : Prop :=
  e.ty = e'.ty ∧ ((e.a = e'.a ∧ e.b = e'.b) ∨ (e.a = e'.b ∧ e.b = e'.a))

instance (e e' : UEdge) : Decidable (e.same e') := by
  unfold UEdge.same; exact inferInstance

theorem UEdge.same_symm {e e' : UEdge} (hs : e.same e') : e'.same e := by
  obtain ⟨ht, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := hs
  · exact ⟨ht.symm, Or.inl ⟨ha.symm, hb.symm⟩⟩
  · exact ⟨ht.symm, Or.inr ⟨hb.symm, ha.symm⟩⟩

/-- A raw ancestry edge is never identified with a received shortcut. -/
theorem raw_not_received (a b a' b' : QuestionId) :
    ¬ (UEdge.same ⟨.raw, a, b⟩ ⟨.received, a', b'⟩) := fun hs => nomatch hs.1

/-- **Definition 23.1.** `ι_f = (𝗾, τ, j+1, v₀, v₁, v₂)`, ordered: parent,
    committed child, refused child. -/
structure FaceId where
  q : ℕ
  tau : ℕ
  event : ℕ
  v0 : QuestionId
  v1 : QuestionId
  v2 : QuestionId
deriving DecidableEq

def faceIdOf (i : EligInput) : FaceId := ⟨i.x.qid, i.x.cycle, i.j + 1, i.x, i.idS, i.idBar⟩

/-- `e⃗₀ = (raw, v₀, v₁; s)`, `e⃗₁ = (received, v₁, v₂; A_s)`, `e⃗₂ = (raw, v₂, v₀; s̄⁻¹)`. -/
def edge0 (i : EligInput) : OEdge := ⟨.raw, i.x, i.idS, .gen i.s⟩
def edge1 (i : EligInput) : OEdge := ⟨.received, i.idS, i.idBar, .mat (A i.s)⟩
def edge2 (i : EligInput) : OEdge := ⟨.raw, i.idBar, i.x, .genInv (!i.s)⟩

/-! ## Proposition 23.2 — Face identifiers are injective on attached packets -/

/-- An input is stably keyed when its two children are the parent's children
    by the incoming hand and its opposite. -/
def WellKeyed (i : EligInput) : Prop := i.idS = i.x.child i.s ∧ i.idBar = i.x.child (!i.s)

/-- The incoming hand is recovered from the child identifier. -/
theorem child_hand_inj (x : QuestionId) (s s' : Bool) (he : x.child s = x.child s') : s = s' := by
  have hr := congrArg QuestionId.rel he
  simp only [QuestionId.child] at hr
  have := List.append_cancel_left hr
  exact List.head_eq_of_cons_eq this

/-- **Proposition 23.2.** On a stably keyed family — one packet per occurrence
    key `(j, x, s)` — two attached packets have the same face identifier if and
    only if they are the same packet. -/
theorem faceId_injective (key : ℕ → QuestionId → Bool → FElig Aux Cert RawAux EvalAux h)
    (hkey : ∀ j x s, (key j x s).input.j = j ∧ (key j x s).input.x = x ∧
      (key j x s).input.s = s ∧ WellKeyed (key j x s).input)
    (j j' : ℕ) (x x' : QuestionId) (s s' : Bool) :
    faceIdOf (key j x s).input = faceIdOf (key j' x' s').input ↔ key j x s = key j' x' s' := by
  constructor
  · intro he
    obtain ⟨hj, hx, hs, hk, -⟩ := hkey j x s
    obtain ⟨hj', hx', hs', hk', -⟩ := hkey j' x' s'
    simp only [faceIdOf, FaceId.mk.injEq] at he
    obtain ⟨-, -, hev, hv0, hv1, -⟩ := he
    have ejj : j = j' := by rw [← hj, ← hj']; omega
    have exx : x = x' := by rw [← hx, ← hx']; exact hv0
    subst ejj; subst exx
    rw [hk, hk', hs, hs', hx, hx'] at hv1
    rw [child_hand_inj x s s' hv1]
  · intro he; rw [he]

/-! ## Definition 23.3 — Complete incidence-bearing face record -/

/-- The tagged holonomy entry: a matrix or an exact lift-status tag. -/
inductive HolEntry where
  | mat : Mat2 → HolEntry
  | tag : LiftStatus → HolEntry

/-- `Hol_SL(f)`: `I` for determined-0, `−I` for determined-1, the tag otherwise. -/
def holSL : LiftStatus → HolEntry
  | .determined false => .mat 1
  | .determined true => .mat (matNeg 1)
  | st => .tag st

theorem holSL_tag (st : LiftStatus) (hst : ∀ b, st ≠ .determined b) : holSL st = .tag st := by
  cases st with
  | notEvaluated => rfl
  | unresolvedNone => rfl
  | unresolvedMultiple => rfl
  | determined b => exact absurd rfl (hst b)

/-- The only release status the section authorizes. -/
inductive ReleaseStatus where
  | retainedAtEntry
deriving DecidableEq

/-- **Definition 23.3.** The complete record. `𝗾, τ, j+1, v₀, v₁, v₂` are in `id`;
    `s`, `CF(x;s)`, `FElig`, `SibRec`, `j_s`, `Lift_sib` and the cycle
    certificate are in `packet`, retained whole. -/
structure FaceRec (Aux Cert RawAux EvalAux : Type) (h : ℕ) (Prov Renew : Type) where
  id : FaceId
  packet : FElig Aux Cert RawAux EvalAux h
  e0 : OEdge
  e1 : OEdge
  e2 : OEdge
  hol : HolEntry
  target : QuestionId
  prov : Prov
  renew : List Renew
  release : ReleaseStatus

/-- The record at entry: `RenewTrans(f) = ()`, `releaseStatus(f) = retained-at-entry`. -/
def entryRec (p : FElig Aux Cert RawAux EvalAux h) (target : QuestionId) (prov : Prov) :
    FaceRec Aux Cert RawAux EvalAux h Prov Renew where
  id := faceIdOf p.input
  packet := p
  e0 := edge0 p.input
  e1 := edge1 p.input
  e2 := edge2 p.input
  hol := holSL p.lift
  target := target
  prov := prov
  renew := []
  release := .retainedAtEntry

theorem entryRec_at_entry (p : FElig Aux Cert RawAux EvalAux h) (t : QuestionId) (pv : Prov) :
    (entryRec (Renew := Renew) p t pv).renew = [] ∧
    (entryRec (Renew := Renew) p t pv).release = .retainedAtEntry ∧
    (entryRec (Renew := Renew) p t pv).hol = holSL p.lift := ⟨rfl, rfl, rfl⟩

/-! ## Definition 23.4 — Face ledger and incidence maps -/

def V (r : FaceRec Aux Cert RawAux EvalAux h Prov Renew) : List QuestionId := [r.id.v0, r.id.v1, r.id.v2]

def E (r : FaceRec Aux Cert RawAux EvalAux h Prov Renew) : List UEdge := [und r.e0, und r.e1, und r.e2]

/-- `𝖥_{τ+1}`: one entry record per attached face. No quotient of identifiers. -/
def ledgerOf (fs : List (ReceivedFace Aux Cert RawAux EvalAux h)) (target : QuestionId) (prov : Prov) :
    List (FaceRec Aux Cert RawAux EvalAux h Prov Renew) :=
  fs.map (fun f => entryRec f.packet target prov)

/-- `Inc_V(v) = {ι_f : v ∈ V(f)}`. -/
def incV (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) (v : QuestionId) : List FaceId :=
  (L.filter (fun r => decide (v ∈ V r))).map (·.id)

/-- `Inc_E(e) = {ι_f : e ∈ E(f)}`, membership up to `Und`. -/
def incE (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) (e : UEdge) : List FaceId :=
  (L.filter (fun r => (E r).any (fun e' => decide (e.same e')))).map (·.id)

/-- `Bd(ι_f) = (e⃗₀, e⃗₁, e⃗₂)`. -/
def bd (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) (fid : FaceId) : Option (OEdge × OEdge × OEdge) :=
  (L.find? (fun r => decide (r.id = fid))).map (fun r => (r.e0, r.e1, r.e2))

/-! ## Definition 23.5 — Incidence-recording map -/

/-- **Definition 23.5.** `RecordFace(S_{τ+1}, 𝔏) = S_{τ+1}` with `H ∥ (ι_target, 𝔏)`:
    the operative components untouched, the ledger appended once. -/
def recordFace (st : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (target : QuestionId) (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) :
    RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) :=
  faceAppend st target L

/-! ## Theorem 23.6 — Determinism and typedness of incidence recording -/

/-- The occurrence key of a received face. -/
def occKey (f : ReceivedFace Aux Cert RawAux EvalAux h) : ℕ × QuestionId × Bool :=
  (f.packet.input.j, f.packet.input.x, f.packet.input.s)

def idOfKey (k : ℕ × QuestionId × Bool) : FaceId :=
  ⟨k.2.1.qid, k.2.1.cycle, k.1 + 1, k.2.1, k.2.1.child k.2.2, k.2.1.child (!k.2.2)⟩

/-- `List.Nodup.map`, choice-free and without Mathlib. -/
theorem nodup_map_inj {α β : Type} (f : α → β) (hf : Function.Injective f) :
    ∀ l : List α, l.Nodup → (l.map f).Nodup
  | [], _ => List.Pairwise.nil
  | a :: t, hnd => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ha ?_, nodup_map_inj f hf t ht⟩
    obtain ⟨z, hz, hzf⟩ := List.mem_map.mp hm
    rwa [← hf hzf]

theorem idOfKey_injective : Function.Injective idOfKey := by
  rintro ⟨j, x, s⟩ ⟨j', x', s'⟩ he
  simp only [idOfKey, FaceId.mk.injEq] at he
  obtain ⟨-, -, hev, hv0, hv1, -⟩ := he
  have ejj : j = j' := by omega
  subst ejj; subst hv0
  rw [child_hand_inj x s s' hv1]

/-- **Theorem 23.6.** On a stably keyed attached family with distinct occurrence
    keys, the ledger's face keys are distinct, and recording is lossless: the
    operative state is unchanged and the ledger is appended exactly once. -/
theorem record_deterministic_typed (fs : List (ReceivedFace Aux Cert RawAux EvalAux h))
    (hwk : ∀ f ∈ fs, WellKeyed f.packet.input) (hnd : (fs.map occKey).Nodup)
    (st : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (target : QuestionId) (prov : Prov) :
    ((ledgerOf (Renew := Renew) fs target prov).map (·.id)).Nodup ∧
    Lossless st (recordFace st target (ledgerOf fs target prov)) target target (ledgerOf fs target prov) := by
  refine ⟨?_, (faceAppend_lossless_iff _ _ _ _).mpr rfl⟩
  have hmap : (ledgerOf (Prov := Prov) (Renew := Renew) fs target prov).map (·.id) = (fs.map occKey).map idOfKey := by
    rw [ledgerOf, List.map_map, List.map_map]
    apply List.map_congr_left
    intro f hf
    obtain ⟨hs, hb⟩ := hwk f hf
    simp only [Function.comp, entryRec, faceIdOf, occKey, idOfKey, hs, hb]
  rw [hmap]
  exact nodup_map_inj idOfKey idOfKey_injective _ hnd

/-! ## Theorem 23.7 — Face recording preserves every exact preimage -/

/-- **Theorem 23.7.** Parent and both children; both raw edges; the oriented
    received shortcut and its inverse orientation; the admission certificates
    (in the causal pair); the cycle certificate with its terminal report; the
    lift status unreplaced; and, after recording, the whole prior history. -/
theorem face_preimages (p : FElig Aux Cert RawAux EvalAux h) (hwk : WellKeyed p.input)
    (t : QuestionId) (pv : Prov)
    (st : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) :
    let r := entryRec (Renew := Renew) p t pv
    (r.id.v0 = p.input.x ∧ r.id.v1 = p.input.x.child p.input.s ∧ r.id.v2 = p.input.x.child (!p.input.s)) ∧
    (r.e0.ty = .raw ∧ r.e0.src = p.input.x ∧ r.e2.ty = .raw ∧ r.e2.dst = p.input.x) ∧
    (r.e1.ty = .received ∧ inv2 (A p.input.s) = A (!p.input.s)) ∧
    r.packet.shortcut = p.shortcut ∧ r.packet.cycle = p.cycle ∧ r.packet.lift = p.lift ∧
    st.hist <+: (recordFace st t L).hist := by
  intro r
  obtain ⟨hs, hb⟩ := hwk
  exact ⟨⟨rfl, hs, hb⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, (side_exchange_shortcut_matrix p.input.s).2.symm⟩,
    rfl, rfl, rfl, List.prefix_append _ _⟩

/-! ## Theorem 23.8 — Every edge of a one-lineage face family has incidence one

    Face at event `j+1` of the lineage ending at `i`: parent `x_j`, committed
    child `x_{j+1}`, archived counter-sibling `x_{j+1}^⊥`. -/

/-- `x_n`, the lineage entry at depth `n`. -/
def linV (i : QuestionId) (n : ℕ) : QuestionId := { i with rel := i.rel.take n }

theorem getD_of_lt (l : List Bool) (j : ℕ) (hj : j < l.length) (d : Bool) : l.getD j d = l[j] := by
  unfold List.getD; rw [List.getElem?_eq_getElem hj]; rfl

def lineFaceV (i : QuestionId) (j : ℕ) : List QuestionId :=
  [linV i j, linV i (j + 1), counterSibling i j]

def lineFaceE (i : QuestionId) (j : ℕ) : List UEdge :=
  [⟨.raw, linV i j, linV i (j + 1)⟩, ⟨.received, linV i (j + 1), counterSibling i j⟩,
    ⟨.raw, counterSibling i j, linV i j⟩]

/-- The lineage face is exactly the entry record's face on a stably keyed packet
    whose parent is `x_j` and whose hand is the lineage's next letter. -/
theorem entry_is_lineFace (p : FElig Aux Cert RawAux EvalAux h) (hwk : WellKeyed p.input)
    (i : QuestionId) (j : ℕ) (hj : j < i.rel.length)
    (hx : p.input.x = linV i j) (hs : p.input.s = i.rel.getD j false) (t : QuestionId) (pv : Prov) :
    V (entryRec (Renew := Renew) p t pv) = lineFaceV i j := by
  obtain ⟨hS, hB⟩ := hwk
  simp only [V, entryRec, faceIdOf, lineFaceV, hS, hB, hx, hs, counterSibling_eq]
  refine congrArg (fun v => linV i j :: v :: _) ?_
  simp only [linV, QuestionId.child, QuestionId.mk.injEq, true_and]
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, getD_of_lt _ j hj false]

theorem rel_len_linV (i : QuestionId) (n : ℕ) : (linV i n).rel.length = min n i.rel.length := by
  simp only [linV, List.length_take]

theorem rel_len_cs (i : QuestionId) (j : ℕ) : (counterSibling i j).rel.length = min j i.rel.length + 1 := by
  simp only [counterSibling, List.length_append, List.length_take, List.length_singleton]

/-- The committed child is not its counter-sibling. -/
theorem linV_ne_cs (i : QuestionId) (j : ℕ) (hj : j < i.rel.length) : linV i (j + 1) ≠ counterSibling i j := by
  intro he
  have hr := congrArg QuestionId.rel he
  simp only [linV, counterSibling] at hr
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, getD_of_lt _ j hj false] at hr
  have h1 := List.head_eq_of_cons_eq (List.append_cancel_left hr)
  cases hb : i.rel[j] <;> rw [hb] at h1 <;> exact nomatch h1

theorem lenEq {a b : QuestionId} (he : a = b) : a.rel.length = b.rel.length := by rw [he]

/-- **Theorem 23.8, vertices.** For events `j < j'` on one lineage, the faces
    share a vertex exactly when `j' = j + 1`, and then only `x_{j+1}`. -/
theorem lineage_vertices (i : QuestionId) (j j' : ℕ) (hjj : j < j') (hj' : j' < i.rel.length) (v : QuestionId) :
    (v ∈ lineFaceV i j ∧ v ∈ lineFaceV i j') ↔ (j' = j + 1 ∧ v = linV i (j + 1)) := by
  have l0 := rel_len_linV i j
  have l1 := rel_len_linV i (j + 1)
  have l2 := rel_len_cs i j
  have m0 := rel_len_linV i j'
  have m1 := rel_len_linV i (j' + 1)
  have m2 := rel_len_cs i j'
  constructor
  · rintro ⟨ha, hb⟩
    simp only [lineFaceV, List.mem_cons, List.mem_nil_iff, or_false] at ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      have hl := lenEq (ha.symm.trans hb) <;> try (exfalso; omega)
    · exact ⟨Decidable.byContradiction fun hne => by omega, ha⟩
    · have ej : j' = j + 1 := Decidable.byContradiction fun hne => by omega
      subst ej
      exact absurd (ha.symm.trans hb).symm (linV_ne_cs i j (by omega))
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩ <;> simp only [lineFaceV, List.mem_cons, List.mem_nil_iff, or_false, true_or, or_true]

theorem mem_lineFaceV_of_edge (i : QuestionId) (j : ℕ) (e : UEdge) (he : e ∈ lineFaceE i j) :
    e.a ∈ lineFaceV i j ∧ e.b ∈ lineFaceV i j := by
  simp only [lineFaceE, lineFaceV, List.mem_cons, List.mem_nil_iff, or_false] at he ⊢
  rcases he with rfl | rfl | rfl <;> simp

/-- Within one face the two endpoints of every edge differ. -/
theorem edge_endpoints_ne (i : QuestionId) (j : ℕ) (hj : j < i.rel.length) (e : UEdge) (he : e ∈ lineFaceE i j) :
    e.a ≠ e.b := by
  have l0 := rel_len_linV i j
  have l1 := rel_len_linV i (j + 1)
  have l2 := rel_len_cs i j
  simp only [lineFaceE, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · intro hab; have := lenEq (show linV i j = linV i (j + 1) from hab); omega
  · exact linV_ne_cs i j hj
  · intro hab; have := lenEq (show counterSibling i j = linV i j from hab); omega

/-- **Theorem 23.8, edges.** Distinct faces of one lineage share no edge. -/
theorem lineage_no_shared_edge (i : QuestionId) (j j' : ℕ) (hjj : j < j') (hj' : j' < i.rel.length)
    (e e' : UEdge) (he : e ∈ lineFaceE i j) (he' : e' ∈ lineFaceE i j') : ¬ e.same e' := by
  intro hs
  obtain ⟨ha, hb⟩ := mem_lineFaceV_of_edge i j e he
  obtain ⟨ha', hb'⟩ := mem_lineFaceV_of_edge i j' e' he'
  have ne := edge_endpoints_ne i j (by omega) e he
  obtain ⟨-, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := hs
  · have va := ((lineage_vertices i j j' hjj hj' e.a).mp ⟨ha, h1 ▸ ha'⟩).2
    have vb := ((lineage_vertices i j j' hjj hj' e.b).mp ⟨hb, h2 ▸ hb'⟩).2
    exact ne (va.trans vb.symm)
  · have va := ((lineage_vertices i j j' hjj hj' e.a).mp ⟨ha, h1 ▸ hb'⟩).2
    have vb := ((lineage_vertices i j j' hjj hj' e.b).mp ⟨hb, h2 ▸ ha'⟩).2
    exact ne (va.trans vb.symm)

set_option linter.unusedDecidableInType false in
theorem filter_eq_singleton {α : Type} [DecidableEq α]
    (p : α → Bool) (a : α) :
    ∀ l : List α, l.Nodup → a ∈ l → p a = true → (∀ y ∈ l, p y = true → y = a) → l.filter p = [a]
  | [], _, ha, _, _ => nomatch ha
  | b :: t, hnd, ha, hpa, hu => by
    have hbt : b ∉ t := (List.nodup_cons.mp hnd).1
    by_cases hba : b = a
    · subst hba
      rw [List.filter_cons_of_pos hpa]
      refine congrArg (b :: ·) (filter_eq_nil_of p t fun y hy => ?_)
      cases hpy : p y
      · rfl
      · exact absurd (hu y (List.Mem.tail b hy) hpy ▸ hy) hbt
    · have hpb : p b = false := by
        cases hpb : p b
        · rfl
        · exact absurd (hu b (List.Mem.head t) hpb) hba
      rw [List.filter_cons_of_neg (by rw [hpb]; exact Bool.false_ne_true)]
      have hat : a ∈ t := by
        cases ha with
        | head => exact absurd rfl hba
        | tail _ h' => exact h'
      exact filter_eq_singleton p a t (List.nodup_cons.mp hnd).2 hat hpa (fun y hy => hu y (List.Mem.tail b hy))

/-- `e ∈ E(f)` up to `Und`, over a family of lineage events. -/
def lineIncE (i : QuestionId) (evs : List ℕ) (e : UEdge) : List ℕ :=
  evs.filter (fun j => (lineFaceE i j).any (fun e' => decide (e.same e')))

theorem same_refl (e : UEdge) : e.same e := ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- **Theorem 23.8, incidence one.** For any attached subfamily of one lineage's
    events (it may omit events), every edge of a face in it is incident to that
    face alone: `|Inc_E(e)| = 1`. So the family is never a closed two-manifold,
    which needs two incident faces at every edge. -/
theorem lineage_incidence_one (i : QuestionId) (evs : List ℕ) (hnd : evs.Nodup)
    (hlt : ∀ j ∈ evs, j < i.rel.length) (j : ℕ) (hj : j ∈ evs) (e : UEdge) (he : e ∈ lineFaceE i j) :
    lineIncE i evs e = [j] := by
  apply filter_eq_singleton _ j evs hnd hj
  · exact List.any_eq_true.mpr ⟨e, he, decide_eq_true (same_refl e)⟩
  · intro y hy hpy
    obtain ⟨e', he', hs⟩ := List.any_eq_true.mp hpy
    have hs := of_decide_eq_true hs
    rcases Nat.lt_trichotomy j y with hlt' | heq | hgt
    · exact absurd hs (lineage_no_shared_edge i j y hlt' (hlt y hy) e e' he he')
    · exact heq.symm
    · exact absurd (UEdge.same_symm hs) (lineage_no_shared_edge i y j hgt (hlt j hj) e' e he' he)

theorem lineage_not_closed (i : QuestionId) (evs : List ℕ) (hnd : evs.Nodup)
    (hlt : ∀ j ∈ evs, j < i.rel.length) :
    ∀ j ∈ evs, ∀ e ∈ lineFaceE i j, (lineIncE i evs e).length = 1 :=
  fun j hj e he => by rw [lineage_incidence_one i evs hnd hlt j hj e he]; rfl

/-! ## Corollary 23.9 — Locally closed faces keep one-lineage edge incidence at one -/

/-- **Corollary 23.9.** Every face is projectively closed on either sheet
    (Proposition 22.2) and still every edge of the one-lineage family has
    incidence one (Theorem 23.8): local closure is not the missing second
    incidence. -/
theorem holonomy_not_incidence (i : QuestionId) (evs : List ℕ) (hnd : evs.Nodup)
    (hlt : ∀ j ∈ evs, j < i.rel.length) :
    (∀ s ℓ : Bool, projClass (Word.gen s * liftedA s ℓ * inv2 (Word.gen (!s))) = projClass 1) ∧
    (∀ j ∈ evs, ∀ e ∈ lineFaceE i j, (lineIncE i evs e).length = 1) :=
  ⟨boundary_projectively_closed, lineage_not_closed i evs hnd hlt⟩

/-! ## Proposition 23.10 — Covariance of the incidence ledger

    Incidence reads only the face identifier and the boundary endpoints; the
    packet itself is transported by Theorem 22.11. -/

def relabelFaceId (σ : QuestionId → QuestionId) (f : FaceId) : FaceId :=
  { f with v0 := σ f.v0, v1 := σ f.v1, v2 := σ f.v2 }

def relabelEdge (σ : QuestionId → QuestionId) (e : OEdge) : OEdge := { e with src := σ e.src, dst := σ e.dst }

def FaceRec.relabel (σ : QuestionId → QuestionId) (r : FaceRec Aux Cert RawAux EvalAux h Prov Renew) :
    FaceRec Aux Cert RawAux EvalAux h Prov Renew :=
  { r with id := relabelFaceId σ r.id, e0 := relabelEdge σ r.e0, e1 := relabelEdge σ r.e1, e2 := relabelEdge σ r.e2 }

theorem mem_map_inj (σ : QuestionId → QuestionId) (hσ : Function.Injective σ) (v : QuestionId) (l : List QuestionId) :
    σ v ∈ l.map σ ↔ v ∈ l := by
  constructor
  · intro hm; obtain ⟨z, hz, hzy⟩ := List.mem_map.mp hm; rwa [← hσ hzy]
  · exact List.mem_map_of_mem

theorem same_relabel (σ : QuestionId → QuestionId) (hσ : Function.Injective σ) (e e' : UEdge) :
    UEdge.same ⟨e.ty, σ e.a, σ e.b⟩ ⟨e'.ty, σ e'.a, σ e'.b⟩ ↔ e.same e' := by
  simp only [UEdge.same]
  constructor
  · rintro ⟨ht, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · exact ⟨ht, Or.inl ⟨hσ h1, hσ h2⟩⟩
    · exact ⟨ht, Or.inr ⟨hσ h1, hσ h2⟩⟩
  · rintro ⟨ht, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · exact ⟨ht, Or.inl ⟨congrArg σ h1, congrArg σ h2⟩⟩
    · exact ⟨ht, Or.inr ⟨congrArg σ h1, congrArg σ h2⟩⟩

/-- **Proposition 23.10.** Under an injective relabeling of stable identifiers
    (common-prefix transport and side exchange both are one), vertex and edge
    incidence of the transported ledger is the transported incidence, so every
    incidence cardinality is preserved. Side exchange also swaps phases 1 and 3
    (`side_exchange_phases_and_holonomy`). -/
theorem incidence_covariant (σ : QuestionId → QuestionId) (hσ : Function.Injective σ)
    (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) (v : QuestionId) (e : UEdge) :
    incV (L.map (FaceRec.relabel σ)) (σ v) = (incV L v).map (relabelFaceId σ) ∧
    incE (L.map (FaceRec.relabel σ)) ⟨e.ty, σ e.a, σ e.b⟩ = (incE L e).map (relabelFaceId σ) := by
  constructor
  · simp only [incV, List.filter_map, List.map_map]
    congr 1
    · apply List.filter_congr
      intro r _
      simp only [Function.comp, V, FaceRec.relabel, relabelFaceId]
      exact dec_congr (mem_map_inj σ hσ v [r.id.v0, r.id.v1, r.id.v2])
  · simp only [incE, List.filter_map, List.map_map]
    congr 1
    · apply List.filter_congr
      intro r _
      simp only [Function.comp, E, FaceRec.relabel, und, relabelEdge, List.any_cons, List.any_nil, Bool.or_false]
      rw [dec_congr (same_relabel σ hσ e ⟨r.e0.ty, r.e0.src, r.e0.dst⟩),
        dec_congr (same_relabel σ hσ e ⟨r.e1.ty, r.e1.src, r.e1.dst⟩),
        dec_congr (same_relabel σ hσ e ⟨r.e2.ty, r.e2.src, r.e2.dst⟩)]

theorem incidence_cardinality_covariant (σ : QuestionId → QuestionId) (hσ : Function.Injective σ)
    (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)) (v : QuestionId) (e : UEdge) :
    (incV (L.map (FaceRec.relabel σ)) (σ v)).length = (incV L v).length ∧
    (incE (L.map (FaceRec.relabel σ)) ⟨e.ty, σ e.a, σ e.b⟩).length = (incE L e).length := by
  obtain ⟨h1, h2⟩ := incidence_covariant σ hσ L v e
  rw [h1, h2, List.length_map, List.length_map]
  exact ⟨rfl, rfl⟩

/-! ## Boundary Statement 23.11 -/

/-- **Boundary Statement 23.11.** Eligibility, attachment (II.2), recording: the
    operative state is untouched, the history gains exactly the ledger, every
    recorded face was eligible, and no face has a renewal transport or a release
    beyond retention at entry. -/
theorem cycle_exports_face_ledger (ps : List (FElig Aux Cert RawAux EvalAux h))
    (st : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))) (target : QuestionId) (prov : Prov) :
    let L := ledgerOf (Renew := Renew) (receivedFaces ps) target prov
    (recordFace st target L).op = st.op ∧
    (recordFace st target L).hist = st.hist ++ [(target, L)] ∧
    ∀ r ∈ L, r.packet.elig.all = true ∧ r.renew = [] ∧ r.release = .retainedAtEntry := by
  intro L
  refine ⟨rfl, rfl, ?_⟩
  intro r hr
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf
  exact ⟨(List.mem_filter.mp hq).2, rfl, rfl⟩

#print axioms raw_not_received
#print axioms child_hand_inj
#print axioms faceId_injective
#print axioms holSL_tag
#print axioms entryRec_at_entry
#print axioms record_deterministic_typed
#print axioms face_preimages
#print axioms entry_is_lineFace
#print axioms linV_ne_cs
#print axioms lineage_vertices
#print axioms lineage_no_shared_edge
#print axioms lineage_incidence_one
#print axioms lineage_not_closed
#print axioms holonomy_not_incidence
#print axioms incidence_covariant
#print axioms incidence_cardinality_covariant
#print axioms cycle_exports_face_ledger

end Incidence
end Two
end RatioSpace
