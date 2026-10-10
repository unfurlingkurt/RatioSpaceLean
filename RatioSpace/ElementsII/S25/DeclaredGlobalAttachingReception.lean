/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S25.Shell
import RatioSpace.ElementsII.S33.Export
/-!
  Gap G2-31 · Elements II Definition 25.4, declared global attaching reception:
  "The identity reception on stable occurrence keys is always a valid prequotient case."

  `gid_admissible` (`Two/Shell.lean`) proves `Γ_id` admissible for any face ledger given two
  hypotheses, distinct face keys and triadic nondegeneracy of every record, and
  `gid_lineage_admissible` discharges both for a one-lineage ledger. Nothing discharged them
  for an archival or active family drawn from several lineages or cycles.

  This file discharges both from the book's own hypothesis, stable (distinct) occurrence keys,
  for any family of faces recorded by Definition 23.5 from well-keyed inputs. No lineage is
  named:
  * triadic nondegeneracy holds for every well-keyed recorded face on its own (its vertices are
    `x`, the `s`-child and the `s̄`-child of `x`; its three undirected edges have three different
    endpoint pairs), so composition across lineages is pointwise;
  * distinct occurrence keys give distinct face keys through Theorem 23.6's `idOfKey_injective`,
    across cycles as well, because the occurrence key carries the cycle: a family assembled from
    several cycles has distinct keys as soon as each cycle's part has and the cycles differ.
  The archival family of an export (`Export.ofState`: every ledger the state recorded), its
  active family (`def_33_1`'s sublist), and Theorem 23.6's own `ledgerOf` are covered, under the
  recording invariant that every ledger in the history came from a Definition 23.5 call
  (`HistOfLedgers`, preserved by every such call from an empty history).

  What the book guarantees and what it leaves to discipline. Definition 23.5: "Within one
  application, the ledger is inserted once and contains each stable face key exactly once."
  That is per application; across applications the book does not state that keys never repeat
  (Theorem 25.3: released records stay in the archival ledger). So distinct occurrence keys over
  the whole recorded history is the recording discipline of Theorem 23.6 carried across
  applications, stated here as the hypothesis it is; the n-fold cross-cycle theorem reduces it
  to per-application distinctness plus distinct cycle tags.
  No existing declaration is changed.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_31

open RatioSpace.Two RatioSpace.Two.Face RatioSpace.Two.Incidence RatioSpace.Two.Shell
  RatioSpace.Two.Advance

variable {Aux Cert RawAux EvalAux Prov Renew : Type} {h : ℕ}

/-! ## Recorded faces: what Definition 23.5 writes -/

/-- A face record as Definition 23.5's `entryRec` writes it from a well-keyed input: its key is
    `faceIdOf` its input and its three edges are the input's `e⃗₀, e⃗₁, e⃗₂`. Every record produced
    by `ledgerOf` satisfies this (`entryRec_keyed`); so does every `LineShaped` record
    (`keyed_of_lineShaped`). -/
structure Keyed (r : FaceRec Aux Cert RawAux EvalAux h Prov Renew) : Prop where
  wk : WellKeyed r.packet.input
  hid : r.id = faceIdOf r.packet.input
  he0 : r.e0 = edge0 r.packet.input
  he1 : r.e1 = edge1 r.packet.input
  he2 : r.e2 = edge2 r.packet.input

theorem entryRec_keyed (p : FElig Aux Cert RawAux EvalAux h) (target : QuestionId) (prov : Prov)
    (hwk : WellKeyed p.input) : Keyed (entryRec (Renew := Renew) p target prov) :=
  ⟨hwk, rfl, rfl, rfl, rfl⟩

theorem ledgerOf_keyed (fs : List (ReceivedFace Aux Cert RawAux EvalAux h)) (target : QuestionId)
    (prov : Prov) (hwk : ∀ f ∈ fs, WellKeyed f.packet.input) :
    ∀ r ∈ ledgerOf (Renew := Renew) fs target prov, Keyed r := by
  intro r hr
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hr
  exact entryRec_keyed _ _ _ (hwk f hf)

theorem keyed_of_lineShaped {i : QuestionId} {r : FaceRec Aux Cert RawAux EvalAux h Prov Renew}
    (hL : LineShaped i r) : Keyed r :=
  ⟨hL.wk, hL.hid, hL.he0, hL.he1, hL.he2⟩

/-- The occurrence key of a face record, `(j, x, s)`: Theorem 23.6's `occKey` read off the
    record instead of the received face. -/
def occKeyRec (r : FaceRec Aux Cert RawAux EvalAux h Prov Renew) : ℕ × QuestionId × Bool :=
  (r.packet.input.j, r.packet.input.x, r.packet.input.s)

theorem occKeyRec_entryRec (p : FElig Aux Cert RawAux EvalAux h) (target : QuestionId)
    (prov : Prov) :
    occKeyRec (entryRec (Renew := Renew) p target prov) = (p.input.j, p.input.x, p.input.s) := rfl

/-! ## Distinct occurrence keys give distinct face keys, across lineages and cycles -/

/-- A keyed record's face key is `idOfKey` of its occurrence key. -/
theorem keyed_id_eq {r : FaceRec Aux Cert RawAux EvalAux h Prov Renew} (hk : Keyed r) :
    r.id = idOfKey (occKeyRec r) := by
  rw [hk.hid]
  unfold faceIdOf idOfKey occKeyRec
  rw [hk.wk.1, hk.wk.2]

/-- **Condition 4's hypothesis discharged** (boundary compatibility needs distinct face keys;
    condition 5, face-key separation, is trivial under `Γ_id`). Distinct occurrence keys on a
    keyed family give distinct face keys, whatever lineages or cycles the records come from. -/
theorem ids_nodup_of_occKeys (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hk : ∀ r ∈ L, Keyed r) (hnd : (L.map occKeyRec).Nodup) : (L.map (·.id)).Nodup := by
  have hmap : L.map (·.id) = (L.map occKeyRec).map idOfKey := by
    rw [List.map_map]
    exact List.map_congr_left fun r hr => keyed_id_eq (hk r hr)
  rw [hmap]
  exact nodup_map_inj idOfKey idOfKey_injective _ hnd

/-- The occurrence key carries the cycle. -/
theorem occKeyRec_cycle (r : FaceRec Aux Cert RawAux EvalAux h Prov Renew) :
    (occKeyRec r).2.1.cycle = r.packet.input.x.cycle := rfl

theorem nodup_append_of_disjoint {β : Type} :
    ∀ (l₁ l₂ : List β), l₁.Nodup → l₂.Nodup → (∀ a ∈ l₁, a ∉ l₂) → (l₁ ++ l₂).Nodup
  | [], l₂, _, h2, _ => h2
  | a :: t, l₂, h1, h2, hd => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp h1
    rw [List.cons_append, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_append_of_disjoint t l₂ ht h2
      (fun b hb => hd b (List.mem_cons_of_mem a hb))⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact ha hm
    · exact hd a (by simp) hm

/-- **Across cycles.** Two families from different cycles, each with distinct occurrence keys,
    have distinct occurrence keys together: no key of one cycle can equal a key of another. -/
theorem occKeys_nodup_of_cycles (L₁ L₂ : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (c₁ c₂ : ℕ) (h1 : ∀ r ∈ L₁, r.packet.input.x.cycle = c₁)
    (h2 : ∀ r ∈ L₂, r.packet.input.x.cycle = c₂) (hne : c₁ ≠ c₂)
    (n1 : (L₁.map occKeyRec).Nodup) (n2 : (L₂.map occKeyRec).Nodup) :
    ((L₁ ++ L₂).map occKeyRec).Nodup := by
  rw [List.map_append]
  refine nodup_append_of_disjoint _ _ n1 n2 fun k hk hk' => ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
  obtain ⟨r', hr', he⟩ := List.mem_map.mp hk'
  have hc : (occKeyRec r').2.1.cycle = (occKeyRec r).2.1.cycle := by rw [he]
  rw [occKeyRec_cycle, occKeyRec_cycle, h1 r hr, h2 r' hr'] at hc
  exact hne hc.symm

/-! ## Triadic nondegeneracy holds for every keyed record on its own -/

theorem nodup_three {β : Type} (a b c : β) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    [a, b, c].Nodup :=
  List.nodup_cons.mpr ⟨by simp [hab, hac], List.nodup_cons.mpr ⟨by simp [hbc], List.nodup_singleton c⟩⟩

/-- A question is not its own child: the child's relative word is one longer. -/
theorem ne_child (x : QuestionId) (g : Bool) : x ≠ x.child g :=
  child_ne_of_length_le rfl (Nat.le_refl _)

/-- The two children of one question differ: `child_hand_inj`. -/
theorem child_ne_child (x : QuestionId) (s : Bool) : x.child s ≠ x.child (!s) := fun he => by
  have := child_hand_inj x s (!s) he
  cases s <;> exact absurd this (by decide)

/-- **Condition 3's hypothesis discharged**, one record at a time: the three vertices of a
    keyed face are `x`, `x·s` and `x·s̄`, pairwise distinct; its three undirected edges are
    `raw{x, x·s}`, `received{x·s, x·s̄}` and `raw{x·s̄, x}`, whose canonical keys are pairwise
    distinct (types differ, or the endpoint pairs differ). -/
theorem keyed_nondegenerate {r : FaceRec Aux Cert RawAux EvalAux h Prov Renew} (hk : Keyed r) :
    [r.id.v0, r.id.v1, r.id.v2].Nodup ∧
    [canon (und r.e0), canon (und r.e1), canon (und r.e2)].Nodup := by
  obtain ⟨⟨hS, hB⟩, hid, he0, he1, he2⟩ := hk
  set x := r.packet.input.x with hx
  set s := r.packet.input.s with hs
  have v0 : r.id.v0 = x := by rw [hid]; rfl
  have v1 : r.id.v1 = x.child s := by rw [hid]; exact hS
  have v2 : r.id.v2 = x.child (!s) := by rw [hid]; exact hB
  have u0 : und r.e0 = ⟨.raw, x, x.child s⟩ := by rw [he0]; unfold und edge0; rw [hS]
  have u1 : und r.e1 = ⟨.received, x.child s, x.child (!s)⟩ := by
    rw [he1]; unfold und edge1; rw [hS, hB]
  have u2 : und r.e2 = ⟨.raw, x.child (!s), x⟩ := by rw [he2]; unfold und edge2; rw [hB]
  rw [v0, v1, v2, u0, u1, u2]
  refine ⟨nodup_three _ _ _ (ne_child x s) (ne_child x (!s)) (child_ne_child x s), ?_⟩
  refine nodup_three _ _ _ ?_ ?_ ?_
  · intro he
    obtain ⟨ht, -⟩ := (canon_eq_iff _ _).mp he
    exact nomatch ht
  · intro he
    obtain ⟨-, (⟨h1, -⟩ | ⟨-, h2⟩)⟩ := (canon_eq_iff _ _).mp he
    · exact ne_child x (!s) h1
    · exact child_ne_child x s h2
  · intro he
    obtain ⟨ht, -⟩ := (canon_eq_iff _ _).mp he
    exact nomatch ht

/-! ## The identity reception on stable occurrence keys -/

/-- **Definition 25.4's closing sentence, for any family.** `Γ_id` is admissible on every keyed
    family with distinct occurrence keys: several lineages, several cycles, any recording order.
    The two hypotheses of `gid_admissible` are discharged by `ids_nodup_of_occKeys` and
    `keyed_nondegenerate`. "Distinct occurrence keys" is how the tree renders the book's "stable
    occurrence keys": within one application the book derives it (Proposition 23.2, Theorem 22.8)
    and `record_deterministic_typed` takes it as a hypothesis; across applications it is the
    recording discipline of Definition 23.5, not a theorem of the book. -/
theorem gid_keyed_admissible (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hk : ∀ r ∈ L, Keyed r) (hnd : (L.map occKeyRec).Nodup) :
    Admissible (Gid (L.map FaceRec.pre)) oedges (L.map FaceRec.pre) :=
  gid_admissible L (ids_nodup_of_occKeys L hk hnd) fun r hr => keyed_nondegenerate (hk r hr)

/-- **Theorem 23.6's ledger.** The ledger `ledgerOf fs` recorded from received faces with
    distinct occurrence keys admits `Γ_id`: the hypotheses are exactly those of
    `record_deterministic_typed`. -/
theorem gid_ledgerOf_admissible (fs : List (ReceivedFace Aux Cert RawAux EvalAux h))
    (target : QuestionId) (prov : Prov) (hwk : ∀ f ∈ fs, WellKeyed f.packet.input)
    (hnd : (fs.map occKey).Nodup) :
    Admissible (Gid ((ledgerOf (Renew := Renew) fs target prov).map FaceRec.pre)) oedges
      ((ledgerOf (Renew := Renew) fs target prov).map FaceRec.pre) := by
  refine gid_keyed_admissible _ (ledgerOf_keyed fs target prov hwk) ?_
  change ((fs.map _).map occKeyRec).Nodup
  rw [List.map_map]
  exact hnd

/-- **Two cycles.** A family assembled from two cycles' keyed families, each with distinct
    occurrence keys, admits `Γ_id`. -/
theorem gid_two_cycles_admissible (L₁ L₂ : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (c₁ c₂ : ℕ) (hk1 : ∀ r ∈ L₁, Keyed r) (hk2 : ∀ r ∈ L₂, Keyed r)
    (h1 : ∀ r ∈ L₁, r.packet.input.x.cycle = c₁) (h2 : ∀ r ∈ L₂, r.packet.input.x.cycle = c₂)
    (hne : c₁ ≠ c₂) (n1 : (L₁.map occKeyRec).Nodup) (n2 : (L₂.map occKeyRec).Nodup) :
    Admissible (Gid ((L₁ ++ L₂).map FaceRec.pre)) oedges ((L₁ ++ L₂).map FaceRec.pre) :=
  gid_keyed_admissible _ (fun r hr => (List.mem_append.mp hr).elim (hk1 r) (hk2 r))
    (occKeys_nodup_of_cycles L₁ L₂ c₁ c₂ h1 h2 hne n1 n2)

/-- **The active family.** Any sublist of an admissible keyed family (the active family is a
    filter of the archival one, `Export.def_33_1`) admits `Γ_id`. -/
theorem gid_sublist_admissible (L L' : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hs : List.Sublist L' L) (hk : ∀ r ∈ L, Keyed r) (hnd : (L.map occKeyRec).Nodup) :
    Admissible (Gid (L'.map FaceRec.pre)) oedges (L'.map FaceRec.pre) :=
  gid_keyed_admissible L' (fun r hr => hk r (hs.subset hr)) ((hs.map occKeyRec).nodup hnd)

/-- **The one-lineage case is a corollary.** On a line-shaped family the occurrence key is
    determined by the event, so `gid_lineage_admissible`'s hypothesis (distinct events) gives
    distinct occurrence keys. -/
theorem occKeyRec_lineShaped {i : QuestionId} {r : FaceRec Aux Cert RawAux EvalAux h Prov Renew}
    (hL : LineShaped i r) : occKeyRec r = (evJ r, linV i (evJ r), i.rel.getD (evJ r) false) := by
  unfold occKeyRec evJ
  rw [hL.hx, hL.hs]

theorem gid_lineage_admissible' (i : QuestionId)
    (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hL : ∀ r ∈ L, LineShaped i r) (hnd : (L.map evJ).Nodup) :
    Admissible (Gid (L.map FaceRec.pre)) oedges (L.map FaceRec.pre) := by
  refine gid_keyed_admissible L (fun r hr => keyed_of_lineShaped (hL r hr)) ?_
  have hmap : L.map occKeyRec =
      (L.map evJ).map (fun j => (j, linV i j, i.rel.getD j false)) := by
    rw [List.map_map]
    exact List.map_congr_left fun r hr => occKeyRec_lineShaped (hL r hr)
  rw [hmap]
  exact nodup_map_inj _ (fun j j' he => congrArg Prod.fst he) _ hnd

/-! ## The archival family of an export -/

section Export
variable {Op σ P Y Ph St : Type}

/-- `ofState`'s archival family is every face ledger the state recorded, concatenated in
    recording order. -/
theorem ofState_archFaces (S : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (c : Cycle.CycleOutcome σ RawAux EvalAux h) (Θ : Lifecycle.Retention P Y Ph St)
    (D : Lifecycle.LifeLedger P Y) (rel : List (Lifecycle.ReleaseRec P)) (n : ℕ)
    (entry : FaceRec Aux Cert RawAux EvalAux h Prov Renew → ℕ)
    (compat : FaceRec Aux Cert RawAux EvalAux h Prov Renew → Bool)
    (recOf : σ → RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (t : QuestionId) (L : List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))
    (hS : ∀ x k, c = .assimilated x k → S = recordFace (recOf x) t L)
    (hD : ∀ ev ∈ D, ev.1.1 ∈ (S.hist.flatMap Prod.snd).map (·.id) ∧
      ev.2.fid ∈ (S.hist.flatMap Prod.snd).map (·.id))
    (hrel : ∀ r ∈ rel, r.fid ∈ (S.hist.flatMap Prod.snd).map (·.id)) :
    (Export.ofState S c Θ D rel n entry compat recOf t L hS hD hrel).archFaces =
      S.hist.flatMap Prod.snd := rfl

/-- **The archival family admits `Γ_id`** whenever every recorded face is keyed and the
    occurrence keys across the whole recorded history are distinct, however many cycles and
    lineages the ledgers came from. -/
theorem gid_archival_admissible
    (S : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (hk : ∀ p ∈ S.hist, ∀ r ∈ p.2, Keyed r)
    (hnd : ((S.hist.flatMap Prod.snd).map occKeyRec).Nodup) :
    Admissible (Gid ((S.hist.flatMap Prod.snd).map FaceRec.pre)) oedges
      ((S.hist.flatMap Prod.snd).map FaceRec.pre) :=
  gid_keyed_admissible _ (fun r hr => by
    obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
    exact hk p hp r hr) hnd

/-- **The recording invariant.** Every ledger in the history is `ledgerOf` some well-keyed
    received faces, recorded under its own target. It holds for an empty history and is preserved
    by every Definition 23.5 call, so it holds for every state Definition 23.5 builds. -/
def HistOfLedgers (S : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew))) : Prop :=
  ∀ p ∈ S.hist, ∃ (fs : List (ReceivedFace Aux Cert RawAux EvalAux h)) (prov : Prov),
    (∀ f ∈ fs, WellKeyed f.packet.input) ∧ p.2 = ledgerOf fs p.1 prov

theorem histOfLedgers_empty (S : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (hS : S.hist = []) : HistOfLedgers S := fun p hp => by
  rw [hS] at hp; exact nomatch hp

/-- A `recordFace` call of a `ledgerOf` ledger from well-keyed faces preserves the invariant. -/
theorem histOfLedgers_recordFace
    (st : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (hst : HistOfLedgers st) (fs : List (ReceivedFace Aux Cert RawAux EvalAux h))
    (target : QuestionId) (prov : Prov) (hwk : ∀ f ∈ fs, WellKeyed f.packet.input) :
    HistOfLedgers (recordFace st target (ledgerOf fs target prov)) := by
  intro p hp
  change p ∈ st.hist ++ [(target, ledgerOf fs target prov)] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hst p hp
  · rw [List.mem_singleton] at hp
    subst hp
    exact ⟨fs, prov, hwk, rfl⟩

/-- Under the invariant every recorded face is keyed. -/
theorem keyed_of_histOfLedgers
    (S : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (hS : HistOfLedgers S) : ∀ p ∈ S.hist, ∀ r ∈ p.2, Keyed r := by
  intro p hp r hr
  obtain ⟨fs, prov, hwk, he⟩ := hS p hp
  rw [he] at hr
  exact ledgerOf_keyed fs p.1 prov hwk r hr

/-- **The archival family of a state built by Definition 23.5 admits `Γ_id`**, given distinct
    occurrence keys over the recorded history. -/
theorem gid_archival_admissible'
    (S : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (hS : HistOfLedgers S) (hnd : ((S.hist.flatMap Prod.snd).map occKeyRec).Nodup) :
    Admissible (Gid ((S.hist.flatMap Prod.snd).map FaceRec.pre)) oedges
      ((S.hist.flatMap Prod.snd).map FaceRec.pre) :=
  gid_archival_admissible S (keyed_of_histOfLedgers S hS) hnd

/-- **Across cycles, n-fold.** If every recorded ledger sits in one cycle (`cycleOf`), is
    internally free of repeated occurrence keys (Definition 23.5: "within one application, the
    ledger ... contains each stable face key exactly once"), and the recorded ledgers' cycles are
    pairwise distinct, then the whole history has distinct occurrence keys. -/
theorem occKeys_nodup_of_hist_cycles
    (hist : List (QuestionId × List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (cycleOf : QuestionId × List (FaceRec Aux Cert RawAux EvalAux h Prov Renew) → ℕ)
    (hhom : ∀ p ∈ hist, ∀ r ∈ p.2, r.packet.input.x.cycle = cycleOf p)
    (heach : ∀ p ∈ hist, (p.2.map occKeyRec).Nodup)
    (htags : (hist.map cycleOf).Nodup) :
    ((hist.flatMap Prod.snd).map occKeyRec).Nodup := by
  induction hist with
  | nil => simp
  | cons p hist ih =>
    rw [List.flatMap_cons, List.map_append]
    obtain ⟨hp, htags'⟩ := List.nodup_cons.mp htags
    refine nodup_append_of_disjoint _ _ (heach p (by simp))
      (ih (fun q hq => hhom q (List.mem_cons_of_mem p hq))
        (fun q hq => heach q (List.mem_cons_of_mem p hq)) htags') ?_
    intro k hk hk'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
    obtain ⟨r', hr', he⟩ := List.mem_map.mp hk'
    obtain ⟨q, hq, hr'q⟩ := List.mem_flatMap.mp hr'
    have hc : (occKeyRec r').2.1.cycle = (occKeyRec r).2.1.cycle := by rw [he]
    rw [occKeyRec_cycle, occKeyRec_cycle, hhom p (by simp) r hr,
      hhom q (List.mem_cons_of_mem p hq) r' hr'q] at hc
    exact hp (List.mem_map.mpr ⟨q, hq, hc⟩)

/-- **The archival family across cycles.** A state built by Definition 23.5 whose recorded
    ledgers each sit in one cycle, are internally key-distinct, and come from pairwise distinct
    cycles, admits `Γ_id` on its whole archival family. -/
theorem gid_archival_admissible_cycles
    (S : RecState Op (List (FaceRec Aux Cert RawAux EvalAux h Prov Renew)))
    (hS : HistOfLedgers S)
    (cycleOf : QuestionId × List (FaceRec Aux Cert RawAux EvalAux h Prov Renew) → ℕ)
    (hhom : ∀ p ∈ S.hist, ∀ r ∈ p.2, r.packet.input.x.cycle = cycleOf p)
    (heach : ∀ p ∈ S.hist, (p.2.map occKeyRec).Nodup)
    (htags : (S.hist.map cycleOf).Nodup) :
    Admissible (Gid ((S.hist.flatMap Prod.snd).map FaceRec.pre)) oedges
      ((S.hist.flatMap Prod.snd).map FaceRec.pre) :=
  gid_archival_admissible S (keyed_of_histOfLedgers S hS)
    (occKeys_nodup_of_hist_cycles S.hist cycleOf hhom heach htags)

/-- **`def_33_1`'s hypothesis discharged.** The distinct-keys hypothesis of the export packet
    theorem follows from keyed records with distinct occurrence keys. -/
theorem export_keys_nodup (X : Export.ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (hk : ∀ r ∈ X.archFaces, Keyed r) (hnd : (X.archFaces.map occKeyRec).Nodup) :
    (X.archFaces.map (·.id)).Nodup :=
  ids_nodup_of_occKeys _ hk hnd


/-- **The active family admits `Γ_id`.** `def_33_1` makes the active map a sublist of the
    archival family; with keyed records and distinct occurrence keys the admissibility the
    export's `substrate` field asks for follows. -/
theorem gid_active_admissible
    (X : Export.ElemIIOut Op σ Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (hk : ∀ r ∈ X.archFaces, Keyed r) (hnd : (X.archFaces.map occKeyRec).Nodup) :
    Admissible (Gid (X.shell.actMap.map FaceRec.pre)) oedges (X.shell.actMap.map FaceRec.pre) := by
  have hd := Export.def_33_1 X (export_keys_nodup X hk hnd)
  exact gid_sublist_admissible _ _ (hd.2.2.2.1.trans hd.2.2.2.2.1) hk hnd

end Export

#print axioms entryRec_keyed
#print axioms ledgerOf_keyed
#print axioms keyed_of_lineShaped
#print axioms keyed_id_eq
#print axioms ids_nodup_of_occKeys
#print axioms occKeys_nodup_of_cycles
#print axioms ne_child
#print axioms child_ne_child
#print axioms keyed_nondegenerate
#print axioms gid_keyed_admissible
#print axioms gid_ledgerOf_admissible
#print axioms gid_two_cycles_admissible
#print axioms gid_sublist_admissible
#print axioms gid_lineage_admissible'
#print axioms ofState_archFaces
#print axioms gid_archival_admissible
#print axioms histOfLedgers_empty
#print axioms histOfLedgers_recordFace
#print axioms keyed_of_histOfLedgers
#print axioms gid_archival_admissible'
#print axioms occKeys_nodup_of_hist_cycles
#print axioms gid_archival_admissible_cycles
#print axioms export_keys_nodup
#print axioms gid_active_admissible

end G2_31
end Gaps
end RatioSpace
