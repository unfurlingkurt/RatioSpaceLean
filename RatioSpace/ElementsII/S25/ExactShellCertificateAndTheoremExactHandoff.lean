/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsII.S25.Shell
import RatioSpace.ElementsII.S33.Export
/-!
  Elements II §25, Definition 25.6 Exact shell certificate and
  Theorem 25.10 Exact handoff: the `Src_Γ` coordinate.

  **Book statement.** Definition 25.5: *"`Src_Γ` is the complete
  lossless source ledger."* Definition 25.6: `ShellCert = (c_sh, |V_Γ|, |E_Γ|,
  |F_Γ|, (d_Γ(v)), (δ_Γ(v)), D_Γ, Src_Γ)`. Definition 25.4, condition 6:
  *"For every received vertex, edge, and face, `src_V`, `src_E`, and `src_F`
  retain the complete finite set of exact prequotient records mapped to it."*
  Theorem 25.10, item 7: *"lossless exact preimages"*.

  **The free-parameter certificate.** `Cx.cert` (`Shell.lean`) takes the source
  ledger as a free parameter `src : S`, not built from the reception's `srcV`,
  `srcE`, `srcF`, and not tied to condition 6. `handoff_complete` proves
  certificate equality for the same arbitrary `src`.

  **Contents.**
  * `SrcLedger`, `srcLedger`: `Src_Γ` built from `Γ` and the export,
    one entry `(x, src_Γ x)` for each received vertex, edge key and face key of
    `K^Γ` (`V_Γ`, `E_Γ`, `F_Γ` in order), and `cert`, the certificate
    whose last coordinate is that ledger. Nothing is a free input.
  * `srcLedger_index`: the ledger is indexed by exactly `V_Γ`, `E_Γ`, `F_Γ`.
  * `srcLedger_lossless`: under condition 6 each entry holds exactly the
    prequotient records of the export mapped to its index.
  * `srcLedger_complete`: under condition 6 every prequotient vertex, edge and
    face record of the export sits in the entry of its image, and that entry is
    in the ledger.
  * `srcLedger_determined`: two receptions with the same maps `q_V, q_E, q_F`,
    both meeting condition 6, have ledgers with the same indices and the same
    records in every entry. `Src_Γ` is fixed as sets by the maps and the export
    (the book's "complete finite set"); the source maps add no freedom beyond
    list order and repeats within an entry.
  * `ofMaps_srcLedger_lossless`: the reception `Shell.Reception.ofMaps` builds from
    the maps and the export has a lossless ledger with no hypothesis.
  * `cert_src`, `cert_agrees`: the source coordinate of `cert` is the
    ledger, and its other seven coordinates are `Cx.cert`'s.
  * `handoff_complete_src`: Theorem 25.10 with `Src_Γ` supplied by `Γ`: two
    exports with the same active family give the same whole certificate, the
    ledger is lossless and complete over the active family, and every active
    record's face key sits in the entry of its received face.
  * `stage_cert_agrees`: the shell stage's certificate (`ShellStageIn.cert`,
    Theorem 33.2(1)), which carries the active records as its source, agrees
    with `cert` on the other seven coordinates.
-/
set_option linter.style.longLine false

namespace RatioSpace
namespace Gaps
namespace G2_33

open RatioSpace.Two RatioSpace.Two.Incidence RatioSpace.Two.Shell

/-! ## The source ledger `Src_Γ`, built from the reception -/

/-- **Definition 25.5, `Src_Γ`.** One entry per received vertex, edge key and
    face key, each carrying the reception's source list for it. -/
structure SrcLedger (Vp Ep Fp V E F : Type) where
  V : List (V × List Vp)
  E : List (E × List Ep)
  F : List (F × List Fp)

section Ledger
variable {Vp Ep Fp R V E F : Type} [DecidableEq V] [DecidableEq E] [DecidableEq F]

/-- `Src_Γ` of `K^Γ`: indexed by `V_Γ`, `E_Γ`, `F_Γ` of the received complex,
    each entry the reception's `src_V`, `src_E`, `src_F` at that index. -/
def srcLedger (Γ : Shell.Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R)) :
    SrcLedger Vp Ep Fp V E F :=
  ⟨(Γ.complex fs).VG.map (fun w => (w, Γ.srcV w)),
   (Γ.complex fs).EG.map (fun k => (k, Γ.srcE k)),
   (Γ.complex fs).FG.map (fun k => (k, Γ.srcF k))⟩

/-- **Definition 25.6.** The complete certificate with `Src_Γ` supplied by `Γ`. -/
def cert (Γ : Shell.Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R)) :
    ShellCert V F (SrcLedger Vp Ep Fp V E F) :=
  (Γ.complex fs).cert (srcLedger Γ fs)

theorem cert_src (Γ : Shell.Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R)) :
    (cert Γ fs).src = srcLedger Γ fs := rfl

/-- The other seven coordinates are those of `Cx.cert`, whatever it was passed. -/
theorem cert_agrees {S : Type} (Γ : Shell.Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R)) (s : S) :
    (cert Γ fs).c = ((Γ.complex fs).cert s).c ∧ (cert Γ fs).nV = ((Γ.complex fs).cert s).nV ∧
    (cert Γ fs).nE = ((Γ.complex fs).cert s).nE ∧ (cert Γ fs).nF = ((Γ.complex fs).cert s).nF ∧
    (cert Γ fs).d = ((Γ.complex fs).cert s).d ∧ (cert Γ fs).delta = ((Γ.complex fs).cert s).delta ∧
    (cert Γ fs).D = ((Γ.complex fs).cert s).D :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The ledger is indexed by exactly `V_Γ`, `E_Γ`, `F_Γ`. -/
theorem srcLedger_index (Γ : Shell.Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R)) :
    (srcLedger Γ fs).V.map Prod.fst = (Γ.complex fs).VG ∧
    (srcLedger Γ fs).E.map Prod.fst = (Γ.complex fs).EG ∧
    (srcLedger Γ fs).F.map Prod.fst = (Γ.complex fs).FG := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold srcLedger; rw [List.map_map]; exact List.map_id' _)

/-- **Condition 6 makes the ledger lossless.** Every entry holds exactly the
    export's prequotient records mapped to its index. -/
theorem srcLedger_lossless (Γ : Shell.Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R))
    (hV : ∀ w x, x ∈ Γ.srcV w ↔ x ∈ preV fs ∧ Γ.qV x = w)
    (hE : ∀ k x, x ∈ Γ.srcE k ↔ x ∈ preE fs ∧ (Γ.qE x).key = k)
    (hF : ∀ k x, x ∈ Γ.srcF k ↔ x ∈ preF fs ∧ Γ.qF x = k) :
    (∀ p ∈ (srcLedger Γ fs).V, ∀ x, x ∈ p.2 ↔ x ∈ preV fs ∧ Γ.qV x = p.1) ∧
    (∀ p ∈ (srcLedger Γ fs).E, ∀ x, x ∈ p.2 ↔ x ∈ preE fs ∧ (Γ.qE x).key = p.1) ∧
    (∀ p ∈ (srcLedger Γ fs).F, ∀ x, x ∈ p.2 ↔ x ∈ preF fs ∧ Γ.qF x = p.1) := by
  refine ⟨fun p hp x => ?_, fun p hp x => ?_, fun p hp x => ?_⟩
  · obtain ⟨w, _, rfl⟩ := List.mem_map.mp hp; exact hV w x
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp; exact hE k x
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp; exact hF k x

omit [DecidableEq E] [DecidableEq F] in
/-- Every prequotient vertex of the export is received at a vertex of `K^Γ`. -/
theorem qV_mem_VG (Γ : Shell.Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R)) (x : Vp)
    (hx : x ∈ preV fs) : Γ.qV x ∈ (Γ.complex fs).VG := by
  obtain ⟨f, hf, hxf⟩ := List.mem_flatMap.mp hx
  refine (mem_nub _ _).mpr (List.mem_flatMap.mpr ⟨Γ.face f, List.mem_map_of_mem hf, ?_⟩)
  change Γ.qV x ∈ [Γ.qV f.v0, Γ.qV f.v1, Γ.qV f.v2]
  rcases List.mem_cons.mp hxf with rfl | h1
  · exact List.mem_cons_self
  rcases List.mem_cons.mp h1 with rfl | h2
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  rcases List.mem_cons.mp h2 with rfl | h3
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact absurd h3 List.not_mem_nil

omit [DecidableEq V] [DecidableEq F] in
/-- Every prequotient edge of the export is received at an edge key of `K^Γ`. -/
theorem qE_mem_EG (Γ : Shell.Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R)) (x : Ep)
    (hx : x ∈ preE fs) : (Γ.qE x).key ∈ (Γ.complex fs).EG := by
  obtain ⟨f, hf, hxf⟩ := List.mem_flatMap.mp hx
  refine (mem_nub _ _).mpr (List.mem_flatMap.mpr ⟨Γ.face f, List.mem_map_of_mem hf, ?_⟩)
  change (Γ.qE x).key ∈ [Γ.qE f.e0, Γ.qE f.e1, Γ.qE f.e2].map ROEdge.key
  exact List.mem_map_of_mem (List.mem_map_of_mem (f := Γ.qE) hxf)

omit [DecidableEq V] [DecidableEq E] in
/-- Every prequotient face key of the export is received at a face key of `K^Γ`. -/
theorem qF_mem_FG (Γ : Shell.Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R)) (x : Fp)
    (hx : x ∈ preF fs) : Γ.qF x ∈ (Γ.complex fs).FG := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
  exact (mem_nub _ _).mpr (List.mem_map.mpr ⟨Γ.face f, List.mem_map_of_mem hf, rfl⟩)

/-- **The ledger is complete.** Under condition 6, every prequotient vertex,
    edge and face record of the export sits in the ledger entry of its image. -/
theorem srcLedger_complete (Γ : Shell.Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R))
    (hV : ∀ w x, x ∈ Γ.srcV w ↔ x ∈ preV fs ∧ Γ.qV x = w)
    (hE : ∀ k x, x ∈ Γ.srcE k ↔ x ∈ preE fs ∧ (Γ.qE x).key = k)
    (hF : ∀ k x, x ∈ Γ.srcF k ↔ x ∈ preF fs ∧ Γ.qF x = k) :
    (∀ x ∈ preV fs, ∃ p ∈ (srcLedger Γ fs).V, p.1 = Γ.qV x ∧ x ∈ p.2) ∧
    (∀ x ∈ preE fs, ∃ p ∈ (srcLedger Γ fs).E, p.1 = (Γ.qE x).key ∧ x ∈ p.2) ∧
    (∀ x ∈ preF fs, ∃ p ∈ (srcLedger Γ fs).F, p.1 = Γ.qF x ∧ x ∈ p.2) :=
  ⟨fun x hx => ⟨_, List.mem_map_of_mem (qV_mem_VG Γ fs x hx), rfl, (hV _ x).mpr ⟨hx, rfl⟩⟩,
   fun x hx => ⟨_, List.mem_map_of_mem (qE_mem_EG Γ fs x hx), rfl, (hE _ x).mpr ⟨hx, rfl⟩⟩,
   fun x hx => ⟨_, List.mem_map_of_mem (qF_mem_FG Γ fs x hx), rfl, (hF _ x).mpr ⟨hx, rfl⟩⟩⟩

omit [DecidableEq V] [DecidableEq E] [DecidableEq F] in
/-- The same received complex from the same maps. -/
theorem complex_of_maps (Γ Γ' : Shell.Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R))
    (hqV : Γ.qV = Γ'.qV) (hqE : Γ.qE = Γ'.qE) (hqF : Γ.qF = Γ'.qF) :
    Γ.complex fs = Γ'.complex fs := by
  unfold Reception.complex Reception.face
  rw [hqV, hqE, hqF]

/-- **`Src_Γ` is determined by the maps and the export, as sets.** Two
    receptions with the same `q_V, q_E, q_F`, both meeting condition 6, have
    ledgers with the same indices in the same order and the same members in
    every entry (the book's "complete finite set"; order and repeats within an
    entry are not fixed). -/
theorem srcLedger_determined (Γ Γ' : Shell.Reception Vp Ep Fp V E F) (fs : List (PFace Vp Ep Fp R))
    (hqV : Γ.qV = Γ'.qV) (hqE : Γ.qE = Γ'.qE) (hqF : Γ.qF = Γ'.qF)
    (hV : ∀ w x, x ∈ Γ.srcV w ↔ x ∈ preV fs ∧ Γ.qV x = w)
    (hE : ∀ k x, x ∈ Γ.srcE k ↔ x ∈ preE fs ∧ (Γ.qE x).key = k)
    (hF : ∀ k x, x ∈ Γ.srcF k ↔ x ∈ preF fs ∧ Γ.qF x = k)
    (hV' : ∀ w x, x ∈ Γ'.srcV w ↔ x ∈ preV fs ∧ Γ'.qV x = w)
    (hE' : ∀ k x, x ∈ Γ'.srcE k ↔ x ∈ preE fs ∧ (Γ'.qE x).key = k)
    (hF' : ∀ k x, x ∈ Γ'.srcF k ↔ x ∈ preF fs ∧ Γ'.qF x = k) :
    (srcLedger Γ fs).V.map Prod.fst = (srcLedger Γ' fs).V.map Prod.fst ∧
    (srcLedger Γ fs).E.map Prod.fst = (srcLedger Γ' fs).E.map Prod.fst ∧
    (srcLedger Γ fs).F.map Prod.fst = (srcLedger Γ' fs).F.map Prod.fst ∧
    (∀ w x, x ∈ Γ.srcV w ↔ x ∈ Γ'.srcV w) ∧
    (∀ k x, x ∈ Γ.srcE k ↔ x ∈ Γ'.srcE k) ∧
    (∀ k x, x ∈ Γ.srcF k ↔ x ∈ Γ'.srcF k) := by
  have hK := complex_of_maps Γ Γ' fs hqV hqE hqF
  obtain ⟨i1, i2, i3⟩ := srcLedger_index Γ fs
  obtain ⟨j1, j2, j3⟩ := srcLedger_index Γ' fs
  refine ⟨by rw [i1, j1, hK], by rw [i2, j2, hK], by rw [i3, j3, hK],
    fun w x => ?_, fun k x => ?_, fun k x => ?_⟩
  · rw [hV, hV', hqV]
  · rw [hE, hE', hqE]
  · rw [hF, hF', hqF]

/-- The reception built from the maps and the export has a lossless, complete
    ledger with no hypothesis. -/
theorem ofMaps_srcLedger_lossless (qV : Vp → V) (qE : Ep → ROEdge V E) (qF : Fp → F)
    (fs : List (PFace Vp Ep Fp R)) :
    let Γ := Shell.Reception.ofMaps qV qE qF fs
    (∀ p ∈ (srcLedger Γ fs).V, ∀ x, x ∈ p.2 ↔ x ∈ preV fs ∧ Γ.qV x = p.1) ∧
    (∀ p ∈ (srcLedger Γ fs).E, ∀ x, x ∈ p.2 ↔ x ∈ preE fs ∧ (Γ.qE x).key = p.1) ∧
    (∀ p ∈ (srcLedger Γ fs).F, ∀ x, x ∈ p.2 ↔ x ∈ preF fs ∧ Γ.qF x = p.1) := by
  obtain ⟨hV, hE, hF⟩ := ofMaps_lossless qV qE qF fs
  exact srcLedger_lossless _ fs hV hE hF

/-- Condition 6 read off an admissible reception. -/
theorem lossless_of_admissible {Γ : Shell.Reception Vp Ep Fp V E F} {pe : PreEdges Vp Ep}
    {fs : List (PFace Vp Ep Fp R)} (hA : Admissible Γ pe fs) :
    (∀ p ∈ (srcLedger Γ fs).V, ∀ x, x ∈ p.2 ↔ x ∈ preV fs ∧ Γ.qV x = p.1) ∧
    (∀ p ∈ (srcLedger Γ fs).E, ∀ x, x ∈ p.2 ↔ x ∈ preE fs ∧ (Γ.qE x).key = p.1) ∧
    (∀ p ∈ (srcLedger Γ fs).F, ∀ x, x ∈ p.2 ↔ x ∈ preF fs ∧ Γ.qF x = p.1) :=
  srcLedger_lossless Γ fs hA.losslessV hA.losslessE hA.losslessF

end Ledger

/-! ## Theorem 25.10 with `Src_Γ` supplied by `Γ` -/

section Handoff
variable {Aux Cert RawAux EvalAux Prov Renew P Y Ph St S V E F : Type} {h : ℕ}
  [DecidableEq V] [DecidableEq E] [DecidableEq F]

/-- **Theorem 25.10.** Given an export and an admissible reception, the whole
    certificate, `Src_Γ` included, is a function of the active face map and `Γ`:
    two exports with the same active family give the same certificate. Its
    source ledger holds exactly the active prequotient records received at each
    index (item 7, lossless exact preimages), every active record's face key
    sits in the entry of its received face, and the records are retained whole. -/
theorem handoff_complete_src (X X' : ShellIn S Aux Cert RawAux EvalAux Prov Renew P Y Ph St h)
    (hact : X.actMap = X'.actMap) (Γ : Shell.Reception QuestionId OEdge FaceId V E F) (pe : PreEdges QuestionId OEdge)
    (hA : Admissible Γ pe (X.actMap.map FaceRec.pre)) :
    cert Γ (X.actMap.map FaceRec.pre) = cert Γ (X'.actMap.map FaceRec.pre) ∧
    (cert Γ (X.actMap.map FaceRec.pre)).src = srcLedger Γ (X.actMap.map FaceRec.pre) ∧
    (∀ p ∈ (srcLedger Γ (X.actMap.map FaceRec.pre)).V, ∀ x,
      x ∈ p.2 ↔ x ∈ preV (X.actMap.map FaceRec.pre) ∧ Γ.qV x = p.1) ∧
    (∀ p ∈ (srcLedger Γ (X.actMap.map FaceRec.pre)).E, ∀ x,
      x ∈ p.2 ↔ x ∈ preE (X.actMap.map FaceRec.pre) ∧ (Γ.qE x).key = p.1) ∧
    (∀ p ∈ (srcLedger Γ (X.actMap.map FaceRec.pre)).F, ∀ x,
      x ∈ p.2 ↔ x ∈ preF (X.actMap.map FaceRec.pre) ∧ Γ.qF x = p.1) ∧
    (∀ r ∈ X.actMap, ∃ p ∈ (srcLedger Γ (X.actMap.map FaceRec.pre)).F, p.1 = Γ.qF r.id ∧ r.id ∈ p.2) ∧
    (X.actMap.map FaceRec.pre).map PFace.record = X.actMap := by
  obtain ⟨l1, l2, l3⟩ := lossless_of_admissible hA
  obtain ⟨_, _, c3⟩ := srcLedger_complete Γ _ hA.losslessV hA.losslessE hA.losslessF
  refine ⟨by rw [hact], rfl, l1, l2, l3, fun r hr => ?_, ?_⟩
  · exact c3 r.id (List.mem_map.mpr ⟨FaceRec.pre r, List.mem_map_of_mem hr, rfl⟩)
  · rw [List.map_map]; exact List.map_id' X.actMap

end Handoff

/-! ## The shell stage (Theorem 33.2(1)) -/

section Stage
variable {Op Aux Cert RawAux EvalAux Prov Renew P Y Ph St V E F : Type} {h : ℕ}
  [DecidableEq V] [DecidableEq E] [DecidableEq F]

/-- `ShellStageIn.cert` (`Export.lean`) carries the active records as its
    source coordinate. The certificate with `Γ`'s own ledger agrees with it on
    the other seven coordinates, and its ledger holds every active record's face
    key in the entry of its received face when `Γ` is admissible. -/
theorem stage_cert_agrees (I : Export.ShellStageIn Op Aux Cert RawAux EvalAux Prov Renew P Y Ph St h V E F)
    (pe : PreEdges QuestionId OEdge) (hA : Admissible I.gamma pe (I.shell.actMap.map FaceRec.pre)) :
    (cert I.gamma (I.shell.actMap.map FaceRec.pre)).c = I.cert.c ∧
    (cert I.gamma (I.shell.actMap.map FaceRec.pre)).nV = I.cert.nV ∧
    (cert I.gamma (I.shell.actMap.map FaceRec.pre)).nE = I.cert.nE ∧
    (cert I.gamma (I.shell.actMap.map FaceRec.pre)).nF = I.cert.nF ∧
    (cert I.gamma (I.shell.actMap.map FaceRec.pre)).d = I.cert.d ∧
    (cert I.gamma (I.shell.actMap.map FaceRec.pre)).delta = I.cert.delta ∧
    (cert I.gamma (I.shell.actMap.map FaceRec.pre)).D = I.cert.D ∧
    I.cert.src = I.shell.actMap ∧
    (∀ r ∈ I.shell.actMap, ∃ p ∈ (srcLedger I.gamma (I.shell.actMap.map FaceRec.pre)).F,
      p.1 = I.gamma.qF r.id ∧ r.id ∈ p.2) := by
  obtain ⟨_, _, c3⟩ := srcLedger_complete I.gamma _ hA.losslessV hA.losslessE hA.losslessF
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun r hr => c3 r.id (List.mem_map.mpr ⟨FaceRec.pre r, List.mem_map_of_mem hr, rfl⟩)⟩

end Stage

#print axioms srcLedger_index
#print axioms srcLedger_lossless
#print axioms srcLedger_complete
#print axioms srcLedger_determined
#print axioms ofMaps_srcLedger_lossless
#print axioms lossless_of_admissible
#print axioms cert_agrees
#print axioms handoff_complete_src
#print axioms stage_cert_agrees

end G2_33
end Gaps
end RatioSpace
