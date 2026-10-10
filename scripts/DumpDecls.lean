/-
  DumpDecls.lean: the one generator of the declaration and axiom reports (Codex spec
  v0.25, A1). Run from `research/lean`:

    lake env lean --run ../lean-support/v0.25-baseline/DumpDecls.lean <outdir>

  It imports `RatioSpace`, visits every constant whose module starts with `RatioSpace`,
  skips internal and auxiliary names (`Name.isInternal`, recursors, `noConfusion`,
  `match_`, `proof_`, structure projections' auxiliaries), normalises private names
  (`privateToUserName?`), and writes
    <outdir>/declarations.tsv  (name, kind, module, type, value_hash)
    <outdir>/axioms.tsv        (name, axioms)
  with `type` pretty-printed on one line (pp.fullNames, pp.universes, pp.piBinderTypes,
  pp.proofs on, no width limit), `value_hash` the Expr hash of the value for def, abbrev
  and instance and empty for theorems, and axioms from `Lean.collectAxioms`, sorted,
  comma-separated. Rows are sorted by name. Written 2026-09-22.
-/
import Lean
open Lean Meta

def auxSuffix (s : String) : Bool :=
  s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_" ||
  s == "noConfusion" || s == "noConfusionType" || s == "rec" || s == "recOn" ||
  s == "casesOn" || s == "brecOn" || s == "binductionOn" || s == "below" || s == "ibelow" ||
  s == "inj" || s == "injEq" || s == "sizeOf_spec" || s.startsWith "eq_" && s.length ≤ 4

def skipped (n : Name) : Bool :=
  n.isInternal || n.isInternalDetail ||
  n.components.any fun c => match c with
    | .str _ s => auxSuffix s
    | _ => false

def kindOf (n : Name) (ci : ConstantInfo) : MetaM String := do
  match ci with
  | .thmInfo _ => pure "theorem"
  | .axiomInfo _ => pure "axiom"
  | .inductInfo _ => pure "inductive"
  | .ctorInfo _ => pure "constructor"
  | .recInfo _ => pure "recursor"
  | .quotInfo _ => pure "quot"
  | .opaqueInfo _ => pure "opaque"
  | .defnInfo _ =>
    if ← Lean.Meta.isInstance n then pure "instance"
    else
      let st ← getReducibilityStatus n
      match st with
      | ReducibilityStatus.reducible => pure "abbrev"
      | _ => pure "def"

def oneLine (s : String) : String :=
  String.intercalate " " ((s.replace "\r" " " |>.replace "\t" " " |>.splitOn "\n").filter (· ≠ ""))

def ppType (e : Expr) : MetaM String := do
  let fmt ← withOptions (fun o => o
      |>.setBool `pp.fullNames true
      |>.setBool `pp.universes true
      |>.setBool `pp.piBinderTypes true
      |>.setBool `pp.proofs true
      |>.set `format.width (1000000 : Nat)) (ppExpr e)
  pure (oneLine (fmt.pretty 1000000))

def main (args : List String) : IO Unit := do
  let outDir := args.headD "reports"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `RatioSpace }] {} 0
  let moduleOf (n : Name) : String :=
    match env.getModuleIdxFor? n with
    | some idx => (env.header.moduleNames[idx.toNat]!).toString
    | none => ""
  let mut collected : Array Name := #[]
  for (n, _) in env.constants.toList do
    if (moduleOf n).startsWith "RatioSpace" && !(skipped n) then collected := collected.push n
  let names := collected.qsort (fun a b => a.toString < b.toString)
  let ctx : Core.Context := { fileName := "<DumpDecls>", fileMap := default }
  let st : Core.State := { env := env }
  let ((declRows, axRows), _) ← (do
      let mut declRows : Array String := #[]
      let mut axRows : Array String := #[]
      for n in names do
        let some ci := env.find? n | continue
        let user := (privateToUserName? n).getD n
        let kind ← kindOf n ci
        let ty ← ppType ci.type
        let modName := moduleOf n
        let vh := match kind, ci.value? with
          | "theorem", _ => ""
          | _, some v => toString v.hash
          | _, none => ""
        declRows := declRows.push s!"{user}\t{kind}\t{modName}\t{ty}\t{vh}"
        let axs ← collectAxioms n
        let axs := (axs.map (·.toString)).qsort (· < ·)
        axRows := axRows.push s!"{user}\t{String.intercalate "," axs.toList}"
      pure (declRows, axRows) : MetaM (Array String × Array String)).run'.toIO ctx st
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir ++ "/declarations.tsv")
    ("name\tkind\tmodule\ttype\tvalue_hash\n" ++ String.intercalate "\n" declRows.toList ++ "\n")
  IO.FS.writeFile (outDir ++ "/axioms.tsv")
    ("name\taxioms\n" ++ String.intercalate "\n" axRows.toList ++ "\n")
  IO.println s!"{declRows.size} declarations, {axRows.size} axiom rows -> {outDir}"
