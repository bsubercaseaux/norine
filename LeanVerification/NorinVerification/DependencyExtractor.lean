import Lean
import Lean.Data.Json.FromToJson
import Lean.Elab.BuiltinCommand
import Lean.Meta.Basic
import Lean.Message

import NorinVerification.fHat
set_option linter.hashCommand false

-- import fHat
open Lean Elab Term Meta Std

/-!
This file is a lightly modified version of the upstream `lean-graph` extractor.

Goal: generate a *reduced* dependency JSON that only contains declarations coming
from this project/file (i.e., excludes Mathlib/Init/Lean).

We apply the "local" filter both when expanding the BFS frontier and when
serializing nodes/edges.
-/

/-!
### Configure "local" declarations

Edit `localNamePrefixes` to match your project.

Typical choices:
* the project/library name (e.g. `NorinVerification`)
* your main namespace(s) (e.g. `NorinLemma8`)
* the internal private namespace produced by the module (often `_private.<Module>...`)
-/

def localNamePrefixes : List String :=
  [
    "NorinVerification",              -- project/library prefix
    "NorinLemma8",                     -- your main namespace
    "_private.NorinVerification.fHat"  -- internal names generated from the file/module
  ]

def isLocalDeclName (n : Name) : Bool :=
  let s := n.toString
  localNamePrefixes.any (fun p => s.startsWith p)

def getExpr (x : TermElabM Syntax) : TermElabM Expr := do
  let synt ← x
  elabTerm synt none


def getTypeStr (n : Name) := do
  let inf ← getConstInfo n
  let t := inf.toConstantVal.type
  let dat ← ppExpr t
  return s!"{dat}"

def getTypeExpr (n : Name) : TermElabM Expr := do
  let inf ← getConstInfo n
  let t := inf.toConstantVal.type
  return t

def getConstType (n : Name) : TermElabM String := do
  let constInfo ← getConstInfo n
  return match constInfo with
    | ConstantInfo.defnInfo _ => "Definition"
    | ConstantInfo.thmInfo _  => "Theorem"
    | ConstantInfo.axiomInfo _ => "Axiom"
    | _ => "Other"

def getConstantBody (n : Name) : TermElabM (Option Expr) := do
  let constInfo ← getConstInfo n
  let constValue := constInfo.value?
  return constValue


/--
Leuenberger: Collect only the 'relevant' dependencies of a constant/definition by optionally filtering out instance dictionaries,
which can reduce the total number of dependencies by orders of magnitude. To readmit instances set keepInstances to true.
-/
def getRelevantConstsFromConst (n : Name) (keepInstances := false) (keepTheorems := true) (keepInternal := true) :
    TermElabM (Array Name) := do
  let body ← getConstantBody n
  let consts := match body with | some b => b.getUsedConstants | none => #[]
  let consts ← consts.filterM fun m => do
    let info ← getConstInfo m
    let inst ← isInstance m
    pure <|
      (match info with
       | ConstantInfo.defnInfo _  => true
       | ConstantInfo.axiomInfo _ => true
       | ConstantInfo.thmInfo _  => keepTheorems
       | _                        => false) &&
      (keepInstances || !inst) &&
      (keepInternal  || !m.isInternal)
  -- Additional reduction step: only keep declarations that look local to this project.
  let consts := consts.filter isLocalDeclName
  return HashSet.ofArray consts |>.toArray



def getAllConstsFromNamespace (n : String) : TermElabM (List Name) := do
  let env ← getEnv
  let consts := env.constants.fold (fun res name _ => if name.getRoot.toString == n then name :: res else res) []
  return consts.toArray.toList


structure BFSState :=
  (g : HashMap Name (List Name))
  (outerLayer : List Name)

def getUsedConstantGraph (names : List Name) (depth : Nat) : TermElabM (List (Name × List Name)) := do

  -- make bfs from the specified root node

  -- the goal is to construct a hashmap where the key is the name of the const, and the entry is a list of names of other consts

  -- we keep a list of const names representing the outer layer of the bfs

  -- in each iteration we for each const in the outer layer find its references and that way construct the nodes that will be added to the graph

  -- then we extract the outer layer from the new nodes by looking at the children and checking whether they are already in the graph

  let state ← (List.range depth).foldlM (fun (state : BFSState) (_ : Nat) => do
    let g := state.g
    let outerLayer := state.outerLayer


    let newNodes ← outerLayer.mapM fun name => do
      let consts ← try getRelevantConstsFromConst name catch | _ => pure #[]
      pure (name, consts)


    let g := newNodes.foldl (fun m p => m.insert p.fst p.snd.toList) g
    let newOuterLayer := newNodes.foldl (fun (set : HashSet Name) (node : Name × Array Name) =>
      let set := set.insertMany node.snd
      set) HashSet.emptyWithCapacity
    -- Don't expand into non-local nodes.
    let newOuterLayer :=
      newOuterLayer.toList
        |>.filter (fun n => isLocalDeclName n && !(g.contains n))

    return BFSState.mk g newOuterLayer
  )
    (BFSState.mk HashMap.emptyWithCapacity names)




  return state.g.toList


#synth ToJson (List (Name × List Name))

def writeJsonToFile (filePath : String) (json : Json) : IO Unit := do
  let jsonString := toString json
  IO.FS.withFile filePath IO.FS.Mode.write fun handle => do
    handle.putStr jsonString

-- Convert a Name to a String
def nameToString (n : Name) : String :=
  toString n


-- Convert a Name and List Name pair to JSON
def pairToJson (pair : Name × List Name) : TermElabM (Option Json) := do
  let nameStr := nameToString pair.fst
  let constCategoryStr ← try (getConstType pair.fst) catch | _ => return none
  -- Only serialize local-to-project edges.
  let nameListStr := (pair.snd.filter isLocalDeclName).map nameToString
  let constTypeStr ← getTypeStr pair.fst
  return Json.mkObj [("name", Json.str nameStr),("constCategory", Json.str constCategoryStr), ("constType", constTypeStr), ("references", Json.arr (nameListStr.map Json.str).toArray)]

-- Serialize a List (Name, List Name) to JSON
def serializeList (l : List (Name × List Name)) : TermElabM Json := do
  -- Drop any non-local nodes entirely.
  let res ← ((l.filter (fun p => isLocalDeclName p.fst)).filterMapM pairToJson)
  return Json.arr res.toArray

inductive Source
| Namespace (n : String)
| Constant (s : TermElabM Syntax)


def getConstsFromSource (s : Source) : TermElabM (List Name) := do
  match s with
  | Source.Namespace n => do
    (getAllConstsFromNamespace n)
  | Source.Constant snt => do
    let expr ← getExpr snt
    let name := expr.constName!
    return [name]


def serializeAndWriteToFile (source : Source) (depth : Nat) : TermElabM Unit := do
  let consts ← getConstsFromSource source
  let name ← match source with
    | Source.Namespace n => do
      pure n
    | Source.Constant s => do
      let expr ← getExpr s
      pure (expr.constName!).toString

  let g ← getUsedConstantGraph consts depth
  let js ←  serializeList g
  let _ ← writeJsonToFile ((toString name).append ".json") js


-- Edit and uncomment one of the lines below to get your .json file created in the current workspace folder

-- import Lean
-- import Lean.Data.Json.FromToJson
-- import Lean.Elab.BuiltinCommand
-- import Lean.Meta.Basic
-- import Lean.Message

-- import NorinVerification.fHat
-- set_option linter.hashCommand false

-- open Lean Elab Term Meta Std

-- /-- Adjust these to match the prefixes of declarations *defined in your file/project*. -/
-- def localNamePrefixes : List String := [
--   "NorinLemma8",                    -- your main namespace (from the screenshot)
--   "NorinVerification",             -- project prefix (safe to include)
--   "_private.NorinVerification.fHat" -- helper/anonymous decls created in fHat.lean
-- ]

-- /-- True iff `n` should count as "from my file/project". -/
-- def isLocalDeclName (n : Name) : Bool :=
--   let s := n.toString
--   localNamePrefixes.any (fun p => s.startsWith p)

/-- Optional: filter out autogenerated noise (you can comment this out). -/
def isProbablyUserFacing (n : Name) : Bool :=
  let s := n.toString
  -- Drop lots of compiler-generated names if you want cleaner lists:
  not (s.contains ".match_" || s.contains "._match_" || s.contains "rec_" || s.contains "casesOn" || s.contains "brecOn")

/-- Collect all declarations in the environment whose name matches your local prefix filter. -/
def getAllLocalDecls : TermElabM (Array Name) := do
  let env ← getEnv
  let mut acc : Array Name := #[]
  for (n, _) in env.constants.toList do
    if isLocalDeclName n && isProbablyUserFacing n then
      acc := acc.push n
  return acc

/-- Turn a graph `List (Name × List Name)` into the used-set (nodes ∪ deps). -/
def usedSetOfGraph (g : List (Name × List Name)) : HashSet Name :=
  g.foldl
    (fun s (p : Name × List Name) =>
      let s := s.insert p.fst
      s.insertMany p.snd)
    (HashSet.emptyWithCapacity)

/-- Write one name per line. -/
def writeNamesToFile (path : String) (names : Array Name) : IO Unit := do
  let content :=
    String.intercalate "\n" (names.toList.map (fun n => n.toString)) ++ "\n"
  IO.FS.writeFile path content

/--
Compute local used/unused declarations for a root theorem/definition.

`depth` should be reasonably large (20–80) or you'll misclassify used decls as unused.
-/
def writeUnusedForRoot
    (root : Source)
    (depth : Nat)
    (outBase : String)
    : TermElabM Unit := do

  let roots ← getConstsFromSource root
  let g ← getUsedConstantGraph roots depth
  let used := usedSetOfGraph g

  let allLocal ← getAllLocalDecls

  let usedLocal :=
    allLocal
      |>.filter (fun n => used.contains n)
      |>.qsort (fun a b => a.toString < b.toString)

  let unusedLocal :=
    allLocal
      |>.filter (fun n => !(used.contains n))
      |>.qsort (fun a b => a.toString < b.toString)

  -- Write results
  let _ ← writeNamesToFile (outBase ++ ".used.txt") usedLocal
  let _ ← writeNamesToFile (outBase ++ ".unused.txt") unusedLocal
  pure ()

/- Example invocation for your theorem: -/
#eval writeUnusedForRoot
  (Source.Constant `(NorinLemma8.Algo1.lemma8))
  30
  "NorinLemma8.Algo1.lemma8"
