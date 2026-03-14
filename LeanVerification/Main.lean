import NorinVerification.NorinCNF
import NorinVerification.NorinSimplified

open NorinCNF
open NorinSimplified

def usage : String :=
  "Usage: lake exe NorinCNFGen -n <n> [--python-conjecture1 | --simplified-conjecture2]"

def parseN : List String → Except String Nat
  | [] => .error s!"Missing -n argument.\n{usage}"
  | "-n" :: nStr :: _ =>
      match nStr.toNat? with
      | some n => .ok n
      | none => .error s!"Invalid n: '{nStr}'. Expected a natural number."
  | "--n" :: nStr :: _ =>
      match nStr.toNat? with
      | some n => .ok n
      | none => .error s!"Invalid n: '{nStr}'. Expected a natural number."
  | arg :: rest =>
      if arg.startsWith "--n=" then
        let nStr := arg.drop 4
        match nStr.toNat? with
        | some n => .ok n
        | none => .error s!"Invalid n: '{nStr}'. Expected a natural number."
      else
        parseN rest

def writeBoth (n : Nat) : IO Unit := do
  let phiFile := s!"phi{n}.cnf"
  let psiFile := s!"psi{n}.cnf"
  IO.FS.writeFile phiFile (toDimacs .path n)
  IO.FS.writeFile psiFile (toDimacs .geodesic n)
  IO.println s!"Wrote {phiFile}"
  IO.println s!"Wrote {psiFile}"

def hasFlag (args : List String) (flag : String) : Bool :=
  args.any (· = flag)

def parseStringFlag (args : List String) (flag : String) : Option String :=
  match args with
  | [] => none
  | arg :: rest =>
      if arg = flag then
        match rest with
        | val :: _ => some val
        | [] => none
      else if arg.startsWith s!"{flag}=" then
        some ((arg.drop (flag.length + 1)).toString)
      else
        parseStringFlag rest flag

def parseNatFlag (args : List String) (flag : String) : Option Nat := do
  let s ← parseStringFlag args flag
  s.toNat?

def writePythonConjecture1 (n : Nat) : IO Unit := do
  let outFile := s!"n{n}.cnf"
  IO.FS.writeFile outFile (toDimacsPysatConjecture1AntipodalLexLeader n)
  IO.println s!"Wrote {outFile}"

def writeSimplifiedConjecture2Cli (n : Nat) (args : List String) : IO Unit := do
  let outFile := (parseStringFlag args "--tmp-file").getD "NorinSimplified.cnf"
  let maxComparisons := (parseNatFlag args "--partial-sym-break").getD 20
  let useFirstVertexMinDegree := hasFlag args "--first-vertex-min-degree"
  writeSimplifiedConjecture2 n outFile maxComparisons useFirstVertexMinDegree

def main (args : List String) : IO UInt32 := do
  match parseN args with
  | .ok n =>
      if hasFlag args "--simplified-conjecture2" then
        writeSimplifiedConjecture2Cli n args
      else if hasFlag args "--python-conjecture1" then
        writePythonConjecture1 n
      else
        writeBoth n
      pure 0
  | .error msg =>
      IO.eprintln msg
      pure 1
