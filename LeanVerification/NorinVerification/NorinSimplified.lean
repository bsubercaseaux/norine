import NorinVerification.NorinCNF

open NorinCNF

namespace NorinSimplified

/--
Eq. (1): if an edge `(u,v)` is red, then there is a monochromatic red reachability witness
from `u` to `v`.

This uses the antipodal-aware signed edge literal `rLitPy`, matching the Python context.
-/
def addMonoInitClausesPy (n : Nat) (vs : List VCode) : PyEncM Unit := do
  for u in vs do
    if vLt n (antipodeCode n u) u then
      pure ()
    else
      for v in neighborsCode n u do
        let ruv ← rLitPy n u v
        let puv ← pcLitPy true u v 0
        pushClausePy [-ruv, puv]

/--
Eq. (2): transitive propagation of monochromatic red reachability.

If `geodesicOnly = true`, we additionally enforce `dist(u,v)+1 = dist(u,w)`.
-/
def addMonoStepClausesPy (n : Nat) (vs : List VCode) (geodesicOnly : Bool) : PyEncM Unit := do
  for u in vs do
    if vLt n (antipodeCode n u) u then
      pure ()
    else
      for w in vs do
        if w ∈ neighborsCode n u then
          pure ()
        else
          for v in neighborsCode n w do
            let stepOk : Prop :=
              if geodesicOnly then
                distCode n u v + 1 = distCode n u w
              else
                True
            if stepOk then
              let puv ← pcLitPy true u v 0
              let rvw ← rLitPy n v w
              let puw ← pcLitPy true u w 0
              pushClausePy [-puv, -rvw, puw]
            else
              pure ()

/-- Forbid monochromatic red reachability from `u` to its antipode. -/
def addNoMonoAntipodeUnitClausesPy (n : Nat) (vs : List VCode) : PyEncM Unit := do
  for u in vs do
    if vLt n (antipodeCode n u) u then
      pure ()
    else
      let p ← pcLitPy true u (antipodeCode n u) 0
      pushClausePy [-p]

/--
Simplified conjecture-2 profile:
`--conjecture2 --antipodal-coloring` in the refactored Python structure,
plus optional symmetry-breaking and optional first-vertex-min-degree.
-/
def buildSimplifiedConjecture2AntipodalState
    (n : Nat)
    (maxComparisons : Nat := 20)
    (firstVertexMinDegree : Bool := false) : PyEncState :=
  ((do
    let vs := allVertexCodes n
    addEdgeInitClausesPy n vs
    addAntipodalClausesPy n vs
    addMonoInitClausesPy n vs
    addMonoStepClausesPy n vs true
    addNoMonoAntipodeUnitClausesPy n vs
    if maxComparisons = 0 then
      pure ()
    else
      addPartialSymBreakPy n vs maxComparisons
    if firstVertexMinDegree then
      addFirstVertexMinDegreePy n vs
    else
      pure ()
  ).run {}).2

/-- DIMACS for the simplified conjecture-2 antipodal profile. -/
def toDimacsSimplifiedConjecture2Antipodal
    (n : Nat)
    (maxComparisons : Nat := 20)
    (firstVertexMinDegree : Bool := false) : String :=
  let st := buildSimplifiedConjecture2AntipodalState n maxComparisons firstVertexMinDegree
  let numVars := st.nextId - 1
  let cls := st.clauses.toList
  let header := s!"p cnf {numVars} {cls.length}\n"
  header ++ String.intercalate "\n" (cls.map clauseLinePy) ++ "\n"

def writeSimplifiedConjecture2
    (n : Nat)
    (outFile : String)
    (maxComparisons : Nat := 20)
    (firstVertexMinDegree : Bool := false) : IO Unit := do
  IO.FS.writeFile outFile
    (toDimacsSimplifiedConjecture2Antipodal n maxComparisons firstVertexMinDegree)
  IO.println s!"Wrote {outFile}"

end NorinSimplified
