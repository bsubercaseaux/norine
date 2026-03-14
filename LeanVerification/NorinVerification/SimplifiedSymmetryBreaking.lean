import NorinVerification.NorinSimplified
import NorinVerification.SymmetryBreaking

namespace NorinCNF
namespace SimplifiedSymmetryBreaking

open CNF

/-- Clauses produced by the simplified conjecture-2 antipodal generator. -/
def simplifiedConjecture2Clauses
    (n : Nat)
    (maxComparisons : Nat := 20)
    (firstVertexMinDegree : Bool := false) : List (Clause Nat) :=
  (NorinSimplified.buildSimplifiedConjecture2AntipodalState
      n maxComparisons firstVertexMinDegree).clauses.toList.map clauseOfDimacsArray

/--
Formula view of the simplified conjecture-2 antipodal generator
(`--simplified-conjecture2` in the CLI).
-/
def SimplifiedConjecture2Formula
    (n : Nat)
    (maxComparisons : Nat := 20)
    (firstVertexMinDegree : Bool := false) : Formula Nat :=
  {cl | cl ∈ simplifiedConjecture2Clauses n maxComparisons firstVertexMinDegree}

/-- Symmetry-breaking profile without first-vertex-min-degree side constraints. -/
abbrev SimplifiedConjecture2LexFormula
    (n : Nat) (maxComparisons : Nat := 20) : Formula Nat :=
  SimplifiedConjecture2Formula n maxComparisons false

/--
Generic reduction: if every `Ψ_n` model lifts to the simplified generated formula,
UNSAT of the generated formula implies the geodesic conjecture at `n`.
-/
theorem geodesicConjecture_of_simplifiedConjecture2_unsat
    (n : Nat)
    (maxComparisons : Nat := 20)
    (firstVertexMinDegree : Bool := false)
    (hLift :
      Satisfiable (Psi n) →
      Satisfiable (SimplifiedConjecture2Formula n maxComparisons firstVertexMinDegree))
    (hUnsat :
      ¬ Satisfiable (SimplifiedConjecture2Formula n maxComparisons firstVertexMinDegree)) :
    NorinGeodesicConjecture n := by
  apply geodesicConjecture_of_psi_unsat (n := n)
  intro hPsiSat
  exact hUnsat (hLift hPsiSat)

/--
Pure symmetry-breaking lift pattern for the simplified lex profile.

The only encoding-specific ingredient needed is `hLexSat`: a proof that a lex-leader
counterexample satisfies the generated simplified formula.
-/
theorem hLift_simplifiedLex_of_lexLeader
    (n : Nat) (hDim : 2 ≤ n)
    (maxComparisons : Nat := 20)
    (hLexSat :
      ∀ {c : EdgeColoring n},
        IsAntipodalColoring c →
        SymmetryBreaking.NoMonochromaticAntipodalGeodesic n c →
        SymmetryBreaking.LexLeaderCanonical n c →
        Satisfiable (SimplifiedConjecture2LexFormula n maxComparisons)) :
    Satisfiable (Psi n) →
    Satisfiable (SimplifiedConjecture2LexFormula n maxComparisons) := by
  intro hPsi
  rcases SymmetryBreaking.psi_counterexample_of_sat n hDim hPsi with ⟨c, hAnti, hNoGeo⟩
  rcases SymmetryBreaking.exists_lexLeader_representative (n := n) c with ⟨c', hEqv, hLex⟩
  have hPres :
      IsAntipodalColoring c' ∧ SymmetryBreaking.NoMonochromaticAntipodalGeodesic n c' :=
    SymmetryBreaking.symmetry_equivalent_preserves_counterexample
      (n := n) (c := c) (c' := c') hEqv hAnti hNoGeo
  exact hLexSat hPres.1 hPres.2 hLex

/--
Final UNSAT wrapper for the simplified lex profile, parameterized by the
encoding-specific lex-leader satisfiability lemma.
-/
theorem geodesicConjecture_of_simplifiedConjecture2_unsat_lex
    (n : Nat) (hDim : 2 ≤ n)
    (maxComparisons : Nat := 20)
    (hLexSat :
      ∀ {c : EdgeColoring n},
        IsAntipodalColoring c →
        SymmetryBreaking.NoMonochromaticAntipodalGeodesic n c →
        SymmetryBreaking.LexLeaderCanonical n c →
        Satisfiable (SimplifiedConjecture2LexFormula n maxComparisons))
    (hUnsat : ¬ Satisfiable (SimplifiedConjecture2LexFormula n maxComparisons)) :
    NorinGeodesicConjecture n := by
  apply geodesicConjecture_of_simplifiedConjecture2_unsat
    (n := n) (maxComparisons := maxComparisons) (firstVertexMinDegree := false)
  · exact hLift_simplifiedLex_of_lexLeader
      (n := n) hDim (maxComparisons := maxComparisons) hLexSat
  · exact hUnsat

/-- Encoding-specific lex-leader satisfiability for the simplified `maxComparisons = 20` profile. -/
theorem hLexSat_simplified20
    {n : Nat} {c : EdgeColoring n} :
    IsAntipodalColoring c →
    SymmetryBreaking.NoMonochromaticAntipodalGeodesic n c →
    SymmetryBreaking.LexLeaderCanonical n c →
    Satisfiable (SimplifiedConjecture2LexFormula n 20) := by
  intro hAnti hNoGeo hLex
  simpa [SimplifiedConjecture2LexFormula, SimplifiedConjecture2Formula, simplifiedConjecture2Clauses] using
    (SymmetryBreaking.simplified_sat_of_lexLeader_counterexample
      (n := n) (c := c) hAnti hNoGeo hLex)

/-- Instantiated lift theorem for the simplified lex profile with `maxComparisons = 20`. -/
theorem hLift_simplifiedLex20 (n : Nat) (hDim : 2 ≤ n) :
    Satisfiable (Psi n) → Satisfiable (SimplifiedConjecture2LexFormula n 20) := by
  exact hLift_simplifiedLex_of_lexLeader
    (n := n) hDim (maxComparisons := 20)
    (hLexSat := fun {c} hAnti hNoGeo hLex =>
      hLexSat_simplified20 (n := n) (c := c) hAnti hNoGeo hLex)

/-- Final UNSAT wrapper for the simplified lex profile at `maxComparisons = 20`. -/
theorem geodesicConjecture_of_simplifiedConjecture2_unsat_lex20
    (n : Nat) (hDim : 2 ≤ n)
    (hUnsat : ¬ Satisfiable (SimplifiedConjecture2LexFormula n 20)) :
    NorinGeodesicConjecture n := by
  exact geodesicConjecture_of_simplifiedConjecture2_unsat_lex
    (n := n) hDim (maxComparisons := 20)
    (hLexSat := fun {c} hAnti hNoGeo hLex =>
      hLexSat_simplified20 (n := n) (c := c) hAnti hNoGeo hLex)
    hUnsat

end SimplifiedSymmetryBreaking
end NorinCNF
