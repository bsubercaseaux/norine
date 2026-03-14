import NorinVerification.Cnf
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walks.Operations

/-!
Section-2 style CNF encoding for Norin's conjecture (finite cases), following
`Norin_CP (4).pdf`:

- `Φ n` encodes counterexamples to Conjecture 1 (monochromatic antipodal path).
- `Ψ n` encodes counterexamples to Conjecture 2 (monochromatic antipodal geodesic).

This file provides:
- the variable/literal scheme (`r_{u,v}` and `p_{u,v}` style),
- clause families (1), (2), and the antipode-forbidding unit clauses,
- DIMACS export helpers (including `n = 8`).
-/

namespace NorinCNF

open CNF
open ThreeColorSAT.Hypercube

abbrev Vertex (n : Nat) : Type := Fin n → Bool

/-- Antipodal vertex in `Q_n`. -/
def antipode {n : Nat} (v : Vertex n) : Vertex n :=
  fun i => !v i

/-- Numeric code used as a concrete lex ordering key on vertices. -/
def lexCode {n : Nat} (v : Vertex n) : Nat :=
  (List.finRange n).foldl (fun acc i => 2 * acc + (if v i then 1 else 0)) 0

/-- `u` is in the "lower" half: `u <_lex antipode(u)`. -/
def inLowerHalf {n : Nat} (u : Vertex n) : Prop :=
  lexCode u < lexCode (antipode u)

instance {n : Nat} (u : Vertex n) : Decidable (inLowerHalf u) := by
  unfold inLowerHalf
  infer_instance

/-- Order a pair according to `lexCode`. -/
def orderedPair {n : Nat} (u v : Vertex n) : Vertex n × Vertex n :=
  if lexCode u ≤ lexCode v then (u, v) else (v, u)

/-- Variables used by the Section 2 encoding. -/
inductive Var (n : Nat) : Type
  | edge  : Vertex n → Vertex n → Var n
  | reach : Vertex n → Vertex n → Var n
deriving DecidableEq

/-- Negate a CNF literal. -/
def litNeg {α : Type} : Lit α → Lit α
  | .pos a => .neg a
  | .neg a => .pos a

/-- Base edge variable `r_{u,v}` with ordered endpoints. -/
def rBaseVar {n : Nat} (u v : Vertex n) : Var n :=
  let p := orderedPair u v
  Var.edge p.1 p.2

/--
Literal-level representation of `r_{u,v}` with the antipodal-elimination convention:
if `antipode(v) <_lex u`, use `¬ r_{antipode(v), antipode(u)}`.
-/
def rLiteral {n : Nat} (u v : Vertex n) : Lit (Var n) :=
  let p := orderedPair u v
  let a := p.1
  let b := p.2
  if lexCode (antipode b) < lexCode a then
    .neg (Var.edge (antipode b) (antipode a))
  else
    .pos (Var.edge a b)

/-- Reachability variable `p_{u,v}`. -/
def pVar {n : Nat} (u v : Vertex n) : Var n :=
  Var.reach u v

def pPos {n : Nat} (u v : Vertex n) : Lit (Var n) :=
  .pos (pVar u v)

def pNeg {n : Nat} (u v : Vertex n) : Lit (Var n) :=
  .neg (pVar u v)

/-- Mode selecting `Φ_n` (paths) or `Ψ_n` (geodesics). -/
inductive Mode : Type
  | path
  | geodesic
deriving DecidableEq, Repr

instance : ToString Mode where
  toString
    | .path => "path"
    | .geodesic => "geodesic"

/-- Clause family (1): `r_{u,v} -> p_{u,v}`. -/
def clause1 {n : Nat} (u v : Vertex n) : Clause (Var n) :=
  [litNeg (rLiteral u v), pPos u v]

/-- Clause family (2): `(p_{u,v} ∧ r_{v,w}) -> p_{u,w}`. -/
def clause2 {n : Nat} (u v w : Vertex n) : Clause (Var n) :=
  [pNeg u v, litNeg (rLiteral v w), pPos u w]

/-- Unit clause forbidding red antipodal connection: `¬p_{v,antipode(v)}`. -/
def clauseNoAntipode {n : Nat} (v : Vertex n) : Clause (Var n) :=
  [pNeg v (antipode v)]

/-- Distance in `Q_n`. -/
def dist {n : Nat} (u v : Vertex n) : Nat :=
  hamming u v

/-- Adjacency in `Q_n`. -/
def Adj {n : Nat} (u v : Vertex n) : Prop :=
  (Q n).Adj u v

instance {n : Nat} : DecidableRel (@Adj n) := by
  intro u v
  dsimp [Adj]
  infer_instance

/-- Geodesic-only side condition used in `Ψ_n`. -/
def modeStepOk {n : Nat} (mode : Mode) (u v w : Vertex n) : Prop :=
  match mode with
  | .path => True
  | .geodesic => dist u v + 1 = dist u w

instance {n : Nat} (mode : Mode) (u v w : Vertex n) : Decidable (modeStepOk mode u v w) := by
  cases mode with
  | path =>
      simpa [modeStepOk] using (inferInstance : Decidable True)
  | geodesic =>
      simpa [modeStepOk] using (inferInstance : Decidable (dist u v + 1 = dist u w))

/-- Decode `m` into an `n`-bit vertex (little-endian coordinates). -/
def natToVertex (n m : Nat) : Vertex n :=
  fun i => Nat.testBit m i.1

/-- All vertices of `Q_n` as a list. -/
def allVertices (n : Nat) : List (Vertex n) :=
  (List.range (2 ^ n)).map (natToVertex n)

/-- Clause family (1) over all admissible pairs. -/
def clausesFamily1 (n : Nat) : List (Clause (Var n)) :=
  let vs := allVertices n
  let lower := vs.filter (fun u => decide (inLowerHalf u))
  List.flatMap
    (fun u =>
      let nbrs := vs.filter (fun v => decide (Adj u v))
      nbrs.map (fun v => clause1 u v))
    lower

/-- Clause family (2) over all admissible triples. -/
def clausesFamily2 (mode : Mode) (n : Nat) : List (Clause (Var n)) :=
  let vs := allVertices n
  let lower := vs.filter (fun u => decide (inLowerHalf u))
  List.flatMap
    (fun u =>
      List.flatMap
        (fun v =>
          let ws :=
            vs.filter (fun w =>
              decide (Adj v w ∧ ¬ Adj u w ∧ modeStepOk mode u v w))
          ws.map (fun w => clause2 u v w))
        vs)
    lower

/-- Unit clauses `¬p_{v,antipode(v)}` for `v <_lex antipode(v)`. -/
def clausesNoAntipode (n : Nat) : List (Clause (Var n)) :=
  let vs := allVertices n
  let lower := vs.filter (fun v => decide (inLowerHalf v))
  lower.map clauseNoAntipode

/-- Full clause list for Section-2 encoding. -/
def clauses (mode : Mode) (n : Nat) : List (Clause (Var n)) :=
  clausesFamily1 n ++ clausesFamily2 mode n ++ clausesNoAntipode n

/-- Set-formula view, compatible with the shared `CNF` API. -/
def formula (mode : Mode) (n : Nat) : Formula (Var n) :=
  {cl | cl ∈ clauses mode n}

/-- `Φ_n`: path version (Conjecture 1 counterexample encoding). -/
abbrev Phi (n : Nat) : Formula (Var n) :=
  formula .path n

/-- `Ψ_n`: geodesic version (Conjecture 2 counterexample encoding). -/
abbrev Psi (n : Nat) : Formula (Var n) :=
  formula .geodesic n

/-!
## Correctness Interface (Section 2)

These declarations capture the intended link with the paper's finite conjectures:

- `Φ_n` is UNSAT iff Conjecture 1 holds at `n` (monochromatic antipodal path).
- `Ψ_n` is UNSAT iff Conjecture 2 holds at `n` (monochromatic antipodal geodesic).

The theorems below are the requested implication direction
`UNSATISFIABLE -> conjecture is true for n`.
-/

/-- Undirected edges of `Q_n` (encoded as unordered pairs of vertices). -/
abbrev Edge (n : Nat) : Type := Sym2 (Vertex n)

/-- A (boolean) edge-coloring. -/
abbrev EdgeColoring (n : Nat) : Type := Edge n → Bool

/-- Unordered edge constructor from endpoints. -/
def edgeOf {n : Nat} (u v : Vertex n) : Edge n :=
  Sym2.mk (u, v)

/-- All edges of a walk have the same color. -/
def WalkMonochromatic {n : Nat} (c : EdgeColoring n) {u v : Vertex n}
    (p : (Q n).Walk u v) : Prop :=
  ∃ b : Bool, ∀ e : Edge n, e ∈ p.edges → c e = b

/-- All edges of a walk are red (`true`). -/
def WalkAllRed {n : Nat} (c : EdgeColoring n) {u v : Vertex n}
    (p : (Q n).Walk u v) : Prop :=
  ∀ e : Edge n, e ∈ p.edges → c e = true

/-- Antipodal-coloring condition from the paper. -/
def IsAntipodalColoring {n : Nat} (c : EdgeColoring n) : Prop :=
  ∀ u v : Vertex n, Adj u v →
    c (edgeOf u v) ≠ c (edgeOf (antipode u) (antipode v))

/-- Conjecture 1 at dimension `n`: monochromatic antipodal path exists. -/
def NorinPathConjecture (n : Nat) : Prop :=
  ∀ c : EdgeColoring n, IsAntipodalColoring c →
    ∃ v : Vertex n, ∃ p : (Q n).Walk v (antipode v), WalkMonochromatic c p

/-- Conjecture 2 at dimension `n`: monochromatic antipodal geodesic exists. -/
def NorinGeodesicConjecture (n : Nat) : Prop :=
  ∀ c : EdgeColoring n, IsAntipodalColoring c →
    ∃ v : Vertex n, ∃ p : (Q n).Walk v (antipode v),
      p.length = dist v (antipode v) ∧ WalkMonochromatic c p

lemma walkMonochromatic_of_allRed {n : Nat} (c : EdgeColoring n) {u v : Vertex n}
    {p : (Q n).Walk u v} (hRed : WalkAllRed c p) :
    WalkMonochromatic c p := by
  refine ⟨true, ?_⟩
  intro e he
  exact hRed e he

lemma dist_antipode {n : Nat} (v : Vertex n) :
    dist v (antipode v) = n := by
  simp [dist, ThreeColorSAT.Hypercube.hamming, antipode]

lemma hamming_antipode_eq {n : Nat} (u v : Vertex n) :
    ThreeColorSAT.Hypercube.hamming (antipode u) (antipode v) =
      ThreeColorSAT.Hypercube.hamming u v := by
  unfold ThreeColorSAT.Hypercube.hamming antipode
  congr
  ext i
  simp

lemma Adj_antipode {n : Nat} {u v : Vertex n} (h : Adj u v) :
    Adj (antipode u) (antipode v) := by
  dsimp [Adj] at h ⊢
  simpa [ThreeColorSAT.Hypercube.Q, hamming_antipode_eq (u := u) (v := v)] using h

lemma edgeOf_orderedPair_eq {n : Nat} (u v : Vertex n) :
    edgeOf (orderedPair u v).1 (orderedPair u v).2 = edgeOf u v := by
  unfold orderedPair
  split_ifs <;> simp [edgeOf, Sym2.eq_swap]

lemma edgeOf_antipode_orderedPair_eq {n : Nat} (u v : Vertex n) :
    edgeOf (antipode (orderedPair u v).2) (antipode (orderedPair u v).1) =
      edgeOf (antipode u) (antipode v) := by
  unfold orderedPair
  split_ifs <;> simp [edgeOf, Sym2.eq_swap]

/-- Assignment induced by edge colors only (reachability vars are set to `False`). -/
def edgeAssignment {n : Nat} (c : EdgeColoring n) : Assignment (Var n)
  | .edge u v => c (edgeOf u v) = true
  | .reach _ _ => False

/-- There is a nonempty red walk from `u` to `v`. -/
def RedWalkExists {n : Nat} (c : EdgeColoring n) (u v : Vertex n) : Prop :=
  ∃ p : (Q n).Walk u v, 0 < p.length ∧ WalkAllRed c p

/-- There is a red walk from `u` to `v` of length exactly `dist u v`. -/
def RedGeodesicExists {n : Nat} (c : EdgeColoring n) (u v : Vertex n) : Prop :=
  ∃ p : (Q n).Walk u v, p.length = dist u v ∧ WalkAllRed c p

/-- SAT assignment used for `Φ_n` (path mode). -/
def pathAssignment {n : Nat} (c : EdgeColoring n) : Assignment (Var n)
  | .edge u v => c (edgeOf u v) = true
  | .reach u v => RedWalkExists c u v

/-- SAT assignment used for `Ψ_n` (geodesic mode). -/
def geodesicAssignment {n : Nat} (c : EdgeColoring n) : Assignment (Var n)
  | .edge u v => c (edgeOf u v) = true
  | .reach u v => RedGeodesicExists c u v

lemma rLiteral_sat_iff_edge_red {n : Nat} (c : EdgeColoring n)
    (hAnti : IsAntipodalColoring c) {u v : Vertex n} (hAdj : Adj u v) :
    CNF.Lit.Sat (edgeAssignment c) (rLiteral u v) ↔ c (edgeOf u v) = true := by
  unfold rLiteral
  by_cases hlt :
      lexCode (antipode (orderedPair u v).2) < lexCode (orderedPair u v).1
  · simp [hlt]
    have hEqAnti :
        c (edgeOf (antipode (orderedPair u v).2) (antipode (orderedPair u v).1)) =
          c (edgeOf (antipode u) (antipode v)) := by
      simpa using congrArg c (edgeOf_antipode_orderedPair_eq (u := u) (v := v))
    have hNeUV : c (edgeOf u v) ≠ c (edgeOf (antipode u) (antipode v)) := hAnti u v hAdj
    have hNe :
        c (edgeOf (antipode (orderedPair u v).2) (antipode (orderedPair u v).1)) ≠
          c (edgeOf u v) := by
      intro hEq
      apply hNeUV
      calc
        c (edgeOf u v) = c (edgeOf (antipode (orderedPair u v).2) (antipode (orderedPair u v).1)) := hEq.symm
        _ = c (edgeOf (antipode u) (antipode v)) := hEqAnti
    have hComp :
        c (edgeOf (antipode (orderedPair u v).2) (antipode (orderedPair u v).1)) =
          !(c (edgeOf u v)) := by
      cases hA : c (edgeOf (antipode (orderedPair u v).2) (antipode (orderedPair u v).1)) <;>
        cases hU : c (edgeOf u v) <;>
        simp [hA, hU] at hNe ⊢
    calc
      CNF.Lit.Sat (edgeAssignment c)
          (Lit.neg (Var.edge (antipode (orderedPair u v).2) (antipode (orderedPair u v).1)))
          ↔ c (edgeOf (antipode (orderedPair u v).2) (antipode (orderedPair u v).1)) = false := by
              simp [CNF.Lit.Sat, edgeAssignment]
      _ ↔ c (edgeOf u v) = true := by
            rw [hComp]
            cases h : c (edgeOf u v) <;> simp [h]
  · simp [hlt]
    have hEq :
        c (edgeOf (orderedPair u v).1 (orderedPair u v).2) = c (edgeOf u v) := by
      simpa using congrArg c (edgeOf_orderedPair_eq (u := u) (v := v))
    calc
      CNF.Lit.Sat (edgeAssignment c) (Lit.pos (Var.edge (orderedPair u v).1 (orderedPair u v).2))
          ↔ c (edgeOf (orderedPair u v).1 (orderedPair u v).2) = true := by
              simp [CNF.Lit.Sat, edgeAssignment]
      _ ↔ c (edgeOf u v) = true := by simpa [hEq]

lemma rLiteral_sat_iff_edge_red_pathAssignment {n : Nat} (c : EdgeColoring n)
    (hAnti : IsAntipodalColoring c) {u v : Vertex n} (hAdj : Adj u v) :
    CNF.Lit.Sat (pathAssignment c) (rLiteral u v) ↔ c (edgeOf u v) = true := by
  have hEqSat :
      CNF.Lit.Sat (pathAssignment c) (rLiteral u v) ↔
        CNF.Lit.Sat (edgeAssignment c) (rLiteral u v) := by
    by_cases hcond : lexCode (antipode (orderedPair u v).2) < lexCode (orderedPair u v).1
    · simp [rLiteral, hcond, CNF.Lit.Sat, pathAssignment, edgeAssignment]
    · simp [rLiteral, hcond, CNF.Lit.Sat, pathAssignment, edgeAssignment]
  exact hEqSat.trans (rLiteral_sat_iff_edge_red (c := c) hAnti hAdj)

lemma litNeg_sat_iff_not_sat {α : Type} (τ : Assignment α) (l : Lit α) :
    CNF.Lit.Sat τ (litNeg l) ↔ ¬ CNF.Lit.Sat τ l := by
  cases l <;> simp [litNeg, CNF.Lit.Sat]

lemma sat_clause1_path {n : Nat} (c : EdgeColoring n) (hAnti : IsAntipodalColoring c)
    {u v : Vertex n} (hAdj : Adj u v) :
    CNF.Clause.Sat (pathAssignment c) (clause1 u v) := by
  unfold clause1 CNF.Clause.Sat
  by_cases hRed : c (edgeOf u v) = true
  · refine ⟨pPos u v, by simp [pPos], ?_⟩
    refine ⟨hAdj.toWalk, by simp, ?_⟩
    intro e he
    have hEdge : e = edgeOf u v := by simpa [edgeOf] using he
    simpa [hEdge] using hRed
  · refine ⟨litNeg (rLiteral u v), by simp [litNeg], ?_⟩
    have hNotSat : ¬ CNF.Lit.Sat (pathAssignment c) (rLiteral u v) := by
      intro hSat
      exact hRed ((rLiteral_sat_iff_edge_red_pathAssignment (c := c) hAnti hAdj).1 hSat)
    exact (litNeg_sat_iff_not_sat (τ := pathAssignment c) (l := rLiteral u v)).2 hNotSat

lemma sat_clause2_path {n : Nat} (c : EdgeColoring n) (hAnti : IsAntipodalColoring c)
    {u v w : Vertex n} (hAdjVW : Adj v w) :
    CNF.Clause.Sat (pathAssignment c) (clause2 u v w) := by
  unfold clause2 CNF.Clause.Sat
  by_cases hReach : pathAssignment c (.reach u v)
  · by_cases hRedLit : CNF.Lit.Sat (pathAssignment c) (rLiteral v w)
    · refine ⟨pPos u w, by simp [pPos], ?_⟩
      rcases hReach with ⟨p, hpLen, hpRed⟩
      have hRedEdge : c (edgeOf v w) = true :=
        (rLiteral_sat_iff_edge_red_pathAssignment (c := c) hAnti hAdjVW).1 hRedLit
      refine ⟨p.append hAdjVW.toWalk, ?_, ?_⟩
      · rw [SimpleGraph.Walk.length_append]
        simpa using hpLen
      · intro e he
        rw [SimpleGraph.Walk.edges_append] at he
        rcases List.mem_append.mp he with he | he
        · exact hpRed e he
        · have hEdge : e = edgeOf v w := by simpa [edgeOf] using he
          simpa [hEdge] using hRedEdge
    · refine ⟨litNeg (rLiteral v w), by simp [litNeg], ?_⟩
      exact (litNeg_sat_iff_not_sat (τ := pathAssignment c) (l := rLiteral v w)).2 hRedLit
  · refine ⟨pNeg u v, by simp [pNeg], ?_⟩
    simpa [pNeg, CNF.Lit.Sat] using hReach

lemma sat_clauseNoAntipode_path {n : Nat} (c : EdgeColoring n)
    (hNoMono : ∀ v : Vertex n, ∀ p : (Q n).Walk v (antipode v), ¬ WalkMonochromatic c p)
    (v : Vertex n) :
    CNF.Clause.Sat (pathAssignment c) (clauseNoAntipode v) := by
  unfold clauseNoAntipode CNF.Clause.Sat
  refine ⟨pNeg v (antipode v), by simp [pNeg], ?_⟩
  have hNoRed : ¬ RedWalkExists c v (antipode v) := by
    intro hRed
    rcases hRed with ⟨p, _hpLen, hpAllRed⟩
    exact hNoMono v p (walkMonochromatic_of_allRed (c := c) hpAllRed)
  simpa [pNeg, CNF.Lit.Sat, pathAssignment] using hNoRed

theorem phi_satisfiable_of_counterexample {n : Nat} (c : EdgeColoring n)
    (hAnti : IsAntipodalColoring c)
    (hNoMono : ∀ v : Vertex n, ∀ p : (Q n).Walk v (antipode v), ¬ WalkMonochromatic c p) :
    Satisfiable (Phi n) := by
  refine ⟨pathAssignment c, ?_⟩
  intro cl hcl
  have hmem : cl ∈ clauses .path n := by
    simpa [Phi, formula] using hcl
  have hsplit :
      cl ∈ clausesFamily1 n ∨ cl ∈ clausesFamily2 .path n ∨ cl ∈ clausesNoAntipode n := by
    simpa [clauses, List.mem_append, or_assoc] using hmem
  rcases hsplit with hFam1 | hRest
  · rcases List.mem_flatMap.1 hFam1 with ⟨u, _huLower, huMap⟩
    rcases List.mem_map.1 huMap with ⟨v, hvNbr, rfl⟩
    have hAdj : Adj u v := by
      exact (decide_eq_true_eq.mp ((List.mem_filter.1 hvNbr).2))
    exact sat_clause1_path (c := c) hAnti hAdj
  · rcases hRest with hFam2 | hNo
    · rcases List.mem_flatMap.1 hFam2 with ⟨u, _huLower, huFlat⟩
      rcases List.mem_flatMap.1 huFlat with ⟨v, _hvVs, hvMap⟩
      rcases List.mem_map.1 hvMap with ⟨w, hwWs, rfl⟩
      have hAdjVW : Adj v w := (decide_eq_true_eq.mp ((List.mem_filter.1 hwWs).2)).1
      exact sat_clause2_path (c := c) hAnti hAdjVW
    · rcases List.mem_map.1 hNo with ⟨v, _hvLower, rfl⟩
      exact sat_clauseNoAntipode_path (c := c) hNoMono v

/-- If `Φ_n` is UNSAT, then Norin's path conjecture holds at dimension `n`. -/
theorem pathConjecture_of_phi_unsat (n : Nat)
    (hUnsat : ¬ Satisfiable (Phi n)) :
    NorinPathConjecture n := by
  intro c hAnti
  by_contra hNo
  have hNoMono :
      ∀ v : Vertex n, ∀ p : (Q n).Walk v (antipode v), ¬ WalkMonochromatic c p := by
    intro v p hpMono
    exact hNo ⟨v, p, hpMono⟩
  exact hUnsat (phi_satisfiable_of_counterexample (n := n) c hAnti hNoMono)

theorem phi_satisfiable_of_not_pathConjecture (n : Nat)
    (hNot : ¬ NorinPathConjecture n) :
    Satisfiable (Phi n) := by
  classical
  simp [NorinPathConjecture] at hNot
  rcases hNot with ⟨c, hAnti, hNoMono⟩
  exact phi_satisfiable_of_counterexample (n := n) c hAnti hNoMono

lemma rLiteral_sat_iff_edge_red_geodesicAssignment {n : Nat} (c : EdgeColoring n)
    (hAnti : IsAntipodalColoring c) {u v : Vertex n} (hAdj : Adj u v) :
    CNF.Lit.Sat (geodesicAssignment c) (rLiteral u v) ↔ c (edgeOf u v) = true := by
  have hEqSat :
      CNF.Lit.Sat (geodesicAssignment c) (rLiteral u v) ↔
        CNF.Lit.Sat (edgeAssignment c) (rLiteral u v) := by
    by_cases hcond : lexCode (antipode (orderedPair u v).2) < lexCode (orderedPair u v).1
    · simp [rLiteral, hcond, CNF.Lit.Sat, geodesicAssignment, edgeAssignment]
    · simp [rLiteral, hcond, CNF.Lit.Sat, geodesicAssignment, edgeAssignment]
  exact hEqSat.trans (rLiteral_sat_iff_edge_red (c := c) hAnti hAdj)

lemma sat_clause1_geodesic {n : Nat} (c : EdgeColoring n) (hAnti : IsAntipodalColoring c)
    {u v : Vertex n} (hAdj : Adj u v) :
    CNF.Clause.Sat (geodesicAssignment c) (clause1 u v) := by
  unfold clause1 CNF.Clause.Sat
  by_cases hRed : c (edgeOf u v) = true
  · refine ⟨pPos u v, by simp [pPos], ?_⟩
    have hDist : dist u v = 1 := by
      simpa [dist, Adj, ThreeColorSAT.Hypercube.Q] using hAdj
    refine ⟨hAdj.toWalk, ?_, ?_⟩
    · simpa [hDist] using (SimpleGraph.Walk.length_eq_one_iff.mpr hAdj)
    · intro e he
      have hEdge : e = edgeOf u v := by simpa [edgeOf] using he
      simpa [hEdge] using hRed
  · refine ⟨litNeg (rLiteral u v), by simp [litNeg], ?_⟩
    have hNotSat : ¬ CNF.Lit.Sat (geodesicAssignment c) (rLiteral u v) := by
      intro hSat
      exact hRed ((rLiteral_sat_iff_edge_red_geodesicAssignment (c := c) hAnti hAdj).1 hSat)
    exact (litNeg_sat_iff_not_sat (τ := geodesicAssignment c) (l := rLiteral u v)).2 hNotSat

lemma sat_clause2_geodesic {n : Nat} (c : EdgeColoring n) (hAnti : IsAntipodalColoring c)
    {u v w : Vertex n} (hAdjVW : Adj v w) (hStep : dist u v + 1 = dist u w) :
    CNF.Clause.Sat (geodesicAssignment c) (clause2 u v w) := by
  unfold clause2 CNF.Clause.Sat
  by_cases hReach : geodesicAssignment c (.reach u v)
  · by_cases hRedLit : CNF.Lit.Sat (geodesicAssignment c) (rLiteral v w)
    · refine ⟨pPos u w, by simp [pPos], ?_⟩
      rcases hReach with ⟨p, hpLen, hpRed⟩
      have hRedEdge : c (edgeOf v w) = true :=
        (rLiteral_sat_iff_edge_red_geodesicAssignment (c := c) hAnti hAdjVW).1 hRedLit
      refine ⟨p.append hAdjVW.toWalk, ?_, ?_⟩
      · rw [SimpleGraph.Walk.length_append, hpLen]
        simpa [hStep]
      · intro e he
        rw [SimpleGraph.Walk.edges_append] at he
        rcases List.mem_append.mp he with he | he
        · exact hpRed e he
        · have hEdge : e = edgeOf v w := by simpa [edgeOf] using he
          simpa [hEdge] using hRedEdge
    · refine ⟨litNeg (rLiteral v w), by simp [litNeg], ?_⟩
      exact (litNeg_sat_iff_not_sat (τ := geodesicAssignment c) (l := rLiteral v w)).2 hRedLit
  · refine ⟨pNeg u v, by simp [pNeg], ?_⟩
    simpa [pNeg, CNF.Lit.Sat] using hReach

lemma sat_clauseNoAntipode_geodesic {n : Nat} (c : EdgeColoring n)
    (hNoGeo : ∀ v : Vertex n, ∀ p : (Q n).Walk v (antipode v),
      p.length = dist v (antipode v) → ¬ WalkMonochromatic c p)
    (v : Vertex n) :
    CNF.Clause.Sat (geodesicAssignment c) (clauseNoAntipode v) := by
  unfold clauseNoAntipode CNF.Clause.Sat
  refine ⟨pNeg v (antipode v), by simp [pNeg], ?_⟩
  have hNoRedGeo : ¬ RedGeodesicExists c v (antipode v) := by
    intro hRed
    rcases hRed with ⟨p, hpLen, hpAllRed⟩
    exact hNoGeo v p hpLen (walkMonochromatic_of_allRed (c := c) hpAllRed)
  simpa [pNeg, CNF.Lit.Sat, geodesicAssignment] using hNoRedGeo

theorem psi_satisfiable_of_counterexample {n : Nat} (c : EdgeColoring n)
    (hAnti : IsAntipodalColoring c)
    (hNoGeo : ∀ v : Vertex n, ∀ p : (Q n).Walk v (antipode v),
      p.length = dist v (antipode v) → ¬ WalkMonochromatic c p) :
    Satisfiable (Psi n) := by
  refine ⟨geodesicAssignment c, ?_⟩
  intro cl hcl
  have hmem : cl ∈ clauses .geodesic n := by
    simpa [Psi, formula] using hcl
  have hsplit :
      cl ∈ clausesFamily1 n ∨ cl ∈ clausesFamily2 .geodesic n ∨ cl ∈ clausesNoAntipode n := by
    simpa [clauses, List.mem_append, or_assoc] using hmem
  rcases hsplit with hFam1 | hRest
  · rcases List.mem_flatMap.1 hFam1 with ⟨u, _huLower, huMap⟩
    rcases List.mem_map.1 huMap with ⟨v, hvNbr, rfl⟩
    have hAdj : Adj u v := decide_eq_true_eq.mp ((List.mem_filter.1 hvNbr).2)
    exact sat_clause1_geodesic (c := c) hAnti hAdj
  · rcases hRest with hFam2 | hNo
    · rcases List.mem_flatMap.1 hFam2 with ⟨u, _huLower, huFlat⟩
      rcases List.mem_flatMap.1 huFlat with ⟨v, _hvVs, hvMap⟩
      rcases List.mem_map.1 hvMap with ⟨w, hwWs, rfl⟩
      have hPred : Adj v w ∧ ¬ Adj u w ∧ modeStepOk .geodesic u v w :=
        decide_eq_true_eq.mp ((List.mem_filter.1 hwWs).2)
      have hAdjVW : Adj v w := hPred.1
      have hStep : dist u v + 1 = dist u w := by
        simpa [modeStepOk] using hPred.2.2
      exact sat_clause2_geodesic (c := c) hAnti hAdjVW hStep
    · rcases List.mem_map.1 hNo with ⟨v, _hvLower, rfl⟩
      exact sat_clauseNoAntipode_geodesic (c := c) hNoGeo v

/-- If `Ψ_n` is UNSAT, then Norin's geodesic conjecture holds at dimension `n`. -/
theorem geodesicConjecture_of_psi_unsat (n : Nat)
    (hUnsat : ¬ Satisfiable (Psi n)) :
    NorinGeodesicConjecture n := by
  intro c hAnti
  by_contra hNo
  have hNoGeo :
      ∀ v : Vertex n, ∀ p : (Q n).Walk v (antipode v),
        p.length = dist v (antipode v) → ¬ WalkMonochromatic c p := by
    intro v p hpLen hpMono
    exact hNo ⟨v, p, hpLen, hpMono⟩
  exact hUnsat (psi_satisfiable_of_counterexample (n := n) c hAnti hNoGeo)

theorem psi_satisfiable_of_not_geodesicConjecture (n : Nat)
    (hNot : ¬ NorinGeodesicConjecture n) :
    Satisfiable (Psi n) := by
  classical
  simp [NorinGeodesicConjecture] at hNot
  rcases hNot with ⟨c, hAnti, hNoGeo⟩
  exact psi_satisfiable_of_counterexample (n := n) c hAnti hNoGeo

/-- Number of vertices in `Q_n`. -/
def numVertices (n : Nat) : Nat :=
  2 ^ n

/-- Pair-code for vertex pairs (used by DIMACS variable numbering). -/
def pairCode {n : Nat} (u v : Vertex n) : Nat :=
  lexCode u * numVertices n + lexCode v

/-- DIMACS variable id (1-based). -/
def varId {n : Nat} : Var n → Nat
  | .edge u v => pairCode u v + 1
  | .reach u v => numVertices n * numVertices n + pairCode u v + 1

/-- Upper bound used in DIMACS header (`p cnf`). -/
def numVars (n : Nat) : Nat :=
  2 * numVertices n * numVertices n

/-- Convert a literal to DIMACS signed integer. -/
def litToInt {n : Nat} : Lit (Var n) → Int
  | .pos a => Int.ofNat (varId (n := n) a)
  | .neg a => -Int.ofNat (varId (n := n) a)

/-- Render one clause line (ending with `0`). -/
def clauseLine {n : Nat} (cl : Clause (Var n)) : String :=
  let xs := cl.map (fun l => toString (litToInt (n := n) l))
  String.intercalate " " xs ++ " 0"

/-- DIMACS text for the selected Section-2 encoding mode. -/
def toDimacs (mode : Mode) (n : Nat) : String :=
  let cls := clauses mode n
  let header :=
    s!"c Norin Section-2 encoding ({mode}) for Q_{n}\n" ++
    s!"p cnf {numVars n} {cls.length}\n"
  header ++ String.intercalate "\n" (cls.map (clauseLine (n := n))) ++ "\n"

/-- Convenience output for `Φ_8`. -/
def phi8Dimacs : String :=
  toDimacs .path 8

/-- Convenience output for `Ψ_8`. -/
def psi8Dimacs : String :=
  toDimacs .geodesic 8

/-- Print `Φ_8` to stdout. -/
def printPhi8 : IO Unit :=
  IO.println phi8Dimacs

/-- Print `Ψ_8` to stdout. -/
def printPsi8 : IO Unit :=
  IO.println psi8Dimacs

/-!
## Python-compatible encoder (`norine_general_pysat.py`)

The functions below mirror exactly the clause-generation order and variable-allocation
scheme of:

`python3 enc/norine_general_pysat.py -n N --conjecture1 --antipodal-coloring --no-solve`

including:
- the initial tautological edge-variable clauses,
- antipodal edge-coloring equalities,
- Eq. 5 / 7 / 9 / conjecture1 unit clauses (with `S = [0]`),
- partial symmetry breaking with `maxcomparisons = 20`,
-/

abbrev VCode := Nat

def allVertexCodes (n : Nat) : List VCode :=
  List.range (2 ^ n)

def bitAt (u i : Nat) : Bool :=
  Nat.testBit u i

def lexCodeNat (n : Nat) (u : VCode) : Nat :=
  (List.range n).foldl (fun acc i => 2 * acc + (if bitAt u i then 1 else 0)) 0

def vLt (n : Nat) (u v : VCode) : Bool :=
  lexCodeNat n u < lexCodeNat n v

def vLe (n : Nat) (u v : VCode) : Bool :=
  lexCodeNat n u ≤ lexCodeNat n v

def antipodeCode (n : Nat) (u : VCode) : VCode :=
  (2 ^ n - 1) - u

def toggleBit (u i : Nat) : Nat :=
  u ^^^ 2 ^ i

def flipCode (u i : Nat) : VCode :=
  toggleBit u i

def swapCode (u i j : Nat) : VCode :=
  if bitAt u i = bitAt u j then u else toggleBit (toggleBit u i) j

def neighborsCode (n : Nat) (u : VCode) : List VCode :=
  (List.range n).map (fun i => flipCode u i)

def distCode (n : Nat) (u v : VCode) : Nat :=
  (List.range n).foldl
    (fun acc i => if bitAt u i = bitAt v i then acc else acc + 1)
    0

inductive PyVarKey : Type
  | r (u v : VCode)
  | pc (isRed : Bool) (u v s : Nat)
deriving DecidableEq, BEq, Hashable, ReflBEq, LawfulBEq, Repr

structure PyEncState where
  nextId : Nat := 1
  namedIds : Std.HashMap PyVarKey Nat := {}
  idToNamed : Std.HashMap Nat PyVarKey := {}
  clauses : Array (Array Int) := #[]

abbrev PyEncM := StateM PyEncState

def pushClausePy (cl : List Int) : PyEncM Unit :=
  modify fun st => { st with clauses := st.clauses.push cl.toArray }

def freshIdPy : PyEncM Nat := do
  let st ← get
  let i := st.nextId
  set { st with nextId := i + 1 }
  pure i

def idForPy (k : PyVarKey) : PyEncM Nat := do
  let st ← get
  match st.namedIds.get? k with
  | some i => pure i
  | none =>
      let i := st.nextId
      set { st with
        nextId := i + 1
        namedIds := st.namedIds.insert k i
        idToNamed := st.idToNamed.insert i k
      }
      pure i

def orderedCodePair (n : Nat) (u v : VCode) : VCode × VCode :=
  if vLe n u v then (u, v) else (v, u)

def rOldIdPy (n : Nat) (u v : VCode) : PyEncM Nat := do
  let p := orderedCodePair n u v
  idForPy (.r p.1 p.2)

def rLitPy (n : Nat) (u v : VCode) : PyEncM Int := do
  let p := orderedCodePair n u v
  let a := p.1
  let b := p.2
  if vLt n a (antipodeCode n b) then
    return Int.ofNat (← rOldIdPy n a b)
  else
    return -Int.ofNat (← rOldIdPy n (antipodeCode n a) (antipodeCode n b))

def pcIdPy (isRed : Bool) (u v s : Nat) : PyEncM Nat :=
  idForPy (.pc isRed u v s)

def pcLitPy (isRed : Bool) (u v s : Nat) : PyEncM Int :=
  return Int.ofNat (← pcIdPy isRed u v s)

def addEdgeInitClausesPy (n : Nat) (vs : List VCode) : PyEncM Unit := do
  for u in vs do
    for v in neighborsCode n u do
      let rid ← rOldIdPy n u v
      let r := Int.ofNat rid
      pushClausePy [r, -r]

def addAntipodalClausesPy (n : Nat) (vs : List VCode) : PyEncM Unit := do
  for u in vs do
    for v in neighborsCode n u do
      if vLt n v u then
        pure ()
      else
        let ruv ← rOldIdPy n u v
        let rauv ← rOldIdPy n (antipodeCode n u) (antipodeCode n v)
        pushClausePy [-Int.ofNat ruv, -Int.ofNat rauv]
        pushClausePy [Int.ofNat ruv, Int.ofNat rauv]

def addEq5ClausesPy (n : Nat) (vs : List VCode) : PyEncM Unit := do
  for u in vs do
    if vLt n (antipodeCode n u) u then
      pure ()
    else
      for v in neighborsCode n u do
        let ruv ← rLitPy n u v
        let p ← pcLitPy true u v 0
        pushClausePy [-ruv, p]

def addEq7Eq9ClausesPy (n : Nat) (vs : List VCode) : PyEncM Unit := do
  for u in vs do
    if vLt n (antipodeCode n u) u then
      pure ()
    else
      for w in vs do
        if w ∈ neighborsCode n u then
          pure ()
        else
          for v in neighborsCode n w do
            if distCode n u v + 1 = distCode n u w then
              let puv ← pcLitPy true u v 0
              let rvw ← rLitPy n v w
              let puw ← pcLitPy true u w 0
              pushClausePy [-puv, -rvw, puw]
              if 0 < n - 1 then
                let buw ← pcLitPy false u w 1
                pushClausePy [-puv, rvw, buw]
              else
                pure ()
            else
              pure ()

def addConjecture1UnitClausesPy (n : Nat) (vs : List VCode) : PyEncM Unit := do
  for u in vs do
    if vLt n (antipodeCode n u) u then
      pure ()
    else
      let p ← pcLitPy true u (antipodeCode n u) 0
      pushClausePy [-p]

def originalSignedEdgesPy (n : Nat) (vs : List VCode) : List (VCode × VCode) :=
  List.flatMap
    (fun u =>
      (neighborsCode n u).filterMap (fun v =>
        if vLt n u v then some (u, v) else none))
    vs

def lexSmallerEqLoopPy (maxComparisons : Option Nat) :
    List Int → List Int → Nat → Nat → PyEncM Unit
  | [], [], _, _ =>
      pure ()
  | x :: xt, y :: yt, allPrevNow, rcnt =>
      if x = y then
        lexSmallerEqLoopPy maxComparisons xt yt allPrevNow rcnt
      else
        let rcnt' := rcnt + 1
        let allPrevLit := Int.ofNat allPrevNow
        do
          pushClausePy [-allPrevLit, -x, y]
          let allPrevNew ← freshIdPy
          let allPrevNewLit := Int.ofNat allPrevNew
          pushClausePy [-allPrevLit, -x, allPrevNewLit]
          pushClausePy [-allPrevLit, y, allPrevNewLit]
          match maxComparisons with
          | none =>
              lexSmallerEqLoopPy maxComparisons xt yt allPrevNew rcnt'
          | some m =>
              if rcnt' > m then
                pure ()
              else
                lexSmallerEqLoopPy maxComparisons xt yt allPrevNew rcnt'
  | _, _, _, _ =>
      pure ()

def lexSmallerEqPy (maxComparisons : Option Nat) (seq1 seq2 : List Int) : PyEncM Unit := do
  let allPrev ← freshIdPy
  pushClausePy [Int.ofNat allPrev]
  lexSmallerEqLoopPy maxComparisons seq1 seq2 allPrev 0

def natPairsIncreasing (n : Nat) : List (Nat × Nat) :=
  List.flatMap
    (fun i =>
      (List.range n).filterMap (fun j => if i < j then some (i, j) else none))
    (List.range n)

def edgeSeqPy (n : Nat) (es : List (VCode × VCode)) : PyEncM (List Int) :=
  es.mapM (fun (u, v) => rLitPy n u v)

def addPartialSymBreakPy (n : Nat) (vs : List VCode) (maxComparisons : Nat) : PyEncM Unit := do
  let originalEdges := originalSignedEdgesPy n vs
  for i in List.range n do
    let permuted := originalEdges.map (fun (u, v) => (flipCode u i, flipCode v i))
    let lhs ← edgeSeqPy n originalEdges
    let rhs ← edgeSeqPy n permuted
    lexSmallerEqPy none lhs rhs
  let pairs := natPairsIncreasing n
  for (i, j) in pairs do
    let permuted := originalEdges.map (fun (u, v) => (swapCode u i j, swapCode v i j))
    let lhs ← edgeSeqPy n originalEdges
    let rhs ← edgeSeqPy n permuted
    lexSmallerEqPy (some maxComparisons) lhs rhs
  for (i, j) in pairs do
    for k in List.range n do
      let permuted :=
        originalEdges.map
          (fun (u, v) => (swapCode (flipCode u k) i j, swapCode (flipCode v k) i j))
      let lhs ← edgeSeqPy n originalEdges
      let rhs ← edgeSeqPy n permuted
      lexSmallerEqPy (some maxComparisons) lhs rhs

def seqCounterPy (varsIn : List Int) (countUpto : Nat) : PyEncM (List Int) := do
  let n := varsIn.length
  let mut counter : Array (Array Int) := #[]
  for _ in List.range n do
    let mut row : Array Int := #[]
    for _ in List.range countUpto do
      let v ← freshIdPy
      row := row.push (Int.ofNat v)
    counter := counter.push row
  if n = 0 then
    pure []
  else
    if countUpto = 0 then
      pure []
    else
      let vars := varsIn.toArray
      let row0 := (counter[0]!).set! 0 (vars[0]!)
      counter := counter.set! 0 row0
      for i in List.range countUpto do
        if i = 0 then
          pure ()
        else
          pushClausePy [-(counter[0]!)[i]!]
      for i in List.range (n - 1) do
        pushClausePy [-(vars[i + 1]!), (counter[i + 1]!)[0]!]
        for j in List.range countUpto do
          let cij := (counter[i]!)[j]!
          let ci1j := (counter[i + 1]!)[j]!
          pushClausePy [-cij, ci1j]
          pushClausePy [cij, vars[i + 1]!, -ci1j]
          if j < countUpto - 1 then
            let ci1j1 := (counter[i + 1]!)[j + 1]!
            pushClausePy [-cij, -(vars[i + 1]!), ci1j1]
            pushClausePy [cij, -ci1j1]
          else
            pure ()
      pure ((counter[n - 1]!).toList)

def addFirstVertexMinDegreePy (n : Nat) (vs : List VCode) : PyEncM Unit := do
  if n = 0 then
    pure ()
  else
    let first := vs[0]!
    let vars0 ← (neighborsCode n first).mapM (fun v => rLitPy n first v)
    let count0 := (← seqCounterPy vars0 n).toArray
    for v in vs.drop 1 do
      let vars ← (neighborsCode n v).mapM (fun u => rLitPy n v u)
      let count := (← seqCounterPy vars n).toArray
      for i in List.range n do
        pushClausePy [-(count0[i]!), count[i]!]

/-- Python profile: `--conjecture1 --antipodal-coloring` (with default partial SB 20). -/
def buildPysatConjecture1AntipodalLexState (n : Nat)
    (maxComparisons : Nat := 20) : PyEncState :=
  ((do
    let vs := allVertexCodes n
    addEdgeInitClausesPy n vs
    addAntipodalClausesPy n vs
    addEq5ClausesPy n vs
    addEq7Eq9ClausesPy n vs
    addConjecture1UnitClausesPy n vs
    if maxComparisons = 0 then
      pure ()
    else
      addPartialSymBreakPy n vs maxComparisons).run {}).2

/- Legacy/profile helper that also adds `--first-vertex-min-degree`. -/
def buildPysatConjecture1AntipodalFirstVertexMinDegreeState (n : Nat)
    (maxComparisons : Nat := 20) : PyEncState :=
  ((do
    let vs := allVertexCodes n
    addEdgeInitClausesPy n vs
    addAntipodalClausesPy n vs
    addEq5ClausesPy n vs
    addEq7Eq9ClausesPy n vs
    addConjecture1UnitClausesPy n vs
    if maxComparisons = 0 then
      pure ()
    else
      addPartialSymBreakPy n vs maxComparisons
    addFirstVertexMinDegreePy n vs).run {}).2

def clauseLinePy (cl : Array Int) : String :=
  let xs := cl.toList.map toString
  String.intercalate " " xs ++ " 0"

/-- DIMACS exactly matching `norine_general_pysat.py` for:
`--conjecture1 --antipodal-coloring` (with default partial SB 20). -/
def toDimacsPysatConjecture1AntipodalLexLeader (n : Nat) : String :=
  let st := buildPysatConjecture1AntipodalLexState n
  let numVars := st.nextId - 1
  let cls := st.clauses.toList
  let header := s!"p cnf {numVars} {cls.length}\n"
  header ++ String.intercalate "\n" (cls.map clauseLinePy) ++ "\n"

/-- Interpret a DIMACS signed literal as a `CNF.Lit Nat` (variable ids are positive naturals). -/
def litOfDimacsInt (i : Int) : Lit Nat :=
  if i < 0 then Lit.neg i.natAbs else Lit.pos i.toNat

def clauseOfDimacsArray (cl : Array Int) : Clause Nat :=
  cl.toList.map litOfDimacsInt

def pysatConjecture1Clauses (n : Nat) : List (Clause Nat) :=
  (buildPysatConjecture1AntipodalLexState n).clauses.toList.map clauseOfDimacsArray

/-- Formula corresponding to the Python-compatible `--conjecture1 --antipodal-coloring` CNF. -/
def PysatConjecture1Formula (n : Nat) : Formula Nat :=
  {cl | cl ∈ pysatConjecture1Clauses n}

/--
Reduction theorem: if every `Ψ_n` model can be lifted to a model of the Python-compatible
Conjecture-1 encoding, then UNSAT of that encoding implies the geodesic conjecture at `n`.
-/
theorem geodesicConjecture_of_pysatConjecture1_unsat
    (n : Nat)
    (hLift : Satisfiable (Psi n) → Satisfiable (PysatConjecture1Formula n))
    (hUnsat : ¬ Satisfiable (PysatConjecture1Formula n)) :
    NorinGeodesicConjecture n := by
  apply geodesicConjecture_of_psi_unsat (n := n)
  intro hPsiSat
  exact hUnsat (hLift hPsiSat)

end NorinCNF
