import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
A tiny CNF/SAT DSL + a clean reduction from 3-coloring to CNF-SAT.

Key design goal (per your request):
* `CNF.Satisfiable φ` is *definitionally* `∃ τ, τ ⊨ φ`.
  So from “satisfiable” you immediately `rcases` an assignment `τ` and a proof it satisfies all
  clauses.
* The 3-coloring CNF is packaged as a *set of clauses* (rather than a concatenated list), so
  extracting individual constraints is easy: you just apply the satisfaction hypothesis to the
  appropriate constructor of `ClauseIn`.
* We then bundle the extracted consequences into a `Constraints` structure, so the
  SAT → 3-coloring direction becomes essentially: “get constraints → choose a color per vertex →
  prove proper by the edge-clauses”.
-/

namespace CNF

universe u

/-- Propositional literals over variables `α`. -/
inductive Lit (α : Type u) : Type u
  | pos : α → Lit α
  | neg : α → Lit α
deriving DecidableEq, Repr

/-- A clause is a finite disjunction of literals. -/
abbrev Clause (α : Type u) : Type u := List (Lit α)

/-- A CNF formula is a (possibly infinite) set of clauses (conjunction over the set). -/
abbrev Formula (α : Type u) : Type u := Set (Clause α)

/-- A truth assignment for variables `α` (Prop-valued, for easy reasoning). -/
abbrev Assignment (α : Type u) : Type u := α → Prop

/-- Satisfaction of a literal. -/
def Lit.Sat {α : Type u} (τ : Assignment α) : Lit α → Prop
  | .pos a => τ a
  | .neg a => ¬ τ a

/-- Satisfaction of a clause (some literal in it holds). -/
def Clause.Sat {α : Type u} (τ : Assignment α) (cl : Clause α) : Prop :=
  ∃ l, l ∈ cl ∧ Lit.Sat τ l

/-- Satisfaction of a CNF formula (every clause in the set is satisfied). -/
def Formula.Sat {α : Type u} (τ : Assignment α) (φ : Formula α) : Prop :=
  ∀ cl, cl ∈ φ → Clause.Sat τ cl

/-- Satisfiable iff there exists a satisfying assignment. -/
def Satisfiable {α : Type u} (φ : Formula α) : Prop :=
  ∃ τ, Formula.Sat τ φ

notation:55 τ " ⊨ₗ " l => Lit.Sat τ l
notation:55 τ " ⊨ᶜ " c => Clause.Sat τ c
notation:55 τ " ⊨ " φ => Formula.Sat τ φ

@[simp] theorem satisfiable_iff {α : Type u} {φ : Formula α} :
    Satisfiable φ ↔ ∃ τ, τ ⊨ φ := Iff.rfl

/-- If `τ` satisfies a formula, then it satisfies each clause in it. -/
theorem sat_of_mem {α : Type u} {τ : Assignment α} {φ : Formula α}
    (hφ : τ ⊨ φ) {cl : Clause α} (hcl : cl ∈ φ) : τ ⊨ᶜ cl :=
  hφ cl hcl

end CNF


namespace ThreeColorSAT

open CNF

universe u
variable {V : Type u}

/-- Three colors. -/
inductive Color : Type
  | red | green | blue
deriving DecidableEq, Repr

open Color

/-- Variables are `x_{v,c}` meaning “vertex `v` has color `c`”. -/
abbrev Var (V : Type u) : Type u := V × Color

/-- Convenience constructor for variables `x_{v,c}`. -/
def x (v : V) (c : Color) : Var V := (v, c)

/-- Positive literal `x_{v,c}`. -/
def pos (v : V) (c : Color) : CNF.Lit (Var V) := .pos (x v c)

/-- Negative literal `¬x_{v,c}`. -/
def neg (v : V) (c : Color) : CNF.Lit (Var V) := .neg (x v c)

/-- Vertex clause: at least one of the three colors holds. -/
def vertexAtLeastOne (v : V) : CNF.Clause (Var V) :=
  [pos v red, pos v green, pos v blue]

/-- Vertex clause: not both `c₁` and `c₂`. -/
def vertexAtMostOne (v : V) (c₁ c₂ : Color) : CNF.Clause (Var V) :=
  [neg v c₁, neg v c₂]

/-- Edge clause: endpoints cannot share color `c`. -/
def edgeNotSame (v w : V) (c : Color) : CNF.Clause (Var V) :=
  [neg v c, neg w c]

/-!
Instead of building a giant list and fighting `List.mem` proofs, we define “the CNF for 3-coloring”
as a set of clauses described by an inductive predicate.

This is the main “abstraction for easy proofs”.
-/
inductive ClauseIn (G : SimpleGraph V) : CNF.Clause (Var V) → Prop
  | vertexAtLeast (v : V) :
      ClauseIn G (vertexAtLeastOne (V := V) v)
  | vertexAtMost (v : V) (c₁ c₂ : Color) (h : c₁ ≠ c₂) :
      ClauseIn G (vertexAtMostOne (V := V) v c₁ c₂)
  | edge (v w : V) (hAdj : G.Adj v w) (c : Color) :
      ClauseIn G (edgeNotSame (V := V) v w c)

/-- The CNF encoding of 3-coloring for `G`. -/
def threeColorCNF (G : SimpleGraph V) : CNF.Formula (Var V) :=
  {cl | ClauseIn (V := V) G cl}

/-- Proper coloring predicate. -/
def IsProperColoring (G : SimpleGraph V) (f : V → Color) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → f v ≠ f w

/-- `G` is 3-colorable if it has a proper coloring into `Color`. -/
def ThreeColorable (G : SimpleGraph V) : Prop :=
  ∃ f : V → Color, IsProperColoring (V := V) G f


/-!
Small “SAT → constraints” lemmas for the specific clauses.
These are the little building blocks that make the main theorem clean.
-/

lemma exists_color_of_sat_vertexAtLeastOne
    {τ : CNF.Assignment (Var V)} {v : V}
    (h : τ ⊨ᶜ vertexAtLeastOne (V := V) v) :
    ∃ c : Color, τ (x (V := V) v c) := by
  rcases h with ⟨l, hlmem, hlsat⟩
  have hlmem' :
      l = pos (V := V) v red ∨ l = pos (V := V) v green ∨ l = pos (V := V) v blue := by
    simpa [vertexAtLeastOne, pos] using hlmem
  rcases hlmem' with hred | hrest
  · subst hred
    refine ⟨red, ?_⟩
    simpa [CNF.Lit.Sat, pos, x] using hlsat
  · rcases hrest with hgreen | hblue
    · subst hgreen
      refine ⟨green, ?_⟩
      simpa [CNF.Lit.Sat, pos, x] using hlsat
    · subst hblue
      refine ⟨blue, ?_⟩
      simpa [CNF.Lit.Sat, pos, x] using hlsat

lemma not_both_of_sat_vertexAtMostOne
    {τ : CNF.Assignment (Var V)} {v : V} {c₁ c₂ : Color}
    (h : τ ⊨ᶜ vertexAtMostOne (V := V) v c₁ c₂) :
    ¬ (τ (x (V := V) v c₁) ∧ τ (x (V := V) v c₂)) := by
  rcases h with ⟨l, hlmem, hlsat⟩
  have hlmem' :
      l = neg (V := V) v c₁ ∨ l = neg (V := V) v c₂ := by
    simpa [vertexAtMostOne, neg] using hlmem
  rcases hlmem' with h1 | h2
  · subst h1
    have hn : ¬ τ (x (V := V) v c₁) := by
      simpa [CNF.Lit.Sat, neg, x] using hlsat
    intro hBoth
    exact hn hBoth.1
  · subst h2
    have hn : ¬ τ (x (V := V) v c₂) := by
      simpa [CNF.Lit.Sat, neg, x] using hlsat
    intro hBoth
    exact hn hBoth.2

lemma not_both_of_sat_edgeNotSame
    {τ : CNF.Assignment (Var V)} {v w : V} {c : Color}
    (h : τ ⊨ᶜ edgeNotSame (V := V) v w c) :
    ¬ (τ (x (V := V) v c) ∧ τ (x (V := V) w c)) := by
  rcases h with ⟨l, hlmem, hlsat⟩
  have hlmem' :
      l = neg (V := V) v c ∨ l = neg (V := V) w c := by
    simpa [edgeNotSame, neg] using hlmem
  rcases hlmem' with h1 | h2
  · subst h1
    have hn : ¬ τ (x (V := V) v c) := by
      simpa [CNF.Lit.Sat, neg, x] using hlsat
    intro hBoth
    exact hn hBoth.1
  · subst h2
    have hn : ¬ τ (x (V := V) w c) := by
      simpa [CNF.Lit.Sat, neg, x] using hlsat
    intro hBoth
    exact hn hBoth.2


/--
A convenient “semantic interface” to the 3-coloring CNF:
these are exactly the consequences we want to use to build a graph coloring.
-/
structure Constraints (G : SimpleGraph V) (τ : CNF.Assignment (Var V)) : Prop where
  vertex_has :
    ∀ v : V, ∃ c : Color, τ (x (V := V) v c)
  vertex_no_two :
    ∀ v : V, ∀ {c₁ c₂ : Color}, c₁ ≠ c₂ →
      ¬ (τ (x (V := V) v c₁) ∧ τ (x (V := V) v c₂))
  edge_no_same :
    ∀ ⦃v w : V⦄, G.Adj v w → ∀ c : Color,
      ¬ (τ (x (V := V) v c) ∧ τ (x (V := V) w c))

/-- From `τ ⊨ threeColorCNF G` we can immediately extract the constraints we care about. -/
theorem constraints_of_sat
    {G : SimpleGraph V} {τ : CNF.Assignment (Var V)}
    (h : τ ⊨ threeColorCNF (V := V) G) :
    Constraints (V := V) G τ := by
  refine ⟨?vertex_has, ?vertex_no_two, ?edge_no_same⟩
  · intro v
    have hcl : τ ⊨ᶜ vertexAtLeastOne (V := V) v :=
      h _ (ClauseIn.vertexAtLeast (V := V) (G := G) v)
    exact exists_color_of_sat_vertexAtLeastOne (V := V) (τ := τ) hcl
  · intro v c₁ c₂ hne
    have hcl : τ ⊨ᶜ vertexAtMostOne (V := V) v c₁ c₂ :=
      h _ (ClauseIn.vertexAtMost (V := V) (G := G) v c₁ c₂ hne)
    exact not_both_of_sat_vertexAtMostOne (V := V) (τ := τ) (v := v) (c₁ := c₁) (c₂ := c₂) hcl
  · intro v w hvw c
    have hcl : τ ⊨ᶜ edgeNotSame (V := V) v w c :=
      h _ (ClauseIn.edge (V := V) (G := G) v w hvw c)
    exact not_both_of_sat_edgeNotSame (V := V) (τ := τ) (v := v) (w := w) (c := c) hcl


/-- Given constraints, choose *some* color for each vertex (noncomputably). -/
noncomputable def coloringOf
    {G : SimpleGraph V} {τ : CNF.Assignment (Var V)}
    (h : Constraints (V := V) G τ) : V → Color :=
  fun v => Classical.choose (h.vertex_has v)

lemma coloringOf_spec
    {G : SimpleGraph V} {τ : CNF.Assignment (Var V)}
    (h : Constraints (V := V) G τ) (v : V) :
    τ (x (V := V) v (coloringOf (V := V) (G := G) (τ := τ) h v)) :=
  Classical.choose_spec (h.vertex_has v)

/-- The chosen coloring is proper thanks to the edge-clauses. -/
theorem coloringOf_proper
    {G : SimpleGraph V} {τ : CNF.Assignment (Var V)}
    (h : Constraints (V := V) G τ) :
    IsProperColoring (V := V) G (coloringOf (V := V) (G := G) (τ := τ) h) := by
  intro v w hvw hEq
  have hv : τ (x (V := V) v (coloringOf (V := V) (G := G) (τ := τ) h v)) :=
    coloringOf_spec (V := V) (G := G) (τ := τ) h v
  have hw : τ (x (V := V) w (coloringOf (V := V) (G := G) (τ := τ) h w)) :=
    coloringOf_spec (V := V) (G := G) (τ := τ) h w
  have hw' : τ (x (V := V) w (coloringOf (V := V) (G := G) (τ := τ) h v)) := by
    simpa [hEq] using hw
  exact (h.edge_no_same (v := v) (w := w) hvw (coloringOf (V := V) (G := G) (τ := τ) h v)) ⟨hv, hw'⟩


/-!
Main equivalence: the CNF is satisfiable iff the graph is 3-colorable.
-/

theorem threeColorCNF_satisfiable_iff
    (G : SimpleGraph V) :
    CNF.Satisfiable (threeColorCNF (V := V) G) ↔ ThreeColorable (V := V) G := by
  constructor
  · intro hSat
    rcases hSat with ⟨τ, hτ⟩
    let hC : Constraints (V := V) G τ := constraints_of_sat (V := V) (G := G) (τ := τ) hτ
    refine ⟨coloringOf (V := V) (G := G) (τ := τ) hC, ?_⟩
    exact coloringOf_proper (V := V) (G := G) (τ := τ) hC
  · rintro ⟨f, hf⟩
    classical
    -- assignment induced by a coloring: τ(v,c) := (f v = c)
    let τ : CNF.Assignment (Var V) := fun vc => f vc.1 = vc.2
    refine ⟨τ, ?_⟩
    intro cl hcl
    cases hcl with
    | vertexAtLeast v =>
        -- Pick the literal corresponding to `f v`.
        cases hfv : f v with
        | red =>
            refine ⟨pos (V := V) v red, ?_, ?_⟩
            · simp [vertexAtLeastOne, pos]
            · -- τ(x v red) holds because f v = red
              simp [CNF.Lit.Sat, τ, pos, x, hfv]
        | green =>
            refine ⟨pos (V := V) v green, ?_, ?_⟩
            · simp [vertexAtLeastOne, pos]
            · simp [CNF.Lit.Sat, τ, pos, x, hfv]
        | blue =>
            refine ⟨pos (V := V) v blue, ?_, ?_⟩
            · simp [vertexAtLeastOne, pos]
            · simp [CNF.Lit.Sat, τ, pos, x, hfv]
    | vertexAtMost v c₁ c₂ hne =>
        -- Either `f v = c₁` (then `f v ≠ c₂`) or not (then `f v ≠ c₁`).
        by_cases h1 : f v = c₁
        · refine ⟨neg (V := V) v c₂, ?_, ?_⟩
          · simp [vertexAtMostOne, neg]
          · have : f v ≠ c₂ := by
              intro h2
              exact hne (by simpa [h1] using h2)
            -- literal is `¬τ(x v c₂)` i.e. `¬(f v = c₂)`
            simpa [CNF.Lit.Sat, τ, neg, x] using this
        · refine ⟨neg (V := V) v c₁, ?_, ?_⟩
          · simp [vertexAtMostOne, neg]
          · -- literal is `¬τ(x v c₁)` i.e. `¬(f v = c₁)`
            simpa [CNF.Lit.Sat, τ, neg, x] using h1
    | edge v w hvw c =>
        -- Either `f v = c` (then `f w ≠ c` by properness) or not (then `f v ≠ c`).
        by_cases hvc : f v = c
        · refine ⟨neg (V := V) w c, ?_, ?_⟩
          · simp [edgeNotSame, neg]
          · have : f w ≠ c := by
              intro hwc
              -- would imply f v = f w, contradict properness
              exact (hf (v := v) (w := w) hvw) (by simp [hvc, hwc])
            simpa [CNF.Lit.Sat, τ, neg, x] using this
        · refine ⟨neg (V := V) v c, ?_, ?_⟩
          · simp [edgeNotSame, neg]
          · simpa [CNF.Lit.Sat, τ, neg, x] using hvc

/-! ## Hypercube graph `Q_n` -/
namespace Hypercube

open Finset

/-- Hamming distance between two bitstrings `Fin n → Bool`. -/
def hamming {n : Nat} (v w : Fin n → Bool) : Nat :=
  (Finset.univ.filter (fun i : Fin n => v i ≠ w i)).card

/-- The n-dimensional hypercube graph `Q_n`.

Vertices are bitstrings `Fin n → Bool`. Two vertices are adjacent iff they differ
in exactly one coordinate (Hamming distance 1).
-/
def Q (n : Nat) : SimpleGraph (Fin n → Bool) :=
{ Adj := fun v w => hamming v w = 1
  symm := by
    intro v w h
    -- `hamming v w = hamming w v` since `≠` is symmetric.
    have hEq :
        (Finset.univ.filter (fun i : Fin n => v i ≠ w i)) =
          (Finset.univ.filter (fun i : Fin n => w i ≠ v i)) := by
      ext i
      simp [ne_comm]
    simpa [hamming, hEq] using h
  loopless := by
    intro v
    -- no loops: hamming(v,v) = 0
    simp [hamming] }

abbrev Q5 : SimpleGraph (Fin 5 → Bool) := Q 5

/-- `Q_n` has decidable adjacency (needed for enumerating edges to print DIMACS). -/
instance (n : Nat) : DecidableRel (Q n).Adj := by
  intro v w
  -- adjacency is an equality of naturals, hence decidable
  dsimp [Q, hamming]
  infer_instance

end Hypercube


/-! ## DIMACS printing for the generated CNF -/
namespace Dimacs

open CNF
open Hypercube

/-- Fixed list of colors for iteration. -/
def colors : List Color :=
  [Color.red, Color.green, Color.blue]

/-- All ordered pairs of distinct colors (6 pairs). -/
def orderedUnequalColorPairs : List (Color × Color) :=
  [ (Color.red,   Color.green),
    (Color.red,   Color.blue),
    (Color.green, Color.red),
    (Color.green, Color.blue),
    (Color.blue,  Color.red),
    (Color.blue,  Color.green) ]

/-- `Color` → `0,1,2` for DIMACS numbering. -/
def colorToNat : Color → Nat
  | .red   => 0
  | .green => 1
  | .blue  => 2

/-- Decode an integer `m` into an `n`-bit vertex (little-endian). -/
def natToVertex (n m : Nat) : Fin n → Bool :=
  fun i => Nat.testBit m i.1

/-- All vertices of `Q_n`, encoded as bit-vectors of length `n`. -/
def allVertices (n : Nat) : List (Fin n → Bool) :=
  (List.range (2 ^ n)).map (natToVertex n)

/-- Interpret a vertex `Fin n → Bool` as a Nat in `[0, 2^n)` (little-endian bits). -/
def vertexToNat {n : Nat} (v : Fin n → Bool) : Nat :=
  (List.finRange n).foldl
    (fun acc i => acc + (if v i then 1 else 0) * (2 ^ (i : Nat)))
    0

/-- DIMACS variable id for `x_{v,c}` (1-based). -/
def varId {n : Nat} : Var (Fin n → Bool) → Nat
  | (v, c) => vertexToNat v * 3 + colorToNat c + 1

/-- Convert a literal to a signed DIMACS `Int`. -/
def litToInt {n : Nat} : Lit (Var (Fin n → Bool)) → Int
  | .pos a => Int.ofNat (varId (n := n) a)
  | .neg a => -Int.ofNat (varId (n := n) a)

/-- Render a clause as one DIMACS line (ending with `0`). -/
def clauseLine {n : Nat} (cl : Clause (Var (Fin n → Bool))) : String :=
  let xs : List String := cl.map (fun l => toString (litToInt (n := n) l))
  String.intercalate " " xs ++ " 0"

/--
Enumerate the clauses of the 3-coloring CNF for a finite graph `G`
(“finite” here is because we can list all vertices and ordered adjacent pairs).

This matches the *same logical constraints* used by `threeColorCNF`:
* for each vertex `v`: `x(v,red) ∨ x(v,green) ∨ x(v,blue)`
* for each vertex `v` and each ordered `c₁ ≠ c₂`: `¬x(v,c₁) ∨ ¬x(v,c₂)`
* for each ordered edge `(v,w)` and each color `c`: `¬x(v,c) ∨ ¬x(w,c)`

(There may be duplicates from ordered pairs; DIMACS solvers typically allow that,
and it doesn’t change satisfiability.)
-/
def threeColorCNFClauses {n : Nat} (G : SimpleGraph (Fin n → Bool))
    [DecidableRel G.Adj] : List (Clause (Var (Fin n → Bool))) :=
  let vs : List (Fin n → Bool) := allVertices n
  let es : List ((Fin n → Bool) × (Fin n → Bool)) :=
    List.flatMap
      (fun v =>
        (List.filter (fun w => decide (G.Adj v w)) vs).map (fun w => (v, w)))
      vs
  let vertexClauses : List (Clause (Var (Fin n → Bool))) :=
    List.flatMap (fun v =>
      -- at least one color:
      vertexAtLeastOne (V := Fin n → Bool) v
        -- at most one color (all ordered unequal pairs):
        :: (orderedUnequalColorPairs.map (fun p =>
              vertexAtMostOne (V := Fin n → Bool) v p.1 p.2))) vs
  let edgeClauses : List (Clause (Var (Fin n → Bool))) :=
    List.flatMap (fun vw =>
      colors.map (fun c => edgeNotSame (V := Fin n → Bool) vw.1 vw.2 c)) es
  vertexClauses ++ edgeClauses

/-- Render a list-of-clauses CNF to a DIMACS string. -/
def toDimacs {n : Nat} (clauses : List (Clause (Var (Fin n → Bool)))) : String :=
  let numVerts : Nat := 2 ^ n
  let numVars  : Nat := 3 * numVerts
  let numClauses : Nat := clauses.length
  let header := s!"c 3-coloring CNF for Q_{n}\n" ++
                s!"c varId(v,c) = 3*vertexToNat(v) + colorToNat(c) + 1\n" ++
                s!"p cnf {numVars} {numClauses}\n"
  header ++ String.intercalate "\n" (clauses.map (clauseLine (n := n))) ++ "\n"

/-- Print the DIMACS encoding of the 3-coloring CNF for the hypercube `Q_n`. -/
def printQn (n : Nat) : IO Unit := do
  let G := Hypercube.Q n
  let cls := threeColorCNFClauses (n := n) G
  IO.println (toDimacs (n := n) cls)

/-- Example: print the DIMACS for `Q_5`. -/
def main : IO Unit := printQn 5

end Dimacs


/-! ## Demo: assume SAT(F) ⇒ derive 3-colorability of Q₅ -/
namespace DemoQ5

open CNF
open Hypercube

/-- The 5D hypercube graph. -/
def Q5 : SimpleGraph (Fin 5 → Bool) := Hypercube.Q5

/-- The abstract CNF formula (as a set of clauses) encoding “Q5 is 3-colorable”. -/
abbrev F : CNF.Formula (Var (Fin 5 → Bool)) :=
  threeColorCNF (V := Fin 5 → Bool) Q5

/--
Axiom: the CNF is satisfiable (imagine: an external SAT solver returned SAT).
-/
axiom F_sat : CNF.Satisfiable F

/--
Then `Q_5` is 3-colorable (immediate from the correctness theorem).
-/
theorem Q5_threeColorable : ThreeColorable (V := Fin 5 → Bool) Q5 :=
  (threeColorCNF_satisfiable_iff (V := Fin 5 → Bool) Q5).1 F_sat

end DemoQ5

end ThreeColorSAT
