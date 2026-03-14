import Mathlib


set_option linter.style.longLine false
set_option linter.unusedDecidableInType false



open scoped BigOperators

open Finset

namespace NorinLemma8

/-! ## 0. Vertices, antipode, hamming -/

abbrev Vertex (n : ℕ) := Fin n → Bool

def antipode {n : ℕ} (v : Vertex n) : Vertex n := fun i => ! v i

lemma antipode_involutive {n : ℕ} : Function.Involutive (@antipode n) := by
  intro v; funext i; simp [antipode]

def diffCoords {n : ℕ} (u v : Vertex n) : Finset (Fin n) :=
  univ.filter (fun i => u i ≠ v i)

def hamming {n : ℕ} (u v : Vertex n) : ℕ :=
  (diffCoords u v).card

lemma hamming_antipode {n : ℕ} (v : Vertex n) :
    hamming v (antipode v) = n := by
  -- each coordinate differs
  simp [hamming, diffCoords, antipode]

lemma hamming_symmetric {n : ℕ} (u v : Vertex n) :
    hamming u v = hamming v u := by
  simp [hamming, diffCoords, ne_comm]

/-! ## 1. Hypercube graph as SimpleGraph -/

def cube (n : ℕ) : SimpleGraph (Vertex n) :=
{ Adj := fun u v => hamming u v = 1
  symm := by
    intro u v h
    rw [hamming_symmetric]
    exact h
  loopless := by
    intro v; -- hamming v v = 0
    simp [hamming, diffCoords]
}

lemma cube_adj_iff {n : ℕ} {u v : Vertex n} :
    (cube n).Adj u v ↔ hamming u v = 1 := Iff.rfl

/-! ## 2. k-subcubes encoded as support + base -/

structure Subcube (n k : ℕ) where
  support : Finset (Fin n)
  support_card : support.card = k
  base : Vertex n

def Subcube.mem {n k : ℕ} (q : Subcube n k) (v : Vertex n) : Prop :=
  ∀ i, i ∉ q.support → v i = q.base i

/-- The set of vertices belonging to the subcube `q`. -/
noncomputable def Subcube.verts {n k : ℕ} (q : Subcube n k) : Finset (Vertex n) :=
  letI := Classical.decPred q.mem
  univ.filter q.mem

lemma Subcube.card_verts {n k : ℕ} (q : Subcube n k) :
    q.verts.card = 2^k := by
  letI := Classical.decPred q.mem
  have h_verts : q.verts.card = (univ.filter q.mem).card := by
    unfold Subcube.verts; rfl
  rw [h_verts, ← Fintype.card_subtype q.mem]
  let e : {v // q.mem v} ≃ (q.support → Bool) := {
    toFun := fun v i => v.val i
    invFun := fun f => ⟨fun i => if h : i ∈ q.support then f ⟨i, h⟩ else q.base i, by
      intro i hi
      simp [hi] ⟩
    left_inv := fun v => by
      ext i
      by_cases hi : i ∈ q.support
      · simp [hi]
      · simp [hi, v.property i hi]
    right_inv := fun f => by
      ext ⟨i, hi⟩
      simp [hi]
  }
  rw [Fintype.card_congr e]
  simp [Fintype.card_bool, q.support_card]

def spanSubcube {n k : ℕ} (u v : Vertex n) (hk : hamming u v = k) : Subcube n k :=
{ support := diffCoords u v
  support_card := by simpa [hamming] using hk
  base := u }

lemma unique_subcube_of_dist
  {n k : ℕ} {u v : Vertex n} (hk : hamming u v = k) :
  ∀ q : Subcube n k, q.mem u → q.mem v → q.verts = (spanSubcube (n:=n) (k:=k) u v hk).verts := by
  intro q hu hv
  -- First, show q.support covers the differences
  have h_supp : diffCoords u v ⊆ q.support := by
    intro i hi
    -- i ∈ diffCoords u v => u i ≠ v i
    simp only [diffCoords, mem_filter, mem_univ, true_and] at hi
    by_contra h_not
    -- i ∉ q.support => u i = q.base i  and  v i = q.base i
    have h1 := hu i h_not
    have h2 := hv i h_not
    rw [h1, h2] at hi
    contradiction
  -- Since sizes match (k), the subset is an equality
  have h_eq_supp : q.support = diffCoords u v := by
    apply (Finset.eq_of_subset_of_card_le h_supp _).symm
    rw [q.support_card]
    exact hk.symm.le
  -- Now show the sets of vertices are the same
  letI := Classical.decPred q.mem
  letI := Classical.decPred (spanSubcube (n:=n) (k:=k) u v hk).mem
  ext x
  rw [Subcube.verts, Subcube.verts, mem_filter, mem_filter]
  apply and_congr_right
  intro _
  -- x is in q.verts iff x matches q.base outside q.support
  -- x is in span...verts iff x matches u (span's base) outside diffCoords...
  rw [Subcube.mem, Subcube.mem]
  constructor
  · intro h i hi_diff
    -- i ∉ (span ...).support
    rw [spanSubcube] at hi_diff
    -- simp at hi_diff
    simp_rw [← h_eq_supp] at hi_diff
    rw [h i hi_diff]
    -- q.base i matches u i because q.mem u
    exact (hu i hi_diff).symm
  · intro h i hi_sup
    -- need to show x i = (span ...).base i
    -- (span ...).base = u
    rw [h_eq_supp] at hi_sup
    rw [h i hi_sup]
    rw [spanSubcube];
    -- x i = q.base i.
    -- we need q.base i = u i
    convert hu i _
    rwa [h_eq_supp]

/-! ## 3. Colorings and color changes -/

abbrev Edge (n : ℕ) := Sym2 (Vertex n)

abbrev Coloring (n : ℕ) := Edge n → Bool

-- Bool = {red, blue}

def edgeOf {n : ℕ} (u v : Vertex n) : Edge n := Sym2.mk (u, v)

def changesOnColors : List Bool → Nat
| []        => 0
| [_]       => 0
| b₀::b₁::t => (if b₀ = b₁ then 0 else 1) + changesOnColors (b₁::t)

lemma changesOnColors_add1 (b : Bool) (l : List Bool) :
    changesOnColors (b::l) ≤ changesOnColors l + 1 := by
  cases l with
  | nil => simp [changesOnColors]
  | cons h t =>
    simp [changesOnColors]
    split_ifs
    · omega
    · omega

-- split_ifs

lemma changesOnColors_append (l1 l2 : List Bool) :
    changesOnColors (l1 ++ l2) ≤ changesOnColors l1 + changesOnColors l2 + 1 := by
  induction l1 with
  | nil =>
      simp only [List.nil_append, changesOnColors, zero_add, le_add_iff_nonneg_right]
      apply Nat.zero_le
  | cons h t ih =>
      cases t with
      | nil =>
          simp only [List.cons_append, List.nil_append, changesOnColors, zero_add]
          apply changesOnColors_add1
      | cons h' t' =>
          simp only [List.cons_append, changesOnColors]
          simp only [List.cons_append] at ih
          split_ifs
          · simp only [zero_add]
            exact ih
          · simp only [add_assoc]
            omega


lemma changesOnColors_le_length (l : List Bool) :
    changesOnColors l ≤ l.length := by
  induction l with
  | nil => rfl
  | cons h t ih =>
      have h_le := changesOnColors_add1 h t
      have h_ind : changesOnColors t +1 ≤ t.length + 1 := by omega
      exact le_trans h_le h_ind

/- A geodesic/path representation that is convenient for chunk indexing. -/
structure GeoPath (n ℓ : ℕ) where
  verts : Fin (ℓ+1) → Vertex n
  adj : ∀ i : Fin ℓ, (cube n).Adj (verts i.castSucc) (verts i.succ)

def GeoPath.edgeColors {n ℓ : ℕ} (c : Coloring n) (p : GeoPath n ℓ) : List Bool :=
  List.ofFn (fun i : Fin ℓ => c (edgeOf (p.verts i.castSucc) (p.verts i.succ)))

def GeoPath.colorChanges {n ℓ : ℕ} (c : Coloring n) (p : GeoPath n ℓ) : Nat :=
  changesOnColors (p.edgeColors c)

lemma GeoPath.colorChanges_le_length {n ℓ : ℕ} (c : Coloring n) (p : GeoPath n ℓ) :
    p.colorChanges c ≤ ℓ := by
  have heq : (p.edgeColors c).length = ℓ := by simp [GeoPath.edgeColors]
  rw [GeoPath.colorChanges]
  generalize hl : p.edgeColors c = l
  rw [← heq, hl]
  clear heq hl p c n
  induction l with
  | nil => simp [changesOnColors]
  | cons h t ih =>
    cases t with
    | nil => simp [changesOnColors]
    | cons h' t' =>
      simp only [changesOnColors, List.length_cons, ge_iff_le]
      split_ifs with heq
      · simpa [changesOnColors, heq] using Nat.le_trans ih (Nat.le_succ _)
      · rw [add_comm]
        have : 1 + changesOnColors (h'::t') ≤ 1 + (h'::t').length := by
          -- ih: changesOnColors (h' :: t') ≤ (h' :: t').length
          omega
        aesop

/-- Flip a single coordinate. -/
def flipCoord {n : ℕ} (i : Fin n) (v : Vertex n) : Vertex n :=
  fun j => if j = i then ! v j else v j

lemma hamming_flipCoord {n : ℕ} (v : Vertex n) (i : Fin n) :
    hamming v (flipCoord i v) = 1 := by
  unfold hamming diffCoords flipCoord
  have hset :
      (Finset.univ.filter (fun j : Fin n => v j ≠ (if j = i then !v j else v j)))
        = ({i} : Finset (Fin n)) := by
    ext j
    by_cases hji : j = i
    · subst hji
      aesop
    · simp [hji]
  simp_all only [ne_eq, right_eq_ite_iff, Bool.eq_not_self, imp_false, Decidable.not_not, card_singleton]

lemma cube_adj_flipCoord {n : ℕ} (v : Vertex n) (i : Fin n) :
    (cube n).Adj v (flipCoord i v) := by
  simp [cube, hamming_flipCoord]

/-- The vertex at step `t` when starting at `start` and flipping coords according to `coord`. -/
def vertsNat {n : ℕ} (start : Vertex n) (coord : Fin n → Fin n) : ℕ → Vertex n
  | 0 => start
  | t + 1 => if h : t < n then flipCoord (coord ⟨t, h⟩) (vertsNat start coord t) else vertsNat start coord t

noncomputable def GeoPath.ofCoordFn {n : ℕ} (start : Vertex n) (coord : Fin n → Fin n) :
    GeoPath n n := by
  classical
  refine
    { verts := fun t : Fin (n+1) => vertsNat start coord t.1
      adj := ?_ }
  intro i
  have hstep : vertsNat start coord (i.1 + 1) = flipCoord (coord i) (vertsNat start coord i.1) := by
    simp [vertsNat, i.2]
  -- goal: Adj (vertsNat i) (vertsNat (i+1))
  simpa [hstep] using (cube_adj_flipCoord (n:=n) (v := vertsNat start coord i.1) (i := coord i))

/-! ## 4. Random antipodal geodesic as (start, perm) -/

structure AntiGeoData (n : ℕ) where
  start : Vertex n
  perm  : Equiv.Perm (Fin n)
deriving Fintype

def flipSet {n : ℕ} (S : Finset (Fin n)) (v : Vertex n) : Vertex n :=
  fun i => if i ∈ S then ! v i else v i

lemma vertsNat_congr_at_x {n : ℕ} (s1 s2 : Vertex n) (coord : Fin n → Fin n) (t : ℕ) (x : Fin n) (h : s1 x = s2 x) :
  vertsNat s1 coord t x = vertsNat s2 coord t x := by
  induction t with
  | zero => exact h
  | succ t ih =>
      simp only [vertsNat]
      by_cases ht : t < n
      · simp [ht, flipCoord, ih]
      · simp [ht, ih]

lemma vertsNat_not_flipped {n : ℕ} (start : Vertex n) (coord : Fin n → Fin n) (t : ℕ) (x : Fin n)
    (hx : ∀ j : ℕ, (hj : j < t) → (hjn : j < n) → coord ⟨j, hjn⟩ ≠ x) :
    vertsNat start coord t x = start x := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [vertsNat]
      by_cases ht : t < n
      · simp only [ht, ↓reduceDIte, flipCoord]
        split_ifs with h_coord
        · exact False.elim (hx t (Nat.le_refl _) ht h_coord.symm)
        · apply ih
          intro j hj hjn
          apply hx j (Nat.le_succ_of_le hj) hjn
      · simp only [ht, ↓reduceDIte]
        apply ih
        intro j hj hjn
        apply hx j (Nat.le_succ_of_le hj) hjn

/--
Constructs a geodesic path in the hypercube graph from `g.start` to its antipode.
-/
noncomputable def AntiGeoData.toGeoPath {n : ℕ} (g : AntiGeoData n) : GeoPath n n :=
  GeoPath.ofCoordFn (n:=n) g.start g.perm

/-- The vertex list visited when starting at `start` and flipping the coordinates in `coords` in order. -/
def vertsFromOrder {n : ℕ} (start : Vertex n) (coords : List (Fin n)) : List (Vertex n) :=
  coords.scanl (fun v i => flipCoord i v) start

/-- The vertex at step `t` for a coordinate function of length `ℓ`. -/
def vertsNatLen {n ℓ : ℕ} (start : Vertex n) (coord : Fin ℓ → Fin n) : ℕ → Vertex n
  | 0 => start
  | t + 1 => if h : t < ℓ then flipCoord (coord ⟨t, h⟩) (vertsNatLen start coord t) else vertsNatLen start coord t

private lemma vertsNatLen_congr
    {n ℓ : ℕ} (start : Vertex n) {coord1 coord2 : Fin ℓ → Fin n}
    (hcoord : ∀ i : Fin ℓ, coord1 i = coord2 i) :
    ∀ t : ℕ, vertsNatLen start coord1 t = vertsNatLen start coord2 t
  | 0 => rfl
  | t + 1 => by
      by_cases ht : t < ℓ
      · simp [vertsNatLen, ht, hcoord ⟨t, ht⟩, vertsNatLen_congr start hcoord t]
      · simp [vertsNatLen, ht, vertsNatLen_congr start hcoord t]

/-- Build a length-`ℓ` path by flipping coordinates given by `coord : Fin ℓ → Fin n`. -/
noncomputable def GeoPath.ofCoordFnLen {n ℓ : ℕ} (start : Vertex n) (coord : Fin ℓ → Fin n) :
    GeoPath n ℓ := by
  classical
  refine
    { verts := fun t : Fin (ℓ + 1) => vertsNatLen start coord t.1
      adj := ?_ }
  intro i
  have hstep : vertsNatLen start coord (i.1 + 1) = flipCoord (coord i) (vertsNatLen start coord i.1) := by
    simp [vertsNatLen, i.2]
  simpa [hstep] using (cube_adj_flipCoord (n := n) (v := vertsNatLen start coord i.1) (i := coord i))

/-- The edge-color list along that walk (length = `coords.length`). -/
noncomputable def edgeColorsFromOrder {n : ℕ} (c : Coloring n) (start : Vertex n)
    (coords : List (Fin n)) : List Bool :=
  (GeoPath.ofCoordFnLen (n := n) (ℓ := coords.length) start (fun i : Fin coords.length => coords[i])).edgeColors c

-- NOTE: helper lemmas for rewriting `edgeColorsFromOrder` on `List.ofFn` are added as needed.

noncomputable def changesFromOrder {n : ℕ} (c : Coloring n) (start : Vertex n) (coords : List (Fin n)) : Nat :=
  changesOnColors (edgeColorsFromOrder (n:=n) c start coords)

noncomputable def firstColorFromOrder? {n : ℕ} (c : Coloring n) (start : Vertex n) (coords : List (Fin n)) : Option Bool :=
  (edgeColorsFromOrder (n:=n) c start coords).head?

noncomputable def lastColorFromOrder? {n : ℕ} (c : Coloring n) (start : Vertex n) (coords : List (Fin n)) : Option Bool :=
  (edgeColorsFromOrder (n:=n) c start coords).reverse.head?

/--
Given a chunk coordinate “segment” `seg` (intended: length `k`), interpret it as an enumeration
`Fin k → Fin n` via `getD`, then search over all `Equiv.Perm (Fin k)` to minimize internal
color changes. If `prev` is `some b`, we tie-break by preferring minimizers whose *first*
edge color is `b` (if any).

Returns: chosen order (a list of length `k`) and the *last* edge color of that chunk (as `Option Bool`).
-/
noncomputable def bestChunkOrder
  {n k : ℕ} (c : Coloring n)
  (u : Vertex n) (seg : List (Fin n)) (prev : Option Bool) (defaultCoord : Fin n) :
  List (Fin n) × Option Bool := by
  classical
  let enum : Fin k → Fin n := fun j => seg.getD j.1 defaultCoord
  let order : Equiv.Perm (Fin k) → List (Fin n) :=
    fun σ => List.ofFn (fun t : Fin k => enum (σ t))
  let cost : Equiv.Perm (Fin k) → Nat :=
    fun σ => changesFromOrder (n:=n) c u (order σ)
  let perms : Finset (Equiv.Perm (Fin k)) := Finset.univ
  let costSet : Finset Nat := perms.image cost
  have hcostSet : costSet.Nonempty := by
    simp_all only [List.getD_eq_getElem?_getD, image_nonempty, univ_nonempty, costSet, cost, order, enum, perms]
  let minC : Nat := costSet.min' hcostSet
  let opt : Finset (Equiv.Perm (Fin k)) := perms.filter (fun σ => cost σ = minC)
  have hopt : opt.Nonempty := by
    have hmem : minC ∈ costSet := Finset.min'_mem costSet hcostSet
    -- extract a witness σ with cost σ = minC
    rcases (Finset.mem_image.mp hmem) with ⟨σ, hσuniv, hσcost⟩
    refine ⟨σ, ?_⟩
    -- membership in filter = membership in univ ∧ predicate
    simp [opt, perms, hσuniv, hσcost]
  let σbase : Equiv.Perm (Fin k) := Classical.choose hopt
  have hσbase : σbase ∈ opt := Classical.choose_spec hopt
  -- tie-break on first edge color, if requested
  let σchosen : Equiv.Perm (Fin k) :=
    match prev with
    | none => σbase
    | some b =>
        let good : Finset (Equiv.Perm (Fin k)) :=
          opt.filter (fun σ => firstColorFromOrder? (n:=n) c u (order σ) = some b)
        if hgood : good.Nonempty then Classical.choose hgood else σbase
  let chosenOrder : List (Fin n) := order σchosen
  let lastC : Option Bool := lastColorFromOrder? (n:=n) c u chosenOrder
  exact (chosenOrder, lastC)

def GeoPath.edgeColorAt {n ℓ : ℕ} (c : Coloring n) (p : GeoPath n ℓ) (i : Fin ℓ) : Bool :=
  c (edgeOf (p.verts i.castSucc) (p.verts i.succ))

noncomputable def Subcube.supportEquiv {n k : ℕ} (q : Subcube n k) : q.support ≃ Fin k := by
  classical
  -- Fintype.card q.support = q.support.card
  have hc : Fintype.card (q.support) = k := by
    -- q.support as a type is the coercion of Finset to Sort
    simpa using q.support_card
  exact Fintype.equivFinOfCardEq hc

noncomputable def Subcube.decode {n k : ℕ} (q : Subcube n k) (v : Vertex n) : Vertex k :=
  fun j => v ((q.supportEquiv (k:=k)).symm j).1

noncomputable def Subcube.encode {n k : ℕ} (q : Subcube n k) (x : Vertex k) : Vertex n :=
  fun i =>
    if hi : i ∈ q.support then
      x ((q.supportEquiv (k:=k)) ⟨i, hi⟩)
    else
      q.base i

noncomputable def Subcube.inducedColoring {n k : ℕ} (q : Subcube n k) (c : Coloring n) : Coloring k :=
  fun e => c (Sym2.map (q.encode (k:=k)) e)

namespace Algo1

variable {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)

def numChunks (n k : ℕ) : ℕ := n / k

def remSteps (n k : ℕ) : ℕ := n % k

abbrev m : ℕ := numChunks n k

abbrev r : ℕ := remSteps n k

variable [DecidableEq (Fin n)]

-- index arithmetic: you’ll need helper lemmas “k*i + j < n” etc.
-- In practice, `omega` is your friend if you imported it.

noncomputable def chunkSupport (g : AntiGeoData n) (i : Fin (m (n := n) (k := k))) : Finset (Fin n) := by
  classical
  -- image of the k indices in this block under g.perm
  refine (Finset.univ : Finset (Fin k)).image (fun j : Fin k =>
    g.perm ⟨k * i.1 + j.1, by
      have hjk : j.1 < k := j.2
      unfold m at i
      unfold numChunks at i
      have him : i.1 < n/k := i.2
      have hi : i.1 ≤ n/k - 1 := by
        omega
      have nke : ((n / k) - 1)*k ≤ n-k := by
        rw [Nat.mul_sub_right_distrib]
        simp_all only [Fin.is_lt, one_mul, tsub_le_iff_right, Nat.sub_add_cancel]
        exact Nat.div_mul_le_self n k
      have hki : k * i.1 ≤ n - k := by
        rw [mul_comm] at nke
        have hki' : k * i.1 ≤ k * (n/k - 1) := by
          apply Nat.mul_le_mul_left
          exact hi
        exact Nat.le_trans hki' nke
      omega
    ⟩)

lemma chunkSupport_card (g : AntiGeoData n) (i : Fin (m (n := n) (k := k))) :  (chunkSupport (n:=n) (k:=k) hkn g i).card = k := by
  unfold chunkSupport
  rw [Finset.card_image_of_injective]
  · simp
  · intro j1 j2 h
    simp only [EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff, Nat.add_left_cancel_iff] at h
    exact Fin.ext h

noncomputable def chunkStartVertex (g : AntiGeoData n) (i : Fin (m (n := n) (k := k))) : Vertex n := by
  classical
  -- v_{k*i}
  exact g.toGeoPath.verts ⟨k * i.1, by
    -- k*i < n+1
    unfold m at i
    unfold numChunks at i
    have him : i.1 < n/k := i.2
    have hi : i.1 ≤ n/k - 1 := by
      omega
    have nke : ((n / k) - 1)*k ≤ n-k := by
      rw [Nat.mul_sub_right_distrib]
      simp_all only [Fin.is_lt, one_mul, tsub_le_iff_right, Nat.sub_add_cancel]
      exact Nat.div_mul_le_self n k
    have hki : k * i.1 ≤ n - k := by
      rw [mul_comm] at nke
      have hki' : k * i.1 ≤ k * (n/k - 1) := by
        apply Nat.mul_le_mul_left
        exact hi
      exact Nat.le_trans hki' nke
    omega
  ⟩

noncomputable def chunkSubcube (g : AntiGeoData n) (i : Fin (m (n := n) (k := k))) : Subcube n k := by
  classical
  refine
  { support := chunkSupport (n:=n) (k:=k) hkn g i
    support_card := by
      have hcard' : (chunkSupport (n:=n) (k:=k) hkn g i).card = k := by
        unfold chunkSupport
        -- simp [Finset.card_univ]
        let f := fun j : Fin k => g.perm ⟨k * i.1 + j.1, by
          have hjk : j.1 < k := j.2
          unfold m at i
          unfold numChunks at i
          have him : i.1 < n/k := i.2
          have hi : i.1 ≤ n/k - 1 := by
            omega
          have nke : ((n / k) - 1)*k ≤ n-k := by
            rw [Nat.mul_sub_right_distrib]
            simp_all only [Fin.is_lt, one_mul, tsub_le_iff_right, Nat.sub_add_cancel]
            exact Nat.div_mul_le_self n k
          have hki : k * i.1 ≤ n - k := by
            rw [mul_comm] at nke
            have hki' : k * i.1 ≤ k * (n/k - 1) := by
              apply Nat.mul_le_mul_left
              exact hi
            exact Nat.le_trans hki' nke
          omega
        ⟩
        have inj : Function.Injective f := by
          intro j1 j2 hj1j2
          aesop
        have c := Finset.card_image_of_injective (Finset.univ : Finset (Fin k)) inj
        rw [c]
        simp
      exact hcard'
    base := fun t =>
      if ht : t ∈ chunkSupport (n:=n) (k:=k) hkn g i then
        false
      else
        (chunkStartVertex (n:=n) (k:=k) hk hkn g i) t
  }

noncomputable def chunkColoring (c : Coloring n) (g : AntiGeoData n) (i : Fin (m (n := n) (k := k))) : Coloring k :=
  (chunkSubcube (n := n) (k := k) hk hkn g i).inducedColoring (k := k) c

noncomputable def chunkStartSmall (g : AntiGeoData n) (i : Fin (m (n := n) (k := k))) : Vertex k :=
  (chunkSubcube (n := n) (k := k) hk hkn g i).decode (k := k) (chunkStartVertex (n := n) (k := k) hk hkn g i)

noncomputable def localPath (u : Vertex k) (σ : Equiv.Perm (Fin k)) : GeoPath k k :=
  (AntiGeoData.mk u σ).toGeoPath

noncomputable def localCost (c' : Coloring k) (u : Vertex k) (σ : Equiv.Perm (Fin k)) : Nat :=
  (localPath u σ).colorChanges c'

noncomputable def minChangesInCube (k : ℕ) (c : Coloring k) (u : Vertex k) : Nat :=
  let perms := (Finset.univ : Finset (Equiv.Perm (Fin k)))
  let costs := perms.image (localCost c u)
  costs.min' (Finset.univ_nonempty.image _)

lemma exists_perm_minimizing_colorChanges (c' : Coloring k) (u : Vertex k) :
  ∃ σ : Equiv.Perm (Fin k), localCost c' u σ = minChangesInCube k c' u := by
  let perms := (Finset.univ : Finset (Equiv.Perm (Fin k)))
  let costs := perms.image (localCost c' u)
  have H : costs.Nonempty := Finset.univ_nonempty.image _
  let minC := costs.min' H
  have hmin : minC ∈ costs := Finset.min'_mem costs H
  rcases Finset.mem_image.mp hmin with ⟨σ, _, hcost⟩
  exact ⟨σ, hcost⟩

noncomputable def chooseOptPerm (c' : Coloring k) (u : Vertex k) : Equiv.Perm (Fin k) :=
  Classical.choose (exists_perm_minimizing_colorChanges (k:=k) c' u)

def canStartBothColorsAtOpt (k : ℕ) (c : Coloring k) (u : Vertex k) : Prop :=
  let minC := minChangesInCube k c u
  (∃ σ : Equiv.Perm (Fin k),
    let p := (AntiGeoData.mk u σ).toGeoPath
    p.colorChanges c = minC ∧
    (p.edgeColors c).head? = some true) ∧
  (∃ σ : Equiv.Perm (Fin k),
    let p := (AntiGeoData.mk u σ).toGeoPath
    p.colorChanges c = minC ∧
    (p.edgeColors c).head? = some false)

-- lemma ifCanStartBoth

noncomputable def adjustedCost (k : ℕ) (c : Coloring k) (u : Vertex k) : ℤ :=
  letI := Classical.propDecidable (canStartBothColorsAtOpt k c u)
  (minChangesInCube k c u : ℤ) - (if canStartBothColorsAtOpt k c u then 1 else 0)

-- Aristotle skipped at least one sorry in the block below (common reasons: Aristotle does not define data).
noncomputable def avgAdjustedCost (k : ℕ) (c : Coloring k) : ℚ :=
  (∑ u : Vertex k, (adjustedCost k c u : ℚ)) / (2 ^ k : ℚ)

-- Aristotle skipped at least one sorry in the block below (common reasons: Aristotle does not define data).
noncomputable def fhat (k : ℕ) : ℚ :=
  let costs := (Finset.univ : Finset (Coloring k)).image (avgAdjustedCost k)
  costs.max' (Finset.univ_nonempty.image _)


lemma avgAdjustedCost_le_fhat (k : ℕ) (c : Coloring k) :
    avgAdjustedCost k c ≤ fhat k := by
  -- unfold fhat as a Finset.max' / sup over all colorings
  unfold fhat
  apply Finset.le_max'
  apply Finset.mem_image_of_mem
  exact Finset.mem_univ c

lemma avgAdjustedCost_ge_neg_one (k : ℕ) (c : Coloring k) : -1 ≤ avgAdjustedCost k c := by
  unfold avgAdjustedCost
  field_simp
  have cost_per_u (u : Vertex k) : (-1 : ℤ) ≤ adjustedCost k c u := by
    unfold adjustedCost
    have minChange_pos : (0 : ℤ) ≤ minChangesInCube k c u := by
      exact Int.natCast_nonneg (minChangesInCube k c u)
    simp_all only [Nat.cast_nonneg, Int.reduceNeg, neg_le_sub_iff_le_add, ge_iff_le]
    split
    next h => simp_all only [le_add_iff_nonneg_left, Nat.cast_nonneg]
    next h =>
      have minChange_pos : (0 : ℤ) ≤ minChangesInCube k c u := by
       exact Int.natCast_nonneg (minChangesInCube k c u)
      omega
  have t := Finset.card_nsmul_le_sum (Finset.univ : Finset (Vertex k)) (fun u => adjustedCost k c u) (-1 : ℤ)
  simp only [mem_univ, Int.reduceNeg, forall_const, card_univ, Fintype.card_pi, Fintype.card_bool,
    prod_const, Fintype.card_fin, Int.nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_neg,
    mul_one] at t
  have tt := t cost_per_u
  exact_mod_cast tt

noncomputable def chooseOptPermStartingWith
  (c' : Coloring k) (u : Vertex k) (b : Bool)
  (h : canStartBothColorsAtOpt k c' u) : Equiv.Perm (Fin k) := by
  classical
  -- from h: there exists optimal σ starting with true and with false,
  -- so pick whichever matches b.
  by_cases hb : b = true
  · exact Classical.choose h.1  -- (σ, optimal, starts true)
  · have : b = false := by cases b <;> simp at hb ⊢
    -- pick from h.2
    exact Classical.choose h.2

structure ChunkChoice where
  σ : Equiv.Perm (Fin k)
  last : Bool

noncomputable def chooseChunk
  (c : Coloring n) (g : AntiGeoData n) (i : Fin (m (n := n) (k := k)))
  (prev : Option Bool) : ChunkChoice (k:=k) := by
  classical
  let c' := chunkColoring (n:=n) (k:=k) hk hkn c g i
  let u  := chunkStartSmall (n:=n) (k:=k) hk hkn g i
  let σ : Equiv.Perm (Fin k) :=
    match prev with
    | none =>
        chooseOptPerm (k:=k) c' u
    | some b =>
        if h : canStartBothColorsAtOpt k c' u then
          chooseOptPermStartingWith (k:=k) c' u b h
        else
          chooseOptPerm (k:=k) c' u
  let p := localPath (k:=k) u σ
  -- last edge color is at index k-1
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  let last := GeoPath.edgeColorAt (n:=k) (ℓ:=k) c' p ⟨k-1, by omega⟩
  exact ⟨σ, last⟩

noncomputable def chunkOrderFromChoice
  (g : AntiGeoData n) (i : Fin (m (n := n) (k := k)))
  (choice : ChunkChoice (k := k)) : List (Fin n) := by
  let q := chunkSubcube (n := n) (k := k) hk hkn g i
  exact List.ofFn (fun t : Fin k => (q.supportEquiv.symm (choice.σ t)).1)

lemma chooseOptPerm_spec
  (c' : Coloring k) (u : Vertex k) :
  localCost (k := k) c' u (chooseOptPerm (k := k) c' u) = minChangesInCube k c' u := by
  simpa [chooseOptPerm] using (Classical.choose_spec (exists_perm_minimizing_colorChanges (k := k) c' u))

lemma chooseOptPermStartingWith_spec_cost
  (c' : Coloring k) (u : Vertex k) (b : Bool)
  (h : canStartBothColorsAtOpt k c' u) :
  localCost (k := k) c' u (chooseOptPermStartingWith (k := k) c' u b h) = minChangesInCube k c' u := by
  classical
  by_cases hb : b = true
  · subst hb
    simpa [chooseOptPermStartingWith] using (Classical.choose_spec h.1).1
  · have hb' : b = false := by cases b <;> simp at hb ⊢
    subst hb'
    simpa [chooseOptPermStartingWith] using (Classical.choose_spec h.2).1

lemma chooseOptPermStartingWith_spec_first
  (c' : Coloring k) (u : Vertex k) (b : Bool)
  (h : canStartBothColorsAtOpt k c' u) :
  List.head? ((localPath (k := k) u (chooseOptPermStartingWith (k := k) c' u b h)).edgeColors c') = some b := by
  classical
  by_cases hb : b = true
  · subst hb
    simpa [chooseOptPermStartingWith] using (Classical.choose_spec h.1).2
  · have hb' : b = false := by cases b <;> simp at hb ⊢
    subst hb'
    simpa [chooseOptPermStartingWith] using (Classical.choose_spec h.2).2

lemma chooseChunk_sigma_opt
  (c : Coloring n) (g : AntiGeoData n) (i : Fin (m (n := n) (k := k)))
  (prev : Option Bool) :
  localCost (k := k)
      (chunkColoring (n := n) (k := k) hk hkn c g i)
      (chunkStartSmall (n := n) (k := k) hk hkn g i)
      (chooseChunk (n := n) (k := k) hk hkn c g i prev).σ
    =
  minChangesInCube k
      (chunkColoring (n := n) (k := k) hk hkn c g i)
      (chunkStartSmall (n := n) (k := k) hk hkn g i) := by
  classical
  cases prev with
  | none =>
      simp [chooseChunk, chooseOptPerm_spec]
  | some b =>
      by_cases h :
          canStartBothColorsAtOpt k
            (chunkColoring (n := n) (k := k) hk hkn c g i)
            (chunkStartSmall (n := n) (k := k) hk hkn g i)
      · simp [chooseChunk, h, chooseOptPermStartingWith_spec_cost]
      · simp [chooseChunk, h, chooseOptPerm_spec]

lemma chooseChunk_firstColor_eq_prev_of_canStartBoth
  (c : Coloring n) (g : AntiGeoData n) (i : Fin (m (n := n) (k := k)))
  (b : Bool)
  (h : canStartBothColorsAtOpt k
        (chunkColoring (n := n) (k := k) hk hkn c g i)
        (chunkStartSmall (n := n) (k := k) hk hkn g i)) :
  List.head?
      ((localPath (k := k)
          (chunkStartSmall (n := n) (k := k) hk hkn g i)
          (chooseChunk (n := n) (k := k) hk hkn c g i (some b)).σ).edgeColors
        (chunkColoring (n := n) (k := k) hk hkn c g i))
    = some b := by
  classical
  simp [chooseChunk, h, chooseOptPermStartingWith_spec_first]

noncomputable def algorithm1Step
  (c : Coloring n) (g : AntiGeoData n) :
    (List (Fin n) × Option Bool) → Nat → (List (Fin n) × Option Bool) :=
  fun acc i =>
    let soFar := acc.1
    let prev  := acc.2
    if hi : i < numChunks n k then
      let ii : Fin (numChunks n k) := ⟨i, hi⟩
      let choice := chooseChunk (n := n) (k := k) hk hkn c g ii prev
      let chunkOrder := chunkOrderFromChoice (n := n) (k := k) hk hkn g ii choice
      (soFar ++ chunkOrder, some choice.last)
    else
      acc

noncomputable def algorithm1ChunkAcc
  (c : Coloring n) (g : AntiGeoData n) : List (Fin n) × Option Bool :=
  (List.range (numChunks n k)).foldl (algorithm1Step (n := n) (k := k) hk hkn c g) ([], none)

noncomputable def algorithm1ChunkCoords
  (c : Coloring n) (g : AntiGeoData n) : List (Fin n) :=
  (algorithm1ChunkAcc (n := n) (k := k) hk hkn c g).1

noncomputable def algorithm1FinalCoords
  (c : Coloring n) (g : AntiGeoData n) : List (Fin n) :=
  (algorithm1ChunkCoords (n := n) (k := k) hk hkn c g) ++
    (List.ofFn g.perm).drop ((numChunks n k) * k)

noncomputable def algorithm1
  {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (c : Coloring n) :
  AntiGeoData n → GeoPath n n := by
  classical
  intro g
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_two (le_trans hk hkn)
  let defaultCoord : Fin n := ⟨0, hn⟩
  let finalCoords := algorithm1FinalCoords (n := n) (k := k) hk hkn c g
  -- turn the coordinate list into a coordinate function for `GeoPath.ofCoordFn`
  let coordAt : Fin n → Fin n := fun t => finalCoords.getD t.1 defaultCoord
  exact GeoPath.ofCoordFn (n:=n) g.start coordAt

noncomputable def chunkContribution (k : ℕ) (c : Coloring k) (u : Vertex k) : ℤ :=
  letI := Classical.propDecidable (canStartBothColorsAtOpt k c u)
  (minChangesInCube k c u : ℤ) + (if canStartBothColorsAtOpt k c u then 0 else 1)

/--
Key inequality used in Lemma 8: the chunk contribution is bounded by `adjustedCost + 1`.
With the above definition of `chunkContribution`, this is actually an equality case-by-case.
-/
lemma chunkContribution_le_adjustedCost_add_one
  (k : ℕ) (c : Coloring k) (u : Vertex k) :
  chunkContribution k c u ≤ adjustedCost k c u + 1 := by
  classical
  by_cases h : canStartBothColorsAtOpt k c u
  · -- if we can start optimal paths with either color, the penalty is `0`
    simp [chunkContribution, adjustedCost, h]
  · -- otherwise we may need to pay `+1`
    simp [chunkContribution, adjustedCost, h]

/-- (Optional) Same lemma, but already cast to `ℚ`. -/
lemma chunkContribution_le_adjustedCost_add_one_q
  (k : ℕ) (c : Coloring k) (u : Vertex k) :
  (chunkContribution k c u : ℚ) ≤ (adjustedCost k c u : ℚ) + 1 := by
  have hz : chunkContribution k c u ≤ adjustedCost k c u + 1 :=
    chunkContribution_le_adjustedCost_add_one (k:=k) (c:=c) (u:=u)
  exact_mod_cast hz

noncomputable def algoCost {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (c : Coloring n) (g : AntiGeoData n) : Nat :=
  changesFromOrder c g.start (algorithm1FinalCoords (n := n) (k := k) hk hkn c g)

def expectedCost (n : ℕ) (X : AntiGeoData n → ℚ) : ℚ := by
  classical
  exact (∑ g, X g) / (Fintype.card (AntiGeoData n) : ℚ)

/-! ### Lemma 8 (current placeholder Algorithm 1 version) -/

-- lemma avgAdjustedCost_le_fhat (k : ℕ) (c : Coloring k) :
--     avgAdjustedCost k c ≤ fhat k := by
--   -- unfold fhat as a Finset.max' / sup over all colorings
--   unfold fhat
--   apply Finset.le_max'
--   apply Finset.mem_image_of_mem
--   exact Finset.mem_univ c

lemma edgeOf_swap {n : ℕ} (u v : Vertex n) : edgeOf u v = edgeOf v u := by
  -- `Sym2` is the quotient identifying `(u,v)` with `(v,u)`.
  simp [edgeOf]

/-- A constant-color list has no color changes. -/
lemma changesOnColors_replicate (m : ℕ) (b : Bool) :
    changesOnColors (List.replicate m b) = 0 := by
  induction m with
  | zero =>
      simp [changesOnColors]
  | succ m ih =>
      cases m with
      | zero =>
          simp [changesOnColors]
      | succ m =>
          -- `replicate (m+2) b = b :: b :: replicate m b`
          simp only [List.replicate, changesOnColors, ↓reduceIte, zero_add]
          simp only [List.replicate] at ih
          exact ih

/-- All-false vertex. -/
def bounceV0 (n : ℕ) : Vertex n := fun _ => false

/-- The vertex that is `true` only at coordinate `0`. Requires `n > 0`. -/
def bounceV1 (n : ℕ) (hn : 0 < n) : Vertex n :=
  fun i => if i = (⟨0, hn⟩ : Fin n) then true else false

lemma hamming_bounceV0_bounceV1 {n : ℕ} (hn : 0 < n) :
    hamming (bounceV0 n) (bounceV1 n hn) = 1 := by
  classical
  -- The two vertices differ exactly at coordinate 0.
  unfold hamming diffCoords bounceV0 bounceV1
  have :
      (univ.filter (fun i : Fin n =>
        (fun _ => false) i ≠ (fun i => if i = (⟨0, hn⟩ : Fin n) then true else false) i))
        = ({(⟨0, hn⟩ : Fin n)} : Finset (Fin n)) := by
    ext i
    by_cases hi : i = (⟨0, hn⟩ : Fin n)
    · simp [hi]
    · simp [hi]
  simp at this
  simp
  aesop

lemma modTwo_succ_eq_one_of_eq_zero (a : ℕ) (h : a % 2 = 0) : (a + 1) % 2 = 1 := by
  -- (a+1) % 2 = (a%2 + 1%2) % 2
  have h' : (a + 1) % 2 = (a % 2 + 1 % 2) % 2 := by
    simp [Nat.add_mod]
  -- simplify with `h`
  simp [h, h']

lemma modTwo_eq_one_of_ne_zero (a : ℕ) (h : a % 2 ≠ 0) : a % 2 = 1 := by
  -- since a%2 < 2 and not 0, it must be 1
  have hlt : a % 2 < 2 := Nat.mod_lt a (by decide)
  have hle : a % 2 ≤ 1 := by
    have : a % 2 < Nat.succ 1 := by simpa using hlt
    exact (Nat.lt_succ_iff.mp this)
  have hge : 1 ≤ a % 2 := by
    have : 0 < a % 2 := Nat.pos_of_ne_zero h
    exact Nat.succ_le_iff.mpr this
  exact Nat.le_antisymm hle hge

lemma modTwo_succ_eq_zero_of_ne_zero (a : ℕ) (h : a % 2 ≠ 0) : (a + 1) % 2 = 0 := by
  have ha : a % 2 = 1 := modTwo_eq_one_of_ne_zero a h
  have h' : (a + 1) % 2 = (a % 2 + 1 % 2) % 2 := by
    simp [Nat.add_mod]
  -- simplify with `ha`; (1+1)%2 = 0
  simp [ha, h']

/-- A concrete length-`n` walk alternating along the fixed edge between `bounceV0` and `bounceV1`. -/
noncomputable def bouncePath (n : ℕ) (hn : 0 < n) : GeoPath n n := by
  classical
  refine
  { verts := fun t : Fin (n+1) =>
      if t.1 % 2 = 0 then bounceV0 n else bounceV1 n hn
    adj := ?_ }
  intro i
  -- adjacency in the cube is exactly `hamming = 1`
  by_cases hpar : i.1 % 2 = 0
  · have hsucc : (i.1 + 1) % 2 = 1 := modTwo_succ_eq_one_of_eq_zero i.1 hpar
    -- edge is `bounceV0 -- bounceV1`
    simp [cube, hpar, hsucc, hamming_bounceV0_bounceV1 (n:=n) hn]
  · have hsucc : (i.1 + 1) % 2 = 0 := modTwo_succ_eq_zero_of_ne_zero i.1 hpar
    -- edge is `bounceV1 -- bounceV0`
    simp [cube, hpar, hsucc, hamming_symmetric, hamming_bounceV0_bounceV1 (n:=n) hn]

lemma bouncePath_colorChanges (n : ℕ) (hn : 0 < n) (c : Coloring n) :
    (bouncePath n hn).colorChanges c = 0 := by
  classical
  -- The edge color is constant along the path.
  have hconst :
      (fun i : Fin n =>
          c (edgeOf ((bouncePath n hn).verts i.castSucc)
                    ((bouncePath n hn).verts i.succ)))
        = (fun _ : Fin n => c (edgeOf (bounceV0 n) (bounceV1 n hn))) := by
    funext i
    by_cases hpar : i.1 % 2 = 0
    · have hsucc : (i.1 + 1) % 2 = 1 := modTwo_succ_eq_one_of_eq_zero i.1 hpar
      -- verts are (v0,v1)
      simp [bouncePath, hpar, hsucc]
    · have hsucc : (i.1 + 1) % 2 = 0 := modTwo_succ_eq_zero_of_ne_zero i.1 hpar
      -- verts are (v1,v0); swap the undirected edge
      have : edgeOf (bounceV1 n hn) (bounceV0 n) = edgeOf (bounceV0 n) (bounceV1 n hn) := by
        simpa using (edgeOf_swap (n:=n) (bounceV1 n hn) (bounceV0 n))
      simp [bouncePath, hpar, hsucc, this]
  -- compute `edgeColors` and finish
  unfold GeoPath.colorChanges GeoPath.edgeColors
  simp [hconst, List.ofFn_const, changesOnColors_replicate]

lemma fhat_ge_neg_one (k : ℕ) : (-1 : ℚ) ≤ fhat k := by
  classical
  -- pick any coloring; its average is ≥ -1 and ≤ fhat
  let c0 : Coloring k := fun _ => false
  have h1 : (-1 : ℚ) ≤ avgAdjustedCost k c0 := avgAdjustedCost_ge_neg_one k c0
  have h2 : avgAdjustedCost k c0 ≤ fhat k := avgAdjustedCost_le_fhat (k:=k) c0
  exact le_trans h1 h2

-- apply Finset.mem_image_of_mem
  -- exact Finset.mem_univ c


-- I’m assuming your definition:
-- def expectedCost (n : ℕ) (X : AntiGeoData n → ℚ) : ℚ :=
--   (∑ g, X g) / (Fintype.card (AntiGeoData n) : ℚ)

lemma antiGeoData_nonempty (n : ℕ) : Nonempty (AntiGeoData n) := by
  exact ⟨⟨fun _ => false, Equiv.refl _⟩⟩

lemma expectedCost_const (n : ℕ) (a : ℚ) :
    expectedCost n (fun _ : AntiGeoData n => a) = a := by
  classical
  unfold expectedCost
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_card : (Fintype.card (AntiGeoData n) : ℚ) ≠ 0 := by
    norm_cast
    refine Nat.ne_zero_iff_zero_lt.mpr ?_
    exact_mod_cast (Fintype.card_pos_iff.mpr (antiGeoData_nonempty n))
  field_simp [h_card]

lemma expectedCost_add (n : ℕ) (X Y : AntiGeoData n → ℚ) :
    expectedCost n (fun g => X g + Y g)
      = expectedCost n X + expectedCost n Y := by
  classical
  unfold expectedCost
  -- distribute sum and division
  simp [Finset.sum_add_distrib, add_div]

lemma expectedCost_sum
  (n : ℕ) {ι : Type} [Fintype ι]
  (f : ι → AntiGeoData n → ℚ) :
    expectedCost n (fun g => ∑ i : ι, f i g)
      = ∑ i : ι, expectedCost n (f i) := by
  classical
  unfold expectedCost
  -- swap the two finite sums
  rw [Finset.sum_comm]
  rw [Finset.sum_div]

lemma expectedCost_sum_fin {n m : ℕ} (X : Fin m → AntiGeoData n → ℚ) :
    expectedCost n (fun g => ∑ i : Fin m, X i g)
      = ∑ i : Fin m, expectedCost n (X i) := by
  classical
  unfold expectedCost
  have hcomm :
      (∑ g : AntiGeoData n, ∑ i : Fin m, X i g)
        = ∑ i : Fin m, ∑ g : AntiGeoData n, X i g := by
    simpa using (Finset.sum_comm (f := fun g i => X i g))
  -- pull out the (constant) denominator
  have hcard : (Fintype.card (AntiGeoData n) : ℚ) ≠ 0 := by
    norm_cast
    refine Nat.ne_zero_iff_zero_lt.mpr ?_
    exact_mod_cast (Fintype.card_pos_iff.mpr (antiGeoData_nonempty n))
  -- `simp` can finish after rewriting the numerator with `hcomm`
  -- and using `div_eq_mul_inv` + `Finset.sum_mul`/`mul_sum`.
  -- In ℚ this is straightforward.
  simp [hcomm, div_eq_mul_inv]
  field_simp [hcard]
  rw [Finset.mul_sum]
  field_simp

/-- Monotonicity: pointwise ≤ implies expectation ≤. -/
lemma expectedCost_mono (n : ℕ) {X Y : AntiGeoData n → ℚ}
    (h : ∀ g, X g ≤ Y g) :
    expectedCost n X ≤ expectedCost n Y := by
  classical
  unfold expectedCost
  -- sum_le_sum, then divide by positive card
  have hsum : (∑ g, X g) ≤ ∑ g, Y g := by
    exact Finset.sum_le_sum (fun g _ => h g)
  have hcard_pos : (0 : ℚ) < (Fintype.card (AntiGeoData n) : ℚ) := by
    -- card > 0
    simp_all only [Nat.cast_pos]
    apply Fintype.card_pos_iff.mpr
    exact antiGeoData_nonempty n
  -- divide by positive
  exact (div_le_div_of_nonneg_right hsum (le_of_lt hcard_pos))

noncomputable def chunkContributionG {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (c : Coloring n)
    (i : Fin (numChunks n k)) (g : AntiGeoData n) : ℚ :=
  chunkContribution k (@chunkColoring n k hk hkn _ c g i) (@chunkStartSmall n k hk hkn _ g i)

-- lemma expected_adjustedCost_eq_expected_avgAdjustedCost
--   (k : ℕ) (c : Coloring k) :
--   expectedCost k (fun u => (adjustedCost k c u : ℚ))
--     = avgAdjustedCost k c := by
--   classical
--   -- unfold both sides
--   unfold expectedCost avgAdjustedCost
--   -- rewrite the denominator `(Fintype.card (Vertex k) : ℚ)` as `(2^k : ℚ)`
--   have hcardQ : (Fintype.card (Vertex k) : ℚ) = (2 ^ k : ℚ) := by
--     exact_mod_cast (card_Vertex k)
--   -- now it’s literally the same expression
--   simp [hcardQ]




/-- Factor a sum over `AntiGeoData n` as a double sum over permutations and start vertices. -/
private lemma sum_antiGeoData_eq_sum_perm_sum_start
    {β : Type*} [AddCommMonoid β]
    (f : AntiGeoData n → β) :
    ∑ g : AntiGeoData n, f g
      = ∑ σ : Equiv.Perm (Fin n), ∑ s : Vertex n, f ⟨s, σ⟩ := by
  -- Build the equivalence AntiGeoData n ≃ Perm (Fin n) × Vertex n
  let e : Equiv.Perm (Fin n) × Vertex n ≃ AntiGeoData n :=
    { toFun := fun p => ⟨p.2, p.1⟩
      invFun := fun g => (g.perm, g.start)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  -- Use the equivalence to reindex, then split the product sum
  rw [← e.sum_comp, Fintype.sum_prod_type]
  -- After splitting, `f (e (σ, s))` reduces to `f ⟨s, σ⟩`
  rfl

/-- The chunk support depends only on the permutation, not the start vertex. -/
private lemma chunkSupport_start_indep
    (s₁ s₂ : Vertex n) (σ : Equiv.Perm (Fin n))
    (i : Fin (numChunks n k)) :
    chunkSupport (n:=n) (k:=k) hkn ⟨s₁, σ⟩ i
      = chunkSupport (n:=n) (k:=k) hkn ⟨s₂, σ⟩ i := by
  -- chunkSupport only references g.perm, never g.start
  unfold chunkSupport
  rfl

/-- If two start vertices agree outside the chunk support, they induce the same chunk coloring.
    Intuitively: the induced coloring on the k-subcube depends on the original coloring `c`
    and on the "base" vertex of the subcube (which uses non-support coordinates of `start`),
    but NOT on the support coordinates of `start`. -/
private lemma chunkColoring_support_invariant
    (c : Coloring n) (σ : Equiv.Perm (Fin n))
    (s₁ s₂ : Vertex n) (i : Fin (numChunks n k))
    (h : ∀ j : Fin n, j ∉ chunkSupport (n:=n) (k:=k) hkn ⟨s₁, σ⟩ i → s₁ j = s₂ j) :
    chunkColoring (n:=n) (k:=k) hk hkn c ⟨s₁, σ⟩ i
      = chunkColoring (n:=n) (k:=k) hk hkn c ⟨s₂, σ⟩ i := by
  -- It suffices to show the two chunkSubcubes are equal (then inducedColoring is equal).
  -- The support is the same (depends only on σ), so we need the base to agree.
  -- The base at j ∈ support is `false` in both cases.
  -- The base at j ∉ support is `chunkStartVertex(j)`, which depends on s only at coordinate j,
  -- and j ∉ support so s₁ j = s₂ j by assumption h.
  suffices hsub : chunkSubcube (n:=n) (k:=k) hk hkn ⟨s₁, σ⟩ i
      = chunkSubcube (n:=n) (k:=k) hk hkn ⟨s₂, σ⟩ i by
    unfold chunkColoring
    rw [hsub]
  unfold chunkSubcube
  simp only [dite_eq_ite, Bool.if_false_left, Subcube.mk.injEq]
  constructor
  · rfl
  · ext x
    by_cases hx : x ∈ chunkSupport hkn ⟨s₁, σ⟩ i
    · have hx2 : x ∈ chunkSupport hkn ⟨s₂, σ⟩ i := by
        rw [← chunkSupport_start_indep hkn s₁ s₂ σ i]
        exact hx
      simp only [hx, hx2]
      rfl
    · have hx2 : x ∉ chunkSupport hkn ⟨s₂, σ⟩ i := by
        rw [← chunkSupport_start_indep hkn s₁ s₂ σ i]
        exact hx
      simp only [hx, hx2]
      unfold chunkStartVertex AntiGeoData.toGeoPath
      apply vertsNat_congr_at_x
      · apply h
        exact hx

/-- If two start vertices agree on the chunk support, they produce the same small start vertex.
    Intuitively: `chunkStartSmall` decodes the "big" start vertex onto the k-subcube
    by reading only the support coordinates. -/
private lemma chunkStartSmall_complement_invariant
    (σ : Equiv.Perm (Fin n))
    (s₁ s₂ : Vertex n) (i : Fin (numChunks n k))
    (h : ∀ j : Fin n, j ∈ chunkSupport (n:=n) (k:=k) hkn ⟨s₁, σ⟩ i → s₁ j = s₂ j) :
    chunkStartSmall (n:=n) (k:=k) hk hkn ⟨s₁, σ⟩ i
      = chunkStartSmall (n:=n) (k:=k) hk hkn ⟨s₂, σ⟩ i := by
    unfold chunkStartSmall
    let q1 := chunkSubcube hk hkn ⟨s₁, σ⟩ i
    let q2 := chunkSubcube hk hkn ⟨s₂, σ⟩ i
    have h_supp_eq : q1.support = q2.support := by
      unfold q1 q2
      unfold chunkSubcube
      simp only [chunkSupport_start_indep hkn s₁ s₂ σ i]
    ext j'
    unfold Subcube.decode
    let x1 := q1.supportEquiv.symm j'
    let x2 := q2.supportEquiv.symm j'
    have hx_eq : x1.1 = x2.1 := by
      unfold x1 x2
      cases h_supp_eq
      rfl
    have h_v1 : chunkStartVertex hk hkn ⟨s₁, σ⟩ i x1.1 = s₁ x1.1 := by
      unfold chunkStartVertex AntiGeoData.toGeoPath GeoPath.ofCoordFn
      simp only []
      apply vertsNat_not_flipped
      intro j hj hjn h_flip_idx
      have hx1_supp := x1.2
      unfold q1 chunkSubcube chunkSupport at hx1_supp
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx1_supp
      rcases hx1_supp with ⟨j_supp, hj_supp_eq⟩
      -- h_flip_idx : σ ⟨j, hjn⟩ = x1.1
      -- hj_supp_eq : σ ⟨k * i.1 + j_supp.1, ...⟩ = x1.1
      have h_eq_idx := σ.injective (h_flip_idx.trans hj_supp_eq.symm)
      rw [Fin.ext_iff] at h_eq_idx
      simp at h_eq_idx
      unfold numChunks at i
      omega
    have h_v2 : chunkStartVertex hk hkn ⟨s₂, σ⟩ i x2.1 = s₂ x2.1 := by
      unfold chunkStartVertex AntiGeoData.toGeoPath GeoPath.ofCoordFn
      simp only []
      apply vertsNat_not_flipped
      intro j hj hjn h_flip_idx
      have hx2_supp := x2.2
      unfold q2 chunkSubcube chunkSupport at hx2_supp
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx2_supp
      rcases hx2_supp with ⟨j_supp, hj_supp_eq⟩
      -- h_flip_idx : σ ⟨j, hjn⟩ = x2.1
      -- hj_supp_eq : σ ⟨k * i.1 + j_supp.1, ...⟩ = x2.1
      have h_eq_idx := σ.injective (h_flip_idx.trans hj_supp_eq.symm)
      rw [Fin.ext_iff] at h_eq_idx
      simp at h_eq_idx
      unfold numChunks at i
      omega
    rw [h_v1, h_v2, hx_eq]
    apply h
    have hx1_supp_val : x1.1 ∈ chunkSupport hkn ⟨s₁, σ⟩ i := by
      let h' := x1.2
      unfold q1 chunkSubcube at h'
      exact h'
    change x2.1 ∈ chunkSupport hkn ⟨s₁, σ⟩ i
    rw [← hx_eq]
    exact hx1_supp_val

/-- Equivalence splitting `Vertex n` into values on a finset `S` and its complement. -/
private noncomputable def vertexSplitEquiv' (S : Finset (Fin n)) :
    Vertex n ≃ (↥S → Bool) × (↥(Sᶜ) → Bool) where
  toFun v := (fun ⟨j, _⟩ => v j, fun ⟨j, _⟩ => v j)
  invFun p := fun j =>
    if h : j ∈ S then p.1 ⟨j, h⟩
    else p.2 ⟨j, Finset.mem_compl.mpr h⟩
  left_inv v := by
    funext j; simp only; split_ifs <;> rfl
  right_inv p := by
    ext1
    · ext ⟨j, hj⟩; simp [hj]
    · ext ⟨j, hj⟩; simp [Finset.mem_compl.mp hj]

/-- For fixed σ, the map from support-bit-assignments to `Vertex k` via `chunkStartSmall`
    is a bijection. This follows because `decode` reads exactly the support coordinates
    (reindexed via `supportEquiv`), and the support coordinates of `chunkStartVertex`
    equal the start vertex at those coordinates (no prior flips touch them). -/
private lemma chunkStartSmall_support_bijective
    (σ : Equiv.Perm (Fin n)) (i : Fin (numChunks n k))
    (b : ↥((chunkSupport (n := n) (k := k) hkn ⟨fun _ => false, σ⟩ i)ᶜ) → Bool) :
    Function.Bijective (fun a : ↥(chunkSupport (n:=n) (k:=k) hkn ⟨fun _ => false, σ⟩ i) → Bool =>
      chunkStartSmall (n:=n) (k:=k) hk hkn
        ⟨(vertexSplitEquiv' (chunkSupport (n:=n) (k:=k) hkn ⟨fun _ => false, σ⟩ i)).symm (a, b), σ⟩ i) := by
  let S := chunkSupport (n:=n) (k:=k) hkn ⟨fun _ => false, σ⟩ i
  let f := (fun a : (↥S → Bool) =>
      chunkStartSmall (n:=n) (k:=k) hk hkn
        ⟨(vertexSplitEquiv' S).symm (a, b), σ⟩ i)
  have h_base : ∀ a, (chunkSubcube hk hkn ⟨(vertexSplitEquiv' S).symm (a, b), σ⟩ i).support = S := by
    intro a
    unfold chunkSubcube
    simp only [chunkSupport_start_indep hkn _ (fun _ => false) σ i]
    rfl
  let q_ref := chunkSubcube hk hkn ⟨fun _ => false, σ⟩ i
  have h_S_ref : q_ref.support = S := rfl
  let reindex : ↥S ≃ Fin k := q_ref.supportEquiv
  have h_f_eq : ∀ a, f a = a ∘ reindex.symm := by
    intro a
    let s := (vertexSplitEquiv' S).symm (a, b)
    let q := chunkSubcube hk hkn ⟨s, σ⟩ i
    have h_v : ∀ j', chunkStartVertex hk hkn ⟨s, σ⟩ i (q.supportEquiv.symm j').1 = s (q.supportEquiv.symm j').1 := by
      intro j'
      unfold chunkStartVertex AntiGeoData.toGeoPath GeoPath.ofCoordFn
      apply vertsNat_not_flipped
      intro j_step hj_step hjn
      let x := (q.supportEquiv.symm j').1
      have hx_q_supp : x ∈ q.support := (q.supportEquiv.symm j').2
      simp only [q, chunkSubcube, chunkSupport, Finset.mem_image, Finset.mem_univ, true_and] at hx_q_supp
      rcases hx_q_supp with ⟨j_supp, hj_supp_eq⟩
      intro h_flip
      have h_eq_idx : j_step = k * i.val + j_supp.val := by
        have h_bound : k * i.val + j_supp.val < n := by
          have hi : i.val < n / k := i.is_lt
          have hj : j_supp.val < k := j_supp.is_lt
          calc
            k * i.val + j_supp.val < k * i.val + k := Nat.add_lt_add_left hj _
            _ = k * (i.val + 1) := by rw [Nat.mul_add, Nat.mul_one]
            _ ≤ k * (n / k) := Nat.mul_le_mul_left k hi
            _ = (n / k) * k := Nat.mul_comm k _
            _ ≤ n := Nat.div_mul_le_self n k
        have : (⟨j_step, hjn⟩ : Fin n) = ⟨k * i.val + j_supp.val, h_bound⟩ := by
          apply σ.injective
          rw [h_flip, hj_supp_eq]
        exact Fin.ext_iff.mp this
      have h_ge : j_step ≥ k * i.val := by omega
      exact absurd hj_step (not_lt_of_ge h_ge)
    ext j'
    unfold f chunkStartSmall Subcube.decode
    rw [h_v j']
    unfold s vertexSplitEquiv'
    simp only [Equiv.coe_fn_symm_mk]
    have h_qS : q.support = S := h_base a
    revert j'
    cases h_qS
    intro j'
    split_ifs with h_mem
    · have h_eq : q.supportEquiv = reindex := rfl
      simp only [h_eq]
      rfl
    · have : (q.supportEquiv.symm j').1 ∈ S := (q.supportEquiv.symm j').2
      contradiction
  change Function.Bijective f
  rw [funext h_f_eq]
  exact (Equiv.arrowCongr reindex (Equiv.refl Bool)).bijective

/-- For fixed σ, summing any function `h(chunkColoring, chunkStartSmall)` over all start vertices
    equals summing `(∑ u, h(chunkColoring, u)) / 2^k` over all start vertices.

    This captures the key uniformity property: as the start vertex `s` ranges over `Vertex n`,
    `chunkStartSmall s` is "uniformly distributed" over `Vertex k` conditioned on the chunk
    coloring (which depends only on the complement-of-support bits of `s`).

    Proof sketch: split `Vertex n ≃ (S → Bool) × (Sᶜ → Bool)` where `S` is the chunk support.
    For fixed complement bits, `chunkColoring` is constant and `chunkStartSmall` bijects
    with `Vertex k`. So the inner sum over support bits of `h(c', u_{sup})` equals
    `∑_{v : Vertex k} h(c', v)`, and the inner sum of the averaged version equals
    `2^k · (∑_v h(c', v)) / 2^k = ∑_v h(c', v)` as well. -/
private lemma sum_vertex_chunkStartSmall_avg
    (c : Coloring n) (σ : Equiv.Perm (Fin n)) (i : Fin (numChunks n k))
    (h : Coloring k → Vertex k → ℚ) :
    ∑ s : Vertex n,
      h (chunkColoring (n:=n) (k:=k) hk hkn c ⟨s, σ⟩ i)
        (chunkStartSmall (n:=n) (k:=k) hk hkn ⟨s, σ⟩ i)
    = ∑ s : Vertex n,
      (∑ u : Vertex k,
        h (chunkColoring (n:=n) (k:=k) hk hkn c ⟨s, σ⟩ i) u) / (2 ^ k : ℚ) := by
  let s₀ : Vertex n := fun _ => false
  let S := chunkSupport hkn ⟨s₀, σ⟩ i
  let eqv := vertexSplitEquiv' S
  -- Transform the LHS sum
  have h_lhs : ∑ s : Vertex n, h (chunkColoring hk hkn c ⟨s, σ⟩ i) (chunkStartSmall hk hkn ⟨s, σ⟩ i)
      = ∑ b : ↥(Sᶜ) → Bool, ∑ a : ↥S → Bool, h (chunkColoring hk hkn c ⟨eqv.symm (a, b), σ⟩ i) (chunkStartSmall hk hkn ⟨eqv.symm (a, b), σ⟩ i) := by
    rw [← Equiv.sum_comp eqv.symm, Fintype.sum_prod_type, Finset.sum_comm]
  have h_S_card : Fintype.card S = k := by
    unfold S
    have S_c := chunkSupport_card hkn ⟨s₀, σ⟩ i
    simp [S_c]
    -- rfl
  have h_rhs : ∑ s : Vertex n, (∑ u : Vertex k, h (chunkColoring hk hkn c ⟨s, σ⟩ i) u) / (2 ^ k : ℚ)
      = ∑ b : ↥(Sᶜ) → Bool, ∑ a : ↥S → Bool, (∑ u : Vertex k, h (chunkColoring hk hkn c ⟨eqv.symm (a, b), σ⟩ i) u) / (2 ^ k : ℚ) := by
    rw [← Equiv.sum_comp eqv.symm, Fintype.sum_prod_type, Finset.sum_comm]
  rw [h_lhs, h_rhs]
  apply Finset.sum_congr rfl
  intro b _
  -- 1. Chunk coloring is independent of support bits 'a'
  have h_c_fixed : ∀ a₁ a₂ : ↥S → Bool,
      chunkColoring hk hkn c ⟨eqv.symm (a₁, b), σ⟩ i = chunkColoring hk hkn c ⟨eqv.symm (a₂, b), σ⟩ i := by
    intro a₁ a₂
    apply chunkColoring_support_invariant
    intro j hj
    unfold eqv vertexSplitEquiv'
    simp only [Equiv.coe_fn_symm_mk]
    split_ifs with hjS
    · contradiction
    · rfl
  -- Pick a representative a_base (e.g. fun _ => false) to pull it out
  let a_base : ↥S → Bool := fun _ => false
  let c_fixed := chunkColoring hk hkn c ⟨eqv.symm (a_base, b), σ⟩ i
  have h_left : ∑ a : ↥S → Bool, h (chunkColoring hk hkn c ⟨eqv.symm (a, b), σ⟩ i) (chunkStartSmall hk hkn ⟨eqv.symm (a, b), σ⟩ i)
      = ∑ a : ↥S → Bool, h c_fixed (chunkStartSmall hk hkn ⟨eqv.symm (a, b), σ⟩ i) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [h_c_fixed a a_base]
    -- rfl
  have h_right : ∑ a : ↥S → Bool, (∑ u : Vertex k, h (chunkColoring hk hkn c ⟨eqv.symm (a, b), σ⟩ i) u) / (2 ^ k : ℚ)
      = ∑ a : ↥S → Bool, (∑ u : Vertex k, h c_fixed u) / (2 ^ k : ℚ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [h_c_fixed a a_base]
    -- rfl
  rw [h_left, h_right]
  -- 2. Inner sum on left: use bijection
  let f_bij := fun a : (↥S → Bool) => chunkStartSmall hk hkn ⟨eqv.symm (a, b), σ⟩ i
  have h_f_bij : Function.Bijective f_bij := chunkStartSmall_support_bijective hk hkn σ i b
  -- Use the bijection to reindex the sum
  have h_bij_sum : ∑ a, h c_fixed (f_bij a) = ∑ u : Vertex k, h c_fixed u := by
    apply Fintype.sum_bijective f_bij h_f_bij
    intro x
    simp_all only [mem_univ, sum_const, card_univ, Fintype.card_pi, univ_eq_attach, Fintype.card_bool, prod_const,
      card_attach, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, Multiset.bijective_iff_map_univ_eq_univ, S, s₀, eqv,
      c_fixed, a_base, f_bij]
  rw [h_bij_sum]
  -- 3. Inner sum on right: constant summand
  simp only [sum_const, Fintype.card_fun, card_univ, nsmul_eq_mul, h_S_card, Fintype.card_bool]
  -- 2^k * (sum / 2^k) = sum
  have h_pow : (2 ^ k : ℚ) ≠ 0 := by
    apply pow_ne_zero; norm_num
  field_simp [h_pow]
  exact_mod_cast rfl

private lemma sum_adjustedCost_eq_sum_avgAdjustedCost_fixed_perm
    (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    [DecidableEq (Fin n)]
    (c : Coloring n) (i : Fin (numChunks n k))
    (σ : Equiv.Perm (Fin n)) :
    ∑ s : Vertex n,
      (adjustedCost k
        (chunkColoring (n:=n) (k:=k) hk hkn c ⟨s, σ⟩ i)
        (chunkStartSmall (n:=n) (k:=k) hk hkn ⟨s, σ⟩ i) : ℚ)
    = ∑ s : Vertex n,
      avgAdjustedCost k
        (chunkColoring (n:=n) (k:=k) hk hkn c ⟨s, σ⟩ i) := by
  -- Step 1: Apply the averaging lemma to reindex the LHS
  rw [sum_vertex_chunkStartSmall_avg hk hkn c σ i
      (fun c' u => (adjustedCost k c' u : ℚ))]
  -- Step 2: The summands now match the definition of avgAdjustedCost
  simp only [avgAdjustedCost]

lemma expected_adjustedCost_eq_expected_avgAdjustedCost
  (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
  (c : Coloring n) (i : Fin (numChunks n k)) :
  expectedCost n
      (fun g =>
        (adjustedCost k
          (chunkColoring (n:=n) (k:=k) hk hkn c g i)
          (chunkStartSmall (n:=n) (k:=k) hk hkn g i) : ℚ))
    =
  expectedCost n
      (fun g =>
        avgAdjustedCost k
          (chunkColoring (n:=n) (k:=k) hk hkn c g i)) := by
  classical
  -- Unfold expectedCost: both sides are (∑ g, ·) / card, so it suffices
  -- to show the numerators are equal.
  unfold expectedCost
  congr 1
  -- Factor both sums as ∑ σ, ∑ s using the product decomposition of AntiGeoData
  rw [sum_antiGeoData_eq_sum_perm_sum_start, sum_antiGeoData_eq_sum_perm_sum_start]
  -- Now apply the per-permutation equality
  congr 1; ext σ
  exact sum_adjustedCost_eq_sum_avgAdjustedCost_fixed_perm n k hk hkn c i σ

/-- The lemma you said is currently `sorry`: it becomes a one-liner once the bridge lemma exists. -/
lemma expected_adjustedCost_le_fhat
  (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (c : Coloring n)
  (i : Fin (numChunks n k)) :
  expectedCost n
      (fun g =>
        (adjustedCost k
          (chunkColoring (n:=n) (k:=k) hk hkn c g i)
          (chunkStartSmall (n:=n) (k:=k) hk hkn g i) : ℚ))
    ≤ fhat k := by
  classical
  -- Step 1: replace adjustedCost-at-random-start by avgAdjustedCost (this is the missing bridge).
  have hEq :
      expectedCost n
          (fun g =>
            (adjustedCost k
              (chunkColoring (n:=n) (k:=k) hk hkn c g i)
              (chunkStartSmall (n:=n) (k:=k) hk hkn g i) : ℚ))
        =
      expectedCost n
          (fun g =>
            avgAdjustedCost k
              (chunkColoring (n:=n) (k:=k) hk hkn c g i)) :=
    expected_adjustedCost_eq_expected_avgAdjustedCost (n:=n) (k:=k) hk hkn c i
  -- Step 2: bound the avgAdjustedCost pointwise by `fhat k`.
  have hpoint :
      ∀ g : AntiGeoData n,
        avgAdjustedCost k (chunkColoring (n:=n) (k:=k) hk hkn c g i) ≤ fhat k := by
    intro g
    exact avgAdjustedCost_le_fhat (k:=k) (chunkColoring (n:=n) (k:=k) hk hkn c g i)
  -- Step 3: take expectations (monotonicity), then evaluate expectation of a constant.
  have hle :
      expectedCost n
          (fun g =>
            avgAdjustedCost k (chunkColoring (n:=n) (k:=k) hk hkn c g i))
        ≤
      expectedCost n (fun _ : AntiGeoData n => fhat k) :=
    expectedCost_mono (n:=n) hpoint
  -- Step 4: rewrite the constant expectation and transport across `hEq`.
  have hconst : expectedCost n (fun _ : AntiGeoData n => fhat k) = fhat k :=
    expectedCost_const (n:=n) (a:=fhat k)
  -- finish
  -- (rewrite LHS using `hEq`, then apply `hle` and `hconst`)
  calc
    expectedCost n
        (fun g =>
          (adjustedCost k
            (chunkColoring (n:=n) (k:=k) hk hkn c g i)
            (chunkStartSmall (n:=n) (k:=k) hk hkn g i) : ℚ))
        =
        expectedCost n
          (fun g =>
            avgAdjustedCost k (chunkColoring (n:=n) (k:=k) hk hkn c g i)) := by
          simp [hEq]
    _ ≤ expectedCost n (fun _ : AntiGeoData n => fhat k) := hle
    _ = fhat k := hconst

section Algo1DecompHelpers

private lemma chunkStartVertex_eq_encode_chunkStartSmall
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (g : AntiGeoData n) (i : Fin (numChunks n k)) :
    chunkStartVertex (n := n) (k := k) hk hkn g i
      =
    (chunkSubcube (n := n) (k := k) hk hkn g i).encode (k := k)
      (chunkStartSmall (n := n) (k := k) hk hkn g i) := by
  ext x
  by_cases hx : x ∈ chunkSupport (n := n) (k := k) hkn g i
  · -- on support coordinates, encode(decode(v)) returns v
    unfold chunkStartSmall Subcube.decode Subcube.encode
    have hxs : x ∈ (chunkSubcube (n := n) (k := k) hk hkn g i).support := by
      simpa [chunkSubcube] using hx
    simp [hxs]
  · -- off support, `encode` uses the subcube base, which is chunkStartVertex
    unfold Subcube.encode chunkSubcube
    simp [hx]

private lemma subcube_encode_flip_supportCoord
    {n k : ℕ} (q : Subcube n k) (x : Vertex k) (j : Fin k) :
    flipCoord ((q.supportEquiv (k := k)).symm j).1 ((q.encode (k := k) x))
      =
    q.encode (k := k) (flipCoord j x) := by
  ext i
  by_cases hi : i ∈ q.support
  · have hEq :
      i = ((q.supportEquiv (k := k)).symm j).1
        ↔ (q.supportEquiv (k := k) ⟨i, hi⟩ = j) := by
      constructor
      · intro h
        subst h
        simp
      · intro h
        have h' :
            (q.supportEquiv (k := k) ⟨i, hi⟩)
              =
            (q.supportEquiv (k := k) ((q.supportEquiv (k := k)).symm j)) := by
          simpa using h
        have hs : (⟨i, hi⟩ : q.support) = (q.supportEquiv (k := k)).symm j :=
          (q.supportEquiv (k := k)).injective h'
        exact congrArg Subtype.val hs
    simp [flipCoord, Subcube.encode, hi, hEq]
  · have hne : i ≠ ((q.supportEquiv (k := k)).symm j).1 := by
      intro hEq
      apply hi
      simp [hEq]
    simp [flipCoord, Subcube.encode, hi, hne]

private lemma vertsNat_eq_vertsNatLen
    {n : ℕ} (start : Vertex n) (coord : Fin n → Fin n) :
    ∀ t : ℕ, vertsNat start coord t = vertsNatLen start coord t
  | 0 => rfl
  | t + 1 => by
      simp [vertsNat, vertsNatLen, vertsNat_eq_vertsNatLen start coord t]

private lemma localPath_edgeColors_eq_ofCoordFnLen
    {k : ℕ} (u : Vertex k) (σ : Equiv.Perm (Fin k)) (c : Coloring k) :
    (localPath (k := k) u σ).edgeColors c
      =
    (GeoPath.ofCoordFnLen (n := k) (ℓ := k) u σ).edgeColors c := by
  unfold localPath AntiGeoData.toGeoPath GeoPath.edgeColors GeoPath.ofCoordFn GeoPath.ofCoordFnLen
  simp [vertsNat_eq_vertsNatLen]

/--
Canonical coercion from `Fin (List.ofFn f).length` back to `Fin k`.
This is the normalization map needed when `ofFn` introduces a length-indexed `Fin`.
-/
private def ofFnIndexCast
    {α : Type*} {k : ℕ} (f : Fin k → α) :
    Fin (List.ofFn f).length → Fin k :=
  Fin.cast (List.length_ofFn (f := f))

private lemma ofFnIndexCast_eq_mk
    {α : Type*} {k : ℕ} (f : Fin k → α) (i : Fin (List.ofFn f).length) :
    ofFnIndexCast f i = ⟨i.1, by simpa [List.length_ofFn (f := f)] using i.2⟩ := by
  apply Fin.ext
  simp [ofFnIndexCast, Fin.val_cast]

omit [DecidableEq (Fin n)] in
private lemma ofFn_getElem_eq_getElem_ofFnIndexCast
    {α : Type*} {k : ℕ} (f : Fin k → α) (i : Fin (List.ofFn f).length) :
    (List.ofFn f)[i] = f (ofFnIndexCast f i) := by
  rw [ofFnIndexCast_eq_mk (f := f) (i := i)]
  simp [List.getElem_ofFn]

private lemma vertsNatLen_ofFnIndexCast_eq
    {n k : ℕ} (start : Vertex n) (f : Fin k → Fin n) :
    ∀ t : ℕ, t ≤ k →
      vertsNatLen start (fun i : Fin (List.ofFn f).length => f (ofFnIndexCast f i)) t
        =
      vertsNatLen start f t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
      have htk : t < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht
      have hlen : (List.ofFn f).length = k := List.length_ofFn (f := f)
      have htl : t < (List.ofFn f).length := by simpa [hlen] using htk
      have hcast :
          ofFnIndexCast f ⟨t, htl⟩ = ⟨t, htk⟩ := by
        apply Fin.ext
        simp [ofFnIndexCast]
      simp [vertsNatLen, htk, ih (Nat.le_of_lt htk), hcast]

private lemma chunk_vertsNatLen_eq_encode_local
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (g : AntiGeoData n) (i : Fin (numChunks n k))
    (σ : Equiv.Perm (Fin k)) :
      let q := chunkSubcube (n := n) (k := k) hk hkn g i
      let f : Fin k → Fin n := fun t => ((q.supportEquiv (k := k)).symm (σ t)).1
      ∀ t : ℕ, t ≤ k →
      vertsNatLen (chunkStartVertex (n := n) (k := k) hk hkn g i) f t
        =
      q.encode (k := k)
        (vertsNatLen (chunkStartSmall (n := n) (k := k) hk hkn g i) σ t) := by
  classical
  intro q f t ht
  induction t with
  | zero =>
      simpa [q, f] using
        (chunkStartVertex_eq_encode_chunkStartSmall (n := n) (k := k) hk hkn g i)
  | succ t ih =>
      have htk : t < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht
      have htle : t ≤ k := Nat.le_of_lt htk
      specialize ih htle
      have hL :
          vertsNatLen (chunkStartVertex (n := n) (k := k) hk hkn g i) f (t + 1)
            =
          flipCoord (f ⟨t, htk⟩)
            (vertsNatLen (chunkStartVertex (n := n) (k := k) hk hkn g i) f t) := by
        simp [vertsNatLen, htk]
      have hR :
          vertsNatLen (chunkStartSmall (n := n) (k := k) hk hkn g i) σ (t + 1)
            =
          flipCoord (σ ⟨t, htk⟩)
            (vertsNatLen (chunkStartSmall (n := n) (k := k) hk hkn g i) σ t) := by
        simp [vertsNatLen, htk]
      rw [hL, hR, ih]
      have hflip :=
        subcube_encode_flip_supportCoord (q := q)
          (x := vertsNatLen (chunkStartSmall (n := n) (k := k) hk hkn g i) σ t)
          (j := σ ⟨t, htk⟩)
      simpa [f] using hflip

private lemma edgeOf_encode_eq_map_edgeOf
    {n k : ℕ} (q : Subcube n k) (u v : Vertex k) :
    edgeOf (q.encode (k := k) u) (q.encode (k := k) v)
      =
    Sym2.map (q.encode (k := k)) (edgeOf u v) := by
  rfl

private lemma edgeColorsFromOrder_chunkOrder_eq_localPath_edgeColors
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (c : Coloring n) (g : AntiGeoData n) (i : Fin (numChunks n k))
    (σ : Equiv.Perm (Fin k)) :
    let q := chunkSubcube (n := n) (k := k) hk hkn g i
    let order : List (Fin n) := List.ofFn (fun t : Fin k => ((q.supportEquiv (k := k)).symm (σ t)).1)
    edgeColorsFromOrder (n := n) c (chunkStartVertex (n := n) (k := k) hk hkn g i) order
      =
    (GeoPath.ofCoordFnLen (n := k) (ℓ := k)
        (chunkStartSmall (n := n) (k := k) hk hkn g i) σ).edgeColors
      (chunkColoring (n := n) (k := k) hk hkn c g i) := by
  classical
  intro q order
  let f : Fin k → Fin n := fun t => ((q.supportEquiv (k := k)).symm (σ t)).1
  have horder : order = List.ofFn f := by
    ext t
    simp [order, f]
  rw [horder]
  unfold edgeColorsFromOrder GeoPath.edgeColors chunkColoring Subcube.inducedColoring
  have hcoord :
      (fun t : Fin (List.ofFn f).length => (List.ofFn f)[t])
        =
      (fun t : Fin (List.ofFn f).length => f (ofFnIndexCast f t)) := by
    funext t
    rw [ofFnIndexCast_eq_mk (f := f) (i := t)]
    simp [List.getElem_ofFn]
  rw [hcoord]
  apply List.ext_getElem <;> simp only [List.length_ofFn]
  intro j hjL hjR
  have hjk : j < k := by simpa using hjL
  have h0' :
      vertsNatLen
          (chunkStartVertex (n := n) (k := k) hk hkn g i)
          (fun t : Fin (List.ofFn f).length => f (ofFnIndexCast f t)) j
        =
      vertsNatLen (chunkStartVertex (n := n) (k := k) hk hkn g i) f j :=
    vertsNatLen_ofFnIndexCast_eq
      (start := chunkStartVertex (n := n) (k := k) hk hkn g i)
      (f := f) j (Nat.le_of_lt hjk)
  have h1' :
      vertsNatLen
          (chunkStartVertex (n := n) (k := k) hk hkn g i)
          (fun t : Fin (List.ofFn f).length => f (ofFnIndexCast f t)) (j + 1)
        =
      vertsNatLen (chunkStartVertex (n := n) (k := k) hk hkn g i) f (j + 1) :=
    vertsNatLen_ofFnIndexCast_eq
      (start := chunkStartVertex (n := n) (k := k) hk hkn g i)
      (f := f) (j + 1) (Nat.succ_le_of_lt hjk)
  have h0 :
      vertsNatLen (chunkStartVertex (n := n) (k := k) hk hkn g i) f j
        =
      q.encode (k := k)
        (vertsNatLen (chunkStartSmall (n := n) (k := k) hk hkn g i) σ j) :=
    chunk_vertsNatLen_eq_encode_local (n := n) (k := k) hk hkn g i σ j (Nat.le_of_lt hjk)
  have h1 :
      vertsNatLen (chunkStartVertex (n := n) (k := k) hk hkn g i) f (j + 1)
        =
      q.encode (k := k)
        (vertsNatLen (chunkStartSmall (n := n) (k := k) hk hkn g i) σ (j + 1)) :=
    chunk_vertsNatLen_eq_encode_local (n := n) (k := k) hk hkn g i σ (j + 1) (Nat.succ_le_of_lt hjk)
  simp only [GeoPath.ofCoordFnLen, Fin.val_castSucc, Fin.val_cast, Fin.val_succ, List.getElem_ofFn]
  rw [h0', h1', h0, h1]
  exact congrArg c
    (edgeOf_encode_eq_map_edgeOf (q := q)
      (u := vertsNatLen (chunkStartSmall (n := n) (k := k) hk hkn g i) σ j)
      (v := vertsNatLen (chunkStartSmall (n := n) (k := k) hk hkn g i) σ (j + 1)))

private lemma changesFromOrder_chunkOrder_eq_localCost
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (c : Coloring n) (g : AntiGeoData n) (i : Fin (numChunks n k))
    (σ : Equiv.Perm (Fin k)) :
    let q := chunkSubcube (n := n) (k := k) hk hkn g i
    let order : List (Fin n) := List.ofFn (fun t : Fin k => ((q.supportEquiv (k := k)).symm (σ t)).1)
    changesFromOrder (n := n) c (chunkStartVertex (n := n) (k := k) hk hkn g i) order
      =
    localCost (k := k)
      (chunkColoring (n := n) (k := k) hk hkn c g i)
      (chunkStartSmall (n := n) (k := k) hk hkn g i) σ := by
  classical
  intro q order
  unfold changesFromOrder localCost GeoPath.colorChanges
  rw [edgeColorsFromOrder_chunkOrder_eq_localPath_edgeColors
        (n := n) (k := k) hk hkn c g i σ]
  simpa using congrArg changesOnColors
    (localPath_edgeColors_eq_ofCoordFnLen
      (k := k)
      (u := chunkStartSmall (n := n) (k := k) hk hkn g i)
      (σ := σ)
      (c := chunkColoring (n := n) (k := k) hk hkn c g i)).symm

private lemma firstColorFromOrder_chunkOrder_eq_localPath_head
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (c : Coloring n) (g : AntiGeoData n) (i : Fin (numChunks n k))
    (σ : Equiv.Perm (Fin k)) :
    let q := chunkSubcube (n := n) (k := k) hk hkn g i
    let order : List (Fin n) := List.ofFn (fun t : Fin k => ((q.supportEquiv (k := k)).symm (σ t)).1)
    firstColorFromOrder? (n := n) c (chunkStartVertex (n := n) (k := k) hk hkn g i) order
      =
    List.head?
      ((localPath (k := k)
          (chunkStartSmall (n := n) (k := k) hk hkn g i) σ).edgeColors
        (chunkColoring (n := n) (k := k) hk hkn c g i)) := by
  classical
  intro q order
  unfold firstColorFromOrder?
  rw [edgeColorsFromOrder_chunkOrder_eq_localPath_edgeColors
        (n := n) (k := k) hk hkn c g i σ]
  simpa using congrArg List.head?
    (localPath_edgeColors_eq_ofCoordFnLen
      (k := k)
      (u := chunkStartSmall (n := n) (k := k) hk hkn g i)
      (σ := σ)
      (c := chunkColoring (n := n) (k := k) hk hkn c g i)).symm

private lemma lastColorFromOrder_chunkOrder_eq_localPath_last
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (c : Coloring n) (g : AntiGeoData n) (i : Fin (numChunks n k))
    (σ : Equiv.Perm (Fin k)) :
    let q := chunkSubcube (n := n) (k := k) hk hkn g i
    let order : List (Fin n) := List.ofFn (fun t : Fin k => ((q.supportEquiv (k := k)).symm (σ t)).1)
    lastColorFromOrder? (n := n) c (chunkStartVertex (n := n) (k := k) hk hkn g i) order
      =
    List.head?
      (List.reverse
        ((localPath (k := k)
          (chunkStartSmall (n := n) (k := k) hk hkn g i) σ).edgeColors
          (chunkColoring (n := n) (k := k) hk hkn c g i))) := by
  classical
  intro q order
  unfold lastColorFromOrder?
  rw [edgeColorsFromOrder_chunkOrder_eq_localPath_edgeColors
        (n := n) (k := k) hk hkn c g i σ]
  simpa using congrArg (fun l => List.head? (List.reverse l))
    (localPath_edgeColors_eq_ofCoordFnLen
      (k := k)
      (u := chunkStartSmall (n := n) (k := k) hk hkn g i)
      (σ := σ)
      (c := chunkColoring (n := n) (k := k) hk hkn c g i)).symm

-- NOTE: edge-color transport for chunk orders is developed later as needed.

private lemma chunkIndex_lt_n
    {n k : ℕ} (i : Fin (numChunks n k)) (j : Fin k) :
    k * i.1 + j.1 < n := by
  have hi : i.1 < n / k := i.2
  have hj : j.1 < k := j.2
  have hi1 : i.1 + 1 ≤ n / k := Nat.succ_le_of_lt hi
  have hmul : k * (i.1 + 1) ≤ n := by
    calc
      k * (i.1 + 1) ≤ k * (n / k) := Nat.mul_le_mul_left _ hi1
      _ = (n / k) * k := by simp [Nat.mul_comm]
      _ ≤ n := Nat.div_mul_le_self _ _
  have hkik : k * i.1 + k = k * (i.1 + 1) := by
    simp [Nat.mul_add,  Nat.add_comm]
  calc
    k * i.1 + j.1 < k * i.1 + k := Nat.add_lt_add_left hj _
    _ = k * (i.1 + 1) := hkik
    _ ≤ n := hmul

/-- Coordinate enumeration for the `i`-th chunk in the original permutation order. -/
noncomputable def chunkEnum
    {n k : ℕ} (g : AntiGeoData n) (i : Fin (numChunks n k)) : Fin k → Fin n :=
  fun j => g.perm ⟨k * i.1 + j.1, chunkIndex_lt_n (n := n) (k := k) i j⟩

private lemma chunkEnum_mem_support
    {n k : ℕ} (hkn : k ≤ n) (g : AntiGeoData n) (i : Fin (numChunks n k)) (j : Fin k) :
    chunkEnum g i j ∈ chunkSupport (n := n) (k := k) hkn g i := by
  unfold chunkEnum chunkSupport
  rw [Finset.mem_image]
  refine ⟨j, by simp, ?_⟩
  rfl

private lemma chunkEnum_injective
    {n k : ℕ} (g : AntiGeoData n) (i : Fin (numChunks n k)) :
    Function.Injective (chunkEnum g i) := by
  intro j1 j2 h
  apply Fin.ext
  have hperm :
      (⟨k * i.1 + j1.1, chunkIndex_lt_n (n := n) (k := k) i j1⟩ : Fin n)
        =
      (⟨k * i.1 + j2.1, chunkIndex_lt_n (n := n) (k := k) i j2⟩ : Fin n) := by
    exact g.perm.injective h
  have hval : k * i.1 + j1.1 = k * i.1 + j2.1 := congrArg Fin.val hperm
  exact Nat.add_left_cancel hval

/--
Permutation of `Fin k` induced by reindexing chunk coordinates through the chunk subcube support.
-/
noncomputable def chunkBijection
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (g : AntiGeoData n) (i : Fin (numChunks n k)) : Equiv.Perm (Fin k) := by
  let q := chunkSubcube (n := n) (k := k) hk hkn g i
  let f : Fin k → Fin k := fun j =>
    q.supportEquiv ⟨chunkEnum g i j, chunkEnum_mem_support (n := n) (k := k) hkn g i j⟩
  have hf_inj : Function.Injective f := by
    intro j1 j2 h
    have hs :
        (⟨chunkEnum g i j1, chunkEnum_mem_support (n := n) (k := k) hkn g i j1⟩ : q.support)
          =
        ⟨chunkEnum g i j2, chunkEnum_mem_support (n := n) (k := k) hkn g i j2⟩ :=
      q.supportEquiv.injective h
    exact chunkEnum_injective (g := g) (i := i) (congrArg Subtype.val hs)
  exact Equiv.ofBijective f ⟨hf_inj, Finite.injective_iff_surjective.mp hf_inj⟩

private lemma chunkEnum_eq_supportEquiv_symm_chunkBijection
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (g : AntiGeoData n) (i : Fin (numChunks n k)) (j : Fin k) :
    chunkEnum g i j =
      ((chunkSubcube (n := n) (k := k) hk hkn g i).supportEquiv.symm
        (chunkBijection (n := n) (k := k) hk hkn g i j)).1 := by
  unfold chunkBijection
  simp

private lemma chunkSeg_getD_eq_chunkEnum
    {n k : ℕ} (hk : 2 ≤ k)
    (g : AntiGeoData n) (i : Fin (numChunks n k)) (j : Fin k)
    (defaultCoord : Fin n) :
    (((List.ofFn g.perm).drop (k * i.1)).take k).getD j.1 defaultCoord = chunkEnum g i j := by
  let seg : List (Fin n) := ((List.ofFn g.perm).drop (k * i.1)).take k
  have hdrop_len : k ≤ ((List.ofFn g.perm).drop (k * i.1)).length := by
    simp only [List.length_drop, List.length_ofFn]
    have hki : k * i.1 + k ≤ n := by
      have hi : i.1 < n / k := i.2
      have hi1 : i.1 + 1 ≤ n / k := Nat.succ_le_of_lt hi
      calc
        k * i.1 + k = k * (i.1 + 1) := by
          simp [Nat.mul_add,  Nat.add_comm]
        _ ≤ k * (n / k) := Nat.mul_le_mul_left _ hi1
        _ = (n / k) * k := by simp [Nat.mul_comm]
        _ ≤ n := Nat.div_mul_le_self _ _
    omega
  have hk_minus : k ≤ n - k * i.1 := by
    simpa [List.length_drop, List.length_ofFn] using hdrop_len
  have hseg_len : seg.length = k := by
    simp [seg, List.length_take, hk_minus]
  have hj_seg : j.1 < seg.length := by
    simp [hseg_len] -- using j.2
  rw [List.getD_eq_getElem (l := seg) (d := defaultCoord) hj_seg]
  have hj_drop : j.1 < ((List.ofFn g.perm).drop (k * i.1)).length := by
    exact lt_of_lt_of_le j.2 hdrop_len
  have htake :
      (((List.ofFn g.perm).drop (k * i.1)).take k)[j.1] =
      ((List.ofFn g.perm).drop (k * i.1))[j.1] := by
    simp only [List.getElem_take]
  rw [show seg[j.1] = (((List.ofFn g.perm).drop (k * i.1)).take k)[j.1] by rfl, htake]
  have hidx : k * i.1 + j.1 < n := chunkIndex_lt_n (n := n) (k := k) i j
  simp [List.getElem_drop, List.getElem_ofFn, chunkEnum]

end Algo1DecompHelpers

section Algo1DecompFinalHelpers

private def applyOrder {n : ℕ} (start : Vertex n) (coords : List (Fin n)) : Vertex n :=
  coords.foldl (fun v i => flipCoord i v) start

private lemma flipCoord_right_comm {n : ℕ} :
    RightCommutative (fun v : Vertex n => fun i : Fin n => flipCoord i v) := by
  refine ⟨?_⟩
  intro v i j
  funext x
  by_cases hxi : x = i <;> by_cases hxj : x = j
  · subst x
    by_cases hij : i = j <;> simp [flipCoord, hij]
  · subst x
    have hij : i ≠ j := hxj
    simp [flipCoord, hij]
  · subst x
    have hji : j ≠ i := hxi
    simp [flipCoord, hji]
  · simp [flipCoord, hxi, hxj]

private lemma vertsNatLen_eq_applyOrder_take
    {n ℓ : ℕ} (start : Vertex n) (coord : Fin ℓ → Fin n) :
    ∀ t : ℕ, t ≤ ℓ →
      vertsNatLen start coord t = applyOrder start ((List.ofFn coord).take t)
  | 0, _ => by simp [vertsNatLen, applyOrder]
  | t + 1, ht => by
      have htl : t < ℓ := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht
      have ih := vertsNatLen_eq_applyOrder_take start coord t (Nat.le_of_lt htl)
      have htake :
          (List.ofFn coord).take (t + 1)
            = (List.ofFn coord).take t ++ [coord ⟨t, htl⟩] := by
        have hlen_take : ((List.ofFn coord).take t).length = t := by
          simp [List.length_ofFn, Nat.min_eq_left (Nat.le_of_lt htl)]
        calc
          (List.ofFn coord).take (t + 1)
              = ((List.ofFn coord).take t ++ (List.ofFn coord).drop t).take (t + 1) := by
                  simp [List.take_append_drop]
          _ = (List.ofFn coord).take t ++ (((List.ofFn coord).drop t).take 1) := by
                rw [List.take_append]
                simp [hlen_take]
          _ = (List.ofFn coord).take t ++ [coord ⟨t, htl⟩] := by
                have hlt_len : t < (List.ofFn coord).length := by
                  simpa [List.length_ofFn] using htl
                have hone :
                    ((List.ofFn coord).drop t).take 1
                      = [((List.ofFn coord).get ⟨t, hlt_len⟩)] := by
                  simpa using (List.take_one_drop_eq_of_lt_length (l := List.ofFn coord) (n := t) hlt_len)
                simpa [List.get_ofFn] using congrArg (fun l => (List.ofFn coord).take t ++ l) hone
      have hstep :
          vertsNatLen start coord (t + 1)
            = flipCoord (coord ⟨t, htl⟩) (vertsNatLen start coord t) := by
        simp [vertsNatLen, htl]
      rw [hstep, ih, htake]
      unfold applyOrder
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma vertsNatLen_eq_applyOrder
    {n ℓ : ℕ} (start : Vertex n) (coord : Fin ℓ → Fin n) :
    vertsNatLen start coord ℓ = applyOrder start (List.ofFn coord) := by
  have htake : (List.ofFn coord).take ℓ = List.ofFn coord := by
    simp [List.length_ofFn]
  simpa [htake] using
    (vertsNatLen_eq_applyOrder_take (n := n) (ℓ := ℓ) start coord ℓ (Nat.le_refl ℓ))

private lemma chunkOrderFromChoice_perm_chunkEnum
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (g : AntiGeoData n) (i : Fin (numChunks n k)) (choice : ChunkChoice (k := k)) :
    List.Perm
      (chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice)
      (List.ofFn (chunkEnum (n := n) (k := k) g i)) := by
  classical
  unfold chunkOrderFromChoice
  let q := chunkSubcube (n := n) (k := k) hk hkn g i
  let f : Fin k → Fin n := fun t => (q.supportEquiv.symm t).1
  have hchoice : List.Perm (List.ofFn (fun t : Fin k => f (choice.σ t))) (List.ofFn f) :=
    Equiv.Perm.ofFn_comp_perm choice.σ f
  have hchunk :
      List.Perm
        (List.ofFn (fun t : Fin k =>
          f (chunkBijection (n := n) (k := k) hk hkn g i t)))
        (List.ofFn f) :=
    Equiv.Perm.ofFn_comp_perm (chunkBijection (n := n) (k := k) hk hkn g i) f
  have henum :
      List.ofFn (chunkEnum (n := n) (k := k) g i)
        = List.ofFn (fun t : Fin k => f (chunkBijection (n := n) (k := k) hk hkn g i t)) := by
    apply List.ext_get
    · simp
    · intro j hj1 hj2
      have hjk : j < k := by simpa using hj1
      let jf : Fin k := ⟨j, hjk⟩
      have hq :
          chunkEnum (n := n) (k := k) g i jf
            = ((chunkSubcube (n := n) (k := k) hk hkn g i).supportEquiv.symm
                (chunkBijection (n := n) (k := k) hk hkn g i jf)).1 :=
        chunkEnum_eq_supportEquiv_symm_chunkBijection (n := n) (k := k) hk hkn g i jf
      have hleft :
          (List.ofFn (chunkEnum (n := n) (k := k) g i)).get ⟨j, hj1⟩
            = chunkEnum (n := n) (k := k) g i jf := by
        simp [jf]
      have hright :
          (List.ofFn (fun t : Fin k => f (chunkBijection (n := n) (k := k) hk hkn g i t))).get ⟨j, hj2⟩
            = f (chunkBijection (n := n) (k := k) hk hkn g i jf) := by
        simp [f, jf]
      simpa [hleft, hright, f] using hq
  exact hchoice.trans (hchunk.symm.trans (henum ▸ List.Perm.refl _))

private lemma vertsNat_chunk_shift
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (g : AntiGeoData n) (i : Fin (numChunks n k)) :
    ∀ t : ℕ, t ≤ k →
      vertsNat g.start g.perm (k * i.1 + t)
        = vertsNatLen (chunkStartVertex (n := n) (k := k) hk hkn g i)
            (chunkEnum (n := n) (k := k) g i) t
  | 0, _ => by
      simp [chunkStartVertex, AntiGeoData.toGeoPath, GeoPath.ofCoordFn, vertsNatLen]
  | t + 1, ht => by
      have htk : t < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht
      have ih := vertsNat_chunk_shift hk hkn g i t (Nat.le_of_lt htk)
      have hidx : k * i.1 + t < n := by
        exact chunkIndex_lt_n (n := n) (k := k) i ⟨t, htk⟩
      have hleft :
          vertsNat g.start g.perm (k * i.1 + (t + 1))
            = flipCoord
                (g.perm ⟨k * i.1 + t, hidx⟩)
                (vertsNat g.start g.perm (k * i.1 + t)) := by
        have hEq : k * i.1 + (t + 1) = (k * i.1 + t) + 1 := by omega
        rw [hEq]
        simp [vertsNat, hidx]
      have hright :
          vertsNatLen (chunkStartVertex (n := n) (k := k) hk hkn g i)
              (chunkEnum (n := n) (k := k) g i) (t + 1)
            = flipCoord
                (chunkEnum (n := n) (k := k) g i ⟨t, htk⟩)
                (vertsNatLen (chunkStartVertex (n := n) (k := k) hk hkn g i)
                  (chunkEnum (n := n) (k := k) g i) t) := by
        simp [vertsNatLen, htk]
      rw [hleft, hright, ih]
      rfl

private lemma applyOrder_chunkEnum_eq_vertsNat_next
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (g : AntiGeoData n) (i : Fin (numChunks n k)) :
    applyOrder
        (chunkStartVertex (n := n) (k := k) hk hkn g i)
        (List.ofFn (chunkEnum (n := n) (k := k) g i))
      =
    vertsNat g.start g.perm (k * (i.1 + 1)) := by
  have hshift := vertsNat_chunk_shift (n := n) (k := k) hk hkn g i k (Nat.le_refl k)
  have hend :
      vertsNatLen
          (chunkStartVertex (n := n) (k := k) hk hkn g i)
          (chunkEnum (n := n) (k := k) g i) k
        =
      applyOrder
          (chunkStartVertex (n := n) (k := k) hk hkn g i)
          (List.ofFn (chunkEnum (n := n) (k := k) g i)) :=
    vertsNatLen_eq_applyOrder
      (start := chunkStartVertex (n := n) (k := k) hk hkn g i)
      (coord := chunkEnum (n := n) (k := k) g i)
  rw [← hend, ← hshift]
  ring_nf

private lemma applyOrder_chunkOrderFromChoice_eq_vertsNat_next
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (g : AntiGeoData n) (i : Fin (numChunks n k)) (choice : ChunkChoice (k := k)) :
    applyOrder
        (chunkStartVertex (n := n) (k := k) hk hkn g i)
        (chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice)
      =
    vertsNat g.start g.perm (k * (i.1 + 1)) := by
  have hperm :=
    chunkOrderFromChoice_perm_chunkEnum (n := n) (k := k) hk hkn g i choice
  letI : RightCommutative (fun v : Vertex n => fun i : Fin n => flipCoord i v) :=
    flipCoord_right_comm
  have happly :
      applyOrder
          (chunkStartVertex (n := n) (k := k) hk hkn g i)
          (chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice)
        =
      applyOrder
          (chunkStartVertex (n := n) (k := k) hk hkn g i)
          (List.ofFn (chunkEnum (n := n) (k := k) g i)) := by
    unfold applyOrder
    exact hperm.foldl_eq _
  rw [happly, applyOrder_chunkEnum_eq_vertsNat_next (n := n) (k := k) hk hkn g i]

end Algo1DecompFinalHelpers

section Algo1DecompInvariant

noncomputable def algorithm1ChunkAccRec
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (c : Coloring n) (g : AntiGeoData n) :
    Nat → (List (Fin n) × Option Bool)
  | 0 => ([], none)
  | t + 1 =>
      let acc := algorithm1ChunkAccRec hk hkn c g t
      let prev := acc.2
      if ht : t < numChunks n k then
        let ii : Fin (numChunks n k) := ⟨t, ht⟩
        let choice := chooseChunk (n := n) (k := k) hk hkn c g ii prev
        let chunkOrder := chunkOrderFromChoice (n := n) (k := k) hk hkn g ii choice
        (acc.1 ++ chunkOrder, some choice.last)
      else
        acc

private lemma algorithm1ChunkAccRec_eq_foldl_range
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (c : Coloring n) (g : AntiGeoData n) :
    ∀ t : Nat,
      algorithm1ChunkAccRec hk hkn c g t
        = (List.range t).foldl (algorithm1Step (n := n) (k := k) hk hkn c g) ([], none)
  | 0 => by
      simp [algorithm1ChunkAccRec]
  | t + 1 => by
      simp [algorithm1ChunkAccRec, algorithm1ChunkAccRec_eq_foldl_range (t := t),
        List.range_succ, List.foldl_append, algorithm1Step]

private lemma algorithm1ChunkAcc_eq_rec
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (c : Coloring n) (g : AntiGeoData n) :
    algorithm1ChunkAcc (n := n) (k := k) hk hkn c g
      = algorithm1ChunkAccRec hk hkn c g (numChunks n k) := by
  symm
  simpa [algorithm1ChunkAcc] using
    (algorithm1ChunkAccRec_eq_foldl_range (n := n) (k := k) hk hkn c g (numChunks n k))

private lemma applyOrder_chunkAccRec_eq_chunkBoundary
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (c : Coloring n) (g : AntiGeoData n) :
    ∀ t : Nat, t ≤ numChunks n k →
      applyOrder g.start (algorithm1ChunkAccRec hk hkn c g t).1
        = vertsNat g.start g.perm (k * t)
  | 0, _ => by
      simp [algorithm1ChunkAccRec, applyOrder, vertsNat]
  | t + 1, ht1 => by
      have ht : t < numChunks n k := Nat.lt_of_succ_le ht1
      have ih :=
        applyOrder_chunkAccRec_eq_chunkBoundary
          (hk := hk) (hkn := hkn) (c := c) (g := g) t (Nat.le_of_lt ht)
      simp only [algorithm1ChunkAccRec, ht, ↓reduceDIte]
      let ii : Fin (numChunks n k) := ⟨t, ht⟩
      let acc := algorithm1ChunkAccRec hk hkn c g t
      let prev := acc.2
      let choice := chooseChunk (n := n) (k := k) hk hkn c g ii prev
      let chunkOrder := chunkOrderFromChoice (n := n) (k := k) hk hkn g ii choice
      have hstart :
          applyOrder g.start acc.1 = chunkStartVertex (n := n) (k := k) hk hkn g ii := by
        change applyOrder g.start (algorithm1ChunkAccRec hk hkn c g t).1
            = chunkStartVertex (n := n) (k := k) hk hkn g ii
        rw [ih]
        simp [ii, chunkStartVertex, AntiGeoData.toGeoPath, GeoPath.ofCoordFn]
      simp only [Order.add_one_le_iff, applyOrder, List.foldl_append, acc, ii] at *
      have hstart' :
          List.foldl (fun v i => flipCoord i v) g.start (algorithm1ChunkAccRec hk hkn c g t).1
            = chunkStartVertex (n := n) (k := k) hk hkn g ii := by
        simpa [applyOrder, acc] using hstart
      rw [hstart']
      have hnext :
          List.foldl (fun v i => flipCoord i v) (chunkStartVertex (n := n) (k := k) hk hkn g ii)
            (chunkOrderFromChoice (n := n) (k := k) hk hkn g ii choice)
            = vertsNat g.start g.perm (k * (ii.1 + 1)) := by
        simpa [applyOrder] using
          (applyOrder_chunkOrderFromChoice_eq_vertsNat_next
            (n := n) (k := k) hk hkn g ii choice)
      rw [hnext]

private lemma applyOrder_algorithm1ChunkCoords_eq_chunkBoundaryEnd
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (c : Coloring n) (g : AntiGeoData n) :
    applyOrder g.start (algorithm1ChunkCoords (n := n) (k := k) hk hkn c g)
      = vertsNat g.start g.perm (k * numChunks n k) := by
  unfold algorithm1ChunkCoords
  rw [algorithm1ChunkAcc_eq_rec (n := n) (k := k) hk hkn c g]
  exact applyOrder_chunkAccRec_eq_chunkBoundary (n := n) (k := k) hk hkn c g
    (numChunks n k) (Nat.le_refl _)

end Algo1DecompInvariant

section Algo1AppendHelpers

omit [DecidableEq (Fin n)] in
private lemma applyOrder_eq_vertsNatLen_ofList
    (start : Vertex n) (coords : List (Fin n)) :
    applyOrder start coords
      = vertsNatLen start (fun i : Fin coords.length => coords[i]) coords.length := by
  symm
  simpa using
    (vertsNatLen_eq_applyOrder
      (n := n) (ℓ := coords.length) start (fun i : Fin coords.length => coords[i]))

omit [DecidableEq (Fin n)] in
private lemma vertsNatLen_append_left
    (start : Vertex n) (l1 l2 : List (Fin n)) :
    ∀ t : ℕ, t ≤ l1.length →
      vertsNatLen start (fun i : Fin (l1.length + l2.length) => (l1 ++ l2)[i]) t
        =
      vertsNatLen start (fun i : Fin l1.length => l1[i]) t
  | 0, _ => by simp [vertsNatLen]
  | t + 1, ht1 => by
      have ht : t < l1.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht1
      have ih := vertsNatLen_append_left start l1 l2 t (Nat.le_of_lt ht)
      have htl : t < l1.length + l2.length := lt_of_lt_of_le ht (Nat.le_add_right _ _)
      have hget :
          ((l1 ++ l2)[t]'(by simpa [List.length_append] using htl))
            = l1[t]'ht := by
        simpa using (List.getElem_append_left (as := l1) (bs := l2) (i := t) ht)
      simp only [vertsNatLen, htl, ↓reduceDIte, Fin.getElem_fin, ht, List.getElem_append_left]
      exact congrArg (flipCoord (l1[t]'ht)) ih

omit [DecidableEq (Fin n)] in
private lemma vertsNatLen_append_right
    (start : Vertex n) (l1 l2 : List (Fin n)) :
    ∀ t : ℕ, t ≤ l2.length →
      vertsNatLen start (fun i : Fin (l1.length + l2.length) => (l1 ++ l2)[i]) (l1.length + t)
        =
      vertsNatLen (applyOrder start l1) (fun i : Fin l2.length => l2[i]) t
  | 0, _ => by
      have hleft :=
        vertsNatLen_append_left (k := k) start l1 l2 l1.length (Nat.le_refl _)
      have happly : applyOrder start l1
          = vertsNatLen start (fun i : Fin l1.length => l1[i]) l1.length :=
        applyOrder_eq_vertsNatLen_ofList (k := k) start l1
      simpa [Nat.add_zero] using hleft.trans happly.symm
  | t + 1, ht1 => by
      have ht : t < l2.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht1
      have ih := vertsNatLen_append_right start l1 l2 t (Nat.le_of_lt ht)
      have hidx : l1.length + t < l1.length + l2.length := Nat.add_lt_add_left ht _
      have hget :
          ((l1 ++ l2)[l1.length + t]'(by simpa [List.length_append] using hidx))
            = l2[t]'ht := by
        have hle : l1.length ≤ l1.length + t := Nat.le_add_right _ _
        simp -- only [le_add_iff_nonneg_right, zero_le, List.getElem_append_right,
          --add_tsub_cancel_left]
          -- (List.getElem_append_right (as := l1) (bs := l2) (i := l1.length + t) hle)
      have hidx' : l1.length + t < l1.length + l2.length := hidx
      have hadd : l1.length + (t + 1) = (l1.length + t) + 1 := by omega
      rw [hadd]
      simp only [vertsNatLen, hidx', ↓reduceDIte, Fin.getElem_fin, hget, ht]
      exact congrArg (flipCoord (l2[t]'ht)) ih

omit [DecidableEq (Fin n)] in
private lemma vertsNatLen_append_len_bridge
    (start : Vertex n) (l1 l2 : List (Fin n)) :
    ∀ t : ℕ,
      vertsNatLen start (fun i : Fin (l1.length + l2.length) => (l1 ++ l2)[i]) t
        =
      vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i]) t
  | 0 => rfl
  | t + 1 => by
      by_cases ht : t < l1.length + l2.length
      · have ht' : t < (l1 ++ l2).length := by
          simpa [List.length_append] using ht
        have ih := vertsNatLen_append_len_bridge start l1 l2 t
        simp [vertsNatLen, ht]
        simpa using congrArg (flipCoord ((l1 ++ l2)[t]'ht')) ih
      · have ht' : ¬ t < (l1 ++ l2).length := by
          simpa [List.length_append] using ht
        simp only [vertsNatLen, ht, ht']
        exact vertsNatLen_append_len_bridge start l1 l2 t

omit [DecidableEq (Fin n)] in
private lemma edgeColorsFromOrder_append
    (c : Coloring n) (start : Vertex n) (l1 l2 : List (Fin n)) :
    edgeColorsFromOrder (n := n) c start (l1 ++ l2)
      =
    edgeColorsFromOrder (n := n) c start l1 ++
      edgeColorsFromOrder (n := n) c (applyOrder start l1) l2 := by
  unfold edgeColorsFromOrder GeoPath.edgeColors
  simpa [List.length_append] using
    (by
      let A : List Bool :=
        List.ofFn
          (fun i : Fin l1.length =>
            c (edgeOf ((GeoPath.ofCoordFnLen start fun i => l1[i]).verts i.castSucc)
                ((GeoPath.ofCoordFnLen start fun i => l1[i]).verts i.succ)))
      let B : List Bool :=
        List.ofFn
          (fun i : Fin l2.length =>
            c (edgeOf ((GeoPath.ofCoordFnLen (applyOrder start l1) fun i => l2[i]).verts i.castSucc)
                ((GeoPath.ofCoordFnLen (applyOrder start l1) fun i => l2[i]).verts i.succ)))
      let castIdx : Fin (l1.length + l2.length) → Fin (l1 ++ l2).length :=
        Fin.cast (by simp [List.length_append])
      let C : List Bool :=
        List.ofFn
          (fun i : Fin (l1.length + l2.length) =>
            c (edgeOf ((GeoPath.ofCoordFnLen start fun i => (l1 ++ l2)[i]).verts (castIdx i).castSucc)
                ((GeoPath.ofCoordFnLen start fun i => (l1 ++ l2)[i]).verts (castIdx i).succ)))
      change C = A ++ B
      apply List.ext_getElem
      · simp [A, B, C, List.length_append, List.length_ofFn]
      · intro j hjL hjR
        by_cases hj : j < l1.length
        · have hjA : j < A.length := by
            simpa [A, List.length_ofFn] using hj
          have h0 :=
            vertsNatLen_append_left (k := 0) start l1 l2 j (Nat.le_of_lt hj)
          have h1 :=
            vertsNatLen_append_left (k := 0) start l1 l2 (j + 1) (Nat.succ_le_of_lt hj)
          rw [List.getElem_append_left (as := A) (bs := B) (i := j) hjA]
          have h0' :
              vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i]) j
                =
              vertsNatLen start (fun i : Fin l1.length => l1[i]) j := by
            exact (vertsNatLen_append_len_bridge (k := 0) start l1 l2 j).symm.trans h0
          have h1' :
              vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i]) (j + 1)
                =
              vertsNatLen start (fun i : Fin l1.length => l1[i]) (j + 1) := by
            exact (vertsNatLen_append_len_bridge (k := 0) start l1 l2 (j + 1)).symm.trans h1
          have hCA :
              c
                  (edgeOf
                    (vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i]) j)
                    (vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i]) (j + 1)))
                =
              c
                  (edgeOf
                    (vertsNatLen start (fun i : Fin l1.length => l1[i]) j)
                    (vertsNatLen start (fun i : Fin l1.length => l1[i]) (j + 1))) := by
            rw [h0', h1']
          simpa [A, C, castIdx, List.getElem_ofFn, GeoPath.ofCoordFnLen, Fin.cast_mk, List.length_append]
            using hCA
        · have hjge : l1.length ≤ j := Nat.le_of_not_lt hj
          have hjTot : j < l1.length + l2.length := by
            simpa [C, List.length_ofFn] using hjL
          have ht : j - l1.length < l2.length := by
            refine (Nat.sub_lt_iff_lt_add hjge).2 ?_
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hjTot
          have hjA : A.length ≤ j := by
            simpa [A, List.length_ofFn] using hjge
          have h0 :=
            vertsNatLen_append_right (k := 0) start l1 l2 (j - l1.length) (Nat.le_of_lt ht)
          have h1 :=
            vertsNatLen_append_right (k := 0) start l1 l2 (j - l1.length + 1) (Nat.succ_le_of_lt ht)
          rw [List.getElem_append_right (as := A) (bs := B) (i := j) hjA]
          have hsplit : j = l1.length + (j - l1.length) := by
            simpa using (Nat.add_sub_of_le hjge).symm
          have hsplit1 : j + 1 = l1.length + (j - l1.length + 1) := by
            omega
          have hlenA : A.length = l1.length := by
            simp [A, List.length_ofFn]
          have hsubA : j - A.length = j - l1.length := by
            simp [hlenA]
          have hBlen : B.length = l2.length := by
            simp [B, List.length_ofFn]
          have hBidx : j - l1.length < B.length := by
            simpa [hBlen] using ht
          have h0' :
              vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i])
                  (l1.length + (j - l1.length))
                =
              vertsNatLen (applyOrder start l1) (fun i : Fin l2.length => l2[i]) (j - l1.length) := by
            exact
              (vertsNatLen_append_len_bridge (k := 0) start l1 l2 (l1.length + (j - l1.length))).symm.trans h0
          have h1' :
              vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i])
                  (l1.length + (j - l1.length + 1))
                =
              vertsNatLen (applyOrder start l1) (fun i : Fin l2.length => l2[i]) (j - l1.length + 1) := by
            exact
              (vertsNatLen_append_len_bridge (k := 0) start l1 l2 (l1.length + (j - l1.length + 1))).symm.trans h1
          have hCB :
              c
                  (edgeOf
                    (vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i])
                      (l1.length + (j - l1.length)))
                    (vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i])
                      (l1.length + (j - l1.length + 1))))
                =
              c
                  (edgeOf
                    (vertsNatLen (applyOrder start l1) (fun i : Fin l2.length => l2[i]) (j - l1.length))
                    (vertsNatLen (applyOrder start l1) (fun i : Fin l2.length => l2[i]) (j - l1.length + 1))) := by
            rw [h0', h1']
          have hCBj :
              c
                  (edgeOf
                    (vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i]) j)
                    (vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i]) (j + 1)))
                =
              c
                  (edgeOf
                    (vertsNatLen (applyOrder start l1) (fun i : Fin l2.length => l2[i]) (j - l1.length))
                    (vertsNatLen (applyOrder start l1) (fun i : Fin l2.length => l2[i]) (j - l1.length + 1))) := by
            calc
              c
                  (edgeOf
                    (vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i]) j)
                    (vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i]) (j + 1)))
                  =
              c
                  (edgeOf
                    (vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i])
                      (l1.length + (j - l1.length)))
                    (vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i])
                      (l1.length + (j - l1.length + 1)))) := by
                conv_lhs => rw [hsplit1, hsplit]
                have hnorm :
                    l1.length + (l1.length + (j - l1.length) - l1.length + 1)
                      =
                    l1.length + (j - l1.length + 1) := by
                  omega
                simp
              _ = c
                    (edgeOf
                      (vertsNatLen (applyOrder start l1) (fun i : Fin l2.length => l2[i]) (j - l1.length))
                      (vertsNatLen (applyOrder start l1) (fun i : Fin l2.length => l2[i]) (j - l1.length + 1))) := hCB
          have hCj :
              C[j]'hjL
                =
              c
                  (edgeOf
                    (vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i]) j)
                    (vertsNatLen start (fun i : Fin (l1 ++ l2).length => (l1 ++ l2)[i]) (j + 1))) := by
            simp [C, castIdx, List.getElem_ofFn, GeoPath.ofCoordFnLen]
          have hBj :
              B[j - l1.length]'hBidx
                =
              c
                  (edgeOf
                    (vertsNatLen (applyOrder start l1) (fun i : Fin l2.length => l2[i]) (j - l1.length))
                    (vertsNatLen (applyOrder start l1) (fun i : Fin l2.length => l2[i]) (j - l1.length + 1))) := by
            simp [B, List.getElem_ofFn, GeoPath.ofCoordFnLen]
          have hgoal : C[j]'hjL = B[j - l1.length]'hBidx := by
            exact hCj.trans (hCBj.trans hBj.symm)
          simpa [hsubA] using hgoal
    )

end Algo1AppendHelpers

section Algo1ChunkStepBounds

private lemma chunkOrderFromChoice_eq_canonical
    (g : AntiGeoData n) (i : Fin (numChunks n k))
    (choice : ChunkChoice (k := k)) :
    chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice
      =
    @chunkOrderFromChoice n k hk hkn (instDecidableEqFin n) g i choice := by
  have hdeq : (inferInstance : DecidableEq (Fin n)) = instDecidableEqFin n := by
    exact Subsingleton.elim _ _
  cases hdeq
  rfl

private lemma chunkColoring_eq_canonical
    (c : Coloring n) (g : AntiGeoData n) (i : Fin (numChunks n k)) :
    chunkColoring (n := n) (k := k) hk hkn c g i
      =
    @chunkColoring n k hk hkn (instDecidableEqFin n) c g i := by
  have hdeq : (inferInstance : DecidableEq (Fin n)) = instDecidableEqFin n := by
    exact Subsingleton.elim _ _
  cases hdeq
  rfl

private lemma chunkStartSmall_eq_canonical
    (g : AntiGeoData n) (i : Fin (numChunks n k)) :
    chunkStartSmall (n := n) (k := k) hk hkn g i
      =
    @chunkStartSmall n k hk hkn (instDecidableEqFin n) g i := by
  have hdeq : (inferInstance : DecidableEq (Fin n)) = instDecidableEqFin n := by
    exact Subsingleton.elim _ _
  cases hdeq
  rfl

private lemma chooseChunk_firstColor_big_eq_prev_of_canStartBoth
    (c : Coloring n) (g : AntiGeoData n) (i : Fin (numChunks n k))
    (b : Bool)
    (h : canStartBothColorsAtOpt k
          (chunkColoring (n := n) (k := k) hk hkn c g i)
          (chunkStartSmall (n := n) (k := k) hk hkn g i)) :
    let choice := chooseChunk (n := n) (k := k) hk hkn c g i (some b)
    firstColorFromOrder? (n := n) c
        (chunkStartVertex (n := n) (k := k) hk hkn g i)
        (chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice)
      = some b := by
  classical
  intro choice
  have hlocal :
      List.head?
        ((localPath (k := k)
            (chunkStartSmall (n := n) (k := k) hk hkn g i)
            choice.σ).edgeColors
          (chunkColoring (n := n) (k := k) hk hkn c g i))
        = some b := by
    simpa [choice] using
      chooseChunk_firstColor_eq_prev_of_canStartBoth
        (n := n) (k := k) hk hkn c g i b h
  have hcanon :
      chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice
        =
      @chunkOrderFromChoice n k hk hkn (instDecidableEqFin n) g i choice :=
    chunkOrderFromChoice_eq_canonical (n := n) (k := k) hk hkn g i choice
  have hcol :
      chunkColoring (n := n) (k := k) hk hkn c g i
        =
      @chunkColoring n k hk hkn (instDecidableEqFin n) c g i :=
    chunkColoring_eq_canonical (n := n) (k := k) hk hkn c g i
  have hsmall :
      chunkStartSmall (n := n) (k := k) hk hkn g i
        =
      @chunkStartSmall n k hk hkn (instDecidableEqFin n) g i :=
    chunkStartSmall_eq_canonical (n := n) (k := k) hk hkn g i
  have htransportCanonical :
      firstColorFromOrder? (n := n) c
          (chunkStartVertex (n := n) (k := k) hk hkn g i)
          (@chunkOrderFromChoice n k hk hkn (instDecidableEqFin n) g i choice)
        =
      List.head?
        ((localPath (k := k)
            (chunkStartSmall (n := n) (k := k) hk hkn g i)
            choice.σ).edgeColors
          (chunkColoring (n := n) (k := k) hk hkn c g i)) := by
    simpa [chunkOrderFromChoice, hcol, hsmall] using
      (firstColorFromOrder_chunkOrder_eq_localPath_head
        (n := n) (k := k) hk hkn c g i choice.σ)
  have htransport :
      firstColorFromOrder? (n := n) c
        (chunkStartVertex (n := n) (k := k) hk hkn g i)
        (chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice)
      =
    List.head?
      ((localPath (k := k)
          (chunkStartSmall (n := n) (k := k) hk hkn g i)
          choice.σ).edgeColors
        (chunkColoring (n := n) (k := k) hk hkn c g i)) := by
    simpa [hcanon] using htransportCanonical
  exact htransport.trans hlocal

private lemma chooseChunk_chunkOrder_changes_eq_minChanges
    (c : Coloring n) (g : AntiGeoData n) (i : Fin (numChunks n k))
    (prev : Option Bool) :
    let choice := chooseChunk (n := n) (k := k) hk hkn c g i prev
    changesFromOrder (n := n) c
        (chunkStartVertex (n := n) (k := k) hk hkn g i)
        (chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice)
      =
    minChangesInCube k
      (chunkColoring (n := n) (k := k) hk hkn c g i)
      (chunkStartSmall (n := n) (k := k) hk hkn g i) := by
  classical
  intro choice
  have hcanon :
      chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice
        =
      @chunkOrderFromChoice n k hk hkn (instDecidableEqFin n) g i choice :=
    chunkOrderFromChoice_eq_canonical (n := n) (k := k) hk hkn g i choice
  have hcol :
      chunkColoring (n := n) (k := k) hk hkn c g i
        =
      @chunkColoring n k hk hkn (instDecidableEqFin n) c g i :=
    chunkColoring_eq_canonical (n := n) (k := k) hk hkn c g i
  have hsmall :
      chunkStartSmall (n := n) (k := k) hk hkn g i
        =
      @chunkStartSmall n k hk hkn (instDecidableEqFin n) g i :=
    chunkStartSmall_eq_canonical (n := n) (k := k) hk hkn g i
  have htransportCanonical :
      changesFromOrder (n := n) c
          (chunkStartVertex (n := n) (k := k) hk hkn g i)
          (@chunkOrderFromChoice n k hk hkn (instDecidableEqFin n) g i choice)
        =
      localCost (k := k)
          (chunkColoring (n := n) (k := k) hk hkn c g i)
          (chunkStartSmall (n := n) (k := k) hk hkn g i)
          choice.σ := by
    simpa [chunkOrderFromChoice, hcol, hsmall] using
      (changesFromOrder_chunkOrder_eq_localCost
        (n := n) (k := k) hk hkn c g i choice.σ)
  have htransport :
      changesFromOrder (n := n) c
          (chunkStartVertex (n := n) (k := k) hk hkn g i)
          (chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice)
        =
      localCost (k := k)
          (chunkColoring (n := n) (k := k) hk hkn c g i)
          (chunkStartSmall (n := n) (k := k) hk hkn g i)
          choice.σ := by
    simpa [hcanon] using htransportCanonical
  have hopt :
      localCost (k := k)
          (chunkColoring (n := n) (k := k) hk hkn c g i)
          (chunkStartSmall (n := n) (k := k) hk hkn g i)
          choice.σ
        =
      minChangesInCube k
          (chunkColoring (n := n) (k := k) hk hkn c g i)
          (chunkStartSmall (n := n) (k := k) hk hkn g i) := by
    simpa [choice] using
      chooseChunk_sigma_opt (n := n) (k := k) hk hkn c g i prev
  exact htransport.trans hopt

end Algo1ChunkStepBounds

section Algo1FinalDecomp

private lemma changesOnColors_append_le_of_boundary_match :
    ∀ l1 l2 : List Bool,
      List.head? (List.reverse l1) = List.head? l2 →
      changesOnColors (l1 ++ l2) ≤ changesOnColors l1 + changesOnColors l2
  | [], l2, h => by
      cases l2 with
      | nil =>
          simp [changesOnColors]
      | cons b t =>
          cases h
  | [a], l2, h => by
      cases l2 with
      | nil =>
          cases h
      | cons b t =>
          have hb : a = b := by simpa using h
          subst hb
          simp [changesOnColors]
  | a :: b :: t, l2, h => by
      have htail : List.head? (List.reverse (b :: t)) = List.head? l2 := by
        simpa using h
      have ih := changesOnColors_append_le_of_boundary_match (b :: t) l2 htail
      simpa [changesOnColors, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_le_add_left ih (if a = b then 0 else 1)

omit [DecidableEq (Fin n)] in
private lemma changesFromOrder_append_le_add_one
    (c : Coloring n) (start : Vertex n) (l1 l2 : List (Fin n)) :
    changesFromOrder (n := n) c start (l1 ++ l2)
      ≤ changesFromOrder (n := n) c start l1
          + changesFromOrder (n := n) c (applyOrder start l1) l2 + 1 := by
  unfold changesFromOrder
  rw [edgeColorsFromOrder_append (n := n) (c := c) (start := start) (l1 := l1) (l2 := l2)]
  exact changesOnColors_append
    (edgeColorsFromOrder (n := n) c start l1)
    (edgeColorsFromOrder (n := n) c (applyOrder start l1) l2)

omit [DecidableEq (Fin n)] in
private lemma changesFromOrder_append_le_of_boundary_match
    (c : Coloring n) (start : Vertex n) (l1 l2 : List (Fin n))
    (hmatch :
      lastColorFromOrder? (n := n) c start l1
        =
      firstColorFromOrder? (n := n) c (applyOrder start l1) l2) :
    changesFromOrder (n := n) c start (l1 ++ l2)
      ≤ changesFromOrder (n := n) c start l1
          + changesFromOrder (n := n) c (applyOrder start l1) l2 := by
  unfold changesFromOrder lastColorFromOrder? firstColorFromOrder? at *
  rw [edgeColorsFromOrder_append (n := n) (c := c) (start := start) (l1 := l1) (l2 := l2)]
  exact changesOnColors_append_le_of_boundary_match
    (edgeColorsFromOrder (n := n) c start l1)
    (edgeColorsFromOrder (n := n) c (applyOrder start l1) l2)
    (by simpa [List.head?_reverse] using hmatch)

private lemma chooseChunk_lastColor_big_eq_choice_last
    (c : Coloring n) (g : AntiGeoData n) (i : Fin (numChunks n k))
    (prev : Option Bool) :
    let choice := chooseChunk (n := n) (k := k) hk hkn c g i prev
    lastColorFromOrder? (n := n) c
        (chunkStartVertex (n := n) (k := k) hk hkn g i)
        (chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice)
      = some choice.last := by
  classical
  intro choice
  have hcanon :
      chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice
        =
      @chunkOrderFromChoice n k hk hkn (instDecidableEqFin n) g i choice :=
    chunkOrderFromChoice_eq_canonical (n := n) (k := k) hk hkn g i choice
  have hcol :
      chunkColoring (n := n) (k := k) hk hkn c g i
        =
      @chunkColoring n k hk hkn (instDecidableEqFin n) c g i :=
    chunkColoring_eq_canonical (n := n) (k := k) hk hkn c g i
  have hsmall :
      chunkStartSmall (n := n) (k := k) hk hkn g i
        =
      @chunkStartSmall n k hk hkn (instDecidableEqFin n) g i :=
    chunkStartSmall_eq_canonical (n := n) (k := k) hk hkn g i
  have htransportCanonical :
      lastColorFromOrder? (n := n) c
          (chunkStartVertex (n := n) (k := k) hk hkn g i)
          (@chunkOrderFromChoice n k hk hkn (instDecidableEqFin n) g i choice)
        =
      List.head?
        (List.reverse
          ((localPath (k := k)
            (chunkStartSmall (n := n) (k := k) hk hkn g i) choice.σ).edgeColors
            (chunkColoring (n := n) (k := k) hk hkn c g i))) := by
    simpa [chunkOrderFromChoice, hcol, hsmall] using
      (lastColorFromOrder_chunkOrder_eq_localPath_last
        (n := n) (k := k) hk hkn c g i choice.σ)
  have htransport :
      lastColorFromOrder? (n := n) c
          (chunkStartVertex (n := n) (k := k) hk hkn g i)
          (chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice)
        =
      List.head?
        (List.reverse
          ((localPath (k := k)
            (chunkStartSmall (n := n) (k := k) hk hkn g i) choice.σ).edgeColors
            (chunkColoring (n := n) (k := k) hk hkn c g i))) := by
    simpa [hcanon] using htransportCanonical
  have hlocal :
      List.head?
        (List.reverse
          ((localPath (k := k)
            (chunkStartSmall (n := n) (k := k) hk hkn g i) choice.σ).edgeColors
            (chunkColoring (n := n) (k := k) hk hkn c g i)))
        = some choice.last := by
    have hkminus : k - 1 < k := by omega
    simp only [GeoPath.edgeColors, localPath, chooseChunk, GeoPath.edgeColorAt, Fin.castSucc_mk,
      Fin.succ_mk, List.head?_reverse, choice]
    rw [List.getLast?_eq_getElem?]
    simp [List.length_ofFn, hkminus]
  exact htransport.trans hlocal

end Algo1FinalDecomp

section Algo1FinalBound

private lemma changesOnColors_add_one_le_length_of_ne_nil
    (l : List Bool) (h : l ≠ []) :
    changesOnColors l + 1 ≤ l.length := by
  cases l with
  | nil =>
      cases h rfl
  | cons a t =>
      cases t with
      | nil =>
          simp [changesOnColors]
      | cons b t =>
          have ih :
              changesOnColors (b :: t) + 1 ≤ (b :: t).length :=
            changesOnColors_add_one_le_length_of_ne_nil (b :: t) (by simp)
          by_cases hab : a = b
          · have hbound : changesOnColors (b :: t) + 1 ≤ (b :: t).length + 1 :=
              Nat.le_trans ih (Nat.le_succ _)
            simpa [changesOnColors, hab, Nat.add_assoc] using hbound
          · have hbound : changesOnColors (b :: t) + 2 ≤ (b :: t).length + 1 := by
              omega
            simpa [changesOnColors, hab, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbound

private lemma changesOnColors_append_le_left_plus_length
    (l1 l2 : List Bool) :
    changesOnColors (l1 ++ l2) ≤ changesOnColors l1 + l2.length := by
  by_cases h2 : l2 = []
  · subst h2
    simp
  · have happ := changesOnColors_append l1 l2
    have hlen : changesOnColors l2 + 1 ≤ l2.length :=
      changesOnColors_add_one_le_length_of_ne_nil l2 h2
    exact le_trans happ (by omega)

omit [DecidableEq (Fin n)] in
private lemma changesFromOrder_append_le_right_length
    (c : Coloring n) (start : Vertex n) (l1 l2 : List (Fin n)) :
    changesFromOrder (n := n) c start (l1 ++ l2)
      ≤ changesFromOrder (n := n) c start l1 + l2.length := by
  unfold changesFromOrder
  rw [edgeColorsFromOrder_append (n := n) (c := c) (start := start) (l1 := l1) (l2 := l2)]
  have h :=
    changesOnColors_append_le_left_plus_length
      (edgeColorsFromOrder (n := n) c start l1)
      (edgeColorsFromOrder (n := n) c (applyOrder start l1) l2)
  have hlen :
      (edgeColorsFromOrder (n := n) c (applyOrder start l1) l2).length = l2.length := by
    simp [edgeColorsFromOrder, GeoPath.edgeColors]
  exact h.trans (by simp [hlen])

omit [DecidableEq (Fin n)] in
private lemma lastColorFromOrder_append_eq_right_of_some
    (c : Coloring n) (start : Vertex n) (l1 l2 : List (Fin n)) (b : Bool)
    (h2 : lastColorFromOrder? (n := n) c (applyOrder start l1) l2 = some b) :
    lastColorFromOrder? (n := n) c start (l1 ++ l2) = some b := by
  let A := edgeColorsFromOrder (n := n) c start l1
  let B := edgeColorsFromOrder (n := n) c (applyOrder start l1) l2
  have hBLast : B.getLast? = some b := by
    simpa [lastColorFromOrder?, B, List.head?_reverse] using h2
  have hBne : B ≠ [] := by
    intro hnil
    simp [B, hnil] at hBLast
  unfold lastColorFromOrder?
  rw [edgeColorsFromOrder_append (n := n) (c := c) (start := start) (l1 := l1) (l2 := l2)]
  have hABLast : (A ++ B).getLast? = some b := (List.getLast?_append_of_ne_nil A hBne).trans hBLast
  simpa [A, B] using hABLast

@[simp] private lemma chooseChunk_eq_canonical
    (c : Coloring n) (g : AntiGeoData n) (i : Fin (numChunks n k)) (prev : Option Bool) :
    chooseChunk (n := n) (k := k) hk hkn c g i prev
      =
    @chooseChunk n k hk hkn (instDecidableEqFin n) c g i prev := by
  have hdeq : (inferInstance : DecidableEq (Fin n)) = instDecidableEqFin n := by
    exact Subsingleton.elim _ _
  cases hdeq
  rfl

@[simp] private lemma chunkOrderFromChoice_eq_canonical_simp
    (g : AntiGeoData n) (i : Fin (numChunks n k))
    (choice : ChunkChoice (k := k)) :
    chunkOrderFromChoice (n := n) (k := k) hk hkn g i choice
      =
    @chunkOrderFromChoice n k hk hkn (instDecidableEqFin n) g i choice :=
  chunkOrderFromChoice_eq_canonical (n := n) (k := k) hk hkn g i choice

@[simp] private lemma algorithm1ChunkAcc_eq_canonical
    (c : Coloring n) (g : AntiGeoData n) :
    algorithm1ChunkAcc (n := n) (k := k) hk hkn c g
      =
    @algorithm1ChunkAcc n k hk hkn (instDecidableEqFin n) c g := by
  have hdeq : (inferInstance : DecidableEq (Fin n)) = instDecidableEqFin n := by
    exact Subsingleton.elim _ _
  cases hdeq
  rfl

@[simp] private lemma algorithm1ChunkCoords_eq_canonical
    (c : Coloring n) (g : AntiGeoData n) :
    algorithm1ChunkCoords (n := n) (k := k) hk hkn c g
      =
    @algorithm1ChunkCoords n k hk hkn (instDecidableEqFin n) c g := by
  unfold algorithm1ChunkCoords
  simp

private noncomputable def chunkContributionNat
    (c : Coloring n) (i : Fin (numChunks n k)) (g : AntiGeoData n) : Nat :=
  by
    classical
    exact
      minChangesInCube k
          (chunkColoring (n := n) (k := k) hk hkn c g i)
          (chunkStartSmall (n := n) (k := k) hk hkn g i)
        +
        if canStartBothColorsAtOpt k
            (chunkColoring (n := n) (k := k) hk hkn c g i)
            (chunkStartSmall (n := n) (k := k) hk hkn g i) then 0 else 1

private lemma chunkContributionG_eq_chunkContributionNat
    (c : Coloring n) (i : Fin (numChunks n k)) (g : AntiGeoData n) :
    chunkContributionG hk hkn c i g
      = (chunkContributionNat (n := n) (k := k) hk hkn c i g : ℚ) := by
  classical
  unfold chunkContributionG chunkContributionNat chunkContribution
  simp [chunkColoring_eq_canonical (n := n) (k := k) hk hkn c g i,
    chunkStartSmall_eq_canonical (n := n) (k := k) hk hkn g i]

private lemma minChanges_le_chunkContributionNat
    (c : Coloring n) (i : Fin (numChunks n k)) (g : AntiGeoData n) :
    minChangesInCube k
        (chunkColoring (n := n) (k := k) hk hkn c g i)
        (chunkStartSmall (n := n) (k := k) hk hkn g i)
      ≤ chunkContributionNat (n := n) (k := k) hk hkn c i g := by
  simp [chunkContributionNat]

private noncomputable def chunkPrefixNat (c : Coloring n) (g : AntiGeoData n) (t : Nat) : Nat := by
  classical
  exact Finset.sum (Finset.range t) (fun j =>
    if hj : j < numChunks n k then
      chunkContributionNat (n := n) (k := k) hk hkn c ⟨j, hj⟩ g
    else 0)

private lemma chunkPrefixNat_succ_of_lt
    (c : Coloring n) (g : AntiGeoData n) {t : Nat} (ht : t < numChunks n k) :
    chunkPrefixNat hk hkn c g (t + 1)
      =
    chunkPrefixNat hk hkn c g t
      + chunkContributionNat (n := n) (k := k) hk hkn c ⟨t, ht⟩ g := by
  unfold chunkPrefixNat
  simp [Finset.sum_range_succ, ht]

private lemma chunkPrefixNat_eq_sum_fin
    (c : Coloring n) (g : AntiGeoData n) :
    chunkPrefixNat hk hkn c g (numChunks n k)
      =
    ∑ i : Fin (numChunks n k), chunkContributionNat (n := n) (k := k) hk hkn c i g := by
  unfold chunkPrefixNat
  let f : ℕ → Nat := fun j =>
    if hj : j < numChunks n k then
      chunkContributionNat (n := n) (k := k) hk hkn c ⟨j, hj⟩ g
    else 0
  have hsum : (∑ i : Fin (numChunks n k), f i.1)
      = (∑ j ∈ Finset.range (numChunks n k), f j) :=
    Fin.sum_univ_eq_sum_range f (numChunks n k)
  have hfin :
      (∑ i : Fin (numChunks n k), f i.1)
        =
      ∑ i : Fin (numChunks n k), chunkContributionNat (n := n) (k := k) hk hkn c i g := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [f, i.2]
  calc
    (∑ j ∈ Finset.range (numChunks n k),
        if hj : j < numChunks n k then chunkContributionNat (n := n) (k := k) hk hkn c ⟨j, hj⟩ g else 0)
      = ∑ i : Fin (numChunks n k), f i.1 := by
          simpa [f] using hsum.symm
    _ = ∑ i : Fin (numChunks n k), chunkContributionNat (n := n) (k := k) hk hkn c i g := hfin

private lemma algorithm1ChunkAccRec_bound_and_prev
    (c : Coloring n) (g : AntiGeoData n) :
    ∀ t : Nat, t ≤ numChunks n k →
      changesFromOrder (n := n) c g.start (algorithm1ChunkAccRec hk hkn c g t).1
        ≤ chunkPrefixNat hk hkn c g t
      ∧
      (algorithm1ChunkAccRec hk hkn c g t).2
        =
      lastColorFromOrder? (n := n) c g.start (algorithm1ChunkAccRec hk hkn c g t).1
  | 0, _ => by
      constructor
      · simp [algorithm1ChunkAccRec, chunkPrefixNat, changesFromOrder, edgeColorsFromOrder,
          GeoPath.edgeColors, changesOnColors]
      · simp [algorithm1ChunkAccRec, lastColorFromOrder?, edgeColorsFromOrder, GeoPath.edgeColors]
  | t + 1, ht1 => by
      have ht : t < numChunks n k := Nat.lt_of_succ_le ht1
      rcases algorithm1ChunkAccRec_bound_and_prev c g t (Nat.le_of_lt ht) with ⟨ihCost, ihPrev⟩
      let ii : Fin (numChunks n k) := ⟨t, ht⟩
      let acc := algorithm1ChunkAccRec hk hkn c g t
      let prev := acc.2
      let choice := chooseChunk (n := n) (k := k) hk hkn c g ii prev
      let chunkOrder := chunkOrderFromChoice (n := n) (k := k) hk hkn g ii choice
      have ihCostAcc :
          changesFromOrder (n := n) c g.start acc.1
            ≤ chunkPrefixNat hk hkn c g t := by
        simpa [acc] using ihCost
      have ihPrevAcc :
          prev
            =
          lastColorFromOrder? (n := n) c g.start acc.1 := by
        simpa [acc, prev] using ihPrev
      have hstart :
          applyOrder g.start acc.1
            = chunkStartVertex (n := n) (k := k) hk hkn g ii := by
        have hboundary :=
          applyOrder_chunkAccRec_eq_chunkBoundary
            (n := n) (k := k) hk hkn c g t (Nat.le_of_lt ht)
        change applyOrder g.start (algorithm1ChunkAccRec hk hkn c g t).1
            = chunkStartVertex (n := n) (k := k) hk hkn g ii
        rw [hboundary]
        simp [ii, chunkStartVertex, AntiGeoData.toGeoPath, GeoPath.ofCoordFn]
      have hchunkMin :
          changesFromOrder (n := n) c (applyOrder g.start acc.1) chunkOrder
            =
          minChangesInCube k
            (chunkColoring (n := n) (k := k) hk hkn c g ii)
            (chunkStartSmall (n := n) (k := k) hk hkn g ii) := by
        rw [hstart]
        simpa [choice, chunkOrder, prev, ii] using
          (chooseChunk_chunkOrder_changes_eq_minChanges
            (n := n) (k := k) hk hkn c g ii prev)
      have hcostStep :
          changesFromOrder (n := n) c g.start (acc.1 ++ chunkOrder)
            ≤
          changesFromOrder (n := n) c g.start acc.1
            + chunkContributionNat (n := n) (k := k) hk hkn c ii g := by
        cases hprev : prev with
        | none =>
            have hlastNone :
                lastColorFromOrder? (n := n) c g.start acc.1 = none := by
              simpa [hprev] using ihPrevAcc.symm
            have hedgeNil :
                edgeColorsFromOrder (n := n) c g.start acc.1 = [] := by
              cases hE : edgeColorsFromOrder (n := n) c g.start acc.1 with
              | nil =>
                  rfl
              | cons b t =>
                  have : False := by
                    simp [lastColorFromOrder?, hE] at hlastNone -- [lastColorFromOrder?, hE] using hlastNone
                  exact this.elim
            have haccNil : acc.1 = [] := by
              have : (edgeColorsFromOrder (n := n) c g.start acc.1).length = 0 := by
                simp [hedgeNil]
              have hlen0 : acc.1.length = 0 := by
                simpa [edgeColorsFromOrder, GeoPath.edgeColors] using this
              exact List.eq_nil_of_length_eq_zero hlen0
            have hminLe :
                minChangesInCube k
                    (chunkColoring (n := n) (k := k) hk hkn c g ii)
                    (chunkStartSmall (n := n) (k := k) hk hkn g ii)
                  ≤
                chunkContributionNat (n := n) (k := k) hk hkn c ii g :=
              minChanges_le_chunkContributionNat (n := n) (k := k) hk hkn c ii g
            have hchunkMin' :
                changesFromOrder (n := n) c g.start chunkOrder
                  =
                minChangesInCube k
                  (chunkColoring (n := n) (k := k) hk hkn c g ii)
                  (chunkStartSmall (n := n) (k := k) hk hkn g ii) := by
              simpa [haccNil, applyOrder] using hchunkMin
            have hchunkLe :
                changesFromOrder (n := n) c g.start (acc.1 ++ chunkOrder)
                  ≤
                chunkContributionNat (n := n) (k := k) hk hkn c ii g := by
              calc
                changesFromOrder (n := n) c g.start (acc.1 ++ chunkOrder)
                    =
                  changesFromOrder (n := n) c g.start chunkOrder := by
                      simp [haccNil]
                _ =
                  minChangesInCube k
                    (chunkColoring (n := n) (k := k) hk hkn c g ii)
                    (chunkStartSmall (n := n) (k := k) hk hkn g ii) := by
                      exact hchunkMin'
                _ ≤ chunkContributionNat (n := n) (k := k) hk hkn c ii g := hminLe
            have haccZero : changesFromOrder (n := n) c g.start acc.1 = 0 := by
              simp [haccNil, changesFromOrder, edgeColorsFromOrder, GeoPath.edgeColors, changesOnColors]
            calc
              changesFromOrder (n := n) c g.start (acc.1 ++ chunkOrder)
                  ≤ chunkContributionNat (n := n) (k := k) hk hkn c ii g := hchunkLe
              _ = changesFromOrder (n := n) c g.start acc.1
                    + chunkContributionNat (n := n) (k := k) hk hkn c ii g := by
                    simp [haccZero]
        | some b =>
            by_cases hcan :
                canStartBothColorsAtOpt k
                  (chunkColoring (n := n) (k := k) hk hkn c g ii)
                  (chunkStartSmall (n := n) (k := k) hk hkn g ii)
            · have hlastAcc :
                  lastColorFromOrder? (n := n) c g.start acc.1 = some b := by
                simpa [hprev] using ihPrevAcc.symm
              have hfirstChunk :
                  firstColorFromOrder? (n := n) c
                      (chunkStartVertex (n := n) (k := k) hk hkn g ii)
                      chunkOrder
                    = some b := by
                simpa [choice, chunkOrder, hprev] using
                  (chooseChunk_firstColor_big_eq_prev_of_canStartBoth
                    (n := n) (k := k) hk hkn c g ii b hcan)
              have hfirstApply :
                  firstColorFromOrder? (n := n) c (applyOrder g.start acc.1) chunkOrder
                    = some b := by
                simpa [hstart] using hfirstChunk
              have hmatch :
                  lastColorFromOrder? (n := n) c g.start acc.1
                    =
                  firstColorFromOrder? (n := n) c (applyOrder g.start acc.1) chunkOrder := by
                exact hlastAcc.trans hfirstApply.symm
              have happ :
                  changesFromOrder (n := n) c g.start (acc.1 ++ chunkOrder)
                    ≤
                  changesFromOrder (n := n) c g.start acc.1
                    + changesFromOrder (n := n) c (applyOrder g.start acc.1) chunkOrder :=
                changesFromOrder_append_le_of_boundary_match
                  (n := n) (c := c) (start := g.start)
                  (l1 := acc.1) (l2 := chunkOrder) hmatch
              have hcontrib :
                  chunkContributionNat (n := n) (k := k) hk hkn c ii g
                    =
                  minChangesInCube k
                    (chunkColoring (n := n) (k := k) hk hkn c g ii)
                    (chunkStartSmall (n := n) (k := k) hk hkn g ii) := by
                simp [chunkContributionNat, hcan]
              calc
                changesFromOrder (n := n) c g.start (acc.1 ++ chunkOrder)
                    ≤
                  changesFromOrder (n := n) c g.start acc.1
                    + changesFromOrder (n := n) c (applyOrder g.start acc.1) chunkOrder := happ
                _ =
                  changesFromOrder (n := n) c g.start acc.1
                    + minChangesInCube k
                        (chunkColoring (n := n) (k := k) hk hkn c g ii)
                        (chunkStartSmall (n := n) (k := k) hk hkn g ii) := by
                      rw [hchunkMin]
                _ =
                  changesFromOrder (n := n) c g.start acc.1
                    + chunkContributionNat (n := n) (k := k) hk hkn c ii g := by
                      rw [hcontrib]
            · have happ :
                  changesFromOrder (n := n) c g.start (acc.1 ++ chunkOrder)
                    ≤
                  changesFromOrder (n := n) c g.start acc.1
                    + changesFromOrder (n := n) c (applyOrder g.start acc.1) chunkOrder + 1 :=
                changesFromOrder_append_le_add_one
                  (n := n) (c := c) (start := g.start) (l1 := acc.1) (l2 := chunkOrder)
              have hcontrib :
                  chunkContributionNat (n := n) (k := k) hk hkn c ii g
                    =
                  minChangesInCube k
                    (chunkColoring (n := n) (k := k) hk hkn c g ii)
                    (chunkStartSmall (n := n) (k := k) hk hkn g ii) + 1 := by
                simp [chunkContributionNat, hcan]
              calc
                changesFromOrder (n := n) c g.start (acc.1 ++ chunkOrder)
                    ≤
                  changesFromOrder (n := n) c g.start acc.1
                    + changesFromOrder (n := n) c (applyOrder g.start acc.1) chunkOrder + 1 := happ
                _ =
                  changesFromOrder (n := n) c g.start acc.1
                    + (minChangesInCube k
                        (chunkColoring (n := n) (k := k) hk hkn c g ii)
                        (chunkStartSmall (n := n) (k := k) hk hkn g ii) + 1) := by
                      rw [hchunkMin]
                      omega
                _ =
                  changesFromOrder (n := n) c g.start acc.1
                    + chunkContributionNat (n := n) (k := k) hk hkn c ii g := by
                      rw [hcontrib]
      have hprefixSucc :
          chunkPrefixNat hk hkn c g (t + 1)
            =
          chunkPrefixNat hk hkn c g t
            + chunkContributionNat (n := n) (k := k) hk hkn c ii g :=
        chunkPrefixNat_succ_of_lt hk hkn c g ht
      have hii : ∀ h' : t < numChunks n k, (⟨t, h'⟩ : Fin (numChunks n k)) = ii := by
        intro h'
        ext
        rfl
      have hrec1 :
          (algorithm1ChunkAccRec hk hkn c g (t + 1)).1 = acc.1 ++ chunkOrder := by
        simp [algorithm1ChunkAccRec, ht, acc, prev, ii, choice, chunkOrder, hii]
      have hrec2 :
          (algorithm1ChunkAccRec hk hkn c g (t + 1)).2 = some choice.last := by
        simp [algorithm1ChunkAccRec, ht, acc, prev, ii, choice, hii]
      have hcostNext :
          changesFromOrder (n := n) c g.start (algorithm1ChunkAccRec hk hkn c g (t + 1)).1
            ≤
          chunkPrefixNat hk hkn c g (t + 1) := by
        rw [hrec1, hprefixSucc]
        exact le_trans hcostStep (Nat.add_le_add_right ihCostAcc _)
      have hlastChunk :
          lastColorFromOrder? (n := n) c
              (chunkStartVertex (n := n) (k := k) hk hkn g ii)
              chunkOrder
            = some choice.last := by
        simpa [choice, chunkOrder, prev, ii] using
          (chooseChunk_lastColor_big_eq_choice_last
            (n := n) (k := k) hk hkn c g ii prev)
      have hlastApply :
          lastColorFromOrder? (n := n) c (applyOrder g.start acc.1) chunkOrder
            = some choice.last := by
        simpa [hstart] using hlastChunk
      have hlastAppend :
          lastColorFromOrder? (n := n) c g.start (acc.1 ++ chunkOrder)
            = some choice.last :=
        lastColorFromOrder_append_eq_right_of_some
          (n := n) (c := c) (start := g.start)
          (l1 := acc.1) (l2 := chunkOrder) (b := choice.last) hlastApply
      have hprevNext :
          (algorithm1ChunkAccRec hk hkn c g (t + 1)).2
            =
          lastColorFromOrder? (n := n) c g.start (algorithm1ChunkAccRec hk hkn c g (t + 1)).1 := by
        rw [hrec2, hrec1]
        exact hlastAppend.symm
      exact ⟨hcostNext, hprevNext⟩

set_option maxHeartbeats 800000 in
-- This lemma triggers heavy definitional reduction across instance transports.
private lemma algoCost_nat_le_sum_chunkContributionNat_add_remSteps
    (c : Coloring n) (g : AntiGeoData n) :
    algoCost (n := n) (k := k) hk hkn c g
      ≤
    (∑ i : Fin (numChunks n k), chunkContributionNat (n := n) (k := k) hk hkn c i g)
      + remSteps n k := by
  have hinv :=
    algorithm1ChunkAccRec_bound_and_prev
      (n := n) (k := k) hk hkn c g
      (numChunks n k) (Nat.le_refl _)
  have hchunkPrefix :
      changesFromOrder (n := n) c g.start (algorithm1ChunkAccRec hk hkn c g (numChunks n k)).1
        ≤ chunkPrefixNat hk hkn c g (numChunks n k) := hinv.1
  have hchunkCost :
      changesFromOrder (n := n) c g.start (algorithm1ChunkCoords (n := n) (k := k) hk hkn c g)
        ≤ chunkPrefixNat hk hkn c g (numChunks n k) := by
    unfold algorithm1ChunkCoords
    have haccEq :
        (algorithm1ChunkAcc (n := n) (k := k) hk hkn c g).1
          =
        (algorithm1ChunkAccRec hk hkn c g (numChunks n k)).1 := by
      have haccEqCanon :
          (@algorithm1ChunkAcc n k hk hkn (instDecidableEqFin n) c g).1
            =
          (algorithm1ChunkAccRec hk hkn c g (numChunks n k)).1 := by
        simpa using congrArg Prod.fst (algorithm1ChunkAcc_eq_rec (n := n) (k := k) hk hkn c g)
      simpa [algorithm1ChunkAcc_eq_canonical (n := n) (k := k) hk hkn c g] using haccEqCanon
    rw [haccEq]
    exact hchunkPrefix
  have hprefixFull :
      chunkPrefixNat hk hkn c g (numChunks n k)
        =
      ∑ i : Fin (numChunks n k), chunkContributionNat (n := n) (k := k) hk hkn c i g :=
    chunkPrefixNat_eq_sum_fin hk hkn c g
  have hchunkBound :
      changesFromOrder (n := n) c g.start (algorithm1ChunkCoords (n := n) (k := k) hk hkn c g)
        ≤
      ∑ i : Fin (numChunks n k), chunkContributionNat (n := n) (k := k) hk hkn c i g := by
    rw [← hprefixFull]
    exact hchunkCost
  have hchunkBoundCanon :
      changesFromOrder (n := n) c g.start
          (@algorithm1ChunkCoords n k hk hkn (instDecidableEqFin n) c g)
        ≤
      ∑ i : Fin (numChunks n k), chunkContributionNat (n := n) (k := k) hk hkn c i g := by
    simpa [algorithm1ChunkCoords_eq_canonical (n := n) (k := k) hk hkn c g] using hchunkBound
  have happ :
      changesFromOrder (n := n) c g.start
          ((algorithm1ChunkCoords (n := n) (k := k) hk hkn c g)
            ++ (List.ofFn g.perm).drop ((numChunks n k) * k))
        ≤
      changesFromOrder (n := n) c g.start (algorithm1ChunkCoords (n := n) (k := k) hk hkn c g)
        + ((List.ofFn g.perm).drop ((numChunks n k) * k)).length :=
    changesFromOrder_append_le_right_length
      (n := n) (c := c) (start := g.start)
      (l1 := algorithm1ChunkCoords (n := n) (k := k) hk hkn c g)
      (l2 := (List.ofFn g.perm).drop ((numChunks n k) * k))
  have happCanon :
      changesFromOrder (n := n) c g.start
          ((@algorithm1ChunkCoords n k hk hkn (instDecidableEqFin n) c g)
            ++ (List.ofFn g.perm).drop ((numChunks n k) * k))
        ≤
      changesFromOrder (n := n) c g.start
          (@algorithm1ChunkCoords n k hk hkn (instDecidableEqFin n) c g)
        + ((List.ofFn g.perm).drop ((numChunks n k) * k)).length := by
    simpa [algorithm1ChunkCoords_eq_canonical (n := n) (k := k) hk hkn c g] using happ
  have hremLen :
      ((List.ofFn g.perm).drop ((numChunks n k) * k)).length = remSteps n k := by
    simp [List.length_drop, List.length_ofFn, remSteps, numChunks,
      Nat.mod_eq_sub_mul_div, Nat.mul_comm]
  unfold algoCost algorithm1FinalCoords
  calc
    changesFromOrder (n := n) c g.start
        ((@algorithm1ChunkCoords n k hk hkn (instDecidableEqFin n) c g)
          ++ (List.ofFn g.perm).drop ((numChunks n k) * k))
      ≤
    changesFromOrder (n := n) c g.start
        (@algorithm1ChunkCoords n k hk hkn (instDecidableEqFin n) c g)
      + ((List.ofFn g.perm).drop ((numChunks n k) * k)).length := happCanon
    _ ≤
      (∑ i : Fin (numChunks n k), chunkContributionNat (n := n) (k := k) hk hkn c i g)
        + ((List.ofFn g.perm).drop ((numChunks n k) * k)).length := by
          exact Nat.add_le_add_right hchunkBoundCanon _
    _ =
      (∑ i : Fin (numChunks n k), chunkContributionNat (n := n) (k := k) hk hkn c i g)
        + remSteps n k := by
          simp [hremLen]

end Algo1FinalBound

lemma algoCost_le_sum_chunkContributionG_add_remSteps
  (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (c : Coloring n) (g : AntiGeoData n) :
  (algoCost (n := n) (k := k) hk hkn c g : ℚ)
    ≤ (∑ i : Fin (numChunks n k), chunkContributionG hk hkn c i g)
      + (remSteps n k : ℚ) := by
  have hnat :
      algoCost (n := n) (k := k) hk hkn c g
        ≤
      (∑ i : Fin (numChunks n k), chunkContributionNat (n := n) (k := k) hk hkn c i g)
        + remSteps n k :=
    algoCost_nat_le_sum_chunkContributionNat_add_remSteps
      (n := n) (k := k) hk hkn c g
  have hnatQ :
      (algoCost (n := n) (k := k) hk hkn c g : ℚ)
        ≤
      ((∑ i : Fin (numChunks n k),
          chunkContributionNat (n := n) (k := k) hk hkn c i g) : ℚ)
        + (remSteps n k : ℚ) := by
    exact_mod_cast hnat
  calc
    (algoCost (n := n) (k := k) hk hkn c g : ℚ)
      ≤
    ((∑ i : Fin (numChunks n k),
        chunkContributionNat (n := n) (k := k) hk hkn c i g) : ℚ)
      + (remSteps n k : ℚ) := hnatQ
    _ =
      (∑ i : Fin (numChunks n k), chunkContributionG hk hkn c i g)
        + (remSteps n k : ℚ) := by
          congr 1
          simp [chunkContributionG_eq_chunkContributionNat]

-- (B) per‑chunk expectation bound:
lemma expected_chunkContribution_le_fhat_add_one
  (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (c : Coloring n)
  (i : Fin (numChunks n k)) :
  expectedCost n (fun g => chunkContributionG hk hkn c i g)
    ≤ fhat k + 1 := by
  classical
  -- 1) pointwise inequality
  have hpoint :
      ∀ g : AntiGeoData n,
        chunkContributionG hk hkn c i g
          ≤ (adjustedCost k (@chunkColoring n k hk hkn _ c g i) (@chunkStartSmall n k hk hkn _ g i) : ℚ) + 1 := by
    intro g
    -- your lemma is on the k-cube, so we apply it to the induced k-coloring + start vertex:
    exact chunkContribution_le_adjustedCost_add_one_q
        (k := k)
        (c := @chunkColoring n k hk hkn _ c g i)
        (u := @chunkStartSmall n k hk hkn _ g i)
  -- 2) take expectations + pull out the constant
  have hmono :
      expectedCost n (fun g => chunkContributionG hk hkn c i g)
        ≤ expectedCost n (fun g =>
            (adjustedCost k (@chunkColoring n k hk hkn _ c g i) (@chunkStartSmall n k hk hkn _ g i) : ℚ) + 1) :=
    expectedCost_mono (n := n) hpoint
  have hadd :
      expectedCost n (fun g =>
          (adjustedCost k (@chunkColoring n k hk hkn _ c g i) (@chunkStartSmall n k hk hkn _ g i) : ℚ) + 1)
        =
      expectedCost n (fun g =>
          (adjustedCost k (@chunkColoring n k hk hkn _ c g i) (@chunkStartSmall n k hk hkn _ g i) : ℚ)) + 1 := by
    simp [expectedCost_add, expectedCost_const]
  -- 3) plug in your “expected adjustedCost ≤ fhat” lemma
  have hadj :
      expectedCost n (fun g =>
          (adjustedCost k (@chunkColoring n k hk hkn _ c g i) (@chunkStartSmall n k hk hkn _ g i) : ℚ))
        ≤ fhat k := by
    exact expected_adjustedCost_le_fhat n k hk hkn c i
  -- finish
  calc
    expectedCost n (fun g => chunkContributionG hk hkn c i g)
        ≤ expectedCost n (fun g =>
            (adjustedCost k (@chunkColoring n k hk hkn _ c g i) (@chunkStartSmall n k hk hkn _ g i) : ℚ) + 1) := hmono
    _ = expectedCost n (fun g =>
            (adjustedCost k (@chunkColoring n k hk hkn _ c g i) (@chunkStartSmall n k hk hkn _ g i) : ℚ)) + 1 := hadd
    _ ≤ fhat k + 1 := by
      linarith [hadj]

theorem lemma8
  (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (c : Coloring n) :
  expectedCost n (fun g => (algoCost (n:=n) (k:=k) hk hkn c g : ℚ))
    ≤ (numChunks n k : ℚ) * (fhat k + 1) + (remSteps n k : ℚ) := by
  classical
  -- Step 1: bound algoCost pointwise by the sum of chunk contributions
  have hle :
      ∀ g, (algoCost (n := n) (k := k) hk hkn c g : ℚ)
        ≤ (∑ i : Fin (numChunks n k), chunkContributionG hk hkn c i g)
          + (remSteps n k : ℚ) := by
    intro g
    exact algoCost_le_sum_chunkContributionG_add_remSteps n k hk hkn c g
  -- Step 2: Use monotonicity of expectation
  apply le_trans (expectedCost_mono (n := n) hle)
  -- Step 3: Linearity of expectation
  rw [expectedCost_add]
  rw [expectedCost_sum_fin]
  -- Step 4: bound each chunk expectation by fhat k + 1
  have hchunks :
      (∑ i : Fin (numChunks n k),
          expectedCost n (fun g => chunkContributionG hk hkn c i g))
        ≤
      (∑ _i : Fin (numChunks n k), (fhat k + 1)) := by
    refine Finset.sum_le_sum ?_
    intro i _
    exact expected_chunkContribution_le_fhat_add_one n k hk hkn c i
  -- Step 5: simplify RHS sum of constants to `numChunks * (fhat + 1)`
  have hconst :
      (∑ _i : Fin (numChunks n k), (fhat k + 1))
        = (numChunks n k : ℚ) * (fhat k + 1) := by
    simp
    linarith
  -- Step 6: finish
  simp only [expectedCost_const]
  linarith [hchunks, hconst]

-- Computational input (Lemma 9 in the paper).
axiom fhat6_eq_0_875 : fhat 6 = (0.875 : ℚ)

/-- Theorem 6 specialized bound on the expected number of color changes (for `k = 6`). -/
theorem theorem6_expected
  (n : ℕ) (hn : 6 ≤ n) (c : Coloring n) :
  expectedCost n (fun g => (algoCost (n := n) (k := 6) (by decide) hn c g : ℚ))
    ≤ (5 / 16 : ℚ) * n + 6 := by
  have h8 :=
    lemma8 n 6 (by decide) hn c
  have hf : fhat 6 + 1 = (15 / 8 : ℚ) := by
    calc
      fhat 6 + 1 = (0.875 : ℚ) + 1 := by rw [fhat6_eq_0_875]
      _ = (15 / 8 : ℚ) := by norm_num
  have h8' :
      expectedCost n (fun g => (algoCost (n := n) (k := 6) (by decide) hn c g : ℚ))
        ≤ (numChunks n 6 : ℚ) * (15 / 8 : ℚ) + (remSteps n 6 : ℚ) := by
    simpa [hf] using h8
  have hmain :
      (numChunks n 6 : ℚ) * (15 / 8 : ℚ) ≤ (5 / 16 : ℚ) * n := by
    have hmulNat : numChunks n 6 * 6 ≤ n := by
      simpa [numChunks] using (Nat.div_mul_le_self n 6)
    have hmulQ : ((numChunks n 6 * 6 : ℕ) : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast hmulNat
    have hmulQ' :
        (5 / 16 : ℚ) * ((numChunks n 6 * 6 : ℕ) : ℚ)
          ≤ (5 / 16 : ℚ) * (n : ℚ) :=
      mul_le_mul_of_nonneg_left hmulQ (by norm_num)
    have hrewrite :
        (numChunks n 6 : ℚ) * (15 / 8 : ℚ)
          = (5 / 16 : ℚ) * ((numChunks n 6 * 6 : ℕ) : ℚ) := by
      calc
        (numChunks n 6 : ℚ) * (15 / 8 : ℚ)
            = (numChunks n 6 : ℚ) * ((6 : ℚ) * (5 / 16 : ℚ)) := by norm_num
        _ = ((numChunks n 6 : ℚ) * (6 : ℚ)) * (5 / 16 : ℚ) := by ring
        _ = ((numChunks n 6 * 6 : ℕ) : ℚ) * (5 / 16 : ℚ) := by
              norm_num [Nat.cast_mul]
        _ = (5 / 16 : ℚ) * ((numChunks n 6 * 6 : ℕ) : ℚ) := by ring
    calc
      (numChunks n 6 : ℚ) * (15 / 8 : ℚ)
          = (5 / 16 : ℚ) * ((numChunks n 6 * 6 : ℕ) : ℚ) := hrewrite
      _ ≤ (5 / 16 : ℚ) * (n : ℚ) := hmulQ'
  have hrem : (remSteps n 6 : ℚ) ≤ 6 := by
    have hremNat : remSteps n 6 ≤ 6 := by
      unfold remSteps
      have hlt : n % 6 < 6 := Nat.mod_lt n (by decide)
      omega
    exact_mod_cast hremNat
  calc
    expectedCost n (fun g => (algoCost (n := n) (k := 6) (by decide) hn c g : ℚ))
        ≤ (numChunks n 6 : ℚ) * (15 / 8 : ℚ) + (remSteps n 6 : ℚ) := h8'
    _ ≤ (5 / 16 : ℚ) * n + 6 := by
      linarith [hmain, hrem]

/-- Theorem 6 (existence form) from the expected bound. -/
theorem theorem6
  (n : ℕ) (hn : 6 ≤ n) (c : Coloring n) :
  ∃ g : AntiGeoData n,
    (algoCost (n := n) (k := 6) (by decide) hn c g : ℚ)
      ≤ (5 / 16 : ℚ) * n + 6 := by
  classical
  let B : ℚ := (5 / 16 : ℚ) * n + 6
  let X : AntiGeoData n → ℚ :=
    fun g => (algoCost (n := n) (k := 6) (by decide) hn c g : ℚ)
  have hExp : expectedCost n X ≤ B := by
    simpa [B, X] using theorem6_expected n hn c
  by_contra hnone
  have hall : ∀ g : AntiGeoData n, B < X g := by
    intro g
    by_contra hgt
    have hle : X g ≤ B := le_of_not_gt hgt
    exact hnone ⟨g, by simpa [X, B] using hle⟩
  have hltWitness :
      ∃ g ∈ (Finset.univ : Finset (AntiGeoData n)), (fun _ : AntiGeoData n => B) g < X g := by
    rcases antiGeoData_nonempty n with ⟨g0⟩
    have hg0 : g0 ∈ (Finset.univ : Finset (AntiGeoData n)) := by simp
    exact ⟨g0, hg0, hall g0⟩
  have hsumLt :
      (∑ g : AntiGeoData n, (fun _ : AntiGeoData n => B) g)
        < ∑ g : AntiGeoData n, X g := by
    exact Finset.sum_lt_sum (s := Finset.univ)
      (hle := by intro g hg; exact le_of_lt (hall g))
      (hlt := hltWitness)
  have hcardPos : (0 : ℚ) < (Fintype.card (AntiGeoData n) : ℚ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (antiGeoData_nonempty n))
  have hcardNe : (Fintype.card (AntiGeoData n) : ℚ) ≠ 0 := ne_of_gt hcardPos
  have hExpLower :
      B < expectedCost n X := by
    unfold expectedCost
    have hdiv := div_lt_div_of_pos_right hsumLt hcardPos
    simpa [Finset.sum_const, nsmul_eq_mul, hcardNe] using hdiv
  exact (not_lt_of_ge hExp) hExpLower

private lemma applyOrder_coord_eq_start_of_not_mem
  {n : ℕ} (start : Vertex n) (coords : List (Fin n)) (x : Fin n)
  (hnot : ∀ i ∈ coords, i ≠ x) :
  (applyOrder start coords) x = start x := by
  induction coords generalizing start with
  | nil =>
      simp [applyOrder]
  | cons i t ih =>
      have hix : i ≠ x := hnot i (by simp)
      have hxi : x ≠ i := fun hx => hix hx.symm
      have hnotTail : ∀ j ∈ t, j ≠ x := by
        intro j hj
        exact hnot j (by simp [hj])
      calc
        (applyOrder start (i :: t)) x
            = (applyOrder (flipCoord i start) t) x := by
                simp [applyOrder]
        _ = (flipCoord i start) x := ih (start := flipCoord i start) hnotTail
        _ = start x := by simp [flipCoord, hxi]

private lemma applyOrder_ofFn_perm_eq_antipode
  {n : ℕ} (start : Vertex n) (σ : Equiv.Perm (Fin n)) :
  applyOrder start (List.ofFn σ) = antipode start := by
  ext x
  have hxmem : x ∈ List.ofFn σ := by
    rw [List.mem_ofFn]
    exact ⟨σ.symm x, by simp⟩
  have hnodup : (List.ofFn σ).Nodup := by
    exact (List.nodup_ofFn (f := σ)).2 σ.injective
  have hperm : List.Perm (List.ofFn σ) (x :: (List.ofFn σ).erase x) :=
    List.perm_cons_erase hxmem
  letI : RightCommutative (fun v : Vertex n => fun i : Fin n => flipCoord i v) :=
    flipCoord_right_comm
  have happly :
      applyOrder start (List.ofFn σ)
        = applyOrder start (x :: (List.ofFn σ).erase x) := by
    unfold applyOrder
    exact hperm.foldl_eq _
  have hnotRest : ∀ j ∈ (List.ofFn σ).erase x, j ≠ x := by
    intro j hj
    exact (List.Nodup.mem_erase_iff (d := hnodup)).1 hj |>.1
  calc
    (applyOrder start (List.ofFn σ)) x
        = (applyOrder start (x :: (List.ofFn σ).erase x)) x := by
            simp [happly]
    _ = (applyOrder (flipCoord x start) ((List.ofFn σ).erase x)) x := by
          simp [applyOrder]
    _ = (flipCoord x start) x :=
          applyOrder_coord_eq_start_of_not_mem
            (start := flipCoord x start) (coords := (List.ofFn σ).erase x) (x := x) hnotRest
    _ = ! start x := by simp [flipCoord]
    _ = (antipode start) x := rfl

private lemma applyOrder_boundary_then_suffix_eq_antipode
  (n : ℕ) (g : AntiGeoData n) :
  applyOrder (vertsNat g.start g.perm (6 * numChunks n 6))
      ((List.ofFn g.perm).drop (6 * numChunks n 6))
    = antipode g.start := by
  let l1 : List (Fin n) := (List.ofFn g.perm).take (6 * numChunks n 6)
  let l2 : List (Fin n) := (List.ofFn g.perm).drop (6 * numChunks n 6)
  have hkm : 6 * numChunks n 6 ≤ n := by
    simpa [numChunks, Nat.mul_comm] using (Nat.div_mul_le_self n 6)
  have hstart : applyOrder g.start l1 = vertsNat g.start g.perm (6 * numChunks n 6) := by
    have htake :=
      vertsNatLen_eq_applyOrder_take
        (n := n) (ℓ := n) g.start g.perm (6 * numChunks n 6) hkm
    calc
      applyOrder g.start l1
          = vertsNatLen g.start g.perm (6 * numChunks n 6) := by
              simpa [l1] using htake.symm
      _ = vertsNat g.start g.perm (6 * numChunks n 6) := by
            simpa using (vertsNat_eq_vertsNatLen (start := g.start) (coord := g.perm) (6 * numChunks n 6)).symm
  have happ :
      applyOrder (applyOrder g.start l1) l2
        = applyOrder g.start (l1 ++ l2) := by
    unfold applyOrder
    simp [List.foldl_append]
  calc
    applyOrder (vertsNat g.start g.perm (6 * numChunks n 6))
        ((List.ofFn g.perm).drop (6 * numChunks n 6))
        = applyOrder (applyOrder g.start l1) l2 := by
            simp [hstart, l2]
    _ = applyOrder g.start (l1 ++ l2) := happ
    _ = applyOrder g.start (List.ofFn g.perm) := by
          simp [l1, l2, List.take_append_drop]
    _ = antipode g.start := applyOrder_ofFn_perm_eq_antipode (start := g.start) (σ := g.perm)

private lemma applyOrder_algorithm1FinalCoords_eq_antipode
  (n : ℕ) (hn : 6 ≤ n) (c : Coloring n) (g : AntiGeoData n) :
  applyOrder g.start (algorithm1FinalCoords (n := n) (k := 6) (by decide) hn c g)
    = antipode g.start := by
  unfold algorithm1FinalCoords
  have happ :
      applyOrder g.start
          ((algorithm1ChunkCoords (n := n) (k := 6) (by decide) hn c g)
            ++ (List.ofFn g.perm).drop ((numChunks n 6) * 6))
        = applyOrder
            (applyOrder g.start (algorithm1ChunkCoords (n := n) (k := 6) (by decide) hn c g))
            ((List.ofFn g.perm).drop ((numChunks n 6) * 6)) := by
    unfold applyOrder
    simp [List.foldl_append]
  have hboundary :
      applyOrder g.start (algorithm1ChunkCoords (n := n) (k := 6) (by decide) hn c g)
        = vertsNat g.start g.perm (6 * numChunks n 6) := by
    simpa [Nat.mul_comm] using
      (applyOrder_algorithm1ChunkCoords_eq_chunkBoundaryEnd
        (n := n) (k := 6) (by decide) hn c g)
  calc
    applyOrder g.start
        ((algorithm1ChunkCoords (n := n) (k := 6) (by decide) hn c g)
          ++ (List.ofFn g.perm).drop ((numChunks n 6) * 6))
      = applyOrder
          (applyOrder g.start (algorithm1ChunkCoords (n := n) (k := 6) (by decide) hn c g))
          ((List.ofFn g.perm).drop ((numChunks n 6) * 6)) := happ
    _ = applyOrder (vertsNat g.start g.perm (6 * numChunks n 6))
          ((List.ofFn g.perm).drop ((numChunks n 6) * 6)) := by rw [hboundary]
    _ = antipode g.start := by
          simpa [Nat.mul_comm] using applyOrder_boundary_then_suffix_eq_antipode n g

/--
Paper-style wrapper of Theorem 6 (path form):
for every `n ≥ 6` and coloring `c`, there exists a vertex `v`
and a path from `v` to `antipode v` with at most `(5/16) * n + 6` color changes.
-/
theorem theorem6_wrapper
  (n : ℕ) (hn : 6 ≤ n) (c : Coloring n) :
  ∃ v : Vertex n, ∃ ℓ : ℕ, ∃ p : GeoPath n ℓ,
    p.verts ⟨0, Nat.succ_pos ℓ⟩ = v ∧
    p.verts ⟨ℓ, Nat.lt_succ_self ℓ⟩ = antipode v ∧
    (p.colorChanges c : ℚ) ≤ (5 / 16 : ℚ) * n + 6 := by
  rcases theorem6 n hn c with ⟨g, hg⟩
  let coords : List (Fin n) :=
    @algorithm1FinalCoords n 6 (by decide) hn (instDecidableEqFin n) c g
  let p : GeoPath n coords.length :=
    GeoPath.ofCoordFnLen (n := n) (ℓ := coords.length) g.start
      (fun i : Fin coords.length => coords[i])
  have hstart : p.verts ⟨0, Nat.succ_pos _⟩ = g.start := by
    simp [p, coords, GeoPath.ofCoordFnLen, vertsNatLen]
  have hendApply : p.verts ⟨coords.length, Nat.lt_succ_self _⟩ = applyOrder g.start coords := by
    have hcore :=
      vertsNatLen_eq_applyOrder
        (n := n) (ℓ := coords.length) g.start (fun i : Fin coords.length => coords[i])
    simpa [p, coords, GeoPath.ofCoordFnLen] using hcore
  have hendCoords : applyOrder g.start coords = antipode g.start := by
    simpa [coords] using
      (applyOrder_algorithm1FinalCoords_eq_antipode n hn c g)
  have hend : p.verts ⟨coords.length, Nat.lt_succ_self _⟩ = antipode g.start :=
    hendApply.trans hendCoords
  have hcostNat : p.colorChanges c = algoCost (n := n) (k := 6) (by decide) hn c g := by
    -- set_option maxHeartbeats 100000 in
    unfold algoCost changesFromOrder edgeColorsFromOrder GeoPath.colorChanges
    rfl
  have hcostQ : (p.colorChanges c : ℚ) = (algoCost (n := n) (k := 6) (by decide) hn c g : ℚ) := by
    exact_mod_cast hcostNat
  have hbound : (p.colorChanges c : ℚ) ≤ (5 / 16 : ℚ) * n + 6 := by
    calc
      (p.colorChanges c : ℚ)
          = (algoCost (n := n) (k := 6) (by decide) hn c g : ℚ) := hcostQ
      _ ≤ (5 / 16 : ℚ) * n + 6 := hg
  exact ⟨g.start, coords.length, p, hstart, hend, hbound⟩

end Algo1

end NorinLemma8
