import NorinVerification.NorinCNF
import NorinVerification.NorinSimplified
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Bitwise
import Mathlib.InformationTheory.Hamming
import Mathlib.Order.Preorder.Finite

namespace NorinCNF
namespace SymmetryBreaking

/--
Geodesic-counterexample predicate used in the `Ψ_n` completeness and lifting statements.
-/
def NoMonochromaticAntipodalGeodesic (n : Nat) (c : EdgeColoring n) : Prop :=
  ∀ v : Vertex n, ∀ p : (ThreeColorSAT.Hypercube.Q n).Walk v (antipode v),
    p.length = dist v (antipode v) → ¬ WalkMonochromatic c p

private lemma lexCode_eq_ofDigits_reverse_digits {n : Nat} (v : Vertex n) :
    lexCode v = Nat.ofDigits 2 (((List.finRange n).map (fun i => if v i then 1 else 0)).reverse) := by
  unfold lexCode
  have hmap :=
    (List.foldl_map
      (f := fun i : Fin n => (if v i then 1 else 0))
      (g := fun acc x : Nat => 2 * acc + x)
      (l := List.finRange n) (init := 0)).symm
  have hfold :=
    (List.foldl_eq_foldr_reverse
      (l := (List.finRange n).map (fun i => if v i then 1 else 0))
      (f := fun acc x : Nat => 2 * acc + x) (b := 0))
  calc
    List.foldl (fun acc i => 2 * acc + (if v i then 1 else 0)) 0 (List.finRange n)
        = List.foldl (fun acc x : Nat => 2 * acc + x) 0
            ((List.finRange n).map (fun i => if v i then 1 else 0)) := by simpa using hmap
    _ = List.foldr (fun x y => 2 * y + x) 0
            (((List.finRange n).map (fun i => if v i then 1 else 0)).reverse) := by
              simpa using hfold
    _ = List.foldr (fun x y => x + 2 * y) 0
            (((List.finRange n).map (fun i => if v i then 1 else 0)).reverse) := by
          simp [Nat.add_comm]
    _ = Nat.ofDigits 2 (((List.finRange n).map (fun i => if v i then 1 else 0)).reverse) := by
          simpa [Nat.ofDigits_eq_foldr]

private lemma map_bits_eq_implies_eq {n : Nat} {u v : Vertex n}
    (h : (List.finRange n).map (fun i => if u i then 1 else 0)
      = (List.finRange n).map (fun i => if v i then 1 else 0)) : u = v := by
  funext i
  have hget := congrArg (fun l => l[i.1]?) h
  simp at hget
  cases hu : u i <;> cases hv : v i <;> simp [hu, hv] at hget ⊢

private lemma lexCode_injective {n : Nat} : Function.Injective (@lexCode n) := by
  intro u v hEq
  have hdigitsEq :
      ((List.finRange n).map (fun i => if u i then 1 else 0)).reverse =
      ((List.finRange n).map (fun i => if v i then 1 else 0)).reverse := by
    apply Nat.ofDigits_inj_of_len_eq (b := 2) (hb := by decide)
    · simp
    · intro d hd
      have hd' : d = 0 ∨ d = 1 := by
        have := List.mem_map.1 (List.mem_reverse.1 hd)
        rcases this with ⟨i, _hi, rfl⟩
        by_cases hbi : u i
        · right; simp [hbi]
        · left; simp [hbi]
      omega
    · intro d hd
      have hd' : d = 0 ∨ d = 1 := by
        have := List.mem_map.1 (List.mem_reverse.1 hd)
        rcases this with ⟨i, _hi, rfl⟩
        by_cases hbi : v i
        · right; simp [hbi]
        · left; simp [hbi]
      omega
    · simpa [lexCode_eq_ofDigits_reverse_digits] using hEq
  have hmapEq :
      (List.finRange n).map (fun i => if u i then 1 else 0) =
      (List.finRange n).map (fun i => if v i then 1 else 0) := by
    simpa using congrArg List.reverse hdigitsEq
  exact map_bits_eq_implies_eq hmapEq

private lemma orderedPair_comm {n : Nat} (u v : Vertex n) : orderedPair u v = orderedPair v u := by
  unfold orderedPair
  by_cases huv : lexCode u ≤ lexCode v
  · by_cases hvu : lexCode v ≤ lexCode u
    · have heq : u = v := lexCode_injective (le_antisymm huv hvu)
      subst heq
      simp
    · simp [huv, hvu]
  · by_cases hvu : lexCode v ≤ lexCode u
    · simp [huv, hvu]
    · exfalso
      exact huv (le_of_not_ge hvu)

private lemma rLiteral_comm {n : Nat} (u v : Vertex n) : rLiteral u v = rLiteral v u := by
  unfold rLiteral
  rw [orderedPair_comm (u := u) (v := v)]

@[simp] private lemma antipode_antipode {n : Nat} (v : Vertex n) : antipode (antipode v) = v := by
  funext i
  simp [antipode]

private def bitDigits {n : Nat} (v : Vertex n) : List Nat :=
  ((List.finRange n).map (fun i => if v i then 1 else 0)).reverse

private lemma bitDigits_mem_lt_two {n : Nat} (v : Vertex n) :
    ∀ d ∈ bitDigits v, d < 2 := by
  intro d hd
  unfold bitDigits at hd
  have hrev : d ∈ (List.finRange n).map (fun i => if v i then 1 else 0) := List.mem_reverse.1 hd
  rcases List.mem_map.1 hrev with ⟨i, _hi, rfl⟩
  by_cases h : v i <;> simp [h]

private lemma bitDigits_antipode {n : Nat} (v : Vertex n) :
    bitDigits (antipode v) = (bitDigits v).map (fun d => 1 - d) := by
  have hfun :
      (fun i => if !v i then 1 else 0) = (fun i => 1 - (if v i then 1 else 0)) := by
    funext i
    by_cases h : v i
    · simp [h]
    · simp [h]
  unfold bitDigits antipode
  rw [hfun]
  simp [List.map_reverse, List.map_map]

private lemma ofDigits_complement_bits (L : List Nat)
    (hLt : ∀ d ∈ L, d < 2) :
    Nat.ofDigits 2 (L.map (fun d => 1 - d)) = 2 ^ L.length - 1 - Nat.ofDigits 2 L := by
  induction L with
  | nil =>
      simp
  | cons d t ih =>
      have hdlt : d < 2 := hLt d (by simp)
      have ht : ∀ x ∈ t, x < 2 := by
        intro x hx
        exact hLt x (by simp [hx])
      have hbound : Nat.ofDigits 2 t < 2 ^ t.length :=
        Nat.ofDigits_lt_base_pow_length (b := 2) (hb := by decide) ht
      interval_cases d
      · simp [Nat.ofDigits, ih ht]
        omega
      · simp [Nat.ofDigits, ih ht]
        omega

private lemma lexCode_ofDigits_bitDigits {n : Nat} (v : Vertex n) :
    lexCode v = Nat.ofDigits 2 (bitDigits v) := by
  simpa [bitDigits] using lexCode_eq_ofDigits_reverse_digits (v := v)

private lemma lexCode_antipode_formula {n : Nat} (v : Vertex n) :
    lexCode (antipode v) = 2 ^ n - 1 - lexCode v := by
  rw [lexCode_ofDigits_bitDigits (v := antipode v), bitDigits_antipode,
    ofDigits_complement_bits (L := bitDigits v) (bitDigits_mem_lt_two v),
    lexCode_ofDigits_bitDigits (v := v)]
  simp [bitDigits]

private lemma lexCode_lt_pow {n : Nat} (v : Vertex n) : lexCode v < 2 ^ n := by
  rw [lexCode_ofDigits_bitDigits]
  simpa [bitDigits] using
    Nat.ofDigits_lt_base_pow_length (b := 2) (hb := by decide) (bitDigits_mem_lt_two v)

private lemma lexCode_antipode_antitone {n : Nat} {u v : Vertex n} (h : lexCode u ≤ lexCode v) :
    lexCode (antipode v) ≤ lexCode (antipode u) := by
  have hu : lexCode u < 2 ^ n := lexCode_lt_pow u
  have hv : lexCode v < 2 ^ n := lexCode_lt_pow v
  rw [lexCode_antipode_formula, lexCode_antipode_formula]
  omega

private lemma orderedPair_antipode_swap {n : Nat} (u v : Vertex n) :
    orderedPair (antipode u) (antipode v) =
      (antipode (orderedPair u v).2, antipode (orderedPair u v).1) := by
  unfold orderedPair
  by_cases huv : lexCode u ≤ lexCode v
  · have hanti : lexCode (antipode v) ≤ lexCode (antipode u) :=
      lexCode_antipode_antitone (u := u) (v := v) huv
    by_cases hanti' : lexCode (antipode u) ≤ lexCode (antipode v)
    · have hEqLex : lexCode (antipode u) = lexCode (antipode v) := le_antisymm hanti' hanti
      have hEqAnti : antipode u = antipode v := lexCode_injective hEqLex
      have hEq : u = v := by
        have htmp := congrArg (fun x => antipode x) hEqAnti
        simpa using htmp
      subst hEq
      simp
    · simp [huv, hanti']
  · have hvu : lexCode v ≤ lexCode u := le_of_not_ge huv
    have hanti : lexCode (antipode u) ≤ lexCode (antipode v) :=
      lexCode_antipode_antitone (u := v) (v := u) hvu
    by_cases hanti' : lexCode (antipode v) ≤ lexCode (antipode u)
    · have hEqLex : lexCode (antipode u) = lexCode (antipode v) := le_antisymm hanti hanti'
      have hEqAnti : antipode u = antipode v := lexCode_injective hEqLex
      have hEq : u = v := by
        have htmp := congrArg (fun x => antipode x) hEqAnti
        simpa using htmp
      subst hEq
      simp
    · simp [huv, hanti]

private lemma orderedPair_adj {n : Nat} {u v : Vertex n} (hAdj : Adj u v) :
    Adj (orderedPair u v).1 (orderedPair u v).2 := by
  unfold orderedPair
  split_ifs
  · simpa [Adj] using hAdj
  · simpa [Adj] using hAdj.symm

private lemma adj_not_antipode_left {n : Nat} (hDim : 2 ≤ n) {u v : Vertex n} (hAdj : Adj u v) :
    v ≠ antipode u := by
  intro hEq
  have hDist1 : dist u v = 1 := by simpa [dist, Adj, ThreeColorSAT.Hypercube.Q] using hAdj
  have hDistN : dist u v = n := by simpa [hEq] using dist_antipode u
  omega

private lemma rLiteral_antipode_neg_of_adj {n : Nat} (hDim : 2 ≤ n)
    {u v : Vertex n} (hAdj : Adj u v) :
    rLiteral (antipode u) (antipode v) = litNeg (rLiteral u v) := by
  let p : Vertex n × Vertex n := orderedPair u v
  let a : Vertex n := p.1
  let b : Vertex n := p.2
  have hpair : orderedPair (antipode u) (antipode v) = (antipode b, antipode a) := by
    simpa [p, a, b] using orderedPair_antipode_swap (u := u) (v := v)
  have hAdjAB : Adj a b := by
    simpa [p, a, b] using orderedPair_adj (u := u) (v := v) hAdj
  have hNotEq : a ≠ antipode b := by
    intro hEq
    have hb : b = antipode a := by
      have htmp := congrArg (fun x => antipode x) hEq
      simpa using htmp.symm
    exact adj_not_antipode_left (hDim := hDim) (u := a) (v := b) hAdjAB hb
  have hLexNe : lexCode a ≠ lexCode (antipode b) := by
    intro hEq
    exact hNotEq (lexCode_injective hEq)
  unfold rLiteral litNeg
  by_cases hcond : lexCode (antipode (orderedPair u v).2) < lexCode (orderedPair u v).1
  · have hle : lexCode (antipode (orderedPair u v).2) ≤ lexCode (orderedPair u v).1 := le_of_lt hcond
    have hcond' : ¬ lexCode (orderedPair u v).1 < lexCode (antipode (orderedPair u v).2) :=
      not_lt_of_ge hle
    simp [hpair, p, a, b, hcond, hcond', hle]
  · have hle : lexCode (orderedPair u v).1 ≤ lexCode (antipode (orderedPair u v).2) := le_of_not_gt hcond
    have hcond' : lexCode (orderedPair u v).1 < lexCode (antipode (orderedPair u v).2) :=
      lt_of_le_of_ne hle (by simpa [p, a, b] using hLexNe)
    simp [hpair, p, a, b, hcond, hcond', hle]

noncomputable def litSatBool {n : Nat} (τ : CNF.Assignment (Var n))
    (l : CNF.Lit (Var n)) : Bool := by
  classical
  exact if CNF.Lit.Sat τ l then true else false

private lemma litSatBool_eq_true_iff {n : Nat} (τ : CNF.Assignment (Var n))
    (l : CNF.Lit (Var n)) :
    litSatBool τ l = true ↔ CNF.Lit.Sat τ l := by
  classical
  unfold litSatBool
  by_cases h : CNF.Lit.Sat τ l <;> simp [h]

private lemma litSatBool_neg {n : Nat} (τ : CNF.Assignment (Var n)) (l : CNF.Lit (Var n)) :
    litSatBool τ (litNeg l) = !(litSatBool τ l) := by
  classical
  by_cases h : CNF.Lit.Sat τ l
  · simp [litSatBool, litNeg_sat_iff_not_sat, h]
  · simp [litSatBool, litNeg_sat_iff_not_sat, h]

noncomputable def coloringOfAssignment {n : Nat}
    (τ : CNF.Assignment (Var n)) : EdgeColoring n := by
  classical
  exact Sym2.lift ⟨fun u v => litSatBool τ (rLiteral u v), by
    intro u v
    simp [rLiteral_comm (u := u) (v := v)]⟩

@[simp] lemma coloringOfAssignment_edgeOf {n : Nat}
    (τ : CNF.Assignment (Var n)) (u v : Vertex n) :
    coloringOfAssignment τ (edgeOf u v) = litSatBool τ (rLiteral u v) := by
  classical
  simp [coloringOfAssignment, edgeOf]

private lemma coloringOfAssignment_isAntipodal {n : Nat} (hDim : 2 ≤ n)
    (τ : CNF.Assignment (Var n)) :
    IsAntipodalColoring (coloringOfAssignment τ) := by
  intro u v hAdj
  rw [coloringOfAssignment_edgeOf, coloringOfAssignment_edgeOf]
  rw [rLiteral_antipode_neg_of_adj (hDim := hDim) hAdj, litSatBool_neg]
  cases h : litSatBool τ (rLiteral u v) <;> simp [h]

private lemma testBit_ofDigits_boolList (L : List Bool) (i : Nat) :
    (Nat.ofDigits 2 (L.map Bool.toNat)).testBit i = L.getI i := by
  induction L generalizing i with
  | nil =>
      cases i <;> simp
  | cons b t ih =>
      cases b with
      | false =>
          cases i with
          | zero =>
              simp [Nat.ofDigits]
          | succ i =>
              let m := Nat.ofDigits 2 (t.map Bool.toNat)
              have htb : (2 * m).testBit (i + 1) = m.testBit i := by
                simpa [m, Nat.bit_false_apply] using (Nat.testBit_bit_succ i false m)
              calc
                (Nat.ofDigits 2 (Bool.false.toNat :: t.map Bool.toNat)).testBit (i + 1)
                    = (2 * m).testBit (i + 1) := by simp [Nat.ofDigits, m]
                _ = m.testBit i := htb
                _ = t.getI i := ih i
                _ = (Bool.false :: t).getI (i + 1) := by simp
      | true =>
          cases i with
          | zero =>
              simp [Nat.ofDigits]
          | succ i =>
              let m := Nat.ofDigits 2 (t.map Bool.toNat)
              have htb : (1 + 2 * m).testBit (i + 1) = m.testBit i := by
                simpa [m, Nat.bit_true_apply, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                  using (Nat.testBit_bit_succ i true m)
              calc
                (Nat.ofDigits 2 (Bool.true.toNat :: t.map Bool.toNat)).testBit (i + 1)
                    = (1 + 2 * m).testBit (i + 1) := by simp [Nat.ofDigits, m]
                _ = m.testBit i := htb
                _ = t.getI i := ih i
                _ = (Bool.true :: t).getI (i + 1) := by simp

private lemma natToVertex_ofBoolDigits {n : Nat} (v : Vertex n) :
    natToVertex n (Nat.ofDigits 2 (((List.finRange n).map (fun i => v i)).map Bool.toNat)) = v := by
  funext i
  have hget : ((List.finRange n).map (fun j => v j)).getI i.1 = v i := by
    simpa [List.getI_eq_getElem, i.2] using
      List.getElem_map (f := fun j => v j) (l := List.finRange n) ⟨i.1, i.2⟩
  calc
    natToVertex n (Nat.ofDigits 2 (((List.finRange n).map (fun i => v i)).map Bool.toNat)) i
        = ((List.finRange n).map (fun j => v j)).getI i.1 := by
            simpa [natToVertex] using
              testBit_ofDigits_boolList (((List.finRange n).map (fun j => v j))) i.1
    _ = v i := hget

private lemma ofDigits_testBit_range_eq_of_lt_pow (n u : Nat) (hu : u < 2 ^ n) :
    Nat.ofDigits 2 (((List.range n).map (fun i => Nat.testBit u i)).map Bool.toNat) = u := by
  let bits : List Bool := (List.range n).map (fun i => Nat.testBit u i)
  let m : Nat := Nat.ofDigits 2 (bits.map Bool.toNat)
  have hmLt : m < 2 ^ n := by
    have hraw : m < 2 ^ (bits.map Bool.toNat).length := by
      dsimp [m]
      exact Nat.ofDigits_lt_base_pow_length (b := 2) (hb := by decide)
        (by
          intro d hd
          rcases List.mem_map.mp hd with ⟨(b : Bool), _hb, rfl⟩
          cases b <;> decide)
    simpa [bits, List.length_map] using hraw
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have hget : bits.getI i = Nat.testBit u i := by
      unfold bits
      simp [List.getI_eq_getElem, hi]
    calc
      m.testBit i = bits.getI i := by
        simpa [m] using
          testBit_ofDigits_boolList bits i
      _ = Nat.testBit u i := hget
  · have hni : n ≤ i := le_of_not_gt hi
    have hpow : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hni
    have hmBit : m.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hmLt hpow)
    have huBit : u.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hu hpow)
    change m.testBit i = u.testBit i
    rw [huBit]
    exact hmBit

private lemma natToVertex_antipodeCode_eq_antipode_of_lt_pow (n u : Nat) (hu : u < 2 ^ n) :
    natToVertex n (antipodeCode n u) = antipode (natToVertex n u) := by
  let bits : List Bool := (List.range n).map (fun i => Nat.testBit u i)
  have hBitsVal :
      Nat.ofDigits 2 (bits.map Bool.toNat) = u := by
    simpa [bits] using ofDigits_testBit_range_eq_of_lt_pow (n := n) (u := u) hu
  have hComplement :
      Nat.ofDigits 2 ((bits.map Bool.toNat).map (fun d => 1 - d)) = antipodeCode n u := by
    calc
      Nat.ofDigits 2 ((bits.map Bool.toNat).map (fun d => 1 - d))
          = 2 ^ n - 1 - Nat.ofDigits 2 (bits.map Bool.toNat) := by
              simpa [bits] using
                ofDigits_complement_bits (L := bits.map Bool.toNat)
                  (by
                    intro d hd
                    rcases List.mem_map.mp hd with ⟨b, _hb, rfl⟩
                    cases b <;> decide)
      _ = 2 ^ n - 1 - u := by rw [hBitsVal]
      _ = antipodeCode n u := rfl
  have hMapNot :
      (bits.map Bool.toNat).map (fun d => 1 - d) = (bits.map (fun b => !b)).map Bool.toNat := by
    have hFun :
        (fun b : Bool => 1 - Bool.toNat b) = (fun b : Bool => Bool.toNat (!b)) := by
      funext b
      cases b <;> simp
    simpa [List.map_map, hFun, Function.comp] using
      (rfl : bits.map ((fun d => 1 - d) ∘ Bool.toNat) = bits.map (Bool.toNat ∘ fun b => !b))
  funext j
  have hlenBits : bits.length = n := by
    unfold bits
    simp
  have hgetBits : bits.getI j.1 = Nat.testBit u j.1 := by
    unfold bits
    simpa [List.getI_eq_getElem, j.2] using
      List.getElem_map (f := fun i => Nat.testBit u i) (l := List.range n) ⟨j.1, by simpa using j.2⟩
  calc
    natToVertex n (antipodeCode n u) j
        = natToVertex n (Nat.ofDigits 2 (((bits.map Bool.toNat).map (fun d => 1 - d)))) j := by
            rw [← hComplement]
    _ = ((bits.map (fun b => !b)).getI j.1) := by
          rw [hMapNot]
          simpa [natToVertex] using
            testBit_ofDigits_boolList (bits.map (fun b => !b)) j.1
    _ = !(bits.getI j.1) := by
          simpa [List.getI_eq_getElem, hlenBits, j.2] using
            List.getElem_map (f := fun b => !b) (l := bits) ⟨j.1, by simpa [hlenBits] using j.2⟩
    _ = !(Nat.testBit u j.1) := by rw [hgetBits]
    _ = antipode (natToVertex n u) j := by rfl

private lemma ofDigits_boolDigits_lt_pow_mapLength (L : List Bool) :
    Nat.ofDigits 2 (L.map Bool.toNat) < 2 ^ (L.map Bool.toNat).length := by
  exact Nat.ofDigits_lt_base_pow_length (b := 2) (hb := by decide)
    (by
      intro d hd
      rcases (List.mem_map.mp hd) with ⟨(b : Bool), hb, rfl⟩
      cases b <;> decide)

private lemma mem_allVertices {n : Nat} (v : Vertex n) : v ∈ allVertices n := by
  let digits := (List.finRange n).map (fun i => v i)
  let m := Nat.ofDigits 2 (digits.map Bool.toNat)
  have hm : m < 2 ^ n := by
    dsimp [m, digits]
    simpa [List.length_map] using
      ofDigits_boolDigits_lt_pow_mapLength ((List.finRange n).map (fun i => v i))
  refine List.mem_map.2 ?_
  refine ⟨m, List.mem_range.2 hm, ?_⟩
  dsimp [m]
  simpa [digits] using natToVertex_ofBoolDigits (v := v)

private lemma clause1_mem_family1 {n : Nat} {u v : Vertex n}
    (hLower : inLowerHalf u) (hAdj : Adj u v) :
    clause1 u v ∈ clausesFamily1 n := by
  unfold clausesFamily1
  refine List.mem_flatMap.2 ?_
  refine ⟨u, ?_, ?_⟩
  · exact List.mem_filter.2 ⟨mem_allVertices u, decide_eq_true hLower⟩
  · refine List.mem_map.2 ?_
    refine ⟨v, ?_, rfl⟩
    exact List.mem_filter.2 ⟨mem_allVertices v, decide_eq_true hAdj⟩

private lemma clause2_mem_family2_geodesic {n : Nat} {u v w : Vertex n}
    (hLower : inLowerHalf u)
    (hAdj : Adj v w)
    (hNotAdj : ¬ Adj u w)
    (hStep : dist u v + 1 = dist u w) :
    clause2 u v w ∈ clausesFamily2 .geodesic n := by
  unfold clausesFamily2 modeStepOk
  refine List.mem_flatMap.2 ?_
  refine ⟨u, ?_, ?_⟩
  · exact List.mem_filter.2 ⟨mem_allVertices u, decide_eq_true hLower⟩
  · refine List.mem_flatMap.2 ?_
    refine ⟨v, mem_allVertices v, ?_⟩
    refine List.mem_map.2 ?_
    refine ⟨w, ?_, rfl⟩
    exact List.mem_filter.2 ⟨mem_allVertices w, decide_eq_true ⟨hAdj, hNotAdj, hStep⟩⟩

private lemma clauseNoAntipode_mem_family {n : Nat} {v : Vertex n}
    (hLower : inLowerHalf v) :
    clauseNoAntipode v ∈ clausesNoAntipode n := by
  unfold clausesNoAntipode
  refine List.mem_map.2 ?_
  refine ⟨v, ?_, rfl⟩
  exact List.mem_filter.2 ⟨mem_allVertices v, decide_eq_true hLower⟩

private lemma clause1_mem_psi {n : Nat} {u v : Vertex n}
    (hLower : inLowerHalf u) (hAdj : Adj u v) :
    clause1 u v ∈ Psi n := by
  unfold Psi formula clauses
  exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
    (clause1_mem_family1 (u := u) (v := v) hLower hAdj))))

private lemma clause2_mem_psi {n : Nat} {u v w : Vertex n}
    (hLower : inLowerHalf u)
    (hAdj : Adj v w)
    (hNotAdj : ¬ Adj u w)
    (hStep : dist u v + 1 = dist u w) :
    clause2 u v w ∈ Psi n := by
  unfold Psi formula clauses
  exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
    (clause2_mem_family2_geodesic (u := u) (v := v) (w := w)
      hLower hAdj hNotAdj hStep))))

private lemma clauseNoAntipode_mem_psi {n : Nat} {v : Vertex n}
    (hLower : inLowerHalf v) :
    clauseNoAntipode v ∈ Psi n := by
  unfold Psi formula clauses
  exact List.mem_append.2 (Or.inr (clauseNoAntipode_mem_family (v := v) hLower))

private lemma clause1_sat_imp_reach {n : Nat} {τ : CNF.Assignment (Var n)} {u v : Vertex n}
    (hSat : CNF.Clause.Sat τ (clause1 u v))
    (hRed : CNF.Lit.Sat τ (rLiteral u v)) :
    τ (.reach u v) := by
  unfold clause1 CNF.Clause.Sat at hSat
  rcases hSat with ⟨l, hlmem, hlSat⟩
  simp at hlmem
  rcases hlmem with rfl | rfl
  · have hNotSat : ¬ CNF.Lit.Sat τ (rLiteral u v) :=
      (litNeg_sat_iff_not_sat (τ := τ) (l := rLiteral u v)).1 hlSat
    exact False.elim (hNotSat hRed)
  · simpa [pPos, pVar, CNF.Lit.Sat] using hlSat

private lemma clause2_sat_imp_reach {n : Nat} {τ : CNF.Assignment (Var n)} {u v w : Vertex n}
    (hSat : CNF.Clause.Sat τ (clause2 u v w))
    (hReachUV : τ (.reach u v))
    (hRedVW : CNF.Lit.Sat τ (rLiteral v w)) :
    τ (.reach u w) := by
  unfold clause2 CNF.Clause.Sat at hSat
  rcases hSat with ⟨l, hlmem, hlSat⟩
  simp at hlmem
  rcases hlmem with rfl | rfl | rfl
  · have : ¬ τ (.reach u v) := by
      simpa [pNeg, pVar, CNF.Lit.Sat] using hlSat
    exact False.elim (this hReachUV)
  · have hNotSat : ¬ CNF.Lit.Sat τ (rLiteral v w) :=
      (litNeg_sat_iff_not_sat (τ := τ) (l := rLiteral v w)).1 hlSat
    exact False.elim (hNotSat hRedVW)
  · simpa [pPos, pVar, CNF.Lit.Sat] using hlSat

private lemma clauseNoAntipode_sat_imp_notReach
    {n : Nat} {τ : CNF.Assignment (Var n)} {v : Vertex n}
    (hSat : CNF.Clause.Sat τ (clauseNoAntipode v)) :
    ¬ τ (.reach v (antipode v)) := by
  unfold clauseNoAntipode CNF.Clause.Sat at hSat
  rcases hSat with ⟨l, hlmem, hlSat⟩
  have : l = pNeg v (antipode v) := by simpa using hlmem
  subst this
  simpa [pNeg, pVar, CNF.Lit.Sat] using hlSat

private lemma dist_triangle_hamming {n : Nat} (u v w : Vertex n) :
    dist u w ≤ dist u v + dist v w := by
  simpa [dist, ThreeColorSAT.Hypercube.hamming] using (hammingDist_triangle u v w)

private lemma dist_le_length_hamming {n : Nat} {u v : Vertex n}
    (p : (ThreeColorSAT.Hypercube.Q n).Walk u v) : dist u v ≤ p.length := by
  induction p with
  | nil =>
      simp [dist, ThreeColorSAT.Hypercube.hamming]
  | @cons u v w h p ih =>
      have hAdjDist : dist u v = 1 := by
        simpa [dist, Adj, ThreeColorSAT.Hypercube.Q] using h
      have hTri : dist u w ≤ dist u v + dist v w := dist_triangle_hamming u v w
      calc
        dist u w ≤ dist u v + dist v w := hTri
        _ = 1 + dist v w := by simp [hAdjDist]
        _ ≤ 1 + p.length := Nat.add_le_add_left ih 1
        _ = (SimpleGraph.Walk.cons h p).length := by simp [Nat.add_comm]

private lemma dist_getVert_eq_index_of_geodesic {n : Nat} {u v : Vertex n}
    (p : (ThreeColorSAT.Hypercube.Q n).Walk u v)
    (hpLen : p.length = dist u v) {i : Nat} (hi : i ≤ p.length) :
    dist u (p.getVert i) = i := by
  let p₁ : (ThreeColorSAT.Hypercube.Q n).Walk u (p.getVert i) := p.take i
  let p₂ : (ThreeColorSAT.Hypercube.Q n).Walk (p.getVert i) v := p.drop i
  have hA : dist u (p.getVert i) ≤ p₁.length := dist_le_length_hamming p₁
  have hB : dist (p.getVert i) v ≤ p₂.length := dist_le_length_hamming p₂
  have hTri : dist u v ≤ dist u (p.getVert i) + dist (p.getVert i) v :=
    dist_triangle_hamming u (p.getVert i) v
  have hLen1 : p₁.length = i := by
    simp [p₁, SimpleGraph.Walk.take_length, Nat.min_eq_left hi]
  have hLen2 : p₂.length = p.length - i := by
    simp [p₂, SimpleGraph.Walk.drop_length]
  have hA' : dist u (p.getVert i) ≤ i := by simpa [hLen1] using hA
  have hB' : dist (p.getVert i) v ≤ p.length - i := by simpa [hLen2] using hB
  have hTri' : p.length ≤ dist u (p.getVert i) + dist (p.getVert i) v := by
    simpa [hpLen] using hTri
  have hUpper : dist u (p.getVert i) + dist (p.getVert i) v ≤ p.length := by
    calc
      dist u (p.getVert i) + dist (p.getVert i) v
          ≤ i + (p.length - i) := Nat.add_le_add hA' hB'
      _ = p.length := Nat.add_sub_of_le hi
  omega

private lemma edge_getVert_succ_mem_edges {n : Nat} {u v : Vertex n}
    (p : (ThreeColorSAT.Hypercube.Q n).Walk u v) {i : Nat} (hi : i < p.length) :
    edgeOf (p.getVert i) (p.getVert (i + 1)) ∈ p.edges := by
  let q : (ThreeColorSAT.Hypercube.Q n).Walk (p.getVert i) v := p.drop i
  have hqNotNil : ¬ q.Nil := by
    have hlen : 0 < q.length := by
      simpa [q, SimpleGraph.Walk.drop_length] using Nat.sub_pos_of_lt hi
    simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using hlen
  have hmemQ : edgeOf (p.getVert i) (p.getVert (i + 1)) ∈ q.edges := by
    have hhead : edgeOf (q.getVert 0) q.snd ∈ q.edges := by
      simpa [edgeOf] using (SimpleGraph.Walk.mk_start_snd_mem_edges (p := q) hqNotNil)
    simpa [q, edgeOf] using hhead
  have hSub : q.IsSubwalk p := SimpleGraph.Walk.isSubwalk_drop p i
  exact hSub.edges_subset hmemQ

private lemma reach_antipode_of_allRed_geodesic_of_sat
    {n : Nat} {τ : CNF.Assignment (Var n)}
    (hDim : 2 ≤ n)
    (hTau : τ ⊨ Psi n)
    {u : Vertex n} (hLower : inLowerHalf u)
    (p : (ThreeColorSAT.Hypercube.Q n).Walk u (antipode u))
    (hpLen : p.length = dist u (antipode u))
    (hAllRed : WalkAllRed (coloringOfAssignment τ) p) :
    τ (.reach u (antipode u)) := by
  have hStepReach : ∀ i, i < p.length → τ (.reach u (p.getVert (i + 1))) := by
    intro i
    induction i with
    | zero =>
        intro hi0
        have hAdj01 : Adj (p.getVert 0) (p.getVert 1) := p.adj_getVert_succ hi0
        have hAdjU1 : Adj u (p.getVert 1) := by simpa using hAdj01
        have hRedEdge : coloringOfAssignment τ (edgeOf u (p.getVert 1)) = true := by
          simpa [SimpleGraph.Walk.getVert_zero] using
            hAllRed _ (edge_getVert_succ_mem_edges (p := p) (i := 0) hi0)
        have hRedLit : CNF.Lit.Sat τ (rLiteral u (p.getVert 1)) :=
          (litSatBool_eq_true_iff (τ := τ) (l := rLiteral u (p.getVert 1))).1
            (by simpa [coloringOfAssignment_edgeOf] using hRedEdge)
        have hClause1Sat : CNF.Clause.Sat τ (clause1 u (p.getVert 1)) :=
          hTau _ (clause1_mem_psi (u := u) (v := p.getVert 1) hLower hAdjU1)
        exact clause1_sat_imp_reach (hSat := hClause1Sat) hRedLit
    | succ i ih =>
        intro hiSucc
        have hiPrev : i < p.length := Nat.lt_trans (Nat.lt_succ_self i) hiSucc
        have hReachPrev : τ (.reach u (p.getVert (i + 1))) := ih hiPrev
        have hAdj : Adj (p.getVert (i + 1)) (p.getVert (i + 2)) := p.adj_getVert_succ hiSucc
        have hRedEdge :
            coloringOfAssignment τ (edgeOf (p.getVert (i + 1)) (p.getVert (i + 2))) = true := by
          exact hAllRed _ (edge_getVert_succ_mem_edges (p := p) (i := i + 1) hiSucc)
        have hRedLit : CNF.Lit.Sat τ (rLiteral (p.getVert (i + 1)) (p.getVert (i + 2))) :=
          (litSatBool_eq_true_iff (τ := τ)
            (l := rLiteral (p.getVert (i + 1)) (p.getVert (i + 2)))).1
            (by simpa [coloringOfAssignment_edgeOf] using hRedEdge)
        have hi1le : i + 1 ≤ p.length := Nat.succ_le_of_lt hiPrev
        have hi2le : i + 2 ≤ p.length := Nat.succ_le_of_lt hiSucc
        have hDist1 : dist u (p.getVert (i + 1)) = i + 1 :=
          dist_getVert_eq_index_of_geodesic (p := p) hpLen hi1le
        have hDist2 : dist u (p.getVert (i + 2)) = i + 2 :=
          dist_getVert_eq_index_of_geodesic (p := p) hpLen hi2le
        have hStep : dist u (p.getVert (i + 1)) + 1 = dist u (p.getVert (i + 2)) := by
          omega
        have hNotAdj : ¬ Adj u (p.getVert (i + 2)) := by
          intro hAdjU
          have hDistAdj : dist u (p.getVert (i + 2)) = 1 := by
            simpa [dist, Adj, ThreeColorSAT.Hypercube.Q] using hAdjU
          omega
        have hClause2Sat : CNF.Clause.Sat τ (clause2 u (p.getVert (i + 1)) (p.getVert (i + 2))) :=
          hTau _ (clause2_mem_psi (u := u) (v := p.getVert (i + 1)) (w := p.getVert (i + 2))
            hLower hAdj hNotAdj hStep)
        exact clause2_sat_imp_reach (hSat := hClause2Sat) hReachPrev hRedLit
  have hLenPos : 0 < p.length := by
    rw [hpLen, dist_antipode u]
    omega
  have hLast : p.length - 1 < p.length := Nat.sub_lt hLenPos (by decide)
  have hReachLast : τ (.reach u (p.getVert (p.length - 1 + 1))) :=
    hStepReach (p.length - 1) hLast
  have hIndex : p.length - 1 + 1 = p.length := Nat.sub_add_cancel (Nat.succ_le_of_lt hLenPos)
  simpa [hIndex, SimpleGraph.Walk.getVert_length] using hReachLast

private lemma no_allRed_geodesic_lower_of_sat
    {n : Nat} {τ : CNF.Assignment (Var n)}
    (hDim : 2 ≤ n)
    (hTau : τ ⊨ Psi n)
    {u : Vertex n} (hLower : inLowerHalf u)
    (p : (ThreeColorSAT.Hypercube.Q n).Walk u (antipode u))
    (hpLen : p.length = dist u (antipode u)) :
    ¬ WalkAllRed (coloringOfAssignment τ) p := by
  intro hAllRed
  have hReach : τ (.reach u (antipode u)) :=
    reach_antipode_of_allRed_geodesic_of_sat (n := n) (τ := τ)
      hDim hTau hLower p hpLen hAllRed
  have hClauseNo : CNF.Clause.Sat τ (clauseNoAntipode u) :=
    hTau _ (clauseNoAntipode_mem_psi (n := n) (v := u) hLower)
  have hNotReach : ¬ τ (.reach u (antipode u)) :=
    clauseNoAntipode_sat_imp_notReach (n := n) (τ := τ) (v := u) hClauseNo
  exact hNotReach hReach

private def WalkAllBlue {n : Nat} (c : EdgeColoring n) {u v : Vertex n}
    (p : (ThreeColorSAT.Hypercube.Q n).Walk u v) : Prop :=
  ∀ e : Edge n, e ∈ p.edges → c e = false

private lemma walkAllRed_reverse {n : Nat} (c : EdgeColoring n) {u v : Vertex n}
    {p : (ThreeColorSAT.Hypercube.Q n).Walk u v} (hRed : WalkAllRed c p) :
    WalkAllRed c p.reverse := by
  intro e he
  rw [SimpleGraph.Walk.edges_reverse] at he
  exact hRed e (List.mem_reverse.1 he)

private def antipodeHom (n : Nat) :
    (ThreeColorSAT.Hypercube.Q n) →g (ThreeColorSAT.Hypercube.Q n) where
  toFun := antipode
  map_rel' := by
    intro u v h
    simpa [Adj] using Adj_antipode (u := u) (v := v) (by simpa [Adj] using h)

private lemma dist_comm_hamming {n : Nat} (u v : Vertex n) :
    dist u v = dist v u := by
  simpa [dist, ThreeColorSAT.Hypercube.hamming, ne_comm] using hammingDist_comm u v

private lemma antipode_ne_self {n : Nat} (hDim : 2 ≤ n) (v : Vertex n) :
    antipode v ≠ v := by
  have hPos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hDim
  let i0 : Fin n := ⟨0, hPos⟩
  have hneq : (antipode v) i0 ≠ v i0 := by
    cases hv : v i0 <;> simp [antipode, hv]
  intro hEq
  exact hneq (by simpa using congrArg (fun f => f i0) hEq)

private lemma inLowerHalf_antipode_of_not_inLowerHalf {n : Nat}
    (hDim : 2 ≤ n) (v : Vertex n) (hNot : ¬ inLowerHalf v) :
    inLowerHalf (antipode v) := by
  have hNeLex : lexCode v ≠ lexCode (antipode v) := by
    intro hEq
    have hEqV : v = antipode v := lexCode_injective hEq
    exact (antipode_ne_self (hDim := hDim) v) hEqV.symm
  have hlt : lexCode (antipode v) < lexCode v := by
    have hge : lexCode (antipode v) ≤ lexCode v := by
      exact le_of_not_gt (by simpa [inLowerHalf] using hNot)
    exact lt_of_le_of_ne hge (by simpa [eq_comm] using hNeLex)
  simpa [inLowerHalf, antipode_antipode] using hlt

private lemma walkAllRed_map_antipode_of_allBlue {n : Nat} {c : EdgeColoring n}
    (hAnti : IsAntipodalColoring c) {u v : Vertex n}
    (p : (ThreeColorSAT.Hypercube.Q n).Walk u v)
    (hBlue : WalkAllBlue c p) :
    WalkAllRed c (p.map (antipodeHom n)) := by
  intro e he
  rw [SimpleGraph.Walk.edges_map] at he
  rcases List.mem_map.mp he with ⟨e', he', rfl⟩
  revert he'
  refine Sym2.inductionOn e' ?_
  intro a b hab
  have hBlueAB : c (edgeOf a b) = false := by
    exact hBlue _ (by simpa [edgeOf] using hab)
  have hAdjAB : Adj a b := by
    exact (p.adj_of_mem_edges (x := a) (y := b) (by simpa [edgeOf] using hab))
  have hNe : c (edgeOf a b) ≠ c (edgeOf (antipode a) (antipode b)) := hAnti a b hAdjAB
  have hRedAnti : c (edgeOf (antipode a) (antipode b)) = true := by
    cases hA : c (edgeOf (antipode a) (antipode b)) <;> cases hB : c (edgeOf a b) <;>
      simp [hA, hB] at hNe hBlueAB ⊢
  simpa [edgeOf] using hRedAnti

/--
Abstract hypercube symmetry used for normalization to a lex-leader representative.
`map` acts on vertices; `inv` is its inverse; and it preserves both adjacency
and antipodes.
-/
structure CubeSymmetry (n : Nat) where
  map : Vertex n → Vertex n
  inv : Vertex n → Vertex n
  left_inv : Function.LeftInverse inv map
  right_inv : Function.RightInverse inv map
  preservesAdj : ∀ u v : Vertex n, Adj u v ↔ Adj (map u) (map v)
  commutesAntipode : ∀ v : Vertex n, map (antipode v) = antipode (map v)

/--
Coloring transported by a symmetry. This is the key object used to state orbit
equivalence between colorings.
-/
noncomputable def transportedColoring {n : Nat}
    (σ : CubeSymmetry n) (c : EdgeColoring n) : EdgeColoring n := by
  intro e
  exact c (Sym2.map σ.inv e)

@[simp] lemma transportedColoring_edgeOf {n : Nat}
    (σ : CubeSymmetry n) (c : EdgeColoring n) (u v : Vertex n) :
    transportedColoring σ c (edgeOf u v) = c (edgeOf (σ.inv u) (σ.inv v)) := by
  rfl

/-- Two colorings are equivalent if one is a symmetry transport of the other. -/
def SymmetryEquivalent (n : Nat) (c c' : EdgeColoring n) : Prop :=
  ∃ σ : CubeSymmetry n, c' = transportedColoring σ c

def compCubeSymmetry {n : Nat} (σ τ : CubeSymmetry n) : CubeSymmetry n where
  map := fun v => τ.map (σ.map v)
  inv := fun v => σ.inv (τ.inv v)
  left_inv := by
    intro v
    calc
      σ.inv (τ.inv (τ.map (σ.map v))) = σ.inv (σ.map v) := by rw [τ.left_inv (σ.map v)]
      _ = v := σ.left_inv v
  right_inv := by
    intro v
    calc
      τ.map (σ.map (σ.inv (τ.inv v))) = τ.map (τ.inv v) := by rw [σ.right_inv (τ.inv v)]
      _ = v := τ.right_inv v
  preservesAdj := by
    intro u v
    exact (σ.preservesAdj u v).trans (τ.preservesAdj (σ.map u) (σ.map v))
  commutesAntipode := by
    intro v
    simp [σ.commutesAntipode, τ.commutesAntipode]

def invCubeSymmetry {n : Nat} (σ : CubeSymmetry n) : CubeSymmetry n where
  map := σ.inv
  inv := σ.map
  left_inv := σ.right_inv
  right_inv := σ.left_inv
  preservesAdj := by
    intro u v
    constructor
    · intro h
      have h' : Adj (σ.map (σ.inv u)) (σ.map (σ.inv v)) := by
        simpa [σ.right_inv u, σ.right_inv v] using h
      exact (σ.preservesAdj (σ.inv u) (σ.inv v)).2 h'
    · intro h
      have h' : Adj (σ.map (σ.inv u)) (σ.map (σ.inv v)) :=
        (σ.preservesAdj (σ.inv u) (σ.inv v)).1 h
      simpa [σ.right_inv u, σ.right_inv v] using h'
  commutesAntipode := by
    intro v
    have hMap :
        σ.map (σ.inv (antipode v)) = σ.map (antipode (σ.inv v)) := by
      calc
        σ.map (σ.inv (antipode v)) = antipode v := σ.right_inv (antipode v)
        _ = antipode (σ.map (σ.inv v)) := by rw [σ.right_inv v]
        _ = σ.map (antipode (σ.inv v)) := (σ.commutesAntipode (σ.inv v)).symm
    exact σ.left_inv.injective hMap

@[simp] lemma transportedColoring_comp {n : Nat}
    (σ τ : CubeSymmetry n) (c : EdgeColoring n) :
    transportedColoring τ (transportedColoring σ c) =
      transportedColoring (compCubeSymmetry σ τ) c := by
  funext e
  refine Sym2.inductionOn e ?_
  intro a b
  rfl

private lemma edge_map_inv_map_eq {n : Nat} (σ : CubeSymmetry n) (a b : Vertex n) :
    (Sym2.map σ.inv (Sym2.map σ.map (edgeOf a b)) : Edge n) = edgeOf a b := by
  simp [edgeOf]
  exact Or.inl ⟨σ.left_inv a, σ.left_inv b⟩

private lemma edge_map_map_inv_eq {n : Nat} (σ : CubeSymmetry n) (a b : Vertex n) :
    (Sym2.map σ.map (Sym2.map σ.inv (edgeOf a b)) : Edge n) = edgeOf a b := by
  simp [edgeOf]
  exact Or.inl ⟨σ.right_inv a, σ.right_inv b⟩

@[simp] lemma transportedColoring_inv_left {n : Nat}
    (σ : CubeSymmetry n) (c : EdgeColoring n) :
    transportedColoring (invCubeSymmetry σ) (transportedColoring σ c) = c := by
  funext e
  refine Sym2.inductionOn e ?_
  intro a b
  change c ((Sym2.map σ.inv (Sym2.map σ.map (edgeOf a b)) : Edge n)) = c (edgeOf a b)
  rw [edge_map_inv_map_eq]

@[simp] lemma transportedColoring_inv_right {n : Nat}
    (σ : CubeSymmetry n) (c : EdgeColoring n) :
    transportedColoring σ (transportedColoring (invCubeSymmetry σ) c) = c := by
  funext e
  refine Sym2.inductionOn e ?_
  intro a b
  change c ((Sym2.map σ.map (Sym2.map σ.inv (edgeOf a b)) : Edge n)) = c (edgeOf a b)
  rw [edge_map_map_inv_eq]

def idCubeSymmetry (n : Nat) : CubeSymmetry n where
  map := fun v => v
  inv := fun v => v
  left_inv := by intro v; rfl
  right_inv := by intro v; rfl
  preservesAdj := by intro u v; rfl
  commutesAntipode := by intro v; rfl

@[simp] lemma transportedColoring_id {n : Nat} (c : EdgeColoring n) :
    transportedColoring (idCubeSymmetry n) c = c := by
  funext e
  simp [transportedColoring, idCubeSymmetry]

lemma symmetryEquivalent_refl {n : Nat} (c : EdgeColoring n) :
    SymmetryEquivalent n c c := by
  exact ⟨idCubeSymmetry n, (transportedColoring_id (n := n) c).symm⟩

lemma symmetryEquivalent_trans {n : Nat} {c₁ c₂ c₃ : EdgeColoring n} :
    SymmetryEquivalent n c₁ c₂ →
      SymmetryEquivalent n c₂ c₃ →
      SymmetryEquivalent n c₁ c₃ := by
  intro h12 h23
  rcases h12 with ⟨σ, rfl⟩
  rcases h23 with ⟨τ, rfl⟩
  exact ⟨compCubeSymmetry σ τ, by simp [transportedColoring_comp]⟩

lemma inv_preservesAdj {n : Nat} (σ : CubeSymmetry n) {u v : Vertex n}
    (h : Adj u v) : Adj (σ.inv u) (σ.inv v) := by
  have hMap : Adj (σ.map (σ.inv u)) (σ.map (σ.inv v)) := by
    simpa [σ.right_inv u, σ.right_inv v] using h
  exact (σ.preservesAdj (σ.inv u) (σ.inv v)).2 hMap

lemma inv_commutesAntipode {n : Nat} (σ : CubeSymmetry n) (v : Vertex n) :
    σ.inv (antipode v) = antipode (σ.inv v) := by
  have hMap :
      σ.map (σ.inv (antipode v)) = σ.map (antipode (σ.inv v)) := by
    calc
      σ.map (σ.inv (antipode v)) = antipode v := σ.right_inv (antipode v)
      _ = antipode (σ.map (σ.inv v)) := by rw [σ.right_inv v]
      _ = σ.map (antipode (σ.inv v)) := (σ.commutesAntipode (σ.inv v)).symm
  exact σ.left_inv.injective hMap

def cubeSymmetryInvHom (n : Nat) (σ : CubeSymmetry n) :
    (ThreeColorSAT.Hypercube.Q n) →g (ThreeColorSAT.Hypercube.Q n) where
  toFun := σ.inv
  map_rel' := by
    intro u v h
    simpa [Adj] using inv_preservesAdj (σ := σ) (u := u) (v := v) (by simpa [Adj] using h)

lemma walkMonochromatic_copy_iff {n : Nat} (c : EdgeColoring n)
    {u v u' v' : Vertex n} (p : (ThreeColorSAT.Hypercube.Q n).Walk u v)
    (hu : u = u') (hv : v = v') :
    WalkMonochromatic c (p.copy hu hv) ↔ WalkMonochromatic c p := by
  constructor <;> intro hMono
  · rcases hMono with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro e he
    exact hb e (by simpa [SimpleGraph.Walk.edges_copy] using he)
  · rcases hMono with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro e he
    exact hb e (by simpa [SimpleGraph.Walk.edges_copy] using he)

lemma walkMonochromatic_map_inv_of_transport {n : Nat}
    (σ : CubeSymmetry n) (c : EdgeColoring n) {u v : Vertex n}
    (p : (ThreeColorSAT.Hypercube.Q n).Walk u v) :
    WalkMonochromatic (transportedColoring σ c) p →
      WalkMonochromatic c (p.map (cubeSymmetryInvHom n σ)) := by
  intro hMono
  rcases hMono with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro e he
  rw [SimpleGraph.Walk.edges_map] at he
  rcases List.mem_map.mp he with ⟨e', he', rfl⟩
  simpa [transportedColoring] using hb e' he'

/--
Semantic predicate for the lex-leader side-constraints used by the
Python-compatible CNF (`--partial-sym-break` clauses).
-/
private def edgeSeqCode (n : Nat) (c : EdgeColoring n) : Nat :=
  (((originalSignedEdgesPy n (allVertexCodes n)).map
    (fun e => c (edgeOf (natToVertex n e.1) (natToVertex n e.2)))).foldl
      (fun acc b => 2 * acc + Bool.toNat b) 0)

def LexLeaderCanonical (n : Nat) (c : EdgeColoring n) : Prop :=
  ∀ c' : EdgeColoring n, SymmetryEquivalent n c c' →
    edgeSeqCode n c ≤ edgeSeqCode n c'

/--
Completeness direction for `Ψ_n` needed by the lift:
from a satisfying assignment of `Ψ_n`, extract an antipodal coloring with no
monochromatic antipodal geodesic.
-/
lemma psi_counterexample_of_sat (n : Nat) :
    2 ≤ n →
    CNF.Satisfiable (Psi n) →
      ∃ c : EdgeColoring n,
        IsAntipodalColoring c ∧ NoMonochromaticAntipodalGeodesic n c := by
  intro hDim hSat
  rcases hSat with ⟨τ, hTau⟩
  let c : EdgeColoring n := coloringOfAssignment τ
  have hAnti : IsAntipodalColoring c := coloringOfAssignment_isAntipodal (hDim := hDim) τ
  refine ⟨c, hAnti, ?_⟩
  intro v p hpLen hMono
  rcases hMono with ⟨b, hb⟩
  let q : (ThreeColorSAT.Hypercube.Q n).Walk v (antipode v) :=
    if hbTrue : b = true then p else
      ((p.map (antipodeHom n)).reverse).copy (by simp [antipodeHom]) (by simp [antipodeHom])
  have hqLen : q.length = dist v (antipode v) := by
    by_cases hbTrue : b = true
    · simp [q, hbTrue, hpLen]
    · calc
        q.length = ((p.map (antipodeHom n)).reverse).length := by
          simp [q, hbTrue]
        _ = p.length := by simp
        _ = dist v (antipode v) := hpLen
  have hqRed : WalkAllRed c q := by
    by_cases hbTrue : b = true
    · have hRedP : WalkAllRed c p := by
        intro e he
        exact by simpa [c, hbTrue] using hb e he
      simpa [q, hbTrue] using hRedP
    · have hBlueP : WalkAllBlue c p := by
        intro e he
        exact by simpa [WalkAllBlue, c, hbTrue] using hb e he
      have hRedMap : WalkAllRed c (p.map (antipodeHom n)) :=
        walkAllRed_map_antipode_of_allBlue (hAnti := hAnti) (p := p) hBlueP
      have hRedRev : WalkAllRed c ((p.map (antipodeHom n)).reverse) :=
        walkAllRed_reverse (c := c) (p := p.map (antipodeHom n)) hRedMap
      intro e he
      exact hRedRev e (by simpa [q, hbTrue, SimpleGraph.Walk.edges_copy] using he)
  by_cases hLowerV : inLowerHalf v
  · exact
      (no_allRed_geodesic_lower_of_sat
        (n := n) (τ := τ) hDim hTau (u := v) hLowerV q hqLen) hqRed
  · have hLowerAnti : inLowerHalf (antipode v) :=
      inLowerHalf_antipode_of_not_inLowerHalf (hDim := hDim) v hLowerV
    let qr : (ThreeColorSAT.Hypercube.Q n).Walk (antipode v) (antipode (antipode v)) :=
      (q.reverse).copy rfl (by simp)
    have hqRevLen : qr.length = dist (antipode v) (antipode (antipode v)) := by
      calc
        qr.length = q.reverse.length := by simp [qr]
        _ = q.length := by simp
        _ = dist v (antipode v) := hqLen
        _ = dist (antipode v) v := dist_comm_hamming v (antipode v)
        _ = dist (antipode v) (antipode (antipode v)) := by simp
    have hqRevRedBase : WalkAllRed c q.reverse := walkAllRed_reverse (c := c) (p := q) hqRed
    have hqRevRed : WalkAllRed c qr := by
      intro e he
      exact hqRevRedBase e (by simpa [qr, SimpleGraph.Walk.edges_copy] using he)
    exact
      (no_allRed_geodesic_lower_of_sat
        (n := n) (τ := τ) hDim hTau (u := antipode v) hLowerAnti qr hqRevLen) hqRevRed

/--
Every coloring has a symmetry-equivalent lex-leader representative.
This is the finite-orbit minimization step.
-/
lemma exists_lexLeader_representative {n : Nat} (c : EdgeColoring n) :
    ∃ c' : EdgeColoring n,
      SymmetryEquivalent n c c' ∧ LexLeaderCanonical n c' := by
  classical
  let orbit : Set (EdgeColoring n) := {d | SymmetryEquivalent n c d}
  have hOrbitFin : orbit.Finite :=
    (Set.finite_univ.subset (by
      intro d _
      simp))
  have hOrbitNonempty : orbit.Nonempty := by
    refine ⟨c, ?_⟩
    exact symmetryEquivalent_refl (n := n) c
  obtain ⟨c', hmin⟩ :=
    Set.Finite.exists_minimalFor (f := edgeSeqCode n) (s := orbit) hOrbitFin hOrbitNonempty
  refine ⟨c', hmin.prop, ?_⟩
  intro d hd
  have hdOrbit : d ∈ orbit := symmetryEquivalent_trans hmin.prop hd
  have htotal : edgeSeqCode n d ≤ edgeSeqCode n c' ∨ edgeSeqCode n c' ≤ edgeSeqCode n d :=
    le_total (edgeSeqCode n d) (edgeSeqCode n c')
  exact htotal.elim (fun hdc => hmin.le_of_le hdOrbit hdc) (fun hcd => hcd)

/--
Counterexample properties are invariant under symmetry transport.
-/
lemma symmetry_equivalent_preserves_counterexample {n : Nat} {c c' : EdgeColoring n} :
    SymmetryEquivalent n c c' →
      IsAntipodalColoring c →
      NoMonochromaticAntipodalGeodesic n c →
      IsAntipodalColoring c' ∧ NoMonochromaticAntipodalGeodesic n c' := by
  intro hEqv hAnti hNoGeo
  rcases hEqv with ⟨σ, rfl⟩
  refine ⟨?_, ?_⟩
  · intro u v hAdj
    have hAdjInv : Adj (σ.inv u) (σ.inv v) :=
      inv_preservesAdj (σ := σ) hAdj
    have hNe : c (edgeOf (σ.inv u) (σ.inv v)) ≠
        c (edgeOf (antipode (σ.inv u)) (antipode (σ.inv v))) :=
      hAnti (σ.inv u) (σ.inv v) hAdjInv
    simpa [transportedColoring_edgeOf, inv_commutesAntipode] using hNe
  · intro v p hpLen hpMono
    let q : (ThreeColorSAT.Hypercube.Q n).Walk (σ.inv v) (antipode (σ.inv v)) :=
      (p.map (cubeSymmetryInvHom n σ)).copy rfl (inv_commutesAntipode (σ := σ) v)
    have hqLen : q.length = dist (σ.inv v) (antipode (σ.inv v)) := by
      calc
        q.length = (p.map (cubeSymmetryInvHom n σ)).length := by
          simp [q]
        _ = p.length := by simp
        _ = dist v (antipode v) := hpLen
        _ = n := dist_antipode v
        _ = dist (σ.inv v) (antipode (σ.inv v)) := (dist_antipode (σ.inv v)).symm
    have hMonoMap : WalkMonochromatic c (p.map (cubeSymmetryInvHom n σ)) :=
      walkMonochromatic_map_inv_of_transport (σ := σ) (c := c) (p := p) hpMono
    have hMonoQ : WalkMonochromatic c q := by
      simpa [q] using
        (walkMonochromatic_copy_iff (c := c) (p := p.map (cubeSymmetryInvHom n σ))
          (hu := rfl) (hv := inv_commutesAntipode (σ := σ) v)).2 hMonoMap
    exact hNoGeo (σ.inv v) q hqLen hMonoQ

private lemma fold_count_range_eq_sum_range (u v : Nat) :
    ∀ n,
      List.foldl (fun acc i => if u.testBit i = v.testBit i then acc else acc + 1)
        0 (List.range n)
      = Finset.sum (Finset.range n) (fun i => if u.testBit i = v.testBit i then 0 else 1) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
      by_cases h : u.testBit n = v.testBit n
      · simp [h]
      · simp [h, Nat.add_comm]

private lemma distCode_eq_dist_natToVertex (n u v : Nat) :
    distCode n u v = dist (natToVertex n u) (natToVertex n v) := by
  have hfold := fold_count_range_eq_sum_range u v n
  have hcard :
      Finset.card (Finset.univ.filter (fun i : Fin n => u.testBit i.1 ≠ v.testBit i.1))
        = Finset.sum (Finset.range n) (fun i => if u.testBit i = v.testBit i then 0 else 1) := by
    let p : Fin n → Prop := fun i => u.testBit i.1 ≠ v.testBit i.1
    have h1 : Finset.card (Finset.univ.filter p) = Finset.sum (Finset.univ.filter p) (fun _ => 1) := by
      simp
    have h2 : Finset.sum (Finset.univ.filter p) (fun _ => 1)
        = Finset.sum Finset.univ (fun i : Fin n => if p i then 1 else 0) := by
      rw [Finset.sum_filter]
    have h3 : Finset.sum Finset.univ (fun i : Fin n => if p i then 1 else 0)
        = Finset.sum Finset.univ (fun i : Fin n => if u.testBit i.1 = v.testBit i.1 then 0 else 1) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hp : p i
      · simp [p, hp]
      · simp [p, hp]
    have h4 : Finset.sum Finset.univ (fun i : Fin n => if u.testBit i.1 = v.testBit i.1 then 0 else 1)
        = Finset.sum (Finset.range n) (fun i => if u.testBit i = v.testBit i then 0 else 1) := by
      simpa using
        (Fin.sum_univ_eq_sum_range (f := fun i => if u.testBit i = v.testBit i then 0 else 1) (n := n))
    simpa [p] using h1.trans (h2.trans (h3.trans h4))
  simpa [distCode, dist, ThreeColorSAT.Hypercube.hamming, natToVertex, bitAt] using hfold.trans hcard.symm

private lemma mem_allVertexCodes_lt_pow {n u : Nat} (hu : u ∈ allVertexCodes n) : u < 2 ^ n := by
  simpa [allVertexCodes] using (List.mem_range.mp hu)

private lemma natToVertex_antipodeCode_eq_antipode_of_mem {n u : Nat}
    (hu : u ∈ allVertexCodes n) :
    natToVertex n (antipodeCode n u) = antipode (natToVertex n u) := by
  exact natToVertex_antipodeCode_eq_antipode_of_lt_pow n u (mem_allVertexCodes_lt_pow hu)

private lemma distCode_step_implies_dist_step (n u v w : Nat)
    (hStep : distCode n u v + 1 = distCode n u w) :
    dist (natToVertex n u) (natToVertex n v) + 1 =
      dist (natToVertex n u) (natToVertex n w) := by
  simpa [distCode_eq_dist_natToVertex] using hStep

private lemma flipCode_lt_pow {n u i : Nat}
    (hu : u < 2 ^ n) (hi : i < n) :
    flipCode u i < 2 ^ n := by
  unfold flipCode toggleBit
  exact Nat.xor_lt_two_pow hu
    (Nat.pow_lt_pow_right (by decide : 1 < 2) hi)

private lemma testBit_flipCode (u i j : Nat) :
    (flipCode u i).testBit j = (u.testBit j ^^ (2 ^ i).testBit j) := by
  unfold flipCode toggleBit
  simpa using (Nat.testBit_xor u (2 ^ i) j)

private lemma testBit_flipCode_eq_of_ne (u i j : Nat) (hji : j ≠ i) :
    (flipCode u i).testBit j = u.testBit j := by
  rw [testBit_flipCode]
  simpa [Nat.testBit_two_pow_of_ne (n := i) (m := j) hji.symm]

private lemma testBit_flipCode_eq_not (u i : Nat) :
    (flipCode u i).testBit i = !(u.testBit i) := by
  rw [testBit_flipCode]
  have hpow : (2 ^ i).testBit i = true := by
    simpa using (Nat.testBit_two_pow (n := i) (m := i))
  cases hbit : u.testBit i <;> simp [hpow, hbit]

private lemma distCode_flipCode_self (n u i : Nat) (hi : i < n) :
    distCode n u (flipCode u i) = 1 := by
  have hsum :
      distCode n u (flipCode u i) =
        Finset.sum (Finset.range n)
          (fun j => if u.testBit j = (flipCode u i).testBit j then 0 else 1) := by
    simpa [distCode, bitAt] using
      (fold_count_range_eq_sum_range u (flipCode u i) n)
  rw [hsum]
  have hTerm :
      ∀ j : Nat,
        j ∈ Finset.range n →
          (if u.testBit j = (flipCode u i).testBit j then 0 else 1) =
            (if j = i then 1 else 0) := by
    intro j hj
    by_cases hji : j = i
    · subst hji
      rw [testBit_flipCode_eq_not]
      cases hbit : u.testBit j <;> simp [hbit]
    · rw [testBit_flipCode_eq_of_ne (u := u) (i := i) (j := j) hji]
      simp [hji]
  have hSumEq :
      Finset.sum (Finset.range n)
        (fun j => if u.testBit j = (flipCode u i).testBit j then 0 else 1) =
      Finset.sum (Finset.range n) (fun j => if j = i then 1 else 0) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact hTerm j hj
  rw [hSumEq]
  have hiMem : i ∈ Finset.range n := Finset.mem_range.mpr hi
  calc
    Finset.sum (Finset.range n) (fun j => if j = i then 1 else 0)
        = (if i ∈ Finset.range n then 1 else 0) := by
            simpa using
              (Finset.sum_ite_eq' (s := Finset.range n) (a := i) (b := fun _ => (1 : Nat)))
    _ = 1 := by simp [hiMem]

private lemma neighborsCode_mem_allVertexCodes {n u v : Nat}
    (hu : u ∈ allVertexCodes n)
    (hv : v ∈ neighborsCode n u) :
    v ∈ allVertexCodes n := by
  have huLt : u < 2 ^ n := mem_allVertexCodes_lt_pow hu
  rcases List.mem_map.mp hv with ⟨i, hi, rfl⟩
  have hiLt : i < n := List.mem_range.mp hi
  exact List.mem_range.mpr (flipCode_lt_pow huLt hiLt)

private lemma neighborsCode_adj {n u v : Nat}
    (hv : v ∈ neighborsCode n u) :
    Adj (natToVertex n u) (natToVertex n v) := by
  rcases List.mem_map.mp hv with ⟨i, hi, rfl⟩
  have hiLt : i < n := List.mem_range.mp hi
  have hDistCode : distCode n u (flipCode u i) = 1 :=
    distCode_flipCode_self n u i hiLt
  have hDist : dist (natToVertex n u) (natToVertex n (flipCode u i)) = 1 := by
    simpa [distCode_eq_dist_natToVertex] using hDistCode
  simpa [Adj, ThreeColorSAT.Hypercube.Q] using hDist

/--
If a coloring is a geodesic counterexample and satisfies the lex-leader
normal form, then the Python-compatible CNF is satisfiable.
-/
private def pysatState (n : Nat) : PyEncState :=
  buildPysatConjecture1AntipodalLexState n

private def simplifiedLexState (n : Nat) : PyEncState :=
  NorinSimplified.buildSimplifiedConjecture2AntipodalState n 20 false

private def PyStateInv (st : PyEncState) : Prop :=
  (∀ {k : PyVarKey} {i : Nat}, st.idToNamed[i]? = some k → st.nextId > i) ∧
  (∀ {k : PyVarKey} {i : Nat}, st.namedIds[k]? = some i → st.idToNamed[i]? = some k)

private lemma pyState_noZero_empty :
    (({} : PyEncState).idToNamed[0]? = none) := by
  simp

private lemma pyState_nextPos_empty :
    (0 < ({} : PyEncState).nextId) := by
  decide

private lemma pyState_noZero_pushClausePy {st : PyEncState} {cl : List Int}
    (hNoZero : st.idToNamed[0]? = none) :
    (((pushClausePy cl).run st).2.idToNamed[0]? = none) := by
  simpa [pushClausePy] using hNoZero

private lemma pyState_nextPos_pushClausePy {st : PyEncState} {cl : List Int}
    (hNextPos : 0 < st.nextId) :
    (0 < ((pushClausePy cl).run st).2.nextId) := by
  simpa [pushClausePy] using hNextPos

private lemma pyState_noZero_freshIdPy {st : PyEncState}
    (hNoZero : st.idToNamed[0]? = none) :
    ((freshIdPy.run st).2.idToNamed[0]? = none) := by
  simpa [freshIdPy] using hNoZero

private lemma pyState_nextPos_freshIdPy {st : PyEncState} :
    (0 < (freshIdPy.run st).2.nextId) := by
  rcases st with ⟨nextId, namedIds, idToNamed, clauses⟩
  change 0 < nextId + 1
  exact Nat.succ_pos nextId

private lemma pushClausePy_run_nextId {st : PyEncState} {cl : List Int} :
    ((pushClausePy cl).run st).2.nextId = st.nextId := by
  cases st
  rfl

private lemma freshIdPy_run_fst {st : PyEncState} :
    (freshIdPy.run st).1 = st.nextId := by
  cases st
  rfl

private lemma freshIdPy_run_nextId {st : PyEncState} :
    (freshIdPy.run st).2.nextId = st.nextId + 1 := by
  cases st
  rfl

private lemma pyStateInv_freshIdPy_new_none {st : PyEncState}
    (hInv : PyStateInv st) :
    ((freshIdPy.run st).2.idToNamed[(freshIdPy.run st).1]? = none) := by
  have hNone : st.idToNamed[st.nextId]? = none := by
    cases hget : st.idToNamed[st.nextId]? with
    | none =>
        rfl
    | some k =>
        have hlt : st.nextId < st.nextId := hInv.1 hget
        exact False.elim ((Nat.lt_irrefl st.nextId) hlt)
  simpa [freshIdPy] using hNone

private lemma pyState_noZero_idForPy {st : PyEncState} {k : PyVarKey}
    (hNoZero : st.idToNamed[0]? = none)
    (hNextPos : 0 < st.nextId) :
    ((idForPy k).run st).2.idToNamed[0]? = none := by
  cases hget : st.namedIds[k]? with
  | some i =>
      simpa [idForPy, hget] using hNoZero
  | none =>
      have hNoZeroMem : 0 ∉ st.idToNamed := by
        intro hMem0
        have hSome : st.idToNamed[0]? = some (st.idToNamed[0]) :=
          (Std.HashMap.getElem?_eq_some_iff
            (m := st.idToNamed) (k := 0) (v := st.idToNamed[0])).2 ⟨hMem0, rfl⟩
        simpa [hNoZero] using hSome
      have hInsNotMem : 0 ∉ st.idToNamed.insert st.nextId k := by
        intro hMemIns
        have hContIns : (st.idToNamed.insert st.nextId k).contains 0 = true :=
          (Std.HashMap.mem_iff_contains).1 hMemIns
        have hCont0 : st.idToNamed.contains 0 = false := by
          exact (Bool.eq_false_iff).2 (by
            intro hC
            exact hNoZeroMem ((Std.HashMap.mem_iff_contains).2 hC))
        have hEq0 : (st.nextId == 0) = false := by
          exact by simp [Nat.ne_of_gt hNextPos]
        rw [Std.HashMap.contains_insert (m := st.idToNamed) (k := st.nextId) (a := 0) (v := k)] at hContIns
        simp [hEq0, hCont0] at hContIns
      unfold idForPy
      simp [hget]
      exact hInsNotMem

private lemma pyState_nextPos_idForPy {st : PyEncState} {k : PyVarKey}
    (hNextPos : 0 < st.nextId) :
    0 < ((idForPy k).run st).2.nextId := by
  cases hget : st.namedIds[k]? with
  | some i =>
      simpa [idForPy, hget] using hNextPos
  | none =>
      unfold idForPy
      simp [hget]
      exact Nat.succ_pos st.nextId

private lemma pyState_nextId_le_idForPy {st : PyEncState} {k : PyVarKey} :
    st.nextId ≤ ((idForPy k).run st).2.nextId := by
  cases hget : st.namedIds[k]? with
  | some i =>
      have hRun : (idForPy k).run st = (i, st) := by
        simp [idForPy, hget]
        rfl
      simpa [hRun]
  | none =>
      let st' : PyEncState := { st with
        nextId := st.nextId + 1
        namedIds := st.namedIds.insert k st.nextId
        idToNamed := st.idToNamed.insert st.nextId k
      }
      have hRun : (idForPy k).run st = (st.nextId, st') := by
        simp [idForPy, hget, st']
        rfl
      rw [hRun]
      change st.nextId ≤ st'.nextId
      simpa [st'] using (Nat.le_succ st.nextId)

private lemma pyState_noZero_rOldIdPy {st : PyEncState} {n u v : Nat}
    (hNoZero : st.idToNamed[0]? = none)
    (hNextPos : 0 < st.nextId) :
    ((rOldIdPy n u v).run st).2.idToNamed[0]? = none := by
  unfold rOldIdPy
  simpa using
    (pyState_noZero_idForPy (st := st)
      (k := .r (orderedCodePair n u v).1 (orderedCodePair n u v).2) hNoZero hNextPos)

private lemma pyState_nextPos_rOldIdPy {st : PyEncState} {n u v : Nat}
    (hNextPos : 0 < st.nextId) :
    0 < ((rOldIdPy n u v).run st).2.nextId := by
  unfold rOldIdPy
  simpa using
    (pyState_nextPos_idForPy (st := st)
      (k := .r (orderedCodePair n u v).1 (orderedCodePair n u v).2) hNextPos)

private lemma pyState_nextId_le_rOldIdPy {st : PyEncState} {n u v : Nat} :
    st.nextId ≤ ((rOldIdPy n u v).run st).2.nextId := by
  unfold rOldIdPy
  simpa using
    (pyState_nextId_le_idForPy (st := st)
      (k := .r (orderedCodePair n u v).1 (orderedCodePair n u v).2))

private lemma pyState_noZero_pcLitPy {st : PyEncState} {isRed : Bool} {u v s : Nat}
    (hNoZero : st.idToNamed[0]? = none)
    (hNextPos : 0 < st.nextId) :
    ((pcLitPy isRed u v s).run st).2.idToNamed[0]? = none := by
  unfold pcLitPy pcIdPy
  simpa using
    (pyState_noZero_idForPy (st := st) (k := .pc isRed u v s) hNoZero hNextPos)

private lemma pyState_nextPos_pcLitPy {st : PyEncState} {isRed : Bool} {u v s : Nat}
    (hNextPos : 0 < st.nextId) :
    0 < ((pcLitPy isRed u v s).run st).2.nextId := by
  unfold pcLitPy pcIdPy
  simpa using
    (pyState_nextPos_idForPy (st := st) (k := .pc isRed u v s) hNextPos)

private lemma pyState_nextId_le_pcLitPy {st : PyEncState} {isRed : Bool} {u v s : Nat} :
    st.nextId ≤ ((pcLitPy isRed u v s).run st).2.nextId := by
  unfold pcLitPy pcIdPy
  simpa using
    (pyState_nextId_le_idForPy (st := st) (k := .pc isRed u v s))

private lemma pyState_nextId_le_rLitPy {st : PyEncState} {n u v : Nat} :
    st.nextId ≤ ((rLitPy n u v).run st).2.nextId := by
  let p := orderedCodePair n u v
  let a := p.1
  let b := p.2
  by_cases hlt : vLt n a (antipodeCode n b) = true
  · have hLe :
      st.nextId ≤ ((rOldIdPy n a b).run st).2.nextId :=
      pyState_nextId_le_rOldIdPy (st := st) (n := n) (u := a) (v := b)
    simpa [rLitPy, a, b, p, hlt] using hLe
  · have hLe :
      st.nextId ≤ ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2.nextId :=
      pyState_nextId_le_rOldIdPy (st := st) (n := n)
        (u := antipodeCode n a) (v := antipodeCode n b)
    have hRun :
        (rLitPy n u v).run st =
          (-Int.ofNat ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1,
            ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2) := by
      unfold rLitPy
      simp [a, b, p, hlt]
      rfl
    rw [hRun]
    exact hLe

private lemma pyState_noZero_rLitPy {st : PyEncState} {n u v : Nat}
    (hNoZero : st.idToNamed[0]? = none)
    (hNextPos : 0 < st.nextId) :
    ((rLitPy n u v).run st).2.idToNamed[0]? = none := by
  let p := orderedCodePair n u v
  let a := p.1
  let b := p.2
  by_cases hlt : vLt n a (antipodeCode n b) = true
  · have hR :
      ((rOldIdPy n a b).run st).2.idToNamed[0]? = none :=
      pyState_noZero_rOldIdPy (st := st) (n := n) (u := a) (v := b) hNoZero hNextPos
    simpa [rLitPy, a, b, p, hlt] using hR
  · have hR :
      ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2.idToNamed[0]? = none :=
      pyState_noZero_rOldIdPy (st := st) (n := n)
        (u := antipodeCode n a) (v := antipodeCode n b) hNoZero hNextPos
    have hRun :
        (rLitPy n u v).run st =
          (-Int.ofNat ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1,
            ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2) := by
      unfold rLitPy
      simp [a, b, p, hlt]
      rfl
    rw [hRun]
    simpa using hR

private lemma pyState_nextPos_rLitPy {st : PyEncState} {n u v : Nat}
    (hNextPos : 0 < st.nextId) :
    0 < ((rLitPy n u v).run st).2.nextId := by
  let p := orderedCodePair n u v
  let a := p.1
  let b := p.2
  by_cases hlt : vLt n a (antipodeCode n b) = true
  · have hR : 0 < ((rOldIdPy n a b).run st).2.nextId :=
      pyState_nextPos_rOldIdPy (st := st) (n := n) (u := a) (v := b) hNextPos
    simpa [rLitPy, a, b, p, hlt] using hR
  · have hR : 0 < ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2.nextId :=
      pyState_nextPos_rOldIdPy (st := st) (n := n)
        (u := antipodeCode n a) (v := antipodeCode n b) hNextPos
    have hRun :
        (rLitPy n u v).run st =
          (-Int.ofNat ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1,
            ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2) := by
      unfold rLitPy
      simp [a, b, p, hlt]
      rfl
    rw [hRun]
    simpa using hR

private lemma pyStateInv_empty : PyStateInv {} := by
  constructor
  · intro k i hi
    simpa using hi
  · intro k i hi
    simpa using hi

private lemma pyStateInv_pushClausePy (st : PyEncState) (cl : List Int)
    (hInv : PyStateInv st) :
    PyStateInv ((pushClausePy cl).run st).2 := by
  simpa [pushClausePy] using hInv

private lemma pyStateInv_freshIdPy {st : PyEncState}
    (hInv : PyStateInv st) :
    PyStateInv (freshIdPy.run st).2 := by
  rcases st with ⟨nextId, namedIds, idToNamed, clauses⟩
  rcases hInv with ⟨hInvId, hInvNamed⟩
  constructor
  · intro k i hi
    have hOld : idToNamed[i]? = some k := by
      simpa [freshIdPy] using hi
    have hiLt : nextId > i := hInvId hOld
    change nextId + 1 > i
    omega
  · intro k i hi
    have hOld : namedIds[k]? = some i := by
      simpa [freshIdPy] using hi
    have hId : idToNamed[i]? = some k := hInvNamed hOld
    simpa [freshIdPy] using hId

private lemma pyStateInv_idForPy {st : PyEncState} {k : PyVarKey}
    (hInv : PyStateInv st) :
    PyStateInv ((idForPy k).run st).2 ∧
      ((idForPy k).run st).2.idToNamed[((idForPy k).run st).1]? = some k := by
  cases hget : st.namedIds[k]? with
  | some i =>
      have hiNamed : st.idToNamed[i]? = some k := hInv.2 hget
      simpa [idForPy, hget] using And.intro hInv hiNamed
  | none =>
      let i := st.nextId
      let st' : PyEncState := { st with
        nextId := i + 1
        namedIds := st.namedIds.insert k i
        idToNamed := st.idToNamed.insert i k
      }
      have hIdSelf : (st.idToNamed.insert i k)[i]? = some k := by
        simpa using (Std.HashMap.getElem?_insert_self (m := st.idToNamed) (k := i) (v := k))
      have hInv' : PyStateInv st' := by
        constructor
        · intro k' j hj
          have hIns : (st.idToNamed.insert i k)[j]? = some k' := by
            simpa [st', i] using hj
          have hGetIns :
              (st.idToNamed.insert i k)[j]? =
                if (i == j) = true then some k else st.idToNamed[j]? := by
            simpa using (Std.HashMap.getElem?_insert (m := st.idToNamed) (k := i) (a := j) (v := k))
          rw [hGetIns] at hIns
          by_cases hij : i = j
          · subst hij
            simp [st', i]
          · have hEqFalse : (i == j) = false := by simp [hij]
            rw [hEqFalse] at hIns
            have hOld : st.idToNamed[j]? = some k' := by simpa using hIns
            have hjLt : st.nextId > j := hInv.1 hOld
            have hjLt' : i > j := by simpa [i] using hjLt
            have hjSucc : i + 1 > j := lt_trans hjLt' (Nat.lt_succ_self i)
            simpa [st', i] using hjSucc
        · intro k' j hj
          have hGetIns :
              (st.namedIds.insert k i)[k']? =
                if (k == k') = true then some i else st.namedIds[k']? := by
            simpa using (Std.HashMap.getElem?_insert (m := st.namedIds) (k := k) (a := k') (v := i))
          have hNamedIns : (st.namedIds.insert k i)[k']? = some j := by
            simpa [st', i] using hj
          rw [hGetIns] at hNamedIns
          by_cases hkk : k = k'
          · subst hkk
            have hEqTrue : (k == k) = true := by simp
            rw [hEqTrue] at hNamedIns
            have hjEq : j = i := by simpa using (Option.some.inj hNamedIns).symm
            subst hjEq
            simpa [st', i] using hIdSelf
          · have hEqFalse : (k == k') = false := by simp [hkk]
            rw [hEqFalse] at hNamedIns
            have hOld : st.namedIds[k']? = some j := by simpa using hNamedIns
            have hOldId : st.idToNamed[j]? = some k' := hInv.2 hOld
            have hji : j ≠ i := by
              intro hji
              subst hji
              have hiLt : st.nextId > i := hInv.1 hOldId
              omega
            have hij : ¬ i = j := by
              intro hij
              exact hji hij.symm
            have hEqNatFalse : (i == j) = false := by simp [hij]
            have hGetIdIns :
                (st.idToNamed.insert i k)[j]? =
                  if (i == j) = true then some k else st.idToNamed[j]? := by
              simpa using (Std.HashMap.getElem?_insert (m := st.idToNamed) (k := i) (a := j) (v := k))
            rw [hGetIdIns, hEqNatFalse]
            simpa [st', i] using hOldId
      have hRet : st'.idToNamed[i]? = some k := by
        simpa [st', i] using hIdSelf
      have hRun : (idForPy k).run st = (i, st') := by
        simp [idForPy, hget, i, st']
        rfl
      constructor
      · simpa [hRun] using hInv'
      · simpa [hRun] using hRet

private lemma pyStateInv_rOldIdPy {st : PyEncState} {n u v : Nat}
    (hInv : PyStateInv st) :
    PyStateInv ((rOldIdPy n u v).run st).2 ∧
      ((rOldIdPy n u v).run st).2.idToNamed[((rOldIdPy n u v).run st).1]? =
        some (.r (orderedCodePair n u v).1 (orderedCodePair n u v).2) := by
  unfold rOldIdPy
  simpa using pyStateInv_idForPy
    (st := st) (k := .r (orderedCodePair n u v).1 (orderedCodePair n u v).2) hInv

private lemma pyStateInv_pcIdPy {st : PyEncState} {isRed : Bool} {u v s : Nat}
    (hInv : PyStateInv st) :
    PyStateInv ((pcIdPy isRed u v s).run st).2 ∧
      ((pcIdPy isRed u v s).run st).2.idToNamed[((pcIdPy isRed u v s).run st).1]? =
        some (.pc isRed u v s) := by
  unfold pcIdPy
  simpa using pyStateInv_idForPy (st := st) (k := .pc isRed u v s) hInv

private lemma pyStateInv_pcLitPy {st : PyEncState} {isRed : Bool} {u v s : Nat}
    (hInv : PyStateInv st) :
    PyStateInv ((pcLitPy isRed u v s).run st).2 ∧
      ((pcLitPy isRed u v s).run st).2.idToNamed[((pcLitPy isRed u v s).run st).1.natAbs]? =
        some (.pc isRed u v s) := by
  unfold pcLitPy
  simpa using pyStateInv_pcIdPy (st := st) (isRed := isRed) (u := u) (v := v) (s := s) hInv

private lemma pyStateInv_rLitPy {st : PyEncState} {n u v : Nat}
    (hInv : PyStateInv st) :
    let p := orderedCodePair n u v
    let a := p.1
    let b := p.2
    ((rLitPy n u v).run st).2.idToNamed[((rLitPy n u v).run st).1.natAbs]? =
      some (if vLt n a (antipodeCode n b) = true
        then .r (orderedCodePair n a b).1 (orderedCodePair n a b).2
        else .r (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).1
                 (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).2) := by
  let p := orderedCodePair n u v
  let a := p.1
  let b := p.2
  by_cases hlt : vLt n a (antipodeCode n b) = true
  · have hR :
      ((rOldIdPy n a b).run st).2.idToNamed.get? ((rOldIdPy n a b).run st).1 =
        some (.r (orderedCodePair n a b).1 (orderedCodePair n a b).2) := by
      exact (pyStateInv_rOldIdPy (st := st) (n := n) (u := a) (v := b) hInv).2
    simpa [rLitPy, a, b, p, hlt] using hR
  · have hR :
      ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2.idToNamed.get?
        ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1 =
        some (.r (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).1
                 (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).2) := by
      exact (pyStateInv_rOldIdPy (st := st) (n := n)
        (u := antipodeCode n a) (v := antipodeCode n b) hInv).2
    have hRun :
        (rLitPy n u v).run st =
          (-Int.ofNat ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1,
            ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2) := by
      unfold rLitPy
      simp [a, b, p, hlt]
      rfl
    rw [hRun]
    simpa [a, b, p, hlt] using hR

private lemma pyStateInv_rLitPy_inv {st : PyEncState} {n u v : Nat}
    (hInv : PyStateInv st) :
    PyStateInv ((rLitPy n u v).run st).2 := by
  let p := orderedCodePair n u v
  let a := p.1
  let b := p.2
  by_cases hlt : vLt n a (antipodeCode n b) = true
  · have hR : PyStateInv ((rOldIdPy n a b).run st).2 :=
      (pyStateInv_rOldIdPy (st := st) (n := n) (u := a) (v := b) hInv).1
    simpa [rLitPy, a, b, p, hlt] using hR
  · have hR : PyStateInv ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2 :=
      (pyStateInv_rOldIdPy (st := st) (n := n)
        (u := antipodeCode n a) (v := antipodeCode n b) hInv).1
    have hRun :
        (rLitPy n u v).run st =
          (-Int.ofNat ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1,
            ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2) := by
      unfold rLitPy
      simp [a, b, p, hlt]
      rfl
    rw [hRun]
    simpa using hR

private def pyVarSemantics (n : Nat) (c : EdgeColoring n) : PyVarKey → Prop
  | .r u v =>
      c (edgeOf (natToVertex n u) (natToVertex n v)) = true
  | .pc true u v 0 =>
      RedGeodesicExists c (natToVertex n u) (natToVertex n v)
  | .pc true _ _ (_ + 1) =>
      False
  | .pc false _ _ _ =>
      True

private lemma pyVarSemantics_pc0_of_adj_red {n : Nat} {c : EdgeColoring n}
    {u v : Nat}
    (hAdj : Adj (natToVertex n u) (natToVertex n v))
    (hRed : pyVarSemantics n c (.r u v)) :
    pyVarSemantics n c (.pc true u v 0) := by
  unfold pyVarSemantics at hRed ⊢
  refine ⟨hAdj.toWalk, ?_, ?_⟩
  · have hDist : dist (natToVertex n u) (natToVertex n v) = 1 := by
      simpa [dist, Adj, ThreeColorSAT.Hypercube.Q] using hAdj
    simpa [hDist] using (SimpleGraph.Walk.length_eq_one_iff.mpr hAdj)
  · intro e he
    have hEdge : e = edgeOf (natToVertex n u) (natToVertex n v) := by
      simpa [edgeOf] using he
    simpa [hEdge] using hRed

private lemma pyVarSemantics_pc0_step_of_pc0_red {n : Nat} {c : EdgeColoring n}
    {u v w : Nat}
    (hPcUV : pyVarSemantics n c (.pc true u v 0))
    (hAdjVW : Adj (natToVertex n v) (natToVertex n w))
    (hStep : distCode n u v + 1 = distCode n u w)
    (hRedVW : pyVarSemantics n c (.r v w)) :
    pyVarSemantics n c (.pc true u w 0) := by
  unfold pyVarSemantics at hPcUV hRedVW ⊢
  rcases hPcUV with ⟨p, hpLen, hpRed⟩
  refine ⟨p.append hAdjVW.toWalk, ?_, ?_⟩
  · rw [SimpleGraph.Walk.length_append, hpLen]
    have hStep' :
        dist (natToVertex n u) (natToVertex n v) + 1 =
          dist (natToVertex n u) (natToVertex n w) :=
      distCode_step_implies_dist_step n u v w hStep
    simpa [hStep'] using rfl
  · intro e he
    rw [SimpleGraph.Walk.edges_append] at he
    rcases List.mem_append.mp he with he | he
    · exact hpRed e he
    · have hEdge : e = edgeOf (natToVertex n v) (natToVertex n w) := by
        simpa [edgeOf] using he
      simpa [hEdge] using hRedVW

private lemma not_pyVarSemantics_pc_antipode_of_noGeo {n : Nat} {c : EdgeColoring n}
    (hNoGeo : NoMonochromaticAntipodalGeodesic n c) {u : Nat}
    (hu : u ∈ allVertexCodes n) :
    ¬ pyVarSemantics n c (.pc true u (antipodeCode n u) 0) := by
  intro hPc
  rcases hPc with ⟨p, hpLen, hpRed⟩
  let v : Vertex n := natToVertex n u
  have hAntiV : natToVertex n (antipodeCode n u) = antipode v := by
    simpa [v] using natToVertex_antipodeCode_eq_antipode_of_mem (n := n) (u := u) hu
  let p' : (ThreeColorSAT.Hypercube.Q n).Walk v (antipode v) := p.copy rfl hAntiV
  have hp'Mono : WalkMonochromatic c p' := by
    exact (walkMonochromatic_copy_iff (c := c) (p := p) (hu := rfl) (hv := hAntiV)).2
      (walkMonochromatic_of_allRed (c := c) hpRed)
  have hp'Len : p'.length = dist v (antipode v) := by
    simpa [p', hAntiV, v] using hpLen
  exact hNoGeo v p' hp'Len hp'Mono

private lemma pyVarSemantics_r_antipode_not {n : Nat} {c : EdgeColoring n}
    (hAnti : IsAntipodalColoring c)
    {u v : Nat}
    (hu : u ∈ allVertexCodes n) (hv : v ∈ allVertexCodes n)
    (hAdj : Adj (natToVertex n u) (natToVertex n v)) :
    pyVarSemantics n c (.r u v) ↔
      ¬ pyVarSemantics n c (.r (antipodeCode n u) (antipodeCode n v)) := by
  let vu : Vertex n := natToVertex n u
  let vv : Vertex n := natToVertex n v
  have huAnti : natToVertex n (antipodeCode n u) = antipode vu := by
    simpa [vu] using natToVertex_antipodeCode_eq_antipode_of_mem (n := n) (u := u) hu
  have hvAnti : natToVertex n (antipodeCode n v) = antipode vv := by
    simpa [vv] using natToVertex_antipodeCode_eq_antipode_of_mem (n := n) (u := v) hv
  have hNe : c (edgeOf vu vv) ≠
      c (edgeOf (natToVertex n (antipodeCode n u)) (natToVertex n (antipodeCode n v))) := by
    simpa [huAnti, hvAnti] using hAnti vu vv hAdj
  have hComp :
      c (edgeOf (natToVertex n (antipodeCode n u)) (natToVertex n (antipodeCode n v))) =
        !(c (edgeOf vu vv)) := by
    cases hA : c (edgeOf (natToVertex n (antipodeCode n u)) (natToVertex n (antipodeCode n v))) <;>
      cases hU : c (edgeOf vu vv) <;> simp [hA, hU] at hNe ⊢
  constructor
  · intro hRed
    intro hRedAnti
    have hRedEq : c (edgeOf vu vv) = true := by simpa [pyVarSemantics, vu, vv] using hRed
    have hRedAntiEq :
        c (edgeOf (natToVertex n (antipodeCode n u)) (natToVertex n (antipodeCode n v))) = true := by
      simpa [pyVarSemantics] using hRedAnti
    rw [hComp, hRedEq] at hRedAntiEq
    simp at hRedAntiEq
  · intro hNotRedAnti
    by_cases hRedEq : c (edgeOf vu vv) = true
    · simpa [pyVarSemantics, vu, vv] using hRedEq
    · exfalso
      have hNotTrue : c (edgeOf vu vv) ≠ true := hRedEq
      have hFalse : c (edgeOf vu vv) = false := by
        cases hVal : c (edgeOf vu vv) <;> simp [hVal] at hNotTrue ⊢
      have hRedAnti : pyVarSemantics n c (.r (antipodeCode n u) (antipodeCode n v)) := by
        show c (edgeOf (natToVertex n (antipodeCode n u)) (natToVertex n (antipodeCode n v))) = true
        rw [hComp, hFalse]
        simp
      exact hNotRedAnti hRedAnti

private lemma pySem_clause_antipodal_left {n : Nat} {c : EdgeColoring n}
    (hAnti : IsAntipodalColoring c)
    {u v : Nat}
    (hu : u ∈ allVertexCodes n) (hv : v ∈ allVertexCodes n)
    (hAdj : Adj (natToVertex n u) (natToVertex n v)) :
    ¬ pyVarSemantics n c (.r u v) ∨
      ¬ pyVarSemantics n c (.r (antipodeCode n u) (antipodeCode n v)) := by
  by_cases hRed : pyVarSemantics n c (.r u v)
  · right
    exact (pyVarSemantics_r_antipode_not (n := n) (c := c) hAnti hu hv hAdj).1 hRed
  · left
    exact hRed

private lemma pySem_clause_antipodal_right {n : Nat} {c : EdgeColoring n}
    (hAnti : IsAntipodalColoring c)
    {u v : Nat}
    (hu : u ∈ allVertexCodes n) (hv : v ∈ allVertexCodes n)
    (hAdj : Adj (natToVertex n u) (natToVertex n v)) :
    pyVarSemantics n c (.r u v) ∨
      pyVarSemantics n c (.r (antipodeCode n u) (antipodeCode n v)) := by
  classical
  by_cases hRed : pyVarSemantics n c (.r u v)
  · exact Or.inl hRed
  · right
    have hNotNotAnti :
        ¬¬ pyVarSemantics n c (.r (antipodeCode n u) (antipodeCode n v)) := by
      intro hNotAnti
      exact hRed
        ((pyVarSemantics_r_antipode_not (n := n) (c := c) hAnti hu hv hAdj).2 hNotAnti)
    exact Classical.not_not.mp hNotNotAnti

private lemma pySem_clause_eq5 {n : Nat} {c : EdgeColoring n}
    {u v : Nat}
    (hAdj : Adj (natToVertex n u) (natToVertex n v)) :
    ¬ pyVarSemantics n c (.r u v) ∨
      pyVarSemantics n c (.pc true u v 0) := by
  by_cases hRed : pyVarSemantics n c (.r u v)
  · right
    exact pyVarSemantics_pc0_of_adj_red (n := n) (c := c) hAdj hRed
  · left
    exact hRed

private lemma pySem_clause_eq7 {n : Nat} {c : EdgeColoring n}
    {u v w : Nat}
    (hAdjVW : Adj (natToVertex n v) (natToVertex n w))
    (hStep : distCode n u v + 1 = distCode n u w) :
    ¬ pyVarSemantics n c (.pc true u v 0) ∨
      ¬ pyVarSemantics n c (.r v w) ∨
      pyVarSemantics n c (.pc true u w 0) := by
  by_cases hPcUV : pyVarSemantics n c (.pc true u v 0)
  · by_cases hRedVW : pyVarSemantics n c (.r v w)
    · exact Or.inr (Or.inr
        (pyVarSemantics_pc0_step_of_pc0_red (n := n) (c := c) hPcUV hAdjVW hStep hRedVW))
    · exact Or.inr (Or.inl hRedVW)
  · exact Or.inl hPcUV

private lemma pySem_clause_conjecture1 {n : Nat} {c : EdgeColoring n}
    (hNoGeo : NoMonochromaticAntipodalGeodesic n c)
    {u : Nat} (hu : u ∈ allVertexCodes n) :
    ¬ pyVarSemantics n c (.pc true u (antipodeCode n u) 0) :=
  not_pyVarSemantics_pc_antipode_of_noGeo (n := n) (c := c) hNoGeo hu

private def pyAssignmentAt (st : PyEncState) (n : Nat) (c : EdgeColoring n)
    (aux : Nat → Prop) : CNF.Assignment Nat := fun i =>
  match st.idToNamed.get? i with
  | some k => pyVarSemantics n c k
  | none => aux i

private def pyAssignment (n : Nat) (c : EdgeColoring n)
    (aux : Nat → Prop) : CNF.Assignment Nat :=
  pyAssignmentAt (pysatState n) n c aux

private lemma edgeOf_orderedCodePair_eq (n x y : Nat) :
    edgeOf (natToVertex n (orderedCodePair n x y).1) (natToVertex n (orderedCodePair n x y).2) =
      edgeOf (natToVertex n x) (natToVertex n y) := by
  unfold orderedCodePair
  by_cases hxy : vLe n x y
  · simp [hxy, edgeOf, Sym2.eq_swap]
  · simp [hxy, edgeOf, Sym2.eq_swap]

private lemma pyVarSemantics_r_orderedCodePair {n : Nat} {c : EdgeColoring n} (x y : Nat) :
    pyVarSemantics n c (.r (orderedCodePair n x y).1 (orderedCodePair n x y).2) ↔
      pyVarSemantics n c (.r x y) := by
  simpa [pyVarSemantics, edgeOf_orderedCodePair_eq] using
    Iff.rfl (α := c (edgeOf (natToVertex n (orderedCodePair n x y).1)
      (natToVertex n (orderedCodePair n x y).2)) = true)

private lemma pyAssignmentAt_named {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {i : Nat} {k : PyVarKey}
    (h : st.idToNamed[i]? = some k) :
    pyAssignmentAt st n c aux i ↔ pyVarSemantics n c k := by
  simp [pyAssignmentAt, h]

private lemma pyAssignmentAt_aux {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {i : Nat}
    (h : st.idToNamed[i]? = none) :
    pyAssignmentAt st n c aux i ↔ aux i := by
  simp [pyAssignmentAt, h]

private lemma pyStateInv_idToNamed_nextId_none {st : PyEncState}
    (hInv : PyStateInv st) :
    st.idToNamed[st.nextId]? = none := by
  cases hget : st.idToNamed[st.nextId]? with
  | none =>
      rfl
  | some k =>
      have hlt : st.nextId < st.nextId := hInv.1 hget
      exact False.elim ((Nat.lt_irrefl st.nextId) hlt)

private lemma pyAssignmentAt_update_nextId_eq_of_lt
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) (v : Prop) {i : Nat}
    (hi : i < st.nextId) :
    pyAssignmentAt st n c (Function.update aux st.nextId v) i ↔
      pyAssignmentAt st n c aux i := by
  unfold pyAssignmentAt
  cases hget : st.idToNamed[i]? with
  | some k =>
      simp [hget]
  | none =>
      have hne : i ≠ st.nextId := Nat.ne_of_lt hi
      simp [hget, Function.update, hne]

private lemma pyLitSat_update_nextId_eq_of_bound
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) (v : Prop) {i : Int}
    (hi : i.natAbs < st.nextId) :
    CNF.Lit.Sat (pyAssignmentAt st n c (Function.update aux st.nextId v)) (litOfDimacsInt i) ↔
      CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i) := by
  cases i with
  | ofNat j =>
      have hj : j < st.nextId := by simpa using hi
      simpa [litOfDimacsInt, CNF.Lit.Sat] using
        (pyAssignmentAt_update_nextId_eq_of_lt
          (st := st) (n := n) (c := c) aux v (i := j) hj)
  | negSucc j =>
      have hj : Nat.succ j < st.nextId := by simpa using hi
      simpa [litOfDimacsInt, CNF.Lit.Sat] using
        (not_congr
          (pyAssignmentAt_update_nextId_eq_of_lt
            (st := st) (n := n) (c := c) aux v (i := Nat.succ j) hj))

private lemma pyLitSat_pos_named_at {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {i : Nat} {k : PyVarKey}
    (h : st.idToNamed[i]? = some k) :
    CNF.Lit.Sat (pyAssignmentAt st n c aux) (.pos i) ↔ pyVarSemantics n c k := by
  simpa [CNF.Lit.Sat] using pyAssignmentAt_named (st := st) (n := n) (c := c) aux h

private lemma pyLitSat_neg_named_at {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {i : Nat} {k : PyVarKey}
    (h : st.idToNamed[i]? = some k) :
    CNF.Lit.Sat (pyAssignmentAt st n c aux) (.neg i) ↔ ¬ pyVarSemantics n c k := by
  simpa [CNF.Lit.Sat] using
    (not_congr (pyAssignmentAt_named (st := st) (n := n) (c := c) aux h))

private lemma rOldIdPy_ne_zero {st : PyEncState} {n u v : Nat}
    (hInv : PyStateInv st)
    (hNoZero : st.idToNamed[0]? = none)
    (hNextPos : 0 < st.nextId) :
    ((rOldIdPy n u v).run st).1 ≠ 0 := by
  let k : PyVarKey := .r (orderedCodePair n u v).1 (orderedCodePair n u v).2
  unfold rOldIdPy
  change ((idForPy k).run st).1 ≠ 0
  cases hget : st.namedIds[k]? with
  | some i =>
      have hId : st.idToNamed[i]? = some k := hInv.2 hget
      have hiNe0 : i ≠ 0 := by
        intro hi0
        have hId0 : st.idToNamed[0]? = some k := by simpa [hi0] using hId
        simpa [hNoZero] using hId0
      simpa [idForPy, hget] using hiNe0
  | none =>
      simpa [idForPy, hget] using (Nat.ne_of_gt hNextPos)

private lemma rLitPy_ne_zero {st : PyEncState} {n u v : Nat}
    (hInv : PyStateInv st)
    (hNoZero : st.idToNamed[0]? = none)
    (hNextPos : 0 < st.nextId) :
    ((rLitPy n u v).run st).1 ≠ 0 := by
  let p := orderedCodePair n u v
  let a := p.1
  let b := p.2
  by_cases hlt : vLt n a (antipodeCode n b) = true
  · have hRun :
      (rLitPy n u v).run st =
        (Int.ofNat ((rOldIdPy n a b).run st).1, ((rOldIdPy n a b).run st).2) := by
      unfold rLitPy
      simp [p, a, b, hlt]
      rfl
    have hRidNe0 :
        ((rOldIdPy n a b).run st).1 ≠ 0 :=
      rOldIdPy_ne_zero (st := st) (n := n) (u := a) (v := b) hInv hNoZero hNextPos
    cases hRid : ((rOldIdPy n a b).run st).1 with
    | zero =>
        exact False.elim (hRidNe0 hRid)
    | succ k =>
        have hkne : Int.ofNat (Nat.succ k) ≠ 0 := by
          change ¬ (((k : Nat) : Int) + 1 = 0)
          omega
        simpa [hRun, hRid] using hkne
  · have hRun :
      (rLitPy n u v).run st =
        (-Int.ofNat ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1,
          ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2) := by
      unfold rLitPy
      simp [p, a, b, hlt]
      rfl
    have hRidNe0 :
        ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1 ≠ 0 :=
      rOldIdPy_ne_zero (st := st) (n := n)
        (u := antipodeCode n a) (v := antipodeCode n b) hInv hNoZero hNextPos
    cases hRid : ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1 with
    | zero =>
        exact False.elim (hRidNe0 hRid)
    | succ k =>
        have hkne : Int.ofNat (Nat.succ k) ≠ 0 := by
          change ¬ (((k : Nat) : Int) + 1 = 0)
          omega
        have hNegNe : -Int.ofNat (Nat.succ k) ≠ 0 := by
          exact neg_ne_zero.mpr hkne
        simpa [hRun, hRid] using hNegNe

private lemma pyLitSat_rLitPy_iff_red_at
    {st : PyEncState} {n : Nat} {c : EdgeColoring n} (aux : Nat → Prop)
    (hInv : PyStateInv st) (hAnti : IsAntipodalColoring c)
    (hNoZero : st.idToNamed[0]? = none) (hNextPos : 0 < st.nextId)
    {u v : Nat}
    (hu : u ∈ allVertexCodes n) (hv : v ∈ allVertexCodes n)
    (hAdj : Adj (natToVertex n u) (natToVertex n v)) :
    CNF.Lit.Sat (pyAssignmentAt ((rLitPy n u v).run st).2 n c aux)
      (litOfDimacsInt ((rLitPy n u v).run st).1)
      ↔ pyVarSemantics n c (.r u v) := by
  let p := orderedCodePair n u v
  let a := p.1
  let b := p.2
  have hA_mem : a ∈ allVertexCodes n := by
    unfold a p orderedCodePair
    by_cases hle : vLe n u v
    · simpa [hle] using hu
    · simpa [hle] using hv
  have hB_mem : b ∈ allVertexCodes n := by
    unfold b p orderedCodePair
    by_cases hle : vLe n u v
    · simpa [hle] using hv
    · simpa [hle] using hu
  have hAdjAB : Adj (natToVertex n a) (natToVertex n b) := by
    unfold a b p orderedCodePair
    by_cases hle : vLe n u v
    · simpa [hle] using hAdj
    · simpa [hle] using hAdj.symm
  have hSemAB :
      pyVarSemantics n c (.r a b) ↔ pyVarSemantics n c (.r u v) := by
    simpa [a, b, p] using (pyVarSemantics_r_orderedCodePair (n := n) (c := c) u v)
  by_cases hlt : vLt n a (antipodeCode n b) = true
  · have hRun :
      (rLitPy n u v).run st =
        (Int.ofNat ((rOldIdPy n a b).run st).1, ((rOldIdPy n a b).run st).2) := by
      unfold rLitPy
      simp [a, b, p, hlt]
      rfl
    rw [hRun]
    have hNamed :
        ((rOldIdPy n a b).run st).2.idToNamed[((rOldIdPy n a b).run st).1]? =
          some (.r (orderedCodePair n a b).1 (orderedCodePair n a b).2) :=
      (pyStateInv_rOldIdPy (st := st) (n := n) (u := a) (v := b) hInv).2
    have hSat :
        CNF.Lit.Sat (pyAssignmentAt ((rOldIdPy n a b).run st).2 n c aux)
          (litOfDimacsInt (Int.ofNat ((rOldIdPy n a b).run st).1))
          ↔ pyVarSemantics n c (.r (orderedCodePair n a b).1 (orderedCodePair n a b).2) := by
      simpa [litOfDimacsInt, CNF.Lit.Sat] using
        (pyLitSat_pos_named_at
          (st := ((rOldIdPy n a b).run st).2) (n := n) (c := c) aux
          (i := ((rOldIdPy n a b).run st).1)
          (k := .r (orderedCodePair n a b).1 (orderedCodePair n a b).2) hNamed)
    have hSemABOrd :
        pyVarSemantics n c (.r (orderedCodePair n a b).1 (orderedCodePair n a b).2)
          ↔ pyVarSemantics n c (.r a b) := by
      simpa using (pyVarSemantics_r_orderedCodePair (n := n) (c := c) a b)
    exact hSat.trans (hSemABOrd.trans hSemAB)
  · have hRun :
      (rLitPy n u v).run st =
        (-Int.ofNat ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1,
          ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2) := by
      unfold rLitPy
      simp [a, b, p, hlt]
      rfl
    rw [hRun]
    have hNamed :
        (((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2.idToNamed).get?
          ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1 =
            some (.r (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).1
              (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).2) := by
      simpa using
        (pyStateInv_rOldIdPy (st := st) (n := n)
          (u := antipodeCode n a) (v := antipodeCode n b) hInv).2
    have hSat :
        CNF.Lit.Sat
            (pyAssignmentAt ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2 n c aux)
            (litOfDimacsInt (-Int.ofNat ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1))
          ↔ ¬ pyVarSemantics n c
            (.r (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).1
              (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).2) := by
      have hNe0 :
          ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1 ≠ 0 :=
        rOldIdPy_ne_zero (st := st) (n := n) (u := antipodeCode n a) (v := antipodeCode n b)
          hInv hNoZero hNextPos
      have hPos :
          0 < ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1 :=
        Nat.pos_of_ne_zero hNe0
      simpa [litOfDimacsInt, CNF.Lit.Sat, hPos] using
        (pyLitSat_neg_named_at
          (st := ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).2)
          (n := n) (c := c) aux
          (i := ((rOldIdPy n (antipodeCode n a) (antipodeCode n b)).run st).1)
          (k := .r (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).1
            (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).2) hNamed)
    have hSemAntiOrd :
        pyVarSemantics n c
          (.r (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).1
            (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).2)
          ↔ pyVarSemantics n c (.r (antipodeCode n a) (antipodeCode n b)) := by
      simpa using
        (pyVarSemantics_r_orderedCodePair (n := n) (c := c) (antipodeCode n a) (antipodeCode n b))
    have hSemABAnti :
        pyVarSemantics n c (.r a b) ↔
          ¬ pyVarSemantics n c (.r (antipodeCode n a) (antipodeCode n b)) :=
      pyVarSemantics_r_antipode_not (n := n) (c := c) hAnti hA_mem hB_mem hAdjAB
    exact hSat.trans ((not_congr hSemAntiOrd).trans (hSemABAnti.symm.trans hSemAB))

private def PyIntClauseSatAt (st : PyEncState) (n : Nat) (c : EdgeColoring n)
    (aux : Nat → Prop) : Prop :=
  ∀ cl, cl ∈ st.clauses →
    ∃ i : Int, i ∈ cl.toList ∧
      CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i)

private def PyIntClauseBound (st : PyEncState) : Prop :=
  ∀ cl, cl ∈ st.clauses →
    ∀ i : Int, i ∈ cl.toList → i.natAbs < st.nextId

private lemma pyIntClauseSatAt_empty {n : Nat} {c : EdgeColoring n} (aux : Nat → Prop) :
    PyIntClauseSatAt ({} : PyEncState) n c aux := by
  intro cl hcl
  simpa using hcl

private lemma pyIntClauseBound_empty :
    PyIntClauseBound ({} : PyEncState) := by
  intro cl hcl
  simpa using hcl

private lemma pyAssignmentAt_pushClausePy_eq {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {cl : List Int} {i : Nat} :
    pyAssignmentAt ((pushClausePy cl).run st).2 n c aux i ↔
      pyAssignmentAt st n c aux i := by
  rcases st with ⟨nextId, namedIds, idToNamed, clauses⟩
  rfl

private lemma pyAssignmentAt_pushClausePy_eq_fun {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {cl : List Int} :
    pyAssignmentAt ((pushClausePy cl).run st).2 n c aux =
      pyAssignmentAt st n c aux := by
  funext i
  exact propext (pyAssignmentAt_pushClausePy_eq (st := st) (n := n) (c := c) aux
    (cl := cl) (i := i))

private lemma pyLitSat_pushClausePy_eq {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {cl : List Int} {i : Int} :
    CNF.Lit.Sat (pyAssignmentAt ((pushClausePy cl).run st).2 n c aux) (litOfDimacsInt i) ↔
      CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i) := by
  cases i with
  | ofNat j =>
      simpa [litOfDimacsInt, CNF.Lit.Sat] using
        (pyAssignmentAt_pushClausePy_eq (st := st) (n := n) (c := c) aux
          (cl := cl) (i := j))
  | negSucc j =>
      simpa [litOfDimacsInt, CNF.Lit.Sat] using
        (not_congr
          (pyAssignmentAt_pushClausePy_eq (st := st) (n := n) (c := c) aux
            (cl := cl) (i := Nat.succ j)))

private lemma pyIntClauseSatAt_pushClausePy {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {cl : List Int}
    (hSat : PyIntClauseSatAt st n c aux)
    (hNew :
      ∃ i : Int, i ∈ cl ∧
        CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i)) :
    PyIntClauseSatAt ((pushClausePy cl).run st).2 n c aux := by
  intro cl' hcl'
  change cl' ∈ st.clauses.push cl.toArray at hcl'
  have hMem : cl' ∈ st.clauses ∨ cl' = cl.toArray :=
    Array.mem_push.mp hcl'
  rcases hMem with hOld | rfl
  · rcases hSat cl' hOld with ⟨i, hiMem, hiSat⟩
    refine ⟨i, ?_, ?_⟩
    · exact hiMem
    · exact (pyLitSat_pushClausePy_eq (st := st) (n := n) (c := c) aux
        (cl := cl) (i := i)).2 hiSat
  ·
    rcases hNew with ⟨i, hiMem, hiSat⟩
    refine ⟨i, ?_, ?_⟩
    · simpa using hiMem
    · exact (pyLitSat_pushClausePy_eq (st := st) (n := n) (c := c) aux
        (cl := cl) (i := i)).2 hiSat

private lemma pyIntClauseBound_pushClausePy {st : PyEncState} {cl : List Int}
    (hBound : PyIntClauseBound st)
    (hClBound : ∀ i : Int, i ∈ cl → i.natAbs < st.nextId) :
    PyIntClauseBound ((pushClausePy cl).run st).2 := by
  intro cl' hcl' i hi
  change cl' ∈ st.clauses.push cl.toArray at hcl'
  have hMem : cl' ∈ st.clauses ∨ cl' = cl.toArray :=
    Array.mem_push.mp hcl'
  rcases hMem with hOld | rfl
  · exact hBound cl' hOld i hi
  · exact hClBound i (by simpa using hi)

private lemma pyAssignmentAt_freshIdPy_eq {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {i : Nat} :
    pyAssignmentAt (freshIdPy.run st).2 n c aux i ↔
      pyAssignmentAt st n c aux i := by
  rcases st with ⟨nextId, namedIds, idToNamed, clauses⟩
  rfl

private lemma pyAssignmentAt_freshIdPy_eq_fun {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) :
    pyAssignmentAt (freshIdPy.run st).2 n c aux =
      pyAssignmentAt st n c aux := by
  funext i
  exact propext (pyAssignmentAt_freshIdPy_eq (st := st) (n := n) (c := c) aux (i := i))

private lemma pyLitSat_freshIdPy_eq {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {i : Int} :
    CNF.Lit.Sat (pyAssignmentAt (freshIdPy.run st).2 n c aux) (litOfDimacsInt i) ↔
      CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i) := by
  cases i with
  | ofNat j =>
      simpa [litOfDimacsInt, CNF.Lit.Sat] using
        (pyAssignmentAt_freshIdPy_eq (st := st) (n := n) (c := c) aux (i := j))
  | negSucc j =>
      simpa [litOfDimacsInt, CNF.Lit.Sat] using
        (not_congr
          (pyAssignmentAt_freshIdPy_eq (st := st) (n := n) (c := c) aux (i := Nat.succ j)))

private lemma pyIntClauseBound_freshIdPy {st : PyEncState}
    (hBound : PyIntClauseBound st) :
    PyIntClauseBound (freshIdPy.run st).2 := by
  intro cl hcl i hi
  have hOld : cl ∈ st.clauses := by
    simpa [freshIdPy] using hcl
  have hiOld : i.natAbs < st.nextId := hBound cl hOld i hi
  change i.natAbs < st.nextId + 1
  exact Nat.lt_succ_of_lt hiOld

private lemma pyAssignmentAt_idForPy_eq_of_lt
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {k : PyVarKey} {i : Nat}
    (hi : i < st.nextId) :
    pyAssignmentAt ((idForPy k).run st).2 n c aux i ↔
      pyAssignmentAt st n c aux i := by
  cases hget : st.namedIds[k]? with
  | some j =>
      have hRun : (idForPy k).run st = pure (j, st) := by
        simp [idForPy, hget]
      rw [hRun]
      rfl
  | none =>
      let st' : PyEncState := { st with
        nextId := st.nextId + 1
        namedIds := st.namedIds.insert k st.nextId
        idToNamed := st.idToNamed.insert st.nextId k
      }
      have hRun : (idForPy k).run st = pure (st.nextId, st') := by
        simp [idForPy, hget, st']
      have hNe : st.nextId ≠ i := by exact (Nat.ne_of_lt hi).symm
      have hEqFalse : (st.nextId == i) = false := by simp [hNe]
      have hGetIns : (st.idToNamed.insert st.nextId k)[i]? = st.idToNamed[i]? := by
        have hRaw :
            (st.idToNamed.insert st.nextId k)[i]? =
              if (st.nextId == i) = true then some k else st.idToNamed[i]? := by
          simpa using
            (Std.HashMap.getElem?_insert (m := st.idToNamed)
              (k := st.nextId) (a := i) (v := k))
        simpa [hEqFalse] using hRaw
      rw [hRun]
      change
          (match (st.idToNamed.insert st.nextId k)[i]? with
            | some k' => pyVarSemantics n c k'
            | none => aux i) ↔
          (match st.idToNamed[i]? with
            | some k' => pyVarSemantics n c k'
            | none => aux i)
      rw [hGetIns]

private lemma pyLitSat_idForPy_eq_of_bound
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {k : PyVarKey} {i : Int}
    (hi : i.natAbs < st.nextId) :
    CNF.Lit.Sat (pyAssignmentAt ((idForPy k).run st).2 n c aux) (litOfDimacsInt i) ↔
      CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i) := by
  cases i with
  | ofNat j =>
      have hj : j < st.nextId := by simpa using hi
      simpa [litOfDimacsInt, CNF.Lit.Sat] using
        (pyAssignmentAt_idForPy_eq_of_lt (st := st) (n := n) (c := c) aux
          (k := k) (i := j) hj)
  | negSucc j =>
      have hj : Nat.succ j < st.nextId := by simpa using hi
      simpa [litOfDimacsInt, CNF.Lit.Sat] using
        (not_congr
          (pyAssignmentAt_idForPy_eq_of_lt (st := st) (n := n) (c := c) aux
            (k := k) (i := Nat.succ j) hj))

private lemma pyLitSat_rLitPy_eq_of_bound
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {u v : Nat} {i : Int}
    (hi : i.natAbs < st.nextId) :
    CNF.Lit.Sat (pyAssignmentAt ((rLitPy n u v).run st).2 n c aux) (litOfDimacsInt i) ↔
      CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i) := by
  let p := orderedCodePair n u v
  let a := p.1
  let b := p.2
  by_cases hlt : vLt n a (antipodeCode n b) = true
  · unfold rLitPy
    simp [a, b, p, hlt]
    exact pyLitSat_idForPy_eq_of_bound
      (st := st) (n := n) (c := c) aux
      (k := .r (orderedCodePair n a b).1 (orderedCodePair n a b).2)
      (i := i) hi
  · unfold rLitPy
    simp [a, b, p, hlt]
    exact pyLitSat_idForPy_eq_of_bound
      (st := st) (n := n) (c := c) aux
      (k := .r (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).1
        (orderedCodePair n (antipodeCode n a) (antipodeCode n b)).2)
      (i := i) hi

private lemma pyIntClauseSatAt_idForPy
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {k : PyVarKey}
    (hSat : PyIntClauseSatAt st n c aux)
    (hBound : PyIntClauseBound st) :
    PyIntClauseSatAt ((idForPy k).run st).2 n c aux := by
  intro cl hcl
  have hOld : cl ∈ st.clauses := by
    cases hget : st.namedIds[k]? <;> simpa [idForPy, hget] using hcl
  rcases hSat cl hOld with ⟨i, hiMem, hiSat⟩
  have hiBound : i.natAbs < st.nextId := hBound cl hOld i hiMem
  refine ⟨i, ?_, ?_⟩
  · cases hget : st.namedIds[k]? <;> simpa [idForPy, hget] using hiMem
  · exact (pyLitSat_idForPy_eq_of_bound (st := st) (n := n) (c := c) aux
      (k := k) (i := i) hiBound).2 hiSat

private lemma pyIntClauseBound_idForPy
    {st : PyEncState} {k : PyVarKey}
    (hBound : PyIntClauseBound st) :
    PyIntClauseBound ((idForPy k).run st).2 := by
  intro cl hcl i hi
  cases hget : st.namedIds[k]? with
  | some j =>
      have hRun : (idForPy k).run st = pure (j, st) := by
        simp [idForPy, hget]
      have hOld : cl ∈ st.clauses := by
        simpa [hRun] using hcl
      have hiOld : i.natAbs < st.nextId := hBound cl hOld i (by simpa [idForPy, hget] using hi)
      simpa [hRun] using hiOld
  | none =>
      let st' : PyEncState := { st with
        nextId := st.nextId + 1
        namedIds := st.namedIds.insert k st.nextId
        idToNamed := st.idToNamed.insert st.nextId k
      }
      have hRun : (idForPy k).run st = pure (st.nextId, st') := by
        simp [idForPy, hget, st']
      have hOld : cl ∈ st.clauses := by
        simpa [hRun] using hcl
      have hiOld : i.natAbs < st.nextId := hBound cl hOld i (by simpa [idForPy, hget] using hi)
      rw [hRun]
      change i.natAbs < st'.nextId
      change i.natAbs < st.nextId + 1
      exact Nat.lt_succ_of_lt hiOld

private lemma pyIntClauseSatAt_rOldIdPy {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {u v : Nat}
    (hSat : PyIntClauseSatAt st n c aux)
    (hBound : PyIntClauseBound st) :
    PyIntClauseSatAt ((rOldIdPy n u v).run st).2 n c aux := by
  unfold rOldIdPy
  simpa using
    (pyIntClauseSatAt_idForPy (st := st) (n := n) (c := c) aux
      (k := .r (orderedCodePair n u v).1 (orderedCodePair n u v).2) hSat hBound)

private lemma pyIntClauseBound_rOldIdPy {st : PyEncState} {n u v : Nat}
    (hBound : PyIntClauseBound st) :
    PyIntClauseBound ((rOldIdPy n u v).run st).2 := by
  unfold rOldIdPy
  simpa using
    (pyIntClauseBound_idForPy (st := st)
      (k := .r (orderedCodePair n u v).1 (orderedCodePair n u v).2) hBound)

private lemma pyIntClauseSatAt_pcLitPy {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {isRed : Bool} {u v s : Nat}
    (hSat : PyIntClauseSatAt st n c aux)
    (hBound : PyIntClauseBound st) :
    PyIntClauseSatAt ((pcLitPy isRed u v s).run st).2 n c aux := by
  unfold pcLitPy pcIdPy
  simpa using
    (pyIntClauseSatAt_idForPy (st := st) (n := n) (c := c) aux
      (k := .pc isRed u v s) hSat hBound)

private lemma pyIntClauseBound_pcLitPy {st : PyEncState} {isRed : Bool} {u v s : Nat}
    (hBound : PyIntClauseBound st) :
    PyIntClauseBound ((pcLitPy isRed u v s).run st).2 := by
  unfold pcLitPy pcIdPy
  simpa using
    (pyIntClauseBound_idForPy (st := st) (k := .pc isRed u v s) hBound)

private lemma pyIntClauseSatAt_rLitPy {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {u v : Nat}
    (hSat : PyIntClauseSatAt st n c aux)
    (hBound : PyIntClauseBound st) :
    PyIntClauseSatAt ((rLitPy n u v).run st).2 n c aux := by
  let p := orderedCodePair n u v
  let a := p.1
  let b := p.2
  by_cases hlt : vLt n a (antipodeCode n b) = true
  · simpa [rLitPy, a, b, p, hlt] using
      (pyIntClauseSatAt_rOldIdPy (st := st) (n := n) (c := c) aux
        (u := a) (v := b) hSat hBound)
  · simpa [rLitPy, a, b, p, hlt] using
      (pyIntClauseSatAt_rOldIdPy (st := st) (n := n) (c := c) aux
        (u := antipodeCode n a) (v := antipodeCode n b) hSat hBound)

private lemma pyIntClauseBound_rLitPy {st : PyEncState} {n u v : Nat}
    (hBound : PyIntClauseBound st) :
    PyIntClauseBound ((rLitPy n u v).run st).2 := by
  let p := orderedCodePair n u v
  let a := p.1
  let b := p.2
  by_cases hlt : vLt n a (antipodeCode n b) = true
  · simpa [rLitPy, a, b, p, hlt] using
      (pyIntClauseBound_rOldIdPy (st := st) (n := n) (u := a) (v := b) hBound)
  · simpa [rLitPy, a, b, p, hlt] using
      (pyIntClauseBound_rOldIdPy (st := st) (n := n)
        (u := antipodeCode n a) (v := antipodeCode n b) hBound)

private structure PySemInv (st : PyEncState) (n : Nat) (c : EdgeColoring n)
    (aux : Nat → Prop) : Prop where
  inv : PyStateInv st
  noZero : st.idToNamed[0]? = none
  nextPos : 0 < st.nextId
  sat : PyIntClauseSatAt st n c aux
  bound : PyIntClauseBound st

private lemma pySemInv_empty {n : Nat} {c : EdgeColoring n} (aux : Nat → Prop) :
    PySemInv ({} : PyEncState) n c aux := by
  refine ⟨pyStateInv_empty, pyState_noZero_empty, pyState_nextPos_empty,
    pyIntClauseSatAt_empty (n := n) (c := c) aux, pyIntClauseBound_empty⟩

private lemma pyIntClauseSatAt_freshIdPy_update_oldNextId
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) (v : Prop)
    (hSat : PyIntClauseSatAt st n c aux)
    (hBound : PyIntClauseBound st) :
    PyIntClauseSatAt (freshIdPy.run st).2 n c (Function.update aux st.nextId v) := by
  intro cl hcl
  have hOld : cl ∈ st.clauses := by
    simpa [freshIdPy] using hcl
  rcases hSat cl hOld with ⟨i, hiMem, hiSatOld⟩
  have hiBound : i.natAbs < st.nextId := hBound cl hOld i hiMem
  refine ⟨i, ?_, ?_⟩
  · simpa [freshIdPy] using hiMem
  · have hFreshEq :
        CNF.Lit.Sat (pyAssignmentAt (freshIdPy.run st).2 n c (Function.update aux st.nextId v))
          (litOfDimacsInt i) ↔
        CNF.Lit.Sat (pyAssignmentAt st n c (Function.update aux st.nextId v))
          (litOfDimacsInt i) :=
      pyLitSat_freshIdPy_eq
        (st := st) (n := n) (c := c) (Function.update aux st.nextId v) (i := i)
    have hUpdEq :
        CNF.Lit.Sat (pyAssignmentAt st n c (Function.update aux st.nextId v))
          (litOfDimacsInt i) ↔
        CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i) :=
      pyLitSat_update_nextId_eq_of_bound
        (st := st) (n := n) (c := c) aux v (i := i) hiBound
    exact (hFreshEq.trans hUpdEq).2 hiSatOld

private lemma pySemInv_freshIdPy_update_oldNextId
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) (v : Prop)
    (hSem : PySemInv st n c aux) :
    PySemInv (freshIdPy.run st).2 n c (Function.update aux st.nextId v) := by
  have hInvFresh : PyStateInv (freshIdPy.run st).2 :=
    pyStateInv_freshIdPy (st := st) hSem.inv
  have hNoZeroFresh : (freshIdPy.run st).2.idToNamed[0]? = none :=
    pyState_noZero_freshIdPy (st := st) hSem.noZero
  have hNextPosFresh : 0 < (freshIdPy.run st).2.nextId :=
    pyState_nextPos_freshIdPy (st := st)
  have hSatFresh :
      PyIntClauseSatAt (freshIdPy.run st).2 n c (Function.update aux st.nextId v) :=
    pyIntClauseSatAt_freshIdPy_update_oldNextId
      (st := st) (n := n) (c := c) aux v hSem.sat hSem.bound
  have hBoundFresh : PyIntClauseBound (freshIdPy.run st).2 :=
    pyIntClauseBound_freshIdPy (st := st) hSem.bound
  exact ⟨hInvFresh, hNoZeroFresh, hNextPosFresh, hSatFresh, hBoundFresh⟩

private lemma pySemInv_rOldIdPy {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {u v : Nat}
    (hSem : PySemInv st n c aux) :
    PySemInv ((rOldIdPy n u v).run st).2 n c aux := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (pyStateInv_rOldIdPy (st := st) (n := n) (u := u) (v := v) hSem.inv).1
  · exact pyState_noZero_rOldIdPy (st := st) (n := n) (u := u) (v := v) hSem.noZero hSem.nextPos
  · exact pyState_nextPos_rOldIdPy (st := st) (n := n) (u := u) (v := v) hSem.nextPos
  · exact pyIntClauseSatAt_rOldIdPy (st := st) (n := n) (c := c) aux
      (u := u) (v := v) hSem.sat hSem.bound
  · exact pyIntClauseBound_rOldIdPy (st := st) (n := n) (u := u) (v := v) hSem.bound

private lemma pySemInv_pcLitPy {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {isRed : Bool} {u v s : Nat}
    (hSem : PySemInv st n c aux) :
    PySemInv ((pcLitPy isRed u v s).run st).2 n c aux := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (pyStateInv_pcLitPy (st := st) (isRed := isRed) (u := u) (v := v) (s := s) hSem.inv).1
  · exact pyState_noZero_pcLitPy (st := st) (isRed := isRed) (u := u) (v := v) (s := s)
      hSem.noZero hSem.nextPos
  · exact pyState_nextPos_pcLitPy (st := st) (isRed := isRed) (u := u) (v := v) (s := s)
      hSem.nextPos
  · exact pyIntClauseSatAt_pcLitPy (st := st) (n := n) (c := c) aux
      (isRed := isRed) (u := u) (v := v) (s := s) hSem.sat hSem.bound
  · exact pyIntClauseBound_pcLitPy (st := st) (isRed := isRed) (u := u) (v := v) (s := s) hSem.bound

private lemma pySemInv_rLitPy {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {u v : Nat}
    (hSem : PySemInv st n c aux) :
    PySemInv ((rLitPy n u v).run st).2 n c aux := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact pyStateInv_rLitPy_inv (st := st) (n := n) (u := u) (v := v) hSem.inv
  · exact pyState_noZero_rLitPy (st := st) (n := n) (u := u) (v := v) hSem.noZero hSem.nextPos
  · exact pyState_nextPos_rLitPy (st := st) (n := n) (u := u) (v := v) hSem.nextPos
  · exact pyIntClauseSatAt_rLitPy (st := st) (n := n) (c := c) aux
      (u := u) (v := v) hSem.sat hSem.bound
  · exact pyIntClauseBound_rLitPy (st := st) (n := n) (u := u) (v := v) hSem.bound

private lemma pySemInv_pushClausePy {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {cl : List Int}
    (hSem : PySemInv st n c aux)
    (hClSat :
      ∃ i : Int, i ∈ cl ∧ CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i))
    (hClBound : ∀ i : Int, i ∈ cl → i.natAbs < st.nextId) :
    PySemInv ((pushClausePy cl).run st).2 n c aux := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact pyStateInv_pushClausePy _ _ hSem.inv
  · exact pyState_noZero_pushClausePy (st := st) (cl := cl) hSem.noZero
  · exact pyState_nextPos_pushClausePy (st := st) (cl := cl) hSem.nextPos
  · exact pyIntClauseSatAt_pushClausePy (st := st) (n := n) (c := c) aux
      (cl := cl) hSem.sat hClSat
  · exact pyIntClauseBound_pushClausePy (st := st) (cl := cl) hSem.bound hClBound

private lemma pySemInv_forIn {α β : Type} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop)
    (xs : List α) (init : β)
    (f : α → β → PyEncM (ForInStep β))
    (hStep : ∀ (a : α) (b : β) (st : PyEncState),
      PySemInv st n c aux → PySemInv ((f a b).run st).2 n c aux) :
    ∀ (st : PyEncState), PySemInv st n c aux →
      PySemInv ((forIn xs init f).run st).2 n c aux := by
  induction xs generalizing init with
  | nil =>
      intro st hSem
      simpa using hSem
  | cons a xs ih =>
      intro st hSem
      rcases hRun : (f a init).run st with ⟨s, st1⟩
      have hA : PySemInv st1 n c aux := by
        simpa [hRun] using hStep a init st hSem
      cases s with
      | done b =>
          simpa [List.forIn_cons, hRun] using hA
      | yield b =>
          have hTail : PySemInv ((forIn xs b f).run st1).2 n c aux := ih b st1 hA
          simpa [List.forIn_cons, hRun] using hTail

private lemma pySemInv_forIn_mem {α β : Type} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop)
    (xs : List α) (init : β)
    (f : α → β → PyEncM (ForInStep β))
    (hStep : ∀ (a : α), a ∈ xs →
      ∀ (b : β) (st : PyEncState),
        PySemInv st n c aux → PySemInv ((f a b).run st).2 n c aux) :
    ∀ (st : PyEncState), PySemInv st n c aux →
      PySemInv ((forIn xs init f).run st).2 n c aux := by
  induction xs generalizing init with
  | nil =>
      intro st hSem
      simpa using hSem
  | cons a xs ih =>
      intro st hSem
      rcases hRun : (f a init).run st with ⟨s, st1⟩
      have hA : PySemInv st1 n c aux := by
        simpa [hRun] using hStep a (by simp) init st hSem
      cases s with
      | done b =>
          simpa [List.forIn_cons, hRun] using hA
      | yield b =>
          have hStepTail :
              ∀ (a' : α), a' ∈ xs →
                ∀ (b' : β) (st' : PyEncState),
                  PySemInv st' n c aux →
                    PySemInv ((f a' b').run st').2 n c aux := by
            intro a' ha' b' st' hSem'
            exact hStep a' (by simp [ha']) b' st' hSem'
          have hTail :
              PySemInv ((forIn xs b f).run st1).2 n c aux :=
            ih b hStepTail st1 hA
          simpa [List.forIn_cons, hRun] using hTail

private lemma pyClauseWitness_taut {τ : CNF.Assignment Nat} {rid : Nat}
    (hNe0 : rid ≠ 0) :
    ∃ i : Int, i ∈ ([Int.ofNat rid, -Int.ofNat rid] : List Int) ∧
      CNF.Lit.Sat τ (litOfDimacsInt i) := by
  by_cases hSat : CNF.Lit.Sat τ (litOfDimacsInt (Int.ofNat rid))
  · exact ⟨Int.ofNat rid, by simp, hSat⟩
  · refine ⟨-Int.ofNat rid, by simp, ?_⟩
    have hPos : 0 < rid := Nat.pos_of_ne_zero hNe0
    have hNot : ¬ τ rid := by
      intro hr
      exact hSat (by simpa [litOfDimacsInt, CNF.Lit.Sat, hPos] using hr)
    simpa [litOfDimacsInt, CNF.Lit.Sat, hPos, hNot]

private lemma pySemInv_addEdgeInitClausesPy {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    {vs : List Nat} (aux : Nat → Prop)
    (hSem : PySemInv st n c aux) :
    PySemInv ((addEdgeInitClausesPy n vs).run st).2 n c aux := by
  let innerStep : Nat → Nat → PUnit → PyEncM (ForInStep PUnit) := fun u v _ => do
    let rid ← rOldIdPy n u v
    let r := Int.ofNat rid
    (fun _ => ForInStep.yield PUnit.unit) <$> pushClausePy [r, -r]
  have hInnerStep :
      ∀ (u : Nat) (v : Nat) (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((innerStep u v r).run st').2 n c aux := by
    intro u v r st' hSem'
    have hROld : PySemInv ((rOldIdPy n u v).run st').2 n c aux :=
      pySemInv_rOldIdPy (st := st') (n := n) (c := c) aux (u := u) (v := v) hSem'
    let rid : Nat := ((rOldIdPy n u v).run st').1
    have hRidNe0 : rid ≠ 0 := by
      exact rOldIdPy_ne_zero (st := st') (n := n) (u := u) (v := v)
        hSem'.inv hSem'.noZero hSem'.nextPos
    have hClauseSat :
        ∃ i : Int, i ∈ ([Int.ofNat rid, -Int.ofNat rid] : List Int) ∧
          CNF.Lit.Sat (pyAssignmentAt ((rOldIdPy n u v).run st').2 n c aux)
            (litOfDimacsInt i) := by
      simpa [rid] using
        (pyClauseWitness_taut
          (τ := pyAssignmentAt ((rOldIdPy n u v).run st').2 n c aux) hRidNe0)
    have hRidLt : rid < ((rOldIdPy n u v).run st').2.nextId := by
      have hNamed :
          ((rOldIdPy n u v).run st').2.idToNamed[((rOldIdPy n u v).run st').1]? =
            some (.r (orderedCodePair n u v).1 (orderedCodePair n u v).2) :=
        (pyStateInv_rOldIdPy (st := st') (n := n) (u := u) (v := v) hSem'.inv).2
      exact hROld.inv.1 hNamed
    have hClauseBound :
        ∀ i : Int, i ∈ ([Int.ofNat rid, -Int.ofNat rid] : List Int) →
          i.natAbs < ((rOldIdPy n u v).run st').2.nextId := by
      intro i hi
      rcases List.mem_cons.1 hi with hi | hi
      · have hiEq : i = Int.ofNat rid := hi
        subst hiEq
        simpa [rid] using hRidLt
      · have hiTail : i = -Int.ofNat rid := by
          simpa using hi
        subst hiTail
        simpa [rid]
          using hRidLt
    have hPush :
        PySemInv
          ((pushClausePy [Int.ofNat rid, -Int.ofNat rid]).run
            ((rOldIdPy n u v).run st').2).2 n c aux :=
      pySemInv_pushClausePy
        (st := ((rOldIdPy n u v).run st').2) (n := n) (c := c) aux
        (cl := [Int.ofNat rid, -Int.ofNat rid]) hROld hClauseSat hClauseBound
    simpa [innerStep, rid, Bind.bind, pure] using hPush
  let outerStep : Nat → PUnit → PyEncM (ForInStep PUnit) := fun u _ =>
    let inner := forIn (neighborsCode n u) PUnit.unit (innerStep u)
    inner.bind fun _ => StateT.pure (ForInStep.yield PUnit.unit)
  have hOuterStep :
      ∀ (u : Nat) (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((outerStep u r).run st').2 n c aux := by
    intro u r st' hSem'
    have hInnerFor :
        PySemInv ((forIn (neighborsCode n u) PUnit.unit (innerStep u)).run st').2 n c aux :=
      pySemInv_forIn (n := n) (c := c) (aux := aux)
        (xs := neighborsCode n u) (init := PUnit.unit) (f := innerStep u)
        (hStep := hInnerStep u) st' hSem'
    have hInnerYield :
        PySemInv
          (((forIn (neighborsCode n u) PUnit.unit (innerStep u)).bind
            fun _ => StateT.pure (ForInStep.yield PUnit.unit)).run st').2 n c aux := by
      simpa [Bind.bind, pure] using hInnerFor
    simpa [outerStep] using hInnerYield
  have hFor :
      PySemInv ((forIn vs PUnit.unit outerStep).run st).2 n c aux :=
    pySemInv_forIn (n := n) (c := c) (aux := aux)
      (xs := vs) (init := PUnit.unit) (f := outerStep) (hStep := hOuterStep) st hSem
  have hForUnit :
      PySemInv (((forIn vs PUnit.unit outerStep).bind fun _ => StateT.pure PUnit.unit).run st).2 n c aux := by
    simpa [Bind.bind, pure] using hFor
  unfold addEdgeInitClausesPy
  simpa [outerStep, innerStep, Bind.bind, pure] using hForUnit

private lemma pySemInv_addConjecture1UnitClausesPy
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    {vs : List Nat} (aux : Nat → Prop)
    (hNoGeo : NoMonochromaticAntipodalGeodesic n c)
    (hVsMem : ∀ u : Nat, u ∈ vs → u ∈ allVertexCodes n)
    (hSem : PySemInv st n c aux) :
    PySemInv ((addConjecture1UnitClausesPy n vs).run st).2 n c aux := by
  let step : Nat → PUnit → PyEncM (ForInStep PUnit) := fun u _ =>
    if vLt n (antipodeCode n u) u then
      pure (ForInStep.yield PUnit.unit)
    else do
      let p ← pcLitPy true u (antipodeCode n u) 0
      (fun _ => ForInStep.yield PUnit.unit) <$> pushClausePy [-p]
  have hStep :
      ∀ (u : Nat), u ∈ vs →
      ∀ (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((step u r).run st').2 n c aux := by
    intro u huVs r st' hSem'
    by_cases hlt : vLt n (antipodeCode n u) u = true
    · simpa [step, hlt] using hSem'
    · have hPc :
        PySemInv ((pcLitPy true u (antipodeCode n u) 0).run st').2 n c aux :=
        pySemInv_pcLitPy (st := st') (n := n) (c := c) aux
          (isRed := true) (u := u) (v := antipodeCode n u) (s := 0) hSem'
      let pVal : Int := ((pcLitPy true u (antipodeCode n u) 0).run st').1
      let pId : Nat := ((pcLitPy true u (antipodeCode n u) 0).run st').1.natAbs
      have hRunPc :
          (pcLitPy true u (antipodeCode n u) 0).run st' =
            (Int.ofNat ((pcIdPy true u (antipodeCode n u) 0).run st').1,
              ((pcIdPy true u (antipodeCode n u) 0).run st').2) := rfl
      have hpVal : pVal = Int.ofNat pId := by
        simp [pVal, pId, hRunPc]
      have hNamed :
          ((pcLitPy true u (antipodeCode n u) 0).run st').2.idToNamed[pId]? =
            some (.pc true u (antipodeCode n u) 0) := by
        simpa [pId] using
          (pyStateInv_pcLitPy (st := st') (isRed := true) (u := u)
            (v := antipodeCode n u) (s := 0) hSem'.inv).2
      have huMem : u ∈ allVertexCodes n := hVsMem u huVs
      have hNotPcSem :
          ¬ pyVarSemantics n c (.pc true u (antipodeCode n u) 0) :=
        pySem_clause_conjecture1 (n := n) (c := c) hNoGeo huMem
      have hPidNe0 : pId ≠ 0 := by
        intro hp0
        have hId0 :
            ((pcLitPy true u (antipodeCode n u) 0).run st').2.idToNamed[0]? =
              some (.pc true u (antipodeCode n u) 0) := by
          simpa [pId, hp0] using hNamed
        have hContra :
            (none : Option PyVarKey) = some (.pc true u (antipodeCode n u) 0) := by
          simpa [hPc.noZero] using hId0
        cases hContra
      have hPidPos : 0 < pId := Nat.pos_of_ne_zero hPidNe0
      have hPidLt : pId < ((pcLitPy true u (antipodeCode n u) 0).run st').2.nextId :=
        hPc.inv.1 hNamed
      have hClauseSat :
          ∃ i : Int, i ∈ ([-pVal] : List Int) ∧
            CNF.Lit.Sat
              (pyAssignmentAt ((pcLitPy true u (antipodeCode n u) 0).run st').2 n c aux)
              (litOfDimacsInt i) := by
        refine ⟨-pVal, by simp, ?_⟩
        have hNegSat :
            CNF.Lit.Sat
              (pyAssignmentAt ((pcLitPy true u (antipodeCode n u) 0).run st').2 n c aux)
              (.neg pId) := by
          exact (pyLitSat_neg_named_at
            (st := ((pcLitPy true u (antipodeCode n u) 0).run st').2)
            (n := n) (c := c) aux (i := pId)
            (k := .pc true u (antipodeCode n u) 0) hNamed).2 hNotPcSem
        simpa [pVal, hpVal, litOfDimacsInt, CNF.Lit.Sat, hPidPos] using hNegSat
      have hClauseBound :
          ∀ i : Int, i ∈ ([-pVal] : List Int) →
            i.natAbs < ((pcLitPy true u (antipodeCode n u) 0).run st').2.nextId := by
        intro i hi
        have hiEq : i = -pVal := by simpa using hi
        subst hiEq
        simpa [pVal, hpVal] using hPidLt
      have hPush :
          PySemInv
            ((pushClausePy [-pVal]).run
              ((pcLitPy true u (antipodeCode n u) 0).run st').2).2 n c aux :=
        pySemInv_pushClausePy
          (st := ((pcLitPy true u (antipodeCode n u) 0).run st').2) (n := n) (c := c) aux
          (cl := [-pVal]) hPc hClauseSat hClauseBound
      have hRunStep :
          (step u r).run st' =
            (ForInStep.yield PUnit.unit,
              ((pushClausePy [-pVal]).run
                ((pcLitPy true u (antipodeCode n u) 0).run st').2).2) := by
        unfold step
        simp [hlt]
        rw [hRunPc]
        rfl
      rw [hRunStep]
      simpa using hPush
  have hFor :
      PySemInv ((forIn vs PUnit.unit step).run st).2 n c aux :=
    pySemInv_forIn_mem (n := n) (c := c) (aux := aux)
      (xs := vs) (init := PUnit.unit) (f := step) (hStep := hStep) st hSem
  have hForUnit :
      PySemInv (((forIn vs PUnit.unit step).bind fun _ => StateT.pure PUnit.unit).run st).2 n c aux := by
    simpa [Bind.bind, pure] using hFor
  unfold addConjecture1UnitClausesPy
  simpa [step, Bind.bind, pure] using hForUnit

private lemma pySemInv_addAntipodalClausesPy
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    {vs : List Nat} (aux : Nat → Prop)
    (hAnti : IsAntipodalColoring c)
    (hVsMem : ∀ u : Nat, u ∈ vs → u ∈ allVertexCodes n)
    (hNbrMem : ∀ u : Nat, u ∈ vs → ∀ v : Nat, v ∈ neighborsCode n u → v ∈ allVertexCodes n)
    (hNbrAdj : ∀ u : Nat, u ∈ vs → ∀ v : Nat,
      v ∈ neighborsCode n u → Adj (natToVertex n u) (natToVertex n v))
    (hSem : PySemInv st n c aux) :
    PySemInv ((addAntipodalClausesPy n vs).run st).2 n c aux := by
  let innerStep : Nat → Nat → PUnit → PyEncM (ForInStep PUnit) := fun u v _ =>
    if vLt n v u then
      pure (ForInStep.yield PUnit.unit)
    else do
      let ruv ← rOldIdPy n u v
      let rauv ← rOldIdPy n (antipodeCode n u) (antipodeCode n v)
      let _ ← pushClausePy [-Int.ofNat ruv, -Int.ofNat rauv]
      (fun _ => ForInStep.yield PUnit.unit) <$> pushClausePy [Int.ofNat ruv, Int.ofNat rauv]
  have hInnerStep :
      ∀ (u : Nat), u ∈ vs →
      ∀ (v : Nat), v ∈ neighborsCode n u →
      ∀ (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((innerStep u v r).run st').2 n c aux := by
    intro u huVs v hvNbr r st' hSem'
    by_cases hlt : vLt n v u = true
    · simpa [innerStep, hlt] using hSem'
    · let key1 : PyVarKey := .r (orderedCodePair n u v).1 (orderedCodePair n u v).2
      let st1 : PyEncState := ((rOldIdPy n u v).run st').2
      let rid1 : Nat := ((rOldIdPy n u v).run st').1
      have hRuv : PySemInv st1 n c aux :=
        pySemInv_rOldIdPy (st := st') (n := n) (c := c) aux (u := u) (v := v) hSem'
      let key2 : PyVarKey :=
        .r (orderedCodePair n (antipodeCode n u) (antipodeCode n v)).1
          (orderedCodePair n (antipodeCode n u) (antipodeCode n v)).2
      let st2 : PyEncState := ((rOldIdPy n (antipodeCode n u) (antipodeCode n v)).run st1).2
      let rid2 : Nat := ((rOldIdPy n (antipodeCode n u) (antipodeCode n v)).run st1).1
      have hRauv : PySemInv st2 n c aux :=
        pySemInv_rOldIdPy (st := st1) (n := n) (c := c) aux
          (u := antipodeCode n u) (v := antipodeCode n v) hRuv
      have hNamed1_st1 : st1.idToNamed[rid1]? = some key1 := by
        simpa [st1, rid1, key1] using
          (pyStateInv_rOldIdPy (st := st') (n := n) (u := u) (v := v) hSem'.inv).2
      have hNamed2_st2 : st2.idToNamed[rid2]? = some key2 := by
        simpa [st2, st1, rid2, key2] using
          (pyStateInv_rOldIdPy (st := st1) (n := n)
            (u := antipodeCode n u) (v := antipodeCode n v) hRuv.inv).2
      have hrid1Ne0 : rid1 ≠ 0 := by
        simpa [rid1] using
          (rOldIdPy_ne_zero (st := st') (n := n) (u := u) (v := v)
            hSem'.inv hSem'.noZero hSem'.nextPos)
      have hrid2Ne0 : rid2 ≠ 0 := by
        simpa [rid2] using
          (rOldIdPy_ne_zero (st := st1) (n := n)
            (u := antipodeCode n u) (v := antipodeCode n v)
            hRuv.inv hRuv.noZero hRuv.nextPos)
      have hrid1Lt : rid1 < st1.nextId := hRuv.inv.1 hNamed1_st1
      have hSt1LeSt2 : st1.nextId ≤ st2.nextId := by
        simpa [st2] using
          (pyState_nextId_le_rOldIdPy (st := st1) (n := n)
            (u := antipodeCode n u) (v := antipodeCode n v))
      have hrid1Lt_st2 : rid1 < st2.nextId := lt_of_lt_of_le hrid1Lt hSt1LeSt2
      have huMem : u ∈ allVertexCodes n := hVsMem u huVs
      have hvMem : v ∈ allVertexCodes n := hNbrMem u huVs v hvNbr
      have hAdj : Adj (natToVertex n u) (natToVertex n v) := hNbrAdj u huVs v hvNbr
      have hSemLeft :
          ¬ pyVarSemantics n c (.r u v) ∨
            ¬ pyVarSemantics n c (.r (antipodeCode n u) (antipodeCode n v)) :=
        pySem_clause_antipodal_left (n := n) (c := c) hAnti huMem hvMem hAdj
      have hSemRight :
          pyVarSemantics n c (.r u v) ∨
            pyVarSemantics n c (.r (antipodeCode n u) (antipodeCode n v)) :=
        pySem_clause_antipodal_right (n := n) (c := c) hAnti huMem hvMem hAdj
      have hOrd1 :
          pyVarSemantics n c key1 ↔ pyVarSemantics n c (.r u v) := by
        simpa [key1] using (pyVarSemantics_r_orderedCodePair (n := n) (c := c) u v)
      have hOrd2 :
          pyVarSemantics n c key2 ↔
            pyVarSemantics n c (.r (antipodeCode n u) (antipodeCode n v)) := by
        simpa [key2] using
          (pyVarSemantics_r_orderedCodePair (n := n) (c := c) (antipodeCode n u) (antipodeCode n v))
      have hLeftOrd :
          ¬ pyVarSemantics n c key1 ∨ ¬ pyVarSemantics n c key2 := by
        rcases hSemLeft with h1 | h2
        · exact Or.inl ((not_congr hOrd1).2 h1)
        · exact Or.inr ((not_congr hOrd2).2 h2)
      have hRightOrd :
          pyVarSemantics n c key1 ∨ pyVarSemantics n c key2 := by
        rcases hSemRight with h1 | h2
        · exact Or.inl (hOrd1.symm.mp h1)
        · exact Or.inr (hOrd2.symm.mp h2)
      have hClause1Sat :
          ∃ i : Int, i ∈ ([-Int.ofNat rid1, -Int.ofNat rid2] : List Int) ∧
            CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt i) := by
        rcases hLeftOrd with hNot1 | hNot2
        · refine ⟨-Int.ofNat rid1, by simp, ?_⟩
          have hNeg1_st1 :
              CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt (-Int.ofNat rid1)) := by
            have hNegNamed :
                CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (.neg rid1) :=
              (pyLitSat_neg_named_at (st := st1) (n := n) (c := c) aux
                (i := rid1) (k := key1) hNamed1_st1).2 hNot1
            have hPos1 : 0 < rid1 := Nat.pos_of_ne_zero hrid1Ne0
            simpa [litOfDimacsInt, CNF.Lit.Sat, hPos1] using hNegNamed
          have hKeep :
              CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt (-Int.ofNat rid1)) ↔
                CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt (-Int.ofNat rid1)) :=
            pyLitSat_idForPy_eq_of_bound (st := st1) (n := n) (c := c) aux
              (k := key2) (i := -Int.ofNat rid1) (by simpa using hrid1Lt)
          exact hKeep.2 hNeg1_st1
        · refine ⟨-Int.ofNat rid2, by simp, ?_⟩
          have hNegNamed2 :
              CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (.neg rid2) :=
            (pyLitSat_neg_named_at (st := st2) (n := n) (c := c) aux
              (i := rid2) (k := key2) hNamed2_st2).2 hNot2
          have hPos2 : 0 < rid2 := Nat.pos_of_ne_zero hrid2Ne0
          simpa [litOfDimacsInt, CNF.Lit.Sat, hPos2] using hNegNamed2
      have hClause1Bound :
          ∀ i : Int, i ∈ ([-Int.ofNat rid1, -Int.ofNat rid2] : List Int) → i.natAbs < st2.nextId := by
        intro i hi
        rcases List.mem_cons.1 hi with hi | hi
        · have hiEq : i = -Int.ofNat rid1 := hi
          subst hiEq
          simpa using hrid1Lt_st2
        · have hiEq : i = -Int.ofNat rid2 := by simpa using hi
          subst hiEq
          simpa using (hRauv.inv.1 hNamed2_st2)
      have hPush1 :
          PySemInv ((pushClausePy [-Int.ofNat rid1, -Int.ofNat rid2]).run st2).2 n c aux :=
        pySemInv_pushClausePy (st := st2) (n := n) (c := c) aux
          (cl := [-Int.ofNat rid1, -Int.ofNat rid2]) hRauv hClause1Sat hClause1Bound
      let st3 : PyEncState := ((pushClausePy [-Int.ofNat rid1, -Int.ofNat rid2]).run st2).2
      have hSt3Next : st3.nextId = st2.nextId := by
        unfold st3 pushClausePy
        rfl
      have hClause2Sat :
          ∃ i : Int, i ∈ ([Int.ofNat rid1, Int.ofNat rid2] : List Int) ∧
            CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt i) := by
        rcases hRightOrd with hPos1 | hPos2
        · refine ⟨Int.ofNat rid1, by simp, ?_⟩
          have hPos1_st1 :
              CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt (Int.ofNat rid1)) := by
            have hPosNamed :
                CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (.pos rid1) :=
              (pyLitSat_pos_named_at (st := st1) (n := n) (c := c) aux
                (i := rid1) (k := key1) hNamed1_st1).2 hPos1
            have hPosRid1 : 0 < rid1 := Nat.pos_of_ne_zero hrid1Ne0
            simpa [litOfDimacsInt, CNF.Lit.Sat, hPosRid1] using hPosNamed
          have hKeep12 :
              CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt (Int.ofNat rid1)) ↔
                CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt (Int.ofNat rid1)) :=
            pyLitSat_idForPy_eq_of_bound (st := st1) (n := n) (c := c) aux
              (k := key2) (i := Int.ofNat rid1) (by simpa using hrid1Lt)
          have hPos1_st2 :
              CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt (Int.ofNat rid1)) :=
            hKeep12.2 hPos1_st1
          have hKeep23 :
              CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt (Int.ofNat rid1)) ↔
                CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt (Int.ofNat rid1)) :=
            pyLitSat_pushClausePy_eq (st := st2) (n := n) (c := c) aux
              (cl := [-Int.ofNat rid1, -Int.ofNat rid2]) (i := Int.ofNat rid1)
          exact hKeep23.2 hPos1_st2
        · refine ⟨Int.ofNat rid2, by simp, ?_⟩
          have hPosNamed2 :
              CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (.pos rid2) :=
            (pyLitSat_pos_named_at (st := st2) (n := n) (c := c) aux
              (i := rid2) (k := key2) hNamed2_st2).2 hPos2
          have hPosRid2 : 0 < rid2 := Nat.pos_of_ne_zero hrid2Ne0
          have hPos2_st2 :
              CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt (Int.ofNat rid2)) := by
            simpa [litOfDimacsInt, CNF.Lit.Sat, hPosRid2] using hPosNamed2
          have hKeep23 :
              CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt (Int.ofNat rid2)) ↔
                CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt (Int.ofNat rid2)) :=
            pyLitSat_pushClausePy_eq (st := st2) (n := n) (c := c) aux
              (cl := [-Int.ofNat rid1, -Int.ofNat rid2]) (i := Int.ofNat rid2)
          exact hKeep23.2 hPos2_st2
      have hClause2Bound :
          ∀ i : Int, i ∈ ([Int.ofNat rid1, Int.ofNat rid2] : List Int) → i.natAbs < st3.nextId := by
        intro i hi
        rcases List.mem_cons.1 hi with hi | hi
        · have hiEq : i = Int.ofNat rid1 := hi
          subst hiEq
          simpa [hSt3Next] using hrid1Lt_st2
        · have hiEq : i = Int.ofNat rid2 := by simpa using hi
          subst hiEq
          simpa [hSt3Next] using (hRauv.inv.1 hNamed2_st2)
      have hPush2 :
          PySemInv
            ((pushClausePy [Int.ofNat rid1, Int.ofNat rid2]).run st3).2 n c aux :=
        pySemInv_pushClausePy (st := st3) (n := n) (c := c) aux
          (cl := [Int.ofNat rid1, Int.ofNat rid2]) hPush1 hClause2Sat hClause2Bound
      simpa [innerStep, hlt, st1, st2, st3, rid1, rid2, key1, key2, Bind.bind, pure] using hPush2
  let outerStep : Nat → PUnit → PyEncM (ForInStep PUnit) := fun u _ =>
    let inner := forIn (neighborsCode n u) PUnit.unit (innerStep u)
    inner.bind fun _ => StateT.pure (ForInStep.yield PUnit.unit)
  have hOuterStep :
      ∀ (u : Nat), u ∈ vs →
      ∀ (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((outerStep u r).run st').2 n c aux := by
    intro u huVs r st' hSem'
    have hInnerFor :
        PySemInv ((forIn (neighborsCode n u) PUnit.unit (innerStep u)).run st').2 n c aux :=
      pySemInv_forIn_mem (n := n) (c := c) (aux := aux)
        (xs := neighborsCode n u) (init := PUnit.unit) (f := innerStep u)
        (hStep := hInnerStep u huVs) st' hSem'
    have hInnerYield :
        PySemInv
          (((forIn (neighborsCode n u) PUnit.unit (innerStep u)).bind
            fun _ => StateT.pure (ForInStep.yield PUnit.unit)).run st').2 n c aux := by
      simpa [Bind.bind, pure] using hInnerFor
    simpa [outerStep] using hInnerYield
  have hFor :
      PySemInv ((forIn vs PUnit.unit outerStep).run st).2 n c aux :=
    pySemInv_forIn_mem (n := n) (c := c) (aux := aux)
      (xs := vs) (init := PUnit.unit) (f := outerStep) (hStep := hOuterStep) st hSem
  have hForUnit :
      PySemInv (((forIn vs PUnit.unit outerStep).bind fun _ => StateT.pure PUnit.unit).run st).2 n c aux := by
    simpa [Bind.bind, pure] using hFor
  unfold addAntipodalClausesPy
  simpa [outerStep, innerStep, Bind.bind, pure] using hForUnit

private lemma litSat_dimacs_neg_local {τ : CNF.Assignment Nat} {i : Int} (hi0 : i ≠ 0) :
    CNF.Lit.Sat τ (litOfDimacsInt (-i)) ↔ ¬ CNF.Lit.Sat τ (litOfDimacsInt i) := by
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          exfalso
          exact hi0 rfl
      | succ n =>
          change CNF.Lit.Sat τ (litOfDimacsInt (Int.negSucc n)) ↔
            ¬ CNF.Lit.Sat τ (litOfDimacsInt (Int.ofNat (Nat.succ n)))
          have hltFalse : ¬ (((n : Int) + 1) < 0) := by
            have hnonneg : (0 : Int) ≤ (n : Int) + 1 := by
              exact add_nonneg (Int.natCast_nonneg n) (show (0 : Int) ≤ 1 by decide)
            exact not_lt_of_ge hnonneg
          simp [litOfDimacsInt, CNF.Lit.Sat, hltFalse]
  | negSucc n =>
      change CNF.Lit.Sat τ (litOfDimacsInt (Int.ofNat (Nat.succ n))) ↔
        ¬ CNF.Lit.Sat τ (litOfDimacsInt (Int.negSucc n))
      have hltFalse : ¬ (((n : Int) + 1) < 0) := by
        have hnonneg : (0 : Int) ≤ (n : Int) + 1 := by
          exact add_nonneg (Int.natCast_nonneg n) (show (0 : Int) ≤ 1 by decide)
        exact not_lt_of_ge hnonneg
      simp [litOfDimacsInt, CNF.Lit.Sat, hltFalse]

private lemma pySemInv_addEq5ClausesPy
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    {vs : List Nat} (aux : Nat → Prop)
    (hAnti : IsAntipodalColoring c)
    (hVsMem : ∀ u : Nat, u ∈ vs → u ∈ allVertexCodes n)
    (hNbrMem : ∀ u : Nat, u ∈ vs → ∀ v : Nat, v ∈ neighborsCode n u → v ∈ allVertexCodes n)
    (hNbrAdj : ∀ u : Nat, u ∈ vs → ∀ v : Nat,
      v ∈ neighborsCode n u → Adj (natToVertex n u) (natToVertex n v))
    (hSem : PySemInv st n c aux) :
    PySemInv ((addEq5ClausesPy n vs).run st).2 n c aux := by
  let innerStep : Nat → Nat → PUnit → PyEncM (ForInStep PUnit) := fun u v _ => do
    let ruv ← rLitPy n u v
    let p ← pcLitPy true u v 0
    (fun _ => ForInStep.yield PUnit.unit) <$> pushClausePy [-ruv, p]
  have hInnerStep :
      ∀ (u : Nat), u ∈ vs →
      ∀ (v : Nat), v ∈ neighborsCode n u →
      ∀ (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((innerStep u v r).run st').2 n c aux := by
    intro u huVs v hvNbr r st' hSem'
    let st1 : PyEncState := ((rLitPy n u v).run st').2
    let ruv : Int := ((rLitPy n u v).run st').1
    have hRuv : PySemInv st1 n c aux :=
      pySemInv_rLitPy (st := st') (n := n) (c := c) aux (u := u) (v := v) hSem'
    let st2 : PyEncState := ((pcLitPy true u v 0).run st1).2
    let p : Int := ((pcLitPy true u v 0).run st1).1
    have hPc : PySemInv st2 n c aux :=
      pySemInv_pcLitPy (st := st1) (n := n) (c := c) aux
        (isRed := true) (u := u) (v := v) (s := 0) hRuv
    have huMem : u ∈ allVertexCodes n := hVsMem u huVs
    have hvMem : v ∈ allVertexCodes n := hNbrMem u huVs v hvNbr
    have hAdj : Adj (natToVertex n u) (natToVertex n v) := hNbrAdj u huVs v hvNbr
    have hClauseSem :
        ¬ pyVarSemantics n c (.r u v) ∨
          pyVarSemantics n c (.pc true u v 0) :=
      pySem_clause_eq5 (n := n) (c := c) (u := u) (v := v) hAdj
    have hNamedR :
        st1.idToNamed[ruv.natAbs]? =
          some
            (if vLt n (orderedCodePair n u v).1
                (antipodeCode n (orderedCodePair n u v).2) = true
             then .r (orderedCodePair n (orderedCodePair n u v).1
                 (orderedCodePair n u v).2).1
                 (orderedCodePair n (orderedCodePair n u v).1
                   (orderedCodePair n u v).2).2
             else .r (orderedCodePair n (antipodeCode n (orderedCodePair n u v).1)
                 (antipodeCode n (orderedCodePair n u v).2)).1
                 (orderedCodePair n (antipodeCode n (orderedCodePair n u v).1)
                   (antipodeCode n (orderedCodePair n u v).2)).2) := by
      simpa [st1, ruv] using
        (pyStateInv_rLitPy (st := st') (n := n) (u := u) (v := v) hSem'.inv)
    have hRuvLt : ruv.natAbs < st1.nextId := hRuv.inv.1 hNamedR
    have hSt1LeSt2 : st1.nextId ≤ st2.nextId := by
      simpa [st2] using
        (pyState_nextId_le_pcLitPy (st := st1) (isRed := true) (u := u) (v := v) (s := 0))
    have hRuvLtSt2 : ruv.natAbs < st2.nextId := lt_of_lt_of_le hRuvLt hSt1LeSt2
    have hNamedP :
        st2.idToNamed[p.natAbs]? = some (.pc true u v 0) := by
      simpa [st2, p] using
        (pyStateInv_pcLitPy (st := st1) (isRed := true) (u := u) (v := v) (s := 0) hRuv.inv).2
    have hPLt : p.natAbs < st2.nextId := hPc.inv.1 hNamedP
    have hRuvNe0 : ruv ≠ 0 := by
      simpa [ruv] using
        (rLitPy_ne_zero (st := st') (n := n) (u := u) (v := v)
          hSem'.inv hSem'.noZero hSem'.nextPos)
    have hSatR_st1 :
        CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt ruv) ↔
          pyVarSemantics n c (.r u v) := by
      simpa [st1, ruv] using
        (pyLitSat_rLitPy_iff_red_at
          (st := st') (n := n) (c := c) aux hSem'.inv hAnti hSem'.noZero hSem'.nextPos
          (u := u) (v := v) huMem hvMem hAdj)
    have hKeepR :
        CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt ruv) ↔
          CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt ruv) := by
      unfold st2 pcLitPy pcIdPy
      simpa using
        (pyLitSat_idForPy_eq_of_bound
          (st := st1) (n := n) (c := c) aux
          (k := .pc true u v 0) (i := ruv) (by simpa using hRuvLt))
    have hClauseSat :
        ∃ i : Int, i ∈ ([-ruv, p] : List Int) ∧
          CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt i) := by
      rcases hClauseSem with hNotR | hPcSem
      · refine ⟨-ruv, by simp, ?_⟩
        have hNotSatR_st1 :
            ¬ CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt ruv) := by
          intro hSatR
          exact hNotR (hSatR_st1.1 hSatR)
        have hNotSatR_st2 :
            ¬ CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt ruv) := by
          intro hSatR
          exact hNotSatR_st1 (hKeepR.1 hSatR)
        exact (litSat_dimacs_neg_local
          (τ := pyAssignmentAt st2 n c aux) (i := ruv) hRuvNe0).2 hNotSatR_st2
      · refine ⟨p, by simp, ?_⟩
        have hPosP :
            CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (.pos p.natAbs) :=
          (pyLitSat_pos_named_at
            (st := st2) (n := n) (c := c) aux
            (i := p.natAbs) (k := .pc true u v 0) hNamedP).2 hPcSem
        have hpEq : p = Int.ofNat ((pcIdPy true u v 0).run st1).1 := by
          unfold p pcLitPy
          rfl
        have hpNonneg : (0 : Int) ≤ p := by
          rw [hpEq]
          exact Int.ofNat_nonneg _
        have hLitEq : litOfDimacsInt p = .pos p.natAbs := by
          rw [hpEq]
          simp [litOfDimacsInt]
        simpa [hLitEq] using hPosP
    have hClauseBound :
        ∀ i : Int, i ∈ ([-ruv, p] : List Int) → i.natAbs < st2.nextId := by
      intro i hi
      rcases List.mem_cons.1 hi with hi | hi
      · have hiEq : i = -ruv := hi
        subst hiEq
        simpa using hRuvLtSt2
      · have hiEq : i = p := by simpa using hi
        subst hiEq
        exact hPLt
    have hPush :
        PySemInv ((pushClausePy [-ruv, p]).run st2).2 n c aux :=
      pySemInv_pushClausePy (st := st2) (n := n) (c := c) aux
        (cl := [-ruv, p]) hPc hClauseSat hClauseBound
    have hRunStep :
        (innerStep u v r).run st' =
          (ForInStep.yield PUnit.unit, ((pushClausePy [-ruv, p]).run st2).2) := by
      unfold innerStep
      simp [st1, st2, ruv, p, Bind.bind]
      rfl
    rw [hRunStep]
    simpa using hPush
  let outerStep : Nat → PUnit → PyEncM (ForInStep PUnit) := fun u _ =>
    if vLt n (antipodeCode n u) u then
      pure (ForInStep.yield PUnit.unit)
    else
      let inner := forIn (neighborsCode n u) PUnit.unit (innerStep u)
      inner.bind fun _ => StateT.pure (ForInStep.yield PUnit.unit)
  have hOuterStep :
      ∀ (u : Nat), u ∈ vs →
      ∀ (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((outerStep u r).run st').2 n c aux := by
    intro u huVs r st' hSem'
    by_cases hlt : vLt n (antipodeCode n u) u = true
    · simpa [outerStep, hlt] using hSem'
    · have hInnerFor :
        PySemInv ((forIn (neighborsCode n u) PUnit.unit (innerStep u)).run st').2 n c aux :=
        pySemInv_forIn_mem (n := n) (c := c) (aux := aux)
          (xs := neighborsCode n u) (init := PUnit.unit) (f := innerStep u)
          (hStep := hInnerStep u huVs) st' hSem'
      have hInnerYield :
          PySemInv
            (((forIn (neighborsCode n u) PUnit.unit (innerStep u)).bind
              fun _ => StateT.pure (ForInStep.yield PUnit.unit)).run st').2 n c aux := by
        simpa [Bind.bind, pure] using hInnerFor
      simpa [outerStep, hlt] using hInnerYield
  have hFor :
      PySemInv ((forIn vs PUnit.unit outerStep).run st).2 n c aux :=
    pySemInv_forIn_mem (n := n) (c := c) (aux := aux)
      (xs := vs) (init := PUnit.unit) (f := outerStep) (hStep := hOuterStep) st hSem
  have hForUnit :
      PySemInv (((forIn vs PUnit.unit outerStep).bind fun _ => StateT.pure PUnit.unit).run st).2 n c aux := by
    simpa [Bind.bind, pure] using hFor
  unfold addEq5ClausesPy
  simpa [outerStep, innerStep, Bind.bind, pure] using hForUnit

set_option maxHeartbeats 800000 in
-- This proof expands several deeply nested `StateT` terms from the generated encoder.
private lemma pySemInv_addEq7Eq9ClausesPy
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    {vs : List Nat} (aux : Nat → Prop)
    (hAnti : IsAntipodalColoring c)
    (hVsMem : ∀ u : Nat, u ∈ vs → u ∈ allVertexCodes n)
    (hNbrMem : ∀ u : Nat, u ∈ vs → ∀ v : Nat, v ∈ neighborsCode n u → v ∈ allVertexCodes n)
    (hNbrAdj : ∀ u : Nat, u ∈ vs → ∀ v : Nat,
      v ∈ neighborsCode n u → Adj (natToVertex n u) (natToVertex n v))
    (hSem : PySemInv st n c aux) :
    PySemInv ((addEq7Eq9ClausesPy n vs).run st).2 n c aux := by
  let innerStep : Nat → Nat → Nat → PUnit → PyEncM (ForInStep PUnit) := fun u w v _ =>
    if distCode n u v + 1 = distCode n u w then
      do
        let puv ← pcLitPy true u v 0
        let rvw ← rLitPy n v w
        let puw ← pcLitPy true u w 0
        let _ ← pushClausePy [-puv, -rvw, puw]
        if 0 < n - 1 then
          let buw ← pcLitPy false u w 1
          (fun _ => ForInStep.yield PUnit.unit) <$> pushClausePy [-puv, rvw, buw]
        else
          pure (ForInStep.yield PUnit.unit)
    else
      pure (ForInStep.yield PUnit.unit)
  have hInnerStep :
      ∀ (u : Nat), u ∈ vs →
      ∀ (w : Nat), w ∈ vs →
      ∀ (v : Nat), v ∈ neighborsCode n w →
      ∀ (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((innerStep u w v r).run st').2 n c aux := by
    intro u huVs w hwVs v hvNbr r st' hSem'
    by_cases hdist : distCode n u v + 1 = distCode n u w
    · let st1 : PyEncState := ((pcLitPy true u v 0).run st').2
      let puv : Int := ((pcLitPy true u v 0).run st').1
      have hPuv : PySemInv st1 n c aux :=
        pySemInv_pcLitPy (st := st') (n := n) (c := c) aux
          (isRed := true) (u := u) (v := v) (s := 0) hSem'
      let st2 : PyEncState := ((rLitPy n v w).run st1).2
      let rvw : Int := ((rLitPy n v w).run st1).1
      have hRvw : PySemInv st2 n c aux :=
        pySemInv_rLitPy (st := st1) (n := n) (c := c) aux
          (u := v) (v := w) hPuv
      let st3 : PyEncState := ((pcLitPy true u w 0).run st2).2
      let puw : Int := ((pcLitPy true u w 0).run st2).1
      have hPuw : PySemInv st3 n c aux :=
        pySemInv_pcLitPy (st := st2) (n := n) (c := c) aux
          (isRed := true) (u := u) (v := w) (s := 0) hRvw
      have hNamedPuv_st1 :
          st1.idToNamed[puv.natAbs]? = some (.pc true u v 0) := by
        simpa [st1, puv] using
          (pyStateInv_pcLitPy (st := st') (isRed := true) (u := u) (v := v) (s := 0) hSem'.inv).2
      have hNamedRvw_st2 :
          st2.idToNamed[rvw.natAbs]? =
            some
              (if vLt n (orderedCodePair n v w).1 (antipodeCode n (orderedCodePair n v w).2) = true
               then .r (orderedCodePair n (orderedCodePair n v w).1
                   (orderedCodePair n v w).2).1
                   (orderedCodePair n (orderedCodePair n v w).1
                     (orderedCodePair n v w).2).2
               else .r (orderedCodePair n (antipodeCode n (orderedCodePair n v w).1)
                   (antipodeCode n (orderedCodePair n v w).2)).1
                   (orderedCodePair n (antipodeCode n (orderedCodePair n v w).1)
                     (antipodeCode n (orderedCodePair n v w).2)).2) := by
        simpa [st2, st1, rvw] using
          (pyStateInv_rLitPy (st := st1) (n := n) (u := v) (v := w) hPuv.inv)
      have hNamedPuw_st3 :
          st3.idToNamed[puw.natAbs]? = some (.pc true u w 0) := by
        simpa [st3, st2, puw] using
          (pyStateInv_pcLitPy (st := st2) (isRed := true) (u := u) (v := w) (s := 0) hRvw.inv).2
      have hPuvLt_st1 : puv.natAbs < st1.nextId := hPuv.inv.1 hNamedPuv_st1
      have hSt1LeSt2 : st1.nextId ≤ st2.nextId := by
        simpa [st2] using
          (pyState_nextId_le_rLitPy (st := st1) (n := n) (u := v) (v := w))
      have hPuvLt_st2 : puv.natAbs < st2.nextId := lt_of_lt_of_le hPuvLt_st1 hSt1LeSt2
      have hRvwLt_st2 : rvw.natAbs < st2.nextId := hRvw.inv.1 hNamedRvw_st2
      have hSt2LeSt3 : st2.nextId ≤ st3.nextId := by
        simpa [st3] using
          (pyState_nextId_le_pcLitPy (st := st2) (isRed := true) (u := u) (v := w) (s := 0))
      have hPuvLt_st3 : puv.natAbs < st3.nextId := lt_of_lt_of_le hPuvLt_st2 hSt2LeSt3
      have hRvwLt_st3 : rvw.natAbs < st3.nextId := lt_of_lt_of_le hRvwLt_st2 hSt2LeSt3
      have hPuwLt_st3 : puw.natAbs < st3.nextId := hPuw.inv.1 hNamedPuw_st3
      have hVmem : v ∈ allVertexCodes n := hNbrMem w hwVs v hvNbr
      have hWmem : w ∈ allVertexCodes n := hVsMem w hwVs
      have hAdjWV : Adj (natToVertex n w) (natToVertex n v) := hNbrAdj w hwVs v hvNbr
      have hAdjVW : Adj (natToVertex n v) (natToVertex n w) := hAdjWV.symm
      have hStep : distCode n u v + 1 = distCode n u w := hdist
      have hClause1Sem :
          ¬ pyVarSemantics n c (.pc true u v 0) ∨
            ¬ pyVarSemantics n c (.r v w) ∨
            pyVarSemantics n c (.pc true u w 0) :=
        pySem_clause_eq7 (n := n) (c := c) (u := u) (v := v) (w := w) hAdjVW hStep
      have hSatPuv_st1 :
          CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt puv) ↔
            pyVarSemantics n c (.pc true u v 0) := by
        have hPos :
            CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (.pos puv.natAbs) ↔
              pyVarSemantics n c (.pc true u v 0) :=
          (pyLitSat_pos_named_at
            (st := st1) (n := n) (c := c) aux
            (i := puv.natAbs) (k := .pc true u v 0) hNamedPuv_st1)
        have hpEq : puv = Int.ofNat ((pcIdPy true u v 0).run st').1 := by
          unfold puv pcLitPy
          rfl
        have hLitEq : litOfDimacsInt puv = .pos puv.natAbs := by
          rw [hpEq]
          simp [litOfDimacsInt]
        simpa [hLitEq] using hPos
      have hSatRvw_st2 :
          CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt rvw) ↔
            pyVarSemantics n c (.r v w) := by
        simpa [st1, st2, rvw] using
          (pyLitSat_rLitPy_iff_red_at
            (st := st1) (n := n) (c := c) aux hPuv.inv hAnti hPuv.noZero hPuv.nextPos
            (u := v) (v := w) hVmem hWmem hAdjVW)
      have hSatPuw_st3 :
          CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt puw) ↔
            pyVarSemantics n c (.pc true u w 0) := by
        have hPos :
            CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (.pos puw.natAbs) ↔
              pyVarSemantics n c (.pc true u w 0) :=
          (pyLitSat_pos_named_at
            (st := st3) (n := n) (c := c) aux
            (i := puw.natAbs) (k := .pc true u w 0) hNamedPuw_st3)
        have hpEq : puw = Int.ofNat ((pcIdPy true u w 0).run st2).1 := by
          unfold puw pcLitPy
          rfl
        have hLitEq : litOfDimacsInt puw = .pos puw.natAbs := by
          rw [hpEq]
          simp [litOfDimacsInt]
        simpa [hLitEq] using hPos
      have hKeepPuv12 :
          CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt puv) ↔
            CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt puv) :=
        pyLitSat_rLitPy_eq_of_bound
          (st := st1) (n := n) (c := c) aux (u := v) (v := w)
          (i := puv) (by simpa using hPuvLt_st1)
      have hKeepPuv23 :
          CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt puv) ↔
            CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt puv) :=
        pyLitSat_idForPy_eq_of_bound
          (st := st2) (n := n) (c := c) aux
          (k := .pc true u w 0) (i := puv) (by simpa using hPuvLt_st2)
      have hKeepRvw23 :
          CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt rvw) ↔
            CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt rvw) :=
        pyLitSat_idForPy_eq_of_bound
          (st := st2) (n := n) (c := c) aux
          (k := .pc true u w 0) (i := rvw) (by simpa using hRvwLt_st2)
      have hPuvNatNe0 : puv.natAbs ≠ 0 := by
        intro h0
        have hId0 : st1.idToNamed[0]? = some (.pc true u v 0) := by
          simpa [h0] using hNamedPuv_st1
        have hContra :
            (none : Option PyVarKey) = some (.pc true u v 0) := by
          simpa [hPuv.noZero] using hId0
        cases hContra
      have hPuvNe0 : puv ≠ 0 := by
        intro h0
        exact hPuvNatNe0 (by simpa [h0])
      have hRvwNe0 : rvw ≠ 0 := by
        simpa [rvw] using
          (rLitPy_ne_zero (st := st1) (n := n) (u := v) (v := w)
            hPuv.inv hPuv.noZero hPuv.nextPos)
      have hClause1Sat :
          ∃ i : Int, i ∈ ([-puv, -rvw, puw] : List Int) ∧
            CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt i) := by
        rcases hClause1Sem with hNotPuv | hRest
        · refine ⟨-puv, by simp, ?_⟩
          have hNotSatPuv_st1 :
              ¬ CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt puv) := by
            intro hSat
            exact hNotPuv (hSatPuv_st1.1 hSat)
          have hNotSatPuv_st2 :
              ¬ CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt puv) := by
            intro hSat
            exact hNotSatPuv_st1 (hKeepPuv12.1 hSat)
          have hNotSatPuv_st3 :
              ¬ CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt puv) := by
            intro hSat
            exact hNotSatPuv_st2 (hKeepPuv23.1 hSat)
          exact (litSat_dimacs_neg_local
            (τ := pyAssignmentAt st3 n c aux) (i := puv) hPuvNe0).2 hNotSatPuv_st3
        · rcases hRest with hNotRvw | hPuwSem
          · refine ⟨-rvw, by simp, ?_⟩
            have hNotSatRvw_st2 :
                ¬ CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt rvw) := by
              intro hSat
              exact hNotRvw (hSatRvw_st2.1 hSat)
            have hNotSatRvw_st3 :
                ¬ CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt rvw) := by
              intro hSat
              exact hNotSatRvw_st2 (hKeepRvw23.1 hSat)
            exact (litSat_dimacs_neg_local
              (τ := pyAssignmentAt st3 n c aux) (i := rvw) hRvwNe0).2 hNotSatRvw_st3
          · exact ⟨puw, by simp, (hSatPuw_st3.2 hPuwSem)⟩
      have hClause1Bound :
          ∀ i : Int, i ∈ ([-puv, -rvw, puw] : List Int) → i.natAbs < st3.nextId := by
        intro i hi
        rcases List.mem_cons.1 hi with hi | hi
        · have hiEq : i = -puv := hi
          subst hiEq
          simpa using hPuvLt_st3
        · rcases List.mem_cons.1 hi with hi | hi
          · have hiEq : i = -rvw := hi
            subst hiEq
            simpa using hRvwLt_st3
          · have hiEq : i = puw := by simpa using hi
            subst hiEq
            exact hPuwLt_st3
      have hPush1 :
          PySemInv ((pushClausePy [-puv, -rvw, puw]).run st3).2 n c aux :=
        pySemInv_pushClausePy (st := st3) (n := n) (c := c) aux
          (cl := [-puv, -rvw, puw]) hPuw hClause1Sat hClause1Bound
      let st4 : PyEncState := ((pushClausePy [-puv, -rvw, puw]).run st3).2
      have hSt4Next : st4.nextId = st3.nextId := by
        unfold st4 pushClausePy
        rfl
      by_cases hN : 0 < n - 1
      · let st5 : PyEncState := ((pcLitPy false u w 1).run st4).2
        let buw : Int := ((pcLitPy false u w 1).run st4).1
        have hBuw : PySemInv st5 n c aux :=
          pySemInv_pcLitPy (st := st4) (n := n) (c := c) aux
            (isRed := false) (u := u) (v := w) (s := 1) hPush1
        have hNamedBuw_st5 :
            st5.idToNamed[buw.natAbs]? = some (.pc false u w 1) := by
          simpa [st5, buw] using
            (pyStateInv_pcLitPy (st := st4) (isRed := false) (u := u) (v := w) (s := 1) hPush1.inv).2
        have hBuwLt_st5 : buw.natAbs < st5.nextId := hBuw.inv.1 hNamedBuw_st5
        have hPuvLt_st4 : puv.natAbs < st4.nextId := by simpa [hSt4Next] using hPuvLt_st3
        have hRvwLt_st4 : rvw.natAbs < st4.nextId := by simpa [hSt4Next] using hRvwLt_st3
        have hSt4LeSt5 : st4.nextId ≤ st5.nextId := by
          simpa [st5] using
            (pyState_nextId_le_pcLitPy (st := st4) (isRed := false) (u := u) (v := w) (s := 1))
        have hPuvLt_st5 : puv.natAbs < st5.nextId := lt_of_lt_of_le hPuvLt_st4 hSt4LeSt5
        have hRvwLt_st5 : rvw.natAbs < st5.nextId := lt_of_lt_of_le hRvwLt_st4 hSt4LeSt5
        have hClause2Sat :
            ∃ i : Int, i ∈ ([-puv, rvw, buw] : List Int) ∧
              CNF.Lit.Sat (pyAssignmentAt st5 n c aux) (litOfDimacsInt i) := by
          refine ⟨buw, by simp, ?_⟩
          have hBuwSem : pyVarSemantics n c (.pc false u w 1) := by simp [pyVarSemantics]
          have hPosBuw :
              CNF.Lit.Sat (pyAssignmentAt st5 n c aux) (.pos buw.natAbs) :=
            (pyLitSat_pos_named_at
              (st := st5) (n := n) (c := c) aux
              (i := buw.natAbs) (k := .pc false u w 1) hNamedBuw_st5).2 hBuwSem
          have hbEq : buw = Int.ofNat ((pcIdPy false u w 1).run st4).1 := by
            unfold buw pcLitPy
            rfl
          have hLitEq : litOfDimacsInt buw = .pos buw.natAbs := by
            rw [hbEq]
            simp [litOfDimacsInt]
          simpa [hLitEq] using hPosBuw
        have hClause2Bound :
            ∀ i : Int, i ∈ ([-puv, rvw, buw] : List Int) → i.natAbs < st5.nextId := by
          intro i hi
          rcases List.mem_cons.1 hi with hi | hi
          · have hiEq : i = -puv := hi
            subst hiEq
            simpa using hPuvLt_st5
          · rcases List.mem_cons.1 hi with hi | hi
            · have hiEq : i = rvw := hi
              subst hiEq
              exact hRvwLt_st5
            · have hiEq : i = buw := by simpa using hi
              subst hiEq
              exact hBuwLt_st5
        have hPush2 :
            PySemInv ((pushClausePy [-puv, rvw, buw]).run st5).2 n c aux :=
          pySemInv_pushClausePy (st := st5) (n := n) (c := c) aux
            (cl := [-puv, rvw, buw]) hBuw hClause2Sat hClause2Bound
        simpa [innerStep, hdist, hN, st1, st2, st3, st4, st5, puv, rvw, puw, buw, Bind.bind, pure]
          using hPush2
      · simpa [innerStep, hdist, hN, st1, st2, st3, st4, puv, rvw, puw, Bind.bind, pure] using hPush1
    · simpa [innerStep, hdist] using hSem'
  let middleStep : Nat → Nat → PUnit → PyEncM (ForInStep PUnit) := fun u w _ =>
    if w ∈ neighborsCode n u then
      pure (ForInStep.yield PUnit.unit)
    else
      let inner := forIn (neighborsCode n w) PUnit.unit (innerStep u w)
      inner.bind fun _ => StateT.pure (ForInStep.yield PUnit.unit)
  have hMiddleStep :
      ∀ (u : Nat), u ∈ vs →
      ∀ (w : Nat), w ∈ vs →
      ∀ (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((middleStep u w r).run st').2 n c aux := by
    intro u huVs w hwVs r st' hSem'
    by_cases hNbr : w ∈ neighborsCode n u
    · simpa [middleStep, hNbr] using hSem'
    · have hInnerFor :
        PySemInv ((forIn (neighborsCode n w) PUnit.unit (innerStep u w)).run st').2 n c aux :=
        pySemInv_forIn_mem (n := n) (c := c) (aux := aux)
          (xs := neighborsCode n w) (init := PUnit.unit) (f := innerStep u w)
          (hStep := hInnerStep u huVs w hwVs) st' hSem'
      have hInnerYield :
          PySemInv
            (((forIn (neighborsCode n w) PUnit.unit (innerStep u w)).bind
              fun _ => StateT.pure (ForInStep.yield PUnit.unit)).run st').2 n c aux := by
        simpa [Bind.bind, pure] using hInnerFor
      simpa [middleStep, hNbr] using hInnerYield
  let outerStep : Nat → PUnit → PyEncM (ForInStep PUnit) := fun u _ =>
    if vLt n (antipodeCode n u) u then
      pure (ForInStep.yield PUnit.unit)
    else
      let middle := forIn vs PUnit.unit (middleStep u)
      middle.bind fun _ => StateT.pure (ForInStep.yield PUnit.unit)
  have hOuterStep :
      ∀ (u : Nat), u ∈ vs →
      ∀ (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((outerStep u r).run st').2 n c aux := by
    intro u huVs r st' hSem'
    by_cases hlt : vLt n (antipodeCode n u) u = true
    · simpa [outerStep, hlt] using hSem'
    · have hMiddleFor :
        PySemInv ((forIn vs PUnit.unit (middleStep u)).run st').2 n c aux :=
        pySemInv_forIn_mem (n := n) (c := c) (aux := aux)
          (xs := vs) (init := PUnit.unit) (f := middleStep u)
          (hStep := hMiddleStep u huVs) st' hSem'
      have hMiddleYield :
          PySemInv
            (((forIn vs PUnit.unit (middleStep u)).bind
              fun _ => StateT.pure (ForInStep.yield PUnit.unit)).run st').2 n c aux := by
        simpa [Bind.bind, pure] using hMiddleFor
      simpa [outerStep, hlt] using hMiddleYield
  have hFor :
      PySemInv ((forIn vs PUnit.unit outerStep).run st).2 n c aux :=
    pySemInv_forIn_mem (n := n) (c := c) (aux := aux)
      (xs := vs) (init := PUnit.unit) (f := outerStep) (hStep := hOuterStep) st hSem
  have hForUnit :
      PySemInv (((forIn vs PUnit.unit outerStep).bind fun _ => StateT.pure PUnit.unit).run st).2 n c aux := by
    simpa [Bind.bind, pure] using hFor
  unfold addEq7Eq9ClausesPy
  simpa [outerStep, middleStep, innerStep, Bind.bind, pure] using hForUnit

private lemma pySemInv_addMonoInitClausesPy
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    {vs : List Nat} (aux : Nat → Prop)
    (hAnti : IsAntipodalColoring c)
    (hVsMem : ∀ u : Nat, u ∈ vs → u ∈ allVertexCodes n)
    (hNbrMem : ∀ u : Nat, u ∈ vs → ∀ v : Nat, v ∈ neighborsCode n u → v ∈ allVertexCodes n)
    (hNbrAdj : ∀ u : Nat, u ∈ vs → ∀ v : Nat,
      v ∈ neighborsCode n u → Adj (natToVertex n u) (natToVertex n v))
    (hSem : PySemInv st n c aux) :
    PySemInv ((NorinSimplified.addMonoInitClausesPy n vs).run st).2 n c aux := by
  simpa [NorinSimplified.addMonoInitClausesPy, addEq5ClausesPy] using
    (pySemInv_addEq5ClausesPy
      (st := st) (n := n) (c := c) (vs := vs) aux
      hAnti hVsMem hNbrMem hNbrAdj hSem)

set_option maxHeartbeats 800000 in
private lemma pySemInv_addMonoStepClausesPy
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    {vs : List Nat} (aux : Nat → Prop)
    (hAnti : IsAntipodalColoring c)
    (hVsMem : ∀ u : Nat, u ∈ vs → u ∈ allVertexCodes n)
    (hNbrMem : ∀ u : Nat, u ∈ vs → ∀ v : Nat, v ∈ neighborsCode n u → v ∈ allVertexCodes n)
    (hNbrAdj : ∀ u : Nat, u ∈ vs → ∀ v : Nat,
      v ∈ neighborsCode n u → Adj (natToVertex n u) (natToVertex n v))
    (hSem : PySemInv st n c aux) :
    PySemInv ((NorinSimplified.addMonoStepClausesPy n vs true).run st).2 n c aux := by
  let innerStep : Nat → Nat → Nat → PUnit → PyEncM (ForInStep PUnit) := fun u w v _ =>
    if distCode n u v + 1 = distCode n u w then
      do
        let puv ← pcLitPy true u v 0
        let rvw ← rLitPy n v w
        let puw ← pcLitPy true u w 0
        (fun _ => ForInStep.yield PUnit.unit) <$> pushClausePy [-puv, -rvw, puw]
    else
      pure (ForInStep.yield PUnit.unit)
  have hInnerStep :
      ∀ (u : Nat), u ∈ vs →
      ∀ (w : Nat), w ∈ vs →
      ∀ (v : Nat), v ∈ neighborsCode n w →
      ∀ (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((innerStep u w v r).run st').2 n c aux := by
    intro u huVs w hwVs v hvNbr r st' hSem'
    by_cases hdist : distCode n u v + 1 = distCode n u w
    · let st1 : PyEncState := ((pcLitPy true u v 0).run st').2
      let puv : Int := ((pcLitPy true u v 0).run st').1
      have hPuv : PySemInv st1 n c aux :=
        pySemInv_pcLitPy (st := st') (n := n) (c := c) aux
          (isRed := true) (u := u) (v := v) (s := 0) hSem'
      let st2 : PyEncState := ((rLitPy n v w).run st1).2
      let rvw : Int := ((rLitPy n v w).run st1).1
      have hRvw : PySemInv st2 n c aux :=
        pySemInv_rLitPy (st := st1) (n := n) (c := c) aux
          (u := v) (v := w) hPuv
      let st3 : PyEncState := ((pcLitPy true u w 0).run st2).2
      let puw : Int := ((pcLitPy true u w 0).run st2).1
      have hPuw : PySemInv st3 n c aux :=
        pySemInv_pcLitPy (st := st2) (n := n) (c := c) aux
          (isRed := true) (u := u) (v := w) (s := 0) hRvw
      have hNamedPuv_st1 :
          st1.idToNamed[puv.natAbs]? = some (.pc true u v 0) := by
        simpa [st1, puv] using
          (pyStateInv_pcLitPy (st := st') (isRed := true) (u := u) (v := v) (s := 0) hSem'.inv).2
      have hNamedRvw_st2 :
          st2.idToNamed[rvw.natAbs]? =
            some
              (if vLt n (orderedCodePair n v w).1 (antipodeCode n (orderedCodePair n v w).2) = true
               then .r (orderedCodePair n (orderedCodePair n v w).1
                   (orderedCodePair n v w).2).1
                   (orderedCodePair n (orderedCodePair n v w).1
                     (orderedCodePair n v w).2).2
               else .r (orderedCodePair n (antipodeCode n (orderedCodePair n v w).1)
                   (antipodeCode n (orderedCodePair n v w).2)).1
                   (orderedCodePair n (antipodeCode n (orderedCodePair n v w).1)
                     (antipodeCode n (orderedCodePair n v w).2)).2) := by
        simpa [st2, st1, rvw] using
          (pyStateInv_rLitPy (st := st1) (n := n) (u := v) (v := w) hPuv.inv)
      have hNamedPuw_st3 :
          st3.idToNamed[puw.natAbs]? = some (.pc true u w 0) := by
        simpa [st3, st2, puw] using
          (pyStateInv_pcLitPy (st := st2) (isRed := true) (u := u) (v := w) (s := 0) hRvw.inv).2
      have hPuvLt_st1 : puv.natAbs < st1.nextId := hPuv.inv.1 hNamedPuv_st1
      have hSt1LeSt2 : st1.nextId ≤ st2.nextId := by
        simpa [st2] using
          (pyState_nextId_le_rLitPy (st := st1) (n := n) (u := v) (v := w))
      have hPuvLt_st2 : puv.natAbs < st2.nextId := lt_of_lt_of_le hPuvLt_st1 hSt1LeSt2
      have hRvwLt_st2 : rvw.natAbs < st2.nextId := hRvw.inv.1 hNamedRvw_st2
      have hSt2LeSt3 : st2.nextId ≤ st3.nextId := by
        simpa [st3] using
          (pyState_nextId_le_pcLitPy (st := st2) (isRed := true) (u := u) (v := w) (s := 0))
      have hPuvLt_st3 : puv.natAbs < st3.nextId := lt_of_lt_of_le hPuvLt_st2 hSt2LeSt3
      have hRvwLt_st3 : rvw.natAbs < st3.nextId := lt_of_lt_of_le hRvwLt_st2 hSt2LeSt3
      have hPuwLt_st3 : puw.natAbs < st3.nextId := hPuw.inv.1 hNamedPuw_st3
      have hVmem : v ∈ allVertexCodes n := hNbrMem w hwVs v hvNbr
      have hWmem : w ∈ allVertexCodes n := hVsMem w hwVs
      have hAdjWV : Adj (natToVertex n w) (natToVertex n v) := hNbrAdj w hwVs v hvNbr
      have hAdjVW : Adj (natToVertex n v) (natToVertex n w) := hAdjWV.symm
      have hStep : distCode n u v + 1 = distCode n u w := hdist
      have hClause1Sem :
          ¬ pyVarSemantics n c (.pc true u v 0) ∨
            ¬ pyVarSemantics n c (.r v w) ∨
            pyVarSemantics n c (.pc true u w 0) :=
        pySem_clause_eq7 (n := n) (c := c) (u := u) (v := v) (w := w) hAdjVW hStep
      have hSatPuv_st1 :
          CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt puv) ↔
            pyVarSemantics n c (.pc true u v 0) := by
        have hPos :
            CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (.pos puv.natAbs) ↔
              pyVarSemantics n c (.pc true u v 0) :=
          (pyLitSat_pos_named_at
            (st := st1) (n := n) (c := c) aux
            (i := puv.natAbs) (k := .pc true u v 0) hNamedPuv_st1)
        have hpEq : puv = Int.ofNat ((pcIdPy true u v 0).run st').1 := by
          unfold puv pcLitPy
          rfl
        have hLitEq : litOfDimacsInt puv = .pos puv.natAbs := by
          rw [hpEq]
          simp [litOfDimacsInt]
        simpa [hLitEq] using hPos
      have hSatRvw_st2 :
          CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt rvw) ↔
            pyVarSemantics n c (.r v w) := by
        simpa [st1, st2, rvw] using
          (pyLitSat_rLitPy_iff_red_at
            (st := st1) (n := n) (c := c) aux hPuv.inv hAnti hPuv.noZero hPuv.nextPos
            (u := v) (v := w) hVmem hWmem hAdjVW)
      have hSatPuw_st3 :
          CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt puw) ↔
            pyVarSemantics n c (.pc true u w 0) := by
        have hPos :
            CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (.pos puw.natAbs) ↔
              pyVarSemantics n c (.pc true u w 0) :=
          (pyLitSat_pos_named_at
            (st := st3) (n := n) (c := c) aux
            (i := puw.natAbs) (k := .pc true u w 0) hNamedPuw_st3)
        have hpEq : puw = Int.ofNat ((pcIdPy true u w 0).run st2).1 := by
          unfold puw pcLitPy
          rfl
        have hLitEq : litOfDimacsInt puw = .pos puw.natAbs := by
          rw [hpEq]
          simp [litOfDimacsInt]
        simpa [hLitEq] using hPos
      have hKeepPuv12 :
          CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt puv) ↔
            CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt puv) :=
        pyLitSat_rLitPy_eq_of_bound
          (st := st1) (n := n) (c := c) aux (u := v) (v := w)
          (i := puv) (by simpa using hPuvLt_st1)
      have hKeepPuv23 :
          CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt puv) ↔
            CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt puv) :=
        pyLitSat_idForPy_eq_of_bound
          (st := st2) (n := n) (c := c) aux
          (k := .pc true u w 0) (i := puv) (by simpa using hPuvLt_st2)
      have hKeepRvw23 :
          CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt rvw) ↔
            CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt rvw) :=
        pyLitSat_idForPy_eq_of_bound
          (st := st2) (n := n) (c := c) aux
          (k := .pc true u w 0) (i := rvw) (by simpa using hRvwLt_st2)
      have hPuvNatNe0 : puv.natAbs ≠ 0 := by
        intro h0
        have hId0 : st1.idToNamed[0]? = some (.pc true u v 0) := by
          simpa [h0] using hNamedPuv_st1
        have hContra :
            (none : Option PyVarKey) = some (.pc true u v 0) := by
          simpa [hPuv.noZero] using hId0
        cases hContra
      have hPuvNe0 : puv ≠ 0 := by
        intro h0
        exact hPuvNatNe0 (by simpa [h0])
      have hRvwNe0 : rvw ≠ 0 := by
        simpa [rvw] using
          (rLitPy_ne_zero (st := st1) (n := n) (u := v) (v := w)
            hPuv.inv hPuv.noZero hPuv.nextPos)
      have hClause1Sat :
          ∃ i : Int, i ∈ ([-puv, -rvw, puw] : List Int) ∧
            CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt i) := by
        rcases hClause1Sem with hNotPuv | hRest
        · refine ⟨-puv, by simp, ?_⟩
          have hNotSatPuv_st1 :
              ¬ CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt puv) := by
            intro hSat
            exact hNotPuv (hSatPuv_st1.1 hSat)
          have hNotSatPuv_st2 :
              ¬ CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt puv) := by
            intro hSat
            exact hNotSatPuv_st1 (hKeepPuv12.1 hSat)
          have hNotSatPuv_st3 :
              ¬ CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt puv) := by
            intro hSat
            exact hNotSatPuv_st2 (hKeepPuv23.1 hSat)
          exact (litSat_dimacs_neg_local
            (τ := pyAssignmentAt st3 n c aux) (i := puv) hPuvNe0).2 hNotSatPuv_st3
        · rcases hRest with hNotRvw | hPuwSem
          · refine ⟨-rvw, by simp, ?_⟩
            have hNotSatRvw_st2 :
                ¬ CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt rvw) := by
              intro hSat
              exact hNotRvw (hSatRvw_st2.1 hSat)
            have hNotSatRvw_st3 :
                ¬ CNF.Lit.Sat (pyAssignmentAt st3 n c aux) (litOfDimacsInt rvw) := by
              intro hSat
              exact hNotSatRvw_st2 (hKeepRvw23.1 hSat)
            exact (litSat_dimacs_neg_local
              (τ := pyAssignmentAt st3 n c aux) (i := rvw) hRvwNe0).2 hNotSatRvw_st3
          · exact ⟨puw, by simp, (hSatPuw_st3.2 hPuwSem)⟩
      have hClause1Bound :
          ∀ i : Int, i ∈ ([-puv, -rvw, puw] : List Int) → i.natAbs < st3.nextId := by
        intro i hi
        rcases List.mem_cons.1 hi with hi | hi
        · have hiEq : i = -puv := hi
          subst hiEq
          simpa using hPuvLt_st3
        · rcases List.mem_cons.1 hi with hi | hi
          · have hiEq : i = -rvw := hi
            subst hiEq
            simpa using hRvwLt_st3
          · have hiEq : i = puw := by simpa using hi
            subst hiEq
            exact hPuwLt_st3
      have hPush1 :
          PySemInv ((pushClausePy [-puv, -rvw, puw]).run st3).2 n c aux :=
        pySemInv_pushClausePy (st := st3) (n := n) (c := c) aux
          (cl := [-puv, -rvw, puw]) hPuw hClause1Sat hClause1Bound
      simpa [innerStep, hdist, st1, st2, st3, puv, rvw, puw, Bind.bind, pure] using hPush1
    · simpa [innerStep, hdist] using hSem'
  let middleStep : Nat → Nat → PUnit → PyEncM (ForInStep PUnit) := fun u w _ =>
    if w ∈ neighborsCode n u then
      pure (ForInStep.yield PUnit.unit)
    else
      let inner := forIn (neighborsCode n w) PUnit.unit (innerStep u w)
      inner.bind fun _ => StateT.pure (ForInStep.yield PUnit.unit)
  have hMiddleStep :
      ∀ (u : Nat), u ∈ vs →
      ∀ (w : Nat), w ∈ vs →
      ∀ (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((middleStep u w r).run st').2 n c aux := by
    intro u huVs w hwVs r st' hSem'
    by_cases hNbr : w ∈ neighborsCode n u
    · simpa [middleStep, hNbr] using hSem'
    · have hInnerFor :
        PySemInv ((forIn (neighborsCode n w) PUnit.unit (innerStep u w)).run st').2 n c aux :=
        pySemInv_forIn_mem (n := n) (c := c) (aux := aux)
          (xs := neighborsCode n w) (init := PUnit.unit) (f := innerStep u w)
          (hStep := hInnerStep u huVs w hwVs) st' hSem'
      have hInnerYield :
          PySemInv
            (((forIn (neighborsCode n w) PUnit.unit (innerStep u w)).bind
              fun _ => StateT.pure (ForInStep.yield PUnit.unit)).run st').2 n c aux := by
        simpa [Bind.bind, pure] using hInnerFor
      simpa [middleStep, hNbr] using hInnerYield
  let outerStep : Nat → PUnit → PyEncM (ForInStep PUnit) := fun u _ =>
    if vLt n (antipodeCode n u) u then
      pure (ForInStep.yield PUnit.unit)
    else
      let middle := forIn vs PUnit.unit (middleStep u)
      middle.bind fun _ => StateT.pure (ForInStep.yield PUnit.unit)
  have hOuterStep :
      ∀ (u : Nat), u ∈ vs →
      ∀ (r : PUnit) (st' : PyEncState),
        PySemInv st' n c aux →
          PySemInv ((outerStep u r).run st').2 n c aux := by
    intro u huVs r st' hSem'
    by_cases hlt : vLt n (antipodeCode n u) u = true
    · simpa [outerStep, hlt] using hSem'
    · have hMiddleFor :
        PySemInv ((forIn vs PUnit.unit (middleStep u)).run st').2 n c aux :=
        pySemInv_forIn_mem (n := n) (c := c) (aux := aux)
          (xs := vs) (init := PUnit.unit) (f := middleStep u)
          (hStep := hMiddleStep u huVs) st' hSem'
      have hMiddleYield :
          PySemInv
            (((forIn vs PUnit.unit (middleStep u)).bind
              fun _ => StateT.pure (ForInStep.yield PUnit.unit)).run st').2 n c aux := by
        simpa [Bind.bind, pure] using hMiddleFor
      simpa [outerStep, hlt] using hMiddleYield
  have hFor :
      PySemInv ((forIn vs PUnit.unit outerStep).run st).2 n c aux :=
    pySemInv_forIn_mem (n := n) (c := c) (aux := aux)
      (xs := vs) (init := PUnit.unit) (f := outerStep) (hStep := hOuterStep) st hSem
  have hForUnit :
      PySemInv (((forIn vs PUnit.unit outerStep).bind fun _ => StateT.pure PUnit.unit).run st).2 n c aux := by
    simpa [Bind.bind, pure] using hFor
  unfold NorinSimplified.addMonoStepClausesPy
  simpa [outerStep, middleStep, innerStep, Bind.bind, pure] using hForUnit

private lemma pySemInv_addNoMonoAntipodeUnitClausesPy
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    {vs : List Nat} (aux : Nat → Prop)
    (hNoGeo : NoMonochromaticAntipodalGeodesic n c)
    (hVsMem : ∀ u : Nat, u ∈ vs → u ∈ allVertexCodes n)
    (hSem : PySemInv st n c aux) :
    PySemInv ((NorinSimplified.addNoMonoAntipodeUnitClausesPy n vs).run st).2 n c aux := by
  simpa [NorinSimplified.addNoMonoAntipodeUnitClausesPy, addConjecture1UnitClausesPy] using
    (pySemInv_addConjecture1UnitClausesPy
      (st := st) (n := n) (c := c) (vs := vs) aux hNoGeo hVsMem hSem)

private lemma pyClauseSat_map_litOfDimacsInt_of_int
    {τ : CNF.Assignment Nat} {cl : Array Int}
    (hSat : ∃ i : Int, i ∈ cl.toList ∧ CNF.Lit.Sat τ (litOfDimacsInt i)) :
    CNF.Clause.Sat τ (cl.toList.map litOfDimacsInt) := by
  rcases hSat with ⟨i, hiMem, hiSat⟩
  refine ⟨litOfDimacsInt i, ?_, hiSat⟩
  exact List.mem_map.mpr ⟨i, hiMem, rfl⟩

private lemma pyFormulaSat_of_pySemInv
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop)
    (hSem : PySemInv st n c aux) :
    CNF.Formula.Sat
      (pyAssignmentAt st n c aux)
      {cl | cl ∈ st.clauses.toList.map clauseOfDimacsArray} := by
  intro cl hcl
  rcases List.mem_map.mp hcl with ⟨clInt, hMem, rfl⟩
  have hMemArr : clInt ∈ st.clauses := by
    simpa using hMem
  exact pyClauseSat_map_litOfDimacsInt_of_int
    (τ := pyAssignmentAt st n c aux) (cl := clInt) (hSem.sat clInt hMemArr)

private lemma pyFormulaSat_pysat_of_pySemInv
    {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop)
    (hSem : PySemInv (pysatState n) n c aux) :
    CNF.Formula.Sat (pyAssignment n c aux) (PysatConjecture1Formula n) := by
  simpa [pyAssignment, pysatState, PysatConjecture1Formula, pysatConjecture1Clauses] using
    (pyFormulaSat_of_pySemInv
      (st := pysatState n) (n := n) (c := c) aux hSem)

private lemma pysatSat_of_pySemInv
    {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop)
    (hSem : PySemInv (pysatState n) n c aux) :
    CNF.Satisfiable (PysatConjecture1Formula n) := by
  refine ⟨pyAssignment n c aux, ?_⟩
  exact pyFormulaSat_pysat_of_pySemInv (n := n) (c := c) aux hSem

private lemma litSat_dimacs_neg {τ : CNF.Assignment Nat} {i : Int} (hi0 : i ≠ 0) :
    CNF.Lit.Sat τ (litOfDimacsInt (-i)) ↔ ¬ CNF.Lit.Sat τ (litOfDimacsInt i) := by
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          exfalso
          exact hi0 rfl
      | succ n =>
          change CNF.Lit.Sat τ (litOfDimacsInt (Int.negSucc n)) ↔
            ¬ CNF.Lit.Sat τ (litOfDimacsInt (Int.ofNat (Nat.succ n)))
          have hltFalse : ¬ (((n : Int) + 1) < 0) := by
            have hnonneg : (0 : Int) ≤ (n : Int) + 1 := by
              exact add_nonneg (Int.natCast_nonneg n) (show (0 : Int) ≤ 1 by decide)
            exact not_lt_of_ge hnonneg
          simp [litOfDimacsInt, CNF.Lit.Sat, hltFalse]
  | negSucc n =>
      change CNF.Lit.Sat τ (litOfDimacsInt (Int.ofNat (Nat.succ n))) ↔
        ¬ CNF.Lit.Sat τ (litOfDimacsInt (Int.negSucc n))
      have hltFalse : ¬ (((n : Int) + 1) < 0) := by
        have hnonneg : (0 : Int) ≤ (n : Int) + 1 := by
          exact add_nonneg (Int.natCast_nonneg n) (show (0 : Int) ≤ 1 by decide)
        exact not_lt_of_ge hnonneg
      simp [litOfDimacsInt, CNF.Lit.Sat, hltFalse]

private noncomputable def litVal (τ : CNF.Assignment Nat) (i : Int) : Bool := by
  classical
  exact if CNF.Lit.Sat τ (litOfDimacsInt i) then true else false

private def boolSeqCode : List Bool → Nat
  | [] => 0
  | b :: bs => Bool.toNat b * 2 ^ bs.length + boolSeqCode bs

private lemma pow_lt_pow_succ (n : Nat) : 2 ^ n < 2 ^ (n + 1) := by
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hlt : 2 ^ n < 2 ^ n * 2 := by
    simpa [Nat.one_mul, Nat.mul_comm] using Nat.lt_mul_of_pos_right hpos (show 1 < 2 by decide)
  simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt

private lemma boolSeqCode_lt_pow : ∀ bs : List Bool, boolSeqCode bs < 2 ^ bs.length := by
  intro bs
  induction bs with
  | nil => simp [boolSeqCode]
  | cons b bs ih =>
      cases b with
      | false =>
          calc
            boolSeqCode (false :: bs) = boolSeqCode bs := by simp [boolSeqCode]
            _ < 2 ^ bs.length := ih
            _ < 2 ^ (bs.length + 1) := pow_lt_pow_succ bs.length
      | true =>
          have hlt : 2 ^ bs.length + boolSeqCode bs < 2 ^ bs.length + 2 ^ bs.length :=
            Nat.add_lt_add_left ih (2 ^ bs.length)
          calc
            boolSeqCode (true :: bs) = 2 ^ bs.length + boolSeqCode bs := by simp [boolSeqCode]
            _ < 2 ^ bs.length + 2 ^ bs.length := hlt
            _ = 2 ^ (bs.length + 1) := by
              simp [Nat.pow_succ, Nat.mul_comm, Nat.two_mul]

private lemma boolSeqCode_cons_le_tail {b c : Bool} {bs cs : List Bool}
    (hlen : bs.length = cs.length)
    (hcode : boolSeqCode (b :: bs) ≤ boolSeqCode (c :: cs)) :
    (b = true → c = true) ∧
    (b = c → boolSeqCode bs ≤ boolSeqCode cs) := by
  constructor
  · intro hb
    cases b with
    | false => cases hb
    | true =>
        cases c with
        | true => rfl
        | false =>
            exfalso
            have hL : 2 ^ bs.length ≤ boolSeqCode (true :: bs) := by
              simp [boolSeqCode]
            have hR : boolSeqCode (false :: cs) < 2 ^ cs.length := by
              simpa [boolSeqCode] using boolSeqCode_lt_pow cs
            have hContra : 2 ^ bs.length < 2 ^ bs.length := by
              calc
                2 ^ bs.length ≤ boolSeqCode (true :: bs) := hL
                _ ≤ boolSeqCode (false :: cs) := hcode
                _ < 2 ^ cs.length := hR
                _ = 2 ^ bs.length := by simpa [hlen]
            exact (lt_irrefl _ hContra)
  · intro hEq
    subst hEq
    cases b with
    | false =>
        simpa [boolSeqCode] using hcode
    | true =>
        have hpow : 2 ^ bs.length = 2 ^ cs.length := by simpa [hlen]
        have hcode' : 2 ^ bs.length + boolSeqCode bs ≤ 2 ^ bs.length + boolSeqCode cs := by
          simpa [boolSeqCode, hpow] using hcode
        exact Nat.add_le_add_iff_left.mp hcode'

private lemma litVal_true_iff {τ : CNF.Assignment Nat} {i : Int} :
    litVal τ i = true ↔ CNF.Lit.Sat τ (litOfDimacsInt i) := by
  classical
  unfold litVal
  split_ifs <;> simp_all

private lemma litVal_false_iff {τ : CNF.Assignment Nat} {i : Int} :
    litVal τ i = false ↔ ¬ CNF.Lit.Sat τ (litOfDimacsInt i) := by
  classical
  unfold litVal
  split_ifs <;> simp_all

private lemma litVal_eq_of_litSat_iff
    {τ τ' : CNF.Assignment Nat} {i : Int}
    (hSatEq : CNF.Lit.Sat τ (litOfDimacsInt i) ↔ CNF.Lit.Sat τ' (litOfDimacsInt i)) :
    litVal τ i = litVal τ' i := by
  by_cases hτ : CNF.Lit.Sat τ (litOfDimacsInt i)
  · have hτ' : CNF.Lit.Sat τ' (litOfDimacsInt i) := hSatEq.mp hτ
    have hvτ : litVal τ i = true := (litVal_true_iff (τ := τ) (i := i)).2 hτ
    have hvτ' : litVal τ' i = true := (litVal_true_iff (τ := τ') (i := i)).2 hτ'
    simp [hvτ, hvτ']
  · have hτ' : ¬ CNF.Lit.Sat τ' (litOfDimacsInt i) := by
      intro hτ'
      exact hτ (hSatEq.mpr hτ')
    have hvτ : litVal τ i = false := (litVal_false_iff (τ := τ) (i := i)).2 hτ
    have hvτ' : litVal τ' i = false := (litVal_false_iff (τ := τ') (i := i)).2 hτ'
    simp [hvτ, hvτ']

private lemma boolSeqCode_eq_map_litVal_of_litSatEq
    {τ τ' : CNF.Assignment Nat} :
    ∀ (xs : List Int),
      (∀ i : Int, i ∈ xs →
        (CNF.Lit.Sat τ (litOfDimacsInt i) ↔ CNF.Lit.Sat τ' (litOfDimacsInt i))) →
      boolSeqCode (xs.map (litVal τ)) = boolSeqCode (xs.map (litVal τ')) := by
  intro xs hEq
  induction xs with
  | nil =>
      simp [boolSeqCode]
  | cons x xt ih =>
      have hxVal : litVal τ x = litVal τ' x :=
        litVal_eq_of_litSat_iff (τ := τ) (τ' := τ') (i := x) (hEq x (by simp))
      have hTailEq :
          ∀ i : Int, i ∈ xt →
            (CNF.Lit.Sat τ (litOfDimacsInt i) ↔ CNF.Lit.Sat τ' (litOfDimacsInt i)) := by
        intro i hi
        exact hEq i (by simp [hi])
      have hTailVal :
          boolSeqCode (xt.map (litVal τ)) = boolSeqCode (xt.map (litVal τ')) :=
        ih hTailEq
      simp [boolSeqCode, hxVal, hTailVal]

private lemma litSat_imp_of_boolSeqCode_le
    {τ : CNF.Assignment Nat} {x y : Int} {xs ys : List Int}
    (hlen : xs.length = ys.length)
    (hCode :
      boolSeqCode (litVal τ x :: xs.map (litVal τ)) ≤
        boolSeqCode (litVal τ y :: ys.map (litVal τ))) :
    CNF.Lit.Sat τ (litOfDimacsInt x) → CNF.Lit.Sat τ (litOfDimacsInt y) := by
  intro hx
  have hHead :
      litVal τ x = true → litVal τ y = true :=
    (boolSeqCode_cons_le_tail (bs := xs.map (litVal τ)) (cs := ys.map (litVal τ))
      (by simpa [hlen]) hCode).1
  have hxVal : litVal τ x = true := (litVal_true_iff (τ := τ) (i := x)).2 hx
  have hyVal : litVal τ y = true := hHead hxVal
  exact (litVal_true_iff (τ := τ) (i := y)).1 hyVal

private lemma tail_boolSeqCode_le_of_head_eq
    {τ : CNF.Assignment Nat} {x y : Int} {xs ys : List Int}
    (hlen : xs.length = ys.length)
    (hCode :
      boolSeqCode (litVal τ x :: xs.map (litVal τ)) ≤
        boolSeqCode (litVal τ y :: ys.map (litVal τ)))
    (hEq : CNF.Lit.Sat τ (litOfDimacsInt x) ↔ CNF.Lit.Sat τ (litOfDimacsInt y)) :
    boolSeqCode (xs.map (litVal τ)) ≤ boolSeqCode (ys.map (litVal τ)) := by
  have hLitEq : litVal τ x = litVal τ y := by
    by_cases hx : CNF.Lit.Sat τ (litOfDimacsInt x)
    · have hy : CNF.Lit.Sat τ (litOfDimacsInt y) := hEq.1 hx
      have hxVal : litVal τ x = true := (litVal_true_iff (τ := τ) (i := x)).2 hx
      have hyVal : litVal τ y = true := (litVal_true_iff (τ := τ) (i := y)).2 hy
      simpa [hxVal, hyVal]
    · have hy : ¬ CNF.Lit.Sat τ (litOfDimacsInt y) := by
        intro hy
        exact hx (hEq.2 hy)
      have hxVal : litVal τ x = false := (litVal_false_iff (τ := τ) (i := x)).2 hx
      have hyVal : litVal τ y = false := (litVal_false_iff (τ := τ) (i := y)).2 hy
      simpa [hxVal, hyVal]
  exact
    (boolSeqCode_cons_le_tail (bs := xs.map (litVal τ)) (cs := ys.map (litVal τ))
      (by simpa [hlen]) hCode).2 hLitEq

private lemma pyClauseSat_lexComparator_main {τ : CNF.Assignment Nat} {allPrev : Nat} {x y : Int}
    (hx0 : x ≠ 0)
    (hImp : CNF.Lit.Sat τ (litOfDimacsInt x) → CNF.Lit.Sat τ (litOfDimacsInt y)) :
    CNF.Clause.Sat τ ([-Int.ofNat allPrev, -x, y].map litOfDimacsInt) := by
  by_cases hx : CNF.Lit.Sat τ (litOfDimacsInt x)
  · refine ⟨litOfDimacsInt y, ?_, ?_⟩
    · simp
    · exact hImp hx
  · refine ⟨litOfDimacsInt (-x), ?_, ?_⟩
    · simp
    · exact (litSat_dimacs_neg (τ := τ) (i := x) hx0).2 hx

private lemma pyClauseSat_lexComparator_main_of_boolSeqCode_le
    {τ : CNF.Assignment Nat} {allPrev : Nat} {x y : Int} {xs ys : List Int}
    (hx0 : x ≠ 0)
    (hlen : xs.length = ys.length)
    (hCode :
      boolSeqCode (litVal τ x :: xs.map (litVal τ)) ≤
        boolSeqCode (litVal τ y :: ys.map (litVal τ))) :
    CNF.Clause.Sat τ ([-Int.ofNat allPrev, -x, y].map litOfDimacsInt) := by
  refine pyClauseSat_lexComparator_main (τ := τ) (allPrev := allPrev) (x := x) (y := y) hx0 ?_
  exact litSat_imp_of_boolSeqCode_le (τ := τ) (x := x) (y := y) (xs := xs) (ys := ys) hlen hCode

private lemma pyClauseSat_lexComparator_main_guarded
    {τ : CNF.Assignment Nat} {allPrev : Nat} {x y : Int} {xs ys : List Int}
    (hAllPrevPos : 0 < allPrev)
    (hx0 : x ≠ 0)
    (hlen : xs.length = ys.length)
    (hCodeImp :
      τ allPrev →
        boolSeqCode (litVal τ x :: xs.map (litVal τ)) ≤
          boolSeqCode (litVal τ y :: ys.map (litVal τ))) :
    CNF.Clause.Sat τ ([-Int.ofNat allPrev, -x, y].map litOfDimacsInt) := by
  by_cases hA : τ allPrev
  · exact pyClauseSat_lexComparator_main_of_boolSeqCode_le
      (τ := τ) (allPrev := allPrev) (x := x) (y := y) (xs := xs) (ys := ys)
      hx0 hlen (hCodeImp hA)
  · refine ⟨litOfDimacsInt (-Int.ofNat allPrev), ?_, ?_⟩
    · simp
    · cases allPrev with
      | zero =>
          cases (Nat.not_lt_zero 0 hAllPrevPos)
      | succ k =>
          change CNF.Lit.Sat τ (litOfDimacsInt (Int.negSucc k))
          simp [litOfDimacsInt, CNF.Lit.Sat, hA]

private lemma lexAllPrev_tail_imp_of_boolSeqCode_le
    {τ : CNF.Assignment Nat} {allPrev allPrevNew : Nat} {x y : Int} {xs ys : List Int}
    (hDef : τ allPrevNew ↔
      τ allPrev ∧ (CNF.Lit.Sat τ (litOfDimacsInt x) ↔ CNF.Lit.Sat τ (litOfDimacsInt y)))
    (hlen : xs.length = ys.length)
    (hCodeImp :
      τ allPrev →
        boolSeqCode (litVal τ x :: xs.map (litVal τ)) ≤
          boolSeqCode (litVal τ y :: ys.map (litVal τ))) :
    τ allPrevNew →
      boolSeqCode (xs.map (litVal τ)) ≤ boolSeqCode (ys.map (litVal τ)) := by
  intro hNew
  have hA : τ allPrev := (hDef.1 hNew).1
  have hEq : CNF.Lit.Sat τ (litOfDimacsInt x) ↔ CNF.Lit.Sat τ (litOfDimacsInt y) :=
    (hDef.1 hNew).2
  exact tail_boolSeqCode_le_of_head_eq
    (τ := τ) (x := x) (y := y) (xs := xs) (ys := ys) hlen (hCodeImp hA) hEq

private lemma lexAllPrev_forward1
    {τ : CNF.Assignment Nat} {allPrev allPrevNew : Nat} {x y : Int}
    (hDef : τ allPrevNew ↔
      τ allPrev ∧ (CNF.Lit.Sat τ (litOfDimacsInt x) ↔ CNF.Lit.Sat τ (litOfDimacsInt y)))
    (hImp : CNF.Lit.Sat τ (litOfDimacsInt x) → CNF.Lit.Sat τ (litOfDimacsInt y)) :
    τ allPrev → CNF.Lit.Sat τ (litOfDimacsInt x) → τ allPrevNew := by
  intro hA hx
  exact hDef.2 ⟨hA, ⟨hImp, fun _ => hx⟩⟩

private lemma lexAllPrev_forward2
    {τ : CNF.Assignment Nat} {allPrev allPrevNew : Nat} {x y : Int}
    (hDef : τ allPrevNew ↔
      τ allPrev ∧ (CNF.Lit.Sat τ (litOfDimacsInt x) ↔ CNF.Lit.Sat τ (litOfDimacsInt y)))
    (hImp : CNF.Lit.Sat τ (litOfDimacsInt x) → CNF.Lit.Sat τ (litOfDimacsInt y)) :
    τ allPrev → ¬ CNF.Lit.Sat τ (litOfDimacsInt y) → τ allPrevNew := by
  intro hA hny
  exact hDef.2 ⟨hA, ⟨hImp, fun hy => False.elim (hny hy)⟩⟩

private lemma pyClauseSat_lexComparator_fresh1 {τ : CNF.Assignment Nat}
    {allPrev allPrevNew : Nat} {x : Int}
    (hAllPrevPos : 0 < allPrev)
    (hx0 : x ≠ 0)
    (hForward : τ allPrev → CNF.Lit.Sat τ (litOfDimacsInt x) → τ allPrevNew) :
    CNF.Clause.Sat τ ([-Int.ofNat allPrev, -x, Int.ofNat allPrevNew].map litOfDimacsInt) := by
  by_cases hA : τ allPrev
  · by_cases hx : CNF.Lit.Sat τ (litOfDimacsInt x)
    · refine ⟨litOfDimacsInt (Int.ofNat allPrevNew), ?_, ?_⟩
      · simp
      · exact hForward hA hx
    · refine ⟨litOfDimacsInt (-x), ?_, ?_⟩
      · simp
      · exact (litSat_dimacs_neg (τ := τ) (i := x) hx0).2 hx
  · refine ⟨litOfDimacsInt (-Int.ofNat allPrev), ?_, ?_⟩
    · simp
    · cases allPrev with
      | zero =>
          cases (Nat.not_lt_zero 0 hAllPrevPos)
      | succ k =>
          change CNF.Lit.Sat τ (litOfDimacsInt (Int.negSucc k))
          simp [litOfDimacsInt, CNF.Lit.Sat, hA]

private lemma pyClauseSat_lexComparator_fresh2 {τ : CNF.Assignment Nat}
    {allPrev allPrevNew : Nat} {y : Int}
    (hAllPrevPos : 0 < allPrev)
    (hForward : τ allPrev → ¬ CNF.Lit.Sat τ (litOfDimacsInt y) → τ allPrevNew) :
    CNF.Clause.Sat τ ([-Int.ofNat allPrev, y, Int.ofNat allPrevNew].map litOfDimacsInt) := by
  by_cases hA : τ allPrev
  · by_cases hy : CNF.Lit.Sat τ (litOfDimacsInt y)
    · refine ⟨litOfDimacsInt y, ?_, ?_⟩
      · simp
      · exact hy
    · refine ⟨litOfDimacsInt (Int.ofNat allPrevNew), ?_, ?_⟩
      · simp
      · exact hForward hA hy
  · refine ⟨litOfDimacsInt (-Int.ofNat allPrev), ?_, ?_⟩
    · simp
    · cases allPrev with
      | zero =>
          cases (Nat.not_lt_zero 0 hAllPrevPos)
      | succ k =>
          change CNF.Lit.Sat τ (litOfDimacsInt (Int.negSucc k))
          simp [litOfDimacsInt, CNF.Lit.Sat, hA]

private lemma pyClauseSat_lexComparator_unit {τ : CNF.Assignment Nat} {allPrev : Nat}
    (hA : τ allPrev) :
    CNF.Clause.Sat τ ([Int.ofNat allPrev].map litOfDimacsInt) := by
  refine ⟨litOfDimacsInt (Int.ofNat allPrev), ?_, ?_⟩
  · simp
  · simpa [litOfDimacsInt, CNF.Lit.Sat] using hA

private lemma pyClauseSat_lexComparator_step_of_boolSeqCode_le
    {τ : CNF.Assignment Nat}
    {allPrev allPrevNew : Nat} {x y : Int} {xs ys : List Int}
    (hAllPrevPos : 0 < allPrev)
    (hx0 : x ≠ 0)
    (hlen : xs.length = ys.length)
    (hDef : τ allPrevNew ↔
      τ allPrev ∧ (CNF.Lit.Sat τ (litOfDimacsInt x) ↔ CNF.Lit.Sat τ (litOfDimacsInt y)))
    (hCodeImp :
      τ allPrev →
        boolSeqCode (litVal τ x :: xs.map (litVal τ)) ≤
          boolSeqCode (litVal τ y :: ys.map (litVal τ))) :
    CNF.Clause.Sat τ ([-Int.ofNat allPrev, -x, y].map litOfDimacsInt) ∧
      CNF.Clause.Sat τ ([-Int.ofNat allPrev, -x, Int.ofNat allPrevNew].map litOfDimacsInt) ∧
      CNF.Clause.Sat τ ([-Int.ofNat allPrev, y, Int.ofNat allPrevNew].map litOfDimacsInt) ∧
      (τ allPrevNew →
        boolSeqCode (xs.map (litVal τ)) ≤ boolSeqCode (ys.map (litVal τ))) := by
  have hMain :
      CNF.Clause.Sat τ ([-Int.ofNat allPrev, -x, y].map litOfDimacsInt) :=
    pyClauseSat_lexComparator_main_guarded
      (τ := τ) (allPrev := allPrev) (x := x) (y := y) (xs := xs) (ys := ys)
      hAllPrevPos hx0 hlen hCodeImp
  have hFresh1 :
      CNF.Clause.Sat τ ([-Int.ofNat allPrev, -x, Int.ofNat allPrevNew].map litOfDimacsInt) := by
    refine pyClauseSat_lexComparator_fresh1
      (τ := τ) (allPrev := allPrev) (allPrevNew := allPrevNew) (x := x)
      hAllPrevPos hx0 ?_
    intro hA hx
    have hImpLocal :
        CNF.Lit.Sat τ (litOfDimacsInt x) → CNF.Lit.Sat τ (litOfDimacsInt y) := by
      intro hx'
      exact litSat_imp_of_boolSeqCode_le
        (τ := τ) (x := x) (y := y) (xs := xs) (ys := ys) hlen (hCodeImp hA) hx'
    exact lexAllPrev_forward1 (τ := τ) (allPrev := allPrev) (allPrevNew := allPrevNew)
      (x := x) (y := y) hDef hImpLocal hA hx
  have hFresh2 :
      CNF.Clause.Sat τ ([-Int.ofNat allPrev, y, Int.ofNat allPrevNew].map litOfDimacsInt) := by
    refine pyClauseSat_lexComparator_fresh2
      (τ := τ) (allPrev := allPrev) (allPrevNew := allPrevNew) (y := y)
      hAllPrevPos ?_
    intro hA hny
    have hImpLocal :
        CNF.Lit.Sat τ (litOfDimacsInt x) → CNF.Lit.Sat τ (litOfDimacsInt y) := by
      intro hx'
      exact litSat_imp_of_boolSeqCode_le
        (τ := τ) (x := x) (y := y) (xs := xs) (ys := ys) hlen (hCodeImp hA) hx'
    exact lexAllPrev_forward2 (τ := τ) (allPrev := allPrev) (allPrevNew := allPrevNew)
      (x := x) (y := y) hDef hImpLocal hA hny
  have hTailImp :
      τ allPrevNew → boolSeqCode (xs.map (litVal τ)) ≤ boolSeqCode (ys.map (litVal τ)) :=
    lexAllPrev_tail_imp_of_boolSeqCode_le
      (τ := τ) (allPrev := allPrev) (allPrevNew := allPrevNew)
      (x := x) (y := y) (xs := xs) (ys := ys)
      hDef hlen hCodeImp
  exact ⟨hMain, hFresh1, hFresh2, hTailImp⟩

private lemma pySemInv_lexSmallerEqLoopPy
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop)
    {maxComparisons : Option Nat} {xs ys : List Int} {allPrevNow rcnt : Nat}
    (hSem : PySemInv st n c aux)
    (hAllPrevPos : 0 < allPrevNow)
    (hAllPrevLt : allPrevNow < st.nextId)
    (hLen : xs.length = ys.length)
    (hBoundXs : ∀ i : Int, i ∈ xs → i.natAbs < st.nextId)
    (hBoundYs : ∀ i : Int, i ∈ ys → i.natAbs < st.nextId)
    (hNoZeroXs : ∀ i : Int, i ∈ xs → i ≠ 0)
    (hNoZeroYs : ∀ i : Int, i ∈ ys → i ≠ 0)
    (hCodeImp :
      pyAssignmentAt st n c aux allPrevNow →
        boolSeqCode (xs.map (litVal (pyAssignmentAt st n c aux))) ≤
          boolSeqCode (ys.map (litVal (pyAssignmentAt st n c aux)))) :
    ∃ aux' : Nat → Prop,
      PySemInv ((lexSmallerEqLoopPy maxComparisons xs ys allPrevNow rcnt).run st).2 n c aux' := by
  induction xs generalizing ys allPrevNow rcnt st aux with
  | nil =>
      cases ys with
      | nil =>
          exact ⟨aux, by simpa [lexSmallerEqLoopPy] using hSem⟩
      | cons y yt =>
          cases (Nat.succ_ne_zero yt.length (hLen.symm))
  | cons x xt ih =>
      cases ys with
      | nil =>
          cases (Nat.succ_ne_zero xt.length hLen)
      | cons y yt =>
          have hLenTail : xt.length = yt.length := by
            simpa using Nat.succ.inj hLen
          have hxBound : x.natAbs < st.nextId := hBoundXs x (by simp)
          have hyBound : y.natAbs < st.nextId := hBoundYs y (by simp)
          have hBoundXt : ∀ i : Int, i ∈ xt → i.natAbs < st.nextId := by
            intro i hi
            exact hBoundXs i (by simp [hi])
          have hBoundYt : ∀ i : Int, i ∈ yt → i.natAbs < st.nextId := by
            intro i hi
            exact hBoundYs i (by simp [hi])
          have hx0 : x ≠ 0 := hNoZeroXs x (by simp)
          have hy0 : y ≠ 0 := hNoZeroYs y (by simp)
          have hNoZeroXt : ∀ i : Int, i ∈ xt → i ≠ 0 := by
            intro i hi
            exact hNoZeroXs i (by simp [hi])
          have hNoZeroYt : ∀ i : Int, i ∈ yt → i ≠ 0 := by
            intro i hi
            exact hNoZeroYs i (by simp [hi])
          by_cases hxy : x = y
          · have hCodeImpTail :
              pyAssignmentAt st n c aux allPrevNow →
                boolSeqCode (xt.map (litVal (pyAssignmentAt st n c aux))) ≤
                  boolSeqCode (yt.map (litVal (pyAssignmentAt st n c aux))) := by
              intro hA
              have hEqSat :
                  CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt x) ↔
                    CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt y) := by
                simpa [hxy]
              exact tail_boolSeqCode_le_of_head_eq
                (τ := pyAssignmentAt st n c aux) (x := x) (y := y)
                (xs := xt) (ys := yt) hLenTail (hCodeImp hA) hEqSat
            rcases
              ih (aux := aux) (st := st) (ys := yt) (allPrevNow := allPrevNow) (rcnt := rcnt)
                hSem hAllPrevPos hAllPrevLt hLenTail hBoundXt hBoundYt
                hNoZeroXt hNoZeroYt hCodeImpTail with ⟨aux', hRec⟩
            exact ⟨aux', by simpa [lexSmallerEqLoopPy, hxy] using hRec⟩
          · let cl1 : List Int := [-Int.ofNat allPrevNow, -x, y]
            let st1 : PyEncState := ((pushClausePy cl1).run st).2
            have hClause1Sat :
                CNF.Clause.Sat (pyAssignmentAt st n c aux) (cl1.map litOfDimacsInt) := by
              simpa [cl1] using
                (pyClauseSat_lexComparator_main_guarded
                  (τ := pyAssignmentAt st n c aux) (allPrev := allPrevNow)
                  (x := x) (y := y) (xs := xt) (ys := yt)
                  hAllPrevPos hx0 hLenTail hCodeImp)
            have hClause1Bound :
                ∀ i : Int, i ∈ cl1 → i.natAbs < st.nextId := by
              intro i hi
              rcases List.mem_cons.1 hi with hi | hi
              · have hiEq : i = -Int.ofNat allPrevNow := hi
                subst hiEq
                simpa using hAllPrevLt
              · rcases List.mem_cons.1 hi with hi | hi
                · have hiEq : i = -x := hi
                  subst hiEq
                  simpa using hxBound
                · have hiEq : i = y := by simpa using hi
                  subst hiEq
                  exact hyBound
            have hSem1 : PySemInv st1 n c aux :=
              pySemInv_pushClausePy (st := st) (n := n) (c := c) aux
                (cl := cl1) hSem
                (by
                  rcases hClause1Sat with ⟨l, hlMem, hlSat⟩
                  rcases List.mem_map.mp hlMem with ⟨i, hiMem, hiEq⟩
                  subst hiEq
                  exact ⟨i, hiMem, hlSat⟩)
                hClause1Bound
            let allPrevNew : Nat := (freshIdPy.run st1).1
            let st2 : PyEncState := (freshIdPy.run st1).2
            let cl2 : List Int := [-Int.ofNat allPrevNow, -x, Int.ofNat allPrevNew]
            let st3 : PyEncState := ((pushClausePy cl2).run st2).2
            let cl3 : List Int := [-Int.ofNat allPrevNow, y, Int.ofNat allPrevNew]
            let st4 : PyEncState := ((pushClausePy cl3).run st3).2
            have hSt1Next : st1.nextId = st.nextId := by
              unfold st1
              simpa using (pushClausePy_run_nextId (st := st) (cl := cl1))
            have hAllPrevNewEq : allPrevNew = st1.nextId := by
              unfold allPrevNew
              simpa using (freshIdPy_run_fst (st := st1))
            have hSt2Next : st2.nextId = st1.nextId + 1 := by
              unfold st2
              simpa using (freshIdPy_run_nextId (st := st1))
            have hSt3Next : st3.nextId = st2.nextId := by
              unfold st3
              simpa using (pushClausePy_run_nextId (st := st2) (cl := cl2))
            have hSt4Next : st4.nextId = st3.nextId := by
              unfold st4
              simpa using (pushClausePy_run_nextId (st := st3) (cl := cl3))
            have hSt4Next' : st4.nextId = st.nextId + 1 := by
              calc
                st4.nextId = st3.nextId := hSt4Next
                _ = st2.nextId := hSt3Next
                _ = st1.nextId + 1 := hSt2Next
                _ = st.nextId + 1 := by simpa [hSt1Next]
            have hAllPrevLtSt1 : allPrevNow < st1.nextId := by
              simpa [hSt1Next] using hAllPrevLt
            have hxBoundSt1 : x.natAbs < st1.nextId := by
              simpa [hSt1Next] using hxBound
            have hyBoundSt1 : y.natAbs < st1.nextId := by
              simpa [hSt1Next] using hyBound
            let defVal : Prop :=
              pyAssignmentAt st1 n c aux allPrevNow ∧
                (CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt x) ↔
                  CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt y))
            let aux1 : Nat → Prop := Function.update aux st1.nextId defVal
            have hSem2 : PySemInv st2 n c aux1 := by
              unfold st2 aux1 defVal
              simpa using
                (pySemInv_freshIdPy_update_oldNextId
                  (st := st1) (n := n) (c := c) aux
                  (pyAssignmentAt st1 n c aux allPrevNow ∧
                    (CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt x) ↔
                      CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt y)))
                  hSem1)
            have hFreshDef1 : aux1 allPrevNew ↔ defVal := by
              unfold aux1 defVal
              rw [hAllPrevNewEq]
              simp [Function.update]
            have hAllPrevNewNoneSt1 : st1.idToNamed[allPrevNew]? = none := by
              rw [hAllPrevNewEq]
              exact pyStateInv_idToNamed_nextId_none (st := st1) hSem1.inv
            have hAllPrevNewSatSt1 :
                pyAssignmentAt st1 n c aux1 allPrevNew ↔ aux1 allPrevNew := by
              exact pyAssignmentAt_aux (st := st1) (n := n) (c := c) aux1 hAllPrevNewNoneSt1
            have hAllPrevNewNone : st2.idToNamed[allPrevNew]? = none := by
              unfold st2 allPrevNew
              exact pyStateInv_freshIdPy_new_none (st := st1) hSem1.inv
            have hAllPrevNewSat :
                pyAssignmentAt st2 n c aux1 allPrevNew ↔ aux1 allPrevNew := by
              exact pyAssignmentAt_aux (st := st2) (n := n) (c := c) aux1 hAllPrevNewNone
            have hAllPrevEqUpd :
                pyAssignmentAt st1 n c aux1 allPrevNow ↔
                  pyAssignmentAt st1 n c aux allPrevNow := by
              unfold aux1 defVal
              exact pyAssignmentAt_update_nextId_eq_of_lt
                (st := st1) (n := n) (c := c) aux
                (pyAssignmentAt st1 n c aux allPrevNow ∧
                  (CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt x) ↔
                    CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt y)))
                (i := allPrevNow) hAllPrevLtSt1
            have hxSatEqUpd :
                CNF.Lit.Sat (pyAssignmentAt st1 n c aux1) (litOfDimacsInt x) ↔
                  CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt x) := by
              unfold aux1 defVal
              exact pyLitSat_update_nextId_eq_of_bound
                (st := st1) (n := n) (c := c) aux
                (pyAssignmentAt st1 n c aux allPrevNow ∧
                  (CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt x) ↔
                    CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt y)))
                (i := x) hxBoundSt1
            have hySatEqUpd :
                CNF.Lit.Sat (pyAssignmentAt st1 n c aux1) (litOfDimacsInt y) ↔
                  CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt y) := by
              unfold aux1 defVal
              exact pyLitSat_update_nextId_eq_of_bound
                (st := st1) (n := n) (c := c) aux
                (pyAssignmentAt st1 n c aux allPrevNow ∧
                  (CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt x) ↔
                    CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt y)))
                (i := y) hyBoundSt1
            have hDefSt1 :
                pyAssignmentAt st1 n c aux1 allPrevNew ↔
                  (pyAssignmentAt st1 n c aux1 allPrevNow ∧
                    (CNF.Lit.Sat (pyAssignmentAt st1 n c aux1) (litOfDimacsInt x) ↔
                      CNF.Lit.Sat (pyAssignmentAt st1 n c aux1) (litOfDimacsInt y))) := by
              have hExprEq :
                  defVal ↔
                    (pyAssignmentAt st1 n c aux1 allPrevNow ∧
                      (CNF.Lit.Sat (pyAssignmentAt st1 n c aux1) (litOfDimacsInt x) ↔
                        CNF.Lit.Sat (pyAssignmentAt st1 n c aux1) (litOfDimacsInt y))) := by
                constructor
                · intro hOld
                  refine ⟨hAllPrevEqUpd.mpr hOld.1, ?_⟩
                  constructor
                  · intro hx1
                    exact hySatEqUpd.mpr ((hOld.2).1 (hxSatEqUpd.mp hx1))
                  · intro hy1
                    exact hxSatEqUpd.mpr ((hOld.2).2 (hySatEqUpd.mp hy1))
                · intro hNew
                  refine ⟨hAllPrevEqUpd.mp hNew.1, ?_⟩
                  constructor
                  · intro hxOld
                    exact hySatEqUpd.mp ((hNew.2).1 (hxSatEqUpd.mpr hxOld))
                  · intro hyOld
                    exact hxSatEqUpd.mp ((hNew.2).2 (hySatEqUpd.mpr hyOld))
              exact (hAllPrevNewSatSt1.trans hFreshDef1).trans hExprEq
            have hDef2 :
                pyAssignmentAt st2 n c aux1 allPrevNew ↔
                  (pyAssignmentAt st2 n c aux1 allPrevNow ∧
                    (CNF.Lit.Sat (pyAssignmentAt st2 n c aux1) (litOfDimacsInt x) ↔
                      CNF.Lit.Sat (pyAssignmentAt st2 n c aux1) (litOfDimacsInt y))) := by
              have hTau2 :
                  pyAssignmentAt st2 n c aux1 = pyAssignmentAt st1 n c aux1 := by
                unfold st2
                simpa using
                  (pyAssignmentAt_freshIdPy_eq_fun (st := st1) (n := n) (c := c) aux1)
              simpa [hTau2] using hDefSt1
            have hCodeImp1Old :
                pyAssignmentAt st1 n c aux allPrevNow →
                  boolSeqCode (litVal (pyAssignmentAt st1 n c aux) x ::
                    xt.map (litVal (pyAssignmentAt st1 n c aux))) ≤
                    boolSeqCode (litVal (pyAssignmentAt st1 n c aux) y ::
                      yt.map (litVal (pyAssignmentAt st1 n c aux))) := by
              have hTau1 :
                  pyAssignmentAt st1 n c aux = pyAssignmentAt st n c aux := by
                unfold st1 cl1
                simpa using
                  (pyAssignmentAt_pushClausePy_eq_fun (st := st) (n := n) (c := c) aux
                    (cl := cl1))
              intro hA
              simpa [hTau1] using hCodeImp (by simpa [hTau1] using hA)
            have hCodeImp1 :
                pyAssignmentAt st1 n c aux1 allPrevNow →
                  boolSeqCode (litVal (pyAssignmentAt st1 n c aux1) x ::
                    xt.map (litVal (pyAssignmentAt st1 n c aux1))) ≤
                    boolSeqCode (litVal (pyAssignmentAt st1 n c aux1) y ::
                      yt.map (litVal (pyAssignmentAt st1 n c aux1))) := by
              intro hA1
              have hTau1Aux1 :
                  pyAssignmentAt st1 n c aux1 = pyAssignmentAt st n c aux1 := by
                unfold st1 cl1
                simpa using
                  (pyAssignmentAt_pushClausePy_eq_fun (st := st) (n := n) (c := c) aux1
                    (cl := cl1))
              have hA1St : pyAssignmentAt st n c aux1 allPrevNow := by
                simpa [hTau1Aux1] using hA1
              have hAllPrevEqSt :
                  pyAssignmentAt st n c aux1 allPrevNow ↔
                    pyAssignmentAt st n c aux allPrevNow := by
                unfold aux1 defVal
                simpa [hSt1Next] using
                  (pyAssignmentAt_update_nextId_eq_of_lt
                    (st := st) (n := n) (c := c) aux
                    (pyAssignmentAt st1 n c aux allPrevNow ∧
                      (CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt x) ↔
                        CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt y)))
                    (i := allPrevNow) hAllPrevLt)
              have hAOld : pyAssignmentAt st n c aux allPrevNow := hAllPrevEqSt.mp hA1St
              have hOldIneq :
                  boolSeqCode (litVal (pyAssignmentAt st n c aux) x ::
                    xt.map (litVal (pyAssignmentAt st n c aux))) ≤
                    boolSeqCode (litVal (pyAssignmentAt st n c aux) y ::
                      yt.map (litVal (pyAssignmentAt st n c aux))) := hCodeImp hAOld
              have hSatEqSt :
                  ∀ i : Int, i.natAbs < st.nextId →
                    (CNF.Lit.Sat (pyAssignmentAt st n c aux1) (litOfDimacsInt i) ↔
                      CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i)) := by
                intro i hi
                unfold aux1 defVal
                simpa [hSt1Next] using
                  (pyLitSat_update_nextId_eq_of_bound
                    (st := st) (n := n) (c := c) aux
                    (pyAssignmentAt st1 n c aux allPrevNow ∧
                      (CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt x) ↔
                        CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt y)))
                    (i := i) hi)
              have hSatEqLeft :
                  ∀ i : Int, i ∈ (x :: xt) →
                    (CNF.Lit.Sat (pyAssignmentAt st1 n c aux1) (litOfDimacsInt i) ↔
                      CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i)) := by
                intro i hi
                have hiBound : i.natAbs < st.nextId := by
                  rcases List.mem_cons.1 hi with hi | hi
                  · subst hi
                    exact hxBound
                  · exact hBoundXt i hi
                have hPushEq :
                    CNF.Lit.Sat (pyAssignmentAt st1 n c aux1) (litOfDimacsInt i) ↔
                      CNF.Lit.Sat (pyAssignmentAt st n c aux1) (litOfDimacsInt i) := by
                  unfold st1 cl1
                  simpa using
                    (pyLitSat_pushClausePy_eq (st := st) (n := n) (c := c) aux1
                      (cl := cl1) (i := i))
                exact hPushEq.trans (hSatEqSt i hiBound)
              have hSatEqRight :
                  ∀ i : Int, i ∈ (y :: yt) →
                    (CNF.Lit.Sat (pyAssignmentAt st1 n c aux1) (litOfDimacsInt i) ↔
                      CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i)) := by
                intro i hi
                have hiBound : i.natAbs < st.nextId := by
                  rcases List.mem_cons.1 hi with hi | hi
                  · subst hi
                    exact hyBound
                  · exact hBoundYt i hi
                have hPushEq :
                    CNF.Lit.Sat (pyAssignmentAt st1 n c aux1) (litOfDimacsInt i) ↔
                      CNF.Lit.Sat (pyAssignmentAt st n c aux1) (litOfDimacsInt i) := by
                  unfold st1 cl1
                  simpa using
                    (pyLitSat_pushClausePy_eq (st := st) (n := n) (c := c) aux1
                      (cl := cl1) (i := i))
                exact hPushEq.trans (hSatEqSt i hiBound)
              have hLeftEq :
                  boolSeqCode ((x :: xt).map (litVal (pyAssignmentAt st1 n c aux1))) =
                    boolSeqCode ((x :: xt).map (litVal (pyAssignmentAt st n c aux))) :=
                boolSeqCode_eq_map_litVal_of_litSatEq
                  (τ := pyAssignmentAt st1 n c aux1) (τ' := pyAssignmentAt st n c aux)
                  (xs := x :: xt) hSatEqLeft
              have hRightEq :
                  boolSeqCode ((y :: yt).map (litVal (pyAssignmentAt st1 n c aux1))) =
                    boolSeqCode ((y :: yt).map (litVal (pyAssignmentAt st n c aux))) :=
                boolSeqCode_eq_map_litVal_of_litSatEq
                  (τ := pyAssignmentAt st1 n c aux1) (τ' := pyAssignmentAt st n c aux)
                  (xs := y :: yt) hSatEqRight
              have hNewList :
                  boolSeqCode ((x :: xt).map (litVal (pyAssignmentAt st1 n c aux1))) ≤
                    boolSeqCode ((y :: yt).map (litVal (pyAssignmentAt st1 n c aux1))) := by
                calc
                  boolSeqCode ((x :: xt).map (litVal (pyAssignmentAt st1 n c aux1)))
                      = boolSeqCode ((x :: xt).map (litVal (pyAssignmentAt st n c aux))) := hLeftEq
                  _ ≤ boolSeqCode ((y :: yt).map (litVal (pyAssignmentAt st n c aux))) := by
                    simpa using hOldIneq
                  _ = boolSeqCode ((y :: yt).map (litVal (pyAssignmentAt st1 n c aux1))) := by
                    symm
                    exact hRightEq
              simpa using hNewList
            have hStepSat :
                CNF.Clause.Sat (pyAssignmentAt st1 n c aux1) (cl1.map litOfDimacsInt) ∧
                  CNF.Clause.Sat (pyAssignmentAt st1 n c aux1) (cl2.map litOfDimacsInt) ∧
                  CNF.Clause.Sat (pyAssignmentAt st1 n c aux1) (cl3.map litOfDimacsInt) ∧
                  (pyAssignmentAt st1 n c aux1 allPrevNew →
                    boolSeqCode (xt.map (litVal (pyAssignmentAt st1 n c aux1))) ≤
                      boolSeqCode (yt.map (litVal (pyAssignmentAt st1 n c aux1)))) := by
              simpa [cl1, cl2, cl3, allPrevNew] using
                (pyClauseSat_lexComparator_step_of_boolSeqCode_le
                  (τ := pyAssignmentAt st1 n c aux1)
                  (allPrev := allPrevNow) (allPrevNew := allPrevNew)
                  (x := x) (y := y) (xs := xt) (ys := yt)
                  hAllPrevPos hx0 hLenTail hDefSt1 hCodeImp1)
            have hTau2 :
                pyAssignmentAt st2 n c aux1 = pyAssignmentAt st1 n c aux1 := by
              unfold st2
              simpa using
                (pyAssignmentAt_freshIdPy_eq_fun (st := st1) (n := n) (c := c) aux1)
            have hClause2Sat :
                CNF.Clause.Sat (pyAssignmentAt st2 n c aux1) (cl2.map litOfDimacsInt) := by
              simpa [hTau2] using hStepSat.2.1
            have hAllPrevLtSt2 : allPrevNow < st2.nextId := by
              have hlt : allPrevNow < st.nextId + 1 := Nat.lt_succ_of_lt hAllPrevLt
              simpa [hSt2Next, hSt1Next] using hlt
            have hxBoundSt2 : x.natAbs < st2.nextId := by
              have hlt : x.natAbs < st.nextId + 1 := Nat.lt_succ_of_lt hxBound
              simpa [hSt2Next, hSt1Next] using hlt
            have hAllPrevNewLtSt2 : allPrevNew < st2.nextId := by
              rw [hAllPrevNewEq, hSt2Next]
              exact Nat.lt_succ_self _
            have hClause2Bound :
                ∀ i : Int, i ∈ cl2 → i.natAbs < st2.nextId := by
              intro i hi
              rcases List.mem_cons.1 hi with hi | hi
              · have hiEq : i = -Int.ofNat allPrevNow := hi
                subst hiEq
                simpa using hAllPrevLtSt2
              · rcases List.mem_cons.1 hi with hi | hi
                · have hiEq : i = -x := hi
                  subst hiEq
                  simpa using hxBoundSt2
                · have hiEq : i = Int.ofNat allPrevNew := by simpa using hi
                  subst hiEq
                  simpa using hAllPrevNewLtSt2
            have hSem3 : PySemInv st3 n c aux1 :=
              pySemInv_pushClausePy (st := st2) (n := n) (c := c) aux1 (cl := cl2) hSem2
                (by
                  rcases hClause2Sat with ⟨l, hlMem, hlSat⟩
                  rcases List.mem_map.mp hlMem with ⟨i, hiMem, hiEq⟩
                  subst hiEq
                  exact ⟨i, hiMem, hlSat⟩)
                hClause2Bound
            have hTau3 :
                pyAssignmentAt st3 n c aux1 = pyAssignmentAt st1 n c aux1 := by
              unfold st3
              calc
                pyAssignmentAt ((pushClausePy cl2).run st2).2 n c aux1
                    = pyAssignmentAt st2 n c aux1 := by
                      simpa using
                        (pyAssignmentAt_pushClausePy_eq_fun
                          (st := st2) (n := n) (c := c) aux1 (cl := cl2))
                _ = pyAssignmentAt st1 n c aux1 := hTau2
            have hClause3Sat :
                CNF.Clause.Sat (pyAssignmentAt st3 n c aux1) (cl3.map litOfDimacsInt) := by
              simpa [hTau3] using hStepSat.2.2.1
            have hAllPrevLtSt3 : allPrevNow < st3.nextId := by
              simpa [hSt3Next] using hAllPrevLtSt2
            have hyBoundSt3 : y.natAbs < st3.nextId := by
              have hyBoundSt2 : y.natAbs < st2.nextId := by
                have hlt : y.natAbs < st.nextId + 1 := Nat.lt_succ_of_lt hyBound
                simpa [hSt2Next, hSt1Next] using hlt
              simpa [hSt3Next] using hyBoundSt2
            have hAllPrevNewLtSt3 : allPrevNew < st3.nextId := by
              simpa [hSt3Next] using hAllPrevNewLtSt2
            have hClause3Bound :
                ∀ i : Int, i ∈ cl3 → i.natAbs < st3.nextId := by
              intro i hi
              rcases List.mem_cons.1 hi with hi | hi
              · have hiEq : i = -Int.ofNat allPrevNow := hi
                subst hiEq
                simpa using hAllPrevLtSt3
              · rcases List.mem_cons.1 hi with hi | hi
                · have hiEq : i = y := hi
                  subst hiEq
                  exact hyBoundSt3
                · have hiEq : i = Int.ofNat allPrevNew := by simpa using hi
                  subst hiEq
                  simpa using hAllPrevNewLtSt3
            have hSem4 : PySemInv st4 n c aux1 :=
              pySemInv_pushClausePy (st := st3) (n := n) (c := c) aux1 (cl := cl3) hSem3
                (by
                  rcases hClause3Sat with ⟨l, hlMem, hlSat⟩
                  rcases List.mem_map.mp hlMem with ⟨i, hiMem, hiEq⟩
                  subst hiEq
                  exact ⟨i, hiMem, hlSat⟩)
                hClause3Bound
            have hTau4 :
                pyAssignmentAt st4 n c aux1 = pyAssignmentAt st1 n c aux1 := by
              unfold st4
              calc
                pyAssignmentAt ((pushClausePy cl3).run st3).2 n c aux1
                    = pyAssignmentAt st3 n c aux1 := by
                      simpa using
                        (pyAssignmentAt_pushClausePy_eq_fun
                          (st := st3) (n := n) (c := c) aux1 (cl := cl3))
                _ = pyAssignmentAt st1 n c aux1 := hTau3
            have hCodeTail :
                pyAssignmentAt st4 n c aux1 allPrevNew →
                  boolSeqCode (xt.map (litVal (pyAssignmentAt st4 n c aux1))) ≤
                    boolSeqCode (yt.map (litVal (pyAssignmentAt st4 n c aux1))) := by
              intro hA4
              have hA1 : pyAssignmentAt st1 n c aux1 allPrevNew := by
                simpa [hTau4] using hA4
              have hTail1 := hStepSat.2.2.2 hA1
              simpa [hTau4] using hTail1
            have hAllPrevNewPos : 0 < allPrevNew := by
              rw [hAllPrevNewEq, hSt1Next]
              exact hSem.nextPos
            have hAllPrevNewLtSt4 : allPrevNew < st4.nextId := by
              rw [hAllPrevNewEq, hSt1Next, hSt4Next']
              exact Nat.lt_succ_self _
            have hBoundXtSt4 : ∀ i : Int, i ∈ xt → i.natAbs < st4.nextId := by
              intro i hi
              have hiOld : i.natAbs < st.nextId := hBoundXt i hi
              have hiSucc : i.natAbs < st.nextId + 1 := Nat.lt_succ_of_lt hiOld
              simpa [hSt4Next'] using hiSucc
            have hBoundYtSt4 : ∀ i : Int, i ∈ yt → i.natAbs < st4.nextId := by
              intro i hi
              have hiOld : i.natAbs < st.nextId := hBoundYt i hi
              have hiSucc : i.natAbs < st.nextId + 1 := Nat.lt_succ_of_lt hiOld
              simpa [hSt4Next'] using hiSucc
            cases maxComparisons with
            | none =>
                rcases
                  ih (aux := aux1) (st := st4) (ys := yt) (allPrevNow := allPrevNew) (rcnt := rcnt + 1)
                    hSem4 hAllPrevNewPos hAllPrevNewLtSt4 hLenTail
                    hBoundXtSt4 hBoundYtSt4 hNoZeroXt hNoZeroYt hCodeTail with ⟨aux', hRec⟩
                exact ⟨aux', by
                  simpa [lexSmallerEqLoopPy, hxy, cl1, st1, allPrevNew, st2, cl2, st3, cl3, st4,
                    Bind.bind, pure] using hRec⟩
            | some m =>
                by_cases hcut : rcnt + 1 > m
                · exact ⟨aux1, by
                    simpa [lexSmallerEqLoopPy, hxy, hcut, cl1, st1, allPrevNew, st2, cl2, st3, cl3, st4,
                      Bind.bind, pure] using hSem4⟩
                · rcases
                  ih (aux := aux1) (st := st4) (ys := yt) (allPrevNow := allPrevNew) (rcnt := rcnt + 1)
                    hSem4 hAllPrevNewPos hAllPrevNewLtSt4 hLenTail
                    hBoundXtSt4 hBoundYtSt4 hNoZeroXt hNoZeroYt hCodeTail with ⟨aux', hRec⟩
                  exact ⟨aux', by
                    simpa [lexSmallerEqLoopPy, hxy, hcut, cl1, st1, allPrevNew, st2, cl2, st3, cl3, st4,
                      Bind.bind, pure] using hRec⟩

private lemma pySemInv_edgeSeqPy {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {es : List (Nat × Nat)}
    (hSem : PySemInv st n c aux) :
    PySemInv ((edgeSeqPy n es).run st).2 n c aux := by
  induction es generalizing st with
  | nil =>
      simpa [edgeSeqPy] using hSem
  | cons e es ih =>
      rcases e with ⟨u, v⟩
      simp [edgeSeqPy]
      exact ih (st := ((rLitPy n u v).run st).2)
        (pySemInv_rLitPy (st := st) (n := n) (c := c) aux (u := u) (v := v) hSem)

private lemma pyState_nextId_le_edgeSeqPy {st : PyEncState} {n : Nat}
    {es : List (Nat × Nat)} :
    st.nextId ≤ ((edgeSeqPy n es).run st).2.nextId := by
  induction es generalizing st with
  | nil =>
      change st.nextId ≤ st.nextId
      exact le_rfl
  | cons e es ih =>
      rcases e with ⟨u, v⟩
      rcases hRun : (rLitPy n u v).run st with ⟨lit, st1⟩
      have h1 : st.nextId ≤ st1.nextId := by
        simpa [hRun] using
          (pyState_nextId_le_rLitPy (st := st) (n := n) (u := u) (v := v))
      have h2 :
          st1.nextId ≤ ((edgeSeqPy n es).run st1).2.nextId :=
        ih (st := st1)
      simpa [edgeSeqPy, hRun] using le_trans h1 h2

private lemma edgeSeqPy_run_length {st : PyEncState} {n : Nat}
    {es : List (Nat × Nat)} :
    ((edgeSeqPy n es).run st).1.length = es.length := by
  induction es generalizing st with
  | nil =>
      rfl
  | cons e es ih =>
      rcases hRun : (rLitPy n e.1 e.2).run st with ⟨lit, st1⟩
      rcases hTailRun : ((edgeSeqPy n es).run st1) with ⟨tailLits, st2⟩
      have hTailLen : tailLits.length = es.length := by
        simpa [hTailRun] using ih (st := st1)
      have hTailRun' :
          (List.mapM (fun x => rLitPy n x.1 x.2) es).run st1 = (tailLits, st2) := by
        simpa [edgeSeqPy] using hTailRun
      unfold edgeSeqPy
      rw [List.mapM_cons]
      change
        (((rLitPy n e.1 e.2 >>= fun head =>
            List.mapM (fun x => rLitPy n x.1 x.2) es >>= fun tail =>
              pure (head :: tail)).run st).1.length =
          es.length + 1)
      simp [hRun]
      change
        (((fun p_1 => (lit :: p_1.1, p_1.2)) <$>
            (List.mapM (fun x => rLitPy n x.1 x.2) es).run st1).1.length =
          es.length + 1)
      rw [hTailRun']
      change (lit :: tailLits).length = es.length + 1
      simpa [hTailLen]

private lemma edgeSeqPy_run_bound_noZero
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {es : List (Nat × Nat)}
    (hSem : PySemInv st n c aux) :
    let run := (edgeSeqPy n es).run st
    (∀ i : Int, i ∈ run.1 → i.natAbs < run.2.nextId) ∧
      (∀ i : Int, i ∈ run.1 → i ≠ 0) := by
  induction es generalizing st with
  | nil =>
      change (∀ i : Int, i ∈ ([] : List Int) → i.natAbs < st.nextId) ∧
        (∀ i : Int, i ∈ ([] : List Int) → i ≠ 0)
      simp
  | cons e es ih =>
      rcases e with ⟨u, v⟩
      rcases hRun : (rLitPy n u v).run st with ⟨lit, st1⟩
      have hSem1 : PySemInv st1 n c aux :=
        by simpa [hRun] using
          (pySemInv_rLitPy (st := st) (n := n) (c := c) aux (u := u) (v := v) hSem)
      have hNamed :
          st1.idToNamed[lit.natAbs]? =
            some
              (if vLt n (orderedCodePair n u v).1 (antipodeCode n (orderedCodePair n u v).2) = true
               then .r (orderedCodePair n (orderedCodePair n u v).1
                   (orderedCodePair n u v).2).1
                   (orderedCodePair n (orderedCodePair n u v).1
                     (orderedCodePair n u v).2).2
               else .r (orderedCodePair n (antipodeCode n (orderedCodePair n u v).1)
                   (antipodeCode n (orderedCodePair n u v).2)).1
                   (orderedCodePair n (antipodeCode n (orderedCodePair n u v).1)
                     (antipodeCode n (orderedCodePair n u v).2)).2) := by
        simpa [hRun] using
          (pyStateInv_rLitPy (st := st) (n := n) (u := u) (v := v) hSem.inv)
      have hHeadLt : lit.natAbs < st1.nextId := hSem1.inv.1 hNamed
      have hHeadNe0 : lit ≠ 0 := by
        simpa [hRun] using
          (rLitPy_ne_zero (st := st) (n := n) (u := u) (v := v)
            hSem.inv hSem.noZero hSem.nextPos)
      have hTail := ih (st := st1) hSem1
      have hTailBound :
          ∀ i : Int, i ∈ ((edgeSeqPy n es).run st1).1 →
            i.natAbs < ((edgeSeqPy n es).run st1).2.nextId := by
        simpa using hTail.1
      have hTailNoZero :
          ∀ i : Int, i ∈ ((edgeSeqPy n es).run st1).1 → i ≠ 0 := by
        simpa using hTail.2
      have hSt1Le :
          st1.nextId ≤ ((edgeSeqPy n es).run st1).2.nextId :=
        pyState_nextId_le_edgeSeqPy (st := st1) (n := n) (es := es)
      simp [edgeSeqPy, hRun]
      constructor
      · intro i hi
        rcases List.mem_cons.1 hi with hi | hi
        · subst hi
          exact lt_of_lt_of_le hHeadLt hSt1Le
        · exact hTailBound i hi
      · intro i hi
        rcases List.mem_cons.1 hi with hi | hi
        · subst hi
          exact hHeadNe0
        · exact hTailNoZero i hi

private lemma pyLitSat_edgeSeqPy_eq_of_bound
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {es : List (Nat × Nat)} {i : Int}
    (hi : i.natAbs < st.nextId) :
    CNF.Lit.Sat (pyAssignmentAt ((edgeSeqPy n es).run st).2 n c aux) (litOfDimacsInt i) ↔
      CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i) := by
  induction es generalizing st with
  | nil =>
      change CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i) ↔
        CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i)
      rfl
  | cons e es ih =>
      rcases e with ⟨u, v⟩
      rcases hRun : (rLitPy n u v).run st with ⟨lit, st1⟩
      have hLe : st.nextId ≤ st1.nextId := by
        simpa [hRun] using
          (pyState_nextId_le_rLitPy (st := st) (n := n) (u := u) (v := v))
      have hi1 : i.natAbs < st1.nextId := lt_of_lt_of_le hi hLe
      have hTail :
          CNF.Lit.Sat (pyAssignmentAt ((edgeSeqPy n es).run st1).2 n c aux) (litOfDimacsInt i) ↔
            CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt i) :=
        ih (st := st1) hi1
      have hHead :
          CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt i) ↔
            CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i) := by
        simpa [hRun] using
          (pyLitSat_rLitPy_eq_of_bound
            (st := st) (n := n) (c := c) aux (u := u) (v := v) (i := i) hi)
      simpa [edgeSeqPy, hRun] using hTail.trans hHead

private lemma litVal_eq_of_sat_iff_true
    {τ : CNF.Assignment Nat} {i : Int} {b : Bool}
    (h : CNF.Lit.Sat τ (litOfDimacsInt i) ↔ b = true) :
    litVal τ i = b := by
  cases hb : b with
  | false =>
      have hNotSat : ¬ CNF.Lit.Sat τ (litOfDimacsInt i) := by
        intro hSat
        have : b = true := h.mp hSat
        simpa [hb] using this
      simp [litVal, hb, hNotSat]
  | true =>
      have hSat : CNF.Lit.Sat τ (litOfDimacsInt i) := h.mpr (by simp [hb])
      simp [litVal, hb, hSat]

private lemma mem_originalSignedEdgesPy_allVertexCodes
    {n u v : Nat}
    (hmem : (u, v) ∈ originalSignedEdgesPy n (allVertexCodes n)) :
    u ∈ allVertexCodes n ∧
      v ∈ allVertexCodes n ∧
      Adj (natToVertex n u) (natToVertex n v) := by
  unfold originalSignedEdgesPy at hmem
  rcases List.mem_flatMap.mp hmem with ⟨u0, hu0, hmem0⟩
  rcases List.mem_filterMap.mp hmem0 with ⟨v0, hv0, hvSome⟩
  cases hlt : vLt n u0 v0 with
  | false =>
      simp [hlt] at hvSome
  | true =>
      simp [hlt] at hvSome
      rcases hvSome with ⟨huEq, hvEq⟩
      subst huEq
      subst hvEq
      refine ⟨hu0, ?_, ?_⟩
      · exact neighborsCode_mem_allVertexCodes (n := n) (u := u0) (v := v0) hu0 hv0
      · exact neighborsCode_adj (n := n) (u := u0) (v := v0) hv0

private lemma edgeSeqPy_run_litVals_eq_colors
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop) {es : List (Nat × Nat)}
    (hAnti : IsAntipodalColoring c)
    (hSem : PySemInv st n c aux)
    (hEdge :
      ∀ e : Nat × Nat, e ∈ es →
        e.1 ∈ allVertexCodes n ∧
          e.2 ∈ allVertexCodes n ∧
          Adj (natToVertex n e.1) (natToVertex n e.2)) :
    let run := (edgeSeqPy n es).run st
    run.1.map (litVal (pyAssignmentAt run.2 n c aux)) =
      es.map (fun e => c (edgeOf (natToVertex n e.1) (natToVertex n e.2))) := by
  induction es generalizing st with
  | nil =>
      rfl
  | cons e es ih =>
      rcases e with ⟨u, v⟩
      rcases hRun : (rLitPy n u v).run st with ⟨lit, st1⟩
      rcases hTailRun : (edgeSeqPy n es).run st1 with ⟨tailLits, st2⟩
      have hSem1 : PySemInv st1 n c aux := by
        simpa [hRun] using
          (pySemInv_rLitPy (st := st) (n := n) (c := c) aux (u := u) (v := v) hSem)
      have hEdgeUV :
          u ∈ allVertexCodes n ∧
            v ∈ allVertexCodes n ∧
            Adj (natToVertex n u) (natToVertex n v) := by
        exact hEdge (u, v) (by simp)
      have hu : u ∈ allVertexCodes n := hEdgeUV.1
      have hv : v ∈ allVertexCodes n := hEdgeUV.2.1
      have hAdj : Adj (natToVertex n u) (natToVertex n v) := hEdgeUV.2.2
      have hSatHeadSt1 :
          CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt lit) ↔
            c (edgeOf (natToVertex n u) (natToVertex n v)) = true := by
        have hSatHead :=
          pyLitSat_rLitPy_iff_red_at
            (st := st) (n := n) (c := c) aux
            hSem.inv hAnti hSem.noZero hSem.nextPos
            (u := u) (v := v) hu hv hAdj
        simpa [hRun, pyVarSemantics] using hSatHead
      have hNamed :
          st1.idToNamed[lit.natAbs]? =
            some
              (if vLt n (orderedCodePair n u v).1 (antipodeCode n (orderedCodePair n u v).2) = true
               then .r (orderedCodePair n (orderedCodePair n u v).1
                   (orderedCodePair n u v).2).1
                   (orderedCodePair n (orderedCodePair n u v).1
                     (orderedCodePair n u v).2).2
               else .r (orderedCodePair n (antipodeCode n (orderedCodePair n u v).1)
                   (antipodeCode n (orderedCodePair n u v).2)).1
                   (orderedCodePair n (antipodeCode n (orderedCodePair n u v).1)
                     (antipodeCode n (orderedCodePair n u v).2)).2) := by
        simpa [hRun] using
          (pyStateInv_rLitPy (st := st) (n := n) (u := u) (v := v) hSem.inv)
      have hLitBound : lit.natAbs < st1.nextId := hSem1.inv.1 hNamed
      have hSatHeadSt2 :
          CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt lit) ↔
            c (edgeOf (natToVertex n u) (natToVertex n v)) = true := by
        have hSatPres :
            CNF.Lit.Sat (pyAssignmentAt st2 n c aux) (litOfDimacsInt lit) ↔
              CNF.Lit.Sat (pyAssignmentAt st1 n c aux) (litOfDimacsInt lit) := by
          have hTail :=
            pyLitSat_edgeSeqPy_eq_of_bound
              (st := st1) (n := n) (c := c) aux (es := es) (i := lit) hLitBound
          simpa [hTailRun] using hTail
        exact hSatPres.trans hSatHeadSt1
      have hHeadVal :
          litVal (pyAssignmentAt st2 n c aux) lit =
            c (edgeOf (natToVertex n u) (natToVertex n v)) := by
        refine (litVal_eq_of_sat_iff_true (τ := pyAssignmentAt st2 n c aux) (i := lit) ?_)
        exact hSatHeadSt2
      have hEdgeTail :
          ∀ e' : Nat × Nat, e' ∈ es →
            e'.1 ∈ allVertexCodes n ∧
              e'.2 ∈ allVertexCodes n ∧
              Adj (natToVertex n e'.1) (natToVertex n e'.2) := by
        intro e' he'
        exact hEdge e' (by simp [he'])
      have hTailVals :
          tailLits.map (litVal (pyAssignmentAt st2 n c aux)) =
            es.map (fun e' => c (edgeOf (natToVertex n e'.1) (natToVertex n e'.2))) := by
        simpa [hTailRun] using
          (ih (st := st1) hSem1 hEdgeTail)
      have hRunSeq :
          (edgeSeqPy n ((u, v) :: es)).run st = (lit :: tailLits, st2) := by
        have hRun' : rLitPy n u v st = (lit, st1) := by
          simpa [StateT.run] using hRun
        have hTailRun' :
            (List.mapM (fun x : Nat × Nat => rLitPy n x.1 x.2) es) st1 =
              (tailLits, st2) := by
          simpa [edgeSeqPy, StateT.run] using hTailRun
        apply Prod.ext <;>
          simp [edgeSeqPy, StateT.run, StateT.bind, StateT.pure, Bind.bind, pure, hRun', hTailRun']
      have hMapCons :
          (lit :: tailLits).map (litVal (pyAssignmentAt st2 n c aux)) =
            c (edgeOf (natToVertex n u) (natToVertex n v)) ::
              es.map (fun e' => c (edgeOf (natToVertex n e'.1) (natToVertex n e'.2))) := by
        simpa [hHeadVal, hTailVals]
      simpa [hRunSeq] using hMapCons

private lemma foldl_boolAcc_eq
    (bs : List Bool) (acc : Nat) :
    List.foldl (fun a b => 2 * a + Bool.toNat b) acc bs =
      2 ^ bs.length * acc + boolSeqCode bs := by
  induction bs generalizing acc with
  | nil =>
      simp [boolSeqCode]
  | cons b bs ih =>
      calc
        List.foldl (fun a b => 2 * a + Bool.toNat b) acc (b :: bs)
            = List.foldl (fun a b => 2 * a + Bool.toNat b) (2 * acc + Bool.toNat b) bs := by
                simp
        _ = 2 ^ bs.length * (2 * acc + Bool.toNat b) + boolSeqCode bs := ih (2 * acc + Bool.toNat b)
        _ = 2 ^ (bs.length + 1) * acc + boolSeqCode (b :: bs) := by
              simp [boolSeqCode, Nat.pow_succ]
              ring

private lemma foldl_boolSeqCode_eq (bs : List Bool) :
    List.foldl (fun a b => 2 * a + Bool.toNat b) 0 bs = boolSeqCode bs := by
  simpa [Nat.zero_mul, Nat.zero_add] using
    (foldl_boolAcc_eq bs 0)

private lemma edgeSeqCode_eq_boolSeqCode_edgeSeqPy_original
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop)
    (hAnti : IsAntipodalColoring c)
    (hSem : PySemInv st n c aux) :
    let es1 := originalSignedEdgesPy n (allVertexCodes n)
    let run1 := (edgeSeqPy n es1).run st
    boolSeqCode (run1.1.map (litVal (pyAssignmentAt run1.2 n c aux))) = edgeSeqCode n c := by
  let es1 := originalSignedEdgesPy n (allVertexCodes n)
  let run1 : List Int × PyEncState := (edgeSeqPy n es1).run st
  have hEdge :
      ∀ e : Nat × Nat, e ∈ es1 →
        e.1 ∈ allVertexCodes n ∧
          e.2 ∈ allVertexCodes n ∧
          Adj (natToVertex n e.1) (natToVertex n e.2) := by
    intro e he
    rcases e with ⟨u, v⟩
    simpa [es1] using
      (mem_originalSignedEdgesPy_allVertexCodes (n := n) (u := u) (v := v) he)
  have hVals :
      run1.1.map (litVal (pyAssignmentAt run1.2 n c aux)) =
        es1.map (fun e => c (edgeOf (natToVertex n e.1) (natToVertex n e.2))) := by
    unfold run1
    simpa [es1] using
      (edgeSeqPy_run_litVals_eq_colors (st := st) (n := n) (c := c) aux (es := es1) hAnti hSem hEdge)
  calc
    boolSeqCode (run1.1.map (litVal (pyAssignmentAt run1.2 n c aux)))
        = boolSeqCode (es1.map (fun e => c (edgeOf (natToVertex n e.1) (natToVertex n e.2)))) := by
            simpa [hVals]
    _ = edgeSeqCode n c := by
          simp [edgeSeqCode, es1, foldl_boolSeqCode_eq]

private lemma pySemInv_lexSmallerEqPy
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop)
    {maxComparisons : Option Nat} {seq1 seq2 : List Int}
    (hSem : PySemInv st n c aux)
    (hLen : seq1.length = seq2.length)
    (hBound1 : ∀ i : Int, i ∈ seq1 → i.natAbs < st.nextId)
    (hBound2 : ∀ i : Int, i ∈ seq2 → i.natAbs < st.nextId)
    (hNoZero1 : ∀ i : Int, i ∈ seq1 → i ≠ 0)
    (hNoZero2 : ∀ i : Int, i ∈ seq2 → i ≠ 0)
    (hCode :
      boolSeqCode (seq1.map (litVal (pyAssignmentAt st n c aux))) ≤
        boolSeqCode (seq2.map (litVal (pyAssignmentAt st n c aux)))) :
    ∃ aux' : Nat → Prop,
      PySemInv ((lexSmallerEqPy maxComparisons seq1 seq2).run st).2 n c aux' := by
  let allPrev : Nat := (freshIdPy.run st).1
  let stFresh : PyEncState := (freshIdPy.run st).2
  let stPush : PyEncState := ((pushClausePy [Int.ofNat allPrev]).run stFresh).2
  let aux1 : Nat → Prop := Function.update aux st.nextId True
  have hAllPrevEq : allPrev = st.nextId := by
    unfold allPrev
    simpa using (freshIdPy_run_fst (st := st))
  have hStFreshNext : stFresh.nextId = st.nextId + 1 := by
    unfold stFresh
    simpa using (freshIdPy_run_nextId (st := st))
  have hStPushNext : stPush.nextId = stFresh.nextId := by
    unfold stPush
    simpa using (pushClausePy_run_nextId (st := stFresh) (cl := [Int.ofNat allPrev]))
  have hStPushNext' : stPush.nextId = st.nextId + 1 := by
    calc
      stPush.nextId = stFresh.nextId := hStPushNext
      _ = st.nextId + 1 := hStFreshNext
  have hSemFresh : PySemInv stFresh n c aux1 := by
    unfold stFresh aux1
    simpa using
      (pySemInv_freshIdPy_update_oldNextId
        (st := st) (n := n) (c := c) aux True hSem)
  have hAllPrevNone : stFresh.idToNamed[allPrev]? = none := by
    show (freshIdPy.run st).2.idToNamed[(freshIdPy.run st).1]? = none
    exact pyStateInv_freshIdPy_new_none (st := st) hSem.inv
  have hAllPrevSat : pyAssignmentAt stFresh n c aux1 allPrev ↔ aux1 allPrev := by
    exact pyAssignmentAt_aux (st := stFresh) (n := n) (c := c) aux1 hAllPrevNone
  have hAllPrevTrue : pyAssignmentAt stFresh n c aux1 allPrev := by
    have hAuxAllPrev : aux1 allPrev := by
      unfold aux1
      rw [hAllPrevEq]
      simp [Function.update]
    exact hAllPrevSat.mpr hAuxAllPrev
  have hUnitSat :
      ∃ i : Int, i ∈ [Int.ofNat allPrev] ∧
        CNF.Lit.Sat (pyAssignmentAt stFresh n c aux1) (litOfDimacsInt i) := by
    have hClauseSat :
        CNF.Clause.Sat
          (pyAssignmentAt stFresh n c aux1)
          ([Int.ofNat allPrev].map litOfDimacsInt) :=
      pyClauseSat_lexComparator_unit
        (τ := pyAssignmentAt stFresh n c aux1) (allPrev := allPrev) hAllPrevTrue
    rcases hClauseSat with ⟨l, hlMem, hlSat⟩
    rcases List.mem_map.mp hlMem with ⟨i, hiMem, hiEq⟩
    subst hiEq
    exact ⟨i, hiMem, hlSat⟩
  have hAllPrevLtFresh : allPrev < stFresh.nextId := by
    rw [hAllPrevEq, hStFreshNext]
    exact Nat.lt_succ_self _
  have hUnitBound :
      ∀ i : Int, i ∈ [Int.ofNat allPrev] → i.natAbs < stFresh.nextId := by
    intro i hi
    have hiEq : i = Int.ofNat allPrev := by simpa using hi
    subst hiEq
    simpa using hAllPrevLtFresh
  have hSemPush : PySemInv stPush n c aux1 :=
    pySemInv_pushClausePy (st := stFresh) (n := n) (c := c) aux1
      (cl := [Int.ofNat allPrev]) hSemFresh hUnitSat hUnitBound
  have hTauPush :
      pyAssignmentAt stPush n c aux1 = pyAssignmentAt stFresh n c aux1 := by
    unfold stPush
    simpa using
      (pyAssignmentAt_pushClausePy_eq_fun (st := stFresh) (n := n) (c := c) aux1
        (cl := [Int.ofNat allPrev]))
  have hTauFresh :
      pyAssignmentAt stFresh n c aux1 = pyAssignmentAt st n c aux1 := by
    unfold stFresh
    simpa using (pyAssignmentAt_freshIdPy_eq_fun (st := st) (n := n) (c := c) aux1)
  have hTau :
      pyAssignmentAt stPush n c aux1 = pyAssignmentAt st n c aux1 := hTauPush.trans hTauFresh
  have hAllPrevPos : 0 < allPrev := by
    rw [hAllPrevEq]
    exact hSem.nextPos
  have hAllPrevLtPush : allPrev < stPush.nextId := by
    rw [hAllPrevEq, hStPushNext']
    exact Nat.lt_succ_self _
  have hBound1Push : ∀ i : Int, i ∈ seq1 → i.natAbs < stPush.nextId := by
    intro i hi
    have hiOld : i.natAbs < st.nextId := hBound1 i hi
    have hiSucc : i.natAbs < st.nextId + 1 := Nat.lt_succ_of_lt hiOld
    simpa [hStPushNext'] using hiSucc
  have hBound2Push : ∀ i : Int, i ∈ seq2 → i.natAbs < stPush.nextId := by
    intro i hi
    have hiOld : i.natAbs < st.nextId := hBound2 i hi
    have hiSucc : i.natAbs < st.nextId + 1 := Nat.lt_succ_of_lt hiOld
    simpa [hStPushNext'] using hiSucc
  have hSatEqSt :
      ∀ i : Int, i.natAbs < st.nextId →
        (CNF.Lit.Sat (pyAssignmentAt st n c aux1) (litOfDimacsInt i) ↔
          CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i)) := by
    intro i hi
    unfold aux1
    simpa using
      (pyLitSat_update_nextId_eq_of_bound
        (st := st) (n := n) (c := c) aux True (i := i) hi)
  have hSatEqPush :
      ∀ i : Int, i.natAbs < st.nextId →
        (CNF.Lit.Sat (pyAssignmentAt stPush n c aux1) (litOfDimacsInt i) ↔
          CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i)) := by
    intro i hi
    exact (by simpa [hTau] using (hSatEqSt i hi))
  have hSatEqSeq1 :
      ∀ i : Int, i ∈ seq1 →
        (CNF.Lit.Sat (pyAssignmentAt stPush n c aux1) (litOfDimacsInt i) ↔
          CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i)) := by
    intro i hi
    exact hSatEqPush i (hBound1 i hi)
  have hSatEqSeq2 :
      ∀ i : Int, i ∈ seq2 →
        (CNF.Lit.Sat (pyAssignmentAt stPush n c aux1) (litOfDimacsInt i) ↔
          CNF.Lit.Sat (pyAssignmentAt st n c aux) (litOfDimacsInt i)) := by
    intro i hi
    exact hSatEqPush i (hBound2 i hi)
  have hCodeEq1 :
      boolSeqCode (seq1.map (litVal (pyAssignmentAt stPush n c aux1))) =
        boolSeqCode (seq1.map (litVal (pyAssignmentAt st n c aux))) :=
    boolSeqCode_eq_map_litVal_of_litSatEq
      (τ := pyAssignmentAt stPush n c aux1) (τ' := pyAssignmentAt st n c aux)
      (xs := seq1) hSatEqSeq1
  have hCodeEq2 :
      boolSeqCode (seq2.map (litVal (pyAssignmentAt stPush n c aux1))) =
        boolSeqCode (seq2.map (litVal (pyAssignmentAt st n c aux))) :=
    boolSeqCode_eq_map_litVal_of_litSatEq
      (τ := pyAssignmentAt stPush n c aux1) (τ' := pyAssignmentAt st n c aux)
      (xs := seq2) hSatEqSeq2
  have hCodePush :
      pyAssignmentAt stPush n c aux1 allPrev →
        boolSeqCode (seq1.map (litVal (pyAssignmentAt stPush n c aux1))) ≤
          boolSeqCode (seq2.map (litVal (pyAssignmentAt stPush n c aux1))) := by
    intro _hA
    calc
      boolSeqCode (seq1.map (litVal (pyAssignmentAt stPush n c aux1)))
          = boolSeqCode (seq1.map (litVal (pyAssignmentAt st n c aux))) := hCodeEq1
      _ ≤ boolSeqCode (seq2.map (litVal (pyAssignmentAt st n c aux))) := hCode
      _ = boolSeqCode (seq2.map (litVal (pyAssignmentAt stPush n c aux1))) := by
          symm
          exact hCodeEq2
  rcases
    pySemInv_lexSmallerEqLoopPy
      (st := stPush) (n := n) (c := c) aux1
      (maxComparisons := maxComparisons) (xs := seq1) (ys := seq2)
      (allPrevNow := allPrev) (rcnt := 0)
      hSemPush hAllPrevPos hAllPrevLtPush hLen
      hBound1Push hBound2Push hNoZero1 hNoZero2 hCodePush with ⟨aux2, hLoop⟩
  unfold lexSmallerEqPy
  exact ⟨aux2, by
    simpa [allPrev, stFresh, stPush, Bind.bind, pure] using hLoop⟩

private lemma pySemInv_forIn_mem_exists {α β : Type} {n : Nat} {c : EdgeColoring n}
    (xs : List α) (init : β)
    (f : α → β → PyEncM (ForInStep β))
    (hStep : ∀ (a : α), a ∈ xs →
      ∀ (b : β) (st : PyEncState) (aux : Nat → Prop),
        PySemInv st n c aux →
          ∃ aux' : Nat → Prop, PySemInv ((f a b).run st).2 n c aux') :
    ∀ (st : PyEncState) (aux : Nat → Prop),
      PySemInv st n c aux →
        ∃ aux' : Nat → Prop, PySemInv ((forIn xs init f).run st).2 n c aux' := by
  induction xs generalizing init with
  | nil =>
      intro st aux hSem
      exact ⟨aux, by simpa using hSem⟩
  | cons a xs ih =>
      intro st aux hSem
      rcases hRun : (f a init).run st with ⟨s, st1⟩
      have hA :
          ∃ aux1 : Nat → Prop, PySemInv st1 n c aux1 := by
        rcases hStep a (by simp) init st aux hSem with ⟨aux1, hA⟩
        exact ⟨aux1, by simpa [hRun] using hA⟩
      rcases hA with ⟨aux1, hA1⟩
      cases s with
      | done b =>
          exact ⟨aux1, by simpa [List.forIn_cons, hRun] using hA1⟩
      | yield b =>
          have hStepTail :
              ∀ (a' : α), a' ∈ xs →
              ∀ (b' : β) (st' : PyEncState) (aux' : Nat → Prop),
                PySemInv st' n c aux' →
                  ∃ aux'' : Nat → Prop, PySemInv ((f a' b').run st').2 n c aux'' := by
            intro a' ha' b' st' aux' hSem'
            exact hStep a' (by simp [ha']) b' st' aux' hSem'
          rcases ih (init := b) hStepTail st1 aux1 hA1 with ⟨aux2, hTail⟩
          exact ⟨aux2, by simpa [List.forIn_cons, hRun] using hTail⟩

private lemma pySemInv_edgeSeqLexStep_exists
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop)
    {es1 es2 : List (Nat × Nat)} {maxComparisons : Option Nat}
    (hSem : PySemInv st n c aux)
    (hLenEs : es1.length = es2.length)
    (hCode :
      let run1 := (edgeSeqPy n es1).run st
      let run2 := (edgeSeqPy n es2).run run1.2
      boolSeqCode (run1.1.map (litVal (pyAssignmentAt run2.2 n c aux))) ≤
        boolSeqCode (run2.1.map (litVal (pyAssignmentAt run2.2 n c aux)))) :
    ∃ aux' : Nat → Prop,
      PySemInv
        ((do
          let lhs ← edgeSeqPy n es1
          let rhs ← edgeSeqPy n es2
          lexSmallerEqPy maxComparisons lhs rhs).run st).2 n c aux' := by
  let run1 : List Int × PyEncState := (edgeSeqPy n es1).run st
  let lhs : List Int := run1.1
  let st1 : PyEncState := run1.2
  have hSem1 : PySemInv st1 n c aux := by
    unfold st1 run1
    exact pySemInv_edgeSeqPy (st := st) (n := n) (c := c) aux (es := es1) hSem
  let run2 : List Int × PyEncState := (edgeSeqPy n es2).run st1
  let rhs : List Int := run2.1
  let st2 : PyEncState := run2.2
  have hSem2 : PySemInv st2 n c aux := by
    unfold st2 run2
    exact pySemInv_edgeSeqPy (st := st1) (n := n) (c := c) aux (es := es2) hSem1
  have hProps1 :
      (∀ i : Int, i ∈ lhs → i.natAbs < st1.nextId) ∧
        (∀ i : Int, i ∈ lhs → i ≠ 0) := by
    unfold lhs st1 run1
    simpa using edgeSeqPy_run_bound_noZero (st := st) (n := n) (c := c) aux (es := es1) hSem
  have hProps2 :
      (∀ i : Int, i ∈ rhs → i.natAbs < st2.nextId) ∧
        (∀ i : Int, i ∈ rhs → i ≠ 0) := by
    unfold rhs st2 run2
    simpa using edgeSeqPy_run_bound_noZero (st := st1) (n := n) (c := c) aux (es := es2) hSem1
  have hSt1LeSt2 : st1.nextId ≤ st2.nextId := by
    unfold st2 run2
    exact pyState_nextId_le_edgeSeqPy (st := st1) (n := n) (es := es2)
  have hBound1 : ∀ i : Int, i ∈ lhs → i.natAbs < st2.nextId := by
    intro i hi
    exact lt_of_lt_of_le (hProps1.1 i hi) hSt1LeSt2
  have hBound2 : ∀ i : Int, i ∈ rhs → i.natAbs < st2.nextId := hProps2.1
  have hNoZero1 : ∀ i : Int, i ∈ lhs → i ≠ 0 := hProps1.2
  have hNoZero2 : ∀ i : Int, i ∈ rhs → i ≠ 0 := hProps2.2
  have hLen : lhs.length = rhs.length := by
    have hLen1 : lhs.length = es1.length := by
      unfold lhs run1
      simpa using edgeSeqPy_run_length (st := st) (n := n) (es := es1)
    have hLen2 : rhs.length = es2.length := by
      unfold rhs run2
      simpa using edgeSeqPy_run_length (st := st1) (n := n) (es := es2)
    exact hLen1.trans (hLenEs.trans hLen2.symm)
  have hCode' :
      boolSeqCode (lhs.map (litVal (pyAssignmentAt st2 n c aux))) ≤
        boolSeqCode (rhs.map (litVal (pyAssignmentAt st2 n c aux))) := by
    unfold lhs rhs st2 run2 run1
    simpa using hCode
  rcases
    pySemInv_lexSmallerEqPy
      (st := st2) (n := n) (c := c) aux
      (maxComparisons := maxComparisons) (seq1 := lhs) (seq2 := rhs)
      hSem2 hLen hBound1 hBound2 hNoZero1 hNoZero2 hCode' with ⟨aux', hLex⟩
  exact ⟨aux', by
    simpa [Bind.bind, pure, run1, lhs, st1, run2, rhs, st2] using hLex⟩

private lemma mem_natPairsIncreasing
    {n i j : Nat} (hmem : (i, j) ∈ natPairsIncreasing n) :
    i < n ∧ j < n ∧ i < j := by
  unfold natPairsIncreasing at hmem
  rcases List.mem_flatMap.mp hmem with ⟨i0, hi0, hInner⟩
  rcases List.mem_filterMap.mp hInner with ⟨j0, hj0, hSome⟩
  by_cases hij : i0 < j0
  · simp [hij] at hSome
    rcases hSome with ⟨hiEq, hjEq⟩
    subst hiEq
    subst hjEq
    exact ⟨List.mem_range.mp hi0, List.mem_range.mp hj0, hij⟩
  · simp [hij] at hSome

private def flipVertex {n : Nat} (i : Fin n) (v : Vertex n) : Vertex n :=
  fun k => if k = i then !v k else v k

private def swapVertex {n : Nat} (i j : Fin n) (v : Vertex n) : Vertex n :=
  fun k => if k = i then v j else if k = j then v i else v k

private lemma swapVertex_eq_swapEquiv {n : Nat} (i j : Fin n) (v : Vertex n) :
    swapVertex i j v = fun k => v ((Equiv.swap i j) k) := by
  funext k
  by_cases hki : k = i
  · subst hki
    simp [swapVertex, Equiv.swap_apply_def]
  · by_cases hkj : k = j
    · subst hkj
      simp [swapVertex, Equiv.swap_apply_def, hki]
    · simp [swapVertex, Equiv.swap_apply_def, hki, hkj]

private lemma dist_reindex {n : Nat} (e : Equiv (Fin n) (Fin n))
    (u v : Vertex n) :
    dist (fun k => u (e k)) (fun k => v (e k)) = dist u v := by
  unfold dist ThreeColorSAT.Hypercube.hamming
  let s : Finset (Fin n) := Finset.univ.filter (fun k : Fin n => u (e k) ≠ v (e k))
  have hImage :
      s.image e = Finset.univ.filter (fun k : Fin n => u k ≠ v k) := by
    ext k
    constructor
    · intro hk
      rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
      exact Finset.mem_filter.mpr ⟨by simp, (Finset.mem_filter.mp hx).2⟩
    · intro hk
      refine Finset.mem_image.mpr ?_
      refine ⟨e.symm k, ?_, by simp⟩
      exact Finset.mem_filter.mpr ⟨by simp, by simpa using hk⟩
  have hCard :
      s.card = (s.image e).card := by
    symm
    exact Finset.card_image_of_injective (s := s) (f := e) (by
      intro a b hab
      exact e.injective hab)
  calc
    (Finset.univ.filter (fun k : Fin n => u (e k) ≠ v (e k))).card = s.card := by rfl
    _ = (s.image e).card := hCard
    _ = (Finset.univ.filter (fun k : Fin n => u k ≠ v k)).card := by simpa [hImage]

private lemma dist_flipVertex {n : Nat} (i : Fin n) (u v : Vertex n) :
    dist (flipVertex i u) (flipVertex i v) = dist u v := by
  unfold dist ThreeColorSAT.Hypercube.hamming flipVertex
  have hEq :
      (Finset.univ.filter (fun k : Fin n =>
        (if k = i then !u k else u k) ≠ (if k = i then !v k else v k))) =
      Finset.univ.filter (fun k : Fin n => u k ≠ v k) := by
    ext k
    by_cases hki : k = i <;> simp [hki]
  simpa [hEq]

private lemma dist_swapVertex {n : Nat} (i j : Fin n) (u v : Vertex n) :
    dist (swapVertex i j u) (swapVertex i j v) = dist u v := by
  calc
    dist (swapVertex i j u) (swapVertex i j v)
        = dist (fun k => u ((Equiv.swap i j) k)) (fun k => v ((Equiv.swap i j) k)) := by
            simp [swapVertex_eq_swapEquiv]
    _ = dist u v := dist_reindex (e := Equiv.swap i j) u v

private def flipCubeSymmetry {n : Nat} (i : Fin n) : CubeSymmetry n where
  map := flipVertex i
  inv := flipVertex i
  left_inv := by
    intro v
    funext k
    by_cases hki : k = i <;> simp [flipVertex, hki]
  right_inv := by
    intro v
    funext k
    by_cases hki : k = i <;> simp [flipVertex, hki]
  preservesAdj := by
    intro u v
    constructor <;> intro h
    · have hDist : dist (flipVertex i u) (flipVertex i v) = dist u v :=
        dist_flipVertex i u v
      have hBase : dist u v = 1 := by
        simpa [Adj, ThreeColorSAT.Hypercube.Q] using h
      have h' : dist (flipVertex i u) (flipVertex i v) = 1 := by
        simpa [hDist] using hBase
      simpa [Adj, ThreeColorSAT.Hypercube.Q] using h'
    · have hDist : dist (flipVertex i u) (flipVertex i v) = dist u v :=
        dist_flipVertex i u v
      have hMapped : dist (flipVertex i u) (flipVertex i v) = 1 := by
        simpa [Adj, ThreeColorSAT.Hypercube.Q] using h
      have h' : dist u v = 1 := by
        simpa [hDist] using hMapped
      simpa [Adj, ThreeColorSAT.Hypercube.Q] using h'
  commutesAntipode := by
    intro v
    funext k
    by_cases hki : k = i <;> simp [flipVertex, antipode, hki]

private def swapCubeSymmetry {n : Nat} (i j : Fin n) : CubeSymmetry n where
  map := swapVertex i j
  inv := swapVertex i j
  left_inv := by
    intro v
    funext k
    simp [swapVertex_eq_swapEquiv]
  right_inv := by
    intro v
    funext k
    simp [swapVertex_eq_swapEquiv]
  preservesAdj := by
    intro u v
    constructor <;> intro h
    · have hDist : dist (swapVertex i j u) (swapVertex i j v) = dist u v :=
        dist_swapVertex i j u v
      have hBase : dist u v = 1 := by
        simpa [Adj, ThreeColorSAT.Hypercube.Q] using h
      have h' : dist (swapVertex i j u) (swapVertex i j v) = 1 := by
        simpa [hDist] using hBase
      simpa [Adj, ThreeColorSAT.Hypercube.Q] using h'
    · have hDist : dist (swapVertex i j u) (swapVertex i j v) = dist u v :=
        dist_swapVertex i j u v
      have hMapped : dist (swapVertex i j u) (swapVertex i j v) = 1 := by
        simpa [Adj, ThreeColorSAT.Hypercube.Q] using h
      have h' : dist u v = 1 := by
        simpa [hDist] using hMapped
      simpa [Adj, ThreeColorSAT.Hypercube.Q] using h'
  commutesAntipode := by
    intro v
    funext k
    by_cases hki : k = i
    · subst hki
      simp [swapVertex, antipode]
    · by_cases hkj : k = j
      · subst hkj
        simp [swapVertex, antipode, hki]
      · simp [swapVertex, antipode, hki, hkj]

private lemma natToVertex_flipCode_eq_flipVertex
    {n u : Nat} (i : Fin n) :
    natToVertex n (flipCode u i.1) = flipVertex i (natToVertex n u) := by
  funext k
  by_cases hki : k = i
  · subst hki
    simp [natToVertex, flipVertex, testBit_flipCode_eq_not]
  · have hki' : k.1 ≠ i.1 := by
      intro hk
      apply hki
      exact Fin.ext hk
    simp [natToVertex, flipVertex, hki,
      testBit_flipCode_eq_of_ne (u := u) (i := i.1) (j := k.1) hki']

private lemma testBit_swapCode (u i j k : Nat) :
    (swapCode u i j).testBit k =
      (if k = i then u.testBit j else if k = j then u.testBit i else u.testBit k) := by
  by_cases hij : u.testBit i = u.testBit j
  · by_cases hki : k = i
    · subst hki
      simp [swapCode, bitAt, hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [swapCode, bitAt, hij]
      · simp [swapCode, bitAt, hij, hki, hkj]
  · have hijNe : u.testBit i ≠ u.testBit j := hij
    have hiToj : (! (u.testBit i)) = u.testBit j := by
      cases hi : u.testBit i <;> cases hj : u.testBit j <;> simp [hi, hj] at hijNe ⊢
    have hjToi : (! (u.testBit j)) = u.testBit i := by
      cases hi : u.testBit i <;> cases hj : u.testBit j <;> simp [hi, hj] at hijNe ⊢
    have hSwap : swapCode u i j = flipCode (flipCode u i) j := by
      unfold swapCode flipCode toggleBit bitAt
      simp [hij]
    rw [hSwap]
    by_cases hki : k = i
    · subst k
      by_cases hijEq : i = j
      · subst hijEq
        exact False.elim (hij rfl)
      · rw [testBit_flipCode_eq_of_ne (u := flipCode u i) (i := j) (j := i) hijEq]
        rw [testBit_flipCode_eq_not (u := u) (i := i)]
        simpa using hjToi.symm
    · by_cases hkj : k = j
      · subst k
        rw [testBit_flipCode_eq_not (u := flipCode u i) (i := j)]
        rw [testBit_flipCode_eq_of_ne (u := u) (i := i) (j := j) hki]
        simpa [hki] using hjToi
      · rw [testBit_flipCode_eq_of_ne (u := flipCode u i) (i := j) (j := k) hkj]
        rw [testBit_flipCode_eq_of_ne (u := u) (i := i) (j := k) hki]
        simp [hki, hkj]

private lemma natToVertex_swapCode_eq_swapVertex
    {n u : Nat} (i j : Fin n) :
    natToVertex n (swapCode u i.1 j.1) = swapVertex i j (natToVertex n u) := by
  funext k
  change (swapCode u i.1 j.1).testBit k.1 = swapVertex i j (natToVertex n u) k
  rw [testBit_swapCode (u := u) (i := i.1) (j := j.1) (k := k.1)]
  by_cases hki : k = i
  · have hki' : k.1 = i.1 := by simpa using congrArg Fin.val hki
    simp [natToVertex, swapVertex, hki, hki']
  · have hki' : k.1 ≠ i.1 := by
      intro hk
      apply hki
      exact Fin.ext hk
    by_cases hkj : k = j
    · have hkj' : k.1 = j.1 := by simpa using congrArg Fin.val hkj
      by_cases hji : j = i
      · subst hji
        simp [natToVertex, swapVertex, hki, hkj, hki', hkj']
      · have hji' : j.1 ≠ i.1 := by
          intro hEq
          exact hji (Fin.ext hEq)
        simp [natToVertex, swapVertex, hki, hkj, hki', hkj', hji, hji']
    · have hkj' : k.1 ≠ j.1 := by
        intro hk
        apply hkj
        exact Fin.ext hk
      simp [natToVertex, swapVertex, hki, hkj, hki', hkj']

private lemma swapCode_lt_pow {n u i j : Nat}
    (hu : u < 2 ^ n) (hi : i < n) (hj : j < n) :
    swapCode u i j < 2 ^ n := by
  by_cases hij : u.testBit i = u.testBit j
  · simp [swapCode, bitAt, hij, hu]
  · have hFlip : flipCode u i < 2 ^ n := flipCode_lt_pow hu hi
    have hSwapLt : flipCode (flipCode u i) j < 2 ^ n := flipCode_lt_pow hFlip hj
    simpa [swapCode, bitAt, hij, flipCode, toggleBit] using hSwapLt

private lemma swapCode_mem_allVertexCodes {n u i j : Nat}
    (hu : u ∈ allVertexCodes n) (hi : i < n) (hj : j < n) :
    swapCode u i j ∈ allVertexCodes n := by
  exact List.mem_range.mpr (swapCode_lt_pow (hu := mem_allVertexCodes_lt_pow hu) hi hj)

private lemma adj_flipCode {n u v i : Nat}
    (hi : i < n)
    (hAdj : Adj (natToVertex n u) (natToVertex n v)) :
    Adj (natToVertex n (flipCode u i)) (natToVertex n (flipCode v i)) := by
  let iFin : Fin n := ⟨i, hi⟩
  have hAdjMap :
      Adj (flipVertex iFin (natToVertex n u)) (flipVertex iFin (natToVertex n v)) :=
    ((flipCubeSymmetry iFin).preservesAdj (natToVertex n u) (natToVertex n v)).1 hAdj
  rw [natToVertex_flipCode_eq_flipVertex (n := n) (u := u) (i := iFin)]
  rw [natToVertex_flipCode_eq_flipVertex (n := n) (u := v) (i := iFin)]
  exact hAdjMap

private lemma adj_swapCode {n u v i j : Nat}
    (hi : i < n) (hj : j < n)
    (hAdj : Adj (natToVertex n u) (natToVertex n v)) :
    Adj (natToVertex n (swapCode u i j)) (natToVertex n (swapCode v i j)) := by
  let iFin : Fin n := ⟨i, hi⟩
  let jFin : Fin n := ⟨j, hj⟩
  have hAdjMap :
      Adj (swapVertex iFin jFin (natToVertex n u)) (swapVertex iFin jFin (natToVertex n v)) :=
    ((swapCubeSymmetry iFin jFin).preservesAdj (natToVertex n u) (natToVertex n v)).1 hAdj
  rw [natToVertex_swapCode_eq_swapVertex (n := n) (u := u) (i := iFin) (j := jFin)]
  rw [natToVertex_swapCode_eq_swapVertex (n := n) (u := v) (i := iFin) (j := jFin)]
  exact hAdjMap

private lemma edgeSeqCode_transport_eq_boolSeqCode_map
    {n : Nat} (σ : CubeSymmetry n) (c : EdgeColoring n) (f : Nat → Nat)
    (hf : ∀ u : Nat, natToVertex n (f u) = σ.inv (natToVertex n u)) :
    edgeSeqCode n (transportedColoring σ c) =
      boolSeqCode
        ((originalSignedEdgesPy n (allVertexCodes n)).map
          (fun e => c (edgeOf (natToVertex n (f e.1)) (natToVertex n (f e.2))))) := by
  let es1 := originalSignedEdgesPy n (allVertexCodes n)
  calc
    edgeSeqCode n (transportedColoring σ c)
        = boolSeqCode
            (es1.map (fun e =>
              c (edgeOf (σ.inv (natToVertex n e.1)) (σ.inv (natToVertex n e.2))))) := by
                simp [edgeSeqCode, es1, foldl_boolSeqCode_eq, transportedColoring_edgeOf]
    _ = boolSeqCode
          (es1.map (fun e =>
            c (edgeOf (natToVertex n (f e.1)) (natToVertex n (f e.2))))) := by
          simp [hf]
    _ = boolSeqCode
          ((originalSignedEdgesPy n (allVertexCodes n)).map
            (fun e => c (edgeOf (natToVertex n (f e.1)) (natToVertex n (f e.2))))) := by
          simp [es1]

private lemma lexLeader_colorBound_of_symmetryMap
    {n : Nat} {c : EdgeColoring n}
    (hLex : LexLeaderCanonical n c)
    (σ : CubeSymmetry n) (f : Nat → Nat)
    (hf : ∀ u : Nat, natToVertex n (f u) = σ.inv (natToVertex n u)) :
    edgeSeqCode n c ≤
      boolSeqCode
        ((originalSignedEdgesPy n (allVertexCodes n)).map
          (fun e => c (edgeOf (natToVertex n (f e.1)) (natToVertex n (f e.2))))) := by
  have hLe : edgeSeqCode n c ≤ edgeSeqCode n (transportedColoring σ c) :=
    hLex (transportedColoring σ c) ⟨σ, rfl⟩
  calc
    edgeSeqCode n c ≤ edgeSeqCode n (transportedColoring σ c) := hLe
    _ = boolSeqCode
          ((originalSignedEdgesPy n (allVertexCodes n)).map
            (fun e => c (edgeOf (natToVertex n (f e.1)) (natToVertex n (f e.2))))) :=
      edgeSeqCode_transport_eq_boolSeqCode_map (σ := σ) (c := c) (f := f) hf

private lemma lexLeader_colorBound_flip
    {n : Nat} {c : EdgeColoring n}
    (hLex : LexLeaderCanonical n c) (i : Nat) (hi : i < n) :
    edgeSeqCode n c ≤
      boolSeqCode
        ((originalSignedEdgesPy n (allVertexCodes n)).map
          (fun e => c (edgeOf (natToVertex n (flipCode e.1 i)) (natToVertex n (flipCode e.2 i))))) := by
  let iFin : Fin n := ⟨i, hi⟩
  exact
    lexLeader_colorBound_of_symmetryMap
      (hLex := hLex) (σ := flipCubeSymmetry iFin)
      (f := fun u => flipCode u i)
      (hf := by
        intro u
        show natToVertex n (flipCode u i) = (flipCubeSymmetry iFin).inv (natToVertex n u)
        simpa [flipCubeSymmetry] using natToVertex_flipCode_eq_flipVertex (n := n) (u := u) iFin)

private lemma lexLeader_colorBound_swap
    {n : Nat} {c : EdgeColoring n}
    (hLex : LexLeaderCanonical n c)
    (i j : Nat) (hi : i < n) (hj : j < n) :
    edgeSeqCode n c ≤
      boolSeqCode
        ((originalSignedEdgesPy n (allVertexCodes n)).map
          (fun e => c (edgeOf (natToVertex n (swapCode e.1 i j)) (natToVertex n (swapCode e.2 i j))))) := by
  let iFin : Fin n := ⟨i, hi⟩
  let jFin : Fin n := ⟨j, hj⟩
  exact
    lexLeader_colorBound_of_symmetryMap
      (hLex := hLex) (σ := swapCubeSymmetry iFin jFin)
      (f := fun u => swapCode u i j)
      (hf := by
        intro u
        show natToVertex n (swapCode u i j) = (swapCubeSymmetry iFin jFin).inv (natToVertex n u)
        simpa [swapCubeSymmetry] using natToVertex_swapCode_eq_swapVertex (n := n) (u := u) iFin jFin)

private lemma lexLeader_colorBound_swapFlip
    {n : Nat} {c : EdgeColoring n}
    (hLex : LexLeaderCanonical n c)
    (i j k : Nat) (hi : i < n) (hj : j < n) (hk : k < n) :
    edgeSeqCode n c ≤
      boolSeqCode
        ((originalSignedEdgesPy n (allVertexCodes n)).map
          (fun e =>
            c (edgeOf
              (natToVertex n (swapCode (flipCode e.1 k) i j))
              (natToVertex n (swapCode (flipCode e.2 k) i j))))) := by
  let iFin : Fin n := ⟨i, hi⟩
  let jFin : Fin n := ⟨j, hj⟩
  let kFin : Fin n := ⟨k, hk⟩
  let σ := compCubeSymmetry (swapCubeSymmetry iFin jFin) (flipCubeSymmetry kFin)
  exact
    lexLeader_colorBound_of_symmetryMap
      (hLex := hLex) (σ := σ)
      (f := fun u => swapCode (flipCode u k) i j)
      (hf := by
        intro u
        change
          natToVertex n (swapCode (flipCode u k) i j) =
            swapVertex iFin jFin (flipVertex kFin (natToVertex n u))
        calc
          natToVertex n (swapCode (flipCode u k) i j)
              = swapVertex iFin jFin (natToVertex n (flipCode u k)) := by
                  simpa using
                    (natToVertex_swapCode_eq_swapVertex
                      (n := n) (u := flipCode u k) (i := iFin) (j := jFin))
          _ = swapVertex iFin jFin (flipVertex kFin (natToVertex n u)) := by
                  rw [natToVertex_flipCode_eq_flipVertex (n := n) (u := u) (i := kFin)])

private lemma edgeProp_flip_permuted
    {n : Nat} (i : Nat) (hi : i < n) :
    ∀ e : Nat × Nat,
      e ∈ (originalSignedEdgesPy n (allVertexCodes n)).map
        (fun p => (flipCode p.1 i, flipCode p.2 i)) →
        e.1 ∈ allVertexCodes n ∧
          e.2 ∈ allVertexCodes n ∧
          Adj (natToVertex n e.1) (natToVertex n e.2) := by
  intro e he
  rcases List.mem_map.mp he with ⟨p, hp, rfl⟩
  rcases p with ⟨u, v⟩
  rcases
    mem_originalSignedEdgesPy_allVertexCodes (n := n) (u := u) (v := v) hp with
      ⟨hu, hv, hAdj⟩
  refine ⟨
    List.mem_range.mpr (flipCode_lt_pow (hu := mem_allVertexCodes_lt_pow hu) hi),
    List.mem_range.mpr (flipCode_lt_pow (hu := mem_allVertexCodes_lt_pow hv) hi),
    adj_flipCode (n := n) (u := u) (v := v) (i := i) hi hAdj⟩

private lemma edgeProp_swap_permuted
    {n : Nat} (i j : Nat) (hi : i < n) (hj : j < n) :
    ∀ e : Nat × Nat,
      e ∈ (originalSignedEdgesPy n (allVertexCodes n)).map
        (fun p => (swapCode p.1 i j, swapCode p.2 i j)) →
        e.1 ∈ allVertexCodes n ∧
          e.2 ∈ allVertexCodes n ∧
          Adj (natToVertex n e.1) (natToVertex n e.2) := by
  intro e he
  rcases List.mem_map.mp he with ⟨p, hp, rfl⟩
  rcases p with ⟨u, v⟩
  rcases
    mem_originalSignedEdgesPy_allVertexCodes (n := n) (u := u) (v := v) hp with
      ⟨hu, hv, hAdj⟩
  refine ⟨
    swapCode_mem_allVertexCodes (n := n) (u := u) (i := i) (j := j) hu hi hj,
    swapCode_mem_allVertexCodes (n := n) (u := v) (i := i) (j := j) hv hi hj,
    adj_swapCode (n := n) (u := u) (v := v) (i := i) (j := j) hi hj hAdj⟩

private lemma edgeProp_swapFlip_permuted
    {n : Nat} (i j k : Nat) (hi : i < n) (hj : j < n) (hk : k < n) :
    ∀ e : Nat × Nat,
      e ∈ (originalSignedEdgesPy n (allVertexCodes n)).map
        (fun p => (swapCode (flipCode p.1 k) i j, swapCode (flipCode p.2 k) i j)) →
        e.1 ∈ allVertexCodes n ∧
          e.2 ∈ allVertexCodes n ∧
          Adj (natToVertex n e.1) (natToVertex n e.2) := by
  intro e he
  rcases List.mem_map.mp he with ⟨p, hp, rfl⟩
  rcases p with ⟨u, v⟩
  rcases
    mem_originalSignedEdgesPy_allVertexCodes (n := n) (u := u) (v := v) hp with
      ⟨hu, hv, hAdj⟩
  have huFlip : flipCode u k ∈ allVertexCodes n := by
    exact List.mem_range.mpr (flipCode_lt_pow (hu := mem_allVertexCodes_lt_pow hu) hk)
  have hvFlip : flipCode v k ∈ allVertexCodes n := by
    exact List.mem_range.mpr (flipCode_lt_pow (hu := mem_allVertexCodes_lt_pow hv) hk)
  have hAdjFlip :
      Adj (natToVertex n (flipCode u k)) (natToVertex n (flipCode v k)) :=
    adj_flipCode (n := n) (u := u) (v := v) (i := k) hk hAdj
  refine ⟨
    swapCode_mem_allVertexCodes (n := n) (u := flipCode u k) (i := i) (j := j) huFlip hi hj,
    swapCode_mem_allVertexCodes (n := n) (u := flipCode v k) (i := i) (j := j) hvFlip hi hj,
    adj_swapCode (n := n) (u := flipCode u k) (v := flipCode v k) (i := i) (j := j) hi hj hAdjFlip⟩

private lemma lexLeader_implies_edgeSeq_hCode
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop)
    (hAnti : IsAntipodalColoring c)
    (hLex : LexLeaderCanonical n c)
    (hSem : PySemInv st n c aux)
    {es2 : List (Nat × Nat)}
    (hLen :
      (originalSignedEdgesPy n (allVertexCodes n)).length = es2.length)
    (hEdge2 :
      ∀ e : Nat × Nat, e ∈ es2 →
        e.1 ∈ allVertexCodes n ∧
          e.2 ∈ allVertexCodes n ∧
          Adj (natToVertex n e.1) (natToVertex n e.2))
    (hColorBound :
      edgeSeqCode n c ≤
        boolSeqCode (es2.map (fun e => c (edgeOf (natToVertex n e.1) (natToVertex n e.2))))) :
    let es1 := originalSignedEdgesPy n (allVertexCodes n)
    let run1 := (edgeSeqPy n es1).run st
    let run2 := (edgeSeqPy n es2).run run1.2
    boolSeqCode (run1.1.map (litVal (pyAssignmentAt run2.2 n c aux))) ≤
      boolSeqCode (run2.1.map (litVal (pyAssignmentAt run2.2 n c aux))) := by
  let es1 := originalSignedEdgesPy n (allVertexCodes n)
  let run1 : List Int × PyEncState := (edgeSeqPy n es1).run st
  let run2 : List Int × PyEncState := (edgeSeqPy n es2).run run1.2
  let τ1 : CNF.Assignment Nat := pyAssignmentAt run1.2 n c aux
  let τ2 : CNF.Assignment Nat := pyAssignmentAt run2.2 n c aux
  have hSem1 : PySemInv run1.2 n c aux := by
    unfold run1 es1
    exact pySemInv_edgeSeqPy (st := st) (n := n) (c := c) aux (es := es1) hSem
  have hBoundRun1 :
      ∀ i : Int, i ∈ run1.1 → i.natAbs < run1.2.nextId := by
    unfold run1 es1
    exact (edgeSeqPy_run_bound_noZero (st := st) (n := n) (c := c) aux
      (es := originalSignedEdgesPy n (allVertexCodes n)) hSem).1
  have hSatEqRun1 :
      ∀ i : Int, i ∈ run1.1 →
        (CNF.Lit.Sat τ2 (litOfDimacsInt i) ↔
          CNF.Lit.Sat τ1 (litOfDimacsInt i)) := by
    intro i hi
    have hiBound : i.natAbs < run1.2.nextId := hBoundRun1 i hi
    have hSatPres :=
      pyLitSat_edgeSeqPy_eq_of_bound
        (st := run1.2) (n := n) (c := c) aux (es := es2) (i := i) hiBound
    simpa [run2, τ1, τ2] using hSatPres
  have hLeftPres :
      boolSeqCode (run1.1.map (litVal τ2)) =
        boolSeqCode (run1.1.map (litVal τ1)) := by
    exact boolSeqCode_eq_map_litVal_of_litSatEq
      (τ := τ2) (τ' := τ1) run1.1 hSatEqRun1
  have hLeftBase :
      boolSeqCode (run1.1.map (litVal τ1)) = edgeSeqCode n c := by
    unfold run1 es1 τ1
    simpa using
      (edgeSeqCode_eq_boolSeqCode_edgeSeqPy_original
        (st := st) (n := n) (c := c) aux hAnti hSem)
  have hRightAsColors :
      run2.1.map (litVal τ2) =
        es2.map (fun e => c (edgeOf (natToVertex n e.1) (natToVertex n e.2))) := by
    unfold run2 τ2
    simpa using
      (edgeSeqPy_run_litVals_eq_colors
        (st := run1.2) (n := n) (c := c) aux (es := es2) hAnti hSem1 hEdge2)
  have hRightEq :
      boolSeqCode (run2.1.map (litVal τ2)) =
        boolSeqCode (es2.map (fun e => c (edgeOf (natToVertex n e.1) (natToVertex n e.2)))) := by
    simpa using congrArg boolSeqCode hRightAsColors
  calc
    boolSeqCode (run1.1.map (litVal τ2))
        = edgeSeqCode n c := by
            exact hLeftPres.trans hLeftBase
    _ ≤ boolSeqCode (es2.map (fun e => c (edgeOf (natToVertex n e.1) (natToVertex n e.2)))) :=
      hColorBound
    _ = boolSeqCode (run2.1.map (litVal τ2)) := hRightEq.symm

private lemma pySemInv_addPartialSymBreakPy_exists_of_lexLeader
    {st : PyEncState} {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop)
    (hAnti : IsAntipodalColoring c)
    (hLex : LexLeaderCanonical n c)
    (hSem : PySemInv st n c aux) :
    ∃ aux' : Nat → Prop,
      PySemInv ((addPartialSymBreakPy n (allVertexCodes n) 20).run st).2 n c aux' := by
  let originalEdges := originalSignedEdgesPy n (allVertexCodes n)
  let stepFlip : Nat → PUnit → PyEncM (ForInStep PUnit) := fun i _ => do
    let permuted := originalEdges.map (fun (u, v) => (flipCode u i, flipCode v i))
    let lhs ← edgeSeqPy n originalEdges
    let rhs ← edgeSeqPy n permuted
    let _ ← lexSmallerEqPy none lhs rhs
    pure (ForInStep.yield PUnit.unit)
  have hStepFlip :
      ∀ (i : Nat), i ∈ List.range n →
      ∀ (r : PUnit) (st' : PyEncState) (aux' : Nat → Prop),
        PySemInv st' n c aux' →
          ∃ aux'' : Nat → Prop, PySemInv ((stepFlip i r).run st').2 n c aux'' := by
    intro i hi r st' aux' hSem'
    let permuted := originalEdges.map (fun (u, v) => (flipCode u i, flipCode v i))
    have hiLt : i < n := List.mem_range.mp hi
    have hLenEs : originalEdges.length = permuted.length := by
      simp [permuted]
    have hEdgePerm :
        ∀ e : Nat × Nat, e ∈ permuted →
          e.1 ∈ allVertexCodes n ∧
            e.2 ∈ allVertexCodes n ∧
            Adj (natToVertex n e.1) (natToVertex n e.2) := by
      simpa [originalEdges, permuted] using edgeProp_flip_permuted (n := n) (i := i) hiLt
    have hColorPerm :
        edgeSeqCode n c ≤
          boolSeqCode (permuted.map (fun e =>
            c (edgeOf (natToVertex n e.1) (natToVertex n e.2)))) := by
      simpa [originalEdges, permuted] using
        (lexLeader_colorBound_flip (n := n) (c := c) hLex i hiLt)
    have hCode :
        let run1 := (edgeSeqPy n originalEdges).run st'
        let run2 := (edgeSeqPy n permuted).run run1.2
        boolSeqCode (run1.1.map (litVal (pyAssignmentAt run2.2 n c aux'))) ≤
          boolSeqCode (run2.1.map (litVal (pyAssignmentAt run2.2 n c aux'))) := by
      simpa [originalEdges] using
        (lexLeader_implies_edgeSeq_hCode
          (st := st') (n := n) (c := c) (aux := aux') hAnti hLex hSem'
          (es2 := permuted) hLenEs hEdgePerm hColorPerm)
    rcases
      pySemInv_edgeSeqLexStep_exists
        (st := st') (n := n) (c := c) aux'
        (es1 := originalEdges) (es2 := permuted) (maxComparisons := none)
        hSem' hLenEs hCode with ⟨aux'', hStep⟩
    exact ⟨aux'', by
      simpa [stepFlip, permuted, Bind.bind, pure] using hStep⟩
  let pairs := natPairsIncreasing n
  let stepSwap : (Nat × Nat) → PUnit → PyEncM (ForInStep PUnit) := fun ij _ => do
    let i := ij.1
    let j := ij.2
    let permuted := originalEdges.map (fun (u, v) => (swapCode u i j, swapCode v i j))
    let lhs ← edgeSeqPy n originalEdges
    let rhs ← edgeSeqPy n permuted
    let _ ← lexSmallerEqPy (some 20) lhs rhs
    pure (ForInStep.yield PUnit.unit)
  have hStepSwap :
      ∀ (ij : Nat × Nat), ij ∈ pairs →
      ∀ (r : PUnit) (st' : PyEncState) (aux' : Nat → Prop),
        PySemInv st' n c aux' →
          ∃ aux'' : Nat → Prop, PySemInv ((stepSwap ij r).run st').2 n c aux'' := by
    intro ij hij r st' aux' hSem'
    let i := ij.1
    let j := ij.2
    have hPair : i < n ∧ j < n ∧ i < j := by
      simpa [pairs, i, j] using
        (mem_natPairsIncreasing (n := n) (i := i) (j := j) hij)
    have hiLt : i < n := hPair.1
    have hjLt : j < n := hPair.2.1
    let permuted := originalEdges.map (fun (u, v) => (swapCode u i j, swapCode v i j))
    have hLenEs : originalEdges.length = permuted.length := by
      simp [permuted]
    have hEdgePerm :
        ∀ e : Nat × Nat, e ∈ permuted →
          e.1 ∈ allVertexCodes n ∧
            e.2 ∈ allVertexCodes n ∧
            Adj (natToVertex n e.1) (natToVertex n e.2) := by
      simpa [originalEdges, permuted] using
        edgeProp_swap_permuted (n := n) (i := i) (j := j) hiLt hjLt
    have hColorPerm :
        edgeSeqCode n c ≤
          boolSeqCode (permuted.map (fun e =>
            c (edgeOf (natToVertex n e.1) (natToVertex n e.2)))) := by
      simpa [originalEdges, permuted] using
        (lexLeader_colorBound_swap (n := n) (c := c) hLex i j hiLt hjLt)
    have hCode :
        let run1 := (edgeSeqPy n originalEdges).run st'
        let run2 := (edgeSeqPy n permuted).run run1.2
        boolSeqCode (run1.1.map (litVal (pyAssignmentAt run2.2 n c aux'))) ≤
          boolSeqCode (run2.1.map (litVal (pyAssignmentAt run2.2 n c aux'))) := by
      simpa [originalEdges] using
        (lexLeader_implies_edgeSeq_hCode
          (st := st') (n := n) (c := c) (aux := aux') hAnti hLex hSem'
          (es2 := permuted) hLenEs hEdgePerm hColorPerm)
    rcases
      pySemInv_edgeSeqLexStep_exists
        (st := st') (n := n) (c := c) aux'
        (es1 := originalEdges) (es2 := permuted) (maxComparisons := some 20)
        hSem' hLenEs hCode with ⟨aux'', hStep⟩
    exact ⟨aux'', by
      simpa [stepSwap, i, j, permuted, Bind.bind, pure] using hStep⟩
  let stepSwapFlipK : Nat → Nat → Nat → PUnit → PyEncM (ForInStep PUnit) := fun i j k _ => do
    let permuted := originalEdges.map (fun (u, v) =>
      (swapCode (flipCode u k) i j, swapCode (flipCode v k) i j))
    let lhs ← edgeSeqPy n originalEdges
    let rhs ← edgeSeqPy n permuted
    let _ ← lexSmallerEqPy (some 20) lhs rhs
    pure (ForInStep.yield PUnit.unit)
  have hStepSwapFlipK :
      ∀ (i j k : Nat), i < n → j < n → k ∈ List.range n →
      ∀ (r : PUnit) (st' : PyEncState) (aux' : Nat → Prop),
        PySemInv st' n c aux' →
          ∃ aux'' : Nat → Prop, PySemInv ((stepSwapFlipK i j k r).run st').2 n c aux'' := by
    intro i j k hi hj hk r st' aux' hSem'
    have hkLt : k < n := List.mem_range.mp hk
    let permuted := originalEdges.map (fun (u, v) =>
      (swapCode (flipCode u k) i j, swapCode (flipCode v k) i j))
    have hLenEs : originalEdges.length = permuted.length := by
      simp [permuted]
    have hEdgePerm :
        ∀ e : Nat × Nat, e ∈ permuted →
          e.1 ∈ allVertexCodes n ∧
            e.2 ∈ allVertexCodes n ∧
            Adj (natToVertex n e.1) (natToVertex n e.2) := by
      simpa [originalEdges, permuted] using
        edgeProp_swapFlip_permuted (n := n) (i := i) (j := j) (k := k) hi hj hkLt
    have hColorPerm :
        edgeSeqCode n c ≤
          boolSeqCode (permuted.map (fun e =>
            c (edgeOf (natToVertex n e.1) (natToVertex n e.2)))) := by
      simpa [originalEdges, permuted] using
        (lexLeader_colorBound_swapFlip (n := n) (c := c) hLex i j k hi hj hkLt)
    have hCode :
        let run1 := (edgeSeqPy n originalEdges).run st'
        let run2 := (edgeSeqPy n permuted).run run1.2
        boolSeqCode (run1.1.map (litVal (pyAssignmentAt run2.2 n c aux'))) ≤
          boolSeqCode (run2.1.map (litVal (pyAssignmentAt run2.2 n c aux'))) := by
      simpa [originalEdges] using
        (lexLeader_implies_edgeSeq_hCode
          (st := st') (n := n) (c := c) (aux := aux') hAnti hLex hSem'
          (es2 := permuted) hLenEs hEdgePerm hColorPerm)
    rcases
      pySemInv_edgeSeqLexStep_exists
        (st := st') (n := n) (c := c) aux'
        (es1 := originalEdges) (es2 := permuted) (maxComparisons := some 20)
        hSem' hLenEs hCode with ⟨aux'', hStep⟩
    exact ⟨aux'', by
      simpa [stepSwapFlipK, permuted, Bind.bind, pure] using hStep⟩
  let stepSwapFlip : (Nat × Nat) → PUnit → PyEncM (ForInStep PUnit) := fun ij _ =>
    let i := ij.1
    let j := ij.2
    let inner := forIn (List.range n) PUnit.unit (stepSwapFlipK i j)
    inner.bind fun _ => StateT.pure (ForInStep.yield PUnit.unit)
  have hStepSwapFlip :
      ∀ (ij : Nat × Nat), ij ∈ pairs →
      ∀ (r : PUnit) (st' : PyEncState) (aux' : Nat → Prop),
        PySemInv st' n c aux' →
          ∃ aux'' : Nat → Prop, PySemInv ((stepSwapFlip ij r).run st').2 n c aux'' := by
    intro ij hij r st' aux' hSem'
    let i := ij.1
    let j := ij.2
    have hPair : i < n ∧ j < n ∧ i < j := by
      simpa [pairs, i, j] using
        (mem_natPairsIncreasing (n := n) (i := i) (j := j) hij)
    have hiLt : i < n := hPair.1
    have hjLt : j < n := hPair.2.1
    rcases
      pySemInv_forIn_mem_exists
        (n := n) (c := c)
        (xs := List.range n) (init := PUnit.unit) (f := stepSwapFlipK i j)
        (hStep := by
          intro k hk r' st'' aux'' hSem''
          exact hStepSwapFlipK i j k hiLt hjLt hk r' st'' aux'' hSem'')
        st' aux' hSem' with ⟨aux1, hInner⟩
    have hInnerYield :
        PySemInv
          (((forIn (List.range n) PUnit.unit (stepSwapFlipK i j)).bind
            fun _ => StateT.pure (ForInStep.yield PUnit.unit)).run st').2 n c aux1 := by
      simpa [Bind.bind, pure] using hInner
    exact ⟨aux1, by
      simpa [stepSwapFlip, i, j] using hInnerYield⟩
  rcases
    pySemInv_forIn_mem_exists
      (n := n) (c := c)
      (xs := List.range n) (init := PUnit.unit) (f := stepFlip)
      (hStep := hStepFlip) st aux hSem with ⟨aux1, hFlipFor⟩
  rcases
    pySemInv_forIn_mem_exists
      (n := n) (c := c)
      (xs := pairs) (init := PUnit.unit) (f := stepSwap)
      (hStep := hStepSwap)
      ((forIn (List.range n) PUnit.unit stepFlip).run st).2 aux1 hFlipFor with ⟨aux2, hSwapFor⟩
  rcases
    pySemInv_forIn_mem_exists
      (n := n) (c := c)
      (xs := pairs) (init := PUnit.unit) (f := stepSwapFlip)
      (hStep := hStepSwapFlip)
      ((forIn pairs PUnit.unit stepSwap).run
        ((forIn (List.range n) PUnit.unit stepFlip).run st).2).2 aux2 hSwapFor with
      ⟨aux3, hSwapFlipFor⟩
  unfold addPartialSymBreakPy
  exact ⟨aux3, by
    simpa [originalEdges, pairs, stepFlip, stepSwap, stepSwapFlip, stepSwapFlipK, Bind.bind, pure]
      using hSwapFlipFor⟩

private lemma pySemInv_pysatState_exists_of_lexLeader
    {n : Nat} {c : EdgeColoring n}
    (hAnti : IsAntipodalColoring c)
    (hNoGeo : NoMonochromaticAntipodalGeodesic n c)
    (hLex : LexLeaderCanonical n c) :
    ∃ aux : Nat → Prop, PySemInv (pysatState n) n c aux := by
  let aux0 : Nat → Prop := fun _ => False
  let vs := allVertexCodes n
  have hVsMem : ∀ u : Nat, u ∈ vs → u ∈ allVertexCodes n := by
    intro u hu
    simpa [vs] using hu
  have hNbrMem :
      ∀ u : Nat, u ∈ vs → ∀ v : Nat, v ∈ neighborsCode n u → v ∈ allVertexCodes n := by
    intro u hu v hv
    exact neighborsCode_mem_allVertexCodes (n := n) (u := u) (v := v) (hVsMem u hu) hv
  have hNbrAdj :
      ∀ u : Nat, u ∈ vs → ∀ v : Nat,
        v ∈ neighborsCode n u → Adj (natToVertex n u) (natToVertex n v) := by
    intro u hu v hv
    exact neighborsCode_adj (n := n) (u := u) (v := v) hv
  let st0 : PyEncState := {}
  have hSem0 : PySemInv st0 n c aux0 := by
    simpa [st0] using (pySemInv_empty (n := n) (c := c) aux0)
  let st1 : PyEncState := ((addEdgeInitClausesPy n vs).run st0).2
  have hSem1 : PySemInv st1 n c aux0 := by
    simpa [st1] using
      (pySemInv_addEdgeInitClausesPy (st := st0) (n := n) (c := c) (vs := vs) aux0 hSem0)
  let st2 : PyEncState := ((addAntipodalClausesPy n vs).run st1).2
  have hSem2 : PySemInv st2 n c aux0 := by
    simpa [st2] using
      (pySemInv_addAntipodalClausesPy
        (st := st1) (n := n) (c := c) (vs := vs) aux0
        hAnti hVsMem hNbrMem hNbrAdj hSem1)
  let st3 : PyEncState := ((addEq5ClausesPy n vs).run st2).2
  have hSem3 : PySemInv st3 n c aux0 := by
    simpa [st3] using
      (pySemInv_addEq5ClausesPy
        (st := st2) (n := n) (c := c) (vs := vs) aux0
        hAnti hVsMem hNbrMem hNbrAdj hSem2)
  let st4 : PyEncState := ((addEq7Eq9ClausesPy n vs).run st3).2
  have hSem4 : PySemInv st4 n c aux0 := by
    simpa [st4] using
      (pySemInv_addEq7Eq9ClausesPy
        (st := st3) (n := n) (c := c) (vs := vs) aux0
        hAnti hVsMem hNbrMem hNbrAdj hSem3)
  let core : PyEncState := ((addConjecture1UnitClausesPy n vs).run st4).2
  have hSemCore : PySemInv core n c aux0 := by
    simpa [core] using
      (pySemInv_addConjecture1UnitClausesPy
        (st := st4) (n := n) (c := c) (vs := vs) aux0
        hNoGeo hVsMem hSem4)
  rcases
    pySemInv_addPartialSymBreakPy_exists_of_lexLeader
      (st := core) (n := n) (c := c) (aux := aux0) hAnti hLex hSemCore with
    ⟨aux1, hSemFinal⟩
  refine ⟨aux1, ?_⟩
  unfold pysatState buildPysatConjecture1AntipodalLexState
  have hIf : (if (20 = 0) then pure () else addPartialSymBreakPy n vs 20) =
      addPartialSymBreakPy n vs 20 := by simp
  simp [vs, st0, st1, st2, st3, st4, core, hIf] at hSemFinal ⊢
  exact hSemFinal

lemma pysat_sat_of_lexLeader_counterexample {n : Nat} {c : EdgeColoring n} :
    IsAntipodalColoring c →
      NoMonochromaticAntipodalGeodesic n c →
      LexLeaderCanonical n c →
      CNF.Satisfiable (PysatConjecture1Formula n) := by
  intro hAnti hNoGeo hLex
  rcases pySemInv_pysatState_exists_of_lexLeader (n := n) (c := c) hAnti hNoGeo hLex with
    ⟨aux, hSem⟩
  exact pysatSat_of_pySemInv (n := n) (c := c) aux hSem

private lemma pySemInv_simplifiedLexState_exists_of_lexLeader
    {n : Nat} {c : EdgeColoring n}
    (hAnti : IsAntipodalColoring c)
    (hNoGeo : NoMonochromaticAntipodalGeodesic n c)
    (hLex : LexLeaderCanonical n c) :
    ∃ aux : Nat → Prop, PySemInv (simplifiedLexState n) n c aux := by
  let aux0 : Nat → Prop := fun _ => False
  let vs := allVertexCodes n
  have hVsMem : ∀ u : Nat, u ∈ vs → u ∈ allVertexCodes n := by
    intro u hu
    simpa [vs] using hu
  have hNbrMem :
      ∀ u : Nat, u ∈ vs → ∀ v : Nat, v ∈ neighborsCode n u → v ∈ allVertexCodes n := by
    intro u hu v hv
    exact neighborsCode_mem_allVertexCodes (n := n) (u := u) (v := v) (hVsMem u hu) hv
  have hNbrAdj :
      ∀ u : Nat, u ∈ vs → ∀ v : Nat,
        v ∈ neighborsCode n u → Adj (natToVertex n u) (natToVertex n v) := by
    intro u hu v hv
    exact neighborsCode_adj (n := n) (u := u) (v := v) hv
  let st0 : PyEncState := {}
  have hSem0 : PySemInv st0 n c aux0 := by
    simpa [st0] using (pySemInv_empty (n := n) (c := c) aux0)
  let st1 : PyEncState := ((addEdgeInitClausesPy n vs).run st0).2
  have hSem1 : PySemInv st1 n c aux0 := by
    simpa [st1] using
      (pySemInv_addEdgeInitClausesPy (st := st0) (n := n) (c := c) (vs := vs) aux0 hSem0)
  let st2 : PyEncState := ((addAntipodalClausesPy n vs).run st1).2
  have hSem2 : PySemInv st2 n c aux0 := by
    simpa [st2] using
      (pySemInv_addAntipodalClausesPy
        (st := st1) (n := n) (c := c) (vs := vs) aux0
        hAnti hVsMem hNbrMem hNbrAdj hSem1)
  let st3 : PyEncState := ((NorinSimplified.addMonoInitClausesPy n vs).run st2).2
  have hSem3 : PySemInv st3 n c aux0 := by
    simpa [st3] using
      (pySemInv_addMonoInitClausesPy
        (st := st2) (n := n) (c := c) (vs := vs) aux0
        hAnti hVsMem hNbrMem hNbrAdj hSem2)
  let st4 : PyEncState := ((NorinSimplified.addMonoStepClausesPy n vs true).run st3).2
  have hSem4 : PySemInv st4 n c aux0 := by
    simpa [st4] using
      (pySemInv_addMonoStepClausesPy
        (st := st3) (n := n) (c := c) (vs := vs) aux0
        hAnti hVsMem hNbrMem hNbrAdj hSem3)
  let core : PyEncState := ((NorinSimplified.addNoMonoAntipodeUnitClausesPy n vs).run st4).2
  have hSemCore : PySemInv core n c aux0 := by
    simpa [core] using
      (pySemInv_addNoMonoAntipodeUnitClausesPy
        (st := st4) (n := n) (c := c) (vs := vs) aux0
        hNoGeo hVsMem hSem4)
  rcases
    pySemInv_addPartialSymBreakPy_exists_of_lexLeader
      (st := core) (n := n) (c := c) (aux := aux0) hAnti hLex hSemCore with
    ⟨aux1, hSemFinal⟩
  refine ⟨aux1, ?_⟩
  unfold simplifiedLexState NorinSimplified.buildSimplifiedConjecture2AntipodalState
  have hIf : (if (20 = 0) then pure () else addPartialSymBreakPy n vs 20) =
      addPartialSymBreakPy n vs 20 := by simp
  simp [vs, st0, st1, st2, st3, st4, core, hIf] at hSemFinal ⊢
  exact hSemFinal

private lemma simplifiedLexSat_of_pySemInv
    {n : Nat} {c : EdgeColoring n}
    (aux : Nat → Prop)
    (hSem : PySemInv (simplifiedLexState n) n c aux) :
    CNF.Satisfiable
      {cl | cl ∈ (simplifiedLexState n).clauses.toList.map clauseOfDimacsArray} := by
  refine ⟨pyAssignmentAt (simplifiedLexState n) n c aux, ?_⟩
  exact pyFormulaSat_of_pySemInv
    (st := simplifiedLexState n) (n := n) (c := c) aux hSem

lemma simplified_sat_of_lexLeader_counterexample {n : Nat} {c : EdgeColoring n} :
    IsAntipodalColoring c →
      NoMonochromaticAntipodalGeodesic n c →
      LexLeaderCanonical n c →
      CNF.Satisfiable
        {cl |
          cl ∈
            (NorinSimplified.buildSimplifiedConjecture2AntipodalState n 20 false).clauses.toList.map
              clauseOfDimacsArray} := by
  intro hAnti hNoGeo hLex
  rcases pySemInv_simplifiedLexState_exists_of_lexLeader
    (n := n) (c := c) hAnti hNoGeo hLex with ⟨aux, hSem⟩
  simpa [simplifiedLexState] using
    (simplifiedLexSat_of_pySemInv (n := n) (c := c) aux hSem)

/--
Required lift theorem for the lex-leader-only encoding:
`SAT(Ψ_n) -> SAT(PysatConjecture1Formula n)`.
-/
theorem hLift_lexLeader (n : Nat) :
    2 ≤ n →
    CNF.Satisfiable (Psi n) → CNF.Satisfiable (PysatConjecture1Formula n) := by
  intro hDim
  intro hPsi
  rcases psi_counterexample_of_sat n hDim hPsi with ⟨c, hAnti, hNoGeo⟩
  rcases exists_lexLeader_representative (n := n) c with ⟨c', hEqv, hLex⟩
  have hPres :
      IsAntipodalColoring c' ∧ NoMonochromaticAntipodalGeodesic n c' :=
    symmetry_equivalent_preserves_counterexample (n := n) (c := c) (c' := c')
      hEqv hAnti hNoGeo
  exact pysat_sat_of_lexLeader_counterexample (n := n) (c := c') hPres.1 hPres.2 hLex

/--
Final UNSAT wrapper with the lex-leader lift instantiated.
-/
theorem geodesicConjecture_of_pysatConjecture1_unsat_lex
    (n : Nat) (hDim : 2 ≤ n)
    (hUnsat : ¬ CNF.Satisfiable (PysatConjecture1Formula n)) :
    NorinGeodesicConjecture n := by
  exact geodesicConjecture_of_pysatConjecture1_unsat
    (n := n) (hLift := hLift_lexLeader n hDim) hUnsat

end SymmetryBreaking
end NorinCNF
