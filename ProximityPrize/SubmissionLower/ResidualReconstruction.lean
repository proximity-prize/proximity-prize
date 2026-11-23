import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Polynomial.DegreeLT


open scoped BigOperators Polynomial
open Polynomial

namespace WronskianLeading

variable {F : Type*} [CommRing F] {n : ℕ}

/-- The coefficient at the sum of individual degree bounds is the product
of the coefficients at those bounds. -/
private theorem coeff_prod_at_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → F[X]) (d : ι → ℕ)
    (h : ∀ i ∈ s, (P i).natDegree ≤ d i) :
    (∏ i ∈ s, P i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (P i).coeff (d i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, (P j).natDegree ≤ d j :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hprod : (∏ j ∈ s, P j).natDegree ≤ ∑ j ∈ s, d j :=
      (natDegree_prod_le s P).trans (Finset.sum_le_sum hs)
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [coeff_mul_add_eq_of_natDegree_le (h i (Finset.mem_insert_self i s)) hprod, ih hs]

/-- Coefficient at the sum of the column degree bounds. This is an equality
even when the determinant cancels in that degree or a column is zero. -/
theorem coeff_det_scaled_hasse (P : Fin n → F[X]) :
    (Matrix.of (fun i j : Fin n => X ^ (i : ℕ) * hasseDeriv i (P j))).det.coeff
        (∑ j, (P j).natDegree) =
      (Matrix.of (fun i j : Fin n =>
        (P j).leadingCoeff * ((P j).natDegree.choose i : F))).det := by
  have hdegree (i j : Fin n) :
      (X ^ (i : ℕ) * hasseDeriv i (P j)).natDegree ≤ (P j).natDegree := by
    by_cases h : (i : ℕ) ≤ (P j).natDegree
    · calc
        _ ≤ (X ^ (i : ℕ) : F[X]).natDegree + (hasseDeriv i (P j)).natDegree :=
          natDegree_mul_le
        _ ≤ (i : ℕ) + ((P j).natDegree - (i : ℕ)) :=
          Nat.add_le_add (natDegree_X_pow_le _) (natDegree_hasseDeriv_le _ _)
        _ = _ := by rw [Nat.add_comm, Nat.sub_add_cancel h]
    · rw [hasseDeriv_eq_zero_of_lt_natDegree _ _ (Nat.lt_of_not_ge h), mul_zero, natDegree_zero]
      exact Nat.zero_le _
  have hcoeff (i j : Fin n) :
      (X ^ (i : ℕ) * hasseDeriv i (P j)).coeff (P j).natDegree =
        (P j).leadingCoeff * ((P j).natDegree.choose i : F) := by
    rw [coeff_X_pow_mul']
    by_cases h : (i : ℕ) ≤ (P j).natDegree
    · rw [if_pos h, hasseDeriv_coeff, Nat.sub_add_cancel h, coeff_natDegree, mul_comm]
    · rw [if_neg h, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h), Nat.cast_zero, mul_zero]
  rw [Matrix.det_apply', Matrix.det_apply', ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [show ((Equiv.Perm.sign σ : ℤ) : F[X]) = C ((Equiv.Perm.sign σ : ℤ) : F) by
      exact (map_intCast (C : F →+* F[X]) _).symm, coeff_C_mul]
  rw [coeff_prod_at_sum Finset.univ (fun j => X ^ (σ j : ℕ) * hasseDeriv (σ j) (P j))
      (fun j => (P j).natDegree) (fun j _ => hdegree (σ j) j)]
  simp_rw [hcoeff]

variable [IsDomain F]

/-- A binomial matrix at distinct natural-number points has nonzero
determinant whenever the points' casts remain distinct. -/
private theorem det_choose_ne_zero (d : Fin n → ℕ)
    (hd : Function.Injective fun j => (d j : F)) :
    (Matrix.of (fun i j : Fin n => ((d j).choose i : F))).det ≠ 0 := by
  let B : Matrix (Fin n) (Fin n) F :=
    Matrix.of (fun i j : Fin n => ((d i).choose j : F))
  have hV : (Matrix.vandermonde (fun j => (d j : F))).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hd
  have hfall :
      (Matrix.of fun i j : Fin n => (descPochhammer F j).eval (d i : F)) =
        Matrix.of (fun i j : Fin n => (Nat.factorial (j : ℕ) : F) * B i j) := by
    ext i j
    simp only [B, Matrix.of_apply, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde (fun j => (d j : F))
    (fun j => descPochhammer F j) (fun j => descPochhammer_natDegree F j)
    (fun j => monic_descPochhammer F j), hfall, Matrix.det_mul_row] at hV
  have hB : B.det ≠ 0 := fun hz => hV (by rw [hz, mul_zero])
  have htrans :
      (Matrix.of (fun i j : Fin n => ((d j).choose i : F))) = B.transpose := by
    ext i j
    rfl
  rw [htrans, Matrix.det_transpose]
  exact hB

/-- Distinct column degrees strictly below the characteristic make the
scaled Hasse matrix invertible over the rational function field. -/
theorem det_scaled_hasse_ne_zero {p : ℕ} [CharP F p] (P : Fin n → F[X])
    (hP : ∀ j, P j ≠ 0) (hdeg : ∀ j, (P j).natDegree < p)
    (hdistinct : Function.Injective fun j => (P j).natDegree) :
    (Matrix.of (fun i j : Fin n => X ^ (i : ℕ) * hasseDeriv i (P j))).det ≠ 0 := by
  have hcast : Function.Injective fun j => ((P j).natDegree : F) := by
    intro i j hij
    exact hdistinct (CharP.natCast_injOn_Iio F p (hdeg i) (hdeg j) hij)
  have hcoeff :
      (Matrix.of (fun i j : Fin n =>
        (P j).leadingCoeff * ((P j).natDegree.choose i : F))).det ≠ 0 := by
    change (Matrix.of (fun i j : Fin n => (P j).leadingCoeff *
      (Matrix.of (fun i j : Fin n => ((P j).natDegree.choose i : F))) i j)).det ≠ 0
    rw [Matrix.det_mul_row]
    exact mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun j _ => leadingCoeff_ne_zero.mpr (hP j)))
      (det_choose_ne_zero (fun j => (P j).natDegree) hcast)
  intro hz
  apply hcoeff
  rw [← coeff_det_scaled_hasse P, hz, coeff_zero]

end WronskianLeading

namespace WronskianLeading
noncomputable section

open Matrix

/-- Compute the value at any constant node from the jets at the symbolic
abscissa. The inverse matrix stays in the field of the symbolic abscissa. -/
theorem reconstruct {F L : Type*} [Field F] [Field L] {p n : ℕ} [CharP F p]
    (P : Fin n → F[X]) (nonzero : ∀ j, P j ≠ 0)
    (degree : ∀ j, (P j).natDegree < p)
    (different : Function.Injective fun j => (P j).natDegree)
    (φ : F[X] →+* L) (injective : Function.Injective φ) :
    ∃ A : F → Fin n → L, ∀ (x : F) (c : Fin n → F),
      let Q := ∑ j, C (c j) * P j
      (∑ i, A x i * φ (hasseDeriv i Q)) = φ (C (Q.eval x)) := by
  classical
  let W : Matrix (Fin n) (Fin n) F[X] := Matrix.of fun i j => hasseDeriv i (P j)
  have hw : W.det ≠ 0 := by
    have hn := det_scaled_hasse_ne_zero P nonzero degree different
    change (Matrix.of fun i j : Fin n => X ^ (i : ℕ) * W i j).det ≠ 0 at hn
    rw [Matrix.det_mul_column] at hn
    intro h
    rw [h,mul_zero] at hn
    exact hn rfl
  let M := φ.mapMatrix W
  have hM : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.map_det]
    exact fun h => hw (injective (h.trans φ.map_zero.symm))
  let val (x : F) : Fin n → L := fun j => φ (C ((P j).eval x))
  let row (x : F) : Fin n → L := Matrix.vecMul (val x) M⁻¹
  have hr (x : F) : Matrix.vecMul (row x) M = val x := by
    unfold row
    rw [Matrix.vecMul_vecMul,Matrix.nonsing_inv_mul _ hM,Matrix.vecMul_one]
  refine ⟨row,?_⟩
  intro x c
  dsimp only
  let a : Fin n → L := fun j => φ (C (c j))
  let Q : F[X] := ∑ j, C (c j) * P j
  have hj : (fun i : Fin n => φ (hasseDeriv i Q)) = Matrix.mulVec M a := by
    funext i
    simp only [Q,map_sum,Matrix.mulVec,dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    change φ (hasseDeriv i (C (c j) * P j)) = φ (hasseDeriv i (P j)) * φ (C (c j))
    rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul, map_mul, mul_comm]
  change dotProduct (row x) (fun i : Fin n => φ (hasseDeriv i Q)) = φ (C (Q.eval x))
  rw [hj,Matrix.dotProduct_mulVec,hr]
  simp only [Q,eval_finsetSum,eval_mul,eval_C,map_sum,map_mul,dotProduct,val,a]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

end
end WronskianLeading


open scoped BigOperators Polynomial
open Polynomial

namespace WronskianBasis

variable {F : Type*} [Field F] {n : ℕ}

/-- A subspace of bounded-degree polynomials has a basis with distinct
leading degrees. The empty subspace gives the empty basis. -/
theorem exists_basis_distinct_natDegree
    (W : Submodule F F[X]) (hW : W ≤ Polynomial.degreeLT F n) :
    ∃ b : Module.Basis (Fin (Module.finrank F W)) F W,
      (∀ i, (b i : F[X]) ≠ 0) ∧
        Function.Injective (fun i => (b i : F[X]).natDegree) := by
  classical
  let D := {i : Fin n // ∃ q : W, (q : F[X]) ≠ 0 ∧ (q : F[X]).natDegree = i.val}
  letI : Fintype D := Fintype.ofFinite D
  let v : D → W := fun i => Classical.choose i.property
  have hv0 (i : D) : (v i : F[X]) ≠ 0 := (Classical.choose_spec i.property).1
  have hvd (i : D) : (v i : F[X]).natDegree = i.val.val :=
    (Classical.choose_spec i.property).2
  have hvdeg : Function.Injective (fun i : D => (v i : F[X]).natDegree) := by
    intro i j h
    apply Subtype.ext
    apply Fin.ext
    simpa only [hvd] using h
  have hli : LinearIndependent F v := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha j
    by_contra hj
    let T := Finset.univ.filter (fun i : D => a i ≠ 0)
    have ht : T.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    obtain ⟨i, hi, hmax⟩ := T.exists_max_image (fun i => (v i : F[X]).natDegree) ht
    have hai : a i ≠ 0 := (Finset.mem_filter.mp hi).2
    let k := (v i : F[X]).natDegree
    let L := (lcoeff F k).comp W.subtype
    have he := congrArg L ha
    simp only [map_sum, map_smul, map_zero] at he
    change (∑ l, a l • (v l : F[X]).coeff k) = 0 at he
    have hsingle : (∑ l, a l • (v l : F[X]).coeff k) =
        a i • (v i : F[X]).coeff k := by
      apply Finset.sum_eq_single_of_mem i (Finset.mem_univ _)
      intro l _ hli'
      by_cases hl : a l = 0
      · rw [hl, zero_smul]
      · have hlT : l ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
        have hlt : (v l : F[X]).natDegree < k :=
          lt_of_le_of_ne (hmax l hlT) (fun eq => hli' (hvdeg eq))
        rw [coeff_eq_zero_of_natDegree_lt hlt, smul_zero]
    rw [hsingle, smul_eq_mul] at he
    change a i * (v i : F[X]).leadingCoeff = 0 at he
    exact (mul_ne_zero hai (leadingCoeff_ne_zero.mpr (hv0 i))) he
  let S := Submodule.span F (Set.range v)
  have hspan : (⊤ : Submodule F W) ≤ S := by
    intro q htop
    clear htop
    generalize hd : (q : F[X]).natDegree = d
    induction d using Nat.strong_induction_on generalizing q with
    | h d ih =>
      by_cases hq : q = 0
      · rw [hq]
        exact S.zero_mem
      have hq0 : (q : F[X]) ≠ 0 := fun h => hq (Subtype.ext h)
      have hdn : d < n := by
        rw [← hd]
        exact (natDegree_lt_iff_degree_lt hq0).mpr (mem_degreeLT.mp (hW q.property))
      let i : D := ⟨⟨d, hdn⟩, ⟨q, hq0, hd⟩⟩
      have hvi : v i ∈ S := Submodule.subset_span (Set.mem_range_self i)
      let a := (q : F[X]).leadingCoeff / (v i : F[X]).leadingCoeff
      have hvlc : (v i : F[X]).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (hv0 i)
      have ha : a ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hq0) hvlc
      let r := q - a • v i
      have hhead : a • v i ∈ S := S.smul_mem a hvi
      have hr : r ∈ S := by
        by_cases hr0 : (r : F[X]) = 0
        · rw [show r = 0 from Subtype.ext hr0]
          exact S.zero_mem
        have htail : (r : F[X]).degree < (d : WithBot ℕ) := by
          change ((q : F[X]) - a • (v i : F[X])).degree < _
          rw [← C_mul']
          have hd' : (q : F[X]).degree = (C a * (v i : F[X])).degree := by
            rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr ha),
              degree_eq_natDegree hq0, degree_eq_natDegree (hv0 i), hd, hvd]
          have hlc : (q : F[X]).leadingCoeff = (C a * (v i : F[X])).leadingCoeff := by
            rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr ha)]
            exact (div_mul_cancel₀ _ hvlc).symm
          simpa only [degree_eq_natDegree hq0, hd] using degree_sub_lt_left hd' hq0 hlc
        exact ih (r : F[X]).natDegree ((natDegree_lt_iff_degree_lt hr0).mpr htail) (q := r) rfl
      simpa only [r, sub_add_cancel] using S.add_mem hr hhead
  let b : Module.Basis D F W := Module.Basis.mk hli hspan
  let e : D ≃ Fin (Module.finrank F W) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  refine ⟨b.reindex e, ?_, ?_⟩
  · intro i
    simpa only [Module.Basis.reindex_apply, b, Module.Basis.mk_apply] using hv0 (e.symm i)
  · intro i j hij
    apply e.symm.injective
    apply hvdeg
    simpa only [Module.Basis.reindex_apply, b, Module.Basis.mk_apply] using hij

end WronskianBasis

namespace ResidualReconstruction

/-- All values of a bounded polynomial space can be reconstructed from as
many symbolic Taylor coefficients as the dimension of that space. -/
theorem at_node {F L : Type*} [Field F] [Field L] {p : ℕ} [CharP F p]
    (W : Submodule F F[X]) (bound : W ≤ degreeLT F p)
    (φ : F[X] →+* L) (injective : Function.Injective φ) :
    ∃ A : F → Fin (Module.finrank F W) → L, ∀ (x : F) (Q : W),
      (∑ i, A x i * φ (hasseDeriv i (Q : F[X]))) = φ (C ((Q : F[X]).eval x)) := by
  obtain ⟨b,nonzero,distinct⟩ := WronskianBasis.exists_basis_distinct_natDegree W bound
  let P (i : Fin (Module.finrank F W)) := (b i : F[X])
  have hp (i : Fin (Module.finrank F W)) : (P i).natDegree < p :=
    (natDegree_lt_iff_degree_lt (nonzero i)).mpr (mem_degreeLT.mp (bound (b i).property))
  obtain ⟨A,hA⟩ := WronskianLeading.reconstruct P nonzero hp distinct φ injective
  refine ⟨A,?_⟩
  intro x Q
  have hp : (∑ i, C (b.repr Q i) * P i) = (Q : F[X]) := by
    have he := congrArg W.subtype (b.sum_repr Q)
    simpa only [P,map_sum,map_smul,Submodule.subtype_apply,smul_eq_C_mul] using he
  simpa only [hp] using hA x (fun i => b.repr Q i)

#print axioms at_node
end ResidualReconstruction
