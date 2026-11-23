import ProximityPrize.SubmissionLower.R6960LineEulerCharts
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option Elab.async false
set_option maxHeartbeats 4300000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.LineEuler
noncomputable section
open LaurentPolynomial Polynomial Module
open scoped Polynomial BigOperators

variable {k ι : Type*} [Field k]

/-- An invertible Laurent polynomial is a nonzero scalar times exactly
one integral power of the Laurent variable. -/
theorem unit_monomial (f : Laurent k) (h : IsUnit f) :
    ∃ (c : k) (j : ℤ),c≠0 ∧ f=LaurentPolynomial.C c*T j := by
  obtain ⟨u,rfl⟩ := h
  obtain ⟨n,a,ea⟩ := LaurentPolynomial.exists_T_pow (u:Laurent k)
  obtain ⟨m,b,eb⟩ := LaurentPolynomial.exists_T_pow (↑u⁻¹:Laurent k)
  have product : a*b=(Polynomial.X : k[X])^(n+m) := by
    apply Polynomial.toLaurent_injective
    rw [map_mul,ea,eb,Polynomial.toLaurent_X_pow]
    rw [mul_mul_mul_comm,Units.mul_inv,one_mul,←T_add]
    push_cast
    rfl
  obtain ⟨j,_,h⟩ := (dvd_prime_pow (Polynomial.prime_X (R:=k)) (n+m)).mp (show a∣_ from ⟨b,product.symm⟩)
  obtain ⟨v,hv⟩ := h.symm
  let c := (v:k[X]).coeff 0
  have vC : (v:k[X])=Polynomial.C c := eq_C_of_natDegree_eq_zero (natDegree_coe_units v)
  have cn : c≠0 := by
    intro z
    exact v.ne_zero (by rw [vC,z,map_zero])
  have aa : a=(Polynomial.X : k[X])^j*Polynomial.C c := by
    rw [vC] at hv
    exact hv.symm
  refine ⟨c,(j:ℤ)-n,cn,?_⟩
  have shifted : (u:Laurent k)*T (n:ℤ)=LaurentPolynomial.C c*T (j:ℤ) := by
    rw [←ea,aa,map_mul,Polynomial.toLaurent_X_pow,Polynomial.toLaurent_C,mul_comm]
  calc
    (u:Laurent k) = ((u:Laurent k)*T (n:ℤ))*T (-(n:ℤ)) := by
      rw [mul_assoc,←T_add,add_neg_cancel,T_zero,mul_one]
    _ = LaurentPolynomial.C c*T ((j:ℤ)-n) := by rw [shifted,mul_assoc,T_sub]

variable [Fintype ι]

/-- A single shift clears the abscissa end of every matrix entry and
expresses the transition as a polynomial matrix on the infinity chart. -/
theorem clear_transition (G : Matrix ι ι (Laurent k)) :
    ∃ (N : ℕ) (A : Matrix ι ι k[X]), G=(T (R:=k) (N:ℤ)) • A.map (infinityEmbedding (k:=k)) := by
  classical
  let N := Finset.univ.sup fun i : ι=>Finset.univ.sup fun j : ι=>(G i j).coeff.support.sup Int.toNat
  have bound (i j : ι) {m : ℤ} (hm : m∈(G i j).coeff.support) : m≤(N:ℤ) := by
    have a := Finset.le_sup (f:=Int.toNat) hm
    have b := Finset.le_sup (f:=fun j : ι=>(G i j).coeff.support.sup Int.toNat) (Finset.mem_univ j)
    have c : (Finset.univ.sup fun j : ι=>(G i j).coeff.support.sup Int.toNat)≤N :=
      Finset.le_sup (f:=fun i : ι=>Finset.univ.sup fun j : ι=>(G i j).coeff.support.sup Int.toNat)
        (Finset.mem_univ i)
    have d := a.trans (b.trans c)
    omega
  have fit (i j : ι) : ∃ p : k[X],shiftPolynomial N p=G i j := by
    change G i j∈LinearMap.range (shiftPolynomial N)
    rw [range_shiftPolynomial]
    exact AddMonoidAlgebra.mem_supported.mpr (fun _ hm=>bound i j hm)
  choose a ha using fit
  refine ⟨N,a,?_⟩
  apply Matrix.ext
  intro i j
  exact (ha i j).symm

variable [DecidableEq ι]

/-- The infinity-chart determinant computation tracks the sign of the
transition degree. The cleared matrix loses one shifted exponent per row. -/
theorem transition_degree (G : Matrix ι ι (Laurent k)) (unit : IsUnit G)
    (N : ℕ) (A : Matrix ι ι k[X]) (clear : G=(T (R:=k) (N:ℤ)) • A.map (infinityEmbedding (k:=k))) :
    A.det≠0 ∧ ∃ d : ℤ, G.det.degree=(d:WithBot ℤ) ∧
      d=(Fintype.card ι:ℤ)*(N:ℤ)-(A.det.natDegree:ℤ) := by
  let M : ℤ := (Fintype.card ι:ℤ)*(N:ℤ)
  have unitDet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp unit
  have mapDet : (A.map (infinityEmbedding (k:=k))).det=infinityEmbedding A.det :=
    ((infinityEmbedding (k:=k)).toRingHom.map_det A).symm
  have factor : G.det = (T M : Laurent k)*infinityEmbedding A.det := by
    rw [clear,Matrix.det_smul,mapDet,LaurentPolynomial.T_pow]
  have nz : A.det≠0 := by
    intro h
    exact unitDet.ne_zero (by rw [factor,h,map_zero,mul_zero])
  obtain ⟨c,d,cn,hd⟩ := unit_monomial G.det unitDet
  have monomial : infinityEmbedding A.det=LaurentPolynomial.C c*T (d-M) := calc
    _ = (T (-M):Laurent k)*G.det := by rw [factor,←mul_assoc,←T_add,neg_add_cancel,T_zero,one_mul]
    _ = _ := by rw [hd,mul_left_comm,←T_add]; congr 2; omega
  have direct : A.det.toLaurent = LaurentPolynomial.C c*T (M-d) := by
    have eq := congrArg (invert (R:=k)) monomial
    simpa only [infinityEmbedding_apply,involutive_invert A.det.toLaurent,map_mul,invert_C,invert_T,neg_sub] using eq
  have supp : A.det.toLaurent.coeff.support={M-d} := by
    rw [direct,support_coeff_C_mul_T_of_ne_zero cn]
  have degreeMem : (A.det.natDegree:ℤ)∈A.det.toLaurent.coeff.support := by
    rw [support_coeff_toLaurent]
    exact Finset.mem_map.mpr ⟨_,natDegree_mem_support_of_nonzero nz,rfl⟩
  have deg := Finset.mem_singleton.mp (supp ▸ degreeMem)
  exact ⟨nz,d,by rw [hd,degree_C_mul_T _ _ cn],by change d=M-_; omega⟩

#print axioms unit_monomial
#print axioms transition_degree
end
end Lower6960.LineEuler
