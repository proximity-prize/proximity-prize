import ProximityPrize.SubmissionLower.R6960LineEulerTransition

set_option Elab.async false
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.Horner
noncomputable section
open Polynomial LaurentPolynomial
open LineEuler (Laurent infinityEmbedding)
open scoped Polynomial BigOperators

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem prod_T (s : Finset ι) (n : ι→ℤ) :
    (∏ i∈s,(T (n i):Laurent k))=T (∑ i∈s,n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj,Finset.sum_insert hj,ih,T_add]

private theorem coeff_C_product (c : k) (p : Laurent k) (i : ℤ) :
    (LaurentPolynomial.C c*p).coeff i=c*p.coeff i := by
  rw [←single_eq_C,AddMonoidAlgebra.coeff_single_zero_mul]

/-- Columns of finite sections, after individual pole clearings on the
reciprocal chart, bound the determinant deficit by the sum of their pole
orders. This uses the actual determinant, not a bound on individual entries. -/
theorem determinant_budget (G : Matrix ι ι (Laurent k)) (unit : IsUnit G)
    (P Q : Matrix ι ι k[X]) (width : ι→ℕ) (independent : P.det≠0)
    (join : P.map (Polynomial.toLaurent (R:=k)) = G * (Q.map (infinityEmbedding (k:=k))) *
      Matrix.diagonal (fun i=>T (R:=k) (width i : ℤ))) :
    ∃ d : ℤ, G.det.degree=(d:WithBot ℤ) ∧ -d≤∑ i,(width i : ℤ) := by
  let D : ℤ := ∑ i,(width i : ℤ)
  obtain ⟨c,d,cn,dc⟩ := LineEuler.unit_monomial G.det ((Matrix.isUnit_iff_isUnit_det G).mp unit)
  have lhs : (P.map (Polynomial.toLaurent (R:=k))).det=P.det.toLaurent :=
    (RingHom.map_det (Polynomial.toLaurent (R:=k)) P).symm
  have rhs : (Q.map (infinityEmbedding (k:=k))).det=infinityEmbedding Q.det :=
    ((infinityEmbedding (k:=k)).toRingHom.map_det Q).symm
  have det := congrArg Matrix.det join
  rw [lhs,Matrix.det_mul,Matrix.det_mul,rhs,Matrix.det_diagonal,prod_T,dc] at det
  have eq : P.det.toLaurent=LaurentPolynomial.C c*(T (d+D)*infinityEmbedding Q.det) := calc
    _ = (LaurentPolynomial.C c*T d)*infinityEmbedding Q.det*T D := det
    _ = _ := by rw [T_add]; ring
  let n : ℤ := P.det.natDegree
  have coeff : P.det.toLaurent.coeff n≠0 := Finsupp.mem_support_iff.mp (by
    rw [support_coeff_toLaurent]
    exact Finset.mem_map.mpr ⟨_,natDegree_mem_support_of_nonzero independent,rfl⟩)
  have bounded : infinityEmbedding Q.det∈AddMonoidAlgebra.supported k k (Set.Iic (0:ℤ)) := by
    change infinityEmbedding Q.det∈AddMonoidAlgebra.supported k k (Set.Iic ((0:ℕ):ℤ))
    rw [←LineEuler.range_shiftPolynomial 0]
    exact ⟨Q.det,by rw [LineEuler.shiftPolynomial_apply,Nat.cast_zero,T_zero,one_mul]⟩
  refine ⟨d,by rw [dc,degree_C_mul_T _ _ cn],?_⟩
  change -d≤D
  by_contra bad
  have near : ¬n-(d+D)∈Set.Iic (0:ℤ) := by
    change ¬n-(d+D)≤0
    have nn : 0≤n := Int.natCast_nonneg _
    omega
  have outside := AddMonoidAlgebra.mem_supported'.mp bounded _ near
  rw [eq,coeff_C_product,LineEuler.coeff_shift,outside,mul_zero] at coeff
  exact coeff rfl

#print axioms determinant_budget
end
end Lower6960.Horner
