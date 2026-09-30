import ProximityPrize.SubmissionLower.MovingSourceTripleRootInvariants6814
namespace ProximityPrize.SubmissionLower.MovingSourceTripleRootPolynomial6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open Polynomial MovingSourceTripleRootInvariants6814

def polynomialInv2 {R : Type*} [CommRing R] (P : Polynomial R) : R :=
  inv2 (P.coeff 4) (P.coeff 3) (P.coeff 2) (P.coeff 1) (P.coeff 0)
def polynomialInv3 {R : Type*} [CommRing R] (P : Polynomial R) : R :=
  inv3 (P.coeff 4) (P.coeff 3) (P.coeff 2) (P.coeff 1) (P.coeff 0)

theorem map_inv2 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : Polynomial R) :
    f (polynomialInv2 P)=polynomialInv2 (P.map f) := by
  simp [polynomialInv2,inv2,map_ofNat]
theorem map_inv3 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : Polynomial R) :
    f (polynomialInv3 P)=polynomialInv3 (P.map f) := by
  simp [polynomialInv3,inv3,map_ofNat]

theorem triple_product_invariants {R : Type*} [CommRing R] (u v t : R) :
    polynomialInv2 ((Polynomial.X-C t)^3*(C u*Polynomial.X+C v))=0 ∧
      polynomialInv3 ((Polynomial.X-C t)^3*(C u*Polynomial.X+C v))=0 := by
  have he : (Polynomial.X-C t)^3*(C u*Polynomial.X+C v)=
      C u*Polynomial.X^4+C (v-3*u*t)*Polynomial.X^3+C (3*u*t^2-3*v*t)*Polynomial.X^2+
        C (3*v*t^2-u*t^3)*Polynomial.X+C (-v*t^3) := by
    simp only [map_sub,map_mul,map_pow,map_neg,map_ofNat]
    ring
  rw [he]
  simp only [polynomialInv2,polynomialInv3,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
  norm_num only
  simp only [ite_true,ite_false,add_zero,zero_add]
  exact triple_factor_invariants u v t

theorem invariants_of_triple_root {K : Type} [Field K]
    (P : Polynomial K) (hP : P≠0) (hs : P.natDegree≤4) (t : K)
    (hroot : (Polynomial.X-C t)^3∣P) : polynomialInv2 P=0 ∧ polynomialInv3 P=0 := by
  obtain ⟨Q,hQ⟩ := hroot
  have hQne : Q≠0 := by intro hz; exact hP (by rw [hQ,hz,mul_zero])
  have hdegree := hs
  rw [hQ,natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero t)) hQne,natDegree_pow,natDegree_X_sub_C] at hdegree
  obtain ⟨u,v,hform⟩ := exists_eq_X_add_C_of_natDegree_le_one (show Q.natDegree≤1 by omega)
  rw [hQ,hform]
  exact triple_product_invariants u v t

theorem degree_four_form {R : Type*} [CommRing R] (P : Polynomial R) (h : P.natDegree≤4) :
    P=C (P.coeff 4)*Polynomial.X^4+C (P.coeff 3)*Polynomial.X^3+C (P.coeff 2)*Polynomial.X^2+
      C (P.coeff 1)*Polynomial.X+C (P.coeff 0) := by
  have hh := P.as_sum_range_C_mul_X_pow' (show P.natDegree<5 by omega)
  conv_lhs => rw [hh]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]
  ring

theorem root_of_small_degree_invariants {K : Type} [Field K]
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    (P : Polynomial K) (hP : P≠0) (hs : P.natDegree=3 ∨ P.natDegree=4)
    (hI : polynomialInv2 P=0) (hJ : polynomialInv3 P=0) : ∃ t : K, P.eval t=0 := by
  have hform := degree_four_form P (by omega)
  rcases hs with hs | hs
  · have hb : P.coeff 3≠0 := by
      rw [←hs]
      exact leadingCoeff_ne_zero.mpr hP
    have ha : P.coeff 4=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hJ' : inv3 0 (P.coeff 3) (P.coeff 2) (P.coeff 1) (P.coeff 0)=0 := by
      simpa only [polynomialInv3,ha] using hJ
    obtain ⟨t,ht⟩ := cubic_has_root_of_inv3 h3 _ _ _ _ hb hJ'
    refine ⟨t,?_⟩
    conv_lhs => rw [hform]
    simpa only [eval_add,eval_mul,eval_pow,eval_C,eval_X,ha,zero_mul,zero_add] using ht
  · have ha : P.coeff 4≠0 := by
      rw [←hs]
      exact leadingCoeff_ne_zero.mpr hP
    obtain ⟨t,ht⟩ := quartic_has_root_of_invariants h2 h3 _ _ _ _ _ ha hI hJ
    refine ⟨t,?_⟩
    conv_lhs => rw [hform]
    simpa only [eval_add,eval_mul,eval_pow,eval_C,eval_X] using ht

theorem irreducible_small_invariants_not_both_zero {K : Type} [Field K]
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    (P : Polynomial K) (hP : Irreducible P) (hs : P.natDegree=3 ∨ P.natDegree=4) :
    ¬(polynomialInv2 P=0 ∧ polynomialInv3 P=0) := by
  rintro ⟨hi,hj⟩
  obtain ⟨t,ht⟩ := root_of_small_degree_invariants h2 h3 P hP.ne_zero hs hi hj
  have ha := (irreducible_X_sub_C t).associated_of_dvd hP (dvd_iff_isRoot.mpr ht)
  have hd := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ha)
  rw [natDegree_X_sub_C] at hd
  omega

end
end ProximityPrize.SubmissionLower.MovingSourceTripleRootPolynomial6814
