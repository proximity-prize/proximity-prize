import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagKernelDerivativeVanish6750Research

 







namespace ProximityPrize.SubmissionLower
namespace ContactIteratedFlagKernelDerivativeVanish6750Research

open scoped Classical
open ProximityPrize.Benchmark
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactFlagTranslation6641Research
open ContactFlagKernelUniversalityResearch
open ContactFlagKernelDerivativeContact6750Research
open ContactIteratedDerivativeDegree6700Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

variable {K : Type*} [Field K]

 


theorem iterate_derivative_translated_contact
    (F : MvPolynomial (Fin 4) K) (x u0 u1 : K) (m q : Nat)
    (hcontact : ∀ r : Nat,
      slopeDifference K ^ (m - r) ∣
        (homogenizedTranslation K x u0 u1 F).coeff r) :
    ∀ r : Nat, slopeDifference K ^ (m - q - r) ∣
      (homogenizedTranslation K x u0 u1
        ((MvPolynomial.pderiv (2 : Fin 4))^[q] F)).coeff r := by
  induction q with
  | zero => simpa using hcontact
  | succ q ih =>
      intro r
      rw [Function.iterate_succ_apply']
      have h := derivative_translated_contact
        ((MvPolynomial.pderiv (2 : Fin 4))^[q] F) x u0 u1 (m - q) ih r
      have hexp : m - (q + 1) - r = m - q - 1 - r := by omega
      simpa only [hexp] using h

 






theorem specialization_iterate_pderiv_R_eq_zero_of_high_kernel_and_low_box
    [DecidableEq K] {I : Type*} [Fintype I] [DecidableEq I]
    (Dcontact Ddegree w L s m q : Nat)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (theta : CoefficientIndex Dcontact w L s → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K Dcontact w L s m nodes u0 u1))
    (hlow : reconstruct K Dcontact w L s theta ∈
      ContactInterpolation.globalCoefficientBox K Ddegree w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hweight : q * (w - 1) < Ddegree)
    (hP : P.natDegree ≤ w)
    (hcapacity : Ddegree ≤
      (m - q) * support.card + q * (w - 1))
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    ContactTranslation.specialization K P gamma
      ((MvPolynomial.pderiv (2 : Fin 4))^[q]
        (reconstruct K Dcontact w L s theta)) = 0 := by
  let F := reconstruct K Dcontact w L s theta
  have hcontact : ∀ i ∈ support, ∀ r : Nat,
      slopeDifference K ^ (m - q - r) ∣
        (homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          ((MvPolynomial.pderiv (2 : Fin 4))^[q] F)).coeff r := by
    intro i hi
    apply iterate_derivative_translated_contact F
      (nodes i) (u0 i) (u1 i) m q
    exact translated_contact_of_mem_ker K Dcontact w L s m
      nodes u0 u1 theta htheta i
  have hdegreeAdd := specialization_iterate_pderiv_R_natDegree_add_lt
    (K := K) Ddegree w L s q F P gamma hweight hlow hP
  have hdegree :
      (ContactFlagTranslation6641Research.specialization K P gamma
        ((MvPolynomial.pderiv (2 : Fin 4))^[q] F)).natDegree <
          (m - q) * support.card := by
    have hdegreeOrdinary :
        (ContactTranslation.specialization K P gamma
          ((MvPolynomial.pderiv (2 : Fin 4))^[q] F)).natDegree +
            q * (w - 1) < Ddegree := by
      exact hdegreeAdd
    rw [specialization_eq_ordinary]
    omega
  have hzero :
      ContactFlagTranslation6641Research.specialization K P gamma
        ((MvPolynomial.pderiv (2 : Fin 4))^[q] F) = 0 := by
    apply specialization_eq_zero_of_contact_and_degree K
      ((MvPolynomial.pderiv (2 : Fin 4))^[q] F) P gamma nodes u0 u1
        support (m - q)
    · exact hcontact
    · exact hvalues
    · exact hdegree
  simpa only [F, specialization_eq_ordinary] using hzero

end

end ContactIteratedFlagKernelDerivativeVanish6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactIteratedFlagKernelDerivativeVanish6750Research.iterate_derivative_translated_contact
#print axioms ProximityPrize.SubmissionLower.ContactIteratedFlagKernelDerivativeVanish6750Research.specialization_iterate_pderiv_R_eq_zero_of_high_kernel_and_low_box
