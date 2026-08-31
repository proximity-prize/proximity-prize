import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagKernelDerivativeContact6750Research
import ProximityPrize.SubmissionLower.ContactIteratedDerivativeDegree6700Research

 














namespace ProximityPrize.SubmissionLower.ContactFlagKernelDerivativeVanish6750Research

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

 




theorem specialization_pderiv_R_eq_zero_of_mem_flag_kernel
    [DecidableEq K] {I : Type*} [Fintype I] [DecidableEq I]
    (D w L s m : Nat) (nodes : I ↪ K) (u0 u1 : I → K)
    (theta : CoefficientIndex D w L s → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K D w L s m nodes u0 u1))
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hweight : w - 1 < D)
    (hP : P.natDegree ≤ w)
    (hcapacity : D ≤ (m - 1) * support.card + (w - 1))
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    ContactTranslation.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (reconstruct K D w L s theta)) = 0 := by
  let F := reconstruct K D w L s theta
  have hcontact : ∀ i ∈ support, ∀ r : Nat,
      slopeDifference K ^ (m - 1 - r) ∣
        (homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4) F)).coeff r := by
    intro i hi
    apply derivative_translated_contact F (nodes i) (u0 i) (u1 i) m
    exact translated_contact_of_mem_ker K D w L s m nodes u0 u1 theta
      htheta i
  have hboxFlag : F ∈ globalCoefficientBox K D w L s :=
    reconstruct_mem_globalCoefficientBox K D w L s theta
  have hboxOrdinary :
      F ∈ ContactInterpolation.globalCoefficientBox K D w L s :=
    flag_box_to_ordinary K D w L s F hboxFlag
  have hdegreeAdd :=
    specialization_iterate_pderiv_R_natDegree_add_lt
      (K := K) D w L s 1 F P gamma (by simpa using hweight)
        hboxOrdinary hP
  have hdegree :
      (ContactFlagTranslation6641Research.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)).natDegree <
          (m - 1) * support.card := by
    have hdegreeOrdinary :
        (ContactTranslation.specialization K P gamma
          (MvPolynomial.pderiv (2 : Fin 4) F)).natDegree + (w - 1) < D := by
      simpa only [Function.iterate_one, one_mul] using hdegreeAdd
    rw [specialization_eq_ordinary]
    omega
  have hzero :
      ContactFlagTranslation6641Research.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) = 0 := by
    apply specialization_eq_zero_of_contact_and_degree K
      (MvPolynomial.pderiv (2 : Fin 4) F) P gamma nodes u0 u1 support
        (m - 1)
    · exact hcontact
    · exact hvalues
    · exact hdegree
  simpa only [F, specialization_eq_ordinary] using hzero

 






theorem specialization_pderiv_R_eq_zero_of_mem_m61_kernel
    [DecidableEq K] {I : Type*} [Fintype I] [DecidableEq I]
    (L : Nat) (nodes : I ↪ K) (u0 u1 : I → K)
    (theta : CoefficientIndex 11407258 131071 L 18 → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K 11407258 131071 L 18 63 nodes u0 u1))
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hP : P.natDegree ≤ 131071)
    (hcard : 181874 ≤ support.card)
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    ContactTranslation.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (reconstruct K 11407258 131071 L 18 theta)) = 0 := by
  apply specialization_pderiv_R_eq_zero_of_mem_flag_kernel
    11407258 131071 L 18 63 nodes u0 u1 theta htheta P gamma support
  · norm_num
  · exact hP
  · omega
  · exact hvalues

 


theorem m61_derivative_cap_identity :
    11407258 = (63 - 1) * 181874 + (131071 - 1) := by
  norm_num

end


end ProximityPrize.SubmissionLower.ContactFlagKernelDerivativeVanish6750Research

#print axioms ProximityPrize.SubmissionLower.ContactFlagKernelDerivativeVanish6750Research.specialization_pderiv_R_eq_zero_of_mem_flag_kernel
#print axioms ProximityPrize.SubmissionLower.ContactFlagKernelDerivativeVanish6750Research.specialization_pderiv_R_eq_zero_of_mem_m61_kernel
#print axioms ProximityPrize.SubmissionLower.ContactFlagKernelDerivativeVanish6750Research.m61_derivative_cap_identity
