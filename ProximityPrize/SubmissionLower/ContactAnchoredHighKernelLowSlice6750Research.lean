import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredActualNullity6750Research
import ProximityPrize.SubmissionLower.ContactFixedFactorQuotientLinear6750Research
import ProximityPrize.SubmissionLower.ContactFixedOrdinaryQuotientExistence6750Research
import ProximityPrize.SubmissionLower.ContactNestedFiveCapSlab6750Research
import ProximityPrize.SubmissionLower.ContactNestedFiveCapQuotientSupport6750Research
import ProximityPrize.SubmissionLower.ContactFlagKernelDerivativeVanish6750Research

 














namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredHighKernelLowSlice6750Research

open scoped Classical BigOperators
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactFlagKernelUniversalityResearch
open ContactFlagKernelDerivativeContact6750Research
open ContactIteratedDerivativeDegree6700Research
open ContactAnchoredOneFamilySelector6750Research
open ContactFixedFactorQuotientLinear6750Research
open ContactFixedOrdinaryQuotientExistence6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactNestedFiveCapSlab6750Research
open ContactNestedFiveCapQuotientSupport6750Research
open ContactFactorCaps
open ContactIdentityResidualGlobalFlagResearch
open ContactFlagTranslation6641Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000

universe u v

variable {K : Type u} [Field K]

abbrev Poly4 (K : Type u) [Field K] := MvPolynomial (Fin 4) K

 

 

theorem nestedFiveCap_lowInsideHigh_finrank_eq
    {Dlow Dhigh w T YS S : Nat} (hD : Dlow ≤ Dhigh) :
    Module.finrank K
        (lowInsideHigh (nestedFiveCapCoefficientBox K Dhigh w T YS S)
          (nestedFiveCapCoefficientBox K Dlow w T YS S)) =
      Module.finrank K (nestedFiveCapCoefficientBox K Dlow w T YS S) := by
  let High := nestedFiveCapCoefficientBox K Dhigh w T YS S
  let Low := nestedFiveCapCoefficientBox K Dlow w T YS S
  have hle : Low ≤ High := nestedFiveCapCoefficientBox_mono_D K hD
  calc
    Module.finrank K (lowInsideHigh High Low) =
        Module.finrank K ((lowInsideHigh High Low).map High.subtype) :=
      (Submodule.equivSubtypeMap High (lowInsideHigh High Low)).finrank_eq
    _ = Module.finrank K Low := by
      rw [lowInsideHigh, Submodule.map_comap_subtype]
      exact congrArg (fun W : Submodule K (Poly4 K) => Module.finrank K W)
        (inf_eq_right.mpr hle)

 
theorem nestedFiveCap_quotient_finrank_eq_count_sub
    {Dlow Dhigh w T YS S : Nat} (hD : Dlow ≤ Dhigh) :
    Module.finrank K
        (nestedFiveCapCoefficientBox K Dhigh w T YS S ⧸
          lowInsideHigh (nestedFiveCapCoefficientBox K Dhigh w T YS S)
            (nestedFiveCapCoefficientBox K Dlow w T YS S)) =
      nestedFiveCapCoefficientCount Dhigh w T YS S -
        nestedFiveCapCoefficientCount Dlow w T YS S := by
  letI : FiniteDimensional K
      (nestedFiveCapCoefficientBox K Dhigh w T YS S) :=
    nestedFiveCapCoefficientBox_finiteDimensional K Dhigh w T YS S
  rw [Submodule.finrank_quotient]
  rw [nestedFiveCapCoefficientBox_finrank_eq_count]
  rw [nestedFiveCap_lowInsideHigh_finrank_eq hD]
  rw [nestedFiveCapCoefficientBox_finrank_eq_count]

 

 






theorem exists_nonzero_source_with_low_factor_quotient
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Dlow Dhigh w T YS S c t y s : Nat}
    (hD : Dlow ≤ Dhigh) (hc : c ≤ Dlow)
    (f : V →ₗ[K] Poly4 K) (hf : Function.Injective f)
    (H : Poly4 K) (hH : H ≠ 0)
    (hdiv : ∀ v : V, H ∣ f v)
    (hparent : ∀ v : V,
      f v ∈ nestedFiveCapCoefficientBox K Dhigh w T YS S)
    (hHc : MvPolynomial.weightedTotalDegree (contactWeights w) H = c)
    (hHt : MvPolynomial.weightedTotalDegree residualTotalWeights H = t)
    (hHy : MvPolynomial.weightedTotalDegree residualYSWeights H = y)
    (hHs : MvPolynomial.weightedTotalDegree residualSWeights H = s)
    (hwidth : ∀ i r,
      i < min (T - t) (YS - y) + 1 →
      r < min (S - s) (min ((T - t) - i) ((YS - y) - i)) + 1 →
      w * i + (w - 1) * r < Dlow - c)
    (hgap : (Dhigh - Dlow) *
      nestedFiveCapChannelCount (T - t) (YS - y) (S - s) <
        Module.finrank K V) :
    ∃ v : V, v ≠ 0 ∧
      mappedFixedFactorQuotientLinearMap H hH f hdiv v ≠ 0 ∧
      H * mappedFixedFactorQuotientLinearMap H hH f hdiv v = f v ∧
      mappedFixedFactorQuotientLinearMap H hH f hdiv v ∈
        nestedFiveCapCoefficientBox K (Dlow - c) w
          (T - t) (YS - y) (S - s) := by
  classical
  let qLin := mappedFixedFactorQuotientLinearMap H hH f hdiv
  let QHigh := nestedFiveCapCoefficientBox K (Dhigh - c) w
    (T - t) (YS - y) (S - s)
  let QLow := nestedFiveCapCoefficientBox K (Dlow - c) w
    (T - t) (YS - y) (S - s)
  have hQc : Dlow - c ≤ Dhigh - c := Nat.sub_le_sub_right hD c
  have hqimage : ∀ v : V, qLin v ∈ QHigh := by
    intro v
    rcases Classical.em (v = 0) with hv | hv
    · subst v
      change qLin (0 : V) ∈ QHigh
      rw [map_zero]
      exact QHigh.zero_mem
    · have hqv : qLin v ≠ 0 :=
        mappedFixedFactorQuotientLinearMap_ne_zero H hH f hdiv hf hv
      apply quotient_mem_nestedFiveCapCoefficientBox_of_mul_eq
        hH hqv (mul_mappedFixedFactorQuotientLinearMap H hH f hdiv v)
          (hparent v) hHc hHt hHy hHs
  have hqinj : Function.Injective qLin :=
    mappedFixedFactorQuotientLinearMap_injective H hH f hdiv hf
  letI : FiniteDimensional K QHigh :=
    nestedFiveCapCoefficientBox_finiteDimensional K
      (Dhigh - c) w (T - t) (YS - y) (S - s)
  have hcodim : Module.finrank K (QHigh ⧸ lowInsideHigh QHigh QLow) ≤
      (Dhigh - Dlow) *
        nestedFiveCapChannelCount (T - t) (YS - y) (S - s) := by
    rw [nestedFiveCap_quotient_finrank_eq_count_sub hQc]
    rw [nestedFiveCapCoefficientCount_sub_eq_slab hQc hwidth]
    have hsub : (Dhigh - c) - (Dlow - c) = Dhigh - Dlow := by omega
    rw [hsub]
  obtain ⟨v, hv, hqv, hlow⟩ :=
    exists_ne_zero_map_mem_low_of_nested_codim_cap
      qLin QHigh QLow hqimage hqinj
      ((Dhigh - Dlow) *
        nestedFiveCapChannelCount (T - t) (YS - y) (S - s))
      hcodim hgap
  exact ⟨v, hv, hqv,
    mul_mappedFixedFactorQuotientLinearMap H hH f hdiv v, hlow⟩

 

 


theorem reconstruct_mem_m61_high_fiveCap
    (L : Nat) (theta : CoefficientIndex 11458062 131071 L 18 → K) :
    reconstruct K 11458062 131071 L 18 theta ∈
      nestedFiveCapCoefficientBox K 11458062 131071 L 87 18 := by
  have hbox := reconstruct_mem_globalCoefficientBox K
    11458062 131071 L 18 theta
  intro d hd
  have h := hbox hd
  refine ⟨h.1, ?_, h.2.1, h.2.2⟩
  have hweight := h.2.2
  norm_num at hweight ⊢
  omega

 

theorem constraintKernel_finrank_ge_rank_bound
    {I : Type*} [Fintype I]
    (D w L s m : Nat) (nodes u0 u1 : I → K) :
    coefficientCount D w L s -
        Fintype.card I * localRankBound m L s ≤
      Module.finrank K
        (LinearMap.ker (constraintMap K D w L s m nodes u0 u1)) := by
  classical
  have hrange : Module.finrank K (LinearMap.range
      (constraintMap K D w L s m nodes u0 u1)) ≤
      Fintype.card I * localRankBound m L s := by
    calc
      Module.finrank K (LinearMap.range
          (constraintMap K D w L s m nodes u0 u1)) ≤
          Module.finrank K (GlobalTarget K I m L s) :=
        Submodule.finrank_le _
      _ ≤ Fintype.card I * localRankBound m L s :=
        globalTarget_finrank_le K m L s
  have hsum :=
    (constraintMap K D w L s m nodes u0 u1).finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card, coefficient_index_card] at hsum
  apply Nat.sub_le_iff_le_add.mpr
  omega

theorem m61_high_constraintKernel_finrank_ge_actualNullity
    {I : Type*} [Fintype I]
    (L : Nat) (nodes u0 u1 : I → K)
    (hcard : Fintype.card I = domainSize) :
    actualNullity L ≤ Module.finrank K
      (LinearMap.ker
        (constraintMap K 11458062 131071 L 18 63 nodes u0 u1)) := by
  have h := constraintKernel_finrank_ge_rank_bound (K := K)
    11458062 131071 L 18 63 nodes u0 u1
  rw [hcard] at h
  simpa only [actualNullity, familyMultiplicity, agreements, contactSlope,
    familySlopeCap] using h

 

theorem specialization_eq_zero_of_mem_m61_high_kernel
    [DecidableEq K] {I : Type*} [Fintype I] [DecidableEq I]
    (L : Nat) (nodes : I ↪ K) (u0 u1 : I → K)
    (theta : CoefficientIndex 11458062 131071 L 18 → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K 11458062 131071 L 18 63 nodes u0 u1))
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hP : P.natDegree ≤ 131071)
    (hcard : 181874 ≤ support.card)
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    ContactTranslation.specialization K P gamma
      (reconstruct K 11458062 131071 L 18 theta) = 0 := by
  have hflag := specialization_eq_zero_of_agreements K
    11458062 131071 L 18 63 181874 nodes u0 u1 theta htheta
      (by norm_num) (by norm_num) P gamma support hP hcard hvalues
  simpa only [specialization_eq_ordinary] using hflag

 


theorem specialization_pderiv_R_eq_zero_of_high_kernel_and_low_box
    [DecidableEq K] {I : Type*} [Fintype I] [DecidableEq I]
    (Dcontact Ddegree w L s m : Nat)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (theta : CoefficientIndex Dcontact w L s → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K Dcontact w L s m nodes u0 u1))
    (hlow : reconstruct K Dcontact w L s theta ∈
      ContactInterpolation.globalCoefficientBox K Ddegree w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hweight : w - 1 < Ddegree)
    (hP : P.natDegree ≤ w)
    (hcapacity : Ddegree ≤ (m - 1) * support.card + (w - 1))
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    ContactTranslation.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (reconstruct K Dcontact w L s theta)) = 0 := by
  let F := reconstruct K Dcontact w L s theta
  have hcontact : ∀ i ∈ support, ∀ r : Nat,
      slopeDifference K ^ (m - 1 - r) ∣
        (homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4) F)).coeff r := by
    intro i hi
    apply derivative_translated_contact F (nodes i) (u0 i) (u1 i) m
    exact translated_contact_of_mem_ker K Dcontact w L s m
      nodes u0 u1 theta htheta i
  have hdegreeAdd := specialization_iterate_pderiv_R_natDegree_add_lt
    (K := K) Ddegree w L s 1 F P gamma (by simpa using hweight) hlow hP
  have hdegree :
      (ContactFlagTranslation6641Research.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)).natDegree <
          (m - 1) * support.card := by
    have hdegreeOrdinary :
        (ContactTranslation.specialization K P gamma
          (MvPolynomial.pderiv (2 : Fin 4) F)).natDegree + (w - 1) <
            Ddegree := by
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

end

end ContactAnchoredHighKernelLowSlice6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighKernelLowSlice6750Research.exists_nonzero_source_with_low_factor_quotient
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighKernelLowSlice6750Research.reconstruct_mem_m61_high_fiveCap
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighKernelLowSlice6750Research.m61_high_constraintKernel_finrank_ge_actualNullity
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighKernelLowSlice6750Research.specialization_eq_zero_of_mem_m61_high_kernel
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighKernelLowSlice6750Research.specialization_pderiv_R_eq_zero_of_high_kernel_and_low_box
