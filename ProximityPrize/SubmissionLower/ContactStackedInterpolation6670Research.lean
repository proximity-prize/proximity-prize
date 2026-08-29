import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagKernelUniversalityResearch
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research

/-! .




 -/

namespace ProximityPrize.SubmissionLower.ContactStackedInterpolation6670Research

open ProximityPrize.Benchmark
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactTranslation
open ContactFlagKernelUniversalityResearch
open ContactStackedParameters6670Research

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

/-- .
 -/
theorem exists_stacked_universal_vanishing_interpolants
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ QA QB QC : MvPolynomial (Fin 4) IRSProfile.Field,
      QA ≠ 0 ∧
      QA ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        (34 * agreements) w 20000 10 ∧
      QB ≠ 0 ∧
      QB ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        (68 * agreements) w 900 21 ∧
      QC ≠ 0 ∧
      QC ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        (37 * agreements) w 42000 9 ∧
      QB ∈ ContactFlagInterpolation6641Research.globalCoefficientBox IRSProfile.Field
        (68 * agreements) w 900 21 ∧
      ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support,
          P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        specialization IRSProfile.Field P gamma QA = 0 ∧
        specialization IRSProfile.Field P gamma QB = 0 ∧
        specialization IRSProfile.Field P gamma QC = 0 := by
  have hgateA : Fintype.card IRSProfile.Index * localRankBound 34 20000 10 <
      coefficientCount (34 * agreements) w 20000 10 := by
    rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change profileA.totalRank < profileA.coefficients
    exact interpolation_gates.1
  have hgateB : Fintype.card IRSProfile.Index * localRankBound 68 900 21 <
      coefficientCount (68 * agreements) w 900 21 := by
    rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change profileB.totalRank < profileB.coefficients
    exact interpolation_gates.2.1
  have hgateC : Fintype.card IRSProfile.Index * localRankBound 37 42000 9 <
      coefficientCount (37 * agreements) w 42000 9 := by
    rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change profileC.totalRank < profileC.coefficients
    exact interpolation_gates.2.2
  obtain ⟨thetaA, hthetaA, hkernelA⟩ := exists_nonzero_kernel_array
    IRSProfile.Field (34 * agreements) w 20000 10 34
      IRSProfile.domain u0 u1 hgateA
  obtain ⟨thetaB, hthetaB, hkernelB⟩ := exists_nonzero_kernel_array
    IRSProfile.Field (68 * agreements) w 900 21 68
      IRSProfile.domain u0 u1 hgateB
  obtain ⟨thetaC, hthetaC, hkernelC⟩ := exists_nonzero_kernel_array
    IRSProfile.Field (37 * agreements) w 42000 9 37
      IRSProfile.domain u0 u1 hgateC
  have hDA : 0 < 34 * agreements := by norm_num [agreements]
  have hDB : 0 < 68 * agreements := by norm_num [agreements]
  have hDC : 0 < 37 * agreements := by norm_num [agreements]
  have hA := nonzero_kernel_member_universal IRSProfile.Field
    (34 * agreements) w 20000 10 34 agreements IRSProfile.domain u0 u1 thetaA
    hthetaA (LinearMap.mem_ker.mpr hkernelA) hDA rfl
  have hB := nonzero_kernel_member_universal IRSProfile.Field
    (68 * agreements) w 900 21 68 agreements IRSProfile.domain u0 u1 thetaB
    hthetaB (LinearMap.mem_ker.mpr hkernelB) hDB rfl
  have hC := nonzero_kernel_member_universal IRSProfile.Field
    (37 * agreements) w 42000 9 37 agreements IRSProfile.domain u0 u1 thetaC
    hthetaC (LinearMap.mem_ker.mpr hkernelC) hDC rfl
  have hOrdA := flag_box_to_ordinary IRSProfile.Field
    (34 * agreements) w 20000 10 _ hA.2.1
  have hOrdB := flag_box_to_ordinary IRSProfile.Field
    (68 * agreements) w 900 21 _ hB.2.1
  have hOrdC := flag_box_to_ordinary IRSProfile.Field
    (37 * agreements) w 42000 9 _ hC.2.1
  refine ⟨reconstruct IRSProfile.Field (34 * agreements) w 20000 10 thetaA,
    reconstruct IRSProfile.Field (68 * agreements) w 900 21 thetaB,
    reconstruct IRSProfile.Field (37 * agreements) w 42000 9 thetaC,
    hA.1, hOrdA, hB.1, hOrdB, hC.1, hOrdC, hB.2.1, ?_⟩
  intro gamma P support hP hcard hvalues
  exact ⟨hA.2.2 gamma P support hP hcard hvalues,
    hB.2.2 gamma P support hP hcard hvalues,
    hC.2.2 gamma P support hP hcard hvalues⟩

end

end ProximityPrize.SubmissionLower.ContactStackedInterpolation6670Research
