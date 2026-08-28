import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactKernelMemberUniversality
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research

/-!
# Three universal contact interpolants at the 66.70 row

This is the target-specific instantiation of the generic contact-kernel
universality theorem at `a = 182668`.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedInterpolation6670Research

open ProximityPrize.Benchmark
open ContactInterpolation ContactRankKernel ContactTranslation
open ContactKernelMemberUniversality
open ContactStackedParameters6670Research

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

/-- Three nonzero boxed kernel members with their shared universal
specialization property. -/
theorem exists_stacked_universal_vanishing_interpolants
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ QA QB QC : MvPolynomial (Fin 4) IRSProfile.Field,
      QA ≠ 0 ∧
      QA ∈ globalCoefficientBox IRSProfile.Field
        (27 * agreements) w 11937 7 ∧
      QB ≠ 0 ∧
      QB ∈ globalCoefficientBox IRSProfile.Field
        (34 * agreements) w 1059 9 ∧
      QC ≠ 0 ∧
      QC ∈ globalCoefficientBox IRSProfile.Field
        (54 * agreements) w 690 16 ∧
      ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support,
          P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        specialization IRSProfile.Field P gamma QA = 0 ∧
        specialization IRSProfile.Field P gamma QB = 0 ∧
        specialization IRSProfile.Field P gamma QC = 0 := by
  have hgateA : Fintype.card IRSProfile.Index * localRankBound 27 11937 7 <
      coefficientCount (27 * agreements) w 11937 7 := by
    rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change profileA.totalRank < profileA.coefficients
    exact interpolation_gates.1
  have hgateB : Fintype.card IRSProfile.Index * localRankBound 34 1059 9 <
      coefficientCount (34 * agreements) w 1059 9 := by
    rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change profileB.totalRank < profileB.coefficients
    exact interpolation_gates.2.1
  have hgateC : Fintype.card IRSProfile.Index * localRankBound 54 690 16 <
      coefficientCount (54 * agreements) w 690 16 := by
    rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change profileC.totalRank < profileC.coefficients
    exact interpolation_gates.2.2
  obtain ⟨thetaA, hthetaA, hkernelA⟩ := exists_nonzero_kernel_array
    IRSProfile.Field (27 * agreements) w 11937 7 27
      IRSProfile.domain u0 u1 hgateA
  obtain ⟨thetaB, hthetaB, hkernelB⟩ := exists_nonzero_kernel_array
    IRSProfile.Field (34 * agreements) w 1059 9 34
      IRSProfile.domain u0 u1 hgateB
  obtain ⟨thetaC, hthetaC, hkernelC⟩ := exists_nonzero_kernel_array
    IRSProfile.Field (54 * agreements) w 690 16 54
      IRSProfile.domain u0 u1 hgateC
  have hDA : 0 < 27 * agreements := by norm_num [agreements]
  have hDB : 0 < 34 * agreements := by norm_num [agreements]
  have hDC : 0 < 54 * agreements := by norm_num [agreements]
  have hA := nonzero_kernel_member_universal IRSProfile.Field
    (27 * agreements) w 11937 7 27 agreements IRSProfile.domain u0 u1 thetaA
    hthetaA (LinearMap.mem_ker.mpr hkernelA) hDA rfl
  have hB := nonzero_kernel_member_universal IRSProfile.Field
    (34 * agreements) w 1059 9 34 agreements IRSProfile.domain u0 u1 thetaB
    hthetaB (LinearMap.mem_ker.mpr hkernelB) hDB rfl
  have hC := nonzero_kernel_member_universal IRSProfile.Field
    (54 * agreements) w 690 16 54 agreements IRSProfile.domain u0 u1 thetaC
    hthetaC (LinearMap.mem_ker.mpr hkernelC) hDC rfl
  refine ⟨reconstruct IRSProfile.Field (27 * agreements) w 11937 7 thetaA,
    reconstruct IRSProfile.Field (34 * agreements) w 1059 9 thetaB,
    reconstruct IRSProfile.Field (54 * agreements) w 690 16 thetaC,
    hA.1, hA.2.1, hB.1, hB.2.1, hC.1, hC.2.1, ?_⟩
  intro gamma P support hP hcard hvalues
  exact ⟨hA.2.2 gamma P support hP hcard hvalues,
    hB.2.2 gamma P support hP hcard hvalues,
    hC.2.2 gamma P support hP hcard hvalues⟩

end

end ProximityPrize.SubmissionLower.ContactStackedInterpolation6670Research

#print axioms ProximityPrize.SubmissionLower.ContactStackedInterpolation6670Research.exists_stacked_universal_vanishing_interpolants
