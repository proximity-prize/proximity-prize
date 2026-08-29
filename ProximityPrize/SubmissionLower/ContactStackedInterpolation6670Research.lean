import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagKernelUniversalityResearch
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research

/-!
# Three universal contact interpolants at the 67.30 row

This is the target-specific instantiation of the generic contact-kernel
universality theorem at `a = 182078`.
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

/-- Three nonzero boxed kernel members with their shared universal
specialization property. -/
theorem exists_stacked_universal_vanishing_interpolants
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ QA QB QC : MvPolynomial (Fin 4) IRSProfile.Field,
      QA ≠ 0 ∧
      QA ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        (50 * agreements) w 25000 15 ∧
      QB ≠ 0 ∧
      QB ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        (60 * agreements) w 3100 18 ∧
      QC ≠ 0 ∧
      QC ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        (50 * agreements) w 800000 15 ∧
      QB ∈ ContactFlagInterpolation6641Research.globalCoefficientBox IRSProfile.Field
        (60 * agreements) w 3100 18 ∧
      ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support,
          P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        specialization IRSProfile.Field P gamma QA = 0 ∧
        specialization IRSProfile.Field P gamma QB = 0 ∧
        specialization IRSProfile.Field P gamma QC = 0 := by
  have hgateA : Fintype.card IRSProfile.Index * localRankBound 50 25000 15 <
      coefficientCount (50 * agreements) w 25000 15 := by
    rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change profileA.totalRank < profileA.coefficients
    exact interpolation_gates.1
  have hgateB : Fintype.card IRSProfile.Index * localRankBound 60 3100 18 <
      coefficientCount (60 * agreements) w 3100 18 := by
    rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change profileB.totalRank < profileB.coefficients
    exact interpolation_gates.2.1
  have hgateC : Fintype.card IRSProfile.Index * localRankBound 50 800000 15 <
      coefficientCount (50 * agreements) w 800000 15 := by
    rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change profileC.totalRank < profileC.coefficients
    exact interpolation_gates.2.2
  obtain ⟨thetaA, hthetaA, hkernelA⟩ := exists_nonzero_kernel_array
    IRSProfile.Field (50 * agreements) w 25000 15 50
      IRSProfile.domain u0 u1 hgateA
  obtain ⟨thetaB, hthetaB, hkernelB⟩ := exists_nonzero_kernel_array
    IRSProfile.Field (60 * agreements) w 3100 18 60
      IRSProfile.domain u0 u1 hgateB
  obtain ⟨thetaC, hthetaC, hkernelC⟩ := exists_nonzero_kernel_array
    IRSProfile.Field (50 * agreements) w 800000 15 50
      IRSProfile.domain u0 u1 hgateC
  have hDA : 0 < 50 * agreements := by norm_num [agreements]
  have hDB : 0 < 60 * agreements := by norm_num [agreements]
  have hDC : 0 < 50 * agreements := by norm_num [agreements]
  have hA := nonzero_kernel_member_universal IRSProfile.Field
    (50 * agreements) w 25000 15 50 agreements IRSProfile.domain u0 u1 thetaA
    hthetaA (LinearMap.mem_ker.mpr hkernelA) hDA rfl
  have hB := nonzero_kernel_member_universal IRSProfile.Field
    (60 * agreements) w 3100 18 60 agreements IRSProfile.domain u0 u1 thetaB
    hthetaB (LinearMap.mem_ker.mpr hkernelB) hDB rfl
  have hC := nonzero_kernel_member_universal IRSProfile.Field
    (50 * agreements) w 800000 15 50 agreements IRSProfile.domain u0 u1 thetaC
    hthetaC (LinearMap.mem_ker.mpr hkernelC) hDC rfl
  have hOrdA := flag_box_to_ordinary IRSProfile.Field
    (50 * agreements) w 25000 15 _ hA.2.1
  have hOrdB := flag_box_to_ordinary IRSProfile.Field
    (60 * agreements) w 3100 18 _ hB.2.1
  have hOrdC := flag_box_to_ordinary IRSProfile.Field
    (50 * agreements) w 800000 15 _ hC.2.1
  refine ⟨reconstruct IRSProfile.Field (50 * agreements) w 25000 15 thetaA,
    reconstruct IRSProfile.Field (60 * agreements) w 3100 18 thetaB,
    reconstruct IRSProfile.Field (50 * agreements) w 800000 15 thetaC,
    hA.1, hOrdA, hB.1, hOrdB, hC.1, hOrdC, hB.2.1, ?_⟩
  intro gamma P support hP hcard hvalues
  exact ⟨hA.2.2 gamma P support hP hcard hvalues,
    hB.2.2 gamma P support hP hcard hvalues,
    hC.2.2 gamma P support hP hcard hvalues⟩

end

end ProximityPrize.SubmissionLower.ContactStackedInterpolation6670Research
