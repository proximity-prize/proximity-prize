import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagKernelUniversalityResearch
import ProximityPrize.SubmissionLower.ContactMovingParameters6732Research
import ProximityPrize.SubmissionLower.ContactStackedGCDCover6670Research

namespace ProximityPrize.SubmissionLower.ContactMovingStackedInterpolation6732Research

open ProximityPrize.Benchmark
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactTranslation ContactFlagKernelUniversalityResearch
open ContactMovingParameters6732Research ContactStackedGCDCover6670Research
attribute [local simp] n errors agreements

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

theorem exists_stacked_universal_vanishing_interpolants
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ QA QB QC : MvPolynomial (Fin 4) IRSProfile.Field,
      QA ≠ 0 ∧
      QA ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        (43 * agreements) w 38583 11 ∧
      QB ≠ 0 ∧
      QB ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        (81 * agreements) w 1222 25 ∧
      QC ≠ 0 ∧
      QC ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        (40 * agreements) w 91386 12 ∧
      QB ∈ ContactFlagInterpolation6641Research.globalCoefficientBox IRSProfile.Field
        (81 * agreements) w 1222 25 ∧
      ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support,
          P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        specialization IRSProfile.Field P gamma QA = 0 ∧
        specialization IRSProfile.Field P gamma QB = 0 ∧
        specialization IRSProfile.Field P gamma QC = 0 := by
  have hgateA : Fintype.card IRSProfile.Index * localRankBound 43 38583 11 <
      coefficientCount (43 * agreements) w 38583 11 := by
    rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change profileA.totalRank < profileA.coefficients
    exact interpolation_gates.1
  have hgateB : Fintype.card IRSProfile.Index * localRankBound 81 1222 25 <
      coefficientCount (81 * agreements) w 1222 25 := by
    rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change profileB.totalRank < profileB.coefficients
    exact interpolation_gates.2.1
  have hgateC : Fintype.card IRSProfile.Index * localRankBound 40 91386 12 <
      coefficientCount (40 * agreements) w 91386 12 := by
    rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change profileC.totalRank < profileC.coefficients
    exact interpolation_gates.2.2
  obtain ⟨thetaA, hthetaA, hkernelA⟩ := exists_nonzero_kernel_array
    IRSProfile.Field (43 * agreements) w 38583 11 43
      IRSProfile.domain u0 u1 hgateA
  obtain ⟨thetaB, hthetaB, hkernelB⟩ := exists_nonzero_kernel_array
    IRSProfile.Field (81 * agreements) w 1222 25 81
      IRSProfile.domain u0 u1 hgateB
  obtain ⟨thetaC, hthetaC, hkernelC⟩ := exists_nonzero_kernel_array
    IRSProfile.Field (40 * agreements) w 91386 12 40
      IRSProfile.domain u0 u1 hgateC
  have hDA : 0 < 43 * agreements := by norm_num [agreements]
  have hDB : 0 < 81 * agreements := by norm_num [agreements]
  have hDC : 0 < 40 * agreements := by norm_num [agreements]
  have hA := nonzero_kernel_member_universal IRSProfile.Field
    (43 * agreements) w 38583 11 43 agreements IRSProfile.domain u0 u1 thetaA
    hthetaA (LinearMap.mem_ker.mpr hkernelA) hDA rfl
  have hB := nonzero_kernel_member_universal IRSProfile.Field
    (81 * agreements) w 1222 25 81 agreements IRSProfile.domain u0 u1 thetaB
    hthetaB (LinearMap.mem_ker.mpr hkernelB) hDB rfl
  have hC := nonzero_kernel_member_universal IRSProfile.Field
    (40 * agreements) w 91386 12 40 agreements IRSProfile.domain u0 u1 thetaC
    hthetaC (LinearMap.mem_ker.mpr hkernelC) hDC rfl
  have hOrdA := flag_box_to_ordinary IRSProfile.Field
    (43 * agreements) w 38583 11 _ hA.2.1
  have hOrdB := flag_box_to_ordinary IRSProfile.Field
    (81 * agreements) w 1222 25 _ hB.2.1
  have hOrdC := flag_box_to_ordinary IRSProfile.Field
    (40 * agreements) w 91386 12 _ hC.2.1
  refine ⟨reconstruct IRSProfile.Field (43 * agreements) w 38583 11 thetaA,
    reconstruct IRSProfile.Field (81 * agreements) w 1222 25 thetaB,
    reconstruct IRSProfile.Field (40 * agreements) w 91386 12 thetaC,
    hA.1, hOrdA, hB.1, hOrdB, hC.1, hOrdC, hB.2.1, ?_⟩
  intro gamma P support hP hcard hvalues
  exact ⟨hA.2.2 gamma P support hP hcard hvalues,
    hB.2.2 gamma P support hP hcard hvalues,
    hC.2.2 gamma P support hP hcard hvalues⟩

local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly

theorem exists_stacked_interpolants_with_recursive_cover
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ QA QB QC : GlobalPoly,
      QA ≠ 0 ∧
      QA ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        (43 * agreements) w 38583 11 ∧
      QB ≠ 0 ∧
      QB ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        (81 * agreements) w 1222 25 ∧
      QC ≠ 0 ∧
      QC ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        (40 * agreements) w 91386 12 ∧
      QB ∈ ContactFlagInterpolation6641Research.globalCoefficientBox IRSProfile.Field
        (81 * agreements) w 1222 25 ∧
      ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support,
          P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        RecursiveSpecializationBranch P gamma QA QB QC := by
  obtain ⟨QA, QB, QC, hQA, hboxA, hQB, hboxB, hQC, hboxC, hflagB,
      huniversal⟩ :=
    exists_stacked_universal_vanishing_interpolants u0 u1
  refine ⟨QA, QB, QC, hQA, hboxA, hQB, hboxB, hQC, hboxC, hflagB, ?_⟩
  intro gamma P support hP hcard hvalues
  obtain ⟨hA, hB, hC⟩ := huniversal gamma P support hP hcard hvalues
  exact recursive_branch_of_three_vanishings P gamma QA QB QC hA hB hC

end

end ProximityPrize.SubmissionLower.ContactMovingStackedInterpolation6732Research
