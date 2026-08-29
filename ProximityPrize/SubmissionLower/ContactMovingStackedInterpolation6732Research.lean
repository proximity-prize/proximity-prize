import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingParameters6732Research
import ProximityPrize.SubmissionLower.ContactStackedGCDCover6670Research
import ProximityPrize.SubmissionLower.ContactFlagInterpolation6641Research

/-! Existence of stacked interpolants QA, QB, QC with nonzero kernel. -/

namespace ProximityPrize.SubmissionLower.ContactMovingStackedInterpolation6732Research

open ProximityPrize.Benchmark
open ContactFlagInterpolation6641Research
open ContactStackedGCDCover6670Research
open ContactMovingParameters6732Research

noncomputable section

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

theorem exists_stacked_interpolants_with_recursive_cover
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ QA QB QC : GlobalPoly,
      QA ≠ 0 ∧
      QA ∈ globalCoefficientBox IRSProfile.Field
        (43 * agreements) w 6135 12 ∧
      QB ≠ 0 ∧
      QB ∈ globalCoefficientBox IRSProfile.Field
        (81 * agreements) w 1242 25 ∧
      QC ≠ 0 ∧
      QC ∈ globalCoefficientBox IRSProfile.Field
        (41 * agreements) w 19688 12 ∧
      QB ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
        IRSProfile.Field (81 * agreements) w 1242 25 ∧
      ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support, P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        RecursiveSpecializationBranch P gamma QA QB QC := by
  have hA := exists_nonzero_kernel_polynomial IRSProfile.Field
    (43 * agreements) w 6135 12 43 IRSProfile.domain u0 u1
    (by rw [show Fintype.card IRSProfile.Index = n by norm_num [IRSProfile.Index, n]]
        exact interpolation_gates.1)
  have hB := exists_nonzero_kernel_flag_polynomial IRSProfile.Field
    (81 * agreements) w 1242 25 81 IRSProfile.domain u0 u1
    (by rw [show Fintype.card IRSProfile.Index = n by norm_num [IRSProfile.Index, n]]
        exact interpolation_gates.2.1)
  have hC := exists_nonzero_kernel_polynomial IRSProfile.Field
    (41 * agreements) w 19688 12 41 IRSProfile.domain u0 u1
    (by rw [show Fintype.card IRSProfile.Index = n by norm_num [IRSProfile.Index, n]]
        exact interpolation_gates.2.2)
  obtain ⟨QA, hQAne, hQAbox, hQAdiv⟩ := hA
  obtain ⟨QB, hQBne, hQBbox, hQBflag, hQBdiv⟩ := hB
  obtain ⟨QC, hQCne, hQCbox, hQCdiv⟩ := hC
  refine ⟨QA, QB, QC, hQAne, hQAbox, hQBne, hQBbox, hQCne, hQCbox, hQBflag, ?_⟩
  intro gamma P support hPdeg hcard hagree
  have hcov := stacked_gcd_cover_of_divisible QA QB QC 43 81 41
    IRSProfile.domain u0 u1 gamma P support hPdeg hcard hagree
    hQAdiv hQBdiv hQCdiv
  exact hcov

end ProximityPrize.SubmissionLower.ContactMovingStackedInterpolation6732Research
