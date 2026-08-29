import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagKernelUniversalityResearch
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research

/-!
# Three universal contact interpolants at the 67.40 row

This is the target-specific instantiation of the generic contact-kernel
universality theorem at `a = 181982`.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedInterpolation6670Research

open ProximityPrize.Benchmark
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactFlagKernelUniversalityResearch ContactStackedParameters6670Research

noncomputable section

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

/-- Three boxed interpolants that vanish universally on all agreement points
with multiplicity vector `(45, 76, 45)`. -/
theorem exists_stacked_universal_vanishing_interpolants
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ QA QB QC : GlobalPoly,
      QA ≠ 0 ∧
      QA ∈ globalCoefficientBox IRSProfile.Field
        (45 * agreements) w 20000 14 ∧
      QB ≠ 0 ∧
      QB ∈ globalCoefficientBox IRSProfile.Field
        (76 * agreements) w 1450 23 ∧
      QC ≠ 0 ∧
      QC ∈ globalCoefficientBox IRSProfile.Field
        (45 * agreements) w 50000 14 ∧
      QB ∈ ContactFlagInterpolation6641Research.globalCoefficientBox IRSProfile.Field
        (76 * agreements) w 1450 23 ∧
      ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support,
          P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        specialization IRSProfile.Field P gamma QA = 0 ∧
        specialization IRSProfile.Field P gamma QB = 0 ∧
        specialization IRSProfile.Field P gamma QC = 0 := by
  have hA := exists_universal_vanishing_interpolant u0 u1
    45 20000 14 (by norm_num [agreements])
    (by norm_num [agreements]) (by norm_num [agreements])
    (by norm_num [agreements])
    profileA_values.2.2.2.2
  have hB := exists_universal_vanishing_interpolant u0 u1
    76 1450 23 (by norm_num [agreements])
    (by norm_num [agreements]) (by norm_num [agreements])
    (by norm_num [agreements])
    profileB_values.2.2.2.2
  have hC := exists_universal_vanishing_interpolant u0 u1
    45 50000 14 (by norm_num [agreements])
    (by norm_num [agreements]) (by norm_num [agreements])
    (by norm_num [agreements])
    profileC_values.2.2.2.2
  rcases hA with ⟨QA, hQA_ne, hQA_box, hQA_univ⟩
  rcases hB with ⟨QB, hQB_ne, hQB_box, hQB_univ⟩
  rcases hC with ⟨QC, hQC_ne, hQC_box, hQC_univ⟩
  have hQB_flag : QB ∈ ContactFlagInterpolation6641Research.globalCoefficientBox IRSProfile.Field
      (76 * agreements) w 1450 23 := by
    exact mem_globalFlagBox_of_mem_box QB (76 * agreements) w 1450 23 hQB_box
  refine ⟨QA, QB, QC, hQA_ne, hQA_box, hQB_ne, hQB_box, hQC_ne, hQC_box, hQB_flag, ?_⟩
  intro gamma P support hP hcard hvalues
  exact ⟨hQA_univ gamma P support hP hcard hvalues,
    hQB_univ gamma P support hP hcard hvalues,
    hQC_univ gamma P support hP hcard hvalues⟩

end

end ProximityPrize.SubmissionLower.ContactStackedInterpolation6670Research
