import ProximityPrize.SubmissionLower.ContactFlagKernelUniversalityResearch
import ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research

namespace ProximityPrize.SubmissionLower.ContactTwoTailInterpolantC6733Research

open ProximityPrize.Benchmark
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactTranslation ContactFlagKernelUniversalityResearch
open ContactTwoTailParameters6733Research

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

theorem exists_universal_interpolant
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ QC : GlobalPoly,
      QC ≠ 0 ∧
      QC ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileC.weightedCap w profileC.totalCap profileC.slopeCap ∧
      ∀ gamma P (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support, P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        specialization IRSProfile.Field P gamma QC = 0 := by
  have hindex : Fintype.card IRSProfile.Index = n := by
    norm_num [IRSProfile.Index, n]
  have hC : Fintype.card IRSProfile.Index *
      localRankBound profileC.multiplicity profileC.totalCap profileC.slopeCap <
      coefficientCount profileC.weightedCap w profileC.totalCap profileC.slopeCap := by
    rw [hindex]
    exact interpolation_gateC_exact
  obtain ⟨thetaC, hnC, hkC⟩ := exists_nonzero_kernel_array
    IRSProfile.Field profileC.weightedCap w profileC.totalCap profileC.slopeCap
      profileC.multiplicity IRSProfile.domain u0 u1 hC
  have hDC : 0 < profileC.weightedCap := by decide
  have rC := nonzero_kernel_member_universal IRSProfile.Field
    profileC.weightedCap w profileC.totalCap profileC.slopeCap profileC.multiplicity
    agreements IRSProfile.domain u0 u1 thetaC hnC (LinearMap.mem_ker.mpr hkC) hDC rfl
  let QC := reconstruct IRSProfile.Field profileC.weightedCap w
    profileC.totalCap profileC.slopeCap thetaC
  exact ⟨QC, rC.1,
    flag_box_to_ordinary IRSProfile.Field _ w _ _ _ rC.2.1,
    rC.2.2⟩

end
end ProximityPrize.SubmissionLower.ContactTwoTailInterpolantC6733Research
