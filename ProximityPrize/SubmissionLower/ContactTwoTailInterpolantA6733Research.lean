import ProximityPrize.SubmissionLower.ContactFlagKernelUniversalityResearch
import ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research

namespace ProximityPrize.SubmissionLower.ContactTwoTailInterpolantA6733Research

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
    ∃ QA : GlobalPoly,
      QA ≠ 0 ∧
      QA ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileA.weightedCap w profileA.totalCap profileA.slopeCap ∧
      ∀ gamma P (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support, P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        specialization IRSProfile.Field P gamma QA = 0 := by
  have hindex : Fintype.card IRSProfile.Index = n := by
    norm_num [IRSProfile.Index, n]
  have hA : Fintype.card IRSProfile.Index *
      localRankBound profileA.multiplicity profileA.totalCap profileA.slopeCap <
      coefficientCount profileA.weightedCap w profileA.totalCap profileA.slopeCap := by
    rw [hindex]
    exact interpolation_gateA_exact
  obtain ⟨thetaA, hnA, hkA⟩ := exists_nonzero_kernel_array
    IRSProfile.Field profileA.weightedCap w profileA.totalCap profileA.slopeCap
      profileA.multiplicity IRSProfile.domain u0 u1 hA
  have hDA : 0 < profileA.weightedCap := by decide
  have rA := nonzero_kernel_member_universal IRSProfile.Field
    profileA.weightedCap w profileA.totalCap profileA.slopeCap profileA.multiplicity
    agreements IRSProfile.domain u0 u1 thetaA hnA (LinearMap.mem_ker.mpr hkA) hDA rfl
  let QA := reconstruct IRSProfile.Field profileA.weightedCap w
    profileA.totalCap profileA.slopeCap thetaA
  exact ⟨QA, rA.1,
    flag_box_to_ordinary IRSProfile.Field _ w _ _ _ rA.2.1,
    rA.2.2⟩

end
end ProximityPrize.SubmissionLower.ContactTwoTailInterpolantA6733Research
