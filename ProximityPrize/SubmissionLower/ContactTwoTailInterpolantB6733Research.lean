import ProximityPrize.SubmissionLower.ContactFlagKernelUniversalityResearch
import ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research

namespace ProximityPrize.SubmissionLower.ContactTwoTailInterpolantB6733Research

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
    ∃ QB : GlobalPoly,
      QB ≠ 0 ∧
      QB ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileB.weightedCap w profileB.totalCap profileB.slopeCap ∧
      ∀ gamma P (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support, P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        specialization IRSProfile.Field P gamma QB = 0 := by
  have hindex : Fintype.card IRSProfile.Index = n := by
    norm_num [IRSProfile.Index, n]
  have hB : Fintype.card IRSProfile.Index *
      ContactSeedlessInterpolationResearch.localRankBound
        profileB.multiplicity profileB.totalCap profileB.slopeCap <
      ContactSeedlessInterpolationResearch.coefficientCount
        profileB.weightedCap w profileB.totalCap profileB.slopeCap := by
    rw [hindex]
    exact interpolation_gateB_exact
  obtain ⟨thetaB, hnB, hkB⟩ := exists_nonzero_kernel_array
    IRSProfile.Field profileB.weightedCap w profileB.totalCap profileB.slopeCap
      profileB.multiplicity IRSProfile.domain u0 u1 hB
  have hDB : 0 < profileB.weightedCap := by decide
  have rB := nonzero_kernel_member_universal IRSProfile.Field
    profileB.weightedCap w profileB.totalCap profileB.slopeCap profileB.multiplicity
    agreements IRSProfile.domain u0 u1 thetaB hnB (LinearMap.mem_ker.mpr hkB) hDB rfl
  let QB := reconstruct IRSProfile.Field profileB.weightedCap w
    profileB.totalCap profileB.slopeCap thetaB
  exact ⟨QB, rB.1,
    flag_box_to_ordinary IRSProfile.Field _ w _ _ _ rB.2.1,
    rB.2.2⟩

end
end ProximityPrize.SubmissionLower.ContactTwoTailInterpolantB6733Research
