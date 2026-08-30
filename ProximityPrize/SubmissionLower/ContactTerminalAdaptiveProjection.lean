import ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamily
import ProximityPrize.SubmissionLower.ContactRobustFixedMeet
import ProximityPrize.SubmissionLower.ContactAdaptiveNestedUnitFamily
namespace ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection

open scoped Classical
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualCurveJointProjectionBounds
open ActualCoordinateDegreeSum
open ContactParameters
open ContactPrimeSeedIncidence
open ContactGenericSurface
open ContactProperCutSeedCount
open ContactRegularComponentCover
open ContactRegularFactorGate
open ContactFlagBezout
open ContactIdentityResidualIteration
open ContactIdentityResidualGlobalFlag
open ContactAdaptiveNestedProjection
open ContactAdaptiveNestedUnitFamily
open ContactAdaptiveUnitPoleFamily
open ContactWeakSeparableSeparator
open ContactResidualSupportParameters
open ContactRobustFixedMeet

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}

omit [IsAlgClosed Omega] in
theorem degree_bounds_of_polynomialInFlag
    {p : FlagDegree} {F : MvPolynomial (Fin 3) Omega}
    (hF : PolynomialInFlag p F) :
    F.degreeOf 0 ≤ p.yz + p.all ∧
      F.degreeOf 1 ≤ p.all ∧
      F.degreeOf 2 ≤ p.zOnly + p.yz + p.all := by
  refine ⟨?_, ?_, ?_⟩
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (Nat.le_add_right (e 0) (e 1)).trans (hF e he).2.1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (hF e he).1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (Nat.le_add_left (e 2) (e 0 + e 1)).trans (by
      simpa only [Nat.add_assoc] using (hF e he).2.2)

omit [IsAlgClosed Omega] in
theorem residualStage_pderiv_one_ne_zero_of_support
    {p e d : ℕ} [CharP Omega p] {flag : FlagDegree}
    {support : ResidualSupportParameters}
    (S : ResidualStage phi Gamma x p e flag d support) :
    MvPolynomial.pderiv (1 : Fin 3) S.G ≠ 0 := by
  intro hzero
  apply S.regular_proper
  rw [← surfaceMap_pderiv_R]
  obtain ⟨Q, hQ⟩ := S.G_dvd_surface
  refine ⟨MvPolynomial.pderiv (1 : Fin 3) Q, ?_⟩
  rw [hQ, MvPolynomial.pderiv_mul, hzero, zero_mul, zero_add]

end

end ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection
