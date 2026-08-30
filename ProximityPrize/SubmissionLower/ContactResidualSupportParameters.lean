import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag

namespace ProximityPrize.SubmissionLower.ContactResidualSupportParameters

open ContactGenericSurface ContactTaylorNumerators
open ContactInterpolation ContactFactorCaps
open ContactPost6464MinkowskiRecurrence
open ContactIdentityResidualGlobalTransform
open ContactIdentityResidualGlobalFlag
open ContactFlagBezout

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

structure ResidualSupportParameters where
  s : ℕ
  ys : ℕ
  total : ℕ
  one_le_s : 1 ≤ s
  s_le_ys : s ≤ ys
  ys_le_total : ys ≤ total
  two_le_ys : 2 ≤ ys
  deriving DecidableEq

namespace ResidualSupportParameters

def acceptedSupport : ResidualSupportParameters where
  s := 8
  ys := 43
  total := 503
  one_le_s := by norm_num
  s_le_ys := by norm_num
  ys_le_total := by norm_num
  two_le_ys := by norm_num

end ResidualSupportParameters

variable {K Omega : Type} [Field K] [Field Omega]

abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

structure ResidualSupportData (P : ResidualSupportParameters) (F : Poly4 K) : Prop where
  s_weight : wt residualSWeights F ≤ P.s
  ys_weight : wt residualYSWeights F ≤ P.ys
  total_weight : wt residualTotalWeights F ≤ P.total

namespace ResidualSupportData

theorem globalResidual
    {P : ResidualSupportParameters} {F : Poly4 K}
    (H : ResidualSupportData P F)
    (P0 P1 V : Polynomial K) :
    ResidualSupportData P (globalResidualHom P0 P1 V F) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (globalResidualHom_wt_le_pulled residualSWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_s] using H.s_weight)
  · exact (globalResidualHom_wt_le_pulled residualYSWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_ys] using H.ys_weight)
  · exact (globalResidualHom_wt_le_pulled residualTotalWeights rfl
      P0 P1 V F).trans (by
        simpa [residualPullWeights_total] using H.total_weight)

theorem coordinate_bounds
    {P : ResidualSupportParameters} {F : Poly4 K}
    (H : ResidualSupportData P F) :
    F.degreeOf (1 : Fin 4) ≤ P.ys ∧
      F.degreeOf (2 : Fin 4) ≤ P.s ∧
      F.degreeOf (3 : Fin 4) ≤ P.total := by
  have hR : F.degreeOf (2 : Fin 4) ≤ P.s := by
    have hw : residualSWeights = Pi.single (2 : Fin 4) 1 := by
      funext i
      fin_cases i <;> rfl
    have hs := H.s_weight
    rw [hw, wt, MvPolynomial.weightedTotalDegree_piSingle] at hs
    exact hs
  have hY : F.degreeOf (1 : Fin 4) ≤ P.ys := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree residualYSWeights he).trans
      H.ys_weight
    rw [ContactFactorCaps.weight_fin4] at hw
    change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 0 ≤ P.ys at hw
    norm_num at hw
    omega
  have hZ : F.degreeOf (3 : Fin 4) ≤ P.total := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans
      H.total_weight
    rw [ContactFactorCaps.weight_fin4] at hw
    change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 1 ≤ P.total at hw
    norm_num at hw
    omega
  exact ⟨hY, hR, hZ⟩

end ResidualSupportData

end

end ProximityPrize.SubmissionLower.ContactResidualSupportParameters
