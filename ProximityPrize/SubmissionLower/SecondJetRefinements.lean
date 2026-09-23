import ProximityPrize.SubmissionLower.HigherInitialArithmetic6810
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.SecondJetTotalAvoidance
open MvPolynomial SecondJetSupport SecondJetCoefficients RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {K : Type*} [Field K]

/-- A coefficient loses one unit of residual total weight per S power. -/
theorem coefficient_total_weight (P : Poly (K := K)) (L j : ℕ)
    (hP : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L) :
    wt residualTotalWeights ((asS P).coeff j) ≤ L-j := by
  apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
  intro e he
  have hh := hP _ (coefficient_support P j e he)
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j e
  rw [h1,h2,h3,h4] at hh
  simp [residualTotalWeights, RCN081.weight_fin4]
  omega

theorem coefficient_not_dvd (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (L j : ℕ) (hP : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L)
    (hF : L < wt residualTotalWeights F) (hC : (asS P).coeff j ≠ 0) :
    ¬ F ∣ (asS P).coeff j := by
  intro hdiv
  have hh := RCN081.weightedTotalDegree_le_of_dvd residualTotalWeights F
    ((asS P).coeff j) hdiv hC
  have hc := coefficient_total_weight P L j hP
  change wt residualTotalWeights F ≤ wt residualTotalWeights ((asS P).coeff j) at hh
  omega

theorem leading_not_dvd (P : Poly (K := K)) (hP : P ≠ 0)
    (F : MvPolynomial (Fin 4) K) (L : ℕ)
    (hPL : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L)
    (hF : L < wt residualTotalWeights F) :
    (asS P).leadingCoeff ≠ 0 ∧ ¬ F ∣ (asS P).leadingCoeff := by
  have hn : asS P ≠ 0 := by
    intro hz
    apply hP
    apply (asS (K := K)).injective
    simpa only [map_zero] using hz
  have hc := Polynomial.leadingCoeff_ne_zero.mpr hn
  exact ⟨hc,coefficient_not_dvd P F L (asS P).natDegree hPL hF hc⟩

open SecondJetCoefficientSpecialization SecondJetClearedHelper SecondJetHelperWeights
open SecondJetRelaxedInterpolation SecondJetRelaxedCoefficientsReceipt SecondJetProperAlternatives
variable {N : Type*} [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJetTotalAvoidance

namespace ProximityPrize.SubmissionLower.SecondJetPairBounds
open RCN260 RCN052 RCN294

/-- The regular-seed inequality only needs the carrier's agreement vector. -/
theorem count_le_left_cap {K : Type} [Field K]
    (P : UnequalParameters) (F : MvPolynomial (Fin 4) K)
    (hY : F.degreeOf 1 ≤ P.leftY) (hR : F.degreeOf 2 ≤ P.leftR)
    (hZ : F.degreeOf 3 ≤ P.leftZ) (count : ℕ) (hgap : 0 < P.gap)
    (hc : count*P.gap ≤ (P.n-P.w)*dot P.leftAgreement (regularVector P F)+
      (P.errors+1)*P.gap*(regularVector P F).z) :
    count ≤ AsymmetricHelper.leftRegularCountCap P := by
  have hv := LocatorCoprimeQuotient.regularVector_le_mixedCost P F hY hR hZ
  have hdot : dot P.leftAgreement (regularVector P F) ≤ dot P.leftAgreement P.mixedCost :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left P.leftAgreement.y hv.1)
        (Nat.mul_le_mul_left P.leftAgreement.r hv.2.1))
      (Nat.mul_le_mul_left P.leftAgreement.z hv.2.2)
  apply (Nat.le_div_iff_mul_le hgap).mpr
  exact hc.trans (Nat.add_le_add (Nat.mul_le_mul_left (P.n-P.w) hdot)
    (Nat.mul_le_mul_left ((P.errors+1)*P.gap) hv.2.2))

end ProximityPrize.SubmissionLower.SecondJetPairBounds

namespace ProximityPrize.SubmissionLower.SecondJetRegularData.Data
open MvPolynomial RCN319 RCN260 RCN327
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetRegularData.Data

namespace ProximityPrize.SubmissionLower.SecondJetAsymmetric
open scoped Classical
open MvPolynomial RCN135 RCN136 RCN319 RCN327 RCN238 RCN222 RCN234 RCN156
open SecondJetRegularData SecondJetRegularData.Data SecondJetCoefficients
open SecondJetRelaxedInterpolation SecondJetProperAlternatives SecondJetExceptionalComponents
open AsymmetricHelper
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetAsymmetric

namespace ProximityPrize.SubmissionLower.SecondJetOwnShape
open MvPolynomial RCN130 RCN234 RCN156 RCN095 RCN347 RCN135
open SecondJetRegularData SecondJetRegularData.Data
noncomputable section
set_option autoImplicit false
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetOwnShape

namespace ProximityPrize.SubmissionLower.SecondJetProfile114
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts SecondJetRelaxedCounts
open SecondJetRelaxedCoefficientsReceipt SecondJetRelaxedInterpolation
open SecondJetNumericGeometry RCN260 RCN294 RCN135
open SecondJetRegularData SecondJetRegularData.Data SecondJetOwnShape
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

end
end ProximityPrize.SubmissionLower.SecondJetProfile114

namespace ProximityPrize.SubmissionLower.SecondJetRefinedCap
open RCN095 RCN260 RCN294 AsymmetricHelper SecondJetNumericGeometry
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end ProximityPrize.SubmissionLower.SecondJetRefinedCap

namespace ProximityPrize.SubmissionLower.SecondJetRefinedCap
open RCN130 RCN234 RCN156 RCN347 SecondJetRegularData SecondJetRegularData.Data SecondJetOwnShape
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetRefinedCap
