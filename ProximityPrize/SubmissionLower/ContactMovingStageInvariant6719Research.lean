import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIntrinsicRationalZero6719Research
import ProximityPrize.SubmissionLower.ContactMovingBudgetTransport6719Research
import ProximityPrize.SubmissionLower.ContactActualResidualStep6719Research
import ProximityPrize.SubmissionLower.ContactMovingRecursiveIncidence6719Research
import ProximityPrize.SubmissionLower.ContactResidualContactQuotient6719Research

/-! .
 -/

namespace ProximityPrize.SubmissionLower.ContactMovingStageInvariant6719Research

open scoped Classical
open ContactGenericSurface ContactTaylorNumerators
open ContactFlagBezout6543Research ContactResidualSupportParametersResearch
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualCurveIterationResearch.CurveResidualStage
open ContactActualResidualStep6719Research
open ContactMovingRecursiveIncidence6719Research
open ContactIntrinsicRationalZero6719Research ContactMovingCurveBudget6719Research
open ContactFlagAffineResidualAutomorphismResearch
open ContactResidualContactQuotient6719Research

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

variable {K Ω I : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable {φ : Polynomial K →+* Ω} {Γ : Finset K} {x : I → K}
variable {p e : ℕ} [CharP Ω p] {sf cf : FlagDegree}
variable {support : ResidualSupportParameters}

def stageH {n : ℕ} (S : CurveResidualStage φ Γ x p e sf cf n support) :=
  surfaceMap φ (polyH K S.F)

def stageG {n : ℕ} (S : CurveResidualStage φ Γ x p e sf cf n support) :=
  surfaceMap φ (polyG K S.F)

/-- .
 -/
def StageInvariant (zCost yzCost allCost movingCost : ℕ) {n : ℕ}
    (S : CurveResidualStage φ Γ x p e sf cf n support) : Prop :=
  letI : S.primeIdeal.IsPrime := S.primeIdeal_isPrime
  RationalZeroCriterion S.primeIdeal ∧
    ∃ B : MovingPoleBudget S.primeIdeal (stageH S) (stageG S),
      B.zCost = zCost ∧ B.yzCost = yzCost ∧ B.allCost = allCost ∧ B.movingCost = movingCost

theorem StageInvariant.transport_actual
    {zCost yzCost allCost movingCost n m : ℕ}
    {S : CurveResidualStage φ Γ x p e sf cf n support}
    {T : CurveResidualStage φ Γ x p e sf cf m support}
    (hstep : ActualResidualTransition S T)
    (h : StageInvariant zCost yzCost allCost movingCost S) :
    StageInvariant zCost yzCost allCost movingCost T := by
  letI : S.primeIdeal.IsPrime := S.primeIdeal_isPrime
  letI : T.primeIdeal.IsPrime := T.primeIdeal_isPrime
  obtain ⟨P0, P1, V, hv, hF, _, _, hprime⟩ := hstep
  obtain ⟨hcriterion, budget, hz, hyz, ha, hm⟩ := h
  let E := residualEquiv (φ P0) (φ V) (φ P1)
    (φ P0.derivative) (φ V.derivative) (φ P1.derivative) hv
  let L := MvPolynomial.C (-1 : Ω) * surfaceMap φ (residualAcceleration P0 P1 V)
  have hL : PolynomialInFlag unitAllFlag L :=
    scaled_acceleration_inFlag φ P0 P1 V (-1)
  have hH : stageH S ∉ S.primeIdeal := S.regularity_not_mem_primeIdeal
  have hHnext : stageH T = MvPolynomial.C (φ V) * E (stageH S) := by
    dsimp only [stageH]
    rw [hF]
    exact surfaceMap_polyH_residual φ P0 P1 V S.F
  have hGnext : stageG T = MvPolynomial.C (1 : Ω) * E (stageG S) + L * E (stageH S) := by
    dsimp only [stageG]
    rw [hF, surfaceMap_polyG_residual]
    change E (stageG S) - surfaceMap φ (residualAcceleration P0 P1 V) * E (stageH S) = _
    simp only [stageG, L, map_neg, map_one, one_mul, neg_one_mul, neg_mul, sub_eq_add_neg]
  let nextBudget : MovingPoleBudget T.primeIdeal (stageH T) (stageG T) :=
    budget.map_residual (φ P0) (φ V) (φ P1)
      (φ P0.derivative) (φ V.derivative) (φ P1.derivative) hv hprime
      L (φ V) 1 hv one_ne_zero hH hHnext hGnext hL
  have hnextCriterion : RationalZeroCriterion T.primeIdeal :=
    RationalZeroCriterion.map_residual S.primeIdeal T.primeIdeal hcriterion
      (φ P0) (φ V) (φ P1)
      (φ P0.derivative) (φ V.derivative) (φ P1.derivative) hv hprime
  refine ⟨hnextCriterion, nextBudget, ?_, ?_, ?_, ?_⟩
  · exact hz
  · exact hyz
  · exact ha
  · exact hm

/-- .
 -/
theorem stageInvariant_advance (hφ : Function.Injective φ)
    (zCost yzCost allCost movingCost : ℕ) :
    InvariantAdvance (fun n (S : CurveResidualStage φ Γ x p e sf cf n support) ↦
      StageInvariant zCost yzCost allCost movingCost S) := by
  apply invariantAdvance_of_relation _ (fun {_ _} S T ↦ ActualResidualTransition S T)
  · intro n S hne hcard
    exact actual_advance_card_certified hφ S hne hcard
  · intro n m S T hstep hInv
    exact hInv.transport_actual hstep

end

end ProximityPrize.SubmissionLower.ContactMovingStageInvariant6719Research
