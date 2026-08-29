import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingStageInvariant6719Research
import ProximityPrize.SubmissionLower.ContactMovingAgreementCertificate6719Research

/-! .
 -/

namespace ProximityPrize.SubmissionLower.ContactMovingStageZero6719Research

open scoped Classical
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactFlagBezout6543Research ContactResidualSupportParametersResearch
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualCurveIterationResearch.CurveResidualStage
open ContactMovingRecursiveIncidence6719Research ContactMovingStageInvariant6719Research
open ContactMovingAgreementCertificate6719Research ContactMovingCurveBudget6719Research
open ContactIntrinsicRationalZero6719Research ContactMovingProjection6676Research
open ContactRegularZeroBudget6676Research

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

variable {K Ω I : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable {φ : Polynomial K →+* Ω} {Γ : Finset K} {x : I → K}
variable {p e : ℕ} [CharP Ω p] {sf cf : FlagDegree} {a b s : ℕ}

def degreeCost (a b s z yz all moving : ℕ) : ℕ :=
  a*z+b*yz+s*all+moving

def unitCost (a b s z yz all : ℕ) : ℕ :=
  (center a b s).zOnly*z+(center a b s).yz*yz+(center a b s).all*all

theorem stage_support_bounds {n : ℕ}
    (S : CurveResidualStage φ Γ x p e sf cf n (support a b s)) :
    S.F.degreeOf 2 ≤ s+2 ∧
      ContactPost6464MinkowskiRecurrenceResearch.wt ![0,1,1,0] S.F ≤ b+s+3 ∧
      ContactPost6464MinkowskiRecurrenceResearch.wt ![0,1,1,1] S.F ≤ a+b+s+3 := by
  have h : ResidualSupportData (support a b s) S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  exact ⟨h.coordinate_bounds.2.1, S.surface_ys_weight, S.surface_total_weight⟩

/-- .
 -/
theorem regular_agreement_zero_bound {n z yz all moving : ℕ}
    (S : CurveResidualStage φ Γ x p e sf cf n (support a b s))
    (hInv : StageInvariant z yz all moving S) (x0 u0 u1 : K)
    (hproper : agreementPolynomial φ S.F n x0 u0 u1 ∉ S.primeIdeal) :
    FiniteRegularZeroSetBound S.primeIdeal (regularitySurface φ S.F)
      (agreementPolynomial φ S.F n x0 u0 u1)
      (n * degreeCost a b s z yz all moving + unitCost a b s z yz all) := by
  letI : S.primeIdeal.IsPrime := S.primeIdeal_isPrime
  obtain ⟨hcriterion, budget, hz, hyz, ha, hm⟩ := hInv
  obtain ⟨hR, hYR, hAll⟩ := stage_support_bounds S
  obtain ⟨B, c, hEq, hB, hc, hk⟩ := exists_actual_agreement_certificate
    φ a b s S.F hR hYR hAll n x0 u0 u1
  have hH : stageH S ∉ S.primeIdeal := S.regularity_not_mem_primeIdeal
  have hcut : filteredCut (n-1) B (stageH S) (stageG S) ∉ S.primeIdeal := by
    simpa only [stageH, stageG, hEq] using hproper
  let cost := budget.weightedCost (center a b s) +
    (n-1)*(budget.weightedCost (⟨a,b,s⟩ : FlagDegree)+budget.movingCost)
  have hzero : FiniteRegularZeroSetBound S.primeIdeal (stageH S)
      (filteredCut (n-1) B (stageH S) (stageG S)) cost := by
    apply hcriterion (stageH S) _ (n-1) cost hcut hH
    intro W
    exact budget.sum_filteredCut_pole_le a b s (n-1) (center a b s) B c hH hB hc W
  have hcenter : budget.weightedCost (center a b s) = unitCost a b s z yz all := by
    simp only [MovingPoleBudget.weightedCost, hz, hyz, ha, unitCost]
  have hdegree : budget.weightedCost (⟨a,b,s⟩ : FlagDegree)+budget.movingCost =
      degreeCost a b s z yz all moving := by
    simp only [MovingPoleBudget.weightedCost, hz, hyz, ha, hm, degreeCost]
  have hcost : cost ≤ n * degreeCost a b s z yz all moving + unitCost a b s z yz all := by
    dsimp only [cost]
    rw [hcenter, hdegree]
    calc
      _ ≤ unitCost a b s z yz all + n * degreeCost a b s z yz all moving :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
      _ = _ := Nat.add_comm _ _
  have hfinal := hzero.mono hcost
  change FiniteRegularZeroSetBound S.primeIdeal (stageH S)
    (agreementPolynomial φ S.F n x0 u0 u1) _
  rw [hEq]
  exact hfinal

/-- .

 -/
theorem recursive_curve_moving_bound {d agreement : ℕ}
    (hφ : Function.Injective φ)
    (S : CurveResidualStage φ Γ x p e sf cf d (support a b s))
    (z yz all moving : ℕ) (hInv : StageInvariant z yz all moving S)
    (U V zCharge : ℕ) (hda : d < agreement)
    (hagreement : ∀ γ ∈ Γ, agreement ≤ (S.agreementFiber γ).card)
    (hlarge : ∀ D : S.TerminalDescendant,
      D.degree < D.stage.identities.card →
        Γ.card*(agreement-d) ≤ (e+1)*(agreement-d)*zCharge)
    (hdegree : ∀ k ≤ d,
      (S.nodes.card-k)*(agreement-d)*(d-k) ≤ U*(agreement-k))
    (hunit : ∀ k ≤ d,
      (S.nodes.card-k)*(agreement-d) ≤ V*(agreement-k)) :
    Γ.card*(agreement-d) ≤
      U*degreeCost a b s z yz all moving + V*unitCost a b s z yz all +
        (e+1)*(agreement-d)*zCharge := by
  apply recursive_curve_stratified_incidence_of_regular_invariant S
    (fun _ A ↦ StageInvariant z yz all moving A)
    (stageInvariant_advance hφ z yz all moving) hInv
    (degreeCost a b s z yz all moving) (unitCost a b s z yz all)
    U V zCharge
  · intro n A hA i _ hproper
    exact regular_agreement_zero_bound A hA (x i) (A.u0 i) (A.u1 i) hproper
  · exact hda
  · exact hagreement
  · exact hlarge
  · exact hdegree
  · exact hunit

end

end ProximityPrize.SubmissionLower.ContactMovingStageZero6719Research
