import ProximityPrize.SubmissionLower.GH
import ProximityPrize.SubmissionLower.RegularColonArithmetic
import ProximityPrize.SubmissionLower.TwoInterpolatorCover
namespace ProximityPrize.SubmissionLower.RegularColonResidual
open scoped Classical
open RegularColonArithmetic RCN174 RCN319
open RCN260 RCN318
open RCN238 RCN243
open RCN052 RCN303
open RCN259 RCN180
open RCN156 RCN234
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

structure Gates (lt : ℕ) : Prop where
  kD : w < (residualSingular lt).kappa * (residualSingular lt).D
  algebraic_pos : 1 ≤ (residualSingular lt).algebraicCap
  implicit_small : (residualSingular lt).implicitYCap < 2130706433
  algebraic_small : (residualSingular lt).algebraicCap < 2130706433
  mixed_small : 2 * (residualSingular lt).implicitYCap *
    (residualSingular lt).algebraicCap < 2130706433
  qY : ((residualSingular lt).D - 1) / w ≤ (residualStage lt).leftY
  leftZ_small : (residualStage lt).leftZ < 2130706433
  mixedY_small : (residualStage lt).mixedCost.y < 2130706433
  mixedR_small : (residualStage lt).mixedCost.r < 2130706433
  mixedZ_small : (residualStage lt).mixedCost.z < 2130706433

theorem gates (lt : ℕ) (h : lt = 0 ∨ lt = 1281) : Gates lt := by
  rcases h with rfl | rfl <;> constructor <;> decide

/- Existing asymmetric residual counting, now with the 80112-error row.
   This is not a proof of the fixed-factor count or the full ProtocolClaim. -/
theorem residual_count_lt
    (lt : ℕ) (valid : Gates lt)
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (hbox : Q ∈ globalCoefficientBox K (81 * agreements) w (1283 - lt) 25)
    (hTcaps : T.degreeOf 1 ≤ 58 ∧ T.degreeOf 2 ≤ 12 ∧ T.degreeOf 3 ≤ 240000 - lt)
    (selected : K → Polynomial K) (seeds : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hQsolution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma Q = 0)
    (hTsolution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma T = 0)
    (hagreement : ∀ gamma ∈ seeds, agreements ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected seeds w (n - agreements)) :
    seeds.card < (residualStage lt).regularCountCap +
      (residualSingular lt).countCap + 1 := by
  classical
  apply asymmetric_stage_count_lt_of_regular_factors
    (residualStage lt) (residualSingular lt) Q T hQ 2130706433
    (by change 1 ≤ 25; decide) (by change 25 < 2130706433; decide)
    (by change 1 ≤ 131071; decide) (by change 131071 < 2130706433; decide) valid.kD
    valid.algebraic_pos valid.implicit_small valid.algebraic_small valid.mixed_small
    (by change 131071 < 182032; decide) (by change 182032 ≤ 262144; decide)
    hbox (by norm_num only [residualStage, UnequalParameters.gap, agreements, w])
    (by simp only [residualSingular, residualStage, TightParameters.gap,
      UnequalParameters.gap])
    valid.qY (by change 25 ≤ 25; decide) (by exact Nat.le_refl _)
    selected seeds nodes x u0 u1 hinj hnodes hdegree hQsolution hTsolution hagreement
    (by simpa only [residualSingular, TightParameters.errors] using hno)
  exact all_regularPairSeeds_bound (residualStage lt) Q T hQ hrel
    (81 * agreements) w (1283 - lt) 25 2130706433 hbox (by decide)
    valid.qY (by change 25 ≤ 25; decide) (by exact Nat.le_refl _)
    hTcaps.1 hTcaps.2.1 hTcaps.2.2 (by change 1 ≤ 25; decide)
    (by change 112 < 2130706433; decide) (by change 25 < 2130706433; decide)
    valid.leftZ_small valid.mixedY_small valid.mixedR_small valid.mixedZ_small
    selected seeds nodes x u0 u1 hinj hnodes
    (by change 1 ≤ 131071; decide) (by change 131071 < 2130706433; decide)
    (by change 131071 < 182032; decide) (by change 182032 ≤ 262144; decide)
    hdegree hagreement
    (by simpa only [residualStage, UnequalParameters.errors] using hno)

/- The residual-count hypothesis in TwoInterpolatorCover is supplied here
   by the two actual quotient polynomials, not by an assumed count. -/
theorem gcd_residual_count_lt
    [GCDMonoid (MvPolynomial (Fin 4) K)]
    (lt : ℕ) (hlt : lt = 0 ∨ lt = 1281)
    (QA QB : MvPolynomial (Fin 4) K) (hQA : QA ≠ 0) (hQB : QB ≠ 0)
    (hboxA : QA ∈ RCN100.globalCoefficientBox K
      (42 * agreements) w 240000 12)
    (hboxB : QB ∈ RCN100.globalCoefficientBox K
      (81 * agreements) w 1283 25)
    (htotal : lt ≤ wt residualTotalWeights (gcd12 QA QB))
    (selected : K → Polynomial K) (seeds : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hA : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma QA = 0)
    (hB : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma QB = 0)
    (hagreement : ∀ gamma ∈ seeds, agreements ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected seeds w (n - agreements)) :
    (TwoInterpolatorCover.residual
      (fun gamma => (specialization K (selected gamma) gamma).toRingHom)
      seeds QA QB).card < (residualStage lt).regularCountCap +
        (residualSingular lt).countCap + 1 := by
  classical
  let phi := fun gamma => (specialization K (selected gamma) gamma).toRingHom
  let Delta := TwoInterpolatorCover.residual phi seeds QA QB
  let H := gcd12 QA QB
  let Q := quotientB QA QB
  let T := quotientA QA QB
  have hH : H ≠ 0 := gcd_ne_zero_of_left hQA
  have hQeq : QB = H * Q := b_eq_gcd12_mul_quotientB QA QB
  have hTeq : QA = H * T := a_eq_gcd12_mul_quotientA QA QB
  have hQ : Q ≠ 0 := by
    intro hz
    exact hQB (by rw [hQeq, hz, mul_zero])
  have hT : T ≠ 0 := by
    intro hz
    exact hQA (by rw [hTeq, hz, mul_zero])
  have hQflag := quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    QB H Q (81 * agreements) w 1283 25 0 lt 0 hQB hH hQ hboxB hQeq
    (Nat.zero_le _) htotal (Nat.zero_le _)
  have hTflag := quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    QA H T (42 * agreements) w 240000 12 0 lt 0 hQA hH hT hboxA hTeq
    (Nat.zero_le _) htotal (Nat.zero_le _)
  have hQbox : Q ∈ globalCoefficientBox K (81 * agreements) w (1283 - lt) 25 :=
    RCN101.flag_box_to_ordinary K
      (81 * agreements) w (1283 - lt) 25 Q (by simpa only [Nat.sub_zero] using hQflag)
  have hTbox : T ∈ globalCoefficientBox K (42 * agreements) w (240000 - lt) 12 :=
    RCN101.flag_box_to_ordinary K
      (42 * agreements) w (240000 - lt) 12 T (by simpa only [Nat.sub_zero] using hTflag)
  have hTcaps := RCN081.degree_bounds_of_mem_box
    T (42 * agreements) w (240000 - lt) 12 (by decide) hTbox
  rw [show (42 * agreements - 1) / w = 58 by decide] at hTcaps
  have hsub : Delta ⊆ seeds := by
    intro gamma hg
    have hm : gamma ∈ seeds ∧ (phi gamma) (gcd12 QA QB) ≠ 0 := by
      simpa only [Delta, TwoInterpolatorCover.residual, Finset.mem_filter] using hg
    exact hm.1
  have hsol (gamma : K) (hg : gamma ∈ Delta) :
      specialization K (selected gamma) gamma T = 0 ∧
      specialization K (selected gamma) gamma Q = 0 :=
    TwoInterpolatorCover.residual_vanish phi seeds QA QB hA hB gamma hg
  exact residual_count_lt lt (gates lt hlt) Q T hQ
    (firstQuotients_isRelPrime hQA).symm hQbox hTcaps selected Delta
    nodes x u0 u1 hinj hnodes
    (fun gamma hg => hdegree gamma (hsub hg))
    (fun gamma hg => (hsol gamma hg).2) (fun gamma hg => (hsol gamma hg).1)
    (fun gamma hg => hagreement gamma (hsub hg))
    (noLargeSelectedPencil_mono selected seeds Delta w (n - agreements) hsub hno)
end
end ProximityPrize.SubmissionLower.RegularColonResidual
