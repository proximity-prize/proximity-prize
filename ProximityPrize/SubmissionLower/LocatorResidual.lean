import ProximityPrize.SubmissionLower.GH
import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorCover
namespace ProximityPrize.SubmissionLower.LocatorResidual
open scoped Classical
open LocatorArithmetic RCN174 RCN319 RCN260 RCN318 RCN238 RCN243 RCN052 RCN303 RCN259 RCN180 RCN156 RCN234
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
structure Gates:Prop where
  kD:w < residualSingular.kappa * residualSingular.D
  algebraic_pos:1 ≤ residualSingular.algebraicCap
  implicit_small:residualSingular.implicitYCap < 2130706433
  algebraic_small:residualSingular.algebraicCap < 2130706433
  mixed_small:2 * residualSingular.implicitYCap *
    residualSingular.algebraicCap < 2130706433
  qY:(residualSingular.D - 1) / w ≤ residualStage.leftY
  leftZ_small:residualStage.leftZ < 2130706433
  mixedY_small:residualStage.mixedCost.y < 2130706433
  mixedR_small:residualStage.mixedCost.r < 2130706433
  mixedZ_small:residualStage.mixedCost.z < 2130706433
theorem gates:Gates:=by
  exact ⟨residual_singular_gates.kD,
    residual_singular_gates.algebraic_pos,
    residual_singular_gates.implicit_small,
    residual_singular_gates.algebraic_small,
    residual_singular_gates.mixed_small,
    residual_gates.qY,residual_gates.leftZ_small,
    residual_gates.mixedY_small,residual_gates.mixedR_small,
    residual_gates.mixedZ_small⟩
theorem residual_count_lt
    (valid:Gates)
    (Q T:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0) (hrel:IsRelPrime Q T)
    (hbox:Q ∈ globalCoefficientBox K weightedB w LB 22)
    (hTcaps:T.degreeOf 1 ≤ 243 ∧ T.degreeOf 2 ≤ 52 ∧ T.degreeOf 3 ≤ LA)
    (selected:K → Polynomial K) (seeds:Finset K)
    (nodes:Finset I) (x u0 u1:I → K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hQsolution:∀ gamma ∈ seeds,specialization K (selected gamma) gamma Q=0)
    (hTsolution:∀ gamma ∈ seeds,specialization K (selected gamma) gamma T=0)
    (hagreement:∀ gamma ∈ seeds,agreements ≤
      (nodes.filter (fun i=> (selected gamma).eval (x i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected seeds w (n - agreements)) :
    seeds.card < residualStage.regularCountCap +
      residualSingular.countCap + 1:=by
  classical
  apply asymmetric_stage_count_lt_of_regular_factors
    residualStage residualSingular Q T hQ 2130706433
    (by change 1 ≤ 22; decide) (by change 22 < 2130706433; decide)
    (by change 1 ≤ 131071; decide) (by change 131071 < 2130706433; decide) valid.kD
    valid.algebraic_pos valid.implicit_small valid.algebraic_small valid.mixed_small
    (by change 131071 < 181648; decide) (by change 181648 ≤ 262144; decide)
    hbox (by norm_num only [residualStage,UnequalParameters.gap,agreements,w])
    (by simp only [residualSingular,residualStage,TightParameters.gap,
      UnequalParameters.gap])
    valid.qY (by change 22 ≤ 22; decide) (by exact Nat.le_refl _)
    selected seeds nodes x u0 u1 hinj hnodes hdegree hQsolution hTsolution hagreement
    (by simpa only [residualSingular,TightParameters.errors] using hno)
  exact all_regularPairSeeds_bound residualStage Q T hQ hrel
    weightedB w LB 22 2130706433 hbox (by decide)
    valid.qY (by change 22 ≤ 22; decide) (by exact Nat.le_refl _)
    hTcaps.1 hTcaps.2.1 hTcaps.2.2 (by change 1 ≤ 22; decide)
    (by change 105 < 2130706433; decide) (by change 22 < 2130706433; decide)
    valid.leftZ_small valid.mixedY_small valid.mixedR_small valid.mixedZ_small
    selected seeds nodes x u0 u1 hinj hnodes
    (by change 1 ≤ 131071; decide) (by change 131071 < 2130706433; decide)
    (by change 131071 < 181648; decide) (by change 181648 ≤ 262144; decide)
    hdegree hagreement
    (by simpa only [residualStage,UnequalParameters.errors] using hno)
theorem gcd_residual_count_lt
    [GCDMonoid (MvPolynomial (Fin 4) K)]
    (QA QB:MvPolynomial (Fin 4) K) (hQA:QA ≠ 0) (hQB:QB ≠ 0)
    (hboxA:QA ∈ RCN100.globalCoefficientBox K weightedC w LA 52)
    (hboxB:QB ∈ RCN100.globalCoefficientBox K weightedB w LB 22)
    (selected:K → Polynomial K) (seeds:Finset K)
    (nodes:Finset I) (x u0 u1:I → K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hA:∀ gamma ∈ seeds,specialization K (selected gamma) gamma QA=0)
    (hB:∀ gamma ∈ seeds,specialization K (selected gamma) gamma QB=0)
    (hagreement:∀ gamma ∈ seeds,agreements ≤
      (nodes.filter (fun i=> (selected gamma).eval (x i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected seeds w (n - agreements)) :
    (LocatorCover.residual
      (fun gamma=> (specialization K (selected gamma) gamma).toRingHom)
      seeds QA QB).card < residualStage.regularCountCap +
        residualSingular.countCap + 1:=by
  classical
  let phi:=fun gamma=> (specialization K (selected gamma) gamma).toRingHom
  let Delta:=LocatorCover.residual phi seeds QA QB
  let H:=gcd12 QA QB
  let Q:=quotientB QA QB
  let T:=quotientA QA QB
  have hH:H ≠ 0:=gcd_ne_zero_of_left hQA
  have hQeq:QB=H * Q:=b_eq_gcd12_mul_quotientB QA QB
  have hTeq:QA=H * T:=a_eq_gcd12_mul_quotientA QA QB
  have hQ:Q ≠ 0:=by
    intro hz
    exact hQB (by rw [hQeq,hz,mul_zero])
  have hT:T ≠ 0:=by
    intro hz
    exact hQA (by rw [hTeq,hz,mul_zero])
  have hQflag:=quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    QB H Q weightedB w LB 22 0 0 0 hQB hH hQ hboxB hQeq
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have hTflag:=quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    QA H T weightedC w LA 52 0 0 0 hQA hH hT hboxA hTeq
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have hQbox:Q ∈ globalCoefficientBox K weightedB w LB 22:=
    RCN101.flag_box_to_ordinary K
      weightedB w LB 22 Q (by simpa only [Nat.sub_zero] using hQflag)
  have hTbox:T ∈ globalCoefficientBox K weightedC w LA 52:=
    RCN101.flag_box_to_ordinary K
      weightedC w LA 52 T (by simpa only [Nat.sub_zero] using hTflag)
  have hTcaps:=RCN081.degree_bounds_of_mem_box
    T weightedC w LA 52 (by decide) hTbox
  rw [show (weightedC - 1) / w=243 by decide] at hTcaps
  have hsub:Delta ⊆ seeds:=by
    intro gamma hg
    have hm:gamma ∈ seeds ∧ (phi gamma) (gcd12 QA QB) ≠ 0:=by
      simpa only [Delta,LocatorCover.residual,Finset.mem_filter] using hg
    exact hm.1
  have hsol (gamma:K) (hg:gamma ∈ Delta) :
      specialization K (selected gamma) gamma T=0 ∧
      specialization K (selected gamma) gamma Q=0:=
    LocatorCover.residual_vanish phi seeds QA QB hA hB gamma hg
  exact residual_count_lt gates Q T hQ
    (firstQuotients_isRelPrime hQA).symm hQbox hTcaps selected Delta
    nodes x u0 u1 hinj hnodes
    (fun gamma hg=> hdegree gamma (hsub hg))
    (fun gamma hg=> (hsol gamma hg).2) (fun gamma hg=> (hsol gamma hg).1)
    (fun gamma hg=> hagreement gamma (hsub hg))
    (noLargeSelectedPencil_mono selected seeds Delta w (n - agreements) hsub hno)
end
end ProximityPrize.SubmissionLower.LocatorResidual
