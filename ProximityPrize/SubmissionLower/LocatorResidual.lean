import ProximityPrize.SubmissionLower.GH
import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorCover
import ProximityPrize.SubmissionLower.LocatorDerivativeChain
namespace ProximityPrize.SubmissionLower.LocatorResidual
open scoped Classical
open LocatorArithmetic LocatorDerivativeChain RCN174 RCN319 RCN260 RCN318 RCN238 RCN243 RCN052 RCN303
  RCN259 RCN180 RCN156 RCN234
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

/-- Residual bound: regular pairs `(Q, T)`, the derivative-chain pairs
`(∂_R^j F, F)` for the positive-slope factors `F` of `Q`, and the slope-free
tails, all with linear characteristic gates only. -/
theorem residual_count_lt
    (Q T:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0) (hrel:IsRelPrime Q T)
    (hbox:Q ∈ globalCoefficientBox K weightedB w LB sB)
    (hTcaps:T.degreeOf 1 ≤ yT ∧ T.degreeOf 2 ≤ sT ∧ T.degreeOf 3 ≤ LCap)
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
      (sB - 1) * chainStage.regularCountCap + (sB + 1) * tailSingular.countCap + 1:=by
  have h:=residual_chain_count_le residualStage chainStage tailSingular Q T hQ hrel
    weightedB w LB sB 2130706433
    (by norm_num [sB]) (by norm_num [sB, prime]) (by norm_num [w]) (by norm_num)
    hbox
    (by norm_num [residualStage, UnequalParameters.gap, agreements, w])
    (by norm_num [residualStage, weightedB, w, yB]) (by norm_num [residualStage, sB])
    (by norm_num [residualStage, LB])
    (by simpa [residualStage, yT] using hTcaps.1) (by simpa [residualStage, sT] using hTcaps.2.1)
    (by simpa [residualStage, LCap] using hTcaps.2.2)
    (by norm_num [residualStage, sB]) (by norm_num [residualStage, yB])
    (by norm_num [residualStage, sB])
    (by norm_num [residualStage, LB])
    (by norm_num [residualStage, UnequalParameters.mixedCost, LCap, LB, yB, yT, sB, sT])
    (by norm_num [residualStage, UnequalParameters.mixedCost, LCap, LB, yB, yT, sB, sT])
    (by norm_num [residualStage, UnequalParameters.mixedCost, LCap, LB, yB, yT, sB, sT])
    (by norm_num [chainStage, UnequalParameters.gap, agreements, w])
    (by norm_num [chainStage, weightedB, w, yB]) (by norm_num [chainStage, sB])
    (by norm_num [chainStage, LB])
    (by norm_num [chainStage, weightedB, w, yB]) (by norm_num [chainStage, sB])
    (by norm_num [chainStage, LB])
    (by norm_num [chainStage, sB]) (by norm_num [chainStage, yB]) (by norm_num [chainStage, sB])
    (by norm_num [chainStage, LB])
    (by norm_num [chainStage, UnequalParameters.mixedCost, LB, yB, sB])
    (by norm_num [chainStage, UnequalParameters.mixedCost, LB, yB, sB])
    (by norm_num [chainStage, UnequalParameters.mixedCost, LB, yB, sB])
    rfl rfl rfl rfl
    (by norm_num [tailSingular, w])
    (by norm_num [tailSingular, TightParameters.kappa, weightedB, w])
    (by norm_num [tailSingular, TightParameters.algebraicCap, TightParameters.kappa, LB])
    (by norm_num [tailSingular, TightParameters.implicitYCap, TightParameters.kappa, weightedB, w])
    (by norm_num [tailSingular, TightParameters.algebraicCap, TightParameters.kappa, LB])
    (by norm_num [tailSingular, TightParameters.implicitYCap, TightParameters.algebraicCap,
      TightParameters.kappa, weightedB, w, LB])
    (by norm_num [tailSingular, w, agreements]) (by norm_num [tailSingular, n, agreements])
    selected seeds nodes x u0 u1 hinj
    (by simpa [residualStage] using hnodes) (by simpa [chainStage] using hnodes)
    (by simpa [tailSingular] using hnodes)
    (by norm_num [residualStage, w]) (by norm_num [residualStage, w])
    (by norm_num [residualStage, w, agreements]) (by norm_num [residualStage, n, agreements])
    (by norm_num [chainStage, w]) (by norm_num [chainStage, w])
    (by norm_num [chainStage, w, agreements]) (by norm_num [chainStage, n, agreements])
    (by simpa [residualStage] using hdegree) (by simpa [chainStage] using hdegree)
    (by simpa [tailSingular] using hdegree)
    (by simpa [residualStage] using hagreement) (by simpa [chainStage] using hagreement)
    (by simpa [tailSingular] using hagreement)
    (by simpa [residualStage, UnequalParameters.errors] using hno)
    (by simpa [chainStage, UnequalParameters.errors] using hno)
    (by simpa [tailSingular, TightParameters.errors] using hno)
    hQsolution hTsolution
  omega

theorem gcd_residual_count_lt
    [GCDMonoid (MvPolynomial (Fin 4) K)]
    (QA QB:MvPolynomial (Fin 4) K) (hQA:QA ≠ 0) (hQB:QB ≠ 0)
    (hboxA:QA ∈ RCN100.globalCoefficientBox K weightedTCap w LCap sT)
    (hboxB:QB ∈ RCN100.globalCoefficientBox K weightedB w LB sB)
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
        (sB - 1) * chainStage.regularCountCap + (sB + 1) * tailSingular.countCap + 1:=by
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
    QB H Q weightedB w LB sB 0 0 0 hQB hH hQ hboxB hQeq
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have hTflag:=quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    QA H T weightedTCap w LCap sT 0 0 0 hQA hH hT hboxA hTeq
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have hQbox:Q ∈ globalCoefficientBox K weightedB w LB sB:=
    RCN101.flag_box_to_ordinary K
      weightedB w LB sB Q (by simpa only [Nat.sub_zero] using hQflag)
  have hTbox:T ∈ globalCoefficientBox K weightedTCap w LCap sT:=
    RCN101.flag_box_to_ordinary K
      weightedTCap w LCap sT T (by simpa only [Nat.sub_zero] using hTflag)
  have hTcaps:=RCN081.degree_bounds_of_mem_box
    T weightedTCap w LCap sT (by decide) hTbox
  rw [show (weightedTCap - 1) / w=yT by decide] at hTcaps
  have hsub:Delta ⊆ seeds:=by
    intro gamma hg
    have hm:gamma ∈ seeds ∧ (phi gamma) (gcd12 QA QB) ≠ 0:=by
      simpa only [Delta,LocatorCover.residual,Finset.mem_filter] using hg
    exact hm.1
  have hsol (gamma:K) (hg:gamma ∈ Delta) :
      specialization K (selected gamma) gamma T=0 ∧
      specialization K (selected gamma) gamma Q=0:=
    LocatorCover.residual_vanish phi seeds QA QB hA hB gamma hg
  exact residual_count_lt Q T hQ
    (firstQuotients_isRelPrime hQA).symm hQbox hTcaps selected Delta
    nodes x u0 u1 hinj hnodes
    (fun gamma hg=> hdegree gamma (hsub hg))
    (fun gamma hg=> (hsol gamma hg).2) (fun gamma hg=> (hsol gamma hg).1)
    (fun gamma hg=> hagreement gamma (hsub hg))
    (noLargeSelectedPencil_mono selected seeds Delta w (n - agreements) hsub hno)
end
end ProximityPrize.SubmissionLower.LocatorResidual
