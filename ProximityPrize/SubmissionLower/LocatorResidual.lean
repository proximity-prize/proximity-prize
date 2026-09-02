import ProximityPrize.SubmissionLower.GH
import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorCover
import ProximityPrize.SubmissionLower.LocatorDerivativeChainPartial
namespace ProximityPrize.SubmissionLower.LocatorResidual
open scoped Classical
open LocatorArithmetic LocatorDerivativeChain LocatorDerivativeChainPartial
  RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318
  RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243
  RCN303 RCN259 RCN180 RCN156 RCN234
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
    (hTcaps:T.degreeOf 1 ≤ yC ∧ T.degreeOf 2 ≤ sC ∧ T.degreeOf 3 ≤ LC)
    (selected:K → Polynomial K) (seeds:Finset K)
    (nodes:Finset I) (x u0 u1:I → K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hQsolution:∀ gamma ∈ seeds,specialization K (selected gamma) gamma Q=0)
    (hTsolution:∀ gamma ∈ seeds,specialization K (selected gamma) gamma T=0)
    (hagreement:∀ gamma ∈ seeds,agreements ≤
      (nodes.filter (fun i=> (selected gamma).eval (x i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected seeds w (n - agreements)) :
    seeds.card < residualCap + 1:=by
  classical
  have hregular := all_regularPairSeeds_bound residualStage Q T hQ hrel
    weightedB w LB sB 2130706433 hbox (by norm_num [w])
    (by norm_num [residualStage, weightedB, w, yB])
    (by norm_num [residualStage, sB]) (by norm_num [residualStage, LB])
    (by simpa [residualStage, yC] using hTcaps.1)
    (by simpa [residualStage, sC] using hTcaps.2.1)
    (by simpa [residualStage, LC] using hTcaps.2.2)
    (by norm_num [residualStage, sB])
    (by norm_num [residualStage, yB]) (by norm_num [residualStage, sB])
    (by norm_num [residualStage, LB])
    (by norm_num [residualStage, UnequalParameters.mixedCost,
      LC, LB, yB, yC, sB, sC])
    (by norm_num [residualStage, UnequalParameters.mixedCost,
      LC, LB, yB, yC, sB, sC])
    (by norm_num [residualStage, UnequalParameters.mixedCost,
      LC, LB, yB, yC, sB, sC])
    selected seeds nodes x u0 u1 hinj (by simpa [residualStage] using hnodes)
    (by norm_num [residualStage, w]) (by norm_num [residualStage, w])
    (by norm_num [residualStage, w, agreements])
    (by norm_num [residualStage, n, agreements])
    (by simpa [residualStage] using hdegree)
    (by simpa [residualStage] using hagreement)
    (by simpa [residualStage, UnequalParameters.errors] using hno)
  have hregSum := sum_regular_counts_bound residualStage Q T selected seeds
    (regularVector_budgets residualStage Q hQ weightedB w LB sB
      (by norm_num [w]) hbox
      (by norm_num [residualStage, weightedB, w, yB])
      (by norm_num [residualStage, sB]) (by norm_num [residualStage, LB]))
    hregular
  have hregCap : (∑ F : RegularIndex Q,
      (regularPairSeeds Q T selected seeds F).card) ≤
        residualStage.regularCountCap :=
    residualStage.regular_count_le _
      (by norm_num [residualStage, UnequalParameters.gap, agreements, w]) hregSum
  have hregularUnion : (Finset.univ.biUnion fun F : RegularIndex Q =>
      regularPairSeeds Q T selected seeds F).card ≤
        residualStage.regularCountCap := Finset.card_biUnion_le.trans hregCap
  have hchain : ∀ F ∈ positiveRFactors Q,
      ∀ j ∈ Finset.Ico 1 (chainLength F),
      (chainSeeds F j selected seeds).card ≤ chainStage.regularCountCap := by
    intro F hF j hj
    obtain ⟨hj1, hjm⟩ := Finset.mem_Ico.mp hj
    exact chainSeeds_card_le chainStage Q F hQ hF j hj1 hjm.le
      weightedB w LB sB 2130706433
      (by norm_num [sB, prime]) (by norm_num [w]) hbox
      (by norm_num [chainStage, UnequalParameters.gap, agreements, w])
      (by norm_num [chainStage, weightedB, w, yB])
      (by norm_num [chainStage, sB]) (by norm_num [chainStage, LB])
      (by norm_num [chainStage, weightedB, w, yB])
      (by norm_num [chainStage, sB]) (by norm_num [chainStage, LB])
      (by norm_num [chainStage, sB]) (by norm_num [chainStage, yB])
      (by norm_num [chainStage, sB]) (by norm_num [chainStage, LB])
      (by norm_num [chainStage, UnequalParameters.mixedCost, LB, yB, sB])
      (by norm_num [chainStage, UnequalParameters.mixedCost, LB, yB, sB])
      (by norm_num [chainStage, UnequalParameters.mixedCost, LB, yB, sB])
      selected seeds nodes x u0 u1 hinj (by simpa [chainStage] using hnodes)
      (by norm_num [chainStage, w]) (by norm_num [chainStage, w])
      (by norm_num [chainStage, w, agreements])
      (by norm_num [chainStage, n, agreements])
      (by simpa [chainStage] using hdegree)
      (by simpa [chainStage] using hagreement)
      (by simpa [chainStage, UnequalParameters.errors] using hno)
  have htail : ∀ F ∈ positiveRFactors Q,
      (tailSeeds F selected seeds).card ≤ tailSingular.countCap := by
    intro F hF
    obtain ⟨hFirr, _hFpos, hFbox⟩ :=
      directFactor_data Q F hQ weightedB w LB sB hbox hF
    have hFsmall : F.degreeOf 2 < 2130706433 := by
      exact (degreeOf_R_le_of_mem_box F weightedB w LB sB hFbox).trans_lt
        (by norm_num [sB])
    have hJ : dR (chainLength F) F ≠ 0 :=
      dR_ne_zero F hFirr.ne_zero 2130706433 hFsmall _ le_rfl
    have hJbox : dR (chainLength F) F ∈
        globalCoefficientBox K tailSingular.D tailSingular.w
          tailSingular.L tailSingular.s := by
      change dR (chainLength F) F ∈
        globalCoefficientBox K weightedB w LB 1
      exact mem_box_slope_one _ weightedB w LB sB
        (dR_mem_box _ F weightedB w LB sB hFbox) (chainLength_spec F)
    refine rfree_seed_count_le tailSingular _ hJ 2130706433 hJbox
      (chainLength_spec F) rfl (by norm_num) (by norm_num [tailSingular, w])
      (by norm_num [tailSingular, w, prime])
      (by norm_num [tailSingular, TightParameters.kappa, weightedB, w])
      (by norm_num [tailSingular, TightParameters.algebraicCap,
        TightParameters.kappa, LB])
      (by norm_num [tailSingular, TightParameters.implicitYCap,
        TightParameters.kappa, weightedB, w])
      (by norm_num [tailSingular, TightParameters.algebraicCap,
        TightParameters.kappa, LB])
      (by norm_num [tailSingular, TightParameters.implicitYCap,
        TightParameters.algebraicCap, TightParameters.kappa, weightedB, w, LB])
      (by norm_num [tailSingular, w, agreements])
      (by norm_num [tailSingular, n, agreements]) selected
      (tailSeeds F selected seeds) nodes x u0 u1 hinj
      (by simpa [tailSingular] using hnodes) ?_ ?_ ?_ ?_
    · intro gamma hg
      exact hdegree gamma (tailSeeds_subset F selected seeds hg)
    · intro gamma hg
      exact (Finset.mem_filter.mp hg).2
    · intro gamma hg
      exact hagreement gamma (tailSeeds_subset F selected seeds hg)
    · exact noLargeSelectedPencil_mono selected seeds _ w (n - agreements)
        (tailSeeds_subset F selected seeds) hno
  have hrfree : (rfreeSeeds Q selected seeds).card ≤ tailSingular.countCap := by
    have hJ := rfreeProduct_ne_zero Q hQ
    have hJbox : rfreeProduct Q ∈
        globalCoefficientBox K tailSingular.D tailSingular.w
          tailSingular.L tailSingular.s := by
      change rfreeProduct Q ∈ globalCoefficientBox K weightedB w LB 1
      exact mem_box_slope_one _ weightedB w LB sB
        (mem_globalCoefficientBox_of_dvd _ Q weightedB w LB sB hQ
          (rfreeProduct_dvd Q hQ) hbox) (rfreeProduct_R_degree Q)
    refine rfree_seed_count_le tailSingular _ hJ 2130706433 hJbox
      (rfreeProduct_R_degree Q) rfl (by norm_num)
      (by norm_num [tailSingular, w])
      (by norm_num [tailSingular, w, prime])
      (by norm_num [tailSingular, TightParameters.kappa, weightedB, w])
      (by norm_num [tailSingular, TightParameters.algebraicCap,
        TightParameters.kappa, LB])
      (by norm_num [tailSingular, TightParameters.implicitYCap,
        TightParameters.kappa, weightedB, w])
      (by norm_num [tailSingular, TightParameters.algebraicCap,
        TightParameters.kappa, LB])
      (by norm_num [tailSingular, TightParameters.implicitYCap,
        TightParameters.algebraicCap, TightParameters.kappa, weightedB, w, LB])
      (by norm_num [tailSingular, w, agreements])
      (by norm_num [tailSingular, n, agreements]) selected
      (rfreeSeeds Q selected seeds) nodes x u0 u1 hinj
      (by simpa [tailSingular] using hnodes) ?_ ?_ ?_ ?_
    · intro gamma hg
      exact hdegree gamma (rfreeSeeds_subset Q selected seeds hg)
    · intro gamma hg
      exact (Finset.mem_filter.mp hg).2
    · intro gamma hg
      exact hagreement gamma (rfreeSeeds_subset Q selected seeds hg)
    · exact noLargeSelectedPencil_mono selected seeds _ w (n - agreements)
        (rfreeSeeds_subset Q selected seeds) hno
  have hfactorLow : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ 7 →
      (factorSingularSeeds F selected seeds).card ≤
        (F.degreeOf 2 - 1) * chainStage.regularCountCap +
          tailSingular.countCap := by
    intro F hF _hd
    apply full_factor_bound_to_degree_bound
    exact factorSingularSeeds_card_le_full F
      (positiveRFactors_spec Q F hF).2.2 selected seeds
      chainStage.regularCountCap tailSingular.countCap (hchain F hF) (htail F hF)
  have hfactorHigh : ∀ F ∈ positiveRFactors Q, 7 < F.degreeOf 2 →
      (factorSingularSeeds F selected seeds).card ≤
        (F.degreeOf 2 - 7) * chainStage.regularCountCap +
          partialSingular7.countCap := by
    intro F hF hd
    apply partial_factor_bound_to_degree_bound
    exact factorSingularSeeds_card_le_partial chainStage partialSingular7 Q F
      hQ hF weightedB w LB sB 7 2130706433
      (by norm_num [sB]) (by norm_num [sB, prime]) (by norm_num [w]) hbox
      (by norm_num) hd
      (by norm_num [chainStage, UnequalParameters.gap, agreements, w])
      (by norm_num [chainStage, weightedB, w, yB])
      (by norm_num [chainStage, sB]) (by norm_num [chainStage, LB])
      (by norm_num [chainStage, weightedB, w, yB])
      (by norm_num [chainStage, sB]) (by norm_num [chainStage, LB])
      (by norm_num [chainStage, sB]) (by norm_num [chainStage, yB])
      (by norm_num [chainStage, sB]) (by norm_num [chainStage, LB])
      (by norm_num [chainStage, UnequalParameters.mixedCost, LB, yB, sB])
      (by norm_num [chainStage, UnequalParameters.mixedCost, LB, yB, sB])
      (by norm_num [chainStage, UnequalParameters.mixedCost, LB, yB, sB])
      rfl rfl rfl rfl
      (by norm_num [partialSingular7]) (by norm_num [partialSingular7, w])
      (by norm_num [partialSingular7, TightParameters.kappa, weightedB, w])
      (by norm_num [partialSingular7, TightParameters.algebraicCap,
        TightParameters.kappa, LB])
      (by norm_num [partialSingular7, TightParameters.implicitYCap,
        TightParameters.kappa, weightedB, w])
      (by norm_num [partialSingular7, TightParameters.algebraicCap,
        TightParameters.kappa, LB])
      (by norm_num [partialSingular7, TightParameters.implicitYCap,
        TightParameters.algebraicCap, TightParameters.kappa, weightedB, w, LB])
      (by norm_num [partialSingular7, w, agreements])
      (by norm_num [partialSingular7, n, agreements]) selected seeds
      nodes x u0 u1 hinj (by simpa [chainStage] using hnodes)
      (by simpa [partialSingular7] using hnodes)
      (by norm_num [chainStage, w]) (by norm_num [chainStage, w])
      (by norm_num [chainStage, w, agreements])
      (by norm_num [chainStage, n, agreements])
      (by simpa [chainStage] using hdegree)
      (by simpa [partialSingular7] using hdegree)
      (by simpa [chainStage] using hagreement)
      (by simpa [partialSingular7] using hagreement)
      (by simpa [chainStage, UnequalParameters.errors] using hno)
      (by simpa [partialSingular7, TightParameters.errors] using hno)
  have hdegreeSum :=
    (directFactor_input_budgets Q hQ weightedB w LB sB (by norm_num [w]) hbox).2.1
  have h := residual_card_le_target25_stop7 Q T hQ selected seeds
    residualStage.regularCountCap hQsolution hTsolution hregularUnion hrfree
    hfactorLow hfactorHigh hdegreeSum
  simpa [residualCap, sB] using Nat.lt_succ_iff.mpr h

theorem gcd_residual_count_lt
    [GCDMonoid (MvPolynomial (Fin 4) K)]
    (QA QB:MvPolynomial (Fin 4) K) (hQA:QA ≠ 0) (hQB:QB ≠ 0)
    (hboxA:QA ∈ RCN100.globalCoefficientBox K weightedC w LC sC)
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
      seeds QA QB).card < residualCap + 1:=by
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
    QA H T weightedC w LC sC 0 0 0 hQA hH hT hboxA hTeq
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have hQbox:Q ∈ globalCoefficientBox K weightedB w LB sB:=
    RCN101.flag_box_to_ordinary K
      weightedB w LB sB Q (by simpa only [Nat.sub_zero] using hQflag)
  have hTbox:T ∈ globalCoefficientBox K weightedC w LC sC:=
    RCN101.flag_box_to_ordinary K
      weightedC w LC sC T (by simpa only [Nat.sub_zero] using hTflag)
  have hTcaps:=RCN081.degree_bounds_of_mem_box
    T weightedC w LC sC (by decide) hTbox
  have hTcaps':T.degreeOf 1 ≤ yC ∧ T.degreeOf 2 ≤ sC ∧ T.degreeOf 3 ≤ LC:=
    ⟨hTcaps.1.trans (by norm_num [weightedC, w, yC]), hTcaps.2⟩
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
    (firstQuotients_isRelPrime hQA).symm hQbox hTcaps' selected Delta
    nodes x u0 u1 hinj hnodes
    (fun gamma hg=> hdegree gamma (hsub hg))
    (fun gamma hg=> (hsol gamma hg).2) (fun gamma hg=> (hsol gamma hg).1)
    (fun gamma hg=> hagreement gamma (hsub hg))
    (noLargeSelectedPencil_mono selected seeds Delta w (n - agreements) hsub hno)
end
end ProximityPrize.SubmissionLower.LocatorResidual
