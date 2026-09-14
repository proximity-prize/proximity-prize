import ProximityPrize.SubmissionLower.HigherCountingArithmetic6810
import ProximityPrize.SubmissionLower.HigherInitial6810
import ProximityPrize.SubmissionLower.BoundaryTailCounting




/-! Shared factor-family counting for the proposed error-80850 profile.
The aggregation framework is adapted from jsign PR506. Its AsymmetricChainPolynomial80850.stage count is
replaced by the checked derivative-carrier numerator and polynomial bound.
This module does not assert a protocol claim. -/

namespace ProximityPrize.SubmissionLower.Lower80850.Counting
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238
  RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open LocatorDerivativeChain BoundaryTailSharedDegreeBudget AsymmetricChainPolynomial80850 BoundaryTailChainHelper AsymmetricHelper
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
local instance : StrongNormalizationMonoid P4 := UniqueFactorizationMonoid.strongNormalizationMonoid

structure Input (u0 u1 : I → K) (selected : K → Polynomial K) (Gamma : Finset K) : Prop where
  degree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071
  agreement : ∀ gamma ∈ Gamma, 181294 ≤ ((Finset.univ : Finset I).filter (fun i =>
    (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma*u1 i)).card
  noPencil : NoLargeSelectedPencil selected Gamma 131071 80850

variable {u0 u1 : I → K} {selected : K → Polynomial K} {Gamma : Finset K}

theorem Input.restrict (inp : Input u0 u1 selected Gamma) (Delta : Finset K) (h : Delta ⊆ Gamma) :
    Input u0 u1 selected Delta :=
  ⟨fun g hg => inp.degree g (h hg), fun g hg => inp.agreement g (h hg),
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80850 h inp.noPencil⟩

def tailParameters : TightParameters := ⟨262144,131071,181294,21573986,38980,1⟩

theorem freePolynomial_count (inp : Input u0 u1 selected Gamma)
    (J : P4) (hJ : J ≠ 0) (hbox : J ∈ RCN174.globalCoefficientBox K 21573986 131071 38980 1)
    (hR : J.degreeOf 2 = 0) (hsol : ∀ g ∈ Gamma, specialization K (selected g) g J = 0) :
    Gamma.card ≤ 13123665506192 := by
  have h := rfree_seed_count_le tailParameters J hJ 2130706433 hbox hR (by rfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [tailParameters, TightParameters.kappa])
    (by norm_num [tailParameters, TightParameters.algebraicCap, TightParameters.kappa])
    (by norm_num [tailParameters, TightParameters.implicitYCap, TightParameters.kappa])
    (by norm_num [tailParameters, TightParameters.algebraicCap, TightParameters.kappa])
    (by norm_num [tailParameters, TightParameters.implicitYCap, TightParameters.algebraicCap, TightParameters.kappa])
    (by decide +kernel) (by decide +kernel) selected Gamma Finset.univ IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn (by rw [Finset.card_univ]; exact Fintype.card_fin _)
    inp.degree hsol inp.agreement (by
      simpa only [tailParameters, TightParameters.errors, (show (262144 - 181294 : ℕ) = 80850 by decide +kernel)] using inp.noPencil)
  have ht : tailParameters.countCap ≤ 13123665506192 := by
    norm_num [tailParameters, TightParameters.countCap, TightParameters.gap,
      TightParameters.errors, TightParameters.kappa, TightParameters.algebraicCap,
      TightParameters.implicitYCap, TightParameters.tightNumerator,
      TightParameters.coreNumerator, TightParameters.agreement,
      TightParameters.aggregateCost, RCN294.dot]
  exact h.trans ht

theorem factor_tail_count (inp : Input u0 u1 selected Gamma)
    (F : P4) (hF : F ≠ 0) (hbox : F ∈ RCN174.globalCoefficientBox K 21573986 131071 38980 37) :
    (tailSeeds F selected Gamma).card ≤ 13123665506192 := by
  have hsmall : F.degreeOf 2 < 2130706433 :=
    (degreeOf_R_le_of_mem_box F 21573986 131071 38980 37 hbox).trans_lt (by decide +kernel)
  have hJ := dR_ne_zero F hF 2130706433 hsmall (chainLength F) le_rfl
  have hb := mem_box_slope_one (dR (chainLength F) F) 21573986 131071 38980 37
    (dR_mem_box _ F 21573986 131071 38980 37 hbox) (chainLength_spec F)
  exact freePolynomial_count (inp.restrict _ (tailSeeds_subset F selected Gamma)) _ hJ hb
    (chainLength_spec F) (fun _ hg => (Finset.mem_filter.mp hg).2)

theorem freePart_count (inp : Input u0 u1 selected Gamma)
    (Q : P4) (hQ : Q ≠ 0) (hbox : Q ∈ RCN174.globalCoefficientBox K 21573986 131071 38980 37) :
    (rfreeSeeds Q selected Gamma).card ≤ 13123665506192 := by
  have hb := mem_box_slope_one (rfreeProduct Q) 21573986 131071 38980 37
    (mem_globalCoefficientBox_of_dvd _ Q 21573986 131071 38980 37 hQ
      (rfreeProduct_dvd Q hQ) hbox) (rfreeProduct_R_degree Q)
  exact freePolynomial_count (inp.restrict _ (rfreeSeeds_subset Q selected Gamma)) _
    (rfreeProduct_ne_zero Q hQ) hb (rfreeProduct_R_degree Q)
    (fun _ hg => (Finset.mem_filter.mp hg).2)

def factorCharge (F : P4) (selected : K → Polynomial K) (Gamma : Finset K) : ℕ :=
  (∑ j ∈ Finset.Ico 1 (chainLength F), (chainSeeds F j selected Gamma).card) +
    (tailSeeds F selected Gamma).card

theorem factorCharge_le_unit (inp : Input u0 u1 selected Gamma)
    (F : P4) (hF : Irreducible F) (hpos : 0 < F.degreeOf 2)
    (hbox : F ∈ RCN174.globalCoefficientBox K 21573986 131071 38980 37)
    (y z r : ℕ) (hy : y ≤ 164) (hz : z ≤ 38980) (hr : r ≤ 37)
    (hFY : F.degreeOf 1 ≤ y) (hFZ : F.degreeOf 3 ≤ z) (hFR : F.degreeOf 2 ≤ r) :
    factorCharge F selected Gamma ≤ F.degreeOf 2 * (unit y z r + 4123665506192) := by
  have hd : F.degreeOf 2 ≤ 37 := hFR.trans hr
  apply BoundaryTailDegreeAwareChain.factor_charge_le F selected Gamma
    (fun j => leftRegularCountCap (AsymmetricChainPolynomial80850.stage y z (F.degreeOf 2) j)) 13123665506192 (unit y z r + 4123665506192)
  · intro j hj
    have hj1 := (Finset.mem_Ico.mp hj).1
    have hjl := (Finset.mem_Ico.mp hj).2
    have hjd : j < F.degreeOf 2 := hjl.trans_le (chainLength_le F)
    have hleft : F.degreeOf 2-j ≤ 37 := (Nat.sub_le _ _).trans hd
    exact BoundaryTailChainHelper.chainSeeds_card_le_left (AsymmetricChainPolynomial80850.stage y z (F.degreeOf 2) j) F hF 2130706433
      hpos (hd.trans_lt (by decide +kernel)) j hj1 hjl.le
      (by norm_num [AsymmetricChainPolynomial80850.stage, UnequalParameters.gap])
      ((dR_degree_le j F 1).trans hFY) le_rfl
      ((dR_degree_le j F 3).trans hFZ) hFY le_rfl hFZ
      (by dsimp [AsymmetricChainPolynomial80850.stage]; omega) (by dsimp [AsymmetricChainPolynomial80850.stage]; omega) (by dsimp [AsymmetricChainPolynomial80850.stage]; omega)
      (by dsimp [AsymmetricChainPolynomial80850.stage]; omega)
      (by
        dsimp [AsymmetricChainPolynomial80850.stage, UnequalParameters.mixedCost]
        exact (Nat.add_le_add (Nat.mul_le_mul hleft hz) (Nat.mul_le_mul hz hd)).trans_lt (by decide +kernel))
      (by
        dsimp [AsymmetricChainPolynomial80850.stage, UnequalParameters.mixedCost]
        exact (Nat.add_le_add (Nat.mul_le_mul hy hz) (Nat.mul_le_mul hz hy)).trans_lt (by decide +kernel))
      (by
        dsimp [AsymmetricChainPolynomial80850.stage, UnequalParameters.mixedCost]
        exact (Nat.add_le_add (Nat.mul_le_mul hy hd) (Nat.mul_le_mul hleft hy)).trans_lt (by decide +kernel))
      selected Gamma Finset.univ IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
      (by rw [Finset.card_univ]; exact Fintype.card_fin _) (by norm_num [AsymmetricChainPolynomial80850.stage]) (by norm_num [AsymmetricChainPolynomial80850.stage]) (by norm_num [AsymmetricChainPolynomial80850.stage]) (by norm_num [AsymmetricChainPolynomial80850.stage])
      inp.degree inp.agreement (by simpa only [AsymmetricChainPolynomial80850.stage, UnequalParameters.errors, (show (262144 - 181294 : ℕ) = 80850 by decide +kernel)] using inp.noPencil)
  · exact factor_tail_count inp F hF.ne_zero hbox
  · have h := charge_le_unit y z (F.degreeOf 2) r hpos hFR hr
    unfold AsymmetricChainPolynomial80850.charge at h
    nlinarith

end
end ProximityPrize.SubmissionLower.Lower80850.Counting



namespace ProximityPrize.SubmissionLower.Lower80850.Budgets
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN266 RCN319
open RCN286 RCN267 RCN180 LocatorBatchProductRoute
open LocatorFactorAggregate LocatorBatchPhase6800 LocatorPhase6800Oracle Counting BoundaryTailSharedDegreeBudget AsymmetricChainPolynomial80850
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

theorem degreeY_le (F : P4) : F.degreeOf 1 ≤ wt residualYSWeights F := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*0 ≤ wt residualYSWeights F at h
  omega

theorem degreeZ_le (F : P4) : F.degreeOf 3 ≤ wt residualTotalWeights F := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*1 ≤ wt residualTotalWeights F at h
  omega

theorem factor_coordinates (H : P4) (A : Finset (RegularIndex H)) (F : RegularIndex H) (hF : F ∈ A) :
    F.1.degreeOf 1 ≤ middle (regularAggregateFlag H A) ∧
    F.1.degreeOf 2 ≤ (regularAggregateFlag H A).all ∧
    F.1.degreeOf 3 ≤ total (regularAggregateFlag H A) := by
  have hm := regularAggregateFlag_mono H (Finset.singleton_subset_iff.mpr hF)
  have hc := originalCumulativeFlag_cumulative F.1
  have hy : F.1.degreeOf 1 ≤ middle (regularCumulativeFlag H F) := by
    rw [regularCumulativeFlag, middle, hc.2.1]
    exact degreeY_le F.1
  have hz : F.1.degreeOf 3 ≤ total (regularCumulativeFlag H F) := by
    rw [regularCumulativeFlag, total, hc.2.2]
    exact degreeZ_le F.1
  have hr : F.1.degreeOf 2 = (regularCumulativeFlag H F).all := by
    rw [regularCumulativeFlag, originalCumulativeFlag_all]
  simpa only [regularAggregateFlag, sumFlag, Finset.sum_singleton] using
    And.intro (hy.trans hm.2.1) (And.intro (hr.le.trans hm.1) (hz.trans hm.2.2))

theorem aggregate_pair_weight (H Q : P4) (hH : H ≠ 0) (hQ : Q ≠ 0) (weights : Fin 4 → ℕ) :
    wt weights (regularProduct H Finset.univ) + wt weights (regularProduct Q Finset.univ) ≤
      wt weights (H*Q) := by
  simp only [wt]
  rw [weightedTotalDegree_mul weights H Q hH hQ]
  exact Nat.add_le_add
    (weightedTotalDegree_le_of_dvd weights _ H (regularProduct_dvd_carrier H _) hH)
    (weightedTotalDegree_le_of_dvd weights _ Q (regularProduct_dvd_carrier Q _) hQ)

theorem aggregate_pair_caps (H Q : P4) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hbox : H*Q ∈ RCN100.globalCoefficientBox K 21573986 131071 38980 37) :
    (regularAggregateFlag H Finset.univ).all+(regularAggregateFlag Q Finset.univ).all ≤ 37 ∧
    middle (regularAggregateFlag H Finset.univ)+middle (regularAggregateFlag Q Finset.univ) ≤ 164 ∧
    total (regularAggregateFlag H Finset.univ)+total (regularAggregateFlag Q Finset.univ) ≤ 38980 := by
  have hc := (mem_flagGlobalCoefficientBox_iff (H*Q) 21573986 131071 38980 37 (by decide +kernel)).mp hbox
  have hw := residualYS_mul_le_contact_add_slope (H*Q) 131071 (by decide +kernel)
  have hy : wt residualYSWeights (H*Q) ≤ 164 := by omega
  rw [regularAggregateFlag_all, regularAggregateFlag_all,
    regularAggregateFlag_middle, regularAggregateFlag_middle,
    regularAggregateFlag_total, regularAggregateFlag_total]
  exact ⟨(aggregate_pair_weight H Q hH hQ _).trans hc.2.1,
    (aggregate_pair_weight H Q hH hQ _).trans hy,
    (aggregate_pair_weight H Q hH hQ _).trans hc.1⟩

theorem split_aggregate (H : P4) (U : Finset (RegularIndex H)) :
    let N := (Finset.univ : Finset (RegularIndex H)) \ U
    (regularAggregateFlag H U).all+(regularAggregateFlag H N).all = (regularAggregateFlag H Finset.univ).all ∧
    middle (regularAggregateFlag H U)+middle (regularAggregateFlag H N) = middle (regularAggregateFlag H Finset.univ) ∧
    total (regularAggregateFlag H U)+total (regularAggregateFlag H N) = total (regularAggregateFlag H Finset.univ) := by
  simp only [regularAggregateFlag, sumFlag_all, sumFlag_middle, sumFlag_total]
  exact ⟨by rw [Nat.add_comm]; exact Finset.sum_sdiff (Finset.subset_univ _),
    by rw [Nat.add_comm]; exact Finset.sum_sdiff (Finset.subset_univ _),
    by rw [Nat.add_comm]; exact Finset.sum_sdiff (Finset.subset_univ _)⟩

theorem joint_charge (H Q : P4) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hbox : H*Q ∈ RCN100.globalCoefficientBox K 21573986 131071 38980 37)
    (hHbox : H ∈ RCN174.globalCoefficientBox K 21573986 131071 38980 37)
    (hQbox : Q ∈ RCN174.globalCoefficientBox K 21573986 131071 38980 37)
    (U : Finset (RegularIndex H)) (u0 u1 : I → K) (selected : K → Polynomial K)
    (Gamma Delta : Finset K) (inpH : Input u0 u1 selected Gamma) (inpQ : Input u0 u1 selected Delta)
    (hr : (regularAggregateFlag H U).all ≤ 34)
    (hy : middle (regularAggregateFlag H U) ≤ 156)
    (ht : total (regularAggregateFlag H U) ≤ 8865) :
    let p := regularAggregateFlag H U
    (∑ F : RegularIndex H, factorCharge F.1 selected Gamma) +
      (∑ F : RegularIndex Q, factorCharge F.1 selected Delta) ≤
      p.all*unit (middle p) (total p) p.all +
      (37-p.all)*unit (164-middle p) (38980-total p) (37-p.all) + 37*4123665506192 := by
  let p := regularAggregateFlag H U
  let N := (Finset.univ : Finset (RegularIndex H)) \ U
  have hb := aggregate_pair_caps H Q hH hQ hbox
  have hs := split_aggregate H U
  have hnR : (regularAggregateFlag H N).all ≤ 37-p.all := by dsimp only [p,N]; omega
  have hnY : middle (regularAggregateFlag H N) ≤ 164-middle p := by dsimp only [p,N]; omega
  have hnT : total (regularAggregateFlag H N) ≤ 38980-total p := by dsimp only [p,N]; omega
  have hqR : (regularAggregateFlag Q Finset.univ).all ≤ 37-p.all := by dsimp only [p]; omega
  have hqY : middle (regularAggregateFlag Q Finset.univ) ≤ 164-middle p := by dsimp only [p]; omega
  have hqT : total (regularAggregateFlag Q Finset.univ) ≤ 38980-total p := by dsimp only [p]; omega
  have hsum : (∑ F ∈ U, F.1.degreeOf 2) = p.all := by
    simp only [p, regularAggregateFlag, sumFlag_all, regularCumulativeFlag, originalCumulativeFlag_all]
  have hprodBox := RCN101.flag_box_to_ordinary K 21573986 131071 38980 37 (H*Q) hbox
  have hc := split_slope_charge (Finset.univ : Finset (RegularIndex H)) U
    (Finset.univ : Finset (RegularIndex Q)) (Finset.subset_univ _) (fun F => F.1) (fun F => F.1)
    H Q hH hQ (regularProduct_dvd_carrier H _) (regularProduct_dvd_carrier Q _)
    37 (unit (middle p) (total p) p.all + 4123665506192) (unit (164-middle p) (38980-total p) (37-p.all) + 4123665506192)
    (degreeOf_R_le_of_mem_box (H*Q) 21573986 131071 38980 37 hprodBox)
    (fun F => factorCharge F.1 selected Gamma) (fun F => factorCharge F.1 selected Delta)
    (fun F hF => by
      have hf := directFactor_data H F.1 hH 21573986 131071 38980 37 hHbox F.2
      have hd := factor_coordinates H U F hF
      exact factorCharge_le_unit inpH F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (hy.trans (by decide +kernel)) (ht.trans (by decide +kernel)) (hr.trans (by decide +kernel)) hd.1 hd.2.2 hd.2.1)
    (fun F hF => by
      have hf := directFactor_data H F.1 hH 21573986 131071 38980 37 hHbox F.2
      have hd := factor_coordinates H N F hF
      exact factorCharge_le_unit inpH F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
        (hd.1.trans hnY) (hd.2.2.trans hnT) (hd.2.1.trans hnR))
    (fun F _ => by
      have hf := directFactor_data Q F.1 hQ 21573986 131071 38980 37 hQbox F.2
      have hd := factor_coordinates Q Finset.univ F (Finset.mem_univ _)
      exact factorCharge_le_unit inpQ F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
        (hd.1.trans hqY) (hd.2.2.trans hqT) (hd.2.1.trans hqR))
  rw [hsum] at hc
  have hp : p.all + (37-p.all) = 37 := by dsimp only [p]; omega
  calc
    _ ≤ _ := hc
    _ = p.all*unit (middle p) (total p) p.all +
        (37-p.all)*unit (164-middle p) (38980-total p) (37-p.all) +
          (p.all+(37-p.all))*4123665506192 := by ring
    _ = _ := by rw [hp]

end
end ProximityPrize.SubmissionLower.Lower80850.Budgets
