import ProximityPrize.SubmissionLower.MovingFiberCountingArithmetic6815
import ProximityPrize.SubmissionLower.MovingFiberInitialCore6815
import ProximityPrize.SubmissionLower.BoundaryTailCounting
namespace ProximityPrize.SubmissionLower.Lower80899.Counting
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open LocatorDerivativeChain BoundaryTailSharedDegreeBudget AsymmetricChainPolynomial80899 BoundaryTailChainHelper AsymmetricHelper
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
  agreement : ∀ gamma ∈ Gamma, 181245 ≤ ((Finset.univ : Finset I).filter (fun i =>
    (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma*u1 i)).card
  noPencil : NoLargeSelectedPencil selected Gamma 131071 80899

variable {u0 u1 : I → K} {selected : K → Polynomial K} {Gamma : Finset K}

theorem Input.restrict (inp : Input u0 u1 selected Gamma) (Delta : Finset K) (h : Delta ⊆ Gamma) :
    Input u0 u1 selected Delta :=
  ⟨fun g hg => inp.degree g (h hg), fun g hg => inp.agreement g (h hg),
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80899 h inp.noPencil⟩

def tailParameters : TightParameters := ⟨262144,131071,181245,30086670,15421,1⟩

theorem freePolynomial_count (inp : Input u0 u1 selected Gamma)
    (J : P4) (hJ : J ≠ 0) (hbox : J ∈ RCN174.globalCoefficientBox K 30086670 131071 15421 1)
    (hR : J.degreeOf 2 = 0) (hsol : ∀ g ∈ Gamma, specialization K (selected g) g J = 0) :
    Gamma.card ≤ 9000000000000+0 := by
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
      simpa only [tailParameters, TightParameters.errors, (show (262144 - 181245 : ℕ) = 80899 by decide +kernel)] using inp.noPencil)
  have ht : tailParameters.countCap ≤ 9000000000000+0 := by
    norm_num [tailParameters, TightParameters.countCap, TightParameters.gap,
      TightParameters.errors, TightParameters.kappa, TightParameters.algebraicCap,
      TightParameters.implicitYCap, TightParameters.tightNumerator,
      TightParameters.coreNumerator, TightParameters.agreement,
      TightParameters.aggregateCost, RCN294.dot]
  exact h.trans ht

theorem factor_tail_count (inp : Input u0 u1 selected Gamma)
    (F : P4) (hF : F ≠ 0) (hbox : F ∈ RCN174.globalCoefficientBox K 30086670 131071 15421 50) :
    (tailSeeds F selected Gamma).card ≤ 9000000000000+0 := by
  have hsmall : F.degreeOf 2 < 2130706433 :=
    (degreeOf_R_le_of_mem_box F 30086670 131071 15421 50 hbox).trans_lt (by decide +kernel)
  have hJ := dR_ne_zero F hF 2130706433 hsmall (chainLength F) le_rfl
  have hb := mem_box_slope_one (dR (chainLength F) F) 30086670 131071 15421 50
    (dR_mem_box _ F 30086670 131071 15421 50 hbox) (chainLength_spec F)
  exact freePolynomial_count (inp.restrict _ (tailSeeds_subset F selected Gamma)) _ hJ hb
    (chainLength_spec F) (fun _ hg => (Finset.mem_filter.mp hg).2)

theorem freePart_count (inp : Input u0 u1 selected Gamma)
    (Q : P4) (hQ : Q ≠ 0) (hbox : Q ∈ RCN174.globalCoefficientBox K 30086670 131071 15421 50) :
    (rfreeSeeds Q selected Gamma).card ≤ 9000000000000+0 := by
  have hb := mem_box_slope_one (rfreeProduct Q) 30086670 131071 15421 50
    (mem_globalCoefficientBox_of_dvd _ Q 30086670 131071 15421 50 hQ
      (rfreeProduct_dvd Q hQ) hbox) (rfreeProduct_R_degree Q)
  exact freePolynomial_count (inp.restrict _ (rfreeSeeds_subset Q selected Gamma)) _
    (rfreeProduct_ne_zero Q hQ) hb (rfreeProduct_R_degree Q)
    (fun _ hg => (Finset.mem_filter.mp hg).2)

end
end ProximityPrize.SubmissionLower.Lower80899.Counting

namespace ProximityPrize.SubmissionLower.Lower80899.Budgets
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN266 RCN319
open RCN286 RCN267 RCN180 LocatorBatchProductRoute
open LocatorFactorAggregate LocatorBatchPhase6800 LocatorPhase6800Oracle Counting BoundaryTailSharedDegreeBudget AsymmetricChainPolynomial80899
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
    (hbox : H*Q ∈ RCN100.globalCoefficientBox K 30086670 131071 15421 50) :
    (regularAggregateFlag H Finset.univ).all+(regularAggregateFlag Q Finset.univ).all ≤ 50 ∧
    middle (regularAggregateFlag H Finset.univ)+middle (regularAggregateFlag Q Finset.univ) ≤ 229 ∧
    total (regularAggregateFlag H Finset.univ)+total (regularAggregateFlag Q Finset.univ) ≤ 15421 := by
  have hc := (mem_flagGlobalCoefficientBox_iff (H*Q) 30086670 131071 15421 50 (by decide +kernel)).mp hbox
  have hw := residualYS_mul_le_contact_add_slope (H*Q) 131071 (by decide +kernel)
  have hy : wt residualYSWeights (H*Q) ≤ 229 := by omega
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

end
end ProximityPrize.SubmissionLower.Lower80899.Budgets
