import ProximityPrize.SubmissionLower.LocatorSelectedCaps6803
import ProximityPrize.SubmissionLower.LocatorCaps6803
import ProximityPrize.SubmissionLower.LocatorFixedBridgeDirect6803
import ProximityPrize.SubmissionLower.LocatorFixedBridgeOwnBound6803
import ProximityPrize.SubmissionLower.LocatorFixedCorrelatedBridge6803
import ProximityPrize.SubmissionLower.LocatorFixedGrouped6803
import ProximityPrize.SubmissionLower.LocatorResidualBridge6803
import ProximityPrize.SubmissionLower.LocatorResidualCharge6803
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptSemantic
import ProximityPrize.SubmissionLower.LocatorCoupledClose6803

/-!
# End-to-end 68.03 locator certificate

The fixed and residual populations are kept correlated through the aggregate
flag of the A-universal factors.  This is the only state passed to the checked
receipt and to the retained quotient boxes.
-/

namespace ProximityPrize.SubmissionLower.LocatorFinalCore6803

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN052 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN167
  RCN174 RCN180 RCN234 RCN238 RCN243 RCN259 RCN266 RCN319
open LocatorSelection6803 LocatorFactorAggregate LocatorBatchProductRoute
  LocatorBatchPhase6803 LocatorFixedBridge6803
  LocatorFixedCorrelatedBridge6803 LocatorGroupedNonRegularAssembly6803
  LocatorGroupedCoverCardinality6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 200000

abbrev K := LocatorSelection6803.K
abbrev I := LocatorSelection6803.I
abbrev P4 := LocatorSelection6803.P4

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (Polynomial K) := Classical.decEq (Polynomial K)
local instance : GCDMonoid P4 :=
  UniqueFactorizationMonoid.toGCDMonoid P4
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- Receipt-independent form of the sole inner combinatorial obligation. -/
def SelectedPairCountBound : Prop :=
  ∀ (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (seeds : Finset K),
    (∀ gamma ∈ seeds, (selected gamma).natDegree ≤ 131071) →
    (∀ gamma ∈ seeds, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card) →
    NoLargeSelectedPencil selected seeds 131071 80781 →
    seeds.card < LocatorProtocol6803.mcaBudget

theorem selected_pair_count_bound
    (checkedRows : LocatorPhase6803ReceiptSemantic.CheckedRows)
    (baseSound : LocatorPhase6803SemanticOracle.StateLocalBaseOracleSound
      LocatorPhase6803ReceiptSemantic.checkedBaseCap) :
    SelectedPairCountBound := by
  intro u0 u1 S selected seeds hdegree hagreement hno
  let H : P4 := gcd12 S.QA S.QB
  let phi : K → P4 →+* Polynomial K := fun gamma ↦
    (specialization K (selected gamma) gamma).toRingHom
  let fixed := LocatorCover.fixed phi seeds S.QA S.QB
  let residual := LocatorCover.residual phi seeds S.QA S.QB
  let U := initialAUniversalFactors u0 u1 H
  let P := regularProduct H U
  let p := regularAggregateFlag H U

  have hH : H ≠ 0 := by
    simpa only [H, gcd12] using S.common_ne
  have hwide : ResidualSupportData wideSupport H := ⟨
    by simpa only [H, gcd12] using S.common_slope_le,
    by simpa only [H, gcd12] using S.common_ys_le,
    by simpa only [H, gcd12] using S.common_total_le⟩
  have hHBox : H ∈ globalCoefficientBox K 20131293 131071 14261 34 := by
    simpa only [H, gcd12] using S.common_B_box
  have hcontact : wt (contactWeights 131071) H ≤ 20131292 := by
    have hc := (mem_flagGlobalCoefficientBox_iff H
      20131293 131071 14261 34 (by decide)).mp hHBox
    exact hc.2.2

  have hfixedSub : fixed ⊆ seeds := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).1
  have hresidualSub : residual ⊆ seeds := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).1
  have hdegreeFixed : ∀ gamma ∈ fixed,
      (selected gamma).natDegree ≤ 131071 :=
    fun gamma hgamma ↦ hdegree gamma (hfixedSub hgamma)
  have hagreementFixed : ∀ gamma ∈ fixed, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card :=
    fun gamma hgamma ↦ hagreement gamma (hfixedSub hgamma)
  have hnoFixed : NoLargeSelectedPencil selected fixed 131071 80781 :=
    RCN243.noLargeSelectedPencil_mono selected seeds fixed
      131071 80781 hfixedSub hno
  have hdegreeResidual : ∀ gamma ∈ residual,
      (selected gamma).natDegree ≤ 131071 :=
    fun gamma hgamma ↦ hdegree gamma (hresidualSub hgamma)
  have hagreementResidual : ∀ gamma ∈ residual, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card :=
    fun gamma hgamma ↦ hagreement gamma (hresidualSub hgamma)
  have hnoResidual : NoLargeSelectedPencil selected residual 131071 80781 :=
    RCN243.noLargeSelectedPencil_mono selected seeds residual
      131071 80781 hresidualSub hno

  have hPne : P ≠ 0 := by
    simpa only [P, U] using regularProduct_ne_zero H
      (initialAUniversalFactors u0 u1 H)
  have hdivA : ∀ v : AKernel u0 u1,
      P ∣ reconstruct K 17773574 131071 130000 29 v.1 := by
    simpa only [P, U] using initialAUniversalProduct_dvd u0 u1 H
  have hPMiddle : wt residualYSWeights P ≤ 135 :=
    LocatorCaps6803.common_A_ys_le u0 u1 P hPne hdivA
  have hPSlope : wt residualSWeights P ≤ 29 :=
    LocatorCaps6803.common_A_slope_le u0 u1 P hPne hdivA
  have hretained := initialA_retained_data u0 u1 H hH
    hwide.total_weight
    (by simpa only [P, U] using hPMiddle)
    (by simpa only [P, U] using hPSlope)
  have hPdvd : P ∣ H := by simpa only [P, U, p] using hretained.2.1
  have hpEq : originalCumulativeFlag P = p := by
    simpa only [P, U, p] using hretained.2.2.1
  have hpS : p.all ≤ 29 := by
    simpa only [P, U, p] using hretained.2.2.2.1
  have hpY : middle p ≤ 135 := by
    simpa only [P, U, p] using hretained.2.2.2.2.1
  have hpT : total p ≤ 6676 := by
    simpa only [P, U, p] using hretained.2.2.2.2.2

  have hown : ∀ F ∈ U, LocatorHybridCost.OwnBound
      (regularSeeds H selected fixed F).card
      (regularCumulativeFlag H F) := by
    intro F hFU
    exact initialA_universal_ownBound u0 u1 H hH hwide.total_weight
      selected fixed hdegreeFixed hagreementFixed hnoFixed F hFU
  have hphaseOn :=
    (LocatorPhase6803ReceiptSemantic.phaseCertificate checkedRows
      baseSound).stateLocalBoundOn
      u0 u1 H selected fixed U hdegreeFixed hagreementFixed hnoFixed hown
  have hphaseU : (∑ F ∈ U, (regularSeeds H selected fixed F).card) ≤
      LocatorCoupledClose6803.phaseCap p := by
    have hraw := hphaseOn U (fun _ hFU ↦ hFU) hpS hpY hpT
    simpa only [LocatorPhase6803ReceiptSemantic.phaseCertificate,
      LocatorCoupledClose6803.phaseCap] using hraw
  have houtside : ∀ F ∈
      (Finset.univ : Finset (RegularIndex H)) \ U,
      (regularSeeds H selected fixed F).card ≤
        initialAHelperCap (regularCumulativeFlag H F) := by
    intro F hFN
    apply initialA_nonuniversal_count u0 u1 H hH hwide
      selected fixed hdegreeFixed hagreementFixed hnoFixed F
    exact (Finset.mem_sdiff.mp hFN).2
  have hregular : (∑ F : RegularIndex H,
      (regularSeeds H selected fixed F).card) ≤
      LocatorCoupledClose6803.phaseCap p +
        LocatorPhase6803ReceiptCore.initialAComplement p := by
    have hraw := initialA_regular_sum_le u0 u1 H hH hwide
      selected fixed LocatorCoupledClose6803.phaseCap
      (by simpa only [U, p] using hphaseU)
      (by simpa only [U] using houtside)
    simpa only [U, p] using hraw

  have hR : ∀ F ∈ positiveRFactors H, F.degreeOf 2 ≤ 34 := by
    intro F hF
    exact (RCN081.degreeOf_le_of_dvd (2 : Fin 4) F H
      (positiveRFactors_spec H F hF).2.1 hH).trans
        ((by
          apply MvPolynomial.degreeOf_le_iff.mpr
          intro d hd
          have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
          rw [weight_fin4] at h
          change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
            MvPolynomial.weightedTotalDegree residualSWeights H at h
          simpa only [Nat.mul_zero, Nat.mul_one, Nat.add_zero,
            Nat.zero_add, RCN234.wt] using h).trans hwide.s_weight)
  have hfixedSolution : ∀ gamma ∈ fixed,
      specialization K (selected gamma) gamma H = 0 := by
    intro gamma hgamma
    change phi gamma H = 0
    simpa only [H] using
      LocatorCover.fixed_vanish phi seeds S.QA S.QB gamma hgamma
  have hgrouped : (allGroupedNonRegularSeeds H selected fixed).card ≤
      142046491699954 :=
    LocatorFixedGrouped6803.fixed_allGroupedNonRegularSeeds_card_le_numeric
      H hH hwide.ys_weight hwide.s_weight hwide.total_weight hcontact
      selected fixed u0 u1 hdegreeFixed hagreementFixed hnoFixed
  have hfixed : fixed.card ≤
      LocatorCoupledClose6803.phaseCap p +
          LocatorPhase6803ReceiptCore.initialAComplement p +
        LocatorCoupledResidualLedger6803.singleAllHGroupedCap := by
    have hraw := fixed_card_le_regular_add_grouped H hH 2130706433 34
      (by decide) hR selected fixed hfixedSolution
      (LocatorCoupledClose6803.phaseCap p +
        LocatorPhase6803ReceiptCore.initialAComplement p)
      142046491699954 hregular hgrouped
    simpa only [LocatorCoupledResidualLedger6803.singleAllHGroupedCap_exact]
      using hraw

  have hparents (gamma : K) (hg : gamma ∈ seeds) :
      specialization K (selected gamma) gamma S.QA = 0 ∧
        specialization K (selected gamma) gamma S.QB = 0 := by
    exact S.universal_vanishing gamma (selected gamma)
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i))
      (hdegree gamma hg) (hagreement gamma hg)
      (fun _ hi ↦ (Finset.mem_filter.mp hi).2)
  have hresidualRaw := LocatorResidualBridge6803.retained_residual_count_le
    S.QA S.QB P S.QA_ne S.QB_ne hPne S.QA_flag S.QB_flag
      (by simpa only [H] using hPdvd) hpS hpY hpT
      selected residual u0 u1 hdegreeResidual hagreementResidual hnoResidual
      (fun gamma hgamma ↦ (hparents gamma (hresidualSub hgamma)).1)
      (fun gamma hgamma ↦ (hparents gamma (hresidualSub hgamma)).2)
  have hresidual : residual.card ≤
      LocatorPhase6803ReceiptCore.residualCharge p.all p.yz p.zOnly := by
    have hraw := hresidualRaw
    dsimp only at hraw
    rw [hpEq, LocatorResidualCharge6803.residual_components_eq_receipt] at hraw
    simpa only [phi, residual] using hraw

  have hpZero : p.all = 0 → p = LocatorPhase6800Oracle.rawFlag 0 0 0 := by
    intro hp0
    have hUempty : U = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro F hFU
      have hsingle : ({F} : Finset (RegularIndex H)) ⊆ U :=
        Finset.singleton_subset_iff.mpr hFU
      have hmono := regularAggregateFlag_mono H hsingle
      have hpositive := regularCumulativeFlag_positive H F
      have : (regularCumulativeFlag H F).all ≤ p.all := by
        simpa [p, regularAggregateFlag, sumFlag] using hmono.1
      omega
    simp [p, hUempty, regularAggregateFlag, sumFlag,
      LocatorPhase6800Oracle.rawFlag]

  have hpartition := LocatorCover.partition_card phi seeds S.QA S.QB
  exact LocatorCoupledClose6803.correlated_partition_lt
    checkedRows p hpS hpY hpT
    fixed.card residual.card seeds.card
    (by simpa only [fixed, residual] using hpartition)
    hfixed hresidual hpZero

end

end ProximityPrize.SubmissionLower.LocatorFinalCore6803
