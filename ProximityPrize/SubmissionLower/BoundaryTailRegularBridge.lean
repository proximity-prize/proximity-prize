import ProximityPrize.SubmissionLower.BoundaryTailInitial
import ProximityPrize.SubmissionLower.BoundaryTailCounting
import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics

namespace ProximityPrize.SubmissionLower.Lower80801.RegularBridge
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN259 RCN260 RCN266 RCN275 RCN319
open Lower80801.Selection Lower80801.InitialBridge Lower80801.Initial
open LocatorFactorAggregate LocatorBatchProductRoute
open LocatorBatchPhase6800 (regularAggregateFlag regularAggregateFlag_total
  regularAggregateFlag_middle regularAggregateFlag_all regularAggregateFlag_mono)
open LocatorPhase6800Oracle (sumFlag sumFlag_total sumFlag_middle sumFlag_all)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4
private theorem whole_regular_total_le
    (H : P4) (hH : H ≠ 0) (T : ℕ)
    (hT : wt residualTotalWeights H ≤ T) :
    total (regularAggregateFlag H
      (Finset.univ : Finset (RegularIndex H))) ≤ T := by
  rw [regularAggregateFlag_total]
  exact (weightedTotalDegree_le_of_dvd residualTotalWeights
    (regularProduct H (Finset.univ : Finset (RegularIndex H))) H
    (regularProduct_dvd_carrier H Finset.univ) hH).trans hT

private theorem whole_regular_middle_le
    (H : P4) (hH : H ≠ 0) (YS : ℕ)
    (hYS : wt residualYSWeights H ≤ YS) :
    middle (regularAggregateFlag H
      (Finset.univ : Finset (RegularIndex H))) ≤ YS := by
  rw [regularAggregateFlag_middle]
  exact (weightedTotalDegree_le_of_dvd residualYSWeights
    (regularProduct H (Finset.univ : Finset (RegularIndex H))) H
    (regularProduct_dvd_carrier H Finset.univ) hH).trans hYS

private theorem whole_regular_all_le
    (H : P4) (hH : H ≠ 0) (S : ℕ)
    (hS : wt residualSWeights H ≤ S) :
    (regularAggregateFlag H
      (Finset.univ : Finset (RegularIndex H))).all ≤ S := by
  rw [regularAggregateFlag_all]
  exact (weightedTotalDegree_le_of_dvd residualSWeights
    (regularProduct H (Finset.univ : Finset (RegularIndex H))) H
    (regularProduct_dvd_carrier H Finset.univ) hH).trans hS

theorem regular_count
    {zero : ℕ → ℕ → ℕ} {split : FlagDegree → ℕ}
    (hbaseReceipt : BoundaryTailBaseOracle.Receipt zero split (PhaseSemantics.phaseCap 0))
    (hpref : PhaseSemantics.PrefixReceiptSound)
    (hthreshold : PhaseSemantics.ThresholdReceiptSound)
    (hruns : PhaseSemantics.RunReceiptSound)
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K) (inp : Counting.Input u0 u1 selected Gamma) :
    let H : P4 := gcd12 S.QA S.QB
    let phi : K → P4 →+* Polynomial K := fun g => (specialization K (selected g) g).toRingHom
    let Delta := LocatorCover.fixed phi Gamma S.QA S.QB
    let U := initialAUniversalFactors u0 u1 H
    let p := regularAggregateFlag H U
    p.all ≤ 30 ∧ middle p ≤ 139 ∧ total p ≤ 7199 ∧
      (∑ F : RegularIndex H, (regularSeeds H selected Delta F).card) ≤
        PhaseSemantics.phaseCap 6 p + initialAComplement p := by
  classical
  let H : P4 := gcd12 S.QA S.QB
  let phi : K → P4 →+* Polynomial K :=
    fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom
  let Delta : Finset K := LocatorCover.fixed phi Gamma S.QA S.QB
  let U := initialAUniversalFactors u0 u1 H
  let A := (Finset.univ : Finset (RegularIndex H))
  let N := A \ U
  let p := regularAggregateFlag H U
  have hH : H ≠ 0 := by
    simpa only [H, gcd12] using gcd_ne_zero_of_left S.QA_ne
  have hUsub : U ⊆ A := fun _ _ ↦ Finset.mem_univ _
  have hPne : regularProduct H U ≠ 0 := regularProduct_ne_zero H U
  have hdivA : ∀ v : Caps.AKernel u0 u1,
      regularProduct H U ∣
        reconstruct K 18315643 131071 350390 30 v.1 := by
    simpa only [U] using initialAUniversalProduct_dvd u0 u1 H
  have hpS : p.all ≤ 30 := by
    simp only [p, regularAggregateFlag_all]
    exact Caps.common_A_slope_le u0 u1 (regularProduct H U)
      hPne hdivA
  have hpY : middle p ≤ 139 := by
    simp only [p, regularAggregateFlag_middle]
    exact Caps.common_A_ys_le u0 u1 (regularProduct H U)
      hPne hdivA
  have hpT : total p ≤ 7199 := by
    simp only [p, regularAggregateFlag_total]
    exact (weightedTotalDegree_le_of_dvd residualTotalWeights
      (regularProduct H U) H
      (initialAUniversalProduct_dvd_carrier u0 u1 H) hH).trans
        S.common_total_le
  have hwholeT : total (regularAggregateFlag H A) ≤ 7199 := by
    simpa only [H, A] using
      whole_regular_total_le H hH 7199 S.common_total_le
  have hwholeY : middle (regularAggregateFlag H A) ≤ 153 := by
    simpa only [H, A] using
      whole_regular_middle_le H hH 153 S.common_ys_le
  have hwholeS : (regularAggregateFlag H A).all ≤ 33 := by
    simpa only [H, A] using
      whole_regular_all_le H hH 33 S.common_slope_le
  have hsplitT := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H => total (regularCumulativeFlag H F))
  have hsplitY := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H => middle (regularCumulativeFlag H F))
  have hsplitS := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H => (regularCumulativeFlag H F).all)
  have hcomplementT : total p +
      (∑ F ∈ N, total (regularCumulativeFlag H F)) ≤ 7199 := by
    have hpEq : total p =
        ∑ F ∈ U, total (regularCumulativeFlag H F) := by
      simp only [p, regularAggregateFlag, sumFlag_total]
    have hwhole : (∑ F ∈ A, total (regularCumulativeFlag H F)) ≤
        7199 := by
      simpa only [regularAggregateFlag, sumFlag_total] using hwholeT
    rw [hpEq]
    change (∑ F ∈ U, total (regularCumulativeFlag H F)) +
      (∑ F ∈ A \ U, total (regularCumulativeFlag H F)) ≤ 7199
    omega
  have hcomplementY : middle p +
      (∑ F ∈ N, middle (regularCumulativeFlag H F)) ≤ 153 := by
    have hpEq : middle p =
        ∑ F ∈ U, middle (regularCumulativeFlag H F) := by
      simp only [p, regularAggregateFlag, sumFlag_middle]
    have hwhole : (∑ F ∈ A, middle (regularCumulativeFlag H F)) ≤
        153 := by
      simpa only [regularAggregateFlag, sumFlag_middle] using hwholeY
    rw [hpEq]
    change (∑ F ∈ U, middle (regularCumulativeFlag H F)) +
      (∑ F ∈ A \ U, middle (regularCumulativeFlag H F)) ≤ 153
    omega
  have hcomplementS : p.all +
      (∑ F ∈ N, (regularCumulativeFlag H F).all) ≤ 33 := by
    have hpEq : p.all =
        ∑ F ∈ U, (regularCumulativeFlag H F).all := by
      simp only [p, regularAggregateFlag, sumFlag_all]
    have hwhole : (∑ F ∈ A, (regularCumulativeFlag H F).all) ≤ 33 := by
      simpa only [regularAggregateFlag, sumFlag_all] using hwholeS
    rw [hpEq]
    change (∑ F ∈ U, (regularCumulativeFlag H F).all) +
      (∑ F ∈ A \ U, (regularCumulativeFlag H F).all) ≤ 33
    omega
  have hNpotential : ∀ F ∈ N,
      initialAHelperCap (regularCumulativeFlag H F) ≤
        initialAPotential.eval (regularCumulativeFlag H F) := by
    intro F hFN
    have hFA : F ∈ A := (Finset.mem_sdiff.mp hFN).1
    have hsingle : ({F} : Finset (RegularIndex H)) ⊆ A :=
      Finset.singleton_subset_iff.mpr hFA
    have hmono := regularAggregateFlag_mono H hsingle
    have hr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    apply Initial.initialA_majorant (regularCumulativeFlag H F) hr
    · simpa [regularAggregateFlag, sumFlag] using hmono.1.trans hwholeS
    · simpa [regularAggregateFlag, sumFlag] using hmono.2.1.trans hwholeY
    · simpa [regularAggregateFlag, sumFlag] using hmono.2.2.trans hwholeT
  have hhelperSum :
      (∑ F ∈ N, initialAHelperCap (regularCumulativeFlag H F)) ≤
        initialAComplement p := by
    exact initialA_helpers_sum_le_complement N (regularCumulativeFlag H)
      (fun F ↦ initialAHelperCap (regularCumulativeFlag H F)) p
      hNpotential hcomplementT hcomplementY hcomplementS
  have hsub : Delta ⊆ Gamma := by
    intro g hg
    have hm : g ∈ Gamma ∧ (phi g) (gcd12 S.QA S.QB) = 0 := by
      simpa only [Delta, LocatorCover.fixed, Finset.mem_filter] using hg
    exact hm.1
  have inpD := inp.restrict Delta hsub
  have hwide : ResidualSupportData InitialSupports.wideSupport H :=
    ⟨S.common_slope_le,S.common_ys_le,S.common_total_le⟩
  have hsingle := initialA_universal_singleBound u0 u1 H hH S.common_total_le
    selected Delta inpD.degree inpD.agreement inpD.noPencil
  have hbase := PhaseSemantics.stateLocalRegularBoundOn_of_base hbaseReceipt
    H selected Delta U hsingle
  have hphase := PhaseSemantics.bound_all hpref hthreshold hruns u0 u1 H selected Delta U
    inpD.degree inpD.agreement inpD.noPencil hbase 6 le_rfl
  have hphaseU : (∑ F ∈ U, (regularSeeds H selected Delta F).card) ≤ PhaseSemantics.phaseCap 6 p :=
    hphase U (fun _ h => h) hpS hpY hpT
  have hN : (∑ F ∈ N, (regularSeeds H selected Delta F).card) ≤ initialAComplement p := by
    apply le_trans (Finset.sum_le_sum (fun F hF => ?_)) hhelperSum
    exact initialA_nonuniversal_count u0 u1 H hH hwide selected Delta
      inpD.degree inpD.agreement inpD.noPencil F (Finset.mem_sdiff.mp hF).2
  have he := Finset.sum_sdiff hUsub (f := fun F => (regularSeeds H selected Delta F).card)
  refine ⟨hpS,hpY,hpT,?_⟩
  change (∑ F ∈ A, (regularSeeds H selected Delta F).card) ≤ PhaseSemantics.phaseCap 6 p + initialAComplement p
  change (∑ F ∈ A \ U, (regularSeeds H selected Delta F).card) ≤ initialAComplement p at hN
  omega
end
end ProximityPrize.SubmissionLower.Lower80801.RegularBridge
