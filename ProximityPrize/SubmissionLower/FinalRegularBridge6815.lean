import ProximityPrize.SubmissionLower.MergedInfra6815_19
import ProximityPrize.SubmissionLower.FinalRegularCount6815
namespace ProximityPrize.SubmissionLower.Lower80899.FinalRegularBridge
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN259 RCN260 RCN266 RCN275 RCN319
open Lower80899.Selection Lower80899.InitialBridge
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

def Rules : Prop := ∀ r v z : ℕ, 1≤r → r≤39 → r+v≤182 → r+v+z≤11192 →
  FinalRuleCheck6815.RuleBound r v z (FinalLedgerData6815.cap r v z)
def finalCap (p : FlagDegree) := FinalLedgerData6815.cap p.all p.yz p.zOnly
def initialUpper (p : FlagDegree) := FinalLedgerChord6815.initialNum p.all (middle p) p.zOnly / 50174
def carrierSupport : ResidualSupportParameters :=
  ⟨50,229,15421,by decide,by decide,by decide,by decide⟩

theorem regular_count
    (hrules : Rules)
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K) (inp : Counting.Input u0 u1 selected Gamma) :
    let H : P4 := gcd12 S.QA S.QB
    let phi : K → P4 →+* Polynomial K := fun g => (specialization K (selected g) g).toRingHom
    let Delta := LocatorCover.fixed phi Gamma S.QA S.QB
    let U := initialAUniversalFactors u0 u1 H
    let p := regularAggregateFlag H U
    p.all ≤ 39 ∧ middle p ≤ 182 ∧ total p ≤ 11192 ∧
      (∑ F : RegularIndex H, (regularSeeds H selected Delta F).card) ≤
        finalCap p + initialUpper p := by
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
        reconstruct K 23924340 131071 76330 39 v.1 := by
    simpa only [U] using initialAUniversalProduct_dvd u0 u1 H
  have hpS : p.all ≤ 39 := by
    simp only [p, regularAggregateFlag_all]
    exact Caps.common_A_slope_le u0 u1 (regularProduct H U)
      hPne hdivA
  have hpY : middle p ≤ 182 := by
    simp only [p, regularAggregateFlag_middle]
    exact Caps.common_A_ys_le u0 u1 (regularProduct H U)
      hPne hdivA
  have hpT : total p ≤ 11192 := by
    simp only [p, regularAggregateFlag_total]
    exact (weightedTotalDegree_le_of_dvd residualTotalWeights
      (regularProduct H U) H
      (initialAUniversalProduct_dvd_carrier u0 u1 H) hH).trans
        S.common_total_le
  have hwholeT : total (regularAggregateFlag H A) ≤ 11192 := by
    simpa only [H, A] using
      whole_regular_total_le H hH 11192 S.common_total_le
  have hwholeY : middle (regularAggregateFlag H A) ≤ 229 := by
    simpa only [H, A] using
      whole_regular_middle_le H hH 229 S.common_ys_le
  have hwholeS : (regularAggregateFlag H A).all ≤ 50 := by
    simpa only [H, A] using
      whole_regular_all_le H hH 50 S.common_slope_le
  have hsplitT := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H => total (regularCumulativeFlag H F))
  have hsplitY := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H => middle (regularCumulativeFlag H F))
  have hsplitS := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H => (regularCumulativeFlag H F).all)
  have hcomplementT : total p +
      (∑ F ∈ N, total (regularCumulativeFlag H F)) ≤ 11192 := by
    have hpEq : total p =
        ∑ F ∈ U, total (regularCumulativeFlag H F) := by
      simp only [p, regularAggregateFlag, sumFlag_total]
    have hwhole : (∑ F ∈ A, total (regularCumulativeFlag H F)) ≤
        11192 := by
      simpa only [regularAggregateFlag, sumFlag_total] using hwholeT
    rw [hpEq]
    change (∑ F ∈ U, total (regularCumulativeFlag H F)) +
      (∑ F ∈ A \ U, total (regularCumulativeFlag H F)) ≤ 11192
    omega
  have hcomplementY : middle p +
      (∑ F ∈ N, middle (regularCumulativeFlag H F)) ≤ 229 := by
    have hpEq : middle p =
        ∑ F ∈ U, middle (regularCumulativeFlag H F) := by
      simp only [p, regularAggregateFlag, sumFlag_middle]
    have hwhole : (∑ F ∈ A, middle (regularCumulativeFlag H F)) ≤
        229 := by
      simpa only [regularAggregateFlag, sumFlag_middle] using hwholeY
    rw [hpEq]
    change (∑ F ∈ U, middle (regularCumulativeFlag H F)) +
      (∑ F ∈ A \ U, middle (regularCumulativeFlag H F)) ≤ 229
    omega
  have hcomplementS : p.all +
      (∑ F ∈ N, (regularCumulativeFlag H F).all) ≤ 50 := by
    have hpEq : p.all =
        ∑ F ∈ U, (regularCumulativeFlag H F).all := by
      simp only [p, regularAggregateFlag, sumFlag_all]
    have hwhole : (∑ F ∈ A, (regularCumulativeFlag H F).all) ≤ 50 := by
      simpa only [regularAggregateFlag, sumFlag_all] using hwholeS
    rw [hpEq]
    change (∑ F ∈ U, (regularCumulativeFlag H F).all) +
      (∑ F ∈ A \ U, (regularCumulativeFlag H F).all) ≤ 50
    omega
  have hhelperSum : (∑ F∈N,initialAHelperCap (regularCumulativeFlag H F)) ≤ initialUpper p := by
    have h := ExactInitialCharge6815.initial_helpers_sum_le N p.all (middle p) (total p)
      (fun F => (regularCumulativeFlag H F).all)
      (fun F => middle (regularCumulativeFlag H F))
      (fun F => total (regularCumulativeFlag H F))
      (fun F => initialAHelperCap (regularCumulativeFlag H F))
      (fun F _ => le_rfl) (fun F _ => regularCumulativeFlag_positive H F)
      (fun F _ => all_le_middle _) (fun F _ => middle_le_total _)
      hcomplementS hcomplementY hcomplementT
    have hcost : (∑ F∈N,initialAHelperCap (regularCumulativeFlag H F))≤
        ExactInitialCharge6815.cost 76330 182 39
          (min (min (11192-total p) (229-middle p)) (50-p.all))
          (min (11192-total p) (229-middle p)) (11192-total p) := by
      dsimp only at h
      split_ifs at h with hz
      · exact h.trans (Nat.zero_le _)
      · exact h
    simpa only [initialUpper,FinalLedgerChord6815.initialNum,ExactInitialCharge6815.cost_eq,
      total,middle,Nat.sub_sub,min_comm,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hcost
  have hsub : Delta ⊆ Gamma := by
    intro g hg
    have hm : g ∈ Gamma ∧ (phi g) (gcd12 S.QA S.QB) = 0 := by
      simpa only [Delta, LocatorCover.fixed, Finset.mem_filter] using hg
    exact hm.1
  have inpD := inp.restrict Delta hsub
  have hwide : ResidualSupportData InitialSupports.wideSupport H :=
    ⟨S.common_slope_le,S.common_ys_le,S.common_total_le⟩
  have hb := flag_box_to_ordinary K 30086670 131071 15421 50 S.QB S.QB_flag
  have hHbox : H∈RCN174.globalCoefficientBox K 30086670 131071 15421 50 :=
    mem_globalCoefficientBox_of_dvd H S.QB 30086670 131071 15421 50 S.QB_ne
      (gcd_dvd_right S.QA S.QB) hb
  have hphaseU : (∑ F∈U,(regularSeeds H selected Delta F).card)≤finalCap p :=
    FinalRegularCount6815.count_of_rules 30086670 carrierSupport (by decide) (by decide)
      H hH hHbox selected Delta u0 u1 inpD.degree inpD.agreement inpD.noPencil U hpS hpY hpT hrules
  have hN : (∑ F ∈ N, (regularSeeds H selected Delta F).card) ≤ initialUpper p := by
    apply le_trans (Finset.sum_le_sum (fun F hF => ?_)) hhelperSum
    exact initialA_nonuniversal_count u0 u1 H hH hwide selected Delta
      inpD.degree inpD.agreement inpD.noPencil F (Finset.mem_sdiff.mp hF).2
  have he := Finset.sum_sdiff hUsub (f := fun F => (regularSeeds H selected Delta F).card)
  refine ⟨hpS,hpY,hpT,?_⟩
  change (∑ F ∈ A, (regularSeeds H selected Delta F).card) ≤ finalCap p + initialUpper p
  change (∑ F ∈ A \ U, (regularSeeds H selected Delta F).card) ≤ initialUpper p at hN
  omega
end
end ProximityPrize.SubmissionLower.Lower80899.FinalRegularBridge
