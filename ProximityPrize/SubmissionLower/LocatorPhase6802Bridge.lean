import ProximityPrize.SubmissionLower.LocatorInitialA6802

namespace ProximityPrize.SubmissionLower.LocatorPhase6802Bridge

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN259 RCN260 RCN266 RCN319
open LocatorSelection6802 LocatorFactorAggregate LocatorBatchProductRoute
  LocatorBatchPhase6802 LocatorPhase6802Oracle LocatorFixedBridge6802

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : GCDMonoid P4 :=
  UniqueFactorizationMonoid.toGCDMonoid P4

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

/-- Structural completion of the initial A split.  The numerical proof only
has to provide a state-local phase cap, the analytic A-helper majorant, and
the correlated final ledger at the same aggregate flag. -/
theorem gcd_fixed_count_le_of_stateLocalPhase
    (u0 u1 : I → K) (S : LocatorSelection6802.SelectedPair u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80771)
    (phaseCap : FlagDegree → ℕ)
    (hphase :
      let H : P4 := gcd12 S.QA S.QB
      let phi : K → P4 →+* Polynomial K :=
        fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom
      let Delta := LocatorCover.fixed phi Gamma S.QA S.QB
      let U := initialAUniversalFactors u0 u1 H
      StateLocalRegularBoundOn H selected Delta U phaseCap)
    (hAhelper : ∀ p : FlagDegree,
      1 ≤ p.all → p.all ≤ 32 → middle p ≤ 149 → total p ≤ 6403 →
      initialAHelperCap p ≤ initialAPotential.eval p)
    (hjoint : ∀ p : FlagDegree,
      p.all ≤ 29 → middle p ≤ 132 → total p ≤ 6403 →
      phaseCap p + initialAComplement p ≤
        LocatorFixedConsumer6802.initialRegularCap) :
    (LocatorCover.fixed
      (fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      LocatorFixedConsumer6802.initialRegularCap +
        LocatorArithmetic6802.fixedSingularCap := by
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
  have hdivA : ∀ v : LocatorCaps6802.AKernel u0 u1,
      regularProduct H U ∣
        reconstruct K 17411808 131071 130000 29 v.1 := by
    simpa only [U] using initialAUniversalProduct_dvd u0 u1 H
  have hpS : p.all ≤ 29 := by
    simp only [p, regularAggregateFlag_all]
    exact LocatorCaps6802.common_A_slope_le u0 u1 (regularProduct H U)
      hPne hdivA
  have hpY : middle p ≤ 132 := by
    simp only [p, regularAggregateFlag_middle]
    exact LocatorCaps6802.common_A_ys_le u0 u1 (regularProduct H U)
      hPne hdivA
  have hpT : total p ≤ 6403 := by
    simp only [p, regularAggregateFlag_total]
    exact (weightedTotalDegree_le_of_dvd residualTotalWeights
      (regularProduct H U) H
      (initialAUniversalProduct_dvd_carrier u0 u1 H) hH).trans
        S.common_total_le
  have hwholeT : total (regularAggregateFlag H A) ≤ 6403 := by
    simpa only [H, A] using
      whole_regular_total_le H hH 6403 S.common_total_le
  have hwholeY : middle (regularAggregateFlag H A) ≤ 149 := by
    simpa only [H, A] using
      whole_regular_middle_le H hH 149 S.common_ys_le
  have hwholeS : (regularAggregateFlag H A).all ≤ 32 := by
    simpa only [H, A] using
      whole_regular_all_le H hH 32 S.common_slope_le
  have hsplitT := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H => total (regularCumulativeFlag H F))
  have hsplitY := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H => middle (regularCumulativeFlag H F))
  have hsplitS := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H => (regularCumulativeFlag H F).all)
  have hcomplementT : total p +
      (∑ F ∈ N, total (regularCumulativeFlag H F)) ≤ 6403 := by
    have hpEq : total p =
        ∑ F ∈ U, total (regularCumulativeFlag H F) := by
      simp only [p, regularAggregateFlag, sumFlag_total]
    have hwhole : (∑ F ∈ A, total (regularCumulativeFlag H F)) ≤
        6403 := by
      simpa only [regularAggregateFlag, sumFlag_total] using hwholeT
    rw [hpEq]
    change (∑ F ∈ U, total (regularCumulativeFlag H F)) +
      (∑ F ∈ A \ U, total (regularCumulativeFlag H F)) ≤ 6403
    omega
  have hcomplementY : middle p +
      (∑ F ∈ N, middle (regularCumulativeFlag H F)) ≤ 149 := by
    have hpEq : middle p =
        ∑ F ∈ U, middle (regularCumulativeFlag H F) := by
      simp only [p, regularAggregateFlag, sumFlag_middle]
    have hwhole : (∑ F ∈ A, middle (regularCumulativeFlag H F)) ≤
        149 := by
      simpa only [regularAggregateFlag, sumFlag_middle] using hwholeY
    rw [hpEq]
    change (∑ F ∈ U, middle (regularCumulativeFlag H F)) +
      (∑ F ∈ A \ U, middle (regularCumulativeFlag H F)) ≤ 149
    omega
  have hcomplementS : p.all +
      (∑ F ∈ N, (regularCumulativeFlag H F).all) ≤ 32 := by
    have hpEq : p.all =
        ∑ F ∈ U, (regularCumulativeFlag H F).all := by
      simp only [p, regularAggregateFlag, sumFlag_all]
    have hwhole : (∑ F ∈ A, (regularCumulativeFlag H F).all) ≤ 32 := by
      simpa only [regularAggregateFlag, sumFlag_all] using hwholeS
    rw [hpEq]
    change (∑ F ∈ U, (regularCumulativeFlag H F).all) +
      (∑ F ∈ A \ U, (regularCumulativeFlag H F).all) ≤ 32
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
    apply hAhelper (regularCumulativeFlag H F) hr
    · simpa [regularAggregateFlag, sumFlag] using hmono.1.trans hwholeS
    · simpa [regularAggregateFlag, sumFlag] using hmono.2.1.trans hwholeY
    · simpa [regularAggregateFlag, sumFlag] using hmono.2.2.trans hwholeT
  have hhelperSum :
      (∑ F ∈ N, initialAHelperCap (regularCumulativeFlag H F)) ≤
        initialAComplement p := by
    exact initialA_helpers_sum_le_complement N (regularCumulativeFlag H)
      (fun F ↦ initialAHelperCap (regularCumulativeFlag H F)) p
      hNpotential hcomplementT hcomplementY hcomplementS
  have hphaseU :
      (∑ F ∈ U, (regularSeeds H selected Delta F).card) ≤ phaseCap p := by
    have hp := hphase U (fun _ hFU ↦ hFU) hpS hpY hpT
    simpa only [H, phi, Delta, p, U] using hp
  apply gcd_fixed_count_le_of_initial_phase u0 u1 S selected Gamma
    hdegree hagreement hno (phaseCap p)
  · simpa only [H, phi, Delta, U, p] using hphaseU
  · have hfinal := Nat.add_le_add_left hhelperSum (phaseCap p)
    exact (hfinal.trans (hjoint p hpS hpY hpT))

end

end ProximityPrize.SubmissionLower.LocatorPhase6802Bridge
