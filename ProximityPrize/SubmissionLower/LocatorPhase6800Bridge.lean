import ProximityPrize.SubmissionLower.LocatorFixedBridge
import ProximityPrize.SubmissionLower.LocatorBatchPhase6800

/-!
# Correlated initial-A bridge for the 6800 phase certificate

This file turns a state-local narrow phase bound into the exact two-piece
ledger required by `LocatorFixedBridge`.  The aggregate flag of the
A-universal factors is retained in both terms; no independent maxima are
taken.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Bridge

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN259 RCN260 RCN266 RCN319
open LocatorSelection LocatorFactorAggregate LocatorBatchProductRoute
  LocatorBatchPhase6800 LocatorPhase6800Oracle LocatorFixedBridge

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
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (phaseCap : FlagDegree → ℕ)
    (hphase :
      let H : P4 := gcd12 S.QA S.QB
      let phi : K → P4 →+* Polynomial K :=
        fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom
      let Delta := LocatorCover.fixed phi Gamma S.QA S.QB
      let U := initialAUniversalFactors u0 u1 H
      StateLocalRegularBoundOn H selected Delta U phaseCap)
    (hAhelper : ∀ p : FlagDegree,
      1 ≤ p.all → p.all ≤ 33 → middle p ≤ 153 → total p ≤ 5964 →
      initialAHelperCap p ≤ initialAPotential.eval p)
    (hjoint : ∀ p : FlagDegree,
      p.all ≤ 28 → middle p ≤ 127 → total p ≤ 5964 →
      phaseCap p + initialAComplement p ≤
        LocatorFixedConsumer.initialRegularCap) :
    (LocatorCover.fixed
      (fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      LocatorFixedConsumer.initialRegularCap +
        LocatorArithmetic.fixedSingularCap := by
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
  have hdivA : ∀ v : LocatorCaps.AKernel u0 u1,
      regularProduct H U ∣
        reconstruct K 16688064 131071 130000 28 v.1 := by
    simpa only [U] using initialAUniversalProduct_dvd u0 u1 H
  have hpS : p.all ≤ 28 := by
    simp only [p, regularAggregateFlag_all]
    exact LocatorCaps.common_A_slope_le u0 u1 (regularProduct H U)
      hPne hdivA
  have hpY : middle p ≤ 127 := by
    simp only [p, regularAggregateFlag_middle]
    exact LocatorCaps.common_A_ys_le u0 u1 (regularProduct H U)
      hPne hdivA
  have hpT : total p ≤ 5964 := by
    simp only [p, regularAggregateFlag_total]
    exact (weightedTotalDegree_le_of_dvd residualTotalWeights
      (regularProduct H U) H
      (initialAUniversalProduct_dvd_carrier u0 u1 H) hH).trans
        S.common_total_le
  have hwholeT : total (regularAggregateFlag H A) ≤ 5964 := by
    simpa only [H, A] using
      whole_regular_total_le H hH 5964 S.common_total_le
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
      (∑ F ∈ N, total (regularCumulativeFlag H F)) ≤ 5964 := by
    have hpEq : total p =
        ∑ F ∈ U, total (regularCumulativeFlag H F) := by
      simp only [p, regularAggregateFlag, sumFlag_total]
    have hwhole : (∑ F ∈ A, total (regularCumulativeFlag H F)) ≤
        5964 := by
      simpa only [regularAggregateFlag, sumFlag_total] using hwholeT
    rw [hpEq]
    change (∑ F ∈ U, total (regularCumulativeFlag H F)) +
      (∑ F ∈ A \ U, total (regularCumulativeFlag H F)) ≤ 5964
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

end ProximityPrize.SubmissionLower.LocatorPhase6800Bridge
