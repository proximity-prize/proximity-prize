import ProximityPrize.SubmissionLower.LocatorFixedBridge6803
import ProximityPrize.SubmissionLower.LocatorInitialAComplement6803
import ProximityPrize.SubmissionLower.LocatorAggregateFlagProduct6803

/-!
# Correlated initial-A regular ledger for 68.03

The aggregate flag of the retained universal product is kept symbolic.  This
is the same flag used by the fixed phase cap, the initial-A complement, and
the residual quotient subtraction.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixedCorrelatedBridge6803

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN266 RCN275
open LocatorFactorAggregate LocatorBatchProductRoute LocatorBatchPhase6803
  LocatorFixedBridge6803 LocatorPhase6800Oracle

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

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

/-- Structural data of the retained product.  The two A-cap hypotheses are
exactly what the retuned A-divisor certificate supplies. -/
theorem initialA_retained_data
    (u0 u1 : I → K) (H : P4) (hH : H ≠ 0)
    (hTotal : wt residualTotalWeights H ≤ 6676)
    (hMiddle : wt residualYSWeights
      (regularProduct H (initialAUniversalFactors u0 u1 H)) ≤ 135)
    (hSlope : wt residualSWeights
      (regularProduct H (initialAUniversalFactors u0 u1 H)) ≤ 29) :
    let U := initialAUniversalFactors u0 u1 H
    let P := regularProduct H U
    let p := regularAggregateFlag H U
    P ≠ 0 ∧ P ∣ H ∧ originalCumulativeFlag P = p ∧
      p.all ≤ 29 ∧ middle p ≤ 135 ∧ total p ≤ 6676 := by
  dsimp only
  have hPne := regularProduct_ne_zero H
    (initialAUniversalFactors u0 u1 H)
  have hPdvd := initialAUniversalProduct_dvd_carrier u0 u1 H
  refine ⟨hPne, hPdvd,
    LocatorAggregateFlagProduct6803.originalCumulativeFlag_regularProduct
      H (initialAUniversalFactors u0 u1 H), ?_, ?_, ?_⟩
  · simpa only [regularAggregateFlag_all] using hSlope
  · simpa only [regularAggregateFlag_middle] using hMiddle
  · rw [regularAggregateFlag_total]
    exact (weightedTotalDegree_le_of_dvd residualTotalWeights
      (regularProduct H (initialAUniversalFactors u0 u1 H)) H
      hPdvd hH).trans hTotal

/-- Combine a phase bound on the retained A-universal child with all direct
A-helper exits, retaining the same aggregate flag in both numerical terms.
The pointwise outside-factor hypothesis is discharged by
`LocatorFixedBridge6803.initialA_nonuniversal_count`. -/
theorem initialA_regular_sum_le
    (u0 u1 : I → K) (H : P4) (hH : H ≠ 0)
    (hwide : ResidualSupportData wideSupport H)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (phaseCap : FlagDegree → ℕ)
    (hphase :
      let U := initialAUniversalFactors u0 u1 H
      let p := regularAggregateFlag H U
      (∑ F ∈ U, (regularSeeds H selected Gamma F).card) ≤ phaseCap p)
    (houtside : ∀ F ∈
      (Finset.univ : Finset (RegularIndex H)) \
        initialAUniversalFactors u0 u1 H,
      (regularSeeds H selected Gamma F).card ≤
        initialAHelperCap (regularCumulativeFlag H F)) :
    let U := initialAUniversalFactors u0 u1 H
    let p := regularAggregateFlag H U
    (∑ F : RegularIndex H, (regularSeeds H selected Gamma F).card) ≤
      phaseCap p +
        LocatorPhase6803ReceiptCore.initialAComplement p := by
  classical
  let A := (Finset.univ : Finset (RegularIndex H))
  let U := initialAUniversalFactors u0 u1 H
  let N := A \ U
  let p := regularAggregateFlag H U
  have hUsub : U ⊆ A := fun _ _ ↦ Finset.mem_univ _
  have hwholeT : total (regularAggregateFlag H A) ≤ 6676 := by
    simpa only [A] using
      whole_regular_total_le H hH 6676 hwide.total_weight
  have hwholeY : middle (regularAggregateFlag H A) ≤ 153 := by
    simpa only [A] using
      whole_regular_middle_le H hH 153 hwide.ys_weight
  have hwholeS : (regularAggregateFlag H A).all ≤ 34 := by
    simpa only [A] using
      whole_regular_all_le H hH 34 hwide.s_weight
  have hsplitT := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H ↦ total (regularCumulativeFlag H F))
  have hsplitY := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H ↦ middle (regularCumulativeFlag H F))
  have hsplitS := Finset.sum_sdiff hUsub
    (f := fun F : RegularIndex H ↦ (regularCumulativeFlag H F).all)
  have hcomplementT : total p +
      (∑ F ∈ N, total (regularCumulativeFlag H F)) ≤ 6676 := by
    have hpEq : total p =
        ∑ F ∈ U, total (regularCumulativeFlag H F) := by
      simp only [p, regularAggregateFlag, sumFlag_total]
    have hwhole : (∑ F ∈ A, total (regularCumulativeFlag H F)) ≤
        6676 := by
      simpa only [regularAggregateFlag, sumFlag_total] using hwholeT
    rw [hpEq]
    change (∑ F ∈ U, total (regularCumulativeFlag H F)) +
      (∑ F ∈ A \ U, total (regularCumulativeFlag H F)) ≤ 6676
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
      (∑ F ∈ N, (regularCumulativeFlag H F).all) ≤ 34 := by
    have hpEq : p.all =
        ∑ F ∈ U, (regularCumulativeFlag H F).all := by
      simp only [p, regularAggregateFlag, sumFlag_all]
    have hwhole :
        (∑ F ∈ A, (regularCumulativeFlag H F).all) ≤ 34 := by
      simpa only [regularAggregateFlag, sumFlag_all] using hwholeS
    rw [hpEq]
    change (∑ F ∈ U, (regularCumulativeFlag H F).all) +
      (∑ F ∈ A \ U, (regularCumulativeFlag H F).all) ≤ 34
    omega
  have hNpotential : ∀ F ∈ N,
      initialAHelperCap (regularCumulativeFlag H F) ≤
        LocatorPhase6803Oracle.initialAWidePotential.eval
          (regularCumulativeFlag H F) := by
    intro F hFN
    have hFA : F ∈ A := (Finset.mem_sdiff.mp hFN).1
    have hsingle : ({F} : Finset (RegularIndex H)) ⊆ A :=
      Finset.singleton_subset_iff.mpr hFA
    have hmono := regularAggregateFlag_mono H hsingle
    have hsingleS : (regularCumulativeFlag H F).all ≤ 34 := by
      simpa [regularAggregateFlag, sumFlag] using hmono.1.trans hwholeS
    have hsingleY : middle (regularCumulativeFlag H F) ≤ 153 := by
      simpa [regularAggregateFlag, sumFlag] using hmono.2.1.trans hwholeY
    have hsingleT : total (regularCumulativeFlag H F) ≤ 6676 := by
      simpa [regularAggregateFlag, sumFlag] using hmono.2.2.trans hwholeT
    simpa only [initialAHelperCap,
      LocatorGenericHelperFactorSwitch6803.helperPair,
      LocatorPhase6803Oracle.helperPair] using
      LocatorPhase6803SourceSound.initialAHelperCap_le_widePotential
        (regularCumulativeFlag H F) hsingleS hsingleY hsingleT
  have hhelperSum :
      (∑ F ∈ N, initialAHelperCap (regularCumulativeFlag H F)) ≤
        LocatorPhase6803ReceiptCore.initialAComplement p := by
    exact LocatorInitialAComplement6803.initialA_helpers_sum_le_complement
      N (regularCumulativeFlag H)
      (fun F ↦ initialAHelperCap (regularCumulativeFlag H F)) p
      hNpotential hcomplementT hcomplementY hcomplementS
  have hphaseU :
      (∑ F ∈ U, (regularSeeds H selected Gamma F).card) ≤
        phaseCap p := by
    simpa only [U, p] using hphase
  have houtsideN : ∀ F ∈ N,
      (regularSeeds H selected Gamma F).card ≤
        initialAHelperCap (regularCumulativeFlag H F) := by
    intro F hFN
    simpa only [A, N, U] using houtside F hFN
  have hsplitA : A = U ∪ N := by
    ext F
    simp only [A, N, Finset.mem_univ, Finset.mem_union,
      Finset.mem_sdiff, true_and]
    tauto
  have hdisjoint : Disjoint U N := by
    apply Finset.disjoint_left.mpr
    intro F hFU hFN
    exact (Finset.mem_sdiff.mp hFN).2 hFU
  change (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
    phaseCap p + LocatorPhase6803ReceiptCore.initialAComplement p
  rw [hsplitA, Finset.sum_union hdisjoint]
  exact (Nat.add_le_add hphaseU
    (Finset.sum_le_sum (fun F hFN ↦ houtsideN F hFN))).trans
      (Nat.add_le_add_left hhelperSum (phaseCap p))

end

end ProximityPrize.SubmissionLower.LocatorFixedCorrelatedBridge6803
