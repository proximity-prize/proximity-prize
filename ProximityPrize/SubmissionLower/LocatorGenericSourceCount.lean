import ProximityPrize.SubmissionLower.LocatorReplacementGridCore
import ProximityPrize.SubmissionLower.LocatorGenericPowerAvoidance
import ProximityPrize.SubmissionLower.BF

namespace ProximityPrize.SubmissionLower.LocatorGenericSourceCount

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient LocatorGenericPowerAvoidance
  LocatorReplacementGridData LocatorFactorAggregate

open scoped BigOperators Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

theorem forwardSum_succ_last (f : ℕ → ℕ) (start n : ℕ) :
    forwardSum f start (n + 1) = forwardSum f start n + f (start + n) := by
  induction n generalizing start with
  | zero => simp [forwardSum]
  | succ n ih =>
      change f start + forwardSum f (start + 1) (n + 1) =
        (f start + forwardSum f (start + 1) n) + f (start + (n + 1))
      rw [ih]
      calc
        f start + (forwardSum f (start + 1) n + f (start + 1 + n)) =
            (f start + forwardSum f (start + 1) n) +
              f (start + 1 + n) := (Nat.add_assoc _ _ _).symm
        _ = (f start + forwardSum f (start + 1) n) +
              f (start + (n + 1)) := by
                rw [show start + 1 + n = start + (n + 1) by omega]

theorem forwardSum_stageBand_eq_bandSum (src : Source) (b : Box) (k : ℕ) :
    forwardSum (stageBand src b) 1 k = bandSum src b k := by
  induction k with
  | zero => simp [forwardSum, bandSum]
  | succ k ih =>
      rw [forwardSum_succ_last, bandSum, ih]
      exact congrArg (fun j => bandSum src b k + stageBand src b j)
        (Nat.add_comm 1 k)

theorem pairGatesThrough_get (src : Source) (b : Box) {j k : ℕ}
    (hj : 1 ≤ j) (hjk : j ≤ k) (h : pairGatesThrough src b k) :
    PairGates (stagePair src b j) := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [pairGatesThrough] at h
      by_cases hjk' : j ≤ k
      · exact ih hjk' h.1
      · have : j = k + 1 := by omega
        simpa [this] using h.2

theorem stageCost_le_routeCost (src : Source) (b : Box) {j k : ℕ}
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    stageCost src b j ≤ routeCost src b k := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [routeCost]
      by_cases hjk' : j ≤ k
      · exact (ih hjk').trans (Nat.le_max_left _ _)
      · have : j = k + 1 := by omega
        simpa [this] using Nat.le_max_right
          (routeCost src b k) (stageCost src b (k + 1))

theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

theorem factor_bounds_of_cell (H : P4) (F : RegularIndex H)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c) :
    wt residualSWeights F.1 = (box c).r ∧
      (box c).ylo ≤ wt residualYSWeights F.1 ∧
      wt residualYSWeights F.1 ≤ (box c).factorY ∧
      (box c).factorT ≤ wt residualTotalWeights F.1 ∧
      wt residualTotalWeights F.1 ≤ (box c).thi := by
  have hc := originalCumulativeFlag_cumulative F.1
  have hr : wt residualSWeights F.1 = (box c).r := by
    simpa only [regularCumulativeFlag, hc.1] using hcell.all_eq
  have hylo : (box c).ylo ≤ wt residualYSWeights F.1 := by
    simpa only [middle, regularCumulativeFlag, hc.2.1] using hcell.ylo_le
  have hyhi : wt residualYSWeights F.1 ≤ (box c).yhi := by
    simpa only [middle, regularCumulativeFlag, hc.2.1] using
      hcell.middle_le_yhi
  have hyT : wt residualYSWeights F.1 ≤ (box c).thi := by
    simpa only [middle, total, regularCumulativeFlag, hc.2.1, hc.2.2] using
      (middle_le_total (regularCumulativeFlag H F)).trans hcell.total_le_thi
  have htlo : (box c).tlo ≤ wt residualTotalWeights F.1 := by
    simpa only [total, regularCumulativeFlag, hc.2.2] using hcell.tlo_le
  have hthi : wt residualTotalWeights F.1 ≤ (box c).thi := by
    simpa only [total, regularCumulativeFlag, hc.2.2] using hcell.total_le_thi
  have hysTotal : wt residualYSWeights F.1 ≤ wt residualTotalWeights F.1 := by
    simpa only [middle, total, regularCumulativeFlag, hc.2.1, hc.2.2] using
      middle_le_total (regularCumulativeFlag H F)
  exact ⟨hr, hylo, le_min hyhi hyT, max_le htlo (hylo.trans hysTotal), hthi⟩

theorem count_le_stageCost
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181540 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80604)
    (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (src : Source) (j : ℕ) (Q : P4) (_hQ : Q ≠ 0)
    (hQT : wt residualTotalWeights Q ≤ stageT src (box c) j)
    (hQY : wt residualYSWeights Q ≤ stageY src (box c) j)
    (hQR : wt residualSWeights Q ≤ stageR src (box c) j)
    (hrel : IsRelPrime F.1 Q)
    (hgates : PairGates (stagePair src (box c) j))
    (hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q = 0) :
    (regularSeeds H selected Gamma F).card ≤ stageCost src (box c) j := by
  obtain ⟨hr, _hylo, hyhi, _htlo, hthi⟩ :=
    factor_bounds_of_cell H F c hcell
  have hFY : F.1.degreeOf 1 ≤ (stagePair src (box c) j).leftY := by
    simpa only [stagePair] using (degreeY_le_ysWeight F.1).trans hyhi
  have hFR : F.1.degreeOf 2 ≤ (stagePair src (box c) j).leftR := by
    simpa only [stagePair, LocatorContact.slope_weight_eq_degreeR] using hr.le
  have hFZ : F.1.degreeOf 3 ≤ (stagePair src (box c) j).leftZ := by
    simpa only [stagePair] using (degreeZ_le_totalWeight F.1).trans hthi
  have hQY' : Q.degreeOf 1 ≤ (stagePair src (box c) j).rightY := by
    simpa only [stagePair] using (degreeY_le_ysWeight Q).trans hQY
  have hQR' : Q.degreeOf 2 ≤ (stagePair src (box c) j).rightR := by
    simpa only [stagePair, LocatorContact.slope_weight_eq_degreeR] using hQR
  have hQZ : Q.degreeOf 3 ≤ (stagePair src (box c) j).rightZ := by
    simpa only [stagePair] using (degreeZ_le_totalWeight Q).trans hQT
  obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
    hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ := hgates
  have hcount := regularSeeds_count_le_intersection
    (stagePair src (box c) j) H Q F hrel 2130706433
    hFY hFR hFZ hQY' hQR' hQZ hleftR hleftYSmall hleftRSmall
    hleftZSmall hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
    (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ : Finset I).card = 262144
      rw [Finset.card_univ]
      norm_num [I, IRSProfile.Index])
    (by norm_num [stagePair]) (by norm_num [stagePair])
    (by norm_num [stagePair]) (by norm_num [stagePair])
    (by simpa only [stagePair] using hdegree)
    (by simpa only [stagePair] using hagreement)
    (by simpa only [stagePair, UnequalParameters.errors] using hno)
    hQzero
  simpa only [stageCost] using hcount

theorem terminal_relPrime
    (H : P4) (F : RegularIndex H) (c : Cell) (src : Source) (j : ℕ)
    (Q : P4) (hQ : Q ≠ 0)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hQT : wt residualTotalWeights Q ≤ stageT src (box c) j)
    (hQY : wt residualYSWeights Q ≤ stageY src (box c) j)
    (hQR : wt residualSWeights Q ≤ stageR src (box c) j)
    (hterminal : terminalCoprime src (box c) j) : IsRelPrime F.1 Q := by
  obtain ⟨hr, hylo, _hyhi, htlo, _hthi⟩ :=
    factor_bounds_of_cell H F c hcell
  have hirr := (RCN167.positiveRFactors_spec H F.1 F.2).1
  rcases hterminal with hT | hY | hR
  · apply isRelPrime_of_weight_lt residualTotalWeights F.1 Q hirr hQ
    exact hQT.trans_lt (hT.trans_le htlo)
  · apply isRelPrime_of_weight_lt residualYSWeights F.1 Q hirr hQ
    exact hQY.trans_lt (hY.trans_le hylo)
  · apply isRelPrime_of_weight_lt residualSWeights F.1 Q hirr hQ
    rw [hr]
    exact hQR.trans_lt hR

theorem reconstruct_mem_low_of_power
    {D Dlow w L s m j : ℕ} (nodes u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (F Q : P4) (heq : reconstruct K D w L s v.1 = F ^ j * Q)
    (hD : 0 < D) (hDlow : 0 < Dlow)
    (hcontact : wt (contactWeights w) Q <
      Dlow - j * wt (contactWeights w) F) :
    reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s := by
  have hsource := (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D w L s v.1) D w L s hD).mp
      (reconstruct_mem_globalCoefficientBox K D w L s v.1)
  apply (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D w L s v.1) Dlow w L s hDlow).mpr
  refine ⟨hsource.1, hsource.2.1, ?_⟩
  rw [heq]
  have hmul := wt_mul_le (contactWeights w) (F ^ j) Q
  have hp := wt_pow_le (contactWeights w) F j
  omega

end

end ProximityPrize.SubmissionLower.LocatorGenericSourceCount
