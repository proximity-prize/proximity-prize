import ProximityPrize.SubmissionLower.LocatorReplacementGridData
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
import ProximityPrize.SubmissionLower.LocatorIteratedPowerAvoidance
import ProximityPrize.SubmissionLower.LocatorSixthPowerAvoidance
import ProximityPrize.SubmissionLower.LocatorNinthPowerAvoidance
import ProximityPrize.SubmissionLower.LocatorHybridCost
import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
import ProximityPrize.SubmissionLower.LocatorSourceCGap
import ProximityPrize.SubmissionLower.BF

namespace ProximityPrize.SubmissionLower.LocatorQuotientReplacement

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238
  RCN260 RCN266
open LocatorFactorAggregate LocatorLowQuotient LocatorCoprimeQuotient
  LocatorReplacementGridData

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

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

private theorem factor_bounds_of_cell (H : P4) (F : RegularIndex H)
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

private theorem ordinary_count
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (hv : Valid c)
    (hown : LocatorHybridCost.OwnBound (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F)) :
    (regularSeeds H selected Gamma F).card ≤ (box c).ordinaryCost := by
  have hb := hv.1
  have hcap := cap_cumulative (box c).thi (box c).factorY (box c).r
    (by
      apply le_min
      · exact hb.2.1.trans hb.2.2.1
      · exact hb.2.1.trans hb.2.2.2.2.1)
    (Nat.min_le_right _ _)
  have hbelow : Below (regularCumulativeFlag H F) (box c).ordinaryCap := by
    unfold Below Box.ordinaryCap
    rw [hcap.1, hcap.2.1, hcap.2.2]
    exact ⟨hcell.all_eq.le,
      le_min hcell.middle_le_yhi
        ((middle_le_total (regularCumulativeFlag H F)).trans hcell.total_le_thi),
      hcell.total_le_thi⟩
  unfold Box.ordinaryCost
  split_ifs with hhyb
  · have happ : LocatorHybridCost.HybridApplies (regularCumulativeFlag H F) := by
      refine ⟨?_, ?_⟩
      · rw [hcell.all_eq]; exact hhyb.1
      · have h1 := hcell.all_eq
        have h2 := hcell.ylo_le
        omega
    exact (hown.2 happ).trans (LocatorHybridCost.hybridCost_mono hbelow)
  · exact hown.1.trans (paddedCost_mono 131072 131073 hbelow)

private theorem count_le_stageCost
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181569 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80575)
    (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (src : Source) (j : ℕ) (Q : P4) (_hQ : Q ≠ 0)
    (hQT : wt residualTotalWeights Q ≤ stageT (box c) j)
    (hQY : wt residualYSWeights Q ≤ stageY src (box c) j)
    (hQR : wt residualSWeights Q ≤ stageR src (box c) j)
    (hrel : IsRelPrime F.1 Q)
    (hgates : PairGates (stagePair src (box c) j))
    (hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q = 0) :
    (regularSeeds H selected Gamma F).card ≤ stageCost src (box c) j := by
  obtain ⟨hr, _hylo, hyhi, _htlo, hthi⟩ := factor_bounds_of_cell H F c hcell
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
    (by simpa only [stagePair] using (show 1 ≤ 131071 by decide))
    (by simpa only [stagePair] using (show 131071 < 2130706433 by decide))
    (by simpa only [stagePair] using (show 131071 < 181569 by decide))
    (by simpa only [stagePair] using (show 181569 ≤ 262144 by decide))
    hdegree hagreement
    (by simpa only [stagePair, UnequalParameters.errors, Nat.reduceSub] using hno)
    hQzero
  simpa only [stageCost] using hcount

private theorem terminal_relPrime
    (H : P4) (F : RegularIndex H) (c : Cell) (src : Source) (j : ℕ)
    (Q : P4) (hQ : Q ≠ 0)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hQT : wt residualTotalWeights Q ≤ stageT (box c) j)
    (hQY : wt residualYSWeights Q ≤ stageY src (box c) j)
    (hQR : wt residualSWeights Q ≤ stageR src (box c) j)
    (hterminal : terminalCoprime src (box c) j) : IsRelPrime F.1 Q := by
  obtain ⟨hr, hylo, _hyhi, htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  have hirr := (RCN167.positiveRFactors_spec H F.1 F.2).1
  rcases hterminal with hT | hY | hR
  · apply isRelPrime_of_weight_lt residualTotalWeights F.1 Q hirr hQ
    exact hQT.trans_lt (hT.trans_le htlo)
  · apply isRelPrime_of_weight_lt residualYSWeights F.1 Q hirr hQ
    exact hQY.trans_lt (hY.trans_le hylo)
  · apply isRelPrime_of_weight_lt residualSWeights F.1 Q hirr hQ
    rw [hr]
    exact hQR.trans_lt hR

private theorem source_one_count
    (D s m Ysrc gap : ℕ) (src : Source)
    (hsrcY : src.y = Ysrc) (hsrcR : src.r = s) (hsrcGap : src.gap = gap)
    (hgap : coefficientCount D 131071 130000 s -
      262144 * localRankBound m 130000 s = gap)
    (hshape : D + s ≤ 131071 * (Ysrc + 1))
    (hcapacity : D - 50499 ≤ (m - 1) * 181569 + (131071 - 1))
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181569 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80575)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := K) D 131071 130000 s m
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K D 131071 130000 s v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits src 1 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost src (box c) 1 := by
  classical
  obtain ⟨_hkpos, _hkcap, _hyroom, _hrroom, _hshapeRoute, hband,
    hterminal, hgates, _hrate⟩ := hfit
  obtain ⟨hr, hylo, _hyhi, htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  have hqT : 130000 - wt residualTotalWeights F.1 ≤ stageT (box c) 1 := by
    simpa only [stageT, Nat.one_mul] using Nat.sub_le_sub_left htlo 130000
  have hqY : Ysrc - wt residualYSWeights F.1 ≤ stageY src (box c) 1 := by
    rw [stageY, Nat.one_mul, hsrcY]
    exact Nat.sub_le_sub_left hylo Ysrc
  have hqR : s - wt residualSWeights F.1 ≤ stageR src (box c) 1 := by
    rw [stageR, Nat.one_mul, hsrcR, hr]
  have hchannels := channelCount_mono hqT hqY hqR
  have hsource : 50499 * channelCount
      (130000 - wt residualTotalWeights F.1)
      (Ysrc - wt residualYSWeights F.1)
      (s - wt residualSWeights F.1) <
      coefficientCount D 131071 130000 s -
        Fintype.card I * localRankBound m 130000 s := by
    rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index], hgap]
    exact (Nat.mul_le_mul_left 50499 hchannels).trans_lt (by
      simpa only [bandSum, stageBand_eq, hsrcGap, Nat.zero_add] using hband)
  obtain ⟨_v, Q, _hv, hQ, _heq, hQbox, _hparent, hproduct⟩ :=
    exists_fixed_quotient_with_derivative_vanishing (K := K) (I := I)
      D 131071 130000 s m Ysrc 50499 181569 IRSProfile.domain u0 u1
      F.1 hF hdiv (by decide) hshape hsource hcapacity
      selected Gamma hdegree hagreement
  have hwQ := nested_mem_weights hQbox hQ
  have hQT := hwQ.1.trans hqT
  have hQY := hwQ.2.1.trans hqY
  have hQR := hwQ.2.2.1.trans hqR
  have hrel := terminal_relPrime H F c src 1 Q hQ hcell hQT hQY hQR hterminal
  have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q = 0 := by
    intro gamma hgamma
    obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
    have hp := hproduct gamma (regularSeeds_subset H selected Gamma F hgamma)
    have hmul :
        RCN319.specialization K (selected gamma) gamma
            (MvPolynomial.pderiv (2 : Fin 4) F.1) *
          RCN319.specialization K (selected gamma) gamma Q = 0 := by
      simpa only [MvPolynomial.pderiv_mul, map_add, map_mul, hFzero,
        zero_mul, add_zero] using hp
    exact (mul_eq_zero.mp hmul).resolve_left hregular
  have hgate : PairGates (stagePair src (box c) 1) := by
    simpa only [pairGatesThrough, true_and] using hgates
  have hcount := count_le_stageCost u0 u1 H selected Gamma hdegree hagreement
    hno F c hcell src 1 Q hQ hQT hQY hQR hrel hgate hQzero
  simpa only [routeCost, Nat.zero_max] using hcount

private theorem reconstruct_mem_low_of_power
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

private theorem factorial_cast_ne_zero (j : ℕ) (hj : j ≤ 14) :
    ((Nat.factorial j : ℕ) : K) ≠ 0 := by
  intro hz
  have hdvd : (2130706433 : ℕ) ∣ Nat.factorial j :=
    (CharP.cast_eq_zero_iff K 2130706433 _).mp hz
  interval_cases j <;> revert hdvd <;> decide

private theorem sourceC_power_count
    (j : ℕ) (hjpos : 1 ≤ j) (hjcap : j ≤ 14)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181569 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80575)
    (F : RegularIndex H)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (v : ConstraintKernel (K := K) 72627600 131071 130000 120 400
      IRSProfile.domain u0 u1)
    (Q : P4) (hQ : Q ≠ 0)
    (heq : reconstruct K 72627600 131071 130000 120 v.1 = F.1 ^ j * Q)
    (hcQ : wt (contactWeights 131071) Q <
      72627600 - j * 50499 - j * wt (contactWeights 131071) F.1)
    (htQ : wt residualTotalWeights Q ≤
      130000 - j * wt residualTotalWeights F.1)
    (hyQ : wt residualYSWeights Q ≤
      554 - j * wt residualYSWeights F.1)
    (hrQ : wt residualSWeights Q ≤
      120 - j * wt residualSWeights F.1)
    (hrel : IsRelPrime F.1 Q)
    (hgate : PairGates (stagePair sourceC (box c) j)) :
    (regularSeeds H selected Gamma F).card ≤ stageCost sourceC (box c) j := by
  classical
  have hlow : reconstruct K 72627600 131071 130000 120 v.1 ∈
      globalCoefficientBox K (72627600 - j * 50499) 131071 130000 120 :=
    reconstruct_mem_low_of_power IRSProfile.domain u0 u1 v F.1 Q heq
      (by decide) (by omega) hcQ
  obtain ⟨hr, hylo, _hyhi, htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  have hQT : wt residualTotalWeights Q ≤ stageT (box c) j := by
    apply htQ.trans
    change 130000 - j * wt residualTotalWeights F.1 ≤
      130000 - j * (box c).factorT
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j htlo) 130000
  have hQY : wt residualYSWeights Q ≤ stageY sourceC (box c) j := by
    apply hyQ.trans
    change 554 - j * wt residualYSWeights F.1 ≤ 554 - j * (box c).ylo
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j hylo) 554
  have hQR : wt residualSWeights Q ≤ stageR sourceC (box c) j := by
    apply hrQ.trans
    change 120 - j * wt residualSWeights F.1 ≤ 120 - j * (box c).r
    rw [hr]
  obtain ⟨jm, rfl⟩ : ∃ jm, j = jm + 1 := ⟨j - 1, by omega⟩
  have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q = 0 := by
    intro gamma hgamma
    have hgammaG := regularSeeds_subset H selected Gamma F hgamma
    let support := (Finset.univ : Finset I).filter (fun i =>
      (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
    have hcard : 181569 ≤ support.card := hagreement gamma hgammaG
    have hchain := LocatorAuxiliaryArithmetic.chain_capacity
      72627600 181569 131071 400 (by decide) (by decide) (jm + 1) (by omega)
    have hdelta : 181569 - 131071 + 1 = 50499 := by decide
    rw [hdelta] at hchain
    have hcap : 72627600 - (jm + 1) * 50499 ≤
        (400 - (jm + 1)) * support.card + (jm + 1) * (131071 - 1) :=
      hchain.trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left (400 - (jm + 1)) hcard) _)
    have hvalues : ∀ i ∈ support,
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hder :=
      LocatorIteratedPowerAvoidance.specialization_pderivRIter_eq_zero_of_kernel_low_box
        jm 72627600 (72627600 - (jm + 1) * 50499) 131071 130000 120 400
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hgammaG) hcap hvalues
    obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
    rw [heq] at hder
    exact
      LocatorIteratedPowerAvoidance.specialization_eq_zero_of_pderivRIter_power_product
        (jm + 1) (selected gamma) gamma F.1 Q
        (factorial_cast_ne_zero (jm + 1) (by omega)) hFzero hregular hder
  exact count_le_stageCost u0 u1 H selected Gamma hdegree hagreement hno
    F c hcell sourceC (jm + 1) Q hQ hQT hQY hQR hrel hgate hQzero

private theorem sub_two_mul (a b : ℕ) : a - 2 * b = a - b - b := by omega
private theorem sub_three_mul (a b : ℕ) : a - 3 * b = a - b - 2 * b := by omega
private theorem sub_four_mul (a b : ℕ) : a - 4 * b = a - b - 3 * b := by omega
private theorem sub_five_mul (a b : ℕ) : a - 5 * b = a - b - 4 * b := by omega
private theorem sub_six_mul (a b : ℕ) : a - 6 * b = a - b - 5 * b := by omega
private theorem sub_seven_mul (a b : ℕ) : a - 7 * b = a - b - 6 * b := by omega
private theorem sub_eight_mul (a b : ℕ) : a - 8 * b = a - b - 7 * b := by omega
private theorem sub_nine_mul (a b : ℕ) : a - 9 * b = a - b - 8 * b := by omega

private theorem sub_succ_mul (a b j : ℕ) :
    a - b - j * b = a - (j + 1) * b := by
  rw [Nat.add_mul, Nat.one_mul]
  omega
private theorem sub_two_succ_mul (a b c j : ℕ) :
    a - b - c - j * b - j * c = a - (j + 1) * b - (j + 1) * c := by
  simp only [Nat.add_mul, Nat.one_mul]
  omega

private abbrev KernelC (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 72627600 131071 130000 120 400
    IRSProfile.domain u0 u1

private theorem sum_band_le (H : P4) (F : RegularIndex H) (c : Cell)
    (hbandLe : ∀ j, 50499 * channelCount
      (130000 - j * wt residualTotalWeights F.1)
      (554 - j * wt residualYSWeights F.1)
      (120 - j * wt residualSWeights F.1) ≤ stageBand sourceC (box c) j)
    (m : ℕ) :
    (∑ i ∈ Finset.range m, 50499 * channelCount
      (130000 - (i + 1) * wt residualTotalWeights F.1)
      (554 - (i + 1) * wt residualYSWeights F.1)
      (120 - (i + 1) * wt residualSWeights F.1))
        ≤ bandSum sourceC (box c) m := by
  induction m with
  | zero => simp [bandSum]
  | succ m ih =>
      rw [Finset.sum_range_succ]
      exact Nat.add_le_add ih (hbandLe (m + 1))

/-- Depth-generic repeated projection along the `sourceC` kernel. -/
private theorem sourceC_count_k_core
    (n : ℕ) (hncap : n + 1 ≤ 14)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181569 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80575)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (q : KernelC u0 u1 →ₗ[K] P4) (hqinj : Function.Injective q)
    (hprod : ∀ v, reconstruct K 72627600 131071 130000 120 v.1 = F.1 * q v)
    (hqNested : ∀ v, q v ∈ nestedCoefficientBox K
      (72627600 - wt (contactWeights 131071) F.1) 131071
      (130000 - wt residualTotalWeights F.1)
      (554 - wt residualYSWeights F.1)
      (120 - wt residualSWeights F.1))
    (hTstage : ∀ j, 130000 - j * wt residualTotalWeights F.1 ≤ stageT (box c) j)
    (hYstage : ∀ j, 554 - j * wt residualYSWeights F.1 ≤ stageY sourceC (box c) j)
    (hRstage : ∀ j, 120 - j * wt residualSWeights F.1 ≤ stageR sourceC (box c) j)
    (hbandLe : ∀ j, 50499 * channelCount
      (130000 - j * wt residualTotalWeights F.1)
      (554 - j * wt residualYSWeights F.1)
      (120 - j * wt residualSWeights F.1) ≤ stageBand sourceC (box c) j)
    (hgapLe : 1743757566946340 ≤ Module.finrank K
      (ConstraintKernel (K := K) 72627600 131071 130000 120 400
        IRSProfile.domain u0 u1))
    (hwidth : 72627600 - wt (contactWeights 131071) F.1 ≤
      (72627600 - 50499 - wt (contactWeights 131071) F.1) + 50499)
    (hfit : RouteFits sourceC (n + 1) (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) (n + 1) := by
  classical
  obtain ⟨_hkpos, _hkcap, _hyroom, _hrroom, _hshapeRoute, hband,
    hterminal, hgates, _hrate⟩ := hfit
  have hsource : (∑ i ∈ Finset.range (n + 1), 50499 * channelCount
      (130000 - wt residualTotalWeights F.1 - i * wt residualTotalWeights F.1)
      (554 - wt residualYSWeights F.1 - i * wt residualYSWeights F.1)
      (120 - wt residualSWeights F.1 - i * wt residualSWeights F.1)) <
      Module.finrank K (ConstraintKernel (K := K)
        72627600 131071 130000 120 400 IRSProfile.domain u0 u1) := by
    have hrw : ∀ i ∈ Finset.range (n + 1),
        50499 * channelCount
          (130000 - wt residualTotalWeights F.1 - i * wt residualTotalWeights F.1)
          (554 - wt residualYSWeights F.1 - i * wt residualYSWeights F.1)
          (120 - wt residualSWeights F.1 - i * wt residualSWeights F.1) =
        50499 * channelCount
          (130000 - (i + 1) * wt residualTotalWeights F.1)
          (554 - (i + 1) * wt residualYSWeights F.1)
          (120 - (i + 1) * wt residualSWeights F.1) := by
      intro i _
      rw [sub_succ_mul, sub_succ_mul, sub_succ_mul]
    rw [Finset.sum_congr rfl hrw]
    have hbandGap : bandSum sourceC (box c) (n + 1) < 1743757566946340 := by
      simpa only [sourceC] using hband
    exact ((sum_band_le H F c hbandLe (n + 1)).trans_lt hbandGap).trans_le hgapLe
  obtain ⟨j, v, Q, hjle, _hv, hQ, heq, hndvd, hbox⟩ :=
    LocatorIteratedPowerAvoidance.exists_low_not_dvd_iter n
      (72627600 - wt (contactWeights 131071) F.1)
      (72627600 - 50499 - wt (contactWeights 131071) F.1)
      131071 50499
      (130000 - wt residualTotalWeights F.1)
      (554 - wt residualYSWeights F.1)
      (120 - wt residualSWeights F.1)
      hwidth q hqinj hqNested F.1 hF hsource
  have hw := nested_mem_weights hbox hQ
  have heqR : reconstruct K 72627600 131071 130000 120 v.1 = F.1 ^ (j + 1) * Q := by
    rw [hprod v, ← heq]
    ring
  have hcQ : wt (contactWeights 131071) Q <
      72627600 - (j + 1) * 50499 - (j + 1) * wt (contactWeights 131071) F.1 := by
    have h := hw.2.2.2
    rwa [sub_two_succ_mul] at h
  have htQ : wt residualTotalWeights Q ≤
      130000 - (j + 1) * wt residualTotalWeights F.1 := by
    have h := hw.1
    rwa [sub_succ_mul] at h
  have hyQ : wt residualYSWeights Q ≤
      554 - (j + 1) * wt residualYSWeights F.1 := by
    have h := hw.2.1
    rwa [sub_succ_mul] at h
  have hrQ : wt residualSWeights Q ≤
      120 - (j + 1) * wt residualSWeights F.1 := by
    have h := hw.2.2.1
    rwa [sub_succ_mul] at h
  have hgate : PairGates (stagePair sourceC (box c) (j + 1)) :=
    pairGates_of_pairGatesThrough sourceC (box c) (j + 1) (n + 1)
      (by omega) (by omega) hgates
  have hrel : IsRelPrime F.1 Q := by
    rcases Nat.lt_or_ge j n with hlt | hge
    · exact ((RCN167.positiveRFactors_spec H F.1 F.2).1).isRelPrime_iff_not_dvd.mpr
        (hndvd hlt)
    · have hjn : j = n := by omega
      subst hjn
      exact terminal_relPrime H F c sourceC (j + 1) Q hQ hcell
        (htQ.trans (hTstage (j + 1))) (hyQ.trans (hYstage (j + 1)))
        (hrQ.trans (hRstage (j + 1))) hterminal
  have hcount := sourceC_power_count (j + 1) (by omega) (by omega)
    u0 u1 H selected Gamma hdegree hagreement hno F c hcell v Q hQ heqR
    hcQ htQ hyQ hrQ hrel hgate
  exact hcount.trans (stageCost_le_routeCost sourceC (box c) (j + 1) (n + 1)
    (by omega) (by omega))

private theorem sourceC_quotient_nested
    (u0 u1 : I → K) (H : P4) (F : RegularIndex H) (hF : F.1 ≠ 0)
    (q : KernelC u0 u1 →ₗ[K] P4) (hqinj : Function.Injective q)
    (hprod : ∀ v, reconstruct K 72627600 131071 130000 120 v.1 = F.1 * q v)
    (hqbox : ∀ v, q v ∈ globalCoefficientBox K
      (72627600 - wt (contactWeights 131071) F.1) 131071
      (130000 - wt residualTotalWeights F.1)
      (120 - wt residualSWeights F.1)) :
    ∀ v, q v ∈ nestedCoefficientBox K
      (72627600 - wt (contactWeights 131071) F.1) 131071
      (130000 - wt residualTotalWeights F.1)
      (554 - wt residualYSWeights F.1)
      (120 - wt residualSWeights F.1) := by
  intro v
  have hqYS : wt residualYSWeights (q v) ≤
      554 - wt residualYSWeights F.1 := by
    by_cases hv : v = 0
    · subst v
      simp [wt, MvPolynomial.weightedTotalDegree]
    · have hqv : q v ≠ 0 := by
        intro hz
        apply hv
        apply hqinj
        simpa only [map_zero] using hz
      have hsrc : wt residualYSWeights
          (reconstruct K 72627600 131071 130000 120 v.1) ≤ 554 := by
        apply flag_box_ys_bound 72627600 131071 130000 120 554
          (by decide) LocatorAuxiliaryArithmetic.auxiliary176_shape
        exact reconstruct_mem_globalCoefficientBox K
          72627600 131071 130000 120 v.1
      have hmul := weightedTotalDegree_mul residualYSWeights F.1 (q v) hF hqv
      rw [← hprod v] at hmul
      simp only [wt] at hsrc ⊢
      omega
  intro d hd
  have hb := hqbox v hd
  have hy := (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans hqYS
  rw [weight_fin4] at hy
  simp only [residualYSWeights] at hy
  refine ⟨hb.1, ?_, hb.2.1, hb.2.2⟩
  simpa [residualYSWeights] using hy

private theorem exists_sourceC_quotient
    (u0 u1 : I → K) (H : P4) (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : KernelC u0 u1,
      F.1 ∣ reconstruct K 72627600 131071 130000 120 v.1) :
    ∃ q : KernelC u0 u1 →ₗ[K] P4,
      Function.Injective q ∧
      (∀ v, reconstruct K 72627600 131071 130000 120 v.1 = F.1 * q v) ∧
      (∀ v, q v ∈ nestedCoefficientBox K
        (72627600 - wt (contactWeights 131071) F.1) 131071
        (130000 - wt residualTotalWeights F.1)
        (554 - wt residualYSWeights F.1)
        (120 - wt residualSWeights F.1)) := by
  let recon := kernelReconstructLinear (K := K) 72627600 131071 130000 120 400
    IRSProfile.domain u0 u1
  have hdivK : ∀ v : KernelC u0 u1, F.1 ∣ recon v := by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hdiv v
  let q := quotientLinear recon F.1 hF hdivK
  have hqinj : Function.Injective q := quotientLinear_injective recon
    (kernelReconstructLinear_injective (K := K) 72627600 131071 130000 120 400
      IRSProfile.domain u0 u1) F.1 hF hdivK
  have hprod (v : KernelC u0 u1) : recon v = F.1 * q v :=
    recon_eq_mul_quotientPolynomial recon F.1 hdivK v
  have hproduct : ∀ v, reconstruct K 72627600 131071 130000 120 v.1 =
      F.1 * q v := by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hprod v
  have hqbox : ∀ v : KernelC u0 u1,
      q v ∈ globalCoefficientBox K
        (72627600 - wt (contactWeights 131071) F.1) 131071
        (130000 - wt residualTotalWeights F.1)
        (120 - wt residualSWeights F.1) :=
    quotient_box_of_full_divisor 72627600 131071 130000 120 400
      (wt (contactWeights 131071) F.1) (wt residualTotalWeights F.1)
      (wt residualSWeights F.1) IRSProfile.domain u0 u1 F.1 hF hdivK
      le_rfl le_rfl le_rfl
  exact ⟨q, hqinj, hproduct,
    sourceC_quotient_nested u0 u1 H F hF q hqinj hproduct hqbox⟩

private theorem sourceC_tstage (H : P4) (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (j : ℕ) :
    130000 - j * wt residualTotalWeights F.1 ≤ stageT (box c) j := by
  obtain ⟨_hr, _hylo, _hyhi, htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  change 130000 - j * wt residualTotalWeights F.1 ≤
    130000 - j * (box c).factorT
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j htlo) 130000

private theorem sourceC_ystage (H : P4) (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (j : ℕ) :
    554 - j * wt residualYSWeights F.1 ≤ stageY sourceC (box c) j := by
  obtain ⟨_hr, hylo, _hyhi, _htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  change 554 - j * wt residualYSWeights F.1 ≤ 554 - j * (box c).ylo
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j hylo) 554

private theorem sourceC_rstage (H : P4) (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (j : ℕ) :
    120 - j * wt residualSWeights F.1 ≤ stageR sourceC (box c) j := by
  obtain ⟨hr, _hylo, _hyhi, _htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  change 120 - j * wt residualSWeights F.1 ≤ 120 - j * (box c).r
  rw [hr]

private theorem sourceC_bandLe (H : P4) (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (j : ℕ) :
    50499 * channelCount
      (130000 - j * wt residualTotalWeights F.1)
      (554 - j * wt residualYSWeights F.1)
      (120 - j * wt residualSWeights F.1) ≤ stageBand sourceC (box c) j := by
  rw [stageBand_eq]
  exact Nat.mul_le_mul_left 50499 (channelCount_mono
    (sourceC_tstage H F c hcell j) (sourceC_ystage H F c hcell j)
    (sourceC_rstage H F c hcell j))

private theorem sourceC_gapLe (u0 u1 : I → K) :
    1743757566946340 ≤ Module.finrank K
      (ConstraintKernel (K := K) 72627600 131071 130000 120 400
        IRSProfile.domain u0 u1) :=
  LocatorSourceCGap.finrank_lower_bound u0 u1

private theorem sourceC_width (H : P4) (F : RegularIndex H) :
    72627600 - wt (contactWeights 131071) F.1 ≤
      (72627600 - 50499 - wt (contactWeights 131071) F.1) + 50499 := by
  omega

private theorem sourceC_count_k
    (n : ℕ) (hncap : n + 1 ≤ 14)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181569 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80575)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : KernelC u0 u1,
      F.1 ∣ reconstruct K 72627600 131071 130000 120 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceC (n + 1) (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) (n + 1) := by
  obtain ⟨q, hqinj, hproduct, hqNested⟩ :=
    exists_sourceC_quotient u0 u1 H F hF hdiv
  exact sourceC_count_k_core n hncap u0 u1 H selected Gamma hdegree hagreement
    hno F hF c hcell q hqinj hproduct hqNested (sourceC_tstage H F c hcell)
    (sourceC_ystage H F c hcell) (sourceC_rstage H F c hcell)
    (sourceC_bandLe H F c hcell) (sourceC_gapLe u0 u1) (sourceC_width H F) hfit

theorem regularSeeds_count_le_chosen
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181569 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80575)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdivA : ∀ v : ConstraintKernel (K := K) 12528261 131071 130000 21 69
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 12528261 131071 130000 21 v.1)
    (hdivAux : ∀ v : ConstraintKernel (K := K) 13072968 131071 130000 21 72
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 13072968 131071 130000 21 v.1)
    (hdivC : ∀ v : ConstraintKernel (K := K) 72627600 131071 130000 120 400
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 72627600 131071 130000 120 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hv : Valid c)
    (hown : LocatorHybridCost.OwnBound (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F)) :
    (regularSeeds H selected Gamma F).card ≤ chosenCost c := by
  classical
  by_cases ho : (box c).ordinaryFits
  · have h := ordinary_count H selected Gamma F c hcell hv hown
    simpa only [chosenCost, ho, if_pos] using h
  have hroutes := (receipt c hv).resolve_left ho
  by_cases hA : RouteFits sourceA 1 (box c)
  · have h := source_one_count 12528261 21 69 95 68264678009 sourceA
      rfl rfl rfl LocatorArithmetic.kernelA_nullity (by decide) (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivA c hcell hA
    simpa only [chosenCost, ho, hA, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hA
  by_cases hAux : RouteFits sourceAux 1 (box c)
  · have h := source_one_count 13072968 21 72 99 534293974082 sourceAux
      rfl rfl rfl LocatorAuxiliaryArithmetic.auxiliary72_nullity
      LocatorAuxiliaryArithmetic.auxiliary72_shape
      LocatorAuxiliaryArithmetic.auxiliary72_capacity
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivAux c hcell hAux
    simpa only [chosenCost, ho, hA, hAux, if_pos, if_false] using h
  have hC : CFits (box c) := hroutes.resolve_left hAux
  have hne : routeDepth sourceC (box c) ≠ 0 := hC
  obtain ⟨n, hn⟩ : ∃ n, routeDepth sourceC (box c) = n + 1 :=
    ⟨routeDepth sourceC (box c) - 1, by omega⟩
  have hfit := routeDepth_spec sourceC (box c) hC
  rw [hn] at hfit
  have h := sourceC_count_k n hfit.2.1 u0 u1 H selected Gamma hdegree
    hagreement hno F hF hdivC c hcell hfit
  simpa only [chosenCost, ho, hA, hAux, hn, if_pos, if_false] using h

end

end LocatorQuotientReplacement
