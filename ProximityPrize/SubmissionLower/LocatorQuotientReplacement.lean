import ProximityPrize.SubmissionLower.LocatorReplacementGridData
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
import ProximityPrize.SubmissionLower.LocatorSixthPowerAvoidance
import ProximityPrize.SubmissionLower.LocatorSeventhPowerAvoidance
import ProximityPrize.SubmissionLower.LocatorEighthPowerAvoidance
import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
import ProximityPrize.SubmissionLower.LocatorSourceCGap
import ProximityPrize.SubmissionLower.LocatorSourceCLongGap
import ProximityPrize.SubmissionLower.LocatorHelperFactorSwitch
import ProximityPrize.SubmissionLower.BF

namespace ProximityPrize.SubmissionLower.LocatorQuotientReplacement

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238
  RCN260 RCN266
open LocatorFactorAggregate LocatorLowQuotient LocatorCoprimeQuotient
  LocatorReplacementGridData
open LocatorEighthPowerAvoidance

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
    (hown : (regularSeeds H selected Gamma F).card ≤
      paddedCost 131072 131073 (regularCumulativeFlag H F)) :
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
  exact hown.trans (by
    simpa only [Box.ordinaryCost] using paddedCost_mono 131072 131073 hbelow)

private theorem count_le_stageCost
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
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
    (by simpa only [stagePair] using (show 131071 < 181589 by decide))
    (by simpa only [stagePair] using (show 181589 ≤ 262144 by decide))
    hdegree hagreement
    (by simpa only [stagePair, UnequalParameters.errors, Nat.reduceSub] using hno)
    hQzero
  simpa only [stageCost] using hcount

private theorem terminal_relPrime
    (H : P4) (F : RegularIndex H) (c : Cell) (src : Source) (j : ℕ)
    (Q : P4) (hQ : Q ≠ 0)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hQT : wt residualTotalWeights Q ≤ stageT src (box c) j)
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
    (hsrcLength : src.length = 230000)
    (hsrcY : src.y = Ysrc) (hsrcR : src.r = s) (hsrcGap : src.gap = gap)
    (hgap : coefficientCount D 131071 230000 s -
      262144 * localRankBound m 230000 s = gap)
    (hshape : D + s ≤ 131071 * (Ysrc + 1))
    (hcapacity : D - 50519 ≤ (m - 1) * 181589 + (131071 - 1))
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := K) D 131071 230000 s m
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K D 131071 230000 s v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits src 1 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost src (box c) 1 := by
  classical
  obtain ⟨_hkpos, _hkcap, _hyroom, _hrroom, _hshapeRoute, hband,
    hterminal, hgates, _hrate⟩ := hfit
  obtain ⟨hr, hylo, _hyhi, htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  have hqT : 230000 - wt residualTotalWeights F.1 ≤ stageT src (box c) 1 := by
    simpa only [stageT, Nat.one_mul, hsrcLength] using
      Nat.sub_le_sub_left htlo 230000
  have hqY : Ysrc - wt residualYSWeights F.1 ≤ stageY src (box c) 1 := by
    rw [stageY, Nat.one_mul, hsrcY]
    exact Nat.sub_le_sub_left hylo Ysrc
  have hqR : s - wt residualSWeights F.1 ≤ stageR src (box c) 1 := by
    rw [stageR, Nat.one_mul, hsrcR, hr]
  have hchannels := channelCount_mono hqT hqY hqR
  have hsource : 50519 * channelCount
      (230000 - wt residualTotalWeights F.1)
      (Ysrc - wt residualYSWeights F.1)
      (s - wt residualSWeights F.1) <
      coefficientCount D 131071 230000 s -
        Fintype.card I * localRankBound m 230000 s := by
    rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index], hgap]
    exact (Nat.mul_le_mul_left 50519 hchannels).trans_lt (by
      simpa only [bandSum, stageBand, hsrcGap] using hband)
  obtain ⟨_v, Q, _hv, hQ, _heq, hQbox, _hparent, hproduct⟩ :=
    exists_fixed_quotient_with_derivative_vanishing (K := K) (I := I)
      D 131071 230000 s m Ysrc 50519 181589 IRSProfile.domain u0 u1
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
    simpa only [pairGatesThrough] using hgates
  have hcount := count_le_stageCost u0 u1 H selected Gamma hdegree hagreement
    hno F c hcell src 1 Q hQ hQT hQY hQR hrel hgate hQzero
  simpa only [routeCost] using hcount

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

private theorem sourceC_power_count
    (j : ℕ) (hjpos : 1 ≤ j) (hjcap : j ≤ 8)
    (L : ℕ) (src : Source)
    (hsrcLength : src.length = L) (hsrcY : src.y = 333)
    (hsrcR : src.r = 71)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (v : ConstraintKernel (K := K) 43762949 131071 L 71 241
      IRSProfile.domain u0 u1)
    (Q : P4) (hQ : Q ≠ 0)
    (heq : reconstruct K 43762949 131071 L 71 v.1 = F.1 ^ j * Q)
    (hcQ : wt (contactWeights 131071) Q <
      43762949 - j * 50519 - j * wt (contactWeights 131071) F.1)
    (htQ : wt residualTotalWeights Q ≤
      L - j * wt residualTotalWeights F.1)
    (hyQ : wt residualYSWeights Q ≤
      333 - j * wt residualYSWeights F.1)
    (hrQ : wt residualSWeights Q ≤
      71 - j * wt residualSWeights F.1)
    (hrel : IsRelPrime F.1 Q)
    (hgate : PairGates (stagePair src (box c) j)) :
    (regularSeeds H selected Gamma F).card ≤ stageCost src (box c) j := by
  classical
  have hlow : reconstruct K 43762949 131071 L 71 v.1 ∈
      globalCoefficientBox K (43762949 - j * 50519) 131071 L 71 :=
    reconstruct_mem_low_of_power IRSProfile.domain u0 u1 v F.1 Q heq
      (by decide) (by omega) hcQ
  obtain ⟨hr, hylo, _hyhi, htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  have hQT : wt residualTotalWeights Q ≤ stageT src (box c) j := by
    apply htQ.trans
    rw [stageT, hsrcLength]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j htlo) L
  have hQY : wt residualYSWeights Q ≤ stageY src (box c) j := by
    apply hyQ.trans
    rw [stageY, hsrcY]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j hylo) 333
  have hQR : wt residualSWeights Q ≤ stageR src (box c) j := by
    apply hrQ.trans
    rw [stageR, hsrcR]
    rw [hr]
  have htwo : (2 : K) ≠ 0 := by
    intro hz
    have hdvd : 2130706433 ∣ 2 :=
      (CharP.cast_eq_zero_iff K 2130706433 2).mp hz
    norm_num at hdvd
  have hsix : (6 : K) ≠ 0 := by
    intro hz
    have hdvd : 2130706433 ∣ 6 :=
      (CharP.cast_eq_zero_iff K 2130706433 6).mp hz
    norm_num at hdvd
  have h24 : (24 : K) ≠ 0 := by
    intro hz
    have hdvd : 2130706433 ∣ 24 :=
      (CharP.cast_eq_zero_iff K 2130706433 24).mp hz
    norm_num at hdvd
  have h120 : (120 : K) ≠ 0 := by
    intro hz
    have hdvd : 2130706433 ∣ 120 :=
      (CharP.cast_eq_zero_iff K 2130706433 120).mp hz
    norm_num at hdvd
  have h720 : (720 : K) ≠ 0 := by
    intro hz
    have hdvd : 2130706433 ∣ 720 :=
      (CharP.cast_eq_zero_iff K 2130706433 720).mp hz
    norm_num at hdvd
  have h5040 : (5040 : K) ≠ 0 := by
    intro hz
    have hdvd : 2130706433 ∣ 5040 :=
      (CharP.cast_eq_zero_iff K 2130706433 5040).mp hz
    norm_num at hdvd
  have h40320 : (40320 : K) ≠ 0 := by
    intro hz
    have hdvd : 2130706433 ∣ 40320 :=
      (CharP.cast_eq_zero_iff K 2130706433 40320).mp hz
    norm_num at hdvd
  interval_cases j
  · have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q = 0 := by
      intro gamma hgamma
      have hgammaG := regularSeeds_subset H selected Gamma F hgamma
      let support := (Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
      have hcard : 181589 ≤ support.card := hagreement gamma hgammaG
      have hcap : 43762949 - 50519 ≤
          (241 - 1) * support.card + (131071 - 1) :=
        LocatorAuxiliaryArithmetic.auxiliary176_capacity.trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left (241 - 1) hcard) _)
      have hvalues : ∀ i ∈ support,
          (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      have hder := specialization_pderiv_R_eq_zero_of_kernel_low_box
        43762949 (43762949 - 50519) 131071 L 71 241
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hgammaG) hcap hvalues
      obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
      have hmul :
          RCN319.specialization K (selected gamma) gamma
              (MvPolynomial.pderiv (2 : Fin 4) F.1) *
            RCN319.specialization K (selected gamma) gamma Q = 0 := by
        rw [heq] at hder
        simpa only [pow_one, MvPolynomial.pderiv_mul, map_add, map_mul,
          hFzero, zero_mul, add_zero] using hder
      exact (mul_eq_zero.mp hmul).resolve_left hregular
    exact count_le_stageCost u0 u1 H selected Gamma hdegree hagreement hno
      F c hcell src 1 Q hQ hQT hQY hQR hrel hgate hQzero
  · have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q = 0 := by
      intro gamma hgamma
      have hgammaG := regularSeeds_subset H selected Gamma F hgamma
      let support := (Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
      have hcard : 181589 ≤ support.card := hagreement gamma hgammaG
      have hcap : 43762949 - 2 * 50519 ≤
          (241 - 2) * support.card + 2 * (131071 - 1) :=
        LocatorAuxiliaryArithmetic.auxiliary176_double_capacity.trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left (241 - 2) hcard) _)
      have hvalues : ∀ i ∈ support,
          (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      have hder := LocatorDoubleSquareAvoidance.specialization_pderiv_R2_eq_zero_of_kernel_low_box
        43762949 (43762949 - 2 * 50519) 131071 L 71 241
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hgammaG) hcap hvalues
      have heq' : reconstruct K 43762949 131071 L 71 v.1 =
          F.1 * (F.1 * Q) := by rw [heq]; ring
      rw [heq'] at hder
      obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
      exact LocatorDoubleSquareAvoidance.specialization_eq_zero_of_pderiv_R2_square_product
        (selected gamma) gamma F.1 Q htwo hFzero hregular hder
    exact count_le_stageCost u0 u1 H selected Gamma hdegree hagreement hno
      F c hcell src 2 Q hQ hQT hQY hQR hrel hgate hQzero
  · have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q = 0 := by
      intro gamma hgamma
      have hgammaG := regularSeeds_subset H selected Gamma F hgamma
      let support := (Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
      have hcard : 181589 ≤ support.card := hagreement gamma hgammaG
      have hcap : 43762949 - 3 * 50519 ≤
          (241 - 3) * support.card + 3 * (131071 - 1) := by
        apply (show 43762949 - 3 * 50519 ≤
          (241 - 3) * 181589 + 3 * (131071 - 1) by decide).trans
        exact Nat.add_le_add_right (Nat.mul_le_mul_left (241 - 3) hcard) _
      have hvalues : ∀ i ∈ support,
          (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      have hder := LocatorTripleCubeAvoidance.specialization_pderiv_R3_eq_zero_of_kernel_low_box
        43762949 (43762949 - 3 * 50519) 131071 L 71 241
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hgammaG) hcap hvalues
      have heq' : reconstruct K 43762949 131071 L 71 v.1 =
          F.1 * (F.1 * (F.1 * Q)) := by rw [heq]; ring
      rw [heq'] at hder
      obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
      exact LocatorTripleCubeAvoidance.specialization_eq_zero_of_pderiv_R3_cube_product
        (selected gamma) gamma F.1 Q hsix hFzero hregular hder
    exact count_le_stageCost u0 u1 H selected Gamma hdegree hagreement hno
      F c hcell src 3 Q hQ hQT hQY hQR hrel hgate hQzero
  · have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q = 0 := by
      intro gamma hgamma
      have hgammaG := regularSeeds_subset H selected Gamma F hgamma
      let support := (Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
      have hcard : 181589 ≤ support.card := hagreement gamma hgammaG
      have hcap : 43762949 - 4 * 50519 ≤
          (241 - 4) * support.card + 4 * (131071 - 1) := by
        apply (show 43762949 - 4 * 50519 ≤
          (241 - 4) * 181589 + 4 * (131071 - 1) by decide).trans
        exact Nat.add_le_add_right (Nat.mul_le_mul_left (241 - 4) hcard) _
      have hvalues : ∀ i ∈ support,
          (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      have hder := LocatorFourthPowerAvoidance.specialization_pderiv_R4_eq_zero_of_kernel_low_box
        43762949 (43762949 - 4 * 50519) 131071 L 71 241
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hgammaG) hcap hvalues
      have heq' : reconstruct K 43762949 131071 L 71 v.1 =
          F.1 * (F.1 * (F.1 * (F.1 * Q))) := by rw [heq]; ring
      rw [heq'] at hder
      obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
      exact LocatorFourthPowerAvoidance.specialization_eq_zero_of_pderiv_R4_fourth_product
        (selected gamma) gamma F.1 Q h24 hFzero hregular hder
    exact count_le_stageCost u0 u1 H selected Gamma hdegree hagreement hno
      F c hcell src 4 Q hQ hQT hQY hQR hrel hgate hQzero
  · have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q = 0 := by
      intro gamma hgamma
      have hgammaG := regularSeeds_subset H selected Gamma F hgamma
      let support := (Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
      have hcard : 181589 ≤ support.card := hagreement gamma hgammaG
      have hcap : 43762949 - 5 * 50519 ≤
          (241 - 5) * support.card + 5 * (131071 - 1) := by
        apply (show 43762949 - 5 * 50519 ≤
          (241 - 5) * 181589 + 5 * (131071 - 1) by decide).trans
        exact Nat.add_le_add_right (Nat.mul_le_mul_left (241 - 5) hcard) _
      have hvalues : ∀ i ∈ support,
          (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      have hder := LocatorFifthPowerAvoidance.specialization_pderiv_R5_eq_zero_of_kernel_low_box
        43762949 (43762949 - 5 * 50519) 131071 L 71 241
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hgammaG) hcap hvalues
      have heq' : reconstruct K 43762949 131071 L 71 v.1 =
          F.1 * (F.1 * (F.1 * (F.1 * (F.1 * Q)))) := by rw [heq]; ring
      rw [heq'] at hder
      obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
      exact LocatorFifthPowerAvoidance.specialization_eq_zero_of_pderiv_R5_fifth_product
        (selected gamma) gamma F.1 Q h120 hFzero hregular hder
    exact count_le_stageCost u0 u1 H selected Gamma hdegree hagreement hno
      F c hcell src 5 Q hQ hQT hQY hQR hrel hgate hQzero
  · have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q = 0 := by
      intro gamma hgamma
      have hgammaG := regularSeeds_subset H selected Gamma F hgamma
      let support := (Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
      have hcard : 181589 ≤ support.card := hagreement gamma hgammaG
      have hcap : 43762949 - 6 * 50519 ≤
          (241 - 6) * support.card + 6 * (131071 - 1) := by
        apply (show 43762949 - 6 * 50519 ≤
          (241 - 6) * 181589 + 6 * (131071 - 1) by decide).trans
        exact Nat.add_le_add_right (Nat.mul_le_mul_left (241 - 6) hcard) _
      have hvalues : ∀ i ∈ support,
          (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      have hder := LocatorSixthPowerAvoidance.specialization_pderiv_R6_eq_zero_of_kernel_low_box
        43762949 (43762949 - 6 * 50519) 131071 L 71 241
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hgammaG) hcap hvalues
      have heq' : reconstruct K 43762949 131071 L 71 v.1 =
          F.1 * (F.1 * (F.1 * (F.1 * (F.1 * (F.1 * Q))))) := by rw [heq]; ring
      rw [heq'] at hder
      obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
      exact LocatorSixthPowerAvoidance.specialization_eq_zero_of_pderiv_R6_sixth_product
        (selected gamma) gamma F.1 Q h720 hFzero hregular hder
    exact count_le_stageCost u0 u1 H selected Gamma hdegree hagreement hno
      F c hcell src 6 Q hQ hQT hQY hQR hrel hgate hQzero
  · have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q = 0 := by
      intro gamma hgamma
      have hgammaG := regularSeeds_subset H selected Gamma F hgamma
      let support := (Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
      have hcard : 181589 ≤ support.card := hagreement gamma hgammaG
      have hcap : 43762949 - 7 * 50519 ≤
          (241 - 7) * support.card + 7 * (131071 - 1) := by
        apply (show 43762949 - 7 * 50519 ≤
          (241 - 7) * 181589 + 7 * (131071 - 1) by decide).trans
        exact Nat.add_le_add_right (Nat.mul_le_mul_left (241 - 7) hcard) _
      have hvalues : ∀ i ∈ support,
          (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      have hder :=
        LocatorSeventhPowerAvoidance.specialization_pderiv_R7_eq_zero_of_kernel_low_box
          43762949 (43762949 - 7 * 50519) 131071 L 71 241
          IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
          (by decide) (hdegree gamma hgammaG) hcap hvalues
      have heq' : reconstruct K 43762949 131071 L 71 v.1 =
          F.1 * (F.1 * (F.1 * (F.1 * (F.1 * (F.1 * (F.1 * Q)))))) := by
        rw [heq]
        ring
      rw [heq'] at hder
      obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
      exact
        LocatorSeventhPowerAvoidance.specialization_eq_zero_of_pderiv_R7_seventh_product
          (selected gamma) gamma F.1 Q h5040 hFzero hregular hder
    exact count_le_stageCost u0 u1 H selected Gamma hdegree hagreement hno
      F c hcell src 7 Q hQ hQT hQY hQR hrel hgate hQzero
  · have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q = 0 := by
      intro gamma hgamma
      have hgammaG := regularSeeds_subset H selected Gamma F hgamma
      let support := (Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
      have hcard : 181589 ≤ support.card := hagreement gamma hgammaG
      have hcap : 43762949 - 8 * 50519 ≤
          (241 - 8) * support.card + 8 * (131071 - 1) := by
        apply (show 43762949 - 8 * 50519 ≤
          (241 - 8) * 181589 + 8 * (131071 - 1) by decide).trans
        exact Nat.add_le_add_right (Nat.mul_le_mul_left (241 - 8) hcard) _
      have hvalues : ∀ i ∈ support,
          (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      have hder :=
        LocatorEighthPowerAvoidance.specialization_pderiv_R8_eq_zero_of_kernel_low_box
          43762949 (43762949 - 8 * 50519) 131071 L 71 241
          IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
          (by decide) (hdegree gamma hgammaG) hcap hvalues
      rw [heq] at hder
      obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
      exact
        LocatorEighthPowerAvoidance.specialization_eq_zero_of_pderiv_R8_eighth_product
          (selected gamma) gamma F.1 Q h40320 hFzero hregular hder
    exact count_le_stageCost u0 u1 H selected Gamma hdegree hagreement hno
      F c hcell src 8 Q hQ hQT hQY hQR hrel hgate hQzero

private abbrev KernelC (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 43762949 131071 230000 71 241
    IRSProfile.domain u0 u1

private theorem sub_two_mul (a b : ℕ) : a - 2 * b = a - b - b := by omega
private theorem sub_three_mul (a b : ℕ) : a - 3 * b = a - b - 2 * b := by omega
private theorem sub_four_mul (a b : ℕ) : a - 4 * b = a - b - 3 * b := by omega
private theorem sub_five_mul (a b : ℕ) : a - 5 * b = a - b - 4 * b := by omega
private theorem sub_six_mul (a b : ℕ) : a - 6 * b = a - b - 5 * b := by omega
private theorem sub_seven_mul (a b : ℕ) : a - 7 * b = a - b - 6 * b := by omega
private theorem sub_eight_mul (a b : ℕ) : a - 8 * b = a - b - 7 * b := by omega
private theorem sub_succ_mul (a b j : ℕ) :
    a - b - j * b = a - (j + 1) * b := by
  rw [Nat.add_mul, Nat.one_mul]
  omega
private theorem sub_two_succ_mul (a b c j : ℕ) :
    a - b - c - j * b - j * c = a - (j + 1) * b - (j + 1) * c := by
  simp only [Nat.add_mul, Nat.one_mul]
  omega

private theorem sourceC_count_k2_core
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (q : KernelC u0 u1 →ₗ[K] P4) (hqinj : Function.Injective q)
    (hprod : ∀ v, reconstruct K 43762949 131071 230000 71 v.1 = F.1 * q v)
    (hqNested : ∀ v, q v ∈ nestedCoefficientBox K
      (43762949 - wt (contactWeights 131071) F.1) 131071
      (230000 - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1)
      (71 - wt residualSWeights F.1))
    (hTstage : ∀ j, 230000 - j * wt residualTotalWeights F.1 ≤ stageT sourceC (box c) j)
    (hYstage : ∀ j, 333 - j * wt residualYSWeights F.1 ≤ stageY sourceC (box c) j)
    (hRstage : ∀ j, 71 - j * wt residualSWeights F.1 ≤ stageR sourceC (box c) j)
    (hbandLe : ∀ j, 50519 * channelCount
      (230000 - j * wt residualTotalWeights F.1)
      (333 - j * wt residualYSWeights F.1)
      (71 - j * wt residualSWeights F.1) ≤ stageBand sourceC (box c) j)
    (hgapLe : 96314062520372778 ≤ Module.finrank K
      (ConstraintKernel (K := K) 43762949 131071 230000 71 241
        IRSProfile.domain u0 u1))
    (hwidth : 43762949 - wt (contactWeights 131071) F.1 ≤
      (43762949 - 50519 - wt (contactWeights 131071) F.1) + 50519)
    (hfit : RouteFits sourceC 2 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 2 := by
  classical
  obtain ⟨_hkpos, _hkcap, _hyroom, _hrroom, _hshapeRoute, hband,
    hterminal, hgates, _hrate⟩ := hfit
  have hsource :
      50519 * channelCount
          (230000 - wt residualTotalWeights F.1)
          (333 - wt residualYSWeights F.1)
          (71 - wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 2 * wt residualTotalWeights F.1)
          (333 - 2 * wt residualYSWeights F.1)
          (71 - 2 * wt residualSWeights F.1) <
      Module.finrank K (ConstraintKernel (K := K)
        43762949 131071 230000 71 241 IRSProfile.domain u0 u1) := by
    apply (Nat.add_le_add
      (by simpa only [Nat.one_mul] using hbandLe 1) (hbandLe 2)).trans_lt
    have hstages : stageBand sourceC (box c) 1 +
        stageBand sourceC (box c) 2 < 96314062520372778 := by
      simpa only [bandSum, sourceC] using hband
    exact hstages.trans_le hgapLe
  rcases LocatorDoubleSquareAvoidance.exists_first_low_not_dvd_or_second_low
      (43762949 - wt (contactWeights 131071) F.1)
      (43762949 - 50519 - wt (contactWeights 131071) F.1)
      131071 50519 (230000 - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1) (71 - wt residualSWeights F.1)
      hwidth q hqinj hqNested F.1 hF
        (by simpa only [sub_two_mul] using hsource) with hfirst | hsecond
  · obtain ⟨v, _hv, hQ, hQbox, hnot⟩ := hfirst
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 =
        F.1 ^ 1 * q v := by simpa only [pow_one] using hprod v
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 1 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v (q v) hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hQbox⟩ := hsecond
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 2 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := terminal_relPrime H F c sourceC 2 Q hQ hcell
      (by have h := hTstage 2; omega)
      (by have h := hYstage 2; omega)
      (by have h := hRstage 2; omega) hterminal
    have hcount := sourceC_power_count 2 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2
    exact hcount.trans (by simp [routeCost])

private theorem sourceC_count_k3_core
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (q : KernelC u0 u1 →ₗ[K] P4) (hqinj : Function.Injective q)
    (hprod : ∀ v, reconstruct K 43762949 131071 230000 71 v.1 = F.1 * q v)
    (hqNested : ∀ v, q v ∈ nestedCoefficientBox K
      (43762949 - wt (contactWeights 131071) F.1) 131071
      (230000 - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1)
      (71 - wt residualSWeights F.1))
    (hTstage : ∀ j, 230000 - j * wt residualTotalWeights F.1 ≤ stageT sourceC (box c) j)
    (hYstage : ∀ j, 333 - j * wt residualYSWeights F.1 ≤ stageY sourceC (box c) j)
    (hRstage : ∀ j, 71 - j * wt residualSWeights F.1 ≤ stageR sourceC (box c) j)
    (hbandLe : ∀ j, 50519 * channelCount
      (230000 - j * wt residualTotalWeights F.1)
      (333 - j * wt residualYSWeights F.1)
      (71 - j * wt residualSWeights F.1) ≤ stageBand sourceC (box c) j)
    (hgapLe : 96314062520372778 ≤ Module.finrank K
      (ConstraintKernel (K := K) 43762949 131071 230000 71 241
        IRSProfile.domain u0 u1))
    (hwidth : 43762949 - wt (contactWeights 131071) F.1 ≤
      (43762949 - 50519 - wt (contactWeights 131071) F.1) + 50519)
    (hfit : RouteFits sourceC 3 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 3 := by
  classical
  obtain ⟨_hkpos, _hkcap, _hyroom, _hrroom, _hshapeRoute, hband,
    hterminal, hgates, _hrate⟩ := hfit
  have hsource :
      50519 * channelCount
          (230000 - wt residualTotalWeights F.1)
          (333 - wt residualYSWeights F.1)
          (71 - wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 2 * wt residualTotalWeights F.1)
          (333 - 2 * wt residualYSWeights F.1)
          (71 - 2 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 3 * wt residualTotalWeights F.1)
          (333 - 3 * wt residualYSWeights F.1)
          (71 - 3 * wt residualSWeights F.1) <
      Module.finrank K (ConstraintKernel (K := K)
        43762949 131071 230000 71 241 IRSProfile.domain u0 u1) := by
    apply (Nat.add_le_add (Nat.add_le_add
      (by simpa only [Nat.one_mul] using hbandLe 1) (hbandLe 2))
      (hbandLe 3)).trans_lt
    have hstages : stageBand sourceC (box c) 1 +
          stageBand sourceC (box c) 2 + stageBand sourceC (box c) 3 <
        96314062520372778 := by
      simpa only [bandSum, sourceC] using hband
    exact hstages.trans_le hgapLe
  rcases LocatorTripleCubeAvoidance.exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low
      (43762949 - wt (contactWeights 131071) F.1)
      (43762949 - 50519 - wt (contactWeights 131071) F.1)
      131071 50519 (230000 - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1) (71 - wt residualSWeights F.1)
      hwidth q hqinj hqNested F.1 hF
        (by simpa only [sub_two_mul, sub_three_mul] using hsource) with
      hfirst | hsecond | hthird
  · obtain ⟨v, _hv, hQ, hQbox, hnot⟩ := hfirst
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 =
        F.1 ^ 1 * q v := by simpa only [pow_one] using hprod v
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 1 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v (q v) hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hsecond
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 2 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 2 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hQbox⟩ := hthird
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 3 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := terminal_relPrime H F c sourceC 3 Q hQ hcell
      (by have h := hTstage 3; omega)
      (by have h := hYstage 3; omega)
      (by have h := hRstage 3; omega) hterminal
    have hcount := sourceC_power_count 3 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2
    exact hcount.trans (by simp [routeCost])

private theorem sourceC_count_k4_core
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (q : KernelC u0 u1 →ₗ[K] P4) (hqinj : Function.Injective q)
    (hprod : ∀ v, reconstruct K 43762949 131071 230000 71 v.1 = F.1 * q v)
    (hqNested : ∀ v, q v ∈ nestedCoefficientBox K
      (43762949 - wt (contactWeights 131071) F.1) 131071
      (230000 - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1)
      (71 - wt residualSWeights F.1))
    (hTstage : ∀ j, 230000 - j * wt residualTotalWeights F.1 ≤ stageT sourceC (box c) j)
    (hYstage : ∀ j, 333 - j * wt residualYSWeights F.1 ≤ stageY sourceC (box c) j)
    (hRstage : ∀ j, 71 - j * wt residualSWeights F.1 ≤ stageR sourceC (box c) j)
    (hbandLe : ∀ j, 50519 * channelCount
      (230000 - j * wt residualTotalWeights F.1)
      (333 - j * wt residualYSWeights F.1)
      (71 - j * wt residualSWeights F.1) ≤ stageBand sourceC (box c) j)
    (hgapLe : 96314062520372778 ≤ Module.finrank K
      (ConstraintKernel (K := K) 43762949 131071 230000 71 241
        IRSProfile.domain u0 u1))
    (hwidth : 43762949 - wt (contactWeights 131071) F.1 ≤
      (43762949 - 50519 - wt (contactWeights 131071) F.1) + 50519)
    (hfit : RouteFits sourceC 4 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 4 := by
  classical
  obtain ⟨_hkpos, _hkcap, _hyroom, _hrroom, _hshapeRoute, hband,
    hterminal, hgates, _hrate⟩ := hfit
  have hsource :
      50519 * channelCount
          (230000 - wt residualTotalWeights F.1)
          (333 - wt residualYSWeights F.1)
          (71 - wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 2 * wt residualTotalWeights F.1)
          (333 - 2 * wt residualYSWeights F.1)
          (71 - 2 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 3 * wt residualTotalWeights F.1)
          (333 - 3 * wt residualYSWeights F.1)
          (71 - 3 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 4 * wt residualTotalWeights F.1)
          (333 - 4 * wt residualYSWeights F.1)
          (71 - 4 * wt residualSWeights F.1) <
      Module.finrank K (ConstraintKernel (K := K)
        43762949 131071 230000 71 241 IRSProfile.domain u0 u1) := by
    apply (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add
        (by simpa only [Nat.one_mul] using hbandLe 1) (hbandLe 2)) (hbandLe 3))
      (hbandLe 4)).trans_lt
    have hstages : stageBand sourceC (box c) 1 +
            stageBand sourceC (box c) 2 + stageBand sourceC (box c) 3 +
          stageBand sourceC (box c) 4 < 96314062520372778 := by
      simpa only [bandSum, sourceC] using hband
    exact hstages.trans_le hgapLe
  rcases LocatorFourthPowerAvoidance.exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low_not_dvd_or_fourth_low
      (43762949 - wt (contactWeights 131071) F.1)
      (43762949 - 50519 - wt (contactWeights 131071) F.1)
      131071 50519 (230000 - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1) (71 - wt residualSWeights F.1)
      hwidth q hqinj hqNested F.1 hF
        (by simpa only [sub_two_mul, sub_three_mul, sub_four_mul] using hsource) with
    hfirst | hsecond | hthird | hfourth
  · obtain ⟨v, _hv, hQ, hQbox, hnot⟩ := hfirst
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 =
        F.1 ^ 1 * q v := by simpa only [pow_one] using hprod v
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 1 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v (q v) hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hsecond
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 2 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 2 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hthird
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 3 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 3 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hQbox⟩ := hfourth
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 4 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := terminal_relPrime H F c sourceC 4 Q hQ hcell
      (by have h := hTstage 4; omega)
      (by have h := hYstage 4; omega)
      (by have h := hRstage 4; omega) hterminal
    have hcount := sourceC_power_count 4 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.2
    exact hcount.trans (by simp [routeCost])

private theorem sourceC_count_k5_core
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (q : KernelC u0 u1 →ₗ[K] P4) (hqinj : Function.Injective q)
    (hprod : ∀ v, reconstruct K 43762949 131071 230000 71 v.1 = F.1 * q v)
    (hqNested : ∀ v, q v ∈ nestedCoefficientBox K
      (43762949 - wt (contactWeights 131071) F.1) 131071
      (230000 - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1)
      (71 - wt residualSWeights F.1))
    (hTstage : ∀ j, 230000 - j * wt residualTotalWeights F.1 ≤ stageT sourceC (box c) j)
    (hYstage : ∀ j, 333 - j * wt residualYSWeights F.1 ≤ stageY sourceC (box c) j)
    (hRstage : ∀ j, 71 - j * wt residualSWeights F.1 ≤ stageR sourceC (box c) j)
    (hbandLe : ∀ j, 50519 * channelCount
      (230000 - j * wt residualTotalWeights F.1)
      (333 - j * wt residualYSWeights F.1)
      (71 - j * wt residualSWeights F.1) ≤ stageBand sourceC (box c) j)
    (hgapLe : 96314062520372778 ≤ Module.finrank K
      (ConstraintKernel (K := K) 43762949 131071 230000 71 241
        IRSProfile.domain u0 u1))
    (hwidth : 43762949 - wt (contactWeights 131071) F.1 ≤
      (43762949 - 50519 - wt (contactWeights 131071) F.1) + 50519)
    (hfit : RouteFits sourceC 5 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 5 := by
  classical
  obtain ⟨_hkpos, _hkcap, _hyroom, _hrroom, _hshapeRoute, hband,
    hterminal, hgates, _hrate⟩ := hfit
  have hsource :
      50519 * channelCount
          (230000 - wt residualTotalWeights F.1)
          (333 - wt residualYSWeights F.1)
          (71 - wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 2 * wt residualTotalWeights F.1)
          (333 - 2 * wt residualYSWeights F.1)
          (71 - 2 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 3 * wt residualTotalWeights F.1)
          (333 - 3 * wt residualYSWeights F.1)
          (71 - 3 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 4 * wt residualTotalWeights F.1)
          (333 - 4 * wt residualYSWeights F.1)
          (71 - 4 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 5 * wt residualTotalWeights F.1)
          (333 - 5 * wt residualYSWeights F.1)
          (71 - 5 * wt residualSWeights F.1) <
      Module.finrank K (ConstraintKernel (K := K)
        43762949 131071 230000 71 241 IRSProfile.domain u0 u1) := by
    apply (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add
          (by simpa only [Nat.one_mul] using hbandLe 1) (hbandLe 2)) (hbandLe 3))
        (hbandLe 4)) (hbandLe 5)).trans_lt
    have hstages : stageBand sourceC (box c) 1 +
              stageBand sourceC (box c) 2 + stageBand sourceC (box c) 3 +
            stageBand sourceC (box c) 4 + stageBand sourceC (box c) 5 <
        96314062520372778 := by
      simpa only [bandSum, sourceC] using hband
    exact hstages.trans_le hgapLe
  rcases LocatorFifthPowerAvoidance.exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low_not_dvd_or_fourth_low_not_dvd_or_fifth_low
      (43762949 - wt (contactWeights 131071) F.1)
      (43762949 - 50519 - wt (contactWeights 131071) F.1)
      131071 50519 (230000 - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1) (71 - wt residualSWeights F.1)
      hwidth q hqinj hqNested F.1 hF
        (by simpa only [sub_two_mul, sub_three_mul, sub_four_mul, sub_five_mul]
          using hsource) with
    hfirst | hsecond | hthird | hfourth | hfifth
  · obtain ⟨v, _hv, hQ, hQbox, hnot⟩ := hfirst
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 =
        F.1 ^ 1 * q v := by simpa only [pow_one] using hprod v
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 1 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v (q v) hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hsecond
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 2 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 2 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hthird
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 3 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 3 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hfourth
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 4 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 4 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hQbox⟩ := hfifth
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 5 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := terminal_relPrime H F c sourceC 5 Q hQ hcell
      (by have h := hTstage 5; omega)
      (by have h := hYstage 5; omega)
      (by have h := hRstage 5; omega) hterminal
    have hcount := sourceC_power_count 5 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.2.2
    exact hcount.trans (by simp [routeCost])

private theorem sourceC_count_k6_core
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (q : KernelC u0 u1 →ₗ[K] P4) (hqinj : Function.Injective q)
    (hprod : ∀ v, reconstruct K 43762949 131071 230000 71 v.1 = F.1 * q v)
    (hqNested : ∀ v, q v ∈ nestedCoefficientBox K
      (43762949 - wt (contactWeights 131071) F.1) 131071
      (230000 - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1)
      (71 - wt residualSWeights F.1))
    (hTstage : ∀ j, 230000 - j * wt residualTotalWeights F.1 ≤ stageT sourceC (box c) j)
    (hYstage : ∀ j, 333 - j * wt residualYSWeights F.1 ≤ stageY sourceC (box c) j)
    (hRstage : ∀ j, 71 - j * wt residualSWeights F.1 ≤ stageR sourceC (box c) j)
    (hbandLe : ∀ j, 50519 * channelCount
      (230000 - j * wt residualTotalWeights F.1)
      (333 - j * wt residualYSWeights F.1)
      (71 - j * wt residualSWeights F.1) ≤ stageBand sourceC (box c) j)
    (hgapLe : 96314062520372778 ≤ Module.finrank K
      (ConstraintKernel (K := K) 43762949 131071 230000 71 241
        IRSProfile.domain u0 u1))
    (hwidth : 43762949 - wt (contactWeights 131071) F.1 ≤
      (43762949 - 50519 - wt (contactWeights 131071) F.1) + 50519)
    (hfit : RouteFits sourceC 6 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 6 := by
  classical
  obtain ⟨_hkpos, _hkcap, _hyroom, _hrroom, _hshapeRoute, hband,
    hterminal, hgates, _hrate⟩ := hfit
  have hsource :
      50519 * channelCount
          (230000 - wt residualTotalWeights F.1)
          (333 - wt residualYSWeights F.1)
          (71 - wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 2 * wt residualTotalWeights F.1)
          (333 - 2 * wt residualYSWeights F.1)
          (71 - 2 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 3 * wt residualTotalWeights F.1)
          (333 - 3 * wt residualYSWeights F.1)
          (71 - 3 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 4 * wt residualTotalWeights F.1)
          (333 - 4 * wt residualYSWeights F.1)
          (71 - 4 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 5 * wt residualTotalWeights F.1)
          (333 - 5 * wt residualYSWeights F.1)
          (71 - 5 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 6 * wt residualTotalWeights F.1)
          (333 - 6 * wt residualYSWeights F.1)
          (71 - 6 * wt residualSWeights F.1) <
      Module.finrank K (ConstraintKernel (K := K)
        43762949 131071 230000 71 241 IRSProfile.domain u0 u1) := by
    apply (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add
            (by simpa only [Nat.one_mul] using hbandLe 1) (hbandLe 2))
            (hbandLe 3)) (hbandLe 4)) (hbandLe 5)) (hbandLe 6)).trans_lt
    have hstages : stageBand sourceC (box c) 1 +
              stageBand sourceC (box c) 2 + stageBand sourceC (box c) 3 +
            stageBand sourceC (box c) 4 + stageBand sourceC (box c) 5 +
              stageBand sourceC (box c) 6 <
        96314062520372778 := by
      simpa only [bandSum, sourceC] using hband
    exact hstages.trans_le hgapLe
  rcases LocatorSixthPowerAvoidance.exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low_not_dvd_or_fourth_low_not_dvd_or_fifth_low_not_dvd_or_sixth_low
      (43762949 - wt (contactWeights 131071) F.1)
      (43762949 - 50519 - wt (contactWeights 131071) F.1)
      131071 50519 (230000 - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1) (71 - wt residualSWeights F.1)
      hwidth q hqinj hqNested F.1 hF
        (by simpa only [sub_two_mul, sub_three_mul, sub_four_mul, sub_five_mul,
          sub_six_mul]
          using hsource) with
    hfirst | hsecond | hthird | hfourth | hfifth | hsixth
  · obtain ⟨v, _hv, hQ, hQbox, hnot⟩ := hfirst
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 =
        F.1 ^ 1 * q v := by simpa only [pow_one] using hprod v
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 1 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v (q v) hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.1
    exact hcount.trans (by simp [routeCost])

  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hsecond
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 2 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 2 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hthird
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 3 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 3 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hfourth
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 4 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 4 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hfifth
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 5 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 5 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.2.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hQbox⟩ := hsixth
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 6 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := terminal_relPrime H F c sourceC 6 Q hQ hcell
      (by have h := hTstage 6; omega)
      (by have h := hYstage 6; omega)
      (by have h := hRstage 6; omega) hterminal
    have hcount := sourceC_power_count 6 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.2.2.2
    exact hcount.trans (by simp [routeCost])

private theorem sourceC_count_k7_core
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (q : KernelC u0 u1 →ₗ[K] P4) (hqinj : Function.Injective q)
    (hprod : ∀ v, reconstruct K 43762949 131071 230000 71 v.1 = F.1 * q v)
    (hqNested : ∀ v, q v ∈ nestedCoefficientBox K
      (43762949 - wt (contactWeights 131071) F.1) 131071
      (230000 - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1)
      (71 - wt residualSWeights F.1))
    (hTstage : ∀ j, 230000 - j * wt residualTotalWeights F.1 ≤ stageT sourceC (box c) j)
    (hYstage : ∀ j, 333 - j * wt residualYSWeights F.1 ≤ stageY sourceC (box c) j)
    (hRstage : ∀ j, 71 - j * wt residualSWeights F.1 ≤ stageR sourceC (box c) j)
    (hbandLe : ∀ j, 50519 * channelCount
      (230000 - j * wt residualTotalWeights F.1)
      (333 - j * wt residualYSWeights F.1)
      (71 - j * wt residualSWeights F.1) ≤ stageBand sourceC (box c) j)
    (hgapLe : 96314062520372778 ≤ Module.finrank K
      (ConstraintKernel (K := K) 43762949 131071 230000 71 241
        IRSProfile.domain u0 u1))
    (hwidth : 43762949 - wt (contactWeights 131071) F.1 ≤
      (43762949 - 50519 - wt (contactWeights 131071) F.1) + 50519)
    (hfit : RouteFits sourceC 7 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 7 := by
  classical
  obtain ⟨_hkpos, _hkcap, _hyroom, _hrroom, _hshapeRoute, hband,
    hterminal, hgates, _hrate⟩ := hfit
  have hsource :
      50519 * channelCount
          (230000 - wt residualTotalWeights F.1)
          (333 - wt residualYSWeights F.1)
          (71 - wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 2 * wt residualTotalWeights F.1)
          (333 - 2 * wt residualYSWeights F.1)
          (71 - 2 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 3 * wt residualTotalWeights F.1)
          (333 - 3 * wt residualYSWeights F.1)
          (71 - 3 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 4 * wt residualTotalWeights F.1)
          (333 - 4 * wt residualYSWeights F.1)
          (71 - 4 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 5 * wt residualTotalWeights F.1)
          (333 - 5 * wt residualYSWeights F.1)
          (71 - 5 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 6 * wt residualTotalWeights F.1)
          (333 - 6 * wt residualYSWeights F.1)
          (71 - 6 * wt residualSWeights F.1) +
        50519 * channelCount
          (230000 - 7 * wt residualTotalWeights F.1)
          (333 - 7 * wt residualYSWeights F.1)
          (71 - 7 * wt residualSWeights F.1) <
      Module.finrank K (ConstraintKernel (K := K)
        43762949 131071 230000 71 241 IRSProfile.domain u0 u1) := by
    apply (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (by simpa only [Nat.one_mul] using hbandLe 1)
                (hbandLe 2))
              (hbandLe 3))
            (hbandLe 4))
          (hbandLe 5))
        (hbandLe 6))
      (hbandLe 7)).trans_lt
    have hstages : stageBand sourceC (box c) 1 +
              stageBand sourceC (box c) 2 + stageBand sourceC (box c) 3 +
            stageBand sourceC (box c) 4 + stageBand sourceC (box c) 5 +
          stageBand sourceC (box c) 6 + stageBand sourceC (box c) 7 <
        96314062520372778 := by
      simpa only [bandSum, sourceC] using hband
    exact hstages.trans_le hgapLe
  rcases
    LocatorSeventhPowerAvoidance.exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low_not_dvd_or_fourth_low_not_dvd_or_fifth_low_not_dvd_or_sixth_low_not_dvd_or_seventh_low
      (43762949 - wt (contactWeights 131071) F.1)
      (43762949 - 50519 - wt (contactWeights 131071) F.1)
      131071 50519 (230000 - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1) (71 - wt residualSWeights F.1)
      hwidth q hqinj hqNested F.1 hF
        (by simpa only [sub_two_mul, sub_three_mul, sub_four_mul, sub_five_mul,
          sub_six_mul, sub_seven_mul]
          using hsource) with
    hfirst | hsecond | hthird | hfourth | hfifth | hsixth | hseventh
  · obtain ⟨v, _hv, hQ, hQbox, hnot⟩ := hfirst
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 =
        F.1 ^ 1 * q v := by simpa only [pow_one] using hprod v
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 1 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v (q v) hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hsecond
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 2 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 2 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hthird
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 3 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 3 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hfourth
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 4 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 4 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hfifth
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 5 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 5 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.2.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ := hsixth
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 6 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := (RCN167.positiveRFactors_spec H F.1 F.2).1
      |>.isRelPrime_iff_not_dvd.mpr hnot
    have hcount := sourceC_power_count 6 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.2.2.2.1
    exact hcount.trans (by simp [routeCost])
  · obtain ⟨v, Q, _hv, hQ, hFQ, hQbox⟩ := hseventh
    have hw := nested_mem_weights hQbox hQ
    have heq : reconstruct K 43762949 131071 230000 71 v.1 = F.1 ^ 7 * Q := by
      rw [hprod v, ← hFQ]
      ring
    have hrel := terminal_relPrime H F c sourceC 7 Q hQ hcell
      (by have h := hTstage 7; omega)
      (by have h := hYstage 7; omega)
      (by have h := hRstage 7; omega) hterminal
    have hcount := sourceC_power_count 7 (by decide) (by decide) 230000 sourceC rfl rfl rfl u0 u1 H
      selected Gamma hdegree hagreement hno F c hcell v Q hQ heq
      (by omega) (by omega) (by omega) (by omega) hrel hgates.2.2.2.2.2.2
    exact hcount.trans (by simp [routeCost])

private theorem sourceC_count_k8_core
    (L : ℕ) (src : Source)
    (hsrcLength : src.length = L) (hsrcY : src.y = 333)
    (hsrcR : src.r = 71) (gap : ℕ) (hsrcGap : src.gap = gap)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (q : ConstraintKernel (K := K) 43762949 131071 L 71 241
      IRSProfile.domain u0 u1 →ₗ[K] P4)
    (hqinj : Function.Injective q)
    (hprod : ∀ v, reconstruct K 43762949 131071 L 71 v.1 = F.1 * q v)
    (hqNested : ∀ v, q v ∈ nestedCoefficientBox K
      (43762949 - wt (contactWeights 131071) F.1) 131071
      (L - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1)
      (71 - wt residualSWeights F.1))
    (hTstage : ∀ j, L - j * wt residualTotalWeights F.1 ≤ stageT src (box c) j)
    (hYstage : ∀ j, 333 - j * wt residualYSWeights F.1 ≤ stageY src (box c) j)
    (hRstage : ∀ j, 71 - j * wt residualSWeights F.1 ≤ stageR src (box c) j)
    (hbandLe : ∀ j, 50519 * channelCount
      (L - j * wt residualTotalWeights F.1)
      (333 - j * wt residualYSWeights F.1)
      (71 - j * wt residualSWeights F.1) ≤ stageBand src (box c) j)
    (hgapLe : gap ≤ Module.finrank K
      (ConstraintKernel (K := K) 43762949 131071 L 71 241
        IRSProfile.domain u0 u1))
    (hwidth : 43762949 - wt (contactWeights 131071) F.1 ≤
      (43762949 - 50519 - wt (contactWeights 131071) F.1) + 50519)
    (hfit : RouteFits src 8 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost src (box c) 8 := by
  classical
  obtain ⟨_hkpos, _hkcap, _hyroom, _hrroom, _hshapeRoute, hband,
    hterminal, hgates, _hrate⟩ := hfit
  have h1 := hbandLe 1
  have h2 := hbandLe 2
  have h3 := hbandLe 3
  have h4 := hbandLe 4
  have h5 := hbandLe 5
  have h6 := hbandLe 6
  have h7 := hbandLe 7
  have h8 := hbandLe 8
  simp only [Nat.one_mul] at h1
  have hsource :
      50519 * channelCount
          (L - wt residualTotalWeights F.1)
          (333 - wt residualYSWeights F.1)
          (71 - wt residualSWeights F.1) +
        50519 * channelCount
          (L - 2 * wt residualTotalWeights F.1)
          (333 - 2 * wt residualYSWeights F.1)
          (71 - 2 * wt residualSWeights F.1) +
        50519 * channelCount
          (L - 3 * wt residualTotalWeights F.1)
          (333 - 3 * wt residualYSWeights F.1)
          (71 - 3 * wt residualSWeights F.1) +
        50519 * channelCount
          (L - 4 * wt residualTotalWeights F.1)
          (333 - 4 * wt residualYSWeights F.1)
          (71 - 4 * wt residualSWeights F.1) +
        50519 * channelCount
          (L - 5 * wt residualTotalWeights F.1)
          (333 - 5 * wt residualYSWeights F.1)
          (71 - 5 * wt residualSWeights F.1) +
        50519 * channelCount
          (L - 6 * wt residualTotalWeights F.1)
          (333 - 6 * wt residualYSWeights F.1)
          (71 - 6 * wt residualSWeights F.1) +
        50519 * channelCount
          (L - 7 * wt residualTotalWeights F.1)
          (333 - 7 * wt residualYSWeights F.1)
          (71 - 7 * wt residualSWeights F.1) +
        50519 * channelCount
          (L - 8 * wt residualTotalWeights F.1)
          (333 - 8 * wt residualYSWeights F.1)
          (71 - 8 * wt residualSWeights F.1) <
      Module.finrank K (ConstraintKernel (K := K)
        43762949 131071 L 71 241 IRSProfile.domain u0 u1) := by
    have hsum :
        50519 * channelCount
            (L - wt residualTotalWeights F.1)
            (333 - wt residualYSWeights F.1)
            (71 - wt residualSWeights F.1) +
          50519 * channelCount
            (L - 2 * wt residualTotalWeights F.1)
            (333 - 2 * wt residualYSWeights F.1)
            (71 - 2 * wt residualSWeights F.1) +
          50519 * channelCount
            (L - 3 * wt residualTotalWeights F.1)
            (333 - 3 * wt residualYSWeights F.1)
            (71 - 3 * wt residualSWeights F.1) +
          50519 * channelCount
            (L - 4 * wt residualTotalWeights F.1)
            (333 - 4 * wt residualYSWeights F.1)
            (71 - 4 * wt residualSWeights F.1) +
          50519 * channelCount
            (L - 5 * wt residualTotalWeights F.1)
            (333 - 5 * wt residualYSWeights F.1)
            (71 - 5 * wt residualSWeights F.1) +
          50519 * channelCount
            (L - 6 * wt residualTotalWeights F.1)
            (333 - 6 * wt residualYSWeights F.1)
            (71 - 6 * wt residualSWeights F.1) +
          50519 * channelCount
            (L - 7 * wt residualTotalWeights F.1)
            (333 - 7 * wt residualYSWeights F.1)
            (71 - 7 * wt residualSWeights F.1) +
          50519 * channelCount
            (L - 8 * wt residualTotalWeights F.1)
            (333 - 8 * wt residualYSWeights F.1)
            (71 - 8 * wt residualSWeights F.1) ≤
        stageBand src (box c) 1 + stageBand src (box c) 2 +
          stageBand src (box c) 3 + stageBand src (box c) 4 +
          stageBand src (box c) 5 + stageBand src (box c) 6 +
          stageBand src (box c) 7 + stageBand src (box c) 8 := by omega
    apply hsum.trans_lt
    have hstages : stageBand src (box c) 1 + stageBand src (box c) 2 +
          stageBand src (box c) 3 + stageBand src (box c) 4 +
          stageBand src (box c) 5 + stageBand src (box c) 6 +
          stageBand src (box c) 7 + stageBand src (box c) 8 < gap := by
      simpa only [bandSum, hsrcGap] using hband
    exact hstages.trans_le hgapLe
  obtain ⟨j, v, Q, _hv, hQ, hFQ, hnot, hQbox⟩ :=
    LocatorEighthPowerAvoidance.exists_low_not_dvd_before_eighth_or_eighth_low
      (43762949 - wt (contactWeights 131071) F.1)
      (43762949 - 50519 - wt (contactWeights 131071) F.1)
      131071 50519 (L - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1) (71 - wt residualSWeights F.1)
      hwidth q hqinj hqNested F.1 hF
      (by simpa only [sub_two_mul, sub_three_mul, sub_four_mul, sub_five_mul,
        sub_six_mul, sub_seven_mul, sub_eight_mul] using hsource)
  have hw := nested_mem_weights hQbox hQ
  have heq : reconstruct K 43762949 131071 L 71 v.1 =
      F.1 ^ (j.val + 1) * Q := by
    rw [hprod v, ← hFQ, pow_succ]
    ring
  have hcQ : wt (contactWeights 131071) Q <
      43762949 - (j.val + 1) * 50519 -
        (j.val + 1) * wt (contactWeights 131071) F.1 := by
    simpa only [sub_two_succ_mul] using hw.2.2.2
  have htQ : wt residualTotalWeights Q ≤
      L - (j.val + 1) * wt residualTotalWeights F.1 := by
    simpa only [sub_succ_mul] using hw.1
  have hyQ : wt residualYSWeights Q ≤
      333 - (j.val + 1) * wt residualYSWeights F.1 := by
    simpa only [sub_succ_mul] using hw.2.1
  have hrQ : wt residualSWeights Q ≤
      71 - (j.val + 1) * wt residualSWeights F.1 := by
    simpa only [sub_succ_mul] using hw.2.2.1
  have hirr := (RCN167.positiveRFactors_spec H F.1 F.2).1
  fin_cases j
  · have hrel := hirr.isRelPrime_iff_not_dvd.mpr (hnot (by decide))
    have hcount := sourceC_power_count 1 (by decide) (by decide)
      L src hsrcLength hsrcY hsrcR u0 u1 H selected Gamma hdegree
      hagreement hno F c hcell v Q hQ (by simpa using heq) hcQ htQ hyQ hrQ
      hrel hgates.1
    exact hcount.trans (by simp [routeCost])
  · have hrel := hirr.isRelPrime_iff_not_dvd.mpr (hnot (by decide))
    have hcount := sourceC_power_count 2 (by decide) (by decide)
      L src hsrcLength hsrcY hsrcR u0 u1 H selected Gamma hdegree
      hagreement hno F c hcell v Q hQ (by simpa using heq) hcQ htQ hyQ hrQ
      hrel hgates.2.1
    exact hcount.trans (by simp [routeCost])
  · have hrel := hirr.isRelPrime_iff_not_dvd.mpr (hnot (by decide))
    have hcount := sourceC_power_count 3 (by decide) (by decide)
      L src hsrcLength hsrcY hsrcR u0 u1 H selected Gamma hdegree
      hagreement hno F c hcell v Q hQ (by simpa using heq) hcQ htQ hyQ hrQ
      hrel hgates.2.2.1
    exact hcount.trans (by simp [routeCost])
  · have hrel := hirr.isRelPrime_iff_not_dvd.mpr (hnot (by decide))
    have hcount := sourceC_power_count 4 (by decide) (by decide)
      L src hsrcLength hsrcY hsrcR u0 u1 H selected Gamma hdegree
      hagreement hno F c hcell v Q hQ (by simpa using heq) hcQ htQ hyQ hrQ
      hrel hgates.2.2.2.1
    exact hcount.trans (by simp [routeCost])
  · have hrel := hirr.isRelPrime_iff_not_dvd.mpr (hnot (by decide))
    have hcount := sourceC_power_count 5 (by decide) (by decide)
      L src hsrcLength hsrcY hsrcR u0 u1 H selected Gamma hdegree
      hagreement hno F c hcell v Q hQ (by simpa using heq) hcQ htQ hyQ hrQ
      hrel hgates.2.2.2.2.1
    exact hcount.trans (by simp [routeCost])
  · have hrel := hirr.isRelPrime_iff_not_dvd.mpr (hnot (by decide))
    have hcount := sourceC_power_count 6 (by decide) (by decide)
      L src hsrcLength hsrcY hsrcR u0 u1 H selected Gamma hdegree
      hagreement hno F c hcell v Q hQ (by simpa using heq) hcQ htQ hyQ hrQ
      hrel hgates.2.2.2.2.2.1
    exact hcount.trans (by simp [routeCost])
  · have hrel := hirr.isRelPrime_iff_not_dvd.mpr (hnot (by decide))
    have hcount := sourceC_power_count 7 (by decide) (by decide)
      L src hsrcLength hsrcY hsrcR u0 u1 H selected Gamma hdegree
      hagreement hno F c hcell v Q hQ (by simpa using heq) hcQ htQ hyQ hrQ
      hrel hgates.2.2.2.2.2.2.1
    exact hcount.trans (by simp [routeCost])
  · have hrel := terminal_relPrime H F c src 8 Q hQ hcell
      (htQ.trans (hTstage 8)) (hyQ.trans (hYstage 8))
      (hrQ.trans (hRstage 8)) hterminal
    have hcount := sourceC_power_count 8 (by decide) (by decide)
      L src hsrcLength hsrcY hsrcR u0 u1 H selected Gamma hdegree
      hagreement hno F c hcell v Q hQ (by simpa using heq) hcQ htQ hyQ hrQ
      hrel hgates.2.2.2.2.2.2.2
    exact hcount.trans (by simp [routeCost])

private theorem sourceC_quotient_nested
    (L : ℕ) (u0 u1 : I → K) (H : P4) (F : RegularIndex H) (hF : F.1 ≠ 0)
    (q : ConstraintKernel (K := K) 43762949 131071 L 71 241
      IRSProfile.domain u0 u1 →ₗ[K] P4) (hqinj : Function.Injective q)
    (hprod : ∀ v, reconstruct K 43762949 131071 L 71 v.1 = F.1 * q v)
    (hqbox : ∀ v, q v ∈ globalCoefficientBox K
      (43762949 - wt (contactWeights 131071) F.1) 131071
      (L - wt residualTotalWeights F.1)
      (71 - wt residualSWeights F.1)) :
    ∀ v, q v ∈ nestedCoefficientBox K
      (43762949 - wt (contactWeights 131071) F.1) 131071
      (L - wt residualTotalWeights F.1)
      (333 - wt residualYSWeights F.1)
      (71 - wt residualSWeights F.1) := by
  intro v
  have hqYS : wt residualYSWeights (q v) ≤
      333 - wt residualYSWeights F.1 := by
    by_cases hv : v = 0
    · subst v
      simp [wt, MvPolynomial.weightedTotalDegree]
    · have hqv : q v ≠ 0 := by
        intro hz
        apply hv
        apply hqinj
        simpa only [map_zero] using hz
      have hsrc : wt residualYSWeights
          (reconstruct K 43762949 131071 L 71 v.1) ≤ 333 := by
        apply flag_box_ys_bound 43762949 131071 L 71 333
          (by decide) LocatorAuxiliaryArithmetic.auxiliary176_shape
        exact reconstruct_mem_globalCoefficientBox K
          43762949 131071 L 71 v.1
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
    (L : ℕ) (u0 u1 : I → K) (H : P4) (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := K) 43762949 131071 L 71 241
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 43762949 131071 L 71 v.1) :
    ∃ q : ConstraintKernel (K := K) 43762949 131071 L 71 241
        IRSProfile.domain u0 u1 →ₗ[K] P4,
      Function.Injective q ∧
      (∀ v, reconstruct K 43762949 131071 L 71 v.1 = F.1 * q v) ∧
      (∀ v, q v ∈ nestedCoefficientBox K
        (43762949 - wt (contactWeights 131071) F.1) 131071
        (L - wt residualTotalWeights F.1)
        (333 - wt residualYSWeights F.1)
        (71 - wt residualSWeights F.1)) := by
  let recon := kernelReconstructLinear (K := K) 43762949 131071 L 71 241
    IRSProfile.domain u0 u1
  have hdivK : ∀ v : ConstraintKernel (K := K) 43762949 131071 L 71 241
      IRSProfile.domain u0 u1, F.1 ∣ recon v := by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hdiv v
  let q := quotientLinear recon F.1 hF hdivK
  have hqinj : Function.Injective q := quotientLinear_injective recon
    (kernelReconstructLinear_injective (K := K) 43762949 131071 L 71 241
      IRSProfile.domain u0 u1) F.1 hF hdivK
  have hprod (v : ConstraintKernel (K := K) 43762949 131071 L 71 241
      IRSProfile.domain u0 u1) : recon v = F.1 * q v :=
    recon_eq_mul_quotientPolynomial recon F.1 hdivK v
  have hproduct : ∀ v, reconstruct K 43762949 131071 L 71 v.1 =
      F.1 * q v := by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hprod v
  have hqbox : ∀ v : ConstraintKernel (K := K) 43762949 131071 L 71 241
      IRSProfile.domain u0 u1,
      q v ∈ globalCoefficientBox K
        (43762949 - wt (contactWeights 131071) F.1) 131071
        (L - wt residualTotalWeights F.1)
        (71 - wt residualSWeights F.1) :=
    quotient_box_of_full_divisor 43762949 131071 L 71 241
      (wt (contactWeights 131071) F.1) (wt residualTotalWeights F.1)
      (wt residualSWeights F.1) IRSProfile.domain u0 u1 F.1 hF hdivK
      le_rfl le_rfl le_rfl
  exact ⟨q, hqinj, hproduct,
    sourceC_quotient_nested L u0 u1 H F hF q hqinj hproduct hqbox⟩

private theorem sourceC_tstage (H : P4) (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (j : ℕ) :
    230000 - j * wt residualTotalWeights F.1 ≤ stageT sourceC (box c) j := by
  obtain ⟨_hr, _hylo, _hyhi, htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  change 230000 - j * wt residualTotalWeights F.1 ≤
    230000 - j * (box c).factorT
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j htlo) 230000

private theorem sourceC_ystage (H : P4) (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (j : ℕ) :
    333 - j * wt residualYSWeights F.1 ≤ stageY sourceC (box c) j := by
  obtain ⟨_hr, hylo, _hyhi, _htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  change 333 - j * wt residualYSWeights F.1 ≤ 333 - j * (box c).ylo
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j hylo) 333

private theorem sourceC_rstage (H : P4) (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (j : ℕ) :
    71 - j * wt residualSWeights F.1 ≤ stageR sourceC (box c) j := by
  obtain ⟨hr, _hylo, _hyhi, _htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  change 71 - j * wt residualSWeights F.1 ≤ 71 - j * (box c).r
  rw [hr]

private theorem sourceC_bandLe (H : P4) (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (j : ℕ) :
    50519 * channelCount
      (230000 - j * wt residualTotalWeights F.1)
      (333 - j * wt residualYSWeights F.1)
      (71 - j * wt residualSWeights F.1) ≤ stageBand sourceC (box c) j := by
  change 50519 * channelCount _ _ _ ≤ 50519 * channelCount _ _ _
  exact Nat.mul_le_mul_left 50519 (channelCount_mono
    (sourceC_tstage H F c hcell j) (sourceC_ystage H F c hcell j)
    (sourceC_rstage H F c hcell j))

private theorem sourceC_gapLe (u0 u1 : I → K) :
    96314062520372778 ≤ Module.finrank K
      (ConstraintKernel (K := K) 43762949 131071 230000 71 241
        IRSProfile.domain u0 u1) :=
  LocatorSourceCGap.finrank_lower_bound u0 u1

private theorem sourceC_width (H : P4) (F : RegularIndex H) :
    43762949 - wt (contactWeights 131071) F.1 ≤
      (43762949 - 50519 - wt (contactWeights 131071) F.1) + 50519 := by
  omega

private theorem sourceC_count_k2
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : KernelC u0 u1,
      F.1 ∣ reconstruct K 43762949 131071 230000 71 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceC 2 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 2 := by
  obtain ⟨q, hqinj, hproduct, hqNested⟩ :=
    exists_sourceC_quotient 230000 u0 u1 H F hF hdiv
  exact sourceC_count_k2_core u0 u1 H selected Gamma hdegree hagreement hno
    F hF c hcell q hqinj hproduct hqNested (sourceC_tstage H F c hcell)
    (sourceC_ystage H F c hcell) (sourceC_rstage H F c hcell)
    (sourceC_bandLe H F c hcell) (sourceC_gapLe u0 u1) (sourceC_width H F) hfit

private theorem sourceC_count_k3
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : KernelC u0 u1,
      F.1 ∣ reconstruct K 43762949 131071 230000 71 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceC 3 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 3 := by
  obtain ⟨q, hqinj, hproduct, hqNested⟩ :=
    exists_sourceC_quotient 230000 u0 u1 H F hF hdiv
  exact sourceC_count_k3_core u0 u1 H selected Gamma hdegree hagreement hno
    F hF c hcell q hqinj hproduct hqNested (sourceC_tstage H F c hcell)
    (sourceC_ystage H F c hcell) (sourceC_rstage H F c hcell)
    (sourceC_bandLe H F c hcell) (sourceC_gapLe u0 u1) (sourceC_width H F) hfit

private theorem sourceC_count_k4
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : KernelC u0 u1,
      F.1 ∣ reconstruct K 43762949 131071 230000 71 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceC 4 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 4 := by
  obtain ⟨q, hqinj, hproduct, hqNested⟩ :=
    exists_sourceC_quotient 230000 u0 u1 H F hF hdiv
  exact sourceC_count_k4_core u0 u1 H selected Gamma hdegree hagreement hno
    F hF c hcell q hqinj hproduct hqNested (sourceC_tstage H F c hcell)
    (sourceC_ystage H F c hcell) (sourceC_rstage H F c hcell)
    (sourceC_bandLe H F c hcell) (sourceC_gapLe u0 u1) (sourceC_width H F) hfit

private theorem sourceC_count_k5
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : KernelC u0 u1,
      F.1 ∣ reconstruct K 43762949 131071 230000 71 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceC 5 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 5 := by
  obtain ⟨q, hqinj, hproduct, hqNested⟩ :=
    exists_sourceC_quotient 230000 u0 u1 H F hF hdiv
  exact sourceC_count_k5_core u0 u1 H selected Gamma hdegree hagreement hno
    F hF c hcell q hqinj hproduct hqNested (sourceC_tstage H F c hcell)
    (sourceC_ystage H F c hcell) (sourceC_rstage H F c hcell)
    (sourceC_bandLe H F c hcell) (sourceC_gapLe u0 u1) (sourceC_width H F) hfit

private theorem sourceC_count_k6
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : KernelC u0 u1,
      F.1 ∣ reconstruct K 43762949 131071 230000 71 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceC 6 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 6 := by
  obtain ⟨q, hqinj, hproduct, hqNested⟩ :=
    exists_sourceC_quotient 230000 u0 u1 H F hF hdiv
  exact sourceC_count_k6_core u0 u1 H selected Gamma hdegree hagreement hno
    F hF c hcell q hqinj hproduct hqNested (sourceC_tstage H F c hcell)
    (sourceC_ystage H F c hcell) (sourceC_rstage H F c hcell)
    (sourceC_bandLe H F c hcell) (sourceC_gapLe u0 u1) (sourceC_width H F) hfit

private theorem sourceC_count_k7
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : KernelC u0 u1,
      F.1 ∣ reconstruct K 43762949 131071 230000 71 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceC 7 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 7 := by
  obtain ⟨q, hqinj, hproduct, hqNested⟩ :=
    exists_sourceC_quotient 230000 u0 u1 H F hF hdiv
  exact sourceC_count_k7_core u0 u1 H selected Gamma hdegree hagreement hno
    F hF c hcell q hqinj hproduct hqNested (sourceC_tstage H F c hcell)
    (sourceC_ystage H F c hcell) (sourceC_rstage H F c hcell)
    (sourceC_bandLe H F c hcell) (sourceC_gapLe u0 u1) (sourceC_width H F) hfit

private theorem sourceC_count_k8
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : KernelC u0 u1,
      F.1 ∣ reconstruct K 43762949 131071 230000 71 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceC 8 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) 8 := by
  obtain ⟨q, hqinj, hproduct, hqNested⟩ :=
    exists_sourceC_quotient 230000 u0 u1 H F hF hdiv
  exact sourceC_count_k8_core 230000 sourceC rfl rfl rfl
    96314062520372778 rfl u0 u1 H selected Gamma hdegree hagreement hno
    F hF c hcell q hqinj hproduct hqNested (sourceC_tstage H F c hcell)
    (sourceC_ystage H F c hcell) (sourceC_rstage H F c hcell)
    (sourceC_bandLe H F c hcell) (sourceC_gapLe u0 u1) (sourceC_width H F) hfit

private theorem sourceCLong_tstage (H : P4) (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (j : ℕ) :
    457347 - j * wt residualTotalWeights F.1 ≤ stageT sourceCLong (box c) j := by
  obtain ⟨_hr, _hylo, _hyhi, htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  change 457347 - j * wt residualTotalWeights F.1 ≤
    457347 - j * (box c).factorT
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j htlo) 457347

private theorem sourceCLong_ystage (H : P4) (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (j : ℕ) :
    333 - j * wt residualYSWeights F.1 ≤ stageY sourceCLong (box c) j := by
  obtain ⟨_hr, hylo, _hyhi, _htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  change 333 - j * wt residualYSWeights F.1 ≤ 333 - j * (box c).ylo
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j hylo) 333

private theorem sourceCLong_rstage (H : P4) (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (j : ℕ) :
    71 - j * wt residualSWeights F.1 ≤ stageR sourceCLong (box c) j := by
  obtain ⟨hr, _hylo, _hyhi, _htlo, _hthi⟩ := factor_bounds_of_cell H F c hcell
  change 71 - j * wt residualSWeights F.1 ≤ 71 - j * (box c).r
  rw [hr]

private theorem sourceCLong_bandLe (H : P4) (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (j : ℕ) :
    50519 * channelCount
      (457347 - j * wt residualTotalWeights F.1)
      (333 - j * wt residualYSWeights F.1)
      (71 - j * wt residualSWeights F.1) ≤ stageBand sourceCLong (box c) j := by
  change 50519 * channelCount _ _ _ ≤ 50519 * channelCount _ _ _
  exact Nat.mul_le_mul_left 50519 (channelCount_mono
    (sourceCLong_tstage H F c hcell j) (sourceCLong_ystage H F c hcell j)
    (sourceCLong_rstage H F c hcell j))

private theorem sourceCLong_count_k8
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : LocatorHelperFactorSwitch.LongKernel u0 u1,
      F.1 ∣ reconstruct K 43762949 131071 457347 71 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceCLong 8 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceCLong (box c) 8 := by
  obtain ⟨q, hqinj, hproduct, hqNested⟩ :=
    exists_sourceC_quotient 457347 u0 u1 H F hF hdiv
  exact sourceC_count_k8_core 457347 sourceCLong rfl rfl rfl
    191571608363612394 rfl u0 u1 H selected Gamma hdegree hagreement hno
    F hF c hcell q hqinj hproduct hqNested (sourceCLong_tstage H F c hcell)
    (sourceCLong_ystage H F c hcell) (sourceCLong_rstage H F c hcell)
    (sourceCLong_bandLe H F c hcell)
    (LocatorSourceCLongGap.finrank_lower_bound u0 u1) (sourceC_width H F) hfit

private theorem helperLong_count
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperLongC8Fits (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceCLong (box c) 8) (helperPairCost (box c)) := by
  obtain ⟨hr, _hylo, hyhi, _htlo, hthi⟩ := factor_bounds_of_cell H F c hcell
  have hFY : F.1.degreeOf 1 ≤ (box c).factorY :=
    (degreeY_le_ysWeight F.1).trans hyhi
  have hFR : F.1.degreeOf 2 ≤ (box c).r := by
    simpa only [LocatorContact.slope_weight_eq_degreeR] using hr.le
  have hFZ : F.1.degreeOf 3 ≤ (box c).thi :=
    (degreeZ_le_totalWeight F.1).trans hthi
  have hgates : LocatorHelperFactorSwitch.HelperPairGates
      (box c).factorY (box c).r (box c).thi := by
    simpa only [LocatorHelperFactorSwitch.HelperPairGates,
      LocatorHelperFactorSwitch.helperPair, HelperPairGates, helperPair, PairGates]
      using hfit.2.1
  rcases LocatorHelperFactorSwitch.long_divisor_or_helper_count
      selected Gamma hdegree hagreement hno F
      (box c).factorY (box c).r (box c).thi hFY hFR hFZ hgates with
    hdiv | hhelper
  · exact (sourceCLong_count_k8 u0 u1 H selected Gamma hdegree hagreement hno
      F hF hdiv c hcell hfit.1).trans (Nat.le_max_left _ _)
  · have hhelper' : (regularSeeds H selected Gamma F).card ≤
        helperPairCost (box c) := by
      simpa only [helperPairCost, helperPair,
        LocatorHelperFactorSwitch.helperPair] using hhelper
    exact hhelper'.trans (Nat.le_max_right _ _)

theorem regularSeeds_count_le_chosen
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181589 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80555)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdivA : ∀ v : ConstraintKernel (K := K) 11621696 131071 230000 19 64
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 11621696 131071 230000 19 v.1)
    (hdivAux : ∀ v : ConstraintKernel (K := K) 13074408 131071 230000 21 72
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 13074408 131071 230000 21 v.1)
    (hdivC : ∀ v : ConstraintKernel (K := K) 43762949 131071 230000 71 241
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 43762949 131071 230000 71 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hv : Valid c)
    (hown : (regularSeeds H selected Gamma F).card ≤
      paddedCost 131072 131073 (regularCumulativeFlag H F)) :
    (regularSeeds H selected Gamma F).card ≤ chosenCost c := by
  classical
  by_cases ho : (box c).ordinaryFits
  · have h := ordinary_count H selected Gamma F c hcell hv hown
    simpa only [chosenCost, ho, if_pos] using h
  have hroutes := (receipt c hv).resolve_left ho
  by_cases hA : RouteFits sourceA 1 (box c)
  · have h := source_one_count 11621696 19 64 88 1844712187971945 sourceA
      rfl rfl rfl rfl LocatorArithmetic.kernelA_nullity (by decide) (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivA c hcell hA
    simpa only [chosenCost, ho, hA, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hA
  by_cases hAux : RouteFits sourceAux 1 (box c)
  · have h := source_one_count 13074408 21 72 99 2587242818908418 sourceAux
      rfl rfl rfl rfl LocatorAuxiliaryArithmetic.auxiliary72_nullity
      LocatorAuxiliaryArithmetic.auxiliary72_shape
      LocatorAuxiliaryArithmetic.auxiliary72_capacity
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivAux c hcell hAux
    simpa only [chosenCost, ho, hA, hAux, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hAux
  by_cases hC2 : RouteFits sourceC 2 (box c)
  · have h := sourceC_count_k2 u0 u1 H selected Gamma hdegree
      hagreement hno F hF hdivC c hcell hC2
    simpa only [chosenCost, ho, hA, hAux, hC2, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC2
  by_cases hC3 : RouteFits sourceC 3 (box c)
  · have h := sourceC_count_k3 u0 u1 H selected Gamma hdegree
      hagreement hno F hF hdivC c hcell hC3
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC3
  by_cases hC4 : RouteFits sourceC 4 (box c)
  · have h := sourceC_count_k4 u0 u1 H selected Gamma hdegree
      hagreement hno F hF hdivC c hcell hC4
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC4
  by_cases hC5 : RouteFits sourceC 5 (box c)
  · have h := sourceC_count_k5 u0 u1 H selected Gamma hdegree
      hagreement hno F hF hdivC c hcell hC5
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC5
  by_cases hC6 : RouteFits sourceC 6 (box c)
  · have h := sourceC_count_k6 u0 u1 H selected Gamma hdegree
      hagreement hno F hF hdivC c hcell hC6
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC6
  by_cases hC7 : RouteFits sourceC 7 (box c)
  · have h := sourceC_count_k7 u0 u1 H selected Gamma hdegree
      hagreement hno F hF hdivC c hcell hC7
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6, hC7,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC7
  by_cases hC8 : RouteFits sourceC 8 (box c)
  · have h := sourceC_count_k8 u0 u1 H selected Gamma hdegree
      hagreement hno F hF hdivC c hcell hC8
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6, hC7,
      hC8, if_pos, if_false] using h
  have hhelper := hroutes.resolve_left hC8
  have h := helperLong_count u0 u1 H selected Gamma hdegree hagreement hno
    F hF c hcell hhelper
  simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6, hC7,
    hC8, if_pos, if_false] using h

end

end LocatorQuotientReplacement
