import ProximityPrize.SubmissionLower.LocatorLowQuotient
import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
import ProximityPrize.SubmissionLower.LocatorReplacementData
import ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
import ProximityPrize.SubmissionLower.BF
namespace ProximityPrize.SubmissionLower.LocatorQuotientReplacement
open ProximityPrize.Benchmark
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN266
open RCN260 LocatorFactorAggregate LocatorLowQuotient
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
theorem degreeY_le_ysWeight (Q:P4) :
    Q.degreeOf (1:Fin 4) ≤ wt residualYSWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ wt residualYSWeights Q at h
  omega
theorem degreeZ_le_totalWeight (Q:P4) :
    Q.degreeOf (3:Fin 4) ≤ wt residualTotalWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ wt residualTotalWeights Q at h
  omega
theorem factor_weights_of_cell (H:P4) (F:RegularIndex H)
    (c:LocatorReplacementGrid.Cell)
    (hcell:LocatorReplacementGrid.InCell (regularCumulativeFlag H F) c) :
    wt residualSWeights F.1 = LocatorReplacementGrid.r c ∧
      LocatorReplacementGrid.ylo c ≤ wt residualYSWeights F.1 ∧
      wt residualYSWeights F.1 ≤
        min (LocatorReplacementGrid.yhi c) (LocatorReplacementGrid.thi c) ∧
      LocatorReplacementGrid.tlo c ≤ wt residualTotalWeights F.1 ∧
      wt residualTotalWeights F.1 ≤ LocatorReplacementGrid.thi c ∧
      131071 * LocatorReplacementGrid.ylo c - LocatorReplacementGrid.r c ≤
        wt (contactWeights 131071) F.1:=by
  have hc:=originalCumulativeFlag_cumulative F.1
  have hr:wt residualSWeights F.1 = LocatorReplacementGrid.r c:=by
    simpa only [regularCumulativeFlag, hc.1] using hcell.all_eq
  have hylo:LocatorReplacementGrid.ylo c ≤ wt residualYSWeights F.1:=by
    simpa only [middle, regularCumulativeFlag, hc.2.1] using hcell.ylo_le
  have hyhi:wt residualYSWeights F.1 ≤ LocatorReplacementGrid.yhi c:=by
    simpa only [middle, regularCumulativeFlag, hc.2.1] using hcell.middle_le_yhi
  have hyT:wt residualYSWeights F.1 ≤ LocatorReplacementGrid.thi c:=by
    simpa only [middle, total, regularCumulativeFlag, hc.2.1, hc.2.2] using
      (middle_le_total (regularCumulativeFlag H F)).trans hcell.total_le_thi
  have htlo:LocatorReplacementGrid.tlo c ≤ wt residualTotalWeights F.1:=by
    simpa only [total, regularCumulativeFlag, hc.2.2] using hcell.tlo_le
  have hthi:wt residualTotalWeights F.1 ≤ LocatorReplacementGrid.thi c:=by
    simpa only [total, regularCumulativeFlag, hc.2.2] using hcell.total_le_thi
  have hmul:=Nat.mul_le_mul_left 131071 hylo
  have hweight:=residualYS_mul_le_contact_add_slope F.1 131071 (by decide)
  rw [hr] at hweight
  exact ⟨hr, hylo, le_min hyhi hyT, htlo, hthi, by omega⟩
private theorem source95_count
    (u0 u1:I → K) (H:P4) (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma, 181756 ≤
      ((Finset.univ:Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80388)
    (F:RegularIndex H) (hF:F.1 ≠ 0)
    (hdiv:∀ v:ConstraintKernel (K:=K) 17266820 131071 3200 29 95
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 17266820 131071 3200 29 v.1)
    (c:LocatorReplacementGrid.Cell)
    (hcell:LocatorReplacementGrid.InCell (regularCumulativeFlag H F) c)
    (hfit:LocatorReplacementData.Pair95Fits c) :
    (regularSeeds H selected Gamma F).card ≤ LocatorReplacementData.pair95Cost c:=by
  classical
  obtain ⟨hr, hylo, hyhi, htlo, hthi, hc⟩ :=
    factor_weights_of_cell H F c hcell
  have hqT:3200 - wt residualTotalWeights F.1 ≤
      LocatorReplacementData.quotient95T c:=by
    simpa only [LocatorReplacementData.quotient95T] using
      Nat.sub_le_sub_left htlo 3200
  have hqY:131 - wt residualYSWeights F.1 ≤
      LocatorReplacementData.quotient95YS c:=by
    simpa only [LocatorReplacementData.quotient95YS] using
      Nat.sub_le_sub_left hylo 131
  have hqS:29 - wt residualSWeights F.1 ≤
      LocatorReplacementData.quotient95S c:=by
    rw [hr]
    exact Nat.le_refl _
  have hqD:17266820 - 50686 - wt (contactWeights 131071) F.1 ≤
      LocatorReplacementData.quotient95D c:=by
    dsimp [LocatorReplacementData.quotient95D]
    omega
  have hchannels:=channelCount_mono hqT hqY hqS
  have hsource:50686 * channelCount (3200 - wt residualTotalWeights F.1)
      (131 - wt residualYSWeights F.1) (29 - wt residualSWeights F.1) <
      coefficientCount 17266820 131071 3200 29 -
        Fintype.card I * localRankBound 95 3200 29:=by
    rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
      LocatorAuxiliaryArithmetic.auxiliary95_nullity]
    exact (Nat.mul_le_mul_left 50686 hchannels).trans_lt hfit.1
  obtain ⟨v, Q, _hv, hQ, _heq, hqbox, _hparent, hproduct⟩ :=
    exists_fixed_quotient_with_derivative_vanishing (K:=K) (I:=I)
      17266820 131071 3200 29 95 131 50686 181756
      IRSProfile.domain u0 u1 F.1 hF hdiv
      (by decide) LocatorAuxiliaryArithmetic.auxiliary95_shape hsource
      LocatorAuxiliaryArithmetic.auxiliary95_capacity selected Gamma hdegree hagreement
  have hbox:Q ∈ nestedCoefficientBox K
      (LocatorReplacementData.quotient95D c) 131071
      (LocatorReplacementData.quotient95T c)
      (LocatorReplacementData.quotient95YS c)
      (LocatorReplacementData.quotient95S c) :=
    nestedCoefficientBox_mono hqD hqT hqY hqS hqbox
  have hwActual:=nested_mem_weights hqbox hQ
  have hwCell:=nested_mem_weights hbox hQ
  have hrel:IsRelPrime F.1 Q:=by
    have hirr:=(RCN167.positiveRFactors_spec H F.1 F.2).1
    rcases hfit.2.1 with hT | hY | hR
    · apply LocatorCoprimeQuotient.isRelPrime_of_weight_sub_bound
        residualTotalWeights F.1 Q hirr hQ 3200 hwActual.1
      dsimp [LocatorReplacementData.quotient95T] at hT
      omega
    · apply LocatorCoprimeQuotient.isRelPrime_of_weight_sub_bound
        residualYSWeights F.1 Q hirr hQ 131 hwActual.2.1
      dsimp [LocatorReplacementData.quotient95YS] at hY
      omega
    · apply LocatorCoprimeQuotient.isRelPrime_of_weight_sub_bound
        residualSWeights F.1 Q hirr hQ 29 hwActual.2.2.1
      dsimp [LocatorReplacementData.quotient95S] at hR
      omega
  have hFY:F.1.degreeOf 1 ≤ (LocatorReplacementData.pair95 c).leftY:=by
    exact (degreeY_le_ysWeight F.1).trans hyhi
  have hFR:F.1.degreeOf 2 ≤ (LocatorReplacementData.pair95 c).leftR:=by
    simpa only [LocatorReplacementData.pair95, LocatorContact.slope_weight_eq_degreeR]
      using hr.le
  have hFZ:F.1.degreeOf 3 ≤ (LocatorReplacementData.pair95 c).leftZ:=by
    exact (degreeZ_le_totalWeight F.1).trans hthi
  have hQY:Q.degreeOf 1 ≤ (LocatorReplacementData.pair95 c).rightY :=
    (degreeY_le_ysWeight Q).trans hwCell.2.1
  have hQR:Q.degreeOf 2 ≤ (LocatorReplacementData.pair95 c).rightR:=by
    simpa only [LocatorReplacementData.pair95, LocatorContact.slope_weight_eq_degreeR]
      using hwCell.2.2.1
  have hQZ:Q.degreeOf 3 ≤ (LocatorReplacementData.pair95 c).rightZ :=
    (degreeZ_le_totalWeight Q).trans hwCell.1
  rcases hfit.2.2.1 with
    ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
      hmixedYSmall, hmixedRSmall, hmixedZSmall⟩
  have hcount:=LocatorCoprimeQuotient.regularSeeds_count_le_intersection_of_product
    (LocatorReplacementData.pair95 c) H Q F hrel 2130706433
    hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
    (Finset.univ:Finset I) IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ:Finset I).card = 262144
      rw [Finset.card_univ]
      norm_num [I, IRSProfile.Index])
    (by
      simpa only [LocatorReplacementData.pair95] using
        (show 1 ≤ 131071 by decide))
    (by
      simpa only [LocatorReplacementData.pair95] using
        (show 131071 < 2130706433 by decide))
    (by
      simpa only [LocatorReplacementData.pair95] using
        (show 131071 < 181756 by decide))
    (by
      simpa only [LocatorReplacementData.pair95] using
        (show 181756 ≤ 262144 by decide))
    hdegree hagreement
    (by
      simpa only [LocatorReplacementData.pair95, UnequalParameters.errors,
        Nat.reduceSub] using hno)
    (fun gamma hgamma => hproduct gamma
      (regularSeeds_subset H selected Gamma F hgamma))
  simpa only [LocatorReplacementData.pair95Cost] using hcount
private theorem source72_count
    (u0 u1:I → K) (H:P4) (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma, 181756 ≤
      ((Finset.univ:Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80388)
    (F:RegularIndex H) (hF:F.1 ≠ 0)
    (hdiv:∀ v:ConstraintKernel (K:=K) 13086432 131071 24000 21 72
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 13086432 131071 24000 21 v.1)
    (c:LocatorReplacementGrid.Cell)
    (hcell:LocatorReplacementGrid.InCell (regularCumulativeFlag H F) c)
    (hfit:LocatorReplacementData.Pair72Fits c) :
    (regularSeeds H selected Gamma F).card ≤ LocatorReplacementData.pair72Cost c:=by
  classical
  obtain ⟨hr, hylo, hyhi, htlo, hthi, hc⟩ :=
    factor_weights_of_cell H F c hcell
  have hqT:24000 - wt residualTotalWeights F.1 ≤
      LocatorReplacementData.quotient72T c:=by
    simpa only [LocatorReplacementData.quotient72T] using
      Nat.sub_le_sub_left htlo 24000
  have hqY:99 - wt residualYSWeights F.1 ≤
      LocatorReplacementData.quotient72YS c:=by
    simpa only [LocatorReplacementData.quotient72YS] using
      Nat.sub_le_sub_left hylo 99
  have hqS:21 - wt residualSWeights F.1 ≤
      LocatorReplacementData.quotient72S c:=by
    rw [hr]
    exact Nat.le_refl _
  have hqD:13086432 - 50686 - wt (contactWeights 131071) F.1 ≤
      LocatorReplacementData.quotient72D c:=by
    dsimp [LocatorReplacementData.quotient72D]
    omega
  have hchannels:=channelCount_mono hqT hqY hqS
  have hsource:50686 * channelCount (24000 - wt residualTotalWeights F.1)
      (99 - wt residualYSWeights F.1) (21 - wt residualSWeights F.1) <
      coefficientCount 13086432 131071 24000 21 -
        Fintype.card I * localRankBound 72 24000 21:=by
    rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
      LocatorAuxiliaryArithmetic.auxiliary72_nullity]
    exact (Nat.mul_le_mul_left 50686 hchannels).trans_lt hfit.1
  obtain ⟨v, Q, _hv, hQ, _heq, hqbox, _hparent, hproduct⟩ :=
    exists_fixed_quotient_with_derivative_vanishing (K:=K) (I:=I)
      13086432 131071 24000 21 72 99 50686 181756
      IRSProfile.domain u0 u1 F.1 hF hdiv
      (by decide) LocatorAuxiliaryArithmetic.auxiliary72_shape hsource
      LocatorAuxiliaryArithmetic.auxiliary72_capacity selected Gamma hdegree hagreement
  have hbox:Q ∈ nestedCoefficientBox K
      (LocatorReplacementData.quotient72D c) 131071
      (LocatorReplacementData.quotient72T c)
      (LocatorReplacementData.quotient72YS c)
      (LocatorReplacementData.quotient72S c) :=
    nestedCoefficientBox_mono hqD hqT hqY hqS hqbox
  have hwActual:=nested_mem_weights hqbox hQ
  have hwCell:=nested_mem_weights hbox hQ
  have hrel:IsRelPrime F.1 Q:=by
    have hirr:=(RCN167.positiveRFactors_spec H F.1 F.2).1
    rcases hfit.2.1 with hT | hY | hR
    · apply LocatorCoprimeQuotient.isRelPrime_of_weight_sub_bound
        residualTotalWeights F.1 Q hirr hQ 24000 hwActual.1
      dsimp [LocatorReplacementData.quotient72T] at hT
      omega
    · apply LocatorCoprimeQuotient.isRelPrime_of_weight_sub_bound
        residualYSWeights F.1 Q hirr hQ 99 hwActual.2.1
      dsimp [LocatorReplacementData.quotient72YS] at hY
      omega
    · apply LocatorCoprimeQuotient.isRelPrime_of_weight_sub_bound
        residualSWeights F.1 Q hirr hQ 21 hwActual.2.2.1
      dsimp [LocatorReplacementData.quotient72S] at hR
      omega
  have hFY:F.1.degreeOf 1 ≤ (LocatorReplacementData.pair72 c).leftY:=by
    exact (degreeY_le_ysWeight F.1).trans hyhi
  have hFR:F.1.degreeOf 2 ≤ (LocatorReplacementData.pair72 c).leftR:=by
    simpa only [LocatorReplacementData.pair72, LocatorContact.slope_weight_eq_degreeR]
      using hr.le
  have hFZ:F.1.degreeOf 3 ≤ (LocatorReplacementData.pair72 c).leftZ:=by
    exact (degreeZ_le_totalWeight F.1).trans hthi
  have hQY:Q.degreeOf 1 ≤ (LocatorReplacementData.pair72 c).rightY :=
    (degreeY_le_ysWeight Q).trans hwCell.2.1
  have hQR:Q.degreeOf 2 ≤ (LocatorReplacementData.pair72 c).rightR:=by
    simpa only [LocatorReplacementData.pair72, LocatorContact.slope_weight_eq_degreeR]
      using hwCell.2.2.1
  have hQZ:Q.degreeOf 3 ≤ (LocatorReplacementData.pair72 c).rightZ :=
    (degreeZ_le_totalWeight Q).trans hwCell.1
  rcases hfit.2.2.1 with
    ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
      hmixedYSmall, hmixedRSmall, hmixedZSmall⟩
  have hcount:=LocatorCoprimeQuotient.regularSeeds_count_le_intersection_of_product
    (LocatorReplacementData.pair72 c) H Q F hrel 2130706433
    hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
    (Finset.univ:Finset I) IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ:Finset I).card = 262144
      rw [Finset.card_univ]
      norm_num [I, IRSProfile.Index])
    (by
      simpa only [LocatorReplacementData.pair72] using
        (show 1 ≤ 131071 by decide))
    (by
      simpa only [LocatorReplacementData.pair72] using
        (show 131071 < 2130706433 by decide))
    (by
      simpa only [LocatorReplacementData.pair72] using
        (show 131071 < 181756 by decide))
    (by
      simpa only [LocatorReplacementData.pair72] using
        (show 181756 ≤ 262144 by decide))
    hdegree hagreement
    (by
      simpa only [LocatorReplacementData.pair72, UnequalParameters.errors,
        Nat.reduceSub] using hno)
    (fun gamma hgamma => hproduct gamma
      (regularSeeds_subset H selected Gamma F hgamma))
  simpa only [LocatorReplacementData.pair72Cost] using hcount
private theorem source126_count
    (u0 u1:I → K) (H:P4) (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma, 181756 ≤
      ((Finset.univ:Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80388)
    (F:RegularIndex H) (hF:F.1 ≠ 0)
    (hdiv:∀ v:ConstraintKernel (K:=K) 22901256 131071 2814 39 126
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 22901256 131071 2814 39 v.1)
    (c:LocatorReplacementGrid.Cell)
    (hcell:LocatorReplacementGrid.InCell (regularCumulativeFlag H F) c)
    (hfit:LocatorReplacementData.Pair126Fits c) :
    (regularSeeds H selected Gamma F).card ≤
      LocatorReplacementData.pair126Cost c:=by
  classical
  obtain ⟨hr, hylo, hyhi, htlo, hthi, hc⟩ :=
    factor_weights_of_cell H F c hcell
  have hqT:2814 - wt residualTotalWeights F.1 ≤
      LocatorReplacementData.quotient126T c:=by
    simpa only [LocatorReplacementData.quotient126T] using
      Nat.sub_le_sub_left htlo 2814
  have hqY:174 - wt residualYSWeights F.1 ≤
      LocatorReplacementData.quotient126YS c:=by
    simpa only [LocatorReplacementData.quotient126YS] using
      Nat.sub_le_sub_left hylo 174
  have hqS:39 - wt residualSWeights F.1 ≤
      LocatorReplacementData.quotient126S c:=by
    rw [hr]
    exact Nat.le_refl _
  have hqD:22901256 - 50686 - wt (contactWeights 131071) F.1 ≤
      LocatorReplacementData.quotient126D c:=by
    dsimp [LocatorReplacementData.quotient126D]
    omega
  have hchannels:=channelCount_mono hqT hqY hqS
  have hsource:50686 * channelCount (2814 - wt residualTotalWeights F.1)
      (174 - wt residualYSWeights F.1) (39 - wt residualSWeights F.1) <
      coefficientCount 22901256 131071 2814 39 -
        Fintype.card I * localRankBound 126 2814 39:=by
    rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
      LocatorAuxiliaryArithmetic.auxiliary126_nullity]
    exact (Nat.mul_le_mul_left 50686 hchannels).trans_lt hfit.1
  obtain ⟨v, Q, _hv, hQ, _heq, hqbox, _hparent, hproduct⟩ :=
    exists_fixed_quotient_with_derivative_vanishing (K:=K) (I:=I)
      22901256 131071 2814 39 126 174 50686 181756
      IRSProfile.domain u0 u1 F.1 hF hdiv
      (by decide) LocatorAuxiliaryArithmetic.auxiliary126_shape hsource
      LocatorAuxiliaryArithmetic.auxiliary126_capacity selected Gamma hdegree hagreement
  have hbox:Q ∈ nestedCoefficientBox K
      (LocatorReplacementData.quotient126D c) 131071
      (LocatorReplacementData.quotient126T c)
      (LocatorReplacementData.quotient126YS c)
      (LocatorReplacementData.quotient126S c) :=
    nestedCoefficientBox_mono hqD hqT hqY hqS hqbox
  have hwActual:=nested_mem_weights hqbox hQ
  have hwCell:=nested_mem_weights hbox hQ
  have hrel:IsRelPrime F.1 Q:=by
    have hirr:=(RCN167.positiveRFactors_spec H F.1 F.2).1
    rcases hfit.2.1 with hT | hY | hR
    · apply LocatorCoprimeQuotient.isRelPrime_of_weight_sub_bound
        residualTotalWeights F.1 Q hirr hQ 2814 hwActual.1
      dsimp [LocatorReplacementData.quotient126T] at hT
      omega
    · apply LocatorCoprimeQuotient.isRelPrime_of_weight_sub_bound
        residualYSWeights F.1 Q hirr hQ 174 hwActual.2.1
      dsimp [LocatorReplacementData.quotient126YS] at hY
      omega
    · apply LocatorCoprimeQuotient.isRelPrime_of_weight_sub_bound
        residualSWeights F.1 Q hirr hQ 39 hwActual.2.2.1
      dsimp [LocatorReplacementData.quotient126S] at hR
      omega
  have hFY:F.1.degreeOf 1 ≤ (LocatorReplacementData.pair126 c).leftY:=by
    exact (degreeY_le_ysWeight F.1).trans hyhi
  have hFR:F.1.degreeOf 2 ≤ (LocatorReplacementData.pair126 c).leftR:=by
    simpa only [LocatorReplacementData.pair126, LocatorContact.slope_weight_eq_degreeR]
      using hr.le
  have hFZ:F.1.degreeOf 3 ≤ (LocatorReplacementData.pair126 c).leftZ:=by
    exact (degreeZ_le_totalWeight F.1).trans hthi
  have hQY:Q.degreeOf 1 ≤ (LocatorReplacementData.pair126 c).rightY :=
    (degreeY_le_ysWeight Q).trans hwCell.2.1
  have hQR:Q.degreeOf 2 ≤ (LocatorReplacementData.pair126 c).rightR:=by
    simpa only [LocatorReplacementData.pair126, LocatorContact.slope_weight_eq_degreeR]
      using hwCell.2.2.1
  have hQZ:Q.degreeOf 3 ≤ (LocatorReplacementData.pair126 c).rightZ :=
    (degreeZ_le_totalWeight Q).trans hwCell.1
  rcases hfit.2.2.1 with
    ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
      hmixedYSmall, hmixedRSmall, hmixedZSmall⟩
  have hcount:=LocatorCoprimeQuotient.regularSeeds_count_le_intersection_of_product
    (LocatorReplacementData.pair126 c) H Q F hrel 2130706433
    hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
    (Finset.univ:Finset I) IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ:Finset I).card = 262144
      rw [Finset.card_univ]
      norm_num [I, IRSProfile.Index])
    (by
      simpa only [LocatorReplacementData.pair126] using
        (show 1 ≤ 131071 by decide))
    (by
      simpa only [LocatorReplacementData.pair126] using
        (show 131071 < 2130706433 by decide))
    (by
      simpa only [LocatorReplacementData.pair126] using
        (show 131071 < 181756 by decide))
    (by
      simpa only [LocatorReplacementData.pair126] using
        (show 181756 ≤ 262144 by decide))
    hdegree hagreement
    (by
      simpa only [LocatorReplacementData.pair126, UnequalParameters.errors,
        Nat.reduceSub] using hno)
    (fun gamma hgamma => hproduct gamma
      (regularSeeds_subset H selected Gamma F hgamma))
  simpa only [LocatorReplacementData.pair126Cost] using hcount
theorem regularSeeds_count_le_chosen
    (u0 u1:I → K) (H:P4) (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma, 181756 ≤
      ((Finset.univ:Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80388)
    (F:RegularIndex H) (hF:F.1 ≠ 0)
    (hdiv95:∀ v:ConstraintKernel (K:=K) 17266820 131071 3200 29 95
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 17266820 131071 3200 29 v.1)
    (hdiv72:∀ v:ConstraintKernel (K:=K) 13086432 131071 24000 21 72
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 13086432 131071 24000 21 v.1)
    (hdiv126:∀ v:ConstraintKernel (K:=K) 22901256 131071 2814 39 126
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 22901256 131071 2814 39 v.1)
    (c:LocatorReplacementGrid.Cell)
    (hcell:LocatorReplacementGrid.InCell (regularCumulativeFlag H F) c)
    (hspecial:¬ LocatorReplacementData.Special c)
    (hbad:LocatorFactorReplacement.Bad 2184 131072 131073
      271423674026155232 (regularCumulativeFlag H F))
    (hown:(regularSeeds H selected Gamma F).card ≤
      paddedCost 131072 131073 (regularCumulativeFlag H F)) :
    (regularSeeds H selected Gamma F).card ≤ LocatorReplacementData.chosenCost c:=by
  classical
  by_cases ho:LocatorReplacementData.OrdinaryFits c
  · simpa only [LocatorReplacementData.chosenCost, if_pos ho] using
      LocatorReplacementGrid.count_le_ordinaryCost (regularCumulativeFlag H F) c
        (regularSeeds H selected Gamma F).card hcell hown
  have hv:=LocatorReplacementGrid.valid_of_inCell
    (regularCumulativeFlag H F) c hcell
  have hnr:¬ LocatorReplacementData.RateFits c:=by
    intro hrate
    have hglobal:=LocatorRateCover.global_rate_of_endpoints
      (regularCumulativeFlag H F) 2184 (LocatorReplacementGrid.yhi c)
      (LocatorReplacementGrid.r c) 271423674026155232
      (by dsimp [LocatorReplacementGrid.r]; omega)
      hcell.all_eq hcell.middle_le_yhi
      (by dsimp [LocatorReplacementGrid.yhi]; omega)
      (hcell.total_le_thi.trans (Nat.min_le_left _ _)) hrate.1 hrate.2
    exact (not_lt_of_ge hglobal) hbad
  have hpairs:=((LocatorReplacementData.receipt c hv).resolve_left hnr).resolve_left ho
  by_cases h95:LocatorReplacementData.Pair95Fits c
  · have h:=source95_count u0 u1 H selected Gamma hdegree hagreement hno
      F hF hdiv95 c hcell h95
    simpa only [LocatorReplacementData.chosenCost, if_neg ho, if_pos h95] using h
  · have hpairs':=hpairs.resolve_left h95
    by_cases h72:LocatorReplacementData.Pair72Fits c
    · have h:=source72_count u0 u1 H selected Gamma hdegree hagreement hno
        F hF hdiv72 c hcell h72
      simpa only [LocatorReplacementData.chosenCost, if_neg ho, if_neg h95,
        if_pos h72] using h
    · have h126:LocatorReplacementData.Pair126Fits c :=
        ((hpairs'.resolve_left h72).resolve_right hspecial)
      have h:=source126_count u0 u1 H selected Gamma hdegree hagreement hno
        F hF hdiv126 c hcell h126
      simpa only [LocatorReplacementData.chosenCost, if_neg ho, if_neg h95,
        if_neg h72] using h
end
end ProximityPrize.SubmissionLower.LocatorQuotientReplacement
