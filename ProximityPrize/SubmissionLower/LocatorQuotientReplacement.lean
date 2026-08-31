import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
import ProximityPrize.SubmissionLower.LocatorReplacementData
import ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
import ProximityPrize.SubmissionLower.LocatorSquareAvoidance
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
import ProximityPrize.SubmissionLower.BF
namespace ProximityPrize.SubmissionLower.LocatorQuotientReplacement
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN266 RCN260 LocatorFactorAggregate LocatorLowQuotient LocatorReplacementData LocatorReplacementGrid LocatorAuxiliaryArithmetic LocatorCoprimeQuotient
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

theorem degreeY_le_ysWeight (Q:P4) :Q.degreeOf (1:Fin 4) ≤ wt residualYSWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*0≤wt residualYSWeights Q at h
  omega

theorem degreeZ_le_totalWeight (Q:P4) :Q.degreeOf (3:Fin 4) ≤ wt residualTotalWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*1≤wt residualTotalWeights Q at h
  omega

theorem factor_weights_of_cell (H:P4) (F:RegularIndex H)
    (c:Cell)
    (hcell:InCell (regularCumulativeFlag H F) c) :
    wt residualSWeights F.1=r c ∧
      ylo c≤wt residualYSWeights F.1 ∧
      wt residualYSWeights F.1≤min (yhi c)
        (thi c) ∧
      tlo c≤wt residualTotalWeights F.1 ∧
      wt residualTotalWeights F.1≤thi c ∧
      131071*ylo c-r c≤
        wt (contactWeights 131071) F.1:=by
  have hc:=originalCumulativeFlag_cumulative F.1
  have hr:wt residualSWeights F.1=r c:=by
    simpa only [regularCumulativeFlag,hc.1] using hcell.all_eq
  have hylo:ylo c≤wt residualYSWeights F.1:=by
    simpa only [middle,regularCumulativeFlag,hc.2.1] using hcell.ylo_le
  have hyhi:wt residualYSWeights F.1≤yhi c:=by
    simpa only [middle,regularCumulativeFlag,hc.2.1] using hcell.middle_le_yhi
  have hyT:wt residualYSWeights F.1≤thi c:=by
    simpa only [middle,total,regularCumulativeFlag,hc.2.1,hc.2.2] using
      (middle_le_total (regularCumulativeFlag H F)).trans hcell.total_le_thi
  have htlo:tlo c≤wt residualTotalWeights F.1:=by
    simpa only [total,regularCumulativeFlag,hc.2.2] using hcell.tlo_le
  have hthi:wt residualTotalWeights F.1≤thi c:=by
    simpa only [total,regularCumulativeFlag,hc.2.2] using hcell.total_le_thi
  have hmul:=Nat.mul_le_mul_left 131071 hylo
  have hweight:=residualYS_mul_le_contact_add_slope F.1 131071 (by decide)
  rw [hr] at hweight
  exact ⟨hr,hylo,le_min hyhi hyT,htlo,hthi,by omega⟩

private theorem coefficientCount_mono_D_L_s {D D' w L L' s s':ℕ}
    (hD:D≤D') (hL:L≤L') (hs:s≤s') :
    coefficientCount D w L s≤coefficientCount D' w L' s':=by
  unfold coefficientCount
  calc
    (∑ i∈Finset.range (L+1),∑ j∈Finset.range (s+1),
      (L+1-i-j)*(D-w*i-(w-1)*j))≤
        ∑ i∈Finset.range (L+1),∑ j∈Finset.range (s+1),
          (L'+1-i-j)*(D'-w*i-(w-1)*j):=by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            gcongr
    _≤∑ i∈Finset.range (L+1),∑ j∈Finset.range (s'+1),
          (L'+1-i-j)*(D'-w*i-(w-1)*j):=by
            apply Finset.sum_le_sum
            intro i _
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (Nat.succ_le_succ hs)) (by simp)
    _≤∑ i∈Finset.range (L'+1),∑ j∈Finset.range (s'+1),
          (L'+1-i-j)*(D'-w*i-(w-1)*j):=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (Nat.succ_le_succ hL)) (by simp)

private theorem source72_count
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181746≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80398)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤51967→∀ v:ConstraintKernel (K:=K) 13085712 131071 L 21 72
      IRSProfile.domain u0 u1,F.1∣reconstruct K 13085712 131071 L 21 v.1)
    (c:Cell)
    (hcell:InCell (regularCumulativeFlag H F) c)
    (hfit:Pair72Fits c):
    (regularSeeds H selected Gamma F).card≤pair72Cost c:=by
  classical
  obtain ⟨hr,hylo,hyhi,htlo,hthi,hc⟩:=factor_weights_of_cell H F c hcell
  have hqT:length72 c-wt residualTotalWeights F.1≤
      quotient72T c:=by
    simpa only [quotient72T] using
      Nat.sub_le_sub_left htlo (length72 c)
  have hqY:99-wt residualYSWeights F.1≤quotient72YS c:=by
    simpa only [quotient72YS] using Nat.sub_le_sub_left hylo 99
  have hqS:21-wt residualSWeights F.1≤quotient72S c:=by
    simp only [quotient72S,hr]
    exact le_rfl
  have hqD:13085712-50676-wt (contactWeights 131071) F.1≤
      quotient72D c:=by
    change 13085712-50676-wt (contactWeights 131071) F.1≤
      13085712-(131071*ylo c-r c)-50676
    calc
      _≤13085712-50676-(131071*ylo c-
          r c):=Nat.sub_le_sub_left hc _
      _=_:=by omega
  have hchannels:=channelCount_mono hqT hqY hqS
  have hLmin:3106≤length72 c:=by
    simp only [length72,suggestedLength]
    split <;> omega
  have hsource:50676*channelCount
      (length72 c-wt residualTotalWeights F.1)
      (99-wt residualYSWeights F.1) (21-wt residualSWeights F.1)<
      coefficientCount 13085712 131071 (length72 c) 21-
        Fintype.card I*localRankBound 72 (length72 c) 21:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      auxiliary72_gap_affine
        (length72 c) hLmin]
    exact (Nat.mul_le_mul_left 50676 hchannels).trans_lt hfit.2.1
  obtain ⟨v,Q,_hv,hQ,_heq,hqbox,_hparent,hproduct⟩:=
    exists_fixed_quotient_with_derivative_vanishing (K:=K) (I:=I)
      13085712 131071 (length72 c) 21 72 99 50676 181746
      IRSProfile.domain u0 u1 F.1 hF
      (hdiv (length72 c) hfit.1) (by decide)
      auxiliary72_shape hsource
      auxiliary72_capacity selected Gamma hdegree hagreement
  have hbox:Q∈nestedCoefficientBox K (quotient72D c) 131071
      (quotient72T c) (quotient72YS c)
      (quotient72S c):=
    nestedCoefficientBox_mono hqD hqT hqY hqS hqbox
  have hwActual:=nested_mem_weights hqbox hQ
  have hwCell:=nested_mem_weights hbox hQ
  have hrel:IsRelPrime F.1 Q:=by
    have hirr:=(RCN167.positiveRFactors_spec H F.1 F.2).1
    rcases hfit.2.2.1 with hT|hY|hR
    · apply isRelPrime_of_weight_sub_bound residualTotalWeights
        F.1 Q hirr hQ (length72 c) hwActual.1
      dsimp [quotient72T] at hT;omega
    · apply isRelPrime_of_weight_sub_bound residualYSWeights
        F.1 Q hirr hQ 99 hwActual.2.1
      dsimp [quotient72YS] at hY;omega
    · apply isRelPrime_of_weight_sub_bound residualSWeights
        F.1 Q hirr hQ 21 hwActual.2.2.1
      dsimp [quotient72S] at hR;omega
  have hFY:F.1.degreeOf 1≤(pair72 c).leftY:=
    (degreeY_le_ysWeight F.1).trans hyhi
  have hFR:F.1.degreeOf 2≤(pair72 c).leftR:=by
    simpa only [pair72,LocatorContact.slope_weight_eq_degreeR]
      using hr.le
  have hFZ:F.1.degreeOf 3≤(pair72 c).leftZ:=
    (degreeZ_le_totalWeight F.1).trans hthi
  have hQY:Q.degreeOf 1≤(pair72 c).rightY:=
    (degreeY_le_ysWeight Q).trans hwCell.2.1
  have hQR:Q.degreeOf 2≤(pair72 c).rightR:=by
    simpa only [pair72,LocatorContact.slope_weight_eq_degreeR]
      using hwCell.2.2.1
  have hQZ:Q.degreeOf 3≤(pair72 c).rightZ:=
    (degreeZ_le_totalWeight Q).trans hwCell.1
  rcases hfit.2.2.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
    hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
  have hcount:=regularSeeds_count_le_intersection_of_product
    (pair72 c) H Q F hrel 2130706433 hFY hFR hFZ hQY hQR hQZ
    hleftR hleftYSmall hleftRSmall hleftZSmall hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by change (Finset.univ:Finset I).card=262144;rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
    (by simpa only [pair72] using (show 1≤131071 by decide))
    (by simpa only [pair72] using (show 131071<2130706433 by decide))
    (by simpa only [pair72] using (show 131071<181746 by decide))
    (by simpa only [pair72] using (show 181746≤262144 by decide))
    hdegree hagreement
    (by simpa only [pair72,UnequalParameters.errors,Nat.reduceSub] using hno)
    (fun gamma hgamma=> hproduct gamma (regularSeeds_subset H selected Gamma F hgamma))
  simpa only [pair72Cost] using hcount

private theorem source126_count
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181746≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80398)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤51967→∀ v:ConstraintKernel (K:=K) 22899996 131071 L 39 126
      IRSProfile.domain u0 u1,F.1∣reconstruct K 22899996 131071 L 39 v.1)
    (c:Cell)
    (hcell:InCell (regularCumulativeFlag H F) c)
    (hfit:Pair126Fits c):
    (regularSeeds H selected Gamma F).card≤pair126Cost c:=by
  classical
  obtain ⟨hr,hylo,hyhi,htlo,hthi,hc⟩:=factor_weights_of_cell H F c hcell
  have hqT:length126 c-wt residualTotalWeights F.1≤
      quotient126T c:=by
    simpa only [quotient126T] using
      Nat.sub_le_sub_left htlo (length126 c)
  have hqY:174-wt residualYSWeights F.1≤quotient126YS c:=by
    simpa only [quotient126YS] using Nat.sub_le_sub_left hylo 174
  have hqS:39-wt residualSWeights F.1≤quotient126S c:=by
    simp only [quotient126S,hr]
    exact le_rfl
  have hqD:22899996-50676-wt (contactWeights 131071) F.1≤
      quotient126D c:=by
    change 22899996-50676-wt (contactWeights 131071) F.1≤
      22899996-(131071*ylo c-r c)-50676
    calc
      _≤22899996-50676-(131071*ylo c-
          r c):=Nat.sub_le_sub_left hc _
      _=_:=by omega
  have hchannels:=channelCount_mono hqT hqY hqS
  have hLmin:2255≤length126 c:=by
    simp only [length126,suggestedLength]
    split <;> omega
  have hsource:50676*channelCount
      (length126 c-wt residualTotalWeights F.1)
      (174-wt residualYSWeights F.1) (39-wt residualSWeights F.1)<
      coefficientCount 22899996 131071 (length126 c) 39-
        Fintype.card I*localRankBound 126 (length126 c) 39:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      auxiliary126_gap_affine
        (length126 c) hLmin]
    exact (Nat.mul_le_mul_left 50676 hchannels).trans_lt hfit.2.1
  obtain ⟨v,Q,_hv,hQ,_heq,hqbox,_hparent,hproduct⟩:=
    exists_fixed_quotient_with_derivative_vanishing (K:=K) (I:=I)
      22899996 131071 (length126 c) 39 126 174 50676 181746
      IRSProfile.domain u0 u1 F.1 hF
      (hdiv (length126 c) hfit.1) (by decide)
      auxiliary126_shape hsource
      auxiliary126_capacity selected Gamma hdegree hagreement
  have hbox:Q∈nestedCoefficientBox K (quotient126D c) 131071
      (quotient126T c) (quotient126YS c)
      (quotient126S c):=
    nestedCoefficientBox_mono hqD hqT hqY hqS hqbox
  have hwActual:=nested_mem_weights hqbox hQ
  have hwCell:=nested_mem_weights hbox hQ
  have hrel:IsRelPrime F.1 Q:=by
    have hirr:=(RCN167.positiveRFactors_spec H F.1 F.2).1
    rcases hfit.2.2.1 with hT|hY|hR
    · apply isRelPrime_of_weight_sub_bound residualTotalWeights
        F.1 Q hirr hQ (length126 c) hwActual.1
      dsimp [quotient126T] at hT;omega
    · apply isRelPrime_of_weight_sub_bound residualYSWeights
        F.1 Q hirr hQ 174 hwActual.2.1
      dsimp [quotient126YS] at hY;omega
    · apply isRelPrime_of_weight_sub_bound residualSWeights
        F.1 Q hirr hQ 39 hwActual.2.2.1
      dsimp [quotient126S] at hR;omega
  have hFY:F.1.degreeOf 1≤(pair126 c).leftY:=
    (degreeY_le_ysWeight F.1).trans hyhi
  have hFR:F.1.degreeOf 2≤(pair126 c).leftR:=by
    simpa only [pair126,LocatorContact.slope_weight_eq_degreeR]
      using hr.le
  have hFZ:F.1.degreeOf 3≤(pair126 c).leftZ:=
    (degreeZ_le_totalWeight F.1).trans hthi
  have hQY:Q.degreeOf 1≤(pair126 c).rightY:=
    (degreeY_le_ysWeight Q).trans hwCell.2.1
  have hQR:Q.degreeOf 2≤(pair126 c).rightR:=by
    simpa only [pair126,LocatorContact.slope_weight_eq_degreeR]
      using hwCell.2.2.1
  have hQZ:Q.degreeOf 3≤(pair126 c).rightZ:=
    (degreeZ_le_totalWeight Q).trans hwCell.1
  rcases hfit.2.2.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
    hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
  have hcount:=regularSeeds_count_le_intersection_of_product
    (pair126 c) H Q F hrel 2130706433 hFY hFR hFZ hQY hQR hQZ
    hleftR hleftYSmall hleftRSmall hleftZSmall hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by change (Finset.univ:Finset I).card=262144;rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
    (by simpa only [pair126] using (show 1≤131071 by decide))
    (by simpa only [pair126] using (show 131071<2130706433 by decide))
    (by simpa only [pair126] using (show 131071<181746 by decide))
    (by simpa only [pair126] using (show 181746≤262144 by decide))
    hdegree hagreement
    (by simpa only [pair126,UnequalParameters.errors,Nat.reduceSub] using hno)
    (fun gamma hgamma=> hproduct gamma (regularSeeds_subset H selected Gamma F hgamma))
  simpa only [pair126Cost] using hcount

private theorem square72_count
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181746≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80398)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤51967→∀ v:ConstraintKernel (K:=K) 13085712 131071 L 21 72
      IRSProfile.domain u0 u1,F.1∣reconstruct K 13085712 131071 L 21 v.1)
    (c:Cell)
    (hcell:InCell (regularCumulativeFlag H F) c)
    (hfit:SquareFits c):
    (regularSeeds H selected Gamma F).card≤squareCost:=by
  classical
  obtain ⟨hr,hylo,hyhi,htlo,hthi,hc⟩:=factor_weights_of_cell H F c hcell
  obtain ⟨hrc,hyl,hyh,htl,hth,_hcost⟩:=hfit
  have hFys:wt residualYSWeights F.1=49:=by
    have hlo:=hylo
    have hhi:=hyhi.trans (Nat.min_le_left _ _)
    omega
  have hFr:wt residualSWeights F.1=10:=by omega
  have hFtlo:1415≤wt residualTotalWeights F.1:=htl.trans htlo
  have hsquare:coefficientCount
      (13085712-50676-wt (contactWeights 131071) F.1-wt (contactWeights 131071) F.1)
      131071 (27001-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
      (21-wt residualSWeights F.1-wt residualSWeights F.1)≤7448556261:=by
    rw [square72_box.symm]
    apply coefficientCount_mono_D_L_s <;> omega
  have hchannels:channelCount (27001-wt residualTotalWeights F.1)
      (99-wt residualYSWeights F.1) (21-wt residualSWeights F.1)≤
      channelCount 25586 50 11:=by
    apply channelCount_mono <;> omega
  have hsource:50676*channelCount (27001-wt residualTotalWeights F.1)
      (99-wt residualYSWeights F.1) (21-wt residualSWeights F.1)+7448556261<
      coefficientCount 13085712 131071 27001 21-
        Fintype.card I*localRankBound 72 27001 21:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      square72_nullity]
    calc
      _≤50676*channelCount 25586 50 11+7448556261:=
        Nat.add_le_add_right (Nat.mul_le_mul_left 50676 hchannels) _
      _=707204965272+7448556261:=by rw [square72_band]
      _<714654127055:=square72_strict_margin
  obtain ⟨v,Q,_hv,hQ,_heq,hqbox,_hparent,hproduct,hnot⟩:=
    LocatorSquareAvoidance.exists_fixed_quotient_with_derivative_vanishing_not_dvd
      (K:=K) (I:=I) 13085712 131071 27001 21 72 99 50676 7448556261 181746
      IRSProfile.domain u0 u1 F.1 hF (hdiv 27001 (by decide)) (by decide)
      square72_shape hsquare hsource
      auxiliary72_capacity selected Gamma hdegree hagreement
  have hwQ:=nested_mem_weights hqbox hQ
  have hrel:IsRelPrime F.1 Q:=
    (RCN167.positiveRFactors_spec H F.1 F.2).1.isRelPrime_iff_not_dvd.mpr hnot
  have hFY:F.1.degreeOf 1≤squarePair.leftY:=by
    have h:=hyhi.trans (Nat.min_le_left _ _)
    exact (degreeY_le_ysWeight F.1).trans (by
      simpa only [squarePair,hyh] using h)
  have hFR:F.1.degreeOf 2≤squarePair.leftR:=by
    simpa only [squarePair,LocatorContact.slope_weight_eq_degreeR,hrc]
      using hr.le
  have hFZ:F.1.degreeOf 3≤squarePair.leftZ:=by
    exact (degreeZ_le_totalWeight F.1).trans (by
      simpa only [squarePair] using hthi.trans hth)
  have hQYweight:wt residualYSWeights Q≤50:=by
    have h:=hwQ.2.1
    omega
  have hQY:Q.degreeOf 1≤squarePair.rightY:=by
    simpa only [squarePair] using
      (degreeY_le_ysWeight Q).trans hQYweight
  have hQRweight:wt residualSWeights Q≤11:=by
    have h:=hwQ.2.2.1
    omega
  have hQR:Q.degreeOf 2≤squarePair.rightR:=by
    simpa only [squarePair,LocatorContact.slope_weight_eq_degreeR]
      using hQRweight
  have hQZweight:wt residualTotalWeights Q≤25586:=by
    have h:=hwQ.1
    omega
  have hQZ:Q.degreeOf 3≤squarePair.rightZ:=by
    simpa only [squarePair] using
      (degreeZ_le_totalWeight Q).trans hQZweight
  have hcount:=regularSeeds_count_le_intersection_of_product
    squarePair H Q F hrel 2130706433 hFY hFR hFZ hQY hQR hQZ
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by change (Finset.univ:Finset I).card=262144;rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
    (by decide) (by decide) (by decide) (by decide) hdegree hagreement
    (by simpa only [squarePair,UnequalParameters.errors,Nat.reduceSub] using hno)
    (fun gamma hgamma=> hproduct gamma (regularSeeds_subset H selected Gamma F hgamma))
  simpa only [squareCost] using hcount

theorem regularSeeds_count_le_chosen
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181746≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80398)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv72:∀ L,L≤51967→∀ v:ConstraintKernel (K:=K) 13085712 131071 L 21 72
      IRSProfile.domain u0 u1,F.1∣reconstruct K 13085712 131071 L 21 v.1)
    (hdiv126:∀ L,L≤51967→∀ v:ConstraintKernel (K:=K) 22899996 131071 L 39 126
      IRSProfile.domain u0 u1,F.1∣reconstruct K 22899996 131071 L 39 v.1)
    (c:Cell)
    (hcell:InCell (regularCumulativeFlag H F) c)
    (hbad:LocatorFactorReplacement.Bad 2239 131072 131073 271752452545913260
      (regularCumulativeFlag H F))
    (hown:(regularSeeds H selected Gamma F).card≤
      paddedCost 131072 131073 (regularCumulativeFlag H F)):
    (regularSeeds H selected Gamma F).card≤chosenCost c:=by
  classical
  by_cases ho:OrdinaryFits c
  · simpa only [chosenCost,if_pos ho] using
      count_le_ordinaryCost (regularCumulativeFlag H F) c
        (regularSeeds H selected Gamma F).card hcell hown
  have hv:=valid_of_inCell (regularCumulativeFlag H F) c hcell
  have hnr:¬RateFits c:=by
    intro hrate
    have hrpos:1≤r c:=by
      have hp:0<r c:=by
        simpa only [hcell.all_eq] using regularCumulativeFlag_positive H F
      exact Nat.succ_le_iff.mpr hp
    have hglobal:=LocatorRateCover.global_rate_of_endpoints
      (regularCumulativeFlag H F) 2239 (yhi c)
      (r c) 271752452545913260
      hrpos hcell.all_eq hcell.middle_le_yhi
      ((yhi_le_74 c).trans (by decide))
      (hcell.total_le_thi.trans (thi_le_2239 c))
      hrate.1 hrate.2
    exact (not_lt_of_ge hglobal) hbad
  have hroutes:=((receipt c hv).resolve_left hnr).resolve_left ho
  by_cases h72:Pair72Fits c
  · have h:=source72_count u0 u1 H selected Gamma hdegree hagreement hno F hF
      hdiv72 c hcell h72
    simpa only [chosenCost,if_neg ho,if_pos h72] using h
  have hroutes':=hroutes.resolve_left h72
  by_cases h126:Pair126Fits c
  · have h:=source126_count u0 u1 H selected Gamma hdegree hagreement hno F hF
      hdiv126 c hcell h126
    simpa only [chosenCost,if_neg ho,if_neg h72,if_pos h126] using h
  have hsquare:SquareFits c:=hroutes'.resolve_left h126
  have h:=square72_count u0 u1 H selected Gamma hdegree hagreement hno F hF
    hdiv72 c hcell hsquare
  simpa only [chosenCost,if_neg ho,if_neg h72,if_neg h126] using h
end
end LocatorQuotientReplacement
