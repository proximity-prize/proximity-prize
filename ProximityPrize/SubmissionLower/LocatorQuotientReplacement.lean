import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
import ProximityPrize.SubmissionLower.LocatorReplacementData
import ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
import ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance
import ProximityPrize.SubmissionLower.LocatorTripleSquareAvoidance
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
    (hagreement:∀ gamma∈Gamma,181717≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80427)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤52091→∀ v:ConstraintKernel (K:=K) 13083624 131071 L 21 72
      IRSProfile.domain u0 u1,F.1∣reconstruct K 13083624 131071 L 21 v.1)
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
  have hqD:13083624-50647-wt (contactWeights 131071) F.1≤
      quotient72D c:=by
    change 13083624-50647-wt (contactWeights 131071) F.1≤
      13083624-(131071*ylo c-r c)-50647
    calc
      _≤13083624-50647-(131071*ylo c-
          r c):=Nat.sub_le_sub_left hc _
      _=_:=by omega
  have hchannels:=channelCount_mono hqT hqY hqS
  have hLmin:3592≤length72 c:=by
    simp only [length72,suggestedLength]
    split <;> omega
  have hsource:50647*channelCount
      (length72 c-wt residualTotalWeights F.1)
      (99-wt residualYSWeights F.1) (21-wt residualSWeights F.1)<
      coefficientCount 13083624 131071 (length72 c) 21-
        Fintype.card I*localRankBound 72 (length72 c) 21:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      auxiliary72_gap_affine
        (length72 c) hLmin]
    exact (Nat.mul_le_mul_left 50647 hchannels).trans_lt hfit.2.1
  obtain ⟨v,Q,_hv,hQ,_heq,hqbox,_hparent,hproduct⟩:=
    exists_fixed_quotient_with_derivative_vanishing (K:=K) (I:=I)
      13083624 131071 (length72 c) 21 72 99 50647 181717
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
    (by simpa only [pair72] using (show 131071<181717 by decide))
    (by simpa only [pair72] using (show 181717≤262144 by decide))
    hdegree hagreement
    (by simpa only [pair72,UnequalParameters.errors,Nat.reduceSub] using hno)
    (fun gamma hgamma=> hproduct gamma (regularSeeds_subset H selected Gamma F hgamma))
  simpa only [pair72Cost] using hcount

private theorem source126_count
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181717≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80427)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤52091→∀ v:ConstraintKernel (K:=K) 22896342 131071 L 39 126
      IRSProfile.domain u0 u1,F.1∣reconstruct K 22896342 131071 L 39 v.1)
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
  have hqD:22896342-50647-wt (contactWeights 131071) F.1≤
      quotient126D c:=by
    change 22896342-50647-wt (contactWeights 131071) F.1≤
      22896342-(131071*ylo c-r c)-50647
    calc
      _≤22896342-50647-(131071*ylo c-
          r c):=Nat.sub_le_sub_left hc _
      _=_:=by omega
  have hchannels:=channelCount_mono hqT hqY hqS
  have hLmin:2387≤length126 c:=by
    simp only [length126,suggestedLength]
    split <;> omega
  have hsource:50647*channelCount
      (length126 c-wt residualTotalWeights F.1)
      (174-wt residualYSWeights F.1) (39-wt residualSWeights F.1)<
      coefficientCount 22896342 131071 (length126 c) 39-
        Fintype.card I*localRankBound 126 (length126 c) 39:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      auxiliary126_gap_affine
        (length126 c) hLmin]
    exact (Nat.mul_le_mul_left 50647 hchannels).trans_lt hfit.2.1
  obtain ⟨v,Q,_hv,hQ,_heq,hqbox,_hparent,hproduct⟩:=
    exists_fixed_quotient_with_derivative_vanishing (K:=K) (I:=I)
      22896342 131071 (length126 c) 39 126 174 50647 181717
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
    (by simpa only [pair126] using (show 131071<181717 by decide))
    (by simpa only [pair126] using (show 181717≤262144 by decide))
    hdegree hagreement
    (by simpa only [pair126,UnequalParameters.errors,Nat.reduceSub] using hno)
    (fun gamma hgamma=> hproduct gamma (regularSeeds_subset H selected Gamma F hgamma))
  simpa only [pair126Cost] using hcount

private theorem double126_count
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181717≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80427)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤52091→∀ v:ConstraintKernel (K:=K) 22896342 131071 L 39 126
      IRSProfile.domain u0 u1,F.1∣reconstruct K 22896342 131071 L 39 v.1)
    (c:Cell)
    (hcell:InCell (regularCumulativeFlag H F) c)
    (hfit:Double126Fits c):
    (regularSeeds H selected Gamma F).card≤doubleCost c:=by
  classical
  obtain ⟨hr,hylo,hyhi,htlo,hthi,hc⟩:=factor_weights_of_cell H F c hcell
  have hqT:lengthDouble126 c-wt residualTotalWeights F.1≤quotientDoubleT c:=by
    simpa only [quotientDoubleT] using
      Nat.sub_le_sub_left htlo (lengthDouble126 c)
  have hqY:174-wt residualYSWeights F.1≤quotientDoubleYS c:=by
    simpa only [quotientDoubleYS] using Nat.sub_le_sub_left hylo 174
  have hqS:39-wt residualSWeights F.1≤quotientDoubleS c:=by
    simpa only [quotientDoubleS,hr] using Nat.le_refl (39-r c)
  have hhT:lengthDouble126 c-wt residualTotalWeights F.1-
      wt residualTotalWeights F.1≤secondDoubleT c:=by
    dsimp [secondDoubleT]
    omega
  have hhY:174-wt residualYSWeights F.1-wt residualYSWeights F.1≤
      secondDoubleYS c:=by
    dsimp [secondDoubleYS]
    omega
  have hhS:39-wt residualSWeights F.1-wt residualSWeights F.1≤
      secondDoubleS c:=by
    simp only [secondDoubleS,hr]
    omega
  let recon:=kernelReconstructLinear (K:=K) 22896342 131071
    (lengthDouble126 c) 39 126 IRSProfile.domain u0 u1
  have hdivK:∀ v:ConstraintKernel (K:=K) 22896342 131071
      (lengthDouble126 c) 39 126 IRSProfile.domain u0 u1,F.1∣recon v:=by
    intro v
    simpa only [recon,kernelReconstructLinear_apply] using
      hdiv (lengthDouble126 c) hfit.2.1 v
  let q:=quotientLinear recon F.1 hF hdivK
  have hqinj:Function.Injective q:=
    quotientLinear_injective recon
      (kernelReconstructLinear_injective (K:=K) 22896342 131071
        (lengthDouble126 c) 39 126 IRSProfile.domain u0 u1)
      F.1 hF hdivK
  have hprod (v:ConstraintKernel (K:=K) 22896342 131071
      (lengthDouble126 c) 39 126 IRSProfile.domain u0 u1):
      recon v=F.1*q v:=recon_eq_mul_quotientPolynomial recon F.1 hdivK v
  have hqbox:∀ v:ConstraintKernel (K:=K) 22896342 131071
      (lengthDouble126 c) 39 126 IRSProfile.domain u0 u1,
      q v∈globalCoefficientBox K
        (22896342-wt (contactWeights 131071) F.1) 131071
        (lengthDouble126 c-wt residualTotalWeights F.1)
        (39-wt residualSWeights F.1):=
    quotient_box_of_full_divisor 22896342 131071 (lengthDouble126 c) 39 126
      (wt (contactWeights 131071) F.1) (wt residualTotalWeights F.1)
      (wt residualSWeights F.1) IRSProfile.domain u0 u1 F.1 hF hdivK
      le_rfl le_rfl le_rfl
  have hqYS (v:ConstraintKernel (K:=K) 22896342 131071
      (lengthDouble126 c) 39 126 IRSProfile.domain u0 u1):
      wt residualYSWeights (q v)≤174-wt residualYSWeights F.1:=by
    by_cases hv:v=0
    · subst v
      simp [wt,MvPolynomial.weightedTotalDegree]
    · have hqv:q v≠0:=by
        intro hz
        apply hv
        apply hqinj
        simpa only [map_zero] using hz
      have hsrc:wt residualYSWeights (recon v)≤174:=by
        apply flag_box_ys_bound 22896342 131071 (lengthDouble126 c) 39 174
          (by decide) auxiliary126_shape
        change reconstruct K 22896342 131071 (lengthDouble126 c) 39 v.1∈
          globalCoefficientBox K 22896342 131071 (lengthDouble126 c) 39
        exact reconstruct_mem_globalCoefficientBox K 22896342 131071
          (lengthDouble126 c) 39 v.1
      have hmul:=weightedTotalDegree_mul residualYSWeights F.1 (q v) hF hqv
      rw [← hprod v] at hmul
      simp only [wt] at hsrc ⊢
      omega
  have hqNested:∀ v:ConstraintKernel (K:=K) 22896342 131071
      (lengthDouble126 c) 39 126 IRSProfile.domain u0 u1,
      q v∈nestedCoefficientBox K
        (22896342-wt (contactWeights 131071) F.1) 131071
        (lengthDouble126 c-wt residualTotalWeights F.1)
        (174-wt residualYSWeights F.1) (39-wt residualSWeights F.1):=by
    intro v d hd
    have hb:=hqbox v hd
    have hy:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans (hqYS v)
    rw [weight_fin4] at hy
    simp only [residualYSWeights] at hy
    refine ⟨hb.1,?_,hb.2.1,hb.2.2⟩
    simpa [residualYSWeights] using hy
  have hchannelsFirst:=channelCount_mono hqT hqY hqS
  have hchannelsSecond:=channelCount_mono hhT hhY hhS
  have hsourceCoeff:50647*channelCount
      (lengthDouble126 c-wt residualTotalWeights F.1)
      (174-wt residualYSWeights F.1) (39-wt residualSWeights F.1)+
      50647*channelCount
        (lengthDouble126 c-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
        (174-wt residualYSWeights F.1-wt residualYSWeights F.1)
        (39-wt residualSWeights F.1-wt residualSWeights F.1)<
      coefficientCount 22896342 131071 (lengthDouble126 c) 39-
        Fintype.card I*localRankBound 126 (lengthDouble126 c) 39:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      auxiliary126_gap_affine (lengthDouble126 c) hfit.1]
    exact (Nat.add_le_add (Nat.mul_le_mul_left 50647 hchannelsFirst)
      (Nat.mul_le_mul_left 50647 hchannelsSecond)).trans_lt
        (by simpa only [bandDoubleFirst,bandDoubleSecond,sourceGapDouble126]
          using hfit.2.2.2.1)
  have hsource:=hsourceCoeff.trans_le
    (constraintKernel_finrank_lower_bound 22896342 131071
      (lengthDouble126 c) 39 126 IRSProfile.domain u0 u1)
  have hwidth:22896342-wt (contactWeights 131071) F.1≤
      (22896342-50647-wt (contactWeights 131071) F.1)+50647:=by omega
  rcases LocatorDoubleSquareAvoidance.exists_first_low_not_dvd_or_second_low
      (22896342-wt (contactWeights 131071) F.1)
      (22896342-50647-wt (contactWeights 131071) F.1)
      131071 50647
      (lengthDouble126 c-wt residualTotalWeights F.1)
      (174-wt residualYSWeights F.1) (39-wt residualSWeights F.1)
      hwidth q hqinj hqNested F.1 hF hsource with hfirst|hsecond
  · obtain ⟨v,hv,hQ,hQbox,hnot⟩:=hfirst
    have heq:F.1*q v=reconstruct K 22896342 131071
        (lengthDouble126 c) 39 v.1:=by
      simpa only [recon,kernelReconstructLinear_apply] using (hprod v).symm
    have hlow:reconstruct K 22896342 131071 (lengthDouble126 c) 39 v.1∈
        globalCoefficientBox K (22896342-50647) 131071
          (lengthDouble126 c) 39:=by
      rw [← heq]
      have hsourceBox:F.1*q v∈globalCoefficientBox K 22896342 131071
          (lengthDouble126 c) 39:=by
        rw [heq]
        exact reconstruct_mem_globalCoefficientBox K 22896342 131071
          (lengthDouble126 c) 39 v.1
      have hsrc:=(mem_flagGlobalCoefficientBox_iff (F.1*q v) 22896342
        131071 (lengthDouble126 c) 39 (by decide)).mp hsourceBox
      have hqc:=(nested_mem_weights hQbox hQ).2.2.2
      have hmul:=weightedTotalDegree_mul (contactWeights 131071) F.1 (q v) hF hQ
      apply (mem_flagGlobalCoefficientBox_iff (F.1*q v) (22896342-50647)
        131071 (lengthDouble126 c) 39 (by decide)).mpr
      refine ⟨hsrc.1,hsrc.2.1,?_⟩
      simp only [wt] at hqc ⊢
      omega
    have hrel:IsRelPrime F.1 (q v):=
      (RCN167.positiveRFactors_spec H F.1 F.2).1.isRelPrime_iff_not_dvd.mpr hnot
    have hwQ:=nested_mem_weights hQbox hQ
    have hFY:F.1.degreeOf 1≤(pairDoubleFirst c).leftY:=
      (degreeY_le_ysWeight F.1).trans hyhi
    have hFR:F.1.degreeOf 2≤(pairDoubleFirst c).leftR:=by
      simpa only [pairDoubleFirst,LocatorContact.slope_weight_eq_degreeR]
        using hr.le
    have hFZ:F.1.degreeOf 3≤(pairDoubleFirst c).leftZ:=
      (degreeZ_le_totalWeight F.1).trans hthi
    have hQY:(q v).degreeOf 1≤(pairDoubleFirst c).rightY:=by
      simpa only [pairDoubleFirst] using (degreeY_le_ysWeight (q v)).trans
        (hwQ.2.1.trans hqY)
    have hQR:(q v).degreeOf 2≤(pairDoubleFirst c).rightR:=by
      simpa only [pairDoubleFirst,LocatorContact.slope_weight_eq_degreeR]
        using hwQ.2.2.1.trans hqS
    have hQZ:(q v).degreeOf 3≤(pairDoubleFirst c).rightZ:=by
      simpa only [pairDoubleFirst] using (degreeZ_le_totalWeight (q v)).trans
        (hwQ.1.trans hqT)
    rcases hfit.2.2.2.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
      hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hproduct:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2:Fin 4) (F.1*q v))=0:=by
      intro gamma hgamma
      have hgammaG:gamma∈Gamma:=(Finset.mem_filter.mp hgamma).1
      let support:=(Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)
      have hcard:181717≤support.card:=hagreement gamma hgammaG
      have hcap:22896342-50647≤(126-1)*support.card+(131071-1):=
        auxiliary126_capacity.trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left (126-1) hcard) _)
      have hvalues:∀ i∈support,(selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i:=by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      rw [heq]
      exact specialization_pderiv_R_eq_zero_of_kernel_low_box
        22896342 (22896342-50647) 131071 (lengthDouble126 c) 39 126
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hgammaG) hcap hvalues
    have hcount:=regularSeeds_count_le_intersection_of_product
      (pairDoubleFirst c) H (q v) F hrel 2130706433
      hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
      (by change (Finset.univ:Finset I).card=262144
          rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
      (by simpa only [pairDoubleFirst] using (show 1≤131071 by decide))
      (by simpa only [pairDoubleFirst] using (show 131071<2130706433 by decide))
      (by simpa only [pairDoubleFirst] using (show 131071<181717 by decide))
      (by simpa only [pairDoubleFirst] using (show 181717≤262144 by decide))
      hdegree hagreement
      (by simpa only [pairDoubleFirst,UnequalParameters.errors,Nat.reduceSub] using hno)
      hproduct
    exact hcount.trans (by simp only [doubleCost];exact Nat.le_max_left _ _)
  · obtain ⟨v,Q,hv,hQ,hFQ,hQbox⟩:=hsecond
    have heq:reconstruct K 22896342 131071 (lengthDouble126 c) 39 v.1=
        F.1*(F.1*Q):=by
      calc
        _=recon v:=by rfl
        _=F.1*q v:=hprod v
        _=F.1*(F.1*Q):=congrArg (fun W=>F.1*W) hFQ.symm
    have hwQ:=nested_mem_weights hQbox hQ
    have hrel:IsRelPrime F.1 Q:=by
      apply isRelPrime_of_weight_lt residualTotalWeights F.1 Q
        (RCN167.positiveRFactors_spec H F.1 F.2).1 hQ
      have h:=hwQ.1
      have hlen3:lengthDouble126 c<3*tlo c:=hfit.2.2.1
      omega
    have hlow:reconstruct K 22896342 131071 (lengthDouble126 c) 39 v.1∈
        globalCoefficientBox K (22896342-2*50647) 131071
          (lengthDouble126 c) 39:=by
      rw [heq]
      have hsourceBox:F.1*(F.1*Q)∈globalCoefficientBox K 22896342 131071
          (lengthDouble126 c) 39:=by
        rw [← heq]
        exact reconstruct_mem_globalCoefficientBox K 22896342 131071
          (lengthDouble126 c) 39 v.1
      have hsrc:=(mem_flagGlobalCoefficientBox_iff (F.1*(F.1*Q)) 22896342
        131071 (lengthDouble126 c) 39 (by decide)).mp hsourceBox
      have hqc:=hwQ.2.2.2
      have hmulInner:=weightedTotalDegree_mul (contactWeights 131071) F.1 Q hF hQ
      have hmulOuter:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*Q) hF (mul_ne_zero hF hQ)
      apply (mem_flagGlobalCoefficientBox_iff (F.1*(F.1*Q))
        (22896342-2*50647) 131071 (lengthDouble126 c) 39 (by decide)).mpr
      refine ⟨hsrc.1,hsrc.2.1,?_⟩
      simp only [wt] at hqc ⊢
      omega
    have hFY:F.1.degreeOf 1≤(pairDoubleSecond c).leftY:=
      (degreeY_le_ysWeight F.1).trans hyhi
    have hFR:F.1.degreeOf 2≤(pairDoubleSecond c).leftR:=by
      simpa only [pairDoubleSecond,LocatorContact.slope_weight_eq_degreeR]
        using hr.le
    have hFZ:F.1.degreeOf 3≤(pairDoubleSecond c).leftZ:=
      (degreeZ_le_totalWeight F.1).trans hthi
    have hQY:Q.degreeOf 1≤(pairDoubleSecond c).rightY:=by
      simpa only [pairDoubleSecond] using (degreeY_le_ysWeight Q).trans
        (hwQ.2.1.trans hhY)
    have hQR:Q.degreeOf 2≤(pairDoubleSecond c).rightR:=by
      simpa only [pairDoubleSecond,LocatorContact.slope_weight_eq_degreeR]
        using hwQ.2.2.1.trans hhS
    have hQZ:Q.degreeOf 3≤(pairDoubleSecond c).rightZ:=by
      simpa only [pairDoubleSecond] using (degreeZ_le_totalWeight Q).trans
        (hwQ.1.trans hhT)
    rcases hfit.2.2.2.2.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
      hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have htwo:(2:K)≠0:=by
      intro hz
      have hdvd:2130706433∣2:=(CharP.cast_eq_zero_iff K 2130706433 2).mp hz
      norm_num at hdvd
    have hproduct:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2:Fin 4)
            (MvPolynomial.pderiv (2:Fin 4) (F.1*(F.1*Q))))=0:=by
      intro gamma hgamma
      have hgammaG:gamma∈Gamma:=(Finset.mem_filter.mp hgamma).1
      let support:=(Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)
      have hcard:181717≤support.card:=hagreement gamma hgammaG
      have hcap:22896342-2*50647≤(126-2)*support.card+2*(131071-1):=
        auxiliary126_double_capacity.trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left (126-2) hcard) _)
      have hvalues:∀ i∈support,(selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i:=by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      rw [← heq]
      exact LocatorDoubleSquareAvoidance.specialization_pderiv_R2_eq_zero_of_kernel_low_box
        22896342 (22896342-2*50647) 131071 (lengthDouble126 c) 39 126
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hgammaG) hcap hvalues
    have hQzero:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q=0:=by
      intro gamma hgamma
      obtain ⟨hFzero,hregular⟩:=(Finset.mem_filter.mp hgamma).2
      exact LocatorDoubleSquareAvoidance.specialization_eq_zero_of_pderiv_R2_square_product
        (selected gamma) gamma F.1 Q htwo hFzero hregular
          (hproduct gamma hgamma)
    have hcount:=regularSeeds_count_le_intersection
      (pairDoubleSecond c) H Q F hrel 2130706433
      hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
      (by change (Finset.univ:Finset I).card=262144
          rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
      (by simpa only [pairDoubleSecond] using (show 1≤131071 by decide))
      (by simpa only [pairDoubleSecond] using (show 131071<2130706433 by decide))
      (by simpa only [pairDoubleSecond] using (show 131071<181717 by decide))
      (by simpa only [pairDoubleSecond] using (show 181717≤262144 by decide))
      hdegree hagreement
      (by simpa only [pairDoubleSecond,UnequalParameters.errors,Nat.reduceSub] using hno)
      hQzero
    exact hcount.trans (by simp only [doubleCost];exact Nat.le_max_right _ _)

private theorem triple126_count
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181717≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80427)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤52091→∀ v:ConstraintKernel (K:=K) 22896342 131071 L 39 126
      IRSProfile.domain u0 u1,F.1∣reconstruct K 22896342 131071 L 39 v.1)
    (c:Cell)
    (hcell:InCell (regularCumulativeFlag H F) c)
    (hfit:Triple126Fits c):
    (regularSeeds H selected Gamma F).card≤tripleCost c:=by
  classical
  obtain ⟨hr,hylo,hyhi,htlo,hthi,hc⟩:=factor_weights_of_cell H F c hcell
  have hqT:lengthTriple126 c-wt residualTotalWeights F.1≤quotientTripleT c:=by
    simpa only [quotientTripleT] using
      Nat.sub_le_sub_left htlo (lengthTriple126 c)
  have hqY:174-wt residualYSWeights F.1≤quotientTripleYS c:=by
    simpa only [quotientTripleYS] using Nat.sub_le_sub_left hylo 174
  have hqS:39-wt residualSWeights F.1≤quotientTripleS c:=by
    simpa only [quotientTripleS,hr] using Nat.le_refl (39-r c)
  have hhT:lengthTriple126 c-wt residualTotalWeights F.1-
      wt residualTotalWeights F.1≤secondTripleT c:=by
    dsimp [secondTripleT]
    omega
  have hhY:174-wt residualYSWeights F.1-wt residualYSWeights F.1≤
      secondTripleYS c:=by
    dsimp [secondTripleYS]
    omega
  have hhS:39-wt residualSWeights F.1-wt residualSWeights F.1≤
      secondTripleS c:=by
    simp only [secondTripleS,hr]
    omega
  have hhhT:lengthTriple126 c-wt residualTotalWeights F.1-
      wt residualTotalWeights F.1-wt residualTotalWeights F.1≤thirdTripleT c:=by
    dsimp [thirdTripleT]
    omega
  have hhhY:174-wt residualYSWeights F.1-wt residualYSWeights F.1-
      wt residualYSWeights F.1≤thirdTripleYS c:=by
    dsimp [thirdTripleYS]
    omega
  have hhhS:39-wt residualSWeights F.1-wt residualSWeights F.1-
      wt residualSWeights F.1≤thirdTripleS c:=by
    simp only [thirdTripleS,hr]
    omega
  let recon:=kernelReconstructLinear (K:=K) 22896342 131071
    (lengthTriple126 c) 39 126 IRSProfile.domain u0 u1
  have hdivK:∀ v:ConstraintKernel (K:=K) 22896342 131071
      (lengthTriple126 c) 39 126 IRSProfile.domain u0 u1,F.1∣recon v:=by
    intro v
    simpa only [recon,kernelReconstructLinear_apply] using
      hdiv (lengthTriple126 c) hfit.2.1 v
  let q:=quotientLinear recon F.1 hF hdivK
  have hqinj:Function.Injective q:=
    quotientLinear_injective recon
      (kernelReconstructLinear_injective (K:=K) 22896342 131071
        (lengthTriple126 c) 39 126 IRSProfile.domain u0 u1)
      F.1 hF hdivK
  have hprod (v:ConstraintKernel (K:=K) 22896342 131071
      (lengthTriple126 c) 39 126 IRSProfile.domain u0 u1):
      recon v=F.1*q v:=recon_eq_mul_quotientPolynomial recon F.1 hdivK v
  have hqbox:∀ v:ConstraintKernel (K:=K) 22896342 131071
      (lengthTriple126 c) 39 126 IRSProfile.domain u0 u1,
      q v∈globalCoefficientBox K
        (22896342-wt (contactWeights 131071) F.1) 131071
        (lengthTriple126 c-wt residualTotalWeights F.1)
        (39-wt residualSWeights F.1):=
    quotient_box_of_full_divisor 22896342 131071 (lengthTriple126 c) 39 126
      (wt (contactWeights 131071) F.1) (wt residualTotalWeights F.1)
      (wt residualSWeights F.1) IRSProfile.domain u0 u1 F.1 hF hdivK
      le_rfl le_rfl le_rfl
  have hqYS (v:ConstraintKernel (K:=K) 22896342 131071
      (lengthTriple126 c) 39 126 IRSProfile.domain u0 u1):
      wt residualYSWeights (q v)≤174-wt residualYSWeights F.1:=by
    by_cases hv:v=0
    · subst v
      simp [wt,MvPolynomial.weightedTotalDegree]
    · have hqv:q v≠0:=by
        intro hz
        apply hv
        apply hqinj
        simpa only [map_zero] using hz
      have hsrc:wt residualYSWeights (recon v)≤174:=by
        apply flag_box_ys_bound 22896342 131071 (lengthTriple126 c) 39 174
          (by decide) auxiliary126_shape
        change reconstruct K 22896342 131071 (lengthTriple126 c) 39 v.1∈
          globalCoefficientBox K 22896342 131071 (lengthTriple126 c) 39
        exact reconstruct_mem_globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39 v.1
      have hmul:=weightedTotalDegree_mul residualYSWeights F.1 (q v) hF hqv
      rw [← hprod v] at hmul
      simp only [wt] at hsrc ⊢
      omega
  have hqNested:∀ v:ConstraintKernel (K:=K) 22896342 131071
      (lengthTriple126 c) 39 126 IRSProfile.domain u0 u1,
      q v∈nestedCoefficientBox K
        (22896342-wt (contactWeights 131071) F.1) 131071
        (lengthTriple126 c-wt residualTotalWeights F.1)
        (174-wt residualYSWeights F.1) (39-wt residualSWeights F.1):=by
    intro v d hd
    have hb:=hqbox v hd
    have hy:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans (hqYS v)
    rw [weight_fin4] at hy
    simp only [residualYSWeights] at hy
    refine ⟨hb.1,?_,hb.2.1,hb.2.2⟩
    simpa [residualYSWeights] using hy
  have hchannelsFirst:=channelCount_mono hqT hqY hqS
  have hchannelsSecond:=channelCount_mono hhT hhY hhS
  have hchannelsThird:=channelCount_mono hhhT hhhY hhhS
  have hsourceCoeff:50647*channelCount
      (lengthTriple126 c-wt residualTotalWeights F.1)
      (174-wt residualYSWeights F.1) (39-wt residualSWeights F.1)+
      50647*channelCount
        (lengthTriple126 c-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
        (174-wt residualYSWeights F.1-wt residualYSWeights F.1)
        (39-wt residualSWeights F.1-wt residualSWeights F.1)+
      50647*channelCount
        (lengthTriple126 c-wt residualTotalWeights F.1-wt residualTotalWeights F.1-
          wt residualTotalWeights F.1)
        (174-wt residualYSWeights F.1-wt residualYSWeights F.1-
          wt residualYSWeights F.1)
        (39-wt residualSWeights F.1-wt residualSWeights F.1-
          wt residualSWeights F.1)<
      coefficientCount 22896342 131071 (lengthTriple126 c) 39-
        Fintype.card I*localRankBound 126 (lengthTriple126 c) 39:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      auxiliary126_gap_affine (lengthTriple126 c) hfit.1]
    exact (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left 50647 hchannelsFirst)
      (Nat.mul_le_mul_left 50647 hchannelsSecond))
      (Nat.mul_le_mul_left 50647 hchannelsThird)).trans_lt
        (by simpa only [bandTripleFirst,bandTripleSecond,bandTripleThird,
          sourceGapTriple126] using hfit.2.2.2.1)
  have hsource:=hsourceCoeff.trans_le
    (constraintKernel_finrank_lower_bound 22896342 131071
      (lengthTriple126 c) 39 126 IRSProfile.domain u0 u1)
  have hwidth:22896342-wt (contactWeights 131071) F.1≤
      (22896342-50647-wt (contactWeights 131071) F.1)+50647:=by omega
  have hirr:=(RCN167.positiveRFactors_spec H F.1 F.2).1
  have htwo:(2:K)≠0:=by
    intro hz
    have hdvd:2130706433∣2:=(CharP.cast_eq_zero_iff K 2130706433 2).mp hz
    norm_num at hdvd
  have hsix:(6:K)≠0:=by
    intro hz
    have hdvd:2130706433∣6:=(CharP.cast_eq_zero_iff K 2130706433 6).mp hz
    norm_num at hdvd
  rcases LocatorTripleSquareAvoidance.exists_low_not_dvd_or_squares
      (22896342-wt (contactWeights 131071) F.1)
      (22896342-50647-wt (contactWeights 131071) F.1)
      131071 50647
      (lengthTriple126 c-wt residualTotalWeights F.1)
      (174-wt residualYSWeights F.1) (39-wt residualSWeights F.1)
      hwidth q hqinj hqNested F.1 hF hsource with hfirst|hrest
  · obtain ⟨v,hv,hQ,hQbox,hnot⟩:=hfirst
    have heq:F.1*q v=reconstruct K 22896342 131071
        (lengthTriple126 c) 39 v.1:=by
      simpa only [recon,kernelReconstructLinear_apply] using (hprod v).symm
    have hlow:reconstruct K 22896342 131071 (lengthTriple126 c) 39 v.1∈
        globalCoefficientBox K (22896342-50647) 131071
          (lengthTriple126 c) 39:=by
      rw [← heq]
      have hsourceBox:F.1*q v∈globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39:=by
        rw [heq]
        exact reconstruct_mem_globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39 v.1
      have hsrc:=(mem_flagGlobalCoefficientBox_iff (F.1*q v) 22896342
        131071 (lengthTriple126 c) 39 (by decide)).mp hsourceBox
      have hqc:=(nested_mem_weights hQbox hQ).2.2.2
      have hmul:=weightedTotalDegree_mul (contactWeights 131071) F.1 (q v) hF hQ
      apply (mem_flagGlobalCoefficientBox_iff (F.1*q v) (22896342-50647)
        131071 (lengthTriple126 c) 39 (by decide)).mpr
      refine ⟨hsrc.1,hsrc.2.1,?_⟩
      simp only [wt] at hqc ⊢
      omega
    have hrel:IsRelPrime F.1 (q v):=hirr.isRelPrime_iff_not_dvd.mpr hnot
    have hwQ:=nested_mem_weights hQbox hQ
    have hFY:F.1.degreeOf 1≤(pairTripleFirst c).leftY:=
      (degreeY_le_ysWeight F.1).trans hyhi
    have hFR:F.1.degreeOf 2≤(pairTripleFirst c).leftR:=by
      simpa only [pairTripleFirst,LocatorContact.slope_weight_eq_degreeR]
        using hr.le
    have hFZ:F.1.degreeOf 3≤(pairTripleFirst c).leftZ:=
      (degreeZ_le_totalWeight F.1).trans hthi
    have hQY:(q v).degreeOf 1≤(pairTripleFirst c).rightY:=by
      simpa only [pairTripleFirst] using (degreeY_le_ysWeight (q v)).trans
        (hwQ.2.1.trans hqY)
    have hQR:(q v).degreeOf 2≤(pairTripleFirst c).rightR:=by
      simpa only [pairTripleFirst,LocatorContact.slope_weight_eq_degreeR]
        using hwQ.2.2.1.trans hqS
    have hQZ:(q v).degreeOf 3≤(pairTripleFirst c).rightZ:=by
      simpa only [pairTripleFirst] using (degreeZ_le_totalWeight (q v)).trans
        (hwQ.1.trans hqT)
    rcases hfit.2.2.2.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
      hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hproduct:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2:Fin 4) (F.1*q v))=0:=by
      intro gamma hgamma
      have hgammaG:gamma∈Gamma:=(Finset.mem_filter.mp hgamma).1
      let support:=(Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)
      have hcard:181717≤support.card:=hagreement gamma hgammaG
      have hcap:22896342-50647≤(126-1)*support.card+(131071-1):=
        auxiliary126_capacity.trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left (126-1) hcard) _)
      have hvalues:∀ i∈support,(selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i:=by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      rw [heq]
      exact specialization_pderiv_R_eq_zero_of_kernel_low_box
        22896342 (22896342-50647) 131071 (lengthTriple126 c) 39 126
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hgammaG) hcap hvalues
    have hcount:=regularSeeds_count_le_intersection_of_product
      (pairTripleFirst c) H (q v) F hrel 2130706433
      hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
      (by change (Finset.univ:Finset I).card=262144
          rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
      (by simpa only [pairTripleFirst] using (show 1≤131071 by decide))
      (by simpa only [pairTripleFirst] using (show 131071<2130706433 by decide))
      (by simpa only [pairTripleFirst] using (show 131071<181717 by decide))
      (by simpa only [pairTripleFirst] using (show 181717≤262144 by decide))
      hdegree hagreement
      (by simpa only [pairTripleFirst,UnequalParameters.errors,Nat.reduceSub] using hno)
      hproduct
    exact hcount.trans (by
      simp only [tripleCost]
      exact (Nat.le_max_left _ _).trans (Nat.le_max_left _ _))
  rcases hrest with hsecond|hthird
  · obtain ⟨v,Q,hv,hQ,hFQ,hQbox,hnot⟩:=hsecond
    have heq:reconstruct K 22896342 131071 (lengthTriple126 c) 39 v.1=
        F.1*(F.1*Q):=by
      calc
        _=recon v:=by rfl
        _=F.1*q v:=hprod v
        _=F.1*(F.1*Q):=congrArg (fun W=>F.1*W) hFQ.symm
    have hwQ:=nested_mem_weights hQbox hQ
    have hrel:IsRelPrime F.1 Q:=hirr.isRelPrime_iff_not_dvd.mpr hnot
    have hlow:reconstruct K 22896342 131071 (lengthTriple126 c) 39 v.1∈
        globalCoefficientBox K (22896342-2*50647) 131071
          (lengthTriple126 c) 39:=by
      rw [heq]
      have hsourceBox:F.1*(F.1*Q)∈globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39:=by
        rw [← heq]
        exact reconstruct_mem_globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39 v.1
      have hsrc:=(mem_flagGlobalCoefficientBox_iff (F.1*(F.1*Q)) 22896342
        131071 (lengthTriple126 c) 39 (by decide)).mp hsourceBox
      have hqc:=hwQ.2.2.2
      have hmulInner:=weightedTotalDegree_mul (contactWeights 131071) F.1 Q hF hQ
      have hmulOuter:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*Q) hF (mul_ne_zero hF hQ)
      apply (mem_flagGlobalCoefficientBox_iff (F.1*(F.1*Q))
        (22896342-2*50647) 131071 (lengthTriple126 c) 39 (by decide)).mpr
      refine ⟨hsrc.1,hsrc.2.1,?_⟩
      simp only [wt] at hqc ⊢
      omega
    have hFY:F.1.degreeOf 1≤(pairTripleSecond c).leftY:=
      (degreeY_le_ysWeight F.1).trans hyhi
    have hFR:F.1.degreeOf 2≤(pairTripleSecond c).leftR:=by
      simpa only [pairTripleSecond,LocatorContact.slope_weight_eq_degreeR]
        using hr.le
    have hFZ:F.1.degreeOf 3≤(pairTripleSecond c).leftZ:=
      (degreeZ_le_totalWeight F.1).trans hthi
    have hQY:Q.degreeOf 1≤(pairTripleSecond c).rightY:=by
      simpa only [pairTripleSecond] using (degreeY_le_ysWeight Q).trans
        (hwQ.2.1.trans hhY)
    have hQR:Q.degreeOf 2≤(pairTripleSecond c).rightR:=by
      simpa only [pairTripleSecond,LocatorContact.slope_weight_eq_degreeR]
        using hwQ.2.2.1.trans hhS
    have hQZ:Q.degreeOf 3≤(pairTripleSecond c).rightZ:=by
      simpa only [pairTripleSecond] using (degreeZ_le_totalWeight Q).trans
        (hwQ.1.trans hhT)
    rcases hfit.2.2.2.2.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
      hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hproduct:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2:Fin 4)
            (MvPolynomial.pderiv (2:Fin 4) (F.1*(F.1*Q))))=0:=by
      intro gamma hgamma
      have hgammaG:gamma∈Gamma:=(Finset.mem_filter.mp hgamma).1
      let support:=(Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)
      have hcard:181717≤support.card:=hagreement gamma hgammaG
      have hcap:22896342-2*50647≤(126-2)*support.card+2*(131071-1):=
        auxiliary126_double_capacity.trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left (126-2) hcard) _)
      have hvalues:∀ i∈support,(selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i:=by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      rw [← heq]
      exact LocatorDoubleSquareAvoidance.specialization_pderiv_R2_eq_zero_of_kernel_low_box
        22896342 (22896342-2*50647) 131071 (lengthTriple126 c) 39 126
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hgammaG) hcap hvalues
    have hQzero:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q=0:=by
      intro gamma hgamma
      obtain ⟨hFzero,hregular⟩:=(Finset.mem_filter.mp hgamma).2
      exact LocatorDoubleSquareAvoidance.specialization_eq_zero_of_pderiv_R2_square_product
        (selected gamma) gamma F.1 Q htwo hFzero hregular
          (hproduct gamma hgamma)
    have hcount:=regularSeeds_count_le_intersection
      (pairTripleSecond c) H Q F hrel 2130706433
      hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
      (by change (Finset.univ:Finset I).card=262144
          rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
      (by simpa only [pairTripleSecond] using (show 1≤131071 by decide))
      (by simpa only [pairTripleSecond] using (show 131071<2130706433 by decide))
      (by simpa only [pairTripleSecond] using (show 131071<181717 by decide))
      (by simpa only [pairTripleSecond] using (show 181717≤262144 by decide))
      hdegree hagreement
      (by simpa only [pairTripleSecond,UnequalParameters.errors,Nat.reduceSub] using hno)
      hQzero
    exact hcount.trans (by
      simp only [tripleCost]
      exact (Nat.le_max_right _ _).trans (Nat.le_max_left _ _))
  · obtain ⟨v,Q,hv,hQ,hFQ,hQbox⟩:=hthird
    have heq:reconstruct K 22896342 131071 (lengthTriple126 c) 39 v.1=
        F.1*(F.1*(F.1*Q)):=by
      calc
        _=recon v:=by rfl
        _=F.1*q v:=hprod v
        _=F.1*(F.1*(F.1*Q)):=congrArg (fun W=>F.1*W) hFQ.symm
    have hwQ:=nested_mem_weights hQbox hQ
    have hrel:IsRelPrime F.1 Q:=by
      apply isRelPrime_of_weight_lt residualTotalWeights F.1 Q hirr hQ
      have h:=hwQ.1
      have hlen4:lengthTriple126 c<4*tlo c:=hfit.2.2.1
      omega
    have hlow:reconstruct K 22896342 131071 (lengthTriple126 c) 39 v.1∈
        globalCoefficientBox K (22896342-3*50647) 131071
          (lengthTriple126 c) 39:=by
      rw [heq]
      have hsourceBox:F.1*(F.1*(F.1*Q))∈globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39:=by
        rw [← heq]
        exact reconstruct_mem_globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39 v.1
      have hsrc:=(mem_flagGlobalCoefficientBox_iff (F.1*(F.1*(F.1*Q))) 22896342
        131071 (lengthTriple126 c) 39 (by decide)).mp hsourceBox
      have hqc:=hwQ.2.2.2
      have hmulInner:=weightedTotalDegree_mul (contactWeights 131071) F.1 Q hF hQ
      have hmulMiddle:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*Q) hF (mul_ne_zero hF hQ)
      have hmulOuter:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*(F.1*Q)) hF (mul_ne_zero hF (mul_ne_zero hF hQ))
      apply (mem_flagGlobalCoefficientBox_iff (F.1*(F.1*(F.1*Q)))
        (22896342-3*50647) 131071 (lengthTriple126 c) 39 (by decide)).mpr
      refine ⟨hsrc.1,hsrc.2.1,?_⟩
      simp only [wt] at hqc ⊢
      omega
    have hFY:F.1.degreeOf 1≤(pairTripleThird c).leftY:=
      (degreeY_le_ysWeight F.1).trans hyhi
    have hFR:F.1.degreeOf 2≤(pairTripleThird c).leftR:=by
      simpa only [pairTripleThird,LocatorContact.slope_weight_eq_degreeR]
        using hr.le
    have hFZ:F.1.degreeOf 3≤(pairTripleThird c).leftZ:=
      (degreeZ_le_totalWeight F.1).trans hthi
    have hQY:Q.degreeOf 1≤(pairTripleThird c).rightY:=by
      simpa only [pairTripleThird] using (degreeY_le_ysWeight Q).trans
        (hwQ.2.1.trans hhhY)
    have hQR:Q.degreeOf 2≤(pairTripleThird c).rightR:=by
      simpa only [pairTripleThird,LocatorContact.slope_weight_eq_degreeR]
        using hwQ.2.2.1.trans hhhS
    have hQZ:Q.degreeOf 3≤(pairTripleThird c).rightZ:=by
      simpa only [pairTripleThird] using (degreeZ_le_totalWeight Q).trans
        (hwQ.1.trans hhhT)
    rcases hfit.2.2.2.2.2.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
      hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hproduct:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2:Fin 4)
            (MvPolynomial.pderiv (2:Fin 4)
              (MvPolynomial.pderiv (2:Fin 4) (F.1*(F.1*(F.1*Q))))))=0:=by
      intro gamma hgamma
      have hgammaG:gamma∈Gamma:=(Finset.mem_filter.mp hgamma).1
      let support:=(Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)
      have hcard:181717≤support.card:=hagreement gamma hgammaG
      have hcap:22896342-3*50647≤(126-3)*support.card+3*(131071-1):=
        auxiliary126_triple_capacity.trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left (126-3) hcard) _)
      have hvalues:∀ i∈support,(selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i:=by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      rw [← heq]
      exact LocatorTripleSquareAvoidance.specialization_pderiv_R3_eq_zero_of_kernel_low_box
        22896342 (22896342-3*50647) 131071 (lengthTriple126 c) 39 126
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hgammaG) hcap hvalues
    have hQzero:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q=0:=by
      intro gamma hgamma
      obtain ⟨hFzero,hregular⟩:=(Finset.mem_filter.mp hgamma).2
      exact LocatorTripleSquareAvoidance.specialization_eq_zero_of_pderiv_R3_cube_product
        (selected gamma) gamma F.1 Q hsix hFzero hregular
          (hproduct gamma hgamma)
    have hcount:=regularSeeds_count_le_intersection
      (pairTripleThird c) H Q F hrel 2130706433
      hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
      (by change (Finset.univ:Finset I).card=262144
          rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
      (by simpa only [pairTripleThird] using (show 1≤131071 by decide))
      (by simpa only [pairTripleThird] using (show 131071<2130706433 by decide))
      (by simpa only [pairTripleThird] using (show 131071<181717 by decide))
      (by simpa only [pairTripleThird] using (show 181717≤262144 by decide))
      hdegree hagreement
      (by simpa only [pairTripleThird,UnequalParameters.errors,Nat.reduceSub] using hno)
      hQzero
    exact hcount.trans (by
      simp only [tripleCost]
      exact Nat.le_max_right _ _)

theorem regularSeeds_count_le_chosen
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181717≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80427)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv72:∀ L,L≤52091→∀ v:ConstraintKernel (K:=K) 13083624 131071 L 21 72
      IRSProfile.domain u0 u1,F.1∣reconstruct K 13083624 131071 L 21 v.1)
    (hdiv126:∀ L,L≤52091→∀ v:ConstraintKernel (K:=K) 22896342 131071 L 39 126
      IRSProfile.domain u0 u1,F.1∣reconstruct K 22896342 131071 L 39 v.1)
    (c:Cell)
    (hcell:InCell (regularCumulativeFlag H F) c)
    (hbad:LocatorFactorReplacement.Bad 2450 131072 131073 271696879461797498
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
      (regularCumulativeFlag H F) 2450 (yhi c)
      (r c) 271696879461797498
      hrpos hcell.all_eq hcell.middle_le_yhi
      ((yhi_le_77 c).trans (by decide))
      (hcell.total_le_thi.trans (thi_le_2450 c))
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
  have hlast:=hroutes'.resolve_left h126
  by_cases hdouble:Double126Fits c
  · have h:=double126_count u0 u1 H selected Gamma hdegree hagreement hno F hF
      hdiv126 c hcell hdouble
    simpa only [chosenCost,if_neg ho,if_neg h72,if_neg h126,if_pos hdouble] using h
  · have htriple:Triple126Fits c:=hlast.resolve_left hdouble
    have h:=triple126_count u0 u1 H selected Gamma hdegree hagreement hno F hF
      hdiv126 c hcell htriple
    simpa only [chosenCost,if_neg ho,if_neg h72,if_neg h126,if_neg hdouble] using h
end
end LocatorQuotientReplacement
