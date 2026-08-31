import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
import ProximityPrize.SubmissionLower.LocatorReplacementReceipts
import ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
import ProximityPrize.SubmissionLower.LocatorStaircaseWitness
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
import ProximityPrize.SubmissionLower.BF
namespace ProximityPrize.SubmissionLower.LocatorQuotientReplacement
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN266 RCN260 LocatorFactorAggregate LocatorLowQuotient LocatorReplacementData LocatorReplacementGrid LocatorAuxiliaryArithmetic LocatorCoprimeQuotient LocatorStaircaseWitness LocatorStaircaseAvoidance
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
    (hagreement:∀ gamma∈Gamma,181736≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80408)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤55600→∀ v:ConstraintKernel (K:=K) 13084992 131071 L 21 72
      IRSProfile.domain u0 u1,F.1∣reconstruct K 13084992 131071 L 21 v.1)
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
  have hqD:13084992-50666-wt (contactWeights 131071) F.1≤
      quotient72D c:=by
    change 13084992-50666-wt (contactWeights 131071) F.1≤
      13084992-(131071*ylo c-r c)-50666
    calc
      _≤13084992-50666-(131071*ylo c-
          r c):=Nat.sub_le_sub_left hc _
      _=_:=by omega
  have hchannels:=channelCount_mono hqT hqY hqS
  have hLmin:3257≤length72 c:=by
    have h:=hfit.2.1
    simp only [sourceGap72] at h
    omega
  have hsource:50666*channelCount
      (length72 c-wt residualTotalWeights F.1)
      (99-wt residualYSWeights F.1) (21-wt residualSWeights F.1)<
      coefficientCount 13084992 131071 (length72 c) 21-
        Fintype.card I*localRankBound 72 (length72 c) 21:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      auxiliary72_gap_affine
        (length72 c) hLmin]
    exact (Nat.mul_le_mul_left 50666 hchannels).trans_lt hfit.2.1
  obtain ⟨v,Q,_hv,hQ,_heq,hqbox,_hparent,hproduct⟩:=
    exists_fixed_quotient_with_derivative_vanishing (K:=K) (I:=I)
      13084992 131071 (length72 c) 21 72 99 50666 181736
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
    (by simpa only [pair72] using (show 131071<181736 by decide))
    (by simpa only [pair72] using (show 181736≤262144 by decide))
    hdegree hagreement
    (by simpa only [pair72,UnequalParameters.errors,Nat.reduceSub] using hno)
    (fun gamma hgamma=> hproduct gamma (regularSeeds_subset H selected Gamma F hgamma))
  simpa only [pair72Cost] using hcount

private theorem source126_count
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181736≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80408)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤55600→∀ v:ConstraintKernel (K:=K) 23443944 131071 L 40 129
      IRSProfile.domain u0 u1,F.1∣reconstruct K 23443944 131071 L 40 v.1)
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
  have hqY:178-wt residualYSWeights F.1≤quotient126YS c:=by
    simpa only [quotient126YS] using Nat.sub_le_sub_left hylo 178
  have hqS:40-wt residualSWeights F.1≤quotient126S c:=by
    simp only [quotient126S,hr]
    exact le_rfl
  have hqD:23443944-50666-wt (contactWeights 131071) F.1≤
      quotient126D c:=by
    change 23443944-50666-wt (contactWeights 131071) F.1≤
      23443944-(131071*ylo c-r c)-50666
    calc
      _≤23443944-50666-(131071*ylo c-
          r c):=Nat.sub_le_sub_left hc _
      _=_:=by omega
  have hchannels:=channelCount_mono hqT hqY hqS
  have hLmin:2313≤length126 c:=by
    have h:=hfit.2.1
    simp only [sourceGap126] at h
    omega
  have hsource:50666*channelCount
      (length126 c-wt residualTotalWeights F.1)
      (178-wt residualYSWeights F.1) (40-wt residualSWeights F.1)<
      coefficientCount 23443944 131071 (length126 c) 40-
        Fintype.card I*localRankBound 129 (length126 c) 40:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      auxiliary126_gap_affine
        (length126 c) hLmin]
    exact (Nat.mul_le_mul_left 50666 hchannels).trans_lt hfit.2.1
  obtain ⟨v,Q,_hv,hQ,_heq,hqbox,_hparent,hproduct⟩:=
    exists_fixed_quotient_with_derivative_vanishing (K:=K) (I:=I)
      23443944 131071 (length126 c) 40 129 178 50666 181736
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
        F.1 Q hirr hQ 178 hwActual.2.1
      dsimp [quotient126YS] at hY;omega
    · apply isRelPrime_of_weight_sub_bound residualSWeights
        F.1 Q hirr hQ 40 hwActual.2.2.1
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
    (by simpa only [pair126] using (show 131071<181736 by decide))
    (by simpa only [pair126] using (show 181736≤262144 by decide))
    hdegree hagreement
    (by simpa only [pair126,UnequalParameters.errors,Nat.reduceSub] using hno)
    (fun gamma hgamma=> hproduct gamma (regularSeeds_subset H selected Gamma F hgamma))
  simpa only [pair126Cost] using hcount

private theorem staircase129_count
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181736≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80408)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤55600→∀ v:ConstraintKernel (K:=K) 23443944 131071 L 40 129
      IRSProfile.domain u0 u1,F.1∣reconstruct K 23443944 131071 L 40 v.1)
    (c:Cell)
    (hcell:InCell (regularCumulativeFlag H F) c)
    (hfit:StaircaseFits c):
    (regularSeeds H selected Gamma F).card≤staircaseCost c:=by
  classical
  obtain ⟨hr,hylo,hyhi,htlo,hthi,hc⟩:=factor_weights_of_cell H F c hcell
  have hcube:coefficientCount
      (23443944-50666-50666-wt (contactWeights 131071) F.1-
        wt (contactWeights 131071) F.1-wt (contactWeights 131071) F.1)
      131071
      (3057-wt residualTotalWeights F.1-wt residualTotalWeights F.1-
        wt residualTotalWeights F.1)
      (40-wt residualSWeights F.1-wt residualSWeights F.1-
        wt residualSWeights F.1)≤staircaseCube c:=by
    have hcontact3:
        (131071*ylo c-r c)+(131071*ylo c-r c)+(131071*ylo c-r c)≤
          wt (contactWeights 131071) F.1+wt (contactWeights 131071) F.1+
            wt (contactWeights 131071) F.1:=
      Nat.add_le_add (Nat.add_le_add hc hc) hc
    have htotal3:tlo c+tlo c+tlo c≤
        wt residualTotalWeights F.1+wt residualTotalWeights F.1+
          wt residualTotalWeights F.1:=
      Nat.add_le_add (Nat.add_le_add htlo htlo) htlo
    have hD:23443944-50666-50666-wt (contactWeights 131071) F.1-
          wt (contactWeights 131071) F.1-wt (contactWeights 131071) F.1≤
        23443944-50666-50666-3*(131071*ylo c-r c):=by
      calc
        _=(23443944-50666-50666)-
            (wt (contactWeights 131071) F.1+wt (contactWeights 131071) F.1+
              wt (contactWeights 131071) F.1):=by omega
        _≤(23443944-50666-50666)-
            ((131071*ylo c-r c)+(131071*ylo c-r c)+
              (131071*ylo c-r c)):=
          Nat.sub_le_sub_left hcontact3 (23443944-50666-50666)
        _=_:=by omega
    have hL:3057-wt residualTotalWeights F.1-wt residualTotalWeights F.1-
          wt residualTotalWeights F.1≤3057-3*tlo c:=by
      calc
        _=3057-(wt residualTotalWeights F.1+wt residualTotalWeights F.1+
            wt residualTotalWeights F.1):=by omega
        _≤3057-(tlo c+tlo c+tlo c):=
          Nat.sub_le_sub_left htotal3 3057
        _=_:=by omega
    have hs:40-wt residualSWeights F.1-wt residualSWeights F.1-
        wt residualSWeights F.1≤40-3*r c:=by
      rw [hr]
      omega
    simp only [staircaseCube,staircaseLength]
    exact coefficientCount_mono_D_L_s hD hL hs
  have hqT:3057-wt residualTotalWeights F.1≤staircaseQT c:=by
    simp only [staircaseQT,staircaseLength]
    omega
  have hqY:178-wt residualYSWeights F.1≤staircaseQYS c:=by
    simp only [staircaseQYS]
    omega
  have hqS:40-wt residualSWeights F.1≤staircaseQS c:=by
    simp only [staircaseQS,hr]
    exact le_rfl
  have hrT:3057-wt residualTotalWeights F.1-wt residualTotalWeights F.1≤
      staircaseRT c:=by
    simp only [staircaseRT,staircaseLength]
    omega
  have hrY:178-wt residualYSWeights F.1-wt residualYSWeights F.1≤
      staircaseRYS c:=by
    simp only [staircaseRYS]
    omega
  have hrS:40-wt residualSWeights F.1-wt residualSWeights F.1≤
      staircaseRS c:=by
    simp only [staircaseRS,hr]
    omega
  have hchannelsQ:=channelCount_mono hqT hqY hqS
  have hchannelsR:=channelCount_mono hrT hrY hrS
  have hsource:
      50666*channelCount (3057-wt residualTotalWeights F.1)
          (178-wt residualYSWeights F.1) (40-wt residualSWeights F.1)+
        50666*channelCount
          (3057-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
          (178-wt residualYSWeights F.1-wt residualYSWeights F.1)
          (40-wt residualSWeights F.1-wt residualSWeights F.1)+
        staircaseCube c<
      coefficientCount 23443944 131071 3057 40-
        Fintype.card I*localRankBound 129 3057 40:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      auxiliary126_fixed_staircase_gap]
    calc
      _≤50666*channelCount (staircaseQT c) (staircaseQYS c) (staircaseQS c)+
          50666*channelCount (staircaseRT c) (staircaseRYS c) (staircaseRS c)+
          staircaseCube c:=by gcongr
      _=staircaseBand c+staircaseCube c:=by
        simp only [staircaseBand,Nat.mul_add]
      _<313626209135:=hfit.1
  obtain hfirst|hsecond:=
    exists_fixed_staircase_with_derivative_vanishing (K:=K) (I:=I)
      23443944 131071 3057 40 129 178 50666 (staircaseCube c) 181736
      IRSProfile.domain u0 u1 F.1 hF (hdiv 3057 (by decide)) (by decide)
      auxiliary126_shape hcube hsource auxiliary126_capacity
      auxiliary126_second_capacity selected Gamma hdegree hagreement
  · obtain ⟨v,Q,_hv,hQ,_heq,hqbox,_hparent,hproduct,hnot⟩:=hfirst
    have hqD:23443944-50666-wt (contactWeights 131071) F.1≤
        staircaseQD c:=by
      change 23443944-50666-wt (contactWeights 131071) F.1≤
        23443944-50666-(131071*ylo c-r c)
      exact Nat.sub_le_sub_left hc (23443944-50666)
    have hbox:Q∈nestedCoefficientBox K (staircaseQD c) 131071
        (staircaseQT c) (staircaseQYS c) (staircaseQS c):=
      nestedCoefficientBox_mono hqD hqT hqY hqS hqbox
    have hwCell:=nested_mem_weights hbox hQ
    have hrel:IsRelPrime F.1 Q:=
      (RCN167.positiveRFactors_spec H F.1 F.2).1.isRelPrime_iff_not_dvd.mpr hnot
    have hFY:F.1.degreeOf 1≤(staircasePairQ c).leftY:=
      (degreeY_le_ysWeight F.1).trans hyhi
    have hFR:F.1.degreeOf 2≤(staircasePairQ c).leftR:=by
      simpa only [staircasePairQ,LocatorContact.slope_weight_eq_degreeR] using hr.le
    have hFZ:F.1.degreeOf 3≤(staircasePairQ c).leftZ:=
      (degreeZ_le_totalWeight F.1).trans hthi
    have hQY:Q.degreeOf 1≤(staircasePairQ c).rightY:=
      (degreeY_le_ysWeight Q).trans hwCell.2.1
    have hQR:Q.degreeOf 2≤(staircasePairQ c).rightR:=by
      simpa only [staircasePairQ,LocatorContact.slope_weight_eq_degreeR]
        using hwCell.2.2.1
    have hQZ:Q.degreeOf 3≤(staircasePairQ c).rightZ:=
      (degreeZ_le_totalWeight Q).trans hwCell.1
    rcases hfit.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
      hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hcount:=regularSeeds_count_le_intersection_of_product
      (staircasePairQ c) H Q F hrel 2130706433 hFY hFR hFZ hQY hQR hQZ
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall
      selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by change (Finset.univ:Finset I).card=262144;rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
      (by simpa only [staircasePairQ] using (show 1≤131071 by decide))
      (by simpa only [staircasePairQ] using (show 131071<2130706433 by decide))
      (by simpa only [staircasePairQ] using (show 131071<181736 by decide))
      (by simpa only [staircasePairQ] using (show 181736≤262144 by decide))
      hdegree hagreement
      (by simpa only [staircasePairQ,UnequalParameters.errors,Nat.reduceSub] using hno)
      (fun gamma hgamma=>hproduct gamma
        (regularSeeds_subset H selected Gamma F hgamma))
    exact hcount.trans (by simp only [staircaseCost];exact Nat.le_max_left _ _)
  · obtain ⟨v,R,_hv,hR,_heq,hrbox,_hparent,hproduct,hnot⟩:=hsecond
    have hrD:23443944-50666-50666-wt (contactWeights 131071) F.1-
        wt (contactWeights 131071) F.1≤staircaseRD c:=by
      change 23443944-50666-50666-wt (contactWeights 131071) F.1-
          wt (contactWeights 131071) F.1≤
        23443944-50666-50666-2*(131071*ylo c-r c)
      have hadd:=Nat.add_le_add hc hc
      calc
        _=(23443944-50666-50666)-
            (wt (contactWeights 131071) F.1+wt (contactWeights 131071) F.1):=by omega
        _≤(23443944-50666-50666)-
            ((131071*ylo c-r c)+(131071*ylo c-r c)):=
          Nat.sub_le_sub_left hadd (23443944-50666-50666)
        _=_:=by omega
    have hbox:R∈nestedCoefficientBox K (staircaseRD c) 131071
        (staircaseRT c) (staircaseRYS c) (staircaseRS c):=
      nestedCoefficientBox_mono hrD hrT hrY hrS hrbox
    have hwCell:=nested_mem_weights hbox hR
    have hrel:IsRelPrime F.1 R:=
      (RCN167.positiveRFactors_spec H F.1 F.2).1.isRelPrime_iff_not_dvd.mpr hnot
    have hFY:F.1.degreeOf 1≤(staircasePairR c).leftY:=
      (degreeY_le_ysWeight F.1).trans hyhi
    have hFR:F.1.degreeOf 2≤(staircasePairR c).leftR:=by
      simpa only [staircasePairR,LocatorContact.slope_weight_eq_degreeR] using hr.le
    have hFZ:F.1.degreeOf 3≤(staircasePairR c).leftZ:=
      (degreeZ_le_totalWeight F.1).trans hthi
    have hRY:R.degreeOf 1≤(staircasePairR c).rightY:=
      (degreeY_le_ysWeight R).trans hwCell.2.1
    have hRR:R.degreeOf 2≤(staircasePairR c).rightR:=by
      simpa only [staircasePairR,LocatorContact.slope_weight_eq_degreeR]
        using hwCell.2.2.1
    have hRZ:R.degreeOf 3≤(staircasePairR c).rightZ:=
      (degreeZ_le_totalWeight R).trans hwCell.1
    rcases hfit.2.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
      hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hcount:=regularSeeds_count_le_intersection_of_square_product
      (staircasePairR c) H R F hrel 2130706433 (by decide)
      hFY hFR hFZ hRY hRR hRZ hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall
      selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by change (Finset.univ:Finset I).card=262144;rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
      (by simpa only [staircasePairR] using (show 1≤131071 by decide))
      (by simpa only [staircasePairR] using (show 131071<2130706433 by decide))
      (by simpa only [staircasePairR] using (show 131071<181736 by decide))
      (by simpa only [staircasePairR] using (show 181736≤262144 by decide))
      hdegree hagreement
      (by simpa only [staircasePairR,UnequalParameters.errors,Nat.reduceSub] using hno)
      (fun gamma hgamma=>hproduct gamma
        (regularSeeds_subset H selected Gamma F hgamma))
    exact hcount.trans (by simp only [staircaseCost];exact Nat.le_max_right _ _)

theorem regularSeeds_count_le_chosen
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181736≤((Finset.univ:Finset I).filter
      (fun i=> (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80408)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv72:∀ L,L≤55600→∀ v:ConstraintKernel (K:=K) 13084992 131071 L 21 72
      IRSProfile.domain u0 u1,F.1∣reconstruct K 13084992 131071 L 21 v.1)
    (hdiv126:∀ L,L≤55600→∀ v:ConstraintKernel (K:=K) 23443944 131071 L 40 129
      IRSProfile.domain u0 u1,F.1∣reconstruct K 23443944 131071 L 40 v.1)
    (c:Cell)
    (hcell:InCell (regularCumulativeFlag H F) c)
    (hbad:LocatorFactorReplacement.Bad 2319 131072 131073 271797226259522258
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
      (regularCumulativeFlag H F) 2319 (yhi c)
      (r c) 271797226259522258
      hrpos hcell.all_eq hcell.middle_le_yhi
      ((yhi_le_75 c).trans (by decide))
      (hcell.total_le_thi.trans (thi_le_2319 c))
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
  have hstaircase:StaircaseFits c:=hroutes'.resolve_left h126
  have h:=staircase129_count u0 u1 H selected Gamma hdegree hagreement hno F hF
    hdiv126 c hcell hstaircase
  simpa only [chosenCost,if_neg ho,if_neg h72,if_neg h126] using h
end
end LocatorQuotientReplacement
