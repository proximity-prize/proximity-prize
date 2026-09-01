import ProximityPrize.SubmissionLower.LocatorQuotientReplacement
import ProximityPrize.SubmissionLower.LocatorTripleFactorSwitch
import ProximityPrize.SubmissionLower.LocatorQuarticFourthAvoidance

namespace ProximityPrize.SubmissionLower.LocatorHybridQuarticReplacement

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN266
open RCN260 LocatorFactorAggregate LocatorLowQuotient LocatorCoprimeQuotient
open LocatorReplacementData LocatorReplacementGrid LocatorQuotientReplacement

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
theorem regularSeeds_count_le_hybrid126
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181707≤((Finset.univ:Finset I).filter
      (fun i=>(selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80437)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤52091→∀ v:ConstraintKernel (K:=K) 22895082 131071 L 39 126
      IRSProfile.domain u0 u1,F.1∣reconstruct K 22895082 131071 L 39 v.1)
    (c:Cell) (hcell:InCell (regularCumulativeFlag H F) c)
    (hfit:hybridFits c):
    (regularSeeds H selected Gamma F).card≤hybridCost c:=by
  classical
  obtain ⟨hr,hy,htlo,hthi⟩:=factor_weights_of_cell H F c hcell
  have hylo:y c≤wt residualYSWeights F.1:=hy.ge
  have hyhi:wt residualYSWeights F.1≤y c:=hy.le
  let recon:=kernelReconstructLinear (K:=K) 22895082 131071
    (hybridLength c) 39 126 IRSProfile.domain u0 u1
  have hdivK:∀ v:ConstraintKernel (K:=K) 22895082 131071
      (hybridLength c) 39 126 IRSProfile.domain u0 u1,F.1∣recon v:=by
    intro v
    simpa only [recon,kernelReconstructLinear_apply] using
      hdiv (hybridLength c) hfit.2.1 v
  let q:=quotientLinear recon F.1 hF hdivK
  have hqinj:Function.Injective q:=
    quotientLinear_injective recon
      (kernelReconstructLinear_injective (K:=K) 22895082 131071
        (hybridLength c) 39 126 IRSProfile.domain u0 u1)
      F.1 hF hdivK
  have hprod (v:ConstraintKernel (K:=K) 22895082 131071
      (hybridLength c) 39 126 IRSProfile.domain u0 u1):
      recon v=F.1*q v:=recon_eq_mul_quotientPolynomial recon F.1 hdivK v
  have hqbox:∀ v:ConstraintKernel (K:=K) 22895082 131071
      (hybridLength c) 39 126 IRSProfile.domain u0 u1,
      q v∈globalCoefficientBox K
        (22895082-wt (contactWeights 131071) F.1) 131071
        (hybridLength c-wt residualTotalWeights F.1)
        (39-wt residualSWeights F.1):=
    quotient_box_of_full_divisor 22895082 131071 (hybridLength c) 39 126
      (wt (contactWeights 131071) F.1) (wt residualTotalWeights F.1)
      (wt residualSWeights F.1) IRSProfile.domain u0 u1 F.1 hF hdivK
      le_rfl le_rfl le_rfl
  have hqYS (v:ConstraintKernel (K:=K) 22895082 131071
      (hybridLength c) 39 126 IRSProfile.domain u0 u1):
      wt residualYSWeights (q v)≤174-wt residualYSWeights F.1:=by
    by_cases hv:v=0
    · subst v
      simp [wt,MvPolynomial.weightedTotalDegree]
    · have hqv:q v≠0:=by
        intro hz
        apply hv
        apply hqinj
        simpa only [map_zero] using hz
      have hsrc':wt residualYSWeights
          (reconstruct K 22895082 131071 (hybridLength c) 39 v.1)≤174:=
        flag_box_ys_bound 22895082 131071 (hybridLength c) 39 174
          (by decide) LocatorAuxiliaryArithmetic.source126_shape
          (reconstruct K 22895082 131071 (hybridLength c) 39 v.1)
          (reconstruct_mem_globalCoefficientBox K 22895082 131071
            (hybridLength c) 39 v.1)
      have hsrc:wt residualYSWeights (recon v)≤174:=by
        simpa only [recon,kernelReconstructLinear_apply] using hsrc'
      have hmul:=weightedTotalDegree_mul residualYSWeights F.1 (q v) hF hqv
      rw [←hprod v] at hmul
      simp only [wt] at hsrc ⊢
      omega
  have hqNested:∀ v:ConstraintKernel (K:=K) 22895082 131071
      (hybridLength c) 39 126 IRSProfile.domain u0 u1,
      q v∈nestedCoefficientBox K
        (22895082-wt (contactWeights 131071) F.1) 131071
        (hybridFirstT c) (hybridFirstY c) (hybridFirstS c):=by
    intro v d hd
    have hb:=hqbox v hd
    have hy:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans (hqYS v)
    rw [weight_fin4] at hy
    have hy':d 1+d 2≤174-wt residualYSWeights F.1:=by
      simpa [residualYSWeights] using hy
    have hT:d 1+d 2+d 3≤hybridFirstT c:=by
      apply hb.1.trans
      simpa only [hybridFirstT] using
        Nat.sub_le_sub_left htlo (hybridLength c)
    have hY:d 1+d 2≤hybridFirstY c:=by
      apply le_min
      · exact hy'.trans (Nat.sub_le_sub_left hylo 174)
      · exact (Nat.le_add_right (d 1+d 2) (d 3)).trans hT
    have hS:d 2≤hybridFirstS c:=by
      apply le_min
      · simpa only [hr] using hb.2.1
      · omega
    exact ⟨hT,hY,hS,hb.2.2⟩
  have hT2:hybridFirstT c-wt residualTotalWeights F.1≤hybridSecondT c:=by
    dsimp [hybridFirstT,hybridSecondT]
    omega
  have hY2:min (hybridFirstY c-wt residualYSWeights F.1)
      (hybridFirstT c-wt residualTotalWeights F.1)≤hybridSecondY c:=by
    dsimp [hybridSecondY]
    apply le_min
    · calc
        _≤hybridFirstY c-wt residualYSWeights F.1:=Nat.min_le_left _ _
        _≤(174-y c)-wt residualYSWeights F.1:=by
          apply Nat.sub_le_sub_right
          exact Nat.min_le_left _ _
        _≤174-2*y c:=by omega
    · exact (Nat.min_le_right _ _).trans hT2
  have hS2:min (hybridFirstS c-wt residualSWeights F.1)
      (min (hybridFirstY c-wt residualYSWeights F.1)
        (hybridFirstT c-wt residualTotalWeights F.1))≤hybridSecondS c:=by
    dsimp [hybridSecondS]
    apply le_min
    · calc
        _≤hybridFirstS c-wt residualSWeights F.1:=Nat.min_le_left _ _
        _≤(39-r c)-wt residualSWeights F.1:=by
          apply Nat.sub_le_sub_right
          exact Nat.min_le_left _ _
        _≤39-2*r c:=by omega
    · exact (Nat.min_le_right _ _).trans hY2
  have hT3:hybridFirstT c-wt residualTotalWeights F.1-
      wt residualTotalWeights F.1≤hybridThirdT c:=by
    dsimp [hybridFirstT,hybridThirdT]
    omega
  have hY3:min
      (min (hybridFirstY c-wt residualYSWeights F.1)
          (hybridFirstT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
      (hybridFirstT c-wt residualTotalWeights F.1-
        wt residualTotalWeights F.1)≤hybridThirdY c:=by
    dsimp [hybridThirdY]
    apply le_min
    · calc
        _≤hybridFirstY c-wt residualYSWeights F.1-
            wt residualYSWeights F.1:=by
              exact (Nat.min_le_left _ _).trans (Nat.sub_le_sub_right
                (Nat.min_le_left _ _) _)
        _≤(174-y c)-wt residualYSWeights F.1-
            wt residualYSWeights F.1:=by
              apply Nat.sub_le_sub_right
              apply Nat.sub_le_sub_right
              exact Nat.min_le_left _ _
        _≤174-3*y c:=by omega
    · exact (Nat.min_le_right _ _).trans hT3
  have hS3:min
      (min (hybridFirstS c-wt residualSWeights F.1)
          (min (hybridFirstY c-wt residualYSWeights F.1)
            (hybridFirstT c-wt residualTotalWeights F.1))-wt residualSWeights F.1)
      (min
        (min (hybridFirstY c-wt residualYSWeights F.1)
            (hybridFirstT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
        (hybridFirstT c-wt residualTotalWeights F.1-
          wt residualTotalWeights F.1))≤hybridThirdS c:=by
    dsimp [hybridThirdS]
    apply le_min
    · calc
        _≤hybridFirstS c-wt residualSWeights F.1-
            wt residualSWeights F.1:=by
              exact (Nat.min_le_left _ _).trans (Nat.sub_le_sub_right
                (Nat.min_le_left _ _) _)
        _≤(39-r c)-wt residualSWeights F.1-
            wt residualSWeights F.1:=by
              apply Nat.sub_le_sub_right
              apply Nat.sub_le_sub_right
              exact Nat.min_le_left _ _
        _≤39-3*r c:=by omega
    · exact (Nat.min_le_right _ _).trans hY3
  have hT4:hybridFirstT c-wt residualTotalWeights F.1-
      wt residualTotalWeights F.1-wt residualTotalWeights F.1≤
      hybridFourthT c:=by
    dsimp [hybridFirstT,hybridFourthT]
    omega
  have hY4:min
      (min
          (min (hybridFirstY c-wt residualYSWeights F.1)
              (hybridFirstT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
          (hybridFirstT c-wt residualTotalWeights F.1-
            wt residualTotalWeights F.1)-wt residualYSWeights F.1)
      (hybridFirstT c-wt residualTotalWeights F.1-
        wt residualTotalWeights F.1-wt residualTotalWeights F.1)≤
      hybridFourthY c:=by
    dsimp [hybridFourthY]
    apply le_min
    · calc
        _≤(min
            (min (hybridFirstY c-wt residualYSWeights F.1)
                (hybridFirstT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
            (hybridFirstT c-wt residualTotalWeights F.1-
              wt residualTotalWeights F.1))-wt residualYSWeights F.1:=
          Nat.min_le_left _ _
        _≤hybridThirdY c-wt residualYSWeights F.1:=
          Nat.sub_le_sub_right hY3 _
        _=hybridThirdY c-y c:=by rw [hy]
        _≤(174-3*y c)-y c:=
          Nat.sub_le_sub_right (Nat.min_le_left _ _) _
        _≤174-4*y c:=by omega
    · exact (Nat.min_le_right _ _).trans hT4
  have hS4:min
      (min
          (min (hybridFirstS c-wt residualSWeights F.1)
              (min (hybridFirstY c-wt residualYSWeights F.1)
                (hybridFirstT c-wt residualTotalWeights F.1))-wt residualSWeights F.1)
          (min
            (min (hybridFirstY c-wt residualYSWeights F.1)
                (hybridFirstT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
            (hybridFirstT c-wt residualTotalWeights F.1-
              wt residualTotalWeights F.1))-wt residualSWeights F.1)
      (min
        (min
            (min (hybridFirstY c-wt residualYSWeights F.1)
                (hybridFirstT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
            (hybridFirstT c-wt residualTotalWeights F.1-
              wt residualTotalWeights F.1)-wt residualYSWeights F.1)
        (hybridFirstT c-wt residualTotalWeights F.1-
          wt residualTotalWeights F.1-wt residualTotalWeights F.1))≤
      hybridFourthS c:=by
    dsimp [hybridFourthS]
    apply le_min
    · calc
        _≤(min
            (min (hybridFirstS c-wt residualSWeights F.1)
                (min (hybridFirstY c-wt residualYSWeights F.1)
                  (hybridFirstT c-wt residualTotalWeights F.1))-wt residualSWeights F.1)
            (min
              (min (hybridFirstY c-wt residualYSWeights F.1)
                  (hybridFirstT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
              (hybridFirstT c-wt residualTotalWeights F.1-
                wt residualTotalWeights F.1)))-wt residualSWeights F.1:=
          Nat.min_le_left _ _
        _≤hybridThirdS c-wt residualSWeights F.1:=
          Nat.sub_le_sub_right hS3 _
        _=hybridThirdS c-r c:=by rw [hr]
        _≤(39-3*r c)-r c:=
          Nat.sub_le_sub_right (Nat.min_le_left _ _) _
        _≤39-4*r c:=by omega
    · exact (Nat.min_le_right _ _).trans hY4
  have hchannels1:channelCount (hybridFirstT c) (hybridFirstY c)
      (hybridFirstS c)≤channelCount (hybridFirstT c) (hybridFirstY c)
        (hybridFirstS c):=le_rfl
  have hchannels2:=channelCount_mono hT2 hY2 hS2
  have hchannels3:=channelCount_mono hT3 hY3 hS3
  have hchannels4:=channelCount_mono hT4 hY4 hS4
  have hsourceCoeff:
      50637*channelCount (hybridFirstT c) (hybridFirstY c) (hybridFirstS c)+
        50637*channelCount
          (hybridFirstT c-wt residualTotalWeights F.1)
          (min (hybridFirstY c-wt residualYSWeights F.1)
            (hybridFirstT c-wt residualTotalWeights F.1))
          (min (hybridFirstS c-wt residualSWeights F.1)
            (min (hybridFirstY c-wt residualYSWeights F.1)
              (hybridFirstT c-wt residualTotalWeights F.1)))+
        50637*channelCount
          (hybridFirstT c-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
          (min
            (min (hybridFirstY c-wt residualYSWeights F.1)
                (hybridFirstT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
            (hybridFirstT c-wt residualTotalWeights F.1-wt residualTotalWeights F.1))
          (min
            (min (hybridFirstS c-wt residualSWeights F.1)
                (min (hybridFirstY c-wt residualYSWeights F.1)
                  (hybridFirstT c-wt residualTotalWeights F.1))-wt residualSWeights F.1)
            (min
              (min (hybridFirstY c-wt residualYSWeights F.1)
                  (hybridFirstT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
              (hybridFirstT c-wt residualTotalWeights F.1-wt residualTotalWeights F.1)))+
        50637*channelCount
          (hybridFirstT c-wt residualTotalWeights F.1-
            wt residualTotalWeights F.1-wt residualTotalWeights F.1)
          (min
            (min
                (min (hybridFirstY c-wt residualYSWeights F.1)
                    (hybridFirstT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
                (hybridFirstT c-wt residualTotalWeights F.1-
                  wt residualTotalWeights F.1)-wt residualYSWeights F.1)
            (hybridFirstT c-wt residualTotalWeights F.1-
              wt residualTotalWeights F.1-wt residualTotalWeights F.1))
          (min
            (min
                (min (hybridFirstS c-wt residualSWeights F.1)
                    (min (hybridFirstY c-wt residualYSWeights F.1)
                      (hybridFirstT c-wt residualTotalWeights F.1))-wt residualSWeights F.1)
                (min
                  (min (hybridFirstY c-wt residualYSWeights F.1)
                      (hybridFirstT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
                  (hybridFirstT c-wt residualTotalWeights F.1-
                    wt residualTotalWeights F.1))-wt residualSWeights F.1)
            (min
              (min
                  (min (hybridFirstY c-wt residualYSWeights F.1)
                      (hybridFirstT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
                  (hybridFirstT c-wt residualTotalWeights F.1-
                    wt residualTotalWeights F.1)-wt residualYSWeights F.1)
              (hybridFirstT c-wt residualTotalWeights F.1-
                wt residualTotalWeights F.1-wt residualTotalWeights F.1)))<
      coefficientCount 22895082 131071 (hybridLength c) 39-
        Fintype.card I*localRankBound 126 (hybridLength c) 39:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      LocatorAuxiliaryArithmetic.source126_gap_affine (hybridLength c) hfit.1]
    have hbands:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left 50637 hchannels1)
      (Nat.mul_le_mul_left 50637 hchannels2))
      (Nat.mul_le_mul_left 50637 hchannels3))
      (Nat.mul_le_mul_left 50637 hchannels4)
    exact hbands.trans_lt (by
      simpa only [hybridNullity] using hfit.2.2.1)
  have hsourceRank:=hsourceCoeff.trans_le
    (constraintKernel_finrank_lower_bound 22895082 131071
      (hybridLength c) 39 126 IRSProfile.domain u0 u1)
  have hwidth:22895082-wt (contactWeights 131071) F.1≤
      (22895082-50637-wt (contactWeights 131071) F.1)+50637:=by omega
  rcases LocatorTripleFactorSwitch.exists_first_or_second_or_third_not_dvd_or_fourth_low
      (22895082-wt (contactWeights 131071) F.1)
      (22895082-50637-wt (contactWeights 131071) F.1)
      131071 50637 (hybridFirstT c) (hybridFirstY c) (hybridFirstS c)
      hwidth recon q hqinj F.1 hF hprod hqNested hsourceRank with
    hfirst|hsecond|hthird|hfourth
  · obtain ⟨v,hv,hQ,heq,hQbox,hnot⟩:=hfirst
    have hrel:IsRelPrime F.1 (q v):=
      (RCN167.positiveRFactors_spec H F.1 F.2).1.isRelPrime_iff_not_dvd.mpr hnot
    have hwQ:=nested_mem_weights hQbox hQ
    have heqR:reconstruct K 22895082 131071 (hybridLength c) 39 v.1=
        F.1*q v:=by
      simpa only [recon,kernelReconstructLinear_apply] using heq
    have hlow:reconstruct K 22895082 131071 (hybridLength c) 39 v.1∈
        globalCoefficientBox K (22895082-50637) 131071
          (hybridLength c) 39:=by
      rw [heqR]
      have hsrc:F.1*q v∈globalCoefficientBox K 22895082 131071
          (hybridLength c) 39:=by
        rw [←heqR]
        exact reconstruct_mem_globalCoefficientBox K 22895082 131071
          (hybridLength c) 39 v.1
      have hc:=(mem_flagGlobalCoefficientBox_iff (F.1*q v) 22895082
        131071 (hybridLength c) 39 (by decide)).mp hsrc
      have hqc:=hwQ.2.2.2
      have hmul:=weightedTotalDegree_mul (contactWeights 131071) F.1 (q v) hF hQ
      apply (mem_flagGlobalCoefficientBox_iff (F.1*q v) (22895082-50637)
        131071 (hybridLength c) 39 (by decide)).mpr
      refine ⟨hc.1,hc.2.1,?_⟩
      simp only [wt] at hqc hmul ⊢
      omega
    have hproduct:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2:Fin 4) (F.1*q v))=0:=by
      intro gamma hgamma
      have hg:gamma∈Gamma:=(Finset.mem_filter.mp hgamma).1
      let support:=(Finset.univ:Finset I).filter (fun i=>(selected gamma).eval
        (IRSProfile.domain i)=u0 i+gamma*u1 i)
      have hcard:181707≤support.card:=hagreement gamma hg
      have hcap:22895082-50637≤(126-1)*support.card+(131071-1):=
        LocatorAuxiliaryArithmetic.source126_capacity_one.trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left (126-1) hcard) _)
      have hvalues:∀ i∈support,(selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i:=fun i hi=>(Finset.mem_filter.mp hi).2
      rw [←heqR]
      exact specialization_pderiv_R_eq_zero_of_kernel_low_box
        22895082 (22895082-50637) 131071 (hybridLength c) 39 126
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hg) hcap hvalues
    rcases hfit.2.2.2.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
      hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hcount:=regularSeeds_count_le_intersection_of_product
      (hybridPairFirst c) H (q v) F hrel 2130706433
      ((degreeY_le_ysWeight F.1).trans hyhi)
      (by simpa only [hybridPairFirst,LocatorContact.slope_weight_eq_degreeR]
        using hr.le)
      ((degreeZ_le_totalWeight F.1).trans hthi)
      ((degreeY_le_ysWeight (q v)).trans hwQ.2.1)
      (by simpa only [hybridPairFirst,LocatorContact.slope_weight_eq_degreeR]
        using hwQ.2.2.1)
      ((degreeZ_le_totalWeight (q v)).trans hwQ.1)
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by change (Finset.univ:Finset I).card=262144
          rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
      (by simpa only [hybridPairFirst] using (show 1≤131071 by decide))
      (by simpa only [hybridPairFirst] using (show 131071<2130706433 by decide))
      (by simpa only [hybridPairFirst] using (show 131071<181707 by decide))
      (by simpa only [hybridPairFirst] using (show 181707≤262144 by decide))
      hdegree hagreement
      (by simpa only [hybridPairFirst,UnequalParameters.errors,Nat.reduceSub] using hno)
      hproduct
    exact hcount.trans (by simp only [hybridCost];exact Nat.le_max_left _ _)
  · obtain ⟨v,Q2,hv,hQ,heq,hQbox,hnot⟩:=hsecond
    have hrel:IsRelPrime F.1 Q2:=
      (RCN167.positiveRFactors_spec H F.1 F.2).1.isRelPrime_iff_not_dvd.mpr hnot
    have hwQ:=nested_mem_weights hQbox hQ
    have heqR:reconstruct K 22895082 131071 (hybridLength c) 39 v.1=
        F.1*(F.1*Q2):=by
      simpa only [recon,kernelReconstructLinear_apply] using heq
    have hlow:reconstruct K 22895082 131071 (hybridLength c) 39 v.1∈
        globalCoefficientBox K (22895082-2*50637) 131071
          (hybridLength c) 39:=by
      rw [heqR]
      have hsrc:F.1*(F.1*Q2)∈globalCoefficientBox K 22895082 131071
          (hybridLength c) 39:=by
        rw [←heqR]
        exact reconstruct_mem_globalCoefficientBox K 22895082 131071
          (hybridLength c) 39 v.1
      have hc:=(mem_flagGlobalCoefficientBox_iff (F.1*(F.1*Q2)) 22895082
        131071 (hybridLength c) 39 (by decide)).mp hsrc
      have hqc:=hwQ.2.2.2
      have hm1:=weightedTotalDegree_mul (contactWeights 131071) F.1 Q2 hF hQ
      have hm2:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*Q2) hF (mul_ne_zero hF hQ)
      apply (mem_flagGlobalCoefficientBox_iff (F.1*(F.1*Q2))
        (22895082-2*50637) 131071 (hybridLength c) 39 (by decide)).mpr
      refine ⟨hc.1,hc.2.1,?_⟩
      simp only [wt] at hqc hm1 hm2 ⊢
      omega
    have htwo:(2:K)≠0:=by
      intro hz
      have hdvd:2130706433∣2:=(CharP.cast_eq_zero_iff K 2130706433 2).mp hz
      norm_num at hdvd
    have hQzero:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q2=0:=by
      intro gamma hgamma
      have hg:gamma∈Gamma:=(Finset.mem_filter.mp hgamma).1
      let support:=(Finset.univ:Finset I).filter (fun i=>(selected gamma).eval
        (IRSProfile.domain i)=u0 i+gamma*u1 i)
      have hcard:181707≤support.card:=hagreement gamma hg
      have hcap:22895082-2*50637≤(126-2)*support.card+2*(131071-1):=
        LocatorAuxiliaryArithmetic.source126_capacity_two.trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left (126-2) hcard) _)
      have hvalues:∀ i∈support,(selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i:=fun i hi=>(Finset.mem_filter.mp hi).2
      have hderiv:RCN319.specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2:Fin 4)
            (MvPolynomial.pderiv (2:Fin 4) (F.1*(F.1*Q2))))=0:=by
        rw [←heqR]
        exact LocatorDoubleSquareAvoidance.specialization_pderiv_R2_eq_zero_of_kernel_low_box
          22895082 (22895082-2*50637) 131071 (hybridLength c) 39 126
          IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
          (by decide) (hdegree gamma hg) hcap hvalues
      obtain ⟨hFzero,hregular⟩:=(Finset.mem_filter.mp hgamma).2
      exact LocatorDoubleSquareAvoidance.specialization_eq_zero_of_pderiv_R2_square_product
        (selected gamma) gamma F.1 Q2 htwo hFzero hregular hderiv
    rcases hfit.2.2.2.2.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
      hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hcount:=regularSeeds_count_le_intersection
      (hybridPairSecond c) H Q2 F hrel 2130706433
      ((degreeY_le_ysWeight F.1).trans hyhi)
      (by simpa only [hybridPairSecond,LocatorContact.slope_weight_eq_degreeR]
        using hr.le)
      ((degreeZ_le_totalWeight F.1).trans hthi)
      ((degreeY_le_ysWeight Q2).trans (hwQ.2.1.trans hY2))
      (by simpa only [hybridPairSecond,LocatorContact.slope_weight_eq_degreeR]
        using hwQ.2.2.1.trans hS2)
      ((degreeZ_le_totalWeight Q2).trans (hwQ.1.trans hT2))
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by change (Finset.univ:Finset I).card=262144
          rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
      (by simpa only [hybridPairSecond] using (show 1≤131071 by decide))
      (by simpa only [hybridPairSecond] using (show 131071<2130706433 by decide))
      (by simpa only [hybridPairSecond] using (show 131071<181707 by decide))
      (by simpa only [hybridPairSecond] using (show 181707≤262144 by decide))
      hdegree hagreement
      (by simpa only [hybridPairSecond,UnequalParameters.errors,Nat.reduceSub] using hno)
      hQzero
    exact hcount.trans (by
      simp only [hybridCost]
      exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  · obtain ⟨v,Q3,hv,hQ,heq,hQbox,hnot⟩:=hthird
    have hwQ:=nested_mem_weights hQbox hQ
    have hrel:IsRelPrime F.1 Q3:=
      (RCN167.positiveRFactors_spec H F.1 F.2).1.isRelPrime_iff_not_dvd.mpr hnot
    have heqR:reconstruct K 22895082 131071 (hybridLength c) 39 v.1=
        F.1*(F.1*(F.1*Q3)):=by
      simpa only [recon,kernelReconstructLinear_apply] using heq
    have hlow:reconstruct K 22895082 131071 (hybridLength c) 39 v.1∈
        globalCoefficientBox K 22743171 131071 (hybridLength c) 39:=by
      rw [heqR]
      have hsrc:F.1*(F.1*(F.1*Q3))∈globalCoefficientBox K 22895082 131071
          (hybridLength c) 39:=by
        rw [←heqR]
        exact reconstruct_mem_globalCoefficientBox K 22895082 131071
          (hybridLength c) 39 v.1
      have hc:=(mem_flagGlobalCoefficientBox_iff (F.1*(F.1*(F.1*Q3)))
        22895082 131071 (hybridLength c) 39 (by decide)).mp hsrc
      have hqc:=hwQ.2.2.2
      have hm1:=weightedTotalDegree_mul (contactWeights 131071) F.1 Q3 hF hQ
      have hm2:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*Q3) hF (mul_ne_zero hF hQ)
      have hm3:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*(F.1*Q3)) hF (mul_ne_zero hF (mul_ne_zero hF hQ))
      apply (mem_flagGlobalCoefficientBox_iff (F.1*(F.1*(F.1*Q3)))
        22743171 131071 (hybridLength c) 39 (by decide)).mpr
      refine ⟨hc.1,hc.2.1,?_⟩
      simp only [wt] at hqc hm1 hm2 hm3 ⊢
      have hexact:=LocatorTripleFactorSwitch.c126_third_capacity_exact.2
      omega
    have hQzero:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q3=0:=by
      intro gamma hgamma
      have hg:gamma∈Gamma:=(Finset.mem_filter.mp hgamma).1
      let support:=(Finset.univ:Finset I).filter (fun i=>(selected gamma).eval
        (IRSProfile.domain i)=u0 i+gamma*u1 i)
      have hcard:181707≤support.card:=hagreement gamma hg
      have hvalues:∀ i∈support,(selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i:=fun i hi=>(Finset.mem_filter.mp hi).2
      obtain ⟨hFzero,hregular⟩:=(Finset.mem_filter.mp hgamma).2
      apply LocatorTripleFactorSwitch.c126_third_cube_quotient_vanish (hybridLength c)
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (hdegree gamma hg) hcard hvalues F.1 Q3
      · exact heqR
      · exact hFzero
      · exact hregular
    rcases hfit.2.2.2.2.2.2.1 with
      ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
        hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hcount:=regularSeeds_count_le_intersection
      (hybridPairThird c) H Q3 F hrel 2130706433
      ((degreeY_le_ysWeight F.1).trans hyhi)
      (by simpa only [hybridPairThird,LocatorContact.slope_weight_eq_degreeR]
        using hr.le)
      ((degreeZ_le_totalWeight F.1).trans hthi)
      ((degreeY_le_ysWeight Q3).trans (hwQ.2.1.trans hY3))
      (by simpa only [hybridPairThird,LocatorContact.slope_weight_eq_degreeR]
        using hwQ.2.2.1.trans hS3)
      ((degreeZ_le_totalWeight Q3).trans (hwQ.1.trans hT3))
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by change (Finset.univ:Finset I).card=262144
          rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
      (by simpa only [hybridPairThird] using (show 1≤131071 by decide))
      (by simpa only [hybridPairThird] using (show 131071<2130706433 by decide))
      (by simpa only [hybridPairThird] using (show 131071<181707 by decide))
      (by simpa only [hybridPairThird] using (show 181707≤262144 by decide))
      hdegree hagreement
      (by simpa only [hybridPairThird,UnequalParameters.errors,Nat.reduceSub] using hno)
      hQzero
    exact hcount.trans (by
      simp only [hybridCost]
      exact (Nat.le_max_left _ _).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  · obtain ⟨v,Q4,hv,hQ,heq,hQbox⟩:=hfourth
    have hwQ:=nested_mem_weights hQbox hQ
    have hrel:IsRelPrime F.1 Q4:=by
      have hirr:=(RCN167.positiveRFactors_spec H F.1 F.2).1
      rcases hfit.2.2.2.1 with hT|hY|hR
      · apply isRelPrime_of_weight_lt residualTotalWeights F.1 Q4 hirr hQ
        exact (hwQ.1.trans hT4).trans_lt (hT.trans_le htlo)
      · apply isRelPrime_of_weight_lt residualYSWeights F.1 Q4 hirr hQ
        exact (hwQ.2.1.trans hY4).trans_lt (hY.trans_le hylo)
      · apply isRelPrime_of_weight_lt residualSWeights F.1 Q4 hirr hQ
        rw [hr]
        exact (hwQ.2.2.1.trans hS4).trans_lt hR
    have heqR:reconstruct K 22895082 131071 (hybridLength c) 39 v.1=
        F.1*(F.1*(F.1*(F.1*Q4))):=by
      simpa only [recon,kernelReconstructLinear_apply] using heq
    have hlow:reconstruct K 22895082 131071 (hybridLength c) 39 v.1∈
        globalCoefficientBox K 22692534 131071 (hybridLength c) 39:=by
      rw [heqR]
      have hsrc:F.1*(F.1*(F.1*(F.1*Q4)))∈
          globalCoefficientBox K 22895082 131071 (hybridLength c) 39:=by
        rw [←heqR]
        exact reconstruct_mem_globalCoefficientBox K 22895082 131071
          (hybridLength c) 39 v.1
      have hc:=(mem_flagGlobalCoefficientBox_iff
        (F.1*(F.1*(F.1*(F.1*Q4)))) 22895082 131071
        (hybridLength c) 39 (by decide)).mp hsrc
      have hqc:=hwQ.2.2.2
      have hm1:=weightedTotalDegree_mul (contactWeights 131071) F.1 Q4 hF hQ
      have hm2:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*Q4) hF (mul_ne_zero hF hQ)
      have hm3:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*(F.1*Q4)) hF (mul_ne_zero hF (mul_ne_zero hF hQ))
      have hm4:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*(F.1*(F.1*Q4))) hF
        (mul_ne_zero hF (mul_ne_zero hF (mul_ne_zero hF hQ)))
      apply (mem_flagGlobalCoefficientBox_iff (F.1*(F.1*(F.1*(F.1*Q4))))
        22692534 131071 (hybridLength c) 39 (by decide)).mpr
      refine ⟨hc.1,hc.2.1,?_⟩
      simp only [wt] at hqc hm1 hm2 hm3 hm4 ⊢
      have hexact:=LocatorTripleFactorSwitch.c126_fourth_capacity_exact.2
      omega
    have hQzero:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q4=0:=by
      intro gamma hgamma
      have hg:gamma∈Gamma:=(Finset.mem_filter.mp hgamma).1
      let support:=(Finset.univ:Finset I).filter (fun i=>(selected gamma).eval
        (IRSProfile.domain i)=u0 i+gamma*u1 i)
      have hcard:181707≤support.card:=hagreement gamma hg
      have hvalues:∀ i∈support,(selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i:=fun i hi=>(Finset.mem_filter.mp hi).2
      obtain ⟨hFzero,hregular⟩:=(Finset.mem_filter.mp hgamma).2
      apply LocatorTripleFactorSwitch.c126_fourth_power_quotient_vanish
        (hybridLength c) IRSProfile.domain u0 u1 v hlow
        (selected gamma) gamma support (hdegree gamma hg) hcard hvalues F.1 Q4
      · exact heqR
      · exact hFzero
      · exact hregular
    rcases hfit.2.2.2.2.2.2.2.1 with
      ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
        hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hcount:=regularSeeds_count_le_intersection
      (hybridPairFourth c) H Q4 F hrel 2130706433
      ((degreeY_le_ysWeight F.1).trans hyhi)
      (by simpa only [hybridPairFourth,LocatorContact.slope_weight_eq_degreeR]
        using hr.le)
      ((degreeZ_le_totalWeight F.1).trans hthi)
      ((degreeY_le_ysWeight Q4).trans (hwQ.2.1.trans hY4))
      (by simpa only [hybridPairFourth,LocatorContact.slope_weight_eq_degreeR]
        using hwQ.2.2.1.trans hS4)
      ((degreeZ_le_totalWeight Q4).trans (hwQ.1.trans hT4))
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by change (Finset.univ:Finset I).card=262144
          rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
      (by simpa only [hybridPairFourth] using (show 1≤131071 by decide))
      (by simpa only [hybridPairFourth] using (show 131071<2130706433 by decide))
      (by simpa only [hybridPairFourth] using (show 131071<181707 by decide))
      (by simpa only [hybridPairFourth] using (show 181707≤262144 by decide))
      hdegree hagreement
      (by simpa only [hybridPairFourth,UnequalParameters.errors,Nat.reduceSub]
        using hno)
      hQzero
    exact hcount.trans (by
      simp only [hybridCost]
      exact (Nat.le_max_right _ _).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))

end
end ProximityPrize.SubmissionLower.LocatorHybridQuarticReplacement
