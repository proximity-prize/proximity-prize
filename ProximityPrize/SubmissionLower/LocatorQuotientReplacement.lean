import ProximityPrize.SubmissionLower.LocatorReplacementData
import ProximityPrize.SubmissionLower.LocatorFactorSwitchApplication6768
import ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
import ProximityPrize.SubmissionLower.BF
namespace ProximityPrize.SubmissionLower.LocatorQuotientReplacement
open ProximityPrize.Benchmark
open RCN081 RCN100 RCN119 RCN122 RCN128 RCN130 RCN140 RCN156 RCN180 RCN234
open RCN238 RCN266
open RCN260 LocatorFactorAggregate LocatorLowQuotient
open LocatorReplacementData LocatorReplacementGrid
open LocatorChannelUpper6765 LocatorFactorSwitchApplication6768
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

theorem degreeY_le_ysWeight (Q:P4):
    Q.degreeOf (1:Fin 4)≤wt residualYSWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*0≤wt residualYSWeights Q at h
  omega

theorem degreeZ_le_totalWeight (Q:P4):
    Q.degreeOf (3:Fin 4)≤wt residualTotalWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*1≤wt residualTotalWeights Q at h
  omega

private theorem coefficientCount_mono_L_s {D w L L' s s':ℕ}
    (hL:L≤L') (hs:s≤s'):
    coefficientCount D w L s≤coefficientCount D w L' s':=by
  unfold coefficientCount
  calc
    (∑ i∈Finset.range (L+1),∑ j∈Finset.range (s+1),
      (L+1-i-j)*(D-w*i-(w-1)*j))≤
        ∑ i∈Finset.range (L+1),∑ j∈Finset.range (s+1),
          (L'+1-i-j)*(D-w*i-(w-1)*j):=by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            gcongr
    _≤∑ i∈Finset.range (L+1),∑ j∈Finset.range (s'+1),
          (L'+1-i-j)*(D-w*i-(w-1)*j):=by
            apply Finset.sum_le_sum
            intro i _
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (Nat.succ_le_succ hs)) (by simp)
    _≤∑ i∈Finset.range (L'+1),∑ j∈Finset.range (s'+1),
          (L'+1-i-j)*(D-w*i-(w-1)*j):=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (Nat.succ_le_succ hL)) (by simp)

theorem factor_weights_of_cell (H:P4) (F:RegularIndex H) (c:Cell)
    (hcell:InCell (regularCumulativeFlag H F) c):
    wt residualSWeights F.1=r c ∧
      wt residualYSWeights F.1=y c ∧
      tlo c≤wt residualTotalWeights F.1 ∧
      wt residualTotalWeights F.1≤thi c:=by
  have hc:=originalCumulativeFlag_cumulative F.1
  exact ⟨by simpa only [regularCumulativeFlag,hc.1] using hcell.all_eq,
    by simpa only [middle,regularCumulativeFlag,hc.2.1] using hcell.middle_eq,
    by simpa only [total,regularCumulativeFlag,hc.2.2] using hcell.tlo_le,
    by simpa only [total,regularCumulativeFlag,hc.2.2] using hcell.total_le_thi⟩

theorem regularSeeds_count_le_source93
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181707≤((Finset.univ:Finset I).filter
      (fun i=>(selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80437)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤52091→∀ v:ConstraintKernel (K:=K) 16898751 131071 L 27 93
      IRSProfile.domain u0 u1,F.1∣reconstruct K 16898751 131071 L 27 v.1)
    (hcontact:wt (contactWeights 131071) F.1<10539006)
    (c:Cell) (hcell:InCell (regularCumulativeFlag H F) c)
    (hfit:sourceFits c):
    (regularSeeds H selected Gamma F).card≤sourceCost c:=by
  classical
  obtain ⟨hLmin,hLmax,h2t,hbands,hsmall,hcop,hqGates,hcGates,hcost⟩:=hfit
  obtain ⟨hr,hy,htlo,hthi⟩:=factor_weights_of_cell H F c hcell
  let L:=sourceLength c
  have hdivL:∀ v:ConstraintKernel (K:=K) 16898751 131071 L 27 93
      IRSProfile.domain u0 u1,
      F.1∣reconstruct K 16898751 131071 L 27 v.1:=hdiv L hLmax
  have hnull:
      coefficientCount 16898751 131071 L 27-
        Fintype.card I*localRankBound 93 L 27=sourceNullity c:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      LocatorAuxiliaryArithmetic.source93_gap_affine L hLmin]
    rfl
  have hqT:L-wt residualTotalWeights F.1≤quotientT c:=by
    simpa only [quotientT,L] using
      Nat.sub_le_sub_left htlo L
  have hqY:128-wt residualYSWeights F.1=quotientY c:=by
    simp only [hy,quotientY]
  have hqS:27-wt residualSWeights F.1=quotientS c:=by
    simp only [hr,quotientS]
  have hcT:L-wt residualTotalWeights F.1-wt residualTotalWeights F.1≤
      cofactorT c:=by
    dsimp only [cofactorT,L]
    omega
  have hcY:128-wt residualYSWeights F.1-wt residualYSWeights F.1=
      cofactorY c:=by simp only [hy,cofactorY]
  have hcS:27-wt residualSWeights F.1-wt residualSWeights F.1=
      cofactorS c:=by simp only [hr,cofactorS]
  have hqChannel:
      channelCount (L-wt residualTotalWeights F.1)
        (128-wt residualYSWeights F.1) (27-wt residualSWeights F.1)≤
      channelUpper (quotientT c) (quotientY c) (quotientS c):=
    (channelCount_mono hqT hqY.le hqS.le).trans
      (channelCount_le_channelUpper _ _ _)
  have hcChannel:
      channelCount (L-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
        (128-wt residualYSWeights F.1-wt residualYSWeights F.1)
        (27-wt residualSWeights F.1-wt residualSWeights F.1)≤
      channelUpper (cofactorT c) (cofactorY c) (cofactorS c):=
    (channelCount_mono hcT hcY.le hcS.le).trans
      (channelCount_le_channelUpper _ _ _)
  have hsource:
      50637*channelCount (L-wt residualTotalWeights F.1)
          (128-wt residualYSWeights F.1) (27-wt residualSWeights F.1)+
        50637*channelCount
          (L-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
          (128-wt residualYSWeights F.1-wt residualYSWeights F.1)
          (27-wt residualSWeights F.1-wt residualSWeights F.1)<
        coefficientCount 16898751 131071 L 27-
          Fintype.card I*localRankBound 93 L 27:=by
    rw [hnull]
    exact (Nat.add_le_add (Nat.mul_le_mul_left 50637 hqChannel)
      (Nat.mul_le_mul_left 50637 hcChannel)).trans_lt hbands
  have hsmallBox:
      coefficientCount 50637 131071
        (L-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
        (27-wt residualSWeights F.1-wt residualSWeights F.1)≤
      (cofactorT c+1)*50637:=by
    calc
      _≤coefficientCount 50637 131071 (cofactorT c) (cofactorS c):=
        coefficientCount_mono_L_s hcT hcS.le
      _=(cofactorT c+1)*50637:=
        LocatorAuxiliaryArithmetic.smallBox_coefficientCount _ _
  have hsourceSmall:
      50637*channelCount (L-wt residualTotalWeights F.1)
          (128-wt residualYSWeights F.1) (27-wt residualSWeights F.1)+
        coefficientCount 50637 131071
          (L-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
          (27-wt residualSWeights F.1-wt residualSWeights F.1)<
        coefficientCount 16898751 131071 L 27-
          Fintype.card I*localRankBound 93 L 27:=by
    rw [hnull]
    exact (Nat.add_le_add (Nat.mul_le_mul_left 50637 hqChannel)
      hsmallBox).trans_lt hsmall
  have hwidth:16898751-wt (contactWeights 131071) F.1≤
      16898751-50637-wt (contactWeights 131071) F.1+50637:=by omega
  have hcofactor:
      L-wt residualTotalWeights F.1-wt residualTotalWeights F.1<
          wt residualTotalWeights F.1 ∨
        128-wt residualYSWeights F.1-wt residualYSWeights F.1<
          wt residualYSWeights F.1 ∨
        27-wt residualSWeights F.1-wt residualSWeights F.1<
          wt residualSWeights F.1:=by
    rcases hcop with hT|hY|hS
    · exact Or.inl (hcT.trans_lt (hT.trans_le htlo))
    · exact Or.inr (Or.inl (by simpa only [cofactorY,hy] using hY))
    · exact Or.inr (Or.inr (by simpa only [cofactorS,hr] using hS))
  let seeds:=regularSeeds H selected Gamma F
  have hsub:seeds⊆Gamma:=regularSeeds_subset H selected Gamma F
  have hroot:∀ gamma∈seeds,specialization K (selected gamma) gamma F.1=0:=
    fun _ hg=>(Finset.mem_filter.mp hg).2.1
  have hregular:∀ gamma∈seeds,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2:Fin 4) F.1)≠0:=
    fun _ hg=>(Finset.mem_filter.mp hg).2.2
  have htwo:(2:K)≠0:=by
    intro hz
    have hdvd:2130706433∣2:=(CharP.cast_eq_zero_iff K 2130706433 2).mp hz
    norm_num at hdvd
  obtain hQ|hC:=exists_coprime_quotient_or_small_cofactor
    16898751 131071 L 27 93 128 50637 181707 IRSProfile.domain u0 u1
    F.1 hF (RCN167.positiveRFactors_spec H F.1 F.2).1 hdivL (by decide)
    LocatorAuxiliaryArithmetic.source93_shape hsource hsourceSmall hwidth
    LocatorAuxiliaryArithmetic.source93_capacity_one
    LocatorAuxiliaryArithmetic.source93_capacity_two hcofactor htwo
    selected seeds (fun g hg=>hdegree g (hsub hg))
    (fun g hg=>hagreement g (hsub hg)) hroot hregular
  · obtain ⟨v,Q,hv,hQne,hrel,heq,hQbox,hparent,hproduct⟩:=hQ
    have hw:=nested_mem_weights hQbox hQne
    have hQYweight:wt residualYSWeights Q≤quotientY c:=by
      rw [←hqY]
      exact hw.2.1
    have hQRweight:wt residualSWeights Q≤quotientS c:=by
      rw [←hqS]
      exact hw.2.2.1
    have hQY:Q.degreeOf 1≤(quotientPair c).rightY:=
      (degreeY_le_ysWeight Q).trans (by simpa only [quotientPair] using hQYweight)
    have hQR:Q.degreeOf 2≤(quotientPair c).rightR:=by
      simpa only [quotientPair,LocatorContact.slope_weight_eq_degreeR]
        using hQRweight
    have hQZ:Q.degreeOf 3≤(quotientPair c).rightZ:=by
      simpa only [quotientPair] using
        (degreeZ_le_totalWeight Q).trans (hw.1.trans hqT)
    have hFY:F.1.degreeOf 1≤(quotientPair c).leftY:=by
      simpa only [quotientPair] using
        (degreeY_le_ysWeight F.1).trans hy.le
    have hFR:F.1.degreeOf 2≤(quotientPair c).leftR:=by
      simpa only [quotientPair,LocatorContact.slope_weight_eq_degreeR] using hr.le
    have hFZ:F.1.degreeOf 3≤(quotientPair c).leftZ:=by
      simpa only [quotientPair] using (degreeZ_le_totalWeight F.1).trans hthi
    rcases hqGates with ⟨hlr,hly,hlr',hlz,hmy,hmr,hmz⟩
    have hp:∀ gamma∈regularSeeds H selected Gamma F,
        specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2:Fin 4) (F.1*Q))=0:=by
      intro gamma hg
      have hh:=hproduct gamma (by simpa only [seeds] using hg)
      rw [heq] at hh
      exact hh
    have hcount:=LocatorCoprimeQuotient.regularSeeds_count_le_intersection_of_product
      (quotientPair c) H Q F hrel 2130706433
      hFY hFR hFZ
      hQY hQR hQZ hlr hly hlr' hlz hmy hmr hmz
      selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by norm_num [quotientPair,I,IRSProfile.Index])
      (by simp [quotientPair]) (by simp [quotientPair])
      (by simp [quotientPair]) (by simp [quotientPair])
      hdegree hagreement
      (by simpa only [quotientPair,UnequalParameters.errors,Nat.reduceSub] using hno)
      hp
    exact hcount.trans (Nat.le_max_left _ _)
  · obtain ⟨v,C,hv,hCne,hrel,heq,hCbox,hparent,hCroot⟩:=hC
    have hw:=nested_mem_weights hCbox hCne
    have hCYweight:wt residualYSWeights C≤cofactorY c:=by
      rw [←hcY]
      exact hw.2.1
    have hCRweight:wt residualSWeights C≤cofactorS c:=by
      rw [←hcS]
      exact hw.2.2.1
    have hCY:C.degreeOf 1≤(cofactorPair c).rightY:=
      (degreeY_le_ysWeight C).trans (by simpa only [cofactorPair] using hCYweight)
    have hCR:C.degreeOf 2≤(cofactorPair c).rightR:=by
      simpa only [cofactorPair,LocatorContact.slope_weight_eq_degreeR]
        using hCRweight
    have hCZ:C.degreeOf 3≤(cofactorPair c).rightZ:=by
      simpa only [cofactorPair] using
        (degreeZ_le_totalWeight C).trans (hw.1.trans hcT)
    have hFY:F.1.degreeOf 1≤(cofactorPair c).leftY:=by
      simpa only [cofactorPair] using
        (degreeY_le_ysWeight F.1).trans hy.le
    have hFR:F.1.degreeOf 2≤(cofactorPair c).leftR:=by
      simpa only [cofactorPair,LocatorContact.slope_weight_eq_degreeR] using hr.le
    have hFZ:F.1.degreeOf 3≤(cofactorPair c).leftZ:=by
      simpa only [cofactorPair] using (degreeZ_le_totalWeight F.1).trans hthi
    rcases hcGates with ⟨hlr,hly,hlr',hlz,hmy,hmr,hmz⟩
    have hrootC:∀ gamma∈regularSeeds H selected Gamma F,
        specialization K (selected gamma) gamma C=0:=by
      intro gamma hg
      exact hCroot gamma (by simpa only [seeds] using hg)
    have hcount:=LocatorCoprimeQuotient.regularSeeds_count_le_intersection
      (cofactorPair c) H C F hrel 2130706433
      hFY hFR hFZ
      hCY hCR hCZ hlr hly hlr' hlz hmy hmr hmz
      selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by norm_num [cofactorPair,I,IRSProfile.Index])
      (by simp [cofactorPair]) (by simp [cofactorPair])
      (by simp [cofactorPair]) (by simp [cofactorPair])
      hdegree hagreement
      (by simpa only [cofactorPair,UnequalParameters.errors,Nat.reduceSub] using hno)
      hrootC
    exact hcount.trans (Nat.le_max_right _ _)

theorem regularSeeds_count_le_source126
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181707≤((Finset.univ:Finset I).filter
      (fun i=>(selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80437)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤52091→∀ v:ConstraintKernel (K:=K) 22895082 131071 L 39 126
      IRSProfile.domain u0 u1,F.1∣reconstruct K 22895082 131071 L 39 v.1)
    (hcontact:wt (contactWeights 131071) F.1<10539006)
    (c:Cell) (hcell:InCell (regularCumulativeFlag H F) c)
    (hfit:sourceFits126 c):
    (regularSeeds H selected Gamma F).card≤sourceCost126 c:=by
  classical
  obtain ⟨hLmin,hLmax,h2t,hbands,hsmall,hcop,hqGates,hcGates,hcost⟩:=hfit
  obtain ⟨hr,hy,htlo,hthi⟩:=factor_weights_of_cell H F c hcell
  let L:=sourceLength126 c
  have hdivL:∀ v:ConstraintKernel (K:=K) 22895082 131071 L 39 126
      IRSProfile.domain u0 u1,
      F.1∣reconstruct K 22895082 131071 L 39 v.1:=hdiv L hLmax
  have hnull:
      coefficientCount 22895082 131071 L 39-
        Fintype.card I*localRankBound 126 L 39=sourceNullity126 c:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      LocatorAuxiliaryArithmetic.source126_gap_affine L hLmin]
    rfl
  have hqT:L-wt residualTotalWeights F.1≤quotientT126 c:=by
    simpa only [quotientT126,L] using
      Nat.sub_le_sub_left htlo L
  have hqY:174-wt residualYSWeights F.1=quotientY126 c:=by
    simp only [hy,quotientY126]
  have hqS:39-wt residualSWeights F.1=quotientS126 c:=by
    simp only [hr,quotientS126]
  have hcT:L-wt residualTotalWeights F.1-wt residualTotalWeights F.1≤
      cofactorT126 c:=by
    dsimp only [cofactorT126,L]
    omega
  have hcY:174-wt residualYSWeights F.1-wt residualYSWeights F.1=
      cofactorY126 c:=by simp only [hy,cofactorY126]
  have hcS:39-wt residualSWeights F.1-wt residualSWeights F.1=
      cofactorS126 c:=by simp only [hr,cofactorS126]
  have hqChannel:
      channelCount (L-wt residualTotalWeights F.1)
        (174-wt residualYSWeights F.1) (39-wt residualSWeights F.1)≤
      channelUpper (quotientT126 c) (quotientY126 c) (quotientS126 c):=
    (channelCount_mono hqT hqY.le hqS.le).trans
      (channelCount_le_channelUpper _ _ _)
  have hcChannel:
      channelCount (L-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
        (174-wt residualYSWeights F.1-wt residualYSWeights F.1)
        (39-wt residualSWeights F.1-wt residualSWeights F.1)≤
      channelUpper (cofactorT126 c) (cofactorY126 c) (cofactorS126 c):=
    (channelCount_mono hcT hcY.le hcS.le).trans
      (channelCount_le_channelUpper _ _ _)
  have hsource:
      50637*channelCount (L-wt residualTotalWeights F.1)
          (174-wt residualYSWeights F.1) (39-wt residualSWeights F.1)+
        50637*channelCount
          (L-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
          (174-wt residualYSWeights F.1-wt residualYSWeights F.1)
          (39-wt residualSWeights F.1-wt residualSWeights F.1)<
        coefficientCount 22895082 131071 L 39-
          Fintype.card I*localRankBound 126 L 39:=by
    rw [hnull]
    exact (Nat.add_le_add (Nat.mul_le_mul_left 50637 hqChannel)
      (Nat.mul_le_mul_left 50637 hcChannel)).trans_lt hbands
  have hsmallBox:
      coefficientCount 50637 131071
        (L-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
        (39-wt residualSWeights F.1-wt residualSWeights F.1)≤
      (cofactorT126 c+1)*50637:=by
    calc
      _≤coefficientCount 50637 131071 (cofactorT126 c) (cofactorS126 c):=
        coefficientCount_mono_L_s hcT hcS.le
      _=(cofactorT126 c+1)*50637:=
        LocatorAuxiliaryArithmetic.smallBox_coefficientCount _ _
  have hsourceSmall:
      50637*channelCount (L-wt residualTotalWeights F.1)
          (174-wt residualYSWeights F.1) (39-wt residualSWeights F.1)+
        coefficientCount 50637 131071
          (L-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
          (39-wt residualSWeights F.1-wt residualSWeights F.1)<
        coefficientCount 22895082 131071 L 39-
          Fintype.card I*localRankBound 126 L 39:=by
    rw [hnull]
    exact (Nat.add_le_add (Nat.mul_le_mul_left 50637 hqChannel)
      hsmallBox).trans_lt hsmall
  have hwidth:22895082-wt (contactWeights 131071) F.1≤
      22895082-50637-wt (contactWeights 131071) F.1+50637:=by omega
  have hcofactor:
      L-wt residualTotalWeights F.1-wt residualTotalWeights F.1<
          wt residualTotalWeights F.1 ∨
        174-wt residualYSWeights F.1-wt residualYSWeights F.1<
          wt residualYSWeights F.1 ∨
        39-wt residualSWeights F.1-wt residualSWeights F.1<
          wt residualSWeights F.1:=by
    rcases hcop with hT|hY|hS
    · exact Or.inl (hcT.trans_lt (hT.trans_le htlo))
    · exact Or.inr (Or.inl (by simpa only [cofactorY126,hy] using hY))
    · exact Or.inr (Or.inr (by simpa only [cofactorS126,hr] using hS))
  let seeds:=regularSeeds H selected Gamma F
  have hsub:seeds⊆Gamma:=regularSeeds_subset H selected Gamma F
  have hroot:∀ gamma∈seeds,specialization K (selected gamma) gamma F.1=0:=
    fun _ hg=>(Finset.mem_filter.mp hg).2.1
  have hregular:∀ gamma∈seeds,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2:Fin 4) F.1)≠0:=
    fun _ hg=>(Finset.mem_filter.mp hg).2.2
  have htwo:(2:K)≠0:=by
    intro hz
    have hdvd:2130706433∣2:=(CharP.cast_eq_zero_iff K 2130706433 2).mp hz
    norm_num at hdvd
  obtain hQ|hC:=exists_coprime_quotient_or_small_cofactor
    22895082 131071 L 39 126 174 50637 181707 IRSProfile.domain u0 u1
    F.1 hF (RCN167.positiveRFactors_spec H F.1 F.2).1 hdivL (by decide)
    LocatorAuxiliaryArithmetic.source126_shape hsource hsourceSmall hwidth
    LocatorAuxiliaryArithmetic.source126_capacity_one
    LocatorAuxiliaryArithmetic.source126_capacity_two hcofactor htwo
    selected seeds (fun g hg=>hdegree g (hsub hg))
    (fun g hg=>hagreement g (hsub hg)) hroot hregular
  · obtain ⟨v,Q,hv,hQne,hrel,heq,hQbox,hparent,hproduct⟩:=hQ
    have hw:=nested_mem_weights hQbox hQne
    have hQYweight:wt residualYSWeights Q≤quotientY126 c:=by
      rw [←hqY]
      exact hw.2.1
    have hQRweight:wt residualSWeights Q≤quotientS126 c:=by
      rw [←hqS]
      exact hw.2.2.1
    have hQY:Q.degreeOf 1≤(quotientPair126 c).rightY:=
      (degreeY_le_ysWeight Q).trans (by simpa only [quotientPair126] using hQYweight)
    have hQR:Q.degreeOf 2≤(quotientPair126 c).rightR:=by
      simpa only [quotientPair126,LocatorContact.slope_weight_eq_degreeR]
        using hQRweight
    have hQZ:Q.degreeOf 3≤(quotientPair126 c).rightZ:=by
      simpa only [quotientPair126] using
        (degreeZ_le_totalWeight Q).trans (hw.1.trans hqT)
    have hFY:F.1.degreeOf 1≤(quotientPair126 c).leftY:=by
      simpa only [quotientPair126] using
        (degreeY_le_ysWeight F.1).trans hy.le
    have hFR:F.1.degreeOf 2≤(quotientPair126 c).leftR:=by
      simpa only [quotientPair126,LocatorContact.slope_weight_eq_degreeR] using hr.le
    have hFZ:F.1.degreeOf 3≤(quotientPair126 c).leftZ:=by
      simpa only [quotientPair126] using (degreeZ_le_totalWeight F.1).trans hthi
    rcases hqGates with ⟨hlr,hly,hlr',hlz,hmy,hmr,hmz⟩
    have hp:∀ gamma∈regularSeeds H selected Gamma F,
        specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2:Fin 4) (F.1*Q))=0:=by
      intro gamma hg
      have hh:=hproduct gamma (by simpa only [seeds] using hg)
      rw [heq] at hh
      exact hh
    have hcount:=LocatorCoprimeQuotient.regularSeeds_count_le_intersection_of_product
      (quotientPair126 c) H Q F hrel 2130706433
      hFY hFR hFZ
      hQY hQR hQZ hlr hly hlr' hlz hmy hmr hmz
      selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by norm_num [quotientPair126,I,IRSProfile.Index])
      (by simp [quotientPair126]) (by simp [quotientPair126])
      (by simp [quotientPair126]) (by simp [quotientPair126])
      hdegree hagreement
      (by simpa only [quotientPair126,UnequalParameters.errors,Nat.reduceSub] using hno)
      hp
    exact hcount.trans (Nat.le_max_left _ _)
  · obtain ⟨v,C,hv,hCne,hrel,heq,hCbox,hparent,hCroot⟩:=hC
    have hw:=nested_mem_weights hCbox hCne
    have hCYweight:wt residualYSWeights C≤cofactorY126 c:=by
      rw [←hcY]
      exact hw.2.1
    have hCRweight:wt residualSWeights C≤cofactorS126 c:=by
      rw [←hcS]
      exact hw.2.2.1
    have hCY:C.degreeOf 1≤(cofactorPair126 c).rightY:=
      (degreeY_le_ysWeight C).trans (by simpa only [cofactorPair126] using hCYweight)
    have hCR:C.degreeOf 2≤(cofactorPair126 c).rightR:=by
      simpa only [cofactorPair126,LocatorContact.slope_weight_eq_degreeR]
        using hCRweight
    have hCZ:C.degreeOf 3≤(cofactorPair126 c).rightZ:=by
      simpa only [cofactorPair126] using
        (degreeZ_le_totalWeight C).trans (hw.1.trans hcT)
    have hFY:F.1.degreeOf 1≤(cofactorPair126 c).leftY:=by
      simpa only [cofactorPair126] using
        (degreeY_le_ysWeight F.1).trans hy.le
    have hFR:F.1.degreeOf 2≤(cofactorPair126 c).leftR:=by
      simpa only [cofactorPair126,LocatorContact.slope_weight_eq_degreeR] using hr.le
    have hFZ:F.1.degreeOf 3≤(cofactorPair126 c).leftZ:=by
      simpa only [cofactorPair126] using (degreeZ_le_totalWeight F.1).trans hthi
    rcases hcGates with ⟨hlr,hly,hlr',hlz,hmy,hmr,hmz⟩
    have hrootC:∀ gamma∈regularSeeds H selected Gamma F,
        specialization K (selected gamma) gamma C=0:=by
      intro gamma hg
      exact hCroot gamma (by simpa only [seeds] using hg)
    have hcount:=LocatorCoprimeQuotient.regularSeeds_count_le_intersection
      (cofactorPair126 c) H C F hrel 2130706433
      hFY hFR hFZ
      hCY hCR hCZ hlr hly hlr' hlz hmy hmr hmz
      selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by norm_num [cofactorPair126,I,IRSProfile.Index])
      (by simp [cofactorPair126]) (by simp [cofactorPair126])
      (by simp [cofactorPair126]) (by simp [cofactorPair126])
      hdegree hagreement
      (by simpa only [cofactorPair126,UnequalParameters.errors,Nat.reduceSub] using hno)
      hrootC
    exact hcount.trans (Nat.le_max_right _ _)
end
end ProximityPrize.SubmissionLower.LocatorQuotientReplacement
