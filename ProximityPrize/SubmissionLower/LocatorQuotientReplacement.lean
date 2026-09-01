import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
import ProximityPrize.SubmissionLower.LocatorReplacementData
import ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
import ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance
import ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance
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

section ThreeStageLowQuotient

variable {V:Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Three successive high-band cuts of a quotient map.  The first two cuts
stop as soon as the selected quotient is not divisible by `F`; if both
selected low spaces remain `F`-divisible, the third cut returns an exact
source reconstruction by `F^3 * Q3`. -/
theorem exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low
    (Dhigh Dlow w delta T YS S:ℕ)
    (hwidth:Dhigh≤Dlow+delta)
    (source q:V→ₗ[K] MvPolynomial (Fin 4) K)
    (hq:Function.Injective q)
    (F:MvPolynomial (Fin 4) K) (hF:F≠0)
    (hsource:∀ v,source v=F*q v)
    (hmem:∀ v,q v∈nestedCoefficientBox K Dhigh w T YS S)
    (hrank:
      delta*channelCount T YS S+
          delta*channelCount
            (T-wt residualTotalWeights F)
            (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F))
            (min (S-wt residualSWeights F)
              (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F)))+
          delta*channelCount
            (T-wt residualTotalWeights F-wt residualTotalWeights F)
            (min
              (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F)-
                wt residualYSWeights F)
              (T-wt residualTotalWeights F-wt residualTotalWeights F))
            (min
              (min (S-wt residualSWeights F)
                  (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F))-
                wt residualSWeights F)
              (min
                (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F)-
                  wt residualYSWeights F)
                (T-wt residualTotalWeights F-wt residualTotalWeights F)))<
        Module.finrank K V):
    (∃ v:V,v≠0∧q v≠0∧source v=F*q v∧
      q v∈nestedCoefficientBox K Dlow w T YS S∧¬F∣q v)∨
    (∃ (v:V) (Q2:MvPolynomial (Fin 4) K),
      v≠0∧Q2≠0∧source v=F*(F*Q2)∧
      Q2∈nestedCoefficientBox K
        (Dlow-delta-wt (contactWeights w) F) w
        (T-wt residualTotalWeights F)
        (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F))
        (min (S-wt residualSWeights F)
          (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F)))∧
        ¬F∣Q2)∨
    (∃ (v:V) (Q3:MvPolynomial (Fin 4) K),
      v≠0∧Q3≠0∧source v=F*(F*(F*Q3))∧
      Q3∈nestedCoefficientBox K
        (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta) w
        (T-wt residualTotalWeights F-wt residualTotalWeights F)
        (min
          (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F)-
            wt residualYSWeights F)
          (T-wt residualTotalWeights F-wt residualTotalWeights F))
        (min
          (min (S-wt residualSWeights F)
              (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F))-
            wt residualSWeights F)
          (min
            (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F)-
              wt residualYSWeights F)
            (T-wt residualTotalWeights F-wt residualTotalWeights F)))):=by
  classical
  let band1:=(highBandMap (K:=K) w Dlow delta T YS S).comp q
  let low1:=LinearMap.ker band1
  have hrange1:Module.finrank K band1.range≤delta*channelCount T YS S:=by
    calc
      Module.finrank K band1.range≤
          Module.finrank K (HighBandIndex delta T YS S→K):=
        band1.range.finrank_le
      _=delta*channelCount T YS S:=by
        rw [Module.finrank_fintype_fun_eq_card,highBandIndex_card]
  have hlowrank1:
      delta*channelCount
          (T-wt residualTotalWeights F)
          (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F))
          (min (S-wt residualSWeights F)
            (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F)))+
        delta*channelCount
          (T-wt residualTotalWeights F-wt residualTotalWeights F)
          (min
            (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F)-
              wt residualYSWeights F)
            (T-wt residualTotalWeights F-wt residualTotalWeights F))
          (min
            (min (S-wt residualSWeights F)
                (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F))-
              wt residualSWeights F)
            (min
              (min (YS-wt residualYSWeights F) (T-wt residualTotalWeights F)-
                wt residualYSWeights F)
              (T-wt residualTotalWeights F-wt residualTotalWeights F)))<
      Module.finrank K low1:=by
    have hsum:=band1.finrank_range_add_finrank_ker
    change Module.finrank K band1.range+Module.finrank K low1=
      Module.finrank K V at hsum
    omega
  let qlow1:low1→ₗ[K] MvPolynomial (Fin 4) K:=q.comp low1.subtype
  have hqlow1:Function.Injective qlow1:=by
    intro a b hab
    apply Subtype.ext
    apply hq
    simpa only [qlow1,LinearMap.comp_apply,Submodule.coe_subtype] using hab
  have hqLow1Box:∀ v:low1,qlow1 v∈nestedCoefficientBox K Dlow w T YS S:=by
    intro v
    have hhigh:=hmem v.1
    have hzero:highBandMap w Dlow delta T YS S (q v.1)=0:=by
      have hv:=v.2
      change band1 v.1=0 at hv
      simpa only [band1,qlow1,LinearMap.comp_apply,Submodule.coe_subtype] using hv
    simpa only [qlow1,LinearMap.comp_apply,Submodule.coe_subtype] using
      mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
        (q v.1) hhigh hzero
  by_cases hdiv1:∀ v:low1,F∣qlow1 v
  · let T1:=T-wt residualTotalWeights F
    let YS1:=min (YS-wt residualYSWeights F) T1
    let S1:=min (S-wt residualSWeights F) YS1
    let T2:=T1-wt residualTotalWeights F
    let YS2:=min (YS1-wt residualYSWeights F) T2
    let S2:=min (S1-wt residualSWeights F) YS2
    let q2:=quotientLinear qlow1 F hF hdiv1
    have hq2inj:Function.Injective q2:=
      quotientLinear_injective qlow1 hqlow1 F hF hdiv1
    have hq2Box:∀ v:low1,
        q2 v∈nestedCoefficientBox K
          (Dlow-wt (contactWeights w) F) w
          T1 YS1 S1:=by
      intro v
      by_cases hv:v=0
      · subst v
        rw [map_zero]
        exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
      · have hqlowv:qlow1 v≠0:=by
          intro hz
          apply hv
          apply hqlow1
          simpa only [map_zero] using hz
        have hq2v:q2 v≠0:=by
          intro hz
          apply hqlowv
          calc
            qlow1 v=F*q2 v:=recon_eq_mul_quotientPolynomial qlow1 F hdiv1 v
            _=0:=by rw [hz,mul_zero]
        have hraw:=LocatorDoubleSquareAvoidance.quotient_mem_nestedCoefficientBox_of_mul_eq
          (qlow1 v) F (q2 v) Dlow w T YS S hqlowv hF hq2v
          (hqLow1Box v) (recon_eq_mul_quotientPolynomial qlow1 F hdiv1 v)
        intro d hd
        have hb:=hraw hd
        have hT:d 1+d 2+d 3≤T1:=by simpa only [T1] using hb.1
        have hY:d 1+d 2≤YS1:=by
          apply le_min hb.2.1
          exact (Nat.le_add_right (d 1+d 2) (d 3)).trans hT
        have hS:d 2≤S1:=by
          apply le_min hb.2.2.1
          omega
        exact ⟨hT,hY,hS,hb.2.2.2⟩
    let band2:=(highBandMap (K:=K) w
      (Dlow-delta-wt (contactWeights w) F) delta
      T1 YS1 S1).comp q2
    let low2:=LinearMap.ker band2
    have hrange2:Module.finrank K band2.range≤
        delta*channelCount T1 YS1 S1:=by
      calc
        Module.finrank K band2.range≤Module.finrank K
            (HighBandIndex delta T1 YS1 S1→K):=
          band2.range.finrank_le
        _=delta*channelCount T1 YS1 S1:=by
          rw [Module.finrank_fintype_fun_eq_card,highBandIndex_card]
    have hlowrank2:
        delta*channelCount T2 YS2 S2<
        Module.finrank K low2:=by
      have hbudget:
          delta*channelCount T1 YS1 S1+
            delta*channelCount T2 YS2 S2<Module.finrank K low1:=by
        simpa only [T1,YS1,S1,T2,YS2,S2] using hlowrank1
      have hsum:=band2.finrank_range_add_finrank_ker
      change Module.finrank K band2.range+Module.finrank K low2=
        Module.finrank K low1 at hsum
      omega
    let qlow2:low2→ₗ[K] MvPolynomial (Fin 4) K:=q2.comp low2.subtype
    have hqlow2:Function.Injective qlow2:=by
      intro a b hab
      apply Subtype.ext
      apply hq2inj
      simpa only [qlow2,LinearMap.comp_apply,Submodule.coe_subtype] using hab
    have hwidth2:Dlow-wt (contactWeights w) F≤
        (Dlow-delta-wt (contactWeights w) F)+delta:=by omega
    have hqLow2Box:∀ v:low2,
        qlow2 v∈nestedCoefficientBox K
          (Dlow-delta-wt (contactWeights w) F) w
          T1 YS1 S1:=by
      intro v
      have hhigh:=hq2Box v.1
      have hzero:highBandMap w
          (Dlow-delta-wt (contactWeights w) F) delta
          T1 YS1 S1 (q2 v.1)=0:=by
        have hv:=v.2
        change band2 v.1=0 at hv
        simpa only [band2,qlow2,LinearMap.comp_apply,Submodule.coe_subtype] using hv
      simpa only [qlow2,LinearMap.comp_apply,Submodule.coe_subtype] using
        mem_low_of_highBandMap_eq_zero
          (Dlow-wt (contactWeights w) F)
          (Dlow-delta-wt (contactWeights w) F) w delta
          T1 YS1 S1 hwidth2 (q2 v.1) hhigh hzero
    by_cases hdiv2:∀ v:low2,F∣qlow2 v
    · let q3:=quotientLinear qlow2 F hF hdiv2
      have hq3inj:Function.Injective q3:=
        quotientLinear_injective qlow2 hqlow2 F hF hdiv2
      have hq3Box:∀ v:low2,
          q3 v∈nestedCoefficientBox K
            (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F) w
            T2 YS2 S2:=by
        intro v
        by_cases hv:v=0
        · subst v
          rw [map_zero]
          exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
        · have hqlowv:qlow2 v≠0:=by
            intro hz
            apply hv
            apply hqlow2
            simpa only [map_zero] using hz
          have hq3v:q3 v≠0:=by
            intro hz
            apply hqlowv
            calc
              qlow2 v=F*q3 v:=recon_eq_mul_quotientPolynomial qlow2 F hdiv2 v
              _=0:=by rw [hz,mul_zero]
          have hraw:=LocatorDoubleSquareAvoidance.quotient_mem_nestedCoefficientBox_of_mul_eq
            (qlow2 v) F (q3 v)
            (Dlow-delta-wt (contactWeights w) F) w
            T1 YS1 S1 hqlowv hF hq3v (hqLow2Box v)
            (recon_eq_mul_quotientPolynomial qlow2 F hdiv2 v)
          intro d hd
          have hb:=hraw hd
          have hT:d 1+d 2+d 3≤T2:=by simpa only [T2] using hb.1
          have hY:d 1+d 2≤YS2:=by
            apply le_min hb.2.1
            exact (Nat.le_add_right (d 1+d 2) (d 3)).trans hT
          have hS:d 2≤S2:=by
            apply le_min hb.2.2.1
            omega
          exact ⟨hT,hY,hS,hb.2.2.2⟩
      have hwidth3:
          Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F≤
          (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta)+
            delta:=by omega
      obtain ⟨v,hv,hQ3,hQ3box⟩:=exists_nonzero_image_mem_low
        (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F)
        (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta)
        w delta T2 YS2 S2
        hwidth3 q3 hq3inj hq3Box hlowrank2
      have hvV:v.1.1≠0:=by
        intro hz
        apply hv
        apply Subtype.ext
        apply Subtype.ext
        exact hz
      have hq2eq:F*q2 v.1= q v.1.1:=by
        change F*quotientPolynomial qlow1 F hdiv1 v.1=q v.1.1
        simpa only [qlow1,LinearMap.comp_apply,Submodule.coe_subtype] using
          (recon_eq_mul_quotientPolynomial qlow1 F hdiv1 v.1).symm
      have hq3eq:F*q3 v= q2 v.1:=by
        change F*quotientPolynomial qlow2 F hdiv2 v=
          quotientPolynomial qlow1 F hdiv1 v.1
        calc
          F*quotientPolynomial qlow2 F hdiv2 v=q2 v.1:=by
            simpa only [qlow2,LinearMap.comp_apply,Submodule.coe_subtype] using
              (recon_eq_mul_quotientPolynomial qlow2 F hdiv2 v).symm
          _=quotientPolynomial qlow1 F hdiv1 v.1:=by rfl
      right
      right
      refine ⟨v.1.1,q3 v,hvV,hQ3,?_,?_⟩
      calc
        source v.1.1=F*q v.1.1:=hsource v.1.1
        _=F*(F*q2 v.1):=congrArg (fun W=>F*W) hq2eq.symm
        _=F*(F*(F*q3 v)):=congrArg (fun W=>F*(F*W)) hq3eq.symm
      simpa only [T1,YS1,S1,T2,YS2,S2] using hQ3box
    · push Not at hdiv2
      obtain ⟨v,hvdiv⟩:=hdiv2
      have hQ2:qlow2 v≠0:=by
        intro hz
        apply hvdiv
        rw [hz]
        exact dvd_zero F
      have hvV:v.1.1≠0:=by
        intro hz
        have hv0:v=0:=by
          apply Subtype.ext
          apply Subtype.ext
          exact hz
        exact hQ2 (by rw [hv0,map_zero])
      have hq2eq:F*q2 v.1=q v.1.1:=by
        change F*quotientPolynomial qlow1 F hdiv1 v.1=q v.1.1
        simpa only [qlow1,LinearMap.comp_apply,Submodule.coe_subtype] using
          (recon_eq_mul_quotientPolynomial qlow1 F hdiv1 v.1).symm
      right
      left
      refine ⟨v.1.1,qlow2 v,hvV,hQ2,?_,?_,hvdiv⟩
      calc
        source v.1.1=F*q v.1.1:=hsource v.1.1
        _=F*(F*q2 v.1):=congrArg (fun W=>F*W) hq2eq.symm
        _=F*(F*qlow2 v):=by rfl
      simpa only [T1,YS1,S1] using hqLow2Box v
  · push Not at hdiv1
    obtain ⟨v,hvdiv⟩:=hdiv1
    have hv:v.1≠0:=by
      intro hz
      apply hvdiv
      have hvzero:v=0:=Subtype.ext hz
      rw [hvzero]
      simp only [map_zero]
      exact dvd_zero F
    have hqv:q v.1≠0:=by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    left
    refine ⟨v.1,hv,hqv,hsource v.1,?_,?_⟩
    · simpa only [qlow1,LinearMap.comp_apply,Submodule.coe_subtype] using hqLow1Box v
    · simpa only [qlow1,LinearMap.comp_apply,Submodule.coe_subtype] using hvdiv

end ThreeStageLowQuotient

/-- Exact score-67.67 C126 third-contact budget. -/
theorem c126_third_capacity_exact:
    22896342-3*50647=(126-3)*181717+3*(131071-1)∧
      22896342-3*50647=22744401:=by norm_num

/-- Consumer-neutral score-67.67 C126 bridge from an exact cubic
reconstruction to quotient vanishing at a regular seed. -/
theorem c126_third_cube_quotient_vanish
    (L:ℕ) (nodes:I↪K) (u0 u1:I→K)
    (v:ConstraintKernel (K:=K) 22896342 131071 L 39 126 nodes u0 u1)
    (hlow:reconstruct K 22896342 131071 L 39 v.1∈
      globalCoefficientBox K 22744401 131071 L 39)
    (P:Polynomial K) (gamma:K) (support:Finset I)
    (hP:P.natDegree≤131071) (hcard:181717≤support.card)
    (hvalues:∀ i∈support,P.eval (nodes i)=u0 i+gamma*u1 i)
    (F Q3:P4)
    (hcube:reconstruct K 22896342 131071 L 39 v.1=F*(F*(F*Q3)))
    (hFzero:RCN319.specialization K P gamma F=0)
    (hregular:RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2:Fin 4) F)≠0):
    RCN319.specialization K P gamma Q3=0:=by
  have hcapacity:22744401≤
      (126-3)*support.card+3*(131071-1):=by
    have hexact:=c126_third_capacity_exact
    omega
  have hsix:(6:K)≠0:=by
    intro hz
    have hdvd:2130706433∣6:=
      (CharP.cast_eq_zero_iff K 2130706433 6).mp hz
    norm_num at hdvd
  exact LocatorTripleCubeAvoidance.specialization_eq_zero_of_kernel_low_box_cube_product
    22896342 22744401 131071 L 39 126 nodes u0 u1 v hlow
    P gamma support (by decide) hP hcapacity hvalues F Q3 hsix hcube
      hFzero hregular

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
      (fun i=>(selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80427)
    (F:RegularIndex H) (hF:F.1≠0)
    (hdiv:∀ L,L≤52091→∀ v:ConstraintKernel (K:=K) 22896342 131071 L 39 126
      IRSProfile.domain u0 u1,F.1∣reconstruct K 22896342 131071 L 39 v.1)
    (c:Cell) (hcell:InCell (regularCumulativeFlag H F) c)
    (hfit:Triple126Fits c):
    (regularSeeds H selected Gamma F).card≤tripleCost c:=by
  classical
  obtain ⟨hr,hylo,hyhi,htlo,hthi,_hc⟩:=factor_weights_of_cell H F c hcell
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
      rw [←hprod v] at hmul
      simp only [wt] at hsrc ⊢
      omega
  have hqNested:∀ v:ConstraintKernel (K:=K) 22896342 131071
      (lengthTriple126 c) 39 126 IRSProfile.domain u0 u1,
      q v∈nestedCoefficientBox K
        (22896342-wt (contactWeights 131071) F.1) 131071
        (firstTripleT c) (firstTripleYS c) (firstTripleS c):=by
    intro v d hd
    have hb:=hqbox v hd
    have hy:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans (hqYS v)
    rw [weight_fin4] at hy
    have hy':d 1+d 2≤174-wt residualYSWeights F.1:=by
      simpa [residualYSWeights] using hy
    have hT:d 1+d 2+d 3≤firstTripleT c:=by
      apply hb.1.trans
      simpa only [firstTripleT] using
        Nat.sub_le_sub_left htlo (lengthTriple126 c)
    have hY:d 1+d 2≤firstTripleYS c:=by
      apply le_min
      · exact hy'.trans (Nat.sub_le_sub_left hylo 174)
      · exact (Nat.le_add_right (d 1+d 2) (d 3)).trans hT
    have hS:d 2≤firstTripleS c:=by
      apply le_min
      · simpa only [hr] using hb.2.1
      · omega
    exact ⟨hT,hY,hS,hb.2.2⟩
  have hT2:firstTripleT c-wt residualTotalWeights F.1≤secondTripleT c:=by
    dsimp [firstTripleT,secondTripleT]
    omega
  have hY2:min (firstTripleYS c-wt residualYSWeights F.1)
      (firstTripleT c-wt residualTotalWeights F.1)≤secondTripleYS c:=by
    dsimp [secondTripleYS]
    apply le_min
    · calc
        _≤firstTripleYS c-wt residualYSWeights F.1:=Nat.min_le_left _ _
        _≤(174-ylo c)-wt residualYSWeights F.1:=by
          apply Nat.sub_le_sub_right
          exact Nat.min_le_left _ _
        _≤174-2*ylo c:=by omega
    · exact (Nat.min_le_right _ _).trans hT2
  have hS2:min (firstTripleS c-wt residualSWeights F.1)
      (min (firstTripleYS c-wt residualYSWeights F.1)
        (firstTripleT c-wt residualTotalWeights F.1))≤secondTripleS c:=by
    dsimp [secondTripleS]
    apply le_min
    · calc
        _≤firstTripleS c-wt residualSWeights F.1:=Nat.min_le_left _ _
        _≤(39-r c)-wt residualSWeights F.1:=by
          apply Nat.sub_le_sub_right
          exact Nat.min_le_left _ _
        _≤39-2*r c:=by omega
    · exact (Nat.min_le_right _ _).trans hY2
  have hT3:firstTripleT c-wt residualTotalWeights F.1-
      wt residualTotalWeights F.1≤thirdTripleT c:=by
    dsimp [firstTripleT,thirdTripleT]
    omega
  have hY3:min
      (min (firstTripleYS c-wt residualYSWeights F.1)
          (firstTripleT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
      (firstTripleT c-wt residualTotalWeights F.1-
        wt residualTotalWeights F.1)≤thirdTripleYS c:=by
    dsimp [thirdTripleYS]
    apply le_min
    · calc
        _≤firstTripleYS c-wt residualYSWeights F.1-
            wt residualYSWeights F.1:=by
              exact (Nat.min_le_left _ _).trans (Nat.sub_le_sub_right
                (Nat.min_le_left _ _) _)
        _≤(174-ylo c)-wt residualYSWeights F.1-
            wt residualYSWeights F.1:=by
              apply Nat.sub_le_sub_right
              apply Nat.sub_le_sub_right
              exact Nat.min_le_left _ _
        _≤174-3*ylo c:=by omega
    · exact (Nat.min_le_right _ _).trans hT3
  have hS3:min
      (min (firstTripleS c-wt residualSWeights F.1)
          (min (firstTripleYS c-wt residualYSWeights F.1)
            (firstTripleT c-wt residualTotalWeights F.1))-wt residualSWeights F.1)
      (min
        (min (firstTripleYS c-wt residualYSWeights F.1)
            (firstTripleT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
        (firstTripleT c-wt residualTotalWeights F.1-
          wt residualTotalWeights F.1))≤thirdTripleS c:=by
    dsimp [thirdTripleS]
    apply le_min
    · calc
        _≤firstTripleS c-wt residualSWeights F.1-
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
  have hchannels1:channelCount (firstTripleT c) (firstTripleYS c)
      (firstTripleS c)≤channelCount (firstTripleT c) (firstTripleYS c)
        (firstTripleS c):=le_rfl
  have hchannels2:=channelCount_mono hT2 hY2 hS2
  have hchannels3:=channelCount_mono hT3 hY3 hS3
  have hsourceCoeff:
      50647*channelCount (firstTripleT c) (firstTripleYS c) (firstTripleS c)+
        50647*channelCount
          (firstTripleT c-wt residualTotalWeights F.1)
          (min (firstTripleYS c-wt residualYSWeights F.1)
            (firstTripleT c-wt residualTotalWeights F.1))
          (min (firstTripleS c-wt residualSWeights F.1)
            (min (firstTripleYS c-wt residualYSWeights F.1)
              (firstTripleT c-wt residualTotalWeights F.1)))+
        50647*channelCount
          (firstTripleT c-wt residualTotalWeights F.1-wt residualTotalWeights F.1)
          (min
            (min (firstTripleYS c-wt residualYSWeights F.1)
                (firstTripleT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
            (firstTripleT c-wt residualTotalWeights F.1-wt residualTotalWeights F.1))
          (min
            (min (firstTripleS c-wt residualSWeights F.1)
                (min (firstTripleYS c-wt residualYSWeights F.1)
                  (firstTripleT c-wt residualTotalWeights F.1))-wt residualSWeights F.1)
            (min
              (min (firstTripleYS c-wt residualYSWeights F.1)
                  (firstTripleT c-wt residualTotalWeights F.1)-wt residualYSWeights F.1)
              (firstTripleT c-wt residualTotalWeights F.1-wt residualTotalWeights F.1)))<
      coefficientCount 22896342 131071 (lengthTriple126 c) 39-
        Fintype.card I*localRankBound 126 (lengthTriple126 c) 39:=by
    rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      auxiliary126_gap_affine (lengthTriple126 c) hfit.1]
    have hbands:=Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left 50647 hchannels1)
      (Nat.mul_le_mul_left 50647 hchannels2))
      (Nat.mul_le_mul_left 50647 hchannels3)
    exact hbands.trans_lt (by
      simpa only [bandTripleFirst,bandTripleSecond,bandTripleThird,
        sourceGapTriple126] using hfit.2.2.1)
  have hsourceRank:=hsourceCoeff.trans_le
    (constraintKernel_finrank_lower_bound 22896342 131071
      (lengthTriple126 c) 39 126 IRSProfile.domain u0 u1)
  have hwidth:22896342-wt (contactWeights 131071) F.1≤
      (22896342-50647-wt (contactWeights 131071) F.1)+50647:=by omega
  rcases exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low
      (22896342-wt (contactWeights 131071) F.1)
      (22896342-50647-wt (contactWeights 131071) F.1)
      131071 50647 (firstTripleT c) (firstTripleYS c) (firstTripleS c)
      hwidth recon q hqinj F.1 hF hprod hqNested hsourceRank with
    hfirst|hsecond|hthird
  · obtain ⟨v,hv,hQ,heq,hQbox,hnot⟩:=hfirst
    have hrel:IsRelPrime F.1 (q v):=
      (RCN167.positiveRFactors_spec H F.1 F.2).1.isRelPrime_iff_not_dvd.mpr hnot
    have hwQ:=nested_mem_weights hQbox hQ
    have hlow:reconstruct K 22896342 131071 (lengthTriple126 c) 39 v.1∈
        globalCoefficientBox K (22896342-50647) 131071
          (lengthTriple126 c) 39:=by
      change recon v∈globalCoefficientBox K (22896342-50647) 131071
        (lengthTriple126 c) 39
      rw [heq]
      have hsrc:F.1*q v∈globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39:=by
        rw [←heq]
        change reconstruct K 22896342 131071 (lengthTriple126 c) 39 v.1∈_
        exact reconstruct_mem_globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39 v.1
      have hc:=(mem_flagGlobalCoefficientBox_iff (F.1*q v) 22896342
        131071 (lengthTriple126 c) 39 (by decide)).mp hsrc
      have hqc:=hwQ.2.2.2
      have hmul:=weightedTotalDegree_mul (contactWeights 131071) F.1 (q v) hF hQ
      apply (mem_flagGlobalCoefficientBox_iff (F.1*q v) (22896342-50647)
        131071 (lengthTriple126 c) 39 (by decide)).mpr
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
      have hcard:181717≤support.card:=hagreement gamma hg
      have hcap:22896342-50647≤(126-1)*support.card+(131071-1):=
        auxiliary126_capacity.trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left (126-1) hcard) _)
      have hvalues:∀ i∈support,(selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i:=fun i hi=>(Finset.mem_filter.mp hi).2
      rw [←heq]
      exact specialization_pderiv_R_eq_zero_of_kernel_low_box
        22896342 (22896342-50647) 131071 (lengthTriple126 c) 39 126
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (by decide) (hdegree gamma hg) hcap hvalues
    rcases hfit.2.2.2.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
      hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hcount:=regularSeeds_count_le_intersection_of_product
      (pairTripleFirst c) H (q v) F hrel 2130706433
      ((degreeY_le_ysWeight F.1).trans hyhi)
      (by simpa only [pairTripleFirst,LocatorContact.slope_weight_eq_degreeR]
        using hr.le)
      ((degreeZ_le_totalWeight F.1).trans hthi)
      ((degreeY_le_ysWeight (q v)).trans hwQ.2.1)
      (by simpa only [pairTripleFirst,LocatorContact.slope_weight_eq_degreeR]
        using hwQ.2.2.1)
      ((degreeZ_le_totalWeight (q v)).trans hwQ.1)
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by change (Finset.univ:Finset I).card=262144
          rw [Finset.card_univ];norm_num [I,IRSProfile.Index])
      (by simpa only [pairTripleFirst] using (show 1≤131071 by decide))
      (by simpa only [pairTripleFirst] using (show 131071<2130706433 by decide))
      (by simpa only [pairTripleFirst] using (show 131071<181717 by decide))
      (by simpa only [pairTripleFirst] using (show 181717≤262144 by decide))
      hdegree hagreement
      (by simpa only [pairTripleFirst,UnequalParameters.errors,Nat.reduceSub] using hno)
      hproduct
    exact hcount.trans (by simp only [tripleCost];exact Nat.le_max_left _ _)
  · obtain ⟨v,Q2,hv,hQ,heq,hQbox,hnot⟩:=hsecond
    have hrel:IsRelPrime F.1 Q2:=
      (RCN167.positiveRFactors_spec H F.1 F.2).1.isRelPrime_iff_not_dvd.mpr hnot
    have hwQ:=nested_mem_weights hQbox hQ
    have hlow:reconstruct K 22896342 131071 (lengthTriple126 c) 39 v.1∈
        globalCoefficientBox K (22896342-2*50647) 131071
          (lengthTriple126 c) 39:=by
      change recon v∈globalCoefficientBox K (22896342-2*50647) 131071
        (lengthTriple126 c) 39
      rw [heq]
      have hsrc:F.1*(F.1*Q2)∈globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39:=by
        rw [←heq]
        change reconstruct K 22896342 131071 (lengthTriple126 c) 39 v.1∈_
        exact reconstruct_mem_globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39 v.1
      have hc:=(mem_flagGlobalCoefficientBox_iff (F.1*(F.1*Q2)) 22896342
        131071 (lengthTriple126 c) 39 (by decide)).mp hsrc
      have hqc:=hwQ.2.2.2
      have hm1:=weightedTotalDegree_mul (contactWeights 131071) F.1 Q2 hF hQ
      have hm2:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*Q2) hF (mul_ne_zero hF hQ)
      apply (mem_flagGlobalCoefficientBox_iff (F.1*(F.1*Q2))
        (22896342-2*50647) 131071 (lengthTriple126 c) 39 (by decide)).mpr
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
      have hcard:181717≤support.card:=hagreement gamma hg
      have hcap:22896342-2*50647≤(126-2)*support.card+2*(131071-1):=
        auxiliary126_double_capacity.trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left (126-2) hcard) _)
      have hvalues:∀ i∈support,(selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i:=fun i hi=>(Finset.mem_filter.mp hi).2
      have hderiv:RCN319.specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2:Fin 4)
            (MvPolynomial.pderiv (2:Fin 4) (F.1*(F.1*Q2))))=0:=by
        rw [←heq]
        exact LocatorDoubleSquareAvoidance.specialization_pderiv_R2_eq_zero_of_kernel_low_box
          22896342 (22896342-2*50647) 131071 (lengthTriple126 c) 39 126
          IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
          (by decide) (hdegree gamma hg) hcap hvalues
      obtain ⟨hFzero,hregular⟩:=(Finset.mem_filter.mp hgamma).2
      exact LocatorDoubleSquareAvoidance.specialization_eq_zero_of_pderiv_R2_square_product
        (selected gamma) gamma F.1 Q2 htwo hFzero hregular hderiv
    rcases hfit.2.2.2.2.2.1 with ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
      hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hcount:=regularSeeds_count_le_intersection
      (pairTripleSecond c) H Q2 F hrel 2130706433
      ((degreeY_le_ysWeight F.1).trans hyhi)
      (by simpa only [pairTripleSecond,LocatorContact.slope_weight_eq_degreeR]
        using hr.le)
      ((degreeZ_le_totalWeight F.1).trans hthi)
      ((degreeY_le_ysWeight Q2).trans (hwQ.2.1.trans hY2))
      (by simpa only [pairTripleSecond,LocatorContact.slope_weight_eq_degreeR]
        using hwQ.2.2.1.trans hS2)
      ((degreeZ_le_totalWeight Q2).trans (hwQ.1.trans hT2))
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
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
      exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  · obtain ⟨v,Q3,hv,hQ,heq,hQbox⟩:=hthird
    have hwQ:=nested_mem_weights hQbox hQ
    have hrel:IsRelPrime F.1 Q3:=by
      have hirr:=(RCN167.positiveRFactors_spec H F.1 F.2).1
      rcases hfit.2.2.2.1 with hT|hY|hR
      · apply isRelPrime_of_weight_lt residualTotalWeights F.1 Q3 hirr hQ
        exact (hwQ.1.trans hT3).trans_lt (hT.trans_le htlo)
      · apply isRelPrime_of_weight_lt residualYSWeights F.1 Q3 hirr hQ
        exact (hwQ.2.1.trans hY3).trans_lt (hY.trans_le hylo)
      · apply isRelPrime_of_weight_lt residualSWeights F.1 Q3 hirr hQ
        rw [hr]
        exact (hwQ.2.2.1.trans hS3).trans_lt hR
    have hlow:reconstruct K 22896342 131071 (lengthTriple126 c) 39 v.1∈
        globalCoefficientBox K 22744401 131071 (lengthTriple126 c) 39:=by
      change recon v∈globalCoefficientBox K 22744401 131071
        (lengthTriple126 c) 39
      rw [heq]
      have hsrc:F.1*(F.1*(F.1*Q3))∈globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39:=by
        rw [←heq]
        change reconstruct K 22896342 131071 (lengthTriple126 c) 39 v.1∈_
        exact reconstruct_mem_globalCoefficientBox K 22896342 131071
          (lengthTriple126 c) 39 v.1
      have hc:=(mem_flagGlobalCoefficientBox_iff (F.1*(F.1*(F.1*Q3)))
        22896342 131071 (lengthTriple126 c) 39 (by decide)).mp hsrc
      have hqc:=hwQ.2.2.2
      have hm1:=weightedTotalDegree_mul (contactWeights 131071) F.1 Q3 hF hQ
      have hm2:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*Q3) hF (mul_ne_zero hF hQ)
      have hm3:=weightedTotalDegree_mul (contactWeights 131071) F.1
        (F.1*(F.1*Q3)) hF (mul_ne_zero hF (mul_ne_zero hF hQ))
      apply (mem_flagGlobalCoefficientBox_iff (F.1*(F.1*(F.1*Q3)))
        22744401 131071 (lengthTriple126 c) 39 (by decide)).mpr
      refine ⟨hc.1,hc.2.1,?_⟩
      simp only [wt] at hqc hm1 hm2 hm3 ⊢
      have hexact:=c126_third_capacity_exact.2
      omega
    have hQzero:∀ gamma∈regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma Q3=0:=by
      intro gamma hgamma
      have hg:gamma∈Gamma:=(Finset.mem_filter.mp hgamma).1
      let support:=(Finset.univ:Finset I).filter (fun i=>(selected gamma).eval
        (IRSProfile.domain i)=u0 i+gamma*u1 i)
      have hcard:181717≤support.card:=hagreement gamma hg
      have hvalues:∀ i∈support,(selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i:=fun i hi=>(Finset.mem_filter.mp hi).2
      obtain ⟨hFzero,hregular⟩:=(Finset.mem_filter.mp hgamma).2
      apply c126_third_cube_quotient_vanish (lengthTriple126 c)
        IRSProfile.domain u0 u1 v hlow (selected gamma) gamma support
        (hdegree gamma hg) hcard hvalues F.1 Q3
      · simpa only [recon,kernelReconstructLinear_apply] using heq
      · exact hFzero
      · exact hregular
    rcases hfit.2.2.2.2.2.2.1 with
      ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
        hmixedYSmall,hmixedRSmall,hmixedZSmall⟩
    have hcount:=regularSeeds_count_le_intersection
      (pairTripleThird c) H Q3 F hrel 2130706433
      ((degreeY_le_ysWeight F.1).trans hyhi)
      (by simpa only [pairTripleThird,LocatorContact.slope_weight_eq_degreeR]
        using hr.le)
      ((degreeZ_le_totalWeight F.1).trans hthi)
      ((degreeY_le_ysWeight Q3).trans (hwQ.2.1.trans hY3))
      (by simpa only [pairTripleThird,LocatorContact.slope_weight_eq_degreeR]
        using hwQ.2.2.1.trans hS3)
      ((degreeZ_le_totalWeight Q3).trans (hwQ.1.trans hT3))
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
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
      exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

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
    (hbad:LocatorFactorReplacement.Bad 2445 131072 131073 271673448487290497
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
      (regularCumulativeFlag H F) 2445 (yhi c)
      (r c) 271673448487290497
      hrpos hcell.all_eq hcell.middle_le_yhi
      ((yhi_le_76 c).trans (by decide))
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
  have htail:Double126Fits c∨Triple126Fits c:=hroutes'.resolve_left h126
  by_cases hdouble:Double126Fits c
  · have h:=double126_count u0 u1 H selected Gamma hdegree hagreement hno F hF
      hdiv126 c hcell hdouble
    simpa only [chosenCost,if_neg ho,if_neg h72,if_neg h126,if_pos hdouble] using h
  · have htriple:Triple126Fits c:=htail.resolve_left hdouble
    have h:=triple126_count u0 u1 H selected Gamma hdegree hagreement hno F hF
      hdiv126 c hcell htriple
    simpa only [chosenCost,if_neg ho,if_neg h72,if_neg h126,if_neg hdouble] using h
end
end LocatorQuotientReplacement
