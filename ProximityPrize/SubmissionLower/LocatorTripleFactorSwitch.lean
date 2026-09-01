import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
import ProximityPrize.SubmissionLower.LocatorLowQuotient
import ProximityPrize.SubmissionLower.LocatorFactorAggregate
import ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance
import ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance
import ProximityPrize.SubmissionLower.LocatorQuarticFourthAvoidance
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
import ProximityPrize.SubmissionLower.BF

namespace ProximityPrize.SubmissionLower.LocatorTripleFactorSwitch

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN266
open RCN260 LocatorFactorAggregate LocatorLowQuotient LocatorCoprimeQuotient

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
section FourStageLowQuotient

variable {V:Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private def nextT (T:ℕ) (F:P4):ℕ:=T-wt residualTotalWeights F
private def nextYS (T YS:ℕ) (F:P4):ℕ:=
  min (YS-wt residualYSWeights F) (nextT T F)
private def nextS (T YS S:ℕ) (F:P4):ℕ:=
  min (S-wt residualSWeights F) (nextYS T YS F)

/-- Four successive high-band cuts of a quotient map.  The first three cuts
stop as soon as the selected quotient is not divisible by `F`; if all three
selected low spaces remain `F`-divisible, the fourth cut returns an exact
source reconstruction by `F^4 * Q4`. -/
theorem exists_first_or_second_or_third_not_dvd_or_fourth_low
    (Dhigh Dlow w delta T YS S:ℕ)
    (hwidth:Dhigh≤Dlow+delta)
    (source q:V→ₗ[K] MvPolynomial (Fin 4) K)
    (hq:Function.Injective q)
    (F:MvPolynomial (Fin 4) K) (hF:F≠0)
    (hsource:∀ v,source v=F*q v)
    (hmem:∀ v,q v∈nestedCoefficientBox K Dhigh w T YS S)
    (hrank:
      delta*channelCount T YS S+
        delta*channelCount (nextT T F) (nextYS T YS F) (nextS T YS S F)+
        delta*channelCount (nextT (nextT T F) F)
          (nextYS (nextT T F) (nextYS T YS F) F)
          (nextS (nextT T F) (nextYS T YS F) (nextS T YS S F) F)+
        delta*channelCount (nextT (nextT (nextT T F) F) F)
          (nextYS (nextT (nextT T F) F)
            (nextYS (nextT T F) (nextYS T YS F) F) F)
          (nextS (nextT (nextT T F) F)
            (nextYS (nextT T F) (nextYS T YS F) F)
            (nextS (nextT T F) (nextYS T YS F) (nextS T YS S F) F) F)<
        Module.finrank K V):
    (∃ v:V,v≠0∧q v≠0∧source v=F*q v∧
      q v∈nestedCoefficientBox K Dlow w T YS S∧¬F∣q v)∨
    (∃ (v:V) (Q2:MvPolynomial (Fin 4) K),
      v≠0∧Q2≠0∧source v=F*(F*Q2)∧
      Q2∈nestedCoefficientBox K
        (Dlow-delta-wt (contactWeights w) F) w
        (nextT T F) (nextYS T YS F) (nextS T YS S F)∧
        ¬F∣Q2)∨
    (∃ (v:V) (Q3:MvPolynomial (Fin 4) K),
      v≠0∧Q3≠0∧source v=F*(F*(F*Q3))∧
      Q3∈nestedCoefficientBox K
        (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta) w
        (nextT (nextT T F) F)
        (nextYS (nextT T F) (nextYS T YS F) F)
        (nextS (nextT T F) (nextYS T YS F) (nextS T YS S F) F)∧
        ¬F∣Q3)∨
    (∃ (v:V) (Q4:MvPolynomial (Fin 4) K),
      v≠0∧Q4≠0∧source v=F*(F*(F*(F*Q4)))∧
      Q4∈nestedCoefficientBox K
        (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta-
          wt (contactWeights w) F-delta) w
        (nextT (nextT (nextT T F) F) F)
        (nextYS (nextT (nextT T F) F)
          (nextYS (nextT T F) (nextYS T YS F) F) F)
        (nextS (nextT (nextT T F) F)
          (nextYS (nextT T F) (nextYS T YS F) F)
          (nextS (nextT T F) (nextYS T YS F) (nextS T YS S F) F) F)):=by
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
      delta*channelCount (nextT T F) (nextYS T YS F) (nextS T YS S F)+
        delta*channelCount (nextT (nextT T F) F)
          (nextYS (nextT T F) (nextYS T YS F) F)
          (nextS (nextT T F) (nextYS T YS F) (nextS T YS S F) F)+
        delta*channelCount (nextT (nextT (nextT T F) F) F)
          (nextYS (nextT (nextT T F) F)
            (nextYS (nextT T F) (nextYS T YS F) F) F)
          (nextS (nextT (nextT T F) F)
            (nextYS (nextT T F) (nextYS T YS F) F)
            (nextS (nextT T F) (nextYS T YS F) (nextS T YS S F) F) F)<
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
    let T3:=T2-wt residualTotalWeights F
    let YS3:=min (YS2-wt residualYSWeights F) T3
    let S3:=min (S2-wt residualSWeights F) YS3
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
        delta*channelCount T2 YS2 S2+
          delta*channelCount T3 YS3 S3<
        Module.finrank K low2:=by
      have hbudget:
          delta*channelCount T1 YS1 S1+
            delta*channelCount T2 YS2 S2+
            delta*channelCount T3 YS3 S3<Module.finrank K low1:=by
        simpa only [T1,YS1,S1,T2,YS2,S2,T3,YS3,S3,
          nextT,nextYS,nextS] using hlowrank1
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
      let band3:=(highBandMap (K:=K) w
        (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta)
        delta T2 YS2 S2).comp q3
      let low3:=LinearMap.ker band3
      have hrange3:Module.finrank K band3.range≤
          delta*channelCount T2 YS2 S2:=by
        calc
          Module.finrank K band3.range≤Module.finrank K
              (HighBandIndex delta T2 YS2 S2→K):=band3.range.finrank_le
          _=delta*channelCount T2 YS2 S2:=by
            rw [Module.finrank_fintype_fun_eq_card,highBandIndex_card]
      have hlowrank3:delta*channelCount T3 YS3 S3<
          Module.finrank K low3:=by
        have hsum:=band3.finrank_range_add_finrank_ker
        change Module.finrank K band3.range+Module.finrank K low3=
          Module.finrank K low2 at hsum
        omega
      let qlow3:low3→ₗ[K] MvPolynomial (Fin 4) K:=q3.comp low3.subtype
      have hqlow3:Function.Injective qlow3:=by
        intro a b hab
        apply Subtype.ext
        apply hq3inj
        simpa only [qlow3,LinearMap.comp_apply,Submodule.coe_subtype] using hab
      have hwidth3:
          Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F≤
          (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta)+
            delta:=by omega
      have hqLow3Box:∀ v:low3,qlow3 v∈nestedCoefficientBox K
          (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta) w
          T2 YS2 S2:=by
        intro v
        have hhigh:=hq3Box v.1
        have hzero:highBandMap w
            (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta)
            delta T2 YS2 S2 (q3 v.1)=0:=by
          have hv:=v.2
          change band3 v.1=0 at hv
          simpa only [band3,qlow3,LinearMap.comp_apply,Submodule.coe_subtype] using hv
        simpa only [qlow3,LinearMap.comp_apply,Submodule.coe_subtype] using
          mem_low_of_highBandMap_eq_zero
            (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F)
            (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta)
            w delta T2 YS2 S2 hwidth3 (q3 v.1) hhigh hzero
      by_cases hdiv3:∀ v:low3,F∣qlow3 v
      · let q4:low3→ₗ[K] MvPolynomial (Fin 4) K:=
          quotientLinear (V:=low3) qlow3 F hF hdiv3
        have hq4inj:Function.Injective q4:=by
          simpa only [q4] using
            (quotientLinear_injective (V:=low3) qlow3 hqlow3 F hF hdiv3)
        have hq4Box:∀ v:low3,q4 v∈nestedCoefficientBox K
            (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta-
              wt (contactWeights w) F) w T3 YS3 S3:=by
          intro v
          by_cases hv:v=0
          · subst v
            rw [map_zero]
            exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
          · have hqlowv:qlow3 v≠0:=by
              intro hz
              apply hv
              apply hqlow3
              simpa only [map_zero] using hz
            have hq4v:q4 v≠0:=by
              intro hz
              apply hqlowv
              calc
                qlow3 v=F*q4 v:=recon_eq_mul_quotientPolynomial qlow3 F hdiv3 v
                _=0:=by rw [hz,mul_zero]
            have hraw:=
              LocatorDoubleSquareAvoidance.quotient_mem_nestedCoefficientBox_of_mul_eq
                (qlow3 v) F (q4 v)
                (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta)
                w T2 YS2 S2 hqlowv hF hq4v (hqLow3Box v)
                (recon_eq_mul_quotientPolynomial qlow3 F hdiv3 v)
            intro d hd
            have hb:=hraw hd
            have hT:d 1+d 2+d 3≤T3:=by simpa only [T3] using hb.1
            have hY:d 1+d 2≤YS3:=by
              apply le_min hb.2.1
              exact (Nat.le_add_right (d 1+d 2) (d 3)).trans hT
            have hS:d 2≤S3:=by
              apply le_min hb.2.2.1
              omega
            exact ⟨hT,hY,hS,hb.2.2.2⟩
        have hwidth4:
            Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta-
                wt (contactWeights w) F≤
              (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta-
                wt (contactWeights w) F-delta)+delta:=by omega
        obtain ⟨v,hv,hQ4,hQ4box⟩:=exists_nonzero_image_mem_low (K:=K) (V:=low3)
          (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta-
            wt (contactWeights w) F)
          (Dlow-delta-wt (contactWeights w) F-wt (contactWeights w) F-delta-
            wt (contactWeights w) F-delta)
          w delta T3 YS3 S3 hwidth4 q4 hq4inj hq4Box hlowrank3
        have hvV:v.1.1.1≠0:=by
          intro hz
          apply hv
          apply Subtype.ext
          apply Subtype.ext
          apply Subtype.ext
          exact hz
        have hq2eq:F*q2 v.1.1=q v.1.1.1:=by
          change F*quotientPolynomial qlow1 F hdiv1 v.1.1=q v.1.1.1
          simpa only [qlow1,LinearMap.comp_apply,Submodule.coe_subtype] using
            (recon_eq_mul_quotientPolynomial qlow1 F hdiv1 v.1.1).symm
        have hq3eq:F*q3 v.1=q2 v.1.1:=by
          change F*quotientPolynomial qlow2 F hdiv2 v.1=
            quotientPolynomial qlow1 F hdiv1 v.1.1
          calc
            F*quotientPolynomial qlow2 F hdiv2 v.1=q2 v.1.1:=by
              simpa only [qlow2,LinearMap.comp_apply,Submodule.coe_subtype] using
                (recon_eq_mul_quotientPolynomial qlow2 F hdiv2 v.1).symm
            _=quotientPolynomial qlow1 F hdiv1 v.1.1:=by rfl
        have hq4eq:F*q4 v=q3 v.1:=by
          change F*quotientPolynomial qlow3 F hdiv3 v=
            quotientPolynomial qlow2 F hdiv2 v.1
          calc
            F*quotientPolynomial qlow3 F hdiv3 v=qlow3 v:=by
              simpa only using
                (recon_eq_mul_quotientPolynomial qlow3 F hdiv3 v).symm
            _=q3 v.1:=by rfl
        right
        right
        right
        refine ⟨v.1.1.1,q4 v,hvV,hQ4,?_,?_⟩
        · calc
            source v.1.1.1=F*q v.1.1.1:=hsource v.1.1.1
            _=F*(F*q2 v.1.1):=congrArg (fun W=>F*W) hq2eq.symm
            _=F*(F*(F*q3 v.1)):=congrArg (fun W=>F*(F*W)) hq3eq.symm
            _=F*(F*(F*(F*q4 v))):=congrArg (fun W=>F*(F*(F*W))) hq4eq.symm
        · simpa only [T1,YS1,S1,T2,YS2,S2,T3,YS3,S3,
            nextT,nextYS,nextS] using hQ4box
      · push Not at hdiv3
        obtain ⟨v,hvdiv⟩:=hdiv3
        have hQ3:qlow3 v≠0:=by
          intro hz
          apply hvdiv
          rw [hz]
          exact dvd_zero F
        have hvV:v.1.1.1≠0:=by
          intro hz
          have hv0:v=0:=by
            apply Subtype.ext
            apply Subtype.ext
            apply Subtype.ext
            exact hz
          exact hQ3 (by rw [hv0,map_zero])
        have hq2eq:F*q2 v.1.1=q v.1.1.1:=by
          change F*quotientPolynomial qlow1 F hdiv1 v.1.1=q v.1.1.1
          simpa only [qlow1,LinearMap.comp_apply,Submodule.coe_subtype] using
            (recon_eq_mul_quotientPolynomial qlow1 F hdiv1 v.1.1).symm
        have hq3eq:F*q3 v.1=q2 v.1.1:=by
          change F*quotientPolynomial qlow2 F hdiv2 v.1=
            quotientPolynomial qlow1 F hdiv1 v.1.1
          calc
            F*quotientPolynomial qlow2 F hdiv2 v.1=q2 v.1.1:=by
              simpa only [qlow2,LinearMap.comp_apply,Submodule.coe_subtype] using
                (recon_eq_mul_quotientPolynomial qlow2 F hdiv2 v.1).symm
            _=quotientPolynomial qlow1 F hdiv1 v.1.1:=by rfl
        right
        right
        left
        refine ⟨v.1.1.1,qlow3 v,hvV,hQ3,?_,?_,hvdiv⟩
        · calc
            source v.1.1.1=F*q v.1.1.1:=hsource v.1.1.1
            _=F*(F*q2 v.1.1):=congrArg (fun W=>F*W) hq2eq.symm
            _=F*(F*(F*q3 v.1)):=congrArg (fun W=>F*(F*W)) hq3eq.symm
            _=F*(F*(F*qlow3 v)):=by rfl
        · simpa only [T1,YS1,S1,T2,YS2,S2,nextT,nextYS,nextS] using
            hqLow3Box v
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
      simpa only [T1,YS1,S1,nextT,nextYS,nextS] using hqLow2Box v
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

end FourStageLowQuotient

/-- Exact score-67.67 C126 third-contact budget. -/
theorem c126_third_capacity_exact:
    22895082-3*50637=(126-3)*181707+3*(131071-1)∧
      22895082-3*50637=22743171:=by norm_num

/-- Consumer-neutral score-67.67 C126 bridge from an exact cubic
reconstruction to quotient vanishing at a regular seed. -/
theorem c126_third_cube_quotient_vanish
    (L:ℕ) (nodes:I↪K) (u0 u1:I→K)
    (v:ConstraintKernel (K:=K) 22895082 131071 L 39 126 nodes u0 u1)
    (hlow:reconstruct K 22895082 131071 L 39 v.1∈
      globalCoefficientBox K 22743171 131071 L 39)
    (P:Polynomial K) (gamma:K) (support:Finset I)
    (hP:P.natDegree≤131071) (hcard:181707≤support.card)
    (hvalues:∀ i∈support,P.eval (nodes i)=u0 i+gamma*u1 i)
    (F Q3:P4)
    (hcube:reconstruct K 22895082 131071 L 39 v.1=F*(F*(F*Q3)))
    (hFzero:RCN319.specialization K P gamma F=0)
    (hregular:RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2:Fin 4) F)≠0):
    RCN319.specialization K P gamma Q3=0:=by
  have hcapacity:22743171≤
      (126-3)*support.card+3*(131071-1):=by
    have hexact:=c126_third_capacity_exact
    omega
  have hsix:(6:K)≠0:=by
    intro hz
    have hdvd:2130706433∣6:=
      (CharP.cast_eq_zero_iff K 2130706433 6).mp hz
    norm_num at hdvd
  exact LocatorTripleCubeAvoidance.specialization_eq_zero_of_kernel_low_box_cube_product
    22895082 22743171 131071 L 39 126 nodes u0 u1 v hlow
    P gamma support (by decide) hP hcapacity hvalues F Q3 hsix hcube
      hFzero hregular

theorem c126_fourth_capacity_exact:
    22895082-4*50637=(126-4)*181707+4*(131071-1)∧
      22895082-4*50637=22692534:=by norm_num

theorem c126_fourth_power_quotient_vanish
    (L:ℕ) (nodes:I↪K) (u0 u1:I→K)
    (v:ConstraintKernel (K:=K) 22895082 131071 L 39 126 nodes u0 u1)
    (hlow:reconstruct K 22895082 131071 L 39 v.1∈
      globalCoefficientBox K 22692534 131071 L 39)
    (P:Polynomial K) (gamma:K) (support:Finset I)
    (hP:P.natDegree≤131071) (hcard:181707≤support.card)
    (hvalues:∀ i∈support,P.eval (nodes i)=u0 i+gamma*u1 i)
    (F Q4:P4)
    (hfourth:reconstruct K 22895082 131071 L 39 v.1=F*(F*(F*(F*Q4))))
    (hFzero:RCN319.specialization K P gamma F=0)
    (hregular:RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2:Fin 4) F)≠0):
    RCN319.specialization K P gamma Q4=0:=by
  have hcapacity:22692534≤
      (126-4)*support.card+4*(131071-1):=by
    have hexact:=c126_fourth_capacity_exact
    omega
  have htwentyfour:(24:K)≠0:=by
    intro hz
    have hdvd:2130706433∣24:=
      (CharP.cast_eq_zero_iff K 2130706433 24).mp hz
    norm_num at hdvd
  exact LocatorQuarticFourthAvoidance.specialization_eq_zero_of_kernel_low_box_fourth_product
    22895082 22692534 131071 L 39 126 nodes u0 u1 v hlow
    P gamma support (by decide) hP hcapacity hvalues F Q4 htwentyfour
      hfourth hFzero hregular

end
end ProximityPrize.SubmissionLower.LocatorTripleFactorSwitch
