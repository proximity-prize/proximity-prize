import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactJointTaylorMiddleCap6631Research
import ProximityPrize.SubmissionLower.ContactResidualSupportParametersResearch
import ProximityPrize.SubmissionLower.ContactFixedMeetFactorIncidence6656Research
import ProximityPrize.SubmissionLower.ContactTightFixedMeet6656Research
namespace ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet6656Research
open scoped Classical BigOperators
open ContactFactorCaps ContactTaylorNumerators ContactGenericSurface
open ContactPost6464MinkowskiRecurrenceResearch
open ContactJointTaylorMiddleCap6631Research
open ContactFlagBezout6543Research
open ContactResidualSupportParametersResearch
open ContactResidualSupportParametersResearch.ResidualSupportParameters
open ContactIdentityResidualGlobalFlagResearch
open ContactInterpolation ContactPrimeSeedIncidence
open ContactRegularFactorFlag6600Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualTerminalIncidenceResearch
open ContactFixedMeetFactorIncidence6656Research
open ContactRobustFixedMeet6656Research
open ContactTightSingularLedgerResearch
open ContactGlobalSelectedFamilies6656Research
open ContactTightFixedMeet6656Research
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
def sharpAgreementDirection (P:ResidualSupportParameters):FlagDegree:=
  ⟨2*(P.total-P.ys),2*(P.ys-P.s)-1,2*P.s-1⟩
def sharpResidualAgreementFlag
    (P:ResidualSupportParameters) (d:ℕ):FlagDegree:=
  ⟨(sharpAgreementDirection P).zOnly*d,
    1+(sharpAgreementDirection P).yz*d,
    (sharpAgreementDirection P).all*d⟩
theorem sharpResidualAgreementFlag_ys
    (P:ResidualSupportParameters) (hsy:P.s < P.ys) (d:ℕ):
    (sharpResidualAgreementFlag P d).yz+
        (sharpResidualAgreementFlag P d).all=
      1+d*(2*P.ys-2):=by
  have hcoeff:
      (2*(P.ys-P.s)-1)+(2*P.s-1)=2*P.ys-2:=by
    have hleft:1 ≤ 2*(P.ys-P.s):=by
      have:1 ≤ P.ys-P.s:=Nat.sub_pos_of_lt hsy
      omega
    have hright:1 ≤ 2*P.s:=by
      have:1 ≤ P.s:=P.one_le_s
      omega
    rw [tsub_add_tsub_comm hleft hright]
    have hsum:2*(P.ys-P.s)+2*P.s=2*P.ys:=by
      calc
        2*(P.ys-P.s)+2*P.s=2*((P.ys-P.s)+P.s):=by ring
        _=2*P.ys:=by rw [Nat.sub_add_cancel (Nat.le_of_lt hsy)]
    rw [hsum]
  simp only [sharpResidualAgreementFlag,sharpAgreementDirection]
  rw [←hcoeff]
  ring
theorem sharpResidualAgreementFlag_total
    (P:ResidualSupportParameters) (hsy:P.s < P.ys) (d:ℕ):
    (sharpResidualAgreementFlag P d).zOnly+
        (sharpResidualAgreementFlag P d).yz+
        (sharpResidualAgreementFlag P d).all=
      1+d*(2*P.total-2):=by
  have hcoeff:
      2*(P.total-P.ys)+(2*(P.ys-P.s)-1)+
          (2*P.s-1)=2*P.total-2:=by
    have hmiddle:
        (2*(P.ys-P.s)-1)+(2*P.s-1)=
          2*P.ys-2:=by
      have hleft:1 ≤ 2*(P.ys-P.s):=by
        have:1 ≤ P.ys-P.s:=Nat.sub_pos_of_lt hsy
        omega
      have hright:1 ≤ 2*P.s:=by
        have:1 ≤ P.s:=P.one_le_s
        omega
      rw [tsub_add_tsub_comm hleft hright]
      have hsum:2*(P.ys-P.s)+2*P.s=2*P.ys:=by
        calc
          2*(P.ys-P.s)+2*P.s=
              2*((P.ys-P.s)+P.s):=by ring
          _=2*P.ys:=by rw [Nat.sub_add_cancel (Nat.le_of_lt hsy)]
      rw [hsum]
    rw [Nat.add_assoc,hmiddle]
    have htwo:2 ≤ 2*P.ys:=by
      have:1 ≤ P.ys:=P.one_le_s.trans P.s_le_ys
      omega
    rw [←Nat.add_sub_assoc htwo]
    have hsum:2*(P.total-P.ys)+2*P.ys=2*P.total:=by
      calc
        2*(P.total-P.ys)+2*P.ys=
            2*((P.total-P.ys)+P.ys):=by ring
        _=2*P.total:=by rw [Nat.sub_add_cancel P.ys_le_total]
    rw [hsum]
  simp only [sharpResidualAgreementFlag,sharpAgreementDirection]
  rw [←hcoeff]
  ring
theorem fixedMeet_sharp_agreement_direction:
    sharpAgreementDirection fixedMeetSupport=⟨1140,55,11⟩:=by
  norm_num [fixedMeetSupport,sharpAgreementDirection]
theorem fixedMeet_sharp_agreement_flag (d:ℕ):
    sharpResidualAgreementFlag fixedMeetSupport d=
      ⟨1140*d,1+55*d,11*d⟩:=by
  rw [show sharpResidualAgreementFlag fixedMeetSupport d=
      ⟨(sharpAgreementDirection fixedMeetSupport).zOnly*d,
        1+(sharpAgreementDirection fixedMeetSupport).yz*d,
        (sharpAgreementDirection fixedMeetSupport).all*d⟩ by rfl,
    fixedMeet_sharp_agreement_direction]
variable {K Omega:Type} [Field K] [Field Omega]
theorem sharp_agreement_weight_bounds
    {P:ResidualSupportParameters} {F:MvPolynomial (Fin 4) K}
    (H:ResidualSupportData P F)
    (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
    (agreementNumerator F d coeffs x u0 u1).degreeOf (2:Fin 4) ≤
        d*(2*P.s-1)∧
      wt residualYSWeights (agreementNumerator F d coeffs x u0 u1) ≤
        1+d*(2*P.ys-2)∧
      wt residualTotalWeights (agreementNumerator F d coeffs x u0 u1) ≤
        1+d*(2*P.total-2):=by
  obtain ⟨hY,hR,hZ⟩:=H.coordinate_bounds
  refine ⟨(agreementNumerator_degree_bounds F P.ys P.s P.total
    P.one_le_s hY hR hZ d coeffs x u0 u1).2.1,?_,?_⟩
  · have h:=agreementNumerator_wt_le_equal_weight residualYSWeights rfl
      F P.ys (by change 1 ≤ 1;norm_num)
      (by change 1 ≤ P.ys;exact P.one_le_s.trans P.s_le_ys)
      (by change 2*1 ≤ P.ys;simpa using P.two_le_ys)
      (by change 1 ≤ 1;norm_num) H.ys_weight d coeffs x u0 u1
    have hcoeff:2*(P.ys-1)=2*P.ys-2:=by omega
    apply h.trans_eq
    change max 1 0+d*(2*(P.ys-1))=
      1+d*(2*P.ys-2)
    rw [hcoeff]
    norm_num
  · have htotalTwo:2 ≤ P.total:=P.two_le_ys.trans P.ys_le_total
    have honeTotal:1 ≤ P.total:=
      P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)
    have h:=agreementNumerator_wt_le_equal_weight residualTotalWeights rfl
      F P.total (by change 1 ≤ 1;norm_num)
      (by change 1 ≤ P.total;exact honeTotal)
      (by change 2*1 ≤ P.total;simpa using htotalTwo)
      (by change 1 ≤ 1;norm_num) H.total_weight d coeffs x u0 u1
    have hcoeff:2*(P.total-1)=2*P.total-2:=by omega
    apply h.trans_eq
    change max 1 1+d*(2*(P.total-1))=
      1+d*(2*P.total-2)
    rw [hcoeff]
    norm_num
theorem surfaceMap_agreement_in_sharp_flag
    {P:ResidualSupportParameters} (hsy:P.s < P.ys)
    (phi:Polynomial K →+*Omega) {F:MvPolynomial (Fin 4) K}
    (H:ResidualSupportData P F)
    (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
    PolynomialInFlag (sharpResidualAgreementFlag P d)
      (surfaceMap phi (agreementNumerator F d coeffs x u0 u1)):=by
  intro e he
  obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
    (support_surfaceMap_subset phi (agreementNumerator F d coeffs x u0 u1) he)
  obtain ⟨hR,hYS,hTotal⟩:=sharp_agreement_weight_bounds H
    d coeffs x u0 u1
  have hqR:=(MvPolynomial.monomial_le_degreeOf (2:Fin 4) hq).trans hR
  have hqYS:=
    (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS
  have hqTotal:=
    (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTotal
  rw [ContactFactorCaps.weight_fin4] at hqYS hqTotal
  change q 0*0+q 1*1+q 2*1+q 3*0 ≤
    1+d*(2*P.ys-2) at hqYS
  change q 0*0+q 1*1+q 2*1+q 3*1 ≤
    1+d*(2*P.total-2) at hqTotal
  norm_num at hqYS hqTotal
  have hqR':q 2 ≤ (sharpResidualAgreementFlag P d).all:=by
    change q 2 ≤ (2*P.s-1)*d
    rw [Nat.mul_comm]
    exact hqR
  change q 2 ≤ (sharpResidualAgreementFlag P d).all∧
    q 1+q 2 ≤ (sharpResidualAgreementFlag P d).yz+
      (sharpResidualAgreementFlag P d).all∧
    q 1+q 2+q 3 ≤ (sharpResidualAgreementFlag P d).zOnly+
      (sharpResidualAgreementFlag P d).yz+
      (sharpResidualAgreementFlag P d).all
  refine ⟨hqR',?_,?_⟩
  · rw [sharpResidualAgreementFlag_ys P hsy]
    exact hqYS
  · rw [sharpResidualAgreementFlag_total P hsy]
    exact hqTotal
def factorRegularLedgerForDirection
    (p:Profile) (direction flag:FlagDegree):ℕ:=
  (flagMixed flag direction direction*p.degreeIncidence^2+
      2*flagMixed flag direction unitYZFlag*
        p.degreeIncidence*p.unitIncidence+
      flagMixed flag unitYZFlag unitYZFlag*p.unitIncidence^2)+
    (p.errors+1)*p.gap*
      (flagMixed flag direction unitZFlag*p.degreeIncidence+
        flagMixed flag unitYZFlag unitZFlag*p.unitIncidence)+
    (p.errors+1)*p.gap*
      (flagMixed flag direction unitAllFlag*p.degreeIncidence+
        flagMixed flag unitYZFlag unitAllFlag*p.unitIncidence)
def sharpRegularNumerator
    (p:Profile) (support:ResidualSupportParameters):ℕ:=
  factorRegularLedgerForDirection p (sharpAgreementDirection support)
    p.rectangularSurfaceFlag
theorem factorRegularLedgerForDirection_projection_decomposition
    (p:Profile) (direction flag:FlagDegree):
    factorRegularLedgerForDirection p direction flag=
      flag.zOnly*factorRegularLedgerForDirection p direction unitZFlag+
      flag.yz*factorRegularLedgerForDirection p direction unitYZFlag+
      flag.all*factorRegularLedgerForDirection p direction unitAllFlag:=by
  cases flag
  simp [factorRegularLedgerForDirection,flagMixed,unitZFlag,unitYZFlag,
    unitAllFlag]
  ring
theorem sum_factorRegularLedgerForDirection_le_flag
    {I:Type} [Fintype I] (p:Profile) (direction:FlagDegree)
    (flag:I → FlagDegree) (cap:FlagDegree)
    (hz:(∑ i,(flag i).zOnly) ≤ cap.zOnly)
    (hyz:(∑ i,(flag i).yz) ≤ cap.yz)
    (hall:(∑ i,(flag i).all) ≤ cap.all):
    (∑ i,factorRegularLedgerForDirection p direction (flag i)) ≤
      factorRegularLedgerForDirection p direction cap:=by
  classical
  calc
    (∑ i,factorRegularLedgerForDirection p direction (flag i))=
        ∑ i,((flag i).zOnly*
            factorRegularLedgerForDirection p direction unitZFlag+
          (flag i).yz*
            factorRegularLedgerForDirection p direction unitYZFlag+
          (flag i).all*
            factorRegularLedgerForDirection p direction unitAllFlag):=by
      apply Finset.sum_congr rfl
      intro i _
      exact factorRegularLedgerForDirection_projection_decomposition
        p direction (flag i)
    _=(∑ i,(flag i).zOnly)*
          factorRegularLedgerForDirection p direction unitZFlag+
        (∑ i,(flag i).yz)*
          factorRegularLedgerForDirection p direction unitYZFlag+
        (∑ i,(flag i).all)*
          factorRegularLedgerForDirection p direction unitAllFlag:=by
      simp only [Finset.sum_add_distrib,Finset.sum_mul]
    _ ≤ cap.zOnly*factorRegularLedgerForDirection p direction unitZFlag+
        cap.yz*factorRegularLedgerForDirection p direction unitYZFlag+
        cap.all*factorRegularLedgerForDirection p direction unitAllFlag:=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ hz)
          (Nat.mul_le_mul_right _ hyz))
        (Nat.mul_le_mul_right _ hall)
    _=factorRegularLedgerForDirection p direction cap:=
      (factorRegularLedgerForDirection_projection_decomposition
        p direction cap).symm
variable {K Omega Iota:Type} [Field K] [Field Omega]
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
variable {pchar:ℕ} [CharP Omega pchar]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem sum_factor_counts_rectangular_sharp_le
    (p:Profile) (support:ResidualSupportParameters)
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (hw:0 < p.w)
    (hbox:Q∈globalCoefficientBox K p.weightedCap p.w
      p.seedTotalCap p.slopeCap)
    (count:RegularIndex Q → ℕ)
    (hcount:∀ F,count F*p.gap^2 ≤
      factorRegularLedgerForDirection p (sharpAgreementDirection support)
        (regularFlag Q F)):
    (∑ F,count F)*p.gap^2 ≤ sharpRegularNumerator p support:=by
  have hcaps:=regularFlag_budgets p Q hQ hw hbox
  calc
    (∑ F,count F)*p.gap^2=∑ F,count F*p.gap^2:=by
      rw [Finset.sum_mul]
    _ ≤ ∑ F,factorRegularLedgerForDirection p
        (sharpAgreementDirection support) (regularFlag Q F):=
      Finset.sum_le_sum (fun F _↦hcount F)
    _ ≤ factorRegularLedgerForDirection p (sharpAgreementDirection support)
        p.rectangularSurfaceFlag:=
      sum_factorRegularLedgerForDirection_le_flag p
        (sharpAgreementDirection support) (regularFlag Q)
        p.rectangularSurfaceFlag hcaps.1 hcaps.2.1 hcaps.2.2
    _=sharpRegularNumerator p support:=rfl
def meetSharpFactorDegreeCost (flag:FlagDegree):ℕ:=
  (flagMixed flag (sharpAgreementDirection fixedMeetSupport)
        (sharpAgreementDirection fixedMeetSupport)*
      meetProfile.degreeIncidence+
    flagMixed flag (sharpAgreementDirection fixedMeetSupport) unitYZFlag*
      meetProfile.unitIncidence)+
  (meetProfile.errors+1)*meetProfile.gap*
    (flagMixed flag (sharpAgreementDirection fixedMeetSupport) unitZFlag+
      flagMixed flag (sharpAgreementDirection fixedMeetSupport) unitAllFlag)
def meetSharpFactorUnitCost (flag:FlagDegree):ℕ:=
  (flagMixed flag (sharpAgreementDirection fixedMeetSupport) unitYZFlag*
      meetProfile.degreeIncidence+
    flagMixed flag unitYZFlag unitYZFlag*meetProfile.unitIncidence)+
  (meetProfile.errors+1)*meetProfile.gap*
    (flagMixed flag unitYZFlag unitZFlag+
      flagMixed flag unitYZFlag unitAllFlag)
theorem meet_sharp_incidence_cost_eq_ledger (flag:FlagDegree):
    meetProfile.degreeIncidence*meetSharpFactorDegreeCost flag+
      meetProfile.unitIncidence*meetSharpFactorUnitCost flag=
    factorRegularLedgerForDirection meetProfile
      (sharpAgreementDirection fixedMeetSupport) flag:=by
  simp [meetSharpFactorDegreeCost,meetSharpFactorUnitCost,
    factorRegularLedgerForDirection]
  ring
theorem recursive_scaled_factor_sharp_6656
    {flag:FlagDegree}
    (hphi:Function.Injective phi)
    (S:ResidualStage phi Gamma x pchar meetProfile.errors flag meetProfile.w
      fixedMeetSupport)
    (hnodes:S.nodes.card=meetProfile.n)
    (hagreement:∀ gamma∈Gamma,
      meetProfile.agreements ≤ (S.agreementFiber gamma).card)
    (hfiber:∀ D:S.TerminalDescendant,∀ i∈D.stage.nodes,
      ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*
          meetProfile.gap ≤
        D.degree*meetSharpFactorDegreeCost flag+
          meetSharpFactorUnitCost flag):
    Gamma.card*meetProfile.gap^2 ≤
      factorRegularLedgerForDirection meetProfile
        (sharpAgreementDirection fixedMeetSupport) flag:=by
  have h:=recursive_scaled_stratified_incidence_bound
    hphi S (meetSharpFactorDegreeCost flag) (meetSharpFactorUnitCost flag)
      meetProfile.degreeIncidence meetProfile.unitIncidence
      (by norm_num [meetProfile]) hagreement hfiber
      (by
        intro k hk
        rw [hnodes]
        exact meet_degree_part_bound k hk)
      (by
        intro k hk
        rw [hnodes]
        exact meet_unit_part_bound k hk)
  calc
    Gamma.card*meetProfile.gap^2 ≤
        meetProfile.degreeIncidence*meetSharpFactorDegreeCost flag+
          meetProfile.unitIncidence*meetSharpFactorUnitCost flag:=by
      simpa only [Profile.gap] using h
    _=factorRegularLedgerForDirection meetProfile
        (sharpAgreementDirection fixedMeetSupport) flag:=
      meet_sharp_incidence_cost_eq_ledger flag
def meetSharpRegularNumerator:ℕ:=
  sharpRegularNumerator meetProfile fixedMeetSupport
def meetSharpTightFixedCountCap:ℕ:=
  meetSharpRegularNumerator/meetProfile.gap^2+
    meetTightProfile.countCap
def meetSharpTightFixedCost:ℕ:=meetSharpTightFixedCountCap+1
theorem meet_sharp_regular_numerator_exact:
    meetSharpRegularNumerator=251547391650163581021710430:=by
  norm_num [meetSharpRegularNumerator,sharpRegularNumerator,
    factorRegularLedgerForDirection,fixedMeetSupport,
    sharpAgreementDirection,
    meetProfile,Profile.rectangularSurfaceFlag,Profile.yCap,
    Profile.degreeIncidence,Profile.unitIncidence,Profile.errors,
    Profile.gap,flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
theorem meet_sharp_tight_fixed_costs_exact:
    meetSharpTightFixedCountCap=93984734489150979∧
      meetSharpTightFixedCost=93984734489150980:=by
  have hcap:meetSharpTightFixedCountCap=93984734489150979:=by
    rw [show meetSharpTightFixedCountCap=
        meetSharpRegularNumerator/meetProfile.gap^2+
          meetTightProfile.countCap by rfl,
      meet_sharp_regular_numerator_exact,
      meet_tight_singular_count_cap_exact]
    norm_num [meetProfile,Profile.gap]
  exact ⟨hcap,by rw [meetSharpTightFixedCost,hcap]⟩
theorem meet_sharp_saving_over_tight_fixed_exact:
    meetTightFixedCost-meetSharpTightFixedCost=1012255769609106:=by
  rw [meet_tight_fixed_costs_exact.2,meet_sharp_tight_fixed_costs_exact.2]
end
end ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet6656Research
