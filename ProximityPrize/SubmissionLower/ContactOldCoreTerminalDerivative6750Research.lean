import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactHighTDerivativeSelectorPositive6750Research
import ProximityPrize.SubmissionLower.ContactIteratedDerivativeDegree6700Research
import ProximityPrize.SubmissionLower.ContactAnchoredThirdResidualAdapter6750Research
import ProximityPrize.SubmissionLower.ContactSelectedOldCoreLowQuotients6750Research

 









namespace ProximityPrize.SubmissionLower
namespace ContactOldCoreTerminalDerivative6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactFactorCaps
open ContactFlagInterpolation6641Research
open ContactIdentityResidualGlobalFlagResearch
open ContactTwoTailParameters6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactAnchoredThirdResidualAdapter6750Research
open ContactSelectedCount6750Research
open ContactSelectedOldCoreQuotientRank6750Research
open ContactSelectedOldCoreLowQuotients6750Research
open ContactHighTDerivativeRouter6750Research
open ContactHighTDerivativeSelectorPositive6750Research
open ContactIteratedDerivativeDegree6700Research
open ContactTaylorNumerators

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : CharP K prime := by
  simpa [prime, ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600

 

theorem degreeOf_pderiv_eq_sub_one_below_char
    {F : Type*} [Field F] {p : Nat} [CharP F p]
    (i : Fin 4) (Q : MvPolynomial (Fin 4) F)
    (hpos : 0 < Q.degreeOf i) (hsmall : Q.degreeOf i < p) :
    (MvPolynomial.pderiv i Q).degreeOf i = Q.degreeOf i - 1 := by
  have hQ : Q ≠ 0 := by
    intro hzero
    subst Q
    simpa using hpos
  obtain ⟨d, hd, hdegree⟩ := Finset.exists_mem_eq_sup Q.support
    (MvPolynomial.support_nonempty.mpr hQ) (fun e ↦ e i)
  have hdi : Q.degreeOf i = d i := by
    simpa only [MvPolynomial.degreeOf_eq_sup] using hdegree
  let e : Fin 4 →₀ Nat := d - Finsupp.single i 1
  have hdi_pos : 0 < d i := by omega
  have headd : e + Finsupp.single i 1 = d := by
    exact Finsupp.sub_add_single_one_cancel (by omega)
  have hei : e i + 1 = d i := by
    have h := congrArg (fun f : Fin 4 →₀ Nat ↦ f i) headd
    simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using h
  have hcast : (d i : F) ≠ 0 :=
    (CharP.cast_eq_zero_iff F p (d i)).not.mpr
      (Nat.not_dvd_of_pos_of_lt hdi_pos (by omega))
  have hcoef : MvPolynomial.coeff e (MvPolynomial.pderiv i Q) ≠ 0 := by
    rw [MvPolynomial.coeff_pderiv, headd]
    apply mul_ne_zero (MvPolynomial.mem_support_iff.mp hd)
    simpa only [← hei, Nat.cast_add, Nat.cast_one] using hcast
  have heSupport : e ∈ (MvPolynomial.pderiv i Q).support :=
    MvPolynomial.mem_support_iff.mpr hcoef
  have hlower : Q.degreeOf i - 1 ≤
      (MvPolynomial.pderiv i Q).degreeOf i := by
    have hmono := MvPolynomial.monomial_le_degreeOf i heSupport
    have heval : e i = Q.degreeOf i - 1 := by
      rw [hdi]
      omega
    omega
  have hupper := pderiv_same_degree_bound i Q (Q.degreeOf i) le_rfl
  omega

 


theorem iterate_pderiv_degreeOf_eq_and_ne_zero_below_char
    {F : Type*} [Field F] {p : Nat} [CharP F p]
    (i : Fin 4) (Q : MvPolynomial (Fin 4) F) (q : Nat)
    (hQ : Q ≠ 0) (hsmall : Q.degreeOf i < p)
    (hq : q ≤ Q.degreeOf i) :
    ((MvPolynomial.pderiv i)^[q] Q).degreeOf i = Q.degreeOf i - q ∧
      (MvPolynomial.pderiv i)^[q] Q ≠ 0 := by
  induction q with
  | zero =>
      constructor
      · simp
      · simpa using hQ
  | succ q ih =>
      have hq' : q ≤ Q.degreeOf i := by omega
      obtain ⟨hdegree, hne⟩ := ih hq'
      let R := (MvPolynomial.pderiv i)^[q] Q
      have hpos : 0 < R.degreeOf i := by
        dsimp only [R]
        rw [hdegree]
        omega
      have hsmallR : R.degreeOf i < p := by
        dsimp only [R]
        rw [hdegree]
        omega
      have hstep := degreeOf_pderiv_eq_sub_one_below_char i R hpos hsmallR
      have hstep_ne : MvPolynomial.pderiv i R ≠ 0 := by
        intro hzero
        have hz := (ContactRegularFactorGate.pderiv_zero_iff_degree_zero_below_char
          i R p hsmallR).mp hzero
        omega
      rw [Function.iterate_succ_apply']
      constructor
      · dsimp only [R] at hstep
        omega
      · exact hstep_ne

 
theorem oldCommonCore_degreeOf_R_eq {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) :
    (oldCommonCore S).degreeOf (2 : Fin 4) = oldCoreS S := by
  unfold oldCoreS
  have hw : residualSWeights = Pi.single (2 : Fin 4) 1 := by
    funext i
    fin_cases i <;> rfl
  rw [hw, MvPolynomial.weightedTotalDegree_piSingle]

 

def terminalDerivativeCutoff (j : Nat) : Nat :=
  profileA.weightedCap - j * (w - 1)

 
theorem terminalDerivative_mem_nestedFiveCap
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (j : Nat) (hj : j ≤ oldCoreS S) :
    (MvPolynomial.pderiv (2 : Fin 4))^[j] (oldCommonCore S) ∈
      nestedFiveCapCoefficientBox K (terminalDerivativeCutoff j) w
        (oldCoreTotal S - j) (oldCoreYS S - j) (oldCoreS S - j) := by
  intro d hd
  have hsource := support_before_iterate_pderiv
    (K := K) (2 : Fin 4) j (oldCommonCore S) d hd
  have htotal := MvPolynomial.le_weightedTotalDegree
    residualTotalWeights hsource
  have hys := MvPolynomial.le_weightedTotalDegree residualYSWeights hsource
  have hs := MvPolynomial.le_weightedTotalDegree residualSWeights hsource
  have hcontact := MvPolynomial.le_weightedTotalDegree
    (contactWeights w) hsource
  have hcontactCap := oldCommonCore_contact_le S
  have hnested := ContactGCDCumulativeFlagsResearch.residual_weight_nested
    (oldCommonCore S)
  have hjys : j ≤ oldCoreYS S := by
    exact hj.trans (by simpa only [oldCoreS, oldCoreYS,
      ContactPost6464MinkowskiRecurrenceResearch.wt] using hnested.1)
  have hjtotal : j ≤ oldCoreTotal S := by
    exact hjys.trans (by simpa only [oldCoreYS, oldCoreTotal,
      ContactPost6464MinkowskiRecurrenceResearch.wt] using hnested.2)
  have htotal' : d 1 + (d 2 + j) + d 3 ≤ oldCoreTotal S := by
    rw [weight_fin4] at htotal
    simpa [oldCoreTotal, residualTotalWeights, Finsupp.add_apply,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htotal
  have hys' : d 1 + (d 2 + j) ≤ oldCoreYS S := by
    rw [weight_fin4] at hys
    simpa [oldCoreYS, residualYSWeights, Finsupp.add_apply,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hys
  have hs' : d 2 + j ≤ oldCoreS S := by
    rw [weight_fin4] at hs
    simpa [oldCoreS, residualSWeights, Finsupp.add_apply,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs
  have hcontact' :
      d 0 + w * d 1 + (w - 1) * (d 2 + j) < profileA.weightedCap := by
    rw [contact_weight] at hcontact
    have hle : d 0 + w * d 1 + (w - 1) * (d 2 + j) ≤
        MvPolynomial.weightedTotalDegree (contactWeights w) (oldCommonCore S) := by
      simpa [Finsupp.add_apply, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using hcontact
    have hcap : MvPolynomial.weightedTotalDegree
        (contactWeights w) (oldCommonCore S) < profileA.weightedCap := by
      norm_num [w, profileA,
        ContactTwoTailParameters6750Research.Profile.weightedCap,
        agreements, n, errors] at hcontactCap ⊢
      omega
    exact hle.trans_lt hcap
  change d 1 + d 2 + d 3 ≤ oldCoreTotal S - j ∧
    d 1 + d 2 ≤ oldCoreYS S - j ∧
    d 2 ≤ oldCoreS S - j ∧
    d 0 + w * d 1 + (w - 1) * d 2 < terminalDerivativeCutoff j
  norm_num [terminalDerivativeCutoff, profileA,
    ContactTwoTailParameters6750Research.Profile.weightedCap,
    w, agreements, n, errors] at hcontact' ⊢
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

 
theorem terminalDerivative_ne_zero
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (j : Nat) (hj : j ≤ oldCoreS S) :
    (MvPolynomial.pderiv (2 : Fin 4))^[j] (oldCommonCore S) ≠ 0 := by
  have hslope : (oldCommonCore S).degreeOf (2 : Fin 4) = oldCoreS S :=
    oldCommonCore_degreeOf_R_eq S
  have hsmall : (oldCommonCore S).degreeOf (2 : Fin 4) < prime := by
    rw [hslope]
    exact (oldCommonCore_slope_le S).trans_lt (by norm_num [prime])
  exact (iterate_pderiv_degreeOf_eq_and_ne_zero_below_char
    (2 : Fin 4) (oldCommonCore S) j (oldCommonCore_ne_zero S)
      hsmall (by simpa only [hslope] using hj)).2

 
theorem terminalDerivative_degreeOf_R_eq
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (j : Nat) (hj : j ≤ oldCoreS S) :
    ((MvPolynomial.pderiv (2 : Fin 4))^[j] (oldCommonCore S)).degreeOf
        (2 : Fin 4) = oldCoreS S - j := by
  have hslope : (oldCommonCore S).degreeOf (2 : Fin 4) = oldCoreS S :=
    oldCommonCore_degreeOf_R_eq S
  have hsmall : (oldCommonCore S).degreeOf (2 : Fin 4) < prime := by
    rw [hslope]
    exact (oldCommonCore_slope_le S).trans_lt (by norm_num [prime])
  simpa only [hslope] using
    (iterate_pderiv_degreeOf_eq_and_ne_zero_below_char
      (2 : Fin 4) (oldCommonCore S) j (oldCommonCore_ne_zero S)
        hsmall (by simpa only [hslope] using hj)).1

 

theorem terminalDerivative_mem_tight_globalBox
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (j : Nat) (hj : j ≤ oldCoreS S) :
    (MvPolynomial.pderiv (2 : Fin 4))^[j] (oldCommonCore S) ∈
      globalCoefficientBox K (terminalDerivativeCutoff j) w
        (oldCoreTotal S - j) (max 1 (oldCoreS S - j)) := by
  intro d hd
  have hbox := terminalDerivative_mem_nestedFiveCap S j hj
  change ∀ e ∈ ((MvPolynomial.pderiv (2 : Fin 4))^[j]
      (oldCommonCore S)).support,
      e 1 + e 2 + e 3 ≤ oldCoreTotal S - j ∧
      e 1 + e 2 ≤ oldCoreYS S - j ∧
      e 2 ≤ oldCoreS S - j ∧
      e 0 + w * e 1 + (w - 1) * e 2 < terminalDerivativeCutoff j at hbox
  have h := hbox d hd
  exact ⟨h.1, h.2.2.1.trans (Nat.le_max_right _ _), h.2.2.2⟩

end

end ContactOldCoreTerminalDerivative6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactOldCoreTerminalDerivative6750Research.terminalDerivative_mem_nestedFiveCap
#print axioms ProximityPrize.SubmissionLower.ContactOldCoreTerminalDerivative6750Research.terminalDerivative_ne_zero
