import ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance

namespace ProximityPrize.SubmissionLower.LocatorFourthPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance LocatorTripleCubeAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Four successive high-band projections.  This is one outer projection and
the cubic extractor applied to its first quotient. -/
theorem exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low_not_dvd_or_fourth_low
    (Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hsource :
      delta * channelCount T YS S +
          delta * channelCount
            (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) +
          delta * channelCount
            (T - 2 * wt residualTotalWeights F)
              (YS - 2 * wt residualYSWeights F)
              (S - 2 * wt residualSWeights F) +
          delta * channelCount
            (T - 3 * wt residualTotalWeights F)
              (YS - 3 * wt residualYSWeights F)
              (S - 3 * wt residualSWeights F) <
        Module.finrank K V) :
    (∃ v : V, v ≠ 0 ∧ q v ≠ 0 ∧
      q v ∈ nestedCoefficientBox K Dlow w T YS S ∧ ¬ F ∣ q v) ∨
    (∃ (v : V) (H : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ H ≠ 0 ∧ F * H = q v ∧ ¬ F ∣ H ∧
      H ∈ nestedCoefficientBox K
        (Dlow - delta - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
          (S - wt residualSWeights F)) ∨
    (∃ (v : V) (J : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ J ≠ 0 ∧ F * (F * J) = q v ∧ ¬ F ∣ J ∧
      J ∈ nestedCoefficientBox K
        (Dlow - 2 * delta - 2 * wt (contactWeights w) F) w
        (T - 2 * wt residualTotalWeights F)
          (YS - 2 * wt residualYSWeights F)
          (S - 2 * wt residualSWeights F)) ∨
    (∃ (v : V) (J : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ J ≠ 0 ∧ F * (F * (F * J)) = q v ∧
      J ∈ nestedCoefficientBox K
        (Dlow - 3 * delta - 3 * wt (contactWeights w) F) w
        (T - 3 * wt residualTotalWeights F)
          (YS - 3 * wt residualYSWeights F)
          (S - 3 * wt residualSWeights F)) := by
  classical
  let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
  let lowOne := LinearMap.ker bandOne
  have hrangeOne : Module.finrank K bandOne.range ≤
      delta * channelCount T YS S := by
    calc
      Module.finrank K bandOne.range ≤
          Module.finrank K (HighBandIndex delta T YS S → K) :=
        bandOne.range.finrank_le
      _ = delta * channelCount T YS S := by
        rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
  have hlowOneRank :
      delta * channelCount
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) +
        delta * channelCount
          (T - 2 * wt residualTotalWeights F)
            (YS - 2 * wt residualYSWeights F)
            (S - 2 * wt residualSWeights F) +
        delta * channelCount
          (T - 3 * wt residualTotalWeights F)
            (YS - 3 * wt residualYSWeights F)
            (S - 3 * wt residualSWeights F) <
        Module.finrank K lowOne := by
    have hsum := bandOne.finrank_range_add_finrank_ker
    change Module.finrank K bandOne.range + Module.finrank K lowOne =
      Module.finrank K V at hsum
    omega
  let qOne : lowOne →ₗ[K] MvPolynomial (Fin 4) K := q.comp lowOne.subtype
  have hqOne : Function.Injective qOne := by
    intro a b hab
    apply Subtype.ext
    apply hq
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
  have hqOneBox : ∀ v : lowOne,
      qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
    intro v
    have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
      have hv := v.2
      change bandOne v.1 = 0 at hv
      simpa only [bandOne, qOne, LinearMap.comp_apply, Submodule.coe_subtype]
        using hv
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
      mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
        (q v.1) (hmem v.1) hzero
  by_cases hdivOne : ∀ v : lowOne, F ∣ qOne v
  · let qTwo := quotientLinear qOne F hF hdivOne
    have hqTwo : Function.Injective qTwo :=
      quotientLinear_injective qOne hqOne F hF hdivOne
    have hqTwoBox : ∀ v : lowOne,
        qTwo v ∈ nestedCoefficientBox K
          (Dlow - wt (contactWeights w) F) w
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
      intro v
      by_cases hv : v = 0
      · subst v
        rw [map_zero]
        exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
      · have hqOneV : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        have hqTwoV : qTwo v ≠ 0 := by
          intro hz
          apply hqOneV
          rw [recon_eq_mul_quotientPolynomial qOne F hdivOne v]
          change F * qTwo v = 0
          rw [hz, mul_zero]
        exact quotient_mem_nestedCoefficientBox_of_mul_eq
          (qOne v) F (qTwo v) Dlow w T YS S hqOneV hF hqTwoV
            (hqOneBox v) (recon_eq_mul_quotientPolynomial qOne F hdivOne v)
    let TOne := T - wt residualTotalWeights F
    let YOne := YS - wt residualYSWeights F
    let SOne := S - wt residualSWeights F
    let DOneHigh := Dlow - wt (contactWeights w) F
    let DOneLow := Dlow - delta - wt (contactWeights w) F
    have hwidthRest : DOneHigh ≤ DOneLow + delta := by
      simp only [DOneHigh, DOneLow]
      omega
    have hsourceRest :
        delta * channelCount TOne YOne SOne +
            delta * channelCount
              (TOne - wt residualTotalWeights F)
                (YOne - wt residualYSWeights F)
                (SOne - wt residualSWeights F) +
            delta * channelCount
              (TOne - 2 * wt residualTotalWeights F)
                (YOne - 2 * wt residualYSWeights F)
                (SOne - 2 * wt residualSWeights F) <
          Module.finrank K lowOne := by
      simp only [TOne, YOne, SOne]
      have hT2 : T - wt residualTotalWeights F - wt residualTotalWeights F =
          T - 2 * wt residualTotalWeights F := by omega
      have hY2 : YS - wt residualYSWeights F - wt residualYSWeights F =
          YS - 2 * wt residualYSWeights F := by omega
      have hS2 : S - wt residualSWeights F - wt residualSWeights F =
          S - 2 * wt residualSWeights F := by omega
      have hT3 : T - wt residualTotalWeights F - 2 * wt residualTotalWeights F =
          T - 3 * wt residualTotalWeights F := by omega
      have hY3 : YS - wt residualYSWeights F - 2 * wt residualYSWeights F =
          YS - 3 * wt residualYSWeights F := by omega
      have hS3 : S - wt residualSWeights F - 2 * wt residualSWeights F =
          S - 3 * wt residualSWeights F := by omega
      simpa only [hT2, hY2, hS2, hT3, hY3, hS3] using hlowOneRank
    rcases exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low
      DOneHigh DOneLow w delta TOne YOne SOne hwidthRest qTwo hqTwo
        hqTwoBox F hF hsourceRest with hfirst | hsecond | hthird
    · obtain ⟨v, hv, hH, hbox, hndvd⟩ := hfirst
      have hv' : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Subtype.ext hz
      right
      left
      refine ⟨v.1, qTwo v, hv', hH, ?_, hndvd, ?_⟩
      · calc
          F * qTwo v = qOne v :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
          _ = q v.1 := rfl
      · simpa only [DOneLow, TOne, YOne, SOne] using hbox
    · obtain ⟨v, J, hv, hJ, heq, hndvd, hbox⟩ := hsecond
      have hv' : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Subtype.ext hz
      right
      right
      left
      refine ⟨v.1, J, hv', hJ, ?_, hndvd, ?_⟩
      · calc
          F * (F * J) = F * qTwo v := by rw [heq]
          _ = qOne v :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
          _ = q v.1 := rfl
      · have hD : DOneLow - delta - wt (contactWeights w) F =
            Dlow - 2 * delta - 2 * wt (contactWeights w) F := by
          simp only [DOneLow]
          omega
        have hT : TOne - wt residualTotalWeights F =
            T - 2 * wt residualTotalWeights F := by
          simp only [TOne]
          omega
        have hY : YOne - wt residualYSWeights F =
            YS - 2 * wt residualYSWeights F := by
          simp only [YOne]
          omega
        have hS : SOne - wt residualSWeights F =
            S - 2 * wt residualSWeights F := by
          simp only [SOne]
          omega
        simpa only [hD, hT, hY, hS] using hbox
    · obtain ⟨v, J, hv, hJ, heq, hbox⟩ := hthird
      have hv' : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Subtype.ext hz
      right
      right
      right
      refine ⟨v.1, J, hv', hJ, ?_, ?_⟩
      · calc
          F * (F * (F * J)) = F * qTwo v := by rw [heq]
          _ = qOne v :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
          _ = q v.1 := rfl
      · have hD : DOneLow - 2 * delta - 2 * wt (contactWeights w) F =
            Dlow - 3 * delta - 3 * wt (contactWeights w) F := by
          simp only [DOneLow]
          omega
        have hT : TOne - 2 * wt residualTotalWeights F =
            T - 3 * wt residualTotalWeights F := by
          simp only [TOne]
          omega
        have hY : YOne - 2 * wt residualYSWeights F =
            YS - 3 * wt residualYSWeights F := by
          simp only [YOne]
          omega
        have hS : SOne - 2 * wt residualSWeights F =
            S - 3 * wt residualSWeights F := by
          simp only [SOne]
          omega
        simpa only [hD, hT, hY, hS] using hbox
  · push Not at hdivOne
    obtain ⟨v, hvdiv⟩ := hdivOne
    have hv : v.1 ≠ 0 := by
      intro hz
      apply hvdiv
      have hvzero : v = 0 := Subtype.ext hz
      rw [hvzero]
      simp only [map_zero]
      exact dvd_zero F
    have hqv : q v.1 ≠ 0 := by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    left
    refine ⟨v.1, hv, hqv, hqOneBox v, ?_⟩
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hvdiv

end LinearDichotomy

section FourthDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

theorem specialization_pderiv_R4_eq_zero_of_kernel_low_box
    (D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 4) * support.card + 4 * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (reconstruct K D w L s v.1))))) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hder4 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) ≠ 0 := by
    intro hz
    apply hne
    rw [hz, map_zero]
  have hder3 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) ≠ 0 := by
    intro hz
    exact hder4 (by rw [hz, map_zero])
  have hder2 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H) ≠ 0 := by
    intro hz
    exact hder3 (by rw [hz, map_zero])
  have hder1 : MvPolynomial.pderiv (2 : Fin 4) H ≠ 0 := by
    intro hz
    exact hder2 (by rw [hz, map_zero])
  have hH : H ≠ 0 := by
    intro hz
    exact hder1 (by rw [hz, map_zero])
  have hDlow : 0 < Dlow := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
    have h := (hlow hd).2.2
    omega
  have hweight1 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) H hder1
  have hweight2 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) hder2
  have hweight3 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H)) hder3
  have hder3weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) ≤
        Dlow - 1 - 3 * (w - 1) := by
    have hHweight : wt (contactWeights w) H ≤ Dlow - 1 :=
      ((mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow).2.2
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) +
      (w - 1) ≤ wt (contactWeights w) H at hweight1
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H)) + (w - 1) ≤
      wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) at hweight2
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H))) + (w - 1) ≤
      wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) at hweight3
    omega
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H))) P gamma w
    (Dlow - 1 - 3 * (w - 1)) hP hder3weight hne
  have hdegreeStrict :
      (RCN122.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4) H))))).natDegree <
        (m - 4) * support.card := by
    rw [RCN101.specialization_eq_ordinary]
    rw [RCN101.specialization_eq_ordinary] at hdegree
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - 4 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (MvPolynomial.pderiv (2 : Fin 4) H))))).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 4) _).mp
    have h1 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) m H
      (ContactOrderBridge.contactAtLeast_of_mem_kernel
        K D w L s m nodes u0 u1 v.1 v.2 i)
    have h2 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 1)
      (MvPolynomial.pderiv (2 : Fin 4) H) h1
    have h3 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 2)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) h2
    have h4 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 3)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) h3
    simpa only [Nat.sub_sub] using h4
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))))
    P gamma nodes u0 u1 support (m - 4) hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

theorem specialization_eq_zero_of_pderiv_R4_fourth_product
    (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K)
    (hfactorial : (24 : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hfourth : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (F * (F * (F * (F * Q)))))))) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  have hfactorialPoly : (24 : Polynomial K) ≠ 0 := by
    intro hz
    apply hfactorial
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hmul : (24 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ 4 *
      RCN319.specialization K P gamma Q = 0 := by
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hFzero,
      zero_mul, mul_zero, zero_add, add_zero, mul_add] at hfourth
    ring_nf at hfourth ⊢
    exact hfourth
  have hcoef : (24 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ 4 ≠ 0 :=
    mul_ne_zero hfactorialPoly (pow_ne_zero 4 hregular)
  exact (mul_eq_zero.mp hmul).resolve_left hcoef

end FourthDerivative

end

end ProximityPrize.SubmissionLower.LocatorFourthPowerAvoidance
