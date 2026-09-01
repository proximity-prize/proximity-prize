import ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance

namespace ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Three successive high-band projections.  The first two quotient stages
expose a coprime branch when possible; if both quotient families remain
divisible by `F`, the last branch writes the original low source as
`F * (F * J)` and places `J` below the third high band. -/
theorem exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low
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
              (S - 2 * wt residualSWeights F) <
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
      v ≠ 0 ∧ J ≠ 0 ∧ F * (F * J) = q v ∧
      J ∈ nestedCoefficientBox K
        (Dlow - 2 * delta - 2 * wt (contactWeights w) F) w
        (T - 2 * wt residualTotalWeights F)
          (YS - 2 * wt residualYSWeights F)
          (S - 2 * wt residualSWeights F)) := by
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
            (S - 2 * wt residualSWeights F) <
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
    have hhigh := hmem v.1
    have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
      have hv := v.2
      change bandOne v.1 = 0 at hv
      simpa only [bandOne, qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hv
    simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
      mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
        (q v.1) hhigh hzero
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
    have hwidthTwo : DOneHigh ≤ DOneLow + delta := by
      simp only [DOneHigh, DOneLow]
      omega
    let bandTwo :=
      (highBandMap (K := K) w DOneLow delta TOne YOne SOne).comp qTwo
    let lowTwo := LinearMap.ker bandTwo
    have hrangeTwo : Module.finrank K bandTwo.range ≤
        delta * channelCount TOne YOne SOne := by
      calc
        Module.finrank K bandTwo.range ≤
            Module.finrank K (HighBandIndex delta TOne YOne SOne → K) :=
          bandTwo.range.finrank_le
        _ = delta * channelCount TOne YOne SOne := by
          rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
    have hlowTwoRank :
        delta * channelCount
          (T - 2 * wt residualTotalWeights F)
            (YS - 2 * wt residualYSWeights F)
            (S - 2 * wt residualSWeights F) <
          Module.finrank K lowTwo := by
      have hsum := bandTwo.finrank_range_add_finrank_ker
      change Module.finrank K bandTwo.range + Module.finrank K lowTwo =
        Module.finrank K lowOne at hsum
      have hrangeTwo' : Module.finrank K bandTwo.range ≤
          delta * channelCount
            (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) := by
        simpa only [TOne, YOne, SOne] using hrangeTwo
      omega
    let qTwoLow : lowTwo →ₗ[K] MvPolynomial (Fin 4) K :=
      qTwo.comp lowTwo.subtype
    have hqTwoLow : Function.Injective qTwoLow := by
      intro a b hab
      apply Subtype.ext
      apply hqTwo
      simpa only [qTwoLow, LinearMap.comp_apply, Submodule.coe_subtype] using hab
    have hqTwoLowBox : ∀ v : lowTwo,
        qTwoLow v ∈ nestedCoefficientBox K DOneLow w TOne YOne SOne := by
      intro v
      have hhigh := hqTwoBox v.1
      have hzero : highBandMap w DOneLow delta TOne YOne SOne
          (qTwo v.1) = 0 := by
        have hv := v.2
        change bandTwo v.1 = 0 at hv
        simpa only [bandTwo, qTwoLow, LinearMap.comp_apply,
          Submodule.coe_subtype] using hv
      exact mem_low_of_highBandMap_eq_zero DOneHigh DOneLow w delta
        TOne YOne SOne hwidthTwo (qTwo v.1) hhigh hzero
    by_cases hdivTwo : ∀ v : lowTwo, F ∣ qTwoLow v
    · let qThree := quotientLinear qTwoLow F hF hdivTwo
      have hqThree : Function.Injective qThree :=
        quotientLinear_injective qTwoLow hqTwoLow F hF hdivTwo
      have hqThreeBox : ∀ v : lowTwo,
          qThree v ∈ nestedCoefficientBox K
            (DOneLow - wt (contactWeights w) F) w
            (TOne - wt residualTotalWeights F)
            (YOne - wt residualYSWeights F)
            (SOne - wt residualSWeights F) := by
        intro v
        by_cases hv : v = 0
        · subst v
          rw [map_zero]
          exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
        · have hqTwoV : qTwoLow v ≠ 0 := by
            intro hz
            apply hv
            apply hqTwoLow
            simpa only [map_zero] using hz
          have hqThreeV : qThree v ≠ 0 := by
            intro hz
            apply hqTwoV
            rw [recon_eq_mul_quotientPolynomial qTwoLow F hdivTwo v]
            change F * qThree v = 0
            rw [hz, mul_zero]
          exact quotient_mem_nestedCoefficientBox_of_mul_eq
            (qTwoLow v) F (qThree v) DOneLow w TOne YOne SOne
              hqTwoV hF hqThreeV (hqTwoLowBox v)
              (recon_eq_mul_quotientPolynomial qTwoLow F hdivTwo v)
      let TTwo := T - 2 * wt residualTotalWeights F
      let YTwo := YS - 2 * wt residualYSWeights F
      let STwo := S - 2 * wt residualSWeights F
      let DTwoHigh := Dlow - delta - 2 * wt (contactWeights w) F
      let DTwoLow := Dlow - 2 * delta - 2 * wt (contactWeights w) F
      have hwidthThree : DTwoHigh ≤ DTwoLow + delta := by
        simp only [DTwoHigh, DTwoLow]
        omega
      have hqThreeBox' : ∀ v : lowTwo,
          qThree v ∈ nestedCoefficientBox K DTwoHigh w TTwo YTwo STwo := by
        intro v
        have hD : DOneLow - wt (contactWeights w) F = DTwoHigh := by
          simp only [DOneLow, DTwoHigh]
          omega
        have hT : TOne - wt residualTotalWeights F = TTwo := by
          simp only [TOne, TTwo]
          omega
        have hY : YOne - wt residualYSWeights F = YTwo := by
          simp only [YOne, YTwo]
          omega
        have hS : SOne - wt residualSWeights F = STwo := by
          simp only [SOne, STwo]
          omega
        simpa only [hD, hT, hY, hS] using hqThreeBox v
      obtain ⟨v, hv, hJ, hJbox⟩ := exists_nonzero_image_mem_low
        DTwoHigh DTwoLow w delta TTwo YTwo STwo hwidthThree qThree hqThree
        hqThreeBox' hlowTwoRank
      right
      right
      refine ⟨v.1.1, qThree v, ?_, hJ, ?_, ?_⟩
      · intro hz
        apply hv
        apply Subtype.ext
        exact Subtype.ext hz
      · calc
          F * (F * qThree v) = F * qTwoLow v := by
            congr 1
            exact (recon_eq_mul_quotientPolynomial qTwoLow F hdivTwo v).symm
          _ = qOne v.1 := by
            exact (recon_eq_mul_quotientPolynomial qOne F hdivOne v.1).symm
          _ = q v.1.1 := rfl
      · simpa only [DTwoLow, TTwo, YTwo, STwo] using hJbox
    · push Not at hdivTwo
      obtain ⟨v, hvdiv⟩ := hdivTwo
      have hv : v.1.1 ≠ 0 := by
        intro hz
        apply hvdiv
        have hvzero : v = 0 := by
          apply Subtype.ext
          exact Subtype.ext hz
        rw [hvzero]
        simp only [map_zero]
        exact dvd_zero F
      have hH : qTwoLow v ≠ 0 := by
        intro hz
        apply hvdiv
        rw [hz]
        exact dvd_zero F
      right
      left
      refine ⟨v.1.1, qTwoLow v, hv, hH, ?_, hvdiv, ?_⟩
      · calc
          F * qTwoLow v = qOne v.1 :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v.1).symm
          _ = q v.1.1 := rfl
      · simpa only [DOneLow, TOne, YOne, SOne] using hqTwoLowBox v
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

section ThirdDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

/-- A third `R`-derivative of a low kernel reconstruction specializes to zero
once the residual contact order and the global weighted-degree cap leave room
for the usual root-counting argument. -/
theorem specialization_pderiv_R3_eq_zero_of_kernel_low_box
    (D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 3) * support.card + 3 * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (reconstruct K D w L s v.1)))) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hder3 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) ≠ 0 := by
    intro hz
    apply hne
    change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) = 0
    rw [hz, map_zero]
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
  have hcaps := (mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow
  have hweight1 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) H hder1
  have hder1weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4) H) ≤ Dlow - 1 - (w - 1) := by
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) +
      (w - 1) ≤ wt (contactWeights w) H at hweight1
    omega
  have hweight2 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) hder2
  have hder2weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) ≤
        Dlow - 1 - 2 * (w - 1) := by
    change wt (contactWeights w)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H)) + (w - 1) ≤
      wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) at hweight2
    omega
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H)) P gamma w
    (Dlow - 1 - 2 * (w - 1)) hP hder2weight hne
  have hdegreeStrict :
      (RCN122.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)))).natDegree <
        (m - 3) * support.card := by
    rw [RCN101.specialization_eq_ordinary]
    rw [RCN101.specialization_eq_ordinary] at hdegree
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - 3 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4) H)))).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 3) _).mp
    have hfirst := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) m H
      (ContactOrderBridge.contactAtLeast_of_mem_kernel
        K D w L s m nodes u0 u1 v.1 v.2 i)
    have hsecond := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 1)
      (MvPolynomial.pderiv (2 : Fin 4) H) hfirst
    have hthird := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 2)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) hsecond
    simpa only [Nat.sub_sub] using hthird
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)))
    P gamma nodes u0 u1 support (m - 3) hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

/-- On the specialization where `F` itself vanishes, the third product-rule
derivative of `F³ Q` is `6 * (∂ᴿ F)³ * Q`.  Thus regularity of the
chosen factor and nonvanishing of `6` force the specialization of `Q` to
vanish. -/
theorem specialization_eq_zero_of_pderiv_R3_cube_product
    (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K)
    (hsix : (6 : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hthird : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) (F * (F * (F * Q)))))) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  have hsixPoly : (6 : Polynomial K) ≠ 0 := by
    intro hz
    apply hsix
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hmul : (6 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) *
      RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) *
      RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) *
      RCN319.specialization K P gamma Q = 0 := by
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hFzero,
      zero_mul, mul_zero, zero_add, add_zero, mul_add] at hthird
    ring_nf at hthird ⊢
    exact hthird
  have hcoef : (6 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) *
      RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) *
      RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ≠ 0 :=
    mul_ne_zero hsixPoly
      (mul_ne_zero (mul_ne_zero hregular hregular) hregular)
  exact (mul_eq_zero.mp hmul).resolve_left hcoef

end ThirdDerivative

end

end ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance
