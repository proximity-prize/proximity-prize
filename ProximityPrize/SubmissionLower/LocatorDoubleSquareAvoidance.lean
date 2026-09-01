import ProximityPrize.SubmissionLower.LocatorLowQuotient
import ProximityPrize.SubmissionLower.LocatorCoprimeQuotient

namespace ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

theorem quotient_mem_nestedCoefficientBox_of_mul_eq
    (P F Q : MvPolynomial (Fin 4) K) (D w T YS S : ℕ)
    (hP : P ≠ 0) (hF : F ≠ 0) (hQ : Q ≠ 0)
    (hbox : P ∈ nestedCoefficientBox K D w T YS S)
    (heq : P = F * Q) :
    Q ∈ nestedCoefficientBox K
      (D - wt (contactWeights w) F) w
      (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
      (S - wt residualSWeights F) := by
  have hglobal :
      Q ∈ globalCoefficientBox K
        (D - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (S - wt residualSWeights F) :=
    quotient_mem_flagGlobalCoefficientBox_of_mul_eq P F Q D w T S
      (wt (contactWeights w) F) (wt residualTotalWeights F)
      (wt residualSWeights F) hP hF hQ (nested_mem_global hbox) heq
      le_rfl le_rfl le_rfl
  have hPYS : wt residualYSWeights P ≤ YS :=
    (nested_mem_weights hbox hP).2.1
  have hmul := weightedTotalDegree_mul residualYSWeights F Q hF hQ
  have hsum : wt residualYSWeights F + wt residualYSWeights Q ≤ YS := by
    change MvPolynomial.weightedTotalDegree residualYSWeights F +
      MvPolynomial.weightedTotalDegree residualYSWeights Q ≤ YS
    rw [← hmul, ← heq]
    exact hPYS
  have hQYS : wt residualYSWeights Q ≤ YS - wt residualYSWeights F := by
    omega
  intro d hd
  have hb := hglobal hd
  have hy := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at hy
  simp only [wt] at hQYS
  simp only [residualYSWeights] at hy ⊢
  refine ⟨hb.1, ?_, hb.2.1, hb.2.2⟩
  change d 1 + d 2 ≤ YS -
    MvPolynomial.weightedTotalDegree residualYSWeights F
  simpa [residualYSWeights] using hy.trans hQYS

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Apply the contact high-band projection to `q` and, only if every first-low
quotient is still divisible by `F`, divide once more and apply a second
high-band projection.  The second branch therefore pays for a second band,
not for the entire square-divisible coefficient box. -/
theorem exists_first_low_not_dvd_or_second_low
    (Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hsource :
      delta * channelCount T YS S +
          delta * channelCount
            (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) <
        Module.finrank K V) :
    (∃ v : V, v ≠ 0 ∧ q v ≠ 0 ∧
      q v ∈ nestedCoefficientBox K Dlow w T YS S ∧ ¬ F ∣ q v) ∨
    (∃ (v : V) (H : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ H ≠ 0 ∧ F * H = q v ∧
      H ∈ nestedCoefficientBox K (Dlow - delta - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
          (S - wt residualSWeights F)) := by
  classical
  let band := (highBandMap (K := K) w Dlow delta T YS S).comp q
  let low := LinearMap.ker band
  have hrange : Module.finrank K band.range ≤ delta * channelCount T YS S := by
    calc
      Module.finrank K band.range ≤
          Module.finrank K (HighBandIndex delta T YS S → K) :=
        band.range.finrank_le
      _ = delta * channelCount T YS S := by
        rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
  have hlowrank :
      delta * channelCount
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) <
        Module.finrank K low := by
    have hsum := band.finrank_range_add_finrank_ker
    change Module.finrank K band.range + Module.finrank K low =
      Module.finrank K V at hsum
    omega
  let qlow : low →ₗ[K] MvPolynomial (Fin 4) K := q.comp low.subtype
  have hqlow : Function.Injective qlow := by
    intro a b hab
    apply Subtype.ext
    apply hq
    simpa only [qlow, LinearMap.comp_apply, Submodule.coe_subtype] using hab
  by_cases hdiv : ∀ v : low, F ∣ qlow v
  · let qtwo := quotientLinear qlow F hF hdiv
    have hqtwo : Function.Injective qtwo :=
      quotientLinear_injective qlow hqlow F hF hdiv
    have hqbox : ∀ v : low,
        qlow v ∈ nestedCoefficientBox K Dlow w T YS S := by
      intro v
      have hhigh : q v.1 ∈ nestedCoefficientBox K Dhigh w T YS S := hmem v.1
      have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
        have hv := v.2
        change band v.1 = 0 at hv
        simpa only [band, qlow, LinearMap.comp_apply, Submodule.coe_subtype] using hv
      simpa only [qlow, LinearMap.comp_apply, Submodule.coe_subtype] using
        mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
          (q v.1) hhigh hzero
    have htwoBox : ∀ v : low,
        qtwo v ∈ nestedCoefficientBox K (Dlow - wt (contactWeights w) F) w
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
      intro v
      by_cases hv : v = 0
      · subst v
        rw [map_zero]
        exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
      · have hqlowv : qlow v ≠ 0 := by
          intro hz
          apply hv
          apply hqlow
          simpa only [map_zero] using hz
        have hqtwoV : qtwo v ≠ 0 := by
          intro hz
          apply hqlowv
          rw [recon_eq_mul_quotientPolynomial qlow F hdiv v]
          change F * qtwo v = 0
          rw [hz, mul_zero]
        exact quotient_mem_nestedCoefficientBox_of_mul_eq
          (qlow v) F (qtwo v) Dlow w T YS S hqlowv hF hqtwoV (hqbox v)
            (recon_eq_mul_quotientPolynomial qlow F hdiv v)
    have hwidthTwo : Dlow - wt (contactWeights w) F ≤
        (Dlow - delta - wt (contactWeights w) F) + delta := by omega
    obtain ⟨v, hv, hH, hHbox⟩ := exists_nonzero_image_mem_low
      (Dlow - wt (contactWeights w) F)
      (Dlow - delta - wt (contactWeights w) F) w delta
      (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
      (S - wt residualSWeights F) hwidthTwo qtwo hqtwo htwoBox hlowrank
    right
    refine ⟨v.1, qtwo v, ?_, hH, ?_, hHbox⟩
    · intro hz
      apply hv
      exact Subtype.ext hz
    · change F * quotientPolynomial qlow F hdiv v = qlow v
      exact (recon_eq_mul_quotientPolynomial qlow F hdiv v).symm
  · push Not at hdiv
    obtain ⟨v, hvdiv⟩ := hdiv
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
    have hhigh : q v.1 ∈ nestedCoefficientBox K Dhigh w T YS S := hmem v.1
    have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
      have hvker := v.2
      change band v.1 = 0 at hvker
      simpa only [band, LinearMap.comp_apply, Submodule.coe_subtype] using hvker
    left
    refine ⟨v.1, hv, hqv,
      mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
        (q v.1) hhigh hzero, ?_⟩
    simpa only [qlow, LinearMap.comp_apply, Submodule.coe_subtype] using hvdiv

end LinearDichotomy

section SecondDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

theorem specialization_pderiv_R2_eq_zero_of_kernel_low_box
    (D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 2) * support.card + 2 * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) (reconstruct K D w L s v.1))) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hder2 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H) ≠ 0 := by
    intro hz
    apply hne
    change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.pderiv (2 : Fin 4) H)) = 0
    rw [hz, map_zero]
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
  have hweight := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) H hder1
  have hder1weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4) H) ≤ Dlow - 1 - (w - 1) := by
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) +
      (w - 1) ≤ wt (contactWeights w) H at hweight
    omega
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (MvPolynomial.pderiv (2 : Fin 4) H) P gamma w (Dlow - 1 - (w - 1))
    hP hder1weight hne
  have hdegreeStrict :
      (RCN122.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.pderiv (2 : Fin 4) H))).natDegree <
        (m - 2) * support.card := by
    rw [RCN101.specialization_eq_ordinary]
    rw [RCN101.specialization_eq_ordinary] at hdegree
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - 2 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H))).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 2) _).mp
    have hfirst := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) m H
      (ContactOrderBridge.contactAtLeast_of_mem_kernel
        K D w L s m nodes u0 u1 v.1 v.2 i)
    have hsecond := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 1)
      (MvPolynomial.pderiv (2 : Fin 4) H) hfirst
    simpa only [Nat.sub_sub] using hsecond
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.pderiv (2 : Fin 4) H))
    P gamma nodes u0 u1 support (m - 2) hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

theorem specialization_eq_zero_of_pderiv_R2_square_product
    (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K)
    (htwo : (2 : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hsecond : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) (F * (F * Q)))) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  have htwoPoly : (2 : Polynomial K) ≠ 0 := by
    intro hz
    apply htwo
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hmul : (2 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) *
      RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) *
      RCN319.specialization K P gamma Q = 0 := by
    simpa only [MvPolynomial.pderiv_mul, map_add, map_mul, hFzero,
      zero_mul, mul_zero, zero_add, add_zero, two_mul, add_mul, mul_assoc] using hsecond
  have hcoef : (2 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) *
      RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ≠ 0 :=
    mul_ne_zero htwoPoly (mul_ne_zero hregular hregular)
  exact (mul_eq_zero.mp hmul).resolve_left hcoef

end SecondDerivative

end

end ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance
