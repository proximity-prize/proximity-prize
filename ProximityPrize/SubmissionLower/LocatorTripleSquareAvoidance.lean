import ProximityPrize.SubmissionLower.LocatorLowQuotient
import ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
import ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance

namespace ProximityPrize.SubmissionLower.LocatorTripleSquareAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient LocatorDoubleSquareAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

section LinearTrichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Apply the contact high-band projection to `q`.  If some first-low quotient
is not divisible by `F`, stop with one copy.  Otherwise divide once and apply
the two-branch dichotomy to the divided family, so the second branch pays for
a second band and the third branch pays for a third band. -/
theorem exists_low_not_dvd_or_squares
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
            (T - wt residualTotalWeights F - wt residualTotalWeights F)
            (YS - wt residualYSWeights F - wt residualYSWeights F)
            (S - wt residualSWeights F - wt residualSWeights F) <
        Module.finrank K V) :
    (∃ v : V, v ≠ 0 ∧ q v ≠ 0 ∧
      q v ∈ nestedCoefficientBox K Dlow w T YS S ∧ ¬ F ∣ q v) ∨
    (∃ (v : V) (H : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ H ≠ 0 ∧ F * H = q v ∧
      H ∈ nestedCoefficientBox K (Dlow - delta - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
          (S - wt residualSWeights F) ∧ ¬ F ∣ H) ∨
    (∃ (v : V) (H : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ H ≠ 0 ∧ F * (F * H) = q v ∧
      H ∈ nestedCoefficientBox K
        (Dlow - delta - wt (contactWeights w) F - delta -
          wt (contactWeights w) F) w
        (T - wt residualTotalWeights F - wt residualTotalWeights F)
        (YS - wt residualYSWeights F - wt residualYSWeights F)
        (S - wt residualSWeights F - wt residualSWeights F)) := by
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
            (S - wt residualSWeights F) +
        delta * channelCount
          (T - wt residualTotalWeights F - wt residualTotalWeights F)
          (YS - wt residualYSWeights F - wt residualYSWeights F)
          (S - wt residualSWeights F - wt residualSWeights F) <
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
    have hsourceTwo :
        delta * channelCount
            (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) +
          delta * channelCount
            (T - wt residualTotalWeights F - wt residualTotalWeights F)
            (YS - wt residualYSWeights F - wt residualYSWeights F)
            (S - wt residualSWeights F - wt residualSWeights F) <
          Module.finrank K low := hlowrank
    rcases exists_first_low_not_dvd_or_second_low
        (Dlow - wt (contactWeights w) F)
        (Dlow - delta - wt (contactWeights w) F) w delta
        (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
        (S - wt residualSWeights F)
        hwidthTwo qtwo hqtwo htwoBox F hF hsourceTwo with hone|htwo
    · obtain ⟨v, hv, hQ, hQbox, hnot⟩ := hone
      right; left
      refine ⟨v.1, qtwo v, ?_, hQ, ?_, hQbox, hnot⟩
      · intro hz
        apply hv
        exact Subtype.ext hz
      · change F * quotientPolynomial qlow F hdiv v = qlow v
        exact (recon_eq_mul_quotientPolynomial qlow F hdiv v).symm
    · obtain ⟨v, H, hv, hH, hFH, hHbox⟩ := htwo
      right; right
      refine ⟨v.1, H, ?_, hH, ?_, hHbox⟩
      · intro hz
        apply hv
        exact Subtype.ext hz
      · have hqv : F * qtwo v = qlow v :=
          (recon_eq_mul_quotientPolynomial qlow F hdiv v).symm
        calc
          F * (F * H) = F * qtwo v := by rw [hFH]
          _ = qlow v := hqv
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

end LinearTrichotomy

section ThirdDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

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
          (MvPolynomial.pderiv (2 : Fin 4) (reconstruct K D w L s v.1)))) = 0 := by
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
  have hweightA := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) H hder1
  have hweightB := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) hder2
  have hder2weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.pderiv (2 : Fin 4) H)) ≤
        Dlow - 1 - (w - 1) - (w - 1) := by
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) +
      (w - 1) ≤ wt (contactWeights w) H at hweightA
    change wt (contactWeights w)
        (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.pderiv (2 : Fin 4) H)) +
      (w - 1) ≤ wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H)
      at hweightB
    omega
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.pderiv (2 : Fin 4) H))
    P gamma w (Dlow - 1 - (w - 1) - (w - 1))
    hP hder2weight hne
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
      K (nodes i) (u0 i) (u1 i) (m - 1 - 1)
      (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.pderiv (2 : Fin 4) H))
      hsecond
    simpa only [Nat.sub_sub] using hthird
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.pderiv (2 : Fin 4) H)))
    P gamma nodes u0 u1 support (m - 3) hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

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
      (RCN319.specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) F) *
        (RCN319.specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) F) *
          RCN319.specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) F))) *
      RCN319.specialization K P gamma Q = 0 := by
    have h := hthird
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hFzero,
      zero_mul, mul_zero, zero_add, add_zero] at h
    linear_combination h
  have hcoef : (6 : Polynomial K) *
      (RCN319.specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) F) *
        (RCN319.specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) F) *
          RCN319.specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) F))) ≠ 0 :=
    mul_ne_zero hsixPoly (mul_ne_zero hregular (mul_ne_zero hregular hregular))
  exact (mul_eq_zero.mp hmul).resolve_left hcoef

end ThirdDerivative

end

end ProximityPrize.SubmissionLower.LocatorTripleSquareAvoidance
