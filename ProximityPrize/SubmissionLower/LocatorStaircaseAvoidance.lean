import ProximityPrize.SubmissionLower.LocatorSquareAvoidance
import ProximityPrize.SubmissionLower.LocatorCoprimeQuotient

namespace ProximityPrize.SubmissionLower.LocatorStaircaseAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN122 RCN130 RCN156 RCN180 RCN234 RCN260
  LocatorLowQuotient

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

/-- A conditional two-step high-band projection.  We pay the second band only
when every vector surviving the first band is still divisible by `F`.  In that
case division by `F` is linear on the first kernel, and square avoidance on the
smaller quotient space excludes a third copy of `F`. -/
theorem exists_nonzero_image_mem_staircase_not_dvd
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Dhigh Dmid Dlow w delta T YS S cubeBound : ℕ)
    (hwidth₁ : Dhigh ≤ Dmid + delta)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hwidth₂ : Dmid - wt (contactWeights w) F ≤ Dlow + delta)
    (hcube : coefficientCount (Dlow - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F - wt residualTotalWeights F)
        (S - wt residualSWeights F - wt residualSWeights F) ≤ cubeBound)
    (hsource :
      delta * channelCount T YS S +
          delta * channelCount
            (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) +
          cubeBound < Module.finrank K V) :
    (∃ v : V, v ≠ 0 ∧ q v ≠ 0 ∧
      q v ∈ nestedCoefficientBox K Dmid w T YS S ∧ ¬ F ∣ q v) ∨
    (∃ (v : V) (R : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ R ≠ 0 ∧ q v = F * R ∧
      R ∈ nestedCoefficientBox K Dlow w
        (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
          (S - wt residualSWeights F) ∧ ¬ F ∣ R) := by
  classical
  let band := (highBandMap (K := K) w Dmid delta T YS S).comp q
  let low := LinearMap.ker band
  have hrange : Module.finrank K band.range ≤
      delta * channelCount T YS S := by
    calc
      Module.finrank K band.range ≤
          Module.finrank K (HighBandIndex delta T YS S → K) :=
        band.range.finrank_le
      _ = delta * channelCount T YS S := by
        rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
  let qlow : low →ₗ[K] MvPolynomial (Fin 4) K := q.comp low.subtype
  have hqlow : Function.Injective qlow := by
    intro a b hab
    apply Subtype.ext
    apply hq
    simpa only [qlow, LinearMap.comp_apply, Submodule.coe_subtype] using hab
  let bad : Submodule K low := {
    carrier := {v | F ∣ qlow v}
    zero_mem' := by simp [qlow]
    add_mem' := by
      intro a b ha hb
      change F ∣ qlow (a + b)
      rw [map_add]
      exact dvd_add ha hb
    smul_mem' := by
      intro a v hv
      change F ∣ qlow (a • v)
      rw [map_smul, MvPolynomial.smul_eq_C_mul]
      exact dvd_mul_of_dvd_right hv _ }
  by_cases hbad : bad = ⊤
  · have hdiv : ∀ v : low, F ∣ qlow v := by
      intro v
      have hv : v ∈ bad := by rw [hbad]; trivial
      exact hv
    let r := quotientLinear qlow F hF hdiv
    have hrinj : Function.Injective r :=
      quotientLinear_injective qlow hqlow F hF hdiv
    have hqproduct (v : low) : qlow v = F * r v :=
      recon_eq_mul_quotientPolynomial qlow F hdiv v
    have hrNested : ∀ v : low,
        r v ∈ nestedCoefficientBox K
          (Dmid - wt (contactWeights w) F) w
          (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
      intro v
      by_cases hv : v = 0
      · subst v
        simpa only [map_zero] using
          (nestedCoefficientBox K
            (Dmid - wt (contactWeights w) F) w
            (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
              (S - wt residualSWeights F)).zero_mem
      · have hqv : qlow v ≠ 0 := by
          intro hz
          apply hv
          apply hqlow
          simpa only [map_zero] using hz
        have hhigh : qlow v ∈ nestedCoefficientBox K Dhigh w T YS S := by
          simpa only [qlow, LinearMap.comp_apply, Submodule.coe_subtype] using
            hmem v.1
        have hzero : highBandMap w Dmid delta T YS S (qlow v) = 0 := by
          have hvker := v.2
          change band v.1 = 0 at hvker
          simpa only [band, qlow, LinearMap.comp_apply,
            Submodule.coe_subtype] using hvker
        have hmid : qlow v ∈ nestedCoefficientBox K Dmid w T YS S :=
          mem_low_of_highBandMap_eq_zero Dhigh Dmid w delta T YS S hwidth₁
            (qlow v) hhigh hzero
        have hrnonzero : r v ≠ 0 := by
          intro hz
          exact hqv (by rw [hqproduct v, hz, mul_zero])
        have hrbox : r v ∈ globalCoefficientBox K
            (Dmid - wt (contactWeights w) F) w
            (T - wt residualTotalWeights F) (S - wt residualSWeights F) :=
          quotient_mem_flagGlobalCoefficientBox_of_mul_eq
            (qlow v) F (r v) Dmid w T S
            (wt (contactWeights w) F) (wt residualTotalWeights F)
            (wt residualSWeights F) hqv hF hrnonzero
            (nested_mem_global hmid) (hqproduct v) le_rfl le_rfl le_rfl
        have hrYS : wt residualYSWeights (r v) ≤
            YS - wt residualYSWeights F := by
          have hqYS := (nested_mem_weights hmid hqv).2.1
          have hmul := weightedTotalDegree_mul residualYSWeights F (r v) hF hrnonzero
          rw [← hqproduct v] at hmul
          simp only [wt] at hqYS ⊢
          omega
        intro d hd
        have hb := hrbox hd
        have hy :=
          (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans hrYS
        rw [weight_fin4] at hy
        simp only [residualYSWeights] at hy
        refine ⟨hb.1, ?_, hb.2.1, hb.2.2⟩
        simpa [residualYSWeights] using hy
    have hlowrank :
        delta * channelCount
            (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) + cubeBound <
          Module.finrank K low := by
      have hsum := band.finrank_range_add_finrank_ker
      change Module.finrank K band.range + Module.finrank K low =
        Module.finrank K V at hsum
      omega
    obtain ⟨v, hv, hR, hRlow, hnot⟩ :=
      LocatorSquareAvoidance.exists_nonzero_image_mem_low_not_dvd
        (Dmid - wt (contactWeights w) F) Dlow w delta
        (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
        (S - wt residualSWeights F) cubeBound hwidth₂ r hrinj hrNested
        F hF hcube hlowrank
    right
    refine ⟨v.1, r v, ?_, hR, ?_, hRlow, hnot⟩
    · intro hz
      apply hv
      exact Subtype.ext hz
    · simpa only [qlow, LinearMap.comp_apply, Submodule.coe_subtype] using
        hqproduct v
  · have hex : ∃ v : low, v ∉ bad := by
      by_contra hn
      apply hbad
      ext v
      simp only [Submodule.mem_top, iff_true]
      by_contra hv
      exact hn ⟨v, hv⟩
    obtain ⟨v, hvbad⟩ := hex
    have hv : v.1 ≠ 0 := by
      intro hz
      apply hvbad
      have hv0 : v = 0 := Subtype.ext hz
      rw [hv0]
      exact bad.zero_mem
    have hqv : q v.1 ≠ 0 := by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    have hhigh : q v.1 ∈ nestedCoefficientBox K Dhigh w T YS S := hmem v.1
    have hzero : highBandMap w Dmid delta T YS S (q v.1) = 0 := by
      have hvker := v.2
      change band v.1 = 0 at hvker
      simpa only [band, LinearMap.comp_apply, Submodule.coe_subtype] using hvker
    have hmid : q v.1 ∈ nestedCoefficientBox K Dmid w T YS S :=
      mem_low_of_highBandMap_eq_zero Dhigh Dmid w delta T YS S hwidth₁
        (q v.1) hhigh hzero
    left
    refine ⟨v.1, hv, hqv, hmid, ?_⟩
    change ¬ F ∣ qlow v at hvbad
    simpa only [qlow, LinearMap.comp_apply, Submodule.coe_subtype] using hvbad

/-- Two contact derivatives vanish after lowering the reconstructed parent by
two agreement bands.  This is the second-order analogue of
`specialization_pderiv_R_eq_zero_of_kernel_low_box`. -/
theorem specialization_second_pderiv_R_eq_zero_of_kernel_low_box
    [Fintype I]
    (D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈
      globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 2) * support.card + 2 * (w - 1))
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (reconstruct K D w L s v.1))) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hH : H ≠ 0 := by
    intro hz
    apply hne
    simp only [H, hz, map_zero]
  have hfirst : MvPolynomial.pderiv (2 : Fin 4) H ≠ 0 := by
    intro hz
    apply hne
    rw [hz]
    change RCN319.specialization K P gamma 0 = 0
    exact map_zero _
  have hDlow : 0 < Dlow := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
    have h := (hlow hd).2.2
    omega
  have hcaps :=
    (mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow
  have hfirstWeight :
      wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) ≤
        Dlow - 1 - (w - 1) := by
    have h := wt_pderiv_le (contactWeights w) H (2 : Fin 4)
      (Dlow - 1) hcaps.2.2
    have hweight : contactWeights w (2 : Fin 4) = w - 1 := by rfl
    rw [hweight] at h
    exact h
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree
    K (MvPolynomial.pderiv (2 : Fin 4) H) P gamma w
      (Dlow - 1 - (w - 1))
      hP hfirstWeight hne
  rw [RCN101.specialization_eq_ordinary] at hdegree
  have hdegreeStrict :
      (RCN122.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))).natDegree <
        (m - 2) * support.card := by
    rw [RCN101.specialization_eq_ordinary]
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - 2 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H))).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 2) _).mp
    have hone := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) m H
      (ContactOrderBridge.contactAtLeast_of_mem_kernel
        K D w L s m nodes u0 u1 v.1 v.2 i)
    have htwo := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 1)
      (MvPolynomial.pderiv (2 : Fin 4) H) hone
    simpa only [Nat.sub_sub] using htwo
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H))
    P gamma nodes u0 u1 support (m - 2) hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

/-- On a regular component, vanishing of the second contact derivative of
`F * (F * R)` forces `R` itself to vanish after specialization.  The two
surviving Leibniz terms are equal, and the characteristic assumption makes
their coefficient `2` cancellable. -/
theorem regularSeeds_count_le_intersection_of_square_product
    (P : UnequalParameters) (H R : MvPolynomial (Fin 4) K)
    (F : RCN266.RegularIndex H) (hrel : IsRelPrime F.1 R)
    (p : ℕ) [CharP K p] (htwo : 2 < p)
    (hFY : F.1.degreeOf 1 ≤ P.leftY) (hFR : F.1.degreeOf 2 ≤ P.leftR)
    (hFZ : F.1.degreeOf 3 ≤ P.leftZ)
    (hRY : R.degreeOf 1 ≤ P.rightY) (hRR : R.degreeOf 2 ≤ P.rightR)
    (hRZ : R.degreeOf 3 ≤ P.rightZ)
    (hleftR : 1 ≤ P.leftR)
    (hleftYSmall : P.leftY < p) (hleftRSmall : P.leftR < p)
    (hleftZSmall : P.leftZ < p)
    (hmixedYSmall : P.mixedCost.y < p) (hmixedRSmall : P.mixedCost.r < p)
    (hmixedZSmall : P.mixedCost.z < p)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = P.n)
    (hw : 1 ≤ P.w) (hchar : P.w < p) (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma, P.a ≤
      (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma P.w P.errors)
    (hproduct : ∀ gamma ∈ RCN140.regularSeeds (K := K) H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) (F.1 * (F.1 * R)))) = 0) :
    (RCN140.regularSeeds (K := K) H selected Gamma F).card ≤ P.regularCountCap := by
  classical
  apply LocatorCoprimeQuotient.regularSeeds_count_le_intersection
    P H R F hrel p
    hFY hFR hFZ hRY hRR hRZ hleftR
    hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hw hchar hwa han
    hdegree hagreement hno
  intro gamma hgamma
  obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
  let b := RCN319.specialization K (selected gamma) gamma
    (MvPolynomial.pderiv (2 : Fin 4) F.1)
  let r := RCN319.specialization K (selected gamma) gamma R
  have hsum : b * b * r + b * b * r = 0 := by
    simpa only [MvPolynomial.pderiv_mul, map_add, map_mul,
      hFzero, zero_mul, mul_zero, zero_add, add_zero, mul_assoc, b, r] using
        hproduct gamma hgamma
  have htwoK : (2 : K) ≠ 0 := by
    intro hc
    exact (Nat.not_dvd_of_pos_of_lt (by omega) htwo)
      ((CharP.cast_eq_zero_iff K p 2).mp hc)
  have htwoPoly : (2 : Polynomial K) ≠ 0 := by
    intro hc
    apply htwoK
    have hc₀ := congrArg (fun f : Polynomial K => f.coeff 0) hc
    simpa only [Polynomial.coeff_ofNat_zero, Polynomial.coeff_zero] using hc₀
  have hterm : b * b * r = 0 := by
    have htwice : (2 : Polynomial K) * (b * b * r) = 0 := by
      simpa only [two_mul] using hsum
    exact (mul_eq_zero.mp htwice).resolve_left htwoPoly
  exact (mul_eq_zero.mp hterm).resolve_left (mul_ne_zero hregular hregular)

end

end ProximityPrize.SubmissionLower.LocatorStaircaseAvoidance
