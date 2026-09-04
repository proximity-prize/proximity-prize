import ProximityPrize.SubmissionLower.LocatorLowQuotient

/-! Packed from ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance. -/
section PackedLocator_LocatorFifthPowerAvoidance

namespace ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
open scoped Classical BigOperators
open UniqueFactorizationMonoid RCN081 RCN156 RCN234 RCN260
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
theorem isRelPrime_of_weight_lt (weights:Fin 4 → ℕ)
    (F Q:MvPolynomial (Fin 4) K) (hF:Irreducible F) (hQ:Q ≠ 0)
    (hlt:wt weights Q < wt weights F):IsRelPrime F Q:=by
  apply hF.isRelPrime_iff_not_dvd.mpr
  intro hdiv
  exact (not_lt_of_ge (weightedTotalDegree_le_of_dvd weights F Q hdiv hQ)) hlt
theorem isRelPrime_of_weight_sub_bound (weights:Fin 4 → ℕ)
    (F Q:MvPolynomial (Fin 4) K) (hF:Irreducible F) (hQ:Q ≠ 0)
    (B:ℕ) (hbound:wt weights Q ≤ B - wt weights F)
    (hhalf:B < 2 * wt weights F):IsRelPrime F Q:=by
  apply isRelPrime_of_weight_lt weights F Q hF hQ
  omega
private theorem regular_mem_normalizedFactors
    (H:MvPolynomial (Fin 4) K) (F:RCN266.RegularIndex H) :
    F.1 ∈ normalizedFactors H:=by
  have hactive:F.1 ∈ RCN082.activeFactors H :=
    (Finset.mem_filter.mp F.2).1
  have hnf:F.1 ∈ (normalizedFactors H).toFinset :=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf
def regularIndexSelf (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):RCN052.RegularIndex F.1:=by
  have hF:=RCN167.positiveRFactors_spec H F.1 F.2
  refine ⟨F.1, ?_⟩
  change F.1 ∈ (RCN082.activeFactors F.1).filter (fun G => 0 < G.degreeOf 2)
  refine Finset.mem_filter.mpr ⟨?_, hF.2.2⟩
  change F.1 ∈ (normalizedFactors F.1).toFinset.filter
    (fun G => 0 < G.degreeOf 1 + G.degreeOf 2 + G.degreeOf 3)
  refine Finset.mem_filter.mpr ⟨?_, by omega⟩
  apply Multiset.mem_toFinset.mpr
  rw [normalizedFactors_irreducible hF.1,
    normalize_normalized_factor F.1 (regular_mem_normalizedFactors H F)]
  exact Multiset.mem_singleton_self _
@[simp] theorem regularIndexSelf_val (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):(regularIndexSelf H F).1 = F.1:=rfl
theorem regularVector_le_mixedCost (P:UnequalParameters)
    (F:MvPolynomial (Fin 4) K)
    (hY:F.degreeOf 1 ≤ P.leftY) (hR:F.degreeOf 2 ≤ P.leftR)
    (hZ:F.degreeOf 3 ≤ P.leftZ) :
    (RCN052.regularVector P F).y ≤ P.mixedCost.y ∧
      (RCN052.regularVector P F).r ≤ P.mixedCost.r ∧
      (RCN052.regularVector P F).z ≤ P.mixedCost.z:=by
  exact ⟨Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hR)
      (Nat.mul_le_mul_right P.rightR hZ),
    Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hY)
      (Nat.mul_le_mul_right P.rightY hZ),
    Nat.add_le_add (Nat.mul_le_mul_right P.rightR hY)
      (Nat.mul_le_mul_right P.rightY hR)⟩
theorem regularSeeds_count_le_intersection
    (P:UnequalParameters) (H Q:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H) (hrel:IsRelPrime F.1 Q)
    (p:ℕ) [CharP K p]
    (hFY:F.1.degreeOf 1 ≤ P.leftY) (hFR:F.1.degreeOf 2 ≤ P.leftR)
    (hFZ:F.1.degreeOf 3 ≤ P.leftZ)
    (hQY:Q.degreeOf 1 ≤ P.rightY) (hQR:Q.degreeOf 2 ≤ P.rightR)
    (hQZ:Q.degreeOf 3 ≤ P.rightZ)
    (hleftR:1 ≤ P.leftR)
    (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
    (hleftZSmall:P.leftZ < p)
    (hmixedYSmall:P.mixedCost.y < p) (hmixedRSmall:P.mixedCost.r < p)
    (hmixedZSmall:P.mixedCost.z < p)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (nodes:Finset I) (x u0 u1:I → K) (hinj:Set.InjOn x nodes)
    (hnodes:nodes.card = P.n)
    (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a) (han:P.a ≤ P.n)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement:∀ gamma ∈ Gamma, P.a ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno:RCN238.NoLargeSelectedPencil selected Gamma P.w P.errors)
    (hQzero:∀ gamma ∈ RCN140.regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q = 0) :
    (RCN140.regularSeeds H selected Gamma F).card ≤ P.regularCountCap:=by
  let Fself:=regularIndexSelf H F
  have hcount:=RCN052.regularPairSeeds_bound P F.1 Q hrel Fself p
    hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hw hchar hwa han hdegree hagreement hno
  have heq:RCN052.regularPairSeeds F.1 Q selected Gamma Fself =
      RCN140.regularSeeds H selected Gamma F:=by
    ext gamma
    simp only [RCN052.regularPairSeeds, RCN140.regularSeeds, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, h.2.1⟩
    · intro h
      exact ⟨h.1, h.2, hQzero gamma (Finset.mem_filter.mpr h)⟩
  rw [heq] at hcount
  have hv:=regularVector_le_mixedCost P F.1 hFY hFR hFZ
  have hdot:RCN294.dot P.agreement (RCN052.regularVector P F.1) ≤
      RCN294.dot P.agreement P.mixedCost :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left P.agreement.y hv.1)
        (Nat.mul_le_mul_left P.agreement.r hv.2.1))
      (Nat.mul_le_mul_left P.agreement.z hv.2.2)
  apply P.regular_count_le _ (by unfold UnequalParameters.gap; omega)
  exact hcount.trans (Nat.add_le_add (Nat.mul_le_mul_left (P.n - P.w) hdot)
    (Nat.mul_le_mul_left ((P.errors + 1) * P.gap) hv.2.2))
theorem regularSeeds_count_le_intersection_of_product
    (P:UnequalParameters) (H Q:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H) (hrel:IsRelPrime F.1 Q)
    (p:ℕ) [CharP K p]
    (hFY:F.1.degreeOf 1 ≤ P.leftY) (hFR:F.1.degreeOf 2 ≤ P.leftR)
    (hFZ:F.1.degreeOf 3 ≤ P.leftZ)
    (hQY:Q.degreeOf 1 ≤ P.rightY) (hQR:Q.degreeOf 2 ≤ P.rightR)
    (hQZ:Q.degreeOf 3 ≤ P.rightZ)
    (hleftR:1 ≤ P.leftR)
    (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
    (hleftZSmall:P.leftZ < p)
    (hmixedYSmall:P.mixedCost.y < p) (hmixedRSmall:P.mixedCost.r < p)
    (hmixedZSmall:P.mixedCost.z < p)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (nodes:Finset I) (x u0 u1:I → K) (hinj:Set.InjOn x nodes)
    (hnodes:nodes.card = P.n)
    (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a) (han:P.a ≤ P.n)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement:∀ gamma ∈ Gamma, P.a ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno:RCN238.NoLargeSelectedPencil selected Gamma P.w P.errors)
    (hproduct:∀ gamma ∈ RCN140.regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2:Fin 4) (F.1 * Q)) = 0) :
    (RCN140.regularSeeds H selected Gamma F).card ≤ P.regularCountCap:=by
  apply regularSeeds_count_le_intersection P H Q F hrel p
    hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hw hchar hwa han hdegree hagreement hno
  intro gamma hgamma
  obtain ⟨hFzero, hregular⟩:=(Finset.mem_filter.mp hgamma).2
  have hmul :
      RCN319.specialization K (selected gamma) gamma (MvPolynomial.pderiv (2:Fin 4) F.1) *
        RCN319.specialization K (selected gamma) gamma Q = 0:=by
    simpa only [MvPolynomial.pderiv_mul, map_add, map_mul,
      hFzero, zero_mul, add_zero] using hproduct gamma hgamma
  exact (mul_eq_zero.mp hmul).resolve_left hregular
end
end ProximityPrize.SubmissionLower.LocatorCoprimeQuotient

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

namespace ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance LocatorTripleCubeAvoidance
open LocatorFourthPowerAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Five successive high-band projections, obtained by applying the
four-stage extractor to the quotient after one outer projection. -/
theorem exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low_not_dvd_or_fourth_low_not_dvd_or_fifth_low
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
              (S - 3 * wt residualSWeights F) +
          delta * channelCount
            (T - 4 * wt residualTotalWeights F)
              (YS - 4 * wt residualYSWeights F)
              (S - 4 * wt residualSWeights F) <
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
      v ≠ 0 ∧ J ≠ 0 ∧ F * (F * (F * J)) = q v ∧ ¬ F ∣ J ∧
      J ∈ nestedCoefficientBox K
        (Dlow - 3 * delta - 3 * wt (contactWeights w) F) w
        (T - 3 * wt residualTotalWeights F)
          (YS - 3 * wt residualYSWeights F)
          (S - 3 * wt residualSWeights F)) ∨
    (∃ (v : V) (J : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ J ≠ 0 ∧ F * (F * (F * (F * J))) = q v ∧
      J ∈ nestedCoefficientBox K
        (Dlow - 4 * delta - 4 * wt (contactWeights w) F) w
        (T - 4 * wt residualTotalWeights F)
          (YS - 4 * wt residualYSWeights F)
          (S - 4 * wt residualSWeights F)) := by
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
            (S - 3 * wt residualSWeights F) +
        delta * channelCount
          (T - 4 * wt residualTotalWeights F)
            (YS - 4 * wt residualYSWeights F)
            (S - 4 * wt residualSWeights F) <
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
                (SOne - 2 * wt residualSWeights F) +
            delta * channelCount
              (TOne - 3 * wt residualTotalWeights F)
                (YOne - 3 * wt residualYSWeights F)
                (SOne - 3 * wt residualSWeights F) <
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
      have hT4 : T - wt residualTotalWeights F - 3 * wt residualTotalWeights F =
          T - 4 * wt residualTotalWeights F := by omega
      have hY4 : YS - wt residualYSWeights F - 3 * wt residualYSWeights F =
          YS - 4 * wt residualYSWeights F := by omega
      have hS4 : S - wt residualSWeights F - 3 * wt residualSWeights F =
          S - 4 * wt residualSWeights F := by omega
      simpa only [hT2, hY2, hS2, hT3, hY3, hS3, hT4, hY4, hS4]
        using hlowOneRank
    rcases
      exists_first_low_not_dvd_or_second_low_not_dvd_or_third_low_not_dvd_or_fourth_low
        DOneHigh DOneLow w delta TOne YOne SOne hwidthRest qTwo hqTwo
          hqTwoBox F hF hsourceRest with hfirst | hsecond | hthird | hfourth
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
            T - 2 * wt residualTotalWeights F := by simp only [TOne]; omega
        have hY : YOne - wt residualYSWeights F =
            YS - 2 * wt residualYSWeights F := by simp only [YOne]; omega
        have hS : SOne - wt residualSWeights F =
            S - 2 * wt residualSWeights F := by simp only [SOne]; omega
        simpa only [hD, hT, hY, hS] using hbox
    · obtain ⟨v, J, hv, hJ, heq, hndvd, hbox⟩ := hthird
      have hv' : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Subtype.ext hz
      right
      right
      right
      left
      refine ⟨v.1, J, hv', hJ, ?_, hndvd, ?_⟩
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
            T - 3 * wt residualTotalWeights F := by simp only [TOne]; omega
        have hY : YOne - 2 * wt residualYSWeights F =
            YS - 3 * wt residualYSWeights F := by simp only [YOne]; omega
        have hS : SOne - 2 * wt residualSWeights F =
            S - 3 * wt residualSWeights F := by simp only [SOne]; omega
        simpa only [hD, hT, hY, hS] using hbox
    · obtain ⟨v, J, hv, hJ, heq, hbox⟩ := hfourth
      have hv' : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Subtype.ext hz
      right
      right
      right
      right
      refine ⟨v.1, J, hv', hJ, ?_, ?_⟩
      · calc
          F * (F * (F * (F * J))) = F * qTwo v := by rw [heq]
          _ = qOne v :=
            (recon_eq_mul_quotientPolynomial qOne F hdivOne v).symm
          _ = q v.1 := rfl
      · have hD : DOneLow - 3 * delta - 3 * wt (contactWeights w) F =
            Dlow - 4 * delta - 4 * wt (contactWeights w) F := by
          simp only [DOneLow]
          omega
        have hT : TOne - 3 * wt residualTotalWeights F =
            T - 4 * wt residualTotalWeights F := by simp only [TOne]; omega
        have hY : YOne - 3 * wt residualYSWeights F =
            YS - 4 * wt residualYSWeights F := by simp only [YOne]; omega
        have hS : SOne - 3 * wt residualSWeights F =
            S - 4 * wt residualSWeights F := by simp only [SOne]; omega
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

section FifthDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

theorem specialization_pderiv_R5_eq_zero_of_kernel_low_box
    (D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 5) * support.card + 5 * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (reconstruct K D w L s v.1)))))) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hder5 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)))) ≠ 0 := by
    intro hz
    apply hne
    rw [hz, map_zero]
  have hder4 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) ≠ 0 := by
    intro hz
    exact hder5 (by rw [hz, map_zero])
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
  have hweight4 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H))) hder4
  have hder4weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)))) ≤
        Dlow - 1 - 4 * (w - 1) := by
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
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H)))) + (w - 1) ≤
      wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) at hweight4
    omega
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H)))) P gamma w
    (Dlow - 1 - 4 * (w - 1)) hP hder4weight hne
  have hdegreeStrict :
      (RCN122.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (MvPolynomial.pderiv (2 : Fin 4) H)))))).natDegree <
        (m - 5) * support.card := by
    rw [RCN101.specialization_eq_ordinary]
    rw [RCN101.specialization_eq_ordinary] at hdegree
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - 5 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (MvPolynomial.pderiv (2 : Fin 4)
                  (MvPolynomial.pderiv (2 : Fin 4) H)))))).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 5) _).mp
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
    have h5 := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)))) h4
    simpa only [Nat.sub_sub] using h5
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)))))
    P gamma nodes u0 u1 support (m - 5) hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

theorem specialization_eq_zero_of_pderiv_R5_fifth_product
    (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K)
    (hfactorial : (120 : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hfifth : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (F * (F * (F * (F * (F * Q)))))))))) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  have hfactorialPoly : (120 : Polynomial K) ≠ 0 := by
    intro hz
    apply hfactorial
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hmul : (120 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ 5 *
      RCN319.specialization K P gamma Q = 0 := by
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hFzero,
      zero_mul, mul_zero, zero_add, add_zero, mul_add] at hfifth
    ring_nf at hfifth ⊢
    exact hfifth
  have hcoef : (120 : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ 5 ≠ 0 :=
    mul_ne_zero hfactorialPoly (pow_ne_zero 5 hregular)
  exact (mul_eq_zero.mp hmul).resolve_left hcoef

end FifthDerivative

end

end ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance
end PackedLocator_LocatorFifthPowerAvoidance

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier04 : True := by trivial
end ProximityPrize.SubmissionLower

