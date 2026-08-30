import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSimultaneousFixedCost6750Research

 













namespace ProximityPrize.SubmissionLower.ContactSimultaneousOrdinaryUnion6750Research

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open ContactInterpolation ContactTranslation ContactSelectedSeedDecomposition
open ContactSingularAuxiliary ContactSingularDegreeBounds
open ContactImplicitContactLift ContactImplicitPairBudgets
open ContactSingularBranch6600Research
open ContactSingularBranchParameterizedResearch
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactResidualSupportParametersResearch
open ContactTwoTailParameters6733Research
open ContactTwoTailFixedSelected6733Research
open ContactSimultaneousFixedCost6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K prime := by
  simpa [prime, ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600

 
def auxiliaryZeroSeeds (G : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter (fun gamma =>
    specialization K (selected gamma) gamma (singularAuxiliary G) = 0)

 


def simultaneousRegularSeeds (G : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter (fun gamma =>
    specialization K (selected gamma) gamma (singularAuxiliary G) ≠ 0 ∧
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) G) = 0)

 


def ordinaryZeroSeeds (Qlow : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter (fun gamma =>
    specialization K (selected gamma) gamma Qlow = 0)

 

theorem ordinary_specialization_zero_of_product_derivative_zero
    (G Qlow : MvPolynomial (Fin 4) K)
    (P : Polynomial K) (gamma : K)
    (hGzero : specialization K P gamma G = 0)
    (hproductDerivative : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) (G * Qlow)) = 0)
    (hGderivative : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0) :
    specialization K P gamma Qlow = 0 := by
  rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, hGzero,
    zero_mul, add_zero] at hproductDerivative
  exact (mul_eq_zero.mp hproductDerivative).resolve_left hGderivative

 

theorem subset_auxiliary_union_simultaneous_union_ordinary
    (G Qlow : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (hordinaryRoute : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma (singularAuxiliary G) ≠ 0 ->
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0 ->
      specialization K (selected gamma) gamma Qlow = 0) :
    Gamma ⊆
      (auxiliaryZeroSeeds G selected Gamma ∪
        simultaneousRegularSeeds G selected Gamma) ∪
      ordinaryZeroSeeds Qlow selected Gamma := by
  intro gamma hgamma
  by_cases haux :
      specialization K (selected gamma) gamma (singularAuxiliary G) = 0
  · exact Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hgamma, haux⟩
  · by_cases hderiv : specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) G) = 0
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_filter.mpr ⟨hgamma, haux, hderiv⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr
          ⟨hgamma, hordinaryRoute gamma hgamma haux hderiv⟩

 

theorem card_le_auxiliary_add_simultaneous_add_ordinary
    (G Qlow : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (hordinaryRoute : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma (singularAuxiliary G) ≠ 0 ->
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0 ->
      specialization K (selected gamma) gamma Qlow = 0) :
    Gamma.card <=
      (auxiliaryZeroSeeds G selected Gamma).card +
        (simultaneousRegularSeeds G selected Gamma).card +
          (ordinaryZeroSeeds Qlow selected Gamma).card := by
  have hsub := subset_auxiliary_union_simultaneous_union_ordinary
    G Qlow selected Gamma hordinaryRoute
  calc
    Gamma.card <=
        ((auxiliaryZeroSeeds G selected Gamma ∪
          simultaneousRegularSeeds G selected Gamma) ∪
          ordinaryZeroSeeds Qlow selected Gamma).card :=
      Finset.card_le_card hsub
    _ <= (auxiliaryZeroSeeds G selected Gamma ∪
          simultaneousRegularSeeds G selected Gamma).card +
          (ordinaryZeroSeeds Qlow selected Gamma).card :=
      Finset.card_union_le _ _
    _ <= ((auxiliaryZeroSeeds G selected Gamma).card +
          (simultaneousRegularSeeds G selected Gamma).card) +
          (ordinaryZeroSeeds Qlow selected Gamma).card :=
      Nat.add_le_add_right
        (Finset.card_union_le (auxiliaryZeroSeeds G selected Gamma)
          (simultaneousRegularSeeds G selected Gamma)) _

 


theorem auxiliaryZeroSeeds_subset_singularSeeds
    {p D w0 L s : Nat} [CharP K p]
    (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
    (hbox : G ∈ globalCoefficientBox K D w0 L s)
    (hs : 1 <= s) (hsSmall : s < p)
    (hw : 1 <= w0) (hDw : w0 < (2 * s - 1) * D)
    (selected : K -> Polynomial K) (Gamma : Finset K) :
    auxiliaryZeroSeeds G selected Gamma ⊆
      singularSeeds G selected Gamma := by
  obtain ⟨hJ, hJbox⟩ := singularAuxiliary_nonzero_mem_box G
    D w0 L s p hG hs hsSmall hbox
  intro gamma hgamma
  have hmem := Finset.mem_filter.mp hgamma
  obtain hexceptional | ⟨q, hq, hpair⟩ :=
    solution_implicit_pair_or_exceptional (singularAuxiliary G) hJ
      (selected gamma) gamma ((2 * s - 1) * D) w0 ((2 * s - 1) * L)
      hw hDw hJbox hmem.2
  · exact Finset.mem_union.mpr <| Or.inr <|
      Finset.mem_filter.mpr ⟨hmem.1, hexceptional⟩
  · exact Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_biUnion.mpr
        ⟨⟨q, hq⟩, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨hmem.1, hpair⟩⟩

 
theorem fixed_simultaneousRegularSeeds_card_le_half
    (proper : ProperStageProvider6733)
    (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
    (hbox : G ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport G)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (u0 u1 : I -> K)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma G = 0)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree <= w)
    (hagreement : ∀ gamma ∈ Gamma, agreements <=
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (simultaneousRegularSeeds G selected Gamma).card <=
      fixedRegularCost / 2 := by
  let Sim := simultaneousRegularSeeds G selected Gamma
  have hsub : Sim ⊆ Gamma := Finset.filter_subset _ _
  apply fixed_simultaneous_regular_card_le_half proper G hG hbox Hsupport
    selected Sim u0 u1
  · intro gamma hgamma
    exact hsolution gamma (hsub hgamma)
  · intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.2
  · intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  · intro gamma hgamma
    exact hdegree gamma (hsub hgamma)
  · intro gamma hgamma
    exact hagreement gamma (hsub hgamma)
  · exact noLargeSelectedPencil_mono selected Gamma Sim w errors hsub hnoPencil

 
theorem fixed_auxiliaryZeroSeeds_card_le_countCap
    (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
    (hbox : G ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (u0 u1 : I -> K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree <= w)
    (hagreement : ∀ gamma ∈ Gamma, agreements <=
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (auxiliaryZeroSeeds G selected Gamma).card <=
      fixedTightProfile.countCap := by
  have hsub : auxiliaryZeroSeeds G selected Gamma ⊆
      singularSeeds G selected Gamma :=
    auxiliaryZeroSeeds_subset_singularSeeds G hG hbox
      (by decide) (by decide) (by decide) (by decide) selected Gamma
  have hboxT : G ∈ globalCoefficientBox K fixedTightProfile.D
      fixedTightProfile.w fixedTightProfile.L fixedTightProfile.s := by
    simpa only [fixedAlignment.weightedCap, fixedAlignment.w,
      fixedAlignment.seedTotalCap, fixedAlignment.slopeCap] using hbox
  have hsing :=
    ContactSingularBranchParameterizedResearch.TightParameters.singularSeeds_count_le_countCap
      fixedTightProfile G hG hboxT
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      selected Gamma (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by
        change Fintype.card I = fixedTightProfile.n
        norm_num [I, IRSProfile.Index, fixedTightProfile, n])
      (by
        intro gamma hgamma
        simpa [fixedTightProfile] using hdegree gamma hgamma)
      (by
        intro gamma hgamma
        simpa [fixedTightProfile] using hagreement gamma hgamma)
      (by
        simpa [fixedTightProfile,
          ContactTightSingularLedgerResearch.TightParameters.errors,
          errors, agreements, n] using hnoPencil)
  exact (Finset.card_le_card hsub).trans hsing

 


theorem fixed_three_way_card_le_half_add_countCap_add_ordinary
    (proper : ProperStageProvider6733)
    (G Qlow : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
    (hbox : G ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport G)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (u0 u1 : I -> K) (ordinaryCap : Nat)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma G = 0)
    (hordinaryRoute : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma (singularAuxiliary G) ≠ 0 ->
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0 ->
      specialization K (selected gamma) gamma Qlow = 0)
    (hordinary : (ordinaryZeroSeeds Qlow selected Gamma).card <= ordinaryCap)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree <= w)
    (hagreement : ∀ gamma ∈ Gamma, agreements <=
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card <= fixedRegularCost / 2 + fixedTightProfile.countCap +
      ordinaryCap := by
  have hcover := card_le_auxiliary_add_simultaneous_add_ordinary
    G Qlow selected Gamma hordinaryRoute
  have haux := fixed_auxiliaryZeroSeeds_card_le_countCap G hG hbox
    selected Gamma u0 u1 hdegree hagreement hnoPencil
  have hsim := fixed_simultaneousRegularSeeds_card_le_half proper G hG hbox
    Hsupport selected Gamma u0 u1 hsolution hdegree hagreement hnoPencil
  omega

 
theorem fixed_three_way_card_le_half_add_singularCost_add_ordinary
    (proper : ProperStageProvider6733)
    (G Qlow : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
    (hbox : G ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport G)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (u0 u1 : I -> K) (ordinaryCap : Nat)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma G = 0)
    (hordinaryRoute : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma (singularAuxiliary G) ≠ 0 ->
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0 ->
      specialization K (selected gamma) gamma Qlow = 0)
    (hordinary : (ordinaryZeroSeeds Qlow selected Gamma).card <= ordinaryCap)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree <= w)
    (hagreement : ∀ gamma ∈ Gamma, agreements <=
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card <= fixedRegularCost / 2 + fixedSingularCost + ordinaryCap := by
  have h := fixed_three_way_card_le_half_add_countCap_add_ordinary proper
    G Qlow hG hbox Hsupport selected Gamma u0 u1 ordinaryCap hsolution
    hordinaryRoute hordinary hdegree hagreement hnoPencil
  have hbridge := fixed_numeric_bridge
  omega

 


theorem fixed_three_way_card_le_of_product_derivative
    (proper : ProperStageProvider6733)
    (G Qlow : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
    (hbox : G ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport G)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (u0 u1 : I -> K) (ordinaryCap : Nat)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma G = 0)
    (hproductDerivative : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (G * Qlow)) = 0)
    (hordinary : (ordinaryZeroSeeds Qlow selected Gamma).card <= ordinaryCap)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree <= w)
    (hagreement : ∀ gamma ∈ Gamma, agreements <=
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card <= fixedRegularCost / 2 + fixedSingularCost + ordinaryCap := by
  apply fixed_three_way_card_le_half_add_singularCost_add_ordinary proper
    G Qlow hG hbox Hsupport selected Gamma u0 u1 ordinaryCap hsolution
    _ hordinary hdegree hagreement hnoPencil
  intro gamma hgamma _haux hGderivative
  exact ordinary_specialization_zero_of_product_derivative_zero G Qlow
    (selected gamma) gamma (hsolution gamma hgamma)
      (hproductDerivative gamma hgamma) hGderivative

end

end ProximityPrize.SubmissionLower.ContactSimultaneousOrdinaryUnion6750Research

#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOrdinaryUnion6750Research.subset_auxiliary_union_simultaneous_union_ordinary
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOrdinaryUnion6750Research.ordinary_specialization_zero_of_product_derivative_zero
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOrdinaryUnion6750Research.auxiliaryZeroSeeds_subset_singularSeeds
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOrdinaryUnion6750Research.fixed_simultaneousRegularSeeds_card_le_half
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOrdinaryUnion6750Research.fixed_auxiliaryZeroSeeds_card_le_countCap
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOrdinaryUnion6750Research.fixed_three_way_card_le_half_add_countCap_add_ordinary
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOrdinaryUnion6750Research.fixed_three_way_card_le_half_add_singularCost_add_ordinary
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOrdinaryUnion6750Research.fixed_three_way_card_le_of_product_derivative
