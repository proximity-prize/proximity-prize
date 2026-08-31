import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredTwoSingularUnion6750Research
import ProximityPrize.SubmissionLower.ContactSingularBranchParameterizedResearch
import ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6600Research

 














namespace ProximityPrize.SubmissionLower.ContactAnchoredParentCapAdapters6750Research

open scoped Classical BigOperators
open ContactTranslation ContactSelectedSeedDecomposition
open ContactImplicitContactLift ContactSingularAuxiliary
open ContactSingularDegreeBounds
open ContactInterpolation ContactResidualSupportParametersResearch
open ContactFlagBezout6543Research ContactGCDCumulativeFlagsResearch
open ContactFactoredFlagCount6676Research
open ContactGlobalSelectedFamilies6600Research
open ContactRegularFactorFlag6600Research
open ContactSimultaneousOccurrenceLedger6750Research
open ContactAnchoredTwoSingularUnion6750Research
open ContactSingularBranch6600Research
open ContactSingularBranchParameterizedResearch
open ContactPrimeSeedIncidence

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K

 

 


theorem occurrence_regular_factor_seed_bound_of_distinct
    (Q : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (q r : FlagDegree)
    (hfactor : ∀ R : RegularIndex Q,
      (regularSeeds Q selected Gamma R).card ≤
        flagMixed (regularCumulativeFlag Q R) q r)
    (R : NormalizedOccurrence Q) :
    (occurrenceRegularSeeds Q selected Gamma R).card ≤
      flagMixed (occurrenceCumulativeFlag Q R) q r := by
  by_cases hRpos : 0 < (occurrenceFactor Q R).degreeOf 2
  · have hactive : occurrenceFactor Q R ∈ ContactFactorCover.activeFactors Q := by
      apply Finset.mem_filter.mpr
      refine ⟨Multiset.mem_toFinset.mpr (occurrenceFactor_mem Q R), ?_⟩
      omega
    let Rdistinct : RegularIndex Q :=
      ⟨occurrenceFactor Q R, Finset.mem_filter.mpr ⟨hactive, hRpos⟩⟩
    have hbound := hfactor Rdistinct
    simpa [occurrenceRegularSeeds, occurrenceCumulativeFlag, occurrenceFactor,
      ContactGlobalSelectedFamilies6600Research.regularSeeds,
      ContactGCDCumulativeFlagsResearch.regularCumulativeFlag,
      Rdistinct] using hbound
  · have hRzero : (occurrenceFactor Q R).degreeOf 2 = 0 :=
      Nat.eq_zero_of_not_pos hRpos
    have hpzero : MvPolynomial.pderiv (2 : Fin 4) (occurrenceFactor Q R) = 0 :=
      ContactRegularFactorGate.pderiv_zero_of_degree_zero
        (2 : Fin 4) (occurrenceFactor Q R) hRzero
    have hempty : occurrenceRegularSeeds Q selected Gamma R = ∅ := by
      ext gamma
      simp [occurrenceRegularSeeds, RegularSolution, hpzero]
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

 


theorem occurrence_regular_sum_le_flagMixed_of_distinct
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {P : ResidualSupportParameters} (Hsupport : ResidualSupportData P Q)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (p q r : FlagDegree)
    (hfactor : ∀ R : RegularIndex Q,
      (regularSeeds Q selected Gamma R).card ≤
        flagMixed (regularCumulativeFlag Q R) q r)
    (hs : P.s ≤ p.all)
    (hys : P.ys ≤ p.yz + p.all)
    (htotal : P.total ≤ p.zOnly + p.yz + p.all) :
    (∑ R : NormalizedOccurrence Q,
      (occurrenceRegularSeeds Q selected Gamma R).card) ≤
        flagMixed p q r := by
  have hc := occurrenceCumulativeFlag_budgets Q hQ Hsupport
  calc
    (∑ R : NormalizedOccurrence Q,
        (occurrenceRegularSeeds Q selected Gamma R).card) ≤
        ∑ R : NormalizedOccurrence Q,
          flagMixed (occurrenceCumulativeFlag Q R) q r :=
      Finset.sum_le_sum (fun R _ =>
        occurrence_regular_factor_seed_bound_of_distinct
          Q selected Gamma q r hfactor R)
    _ <= flagMixed p q r :=
      sum_flagMixed_le_of_cumulative (occurrenceCumulativeFlag Q)
        p q r (hc.1.trans hs) (hc.2.1.trans hys) (hc.2.2.trans htotal)

 

 

theorem anchoredSingularGSeeds_subset_singularSeeds
    {p D w L s : Nat} [CharP K p]
    (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
    (hbox : G ∈ globalCoefficientBox K D w L s)
    (hs : 1 ≤ s) (hsSmall : s < p)
    (hw : 1 ≤ w) (hDw : w < (2 * s - 1) * D)
    (selected : K -> Polynomial K) (Gamma : Finset K) :
    anchoredSingularGSeeds G selected Gamma ⊆
      singularSeeds G selected Gamma := by
  obtain ⟨hJ, hJbox⟩ := singularAuxiliary_nonzero_mem_box G
    D w L s p hG hs hsSmall hbox
  intro gamma hgamma
  have hmem := Finset.mem_filter.mp hgamma
  obtain hexceptional | ⟨q, hq, hpair⟩ :=
    solution_implicit_pair_or_exceptional (singularAuxiliary G) hJ
      (selected gamma) gamma ((2 * s - 1) * D) w ((2 * s - 1) * L)
      hw hDw hJbox hmem.2
  · exact Finset.mem_union.mpr <| Or.inr <|
      Finset.mem_filter.mpr ⟨hmem.1, hexceptional⟩
  · exact Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_biUnion.mpr
        ⟨⟨q, hq⟩, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨hmem.1, hpair⟩⟩

 

theorem anchoredSingularQSeeds_subset_singularSeeds
    {p D w L s : Nat} [CharP K p]
    (G Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hs : 1 ≤ s) (hsSmall : s < p)
    (hw : 1 ≤ w) (hDw : w < (2 * s - 1) * D)
    (selected : K -> Polynomial K) (Gamma : Finset K) :
    anchoredSingularQSeeds G Q selected Gamma ⊆
      singularSeeds Q selected Gamma := by
  obtain ⟨hJ, hJbox⟩ := singularAuxiliary_nonzero_mem_box Q
    D w L s p hQ hs hsSmall hbox
  intro gamma hgamma
  have hmem := Finset.mem_filter.mp hgamma
  obtain hexceptional | ⟨q, hq, hpair⟩ :=
    solution_implicit_pair_or_exceptional (singularAuxiliary Q) hJ
      (selected gamma) gamma ((2 * s - 1) * D) w ((2 * s - 1) * L)
      hw hDw hJbox hmem.2.2
  · exact Finset.mem_union.mpr <| Or.inr <|
      Finset.mem_filter.mpr ⟨hmem.1, hexceptional⟩
  · exact Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_biUnion.mpr
        ⟨⟨q, hq⟩, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨hmem.1, hpair⟩⟩

 

theorem anchoredSingularGSeeds_card_le_countCap
    (P : ContactTightSingularLedgerResearch.TightParameters)
    (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
    {p : Nat} [CharP K p]
    (hbox : G ∈ globalCoefficientBox K P.D P.w P.L P.s)
    (hs : 1 ≤ P.s) (hsSmall : P.s < p)
    (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hDw : P.w < P.kappa * P.D)
    (hj : 1 ≤ P.algebraicCap)
    (hjYSmall : P.implicitYCap < p)
    (hjZSmall : P.algebraicCap < p)
    (hmixedSmall : 2 * P.implicitYCap * P.algebraicCap < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    {Iota : Type} (nodes : Finset Iota) (x u0 u1 : Iota -> K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (anchoredSingularGSeeds G selected Gamma).card ≤ P.countCap := by
  have hsub := anchoredSingularGSeeds_subset_singularSeeds
    G hG hbox hs hsSmall hw hDw selected Gamma
  have hsing :=
    ContactSingularBranchParameterizedResearch.TightParameters.singularSeeds_count_le_countCap
      P G hG hbox hs hsSmall hw hchar hDw hj hjYSmall hjZSmall hmixedSmall
      hwa han selected Gamma nodes x u0 u1 hinj hnodes hdegree hagreement
      hnoPencil
  exact (Finset.card_le_card hsub).trans hsing

 


theorem anchoredSingularQSeeds_card_le_countCap
    (P : ContactTightSingularLedgerResearch.TightParameters)
    (G Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {p : Nat} [CharP K p]
    (hbox : Q ∈ globalCoefficientBox K P.D P.w P.L P.s)
    (hs : 1 ≤ P.s) (hsSmall : P.s < p)
    (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hDw : P.w < P.kappa * P.D)
    (hj : 1 ≤ P.algebraicCap)
    (hjYSmall : P.implicitYCap < p)
    (hjZSmall : P.algebraicCap < p)
    (hmixedSmall : 2 * P.implicitYCap * P.algebraicCap < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    {Iota : Type} (nodes : Finset Iota) (x u0 u1 : Iota -> K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (anchoredSingularQSeeds G Q selected Gamma).card ≤ P.countCap := by
  have hsub := anchoredSingularQSeeds_subset_singularSeeds
    G Q hQ hbox hs hsSmall hw hDw selected Gamma
  have hsing :=
    ContactSingularBranchParameterizedResearch.TightParameters.singularSeeds_count_le_countCap
      P Q hQ hbox hs hsSmall hw hchar hDw hj hjYSmall hjZSmall hmixedSmall
      hwa han selected Gamma nodes x u0 u1 hinj hnodes hdegree hagreement
      hnoPencil
  exact (Finset.card_le_card hsub).trans hsing

 

 



theorem anchored_card_le_of_distinct_regular_and_singular_caps
    (G Q : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (hQ : Q ≠ 0)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    {PG PQ : ResidualSupportParameters}
    (HsupportG : ResidualSupportData PG G)
    (HsupportQ : ResidualSupportData PQ Q)
    (pG qG rG pQ qQ rQ : FlagDegree)
    (singularG singularQ : Nat)
    (hGzero : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma G = 0)
    (hproductDerivative : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (G * Q)) = 0)
    (hsingularG :
      (anchoredSingularGSeeds G selected Gamma).card ≤ singularG)
    (hsingularQ :
      (anchoredSingularQSeeds G Q selected Gamma).card ≤ singularQ)
    (hfactorG : ∀ R : RegularIndex G,
      (regularSeeds G selected (anchoredGoodSeeds G Q selected Gamma) R).card ≤
        flagMixed (regularCumulativeFlag G R) qG rG)
    (hfactorQ : ∀ R : RegularIndex Q,
      (regularSeeds Q selected (anchoredGoodSeeds G Q selected Gamma) R).card ≤
        flagMixed (regularCumulativeFlag Q R) qQ rQ)
    (hsG : PG.s ≤ pG.all)
    (hysG : PG.ys ≤ pG.yz + pG.all)
    (htotalG : PG.total ≤ pG.zOnly + pG.yz + pG.all)
    (hsQ : PQ.s ≤ pQ.all)
    (hysQ : PQ.ys ≤ pQ.yz + pQ.all)
    (htotalQ : PQ.total ≤ pQ.zOnly + pQ.yz + pQ.all) :
    Gamma.card ≤ singularG + singularQ +
      (flagMixed pG qG rG + flagMixed pQ qQ rQ) / 2 := by
  apply anchored_card_le_two_singular_add_regular_of_product_derivative
    G Q hG hQ selected Gamma singularG singularQ
      (flagMixed pG qG rG) (flagMixed pQ qQ rQ)
      hGzero hproductDerivative hsingularG hsingularQ
  · exact occurrence_regular_sum_le_flagMixed_of_distinct
      G hG HsupportG selected (anchoredGoodSeeds G Q selected Gamma)
        pG qG rG hfactorG hsG hysG htotalG
  · exact occurrence_regular_sum_le_flagMixed_of_distinct
      Q hQ HsupportQ selected (anchoredGoodSeeds G Q selected Gamma)
        pQ qQ rQ hfactorQ hsQ hysQ htotalQ

end

end ProximityPrize.SubmissionLower.ContactAnchoredParentCapAdapters6750Research

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredParentCapAdapters6750Research.occurrence_regular_sum_le_flagMixed_of_distinct
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredParentCapAdapters6750Research.anchoredSingularGSeeds_card_le_countCap
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredParentCapAdapters6750Research.anchoredSingularQSeeds_card_le_countCap
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredParentCapAdapters6750Research.anchored_card_le_of_distinct_regular_and_singular_caps
