import ProximityPrize.SubmissionLower.ContactAnchoredReducedDelayedTailAssembly6750Bisect

namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredCongruentTangent6750Research

open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactIdentityResidualIterationResearch ContactRegularComponentCover
open ContactFirstTailCertificate6731Research ContactProperCutSeedCount
open ContactDelayedTailMultiplicityProvider6732Research
open ContactPrimeSeedIncidence ContactInterpolation
open ContactResidualSupportParametersResearch
open ContactFlagBezout6543Research
open ContactTangentCoefficientProvider6732Research
open ContactAnchoredCongruentCuts6750Research
open ContactAnchoredReducedDelayedTailAssembly6750Bisect
open ContactAdaptiveUnitPoleFamilyResearch
open ContactWeakSeparableSeparatorResearch
open ActualCurveCoordinateField CoordinateBoxZeroCount

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000

 


theorem tangent_component_card_le_of_congruentCut
    {K I : Type} [Field K]
    {Gamma : Finset K} {x : I → K} {p errors w : Nat}
    [CharP (GenericField K) p]
    {flag tailFlag1 : FlagDegree}
    {support : ResidualSupportParameters}
    (S : ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
    (C : FirstTailComponent S)
    (hfirstProper : ¬ S.G ∣
      globalTailCut (polynomialEmbedding K) S.F (w + 1))
    {T' : MvPolynomial (Fin 3) (GenericField K)}
    (hd : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1) - T')
    (base : ∀ C' : RegularComponent (GenericField K) S.G T'
      (regularitySurface (polynomialEmbedding K) S.F),
      SeparableLiteralCoordinate C'.1)
    (U : AdaptiveUnitProjectionFamily base flag tailFlag1)
    (agreements bound seedCap slopeCap : Nat)
    (hnodes : S.nodes.card = agreements + errors)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hwa : w < agreements) (hw : 1 ≤ w)
    (hshort : w + 1 ≤ bound) (hchar : bound < p)
    (hbox : S.F ∈ globalCoefficientBox K bound w seedCap slopeCap)
    (hyzPositive : 1 ≤ U.toPrimeFlagBudgetFamily.yzCost
      (regularComponentEquiv hd C))
    (hallTails : ∀ delay,
      globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∈ C.1) :
    (componentSeeds (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
        (errors + 1) *
          (PrimeFlagBudgetFamily.ofCongruentCut hd
            U.toPrimeFlagBudgetFamily).yzCost C := by
  let B := PrimeFlagBudgetFamily.ofCongruentCut hd U.toPrimeFlagBudgetFamily
  exact tangent_component_card_le S C hfirstProper
    (congruentCut_separableLiteralCoordinate hd base C)
    agreements bound seedCap slopeCap hnodes hagreement hwa hw hshort hchar
    hbox B (congruentCut_adaptiveYZPositive hd base U C hyzPositive) hallTails
    (congruentCut_adaptiveYZPole hd base U C)

end
end ContactAnchoredCongruentTangent6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredCongruentTangent6750Research.tangent_component_card_le_of_congruentCut
