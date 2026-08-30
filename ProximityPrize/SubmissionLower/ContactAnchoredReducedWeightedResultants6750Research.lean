import ProximityPrize.SubmissionLower.ContactAnchoredReducedActiveGeometry6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredReducedActivePowers6750Research
import ProximityPrize.SubmissionLower.ContactActiveNestedCertificate6733Research
namespace ProximityPrize.SubmissionLower.ContactAnchoredReducedWeightedResultants6750Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactIdentityResidualIterationResearch
open ContactRegularComponentCover ContactFlagBezout6543Research
open ContactDelayedTailMultiplicityProvider6732Research
open ContactMovingAgreementCertificate6719Research ContactFirstTailCertificate6731Research
open ContactProperCutSeedCount ContactResidualSupportParametersResearch
open ContactAnchoredDelayedTailLocalDVR6750Research
open ContactAnchoredDelayedTailProviderAdapter6750Research
open ContactAnchoredCongruentCuts6750Research
open ContactAnchoredReducedActiveGeometry6750Research
open ContactAnchoredReducedActivePowers6750Research
open ContactActiveNestedCertificate6733Research
open ContactActiveNestedFlagCosts6733Research
open ContactActiveNestedFixedPowers6733Research
open ContactTwoTailResultantProvider6732Research
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactWeakSeparableSeparatorResearch
open ActualCurveCoordinateField
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {a b s : ℕ}

noncomputable def reducedMultiplicity
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (support a b s))
    (hs : (support a b s).s ≤ anchoredFixedSupport.s)
    (hys : (support a b s).ys ≤ anchoredFixedSupport.ys)
    (htotal : (support a b s).total ≤ anchoredFixedSupport.total)
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1)) :
    FirstTailComponent S → ℕ :=
  localMultiplicity (loosenStage S hs hys htotal)
    (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper)

noncomputable def reducedUnitFamily
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (support a b s))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixed : (1 + (anchoredW + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (anchoredW + 1)) < p) :=
  let A := reducedActiveGeometry S hfirstProper hflagChar hmixed
  activeNestedUnitFamily A.base A.hactive A.hZ
    (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S)
    A.data S.irreducible_G (reducedFirstCut_proper S hfirstProper)
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff
      (reducedResidualAgreementFlag6750 (support a b s) (anchoredW + 1))
      (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))

theorem reducedFixedPowers
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (support a b s))
    (hs : (support a b s).s ≤ anchoredFixedSupport.s)
    (hys : (support a b s).ys ≤ anchoredFixedSupport.ys)
    (htotal : (support a b s).total ≤ anchoredFixedSupport.total)
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixed : (1 + (anchoredW + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (anchoredW + 1)) < p) :
    let A := reducedActiveGeometry S hfirstProper hflagChar hmixed
    ActiveNestedFixedPowers A.base A.hactive A.hZ
      (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S)
      A.data
      (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
        (reducedMultiplicity S hs hys htotal hfirstProper)) := by
  dsimp only
  exact reducedStage_activeFixedPowers (loosenStage S hs hys htotal)
    hfirstProper (reducedFirstCut S) (ordinary_sub_reducedFirstCut_dvd S)
    (reducedActiveGeometry S hfirstProper hflagChar hmixed).base
    (reducedActiveGeometry S hfirstProper hflagChar hmixed).hactive
    (reducedActiveGeometry S hfirstProper hflagChar hmixed).hZ
    (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S)
    (reducedActiveGeometry S hfirstProper hflagChar hmixed).data

theorem reducedWeightedResultants
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (support a b s))
    (hs : (support a b s).s ≤ anchoredFixedSupport.s)
    (hys : (support a b s).ys ≤ anchoredFixedSupport.ys)
    (htotal : (support a b s).total ≤ anchoredFixedSupport.total)
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixed : (1 + (anchoredW + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (anchoredW + 1)) < p) :
    RegularComponentWeightedInertiaResultantCertificate
      (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
      (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
        (reducedMultiplicity S hs hys htotal hfirstProper)) := by
  let A := reducedActiveGeometry S hfirstProper hflagChar hmixed
  exact activeNestedWeightedCertificate A.base A.hactive A.hZ
    (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S)
    A.data S.irreducible_G (reducedFirstCut_proper S hfirstProper)
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff
      (reducedResidualAgreementFlag6750 (support a b s) (anchoredW + 1))
      (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
    (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
      (reducedMultiplicity S hs hys htotal hfirstProper))
    (reducedFixedPowers S hs hys htotal hfirstProper hflagChar hmixed)

noncomputable def reducedBudgetFamily
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (support a b s))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixed : (1 + (anchoredW + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (anchoredW + 1)) < p) :=
  PrimeFlagBudgetFamily.ofCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
    (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily

theorem transportedWeightedResultants
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (support a b s))
    (hs : (support a b s).s ≤ anchoredFixedSupport.s)
    (hys : (support a b s).ys ≤ anchoredFixedSupport.ys)
    (htotal : (support a b s).total ≤ anchoredFixedSupport.total)
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixed : (1 + (anchoredW + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (anchoredW + 1)) < p) :
    RegularComponentWeightedInertiaResultantCertificate
      (reducedBudgetFamily S hfirstProper hflagChar hmixed)
      (reducedMultiplicity S hs hys htotal hfirstProper) := by
  exact weightedCertificate_of_congruentCut
    (ordinary_sub_reducedFirstCut_dvd S)
    (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
    (reducedMultiplicity S hs hys htotal hfirstProper)
    (reducedWeightedResultants S hs hys htotal hfirstProper hflagChar hmixed)
end
end ProximityPrize.SubmissionLower.ContactAnchoredReducedWeightedResultants6750Research
