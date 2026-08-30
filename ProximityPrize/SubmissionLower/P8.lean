import ProximityPrize.SubmissionLower.Q0
import ProximityPrize.SubmissionLower.A0
namespace ProximityPrize.SubmissionLower.ContactTwoTailReducedActivePowers6734Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6732Research
open ContactDelayedTailMultiplicityProvider6732Research
open ContactProperCutSeedCount
open ContactRegularComponentCover
open ContactFlagBezout6543Research
open ContactCongruentCuts6643Research
open ContactTwoTailReducedTransport6734Research
open ContactTwoTailReducedPowers6734Research
open ContactActiveNestedFixedPowers6733Research
open ContactActiveNestedFlagData6733Research
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactWeakSeparableSeparatorResearch
open ContactFlagProjectionPositivity6543Research
open ContactFlagTriangularProjectionResearch
open ActualCurveCoordinateField
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
theorem reducedStage_activeFixedPowers
   (S : Stage K I Gamma x p flag)
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (ContactTwoTailParameters6733Research.w + 1))
   (Tred : MvPolynomial (Fin 3) (GenericField K))
   (hd : S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (ContactTwoTailParameters6733Research.w + 1) - Tred)
   (base : ∀ C : RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     SeparableLiteralCoordinate C.1)
   (hactive : ∀ C : RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     KaehlerDifferential.D (GenericField K)
         (CoordinateField (GenericField K) C.1)
         (coordinate (GenericField K) C.1 0) ≠ 0 ∨
       KaehlerDifferential.D (GenericField K)
         (CoordinateField (GenericField K) C.1)
         (coordinate (GenericField K) C.1 2) ≠ 0)
   (hZ : ∀ C : RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     LiteralProjectionGate C 2)
   (hSderiv : MvPolynomial.pderiv (1 : Fin 3) S.G ≠ 0)
   (D : AdaptiveNestedProjectionDataActive base hactive hSderiv) :
   ActiveNestedFixedPowers base hactive hZ hSderiv D
     (transportedMultiplicity hd
       (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))) := by
 refine { z := ?_, u := ?_, v := ?_ }
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (activeNestedZComponent (G := S.G) (T := Tred)
       (H := regularitySurface (polynomialEmbedding K) S.F))
     activeNestedZComponent_injective D.lam D.mu (D.mu * D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D)
     (activeNestedZFinite base hactive hZ hSderiv D)
     (activeNestedZGenerates base hactive hSderiv D)
     (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hSderiv).2
     q hq hqMonic a0
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (fun C : RegularComponent (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) => C)
     Function.injective_id D.lam D.mu (D.mu * D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D)
     (activeNestedUFinite base hactive hSderiv D)
     (activeNestedUGenerates base hactive hSderiv D)
     (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hSderiv).1
     q hq hqMonic a0
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (fun C : RegularComponent (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) => C)
     Function.injective_id D.lam D.mu (D.mu * D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D)
     (activeNestedVFinite base hactive hSderiv D)
     (activeNestedVGenerates base hactive hSderiv D)
     (flag_v_outer_positive_of_directional D.lam D.mu S.G D.directional)
     q hq hqMonic a0
end
end ProximityPrize.SubmissionLower.ContactTwoTailReducedActivePowers6734Research
