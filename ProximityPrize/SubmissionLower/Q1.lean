import ProximityPrize.SubmissionLower.J5
import ProximityPrize.SubmissionLower.P8
import ProximityPrize.SubmissionLower.DH
namespace ProximityPrize.SubmissionLower.ContactTwoTailReducedProvider6734Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactTranslation ContactInterpolation
open ContactIdentityResidualIterationResearch ContactRegularComponentCover
open ContactDelayedTailMultiplicityProvider6732Research
open ContactFirstTailCertificate6731Research ContactProperCutSeedCount
open ContactPrimeSeedIncidence ContactFlagBezout6543Research
open ContactPrimeFlagBudgetFamilyResearch
open ContactMovingAgreementCertificate6719Research
open ContactResidualSupportParametersResearch
open ContactProperDelayedTailCertificate6732Research
open ContactTwoTailParameters6734Research
open ContactReducedTaylorProfileResearch ContactFirstTailReducedCertificate6732Research
open ContactCongruentCuts6643Research
open ContactFirstTailReducedProjection6732Research
open ContactTwoTailReducedActivePowers6734Research
open ContactTwoTailReducedTransport6734Research
open ContactActiveNestedCertificate6733Research
open ContactActiveNestedFlagCosts6733Research
open ContactActiveNestedFixedPowers6733Research
open ContactTwoTailResultantProvider6732Research
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveProjectionCoordinateResearch
open ContactWeakSeparableSeparatorResearch
open ContactTangentCoefficientProvider6732Research
open ContactTwoTailTangentCost6732Research
open ContactTwoTailRecurrence6731Research
open ActualCurveCoordinateField CoordinateBoxZeroCount
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {tightSupport : ResidualSupportParameters}
def loosenStage
   (S : ResidualStage (polynomialEmbedding K) Gamma x p errors flag w tightSupport)
   (hs : tightSupport.s ≤ fixedSupport.s)
   (hys : tightSupport.ys ≤ fixedSupport.ys)
   (htotal : tightSupport.total ≤ fixedSupport.total) :
   Stage K I Gamma x p flag :=
 { S with
   surface_s_weight := S.surface_s_weight.trans hs
   surface_ys_weight := S.surface_ys_weight.trans hys
   surface_total_weight := S.surface_total_weight.trans htotal }
theorem loosenStage_one_le_localMultiplicity
   (S : ResidualStage (polynomialEmbedding K) Gamma x p errors flag w tightSupport)
   (hs : tightSupport.s ≤ fixedSupport.s)
   (hys : tightSupport.ys ≤ fixedSupport.ys)
   (htotal : tightSupport.total ≤ fixedSupport.total)
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   ∀ C, 1 ≤ localMultiplicity (loosenStage S hs hys htotal)
     (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper) C := by
 exact one_le_localMultiplicity (loosenStage S hs hys htotal) hfirstProper
theorem laterTail_in_reduced_delay_secondFlag
   (S : ResidualStage (polynomialEmbedding K) Gamma x p errors flag w tightSupport)
   (C : FirstTailComponent S) (delay : ℕ) (hdelay : 1 ≤ delay) :
   PolynomialInFlagMod C.1
     (delay • reducedResidualAgreementFlag tightSupport (w + 2))
     (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
 let d := w + 1 + delay
 let Tred := reducedGlobalTailCut (polynomialEmbedding K) tightSupport S.F d
 let Hsupport : ResidualSupportData tightSupport S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 have hred : PolynomialInFlag (reducedResidualAgreementFlag tightSupport d) Tred :=
   reducedGlobalTailCut_in_flag (polynomialEmbedding K) tightSupport Hsupport d
 have hflag : PolynomialInFlag
     (delay • reducedResidualAgreementFlag tightSupport (w + 2)) Tred := by
   have hscale : d ≤ delay * (w + 2) := by
     dsimp only [d]
     norm_num [w]
     omega
   have hallFlag : (reducedResidualAgreementFlag tightSupport d).all ≤
       (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all := by
     simp only [reducedResidualAgreementFlag, reducedAgreementDirection, nsmul_all]
     calc
       (2 * tightSupport.s - 2) * d ≤
           (2 * tightSupport.s - 2) * (delay * (w + 2)) :=
         Nat.mul_le_mul_left _ hscale
       _ = delay * ((2 * tightSupport.s - 2) * (w + 2)) := by ring
   have hysFlag :
       (reducedResidualAgreementFlag tightSupport d).yz +
           (reducedResidualAgreementFlag tightSupport d).all ≤
         (delay • reducedResidualAgreementFlag tightSupport (w + 2)).yz +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all := by
     rw [reducedResidualAgreementFlag_ys]
     simp only [nsmul_yz, nsmul_all]
     rw [← Nat.mul_add]
     rw [reducedResidualAgreementFlag_ys]
     calc
       1 + d * (2 * tightSupport.ys - 2) ≤
           delay + (delay * (w + 2)) * (2 * tightSupport.ys - 2) :=
         Nat.add_le_add hdelay (Nat.mul_le_mul_right _ hscale)
       _ = delay * (1 + (w + 2) * (2 * tightSupport.ys - 2)) := by ring
   have htotalFlag :
       (reducedResidualAgreementFlag tightSupport d).zOnly +
           (reducedResidualAgreementFlag tightSupport d).yz +
           (reducedResidualAgreementFlag tightSupport d).all ≤
         (delay • reducedResidualAgreementFlag tightSupport (w + 2)).zOnly +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).yz +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all := by
     rw [reducedResidualAgreementFlag_total]
     simp only [nsmul_zOnly, nsmul_yz, nsmul_all]
     rw [← Nat.mul_add, ← Nat.mul_add]
     rw [reducedResidualAgreementFlag_total]
     calc
       1 + d * (2 * tightSupport.total - 2) ≤
           delay + (delay * (w + 2)) * (2 * tightSupport.total - 2) :=
         Nat.add_le_add hdelay (Nat.mul_le_mul_right _ hscale)
       _ = delay * (1 + (w + 2) * (2 * tightSupport.total - 2)) := by ring
   intro exponent hexponent
   have h := hred exponent hexponent
   exact ⟨h.1.trans hallFlag, h.2.1.trans hysFlag, h.2.2.trans htotalFlag⟩
 refine ⟨Tred, hflag, ?_⟩
 have hd : S.G ∣ globalTailCut (polynomialEmbedding K) S.F d - Tred :=
   S.G_dvd_surface.trans
     (globalTailCut_sub_reduced_dvd (polynomialEmbedding K) tightSupport S.F d)
 exact C.1.mem_of_dvd hd
   (regularComponent_G_mem (GenericField K) S.G
     (globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F) C)
theorem loosenStage_dichotomy_with_tangent
   {tailFlag1 : FlagDegree}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p errors flag w tightSupport)
   (hs : tightSupport.s ≤ fixedSupport.s)
   (hys : tightSupport.ys ≤ fixedSupport.ys)
   (htotal : tightSupport.total ≤ fixedSupport.total)
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (B : PrimeFlagBudgetFamily
     (G := S.G) (T := globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (H := regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
   (htangent : ∀ C : FirstTailComponent S,
     (∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) →
     (componentSeeds (GenericField K) S.G
       (globalTailCut (polynomialEmbedding K) S.F (w + 1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (errors + 1) * B.yzCost C) :
   ∀ C : FirstTailComponent S,
     (∃ delay, 1 ≤ delay ∧
       delay ≤ localMultiplicity (loosenStage S hs hys htotal)
         (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper) C ∧
       globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1) ∨
     ((∀ delay, globalTailCut (polynomialEmbedding K) S.F
         (w + 1 + delay) ∈ C.1) ∧
       (componentSeeds (GenericField K) S.G
         (globalTailCut (polynomialEmbedding K) S.F (w + 1))
         (regularitySurface (polynomialEmbedding K) S.F) Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
           (errors + 1) * B.yzCost C) := by
 intro C
 have dichotomy := local_order_tail_dichotomy (loosenStage S hs hys htotal)
   (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper)
   C hfirstProper
 rcases dichotomy.2 with hproper | hall
 · exact Or.inl hproper
 · exact Or.inr ⟨hall, htangent C hall⟩
structure ReducedActiveGeometry
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p errors flag w
     (support a b s)) where
 base : ∀ C : RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F),
   SeparableLiteralCoordinate C.1
 hactive : ∀ C : RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F),
   KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
       (coordinate (GenericField K) C.1 0) ≠ 0 ∨
     KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
       (coordinate (GenericField K) C.1 2) ≠ 0
 hZ : ∀ C : RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F), LiteralProjectionGate C 2
 data : AdaptiveNestedProjectionDataActive base hactive
   (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S)
theorem exists_reducedActiveGeometry
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p errors flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   Nonempty (ReducedActiveGeometry S) := by
 obtain ⟨base, hactive, hZ, ⟨D⟩⟩ :=
   exists_reduced_firstTail_activeNestedData_of_caps S hfirstProper hflagChar hmixed
 exact ⟨⟨base, hactive, hZ, D⟩⟩
noncomputable def reducedActiveGeometry
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p errors flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   ReducedActiveGeometry S :=
 Classical.choice (exists_reducedActiveGeometry S hfirstProper hflagChar hmixed)
end
end ProximityPrize.SubmissionLower.ContactTwoTailReducedProvider6734Research
