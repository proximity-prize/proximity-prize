import ProximityPrize.SubmissionLower.DJ
import ProximityPrize.SubmissionLower.A0
import ProximityPrize.SubmissionLower.K1
import ProximityPrize.SubmissionLower.Q9
namespace ProximityPrize.SubmissionLower.ContactActiveNestedChannels6733Research
open scoped Classical BigOperators
open ContactRegularComponentCover ActualCurveCoordinateField
open ContactWeakSeparableSeparatorResearch
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactFlagBezout6543Research ContactFlagTriangularProjectionResearch
open ContactFlagProjectionPositivity6543Research
open ContactActiveNestedFlagData6733Research ContactActiveNestedFlagCosts6733Research
open ContactActiveNestedFixedPowers6733Research
open ContactFlagPlaneResultantBounds6733Research
open ContactFlagPlaneIndexedChannel6733Research
open ContactWeightedGroupedResultantChannel6733Research
open ContactWeightedChannelUtilities6733Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
variable {surfaceFlag tailFlag:FlagDegree}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
variable (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
variable (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
variable (hG:Irreducible G) (hproper:¬ G∣T)
variable (hGsupport:G.support ⊆ flagSupport surfaceFlag)
variable (hTsupport:T.support ⊆ flagSupport tailFlag)
variable (multiplicity:RegularComponent Omega G T H → ℕ)
variable (powers:ActiveNestedFixedPowers base hactive hZ hSderiv D multiplicity)
noncomputable def activeNestedZChannel
   [Nonempty (ActiveNestedZIndex (G:=G) (T:=T) (H:=H))]:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     (fun a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)↦multiplicity a.1)
     (fun a↦U.toPrimeFlagBudgetFamily.zCost a.1)
     (flagMixed surfaceFlag tailFlag unitZFlag):=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
   hGsupport hTsupport
 let a₀:ActiveNestedZIndex (G:=G) (T:=T) (H:=H):=Classical.choice inferInstance
 have hTne:T≠0:=fun hz↦hproper (hz ▸ dvd_zero G)
 have hres:=flagPlaneResultant_ne D.lam D.mu (D.mu*D.lam) zOrder
   hG hproper a₀.1 (activeNestedZTranscendental base hactive hSderiv D a₀)
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).2
 have hdeg:=flagPlaneResultant_z_degree_le surfaceFlag tailFlag D.lam D.mu
   (D.mu*D.lam) hGsupport hTsupport hTne
 let raw:=indexedWeightedFlagPlaneChannel_of_fixedFactors
   (activeNestedZComponent (G:=G) (T:=T) (H:=H))
   D.lam D.mu (D.mu*D.lam) zOrder
   (activeNestedZTranscendental base hactive hSderiv D)
   (activeNestedZFinite base hactive hZ hSderiv D)
   (activeNestedZGenerates base hactive hSderiv D)
   (activeNestedZGate base hactive hZ hSderiv D)
   (fun a↦multiplicity a.1)
   (flagPlaneResultant D.lam D.mu (D.mu*D.lam) zOrder G T)
   (flagMixed surfaceFlag tailFlag unitZFlag) hres hdeg powers.z
 exact recost raw fun a↦
   (activeNestedUnitFamily_zCost_eq_flagCost base hactive hZ hSderiv D
     hG hproper hGsupport hTsupport a).le
noncomputable def activeNestedUChannel
   [Nonempty (RegularComponent Omega G T H)]:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   WeightedGroupedResultantChannel (Base:=RatFunc Omega) multiplicity
     U.toPrimeFlagBudgetFamily.yzCost
     (flagMixed surfaceFlag tailFlag unitYZFlag):=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper hGsupport hTsupport
 let C₀:RegularComponent Omega G T H:=Classical.choice inferInstance
 have hTne:T≠0:=fun hz↦hproper (hz ▸ dvd_zero G)
 have hres:=flagPlaneResultant_ne D.lam D.mu (D.mu*D.lam) uOrder
   hG hproper C₀ (activeNestedUTranscendental base hactive hSderiv D C₀)
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).1
 have hdeg:=flagPlaneResultant_u_degree_le surfaceFlag tailFlag D.lam D.mu
   (D.mu*D.lam) hGsupport hTsupport hTne
 let raw:=indexedWeightedFlagPlaneChannel_of_fixedFactors
   (fun C:RegularComponent Omega G T H↦C) D.lam D.mu (D.mu*D.lam) uOrder
   (activeNestedUTranscendental base hactive hSderiv D)
   (activeNestedUFinite base hactive hSderiv D)
   (activeNestedUGenerates base hactive hSderiv D)
   (activeNestedUGate base hactive hSderiv D) multiplicity
   (flagPlaneResultant D.lam D.mu (D.mu*D.lam) uOrder G T)
   (flagMixed surfaceFlag tailFlag unitYZFlag) hres hdeg powers.u
 exact recost raw fun C↦
   (activeNestedUnitFamily_uCost_eq_flagCost base hactive hZ hSderiv D
     hG hproper hGsupport hTsupport C).le
noncomputable def activeNestedVChannel
   [Nonempty (RegularComponent Omega G T H)]:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   WeightedGroupedResultantChannel (Base:=RatFunc Omega) multiplicity
     U.toPrimeFlagBudgetFamily.allCost
     (flagMixed surfaceFlag tailFlag unitAllFlag):=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper hGsupport hTsupport
 let C₀:RegularComponent Omega G T H:=Classical.choice inferInstance
 have hTne:T≠0:=fun hz↦hproper (hz ▸ dvd_zero G)
 have hres:=flagPlaneResultant_ne D.lam D.mu (D.mu*D.lam) vOrder
   hG hproper C₀ (activeNestedVTranscendental base hactive hSderiv D C₀)
   (flag_v_outer_positive_of_directional D.lam D.mu G D.directional)
 have hdeg:=flagPlaneResultant_v_degree_le surfaceFlag tailFlag D.lam D.mu
   (D.mu*D.lam) hGsupport hTsupport hTne
 let raw:=indexedWeightedFlagPlaneChannel_of_fixedFactors
   (fun C:RegularComponent Omega G T H↦C) D.lam D.mu (D.mu*D.lam) vOrder
   (activeNestedVTranscendental base hactive hSderiv D)
   (activeNestedVFinite base hactive hSderiv D)
   (activeNestedVGenerates base hactive hSderiv D)
   (activeNestedVGate base hactive hSderiv D) multiplicity
   (flagPlaneResultant D.lam D.mu (D.mu*D.lam) vOrder G T)
   (flagMixed surfaceFlag tailFlag unitAllFlag) hres hdeg powers.v
 exact recost raw fun C↦
   (activeNestedUnitFamily_allCost_eq_flagCost base hactive hZ hSderiv D
     hG hproper hGsupport hTsupport C).le
end
end ProximityPrize.SubmissionLower.ContactActiveNestedChannels6733Research
