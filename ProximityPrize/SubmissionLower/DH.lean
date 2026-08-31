import ProximityPrize.SubmissionLower.DI
import ProximityPrize.SubmissionLower.DK
import ProximityPrize.SubmissionLower.DL
namespace ProximityPrize.SubmissionLower.RCN027
open scoped Classical BigOperators
open RCN264 RCN002 RCN341 RCN042 RCN344 RCN037 RCN038 RCN095 RCN031 RCN030 RCN029 RCN028 RCN032 RCN033 RCN343 RCN342 RCN338
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag tailFlag:FlagDegree}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (hG:Irreducible G) (hproper:¬ G∣T)
 (hGsupport:G.support ⊆ flagSupport surfaceFlag)
 (hTsupport:T.support ⊆ flagSupport tailFlag)
 (multiplicity:RegularComponent Omega G T H → ℕ)
 (powers:ActiveNestedFixedPowers base hactive hZ hSderiv D multiplicity)
noncomputable def activeNestedWeightedCertificate:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   RegularComponentWeightedInertiaResultantCertificate
     U.toPrimeFlagBudgetFamily multiplicity:=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
   hGsupport hTsupport
 let B:=U.toPrimeFlagBudgetFamily
 let zIndex:=ActiveNestedZIndex (G:=G) (T:=T) (H:=H)
 let zComponent:=activeNestedZComponent (G:=G) (T:=T) (H:=H)
 let zChannel:WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     (fun a:zIndex↦multiplicity (zComponent a))
     (fun a↦B.zCost (zComponent a))
     (flagMixed surfaceFlag tailFlag unitZFlag):=by
   by_cases hz:Nonempty zIndex
   · letI:Nonempty zIndex:=hz
     exact activeNestedZChannel base hactive hZ hSderiv D hG hproper
       hGsupport hTsupport multiplicity powers
   · letI:IsEmpty zIndex:=⟨fun a↦hz ⟨a⟩⟩
     exact emptyChannel _ _ _
 let uChannel:WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     multiplicity B.yzCost (flagMixed surfaceFlag tailFlag unitYZFlag):=by
   by_cases hu:Nonempty (RegularComponent Omega G T H)
   · letI:Nonempty (RegularComponent Omega G T H):=hu
     exact activeNestedUChannel base hactive hZ hSderiv D hG hproper
       hGsupport hTsupport multiplicity powers
   · letI:IsEmpty (RegularComponent Omega G T H):=⟨fun C↦hu ⟨C⟩⟩
     exact emptyChannel _ _ _
 let allChannel:WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     multiplicity B.allCost (flagMixed surfaceFlag tailFlag unitAllFlag):=by
   by_cases hv:Nonempty (RegularComponent Omega G T H)
   · letI:Nonempty (RegularComponent Omega G T H):=hv
     exact activeNestedVChannel base hactive hZ hSderiv D hG hproper
       hGsupport hTsupport multiplicity powers
   · letI:IsEmpty (RegularComponent Omega G T H):=⟨fun C↦hv ⟨C⟩⟩
     exact emptyChannel _ _ _
 have zRewrite:(∑ C,multiplicity C*B.zCost C)=
     ∑ a:zIndex,multiplicity (zComponent a)*B.zCost (zComponent a):=by
   calc
     _=∑ C,multiplicity C*coordinateDegree Omega
         (CoordinateField Omega C.1)
         (coordinateOfGate (coordinate Omega C.1 2) (hZ C)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [activeNestedUnitFamily_zCost base hactive hZ hSderiv D hG
         hproper hGsupport hTsupport]
     _=∑ a:zIndex,multiplicity a.1*coordinateDegree Omega
         (CoordinateField Omega a.1.1)
         (coordinateOfGate (coordinate Omega a.1.1 2) (hZ a.1)):=
       sum_mul_coordinateOfGate_eq_active
         (fun C:RegularComponent Omega G T H↦CoordinateField Omega C.1)
         (fun C↦coordinate Omega C.1 2) hZ multiplicity
     _=_:=by
       apply Finset.sum_congr rfl
       intro a _
       rw [activeNestedUnitFamily_zCost base hactive hZ hSderiv D hG
         hproper hGsupport hTsupport]
       rfl
 exact regularComponentWeightedInertiaCertificate_of_active_channels B
   multiplicity zComponent (fun C:RegularComponent Omega G T H↦C)
   zRewrite rfl zChannel uChannel allChannel
end
end ProximityPrize.SubmissionLower.RCN027
