import ProximityPrize.SubmissionLower.ContactActiveNestedChannels6733Research
import ProximityPrize.SubmissionLower.ContactActiveSubtypeWeightedSum6733Research
import ProximityPrize.SubmissionLower.ContactActiveThreeChannelAssembly6733Research
namespace ProximityPrize.SubmissionLower.ContactActiveNestedCertificate6733Research
open scoped Classical BigOperators
open ContactRegularComponentCover ActualCurveCoordinateField
open ContactWeakSeparableSeparatorResearch
open ContactAdaptiveProjectionCoordinateResearch CoordinateBoxZeroCount
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactFlagBezout6543Research
open ContactActiveNestedFlagData6733Research ContactActiveNestedFlagCosts6733Research
open ContactActiveNestedFixedPowers6733Research ContactActiveNestedChannels6733Research
open ContactActiveSubtypeWeightedSum6733Research
open ContactActiveThreeChannelAssembly6733Research
open ContactWeightedGroupedResultantChannel6733Research
open ContactWeightedChannelUtilities6733Research
open ContactTwoTailResultantProvider6732Research
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
end ProximityPrize.SubmissionLower.ContactActiveNestedCertificate6733Research
