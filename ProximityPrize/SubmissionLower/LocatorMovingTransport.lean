import ProximityPrize.SubmissionLower.J3
import ProximityPrize.SubmissionLower.P9
import ProximityPrize.SubmissionLower.LocatorFactorAggregate
namespace ProximityPrize.SubmissionLower.LocatorMovingTransport
open scoped Classical BigOperators
open RCN046 RCN066 RCN074 RCN086 RCN095 RCN135 RCN159 RCN198
open RCN237 RCN238 RCN243 RCN264 RCN275 RCN332 RCN341
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure UnitFamilyBundle
   {F I0:Type} [Field F] {Gamma:Finset F} {x:I0 → F}
   {p e w0:ℕ} {flag:FlagDegree} {P:ResidualSupportParameters}
   [CharP (GenericField F) p]
   (S:ResidualStage (polynomialEmbedding F) Gamma x p e flag w0 P)
   (Q:FlagDegree) where
 base:∀ C:FirstTailComponent S, SeparableLiteralCoordinate C.1
 unit:AdaptiveUnitProjectionFamily
   (G:=S.G)
   (T:=globalTailCut (polynomialEmbedding F) S.F (w0 + 1))
   (H:=regularitySurface (polynomialEmbedding F) S.F)
   base flag Q
noncomputable def unitFamily_ofCongruentCut
   {Omega:Type} [Field Omega] [IsAlgClosed Omega]
   {G T T' H:MvPolynomial (Fin 3) Omega} {p q Q:FlagDegree}
   (h:G ∣ T - T')
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   {base':∀ C:RegularComponent Omega G T' H,
     SeparableLiteralCoordinate C.1}
   (U:AdaptiveUnitProjectionFamily base' p q)
   (hbelow:LocatorFactorAggregate.Below q Q) :
   AdaptiveUnitProjectionFamily base p Q:=by
 refine {
   zProjection:=fun C => U.zProjection (regularComponentEquiv h C)
   yzProjection:=fun C => U.yzProjection (regularComponentEquiv h C)
   allProjection:=fun C => U.allProjection (regularComponentEquiv h C)
   zValue:=?_
   allTranscendental:=?_
   zPole_eq:=?_
   yzPole_eq:=?_
   allPole_eq:=?_
   sum_zDegree_le:=?_
   sum_yzDegree_le:=?_
   sum_allDegree_le:=?_ }
 · intro C
   exact U.zValue (regularComponentEquiv h C)
 · intro C
   exact U.allTranscendental (regularComponentEquiv h C)
 · intro C v
   exact U.zPole_eq (regularComponentEquiv h C) v
 · intro C v
   exact U.yzPole_eq (regularComponentEquiv h C) v
 · intro C v
   exact U.allPole_eq (regularComponentEquiv h C) v
 · have hz:=U.sum_zDegree_le
   rw [← (regularComponentEquiv h).sum_comp] at hz
   exact hz.trans (LocatorFactorAggregate.mixed_mono_second p hbelow unitZFlag)
 · have hyz:=U.sum_yzDegree_le
   rw [← (regularComponentEquiv h).sum_comp] at hyz
   exact hyz.trans (LocatorFactorAggregate.mixed_mono_second p hbelow unitYZFlag)
 · have hall:=U.sum_allDegree_le
   rw [← (regularComponentEquiv h).sum_comp] at hall
   exact hall.trans (LocatorFactorAggregate.mixed_mono_second p hbelow unitAllFlag)
theorem unitFamily_ofCongruentCut_costs
   {Omega:Type} [Field Omega] [IsAlgClosed Omega]
   {G T T' H:MvPolynomial (Fin 3) Omega} {p q Q:FlagDegree}
   (h:G ∣ T - T')
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   {base':∀ C:RegularComponent Omega G T' H,
     SeparableLiteralCoordinate C.1}
   (U:AdaptiveUnitProjectionFamily base' p q)
   (hbelow:LocatorFactorAggregate.Below q Q)
   (C:RegularComponent Omega G T H) :
   let V:=unitFamily_ofCongruentCut h base U hbelow
   V.toPrimeFlagBudgetFamily.zCost C =
       (PrimeFlagBudgetFamily.ofCongruentCut h
         U.toPrimeFlagBudgetFamily).zCost C ∧
     V.toPrimeFlagBudgetFamily.yzCost C =
       (PrimeFlagBudgetFamily.ofCongruentCut h
         U.toPrimeFlagBudgetFamily).yzCost C ∧
     V.toPrimeFlagBudgetFamily.allCost C =
       (PrimeFlagBudgetFamily.ofCongruentCut h
         U.toPrimeFlagBudgetFamily).allCost C:=by
 exact ⟨rfl, rfl, rfl⟩
end
end ProximityPrize.SubmissionLower.LocatorMovingTransport
