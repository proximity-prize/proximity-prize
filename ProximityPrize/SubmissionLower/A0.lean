import ProximityPrize.SubmissionLower.A1
import ProximityPrize.SubmissionLower.O
import ProximityPrize.SubmissionLower.C4
namespace ProximityPrize.SubmissionLower.RCN029
open scoped Classical BigOperators
open RCN264 RCN002
open RCN341
open RCN037
open RCN038
open RCN125
open RCN031
open RCN106
open RCN111
open RCN112
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
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
variable (multiplicity:RegularComponent Omega G T H → ℕ)
def ActiveNestedZFixedPowers:Prop:=
 ∀ q (hq:Irreducible q) (hm:q.Monic)
   (a₀:IndexedFactorFiber
     (activeNestedZComponent (G:=G) (T:=T) (H:=H))
     D.lam D.mu (D.mu*D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D) q),
   q^(∑ a:IndexedFactorFiber
     (activeNestedZComponent (G:=G) (T:=T) (H:=H))
     D.lam D.mu (D.mu*D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D) q,
     multiplicity a.1.1*indexedPlaneResidueWeight
       (activeNestedZComponent (G:=G) (T:=T) (H:=H))
       D.lam D.mu (D.mu*D.lam) zOrder
       (activeNestedZTranscendental base hactive hSderiv D)
       (activeNestedZFinite base hactive hZ hSderiv D) a.1)∣
     flagPlaneResultant D.lam D.mu (D.mu*D.lam) zOrder G T
def ActiveNestedUFixedPowers:Prop:=
 ∀ q (hq:Irreducible q) (hm:q.Monic)
   (C₀:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D) q),
   q^(∑ C:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D) q,
     multiplicity C.1*indexedPlaneResidueWeight
       (fun C:RegularComponent Omega G T H↦C)
       D.lam D.mu (D.mu*D.lam) uOrder
       (activeNestedUTranscendental base hactive hSderiv D)
       (activeNestedUFinite base hactive hSderiv D) C.1)∣
     flagPlaneResultant D.lam D.mu (D.mu*D.lam) uOrder G T
def ActiveNestedVFixedPowers:Prop:=
 ∀ q (hq:Irreducible q) (hm:q.Monic)
   (C₀:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D) q),
   q^(∑ C:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D) q,
     multiplicity C.1*indexedPlaneResidueWeight
       (fun C:RegularComponent Omega G T H↦C)
       D.lam D.mu (D.mu*D.lam) vOrder
       (activeNestedVTranscendental base hactive hSderiv D)
       (activeNestedVFinite base hactive hSderiv D) C.1)∣
     flagPlaneResultant D.lam D.mu (D.mu*D.lam) vOrder G T
structure ActiveNestedFixedPowers:Prop where
 z:ActiveNestedZFixedPowers base hactive hZ hSderiv D multiplicity
 u:ActiveNestedUFixedPowers base hactive hSderiv D multiplicity
 v:ActiveNestedVFixedPowers base hactive hSderiv D multiplicity
end
end ProximityPrize.SubmissionLower.RCN029
