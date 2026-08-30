import ProximityPrize.SubmissionLower.A2
import ProximityPrize.SubmissionLower.Z1
namespace ProximityPrize.SubmissionLower.RCN031
open RCN002 RCN264
open RCN341
open RCN037
open RCN038
open RCN093 RCN125
open RCN116 RCN120
open RCN021 RCN022
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
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
abbrev ActiveNestedZIndex:={C:RegularComponent Omega G T H//
 Transcendental Omega (coordinate Omega C.1 2)}
def activeNestedZComponent:ActiveNestedZIndex (G:=G) (T:=T) (H:=H) →
   RegularComponent Omega G T H:=Subtype.val
theorem activeNestedZComponent_injective:Function.Injective
   (activeNestedZComponent (G:=G) (T:=T) (H:=H)):=
 Subtype.val_injective
def activeNestedZTranscendental
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):
   Transcendental Omega
     (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (zOrder 0))):=by
 simpa [zOrder,Equiv.swap_apply_def] using a.2
def activeNestedUTranscendental (C:RegularComponent Omega G T H):
   Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (uOrder 0))):=by
 simpa [uOrder] using D.uTranscendental C
def activeNestedVTranscendental (C:RegularComponent Omega G T H):
   Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (vOrder 0))):=by
 simpa [vOrder,Equiv.swap_apply_def] using D.allAffineTranscendental C
include hZ in
theorem activeNestedZGate
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H))
   (hx:Transcendental Omega
     (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (zOrder 0)))):
   (letI:=flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam) zOrder hx
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega a.1.1))∧
   (letI:=flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam) zOrder hx
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega a.1.1)):=by
 have hx':Transcendental Omega (coordinate Omega a.1.1 2):=by
   simpa [zOrder,Equiv.swap_apply_def] using hx
 have hemb:=elementEmbedding_congr hx hx' (by simp [zOrder,flagEvaluation_X_two])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega a.1.1):=
     (elementEmbedding Omega (CoordinateField Omega a.1.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega a.1.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega a.1.1):=
     (elementEmbedding Omega (CoordinateField Omega a.1.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega a.1.1))
 rw [hemb]
 exact hZ a.1 hx'
theorem activeNestedUGate (C:RegularComponent Omega G T H)
   (hx:Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (uOrder 0)))):
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) uOrder hx
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) uOrder hx
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)):=by
 have hx':Transcendental Omega (affineU Omega C.1 D.lam):=by
   simpa [uOrder] using hx
 have hemb:=elementEmbedding_congr hx hx' (by simp [uOrder,flagEvaluation_X_zero])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
 rw [hemb]
 exact D.uGate C hx'
theorem activeNestedVGate (C:RegularComponent Omega G T H)
   (hx:Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (vOrder 0)))):
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) vOrder hx
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) vOrder hx
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)):=by
 have hemb:=elementEmbedding_congr hx (D.allAffineTranscendental C)
   (by simp [vOrder,flagEvaluation_X_one])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
 rw [hemb]
 exact ⟨D.allFinite C,D.allSeparable C⟩
def activeNestedZFinite (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):=
 (activeNestedZGate base hactive hZ hSderiv D a
   (activeNestedZTranscendental base hactive hSderiv D a)).1
def activeNestedUFinite (C:RegularComponent Omega G T H):=
 (activeNestedUGate base hactive hSderiv D C
   (activeNestedUTranscendental base hactive hSderiv D C)).1
def activeNestedVFinite (C:RegularComponent Omega G T H):=
 (activeNestedVGate base hactive hSderiv D C
   (activeNestedVTranscendental base hactive hSderiv D C)).1
theorem activeNestedZGenerates
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):
   letI:=flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam)
     zOrder (activeNestedZTranscendental base hactive hSderiv D a)
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (zOrder 2)),
       flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (zOrder 1))}:
       Set (CoordinateField Omega a.1.1))=⊤:=by
 have hemb:=elementEmbedding_congr
   (activeNestedZTranscendental base hactive hSderiv D a) a.2
   (by simp [zOrder,flagEvaluation_X_two])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega a.1.1):=
     (elementEmbedding Omega (CoordinateField Omega a.1.1)
       (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (zOrder 0)))
       (activeNestedZTranscendental base hactive hSderiv D a)).toRingHom.toAlgebra;
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (zOrder 2)),
       flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (zOrder 1))}:Set (CoordinateField Omega a.1.1))=⊤)
 rw [hemb]
 simpa [zOrder,Equiv.swap_apply_def] using flag_generators_z Omega a.1.1 D.lam D.mu
   (D.mu*D.lam) a.2
theorem activeNestedUGenerates (C:RegularComponent Omega G T H):
   letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam)
     uOrder (activeNestedUTranscendental base hactive hSderiv D C)
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (uOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (uOrder 1))}:
       Set (CoordinateField Omega C.1))=⊤:=by
 have hemb:=elementEmbedding_congr
   (activeNestedUTranscendental base hactive hSderiv D C)
   (D.uTranscendental C) (by simp [uOrder,flagEvaluation_X_zero])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (uOrder 0)))
       (activeNestedUTranscendental base hactive hSderiv D C)).toRingHom.toAlgebra;
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (uOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (uOrder 1))}:Set (CoordinateField Omega C.1))=⊤)
 rw [hemb]
 simpa [uOrder] using flag_generators_u Omega C.1 D.lam D.mu
   (D.mu*D.lam) (D.uTranscendental C)
theorem activeNestedVGenerates (C:RegularComponent Omega G T H):
   letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam)
     vOrder (activeNestedVTranscendental base hactive hSderiv D C)
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (vOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (vOrder 1))}:
       Set (CoordinateField Omega C.1))=⊤:=by
 have hemb:=elementEmbedding_congr
   (activeNestedVTranscendental base hactive hSderiv D C)
   (D.allAffineTranscendental C) (by simp [vOrder,flagEvaluation_X_one])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (vOrder 0)))
       (activeNestedVTranscendental base hactive hSderiv D C)).toRingHom.toAlgebra;
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (vOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (vOrder 1))}:Set (CoordinateField Omega C.1))=⊤)
 rw [hemb]
 simpa [vOrder,Equiv.swap_apply_def] using flag_generators_v Omega C.1 D.lam D.mu
   (D.mu*D.lam) (D.allAffineTranscendental C)
end
end ProximityPrize.SubmissionLower.RCN031
