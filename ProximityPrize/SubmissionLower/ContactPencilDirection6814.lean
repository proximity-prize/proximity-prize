import ProximityPrize.SubmissionLower.RetainedWholeSpace6814
namespace ProximityPrize.SubmissionLower.ContactPencilDirection6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MvPolynomial

variable {K : Type*} [CommRing K]
abbrev JetPoly := MvPolynomial (Fin 5) K

def contactMap (x u0 u1 : K) : JetPoly (K := K) →ₐ[K] JetPoly (K := K) :=
  MvPolynomial.aeval ![MvPolynomial.C x+MvPolynomial.X 0,MvPolynomial.X 1,
    MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4+
      MvPolynomial.X 0*MvPolynomial.X 3-MvPolynomial.X 0^2*MvPolynomial.X 1+
      MvPolynomial.X 0^3*MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

end
end ProximityPrize.SubmissionLower.ContactPencilDirection6814
