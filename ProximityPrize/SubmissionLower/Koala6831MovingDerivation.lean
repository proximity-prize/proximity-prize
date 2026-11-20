import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs


namespace ProximityPrize.SubmissionLower.Koala6831Moving

noncomputable section

variable {K : Type*} [CommRing K]

abbrev P4 (K : Type*) [CommRing K] := MvPolynomial (Fin 4) K

structure FlowData (K : Type*) [CommRing K] where
  d0 : Polynomial K
  a0 : Polynomial K
  a1 : Polynomial K
  c0 : Polynomial K
  c1 : Polynomial K

def liftX (f : Polynomial K) : P4 K :=
  Polynomial.aeval (MvPolynomial.X (0 : Fin 4) : P4 K) f

def affine (f0 f1 : Polynomial K) : P4 K :=
  liftX f0 + MvPolynomial.X (3 : Fin 4) * liftX f1

namespace FlowData

variable (B : FlowData K)

def A : P4 K := affine B.a0 B.a1

def AX : P4 K := affine B.a0.derivative B.a1.derivative

def C : P4 K := affine B.c0 B.c1

def CX : P4 K := affine B.c0.derivative B.c1.derivative

def minor : P4 K :=
  liftX B.a1 * liftX B.c0 - liftX B.a0 * liftX B.c1

def minorX : P4 K :=
  liftX B.a1.derivative * liftX B.c0 + liftX B.a1 * liftX B.c0.derivative -
    (liftX B.a0.derivative * liftX B.c1 + liftX B.a0 * liftX B.c1.derivative)

def denominator : P4 K := liftX B.d0 * B.A

def denominatorX : P4 K :=
  liftX B.d0.derivative * B.A + liftX B.d0 * B.AX

def yCoefficient : P4 K :=
  B.A * (liftX B.d0)^2 * liftX B.a1 * MvPolynomial.X (1 : Fin 4) + B.denominator * B.minor

def rCoefficient : P4 K :=
  (liftX B.d0)^2 * (liftX B.a1.derivative * B.A - liftX B.a1 * B.AX) *
      MvPolynomial.X (1 : Fin 4) +
    B.A * (liftX B.d0)^2 * liftX B.a1 * MvPolynomial.X (2 : Fin 4) +
    B.denominator * B.minorX - B.denominatorX * B.minor

def flow : Derivation K (P4 K) (P4 K) :=
  B.denominator^2 • MvPolynomial.pderiv (3 : Fin 4) +
    B.yCoefficient • MvPolynomial.pderiv (1 : Fin 4) +
    B.rCoefficient • MvPolynomial.pderiv (2 : Fin 4)

theorem flow_apply (P : P4 K) :
    B.flow P =
      B.denominator^2 * MvPolynomial.pderiv (3 : Fin 4) P +
        B.yCoefficient * MvPolynomial.pderiv (1 : Fin 4) P +
        B.rCoefficient * MvPolynomial.pderiv (2 : Fin 4) P := by
  simp only [flow, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]

theorem flow_X : B.flow (MvPolynomial.X (0 : Fin 4)) = 0 := by
  simp [flow_apply, MvPolynomial.pderiv_X]

theorem flow_Y : B.flow (MvPolynomial.X (1 : Fin 4)) = B.yCoefficient := by
  simp [flow_apply, MvPolynomial.pderiv_X]

theorem flow_R : B.flow (MvPolynomial.X (2 : Fin 4)) = B.rCoefficient := by
  simp [flow_apply, MvPolynomial.pderiv_X]

theorem flow_Z : B.flow (MvPolynomial.X (3 : Fin 4)) = B.denominator^2 := by
  simp [flow_apply, MvPolynomial.pderiv_X]



def numerator : P4 K := liftX B.d0 * MvPolynomial.X (1 : Fin 4) + B.C

def jetNumerator : P4 K :=
  B.A * (liftX B.d0.derivative * MvPolynomial.X (1 : Fin 4) + liftX B.d0 * MvPolynomial.X (2 : Fin 4) + B.CX) -
    B.AX * B.numerator



end FlowData

section ExtractPartner

variable {R : Type*} [CommRing R] [Algebra K R]
variable [UniqueFactorizationMonoid R]


end ExtractPartner


end

end ProximityPrize.SubmissionLower.Koala6831Moving
