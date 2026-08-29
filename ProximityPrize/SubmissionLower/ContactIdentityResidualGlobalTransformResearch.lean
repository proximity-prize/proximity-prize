import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGenericSurface
import ProximityPrize.SubmissionLower.ContactTranslation
import ProximityPrize.SubmissionLower.ContactPolynomialSolutions

/-!
# Global polynomial transform for actual-identity residualization

The nodal decomposition

`S = P0 + gamma * P1 + V * C`

has a polynomial change of ambient coordinates before passing to a geometric
component.  This file constructs that four-variable substitution and proves
the two commutation statements needed by the post-65.33 route:

* specialization at `(X,C,C',gamma)` is specialization of the original
  equation at `(X,S,S',gamma)`;
* after collecting `X` into a coefficient field, the global substitution is
  exactly the componentwise affine-triangular automorphism.

The global substitution is only injective in general (its determinant
contains `V`), so no global irreducibility claim is made.  Once `V` maps to a
nonzero field element, the componentwise map is the genuine algebra
equivalence proved in `ContactFlagAffineResidualAutomorphismResearch`.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalTransformResearch

open ContactGenericSurface ContactTranslation

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K Omega : Type} [Field K] [Field Omega]

abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

/-- Embed a univariate polynomial as a four-variable polynomial in `X`. -/
def embedX (K : Type) [Field K] : Polynomial K →+* Poly4 K :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (0 : Fin 4))

@[simp] theorem embedX_C (a : K) :
    embedX K (Polynomial.C a) = MvPolynomial.C a := by
  simp [embedX]

@[simp] theorem embedX_X :
    embedX K Polynomial.X = MvPolynomial.X (0 : Fin 4) := by
  simp [embedX]

@[simp] theorem pderiv_embedX_R (P : Polynomial K) :
    MvPolynomial.pderiv (2 : Fin 4) (embedX K P) = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial n a =>
      simp [embedX, MvPolynomial.pderiv_X]

@[simp] theorem specialization_embedX (C : Polynomial K) (gamma : K)
    (P : Polynomial K) :
    specialization K C gamma (embedX K P) = P := by
  change ((specialization K C gamma).toRingHom.comp (embedX K)) P =
    (RingHom.id (Polynomial K)) P
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [embedX, specialization, RingHom.comp_apply]
  · simp [embedX, specialization, RingHom.comp_apply]

@[simp] theorem specialization_X (C : Polynomial K) (gamma : K)
    (i : Fin 4) :
    specialization K C gamma (MvPolynomial.X i) =
      ![Polynomial.X, C, C.derivative, Polynomial.C gamma] i := by
  simp [specialization]

@[simp] theorem surfaceMap_embedX (phi : Polynomial K →+* Omega)
    (P : Polynomial K) :
    surfaceMap phi (embedX K P) = MvPolynomial.C (phi P) := by
  change ((surfaceMap phi).comp (embedX K)) P =
    (MvPolynomial.C.comp phi) P
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [embedX, surfaceMap, RingHom.comp_apply]
  · simp [embedX, surfaceMap, RingHom.comp_apply]

@[simp] theorem surfaceMap_X_one (phi : Polynomial K →+* Omega) :
    surfaceMap phi (MvPolynomial.X (1 : Fin 4)) =
      MvPolynomial.X (0 : Fin 3) := by
  simpa using surfaceMap_X_succ phi (0 : Fin 3)

@[simp] theorem surfaceMap_X_two (phi : Polynomial K →+* Omega) :
    surfaceMap phi (MvPolynomial.X (2 : Fin 4)) =
      MvPolynomial.X (1 : Fin 3) := by
  simpa using surfaceMap_X_succ phi (1 : Fin 3)

@[simp] theorem surfaceMap_X_three (phi : Polynomial K →+* Omega) :
    surfaceMap phi (MvPolynomial.X (3 : Fin 4)) =
      MvPolynomial.X (2 : Fin 3) := by
  simpa using surfaceMap_X_succ phi (2 : Fin 3)

/-- Original `(X,Y,R,Z)` coordinates as polynomials in the residual
`(X,C,C',Z)` coordinates. -/
def globalResidualImage (P0 P1 V : Polynomial K) (i : Fin 4) : Poly4 K :=
  ![MvPolynomial.X 0,
    embedX K P0 + MvPolynomial.X 3 * embedX K P1 +
      embedX K V * MvPolynomial.X 1,
    embedX K P0.derivative + MvPolynomial.X 3 * embedX K P1.derivative +
      embedX K V.derivative * MvPolynomial.X 1 +
      embedX K V * MvPolynomial.X 2,
    MvPolynomial.X 3] i

def globalResidualHom (P0 P1 V : Polynomial K) : Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval (globalResidualImage P0 P1 V)

@[simp] theorem globalResidualHom_X (P0 P1 V : Polynomial K) (i : Fin 4) :
    globalResidualHom P0 P1 V (MvPolynomial.X i) =
      globalResidualImage P0 P1 V i := by
  simp [globalResidualHom]

/-- The global residual equation has exactly the intended polynomial
solutions. -/
theorem specialization_globalResidualHom
    (P0 P1 V C : Polynomial K) (gamma : K) (F : Poly4 K) :
    specialization K C gamma (globalResidualHom P0 P1 V F) =
      specialization K
        (P0 + Polynomial.C gamma * P1 + V * C) gamma F := by
  let S := P0 + Polynomial.C gamma * P1 + V * C
  have hSderiv : S.derivative =
      P0.derivative + Polynomial.C gamma * P1.derivative +
        V.derivative * C + V * C.derivative := by
    simp only [S, Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_C, zero_mul, zero_add]
    ring
  have hhom :
      (specialization K C gamma).comp (globalResidualHom P0 P1 V) =
        specialization K S gamma := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [globalResidualImage, hSderiv, S] <;> ring
  exact DFunLike.congr_fun hhom F

theorem globalResidual_solution
    (P0 P1 V C : Polynomial K) (gamma : K) (F : Poly4 K)
    (hsolution : specialization K
      (P0 + Polynomial.C gamma * P1 + V * C) gamma F = 0) :
    specialization K C gamma (globalResidualHom P0 P1 V F) = 0 := by
  rw [specialization_globalResidualHom]
  exact hsolution

/-- The residual derivative coordinate enters the old equation only through
`Rold = ... + V * R`.  Hence the regularity derivative picks up exactly one
factor of the nodal polynomial. -/
theorem pderiv_globalResidualHom_R
    (P0 P1 V : Polynomial K) (F : Poly4 K) :
    MvPolynomial.pderiv (2 : Fin 4) (globalResidualHom P0 P1 V F) =
      embedX K V * globalResidualHom P0 P1 V
        (MvPolynomial.pderiv (2 : Fin 4) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG => simp [hF, hG, mul_add]
  | mul_X F i hF =>
      fin_cases i <;>
        simp [globalResidualImage, hF, Derivation.leibniz] <;> ring

/-- Evaluation at a residual polynomial point is exactly evaluation of the
original equation at the reconstructed polynomial point. -/
theorem eval_globalResidualHom_polynomialPoint
    (coefficients : K →+* Omega) (P0 P1 V C : Polynomial K)
    (gamma : K) (xi : Omega) (F : Poly4 K) :
    MvPolynomial.eval₂Hom coefficients
        (ContactPolynomialSolutions.polynomialPoint coefficients C gamma xi)
        (globalResidualHom P0 P1 V F) =
      MvPolynomial.eval₂Hom coefficients
        (ContactPolynomialSolutions.polynomialPoint coefficients
          (P0 + Polynomial.C gamma * P1 + V * C) gamma xi) F := by
  rw [ContactPolynomialSolutions.eval_polynomialPoint_eq_specialization,
    ContactPolynomialSolutions.eval_polynomialPoint_eq_specialization,
    specialization_globalResidualHom]

/-- Regularity at a reconstructed solution transports provided the nodal
factor is nonzero at the coefficient-field `X` point. -/
theorem globalResidual_regular_at_polynomialPoint
    (coefficients : K →+* Omega) (P0 P1 V C : Polynomial K)
    (gamma : K) (xi : Omega) (F : Poly4 K)
    (hV : V.eval₂ coefficients xi ≠ 0)
    (hregular : MvPolynomial.eval₂Hom coefficients
      (ContactPolynomialSolutions.polynomialPoint coefficients
        (P0 + Polynomial.C gamma * P1 + V * C) gamma xi)
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    MvPolynomial.eval₂Hom coefficients
      (ContactPolynomialSolutions.polynomialPoint coefficients C gamma xi)
      (MvPolynomial.pderiv (2 : Fin 4)
        (globalResidualHom P0 P1 V F)) ≠ 0 := by
  rw [pderiv_globalResidualHom_R, map_mul,
    eval_globalResidualHom_polynomialPoint]
  have hembed : MvPolynomial.eval₂Hom coefficients
      (ContactPolynomialSolutions.polynomialPoint coefficients C gamma xi)
      (embedX K V) = V.eval₂ coefficients xi := by
    change ((MvPolynomial.eval₂Hom coefficients
      (ContactPolynomialSolutions.polynomialPoint coefficients C gamma xi)).comp
        (embedX K)) V = (Polynomial.eval₂RingHom coefficients xi) V
    congr 1
    apply Polynomial.ringHom_ext
    · intro a
      simp [embedX, ContactPolynomialSolutions.polynomialPoint,
        RingHom.comp_apply]
    · simp [embedX, ContactPolynomialSolutions.polynomialPoint,
        RingHom.comp_apply]
  rw [hembed]
  exact mul_ne_zero hV hregular

abbrev Poly3 (Omega : Type) [Field Omega] := MvPolynomial (Fin 3) Omega

/-- The component-field version of `globalResidualImage`.  It is kept as a
plain algebra homomorphism here so this global commutation layer is
independent of the separate automorphism/support implementation. -/
def componentResidualImage
    (aY v bY aR bR cR : Omega) (i : Fin 3) : Poly3 Omega :=
  ![MvPolynomial.C aY + MvPolynomial.C v * MvPolynomial.X 0 +
      MvPolynomial.C bY * MvPolynomial.X 2,
    MvPolynomial.C aR + MvPolynomial.C v * MvPolynomial.X 1 +
      MvPolynomial.C bR * MvPolynomial.X 0 +
      MvPolynomial.C cR * MvPolynomial.X 2,
    MvPolynomial.X 2] i

def componentResidualHom
    (aY v bY aR bR cR : Omega) : Poly3 Omega →ₐ[Omega] Poly3 Omega :=
  MvPolynomial.aeval (componentResidualImage aY v bY aR bR cR)

@[simp] theorem componentResidualHom_X
    (aY v bY aR bR cR : Omega) (i : Fin 3) :
    componentResidualHom aY v bY aR bR cR (MvPolynomial.X i) =
      componentResidualImage aY v bY aR bR cR i := by
  simp [componentResidualHom]

/-- Mapping the `X` coefficients to a field turns the global substitution
into the componentwise affine-triangular substitution. -/
theorem surfaceMap_globalResidualHom
    (phi : Polynomial K →+* Omega) (P0 P1 V : Polynomial K) (F : Poly4 K) :
    surfaceMap phi (globalResidualHom P0 P1 V F) =
      componentResidualHom (phi P0) (phi V) (phi P1)
        (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
        (surfaceMap phi F) := by
  have hhom :
      (surfaceMap phi).comp (globalResidualHom P0 P1 V).toRingHom =
        (componentResidualHom (phi P0) (phi V) (phi P1)
          (phi P0.derivative) (phi V.derivative) (phi P1.derivative)).toRingHom.comp
          (surfaceMap phi) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply, globalResidualHom, componentResidualHom]
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, globalResidualImage, componentResidualImage,
          globalResidualHom, componentResidualHom] <;> ring
  exact RingHom.congr_fun hhom F

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalTransformResearch
