import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualSurfaceResearch
import ProximityPrize.SubmissionLower.ContactTaylorNumerators
import ProximityPrize.SubmissionLower.ContactMovingPoleTransport6719Research
import ProximityPrize.SubmissionLower.ContactMovingProjection6676Research

namespace ProximityPrize.SubmissionLower.ContactResidualContactQuotient6719Research

open scoped Classical
open ContactIdentityResidualGlobalTransformResearch
open ContactIdentityResidualSurfaceResearch ContactGenericSurface
open ContactTaylorNumerators ContactFlagBezout6543Research
open ContactFlagAffineResidualAutomorphismResearch

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K Ω : Type} [Field K] [Field Ω]

@[simp] theorem pderiv_embedX_Y (P : Polynomial K) :
    MvPolynomial.pderiv (1 : Fin 4) (embedX K P) = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial n a => simp [embedX, MvPolynomial.pderiv_X]

@[simp] theorem pderiv_embedX_X (P : Polynomial K) :
    MvPolynomial.pderiv (0 : Fin 4) (embedX K P) = embedX K P.derivative := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial n a =>
      simp [embedX, Polynomial.derivative_monomial, Derivation.leibniz]
      ring

def baseStep (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  MvPolynomial.pderiv (0 : Fin 4) F +
    MvPolynomial.X 2 * MvPolynomial.pderiv (1 : Fin 4) F

@[simp] theorem baseStep_C
    (c : K) : baseStep (MvPolynomial.C c : MvPolynomial (Fin 4) K) = 0 := by
  simp [baseStep]

@[simp] theorem baseStep_add (F G : MvPolynomial (Fin 4) K) :
    baseStep (F+G) = baseStep F + baseStep G := by
  simp [baseStep, mul_add]
  ring

theorem baseStep_mul (F G : MvPolynomial (Fin 4) K) :
    baseStep (F*G) = baseStep F*G + F*baseStep G := by
  simp only [baseStep, Derivation.leibniz]
  ring

def residualAcceleration (P0 P1 V : Polynomial K) : MvPolynomial (Fin 4) K :=
  embedX K P0.derivative.derivative +
    MvPolynomial.X 3 * embedX K P1.derivative.derivative +
    embedX K V.derivative.derivative * MvPolynomial.X 1 +
    2 * embedX K V.derivative * MvPolynomial.X 2

theorem baseStep_image (P0 P1 V : Polynomial K) (i : Fin 4) :
    baseStep (globalResidualImage P0 P1 V i) =
      globalResidualHom P0 P1 V (baseStep (MvPolynomial.X i)) +
      residualAcceleration P0 P1 V *
        globalResidualHom P0 P1 V (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.X i)) := by
  fin_cases i <;>
    simp [baseStep, globalResidualImage, residualAcceleration, Derivation.leibniz] <;> ring

theorem baseStep_globalResidualHom (P0 P1 V : Polynomial K)
    (F : MvPolynomial (Fin 4) K) :
    baseStep (globalResidualHom P0 P1 V F) =
      globalResidualHom P0 P1 V (baseStep F) +
      residualAcceleration P0 P1 V *
        globalResidualHom P0 P1 V (MvPolynomial.pderiv (2 : Fin 4) F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [baseStep]
  | add F G hF hG =>
      simp [hF, hG, mul_add]
      ring
  | mul_X F i hF =>
      rw [map_mul, baseStep_mul, hF, globalResidualHom_X, baseStep_image]
      simp only [baseStep_mul, Derivation.leibniz, map_add, map_mul,
        globalResidualHom_X]
      simp only [smul_eq_mul, map_mul, globalResidualHom_X]
      ring

theorem polyH_globalResidualHom (P0 P1 V : Polynomial K)
    (F : MvPolynomial (Fin 4) K) :
    polyH K (globalResidualHom P0 P1 V F) =
      embedX K V * globalResidualHom P0 P1 V (polyH K F) :=
  pderiv_globalResidualHom_R P0 P1 V F

theorem polyG_globalResidualHom (P0 P1 V : Polynomial K)
    (F : MvPolynomial (Fin 4) K) :
    polyG K (globalResidualHom P0 P1 V F) =
      globalResidualHom P0 P1 V (polyG K F) -
      residualAcceleration P0 P1 V * globalResidualHom P0 P1 V (polyH K F) := by
  change -(baseStep (globalResidualHom P0 P1 V F)) =
    globalResidualHom P0 P1 V (-baseStep F) - residualAcceleration P0 P1 V *
      globalResidualHom P0 P1 V (MvPolynomial.pderiv (2 : Fin 4) F)
  rw [baseStep_globalResidualHom, map_neg]
  ring

theorem surfaceMap_residualAcceleration (φ : Polynomial K →+* Ω)
    (P0 P1 V : Polynomial K) :
    surfaceMap φ (residualAcceleration P0 P1 V) =
      MvPolynomial.C (φ P0.derivative.derivative) +
      MvPolynomial.X 2 * MvPolynomial.C (φ P1.derivative.derivative) +
      MvPolynomial.C (φ V.derivative.derivative) * MvPolynomial.X 0 +
      2 * MvPolynomial.C (φ V.derivative) * MvPolynomial.X 1 := by
  have htwo : surfaceMap φ (2 : MvPolynomial (Fin 4) K) = 2 := by
    exact map_ofNat (surfaceMap φ) 2
  simp [residualAcceleration, htwo]

private theorem const_mul_X_unitAll (c : Ω) (i : Fin 3) :
    PolynomialInFlag unitAllFlag (MvPolynomial.C c * MvPolynomial.X i) := by
  intro d hd
  rw [MvPolynomial.C_mul_X_eq_monomial] at hd
  have h : d = Finsupp.single i 1 :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  fin_cases i <;> simp [InFlag, unitAllFlag]

theorem surfaceMap_residualAcceleration_inFlag (φ : Polynomial K →+* Ω)
    (P0 P1 V : Polynomial K) :
    PolynomialInFlag unitAllFlag (surfaceMap φ (residualAcceleration P0 P1 V)) := by
  rw [surfaceMap_residualAcceleration]
  have h := ContactMovingProjection6676Research.inFlag_add_poly
    (ContactMovingProjection6676Research.inFlag_add_poly
      (ContactMovingProjection6676Research.inFlag_add_poly
        (ContactMovingProjection6676Research.inFlag_const unitAllFlag
          (φ P0.derivative.derivative))
        (const_mul_X_unitAll (φ P1.derivative.derivative) 2))
      (const_mul_X_unitAll (φ V.derivative.derivative) 0))
    (const_mul_X_unitAll (2 * φ V.derivative) 1)
  convert h using 1
  simp only [map_mul, map_ofNat]
  ring

theorem scaled_acceleration_inFlag (φ : Polynomial K →+* Ω)
    (P0 P1 V : Polynomial K) (c : Ω) :
    PolynomialInFlag unitAllFlag
      (MvPolynomial.C c * surfaceMap φ (residualAcceleration P0 P1 V)) := by
  change PolynomialInFlag ((⟨0,0,0⟩ : FlagDegree) + unitAllFlag) _
  exact ContactMovingProjection6676Research.inFlag_mul_poly
    (ContactMovingProjection6676Research.inFlag_const ⟨0,0,0⟩ c)
    (surfaceMap_residualAcceleration_inFlag φ P0 P1 V)

theorem surfaceMap_polyH_residual (φ : Polynomial K →+* Ω)
    (P0 P1 V : Polynomial K) (F : MvPolynomial (Fin 4) K) :
    surfaceMap φ (polyH K (globalResidualHom P0 P1 V F)) =
      MvPolynomial.C (φ V) *
        residualAlgHom (φ P0) (φ V) (φ P1)
          (φ P0.derivative) (φ V.derivative) (φ P1.derivative)
          (surfaceMap φ (polyH K F)) := by
  rw [polyH_globalResidualHom, map_mul, surfaceMap_embedX,
    surfaceMap_globalResidualHom_eq_residualAlgHom]

theorem surfaceMap_polyG_residual (φ : Polynomial K →+* Ω)
    (P0 P1 V : Polynomial K) (F : MvPolynomial (Fin 4) K) :
    surfaceMap φ (polyG K (globalResidualHom P0 P1 V F)) =
      residualAlgHom (φ P0) (φ V) (φ P1)
          (φ P0.derivative) (φ V.derivative) (φ P1.derivative)
          (surfaceMap φ (polyG K F)) -
      surfaceMap φ (residualAcceleration P0 P1 V) *
        residualAlgHom (φ P0) (φ V) (φ P1)
          (φ P0.derivative) (φ V.derivative) (φ P1.derivative)
          (surfaceMap φ (polyH K F)) := by
  rw [polyG_globalResidualHom, map_sub, map_mul,
    surfaceMap_globalResidualHom_eq_residualAlgHom,
    surfaceMap_globalResidualHom_eq_residualAlgHom]

theorem contact_quotient_residual {E : Type} [Field E]
    (ψ : MvPolynomial (Fin 4) K →+* E)
    (P0 P1 V : Polynomial K) (F : MvPolynomial (Fin 4) K)
    (hV : ψ (embedX K V) ≠ 0)
    (hH : ψ (globalResidualHom P0 P1 V (polyH K F)) ≠ 0) :
    ψ (polyG K (globalResidualHom P0 P1 V F)) /
        ψ (polyH K (globalResidualHom P0 P1 V F)) =
      (ψ (globalResidualHom P0 P1 V (polyG K F)) /
        ψ (globalResidualHom P0 P1 V (polyH K F)) -
          ψ (residualAcceleration P0 P1 V)) / ψ (embedX K V) := by
  rw [polyG_globalResidualHom, polyH_globalResidualHom, map_sub, map_mul, map_mul]
  field_simp [hV, hH]

theorem contact_quotient_surfaceMap {E : Type} [Field E]
    (φ : Polynomial K →+* Ω) (ev : MvPolynomial (Fin 3) Ω →+* E)
    (P0 P1 V : Polynomial K) (F : MvPolynomial (Fin 4) K)
    (hV : ev (MvPolynomial.C (φ V)) ≠ 0)
    (hH : ev (surfaceMap φ (globalResidualHom P0 P1 V (polyH K F))) ≠ 0) :
    ev (surfaceMap φ (polyG K (globalResidualHom P0 P1 V F))) /
        ev (surfaceMap φ (polyH K (globalResidualHom P0 P1 V F))) =
      (ev (surfaceMap φ (globalResidualHom P0 P1 V (polyG K F))) /
        ev (surfaceMap φ (globalResidualHom P0 P1 V (polyH K F))) -
          ev (surfaceMap φ (residualAcceleration P0 P1 V))) /
        ev (MvPolynomial.C (φ V)) := by
  have hv : (ev.comp (surfaceMap φ)) (embedX K V) ≠ 0 := by
    simpa only [RingHom.comp_apply, surfaceMap_embedX] using hV
  simpa only [RingHom.comp_apply, surfaceMap_embedX] using
    contact_quotient_residual (ev.comp (surfaceMap φ)) P0 P1 V F hv hH

end
end ProximityPrize.SubmissionLower.ContactResidualContactQuotient6719Research
