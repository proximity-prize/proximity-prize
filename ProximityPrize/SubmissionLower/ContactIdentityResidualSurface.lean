import ProximityPrize.SubmissionLower.ContactFlagAffineResidualAutomorphism
import ProximityPrize.SubmissionLower.ContactIdentityResidualFamily
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalTransform

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualSurface

open scoped Classical
open ContactFlagAffineResidualAutomorphism
open ContactIdentityResidualGlobalTransform
open ContactIdentityResidualFamily
open ContactIdentityResidualPencil
open ContactPrimeSeedIncidence
open ContactFlagTriangularProjection
open TrivariateShear

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K Omega : Type} [Field K] [Field Omega]

abbrev Poly3 (Omega : Type) [Field Omega] := MvPolynomial (Fin 3) Omega
abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

theorem componentResidualHom_eq_residualAlgHom
    (aY v bY aS bS cS : Omega) :
    componentResidualHom aY v bY aS bS cS =
      residualAlgHom aY v bY aS bS cS := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [componentResidualHom, componentResidualImage,
      residualAlgHom, residualImage]

theorem surfaceMap_globalResidualHom_eq_residualAlgHom
    (phi : Polynomial K →+* Omega) (P0 P1 V : Polynomial K) (F : Poly4 K) :
    ContactGenericSurface.surfaceMap phi
        (globalResidualHom P0 P1 V F) =
      residualAlgHom (phi P0) (phi V) (phi P1)
        (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
        (ContactGenericSurface.surfaceMap phi F) := by
  rw [surfaceMap_globalResidualHom]
  rw [componentResidualHom_eq_residualAlgHom]

theorem pderiv_globalResidualHom
    (P0 P1 V : Polynomial K) (F : Poly4 K) :
    MvPolynomial.pderiv (2 : Fin 4) (globalResidualHom P0 P1 V F) =
      embedX K V * globalResidualHom P0 P1 V
        (MvPolynomial.pderiv (2 : Fin 4) F) :=
  pderiv_globalResidualHom_R P0 P1 V F

theorem surfaceMap_pderiv_globalResidualHom
    (phi : Polynomial K →+* Omega) (P0 P1 V : Polynomial K) (F : Poly4 K) :
    ContactGenericSurface.surfaceMap phi
        (MvPolynomial.pderiv (2 : Fin 4)
          (globalResidualHom P0 P1 V F)) =
      MvPolynomial.C (phi V) *
        residualAlgHom (phi P0) (phi V) (phi P1)
          (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
          (ContactGenericSurface.surfaceMap phi
            (MvPolynomial.pderiv (2 : Fin 4) F)) := by
  rw [pderiv_globalResidualHom, map_mul, surfaceMap_embedX,
    surfaceMap_globalResidualHom_eq_residualAlgHom]

theorem residual_dvd_surfaceMap_globalResidualHom_iff
    (phi : Polynomial K →+* Omega) (hphi : Function.Injective phi)
    (P0 P1 V : Polynomial K) (hV : V ≠ 0)
    (G : Poly3 Omega) (F : Poly4 K) :
    residualAlgHom (phi P0) (phi V) (phi P1)
        (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G ∣
      ContactGenericSurface.surfaceMap phi
        (globalResidualHom P0 P1 V F) ↔
      G ∣ ContactGenericSurface.surfaceMap phi F := by
  rw [surfaceMap_globalResidualHom_eq_residualAlgHom]
  exact residual_dvd_iff _ _ _ _ _ _
    ((map_ne_zero_iff phi hphi).mpr hV) _ _

@[simp] theorem polynomial_eval₂_comp_C_X
    (phi : Polynomial K →+* Omega) (P : Polynomial K) :
    P.eval₂ (phi.comp Polynomial.C) (phi Polynomial.X) = phi P := by
  change (Polynomial.eval₂RingHom (phi.comp Polynomial.C)
    (phi Polynomial.X)) P = phi P
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [RingHom.comp_apply]
  · simp

theorem exists_residual_family_with_surface_data
    {iota : Type} [DecidableEq iota]
    (phi : Polynomial K →+* Omega) (hphi : Function.Injective phi)
    (I nodes : Finset iota) (x u0 u1 : iota → K)
    (w e : ℕ) (hsub : I ⊆ nodes) (hIw : I.card ≤ w)
    (hinj : Set.InjOn x nodes)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hvalues : ∀ gamma ∈ Gamma, ∀ i ∈ I,
      (selected gamma).eval (x i) = u0 i + gamma * u1 i)
    (hno : NoLargeSelectedPencil selected Gamma w e)
    (F : Poly4 K)
    (hsolution : ∀ gamma ∈ Gamma,
      ContactTranslation.specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
        (ContactPolynomialSolutions.polynomialPoint
          (phi.comp Polynomial.C) (selected gamma) gamma (phi Polynomial.X))
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    ∃ P0 P1 : Polynomial K, ∃ residual : K → Polynomial K,
      P0.natDegree ≤ w ∧ P1.natDegree ≤ w ∧
      (∀ gamma ∈ Gamma,
        (residual gamma).natDegree ≤ w - I.card) ∧
      NoLargeSelectedPencil residual Gamma (w - I.card) e ∧
      (∀ gamma ∈ Gamma,
        selected gamma = P0 + Polynomial.C gamma * P1 +
          Lagrange.nodal I x * residual gamma) ∧
      (∀ gamma ∈ Gamma, ∀ j ∈ nodes \ I,
        (selected gamma).eval (x j) = u0 j + gamma * u1 j →
          (residual gamma).eval (x j) =
            residualReceived I x u0 P0 j +
              gamma * residualReceived I x u1 P1 j) ∧
      (∀ gamma ∈ Gamma,
        ContactTranslation.specialization K (residual gamma) gamma
          (globalResidualHom P0 P1 (Lagrange.nodal I x) F) = 0) ∧
      ∀ gamma ∈ Gamma,
        MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
          (ContactPolynomialSolutions.polynomialPoint
            (phi.comp Polynomial.C) (residual gamma) gamma
              (phi Polynomial.X))
          (MvPolynomial.pderiv (2 : Fin 4)
            (globalResidualHom P0 P1 (Lagrange.nodal I x) F)) ≠ 0 := by
  obtain ⟨P0, P1, residual, hP0, hP1, hresdeg, hnores, hnormal,
      hagree⟩ := exists_residual_family_with_incidence_data
    I nodes x u0 u1 w e hsub hIw hinj selected Gamma
      hdegree hvalues hno
  have hV : Lagrange.nodal I x ≠ 0 :=
    (Lagrange.nodal_monic (s := I) (v := x)).ne_zero
  have hVeval : (Lagrange.nodal I x).eval₂
      (phi.comp Polynomial.C) (phi Polynomial.X) ≠ 0 := by
    rw [polynomial_eval₂_comp_C_X]
    exact (map_ne_zero_iff phi hphi).mpr hV
  refine ⟨P0, P1, residual, hP0, hP1, hresdeg, hnores, hnormal,
    ?_, ?_, ?_⟩
  · intro gamma hgamma j hj hagreement
    apply hagree gamma hgamma j
    · simpa only [Finset.mem_sdiff] using hj
    · exact hagreement
  · intro gamma hgamma
    apply globalResidual_solution
    rw [← hnormal gamma hgamma]
    exact hsolution gamma hgamma
  · intro gamma hgamma
    apply globalResidual_regular_at_polynomialPoint
      (phi.comp Polynomial.C) P0 P1 (Lagrange.nodal I x)
        (residual gamma) gamma (phi Polynomial.X) F hVeval
    rw [← hnormal gamma hgamma]
    exact hregular gamma hgamma

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualSurface
