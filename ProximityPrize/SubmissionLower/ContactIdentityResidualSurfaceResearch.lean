import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagAffineResidualAutomorphismResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualFamilyResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalTransformResearch

/-! .












 -/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualSurfaceResearch

open scoped Classical
open ContactFlagAffineResidualAutomorphismResearch
open ContactIdentityResidualGlobalTransformResearch
open ContactIdentityResidualFamilyResearch
open ContactIdentityResidualPencilResearch
open ContactPrimeSeedIncidence
open ContactFlagTriangularProjectionResearch
open TrivariateShearResearch

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K Omega : Type} [Field K] [Field Omega]

local instance : DecidableEq Omega := Classical.decEq Omega

abbrev Poly3 (Omega : Type) [Field Omega] := MvPolynomial (Fin 3) Omega
abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

/-! . -/

/-- .
 -/
theorem originalAlgHom_eq_residualAlgHom_inverse
    (aY v bY aS bS cS : Omega) :
    originalAlgHom aY v bY aS bS cS =
      residualAlgHom (-v⁻¹ * aY) v⁻¹ (-v⁻¹ * bY)
        (-v⁻¹ * aS + v⁻¹ * v⁻¹ * bS * aY)
        (-v⁻¹ * v⁻¹ * bS)
        (v⁻¹ * v⁻¹ * bS * bY - v⁻¹ * cS) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [originalAlgHom, originalImage, residualAlgHom, residualImage] <;>
    ring

/-- .
 -/
theorem residual_degreeOf_one_le
    (aY v bY aS bS cS : Omega) (F : Poly3 Omega) :
    (residualAlgHom aY v bY aS bS cS F).degreeOf 1 ≤ F.degreeOf 1 := by
  have h := residualAlgHom_wt_le_pulled
    (Pi.single (1 : Fin 3) 1) aY v bY aS bS cS F
  have hp : flagPullWeights (Pi.single (1 : Fin 3) 1) =
      Pi.single (1 : Fin 3) 1 := by
    funext i
    fin_cases i <;> simp [flagPullWeights]
  rw [hp] at h
  simpa [wt] using h

/-- . -/
theorem original_degreeOf_one_le
    (aY v bY aS bS cS : Omega) (F : Poly3 Omega) :
    (originalAlgHom aY v bY aS bS cS F).degreeOf 1 ≤ F.degreeOf 1 := by
  rw [originalAlgHom_eq_residualAlgHom_inverse]
  exact residual_degreeOf_one_le _ _ _ _ _ _ F

/-- .

 -/
theorem residual_degreeOf_one_eq
    (aY v bY aS bS cS : Omega) (hv : v ≠ 0) (F : Poly3 Omega) :
    (residualAlgHom aY v bY aS bS cS F).degreeOf 1 = F.degreeOf 1 := by
  apply Nat.le_antisymm
  · exact residual_degreeOf_one_le _ _ _ _ _ _ F
  · have h := original_degreeOf_one_le aY v bY aS bS cS
      (residualAlgHom aY v bY aS bS cS F)
    have hback :
        originalAlgHom aY v bY aS bS cS
            (residualAlgHom aY v bY aS bS cS F) = F := by
      have hc := DFunLike.congr_fun
        (original_comp_residual aY v bY aS bS cS hv) F
      simpa [AlgHom.comp_apply] using hc
    simpa only [hback] using h

theorem residual_degreeOf_one_pos_iff
    (aY v bY aS bS cS : Omega) (hv : v ≠ 0) (F : Poly3 Omega) :
    0 < (residualAlgHom aY v bY aS bS cS F).degreeOf 1 ↔
      0 < F.degreeOf 1 := by
  rw [residual_degreeOf_one_eq aY v bY aS bS cS hv F]

/-! . -/

/-- .
 -/
theorem componentResidualHom_eq_residualAlgHom
    (aY v bY aS bS cS : Omega) :
    componentResidualHom aY v bY aS bS cS =
      residualAlgHom aY v bY aS bS cS := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [componentResidualHom, componentResidualImage,
      residualAlgHom, residualImage]

/-- .
 -/
theorem surfaceMap_globalResidualHom_eq_residualAlgHom
    (phi : Polynomial K →+* Omega) (P0 P1 V : Polynomial K) (F : Poly4 K) :
    ContactGenericSurface.surfaceMap phi
        (globalResidualHom P0 P1 V F) =
      residualAlgHom (phi P0) (phi V) (phi P1)
        (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
        (ContactGenericSurface.surfaceMap phi F) := by
  rw [surfaceMap_globalResidualHom]
  rw [componentResidualHom_eq_residualAlgHom]

/-- .
 -/
theorem surfaceMap_globalResidualHom_degreeOf_one
    (phi : Polynomial K →+* Omega) (hphi : Function.Injective phi)
    (P0 P1 V : Polynomial K) (hV : V ≠ 0) (F : Poly4 K) :
    (ContactGenericSurface.surfaceMap phi
      (globalResidualHom P0 P1 V F)).degreeOf 1 =
        (ContactGenericSurface.surfaceMap phi F).degreeOf 1 := by
  rw [surfaceMap_globalResidualHom_eq_residualAlgHom]
  exact residual_degreeOf_one_eq _ _ _ _ _ _
    ((map_ne_zero_iff phi hphi).mpr hV) _

/-- .
 -/
theorem surfaceMap_globalResidualHom_irreducible_iff
    (phi : Polynomial K →+* Omega) (hphi : Function.Injective phi)
    (P0 P1 V : Polynomial K) (hV : V ≠ 0) (F : Poly4 K) :
    Irreducible (ContactGenericSurface.surfaceMap phi
      (globalResidualHom P0 P1 V F)) ↔
      Irreducible (ContactGenericSurface.surfaceMap phi F) := by
  rw [surfaceMap_globalResidualHom_eq_residualAlgHom]
  exact residual_irreducible_iff _ _ _ _ _ _
    ((map_ne_zero_iff phi hphi).mpr hV) _

/-- .
 -/
theorem surfaceMap_globalResidualHom_dvd_iff
    (phi : Polynomial K →+* Omega) (hphi : Function.Injective phi)
    (P0 P1 V : Polynomial K) (hV : V ≠ 0) (F G : Poly4 K) :
    ContactGenericSurface.surfaceMap phi (globalResidualHom P0 P1 V F) ∣
        ContactGenericSurface.surfaceMap phi (globalResidualHom P0 P1 V G) ↔
      ContactGenericSurface.surfaceMap phi F ∣
        ContactGenericSurface.surfaceMap phi G := by
  rw [surfaceMap_globalResidualHom_eq_residualAlgHom,
    surfaceMap_globalResidualHom_eq_residualAlgHom]
  exact residual_dvd_iff _ _ _ _ _ _
    ((map_ne_zero_iff phi hphi).mpr hV) _ _

/-- .
 -/
theorem surfaceMap_globalResidualHom_polynomialInFlag
    (phi : Polynomial K →+* Omega) (P0 P1 V : Polynomial K)
    (F : Poly4 K) (p : ContactFlagBezout6543Research.FlagDegree)
    (hflag : PolynomialInFlag p (ContactGenericSurface.surfaceMap phi F)) :
    PolynomialInFlag p (ContactGenericSurface.surfaceMap phi
      (globalResidualHom P0 P1 V F)) := by
  rw [surfaceMap_globalResidualHom_eq_residualAlgHom]
  exact polynomialInFlag_residualAlgHom p _ _ _ _ _ _ _ hflag

/-! . -/

/-- .
 -/
theorem pderiv_globalResidualHom
    (P0 P1 V : Polynomial K) (F : Poly4 K) :
    MvPolynomial.pderiv (2 : Fin 4) (globalResidualHom P0 P1 V F) =
      embedX K V * globalResidualHom P0 P1 V
        (MvPolynomial.pderiv (2 : Fin 4) F) :=
  pderiv_globalResidualHom_R P0 P1 V F

/-- .
 -/
theorem specialization_pderiv_globalResidualHom
    (P0 P1 V C : Polynomial K) (gamma : K) (F : Poly4 K) :
    ContactTranslation.specialization K C gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (globalResidualHom P0 P1 V F)) =
      V * ContactTranslation.specialization K
        (P0 + Polynomial.C gamma * P1 + V * C) gamma
          (MvPolynomial.pderiv (2 : Fin 4) F) := by
  rw [pderiv_globalResidualHom, map_mul, specialization_embedX,
    specialization_globalResidualHom]

theorem residual_specialization_regular
    (P0 P1 V C : Polynomial K) (gamma : K) (F : Poly4 K)
    (hV : V ≠ 0)
    (hregular : ContactTranslation.specialization K
      (P0 + Polynomial.C gamma * P1 + V * C) gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    ContactTranslation.specialization K C gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (globalResidualHom P0 P1 V F)) ≠ 0 := by
  rw [specialization_pderiv_globalResidualHom]
  exact mul_ne_zero hV hregular

/-- .
 -/
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

/-- .
 -/
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

/-- . -/
theorem residual_dvd_pderiv_globalResidualHom_iff
    (phi : Polynomial K →+* Omega) (hphi : Function.Injective phi)
    (P0 P1 V : Polynomial K) (hV : V ≠ 0)
    (G : Poly3 Omega) (F : Poly4 K) :
    residualAlgHom (phi P0) (phi V) (phi P1)
        (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G ∣
      ContactGenericSurface.surfaceMap phi
        (MvPolynomial.pderiv (2 : Fin 4)
          (globalResidualHom P0 P1 V F)) ↔
      G ∣ ContactGenericSurface.surfaceMap phi
        (MvPolynomial.pderiv (2 : Fin 4) F) := by
  rw [surfaceMap_pderiv_globalResidualHom]
  have hv : phi V ≠ 0 := (map_ne_zero_iff phi hphi).mpr hV
  have hu : IsUnit (MvPolynomial.C (phi V) : Poly3 Omega) :=
    (isUnit_iff_ne_zero.mpr hv).map MvPolynomial.C
  rw [hu.dvd_mul_left]
  exact residual_dvd_iff _ _ _ _ _ _ hv _ _

/-- .
 -/
theorem residual_component_transport
    (phi : Polynomial K →+* Omega) (hphi : Function.Injective phi)
    (P0 P1 V : Polynomial K) (hV : V ≠ 0)
    (F : Poly4 K) (G : Poly3 Omega)
    (hG : Irreducible G)
    (hdiv : G ∣ ContactGenericSurface.surfaceMap phi F)
    (hr : 0 < G.degreeOf 1)
    (hproper : ¬ G ∣ ContactGenericSurface.surfaceMap phi
      (MvPolynomial.pderiv (2 : Fin 4) F))
    (p : ContactFlagBezout6543Research.FlagDegree)
    (hflag : PolynomialInFlag p G) :
    let Gres := residualAlgHom (phi P0) (phi V) (phi P1)
      (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G
    Irreducible Gres ∧
      Gres ∣ ContactGenericSurface.surfaceMap phi
        (globalResidualHom P0 P1 V F) ∧
      0 < Gres.degreeOf 1 ∧
      ¬ Gres ∣ ContactGenericSurface.surfaceMap phi
        (MvPolynomial.pderiv (2 : Fin 4)
          (globalResidualHom P0 P1 V F)) ∧
      PolynomialInFlag p Gres := by
  dsimp only
  have hv : phi V ≠ 0 := (map_ne_zero_iff phi hphi).mpr hV
  refine ⟨(residual_irreducible_iff _ _ _ _ _ _ hv G).mpr hG,
    (residual_dvd_surfaceMap_globalResidualHom_iff
      phi hphi P0 P1 V hV G F).mpr hdiv, ?_, ?_, ?_⟩
  · exact (residual_degreeOf_one_pos_iff _ _ _ _ _ _ hv G).mpr hr
  · exact (residual_dvd_pderiv_globalResidualHom_iff
      phi hphi P0 P1 V hV G F).not.mpr hproper
  · exact polynomialInFlag_residualAlgHom p G _ _ _ _ _ _ hflag

/-! . -/

/-- .
 -/
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

/-- .


 -/
theorem eval_residualComponent_selectedPoint
    (phi : Polynomial K →+* Omega)
    (P0 P1 V C S : Polynomial K) (gamma : K) (G : Poly3 Omega)
    (hnormal : S = P0 + Polynomial.C gamma * P1 + V * C) :
    MvPolynomial.eval (selectedPoint phi (fun _ ↦ C) gamma)
        (residualAlgHom (phi P0) (phi V) (phi P1)
          (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G) =
      MvPolynomial.eval (selectedPoint phi (fun _ ↦ S) gamma) G := by
  have hCpoint : selectedPoint phi (fun _ ↦ C) gamma =
      ![phi C, phi C.derivative, (phi.comp Polynomial.C) gamma] := by
    funext i
    fin_cases i <;>
      simp [selectedPoint, ContactPolynomialSolutions.polynomialPoint,
        RingHom.comp_apply]
  have hSpoint : selectedPoint phi (fun _ ↦ S) gamma =
      ![phi S, phi S.derivative, (phi.comp Polynomial.C) gamma] := by
    funext i
    fin_cases i <;>
      simp [selectedPoint, ContactPolynomialSolutions.polynomialPoint,
        RingHom.comp_apply]
  rw [hCpoint, hSpoint]
  change MvPolynomial.eval₂Hom (algebraMap Omega Omega)
      ![phi C, phi C.derivative, (phi.comp Polynomial.C) gamma]
        (residualAlgHom (phi P0) (phi V) (phi P1)
          (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G) =
    MvPolynomial.eval₂Hom (algebraMap Omega Omega)
      ![phi S, phi S.derivative, (phi.comp Polynomial.C) gamma] G
  rw [eval₂Hom_residual]
  have hcoords :
      ![phi P0 + phi V * phi C + phi P1 * (phi.comp Polynomial.C) gamma,
        phi P0.derivative + phi V * phi C.derivative +
          phi V.derivative * phi C +
            phi P1.derivative * (phi.comp Polynomial.C) gamma,
        (phi.comp Polynomial.C) gamma] =
      ![phi S, phi S.derivative, (phi.comp Polynomial.C) gamma] := by
    funext i
    fin_cases i <;>
      simp [hnormal, RingHom.comp_apply] <;> ring
  simpa using congrArg
    (fun q : Fin 3 → Omega ↦
      MvPolynomial.eval₂Hom (algebraMap Omega Omega) q G) hcoords

/-- .


 -/
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

end ProximityPrize.SubmissionLower.ContactIdentityResidualSurfaceResearch
