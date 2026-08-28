import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.GlobalShearFamilyDegreeResearch
import ProximityPrize.SubmissionLower.ContactGlobalShearComponentSplitResearch
import ProximityPrize.SubmissionLower.ContactGlobalShearFiberResearch
import ProximityPrize.SubmissionLower.ContactGlobalShearPositivityResearch
import ProximityPrize.SubmissionLower.ContactAdaptiveShearConditional

/-!
# Characteristic-free proper-cut estimate from one global shear

This module instantiates the common-shear family-degree theorem on the actual
regular minimal-prime cover.  The S-degree assignment ranges over every
component where `S = R + a Z` is transcendental.  Components with
transcendental Z use the common finite-separable shear and the affine box
count; components with algebraic Z have at most one selected seed and are
paid by positivity of the same global-shear cost.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalShearProperCutResearch

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveZeroCount
open ArbitraryRationalProjectionResearch
open ContactAdaptiveShearConditional ContactGlobalShearComponentSplitResearch
open ContactGlobalShearFiberResearch ContactGlobalShearPositivityResearch
open ContactRegularComponentCover ContactPrimeSeedIncidence
open ContactPolynomialSolutions ContactTranslation
open ContactGenericSurface ContactProperCutSeedCount ActualCoordinateDegreeSum
open GlobalShearFamilyDegreeResearch GlobalShearZeroCountResearch
open CharacteristicFreeInseparableDichotomyResearch

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable {K Omega : Type} [Field K] [Field Omega]
variable (phi : Polynomial K →+* Omega) [IsAlgClosed Omega]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega

variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

/-- The complete global-shear proper-cut estimate.  Only the unchanged Y/Z
family budgets must lie below the characteristic; no R gate remains. -/
theorem proper_cut_seed_bound_global_shear_charfree
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap phi F) (hproper : ¬ G ∣ T)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset ι) (x u0 u1 : ι → K) (hinj : Set.InjOn x nodes)
    (p w agreementCount e : ℕ) [CharP Omega p] (hp : p ≠ 0)
    (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < agreementCount) (han : agreementCount ≤ nodes.card)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
        (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
          (phi Polynomial.X))
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) G = 0)
    (hTpoint : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) T = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      agreementCount ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w e)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial phi F w (x i) (u0 i) (u1 i)).degreeOf j ≤ cap j)
    (hcapY : 1 ≤ cap 0) (hcapS : 1 ≤ cap 1)
    (hYchar : coordinateMixedDegree Omega G T 0 < p)
    (hZchar : coordinateMixedDegree Omega G T 2 < p) :
    Gamma.card * (agreementCount - w) ≤
      (nodes.card - w) * (∑ i,
        adaptiveShearCap cap i * coordinateMixedDegree Omega G T i) +
        (e + 1) * (agreementCount - w) *
          coordinateMixedDegree Omega G T 2 := by
  classical
  let H := regularitySurface phi F
  have hgeom := regularComponents_finite_and_degree_budget_charfree
    phi F G T hG hproper
  have hfinite : ∀ C : RegularComponent Omega G T H,
      ProjectionsFinite Omega C.1 := by
    simpa only [H] using hgeom.1
  have hbudget : ∀ i, (∑ C : RegularComponent Omega G T H,
      actualCoordinateDegree Omega C.1 i) ≤ coordinateMixedDegree Omega G T i := by
    simpa only [H] using hgeom.2
  obtain ⟨shearA, hshearA, hcommon⟩ :=
    exists_common_regularComponent_finite_separable_shear
      Omega G T H p hp hfinite (coordinateMixedDegree Omega G T 2)
        (hbudget 2) hZchar
  let s : Set (RegularComponent Omega G T H) :=
    {C | Transcendental Omega (shearedFieldCoordinate Omega C.1 shearA)}
  let Q : s → Ideal (MvPolynomial (Fin 3) Omega) := fun C ↦ C.1.1
  letI : ∀ C : s, (Q C).IsPrime := fun C ↦
    regularComponent_isPrime Omega G T H C.1
  have hinjQ : Function.Injective Q := by
    intro C D hCD
    apply Subtype.ext
    apply Subtype.ext
    exact hCD
  have hfamily := finite_sum_shear_finrank Omega Q hinjQ shearA
    (fun C ↦ C.2) G T hG
    (fun C ↦ regularComponent_G_mem Omega G T H C.1)
    (fun C ↦ regularComponent_T_mem Omega G T H C.1) hproper
  let D : s → ℕ := fun C ↦
    letI : Algebra (RatFunc Omega) (CoordinateField Omega (Q C)) :=
      (elementEmbedding Omega (CoordinateField Omega (Q C))
        (shearedFieldCoordinate Omega (Q C) shearA) C.2).toRingHom.toAlgebra
    Module.finrank (RatFunc Omega) (CoordinateField Omega (Q C))
  let dS : RegularComponent Omega G T H → ℕ := fun C ↦
    if hSC : Transcendental Omega
        (shearedFieldCoordinate Omega C.1 shearA) then
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (shearedFieldCoordinate Omega C.1 shearA) hSC).toRingHom.toAlgebra
      Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)
    else 0
  have hSbudget : (∑ C : RegularComponent Omega G T H, dS C) ≤
      coordinateMixedDegree Omega G T 1 + coordinateMixedDegree Omega G T 2 := by
    calc
      (∑ C : RegularComponent Omega G T H, dS C) = ∑ C : s, D C := by
        apply Finset.sum_congr_set s dS D
        · intro C hC
          exact dif_pos hC
        · intro C hC
          change ¬ Transcendental Omega
            (shearedFieldCoordinate Omega C.1 shearA) at hC
          exact dif_neg hC
      _ ≤ coordinateMixedDegree Omega G T 1 +
          coordinateMixedDegree Omega G T 2 := hfamily.2
  have hSdegree : ∀ (C : RegularComponent Omega G T H),
      Transcendental Omega (shearedFieldCoordinate Omega C.1 shearA) →
        1 ≤ dS C := by
    intro C hSC
    rw [show dS C = D ⟨C, hSC⟩ by exact dif_pos hSC]
    letI : Algebra (RatFunc Omega) (CoordinateField Omega (Q ⟨C, hSC⟩)) :=
      (elementEmbedding Omega (CoordinateField Omega (Q ⟨C, hSC⟩))
        (shearedFieldCoordinate Omega (Q ⟨C, hSC⟩) shearA)
        hSC).toRingHom.toAlgebra
    letI : FiniteDimensional (RatFunc Omega)
        (CoordinateField Omega (Q ⟨C, hSC⟩)) := hfamily.1 ⟨C, hSC⟩
    exact Module.finrank_pos
  have hfiber : ∀ C : RegularComponent Omega G T H,
      GlobalShearFiberCertificate phi C.1 F selected
        (componentSeeds Omega G T H Gamma (selectedPoint phi selected) C)
        w (dS C) cap := by
    intro C
    by_cases hZ : Transcendental Omega (coordinate Omega C.1 2)
    · obtain ⟨hSC, hfiniteS, hsepS⟩ := hcommon ⟨C, hZ⟩
      apply regularComponent_globalShearFiberCertificate
        phi G T H C p hp hfinite
        (coordinateMixedDegree Omega G T 0)
        (coordinateMixedDegree Omega G T 2)
        (hbudget 0) (hbudget 2) hYchar hZchar
        shearA hSC hfiniteS hsepS F selected
        (componentSeeds Omega G T H Gamma (selectedPoint phi selected) C)
        w (dS C) hchar
      · intro gamma hgamma
        exact hdegree gamma (componentSeeds_subset Omega G T H Gamma
          (selectedPoint phi selected) C hgamma)
      · intro gamma hgamma
        exact hsolution gamma (componentSeeds_subset Omega G T H Gamma
          (selectedPoint phi selected) C hgamma)
      · intro gamma hgamma
        exact hregular gamma (componentSeeds_subset Omega G T H Gamma
          (selectedPoint phi selected) C hgamma)
      · intro gamma hgamma
        exact componentSeeds_on_prime Omega G T H Gamma
          (selectedPoint phi selected) C gamma hgamma
      · exact dif_pos hSC
    · have hZalg : IsAlgebraic Omega (coordinate Omega C.1 2) :=
        not_not.mp hZ
      apply globalShearFiberCertificate_of_seedCoordinate_isAlgebraic
        phi C.1 F selected
        (componentSeeds Omega G T H Gamma (selectedPoint phi selected) C)
        w (dS C) cap
      · intro gamma hgamma
        exact componentSeeds_on_prime Omega G T H Gamma
          (selectedPoint phi selected) C gamma hgamma
      · exact hZalg
      · exact globalShearCost_pos_of_seedCoordinate_isAlgebraic
          Omega C.1 (hfinite C)
          (regularComponent_ne_point Omega G T H C) hZalg
          shearA (dS C) cap (hSdegree C) hcapY hcapS
  exact proper_cut_seed_bound_of_global_shear_sum
    phi F G T hG hdiv hproper selected Gamma nodes x u0 u1 hinj
    p w agreementCount e hw hchar hwa han hdegree hsolution hregular
    hGpoint hTpoint hagreement hnoPencil cap
    (coordinateMixedDegree Omega G T) hcap hfinite hbudget dS hSbudget hfiber

end

end ProximityPrize.SubmissionLower.ContactGlobalShearProperCutResearch

#print axioms ProximityPrize.SubmissionLower.ContactGlobalShearProperCutResearch.proper_cut_seed_bound_global_shear_charfree
