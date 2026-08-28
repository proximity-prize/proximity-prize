import ProximityPrize.SubmissionLower.BCHKSLocatorCramerRankTwoAssembly6400

/-!
# Transport between coordinate and polynomial-pair locator kernels

The rational polynomial-pair kernel is the original coordinate kernel
transported through the coefficient equivalence.  This module records that
linear equivalence and maps an integral polynomial kernel vector into it.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRationalPairKernelTransport6400

open Polynomial
open ProximityPrize.Benchmark
open scoped Matrix

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- A linear equivalence identifies a submodule with the inverse-image
submodule on its source.  Packaging this once keeps concrete large-index
applications from elaborating subtype membership proofs inline. -/
noncomputable def submoduleToComapEquiv
    {K E W : Type} [Field K] [AddCommGroup E] [AddCommGroup W]
    [Module K E] [Module K W]
    (e : E ≃ₗ[K] W) (U : Submodule K W) :
    U ≃ₗ[K] U.comap e.toLinearMap where
  toFun x := ⟨e.symm x.1, by
    change e (e.symm x.1) ∈ U
    simpa only [e.apply_symm_apply] using x.2⟩
  invFun x := ⟨e x.1, x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact e.apply_symm_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  map_add' x y := by
    apply Subtype.ext
    exact e.symm.map_add x.1 y.1
  map_smul' a x := by
    apply Subtype.ext
    exact e.symm.map_smul a x.1

@[simp] theorem submoduleToComapEquiv_apply_coe
    {K E W : Type} [Field K] [AddCommGroup E] [AddCommGroup W]
    [Module K E] [Module K W]
    (e : E ≃ₗ[K] W) (U : Submodule K W) (x : U) :
    ((submoduleToComapEquiv e U x : U.comap e.toLinearMap) : E) =
      e.symm x.1 := rfl

/-- Ring homomorphisms carry square-matrix kernel vectors into the mapped
matrix kernel.  Keeping this proof generic prevents elaboration from
expanding the production `76781`-coordinate type. -/
theorem ringHom_comp_mem_ker_map_mulVec
    {R S I : Type} [CommRing R] [CommRing S] [Fintype I]
    (f : R →+* S) (M : Matrix I I R) (q : I → R)
    (hq : q ∈ LinearMap.ker M.mulVecLin) :
    (f ∘ q) ∈ LinearMap.ker (M.map f).mulVecLin := by
  classical
  rw [LinearMap.mem_ker] at hq ⊢
  change (M.map f) *ᵥ (f ∘ q) = 0
  funext i
  rw [← RingHom.map_mulVec]
  have hi := congrFun hq i
  simpa using congrArg f hi

theorem score6400LocatorRationalPairKernel_finrank_eq
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) :
    Module.finrank (FractionRing IRSProfile.Field[X])
        (score6400LocatorRationalPairKernel f₀ f₁) =
      Module.finrank (FractionRing IRSProfile.Field[X])
        (LinearMap.ker
          ((score6400LocatorPolynomialMatrix f₀ f₁).map
            (algebraMap IRSProfile.Field[X]
              (FractionRing IRSProfile.Field[X]))).mulVecLin) := by
  let K := FractionRing IRSProfile.Field[X]
  let e := polynomialPairCoordinateEquiv K
    locatorOrdinaryRows6400 locatorFrobeniusRows6400
  let W := LinearMap.ker
    ((score6400LocatorPolynomialMatrix f₀ f₁).map
      (algebraMap IRSProfile.Field[X] K)).mulVecLin
  have hmap :
      (W.comap e.toLinearMap).map e.toLinearMap = W :=
    Submodule.map_comap_eq_of_surjective e.surjective W
  have hfin := e.finrank_map_eq (W.comap e.toLinearMap)
  rw [hmap] at hfin
  change Module.finrank K (W.comap e.toLinearMap) = Module.finrank K W
  exact hfin.symm

end BCHKSRationalPairKernelTransport6400
end ProximityPrize.SubmissionLower
