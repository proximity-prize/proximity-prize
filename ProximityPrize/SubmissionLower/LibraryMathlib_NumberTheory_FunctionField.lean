import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LibraryMathlib_FieldTheory_RatFunc_Valuation
import ProximityPrize.SubmissionLower.LibraryMathlib_FieldTheory_RatFunc_Degree
import ProximityPrize.SubmissionLower.LibraryMathlib_FieldTheory_RatFunc_IntermediateField
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Adjoin_Polynomial_Bivariate
set_option Elab.async false
/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/











/-!
# Function fields

This file defines a function field and the ring of integers corresponding to it.

## Main definitions

- `FunctionField F K` states that `K` is a function field over the field `F`,
  i.e. it is a finite extension of the field of rational functions in one variable over `F`.
- `FunctionField.ringOfIntegers` defines the ring of integers corresponding to a function field
  as the integral closure of `(Polynomial F)` in the function field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. We also omit assumptions like
`IsScalarTower (Polynomial F) (FractionRing (Polynomial F)) K` in definitions,
adding them back in lemmas when they are needed.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]
* [M. Rosen, *Number Theory in Function Fields*][rosen2002]

## Tags
function field, ring of integers
-/

section


noncomputable section

open scoped nonZeroDivisors Polynomial WithZero RatFunc

variable (F K : Type*) [Field F] [Field K]

/-- `K` is a function field over the field `F` if it is a finite
extension of the field of rational functions in one variable over `F`.

Note that `K` can be a function field over multiple, non-isomorphic, `F`.
-/
abbrev FunctionField [Algebra F⟮X⟯ K] : Prop :=
  FiniteDimensional F⟮X⟯ K

/-- `K` is a function field over `F` iff it is a finite extension of `F(t)`. -/
theorem functionField_iff (Ft : Type*) [Field Ft] [Algebra (Polynomial F) Ft]
    [IsFractionRing (Polynomial F) Ft] [Algebra F⟮X⟯ K] [Algebra Ft K] [Algebra (Polynomial F) K]
    [IsScalarTower (Polynomial F) Ft K] [IsScalarTower (Polynomial F) F⟮X⟯ K] :
    FunctionField F K ↔ FiniteDimensional Ft K := by
  let e := IsLocalization.algEquiv (Polynomial F)⁰ F⟮X⟯ Ft
  have : ∀ (c) (x : K), e c • x = c • x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def]
    congr
    refine congr_fun (f := fun c => algebraMap Ft K (e c)) ?_ c
    refine IsLocalization.ext (nonZeroDivisors (Polynomial F)) _ _ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
      simp only [map_one, map_mul, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  constructor <;> intro h
  · let b := Module.finBasis F⟮X⟯ K
    exact (b.mapCoeffs e this).finiteDimensional_of_finite
  · let b := Module.finBasis Ft K
    refine (b.mapCoeffs e.symm ?_).finiteDimensional_of_finite
    intro c x; convert (this (e.symm c) x).symm; simp only [e.apply_symm_apply]

namespace FunctionField

theorem algebraMap_injective [Algebra (Polynomial F) K] [Algebra F⟮X⟯ K]
    [IsScalarTower (Polynomial F) F⟮X⟯ K] : Function.Injective (algebraMap (Polynomial F) K) := by
  rw [IsScalarTower.algebraMap_eq (Polynomial F) F⟮X⟯ K]
  exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective (Polynomial F) F⟮X⟯)

/-- The function field analogue of `NumberField.ringOfIntegers`:
`FunctionField.ringOfIntegers F K` is the integral closure of `(Polynomial F)` in `K`.

We don't actually assume `K` is a function field over `F` in the definition,
only when proving its properties.
-/
def ringOfIntegers [Algebra (Polynomial F) K] :=
  integralClosure (Polynomial F) K

namespace ringOfIntegers

variable [Algebra (Polynomial F) K]

instance : IsDomain (ringOfIntegers F K) :=
  (ringOfIntegers F K).isDomain

instance : IsIntegralClosure (ringOfIntegers F K) (Polynomial F) K :=
  integralClosure.isIntegralClosure _ _

variable [Algebra F⟮X⟯ K] [IsScalarTower (Polynomial F) F⟮X⟯ K]

theorem algebraMap_injective : Function.Injective (algebraMap (Polynomial F) (ringOfIntegers F K)) := by
  have hinj : Function.Injective (algebraMap (Polynomial F) K) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial F) F⟮X⟯ K]
    exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective (Polynomial F) F⟮X⟯)
  rw [injective_iff_map_eq_zero (algebraMap (Polynomial F) (↥(ringOfIntegers F K)))]
  intro p hp
  rw [← Subtype.coe_inj, Subalgebra.coe_zero] at hp
  rw [injective_iff_map_eq_zero (algebraMap (Polynomial F) K)] at hinj
  exact hinj p hp

theorem not_isField : ¬IsField (ringOfIntegers F K) := by
  simpa [← (IsIntegralClosure.isIntegral_algebra (Polynomial F) K).isField_iff_isField
      (algebraMap_injective F K)] using
    Polynomial.not_isField F

variable [FunctionField F K]

instance : IsFractionRing (ringOfIntegers F K) K :=
  integralClosure.isFractionRing_of_finite_extension F⟮X⟯ K

instance : IsIntegrallyClosed (ringOfIntegers F K) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension F⟮X⟯

instance [Algebra.IsSeparable F⟮X⟯ K] : IsNoetherian (Polynomial F) (ringOfIntegers F K) :=
  IsIntegralClosure.isNoetherian _ F⟮X⟯ K _

instance [Algebra.IsSeparable F⟮X⟯ K] : IsDedekindDomain (ringOfIntegers F K) :=
  IsIntegralClosure.isDedekindDomain (Polynomial F) F⟮X⟯ K _

end ringOfIntegers

section AdjoinTranscendental

open IntermediateField RatFunc

variable {F K : Type*} [Field F] [Field K] [Algebra F⟮X⟯ K] [FunctionField F K]

instance FiniteDimensional.adjoin_X : FiniteDimensional F⟮(«X» : F⟮X⟯)⟯ K :=
  have : Module.Finite (⊤ : IntermediateField F F⟮X⟯) F⟮X⟯ :=
    .top_left F⟮X⟯ F⟮X⟯
  RatFunc.adjoin_X (K := F) ▸ Module.Finite.trans F⟮X⟯ _

variable [Algebra F K] [IsScalarTower F F⟮X⟯ K]

theorem FiniteDimensional.adjoin_algebraMap_X :
    FiniteDimensional F⟮algebraMap _ K («X» : F⟮X⟯)⟯ K :=
  .of_restrictScalars_finite F⟮(«X» : F⟮X⟯)⟯ _ _

theorem Algebra.IsAlgebraic.adjoin_algebraMap_X :
    Algebra.IsAlgebraic F⟮algebraMap _ K («X» : F⟮X⟯)⟯ K := by
  exact .tower_top (K := F⟮(«X» : F⟮X⟯)⟯) _

variable {y : K}

theorem isAlgebraic_X_over_adjoin_transcendental (hy : Transcendental F y) :
    IsAlgebraic F⟮y⟯ (algebraMap _ K («X» : F⟮X⟯)) :=
  isAlgebraic_adjoin_iff.mpr (.adjoin_singleton transcendental_X hy
    (isAlgebraic_adjoin_iff.mp (Algebra.IsAlgebraic.isAlgebraic y)))

lemma finiteDimensional_of_adjoin_transcendental (hy : Transcendental F y) :
    FiniteDimensional F⟮y⟯ K :=
  -- Local definitions for convenience
  let x := algebraMap _ K («X» : F⟮X⟯)
  let Fyx := restrictScalars F F⟮y⟯⟮x⟯
  let Fxy := restrictScalars F F⟮x⟯⟮y⟯
  have : FiniteDimensional F⟮y⟯ Fyx :=
    adjoin.finiteDimensional
      (isAlgebraic_iff_isIntegral.mp (isAlgebraic_X_over_adjoin_transcendental hy))
  have : FiniteDimensional Fyx K := by
    have := FiniteDimensional.adjoin_algebraMap_X (F := F) (K := K)
    unfold Fyx
    rw [adjoin_simple_comm]
    exact .right F⟮x⟯ Fxy K
  .trans F⟮y⟯ Fyx K

end AdjoinTranscendental

section constantExtension

open RatFunc

variable {F}
variable [Algebra (Polynomial F) K] [FaithfulSMul (Polynomial F) K] [FunctionField F K]

attribute [local instance] Polynomial.algebra

section Unbundled

open Polynomial

variable {E : Type*} [Field E] [Algebra F E] [Algebra (Polynomial E) K] [FaithfulSMul (Polynomial E) K]

theorem finiteDimensional_ratFunc_of_constantExtension [IsScalarTower (Polynomial F) (Polynomial E) K] :
    FiniteDimensional F⟮X⟯ E⟮X⟯ :=
  .equiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F⟮X⟯ E⟮X⟯ K)).toLinearEquiv.symm

/-- Let `K` be a function field over `F`. If `E` is an algebraic extension of `F` which is
contained in `K` then it is finite over `F`. -/
theorem finiteDimensional_of_constantExtension [IsScalarTower (Polynomial F) (Polynomial E) K]
    [Algebra.IsAlgebraic F E] : FiniteDimensional F E :=
  have := finiteDimensional_ratFunc_of_constantExtension (F := F) (E := E) K
  Module.finite_of_finrank_pos ((finrank_ratFunc_ratFunc F E) ▸ Module.finrank_pos)

end Unbundled

section IntermediateField

variable [Algebra F K] (E : IntermediateField F K) [Algebra (Polynomial E) K] [FaithfulSMul (Polynomial E) K]
  [IsScalarTower (Polynomial F) (Polynomial E) K]

instance : FiniteDimensional F⟮X⟯ E⟮X⟯ :=
  finiteDimensional_ratFunc_of_constantExtension K

/-- Let `K` be a function field over `F`. If `E` is an algebraic extension of `F` which is
contained in `K` then it is finite over `F`. -/
instance [Algebra.IsAlgebraic F E] : FiniteDimensional F E :=
  finiteDimensional_of_constantExtension K

end IntermediateField

end constantExtension

end FunctionField
