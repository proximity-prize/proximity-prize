import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Homology_DerivedCategory_Basic
import ProximityPrize.SubmissionLower.LibraryMathlib_CategoryTheory_Shift_Linear
set_option Elab.async false
/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/





/-!
# The derived category of a linear abelian category is linear
-/

section

open CategoryTheory

universe t w v u

variable (R : Type t) [Ring R] (C : Type u) [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{w} C]

namespace DerivedCategory

noncomputable instance : Linear R (DerivedCategory C) :=
  Localization.linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C _)

instance : Functor.Linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C) :=
  Localization.functor_linear _ _ _

instance : Functor.Linear R (DerivedCategory.Q : _ ⥤ DerivedCategory C) :=
  Functor.linear_of_iso _ (quotientCompQhIso C)

instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Linear R :=
  Shift.linear_of_localization R Qh (HomotopyCategory.subcategoryAcyclic C).trW _

instance (n : ℤ) : Functor.Linear R (DerivedCategory.singleFunctor C n) :=
  Functor.linear_of_iso _ (singleFunctorIsoCompQh C n).symm

end DerivedCategory
