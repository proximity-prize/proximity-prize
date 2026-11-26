import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Category_ModuleCat_Projective
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Homology_DerivedCategory_Ext_EnoughProjectives
set_option Elab.async false
/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/





/-!
# HasExt instance for Module Category

If we assume `Small.{v} R`, the category `ModuleCat.{v} R` has enough projectives, which allows to
introduce the instance `HasExt.{v} (ModuleCat.{v} R)`. As a result, `Ext`-groups in this category
of modules are defined and belong to `Type v`.
-/

section

universe v u

variable (R : Type u) [Ring R]

instance [Small.{v} R] : CategoryTheory.HasExt.{v} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{v} (ModuleCat.{v} R)
