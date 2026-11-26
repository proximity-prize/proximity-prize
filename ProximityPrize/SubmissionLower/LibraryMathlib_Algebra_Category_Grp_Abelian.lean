import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Category_Grp_Colimits
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Category_ModuleCat_Abelian
set_option Elab.async false
/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/







set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# The category of abelian groups is abelian
-/

section

open CategoryTheory

universe u

noncomputable section

namespace AddCommGrpCat

variable {«X» «Y» : AddCommGrpCat.{u}} (f : «X» ⟶ «Y»)

/-- In the category of abelian groups, every monomorphism is normal. -/
@[instance_reducible]
def normalMono (_ : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv <|
    ModuleCat.normalMono _ inferInstance

/-- In the category of abelian groups, every epimorphism is normal. -/
@[instance_reducible]
def normalEpi (_ : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv <|
    ModuleCat.normalEpi _ inferInstance

/-- The category of abelian groups is abelian. -/
instance : Abelian AddCommGrpCat.{u} where
  normalMonoOfMono f hf := ⟨normalMono f hf⟩
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

end AddCommGrpCat
