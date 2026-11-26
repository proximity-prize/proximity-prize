import ProximityPrize.Benchmark.TargetLower
set_option Elab.async false
/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/





set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Intermediate Fields of Rational Function Fields

Results relating `IntermediateField` and `RatFunc`.
-/

variable {K : Type*} [Field K]

namespace RatFunc

open IntermediateField algebraAdjoinAdjoin Polynomial Algebra

section

variable (f : K⟮X⟯)

theorem adjoin_X : K⟮(«X» : K⟮X⟯)⟯ = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩

theorem IntermediateField.adjoin_X (E : IntermediateField K K⟮X⟯) :
    E⟮(«X» : K⟮X⟯)⟯ = ⊤ := by
  rw [← restrictScalars_eq_top_iff (K := K), IntermediateField.restrictScalars_adjoin,
    _root_.eq_top_iff]
  exact le_trans (le_of_eq RatFunc.adjoin_X.symm) (adjoin.mono _ _ _ (by simp))

/-- The equivalence between `E⟮X⟯` and `K⟮X⟯` as `E`-algebras. -/
noncomputable def IntermediateField.adjoinXEquiv (E : IntermediateField K K⟮X⟯) :
    E⟮(«X» : K⟮X⟯)⟯ ≃ₐ[E] K⟮X⟯ :=
  (equivOfEq (adjoin_X E)).trans topEquiv

end
end RatFunc
