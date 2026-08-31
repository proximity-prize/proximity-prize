/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Junyan Xu,Andrew Yang
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
section ProximityFlatProofPort
variable (R A:Type*) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
lemma Module.finite_of_isSemisimpleRing [IsJacobsonRing R] [IsSemisimpleRing A]:
    Module.Finite R A:=
  have (I:MaximalSpectrum A):=finite_of_finite_type_of_isJacobsonRing R (A ⧸ I.asIdeal)
  .equiv ((IsArtinianRing.equivPi A).restrictScalars R).toLinearEquiv.symm
lemma Module.finite_of_isArtinianRing [IsJacobsonRing R] [IsArtinianRing A]:
    Module.Finite R A:=
  have:=finite_of_isSemisimpleRing R (A ⧸ Ring.jacobson A)
  IsSemiprimaryRing.finite_of_isArtinian R A A
lemma Module.finite_iff_isArtinianRing [IsArtinianRing R]:
    Module.Finite R A ↔ IsArtinianRing A:=
  ⟨isArtinian_of_tower _ ∘ ((IsArtinianRing.tfae R A).out 0 2).mp,
    fun _↦finite_of_isArtinianRing R A⟩
lemma Module.finite_iff_krullDimLE_zero [IsArtinianRing R]:
    Module.Finite R A ↔ Ring.KrullDimLE 0 A:=by
  have:IsNoetherianRing A:=Algebra.FiniteType.isNoetherianRing R A
  rw [finite_iff_isArtinianRing,isArtinianRing_iff_isNoetherianRing_krullDimLE_zero,
    and_iff_right this]
