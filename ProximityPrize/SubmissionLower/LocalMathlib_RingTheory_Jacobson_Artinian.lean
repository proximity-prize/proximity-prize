/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Andrew Yang
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense

/-!
Permitted flat proof port of Mathlib.RingTheory.Jacobson.Artinian.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: 06fcefd9d2e8fefa05b9d4bdca9149cb45a5aceb7ddd5cd1ef4e639ced848f8f.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/

/-!
# Artinian rings over Jacobson rings

## Main results
- `Module.finite_iff_isArtinianRing`: If `A` is a finite type algebra over an Artinian ring `R`,
  then `A` is finite over `R` if and only if `A` is an Artinian ring.

-/

section ProximityFlatProofPort

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
lemma Module.finite_of_isSemisimpleRing [IsJacobsonRing R] [IsSemisimpleRing A] :
    Module.Finite R A :=
  have (I : MaximalSpectrum A) := finite_of_finite_type_of_isJacobsonRing R (A ⧸ I.asIdeal)
  .equiv ((IsArtinianRing.equivPi A).restrictScalars R).toLinearEquiv.symm

/-- If `A` is a finite type algebra over `R`, then `A` is an Artinian ring and `R` is Jacobson
implies `A` is finite over `R`. -/
/- If made an instance, causes timeouts synthesizing `FaithfulSMul R I.ResidueField` at
`Ideal.algebraMap_residueField_eq_zero` and `Ideal.ker_algebraMap_residueField` during
simpNF linting. -/
lemma Module.finite_of_isArtinianRing [IsJacobsonRing R] [IsArtinianRing A] :
    Module.Finite R A :=
  have := finite_of_isSemisimpleRing R (A ⧸ Ring.jacobson A)
  IsSemiprimaryRing.finite_of_isArtinian R A A

/-- If `A` is a finite type algebra over an Artinian ring `R`,
then `A` is finite over `R` if and only if `A` is an Artinian ring. -/
lemma Module.finite_iff_isArtinianRing [IsArtinianRing R] :
    Module.Finite R A ↔ IsArtinianRing A :=
  ⟨isArtinian_of_tower _ ∘ ((IsArtinianRing.tfae R A).out 0 2).mp,
    fun _ ↦ finite_of_isArtinianRing R A⟩

/-- If `A` is a finite type algebra over an Artinian ring `R`,
then `A` is finite over `R` if and only if `dim A = 0`. -/
lemma Module.finite_iff_krullDimLE_zero [IsArtinianRing R] :
    Module.Finite R A ↔ Ring.KrullDimLE 0 A := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  rw [finite_iff_isArtinianRing, isArtinianRing_iff_isNoetherianRing_krullDimLE_zero,
    and_iff_right this]
