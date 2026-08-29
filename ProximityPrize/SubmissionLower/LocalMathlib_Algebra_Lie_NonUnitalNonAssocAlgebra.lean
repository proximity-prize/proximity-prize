/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense

/-! . -/

/-! . -/

section ProximityFlatProofPort


universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- . -/
def CommutatorRing (L : Type v) : Type v := L

instance : NonUnitalNonAssocRing (CommutatorRing L) :=
  have := LieRing.toNonUnitalNonAssocRing L
  inferInstanceAs <| NonUnitalNonAssocRing L

namespace LieAlgebra

instance (L : Type v) [Nonempty L] : Nonempty (CommutatorRing L) := ‹Nonempty L›

instance (L : Type v) [Inhabited L] : Inhabited (CommutatorRing L) := ‹Inhabited L›

instance : LieRing (CommutatorRing L) := inferInstanceAs <| LieRing L

instance : LieAlgebra R (CommutatorRing L) := inferInstanceAs <| LieAlgebra R L

/-- . -/
instance isScalarTower : IsScalarTower R (CommutatorRing L) (CommutatorRing L) :=
  ⟨smul_lie (L := L) (M := L)⟩

/-- . -/
instance smulCommClass : SMulCommClass R (CommutatorRing L) (CommutatorRing L) :=
  ⟨fun t x y => (lie_smul t x y).symm⟩

end LieAlgebra

namespace LieHom

variable {R L}
variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

/-- . -/
@[simps toFun]
def toNonUnitalAlgHom (f : L →ₗ⁅R⁆ L₂) : CommutatorRing L →ₙₐ[R] CommutatorRing L₂ :=
  { f with
    toFun := f
    map_zero' := f.toLinearMap.map_zero
    map_mul' := f.map_lie }

theorem toNonUnitalAlgHom_injective :
    Function.Injective (toNonUnitalAlgHom : _ → CommutatorRing L →ₙₐ[R] CommutatorRing L₂) :=
  fun _ _ h => ext <| NonUnitalAlgHom.congr_fun h

end LieHom
