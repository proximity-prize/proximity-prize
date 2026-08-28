/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense

/-!
Permitted flat proof port of Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: 40c67a6f58bac8821282d417c20924609d5b377b2a083608843fdf146639907a.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/

/-! .























 -/

section ProximityFlatProofPort


universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- .


 -/
def CommutatorRing (L : Type v) : Type v := L

instance : NonUnitalNonAssocRing (CommutatorRing L) :=
  have := LieRing.toNonUnitalNonAssocRing L
  inferInstanceAs <| NonUnitalNonAssocRing L

namespace LieAlgebra

instance (L : Type v) [Nonempty L] : Nonempty (CommutatorRing L) := ‹Nonempty L›

instance (L : Type v) [Inhabited L] : Inhabited (CommutatorRing L) := ‹Inhabited L›

instance : LieRing (CommutatorRing L) := inferInstanceAs <| LieRing L

instance : LieAlgebra R (CommutatorRing L) := inferInstanceAs <| LieAlgebra R L

/-- .
 -/
instance isScalarTower : IsScalarTower R (CommutatorRing L) (CommutatorRing L) :=
  ⟨smul_lie (L := L) (M := L)⟩

/-- .
 -/
instance smulCommClass : SMulCommClass R (CommutatorRing L) (CommutatorRing L) :=
  ⟨fun t x y => (lie_smul t x y).symm⟩

end LieAlgebra

namespace LieHom

variable {R L}
variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

/-- .
 -/
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
