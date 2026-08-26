import ProximityPrize.SubmissionLower.BCHKSPrimitiveLocalizedSelection
import ProximityPrize.SubmissionLower.BCHKSPrimitiveSpecialization
namespace ProximityPrize.SubmissionLower
open Polynomial
noncomputable def PrimitiveObstruction.toEffective
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))} {DZ DX : ℕ}
    (w : PrimitiveObstruction F R DZ DX) :
    EffectivePrimitiveObstruction F R where
  obstruction := w.obstruction
  ne := w.resultant_ne_zero
  property := w.isPrimitive_of_eval_ne_zero
theorem PrimitiveObstruction.toEffective_degree_le
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))} {DZ DX : ℕ}
    (w : PrimitiveObstruction F R DZ DX) :
    w.toEffective.obstruction.natDegree ≤ 2 * DZ * DX :=
  w.obstruction_natDegree_le
end ProximityPrize.SubmissionLower
