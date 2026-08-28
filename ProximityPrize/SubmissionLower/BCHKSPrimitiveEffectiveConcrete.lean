import ProximityPrize.SubmissionLower.BCHKSPrimitiveSpecialization

namespace ProximityPrize.SubmissionLower

open Polynomial

/-- The completed-column obstruction, packaged in the interface used by the
concrete staged argument.  Keeping this lemma here avoids downstream code
having to pass through the older cleared-certificate interface. -/
noncomputable def CompletedColumnCertificate.toEffective
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))} {N : ℕ}
    (w : CompletedColumnCertificate F R N) :
    EffectivePrimitiveObstruction F R where
  obstruction := w.completion.det
  ne := w.det_ne_zero
  property := w.isPrimitive_of_det_eval_ne_zero

/-- The effective obstruction supplied by a completed localized span has the
sharp determinant bound (and hence also the slightly looser leading-coefficient
resultant bound used by the concrete IRS integration). -/
theorem CompletedColumnCertificate.toEffective_degree_le
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))} {N : ℕ}
    (w : CompletedColumnCertificate F R N) :
    w.toEffective.obstruction.natDegree ≤
      2 * (BCHKSConcreteGS.DZ + 1) * BCHKSConcreteGS.DX := by
  change w.completion.det.natDegree ≤ _
  refine w.det_natDegree_le.trans ?_
  exact Nat.mul_le_mul_right BCHKSConcreteGS.DX
    (Nat.mul_le_mul_left 2 (Nat.le_succ BCHKSConcreteGS.DZ))

end ProximityPrize.SubmissionLower
