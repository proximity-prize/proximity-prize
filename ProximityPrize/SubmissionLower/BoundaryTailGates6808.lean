import ProximityPrize.SubmissionLower.BoundaryTailRealization
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.BoundaryTailGates6808
open RCN095 RCN198 RCN263 RCN287 RCN327 LocatorHybridCells
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Exact characteristic gates for the actual row, instead of a rectangular cap. -/
def Safe (r y : ℕ) : Prop :=
  r * (cellFirstTail y y r).yz + y * (cellFirstTail y y r).all < 2130706433 ∧
  r * (sharpResidualAgreementFlag (cellSupport y y r) w).yz +
    y * (sharpResidualAgreementFlag (cellSupport y y r) w).all < 2130706433
instance (r y : ℕ) : Decidable (Safe r y) := by unfold Safe; infer_instance

theorem z_mixed_bound (f q : FlagDegree) (r y : ℕ)
    (hr : f.all ≤ r) (hy : f.yz + f.all ≤ y) :
    flagMixed f q unitZFlag ≤ r * q.yz + y * q.all := by
  have h1 := Nat.mul_le_mul_right q.yz hr
  have h2 := Nat.mul_le_mul_right q.all hy
  simp only [flagMixed, unitZFlag]
  nlinarith

theorem reduced_gate (f : FlagDegree) (t y r : ℕ)
    (hsafe : Safe r y) (hfa : f.all ≤ r) (hfy : f.yz + f.all ≤ y) :
    flagMixed f (cellFirstTail t y r) unitZFlag < 2130706433 := by
  have hy : (cellFirstTail t y r).yz = (cellFirstTail y y r).yz := rfl
  have hr : (cellFirstTail t y r).all = (cellFirstTail y y r).all := rfl
  exact (z_mixed_bound f _ r y hfa hfy).trans_lt (by rw [hy,hr]; exact hsafe.1)

theorem identity_gate (f : FlagDegree) (t y r : ℕ)
    (hsafe : Safe r y) (hfa : f.all ≤ r) (hfy : f.yz + f.all ≤ y) :
    flagMixed f (sharpResidualAgreementFlag (cellSupport t y r) w) unitZFlag < 2130706433 := by
  have hy : (sharpResidualAgreementFlag (cellSupport t y r) w).yz =
      (sharpResidualAgreementFlag (cellSupport y y r) w).yz := rfl
  have hr : (sharpResidualAgreementFlag (cellSupport t y r) w).all =
      (sharpResidualAgreementFlag (cellSupport y y r) w).all := rfl
  exact (z_mixed_bound f _ r y hfa hfy).trans_lt (by rw [hy,hr]; exact hsafe.2)
end ProximityPrize.SubmissionLower.BoundaryTailGates6808
