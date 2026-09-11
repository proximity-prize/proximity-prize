import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.BoundaryTailGates
open RCN095 RCN198 RCN263 RCN287 RCN327 LocatorHybridCells
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem z_mixed_bound (f q : FlagDegree) (R capY : ℕ) (hfa : f.all ≤ 31)
    (hfy : f.yz + f.all ≤ 142) (hqa : q.all ≤ R)
    (hqy : q.yz + q.all ≤ capY) :
    flagMixed f q unitZFlag ≤ 31 * capY + 111 * R := by
  have h1 := Nat.mul_le_mul_right q.all hfy
  have h2 := Nat.mul_le_mul_right q.yz hfa
  have h3 := Nat.mul_le_mul_left 31 hqy
  have h4 := Nat.mul_le_mul_left 111 hqa
  simp only [flagMixed, unitZFlag]
  nlinarith

theorem reduced_gate (f : FlagDegree) (t y r : ℕ)
    (hr : 3 ≤ r) (hrcap : r ≤ 31) (hycap : y ≤ 142)
    (hry : r + 2 ≤ y) (hyt : y ≤ t)
    (hfa : f.all ≤ r) (hfy : f.yz + f.all ≤ y) :
    flagMixed f (cellFirstTail t y r) unitZFlag < 2130706433 := by
  have hys : cellB y r + cellS r + 3 = y := by dsimp [cellB,cellS]; omega
  have hs : cellS r + 2 = r := by dsimp [cellS]; omega
  have hqa : (cellFirstTail t y r).all ≤ 7864320 := by
    simp only [cellFirstTail, reducedResidualAgreementFlag, reducedAgreementDirection, cellSupport, RCN198.support, hs, w]
    omega
  have hqy : (cellFirstTail t y r).yz + (cellFirstTail t y r).all ≤ 36962305 := by
    rw [cellFirstTail, reducedResidualAgreementFlag_ys]
    simp only [cellSupport, RCN198.support, hys, w]
    omega
  exact (z_mixed_bound f _ _ _ (hfa.trans hrcap) (hfy.trans hycap) hqa hqy).trans_lt (by decide)

theorem identity_gate (f : FlagDegree) (t y r : ℕ)
    (hr : 3 ≤ r) (hrcap : r ≤ 31) (hycap : y ≤ 142)
    (hry : r + 2 ≤ y) (hyt : y ≤ t)
    (hfa : f.all ≤ r) (hfy : f.yz + f.all ≤ y) :
    flagMixed f (sharpResidualAgreementFlag (cellSupport t y r) w) unitZFlag <
      2130706433 := by
  have hys : cellB y r + cellS r + 3 = y := by dsimp [cellB,cellS]; omega
  have hs : cellS r + 2 = r := by dsimp [cellS]; omega
  have hqa : (sharpResidualAgreementFlag (cellSupport t y r) w).all ≤ 7995331 := by
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection, cellSupport, RCN198.support, hs, w]
    omega
  have hqy : (sharpResidualAgreementFlag (cellSupport t y r) w).yz +
      (sharpResidualAgreementFlag (cellSupport t y r) w).all ≤ 36962023 := by
    rw [sharpResidualAgreementFlag_ys (cellSupport t y r) (by
      simp only [cellSupport, RCN198.support]; omega)]
    simp only [cellSupport, RCN198.support, hys, w]
    omega
  exact (z_mixed_bound f _ _ _ (hfa.trans hrcap) (hfy.trans hycap) hqa hqy).trans_lt (by decide)

end ProximityPrize.SubmissionLower.BoundaryTailGates
