import ProximityPrize.SubmissionUpper.OrbitPencil


namespace ProximityPrize.SubmissionUpper.SignOrbit

open ProximityPrize.SubmissionUpper.OrbitPencil

def densityNN : ℕ := 274980728111395088

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
theorem densityNN_spec :
    (2 ^ 31 - 2 ^ 24 + 1) ^ 6 < densityNN * 2 ^ 128 ∧
      densityNN = (2 ^ 31 - 2 ^ 24 + 1) ^ 6 / 2 ^ 128 + 1 := by
  unfold densityNN
  refine ⟨?_, rfl⟩
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
theorem sign_orbit_count :
    ((2 ^ 31 - 2 ^ 24 + 1) ^ 6 * 128) * densityNN < Nat.choose 256 136 := by
  rw [Nat.choose_eq_fast_choose]
  unfold densityNN
  decide

end ProximityPrize.SubmissionUpper.SignOrbit
