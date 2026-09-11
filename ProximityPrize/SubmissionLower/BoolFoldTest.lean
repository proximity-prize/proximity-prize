import ProximityPrize.SubmissionLower.BoundaryTailBaseFast

namespace ProximityPrize.SubmissionLower.BoolFoldTest
open ProximityPrize.SubmissionLower.BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Same arithmetic as `ZeroAtFast`, but a pure Bool fold: no Decidable instances. -/
def zeroCheckB (R V : ℕ) : Bool :=
  (List.range (R+1)).all fun r =>
    (List.range (V+1)).all fun v =>
      if Nat.ble 1 r && (Nat.blt r R || Nat.beq v V) then
        Nat.ble ((fastCarriers r v).c0 + fastZero (R-r) (V-v)) (fastZero R V)
      else true

-- 30 cells, same shape as one receipt chunk
theorem boolFold : (List.range 28).all (fun k => zeroCheckB 12 (100+k)) = true := by
  decide +kernel

end ProximityPrize.SubmissionLower.BoolFoldTest
