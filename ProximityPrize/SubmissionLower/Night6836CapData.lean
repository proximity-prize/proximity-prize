/- Apache-2.0. Multifactor bounds against the actual factor-degree allowance. -/
import ProximityPrize.SubmissionLower.Night6836Fast
import ProximityPrize.SubmissionLower.Night6836Room
namespace Koala6836.Fast
set_option maxRecDepth 30000
set_option maxHeartbeats 0
def capOK (r e : Nat) : Bool :=
  decide (Room.lowBudget r e ≤ Room.highBudget r e) &&
  (List.range N).all fun k => decide (r+e+100*k ≤ Room.maxTotal r e →
    (G-lane (Grid.compRow r e) k)*770000000000000 ≤ Room.budget r e (r+e+100*k))
def capRow (r : Nat) := (List.range (77-r)).all fun e => capOK r e
theorem cap1 : capRow 1=true := by decide +kernel
theorem cap2 : capRow 2=true := by decide +kernel
theorem cap3 : capRow 3=true := by decide +kernel
theorem cap4 : capRow 4=true := by decide +kernel
theorem cap5 : capRow 5=true := by decide +kernel
theorem cap6 : capRow 6=true := by decide +kernel
theorem cap7 : capRow 7=true := by decide +kernel
theorem cap8 : capRow 8=true := by decide +kernel
theorem cap9 : capRow 9=true := by decide +kernel
theorem cap10 : capRow 10=true := by decide +kernel
theorem cap11 : capRow 11=true := by decide +kernel
theorem cap12 : capRow 12=true := by decide +kernel
theorem cap13 : capRow 13=true := by decide +kernel
theorem cap14 : capRow 14=true := by decide +kernel
theorem cap15 : capRow 15=true := by decide +kernel
theorem cap16 : capRow 16=true := by decide +kernel
theorem cap17 : capRow 17=true := by decide +kernel
theorem cap18 : capRow 18=true := by decide +kernel
end Koala6836.Fast
