import ProximityPrize.SubmissionLower.TerminalCharge6815
namespace ProximityPrize.SubmissionLower.ExactRemovalPhase6815
open scoped BigOperators
open ExactInitialCharge6815 TerminalCharge6815
set_option autoImplicit false
set_option maxHeartbeats 1000000

def tSlope (_L U S r y : ℕ) : ℕ :=
  131073*((1+2*131071*y)*S+131071*(2*r-1)*U+2*131071*(y*S+r*U))

theorem num_shift (L U S r y z : ℕ) :
    num L U S r y (y+z)=num L U S r y y+tSlope L U S r y*z := by
  rw [num_formula,num_formula]
  unfold tSlope
  ring

end ProximityPrize.SubmissionLower.ExactRemovalPhase6815
