import ProximityPrize.SubmissionLower.Q
import ProximityPrize.SubmissionLower.CJ
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000
namespace pI
noncomputable section
open K1 cu gT Polynomial
open scoped Classical
def c1 :Prop :=
 ∀ P s,P≠0→ oU P s→Nonempty (NO P s)
end
end pI
end
