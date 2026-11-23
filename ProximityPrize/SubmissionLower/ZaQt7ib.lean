import ProximityPrize.SubmissionLower.V
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.DG
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace rW
noncomputable section
open K1 aR dN Polynomial MvPolynomial
open scoped BigOperators
def c5:Prop :=
  ∀ A:kT,A.IsPrime→(gN A).IsPrime→dimension A=2 →
    asY A →
    2*affineDegree A≤133671*affineDegree (lA A)
end
end rW
