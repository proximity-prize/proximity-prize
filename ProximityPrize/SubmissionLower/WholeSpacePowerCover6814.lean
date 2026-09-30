import ProximityPrize.SubmissionLower.WholeSpacePowerBox6814
import ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814
namespace ProximityPrize.SubmissionLower.WholeSpacePowerCover6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open WholeSpacePowerBox6814 MovingSourceNativeEnvelope6814 RCN095 SecondJetRelaxedFlag

def native (m s b u t : ℕ) : ℕ :=
  3*126275387074424400*m+
    coefficientZ3*flagMixed parentFlag unitZFlag (budgetFlag b u t m s)+
    coefficientU3*flagMixed parentFlag unitYZFlag (budgetFlag b u t m s)+
    coefficientA3*flagMixed parentFlag unitAllFlag (budgetFlag b u t m s)

end
end ProximityPrize.SubmissionLower.WholeSpacePowerCover6814
