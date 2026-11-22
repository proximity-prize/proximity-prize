import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)


theorem block9318_35 : blockEstimate 9318 1962 13162 80 = 0x18f30800 := by decide +kernel

theorem moment9318_group7 : blockEstimate 9318 1962 13162 80 = 0x18f30800 := block9318_35

end HighCore82219BankProof
