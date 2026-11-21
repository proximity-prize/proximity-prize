import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb1307_276_1 : blockEstimate 1307 276 1076 783 = 0x7d30cb26d := by decide +kernel
theorem nb1977_416_2 : blockEstimate 1977 416 2016 793 = 0xf3caa1fdc := by decide +kernel
theorem nb2395_500_0 : blockEstimate 2395 500 500 800 = 0x220fe0e7dd := by decide +kernel
theorem nb4935_1017_3 : blockEstimate 4935 1017 3417 800 = 0x395fb3ae5f0 := by decide +kernel
theorem nb5036_1070_3 : blockEstimate 5036 1070 3470 800 = 0x3e821901250 := by decide +kernel
theorem nb7120_1510_3 : blockEstimate 7120 1510 3910 800 = 0x9a84a01ebd0 := by decide +kernel
theorem nb738_155_0 : blockEstimate 738 155 155 800 = 0x1db9e4ed1 := by decide +kernel
theorem nb975_205_1 : blockEstimate 975 205 1005 380 = 0xd710ddc7 := by decide +kernel

end HighCore82219BankProof
