import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb1154_244_0 : blockEstimate 1154 244 244 800 = 0x7c58f6bfb := by decide +kernel
theorem nb1687_355_2 : blockEstimate 1687 355 1955 442 = 0x28010b587 := by decide +kernel
theorem nb1977_416_0 : blockEstimate 1977 416 416 800 = 0x18ad8f7508 := by decide +kernel
theorem nb233_51_0 : blockEstimate 233 51 51 284 = 0x507dc25 := by decide +kernel
theorem nb2395_500_1 : blockEstimate 2395 500 1300 800 = 0x65101f6bf0 := by decide +kernel
theorem nb414_87_0 : blockEstimate 414 87 87 501 = 0x2fd6e865 := by decide +kernel
theorem nb4935_1017_4 : blockEstimate 4935 1017 4217 800 = 0x304eb38101c := by decide +kernel
theorem nb5036_1070_4 : blockEstimate 5036 1070 4270 800 = 0x363d506fdf2 := by decide +kernel
theorem nb7120_1510_4 : blockEstimate 7120 1510 4710 800 = 0xaf4651e7fd0 := by decide +kernel

end HighCore82219BankProof
