import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb1154_244_1 : blockEstimate 1154 244 1044 598 = 0x36a6b53b6 := by decide +kernel
theorem nb1235_261_0 : blockEstimate 1235 261 261 800 = 0x936a7d77d := by decide +kernel
theorem nb1977_416_1 : blockEstimate 1977 416 1216 800 = 0x37cbd33bc0 := by decide +kernel
theorem nb2395_500_2 : blockEstimate 2395 500 2100 800 = 0x40742eaa77 := by decide +kernel
theorem nb4935_1017_5 : blockEstimate 4935 1017 5017 800 = 0x1b4339d7623 := by decide +kernel
theorem nb5036_1070_5 : blockEstimate 5036 1070 5070 800 = 0x20add271f90 := by decide +kernel
theorem nb7120_1510_5 : blockEstimate 7120 1510 5510 800 = 0xad8401c13d0 := by decide +kernel
theorem nb738_155_1 : blockEstimate 738 155 955 93 = 0x2e9b994 := by decide +kernel
theorem nb844_187_1 : blockEstimate 844 187 987 231 = 0x2ddecc3c := by decide +kernel

end HighCore82219BankProof
