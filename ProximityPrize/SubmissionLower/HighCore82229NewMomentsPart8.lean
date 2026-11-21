import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb1687_355_1 : blockEstimate 1687 355 1155 800 = 0x1e01f51ad8 := by decide +kernel
theorem nb2096_448_1 : blockEstimate 2096 448 1248 800 = 0x44c1214b60 := by decide +kernel
theorem nb2179_461_1 : blockEstimate 2179 461 1261 800 = 0x4d2bfdcb90 := by decide +kernel
theorem nb300_67_0 : blockEstimate 300 67 67 367 = 0xdedff80 := by decide +kernel
theorem nb307_67_0 : blockEstimate 307 67 67 374 = 0xeffb6fa := by decide +kernel
theorem nb4935_1017_1 : blockEstimate 4935 1017 1817 800 = 0x1e1a8da42f2 := by decide +kernel
theorem nb5036_1070_1 : blockEstimate 5036 1070 1870 800 = 0x1f5e109ac8f := by decide +kernel
theorem nb615_129_0 : blockEstimate 615 129 129 744 = 0xe712e33d := by decide +kernel
theorem nb7120_1510_1 : blockEstimate 7120 1510 2310 800 = 0x32ca4f9d54d := by decide +kernel

end HighCore82219BankProof
