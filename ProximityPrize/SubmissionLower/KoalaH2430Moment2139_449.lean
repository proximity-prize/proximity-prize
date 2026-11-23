import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Banks
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem p449 : blockEstimate 2139 449 449 128 = 0x2b94cca0 := by decide +kernel
private theorem p577 : blockEstimate 2139 449 577 128 = 0x11cdb9ca0 := by decide +kernel
private theorem p705 : blockEstimate 2139 449 705 128 = 0x2d1526ca0 := by decide +kernel
private theorem p833 : blockEstimate 2139 449 833 128 = 0x514e48db0 := by decide +kernel
private theorem p961 : blockEstimate 2139 449 961 128 = 0x75ccbe2c0 := by decide +kernel
private theorem p1089 : blockEstimate 2139 449 1089 128 = 0x938f1a2c0 := by decide +kernel
private theorem p1217 : blockEstimate 2139 449 1217 128 = 0xaa49762c0 := by decide +kernel
private theorem p1345 : blockEstimate 2139 449 1345 128 = 0xb9fbd22c0 := by decide +kernel
private theorem p1473 : blockEstimate 2139 449 1473 128 = 0xc2a62e2c0 := by decide +kernel
private theorem p1601 : blockEstimate 2139 449 1601 128 = 0xc4488a2c0 := by decide +kernel
private theorem p1729 : blockEstimate 2139 449 1729 128 = 0xbee2e62c0 := by decide +kernel
private theorem p1857 : blockEstimate 2139 449 1857 128 = 0xb275422c0 := by decide +kernel
private theorem p1985 : blockEstimate 2139 449 1985 128 = 0x9eff9e2c0 := by decide +kernel
private theorem p2113 : blockEstimate 2139 449 2113 128 = 0x84f5d71df := by decide +kernel
private theorem p2241 : blockEstimate 2139 449 2241 128 = 0x683384878 := by decide +kernel
private theorem p2369 : blockEstimate 2139 449 2369 128 = 0x4bf852ea2 := by decide +kernel
private theorem p2497 : blockEstimate 2139 449 2497 128 = 0x321fe41f3 := by decide +kernel
private theorem p2625 : blockEstimate 2139 449 2625 128 = 0x1c3a4de00 := by decide +kernel
private theorem p2753 : blockEstimate 2139 449 2753 128 = 0xbfd43600 := by decide +kernel
private theorem p2881 : blockEstimate 2139 449 2881 128 = 0x27d48e00 := by decide +kernel
private theorem p3009 : blockEstimate 2139 449 3009 28 = 0x4546e2 := by decide +kernel

theorem moment2139_449 : momentEstimate 2139 449 = 0x82dccd701e :=
  moment_from_blocks [⟨128,0x2b94cca0⟩, ⟨128,0x11cdb9ca0⟩, ⟨128,0x2d1526ca0⟩, ⟨128,0x514e48db0⟩, ⟨128,0x75ccbe2c0⟩, ⟨128,0x938f1a2c0⟩, ⟨128,0xaa49762c0⟩, ⟨128,0xb9fbd22c0⟩, ⟨128,0xc2a62e2c0⟩, ⟨128,0xc4488a2c0⟩, ⟨128,0xbee2e62c0⟩, ⟨128,0xb275422c0⟩, ⟨128,0x9eff9e2c0⟩, ⟨128,0x84f5d71df⟩, ⟨128,0x683384878⟩, ⟨128,0x4bf852ea2⟩, ⟨128,0x321fe41f3⟩, ⟨128,0x1c3a4de00⟩, ⟨128,0xbfd43600⟩, ⟨128,0x27d48e00⟩, ⟨28,0x4546e2⟩] ⟨p449, p577, p705, p833, p961, p1089, p1217, p1345, p1473, p1601, p1729, p1857, p1985, p2113, p2241, p2369, p2497, p2625, p2753, p2881, p3009, trivial⟩ rfl rfl

end KoalaH2430Banks
