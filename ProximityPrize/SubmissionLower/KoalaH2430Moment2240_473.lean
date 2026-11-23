import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Banks
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem p473 : blockEstimate 2240 473 473 128 = 0x2dbc2820 := by decide +kernel
private theorem p601 : blockEstimate 2240 473 601 128 = 0x12bbc3820 := by decide +kernel
private theorem p729 : blockEstimate 2240 473 729 128 = 0x2f98c4820 := by decide +kernel
private theorem p857 : blockEstimate 2240 473 857 128 = 0x566264a8a := by decide +kernel
private theorem p985 : blockEstimate 2240 473 985 128 = 0x7f9a775c0 := by decide +kernel
private theorem p1113 : blockEstimate 2240 473 1113 128 = 0xa2380b5c0 := by decide +kernel
private theorem p1241 : blockEstimate 2240 473 1241 128 = 0xbd6d9f5c0 := by decide +kernel
private theorem p1369 : blockEstimate 2240 473 1369 128 = 0xd13b335c0 := by decide +kernel
private theorem p1497 : blockEstimate 2240 473 1497 128 = 0xdda0c75c0 := by decide +kernel
private theorem p1625 : blockEstimate 2240 473 1625 128 = 0xe29e5b5c0 := by decide +kernel
private theorem p1753 : blockEstimate 2240 473 1753 128 = 0xe033ef5c0 := by decide +kernel
private theorem p1881 : blockEstimate 2240 473 1881 128 = 0xd661835c0 := by decide +kernel
private theorem p2009 : blockEstimate 2240 473 2009 128 = 0xc527175c0 := by decide +kernel
private theorem p2137 : blockEstimate 2240 473 2137 128 = 0xac8668034 := by decide +kernel
private theorem p2265 : blockEstimate 2240 473 2265 128 = 0x8e1cd72e7 := by decide +kernel
private theorem p2393 : blockEstimate 2240 473 2393 128 = 0x6e73b32d3 := by decide +kernel
private theorem p2521 : blockEstimate 2240 473 2521 128 = 0x4ff17a1e3 := by decide +kernel
private theorem p2649 : blockEstimate 2240 473 2649 128 = 0x34598a13e := by decide +kernel
private theorem p2777 : blockEstimate 2240 473 2777 128 = 0x1d3d367b0 := by decide +kernel
private theorem p2905 : blockEstimate 2240 473 2905 128 = 0xc46f23b0 := by decide +kernel
private theorem p3033 : blockEstimate 2240 473 3033 128 = 0x2785dfb0 := by decide +kernel
private theorem p3161 : blockEstimate 2240 473 3161 25 = 0x349d57 := by decide +kernel

theorem moment2240_473 : momentEstimate 2240 473 = 0x9e16b78820 :=
  moment_from_blocks [⟨128,0x2dbc2820⟩, ⟨128,0x12bbc3820⟩, ⟨128,0x2f98c4820⟩, ⟨128,0x566264a8a⟩, ⟨128,0x7f9a775c0⟩, ⟨128,0xa2380b5c0⟩, ⟨128,0xbd6d9f5c0⟩, ⟨128,0xd13b335c0⟩, ⟨128,0xdda0c75c0⟩, ⟨128,0xe29e5b5c0⟩, ⟨128,0xe033ef5c0⟩, ⟨128,0xd661835c0⟩, ⟨128,0xc527175c0⟩, ⟨128,0xac8668034⟩, ⟨128,0x8e1cd72e7⟩, ⟨128,0x6e73b32d3⟩, ⟨128,0x4ff17a1e3⟩, ⟨128,0x34598a13e⟩, ⟨128,0x1d3d367b0⟩, ⟨128,0xc46f23b0⟩, ⟨128,0x2785dfb0⟩, ⟨25,0x349d57⟩] ⟨p473, p601, p729, p857, p985, p1113, p1241, p1369, p1497, p1625, p1753, p1881, p2009, p2137, p2265, p2393, p2521, p2649, p2777, p2905, p3033, p3161, trivial⟩ rfl rfl

end KoalaH2430Banks
