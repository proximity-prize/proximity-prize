import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Banks
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem p359 : blockEstimate 1704 359 359 128 = 0x224e2420 := by decide +kernel
private theorem p487 : blockEstimate 1704 359 487 128 = 0xdcc83420 := by decide +kernel
private theorem p615 : blockEstimate 1704 359 615 128 = 0x223dda152 := by decide +kernel
private theorem p743 : blockEstimate 1704 359 743 128 = 0x39c974100 := by decide +kernel
private theorem p871 : blockEstimate 1704 359 871 128 = 0x4cac24100 := by decide +kernel
private theorem p999 : blockEstimate 1704 359 999 128 = 0x59eed4100 := by decide +kernel
private theorem p1127 : blockEstimate 1704 359 1127 128 = 0x619184100 := by decide +kernel
private theorem p1255 : blockEstimate 1704 359 1255 128 = 0x639434100 := by decide +kernel
private theorem p1383 : blockEstimate 1704 359 1383 128 = 0x5ff6e4100 := by decide +kernel
private theorem p1511 : blockEstimate 1704 359 1511 128 = 0x56b994100 := by decide +kernel
private theorem p1639 : blockEstimate 1704 359 1639 128 = 0x47f1becd6 := by decide +kernel
private theorem p1767 : blockEstimate 1704 359 1767 128 = 0x35e36fede := by decide +kernel
private theorem p1895 : blockEstimate 1704 359 1895 128 = 0x240e89f92 := by decide +kernel
private theorem p2023 : blockEstimate 1704 359 2023 128 = 0x145745025 := by decide +kernel
private theorem p2151 : blockEstimate 1704 359 2151 128 = 0x86052ba0 := by decide +kernel
private theorem p2279 : blockEstimate 1704 359 2279 128 = 0x1880bba0 := by decide +kernel
private theorem p2407 : blockEstimate 1704 359 2407 15 = 0x9a2d4 := by decide +kernel

theorem moment1704_359 : momentEstimate 1704 359 = 0x34e8dd2611 :=
  moment_from_blocks [⟨128,0x224e2420⟩, ⟨128,0xdcc83420⟩, ⟨128,0x223dda152⟩, ⟨128,0x39c974100⟩, ⟨128,0x4cac24100⟩, ⟨128,0x59eed4100⟩, ⟨128,0x619184100⟩, ⟨128,0x639434100⟩, ⟨128,0x5ff6e4100⟩, ⟨128,0x56b994100⟩, ⟨128,0x47f1becd6⟩, ⟨128,0x35e36fede⟩, ⟨128,0x240e89f92⟩, ⟨128,0x145745025⟩, ⟨128,0x86052ba0⟩, ⟨128,0x1880bba0⟩, ⟨15,0x9a2d4⟩] ⟨p359, p487, p615, p743, p871, p999, p1127, p1255, p1383, p1511, p1639, p1767, p1895, p2023, p2151, p2279, p2407, trivial⟩ rfl rfl

end KoalaH2430Banks
