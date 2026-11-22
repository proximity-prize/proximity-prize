-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Moments3.lean.
import ProximityPrize.SubmissionLower.Peer653High53Moments2

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace Peer653High53BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem part2235_472_0 : blockEstimate 2235 472 472 220 = 0xde095abd := by decide +kernel
private theorem part2235_472_1 : blockEstimate 2235 472 692 220 = 0x579ac4391 := by decide +kernel
private theorem part2235_472_2 : blockEstimate 2235 472 912 220 = 0xcbf6ce3b6 := by decide +kernel
private theorem part2235_472_3 : blockEstimate 2235 472 1132 220 = 0x12e16e490e := by decide +kernel
private theorem part2235_472_4 : blockEstimate 2235 472 1352 220 = 0x16ab9e96fe := by decide +kernel
private theorem part2235_472_5 : blockEstimate 2235 472 1572 220 = 0x181d68fd6e := by decide +kernel
private theorem part2235_472_6 : blockEstimate 2235 472 1792 220 = 0x1736cd7c5e := by decide +kernel
private theorem part2235_472_7 : blockEstimate 2235 472 2012 220 = 0x13f7cc13ce := by decide +kernel
private theorem part2235_472_8 : blockEstimate 2235 472 2232 220 = 0xeae7710ca := by decide +kernel
private theorem part2235_472_9 : blockEstimate 2235 472 2452 220 = 0x8fb6267c3 := by decide +kernel
private theorem part2235_472_10 : blockEstimate 2235 472 2672 220 = 0x41dfb4461 := by decide +kernel
private theorem part2235_472_11 : blockEstimate 2235 472 2892 220 = 0xf7152799 := by decide +kernel
private theorem part2235_472_12 : blockEstimate 2235 472 3112 67 = 0x3848ec7 := by decide +kernel
theorem moment2235_472 : momentEstimate 2235 472 = 0x9cb2a062f8 := by
  exact moment_from_blocks [⟨220,0xde095abd⟩, ⟨220,0x579ac4391⟩, ⟨220,0xcbf6ce3b6⟩, ⟨220,0x12e16e490e⟩, ⟨220,0x16ab9e96fe⟩, ⟨220,0x181d68fd6e⟩, ⟨220,0x1736cd7c5e⟩, ⟨220,0x13f7cc13ce⟩, ⟨220,0xeae7710ca⟩, ⟨220,0x8fb6267c3⟩, ⟨220,0x41dfb4461⟩, ⟨220,0xf7152799⟩, ⟨67,0x3848ec7⟩]
    ⟨part2235_472_0, part2235_472_1, part2235_472_2, part2235_472_3, part2235_472_4, part2235_472_5, part2235_472_6, part2235_472_7, part2235_472_8, part2235_472_9, part2235_472_10, part2235_472_11, part2235_472_12,trivial⟩ rfl rfl


end Peer653High53BankProof
