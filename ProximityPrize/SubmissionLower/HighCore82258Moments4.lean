import ProximityPrize.SubmissionLower.HighCore82258Moments2

-- merged module HighCore82258Moments3
section Merged_HighCore82258Moments3
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82258BankProof
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


end HighCore82258BankProof
end Merged_HighCore82258Moments3

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem part3131_661_0 : blockEstimate 3131 661 661 220 = 0x13e1c3cbd := by decide +kernel
private theorem part3131_661_1 : blockEstimate 3131 661 881 220 = 0x814fefd91 := by decide +kernel
private theorem part3131_661_2 : blockEstimate 3131 661 1101 220 = 0x1439c24285 := by decide +kernel
private theorem part3131_661_3 : blockEstimate 3131 661 1321 220 = 0x2318e1a2fe := by decide +kernel
private theorem part3131_661_4 : blockEstimate 3131 661 1541 220 = 0x2fca5f778e := by decide +kernel
private theorem part3131_661_5 : blockEstimate 3131 661 1761 220 = 0x39338f9f1e := by decide +kernel
private theorem part3131_661_6 : blockEstimate 3131 661 1981 220 = 0x3f547219ae := by decide +kernel
private theorem part3131_661_7 : blockEstimate 3131 661 2201 220 = 0x422d06e73e := by decide +kernel
private theorem part3131_661_8 : blockEstimate 3131 661 2421 220 = 0x41bd4e07ce := by decide +kernel
private theorem part3131_661_9 : blockEstimate 3131 661 2641 220 = 0x3e05477b5e := by decide +kernel
private theorem part3131_661_10 : blockEstimate 3131 661 2861 220 = 0x3704f341ee := by decide +kernel
private theorem part3131_661_11 : blockEstimate 3131 661 3081 220 = 0x2ced7aaa31 := by decide +kernel
private theorem part3131_661_12 : blockEstimate 3131 661 3301 220 = 0x218df32002 := by decide +kernel
private theorem part3131_661_13 : blockEstimate 3131 661 3521 220 = 0x1692e1b9a9 := by decide +kernel
private theorem part3131_661_14 : blockEstimate 3131 661 3741 220 = 0xcf2dfed74 := by decide +kernel
private theorem part3131_661_15 : blockEstimate 3131 661 3961 220 = 0x59295cf26 := by decide +kernel
private theorem part3131_661_16 : blockEstimate 3131 661 4181 220 = 0x12ee8a16e := by decide +kernel
private theorem part3131_661_17 : blockEstimate 3131 661 4401 52 = 0x25ca9be := by decide +kernel
theorem moment3131_661 : momentEstimate 3131 661 = 0x25ab1ba8825 := by
  exact moment_from_blocks [⟨220,0x13e1c3cbd⟩, ⟨220,0x814fefd91⟩, ⟨220,0x1439c24285⟩, ⟨220,0x2318e1a2fe⟩, ⟨220,0x2fca5f778e⟩, ⟨220,0x39338f9f1e⟩, ⟨220,0x3f547219ae⟩, ⟨220,0x422d06e73e⟩, ⟨220,0x41bd4e07ce⟩, ⟨220,0x3e05477b5e⟩, ⟨220,0x3704f341ee⟩, ⟨220,0x2ced7aaa31⟩, ⟨220,0x218df32002⟩, ⟨220,0x1692e1b9a9⟩, ⟨220,0xcf2dfed74⟩, ⟨220,0x59295cf26⟩, ⟨220,0x12ee8a16e⟩, ⟨52,0x25ca9be⟩]
    ⟨part3131_661_0, part3131_661_1, part3131_661_2, part3131_661_3, part3131_661_4, part3131_661_5, part3131_661_6, part3131_661_7, part3131_661_8, part3131_661_9, part3131_661_10, part3131_661_11, part3131_661_12, part3131_661_13, part3131_661_14, part3131_661_15, part3131_661_16, part3131_661_17,trivial⟩ rfl rfl

private theorem part3142_664_0 : blockEstimate 3142 664 664 220 = 0x13f4a2ef1 := by decide +kernel
private theorem part3142_664_1 : blockEstimate 3142 664 884 220 = 0x81d304ab5 := by decide +kernel
private theorem part3142_664_2 : blockEstimate 3142 664 1104 220 = 0x144ff225d9 := by decide +kernel
private theorem part3142_664_3 : blockEstimate 3142 664 1324 220 = 0x234cc5c69f := by decide +kernel
private theorem part3142_664_4 : blockEstimate 3142 664 1544 220 = 0x3024f805d0 := by decide +kernel
private theorem part3142_664_5 : blockEstimate 3142 664 1764 220 = 0x39b10e1e70 := by decide +kernel
private theorem part3142_664_6 : blockEstimate 3142 664 1984 220 = 0x3ff107af90 := by decide +kernel
private theorem part3142_664_7 : blockEstimate 3142 664 2204 220 = 0x42e4e4b930 := by decide +kernel
private theorem part3142_664_8 : blockEstimate 3142 664 2424 220 = 0x428ca53b50 := by decide +kernel
private theorem part3142_664_9 : blockEstimate 3142 664 2644 220 = 0x3ee84935f0 := by decide +kernel
private theorem part3142_664_10 : blockEstimate 3142 664 2864 220 = 0x37f7d0a910 := by decide +kernel
private theorem part3142_664_11 : blockEstimate 3142 664 3084 220 = 0x2de5b6fd77 := by decide +kernel
private theorem part3142_664_12 : blockEstimate 3142 664 3304 220 = 0x22732ae669 := by decide +kernel
private theorem part3142_664_13 : blockEstimate 3142 664 3524 220 = 0x175892687f := by decide +kernel
private theorem part3142_664_14 : blockEstimate 3142 664 3744 220 = 0xd8f389de2 := by decide +kernel
private theorem part3142_664_15 : blockEstimate 3142 664 3964 220 = 0x5fb3c5c20 := by decide +kernel
private theorem part3142_664_16 : blockEstimate 3142 664 4184 220 = 0x15e5cf233 := by decide +kernel
private theorem part3142_664_17 : blockEstimate 3142 664 4404 66 = 0x4c06b69 := by decide +kernel
theorem moment3142_664 : momentEstimate 3142 664 = 0x263b0eab16b := by
  exact moment_from_blocks [⟨220,0x13f4a2ef1⟩, ⟨220,0x81d304ab5⟩, ⟨220,0x144ff225d9⟩, ⟨220,0x234cc5c69f⟩, ⟨220,0x3024f805d0⟩, ⟨220,0x39b10e1e70⟩, ⟨220,0x3ff107af90⟩, ⟨220,0x42e4e4b930⟩, ⟨220,0x428ca53b50⟩, ⟨220,0x3ee84935f0⟩, ⟨220,0x37f7d0a910⟩, ⟨220,0x2de5b6fd77⟩, ⟨220,0x22732ae669⟩, ⟨220,0x175892687f⟩, ⟨220,0xd8f389de2⟩, ⟨220,0x5fb3c5c20⟩, ⟨220,0x15e5cf233⟩, ⟨66,0x4c06b69⟩]
    ⟨part3142_664_0, part3142_664_1, part3142_664_2, part3142_664_3, part3142_664_4, part3142_664_5, part3142_664_6, part3142_664_7, part3142_664_8, part3142_664_9, part3142_664_10, part3142_664_11, part3142_664_12, part3142_664_13, part3142_664_14, part3142_664_15, part3142_664_16, part3142_664_17,trivial⟩ rfl rfl


end HighCore82258BankProof