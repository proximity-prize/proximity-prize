import ProximityPrize.SubmissionLower.HighCore82219Moments1

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
open scoped P1_7_1_3_2
set_option maxHeartbeats 14000000


theorem moment2034_430 : momentEstimate 2034 430 = 0x6b9d823520 := by
  exact moment_from_blocks [⟨220,0xc87bf9c1⟩, ⟨220,0x4e3f4d3f4⟩, ⟨220,0xae80a0832⟩, ⟨220,0xf6b22dc22⟩, ⟨220,0x11cb25bb92⟩, ⟨220,0x120812a682⟩, ⟨220,0x1021e99cf2⟩, ⟨220,0xc32470568⟩, ⟨220,0x7738b7944⟩, ⟨220,0x3514df015⟩, ⟨220,0xb0b10df9⟩, ⟨44,0xf10757⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment3131_661 : momentEstimate 3131 661 = 0x25ab1ba8825 := by
  exact moment_from_blocks [⟨220,0x13e1c3cbd⟩, ⟨220,0x814fefd91⟩, ⟨220,0x1439c24285⟩, ⟨220,0x2318e1a2fe⟩, ⟨220,0x2fca5f778e⟩, ⟨220,0x39338f9f1e⟩, ⟨220,0x3f547219ae⟩, ⟨220,0x422d06e73e⟩, ⟨220,0x41bd4e07ce⟩, ⟨220,0x3e05477b5e⟩, ⟨220,0x3704f341ee⟩, ⟨220,0x2ced7aaa31⟩, ⟨220,0x218df32002⟩, ⟨220,0x1692e1b9a9⟩, ⟨220,0xcf2dfed74⟩, ⟨220,0x59295cf26⟩, ⟨220,0x12ee8a16e⟩, ⟨52,0x25ca9be⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

end HighCore82219BankProof
