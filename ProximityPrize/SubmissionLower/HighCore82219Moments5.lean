import ProximityPrize.SubmissionLower.HighCore82219Moment9318
import ProximityPrize.SubmissionLower.HighCore82219Moments4

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)
open P1_7_1_3_2 (moment_from_blocks)
open scoped P1_7_1_3_2
set_option maxHeartbeats 14000000


theorem moment10506_2218 : momentEstimate 10506 2218 = 0x129e297a45c0c := P1_7_1_3_6.moment10506

theorem moment115_25 : momentEstimate 115 25 = 0x4ed4ac := by
  exact moment_from_blocks [⟨140,0x4ed4ac⟩]
    ⟨(by decide +kernel), trivial⟩ rfl rfl

theorem moment127_28 : momentEstimate 127 28 = 0x75b415 := by
  exact moment_from_blocks [⟨155,0x75b415⟩]
    ⟨(by decide +kernel), trivial⟩ rfl rfl

theorem moment161_35 : momentEstimate 161 35 = 0x128bb48 := by
  exact moment_from_blocks [⟨196,0x128bb48⟩]
    ⟨(by decide +kernel), trivial⟩ rfl rfl

theorem moment237_50 : momentEstimate 237 50 = 0x53b7f45 := by
  exact moment_from_blocks [⟨287,0x53b7f45⟩]
    ⟨(by decide +kernel), trivial⟩ rfl rfl

theorem moment1126_252 : momentEstimate 1126 252 = 0xa99a27482 := by
  exact moment_from_blocks [⟨320,0x120cbaff5⟩, ⟨320,0x428c58ec0⟩, ⟨320,0x3ffd66340⟩, ⟨320,0x14af15b58⟩, ⟨98,0x5497735⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment6667_1405 : momentEstimate 6667 1405 = 0x304357eb723c := by
  exact moment_from_blocks [⟨320,0x84005f990⟩, ⟨320,0x36fd858d90⟩, ⟨320,0x8d99132190⟩, ⟨320,0x104bfaeb590⟩, ⟨320,0x193a57dafcf⟩, ⟨320,0x21f0250eba0⟩, ⟨320,0x29552df3ba0⟩, ⟨320,0x2f62f3d8ba0⟩, ⟨320,0x341976bdba0⟩, ⟨320,0x3778b6a2ba0⟩, ⟨320,0x3980b387ba0⟩, ⟨320,0x3a316d6cba0⟩, ⟨320,0x398ae451ba0⟩, ⟨320,0x378d1836ba0⟩, ⟨320,0x3438091bba0⟩, ⟨320,0x2f8bb700ba0⟩, ⟨320,0x298f4ae5403⟩, ⟨320,0x22cf7e3d680⟩, ⟨320,0x1bf8f8a3073⟩, ⟨320,0x155c7b18d94⟩, ⟨320,0xf408d366ed⟩, ⟨320,0x9dd70e67b0⟩, ⟨320,0x57cfce9fb0⟩, ⟨320,0x24f93777b0⟩, ⟨320,0x79d38efb0⟩, ⟨72,0xd145616⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl


end HighCore82219BankProof
