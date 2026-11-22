-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Moments1.lean.
import ProximityPrize.SubmissionLower.Peer653High53Moments0

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace Peer653High53BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

theorem moment706_149 : momentEstimate 706 149 = 0x19280bd7d := by
  exact moment_from_blocks [⟨220,0x384bf603⟩, ⟨220,0xb5a64cde⟩, ⟨220,0x8d72c644⟩, ⟨195,0x171bb458⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment731_154 : momentEstimate 731 154 = 0x1cdc7da38 := by
  exact moment_from_blocks [⟨220,0x3b43222d⟩, ⟨220,0xc6ac2ddc⟩, ⟨220,0xa7f5f0af⟩, ⟨220,0x23e25ad5⟩, ⟨5,0x3eab⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment831_188 : momentEstimate 831 188 = 0x32de21d13 := by
  exact moment_from_blocks [⟨220,0x474a7a15⟩, ⟨220,0x11bf315da⟩, ⟨220,0x1347f73fe⟩, ⟨220,0x8b961681⟩, ⟨139,0xa8f02a5⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment892_188 : momentEstimate 892 188 = 0x3fe068fa5 := by
  exact moment_from_blocks [⟨220,0x4dcfd3b1⟩, ⟨220,0x13fb42108⟩, ⟨220,0x1797fbf28⟩, ⟨220,0xd68d4243⟩, ⟨200,0x20759981⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment952_201 : momentEstimate 952 201 = 0x52f0bdb9b := by
  exact moment_from_blocks [⟨220,0x546aa258⟩, ⟨220,0x170901a2a⟩, ⟨220,0x1d51604fa⟩, ⟨220,0x140a22796⟩, ⟨220,0x539a13fe⟩, ⟨53,0xbede8b⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment1101_233 : momentEstimate 1101 233 = 0x947787094 := by
  exact moment_from_blocks [⟨220,0x647174b5⟩, ⟨220,0x1ee3f369d⟩, ⟨220,0x2d20f60ca⟩, ⟨220,0x28cdf7050⟩, ⟨220,0x1557edd5f⟩, ⟨220,0x4054f147⟩, ⟨14,0x52582⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment1126_252 : momentEstimate 1126 252 = 0xa99a27482 := by
  exact moment_from_blocks [⟨220,0x671fb271⟩, ⟨220,0x20f4b9f8c⟩, ⟨220,0x31e83e084⟩, ⟨220,0x2ece27f44⟩, ⟨220,0x1abcea3b4⟩, ⟨220,0x6adbc675⟩, ⟨58,0x1265894⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment1202_254 : momentEstimate 1202 254 = 0xd28832ce8 := by
  exact moment_from_blocks [⟨220,0x6f45dec1⟩, ⟨220,0x24499f480⟩, ⟨220,0x38e8625c2⟩, ⟨220,0x395251032⟩, ⟨220,0x267336efb⟩, ⟨220,0xdb1047e8⟩, ⟨136,0xeb46cd0⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

end Peer653High53BankProof
