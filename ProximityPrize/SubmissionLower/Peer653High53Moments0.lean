-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Moments0.lean.
import ProximityPrize.SubmissionLower.Peer653High53Source

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace Peer653High53BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

open private r10A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r12A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r14A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r15A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r16A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r17A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r19A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r1A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r20A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r23A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r24A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r25A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r2A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r3A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r4A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r5A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r6A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r7A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r8A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r9A from ProximityPrize.SubmissionLower.GoldBranch7N1

theorem moment105_23 : momentEstimate 105 23 = 0x3777f9 := r9A
theorem moment115_25 : momentEstimate 115 25 = 0x4ed4ac := by
  exact moment_from_blocks [⟨140,0x4ed4ac⟩]
    ⟨(by decide +kernel),trivial⟩ rfl rfl

theorem moment127_28 : momentEstimate 127 28 = 0x75b415 := by
  exact moment_from_blocks [⟨155,0x75b415⟩]
    ⟨(by decide +kernel),trivial⟩ rfl rfl

theorem moment137_30 : momentEstimate 137 30 = 0x9dd5af := r15A
theorem moment148_33 : momentEstimate 148 33 = 0xd8f2fa := by
  exact moment_from_blocks [⟨181,0xd8f2fa⟩]
    ⟨(by decide +kernel),trivial⟩ rfl rfl

theorem moment161_35 : momentEstimate 161 35 = 0x128bb48 := by
  exact moment_from_blocks [⟨196,0x128bb48⟩]
    ⟨(by decide +kernel),trivial⟩ rfl rfl

theorem moment175_39 : momentEstimate 175 39 = 0x1a458a5 := by
  exact moment_from_blocks [⟨214,0x1a458a5⟩]
    ⟨(by decide +kernel),trivial⟩ rfl rfl

theorem moment197_43 : momentEstimate 197 43 = 0x294fec6 := r24A
theorem moment237_50 : momentEstimate 237 50 = 0x53b7f45 := by
  exact moment_from_blocks [⟨220,0x4e78e95⟩, ⟨67,0x53f0b0⟩]
    ⟨(by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment247_55 : momentEstimate 247 55 = 0x66c8fdf := by
  exact moment_from_blocks [⟨220,0x5d3001a⟩, ⟨82,0x998fc5⟩]
    ⟨(by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment347_78 : momentEstimate 347 78 = 0x18f6d6a4 := by
  exact moment_from_blocks [⟨220,0xef58fc8⟩, ⟨205,0xa0146dc⟩]
    ⟨(by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment362_81 : momentEstimate 362 81 = 0x1d6fb003 := by
  exact moment_from_blocks [⟨220,0x1079a22e⟩, ⟨220,0xcf603f5⟩, ⟨3,0x9e0⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment478_108 : momentEstimate 478 108 = 0x59a98629 := by
  exact moment_from_blocks [⟨220,0x1da4c475⟩, ⟨220,0x3582a95d⟩, ⟨146,0x6821857⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment522_118 : momentEstimate 522 118 = 0x7f6275d9 := by
  exact moment_from_blocks [⟨220,0x22e6fe09⟩, ⟨220,0x4b56fe51⟩, ⟨200,0x1124797f⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment606_128 : momentEstimate 606 128 = 0xdb115372 := by
  exact moment_from_blocks [⟨220,0x2c330aa8⟩, ⟨220,0x75d346e8⟩, ⟨220,0x37d21840⟩, ⟨74,0x138e9a2⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment608_128 : momentEstimate 608 128 = 0xdd657d32 := by
  exact moment_from_blocks [⟨220,0x2c65fb14⟩, ⟨220,0x76ba16f4⟩, ⟨220,0x38f25711⟩, ⟨76,0x1531419⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment686_144 : momentEstimate 686 144 = 0x1656b0db4 := by
  exact moment_from_blocks [⟨220,0x35d3f27c⟩, ⟨220,0xa78ddb58⟩, ⟨220,0x78d8f705⟩, ⟨170,0xf3048db⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment692_155 : momentEstimate 692 155 = 0x185234383 := by
  exact moment_from_blocks [⟨220,0x374148e9⟩, ⟨220,0xb35c0374⟩, ⟨220,0x866e2306⟩, ⟨187,0x1417d420⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl


end Peer653High53BankProof
