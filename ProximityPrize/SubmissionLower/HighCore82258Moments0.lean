import ProximityPrize.SubmissionLower.HighCore82258Source

set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82258BankProof
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

theorem moment15_3 : momentEstimate 15 3 = 2194 := r1A
theorem moment28_4 : momentEstimate 28 4 = 17031 := r2A
theorem moment29_6 : momentEstimate 29 6 = 24733 := r3A
theorem moment47_10 : momentEstimate 47 10 = 156979 := r4A
theorem moment53_9 : momentEstimate 53 9 = 211909 := r5A
theorem moment75_16 : momentEstimate 75 16 = 957077 := r6A
theorem moment89_15 : momentEstimate 89 15 = 0x17e10a := r7A
theorem moment101_22 : momentEstimate 101 22 = 0x2f6f2a := r8A
theorem moment105_23 : momentEstimate 105 23 = 0x3777f9 := r9A
theorem moment108_24 : momentEstimate 108 24 = 0x3e9e8f := r10A
theorem moment115_25 : momentEstimate 115 25 = 0x4ed4ac := by
  exact moment_from_blocks [⟨140,0x4ed4ac⟩]
    ⟨(by decide +kernel),trivial⟩ rfl rfl

theorem moment119_26 : momentEstimate 119 26 = 0x5a8245 := r12A
theorem moment127_28 : momentEstimate 127 28 = 0x75b415 := by
  exact moment_from_blocks [⟨155,0x75b415⟩]
    ⟨(by decide +kernel),trivial⟩ rfl rfl

theorem moment130_29 : momentEstimate 130 29 = 0x822d2c := r14A
theorem moment137_30 : momentEstimate 137 30 = 0x9dd5af := r15A
theorem moment141_24 : momentEstimate 141 24 = 0x91e8ba := r16A
theorem moment141_31 : momentEstimate 141 31 = 0xb15384 := r17A
theorem moment148_33 : momentEstimate 148 33 = 0xd8f2fa := by
  exact moment_from_blocks [⟨181,0xd8f2fa⟩]
    ⟨(by decide +kernel),trivial⟩ rfl rfl

theorem moment149_33 : momentEstimate 149 33 = 0xdda994 := r19A
theorem moment150_33 : momentEstimate 150 33 = 0xe271e9 := r20A
theorem moment161_35 : momentEstimate 161 35 = 0x128bb48 := by
  exact moment_from_blocks [⟨196,0x128bb48⟩]
    ⟨(by decide +kernel),trivial⟩ rfl rfl

theorem moment173_32 : momentEstimate 173 32 = 0x15c66e5 := r23A
theorem moment175_39 : momentEstimate 175 39 = 0x1a458a5 := by
  exact moment_from_blocks [⟨214,0x1a458a5⟩]
    ⟨(by decide +kernel),trivial⟩ rfl rfl

theorem moment197_43 : momentEstimate 197 43 = 0x294fec6 := r24A
theorem moment226_50 : momentEstimate 226 50 = 0x47e88b5 := r25A
theorem moment237_50 : momentEstimate 237 50 = 0x53b7f45 := by
  exact moment_from_blocks [⟨220,0x4e78e95⟩, ⟨67,0x53f0b0⟩]
    ⟨(by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment247_55 : momentEstimate 247 55 = 0x66c8fdf := by
  exact moment_from_blocks [⟨220,0x5d3001a⟩, ⟨82,0x998fc5⟩]
    ⟨(by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment294_65 : momentEstimate 294 65 = 0xcc1a54f := by
  exact moment_from_blocks [⟨220,0x9b91fd2⟩, ⟨139,0x308857d⟩]
    ⟨(by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment306_68 : momentEstimate 306 68 = 0xf032b8c := by
  exact moment_from_blocks [⟨220,0xadb2093⟩, ⟨154,0x4280af9⟩]
    ⟨(by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment341_75 : momentEstimate 341 75 = 0x16e7d3b2 := by
  exact moment_from_blocks [⟨220,0xe2cbd21⟩, ⟨196,0x8bb1691⟩]
    ⟨(by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment347_78 : momentEstimate 347 78 = 0x18f6d6a4 := by
  exact moment_from_blocks [⟨220,0xef58fc8⟩, ⟨205,0xa0146dc⟩]
    ⟨(by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment362_81 : momentEstimate 362 81 = 0x1d6fb003 := by
  exact moment_from_blocks [⟨220,0x1079a22e⟩, ⟨220,0xcf603f5⟩, ⟨3,0x9e0⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment362_82 : momentEstimate 362 82 = 0x1db6eefa := by
  exact moment_from_blocks [⟨220,0x10953e8c⟩, ⟨220,0xd219e1d⟩, ⟨4,0x1251⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment386_85 : momentEstimate 386 85 = 0x25892b87 := by
  exact moment_from_blocks [⟨220,0x12e20d53⟩, ⟨220,0x1296e6bc⟩, ⟨31,0x103778⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment478_108 : momentEstimate 478 108 = 0x59a98629 := by
  exact moment_from_blocks [⟨220,0x1da4c475⟩, ⟨220,0x3582a95d⟩, ⟨146,0x6821857⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment480_101 : momentEstimate 480 101 = 0x564a51c0 := by
  exact moment_from_blocks [⟨220,0x1cff6c77⟩, ⟨220,0x335db15d⟩, ⟨141,0x5ed33ec⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment489_103 : momentEstimate 489 103 = 0x5cfd94a5 := by
  exact moment_from_blocks [⟨220,0x1e1184e2⟩, ⟨220,0x377640d9⟩, ⟨152,0x775ceea⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment522_118 : momentEstimate 522 118 = 0x7f6275d9 := by
  exact moment_from_blocks [⟨220,0x22e6fe09⟩, ⟨220,0x4b56fe51⟩, ⟨200,0x1124797f⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment535_112 : momentEstimate 535 112 = 0x84679137 := by
  exact moment_from_blocks [⟨220,0x2377d012⟩, ⟨220,0x4d9e6502⟩, ⟨207,0x13515c23⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment572_120 : momentEstimate 572 120 = 0xad1e0c80 := by
  exact moment_from_blocks [⟨220,0x27f8a832⟩, ⟨220,0x61ae3614⟩, ⟨220,0x235c906a⟩, ⟨32,0x1a9dd0⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment606_128 : momentEstimate 606 128 = 0xdb115372 := by
  exact moment_from_blocks [⟨220,0x2c330aa8⟩, ⟨220,0x75d346e8⟩, ⟨220,0x37d21840⟩, ⟨74,0x138e9a2⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment608_128 : momentEstimate 608 128 = 0xdd657d32 := by
  exact moment_from_blocks [⟨220,0x2c65fb14⟩, ⟨220,0x76ba16f4⟩, ⟨220,0x38f25711⟩, ⟨76,0x1531419⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment609_128 : momentEstimate 609 128 = 0xde912dc3 := by
  exact moment_from_blocks [⟨220,0x2c7f734a⟩, ⟨220,0x772d7efa⟩, ⟨220,0x3983871d⟩, ⟨77,0x160b462⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment686_144 : momentEstimate 686 144 = 0x1656b0db4 := by
  exact moment_from_blocks [⟨220,0x35d3f27c⟩, ⟨220,0xa78ddb58⟩, ⟨220,0x78d8f705⟩, ⟨170,0xf3048db⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment692_155 : momentEstimate 692 155 = 0x185234383 := by
  exact moment_from_blocks [⟨220,0x374148e9⟩, ⟨220,0xb35c0374⟩, ⟨220,0x866e2306⟩, ⟨187,0x1417d420⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl


end HighCore82258BankProof
