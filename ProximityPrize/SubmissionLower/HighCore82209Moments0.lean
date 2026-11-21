import ProximityPrize.SubmissionLower.HighCore82209Source

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82209BankProof

open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
open scoped P1_7_1_3_2
set_option maxHeartbeats 14000000

open private r1A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r2A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r3A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r4A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r5A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r6A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r7A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r8A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r9A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r10A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r11A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r12A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r13A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r14A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r15A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r16A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r17A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r18A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r19A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r20A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r21A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r22A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r23A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r24A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r25A from ProximityPrize.SubmissionLower.GoldBranch7N1

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

theorem moment111_24 : momentEstimate 111 24 = 0x4451ef := r11A

theorem moment119_26 : momentEstimate 119 26 = 0x5a8245 := r12A

theorem moment123_27 : momentEstimate 123 27 = 0x67700d := rfl

theorem moment125_27 : momentEstimate 125 27 = 0x6ce383 := r13A

theorem moment130_29 : momentEstimate 130 29 = 0x822d2c := r14A

theorem moment134_30 : momentEstimate 134 30 = 0x931387 := rfl

theorem moment137_30 : momentEstimate 137 30 = 0x9dd5af := r15A

theorem moment141_24 : momentEstimate 141 24 = 0x91e8ba := r16A

theorem moment141_31 : momentEstimate 141 31 = 0xb15384 := r17A

theorem moment147_32 : momentEstimate 147 32 = 0xcf7010 := r18A

theorem moment149_33 : momentEstimate 149 33 = 0xdda994 := r19A

theorem moment150_33 : momentEstimate 150 33 = 0xe271e9 := r20A

theorem moment158_34 : momentEstimate 158 34 = 0x11160fc := r21A

theorem moment159_35 : momentEstimate 159 35 = 0x11d1f9e := r22A

theorem moment160_34 : momentEstimate 160 34 = 0x11c9279 := rfl

theorem moment173_32 : momentEstimate 173 32 = 0x15c66e5 := r23A

theorem moment197_43 : momentEstimate 197 43 = 0x294fec6 := r24A

theorem moment226_50 : momentEstimate 226 50 = 0x47e88b5 := r25A

theorem moment235_50 : momentEstimate 235 50 = 0x517adc3 := by
  exact moment_from_blocks [⟨220,0x4cb36f8⟩, ⟨65,0x4c76cb⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment270_60 : momentEstimate 270 60 = 0x921d91e := by
  exact moment_from_blocks [⟨220,0x7a85c99⟩, ⟨110,0x1797c85⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment294_65 : momentEstimate 294 65 = 0xcc1a54f := by
  exact moment_from_blocks [⟨220,0x9b91fd2⟩, ⟨139,0x308857d⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment296_66 : momentEstimate 296 66 = 0xd30a80f := by
  exact moment_from_blocks [⟨220,0x9f464f2⟩, ⟨142,0x33c431d⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment299_66 : momentEstimate 299 66 = 0xd9f9f46 := by
  exact moment_from_blocks [⟨220,0xa2ae13f⟩, ⟨145,0x374be07⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment306_68 : momentEstimate 306 68 = 0xf032b8c := by
  exact moment_from_blocks [⟨220,0xadb2093⟩, ⟨154,0x4280af9⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment324_73 : momentEstimate 324 73 = 0x130a6f27 := by
  exact moment_from_blocks [⟨220,0xcac1258⟩, ⟨177,0x65e5ccf⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment327_73 : momentEstimate 327 73 = 0x139cbdb4 := by
  exact moment_from_blocks [⟨220,0xce62fd0⟩, ⟨180,0x6b68de4⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment341_75 : momentEstimate 341 75 = 0x16e7d3b2 := by
  exact moment_from_blocks [⟨220,0xe2cbd21⟩, ⟨196,0x8bb1691⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment347_75 : momentEstimate 347 75 = 0x18392b4c := by
  exact moment_from_blocks [⟨220,0xea2eba9⟩, ⟨202,0x9963fa3⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment359_81 : momentEstimate 359 81 = 0x1ca909eb := by
  exact moment_from_blocks [⟨220,0x103bc5ee⟩, ⟨220,0xc6d43fd⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment362_81 : momentEstimate 362 81 = 0x1d6fb003 := by
  exact moment_from_blocks [⟨220,0x1079a22e⟩, ⟨220,0xcf603f5⟩, ⟨3,2528⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment362_82 : momentEstimate 362 82 = 0x1db6eefa := by
  exact moment_from_blocks [⟨220,0x10953e8c⟩, ⟨220,0xd219e1d⟩, ⟨4,4689⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment385_84 : momentEstimate 385 84 = 0x24e31c52 := by
  exact moment_from_blocks [⟨220,0x12af598f⟩, ⟨220,0x12265cdf⟩, ⟨29,878052⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment386_85 : momentEstimate 386 85 = 0x25892b87 := by
  exact moment_from_blocks [⟨220,0x12e20d53⟩, ⟨220,0x1296e6bc⟩, ⟨31,0x103778⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment480_101 : momentEstimate 480 101 = 0x564a51c0 := by
  exact moment_from_blocks [⟨220,0x1cff6c77⟩, ⟨220,0x335db15d⟩, ⟨141,0x5ed33ec⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment485_102 : momentEstimate 485 102 = 0x59e3ed8b := by
  exact moment_from_blocks [⟨220,0x1d93ebb8⟩, ⟨220,0x3593f298⟩, ⟨147,0x6bc0f3b⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment489_103 : momentEstimate 489 103 = 0x5cfd94a5 := by
  exact moment_from_blocks [⟨220,0x1e1184e2⟩, ⟨220,0x377640d9⟩, ⟨152,0x775ceea⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment495_104 : momentEstimate 495 104 = 0x616d5567 := by
  exact moment_from_blocks [⟨220,0x1ebe53fc⟩, ⟨220,0x3a1d2877⟩, ⟨159,0x891d8f4⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment498_104 : momentEstimate 498 104 = 0x6355595b := by
  exact moment_from_blocks [⟨220,0x1f04c4ea⟩, ⟨220,0x3b3aa7e8⟩, ⟨162,0x915ec89⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment499_105 : momentEstimate 499 105 = 0x64b8343e := by
  exact moment_from_blocks [⟨220,0x1f3c9d48⟩, ⟨220,0x3c0f771b⟩, ⟨164,0x96c1fdb⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment535_112 : momentEstimate 535 112 = 0x84679137 := (inferInstance : P1_7_1_3_2.ExactMoment 535 112 2221379895).eq_moment

theorem moment543_114 : momentEstimate 543 114 = 0x8cc85625 := by
  exact moment_from_blocks [⟨220,0x24788777⟩, ⟨220,0x51f9c5b2⟩, ⟨217,0x165608fc⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment565_119 : momentEstimate 565 119 = 0xa5555e6d := by
  exact moment_from_blocks [⟨220,0x272d1ae6⟩, ⟨220,0x5e143828⟩, ⟨220,0x20086329⟩, ⟨24,763958⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment572_120 : momentEstimate 572 120 = 0xad1e0c80 := (inferInstance : P1_7_1_3_2.ExactMoment 572 120 2904427648).eq_moment

theorem moment591_125 : momentEstimate 591 125 = 0xc672a1cc := by
  exact moment_from_blocks [⟨220,0x2a646c05⟩, ⟨220,0x6d20e136⟩, ⟨220,0x2e64b90f⟩, ⟨56,0x889b82⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment593_135 : momentEstimate 593 135 = 0xd4e9369b := by
  exact moment_from_blocks [⟨220,0x2b9099aa⟩, ⟨220,0x74654dd8⟩, ⟨220,0x3403966d⟩, ⟨68,0xefb8ac⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment596_126 : momentEstimate 596 126 = 0xcd26d8f5 := by
  exact moment_from_blocks [⟨220,0x2afe9109⟩, ⟨220,0x7001134e⟩, ⟨220,0x316e7c86⟩, ⟨62,0xb8b818⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment609_128 : momentEstimate 609 128 = 0xde912dc3 := (inferInstance : P1_7_1_3_2.ExactMoment 609 128 3734056387).eq_moment

theorem moment615_137 : momentEstimate 615 137 = 0xf2191e37 := by
  exact moment_from_blocks [⟨220,0x2df7bc00⟩, ⟨220,0x800fa4da⟩, ⟨220,0x41bec627⟩, ⟨92,0x252f736⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment640_135 : momentEstimate 640 135 = 0x1100a07c3 := by
  exact moment_from_blocks [⟨220,0x305156d2⟩, ⟨220,0x8a70a1b8⟩, ⟨220,0x50ac7f0f⟩, ⟨115,0x49b902a⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment671_142 : momentEstimate 671 142 = 0x14954ceae := by
  exact moment_from_blocks [⟨220,0x341dc6ac⟩, ⟨220,0x9e9cca68⟩, ⟨220,0x6b9da33b⟩, ⟨153,0xafc9a5f⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment716_150 : momentEstimate 716 150 = 0x1a74a03e8 := by
  exact moment_from_blocks [⟨220,0x39691313⟩, ⟨220,0xbb8c0396⟩, ⟨220,0x96f209fa⟩, ⟨206,0x1b62e345⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment724_153 : momentEstimate 724 153 = 0x1bd78704c := by
  exact moment_from_blocks [⟨220,0x3a7655a4⟩, ⟨220,0xc234a95a⟩, ⟨220,0xa0b79b34⟩, ⟨217,0x2015d61a⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment726_153 : momentEstimate 726 153 = 0x1c16ef1c7 := (inferInstance : P1_7_1_3_2.ExactMoment 726 153 7540240839).eq_moment

theorem moment740_167 : momentEstimate 740 167 = 0x1ff6e1863 := (inferInstance : P1_7_1_3_2.ExactMoment 740 167 8580372579).eq_moment

theorem moment792_167 : momentEstimate 792 167 = 0x27c2e15db := (inferInstance : P1_7_1_3_2.ExactMoment 792 167 10673329627).eq_moment

theorem moment806_170 : momentEstimate 806 170 = 0x2aa645c9f := by
  exact moment_from_blocks [⟨220,0x44117832⟩, ⟨220,0xfd43e416⟩, ⟨220,0x102ba3dec⟩, ⟨220,0x62d3416b⟩, ⟨96,0x3818100⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment813_172 : momentEstimate 813 172 = 0x2c405b86b := by
  exact moment_from_blocks [⟨220,0x44e5bc21⟩, ⟨220,0x103076e5e⟩, ⟨220,0x10c878fd6⟩, ⟨220,0x6afafe0e⟩, ⟨105,0x4960008⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment846_188 : momentEstimate 846 188 = 0x35e195e5b := by
  exact moment_from_blocks [⟨220,0x48e4f909⟩, ⟨220,0x124bdd574⟩, ⟨220,0x14574b80c⟩, ⟨220,0x9c8b3a02⟩, ⟨154,0xe769dd0⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment883_197 : momentEstimate 883 197 = 0x401d0f0c6 := (inferInstance : P1_7_1_3_2.ExactMoment 883 197 17210339526).eq_moment

theorem moment926_195 : momentEstimate 926 195 = 0x4a1c95ad2 := (inferInstance : P1_7_1_3_2.ExactMoment 926 195 19894196946).eq_moment

theorem moment942_212 : momentEstimate 942 212 = 0x538e63a35 := by
  exact moment_from_blocks [⟨220,0x53640897⟩, ⟨220,0x174ccc78c⟩, ⟨220,0x1dc082c0c⟩, ⟨220,0x1406330e2⟩, ⟨220,0x5382c0d9⟩, ⟨54,0xc74c4b⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment944_199 : momentEstimate 944 199 = 0x5018948c9 := by
  exact moment_from_blocks [⟨220,0x538ab6a2⟩, ⟨220,0x169b32378⟩, ⟨220,0x1c808eb38⟩, ⟨220,0x1310a5186⟩, ⟨220,0x4ad0b19b⟩, ⟨43,0x678056⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment968_204 : momentEstimate 968 204 = 0x5884788a7 := (inferInstance : P1_7_1_3_2.ExactMoment 968 204 23761225895).eq_moment

theorem moment1072_239 : momentEstimate 1072 239 = 0x8af950b98 := P1_7_1_3_3.moment1072_239

theorem moment1076_242 : momentEstimate 1076 242 = 0x8e03abac2 := by
  exact moment_from_blocks [⟨220,0x61c336f9⟩, ⟨220,0x1e5932313⟩, ⟨220,0x2c3b57d52⟩, ⟨220,0x26dcdda3c⟩, ⟨220,0x13431265a⟩, ⟨218,0x332fe2ce⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

end HighCore82209BankProof
