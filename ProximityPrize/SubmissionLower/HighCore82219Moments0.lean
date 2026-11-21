import ProximityPrize.SubmissionLower.HighCore82229LegacyMoments

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
open scoped P1_7_1_3_2
set_option maxHeartbeats 14000000

open private r1A r2A r3A r4A r5A r6A r7A r8A r9A r10A r11A r12A r13A r14A
  r15A r16A r17A r18A r19A r20A r21A r22A r23A r24A r25A
  from ProximityPrize.SubmissionLower.HighCore82229LegacyMoments

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

theorem moment119_26 : momentEstimate 119 26 = 0x5a8245 := r12A

theorem moment130_29 : momentEstimate 130 29 = 0x822d2c := r14A

theorem moment137_30 : momentEstimate 137 30 = 0x9dd5af := r15A

theorem moment141_24 : momentEstimate 141 24 = 0x91e8ba := r16A

theorem moment141_31 : momentEstimate 141 31 = 0xb15384 := r17A

theorem moment149_33 : momentEstimate 149 33 = 0xdda994 := r19A

theorem moment150_33 : momentEstimate 150 33 = 0xe271e9 := r20A

theorem moment173_32 : momentEstimate 173 32 = 0x15c66e5 := r23A

theorem moment197_43 : momentEstimate 197 43 = 0x294fec6 := r24A

theorem moment226_50 : momentEstimate 226 50 = 0x47e88b5 := r25A

theorem moment294_65 : momentEstimate 294 65 = 0xcc1a54f := by
  exact moment_from_blocks [⟨220,0x9b91fd2⟩, ⟨139,0x308857d⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment306_68 : momentEstimate 306 68 = 0xf032b8c := by
  exact moment_from_blocks [⟨220,0xadb2093⟩, ⟨154,0x4280af9⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment341_75 : momentEstimate 341 75 = 0x16e7d3b2 := by
  exact moment_from_blocks [⟨220,0xe2cbd21⟩, ⟨196,0x8bb1691⟩]
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

theorem moment386_85 : momentEstimate 386 85 = 0x25892b87 := by
  exact moment_from_blocks [⟨220,0x12e20d53⟩, ⟨220,0x1296e6bc⟩, ⟨31,0x103778⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment480_101 : momentEstimate 480 101 = 0x564a51c0 := by
  exact moment_from_blocks [⟨220,0x1cff6c77⟩, ⟨220,0x335db15d⟩, ⟨141,0x5ed33ec⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment489_103 : momentEstimate 489 103 = 0x5cfd94a5 := by
  exact moment_from_blocks [⟨220,0x1e1184e2⟩, ⟨220,0x377640d9⟩, ⟨152,0x775ceea⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

theorem moment535_112 : momentEstimate 535 112 = 0x84679137 := (inferInstance : P1_7_1_3_2.ExactMoment 535 112 2221379895).eq_moment

theorem moment572_120 : momentEstimate 572 120 = 0xad1e0c80 := (inferInstance : P1_7_1_3_2.ExactMoment 572 120 2904427648).eq_moment

theorem moment609_128 : momentEstimate 609 128 = 0xde912dc3 := (inferInstance : P1_7_1_3_2.ExactMoment 609 128 3734056387).eq_moment

theorem moment726_153 : momentEstimate 726 153 = 0x1c16ef1c7 := (inferInstance : P1_7_1_3_2.ExactMoment 726 153 7540240839).eq_moment

theorem moment740_167 : momentEstimate 740 167 = 0x1ff6e1863 := (inferInstance : P1_7_1_3_2.ExactMoment 740 167 8580372579).eq_moment

theorem moment792_167 : momentEstimate 792 167 = 0x27c2e15db := (inferInstance : P1_7_1_3_2.ExactMoment 792 167 10673329627).eq_moment

theorem moment883_197 : momentEstimate 883 197 = 0x401d0f0c6 := (inferInstance : P1_7_1_3_2.ExactMoment 883 197 17210339526).eq_moment

theorem moment968_204 : momentEstimate 968 204 = 0x5884788a7 := (inferInstance : P1_7_1_3_2.ExactMoment 968 204 23761225895).eq_moment

theorem moment1072_239 : momentEstimate 1072 239 = 0x8af950b98 := P1_7_1_3_3.moment1072_239

end HighCore82219BankProof
