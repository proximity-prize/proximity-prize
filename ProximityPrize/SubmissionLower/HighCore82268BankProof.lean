import ProximityPrize.SubmissionLower.HighCore82268Source
import ProximityPrize.SubmissionLower.HighCore82268BankMoments

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82268BankProof

open P3_7_1 (BankOK checked)
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)
open HighCore82268

set_option maxHeartbeats 4000000
open private r1A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r2A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r3A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r4A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r5A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r6A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r7A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r8A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r10A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r12A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r14A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r16A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r17A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r19A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r20A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r23A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r24A from ProximityPrize.SubmissionLower.GoldBranch7N1
open private r25A from ProximityPrize.SubmissionLower.GoldBranch7N1

private theorem moment15_3 : momentEstimate 15 3 = 2194  := r1A

private theorem moment28_4 : momentEstimate 28 4 = 17031  := r2A

private theorem moment29_6 : momentEstimate 29 6 = 24733  := r3A

private theorem moment47_10 : momentEstimate 47 10 = 156979  := r4A

private theorem moment53_9 : momentEstimate 53 9 = 211909  := r5A

private theorem moment75_16 : momentEstimate 75 16 = 957077  := r6A

private theorem moment89_15 : momentEstimate 89 15 = 0x17e10a  := r7A

private theorem moment101_22 : momentEstimate 101 22 = 0x2f6f2a  := r8A

private theorem moment108_24 : momentEstimate 108 24 = 0x3e9e8f  := r10A

private theorem moment119_26 : momentEstimate 119 26 = 0x5a8245  := r12A

private theorem moment130_29 : momentEstimate 130 29 = 0x822d2c  := r14A

private theorem moment141_24 : momentEstimate 141 24 = 0x91e8ba  := r16A

private theorem moment141_31 : momentEstimate 141 31 = 0xb15384  := r17A

private theorem moment149_33 : momentEstimate 149 33 = 0xdda994  := r19A

private theorem moment150_33 : momentEstimate 150 33 = 0xe271e9  := r20A

private theorem moment173_32 : momentEstimate 173 32 = 0x15c66e5  := r23A

private theorem moment197_43 : momentEstimate 197 43 = 0x294fec6  := r24A

private theorem moment226_50 : momentEstimate 226 50 = 0x47e88b5  := r25A

private theorem moment294_65 : momentEstimate 294 65 = 0xcc1a54f := by
  exact moment_from_blocks [⟨220,0x9b91fd2⟩, ⟨139,0x308857d⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment306_68 : momentEstimate 306 68 = 0xf032b8c := by
  exact moment_from_blocks [⟨220,0xadb2093⟩, ⟨154,0x4280af9⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment341_75 : momentEstimate 341 75 = 0x16e7d3b2 := by
  exact moment_from_blocks [⟨220,0xe2cbd21⟩, ⟨196,0x8bb1691⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment362_82 : momentEstimate 362 82 = 0x1db6eefa := by
  exact moment_from_blocks [⟨220,0x10953e8c⟩, ⟨220,0xd219e1d⟩, ⟨4,4689⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment386_85 : momentEstimate 386 85 = 0x25892b87 := by
  exact moment_from_blocks [⟨220,0x12e20d53⟩, ⟨220,0x1296e6bc⟩, ⟨31,0x103778⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment480_101 : momentEstimate 480 101 = 0x564a51c0 := by
  exact moment_from_blocks [⟨220,0x1cff6c77⟩, ⟨220,0x335db15d⟩, ⟨141,0x5ed33ec⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment489_103 : momentEstimate 489 103 = 0x5cfd94a5 := by
  exact moment_from_blocks [⟨220,0x1e1184e2⟩, ⟨220,0x377640d9⟩, ⟨152,0x775ceea⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment535_112 : momentEstimate 535 112 = 0x84679137 := by
  exact moment_from_blocks [⟨220,0x2377d012⟩, ⟨220,0x4d9e6502⟩, ⟨207,0x13515c23⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment572_120 : momentEstimate 572 120 = 0xad1e0c80 := by
  exact moment_from_blocks [⟨220,0x27f8a832⟩, ⟨220,0x61ae3614⟩, ⟨220,0x235c906a⟩, ⟨32,0x1a9dd0⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment609_128 : momentEstimate 609 128 = 0xde912dc3 := by
  exact moment_from_blocks [⟨220,0x2c7f734a⟩, ⟨220,0x772d7efa⟩, ⟨220,0x3983871d⟩, ⟨77,0x160b462⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment726_153 : momentEstimate 726 153 = 0x1c16ef1c7 := by
  exact moment_from_blocks [⟨220,0x3aabb454⟩, ⟨220,0xc33b47fa⟩, ⟨220,0xa282e542⟩, ⟨219,0x21051037⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment740_167 : momentEstimate 740 167 = 0x1ff6e1863 := by
  exact moment_from_blocks [⟨220,0x3cf21eda⟩, ⟨220,0xd67bc218⟩, ⟨220,0xbcc3ee24⟩, ⟨220,0x2f26e723⟩, ⟨27,0x15622a⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment792_167 : momentEstimate 792 167 = 0x27c2e15db := by
  exact moment_from_blocks [⟨220,0x4271d23a⟩, ⟨220,0xf2c75298⟩, ⟨220,0xf0b537ce⟩, ⟨220,0x544aa0d7⟩, ⟨79,0x1f51864⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment883_197 : momentEstimate 883 197 = 0x401d0f0c6 := by
  exact moment_from_blocks [⟨220,0x4cfcc39b⟩, ⟨220,0x142ef2dae⟩, ⟨220,0x17ce952be⟩, ⟨220,0xd4e276cc⟩, ⟨200,0x201935f3⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment968_204 : momentEstimate 968 204 = 0x5884788a7 := by
  exact moment_from_blocks [⟨220,0x5626d855⟩, ⟨220,0x17d5abee0⟩, ⟨220,0x1edb84f40⟩, ⟨220,0x15f411d92⟩, ⟨220,0x65f4a3ac⟩, ⟨72,0x1d7e0f4⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1072_239 : momentEstimate 1072 239 = 0x8af950b98 := P1_7_1_3_3.moment1072_239

private theorem moment1183_249 : momentEstimate 1183 249 = 0xc4f2a7606 := P1_7_1_3_3.moment1183_249

private theorem moment1324_279 : momentEstimate 1324 279 = 0x1350bb1fb5 := P1_7_1_3_3.moment1324_279

private theorem moment1443_329 : momentEstimate 1443 329 = 0x1cf53a5560 := P1_7_1_3_3.moment1443_329

private theorem moment1550_329 : momentEstimate 1550 329 = 0x2473d5ffe4 := P1_7_1_3_3.moment1550_329

private theorem moment1696_357 : momentEstimate 1696 357 = 0x33e3754396 := P1_7_1_3_3.moment1696_357

private theorem moment1725_359 : momentEstimate 1725 359 = 0x370899d961 := P1_7_1_3_3.moment1725_359

private theorem moment2034_430 : momentEstimate 2034 430 = 0x6b9d823520 := by
  exact moment_from_blocks [⟨220,0xc87bf9c1⟩, ⟨220,0x4e3f4d3f4⟩, ⟨220,0xae80a0832⟩, ⟨220,0xf6b22dc22⟩, ⟨220,0x11cb25bb92⟩, ⟨220,0x120812a682⟩, ⟨220,0x1021e99cf2⟩, ⟨220,0xc32470568⟩, ⟨220,0x7738b7944⟩, ⟨220,0x3514df015⟩, ⟨220,0xb0b10df9⟩, ⟨44,0xf10757⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment3131_661 : momentEstimate 3131 661 = 0x25ab1ba8825 := by
  exact moment_from_blocks [⟨220,0x13e1c3cbd⟩, ⟨220,0x814fefd91⟩, ⟨220,0x1439c24285⟩, ⟨220,0x2318e1a2fe⟩, ⟨220,0x2fca5f778e⟩, ⟨220,0x39338f9f1e⟩, ⟨220,0x3f547219ae⟩, ⟨220,0x422d06e73e⟩, ⟨220,0x41bd4e07ce⟩, ⟨220,0x3e05477b5e⟩, ⟨220,0x3704f341ee⟩, ⟨220,0x2ced7aaa31⟩, ⟨220,0x218df32002⟩, ⟨220,0x1692e1b9a9⟩, ⟨220,0xcf2dfed74⟩, ⟨220,0x59295cf26⟩, ⟨220,0x12ee8a16e⟩, ⟨52,0x25ca9be⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment4830_1019 : momentEstimate 4830 1019 = 0xd5013df2ef9 := P1_7_1_3_5.moment4830

private theorem moment5798_1223 : momentEstimate 5798 1223 = 0x1ba1a89b2ba1 := P1_7_1_3_5.moment5798

private theorem moment7630_1607 : momentEstimate 7630 1607 = 0x52bdbe618ec3 := P1_7_1_3_5.moment7630

private theorem moment10506_2218 : momentEstimate 10506 2218 = 0x129e297a45c0c := P1_7_1_3_6.moment10506

private theorem moment97_21 : momentEstimate 97 21 = 0x284e2c := rfl

private theorem moment111_24 : momentEstimate 111 24 = 0x4451ef := rfl

private theorem moment115_25 : momentEstimate 115 25 = 0x4ed4ac := rfl

private theorem moment123_27 : momentEstimate 123 27 = 0x67700d := rfl

private theorem moment126_27 : momentEstimate 126 27 = 0x6fafa5 := rfl

private theorem moment134_30 : momentEstimate 134 30 = 0x931387 := rfl

private theorem moment147_32 : momentEstimate 147 32 = 0xcf7010 := rfl

private theorem moment159_35 : momentEstimate 159 35 = 0x11d1f9e := rfl

private theorem moment160_34 : momentEstimate 160 34 = 0x11c9279 := rfl

private theorem moment166_37 : momentEstimate 166 37 = 0x1553865 := rfl

private theorem moment235_50 : momentEstimate 235 50 = 0x517adc3 := by
  exact moment_from_blocks [⟨220,0x4cb36f8⟩, ⟨65,0x4c76cb⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment286_64 : momentEstimate 286 64 = 0xb89ee2e := by
  exact moment_from_blocks [⟨220,0x91374d8⟩, ⟨130,0x2767956⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment287_64 : momentEstimate 287 64 = 0xbab2d1e := by
  exact moment_from_blocks [⟨220,0x925406e⟩, ⟨131,0x285ecb0⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment296_66 : momentEstimate 296 66 = 0xd30a80f := by
  exact moment_from_blocks [⟨220,0x9f464f2⟩, ⟨142,0x33c431d⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment299_66 : momentEstimate 299 66 = 0xd9f9f46 := by
  exact moment_from_blocks [⟨220,0xa2ae13f⟩, ⟨145,0x374be07⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment359_79 : momentEstimate 359 79 = 0x1c1d91ae := by
  exact moment_from_blocks [⟨220,0x10041874⟩, ⟨218,0xc19793a⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment359_81 : momentEstimate 359 81 = 0x1ca909eb := by
  exact moment_from_blocks [⟨220,0x103bc5ee⟩, ⟨220,0xc6d43fd⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment362_80 : momentEstimate 362 80 = 0x1d282567 := by
  exact moment_from_blocks [⟨220,0x105d92b4⟩, ⟨220,0xcca8e76⟩, ⟨2,1085⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment362_81 : momentEstimate 362 81 = 0x1d6fb003 := by
  exact moment_from_blocks [⟨220,0x1079a22e⟩, ⟨220,0xcf603f5⟩, ⟨3,2528⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment385_83 : momentEstimate 385 83 = 0x248c5e25 := by
  exact moment_from_blocks [⟨220,0x12915b23⟩, ⟨220,0x11eee036⟩, ⟨28,795340⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment385_84 : momentEstimate 385 84 = 0x24e31c52 := by
  exact moment_from_blocks [⟨220,0x12af598f⟩, ⟨220,0x12265cdf⟩, ⟨29,878052⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment473_99 : momentEstimate 473 99 = 0x510d7a50 := by
  exact moment_from_blocks [⟨220,0x1c1cc877⟩, ⟨220,0x3017b8a5⟩, ⟨132,0x4d8f934⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment485_102 : momentEstimate 485 102 = 0x59e3ed8b := by
  exact moment_from_blocks [⟨220,0x1d93ebb8⟩, ⟨220,0x3593f298⟩, ⟨147,0x6bc0f3b⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment498_104 : momentEstimate 498 104 = 0x6355595b := by
  exact moment_from_blocks [⟨220,0x1f04c4ea⟩, ⟨220,0x3b3aa7e8⟩, ⟨162,0x915ec89⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment565_119 : momentEstimate 565 119 = 0xa5555e6d := by
  exact moment_from_blocks [⟨220,0x272d1ae6⟩, ⟨220,0x5e143828⟩, ⟨220,0x20086329⟩, ⟨24,763958⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment591_125 : momentEstimate 591 125 = 0xc672a1cc := by
  exact moment_from_blocks [⟨220,0x2a646c05⟩, ⟨220,0x6d20e136⟩, ⟨220,0x2e64b90f⟩, ⟨56,0x889b82⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment593_135 : momentEstimate 593 135 = 0xd4e9369b := by
  exact moment_from_blocks [⟨220,0x2b9099aa⟩, ⟨220,0x74654dd8⟩, ⟨220,0x3403966d⟩, ⟨68,0xefb8ac⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment603_127 : momentEstimate 603 127 = 0xd64bfbb8 := by
  exact moment_from_blocks [⟨220,0x2bcb9620⟩, ⟨220,0x73ccad80⟩, ⟨220,0x35aa7c25⟩, ⟨70,0x1093bf3⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment606_127 : momentEstimate 606 127 = 0xd9bc9eb8 := by
  exact moment_from_blocks [⟨220,0x2c17cca0⟩, ⟨220,0x7524db80⟩, ⟨220,0x37531355⟩, ⟨73,0x12ce343⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment611_140 : momentEstimate 611 140 = 0xf10fe4d6 := by
  exact moment_from_blocks [⟨220,0x2dcf67e1⟩, ⟨220,0x80206c02⟩, ⟨220,0x40e38a9e⟩, ⟨91,0x23c8655⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment640_135 : momentEstimate 640 135 = 0x1100a07c3 := by
  exact moment_from_blocks [⟨220,0x305156d2⟩, ⟨220,0x8a70a1b8⟩, ⟨220,0x50ac7f0f⟩, ⟨115,0x49b902a⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment716_150 : momentEstimate 716 150 = 0x1a74a03e8 := by
  exact moment_from_blocks [⟨220,0x39691313⟩, ⟨220,0xbb8c0396⟩, ⟨220,0x96f209fa⟩, ⟨206,0x1b62e345⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment756_157 : momentEstimate 756 157 = 0x20a3388b0 := by
  exact moment_from_blocks [⟨220,0x3e143d49⟩, ⟨220,0xd652a176⟩, ⟨220,0xc22bcf64⟩, ⟨220,0x337a357d⟩, ⟨33,0x26a510⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment806_170 : momentEstimate 806 170 = 0x2aa645c9f := by
  exact moment_from_blocks [⟨220,0x44117832⟩, ⟨220,0xfd43e416⟩, ⟨220,0x102ba3dec⟩, ⟨220,0x62d3416b⟩, ⟨96,0x3818100⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment831_187 : momentEstimate 831 187 = 0x32a898a11 := by
  exact moment_from_blocks [⟨220,0x47457685⟩, ⟨220,0x11b10b9c4⟩, ⟨220,0x13335ec44⟩, ⟨220,0x8aa61c2d⟩, ⟨138,0xa575157⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment834_175 : momentEstimate 834 175 = 0x30adbb088 := by
  exact moment_from_blocks [⟨220,0x473f757c⟩, ⟨220,0x1119fcdd0⟩, ⟨220,0x126b1fe50⟩, ⟨220,0x82bec87a⟩, ⟨129,0x88ba672⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment846_188 : momentEstimate 846 188 = 0x35e195e5b := by
  exact moment_from_blocks [⟨220,0x48e4f909⟩, ⟨220,0x124bdd574⟩, ⟨220,0x14574b80c⟩, ⟨220,0x9c8b3a02⟩, ⟨154,0xe769dd0⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment944_199 : momentEstimate 944 199 = 0x5018948c9 := by
  exact moment_from_blocks [⟨220,0x538ab6a2⟩, ⟨220,0x169b32378⟩, ⟨220,0x1c808eb38⟩, ⟨220,0x1310a5186⟩, ⟨220,0x4ad0b19b⟩, ⟨43,0x678056⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1018_214 : momentEstimate 1018 214 = 0x6c03bb2c1 := by
  exact moment_from_blocks [⟨220,0x5b8ab541⟩, ⟨220,0x1a676523a⟩, ⟨220,0x23e6c256a⟩, ⟨220,0x1c6f8c1ec⟩, ⟨220,0xad875faf⟩, ⟨132,0xb4e6441⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1076_242 : momentEstimate 1076 242 = 0x8e03abac2 := by
  exact moment_from_blocks [⟨220,0x61c336f9⟩, ⟨220,0x1e5932313⟩, ⟨220,0x2c3b57d52⟩, ⟨220,0x26dcdda3c⟩, ⟨220,0x13431265a⟩, ⟨218,0x332fe2ce⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1126_236 : momentEstimate 1126 236 = 0xa12bddaf7 := by
  exact moment_from_blocks [⟨220,0x671fb271⟩, ⟨220,0x20183ab78⟩, ⟨220,0x2fa5969f4⟩, ⟨220,0x2c6631834⟩, ⟨220,0x18e2ff285⟩, ⟨220,0x5aba4753⟩, ⟨42,0x73c10e⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1220_273 : momentEstimate 1220 273 = 0xe993089da := by
  exact moment_from_blocks [⟨220,0x7133f6b9⟩, ⟨220,0x25fadb9c7⟩, ⟨220,0x3d6deaf92⟩, ⟨220,0x3f3b8ada2⟩, ⟨220,0x2c3dbae0e⟩, ⟨220,0x11bc8a76e⟩, ⟨173,0x1e1326aa⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1233_260 : momentEstimate 1233 260 = 0xe8ae039a1 := by
  exact moment_from_blocks [⟨220,0x7298cf25⟩, ⟨220,0x25ed3506c⟩, ⟨220,0x3c9dccffe⟩, ⟨220,0x3ea3d486e⟩, ⟨220,0x2c814c42a⟩, ⟨220,0x11eda424c⟩, ⟨173,0x1e6afb2e⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1283_271 : momentEstimate 1283 271 = 0x11110dc454 := by
  exact moment_from_blocks [⟨220,0x77f54a9d⟩, ⟨220,0x28a2bfaf7⟩, ⟨220,0x42f56f030⟩, ⟨220,0x47ca182b0⟩, ⟨220,0x3738bb1e4⟩, ⟨220,0x1a33fbe05⟩, ⟨220,0x4c229b7d⟩, ⟨14,393338⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1293_273 : momentEstimate 1293 273 = 0x1199313f68 := by
  exact moment_from_blocks [⟨220,0x7907c9b5⟩, ⟨220,0x292ab8f3b⟩, ⟨220,0x44374e022⟩, ⟨220,0x49a02da52⟩, ⟨220,0x396ee1ad8⟩, ⟨220,0x1c05c3aa7⟩, ⟨220,0x589a07a6⟩, ⟨26,0x21cedf⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1609_361 : momentEstimate 1609 361 = 0x2c2f29a34d := by
  exact moment_from_blocks [⟨220,0x9ae9e045⟩, ⟨220,0x3a19dd58d⟩, ⟨220,0x731b7498a⟩, ⟨220,0x91c0652fa⟩, ⟨220,0x93ad5096a⟩, ⟨220,0x78ff7cdf1⟩, ⟨220,0x4a900d406⟩, ⟨220,0x1ea13115a⟩, ⟨210,0x4703943c⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1638_342 : momentEstimate 1638 342 = 0x2cde589924 := by
  exact moment_from_blocks [⟨220,0x9e05ea71⟩, ⟨220,0x3b19af69e⟩, ⟨220,0x72fd297d2⟩, ⟨220,0x913b13dc2⟩, ⟨220,0x9442da332⟩, ⟨220,0x7c15a10d8⟩, ⟨220,0x4e32b384b⟩, ⟨220,0x20f9ed9dd⟩, ⟨220,0x52e21c4f⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1646_346 : momentEstimate 1646 346 = 0x2dfe19c180 := by
  exact moment_from_blocks [⟨220,0x9ee18351⟩, ⟨220,0x3b8d97ec3⟩, ⟨220,0x7491d3706⟩, ⟨220,0x93ca31a16⟩, ⟨220,0x977b2eea6⟩, ⟨220,0x7fa575add⟩, ⟨220,0x5181b66b2⟩, ⟨220,0x2353959c3⟩, ⟨220,0x613a4f15⟩, ⟨12,333123⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1766_368 : momentEstimate 1766 368 = 0x3c822845f6 := by
  exact moment_from_blocks [⟨220,0xabbf7871⟩, ⟨220,0x41762fbbb⟩, ⟨220,0x859cec168⟩, ⟨220,0xaf873c0c8⟩, ⟨220,0xbc2b5c4a8⟩, ⟨220,0xab894cd08⟩, ⟨220,0x7eb1b1864⟩, ⟨220,0x463dfbf46⟩, ⟨220,0x182d8f7d8⟩, ⟨154,0x1fa4ee68⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1771_373 : momentEstimate 1771 373 = 0x3db5501b19 := by
  exact moment_from_blocks [⟨220,0xac48b7fd⟩, ⟨220,0x41c1142d0⟩, ⟨220,0x870c92f8e⟩, ⟨220,0xb209c1a1e⟩, ⟨220,0xbf5b347ae⟩, ⟨220,0xaf00eb83e⟩, ⟨220,0x820a678cf⟩, ⟨220,0x490412df8⟩, ⟨220,0x19ebed40f⟩, ⟨164,0x26285bde⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1806_381 : momentEstimate 1806 381 = 0x42d0127347 := by
  exact moment_from_blocks [⟨220,0xb00974d1⟩, ⟨220,0x4375848ce⟩, ⟨220,0x8c5a58c46⟩, ⟨220,0xbaf297eb6⟩, ⟨220,0xcb3ca1826⟩, ⟨220,0xbd3875896⟩, ⟨220,0x91756ccaa⟩, ⟨220,0x561c4686f⟩, ⟨220,0x2267d82bb⟩, ⟨207,0x4cf7821c⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment1814_379 : momentEstimate 1814 379 = 0x437d89de31 := by
  exact moment_from_blocks [⟨220,0xb0e50db1⟩, ⟨220,0x43cfcd09c⟩, ⟨220,0x8ce8a8b54⟩, ⟨220,0xbbbd3be74⟩, ⟨220,0xcc6c37f94⟩, ⟨220,0xbef59ceb4⟩, ⟨220,0x93c6c47f8⟩, ⟨220,0x5829688d7⟩, ⟨220,0x23c1a7e72⟩, ⟨213,0x540f1893⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment2015_424 : momentEstimate 2015 424 = 0x6746edbc88 := by
  exact moment_from_blocks [⟨220,0xc6726ead⟩, ⟨220,0x4d5c1d935⟩, ⟨220,0xab625be06⟩, ⟨220,0xf0e30d136⟩, ⟨220,0x114ac3a4e6⟩, ⟨220,0x116bde3916⟩, ⟨220,0xf71808dc6⟩, ⟨220,0xb7c5eb00e⟩, ⟨220,0x6d8c8b9ab⟩, ⟨220,0x2e5921eaf⟩, ⟨220,0x83710c81⟩, ⟨19,0x15e4bf⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment2082_437 : momentEstimate 2082 437 = 0x757781e217 := by
  exact moment_from_blocks [⟨220,0xcda18f01⟩, ⟨220,0x507b89bd8⟩, ⟨220,0xb53127b6e⟩, ⟨220,0x102a00db9e⟩, ⟨220,0x12d4f69ece⟩, ⟨220,0x1353f3c4fe⟩, ⟨220,0x11a6f84e2e⟩, ⟨220,0xdd83bb26f⟩, ⟨220,0x8e48ced1e⟩, ⟨220,0x45c4cd6fb⟩, ⟨220,0x131d86698⟩, ⟨99,0xa43d118⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment2812_593 : momentEstimate 2812 593 = 0x187e8c99b2b := by
  exact moment_from_blocks [⟨220,0x11be7ccd9⟩, ⟨220,0x72769407d⟩, ⟨220,0x11afdaa96c⟩, ⟨220,0x1d5598b7e2⟩, ⟨220,0x265c6633f2⟩, ⟨220,0x2c7136b102⟩, ⟨220,0x2f940a2f12⟩, ⟨220,0x2fc4e0ae22⟩, ⟨220,0x2d03ba2e32⟩, ⟨220,0x275096af42⟩, ⟨220,0x1ef6847271⟩, ⟨220,0x15cdee0fd2⟩, ⟨220,0xd47924b10⟩, ⟨220,0x64d3de43f⟩, ⟨220,0x1bb55e3c8⟩, ⟨105,0x1093f791⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment2816_590 : momentEstimate 2816 590 = 0x1882537ea3b := by
  exact moment_from_blocks [⟨220,0x11c559949⟩, ⟨220,0x72a63e82d⟩, ⟨220,0x11b6fef0f7⟩, ⟨220,0x1d56272126⟩, ⟨220,0x26558c14b6⟩, ⟨220,0x2c66c2e3c6⟩, ⟨220,0x2f89cb8e56⟩, ⟨220,0x2fbea61466⟩, ⟨220,0x2d055275f6⟩, ⟨220,0x275dd0b306⟩, ⟨220,0x1f0bb8331b⟩, ⟨220,0x15e06c6bdc⟩, ⟨220,0xd55e08702⟩, ⟨220,0x656aab3ae⟩, ⟨220,0x1bfb27ee5⟩, ⟨106,0x111239e8⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment4162_879 : momentEstimate 4162 879 = 0x75919b3c614 := by
  exact moment_from_blocks [⟨220,0x1aca8d281⟩, ⟨220,0xb14dd5305⟩, ⟨220,0x1c594aabe9⟩, ⟨220,0x33d70efa2d⟩, ⟨220,0x4e9cfb3890⟩, ⟨220,0x666d9fb310⟩, ⟨220,0x79e13f2590⟩, ⟨220,0x88f7d99010⟩, ⟨220,0x93b16ef290⟩, ⟨220,0x9a0dff4d10⟩, ⟨220,0x9c0d8a9f90⟩, ⟨220,0x99b010ea10⟩, ⟨220,0x92f5922c90⟩, ⟨220,0x87de0e6710⟩, ⟨220,0x7869960370⟩, ⟨220,0x654949aca1⟩, ⟨220,0x511b7fc5ba⟩, ⟨220,0x3d57b4f365⟩, ⟨220,0x2b016476f4⟩, ⟨220,0x1aebf03402⟩, ⟨220,0xe129d81b1⟩, ⟨220,0x525a358f2⟩, ⟨201,0xa7cc0d8f⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment4465_939 : momentEstimate 4465 939 = 0x9b30f69d0d0 := by
  exact moment_from_blocks [⟨220,0x1cd2610a5⟩, ⟨220,0xbf6887159⟩, ⟨220,0x1ebc71c4ad⟩, ⟨220,0x387c0027a1⟩, ⟨220,0x570521322d⟩, ⟨220,0x73f5308734⟩, ⟨220,0x8c435a3f14⟩, ⟨220,0x9fe855dcf4⟩, ⟨220,0xaee42360d4⟩, ⟨220,0xb936c2cab4⟩, ⟨220,0xbee0341a94⟩, ⟨220,0xbfe0775074⟩, ⟨220,0xbc378c6c54⟩, ⟨220,0xb3e5736e34⟩, ⟨220,0xa6ea2c5614⟩, ⟨220,0x9545b723f4⟩, ⟨220,0x7f82835f3b⟩, ⟨220,0x6855b114c2⟩, ⟨220,0x516623adbf⟩, ⟨220,0x3bbd9d46bc⟩, ⟨220,0x283f3387af⟩, ⟨220,0x17cbdfd800⟩, ⟨220,0xb4c06d5d6⟩, ⟨220,0x3467e1f32⟩, ⟨124,0x2b44e4cc⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment5736_1211 : momentEstimate 5736 1211 = 0x1a7cbea93549 := by
  exact moment_from_blocks [⟨220,0x2556e90a9⟩, ⟨220,0xfa926140d⟩, ⟨220,0x28c00f0251⟩, ⟨220,0x4bf7477875⟩, ⟨220,0x77abed9379⟩, ⟨220,0xaa01f57ed0⟩, ⟨220,0xdc517b29b4⟩, ⟨220,0x108dd2c3e54⟩, ⟨220,0x12f666c80f4⟩, ⟨220,0x14fed3bf194⟩, ⟨220,0x16a719a9034⟩, ⟨220,0x17ef3885cd4⟩, ⟨220,0x18d73055774⟩, ⟨220,0x195f0118014⟩, ⟨220,0x1986aacd6b4⟩, ⟨220,0x194e2d75b54⟩, ⟨220,0x18b58910df4⟩, ⟨220,0x17bcbd9ee94⟩, ⟨220,0x1663cb1fd34⟩, ⟨220,0x14aab1939d4⟩, ⟨220,0x12925dae549⟩, ⟨220,0x103ad0e664a⟩, ⟨220,0xdd49b0433e⟩, ⟨220,0xb7390ef835⟩, ⟨220,0x92870f1bb9⟩, ⟨220,0x702c93065b⟩, ⟨220,0x50e7179846⟩, ⟨220,0x35b795e60a⟩, ⟨220,0x1f8dcd164c⟩, ⟨220,0xeecfa40d8⟩, ⟨220,0x45803fc9e⟩, ⟨127,0x3bd383a0⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
    rfl rfl

private theorem moment6714_1410 : momentEstimate 6714 1410 = 0x3180d48a9efa :=
  HighCore82268BankMoments.M6714_1410.proof

private theorem moment8413_1776 : momentEstimate 8413 1776 = 0x7a821d9dae58 :=
  HighCore82268BankMoments.M8413_1776.proof

private theorem moment9027_1904 : momentEstimate 9027 1904 = 0xa24319aee4cb :=
  HighCore82268BankMoments.M9027_1904.proof

private theorem moment9602_2029 : momentEstimate 9602 2029 = 0xd003312b9c31 :=
  HighCore82268BankMoments.M9602_2029.proof

private theorem moment10182_2152 : momentEstimate 10182 2152 = 0x1070a596d35fc :=
  HighCore82268BankMoments.M10182_2152.proof

local notation "pass!" depth "," grade "," deriv "," nodes "," moment ";" witness =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) witness

private theorem terminal_ok (b : Band) : BankOK (terminal b) := by
  cases b with
  | h2527 => exact (pass! 7321,10182,2152,0x290af822d40000,0x1070a596d35fc; moment10182_2152)
  | h2528 => exact (pass! 6903,9602,2029,0x2267f974f80000,0xd003312b9c31; moment9602_2029)
  | h2536 => exact (pass! 7550,10506,2218,0x2cfea55aa80000,0x129e297a45c0c; moment10506_2218)
  | h2540 => exact (pass! 7550,10506,2218,0x2cfea55aa80000,0x129e297a45c0c; moment10506_2218)
  | h2570 => exact (pass! 7550,10506,2218,0x2cfea55aa80000,0x129e297a45c0c; moment10506_2218)
  | h8100 => exact (pass! 124,173,32,0xc4fd80000,0x15c66e5; moment173_32)

private def StageOK (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankOK s.free ∧ BankOK s.moving

private theorem stages_nil : StageOK [] :=
  fun _ hs => (List.not_mem_nil hs).elim

private theorem stages_cons {s : Stage} {ss : List Stage}
    (hf : BankOK s.free) (hm : BankOK s.moving) (ht : StageOK ss) : StageOK (s :: ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩

private theorem stages_ok (b : Band) : StageOK (stages b) := by
  cases b with
  | h2527 =>
    rw [stages]
    refine stages_cons (pass! 70,97,21,0x28d4c0000,0x284e2c; moment97_21) (pass! 340,473,99,0x10f23b80000,0x510d7a50; moment473_99) ?_
    refine stages_cons (pass! 73,101,22,0x2e5640000,0x2f6f2a; moment101_22) (pass! 358,498,104,0x13bbdc40000,0x6355595b; moment498_104) ?_
    refine stages_cons (pass! 83,115,25,0x439080000,0x4ed4ac; moment115_25) (pass! 433,603,127,0x2316e000000,0xd64bfbb8; moment603_127) ?_
    refine stages_cons (pass! 91,126,27,0x57a300000,0x6fafa5; moment126_27) (pass! 435,606,127,0x2373a000000,0xd9bc9eb8; moment606_127) ?_
    refine stages_cons (pass! 106,147,32,0x8b45c0000,0xcf7010; moment147_32) (pass! 542,756,157,0x44042bc0000,0x20a3388b0; moment756_157) ?_
    refine stages_cons (pass! 120,166,37,0xcc31c0000,0x1553865; moment166_37) (pass! 599,834,175,0x5c551c00000,0x30adbb088; moment834_175) ?_
    refine stages_cons (pass! 142,197,43,0x14bde80000,0x294fec6; moment197_43) (pass! 732,1018,214,0xa8578840000,0x6c03bb2c1; moment1018_214) ?_
    refine stages_cons (pass! 169,235,50,0x222f040000,0x517adc3; moment235_50) (pass! 922,1283,271,0x151520600000,0x11110dc454; moment1283_271) ?_
    refine stages_cons (pass! 206,286,64,0x3fe4a40000,0xb89ee2e; moment286_64) (pass! 931,1293,273,0x15aa71680000,0x1199313f68; moment1293_273) ?_
    refine stages_cons (pass! 207,287,64,0x4096600000,0xbab2d1e; moment287_64) (pass! 1178,1638,342,0x2b823f280000,0x2cde589924; moment1638_342) ?_
    refine stages_cons (pass! 261,362,80,0x8008bc0000,0x1d282567; moment362_80) (pass! 1499,2082,437,0x59dab0b80000,0x757781e217; moment2082_437) ?_
    refine stages_cons (pass! 259,359,79,0x7cac400000,0x1c1d91ae; moment359_79) (pass! 1269,1766,368,0x3653ce5c0000,0x3c822845f6; moment1766_368) ?_
    refine stages_cons (pass! 278,385,83,0x9785d80000,0x248c5e25; moment385_83) (pass! 1305,1814,379,0x3b24e1500000,0x437d89de31; moment1814_379) ?_
    refine stages_cons (pass! 441,611,140,0x27581740000,0xf10fe4d6; moment611_140) (pass! 2020,2812,593,0xdcdef0a40000,0x187e8c99b2b; moment2812_593) ?_
    refine stages_cons (pass! 599,831,187,0x61171b00000,0x32a898a11; moment831_187) (pass! 3212,4465,939,0x3746035e80000,0x9b30f69d0d0; moment4465_939) ?_
    refine stages_cons (pass! 881,1220,273,0x132695480000,0xe993089da; moment1220_273) (pass! 4826,6714,1410,0xbb4c7c9d00000,0x3180d48a9efa; moment6714_1410) ?_
    refine stages_cons (pass! 1161,1609,361,0x2be2bfa80000,0x2c2f29a34d; moment1609_361) (pass! 6479,9027,1904,0x1c71d6b5e00000,0xa24319aee4cb; moment9027_1904) ?_
    exact stages_nil
  | h2528 =>
    rw [stages]
    refine stages_cons (pass! 73,101,22,0x2e5640000,0x2f6f2a; moment101_22) (pass! 349,485,102,0x125f7fc0000,0x59e3ed8b; moment485_102) ?_
    refine stages_cons (pass! 80,111,24,0x3c7300000,0x4451ef; moment111_24) (pass! 358,498,104,0x13bbdc40000,0x6355595b; moment498_104) ?_
    refine stages_cons (pass! 89,123,27,0x536d00000,0x67700d; moment123_27) (pass! 406,565,119,0x1ceebd00000,0xa5555e6d; moment565_119) ?_
    refine stages_cons (pass! 97,134,30,0x6d1340000,0x931387; moment134_30) (pass! 425,591,125,0x2141d180000,0xc672a1cc; moment591_125) ?_
    refine stages_cons (pass! 106,147,32,0x8b45c0000,0xcf7010; moment147_32) (pass! 461,640,135,0x2a445e00000,0x1100a07c3; moment640_135) ?_
    refine stages_cons (pass! 115,159,35,0xb24d00000,0x11d1f9e; moment159_35) (pass! 515,716,150,0x3a9f1980000,0x1a74a03e8; moment716_150) ?_
    refine stages_cons (pass! 115,160,34,0xae8580000,0x11c9279; moment160_34) (pass! 579,806,170,0x53ba8f80000,0x2aa645c9f; moment806_170) ?_
    refine stages_cons (pass! 142,197,43,0x14bde80000,0x294fec6; moment197_43) (pass! 679,944,199,0x86af1a00000,0x5018948c9; moment944_199) ?_
    refine stages_cons (pass! 169,235,50,0x222f040000,0x517adc3; moment235_50) (pass! 888,1233,260,0x12c890e80000,0xe8ae039a1; moment1233_260) ?_
    refine stages_cons (pass! 214,296,66,0x472de80000,0xd30a80f; moment296_66) (pass! 809,1126,236,0xe2bba140000,0xa12bddaf7; moment1126_236) ?_
    refine stages_cons (pass! 216,299,66,0x48ac040000,0xd9f9f46; moment299_66) (pass! 1185,1646,346,0x2c7b45940000,0x2dfe19c180; moment1646_346) ?_
    refine stages_cons (pass! 261,362,81,0x813b280000,0x1d6fb003; moment362_81) (pass! 1450,2015,424,0x5186864c0000,0x6746edbc88; moment2015_424) ?_
    refine stages_cons (pass! 259,359,81,0x7f07680000,0x1ca909eb; moment359_81) (pass! 1274,1771,373,0x375ff1cc0000,0x3db5501b19; moment1771_373) ?_
    refine stages_cons (pass! 278,385,84,0x98e52c0000,0x24e31c52; moment385_84) (pass! 1296,1806,381,0x3a78efec0000,0x42d0127347; moment1806_381) ?_
    refine stages_cons (pass! 429,593,135,0x23fdde00000,0xd4e9369b; moment593_135) (pass! 2025,2816,590,0xdd3ba2e40000,0x1882537ea3b; moment2816_590) ?_
    refine stages_cons (pass! 611,846,188,0x65e80780000,0x35e195e5b; moment846_188) (pass! 2993,4162,879,0x2ce2150400000,0x75919b3c614; moment4162_879) ?_
    refine stages_cons (pass! 776,1076,242,0xd28dc840000,0x8e03abac2; moment1076_242) (pass! 4126,5736,1211,0x757a25a480000,0x1a7cbea93549; moment5736_1211) ?_
    refine stages_cons (pass! 1162,1609,361,0x2bf86f440000,0x2c2f29a34d; moment1609_361) (pass! 6051,8413,1776,0x172699d8580000,0x7a821d9dae58; moment8413_1776) ?_
    exact stages_nil
  | h2536 =>
    rw [stages]
    refine stages_cons (pass! 73,101,22,0x2e5640000,0x2f6f2a; moment101_22) (pass! 352,489,103,0x12dda700000,0x5cfd94a5; moment489_103) ?_
    refine stages_cons (pass! 78,108,24,0x392740000,0x3e9e8f; moment108_24) (pass! 345,480,101,0x11c61f80000,0x564a51c0; moment480_101) ?_
    refine stages_cons (pass! 86,119,26,0x4b3780000,0x5a8245; moment119_26) (pass! 385,535,112,0x188bf840000,0x84679137; moment535_112) ?_
    refine stages_cons (pass! 94,130,29,0x633bc0000,0x822d2c; moment130_29) (pass! 411,572,120,0x1dec1a80000,0xad1e0c80; moment572_120) ?_
    refine stages_cons (pass! 102,141,31,0x7cec00000,0xb15384; moment141_31) (pass! 438,609,128,0x2436d340000,0xde912dc3; moment609_128) ?_
    refine stages_cons (pass! 108,150,33,0x948040000,0xe271e9; moment150_33) (pass! 522,726,153,0x3d548e40000,0x1c16ef1c7; moment726_153) ?_
    refine stages_cons (pass! 108,149,33,0x948040000,0xdda994; moment149_33) (pass! 570,792,167,0x4fc3e700000,0x27c2e15db; moment792_167) ?_
    refine stages_cons (pass! 142,197,43,0x14bde80000,0x294fec6; moment197_43) (pass! 696,968,204,0x910a3980000,0x5884788a7; moment968_204) ?_
    refine stages_cons (pass! 163,226,50,0x1f8a780000,0x47e88b5; moment226_50) (pass! 851,1183,249,0x108708880000,0xc4f2a7606; moment1183_249) ?_
    refine stages_cons (pass! 221,306,68,0x4e346c0000,0xf032b8c; moment306_68) (pass! 952,1324,279,0x17270e900000,0x1350bb1fb5; moment1324_279) ?_
    refine stages_cons (pass! 212,294,65,0x44e9c40000,0xcc1a54f; moment294_65) (pass! 1115,1550,329,0x255cff880000,0x2473d5ffe4; moment1550_329) ?_
    refine stages_cons (pass! 261,362,82,0x826c0c0000,0x1db6eefa; moment362_82) (pass! 1463,2034,430,0x54106e900000,0x6b9d823520; moment2034_430) ?_
    refine stages_cons (pass! 246,341,75,0x6ae4280000,0x16e7d3b2; moment341_75) (pass! 1220,1696,357,0x309db61c0000,0x33e3754396; moment1696_357) ?_
    refine stages_cons (pass! 279,386,85,0x9b80980000,0x25892b87; moment386_85) (pass! 1240,1725,359,0x32a0cb700000,0x370899d961; moment1725_359) ?_
    refine stages_cons (pass! 534,740,167,0x44f1df00000,0x1ff6e1863; moment740_167) (pass! 2252,3131,661,0x131ef423c0000,0x25ab1ba8825; moment3131_661) ?_
    refine stages_cons (pass! 637,883,197,0x73e2ad80000,0x401d0f0c6; moment883_197) (pass! 3474,4830,1019,0x461aa92080000,0xd5013df2ef9; moment4830_1019) ?_
    refine stages_cons (pass! 774,1072,239,0xcf60ca00000,0x8af950b98; moment1072_239) (pass! 4170,5798,1223,0x7934721300000,0x1ba1a89b2ba1; moment5798_1223) ?_
    refine stages_cons (pass! 1042,1443,329,0x201c60040000,0x1cf53a5560; moment1443_329) (pass! 5487,7630,1607,0x113c22e7a00000,0x52bdbe618ec3; moment7630_1607) ?_
    exact stages_nil
  | h2540 =>
    rw [stages]
    refine stages_cons (pass! 73,101,22,0x2e5640000,0x2f6f2a; moment101_22) (pass! 352,489,103,0x12dda700000,0x5cfd94a5; moment489_103) ?_
    refine stages_cons (pass! 78,108,24,0x392740000,0x3e9e8f; moment108_24) (pass! 345,480,101,0x11c61f80000,0x564a51c0; moment480_101) ?_
    refine stages_cons (pass! 86,119,26,0x4b3780000,0x5a8245; moment119_26) (pass! 385,535,112,0x188bf840000,0x84679137; moment535_112) ?_
    refine stages_cons (pass! 94,130,29,0x633bc0000,0x822d2c; moment130_29) (pass! 411,572,120,0x1dec1a80000,0xad1e0c80; moment572_120) ?_
    refine stages_cons (pass! 102,141,31,0x7cec00000,0xb15384; moment141_31) (pass! 438,609,128,0x2436d340000,0xde912dc3; moment609_128) ?_
    refine stages_cons (pass! 108,150,33,0x948040000,0xe271e9; moment150_33) (pass! 522,726,153,0x3d548e40000,0x1c16ef1c7; moment726_153) ?_
    refine stages_cons (pass! 108,149,33,0x948040000,0xdda994; moment149_33) (pass! 570,792,167,0x4fc3e700000,0x27c2e15db; moment792_167) ?_
    refine stages_cons (pass! 142,197,43,0x14bde80000,0x294fec6; moment197_43) (pass! 696,968,204,0x910a3980000,0x5884788a7; moment968_204) ?_
    refine stages_cons (pass! 163,226,50,0x1f8a780000,0x47e88b5; moment226_50) (pass! 851,1183,249,0x108708880000,0xc4f2a7606; moment1183_249) ?_
    refine stages_cons (pass! 221,306,68,0x4e346c0000,0xf032b8c; moment306_68) (pass! 952,1324,279,0x17270e900000,0x1350bb1fb5; moment1324_279) ?_
    refine stages_cons (pass! 212,294,65,0x44e9c40000,0xcc1a54f; moment294_65) (pass! 1115,1550,329,0x255cff880000,0x2473d5ffe4; moment1550_329) ?_
    refine stages_cons (pass! 261,362,82,0x826c0c0000,0x1db6eefa; moment362_82) (pass! 1463,2034,430,0x54106e900000,0x6b9d823520; moment2034_430) ?_
    refine stages_cons (pass! 246,341,75,0x6ae4280000,0x16e7d3b2; moment341_75) (pass! 1220,1696,357,0x309db61c0000,0x33e3754396; moment1696_357) ?_
    refine stages_cons (pass! 279,386,85,0x9b80980000,0x25892b87; moment386_85) (pass! 1240,1725,359,0x32a0cb700000,0x370899d961; moment1725_359) ?_
    refine stages_cons (pass! 534,740,167,0x44f1df00000,0x1ff6e1863; moment740_167) (pass! 2252,3131,661,0x131ef423c0000,0x25ab1ba8825; moment3131_661) ?_
    refine stages_cons (pass! 637,883,197,0x73e2ad80000,0x401d0f0c6; moment883_197) (pass! 3474,4830,1019,0x461aa92080000,0xd5013df2ef9; moment4830_1019) ?_
    refine stages_cons (pass! 774,1072,239,0xcf60ca00000,0x8af950b98; moment1072_239) (pass! 4170,5798,1223,0x7934721300000,0x1ba1a89b2ba1; moment5798_1223) ?_
    refine stages_cons (pass! 1042,1443,329,0x201c60040000,0x1cf53a5560; moment1443_329) (pass! 5487,7630,1607,0x113c22e7a00000,0x52bdbe618ec3; moment7630_1607) ?_
    exact stages_nil
  | h2570 =>
    rw [stages]
    refine stages_cons (pass! 73,101,22,0x2e5640000,0x2f6f2a; moment101_22) (pass! 352,489,103,0x12dda700000,0x5cfd94a5; moment489_103) ?_
    refine stages_cons (pass! 78,108,24,0x392740000,0x3e9e8f; moment108_24) (pass! 345,480,101,0x11c61f80000,0x564a51c0; moment480_101) ?_
    refine stages_cons (pass! 86,119,26,0x4b3780000,0x5a8245; moment119_26) (pass! 385,535,112,0x188bf840000,0x84679137; moment535_112) ?_
    refine stages_cons (pass! 94,130,29,0x633bc0000,0x822d2c; moment130_29) (pass! 411,572,120,0x1dec1a80000,0xad1e0c80; moment572_120) ?_
    refine stages_cons (pass! 102,141,31,0x7cec00000,0xb15384; moment141_31) (pass! 438,609,128,0x2436d340000,0xde912dc3; moment609_128) ?_
    refine stages_cons (pass! 108,150,33,0x948040000,0xe271e9; moment150_33) (pass! 522,726,153,0x3d548e40000,0x1c16ef1c7; moment726_153) ?_
    refine stages_cons (pass! 108,149,33,0x948040000,0xdda994; moment149_33) (pass! 570,792,167,0x4fc3e700000,0x27c2e15db; moment792_167) ?_
    refine stages_cons (pass! 142,197,43,0x14bde80000,0x294fec6; moment197_43) (pass! 696,968,204,0x910a3980000,0x5884788a7; moment968_204) ?_
    refine stages_cons (pass! 163,226,50,0x1f8a780000,0x47e88b5; moment226_50) (pass! 851,1183,249,0x108708880000,0xc4f2a7606; moment1183_249) ?_
    refine stages_cons (pass! 221,306,68,0x4e346c0000,0xf032b8c; moment306_68) (pass! 952,1324,279,0x17270e900000,0x1350bb1fb5; moment1324_279) ?_
    refine stages_cons (pass! 212,294,65,0x44e9c40000,0xcc1a54f; moment294_65) (pass! 1115,1550,329,0x255cff880000,0x2473d5ffe4; moment1550_329) ?_
    refine stages_cons (pass! 261,362,82,0x826c0c0000,0x1db6eefa; moment362_82) (pass! 1463,2034,430,0x54106e900000,0x6b9d823520; moment2034_430) ?_
    refine stages_cons (pass! 246,341,75,0x6ae4280000,0x16e7d3b2; moment341_75) (pass! 1220,1696,357,0x309db61c0000,0x33e3754396; moment1696_357) ?_
    refine stages_cons (pass! 279,386,85,0x9b80980000,0x25892b87; moment386_85) (pass! 1240,1725,359,0x32a0cb700000,0x370899d961; moment1725_359) ?_
    refine stages_cons (pass! 534,740,167,0x44f1df00000,0x1ff6e1863; moment740_167) (pass! 2252,3131,661,0x131ef423c0000,0x25ab1ba8825; moment3131_661) ?_
    refine stages_cons (pass! 637,883,197,0x73e2ad80000,0x401d0f0c6; moment883_197) (pass! 3474,4830,1019,0x461aa92080000,0xd5013df2ef9; moment4830_1019) ?_
    refine stages_cons (pass! 774,1072,239,0xcf60ca00000,0x8af950b98; moment1072_239) (pass! 4170,5798,1223,0x7934721300000,0x1ba1a89b2ba1; moment5798_1223) ?_
    refine stages_cons (pass! 1042,1443,329,0x201c60040000,0x1cf53a5560; moment1443_329) (pass! 5487,7630,1607,0x113c22e7a00000,0x52bdbe618ec3; moment7630_1607) ?_
    exact stages_nil
  | h8100 =>
    rw [stages]
    refine stages_cons (pass! 11,15,3,0x3500000,2194; moment15_3) (pass! 20,28,4,0xdc00000,17031; moment28_4) ?_
    refine stages_cons (pass! 21,29,6,0x13cc0000,24733; moment29_6) (pass! 38,53,9,0x5d840000,211909; moment53_9) ?_
    refine stages_cons (pass! 34,47,10,0x4f100000,156979; moment47_10) (pass! 64,89,15,0x1a3600000,0x17e10a; moment89_15) ?_
    refine stages_cons (pass! 54,75,16,0x12f140000,957077; moment75_16) (pass! 101,141,24,0x64f3c0000,0x91e8ba; moment141_24) ?_
    exact stages_nil

theorem listed_ok (b : Band) (t : Bank) (ht : Listed b t) : BankOK t := by
  rcases ht with rfl | ⟨s, hs, rfl | rfl⟩ | ⟨i, rfl⟩
  · exact terminal_ok b
  · exact (stages_ok b s hs).1
  · exact (stages_ok b s hs).2
  · exact ⟨(terminal_ok b).nodes, (terminal_ok b).moment⟩

theorem interpolation_sources : SourceExists :=
  source (fun b t ht => (listed_ok b t ht).nodes) (fun b t ht => (listed_ok b t ht).moment)

#print axioms interpolation_sources
end HighCore82268BankProof
