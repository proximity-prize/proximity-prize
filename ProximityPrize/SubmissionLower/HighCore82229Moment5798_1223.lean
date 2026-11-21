import ProximityPrize.SubmissionLower.HighCore82229MomentAppend
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82229BankProof
open P1_7_1_3 (momentEstimate blockEstimate)

private theorem p5798_1223_1223_220 : blockEstimate 5798 1223 1223 220 = 0x25c147171 := by decide +kernel
private theorem p5798_1223_1443_220 : blockEstimate 5798 1223 1443 220 = 0xfd7533b35 := by decide +kernel
private theorem p5798_1223_1663_220 : blockEstimate 5798 1223 1663 220 = 0x293d1cec59 := by decide +kernel
private theorem p5798_1223_1883_220 : blockEstimate 5798 1223 1883 220 = 0x4cea8fa1dd := by decide +kernel
private theorem p5798_1223_2103_220 : blockEstimate 5798 1223 2103 220 = 0x793cc978c1 := by decide +kernel
private theorem p5798_1223_2323_220 : blockEstimate 5798 1223 2323 220 = 0xac681691ad := by decide +kernel
private theorem p5798_1223_2543_220 : blockEstimate 5798 1223 2543 220 = 0xe01030e5f8 := by decide +kernel
private theorem p5798_1223_2763_220 : blockEstimate 5798 1223 2763 220 = 0x10dfce754b8 := by decide +kernel
private theorem p5798_1223_2983_220 : blockEstimate 5798 1223 2983 220 = 0x135d7f18778 := by decide +kernel
private theorem p5798_1223_3203_220 : blockEstimate 5798 1223 3203 220 = 0x157a14f7e38 := by decide +kernel
private theorem p5798_1223_3423_220 : blockEstimate 5798 1223 3423 220 = 0x173590138f8 := by decide +kernel
private theorem p5798_1223_3643_220 : blockEstimate 5798 1223 3643 220 = 0x188ff06b7b8 := by decide +kernel
private theorem p5798_1223_3863_220 : blockEstimate 5798 1223 3863 220 = 0x198935ffa78 := by decide +kernel
private theorem p5798_1223_4083_220 : blockEstimate 5798 1223 4083 220 = 0x1a2160d0138 := by decide +kernel
private theorem p5798_1223_4303_220 : blockEstimate 5798 1223 4303 220 = 0x1a5870dcbf8 := by decide +kernel
private theorem p5798_1223_4523_220 : blockEstimate 5798 1223 4523 220 = 0x1a2e6625ab8 := by decide +kernel
private theorem p5798_1223_4743_220 : blockEstimate 5798 1223 4743 220 = 0x19a340aad78 := by decide +kernel
private theorem p5798_1223_4963_220 : blockEstimate 5798 1223 4963 220 = 0x18b7006c438 := by decide +kernel
private theorem p5798_1223_5183_220 : blockEstimate 5798 1223 5183 220 = 0x1769a569ef8 := by decide +kernel
private theorem p5798_1223_5403_220 : blockEstimate 5798 1223 5403 220 = 0x15bb2fa3db8 := by decide +kernel
private theorem p5798_1223_5623_220 : blockEstimate 5798 1223 5623 220 = 0x13abb88c884 := by decide +kernel
private theorem p5798_1223_5843_220 : blockEstimate 5798 1223 5843 220 = 0x115008ddcd2 := by decide +kernel
private theorem p5798_1223_6063_220 : blockEstimate 5798 1223 6063 220 = 0xeddf3b52bd := by decide +kernel
private theorem p5798_1223_6283_220 : blockEstimate 5798 1223 6283 220 = 0xc6ce3b8c50 := by decide +kernel
private theorem p5798_1223_6503_220 : blockEstimate 5798 1223 6503 220 = 0xa0de2e5f13 := by decide +kernel
private theorem p5798_1223_6723_220 : blockEstimate 5798 1223 6723 220 = 0x7d0ce117d4 := by decide +kernel
private theorem p5798_1223_6943_220 : blockEstimate 5798 1223 6943 220 = 0x5c2eef2468 := by decide +kernel
private theorem p5798_1223_7163_220 : blockEstimate 5798 1223 7163 220 = 0x3f14a3b201 := by decide +kernel
private theorem p5798_1223_7383_220 : blockEstimate 5798 1223 7383 220 = 0x26de86ecbe := by decide +kernel
private theorem p5798_1223_7603_220 : blockEstimate 5798 1223 7603 220 = 0x141905219d := by decide +kernel
private theorem p5798_1223_7823_220 : blockEstimate 5798 1223 7823 220 = 0x74704e78e := by decide +kernel
private theorem p5798_1223_8043_201 : blockEstimate 5798 1223 8043 201 = 0xeb457ceb := by decide +kernel
private theorem p5798_1223_1223_440 : blockEstimate 5798 1223 1223 440 = 0x123367aca6 :=
  append_checked p5798_1223_1223_220 p5798_1223_1443_220
private theorem p5798_1223_1663_440 : blockEstimate 5798 1223 1663 440 = 0x7627ac8e36 :=
  append_checked p5798_1223_1663_220 p5798_1223_1883_220
private theorem p5798_1223_1223_880 : blockEstimate 5798 1223 1223 880 = 0x885b143adc :=
  append_checked p5798_1223_1223_440 p5798_1223_1663_440
private theorem p5798_1223_2103_440 : blockEstimate 5798 1223 2103 440 = 0x125a4e00a6e :=
  append_checked p5798_1223_2103_220 p5798_1223_2323_220
private theorem p5798_1223_2543_440 : blockEstimate 5798 1223 2543 440 = 0x1ee0d183ab0 :=
  append_checked p5798_1223_2543_220 p5798_1223_2763_220
private theorem p5798_1223_2103_880 : blockEstimate 5798 1223 2103 880 = 0x313b1f8451e :=
  append_checked p5798_1223_2103_440 p5798_1223_2543_440
private theorem p5798_1223_1223_1760 : blockEstimate 5798 1223 1223 1760 = 0x39c0d0c7ffa :=
  append_checked p5798_1223_1223_880 p5798_1223_2103_880
private theorem p5798_1223_2983_440 : blockEstimate 5798 1223 2983 440 = 0x28d794105b0 :=
  append_checked p5798_1223_2983_220 p5798_1223_3203_220
private theorem p5798_1223_3423_440 : blockEstimate 5798 1223 3423 440 = 0x2fc5807f0b0 :=
  append_checked p5798_1223_3423_220 p5798_1223_3643_220
private theorem p5798_1223_2983_880 : blockEstimate 5798 1223 2983 880 = 0x589d148f660 :=
  append_checked p5798_1223_2983_440 p5798_1223_3423_440
private theorem p5798_1223_3863_440 : blockEstimate 5798 1223 3863 440 = 0x33aa96cfbb0 :=
  append_checked p5798_1223_3863_220 p5798_1223_4083_220
private theorem p5798_1223_4303_440 : blockEstimate 5798 1223 4303 440 = 0x3486d7026b0 :=
  append_checked p5798_1223_4303_220 p5798_1223_4523_220
private theorem p5798_1223_3863_880 : blockEstimate 5798 1223 3863 880 = 0x68316dd2260 :=
  append_checked p5798_1223_3863_440 p5798_1223_4303_440
private theorem p5798_1223_2983_1760 : blockEstimate 5798 1223 2983 1760 = 0xc0ce82618c0 :=
  append_checked p5798_1223_2983_880 p5798_1223_3863_880
private theorem p5798_1223_1223_3520 : blockEstimate 5798 1223 1223 3520 = 0xfa8f53298ba :=
  append_checked p5798_1223_1223_1760 p5798_1223_2983_1760
private theorem p5798_1223_4743_440 : blockEstimate 5798 1223 4743 440 = 0x325a41171b0 :=
  append_checked p5798_1223_4743_220 p5798_1223_4963_220
private theorem p5798_1223_5183_440 : blockEstimate 5798 1223 5183 440 = 0x2d24d50dcb0 :=
  append_checked p5798_1223_5183_220 p5798_1223_5403_220
private theorem p5798_1223_4743_880 : blockEstimate 5798 1223 4743 880 = 0x5f7f1624e60 :=
  append_checked p5798_1223_4743_440 p5798_1223_5183_440
private theorem p5798_1223_5623_440 : blockEstimate 5798 1223 5623 440 = 0x24fbc16a556 :=
  append_checked p5798_1223_5623_220 p5798_1223_5843_220
private theorem p5798_1223_6063_440 : blockEstimate 5798 1223 6063 440 = 0x1b4ad76df0d :=
  append_checked p5798_1223_6063_220 p5798_1223_6283_220
private theorem p5798_1223_5623_880 : blockEstimate 5798 1223 5623 880 = 0x404698d8463 :=
  append_checked p5798_1223_5623_440 p5798_1223_6063_440
private theorem p5798_1223_4743_1760 : blockEstimate 5798 1223 4743 1760 = 0x9fc5aefd2c3 :=
  append_checked p5798_1223_4743_880 p5798_1223_5623_880
private theorem p5798_1223_6503_440 : blockEstimate 5798 1223 6503 440 = 0x11deb0f76e7 :=
  append_checked p5798_1223_6503_220 p5798_1223_6723_220
private theorem p5798_1223_6943_440 : blockEstimate 5798 1223 6943 440 = 0x9b4392d669 :=
  append_checked p5798_1223_6943_220 p5798_1223_7163_220
private theorem p5798_1223_6503_880 : blockEstimate 5798 1223 6503 880 = 0x1b92ea24d50 :=
  append_checked p5798_1223_6503_440 p5798_1223_6943_440
private theorem p5798_1223_7383_440 : blockEstimate 5798 1223 7383 440 = 0x3af78c0e5b :=
  append_checked p5798_1223_7383_220 p5798_1223_7603_220
private theorem p5798_1223_7823_421 : blockEstimate 5798 1223 7823 421 = 0x8324a6479 :=
  append_checked p5798_1223_7823_220 p5798_1223_8043_201
private theorem p5798_1223_7383_861 : blockEstimate 5798 1223 7383 861 = 0x4329d672d4 :=
  append_checked p5798_1223_7383_440 p5798_1223_7823_421
private theorem p5798_1223_6503_1741 : blockEstimate 5798 1223 6503 1741 = 0x1fc5878c024 :=
  append_checked p5798_1223_6503_880 p5798_1223_7383_861
private theorem p5798_1223_4743_3501 : blockEstimate 5798 1223 4743 3501 = 0xbf8b36892e7 :=
  append_checked p5798_1223_4743_1760 p5798_1223_6503_1741
private theorem p5798_1223_1223_7021 : blockEstimate 5798 1223 1223 7021 = 0x1ba1a89b2ba1 :=
  append_checked p5798_1223_1223_3520 p5798_1223_4743_3501

theorem moment5798_1223 : momentEstimate 5798 1223 = 0x1ba1a89b2ba1 := p5798_1223_1223_7021
end HighCore82229BankProof
