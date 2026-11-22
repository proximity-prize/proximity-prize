-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Moment3850_812.lean.
import ProximityPrize.SubmissionLower.Peer653High53MomentAppend
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace Peer653High53BankProof
open P1_7_1_3 (momentEstimate blockEstimate)

private theorem p3850_812_812_220 : blockEstimate 3850 812 812 220 = 0x18b348861 := by decide +kernel
private theorem p3850_812_1032_220 : blockEstimate 3850 812 1032 220 = 0xa2c7e3b65 := by decide +kernel
private theorem p3850_812_1252_220 : blockEstimate 3850 812 1252 220 = 0x19e3fc64c9 := by decide +kernel
private theorem p3850_812_1472_220 : blockEstimate 3850 812 1472 220 = 0x2f0578b7aa := by decide +kernel
private theorem p3850_812_1692_220 : blockEstimate 3850 812 1692 220 = 0x45759a29cc := by decide +kernel
private theorem p3850_812_1912_220 : blockEstimate 3850 812 1912 220 = 0x584bbc084c := by decide +kernel
private theorem p3850_812_2132_220 : blockEstimate 3850 812 2132 220 = 0x6719e4994c := by decide +kernel
private theorem p3850_812_2352_220 : blockEstimate 3850 812 2352 220 = 0x71e013dccc := by decide +kernel
private theorem p3850_812_2572_220 : blockEstimate 3850 812 2572 220 = 0x789e49d2cc := by decide +kernel
private theorem p3850_812_2792_220 : blockEstimate 3850 812 2792 220 = 0x7b54867b4c := by decide +kernel
private theorem p3850_812_3012_220 : blockEstimate 3850 812 3012 220 = 0x7a02c9d64c := by decide +kernel
private theorem p3850_812_3232_220 : blockEstimate 3850 812 3232 220 = 0x74a913e3cc := by decide +kernel
private theorem p3850_812_3452_220 : blockEstimate 3850 812 3452 220 = 0x6b4764a3cc := by decide +kernel
private theorem p3850_812_3672_220 : blockEstimate 3850 812 3672 220 = 0x5dde99bae0 := by decide +kernel
private theorem p3850_812_3892_220 : blockEstimate 3850 812 3892 220 = 0x4d4d233ab2 := by decide +kernel
private theorem p3850_812_4112_220 : blockEstimate 3850 812 4112 220 = 0x3c0d29e8e4 := by decide +kernel
private theorem p3850_812_4332_220 : blockEstimate 3850 812 4332 220 = 0x2b6f374ee1 := by decide +kernel
private theorem p3850_812_4552_220 : blockEstimate 3850 812 4552 220 = 0x1c699a31db := by decide +kernel
private theorem p3850_812_4772_220 : blockEstimate 3850 812 4772 220 = 0xfd7341e17 := by decide +kernel
private theorem p3850_812_4992_220 : blockEstimate 3850 812 4992 220 = 0x6a03a0b28 := by decide +kernel
private theorem p3850_812_5212_220 : blockEstimate 3850 812 5212 220 = 0x151315527 := by decide +kernel
private theorem p3850_812_5432_42 : blockEstimate 3850 812 5432 42 = 0x1909942 := by decide +kernel
private theorem p3850_812_812_440 : blockEstimate 3850 812 812 440 = 0xbb7b2c3c6 :=
  append_checked p3850_812_812_220 p3850_812_1032_220
private theorem p3850_812_1472_440 : blockEstimate 3850 812 1472 440 = 0x747b12e176 :=
  append_checked p3850_812_1472_220 p3850_812_1692_220
private theorem p3850_812_1252_660 : blockEstimate 3850 812 1252 660 = 0x8e5f0f463f :=
  append_checked p3850_812_1252_220 p3850_812_1472_440
private theorem p3850_812_812_1100 : blockEstimate 3850 812 812 1100 = 0x9a16c20a05 :=
  append_checked p3850_812_812_440 p3850_812_1252_660
private theorem p3850_812_2132_440 : blockEstimate 3850 812 2132 440 = 0xd8f9f87618 :=
  append_checked p3850_812_2132_220 p3850_812_2352_220
private theorem p3850_812_1912_660 : blockEstimate 3850 812 1912 660 = 0x13145b47e64 :=
  append_checked p3850_812_1912_220 p3850_812_2132_440
private theorem p3850_812_2792_440 : blockEstimate 3850 812 2792 440 = 0xf557505198 :=
  append_checked p3850_812_2792_220 p3850_812_3012_220
private theorem p3850_812_2572_660 : blockEstimate 3850 812 2572 660 = 0x16df59a2464 :=
  append_checked p3850_812_2572_220 p3850_812_2792_440
private theorem p3850_812_1912_1320 : blockEstimate 3850 812 1912 1320 = 0x29f3b4ea2c8 :=
  append_checked p3850_812_1912_660 p3850_812_2572_660
private theorem p3850_812_812_2420 : blockEstimate 3850 812 812 2420 = 0x3395210accd :=
  append_checked p3850_812_812_1100 p3850_812_1912_1320
private theorem p3850_812_3232_440 : blockEstimate 3850 812 3232 440 = 0xdff0788798 :=
  append_checked p3850_812_3232_220 p3850_812_3452_220
private theorem p3850_812_3892_440 : blockEstimate 3850 812 3892 440 = 0x895a4d2396 :=
  append_checked p3850_812_3892_220 p3850_812_4112_220
private theorem p3850_812_3672_660 : blockEstimate 3850 812 3672 660 = 0xe738e6de76 :=
  append_checked p3850_812_3672_220 p3850_812_3892_440
private theorem p3850_812_3232_1100 : blockEstimate 3850 812 3232 1100 = 0x1c7295f660e :=
  append_checked p3850_812_3232_440 p3850_812_3672_660
private theorem p3850_812_4552_440 : blockEstimate 3850 812 4552 440 = 0x2c40ce4ff2 :=
  append_checked p3850_812_4552_220 p3850_812_4772_220
private theorem p3850_812_4332_660 : blockEstimate 3850 812 4332 660 = 0x57b0059ed3 :=
  append_checked p3850_812_4332_220 p3850_812_4552_440
private theorem p3850_812_5212_262 : blockEstimate 3850 812 5212 262 = 0x152c1ee69 :=
  append_checked p3850_812_5212_220 p3850_812_5432_42
private theorem p3850_812_4992_482 : blockEstimate 3850 812 4992 482 = 0x7f2fbf991 :=
  append_checked p3850_812_4992_220 p3850_812_5212_262
private theorem p3850_812_4332_1142 : blockEstimate 3850 812 4332 1142 = 0x5fa3019864 :=
  append_checked p3850_812_4332_660 p3850_812_4992_482
private theorem p3850_812_3232_2242 : blockEstimate 3850 812 3232 2242 = 0x226cc60fe72 :=
  append_checked p3850_812_3232_1100 p3850_812_4332_1142
private theorem p3850_812_812_4662 : blockEstimate 3850 812 812 4662 = 0x5601e71ab3f :=
  append_checked p3850_812_812_2420 p3850_812_3232_2242

theorem moment3850_812 : momentEstimate 3850 812 = 0x5601e71ab3f := p3850_812_812_4662
end Peer653High53BankProof
