import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Banks
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_6 (append)

private theorem p1411 : blockEstimate 6675 1411 1411 128 = 0x8c4ec0a0 := by decide +kernel
private theorem p1539 : blockEstimate 6675 1411 1539 128 = 0x3b90390a0 := by decide +kernel
private theorem p1667 : blockEstimate 6675 1411 1667 128 = 0x9dfe860a0 := by decide +kernel
private theorem p1795 : blockEstimate 6675 1411 1795 128 = 0x12d0fd30a0 := by decide +kernel
private theorem p1923 : blockEstimate 6675 1411 1923 128 = 0x1e5c4200a0 := by decide +kernel
private theorem p2051 : blockEstimate 6675 1411 2051 128 = 0x2c51b6d0a0 := by decide +kernel
private theorem p2179 : blockEstimate 6675 1411 2179 128 = 0x3c815ba0a0 := by decide +kernel
private theorem p2307 : blockEstimate 6675 1411 2307 128 = 0x4ebb3070a0 := by decide +kernel
private theorem p2435 : blockEstimate 6675 1411 2435 128 = 0x62cf3540a0 := by decide +kernel
private theorem p2563 : blockEstimate 6675 1411 2563 128 = 0x788d6a10a0 := by decide +kernel
private theorem p2691 : blockEstimate 6675 1411 2691 128 = 0x8fc5cee0a0 := by decide +kernel
private theorem p2819 : blockEstimate 6675 1411 2819 128 = 0xa7e411f0cb := by decide +kernel
private theorem p2947 : blockEstimate 6675 1411 2947 128 = 0xbf19161e80 := by decide +kernel
private theorem p3075 : blockEstimate 6675 1411 3075 128 = 0xd4ed1a9e80 := by decide +kernel
private theorem p3203 : blockEstimate 6675 1411 3203 128 = 0xe9601f1e80 := by decide +kernel
private theorem p3331 : blockEstimate 6675 1411 3331 128 = 0xfc72239e80 := by decide +kernel
private theorem p3459 : blockEstimate 6675 1411 3459 128 = 0x10e23281e80 := by decide +kernel
private theorem p3587 : blockEstimate 6675 1411 3587 128 = 0x11e732c9e80 := by decide +kernel
private theorem p3715 : blockEstimate 6675 1411 3715 128 = 0x12d62311e80 := by decide +kernel
private theorem p3843 : blockEstimate 6675 1411 3843 128 = 0x13af0359e80 := by decide +kernel
private theorem p3971 : blockEstimate 6675 1411 3971 128 = 0x1471d3a1e80 := by decide +kernel
private theorem p4099 : blockEstimate 6675 1411 4099 128 = 0x151e93e9e80 := by decide +kernel
private theorem p4227 : blockEstimate 6675 1411 4227 128 = 0x15b54431e80 := by decide +kernel
private theorem p4355 : blockEstimate 6675 1411 4355 128 = 0x1635e479e80 := by decide +kernel
private theorem p4483 : blockEstimate 6675 1411 4483 128 = 0x16a074c1e80 := by decide +kernel
private theorem p4611 : blockEstimate 6675 1411 4611 128 = 0x16f4f509e80 := by decide +kernel
private theorem p4739 : blockEstimate 6675 1411 4739 128 = 0x17336551e80 := by decide +kernel
private theorem p4867 : blockEstimate 6675 1411 4867 128 = 0x175bc599e80 := by decide +kernel
private theorem p4995 : blockEstimate 6675 1411 4995 128 = 0x176e15e1e80 := by decide +kernel
private theorem p5123 : blockEstimate 6675 1411 5123 128 = 0x176a5629e80 := by decide +kernel
private theorem p5251 : blockEstimate 6675 1411 5251 128 = 0x17508671e80 := by decide +kernel
private theorem p5379 : blockEstimate 6675 1411 5379 128 = 0x1720a6b9e80 := by decide +kernel
private theorem p5507 : blockEstimate 6675 1411 5507 128 = 0x16dab701e80 := by decide +kernel
private theorem p5635 : blockEstimate 6675 1411 5635 128 = 0x167eb749e80 := by decide +kernel
private theorem p5763 : blockEstimate 6675 1411 5763 128 = 0x160ca791e80 := by decide +kernel
private theorem p5891 : blockEstimate 6675 1411 5891 128 = 0x158487d9e80 := by decide +kernel
private theorem p6019 : blockEstimate 6675 1411 6019 128 = 0x14e65821e80 := by decide +kernel
private theorem p6147 : blockEstimate 6675 1411 6147 128 = 0x14321869e80 := by decide +kernel
private theorem p6275 : blockEstimate 6675 1411 6275 128 = 0x1367c8b1e80 := by decide +kernel
private theorem p6403 : blockEstimate 6675 1411 6403 128 = 0x128768f9e80 := by decide +kernel
private theorem p6531 : blockEstimate 6675 1411 6531 128 = 0x1190f941e80 := by decide +kernel
private theorem p6659 : blockEstimate 6675 1411 6659 128 = 0x10863ba4d30 := by decide +kernel
private theorem p6787 : blockEstimate 6675 1411 6787 128 = 0xf71f24234b := by decide +kernel
private theorem p6915 : blockEstimate 6675 1411 6915 128 = 0xe59abc748e := by decide +kernel
private theorem p7043 : blockEstimate 6675 1411 7043 128 = 0xd3f889f915 := by decide +kernel
private theorem p7171 : blockEstimate 6675 1411 7171 128 = 0xc2596af8c4 := by decide +kernel
private theorem p7299 : blockEstimate 6675 1411 7299 128 = 0xb0dd273e8a := by decide +kernel
private theorem p7427 : blockEstimate 6675 1411 7427 128 = 0x9fa2701a4a := by decide +kernel
private theorem p7555 : blockEstimate 6675 1411 7555 128 = 0x8ec6e061da := by decide +kernel
private theorem p7683 : blockEstimate 6675 1411 7683 128 = 0x7e66fc70b3 := by decide +kernel
private theorem p7811 : blockEstimate 6675 1411 7811 128 = 0x6e9e322441 := by decide +kernel
private theorem p7939 : blockEstimate 6675 1411 7939 128 = 0x5f86d8de90 := by decide +kernel
private theorem p8067 : blockEstimate 6675 1411 8067 128 = 0x51272140be := by decide +kernel
private theorem p8195 : blockEstimate 6675 1411 8195 128 = 0x43997b72d0 := by decide +kernel
private theorem p8323 : blockEstimate 6675 1411 8323 128 = 0x371b334ed0 := by decide +kernel
private theorem p8451 : blockEstimate 6675 1411 8451 128 = 0x2bbbf02ad0 := by decide +kernel
private theorem p8579 : blockEstimate 6675 1411 8579 128 = 0x218ab206d0 := by decide +kernel
private theorem p8707 : blockEstimate 6675 1411 8707 128 = 0x189678e2d0 := by decide +kernel
private theorem p8835 : blockEstimate 6675 1411 8835 128 = 0x10ee44bed0 := by decide +kernel
private theorem p8963 : blockEstimate 6675 1411 8963 128 = 0xaa1159ad0 := by decide +kernel
private theorem p9091 : blockEstimate 6675 1411 9091 128 = 0x5bdeb76d0 := by decide +kernel
private theorem p9219 : blockEstimate 6675 1411 9219 128 = 0x253c652d0 := by decide +kernel
private theorem p9347 : blockEstimate 6675 1411 9347 128 = 0x71a62ed0 := by decide +kernel
private theorem p9475 : blockEstimate 6675 1411 9475 22 = 0x6da34d := by decide +kernel

private theorem sum_1411_256 : blockEstimate 6675 1411 1411 256 = 0x445525140 :=
  append (B := 6675) (J := 1411) (start := 1411) (a := 128) (x := 0x8c4ec0a0)
    p1411 1539 128 0x3b90390a0 256 0x445525140 rfl rfl rfl p1539

private theorem sum_1667_256 : blockEstimate 6675 1411 1667 256 = 0x1cb0e59140 :=
  append (B := 6675) (J := 1411) (start := 1667) (a := 128) (x := 0x9dfe860a0)
    p1667 1795 128 0x12d0fd30a0 256 0x1cb0e59140 rfl rfl rfl p1795

private theorem sum_1923_256 : blockEstimate 6675 1411 1923 256 = 0x4aadf8d140 :=
  append (B := 6675) (J := 1411) (start := 1923) (a := 128) (x := 0x1e5c4200a0)
    p1923 2051 128 0x2c51b6d0a0 256 0x4aadf8d140 rfl rfl rfl p2051

private theorem sum_2179_256 : blockEstimate 6675 1411 2179 256 = 0x8b3c8c1140 :=
  append (B := 6675) (J := 1411) (start := 2179) (a := 128) (x := 0x3c815ba0a0)
    p2179 2307 128 0x4ebb3070a0 256 0x8b3c8c1140 rfl rfl rfl p2307

private theorem sum_2435_256 : blockEstimate 6675 1411 2435 256 = 0xdb5c9f5140 :=
  append (B := 6675) (J := 1411) (start := 2435) (a := 128) (x := 0x62cf3540a0)
    p2435 2563 128 0x788d6a10a0 256 0xdb5c9f5140 rfl rfl rfl p2563

private theorem sum_2691_256 : blockEstimate 6675 1411 2691 256 = 0x137a9e0d16b :=
  append (B := 6675) (J := 1411) (start := 2691) (a := 128) (x := 0x8fc5cee0a0)
    p2691 2819 128 0xa7e411f0cb 256 0x137a9e0d16b rfl rfl rfl p2819

private theorem sum_2947_256 : blockEstimate 6675 1411 2947 256 = 0x1940630bd00 :=
  append (B := 6675) (J := 1411) (start := 2947) (a := 128) (x := 0xbf19161e80)
    p2947 3075 128 0xd4ed1a9e80 256 0x1940630bd00 rfl rfl rfl p3075

private theorem sum_3203_256 : blockEstimate 6675 1411 3203 256 = 0x1e5d242bd00 :=
  append (B := 6675) (J := 1411) (start := 3203) (a := 128) (x := 0xe9601f1e80)
    p3203 3331 128 0xfc72239e80 256 0x1e5d242bd00 rfl rfl rfl p3331

private theorem sum_3459_256 : blockEstimate 6675 1411 3459 256 = 0x22c9654bd00 :=
  append (B := 6675) (J := 1411) (start := 3459) (a := 128) (x := 0x10e23281e80)
    p3459 3587 128 0x11e732c9e80 256 0x22c9654bd00 rfl rfl rfl p3587

private theorem sum_3715_256 : blockEstimate 6675 1411 3715 256 = 0x2685266bd00 :=
  append (B := 6675) (J := 1411) (start := 3715) (a := 128) (x := 0x12d62311e80)
    p3715 3843 128 0x13af0359e80 256 0x2685266bd00 rfl rfl rfl p3843

private theorem sum_3971_256 : blockEstimate 6675 1411 3971 256 = 0x2990678bd00 :=
  append (B := 6675) (J := 1411) (start := 3971) (a := 128) (x := 0x1471d3a1e80)
    p3971 4099 128 0x151e93e9e80 256 0x2990678bd00 rfl rfl rfl p4099

private theorem sum_4227_256 : blockEstimate 6675 1411 4227 256 = 0x2beb28abd00 :=
  append (B := 6675) (J := 1411) (start := 4227) (a := 128) (x := 0x15b54431e80)
    p4227 4355 128 0x1635e479e80 256 0x2beb28abd00 rfl rfl rfl p4355

private theorem sum_4483_256 : blockEstimate 6675 1411 4483 256 = 0x2d9569cbd00 :=
  append (B := 6675) (J := 1411) (start := 4483) (a := 128) (x := 0x16a074c1e80)
    p4483 4611 128 0x16f4f509e80 256 0x2d9569cbd00 rfl rfl rfl p4611

private theorem sum_4739_256 : blockEstimate 6675 1411 4739 256 = 0x2e8f2aebd00 :=
  append (B := 6675) (J := 1411) (start := 4739) (a := 128) (x := 0x17336551e80)
    p4739 4867 128 0x175bc599e80 256 0x2e8f2aebd00 rfl rfl rfl p4867

private theorem sum_4995_256 : blockEstimate 6675 1411 4995 256 = 0x2ed86c0bd00 :=
  append (B := 6675) (J := 1411) (start := 4995) (a := 128) (x := 0x176e15e1e80)
    p4995 5123 128 0x176a5629e80 256 0x2ed86c0bd00 rfl rfl rfl p5123

private theorem sum_5251_256 : blockEstimate 6675 1411 5251 256 = 0x2e712d2bd00 :=
  append (B := 6675) (J := 1411) (start := 5251) (a := 128) (x := 0x17508671e80)
    p5251 5379 128 0x1720a6b9e80 256 0x2e712d2bd00 rfl rfl rfl p5379

private theorem sum_5507_256 : blockEstimate 6675 1411 5507 256 = 0x2d596e4bd00 :=
  append (B := 6675) (J := 1411) (start := 5507) (a := 128) (x := 0x16dab701e80)
    p5507 5635 128 0x167eb749e80 256 0x2d596e4bd00 rfl rfl rfl p5635

private theorem sum_5763_256 : blockEstimate 6675 1411 5763 256 = 0x2b912f6bd00 :=
  append (B := 6675) (J := 1411) (start := 5763) (a := 128) (x := 0x160ca791e80)
    p5763 5891 128 0x158487d9e80 256 0x2b912f6bd00 rfl rfl rfl p5891

private theorem sum_6019_256 : blockEstimate 6675 1411 6019 256 = 0x2918708bd00 :=
  append (B := 6675) (J := 1411) (start := 6019) (a := 128) (x := 0x14e65821e80)
    p6019 6147 128 0x14321869e80 256 0x2918708bd00 rfl rfl rfl p6147

private theorem sum_6275_256 : blockEstimate 6675 1411 6275 256 = 0x25ef31abd00 :=
  append (B := 6675) (J := 1411) (start := 6275) (a := 128) (x := 0x1367c8b1e80)
    p6275 6403 128 0x128768f9e80 256 0x25ef31abd00 rfl rfl rfl p6403

private theorem sum_6531_256 : blockEstimate 6675 1411 6531 256 = 0x221734e6bb0 :=
  append (B := 6675) (J := 1411) (start := 6531) (a := 128) (x := 0x1190f941e80)
    p6531 6659 128 0x10863ba4d30 256 0x221734e6bb0 rfl rfl rfl p6659

private theorem sum_6787_256 : blockEstimate 6675 1411 6787 256 = 0x1dcb9e097d9 :=
  append (B := 6675) (J := 1411) (start := 6787) (a := 128) (x := 0xf71f24234b)
    p6787 6915 128 0xe59abc748e 256 0x1dcb9e097d9 rfl rfl rfl p6915

private theorem sum_7043_256 : blockEstimate 6675 1411 7043 256 = 0x19651f4f1d9 :=
  append (B := 6675) (J := 1411) (start := 7043) (a := 128) (x := 0xd3f889f915)
    p7043 7171 128 0xc2596af8c4 256 0x19651f4f1d9 rfl rfl rfl p7171

private theorem sum_7299_256 : blockEstimate 6675 1411 7299 256 = 0x1507f9758d4 :=
  append (B := 6675) (J := 1411) (start := 7299) (a := 128) (x := 0xb0dd273e8a)
    p7299 7427 128 0x9fa2701a4a 256 0x1507f9758d4 rfl rfl rfl p7427

private theorem sum_7555_256 : blockEstimate 6675 1411 7555 256 = 0x10d2ddcd28d :=
  append (B := 6675) (J := 1411) (start := 7555) (a := 128) (x := 0x8ec6e061da)
    p7555 7683 128 0x7e66fc70b3 256 0x10d2ddcd28d rfl rfl rfl p7683

private theorem sum_7811_256 : blockEstimate 6675 1411 7811 256 = 0xce250b02d1 :=
  append (B := 6675) (J := 1411) (start := 7811) (a := 128) (x := 0x6e9e322441)
    p7811 7939 128 0x5f86d8de90 256 0xce250b02d1 rfl rfl rfl p7939

private theorem sum_8067_256 : blockEstimate 6675 1411 8067 256 = 0x94c09cb38e :=
  append (B := 6675) (J := 1411) (start := 8067) (a := 128) (x := 0x51272140be)
    p8067 8195 128 0x43997b72d0 256 0x94c09cb38e rfl rfl rfl p8195

private theorem sum_8323_256 : blockEstimate 6675 1411 8323 256 = 0x62d72379a0 :=
  append (B := 6675) (J := 1411) (start := 8323) (a := 128) (x := 0x371b334ed0)
    p8323 8451 128 0x2bbbf02ad0 256 0x62d72379a0 rfl rfl rfl p8451

private theorem sum_8579_256 : blockEstimate 6675 1411 8579 256 = 0x3a212ae9a0 :=
  append (B := 6675) (J := 1411) (start := 8579) (a := 128) (x := 0x218ab206d0)
    p8579 8707 128 0x189678e2d0 256 0x3a212ae9a0 rfl rfl rfl p8707

private theorem sum_8835_256 : blockEstimate 6675 1411 8835 256 = 0x1b8f5a59a0 :=
  append (B := 6675) (J := 1411) (start := 8835) (a := 128) (x := 0x10ee44bed0)
    p8835 8963 128 0xaa1159ad0 256 0x1b8f5a59a0 rfl rfl rfl p8963

private theorem sum_9091_256 : blockEstimate 6675 1411 9091 256 = 0x811b1c9a0 :=
  append (B := 6675) (J := 1411) (start := 9091) (a := 128) (x := 0x5bdeb76d0)
    p9091 9219 128 0x253c652d0 256 0x811b1c9a0 rfl rfl rfl p9219

private theorem sum_9347_150 : blockEstimate 6675 1411 9347 150 = 0x7213d21d :=
  append (B := 6675) (J := 1411) (start := 9347) (a := 128) (x := 0x71a62ed0)
    p9347 9475 22 0x6da34d 150 0x7213d21d rfl rfl rfl p9475

private theorem sum_1411_512 : blockEstimate 6675 1411 1411 512 = 0x20f637e280 :=
  append (B := 6675) (J := 1411) (start := 1411) (a := 256) (x := 0x445525140)
    sum_1411_256 1667 256 0x1cb0e59140 512 0x20f637e280 rfl rfl rfl sum_1667_256

private theorem sum_1923_512 : blockEstimate 6675 1411 1923 512 = 0xd5ea84e280 :=
  append (B := 6675) (J := 1411) (start := 1923) (a := 256) (x := 0x4aadf8d140)
    sum_1923_256 2179 256 0x8b3c8c1140 512 0xd5ea84e280 rfl rfl rfl sum_2179_256

private theorem sum_2435_512 : blockEstimate 6675 1411 2435 512 = 0x213068022ab :=
  append (B := 6675) (J := 1411) (start := 2435) (a := 256) (x := 0xdb5c9f5140)
    sum_2435_256 2691 256 0x137a9e0d16b 512 0x213068022ab rfl rfl rfl sum_2691_256

private theorem sum_2947_512 : blockEstimate 6675 1411 2947 512 = 0x379d8737a00 :=
  append (B := 6675) (J := 1411) (start := 2947) (a := 256) (x := 0x1940630bd00)
    sum_2947_256 3203 256 0x1e5d242bd00 512 0x379d8737a00 rfl rfl rfl sum_3203_256

private theorem sum_3459_512 : blockEstimate 6675 1411 3459 512 = 0x494e8bb7a00 :=
  append (B := 6675) (J := 1411) (start := 3459) (a := 256) (x := 0x22c9654bd00)
    sum_3459_256 3715 256 0x2685266bd00 512 0x494e8bb7a00 rfl rfl rfl sum_3715_256

private theorem sum_3971_512 : blockEstimate 6675 1411 3971 512 = 0x557b9037a00 :=
  append (B := 6675) (J := 1411) (start := 3971) (a := 256) (x := 0x2990678bd00)
    sum_3971_256 4227 256 0x2beb28abd00 512 0x557b9037a00 rfl rfl rfl sum_4227_256

private theorem sum_4483_512 : blockEstimate 6675 1411 4483 512 = 0x5c2494b7a00 :=
  append (B := 6675) (J := 1411) (start := 4483) (a := 256) (x := 0x2d9569cbd00)
    sum_4483_256 4739 256 0x2e8f2aebd00 512 0x5c2494b7a00 rfl rfl rfl sum_4739_256

private theorem sum_4995_512 : blockEstimate 6675 1411 4995 512 = 0x5d499937a00 :=
  append (B := 6675) (J := 1411) (start := 4995) (a := 256) (x := 0x2ed86c0bd00)
    sum_4995_256 5251 256 0x2e712d2bd00 512 0x5d499937a00 rfl rfl rfl sum_5251_256

private theorem sum_5507_512 : blockEstimate 6675 1411 5507 512 = 0x58ea9db7a00 :=
  append (B := 6675) (J := 1411) (start := 5507) (a := 256) (x := 0x2d596e4bd00)
    sum_5507_256 5763 256 0x2b912f6bd00 512 0x58ea9db7a00 rfl rfl rfl sum_5763_256

private theorem sum_6019_512 : blockEstimate 6675 1411 6019 512 = 0x4f07a237a00 :=
  append (B := 6675) (J := 1411) (start := 6019) (a := 256) (x := 0x2918708bd00)
    sum_6019_256 6275 256 0x25ef31abd00 512 0x4f07a237a00 rfl rfl rfl sum_6275_256

private theorem sum_6531_512 : blockEstimate 6675 1411 6531 512 = 0x3fe2d2f0389 :=
  append (B := 6675) (J := 1411) (start := 6531) (a := 256) (x := 0x221734e6bb0)
    sum_6531_256 6787 256 0x1dcb9e097d9 512 0x3fe2d2f0389 rfl rfl rfl sum_6787_256

private theorem sum_7043_512 : blockEstimate 6675 1411 7043 512 = 0x2e6d18c4aad :=
  append (B := 6675) (J := 1411) (start := 7043) (a := 256) (x := 0x19651f4f1d9)
    sum_7043_256 7299 256 0x1507f9758d4 512 0x2e6d18c4aad rfl rfl rfl sum_7299_256

private theorem sum_7555_512 : blockEstimate 6675 1411 7555 512 = 0x1db52e7d55e :=
  append (B := 6675) (J := 1411) (start := 7555) (a := 256) (x := 0x10d2ddcd28d)
    sum_7555_256 7811 256 0xce250b02d1 512 0x1db52e7d55e rfl rfl rfl sum_7811_256

private theorem sum_8067_512 : blockEstimate 6675 1411 8067 512 = 0xf797c02d2e :=
  append (B := 6675) (J := 1411) (start := 8067) (a := 256) (x := 0x94c09cb38e)
    sum_8067_256 8323 256 0x62d72379a0 512 0xf797c02d2e rfl rfl rfl sum_8323_256

private theorem sum_8579_512 : blockEstimate 6675 1411 8579 512 = 0x55b0854340 :=
  append (B := 6675) (J := 1411) (start := 8579) (a := 256) (x := 0x3a212ae9a0)
    sum_8579_256 8835 256 0x1b8f5a59a0 512 0x55b0854340 rfl rfl rfl sum_8835_256

private theorem sum_9091_406 : blockEstimate 6675 1411 9091 406 = 0x883c59bbd :=
  append (B := 6675) (J := 1411) (start := 9091) (a := 256) (x := 0x811b1c9a0)
    sum_9091_256 9347 150 0x7213d21d 406 0x883c59bbd rfl rfl rfl sum_9347_150

private theorem sum_1411_1024 : blockEstimate 6675 1411 1411 1024 = 0xf6e0bcc500 :=
  append (B := 6675) (J := 1411) (start := 1411) (a := 512) (x := 0x20f637e280)
    sum_1411_512 1923 512 0xd5ea84e280 1024 0xf6e0bcc500 rfl rfl rfl sum_1923_512

private theorem sum_2435_1024 : blockEstimate 6675 1411 2435 1024 = 0x58cdef39cab :=
  append (B := 6675) (J := 1411) (start := 2435) (a := 512) (x := 0x213068022ab)
    sum_2435_512 2947 512 0x379d8737a00 1024 0x58cdef39cab rfl rfl rfl sum_2947_512

private theorem sum_3459_1024 : blockEstimate 6675 1411 3459 1024 = 0x9eca1bef400 :=
  append (B := 6675) (J := 1411) (start := 3459) (a := 512) (x := 0x494e8bb7a00)
    sum_3459_512 3971 512 0x557b9037a00 1024 0x9eca1bef400 rfl rfl rfl sum_3971_512

private theorem sum_4483_1024 : blockEstimate 6675 1411 4483 1024 = 0xb96e2def400 :=
  append (B := 6675) (J := 1411) (start := 4483) (a := 512) (x := 0x5c2494b7a00)
    sum_4483_512 4995 512 0x5d499937a00 1024 0xb96e2def400 rfl rfl rfl sum_4995_512

private theorem sum_5507_1024 : blockEstimate 6675 1411 5507 1024 = 0xa7f23fef400 :=
  append (B := 6675) (J := 1411) (start := 5507) (a := 512) (x := 0x58ea9db7a00)
    sum_5507_512 6019 512 0x4f07a237a00 1024 0xa7f23fef400 rfl rfl rfl sum_6019_512

private theorem sum_6531_1024 : blockEstimate 6675 1411 6531 1024 = 0x6e4febb4e36 :=
  append (B := 6675) (J := 1411) (start := 6531) (a := 512) (x := 0x3fe2d2f0389)
    sum_6531_512 7043 512 0x2e6d18c4aad 1024 0x6e4febb4e36 rfl rfl rfl sum_7043_512

private theorem sum_7555_1024 : blockEstimate 6675 1411 7555 1024 = 0x2d2eaa8028c :=
  append (B := 6675) (J := 1411) (start := 7555) (a := 512) (x := 0x1db52e7d55e)
    sum_7555_512 8067 512 0xf797c02d2e 1024 0x2d2eaa8028c rfl rfl rfl sum_8067_512

private theorem sum_8579_918 : blockEstimate 6675 1411 8579 918 = 0x5e344adefd :=
  append (B := 6675) (J := 1411) (start := 8579) (a := 512) (x := 0x55b0854340)
    sum_8579_512 9091 406 0x883c59bbd 918 0x5e344adefd rfl rfl rfl sum_9091_406

private theorem sum_1411_2048 : blockEstimate 6675 1411 1411 2048 = 0x683bfb061ab :=
  append (B := 6675) (J := 1411) (start := 1411) (a := 1024) (x := 0xf6e0bcc500)
    sum_1411_1024 2435 1024 0x58cdef39cab 2048 0x683bfb061ab rfl rfl rfl sum_2435_1024

private theorem sum_3459_2048 : blockEstimate 6675 1411 3459 2048 = 0x1583849de800 :=
  append (B := 6675) (J := 1411) (start := 3459) (a := 1024) (x := 0x9eca1bef400)
    sum_3459_1024 4483 1024 0xb96e2def400 2048 0x1583849de800 rfl rfl rfl sum_4483_1024

private theorem sum_5507_2048 : blockEstimate 6675 1411 5507 2048 = 0x116422ba4236 :=
  append (B := 6675) (J := 1411) (start := 5507) (a := 1024) (x := 0xa7f23fef400)
    sum_5507_1024 6531 1024 0x6e4febb4e36 2048 0x116422ba4236 rfl rfl rfl sum_6531_1024

private theorem sum_7555_1942 : blockEstimate 6675 1411 7555 1942 = 0x3311ef2e189 :=
  append (B := 6675) (J := 1411) (start := 7555) (a := 1024) (x := 0x2d2eaa8028c)
    sum_7555_1024 8579 918 0x5e344adefd 1942 0x3311ef2e189 rfl rfl rfl sum_8579_918

private theorem sum_1411_4096 : blockEstimate 6675 1411 1411 4096 = 0x1c07444e49ab :=
  append (B := 6675) (J := 1411) (start := 1411) (a := 2048) (x := 0x683bfb061ab)
    sum_1411_2048 3459 2048 0x1583849de800 4096 0x1c07444e49ab rfl rfl rfl sum_3459_2048

private theorem sum_5507_3990 : blockEstimate 6675 1411 5507 3990 = 0x149541ad23bf :=
  append (B := 6675) (J := 1411) (start := 5507) (a := 2048) (x := 0x116422ba4236)
    sum_5507_2048 7555 1942 0x3311ef2e189 3990 0x149541ad23bf rfl rfl rfl sum_7555_1942

private theorem sum_1411_8086 : blockEstimate 6675 1411 1411 8086 = 0x309c85fb6d6a :=
  append (B := 6675) (J := 1411) (start := 1411) (a := 4096) (x := 0x1c07444e49ab)
    sum_1411_4096 5507 3990 0x149541ad23bf 8086 0x309c85fb6d6a rfl rfl rfl sum_5507_3990

theorem moment6675_1411 : momentEstimate 6675 1411 = 0x309c85fb6d6a := by
  change blockEstimate 6675 1411 1411 8086 = 0x309c85fb6d6a
  exact sum_1411_8086

end KoalaH2430Banks
