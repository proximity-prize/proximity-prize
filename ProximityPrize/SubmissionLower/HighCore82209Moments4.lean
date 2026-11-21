import ProximityPrize.SubmissionLower.HighCore82209Moments3

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82209BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)
open P1_7_1_3_2 (moment_from_blocks)
open scoped P1_7_1_3_2
set_option maxHeartbeats 14000000


private theorem part8413_1776_0 : blockEstimate 8413 1776 1776 220 = 0x374794475 := by decide +kernel
private theorem part8413_1776_1 : blockEstimate 8413 1776 1996 220 = 0x1772ecf4e9 := by decide +kernel
private theorem part8413_1776_2 : blockEstimate 8413 1776 2216 220 = 0x3dd79534fd := by decide +kernel
private theorem part8413_1776_3 : blockEstimate 8413 1776 2436 220 = 0x74ff9021b1 := by decide +kernel
private theorem part8413_1776_4 : blockEstimate 8413 1776 2656 220 = 0xbb47fbd805 := by decide +kernel
private theorem part8413_1776_5 : blockEstimate 8413 1776 2876 220 = 0x10f0df674f9 := by decide +kernel
private theorem part8413_1776_6 : blockEstimate 8413 1776 3096 220 = 0x16eae9e158d := by decide +kernel
private theorem part8413_1776_7 : blockEstimate 8413 1776 3316 220 = 0x1d88710d6c1 := by decide +kernel
private theorem part8413_1776_8 : blockEstimate 8413 1776 3536 220 = 0x248d18db0be := by decide +kernel
private theorem part8413_1776_9 : blockEstimate 8413 1776 3756 220 = 0x2b3c5696bd2 := by decide +kernel
private theorem part8413_1776_10 : blockEstimate 8413 1776 3976 220 = 0x315e9ebea22 := by decide +kernel
private theorem part8413_1776_11 : blockEstimate 8413 1776 4196 220 = 0x36f3ed02cf2 := by decide +kernel
private theorem part8413_1776_12 : blockEstimate 8413 1776 4416 220 = 0x3bfc4163442 := by decide +kernel
private theorem part8413_1776_13 : blockEstimate 8413 1776 4636 220 = 0x40779be0012 := by decide +kernel
private theorem part8413_1776_14 : blockEstimate 8413 1776 4856 220 = 0x4465fc79062 := by decide +kernel
private theorem part8413_1776_15 : blockEstimate 8413 1776 5076 220 = 0x47c7632e532 := by decide +kernel
private theorem part8413_1776_16 : blockEstimate 8413 1776 5296 220 = 0x4a9bcfffe82 := by decide +kernel
private theorem part8413_1776_17 : blockEstimate 8413 1776 5516 220 = 0x4ce342edc52 := by decide +kernel
private theorem part8413_1776_18 : blockEstimate 8413 1776 5736 220 = 0x4e9dbbf7ea2 := by decide +kernel
private theorem part8413_1776_19 : blockEstimate 8413 1776 5956 220 = 0x4fcb3b1e572 := by decide +kernel
private theorem part8413_1776_20 : blockEstimate 8413 1776 6176 220 = 0x506bc0610c2 := by decide +kernel
private theorem part8413_1776_21 : blockEstimate 8413 1776 6396 220 = 0x507f4bc0092 := by decide +kernel
private theorem part8413_1776_22 : blockEstimate 8413 1776 6616 220 = 0x5005dd3b4e2 := by decide +kernel
private theorem part8413_1776_23 : blockEstimate 8413 1776 6836 220 = 0x4eff74d2db2 := by decide +kernel
private theorem part8413_1776_24 : blockEstimate 8413 1776 7056 220 = 0x4d6c1286b02 := by decide +kernel
private theorem part8413_1776_25 : blockEstimate 8413 1776 7276 220 = 0x4b4bb656cd2 := by decide +kernel
private theorem part8413_1776_26 : blockEstimate 8413 1776 7496 220 = 0x489e6043322 := by decide +kernel
private theorem part8413_1776_27 : blockEstimate 8413 1776 7716 220 = 0x4564104bdf2 := by decide +kernel
private theorem part8413_1776_28 : blockEstimate 8413 1776 7936 220 = 0x419cc670d42 := by decide +kernel
private theorem part8413_1776_29 : blockEstimate 8413 1776 8156 220 = 0x3d4882b2112 := by decide +kernel
private theorem part8413_1776_30 : blockEstimate 8413 1776 8376 220 = 0x3870fc56770 := by decide +kernel
private theorem part8413_1776_31 : blockEstimate 8413 1776 8596 220 = 0x335b94711c1 := by decide +kernel
private theorem part8413_1776_32 : blockEstimate 8413 1776 8816 220 = 0x2e32e5faca1 := by decide +kernel
private theorem part8413_1776_33 : blockEstimate 8413 1776 9036 220 = 0x290929ac799 := by decide +kernel
private theorem part8413_1776_34 : blockEstimate 8413 1776 9256 220 = 0x23efb637324 := by decide +kernel
private theorem part8413_1776_35 : blockEstimate 8413 1776 9476 220 = 0x1ef712dbfb8 := by decide +kernel
private theorem part8413_1776_36 : blockEstimate 8413 1776 9696 220 = 0x1a2ef76bf87 := by decide +kernel
private theorem part8413_1776_37 : blockEstimate 8413 1776 9916 220 = 0x15a64c4810a := by decide +kernel
private theorem part8413_1776_38 : blockEstimate 8413 1776 10136 220 = 0x1166e75959c := by decide +kernel
private theorem part8413_1776_39 : blockEstimate 8413 1776 10356 220 = 0xd7da7f3f3e := by decide +kernel
private theorem part8413_1776_40 : blockEstimate 8413 1776 10576 220 = 0xa02f4b9e37 := by decide +kernel
private theorem part8413_1776_41 : blockEstimate 8413 1776 10796 220 = 0x6ff85e6132 := by decide +kernel
private theorem part8413_1776_42 : blockEstimate 8413 1776 11016 220 = 0x47b89e1f1f := by decide +kernel
private theorem part8413_1776_43 : blockEstimate 8413 1776 11236 220 = 0x27f2f16eee := by decide +kernel
private theorem part8413_1776_44 : blockEstimate 8413 1776 11456 220 = 0x112a3ee78f := by decide +kernel
private theorem part8413_1776_45 : blockEstimate 8413 1776 11676 220 = 0x3e16d1ff2 := by decide +kernel
private theorem part8413_1776_46 : blockEstimate 8413 1776 11896 69 = 0xe9512bf := by decide +kernel

private theorem sum8413_1776_1776_440 : blockEstimate 8413 1776 1776 440 = 0x1ae766395e :=
  block_append (B := 8413) (J := 1776) (start := 1776) (next := 1996)
    (a := 220) (b := 220) (n := 440) (x := 0x374794475) (y := 0x1772ecf4e9) (z := 0x1ae766395e)
    part8413_1776_0 part8413_1776_1 rfl rfl rfl

private theorem sum8413_1776_2436_440 : blockEstimate 8413 1776 2436 440 = 0x130478bf9b6 :=
  block_append (B := 8413) (J := 1776) (start := 2436) (next := 2656)
    (a := 220) (b := 220) (n := 440) (x := 0x74ff9021b1) (y := 0xbb47fbd805) (z := 0x130478bf9b6)
    part8413_1776_3 part8413_1776_4 rfl rfl rfl

private theorem sum8413_1776_2216_660 : blockEstimate 8413 1776 2216 660 = 0x16e1f212eb3 :=
  block_append (B := 8413) (J := 1776) (start := 2216) (next := 2436)
    (a := 220) (b := 440) (n := 660) (x := 0x3dd79534fd) (y := 0x130478bf9b6) (z := 0x16e1f212eb3)
    part8413_1776_2 sum8413_1776_2436_440 rfl rfl rfl

private theorem sum8413_1776_1776_1100 : blockEstimate 8413 1776 1776 1100 = 0x18906876811 :=
  block_append (B := 8413) (J := 1776) (start := 1776) (next := 2216)
    (a := 440) (b := 660) (n := 1100) (x := 0x1ae766395e) (y := 0x16e1f212eb3) (z := 0x18906876811)
    sum8413_1776_1776_440 sum8413_1776_2216_660 rfl rfl rfl

private theorem sum8413_1776_3096_440 : blockEstimate 8413 1776 3096 440 = 0x34735aeec4e :=
  block_append (B := 8413) (J := 1776) (start := 3096) (next := 3316)
    (a := 220) (b := 220) (n := 440) (x := 0x16eae9e158d) (y := 0x1d88710d6c1) (z := 0x34735aeec4e)
    part8413_1776_6 part8413_1776_7 rfl rfl rfl

private theorem sum8413_1776_2876_660 : blockEstimate 8413 1776 2876 660 = 0x45643a56147 :=
  block_append (B := 8413) (J := 1776) (start := 2876) (next := 3096)
    (a := 220) (b := 440) (n := 660) (x := 0x10f0df674f9) (y := 0x34735aeec4e) (z := 0x45643a56147)
    part8413_1776_5 sum8413_1776_3096_440 rfl rfl rfl

private theorem sum8413_1776_3756_440 : blockEstimate 8413 1776 3756 440 = 0x5c9af5555f4 :=
  block_append (B := 8413) (J := 1776) (start := 3756) (next := 3976)
    (a := 220) (b := 220) (n := 440) (x := 0x2b3c5696bd2) (y := 0x315e9ebea22) (z := 0x5c9af5555f4)
    part8413_1776_9 part8413_1776_10 rfl rfl rfl

private theorem sum8413_1776_3536_660 : blockEstimate 8413 1776 3536 660 = 0x81280e306b2 :=
  block_append (B := 8413) (J := 1776) (start := 3536) (next := 3756)
    (a := 220) (b := 440) (n := 660) (x := 0x248d18db0be) (y := 0x5c9af5555f4) (z := 0x81280e306b2)
    part8413_1776_8 sum8413_1776_3756_440 rfl rfl rfl

private theorem sum8413_1776_2876_1320 : blockEstimate 8413 1776 2876 1320 = 0xc68c48867f9 :=
  block_append (B := 8413) (J := 1776) (start := 2876) (next := 3536)
    (a := 660) (b := 660) (n := 1320) (x := 0x45643a56147) (y := 0x81280e306b2) (z := 0xc68c48867f9)
    sum8413_1776_2876_660 sum8413_1776_3536_660 rfl rfl rfl

private theorem sum8413_1776_1776_2420 : blockEstimate 8413 1776 1776 2420 = 0xdf1cb0fd00a :=
  block_append (B := 8413) (J := 1776) (start := 1776) (next := 2876)
    (a := 1100) (b := 1320) (n := 2420) (x := 0x18906876811) (y := 0xc68c48867f9) (z := 0xdf1cb0fd00a)
    sum8413_1776_1776_1100 sum8413_1776_2876_1320 rfl rfl rfl

private theorem sum8413_1776_4416_440 : blockEstimate 8413 1776 4416 440 = 0x7c73dd43454 :=
  block_append (B := 8413) (J := 1776) (start := 4416) (next := 4636)
    (a := 220) (b := 220) (n := 440) (x := 0x3bfc4163442) (y := 0x40779be0012) (z := 0x7c73dd43454)
    part8413_1776_12 part8413_1776_13 rfl rfl rfl

private theorem sum8413_1776_4196_660 : blockEstimate 8413 1776 4196 660 = 0xb367ca46146 :=
  block_append (B := 8413) (J := 1776) (start := 4196) (next := 4416)
    (a := 220) (b := 440) (n := 660) (x := 0x36f3ed02cf2) (y := 0x7c73dd43454) (z := 0xb367ca46146)
    part8413_1776_11 sum8413_1776_4416_440 rfl rfl rfl

private theorem sum8413_1776_5076_440 : blockEstimate 8413 1776 5076 440 = 0x9263332e3b4 :=
  block_append (B := 8413) (J := 1776) (start := 5076) (next := 5296)
    (a := 220) (b := 220) (n := 440) (x := 0x47c7632e532) (y := 0x4a9bcfffe82) (z := 0x9263332e3b4)
    part8413_1776_15 part8413_1776_16 rfl rfl rfl

private theorem sum8413_1776_4856_660 : blockEstimate 8413 1776 4856 660 = 0xd6c92fa7416 :=
  block_append (B := 8413) (J := 1776) (start := 4856) (next := 5076)
    (a := 220) (b := 440) (n := 660) (x := 0x4465fc79062) (y := 0x9263332e3b4) (z := 0xd6c92fa7416)
    part8413_1776_14 sum8413_1776_5076_440 rfl rfl rfl

private theorem sum8413_1776_4196_1320 : blockEstimate 8413 1776 4196 1320 = 0x18a30f9ed55c :=
  block_append (B := 8413) (J := 1776) (start := 4196) (next := 4856)
    (a := 660) (b := 660) (n := 1320) (x := 0xb367ca46146) (y := 0xd6c92fa7416) (z := 0x18a30f9ed55c)
    sum8413_1776_4196_660 sum8413_1776_4856_660 rfl rfl rfl

private theorem sum8413_1776_5736_440 : blockEstimate 8413 1776 5736 440 = 0x9e68f716414 :=
  block_append (B := 8413) (J := 1776) (start := 5736) (next := 5956)
    (a := 220) (b := 220) (n := 440) (x := 0x4e9dbbf7ea2) (y := 0x4fcb3b1e572) (z := 0x9e68f716414)
    part8413_1776_18 part8413_1776_19 rfl rfl rfl

private theorem sum8413_1776_5516_660 : blockEstimate 8413 1776 5516 660 = 0xeb4c3a04066 :=
  block_append (B := 8413) (J := 1776) (start := 5516) (next := 5736)
    (a := 220) (b := 440) (n := 660) (x := 0x4ce342edc52) (y := 0x9e68f716414) (z := 0xeb4c3a04066)
    part8413_1776_17 sum8413_1776_5736_440 rfl rfl rfl

private theorem sum8413_1776_6396_440 : blockEstimate 8413 1776 6396 440 = 0xa08528fb574 :=
  block_append (B := 8413) (J := 1776) (start := 6396) (next := 6616)
    (a := 220) (b := 220) (n := 440) (x := 0x507f4bc0092) (y := 0x5005dd3b4e2) (z := 0xa08528fb574)
    part8413_1776_21 part8413_1776_22 rfl rfl rfl

private theorem sum8413_1776_6176_660 : blockEstimate 8413 1776 6176 660 = 0xf0f0e95c636 :=
  block_append (B := 8413) (J := 1776) (start := 6176) (next := 6396)
    (a := 220) (b := 440) (n := 660) (x := 0x506bc0610c2) (y := 0xa08528fb574) (z := 0xf0f0e95c636)
    part8413_1776_20 sum8413_1776_6396_440 rfl rfl rfl

private theorem sum8413_1776_5516_1320 : blockEstimate 8413 1776 5516 1320 = 0x1dc3d236069c :=
  block_append (B := 8413) (J := 1776) (start := 5516) (next := 6176)
    (a := 660) (b := 660) (n := 1320) (x := 0xeb4c3a04066) (y := 0xf0f0e95c636) (z := 0x1dc3d236069c)
    sum8413_1776_5516_660 sum8413_1776_6176_660 rfl rfl rfl

private theorem sum8413_1776_4196_2640 : blockEstimate 8413 1776 4196 2640 = 0x3666e1d4dbf8 :=
  block_append (B := 8413) (J := 1776) (start := 4196) (next := 5516)
    (a := 1320) (b := 1320) (n := 2640) (x := 0x18a30f9ed55c) (y := 0x1dc3d236069c) (z := 0x3666e1d4dbf8)
    sum8413_1776_4196_1320 sum8413_1776_5516_1320 rfl rfl rfl

private theorem sum8413_1776_1776_5060 : blockEstimate 8413 1776 1776 5060 = 0x4458ace4ac02 :=
  block_append (B := 8413) (J := 1776) (start := 1776) (next := 4196)
    (a := 2420) (b := 2640) (n := 5060) (x := 0xdf1cb0fd00a) (y := 0x3666e1d4dbf8) (z := 0x4458ace4ac02)
    sum8413_1776_1776_2420 sum8413_1776_4196_2640 rfl rfl rfl

private theorem sum8413_1776_7056_440 : blockEstimate 8413 1776 7056 440 = 0x98b7c8dd7d4 :=
  block_append (B := 8413) (J := 1776) (start := 7056) (next := 7276)
    (a := 220) (b := 220) (n := 440) (x := 0x4d6c1286b02) (y := 0x4b4bb656cd2) (z := 0x98b7c8dd7d4)
    part8413_1776_24 part8413_1776_25 rfl rfl rfl

private theorem sum8413_1776_6836_660 : blockEstimate 8413 1776 6836 660 = 0xe7b73db0586 :=
  block_append (B := 8413) (J := 1776) (start := 6836) (next := 7056)
    (a := 220) (b := 440) (n := 660) (x := 0x4eff74d2db2) (y := 0x98b7c8dd7d4) (z := 0xe7b73db0586)
    part8413_1776_23 sum8413_1776_7056_440 rfl rfl rfl

private theorem sum8413_1776_7716_440 : blockEstimate 8413 1776 7716 440 = 0x8700d6bcb34 :=
  block_append (B := 8413) (J := 1776) (start := 7716) (next := 7936)
    (a := 220) (b := 220) (n := 440) (x := 0x4564104bdf2) (y := 0x419cc670d42) (z := 0x8700d6bcb34)
    part8413_1776_27 part8413_1776_28 rfl rfl rfl

private theorem sum8413_1776_7496_660 : blockEstimate 8413 1776 7496 660 = 0xcf9f36ffe56 :=
  block_append (B := 8413) (J := 1776) (start := 7496) (next := 7716)
    (a := 220) (b := 440) (n := 660) (x := 0x489e6043322) (y := 0x8700d6bcb34) (z := 0xcf9f36ffe56)
    part8413_1776_26 sum8413_1776_7716_440 rfl rfl rfl

private theorem sum8413_1776_6836_1320 : blockEstimate 8413 1776 6836 1320 = 0x1b75674b03dc :=
  block_append (B := 8413) (J := 1776) (start := 6836) (next := 7496)
    (a := 660) (b := 660) (n := 1320) (x := 0xe7b73db0586) (y := 0xcf9f36ffe56) (z := 0x1b75674b03dc)
    sum8413_1776_6836_660 sum8413_1776_7496_660 rfl rfl rfl

private theorem sum8413_1776_8376_440 : blockEstimate 8413 1776 8376 440 = 0x6bcc90c7931 :=
  block_append (B := 8413) (J := 1776) (start := 8376) (next := 8596)
    (a := 220) (b := 220) (n := 440) (x := 0x3870fc56770) (y := 0x335b94711c1) (z := 0x6bcc90c7931)
    part8413_1776_30 part8413_1776_31 rfl rfl rfl

private theorem sum8413_1776_8156_660 : blockEstimate 8413 1776 8156 660 = 0xa9151379a43 :=
  block_append (B := 8413) (J := 1776) (start := 8156) (next := 8376)
    (a := 220) (b := 440) (n := 660) (x := 0x3d4882b2112) (y := 0x6bcc90c7931) (z := 0xa9151379a43)
    part8413_1776_29 sum8413_1776_8376_440 rfl rfl rfl

private theorem sum8413_1776_9036_440 : blockEstimate 8413 1776 9036 440 = 0x4cf8dfe3abd :=
  block_append (B := 8413) (J := 1776) (start := 9036) (next := 9256)
    (a := 220) (b := 220) (n := 440) (x := 0x290929ac799) (y := 0x23efb637324) (z := 0x4cf8dfe3abd)
    part8413_1776_33 part8413_1776_34 rfl rfl rfl

private theorem sum8413_1776_8816_660 : blockEstimate 8413 1776 8816 660 = 0x7b2bc5de75e :=
  block_append (B := 8413) (J := 1776) (start := 8816) (next := 9036)
    (a := 220) (b := 440) (n := 660) (x := 0x2e32e5faca1) (y := 0x4cf8dfe3abd) (z := 0x7b2bc5de75e)
    part8413_1776_32 sum8413_1776_9036_440 rfl rfl rfl

private theorem sum8413_1776_8156_1320 : blockEstimate 8413 1776 8156 1320 = 0x12440d9581a1 :=
  block_append (B := 8413) (J := 1776) (start := 8156) (next := 8816)
    (a := 660) (b := 660) (n := 1320) (x := 0xa9151379a43) (y := 0x7b2bc5de75e) (z := 0x12440d9581a1)
    sum8413_1776_8156_660 sum8413_1776_8816_660 rfl rfl rfl

private theorem sum8413_1776_6836_2640 : blockEstimate 8413 1776 6836 2640 = 0x2db974e0857d :=
  block_append (B := 8413) (J := 1776) (start := 6836) (next := 8156)
    (a := 1320) (b := 1320) (n := 2640) (x := 0x1b75674b03dc) (y := 0x12440d9581a1) (z := 0x2db974e0857d)
    sum8413_1776_6836_1320 sum8413_1776_8156_1320 rfl rfl rfl

private theorem sum8413_1776_9696_440 : blockEstimate 8413 1776 9696 440 = 0x2fd543b4091 :=
  block_append (B := 8413) (J := 1776) (start := 9696) (next := 9916)
    (a := 220) (b := 220) (n := 440) (x := 0x1a2ef76bf87) (y := 0x15a64c4810a) (z := 0x2fd543b4091)
    part8413_1776_36 part8413_1776_37 rfl rfl rfl

private theorem sum8413_1776_9476_660 : blockEstimate 8413 1776 9476 660 = 0x4ecc5690049 :=
  block_append (B := 8413) (J := 1776) (start := 9476) (next := 9696)
    (a := 220) (b := 440) (n := 660) (x := 0x1ef712dbfb8) (y := 0x2fd543b4091) (z := 0x4ecc5690049)
    part8413_1776_35 sum8413_1776_9696_440 rfl rfl rfl

private theorem sum8413_1776_10356_440 : blockEstimate 8413 1776 10356 440 = 0x17809cadd75 :=
  block_append (B := 8413) (J := 1776) (start := 10356) (next := 10576)
    (a := 220) (b := 220) (n := 440) (x := 0xd7da7f3f3e) (y := 0xa02f4b9e37) (z := 0x17809cadd75)
    part8413_1776_39 part8413_1776_40 rfl rfl rfl

private theorem sum8413_1776_10136_660 : blockEstimate 8413 1776 10136 660 = 0x28e78407311 :=
  block_append (B := 8413) (J := 1776) (start := 10136) (next := 10356)
    (a := 220) (b := 440) (n := 660) (x := 0x1166e75959c) (y := 0x17809cadd75) (z := 0x28e78407311)
    part8413_1776_38 sum8413_1776_10356_440 rfl rfl rfl

private theorem sum8413_1776_9476_1320 : blockEstimate 8413 1776 9476 1320 = 0x77b3da9735a :=
  block_append (B := 8413) (J := 1776) (start := 9476) (next := 10136)
    (a := 660) (b := 660) (n := 1320) (x := 0x4ecc5690049) (y := 0x28e78407311) (z := 0x77b3da9735a)
    sum8413_1776_9476_660 sum8413_1776_10136_660 rfl rfl rfl

private theorem sum8413_1776_11016_440 : blockEstimate 8413 1776 11016 440 = 0x6fab8f8e0d :=
  block_append (B := 8413) (J := 1776) (start := 11016) (next := 11236)
    (a := 220) (b := 220) (n := 440) (x := 0x47b89e1f1f) (y := 0x27f2f16eee) (z := 0x6fab8f8e0d)
    part8413_1776_42 part8413_1776_43 rfl rfl rfl

private theorem sum8413_1776_10796_660 : blockEstimate 8413 1776 10796 660 = 0xdfa3edef3f :=
  block_append (B := 8413) (J := 1776) (start := 10796) (next := 11016)
    (a := 220) (b := 440) (n := 660) (x := 0x6ff85e6132) (y := 0x6fab8f8e0d) (z := 0xdfa3edef3f)
    part8413_1776_41 sum8413_1776_11016_440 rfl rfl rfl

private theorem sum8413_1776_11676_289 : blockEstimate 8413 1776 11676 289 = 0x3f00232b1 :=
  block_append (B := 8413) (J := 1776) (start := 11676) (next := 11896)
    (a := 220) (b := 69) (n := 289) (x := 0x3e16d1ff2) (y := 0xe9512bf) (z := 0x3f00232b1)
    part8413_1776_45 part8413_1776_46 rfl rfl rfl

private theorem sum8413_1776_11456_509 : blockEstimate 8413 1776 11456 509 = 0x151a411a40 :=
  block_append (B := 8413) (J := 1776) (start := 11456) (next := 11676)
    (a := 220) (b := 289) (n := 509) (x := 0x112a3ee78f) (y := 0x3f00232b1) (z := 0x151a411a40)
    part8413_1776_44 sum8413_1776_11676_289 rfl rfl rfl

private theorem sum8413_1776_10796_1169 : blockEstimate 8413 1776 10796 1169 = 0xf4be2f097f :=
  block_append (B := 8413) (J := 1776) (start := 10796) (next := 11456)
    (a := 660) (b := 509) (n := 1169) (x := 0xdfa3edef3f) (y := 0x151a411a40) (z := 0xf4be2f097f)
    sum8413_1776_10796_660 sum8413_1776_11456_509 rfl rfl rfl

private theorem sum8413_1776_9476_2489 : blockEstimate 8413 1776 9476 2489 = 0x86ffbd87cd9 :=
  block_append (B := 8413) (J := 1776) (start := 9476) (next := 10796)
    (a := 1320) (b := 1169) (n := 2489) (x := 0x77b3da9735a) (y := 0xf4be2f097f) (z := 0x86ffbd87cd9)
    sum8413_1776_9476_1320 sum8413_1776_10796_1169 rfl rfl rfl

private theorem sum8413_1776_6836_5129 : blockEstimate 8413 1776 6836 5129 = 0x362970b90256 :=
  block_append (B := 8413) (J := 1776) (start := 6836) (next := 9476)
    (a := 2640) (b := 2489) (n := 5129) (x := 0x2db974e0857d) (y := 0x86ffbd87cd9) (z := 0x362970b90256)
    sum8413_1776_6836_2640 sum8413_1776_9476_2489 rfl rfl rfl

private theorem sum8413_1776_1776_10189 : blockEstimate 8413 1776 1776 10189 = 0x7a821d9dae58 :=
  block_append (B := 8413) (J := 1776) (start := 1776) (next := 6836)
    (a := 5060) (b := 5129) (n := 10189) (x := 0x4458ace4ac02) (y := 0x362970b90256) (z := 0x7a821d9dae58)
    sum8413_1776_1776_5060 sum8413_1776_6836_5129 rfl rfl rfl

theorem moment8413_1776 : momentEstimate 8413 1776 = 0x7a821d9dae58 := sum8413_1776_1776_10189

private theorem part9490_2013_0 : blockEstimate 9490 2013 2013 220 = 0x3e7f48941 := by decide +kernel
private theorem part9490_2013_1 : blockEstimate 9490 2013 2233 220 = 0x1a950dd2c5 := by decide +kernel
private theorem part9490_2013_2 : blockEstimate 9490 2013 2453 220 = 0x4653e5e0a9 := by decide +kernel
private theorem part9490_2013_3 : blockEstimate 9490 2013 2673 220 = 0x85819acfed := by decide +kernel
private theorem part9490_2013_4 : blockEstimate 9490 2013 2893 220 = 0xd67b4abd91 := by decide +kernel
private theorem part9490_2013_5 : blockEstimate 9490 2013 3113 220 = 0x1379e13c695 := by decide +kernel
private theorem part9490_2013_6 : blockEstimate 9490 2013 3333 220 = 0x1a7471407f9 := by decide +kernel
private theorem part9490_2013_7 : blockEstimate 9490 2013 3553 220 = 0x223d3699ebd := by decide +kernel
private theorem part9490_2013_8 : blockEstimate 9490 2013 3773 220 = 0x2aba032a7e1 := by decide +kernel
private theorem part9490_2013_9 : blockEstimate 9490 2013 3993 220 = 0x33b2dede20e := by decide +kernel
private theorem part9490_2013_10 : blockEstimate 9490 2013 4213 220 = 0x3c588a2d4e6 := by decide +kernel
private theorem part9490_2013_11 : blockEstimate 9490 2013 4433 220 = 0x445e99123d6 := by decide +kernel
private theorem part9490_2013_12 : blockEstimate 9490 2013 4653 220 = 0x4bc4e0bc9c6 := by decide +kernel
private theorem part9490_2013_13 : blockEstimate 9490 2013 4873 220 = 0x528b612c6b6 := by decide +kernel
private theorem part9490_2013_14 : blockEstimate 9490 2013 5093 220 = 0x58b21a61aa6 := by decide +kernel
private theorem part9490_2013_15 : blockEstimate 9490 2013 5313 220 = 0x5e390c5c596 := by decide +kernel
private theorem part9490_2013_16 : blockEstimate 9490 2013 5533 220 = 0x6320371c786 := by decide +kernel
private theorem part9490_2013_17 : blockEstimate 9490 2013 5753 220 = 0x67679aa2076 := by decide +kernel
private theorem part9490_2013_18 : blockEstimate 9490 2013 5973 220 = 0x6b0f36ed066 := by decide +kernel
private theorem part9490_2013_19 : blockEstimate 9490 2013 6193 220 = 0x6e170bfd756 := by decide +kernel
private theorem part9490_2013_20 : blockEstimate 9490 2013 6413 220 = 0x707f19d3546 := by decide +kernel
private theorem part9490_2013_21 : blockEstimate 9490 2013 6633 220 = 0x7247606ea36 := by decide +kernel
private theorem part9490_2013_22 : blockEstimate 9490 2013 6853 220 = 0x736fdfcf626 := by decide +kernel
private theorem part9490_2013_23 : blockEstimate 9490 2013 7073 220 = 0x73f897f5916 := by decide +kernel
private theorem part9490_2013_24 : blockEstimate 9490 2013 7293 220 = 0x73e188e1306 := by decide +kernel
private theorem part9490_2013_25 : blockEstimate 9490 2013 7513 220 = 0x732ab2923f6 := by decide +kernel
private theorem part9490_2013_26 : blockEstimate 9490 2013 7733 220 = 0x71d41508be6 := by decide +kernel
private theorem part9490_2013_27 : blockEstimate 9490 2013 7953 220 = 0x6fddb044ad6 := by decide +kernel
private theorem part9490_2013_28 : blockEstimate 9490 2013 8173 220 = 0x6d4784460c6 := by decide +kernel
private theorem part9490_2013_29 : blockEstimate 9490 2013 8393 220 = 0x6a11910cdb6 := by decide +kernel
private theorem part9490_2013_30 : blockEstimate 9490 2013 8613 220 = 0x663bd6991a6 := by decide +kernel
private theorem part9490_2013_31 : blockEstimate 9490 2013 8833 220 = 0x61c654eac96 := by decide +kernel
private theorem part9490_2013_32 : blockEstimate 9490 2013 9053 220 = 0x5cb10c01e86 := by decide +kernel
private theorem part9490_2013_33 : blockEstimate 9490 2013 9273 220 = 0x56fbfbe2787 := by decide +kernel
private theorem part9490_2013_34 : blockEstimate 9490 2013 9493 220 = 0x50baf144924 := by decide +kernel
private theorem part9490_2013_35 : blockEstimate 9490 2013 9713 220 = 0x4a3ffd72937 := by decide +kernel
private theorem part9490_2013_36 : blockEstimate 9490 2013 9933 220 = 0x43ae793ef34 := by decide +kernel
private theorem part9490_2013_37 : blockEstimate 9490 2013 10153 220 = 0x3d1896485b0 := by decide +kernel
private theorem part9490_2013_38 : blockEstimate 9490 2013 10373 220 = 0x368fcf273cd := by decide +kernel
private theorem part9490_2013_39 : blockEstimate 9490 2013 10593 220 = 0x3024e76d065 := by decide +kernel
private theorem part9490_2013_40 : blockEstimate 9490 2013 10813 220 = 0x29e7eba45ca := by decide +kernel
private theorem part9490_2013_41 : blockEstimate 9490 2013 11033 220 = 0x23e83151084 := by decide +kernel
private theorem part9490_2013_42 : blockEstimate 9490 2013 11253 220 = 0x1e3456ef857 := by decide +kernel
private theorem part9490_2013_43 : blockEstimate 9490 2013 11473 220 = 0x18d330f23dc := by decide +kernel
private theorem part9490_2013_44 : blockEstimate 9490 2013 11693 220 = 0x13d44352320 := by decide +kernel
private theorem part9490_2013_45 : blockEstimate 9490 2013 11913 220 = 0xf519c76712 := by decide +kernel
private theorem part9490_2013_46 : blockEstimate 9490 2013 12133 220 = 0xb53a107f4e := by decide +kernel
private theorem part9490_2013_47 : blockEstimate 9490 2013 12353 220 = 0x7e27f702c4 := by decide +kernel
private theorem part9490_2013_48 : blockEstimate 9490 2013 12573 220 = 0x5066618864 := by decide +kernel
private theorem part9490_2013_49 : blockEstimate 9490 2013 12793 220 = 0x2c7836a71e := by decide +kernel
private theorem part9490_2013_50 : blockEstimate 9490 2013 13013 220 = 0x12e05cf5e2 := by decide +kernel
private theorem part9490_2013_51 : blockEstimate 9490 2013 13233 220 = 0x421bb0ba0 := by decide +kernel
private theorem part9490_2013_52 : blockEstimate 9490 2013 13453 63 = 0xc9adaf0 := by decide +kernel

private theorem sum9490_2013_2233_440 : blockEstimate 9490 2013 2233 440 = 0x60e8f3b36e :=
  block_append (B := 9490) (J := 2013) (start := 2233) (next := 2453)
    (a := 220) (b := 220) (n := 440) (x := 0x1a950dd2c5) (y := 0x4653e5e0a9) (z := 0x60e8f3b36e)
    part9490_2013_1 part9490_2013_2 rfl rfl rfl

private theorem sum9490_2013_2013_660 : blockEstimate 9490 2013 2013 660 = 0x64d0e83caf :=
  block_append (B := 9490) (J := 2013) (start := 2013) (next := 2233)
    (a := 220) (b := 440) (n := 660) (x := 0x3e7f48941) (y := 0x60e8f3b36e) (z := 0x64d0e83caf)
    part9490_2013_0 sum9490_2013_2233_440 rfl rfl rfl

private theorem sum9490_2013_2893_440 : blockEstimate 9490 2013 2893 440 = 0x20e195e8426 :=
  block_append (B := 9490) (J := 2013) (start := 2893) (next := 3113)
    (a := 220) (b := 220) (n := 440) (x := 0xd67b4abd91) (y := 0x1379e13c695) (z := 0x20e195e8426)
    part9490_2013_4 part9490_2013_5 rfl rfl rfl

private theorem sum9490_2013_2673_660 : blockEstimate 9490 2013 2673 660 = 0x2939af95413 :=
  block_append (B := 9490) (J := 2013) (start := 2673) (next := 2893)
    (a := 220) (b := 440) (n := 660) (x := 0x85819acfed) (y := 0x20e195e8426) (z := 0x2939af95413)
    part9490_2013_3 sum9490_2013_2893_440 rfl rfl rfl

private theorem sum9490_2013_2013_1320 : blockEstimate 9490 2013 2013 1320 = 0x2f86be190c2 :=
  block_append (B := 9490) (J := 2013) (start := 2013) (next := 2673)
    (a := 660) (b := 660) (n := 1320) (x := 0x64d0e83caf) (y := 0x2939af95413) (z := 0x2f86be190c2)
    sum9490_2013_2013_660 sum9490_2013_2673_660 rfl rfl rfl

private theorem sum9490_2013_3553_440 : blockEstimate 9490 2013 3553 440 = 0x4cf739c469e :=
  block_append (B := 9490) (J := 2013) (start := 3553) (next := 3773)
    (a := 220) (b := 220) (n := 440) (x := 0x223d3699ebd) (y := 0x2aba032a7e1) (z := 0x4cf739c469e)
    part9490_2013_7 part9490_2013_8 rfl rfl rfl

private theorem sum9490_2013_3333_660 : blockEstimate 9490 2013 3333 660 = 0x676bab04e97 :=
  block_append (B := 9490) (J := 2013) (start := 3333) (next := 3553)
    (a := 220) (b := 440) (n := 660) (x := 0x1a7471407f9) (y := 0x4cf739c469e) (z := 0x676bab04e97)
    part9490_2013_6 sum9490_2013_3553_440 rfl rfl rfl

private theorem sum9490_2013_3993_440 : blockEstimate 9490 2013 3993 440 = 0x700b690b6f4 :=
  block_append (B := 9490) (J := 2013) (start := 3993) (next := 4213)
    (a := 220) (b := 220) (n := 440) (x := 0x33b2dede20e) (y := 0x3c588a2d4e6) (z := 0x700b690b6f4)
    part9490_2013_9 part9490_2013_10 rfl rfl rfl

private theorem sum9490_2013_4433_440 : blockEstimate 9490 2013 4433 440 = 0x902379ced9c :=
  block_append (B := 9490) (J := 2013) (start := 4433) (next := 4653)
    (a := 220) (b := 220) (n := 440) (x := 0x445e99123d6) (y := 0x4bc4e0bc9c6) (z := 0x902379ced9c)
    part9490_2013_11 part9490_2013_12 rfl rfl rfl

private theorem sum9490_2013_3993_880 : blockEstimate 9490 2013 3993 880 = 0x1002ee2da490 :=
  block_append (B := 9490) (J := 2013) (start := 3993) (next := 4433)
    (a := 440) (b := 440) (n := 880) (x := 0x700b690b6f4) (y := 0x902379ced9c) (z := 0x1002ee2da490)
    sum9490_2013_3993_440 sum9490_2013_4433_440 rfl rfl rfl

private theorem sum9490_2013_3333_1540 : blockEstimate 9490 2013 3333 1540 = 0x1679a8ddf327 :=
  block_append (B := 9490) (J := 2013) (start := 3333) (next := 3993)
    (a := 660) (b := 880) (n := 1540) (x := 0x676bab04e97) (y := 0x1002ee2da490) (z := 0x1679a8ddf327)
    sum9490_2013_3333_660 sum9490_2013_3993_880 rfl rfl rfl

private theorem sum9490_2013_2013_2860 : blockEstimate 9490 2013 2013 2860 = 0x197214bf83e9 :=
  block_append (B := 9490) (J := 2013) (start := 2013) (next := 3333)
    (a := 1320) (b := 1540) (n := 2860) (x := 0x2f86be190c2) (y := 0x1679a8ddf327) (z := 0x197214bf83e9)
    sum9490_2013_2013_1320 sum9490_2013_3333_1540 rfl rfl rfl

private theorem sum9490_2013_5093_440 : blockEstimate 9490 2013 5093 440 = 0xb6eb26be03c :=
  block_append (B := 9490) (J := 2013) (start := 5093) (next := 5313)
    (a := 220) (b := 220) (n := 440) (x := 0x58b21a61aa6) (y := 0x5e390c5c596) (z := 0xb6eb26be03c)
    part9490_2013_14 part9490_2013_15 rfl rfl rfl

private theorem sum9490_2013_4873_660 : blockEstimate 9490 2013 4873 660 = 0x1097687ea6f2 :=
  block_append (B := 9490) (J := 2013) (start := 4873) (next := 5093)
    (a := 220) (b := 440) (n := 660) (x := 0x528b612c6b6) (y := 0xb6eb26be03c) (z := 0x1097687ea6f2)
    part9490_2013_13 sum9490_2013_5093_440 rfl rfl rfl

private theorem sum9490_2013_5753_440 : blockEstimate 9490 2013 5753 440 = 0xd276d18f0dc :=
  block_append (B := 9490) (J := 2013) (start := 5753) (next := 5973)
    (a := 220) (b := 220) (n := 440) (x := 0x67679aa2076) (y := 0x6b0f36ed066) (z := 0xd276d18f0dc)
    part9490_2013_17 part9490_2013_18 rfl rfl rfl

private theorem sum9490_2013_5533_660 : blockEstimate 9490 2013 5533 660 = 0x1359708ab862 :=
  block_append (B := 9490) (J := 2013) (start := 5533) (next := 5753)
    (a := 220) (b := 440) (n := 660) (x := 0x6320371c786) (y := 0xd276d18f0dc) (z := 0x1359708ab862)
    part9490_2013_16 sum9490_2013_5753_440 rfl rfl rfl

private theorem sum9490_2013_4873_1320 : blockEstimate 9490 2013 4873 1320 = 0x23f0d9095f54 :=
  block_append (B := 9490) (J := 2013) (start := 4873) (next := 5533)
    (a := 660) (b := 660) (n := 1320) (x := 0x1097687ea6f2) (y := 0x1359708ab862) (z := 0x23f0d9095f54)
    sum9490_2013_4873_660 sum9490_2013_5533_660 rfl rfl rfl

private theorem sum9490_2013_6413_440 : blockEstimate 9490 2013 6413 440 = 0xe2c67a41f7c :=
  block_append (B := 9490) (J := 2013) (start := 6413) (next := 6633)
    (a := 220) (b := 220) (n := 440) (x := 0x707f19d3546) (y := 0x7247606ea36) (z := 0xe2c67a41f7c)
    part9490_2013_20 part9490_2013_21 rfl rfl rfl

private theorem sum9490_2013_6193_660 : blockEstimate 9490 2013 6193 660 = 0x150dd863f6d2 :=
  block_append (B := 9490) (J := 2013) (start := 6193) (next := 6413)
    (a := 220) (b := 440) (n := 660) (x := 0x6e170bfd756) (y := 0xe2c67a41f7c) (z := 0x150dd863f6d2)
    part9490_2013_19 sum9490_2013_6413_440 rfl rfl rfl

private theorem sum9490_2013_6853_440 : blockEstimate 9490 2013 6853 440 = 0xe76877c4f3c :=
  block_append (B := 9490) (J := 2013) (start := 6853) (next := 7073)
    (a := 220) (b := 220) (n := 440) (x := 0x736fdfcf626) (y := 0x73f897f5916) (z := 0xe76877c4f3c)
    part9490_2013_22 part9490_2013_23 rfl rfl rfl

private theorem sum9490_2013_7293_440 : blockEstimate 9490 2013 7293 440 = 0xe70c3b736fc :=
  block_append (B := 9490) (J := 2013) (start := 7293) (next := 7513)
    (a := 220) (b := 220) (n := 440) (x := 0x73e188e1306) (y := 0x732ab2923f6) (z := 0xe70c3b736fc)
    part9490_2013_24 part9490_2013_25 rfl rfl rfl

private theorem sum9490_2013_6853_880 : blockEstimate 9490 2013 6853 880 = 0x1ce74b338638 :=
  block_append (B := 9490) (J := 2013) (start := 6853) (next := 7293)
    (a := 440) (b := 440) (n := 880) (x := 0xe76877c4f3c) (y := 0xe70c3b736fc) (z := 0x1ce74b338638)
    sum9490_2013_6853_440 sum9490_2013_7293_440 rfl rfl rfl

private theorem sum9490_2013_6193_1540 : blockEstimate 9490 2013 6193 1540 = 0x31f523977d0a :=
  block_append (B := 9490) (J := 2013) (start := 6193) (next := 6853)
    (a := 660) (b := 880) (n := 1540) (x := 0x150dd863f6d2) (y := 0x1ce74b338638) (z := 0x31f523977d0a)
    sum9490_2013_6193_660 sum9490_2013_6853_880 rfl rfl rfl

private theorem sum9490_2013_4873_2860 : blockEstimate 9490 2013 4873 2860 = 0x55e5fca0dc5e :=
  block_append (B := 9490) (J := 2013) (start := 4873) (next := 6193)
    (a := 1320) (b := 1540) (n := 2860) (x := 0x23f0d9095f54) (y := 0x31f523977d0a) (z := 0x55e5fca0dc5e)
    sum9490_2013_4873_1320 sum9490_2013_6193_1540 rfl rfl rfl

private theorem sum9490_2013_2013_5720 : blockEstimate 9490 2013 2013 5720 = 0x6f5811606047 :=
  block_append (B := 9490) (J := 2013) (start := 2013) (next := 4873)
    (a := 2860) (b := 2860) (n := 5720) (x := 0x197214bf83e9) (y := 0x55e5fca0dc5e) (z := 0x6f5811606047)
    sum9490_2013_2013_2860 sum9490_2013_4873_2860 rfl rfl rfl

private theorem sum9490_2013_7953_440 : blockEstimate 9490 2013 7953 440 = 0xdd25348ab9c :=
  block_append (B := 9490) (J := 2013) (start := 7953) (next := 8173)
    (a := 220) (b := 220) (n := 440) (x := 0x6fddb044ad6) (y := 0x6d4784460c6) (z := 0xdd25348ab9c)
    part9490_2013_27 part9490_2013_28 rfl rfl rfl

private theorem sum9490_2013_7733_660 : blockEstimate 9490 2013 7733 660 = 0x14ef94993782 :=
  block_append (B := 9490) (J := 2013) (start := 7733) (next := 7953)
    (a := 220) (b := 440) (n := 660) (x := 0x71d41508be6) (y := 0xdd25348ab9c) (z := 0x14ef94993782)
    part9490_2013_26 sum9490_2013_7953_440 rfl rfl rfl

private theorem sum9490_2013_8613_440 : blockEstimate 9490 2013 8613 440 = 0xc8022b83e3c :=
  block_append (B := 9490) (J := 2013) (start := 8613) (next := 8833)
    (a := 220) (b := 220) (n := 440) (x := 0x663bd6991a6) (y := 0x61c654eac96) (z := 0xc8022b83e3c)
    part9490_2013_30 part9490_2013_31 rfl rfl rfl

private theorem sum9490_2013_8393_660 : blockEstimate 9490 2013 8393 660 = 0x13213bc90bf2 :=
  block_append (B := 9490) (J := 2013) (start := 8393) (next := 8613)
    (a := 220) (b := 440) (n := 660) (x := 0x6a11910cdb6) (y := 0xc8022b83e3c) (z := 0x13213bc90bf2)
    part9490_2013_29 sum9490_2013_8613_440 rfl rfl rfl

private theorem sum9490_2013_7733_1320 : blockEstimate 9490 2013 7733 1320 = 0x2810d0624374 :=
  block_append (B := 9490) (J := 2013) (start := 7733) (next := 8393)
    (a := 660) (b := 660) (n := 1320) (x := 0x14ef94993782) (y := 0x13213bc90bf2) (z := 0x2810d0624374)
    sum9490_2013_7733_660 sum9490_2013_8393_660 rfl rfl rfl

private theorem sum9490_2013_9273_440 : blockEstimate 9490 2013 9273 440 = 0xa7b6ed270ab :=
  block_append (B := 9490) (J := 2013) (start := 9273) (next := 9493)
    (a := 220) (b := 220) (n := 440) (x := 0x56fbfbe2787) (y := 0x50baf144924) (z := 0xa7b6ed270ab)
    part9490_2013_33 part9490_2013_34 rfl rfl rfl

private theorem sum9490_2013_9053_660 : blockEstimate 9490 2013 9053 660 = 0x10467f928f31 :=
  block_append (B := 9490) (J := 2013) (start := 9053) (next := 9273)
    (a := 220) (b := 440) (n := 660) (x := 0x5cb10c01e86) (y := 0xa7b6ed270ab) (z := 0x10467f928f31)
    part9490_2013_32 sum9490_2013_9273_440 rfl rfl rfl

private theorem sum9490_2013_9713_440 : blockEstimate 9490 2013 9713 440 = 0x8dee76b186b :=
  block_append (B := 9490) (J := 2013) (start := 9713) (next := 9933)
    (a := 220) (b := 220) (n := 440) (x := 0x4a3ffd72937) (y := 0x43ae793ef34) (z := 0x8dee76b186b)
    part9490_2013_35 part9490_2013_36 rfl rfl rfl

private theorem sum9490_2013_10153_440 : blockEstimate 9490 2013 10153 440 = 0x73a8656f97d :=
  block_append (B := 9490) (J := 2013) (start := 10153) (next := 10373)
    (a := 220) (b := 220) (n := 440) (x := 0x3d1896485b0) (y := 0x368fcf273cd) (z := 0x73a8656f97d)
    part9490_2013_37 part9490_2013_38 rfl rfl rfl

private theorem sum9490_2013_9713_880 : blockEstimate 9490 2013 9713 880 = 0x10196dc211e8 :=
  block_append (B := 9490) (J := 2013) (start := 9713) (next := 10153)
    (a := 440) (b := 440) (n := 880) (x := 0x8dee76b186b) (y := 0x73a8656f97d) (z := 0x10196dc211e8)
    sum9490_2013_9713_440 sum9490_2013_10153_440 rfl rfl rfl

private theorem sum9490_2013_9053_1540 : blockEstimate 9490 2013 9053 1540 = 0x205fed54a119 :=
  block_append (B := 9490) (J := 2013) (start := 9053) (next := 9713)
    (a := 660) (b := 880) (n := 1540) (x := 0x10467f928f31) (y := 0x10196dc211e8) (z := 0x205fed54a119)
    sum9490_2013_9053_660 sum9490_2013_9713_880 rfl rfl rfl

private theorem sum9490_2013_7733_2860 : blockEstimate 9490 2013 7733 2860 = 0x4870bdb6e48d :=
  block_append (B := 9490) (J := 2013) (start := 7733) (next := 9053)
    (a := 1320) (b := 1540) (n := 2860) (x := 0x2810d0624374) (y := 0x205fed54a119) (z := 0x4870bdb6e48d)
    sum9490_2013_7733_1320 sum9490_2013_9053_1540 rfl rfl rfl

private theorem sum9490_2013_10813_440 : blockEstimate 9490 2013 10813 440 = 0x4dd01cf564e :=
  block_append (B := 9490) (J := 2013) (start := 10813) (next := 11033)
    (a := 220) (b := 220) (n := 440) (x := 0x29e7eba45ca) (y := 0x23e83151084) (z := 0x4dd01cf564e)
    part9490_2013_40 part9490_2013_41 rfl rfl rfl

private theorem sum9490_2013_10593_660 : blockEstimate 9490 2013 10593 660 = 0x7df504626b3 :=
  block_append (B := 9490) (J := 2013) (start := 10593) (next := 10813)
    (a := 220) (b := 440) (n := 660) (x := 0x3024e76d065) (y := 0x4dd01cf564e) (z := 0x7df504626b3)
    part9490_2013_39 sum9490_2013_10813_440 rfl rfl rfl

private theorem sum9490_2013_11253_440 : blockEstimate 9490 2013 11253 440 = 0x370787e1c33 :=
  block_append (B := 9490) (J := 2013) (start := 11253) (next := 11473)
    (a := 220) (b := 220) (n := 440) (x := 0x1e3456ef857) (y := 0x18d330f23dc) (z := 0x370787e1c33)
    part9490_2013_42 part9490_2013_43 rfl rfl rfl

private theorem sum9490_2013_11693_440 : blockEstimate 9490 2013 11693 440 = 0x2325dfc8a32 :=
  block_append (B := 9490) (J := 2013) (start := 11693) (next := 11913)
    (a := 220) (b := 220) (n := 440) (x := 0x13d44352320) (y := 0xf519c76712) (z := 0x2325dfc8a32)
    part9490_2013_44 part9490_2013_45 rfl rfl rfl

private theorem sum9490_2013_11253_880 : blockEstimate 9490 2013 11253 880 = 0x5a2d67aa665 :=
  block_append (B := 9490) (J := 2013) (start := 11253) (next := 11693)
    (a := 440) (b := 440) (n := 880) (x := 0x370787e1c33) (y := 0x2325dfc8a32) (z := 0x5a2d67aa665)
    sum9490_2013_11253_440 sum9490_2013_11693_440 rfl rfl rfl

private theorem sum9490_2013_10593_1540 : blockEstimate 9490 2013 10593 1540 = 0xd8226c0cd18 :=
  block_append (B := 9490) (J := 2013) (start := 10593) (next := 11253)
    (a := 660) (b := 880) (n := 1540) (x := 0x7df504626b3) (y := 0x5a2d67aa665) (z := 0xd8226c0cd18)
    sum9490_2013_10593_660 sum9490_2013_11253_880 rfl rfl rfl

private theorem sum9490_2013_12353_440 : blockEstimate 9490 2013 12353 440 = 0xce8e588b28 :=
  block_append (B := 9490) (J := 2013) (start := 12353) (next := 12573)
    (a := 220) (b := 220) (n := 440) (x := 0x7e27f702c4) (y := 0x5066618864) (z := 0xce8e588b28)
    part9490_2013_47 part9490_2013_48 rfl rfl rfl

private theorem sum9490_2013_12133_660 : blockEstimate 9490 2013 12133 660 = 0x183c8690a76 :=
  block_append (B := 9490) (J := 2013) (start := 12133) (next := 12353)
    (a := 220) (b := 440) (n := 660) (x := 0xb53a107f4e) (y := 0xce8e588b28) (z := 0x183c8690a76)
    part9490_2013_46 sum9490_2013_12353_440 rfl rfl rfl

private theorem sum9490_2013_12793_440 : blockEstimate 9490 2013 12793 440 = 0x3f58939d00 :=
  block_append (B := 9490) (J := 2013) (start := 12793) (next := 13013)
    (a := 220) (b := 220) (n := 440) (x := 0x2c7836a71e) (y := 0x12e05cf5e2) (z := 0x3f58939d00)
    part9490_2013_49 part9490_2013_50 rfl rfl rfl

private theorem sum9490_2013_13233_283 : blockEstimate 9490 2013 13233 283 = 0x42e55e690 :=
  block_append (B := 9490) (J := 2013) (start := 13233) (next := 13453)
    (a := 220) (b := 63) (n := 283) (x := 0x421bb0ba0) (y := 0xc9adaf0) (z := 0x42e55e690)
    part9490_2013_51 part9490_2013_52 rfl rfl rfl

private theorem sum9490_2013_12793_723 : blockEstimate 9490 2013 12793 723 = 0x4386e98390 :=
  block_append (B := 9490) (J := 2013) (start := 12793) (next := 13233)
    (a := 440) (b := 283) (n := 723) (x := 0x3f58939d00) (y := 0x42e55e690) (z := 0x4386e98390)
    sum9490_2013_12793_440 sum9490_2013_13233_283 rfl rfl rfl

private theorem sum9490_2013_12133_1383 : blockEstimate 9490 2013 12133 1383 = 0x1c74f528e06 :=
  block_append (B := 9490) (J := 2013) (start := 12133) (next := 12793)
    (a := 660) (b := 723) (n := 1383) (x := 0x183c8690a76) (y := 0x4386e98390) (z := 0x1c74f528e06)
    sum9490_2013_12133_660 sum9490_2013_12793_723 rfl rfl rfl

private theorem sum9490_2013_10593_2923 : blockEstimate 9490 2013 10593 2923 = 0xf4976135b1e :=
  block_append (B := 9490) (J := 2013) (start := 10593) (next := 12133)
    (a := 1540) (b := 1383) (n := 2923) (x := 0xd8226c0cd18) (y := 0x1c74f528e06) (z := 0xf4976135b1e)
    sum9490_2013_10593_1540 sum9490_2013_12133_1383 rfl rfl rfl

private theorem sum9490_2013_7733_5783 : blockEstimate 9490 2013 7733 5783 = 0x57ba33ca3fab :=
  block_append (B := 9490) (J := 2013) (start := 7733) (next := 10593)
    (a := 2860) (b := 2923) (n := 5783) (x := 0x4870bdb6e48d) (y := 0xf4976135b1e) (z := 0x57ba33ca3fab)
    sum9490_2013_7733_2860 sum9490_2013_10593_2923 rfl rfl rfl

private theorem sum9490_2013_2013_11503 : blockEstimate 9490 2013 2013 11503 = 0xc712452a9ff2 :=
  block_append (B := 9490) (J := 2013) (start := 2013) (next := 7733)
    (a := 5720) (b := 5783) (n := 11503) (x := 0x6f5811606047) (y := 0x57ba33ca3fab) (z := 0xc712452a9ff2)
    sum9490_2013_2013_5720 sum9490_2013_7733_5783 rfl rfl rfl

theorem moment9490_2013 : momentEstimate 9490 2013 = 0xc712452a9ff2 := sum9490_2013_2013_11503

end HighCore82209BankProof
