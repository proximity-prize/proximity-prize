import ProximityPrize.SubmissionLower.HighCore82258Moments0

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000
set_option quotPrecheck false

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_6 (append)

private theorem b6398_1353_1353 : blockEstimate 6398 1353 1353 660 = 0x4229ecb65f := by decide +kernel
private theorem b6398_1353_2013 : blockEstimate 6398 1353 2013 660 = 0x1a1aae64d83 := by decide +kernel
private theorem b6398_1353_2673 : blockEstimate 6398 1353 2673 660 = 0x3bac56e3656 := by decide +kernel
private theorem b6398_1353_3333 : blockEstimate 6398 1353 3333 660 = 0x56675c0bf4e := by decide +kernel
private theorem b6398_1353_3993 : blockEstimate 6398 1353 3993 660 = 0x65ce3554c5e := by decide +kernel
private theorem b6398_1353_4653 : blockEstimate 6398 1353 4653 660 = 0x69e0c5ce86e := by decide +kernel
private theorem b6398_1353_5313 : blockEstimate 6398 1353 5313 660 = 0x629f0d7937e := by decide +kernel
private theorem b6398_1353_5973 : blockEstimate 6398 1353 5973 660 = 0x501913b7d86 := by decide +kernel
private theorem b6398_1353_6633 : blockEstimate 6398 1353 6633 660 = 0x361c606a07a := by decide +kernel
private theorem b6398_1353_7293 : blockEstimate 6398 1353 7293 660 = 0x1d087600108 := by decide +kernel
private theorem b6398_1353_7953 : blockEstimate 6398 1353 7953 660 = 0x9fbaa090ec := by decide +kernel
private theorem b6398_1353_8613 : blockEstimate 6398 1353 8613 491 = 0xe4c1e0774 := by decide +kernel
private theorem s6398_1353_1353_1320 : blockEstimate 6398 1353 1353 1320 = 0x1e3d4d303e2 :=
  append (B := 6398) (J := 1353) (start := 1353) (a := 660) (x := 0x4229ecb65f)
    b6398_1353_1353 2013 660 0x1a1aae64d83 1320 0x1e3d4d303e2 rfl rfl rfl b6398_1353_2013
private theorem s6398_1353_2673_1320 : blockEstimate 6398 1353 2673 1320 = 0x9213b2ef5a4 :=
  append (B := 6398) (J := 1353) (start := 2673) (a := 660) (x := 0x3bac56e3656)
    b6398_1353_2673 3333 660 0x56675c0bf4e 1320 0x9213b2ef5a4 rfl rfl rfl b6398_1353_3333
private theorem s6398_1353_3993_1320 : blockEstimate 6398 1353 3993 1320 = 0xcfaefb234cc :=
  append (B := 6398) (J := 1353) (start := 3993) (a := 660) (x := 0x65ce3554c5e)
    b6398_1353_3993 4653 660 0x69e0c5ce86e 1320 0xcfaefb234cc rfl rfl rfl b6398_1353_4653
private theorem s6398_1353_5313_1320 : blockEstimate 6398 1353 5313 1320 = 0xb2b82131104 :=
  append (B := 6398) (J := 1353) (start := 5313) (a := 660) (x := 0x629f0d7937e)
    b6398_1353_5313 5973 660 0x501913b7d86 1320 0xb2b82131104 rfl rfl rfl b6398_1353_5973
private theorem s6398_1353_6633_1320 : blockEstimate 6398 1353 6633 1320 = 0x5324d66a182 :=
  append (B := 6398) (J := 1353) (start := 6633) (a := 660) (x := 0x361c606a07a)
    b6398_1353_6633 7293 660 0x1d087600108 1320 0x5324d66a182 rfl rfl rfl b6398_1353_7293
private theorem s6398_1353_7953_1151 : blockEstimate 6398 1353 7953 1151 = 0xae06be9860 :=
  append (B := 6398) (J := 1353) (start := 7953) (a := 660) (x := 0x9fbaa090ec)
    b6398_1353_7953 8613 491 0xe4c1e0774 1151 0xae06be9860 rfl rfl rfl b6398_1353_8613
private theorem s6398_1353_1353_2640 : blockEstimate 6398 1353 1353 2640 = 0xb051001f986 :=
  append (B := 6398) (J := 1353) (start := 1353) (a := 1320) (x := 0x1e3d4d303e2)
    s6398_1353_1353_1320 2673 1320 0x9213b2ef5a4 2640 0xb051001f986 rfl rfl rfl s6398_1353_2673_1320
private theorem s6398_1353_3993_2640 : blockEstimate 6398 1353 3993 2640 = 0x182671c545d0 :=
  append (B := 6398) (J := 1353) (start := 3993) (a := 1320) (x := 0xcfaefb234cc)
    s6398_1353_3993_1320 5313 1320 0xb2b82131104 2640 0x182671c545d0 rfl rfl rfl s6398_1353_5313_1320
private theorem s6398_1353_6633_2471 : blockEstimate 6398 1353 6633 2471 = 0x5e0542539e2 :=
  append (B := 6398) (J := 1353) (start := 6633) (a := 1320) (x := 0x5324d66a182)
    s6398_1353_6633_1320 7953 1151 0xae06be9860 2471 0x5e0542539e2 rfl rfl rfl s6398_1353_7953_1151
private theorem s6398_1353_1353_5280 : blockEstimate 6398 1353 1353 5280 = 0x232b81c73f56 :=
  append (B := 6398) (J := 1353) (start := 1353) (a := 2640) (x := 0xb051001f986)
    s6398_1353_1353_2640 3993 2640 0x182671c545d0 5280 0x232b81c73f56 rfl rfl rfl s6398_1353_3993_2640
private theorem s6398_1353_1353_7751 : blockEstimate 6398 1353 1353 7751 = 0x290bd5ec7938 :=
  append (B := 6398) (J := 1353) (start := 1353) (a := 5280) (x := 0x232b81c73f56)
    s6398_1353_1353_5280 6633 2471 0x5e0542539e2 7751 0x290bd5ec7938 rfl rfl rfl s6398_1353_6633_2471
theorem moment6398_1353 : momentEstimate 6398 1353 = 0x290bd5ec7938 := by
  change blockEstimate 6398 1353 1353 7751 = 0x290bd5ec7938
  exact s6398_1353_1353_7751

private theorem b2018_424_424 : blockEstimate 2018 424 424 660 = 0x105a91248a := by decide +kernel
private theorem b2018_424_1084 : blockEstimate 2018 424 1084 660 = 0x31ebded5d8 := by decide +kernel
private theorem b2018_424_1744 : blockEstimate 2018 424 1744 660 = 0x220432d523 := by decide +kernel
private theorem b2018_424_2404 : blockEstimate 2018 424 2404 462 = 0x37b04f26f := by decide +kernel
private theorem s2018_424_424_1320 : blockEstimate 2018 424 424 1320 = 0x42466ffa62 :=
  append (B := 2018) (J := 424) (start := 424) (a := 660) (x := 0x105a91248a)
    b2018_424_424 1084 660 0x31ebded5d8 1320 0x42466ffa62 rfl rfl rfl b2018_424_1084
private theorem s2018_424_1744_1122 : blockEstimate 2018 424 1744 1122 = 0x257f37c792 :=
  append (B := 2018) (J := 424) (start := 1744) (a := 660) (x := 0x220432d523)
    b2018_424_1744 2404 462 0x37b04f26f 1122 0x257f37c792 rfl rfl rfl b2018_424_2404
private theorem s2018_424_424_2442 : blockEstimate 2018 424 424 2442 = 0x67c5a7c1f4 :=
  append (B := 2018) (J := 424) (start := 424) (a := 1320) (x := 0x42466ffa62)
    s2018_424_424_1320 1744 1122 0x257f37c792 2442 0x67c5a7c1f4 rfl rfl rfl s2018_424_1744_1122
theorem moment2018_424 : momentEstimate 2018 424 = 0x67c5a7c1f4 := by
  change blockEstimate 2018 424 424 2442 = 0x67c5a7c1f4
  exact s2018_424_424_2442

private theorem b966_204_204 : blockEstimate 966 204 204 660 = 0x3bd5f3cd5 := by decide +kernel
private theorem b966_204_864 : blockEstimate 966 204 864 510 = 0x1c1879f70 := by decide +kernel
private theorem s966_204_204_1170 : blockEstimate 966 204 204 1170 = 0x57ee6dc45 :=
  append (B := 966) (J := 204) (start := 204) (a := 660) (x := 0x3bd5f3cd5)
    b966_204_204 864 510 0x1c1879f70 1170 0x57ee6dc45 rfl rfl rfl b966_204_864
theorem moment966_204 : momentEstimate 966 204 = 0x57ee6dc45 := by
  change blockEstimate 966 204 204 1170 = 0x57ee6dc45
  exact s966_204_204_1170

private theorem b691_144_144 : blockEstimate 691 144 144 660 = 0x15d39b281 := by decide +kernel
private theorem b691_144_804 : blockEstimate 691 144 804 175 = 0x109ef195 := by decide +kernel
private theorem s691_144_144_835 : blockEstimate 691 144 144 835 = 0x16dd8a416 :=
  append (B := 691) (J := 144) (start := 144) (a := 660) (x := 0x15d39b281)
    b691_144_144 804 175 0x109ef195 835 0x16dd8a416 rfl rfl rfl b691_144_804
theorem moment691_144 : momentEstimate 691 144 = 0x16dd8a416 := by
  change blockEstimate 691 144 144 835 = 0x16dd8a416
  exact s691_144_144_835

private theorem b355_79_79 : blockEstimate 355 79 79 434 = 0x1b1f653e := by decide +kernel
theorem moment355_79 : momentEstimate 355 79 = 0x1b1f653e := by
  change blockEstimate 355 79 79 434 = 0x1b1f653e
  exact b355_79_79

private theorem b299_66_66 : blockEstimate 299 66 66 365 = 0xd9f9f46 := by decide +kernel
theorem moment299_66 : momentEstimate 299 66 = 0xd9f9f46 := by
  change blockEstimate 299 66 66 365 = 0xd9f9f46
  exact b299_66_66

private theorem b129_28_28 : blockEstimate 129 28 28 157 = 0x7bb5e0 := by decide +kernel
theorem moment129_28 : momentEstimate 129 28 = 0x7bb5e0 := by
  change blockEstimate 129 28 28 157 = 0x7bb5e0
  exact b129_28_28

end HighCore82258BankProof
