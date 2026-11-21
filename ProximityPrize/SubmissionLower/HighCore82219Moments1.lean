import ProximityPrize.SubmissionLower.HighCore82219Moments0

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)

set_option maxHeartbeats 14000000

private theorem p530_100_100 : blockEstimate 530 100 100 215 = 0x1fca4b25 := by decide +kernel
private theorem p530_100_315 : blockEstimate 530 100 315 215 = 0x4482bb8c := by decide +kernel
private theorem p530_100_530 : blockEstimate 530 100 530 200 = 0x114aa9bb := by decide +kernel

private theorem s530_100_315_415 : blockEstimate 530 100 315 415 = 0x55cd6547 :=
  block_append p530_100_315 p530_100_530 rfl rfl rfl

private theorem s530_100_100_630 : blockEstimate 530 100 100 630 = 0x7597b06c :=
  block_append p530_100_100 s530_100_315_415 rfl rfl rfl

theorem moment530_100 : momentEstimate 530 100 = 0x7597b06c := s530_100_100_630

private theorem p559_122_122 : blockEstimate 559 122 122 215 = 0x24f4b91d := by decide +kernel
private theorem p559_122_337 : blockEstimate 559 122 337 215 = 0x5bcdbc1a := by decide +kernel
private theorem p559_122_552 : blockEstimate 559 122 552 215 = 0x21f9056f := by decide +kernel
private theorem p559_122_767 : blockEstimate 559 122 767 36 = 0x2459b2 := by decide +kernel

private theorem s559_122_122_430 : blockEstimate 559 122 122 430 = 0x80c27537 :=
  block_append p559_122_122 p559_122_337 rfl rfl rfl

private theorem s559_122_552_251 : blockEstimate 559 122 552 251 = 0x221d5f21 :=
  block_append p559_122_552 p559_122_767 rfl rfl rfl

private theorem s559_122_122_681 : blockEstimate 559 122 122 681 = 0xa2dfd458 :=
  block_append s559_122_122_430 s559_122_552_251 rfl rfl rfl

theorem moment559_122 : momentEstimate 559 122 = 0xa2dfd458 := s559_122_122_681

private theorem p563_118_118 : blockEstimate 563 118 118 215 = 0x24ea55ce := by decide +kernel
private theorem p563_118_333 : blockEstimate 563 118 333 215 = 0x5b26c1bc := by decide +kernel
private theorem p563_118_548 : blockEstimate 563 118 548 215 = 0x222f8023 := by decide +kernel
private theorem p563_118_763 : blockEstimate 563 118 763 36 = 0x249e46 := by decide +kernel

private theorem s563_118_118_430 : blockEstimate 563 118 118 430 = 0x8011178a :=
  block_append p563_118_118 p563_118_333 rfl rfl rfl

private theorem s563_118_548_251 : blockEstimate 563 118 548 251 = 0x22541e69 :=
  block_append p563_118_548 p563_118_763 rfl rfl rfl

private theorem s563_118_118_681 : blockEstimate 563 118 118 681 = 0xa26535f3 :=
  block_append s563_118_118_430 s563_118_548_251 rfl rfl rfl

theorem moment563_118 : momentEstimate 563 118 = 0xa26535f3 := s563_118_118_681

private theorem p590_130_130 : blockEstimate 590 130 130 215 = 0x2893d217 := by decide +kernel
private theorem p590_130_345 : blockEstimate 590 130 345 215 = 0x6d9c233c := by decide +kernel
private theorem p590_130_560 : blockEstimate 590 130 560 215 = 0x34094027 := by decide +kernel
private theorem p590_130_775 : blockEstimate 590 130 775 75 = 0x13c2494 := by decide +kernel

private theorem s590_130_130_430 : blockEstimate 590 130 130 430 = 0x962ff553 :=
  block_append p590_130_130 p590_130_345 rfl rfl rfl

private theorem s590_130_560_290 : blockEstimate 590 130 560 290 = 0x354564bb :=
  block_append p590_130_560 p590_130_775 rfl rfl rfl

private theorem s590_130_130_720 : blockEstimate 590 130 130 720 = 0xcb755a0e :=
  block_append s590_130_130_430 s590_130_560_290 rfl rfl rfl

theorem moment590_130 : momentEstimate 590 130 = 0xcb755a0e := s590_130_130_720

private theorem p619_130_130 : blockEstimate 619 130 130 215 = 0x2b4dc1cf := by decide +kernel
private theorem p619_130_345 : blockEstimate 619 130 345 215 = 0x7a2ba15e := by decide +kernel
private theorem p619_130_560 : blockEstimate 619 130 560 215 = 0x448c5263 := by decide +kernel
private theorem p619_130_775 : blockEstimate 619 130 775 104 = 0x354504e := by decide +kernel

private theorem s619_130_130_430 : blockEstimate 619 130 130 430 = 0xa579632d :=
  block_append p619_130_130 p619_130_345 rfl rfl rfl

private theorem s619_130_560_319 : blockEstimate 619 130 560 319 = 0x47e0a2b1 :=
  block_append p619_130_560 p619_130_775 rfl rfl rfl

private theorem s619_130_130_749 : blockEstimate 619 130 130 749 = 0xed5a05de :=
  block_append s619_130_130_430 s619_130_560_319 rfl rfl rfl

theorem moment619_130 : momentEstimate 619 130 = 0xed5a05de := s619_130_130_749

private theorem p659_138_138 : blockEstimate 659 138 138 215 = 0x2fcd66f1 := by decide +kernel
private theorem p659_138_353 : blockEstimate 659 138 353 215 = 0x919ce78a := by decide +kernel
private theorem p659_138_568 : blockEstimate 659 138 568 215 = 0x63fcfa9d := by decide +kernel
private theorem p659_138_783 : blockEstimate 659 138 783 152 = 0xa90e49a := by decide +kernel

private theorem s659_138_138_430 : blockEstimate 659 138 138 430 = 0xc16a4e7b :=
  block_append p659_138_138 p659_138_353 rfl rfl rfl

private theorem s659_138_568_367 : blockEstimate 659 138 568 367 = 0x6e8ddf37 :=
  block_append p659_138_568 p659_138_783 rfl rfl rfl

private theorem s659_138_138_797 : blockEstimate 659 138 138 797 = 0x12ff82db2 :=
  block_append s659_138_138_430 s659_138_568_367 rfl rfl rfl

theorem moment659_138 : momentEstimate 659 138 = 0x12ff82db2 := s659_138_138_797

private theorem p688_140_140 : blockEstimate 688 140 140 215 = 0x32beecdb := by decide +kernel
private theorem p688_140_355 : blockEstimate 688 140 355 215 = 0xa05b410e := by decide +kernel
private theorem p688_140_570 : blockEstimate 688 140 570 215 = 0x7b168b43 := by decide +kernel
private theorem p688_140_785 : blockEstimate 688 140 785 183 = 0x12bf0eee := by decide +kernel

private theorem s688_140_140_430 : blockEstimate 688 140 140 430 = 0xd31a2de9 :=
  block_append p688_140_140 p688_140_355 rfl rfl rfl

private theorem s688_140_570_398 : blockEstimate 688 140 570 398 = 0x8dd59a31 :=
  block_append p688_140_570 p688_140_785 rfl rfl rfl

private theorem s688_140_140_828 : blockEstimate 688 140 140 828 = 0x160efc81a :=
  block_append s688_140_140_430 s688_140_570_398 rfl rfl rfl

theorem moment688_140 : momentEstimate 688 140 = 0x160efc81a := s688_140_140_828

private theorem p692_155_155 : blockEstimate 692 155 155 215 = 0x3427022f := by decide +kernel
private theorem p692_155_370 : blockEstimate 692 155 370 215 = 0xade4241c := by decide +kernel
private theorem p692_155_585 : blockEstimate 692 155 585 215 = 0x8a26b916 := by decide +kernel
private theorem p692_155_800 : blockEstimate 692 155 800 202 = 0x18f16422 := by decide +kernel

private theorem s692_155_155_430 : blockEstimate 692 155 155 430 = 0xe20b264b :=
  block_append p692_155_155 p692_155_370 rfl rfl rfl

private theorem s692_155_585_417 : blockEstimate 692 155 585 417 = 0xa3181d38 :=
  block_append p692_155_585 p692_155_800 rfl rfl rfl

private theorem s692_155_155_847 : blockEstimate 692 155 155 847 = 0x185234383 :=
  block_append s692_155_155_430 s692_155_585_417 rfl rfl rfl

theorem moment692_155 : momentEstimate 692 155 = 0x185234383 := s692_155_155_847

private theorem p731_158_158 : blockEstimate 731 158 158 215 = 0x38231650 := by decide +kernel
private theorem p731_158_373 : blockEstimate 731 158 373 215 = 0xc37e7908 := by decide +kernel
private theorem p731_158_588 : blockEstimate 731 158 588 215 = 0xae861f51 := by decide +kernel
private theorem p731_158_803 : blockEstimate 731 158 803 215 = 0x2cd08849 := by decide +kernel
private theorem p731_158_1018 : blockEstimate 731 158 1018 29 = 0x19db94 := by decide +kernel

private theorem s731_158_158_430 : blockEstimate 731 158 158 430 = 0xfba18f58 :=
  block_append p731_158_158 p731_158_373 rfl rfl rfl

private theorem s731_158_803_244 : blockEstimate 731 158 803 244 = 0x2cea63dd :=
  block_append p731_158_803 p731_158_1018 rfl rfl rfl

private theorem s731_158_588_459 : blockEstimate 731 158 588 459 = 0xdb70832e :=
  block_append p731_158_588 s731_158_803_244 rfl rfl rfl

private theorem s731_158_158_889 : blockEstimate 731 158 158 889 = 0x1d7121286 :=
  block_append s731_158_158_430 s731_158_588_459 rfl rfl rfl

theorem moment731_158 : momentEstimate 731 158 = 0x1d7121286 := s731_158_158_889

private theorem p764_141_141 : blockEstimate 764 141 141 215 = 0x3a21798a := by decide +kernel
private theorem p764_141_356 : blockEstimate 764 141 356 215 = 0xc414d312 := by decide +kernel
private theorem p764_141_571 : blockEstimate 764 141 571 215 = 0xba221b25 := by decide +kernel
private theorem p764_141_786 : blockEstimate 764 141 786 215 = 0x37a97789 := by decide +kernel
private theorem p764_141_1001 : blockEstimate 764 141 1001 45 = 0x5efcda := by decide +kernel

private theorem s764_141_141_430 : blockEstimate 764 141 141 430 = 0xfe364c9c :=
  block_append p764_141_141 p764_141_356 rfl rfl rfl

private theorem s764_141_786_260 : blockEstimate 764 141 786 260 = 0x38087463 :=
  block_append p764_141_786 p764_141_1001 rfl rfl rfl

private theorem s764_141_571_475 : blockEstimate 764 141 571 475 = 0xf22a8f88 :=
  block_append p764_141_571 s764_141_786_260 rfl rfl rfl

private theorem s764_141_141_905 : blockEstimate 764 141 141 905 = 0x1f060dc24 :=
  block_append s764_141_141_430 s764_141_571_475 rfl rfl rfl

theorem moment764_141 : momentEstimate 764 141 = 0x1f060dc24 := s764_141_141_905

end HighCore82219BankProof
