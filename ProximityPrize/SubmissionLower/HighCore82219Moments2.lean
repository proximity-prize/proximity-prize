import ProximityPrize.SubmissionLower.HighCore82219Moments1

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)

set_option maxHeartbeats 14000000

private theorem p775_163_163 : blockEstimate 775 163 163 215 = 0x3cb7a05b := by decide +kernel
private theorem p775_163_378 : blockEstimate 775 163 378 215 = 0xddd32ef2 := by decide +kernel
private theorem p775_163_593 : blockEstimate 775 163 593 215 = 0xdc557eb6 := by decide +kernel
private theorem p775_163_808 : blockEstimate 775 163 808 215 = 0x4d8df3dd := by decide +kernel
private theorem p775_163_1023 : blockEstimate 775 163 1023 78 = 0x1d81692 := by decide +kernel

private theorem s775_163_163_430 : blockEstimate 775 163 163 430 = 0x11a8acf4d :=
  block_append (B := 775) (J := 163) (start := 163) (next := 378)
    (a := 215) (b := 215) (n := 430) (x := 0x3cb7a05b) (y := 0xddd32ef2) (z := 0x11a8acf4d)
    p775_163_163 p775_163_378 rfl rfl rfl

private theorem s775_163_808_293 : blockEstimate 775 163 808 293 = 0x4f660a6f :=
  block_append (B := 775) (J := 163) (start := 808) (next := 1023)
    (a := 215) (b := 78) (n := 293) (x := 0x4d8df3dd) (y := 0x1d81692) (z := 0x4f660a6f)
    p775_163_808 p775_163_1023 rfl rfl rfl

private theorem s775_163_593_508 : blockEstimate 775 163 593 508 = 0x12bbb8925 :=
  block_append (B := 775) (J := 163) (start := 593) (next := 808)
    (a := 215) (b := 293) (n := 508) (x := 0xdc557eb6) (y := 0x4f660a6f) (z := 0x12bbb8925)
    p775_163_593 s775_163_808_293 rfl rfl rfl

private theorem s775_163_163_938 : blockEstimate 775 163 163 938 = 0x246465872 :=
  block_append (B := 775) (J := 163) (start := 163) (next := 593)
    (a := 430) (b := 508) (n := 938) (x := 0x11a8acf4d) (y := 0x12bbb8925) (z := 0x246465872)
    s775_163_163_430 s775_163_593_508 rfl rfl rfl

theorem moment775_163 : momentEstimate 775 163 = 0x246465872 := s775_163_163_938

private theorem p908_191_191 : blockEstimate 908 191 191 215 = 0x4abca5d0 := by decide +kernel
private theorem p908_191_406 : blockEstimate 908 191 406 215 = 0x13e8a84c0 := by decide +kernel
private theorem p908_191_621 : blockEstimate 908 191 621 215 = 0x18a73fa60 := by decide +kernel
private theorem p908_191_836 : blockEstimate 908 191 836 215 = 0xfcdb7219 := by decide +kernel
private theorem p908_191_1051 : blockEstimate 908 191 1051 215 = 0x36d7aa1d := by decide +kernel
private theorem p908_191_1266 : blockEstimate 908 191 1266 24 = 0x12de84 := by decide +kernel

private theorem s908_191_406_430 : blockEstimate 908 191 406 430 = 0x2c8fe7f20 :=
  block_append (B := 908) (J := 191) (start := 406) (next := 621)
    (a := 215) (b := 215) (n := 430) (x := 0x13e8a84c0) (y := 0x18a73fa60) (z := 0x2c8fe7f20)
    p908_191_406 p908_191_621 rfl rfl rfl

private theorem s908_191_191_645 : blockEstimate 908 191 191 645 = 0x313bb24f0 :=
  block_append (B := 908) (J := 191) (start := 191) (next := 406)
    (a := 215) (b := 430) (n := 645) (x := 0x4abca5d0) (y := 0x2c8fe7f20) (z := 0x313bb24f0)
    p908_191_191 s908_191_406_430 rfl rfl rfl

private theorem s908_191_1051_239 : blockEstimate 908 191 1051 239 = 0x36ea88a1 :=
  block_append (B := 908) (J := 191) (start := 1051) (next := 1266)
    (a := 215) (b := 24) (n := 239) (x := 0x36d7aa1d) (y := 0x12de84) (z := 0x36ea88a1)
    p908_191_1051 p908_191_1266 rfl rfl rfl

private theorem s908_191_836_454 : blockEstimate 908 191 836 454 = 0x133c5faba :=
  block_append (B := 908) (J := 191) (start := 836) (next := 1051)
    (a := 215) (b := 239) (n := 454) (x := 0xfcdb7219) (y := 0x36ea88a1) (z := 0x133c5faba)
    p908_191_836 s908_191_1051_239 rfl rfl rfl

private theorem s908_191_191_1099 : blockEstimate 908 191 191 1099 = 0x447811faa :=
  block_append (B := 908) (J := 191) (start := 191) (next := 836)
    (a := 645) (b := 454) (n := 1099) (x := 0x313bb24f0) (y := 0x133c5faba) (z := 0x447811faa)
    s908_191_191_645 s908_191_836_454 rfl rfl rfl

theorem moment908_191 : momentEstimate 908 191 = 0x447811faa := s908_191_191_1099

private theorem p925_200_200 : blockEstimate 925 200 200 215 = 0x4c82c692 := by decide +kernel
private theorem p925_200_415 : blockEstimate 925 200 415 215 = 0x15071f817 := by decide +kernel
private theorem p925_200_630 : blockEstimate 925 200 630 215 = 0x1abd27cf4 := by decide +kernel
private theorem p925_200_845 : blockEstimate 925 200 845 215 = 0x1215838ad := by decide +kernel
private theorem p925_200_1060 : blockEstimate 925 200 1060 215 = 0x4a722064 := by decide +kernel
private theorem p925_200_1275 : blockEstimate 925 200 1275 50 = 0x9c98f4 := by decide +kernel

private theorem s925_200_415_430 : blockEstimate 925 200 415 430 = 0x2fc44750b :=
  block_append (B := 925) (J := 200) (start := 415) (next := 630)
    (a := 215) (b := 215) (n := 430) (x := 0x15071f817) (y := 0x1abd27cf4) (z := 0x2fc44750b)
    p925_200_415 p925_200_630 rfl rfl rfl

private theorem s925_200_200_645 : blockEstimate 925 200 200 645 = 0x348c73b9d :=
  block_append (B := 925) (J := 200) (start := 200) (next := 415)
    (a := 215) (b := 430) (n := 645) (x := 0x4c82c692) (y := 0x2fc44750b) (z := 0x348c73b9d)
    p925_200_200 s925_200_415_430 rfl rfl rfl

private theorem s925_200_1060_265 : blockEstimate 925 200 1060 265 = 0x4b0eb958 :=
  block_append (B := 925) (J := 200) (start := 1060) (next := 1275)
    (a := 215) (b := 50) (n := 265) (x := 0x4a722064) (y := 0x9c98f4) (z := 0x4b0eb958)
    p925_200_1060 p925_200_1275 rfl rfl rfl

private theorem s925_200_845_480 : blockEstimate 925 200 845 480 = 0x16c66f205 :=
  block_append (B := 925) (J := 200) (start := 845) (next := 1060)
    (a := 215) (b := 265) (n := 480) (x := 0x1215838ad) (y := 0x4b0eb958) (z := 0x16c66f205)
    p925_200_845 s925_200_1060_265 rfl rfl rfl

private theorem s925_200_200_1125 : blockEstimate 925 200 200 1125 = 0x4b52e2da2 :=
  block_append (B := 925) (J := 200) (start := 200) (next := 845)
    (a := 645) (b := 480) (n := 1125) (x := 0x348c73b9d) (y := 0x16c66f205) (z := 0x4b52e2da2)
    s925_200_200_645 s925_200_845_480 rfl rfl rfl

theorem moment925_200 : momentEstimate 925 200 = 0x4b52e2da2 := s925_200_200_1125

private theorem p976_192_192 : blockEstimate 976 192 192 215 = 0x518c3ac0 := by decide +kernel
private theorem p976_192_407 : blockEstimate 976 192 407 215 = 0x165a73bf2 := by decide +kernel
private theorem p976_192_622 : blockEstimate 976 192 622 215 = 0x1d662d306 := by decide +kernel
private theorem p976_192_837 : blockEstimate 976 192 837 215 = 0x163f6bfe0 := by decide +kernel
private theorem p976_192_1052 : blockEstimate 976 192 1052 215 = 0x755371f6 := by decide +kernel
private theorem p976_192_1267 : blockEstimate 976 192 1267 93 = 0x3e911c4 := by decide +kernel

private theorem s976_192_407_430 : blockEstimate 976 192 407 430 = 0x33c0a0ef8 :=
  block_append (B := 976) (J := 192) (start := 407) (next := 622)
    (a := 215) (b := 215) (n := 430) (x := 0x165a73bf2) (y := 0x1d662d306) (z := 0x33c0a0ef8)
    p976_192_407 p976_192_622 rfl rfl rfl

private theorem s976_192_192_645 : blockEstimate 976 192 192 645 = 0x38d9649b8 :=
  block_append (B := 976) (J := 192) (start := 192) (next := 407)
    (a := 215) (b := 430) (n := 645) (x := 0x518c3ac0) (y := 0x33c0a0ef8) (z := 0x38d9649b8)
    p976_192_192 s976_192_407_430 rfl rfl rfl

private theorem s976_192_1052_308 : blockEstimate 976 192 1052 308 = 0x793c83ba :=
  block_append (B := 976) (J := 192) (start := 1052) (next := 1267)
    (a := 215) (b := 93) (n := 308) (x := 0x755371f6) (y := 0x3e911c4) (z := 0x793c83ba)
    p976_192_1052 p976_192_1267 rfl rfl rfl

private theorem s976_192_837_523 : blockEstimate 976 192 837 523 = 0x1dd33439a :=
  block_append (B := 976) (J := 192) (start := 837) (next := 1052)
    (a := 215) (b := 308) (n := 523) (x := 0x163f6bfe0) (y := 0x793c83ba) (z := 0x1dd33439a)
    p976_192_837 s976_192_1052_308 rfl rfl rfl

private theorem s976_192_192_1168 : blockEstimate 976 192 192 1168 = 0x56ac98d52 :=
  block_append (B := 976) (J := 192) (start := 192) (next := 837)
    (a := 645) (b := 523) (n := 1168) (x := 0x38d9649b8) (y := 0x1dd33439a) (z := 0x56ac98d52)
    s976_192_192_645 s976_192_837_523 rfl rfl rfl

theorem moment976_192 : momentEstimate 976 192 = 0x56ac98d52 := s976_192_192_1168

private theorem p1116_251_251 : blockEstimate 1116 251 251 215 = 0x5fa7e522 := by decide +kernel
private theorem p1116_251_466 : blockEstimate 1116 251 466 215 = 0x1ee6391b1 := by decide +kernel
private theorem p1116_251_681 : blockEstimate 1116 251 681 215 = 0x2f6db7e16 := by decide +kernel
private theorem p1116_251_896 : blockEstimate 1116 251 896 215 = 0x2d52edb78 := by decide +kernel
private theorem p1116_251_1111 : blockEstimate 1116 251 1111 215 = 0x1afbbf34b := by decide +kernel
private theorem p1116_251_1326 : blockEstimate 1116 251 1326 215 = 0x784fafe1 := by decide +kernel
private theorem p1116_251_1541 : blockEstimate 1116 251 1541 77 = 0x2987946 := by decide +kernel

private theorem s1116_251_466_430 : blockEstimate 1116 251 466 430 = 0x4e53f0fc7 :=
  block_append (B := 1116) (J := 251) (start := 466) (next := 681)
    (a := 215) (b := 215) (n := 430) (x := 0x1ee6391b1) (y := 0x2f6db7e16) (z := 0x4e53f0fc7)
    p1116_251_466 p1116_251_681 rfl rfl rfl

private theorem s1116_251_251_645 : blockEstimate 1116 251 251 645 = 0x544e6f4e9 :=
  block_append (B := 1116) (J := 251) (start := 251) (next := 466)
    (a := 215) (b := 430) (n := 645) (x := 0x5fa7e522) (y := 0x4e53f0fc7) (z := 0x544e6f4e9)
    p1116_251_251 s1116_251_466_430 rfl rfl rfl

private theorem s1116_251_896_430 : blockEstimate 1116 251 896 430 = 0x484eacec3 :=
  block_append (B := 1116) (J := 251) (start := 896) (next := 1111)
    (a := 215) (b := 215) (n := 430) (x := 0x2d52edb78) (y := 0x1afbbf34b) (z := 0x484eacec3)
    p1116_251_896 p1116_251_1111 rfl rfl rfl

private theorem s1116_251_1326_292 : blockEstimate 1116 251 1326 292 = 0x7ae82927 :=
  block_append (B := 1116) (J := 251) (start := 1326) (next := 1541)
    (a := 215) (b := 77) (n := 292) (x := 0x784fafe1) (y := 0x2987946) (z := 0x7ae82927)
    p1116_251_1326 p1116_251_1541 rfl rfl rfl

private theorem s1116_251_896_722 : blockEstimate 1116 251 896 722 = 0x4ffd2f7ea :=
  block_append (B := 1116) (J := 251) (start := 896) (next := 1326)
    (a := 430) (b := 292) (n := 722) (x := 0x484eacec3) (y := 0x7ae82927) (z := 0x4ffd2f7ea)
    s1116_251_896_430 s1116_251_1326_292 rfl rfl rfl

private theorem s1116_251_251_1367 : blockEstimate 1116 251 251 1367 = 0xa44b9ecd3 :=
  block_append (B := 1116) (J := 251) (start := 251) (next := 896)
    (a := 645) (b := 722) (n := 1367) (x := 0x544e6f4e9) (y := 0x4ffd2f7ea) (z := 0xa44b9ecd3)
    s1116_251_251_645 s1116_251_896_722 rfl rfl rfl

theorem moment1116_251 : momentEstimate 1116 251 = 0xa44b9ecd3 := s1116_251_251_1367

private theorem p1195_253_253 : blockEstimate 1195 253 253 215 = 0x67908906 := by decide +kernel
private theorem p1195_253_468 : blockEstimate 1195 253 468 215 = 0x2225ea072 := by decide +kernel
private theorem p1195_253_683 : blockEstimate 1195 253 683 215 = 0x364cf9736 := by decide +kernel
private theorem p1195_253_898 : blockEstimate 1195 253 898 215 = 0x37adaff07 := by decide +kernel
private theorem p1195_253_1113 : blockEstimate 1195 253 1113 215 = 0x26dd29909 := by decide +kernel
private theorem p1195_253_1328 : blockEstimate 1195 253 1328 215 = 0xf1b44f69 := by decide +kernel
private theorem p1195_253_1543 : blockEstimate 1195 253 1543 158 = 0x169ab314 := by decide +kernel

private theorem s1195_253_468_430 : blockEstimate 1195 253 468 430 = 0x5872e37a8 :=
  block_append (B := 1195) (J := 253) (start := 468) (next := 683)
    (a := 215) (b := 215) (n := 430) (x := 0x2225ea072) (y := 0x364cf9736) (z := 0x5872e37a8)
    p1195_253_468 p1195_253_683 rfl rfl rfl

private theorem s1195_253_253_645 : blockEstimate 1195 253 253 645 = 0x5eebec0ae :=
  block_append (B := 1195) (J := 253) (start := 253) (next := 468)
    (a := 215) (b := 430) (n := 645) (x := 0x67908906) (y := 0x5872e37a8) (z := 0x5eebec0ae)
    p1195_253_253 s1195_253_468_430 rfl rfl rfl

private theorem s1195_253_898_430 : blockEstimate 1195 253 898 430 = 0x5e8ad9810 :=
  block_append (B := 1195) (J := 253) (start := 898) (next := 1113)
    (a := 215) (b := 215) (n := 430) (x := 0x37adaff07) (y := 0x26dd29909) (z := 0x5e8ad9810)
    p1195_253_898 p1195_253_1113 rfl rfl rfl

private theorem s1195_253_1328_373 : blockEstimate 1195 253 1328 373 = 0x1084f027d :=
  block_append (B := 1195) (J := 253) (start := 1328) (next := 1543)
    (a := 215) (b := 158) (n := 373) (x := 0xf1b44f69) (y := 0x169ab314) (z := 0x1084f027d)
    p1195_253_1328 p1195_253_1543 rfl rfl rfl

private theorem s1195_253_898_803 : blockEstimate 1195 253 898 803 = 0x6f0fc9a8d :=
  block_append (B := 1195) (J := 253) (start := 898) (next := 1328)
    (a := 430) (b := 373) (n := 803) (x := 0x5e8ad9810) (y := 0x1084f027d) (z := 0x6f0fc9a8d)
    s1195_253_898_430 s1195_253_1328_373 rfl rfl rfl

private theorem s1195_253_253_1448 : blockEstimate 1195 253 253 1448 = 0xcdfbb5b3b :=
  block_append (B := 1195) (J := 253) (start := 253) (next := 898)
    (a := 645) (b := 803) (n := 1448) (x := 0x5eebec0ae) (y := 0x6f0fc9a8d) (z := 0xcdfbb5b3b)
    s1195_253_253_645 s1195_253_898_803 rfl rfl rfl

theorem moment1195_253 : momentEstimate 1195 253 = 0xcdfbb5b3b := s1195_253_253_1448

end HighCore82219BankProof
