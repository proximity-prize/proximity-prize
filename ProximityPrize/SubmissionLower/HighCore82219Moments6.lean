import ProximityPrize.SubmissionLower.HighCore82219Moments5

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)

set_option maxHeartbeats 14000000

private theorem p2827_594_594 : blockEstimate 2827 594 594 215 = 0x10af20386 := by decide +kernel
private theorem p2827_594_809 : blockEstimate 2827 594 809 215 = 0x6bd9afc0e := by decide +kernel
private theorem p2827_594_1024 : blockEstimate 2827 594 1024 215 = 0x10ba00db13 := by decide +kernel
private theorem p2827_594_1239 : blockEstimate 2827 594 1239 215 = 0x1c1155017c := by decide +kernel
private theorem p2827_594_1454 : blockEstimate 2827 594 1454 215 = 0x250efdddf0 := by decide +kernel
private theorem p2827_594_1669 : blockEstimate 2827 594 1669 215 = 0x2b4bba1f5a := by decide +kernel
private theorem p2827_594_1884 : blockEstimate 2827 594 1884 215 = 0x2ec789c5ba := by decide +kernel
private theorem p2827_594_2099 : blockEstimate 2827 594 2099 215 = 0x2f826cd110 := by decide +kernel
private theorem p2827_594_2314 : blockEstimate 2827 594 2314 215 = 0x2d7c63415c := by decide +kernel
private theorem p2827_594_2529 : blockEstimate 2827 594 2529 215 = 0x28b56d169e := by decide +kernel
private theorem p2827_594_2744 : blockEstimate 2827 594 2744 215 = 0x21422aa07c := by decide +kernel
private theorem p2827_594_2959 : blockEstimate 2827 594 2959 215 = 0x1873ec5243 := by decide +kernel
private theorem p2827_594_3174 : blockEstimate 2827 594 3174 215 = 0xfebd00e21 := by decide +kernel
private theorem p2827_594_3389 : blockEstimate 2827 594 3389 215 = 0x88f291d43 := by decide +kernel
private theorem p2827_594_3604 : blockEstimate 2827 594 3604 215 = 0x32df7d18f := by decide +kernel
private theorem p2827_594_3819 : blockEstimate 2827 594 3819 196 = 0x68ae17fe := by decide +kernel

private theorem s2827_594_594_430 : blockEstimate 2827 594 594 430 = 0x7c88cff94 :=
  block_append p2827_594_594 p2827_594_809 rfl rfl rfl

private theorem s2827_594_1024_430 : blockEstimate 2827 594 1024 430 = 0x2ccb55dc8f :=
  block_append p2827_594_1024 p2827_594_1239 rfl rfl rfl

private theorem s2827_594_594_860 : blockEstimate 2827 594 594 860 = 0x3493e2dc23 :=
  block_append s2827_594_594_430 s2827_594_1024_430 rfl rfl rfl

private theorem s2827_594_1454_430 : blockEstimate 2827 594 1454 430 = 0x505ab7fd4a :=
  block_append p2827_594_1454 p2827_594_1669 rfl rfl rfl

private theorem s2827_594_1884_430 : blockEstimate 2827 594 1884 430 = 0x5e49f696ca :=
  block_append p2827_594_1884 p2827_594_2099 rfl rfl rfl

private theorem s2827_594_1454_860 : blockEstimate 2827 594 1454 860 = 0xaea4ae9414 :=
  block_append s2827_594_1454_430 s2827_594_1884_430 rfl rfl rfl

private theorem s2827_594_594_1720 : blockEstimate 2827 594 594 1720 = 0xe338917037 :=
  block_append s2827_594_594_860 s2827_594_1454_860 rfl rfl rfl

private theorem s2827_594_2314_430 : blockEstimate 2827 594 2314 430 = 0x5631d057fa :=
  block_append p2827_594_2314 p2827_594_2529 rfl rfl rfl

private theorem s2827_594_2744_430 : blockEstimate 2827 594 2744 430 = 0x39b616f2bf :=
  block_append p2827_594_2744 p2827_594_2959 rfl rfl rfl

private theorem s2827_594_2314_860 : blockEstimate 2827 594 2314 860 = 0x8fe7e74ab9 :=
  block_append s2827_594_2314_430 s2827_594_2744_430 rfl rfl rfl

private theorem s2827_594_3174_430 : blockEstimate 2827 594 3174 430 = 0x187af92b64 :=
  block_append p2827_594_3174 p2827_594_3389 rfl rfl rfl

private theorem s2827_594_3604_411 : blockEstimate 2827 594 3604 411 = 0x396a5e98d :=
  block_append p2827_594_3604 p2827_594_3819 rfl rfl rfl

private theorem s2827_594_3174_841 : blockEstimate 2827 594 3174 841 = 0x1c119f14f1 :=
  block_append s2827_594_3174_430 s2827_594_3604_411 rfl rfl rfl

private theorem s2827_594_2314_1701 : blockEstimate 2827 594 2314 1701 = 0xabf9865faa :=
  block_append s2827_594_2314_860 s2827_594_3174_841 rfl rfl rfl

private theorem s2827_594_594_3421 : blockEstimate 2827 594 594 3421 = 0x18f3217cfe1 :=
  block_append s2827_594_594_1720 s2827_594_2314_1701 rfl rfl rfl

theorem moment2827_594 : momentEstimate 2827 594 = 0x18f3217cfe1 := s2827_594_594_3421

private theorem p2950_628_628 : blockEstimate 2950 628 628 215 = 0x117424d3a := by decide +kernel
private theorem p2950_628_843 : blockEstimate 2950 628 843 215 = 0x7131eae0a := by decide +kernel
private theorem p2950_628_1058 : blockEstimate 2950 628 1058 215 = 0x11a45c2171 := by decide +kernel
private theorem p2950_628_1273 : blockEstimate 2950 628 1273 215 = 0x1e42d56a0a := by decide +kernel
private theorem p2950_628_1488 : blockEstimate 2950 628 1488 215 = 0x28b6a44a32 := by decide +kernel
private theorem p2950_628_1703 : blockEstimate 2950 628 1703 215 = 0x30413e8674 := by decide +kernel
private theorem p2950_628_1918 : blockEstimate 2950 628 1918 215 = 0x34e2a41ed0 := by decide +kernel
private theorem p2950_628_2133 : blockEstimate 2950 628 2133 215 = 0x369ad51346 := by decide +kernel
private theorem p2950_628_2348 : blockEstimate 2950 628 2348 215 = 0x3569d163d6 := by decide +kernel
private theorem p2950_628_2563 : blockEstimate 2950 628 2563 215 = 0x314f991080 := by decide +kernel
private theorem p2950_628_2778 : blockEstimate 2950 628 2778 215 = 0x2a4ce24049 := by decide +kernel
private theorem p2950_628_2993 : blockEstimate 2950 628 2993 215 = 0x2108645f65 := by decide +kernel
private theorem p2950_628_3208 : blockEstimate 2950 628 3208 215 = 0x1767e8060e := by decide +kernel
private theorem p2950_628_3423 : blockEstimate 2950 628 3423 215 = 0xe871f41b9 := by decide +kernel
private theorem p2950_628_3638 : blockEstimate 2950 628 3638 215 = 0x7367c93ce := by decide +kernel
private theorem p2950_628_3853 : blockEstimate 2950 628 3853 215 = 0x24165aba8 := by decide +kernel
private theorem p2950_628_4068 : blockEstimate 2950 628 4068 138 = 0x26e949e2 := by decide +kernel

private theorem s2950_628_628_430 : blockEstimate 2950 628 628 430 = 0x82a60fb44 :=
  block_append p2950_628_628 p2950_628_843 rfl rfl rfl

private theorem s2950_628_1058_430 : blockEstimate 2950 628 1058 430 = 0x2fe7318b7b :=
  block_append p2950_628_1058 p2950_628_1273 rfl rfl rfl

private theorem s2950_628_628_860 : blockEstimate 2950 628 628 860 = 0x38119286bf :=
  block_append s2950_628_628_430 s2950_628_1058_430 rfl rfl rfl

private theorem s2950_628_1488_430 : blockEstimate 2950 628 1488 430 = 0x58f7e2d0a6 :=
  block_append p2950_628_1488 p2950_628_1703 rfl rfl rfl

private theorem s2950_628_1918_430 : blockEstimate 2950 628 1918 430 = 0x6b7d793216 :=
  block_append p2950_628_1918 p2950_628_2133 rfl rfl rfl

private theorem s2950_628_1488_860 : blockEstimate 2950 628 1488 860 = 0xc4755c02bc :=
  block_append s2950_628_1488_430 s2950_628_1918_430 rfl rfl rfl

private theorem s2950_628_628_1720 : blockEstimate 2950 628 628 1720 = 0xfc86ee897b :=
  block_append s2950_628_628_860 s2950_628_1488_860 rfl rfl rfl

private theorem s2950_628_2348_430 : blockEstimate 2950 628 2348 430 = 0x66b96a7456 :=
  block_append p2950_628_2348 p2950_628_2563 rfl rfl rfl

private theorem s2950_628_2778_430 : blockEstimate 2950 628 2778 430 = 0x4b55469fae :=
  block_append p2950_628_2778 p2950_628_2993 rfl rfl rfl

private theorem s2950_628_2348_860 : blockEstimate 2950 628 2348 860 = 0xb20eb11404 :=
  block_append s2950_628_2348_430 s2950_628_2778_430 rfl rfl rfl

private theorem s2950_628_3208_430 : blockEstimate 2950 628 3208 430 = 0x25ef0747c7 :=
  block_append p2950_628_3208 p2950_628_3423 rfl rfl rfl

private theorem s2950_628_3853_353 : blockEstimate 2950 628 3853 353 = 0x2684ef58a :=
  block_append p2950_628_3853 p2950_628_4068 rfl rfl rfl

private theorem s2950_628_3638_568 : blockEstimate 2950 628 3638 568 = 0x99ecb8958 :=
  block_append p2950_628_3638 s2950_628_3853_353 rfl rfl rfl

private theorem s2950_628_3208_998 : blockEstimate 2950 628 3208 998 = 0x2f8dd2d11f :=
  block_append s2950_628_3208_430 s2950_628_3638_568 rfl rfl rfl

private theorem s2950_628_2348_1858 : blockEstimate 2950 628 2348 1858 = 0xe19c83e523 :=
  block_append s2950_628_2348_860 s2950_628_3208_998 rfl rfl rfl

private theorem s2950_628_628_3578 : blockEstimate 2950 628 628 3578 = 0x1de23726e9e :=
  block_append s2950_628_628_1720 s2950_628_2348_1858 rfl rfl rfl

theorem moment2950_628 : momentEstimate 2950 628 = 0x1de23726e9e := s2950_628_628_3578

end HighCore82219BankProof
