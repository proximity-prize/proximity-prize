import ProximityPrize.SubmissionLower.High55Wide2524Source
import ProximityPrize.SubmissionLower.HighCore82219Moments11

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High55Wide2524BankProof

open P3_7_1 (BankOK checked)
open P1_7_1 (groupedPoleMoment)
open P1_7_1_3 (momentEstimate blockEstimate block_append)
open High55Wide2524
open HighCore82219BankProof

set_option maxHeartbeats 6000000

local notation "pass!" depth "," grade "," deriv "," nodes "," moment ";" witness =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) witness

private theorem chunk2160 : blockEstimate 10225 2160 2160 155 = 0x17d410a31 := by decide +kernel
private theorem chunk2315 : blockEstimate 10225 2160 2315 155 = 0xa2ce68729 := by decide +kernel
private theorem chunk2470 : blockEstimate 10225 2160 2470 155 = 0x1b1ef0b403 := by decide +kernel
private theorem chunk2625 : blockEstimate 10225 2160 2625 155 = 0x33ec296aec := by decide +kernel
private theorem chunk2780 : blockEstimate 10225 2160 2780 155 = 0x542d5a8611 := by decide +kernel
private theorem chunk2935 : blockEstimate 10225 2160 2935 155 = 0x7b7b4ddf9f := by decide +kernel
private theorem chunk3090 : blockEstimate 10225 2160 3090 155 = 0xa96ecd51c3 := by decide +kernel
private theorem chunk3245 : blockEstimate 10225 2160 3245 155 = 0xdda0a2b6aa := by decide +kernel
private theorem chunk3400 : blockEstimate 10225 2160 3400 155 = 0x117a997e881 := by decide +kernel
private theorem chunk3555 : blockEstimate 10225 2160 3555 155 = 0x1572276c175 := by decide +kernel
private theorem chunk3710 : blockEstimate 10225 2160 3710 155 = 0x19ba4091bb3 := by decide +kernel
private theorem chunk3865 : blockEstimate 10225 2160 3865 155 = 0x1e4c718d168 := by decide +kernel
private theorem chunk4020 : blockEstimate 10225 2160 4020 155 = 0x232246fbcc1 := by decide +kernel
private theorem chunk4175 : blockEstimate 10225 2160 4175 155 = 0x28354c36e49 := by decide +kernel
private theorem chunk4330 : blockEstimate 10225 2160 4330 155 = 0x2d68ecb2b1a := by decide +kernel
private theorem chunk4485 : blockEstimate 10225 2160 4485 155 = 0x327010f6051 := by decide +kernel
private theorem chunk4640 : blockEstimate 10225 2160 4640 155 = 0x373b403aa22 := by decide +kernel
private theorem chunk4795 : blockEstimate 10225 2160 4795 155 = 0x3bca7a8088d := by decide +kernel
private theorem chunk4950 : blockEstimate 10225 2160 4950 155 = 0x401dbfc7b92 := by decide +kernel
private theorem chunk5105 : blockEstimate 10225 2160 5105 155 = 0x44351010331 := by decide +kernel
private theorem chunk5260 : blockEstimate 10225 2160 5260 155 = 0x48106b59f6a := by decide +kernel
private theorem chunk5415 : blockEstimate 10225 2160 5415 155 = 0x4bafd1a503d := by decide +kernel
private theorem chunk5570 : blockEstimate 10225 2160 5570 155 = 0x4f1342f15aa := by decide +kernel
private theorem chunk5725 : blockEstimate 10225 2160 5725 155 = 0x523abf3efb1 := by decide +kernel
private theorem chunk5880 : blockEstimate 10225 2160 5880 155 = 0x5526468de52 := by decide +kernel
private theorem chunk6035 : blockEstimate 10225 2160 6035 155 = 0x57d5d8de18d := by decide +kernel
private theorem chunk6190 : blockEstimate 10225 2160 6190 155 = 0x5a49762f962 := by decide +kernel
private theorem chunk6345 : blockEstimate 10225 2160 6345 155 = 0x5c811e825d1 := by decide +kernel
private theorem chunk6500 : blockEstimate 10225 2160 6500 155 = 0x5e7cd1d66da := by decide +kernel
private theorem chunk6655 : blockEstimate 10225 2160 6655 155 = 0x603c902bc7d := by decide +kernel
private theorem chunk6810 : blockEstimate 10225 2160 6810 155 = 0x61c059826ba := by decide +kernel
private theorem chunk6965 : blockEstimate 10225 2160 6965 155 = 0x63082dda591 := by decide +kernel
private theorem chunk7120 : blockEstimate 10225 2160 7120 155 = 0x64140d33902 := by decide +kernel
private theorem chunk7275 : blockEstimate 10225 2160 7275 155 = 0x64e3f78e10d := by decide +kernel
private theorem chunk7430 : blockEstimate 10225 2160 7430 155 = 0x6577ece9db2 := by decide +kernel
private theorem chunk7585 : blockEstimate 10225 2160 7585 155 = 0x65cfed46ef1 := by decide +kernel
private theorem chunk7740 : blockEstimate 10225 2160 7740 155 = 0x65ebf8a54ca := by decide +kernel
private theorem chunk7895 : blockEstimate 10225 2160 7895 155 = 0x65cc0f04f3d := by decide +kernel
private theorem chunk8050 : blockEstimate 10225 2160 8050 155 = 0x65703065e4a := by decide +kernel
private theorem chunk8205 : blockEstimate 10225 2160 8205 155 = 0x64d85cc81f1 := by decide +kernel
private theorem chunk8360 : blockEstimate 10225 2160 8360 155 = 0x6404942ba32 := by decide +kernel
private theorem chunk8515 : blockEstimate 10225 2160 8515 155 = 0x62f4d69070d := by decide +kernel
private theorem chunk8670 : blockEstimate 10225 2160 8670 155 = 0x61a923f6882 := by decide +kernel
private theorem chunk8825 : blockEstimate 10225 2160 8825 155 = 0x60217c5de91 := by decide +kernel
private theorem chunk8980 : blockEstimate 10225 2160 8980 155 = 0x5e5ddfc693a := by decide +kernel
private theorem chunk9135 : blockEstimate 10225 2160 9135 155 = 0x5c5e4e3087d := by decide +kernel
private theorem chunk9290 : blockEstimate 10225 2160 9290 155 = 0x5a22c79bc5a := by decide +kernel
private theorem chunk9445 : blockEstimate 10225 2160 9445 155 = 0x57ab4c084d1 := by decide +kernel
private theorem chunk9600 : blockEstimate 10225 2160 9600 155 = 0x54f7db761e2 := by decide +kernel
private theorem chunk9755 : blockEstimate 10225 2160 9755 155 = 0x520875e538d := by decide +kernel
private theorem chunk9910 : blockEstimate 10225 2160 9910 155 = 0x4edd1b559d2 := by decide +kernel
private theorem chunk10065 : blockEstimate 10225 2160 10065 155 = 0x4b75cbc74b1 := by decide +kernel
private theorem chunk10220 : blockEstimate 10225 2160 10220 155 = 0x47d8f455a74 := by decide +kernel
private theorem chunk10375 : blockEstimate 10225 2160 10375 155 = 0x44242712aab := by decide +kernel
private theorem chunk10530 : blockEstimate 10225 2160 10530 155 = 0x40635368fa4 := by decide +kernel
private theorem chunk10685 : blockEstimate 10225 2160 10685 155 = 0x3c9b158ca20 := by decide +kernel
private theorem chunk10840 : blockEstimate 10225 2160 10840 155 = 0x38cfec0f6ba := by decide +kernel
private theorem chunk10995 : blockEstimate 10225 2160 10995 155 = 0x350637e2f2c := by decide +kernel
private theorem chunk11150 : blockEstimate 10225 2160 11150 155 = 0x31423c5f8db := by decide +kernel
private theorem chunk11305 : blockEstimate 10225 2160 11305 155 = 0x2d881f3db82 := by decide +kernel
private theorem chunk11460 : blockEstimate 10225 2160 11460 155 = 0x29dbe89caf9 := by decide +kernel
private theorem chunk11615 : blockEstimate 10225 2160 11615 155 = 0x264182fb7dc := by decide +kernel
private theorem chunk11770 : blockEstimate 10225 2160 11770 155 = 0x22bcbb40252 := by decide +kernel
private theorem chunk11925 : blockEstimate 10225 2160 11925 155 = 0x1f5140b0663 := by decide +kernel
private theorem chunk12080 : blockEstimate 10225 2160 12080 155 = 0x1c02a4f9378 := by decide +kernel
private theorem chunk12235 : blockEstimate 10225 2160 12235 155 = 0x18d45a12148 := by decide +kernel
private theorem chunk12390 : blockEstimate 10225 2160 12390 155 = 0x15c3b6ed18b := by decide +kernel
private theorem chunk12545 : blockEstimate 10225 2160 12545 155 = 0x12d7ffbee7f := by decide +kernel
private theorem chunk12700 : blockEstimate 10225 2160 12700 155 = 0x101a31961f2 := by decide +kernel
private theorem chunk12855 : blockEstimate 10225 2160 12855 155 = 0xd8c507f6d3 := by decide +kernel
private theorem chunk13010 : blockEstimate 10225 2160 13010 155 = 0xb30608ba24 := by decide +kernel
private theorem chunk13165 : blockEstimate 10225 2160 13165 155 = 0x90865c746c := by decide +kernel
private theorem chunk13320 : blockEstimate 10225 2160 13320 155 = 0x716644358a := by decide +kernel
private theorem chunk13475 : blockEstimate 10225 2160 13475 155 = 0x55c600c601 := by decide +kernel
private theorem chunk13630 : blockEstimate 10225 2160 13630 155 = 0x3dc5d3353f := by decide +kernel
private theorem chunk13785 : blockEstimate 10225 2160 13785 155 = 0x2985fc49fa := by decide +kernel
private theorem chunk13940 : blockEstimate 10225 2160 13940 155 = 0x1926bd15e2 := by decide +kernel
private theorem chunk14095 : blockEstimate 10225 2160 14095 155 = 0xcc8565f0e := by decide +kernel
private theorem chunk14250 : blockEstimate 10225 2160 14250 155 = 0x48b093758 := by decide +kernel
private theorem chunk14405 : blockEstimate 10225 2160 14405 140 = 0x8ef6b164 := by decide +kernel
private theorem joined2160_310 : blockEstimate 10225 2160 2160 310 = 0xbaa27915a :=
  block_append chunk2160 chunk2315 rfl rfl rfl

private theorem joined2625_310 : blockEstimate 10225 2160 2625 310 = 0x881983f0fd :=
  block_append chunk2625 chunk2780 rfl rfl rfl

private theorem joined2470_465 : blockEstimate 10225 2160 2470 465 = 0xa33874a500 :=
  block_append chunk2470 joined2625_310 rfl rfl rfl

private theorem joined2160_775 : blockEstimate 10225 2160 2160 775 = 0xaee29c365a :=
  block_append joined2160_310 joined2470_465 rfl rfl rfl

private theorem joined2935_310 : blockEstimate 10225 2160 2935 310 = 0x124ea1b3162 :=
  block_append chunk2935 chunk3090 rfl rfl rfl

private theorem joined3400_310 : blockEstimate 10225 2160 3400 310 = 0x26ecc0ea9f6 :=
  block_append chunk3400 chunk3555 rfl rfl rfl

private theorem joined3245_465 : blockEstimate 10225 2160 3245 465 = 0x34c6cb160a0 :=
  block_append chunk3245 joined3400_310 rfl rfl rfl

private theorem joined2935_775 : blockEstimate 10225 2160 2935 775 = 0x47156cc9202 :=
  block_append joined2935_310 joined3245_465 rfl rfl rfl

private theorem joined2160_1550 : blockEstimate 10225 2160 2160 1550 = 0x5203968c85c :=
  block_append joined2160_775 joined2935_775 rfl rfl rfl

private theorem joined3710_310 : blockEstimate 10225 2160 3710 310 = 0x3806b21ed1b :=
  block_append chunk3710 chunk3865 rfl rfl rfl

private theorem joined4175_310 : blockEstimate 10225 2160 4175 310 = 0x559e38e9963 :=
  block_append chunk4175 chunk4330 rfl rfl rfl

private theorem joined4020_465 : blockEstimate 10225 2160 4020 465 = 0x78c07fe5624 :=
  block_append chunk4020 joined4175_310 rfl rfl rfl

private theorem joined3710_775 : blockEstimate 10225 2160 3710 775 = 0xb0c7320433f :=
  block_append joined3710_310 joined4020_465 rfl rfl rfl

private theorem joined4485_310 : blockEstimate 10225 2160 4485 310 = 0x69ab5130a73 :=
  block_append chunk4485 chunk4640 rfl rfl rfl

private theorem joined4950_310 : blockEstimate 10225 2160 4950 310 = 0x8452cfd7ec3 :=
  block_append chunk4950 chunk5105 rfl rfl rfl

private theorem joined4795_465 : blockEstimate 10225 2160 4795 465 = 0xc01d4a58750 :=
  block_append chunk4795 joined4950_310 rfl rfl rfl

private theorem joined4485_775 : blockEstimate 10225 2160 4485 775 = 0x129c89b891c3 :=
  block_append joined4485_310 joined4795_465 rfl rfl rfl

private theorem joined3710_1550 : blockEstimate 10225 2160 3710 1550 = 0x1da8fcd8d502 :=
  block_append joined3710_775 joined4485_775 rfl rfl rfl

private theorem joined2160_3100 : blockEstimate 10225 2160 2160 3100 = 0x22c936419d5e :=
  block_append joined2160_1550 joined3710_1550 rfl rfl rfl

private theorem joined5260_310 : blockEstimate 10225 2160 5260 310 = 0x93c03cfefa7 :=
  block_append chunk5260 chunk5415 rfl rfl rfl

private theorem joined5725_310 : blockEstimate 10225 2160 5725 310 = 0xa76105cce03 :=
  block_append chunk5725 chunk5880 rfl rfl rfl

private theorem joined5570_465 : blockEstimate 10225 2160 5570 465 = 0xf67448be3ad :=
  block_append chunk5570 joined5725_310 rfl rfl rfl

private theorem joined5260_775 : blockEstimate 10225 2160 5260 775 = 0x18a3485bd354 :=
  block_append joined5260_310 joined5570_465 rfl rfl rfl

private theorem joined6035_310 : blockEstimate 10225 2160 6035 310 = 0xb21f4f0daef :=
  block_append chunk6035 chunk6190 rfl rfl rfl

private theorem joined6500_310 : blockEstimate 10225 2160 6500 310 = 0xbeb96202357 :=
  block_append chunk6500 chunk6655 rfl rfl rfl

private theorem joined6345_465 : blockEstimate 10225 2160 6345 465 = 0x11b3a8084928 :=
  block_append chunk6345 joined6500_310 rfl rfl rfl

private theorem joined6035_775 : blockEstimate 10225 2160 6035 775 = 0x1cd59cf92417 :=
  block_append joined6035_310 joined6345_465 rfl rfl rfl

private theorem joined5260_1550 : blockEstimate 10225 2160 5260 1550 = 0x3578e554f76b :=
  block_append joined5260_775 joined6035_775 rfl rfl rfl

private theorem joined6810_310 : blockEstimate 10225 2160 6810 310 = 0xc4c8875cc4b :=
  block_append chunk6810 chunk6965 rfl rfl rfl

private theorem joined7275_310 : blockEstimate 10225 2160 7275 310 = 0xca5be477ebf :=
  block_append chunk7275 chunk7430 rfl rfl rfl

private theorem joined7120_465 : blockEstimate 10225 2160 7120 465 = 0x12e6ff1ab7c1 :=
  block_append chunk7120 joined7275_310 rfl rfl rfl

private theorem joined6810_775 : blockEstimate 10225 2160 6810 775 = 0x1f338790840c :=
  block_append joined6810_310 joined7120_465 rfl rfl rfl

private theorem joined7585_310 : blockEstimate 10225 2160 7585 310 = 0xcbbbe5ec3bb :=
  block_append chunk7585 chunk7740 rfl rfl rfl

private theorem joined8050_310 : blockEstimate 10225 2160 8050 310 = 0xca488d2e03b :=
  block_append chunk8050 chunk8205 rfl rfl rfl

private theorem joined7895_465 : blockEstimate 10225 2160 7895 465 = 0x130149c32f78 :=
  block_append chunk7895 joined8050_310 rfl rfl rfl

private theorem joined7585_775 : blockEstimate 10225 2160 7585 775 = 0x1fbd0821f333 :=
  block_append joined7585_310 joined7895_465 rfl rfl rfl

private theorem joined6810_1550 : blockEstimate 10225 2160 6810 1550 = 0x3ef08fb2773f :=
  block_append joined6810_775 joined7585_775 rfl rfl rfl

private theorem joined5260_3100 : blockEstimate 10225 2160 5260 3100 = 0x746975076eaa :=
  block_append joined5260_1550 joined6810_1550 rfl rfl rfl

private theorem joined2160_6200 : blockEstimate 10225 2160 2160 6200 = 0x9732ab490c08 :=
  block_append joined2160_3100 joined5260_3100 rfl rfl rfl

private theorem joined8360_310 : blockEstimate 10225 2160 8360 310 = 0xc6f96abc13f :=
  block_append chunk8360 chunk8515 rfl rfl rfl

private theorem joined8825_310 : blockEstimate 10225 2160 8825 310 = 0xbe7f5c247cb :=
  block_append chunk8825 chunk8980 rfl rfl rfl

private theorem joined8670_465 : blockEstimate 10225 2160 8670 465 = 0x12028801b04d :=
  block_append chunk8670 joined8825_310 rfl rfl rfl

private theorem joined8360_775 : blockEstimate 10225 2160 8360 775 = 0x1e721ead718c :=
  block_append joined8360_310 joined8670_465 rfl rfl rfl

private theorem joined9135_310 : blockEstimate 10225 2160 9135 310 = 0xb68115cc4d7 :=
  block_append chunk9135 chunk9290 rfl rfl rfl

private theorem joined9600_310 : blockEstimate 10225 2160 9600 310 = 0xa700515b56f :=
  block_append chunk9600 chunk9755 rfl rfl rfl

private theorem joined9445_465 : blockEstimate 10225 2160 9445 465 = 0xfeab9d63a40 :=
  block_append chunk9445 joined9600_310 rfl rfl rfl

private theorem joined9135_775 : blockEstimate 10225 2160 9135 775 = 0x1b52cb32ff17 :=
  block_append joined9135_310 joined9445_465 rfl rfl rfl

private theorem joined8360_1550 : blockEstimate 10225 2160 8360 1550 = 0x39c4e9e070a3 :=
  block_append joined8360_775 joined9135_775 rfl rfl rfl

private theorem joined9910_310 : blockEstimate 10225 2160 9910 310 = 0x9a52e71ce83 :=
  block_append chunk9910 chunk10065 rfl rfl rfl

private theorem joined10375_310 : blockEstimate 10225 2160 10375 310 = 0x84877a7ba4f :=
  block_append chunk10375 chunk10530 rfl rfl rfl

private theorem joined10220_465 : blockEstimate 10225 2160 10220 465 = 0xcc606ed14c3 :=
  block_append chunk10220 joined10375_310 rfl rfl rfl

private theorem joined9910_775 : blockEstimate 10225 2160 9910 775 = 0x166b355ee346 :=
  block_append joined9910_310 joined10220_465 rfl rfl rfl

private theorem joined10685_310 : blockEstimate 10225 2160 10685 310 = 0x756b019c0da :=
  block_append chunk10685 chunk10840 rfl rfl rfl

private theorem joined11150_310 : blockEstimate 10225 2160 11150 310 = 0x5eca5b9d45d :=
  block_append chunk11150 chunk11305 rfl rfl rfl

private theorem joined10995_465 : blockEstimate 10225 2160 10995 465 = 0x93d09380389 :=
  block_append chunk10995 joined11150_310 rfl rfl rfl

private theorem joined10685_775 : blockEstimate 10225 2160 10685 775 = 0x1093b951c463 :=
  block_append joined10685_310 joined10995_465 rfl rfl rfl

private theorem joined9910_1550 : blockEstimate 10225 2160 9910 1550 = 0x26feeeb0a7a9 :=
  block_append joined9910_775 joined10685_775 rfl rfl rfl

private theorem joined8360_3100 : blockEstimate 10225 2160 8360 3100 = 0x60c3d891184c :=
  block_append joined8360_1550 joined9910_1550 rfl rfl rfl

private theorem joined11460_310 : blockEstimate 10225 2160 11460 310 = 0x501d6b982d5 :=
  block_append chunk11460 chunk11615 rfl rfl rfl

private theorem joined11925_310 : blockEstimate 10225 2160 11925 310 = 0x3b53e5a99db :=
  block_append chunk11925 chunk12080 rfl rfl rfl

private theorem joined11770_465 : blockEstimate 10225 2160 11770 465 = 0x5e10a0e9c2d :=
  block_append chunk11770 joined11925_310 rfl rfl rfl

private theorem joined11460_775 : blockEstimate 10225 2160 11460 775 = 0xae2e0c81f02 :=
  block_append joined11460_310 joined11770_465 rfl rfl rfl

private theorem joined12235_310 : blockEstimate 10225 2160 12235 310 = 0x2e9810ff2d3 :=
  block_append chunk12235 chunk12390 rfl rfl rfl

private theorem joined12700_310 : blockEstimate 10225 2160 12700 310 = 0x1da682158c5 :=
  block_append chunk12700 chunk12855 rfl rfl rfl

private theorem joined12545_465 : blockEstimate 10225 2160 12545 465 = 0x307e81d4744 :=
  block_append chunk12545 joined12700_310 rfl rfl rfl

private theorem joined12235_775 : blockEstimate 10225 2160 12235 775 = 0x5f1692d3a17 :=
  block_append joined12235_310 joined12545_465 rfl rfl rfl

private theorem joined11460_1550 : blockEstimate 10225 2160 11460 1550 = 0x10d449f55919 :=
  block_append joined11460_775 joined12235_775 rfl rfl rfl

private theorem joined13010_310 : blockEstimate 10225 2160 13010 310 = 0x1438c652e90 :=
  block_append chunk13010 chunk13165 rfl rfl rfl

private theorem joined13475_310 : blockEstimate 10225 2160 13475 310 = 0x938bd3fb40 :=
  block_append chunk13475 chunk13630 rfl rfl rfl

private theorem joined13320_465 : blockEstimate 10225 2160 13320 465 = 0x104f21830ca :=
  block_append chunk13320 joined13475_310 rfl rfl rfl

private theorem joined13010_775 : blockEstimate 10225 2160 13010 775 = 0x2487e7d5f5a :=
  block_append joined13010_310 joined13320_465 rfl rfl rfl

private theorem joined13785_310 : blockEstimate 10225 2160 13785 310 = 0x42acb95fdc :=
  block_append chunk13785 chunk13940 rfl rfl rfl

private theorem joined14250_295 : blockEstimate 10225 2160 14250 295 = 0x519ffe8bc :=
  block_append chunk14250 chunk14405 rfl rfl rfl

private theorem joined14095_450 : blockEstimate 10225 2160 14095 450 = 0x11e25647ca :=
  block_append chunk14095 joined14250_295 rfl rfl rfl

private theorem joined13785_760 : blockEstimate 10225 2160 13785 760 = 0x548f0fa7a6 :=
  block_append joined13785_310 joined14095_450 rfl rfl rfl

private theorem joined13010_1535 : blockEstimate 10225 2160 13010 1535 = 0x29d0d8d0700 :=
  block_append joined13010_775 joined13785_760 rfl rfl rfl

private theorem joined11460_3085 : blockEstimate 10225 2160 11460 3085 = 0x137157826019 :=
  block_append joined11460_1550 joined13010_1535 rfl rfl rfl

private theorem joined8360_6185 : blockEstimate 10225 2160 8360 6185 = 0x743530137865 :=
  block_append joined8360_3100 joined11460_3085 rfl rfl rfl

private theorem joined2160_12385 : blockEstimate 10225 2160 2160 12385 = 0x10b67db5c846d :=
  block_append joined2160_6200 joined8360_6185 rfl rfl rfl

private theorem momentTerminal : momentEstimate 10225 2160 = 0x10b67db5c846d := joined2160_12385

private theorem terminal_ok (b : Band) : BankOK (terminal b) := by
  cases b with
  | h2524 => exact (pass! 7351,10225,2160,0x29898d6f900000,0x10b67db5c846d; momentTerminal)

private def StageOK (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankOK s.free ∧ BankOK s.moving

private theorem stages_nil : StageOK [] :=
  fun _ hs => (List.not_mem_nil hs).elim

private theorem stages_cons {s : Stage} {ss : List Stage}
    (hf : BankOK s.free) (hm : BankOK s.moving) (ht : StageOK ss) : StageOK (s :: ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩

private theorem stages_ok (b : Band) : StageOK (stages b) := by
  cases b with
  | h2524 =>
    rw [stages]
    refine stages_cons (pass! 73,101,22,0x2e5640000,0x2f6f2a; moment101_22) (pass! 353,491,103,0x12fc4600000,0x5e3742a9; moment491_103) ?_
    refine stages_cons (pass! 60,83,18,0x19fec0000,0x15f0f2; moment83_18) (pass! 405,563,118,0x1c9714c0000,0xa26535f3; moment563_118) ?_
    refine stages_cons (pass! 109,151,33,0x979280000,0xe74c1b; moment151_33) (pass! 445,619,130,0x25f62dc0000,0xed5a05de; moment619_130) ?_
    refine stages_cons (pass! 122,169,38,0xd80c80000,0x170ad54; moment169_38) (pass! 473,659,138,0x2d836e40000,0x12ff82db2; moment659_138) ?_
    refine stages_cons (pass! 131,181,40,0x106e580000,0x1dd3cf8; moment181_40) (pass! 558,775,163,0x4aad7380000,0x246465872; moment775_163) ?_
    refine stages_cons (pass! 140,194,42,0x13bfdc0000,0x26a2eee; moment194_42) (pass! 653,908,191,0x77a65000000,0x447811faa; moment908_191) ?_
    refine stages_cons (pass! 179,248,55,0x29b7600000,0x681fcb3; moment248_55) (pass! 859,1195,253,0x111524d80000,0xcdfbb5b3b; moment1195_253) ?_
    refine stages_cons (pass! 193,267,58,0x3355540000,0x895de88; moment267_58) (pass! 1043,1451,305,0x1e61e4680000,0x1bcaea101e; moment1451_305) ?_
    refine stages_cons (pass! 362,502,114,0x15ae1900000,0x6d68a9c9; moment502_114) (pass! 1225,1703,357,0x310fd3780000,0x349473cb5b; moment1703_357) ?_
    refine stages_cons (pass! 210,291,64,0x42b1ac0000,0xc32b568; moment291_64) (pass! 1318,1839,385,0x3d329b940000,0x4765896c69; moment1839_385) ?_
    refine stages_cons (pass! 295,409,90,0xb7d8100000,0x2f3b1229; moment409_90) (pass! 1516,2105,443,0x5d1c55480000,0x7afe40f467; moment2105_443) ?_
    refine stages_cons (pass! 402,559,122,0x1cd6b900000,0xa2dfd458; moment559_122) (pass! 2123,2950,628,0x101e034e80000,0x1de23726e9e; moment2950_628) ?_
    refine stages_cons (pass! 377,523,114,0x17bd5e40000,0x7cce7b05; moment523_114) (pass! 2155,2994,634,0x10c9546a80000,0x1f9316168cb; moment2994_634) ?_
    refine stages_cons (pass! 500,692,155,0x3841b080000,0x185234383; moment692_155) (pass! 2696,3749,788,0x20b0925680000,0x4d21177bab1; moment3749_788) ?_
    refine stages_cons (pass! 526,731,158,0x3fecfe00000,0x1d7121286; moment731_158) (pass! 2811,3918,819,0x24f5ff3100000,0x5b99db6de2b; moment3918_819) ?_
    refine stages_cons (pass! 425,590,130,0x22423840000,0xcb755a0e; moment590_130) (pass! 2032,2827,594,0xe01986d40000,0x18f3217cfe1; moment2827_594) ?_
    refine stages_cons (pass! 806,1116,251,0xeba01480000,0xa44b9ecd3; moment1116_251) (pass! 4291,5969,1261,0x844328b580000,0x1f12fe9a79ee; moment5969_1261) ?_
    refine stages_cons (pass! 80,111,24,0x3c7300000,0x4451ef; moment111_24) (pass! 380,530,100,0x15dc6d00000,0x7597b06c; moment530_100) ?_
    refine stages_cons (pass! 86,119,26,0x4b3780000,0x5a8245; moment119_26) (pass! 547,764,141,0x3fe66d80000,0x1f060dc24; moment764_141) ?_
    refine stages_cons (pass! 91,126,27,0x57a300000,0x6fafa5; moment126_27) (pass! 1081,1507,264,0x1d679b940000,0x1bfe368baa; moment1507_264) ?_
    refine stages_cons (pass! 97,134,29,0x6a6580000,0x8f605a; moment134_29) (pass! 664,925,200,0x809ed600000,0x4b52e2da2; moment925_200) ?_
    refine stages_cons (pass! 111,153,34,0xa15400000,0xf6b69e; moment153_34) (pass! 494,688,140,0x32b0a2c0000,0x160efc81a; moment688_140) ?_
    refine stages_cons (pass! 129,179,39,0xf95600000,0x1c3d3dd; moment179_39) (pass! 701,976,192,0x8cad28c0000,0x56ac98d52; moment976_192) ?_
    refine stages_cons (pass! 161,223,49,0x1e3a480000,0x43d826b; moment223_49) (pass! 996,1388,254,0x17ce40840000,0x14de8d1a33; moment1388_254) ?_
    refine stages_cons (pass! 168,233,50,0x21bc440000,0x4f48465; moment233_50) (pass! 1122,1566,343,0x271c0f900000,0x26eb47ca19; moment1566_343) ?_
    refine stages_cons (pass! 190,263,59,0x3235480000,0x849a735; moment263_59) (pass! 1811,2518,553,0xa40e21480000,0x1042a2fc6be; moment2518_553) ?_
    refine stages_cons (pass! 249,346,77,0x7002580000,0x187d9080; moment346_77) (pass! 2394,3335,706,0x170d016500000,0x309550b3c97; moment3335_706) ?_
    refine stages_cons (pass! 253,351,80,0x776e8c0000,0x1a683d4b; moment351_80) (pass! 1126,1572,307,0x243638180000,0x241fd7a6b1; moment1572_307) ?_
    refine stages_cons (pass! 266,369,82,0x8812100000,0x1f9950b6; moment369_82) (pass! 1022,1428,311,0x1d7761500000,0x1ace076bd3; moment1428_311) ?_
    refine stages_cons (pass! 316,439,98,0xe4864c0000,0x3f4c6dc0; moment439_98) (pass! 2509,3505,762,0x1b224cb7c0000,0x3c82694be91; moment3505_762) ?_
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
end High55Wide2524BankProof
