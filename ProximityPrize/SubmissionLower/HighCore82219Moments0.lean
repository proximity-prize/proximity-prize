import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)

set_option maxHeartbeats 14000000

private theorem p83_18_18 : blockEstimate 83 18 18 101 = 0x15f0f2 := by decide +kernel



theorem moment83_18 : momentEstimate 83 18 = 0x15f0f2 := p83_18_18

private theorem p101_22_22 : blockEstimate 101 22 22 123 = 0x2f6f2a := by decide +kernel



theorem moment101_22 : momentEstimate 101 22 = 0x2f6f2a := p101_22_22

private theorem p111_24_24 : blockEstimate 111 24 24 135 = 0x4451ef := by decide +kernel



theorem moment111_24 : momentEstimate 111 24 = 0x4451ef := p111_24_24

private theorem p119_26_26 : blockEstimate 119 26 26 145 = 0x5a8245 := by decide +kernel



theorem moment119_26 : momentEstimate 119 26 = 0x5a8245 := p119_26_26

private theorem p126_27_27 : blockEstimate 126 27 27 153 = 0x6fafa5 := by decide +kernel



theorem moment126_27 : momentEstimate 126 27 = 0x6fafa5 := p126_27_27

private theorem p134_29_29 : blockEstimate 134 29 29 163 = 0x8f605a := by decide +kernel



theorem moment134_29 : momentEstimate 134 29 = 0x8f605a := p134_29_29

private theorem p151_33_33 : blockEstimate 151 33 33 184 = 0xe74c1b := by decide +kernel



theorem moment151_33 : momentEstimate 151 33 = 0xe74c1b := p151_33_33

private theorem p153_34_34 : blockEstimate 153 34 34 187 = 0xf6b69e := by decide +kernel



theorem moment153_34 : momentEstimate 153 34 = 0xf6b69e := p153_34_34

private theorem p169_38_38 : blockEstimate 169 38 38 207 = 0x170ad54 := by decide +kernel



theorem moment169_38 : momentEstimate 169 38 = 0x170ad54 := p169_38_38

private theorem p179_39_39 : blockEstimate 179 39 39 215 = 0x1c3cefe := by decide +kernel
private theorem p179_39_254 : blockEstimate 179 39 254 3 = 1247 := by decide +kernel

private theorem s179_39_39_218 : blockEstimate 179 39 39 218 = 0x1c3d3dd :=
  block_append (B := 179) (J := 39) (start := 39) (next := 254)
    (a := 215) (b := 3) (n := 218) (x := 0x1c3cefe) (y := 1247) (z := 0x1c3d3dd)
    p179_39_39 p179_39_254 rfl rfl rfl

theorem moment179_39 : momentEstimate 179 39 = 0x1c3d3dd := s179_39_39_218

private theorem p181_40_40 : blockEstimate 181 40 40 215 = 0x1dd2539 := by decide +kernel
private theorem p181_40_255 : blockEstimate 181 40 255 6 = 6079 := by decide +kernel

private theorem s181_40_40_221 : blockEstimate 181 40 40 221 = 0x1dd3cf8 :=
  block_append (B := 181) (J := 40) (start := 40) (next := 255)
    (a := 215) (b := 6) (n := 221) (x := 0x1dd2539) (y := 6079) (z := 0x1dd3cf8)
    p181_40_40 p181_40_255 rfl rfl rfl

theorem moment181_40 : momentEstimate 181 40 = 0x1dd3cf8 := s181_40_40_221

private theorem p194_42_42 : blockEstimate 194 42 42 215 = 0x267840b := by decide +kernel
private theorem p194_42_257 : blockEstimate 194 42 257 21 = 174819 := by decide +kernel

private theorem s194_42_42_236 : blockEstimate 194 42 42 236 = 0x26a2eee :=
  block_append (B := 194) (J := 42) (start := 42) (next := 257)
    (a := 215) (b := 21) (n := 236) (x := 0x267840b) (y := 174819) (z := 0x26a2eee)
    p194_42_42 p194_42_257 rfl rfl rfl

theorem moment194_42 : momentEstimate 194 42 = 0x26a2eee := s194_42_42_236

private theorem p223_49_49 : blockEstimate 223 49 49 215 = 0x40b7288 := by decide +kernel
private theorem p223_49_264 : blockEstimate 223 49 264 57 = 0x320fe3 := by decide +kernel

private theorem s223_49_49_272 : blockEstimate 223 49 49 272 = 0x43d826b :=
  block_append p223_49_49 p223_49_264 rfl rfl rfl

theorem moment223_49 : momentEstimate 223 49 = 0x43d826b := s223_49_49_272

private theorem p233_50_50 : blockEstimate 233 50 50 215 = 0x49ecaa2 := by decide +kernel
private theorem p233_50_265 : blockEstimate 233 50 265 68 = 0x55b9c3 := by decide +kernel

private theorem s233_50_50_283 : blockEstimate 233 50 50 283 = 0x4f48465 :=
  block_append p233_50_50 p233_50_265 rfl rfl rfl

theorem moment233_50 : momentEstimate 233 50 = 0x4f48465 := s233_50_50_283

private theorem p248_55_55 : blockEstimate 248 55 55 215 = 0x5c739b3 := by decide +kernel
private theorem p248_55_270 : blockEstimate 248 55 270 88 = 0xbac300 := by decide +kernel

private theorem s248_55_55_303 : blockEstimate 248 55 55 303 = 0x681fcb3 :=
  block_append p248_55_55 p248_55_270 rfl rfl rfl

theorem moment248_55 : momentEstimate 248 55 = 0x681fcb3 := s248_55_55_303

private theorem p263_59_59 : blockEstimate 263 59 59 215 = 0x6f6726d := by decide +kernel
private theorem p263_59_274 : blockEstimate 263 59 274 107 = 0x15334c8 := by decide +kernel

private theorem s263_59_59_322 : blockEstimate 263 59 59 322 = 0x849a735 :=
  block_append p263_59_59 p263_59_274 rfl rfl rfl

theorem moment263_59 : momentEstimate 263 59 = 0x849a735 := s263_59_59_322

private theorem p267_58_58 : blockEstimate 267 58 58 215 = 0x72289d3 := by decide +kernel
private theorem p267_58_273 : blockEstimate 267 58 273 110 = 0x17354b5 := by decide +kernel

private theorem s267_58_58_325 : blockEstimate 267 58 58 325 = 0x895de88 :=
  block_append p267_58_58 p267_58_273 rfl rfl rfl

theorem moment267_58 : momentEstimate 267 58 = 0x895de88 := s267_58_58_325

private theorem p291_64_64 : blockEstimate 291 64 64 215 = 0x9282f7c := by decide +kernel
private theorem p291_64_279 : blockEstimate 291 64 279 140 = 0x30a85ec := by decide +kernel

private theorem s291_64_64_355 : blockEstimate 291 64 64 355 = 0xc32b568 :=
  block_append p291_64_64 p291_64_279 rfl rfl rfl

theorem moment291_64 : momentEstimate 291 64 = 0xc32b568 := s291_64_64_355

private theorem p346_77_77 : blockEstimate 346 77 77 215 = 0xe3ca6ec := by decide +kernel
private theorem p346_77_292 : blockEstimate 346 77 292 208 = 0xa40e994 := by decide +kernel

private theorem s346_77_77_423 : blockEstimate 346 77 77 423 = 0x187d9080 :=
  block_append p346_77_77 p346_77_292 rfl rfl rfl

theorem moment346_77 : momentEstimate 346 77 = 0x187d9080 := s346_77_77_423

private theorem p351_80_80 : blockEstimate 351 80 80 215 = 0xee8ff18 := by decide +kernel
private theorem p351_80_295 : blockEstimate 351 80 295 215 = 0xb7f3cd4 := by decide +kernel
private theorem p351_80_510 : blockEstimate 351 80 510 1 = 351 := by decide +kernel

private theorem s351_80_295_216 : blockEstimate 351 80 295 216 = 0xb7f3e33 :=
  block_append (B := 351) (J := 80) (start := 295) (next := 510)
    (a := 215) (b := 1) (n := 216) (x := 0xb7f3cd4) (y := 351) (z := 0xb7f3e33)
    p351_80_295 p351_80_510 rfl rfl rfl

private theorem s351_80_80_431 : blockEstimate 351 80 80 431 = 0x1a683d4b :=
  block_append p351_80_80 s351_80_295_216 rfl rfl rfl

theorem moment351_80 : momentEstimate 351 80 = 0x1a683d4b := s351_80_80_431

private theorem p369_82_82 : blockEstimate 369 82 82 215 = 0x107c4163 := by decide +kernel
private theorem p369_82_297 : blockEstimate 369 82 297 215 = 0xf17ddc2 := by decide +kernel
private theorem p369_82_512 : blockEstimate 369 82 512 21 = 340369 := by decide +kernel

private theorem s369_82_297_236 : blockEstimate 369 82 297 236 = 0xf1d0f53 :=
  block_append (B := 369) (J := 82) (start := 297) (next := 512)
    (a := 215) (b := 21) (n := 236) (x := 0xf17ddc2) (y := 340369) (z := 0xf1d0f53)
    p369_82_297 p369_82_512 rfl rfl rfl

private theorem s369_82_82_451 : blockEstimate 369 82 82 451 = 0x1f9950b6 :=
  block_append p369_82_82 s369_82_297_236 rfl rfl rfl

theorem moment369_82 : momentEstimate 369 82 = 0x1f9950b6 := s369_82_82_451

private theorem p409_90_90 : blockEstimate 409 90 90 215 = 0x147f67f5 := by decide +kernel
private theorem p409_90_305 : blockEstimate 409 90 305 215 = 0x1a139b0d := by decide +kernel
private theorem p409_90_520 : blockEstimate 409 90 520 69 = 0xa80f27 := by decide +kernel

private theorem s409_90_305_284 : blockEstimate 409 90 305 284 = 0x1abbaa34 :=
  block_append p409_90_305 p409_90_520 rfl rfl rfl

private theorem s409_90_90_499 : blockEstimate 409 90 90 499 = 0x2f3b1229 :=
  block_append p409_90_90 s409_90_305_284 rfl rfl rfl

theorem moment409_90 : momentEstimate 409 90 = 0x2f3b1229 := s409_90_90_499

private theorem p439_98_98 : blockEstimate 439 98 98 215 = 0x17d80547 := by decide +kernel
private theorem p439_98_313 : blockEstimate 439 98 313 215 = 0x24fc1588 := by decide +kernel
private theorem p439_98_528 : blockEstimate 439 98 528 107 = 0x27852f1 := by decide +kernel

private theorem s439_98_313_322 : blockEstimate 439 98 313 322 = 0x27746879 :=
  block_append p439_98_313 p439_98_528 rfl rfl rfl

private theorem s439_98_98_537 : blockEstimate 439 98 98 537 = 0x3f4c6dc0 :=
  block_append p439_98_98 s439_98_313_322 rfl rfl rfl

theorem moment439_98 : momentEstimate 439 98 = 0x3f4c6dc0 := s439_98_98_537

private theorem p491_103_103 : blockEstimate 491 103 103 215 = 0x1cd64e3a := by decide +kernel
private theorem p491_103_318 : blockEstimate 491 103 318 215 = 0x3824db56 := by decide +kernel
private theorem p491_103_533 : blockEstimate 491 103 533 164 = 0x93c1919 := by decide +kernel

private theorem s491_103_318_379 : blockEstimate 491 103 318 379 = 0x4160f46f :=
  block_append p491_103_318 p491_103_533 rfl rfl rfl

private theorem s491_103_103_594 : blockEstimate 491 103 103 594 = 0x5e3742a9 :=
  block_append p491_103_103 s491_103_318_379 rfl rfl rfl

theorem moment491_103 : momentEstimate 491 103 = 0x5e3742a9 := s491_103_103_594

private theorem p502_114_114 : blockEstimate 502 114 114 215 = 0x1efcb313 := by decide +kernel
private theorem p502_114_329 : blockEstimate 502 114 329 215 = 0x4101d085 := by decide +kernel
private theorem p502_114_544 : blockEstimate 502 114 544 186 = 0xd6a2631 := by decide +kernel

private theorem s502_114_329_401 : blockEstimate 502 114 329 401 = 0x4e6bf6b6 :=
  block_append p502_114_329 p502_114_544 rfl rfl rfl

private theorem s502_114_114_616 : blockEstimate 502 114 114 616 = 0x6d68a9c9 :=
  block_append p502_114_114 s502_114_329_401 rfl rfl rfl

theorem moment502_114 : momentEstimate 502 114 = 0x6d68a9c9 := s502_114_114_616

private theorem p523_114_114 : blockEstimate 523 114 114 215 = 0x20dfe05b := by decide +kernel
private theorem p523_114_329 : blockEstimate 523 114 329 215 = 0x49220e59 := by decide +kernel
private theorem p523_114_544 : blockEstimate 523 114 544 207 = 0x12cc8c51 := by decide +kernel

private theorem s523_114_329_422 : blockEstimate 523 114 329 422 = 0x5bee9aaa :=
  block_append p523_114_329 p523_114_544 rfl rfl rfl

private theorem s523_114_114_637 : blockEstimate 523 114 114 637 = 0x7cce7b05 :=
  block_append p523_114_114 s523_114_329_422 rfl rfl rfl

theorem moment523_114 : momentEstimate 523 114 = 0x7cce7b05 := s523_114_114_637

end HighCore82219BankProof
