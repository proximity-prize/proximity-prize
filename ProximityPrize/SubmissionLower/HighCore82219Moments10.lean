import ProximityPrize.SubmissionLower.HighCore82219Moments9

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)

set_option maxHeartbeats 14000000

private theorem p3918_819_819 : blockEstimate 3918 819 819 215 = 0x1782a8d1a := by decide +kernel
private theorem p3918_819_1034 : blockEstimate 3918 819 1034 215 = 0x9b41c8aaa := by decide +kernel
private theorem p3918_819_1249 : blockEstimate 3918 819 1249 215 = 0x18c2f7359d := by decide +kernel
private theorem p3918_819_1464 : blockEstimate 3918 819 1464 215 = 0x2d248c514e := by decide +kernel
private theorem p3918_819_1679 : blockEstimate 3918 819 1679 215 = 0x437e99f7a2 := by decide +kernel
private theorem p3918_819_1894 : blockEstimate 3918 819 1894 215 = 0x56b6316250 := by decide +kernel
private theorem p3918_819_2109 : blockEstimate 3918 819 2109 215 = 0x66224aca26 := by decide +kernel
private theorem p3918_819_2324 : blockEstimate 3918 819 2324 215 = 0x71c2e62f24 := by decide +kernel
private theorem p3918_819_2539 : blockEstimate 3918 819 2539 215 = 0x799803914a := by decide +kernel
private theorem p3918_819_2754 : blockEstimate 3918 819 2754 215 = 0x7da1a2f098 := by decide +kernel
private theorem p3918_819_2969 : blockEstimate 3918 819 2969 215 = 0x7ddfc44d0e := by decide +kernel
private theorem p3918_819_3184 : blockEstimate 3918 819 3184 215 = 0x7a5267a6ac := by decide +kernel
private theorem p3918_819_3399 : blockEstimate 3918 819 3399 215 = 0x72f98cfd72 := by decide +kernel
private theorem p3918_819_3614 : blockEstimate 3918 819 3614 215 = 0x67d5345160 := by decide +kernel
private theorem p3918_819_3829 : blockEstimate 3918 819 3829 215 = 0x58fdb2d86c := by decide +kernel
private theorem p3918_819_4044 : blockEstimate 3918 819 4044 215 = 0x481e83b956 := by decide +kernel
private theorem p3918_819_4259 : blockEstimate 3918 819 4259 215 = 0x37356a59c2 := by decide +kernel
private theorem p3918_819_4474 : blockEstimate 3918 819 4474 215 = 0x2740ae8f5a := by decide +kernel
private theorem p3918_819_4689 : blockEstimate 3918 819 4689 215 = 0x19128db871 := by decide +kernel
private theorem p3918_819_4904 : blockEstimate 3918 819 4904 215 = 0xd7d27eecc := by decide +kernel
private theorem p3918_819_5119 : blockEstimate 3918 819 5119 215 = 0x53fd01893 := by decide +kernel
private theorem p3918_819_5334 : blockEstimate 3918 819 5334 215 = 0xd383f06e := by decide +kernel
private theorem p3918_819_5549 : blockEstimate 3918 819 5549 7 = 195766 := by decide +kernel

private theorem s3918_819_819_430 : blockEstimate 3918 819 819 430 = 0xb2c4717c4 :=
  block_append p3918_819_819 p3918_819_1034 rfl rfl rfl

private theorem s3918_819_1464_430 : blockEstimate 3918 819 1464 430 = 0x70a32648f0 :=
  block_append p3918_819_1464 p3918_819_1679 rfl rfl rfl

private theorem s3918_819_1249_645 : blockEstimate 3918 819 1249 645 = 0x89661d7e8d :=
  block_append p3918_819_1249 s3918_819_1464_430 rfl rfl rfl

private theorem s3918_819_819_1075 : blockEstimate 3918 819 819 1075 = 0x9492649651 :=
  block_append s3918_819_819_430 s3918_819_1249_645 rfl rfl rfl

private theorem s3918_819_2109_430 : blockEstimate 3918 819 2109 430 = 0xd7e530f94a :=
  block_append p3918_819_2109 p3918_819_2324 rfl rfl rfl

private theorem s3918_819_1894_645 : blockEstimate 3918 819 1894 645 = 0x12e9b625b9a :=
  block_append p3918_819_1894 s3918_819_2109_430 rfl rfl rfl

private theorem s3918_819_2754_430 : blockEstimate 3918 819 2754 430 = 0xfb81673da6 :=
  block_append p3918_819_2754 p3918_819_2969 rfl rfl rfl

private theorem s3918_819_2539_645 : blockEstimate 3918 819 2539 645 = 0x175196acef0 :=
  block_append p3918_819_2539 s3918_819_2754_430 rfl rfl rfl

private theorem s3918_819_1894_1290 : blockEstimate 3918 819 1894 1290 = 0x2a3b4cd2a8a :=
  block_append s3918_819_1894_645 s3918_819_2539_645 rfl rfl rfl

private theorem s3918_819_819_2365 : blockEstimate 3918 819 819 2365 = 0x3384731c0db :=
  block_append s3918_819_819_1075 s3918_819_1894_1290 rfl rfl rfl

private theorem s3918_819_3399_430 : blockEstimate 3918 819 3399 430 = 0xdacec14ed2 :=
  block_append p3918_819_3399 p3918_819_3614 rfl rfl rfl

private theorem s3918_819_3184_645 : blockEstimate 3918 819 3184 645 = 0x1552128f57e :=
  block_append p3918_819_3184 s3918_819_3399_430 rfl rfl rfl

private theorem s3918_819_4044_430 : blockEstimate 3918 819 4044 430 = 0x7f53ee1318 :=
  block_append p3918_819_4044 p3918_819_4259 rfl rfl rfl

private theorem s3918_819_3829_645 : blockEstimate 3918 819 3829 645 = 0xd851a0eb84 :=
  block_append p3918_819_3829 s3918_819_4044_430 rfl rfl rfl

private theorem s3918_819_3184_1290 : blockEstimate 3918 819 3184 1290 = 0x22d72c9e102 :=
  block_append s3918_819_3184_645 s3918_819_3829_645 rfl rfl rfl

private theorem s3918_819_4689_430 : blockEstimate 3918 819 4689 430 = 0x268fb5a73d :=
  block_append p3918_819_4689 p3918_819_4904 rfl rfl rfl

private theorem s3918_819_4474_645 : blockEstimate 3918 819 4474 645 = 0x4dd0643697 :=
  block_append p3918_819_4474 s3918_819_4689_430 rfl rfl rfl

private theorem s3918_819_5334_222 : blockEstimate 3918 819 5334 222 = 0xd386ed24 :=
  block_append (B := 3918) (J := 819) (start := 5334) (next := 5549)
    (a := 215) (b := 7) (n := 222) (x := 0xd383f06e) (y := 195766) (z := 0xd386ed24)
    p3918_819_5334 p3918_819_5549 rfl rfl rfl

private theorem s3918_819_5119_437 : blockEstimate 3918 819 5119 437 = 0x6135705b7 :=
  block_append p3918_819_5119 s3918_819_5334_222 rfl rfl rfl

private theorem s3918_819_4474_1082 : blockEstimate 3918 819 4474 1082 = 0x53e3bb3c4e :=
  block_append s3918_819_4474_645 s3918_819_5119_437 rfl rfl rfl

private theorem s3918_819_3184_2372 : blockEstimate 3918 819 3184 2372 = 0x28156851d50 :=
  block_append s3918_819_3184_1290 s3918_819_4474_1082 rfl rfl rfl

private theorem s3918_819_819_4737 : blockEstimate 3918 819 819 4737 = 0x5b99db6de2b :=
  block_append s3918_819_819_2365 s3918_819_3184_2372 rfl rfl rfl

theorem moment3918_819 : momentEstimate 3918 819 = 0x5b99db6de2b := s3918_819_819_4737

end HighCore82219BankProof
