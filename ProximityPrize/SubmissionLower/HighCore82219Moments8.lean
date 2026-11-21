import ProximityPrize.SubmissionLower.HighCore82219Moments7

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)

set_option maxHeartbeats 14000000

private theorem p3505_762_762 : blockEstimate 3505 762 762 215 = 0x14ed20a2e := by decide +kernel
private theorem p3505_762_977 : blockEstimate 3505 762 977 215 = 0x894fa47c6 := by decide +kernel
private theorem p3505_762_1192 : blockEstimate 3505 762 1192 215 = 0x15b964c0b6 := by decide +kernel
private theorem p3505_762_1407 : blockEstimate 3505 762 1407 215 = 0x272506988d := by decide +kernel
private theorem p3505_762_1622 : blockEstimate 3505 762 1622 215 = 0x38c16d241a := by decide +kernel
private theorem p3505_762_1837 : blockEstimate 3505 762 1837 215 = 0x4702e8a7b2 := by decide +kernel
private theorem p3505_762_2052 : blockEstimate 3505 762 2052 215 = 0x51bc6dfb10 := by decide +kernel
private theorem p3505_762_2267 : blockEstimate 3505 762 2267 215 = 0x58edfd1e34 := by decide +kernel
private theorem p3505_762_2482 : blockEstimate 3505 762 2482 215 = 0x5c9796111e := by decide +kernel
private theorem p3505_762_2697 : blockEstimate 3505 762 2697 215 = 0x5cb938d3ce := by decide +kernel
private theorem p3505_762_2912 : blockEstimate 3505 762 2912 215 = 0x5952e56644 := by decide +kernel
private theorem p3505_762_3127 : blockEstimate 3505 762 3127 215 = 0x52649bc880 := by decide +kernel
private theorem p3505_762_3342 : blockEstimate 3505 762 3342 215 = 0x47efd2ee0a := by decide +kernel
private theorem p3505_762_3557 : blockEstimate 3505 762 3557 215 = 0x3ac6eb1efe := by decide +kernel
private theorem p3505_762_3772 : blockEstimate 3505 762 3772 215 = 0x2d04d43439 := by decide +kernel
private theorem p3505_762_3987 : blockEstimate 3505 762 3987 215 = 0x1fcce2624f := by decide +kernel
private theorem p3505_762_4202 : blockEstimate 3505 762 4202 215 = 0x13f913d0ee := by decide +kernel
private theorem p3505_762_4417 : blockEstimate 3505 762 4417 215 = 0xa58568c92 := by decide +kernel
private theorem p3505_762_4632 : blockEstimate 3505 762 4632 215 = 0x3aa755dd5 := by decide +kernel
private theorem p3505_762_4847 : blockEstimate 3505 762 4847 182 = 0x68f7bbb5 := by decide +kernel

private theorem s3505_762_762_430 : blockEstimate 3505 762 762 430 = 0x9e3cc51f4 :=
  block_append p3505_762_762 p3505_762_977 rfl rfl rfl

private theorem s3505_762_1407_430 : blockEstimate 3505 762 1407 430 = 0x5fe673bca7 :=
  block_append p3505_762_1407 p3505_762_1622 rfl rfl rfl

private theorem s3505_762_1192_645 : blockEstimate 3505 762 1192 645 = 0x759fd87d5d :=
  block_append p3505_762_1192 s3505_762_1407_430 rfl rfl rfl

private theorem s3505_762_762_1075 : blockEstimate 3505 762 762 1075 = 0x7f83a4cf51 :=
  block_append s3505_762_762_430 s3505_762_1192_645 rfl rfl rfl

private theorem s3505_762_1837_430 : blockEstimate 3505 762 1837 430 = 0x98bf56a2c2 :=
  block_append p3505_762_1837 p3505_762_2052 rfl rfl rfl

private theorem s3505_762_2482_430 : blockEstimate 3505 762 2482 430 = 0xb950cee4ec :=
  block_append p3505_762_2482 p3505_762_2697 rfl rfl rfl

private theorem s3505_762_2267_645 : blockEstimate 3505 762 2267 645 = 0x1123ecc0320 :=
  block_append p3505_762_2267 s3505_762_2482_430 rfl rfl rfl

private theorem s3505_762_1837_1075 : blockEstimate 3505 762 1837 1075 = 0x1aafe22a5e2 :=
  block_append s3505_762_1837_430 s3505_762_2267_645 rfl rfl rfl

private theorem s3505_762_762_2150 : blockEstimate 3505 762 762 2150 = 0x22a81c77533 :=
  block_append s3505_762_762_1075 s3505_762_1837_1075 rfl rfl rfl

private theorem s3505_762_2912_430 : blockEstimate 3505 762 2912 430 = 0xabb7812ec4 :=
  block_append p3505_762_2912 p3505_762_3127 rfl rfl rfl

private theorem s3505_762_3557_430 : blockEstimate 3505 762 3557 430 = 0x67cbbf5337 :=
  block_append p3505_762_3557 p3505_762_3772 rfl rfl rfl

private theorem s3505_762_3342_645 : blockEstimate 3505 762 3342 645 = 0xafbb924141 :=
  block_append p3505_762_3342 s3505_762_3557_430 rfl rfl rfl

private theorem s3505_762_2912_1075 : blockEstimate 3505 762 2912 1075 = 0x15b73137005 :=
  block_append s3505_762_2912_430 s3505_762_3342_645 rfl rfl rfl

private theorem s3505_762_3987_430 : blockEstimate 3505 762 3987 430 = 0x33c5f6333d :=
  block_append p3505_762_3987 p3505_762_4202 rfl rfl rfl

private theorem s3505_762_4632_397 : blockEstimate 3505 762 4632 397 = 0x4136d198a :=
  block_append p3505_762_4632 p3505_762_4847 rfl rfl rfl

private theorem s3505_762_4417_612 : blockEstimate 3505 762 4417 612 = 0xe6bc3a61c :=
  block_append p3505_762_4417 s3505_762_4632_397 rfl rfl rfl

private theorem s3505_762_3987_1042 : blockEstimate 3505 762 3987 1042 = 0x4231b9d959 :=
  block_append s3505_762_3987_430 s3505_762_4417_612 rfl rfl rfl

private theorem s3505_762_2912_2117 : blockEstimate 3505 762 2912 2117 = 0x19da4cd495e :=
  block_append s3505_762_2912_1075 s3505_762_3987_1042 rfl rfl rfl

private theorem s3505_762_762_4267 : blockEstimate 3505 762 762 4267 = 0x3c82694be91 :=
  block_append s3505_762_762_2150 s3505_762_2912_2117 rfl rfl rfl

theorem moment3505_762 : momentEstimate 3505 762 = 0x3c82694be91 := s3505_762_762_4267

end HighCore82219BankProof
