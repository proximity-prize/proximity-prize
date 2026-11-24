import ProximityPrize.SubmissionLower.Z29Fskc
set_option Elab.async false
set_option autoImplicit true
namespace q8kPhwd
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option quotPrecheck false in
local notation "asr" h "," mm "," qq "," nn "," aa "," dd "," bb "," cc =>
  checked (lo:=3060) (m:=mm) (mid :=qq) (n:=nn) (a :=aa) (b:=bb) (c:=cc)
    h rfl (numeric qq nn dd bb (by decide +kernel) rfl) rfl
private theorem r0:bvj 3060 8=(0x5b4c64cdb60:ℕ) :=numeric 3060 8 0x21ad53f84b 0x5b4c64cdb60 (by decide +kernel) rfl
private theorem r1 :bvj 3060 16=(0xb524a197908:ℕ) :=asr r0,8,3068,8,0x5b4c64cdb60,0x21505d8cae,0x59d83cc9da8,0xb524a197908
private theorem r2 :bvj 3060 24=(0x10d8c36c5cd8:ℕ) :=asr r1,16,3076,8,0xb524a197908,0x20f27b336c,0x5867952e3d0,0x10d8c36c5cd8
theorem total5:bvj 3060 32=(0x16486b276420:ℕ) :=asr r2,24,3084,8,0x10d8c36c5cd8,0x2093c1ceea,0x56fa7bb0748,0x16486b276420
end q8kPhwd
