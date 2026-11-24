import ProximityPrize.SubmissionLower.Z29Fskc
set_option Elab.async false
set_option autoImplicit true
namespace q8kPhwd
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option quotPrecheck false in
local notation "asr" h "," mm "," qq "," nn "," aa "," dd "," bb "," cc =>
  checked (lo:=3092) (m:=mm) (mid :=qq) (n:=nn) (a :=aa) (b:=bb) (c:=cc)
    h rfl (numeric qq nn dd bb (by decide +kernel) rfl) rfl
private theorem r0:bvj 3092 8=(0x5590e36a8d8:ℕ) :=numeric 3092 8 0x2034346f30 0x5590e36a8d8 (by decide +kernel) rfl
private theorem r1 :bvj 3092 16=(0xa9bbb33ed98:ℕ) :=asr r0,8,3100,8,0x5590e36a8d8,0x1fd3e0f816,0x542acfd44c0,0xa9bbb33ed98
private theorem r2 :bvj 3092 24=(0xfc83fdbb488:ℕ) :=asr r1,16,3108,8,0xa9bbb33ed98,0x1f72d94771,0x52c84a7c6f0,0xfc83fdbb488
theorem total6:bvj 3092 32=(0x14ded3095430:ℕ) :=asr r2,24,3116,8,0xfc83fdbb488,0x1f111315ee,0x516932d9fa8,0x14ded3095430
end q8kPhwd
