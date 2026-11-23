import ProximityPrize.SubmissionLower.Z29Fskc
set_option Elab.async false
set_option autoImplicit true
namespace q8kPhwd
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
local notation "asr" h "," mm "," qq "," nn "," aa "," dd "," bb "," cc =>
  checked (lo:=3028) (m:=mm) (mid :=qq) (n:=nn) (a :=aa) (b:=bb) (c:=cc)
    h rfl (numeric qq nn dd bb rfl rfl) rfl
private theorem r0:bvj 3028 8=(0x613f5a4d498:ℕ) :=numeric 3028 8 0x231694221f 0x613f5a4d498 rfl rfl
private theorem r1 :bvj 3028 16=(0xc0fe031cc18:ℕ) :=asr r0,8,3036,8,0x613f5a4d498,0x22bebf4f17,0x5fbea8cf780,0xc0fe031cc18
private theorem r2 :bvj 3028 24=(0x11f3d82bf6a8:ℕ) :=asr r1,16,3044,8,0xc0fe031cc18,0x22647eaeed,0x5e3f7fa2a90,0x11f3d82bf6a8
theorem total4 :bvj 3028 32=(0x17c0199d57b0:ℕ) :=asr r2,24,3052,8,0x11f3d82bf6a8,0x2209593519,0x5cc41716108,0x17c0199d57b0
end q8kPhwd
