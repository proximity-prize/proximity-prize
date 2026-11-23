import ProximityPrize.SubmissionLower.Z29Fskc
set_option Elab.async false
set_option autoImplicit true
namespace q8kPhwd
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
local notation "asr" h "," mm "," qq "," nn "," aa "," dd "," bb "," cc =>
  checked (lo:=3156) (m:=mm) (mid :=qq) (n:=nn) (a :=aa) (b:=bb) (c:=cc)
    h rfl (numeric qq nn dd bb rfl rfl) rfl
private theorem r0:bvj 3156 8=(0x4ac0cadfde8:ℕ) :=numeric 3156 8 0x1d1e548366 0x4ac0cadfde8 rfl rfl
private theorem r1 :bvj 3156 16=(0x9436e37e300:ℕ) :=asr r0,8,3164,8,0x4ac0cadfde8,0x1cb8e45ba8,0x4976189e518,0x9436e37e300
private theorem r2 :bvj 3156 24=(0xdc65b1aa610 :ℕ) :=asr r1,16,3172,8,0x9436e37e300,0x1c52ff5064,0x482ece2c310,0xdc65b1aa610
theorem total8:bvj 3156 32=(0x12350840de10 :ℕ) :=asr r2,24,3180,8,0xdc65b1aa610,0x1bec9f5c47,0x46ead263800,0x12350840de10
end q8kPhwd
