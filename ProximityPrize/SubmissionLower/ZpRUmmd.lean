import ProximityPrize.SubmissionLower.Z29Fskc
set_option Elab.async false
set_option autoImplicit true
namespace q8kPhwd
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option quotPrecheck false in
local notation "asr" h "," mm "," qq "," nn "," aa "," dd "," bb "," cc =>
  checked (lo:=3188) (m:=mm) (mid :=qq) (n:=nn) (a :=aa) (b:=bb) (c:=cc)
    h rfl (numeric qq nn dd bb (by decide +kernel) rfl) rfl
private theorem r0:bvj 3188 8=(0x45aa48c58f0:ℕ) :=numeric 3188 8 0x1b85e6d431 0x45aa48c58f0 (by decide +kernel) rfl
private theorem r1 :bvj 3188 16=(0x8a176777ac0:ℕ) :=asr r0,8,3196,8,0x45aa48c58f0,0x1b1ed3e14c,0x446d1eb21d0,0x8a176777ac0
private theorem r2 :bvj 3188 24=(0xcd4ab6820c0:ℕ) :=asr r1,16,3204,8,0x8a176777ac0,0x1ab76d9867,0x43334f0a600,0xcd4ab6820c0
theorem total9:bvj 3188 32=(0x10f478c21e20:ℕ) :=asr r2,24,3212,8,0xcd4ab6820c0,0x1a4fbb992b,0x41fcd59fd60,0x10f478c21e20
end q8kPhwd
