import ProximityPrize.SubmissionLower.Z29Fskc
set_option Elab.async false
set_option autoImplicit true
namespace q8kPhwd
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option quotPrecheck false in
local notation "asr" h "," mm "," qq "," nn "," aa "," dd "," bb "," cc =>
  checked (lo:=3220) (m:=mm) (mid :=qq) (n:=nn) (a :=aa) (b:=bb) (c:=cc)
    h rfl (numeric qq nn dd bb (by decide +kernel) rfl) rfl
private theorem r0:bvj 3220 8=(0x40b74397258:ℕ) :=numeric 3220 8 0x19db7e5007 0x40b74397258 (by decide +kernel) rfl
private theorem r1 :bvj 3220 16=(0x803c9047380:ℕ) :=asr r0,8,3228,8,0x40b74397258,0x1971e27b7e,0x3f854cb0128,0x803c9047380
private theorem r2 :bvj 3220 24=(0xbe9350e20f8:ℕ) :=asr r1,16,3236,8,0x803c9047380,0x190827650c,0x3e56c09ad78,0xbe9350e20f8
theorem total10 :bvj 3220 32=(0xfbbefad4c00:ℕ) :=asr r2,24,3244,8,0xbe9350e20f8,0x189e5e32d9,0x3d2ba9f2b08,0xfbbefad4c00
end q8kPhwd
