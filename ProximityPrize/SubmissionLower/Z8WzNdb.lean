import ProximityPrize.SubmissionLower.Z29Fskc
set_option Elab.async false
set_option autoImplicit true
namespace q8kPhwd
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option quotPrecheck false in
local notation "asr" h "," mm "," qq "," nn "," aa "," dd "," bb "," cc =>
  checked (lo:=3124) (m:=mm) (mid :=qq) (n:=nn) (a :=aa) (b:=bb) (c:=cc)
    h rfl (numeric qq nn dd bb (by decide +kernel) rfl) rfl
private theorem r0:bvj 3124 8=(0x500da35cea0:ℕ) :=numeric 3124 8 0x1eaeab578a 0x500da35cea0 (by decide +kernel) rfl
private theorem r1 :bvj 3124 16=(0x9ec30c61c30:ℕ) :=asr r0,8,3132,8,0x500da35cea0,0x1e4b8b4aad,0x4eb56904d90,0x9ec30c61c30
private theorem r2 :bvj 3124 24=(0xec2375ac9b8:ℕ) :=asr r1,16,3140,8,0x9ec30c61c30,0x1de7ac6962,0x4d60694ad88,0xec2375ac9b8
theorem total7:bvj 3124 32=(0x13832585d3f0:ℕ) :=asr r2,24,3148,8,0xec2375ac9b8,0x1d8343737b,0x4c0ee2b0a38,0x13832585d3f0
end q8kPhwd
