import ProximityPrize.SubmissionLower.Z29Fskc
set_option Elab.async false
set_option autoImplicit true
namespace q8kPhwd
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option quotPrecheck false in
local notation "asr" h "," mm "," qq "," nn "," aa "," dd "," bb "," cc =>
  checked (lo:=3252) (m:=mm) (mid :=qq) (n:=nn) (a :=aa) (b:=bb) (c:=cc)
    h rfl (numeric qq nn dd bb (by decide +kernel) (by decide +kernel)) rfl
private theorem r0:bvj 3252 8=(0x3c04080c690:ℕ) :=numeric 3252 8 0x183490716d 0x3c04080c690 (by decide +kernel) (by decide +kernel)
private theorem r1 :bvj 3252 16=(0x76e3c641400:ℕ) :=asr r0,8,3260,8,0x3c04080c690,0x17cab4e801,0x3adfbe34d70,0x76e3c641400
private theorem r2 :bvj 3252 24=(0xb0a2c093928:ℕ) :=asr r1,16,3268,8,0x76e3c641400,0x1760f40425,0x39befa52528,0xb0a2c093928
theorem total11 :bvj 3252 32=(0xe9444beeda8:ℕ) :=asr r2,24,3276,8,0xb0a2c093928,0x16f736d377,0x38a18b5b480,0xe9444beeda8
end q8kPhwd
