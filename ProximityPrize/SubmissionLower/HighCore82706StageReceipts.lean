import ProximityPrize.SubmissionLower.HighCore82706Stages

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82706Stages

open HighCore82706
open K1_14 (Shape)
open P3 (p)

private def Checks (lo : ℕ) (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankCertificate lo s.reserve 0 s.free ∧ BankCertificate lo s.reserve 1 s.moving
private theorem nil {lo : ℕ} : Checks lo [] := fun _ hs => (List.not_mem_nil hs).elim
private theorem cons {lo : ℕ} {s : Stage} {ss : List Stage}
    (hf : BankCertificate lo s.reserve 0 s.free)
    (hm : BankCertificate lo s.reserve 1 s.moving)
    (ht : Checks lo ss) : Checks lo (s::ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩
set_option quotPrecheck false

local notation "bank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxHeartbeats 4000000 in
private theorem certificates (b : Band) : Checks (start b) (stages b) := by
  cases b with
  | h3640 =>
    rw [stages]
    refine cons (bank! 84,189507,0x448b047d4080,0x31ad827550) (bank! 364,575865,0x3e4172845090,0x33b809f82c520) ?_
    refine cons (bank! 98,192573,0x51d6cba302d8,0x4580660d60) (bank! 433,747746,0x4dca58f45d40,0x76bb078918b68) ?_
    refine cons (bank! 106,242473,0x70b4de83f180,0x69f1a62080) (bank! 446,698805,0x712e0f855774,0xa9ff5894a32c0) ?_
    refine cons (bank! 120,238259,0xd33cab038ed0,0xe9ceac35b0) (bank! 547,912688,0x125c444ea0bf8,0x1ccf2a786defe0) ?_
    refine cons (bank! 137,217908,0xd972566845dc,0x123611174f4) (bank! 592,913029,0x198cf585b8530,0x2d3eca64e57c48) ?_
    refine cons (bank! 146,319815,0x10179f2ebc444,0x18be0cacd0c) (bank! 635,988794,0x1a8daf6685bc0,0x40dc3435bf3b18) ?_
    refine cons (bank! 173,259380,0x23a9c0c427c20,0x4d5aedae3b8) (bank! 776,0x11cf2c,0x613e8e811b758,0xe972d7d933c070) ?_
    refine cons (bank! 238,366271,0x1bad2dbf4e950,0xf7be629c170) (bank! 1058,0x18a010,0x129ba079295580,0x477b10e2e2f1150) ?_
    refine cons (bank! 242,380301,0x23464ac5c9f5c,0x183158cd74b8) (bank! 1107,0x18f4a3,0x1628a72b0b785c,0x601e3b4a08f5f1c) ?_
    refine cons (bank! 296,453429,0x1ace443935a0,0x415156ed8498) (bank! 1420,0x1fbae2,0x418b228714b3b8,0x12169c023591bfa0) ?_
    refine cons (bank! 329,496478,0x1ce1682f99d0,0x1620eb3373b68) (bank! 1307,0x1cc8eb,0x190b6f10ebb560,0xaa34058facf1f420) ?_
    refine cons (bank! 419,662038,0x5b8e172b76a8,0x1355d9d064ef8) (bank! 1884,0x2aab76,0xc444e04db66438,0x5aba801ca0c9ee70) ?_
    refine cons (bank! 394,574249,0x41fc067c1b30,0x7447fba4ee828) (bank! 1586,0x2191c1,0x4d096d751f65d8,0x5235b41709fed51a0) ?_
    refine cons (bank! 579,777408,0x15c1b98e7a7c8,0x6f910b8de9280) (bank! 2635,0x3aead5,0x2e7dd98a8435150,0x20282df41c62d7798) ?_
    refine cons (bank! 854,0x13012d,0x86c862f12ae24,0x290a8cdec1cf3c) (bank! 3685,0x523de0,0xabc95d39dc07628,0xcd515858ac968bca0) ?_
    refine cons (bank! 1044,0x168e89,0xb8e2e39cd8fb0,0x6b22988d0159a0) (bank! 4711,0x68a17e,0x1d33764439fe7c40,0x24071b7ea51cc5500c) ?_
    exact nil
  | h3690 =>
    rw [stages]
    refine cons (bank! 84,193657,0x4e3ee7f82a20,0x31ad827550) (bank! 364,594015,0x13aeec4db8a248,0x282b954f11140) ?_
    refine cons (bank! 98,197323,0x5f69df919f98,0x4580660d60) (bank! 433,769246,0x5ac44f57f010,0x592e741479da8) ?_
    refine cons (bank! 106,247523,0x856610f64a80,0x69f1a62080) (bank! 446,720855,0x6f2e6bc90ec4,0x7c0d07c44a750) ?_
    refine cons (bank! 120,243809,0x100e708a60b30,0xe9ceac35b0) (bank! 547,939588,0x135e46b2df0e8,0x151ab9dbe05730) ?_
    refine cons (bank! 137,224208,0x1125b4bd11d84,0x123611174f4) (bank! 592,942079,0x13775228bb6c0,0x20f9617f18acb8) ?_
    refine cons (bank! 146,326465,0x14ecbda87d09c,0x18be0cacd0c) (bank! 635,0xf8ff6,0x1902e5eb6c6dc,0x2f2ec357e22e1c) ?_
    refine cons (bank! 173,266980,0x32c583302f610,0x4d5aedae3b8) (bank! 777,0x1262d4,0x61634e48f6d70,0xa39531effcea30) ?_
    refine cons (bank! 238,376521,0x4c105d01cb130,0xf7be629c170) (bank! 1059,0x196874,0x142bdc2bcba448,0x31f720f90ea6980) ?_
    refine cons (bank! 242,390551,0x6ee08047d6b4c,0x183158cd74b8) (bank! 1107,0x19c5d1,0x11dcfd7a437658,0x423e3a2f1ab21f0) ?_
    refine cons (bank! 296,465779,0x5cd303734e59c,0x3c5fb6d749c8) (bank! 1420,0x20c6da,0x33caca52a9ac70,0xcc391f34f947b18) ?_
    refine cons (bank! 329,509678,0xdb9a3cc11480,0x114f24c7d3700) (bank! 1307,0x1dbbb1,0x1c7773e2176f44,0x3ae92ae44e1067ac) ?_
    refine cons (bank! 419,679338,0x87b1f2c382d8,0x10e78db343188) (bank! 1884,0x2c0d5e,0xb2f13722caa8c4,0x3e13108523aff550) ?_
    refine cons (bank! 394,589699,0x6be73aeb3800,0x5262aef4faf28) (bank! 1586,0x22b74f,0x4e34388802a3bc,0x11384123273c87c4c) ?_
    refine cons (bank! 579,800908,0x179f960169d68,0x60d4a39f1d5f8) (bank! 2635,0x3cd863,0x277a47063c545a8,0x15c92c245c335cb28) ?_
    refine cons (bank! 854,0x138823,0x5f4f9d453806c,0x24083614e20d6c) (bank! 3686,0x54ee28,0x78127bb49a87c80,0x870e47d46bc612b80) ?_
    refine cons (bank! 1044,0x17332f,0xd31602cefdea8,0x5e5ca93d712b10) (bank! 4712,0x6c1322,0x15971fba8a0136d8,0x189b770eeae44171c8) ?_
    exact nil
  | h10300 =>
    rw [stages]
    refine cons (bank! 16,162253,0xfd521db18,0x2541db0) (bank! 29,207172,0xa34ec43820,0x1d4ed9a8) ?_
    refine cons (bank! 30,224639,0x43c4355930,0xd5e5da0) (bank! 54,376581,0x3ba5b63e570,0x11f852ac0) ?_
    refine cons (bank! 48,321655,0x13172d01f80,0x5c1ee518) (bank! 90,632413,0x117bce30b3c0,0x9f40923c0) ?_
    refine cons (bank! 76,425827,0x42b6a90df50,0x2eeb83a88) (bank! 142,888527,0x2a46d3af4fbc,0x5d909c030c) ?_
    exact nil

theorem stage_bounds (b : Band) {s : Stage} (hs : s ∈ stages b)
    {h : ℕ} (hl : start b ≤ h) (hh : h ≤ 131071) :
    (WidthGuard h s.reserve s.free.shape ∧
      debit h s.free < gain h s.reserve s.free.shape 0 ∧ s.free.shape.U < p) ∧
    (WidthGuard h s.reserve s.moving.shape ∧
      debit h s.moving < gain h s.reserve s.moving.shape 1 ∧ s.moving.shape.U < p) := by
  obtain ⟨hf,hm⟩ := certificates b s hs
  exact ⟨of_certificate hl hh hf, of_certificate hl hh hm⟩

#print axioms stage_bounds
end HighCore82706Stages
