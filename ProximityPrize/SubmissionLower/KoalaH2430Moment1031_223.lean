import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Banks
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem p223 : blockEstimate 1031 223 223 128 = 0x13f43ea0 := by decide +kernel
private theorem p351 : blockEstimate 1031 223 351 128 = 0x795e7e78 := by decide +kernel
private theorem p479 : blockEstimate 1031 223 479 128 = 0xfbcc7c00 := by decide +kernel
private theorem p607 : blockEstimate 1031 223 607 128 = 0x14db87c00 := by decide +kernel
private theorem p735 : blockEstimate 1031 223 735 128 = 0x167a47c00 := by decide +kernel
private theorem p863 : blockEstimate 1031 223 863 128 = 0x149907c00 := by decide +kernel
private theorem p991 : blockEstimate 1031 223 991 128 = 0xf5d4f20c := by decide +kernel
private theorem p1119 : blockEstimate 1031 223 1119 128 = 0x8c021cce := by decide +kernel
private theorem p1247 : blockEstimate 1031 223 1247 128 = 0x3382c12b := by decide +kernel
private theorem p1375 : blockEstimate 1031 223 1375 102 = 0x56ad0df := by decide +kernel

theorem moment1031_223 : momentEstimate 1031 223 = 0x742d14dfc :=
  moment_from_blocks [⟨128,0x13f43ea0⟩, ⟨128,0x795e7e78⟩, ⟨128,0xfbcc7c00⟩, ⟨128,0x14db87c00⟩, ⟨128,0x167a47c00⟩, ⟨128,0x149907c00⟩, ⟨128,0xf5d4f20c⟩, ⟨128,0x8c021cce⟩, ⟨128,0x3382c12b⟩, ⟨102,0x56ad0df⟩] ⟨p223, p351, p479, p607, p735, p863, p991, p1119, p1247, p1375, trivial⟩ rfl rfl

end KoalaH2430Banks
