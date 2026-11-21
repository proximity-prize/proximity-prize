import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part216

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s240 : directSlab w2 240 = 97911469420 := by decide +kernel
private theorem s241 : directSlab w2 241 = 97481340432 := by decide +kernel
private theorem s242 : directSlab w2 242 = 97051187928 := by decide +kernel
private theorem s243 : directSlab w2 243 = 96620643130 := by decide +kernel
private theorem s244 : directSlab w2 244 = 96190080956 := by decide +kernel
private theorem s245 : directSlab w2 245 = 95759130628 := by decide +kernel
private theorem s246 : directSlab w2 246 = 95328170732 := by decide +kernel
private theorem s247 : directSlab w2 247 = 94896827164 := by decide +kernel
private theorem s248 : directSlab w2 248 = 94465480888 := by decide +kernel
private theorem s249 : directSlab w2 249 = 94033757074 := by decide +kernel
private theorem s250 : directSlab w2 250 = 93602037772 := by decide +kernel
private theorem s251 : directSlab w2 251 = 93169946100 := by decide +kernel
private theorem s252 : directSlab w2 252 = 92737867828 := by decide +kernel
private theorem s253 : directSlab w2 253 = 92305422698 := by decide +kernel
private theorem s254 : directSlab w2 254 = 91872998908 := by decide +kernel
private theorem s255 : directSlab w2 255 = 91440215422 := by decide +kernel
private theorem s256 : directSlab w2 256 = 91007461576 := by decide +kernel
private theorem s257 : directSlab w2 257 = 90574354232 := by decide +kernel
private theorem s258 : directSlab w2 258 = 90141286496 := by decide +kernel
private theorem s259 : directSlab w2 259 = 89707871802 := by decide +kernel
private theorem s260 : directSlab w2 260 = 89274505736 := by decide +kernel
private theorem s261 : directSlab w2 261 = 88840800904 := by decide +kernel
private theorem s262 : directSlab w2 262 = 88407154080 := by decide +kernel
private theorem s263 : directSlab w2 263 = 87973175716 := by decide +kernel

theorem fee2Part240 : affineFeeChunk w2 240 24 = 2230793187622 :=
  affineFeeCertified_eq w2 240 [97911469420, 97481340432, 97051187928, 96620643130, 96190080956, 95759130628, 95328170732, 94896827164, 94465480888, 94033757074, 93602037772, 93169946100, 92737867828, 92305422698, 91872998908, 91440215422, 91007461576, 90574354232, 90141286496, 89707871802, 89274505736, 88840800904, 88407154080, 87973175716]
    ⟨s240, s241, s242, s243, s244, s245, s246, s247, s248, s249, s250, s251, s252, s253, s254, s255, s256, s257, s258, s259, s260, s261, s262, s263, True.intro⟩

end Low48PrimaryPivot
