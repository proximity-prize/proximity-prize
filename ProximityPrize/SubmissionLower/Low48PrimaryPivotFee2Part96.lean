import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part72

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s96 : directSlab w2 96 = 158433185224 := by decide +kernel
private theorem s97 : directSlab w2 97 = 158007363902 := by decide +kernel
private theorem s98 : directSlab w2 98 = 157581977846 := by decide +kernel
private theorem s99 : directSlab w2 99 = 157156763154 := by decide +kernel
private theorem s100 : directSlab w2 100 = 156731975316 := by decide +kernel
private theorem s101 : directSlab w2 101 = 156307349436 := by decide +kernel
private theorem s102 : directSlab w2 102 = 155883143228 := by decide +kernel
private theorem s103 : directSlab w2 103 = 155459089474 := by decide +kernel
private theorem s104 : directSlab w2 104 = 155035446822 := by decide +kernel
private theorem s105 : directSlab w2 105 = 154611948334 := by decide +kernel
private theorem s106 : directSlab w2 106 = 154188852298 := by decide +kernel
private theorem s107 : directSlab w2 107 = 153765890730 := by decide +kernel
private theorem s108 : directSlab w2 108 = 153343324194 := by decide +kernel
private theorem s109 : directSlab w2 109 = 152920882334 := by decide +kernel
private theorem s110 : directSlab w2 110 = 152498826698 := by decide +kernel
private theorem s111 : directSlab w2 111 = 152076887158 := by decide +kernel
private theorem s112 : directSlab w2 112 = 151655324954 := by decide +kernel
private theorem s113 : directSlab w2 113 = 151233868862 := by decide +kernel
private theorem s114 : directSlab w2 114 = 150812782448 := by decide +kernel
private theorem s115 : directSlab w2 115 = 150391792064 := by decide +kernel
private theorem s116 : directSlab w2 116 = 149971162312 := by decide +kernel
private theorem s117 : directSlab w2 117 = 149550619722 := by decide +kernel
private theorem s118 : directSlab w2 118 = 149130428638 := by decide +kernel
private theorem s119 : directSlab w2 119 = 148710314442 := by decide +kernel

theorem fee2Part96 : affineFeeChunk w2 96 24 = 3685459199590 :=
  affineFeeCertified_eq w2 96 [158433185224, 158007363902, 157581977846, 157156763154, 156731975316, 156307349436, 155883143228, 155459089474, 155035446822, 154611948334, 154188852298, 153765890730, 153343324194, 152920882334, 152498826698, 152076887158, 151655324954, 151233868862, 150812782448, 150391792064, 149971162312, 149550619722, 149130428638, 148710314442]
    ⟨s96, s97, s98, s99, s100, s101, s102, s103, s104, s105, s106, s107, s108, s109, s110, s111, s112, s113, s114, s115, s116, s117, s118, s119, True.intro⟩

end Low48PrimaryPivot
