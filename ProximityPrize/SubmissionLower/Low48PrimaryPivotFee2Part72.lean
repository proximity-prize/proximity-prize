import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part48

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s72 : directSlab w2 72 = 168753500304 := by decide +kernel
private theorem s73 : directSlab w2 73 = 168319146824 := by decide +kernel
private theorem s74 : directSlab w2 74 = 167885318126 := by decide +kernel
private theorem s75 : directSlab w2 75 = 167451760924 := by decide +kernel
private theorem s76 : directSlab w2 76 = 167018721044 := by decide +kernel
private theorem s77 : directSlab w2 77 = 166585944410 := by decide +kernel
private theorem s78 : directSlab w2 78 = 166153678868 := by decide +kernel
private theorem s79 : directSlab w2 79 = 165721668224 := by decide +kernel
private theorem s80 : directSlab w2 80 = 165290161054 := by decide +kernel
private theorem s81 : directSlab w2 81 = 164858901648 := by decide +kernel
private theorem s82 : directSlab w2 82 = 164428138018 := by decide +kernel
private theorem s83 : directSlab w2 83 = 163997613612 := by decide +kernel
private theorem s84 : directSlab w2 84 = 163567578514 := by decide +kernel
private theorem s85 : directSlab w2 85 = 163137774004 := by decide +kernel
private theorem s86 : directSlab w2 86 = 162708450946 := by decide +kernel
private theorem s87 : directSlab w2 87 = 162279351052 := by decide +kernel
private theorem s88 : directSlab w2 88 = 161850724674 := by decide +kernel
private theorem s89 : directSlab w2 89 = 161422312632 := by decide +kernel
private theorem s90 : directSlab w2 90 = 160994367400 := by decide +kernel
private theorem s91 : directSlab w2 91 = 160566627578 := by decide +kernel
private theorem s92 : directSlab w2 92 = 160139346472 := by decide +kernel
private theorem s93 : directSlab w2 93 = 159712263064 := by decide +kernel
private theorem s94 : directSlab w2 94 = 159285630198 := by decide +kernel
private theorem s95 : directSlab w2 95 = 158859185912 := by decide +kernel

theorem fee2Part72 : affineFeeChunk w2 72 24 = 3930988165502 :=
  affineFeeCertified_eq w2 72 [168753500304, 168319146824, 167885318126, 167451760924, 167018721044, 166585944410, 166153678868, 165721668224, 165290161054, 164858901648, 164428138018, 163997613612, 163567578514, 163137774004, 162708450946, 162279351052, 161850724674, 161422312632, 160994367400, 160566627578, 160139346472, 159712263064, 159285630198, 158859185912]
    ⟨s72, s73, s74, s75, s76, s77, s78, s79, s80, s81, s82, s83, s84, s85, s86, s87, s88, s89, s90, s91, s92, s93, s94, s95, True.intro⟩

end Low48PrimaryPivot
