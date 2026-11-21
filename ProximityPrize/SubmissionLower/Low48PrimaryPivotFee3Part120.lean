import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part96

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s120 : directSlab w3 120 = 28381516522 := by decide +kernel
private theorem s121 : directSlab w3 121 = 28271551170 := by decide +kernel
private theorem s122 : directSlab w3 122 = 28161773882 := by decide +kernel
private theorem s123 : directSlab w3 123 = 28052045458 := by decide +kernel
private theorem s124 : directSlab w3 124 = 27942506166 := by decide +kernel
private theorem s125 : directSlab w3 125 = 27833017560 := by decide +kernel
private theorem s126 : directSlab w3 126 = 27723719152 := by decide +kernel
private theorem s127 : directSlab w3 127 = 27614473002 := by decide +kernel
private theorem s128 : directSlab w3 128 = 27505418370 := by decide +kernel
private theorem s129 : directSlab w3 129 = 27396417564 := by decide +kernel
private theorem s130 : directSlab w3 130 = 27287609346 := by decide +kernel
private theorem s131 : directSlab w3 131 = 27178856776 := by decide +kernel
private theorem s132 : directSlab w3 132 = 27070297862 := by decide +kernel
private theorem s133 : directSlab w3 133 = 26961796168 := by decide +kernel
private theorem s134 : directSlab w3 134 = 26853489450 := by decide +kernel
private theorem s135 : directSlab w3 135 = 26745241522 := by decide +kernel
private theorem s136 : directSlab w3 136 = 26637189640 := by decide +kernel
private theorem s137 : directSlab w3 137 = 26529198372 := by decide +kernel
private theorem s138 : directSlab w3 138 = 26421404218 := by decide +kernel
private theorem s139 : directSlab w3 139 = 26313672250 := by decide +kernel
private theorem s140 : directSlab w3 140 = 26206138718 := by decide +kernel
private theorem s141 : directSlab w3 141 = 26098668942 := by decide +kernel
private theorem s142 : directSlab w3 142 = 25991398674 := by decide +kernel
private theorem s143 : directSlab w3 143 = 25884193986 := by decide +kernel

theorem fee3Part120 : affineFeeChunk w3 120 24 = 651061594770 :=
  affineFeeCertified_eq w3 120 [28381516522, 28271551170, 28161773882, 28052045458, 27942506166, 27833017560, 27723719152, 27614473002, 27505418370, 27396417564, 27287609346, 27178856776, 27070297862, 26961796168, 26853489450, 26745241522, 26637189640, 26529198372, 26421404218, 26313672250, 26206138718, 26098668942, 25991398674, 25884193986]
    ⟨s120, s121, s122, s123, s124, s125, s126, s127, s128, s129, s130, s131, s132, s133, s134, s135, s136, s137, s138, s139, s140, s141, s142, s143, True.intro⟩

end Low48PrimaryPivot
