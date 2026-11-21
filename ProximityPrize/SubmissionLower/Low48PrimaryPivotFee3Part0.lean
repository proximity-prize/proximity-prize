import ProximityPrize.SubmissionLower.Low48PrimaryPivotFeeBase

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s0 : directSlab w3 0 = 42223791708 := by decide +kernel
private theorem s1 : directSlab w3 1 = 42104723828 := by decide +kernel
private theorem s2 : directSlab w3 2 = 41985775400 := by decide +kernel
private theorem s3 : directSlab w3 3 = 41866777098 := by decide +kernel
private theorem s4 : directSlab w3 4 = 41747899302 := by decide +kernel
private theorem s5 : directSlab w3 5 = 41628973440 := by decide +kernel
private theorem s6 : directSlab w3 6 = 41510169136 := by decide +kernel
private theorem s7 : directSlab w3 7 = 41391318324 := by decide +kernel
private theorem s8 : directSlab w3 8 = 41272590376 := by decide +kernel
private theorem s9 : directSlab w3 9 = 41153817474 := by decide +kernel
private theorem s10 : directSlab w3 10 = 41035168492 := by decide +kernel
private theorem s11 : directSlab w3 11 = 40916476362 := by decide +kernel
private theorem s12 : directSlab w3 12 = 40797909206 := by decide +kernel
private theorem s13 : directSlab w3 13 = 40679300460 := by decide +kernel
private theorem s14 : directSlab w3 14 = 40560817992 := by decide +kernel
private theorem s15 : directSlab w3 15 = 40442295490 := by decide +kernel
private theorem s16 : directSlab w3 16 = 40323900320 := by decide +kernel
private theorem s17 : directSlab w3 17 = 40205466924 := by decide +kernel
private theorem s18 : directSlab w3 18 = 40087161914 := by decide +kernel
private theorem s19 : directSlab w3 19 = 39968820234 := by decide +kernel
private theorem s20 : directSlab w3 20 = 39850608246 := by decide +kernel
private theorem s21 : directSlab w3 21 = 39732361142 := by decide +kernel
private theorem s22 : directSlab w3 22 = 39614244786 := by decide +kernel
private theorem s23 : directSlab w3 23 = 39496095122 := by decide +kernel

theorem fee3Part0 : affineFeeChunk w3 0 24 = 980596462776 :=
  affineFeeCertified_eq w3 0 [42223791708, 42104723828, 41985775400, 41866777098, 41747899302, 41628973440, 41510169136, 41391318324, 41272590376, 41153817474, 41035168492, 40916476362, 40797909206, 40679300460, 40560817992, 40442295490, 40323900320, 40205466924, 40087161914, 39968820234, 39850608246, 39732361142, 39614244786, 39496095122]
    ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, True.intro⟩

end Low48PrimaryPivot
