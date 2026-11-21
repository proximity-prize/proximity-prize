import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part168

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s192 : directSlab w3 192 = 20810154766 := by decide +kernel
private theorem s193 : directSlab w3 193 = 20710489240 := by decide +kernel
private theorem s194 : directSlab w3 194 = 20611053278 := by decide +kernel
private theorem s195 : directSlab w3 195 = 20511725734 := by decide +kernel
private theorem s196 : directSlab w3 196 = 20412628808 := by decide +kernel
private theorem s197 : directSlab w3 197 = 20313642108 := by decide +kernel
private theorem s198 : directSlab w3 198 = 20214887050 := by decide +kernel
private theorem s199 : directSlab w3 199 = 20116243770 := by decide +kernel
private theorem s200 : directSlab w3 200 = 20017833434 := by decide +kernel
private theorem s201 : directSlab w3 201 = 19919536394 := by decide +kernel
private theorem s202 : directSlab w3 202 = 19821473346 := by decide +kernel
private theorem s203 : directSlab w3 203 = 19723525394 := by decide +kernel
private theorem s204 : directSlab w3 204 = 19625812442 := by decide +kernel
private theorem s205 : directSlab w3 205 = 19528216132 := by decide +kernel
private theorem s206 : directSlab w3 206 = 19430856116 := by decide +kernel
private theorem s207 : directSlab w3 207 = 19333614246 := by decide +kernel
private theorem s208 : directSlab w3 208 = 19236609710 := by decide +kernel
private theorem s209 : directSlab w3 209 = 19139725112 := by decide +kernel
private theorem s210 : directSlab w3 210 = 19043078842 := by decide +kernel
private theorem s211 : directSlab w3 211 = 18946554048 := by decide +kernel
private theorem s212 : directSlab w3 212 = 18850268870 := by decide +kernel
private theorem s213 : directSlab w3 213 = 18754106656 := by decide +kernel
private theorem s214 : directSlab w3 214 = 18658185090 := by decide +kernel
private theorem s215 : directSlab w3 215 = 18562388274 := by decide +kernel

theorem fee3Part192 : affineFeeChunk w3 192 24 = 472292608860 :=
  affineFeeCertified_eq w3 192 [20810154766, 20710489240, 20611053278, 20511725734, 20412628808, 20313642108, 20214887050, 20116243770, 20017833434, 19919536394, 19821473346, 19723525394, 19625812442, 19528216132, 19430856116, 19333614246, 19236609710, 19139725112, 19043078842, 18946554048, 18850268870, 18754106656, 18658185090, 18562388274]
    ⟨s192, s193, s194, s195, s196, s197, s198, s199, s200, s201, s202, s203, s204, s205, s206, s207, s208, s209, s210, s211, s212, s213, s214, s215, True.intro⟩

end Low48PrimaryPivot
