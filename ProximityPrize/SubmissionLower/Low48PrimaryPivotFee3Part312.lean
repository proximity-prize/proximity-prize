import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part288

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s312 : directSlab w3 312 = 10244934134 := by decide +kernel
private theorem s313 : directSlab w3 313 = 10170208624 := by decide +kernel
private theorem s314 : directSlab w3 314 = 10095774654 := by decide +kernel
private theorem s315 : directSlab w3 315 = 10021541046 := by decide +kernel
private theorem s316 : directSlab w3 316 = 9947599888 := by decide +kernel
private theorem s317 : directSlab w3 317 = 9873860756 := by decide +kernel
private theorem s318 : directSlab w3 318 = 9800414794 := by decide +kernel
private theorem s319 : directSlab w3 319 = 9727172266 := by decide +kernel
private theorem s320 : directSlab w3 320 = 9654224066 := by decide +kernel
private theorem s321 : directSlab w3 321 = 9581480514 := by decide +kernel
private theorem s322 : directSlab w3 322 = 9509032194 := by decide +kernel
private theorem s323 : directSlab w3 323 = 9436790178 := by decide +kernel
private theorem s324 : directSlab w3 324 = 9364844098 := by decide +kernel
private theorem s325 : directSlab w3 325 = 9293105724 := by decide +kernel
private theorem s326 : directSlab w3 326 = 9221664436 := by decide +kernel
private theorem s327 : directSlab w3 327 = 9150432054 := by decide +kernel
private theorem s328 : directSlab w3 328 = 9079497654 := by decide +kernel
private theorem s329 : directSlab w3 329 = 9008773808 := by decide +kernel
private theorem s330 : directSlab w3 330 = 8938348634 := by decide +kernel
private theorem s331 : directSlab w3 331 = 8868135408 := by decide +kernel
private theorem s332 : directSlab w3 332 = 8798221998 := by decide +kernel
private theorem s333 : directSlab w3 333 = 8728521720 := by decide +kernel
private theorem s334 : directSlab w3 334 = 8659703662 := by decide +kernel
private theorem s335 : directSlab w3 335 = 8591128468 := by decide +kernel

theorem fee3Part312 : affineFeeChunk w3 312 24 = 225765410778 :=
  affineFeeCertified_eq w3 312 [10244934134, 10170208624, 10095774654, 10021541046, 9947599888, 9873860756, 9800414794, 9727172266, 9654224066, 9581480514, 9509032194, 9436790178, 9364844098, 9293105724, 9221664436, 9150432054, 9079497654, 9008773808, 8938348634, 8868135408, 8798221998, 8728521720, 8659703662, 8591128468]
    ⟨s312, s313, s314, s315, s316, s317, s318, s319, s320, s321, s322, s323, s324, s325, s326, s327, s328, s329, s330, s331, s332, s333, s334, s335, True.intro⟩

end Low48PrimaryPivot
