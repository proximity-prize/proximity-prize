import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part72

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s96 : directSlab w3 96 = 31053438472 := by decide +kernel
private theorem s97 : directSlab w3 97 = 30940848580 := by decide +kernel
private theorem s98 : directSlab w3 98 = 30828432954 := by decide +kernel
private theorem s99 : directSlab w3 99 = 30716046370 := by decide +kernel
private theorem s100 : directSlab w3 100 = 30603835118 := by decide +kernel
private theorem s101 : directSlab w3 101 = 30491654726 := by decide +kernel
private theorem s102 : directSlab w3 102 = 30379650730 := by decide +kernel
private theorem s103 : directSlab w3 103 = 30267679162 := by decide +kernel
private theorem s104 : directSlab w3 104 = 30155885306 := by decide +kernel
private theorem s105 : directSlab w3 105 = 30044125444 := by decide +kernel
private theorem s106 : directSlab w3 106 = 29932544360 := by decide +kernel
private theorem s107 : directSlab w3 107 = 29820999090 := by decide +kernel
private theorem s108 : directSlab w3 108 = 29709633662 := by decide +kernel
private theorem s109 : directSlab w3 109 = 29598305616 := by decide +kernel
private theorem s110 : directSlab w3 110 = 29487158730 := by decide +kernel
private theorem s111 : directSlab w3 111 = 29376050792 := by decide +kernel
private theorem s112 : directSlab w3 112 = 29265125082 := by decide +kernel
private theorem s113 : directSlab w3 113 = 29154240140 := by decide +kernel
private theorem s114 : directSlab w3 114 = 29043538490 := by decide +kernel
private theorem s115 : directSlab w3 115 = 28932879178 := by decide +kernel
private theorem s116 : directSlab w3 116 = 28822404476 := by decide +kernel
private theorem s117 : directSlab w3 117 = 28711973680 := by decide +kernel
private theorem s118 : directSlab w3 118 = 28601728562 := by decide +kernel
private theorem s119 : directSlab w3 119 = 28491529170 := by decide +kernel

theorem fee3Part96 : affineFeeChunk w3 96 24 = 714429707890 :=
  affineFeeCertified_eq w3 96 [31053438472, 30940848580, 30828432954, 30716046370, 30603835118, 30491654726, 30379650730, 30267679162, 30155885306, 30044125444, 29932544360, 29820999090, 29709633662, 29598305616, 29487158730, 29376050792, 29265125082, 29154240140, 29043538490, 28932879178, 28822404476, 28711973680, 28601728562, 28491529170]
    ⟨s96, s97, s98, s99, s100, s101, s102, s103, s104, s105, s106, s107, s108, s109, s110, s111, s112, s113, s114, s115, s116, s117, s118, s119, True.intro⟩

end Low48PrimaryPivot
