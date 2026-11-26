import ProximityPrize.SubmissionBinaryLower.Live6402_57
open ProximityPrize.SubmissionBinaryLower B6402PricedCell B6402LinearCertificate B6402RectCover B6402PriceCells Binary6402Targets
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace Binary6402Live
def source58 (box : Box) : Array Row := let pair := B6402GridRouting.rows (Native6402Grid.key 58); cell pair.1 pair.2 21 box
theorem r58_0_1 : Receipt 21 (source58 Binary6402Cover.boxes_48[0]) Binary6402Cover.boxes_48[0] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared148,⟨w1008,w247,w1009,w1010⟩,by decide +kernel,prepared148_ok,by decide +kernel⟩
theorem r58_0_2 : Receipt 21 (source58 Binary6402Cover.boxes_48[0]) Binary6402Cover.boxes_48[0] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared149,⟨w1008,w247,w1011,w1012⟩,by decide +kernel,prepared149_ok,by decide +kernel⟩
theorem r58_1_1 : Receipt 21 (source58 Binary6402Cover.boxes_48[1]) Binary6402Cover.boxes_48[1] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared150,⟨w1013,w253,w1009,w1010⟩,by decide +kernel,prepared150_ok,by decide +kernel⟩
theorem r58_1_2 : Receipt 21 (source58 Binary6402Cover.boxes_48[1]) Binary6402Cover.boxes_48[1] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared151,⟨w1013,w253,w1011,w1012⟩,by decide +kernel,prepared151_ok,by decide +kernel⟩
theorem r58_2_1 : Receipt 21 (source58 Binary6402Cover.boxes_48[2]) Binary6402Cover.boxes_48[2] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared152,⟨w1013,w253,w1009,w1010⟩,by decide +kernel,prepared152_ok,by decide +kernel⟩
theorem r58_2_2 : Receipt 21 (source58 Binary6402Cover.boxes_48[2]) Binary6402Cover.boxes_48[2] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared153,⟨w1013,w253,w1011,w1012⟩,by decide +kernel,prepared153_ok,by decide +kernel⟩
theorem bank58_1 (i : Fin Binary6402Cover.boxes_48.size) : Receipt 21 (source58 Binary6402Cover.boxes_48[i]) Binary6402Cover.boxes_48[i] 1 1250000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r58_0_1
  · exact r58_1_1
  · exact r58_2_1
theorem bank58_2 (i : Fin Binary6402Cover.boxes_48.size) : Receipt 21 (source58 Binary6402Cover.boxes_48[i]) Binary6402Cover.boxes_48[i] 2 2500000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r58_0_2
  · exact r58_1_2
  · exact r58_2_2
#print axioms bank58_2
end Binary6402Live
