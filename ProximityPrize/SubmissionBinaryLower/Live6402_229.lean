import ProximityPrize.SubmissionBinaryLower.Live6402_228
open ProximityPrize.SubmissionBinaryLower B6402PricedCell B6402LinearCertificate B6402RectCover B6402PriceCells Binary6402Targets
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace Binary6402Live
def source229 (box : Box) : Array Row := let pair := B6402GridRouting.rows (Native6402Grid.key 229); cell pair.1 pair.2 49 box
theorem r229_0_1 : Receipt 49 (source229 Binary6402Cover.boxes_207[0]) Binary6402Cover.boxes_207[0] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared970,⟨w3194,w2388,w3199,w3200⟩,by decide +kernel,prepared970_ok,by decide +kernel⟩
theorem r229_0_2 : Receipt 49 (source229 Binary6402Cover.boxes_207[0]) Binary6402Cover.boxes_207[0] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared971,⟨w3194,w2388,w3201,w3202⟩,by decide +kernel,prepared971_ok,by decide +kernel⟩
theorem r229_1_1 : Receipt 49 (source229 Binary6402Cover.boxes_207[1]) Binary6402Cover.boxes_207[1] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared972,⟨w3194,w2418,w3199,w3200⟩,by decide +kernel,prepared972_ok,by decide +kernel⟩
theorem r229_1_2 : Receipt 49 (source229 Binary6402Cover.boxes_207[1]) Binary6402Cover.boxes_207[1] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared973,⟨w3194,w2418,w3201,w3202⟩,by decide +kernel,prepared973_ok,by decide +kernel⟩
theorem r229_2_1 : Receipt 49 (source229 Binary6402Cover.boxes_207[2]) Binary6402Cover.boxes_207[2] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared974,⟨w3194,w2418,w3199,w3200⟩,by decide +kernel,prepared974_ok,by decide +kernel⟩
theorem r229_2_2 : Receipt 49 (source229 Binary6402Cover.boxes_207[2]) Binary6402Cover.boxes_207[2] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared975,⟨w3194,w2418,w3201,w3202⟩,by decide +kernel,prepared975_ok,by decide +kernel⟩
theorem bank229_1 (i : Fin Binary6402Cover.boxes_207.size) : Receipt 49 (source229 Binary6402Cover.boxes_207[i]) Binary6402Cover.boxes_207[i] 1 1250000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r229_0_1
  · exact r229_1_1
  · exact r229_2_1
theorem bank229_2 (i : Fin Binary6402Cover.boxes_207.size) : Receipt 49 (source229 Binary6402Cover.boxes_207[i]) Binary6402Cover.boxes_207[i] 2 2500000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r229_0_2
  · exact r229_1_2
  · exact r229_2_2
#print axioms bank229_2
end Binary6402Live
