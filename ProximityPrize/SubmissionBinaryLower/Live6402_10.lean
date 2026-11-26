import ProximityPrize.SubmissionBinaryLower.Live6402_9
open ProximityPrize.SubmissionBinaryLower B6402PricedCell B6402LinearCertificate B6402RectCover B6402PriceCells Binary6402Targets
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace Binary6402Live
def source10 (box : Box) : Array Row := let pair := B6402GridRouting.rows (Native6402Grid.key 10); cell pair.1 pair.2 23 box
theorem r10_0_1 : Receipt 23 (source10 Binary6402Cover.boxes_5[0]) Binary6402Cover.boxes_5[0] 1 2100000000000000000 (3/100) := Or.inr ⟨prepared58,⟨w120,w121,w122,w123⟩,by decide +kernel,prepared58_ok,by decide +kernel⟩
theorem r10_0_2 : Receipt 23 (source10 Binary6402Cover.boxes_5[0]) Binary6402Cover.boxes_5[0] 2 4200000000000000000 (3/100) := Or.inr ⟨prepared59,⟨w120,w121,w124,w125⟩,by decide +kernel,prepared59_ok,by decide +kernel⟩
theorem r10_1_1 : Receipt 23 (source10 Binary6402Cover.boxes_5[1]) Binary6402Cover.boxes_5[1] 1 2100000000000000000 (3/100) := Or.inr ⟨prepared60,⟨w126,w127,w122,w123⟩,by decide +kernel,prepared60_ok,by decide +kernel⟩
theorem r10_1_2 : Receipt 23 (source10 Binary6402Cover.boxes_5[1]) Binary6402Cover.boxes_5[1] 2 4200000000000000000 (3/100) := Or.inr ⟨prepared61,⟨w126,w127,w124,w125⟩,by decide +kernel,prepared61_ok,by decide +kernel⟩
theorem r10_2_1 : Receipt 23 (source10 Binary6402Cover.boxes_5[2]) Binary6402Cover.boxes_5[2] 1 2100000000000000000 (3/100) := Or.inr ⟨prepared62,⟨w126,w127,w122,w123⟩,by decide +kernel,prepared62_ok,by decide +kernel⟩
theorem r10_2_2 : Receipt 23 (source10 Binary6402Cover.boxes_5[2]) Binary6402Cover.boxes_5[2] 2 4200000000000000000 (3/100) := Or.inr ⟨prepared63,⟨w126,w127,w124,w125⟩,by decide +kernel,prepared63_ok,by decide +kernel⟩
theorem bank10_1 (i : Fin Binary6402Cover.boxes_5.size) : Receipt 23 (source10 Binary6402Cover.boxes_5[i]) Binary6402Cover.boxes_5[i] 1 2100000000000000000 (3/100) := by
  change Fin 3 at i
  fin_cases i
  · exact r10_0_1
  · exact r10_1_1
  · exact r10_2_1
theorem bank10_2 (i : Fin Binary6402Cover.boxes_5.size) : Receipt 23 (source10 Binary6402Cover.boxes_5[i]) Binary6402Cover.boxes_5[i] 2 4200000000000000000 (3/100) := by
  change Fin 3 at i
  fin_cases i
  · exact r10_0_2
  · exact r10_1_2
  · exact r10_2_2
#print axioms bank10_2
end Binary6402Live
