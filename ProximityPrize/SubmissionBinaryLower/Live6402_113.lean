import ProximityPrize.SubmissionBinaryLower.Live6402_112
open ProximityPrize.SubmissionBinaryLower B6402PricedCell B6402LinearCertificate B6402RectCover B6402PriceCells Binary6402Targets
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace Binary6402Live
def source113 (box : Box) : Array Row := let pair := B6402GridRouting.rows (Native6402Grid.key 113); cell pair.1 pair.2 49 box
theorem r113_0_1 : Receipt 49 (source113 Binary6402Cover.boxes_91[0]) Binary6402Cover.boxes_91[0] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared360,⟨w1689,w1586,w1690,w1694⟩,by decide +kernel,prepared360_ok,by decide +kernel⟩
theorem r113_0_2 : Receipt 49 (source113 Binary6402Cover.boxes_91[0]) Binary6402Cover.boxes_91[0] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared361,⟨w1689,w1586,w1692,w1693⟩,by decide +kernel,prepared361_ok,by decide +kernel⟩
theorem r113_1_1 : Receipt 49 (source113 Binary6402Cover.boxes_91[1]) Binary6402Cover.boxes_91[1] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared362,⟨w1689,w1616,w1690,w1694⟩,by decide +kernel,prepared362_ok,by decide +kernel⟩
theorem r113_1_2 : Receipt 49 (source113 Binary6402Cover.boxes_91[1]) Binary6402Cover.boxes_91[1] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared363,⟨w1689,w1616,w1692,w1693⟩,by decide +kernel,prepared363_ok,by decide +kernel⟩
theorem r113_2_1 : Receipt 49 (source113 Binary6402Cover.boxes_91[2]) Binary6402Cover.boxes_91[2] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared364,⟨w1689,w1616,w1690,w1694⟩,by decide +kernel,prepared364_ok,by decide +kernel⟩
theorem r113_2_2 : Receipt 49 (source113 Binary6402Cover.boxes_91[2]) Binary6402Cover.boxes_91[2] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared365,⟨w1689,w1616,w1692,w1693⟩,by decide +kernel,prepared365_ok,by decide +kernel⟩
theorem bank113_1 (i : Fin Binary6402Cover.boxes_91.size) : Receipt 49 (source113 Binary6402Cover.boxes_91[i]) Binary6402Cover.boxes_91[i] 1 1250000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r113_0_1
  · exact r113_1_1
  · exact r113_2_1
theorem bank113_2 (i : Fin Binary6402Cover.boxes_91.size) : Receipt 49 (source113 Binary6402Cover.boxes_91[i]) Binary6402Cover.boxes_91[i] 2 2500000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r113_0_2
  · exact r113_1_2
  · exact r113_2_2
#print axioms bank113_2
end Binary6402Live
