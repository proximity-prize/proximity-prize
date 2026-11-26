import ProximityPrize.SubmissionBinaryLower.Live6402_145
open ProximityPrize.SubmissionBinaryLower B6402PricedCell B6402LinearCertificate B6402RectCover B6402PriceCells Binary6402Targets
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace Binary6402Live
def source146 (box : Box) : Array Row := let pair := B6402GridRouting.rows (Native6402Grid.key 146); cell pair.1 pair.2 49 box
theorem r146_0_1 : Receipt 49 (source146 Binary6402Cover.boxes_124[0]) Binary6402Cover.boxes_124[0] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared366,⟨w2067,w1586,w2011,w2012⟩,by decide +kernel,prepared366_ok,by decide +kernel⟩
theorem r146_0_2 : Receipt 49 (source146 Binary6402Cover.boxes_124[0]) Binary6402Cover.boxes_124[0] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared367,⟨w2067,w1586,w2013,w2014⟩,by decide +kernel,prepared367_ok,by decide +kernel⟩
theorem r146_1_1 : Receipt 49 (source146 Binary6402Cover.boxes_124[1]) Binary6402Cover.boxes_124[1] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared368,⟨w2010,w1616,w2011,w2012⟩,by decide +kernel,prepared368_ok,by decide +kernel⟩
theorem r146_1_2 : Receipt 49 (source146 Binary6402Cover.boxes_124[1]) Binary6402Cover.boxes_124[1] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared369,⟨w2010,w1616,w2013,w2014⟩,by decide +kernel,prepared369_ok,by decide +kernel⟩
theorem r146_2_1 : Receipt 49 (source146 Binary6402Cover.boxes_124[2]) Binary6402Cover.boxes_124[2] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared370,⟨w2010,w1616,w2011,w2012⟩,by decide +kernel,prepared370_ok,by decide +kernel⟩
theorem r146_2_2 : Receipt 49 (source146 Binary6402Cover.boxes_124[2]) Binary6402Cover.boxes_124[2] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared371,⟨w2010,w1616,w2013,w2014⟩,by decide +kernel,prepared371_ok,by decide +kernel⟩
theorem bank146_1 (i : Fin Binary6402Cover.boxes_124.size) : Receipt 49 (source146 Binary6402Cover.boxes_124[i]) Binary6402Cover.boxes_124[i] 1 1250000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r146_0_1
  · exact r146_1_1
  · exact r146_2_1
theorem bank146_2 (i : Fin Binary6402Cover.boxes_124.size) : Receipt 49 (source146 Binary6402Cover.boxes_124[i]) Binary6402Cover.boxes_124[i] 2 2500000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r146_0_2
  · exact r146_1_2
  · exact r146_2_2
#print axioms bank146_2
end Binary6402Live
