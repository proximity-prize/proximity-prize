import ProximityPrize.SubmissionBinaryLower.Live6402_134
open ProximityPrize.SubmissionBinaryLower B6402PricedCell B6402LinearCertificate B6402RectCover B6402PriceCells Binary6402Targets
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace Binary6402Live
def source135 (box : Box) : Array Row := let pair := B6402GridRouting.rows (Native6402Grid.key 135); cell pair.1 pair.2 49 box
theorem r135_0_1 : Receipt 49 (source135 Binary6402Cover.boxes_124[0]) Binary6402Cover.boxes_124[0] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared366,⟨w2010,w1586,w2011,w2012⟩,by decide +kernel,prepared366_ok,by decide +kernel⟩
theorem r135_0_2 : Receipt 49 (source135 Binary6402Cover.boxes_124[0]) Binary6402Cover.boxes_124[0] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared367,⟨w2010,w1586,w2013,w2014⟩,by decide +kernel,prepared367_ok,by decide +kernel⟩
def w2067 : Weights := [(2,(90170642432/54102390625)),(3,(721365139456/270511953125)),(4,(135255963648/270511953125)),(6,(23083706476909/55400848000000)),(10,(45085321216/54102390625)),(14,(180341310693/270511953125)),(15,(360682569728/270511953125)),(17,(180341284864/270511953125)),(19,(180341284864/270511953125)),(26,(90170642432/270511953125)),(46,(90170642432/1352559765625)),(52,(1082047709184/1352559765625)),(58,(90170642432/270511953125)),(60,(90170642432/270511953125)),(62,(180341284864/270511953125)),(66,(90170642432/1352559765625)),(69,(90170642432/1352559765625)),(80,(90170642432/1352559765625)),(84,(90170642432/1352559765625)),(88,(180341284864/270511953125))]
theorem r135_1_1 : Receipt 49 (source135 Binary6402Cover.boxes_124[1]) Binary6402Cover.boxes_124[1] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared368,⟨w2067,w1616,w2011,w2012⟩,by decide +kernel,prepared368_ok,by decide +kernel⟩
theorem r135_1_2 : Receipt 49 (source135 Binary6402Cover.boxes_124[1]) Binary6402Cover.boxes_124[1] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared369,⟨w2067,w1616,w2013,w2014⟩,by decide +kernel,prepared369_ok,by decide +kernel⟩
theorem r135_2_1 : Receipt 49 (source135 Binary6402Cover.boxes_124[2]) Binary6402Cover.boxes_124[2] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared370,⟨w2010,w1616,w2011,w2012⟩,by decide +kernel,prepared370_ok,by decide +kernel⟩
theorem r135_2_2 : Receipt 49 (source135 Binary6402Cover.boxes_124[2]) Binary6402Cover.boxes_124[2] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared371,⟨w2010,w1616,w2013,w2014⟩,by decide +kernel,prepared371_ok,by decide +kernel⟩
theorem bank135_1 (i : Fin Binary6402Cover.boxes_124.size) : Receipt 49 (source135 Binary6402Cover.boxes_124[i]) Binary6402Cover.boxes_124[i] 1 1250000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r135_0_1
  · exact r135_1_1
  · exact r135_2_1
theorem bank135_2 (i : Fin Binary6402Cover.boxes_124.size) : Receipt 49 (source135 Binary6402Cover.boxes_124[i]) Binary6402Cover.boxes_124[i] 2 2500000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r135_0_2
  · exact r135_1_2
  · exact r135_2_2
#print axioms bank135_2
end Binary6402Live
