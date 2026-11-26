import ProximityPrize.SubmissionBinaryLower.Live6402_67
open ProximityPrize.SubmissionBinaryLower B6402PricedCell B6402LinearCertificate B6402RectCover B6402PriceCells Binary6402Targets
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace Binary6402Live
def source68 (box : Box) : Array Row := let pair := B6402GridRouting.rows (Native6402Grid.key 68); cell pair.1 pair.2 21 box
def w1237 : Weights := [(41,(999937/2000000)),(47,(999937/2000000))]
def w1238 : Weights := [(0,(124851894031804564/2402984375)),(1,(58682741343289/1210000)),(4,(93638920523853423/2402984375)),(9,(31212973507951141/2402984375)),(16,(2652617158041/110000)),(34,(2652617158041/110000)),(35,(307403161608093/151250)),(37,(2652617158041/13750))]
def w1239 : Weights := [(0,(6809520876345812/131071875)),(1,(29338690933109/605000)),(4,(1702380219086453/43690625)),(9,(1702380219086453/131071875)),(16,(48225278051/2000)),(34,(48225278051/2000)),(35,(2459198365292267/1210000)),(37,(48225278051/250))]
def w1240 : Weights := [(0,(8240225003883142702/79298484375)),(1,(14670685331877/151250)),(4,(4120112501941571351/52865656250)),(9,(4120112501941571351/158596968750)),(16,(116715154922417/2420000)),(34,(116715154922417/2420000)),(35,(9836901168813639/2420000)),(37,(116715154922417/302500))]
def w1241 : Weights := [(0,(8239873411040208094/79298484375)),(1,(117360135041757/1210000)),(4,(4119936705520104047/52865656250)),(9,(4119936705520104047/158596968750)),(16,(116710174935449/2420000)),(34,(116710174935449/2420000)),(35,(9836847432883173/2420000)),(37,(116710174935449/302500))]
theorem r68_0_1 : Receipt 21 (source68 Binary6402Cover.boxes_48[0]) Binary6402Cover.boxes_48[0] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared148,⟨w1237,w662,w1238,w1239⟩,by decide +kernel,prepared148_ok,by decide +kernel⟩
theorem r68_0_2 : Receipt 21 (source68 Binary6402Cover.boxes_48[0]) Binary6402Cover.boxes_48[0] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared149,⟨w1237,w662,w1240,w1241⟩,by decide +kernel,prepared149_ok,by decide +kernel⟩
def w1242 : Weights := [(1,(8191483904/16382984375)),(2,(24574451712/16382984375)),(3,(8191483904/3276596875)),(6,(125821072773/167761760000)),(8,(32765935616/16382984375)),(10,(8191483904/16382984375)),(35,(8191483904/16382984375))]
theorem r68_1_1 : Receipt 21 (source68 Binary6402Cover.boxes_48[1]) Binary6402Cover.boxes_48[1] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared150,⟨w1242,w667,w1238,w1239⟩,by decide +kernel,prepared150_ok,by decide +kernel⟩
theorem r68_1_2 : Receipt 21 (source68 Binary6402Cover.boxes_48[1]) Binary6402Cover.boxes_48[1] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared151,⟨w1242,w667,w1240,w1241⟩,by decide +kernel,prepared151_ok,by decide +kernel⟩
theorem r68_2_1 : Receipt 21 (source68 Binary6402Cover.boxes_48[2]) Binary6402Cover.boxes_48[2] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared152,⟨w1242,w667,w1238,w1239⟩,by decide +kernel,prepared152_ok,by decide +kernel⟩
theorem r68_2_2 : Receipt 21 (source68 Binary6402Cover.boxes_48[2]) Binary6402Cover.boxes_48[2] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared153,⟨w1242,w667,w1240,w1241⟩,by decide +kernel,prepared153_ok,by decide +kernel⟩
theorem bank68_1 (i : Fin Binary6402Cover.boxes_48.size) : Receipt 21 (source68 Binary6402Cover.boxes_48[i]) Binary6402Cover.boxes_48[i] 1 1250000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r68_0_1
  · exact r68_1_1
  · exact r68_2_1
theorem bank68_2 (i : Fin Binary6402Cover.boxes_48.size) : Receipt 21 (source68 Binary6402Cover.boxes_48[i]) Binary6402Cover.boxes_48[i] 2 2500000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r68_0_2
  · exact r68_1_2
  · exact r68_2_2
#print axioms bank68_2
end Binary6402Live
