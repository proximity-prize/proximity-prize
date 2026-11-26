import ProximityPrize.SubmissionBinaryLower.Live6402_47
import ProximityPrize.SubmissionBinaryLower.KernelPriceTarget9
open ProximityPrize.SubmissionBinaryLower B6402PricedCell B6402LinearCertificate B6402RectCover B6402PriceCells Binary6402Targets
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace Binary6402Live
def source48 (box : Box) : Array Row := let pair := B6402GridRouting.rows (Native6402Grid.key 48); cell pair.1 pair.2 21 box
def w1008 : Weights := [(40,(999937/2000000)),(46,(999937/2000000))]
def w1009 : Weights := [(0,(124851894031804564/2402984375)),(1,(58682741343289/1210000)),(4,(93638920523853423/2402984375)),(9,(31212973507951141/2402984375)),(16,(2652617158041/110000)),(35,(2652617158041/110000)),(36,(307403161608093/151250)),(38,(2652617158041/13750))]
def w1010 : Weights := [(0,(6809520876345812/131071875)),(1,(29338690933109/605000)),(4,(1702380219086453/43690625)),(9,(1702380219086453/131071875)),(16,(48225278051/2000)),(35,(48225278051/2000)),(36,(2459198365292267/1210000)),(38,(48225278051/250))]
def w1011 : Weights := [(0,(8240225003883142702/79298484375)),(1,(14670685331877/151250)),(4,(4120112501941571351/52865656250)),(9,(4120112501941571351/158596968750)),(16,(116715154922417/2420000)),(35,(116715154922417/2420000)),(36,(9836901168813639/2420000)),(38,(116715154922417/302500))]
def w1012 : Weights := [(0,(8239873411040208094/79298484375)),(1,(117360135041757/1210000)),(4,(4119936705520104047/52865656250)),(9,(4119936705520104047/158596968750)),(16,(116710174935449/2420000)),(35,(116710174935449/2420000)),(36,(9836847432883173/2420000)),(38,(116710174935449/302500))]
def prepared148 : Prepared := ⟨plan288,⟨41941,629146,11072962,11072962,3686513247,3515⟩,(999937/50000000),(314573/1048576),⟨true,53,4294967296,55,2069,432106,672272027,4294981358,0,0⟩,target288,target289⟩
theorem prepared148_ok : Correct prepared148 := by
  constructor
  · change B6402PriceTarget.values plan288 (5*(1:ℚ))=target288
    rw [show 5*(1:ℚ)=5 by norm_num]
    exact target288_ok
  · change B6402PriceTarget.values plan288 (1811+(1:ℚ))=target289
    rw [show 1811+(1:ℚ)=1812 by norm_num,show plan288=plan289 from rfl]
    exact target289_ok
theorem r48_0_1 : Receipt 21 (source48 Binary6402Cover.boxes_48[0]) Binary6402Cover.boxes_48[0] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared148,⟨w1008,w247,w1009,w1010⟩,by decide +kernel,prepared148_ok,by decide +kernel⟩
def prepared149 : Prepared := ⟨plan290,⟨41941,629146,11072962,11072962,3686513247,3515⟩,(999937/50000000),(314573/1048576),⟨true,53,4294967296,55,2069,432106,672272027,8589962716,0,0⟩,target290,target291⟩
theorem prepared149_ok : Correct prepared149 := by
  constructor
  · change B6402PriceTarget.values plan290 (5*(2:ℚ))=target290
    rw [show 5*(2:ℚ)=10 by norm_num]
    exact target290_ok
  · change B6402PriceTarget.values plan290 (1811+(2:ℚ))=target291
    rw [show 1811+(2:ℚ)=1813 by norm_num,show plan290=plan291 from rfl]
    exact target291_ok
theorem r48_0_2 : Receipt 21 (source48 Binary6402Cover.boxes_48[0]) Binary6402Cover.boxes_48[0] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared149,⟨w1008,w247,w1011,w1012⟩,by decide +kernel,prepared149_ok,by decide +kernel⟩
def w1013 : Weights := [(1,(8191483904/16382984375)),(2,(24574451712/16382984375)),(3,(8191483904/3276596875)),(6,(125821072773/167761760000)),(8,(32765935616/16382984375)),(10,(8191483904/16382984375)),(36,(8191483904/16382984375))]
def prepared150 : Prepared := ⟨plan288,⟨41941,83886,11072962,11072962,3686513247,3515⟩,(999937/50000000),(1/25),⟨true,53,4294967296,55,2069,432106,672272027,4294981358,0,0⟩,target288,target289⟩
theorem prepared150_ok : Correct prepared150 := by
  constructor
  · change B6402PriceTarget.values plan288 (5*(1:ℚ))=target288
    rw [show 5*(1:ℚ)=5 by norm_num]
    exact target288_ok
  · change B6402PriceTarget.values plan288 (1811+(1:ℚ))=target289
    rw [show 1811+(1:ℚ)=1812 by norm_num,show plan288=plan289 from rfl]
    exact target289_ok
theorem r48_1_1 : Receipt 21 (source48 Binary6402Cover.boxes_48[1]) Binary6402Cover.boxes_48[1] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared150,⟨w1013,w253,w1009,w1010⟩,by decide +kernel,prepared150_ok,by decide +kernel⟩
def prepared151 : Prepared := ⟨plan290,⟨41941,83886,11072962,11072962,3686513247,3515⟩,(999937/50000000),(1/25),⟨true,53,4294967296,55,2069,432106,672272027,8589962716,0,0⟩,target290,target291⟩
theorem prepared151_ok : Correct prepared151 := by
  constructor
  · change B6402PriceTarget.values plan290 (5*(2:ℚ))=target290
    rw [show 5*(2:ℚ)=10 by norm_num]
    exact target290_ok
  · change B6402PriceTarget.values plan290 (1811+(2:ℚ))=target291
    rw [show 1811+(2:ℚ)=1813 by norm_num,show plan290=plan291 from rfl]
    exact target291_ok
theorem r48_1_2 : Receipt 21 (source48 Binary6402Cover.boxes_48[1]) Binary6402Cover.boxes_48[1] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared151,⟨w1013,w253,w1011,w1012⟩,by decide +kernel,prepared151_ok,by decide +kernel⟩
def prepared152 : Prepared := ⟨plan288,⟨41941,10485,11072962,11072962,3686513247,3515⟩,(999937/50000000),(1/200),⟨true,53,4294967296,55,2069,432106,672272027,4294981358,0,0⟩,target288,target289⟩
theorem prepared152_ok : Correct prepared152 := by
  constructor
  · change B6402PriceTarget.values plan288 (5*(1:ℚ))=target288
    rw [show 5*(1:ℚ)=5 by norm_num]
    exact target288_ok
  · change B6402PriceTarget.values plan288 (1811+(1:ℚ))=target289
    rw [show 1811+(1:ℚ)=1812 by norm_num,show plan288=plan289 from rfl]
    exact target289_ok
theorem r48_2_1 : Receipt 21 (source48 Binary6402Cover.boxes_48[2]) Binary6402Cover.boxes_48[2] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared152,⟨w1013,w253,w1009,w1010⟩,by decide +kernel,prepared152_ok,by decide +kernel⟩
def prepared153 : Prepared := ⟨plan290,⟨41941,10485,11072962,11072962,3686513247,3515⟩,(999937/50000000),(1/200),⟨true,53,4294967296,55,2069,432106,672272027,8589962716,0,0⟩,target290,target291⟩
theorem prepared153_ok : Correct prepared153 := by
  constructor
  · change B6402PriceTarget.values plan290 (5*(2:ℚ))=target290
    rw [show 5*(2:ℚ)=10 by norm_num]
    exact target290_ok
  · change B6402PriceTarget.values plan290 (1811+(2:ℚ))=target291
    rw [show 1811+(2:ℚ)=1813 by norm_num,show plan290=plan291 from rfl]
    exact target291_ok
theorem r48_2_2 : Receipt 21 (source48 Binary6402Cover.boxes_48[2]) Binary6402Cover.boxes_48[2] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared153,⟨w1013,w253,w1011,w1012⟩,by decide +kernel,prepared153_ok,by decide +kernel⟩
theorem bank48_1 (i : Fin Binary6402Cover.boxes_48.size) : Receipt 21 (source48 Binary6402Cover.boxes_48[i]) Binary6402Cover.boxes_48[i] 1 1250000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r48_0_1
  · exact r48_1_1
  · exact r48_2_1
theorem bank48_2 (i : Fin Binary6402Cover.boxes_48.size) : Receipt 21 (source48 Binary6402Cover.boxes_48[i]) Binary6402Cover.boxes_48[i] 2 2500000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r48_0_2
  · exact r48_1_2
  · exact r48_2_2
#print axioms bank48_2
end Binary6402Live
