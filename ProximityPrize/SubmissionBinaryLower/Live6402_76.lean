import ProximityPrize.SubmissionBinaryLower.Live6402_75
import ProximityPrize.SubmissionBinaryLower.KernelPriceTarget9
open ProximityPrize.SubmissionBinaryLower B6402PricedCell B6402LinearCertificate B6402RectCover B6402PriceCells Binary6402Targets
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace Binary6402Live
def source76 (box : Box) : Array Row := let pair := B6402GridRouting.rows (Native6402Grid.key 76); cell pair.1 pair.2 21 box
def w1433 : Weights := [(0,(124851894031804564/2402984375)),(1,(58682741343289/1210000)),(4,(93638920523853423/2402984375)),(9,(31212973507951141/2402984375)),(16,(2652617158041/110000)),(37,(2652617158041/110000)),(38,(307403161608093/151250)),(40,(2652617158041/13750))]
def w1434 : Weights := [(0,(6809520876345812/131071875)),(1,(29338690933109/605000)),(4,(1702380219086453/43690625)),(9,(1702380219086453/131071875)),(16,(48225278051/2000)),(37,(48225278051/2000)),(38,(2459198365292267/1210000)),(40,(48225278051/250))]
def w1435 : Weights := [(0,(8240225003883142702/79298484375)),(1,(14670685331877/151250)),(4,(4120112501941571351/52865656250)),(9,(4120112501941571351/158596968750)),(16,(116715154922417/2420000)),(37,(116715154922417/2420000)),(38,(9836901168813639/2420000)),(40,(116715154922417/302500))]
def w1436 : Weights := [(0,(8239873411040208094/79298484375)),(1,(117360135041757/1210000)),(4,(4119936705520104047/52865656250)),(9,(4119936705520104047/158596968750)),(16,(116710174935449/2420000)),(37,(116710174935449/2420000)),(38,(9836847432883173/2420000)),(40,(116710174935449/302500))]
def prepared246 : Prepared := ⟨plan288,⟨1475092,629146,11072962,11072962,3686513247,3515⟩,(14067573/20000000),(314573/1048576),⟨true,53,4294967296,55,2069,432106,672272027,4294981358,0,0⟩,target288,target289⟩
theorem prepared246_ok : Correct prepared246 := by
  constructor
  · change B6402PriceTarget.values plan288 (5*(1:ℚ))=target288
    rw [show 5*(1:ℚ)=5 by norm_num]
    exact target288_ok
  · change B6402PriceTarget.values plan288 (1811+(1:ℚ))=target289
    rw [show 1811+(1:ℚ)=1812 by norm_num,show plan288=plan289 from rfl]
    exact target289_ok
theorem r76_0_1 : Receipt 21 (source76 Binary6402Cover.boxes_76[0]) Binary6402Cover.boxes_76[0] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared246,⟨w1367,w1346,w1433,w1434⟩,by decide +kernel,prepared246_ok,by decide +kernel⟩
def prepared247 : Prepared := ⟨plan290,⟨1475092,629146,11072962,11072962,3686513247,3515⟩,(14067573/20000000),(314573/1048576),⟨true,53,4294967296,55,2069,432106,672272027,8589962716,0,0⟩,target290,target291⟩
theorem prepared247_ok : Correct prepared247 := by
  constructor
  · change B6402PriceTarget.values plan290 (5*(2:ℚ))=target290
    rw [show 5*(2:ℚ)=10 by norm_num]
    exact target290_ok
  · change B6402PriceTarget.values plan290 (1811+(2:ℚ))=target291
    rw [show 1811+(2:ℚ)=1813 by norm_num,show plan290=plan291 from rfl]
    exact target291_ok
theorem r76_0_2 : Receipt 21 (source76 Binary6402Cover.boxes_76[0]) Binary6402Cover.boxes_76[0] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared247,⟨w1367,w1346,w1435,w1436⟩,by decide +kernel,prepared247_ok,by decide +kernel⟩
def prepared248 : Prepared := ⟨plan288,⟨1475092,83886,11072962,11072962,3686513247,3515⟩,(14067573/20000000),(1/25),⟨true,53,4294967296,55,2069,432106,672272027,4294981358,0,0⟩,target288,target289⟩
theorem prepared248_ok : Correct prepared248 := by
  constructor
  · change B6402PriceTarget.values plan288 (5*(1:ℚ))=target288
    rw [show 5*(1:ℚ)=5 by norm_num]
    exact target288_ok
  · change B6402PriceTarget.values plan288 (1811+(1:ℚ))=target289
    rw [show 1811+(1:ℚ)=1812 by norm_num,show plan288=plan289 from rfl]
    exact target289_ok
theorem r76_1_1 : Receipt 21 (source76 Binary6402Cover.boxes_76[1]) Binary6402Cover.boxes_76[1] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared248,⟨w1367,w1372,w1433,w1434⟩,by decide +kernel,prepared248_ok,by decide +kernel⟩
def prepared249 : Prepared := ⟨plan290,⟨1475092,83886,11072962,11072962,3686513247,3515⟩,(14067573/20000000),(1/25),⟨true,53,4294967296,55,2069,432106,672272027,8589962716,0,0⟩,target290,target291⟩
theorem prepared249_ok : Correct prepared249 := by
  constructor
  · change B6402PriceTarget.values plan290 (5*(2:ℚ))=target290
    rw [show 5*(2:ℚ)=10 by norm_num]
    exact target290_ok
  · change B6402PriceTarget.values plan290 (1811+(2:ℚ))=target291
    rw [show 1811+(2:ℚ)=1813 by norm_num,show plan290=plan291 from rfl]
    exact target291_ok
theorem r76_1_2 : Receipt 21 (source76 Binary6402Cover.boxes_76[1]) Binary6402Cover.boxes_76[1] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared249,⟨w1367,w1372,w1435,w1436⟩,by decide +kernel,prepared249_ok,by decide +kernel⟩
def prepared250 : Prepared := ⟨plan288,⟨1475092,10485,11072962,11072962,3686513247,3515⟩,(14067573/20000000),(1/200),⟨true,53,4294967296,55,2069,432106,672272027,4294981358,0,0⟩,target288,target289⟩
theorem prepared250_ok : Correct prepared250 := by
  constructor
  · change B6402PriceTarget.values plan288 (5*(1:ℚ))=target288
    rw [show 5*(1:ℚ)=5 by norm_num]
    exact target288_ok
  · change B6402PriceTarget.values plan288 (1811+(1:ℚ))=target289
    rw [show 1811+(1:ℚ)=1812 by norm_num,show plan288=plan289 from rfl]
    exact target289_ok
theorem r76_2_1 : Receipt 21 (source76 Binary6402Cover.boxes_76[2]) Binary6402Cover.boxes_76[2] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared250,⟨w1367,w1372,w1433,w1434⟩,by decide +kernel,prepared250_ok,by decide +kernel⟩
def prepared251 : Prepared := ⟨plan290,⟨1475092,10485,11072962,11072962,3686513247,3515⟩,(14067573/20000000),(1/200),⟨true,53,4294967296,55,2069,432106,672272027,8589962716,0,0⟩,target290,target291⟩
theorem prepared251_ok : Correct prepared251 := by
  constructor
  · change B6402PriceTarget.values plan290 (5*(2:ℚ))=target290
    rw [show 5*(2:ℚ)=10 by norm_num]
    exact target290_ok
  · change B6402PriceTarget.values plan290 (1811+(2:ℚ))=target291
    rw [show 1811+(2:ℚ)=1813 by norm_num,show plan290=plan291 from rfl]
    exact target291_ok
theorem r76_2_2 : Receipt 21 (source76 Binary6402Cover.boxes_76[2]) Binary6402Cover.boxes_76[2] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared251,⟨w1367,w1372,w1435,w1436⟩,by decide +kernel,prepared251_ok,by decide +kernel⟩
theorem bank76_1 (i : Fin Binary6402Cover.boxes_76.size) : Receipt 21 (source76 Binary6402Cover.boxes_76[i]) Binary6402Cover.boxes_76[i] 1 1250000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r76_0_1
  · exact r76_1_1
  · exact r76_2_1
theorem bank76_2 (i : Fin Binary6402Cover.boxes_76.size) : Receipt 21 (source76 Binary6402Cover.boxes_76[i]) Binary6402Cover.boxes_76[i] 2 2500000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r76_0_2
  · exact r76_1_2
  · exact r76_2_2
#print axioms bank76_2
end Binary6402Live
