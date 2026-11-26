import ProximityPrize.SubmissionBinaryLower.Live6402_194
import ProximityPrize.SubmissionBinaryLower.KernelPriceTarget39
open ProximityPrize.SubmissionBinaryLower B6402PricedCell B6402LinearCertificate B6402RectCover B6402PriceCells Binary6402Targets
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace Binary6402Live
def source195 (box : Box) : Array Row := let pair := B6402GridRouting.rows (Native6402Grid.key 195); cell pair.1 pair.2 49 box
def w2971 : Weights := [(2,(360389148672/360389171875)),(3,(720778297344/360389171875)),(6,(1441559344239/5766226750000)),(10,(360389148672/360389171875)),(14,(360389148672/360389171875)),(15,(360389148672/360389171875)),(26,(180194574336/360389171875)),(30,(720778297344/360389171875)),(51,(360389148672/360389171875)),(52,(720778297344/1801945859375)),(54,(720778297344/1801945859375)),(57,(180194574336/1801945859375)),(58,(180194574336/360389171875)),(67,(720778297344/1801945859375)),(78,(720778297344/1801945859375)),(82,(720778297344/1801945859375)),(91,(180194574336/360389171875)),(92,(720778297344/1801945859375))]
def w2972 : Weights := [(5,(140750904953941189649/20300431360000)),(14,(117523766667199/1936000)),(18,(352571300001597/3872000)),(19,(352571300001597/3872000)),(31,(117523766667199/1936000)),(46,(117523766667199/4840000)),(50,(2232951566676781/19360000)),(64,(352571300001597/38720000)),(65,(117523766667199/7744000)),(66,(589773225293701/440000)),(80,(2467999100011179/19360000)),(82,(117523766667199/4840000))]
def w2973 : Weights := [(5,(21107950711005998651/3045064704000)),(14,(17624653106101/290400)),(18,(17624653106101/193600)),(19,(17624653106101/193600)),(31,(17624653106101/290400)),(46,(17624653106101/726000)),(50,(334868409015919/2904000)),(64,(17624653106101/1936000)),(65,(17624653106101/1161600)),(66,(608177964378757/453750)),(80,(123372571742707/968000)),(82,(17624653106101/726000))]
def w2974 : Weights := [(5,(844505429361029958767/60901294080000)),(14,(705142599700417/5808000)),(18,(705142599700417/3872000)),(19,(705142599700417/3872000)),(31,(705142599700417/5808000)),(46,(705142599700417/14520000)),(50,(13397709394307923/58080000)),(64,(705142599700417/38720000)),(65,(705142599700417/23232000)),(66,(38925032852670469/14520000)),(80,(4935998197902919/19360000)),(82,(705142599700417/14520000))]
def w2975 : Weights := [(5,(211102984034088205871/15225323520000)),(14,(176266133752321/1452000)),(18,(176266133752321/968000)),(19,(176266133752321/968000)),(31,(176266133752321/1452000)),(46,(176266133752321/3630000)),(50,(3349056541294099/14520000)),(64,(176266133752321/9680000)),(65,(176266133752321/5808000)),(66,(884641206744257/330000)),(80,(1233862936266247/4840000)),(82,(176266133752321/3630000))]
def prepared856 : Prepared := ⟨plan1268,⟨922597,629146,17993564,17993564,3951802777,3768⟩,(2749551/6250000),(314573/1048576),⟨true,85,4294967296,59,1301,432874,1073423304,4294982370,0,0⟩,target1268,target1269⟩
theorem prepared856_ok : Correct prepared856 := by
  constructor
  · change B6402PriceTarget.values plan1268 (5*(1:ℚ))=target1268
    rw [show 5*(1:ℚ)=5 by norm_num]
    exact target1268_ok
  · change B6402PriceTarget.values plan1268 (1811+(1:ℚ))=target1269
    rw [show 1811+(1:ℚ)=1812 by norm_num,show plan1268=plan1269 from rfl]
    exact target1269_ok
theorem r195_0_1 : Receipt 49 (source195 Binary6402Cover.boxes_195[0]) Binary6402Cover.boxes_195[0] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared856,⟨w2971,w1586,w2972,w2973⟩,by decide +kernel,prepared856_ok,by decide +kernel⟩
def prepared857 : Prepared := ⟨plan1270,⟨922597,629146,17993564,17993564,3951802777,3768⟩,(2749551/6250000),(314573/1048576),⟨true,85,4294967296,59,1301,432874,1073423304,8589964740,0,0⟩,target1270,target1271⟩
theorem prepared857_ok : Correct prepared857 := by
  constructor
  · change B6402PriceTarget.values plan1270 (5*(2:ℚ))=target1270
    rw [show 5*(2:ℚ)=10 by norm_num]
    exact target1270_ok
  · change B6402PriceTarget.values plan1270 (1811+(2:ℚ))=target1271
    rw [show 1811+(2:ℚ)=1813 by norm_num,show plan1270=plan1271 from rfl]
    exact target1271_ok
theorem r195_0_2 : Receipt 49 (source195 Binary6402Cover.boxes_195[0]) Binary6402Cover.boxes_195[0] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared857,⟨w2971,w1586,w2974,w2975⟩,by decide +kernel,prepared857_ok,by decide +kernel⟩
def prepared858 : Prepared := ⟨plan1268,⟨922597,83886,17993564,17993564,3951802777,3768⟩,(2749551/6250000),(1/25),⟨true,85,4294967296,59,1301,432874,1073423304,4294982370,0,0⟩,target1268,target1269⟩
theorem prepared858_ok : Correct prepared858 := by
  constructor
  · change B6402PriceTarget.values plan1268 (5*(1:ℚ))=target1268
    rw [show 5*(1:ℚ)=5 by norm_num]
    exact target1268_ok
  · change B6402PriceTarget.values plan1268 (1811+(1:ℚ))=target1269
    rw [show 1811+(1:ℚ)=1812 by norm_num,show plan1268=plan1269 from rfl]
    exact target1269_ok
theorem r195_1_1 : Receipt 49 (source195 Binary6402Cover.boxes_195[1]) Binary6402Cover.boxes_195[1] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared858,⟨w2971,w1616,w2972,w2973⟩,by decide +kernel,prepared858_ok,by decide +kernel⟩
def prepared859 : Prepared := ⟨plan1270,⟨922597,83886,17993564,17993564,3951802777,3768⟩,(2749551/6250000),(1/25),⟨true,85,4294967296,59,1301,432874,1073423304,8589964740,0,0⟩,target1270,target1271⟩
theorem prepared859_ok : Correct prepared859 := by
  constructor
  · change B6402PriceTarget.values plan1270 (5*(2:ℚ))=target1270
    rw [show 5*(2:ℚ)=10 by norm_num]
    exact target1270_ok
  · change B6402PriceTarget.values plan1270 (1811+(2:ℚ))=target1271
    rw [show 1811+(2:ℚ)=1813 by norm_num,show plan1270=plan1271 from rfl]
    exact target1271_ok
theorem r195_1_2 : Receipt 49 (source195 Binary6402Cover.boxes_195[1]) Binary6402Cover.boxes_195[1] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared859,⟨w2971,w1616,w2974,w2975⟩,by decide +kernel,prepared859_ok,by decide +kernel⟩
def prepared860 : Prepared := ⟨plan1268,⟨922597,10485,17993564,17993564,3951802777,3768⟩,(2749551/6250000),(1/200),⟨true,85,4294967296,59,1301,432874,1073423304,4294982370,0,0⟩,target1268,target1269⟩
theorem prepared860_ok : Correct prepared860 := by
  constructor
  · change B6402PriceTarget.values plan1268 (5*(1:ℚ))=target1268
    rw [show 5*(1:ℚ)=5 by norm_num]
    exact target1268_ok
  · change B6402PriceTarget.values plan1268 (1811+(1:ℚ))=target1269
    rw [show 1811+(1:ℚ)=1812 by norm_num,show plan1268=plan1269 from rfl]
    exact target1269_ok
theorem r195_2_1 : Receipt 49 (source195 Binary6402Cover.boxes_195[2]) Binary6402Cover.boxes_195[2] 1 1250000000000000000 (3/50) := Or.inr ⟨prepared860,⟨w2971,w1616,w2972,w2973⟩,by decide +kernel,prepared860_ok,by decide +kernel⟩
def prepared861 : Prepared := ⟨plan1270,⟨922597,10485,17993564,17993564,3951802777,3768⟩,(2749551/6250000),(1/200),⟨true,85,4294967296,59,1301,432874,1073423304,8589964740,0,0⟩,target1270,target1271⟩
theorem prepared861_ok : Correct prepared861 := by
  constructor
  · change B6402PriceTarget.values plan1270 (5*(2:ℚ))=target1270
    rw [show 5*(2:ℚ)=10 by norm_num]
    exact target1270_ok
  · change B6402PriceTarget.values plan1270 (1811+(2:ℚ))=target1271
    rw [show 1811+(2:ℚ)=1813 by norm_num,show plan1270=plan1271 from rfl]
    exact target1271_ok
theorem r195_2_2 : Receipt 49 (source195 Binary6402Cover.boxes_195[2]) Binary6402Cover.boxes_195[2] 2 2500000000000000000 (3/50) := Or.inr ⟨prepared861,⟨w2971,w1616,w2974,w2975⟩,by decide +kernel,prepared861_ok,by decide +kernel⟩
theorem bank195_1 (i : Fin Binary6402Cover.boxes_195.size) : Receipt 49 (source195 Binary6402Cover.boxes_195[i]) Binary6402Cover.boxes_195[i] 1 1250000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r195_0_1
  · exact r195_1_1
  · exact r195_2_1
theorem bank195_2 (i : Fin Binary6402Cover.boxes_195.size) : Receipt 49 (source195 Binary6402Cover.boxes_195[i]) Binary6402Cover.boxes_195[i] 2 2500000000000000000 (3/50) := by
  change Fin 3 at i
  fin_cases i
  · exact r195_0_2
  · exact r195_1_2
  · exact r195_2_2
#print axioms bank195_2
end Binary6402Live
