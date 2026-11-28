import ProximityPrize.SubmissionLower.R6970PhysicalRequestCompact
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.Bundle6970_fa0707633ba569a9
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks31
import ProximityPrize.SubmissionLower.Bundle6970_c51a423b59d0dd6b
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks47
import ProximityPrize.SubmissionLower.Bundle6970_6ed322075960e0ab
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks67
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks73
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks41
import ProximityPrize.SubmissionLower.Bundle6970_fa78e5af1890b063
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks63

section Pack_R6970Height2313CommonSources18

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1434 : Request := ⟨⟨⟨1438,2006,436,56688⟩,89880792924160,446854153866⟩,32,5,1,643299,1⟩

theorem rank1434 : P3_7_1.BankOK src1434.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1438_2006_436 56688

theorem width1434 : Lower6960.HelperSource.WidthGuard src1434.bank 179730 2308 src1434.reserve := requestWidth (by decide)

def ends1434 : List ℕ := [2308, 2309, 2313]

theorem inside1434 : Research6966.TerminalBanks.inside src1434.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1434 : Cover (Triangular src1434) 2313 2308 ends1434 := triangleCover (by decide +kernel)

def src1435 : Request := ⟨⟨⟨2100,2913,645,57075⟩,282396798484480,2013318131288⟩,40,5,1,643299,1⟩

theorem rank1435 : P3_7_1.BankOK src1435.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2100_2913_645 57075

theorem width1435 : Lower6960.HelperSource.WidthGuard src1435.bank 179730 2308 src1435.reserve := requestWidth (by decide)

def ends1435 : List ℕ := [2308, 2309, 2313]

theorem inside1435 : Research6966.TerminalBanks.inside src1435.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1435 : Cover (Triangular src1435) 2313 2308 ends1435 := triangleCover (by decide +kernel)

def src1436 : Request := ⟨⟨⟨2301,3194,710,63926⟩,372721737007104,2918134856643⟩,46,5,1,643299,1⟩

theorem rank1436 : P3_7_1.BankOK src1436.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2301_3194_710 63926

theorem width1436 : Lower6960.HelperSource.WidthGuard src1436.bank 179730 2308 src1436.reserve := requestWidth (by decide)

def ends1436 : List ℕ := [2308, 2309, 2313]

theorem inside1436 : Research6966.TerminalBanks.inside src1436.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1436 : Cover (Triangular src1436) 2313 2308 ends1436 := triangleCover (by decide +kernel)

def src1437 : Request := ⟨⟨⟨2304,3207,710,530820⟩,373810967347200,2956554353577⟩,85,5,1,643789,1⟩

theorem rank1437 : P3_7_1.BankOK src1437.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2304_3207_710 530820

theorem width1437 : Lower6960.HelperSource.WidthGuard src1437.bank 179730 2308 src1437.reserve := requestWidth (by decide)

def ends1437 : List ℕ := [2308, 2309, 2313]

theorem inside1437 : Research6966.TerminalBanks.inside src1437.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1437 : Cover (Triangular src1437) 2313 2308 ends1437 := triangleCover (by decide +kernel)

def src1438 : Request := ⟨⟨⟨8300,11569,2514,235440⟩,17222821613404160,492553799321867⟩,190,5,1,643299,1⟩

theorem rank1438 : P3_7_1.BankOK src1438.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8300_11569_2514 235440

theorem width1438 : Lower6960.HelperSource.WidthGuard src1438.bank 179730 2308 src1438.reserve := requestWidth (by decide)

def ends1438 : List ℕ := [2308, 2309, 2313]




theorem cover1438 : Cover (Triangular src1438) 2313 2308 ends1438 := triangleCover (by decide +kernel)

def src1439 : Request := ⟨⟨⟨395,550,120,12206⟩,1881913425920,2560837984⟩,0,5,1,643299,2⟩

theorem rank1439 : P3_7_1.BankOK src1439.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_395_550_120 12206

theorem width1439 : Lower6960.HelperSource.WidthGuard src1439.bank 179730 2308 src1439.reserve := requestWidth (by decide)

def ends1439 : List ℕ := [2308, 2309, 2313]

theorem inside1439 : Research6966.TerminalBanks.inside src1439.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1439 : Cover (Triangular src1439) 2313 2308 ends1439 := triangleCover (by decide +kernel)

def src144 : Request := ⟨⟨⟨2913,4044,900,31222⟩,756649935765504,7501830777122⟩,65,2,1,295365,41⟩

theorem rank144 : P3_7_1.BankOK src144.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2913_4044_900 31222

theorem width144 : Lower6960.HelperSource.WidthGuard src144.bank 179730 2308 src144.reserve := requestWidth (by decide)

def ends144 : List ℕ := [2308, 2309, 2313]

theorem inside144 : Research6966.TerminalBanks.inside src144.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover144 : Cover (Triangular src144) 2313 2308 ends144 := triangleCover (by decide +kernel)

def src1440 : Request := ⟨⟨⟨401,558,123,13899⟩,1982954733568,2734096379⟩,1,5,1,643299,2⟩

theorem rank1440 : P3_7_1.BankOK src1440.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_401_558_123 13899

theorem width1440 : Lower6960.HelperSource.WidthGuard src1440.bank 179730 2308 src1440.reserve := requestWidth (by decide)

def ends1440 : List ℕ := [2308, 2309, 2313]

theorem inside1440 : Research6966.TerminalBanks.inside src1440.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1440 : Cover (Triangular src1440) 2313 2308 ends1440 := triangleCover (by decide +kernel)

def src1441 : Request := ⟨⟨⟨556,773,169,13817⟩,5232427008000,9964025195⟩,2,5,1,643299,2⟩

theorem rank1441 : P3_7_1.BankOK src1441.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_773_169 13817

theorem width1441 : Lower6960.HelperSource.WidthGuard src1441.bank 179730 2308 src1441.reserve := requestWidth (by decide)

def ends1441 : List ℕ := [2308, 2309, 2313]

theorem inside1441 : Research6966.TerminalBanks.inside src1441.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1441 : Cover (Triangular src1441) 2313 2308 ends1441 := triangleCover (by decide +kernel)

def src1442 : Request := ⟨⟨⟨560,781,169,15636⟩,5316921262080,10299257375⟩,3,5,1,643299,2⟩

theorem rank1442 : P3_7_1.BankOK src1442.bank := by
  simpa only [src1442, _root_.Research6969.TransitionBanks.bank155] using _root_.Research6969.TransitionBanks.rank155 15636

theorem width1442 : Lower6960.HelperSource.WidthGuard src1442.bank 179730 2308 src1442.reserve := requestWidth (by decide)

def ends1442 : List ℕ := [2308, 2313]

theorem inside1442 : Research6966.TerminalBanks.inside src1442.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1442 : Cover (Triangular src1442) 2313 2308 ends1442 := triangleCover (by decide +kernel)

def src1443 : Request := ⟨⟨⟨560,781,169,17590⟩,5316921262080,10299257375⟩,4,5,1,643299,2⟩

theorem rank1443 : P3_7_1.BankOK src1443.bank := by
  simpa only [src1443, _root_.Research6969.TransitionBanks.bank155] using _root_.Research6969.TransitionBanks.rank155 17590

theorem width1443 : Lower6960.HelperSource.WidthGuard src1443.bank 179730 2308 src1443.reserve := requestWidth (by decide)

def ends1443 : List ℕ := [2313]

theorem inside1443 : Research6966.TerminalBanks.inside src1443.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1443 : Cover (Triangular src1443) 2313 2308 ends1443 := triangleCover (by decide +kernel)

def src1444 : Request := ⟨⟨⟨690,961,208,22257⟩,9921631092736,23566853761⟩,8,5,1,643299,2⟩

theorem rank1444 : P3_7_1.BankOK src1444.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_690_961_208 22257

theorem width1444 : Lower6960.HelperSource.WidthGuard src1444.bank 179730 2308 src1444.reserve := requestWidth (by decide)

def ends1444 : List ℕ := [2308, 2309, 2313]

theorem inside1444 : Research6966.TerminalBanks.inside src1444.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1444 : Cover (Triangular src1444) 2313 2308 ends1444 := triangleCover (by decide +kernel)

def src1445 : Request := ⟨⟨⟨993,1379,307,22308⟩,30080867762176,101862721867⟩,10,5,1,643299,2⟩

theorem rank1445 : P3_7_1.BankOK src1445.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_993_1379_307 22308

theorem width1445 : Lower6960.HelperSource.WidthGuard src1445.bank 179730 2308 src1445.reserve := requestWidth (by decide)

def ends1445 : List ℕ := [2308, 2309, 2313]

theorem inside1445 : Research6966.TerminalBanks.inside src1445.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1445 : Cover (Triangular src1445) 2313 2308 ends1445 := triangleCover (by decide +kernel)

def src1446 : Request := ⟨⟨⟨1450,2022,445,40111⟩,92998964346880,465769321795⟩,25,5,1,643299,2⟩

theorem rank1446 : P3_7_1.BankOK src1446.bank := by
  simpa only [src1446, _root_.Research6969.TransitionBanks.bank233] using _root_.Research6969.TransitionBanks.rank233 40111

theorem width1446 : Lower6960.HelperSource.WidthGuard src1446.bank 179730 2308 src1446.reserve := requestWidth (by decide)

def ends1446 : List ℕ := [2308, 2313]

theorem inside1446 : Research6966.TerminalBanks.inside src1446.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1446 : Cover (Triangular src1446) 2313 2308 ends1446 := triangleCover (by decide +kernel)

def src1447 : Request := ⟨⟨⟨2100,2929,645,57109⟩,282396798484480,2049139102608⟩,40,5,1,643299,2⟩

theorem rank1447 : P3_7_1.BankOK src1447.bank := by
  simpa only [src1447, _root_.Research6969.TransitionBanks.bank249] using _root_.Research6969.TransitionBanks.rank249 57109

theorem width1447 : Lower6960.HelperSource.WidthGuard src1447.bank 179730 2308 src1447.reserve := requestWidth (by decide)

def ends1447 : List ℕ := [2308, 2313]

theorem inside1447 : Research6966.TerminalBanks.inside src1447.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1447 : Cover (Triangular src1447) 2313 2308 ends1447 := triangleCover (by decide +kernel)

def src1448 : Request := ⟨⟨⟨2301,3194,710,62261⟩,372721737007104,2918134856643⟩,46,5,1,643299,2⟩

theorem rank1448 : P3_7_1.BankOK src1448.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2301_3194_710 62261

theorem width1448 : Lower6960.HelperSource.WidthGuard src1448.bank 179730 2308 src1448.reserve := requestWidth (by decide)

def ends1448 : List ℕ := [2308, 2309, 2313]

theorem inside1448 : Research6966.TerminalBanks.inside src1448.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1448 : Cover (Triangular src1448) 2313 2308 ends1448 := triangleCover (by decide +kernel)

def src1449 : Request := ⟨⟨⟨2100,2928,645,146522⟩,282396798484480,2046887686018⟩,65,5,1,643299,2⟩

theorem rank1449 : P3_7_1.BankOK src1449.bank := by
  simpa only [src1449, _root_.Research6969.TransitionBanks.bank247] using _root_.Research6969.TransitionBanks.rank247 146522

theorem width1449 : Lower6960.HelperSource.WidthGuard src1449.bank 179730 2308 src1449.reserve := requestWidth (by decide)

def ends1449 : List ℕ := [2308, 2313]

theorem inside1449 : Research6966.TerminalBanks.inside src1449.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1449 : Cover (Triangular src1449) 2313 2308 ends1449 := triangleCover (by decide +kernel)

def src145 : Request := ⟨⟨⟨400,558,123,4817⟩,1971918995456,2734096379⟩,0,2,1,296085,41⟩

theorem rank145 : P3_7_1.BankOK src145.bank := by
  simpa only [src145, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 4817

theorem width145 : Lower6960.HelperSource.WidthGuard src145.bank 179730 2308 src145.reserve := requestWidth (by decide)

def ends145 : List ℕ := [2308, 2313]

theorem inside145 : Research6966.TerminalBanks.inside src145.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover145 : Cover (Triangular src145) 2313 2308 ends145 := triangleCover (by decide +kernel)

def src1450 : Request := ⟨⟨⟨2346,3271,716,475797⟩,391734418997248,3171444219448⟩,85,5,1,643789,2⟩

theorem rank1450 : P3_7_1.BankOK src1450.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2346_3271_716 475797

theorem width1450 : Lower6960.HelperSource.WidthGuard src1450.bank 179730 2308 src1450.reserve := requestWidth (by decide)

def ends1450 : List ℕ := [2308, 2313]

theorem inside1450 : Research6966.TerminalBanks.inside src1450.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1450 : Cover (Triangular src1450) 2313 2308 ends1450 := triangleCover (by decide +kernel)

def src1451 : Request := ⟨⟨⟨5726,7943,1758,131503⟩,5714887980351488,111059997495708⟩,110,5,1,643299,2⟩

theorem rank1451 : P3_7_1.BankOK src1451.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5726_7943_1758 131503

theorem width1451 : Lower6960.HelperSource.WidthGuard src1451.bank 179730 2308 src1451.reserve := requestWidth (by decide)

def ends1451 : List ℕ := [2308, 2309, 2313]




theorem cover1451 : Cover (Triangular src1451) 2313 2308 ends1451 := triangleCover (by decide +kernel)

def src1452 : Request := ⟨⟨⟨470,655,144,10983⟩,3184589537280,5168862572⟩,0,5,1,643299,4⟩

theorem rank1452 : P3_7_1.BankOK src1452.bank := by
  simpa only [src1452, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 10983

theorem width1452 : Lower6960.HelperSource.WidthGuard src1452.bank 179730 2308 src1452.reserve := requestWidth (by decide)

def ends1452 : List ℕ := [2309, 2313]

theorem inside1452 : Research6966.TerminalBanks.inside src1452.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1452 : Cover (Triangular src1452) 2313 2308 ends1452 := triangleCover (by decide +kernel)

def src1453 : Request := ⟨⟨⟨470,655,144,12355⟩,3184589537280,5168862572⟩,1,5,1,643299,4⟩

theorem rank1453 : P3_7_1.BankOK src1453.bank := by
  simpa only [src1453, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 12355

theorem width1453 : Lower6960.HelperSource.WidthGuard src1453.bank 179730 2308 src1453.reserve := requestWidth (by decide)

def ends1453 : List ℕ := [2313]

theorem inside1453 : Research6966.TerminalBanks.inside src1453.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1453 : Cover (Triangular src1453) 2313 2308 ends1453 := triangleCover (by decide +kernel)

def src1454 : Request := ⟨⟨⟨470,655,144,13899⟩,3184589537280,5168862572⟩,2,5,1,643299,4⟩

theorem rank1454 : P3_7_1.BankOK src1454.bank := by
  simpa only [src1454, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 13899

theorem width1454 : Lower6960.HelperSource.WidthGuard src1454.bank 179730 2308 src1454.reserve := requestWidth (by decide)

def ends1454 : List ℕ := [2313]

theorem inside1454 : Research6966.TerminalBanks.inside src1454.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1454 : Cover (Triangular src1454) 2313 2308 ends1454 := triangleCover (by decide +kernel)

def src1455 : Request := ⟨⟨⟨470,655,144,15636⟩,3184589537280,5168862572⟩,3,5,1,643299,4⟩

theorem rank1455 : P3_7_1.BankOK src1455.bank := by
  simpa only [src1455, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 15636

theorem width1455 : Lower6960.HelperSource.WidthGuard src1455.bank 179730 2308 src1455.reserve := requestWidth (by decide)

def ends1455 : List ℕ := [2308, 2309, 2313]

theorem inside1455 : Research6966.TerminalBanks.inside src1455.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1455 : Cover (Triangular src1455) 2313 2308 ends1455 := triangleCover (by decide +kernel)

def src1456 : Request := ⟨⟨⟨471,655,144,17990⟩,3199755878400,5168862572⟩,4,5,1,643789,4⟩

theorem rank1456 : P3_7_1.BankOK src1456.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_144 17990

theorem width1456 : Lower6960.HelperSource.WidthGuard src1456.bank 179730 2308 src1456.reserve := requestWidth (by decide)

def ends1456 : List ℕ := [2308, 2309, 2313]

theorem inside1456 : Research6966.TerminalBanks.inside src1456.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1456 : Cover (Triangular src1456) 2313 2308 ends1456 := triangleCover (by decide +kernel)

def src1457 : Request := ⟨⟨⟨693,962,214,19959⟩,10236333916160,24173060093⟩,8,5,1,643299,4⟩

theorem rank1457 : P3_7_1.BankOK src1457.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_693_962_214 19959

theorem width1457 : Lower6960.HelperSource.WidthGuard src1457.bank 179730 2308 src1457.reserve := requestWidth (by decide)

def ends1457 : List ℕ := [2308, 2309, 2313]

theorem inside1457 : Research6966.TerminalBanks.inside src1457.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1457 : Cover (Triangular src1457) 2313 2308 ends1457 := triangleCover (by decide +kernel)

def src1458 : Request := ⟨⟨⟨1200,1674,368,28173⟩,52718727069696,218807905514⟩,16,5,1,643299,4⟩

theorem rank1458 : P3_7_1.BankOK src1458.bank := by
  simpa only [src1458, _root_.Research6969.TransitionBanks.bank228] using _root_.Research6969.TransitionBanks.rank228 28173

theorem width1458 : Lower6960.HelperSource.WidthGuard src1458.bank 179730 2308 src1458.reserve := requestWidth (by decide)

def ends1458 : List ℕ := [2313]

theorem inside1458 : Research6966.TerminalBanks.inside src1458.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1458 : Cover (Triangular src1458) 2313 2308 ends1458 := triangleCover (by decide +kernel)

def src1459 : Request := ⟨⟨⟨1750,2441,537,45124⟩,163381988556800,988269431527⟩,32,5,1,643299,4⟩

theorem rank1459 : P3_7_1.BankOK src1459.bank := by
  simpa only [src1459, _root_.Research6969.TransitionBanks.bank242] using _root_.Research6969.TransitionBanks.rank242 45124

theorem width1459 : Lower6960.HelperSource.WidthGuard src1459.bank 179730 2308 src1459.reserve := requestWidth (by decide)

def ends1459 : List ℕ := [2308, 2309, 2313]

theorem inside1459 : Research6966.TerminalBanks.inside src1459.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1459 : Cover (Triangular src1459) 2313 2308 ends1459 := triangleCover (by decide +kernel)

def src146 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,1,2,1,296085,41⟩

theorem rank146 : P3_7_1.BankOK src146.bank := by
  simpa only [src146, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 4817

theorem width146 : Lower6960.HelperSource.WidthGuard src146.bank 179730 2308 src146.reserve := requestWidth (by decide)

def ends146 : List ℕ := [2313]

theorem inside146 : Research6966.TerminalBanks.inside src146.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover146 : Cover (Triangular src146) 2313 2308 ends146 := triangleCover (by decide +kernel)

def src1460 : Request := ⟨⟨⟨2808,3897,870,80038⟩,679228649242624,6485340504589⟩,64,5,1,643299,4⟩

theorem rank1460 : P3_7_1.BankOK src1460.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2808_3897_870 80038

theorem width1460 : Lower6960.HelperSource.WidthGuard src1460.bank 179730 2308 src1460.reserve := requestWidth (by decide)

def ends1460 : List ℕ := [2308, 2309, 2313]

theorem inside1460 : Research6966.TerminalBanks.inside src1460.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1460 : Cover (Triangular src1460) 2313 2308 ends1460 := triangleCover (by decide +kernel)

def src1461 : Request := ⟨⟨⟨2311,3207,714,475797⟩,377966061158400,2969491350551⟩,85,5,1,643789,4⟩

theorem rank1461 : P3_7_1.BankOK src1461.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2311_3207_714 475797

theorem width1461 : Lower6960.HelperSource.WidthGuard src1461.bank 179730 2308 src1461.reserve := requestWidth (by decide)

def ends1461 : List ℕ := [2308, 2309, 2313]

theorem inside1461 : Research6966.TerminalBanks.inside src1461.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1461 : Cover (Triangular src1461) 2313 2308 ends1461 := triangleCover (by decide +kernel)

def src1462 : Request := ⟨⟨⟨3896,5434,1189,102424⟩,1792666704281600,24123363874836⟩,85,5,1,643299,4⟩

theorem rank1462 : P3_7_1.BankOK src1462.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3896_5434_1189 102424

theorem width1462 : Lower6960.HelperSource.WidthGuard src1462.bank 179730 2308 src1462.reserve := requestWidth (by decide)

def ends1462 : List ℕ := [2308, 2309, 2313]




theorem cover1462 : Cover (Triangular src1462) 2313 2308 ends1462 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources18

section Pack_R6970Height2313CommonSources46

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src566 : Request := ⟨⟨⟨2091,2918,622,180316⟩,272075810406400,1967992842119⟩,3,2,1,308251,7⟩

theorem rank566 : P3_7_1.BankOK src566.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2091_2918_622 180316

theorem width566 : Lower6960.HelperSource.WidthGuard src566.bank 179730 2308 src566.reserve := requestWidth (by decide)

def ends566 : List ℕ := [2308, 2309, 2313]

theorem inside566 : Research6966.TerminalBanks.inside src566.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover566 : Cover (Triangular src566) 2313 2308 ends566 := triangleCover (by decide +kernel)

def src567 : Request := ⟨⟨⟨1759,2454,527,240159⟩,162923095785472,990695907382⟩,4,2,1,308251,7⟩

theorem rank567 : P3_7_1.BankOK src567.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1759_2454_527 240159

theorem width567 : Lower6960.HelperSource.WidthGuard src567.bank 179730 2308 src567.reserve := requestWidth (by decide)

def ends567 : List ℕ := [2308, 2309, 2313]

theorem inside567 : Research6966.TerminalBanks.inside src567.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover567 : Cover (Triangular src567) 2313 2308 ends567 := triangleCover (by decide +kernel)

def src568 : Request := ⟨⟨⟨2099,2929,630,195814⟩,277094667386880,2011923818496⟩,4,2,1,308251,7⟩

theorem rank568 : P3_7_1.BankOK src568.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2099_2929_630 195814

theorem width568 : Lower6960.HelperSource.WidthGuard src568.bank 179730 2308 src568.reserve := requestWidth (by decide)

def ends568 : List ℕ := [2308, 2309, 2313]

theorem inside568 : Research6966.TerminalBanks.inside src568.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover568 : Cover (Triangular src568) 2313 2308 ends568 := triangleCover (by decide +kernel)

def src569 : Request := ⟨⟨⟨2601,3628,783,254697⟩,528209871372288,4745819470168⟩,8,2,1,308251,7⟩

theorem rank569 : P3_7_1.BankOK src569.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2601_3628_783 254697

theorem width569 : Lower6960.HelperSource.WidthGuard src569.bank 179730 2308 src569.reserve := requestWidth (by decide)

def ends569 : List ℕ := [2308, 2309, 2313]

theorem inside569 : Research6966.TerminalBanks.inside src569.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover569 : Cover (Triangular src569) 2313 2308 ends569 := triangleCover (by decide +kernel)

def src57 : Request := ⟨⟨⟨2777,3852,866,28697⟩,660231795507200,6224865038545⟩,73,2,1,257319,46⟩

theorem rank57 : P3_7_1.BankOK src57.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2777_3852_866 28697

theorem width57 : Lower6960.HelperSource.WidthGuard src57.bank 179730 2308 src57.reserve := requestWidth (by decide)

def ends57 : List ℕ := [2308, 2309, 2313]

theorem inside57 : Research6966.TerminalBanks.inside src57.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover57 : Cover (Triangular src57) 2313 2308 ends57 := triangleCover (by decide +kernel)

def src570 : Request := ⟨⟨⟨3200,4465,955,269644⟩,976818203525120,10806484661095⟩,10,2,1,308251,7⟩

theorem rank570 : P3_7_1.BankOK src570.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3200_4465_955 269644

theorem width570 : Lower6960.HelperSource.WidthGuard src570.bank 179730 2308 src570.reserve := requestWidth (by decide)

def ends570 : List ℕ := [2308, 2309, 2313]




theorem cover570 : Cover (Triangular src570) 2313 2308 ends570 := triangleCover (by decide +kernel)

def src571 : Request := ⟨⟨⟨3203,4468,963,331768⟩,985113081937920,10900622576492⟩,13,2,1,308251,7⟩

theorem rank571 : P3_7_1.BankOK src571.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3203_4468_963 331768

theorem width571 : Lower6960.HelperSource.WidthGuard src571.bank 179730 2308 src571.reserve := requestWidth (by decide)

def ends571 : List ℕ := [2308, 2309, 2313]




theorem cover571 : Cover (Triangular src571) 2313 2308 ends571 := triangleCover (by decide +kernel)

def src572 : Request := ⟨⟨⟨4788,6682,1437,396031⟩,3284573675585536,54400253472283⟩,20,2,1,308251,7⟩

theorem rank572 : P3_7_1.BankOK src572.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4788_6682_1437 396031

theorem width572 : Lower6960.HelperSource.WidthGuard src572.bank 179730 2308 src572.reserve := requestWidth (by decide)

def ends572 : List ℕ := [2308, 2309, 2313]




theorem cover572 : Cover (Triangular src572) 2313 2308 ends572 := triangleCover (by decide +kernel)

def src573 : Request := ⟨⟨⟨6419,8954,1931,558931⟩,7926481832378368,175732707213154⟩,32,2,1,308251,7⟩

theorem rank573 : P3_7_1.BankOK src573.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6419_8954_1931 558931

theorem width573 : Lower6960.HelperSource.WidthGuard src573.bank 179730 2308 src573.reserve := requestWidth (by decide)

def ends573 : List ℕ := [2308, 2309, 2313]




theorem cover573 : Cover (Triangular src573) 2313 2308 ends573 := triangleCover (by decide +kernel)

def src574 : Request := ⟨⟨⟨1761,2456,529,141927⟩,163809394688000,996233808436⟩,0,2,1,308288,6⟩

theorem rank574 : P3_7_1.BankOK src574.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1761_2456_529 141927

theorem width574 : Lower6960.HelperSource.WidthGuard src574.bank 179730 2308 src574.reserve := requestWidth (by decide)

def ends574 : List ℕ := [2308, 2309, 2313]

theorem inside574 : Research6966.TerminalBanks.inside src574.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover574 : Cover (Triangular src574) 2313 2308 ends574 := triangleCover (by decide +kernel)

def src575 : Request := ⟨⟨⟨1751,2442,526,159819⟩,161038008844288,973753382962⟩,1,2,1,308288,6⟩

theorem rank575 : P3_7_1.BankOK src575.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_526 159819

theorem width575 : Lower6960.HelperSource.WidthGuard src575.bank 179730 2308 src575.reserve := requestWidth (by decide)

def ends575 : List ℕ := [2308, 2309, 2313]

theorem inside575 : Research6966.TerminalBanks.inside src575.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover575 : Cover (Triangular src575) 2313 2308 ends575 := triangleCover (by decide +kernel)

def src576 : Request := ⟨⟨⟨1755,2448,527,182298⟩,162095945482240,982925287294⟩,2,2,1,308288,6⟩

theorem rank576 : P3_7_1.BankOK src576.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1755_2448_527 182298

theorem width576 : Lower6960.HelperSource.WidthGuard src576.bank 179730 2308 src576.reserve := requestWidth (by decide)

def ends576 : List ℕ := [2308, 2309, 2313]

theorem inside576 : Research6966.TerminalBanks.inside src576.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover576 : Cover (Triangular src576) 2313 2308 ends576 := triangleCover (by decide +kernel)

def src577 : Request := ⟨⟨⟨1788,2494,537,207871⟩,171426255732736,1058996056122⟩,3,2,1,308288,6⟩

theorem rank577 : P3_7_1.BankOK src577.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1788_2494_537 207871

theorem width577 : Lower6960.HelperSource.WidthGuard src577.bank 179730 2308 src577.reserve := requestWidth (by decide)

def ends577 : List ℕ := [2308, 2309, 2313]

theorem inside577 : Research6966.TerminalBanks.inside src577.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover577 : Cover (Triangular src577) 2313 2308 ends577 := triangleCover (by decide +kernel)

def src578 : Request := ⟨⟨⟨1785,2490,537,247258⟩,170783777751040,1053541809432⟩,4,2,1,308288,6⟩

theorem rank578 : P3_7_1.BankOK src578.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1785_2490_537 247258

theorem width578 : Lower6960.HelperSource.WidthGuard src578.bank 179730 2308 src578.reserve := requestWidth (by decide)

def ends578 : List ℕ := [2308, 2309, 2313]

theorem inside578 : Research6966.TerminalBanks.inside src578.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover578 : Cover (Triangular src578) 2313 2308 ends578 := triangleCover (by decide +kernel)

def src579 : Request := ⟨⟨⟨2142,2988,644,260002⟩,294843626291200,2182334193151⟩,6,2,1,308288,6⟩

theorem rank579 : P3_7_1.BankOK src579.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2142_2988_644 260002

theorem width579 : Lower6960.HelperSource.WidthGuard src579.bank 179730 2308 src579.reserve := requestWidth (by decide)

def ends579 : List ℕ := [2308, 2309, 2313]

theorem inside579 : Research6966.TerminalBanks.inside src579.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover579 : Cover (Triangular src579) 2313 2308 ends579 := triangleCover (by decide +kernel)

def src58 : Request := ⟨⟨⟨2312,3207,724,27091⟩,382338138112000,3001726552718⟩,63,2,1,257319,47⟩

theorem rank58 : P3_7_1.BankOK src58.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2312_3207_724 27091

theorem width58 : Lower6960.HelperSource.WidthGuard src58.bank 179730 2308 src58.reserve := requestWidth (by decide)

def ends58 : List ℕ := [2309, 2313]

theorem inside58 : Research6966.TerminalBanks.inside src58.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover58 : Cover (Triangular src58) 2313 2308 ends58 := triangleCover (by decide +kernel)

def src580 : Request := ⟨⟨⟨2605,3634,783,268891⟩,530028320260096,4771119814608⟩,8,2,1,308288,6⟩

theorem rank580 : P3_7_1.BankOK src580.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2605_3634_783 268891

theorem width580 : Lower6960.HelperSource.WidthGuard src580.bank 179730 2308 src580.reserve := requestWidth (by decide)

def ends580 : List ℕ := [2308, 2309, 2313]

theorem inside580 : Research6966.TerminalBanks.inside src580.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover580 : Cover (Triangular src580) 2313 2308 ends580 := triangleCover (by decide +kernel)

def src581 : Request := ⟨⟨⟨3182,4440,947,288393⟩,958405939822592,10543530211269⟩,10,2,1,308288,6⟩

theorem rank581 : P3_7_1.BankOK src581.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3182_4440_947 288393

theorem width581 : Lower6960.HelperSource.WidthGuard src581.bank 179730 2308 src581.reserve := requestWidth (by decide)

def ends581 : List ℕ := [2308, 2309, 2313]




theorem cover581 : Cover (Triangular src581) 2313 2308 ends581 := triangleCover (by decide +kernel)

def src582 : Request := ⟨⟨⟨3203,4468,963,350881⟩,985113081937920,10900622576492⟩,13,2,1,308288,6⟩

theorem rank582 : P3_7_1.BankOK src582.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3203_4468_963 350881

theorem width582 : Lower6960.HelperSource.WidthGuard src582.bank 179730 2308 src582.reserve := requestWidth (by decide)

def ends582 : List ℕ := [2308, 2309, 2313]




theorem cover582 : Cover (Triangular src582) 2313 2308 ends582 := triangleCover (by decide +kernel)

def src583 : Request := ⟨⟨⟨3963,5528,1189,479521⟩,1862381126287360,25492442660491⟩,20,2,1,308288,6⟩

theorem rank583 : P3_7_1.BankOK src583.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3963_5528_1189 479521

theorem width583 : Lower6960.HelperSource.WidthGuard src583.bank 179730 2308 src583.reserve := requestWidth (by decide)

def ends583 : List ℕ := [2308, 2309, 2313]




theorem cover583 : Cover (Triangular src583) 2313 2308 ends583 := triangleCover (by decide +kernel)

def src584 : Request := ⟨⟨⟨6473,9030,1946,588947⟩,8124203203297280,181672708620125⟩,32,2,1,308288,6⟩

theorem rank584 : P3_7_1.BankOK src584.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6473_9030_1946 588947

theorem width584 : Lower6960.HelperSource.WidthGuard src584.bank 179730 2308 src584.reserve := requestWidth (by decide)

def ends584 : List ℕ := [2308, 2309, 2313]




theorem cover584 : Cover (Triangular src584) 2313 2308 ends584 := triangleCover (by decide +kernel)

def src585 : Request := ⟨⟨⟨1778,2480,534,149481⟩,168569368739840,1035458553608⟩,0,2,1,308319,5⟩

theorem rank585 : P3_7_1.BankOK src585.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1778_2480_534 149481

theorem width585 : Lower6960.HelperSource.WidthGuard src585.bank 179730 2308 src585.reserve := requestWidth (by decide)

def ends585 : List ℕ := [2308, 2309, 2313]

theorem inside585 : Research6966.TerminalBanks.inside src585.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover585 : Cover (Triangular src585) 2313 2308 ends585 := triangleCover (by decide +kernel)

def src586 : Request := ⟨⟨⟨1751,2442,526,168561⟩,161038008844288,973753382962⟩,1,2,1,308319,5⟩

theorem rank586 : P3_7_1.BankOK src586.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_526 168561

theorem width586 : Lower6960.HelperSource.WidthGuard src586.bank 179730 2308 src586.reserve := requestWidth (by decide)

def ends586 : List ℕ := [2308, 2309, 2313]

theorem inside586 : Research6966.TerminalBanks.inside src586.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover586 : Cover (Triangular src586) 2313 2308 ends586 := triangleCover (by decide +kernel)

def src587 : Request := ⟨⟨⟨1755,2448,527,192250⟩,162095945482240,982925287294⟩,2,2,1,308319,5⟩

theorem rank587 : P3_7_1.BankOK src587.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1755_2448_527 192250

theorem width587 : Lower6960.HelperSource.WidthGuard src587.bank 179730 2308 src587.reserve := requestWidth (by decide)

def ends587 : List ℕ := [2308, 2309, 2313]

theorem inside587 : Research6966.TerminalBanks.inside src587.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover587 : Cover (Triangular src587) 2313 2308 ends587 := triangleCover (by decide +kernel)

def src588 : Request := ⟨⟨⟨1788,2494,537,219216⟩,171426255732736,1058996056122⟩,3,2,1,308319,5⟩

theorem rank588 : P3_7_1.BankOK src588.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1788_2494_537 219216

theorem width588 : Lower6960.HelperSource.WidthGuard src588.bank 179730 2308 src588.reserve := requestWidth (by decide)

def ends588 : List ℕ := [2308, 2309, 2313]

theorem inside588 : Research6966.TerminalBanks.inside src588.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover588 : Cover (Triangular src588) 2313 2308 ends588 := triangleCover (by decide +kernel)

def src589 : Request := ⟨⟨⟨1785,2490,537,260782⟩,170783777751040,1053541809432⟩,4,2,1,308319,5⟩

theorem rank589 : P3_7_1.BankOK src589.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1785_2490_537 260782

theorem width589 : Lower6960.HelperSource.WidthGuard src589.bank 179730 2308 src589.reserve := requestWidth (by decide)

def ends589 : List ℕ := [2308, 2309, 2313]

theorem inside589 : Research6966.TerminalBanks.inside src589.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover589 : Cover (Triangular src589) 2313 2308 ends589 := triangleCover (by decide +kernel)

def src59 : Request := ⟨⟨⟨2307,3207,724,28173⟩,380487008256000,3001726552718⟩,63,2,1,257319,47⟩

theorem rank59 : P3_7_1.BankOK src59.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2307_3207_724 28173

theorem width59 : Lower6960.HelperSource.WidthGuard src59.bank 179730 2308 src59.reserve := requestWidth (by decide)

def ends59 : List ℕ := [2308, 2309, 2313]

theorem inside59 : Research6966.TerminalBanks.inside src59.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover59 : Cover (Triangular src59) 2313 2308 ends59 := triangleCover (by decide +kernel)

def src590 : Request := ⟨⟨⟨2142,2988,644,274211⟩,294843626291200,2182334193151⟩,6,2,1,308319,5⟩

theorem rank590 : P3_7_1.BankOK src590.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2142_2988_644 274211

theorem width590 : Lower6960.HelperSource.WidthGuard src590.bank 179730 2308 src590.reserve := requestWidth (by decide)

def ends590 : List ℕ := [2308, 2309, 2313]

theorem inside590 : Research6966.TerminalBanks.inside src590.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover590 : Cover (Triangular src590) 2313 2308 ends590 := triangleCover (by decide +kernel)

def src591 : Request := ⟨⟨⟨2605,3634,783,283585⟩,530028320260096,4771119814608⟩,8,2,1,308319,5⟩

theorem rank591 : P3_7_1.BankOK src591.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2605_3634_783 283585

theorem width591 : Lower6960.HelperSource.WidthGuard src591.bank 179730 2308 src591.reserve := requestWidth (by decide)

def ends591 : List ℕ := [2308, 2309, 2313]

theorem inside591 : Research6966.TerminalBanks.inside src591.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover591 : Cover (Triangular src591) 2313 2308 ends591 := triangleCover (by decide +kernel)

def src592 : Request := ⟨⟨⟨3182,4440,947,303778⟩,958405939822592,10543530211269⟩,10,2,1,308319,5⟩

theorem rank592 : P3_7_1.BankOK src592.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3182_4440_947 303778

theorem width592 : Lower6960.HelperSource.WidthGuard src592.bank 179730 2308 src592.reserve := requestWidth (by decide)

def ends592 : List ℕ := [2308, 2309, 2313]




theorem cover592 : Cover (Triangular src592) 2313 2308 ends592 := triangleCover (by decide +kernel)

def src593 : Request := ⟨⟨⟨3203,4468,963,370058⟩,985113081937920,10900622576492⟩,13,2,1,308319,5⟩

theorem rank593 : P3_7_1.BankOK src593.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3203_4468_963 370058

theorem width593 : Lower6960.HelperSource.WidthGuard src593.bank 179730 2308 src593.reserve := requestWidth (by decide)

def ends593 : List ℕ := [2308, 2309, 2313]




theorem cover593 : Cover (Triangular src593) 2313 2308 ends593 := triangleCover (by decide +kernel)

def src594 : Request := ⟨⟨⟨3963,5528,1189,505577⟩,1862381126287360,25492442660491⟩,20,2,1,308319,5⟩

theorem rank594 : P3_7_1.BankOK src594.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3963_5528_1189 505577

theorem width594 : Lower6960.HelperSource.WidthGuard src594.bank 179730 2308 src594.reserve := requestWidth (by decide)

def ends594 : List ℕ := [2308, 2309, 2313]




theorem cover594 : Cover (Triangular src594) 2313 2308 ends594 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources46
