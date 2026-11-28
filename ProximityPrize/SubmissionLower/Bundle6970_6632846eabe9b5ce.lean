import ProximityPrize.SubmissionLower.R6970ExactPrimaryBill
import ProximityPrize.SubmissionLower.Bundle6970_6787940e8645d48e

section Pack_R6970Height2308PrimaryExactSeed04

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed04

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal2 (plan price)

private def pack_R6970Height2308PrimaryExactSeed04_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,174542,813217,
    [(174542,226100356110),
    (584325/4,0),
    (70354,0),
    (342707/8,0),
    (780619/36,0),
    (319867/27,0),
    (1228848/121,0),
    (1228848/121,0),
    (1029250/121,13066615128),
    (163726/21,51272586),
    (163726/21,0),
    (163726/21,0),
    (1035578/147,32402203617),
    (1035578/147,90685419511),
    (21149017/3362,11591424224),
    (21149017/3362,188542099836),
    (2499488/441,115044353170),
    (807317/148,3742700544),
    (807317/148,267317636942),
    (807317/148,545444920954),
    (807317/148,106908910850)],
    [(813217,61569317010),
    (1322777/2,0),
    (630208,0),
    (1027003/3,0),
    (3558177/16,0),
    (2184437/18,0),
    (5553122/49,0),
    (5553122/49,0),
    (4632667/49,0),
    (7558541/98,0),
    (7558541/98,0),
    (307241/4,0),
    (996759/14,0),
    (996759/14,0),
    (47296644/841,0),
    (47296644/841,40735097910),
    (7071040/147,29691585790),
    (134517957/2809,0),
    (134517957/2809,19032765990),
    (134517957/2809,84972134450),
    (134517957/2809,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed04_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed04_rest : List Vertex :=
  [⟨636618853/841,565661187/3362,1348758944314448118555982588/2943991484811045⟩,
   ⟨112471859/147,565661187/3362,239010270210493006926066964/514585907571015⟩,
   ⟨2149808596/2809,565661187/3362,4568848242211906530137760316/9833141594333205⟩,
   ⟨813217,565661187/3362,1756955892249128216258332/3500584405245⟩]

private def pack_R6970Height2308PrimaryExactSeed04_limit : ℚ := 966705852237180020705519823154795612201523/8810593022941946314052310

def lossCap : ℕ := 196858618185192095

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed04_prepared pack_R6970Height2308PrimaryExactSeed04_limit pack_R6970Height2308PrimaryExactSeed04_first pack_R6970Height2308PrimaryExactSeed04_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed04_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed04_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed04_payLimit : pack_R6970Height2308PrimaryExactSeed04_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed04_prepared pack_R6970Height2308PrimaryExactSeed04_first pack_R6970Height2308PrimaryExactSeed04_rest pack_R6970Height2308PrimaryExactSeed04_limit lossCap pack_R6970Height2308PrimaryExactSeed04_fit checked' pack_R6970Height2308PrimaryExactSeed04_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 198623342302957480 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed04
end Pack_R6970Height2308PrimaryExactSeed04

section Pack_R6970Height2308PrimaryExactSeed05

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed05

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal3 (plan price)

private def pack_R6970Height2308PrimaryExactSeed05_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,174090,811643,
    [(174090,224860184613),
    (580545/4,0),
    (69898,0),
    (84281/2,0),
    (775543/36,0),
    (317959/27,0),
    (1223016/121,0),
    (1223016/121,0),
    (1021690/121,12331647283),
    (1140106/147,122587722),
    (1140106/147,0),
    (1140106/147,0),
    (146798/21,32711114750),
    (146798/21,89889628312),
    (21019417/3362,12585701100),
    (21019417/3362,186265188716),
    (2481056/441,116513774271),
    (29658293/5476,0),
    (29658293/5476,273096889239),
    (29658293/5476,545603211820),
    (29658293/5476,107383601462)],
    [(811643,61235482740),
    (1314245/2,0),
    (630208,0),
    (1018594/3,0),
    (3534957/16,0),
    (2171369/18,0),
    (5526986/49,0),
    (5526986/49,0),
    (4598863/49,0),
    (7518041/98,0),
    (7518041/98,0),
    (7518041/98,0),
    (6923853/98,0),
    (6923853/98,0),
    (47006772/841,0),
    (47006772/841,40305326520),
    (7071040/147,30714309190),
    (133567665/2809,0),
    (133567665/2809,18328101540),
    (133567665/2809,84744072140),
    (133567665/2809,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed05_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed05_rest : List Vertex :=
  [⟨635584991/841,564271163/3362,1346889802564586341798099708/2943991484811045⟩,
   ⟨112240481/147,564271163/3362,47709107283583046236139780/102917181514203⟩,
   ⟨2146337522/2809,564271163/3362,912511282159815976111602188/1966628318866641⟩,
   ⟨811643,564271163/3362,350758887575570166047084/700116881049⟩]

private def pack_R6970Height2308PrimaryExactSeed05_limit : ℚ := 14238487057494890378201911828725290418087463/130396776739540805447974188

def lossCap : ℕ := 195524002560469924

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed05_prepared pack_R6970Height2308PrimaryExactSeed05_limit pack_R6970Height2308PrimaryExactSeed05_first pack_R6970Height2308PrimaryExactSeed05_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed05_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed05_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed05_payLimit : pack_R6970Height2308PrimaryExactSeed05_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed05_prepared pack_R6970Height2308PrimaryExactSeed05_first pack_R6970Height2308PrimaryExactSeed05_rest pack_R6970Height2308PrimaryExactSeed05_limit lossCap pack_R6970Height2308PrimaryExactSeed05_fit checked' pack_R6970Height2308PrimaryExactSeed05_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 197285373083582694 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed05
end Pack_R6970Height2308PrimaryExactSeed05

section Pack_R6970Height2308PrimaryExactSeed06

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed06

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal4 (plan price)

private def pack_R6970Height2308PrimaryExactSeed06_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,173007,805383,
    [(173007,224044285374),
    (576835/4,0),
    (625054/9,0),
    (167449/4,0),
    (721492/25,0),
    (818023/49,0),
    (967517/100,8976040178),
    (967517/100,0),
    (3402722/441,561576582),
    (3402722/441,0),
    (3402722/441,0),
    (149571/22,63517341664),
    (149571/22,59596614546),
    (10062884/1681,18263777944),
    (10062884/1681,176075916626),
    (7388896/1323,118598836979),
    (29449791/5476,0),
    (29449791/5476,278494006015),
    (29449791/5476,545842738942),
    (29449791/5476,107849765818)],
    [(805383,61025908950),
    (1305871/2,0),
    (630208,0),
    (3035642/9,0),
    (211854,0),
    (3701582/25,0),
    (760463/8,0),
    (760463/8,0),
    (7478291/98,0),
    (7478291/98,0),
    (7478291/98,0),
    (4782364/75,0),
    (4782364/75,0),
    (45189724/841,0),
    (45189724/841,37029609270),
    (7071040/147,32572457300),
    (132634971/2809,0),
    (132634971/2809,19294110220),
    (132634971/2809,84744070950),
    (132634971/2809,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed06_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed06_rest : List Vertex :=
  [⟨632137379/841,280761883/1681,1339370311707374243904862972/2943991484811045⟩,
   ⟨111320261/147,280761883/1681,236366000459533285393970452/514585907571015⟩,
   ⟨2129685876/2809,280761883/1681,502605417147339679124760412/1092571288259245⟩,
   ⟨805383,280761883/1681,193218629183418084851004/388953822805⟩]

private def pack_R6970Height2308PrimaryExactSeed06_limit : ℚ := 70247067371933998142348666111676191480674759/651983883697704027239870940

def lossCap : ℕ := 194002371161669866

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed06_prepared pack_R6970Height2308PrimaryExactSeed06_limit pack_R6970Height2308PrimaryExactSeed06_first pack_R6970Height2308PrimaryExactSeed06_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed06_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed06_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed06_payLimit : pack_R6970Height2308PrimaryExactSeed06_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed06_prepared pack_R6970Height2308PrimaryExactSeed06_first pack_R6970Height2308PrimaryExactSeed06_rest pack_R6970Height2308PrimaryExactSeed06_limit lossCap pack_R6970Height2308PrimaryExactSeed06_fit checked' pack_R6970Height2308PrimaryExactSeed06_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 195750632915188709 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed06
end Pack_R6970Height2308PrimaryExactSeed06

section Pack_R6970Height2308PrimaryExactSeed07

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed07

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal5 (plan price)

private def pack_R6970Height2308PrimaryExactSeed07_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,172047,800629,
    [(172047,222157010546),
    (573125/4,0),
    (621026/9,0),
    (669607/16,0),
    (721418/25,0),
    (255193/12,0),
    (859655/64,0),
    (1010838/121,32317402588),
    (1010838/121,0),
    (1010838/121,0),
    (1818007/242,0),
    (3114392/441,100859595626),
    (3114392/441,0),
    (9992076/1681,315227836403),
    (29241289/5476,0),
    (29241289/5476,277318226433),
    (29241289/5476,546082274492),
    (29241289/5476,108315398424)],
    [(800629,60502350430),
    (1297497/2,0),
    (630208,0),
    (1013090/3,0),
    (211365,0),
    (211365,0),
    (132886,0),
    (4544483/49,1832888490),
    (4544483/49,0),
    (459536/5,0),
    (549021/8,0),
    (549021/8,0),
    (549021/8,0),
    (44874692/841,70202242730),
    (131702277/2809,0),
    (131702277/2809,16723468650),
    (131702277/2809,84744072140),
    (131702277/2809,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed07_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed07_rest : List Vertex :=
  [⟨34686338/49,279218931/1681,24105907638249202793376116/57176211952335⟩,
   ⟨628454297/841,279218931/1681,147937782815604607838743068/327110164979005⟩,
   ⟨2117264584/2809,279218931/1681,4496635472186844746174063164/9833141594333205⟩,
   ⟨800629,279218931/1681,1728517667179392177497884/3500584405245⟩]

private def pack_R6970Height2308PrimaryExactSeed07_limit : ℚ := 6827602141510948987806766809303251742242524849/64019965742828793848430259380

def lossCap : ℕ := 191913625224890456

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed07_prepared pack_R6970Height2308PrimaryExactSeed07_limit pack_R6970Height2308PrimaryExactSeed07_first pack_R6970Height2308PrimaryExactSeed07_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed07_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed07_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed07_payLimit : pack_R6970Height2308PrimaryExactSeed07_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed07_prepared pack_R6970Height2308PrimaryExactSeed07_first pack_R6970Height2308PrimaryExactSeed07_rest pack_R6970Height2308PrimaryExactSeed07_limit lossCap pack_R6970Height2308PrimaryExactSeed07_fit checked' pack_R6970Height2308PrimaryExactSeed07_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 193647081422721663 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed07
end Pack_R6970Height2308PrimaryExactSeed07

section Pack_R6970Height2308PrimaryExactSeed08

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed08

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal6 (plan price)

private def pack_R6970Height2308PrimaryExactSeed08_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,171734,803499,
    [(171734,222255600578),
    (284725/2,0),
    (617036/9,0),
    (330467/8,0),
    (21129,0),
    (937076/81,0),
    (1205898/121,0),
    (1205898/121,0),
    (1003122/121,17012798234),
    (904436/121,418133248),
    (904436/121,0),
    (904436/121,0),
    (3054620/441,54310298542),
    (100537/15,57964572854),
    (9921936/1681,20321387280),
    (9921936/1681,171124019536),
    (2416984/441,117767682560),
    (14517377/2738,0),
    (14517377/2738,286498795326),
    (14517377/2738,546280410078),
    (14517377/2738,108776505776)],
    [(803499,60561121640),
    (644601,0),
    (630208,0),
    (2995552/9,0),
    (1733401/8,0),
    (355502/3,0),
    (5450272/49,0),
    (5450272/49,0),
    (4503696/49,0),
    (549021/8,0),
    (549021/8,0),
    (549021/8,0),
    (549021/8,0),
    (2997664/49,0),
    (44562632/841,0),
    (44562632/841,35895903580),
    (6522824/135,32504400520),
    (130778382/2809,0),
    (130778382/2809,19749224530),
    (130778382/2809,84639474710),
    (130778382/2809,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed08_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed08_rest : List Vertex :=
  [⟨631180027/841,278762918/1681,89299113282914134914750788/196266098987403⟩,
   ⟨101949541/135,278762918/1681,216736252699655977931595716/472578894708075⟩,
   ⟨2126250309/2809,278762918/1681,4523189315551732224600203836/9833141594333205⟩,
   ⟨803499,278762918/1681,1737074825461033981142812/3500584405245⟩]

private def pack_R6970Height2308PrimaryExactSeed08_limit : ℚ := 332309997283684106566895255567863894401644084/3114664505623895599518363045

def lossCap : ℕ := 191863919344155735

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed08_prepared pack_R6970Height2308PrimaryExactSeed08_limit pack_R6970Height2308PrimaryExactSeed08_first pack_R6970Height2308PrimaryExactSeed08_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed08_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed08_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed08_payLimit : pack_R6970Height2308PrimaryExactSeed08_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed08_prepared pack_R6970Height2308PrimaryExactSeed08_first pack_R6970Height2308PrimaryExactSeed08_rest pack_R6970Height2308PrimaryExactSeed08_limit lossCap pack_R6970Height2308PrimaryExactSeed08_fit checked' pack_R6970Height2308PrimaryExactSeed08_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 193607753023022684 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed08
end Pack_R6970Height2308PrimaryExactSeed08

section Pack_R6970Height2308PrimaryExactSeed09

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed09

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal7 (plan price)

private def pack_R6970Height2308PrimaryExactSeed09_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,170383,797274,
    [(170383,219892223995),
    (565775/4,0),
    (613046/9,0),
    (164131/4,0),
    (712178/25,0),
    (251903/12,0),
    (848105/64,0),
    (997398/121,10261384243),
    (997398/121,0),
    (3350266/441,149367526),
    (3350266/441,0),
    (825164/121,121991133322),
    (825164/121,0),
    (9883632/1681,187838865572),
    (2399974/441,107532711058),
    (2399974/441,0),
    (28828219/5476,299761548790),
    (28828219/5476,546517811664),
    (28828219/5476,109238144878)],
    [(797274,59898545790),
    (1280907/2,0),
    (630208,0),
    (2975602/9,0),
    (211365,0),
    (211365,0),
    (132886,0),
    (4484633/49,0),
    (4484633/49,0),
    (7359791/98,0),
    (7359791/98,0),
    (1611486/25,0),
    (1611486/25,0),
    (44306624/841,36020995530),
    (6477296/135,27319235110),
    (6477296/135,0),
    (129854487/2809,24816976380),
    (129854487/2809,84639473520),
    (129854487/2809,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed09_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed09_rest : List Vertex :=
  [⟨626200810/841,276530191/1681,265793138995737749235141580/588798296962209⟩,
   ⟨101154694/135,276530191/1681,215059462920224644117520324/472578894708075⟩,
   ⟨2109688179/2809,276530191/1681,1496078618771614021543228948/3277713864777735⟩,
   ⟨797274,276530191/1681,191526163511387945139516/388953822805⟩]

private def pack_R6970Height2308PrimaryExactSeed09_limit : ℚ := 327552773718962181741794012412796073633787359/3114664505623895599518363045

def lossCap : ℕ := 189218174027926388

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed09_prepared pack_R6970Height2308PrimaryExactSeed09_limit pack_R6970Height2308PrimaryExactSeed09_first pack_R6970Height2308PrimaryExactSeed09_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed09_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed09_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed09_payLimit : pack_R6970Height2308PrimaryExactSeed09_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed09_prepared pack_R6970Height2308PrimaryExactSeed09_first pack_R6970Height2308PrimaryExactSeed09_rest pack_R6970Height2308PrimaryExactSeed09_limit lossCap pack_R6970Height2308PrimaryExactSeed09_fit checked' pack_R6970Height2308PrimaryExactSeed09_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 190947889997281578 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed09
end Pack_R6970Height2308PrimaryExactSeed09

section Pack_R6970Height2308PrimaryExactSeed10

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed10

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal8 (plan price)

private def pack_R6970Height2308PrimaryExactSeed10_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,169726,795308,
    [(169726,218793204273),
    (562135/4,0),
    (609094/9,0),
    (163039/4,0),
    (703012/25,0),
    (750821/36,0),
    (842385/64,0),
    (980385/121,2553379465),
    (980385/121,0),
    (3262862/441,0),
    (3262862/441,0),
    (818508/121,130845384775),
    (818508/121,0),
    (9811248/1681,184326101113),
    (2383126/441,111041808360),
    (2383126/441,0),
    (28623651/5476,299623704138),
    (28623651/5476,546752957104),
    (28623651/5476,109694726976)],
    [(795308,59606577420),
    (1272691/2,0),
    (630208,0),
    (2955842/9,0),
    (211854,0),
    (211854,0),
    (132886,0),
    (634698/7,0),
    (634698/7,0),
    (549021/8,0),
    (549021/8,0),
    (1598382/25,0),
    (1598382/25,0),
    (43985472/841,35502213840),
    (10720336/225,29579781210),
    (10720336/225,0),
    (128939391/2809,22718519670),
    (128939391/2809,84639473520),
    (128939391/2809,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed10_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed10_rest : List Vertex :=
  [⟨624868556/841,275498158/1681,1326743015634790098335283964/2943991484811045⟩,
   ⟨168223964/225,275498158/1681,357808465407167283748511644/787631491180125⟩,
   ⟨2105080781/2809,275498158/1681,4480382699208847661314236988/9833141594333205⟩,
   ⟨795308,275498158/1681,1720052319779907634161436/3500584405245⟩]

private def pack_R6970Height2308PrimaryExactSeed10_limit : ℚ := 10333493388608709659538326758494831761650769/98878238273774463476773430

def lossCap : ℕ := 187930836205934206

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed10_prepared pack_R6970Height2308PrimaryExactSeed10_limit pack_R6970Height2308PrimaryExactSeed10_first pack_R6970Height2308PrimaryExactSeed10_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed10_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed10_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed10_payLimit : pack_R6970Height2308PrimaryExactSeed10_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed10_prepared pack_R6970Height2308PrimaryExactSeed10_first pack_R6970Height2308PrimaryExactSeed10_rest pack_R6970Height2308PrimaryExactSeed10_limit lossCap pack_R6970Height2308PrimaryExactSeed10_fit checked' pack_R6970Height2308PrimaryExactSeed10_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 189656364807848244 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed10
end Pack_R6970Height2308PrimaryExactSeed10

section Pack_R6970Height2308PrimaryExactSeed11

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed11

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal9 (plan price)

private def pack_R6970Height2308PrimaryExactSeed11_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,170212,794829,
    [(170212,218892291948),
    (138590,0),
    (601010/9,0),
    (322765/8,0),
    (62165/3,0),
    (920540/81,0),
    (1189050/121,0),
    (1189050/121,0),
    (980970/121,18294036028),
    (3244940/441,43008372),
    (3244940/441,0),
    (3244940/441,0),
    (1573305/242,51647490914),
    (1573305/242,56414103794),
    (9711080/1681,31162749144),
    (9711080/1681,156163675444),
    (2366440/441,113873539994),
    (14210525/2738,0),
    (14210525/2738,300451300550),
    (14210525/2738,546985632894),
    (14210525/2738,110147655470)],
    [(794829,59665272980),
    (626497,0),
    (620224,0),
    (2921644/9,0),
    (1699861/8,0),
    (349210/3,0),
    (767824/7,0),
    (767824/7,0),
    (4405104/49,0),
    (549021/8,0),
    (549021/8,0),
    (549021/8,0),
    (13629784/225,0),
    (2928608/49,0),
    (43635928/841,0),
    (43635928/841,34423456060),
    (31937704/675,31435091340),
    (128033094/2809,0),
    (128033094/2809,21240847880),
    (128033094/2809,84639474710),
    (128033094/2809,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed11_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed11_rest : List Vertex :=
  [⟨624815261/841,276415292/1681,265069581473426890285091788/588798296962209⟩,
   ⟨504571871/675,276415292/1681,1072149717192569403713314516/2362894473540375⟩,
   ⟨2104641567/2809,276415292/1681,4475011388844606087879090748/9833141594333205⟩,
   ⟨794829,276415292/1681,1717261234931287730906908/3500584405245⟩]

private def pack_R6970Height2308PrimaryExactSeed11_limit : ℚ := 325671021087607143614958536226686109970598963/3114664505623895599518363045

def lossCap : ℕ := 187915279079788014

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed11_prepared pack_R6970Height2308PrimaryExactSeed11_limit pack_R6970Height2308PrimaryExactSeed11_first pack_R6970Height2308PrimaryExactSeed11_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed11_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed11_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed11_payLimit : pack_R6970Height2308PrimaryExactSeed11_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed11_prepared pack_R6970Height2308PrimaryExactSeed11_first pack_R6970Height2308PrimaryExactSeed11_rest pack_R6970Height2308PrimaryExactSeed11_limit lossCap pack_R6970Height2308PrimaryExactSeed11_fit checked' pack_R6970Height2308PrimaryExactSeed11_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 189640637442865665 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed11
end Pack_R6970Height2308PrimaryExactSeed11

section Pack_R6970Height2308PrimaryExactSeed12

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed12

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal10 (plan price)

private def pack_R6970Height2308PrimaryExactSeed12_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,168785,788464,
    [(168785,217875297672),
    (137663,0),
    (596993/9,0),
    (40219,0),
    (698538/25,0),
    (741139/36,0),
    (831055/64,0),
    (966995/121,230679774),
    (966995/121,0),
    (3227018/441,0),
    (1571413/242,69124176639),
    (1571413/242,55862825019),
    (1571413/242,0),
    (9641040/1681,186147849606),
    (2349754/441,112114758758),
    (2349754/441,0),
    (28218449/5476,305345222784),
    (28218449/5476,547218652798),
    (28218449/5476,110599709030)],
    [(788464,59397409760),
    (1244651/2,0),
    (620224,0),
    (324078,0),
    (211365,0),
    (3377577/16,0),
    (132886,0),
    (626046/7,0),
    (312915/4,0),
    (549021/8,0),
    (2737708/45,0),
    (2737708/45,0),
    (2737708/45,0),
    (43324044/841,34129474720),
    (1268576/27,30229619300),
    (1268576/27,0),
    (127126797/2809,22365740600),
    (127126797/2809,84639474710),
    (127126797/2809,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed12_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed12_rest : List Vertex :=
  [⟨619774180/841,274086545/1681,438263080390477076397506132/981330494937015⟩,
   ⟨20019952/27,274086545/1681,42544062429074797007200244/94515778941615⟩,
   ⟨2087668579/2809,274086545/1681,1479791932767588867737089556/3277713864777735⟩,
   ⟨788464,274086545/1681,37859913543013456877836/77790764561⟩]

private def pack_R6970Height2308PrimaryExactSeed12_limit : ℚ := 64160222461780537096888556742389808200403337/622932901124779119903672609

def lossCap : ℕ := 186220822264961818

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed12_prepared pack_R6970Height2308PrimaryExactSeed12_limit pack_R6970Height2308PrimaryExactSeed12_first pack_R6970Height2308PrimaryExactSeed12_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed12_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed12_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed12_payLimit : pack_R6970Height2308PrimaryExactSeed12_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed12_prepared pack_R6970Height2308PrimaryExactSeed12_first pack_R6970Height2308PrimaryExactSeed12_rest pack_R6970Height2308PrimaryExactSeed12_limit lossCap pack_R6970Height2308PrimaryExactSeed12_fit checked' pack_R6970Height2308PrimaryExactSeed12_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 187932156759301875 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed12
end Pack_R6970Height2308PrimaryExactSeed12

section Pack_R6970Height2308PrimaryExactSeed13

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed13

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal11 (plan price)

private def pack_R6970Height2308PrimaryExactSeed13_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,169514,791117,
    [(169514,216340703340),
    (136754,0),
    (593054/9,0),
    (318379/8,0),
    (61366/3,0),
    (909728/81,0),
    (107094/11,0),
    (107094/11,0),
    (966486/121,18862933184),
    (458492/63,44548),
    (458492/63,13969524),
    (458492/63,0),
    (1550049/242,22660045086),
    (1550049/242,88845760510),
    (9572360/1681,30322775404),
    (9572360/1681,148258047076),
    (2333392/441,110862138256),
    (14009891/2738,3768449360),
    (14009891/2738,306529364782),
    (14009891/2738,547446803654),
    (14009891/2738,111043587016)],
    [(791117,58977876620),
    (618235,0),
    (618235,0),
    (2882068/9,0),
    (1677931/8,0),
    (115032,0),
    (5325400/49,0),
    (5325400/49,0),
    (4340640/49,0),
    (549021/8,0),
    (549021/8,0),
    (549021/8,0),
    (2684504/45,0),
    (2684504/45,0),
    (43018216/841,0),
    (43018216/841,33545897020),
    (31495432/675,30380487840),
    (126238098/2809,0),
    (126238098/2809,22588033790),
    (126238098/2809,84639474710),
    (126238098/2809,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed13_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed13_rest : List Vertex :=
  [⟨622311181/841,275380674/1681,1319936575525249126172310268/2943991484811045⟩,
   ⟨502508543/675,275380674/1681,1067660719731848707456687828/2362894473540375⟩,
   ⟨2096009555/2809,275380674/1681,495134059230445596253955932/1092571288259245⟩,
   ⟨791117,275380674/1681,569608662391901265229748/1166861468415⟩]

private def pack_R6970Height2308PrimaryExactSeed13_limit : ℚ := 64511293900787478974375732841600239023256296/622932901124779119903672609

def lossCap : ℕ := 185358957059060888

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed13_prepared pack_R6970Height2308PrimaryExactSeed13_limit pack_R6970Height2308PrimaryExactSeed13_first pack_R6970Height2308PrimaryExactSeed13_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed13_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed13_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed13_payLimit : pack_R6970Height2308PrimaryExactSeed13_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed13_prepared pack_R6970Height2308PrimaryExactSeed13_first pack_R6970Height2308PrimaryExactSeed13_rest pack_R6970Height2308PrimaryExactSeed13_limit lossCap pack_R6970Height2308PrimaryExactSeed13_fit checked' pack_R6970Height2308PrimaryExactSeed13_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 187076397252030649 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed13
end Pack_R6970Height2308PrimaryExactSeed13

section Pack_R6970Height2308PrimaryExactSeed14

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed14

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal12 (plan price)

private def pack_R6970Height2308PrimaryExactSeed14_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,167759,780412,
    [(167759,214621002741),
    (135845,0),
    (589115/9,0),
    (632415/16,0),
    (731645/36,0),
    (819945/64,0),
    (964630/121,1828641699),
    (964630/121,0),
    (964630/121,0),
    (3191870/441,0),
    (3191870/441,0),
    (72036/11,66740979447),
    (72036/11,55562301261),
    (72036/11,0),
    (9503680/1681,183158385006),
    (2317030/441,140563435375),
    (2317030/441,0),
    (6966505/1369,283615137975),
    (6966505/1369,547812356018),
    (6966505/1369,111510370430)],
    [(780412,58504642860),
    (1228289/2,0),
    (1228289/2,0),
    (954158/3,0),
    (3334147/16,0),
    (132886,0),
    (4338713/49,0),
    (4338713/49,0),
    (4338713/49,0),
    (549021/8,0),
    (549021/8,0),
    (505197/8,0),
    (505197/8,0),
    (505197/8,0),
    (42712388/841,33466581480),
    (10425488/225,28905775750),
    (10425488/225,0),
    (125200502/2809,23618745150),
    (125200502/2809,84972134450),
    (125200502/2809,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed14_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed14_rest : List Vertex :=
  [⟨613614104/841,272499199/1681,1300171889280924380191374076/2943991484811045⟩,
   ⟨165167212/225,272499199/1681,350575031357085071291031452/787631491180125⟩,
   ⟨2066976806/2809,272499199/1681,4390234952596057148622529084/9833141594333205⟩,
   ⟨780412,272499199/1681,1684333961707546808379164/3500584405245⟩]

private def pack_R6970Height2308PrimaryExactSeed14_limit : ℚ := 63113521911718499537181168378984598607049374/622932901124779119903672609

def lossCap : ℕ := 182723908680425709

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed14_prepared pack_R6970Height2308PrimaryExactSeed14_limit pack_R6970Height2308PrimaryExactSeed14_first pack_R6970Height2308PrimaryExactSeed14_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed14_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed14_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed14_payLimit : pack_R6970Height2308PrimaryExactSeed14_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed14_prepared pack_R6970Height2308PrimaryExactSeed14_first pack_R6970Height2308PrimaryExactSeed14_rest pack_R6970Height2308PrimaryExactSeed14_limit lossCap pack_R6970Height2308PrimaryExactSeed14_fit checked' pack_R6970Height2308PrimaryExactSeed14_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 184418777415433058 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed14
end Pack_R6970Height2308PrimaryExactSeed14

section Pack_R6970Height2308PrimaryExactSeed15

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed15

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal13 (plan price)

private def pack_R6970Height2308PrimaryExactSeed15_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,168911,787700,
    [(168911,213875683669),
    (134945,0),
    (585215/9,0),
    (628115/16,0),
    (242315/12,0),
    (899075/81,0),
    (1167180/121,0),
    (1167180/121,0),
    (86565/11,21915706845),
    (3174470/441,247298304),
    (3174470/441,0),
    (3174470/441,0),
    (1527135/242,18543253283),
    (1527135/242,87808230687),
    (9435680/1681,8979685789),
    (9435680/1681,167913868211),
    (328690/63,113678844180),
    (6916105/1369,9040890290),
    (6916105/1369,304083826772),
    (6916105/1369,547810542502),
    (6916105/1369,111750968376)],
    [(787700,58316208740),
    (1220189/2,0),
    (1220189/2,0),
    (2843074/9,0),
    (3312647/16,0),
    (682085/6,0),
    (5276758/49,0),
    (215255/2,0),
    (4277124/49,0),
    (549021/8,0),
    (549021/8,0),
    (549021/8,0),
    (475107/8,0),
    (475107/8,0),
    (4959107/98,0),
    (4959107/98,33666115240),
    (31059664/675,32101995050),
    (27788632/625,0),
    (27788632/625,20404563480),
    (27788632/625,84639474710),
    (27788632/625,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed15_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed15_rest : List Vertex :=
  [⟨72235493/98,274503711/1681,76591443668546177586609244/171528635857005⟩,
   ⟨500637836/675,274503711/1681,1063523990158990079603039956/2362894473540375⟩,
   ⟨464523868/625,274503711/1681,987387677103765840060398428/2187865253278125⟩,
   ⟨787700,274503711/1681,37798641467214921668876/77790764561⟩]

private def pack_R6970Height2308PrimaryExactSeed15_limit : ℚ := 452373420327212105405087612010422684361223/4405546460744767627734375

def lossCap : ℕ := 182932547367465958

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed15_prepared pack_R6970Height2308PrimaryExactSeed15_limit pack_R6970Height2308PrimaryExactSeed15_first pack_R6970Height2308PrimaryExactSeed15_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed15_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed15_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed15_payLimit : pack_R6970Height2308PrimaryExactSeed15_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed15_prepared pack_R6970Height2308PrimaryExactSeed15_first pack_R6970Height2308PrimaryExactSeed15_rest pack_R6970Height2308PrimaryExactSeed15_limit lossCap pack_R6970Height2308PrimaryExactSeed15_fit checked' pack_R6970Height2308PrimaryExactSeed15_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 184642716453188364 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed15
end Pack_R6970Height2308PrimaryExactSeed15

section Pack_R6970Height2308PrimaryExactSeed16

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed16

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal14 (plan price)

private def pack_R6970Height2308PrimaryExactSeed16_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,168614,786017,
    [(168614,212659994652),
    (134054,0),
    (581354/9,0),
    (311929/8,0),
    (60191/3,0),
    (893828/81,0),
    (1161834/121,0),
    (1161834/121,0),
    (85926/11,21111385164),
    (3157244/441,1204),
    (3157244/441,426193832),
    (3157244/441,0),
    (1515849/242,16330981212),
    (1515849/242,89693214928),
    (9368360/1681,11160453610),
    (9368360/1681,163749233290),
    (2284792/441,111084704778),
    (6866209/1369,11899814896),
    (6866209/1369,307902624630),
    (6866209/1369,547876763632),
    (6866209/1369,111882691432)],
    [(786017,57990312620),
    (606085,0),
    (606085,0),
    (2823868/9,0),
    (1645681/8,0),
    (339046/3,0),
    (107200,0),
    (106896,0),
    (4245840/49,0),
    (549021/8,0),
    (549021/8,0),
    (549021/8,0),
    (475107/8,0),
    (475107/8,0),
    (4959107/98,0),
    (4959107/98,32893759000),
    (30845032/675,30910207840),
    (27788632/625,0),
    (27788632/625,22511834520),
    (27788632/625,84639473520),
    (27788632/625,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed16_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed16_rest : List Vertex :=
  [⟨72070559/98,274071774/1681,15280218659377237719131564/34305727171401⟩,
   ⟨499716443/675,274071774/1681,1061486496488776128570646228/2362894473540375⟩,
   ⟨463471993/625,274071774/1681,984959738689735368237038428/2187865253278125⟩,
   ⟨786017,274071774/1681,188561573840246968909116/388953822805⟩]

private def pack_R6970Height2308PrimaryExactSeed16_limit : ℚ := 3154274426495495066220724454037610026903436/30838825225213373394140625

def lossCap : ℕ := 181831003037418482

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed16_prepared pack_R6970Height2308PrimaryExactSeed16_limit pack_R6970Height2308PrimaryExactSeed16_first pack_R6970Height2308PrimaryExactSeed16_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed16_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed16_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed16_payLimit : pack_R6970Height2308PrimaryExactSeed16_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed16_prepared pack_R6970Height2308PrimaryExactSeed16_first pack_R6970Height2308PrimaryExactSeed16_rest pack_R6970Height2308PrimaryExactSeed16_limit lossCap pack_R6970Height2308PrimaryExactSeed16_fit checked' pack_R6970Height2308PrimaryExactSeed16_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 183537585168437776 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed16
end Pack_R6970Height2308PrimaryExactSeed16

section Pack_R6970Height2308PrimaryExactSeed17

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed17

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal15 (plan price)

private def pack_R6970Height2308PrimaryExactSeed17_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,166703,773936,
    [(166703,211181710972),
    (133172,0),
    (577532/9,0),
    (154911/4,0),
    (668046/25,0),
    (756374/49,0),
    (281450/27,0),
    (84960/11,21670751624),
    (84960/11,14448),
    (84960/11,0),
    (3140192/441,0),
    (3140192/441,0),
    (1512531/242,0),
    (1499577/242,45384616620),
    (1499577/242,55655018762),
    (1499577/242,0),
    (9340920/1681,178149198406),
    (6812896/1323,147758576830),
    (6812896/1323,0),
    (6816817/1369,286025735778),
    (6816817/1369,548067199580),
    (6816817/1369,112013154748)],
    [(773936,57587782540),
    (602116,0),
    (602116,0),
    (934952/3,0),
    (409431/2,0),
    (681716/5,0),
    (317467/3,0),
    (605088/7,0),
    (605088/7,0),
    (605088/7,0),
    (549021/8,0),
    (549021/8,0),
    (964947/16,0),
    (946157/16,0),
    (946157/16,0),
    (946157/16,0),
    (4946427/98,32968062260),
    (30617216/675,28414295720),
    (30617216/675,0),
    (27788632/625,24822390880),
    (27788632/625,84972133260),
    (27788632/625,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed17_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed17_rest : List Vertex :=
  [⟨70899301/98,270886823/1681,15011736528554853975336364/34305727171401⟩,
   ⟨491789584/675,270886823/1681,1043376784905885645931863764/2362894473540375⟩,
   ⟨455921368/625,270886823/1681,107512984753335380780826492/243096139253125⟩,
   ⟨773936,270886823/1681,1669305563106675614246684/3500584405245⟩]

private def pack_R6970Height2308PrimaryExactSeed17_limit : ℚ := 9238974728071225005578825492250333150167933/92516475675640120182421875

def lossCap : ℕ := 179361552993759294

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed17_prepared pack_R6970Height2308PrimaryExactSeed17_limit pack_R6970Height2308PrimaryExactSeed17_first pack_R6970Height2308PrimaryExactSeed17_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed17_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed17_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed17_payLimit : pack_R6970Height2308PrimaryExactSeed17_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed17_prepared pack_R6970Height2308PrimaryExactSeed17_first pack_R6970Height2308PrimaryExactSeed17_rest pack_R6970Height2308PrimaryExactSeed17_limit lossCap pack_R6970Height2308PrimaryExactSeed17_fit checked' pack_R6970Height2308PrimaryExactSeed17_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 181043128054534460 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed17
end Pack_R6970Height2308PrimaryExactSeed17

section Pack_R6970Height2308PrimaryExactSeed18

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed18

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal16 (plan price)

private def pack_R6970Height2308PrimaryExactSeed18_prepared : Frame :=
  ⟨17482907648/89865,64380/23173,166686,777168,
    [(166686,210562361047),
    (132299,0),
    (573749/9,0),
    (615473/16,0),
    (237709/12,0),
    (798275/64,0),
    (928255/121,9562811179),
    (928255/121,12040),
    (3123314/441,0),
    (3123314/441,0),
    (767180/121,56780800662),
    (767180/121,53027633140),
    (767180/121,0),
    (9273020/1681,179018823026),
    (966176/189,110018268781),
    (966176/189,0),
    (182917/37,252007936263),
    (182917/37,622918639060),
    (182917/37,112134741130)],
    [(777168,57435897740),
    (1196375/2,0),
    (1196375/2,0),
    (2786038/9,0),
    (3249437/16,0),
    (132886,0),
    (601014/7,0),
    (2704783/36,0),
    (549021/8,0),
    (549021/8,0),
    (505197/8,0),
    (9134644/147,0),
    (9134644/147,0),
    (4946427/98,32787201640),
    (30396056/675,30466078250),
    (30396056/675,0),
    (27788632/625,14782810700),
    (27788632/625,93612737540),
    (27788632/625,0)]⟩

private def pack_R6970Height2308PrimaryExactSeed18_first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def pack_R6970Height2308PrimaryExactSeed18_rest : List Vertex :=
  [⟨71216037/98,270926146/1681,25162323672904041387059572/57176211952335⟩,
   ⟨494192344/675,270926146/1681,1049879138564544198802202324/2362894473540375⟩,
   ⟨457941368/625,270926146/1681,973079724718001262288878428/2187865253278125⟩,
   ⟨777168,270926146/1681,559348714069149383554996/1166861468415⟩]

private def pack_R6970Height2308PrimaryExactSeed18_limit : ℚ := 35801177921749590042940163137175832941062/357206469790116294140625

def lossCap : ℕ := 179146997983671206

private theorem checked' : ExactRank.checked pack_R6970Height2308PrimaryExactSeed18_prepared pack_R6970Height2308PrimaryExactSeed18_limit pack_R6970Height2308PrimaryExactSeed18_first pack_R6970Height2308PrimaryExactSeed18_rest := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed18_fit : RankBill.frame plan price .near = pack_R6970Height2308PrimaryExactSeed18_prepared := by decide +kernel
private theorem pack_R6970Height2308PrimaryExactSeed18_payLimit : pack_R6970Height2308PrimaryExactSeed18_limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near pack_R6970Height2308PrimaryExactSeed18_prepared pack_R6970Height2308PrimaryExactSeed18_first pack_R6970Height2308PrimaryExactSeed18_rest pack_R6970Height2308PrimaryExactSeed18_limit lossCap pack_R6970Height2308PrimaryExactSeed18_fit checked' pack_R6970Height2308PrimaryExactSeed18_payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 180834599844121344 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed18
end Pack_R6970Height2308PrimaryExactSeed18
