/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Singleton and multi-factor terminal prices specialize Lucieno's and BitWonka's interpolation bounds. -/
import ProximityPrize.SubmissionLower.K6833TerminalLedger
import ProximityPrize.SubmissionLower.K6833TerminalIncumbentGraph

namespace ProximityPrize.SubmissionLower.K6833Residual
open RCN095 LocatorFactorAggregate
open K6833TerminalIncumbentGraph (axisPrice)
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000

def clip (f : Envelope) (cfg : Fin 3 → JetProfile) : Envelope :=
  ⟨f.slope,f.middle,jetSourceCap cfg⟩
def predEnvelope (f : Envelope) : Envelope := ⟨f.slope-1,f.middle-1,f.total-1⟩
def sharpDirection (f : Envelope) := shortenedDirection f (pencilBudget*residualPriceScale)
def upperGraphAxis (f : Envelope) (cfg : Fin 3 → JetProfile) (i : Fin 3) : ℕ :=
  max (jetGraphNumerator TailCorrections.original (f.pad 2) cfg (unit i))
    ((residualPriceScale/49997)*131073*81077*byAxis (identityGraph (f.pad 2)) i)
def leadCost (f : Envelope) (cfg : Fin 3 → JetProfile) (left : FlagDegree) :=
  ((List.finRange 3).map (fun j => flagMixed left (cfg j).leading.flag (sharpDirection f))).sum
def graphCost (f : Envelope) (cfg : Fin 3 → JetProfile) (left : FlagDegree) :=
  leadCost f cfg left + axisPrice (upperGraphAxis f cfg) left
def helperCost (f : Envelope) (p : JetProfile) (left : FlagDegree) :=
  flagMixed left (p.helper (f.pad 2)).flag (sharpDirection f)
def rawCost (shape : Envelope) (left : FlagDegree) :=
  rawChargeWithCorrections TailCorrections.original (shape.pad 0) left

structure TerminalRow where
  envelope : Envelope
  terminalLimit : ℕ
  single : Option Profiles
  multiple : Option Profiles

def simpleMode (f : Envelope) (limit : ℕ) : Option Profiles → Bool
  | none => rawGatesWithCorrections TailCorrections.original (f.pad 0) &&
      decide (rawCost f f.flag ≤ limit)
  | some ids => let cfg := cellConfig ids; let short := clip f cfg
    jetGatesWithCorrections TailCorrections.original f cfg && decide (
      1 ≤ f.slope ∧ 2 ≤ f.middle ∧ f.middle ≤ short.total ∧
      rawCost short short.flag ≤ limit ∧ graphCost f cfg f.flag/residualPriceScale ≤ limit) &&
      (List.finRange 3).all (fun j => decide (helperCost f (cfg j) f.flag/residualPriceScale ≤ limit))
def multipleMode (overall f : Envelope) (lim : ℕ) : Option Profiles → Bool
  | none => rawGatesWithCorrections TailCorrections.original (f.pad 0) &&
      decide (rawCost f overall.flag ≤ lim)
  | some ids => let cfg := cellConfig ids
    jetGatesWithCorrections TailCorrections.original f cfg &&
      jetMonotoneWithCorrections TailCorrections.original f cfg && decide (
      1 ≤ f.slope ∧ 2 ≤ f.middle ∧
      axisPrice (jetChargeAxisWithCorrections TailCorrections.original f cfg) overall.flag /
        residualPriceScale ≤ lim)
def validRow (row : TerminalRow) : Bool :=
  let f := row.envelope
  decide (1 ≤ f.slope ∧ f.slope ≤ f.middle ∧ f.middle ≤ f.total ∧
      f.slope ≤ 16 ∧ f.middle ≤ 66 ∧ f.total ≤ 8870) &&
    simpleMode f row.terminalLimit row.single &&
    (decide (f.slope = 1) || multipleMode f (predEnvelope f) row.terminalLimit row.multiple)
private def rows1_0 : List TerminalRow := [
  ⟨⟨1,1,6968⟩,248103920679285493,none,none⟩,
  ⟨⟨1,2,6945⟩,248109582208506812,none,none⟩,
  ⟨⟨1,3,6923⟩,248115258173156121,none,none⟩,
  ⟨⟨1,4,6900⟩,248120948573233419,none,none⟩,
  ⟨⟨1,5,6876⟩,248126653408738709,none,none⟩,
  ⟨⟨1,6,6853⟩,248132372679671989,none,none⟩,
  ⟨⟨1,7,6830⟩,248138106386033259,none,none⟩,
  ⟨⟨1,8,6806⟩,248143854527822518,none,none⟩]
private theorem rows1_0_v : rows1_0.all validRow = true := by decide +kernel
private def rows1_1 : List TerminalRow := [
  ⟨⟨1,9,6782⟩,248149617105039768,none,none⟩,
  ⟨⟨1,10,6758⟩,248155394117685008,none,none⟩,
  ⟨⟨1,11,6734⟩,248161185565758237,none,none⟩,
  ⟨⟨1,12,6709⟩,248166991449259458,none,none⟩,
  ⟨⟨1,13,6685⟩,248172811768188668,none,none⟩,
  ⟨⟨1,14,6660⟩,248178646522545867,none,none⟩,
  ⟨⟨1,15,6635⟩,248184495712331060,none,none⟩,
  ⟨⟨1,16,6610⟩,248190359337544240,none,none⟩]
private theorem rows1_1_v : rows1_1.all validRow = true := by decide +kernel
private def rows1_2 : List TerminalRow := [
  ⟨⟨1,17,6584⟩,248196237398185410,none,none⟩,
  ⟨⟨1,18,6559⟩,248202129894254570,none,none⟩,
  ⟨⟨1,19,6533⟩,248208036825751722,none,none⟩,
  ⟨⟨1,20,6507⟩,248213958192676862,none,none⟩,
  ⟨⟨1,21,6480⟩,248219893995029992,none,none⟩,
  ⟨⟨1,22,6454⟩,248225844232811115,none,none⟩,
  ⟨⟨1,23,6427⟩,248231808906020225,none,none⟩,
  ⟨⟨1,24,6400⟩,248237788014657327,none,none⟩]
private theorem rows1_2_v : rows1_2.all validRow = true := by decide +kernel
private def rows1_3 : List TerminalRow := [
  ⟨⟨1,25,6372⟩,248243781558722419,none,none⟩,
  ⟨⟨1,26,6345⟩,248249789538215499,none,none⟩,
  ⟨⟨1,27,6317⟩,248255811953136571,none,none⟩,
  ⟨⟨1,28,6289⟩,248261848803485633,none,none⟩,
  ⟨⟨1,29,6260⟩,248267900089262685,none,none⟩,
  ⟨⟨1,30,6232⟩,248273965810467726,none,none⟩,
  ⟨⟨1,31,6202⟩,248280045967100758,none,none⟩,
  ⟨⟨1,32,6173⟩,248286140559161781,none,none⟩]
private theorem rows1_3_v : rows1_3.all validRow = true := by decide +kernel
private def rows1_4 : List TerminalRow := [
  ⟨⟨1,33,6143⟩,248292249586650794,none,none⟩,
  ⟨⟨1,34,6113⟩,248298373049567796,none,none⟩,
  ⟨⟨1,35,6083⟩,248304510947912789,none,none⟩,
  ⟨⟨1,36,6052⟩,248310663281685772,none,none⟩,
  ⟨⟨1,37,6021⟩,248316830050886743,none,none⟩,
  ⟨⟨1,38,5989⟩,248323011255515707,none,none⟩,
  ⟨⟨1,39,5957⟩,248329206895572659,none,none⟩,
  ⟨⟨1,40,5924⟩,248335416971057602,none,none⟩]
private theorem rows1_4_v : rows1_4.all validRow = true := by decide +kernel
private def rows1_5 : List TerminalRow := [
  ⟨⟨1,41,5892⟩,248341641481970536,none,none⟩,
  ⟨⟨1,42,5858⟩,248347880428311459,none,none⟩,
  ⟨⟨1,43,5824⟩,248354133810080372,none,none⟩,
  ⟨⟨1,44,5790⟩,248360401627277276,none,none⟩,
  ⟨⟨1,45,5755⟩,248366683879902168,none,none⟩,
  ⟨⟨1,46,5704⟩,248372980567955053,none,none⟩,
  ⟨⟨1,47,5652⟩,248379291691435927,none,none⟩,
  ⟨⟨1,48,5598⟩,248385617250344790,none,none⟩]
private theorem rows1_5_v : rows1_5.all validRow = true := by decide +kernel
private def rows1_6 : List TerminalRow := [
  ⟨⟨1,49,5543⟩,248391957244681645,none,none⟩,
  ⟨⟨1,50,5486⟩,248398311674446489,none,none⟩,
  ⟨⟨1,51,5427⟩,248404680539639322,none,none⟩,
  ⟨⟨1,52,5366⟩,248411063840260146,none,none⟩,
  ⟨⟨1,53,5301⟩,248417461576308961,none,none⟩,
  ⟨⟨1,54,5174⟩,248423873747785765,none,none⟩,
  ⟨⟨1,55,4757⟩,248430300354690560,none,none⟩,
  ⟨⟨1,56,4322⟩,248436741397023344,none,none⟩]
private theorem rows1_6_v : rows1_6.all validRow = true := by decide +kernel
private def rows1_7 : List TerminalRow := [
  ⟨⟨1,57,3869⟩,248443196874784120,none,none⟩,
  ⟨⟨1,58,3397⟩,248449666787972884,none,none⟩,
  ⟨⟨1,59,2907⟩,248456151136589638,none,none⟩,
  ⟨⟨1,60,2398⟩,248462649920634384,none,none⟩,
  ⟨⟨1,61,1871⟩,248469163140107120,none,none⟩,
  ⟨⟨1,62,1325⟩,248475690795007845,none,none⟩,
  ⟨⟨1,63,760⟩,248482232885336560,none,none⟩,
  ⟨⟨1,64,177⟩,248488789411093264,none,none⟩]
private theorem rows1_7_v : rows1_7.all validRow = true := by decide +kernel
def rows1 : List TerminalRow := rows1_0 ++ rows1_1 ++ rows1_2 ++ rows1_3 ++ rows1_4 ++ rows1_5 ++ rows1_6 ++ rows1_7
private theorem rows1_v : rows1.all validRow = true := by simp only [rows1,List.all_append,rows1_0_v,rows1_1_v,rows1_2_v,rows1_3_v,rows1_4_v,rows1_5_v,rows1_6_v,rows1_7_v,Bool.and_self]
private def rows2_0 : List TerminalRow := [
  ⟨⟨2,2,6863⟩,248115233128679128,none,none⟩,
  ⟨⟨2,3,6840⟩,248132200196970608,none,none⟩,
  ⟨⟨2,4,6817⟩,248149181700690077,none,none⟩,
  ⟨⟨2,5,6794⟩,248166177639837538,none,none⟩,
  ⟨⟨2,6,6770⟩,248183188014412986,none,none⟩,
  ⟨⟨2,7,6746⟩,248200212824416426,none,none⟩,
  ⟨⟨2,8,6723⟩,248217252069847854,none,none⟩,
  ⟨⟨2,9,6699⟩,248234305750707275,none,none⟩]
private theorem rows2_0_v : rows2_0.all validRow = true := by decide +kernel
private def rows2_1 : List TerminalRow := [
  ⟨⟨2,10,6675⟩,248251373866994686,none,none⟩,
  ⟨⟨2,11,6650⟩,248268456418710084,none,none⟩,
  ⟨⟨2,12,6626⟩,248285553405853475,none,none⟩,
  ⟨⟨2,13,6601⟩,248302664828424856,none,none⟩,
  ⟨⟨2,14,6576⟩,248319790686424227,none,none⟩,
  ⟨⟨2,15,6551⟩,248336930979851587,none,none⟩,
  ⟨⟨2,16,6526⟩,248354085708706938,none,none⟩,
  ⟨⟨2,17,6500⟩,248371254872990277,none,none⟩]
private theorem rows2_1_v : rows2_1.all validRow = true := by decide +kernel
private def rows2_2 : List TerminalRow := [
  ⟨⟨2,18,6474⟩,248388438472701608,none,none⟩,
  ⟨⟨2,19,6448⟩,248405636507840928,none,none⟩,
  ⟨⟨2,20,6422⟩,248422848978408241,none,none⟩,
  ⟨⟨2,21,6396⟩,248440075884403541,none,none⟩,
  ⟨⟨2,22,6369⟩,248457317225826833,none,none⟩,
  ⟨⟨2,23,6342⟩,248474573002678114,none,none⟩,
  ⟨⟨2,24,6315⟩,248491843214957385,none,none⟩,
  ⟨⟨2,25,6287⟩,248509127862664648,none,none⟩]
private theorem rows2_2_v : rows2_2.all validRow = true := by decide +kernel
private def rows2_3 : List TerminalRow := [
  ⟨⟨2,26,6259⟩,248526426945799899,none,none⟩,
  ⟨⟨2,27,6231⟩,248543740464363140,none,none⟩,
  ⟨⟨2,28,6203⟩,248561068418354372,none,none⟩,
  ⟨⟨2,29,6174⟩,248578410807773594,none,none⟩,
  ⟨⟨2,30,6145⟩,248595767632620807,none,none⟩,
  ⟨⟨2,31,6116⟩,248613138892896008,none,none⟩,
  ⟨⟨2,32,6086⟩,248630524588599200,none,none⟩,
  ⟨⟨2,33,6057⟩,248647924719730382,none,none⟩]
private theorem rows2_3_v : rows2_3.all validRow = true := by decide +kernel
private def rows2_4 : List TerminalRow := [
  ⟨⟨2,34,6026⟩,248665339286289555,none,none⟩,
  ⟨⟨2,35,5996⟩,248682768288276717,none,none⟩,
  ⟨⟨2,36,5965⟩,248700211725691872,none,none⟩,
  ⟨⟨2,37,5933⟩,248717669598535013,none,none⟩,
  ⟨⟨2,38,5901⟩,248735141906806144,none,none⟩,
  ⟨⟨2,39,5869⟩,248752628650505269,none,none⟩,
  ⟨⟨2,40,5836⟩,248770129829632382,none,none⟩,
  ⟨⟨2,41,5803⟩,248787645444187485,none,none⟩]
private theorem rows2_4_v : rows2_4.all validRow = true := by decide +kernel
private def rows2_5 : List TerminalRow := [
  ⟨⟨2,42,5769⟩,248805175494170579,none,none⟩,
  ⟨⟨2,43,5735⟩,248822719979581661,none,none⟩,
  ⟨⟨2,44,5690⟩,248840278900420735,none,none⟩,
  ⟨⟨2,45,5639⟩,248857852256687799,none,none⟩,
  ⟨⟨2,46,5588⟩,248875440048382851,none,none⟩,
  ⟨⟨2,47,5534⟩,248893042275505896,none,none⟩,
  ⟨⟨2,48,5480⟩,248910658938056931,none,none⟩,
  ⟨⟨2,49,5423⟩,248928290036035954,none,none⟩]
private theorem rows2_5_v : rows2_5.all validRow = true := by decide +kernel
private def rows2_6 : List TerminalRow := [
  ⟨⟨2,50,5365⟩,248945935569442968,none,none⟩,
  ⟨⟨2,51,5305⟩,248963595538277972,none,none⟩,
  ⟨⟨2,52,5239⟩,248981269942540967,none,none⟩,
  ⟨⟨2,53,5122⟩,248998958782231952,none,none⟩,
  ⟨⟨2,54,4713⟩,249016662057350925,none,none⟩,
  ⟨⟨2,55,4285⟩,249034379767897891,none,none⟩,
  ⟨⟨2,56,3839⟩,249052111913872845,none,none⟩,
  ⟨⟨2,57,3375⟩,249069858495275790,none,none⟩]
private theorem rows2_6_v : rows2_6.all validRow = true := by decide +kernel
private def rows2_7 : List TerminalRow := [
  ⟨⟨2,58,2892⟩,249087619512106725,none,none⟩,
  ⟨⟨2,59,2390⟩,249105394964365650,none,none⟩,
  ⟨⟨2,60,1870⟩,249123184852052565,none,none⟩,
  ⟨⟨2,61,1332⟩,249140989175167470,none,none⟩,
  ⟨⟨2,62,775⟩,249158807933710366,none,none⟩,
  ⟨⟨2,63,200⟩,249176641127681251,none,none⟩]
private theorem rows2_7_v : rows2_7.all validRow = true := by decide +kernel
def rows2 : List TerminalRow := rows2_0 ++ rows2_1 ++ rows2_2 ++ rows2_3 ++ rows2_4 ++ rows2_5 ++ rows2_6 ++ rows2_7
private theorem rows2_v : rows2.all validRow = true := by simp only [rows2,List.all_append,rows2_0_v,rows2_1_v,rows2_2_v,rows2_3_v,rows2_4_v,rows2_5_v,rows2_6_v,rows2_7_v,Bool.and_self]
private def rows3_0 : List TerminalRow := [
  ⟨⟨3,3,6755⟩,248137851117142925,none,none⟩,
  ⟨⟨3,4,6731⟩,248166123724504565,none,none⟩,
  ⟨⟨3,5,6708⟩,248194410767294194,none,none⟩,
  ⟨⟨3,6,6684⟩,248222712245511813,none,none⟩,
  ⟨⟨3,7,6661⟩,248251028159157424,none,none⟩,
  ⟨⟨3,8,6637⟩,248279358508231023,none,none⟩,
  ⟨⟨3,9,6613⟩,248307703292732612,none,none⟩,
  ⟨⟨3,10,6588⟩,248336062512662192,none,none⟩]
private theorem rows3_0_v : rows3_0.all validRow = true := by decide +kernel
private def rows3_1 : List TerminalRow := [
  ⟨⟨3,11,6564⟩,248364436168019763,none,none⟩,
  ⟨⟨3,12,6539⟩,248392824258805324,none,none⟩,
  ⟨⟨3,13,6515⟩,248421226785018874,none,none⟩,
  ⟨⟨3,14,6489⟩,248449643746660414,none,none⟩,
  ⟨⟨3,15,6464⟩,248478075143729945,none,none⟩,
  ⟨⟨3,16,6439⟩,248506520976227465,none,none⟩,
  ⟨⟨3,17,6413⟩,248534981244152975,none,none⟩,
  ⟨⟨3,18,6387⟩,248563455947506477,none,none⟩]
private theorem rows3_1_v : rows3_1.all validRow = true := by decide +kernel
private def rows3_2 : List TerminalRow := [
  ⟨⟨3,19,6361⟩,248591945086287967,none,none⟩,
  ⟨⟨3,20,6335⟩,248620448660497449,none,none⟩,
  ⟨⟨3,21,6308⟩,248648966670134919,none,none⟩,
  ⟨⟨3,22,6281⟩,248677499115200381,none,none⟩,
  ⟨⟨3,23,6254⟩,248706045995693832,none,none⟩,
  ⟨⟨3,24,6227⟩,248734607311615274,none,none⟩,
  ⟨⟨3,25,6199⟩,248763183062964706,none,none⟩,
  ⟨⟨3,26,6171⟩,248791773249742128,none,none⟩]
private theorem rows3_2_v : rows3_2.all validRow = true := by decide +kernel
private def rows3_3 : List TerminalRow := [
  ⟨⟨3,27,6143⟩,248820377871947539,none,none⟩,
  ⟨⟨3,28,6114⟩,248848996929580941,none,none⟩,
  ⟨⟨3,29,6085⟩,248877630422642332,none,none⟩,
  ⟨⟨3,30,6056⟩,248906278351131714,none,none⟩,
  ⟨⟨3,31,6027⟩,248934940715049087,none,none⟩,
  ⟨⟨3,32,5997⟩,248963617514394450,none,none⟩,
  ⟨⟨3,33,5967⟩,248992308749167801,none,none⟩,
  ⟨⟨3,34,5936⟩,249021014419369144,none,none⟩]
private theorem rows3_3_v : rows3_3.all validRow = true := by decide +kernel
private def rows3_4 : List TerminalRow := [
  ⟨⟨3,35,5905⟩,249049734524998477,none,none⟩,
  ⟨⟨3,36,5874⟩,249078469066055799,none,none⟩,
  ⟨⟨3,37,5842⟩,249107218042541113,none,none⟩,
  ⟨⟨3,38,5810⟩,249135981454454414,none,none⟩,
  ⟨⟨3,39,5778⟩,249164759301795708,none,none⟩,
  ⟨⟨3,40,5745⟩,249193551584564992,none,none⟩,
  ⟨⟨3,41,5711⟩,249222358302762264,none,none⟩,
  ⟨⟨3,42,5667⟩,249251179456387528,none,none⟩]
private theorem rows3_4_v : rows3_4.all validRow = true := by decide +kernel
private def rows3_5 : List TerminalRow := [
  ⟨⟨3,43,5619⟩,249280015045440780,none,none⟩,
  ⟨⟨3,44,5569⟩,249308865069922025,none,none⟩,
  ⟨⟨3,45,5517⟩,249337729529831258,none,none⟩,
  ⟨⟨3,46,5465⟩,249366608425168482,none,none⟩,
  ⟨⟨3,47,5411⟩,249395501755933695,none,none⟩,
  ⟨⟨3,48,5355⟩,249424409522126900,none,none⟩,
  ⟨⟨3,49,5298⟩,249453331723748094,none,none⟩,
  ⟨⟨3,50,5238⟩,249482268360797277,none,none⟩]
private theorem rows3_5_v : rows3_5.all validRow = true := by decide +kernel
private def rows3_6 : List TerminalRow := [
  ⟨⟨3,51,5170⟩,249511219433274452,none,none⟩,
  ⟨⟨3,52,5035⟩,249540184941179617,none,none⟩,
  ⟨⟨3,53,4632⟩,249569164884512772,none,none⟩,
  ⟨⟨3,54,4212⟩,249598159263273916,none,none⟩,
  ⟨⟨3,55,3773⟩,249627168077463050,none,none⟩,
  ⟨⟨3,56,3315⟩,249656191327080175,none,none⟩,
  ⟨⟨3,57,2839⟩,249685229012125288,none,none⟩,
  ⟨⟨3,58,2345⟩,249714281132598394,none,none⟩]
private theorem rows3_6_v : rows3_6.all validRow = true := by decide +kernel
private def rows3_7 : List TerminalRow := [
  ⟨⟨3,59,1832⟩,249743347688499491,none,none⟩,
  ⟨⟨3,60,1301⟩,249772428679828574,none,none⟩,
  ⟨⟨3,61,751⟩,249801524106585651,none,none⟩,
  ⟨⟨3,62,183⟩,249830633968770716,none,none⟩]
private theorem rows3_7_v : rows3_7.all validRow = true := by decide +kernel
def rows3 : List TerminalRow := rows3_0 ++ rows3_1 ++ rows3_2 ++ rows3_3 ++ rows3_4 ++ rows3_5 ++ rows3_6 ++ rows3_7
private theorem rows3_v : rows3.all validRow = true := by simp only [rows3,List.all_append,rows3_0_v,rows3_1_v,rows3_2_v,rows3_3_v,rows3_4_v,rows3_5_v,rows3_6_v,rows3_7_v,Bool.and_self]
private def rows4_0 : List TerminalRow := [
  ⟨⟨4,4,6643⟩,248171774644676882,none,none⟩,
  ⟨⟨4,5,6620⟩,248211352791108681,none,none⟩,
  ⟨⟨4,6,6596⟩,248250945372968470,none,none⟩,
  ⟨⟨4,7,6572⟩,248290552390256250,none,none⟩,
  ⟨⟨4,8,6548⟩,248330173842972021,none,none⟩,
  ⟨⟨4,9,6524⟩,248369809731115781,none,none⟩,
  ⟨⟨4,10,6499⟩,248409460054687530,none,none⟩,
  ⟨⟨4,11,6475⟩,248449124813687271,none,none⟩]
private theorem rows4_0_v : rows4_0.all validRow = true := by decide +kernel
private def rows4_1 : List TerminalRow := [
  ⟨⟨4,12,6450⟩,248488804008115001,none,none⟩,
  ⟨⟨4,13,6425⟩,248528497637970721,none,none⟩,
  ⟨⟨4,14,6400⟩,248568205703254432,none,none⟩,
  ⟨⟨4,15,6374⟩,248607928203966132,none,none⟩,
  ⟨⟨4,16,6349⟩,248647665140105823,none,none⟩,
  ⟨⟨4,17,6323⟩,248687416511673504,none,none⟩,
  ⟨⟨4,18,6297⟩,248727182318669174,none,none⟩,
  ⟨⟨4,19,6271⟩,248766962561092834,none,none⟩]
private theorem rows4_1_v : rows4_1.all validRow = true := by decide +kernel
private def rows4_2 : List TerminalRow := [
  ⟨⟨4,20,6244⟩,248806757238944487,none,none⟩,
  ⟨⟨4,21,6217⟩,248846566352224127,none,none⟩,
  ⟨⟨4,22,6190⟩,248886389900931758,none,none⟩,
  ⟨⟨4,23,6163⟩,248926227885067379,none,none⟩,
  ⟨⟨4,24,6135⟩,248966080304630992,none,none⟩,
  ⟨⟨4,25,6107⟩,249005947159622594,none,none⟩,
  ⟨⟨4,26,6079⟩,249045828450042185,none,none⟩,
  ⟨⟨4,27,6051⟩,249085724175889767,none,none⟩]
private theorem rows4_2_v : rows4_2.all validRow = true := by decide +kernel
private def rows4_3 : List TerminalRow := [
  ⟨⟨4,28,6022⟩,249125634337165339,none,none⟩,
  ⟨⟨4,29,5993⟩,249165558933868902,none,none⟩,
  ⟨⟨4,30,5964⟩,249205497966000454,none,none⟩,
  ⟨⟨4,31,5934⟩,249245451433559995,none,none⟩,
  ⟨⟨4,32,5904⟩,249285419336547527,none,none⟩,
  ⟨⟨4,33,5873⟩,249325401674963050,none,none⟩,
  ⟨⟨4,34,5843⟩,249365398448806563,none,none⟩,
  ⟨⟨4,35,5811⟩,249405409658078066,none,none⟩]
private theorem rows4_3_v : rows4_3.all validRow = true := by decide +kernel
private def rows4_4 : List TerminalRow := [
  ⟨⟨4,36,5780⟩,249445435302777557,none,none⟩,
  ⟨⟨4,37,5748⟩,249485475382905041,none,none⟩,
  ⟨⟨4,38,5715⟩,249525529898460514,none,none⟩,
  ⟨⟨4,39,5682⟩,249565598849443977,none,none⟩,
  ⟨⟨4,40,5637⟩,249605682235855431,none,none⟩,
  ⟨⟨4,41,5590⟩,249645780057694873,none,none⟩,
  ⟨⟨4,42,5541⟩,249685892314962306,none,none⟩,
  ⟨⟨4,43,5492⟩,249726019007657730,none,none⟩]
private theorem rows4_4_v : rows4_4.all validRow = true := by decide +kernel
private def rows4_5 : List TerminalRow := [
  ⟨⟨4,44,5441⟩,249766160135781144,none,none⟩,
  ⟨⟨4,45,5389⟩,249806315699332548,none,none⟩,
  ⟨⟨4,46,5335⟩,249846485698311941,none,none⟩,
  ⟨⟨4,47,5280⟩,249886670132719325,none,none⟩,
  ⟨⟨4,48,5223⟩,249926869002554700,none,none⟩,
  ⟨⟨4,49,5164⟩,249967082307818064,none,none⟩,
  ⟨⟨4,50,5091⟩,250007310048509418,none,none⟩,
  ⟨⟨4,51,4907⟩,250047552224628762,none,none⟩]
private theorem rows4_5_v : rows4_5.all validRow = true := by decide +kernel
private def rows4_6 : List TerminalRow := [
  ⟨⟨4,52,4511⟩,250087808836176097,none,none⟩,
  ⟨⟨4,53,4097⟩,250128079883151420,none,none⟩,
  ⟨⟨4,54,3665⟩,250168365365554736,none,none⟩,
  ⟨⟨4,55,3214⟩,250208665283386041,none,none⟩,
  ⟨⟨4,56,2744⟩,250248979636645335,none,none⟩,
  ⟨⟨4,57,2256⟩,250289308425332620,none,none⟩,
  ⟨⟨4,58,1750⟩,250329651649447896,none,none⟩,
  ⟨⟨4,59,1226⟩,250370009308991160,none,none⟩]
private theorem rows4_6_v : rows4_6.all validRow = true := by decide +kernel
private def rows4_7 : List TerminalRow := [
  ⟨⟨4,60,683⟩,250410381403962414,none,none⟩,
  ⟨⟨4,61,121⟩,250450767934361661,none,none⟩]
private theorem rows4_7_v : rows4_7.all validRow = true := by decide +kernel
def rows4 : List TerminalRow := rows4_0 ++ rows4_1 ++ rows4_2 ++ rows4_3 ++ rows4_4 ++ rows4_5 ++ rows4_6 ++ rows4_7
private theorem rows4_v : rows4.all validRow = true := by simp only [rows4,List.all_append,rows4_0_v,rows4_1_v,rows4_2_v,rows4_3_v,rows4_4_v,rows4_5_v,rows4_6_v,rows4_7_v,Bool.and_self]
private def rows5_0 : List TerminalRow := [
  ⟨⟨5,5,6528⟩,248217003711280998,none,none⟩,
  ⟨⟨5,6,6504⟩,248267887396782957,none,none⟩,
  ⟨⟨5,7,6480⟩,248318785517712908,none,none⟩,
  ⟨⟨5,8,6456⟩,248369698074070848,none,none⟩,
  ⟨⟨5,9,6432⟩,248420625065856778,none,none⟩,
  ⟨⟨5,10,6407⟩,248471566493070698,none,none⟩,
  ⟨⟨5,11,6382⟩,248522522355712608,none,none⟩,
  ⟨⟨5,12,6357⟩,248573492653782509,none,none⟩]
private theorem rows5_0_v : rows5_0.all validRow = true := by decide +kernel
private def rows5_1 : List TerminalRow := [
  ⟨⟨5,13,6332⟩,248624477387280399,none,none⟩,
  ⟨⟨5,14,6307⟩,248675476556206279,none,none⟩,
  ⟨⟨5,15,6281⟩,248726490160560149,none,none⟩,
  ⟨⟨5,16,6255⟩,248777518200342012,none,none⟩,
  ⟨⟨5,17,6229⟩,248828560675551862,none,none⟩,
  ⟨⟨5,18,6203⟩,248879617586189702,none,none⟩,
  ⟨⟨5,19,6177⟩,248930688932255533,none,none⟩,
  ⟨⟨5,20,6150⟩,248981774713749353,none,none⟩]
private theorem rows5_1_v : rows5_1.all validRow = true := by decide +kernel
private def rows5_2 : List TerminalRow := [
  ⟨⟨5,21,6123⟩,249032874930671166,none,none⟩,
  ⟨⟨5,22,6096⟩,249083989583020968,none,none⟩,
  ⟨⟨5,23,6068⟩,249135118670798759,none,none⟩,
  ⟨⟨5,24,6040⟩,249186262194004540,none,none⟩,
  ⟨⟨5,25,6012⟩,249237420152638312,none,none⟩,
  ⟨⟨5,26,5984⟩,249288592546700074,none,none⟩,
  ⟨⟨5,27,5955⟩,249339779376189826,none,none⟩,
  ⟨⟨5,28,5926⟩,249390980641107567,none,none⟩]
private theorem rows5_2_v : rows5_2.all validRow = true := by decide +kernel
private def rows5_3 : List TerminalRow := [
  ⟨⟨5,29,5897⟩,249442196341453300,none,none⟩,
  ⟨⟨5,30,5867⟩,249493426477227022,none,none⟩,
  ⟨⟨5,31,5837⟩,249544671048428733,none,none⟩,
  ⟨⟨5,32,5807⟩,249595930055058437,none,none⟩,
  ⟨⟨5,33,5776⟩,249647203497116129,none,none⟩,
  ⟨⟨5,34,5745⟩,249698491374601812,none,none⟩,
  ⟨⟨5,35,5714⟩,249749793687515484,none,none⟩,
  ⟨⟨5,36,5682⟩,249801110435857147,none,none⟩]
private theorem rows5_3_v : rows5_3.all validRow = true := by decide +kernel
private def rows5_4 : List TerminalRow := [
  ⟨⟨5,37,5645⟩,249852441619626800,none,none⟩,
  ⟨⟨5,38,5599⟩,249903787238824442,none,none⟩,
  ⟨⟨5,39,5553⟩,249955147293450077,none,none⟩,
  ⟨⟨5,40,5506⟩,250006521783503701,none,none⟩,
  ⟨⟨5,41,5457⟩,250057910708985313,none,none⟩,
  ⟨⟨5,42,5408⟩,250109314069894916,none,none⟩,
  ⟨⟨5,43,5358⟩,250160731866232509,none,none⟩,
  ⟨⟨5,44,5306⟩,250212164097998093,(some (2,2,2)),none⟩]
private theorem rows5_4_v : rows5_4.all validRow = true := by decide +kernel
private def rows5_5 : List TerminalRow := [
  ⟨⟨5,45,5252⟩,250263610765191668,(some (2,2,2)),none⟩,
  ⟨⟨5,46,5198⟩,250315071867813230,(some (2,2,2)),none⟩,
  ⟨⟨5,47,5141⟩,250366547405862786,(some (2,2,2)),none⟩,
  ⟨⟨5,48,5076⟩,250418037379340329,(some (2,2,2)),none⟩,
  ⟨⟨5,49,5002⟩,250469541788245863,(some (2,2,2)),none⟩,
  ⟨⟨5,50,4733⟩,250521060632579386,(some (2,2,2)),none⟩,
  ⟨⟨5,51,4343⟩,250572593912340903,none,none⟩,
  ⟨⟨5,52,3934⟩,250624141627530406,none,none⟩]
private theorem rows5_5_v : rows5_5.all validRow = true := by decide +kernel
private def rows5_6 : List TerminalRow := [
  ⟨⟨5,53,3508⟩,250675703778147902,none,none⟩,
  ⟨⟨5,54,3063⟩,250727280364193385,none,none⟩,
  ⟨⟨5,55,2600⟩,250778871385666860,none,none⟩,
  ⟨⟨5,56,2118⟩,250830476842568325,none,none⟩,
  ⟨⟨5,57,1618⟩,250882096734897781,none,none⟩,
  ⟨⟨5,58,1100⟩,250933731062655225,none,none⟩,
  ⟨⟨5,59,564⟩,250985379825840661,none,none⟩]
private theorem rows5_6_v : rows5_6.all validRow = true := by decide +kernel
def rows5 : List TerminalRow := rows5_0 ++ rows5_1 ++ rows5_2 ++ rows5_3 ++ rows5_4 ++ rows5_5 ++ rows5_6
private theorem rows5_v : rows5.all validRow = true := by simp only [rows5,List.all_append,rows5_0_v,rows5_1_v,rows5_2_v,rows5_3_v,rows5_4_v,rows5_5_v,rows5_6_v,Bool.and_self]
private def rows6_0 : List TerminalRow := [
  ⟨⟨6,6,6409⟩,248273538316955275,none,none⟩,
  ⟨⟨6,7,6385⟩,248335727541527395,none,none⟩,
  ⟨⟨6,8,6360⟩,248397931201527505,none,none⟩,
  ⟨⟨6,9,6336⟩,248460149296955605,none,none⟩,
  ⟨⟨6,10,6311⟩,248522381827811695,none,none⟩,
  ⟨⟨6,11,6286⟩,248584628794095776,none,none⟩,
  ⟨⟨6,12,6261⟩,248646890195807845,none,none⟩,
  ⟨⟨6,13,6236⟩,248709166032947906,none,none⟩]
private theorem rows6_0_v : rows6_0.all validRow = true := by decide +kernel
private def rows6_1 : List TerminalRow := [
  ⟨⟨6,14,6210⟩,248771456305515956,none,none⟩,
  ⟨⟨6,15,6184⟩,248833761013511998,none,none⟩,
  ⟨⟨6,16,6158⟩,248896080156936028,none,none⟩,
  ⟨⟨6,17,6132⟩,248958413735788049,none,none⟩,
  ⟨⟨6,18,6106⟩,249020761750068060,none,none⟩,
  ⟨⟨6,19,6079⟩,249083124199776060,none,none⟩,
  ⟨⟨6,20,6052⟩,249145501084912053,none,none⟩,
  ⟨⟨6,21,6025⟩,249207892405476033,none,none⟩]
private theorem rows6_1_v : rows6_1.all validRow = true := by decide +kernel
private def rows6_2 : List TerminalRow := [
  ⟨⟨6,22,5997⟩,249270298161468006,none,none⟩,
  ⟨⟨6,23,5969⟩,249332718352887967,none,none⟩,
  ⟨⟨6,24,5941⟩,249395152979735918,none,none⟩,
  ⟨⟨6,25,5913⟩,249457602042011861,none,none⟩,
  ⟨⟨6,26,5884⟩,249520065539715791,none,none⟩,
  ⟨⟨6,27,5855⟩,249582543472847713,none,none⟩,
  ⟨⟨6,28,5826⟩,249645035841407627,none,none⟩,
  ⟨⟨6,29,5796⟩,249707542645395528,none,none⟩]
private theorem rows6_2_v : rows6_2.all validRow = true := by decide +kernel
private def rows6_3 : List TerminalRow := [
  ⟨⟨6,30,5767⟩,249770063884811420,none,none⟩,
  ⟨⟨6,31,5736⟩,249832599559655302,none,none⟩,
  ⟨⟨6,32,5706⟩,249895149669927175,none,none⟩,
  ⟨⟨6,33,5675⟩,249957714215627038,none,none⟩,
  ⟨⟨6,34,5640⟩,250020293196754890,none,none⟩,
  ⟨⟨6,35,5597⟩,250082886613310733,(some (2,2,2)),none⟩,
  ⟨⟨6,36,5553⟩,250145494465294567,(some (2,2,2)),none⟩,
  ⟨⟨6,37,5507⟩,250208116752706388,(some (2,2,2)),none⟩]
private theorem rows6_3_v : rows6_3.all validRow = true := by decide +kernel
private def rows6_4 : List TerminalRow := [
  ⟨⟨6,38,5461⟩,250270753475546202,(some (2,2,2)),none⟩,
  ⟨⟨6,39,5414⟩,250333404633814005,(some (2,2,2)),none⟩,
  ⟨⟨6,40,5366⟩,250396070227509799,(some (2,2,2)),none⟩,
  ⟨⟨6,41,5317⟩,250458750256633583,(some (2,2,2)),none⟩,
  ⟨⟨6,42,5266⟩,250521444721185354,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨6,43,5214⟩,250584153621165120,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨6,44,5161⟩,250646876956572874,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨6,45,5107⟩,250709614727408617,(some (2,2,2)),(some (2,2,2))⟩]
private theorem rows6_4_v : rows6_4.all validRow = true := by decide +kernel
private def rows6_5 : List TerminalRow := [
  ⟨⟨6,46,5045⟩,250772366933672350,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨6,47,4975⟩,250835133575364075,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨6,48,4869⟩,250897914652483789,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨6,49,4502⟩,250960710165031494,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨6,50,4117⟩,251023520113007187,(some (2,2,2)),none⟩,
  ⟨⟨6,51,3714⟩,251086344496410871,none,none⟩,
  ⟨⟨6,52,3293⟩,251149183315242546,none,none⟩,
  ⟨⟨6,53,2854⟩,251212036569502211,none,none⟩]
private theorem rows6_5_v : rows6_5.all validRow = true := by decide +kernel
private def rows6_6 : List TerminalRow := [
  ⟨⟨6,54,2396⟩,251274904259189865,none,none⟩,
  ⟨⟨6,55,1921⟩,251337786384305511,none,none⟩,
  ⟨⟨6,56,1428⟩,251400682944849146,none,none⟩,
  ⟨⟨6,57,916⟩,251463593940820770,none,none⟩,
  ⟨⟨6,58,386⟩,251526519372220386,none,none⟩]
private theorem rows6_6_v : rows6_6.all validRow = true := by decide +kernel
def rows6 : List TerminalRow := rows6_0 ++ rows6_1 ++ rows6_2 ++ rows6_3 ++ rows6_4 ++ rows6_5 ++ rows6_6
private theorem rows6_v : rows6.all validRow = true := by simp only [rows6,List.all_append,rows6_0_v,rows6_1_v,rows6_2_v,rows6_3_v,rows6_4_v,rows6_5_v,rows6_6_v,Bool.and_self]
private def rows7_0 : List TerminalRow := [
  ⟨⟨7,7,6286⟩,248341378461699712,none,none⟩,
  ⟨⟨7,8,6261⟩,248414873225341991,none,none⟩,
  ⟨⟨7,9,6236⟩,248488382424412263,none,none⟩,
  ⟨⟨7,10,6211⟩,248561906058910523,none,none⟩,
  ⟨⟨7,11,6186⟩,248635444128836773,none,none⟩,
  ⟨⟨7,12,6161⟩,248708996634191013,none,none⟩,
  ⟨⟨7,13,6135⟩,248782563574973244,none,none⟩,
  ⟨⟨7,14,6109⟩,248856144951183465,none,none⟩]
private theorem rows7_0_v : rows7_0.all validRow = true := by decide +kernel
private def rows7_1 : List TerminalRow := [
  ⟨⟨7,15,6083⟩,248929740762821674,none,none⟩,
  ⟨⟨7,16,6057⟩,249003351009887876,none,none⟩,
  ⟨⟨7,17,6031⟩,249076975692382067,none,none⟩,
  ⟨⟨7,18,6004⟩,249150614810304248,none,none⟩,
  ⟨⟨7,19,5977⟩,249224268363654419,none,none⟩,
  ⟨⟨7,20,5950⟩,249297936352432580,none,none⟩,
  ⟨⟨7,21,5922⟩,249371618776638732,none,none⟩,
  ⟨⟨7,22,5894⟩,249445315636272874,none,none⟩]
private theorem rows7_1_v : rows7_1.all validRow = true := by decide +kernel
private def rows7_2 : List TerminalRow := [
  ⟨⟨7,23,5866⟩,249519026931335005,none,none⟩,
  ⟨⟨7,24,5838⟩,249592752661825126,none,none⟩,
  ⟨⟨7,25,5809⟩,249666492827743239,none,none⟩,
  ⟨⟨7,26,5780⟩,249740247429089341,none,none⟩,
  ⟨⟨7,27,5751⟩,249814016465863433,none,none⟩,
  ⟨⟨7,28,5721⟩,249887799938065514,none,none⟩,
  ⟨⟨7,29,5692⟩,249961597845695586,none,none⟩,
  ⟨⟨7,30,5661⟩,250035410188753649,none,none⟩]
private theorem rows7_2_v : rows7_2.all validRow = true := by decide +kernel
private def rows7_3 : List TerminalRow := [
  ⟨⟨7,31,5625⟩,250109236967239702,(some (2,2,2)),none⟩,
  ⟨⟨7,32,5583⟩,250183078181153744,(some (2,2,2)),none⟩,
  ⟨⟨7,33,5540⟩,250256933830495776,(some (2,2,2)),none⟩,
  ⟨⟨7,34,5497⟩,250330803915265800,(some (2,2,2)),none⟩,
  ⟨⟨7,35,5452⟩,250404688435463813,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,36,5407⟩,250478587391089815,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,37,5361⟩,250552500782143808,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,38,5314⟩,250626428608625791,(some (2,2,2)),(some (2,2,2))⟩]
private theorem rows7_3_v : rows7_3.all validRow = true := by decide +kernel
private def rows7_4 : List TerminalRow := [
  ⟨⟨7,39,5265⟩,250700370870535764,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,40,5216⟩,250774327567873726,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,41,5166⟩,250848298700639681,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,42,5114⟩,250922284268833624,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,43,5061⟩,250996284272455558,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,44,4998⟩,251070298711505482,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,45,4931⟩,251144327585983396,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,46,4851⟩,251218370895889300,(some (2,2,2)),(some (2,2,2))⟩]
private theorem rows7_4_v : rows7_4.all validRow = true := by decide +kernel
private def rows7_5 : List TerminalRow := [
  ⟨⟨7,47,4562⟩,251292428641223194,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,48,4199⟩,251366500821985079,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,49,3820⟩,251440587438174952,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨7,50,3422⟩,251514688489792816,(some (2,2,2)),none⟩,
  ⟨⟨7,51,3007⟩,251588803976838671,none,none⟩,
  ⟨⟨7,52,2573⟩,251662933899312516,none,none⟩,
  ⟨⟨7,53,2122⟩,251737078257214350,none,none⟩,
  ⟨⟨7,54,1653⟩,251811237050544175,none,none⟩]
private theorem rows7_5_v : rows7_5.all validRow = true := by decide +kernel
private def rows7_6 : List TerminalRow := [
  ⟨⟨7,55,1166⟩,251885410279301991,none,none⟩,
  ⟨⟨7,56,660⟩,251959597943487795,none,none⟩,
  ⟨⟨7,57,137⟩,252033800043101591,none,none⟩]
private theorem rows7_6_v : rows7_6.all validRow = true := by decide +kernel
def rows7 : List TerminalRow := rows7_0 ++ rows7_1 ++ rows7_2 ++ rows7_3 ++ rows7_4 ++ rows7_5 ++ rows7_6
private theorem rows7_v : rows7.all validRow = true := by simp only [rows7,List.all_append,rows7_0_v,rows7_1_v,rows7_2_v,rows7_3_v,rows7_4_v,rows7_5_v,rows7_6_v,Bool.and_self]
private def rows8_0 : List TerminalRow := [
  ⟨⟨8,8,6157⟩,248420524145514310,none,none⟩,
  ⟨⟨8,9,6132⟩,248505324448226749,none,none⟩,
  ⟨⟨8,10,6107⟩,248590139186367181,none,none⟩,
  ⟨⟨8,11,6081⟩,248674968359935599,none,none⟩,
  ⟨⟨8,12,6056⟩,248759811968932011,none,none⟩,
  ⟨⟨8,13,6030⟩,248844670013356410,none,none⟩,
  ⟨⟨8,14,6004⟩,248929542493208801,none,none⟩,
  ⟨⟨8,15,5978⟩,249014429408489181,none,none⟩]
private theorem rows8_0_v : rows8_0.all validRow = true := by decide +kernel
private def rows8_1 : List TerminalRow := [
  ⟨⟨8,16,5951⟩,249099330759197554,none,none⟩,
  ⟨⟨8,17,5924⟩,249184246545333915,none,none⟩,
  ⟨⟨8,18,5897⟩,249269176766898267,none,none⟩,
  ⟨⟨8,19,5870⟩,249354121423890606,none,none⟩,
  ⟨⟨8,20,5842⟩,249439080516310938,none,none⟩,
  ⟨⟨8,21,5815⟩,249524054044159259,none,none⟩,
  ⟨⟨8,22,5787⟩,249609042007435571,none,none⟩,
  ⟨⟨8,23,5758⟩,249694044406139873,none,none⟩]
private theorem rows8_1_v : rows8_1.all validRow = true := by decide +kernel
private def rows8_2 : List TerminalRow := [
  ⟨⟨8,24,5729⟩,249779061240272164,none,none⟩,
  ⟨⟨8,25,5701⟩,249864092509832446,none,none⟩,
  ⟨⟨8,26,5671⟩,249949138214820718,none,none⟩,
  ⟨⟨8,27,5639⟩,250034198355236981,none,none⟩,
  ⟨⟨8,28,5599⟩,250119272931081234,(some (2,2,2)),none⟩,
  ⟨⟨8,29,5558⟩,250204361942353474,(some (2,2,2)),none⟩,
  ⟨⟨8,30,5516⟩,250289465389053708,(some (2,2,2)),none⟩,
  ⟨⟨8,31,5474⟩,250374583271181930,(some (2,2,2)),(some (2,2,2))⟩]
private theorem rows8_2_v : rows8_2.all validRow = true := by decide +kernel
private def rows8_3 : List TerminalRow := [
  ⟨⟨8,32,5431⟩,250459715588738142,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨8,33,5387⟩,250544862341722345,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨8,34,5342⟩,250630023530134537,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨8,35,5297⟩,250715199153974721,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨8,36,5250⟩,250800389213242893,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨8,37,5203⟩,250885593707939056,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨8,38,5155⟩,250970812638063210,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨8,39,5105⟩,251056046003615354,(some (2,2,2)),(some (2,2,2))⟩]
private theorem rows8_3_v : rows8_3.all validRow = true := by decide +kernel
private def rows8_4 : List TerminalRow := [
  ⟨⟨8,40,5055⟩,251141293804595485,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨8,41,4997⟩,251226556041003610,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨8,42,4934⟩,251311832712839723,(some (4,4,4)),(some (2,2,2))⟩,
  ⟨⟨8,43,4869⟩,251397123820103828,(some (1,1,5)),(some (2,2,2))⟩,
  ⟨⟨8,44,4784⟩,251482429362795921,(some (1,1,5)),(some (2,2,2))⟩,
  ⟨⟨8,45,4502⟩,251567749340916005,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨8,46,4162⟩,251653083754464078,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨8,47,3805⟩,251738432603440143,(some (2,2,2)),(some (2,2,2))⟩]
private theorem rows8_4_v : rows8_4.all validRow = true := by decide +kernel
private def rows8_5 : List TerminalRow := [
  ⟨⟨8,48,3431⟩,251823795887844198,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨8,49,3039⟩,251909173607676242,(some (2,2,2)),none⟩,
  ⟨⟨8,50,2630⟩,251994565762936276,none,none⟩,
  ⟨⟨8,51,2203⟩,252079972353624300,none,none⟩,
  ⟨⟨8,52,1758⟩,252165393379740316,none,none⟩,
  ⟨⟨8,53,1296⟩,252250828841284319,none,none⟩,
  ⟨⟨8,54,815⟩,252336278738256316,none,none⟩,
  ⟨⟨8,55,317⟩,252421743070656300,none,none⟩]
private theorem rows8_5_v : rows8_5.all validRow = true := by decide +kernel
def rows8 : List TerminalRow := rows8_0 ++ rows8_1 ++ rows8_2 ++ rows8_3 ++ rows8_4 ++ rows8_5
private theorem rows8_v : rows8.all validRow = true := by simp only [rows8,List.all_append,rows8_0_v,rows8_1_v,rows8_2_v,rows8_3_v,rows8_4_v,rows8_5_v,Bool.and_self]
private def rows9_0 : List TerminalRow := [
  ⟨⟨9,9,6023⟩,248510975368399067,none,none⟩,
  ⟨⟨9,10,5997⟩,248607081210181667,none,none⟩,
  ⟨⟨9,11,5972⟩,248703201487392258,none,none⟩,
  ⟨⟨9,12,5946⟩,248799336200030838,none,none⟩,
  ⟨⟨9,13,5920⟩,248895485348097409,none,none⟩,
  ⟨⟨9,14,5893⟩,248991648931591969,none,none⟩,
  ⟨⟨9,15,5867⟩,249087826950514521,none,none⟩,
  ⟨⟨9,16,5840⟩,249184019404865061,none,none⟩]
private theorem rows9_0_v : rows9_0.all validRow = true := by decide +kernel
private def rows9_1 : List TerminalRow := [
  ⟨⟨9,17,5813⟩,249280226294643591,none,none⟩,
  ⟨⟨9,18,5785⟩,249376447619850113,none,none⟩,
  ⟨⟨9,19,5758⟩,249472683380484626,none,none⟩,
  ⟨⟨9,20,5730⟩,249568933576547125,none,none⟩,
  ⟨⟨9,21,5702⟩,249665198208037617,none,none⟩,
  ⟨⟨9,22,5673⟩,249761477274956099,none,none⟩,
  ⟨⟨9,23,5638⟩,249857770777302571,none,none⟩,
  ⟨⟨9,24,5599⟩,249954078715077032,none,none⟩]
private theorem rows9_1_v : rows9_1.all validRow = true := by decide +kernel
private def rows9_2 : List TerminalRow := [
  ⟨⟨9,25,5560⟩,250050401088279484,none,none⟩,
  ⟨⟨9,26,5520⟩,250146737896909927,(some (2,2,2)),none⟩,
  ⟨⟨9,27,5479⟩,250243089140968358,(some (2,2,2)),none⟩,
  ⟨⟨9,28,5438⟩,250339454820454780,(some (2,2,2)),none⟩,
  ⟨⟨9,29,5396⟩,250435834935369193,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,30,5353⟩,250532229485711595,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,31,5310⟩,250628638471481989,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,32,5266⟩,250725061892680371,(some (2,2,2)),(some (2,2,2))⟩]
private theorem rows9_2_v : rows9_2.all validRow = true := by decide +kernel
private def rows9_3 : List TerminalRow := [
  ⟨⟨9,33,5221⟩,250821499749306743,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,34,5175⟩,250917952041361106,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,35,5128⟩,251014418768843458,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,36,5080⟩,251110899931753802,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,37,5032⟩,251207395530092136,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,38,4973⟩,251303905563858458,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,39,4913⟩,251400430033052773,(some (1,1,5)),(some (2,2,2))⟩,
  ⟨⟨9,40,4851⟩,251496968937675075,(some (1,1,5)),(some (2,2,2))⟩]
private theorem rows9_3_v : rows9_3.all validRow = true := by decide +kernel
private def rows9_4 : List TerminalRow := [
  ⟨⟨9,41,4771⟩,251593522277725368,(some (1,3,5)),(some (2,2,0))⟩,
  ⟨⟨9,42,4584⟩,251690090053203652,(some (4,4,4)),(some (2,2,2))⟩,
  ⟨⟨9,43,4284⟩,251786672264109926,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,44,3968⟩,251883268910444190,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,45,3635⟩,251979879992206444,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,46,3285⟩,252076505509396688,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨9,47,2919⟩,252173145462014923,(some (2,2,2)),none⟩,
  ⟨⟨9,48,2535⟩,252269799850061147,none,none⟩]
private theorem rows9_4_v : rows9_4.all validRow = true := by decide +kernel
private def rows9_5 : List TerminalRow := [
  ⟨⟨9,49,2133⟩,252366468673535362,none,none⟩,
  ⟨⟨9,50,1715⟩,252463151932437565,none,none⟩,
  ⟨⟨9,51,1278⟩,252559849626767760,none,none⟩,
  ⟨⟨9,52,824⟩,252656561756525945,none,none⟩,
  ⟨⟨9,53,352⟩,252753288321712120,none,none⟩]
private theorem rows9_5_v : rows9_5.all validRow = true := by decide +kernel
def rows9 : List TerminalRow := rows9_0 ++ rows9_1 ++ rows9_2 ++ rows9_3 ++ rows9_4 ++ rows9_5
private theorem rows9_v : rows9.all validRow = true := by simp only [rows9,List.all_append,rows9_0_v,rows9_1_v,rows9_2_v,rows9_3_v,rows9_4_v,rows9_5_v,Bool.and_self]
private def rows10_0 : List TerminalRow := [
  ⟨⟨10,10,5882⟩,248612732130353983,none,none⟩,
  ⟨⟨10,11,5856⟩,248720143511206745,none,none⟩,
  ⟨⟨10,12,5830⟩,248827569327487495,none,none⟩,
  ⟨⟨10,13,5803⟩,248935009579196236,none,none⟩,
  ⟨⟨10,14,5777⟩,249042464266332966,none,none⟩,
  ⟨⟨10,15,5750⟩,249149933388897687,none,none⟩,
  ⟨⟨10,16,5722⟩,249257416946890399,none,none⟩,
  ⟨⟨10,17,5695⟩,249364914940311100,none,none⟩]
private theorem rows10_0_v : rows10_0.all validRow = true := by decide +kernel
private def rows10_1 : List TerminalRow := [
  ⟨⟨10,18,5660⟩,249472427369159791,none,none⟩,
  ⟨⟨10,19,5623⟩,249579954233436472,none,none⟩,
  ⟨⟨10,20,5585⟩,249687495533141144,none,none⟩,
  ⟨⟨10,21,5547⟩,249795051268273805,none,none⟩,
  ⟨⟨10,22,5508⟩,249902621438834457,none,none⟩,
  ⟨⟨10,23,5469⟩,250010206044823100,none,none⟩,
  ⟨⟨10,24,5429⟩,250117805086239731,none,none⟩,
  ⟨⟨10,25,5389⟩,250225418563084352,(some (2,2,2)),none⟩]
private theorem rows10_1_v : rows10_1.all validRow = true := by decide +kernel
private def rows10_2 : List TerminalRow := [
  ⟨⟨10,26,5347⟩,250333046475356965,(some (2,2,2)),none⟩,
  ⟨⟨10,27,5306⟩,250440688823057567,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,28,5263⟩,250548345606186159,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,29,5220⟩,250656016824742741,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,30,5176⟩,250763702478727312,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,31,5131⟩,250871402568139875,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,32,5085⟩,250979117092980429,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,33,5038⟩,251086846053248971,(some (2,2,2)),(some (2,2,2))⟩]
private theorem rows10_2_v : rows10_2.all validRow = true := by decide +kernel
private def rows10_3 : List TerminalRow := [
  ⟨⟨10,34,4982⟩,251194589448945505,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,35,4925⟩,251302347280070027,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,36,4867⟩,251410119546622541,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,37,4793⟩,251517906248603043,(some (4,4,4)),(some (2,2,2))⟩,
  ⟨⟨10,38,4632⟩,251625707386011537,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,39,4378⟩,251733522958848021,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,40,4113⟩,251841352967112495,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,41,3835⟩,251949197410804957,(some (2,2,2)),(some (2,2,2))⟩]
private theorem rows10_3_v : rows10_3.all validRow = true := by decide +kernel
private def rows10_4 : List TerminalRow := [
  ⟨⟨10,42,3545⟩,252057056289925412,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,43,3240⟩,252164929604473854,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,44,2920⟩,252272817354450290,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨10,45,2583⟩,252380719539854714,none,none⟩,
  ⟨⟨10,46,2229⟩,252488636160687127,none,none⟩,
  ⟨⟨10,47,1858⟩,252596567216947532,none,none⟩,
  ⟨⟨10,48,1470⟩,252704512708635926,none,none⟩,
  ⟨⟨10,49,1064⟩,252812472635752312,none,none⟩]
private theorem rows10_4_v : rows10_4.all validRow = true := by decide +kernel
private def rows10_5 : List TerminalRow := [
  ⟨⟨10,50,640⟩,252920446998296685,none,none⟩,
  ⟨⟨10,51,198⟩,253028435796269049,none,none⟩]
private theorem rows10_5_v : rows10_5.all validRow = true := by decide +kernel
def rows10 : List TerminalRow := rows10_0 ++ rows10_1 ++ rows10_2 ++ rows10_3 ++ rows10_4 ++ rows10_5
private theorem rows10_v : rows10.all validRow = true := by simp only [rows10,List.all_append,rows10_0_v,rows10_1_v,rows10_2_v,rows10_3_v,rows10_4_v,rows10_5_v,Bool.and_self]
private def rows11_0 : List TerminalRow := [
  ⟨⟨11,11,5733⟩,248725794431379061,none,none⟩,
  ⟨⟨11,12,5701⟩,248844511351301983,none,none⟩,
  ⟨⟨11,13,5665⟩,248963242706652893,none,none⟩,
  ⟨⟨11,14,5629⟩,249081988497431794,none,none⟩,
  ⟨⟨11,15,5593⟩,249200748723638684,none,none⟩,
  ⟨⟨11,16,5556⟩,249319523385273565,none,none⟩,
  ⟨⟨11,17,5518⟩,249438312482336436,none,none⟩,
  ⟨⟨11,18,5480⟩,249557116014827299,none,none⟩]
private theorem rows11_0_v : rows11_0.all validRow = true := by decide +kernel
private def rows11_1 : List TerminalRow := [
  ⟨⟨11,19,5442⟩,249675933982746149,none,none⟩,
  ⟨⟨11,20,5403⟩,249794766386092992,none,none⟩,
  ⟨⟨11,21,5364⟩,249913613224867822,none,none⟩,
  ⟨⟨11,22,5324⟩,250032474499070646,none,none⟩,
  ⟨⟨11,23,5283⟩,250151350208701456,none,none⟩,
  ⟨⟨11,24,5242⟩,250270240353760258,(some (2,2,2)),none⟩,
  ⟨⟨11,25,5200⟩,250389144934247050,(some (2,2,2)),none⟩,
  ⟨⟨11,26,5157⟩,250508063950161832,(some (2,2,2)),(some (2,2,2))⟩]
private theorem rows11_1_v : rows11_1.all validRow = true := by decide +kernel
private def rows11_2 : List TerminalRow := [
  ⟨⟨11,27,5113⟩,250626997401504605,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨11,28,5066⟩,250745945288275367,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨11,29,5014⟩,250864907610474120,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨11,30,4960⟩,250983884368100863,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨11,31,4904⟩,251102875561155595,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨11,32,4803⟩,251221881189638317,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨11,33,4587⟩,251340901253549031,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨11,34,4364⟩,251459935752887732,(some (2,2,2)),(some (2,2,2))⟩]
private theorem rows11_2_v : rows11_2.all validRow = true := by decide +kernel
private def rows11_3 : List TerminalRow := [
  ⟨⟨11,35,4132⟩,251578984687654427,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨11,36,3893⟩,251698048057849109,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨11,37,3644⟩,251817125863471782,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨11,38,3387⟩,251936218104522446,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨11,39,3120⟩,252055324781001099,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨11,40,2843⟩,252174445892907743,(some (2,2,2)),none⟩,
  ⟨⟨11,41,2555⟩,252293581440242376,none,none⟩,
  ⟨⟨11,42,2255⟩,252412731423005000,none,none⟩]
private theorem rows11_3_v : rows11_3.all validRow = true := by decide +kernel
private def rows11_4 : List TerminalRow := [
  ⟨⟨11,43,1944⟩,252531895841195614,none,none⟩,
  ⟨⟨11,44,1620⟩,252651074694814218,none,none⟩,
  ⟨⟨11,45,1282⟩,252770267983860812,none,none⟩,
  ⟨⟨11,46,929⟩,252889475708335396,none,none⟩,
  ⟨⟨11,47,561⟩,253008697868237970,none,none⟩,
  ⟨⟨11,48,176⟩,253127934463568536,none,none⟩]
private theorem rows11_4_v : rows11_4.all validRow = true := by decide +kernel
def rows11 : List TerminalRow := rows11_0 ++ rows11_1 ++ rows11_2 ++ rows11_3 ++ rows11_4
private theorem rows11_v : rows11.all validRow = true := by simp only [rows11,List.all_append,rows11_0_v,rows11_1_v,rows11_2_v,rows11_3_v,rows11_4_v,Bool.and_self]
private def rows12_0 : List TerminalRow := [
  ⟨⟨12,12,5509⟩,248850162271474300,none,none⟩,
  ⟨⟨12,13,5472⟩,248980184730467381,none,none⟩,
  ⟨⟨12,14,5435⟩,249110221624888450,none,none⟩,
  ⟨⟨12,15,5397⟩,249240272954737512,none,none⟩,
  ⟨⟨12,16,5359⟩,249370338720014563,none,none⟩,
  ⟨⟨12,17,5320⟩,249500418920719604,none,none⟩,
  ⟨⟨12,18,5280⟩,249630513556852635,none,none⟩,
  ⟨⟨12,19,5240⟩,249760622628413658,none,none⟩]
private theorem rows12_0_v : rows12_0.all validRow = true := by decide +kernel
private def rows12_1 : List TerminalRow := [
  ⟨⟨12,20,5200⟩,249890746135402668,none,none⟩,
  ⟨⟨12,21,5158⟩,250020884077819670,none,none⟩,
  ⟨⟨12,22,5110⟩,250151036455664662,none,none⟩,
  ⟨⟨12,23,5060⟩,250281203268937644,none,none⟩,
  ⟨⟨12,24,5009⟩,250411384517638616,(some (2,2,2)),none⟩,
  ⟨⟨12,25,4863⟩,250541580201767578,(some (2,2,2)),none⟩,
  ⟨⟨12,26,4670⟩,250671790321324531,(some (2,2,2)),none⟩,
  ⟨⟨12,27,4473⟩,250802014876309473,(some (2,2,2)),(some (2,2,2))⟩]
private theorem rows12_1_v : rows12_1.all validRow = true := by decide +kernel
private def rows12_2 : List TerminalRow := [
  ⟨⟨12,28,4270⟩,250932253866722405,(some (2,2,2)),(some (2,2,2))⟩,
  ⟨⟨12,29,4061⟩,251062507292563328,(some (2,2,2)),none⟩,
  ⟨⟨12,30,3847⟩,251192775153832239,(some (2,2,2)),none⟩,
  ⟨⟨12,31,3626⟩,251323057450529144,(some (2,2,2)),none⟩,
  ⟨⟨12,32,3399⟩,251453354182654036,(some (2,2,2)),none⟩,
  ⟨⟨12,33,3166⟩,251583665350206918,none,none⟩,
  ⟨⟨12,34,2925⟩,251713990953187792,none,none⟩,
  ⟨⟨12,35,2677⟩,251844330991596655,none,none⟩]
private theorem rows12_2_v : rows12_2.all validRow = true := by decide +kernel
private def rows12_3 : List TerminalRow := [
  ⟨⟨12,36,2421⟩,251974685465433507,none,none⟩,
  ⟨⟨12,37,2157⟩,252105054374698351,none,none⟩,
  ⟨⟨12,38,1885⟩,252235437719391184,none,none⟩,
  ⟨⟨12,39,1605⟩,252365835499512008,none,none⟩,
  ⟨⟨12,40,1314⟩,252496247715060822,none,none⟩,
  ⟨⟨12,41,1015⟩,252626674366037627,none,none⟩,
  ⟨⟨12,42,705⟩,252757115452442419,none,none⟩,
  ⟨⟨12,43,384⟩,252887570974275204,none,none⟩]
private theorem rows12_3_v : rows12_3.all validRow = true := by decide +kernel
private def rows12_4 : List TerminalRow := [
  ⟨⟨12,44,52⟩,253018040931535977,none,none⟩]
private theorem rows12_4_v : rows12_4.all validRow = true := by decide +kernel
def rows12 : List TerminalRow := rows12_0 ++ rows12_1 ++ rows12_2 ++ rows12_3 ++ rows12_4
private theorem rows12_v : rows12.all validRow = true := by simp only [rows12,List.all_append,rows12_0_v,rows12_1_v,rows12_2_v,rows12_3_v,rows12_4_v,Bool.and_self]
private def rows13_0 : List TerminalRow := [
  ⟨⟨13,13,5253⟩,248985835650639697,none,none⟩,
  ⟨⟨13,14,5208⟩,249127163648702938,none,none⟩,
  ⟨⟨13,15,5161⟩,249268506082194169,none,none⟩,
  ⟨⟨13,16,5011⟩,249409862951113391,none,none⟩,
  ⟨⟨13,17,4840⟩,249551234255460603,none,none⟩,
  ⟨⟨13,18,4664⟩,249692619995235803,none,none⟩,
  ⟨⟨13,19,4485⟩,249834020170438995,none,none⟩,
  ⟨⟨13,20,4301⟩,249975434781070176,none,none⟩]
private theorem rows13_0_v : rows13_0.all validRow = true := by decide +kernel
private def rows13_1 : List TerminalRow := [
  ⟨⟨13,21,4114⟩,250116863827129348,none,none⟩,
  ⟨⟨13,22,3922⟩,250258307308616510,none,none⟩,
  ⟨⟨13,23,3726⟩,250399765225531662,none,none⟩,
  ⟨⟨13,24,3525⟩,250541237577874804,none,none⟩,
  ⟨⟨13,25,3319⟩,250682724365645935,none,none⟩,
  ⟨⟨13,26,3109⟩,250824225588845059,none,none⟩,
  ⟨⟨13,27,2893⟩,250965741247472170,none,none⟩,
  ⟨⟨13,28,2672⟩,251107271341527274,none,none⟩]
private theorem rows13_1_v : rows13_1.all validRow = true := by decide +kernel
private def rows13_2 : List TerminalRow := [
  ⟨⟨13,29,2445⟩,251248815871010364,none,none⟩,
  ⟨⟨13,30,2213⟩,251390374835921449,none,none⟩,
  ⟨⟨13,31,1975⟩,251531948236260521,none,none⟩,
  ⟨⟨13,32,1730⟩,251673536072027583,none,none⟩,
  ⟨⟨13,33,1480⟩,251815138343222638,none,none⟩,
  ⟨⟨13,34,1222⟩,251956755049845681,none,none⟩,
  ⟨⟨13,35,958⟩,252098386191896714,none,none⟩,
  ⟨⟨13,36,686⟩,252240031769375737,none,none⟩]
private theorem rows13_2_v : rows13_2.all validRow = true := by decide +kernel
private def rows13_3 : List TerminalRow := [
  ⟨⟨13,37,407⟩,252381691782282749,none,none⟩,
  ⟨⟨13,38,120⟩,252523366230617752,none,none⟩]
private theorem rows13_3_v : rows13_3.all validRow = true := by decide +kernel
def rows13 : List TerminalRow := rows13_0 ++ rows13_1 ++ rows13_2 ++ rows13_3
private theorem rows13_v : rows13.all validRow = true := by simp only [rows13,List.all_append,rows13_0_v,rows13_1_v,rows13_2_v,rows13_3_v,Bool.and_self]
private def rows14_0 : List TerminalRow := [
  ⟨⟨14,14,3728⟩,249132814568875257,none,none⟩,
  ⟨⟨14,15,3546⟩,249285448106008656,none,none⟩,
  ⟨⟨14,16,3360⟩,249438096078570048,none,none⟩,
  ⟨⟨14,17,3170⟩,249590758486559430,none,none⟩,
  ⟨⟨14,18,2977⟩,249743435329976800,none,none⟩,
  ⟨⟨14,19,2779⟩,249896126608822162,none,none⟩,
  ⟨⟨14,20,2578⟩,250048832323095513,none,none⟩,
  ⟨⟨14,21,2372⟩,250201552472796856,none,none⟩]
private theorem rows14_0_v : rows14_0.all validRow = true := by decide +kernel
private def rows14_1 : List TerminalRow := [
  ⟨⟨14,22,2162⟩,250354287057926188,none,none⟩,
  ⟨⟨14,23,1948⟩,250507036078483509,none,none⟩,
  ⟨⟨14,24,1729⟩,250659799534468822,none,none⟩,
  ⟨⟨14,25,1505⟩,250812577425882123,none,none⟩,
  ⟨⟨14,26,1277⟩,250965369752723416,none,none⟩,
  ⟨⟨14,27,1043⟩,251118176514992698,none,none⟩,
  ⟨⟨14,28,804⟩,251270997712689971,none,none⟩,
  ⟨⟨14,29,560⟩,251423833345815234,none,none⟩]
private theorem rows14_1_v : rows14_1.all validRow = true := by decide +kernel
private def rows14_2 : List TerminalRow := [
  ⟨⟨14,30,310⟩,251576683414368487,none,none⟩,
  ⟨⟨14,31,55⟩,251729547918349730,none,none⟩]
private theorem rows14_2_v : rows14_2.all validRow = true := by decide +kernel
def rows14 : List TerminalRow := rows14_0 ++ rows14_1 ++ rows14_2
private theorem rows14_v : rows14.all validRow = true := by simp only [rows14,List.all_append,rows14_0_v,rows14_1_v,rows14_2_v,Bool.and_self]
private def rows15_0 : List TerminalRow := [
  ⟨⟨15,15,1637⟩,249291099026180974,none,none⟩,
  ⟨⟨15,16,1433⟩,249455038102384535,none,none⟩,
  ⟨⟨15,17,1226⟩,249618991614016086,none,none⟩,
  ⟨⟨15,18,1014⟩,249782959561075628,none,none⟩,
  ⟨⟨15,19,799⟩,249946941943563160,none,none⟩,
  ⟨⟨15,20,580⟩,250110938761478681,none,none⟩,
  ⟨⟨15,21,357⟩,250274950014822194,none,none⟩,
  ⟨⟨15,22,129⟩,250438975703593695,none,none⟩]
private theorem rows15_0_v : rows15_0.all validRow = true := by decide +kernel
def rows15 : List TerminalRow := rows15_0
private theorem rows15_v : rows15.all validRow = true := by simp only [rows15,List.all_append,rows15_0_v,Bool.and_self]
def rowsBySlope : ℕ → List TerminalRow
  | 1 => rows1
  | 2 => rows2
  | 3 => rows3
  | 4 => rows4
  | 5 => rows5
  | 6 => rows6
  | 7 => rows7
  | 8 => rows8
  | 9 => rows9
  | 10 => rows10
  | 11 => rows11
  | 12 => rows12
  | 13 => rows13
  | 14 => rows14
  | 15 => rows15
  | _ => []
def rowAt (r y : ℕ) : Option TerminalRow := (rowsBySlope r)[y-r]?
theorem all_rows_valid (r : ℕ) : (rowsBySlope r).all validRow = true := by
  rcases r with _|r
  · rfl
  rcases r with _|r
  · exact rows1_v
  rcases r with _|r
  · exact rows2_v
  rcases r with _|r
  · exact rows3_v
  rcases r with _|r
  · exact rows4_v
  rcases r with _|r
  · exact rows5_v
  rcases r with _|r
  · exact rows6_v
  rcases r with _|r
  · exact rows7_v
  rcases r with _|r
  · exact rows8_v
  rcases r with _|r
  · exact rows9_v
  rcases r with _|r
  · exact rows10_v
  rcases r with _|r
  · exact rows11_v
  rcases r with _|r
  · exact rows12_v
  rcases r with _|r
  · exact rows13_v
  rcases r with _|r
  · exact rows14_v
  rcases r with _|r
  · exact rows15_v
  rfl
theorem rowAt_valid {r y : ℕ} {row : TerminalRow} (h : rowAt r y = some row) :
    validRow row = true := List.all_eq_true.mp (all_rows_valid r) _ (List.mem_of_getElem? h)
end ProximityPrize.SubmissionLower.K6833Residual
