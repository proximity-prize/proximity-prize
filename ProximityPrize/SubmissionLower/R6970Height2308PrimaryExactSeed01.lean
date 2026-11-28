import ProximityPrize.SubmissionLower.R6970ExactPrimaryBill
import ProximityPrize.SubmissionLower.R6970Height2308SeedOnePrimary

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed01

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2308.SeedOnePrimary (plan price)

private def prepared : Frame :=
  ⟨17482907648/89865,64380/23173,177506,825552,
    [(177506,241826295704),
    (158035,0),
    (228428/3,0),
    (369469/8,0),
    (795822/25,0),
    (211264/9,0),
    (238165/16,0),
    (1119062/121,0),
    (1119062/121,0),
    (3915559/484,0),
    (1828895/242,57650266780),
    (3654081/512,90647560558),
    (3654081/512,811000630),
    (13038752/2401,304536022950),
    (188840888/37845,190802314782),
    (188840888/37845,297378598168),
    (188840888/37845,0),
    (188840888/37845,450866370404)],
    [(825552,65831884940),
    (715350,0),
    (630208,0),
    (372644,0),
    (224759,0),
    (224759,0),
    (132886,0),
    (820515/8,0),
    (3229019/36,0),
    (5447588/75,0),
    (15876028/225,0),
    (7906054/121,0),
    (7906054/121,0),
    (58618216/1225,54868159770),
    (42576912/961,35615550970),
    (42576912/961,31221930720),
    (42576912/961,0),
    (42576912/961,0)]⟩

private def first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def rest : List Vertex :=
  [⟨952682984/1225,413153154/2401,6545608833746791284406684/13888728860125⟩,
   ⟨750778560/961,413153154/2401,2277780827298990345587610332/4804944636448845⟩,
   ⟨825552,413153154/2401,2542604135369599751313884/4999942389645⟩]

private def limit : ℚ := 460168049346518697859744803635190224027/4172424287143858483584

def lossCap : ℕ := 199117980417499133

private theorem checked' : ExactRank.checked prepared limit first rest := by decide +kernel
private theorem fit : RankBill.frame plan price .near = prepared := by decide +kernel
private theorem payLimit : limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near prepared first rest limit lossCap fit checked' payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 200903583451401575 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed01
