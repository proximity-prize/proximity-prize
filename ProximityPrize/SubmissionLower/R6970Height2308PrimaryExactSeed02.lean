import ProximityPrize.SubmissionLower.R6970ExactPrimaryBill
import ProximityPrize.SubmissionLower.R6970Height2308SeedTwoPrimary

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed02

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2308.SeedTwoPrimary (plan price)

private def prepared : Frame :=
  ⟨17482907648/89865,64380/23173,177162,826288,
    [(177162,239458803920),
    (313935/2,0),
    (680648/9,0),
    (365621/8,0),
    (46629/2,0),
    (264266/25,0),
    (1273094/169,0),
    (1273094/169,0),
    (1228408/169,0),
    (1228408/169,0),
    (1228408/169,0),
    (1228408/169,0),
    (1228408/169,61165274632),
    (15556157/2738,27902009226),
    (15556157/2738,159232171470),
    (15556157/2738,95020339980),
    (7007394/1369,550410298130),
    (7007394/1369,0),
    (7007394/1369,0),
    (7007394/1369,0),
    (7007394/1369,0),
    (6726800/1369,502700507490)],
    [(826288,65164293240),
    (710531,0),
    (630208,0),
    (3313612/9,0),
    (478339/2,0),
    (4781568/49,0),
    (436734/5,0),
    (436734/5,0),
    (1943136/25,0),
    (1943136/25,0),
    (1943136/25,0),
    (1943136/25,0),
    (5352016/75,0),
    (8662359/169,0),
    (8662359/169,3052651410),
    (8662359/169,24241209330),
    (125825736/2809,93486922580),
    (125825736/2809,0),
    (125825736/2809,0),
    (125825736/2809,0),
    (125825736/2809,0),
    (68453019/1600,191728240)]⟩

private def first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def rest : List Vertex :=
  [⟨130980313/169,469513399/2738,15085840579719422491343332/32119718761923⟩,
   ⟨2195217256/2809,469513399/2738,1267156385742759197950878644/2669357692374015⟩,
   ⟨1253607781/1600,469513399/2738,11314818533954030119211572/23757188433375⟩,
   ⟨826288,469513399/2738,484230866086496937531988/950287537335⟩]

private def limit : ℚ := 1502548729932297069204872676408540298813/13686761416714419382420

def lossCap : ℕ := 196564546610870501

private theorem checked' : ExactRank.checked prepared limit first rest := by decide +kernel
private theorem fit : RankBill.frame plan price .near = prepared := by decide +kernel
private theorem payLimit : limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near prepared first rest limit lossCap fit checked' payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 198354486275453699 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed02
