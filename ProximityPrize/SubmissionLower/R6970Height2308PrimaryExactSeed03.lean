import ProximityPrize.SubmissionLower.R6970ExactPrimaryBill
import ProximityPrize.SubmissionLower.R6970Height2308SeedThreePrimary

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.ExactPrimary.Seed03

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2308.SeedThreePrimary (plan price)

private def prepared : Frame :=
  ⟨17482907648/89865,64380/23173,176796,824580,
    [(176796,238070949948),
    (155900,0),
    (676012/9,0),
    (363059/8,0),
    (208397/9,0),
    (524933/50,0),
    (1265286/169,0),
    (1265286/169,0),
    (1218892/169,0),
    (1218892/169,0),
    (1218892/169,0),
    (1218892/169,0),
    (1218892/169,60834378144),
    (15437573/2738,28005857604),
    (15437573/2738,161038172856),
    (15437573/2738,91068133236),
    (6955971/1369,553451435746),
    (6955971/1369,0),
    (6955971/1369,0),
    (6955971/1369,0),
    (6955971/1369,0),
    (6678610/1369,503841158146)],
    [(824580,64786742280),
    (705712,0),
    (630208,0),
    (3290432/9,0),
    (1900241/8,0),
    (4749116/49,0),
    (436734/5,0),
    (436734/5,0),
    (1943136/25,0),
    (1943136/25,0),
    (1943136/25,0),
    (1943136/25,0),
    (15924776/225,0),
    (8596113/169,0),
    (8596113/169,3036181470),
    (8596113/169,23839328310),
    (124910004/2809,93433832260),
    (124910004/2809,0),
    (124910004/2809,0),
    (124910004/2809,0),
    (124910004/2809,0),
    (135928269/3200,689183180)]⟩

private def first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def rest : List Vertex :=
  [⟨130757907/169,468629875/2738,225915185908763807713191004/481795781428845⟩,
   ⟨2191335216/2809,468629875/2738,758973555696947201849169260/1601614615424409⟩,
   ⟨2502727731/3200,468629875/2738,33884569553584020535178908/71271565300125⟩,
   ⟨824580,468629875/2738,1449619287520766558736124/2850862612005⟩]

private def limit : ℚ := 7180804939334223525717814422883758935885/65696454800229213035616

def lossCap : ℕ := 195095318864241249

private theorem checked' : ExactRank.checked prepared limit first rest := by decide +kernel
private theorem fit : RankBill.frame plan price .near = prepared := by decide +kernel
private theorem payLimit : limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near prepared first rest limit lossCap fit checked' payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 196881618245884581 := by decide +kernel

end Research6970.Height2308.ExactPrimary.Seed03
