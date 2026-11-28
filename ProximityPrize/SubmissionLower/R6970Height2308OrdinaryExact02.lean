import ProximityPrize.SubmissionLower.R6970ExactPrimaryBill
import ProximityPrize.SubmissionLower.Bundle6970_6787940e8645d48e

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Research6970.Height2308.OrdinaryExact.Seed02

open Research6970.ExactRank
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons1 (plan price)

private def prepared : Frame :=
  ⟨17482907648/89865,64380/23173,166047,771431,
    [(166047,208093713575),
    (130589,0),
    (566339/9,0),
    (607303/16,0),
    (654557/25,0),
    (741163/49,0),
    (884209/100,0),
    (915430/121,5670318935),
    (915430/121,0),
    (3090254/441,235625902),
    (3090254/441,0),
    (755020/121,111738463368),
    (755020/121,0),
    (9140020/1681,180496190782),
    (2221984/441,113403368450),
    (2221984/441,251439400652),
    (2221984/441,622825143570),
    (2221984/441,111864473034)],
    [(771431,56772859830),
    (1180985/2,0),
    (1180985/2,0),
    (2749178/9,0),
    (409431/2,0),
    (3340561/25,0),
    (760463/8,0),
    (4123729/49,0),
    (673387/9,0),
    (549021/8,0),
    (549021/8,0),
    (505197/8,0),
    (505197/8,0),
    (4946427/98,35037585990),
    (29962856/675,32024199310),
    (29962856/675,12069038310),
    (29962856/675,93553962250),
    (29962856/675,0)]⟩

private def first : Vertex := ⟨0,0,1620531461217116/2082441645⟩

private def rest : List Vertex :=
  [⟨70653811/98,269984987/1681,74795923510191922027871324/171528635857005⟩,
   ⟨490753069/675,269984987/1681,1041539688265306050381799124/2362894473540375⟩,
   ⟨771431,269984987/1681,332788626365896968364396/700116881049⟩]

private def limit : ℚ := 289932640227410862534703256187250899194/2919438823365707225625

def lossCap : ℕ := 177028765720763168

private theorem checked' : ExactRank.checked prepared limit first rest := by decide +kernel
private theorem fit : RankBill.frame plan price .near = prepared := by decide +kernel
private theorem payLimit : limit + RankBill.commonLoss plan price + plan.seedLimit ≤ lossCap := by decide +kernel

theorem pointwise : RankBill.Pointwise plan price .near lossCap :=
  RankBill.exact_of_checked plan price .near prepared first rest limit lossCap fit checked' payLimit

theorem fee_eq : RankBill.fee plan .near lossCap = 178698617729957900 := by decide +kernel

end Research6970.Height2308.OrdinaryExact.Seed02
