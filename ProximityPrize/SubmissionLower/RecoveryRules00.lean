import ProximityPrize.SubmissionLower.CoreA
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.all false
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
section
namespace ProximityPrize.SubmissionLower
section MergedPart3
namespace CRB
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
open MvPolynomial RCN156 RCN234 RCN238
open AP CVL
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

structure Input (nodes:I ↪ K) (u0 u1:I→K)
    (selected:K→Polynomial K) (Gamma:Finset K):Prop where
  degree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071
  agreement: ∀gamma∈Gamma,181235≤
    ((Finset.univ:Finset I).filter (fun i=>
      (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card
  noPencil:BL selected Gamma 131071 80909

variable (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144)
  (selected:K→Polynomial K) (Gamma:Finset K)
  (inp:Input nodes u0 u1 selected Gamma)
include inp hI

theorem GLE (i:Fin 417) {D L s:ℕ} {H:MvPolynomial (Fin 4) K}
    (F:RCN266.RegularIndex H)
    (hbox:F.val∈RCN174.BA K D 131071 L s)
    (hR:wt BE F.val=(PM.offer i).R)
    (hB:wt BC F.val=(PM.offer i).B)
    (hlo:(PM.offer i).T0≤wt AT F.val)
    (hhi:wt AT F.val≤(PM.offer i).T1):
    (RCN140.regularSeeds H selected Gamma F).card≤(PM.offer i).count:=by
  apply PM.AS K I i F
    (CKU F.val D L s _ _ hbox le_rfl hR.le)
    rfl le_rfl hR.ge hB.le hlo hhi
    (EUN F.val (RCN167.KR H F.val F.property).1.ne_zero
      _ _ hB hR.le)
    nodes u0 u1 hI selected Gamma inp.degree inp.agreement inp.noPencil

theorem greedy_count (i:Fin 361) {D L s:ℕ} {H:MvPolynomial (Fin 4) K}
    (F:RCN266.RegularIndex H)
    (hbox:F.val∈RCN174.BA K D 131071 L s)
    (hR:wt BE F.val=(AAK.offer i).R)
    (hB:wt BC F.val=(AAK.offer i).B)
    (hlo:(AAK.offer i).T0≤wt AT F.val)
    (hhi:wt AT F.val≤(AAK.offer i).T1):
    (RCN140.regularSeeds H selected Gamma F).card≤(AAK.offer i).count:=by
  apply AAK.AS K I i F
    (CKU F.val D L s _ _ hbox le_rfl hR.le)
    rfl le_rfl hR.ge hB.le hlo hhi
    (EUN F.val (RCN167.KR H F.val F.property).1.ne_zero
      _ _ hB hR.le)
    nodes u0 u1 hI selected Gamma inp.degree inp.agreement inp.noPencil

def packetOffer:Fin 52→Band:= ![⟨11,58,3599,3724,240017000000000000⟩,⟨12,58,3347,3774,257168000000000000⟩,⟨12,59,3294,3774,261564000000000000⟩,⟨13,55,3322,3699,254556000000000000⟩,⟨13,56,3266,3699,258792000000000000⟩,⟨13,57,3213,3456,248401000000000000⟩,⟨13,57,3457,3699,261937000000000000⟩,⟨13,58,3161,3378,247611000000000000⟩,⟨13,58,3379,3543,256650000000000000⟩,⟨13,58,3544,3560,257410000000000000⟩,⟨13,58,3561,3618,260938000000000000⟩,⟨13,58,3619,3680,264315000000000000⟩,⟨13,58,3681,3684,264601000000000000⟩,⟨13,59,3106,3146,237075000000000000⟩,⟨13,59,3147,3378,251514000000000000⟩,⟨13,59,3379,3543,260704000000000000⟩,⟨13,59,3544,3560,261492000000000000⟩,⟨13,59,3561,3599,263904000000000000⟩,⟨12,55,3394,3571,232614000000000000⟩,⟨12,55,3572,3749,242370000000000000⟩,⟨12,56,3338,3543,235936000000000000⟩,⟨12,56,3544,3749,246740000000000000⟩,⟨12,57,3283,3399,231627000000000000⟩,⟨12,57,3400,3516,237209000000000000⟩,⟨12,57,3517,3749,251109000000000000⟩,⟨13,53,3318,3533,236771000000000000⟩,⟨13,53,3534,3749,248527000000000000⟩,⟨13,54,3261,3383,232273000000000000⟩,⟨13,54,3384,3505,238262000000000000⟩,⟨13,54,3506,3627,244870000000000000⟩,⟨13,54,3628,3749,252250000000000000⟩,⟨12,51,3347,4000,240784000000000000⟩,⟨13,53,3681,4000,264947000000000000⟩,⟨13,60,3055,3120,246333000000000000⟩,⟨12,58,3681,3899,265620000000000000⟩,⟨12,59,3681,3850,266791000000000000⟩,⟨13,58,3681,4000,271000000000000000⟩,⟨12,59,3561,3680,255098000000000000⟩,⟨12,60,3055,3274,242771000000000000⟩,⟨13,60,3681,3910,274000000000000000⟩,⟨13,60,3895,3924,274040000000000000⟩,⟨13,60,3103,3378,255414000000000000⟩,⟨13,60,3379,3543,264756000000000000⟩,⟨13,60,3544,3560,265572000000000000⟩,⟨13,60,3561,3618,269219000000000000⟩,⟨13,60,3619,3680,273287000000000000⟩,⟨11,58,3599,3724,240017000000000000⟩,⟨13,57,3681,4000,267000000000000000⟩,⟨13,59,3681,3924,271000000000000000⟩,⟨11,70,2307,3276,261994000000000000⟩,⟨12,68,2307,3217,266635000000000000⟩,⟨13,66,2307,3102,265894000000000000⟩]
theorem packet_count (i:Fin 52) {D L s:ℕ} {H:MvPolynomial (Fin 4) K}
    (F:RCN266.RegularIndex H) (hDlow:131072≤D) (hDchar:D<2130706433)
    (hbox:F.val∈RCN174.BA K D 131071 L s)
    (hR:wt BE F.val≤(packetOffer i).R)
    (hB:wt BC F.val≤(packetOffer i).B)
    (hlo:(packetOffer i).T0≤wt AT F.val)
    (hhi:wt AT F.val≤(packetOffer i).T1):
    (RCN140.regularSeeds H selected Gamma F).card≤(packetOffer i).count:=by
  have gates:4≤(packetOffer i).R∧(packetOffer i).R≤13∧
      (packetOffer i).R+2≤(packetOffer i).B∧(packetOffer i).B≤117∧
      (packetOffer i).B≤(packetOffer i).T1∧(packetOffer i).T1≤4100:=by
    fin_cases i<;>decide
  let P:=factorPacket F D L s (packetOffer i).T1 (packetOffer i).B (packetOffer i).R
    hDlow hDchar hbox gates.1 gates.2.1 gates.2.2.1 gates.2.2.2.1
    gates.2.2.2.2.1 gates.2.2.2.2.2 hR hB hhi
    nodes u0 u1 hI selected Gamma inp.degree inp.agreement inp.noPencil
  change P.seeds.card≤(packetOffer i).count
  have hlow:(packetOffer i).T0≤wt AT P.F:=hlo
  fin_cases i
  · exact GI.Concrete.packet_count ⟨0,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨1,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨2,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨3,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨4,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨5,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨6,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨7,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨8,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨9,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨10,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨11,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨12,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨13,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨14,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨15,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨16,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨17,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨18,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨19,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨20,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨21,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨22,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨23,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨24,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨25,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨26,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨27,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨28,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨29,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨30,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨31,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨32,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨33,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨34,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨35,by decide⟩ nodes hI P hlow
  · exact AXH.packet_count nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨37,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨38,by decide⟩ nodes hI P hlow
  · exact BQD.packet_count nodes hI P hlow
  · exact BIL.packet_count nodes hI P hlow
  · exact AJK.packet_count ⟨0,by decide⟩ nodes hI P hlow
  · exact AJK.packet_count ⟨1,by decide⟩ nodes hI P hlow
  · exact AJK.packet_count ⟨2,by decide⟩ nodes hI P hlow
  · exact AJK.packet_count ⟨3,by decide⟩ nodes hI P hlow
  · exact AJK.packet_count ⟨4,by decide⟩ nodes hI P hlow
  · exact GI.Concrete.packet_count ⟨0,by decide⟩ nodes hI P hlow
  · exact BAG.packet_count nodes hI P hlow
  · exact AZW.packet_count nodes hI P hlow
  · exact AWK.packet_count ⟨0,by decide⟩ nodes hI P hlow
  · exact AWK.packet_count ⟨1,by decide⟩ nodes hI P hlow
  · exact AWK.packet_count ⟨2,by decide⟩ nodes hI P hlow

end
end CRB
end MergedPart3
section MergedPart4
namespace UR
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open RCN156 RCN234 RCN095 RCN266 FV
open CRB

inductive Choice where
  | relative (i:Fin 417)
  | packet (i:Fin 52)
  | greedy (i:Fin 361)
  deriving DecidableEq

def price:Choice→ℕ
  | .relative i=>(PM.offer i).count
  | .packet i=>(packetOffer i).count
  | .greedy i=>(AAK.offer i).count

def Active:Choice→ℕ→ℕ→ℕ→Prop
  | .relative i,r,v,z=>
      r=(PM.offer i).R∧
      r+v=(PM.offer i).B∧
      (PM.offer i).T0≤r+v+z∧
      r+v+z≤(PM.offer i).T1
  | .greedy i,r,v,z=>
      r=(AAK.offer i).R∧
      r+v=(AAK.offer i).B∧
      (AAK.offer i).T0≤r+v+z∧
      r+v+z≤(AAK.offer i).T1
  | .packet i,r,v,z=>
      r≤(packetOffer i).R∧r+v≤(packetOffer i).B∧
      (packetOffer i).T0≤r+v+z∧r+v+z≤(packetOffer i).T1

instance (c:Choice) (r v z:ℕ):Decidable (Active c r v z):=by
  cases c<;>unfold Active<;>infer_instance

theorem GLZ (c:Choice) (r v lo hi z:ℕ)
    (ha:Active c r v lo) (hb:Active c r v hi) (hl:lo≤z) (hh:z≤hi):
    Active c r v z:=by
  cases c<;>simp only [Active] at ha hb ⊢ <;>omega

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

theorem count (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (inp:Input nodes u0 u1 selected Gamma)
    {D L s:ℕ} {H:MvPolynomial (Fin 4) K} (F:RegularIndex H)
    (hDlow:131072≤D) (hDchar:D<2130706433)
    (hbox:F.val∈RCN174.BA K D 131071 L s)
    (c:Choice)
    (ha:Active c (RCN130.BG H F).all
      (RCN130.BG H F).yz (RCN130.BG H F).zOnly):
    (RCN140.regularSeeds H selected Gamma F).card≤price c:=by
  have hc:=RCN130.GX F.val
  have hr:(RCN130.BG H F).all=wt BE F.val:=hc.1
  have hy:(RCN130.BG H F).all+(RCN130.BG H F).yz=
      wt BC F.val:=by
    simpa only [RCN130.BG,Nat.add_comm] using hc.2.1
  have ht:(RCN130.BG H F).all+(RCN130.BG H F).yz+
      (RCN130.BG H F).zOnly=wt AT F.val:=by
    simpa only [RCN130.BG,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hc.2.2
  cases c with
  | relative i=>
    simp only [Active] at ha
    rw [ht,hy,hr] at ha
    exact GLE nodes u0 u1 hI selected Gamma inp i F hbox ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
  | greedy i=>
    simp only [Active] at ha
    rw [ht,hy,hr] at ha
    exact greedy_count nodes u0 u1 hI selected Gamma inp i F hbox ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
  | packet i=>
    simp only [Active] at ha
    rw [ht,hy,hr] at ha
    exact packet_count nodes u0 u1 hI selected Gamma inp i F hDlow hDchar hbox ha.1 ha.2.1 ha.2.2.1 ha.2.2.2

end
end UR
end MergedPart4
section MergedPart5
namespace EK
open RCN095 DY FV
open AMT Lower80899.TenPhase
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def cap (slope intercept z:ℕ):ℕ:=slope*z+intercept
def rootIndex (w:ℕ):Fin 21:=⟨(w-1)%21,Nat.mod_lt _ (by decide)⟩
def phaseIndex (j:ℕ):=if j<7 then j else 5
def BSY (j:ℕ):Potential:=
  if j<7 then (Lower80899.TenPhase.sound j).potential else Lower80899.SourceSound.PhaseFinal.potential
def thresholdAt (q:Array ℕ) (j:ℕ):ℕ:=(q[j]?).getD 11193

def Carrier.Correct (c:Carrier) (r v:ℕ):Prop:=
  c.c0=cost r v 0∧c.c1=cost r v 1∧c.c2=cost r v 2∧
  c.c3=cost r v 3∧c.c4=cost r v 4
instance (c:Carrier) (r v:ℕ):Decidable (c.Correct r v):=by
  unfold Carrier.Correct;infer_instance

def Carrier.eval (c:Carrier) (z:ℕ):ℕ:=
  if z=0 then c.c0 else if z=1 then c.c1 else if z=2 then c.c2
  else c.c3+(c.c4-c.c3)*(z-3)

theorem Carrier.eval_correct (c:Carrier) (r v z:ℕ)
    (hr:1≤r) (hc:c.Correct r v):c.eval z=cost r v z:=by
  rcases hc with ⟨h0,h1,h2,h3,h4⟩
  unfold Carrier.eval
  split_ifs with hz0 hz1 hz2
  · simpa only [hz0] using h0
  · simpa only [hz1] using h1
  · simpa only [hz2] using h2
  · rw [h3,h4,raw_affine r v z hr (by omega)]

theorem Carrier.eval_affine (c:Carrier) (lo z:ℕ) (hl:3≤lo) (hz:lo≤z):
    c.eval z=c.eval lo+(c.c4-c.c3)*(z-lo):=by
  simp only [Carrier.eval,if_neg (show z≠0 by omega),if_neg (show z≠1 by omega),
    if_neg (show z≠2 by omega),if_neg (show lo≠0 by omega),
    if_neg (show lo≠1 by omega),if_neg (show lo≠2 by omega)]
  rw [show z-3=(lo-3)+(z-lo) by omega,Nat.mul_add]
  omega

def rootSlope (w r v:ℕ):ℕ:=
  (WI.receipt (rootIndex w)).slope (r-3) (v-2)
def FSY (w r v:ℕ):ℕ:=
  (WI.receipt (rootIndex w)).intercept (r-3) (v-2)
def rootL (w:ℕ):ℕ:=WI.sourceLimit (rootIndex w)
def rootUpper (w r v z:ℕ):ℕ:=rootSlope w r v*z+FSY w r v

def extraChoice (w:ℕ):UR.Choice:=
  if w<449 then .relative ⟨(w-32)%417,Nat.mod_lt _ (by decide)⟩
  else if w<501 then .packet ⟨(w-449)%52,Nat.mod_lt _ (by decide)⟩
  else .greedy ⟨(w-501)%361,Nat.mod_lt _ (by decide)⟩

def choice (c:Carrier) (w r v z:ℕ):ℕ:=
  if 32≤w then UR.price (extraChoice w)
  else if w=0 then c.eval z else if w≤21 then rootUpper w r v z
  else (BSY (w-22)).eval (rawFlag r v z)

def Active (thresholds:Array ℕ) (w r v lo hi:ℕ):Prop:=
  if 32≤w then w≤861∧UR.Active (extraChoice w) r v lo∧
    UR.Active (extraChoice w) r v hi
  else if w=0 then r≤32∧r+v≤149∧r+v+hi≤8121∧ABO.Safe r (r+v)
  else if w≤21 then 3≤r∧r≤31∧2≤v∧3≤lo∧
    rootL w<r+v+lo∧r+v≤142∧r+v+hi≤7501
  else w-22<8∧thresholdAt thresholds (phaseIndex (w-22))≤lo
instance (thresholds:Array ℕ) (w r v lo hi:ℕ):Decidable (Active thresholds w r v lo hi):=by
  unfold Active;infer_instance

def choiceSlope (c:Carrier) (w r v:ℕ):ℕ:=
  if 32≤w then 0
  else if w=0 then c.c4-c.c3 else if w≤21 then rootSlope w r v
  else (BSY (w-22)).totalCoeff

theorem FQA (c:Carrier) (w r v lo z:ℕ)
    (hlo:3≤lo) (hz:lo≤z):
    choice c w r v z=choice c w r v lo+choiceSlope c w r v*(z-lo):=by
  by_cases hn:32≤w
  · simp only [choice,choiceSlope,if_pos hn,Nat.zero_mul,Nat.add_zero]
  by_cases hw0:w=0
  · simpa only [choice,choiceSlope,if_neg hn,if_pos hw0] using c.eval_affine lo z hlo hz
  by_cases hw1:w≤21
  · simp only [choice,choiceSlope,if_neg hn,if_neg hw0,if_pos hw1,rootUpper]
    conv_lhs=>rw [show z=lo+(z-lo) by omega]
    ring
  · simp only [choice,choiceSlope,if_neg hn,if_neg hw0,if_neg hw1,Potential.eval,
      BTK,AVF,rawFlag_all]
    conv_lhs=>rw [show z=lo+(z-lo) by omega]
    ring

def Cover (c:Carrier) (slope intercept r v:ℕ) (thresholds:Array ℕ) (finish:ℕ):
    ℕ→List Run→Prop
  | lo,[]=>lo=finish
  | lo,x::xs=>lo<x.stop∧x.stop≤finish∧(3≤lo∨x.stop=lo+1)∧
    Active thresholds x.who r v lo (x.stop-1)∧
    choice c x.who r v lo≤cap slope intercept lo∧
    choice c x.who r v (x.stop-1)≤cap slope intercept (x.stop-1)∧
    Cover c slope intercept r v thresholds finish x.stop xs
instance (c:Carrier) (slope intercept r v:ℕ) (thresholds:Array ℕ) (finish lo:ℕ) (xs:List Run):
    Decidable (Cover c slope intercept r v thresholds finish lo xs):=by
  induction xs generalizing lo with
  | nil=>simp only [Cover];infer_instance
  | cons x xs ih=>simp only [Cover];infer_instance

theorem active_at (th:Array ℕ) (w r v lo hi z:ℕ)
    (h:Active th w r v lo hi) (hz:lo≤z) (hzi:z≤hi):Active th w r v z z:=by
  unfold Active at h ⊢
  by_cases hn:32≤w
  · simp only [if_pos hn] at h ⊢
    have ha:=UR.GLZ (extraChoice w) r v lo hi z h.2.1 h.2.2 hz hzi
    exact ⟨h.1,ha,ha⟩
  simp only [if_neg hn] at h ⊢
  by_cases h0:w=0
  · simp only [if_pos h0] at h ⊢
    exact ⟨h.1,h.2.1,by omega,h.2.2.2⟩
  · simp only [if_neg h0] at h ⊢
    split_ifs at h ⊢ <;>omega

end EK
end MergedPart5

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace PV
open scoped BigOperators
set_option autoImplicit false

def BellmanRows (Rcap Ycap:ℕ) (b B:ℕ→ℕ→ℕ):Prop:=
  ∀r v R V,1≤r→ r+R≤Rcap→ r+v+R+V≤Ycap→
    b r v+B R V≤B (r+R) (v+V)

theorem FQM {ι:Type*} [DecidableEq ι]
    (Rcap Ycap:ℕ) (b B:ℕ→ℕ→ℕ)
    (hrows:BellmanRows Rcap Ycap b B)
    (s:Finset ι) (r v:ι→ℕ)
    (hr: ∀i ∈ s,1≤r i)
    (hR:(∑ i ∈ s,r i)≤Rcap)
    (hY:(∑ i ∈ s,r i)+(∑ i ∈ s,v i)≤Ycap):
    (∑ i ∈ s,b (r i) (v i))≤B (∑ i ∈ s,r i) (∑ i ∈ s,v i):=by
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert a s ha ih=>
    have hRi:r a+(∑ i ∈ s,r i)≤Rcap:=by
      simpa only [Finset.sum_insert ha] using hR
    have hYi:(r a+ ∑ i ∈ s,r i)+(v a+ ∑ i ∈ s,v i)≤Ycap:=by
      simpa only [Finset.sum_insert ha] using hY
    have hrec:=ih (fun i hi=>hr i (Finset.mem_insert_of_mem hi))
      (by omega) (by omega)
    have hrow:=hrows (r a) (v a) (∑ i ∈ s,r i) (∑ i ∈ s,v i)
      (hr a (Finset.mem_insert_self a s)) hRi (by omega)
    rw [Finset.sum_insert ha,Finset.sum_insert ha,Finset.sum_insert ha]
    exact (Nat.add_le_add_left hrec _).trans hrow

theorem sum_count_le {ι:Type*} [DecidableEq ι]
    (Rcap Ycap slope:ℕ) (b B:ℕ→ℕ→ℕ)
    (hrows:BellmanRows Rcap Ycap b B)
    (s:Finset ι) (r v z count:ι→ℕ)
    (hr: ∀i ∈ s,1≤r i)
    (hR:(∑ i ∈ s,r i)≤Rcap)
    (hY:(∑ i ∈ s,r i)+(∑ i ∈ s,v i)≤Ycap)
    (hcost: ∀i ∈ s,count i≤slope*z i+b (r i) (v i)):
    (∑ i ∈ s,count i)≤slope*(∑ i ∈ s,z i)+
      B (∑ i ∈ s,r i) (∑ i ∈ s,v i):=by
  calc
    (∑ i ∈ s,count i)≤ ∑ i ∈ s,(slope*z i+b (r i) (v i)):=
      Finset.sum_le_sum hcost
    _=slope*(∑ i ∈ s,z i)+ ∑ i ∈ s,b (r i) (v i):=by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
    _≤_:=Nat.add_le_add_left (FQM Rcap Ycap b B hrows s r v hr hR hY) _

theorem GFA {ι:Type*} [DecidableEq ι] (a:ι)
    (count helper:ι→ℕ)
    (hsplit: ∃U:Finset ι,U ⊂ {a}∧ ∀i ∈ ({a}:Finset ι) \ U,
      count i≤helper i):count a≤helper a:=by
  obtain ⟨U,hU,hcount⟩:=hsplit
  have ha:a ∉ U:=by
    intro ha
    apply hU.2
    exact Finset.singleton_subset_iff.mpr ha
  exact hcount a (Finset.mem_sdiff.mpr ⟨Finset.mem_singleton_self a,ha⟩)

end PV
end MergedPart0
section MergedPart1
namespace NK
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1400000
variable {ι A:Type*} [DecidableEq ι]

def Bellman (Rcap Vcap:ℕ) (own packed:ℕ→ℕ→ℕ):Prop:=
  ∀r v R V,1≤r→ r+R≤Rcap→v+V≤Vcap→ own r v+packed R V≤packed (r+R) (v+V)

theorem GPG (Rcap Vcap:ℕ) (own packed:ℕ→ℕ→ℕ) (hb:Bellman Rcap Vcap own packed)
    (s:Finset ι) (r v:ι→ℕ) (hr: ∀i∈s,1≤r i)
    (hR:(∑ i∈s,r i)≤Rcap) (hV:(∑ i∈s,v i)≤Vcap):
    (∑ i∈s,own (r i) (v i))≤packed (∑ i∈s,r i) (∑ i∈s,v i):=by
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert a s ha ih=>
    have hRi:r a+(∑ i∈s,r i)≤Rcap:=by simpa only [Finset.sum_insert ha] using hR
    have hVi:v a+(∑ i∈s,v i)≤Vcap:=by simpa only [Finset.sum_insert ha] using hV
    have hrec:=ih (fun i hi=>hr i (Finset.mem_insert_of_mem hi)) (by omega) (by omega)
    have hrow:=hb (r a) (v a) (∑ i∈s,r i) (∑ i∈s,v i) (hr a (Finset.mem_insert_self a s)) hRi hVi
    rw [Finset.sum_insert ha,Finset.sum_insert ha,Finset.sum_insert ha]
    exact (Nat.add_le_add_left hrec _).trans hrow

theorem sum_affine (Rcap Vcap slope:ℕ) (own packed:ℕ→ℕ→ℕ) (hb:Bellman Rcap Vcap own packed)
    (s:Finset ι) (r v z count:ι→ℕ) (hr: ∀i∈s,1≤r i)
    (hR:(∑ i∈s,r i)≤Rcap) (hV:(∑ i∈s,v i)≤Vcap)
    (hc: ∀i∈s,count i≤slope*z i+own (r i) (v i)):
    (∑ i∈s,count i)≤slope*(∑ i∈s,z i)+packed (∑ i∈s,r i) (∑ i∈s,v i):=by
  have h:=Finset.sum_le_sum hc
  rw [Finset.sum_add_distrib,←Finset.mul_sum] at h
  exact h.trans (Nat.add_le_add_left (GPG Rcap Vcap own packed hb s r v hr hR hV) _)

theorem one_heavy (H Rcap Vcap cap:ℕ) (s:Finset ι) (r v z count:ι→ℕ)
    (slope:A→ℕ) (own packed:A→ℕ→ℕ→ℕ) (single:ℕ→ℕ→ℕ→ℕ)
    (hr: ∀i∈s,1≤r i) (hR:(∑ i∈s,r i)≤Rcap) (hV:(∑ i∈s,v i)≤Vcap)
    (hH:(∑ i∈s,r i)<2*H)
    (hb: ∀a,Bellman Rcap Vcap (own a) (packed a))
    (hlight: ∀i∈s,r i<H→ ∀a,count i≤slope a*z i+own a (r i) (v i))
    (hsingle: ∀i∈s,count i≤single (r i) (v i) (z i))
    (hzero: ∃a,slope a*(∑ i∈s,z i)+packed a (∑ i∈s,r i) (∑ i∈s,v i)≤cap)
    (hheavy: ∀q u,H≤q→q≤∑ i∈s,r i→u≤∑ i∈s,v i→ ∃a,∀x,x≤∑ i∈s,z i→
      single q u x+slope a*((∑ i∈s,z i)-x)+packed a ((∑ i∈s,r i)-q) ((∑ i∈s,v i)-u)≤cap):
    (∑ i∈s,count i)≤cap:=by
  by_cases hex: ∃j∈s,H≤r j
  · obtain ⟨j,hj,hjH⟩:=hex
    have hsumR:=Finset.add_sum_erase s r hj
    have hsumV:=Finset.add_sum_erase s v hj
    have hsumZ:=Finset.add_sum_erase s z hj
    have hsumC:=Finset.add_sum_erase s count hj
    have hrem: ∀i∈s.erase j,r i<H:=by
      intro i hi
      have hri:r i≤∑ k∈s.erase j,r k:=Finset.single_le_sum (fun k _=>Nat.zero_le (r k)) hi
      omega
    have hjR:r j≤∑ i∈s,r i:=Finset.single_le_sum (fun i _=>Nat.zero_le (r i)) hj
    have hjV:v j≤∑ i∈s,v i:=Finset.single_le_sum (fun i _=>Nat.zero_le (v i)) hj
    have hjZ:z j≤∑ i∈s,z i:=Finset.single_le_sum (fun i _=>Nat.zero_le (z i)) hj
    obtain ⟨a,ha⟩:=hheavy (r j) (v j) hjH hjR hjV
    have hrest:=sum_affine Rcap Vcap (slope a) (own a) (packed a) (hb a) (s.erase j) r v z count
      (fun i hi=>hr i (Finset.mem_of_mem_erase hi)) (by omega) (by omega)
      (fun i hi=>hlight i (Finset.mem_of_mem_erase hi) (hrem i hi) a)
    have hhead:=hsingle j hj
    have hbudget:=ha (z j) hjZ
    rw [show (∑ i∈s,r i)-r j=∑ i∈s.erase j,r i by omega,
      show (∑ i∈s,v i)-v j=∑ i∈s.erase j,v i by omega,
      show (∑ i∈s,z i)-z j=∑ i∈s.erase j,z i by omega] at hbudget
    omega
  · have hl: ∀i∈s,r i<H:=by intro i hi;by_contra hn;exact hex ⟨i,hi,by omega⟩
    obtain ⟨a,ha⟩:=hzero
    exact (sum_affine Rcap Vcap (slope a) (own a) (packed a) (hb a) s r v z count hr hR hV
      (fun i hi=>hlight i hi (hl i hi) a)).trans ha

end NK
end MergedPart1

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace AHV
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266 RCN286
open DY FV MM
open Lower80899.Oracle Lower80899.BatchPhase
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ

theorem source_count
    (sound:Lower80899.Oracle.YF) (u0 u1:I→K)
    (kernel:WZ sound u0 u1)
    (H:P4) (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀g ∈ Gamma,(selected g).natDegree≤131071)
    (hagreement: ∀g ∈ Gamma,181235≤((Finset.univ:Finset I).filter (fun i=>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (F:RegularIndex H)
    (hR:(BG H F).all≤28)
    (hY:middle (BG H F)≤117)
    (hT:total (BG H F)≤11192)
    (hroute:sound.source.Routeable (BG H F)):
    (regularSeeds H selected Gamma F).card≤sound.potential.eval (BG H F):=by
  have he:BF H ({F}:Finset (RegularIndex H))=BG H F:=by
    simp [BF,sumFlag]
  have hs:=CSO sound kernel.D kernel.m kernel.weighted
    kernel.shape kernel.slope_le_m kernel.m_lt_char u0 u1 H selected Gamma
    hdegree hagreement hno kernel.gap_le_finrank {F}
    (by rw [he];exact hroute) (by rw [he];omega)
    (by rw [he];omega) (by rw [he];omega)
  exact PV.GFA F
    (fun f=>(regularSeeds H selected Gamma f).card)
    (fun f=>sound.potential.eval (BG H f)) hs

theorem raw_count
    (D:ℕ) (P:BT)
    (hDlow:131072≤D) (hDchar:D<2130706433)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ BA K D 131071 P.total P.s)
    (selected:K→Polynomial K) (Gamma:Finset K) (u0 u1:I→K)
    (hdegree: ∀g ∈ Gamma,(selected g).natDegree≤131071)
    (hagreement: ∀g ∈ Gamma,181235≤((Finset.univ:Finset I).filter (fun i=>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (F:RegularIndex Q)
    (hr:(BG Q F).all≤32)
    (hy:middle (BG Q F)≤149)
    (ht:total (BG Q F)≤8121)
    (hsafe:ABO.Safe (BG Q F).all
      (middle (BG Q F))):
    (regularSeeds Q selected Gamma F).card≤
      QH.rawCost (BG Q F):=by
  have hF:=ALY Q F.1 hQ D 131071 P.total P.s hbox F.2
  let p:=FX F.1
  let Pown:=RCN198.support (QH.padA p)
    (QH.padB p) (QH.padSlope p)
  have hcaps:=QH.EMS p hr hy ht
  have hb:=QH.own_box F.1 D 131071 P.total P.s hF.2.2
  let Fself:=KI.EBE Q F
  have hs:ABO.Safe (BG F.1 Fself).all
      (middle (BG F.1 Fself)):=by
    simpa only [BG,Fself,KI.ASI] using hsafe
  have hc:=QH.EOZ D Pown hDlow hDchar
    hcaps.1 hcaps.2.1 hcaps.2.2 F.1 hF.1.ne_zero hb
    (QH.own_support F.1) selected Gamma u0 u1
    hdegree hagreement hno Fself hs
  first
  | simpa only [RCN140.regularSeeds,BG,Fself,
      KI.ASI] using hc
  | (simp only [RCN140.regularSeeds,BG,Fself,
      KI.ASI]
     convert hc using 1<;>first | rfl | simp | exact Subsingleton.elim _ _ | omega)
  | (simp only [RCN140.regularSeeds,BG,Fself,
      KI.ASI]
     convert hc using 2<;>first | rfl | simp | exact Subsingleton.elim _ _ | omega)
  | (simp only [RCN140.regularSeeds,BG,Fself,
      KI.ASI]
     convert hc using 3<;>first | rfl | simp | exact Subsingleton.elim _ _ | omega)
  | (simp only [RCN140.regularSeeds,BG,Fself,
      KI.ASI]
     convert hc using 4<;>first | rfl | simp | exact Subsingleton.elim _ _ | omega)
  | exact hc

theorem FZL (g:Fin 21)
    (D:ℕ) (P:BT)
    (hDlow:131072≤D) (hDchar:D<2130706433)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ BA K D 131071 P.total P.s)
    (selected:K→Polynomial K) (Gamma:Finset K) (u0 u1:I→K)
    (hdegree: ∀g ∈ Gamma,(selected g).natDegree≤131071)
    (hagreement: ∀g ∈ Gamma,181235≤((Finset.univ:Finset I).filter (fun i=>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (F:RegularIndex Q)
    (hr:(BG Q F).all≤31)
    (hy:middle (BG Q F)≤142)
    (ht:total (BG Q F)≤7501)
    (ha:ATY.Active g (BG Q F)):
    (regularSeeds Q selected Gamma F).card≤
      ATY.ledgerCap g (BG Q F):=by
  have hF:=ALY Q F.1 hQ D 131071 P.total P.s hbox F.2
  have hsub:=ACS Q selected Gamma F
  have hcum:=GX F.1
  have hsmallT:wt AT F.1≤7501:=by
    simpa only [BG,total,hcum.2.2] using ht
  have hsmallY:wt BC F.1≤142:=by
    simpa only [BG,middle,hcum.2.1] using hy
  have hcount:=ATY.EUE g
    (nodes:=IRSProfile.domain) (u0:=u0) (u1:=u1)
    D P.total P.s F.1 hDlow hDchar hF.1 hF.2.1 hF.2.2 hsmallT hsmallY hr
    selected (regularSeeds Q selected Gamma F)
    (fun g hg=>hdegree g (hsub hg)) (fun g hg=>hagreement g (hsub hg))
    (fun g hg=>(Finset.mem_filter.mp hg).2.1)
    (fun g hg=>(Finset.mem_filter.mp hg).2.2)
    (KX selected Gamma _ 131071 80909 hsub hno)
    (by norm_num [I,IRSProfile.Index]) ha
  exact hcount

theorem root_count
    (D:ℕ) (P:BT)
    (hDlow:131072≤D) (hDchar:D<2130706433)
    (Q:P4) (hQ:Q ≠ 0) (hbox:Q ∈ BA K D 131071 P.total P.s)
    (selected:K→Polynomial K) (Gamma:Finset K) (u0 u1:I→K)
    (hdegree: ∀g ∈ Gamma,(selected g).natDegree≤131071)
    (hagreement: ∀g ∈ Gamma,181235≤((Finset.univ:Finset I).filter (fun i=>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno:BL selected Gamma 131071 80909) (F:RegularIndex Q)
    (th:Array ℕ) (w:ℕ) (hw:1≤w) (hw16:w≤21)
    (ha:EK.Active th w (BG Q F).all
      (BG Q F).yz (BG Q F).zOnly
      (BG Q F).zOnly):
    (regularSeeds Q selected Gamma F).card≤EK.rootUpper w
      (BG Q F).all (BG Q F).yz (BG Q F).zOnly:=by
  have h:=ha
  simp only [EK.Active,if_neg (show¬32≤w by omega),
    if_neg (show w≠0 by omega),if_pos hw16] at h
  rcases h with ⟨hr3,hr31,hv2,hz3,hL,hy,ht⟩
  have hc:=FZL (EK.rootIndex w) D P hDlow hDchar Q hQ hbox
    selected Gamma u0 u1 hdegree hagreement hno F hr31
    (by simpa only [middle,Nat.add_comm] using hy)
    (by simpa only [total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht)
    ⟨hr3,hv2,hz3,hL⟩
  simpa only [ATY.ledgerCap,WI.roundedCaps,
    WI.Receipt.rounded_formula,EK.rootUpper,
    EK.rootSlope,EK.FSY] using hc

theorem source_total (j:ℕ) (hj:j<7):11192≤(Lower80899.TenPhase.sound j).source.totalCap:=by
  interval_cases j<;>decide+kernel

end
end AHV
end MergedPart0
section MergedPart1
namespace WT
open DZ EK
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 50000

def carrier (r v:ℕ):Carrier:=
  ⟨AMT.cost r v 0,AMT.cost r v 1,AMT.cost r v 2,
    AMT.cost r v 3,AMT.cost r v 4⟩
theorem GFS (r v:ℕ):(carrier r v).Correct r v:=⟨rfl,rfl,rfl,rfl,rfl⟩

def pointCheck (r v w lo hi z:ℕ) (start:ℕ) (p:Piece):Bool:=
  if lo≤z∧z≤hi then Nat.ble (choice (carrier r v) w r v z) (value p start z) else true

theorem EBJ (r v w lo hi z start:ℕ) (p:Piece)
    (h:pointCheck r v w lo hi z start p=true) (hl:lo≤z) (hh:z≤hi):
    choice (carrier r v) w r v z≤value p start z:=by
  simpa only [pointCheck,if_pos (show lo≤z∧z≤hi from ⟨hl,hh⟩),Nat.ble_eq] using h

def high (r v w lo hi:ℕ) (start:ℕ) (p:Piece):Bool:=
  let a:=max lo 3
  if a≤hi then Nat.ble (choice (carrier r v) w r v a) (value p start a) &&
    Nat.ble (choice (carrier r v) w r v hi) (value p start hi) else true

def checkPair (r v:ℕ) (th:Array ℕ) (start:ℕ) (p:Piece) (runStart:ℕ) (run:Piece):Bool:=
  let lo:=max start runStart
  let stop:=min p.stop run.stop
  if lo<stop then
    decide (Active th run.base r v lo (stop-1)) &&
    pointCheck r v run.base lo (stop-1) 0 start p && pointCheck r v run.base lo (stop-1) 1 start p &&
    pointCheck r v run.base lo (stop-1) 2 start p && high r v run.base lo (stop-1) start p
  else true

theorem GFW (r v:ℕ) (th:Array ℕ) (start:ℕ) (p:Piece)
    (runStart:ℕ) (run:Piece) (z:ℕ)
    (hc:checkPair r v th start p runStart run=true)
    (hp:start≤z) (hp' :z<p.stop) (hr:runStart≤z) (hr' :z<run.stop):
    Active th run.base r v z z∧choice (carrier r v) run.base r v z≤value p start z:=by
  let lo:=max start runStart
  let hi:=min p.stop run.stop-1
  have hn:max start runStart<min p.stop run.stop:=by omega
  simp only [checkPair,if_pos hn,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨ha,h0⟩,h1⟩,h2⟩,hh⟩:=hc
  have hlo:lo≤z:=by dsimp only [lo];omega
  have hhi:z≤hi:=by dsimp only [hi];omega
  have hzActive:Active th run.base r v z z:=by
    exact active_at th run.base r v lo hi z ha hlo hhi
  refine ⟨hzActive,?_⟩
  by_cases hz3:3≤z
  · have ha3:max lo 3≤hi:=by omega
    change high r v run.base lo hi start p=true at hh
    simp only [high,if_pos ha3,Bool.and_eq_true,Nat.ble_eq] at hh
    have hl3:start≤max lo 3:=by dsimp only [lo];omega
    have hbound:=TP.BCJ (max lo 3) hi z (max lo 3) start
      (choice (carrier r v) run.base r v (max lo 3)) p.base
      (choiceSlope (carrier r v) run.base r v) p.slope le_rfl hl3 (by omega) hhi
      (by simpa only [value,Nat.sub_self,Nat.mul_zero,Nat.add_zero] using hh.1)
      (by rw [←FQA (carrier r v) run.base r v (max lo 3) hi (le_max_right _ _) ha3];exact hh.2)
    rwa [←FQA (carrier r v) run.base r v (max lo 3) z (le_max_right _ _) (by omega)] at hbound
  · have hpoint:z=0∨z=1∨z=2:=by omega
    rcases hpoint with rfl | rfl | rfl
    · exact EBJ r v run.base lo hi 0 start p h0 hlo hhi
    · exact EBJ r v run.base lo hi 1 start p h1 hlo hhi
    · exact EBJ r v run.base lo hi 2 start p h2 hlo hhi

def check (r v:ℕ) (th:Array ℕ) (curve runs:List Piece):Bool:=
  validFrom (11193-r-v) 0 curve && validFrom (11193-r-v) 0 runs &&
    allCells (fun lo p=>allCells (checkPair r v th lo p) 0 runs) 0 curve

theorem check_sound (r v:ℕ) (th:Array ℕ) (curve runs:List Piece)
    (hc:check r v th curve runs=true) (z:ℕ) (hz:z<11193-r-v):
    ∃w,Active th w r v z z∧choice (carrier r v) w r v z≤DZ.eval curve z:=by
  simp only [check,Bool.and_eq_true] at hc
  obtain ⟨lo,p,hlo,hhi,he,hp⟩:=cell_at _ 0 _ curve hc.1.1 (ANC _ 0 curve hc.2) z (Nat.zero_le _) hz
  obtain ⟨rlo,run,hrlo,hrhi,_,hcheck⟩:=cell_at _ 0 _ runs hc.1.2 (ANC _ 0 runs hp) z (Nat.zero_le _) hz
  have h:=GFW r v th lo p rlo run z hcheck hlo hhi hrlo hrhi
  exact ⟨run.base,h.1,by simpa only [DZ.eval,he] using h.2⟩

end WT
end MergedPart1
section MergedPart2
namespace CRJ
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266 RCN286
open DY FV MM
open Lower80899.Oracle Lower80899.BatchPhase
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ

open AHV
theorem GFQ
    (D:ℕ) (P:BT)
    (hDlow:131072≤D) (hDchar:D<2130706433)
    (Q:P4) (hQ:Q ≠ 0) (hbox:Q ∈ BA K D 131071 P.total P.s)
    (selected:K→Polynomial K) (Gamma:Finset K) (u0 u1:I→K)
    (hdegree: ∀g ∈ Gamma,(selected g).natDegree≤131071)
    (hagreement: ∀g ∈ Gamma,181235≤((Finset.univ:Finset I).filter (fun i=>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (F:RegularIndex Q) (hr:(BG Q F).all≤28)
    (hy:middle (BG Q F)≤117) (ht:total (BG Q F)≤11192)
    (c:EK.Carrier) (th:Array ℕ) (who:ℕ)
    (hc:c.Correct (BG Q F).all (BG Q F).yz)
    (hactive:EK.Active th who (BG Q F).all
      (BG Q F).yz (BG Q F).zOnly (BG Q F).zOnly)
    (hthreshold: ∀j,j<7→Lower80899.AMY.QM
      (Lower80899.TenPhase.sound j).source (BG Q F).all
      (BG Q F).yz (EK.thresholdAt th j)):
    (regularSeeds Q selected Gamma F).card≤EK.choice c who
      (BG Q F).all (BG Q F).yz (BG Q F).zOnly:=by
  let p:=BG Q F
  have hr1:1≤p.all:=JH Q F
  have ht' :p.all+p.yz+p.zOnly≤11192:=by
    simpa only [p,total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
  by_cases hn:32≤who
  · have ha:who≤861∧
        UR.Active (EK.extraChoice who) p.all p.yz p.zOnly∧
        UR.Active (EK.extraChoice who) p.all p.yz p.zOnly:=by
      simpa only [EK.Active,if_pos hn] using hactive
    have hF:=ALY Q F.val hQ D 131071 P.total P.s hbox F.property
    have hh:=UR.count IRSProfile.domain u0 u1
      (by norm_num [IRSProfile.Index]) selected Gamma ⟨hdegree,hagreement,hno⟩
      F hDlow hDchar hF.2.2 (EK.extraChoice who) ha.2.1
    simpa only [EK.choice,if_pos hn] using hh
  by_cases h0:who=0
  · subst who
    simp only [EK.choice,EK.Active,if_neg hn,if_pos] at hactive ⊢
    rw [EK.Carrier.eval_correct c _ _ _ hr1 hc]
    have hh:=raw_count D P hDlow hDchar Q hQ hbox selected Gamma u0 u1 hdegree hagreement hno F
      hactive.1 (by simpa only [middle,Nat.add_comm] using hactive.2.1)
      (by simpa only [total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hactive.2.2.1)
      (by simpa only [middle,Nat.add_comm] using hactive.2.2.2)
    exact hh
  by_cases h16:who≤21
  · simp only [EK.choice,if_neg hn,if_neg h0,if_pos h16]
    exact root_count D P hDlow hDchar Q hQ hbox selected Gamma u0 u1 hdegree hagreement hno F th who
      (by omega) h16 hactive
  · have ha:who-22<8∧EK.thresholdAt th
        (EK.phaseIndex (who-22))≤p.zOnly:=by
      simpa only [EK.Active,if_neg hn,if_neg h0,if_neg h16] using hactive
    by_cases hj:who-22<7
    · have hc:EK.thresholdAt th (who-22)≤p.zOnly:=by
        simpa only [EK.phaseIndex,if_pos hj] using ha.2
      have hroute:=Lower80899.AMY.DHC (Lower80899.TenPhase.sound (who-22)).source
        p.all p.yz (EK.thresholdAt th (who-22)) p.zOnly
        (source_total _ hj) ht' hc (hthreshold _ hj)
      have hh:=source_count (Lower80899.TenPhase.sound (who-22)) u0 u1
        (Lower80899.TenPhase.kernel u0 u1 (who-22)) Q selected Gamma hdegree hagreement hno F hr hy ht hroute
      simpa only [EK.choice,if_neg hn,if_neg h0,if_neg h16,
        EK.BSY,if_pos hj,rawFlag,p] using hh
    · have hc:EK.thresholdAt th 5≤p.zOnly:=by
        simpa only [EK.phaseIndex,if_neg hj] using ha.2
      have hroute:=Lower80899.AMY.DHC (Lower80899.TenPhase.sound 5).source
        p.all p.yz (EK.thresholdAt th 5) p.zOnly
        (source_total 5 (by decide)) ht' hc (hthreshold 5 (by decide))
      change Lower80899.SourceSound.PhaseFinal.source.Routeable (BG Q F) at hroute
      have hh:=source_count Lower80899.SourceSound.PhaseFinal.sound u0 u1
        (Lower80899.SourceSound.PhaseFinal.kernel u0 u1) Q selected Gamma hdegree hagreement hno F hr hy ht hroute
      simpa only [EK.choice,if_neg hn,if_neg h0,if_neg h16,
        EK.BSY,if_neg hj,Lower80899.SourceSound.PhaseFinal.sound,
        Potential.eval,rawFlag,middle,total,p] using hh


theorem GJI
    (D:ℕ) (P:BT)
    (hDlow:131072≤D) (hDchar:D<2130706433)
    (Q:P4) (hQ:Q ≠ 0) (hbox:Q ∈ BA K D 131071 P.total P.s)
    (selected:K→Polynomial K) (Gamma:Finset K) (u0 u1:I→K)
    (hdegree: ∀g ∈ Gamma,(selected g).natDegree≤131071)
    (hagreement: ∀g ∈ Gamma,181235≤((Finset.univ:Finset I).filter (fun i=>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (F:RegularIndex Q) (hr:(BG Q F).all≤28)
    (hy:middle (BG Q F)≤117) (ht:total (BG Q F)≤11192)
    (th:Array ℕ) (curve runs:List DZ.Piece)
    (hcheck:WT.check (BG Q F).all
      (BG Q F).yz th curve runs=true)
    (hthreshold: ∀j,j<7→Lower80899.AMY.QM
      (Lower80899.TenPhase.sound j).source (BG Q F).all
      (BG Q F).yz (EK.thresholdAt th j)):
    (regularSeeds Q selected Gamma F).card≤DZ.eval curve (BG Q F).zOnly:=by
  let p:=BG Q F
  have hz:p.zOnly<11193-p.all-p.yz:=by
    have h:p.all+p.yz+p.zOnly≤11192:=by
      simpa only [p,total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
    omega
  obtain ⟨who,ha,hb⟩:=WT.check_sound p.all p.yz th curve runs hcheck p.zOnly hz
  exact (GFQ D P hDlow hDchar Q hQ hbox selected Gamma u0 u1 hdegree hagreement hno
    F hr hy ht (WT.carrier p.all p.yz) th who
    (WT.GFS _ _) ha hthreshold).trans hb

end
end CRJ
end MergedPart2
section MergedPart3
namespace CL
open DZ WT EMO
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

structure Header where
  cut:ℕ
  runs:List Lower80899.BLW.Run
  deriving Inhabited

def decodeRuns:ℕ→ℕ→List Lower80899.BLW.Run
  | 0,_=>[]
  | n+1,code=>⟨code%16384,code/16384%16⟩::decodeRuns n (code/262144)

def AH:ℕ→ℕ→List Header
  | 0,_=>[]
  | n+1,code=>
    let count:=code/16384%16
    ⟨code%16384,decodeRuns count (code/262144)⟩::
      AH n (code/(262144*262144^count))

structure Row where
  curve:List Piece
  choices:List Piece
  headers:Array Header
  deriving Inhabited

def thresholds (d:Row):Array ℕ:=d.headers.map Header.cut

def allN (p:ℕ→Bool):ℕ→Bool
  | 0=>true
  | n+1=>allN p n && p n

theorem allN_sound (p:ℕ→Bool) (n:ℕ) (h:allN p n=true):
    ∀j,j<n→p j=true:=by
  induction n with
  | zero=>omega
  | succ n ih=>
    simp only [allN,Bool.and_eq_true] at h
    intro j hj
    by_cases he:j=n
    · simpa only [he] using h.2
    · exact ih h.1 j (by omega)

def GOE (r v:ℕ) (d:Row) (j:ℕ):Bool:=
  thresholdK (Lower80899.TenPhase.sound j).source r v
    (EK.thresholdAt (thresholds d) j)
    ((d.headers[j]?).getD default).runs

def check (r v:ℕ) (d:Row):Bool:=
  allN (GOE r v d) 7 && WT.check r v (thresholds d) d.curve d.choices

theorem ECR (r v:ℕ) (d:Row) (h:check r v d=true):
    ∀j,j<7→Lower80899.AMY.QM
      (Lower80899.TenPhase.sound j).source r v (EK.thresholdAt (thresholds d) j):=by
  simp only [check,Bool.and_eq_true] at h
  intro j hj
  exact GCF _ _ _ _ _ (allN_sound _ 7 h.1 j hj)

theorem check_curve (r v:ℕ) (d:Row) (h:check r v d=true):
    WT.check r v (thresholds d) d.curve d.choices=true:=by
  simp only [check,Bool.and_eq_true] at h
  exact h.2

end CL
end MergedPart3
section MergedPart4
namespace GIM
open CL
set_option autoImplicit false









end GIM
end MergedPart4

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower.BitDecode80909
open DZ
set_option autoImplicit false
set_option maxHeartbeats 10000000

lemma shr(x n:ℕ):Nat.shiftRight x n=x/2^n:=by exact Nat.shiftRight_eq_div_pow x n
lemma mask(x n:ℕ):Nat.land x (2^n-1)=x%2^n:=by exact Nat.and_two_pow_sub_one_eq_mod x n

def aux (bb sb:ℕ):ℕ→ℕ→List Piece
 | 0,_=>[]
 | n+1,code=>
  ⟨Nat.land code (2^14-1),Nat.land (Nat.shiftRight code 14) (2^bb-1),Nat.land (Nat.shiftRight code (14+bb)) (2^sb-1)⟩::
   aux bb sb n (Nat.shiftRight code (14+bb+sb))
lemma aux_eq(bb sb n code:ℕ):aux bb sb n code=DZ.decodeAux (2^bb) (2^sb) n code:=by
 induction n generalizing code with
 | zero=>rfl
 | succ n ih=>
  simp only [aux,DZ.decodeAux,ih,shr,mask,Nat.pow_add,Nat.div_div_eq_div_mul]
  rfl

def decode(bb sb code:ℕ):List Piece:=aux bb sb (Nat.land code (2^16-1)) (Nat.shiftRight code 16)
lemma decode_eq(bb sb code:ℕ):decode bb sb code=DZ.decode bb sb code:=by
 simp only [decode,aux_eq,DZ.decode,mask,shr]
 rfl
#print axioms decode_eq
end ProximityPrize.SubmissionLower.BitDecode80909
end
section
local notation "BCurve" => ProximityPrize.SubmissionLower.BitDecode80909.decode
namespace ProximityPrize.SubmissionLower
namespace AXX
open DZ CL
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
def d0:Row:=⟨BCurve 52 39 0x166aa1fa1b675771a553eb6862fc24e92ded4160b8e000900008002200170001ada58000000000000a000700009000c0000000000003800280003800400000000000010000c000140010006,decode 5 1 0x76bb86a0b801b4b0000300002000010006,(AH 7 0xaee020b860146804f8000cd9727029180a3a0282000346521c175605d281708000d1e15706098181a05f6000348161c26f609b282618000d180e).toArray⟩
theorem h0:check 1 0 d0=true:=by decide+kernel
def d1:Row:=⟨BCurve 52 40 0x3153d0fba18aaedda553eb6862d3b45780e05fe09f9000580004001c001200011657c0000000000004c0032000340030000000000000a00070000900080000000000001c00140001c0010006,decode 5 1 0x76bb76a09f0195f0000300002000010006,(AH 7 0xaedc209f6014680508000cd95f7029180a3a02860003464d9c177605d681718000d1dfc7060d8182a05fa0003480f5c271609b682628000d17fe).toArray⟩
theorem h1:check 1 1 d1=true:=by decide+kernel
def d2:Row:=⟨BCurve 52 40 0x35d25e030c46aed9a553eb6862dbeb46b311146086b000680004002b001a8001565300000000000008000500004400300000000000015000d8000d000800000000000028001c000240010006,decode 5 1 0x76bb66a0860194c0000300002000010006,(AH 7 0x2bb6082198051a014200033653180a4a028600033648dc178605de81728000d1de3706118183a05fe000348085c272609be82648000d17ed).toArray⟩
theorem h2:check 1 2 d2=true:=by decide+kernel
def d3:Row:=⟨BCurve 52 41 0x74a1d614ee055da9a553eb6862e43c8b23f84ee06d88004c000200258015c000cb2740000000000003a002200015000c00000000000052003100022001000000000000060003c000340010006,decode 5 1 0x76bb56a06d0193a0000300002000010006,(AH 7 0x2bb5081b5c0526014680508000d193a7029580a4a028a000346441c179605e281738000d1dc9706198185a0606000348011c274609c682668000d17dc).toArray⟩
theorem h3:check 1 3 d3=true:=by decide+kernel
def d4:Row:=⟨BCurve 53 41 0xfb3de04786fabb434aa7d6d0c2ec737a56290360538cfb0a3e44777c8f3a9d2bc5927b800640002001c400fe000758fe00000000000016800cc0006400300000000000010c009a000540020000000000000b00068000440010007,decode 5 1 0x76bb46a05365927018fe0000300002000010007,(AH 7 0x2bb40814d8052a014200033649d80a5a028a0003363f9c17a605e681758000d1db07061d8186a060a000347fa1c275609ca82678000d17cb).toArray⟩
theorem h4:check 1 4 d4=true:=by decide+kernel
def d5:Row:=⟨BCurve 53 41 0x10d38146531eabb334aa7d6d0c2f4aa698859b7e0398cfb0a3e447826d87917c549914e8007c000200274015a000858eb000000000000200011c0007400300000000000018c00de0006400200000000000011800a0000540010007,decode 5 1 0x76bb36a03965914018eb0000300002000010007,(AH 7 0xaecc20396014a80508000cd9147029980a5a028e0003463adc17b605ea81768000d1d96706218187a060e000347f2dc277609d282698000d17ba).toArray⟩
theorem h5:check 1 5 d5=true:=by decide+kernel
def d6:Row:=⟨BCurve 53 42 0x47cc9220b736aec86954fada185f9c2b17514d8c03e8cfb0a3e4478d121b7925ecd9018c004a00010019e00e10004ac6c0000000000000ac005e00021000c000000000000448025c000e800400000000000019800e4000640010007,decode 5 1 0x76bb26a01f65901018d80000300002000010007,(AH 7 0x2bb20807d8052a014600033640580a6a028e000336361c17d605ee81778000d1d7c706298189a0616000347eb9c279609da826b8000d17a8).toArray⟩
theorem h6:check 1 6 d6=true:=by decide+kernel
def d7:Row:=⟨BCurve 53 42 0x4c4b1f2821f2aec46954fada1860a308fd97641c0088cfb0a3e447977031dbb06318eea4005600010020e011b00052c620000000000000de007800025000c0000000000005a80314001080040000000000002300134000740010007,decode 5 1 0x76bb16a004658ee018c40000300002000010007,(AH 7 0x2bb108011c0536014a80518000d18ee7029d80a6a0292000346311c17e605f681798000d1d627062d818aa061a000347e45c27b609de826d8000d1797).toArray⟩
theorem h7:check 1 7 d7=true:=by decide+kernel
def d8:Row:=⟨BCurve 53 42 0x50c9ac2f8caeaec06954fada1861a69c3c06a9ebfd28cfb0a3e447a214c5c359fb58dabc006200010028a015b0005ac58800000000000116009500029000c00000000000073803e4001280040000000000002e00190000840010007,decode 5 1 0x76bb069fe9658da018b10000300002000010007,(AH 7 0xaec01fe97014d8052a014600034636980a7a02920003362c5c17f605fa817a8000d1d4870631818ba061e000347dd1c27c609e6826f8000d1786).toArray⟩
theorem h8:check 1 8 d8=true:=by decide+kernel
def d9:Row:=⟨BCurve 53 42 0x55483936f76aaebc6954fada1862ad7a224cc07bf9c8cfb0a3e447acb959ab039398c7d4006e00010031201a100062c4f00000000000015400b50002d000c0000000000008f804cc001480040000000000003a801f8000940010007,decode 5 1 0x76baf69fce658c70189e0000300002000010007,(AH 7 0xaebc1fce6014e80518000cd8c7702a180a7a0296000346279c181605fe817b8000d1d2d70639818da0626000347d5dc27e609ee82708000d1774).toArray⟩
theorem h9:check 1 9 d9=true:=by decide+kernel
def d10:Row:=⟨BCurve 53 42 0x59c6c63e6226aeb86954fada1863b4580892d70bf648cfb0a3e447b717700d8e09d8b4ec007a0001003a601ed0006ac4500000000000019800d800031000c000000000000ae805cc00168004000000000000488026c000a40010007,decode 5 1 0x76bae69fb2658b40188a0000300002000010007,(AH 7 0x2bae07ec98053a014a0003362d180a8a0296000336229c18260606817d8000d1d137063d818ea062a000347ce5c280609f682728000d1762).toArray⟩
theorem h10:check 1 10 d10=true:=by decide+kernel
def d11:Row:=⟨BCurve 53 43 0x179154d17338abad0d2a9f5b430c96fd68e0439b7e588cfb0a3e447c1bc03f537a218a0820043000080223011f8003961dc00000000000078803f8000d40030000000000001a100dc80031000800000000000058002ec000b40010007,decode 5 1 0x76bad69f96658a0018770000300002000010007,(AH 7 0x2bad07e59c0546014e80528000d18a0702a580a8a029a0003461ddc1836060a817e8000d1cf8706458190a0632000347c6dc282609fa82748000d1751).toArray⟩
theorem h11:check 1 11 d11=true:=by decide+kernel
def d12:Row:=⟨BCurve 53 43 0x18b0f8134de7abac0d2a9f5b430cb76fd0ae2c557de88cfb0a3e447cc1a1a57c218588c8e0049000080279014b8003d618c0000000000008c8049c000e40030000000000001eb01028003500080000000000006900378000c40010007,decode 5 1 0x76bac69f7a6588c018630000300002000010007,(AH 7 0x2bac07de9c0546014e80528000d188c702a580a8a029a00034618dc1856060e817f8000d1cdd706498191a0636000347bf5c28360a0282768000d173f).toArray⟩
theorem h12:check 1 12 d12=true:=by decide+kernel
def d13:Row:=⟨BCurve 53 43 0x19d09b552896abab0d2a9f5b430cd7e2387c150f7d788cfb0a3e447d67830ba4c8e98789a004f0000802d5017a80041613c000000000000a20054c000f400300000000000023b012b8003900080000000000007b80410000d40010007,decode 5 1 0x76bab69f5e658780184f0000300002000010007,(AH 7 0xaeac1f5e6015280538000cd878702a980a9a029e00034613dc1866061681818000d1cc2706518192a063e000347b7dc28560a0a82788000d172d).toArray⟩
theorem h13:check 1 13 d13=true:=by decide+kernel
def d14:Row:=⟨BCurve 55 43 0x1af03e970345abaa0d2a9f5b43033e1528127f725f43233ec28f9107e0d6471cd704d8648d4523066a5ef522dcffdb55183ba600550000800cdc06b2001157d80000000000000b900608001040030000000000000a44055e000f400200000000000008f804b4000e40010008,decode 5 1 0x76baa69f43658645983b017d80000300002000010008,(AH 7 0x2baa07d0d8054a014e00033619180aaa029e0003360edc1876061a81828000d1ca6706558194a0642000347b01c28760a12827a8000d171b).toArray⟩
theorem h14:check 1 14 d14=true:=by decide+kernel
def d15:Row:=⟨BCurve 55 43 0x1c0fe1d8ddf4aba90d2a9f5b43034631c205f9a0df29233ec28f9107eb345d7f617b18508d4523066a5e4dd0435cc0125827b2005b0000800e7c0786001257090000000000000d1806d0001140030000000000000bb4061a001040020000000000000a500564000f40010008,decode 5 1 0x76ba969f296585059827017090000300002000010008,(AH 7 0x2ba907ca5c0556015280538000d1850702ad80aaa02a200034609dc1896061e81848000d1c8b7065d8196a064a000347a89c28960a1a827c8000d1709).toArray⟩
theorem h15:check 1 15 d15=true:=by decide+kernel
def d16:Row:=⟨BCurve 55 43 0x1d2f851ab8a3aba80d2a9f5b43034e4e5bf973cf5f0f233ec28f9107f54bf65ccccf583c8d4523066a5e7715bf711db21812be006100008010340866001356f70000000000000eb807a4001240030000000000000d3c06e2001140020000000000000bc00620001040010008,decode 5 1 0x76ba869f0f6583c59812016f70000300002000010008,(AH 7 0xaea01f0f701558054a014e0003460f180aba02a2000336049c18a6062681858000d1c6f706618197a0652000347a0dc28b60a22827e8000d16f7).toArray⟩
theorem h16:check 1 16 d16=true:=by decide+kernel
def d17:Row:=⟨BCurve 55 43 0x1e4f285c9352aba70d2a9f5b4303566af5ecedfddef6233ec28f9107ffaa0cbf574598288d4523066a5e9f40b13f6e7d57feca006700008012040952001456e400000000000010700884001340030000000000000edc07b6001240020000000000000d4806e8001140010008,decode 5 1 0x76ba769ef665828597fe016e40000300002000010008,(AH 7 0xae9c1ef66015680548000cd828702b180aba02a6000345ff9c18c6062a81878000d1c53706698199a065600034798dc28d60a2a82808000d16e4).toArray⟩
theorem h17:check 1 17 d17=true:=by decide+kernel
def d18:Row:=⟨BCurve 55 43 0x1f6ecb9e6e01aba60d2a9f5b43035e6d3aa1b1a65edc233ec28f91080a082321e1bbd8138d4523066a5ec8862d53cc1d17ead6006d00008013ec0a4a001556d2000000000000124009700014400300000000000010940896001340020000000000000ee807bc001240010008,decode 5 1 0x76ba669edc65813597ea016d20000300002000010008,(AH 7 0x2ba607b718055a015200033604d80aca02a6000335fa9c18d6063281888000d1c367066d819aa065e000347911c28f60a2e82828000d16d2).toArray⟩
theorem h18:check 1 18 d18=true:=by decide+kernel
def d19:Row:=⟨BCurve 55 43 0x208e6ee048b0aba50d2a9f5b4303666f7f56754edec2233ec28f9108141fbbff4d1017fe8d4523066a5ef0b11f221ce857d5e2007300008015ec0b4e001656bf00000000000014280a6800154003000000000000126409820014400200000000000010a0089c001340010008,decode 5 1 0x76ba569ec2657fe597d5016bf0000300002000010008,(AH 7 0x2ba507b09c0566015680548000d17fe702b580aca02aa000345f55c18f60636818a8000d1c1a70675819ca0666000347891c29160a3682848000d16bf).toArray⟩
theorem h19:check 1 19 d19=true:=by decide+kernel
def d20:Row:=⟨BCurve 55 43 0x21ae1222235faba40d2a9f5b43036e8c1949ef7d5ea7233ec28f91081e3754dcb86457ea8d4523066a5f18dc10f06db397c0ee007900008018040c5e001756ac00000000000016280b6c00164003000000000000144c0a7a0015400200000000000012700988001440010008,decode 5 1 0x76ba469ea7657ea597c0016ac0000300002000010008,(AH 7 0xae901ea76015a80548000cd7ea702b980ada02ae000345f01c1906063e818b8000d1bfd7067d819ea066a000347811c29360a3e82868000d16ac).toArray⟩
theorem h20:check 1 20 d20=true:=by decide+kernel
def d21:Row:=⟨BCurve 55 43 0x22cdb563fe0eaba30d2a9f5b4303768e5dfeb325de8c233ec28f9108284eedba23b897d58d4523066a5f42218d04cb5357abfa007f0000801a340d7a0018569a00000000000018400c7c00174003000000000000164c0b7e0016400200000000000014580a80001540010008,decode 5 1 0x76ba369e8c657d5597ab0169a0000300002000010008,(AH 7 0xae8c1e8c6015a80558000cd7d5702b980ada02ae000345eadc19260646818d8000d1be070685819fa067200034778dc29560a4682888000d169a).toArray⟩
theorem h21:check 1 21 d21=true:=by decide+kernel
def d22:Row:=⟨BCurve 55 44 0x11f6ac52ec5ed5d1034aa7d6d0c0dfa428acddb3979c4467d851f221064cd0d2f1e19af808d4523066a5f6a4c7ed31c1e97968300428000400e3e0751000cab43800000000000069c036600061000c00000000000030c8191c002e800400000000000016580b84001640010008,decode 5 1 0x76ba269e71657c059796016870000300002000010008,(AH 7 0x2ba2079c5c0576015a80558000d17c0702bd80aea02b2000345e59c1936064a818f8000d1bc37068981a1a067a00034770dc29760a4e828a8000d1687).toArray⟩
theorem h22:check 1 22 d22=true:=by decide+kernel
def d23:Row:=⟨BCurve 55 44 0x12867df3d9b655d0834aa7d6d0c0e19e248a60fc37954467d851f221078fc3ee9f4c22f548d4523066a5f915ce65b601557818900458000400f6e07eb000d2b39800000000000072e03b000065000c00000000000035281b540030800400000000000018700c94001740010008,decode 5 1 0x76ba169e55657aa59781016730000300002000010008,(AH 7 0xae841e557015d8056a0156000345ea980afa02b2000335e05c1956065281908000d1ba57069181a3a0682000347689c29960a5a828c8000d1673).toArray⟩
theorem h23:check 1 23 d23=true:=by decide+kernel
def d24:Row:=⟨BCurve 55 44 0x13164f94c70dd5d0034aa7d6d0c0e39eb5b791e6578e4467d851f22108c9e759a8d26af2a8d4523066a5fb987d829b0e0976b8f004880004010aa088b000dab3000000000000007c603fd00069000c00000000000039b81da4003280040000000000001aa00db0001840010008,decode 5 1 0x76ba069e39657955976b016600000300002000010008,(AH 7 0xae801e396015e80568000cd795702c180afa02b6000345dadc1976065681928000d1b887069981a5a0686000347601c29b60a62828e8000d1660).toArray⟩
theorem h24:check 1 24 d24=true:=by decide+kernel
def d25:Row:=⟨BCurve 55 44 0x13a62135b46555cf834aa7d6d0c0e598b195152ef7874467d851f2210a0cda75563cf2efe8d4523066a5fe1b2c9f801abd75695004b80004011f20931000e2b268000000000000864044d0006d000c0000000000003e78200c003480040000000000001ce80ed8001940010008,decode 5 1 0x76b9f69e1d6577f597560164d0000300002000010008,(AH 7 0xae7c1e1d6015e80568000cd77f702c580b0a02ba000345d59c1986065e81948000d1b6a706a181a6a068e00034757dc29d60a6a82918000d164d).toArray⟩
theorem h25:check 1 25 d25=true:=by decide+kernel
def d26:Row:=⟨BCurve 56 44 0xa1af96b50de6ae781a553eb686039e650b0918645e00119f6147c882168dfbc0bf8675da91a8a460cd4a008c3318045a297409b004e80004009a304ee8007558e400000000000024201280001c4003000000000000086d04518006d00080000000000001f48100c001a40010008,decode 5 1 0x76b9e69e006576a59740016390000300002000010008,(AH 7 0x2b9e07801c0586015e80568000d176a702c580b0a02ba000345d01c19a6066681958000d1b4b706a581a8a06960003474f5c29f60a7282938000d1639).toArray⟩
theorem h26:check 1 26 d26=true:=by decide+kernel
def d27:Row:=⟨BCurve 56 44 0xa62e23bc78a2ae741a553eb68603a64cfa7f2586dde2119f6147c88219024296d29305d511a8a460cd4a030ee234e966dd72aa100518000400a53054780079589800000000000026c813d8001d4003000000000000091104a480071000800000000000021c0114c001b40010008,decode 5 1 0x76b9d69de2657545972a016260000300002000010008,(AH 7 0xae741de26016280578000cd754702c980b1a02be000345ca9c19c6066a81978000d1b2d706ad81aaa069e00034746dc2a160a7a82958000d1626).toArray⟩
theorem h27:check 1 27 d27=true:=by decide+kernel
def d28:Row:=⟨BCurve 56 44 0xaaacb0c3e35eae701a553eb68603ae34e9f532a95dc5119f6147c8821b76896ce59f95cf91a8a460cd4a057fe8ad6da649714a700548000400b0905a38007d58480000000000002988153c001e400300000000000009bb04fa80075000800000000000024501298001c40010008,decode 5 1 0x76b9c69dc56573e59714016120000300002000010008,(AH 7 0x2b9c077158058a015e000335cf980b2a02c2000335c51c19e6067281998000d1b0e706b581aca06a60003473e1c2a460a8282988000d1612).toArray⟩
theorem h28:check 1 28 d28=true:=by decide+kernel
def d29:Row:=⟨BCurve 56 44 0xaf2b3dcb4e1aae6c1a553eb68603b61cd96b3fcbdda6119f6147c8821dead042f8ac25ca11a8a460cd4a07f0ef25f1e5b56fead00578000400bc506028008157f80000000000002c6016ac001f40030000000000000a6b055380079000800000000000026f813f0001d40010008,decode 5 1 0x76b9b69da665728596fe015fe0000300002000010008,(AH 7 0x2b9b07699c0596016280578000d1728702cd80b2a02c2000345bf9c19f6067a819b8000d1aef706bd81aea06ae000347355c2a660a8e829a8000d15fe).toArray⟩
theorem h29:check 1 29 d29=true:=by decide+kernel
def d30:Row:=⟨BCurve 56 44 0xb3a9cad2b8d6ae681a553eb68603bdea73a296685d88119f6147c882204d77b7c3f035c451a8a460cd4a0a61f59e7625216e7b3005a8000400c8706648008557a80000000000002f501828002040030000000000000b2105af8007d000800000000000029b81554001e40010008,decode 5 1 0x76b9a69d8865711596e7015ea0000300002000010008,(AH 7 0xae681d886016680588000cd711702d180b3a02c6000345b9dc1a160682819d8000d1acf706c581b0a06b60003472c9c2a860a96829c8000d15ea).toArray⟩
theorem h30:check 1 30 d30=true:=by decide+kernel
def d31:Row:=⟨BCurve 56 44 0xb82857da2392ae641a553eb68603c5d26318a38add69119f6147c88222c1be8dd6fcc5bed1a8a460cd4a0cd2fc16fa648d6d1b9005d8000400d4f06c9800895758000000000000325819b0002140030000000000000bdd060e8008100080000000000002c9016c4001f40010008,decode 5 1 0x76b9969d69656fb596d1015d60000300002000010008,(AH 7 0x2b99075a58059a0162000335bed80b4a02ca000335b45c1a36068a819f8000d1ab0706cd81b2a06be000347239c2ab60a9e829f8000d15d6).toArray⟩
theorem h31:check 1 31 d31=true:=by decide+kernel
def d32:Row:=⟨BCurve 56 44 0xbca6e4e18e4eae601a553eb68603cd9ffd4ffa275d49119f6147c88225246602a240d5b911a8a460cd4a0f3259eb1dd6b16babf00608000400e1d07318008d570400000000000035781b44002240030000000000000c9f06708008500080000000000002f801840002040010008,decode 5 1 0x76b9869d49656e4596ba015c10000300002000010008,(AH 7 0x2b9807525c05a6016680588000d16e4702d580b4a02ca000345ae9c1a56069281a18000d1a8f706d581b4a06c60003471a9c2ad60aaa82a18000d15c1).toArray⟩
theorem h32:check 1 32 d32=true:=by decide+kernel
def d33:Row:=⟨BCurve 56 44 0xc12571e8f90aae5c1a553eb68603d56d978750c3dd29119f6147c88227870d776d84e5b351a8a460cd4a11a36063a2161d6a3c500638000400ef1079c8009156b400000000000038b01ce4002340030000000000000d6706d5800890008000000000000328819c8002140010008,decode 5 1 0x76b9769d29656cd596a3015ad0000300002000010008,(AH 7 0xae5c1d296016a80598000cd6cd702d980b5a02ce000345a8dc1a76069a81a38000d1a6f706e181b6a06d2000347115c2af60ab282a48000d15ad).toArray⟩
theorem h33:check 1 33 d33=true:=by decide+kernel
def d34:Row:=⟨BCurve 56 44 0xc5a3fef063c6ae581a553eb68603dd3b31bea7605d08119f6147c88229e9b4ec38c8f5ad91a8a460cd4a1402be37c5884168ccb00668000400fcb080a8009556600000000000003c001e90002440030000000000000e35073d8008d000800000000000035a81b5c002240010008,decode 5 1 0x76b9669d08656b65968c015980000300002000010008,(AH 7 0x2b9607421805aa0166000335ad980b6a02d2000335a31c1a9606a281a58000d1a4e706e981b8a06da000347085c2b260aba82a68000d1598).toArray⟩
theorem h34:check 1 34 d34=true:=by decide+kernel
def d35:Row:=⟨BCurve 56 44 0xca228bf7ce82ae541a553eb68603e4ee76b74776dce7119f6147c8822c3abcffbc4485a791a8a460cd4a16621c0be8fa65674d1006980004010ab087b80099560c0000000000003f682048002540030000000000000f0907a880091000800000000000038e01cfc002340010008,decode 5 1 0x76b9569ce76569e59674015830000300002000010008,(AH 7 0x2b950739dc05b6016a80598000d169e702dd80b6a02d20003459d1c1ab606aa81a78000d1a2d706f181bba06e2000346fedc2b460ac682a98000d1583).toArray⟩
theorem h35:check 1 35 d35=true:=by decide+kernel
def d36:Row:=⟨BCurve 56 44 0xcea118ff393eae501a553eb68603ecbc10ee9e135cc5119f6147c8822e9d6474878895a1d1a8a460cd4a18c179e00c6c8965dd7006c800040119108ef8009d55b800000000000042e8220c002640030000000000000fe308168009500080000000000003c301ea8002440010008,decode 5 1 0x76b9469cc5656875965d0156e0000300002000010008,(AH 7 0xae501cc56016e805a8000cd687702e180b7a02d6000345975c1ad606b281a98000d1a0b706f981bda06ea000346f55c2b760ace82ab8000d156e).toArray⟩
theorem h36:check 1 36 d36=true:=by decide+kernel
def d37:Row:=⟨BCurve 56 44 0xd31fa606a3faae4c1a553eb68603f46f55e73e29dca4119f6147c88230ee6c880b04259bd1a8a460cd4a1b20d7b42fdead645dd006f800040127d0966800a15564000000000000468023dc0027400300000000000010c308878009900080000000000003f982060002540010008,decode 5 1 0x76b9369ca46566f59645015590000300002000010008,(AH 7 0xae4c1ca46016e805a8000cd66f702e580b8a02da000345915c1af606ba81ab8000d19e97070581bfa06f6000346ebdc2b960ada82ae8000d1559).toArray⟩
theorem h37:check 1 37 d37=true:=by decide+kernel
def d38:Row:=⟨BCurve 56 44 0xd79e330e0eb6ae481a553eb68603fc229adfde405c84119f6147c882333f749b8e7fb595d1a8a460cd4a1d8035885350d162de30072800040136f09e0800a555100000000000004a3025b80028400300000000000011a908fb8009d000800000000000043182224002640010008,decode 5 1 0x76b9269c84656575962d015440000300002000010008,(AH 7 0x2b9207211c05c6016e805a8000d1657702e580b8a02de0003458b5c1b1606c281ad8000d19c77070d81c2a06fe000346e21c2bc60ae282b18000d1544).toArray⟩
theorem h38:check 1 38 d38=true:=by decide+kernel
def d39:Row:=⟨BCurve 56 44 0xdc1cc0157972ae441a553eb6860403d5dfd87e56dc65119f6147c88235907caf11fb458fd1a8a460cd4a1fcdeab815f5ad615e9007580004014670a5d800a954b80000000000004df827a00029400300000000000012950972800a1000800000000000046b023f4002740010008,decode 5 1 0x76b9169c656563f596150152e0000300002000010008,(AH 7 0xae441c6560172805b8000cd63f702e980b9a02de000345855c1b4606ca81b08000d19a47071581c4a070a000346d85c2bf60aee82b38000d152e).toArray⟩
theorem h39:check 1 39 d39=true:=by decide+kernel
def d40:Row:=⟨BCurve 56 44 0xe09b4d1ce42eae401a553eb686040b8924d11e6d5c46119f6147c88237cfe5614dae5589d1a8a460cd4a222d488c3967d15fcef007880004015650add800ad546400000000000051d82994002a4003000000000000138709ec800a500080000000000004a6025d0002840010008,decode 5 1 0x76b9069c4665627595fc015190000300002000010008,(AH 7 0xae401c4660172805b8000cd627702ed80baa02e20003457f1c1b6606d281b28000d19817072181c7a0712000346ce5c2c160afa82b68000d1519).toArray⟩
theorem h40:check 1 40 d40=true:=by decide+kernel
def d41:Row:=⟨BCurve 56 44 0xe519da244eeaae3c1a553eb686041322148b07fddc26119f6147c8823a0f4e138961658391a8a460cd4a247afdbbfc0cad5e3f5007b80004016690b60800b1540c00000000000055d02b94002b4003000000000000147f0a69800a900080000000000004e2827b8002940010008,decode 5 1 0x76b8f69c266560e595e3015030000300002000010008,(AH 7 0xae3c1c2670176805c8000cd60e702f180bba02e600034578dc1b8606de81b48000d195e7072d81c9a071e000346c45c2c460b0282b98000d1503).toArray⟩
theorem h41:check 1 41 d41=true:=by decide+kernel
def d42:Row:=⟨BCurve 56 44 0xe998672bb9a6ae381a553eb686041abb0444f18e5c05119f6147c8823c4eb6c5c514757d51a8a460cd4a26b70a475de4415cafb007e80004017730be6800b553b000000000000059e02da0002c4003000000000000157d0ae9800ad0008000000000000520829ac002a40010008,decode 5 1 0x76b8e69c05655f5595ca014ec0000300002000010008,(AH 7 0x2b8e07015805da01720003357d580bca02ea000335729c1bb606e681b78000d19397073581cca072a000346ba1c2c760b0e82bc8000d14ec).toArray⟩
theorem h42:check 1 42 d42=true:=by decide+kernel
def d43:Row:=⟨BCurve 56 45 0x770b7a199231571a06954fada1810894fcffb6c7b6f90233ec28f91047d1c3ef0018f0aee11a8a460cd4a2904bf7720891d5b1808040c000200c418637c005ca9ac00000000000017820bee000b5000c0000000000002d0216d900162001000000000000056002bac002b40010008,decode 5 1 0x76b8d69be4655dc595b1014d60000300002000010008,(AH 7 0x2b8d06f91c05e60176805c8000d15dc702f580bca02ee0003456c5c1bd606f281b98000d19157074181cfa0732000346afdc2ca60b1a82bf8000d14d6).toArray⟩
theorem h43:check 1 43 d43=true:=by decide+kernel
def d44:Row:=⟨BCurve 56 45 0x794ac09d478f571806954fada1810a74a39e838a56f08233ec28f9104819b105478f52ae111a8a460cd4a2b5274a6e32df95988380424000200ccc867dc005ea98000000000000018920c77000b9000c0000000000002f1617e50016a00100000000000005a102db8002c40010008,decode 5 1 0x76b8c69bc2655c259598014c00000300002000010008,(AH 7 0xae301bc26017a805d8000cd5c2702f980bda02f2000345661c1bf606fa81bc8000d18f07074d81d1a073e000346a51c2cc60b2682c28000d14c0).toArray⟩
theorem h44:check 1 44 d44=true:=by decide+kernel
def d45:Row:=⟨BCurve 56 45 0x7b8a0720fced571606954fada1810c5adf8cfdee76e7c233ec28f910485f6a2f660ca4ad491a8a460cd4a2d8e813245058d57e868043c000200d5a86c540060a95200000000000019a80d03000bd000c000000000000313618f70017200100000000000005e382fd0002d40010008,decode 5 1 0x76b8b69b9f655a95957e014a90000300002000010008,(AH 7 0xae2c1b9f6017a805d8000cd5a9702fd80bea02f60003455f9c1c26070681be8000d18ca7075981d4a074a0003469a9c2cf60b3282c58000d14a9).toArray⟩
theorem h45:check 1 45 d45=true:=by decide+kernel
def d46:Row:=⟨BCurve 56 45 0x7dc94da4b24b571406954fada1810e3a862bcab116df0233ec28f91048a523598489f6ac791a8a460cd4a2fca8dbda6dd215648980454000200deb870e40062a9240000000000001ac40d92000c1000c00000000000033621a0f0017a0010000000000000627831f4002e40010008,decode 5 1 0x76b8a69b7c6558f59564014920000300002000010008,(AH 7 0xae281b7c7017e805e8000cd58f7030180bfa02f6000345591c1c56070e81c18000d18a47076581d7a07560003468f9c2d260b3e82c88000d1492).toArray⟩
theorem h46:check 1 46 d46=true:=by decide+kernel
def d47:Row:=⟨BCurve 56 45 0x8008942867a9571206954fada181101a2cca9773b6d60233ec28f91048eadc83a30748aba91a8a460cd4a32069a4908b4b554a8c8046c000200e7f8758c0064a8f60000000000001be60e24000c5000c000000000000359a1b2d00182001000000000000066d03424002f40010008,decode 5 1 0x76b8969b58655755954a0147b0000300002000010008,(AH 7 0xae241b586017e805e8000cd5757030580c0a02fa000345529c1c76071a81c48000d187d7077181daa0762000346849c2d560b4a82cb8000d147b).toArray⟩
theorem h47:check 1 47 d47=true:=by decide+kernel
def d48:Row:=⟨BCurve 56 45 0x8247daac1d07571006954fada18111f33e19b694d6ccc233ec28f910492e61c1988b8aaad11a8a460cd4a3430fe3009bf0152f8f80484000200f1687a4c0066a8c60000000000001d0e0eb9000c9000c00000000000037de1c510018a00100000000000006b403660003040010008,decode 5 1 0x76b8869b336555a5952f014630000300002000010008,(AH 7 0xae201b3370182805f8000cd55a7030980c1a02fe0003454bdc1ca6072681c78000d18567077d81dda0772000346795c2d860b5682ce8000d1463).toArray⟩
theorem h48:check 1 48 d48=true:=by decide+kernel
def d49:Row:=⟨BCurve 56 45 0x8487212fd265570e06954fada18113cc4f68d5b5f6c38233ec28f9104971e6ff8e0fcca9f91a8a460cd4a365b62170ac94d514928049c000200fb087f240068a8960000000000001e3c0f51000cd000c0000000000003a2e1d7b0019200100000000000006fc838a8003140010008,decode 5 1 0x76b8769b0e6553f595140144b0000300002000010008,(AH 7 0xae1c1b0e60182805f8000cd53f7030d80c2a0302000345451c1cd6073281ca8000d182e7078981e1a077e0003466ddc2dc60b6282d28000d144b).toArray⟩
theorem h49:check 1 49 d49=true:=by decide+kernel
def d50:Row:=⟨BCurve 56 45 0x86c667b387c3570c06954fada18115a560b7f4d716ba0233ec28f91049b56c3d83940ea9211a8a460cd4a38976ea26ca0e14f995804b400020104d88414006aa8680000000000001f700fec000d1000c0000000000003c8a1eab0019a001000000000000074683afc003240010008,decode 5 1 0x76b8669ae865524594f9014340000300002000010008,(AH 7 0x2b8606ba1c061a018200033549180c3a03060003353e5c1d06073a81cd8000d18057079581e4a078a000346625c2df60b6e82d58000d1434).toArray⟩
theorem h50:check 1 50 d50=true:=by decide+kernel
def d51:Row:=⟨BCurve 56 45 0x8905ae373d21570a06954fada1811777dcb76656b6b04233ec28f91049f6bd8f501f40a8411a8a460cd4a3ab029e50cdde54dd98804cc0002010ed8891c006ca83600000000000020aa108a000d5000c0000000000003ef21fe1001a2001000000000000079203d5c003340010008,decode 5 1 0x76b8569ac165508594dd0141b0000300002000010008,(AH 7 0x2b8506b058061a018200033542180c4a030a000335375c1d36074a81d08000d17dc707a581e7a079a000346569c2e260b7a82d88000d141b).toArray⟩
theorem h51:check 1 51 d51=true:=by decide+kernel
def d52:Row:=⟨BCurve 56 45 0x8b44f4baf27f570806954fada1811950ee068577d6a64233ec28f9104a380ee11caa72a7691a8a460cd4a3cda8dcc0de8314c19b804e400020119088e3c006ea80600000000000021ea112b000d9000c0000000000004166211d001aa00100000000000007df03fc8003440010008,decode 5 1 0x76b8469a99654ed594c1014030000300002000010008,(AH 7 0x2b8406a65c062a01860003353b580c5a030e000335305c1d66075681d38000d17b2707b181eba07a60003464a5c2e560b8a82dc8000d1403).toArray⟩
theorem h52:check 1 52 d52=true:=by decide+kernel
def d53:Row:=⟨BCurve 56 45 0x8d843b3ea7dd570606954fada1811b1cd4b64955f69c0233ec28f9104a796032e935a4a6811a8a460cd4a3ef3490eae25354a59e804fc000201236893740070a7d4000000000000233011cf000dd000c00000000000043e6225f001b2001000000000000082d84240003540010008,decode 5 1 0x76b8369a70654d0594a5013ea0000300002000010008,(AH 7 0x2b83069c18062a018600033534180c6a0312000335295c1d96076281d68000d1787707c181eea07b60003463e1c2e960b9682df8000d13ea).toArray⟩
theorem h53:check 1 53 d53=true:=by decide+kernel
def d54:Row:=⟨BCurve 56 45 0x8fc381c25d3b570406954fada1811cef50b5bad596924233ec28f9104ab87d988cc7c6a5a11a8a460cd4a410c04514e6239488a1805140002012df898c40072a7a2000000000000247c1276000e1000c000000000000467223a7001ba001000000000000087d844c4003640010008,decode 5 1 0x76b8269a49654b459488013d10000300002000010008,(AH 7 0x2b8206925c063a018a0003352d180c7a0316000335221c1dd6076e81da8000d175b707d181f2a07c6000346315c2ec60ba682e38000d13d1).toArray⟩
theorem h54:check 1 54 d54=true:=by decide+kernel
def d55:Row:=⟨BCurve 56 45 0x9202c8461299570206954fada1811ebb37657eb3b688c233ec28f9104af79afe3059e8a4b91a8a460cd4a4324bf93ee9f3d46ba48052c00020138b89e2c0074a77000000000000025ce1320000e5000c000000000000490a24f5001c200100000000000008cf04754003740010008,decode 5 1 0x76b8169a23654975946b013b80000300002000010008,(AH 7 0xae041a236018e80628000cd4977032580c8a031a0003451adc1e06077e81dd8000d172e707e181f6a07d6000346249c2f060bb282e78000d13b8).toArray⟩
theorem h55:check 1 55 d55=true:=by decide+kernel
def d56:Row:=⟨BCurve 56 45 0x94420ec9c7f7570006954fada18120871e154291d67f0233ec28f9104b36b863d3ec0aa3d11a8a460cd4a452bd2322e0ef944ea78054400020143a8a3ac0076a73c000000000000272613cd000e9000c0000000000004bae2649001ca0010000000000000922049f0003840010008,decode 5 1 0x76b80699fc6547a5944e0139e0000300002000010008,(AH 7 0x2b80067f1c064a018e0003351e9c0ca6032680c88000d144e7079181e2a0786000345c05c1fca07ea000336175c2f460bc282eb8000d139e).toArray⟩
theorem h56:check 1 56 d56=true:=by decide+kernel
def d57:Row:=⟨BCurve 56 45 0x9681554d7d5556fe06954fada181224c6f7558ce76750233ec28f9104b73a1dd4e851ca2e11a8a460cd4a4732e4d06d7eb5430aa8055c0002014ec8a9440078a7080000000000002884147d000ed000c0000000000004e5e27a3001d2001000000000000097684c98003940010008,decode 5 1 0x76b7f699d46545c59430013840000300002000010008,(AH 7 0xadfc19d46019280638000cd45c7032d80caa03260003450c1c1e86079a81e58000d16d27080181ffa07fa00034609dc2f760bd282ee8000d1384).toArray⟩
theorem h57:check 1 57 d57=true:=by decide+kernel
def d58:Row:=⟨BCurve 56 45 0x98c09bd132b356fc06954fada1812411c0d56f0b166a8233ec28f9104bae576aa0251ea1f11a8a460cd4a4939f76eacee71411ad805740002015a18aef4007aa6d400000000000029e81530000f1000c000000000000511a2903001da00100000000000009cc84f4c003a40010008,decode 5 1 0x76b7e699aa6543e594110136a0000300002000010008,(AH 7 0x2b7e066a9c065a01920003350f9c0cc6032e80ca8000d1411707ad81eaa07a6000345a8dc205a080e000335fbdc2fb60bde82f28000d136a).toArray⟩
theorem h58:check 1 58 d58=true:=by decide+kernel
def d59:Row:=⟨BCurve 56 45 0x9affe254e81156fa06954fada18125d07ce5d7a636600233ec28f9104be90cf7f1c520a0f91a8a460cd4a4b2f61688b90e53f2b08058c0002016598b4bc007ca69e0000000000002b5215e6000f5000c00000000000053e22a69001e20010000000000000a240520c003b40010008,decode 5 1 0x76b7d699806541f593f20134f0000300002000010008,(AH 7 0xadf419806019680648000cd41f7033580cca032e000344fc9c1f0607ba81ed8000d1672708298208a081e000345ed9c2ff60bee82f78000d134f).toArray⟩
theorem h59:check 1 59 d59=true:=by decide+kernel
def d60:Row:=⟨BCurve 56 45 0x9d3f28d89d6f56f806954fada181278f38f6404156554233ec28f9104c23c285436522a0011a8a460cd4a4d24cb626a33593d3b3805a40002017148ba9c007ea6680000000000002cc2169f000f9000c00000000000056b62bd5001ea0010000000000000a7d054d8003c40010008,decode 5 1 0x76b7c6995565400593d3013340000300002000010008,(AH 7 0xadf019556019a80658000cd4007033980cda0332000344f4dc1f4607ca81f18000d164070839820da0832000345df1c30360bfe82fb8000d1334).toArray⟩
theorem h60:check 1 60 d60=true:=by decide+kernel
def d61:Row:=⟨BCurve 56 45 0x9f7e6f5c52cd56f606954fada18129475fb6fb3af64a0233ec28f9104c5c44266c0c149f011a8a460cd4a4f088cb7e808853b3b6805bc0002017d28c0940080a6300000000000002e38175b000fd000c00000000000059962d47001f20010000000000000ad7857b0003d40010008,decode 5 1 0x76b7b69928653e0593b3013180000300002000010008,(AH 7 0xadec19287019e80668000cd3e07034180cfa033a000344ecdc1f8a07da000335835c214a084a000335cfdc30760c0e82ff8000d1318).toArray⟩
theorem h61:check 1 61 d61=true:=by decide+kernel
def d62:Row:=⟨BCurve 56 45 0xa1bdb5e0082b56f406954fada1812aff8677b634963e8233ec28f9104c94c5c794b3069e011a8a460cd4a50fdf6b1c6aaf9393b9805d40002018938c6a40082a5fa0000000000002fb4181a00101000c0000000000005c822ebf001fa0010000000000000b3385a94003e40010008,decode 5 1 0x76b7a698fa653c059393012fd0000300002000010008,(AH 7 0x2b7a063e98067a019a000334f01c0d16034280cf8000d1393707f681fb8000cd5d8708658218a085e000345c01c30b60c1e83038000d12fd).toArray⟩
theorem h62:check 1 62 d62=true:=by decide+kernel
def d63:Row:=⟨BCurve 56 45 0xa3fcfc63bd8956f206954fada1812cb117e8c38cb632c233ec28f9104ccb137c9460e89cf91a8a460cd4a52d00f62e3b2dd372bc805ec0002019578cccc0084a5c0000000000000313618dc00105000c0000000000005f7a303d002020010000000000000b9105d84003f40010008,decode 5 1 0x76b79698cb6539f59372012e00000300002000010008,(AH 7 0x504bac12ca03ba00034aac018cb701a280678000cd39f7034980d1a0342000344dc9c202a0802000335689c21fa0876000335b01c31060c3283088000d12e0).toArray⟩
theorem h63:check 1 63 d63=true:=by decide+kernel
def d64:Row:=⟨BCurve 56 45 0xa63c42e772e756f006954fada1812e62a959d0e4d626c233ec28f9104cff2d456b15ba9bf11a8a460cd4a54b3d0b8618809350bf80604000201a1e8d30c0086a58800000000000032be19a100109000c000000000000627e31c10020a0010000000000000bf006080004040010008,decode 5 1 0x76b786989b6537e59350012c40000300002000010008,(AH 7 0x14129b04a280ea8000d298e0626dc069a01a2000334df9c0d46034e80d28000d13507081e82058000cd56a70896c224a08560003459f1c31460c42830c8000d12c4).toArray⟩
theorem h64:check 1 64 d64=true:=by decide+kernel
def d65:Row:=⟨BCurve 56 45 0xa87b896b284556ee06954fada181300da57b309b761ac233ec28f9104d33470e41ca8c9ae11a8a460cd4a5685e9697e8fed32ec28061c000201ae88d9640088a54e000000000000344c1a690010d000c000000000000658e334b002120010000000000000c5086388004140010008,decode 5 1 0x76b776986b6535c5932e012a70000300002000010008,(AH 7 0x14125b048e80e68000d285f061ad8069a01a2000334d71c0d56035280d38000d132e70832820a8000cd530708b2c22ba08360003458d9c31960c5683118000d12a7).toArray⟩
theorem h65:check 1 65 d65=true:=by decide+kernel
def d66:Row:=⟨BCurve 56 45 0xaabacfeedda356ec06954fada18131b8a19c9052160ec233ec28f9104d652ceaef864e99d11a8a460cd4a584659763aca8930bc580634000201bb58dfd4008aa51200000000000035e01b3400111000c00000000000068aa34db0021a0010000000000000cb28669c004240010008,decode 5 1 0x76b766983b6533a5930b012890000300002000010008,(AH 7 0x14120b047e80e38000d2721060edc06aa01a6000334ce9c0d6a0356000334c2dc212b084282058000d14f4708cec232a08160003457b5c31e60c6a83168000d1289).toArray⟩
theorem h66:check 1 66 d66=true:=by decide+kernel
def d67:Row:=⟨BCurve 56 45 0xacfa1672930156ea06954fada1813356731e94c5b6028233ec28f9104d9712c79d421098b11a8a460cd4a5a06c982f705252e8c88064c000201c858e65c008ca4d6000000000000377a1c0200115000c0000000000006bd23671002220010000000000000d16069bc004340010008,decode 5 1 0x76b756980a65316592e80126b0000300002000010008,(AH 7 0x50472c11ba037e000349758180a701ae806a8000cd3167036180d7a035a000344ba1c218b085a81fd8000d14b5708eac239a07f6000345685c32260c7a831b8000d126b).toArray⟩
theorem h67:check 1 67 d67=true:=by decide+kernel
def d68:Row:=⟨BCurve 56 45 0xaf395cf6485f56e806954fada18134f444a0993955f5c233ec28f9104dc6c4b82204c297911a8a460cd4a5bb590eb5272792c4cb80664000201d588ecfc008ea498000000000000391a1cd300119000c0000000000006f06380d0022a0010000000000000d7b06ce8004440010008,decode 5 1 0x76b74697d7652f2592c40124c0000300002000010008,(AH 7 0x50462c117a03720003491f017d7a01ae000324bc9c0d9a0362000334b11c21eb087681f68000d14747090ec242a07da000345545c32760c8e83208000d124c).toArray⟩
theorem h68:check 1 68 d68=true:=by decide+kernel
def d69:Row:=⟨BCurve 56 45 0xb178a379fdbd56e606954fada181369216229dacf5e88233ec28f9104df20ed054d55496711a8a460cd4a5d645853addfcd29ece8067c000201e2e8f3b40090a45a0000000000003ac01da70011d000c000000000000724639af002320010000000000000de187020004540010008,decode 5 1 0x76b73697a2652ce5929e0122d0000300002000010008,(AH 7 0x14114b044e80d98000d231505e8a806c8000c92ce7036e80da8000cd29e70896c224a07be0003450c2c24ba07be0003353f5c32d60ca683268000d122d).toArray⟩
theorem h69:check 1 69 d69=true:=by decide+kernel
def d70:Row:=⟨BCurve 56 45 0xb3b7e9fdb31b56e406954fada1813822bd0546dd95db0233ec28f9104e1d58e887a5e695411a8a460cd4a5f017717a87fd9278d180694000201f078fa840092a41a0000000000003c6c1e7e00121000c00000000000075923b570023a0010000000000000e4987364004640010008,decode 5 1 0x76b726976c652a8592780120d0000300002000010008,(AH 7 0x14110b043e80d68000d21a005db1806da01b2000334aa1c0dd6037280db8000d1278708b6c22ca07a2000344fa6c255a07a2000335291c33260cba832b8000d120d).toArray⟩
theorem h70:check 1 70 d70=true:=by decide+kernel
def d71:Row:=⟨BCurve 56 45 0xb5f73081687956e206954fada18139b363e7f00e35ccc233ec28f9104e466f14917d6894111a8a460cd4a609e95dba31fe5251d4806ac000201fe39016c0094a3da0000000000003e1e1f5800125000c00000000000078ea3d05002420010000000000000eb3076b4004740010008,decode 5 1 0x76b71697336528259251011ed0000300002000010008,(AH 7 0x1410cb042e80d38000d201c05ccdc06ea01b6000334a09c0df6037a80dd8000d1251708d6c234a0786000344e7ec25fa0786000335121c33760cce83318000d11ed).toArray⟩
theorem h71:check 1 71 d71=true:=by decide+kernel
def d72:Row:=⟨BCurve 56 45 0xb83677051dd756e006954fada1813b36e02b3dfbd5be4233ec28f9104e6d5154725bda92d11a8a460cd4a622a0bfb3cf2a9229d7806c40002020c29086c0096a3980000000000003fd6203500129000c0000000000007c4e3eb90024a0010000000000000f1e07a10004840010008,decode 5 1 0x76b70696f96525a59229011cc0000300002000010008,(AH 7 0x50426c107a0342000347a2c16f9701be806e8000cd25a7038280df8000cd229b08f681da8000cd3515097ac25ba076a000344f99c33d60ce683378000d11cc).toArray⟩
theorem h72:check 1 72 d72=true:=by decide+kernel
def d73:Row:=⟨BCurve 56 45 0xba75bd88d33556de06954fada1813cba5c6e8be975af4233ec28f9104e91ffa82a413c91911a8a460cd4a63a3d97675f825200da806dc0002021a490f840098a354000000000000419421150012d000c0000000000007fbe4073002520010000000000000f8a87d78004940010008,decode 5 1 0x76b6f696bd6523259200011aa0000300002000010008,(AH 7 0x50416c104a03360003473b016bd701c2806f8000cd2327038a80e18000cd200b091e81d48000cd30050956c252a0752000344e05c34360cfe833d8000d11aa).toArray⟩
theorem h73:check 1 73 d73=true:=by decide+kernel
def d74:Row:=⟨BCurve 56 45 0xbcb5040c889356dc06954fada1813e30ae127e9415a00233ec28f9104eb47a0fb92d8e90411a8a460cd4a650bfe4d4e30591d6dd806f4000202289916b4009aa30e000000000000435821f800131000c000000000000833a42330025a0010000000000000ff8880ec004a40010008,decode 5 1 0x76b6e6968065208591d6011870000300002000010008,(AH 7 0x14102b040280ca8000d1b3e05a01c071a01c2000334821c0e4a038e000334759424db092e81cd8000d12aa50936c24ba0736000344c59c34960d1683448000d1187).toArray⟩
theorem h74:check 1 74 d74=true:=by decide+kernel
def d75:Row:=⟨BCurve 56 45 0xbef44a903df156da06954fada1813fa06a66c39d35900233ec28f9104ed4c08b1f20d08ee91a8a460cd4a6674232426688d1abe08070c00020237191dfc009ca2c8000000000000452222de00135000c00000000000086c243f90026200100000000000010680846c004b40010008,decode 5 1 0x76b6d69640651dd591ab011640000300002000010008,(AH 7 0x503fac0fda032200034660c1640701ca80718000cd1dd7039ac0e5a038e0003446ad4246b090e81c78000d12505091ac243a071e000344a9dc35060d2e834a8000d1164).toArray⟩
theorem h75:check 1 75 d75=true:=by decide+kernel
def d76:Row:=⟨BCurve 56 45 0xc1339113f34f56d806954fada1814109916b5b04d57f4233ec28f9104ef09f2e3321f28d891a8a460cd4a67ca9f569dd37917ee38072400020245c9255c009ea28000000000000046f223c700139000c0000000000008a5645c50026a00100000000000010d9087f8004c40010008,decode 5 1 0x76b6c695fd651b15917e011400000300002000010008,(AH 7 0x140fbb03ea80c58000d17ba057f5c073b01ca80708000d11b1703a6c0e8a03820003445f9423eb08ee81c18000d11f3508fac23ba07060003448cdc35660d4a83518000d1140).toArray⟩
theorem h76:check 1 76 d76=true:=by decide+kernel
def d77:Row:=⟨BCurve 56 45 0xc372d797a8ad56d606954fada18142658dd09729756e0233ec28f9104f0815f8f530f48c191a8a460cd4a68fdca4053a3d514fe68073c00020254a92cd400a0a23400000000000048c824b30013d000c0000000000008df6479700272001000000000000114b88b90004d40010008,decode 5 1 0x76b6b695b8651835914f0111a0000300002000010008,(AH 7 0x140f8b03da80c38000d15e3056e1c074b01ce806f8000d1183703aec0eaa037a00034453d4237b08d281bc8000d1191508dec234a06f20003446edc35d60d6683588000d111a).toArray⟩
theorem h77:check 1 77 d77=true:=by decide+kernel
def d78:Row:=⟨BCurve 56 45 0xc5b21e1b5e0b56d406954fada18143baf4e625ac955bc233ec28f9104f1d58d78e46e68aa11a8a460cd4a6a30f52a09743111fe98075400020263b9346400a2a1e80000000000004aa425a200141000c00000000000091a2496f0027a00100000000000011bf88f34004e40010008,decode 5 1 0x76b6a6956f651545911f010f40000300002000010008,(AH 7 0x140f5b03ce80c08000d13fe055bec075a01b6000334551c0eeb03b680db8000d111f508c2c22da06da0003444ad4230b08b681b68000d113e70d9283608000cd0f4).toArray⟩
theorem h78:check 1 78 d78=true:=by decide+kernel
def d79:Row:=⟨BCurve 55 45 0x63f8b24f89b4ab69034aa7d6d0c144fc9c0cab4b35490233ec28f9109e5c67bbaad57112211a1471c633d4fe2b3523a91543b446851c718cf5e35759b89ee950c2ec8076c000204e5f27818014942f400000000000132189a50005140030000000000004aad25a6801410008000000000001235092e4004f40010009,decode 5 1 0x76b696952465122610ed5d0c2010bd0000300002000010009,(AH 7 0x140f1b03c280be8000d120a05492c076a01b200033448ac0f0a03620003343b54229b089a81b08000d10c2508a6c226a06c20003442f5c36cb0da283608000d10cd).toArray⟩
theorem h79:check 1 79 d79=true:=by decide+kernel
def d80:Row:=⟨BCurve 54 45 0x328c2ac8b231d5b401a553eb68614637ade3834855354233ec28f9113ce1cc7e868d6a1de0f51e0201a1e04cb06df472fd0b8ef8078400020a09a50f30029a8048000000000004e6e278900149000c000000000002647934c400a280040000000000012ac096a0005040010008,decode 5 1 0x76b68694d5650ef710b8010090000300002000010008,(AH 7 0x303bd40eeb03b680bb8000d500905355c078b01de806a8000d10ef703cec0f2a03560003442e14222b087e81ab8000d10545088ac21fa06ae0003440ddc374b0dc283568000d10a4).toArray⟩
theorem h80:check 1 80 d80=true:=by decide+kernel
def d81:Row:=⟨BCurve 54 45 0x331bfc699f8955b381a553eb68614765951b000275208233ec28f9113d01f9d5138bb21740f51e0201a1da51b3f8618d15082f28079c00020a48252e9002a26fd000000000000505c28810014d000c00000000000273b93c6c00a4800400000000000132489a68005140010008,decode 5 1 0x76b6769482650ba7108200dfa0000300002000010008,(AH 7 0x140ecb03ae80b98000d0dfa0520ac079a01a60003342eac0f6a034e000334209421bb086681a68000d0fe35086ec219a069a000343eb5c37db0de6834b8000d107a).toArray⟩
theorem h81:check 1 81 d81=true:=by decide+kernel
def d82:Row:=⟨BCurve 54 45 0x33abce0a8ce0d5b301a553eb6861488651b32179950b0233ec28f9113d1087ca58c17a1060f51e0201a1d42118f25e4bf504af5807b400020a87654e5002aa5ee8000000000005250297c00151000c0000000000028329442c00a6800400000000000139e89e3c005240010008,decode 5 1 0x76b666942c650837104a00bdd0000300002000010008,(AH 7 0x140e9b03a280b78000d0bdd050b2c07ba01a200033420ec0f9a03420003341294215b084a81a18000d0f6d50856c212a0686000343c75c385b0e0a83418000d104f).toArray⟩
theorem h82:check 1 82 d82=true:=by decide+kernel
def d83:Row:=⟨BCurve 54 45 0x343b9fab7a3855b281a553eb686149934e5c3a0c34f4c233ec28f9113d04a6adb24a820920f51e0201a1cdbadf5beaaf9d00ff8807cc00020ac7656e7002b24d9000000000000544a2a7a00155000c00000000000292c94c0400a8800400000000000141a0a21c005340010008,decode 5 1 0x76b65693d3650497100f009b20000300002000010008,(AH 7 0x5039ac0e5a02d60003426c813d3b01f280678000cd049703f6c0fca033a00034403d420eb0832819c8000d0ef45083ac20ca0672000343a29c38fb0e3283378000d1022).toArray⟩
theorem h83:check 1 83 d83=true:=by decide+kernel
def d84:Row:=⟨BCurve 54 45 0x34cb714c678fd5b201a553eb68614a932065f75bd4dd8233ec28f9113cde567f2026ca01a0f51e0201a1c722dbad0ebe90fd1fb807e400020b08258ef002ba3bd000000000000564a2b7b00159000c000000000002a29953f400aa80040000000000014970a608005440010008,decode 5 1 0x76b64693766500d70fd10077a0000300002000010008,(AH 7 0x140e3b038a80b28000d077a04ddac07ea0196000334036c100a032e000333f454208b081a81978000d0e7650822c206a065e0003437c9c399b0e5a832d8000d0ff3).toArray⟩
theorem h84:check 1 84 d84=true:=by decide+kernel
def d85:Row:=⟨BCurve 54 45 0x355b42ed54e755b181a553eb68614b85c7d0596874c54233ec28f9113ca666ef463a91f9e0f51e0201a1c05164f5ba6bc8f91fe807fc00020b49a5afd002c229980000000000058502c7f0015d000c000000000002b2995bfc00ac80040000000000015158aa00005540010008,decode 5 1 0x76b636931564fcf70f91005330000300002000010008,(AH 7 0x50386c0e0a02c20003414cc1315b020280648000ccfcf50406c100a0326000343e454202b080281928000d0df55080ac200a064a000343555c3a3b0e8683248000d0fc3).toArray⟩
theorem h85:check 1 85 d85=true:=by decide+kernel
def d86:Row:=⟨BCurve 54 46 0x1af58a47211f6ad8806954fada185317867f013bc52b10467d851f22278b9affc490bb3e340f51e0201a1b94a4fadf5bdc8f4f80c040a000105c5f2e88801650b780000000000016970b6180058400300000000000058592c838015d00080000000000015958ae04005640010008,decode 5 1 0x76b62692b164f8d70f4f002de0000300002000010008,(AH 7 0x140deb037680ae8000d02de04ac5407fb01fa80638000d0f8d503fac0fda031a000343d3d41fcb07ea818d8000d0d6f507f2c1faa06360003432cdc3afb0eb6831a8000d0f90).toArray⟩
theorem h86:check 1 86 d86=true:=by decide+kernel
def d87:Row:=⟨BCurve 54 46 0x1b3d731797cb2ad8406954fada18534bf5b600b50d2490467d851f22277e01494e68043d280f51e0201a1b4e54cebb58a88f098240416000105e772f958016904e400000000000171b8ba40005940030000000000005a652d8a8016100080000000000016170b214005740010008,decode 5 1 0x76b616924964f4a70f09001390000300002000010008,(AH 7 0x2c0dba02b20003301ec1249b01f680628000ccf4a503eec0faa0312000343c2541f6b07d281898000d0ce6507dac1f4a0626000343035c3bbb0eea83118000d0f5c).toArray⟩
theorem h87:check 1 87 d87=true:=by decide+kernel
def d88:Row:=⟨BCurve 54 46 0x1b855be80e76ead8006954fada185379cf9d528cd51de0467d851f22276f4d9cc3c2c53c0c0f51e0201a1b6c8df16a007d8ec283c042200010609530a58016d04e00000000000017a18be74005a40030000000000005c772e9480165000800000000000169a0b630005840010008,decode 5 1 0x76b60691de64f0370ec2001380000300002000010008,(AH 7 0x140d9b036280aa8000d000004779407cb01ee80618000d0f03503e2c0f7a030a000343b0941f1b07be81848000d0c58507c6c1efa0612000342d8dc3c8b0f1e83088000d0f25).toArray⟩
theorem h88:check 1 88 d88=true:=by decide+kernel
def d89:Row:=⟨BCurve 54 46 0x1bcd44b88522aad7c06954fada1853a60430b8fc3d16e0467d851f22275c3217e72b663aec0f51e0201a1b8ac71418a8528e77854042e0001062b931b88017104dc0000000000018290c2b4005b40030000000000005e8f2fa180169000800000000000171e8ba58005940010008,decode 5 1 0x76b5f6916e64ebb70e77001370000300002000010008,(AH 7 0x5035ec0d6a02a2000340000116eb01ea80608000ccebb503d6c0f4a03020003439dd41ebb07a681808000d0bc7507aec1e9a0602000342acd43d5b0f4e83008000d0eed).toArray⟩
theorem h89:check 1 89 d89=true:=by decide+kernel
def d90:Row:=⟨BCurve 54 46 0x1c152d88fbce6ad7806954fada1853cba37471ca250fc0467d851f222747fc9cf6177f39bc0f51e0201a1ba90036c750278e2b86c043a0001064e332ce8017504d80000000000018b20c700005c400300000000000060ad30b18016d00080000000000017a48be8c005a40010008,decode 5 1 0x76b5e690fc64e6f70e2b001360000300002000010008,(AH 7 0x50352c0d3a029a00034000010fcb01e6805f8000cce6f503cec0f2a02fa0003438ad41e6b0792817c8000d0b325079ac1e4a05f200034280143ccb0f2282f78000d0eb2).toArray⟩
theorem h90:check 1 90 d90=true:=by decide+kernel
def d91:Row:=⟨BCurve 54 46 0x1c5d1659727a2ad7406954fada1853edf81053c74d0850467d851f22272f5f49b3117838840f51e0201a1bc7395975f7fc8ddb884044600010671333e78017904d400000000000193c8cb58005d400300000000000062d131c480171000800000000000182c0c2cc005b40010008,decode 5 1 0x76b5d6908564e2170ddb001350000300002000010008,(AH 7 0x140d2b034680a58000d0000042154078b01de805e8000d0e21503c2c0efa02f200034376d41e0b077a81788000d0a9850782c1dea05e200034251d43c1b0ef682ef8000d0e75).toArray⟩
theorem h91:check 1 91 d91=true:=by decide+kernel
def d92:Row:=⟨BCurve 54 46 0x1ca4ff29e925ead7006954fada18540d02045ef3b500c0467d851f2227148e0a47126137440f51e0201a1be5727c249fd18d8989c045200010694935038017d04d00000000000019c88cfbc005e400300000000000064fb32da8017500080000000000018b50c718005c40010008,decode 5 1 0x76b5c6900c64dd170d89001340000300002000010008,(AH 7 0x50342c0cfa028e000340000100cb01da805d8000ccdd1503b6c0eca02ea00034362541dbb076681738000d09fb5076ec1d9a05ce00034222943b7b0ece82e78000d0e36).toArray⟩
theorem h92:check 1 92 d92=true:=by decide+kernel
def d93:Row:=⟨BCurve 54 46 0x1cece7fa5fd1aad6c06954fada1854271bfca7e6fcf8f0467d851f2226f788deb21a3a35f80f51e0201a1c03ab9ed347a68d358b4045e000106b8536228018104cc000000000001a560d42c005f4003000000000000672b33f380179000800000000000193f8cb70005d40010008,decode 5 1 0x76b5b68f8f64d7e70d35001330000300002000010008,(AH 7 0x2c0cda02860003300000f8fb01d6805c8000ccd7e503aec0eaa02e20003434d541d6b0752816f8000d09595075ac1d4a05be000341f2543adb0ea682df8000d0df4).toArray⟩
theorem h93:check 1 93 d93=true:=by decide+kernel
def d94:Row:=⟨BCurve 54 46 0x1d34d0cad67d6ad6806954fada18543c45f92ea124f0e0467d851f2226d61bdacb2ff334a00f51e0201a1c222209026fe3ccdd8cc046a000106dc737448018504cc000000000001ae50d8a8006040030000000000006961350f8017d00080000000000019cb8cfd4005e40010008,decode 5 1 0x76b5a68f0e64d2870cdd001330000300002000010008,(AH 7 0x140cbb032a809f8000d000003c394074b01ce805b8000d0d28503a2c0e7a02da00034337541d1b073e816c8000d08b450746c1cfa05b2000341c0d43a3b0e7e82d78000d0db0).toArray⟩
theorem h94:check 1 94 d94=true:=by decide+kernel
def d95:Row:=⟨BCurve 54 46 0x1d7cb99b4d292ad6406954fada18544e254dde8a8ce890467d851f2226b394e0cfc92433400f51e0201a1c405b2bb117b8cc848e4047600010700f38698018904c8000000000001b758dd30006140030000000000006b9d362e801810008000000000001a590d444005f40010008,decode 5 1 0x76b5968e8964cd070c84001320000300002000010008,(AH 7 0x140c9b0322809e8000d000003a254073b01ca805a8000d0cd05039ac0e5a02d200034321141ccb072e81688000d080b50732c1cba05a20003418e14399b0e5a82cf8000d0d6a).toArray⟩
theorem h95:check 1 95 d95=true:=by decide+kernel
def d96:Row:=⟨BCurve 54 46 0x1dc4a26bc3d4ead6006954fada18545cb9fab7a334e010467d851f22268dc00496ecbd31d80f51e0201a1c5e944e5fbf8dcc288fc048200010725d39918018d04c4000000000001c078e1c4006240030000000000006ddf3750801850008000000000001ae80d8c0006040010008,decode 5 1 0x76b5868e0164c7670c28001310000300002000010008,(AH 7 0x140c7b031a809c8000d0000038054072b01c680598000d0c7650392c0e3a02ca0003430a141c8b071a81648000d075d50722c1c6a05920003415a54390b0e3282c88000d0d22).toArray⟩
theorem h96:check 1 96 d96=true:=by decide+kernel
def d97:Row:=⟨BCurve 54 46 0x1e0c8b3c3a80aad5c06954fada185464b957e31a5cd750467d851f2226649d46209abe30600f51e0201a1c7ccd710e6762cbc9914048e0001074b13abc8019104c0000000000001c9b0e6640063400300000000000070273875801890008000000000001b788dd48006140010008,decode 5 1 0x76b5768d7564c1870bc9001300000300002000010008,(AH 7 0x50316c0c4a026a0003400000d75b01c280588000ccc1850386c0e0a02c2000342f2541c3b070681608000d06ac5070ec1c1a05820003412554387b0e0e82c18000d0cd8).toArray⟩
theorem h97:check 1 97 d97=true:=by decide+kernel
def d98:Row:=⟨BCurve 54 46 0x1e54740cb12c6ad5806954fada18546b1361232924ce60467d851f2226382ca56cd3272ee40f51e0201a1c9b0693bd0f37cb6792c049a00010770b3bea8019504bc000000000001d300eb10006440030000000000007275399d8018d0008000000000001c0a8e1dc006240010008,decode 5 1 0x76b5668ce664bb970b670012f0000300002000010008,(AH 7 0x5030ec0c2a02660003400000ce6b01be80578000ccbb95037ec0dea02ba000342d9d41beb06f6815d8000d05f7506fac1bda0576000340ef5437db0dea82b98000d0c8c).toArray⟩
theorem h98:check 1 98 d98=true:=by decide+kernel
def d99:Row:=⟨BCurve 54 46 0x1e9c5cdd27d82ad5406954fada18546ad81ab5966cc530467d851f22260988189012802d580f51e0201a1cb97cfdec37750b0394404a600010796b3d1b8019904bc000000000001dc68efc80065400300000000000074c93ac8801910008000000000001c9e0e67c006340010008,decode 5 1 0x76b5568c5364b5670b030012f0000300002000010008,(AH 7 0x50306c0c0a025e0003400000c53b01ba80568000ccb5650376c0dca02b2000342c0d41bab06e281598000d053e506eac1b8a0566000340b814374b0dc682b28000d0c3d).toArray⟩
theorem h99:check 1 99 d99=true:=by decide+kernel
def d100:Row:=⟨BCurve 54 46 0x1ee445ad9e83ead5006954fada185467522c7132f4bbc0467d851f2225d8af9f8a58c92bc40f51e0201a1cd7b6209adf4a0a9d95c04b2000107bd13e4f8019d04b8000000000001e5e8f48c0066400300000000000077233bf6801950008000000000001d330eb28006440010008,decode 5 1 0x76b5468bbc64af170a9d0012e0000300002000010008,(AH 7 0x502fec0bea025a0003400000bbcb01b680558000ccaf15036ec0daa02ae000342a7541b6b06d281568000d0480506dac1b4a055a0003407f9436cb0da282ab8000d0bec).toArray⟩
theorem h100:check 1 100 d100=true:=by decide+kernel
def d101:Row:=⟨BCurve 54 46 0x1f2c2e7e152faad4c06954fada185460819655febcb220467d851f2225a4894447297a2a280f51e0201a1cf5ef4349871f0a3497404be000107e3d3f86801a104b4000000000001ef80f95c0067400300000000000079833d27801990008000000000001dc98efe0006540010008,decode 5 1 0x76b5368b2264a8a70a340012d0000300002000010008,(AH 7 0xb02f680948000cc00002c8ac06ca0152000332a2ac0d8a02a60003328d141b1b06c281528000d03bf506c6c1b0a054a0003404614363b0d8282a58000d0b99).toArray⟩
theorem h101:check 1 101 d101=true:=by decide+kernel
def d102:Row:=⟨BCurve 54 46 0x1f74174e8bdb6ad4806954fada185454c104789164a840467d851f22256d1506c6849328800f51e0201a1d142865f82ef409c898c04ca0001080af40c0801a504b0000000000001f930fe38006840030000000000007be93e5b8019d0008000000000001e618f4a4006640010008,decode 5 1 0x76b5268a8464a20709c80012c0000300002000010008,(AH 7 0xb02ee80938000cc00002a12c06ba014e000332882c0d6a029e00033272141adb06b2814f8000d02fa506b6c1aca053e0003400b5435bb0d62829e8000d0b44).toArray⟩
theorem h102:check 1 102 d102=true:=by decide+kernel
def d103:Row:=⟨BCurve 54 46 0x1fbc001f02872ad4406954fada185445b5cac4534c9e30467d851f2225336cdd1ce69c26d00f51e0201a1d329ed0275731495a9a404d600010832741fd801a904b000000000000202f90320006940030000000000007e553f92801a10008000000000001efb0f974006740010008,decode 5 1 0x76b51689e3649b47095a0012c0000300002000010008,(AH 7 0x140bab02e680918000d00000278d406ab01a680538000d09b450352c0d3a029a00034256941a9b069e814c8000d0231506a6c1a7a05320003400014352b0d3e82988000d0aec).toArray⟩
theorem h103:check 1 103 d103=true:=by decide+kernel
def d104:Row:=⟨BCurve 54 46 0x800fa3bde4cbab500467d851f2224f676d135d30d24f80f51e0201a1d50d7f2d5ff0648e99bc04e20001085a5433d801ad04ac0000000000020cd90814006a400300000000000080c740cc801a50008000000000001f960fe50006840010007,decode 5 1 0x76b506493e708e90012b0000300002000010007,(AH 7 0x140b8b02de80908000d0000024f94069b01a280528000d09455034ac0d1a02920003423a541a5b068e81498000d016350696c1a3a0526000340001434ab0d1e82918000d0a92).toArray⟩
theorem h104:check 1 104 d104=true:=by decide+kernel
def d105:Row:=⟨BCurve 54 46 0x812f46ffbf7aab4f0467d851f2224b74cd925c66e22580f51e0201a1d6f111584a6db48769d404ee0001088294480801b104a800000000000216d10d14006b4003000000000000833f4209801a9000800000000000203290338006940010007,decode 5 1 0x76b4f64896708760012a0000300002000010007,(AH 7 0x140b6b02d6808f8000d0000022594068b019e80518000d08d350342c0cfa028e0003421d941a1b067e81468000d009250686c19fa051a0003400014342b0cfe828b8000d0a36).toArray⟩
theorem h105:check 1 105 d105=true:=by decide+kernel
def d106:Row:=⟨BCurve 54 46 0x2093ba90668a6ad380f51e0201a1d8d4a38334eb047ea9ec04fa000108ab345c6801b504a400000000000220e11220006c400300000000000085bd4349801ad00080000000000020d09082c006a40010006,decode 5 1 0x76b4e707ea001290000300002000010006,(AH 7 0xb02d2808d8000cc00001faac067a014200033217ec0cea0286000332001419db067281438000d000050676c19ca050e000340001433bb0ce282858000d09d8).toArray⟩
theorem h106:check 1 106 d106=true:=by decide+kernel
def d107:Row:=⟨BCurve 54 46 0x20dba360dd362ad340f51e0201a1dab835ae1f685473aa040506000108d43470f801b904a00000000000022b091738006d40030000000000008841448c801b1000800000000000217010d2c006b40010006,decode 5 1 0x76b4d7073a001280000300002000010006,(AH 7 0x140b3b02ca808c8000d000001ceac066a0142000331fa2c0cca0282000331e1d4199b0662813f8000d000050666c198a04fe0003400014333b0cc2827f8000d0978).toArray⟩
theorem h107:check 1 107 d107=true:=by decide+kernel
def d108:Row:=⟨BCurve 54 46 0x21238c3153e1ead300f51e0201a1dc9f9c5111ec28686a1c0512000108fd9485b801bd04a000000000000235491c5c006e40030000000000008acb45d2801b5000800000000000221111238006c40010006,decode 5 1 0x76b4c70686001280000300002000010006,(AH 7 0x140b1b02c2808b8000d000001a1ac065a013e000331dbec0caa027a000331c314195b0652813d8000d000050656c194a04f6000340001432bb0ca682798000d0915).toArray⟩
theorem h108:check 1 108 d108=true:=by decide+kernel
def d109:Row:=⟨BCurve 54 46 0x216b7501ca8daad2c0f51e0201a1de832e7bfc69785cfa34051e00010927549aa801c1049c0000000000023fa1218c006f40030000000000008d5b471b801b900080000000000022b391750006d40010006,decode 5 1 0x76b4b705cf001270000300002000010006,(AH 7 0x2c0afa022600033000005cfb0192804e8000cc6f350326c0c8a0276000341a394192b0642813a8000d00005064ac190a04ea0003400014324b0c8682738000d08b1).toArray⟩
theorem h109:check 1 109 d109=true:=by decide+kernel
def d110:Row:=⟨BCurve 54 46 0x21b35dd241396ad280f51e0201a1e066c0a6e6e6c8514a4c052a0001095174afc801c504980000000000024a1126c8007040030000000000008ff14867801bd000800000000000235791c74006e40010006,decode 5 1 0x76b4a70514001260000300002000010006,(AH 7 0x502bac0ada02220003400000514b018e804d8000cc6755031ec0c6a026e000341839418eb063681378000d00005063ac18da04de000340001431db0c6a826e8000d084a).toArray⟩
theorem h110:check 1 110 d110=true:=by decide+kernel
def d111:Row:=⟨BCurve 54 46 0x21fb46a2b7e52ad240f51e0201a1e24e2749d96a9c455a6405360001097bf4c51801c9049800000000000254992c1000714003000000000000928d49b6801c100080000000000023fd121a4006f40010006,decode 5 1 0x76b4970455001260000300002000010006,(AH 7 0x2c0aca021e0003300000455b018a804d8000cc5f450316c0c4a026a00034162d418bb062681348000d00005062ec189a04d20003400014316b0c4e82688000d07e1).toArray⟩
theorem h111:check 1 111 d111=true:=by decide+kernel
def d112:Row:=⟨BCurve 54 46 0x22432f732e90ead200f51e0201a1e431b974c3e7ec394a7c0542000109a6d4da9801cd04940000000000025f39316400724003000000000000952f4b08801c500080000000000024a4126e0007040010006,decode 5 1 0x76b4870394001250000300002000010006,(AH 7 0x140abb02aa80868000d000000e52c061a01320003315c2c0c3a02620003314194187b061a81318000d00005061ec186a04c6000340001430fb0c3282628000d0775).toArray⟩
theorem h112:check 1 112 d112=true:=by decide+kernel
def d113:Row:=⟨BCurve 54 46 0x228b1843a53caad1c0f51e0201a1e6154b9fae653c2cfa94054e000109d214f04801d1049000000000000269f136c40073400300000000000097d74c5d801c9000800000000000254c92c28007140010006,decode 5 1 0x76b47702cf001240000300002000010006,(AH 7 0xb02a680858000cc00000b3d4061b0182804b8000d04ea5030ac0c1a025e0003411f94184b060a812f8000d000050612c182a04be0003400014308b0c16825d8000d0708).toArray⟩
theorem h113:check 1 113 d113=true:=by decide+kernel
def d114:Row:=⟨BCurve 54 46 0x22d301141be86ad180f51e0201a1e7f8ddca98e28c207aac055a000109fdb5062801d5048c00000000000274c13c30007440030000000000009a854db5801cd00080000000000025f69317c007240010006,decode 5 1 0x76b4670207001230000300002000010006,(AH 7 0x140a8b029e80838000d00000081d4060b017e804b8000d046250302c0bfa025a000340fd14180b05fe812c8000d000050602c17fa04b20003400014301b0bfa82588000d0698).toArray⟩
theorem h114:check 1 114 d114=true:=by decide+kernel
def d115:Row:=⟨BCurve 54 46 0x231ae9e492942ad140f51e0201a1e9e0446d8b666013cac4056600010a29b51c3801d9048c0000000000027fa941a8007540030000000000009d394f10801d100080000000000026a2136dc007340010006,decode 5 1 0x76b457013c001230000300002000010006,(AH 7 0xb029a80828000cc000004f2c05fa012a000330f5ac0bea0252000330d9d417db05f281298000d0000505f6c17ca04a600034000142fab0be282538000d0626).toArray⟩
theorem h115:check 1 115 d115=true:=by decide+kernel
def d116:Row:=⟨BCurve 52 46 0x8d8b4ad424ffab440046628377d48b0fd5a91889c0feadc05720001295854c9e0077406d0000000000028aa9472c007640030000000000027fcd41ba0075400200000000000274f13c48007440010006,decode 5 1 0x76b446c0fe0006d0000300002000010006,(AH 7 0x50296c0a4a0206000340000006db017a80498000cc349502f6c0bca024e000340b5d417ab05e281278000d0000505eac178a049e00034000142f4b0bc6824d8000d05b2).toArray⟩
theorem h116:check 1 116 d116=true:=by decide+kernel
def row (v:ℕ):Row:=match v with
 | 0=>d0
 | 1=>d1
 | 2=>d2
 | 3=>d3
 | 4=>d4
 | 5=>d5
 | 6=>d6
 | 7=>d7
 | 8=>d8
 | 9=>d9
 | 10=>d10
 | 11=>d11
 | 12=>d12
 | 13=>d13
 | 14=>d14
 | 15=>d15
 | 16=>d16
 | 17=>d17
 | 18=>d18
 | 19=>d19
 | 20=>d20
 | 21=>d21
 | 22=>d22
 | 23=>d23
 | 24=>d24
 | 25=>d25
 | 26=>d26
 | 27=>d27
 | 28=>d28
 | 29=>d29
 | 30=>d30
 | 31=>d31
 | 32=>d32
 | 33=>d33
 | 34=>d34
 | 35=>d35
 | 36=>d36
 | 37=>d37
 | 38=>d38
 | 39=>d39
 | 40=>d40
 | 41=>d41
 | 42=>d42
 | 43=>d43
 | 44=>d44
 | 45=>d45
 | 46=>d46
 | 47=>d47
 | 48=>d48
 | 49=>d49
 | 50=>d50
 | 51=>d51
 | 52=>d52
 | 53=>d53
 | 54=>d54
 | 55=>d55
 | 56=>d56
 | 57=>d57
 | 58=>d58
 | 59=>d59
 | 60=>d60
 | 61=>d61
 | 62=>d62
 | 63=>d63
 | 64=>d64
 | 65=>d65
 | 66=>d66
 | 67=>d67
 | 68=>d68
 | 69=>d69
 | 70=>d70
 | 71=>d71
 | 72=>d72
 | 73=>d73
 | 74=>d74
 | 75=>d75
 | 76=>d76
 | 77=>d77
 | 78=>d78
 | 79=>d79
 | 80=>d80
 | 81=>d81
 | 82=>d82
 | 83=>d83
 | 84=>d84
 | 85=>d85
 | 86=>d86
 | 87=>d87
 | 88=>d88
 | 89=>d89
 | 90=>d90
 | 91=>d91
 | 92=>d92
 | 93=>d93
 | 94=>d94
 | 95=>d95
 | 96=>d96
 | 97=>d97
 | 98=>d98
 | 99=>d99
 | 100=>d100
 | 101=>d101
 | 102=>d102
 | 103=>d103
 | 104=>d104
 | 105=>d105
 | 106=>d106
 | 107=>d107
 | 108=>d108
 | 109=>d109
 | 110=>d110
 | 111=>d111
 | 112=>d112
 | 113=>d113
 | 114=>d114
 | 115=>d115
 | 116=>d116
 | _=>default
theorem checked (v:ℕ) (hv:1+v≤117):check 1 v (row v)=true:=by
 have hvl:v≤116:=by omega
 interval_cases v
 · exact h0
 · exact h1
 · exact h2
 · exact h3
 · exact h4
 · exact h5
 · exact h6
 · exact h7
 · exact h8
 · exact h9
 · exact h10
 · exact h11
 · exact h12
 · exact h13
 · exact h14
 · exact h15
 · exact h16
 · exact h17
 · exact h18
 · exact h19
 · exact h20
 · exact h21
 · exact h22
 · exact h23
 · exact h24
 · exact h25
 · exact h26
 · exact h27
 · exact h28
 · exact h29
 · exact h30
 · exact h31
 · exact h32
 · exact h33
 · exact h34
 · exact h35
 · exact h36
 · exact h37
 · exact h38
 · exact h39
 · exact h40
 · exact h41
 · exact h42
 · exact h43
 · exact h44
 · exact h45
 · exact h46
 · exact h47
 · exact h48
 · exact h49
 · exact h50
 · exact h51
 · exact h52
 · exact h53
 · exact h54
 · exact h55
 · exact h56
 · exact h57
 · exact h58
 · exact h59
 · exact h60
 · exact h61
 · exact h62
 · exact h63
 · exact h64
 · exact h65
 · exact h66
 · exact h67
 · exact h68
 · exact h69
 · exact h70
 · exact h71
 · exact h72
 · exact h73
 · exact h74
 · exact h75
 · exact h76
 · exact h77
 · exact h78
 · exact h79
 · exact h80
 · exact h81
 · exact h82
 · exact h83
 · exact h84
 · exact h85
 · exact h86
 · exact h87
 · exact h88
 · exact h89
 · exact h90
 · exact h91
 · exact h92
 · exact h93
 · exact h94
 · exact h95
 · exact h96
 · exact h97
 · exact h98
 · exact h99
 · exact h100
 · exact h101
 · exact h102
 · exact h103
 · exact h104
 · exact h105
 · exact h106
 · exact h107
 · exact h108
 · exact h109
 · exact h110
 · exact h111
 · exact h112
 · exact h113
 · exact h114
 · exact h115
 · exact h116
end AXX
namespace AXN
open DZ CL
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
def d0:Row:=⟨BCurve 52 40 0x59aa87e86d9caedda553eb6862f0641787d438a047b0007000060021001600018647c00000000000058003c000480030000000000000b00080000c0008000000000000200018000280010006,decode 5 1 0x76bb76a0470191f0000300002000010006,(AH 7 0xaedc20476014a80508000cd91f7029980a5a028a0003463d9c17b605ea81758000d1da4706218187a060a000347f6dc276609ce82688000d17c4).toArray⟩
theorem h0:check 2 0 d0=true:=by decide+kernel
def d1:Row:=⟨BCurve 52 40 0x5e2914efd858aed9a553eb6862f89b06ba04ed202ed000800006003200200001e6430000000000000940060000600030000000000001800100001200080000000000002c0020000300010006,decode 5 1 0x76bb66a02e0190c0000300002000010006,(AH 7 0xaed8202e6014a80518000cd90c7029980a5a028e00034638dc17c605ee81768000d1d8b706258188a0612000347efdc278609d6826a8000d17b3).toArray⟩
theorem h1:check 2 1 d1=true:=by decide+kernel
def d2:Row:=⟨BCurve 53 41 0x18a9e87dd0c52bb534aa7d6d0c300d1f5ec35a1a0148cfb0a3e447a1f2f7b222eb18f9a8006000030016c00d8000918d000000000000011800a8000780030000000000000c40078000600020000000000000700048000480010007,decode 5 1 0x76bb56a014658f9018d00000300002000010007,(AH 7 0x2bb508051c0536014a80518000d18f97029d80a6a028e000346341c17d605f281788000d1d71706298189a0616000347e89c27a609de826c8000d17a2).toArray⟩
theorem h2:check 2 2 d2=true:=by decide+kernel
def d3:Row:=⟨BCurve 53 41 0x19c98bbfab742bb434aa7d6d0c309233a5d1cdc1ff98cfb0a3e447ac978b99cc8358e7e800800003002300140000a98bd0000000000001bc01000009000300000000000014800c0000780020000000000000d40080000600010007,decode 5 1 0x76bb469ff9658e7018bd0000300002000010007,(AH 7 0x2bb407fe5c0536014a80518000d18e77029d80a6a02920003462f5c17f605f681798000d1d5870631818ba061e000347e19c27b609e2826d8000d1791).toArray⟩
theorem h3:check 2 3 d3=true:=by decide+kernel
def d4:Row:=⟨BCurve 53 42 0x6ba4bc06188caecc6954fada18622b4531e9b213fbe8cfb0a3e447b73c1f81761b98d494005000018018a00dc00060c550000000000000a0005a0002a000c0000000000003d802300012000400000000000015800c8000780010007,decode 5 1 0x76bb369fdf658d4018aa0000300002000010007,(AH 7 0xaecc1fdf6014e80518000cd8d4702a180a7a02920003462a9c180605fe817a8000d1d3e70635818ca0622000347da5c27d609ea826f8000d1780).toArray⟩
theorem h4:check 2 4 d4=true:=by decide+kernel
def d5:Row:=⟨BCurve 53 42 0x7023490d8348aec86954fada18632ed87058f7e3f888cfb0a3e447c1e0b3691fb3d8c0b4006000018020c01200006cc4b8000000000000d9007800030000c0000000000005600300001500040000000000001fc0120000900010007,decode 5 1 0x76bb269fc4658c0018970000300002000010007,(AH 7 0xaec81fc46014e80528000cd8c0702a180a7a029600034625dc18160602817c8000d1d247063d818da0626000347d31c27f609f282718000d176f).toArray⟩
theorem h5:check 2 5 d5=true:=by decide+kernel
def d6:Row:=⟨BCurve 53 42 0x74a1d614ee04aec46954fada186435b6569f0e73f508cfb0a3e447cc854750c94c18add4007000018029e016c00078c4200000000000011a009a00036000c00000000000072803f0001800040000000000002c00188000a80010007,decode 5 1 0x76bb169fa8658ad018840000300002000010007,(AH 7 0xaec41fa86014e80528000cd8ad702a580a8a0296000346211c18260606817d8000d1d0a70641818fa062e000347cbdc281609fa82738000d175d).toArray⟩
theorem h6:check 2 6 d6=true:=by decide+kernel
def d7:Row:=⟨BCurve 53 42 0x7920631c58c0aec06954fada18653c943ce52503f1a8cfb0a3e447d729db3872e4589af4008000018034001c000084c3880000000000016300c00003c000c0000000000009300500001b00040000000000003a40200000c00010007,decode 5 1 0x76bb069f8d6589a018710000300002000010007,(AH 7 0x2bb007e35c0546014e80528000d189a702a580a8a029a0003461c5c1846060e817e8000d1cef706458190a0632000347c49c282609fe82758000d174c).toArray⟩
theorem h7:check 2 7 d7=true:=by decide+kernel
def d8:Row:=⟨BCurve 53 43 0x1f67bc08f0df2baf0d2a9f5b430cc804ef6a8d5a7dc48cfb0a3e447e187f19afd5a98868a00480000c01f9010e0004861740000000000006d003a80010800300000000000016f00c60003c00080000000000004a80288000d80010007,decode 5 1 0x76baf69f71658860185d0000300002000010007,(AH 7 0xaebc1f716015280528000cd886702a980a9a029a000346175c1856061281808000d1cd57064d8192a063a000347bd1c28460a0682768000d173a).toArray⟩
theorem h8:check 2 8 d8=true:=by decide+kernel
def d9:Row:=⟨BCurve 53 43 0x20875f4acb8e2bae0d2a9f5b430ce8e0ac33502c7d588cfb0a3e447ebe607fd87d0d8739a00500000c025a01400004e61240000000000008340460001200030000000000001c000f00004200080000000000005cc0320000f00010007,decode 5 1 0x76bae69f5665873018490000300002000010007,(AH 7 0xaeb81f566015280538000cd873702a980a9a029e000346125c1876061681818000d1cba706518193a063e000347b59c28660a0e82788000d1728).toArray⟩
theorem h9:check 2 9 d9=true:=by decide+kernel
def d10:Row:=⟨BCurve 55 43 0x21a7028ca63d2bad0d2a9f5b43034254c5004e399f3c233ec28f9107f68a9be53169185f8d4523066a5e77f8cad74d7c1836aa00580000c00b0c05d80015171700000000000009b80528001380030000000000000864047800120002000000000000071003c8001080010008,decode 5 1 0x76bad69f3c6585f59836017170000300002000010008,(AH 7 0xaeb41f3c6015280538000cd85f702ad80aaa029e0003460d9c1886061e81838000d1c9f706598195a0646000347ae1c28860a16827a8000d1717).toArray⟩
theorem h10:check 2 10 d10=true:=by decide+kernel
def d11:Row:=⟨BCurve 55 43 0x22c6a5ce80ec2bac0d2a9f5b43034a715ef3c8681f22233ec28f910800e8b247bbdf584b8d4523066a5ea13e46ebab1bd822ba00600000c00cd006c0001697050000000000000b5c06000015000300000000000009e805400013800200000000000008740480001200010008,decode 5 1 0x76bac69f226584b59822017050000300002000010008,(AH 7 0x2bac07c89c0556015280538000d184b702ad80aaa02a2000346089c1896062281848000d1c847065d8196a064a000347a69c28a60a1e827c8000d1705).toArray⟩
theorem h11:check 2 11 d11=true:=by decide+kernel
def d12:Row:=⟨BCurve 55 43 0x23e649105b9b2bab0d2a9f5b4303528df8e742969f09233ec28f91080b46c8aa465598378d4523066a5eca83c30008bb980eca00680000c00eb407b8001816f30000000000000d2006e8001680030000000000000b8c06180015000200000000000009f80548001380010008,decode 5 1 0x76bab69f09658375980e016f30000300002000010008,(AH 7 0xaeac1f096015680538000cd837702b180aba02a2000346039c18b6062681858000d1c69706658198a06520003479f1c28c60a22827e8000d16f3).toArray⟩
theorem h12:check 2 12 d12=true:=by decide+kernel
def d13:Row:=⟨BCurve 55 43 0x2505ec52364a2baa0d2a9f5b43035aaa92dabcc51ef0233ec28f910815a4df0cd0cbd8238d4523066a5ef3c93f14665b57fada00700000c010b808c0001996e10000000000000f0407e0001800030000000000000d500700001680020000000000000b9c0620001500010008,decode 5 1 0x76baa69ef065823597fa016e10000300002000010008,(AH 7 0xaea81ef06015680548000cd823702b180aba02a6000345fe9c18c6062e81878000d1c4d706698199a065a000347975c28d60a2a82808000d16e1).toArray⟩
theorem h13:check 2 13 d13=true:=by decide+kernel
def d14:Row:=⟨BCurve 55 43 0x26258f9410f92ba90d2a9f5b430362c72cce36f39ed7233ec28f91082002f56f5b42180f8d4523066a5f1d0ebb28c3fb17e6ea00780000c012dc09d8001b16cf000000000000110808e8001980030000000000000f3407f8001800020000000000000d600708001680010008,decode 5 1 0x76ba969ed76580f597e6016cf0000300002000010008,(AH 7 0xaea41ed76015680548000cd80f702b580aca02a6000345f99c18e6063281888000d1c3170671819ba065e0003478f9c28f60a3282828000d16cf).toArray⟩
theorem h14:check 2 14 d14=true:=by decide+kernel
def d15:Row:=⟨BCurve 55 43 0x274532d5eba82ba80d2a9f5b43036ae3c6c1b1221ebd233ec28f91082a1a8e4cc69657fb8d4523066a5f4539acf714c657d1fa00800000c015200b00001c96bc000000000000132c0a00001b000300000000000011380900001980020000000000000f440800001800010008,decode 5 1 0x76ba869ebd657fb597d1016bc0000300002000010008,(AH 7 0x2ba807af5c0566015680548000d17fb702b580aca02aa000345f45c18f6063a818a8000d1c1570679819ca066600034787dc29160a3a82848000d16bc).toArray⟩
theorem h15:check 2 15 d15=true:=by decide+kernel
def d16:Row:=⟨BCurve 55 44 0x14326b0be32b95d3834aa7d6d0c0dcb982dd9d32a7a8c467d851f221068f1495ea2192fcc8d4523066a5f6e7f290b726617bd8500440000600bc2061c000f0b55000000000000055c02ca00072000c00000000000026b814300036000400000000000011480908001980010008,decode 5 1 0x76ba769ea3657e6597bd016aa0000300002000010008,(AH 7 0xae9c1ea36015a80548000cd7e6702b980ada02ae000345ef5c1916063e818c8000d1bf97067d819ea066a0003477fdc29360a4282868000d16aa).toArray⟩
theorem h16:check 2 16 d16=true:=by decide+kernel
def d17:Row:=⟨BCurve 55 44 0x14c23cacd08315d3034aa7d6d0c0dec0a95a7bbe47a20467d851f22107d207b1978c1afa48d4523066a5f96aa1ad9c33157a88d00480000600d0406c0000fcb4b80000000000005f5031800078000c0000000000002b40168000390004000000000000136c0a20001b00010008,decode 5 1 0x76ba669e88657d2597a8016970000300002000010008,(AH 7 0x2ba607a218056a0156000335f4980aea02ae000335ea1c19260646818d8000d1bdd7068581a0a0672000347781c29560a4a82888000d1697).toArray⟩
theorem h17:check 2 17 d17=true:=by decide+kernel
def d18:Row:=⟨BCurve 55 44 0x15520e4dbdda95d2834aa7d6d0c0e0c13a87aca8679b8467d851f221091dca7de8dae2f7a8d4523066a5fbfef96ee20d1179495004c0000600e56076c00108b428000000000000696036a0007e000c000000000000300818f0003c000400000000000015b00b48001c80010008,decode 5 1 0x76ba569e6e657bd59794016850000300002000010008,(AH 7 0x2ba5079b9c0576015a80558000d17bd702bd80aea02b2000345e51c1946064a818f8000d1bc07068d81a1a067a000347701c29760a52828a8000d1685).toArray⟩
theorem h18:check 2 18 d18=true:=by decide+kernel
def d19:Row:=⟨BCurve 55 44 0x15e1dfeeab3215d2034aa7d6d0c0e2c1cbb4dd9287948467d851f2210a60bd9996456af508d4523066a5fe81a88bc719c577f9d00500000600fb8082000114b39000000000000073f03c000084000c00000000000035101b80003f000400000000000018140c80001e00010008,decode 5 1 0x76ba469e52657a85977f016720000300002000010008,(AH 7 0x2ba4079498057a0156000335ea180afa02b2000335dfdc1956065281908000d1ba37069181a3a068200034767dc29960a5a828c8000d1672).toArray⟩
theorem h19:check 2 19 d19=true:=by decide+kernel
def d20:Row:=⟨BCurve 56 44 0xb38d8c7cc44cae8c1a553eb686039309738839f29e37119f6147c8821747616a875fe5e4d1a8a460cd4a010457a8ac267976aa500540000600895046e00090597c0000000000001fc0106800228003000000000000074b03c60008400080000000000001a980dc8001f80010008,decode 5 1 0x76ba369e37657935976a0165f0000300002000010008,(AH 7 0xae8c1e376015e80568000cd793702c180afa02b6000345da9c1976065a81928000d1b867069981a5a06860003475fdc29b60a62828f8000d165f).toArray⟩
theorem h20:check 2 20 d20=true:=by decide+kernel
def d21:Row:=⟨BCurve 56 44 0xb80c19842f08ae881a553eb686039b0bb83cfd9b1e1b119f6147c88219bba8409a6c75df91a8a460cd4a038706c591332d754ad0058000060095604d000096593000000000000022a411e00024000300000000000007fc04200008a00080000000000001d3c0f20002100010008,decode 5 1 0x76ba269e1b6577e597540164c0000300002000010008,(AH 7 0xae881e1b6015e80568000cd77e702c580b0a02ba000345d51c1996065e81948000d1b69706a181a7a068e000347579c29e60a6a82918000d164c).toArray⟩
theorem h21:check 2 21 d21=true:=by decide+kernel
def d22:Row:=⟨BCurve 56 44 0xbc8aa68b99c4ae841a553eb68603a30dfcf1c1439dfe119f6147c8821c418e77f54185da51a8a460cd4a0609b5e2763fe173fb5005c0000600a1f05360009c58e400000000000025a813680025800300000000000008b5047e00090000800000000000020001088002280010008,decode 5 1 0x76ba169dfe657695973f016390000300002000010008,(AH 7 0x2ba1077f9c0586015e80568000d1769702c580b0a02ba000345cfdc19a6066681958000d1b4b706a981a8a06960003474f5c2a060a7282938000d1639).toArray⟩
theorem h22:check 2 22 d22=true:=by decide+kernel
def d23:Row:=⟨BCurve 56 44 0xc10933930480ae801a553eb68603aaf5ec67ce661de2119f6147c8821ec774af501695d4d1a8a460cd4a087abc5afa7f4d72abd00600000600af005a0000a2589400000000000028cc150000270003000000000000097604e000096000800000000000022e41200002400010008,decode 5 1 0x76ba069de2657535972a016250000300002000010008,(AH 7 0xae801de26016280578000cd753702c980b1a02be000345ca9c19c6066e81978000d1b2d706b181aaa069e00034746dc2a260a7e82958000d1625).toArray⟩
theorem h23:check 2 23 d23=true:=by decide+kernel
def d24:Row:=⟨BCurve 56 44 0xc587c09a6f3cae7c1a553eb68603b2f8311c920e9dc4119f6147c882213bbb85632325cf91a8a460cd4a0afd6b77df8c01714c500640000600bc9060e000a858480000000000002c1016a8002880030000000000000a3f05460009c000800000000000025e81388002580010008,decode 5 1 0x76b9f69dc46573e59714016120000300002000010008,(AH 7 0x2b9f077118058a015e000335cf980b2a02c2000335c51c19e6067281998000d1b0f706b581aca06a60003473e9c2a460a8682988000d1612).toArray⟩
theorem h24:check 2 24 d24=true:=by decide+kernel
def d25:Row:=⟨BCurve 56 44 0xca064da1d9f8ae781a553eb68603bae020929f311da7119f6147c88223b0025b762fb5ca11a8a460cd4a0d6e71f063cb6d6fecd00680000600caa0680000ae57f80000000000002f741860002a00030000000000000b1005b0000a20008000000000000290c1520002700010008,decode 5 1 0x76b9e69da765728596fe015fe0000300002000010008,(AH 7 0x2b9e0769dc0596016280578000d1728702cd80b2a02c2000345bf9c19f6067a819b8000d1af1706bd81aea06ae000347361c2a660a8e829a8000d15fe).toArray⟩
theorem h25:check 2 25 d25=true:=by decide+kernel
def d26:Row:=⟨BCurve 56 44 0xce84daa944b4ae741a553eb68603c2c81008ac539d89119f6147c88226244931893c45c491a8a460cd4a0ff1210d48d8216e8d5006c0000600d9306f6000b457ac00000000000032f81a28002b80030000000000000be9061e000a800080000000000002c5016c8002880010008,decode 5 1 0x76b9d69d8965712596e8015eb0000300002000010008,(AH 7 0xae741d896016680588000cd712702d180b3a02c6000345ba1c1a160682819d8000d1ad2706c581b0a06b60003472d5c2a860a96829c8000d15eb).toArray⟩
theorem h26:check 2 26 d26=true:=by decide+kernel
def d27:Row:=⟨BCurve 56 44 0xd30367b0af70ae701a553eb68603caafff7eb9761d6a119f6147c882289890079c48d5bf11a8a460cd4a12622785cd178d6d2dd00700000600e840770000ba575c000000000000369c1c00002d00030000000000000cca0690000ae00080000000000002fb41880002a00010008,decode 5 1 0x76b9c69d6a656fc596d2015d70000300002000010008,(AH 7 0x2b9c075a98059a0162000335bf180b4a02ca000335b49c1a36068a819e8000d1ab3706cd81b2a06be000347249c2ab60a9e829f8000d15d7).toArray⟩
theorem h27:check 2 27 d27=true:=by decide+kernel
def d28:Row:=⟨BCurve 56 44 0xd781f4b81a2cae6c1a553eb68603d27d99b610129d4b119f6147c8822afb377c678ce5b951a8a460cd4a14d32dfe5156f96bbe500740000600f7d07ee000c0570c0000000000003a601de8002e80030000000000000db30706000b4000800000000000033381a48002b80010008,decode 5 1 0x76b9b69d4b656e5596bb015c30000300002000010008,(AH 7 0x2b9b0752dc05a6016680588000d16e5702d580b4a02ca000345aedc1a56069281a08000d1a94706d581b4a06c60003471bdc2ad60aaa82a18000d15c3).toArray⟩
theorem h28:check 2 28 d28=true:=by decide+kernel
def d29:Row:=⟨BCurve 56 44 0xdc0081bf84e8ae681a553eb68603da65892c1d351d2c119f6147c8822d6f7e527a9975b3d1a8a460cd4a17443476d596656a5ed0078000060107e0870000c656bc0000000000003e441fe0003000030000000000000ea40780000ba000800000000000036dc1c20002d00010008,decode 5 1 0x76b9a69d2c656cf596a5015af0000300002000010008,(AH 7 0xae681d2c6016a80598000cd6cf702d980b5a02ce000345a95c1a76069a81a28000d1a74706dd81b6a06ce000347131c2af60ab282a38000d15af).toArray⟩
theorem h29:check 2 29 d29=true:=by decide+kernel
def d30:Row:=⟨BCurve 56 44 0xe07f0ec6efa4ae641a553eb68603e233236373d19d0c119f6147c8822fd225c745dd85ae11a8a460cd4a19a3924af9088968ef5007c000060118708f6000cc5668000000000000424821e8003180030000000000000f9d07fe000c000080000000000003aa01e08002e80010008,decode 5 1 0x76b9969d0c656b85968e0159a0000300002000010008,(AH 7 0x2b9907431805aa0166000335ae180b6a02d2000335a39c1a96069e81a48000d1a54706e581b8a06d60003470a1c2b260abe82a68000d159a).toArray⟩
theorem h30:check 2 30 d30=true:=by decide+kernel
def d31:Row:=⟨BCurve 56 44 0xe4fd9bce5a60ae601a553eb68603ea00bd9aca6e1ceb119f6147c8823234cd3c112195a851a8a460cd4a1c1498c37d47f5677fd008000006012980980000d25618000000000000466c240000330003000000000000109e0880000c600080000000000003e842000003000010008,decode 5 1 0x76b9869ceb656a159677015860000300002000010008,(AH 7 0x2b98073adc05b6016a80598000d16a1702dd80b6a02d20003459ddc1ab606a681a68000d1a34706f181baa06e200034700dc2b460ac682a88000d1586).toArray⟩
theorem h31:check 2 31 d31=true:=by decide+kernel
def d32:Row:=⟨BCurve 56 45 0x74be146ae28e572e06954fada180fc7395f48842a7328233ec28f9104692ee961b8cb4b4511a8a460cd4a1e73f697a0ba1966082804200003009d885070006c2ae200000000000012ac098a000d2000c000000000000234e120c00198001000000000000042882208003180010008,decode 5 1 0x76b9769cca6568a59660015710000300002000010008,(AH 7 0xae5c1cca6016e805a8000cd68a702e180b7a02d6000345981c1ad606ae81a88000d1a13706f981bda06ea000346f7dc2b760ace82ab8000d1571).toArray⟩
theorem h32:check 2 32 d32=true:=by decide+kernel
def d33:Row:=⟨BCurve 56 45 0x76fd5aee97ec572c06954fada180fe66fc825de9c72a8233ec28f91046df4384b4f536b3991a8a460cd4a20e4fd1024f9856498680440000300a6905500006f2aba00000000000013c50a18000d8000c00000000000025701320001a4001000000000000046ac2420003300010008,decode 5 1 0x76b9669caa65673596490155d0000300002000010008,(AH 7 0xae581caa6016e805a8000cd673702e580b8a02da000345925c1af606b681aa8000d19f27070181bfa06f2000346ee5c2b960ada82ae8000d155d).toArray⟩
theorem h33:check 2 33 d33=true:=by decide+kernel
def d34:Row:=⟨BCurve 56 45 0x793ca1724d4a572a06954fada181005a63103390e7228233ec28f910472964872564a8b2e11a8a460cd4a23445ae4486ba96318a80460000300afd859b000722a9000000000000014e60aaa000de000c00000000000027a2143c001b000100000000000004af02648003480010008,decode 5 1 0x76b9569c8a6565c59631015480000300002000010008,(AH 7 0x2b9507229c05c6016e805a8000d165c702e580b8a02de0003458c5c1b1606c281ad8000d19d07070981c1a06fe000346e51c2bc60ae282b08000d1548).toArray⟩
theorem h34:check 2 34 d34=true:=by decide+kernel
def d35:Row:=⟨BCurve 56 45 0x7b7be7f602a8572806954fada1810247344e5b96871b0233ec28f9104775b975becd2ab2211a8a460cd4a25a3b8b86bddcd61a8e80480000300b9605e8000752a66000000000000160f0b40000e4000c00000000000029e41560001bc00100000000000004f542880003600010008,decode 5 1 0x76b9469c6c656445961a015330000300002000010008,(AH 7 0xae501c6c60172805b8000cd644702e980b9a02de000345869c1b3606ca81af8000d19af7071581c4a0706000346db9c2be60aee82b38000d1533).toArray⟩
theorem h35:check 2 35 d35=true:=by decide+kernel
def d36:Row:=⟨BCurve 56 45 0x7dbb2e79b806572606954fada1810434058c839c27134233ec28f91047bfda782f3c9cb1611a8a460cd4a27f16de82e82a960292804a0000300c328637000782a3a00000000000017400bda000ea000c0000000000002c36168c001c8001000000000000053d82ac8003780010008,decode 5 1 0x76b9369c4d6562c596020151d0000300002000010008,(AH 7 0xae4c1c4d60172805b8000cd62c702ed80baa02e2000345809c1b5606d281b18000d198d7071d81c6a070e000346d1dc2c160afa82b68000d151d).toArray⟩
theorem h36:check 2 36 d36=true:=by decide+kernel
def d37:Row:=⟨BCurve 56 45 0x7ffa74fd6d64572406954fada1810620d6caaba1c70b8233ec28f9104809fb7a9fac0eb0a11a8a460cd4a2a50cbbc51f4cd5ea96804c0000300cd306880007b2a1000000000000018790c78000f0000c0000000000002e9817c0001d40010000000000000587c2d20003900010008,decode 5 1 0x76b9269c2e65614595ea015080000300002000010008,(AH 7 0xae481c2e70175805ca016e00034585180bba02e60003357a9c1b8606da81b38000d196a7072981c8a071a000346c81c2c460b0282b88000d1508).toArray⟩
theorem h37:check 2 37 d37=true:=by decide+kernel
def d38:Row:=⟨BCurve 56 45 0x8239bb8122c2572206954fada181080da808d3a767038233ec28f9104851e890e72270afe11a8a460cd4a2c9e80ec1499a95d19a804e0000300d7786db0007e29e400000000000019ba0d1a000f6000c000000000000310a18fc001e000100000000000005d402f88003a80010008,decode 5 1 0x76b9169c0e655fc595d1014f20000300002000010008,(AH 7 0xae441c0e60176805c8000cd5fc702f180bba02ea000345745c1ba606e281b68000d19477073181cba0726000346be5c2c660b0e82bb8000d14f2).toArray⟩
theorem h38:check 2 38 d38=true:=by decide+kernel
def d39:Row:=⟨BCurve 56 45 0x84790204d820572006954fada18109f3e3f74e0b86fb8233ec28f910489c09935791e2af191a8a460cd4a2eec361bd73e855b99e80500000300e2007300008129b80000000000001b030dc0000fc000c000000000000338c1a40001ec001000000000000062243200003c00010008,decode 5 1 0x76b9069bee655e3595b9014dc0000300002000010008,(AH 7 0x2b9006fb9c05e60176805c8000d15e3702f580bca02ee0003456e5c1bc606ee81b88000d19247073d81cea072e000346b45c2c960b1a82be8000d14dc).toArray⟩
theorem h39:check 2 39 d39=true:=by decide+kernel
def d40:Row:=⟨BCurve 56 45 0x86b848888d7e571e06954fada1810bda1fe5c86fa6f34233ec28f91048e3f6a99f0844ae511a8a460cd4a3139eb4b99e3615a0a280520000300ecc878700084298c0000000000001c540e6a00102000c000000000000361e1b8c001f8001000000000000067283488003d80010008,decode 5 1 0x76b8f69bcd655ca595a0014c60000300002000010008,(AH 7 0xae3c1bcd6017a805d8000cd5ca702f980bda02ee000345681c1bf606f681bb8000d19007074981d0a073a000346aa1c2cc60b2282c18000d14c6).toArray⟩
theorem h40:check 2 40 d40=true:=by decide+kernel
def d41:Row:=⟨BCurve 56 45 0x88f78f0c42dc571c06954fada1810dc05bd442d3c6eac233ec28f910492be3bfe67ea6ad891a8a460cd4a3387a07b5c883d587a680540000300f7d07e00008729600000000000001dad0f1800108000c00000000000038c01ce00020400100000000000006c4c3720003f00010008,decode 5 1 0x76b8e69bab655b159587014b00000300002000010008,(AH 7 0xae381bab6017a805d8000cd5b1702fd80bea02f200034561dc1c16070281bd8000d18db7075181d3a07460003469fdc2cf60b2e82c48000d14b0).toArray⟩
theorem h41:check 2 41 d41=true:=by decide+kernel
def d42:Row:=⟨BCurve 56 45 0x8b36d58ff83a571a06954fada1810fa697c2bd37e6e24233ec28f91049719cea04fbf8acc11a8a460cd4a35d555ab1f2d1956daa80560000301031883b0008a29340000000000001f0e0fca0010e000c0000000000003b721e3c002100010000000000000719039c8004080010008,decode 5 1 0x76b8d69b89655985956d0149a0000300002000010008,(AH 7 0xae341b897017e805e8000cd5987030180bfa02f60003455b5c1c46070a81c08000d18b67075d81d6a0752000346955c2d260b3a82c78000d149a).toArray⟩
theorem h42:check 2 42 d42=true:=by decide+kernel
def d43:Row:=⟨BCurve 56 45 0x8d761c13ad98571806954fada18111863e6189fa86d98233ec28f91049b98a004c725aabf11a8a460cd4a381162368104ad554ae805800003010ea08980008d29060000000000002077108000114000c0000000000003e341fa00021c001000000000000076f43c80004200010008,decode 5 1 0x76b8c69b666557e59554014830000300002000010008,(AH 7 0x2b8c06d99805fa017a0003355f980c0a02fa000335551c1c66071681c28000d18917076981d9a075e0003468a9c2d560b4682ca8000d1483).toArray⟩
theorem h43:check 2 43 d43=true:=by decide+kernel
def d44:Row:=⟨BCurve 56 45 0x8fb5629762f6571606954fada181136c7a50045ea6d0c233ec28f91049ff432a6aefacab291a8a460cd4a3a4d6ec1e2dc4153ab2805a00003011a688f70009028d800000000000021e8113a0011a000c0000000000004106210c0022800100000000000007c783f48004380010008,decode 5 1 0x76b8b69b43655655953a0146c0000300002000010008,(AH 7 0x2b8b06d0dc0606017e805e8000d15657030580c0a02fe0003454e9c1c96071e81c58000d186b7077581dca076a0003467fdc2d860b5282cd8000d146c).toArray⟩
theorem h44:check 2 44 d44=true:=by decide+kernel
def d45:Row:=⟨BCurve 56 45 0x91f4a91b1854571406954fada18115458b9f237fc6c7c233ec28f9104a44fc54896cfeaa511a8a460cd4a3c897b4d44b3d5520b6805c000030126709580009328aa000000000000236111f800120000c00000000000043e82280002340010000000000000821c4220004500010008,decode 5 1 0x76b8a69b1f6554a59520014550000300002000010008,(AH 7 0xae281b1f60182805f8000cd54a7030980c1a0302000345481c1cc6072a81c88000d18457078181dfa077600034674dc2db60b5e82d08000d1455).toArray⟩
theorem h45:check 2 45 d45=true:=by decide+kernel
def d46:Row:=⟨BCurve 56 45 0x9433ef9ecdb2571206954fada1811725323df04266be8233ec28f9104a8881927ef140a9811a8a460cd4a3eb3df3445be21505ba805e000030132b89bb00096287a00000000000024e212ba00126000c00000000000046da23fc00240001000000000000087e04508004680010008,decode 5 1 0x76b8969afa65530595050143d0000300002000010008,(AH 7 0x2b8906be9c06160182805f8000d15307030d80c2a0306000345415c1ce6073681cb8000d181d7078d81e2a078200034669dc2de60b6a82d48000d143d).toArray⟩
theorem h46:check 2 46 d46=true:=by decide+kernel
def d47:Row:=⟨BCurve 56 45 0x967336228310571006954fada18118fe438d0f6386b50233ec28f9104acc06d0747582a8a91a8a460cd4a40efebbfa795b54eabe806000003013f40a2000099284c000000000000266b13800012c000c00000000000049dc25800024c00100000000000008dc44800004800010008,decode 5 1 0x76b8869ad465515594ea014260000300002000010008,(AH 7 0xae201ad46018680608000cd5157031180c3a030a0003453a9c1d16074281ce8000d17f67079d81e5a078e0003465e5c2e160b7682d78000d1426).toArray⟩
theorem h47:check 2 47 d47=true:=by decide+kernel
def d48:Row:=⟨BCurve 56 45 0x98b27ca6386e570e06954fada1811ad754dc2e84a6ab8233ec28f9104b0f8c0e69f9c4a7d11a8a460cd4a431a4fa6a8a0014cfc2806200003014c08a870009c281c00000000000027fc144a00132000c0000000000004cee270c00258001000000000000093c84b08004980010008,decode 5 1 0x76b8769aae654fa594cf0140e0000300002000010008,(AH 7 0xae1c1aae6018680608000cd4fa7031580c4a030e00034533dc1d46074e81d18000d17cd707a981e9a079e00034652dc2e460b8682da8000d140e).toArray⟩
theorem h48:check 2 48 d48=true:=by decide+kernel
def d49:Row:=⟨BCurve 56 45 0x9af1c329edcc570c06954fada1811cb0662b4da5c6a1c233ec28f9104b53114c5f7e06a6f91a8a460cd4a4544b38da9aa4d4b4c6806400003015910af00009f27ec0000000000002995151800138000c000000000000501028a000264001000000000000099ec4e20004b00010008,decode 5 1 0x76b8669a87654df594b4013f60000300002000010008,(AH 7 0xae181a876018a80618000cd4df7031980c5a03120003452d1c1d76075a81d48000d17a4707b581eca07aa000346471c2e860b9282de8000d13f6).toArray⟩
theorem h49:check 2 49 d49=true:=by decide+kernel
def d50:Row:=⟨BCurve 56 45 0x9d3109ada32a570a06954fada1811e82e22abf256697c233ec28f9104b94629e2c0938a6191a8a460cd4a476f1774aab499498ca806600003016658b5b000a227bc0000000000002b3615ea0013e000c00000000000053422a3c002700010000000000000a0305148004c80010008,decode 5 1 0x76b8569a5f654c359498013de0000300002000010008,(AH 7 0xae141a5f6018a80618000cd4c37031d80c6a0316000345261c1db6076681d78000d177b707c581f0a07ba0003463b1c2eb60b9e82e18000d13de).toArray⟩
theorem h50:check 2 50 d50=true:=by decide+kernel
def d51:Row:=⟨BCurve 56 45 0x9f7050315888570806954fada18120555e2a30a5068e8233ec28f9104bd5b3eff8946aa5391a8a460cd4a4987d2b74af19d47cce8068000030173e0bc8000a5278a0000000000002cdf16c000144000c00000000000056842be00027c0010000000000000a6945480004e00010008,decode 5 1 0x76b8469a3a654a75947c013c50000300002000010008,(AH 7 0xae101a3a6018e80628000cd4a77032180c7a031a0003451f1c1de6077281db8000d1750707d581f3a07ca0003462edc2ee60bae82e58000d13c5).toArray⟩
theorem h51:check 2 51 d51=true:=by decide+kernel
def d52:Row:=⟨BCurve 56 45 0xa1af96b50de6570606954fada1812227da29a224a6854233ec28f9104c14d1559c268ca4591a8a460cd4a4ba08df9eb2ea145fd2806a000030181a8c37000a827580000000000002e90179a0014a000c00000000000059d62d8c002880010000000000000ad1857c8004f80010008,decode 5 1 0x76b8369a156548b5945f013ac0000300002000010008,(AH 7 0xae0c1a156018e80628000cd48b7032580c8a031e00034517dc1e16078281de8000d1725707e581f7a07da000346225c2f260bba82e88000d13ac).toArray⟩
theorem h52:check 2 52 d52=true:=by decide+kernel
def d53:Row:=⟨BCurve 56 45 0xa3eedd38c344570406954fada18123f3c0d96602c67b8233ec28f9104c53eebb3fb8aea3711a8a460cd4a4db9493c8b6ba5442d6806c00003018fb0ca8000ab27260000000000003049187800150000c0000000000005d382f40002940010000000000000b3bc5b20005100010008,decode 5 1 0x76b82699ee6546e59442013930000300002000010008,(AH 7 0xae0819ee6019280638000cd46e7032980c9a0322000345109c1e56078e81e28000d16f8707f581fba07ea000346159c2f560bca82ec8000d1393).toArray⟩
theorem h53:check 2 53 d53=true:=by decide+kernel
def d54:Row:=⟨BCurve 56 45 0xa62e23bc78a2570206954fada18125bfa78929e0e671c233ec28f9104c930c20e34ad0a2891a8a460cd4a4fc05bdacadb61425da806e00003019df8d1b000ae26f2000000000000320a195a00156000c00000000000060aa30fc002a00010000000000000ba805e88005280010008,decode 5 1 0x76b81699c76545159425013790000300002000010008,(AH 7 0x2b810671dc0656019280638000d14517032d80caa0326000345095c1e86079e81e68000d16cb7080581ffa07fa000346089c2f960bda82f08000d1379).toArray⟩
theorem h54:check 2 54 d54=true:=by decide+kernel
def d55:Row:=⟨BCurve 56 45 0xa86d6a402e00570006954fada1812784f8e9401d86678233ec28f9104ccff59a5de3e2a1991a8a460cd4a51c76e790a4b1d407de80700000301ac80d90000b126be00000000000033d31a400015c000c000000000000642c32c0002ac0010000000000000c1646200005400010008,decode 5 1 0x76b806999e65433594070135f0000300002000010008,(AH 7 0xae00199e6019680648000cd4337033180cba032a00034501dc1ec607ae81e98000d169d708158204a080e000345fb5c2fd60be682f48000d135f).toArray⟩
theorem h55:check 2 55 d55=true:=by decide+kernel
def d56:Row:=⟨BCurve 56 45 0xaaacb0c3e35e56fe06954fada181294a4a49565a265d4233ec28f9104d0cdf13d87cf4a0a91a8a460cd4a53ce811749bad93e9e280720000301bb48e07000b4268a00000000000035a41b2a00162000c00000000000067be348c002b80010000000000000c8686588005580010008,decode 5 1 0x76b7f6997565415593e9013450000300002000010008,(AH 7 0xadfc19757019a80658000cd4157033980cda0332000344fa5c1f0607be81ed8000d166e708298208a081e000345ed9c30160bf682f88000d1345).toArray⟩
theorem h56:check 2 56 d56=true:=by decide+kernel
def d57:Row:=⟨BCurve 56 45 0xacebf74798bc56fc06954fada1812b0f9ba96c96c652c233ec28f9104d4794a12a1cf69fb91a8a460cd4a55d593b5892a953cae680740000301ca50e80000b72656000000000000377d1c1800168000c0000000000006b603660002c40010000000000000cf8c6920005700010008,decode 5 1 0x76b7e6994b653f7593ca0132b0000300002000010008,(AH 7 0xadf8194b6019a80658000cd3f77033d80cea0336000344f29c1f4607ce81f28000d163e7083d820da0832000345df5c30560c0682fc8000d132b).toArray⟩
theorem h57:check 2 57 d57=true:=by decide+kernel
def d58:Row:=⟨BCurve 56 45 0xaf2b3dcb4e1a56fa06954fada1812cce57b9d531e647c233ec28f9104d824a2e7bbcf89ec11a8a460cd4a57cafdaf67cd093abea80760000301d998efb000ba2620000000000000395e1d0a0016e000c0000000000006f12383c002d00010000000000000d6d06cc8005880010008,decode 5 1 0x76b7d6991f653d8593ab013100000300002000010008,(AH 7 0xadf4191f7019e80668000cd3d87034180cfa033a000344eadc1f8607de81f68000d160d708518212a0846000345d0dc30960c1683008000d1310).toArray⟩
theorem h58:check 2 58 d58=true:=by decide+kernel
def d59:Row:=⟨BCurve 56 45 0xb16a844f037856f806954fada1812e8d13ca3dcd063cc233ec28f9104dbcffbbcd5cfa9dc91a8a460cd4a59c067a9466f7d38cee80780000301e920f78000bd25ea0000000000003b471e0000174000c00000000000072d43a20002dc0010000000000000de347080005a00010008,decode 5 1 0x76b7c698f3653b95938c012f50000300002000010008,(AH 7 0x2b7c063cd8067a019a000334ee5c0d16034280cf8000d138c707f581fba07ea000345769c219a085e000335c21c30d60c2683058000d12f5).toArray⟩
theorem h59:check 2 59 d59=true:=by decide+kernel
def d60:Row:=⟨BCurve 56 45 0xb3a9cad2b8d656f606954fada18130453a8af8c6a6314233ec28f9104df5815cf603ec9cc91a8a460cd4a5ba428fec444a936cf2807a0000301f8e8ff7000c025b20000000000003d381efa0017a000c00000000000076a63c0c002e80010000000000000e5b87448005b80010008,decode 5 1 0x76b7b698c5653995936c012d90000300002000010008,(AH 7 0x14138b04da80f98000d2b54063158068a019e000334e6580d2a0346000334db1c2016080281ff8000d15a670879821da0872000345b29c31160c3a83098000d12d9).toArray⟩
theorem h60:check 2 60 d60=true:=by decide+kernel
def d61:Row:=⟨BCurve 56 45 0xb5e911566e3456f406954fada18131f6cbfc061ec6258233ec28f9104e2bcf11f5b1ce9bc11a8a460cd4a5d87ea544219d534bf6807c000030208f1078000c3257a0000000000003f311ff800180000c0000000000007a883e00002f40010000000000000ed5c7820005d00010008,decode 5 1 0x76b7a69896653785934b012bd0000300002000010008,(AH 7 0x504cec131a03d600034a9141896701a680688000cd3787035180d3a034a000344d2dc2066081682048000d1570708918223a088a000345a29c31660c4a830e8000d12bd).toArray⟩
theorem h61:check 2 61 d61=true:=by decide+kernel
def d62:Row:=⟨BCurve 56 45 0xb82857da239256f206954fada18133a85d6d1376e619c233ec28f9104e621cc6f55fb09ab91a8a460cd4a5f5a03055f21b932afa807e000030219390fb000c62540000000000000413220fa00186000c0000000000007e7a3ffc003000010000000000000f5207c08005e80010008,decode 5 1 0x76b7969867653575932a012a00000300002000010008,(AH 7 0x1412eb04b280f18000d29290619e80698000c93577035580d4a034e000344ca9c20b6082a82098000d1539708aac229a089a000345921c31a60c5a83128000d12a0).toArray⟩
theorem h62:check 2 62 d62=true:=by decide+kernel
def d63:Row:=⟨BCurve 56 45 0xba679e5dd8f056f006954fada1813559eede20cf060e4233ec28f9104e96368fcc148299b11a8a460cd4a613dc45adcf6e5308fe8080000030229c1180000c92508000000000000433b22000018c000c000000000000827c42000030c0010000000000000fd048000006000010008,decode 5 1 0x76b78698396533659308012840000300002000010008,(AH 7 0x14129b04a280ee8000d27fe060e5806aa01a6000334cd9c0d76035a80d58000d130870846820f8000cd500708c6c230a087a00034580dc31f60c6e83178000d1284).toArray⟩
theorem h63:check 2 63 d63=true:=by decide+kernel
def d64:Row:=⟨BCurve 56 46 0x5e537270c7272b7701a553eb68604dbf956bf4b9098090467d851f2209d9038d8f3a08931311a8a460cd4a62fe34679931812e581404100001811d44903800661266000000000000115308c280064800300000000000010d1c881800630002000000000000105088408006180010008,decode 5 1 0x76b776980965313592e5012660000300002000010008,(AH 7 0x50496c123a03aa000349b181809701ae806a8000cd3137036280d78000cd2e57085e82158000cd4c5708e2c237a08560003456f1c32460c82831c8000d1266).toArray⟩
theorem h64:check 2 64 d64=true:=by decide+kernel
def d65:Row:=⟨BCurve 56 46 0x5f7315b2a1d62b7601a553eb68604e28af20613e517d80467d851f2209df404924f180d2f011a8a460cd4a64bea474556c1d2c2834042000018125c894800067924800000000000011d94906000660003000000000000115608c400064800200000000000010d2c8820006300010008,decode 5 1 0x76b76697d8652f0592c2012480000300002000010008,(AH 7 0x50482c11fa039a00034960017d8701b2806b8000cd2f07036980d9a0362000344b09c21db086e820d8000d1487708fec23ea08360003455c5c32860c9683218000d1248).toArray⟩
theorem h65:check 2 65 d65=true:=by decide+kernel
def d66:Row:=⟨BCurve 56 46 0x6092b8f47c852b7501a553eb68604e91c8d4cdc3997a60467d851f2209e536873589d712cd11a8a460cd4a667f148111a6b929e85404300001812e6c98d80069122a0000000000001261894a80067800300000000000011dc4907800660002000000000000115708c48006480010008,decode 5 1 0x76b75697a6652cd5929e0122a0000300002000010008,(AH 7 0x50472c11ba038e0003490b017a6a01b2000324b35c0dba036a000334a79c223b088a82058000d144870922c247a0816000345489c32d60caa83268000d122a).toArray⟩
theorem h66:check 2 66 d66=true:=by decide+kernel
def d67:Row:=⟨BCurve 56 46 0x61b25c3657342b7401a553eb68604ef797e16378217710467d851f2209eae647c1030b52a811a8a460cd4a682ddbe96d140d279874044000018137309d40006a920b00000000000012ebc9900006900030000000000001264894c00067800200000000000011dd49080006600010008,decode 5 1 0x76b7469771652a8592790120b0000300002000010008,(AH 7 0x14118b045e80df8000d22ca05dc5806da01b2000334aa1c0dd6037280db8000d1279708aac229a07f6000345016c250a07f6000335341c33360cbe832c8000d120b).toArray⟩
theorem h67:check 2 67 d67=true:=by decide+kernel
def d68:Row:=⟨BCurve 56 46 0x62d1ff7831e32b7301a553eb68604f5d66edf92ca973b0467d851f2209f096084c7c3f928311a8a460cd4a69cafaad67b41925489404500001814014a1b8006c11eb000000000000137809d68006a800300000000000012eec9918006900020000000000001265894c8006780010008,decode 5 1 0x76b736973b6528359254011eb0000300002000010008,(AH 7 0x14114b044e80dc8000d215a05cedc06ea01b6000334a0dc0df6037a80dd8000d1254708c6c230a07da000344f02c25aa07da0003351e5c33860cd283318000d11eb).toArray⟩
theorem h68:check 2 68 d68=true:=by decide+kernel
def d69:Row:=⟨BCurve 56 46 0x63f1a2ba0c922b7201a553eb68604fc190a6a378d17030467d851f2209f5b8cdcdb72fd25d11a8a460cd4a6b68197162542522d8b404600001814918a640006d91cb00000000000014064a1e0006c0003000000000000137b09d80006a800200000000000012efc9920006900010008,decode 5 1 0x76b72697036525d5922d011cb0000300002000010008,(AH 7 0x14110b043e80d98000d1fdc05c0dc06fa01ba000334975c0e0a037e0003348b6c239a07be000334ddec264a07be00033507dc33e60cea83378000d11cb).toArray⟩
theorem h69:check 2 69 d69=true:=by decide+kernel
def d70:Row:=⟨BCurve 56 46 0x651145fbe7412b7101a553eb68605024150b625c996ca0467d851f2209fadb934ef220123611a8a460cd4a6cf38f90fc26e92068d40470000181523caad8006f11aa00000000000014968a668006d800300000000000014094a1f8006c0002000000000000137c09d88006a80010008,decode 5 1 0x76b71696ca6523659206011aa0000300002000010008,(AH 7 0x50432c10ba035a00034794016ca701c2806f8000cd2367038a80e18000cd206b090a81e88000cd32a5099ac263a07a2000344efdc34360cfe833d8000d11aa).toArray⟩
theorem h70:check 2 70 d70=true:=by decide+kernel
def d71:Row:=⟨BCurve 56 46 0x6630e93dc1f02b7001a553eb68605084f41c35d8016900467d851f2209ff715dc5eecc520e11a8a460cd4a6e7f05b095f9ad1dd8f404800001815b80af80007091890000000000001528cab00006f000300000000000014998a680006d8002000000000000140a4a200006c00010008,decode 5 1 0x76b70696906520e591dd011890000300002000010008,(AH 7 0x50426c107a034e0003472d81690701c680708000cd20e7039280e38000cd1ddb092e81e18000cd2da5097ac25ba0786000344d6dc34960d1683438000d1189).toArray⟩
theorem h71:check 2 71 d71=true:=by decide+kernel
def d72:Row:=⟨BCurve 56 46 0x67508c7f9c9f2b6f01a553eb686050e42dd91deb096540467d851f220a03c0aab7cc5691e511a8a460cd4a6ff8d32bceff291b3914049000018164e4b4380072116700000000000015bd0afa800708003000000000000152bcab18006f0002000000000000149a8a688006d80010008,decode 5 1 0x76b6f69654651e5591b3011670000300002000010008,(AH 7 0x14105b041280d08000d1b0e05951c072a01c6000334795c0e6a03960003346cd4255b094a81da8000d128650956c252a076a000344bc9c34f60d2e834a8000d1167).toArray⟩
theorem h72:check 2 72 d72=true:=by decide+kernel
def d73:Row:=⟨BCurve 56 46 0x68702fc1774e2b6e01a553eb68605141c2421a95b16150467d851f220a07c97a248abed1bb11a8a460cd4a7160f802a7375d18893404a00001816e68b9000073914400000000000016534b4600072000300000000000015c00afc000708002000000000000152ccab20006f00010008,decode 5 1 0x76b6e69615651bb59188011440000300002000010008,(AH 7 0x14102b040280cd8000d195805855c073a01ca0003346edc0e8a039e000334621424db092e81d48000d122e50936c24ba0752000344a15c35660d4a83508000d1144).toArray⟩
theorem h73:check 2 73 d73=true:=by decide+kernel
def d74:Row:=⟨BCurve 56 46 0x698fd30351fd2b6d01a553eb6860519c0c03406f995d30467d851f220a0b8bcc0c2a05118f11a8a460cd4a72b774351ea24915c95404b0000181780cbdd80075112000000000000016eb8b9280073800300000000000016564b4780072000200000000000015c10afc8007080010008,decode 5 1 0x76b6d695d36518f5915c011200000300002000010008,(AH 7 0x140feb03f680ca8000d17940574dc074a01ce00033463ec0eaa039e0003345714246b090e81cd8000d11d25091ac243a073600034484dc35c60d6283578000d1120).toArray⟩
theorem h74:check 2 74 d74=true:=by decide+kernel
def d75:Row:=⟨BCurve 56 46 0x6aaf76452cac2b6c01a553eb686051f4b0707ae12158f0467d851f220a0ec122e98b07516211a8a460cd4a73fc47c3353fed12e97404c000018181d0c2c0007690fb0000000000001785cbe000075000300000000000016ee8b9400073800200000000000016574b480007200010008,decode 5 1 0x76b6c6958f651625912e010fb0000300002000010008,(AH 7 0x503eec0faa032200034570c158f701d6c074a01c6000344589c0edb03b280e38000d112e508fac23ba071e0003445c9423eb08ee81c78000d119d70d8e835f8000cd0fb).toArray⟩
theorem h75:check 2 75 d75=true:=by decide+kernel
def d76:Row:=⟨BCurve 56 46 0x6bcf1987075b2b6b01a553eb6860524a0a35de81e95470467d851f220a11affc41cce7913311a8a460cd4a752f72aceb10490ff99404d00001818bb4c7b8007810d500000000000018220c2e8007680030000000000001788cbe180075000200000000000016ef8b948007380010008,decode 5 1 0x76b6b6954765133590ff010d50000300002000010008,(AH 7 0x140f8b03da80c58000d13e30551ec076a01c20003344cec0efa03820003343fd4237b08d281c18000d110e508dec234a0706000344489c36b60d9e83668000d10d5).toArray⟩
theorem h76:check 2 76 d76=true:=by decide+kernel
def d77:Row:=⟨BCurve 55 46 0x6ceebcc8e20a2b6a01a553eb6860a53b7d4ead74a29fa08cfb0a3e44284f2d742ac587440c23428e38c67ad7454b492ee4c866846851c718cf659fe36ac6ef3d0a69b404e00001832b71998000f32144000000000000630131f8001e0000c000000000000c1286180003b40010000000000001789cbe20007500010009,decode 5 1 0x76b6a694fd65103610cd5d0a6010a20000300002000010009,(AH 7 0x140f5b03ce80c38000d11f5053f6c077a01be00033440dc0f2b03c680de8000d10cd508c2c22da06f20003442994230b08b681bc8000d10a270dca836e8000cd0ae).toArray⟩
theorem h77:check 2 77 d77=true:=by decide+kernel
def d78:Row:=⟨BCurve 54 46 0x1b839802af2e4ada406954fada1852ee2870f821f94b00467d851f222856810139dae843440f51e0201a1e6d714e911cfb109a9d404f00001867f73476001ec3fe80000000000019608cce800798003000000000000630d31fe001e000080000000000018260c308007680010008,decode 5 1 0x76b69694b0650d17109a00ffa0000300002000010008,(AH 7 0x140f1b03c280c08000d0ffa052c1c079b01e2806d8000d10d1703d6c0f4a036e0003442694229b089a81b68000d103a508a6c226a06da000344079c37ab0dda836b8000d1086).toArray⟩
theorem h78:check 2 78 d78=true:=by decide+kernel
def d79:Row:=⟨BCurve 54 46 0x1bcb80d325da0ada006954fada185339a23ed7508145f0467d851f22285ba0a21ff73942700f51e0201a1e0ef3ecba70a5d0659f40500000186a8835c0001f237c0000000000001a02cd200007b0003000000000000658e3340001e600080000000000018c44c800007800010008,decode 5 1 0x76b686945f6509c7106500df00000300002000010008,(AH 7 0xc0ef503bac0eda02fa0003537c0145fb01ea806c8000cd09c703e2c0f7a03620003441954222b087e81b08000d0fca5088ac21fa06c2000343e59c383b0dfe83608000d105d).toArray⟩
theorem h79:check 2 79 d79=true:=by decide+kernel
def d80:Row:=⟨BCurve 54 46 0x1c1369a39c85cad9c06954fada18538376b8cb16a940a0467d851f22285d7260c89df241980f51e0201a1dad1ca1dcbe9d102da140510000186d21370e001f82f60000000000001aa70d728007c800300000000000068173486001ec00080000000000019648cd08007980010008,decode 5 1 0x76b676940a650667102d00bd80000300002000010008,(AH 7 0x503b2c0eba02ee000342f60140a701f2c07ba01aa00034419ac0fba03560003340b5421bb086681ab8000d0f565086ec219a06ae000343c21c38cb0e2283568000d1032).toArray⟩
theorem h80:check 2 80 d80=true:=by decide+kernel
def d81:Row:=⟨BCurve 54 46 0x1c5b527413318ad9806954fada1853c85b36fca3b13b20467d851f22285d1033484b9b40b40f51e0201a1d4828b57887490ff3a340520000186fc23860001fe26cc000000000001b4d4dc60007e00030000000000006aa835d0001f20008000000000001a06cd220007b00010008,decode 5 1 0x76b66693b26502d70ff3009b30000300002000010008,(AH 7 0x140e9b03a280b98000d09b304ecac07da01a60003340b6c0fea034e000333fcd4215b084a81a68000d0ede50856c212a069a0003439d9c395b0e4a834b8000d1006).toArray⟩
theorem h81:check 2 81 d81=true:=by decide+kernel
def d82:Row:=⟨BCurve 54 46 0x1ca33b4489dd4ad9406954fada185409f50d575ff93570467d851f22285a7a199f00343fc80f51e0201a1cdfdae00d4a418fb7a54053000018726b39b6002041e00000000000001bf58e1a8007f80030000000000006d41371e001f80008000000000001aab0d748007c80010008,decode 5 1 0x76b656935764ff270fb7007800000300002000010008,(AH 7 0x140e6b039680b78000d078004d5ec07fa01a2000333fcac102a0342000333edd420eb083281a18000d0e625083ac20ca0686000343781c39fb0e7683418000d0fd8).toArray⟩
theorem h82:check 2 82 d82=true:=by decide+kernel
def d83:Row:=⟨BCurve 54 46 0x1ceb241500890ad9006954fada185448443bdb4b812f70467d851f222854961db83f353ed40f51e0201a1c73f5da1a871e4f78a74054000018751c3b100020a14f8000000000001c9fce700008100030000000000006fe23870001fe0008000000000001b514dc80007e00010008,decode 5 1 0x76b64692f764fb570f780053e0000300002000010008,(AH 7 0x5038ec0e2a02d60003414f812f7b020680678000ccfb550412c103a033a000343de14208b081a819c8000d0de250822c206a0672000343515c3a9b0e9e83378000d0fa9).toArray⟩
theorem h83:check 2 83 d83=true:=by decide+kernel
def d84:Row:=⟨BCurve 54 46 0x1d330ce57734cad8c06954fada185481a36e9cfde92940467d851f22284b643f94089e3dd40f51e0201a1c04f432a13eafcf36a9405500001877d53c6e002100bbc000000000001d4c0ec6800828003000000000000728b39c6002040008000000000001bf98e1c8007f80010008,decode 5 1 0x76b636929464f7570f36002ef0000300002000010008,(AH 7 0x50386c0e0a02ca000340bbc1294b020280658000ccf7550406c100a032e000343cd94202b080281978000d0d5f5080ac200a065e000343295c3b5b0ece832d8000d0f77).toArray⟩
theorem h84:check 2 84 d84=true:=by decide+kernel
def d85:Row:=⟨BCurve 54 46 0x1d7af5b5ede08ad8806954fada1854b612a59c773122e0467d851f22283ffe7546d8f73cc80f51e0201a1ba823c54e15344ef2ab40560000187a963dd00021603b0000000000001dfa4f1e000840003000000000000753c3b200020a0008000000000001ca3ce720008100010008,decode 5 1 0x76b626922e64f3270ef2000ec0000300002000010008,(AH 7 0x140deb037680b08000d0091048b9407fb01fa80648000d0f32503fac0fda0326000343bc941fcb07ea81928000d0cd7507f2c1faa064a000343005c3c1b0f0283248000d0f43).toArray⟩
theorem h85:check 2 85 d85=true:=by decide+kernel
def d86:Row:=⟨BCurve 54 46 0x1dc2de86648c4ad8406954fada1854e73734c51fb91c40467d851f2228314ac8bc33b83bb40f51e0201a1bc69a2f7d3d718eabad40570000187d5f3f360021c03b0000000000001eaa8f7680085800300000000000077f53c7e002100008000000000001d500ec88008280010008,decode 5 1 0x76b61691c464eed70eab000ec0000300002000010008,(AH 7 0x2c0dba02ba00033000011c4b01f680638000cceed503eec0faa031a000343aad41f6b07d2818d8000d0c4b507dac1f4a0636000342d65c3ceb0f36831a8000d0f0e).toArray⟩
theorem h86:check 2 86 d86=true:=by decide+kernel
def d87:Row:=⟨BCurve 54 46 0x1e0ac756db380ad8006954fada1855136bc82b8f211570467d851f22282063300895693a940f51e0201a1be4d3522be5468e62af4058000018803040a00022203ac000000000001f5ccfd00008700030000000000007ab63de0002160008000000000001dfe4f200008400010008,decode 5 1 0x76b606915764ea570e62000eb0000300002000010008,(AH 7 0x50366c0d8a02b20003400001157501f2c07ba018a000343a9540f8b03de80c48000d0e62507c6c1efa0626000342eed41f1b07be81898000d0aabb0f6e83118000cced6).toArray⟩
theorem h87:check 2 87 d87=true:=by decide+kernel
def d88:Row:=⟨BCurve 54 46 0x1e52b02751e3cad7c06954fada18553c55b3bb2dc90e50467d851f22280c2db5178182396c0f51e0201a1c030c74da8d1b8e16b140590000188309420e0022803a8000000000002011102a8008880030000000000007d7f3f460021c0008000000000001eae8f788008580010008,decode 5 1 0x76b5f690e564e5b70e16000ea0000300002000010008,(AH 7 0x5035ec0d6a02aa00034000010e5b01ea80618000cce5b503d6c0f4a030a00034385941ebb07a681848000d0b27507aec1e9a06120003427e543d7b0f4e83088000d0e9c).toArray⟩
theorem h88:check 2 88 d88=true:=by decide+kernel
def d89:Row:=⟨BCurve 54 46 0x1e9a98f7c88f8ad7806954fada1855604fa38893510700467d851f2227f5c44dfd748b38380f51e0201a1c2145978934f08dc8b3405a00001885ea43800022e03a40000000000020c750860008a0003000000000000805040b0002220008000000000001f60cfd20008700010008,decode 5 1 0x76b5e6907064e0e70dc8000e90000300002000010008,(AH 7 0x50352c0d3a02a20003400001070b01e680608000cce0e503cec0f2a030200034372141e6b079281808000d0a8f5079ac1e4a060200034250d43ccb0f2283008000d0e60).toArray⟩
theorem h89:check 2 89 d89=true:=by decide+kernel
def d90:Row:=⟨BCurve 54 46 0x1ee281c83f3b4ad7406954fada18557f599793bfb8ff80467d851f2227dc0d04a5f1fc36f80f51e0201a1c3f7eba37dcc58d77b5405b00001888d344f60023403a000000000000217f90e28008b80030000000000008329421e002280008000000000002015102c8008880010008,decode 5 1 0x76b5d68ff864dbe70d77000e80000300002000010008,(AH 7 0x140d2b034680a68000d000003fe14078b01de805f8000d0dbe503c2c0efa02fa0003435dd41e0b077a817c8000d09f450782c1dea05f200034222143c1b0ef682f78000d0e22).toArray⟩
theorem h90:check 2 90 d90=true:=by decide+kernel
def d91:Row:=⟨BCurve 54 46 0x1f2a6a98b5e70ad7006954fada18559b18e3c81b60f7c0467d851f2227c021cf25765d35b00f51e0201a1c5db7dce6849a8d24b7405c0000188bc446700023a039c000000000002239d1400008d0003000000000000860a43900022e00080000000000020cb50880008a00010008,decode 5 1 0x76b5c68f7c64d6c70d24000e70000300002000010008,(AH 7 0x50342c0cfa02960003400000f7cb01da805e8000ccd6c503b6c0eca02f200034349141dbb076681788000d09545076ec1d9a05e2000341f2143b7b0ece82ef8000d0de1).toArray⟩
theorem h91:check 2 91 d91=true:=by decide+kernel
def d92:Row:=⟨BCurve 54 46 0x1f7253692c92cad6c06954fada1855b38d8825a648efd0467d851f22279fcec153089e34600f51e0201a1c7bf0ff952c6f8ccdb9405d0000188ebd47ee0024003980000000000022f6119e8008e800300000000000088f3450600234000800000000000218390e48008b80010008,decode 5 1 0x76b5b68efd64d1870ccd000e60000300002000010008,(AH 7 0x2c0cda028e0003300000efdb01d6805d8000ccd18503aec0eaa02ea00034333541d6b075281738000d08b05075ac1d4a05ce000341c1143adb0ea682e78000d0d9e).toArray⟩
theorem h92:check 2 92 d92=true:=by decide+kernel
def d93:Row:=⟨BCurve 54 46 0x1fba3c39a33e8ad6806954fada1855c71230c0f810e7a0467d851f22277e61bd6c1e5733040f51e0201a1c9a2a2243d4448c75bb405e00001891be49700024603940000000000023b451fe0009000030000000000008be446800023a000800000000000223dd1420008d00010008,decode 5 1 0x76b5a68e7a64cc170c75000e50000300002000010008,(AH 7 0x140cbb032a80a18000d0000039e94074b01ce805c8000d0cc1503a2c0e7a02e20003431d541d1b073e816f8000d080950746c1cfa05be0003418ed43a3b0e7e82df8000d0d59).toArray⟩
theorem h93:check 2 93 d93=true:=by decide+kernel
def d94:Row:=⟨BCurve 54 46 0x2002250a19ea4ad6406954fada1855d5a6dd9a10b8df30467d851f222759a6d747be78319c0f51e0201a1cb86344f27c198c1abd405f00001894c74af60024c0390000000000002474925e8009180030000000000008edd47fe0024000080000000000022fa11a08008e80010008,decode 5 1 0x76b5968df364c6770c1a000e40000300002000010008,(AH 7 0x140c9b0322809f8000d0000037cd4073b01ca805b8000d0c675039ac0e5a02da00034306941ccb072e816c8000d075d50732c1cba05b20003415b94399b0e5a82d78000d0d12).toArray⟩
theorem h94:check 2 94 d94=true:=by decide+kernel
def d95:Row:=⟨BCurve 54 46 0x204a0dda90960ad6006954fada1855e0f0e29c58a0d690467d851f2227319e0ee5e901302c0f51e0201a1cd6d9af21a456cbbcbf406000001897d84c80002520390000000000002536d2c000093000300000000000091de49800024600080000000000023b852000009000010008,decode 5 1 0x76b5868d6964c0b70bbc000e40000300002000010008,(AH 7 0x140c7b031a809e8000d0000035a54072b01c6805a8000d0c0b50392c0e3a02d2000342ef141c8b071a81688000d06ad50722c1c6a05a20003412714390b0e3282cf8000d0cc9).toArray⟩
theorem h95:check 2 95 d95=true:=by decide+kernel
def d96:Row:=⟨BCurve 54 46 0x2091f6ab0741cad5c06954fada1855e74aebdc6768cdb0467d851f2227064764469df22eb00f51e0201a1cf512d1d04c2bcb5bc140610000189af14e0e00258038c0000000000025fb132280094800300000000000094e74b060024c000800000000000247892608009180010008,decode 5 1 0x76b5768cdb64bac70b5b000e30000300002000010008,(AH 7 0x50316c0c4a02720003400000cdbb01c280598000ccbac50386c0e0a02ca000342d6d41c3b070681648000d05fa5070ec1c1a0592000340f154387b0e0e82c88000d0c7d).toArray⟩
theorem h96:check 2 96 d96=true:=by decide+kernel
def d97:Row:=⟨BCurve 54 46 0x20d9df7b7ded8ad5806954fada1855ea5a4d45a570c4a0467d851f2226d8bccd7e59d32d2c0f51e0201a1d134bf47ef400caf8c340620000189e124fa00025e03880000000000026c1538600096000300000000000097f84c9000252000800000000000253ad2c20009300010008,decode 5 1 0x76b5668c4a64b4b70af8000e20000300002000010008,(AH 7 0x5030ec0c2a026a0003400000c4ab01be80588000ccb4b5037ec0dea02c2000342be141beb06f681608000d0542506fac1bda0582000340ba9437db0dea82c18000d0c2f).toArray⟩
theorem h97:check 2 97 d97=true:=by decide+kernel
def d98:Row:=⟨BCurve 54 46 0x2121c84bf4994ad5406954fada1855e879b2ecaa58bb40467d851f2226a8fe4a8d1ca42b9c0f51e0201a1d3185172d9bd5ca93c54063000018a13b513600264038400000000000278993ea8009780030000000000009b114e1e0025800080000000000025ff13248009480010008,decode 5 1 0x76b5568bb464ae770a93000e10000300002000010008,(AH 7 0x50306c0c0a02660003400000bb4b01ba80578000ccae750376c0dca02ba000342a4d41bab06e2815d8000d0486506eac1b8a05760003408294374b0dc682b98000d0bdf).toArray⟩
theorem h98:check 2 98 d98=true:=by decide+kernel
def d99:Row:=⟨BCurve 54 46 0x2169b11c6b450ad5006954fada1855e34e70bcde80b1b0467d851f222675f1e55e69dd2a040f51e0201a1d4fbe39dc43aaca2bc74064000018a46c52d00026a0380000000000002853d4500009900030000000000009e324fb00025e00080000000000026c553880009600010008,decode 5 1 0x76b5468b1b64a8170a2b000e00000300002000010008,(AH 7 0x502fec0bea025e0003400000b1bb01b680568000cca815036ec0daa02b20003428ad41b6b06d281598000d03c7506dac1b4a0566000340499436cb0da282b28000d0b8d).toArray⟩
theorem h99:check 2 99 d99=true:=by decide+kernel
def d100:Row:=⟨BCurve 54 46 0x21b199ece1f0cad4c06954fada1855d93332cad988a7f0467d851f22263f979df2417e28600f51e0201a1d6e34a40b6be809c0c94065000018a7a5546e00270038000000000000292014b68009a8003000000000000a15b514600264000800000000000278d93ec8009780010008,decode 5 1 0x76b5368a7f64a18709c0000e00000300002000010008,(AH 7 0xb02f680968000cc000029fec06ca0156000332862c0d8a02ae00033270141b1b06c281568000d0303506c6c1b0a055a0003400f54363b0d8282ab8000d0b39).toArray⟩
theorem h100:check 2 100 d100=true:=by decide+kernel
def d101:Row:=⟨BCurve 54 46 0x21f982bd589c8ad4806954fada1855ca27f9169b709df0467d851f222607096a5d200f26b00f51e0201a1d8c6dc6ba13bd0953cb4066000018aae6561000276037c0000000000029ee551e0009c0003000000000000a48c52e00026a0008000000000002857d4520009900010008,decode 5 1 0x76b52689df649ac70953000df0000300002000010008,(AH 7 0xb02ee80948000cc0000277ec06ba01520003326b2c0d6a02a600033254d41adb06b281528000d023b506b6c1aca054a000340001435bb0d6282a58000d0ae2).toArray⟩
theorem h101:check 2 101 d101=true:=by decide+kernel
def d102:Row:=⟨BCurve 54 46 0x8905ae373d212b510467d851f2225cb2d548a890824ec0f51e0201a1daaa6e968bb9208e3cd4067000018ae2f57b60027c0378000000000002abe95868009d8003000000000000a7c5547e00270000800000000000292414b88009a80010007,decode 5 1 0x76b516493b708e3000de0000300002000010007,(AH 7 0x140bab02e680938000d0000024ed406ab01a680538000d093e50352c0d3a029e00034238d41a9b069e814f8000d0170506a6c1a7a053e0003400014352b0d3e829e8000d0a89).toArray⟩
theorem h102:check 2 102 d102=true:=by decide+kernel
def d103:Row:=⟨BCurve 54 46 0x8a25517917d02b500467d851f22258d1d528ef8f122540f51e0201a1dc8e00c1763670871cf4068000018b1805960002820374000000000002b90d5f00009f0003000000000000ab0656200027600080000000000029f255200009c00010007,decode 5 1 0x76b506489570871000dd0000300002000010007,(AH 7 0x140b8b02de80918000d0000022554069b01a280538000d08ce5034ac0d1a029a0003421c541a5b068e814c8000d00a050696c1a3a0532000340001434ab0d1e82988000d0a2e).toArray⟩
theorem h103:check 2 103 d103=true:=by decide+kernel
def d104:Row:=⟨BCurve 54 46 0x22d13d2ebc9fcad3c0f51e0201a1de7192ec60b3c07ebd14069000018b4d95b0e002880370000000000002c65165a800a08003000000000000ae4f57c60027c0008000000000002ac295888009d80010006,decode 5 1 0x76b4f707eb000dc0000300002000010006,(AH 7 0x140b6b02d680908000d000001fad4068b019e80528000d085b50342c0cfa0292000341ff141a1b067e81498000d000050686c19fa05260003400014342b0cfe82918000d09d1).toArray⟩
theorem h104:check 2 104 d104=true:=by decide+kernel
def d105:Row:=⟨BCurve 54 46 0x231925ff334b8ad380f51e0201a1e058f98f53379473dd3406a000018b83a5cc00028e0370000000000002d3b56c6000a20003000000000000b1a05970002820008000000000002b94d5f20009f00010006,decode 5 1 0x76b4e7073d000dc0000300002000010006,(AH 7 0xb02d2808f8000cc00001cf6c067a0146000331f96c0cea028e000331e15419db067281468000d000050676c19ca051a000340001433bb0ce2828b8000d0972).toArray⟩
theorem h105:check 2 105 d105=true:=by decide+kernel
def d106:Row:=⟨BCurve 54 46 0x23610ecfa9f74ad340f51e0201a1e23c8bba3db4e468cd5406b000018bba35e7600294036c000000000002e139732800a38003000000000000b4f95b1e002880008000000000002c69165c800a080010006,decode 5 1 0x76b4d7068c000db0000300002000010006,(AH 7 0x140b3b02ca808d8000d000001a32c066a0142000331db6c0cca0286000331c2d4199b066281438000d000050666c198a050e0003400014333b0cc282858000d0910).toArray⟩
theorem h106:check 2 106 d106=true:=by decide+kernel
def d107:Row:=⟨BCurve 54 46 0x23a8f7a020a30ad300f51e0201a1e4201de52832345d6d7406c000018bf1460300029a0368000000000002eedd7a0000a50003000000000000b85a5cd00028e0008000000000002d3f56c8000a200010006,decode 5 1 0x76b4c705d6000da0000300002000010006,(AH 7 0x140b1b02c2808c8000d00000175ac065a0142000331bcac0caa0282000331a394195b0652813f8000d000050656c194a04fe000340001432bb0ca6827f8000d08ac).toArray⟩
theorem h107:check 2 107 d107=true:=by decide+kernel
def d108:Row:=⟨BCurve 54 46 0x23f0e070974ecad2c0f51e0201a1e603b01012af8451bd9406d000018c28d61ee002a00364000000000002fca180e800a68003000000000000bbc35e86002940008000000000002e179734800a380010006,decode 5 1 0x76b4b7051b000d90000300002000010006,(AH 7 0x2c0afa022e000330000051bb0192804f8000cc67550326c0c8a027a00034183d4192b0642813d8000d00005064ac190a04f60003400014324b0c8682798000d0846).toArray⟩
theorem h108:check 2 108 d108=true:=by decide+kernel
def d109:Row:=⟨BCurve 54 46 0x2438c9410dfa8ad280f51e0201a1e7e7423afd2cd445edb406e000018c60e63b0002a603600000000000030a8587e000a80003000000000000bf3460400029a0008000000000002ef1d7a2000a500010006,decode 5 1 0x76b4a7045e000d80000300002000010006,(AH 7 0x502bac0ada0226000340000045eb018e804e8000cc5f55031ec0c6a0276000341635418eb0636813a8000d00005063ac18da04ea000340001431db0c6a82738000d07de).toArray⟩
theorem h109:check 2 109 d109=true:=by decide+kernel
def d110:Row:=⟨BCurve 54 46 0x2480b21184a64ad240f51e0201a1e9cea8ddefb0a839ddd406f000018c9976576002ac036000000000000318898ee800a98003000000000000c2ad61fe002a00008000000000002fce1810800a680010006,decode 5 1 0x76b497039d000d80000300002000010006,(AH 7 0x2c0aca0222000330000039db018a804d8000cc57250316c0c4a026e000341425418bb062681378000d00005062ec189a04de0003400014316b0c4e826e8000d0773).toArray⟩
theorem h110:check 2 110 d110=true:=by decide+kernel
def d111:Row:=⟨BCurve 54 46 0x24c89ae1fb520ad200f51e0201a1ebb23b08da2df82d9df4070000018cd286740002b2035c00000000000326ad960000ab0003000000000000c62e63c0002a600080000000000030ac5880000a800010006,decode 5 1 0x76b48702d9000d70000300002000010006,(AH 7 0x140abb02aa80878000d000000b66c061a01360003313b6c0c3a026a0003312094187b061a81348000d00005061ec186a04d2000340001430fb0c3282688000d0707).toArray⟩
theorem h111:check 2 111 d111=true:=by decide+kernel
def d112:Row:=⟨BCurve 54 46 0x94420ec9c7f72b470046628377d424fdb8f781e3608900f51e0201a1ed95cd33c4ab48212e14071000018d0c1690e002b8035800000000000334f19d2800ac8003000000000000c9b76586002ac000800000000000318c98f0800a980010007,decode 5 1 0x76b476c22470212000d60000300002000010007,(AH 7 0xb02a680868000cc000008494061b0182804c8000d04665030ac0c1a0262000340fe54184b060a81318000d000050612c182a04c60003400014308b0c1682628000d0698).toArray⟩
theorem h112:check 2 112 d112=true:=by decide+kernel
def d113:Row:=⟨BCurve 54 46 0x9561b20ba2a62b460046628377d42468f2a832c63088c0f51e0201a1ef795f5eaf2898149e34072000018d4626ae0002be03540000000000034355a46000ae0003000000000000cd486750002b2000800000000000326ed962000ab00010007,decode 5 1 0x76b466c22370149000d50000300002000010007,(AH 7 0x140a8b029e80858000d0000005254060b017e804b8000d03dc50302c0bfa025e000340db54180b05fe812f8000d000050602c17fa04be0003400014301b0bfa825d8000d0627).toArray⟩
theorem h113:check 2 113 d113=true:=by decide+kernel
def d114:Row:=⟨BCurve 52 46 0x9681554d7d552b450046628377d48f3ab29a7931c223e5407300001b602db2d800b1007b00000000000351d9aba800af80030000000000034385a47800ae000200000000000335319d4800ac80010006,decode 5 1 0x76b456c2230007b0000300002000010006,(AH 7 0xb029a80838000cc000001eec05fa012e000330d3ec0bea025a000330b79417db05f2812c8000d0000505f6c17ca04b200034000142fab0be282588000d05b4).toArray⟩
theorem h114:check 2 114 d114=true:=by decide+kernel
def d115:Row:=⟨BCurve 50 37 0x97a0f88f58042b448cc506efac725f60b65af21118000000002391e17ba4f84000c0000000011c863f8cb8c780040000000008e3eb99e24e680010005,decode 5 1 0x76b446c2236c0036c0026c0010005,(AH 7 0x50296c0a4a020a0003400000000b017a804a8000cc2c0502f6c0bca0252000340935417ab05e281298000d0000505eac178a04a600034000142f4b0bc682538000d053e).toArray⟩
theorem h115:check 2 115 d115=true:=by decide+kernel
def row (v:ℕ):Row:=match v with
 | 0=>d0
 | 1=>d1
 | 2=>d2
 | 3=>d3
 | 4=>d4
 | 5=>d5
 | 6=>d6
 | 7=>d7
 | 8=>d8
 | 9=>d9
 | 10=>d10
 | 11=>d11
 | 12=>d12
 | 13=>d13
 | 14=>d14
 | 15=>d15
 | 16=>d16
 | 17=>d17
 | 18=>d18
 | 19=>d19
 | 20=>d20
 | 21=>d21
 | 22=>d22
 | 23=>d23
 | 24=>d24
 | 25=>d25
 | 26=>d26
 | 27=>d27
 | 28=>d28
 | 29=>d29
 | 30=>d30
 | 31=>d31
 | 32=>d32
 | 33=>d33
 | 34=>d34
 | 35=>d35
 | 36=>d36
 | 37=>d37
 | 38=>d38
 | 39=>d39
 | 40=>d40
 | 41=>d41
 | 42=>d42
 | 43=>d43
 | 44=>d44
 | 45=>d45
 | 46=>d46
 | 47=>d47
 | 48=>d48
 | 49=>d49
 | 50=>d50
 | 51=>d51
 | 52=>d52
 | 53=>d53
 | 54=>d54
 | 55=>d55
 | 56=>d56
 | 57=>d57
 | 58=>d58
 | 59=>d59
 | 60=>d60
 | 61=>d61
 | 62=>d62
 | 63=>d63
 | 64=>d64
 | 65=>d65
 | 66=>d66
 | 67=>d67
 | 68=>d68
 | 69=>d69
 | 70=>d70
 | 71=>d71
 | 72=>d72
 | 73=>d73
 | 74=>d74
 | 75=>d75
 | 76=>d76
 | 77=>d77
 | 78=>d78
 | 79=>d79
 | 80=>d80
 | 81=>d81
 | 82=>d82
 | 83=>d83
 | 84=>d84
 | 85=>d85
 | 86=>d86
 | 87=>d87
 | 88=>d88
 | 89=>d89
 | 90=>d90
 | 91=>d91
 | 92=>d92
 | 93=>d93
 | 94=>d94
 | 95=>d95
 | 96=>d96
 | 97=>d97
 | 98=>d98
 | 99=>d99
 | 100=>d100
 | 101=>d101
 | 102=>d102
 | 103=>d103
 | 104=>d104
 | 105=>d105
 | 106=>d106
 | 107=>d107
 | 108=>d108
 | 109=>d109
 | 110=>d110
 | 111=>d111
 | 112=>d112
 | 113=>d113
 | 114=>d114
 | 115=>d115
 | _=>default
theorem checked (v:ℕ) (hv:2+v≤117):check 2 v (row v)=true:=by
 have hvl:v≤115:=by omega
 interval_cases v
 · exact h0
 · exact h1
 · exact h2
 · exact h3
 · exact h4
 · exact h5
 · exact h6
 · exact h7
 · exact h8
 · exact h9
 · exact h10
 · exact h11
 · exact h12
 · exact h13
 · exact h14
 · exact h15
 · exact h16
 · exact h17
 · exact h18
 · exact h19
 · exact h20
 · exact h21
 · exact h22
 · exact h23
 · exact h24
 · exact h25
 · exact h26
 · exact h27
 · exact h28
 · exact h29
 · exact h30
 · exact h31
 · exact h32
 · exact h33
 · exact h34
 · exact h35
 · exact h36
 · exact h37
 · exact h38
 · exact h39
 · exact h40
 · exact h41
 · exact h42
 · exact h43
 · exact h44
 · exact h45
 · exact h46
 · exact h47
 · exact h48
 · exact h49
 · exact h50
 · exact h51
 · exact h52
 · exact h53
 · exact h54
 · exact h55
 · exact h56
 · exact h57
 · exact h58
 · exact h59
 · exact h60
 · exact h61
 · exact h62
 · exact h63
 · exact h64
 · exact h65
 · exact h66
 · exact h67
 · exact h68
 · exact h69
 · exact h70
 · exact h71
 · exact h72
 · exact h73
 · exact h74
 · exact h75
 · exact h76
 · exact h77
 · exact h78
 · exact h79
 · exact h80
 · exact h81
 · exact h82
 · exact h83
 · exact h84
 · exact h85
 · exact h86
 · exact h87
 · exact h88
 · exact h89
 · exact h90
 · exact h91
 · exact h92
 · exact h93
 · exact h94
 · exact h95
 · exact h96
 · exact h97
 · exact h98
 · exact h99
 · exact h100
 · exact h101
 · exact h102
 · exact h103
 · exact h104
 · exact h105
 · exact h106
 · exact h107
 · exact h108
 · exact h109
 · exact h110
 · exact h111
 · exact h112
 · exact h113
 · exact h114
 · exact h115
end AXN
namespace AWY
open DZ CL
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
def d0:Row:=⟨BCurve 53 41 0x219ff2f7291aabb634aa7d6d0c315161c438bb9dfd18cfb0a3e447cbd67e3553f7d8cad0007c00050015c00d8000b58a10000000000000f4009a0008c00300000000000008c005c0006400200000000000006c0048000540010007,decode 5 1 0x76bb669fd1658ca018a10000300002000010007,(AH 7 0xaed81fd16014e80518000cd8ca702a180a7a0292000346285c18160602817b8000d1d3070639818da0626000347d69c27e609ee82708000d1778).toArray⟩
theorem h0:check 3 0 d0=true:=by decide+kernel
def d1:Row:=⟨BCurve 53 41 0x22bf963903c9abb534aa7d6d0c31d6760b472f45fb68cfb0a3e447d67b121cfd9018b8f0008c0005001f4012e000dd88e00000000000017c00e8000b400300000000000010400a20008c00200000000000008c005c000640010007,decode 5 1 0x76bb569fb6658b80188e0000300002000010007,(AH 7 0x2bb507ed98053a014a0003362e180a8a0296000336239c18260606817c8000d1d177063d818ea062a000347cf5c280609f682728000d1767).toArray⟩
theorem h1:check 3 1 d1=true:=by decide+kernel
def d2:Row:=⟨BCurve 53 41 0x23df397ade78abb434aa7d6d0c3259e4fe6a3a8df9b8cfb0a3e447e11fa604a72858a5e501d380cf8020e846841fdd87b00000000000019c037e819600030000000000001298294c12e40020000000000000b701ab00c680010007,decode 5 1 0x76bb469f9b658a50187b0000300002000010007,(AH 7 0x2bb407e6dc0546014e80528000d18a5702a580a8a02960003461edc1836060a817e8000d1cfd706458190a0632000347c85c282609fe82748000d1756).toArray⟩
theorem h2:check 3 2 d2=true:=by decide+kernel
def d3:Row:=⟨BCurve 53 42 0x93fb72f2e49eaecc6954fada1865baa7e31a8babf008cfb0a3e447ebc439ec50c0989298812d408440183031f2164ac3400000000000009b614440914000c0000000000003aa07c78381800400000000000013c82b6813c80010007,decode 5 1 0x76bb369f8065892018680000300002000010007,(AH 7 0xaecc1f80701518053a014a00034624980a9a029a0003361a1c1856060e817f8000d1ce3706498191a0636000347c11c28360a0282758000d1745).toArray⟩
theorem h3:check 3 3 d3=true:=by decide+kernel
def d4:Row:=⟨BCurve 53 42 0x9879fffa4f5aaec86954fada1866be3b2189d17beca8cfb0a3e447f668cdd3fa58d87ebe8170c0a0c0211c42be1d8ac2a8000000000000d941b9c0c42000c00000000000054d0aec84df80040000000000001e8040581cf00010007,decode 5 1 0x76bb269f656587e018550000300002000010007,(AH 7 0xaec81f656015280528000cd87e702a980a9a029a000346155c1866061681808000d1cc9706518193a063a000347b9dc28560a0a82778000d1733).toArray⟩
theorem h4:check 3 4 d4=true:=by decide+kernel
def d5:Row:=⟨BCurve 54 42 0x273e23406e85abb11a553eb6860cf8a320f9fd017d2d19f6147c888010d61bba3f1186be481b440bd40159c2ad312d76108000000000000482890083f880030000000000000e781d310ced00080000000000002b98598027e00010007,decode 5 1 0x76bb169f4b6586b018420000300002000010007,(AH 7 0x2bb107d2d8054a014e0003361ad80aaa029e000336109c1876061a81828000d1caf706558194a0642000347b25c28760a1282798000d1722).toArray⟩
theorem h5:check 3 5 d5=true:=by decide+kernel
def d6:Row:=⟨BCurve 54 43 0xa1771a0924d2aec034aa7d6d0c1a32fdbb857fa6f98919f6147c8880b6b781e2e6758588540fbe06ce00da11aaa8badb05c00000000000017182d7613f4000c00000000000025dc4b2e211a00100000000000003b1076e034980010007,decode 5 1 0x76bb069f31658580182e0000300002000010007,(AH 7 0x2bb007cc5c0556015280538000d1858702ad80aaa02a20003460b9c1896061e81838000d1c947065d8195a0646000347ab1c28960a1a827b8000d1710).toArray⟩
theorem h6:check 3 6 d6=true:=by decide+kernel
def d7:Row:=⟨BCurve 54 43 0xa5f5a7108f8eaebc34aa7d6d0c1a73e28b21511af8c919f6147c88816100c05d7ff984498411da07b2010c020728e28b0360000000000001cbe37f81878000c0000000000002ff85e16293e00100000000000004ce8987843180010007,decode 5 1 0x76baf69f19658440181b0000300002000010007,(AH 7 0xaebc1f19701558054a014e00034611180aba02a200033606dc18a6062681858000d1c7a706618197a064e000347a39c28b60a22827d8000d16ff).toArray⟩
theorem h7:check 3 7 d7=true:=by decide+kernel
def d8:Row:=⟨BCurve 54 43 0xaa743417fa4aaeb834aa7d6d0c1ab4c75abd228ef80119f6147c888206e22686275d830ab413f608960142b26c190dcb00e00000000000022fc43881d6e000c0000000000003b44731a324600100000000000006120be4853600010007,decode 5 1 0x76bae69f0065830018070000300002000010007,(AH 7 0xaeb81f006015680538000cd830702b180aba02a600034601dc18b6062a81868000d1c5f706698198a06560003479c1c28d60a2a827f8000d16ed).toArray⟩
theorem h8:check 3 8 d8=true:=by decide+kernel
def d9:Row:=⟨BCurve 55 43 0x2bbcb047d941abad0d2a9f5b43035ecfda89d5065ee7233ec28f91082acc38caecec181d8d4523066a5f45022e1737bbd7f3be41612097a00bf116cbc9e4d6db0000000000000a74940988b5800300000000000008f8114747864002000000000000077b8e85065700010008,decode 5 1 0x76bad69ee76581d597f3016db0000300002000010008,(AH 7 0x2bad07b9d8055a015200033607580aca02a6000335fcdc18d6063281878000d1c447066d819aa065a000347949c28e60a2e82818000d16db).toArray⟩
theorem h9:check 3 9 d9=true:=by decide+kernel
def d10:Row:=⟨BCurve 55 43 0x2cdc5389b3f0abac0d2a9f5b430366ec747d4f34dece233ec28f9108352a4f2d776258098d4523066a5f6e47aa2b955b97dfd14182e0a5e00df29a7a4b77d6c90000000000000c5017748a2c00030000000000000aad946ec8e04002000000000000090b1169079480010008,decode 5 1 0x76bac69ece65809597df016c90000300002000010008,(AH 7 0x2bac07b39c0566015680548000d1809702b580aca02aa000345f7dc18e6063681898000d1c2870675819ca06620003478d1c29060a3682838000d16c9).toArray⟩
theorem h10:check 3 10 d10=true:=by decide+kernel
def d11:Row:=⟨BCurve 55 43 0x2dfbf6cb8e9fabab0d2a9f5b43036f090e70c9635eb5233ec28f91083f88659001d897f58d4523066a5f978d263ff2fb57cbe441a4a0b420101a1e6c4d2756b70000000000000e519b230bbf00030000000000000c8917d9ca56c0020000000000000ac0949088ee80010008,decode 5 1 0x76bab69eb5657f5597cb016b70000300002000010008,(AH 7 0x2bab07ad58056a0152000335fd580ada02aa000335f2dc1906063e818a8000d1c0d70679819da0666000347855c29260a3e82858000d16b7).toArray⟩
theorem h11:check 3 11 d11=true:=by decide+kernel
def d12:Row:=⟨BCurve 55 43 0x2f1b9a0d694eabaa0d2a9f5b43037725a8644391de9b233ec28f910849e67bf28c4ed7e18d4523066a5fc0d2a254509b17b7f741c660c2601267a2a1cef356a500000000000010791f150d6e80030000000000000e8a9b884be9c0020000000000000c9c17fb8a6500010008,decode 5 1 0x76baa69e9b657e1597b7016a50000300002000010008,(AH 7 0xaea81e9b6015a80558000cd7e1702b980ada02ae000345eddc19160642818c8000d1bf170681819fa066e0003477d9c29460a4682878000d16a5).toArray⟩
theorem h12:check 3 12 d12=true:=by decide+kernel
def d13:Row:=⟨BCurve 55 44 0x181d9ea7a1fed5d4834aa7d6d0c0dfc9fb4641ce97a04467d851f2210a88924aa2d8a2f988d4523066a5fea181e68ae3ad7a38520f41068500a6d938d686deb4980000000000004b1a8d2a3cea000c00000000000021643ef49b3280040000000000000e9d9baa0bf800010008,decode 5 1 0x76ba969e81657cc597a3016930000300002000010008,(AH 7 0xaea41e816015a80558000cd7cc702bd80aea02ae000345e8dc1936064a818e8000d1bd57068981a0a067600034775dc29660a4e82898000d1693).toArray⟩
theorem h13:check 3 13 d13=true:=by decide+kernel
def d14:Row:=⟨BCurve 56 44 0xc56b82447ab2aea01a553eb686038744870c8168de67119f6147c88217970acca08655ee11a8a460cd4a012431036ff06178e8ea104f06f7005dd2af5d4b835a00000000000000153a27c39123000300000000000004bfe8ebf3d95000800000000000010c51f9c0da780010008,decode 5 1 0x76ba869e67657b85978e016800000300002000010008,(AH 7 0x2ba80799dc0576015a80558000d17b8702bd80aea02b2000345e39c1946064e818f8000d1bb97068d81a2a067a0003476e1c29860a56828b8000d1680).toArray⟩
theorem h14:check 3 14 d14=true:=by decide+kernel
def d15:Row:=⟨BCurve 56 44 0xc9ea0f4be56eae9c1a553eb686038f46cbc145115e4c119f6147c8821a2e90654323e5e8d1a8a460cd4a03b888c4b5ca5d77a982115d07690068d0c35d540959b800000000000017d3ac8013280003000000000000055cca0a3453700080000000000001312a3d18f7380010008,decode 5 1 0x76ba769e4c657a35977a0166e0000300002000010008,(AH 7 0xae9c1e4c6015e80558000cd7a3702c180afa02b6000345de9c1966065681918000d1b9d7069581a4a0682000347661c29a60a5e828d8000d166e).toArray⟩
theorem h15:check 3 15 d15=true:=by decide+kernel
def d16:Row:=⟨BCurve 56 44 0xce689c53502aae981a553eb68603976365b4bf3fde31119f6147c8821cb4769c9df8f5e3d1a8a460cd4a063b37e19ad711765a1a126b07db007466d86b5d01596c0000000000001a9331801549800300000000000006032b3954d4b00080000000000001586284a915c00010008,decode 5 1 0x76ba669e316578f597650165b0000300002000010008,(AH 7 0x2ba6078c58057a015a000335e3d80b0a02b6000335d95c1976065a81928000d1b807069d81a5a068a0003475e1c29c60a66828f8000d165b).toArray⟩
theorem h16:check 3 16 d16=true:=by decide+kernel
def d17:Row:=⟨BCurve 56 44 0xd2e7295abae6ae941a553eb686039f65aa6982e85e15119f6147c8821f3a5cd3f8ce05de91a8a460cd4a08cf8fa2e0b10d750ab21379084d008094ee87666b59240000000000001d78b6c39787800300000000000006b30c79555d10008000000000000181fad07136100010008,decode 5 1 0x76ba569e156577a59750016490000300002000010008,(AH 7 0x2ba507855c0586015e80568000d177a702c580b0a02ba000345d41c1996066281948000d1b64706a181a7a0692000347561c29e60a6e82918000d1649).toArray⟩
theorem h17:check 3 17 d17=true:=by decide+kernel
def d18:Row:=⟨BCurve 56 44 0xd765b66225a2ae901a553eb68603a767ef1e4690ddf9119f6147c88221c0430b53a315d951a8a460cd4a0b523ebfc5bdc173bb4a148708bf008d5b05b1704758d800000000000020843c4a99e20003000000000000076c6dca35ec900080000000000001adf3207158280010008,decode 5 1 0x76ba469df9657655973b016360000300002000010008,(AH 7 0xae901df9701618057a015a000345d9580b1a02ba000335cedc19b6066a81968000d1b46706a981a9a06960003474e1c2a060a7682938000d1636).toArray⟩
theorem h18:check 3 18 d18=true:=by decide+kernel
def d19:Row:=⟨BCurve 56 44 0xdbe44369905eae8c1a553eb68603af6a33d30a395ddd119f6147c88224462942ae7825d411a8a460cd4a0dd4eddcaaca75726be215950931009ab91de97a95588c00000000000023b5c2151c590003000000000000082f4f2bf683300080000000000001dc4b74a97c080010008,decode 5 1 0x76ba369ddd6575059726016230000300002000010008,(AH 7 0xae8c1ddd6016280578000cd750702c980b1a02be000345c99c19c6066e81978000d1b29706b181aba069e00034745dc2a260a7e82968000d1623).toArray⟩
theorem h19:check 3 19 d19=true:=by decide+kernel
def d20:Row:=⟨BCurve 56 44 0xe062d070fb1aae881a553eb68603b76c7887cde1ddc0119f6147c88226cc0f7a094d35ced1a8a460cd4a10579cf98fd729711c7a16a309a300a8af372f85555840000000000000270d48231eec800300000000000008fbb09e9720f000800000000000020d03cd19a1b00010008,decode 5 1 0x76ba269dc06573b59711016100000300002000010008,(AH 7 0xae881dc06016280578000cd73b702cd80b2a02c2000345c45c19e6067681998000d1b0c706b981ada06a60003473d9c2a560a8682988000d1610).toArray⟩
theorem h20:check 3 20 d20=true:=by decide+kernel
def d21:Row:=⟨BCurve 56 44 0xe4e15d7865d6ae841a553eb68603bf5467fddb045da3119f6147c882294056501c59c5c951a8a460cd4a12c8a3721416956fbd1217b10a1500b73d5183908757f00000000000002a8ace74a19c800300000000000009d1922217c5d00080000000000002401c29c1c9200010008,decode 5 1 0x76ba169da365725596fb015fc0000300002000010008,(AH 7 0xae841da3701658058a015e000345c9580b3a02c2000335bedc1a06067e819b8000d1aee706c181aea06ae000347355c2a760a92829a8000d15fc).toArray⟩
theorem h21:check 3 21 d21=true:=by decide+kernel
def d22:Row:=⟨BCurve 56 44 0xe95fea7fd092ae801a553eb68603c756acb29eacdd85119f6147c8822bc63c87772ed5c411a8a460cd4a154b528ef923496e6daa18bf0a8700c6636ce59c2b57a40000000000002e2e5509a46900030000000000000ab0f3b67871d0008000000000000275948aa1f2580010008,decode 5 1 0x76ba069d8565710596e6015e90000300002000010008,(AH 7 0xae801d856016680588000cd710702d180b3a02c6000345b99c1a260682819d8000d1ad0706c981b0a06b60003472cdc2a960a9a829c8000d15e9).toArray⟩
theorem h22:check 3 22 d22=true:=by decide+kernel
def d23:Row:=⟨BCurve 56 44 0xedde77873b4eae7c1a553eb68603cf3e9c28abcf5d67119f6147c8822e3a835d8a3b65be91a8a460cd4a17bc59077d62b56d0e4219cd0af900d6218955a841575400000000000031f7dbe2275200030000000000000b99d55bb924f00080000000000002ad6cefba1d580010008,decode 5 1 0x76b9f69d67656fa596d0015d50000300002000010008,(AH 7 0xae7c1d676016680588000cd6fa702d580b4a02ca000345b41c1a36068a819f8000d1ab1706d181b2a06be000347245c2ab60aa2829f8000d15d5).toArray⟩
theorem h23:check 3 23 d23=true:=by decide+kernel
def d24:Row:=⟨BCurve 56 44 0xf25d048ea60aae781a553eb68603d7268b9eb8f1dd49119f6147c88230aeca339d47f5b911a8a460cd4a1a3f0824626f696baeda1adb0b6b00e677a6d3b4c9570800000000000035e762fe2a5780030000000000000c8c3711d9df300080000000000002e7a5590a4a200010008,decode 5 1 0x76b9e69d49656e4596ba015c20000300002000010008,(AH 7 0x2b9e07525c05a6016680588000d16e4702d580b4a02ca000345ae9c1a56069281a08000d1a93706d581b4a06c60003471bdc2ae60aaa82a18000d15c2).toArray⟩
theorem h24:check 3 24 d24=true:=by decide+kernel
def d25:Row:=⟨BCurve 56 44 0xf6db919610c6ae741a553eb68603df0e7b14c6145d2a119f6147c88233231109b05485b391a8a460cd4a1cb00e9ce6aed56a4f721be90bdd00f765c55fc1c356b800000000000039fcea5dad7980030000000000000d8818d8daa0900080000000000003243dc69278b00010008,decode 5 1 0x76b9d69d2a656ce596a4015ae0000300002000010008,(AH 7 0xae741d2a6016a80598000cd6ce702d980b5a02ce000345a91c1a76069a81a28000d1a74706e181b6a06ce000347131c2b060ab682a38000d15ae).toArray⟩
theorem h25:check 3 25 d25=true:=by decide+kernel
def d26:Row:=⟨BCurve 56 45 0x7dad0f4ebdc1573806954fada180f9bd9aa2b4cdb742c233ec28f91046b2eafbf86c22b5c11a8a460cd4a1f2115156aee4168e8050e7b8627808475f27ce797ab340000000000000f8e1c802c2e0000c0000000000001d1af56176d220010000000000000363363852a9080010008,decode 5 1 0x76b9c69d0b656b85968e0159a0000300002000010008,(AH 7 0xae701d0b6016a80598000cd6b8702dd80b6a02d2000345a39c1a9606a281a48000d1a55706e981b8a06d60003470a5c2b260abe82a68000d159a).toArray⟩
theorem h26:check 3 26 d26=true:=by decide+kernel
def d27:Row:=⟨BCurve 56 45 0x7fec55d2731f573606954fada180fbb101308a74d73ac233ec28f91046ff3fea91d4a4b5091a8a460cd4a21921b8def2dad6778510f028660808d8502d0ee86ab0c00000000000010a67e79cd04c000c0000000000001f38b932f871600100000000000003a48eae4adb280010008,decode 5 1 0x76b9b69ceb656a159677015860000300002000010008,(AH 7 0x2b9b073adc05b6016a80598000d16a1702dd80b6a02d20003459ddc1ab606aa81a68000d1a35706f181bba06de000347019c2b560ac682a88000d1586).toArray⟩
theorem h27:check 3 27 d27=true:=by decide+kernel
def d28:Row:=⟨BCurve 56 45 0x822b9c56287d573406954fada180fdaafd0e0dbd7732c233ec28f910474dc8c5543636b4591a8a460cd4a24032206736d1966189d0f8986998096e013abf5aeaae400000000000011c860844de2a000c00000000000021697d263a1ee00100000000000003e847287b0f100010008,decode 5 1 0x76b9a69ccb6568b59661015720000300002000010008,(AH 7 0xae681ccb6016e805a8000cd68b702e180b7a02d6000345985c1ad606b281a88000d1a15706f981bda06ea000346f89c2b760ad282ab8000d1572).toArray⟩
theorem h28:check 3 28 d28=true:=by decide+kernel
def d29:Row:=⟨BCurve 56 45 0x846ae2d9dddb573206954fada180ff9e639be364972ac233ec28f910479a1db3ed9eb8b3a11a8a460cd4a26627fda96df3d64a8e9101086d280a087250dfd0faaba00000000000012f3c29faec7a000c00000000000023ad413b3bdaa001000000000000042e5fa6e344c00010008,decode 5 1 0x76b9969cab656745964a0155d0000300002000010008,(AH 7 0xae641cab6016e805a8000cd674702e580b8a02da000345929c1af606ba81aa8000d19f57070181bfa06f2000346ef9c2ba60ada82ae8000d155d).toArray⟩
theorem h29:check 3 29 d29=true:=by decide+kernel
def d30:Row:=⟨BCurve 56 45 0x86aa295d9339573006954fada1810191ca29b90bb7230233ec28f91047e672a287073ab2e91a8a460cd4a28d386531b1ea96339351097870b80aa7a36f704a9aa920000000000001428a4cbefb3c000c00000000000026040571fda4a0010000000000000476d829837c380010008,decode 5 1 0x76b9869c8c6565d59633015490000300002000010008,(AH 7 0xae601c8c70171805ba016a00034597580b9a02da0003358cdc1b1606c281ac8000d19d57070981c1a06fa000346e65c2bc60ae682b08000d1549).toArray⟩
theorem h30:check 3 30 d30=true:=by decide+kernel
def d31:Row:=⟨BCurve 56 45 0x88e96fe14897572e06954fada181038530b78eb2d71bc233ec28f9104832c791206fbcb2311a8a460cd4a2b32e4273e90cd61c981111e874480b4b949670c7caa680000000000001567070910a70000c000000000000286dc9ca7f7ce00100000000000004c1b0b05bb5780010008,decode 5 1 0x76b9769c6f656465961c015340000300002000010008,(AH 7 0xae5c1c6f60172805b8000cd646702e980b9a02de000345871c1b3606ca81ae8000d19b47071581c3a0706000346dd1c2bf60aee82b38000d1534).toArray⟩
theorem h31:check 3 31 d31=true:=by decide+kernel
def d32:Row:=⟨BCurve 56 45 0x8b28b664fdf5572c06954fada181057201f5b6b877144233ec28f910487ce89390df2eb1711a8a460cd4a2d9241fb6202f16049cd11a5877d80bf445c5e1488aa3e00000000000016aee95711a16000c0000000000002aea8e44c1636001000000000000050ee93b6bf0800010008,decode 5 1 0x76b9669c516562e596040151f0000300002000010008,(AH 7 0xae581c5160172805b8000cd62e702ed80baa02e2000345811c1b5606d281b18000d19927071d81c6a070e000346d3dc2c160afa82b58000d151f).toArray⟩
theorem h32:check 3 32 d32=true:=by decide+kernel
def d33:Row:=⟨BCurve 56 45 0x8d67fce8b353572a06954fada181076568838c5f970c8233ec28f91048c93d822a47b0b0b91a8a460cd4a2ff19fcf8575155eda19122c87b680ca1b6fdc1ccdaa1400000000000018004bb5f2a2e000c0000000000002d7a52e0c3582001000000000000055e81cab42d500010008,decode 5 1 0x76b9569c3265617595ed0150a0000300002000010008,(AH 7 0xae541c3270175805ca016e00034585d80bba02e60003357b5c1b7606da81b38000d19717072581c8a0716000346ca5c2c460b0282b88000d150a).toArray⟩
theorem h33:check 3 33 d33=true:=by decide+kernel
def d34:Row:=⟨BCurve 56 45 0x8fa7436c68b1572806954fada181095239c1b4653704c233ec28f91049135e849ab722aff91a8a460cd4a3250fda3a8e7395d5a6512b387ef80d53e83e1254ba9ea000000000000195b2e25b3ab8000c000000000000301d179e855b200100000000000005b07a5e346be80010008,decode 5 1 0x76b9469c13655ff595d5014f50000300002000010008,(AH 7 0xae501c1360176805c8000cd5ff702f180bba02ea000345755c1b9606e281b58000d194f7073181cba0722000346c09c2c660b0e82bb8000d14f5).toArray⟩
theorem h34:check 3 34 d34=true:=by decide+kernel
def d35:Row:=⟨BCurve 56 45 0x91e689f01e0f572606954fada1810b3f0affdc6ad6fd0233ec28f910495d7f870b2694af391a8a460cd4a34b05b77cc595d5bdab1133a882880e0ad986d2e02a9c00000000000001abf90a654bb4000c00000000000032d2dc7e076c60010000000000000604d2f5ecac480010008,decode 5 1 0x76b9369bf4655e7595bd014e00000300002000010008,(AH 7 0x2b9306fd1c05e60176805c8000d15e7702f580bca02ea0003456f5c1bc606ea81b88000d192c7073981cda072a000346b71c2c960b1a82be8000d14e0).toArray⟩
theorem h35:check 3 35 d35=true:=by decide+kernel
def d36:Row:=⟨BCurve 56 45 0x9425d073d36d572406954fada1810d2bdc3e047076f4c233ec28f91049a56c9d529cf6ae791a8a460cd4a36fe10a78efe395a4afd13c1886180ec68ad8036f2a9940000000000001c2d7337d5d22000c000000000000359ba17f498be001000000000000065b8b91dcee700010008,decode 5 1 0x76b9269bd3655cf595a4014ca0000300002000010008,(AH 7 0xae481bd36017a805d8000cd5cf702f980bda02ee000345691c1be606f681ba8000d19097074581d0a0736000346ad1c2cc60b2282c08000d14ca).toArray⟩
theorem h36:check 3 36 d36=true:=by decide+kernel
def d37:Row:=⟨BCurve 56 45 0x966516f788cb572206954fada1810f12182c7ed496ecc233ec28f91049ef8d9fc30c68adb11a8a460cd4a394bc5d751a31558cb491448889a80f86fc31a401ba9680000000000001da4d5da36f02000c000000000000387766a24bb9a00100000000000006b4a4320532600010008,decode 5 1 0x76b9169bb3655b65958c014b40000300002000010008,(AH 7 0xae441bb36017a805d8000cd5b6702fd80bea02f2000345631c1c1606fe81bc8000d18e67075181d2a0742000346a31c2cf60b2e82c38000d14b4).toArray⟩
theorem h37:check 3 37 d37=true:=by decide+kernel
def d38:Row:=⟨BCurve 56 45 0x98a45d7b3e29572006954fada18110fee96aa6da36e44233ec28f9104a377ab60a82caacf11a8a460cd4a3b997b071447f1573b9514cf88d38104c2d93b497da93c0000000000001f25b88d78154000c0000000000003b662be70df5a00100000000000007101cd66578180010008,decode 5 1 0x76b9069b916559e595730149e0000300002000010008,(AH 7 0xae401b917017d805ea017600034567980bfa02f60003355cdc1c36070a81bf8000d18c37075981d5a074e000346991c2d160b3a82c68000d149e).toArray⟩
theorem h38:check 3 38 d38=true:=by decide+kernel
def d39:Row:=⟨BCurve 56 45 0x9ae3a3fef387571e06954fada18112e52559213e56dc0233ec28f9104a7f67cc51f92cac291a8a460cd4a3de73036d6eccd55abe11556890c811161efe35318a91000000000000020b01b5199418000c0000000000003e67f14d903fe001000000000000076df57efdbf980010008,decode 5 1 0x76b8f69b70655855955a014880000300002000010008,(AH 7 0x2b8f06dc1805fa017a00033561580c0a02fa000335569c1c56071281c28000d189e7076581d8a07560003468edc2d460b4682c98000d1488).toArray⟩
theorem h39:check 3 39 d39=true:=by decide+kernel
def d40:Row:=⟨BCurve 56 45 0x9d22ea82a8e5571c06954fada18114c4cbf7ee00f6d34233ec28f9104ac754e2996f8eab591a8a460cd4a4034e5669991a9541c2d15dd8945811e4d07125ceca8e40000000000002243fe269a74e000c000000000000417cb6d5d298600100000000000007ce2e2bce08e00010008,decode 5 1 0x76b8e69b4d6556b59541014720000300002000010008,(AH 7 0x2b8e06d35c0606017e805e8000d156b7030580c0a02fe000345505c1c86071e81c48000d187a7077181dba0762000346845c2d760b5282cc8000d1472).toArray⟩
theorem h40:check 3 40 d40=true:=by decide+kernel
def d41:Row:=⟨BCurve 56 45 0x9f6231065e43571a06954fada18116ab07e6686516ca8233ec28f9104b0d0e0cb7ece0aa911a8a460cd4a4270f1f1fb693d527c791664897e812b841ec866f9a8b600000000000023e1610c7baf6000c00000000000044a47c7fd4ff20010000000000000830c6dcd653f00010008,decode 5 1 0x76b8d69b2a65552595270145b0000300002000010008,(AH 7 0xae341b2a60182805f8000cd5527030980c1a030200034549dc1cb6072681c78000d18547077d81dea076e00034679dc2da60b5e82cf8000d145b).toArray⟩
theorem h41:check 3 41 d41=true:=by decide+kernel
def d42:Row:=⟨BCurve 56 45 0xa1a1778a13a1571806954fada181188aae853527b6c18233ec28f9104b52c736d66a32a9c11a8a460cd4a44acfe7d5d40d150dcc516eb89b78139073705713fa888000000000000258844033cf10000c00000000000047df424b977420010000000000000895bf9216a0c80010008,decode 5 1 0x76b8c69b06655385950d014440000300002000010008,(AH 7 0xae301b0660182805f8000cd5387030d80c2a0302000345435c1cd6073281ca8000d182f7078981e1a077e0003466f1c2dd60b6a82d38000d1444).toArray⟩
theorem h42:check 3 42 d42=true:=by decide+kernel
def d43:Row:=⟨BCurve 56 45 0xa3e0be0dc8ff571606954fada1811a6a552401ea56b88233ec28f9104b988060f4e784a8f11a8a460cd4a46e90b08bf18654f3d11177289f08146d64fc97bbea85a0000000000002738a70ade39c000c0000000000004b2d083919f7600100000000000008fd184b8eef680010008,decode 5 1 0x76b8b69ae26551e594f30142d0000300002000010008,(AH 7 0xae2c1ae27018680608000cd51e7031180c3a03060003453cdc1d06073e81cc8000d18087079581e4a078a000346645c2e060b7682d68000d142d).toArray⟩
theorem h43:check 3 43 d43=true:=by decide+kernel
def d44:Row:=⟨BCurve 56 45 0xa62004917e5d571406954fada1811c49fbc2ceacf6af4233ec28f9104bde398b1364d6a8211a8a460cd4a4925179420eff94d9d5d17f98a298154f169148676a82c00000000000028f28a235f89a000c0000000000004e8dce485c88e0010000000000000966d1093f3fd00010008,decode 5 1 0x76b8a69abd65504594d9014160000300002000010008,(AH 7 0xae281abd6018680608000cd5047031580c4a030a000345365c1d36074a81cf8000d17e2707a181e7a0796000346591c2e460b8282d98000d1416).toArray⟩
theorem h44:check 3 44 d44=true:=by decide+kernel
def d45:Row:=⟨BCurve 56 45 0xa85f4b1533bb571206954fada1811e230d11edce16a5c233ec28f9104c21bec908e918a7491a8a460cd4a4b61241f82c78d4beda918808a6281635882e69167a7fe0000000000002ab5ed4cc0e0a000c000000000000520194795f28a00100000000000009d2e9cb2792000010008,decode 5 1 0x76b8969a97654e9594be013ff0000300002000010008,(AH 7 0xae241a977018a80618000cd4e97031980c5a030e0003452f9c1d66075681d28000d17ba707b181eaa07a20003464ddc2e760b8e82dc8000d13ff).toArray⟩
theorem h45:check 3 45 d45=true:=by decide+kernel
def d46:Row:=⟨BCurve 56 45 0xaa9e9198e919571006954fada1811ffc1e610cef369c0233ec28f9104c654406fe6d5aa6711a8a460cd4a4d8b880683d1d94a3df519078a9b81720b9d3f9c91a7ce0000000000002c82d087023ec000c00000000000055885acc21d6a0010000000000000a41629147e5f80010008,decode 5 1 0x76b8869a70654ce594a3013e70000300002000010008,(AH 7 0xae201a706018a80618000cd4ce7031d80c6a031200034528dc1d96076281d58000d1792707bd81eea07b2000346425c2ea60b9e82e08000d13e7).toArray⟩
theorem h46:check 3 46 d46=true:=by decide+kernel
def d47:Row:=⟨BCurve 56 45 0xacddd81c9e77570e06954fada18121d52fb02c105692c233ec28f9104ca8c944f3f19ca5991a8a460cd4a4fb5ebed84dc25488e41198e8ad481810ab81fa7f4a79e0000000000002e5933d223a40000c00000000000059222140a492e0010000000000000ab23b5ba03bb80010008,decode 5 1 0x76b8769a4b654b359488013cf0000300002000010008,(AH 7 0xae1c1a4b7018e80628000cd4b37032180c7a0316000345221c1dc6076e81d98000d1769707c981f1a07be00034636dc2ed60baa82e38000d13cf).toArray⟩
theorem h47:check 3 47 d47=true:=by decide+kernel
def d48:Row:=⟨BCurve 56 45 0xaf1d1ea053d5570c06954fada18123ae40ff4b317689c233ec28f9104cea1a96c07ccea4c11a8a460cd4a51e04fd485e67146ce8d1a158b0d819055d386b390a76e0000000000003039172e25106000c0000000000005ccee7d6e75d60010000000000000b25742a3093400010008,decode 5 1 0x76b8669a27654985946c013b70000300002000010008,(AH 7 0xae181a276018e80628000cd4987032580c8a031a0003451b1c1df6077a81dc8000d1740707d981f5a07ce0003462adc2f160bb682e78000d13b7).toArray⟩
theorem h48:check 3 48 d48=true:=by decide+kernel
def d49:Row:=⟨BCurve 56 45 0xb15c65240933570a06954fada1812580bcfebcb116808233ec28f9104d2b6be88d0800a3e11a8a460cd4a53f90b17262375450ed91a9c8b46819fecef74bf65a73c00000000000032227a9b0683e000c000000000000608eae8eea3620010000000000000b9b0cfcf8ec900010008,decode 5 1 0x76b8569a026547c594500139e0000300002000010008,(AH 7 0xae141a027019280638000cd47c7032980c9a031e000345141c1e36078681df8000d1715707e981f9a07de0003461edc2f460bc682eb8000d139e).toArray⟩
theorem h49:check 3 49 d49=true:=by decide+kernel
def d50:Row:=⟨BCurve 56 45 0xb39baba7be91570806954fada181275338fe2e30b6770233ec28f9104d6cbd3a599332a3011a8a460cd4a5611c659c66079434f251b238b7f81afd00be9cb73a70a00000000000034155e18c7fe8000c00000000000064617568ad1d20010000000000000c1305d3f947a80010008,decode 5 1 0x76b84699dc6546059434013850000300002000010008,(AH 7 0xae1019dc6019280638000cd4607032d80caa03260003450d1c1e66079681e38000d16ea707f981fda07ee000346125c2f860bd282ee8000d1385).toArray⟩
theorem h50:check 3 50 d50=true:=by decide+kernel
def d51:Row:=⟨BCurve 56 45 0xb5daf22b73ef570606954fada181291f1fadf20ed66d8233ec28f9104dabda9ffd2554a2191a8a460cd4a582a819c669d7d417f711baa8bb881bfff28e5d7baa6d80000000000003611c1a769804000c00000000000068473c64301260010000000000000c8d5eaf31a4880010008,decode 5 1 0x76b83699b665443594170136c0000300002000010008,(AH 7 0xae0c19b67019680648000cd4437033180cba032a00034505dc1ea607a281e78000d16bf708098201a07fe000346059c2fc60be282f28000d136c).toArray⟩
theorem h51:check 3 51 d51=true:=by decide+kernel
def d52:Row:=⟨BCurve 56 45 0xb81a38af294d570406954fada1812aeb065db5ecf6638233ec28f9104deaf805a0b776a1311a8a460cd4a5a433cdf06da813fafbd1c318bf181d07a4668e43aa6a60000000000003817a546eb092000c0000000000006c4003817315e0010000000000000d0a178ea203300010008,decode 5 1 0x76b826998e65426593fa013530000300002000010008,(AH 7 0xae08198e6019680648000cd4267033580cca032e000344fe9c1ed607b281ea8000d1692708198205a0812000345f8dc2ff60bf282f68000d1353).toArray⟩
theorem h52:check 3 52 d52=true:=by decide+kernel
def d53:Row:=⟨BCurve 58 46 0x5d2cbf996f55ab8101a553eb686012cb6ed0d79cb16594119f6147c8809c4fc2fe36a11140911a8a460cd48971293df51928f4f71f5f4e207d418f71947c62235d93398048e5c4615403c282c8e5e1e747240000000000000e89c23dd3264800300000000000003825e5603b13d00080000000000000d8930724a63a00010009,decode 5 1 0x76b816996565409593dc55339011c90000300002000010009,(AH 7 0xae0419657019a80658000cd4097033980cda0332000344f71c1f1607c281ee8000d16647082d8209a0822000345eb9c30360c0282fa8000d1339).toArray⟩
theorem h53:check 3 53 d53=true:=by decide+kernel
def d54:Row:=⟨BCurve 58 46 0x5e4c62db4a04ab8001a553eb686012e7c3e6d9007b64f0119f6147c8809cc995f12bd3353eb11a8a460cd4897945886e16e7e4ef9fe4a21480f586c2507678de04131f82a8e9fc631c03e4a90607fbcb41940000000000000f0ffb2e238c1000300000000000003a3549109ca3d00080000000000000e0aa95a2ac5d80010009,decode 5 1 0x76b806993c653eb593be5531f010650000300002000010009,(AH 7 0xae00193c6019a80658000cd3eb7033d80cea0336000344ef9c1f5607d281f28000d16357083d820ea0836000345dddc30760c0e82fe8000d131f).toArray⟩
theorem h54:check 3 54 d54=true:=by decide+kernel
def d55:Row:=⟨BCurve 57 46 0x5f6c061d24b3ab7f01a553eb686026075f4fbf145ac888233ec28f9102750da390841564f3046a291833524c0b0e9738a536a741034fb044254ffa4c941263d9ed3058508ee3464e4080ece88702c4279f00000000000003e62508aafce8000c0000000000001e271668ef1d780040000000000000e8e82464329d80010009,decode 5 1 0x76b7f69911653cc593a05530500f3e0000300002000010009,(AH 7 0x2b7f064458067a019a000334f3180d0a033a000334e81c1f9607e281f78000d1606708518213a084a000345d01c30b60c1e83028000d1305).toArray⟩
theorem h55:check 3 55 d55=true:=by decide+kernel
def d56:Row:=⟨BCurve 57 46 0x608ba95eff62ab7e01a553eb68602640097bc1dbeec730233ec28f910276e34ffb111574eb846a291833524c49bbd67479852703077a4fe442ef9c5c8ecd1306a52ea8768f26c66ac08557b06ec61d27238000000000000408e346db173e000c0000000000001f384851ffec980040000000000000f14bb36938fa00010009,decode 5 1 0x76b7e698e6653ae59381552ea00e470000300002000010009,(AH 7 0xadf818e6701a280678000cd3ae7034980d1a0342000344e05c1fd607f281fb8000d15d5708658218a085e000345c19c30f60c2e83068000d12ea).toArray⟩
theorem h56:check 3 56 d56=true:=by decide+kernel
def d57:Row:=⟨BCurve 57 46 0xc3569941b42356fa034aa7d6d0c04cefc1fb9ddea58b90467d851f2204f171f8cb3c2b09c788d4523066a49910d22b609ba74d8a1749df08c11f44e032405c671259f0c517bf19e2f97a30a03b8a170e1789c8f6a46874089d57878498466ff800000000000042c3986193206000c000000000000204e3a4380bf480040000000000000f9d542b1bf730001000a,decode 5 1 0x76b7d698b96538f59362552cf34e1700dff000030000200001000a,(AH 7 0xadf418b9601a280678000cd38f7034d80d2a0346000344d89c2026080281ff8000d15a370879821da0872000345b2dc31360c42830b8000d12cf).toArray⟩
theorem h57:check 3 57 d57=true:=by decide+kernel
def d58:Row:=⟨BCurve 57 46 0xc595dfc5698156f8034aa7d6d0c04d5dcbabcc9d0d88b0467d851f2204f4fa12ddc69a29b788d4523066a49989c280c010f24d0a1f9f1e48fc5f81628f5a24ef92567107c71b3ca37b5a7ebf4fd5488e168c28fadc6a3c08e6640a38cf9e6ff000000000000045027c6654d40000c0000000000002168ec3d71958800400000000000010284d23dc6088001000a,decode 5 1 0x76b7c6988b6536f59342552b334e1600dfe000030000200001000a,(AH 7 0x504f6c13ba040a00034ab38188b601a680688000cd36f7035180d3a034a000344d09c2076081682048000d156f708918223a088a000345a39c31860c52830f8000d12b3).toArray⟩
theorem h58:check 3 58 d58=true:=by decide+kernel
def d59:Row:=⟨BCurve 57 46 0xc7d526491edf56f6034aa7d6d0c04dcbd55bfb5b7585f0467d851f2204f85eee2dc17849a788d4523066a49a02b2d61f863d4c8627f45d89378fbde0c03c96ed8a52f14a76775f63fd3aabec69278a4e158e88ff146c040930a08f0907da6fe8000000000000474ae07bf68ec000c00000000000022885e3fd26f5800400000000000010b5a620d4cba8001000a,decode 5 1 0x76b7b6985f6534f593215529734e1500dfd000030000200001000a,(AH 7 0x14138b04da80fe8000d29c40617dc06aa01a6000334d3dc0d66035680d48000d132170831820aa08260003454e9c22aa08a2000335941c31c60c6283148000d1297).toArray⟩
theorem h59:check 3 59 d59=true:=by decide+kernel
def d60:Row:=⟨BCurve 57 46 0xca146cccd43d56f4034aa7d6d0c04e3839b83eb17d8320467d851f2204fbc3c97dbc56699708d4523066a49a7ba32b7efb884c0230499cc972cffa5ac4e7b3424a4f718d25d382247f1ab8278780dcce1490e9034c6dcc097c0d15f540fa6fe0000000000000499cc4a27850a000c00000000000023ac904aa34cb800400000000000011455f22053890001000a,decode 5 1 0x76b7a698326532e593005527b34e1400dfc000030000200001000a,(AH 7 0x504cec131a03e600034a2b41832601aa80698000cd32e7035d80d6a0356000344c01c211a083e000335411c230a08ba00033583dc32160c7683198000d127b).toArray⟩
theorem h60:check 3 60 d60=true:=by decide+kernel
def d61:Row:=⟨BCurve 58 46 0x198a766a11336ade406954fada1804ea49e148207858040467d851f22027f945266db9a44c3446a2918335226bc0a55f18f6052df8e27b7026b8206da13ab6f2fa6497a39faa5f49c980faa370aae1400e13934907846f9404e454cf7ebd7f37ec00000000000012fe0a36768668003000000000000049ab04bbc85b5000800000000000011d778276da740001000a,decode 5 1 0x76b79698046530d592df5525e34e1300dfb000030000200001000a,(AH 7 0x1412eb04b280f58000d278706011806ba01aa000334c3580d8a035e000334b7dc2166085682148000d14cb708dec235a08be00034572dc32560c8a831d8000d125e).toArray⟩
theorem h61:check 3 61 d61=true:=by decide+kernel
def d62:Row:=⟨BCurve 58 46 0x19d25f3a87df2ade006954fada1804f0f5d1cd9f52d7d40467d851f22028123814c497854bac46a2918335226d92be1035fde92bc903d06d27a520e684932fd33c6490642509178f4982da6dc7d345354e1295a90bbc715c050b3b1510daf337e80000000000001397434886fa7000300000000000004c0668f32a2450008000000000000126bf1310e17b8001000a,decode 5 1 0x76b78697d4652eb592bc5524134e1200dfa000030000200001000a,(AH 7 0x14129b04a280f18000d265405f51c06ca01ae000334badc0da6036680d88000d12bc70872821a8000cd491708fac23ca089a000345615c32a60c9a83228000d1241).toArray⟩
theorem h62:check 3 62 d62=true:=by decide+kernel
def d63:Row:=⟨BCurve 58 46 0x1a1a480afe8aeaddc06954fada1804f7876d1467a757a30467d851f220282c44f92ff1ee4b2046a2918335226f64d6c15305cd29a925256a2892215f5f933a074aa48924aa67cfd4ca84ba172d00b3b9ce1198090ff473240532b95bb0f8d937e40000000000001432dc5ecf704000300000000000004e6b4d3b6bf4700080000000000001302ca3ee689f8001000a,decode 5 1 0x76b77697a3652c85929a5522434e1100df9000030000200001000a,(AH 7 0x50496c123a03ba00034944c17a3a01b2000324b2180dba036a000334a69c222b0882821e8000d145570916c244a087a0003454edc32f60cae83278000d1224).toArray⟩
theorem h63:check 3 63 d63=true:=by decide+kernel
def d64:Row:=⟨BCurve 58 46 0x1a6230db7536aadd806954fada1804fe19085b2ffbd7710467d851f22028441df17253474a9446a29183352271139e29ae73212769467a67297f21d8323ad58f251481652fc6881a4b86999fa033294f0e109a69142c74ec055acfa35f173137e000000000000014d0d5794fe7d8003000000000000050d9b1948dcbb0008000000000000139c0350f6fe00001000a,decode 5 1 0x76b7669771652a5592765520534e1000df8000030000200001000a,(AH 7 0x50482c11fa03aa000348f0c1771601b6806c8000cd2a57037680dc8000cd276708a2c227a085600034505ac24da08560003353b9c33460cc2832d8000d1205).toArray⟩
theorem h64:check 3 64 d64=true:=by decide+kernel
def d65:Row:=⟨BCurve 58 46 0x1aaa19abebe26add406954fada18050475f9248b44573c0467d851f220285adcf3a038184a0046a29183352272d40e366aadbd251967cf642a6c2250fc8a026acbd479e5b525405fcc887907216aa5f4ce0f9cc9186476b405837dec1b35fb37dc00000000000015712e980861380030000000000000535195fe8faa1000800000000000014379c673f73d0001000a,decode 5 1 0x76b756973c6528059251551e734e0f00df7000030000200001000a,(AH 7 0x1411cb046e80e68000d226605cf1806ea01b6000334a01c0df6037a80dd8000d1251708bec22ea0836000344f56c256a0836000335275c33960cd683328000d11e7).toArray⟩
theorem h65:check 3 65 d65=true:=by decide+kernel
def d66:Row:=⟨BCurve 58 46 0x1af2027c628e2add006954fada18050aed3f2c9d12d7070467d851f22028719bf5ce1ce9497046a29183352274712cfa654dc922c98924612b58e2c9be80c0995de471e63a83f8a54d8a584db0a729ab4e0e9f291c9c787c05acc435e5553737d80000000000001613e7baf8dc60003000000000000055d2fa79718f9000800000000000014d59581bfeb68001000a,decode 5 1 0x76b74697076525c5922c551c734e0e00df6000030000200001000a,(AH 7 0x14118b045e80e38000d20fb05c1dc06fa01ba00033497180e0a037e0003348b1c237b08da82058000d139070982c25fa0816000345121c33f60cee83388000d11c7).toArray⟩
theorem h66:check 3 66 d66=true:=by decide+kernel
def d67:Row:=⟨BCurve 58 46 0x1b39eb4cd939eadcc06954fada1805112fdab741d556cf0467d851f22028874101e7853248d846a291833522761ff462c0bb1d2069aa795e2c45e342781f101c9d246a26bfe2b0eace8c37734de8b4728e0da18920d47a4405d6a280bd74e537d400000000000016b900e22159500030000000000000585ddf05337c300080000000000001575eea07864c8001000a,decode 5 1 0x76b73696cf6523659206551a834e0d00df5000030000200001000a,(AH 7 0x50452c113a037e000347e0816cf701c2806f8000cd2367038a80e18000cd206708fec23ea07f6000344d26c26aa07f6000334fbdc34460d02833e8000d11a8).toArray⟩
theorem h67:check 3 67 d67=true:=by decide+kernel
def d68:Row:=⟨BCurve 58 46 0x1b81d41d4fe5aadc806954fada1805175821033011d6980467d851f220289bcc17ec70f3483c46a29183352277ab6a825a8de11df9cbce5b2d32e3bb2964f0f3a8a461e7454169304e8e1677f92f42cd0e0ca3e9250c7c0c060118cca3950537d000000000000017607a0d81d80800300000000000005af243a1d56ff00080000000000001618a7c368dff0001000a,decode 5 1 0x76b72696986520f591df5518734e0c00df4000030000200001000a,(AH 7 0x50442c10fa03720003477ec1698701c680708000cd20f7039280e38000cd1dfb091e81f68000cd2fe509bec26ba07da000344e45c34a60d1a83448000d1187).toArray⟩
theorem h68:check 3 68 d68=true:=by decide+kernel
def d69:Row:=⟨BCurve 58 46 0x1bc9bcedc6916adc406954fada18051d80674f1e4e565f0467d851f22028af3d37dce02c47a046a2918335227936e0a1f460a51b79ed23582e1fe433d252631e806459a7caa02175cf8ff55bb27adbb5ce0ba64929447dd4062c271997b59737cc000000000000180a533d1a588800300000000000005d90284f576ad000800000000000016bdc0ea915ce0001000a,decode 5 1 0x76b716965f651e8591b75516634e0b00df3000030000200001000a,(AH 7 0x1410cb042e80d98000d1c660597dc072a01c60003347a1c0e6a03960003346ddc251b094281ef8000d12af5099ac263a07be000344cbdc35060d32834a8000d1166).toArray⟩
theorem h69:check 3 69 d69=true:=by decide+kernel
def d70:Row:=⟨BCurve 58 46 0x1c11a5be3d3d2adc006954fada18052374031d9f7ed6230467d851f22028c19461b8d2dd46fc46a2918335227ab0ae1d2d662118ea0e78552f0ce4ac72e7669d245451284ffed9bb5091d41e79cb7baece0aa8a92d7c7f9c0657cd6799d69b37c800000000000018b68c70eadad0003000000000000060378d0db96cd000800000000000017653a15f1db98001000a,decode 5 1 0x76b7069623651bf5918e5514434e0a00df2000030000200001000a,(AH 7 0x50426c107a035a000346b101623701ce80728000cd1bf703a280e78000cd18eb096e81e88000cd25c5097ac25ba07a2000344b21c35660d4a83508000d1144).toArray⟩
theorem h70:check 3 70 d70=true:=by decide+kernel
def d71:Row:=⟨BCurve 58 46 0x71663a3acfa3ab6f01a553eb686014a53526b5a8a55794119f6147c880a346de7daf31f919511a8a460cd489f0634bd016795458e8bf3548bfe794942c8fedbe521121a355764803464ecb013c848ae238269265feb3f2e935bf8f35161cccdf1ab0931b4816406840bb6a9f8113694000000000000196525a8f35ee0003000000000000062e871dcfb75f0008000000000000180f13458a5c18001000b,decode 5 1 0x76b6f695e565195591635512134e0910df100da5000030000200001000b,(AH 7 0x14105b041280d38000d191305795c074a01ce000334655c0eaa03a600033458d4255b094a81e18000d120650956c252a0786000344971c35d60d6683578000d1121).toArray⟩
theorem h71:check 3 71 d71=true:=by decide+kernel
def d72:Row:=⟨BCurve 58 46 0x7285dd7caa52ab6e01a553eb686014bc30ebf9f9375690119f6147c880a383039c29265d16a11a8a460cd489f603df2b775a244de944893cc39a96766c208653c1d0fea56af129194a564504c9ef434c38229aca4e6f786913c388c4a440ecdf0ad6935ec832c06b0e206c819f935080000000000001a161ee533e4b8003000000000000065a2d6bd1d863000800000000000018bb4c795ade60001000b,decode 5 1 0x76b6e695a46516a59137550fe34e0810df000d42000030000200001000b,(AH 7 0x14102b040280d08000d175405691c075a01d20003345a980eca03ae0003344dd424db092e81da8000d11ab50936c24ba076a0003447b1c36360d7e835e8000d10fe).toArray⟩
theorem h72:check 3 72 d72=true:=by decide+kernel
def d73:Row:=⟨BCurve 58 46 0x73a580be8501ab6d01a553eb686014d2c35c436fb15584119f6147c880a3bac0e25128a113e11a8a460cd489fb172d63d1d0b442a9c9dd30c74e98588a4f643be4d0d9a7806c0a2f4e5dbe848f6e17f8381ea32e9e2afde8f5709366c760c4defafc93a2484f406de5057f43c53339c0000000000001ac97825ac6c5800300000000000006866bbae1f9d900080000000000001969e5b1636270001000b,decode 5 1 0x76b6d695616513e5910a550d934e0710def00ce7000030000200001000b,(AH 7 0x503fac0fda03360003456201561701da80758000cd13e703bec0eea03aa0003444294246b090e81d48000d114d5091ac243a07520003445ddc36a60d9a83658000d10d9).toArray⟩
theorem h73:check 3 73 d73=true:=by decide+kernel
def d74:Row:=⟨BCurve 58 46 0x74c524005fb0ab6c01a553eb686014e883229731fb546c119f6147c880a3ee16502738c511011a8a460cd48a002a7b9c2c4744372a4f3124cb029a3a871c877338d0b4a995e6eb45526537808d0108e7381aab92ede68368d9a33f82f15ba0deeb2293e5c86bc070c56aa2e5f1f32480000000000001b7f316a5cf5c000300000000000006b3420b001bc100080000000000001a1adeeda3e848001000b,decode 5 1 0x76b6c6951b65110590dc550b434e0610dee00c92000030000200001000b,(AH 7 0x503eec0faa032a000344eb4151bb01de80738000cd110703c6c0f0a039e000344371423eb08ee81cd8000d10ea508fac23ba07360003443f9c37260dba836d8000d10b4).toArray⟩
theorem h74:check 3 74 d74=true:=by decide+kernel
def d75:Row:=⟨BCurve 58 46 0x1d7931d08e97eadac06954fada18053f5c0fbd500554d20467d851f22029050d0d41dca2438023428e38c67161a3c22867eb350ab08d0a38e319c5b3327304825284212ad48518ceb69c1c6287eff9bd9080abab61cc5b526caff8c2a8082b3816b3f73da208d8e24ae302574760dedaf097b58cd7a370903e094ab4b31d6b3f73da208d8c6963cca9a6d0cc6cb48942948884073af4fd76825d31300000000000001c374ab34580f000300000000000006e0b05c2c3e1b00080000000000001ace382e1c6fe8001000e,decode 5 1 0x76b6b694d2650e0610ab5d0845508034e0510ded18c7510c6c00c4c000030000200001000e,(AH 7 0x140f8b03da80c88000d11c50534ac078a01c6000334381c0f4b03ce80e38000d10ab508dec234a071e0003442114237b08d281c78000d108070de683758000cd08e).toArray⟩
theorem h75:check 3 75 d75=true:=by decide+kernel
def d76:Row:=⟨BCurve 58 46 0x77046a84150eab6a01a553eb68601511f4065874175218119f6147c880a435ea4195ba2d0af03d4780806843b3c99f2d19bdc41e6b59d90cd26a9dfe1c919dcf734fceadc0dcad71567427ed3063319f3812bc5b8d5d8e58fa35ffab79982cdecb12a4b739c063ddc598e7e17e731bebc5b8d5d8e58e196c7b32f975cc6bb6e946cc8a4c076a2b51cca60d312c0000000000001cf1c400660de8003000000000000070eb6ae6660e700080000000000001b83f172ccf950001000d,decode 5 1 0x76b6a69486650af7107954fce34e0410dec18c6f10c6b00c4b000030000200001000d,(AH 7 0x503d6c0f3a0316000343f381486701eac079a01c20003442bdc0f7b03da80e08000d1079508c2c22da07060003440654230b08b681c18000d0ffe70e06837d8000cd066).toArray⟩
theorem h76:check 3 76 d76=true:=by decide+kernel
def d77:Row:=⟨BCurve 58 46 0x78240dc5efbdab6901a553eb686015253bcecb19d150d8119f6147c880a44a68c52e2b7107b03d47808068439c8631f82f44d4112c4bfdd1913d8fc9539b4e84f20dcab9494b048c140799f9a730ca2f31280000000000001dae9d51be9ca8003000000000000073d5501ae842500080000000000001c3c0abbb584800010009,decode 5 1 0x76b69694366507b7104410dca00c4a0000300002000010009,(AH 7 0x503c6c0f0a030e0003437281436b01ee806f8000cd07b703eac0f9a037a0003441114229b089a81bc8000d0fab508a6c226a06f2000343dddc38ab0e1a83778000d103d).toArray⟩
theorem h77:check 3 77 d77=true:=by decide+kernel
def d78:Row:=⟨BCurve 54 46 0x1e50ec41f29b2ada006954fada1854e069090b95cd3e30467d851f22291585e608ae1d41180f51e0201a1e11b12a060d7c100dbba94f3c8ddc7ca5ffda2eec32ee0000000000001e6dd6a74f2d3000300000000000076c8b5604a7d50008000000000001cf68408d611780010008,decode 5 1 0x76b68693e3650467100d00bb80000300002000010008,(AH 7 0xc0ef503bac0eda0302000352ee013e3701f6c07ca01b600034411ac0fda036e0003340354222b087e81b68000d0f385088ac21fa06da000343bb1c393b0e3e836b8000d1013).toArray⟩
theorem h78:check 3 78 d78=true:=by decide+kernel
def d79:Row:=⟨BCurve 54 46 0x1e98d5126946ead9c06954fada185526f2db288b3538c0467d851f2229163dae9cd84e40380f51e0201a1dadb25ba3d7c90fd4be0953748fa47fb5e552313c9265c000000000001f2f700117bf8000300000000000079c59ab68cbf70008000000000001db35d5a2ea0380010008,decode 5 1 0x76b676938c6500e70fd4009970000300002000010008,(AH 7 0x140ecb03ae80be8000d099704e32c07ea01b200033403ac100a0362000333f51421bb086681b08000d0ec25086ec219a06c200034396dc39cb0e6683608000d0fe8).toArray⟩
theorem h79:check 3 79 d79=true:=by decide+kernel
def d80:Row:=⟨BCurve 54 46 0x1ee0bde2dff2aad9806954fada18556a32056eafdd3320467d851f222914c18b08096f3f500f51e0201a1d4696ebbb1ccacf99c06957ac916c82cf4adb139411da4000000000001ff3695f1853980030000000000007ccc001daf08b0008000000000001e7296afbf30c00010008,decode 5 1 0x76b666933264fd470f99007690000300002000010008,(AH 7 0x140e9b03a280bb8000d076904ccac080a01aa000333f52c104a0356000333e654215b084a81ab8000d0e4850856c212a06ae00034371dc3a6b0e8e83568000d0fbb).toArray⟩
theorem h80:check 3 80 d80=true:=by decide+kernel
def d81:Row:=⟨BCurve 54 46 0x1f28a6b3569e6ad9406954fada1855a88133f29b652d40467d851f22290ff78535c4f83e5c0f51e0201a1cdc2192cb5c190f5bc2c95be4933485f23074d5f2b14b40000000000020b9c2c150e9780030000000000007fdbe595b15910008000000000001f34300987c3100010008,decode 5 1 0x76b65692d464f9770f5b0052d0000300002000010008,(AH 7 0x5039ac0e5a02e60003414b412d4b020a80698000ccf975041ec106a034e000343d6d420eb083281a68000d0dc95083ac20ca069a0003434b9c3b0b0eba834b8000d0f8c).toArray⟩
theorem h81:check 3 81 d81=true:=by decide+kernel
def d82:Row:=⟨BCurve 54 46 0x1f708f83cd4a2ad9006954fada1855e385ba9fb62d2730467d851f222907df9d260ae93d600f51e0201a1c6e5250d495b3cf1ac529601c94fc891e961f785870b8c0000000000021827c27c1812000300000000000082f54b1e93b090008000000000001ff829678857280010008,decode 5 1 0x76b646927364f5870f1a002e30000300002000010008,(AH 7 0x140e3b038a80b78000d02e3049cd4082b020680688000d0f5850412c103a0342000343c694208b081a81a18000d0d4750822c206a0686000343241c3bcb0eea83418000d0f5b).toArray⟩
theorem h82:check 3 82 d82=true:=by decide+kernel
def d83:Row:=⟨BCurve 54 46 0x1fb8785443f5ead8c06954fada1856199a458a97d520e0467d851f2228fd93c8ed57ca3c580f51e0201a1c0d32dc7864e3ced7c789645496c48c547bdafac55033800000000000224d95926a1a90003000000000000861830b8560f300080000000000020be82c9c0ed080010008,decode 5 1 0x76b636920e64f1670ed7000ce0000300002000010008,(AH 7 0x50386c0e0a02d600034022c120eb020280678000ccf1650406c100a033a000343b5d4202b0802819c8000d0cc15080ac200a0672000342fb5c3c8b0f1a83378000d0f28).toArray⟩
theorem h83:check 3 83 d83=true:=by decide+kernel
def d84:Row:=⟨BCurve 54 46 0x20006124baa1aad8806954fada18564c64289ea8bd1a50467d851f2228effa12772f133b480f51e0201a1c2b6bff270cb8ce91c9e9688c988c8f93e1a75d395033400000000000231b0f014ab5c800300000000000089449662f874f00080000000000021873c303184b00010008,decode 5 1 0x76b62691a564ed270e91000cd0000300002000010008,(AH 7 0x140deb037680b28000d000004695407fb01fa80658000d0ed2503fac0fda032e000343a4541fcb07ea81978000d0c36507f2c1faa065e000342d19c3d5b0f52832d8000d0ef3).toArray⟩
theorem h84:check 3 84 d84=true:=by decide+kernel
def d85:Row:=⟨BCurve 54 46 0x204849f5314d6ad8406954fada18567a3e0ff080851390467d851f2228e02c6fd80d4c3a2c0f51e0201a1c49a521d5b48dce49cc496cc49a5492dcc7849fb4703300000000000023eae8746352c80030000000000008c7a7c1e7ae1d0008000000000002252559ada1e200010008,decode 5 1 0x76b616913964e8b70e49000cc0000300002000010008,(AH 7 0xb036e80b08000cc000044e6c07da0192000333a2d40fbb03ea80c98000d0e49507dac1f4a064a000342ea141f6b07d281928000d0a9bb0f8a83248000ccebc).toArray⟩
theorem h85:check 3 85 d85=true:=by decide+kernel
def d86:Row:=⟨BCurve 54 46 0x209032c5a7f92ad8006954fada1856a4cd4f6b878d0c90467d851f2228cd10eafb75ed39080f51e0201a1c67de44845c62cdfecea970fc9c1c962f2d72c236b032c0000000000024bd21ebb3f1900030000000000008fb9e1eadd55d000800000000000231fcf09bab9580010008,decode 5 1 0x76b60690c964e4270dfe000cb0000300002000010008,(AH 7 0x140d9b036280ae8000d000004325407cb01ee80638000d0e42503e2c0f7a031a0003437f941f1b07be818d8000d0b16507c6c1efa06360003427ad43e2b0f7a831a8000d0e83).toArray⟩
theorem h86:check 3 86 d86=true:=by decide+kernel
def d87:Row:=⟨BCurve 54 46 0x20d81b961ea4ead7c06954fada1856ca6c932455750560467d851f2228b7c179f5e57e37d80f51e0201a1c861767330437cdb1d10975349de4998b1371c4c010328000000000002591bb673c92200030000000000009302c7c81fd0f00080000000000023efa87cd356580010008,decode 5 1 0x76b5f6905664df670db1000ca0000300002000010008,(AH 7 0x5035ec0d6a02b20003400001056b01ea80628000ccdf6503d6c0f4a03120003436c541ebb07a681898000d0a80507aec1e9a06260003424d943d7b0f4e83118000d0e48).toArray⟩
theorem h87:check 3 87 d87=true:=by decide+kernel
def d88:Row:=⟨BCurve 54 46 0x212004669550aad7806954fada1856ecc12f06529cfdf0467d851f22289f2426b2df7736a00f51e0201a1ca45089e1ac0ccd61d369796c9fac9cf07981a75090324000000000002668b4e6fd347800300000000000096552db64253300080000000000024c1e1f423f5200010008,decode 5 1 0x76b5e68fdf64da870d61000c90000300002000010008,(AH 7 0x50352c0d3a02aa0003400000fdfb01e680618000ccda8503cec0f2a030a00034358541e6b079281848000d09e65079ac1e4a06120003421f543ccb0f2283088000d0e0a).toArray⟩
theorem h88:check 3 88 d88=true:=by decide+kernel
def d89:Row:=⟨BCurve 54 46 0x2167ed370bfc6ad7406954fada18570a25cf2616a4f640467d851f22288338f13263d8355c0f51e0201a1cc289ac9053e1cd0ed5c97da4a174a05f5fa269e8303200000000000027420e6af5d89800300000000000099b113b544dc900080000000000025967b6fac95b00010008,decode 5 1 0x76b5d68f6464d5770d0e000c80000300002000010008,(AH 7 0x140d2b034680a88000d000003d914078b01de80608000d0d57503c2c0efa030200034343941e0b077a81808000d094750782c1dea0602000341efd43c1b0ef683008000d0dcb).toArray⟩
theorem h89:check 3 89 d89=true:=by decide+kernel
def d90:Row:=⟨BCurve 54 46 0x21afd60782a82ad7006954fada1857229a7383a18cee60467d851f22286519cf88ef29340c0f51e0201a1ce0c2cf3efbb6ccb9d82981dca33ca3d7c5d40c86f031c00000000000281dc7f3267e800030000000000009d1679c5276d1000800000000000266d74ef6d38080010008,decode 5 1 0x76b5c68ee664d0370cb9000c70000300002000010008,(AH 7 0x50342c0cfa029a0003400000ee6b01da805f8000ccd03503b6c0eca02fa0003432e541dbb0766817c8000d08a55076ec1d9a05f2000341bf543b7b0ece82f78000d0d89).toArray⟩
theorem h90:check 3 90 d90=true:=by decide+kernel
def d91:Row:=⟨BCurve 54 46 0x21f7bed7f953ead6c06954fada185737c4700a5bb4e640467d851f222844c6c1b6816a32b40f51e0201a1cfefbf1eda38bcc62da898614a504a759ac168f2cd03180000000000028fbe17f8f2630003000000000000a0855fe5ea04b0008000000000002746ce7365dc280010008,decode 5 1 0x76b5b68e6464cad70c62000c60000300002000010008,(AH 7 0x2c0cda02960003300000e64b01d6805e8000cccad503aec0eaa02f200034318941d6b075281788000d07ff5075ac1d4a05e20003418d943adb0ea682ef8000d0d45).toArray⟩
theorem h91:check 3 91 d91=true:=by decide+kernel
def d92:Row:=⟨BCurve 54 46 0x223fa7a86fffaad6806954fada185747fe70cedcbcddf0467d851f2228200bdb92218b31500f51e0201a1d1d35149c4b60cc07dce98a4ca6ccaae51269f1d9d03140000000000029dc5b102fcfa8003000000000000a3fdc6178ca37000800000000000282287fb9682100010008,decode 5 1 0x76b5a68ddf64c5470c07000c50000300002000010008,(AH 7 0x140cbb032a80a38000d00000377d4074b01ce805d8000d0c54503a2c0e7a02ea00034301d41d1b073e81738000d075550746c1cfa05ce0003415a943a3b0e7e82e78000d0cfe).toArray⟩
theorem h92:check 3 92 d92=true:=by decide+kernel
def d93:Row:=⟨BCurve 54 46 0x22879078e6ab6ad6406954fada185754edc9bc8d04d560467d851f2227fa36ff5945242fe40f51e0201a1d3b6e374af335cbabdf498e84a894ae79f8ce348df0310000000000002abf34a5087ae8003000000000000a77fac5a0f4950008000000000002900a187ff29c00010008,decode 5 1 0x76b5968d5664bf970bab000c40000300002000010008,(AH 7 0x140c9b032280a18000d0000035594073b01ca805c8000d0bf95039ac0e5a02e2000342ead41ccb072e816f8000d06a750732c1cba05be0003412694399b0e5a82df8000d0cb6).toArray⟩
theorem h93:check 3 93 d93=true:=by decide+kernel
def d94:Row:=⟨BCurve 54 46 0x22cf79495d572ad6006954fada18575e927ad36c8ccca0467d851f2227cffa4ace769d2e700f51e0201a1d59a759f99b0acb4be1a992bcaa5cb2185f4357493030c000000000002ba46e3e1927f0003000000000000ab0b12ad71f6500080000000000029e11b189fd3380010008,decode 5 1 0x76b5868cca64b9c70b4b000c30000300002000010008,(AH 7 0x140c7b031a809f8000d0000033294072b01c6805b8000d0b9c50392c0e3a02da000342d2d41c8b071a816c8000d05f550722c1c6a05b2000340f154390b0e3282d78000d0c6b).toArray⟩
theorem h94:check 3 94 d94=true:=by decide+kernel
def d95:Row:=⟨BCurve 54 46 0x23176219d402ead5c06954fada185761a1dc3caa94c3a0467d851f2227a389aa1aaf062cec0f51e0201a1d77e07ca842dfcae9e40996f4ac24b5c045c95a0b90308000000000002c8c07db61d6c0003000000000000ae9ff911b4aa70008000000000002ac3f4ad787e780010008,decode 5 1 0x76b5768c3a64b3b70ae9000c20000300002000010008,(AH 7 0x50316c0c4a027a0003400000c3ab01c2805a8000ccb3b50386c0e0a02d2000342ba541c3b070681688000d053f5070ec1c1a05a2000340bb14387b0e0e82cf8000d0c1e).toArray⟩
theorem h95:check 3 95 d95=true:=by decide+kernel
def d96:Row:=⟨BCurve 54 46 0x235f4aea4aaeaad5806954fada1857616695cf17dcba70467d851f222774e51d3dee5f2b600f51e0201a1d9656e6d76b1d0a85e6699b2cadecb971ac603cd510308000000000002d76017ce28758003000000000000b23e5f86d765b0008000000000002ba92e46892b800010008,decode 5 1 0x76b5668ba764ad870a85000c20000300002000010008,(AH 7 0x5030ec0c2a02720003400000ba7b01be80598000ccad85037ec0dea02ca000342a1541beb06f681648000d0485506fac1bda0592000340839437db0dea82c88000d0bcf).toArray⟩
theorem h96:check 3 96 d96=true:=by decide+kernel
def d97:Row:=⟨BCurve 54 46 0x23a733bac15a6ad5406954fada18575de0a78ab464b0f0467d851f222742f2ae23b82029cc0f51e0201a1db490098612f20a1ee8c99f64afb4bd2c9307ffa5b0304000000000002e625b229b39b8003000000000000b5e6460cda2810008000000000002c90c7e3d1da500010008,decode 5 1 0x76b5568b0f64a7370a1e000c10000300002000010008,(AH 7 0x50306c0c0a026a0003400000b0fb01ba80588000cca7350376c0dca02c200034287941bab06e281608000d03c7506eac1b8a05820003404b14374b0dc682c18000d0b7e).toArray⟩
theorem h97:check 3 97 d97=true:=by decide+kernel
def d98:Row:=⟨BCurve 54 46 0x23ef1c8b38062ad5006954fada1857556abd8417cca740467d851f22270db25ccc0c49282c0f51e0201a1dd2c92c34bac709b4eb29a39cb17cc0f0f9c0a27d70300000000000002f5114cc8bede0003000000000000b997aca3bcf190008000000000002d7ac185528ae80010008,decode 5 1 0x76b5468a7464a0b709b4000c00000300002000010008,(AH 7 0x502fec0bea02660003400000a74b01b680578000cca0b5036ec0daa02ba0003426d141b6b06d2815d8000d0305506dac1b4a0576000340115436cb0da282b98000d0b2a).toArray⟩
theorem h98:check 3 98 d98=true:=by decide+kernel
def d99:Row:=⟨BCurve 54 46 0x2437055baeb1ead4c06954fada185749aa2ba6aa749d50467d851f2226d63e1f4b676226840f51e0201a1df1024ee3629c0948ed89a7d4b344c4bee08a255c502fc0000000000030422e7ab4a3d0003000000000000bd52934b7fc230008000000000002e671b2b0b3d480010008,decode 5 1 0x76b53689d5649a170948000bf0000300002000010008,(AH 7 0xb02f680978000cc00002756c06ca015a000332686c0d8a02b200033252141b1b06c281598000d023f506c6c1b0a05660003400014363b0d8282b28000d0ad4).toArray⟩
theorem h99:check 3 99 d99=true:=by decide+kernel
def d100:Row:=⟨BCurve 54 46 0x91fbb8b09576ab520467d851f22269b7bff8d4ce324cc0f51e0201a1e0f3b71920a7108d9efe9ac0cb50cc89647648842502f8000000000003135a82d155b88003000000000000c116fa042299f0008000000000002f55d4d4fbf1700010007,decode 5 1 0x76b5264933708d9000be0000300002000010007,(AH 7 0xb02ee80968000cc000024cec06ba01560003324d2c0d6a02ae00033236541adb06b281568000d0175506b6c1aca055a000340001435bb0d6282ab8000d0a7d).toArray⟩
theorem h100:check 3 100 d100=true:=by decide+kernel
def d101:Row:=⟨BCurve 54 46 0x931b5bf27025ab510467d851f22265e85f3a6395422340f51e0201a1e2d749440b2460868f249b044b6d4cc772e4fcb2f702f400000000000322b81e3ae1508003000000000000c4e4e0cda578d0008000000000003046ee8324a7600010007,decode 5 1 0x76b516488d70868000bd0000300002000010007,(AH 7 0x140bab02e680948000d000002235406ab01a680548000d08c450352c0d3a02a60003421a141a9b069e81528000d00a7506a6c1a7a054a0003400014352b0d3e82a58000d0a22).toArray⟩
theorem h101:check 3 101 d101=true:=by decide+kernel
def d102:Row:=⟨BCurve 54 46 0x250ebfcd12b52ad400f51e0201a1e4badb6ef5a1b07e4f4a9b47cb89cd061954bee23b02f0000000000003323bb9e7ed050003000000000000c8bc47a8085ed000800000000000313a6835855f180010006,decode 5 1 0x76b50707e4000bc0000300002000010006,(AH 7 0x140b8b02de80938000d000001f914069b01a280538000d08525034ac0d1a029e000341fd141a5b068e814f8000d000050696c1a3a053e000340001434ab0d1e829e8000d09c6).toArray⟩
theorem h102:check 3 102 d102=true:=by decide+kernel
def d103:Row:=⟨BCurve 54 46 0x2556a89d8960ead3c0f51e0201a1e69e6d99e01f00738f709b8b4ba64d4557c58f11f102ec00000000000341e555d878d60003000000000000cc9d2e934b4bf000800000000000323041ec1e18980010006,decode 5 1 0x76b4f70738000bb0000300002000010006,(AH 7 0x140b6b02d680918000d000001ce14068b019e80538000d07dd50342c0cfa029a000341df941a1b067e814c8000d000050686c19fa05320003400014342b0cfe82988000d0967).toArray⟩
theorem h103:check 3 103 d103=true:=by decide+kernel
def d104:Row:=⟨BCurve 54 46 0x259e916e000caad380f51e0201a1e885d43cd2a2d4689f969bcecbc2cd852e376d421902ec00000000000351b4f20c84c38003000000000000d087958f6e40300080000000000033287ba6eed3e00010006,decode 5 1 0x76b4e70689000bb0000300002000010006,(AH 7 0xb02d280908000cc00001a26c067a014a000331d9ac0cea0292000331c15419db067281498000d000050676c19ca0526000340001433bb0ce282918000d0907).toArray⟩
theorem h104:check 3 104 d104=true:=by decide+kernel
def d105:Row:=⟨BCurve 54 46 0x25e67a3e76b86ad340f51e0201a1ea696667bd20245d5fbc9c124bdf4dc59caa5972b302e800000000000361aa8e8410cd8003000000000000d47b7c9c713b900080000000000034231565f790f00010006,decode 5 1 0x76b4d705d5000ba0000300002000010006,(AH 7 0x140b3b02ca808f8000d000001756c066a0146000331bb2c0cca028e000331a254199b066281468000d000050666c198a051a0003400014333b0cc2828b8000d08a4).toArray⟩
theorem h105:check 3 105 d105=true:=by decide+kernel
def d106:Row:=⟨BCurve 54 46 0x262e630eed642ad300f51e0201a1ec4cf892a79d7451dfe29c55cbfbce06a31e53a3bf02e400000000000371c62b3f1cf40003000000000000d878e3ba543e100080000000000035200f29384fc80010006,decode 5 1 0x76b4c7051d000b90000300002000010006,(AH 7 0x140b1b02c2808d8000d000001476c065a01420003319c2c0caa028600033182d4195b065281438000d000050656c194a050e000340001432bb0ca682858000d083f).toArray⟩
theorem h106:check 3 106 d106=true:=by decide+kernel
def d107:Row:=⟨BCurve 54 47 0x4cec97bec81fd5a580f51e0201a1ee308abd921ac44618044e4ca60c272420c9adea9e8170000000000000e081f20f6a4dc000c000000000001b8ff95d22e8f6001000000000000361f68f0b110680010006,decode 5 1 0x76b4b70461000b80000300002000010006,(AH 7 0x2c0afa02320003300000461b019280508000cc5f150326c0c8a02820003416294192b0642813f8000d00005064ac190a04fe0003400014324b0c86827f8000d07d7).toArray⟩
theorem h107:check 3 107 d107=true:=by decide+kernel
def d108:Row:=⟨BCurve 54 47 0x4d7c695fb57755a500f51e0201a1f0141ce87c98143a18174e6e661a67453c04b90396816e000000000000e49bd95fed65a000c000000000001c120645174b0e001000000000000372122bc61d2d00010006,decode 5 1 0x76b4a703a1000b70000300002000010006,(AH 7 0x502bac0ada022e00034000003a1b018e804f8000cc5705031ec0c6a027a00034141d418eb0636813d8000d00005063ac18da04f6000340001431db0c6a82798000d076e).toArray⟩
theorem h108:check 3 108 d108=true:=by decide+kernel
def d109:Row:=⟨BCurve 54 47 0x27061d8051676ad24008cc506efa84d223b29212441a480f51e0201a1f1fb838b6f1be82de82a4e902628a766a3404b1cc7816e000000000000e8bf40c15084a000c000000000001c95432f27ae0a00100000000000038253c8c4a97000010007,decode 5 1 0x76b496c349702de000b70000300002000010007,(AH 7 0x2c0aca022600033000002deb018a804e8000cc4ec50316c0c4a0276000341205418bb0626813a8000d00005062ec189a04ea0003400014316b0c4e82738000d0702).toArray⟩
theorem h109:check 3 109 d109=true:=by decide+kernel
def d110:Row:=⟨BCurve 54 47 0x274e0650c8132ad20008cc506efa84bfd14b2ba6721a480f51e0201a1f3df15b659993821783d4eb1e636e788567c643631816c000000000000ecec283393aac000c000000000001d19b01b5411ea001000000000000392bb6606b5cf80010007,decode 5 1 0x76b486c34970217000b60000300002000010007,(AH 7 0x140abb02aa80888000d00000085ec061a0136000331196c0c3a026e000330fe54187b061a81378000d00005061ec186a04de000340001430fb0c32826e8000d0694).toArray⟩
theorem h110:check 3 110 d110=true:=by decide+kernel
def d111:Row:=⟨BCurve 54 47 0x2795ef213ebeead1c008cc506efa84ad388141c2cc1a400f51e0201a1f5c2a7e144168814e8504ed3a64527aa55b9044fd4816a000000000000f1228fb6b6d80000c000000000001d9f4d099c76ae0010000000000003a349038c424b80010007,decode 5 1 0x76b476c3487014e000b50000300002000010007,(AH 7 0xb02a680878000cc000005394061b0182804d8000d03dc5030ac0c1a026a000340db94184b060a81348000d000050612c182a04d20003400014308b0c1682688000d0624).toArray⟩
theorem h111:check 3 111 d111=true:=by decide+kernel
def d112:Row:=⟨BCurve 52 47 0x13eeebf8dab55568c0046628377d49346c472556d03488634ef566537f3283d8ada6c2041000000000000f562774aba0c6000c00000000000789867e8037158004000000000003b3fca1554ee400010006,decode 5 1 0x76b466c348000820000300002000010006,(AH 7 0x140a8b029e80868000d0000002094060b017e804c8000d035150302c0bfa0262000340b814180b05fe81318000d000050602c17fa04c60003400014301b0bfa82628000d05b2).toArray⟩
theorem h112:check 3 112 d112=true:=by decide+kernel
def d113:Row:=⟨BCurve 50 37 0xa0970308b059ab458cc506efac91c996a919661a4000000000248d332b3aebe000c0000000012460cd0968648004000000000922c005c7cb500010005,decode 5 1 0x76b456c3486c0036c0026c0010005,(AH 7 0xb029a80858000cc00000002c05fa012e000330b0ac0bea025e000330941417db05f2812f8000d0000505f6c17ca04be00034000142fab0be2825d8000d053d).toArray⟩
theorem h113:check 3 113 d113=true:=by decide+kernel
def d114:Row:=⟨BCurve 50 37 0xa1b6a64a8b08ab448cc506efac9ad2795bc07a1a380000000024d57a40d0248000c00000000126a305b612298004000000000934d1cb2d19780010005,decode 5 1 0x76b446c3476c0036c0026c0010005,(AH 7 0x50296c0a4a020e0003400000000b017a804b8000cc232502f6c0bca025a0003406f9417ab05e2812c8000d0000505eac178a04b200034000142f4b0bc682588000d04c6).toArray⟩
theorem h114:check 3 114 d114=true:=by decide+kernel
def row (v:ℕ):Row:=match v with
 | 0=>d0
 | 1=>d1
 | 2=>d2
 | 3=>d3
 | 4=>d4
 | 5=>d5
 | 6=>d6
 | 7=>d7
 | 8=>d8
 | 9=>d9
 | 10=>d10
 | 11=>d11
 | 12=>d12
 | 13=>d13
 | 14=>d14
 | 15=>d15
 | 16=>d16
 | 17=>d17
 | 18=>d18
 | 19=>d19
 | 20=>d20
 | 21=>d21
 | 22=>d22
 | 23=>d23
 | 24=>d24
 | 25=>d25
 | 26=>d26
 | 27=>d27
 | 28=>d28
 | 29=>d29
 | 30=>d30
 | 31=>d31
 | 32=>d32
 | 33=>d33
 | 34=>d34
 | 35=>d35
 | 36=>d36
 | 37=>d37
 | 38=>d38
 | 39=>d39
 | 40=>d40
 | 41=>d41
 | 42=>d42
 | 43=>d43
 | 44=>d44
 | 45=>d45
 | 46=>d46
 | 47=>d47
 | 48=>d48
 | 49=>d49
 | 50=>d50
 | 51=>d51
 | 52=>d52
 | 53=>d53
 | 54=>d54
 | 55=>d55
 | 56=>d56
 | 57=>d57
 | 58=>d58
 | 59=>d59
 | 60=>d60
 | 61=>d61
 | 62=>d62
 | 63=>d63
 | 64=>d64
 | 65=>d65
 | 66=>d66
 | 67=>d67
 | 68=>d68
 | 69=>d69
 | 70=>d70
 | 71=>d71
 | 72=>d72
 | 73=>d73
 | 74=>d74
 | 75=>d75
 | 76=>d76
 | 77=>d77
 | 78=>d78
 | 79=>d79
 | 80=>d80
 | 81=>d81
 | 82=>d82
 | 83=>d83
 | 84=>d84
 | 85=>d85
 | 86=>d86
 | 87=>d87
 | 88=>d88
 | 89=>d89
 | 90=>d90
 | 91=>d91
 | 92=>d92
 | 93=>d93
 | 94=>d94
 | 95=>d95
 | 96=>d96
 | 97=>d97
 | 98=>d98
 | 99=>d99
 | 100=>d100
 | 101=>d101
 | 102=>d102
 | 103=>d103
 | 104=>d104
 | 105=>d105
 | 106=>d106
 | 107=>d107
 | 108=>d108
 | 109=>d109
 | 110=>d110
 | 111=>d111
 | 112=>d112
 | 113=>d113
 | 114=>d114
 | _=>default
theorem checked (v:ℕ) (hv:3+v≤117):check 3 v (row v)=true:=by
 have hvl:v≤114:=by omega
 interval_cases v
 · exact h0
 · exact h1
 · exact h2
 · exact h3
 · exact h4
 · exact h5
 · exact h6
 · exact h7
 · exact h8
 · exact h9
 · exact h10
 · exact h11
 · exact h12
 · exact h13
 · exact h14
 · exact h15
 · exact h16
 · exact h17
 · exact h18
 · exact h19
 · exact h20
 · exact h21
 · exact h22
 · exact h23
 · exact h24
 · exact h25
 · exact h26
 · exact h27
 · exact h28
 · exact h29
 · exact h30
 · exact h31
 · exact h32
 · exact h33
 · exact h34
 · exact h35
 · exact h36
 · exact h37
 · exact h38
 · exact h39
 · exact h40
 · exact h41
 · exact h42
 · exact h43
 · exact h44
 · exact h45
 · exact h46
 · exact h47
 · exact h48
 · exact h49
 · exact h50
 · exact h51
 · exact h52
 · exact h53
 · exact h54
 · exact h55
 · exact h56
 · exact h57
 · exact h58
 · exact h59
 · exact h60
 · exact h61
 · exact h62
 · exact h63
 · exact h64
 · exact h65
 · exact h66
 · exact h67
 · exact h68
 · exact h69
 · exact h70
 · exact h71
 · exact h72
 · exact h73
 · exact h74
 · exact h75
 · exact h76
 · exact h77
 · exact h78
 · exact h79
 · exact h80
 · exact h81
 · exact h82
 · exact h83
 · exact h84
 · exact h85
 · exact h86
 · exact h87
 · exact h88
 · exact h89
 · exact h90
 · exact h91
 · exact h92
 · exact h93
 · exact h94
 · exact h95
 · exact h96
 · exact h97
 · exact h98
 · exact h99
 · exact h100
 · exact h101
 · exact h102
 · exact h103
 · exact h104
 · exact h105
 · exact h106
 · exact h107
 · exact h108
 · exact h109
 · exact h110
 · exact h111
 · exact h112
 · exact h113
 · exact h114
end AWY
namespace AYP
open DZ CL
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
def d0:Row:=⟨BCurve 54 42 0x2cd543f436ce2bb51a553eb6860ce6b72f0232d47d5919f6147c8880abcaf02b9131874bc006c0003800ad006700046612c0000000000001f80130000e000300000000000004f00310002a000800000000000010000a0000900010007,decode 5 1 0x76bb569f56658740184b0000300002000010007,(AH 7 0xaed41f566015280538000cd874702a980a9a029e00034612dc1876061a81818000d1cb9706558194a063e000347b55c28760a1282788000d172b).toArray⟩
theorem h0:check 4 0 d0=true:=by decide+kernel
def d1:Row:=⟨BCurve 54 42 0x2df4e736117d2bb41a553eb6860d0792ebcaf5a67cf519f6147c888151ac56543895861d400780003800ee008b0005460dc0000000000002e401b400118003000000000000084004f00038000800000000000013c00c4000a80010007,decode 5 1 0x76bb469f3d65861018370000300002000010007,(AH 7 0x2bb407cf5c0556015280538000d1861702ad80aaa029e0003460ddc1886061e81838000d1c9f706598195a0646000347ae1c28860a16827a8000d1719).toArray⟩
theorem h1:check 4 1 d1=true:=by decide+kernel
def d2:Row:=⟨BCurve 54 42 0x2f148a77ec2c2bb31a553eb6860d286ea893b8787c9119f6147c8881fbf594ced21984eba016a409bc00e401d0d0cbb60900000000000002d605d902930003000000000000087011bb07dd00080000000000001620304815b80010007,decode 5 1 0x76bb369f246584e018240000300002000010007,(AH 7 0x2bb307c91c0556015280538000d184e702ad80aaa02a2000346091c18a6062681848000d1c85706618197a064a000347a6dc28a60a1e827c8000d1708).toArray⟩
theorem h2:check 4 2 d2=true:=by decide+kernel
def d3:Row:=⟨BCurve 54 42 0x30342db9c6db2bb21a553eb6860d48e11061a1327c3119f6147c8882a63ed3496b9d83aef01c5c0c140140e27b7113760440000000000004148828038c80030000000000000c9619890b2d0008000000000000236849c820a00010007,decode 5 1 0x76bb269f0c6583a018110000300002000010007,(AH 7 0xaec81f0c6015680538000cd83a702b180aba02a2000346045c18b6062a81858000d1c6b706658198a06520003479f9c28c60a26827e8000d16f7).toArray⟩
theorem h3:check 4 3 d3=true:=by decide+kernel
def d4:Row:=⟨BCurve 54 43 0xc54f43ee8628aec434aa7d6d0c1ad3799a54c808f7a119f6147c8883508811c40521827920110a073600d5819e78b24affc00000000000016202b4a12ae000c0000000000002320458a1e260010000000000000340069002de00010007,decode 5 1 0x76bb169ef465827017fe0000300002000010007,(AH 7 0xaec41ef46015680548000cd827702b180aba02a6000345ff9c18c6062e81878000d1c517066d819aa0656000347981c28e60a2e82808000d16e5).toArray⟩
theorem h4:check 4 4 d4=true:=by decide+kernel
def d5:Row:=⟨BCurve 54 43 0xc9cdd0f5f0e4aec034aa7d6d0c1b153113e64dacf6d919f6147c8883f66977ecac85814ac813e608620111320aa8df8afd40000000000001cc2376217c0000c0000000000002ebc5ade271e001000000000000047e88df03d780010007,decode 5 1 0x76bb069edb65814017ea0000300002000010007,(AH 7 0x2bb007b6dc0566015680548000d1814702b580aca02a6000345fa9c18e6063681888000d1c3670671819ba065e00034790dc29060a3682818000d16d4).toArray⟩
theorem h5:check 4 5 d5=true:=by decide+kernel
def d6:Row:=⟨BCurve 55 43 0x3393177f56e82baf0d2a9f5b43036ac2bc7043e41ec2233ec28f910849c4ade1553e98008d4523066a5fbe660ee859e797d6c7016c2098e00a9c1412488bd6c2000000000000090e113a075a000300000000000007800e61c628400200000000000005f20b8984f680010008,decode 5 1 0x76baf69ec265800597d6016c20000300002000010008,(AH 7 0xaebc1ec2701598055a015200034600180ada02aa000335f59c18f6063a818a8000d1c1b70679819da0662000347895c29160a3e82838000d16c2).toArray⟩
theorem h6:check 4 6 d6=true:=by decide+kernel
def d7:Row:=⟨BCurve 55 43 0x34b2bac131972bae0d2a9f5b430372df5663be129ea9233ec28f9108546941c8fed6d7ec8d4523066a5fe7ab8afcb78757c3e18199e0aba00ce3982aca40d6b00000000000000b2094f708e98003000000000000095d91c347924002000000000000079a8e8f863b00010008,decode 5 1 0x76bae69ea9657ec597c3016b00000300002000010008,(AH 7 0xaeb81ea96015a80548000cd7ec702b980ada02aa000345f0dc19160642818b8000d1c007067d819ea066a00034781dc29360a4282858000d16b0).toArray⟩
theorem h7:check 4 7 d7=true:=by decide+kernel
def d8:Row:=⟨BCurve 56 43 0x1ae92f01862315d686954fada180debefc15ce1047a408cfb0a3e4410bd8eb057129a2fb11a8a460cd4a010f10711152717affc01c7a0be6007b00e4f660dab4f000000000000035a0643e2a7a000c00000000000016e02b0092438004000000000000097811f107a500010008,decode 5 1 0x76bad69e90657d8597af0169e0000300002000010008,(AH 7 0x2bad07a418056a0156000335f6180aea02ae000335ebdc19260646818d8000d1be57068581a0a06720003477a5c29560a4a82878000d169e).toArray⟩
theorem h8:check 4 8 d8=true:=by decide+kernel
def d9:Row:=⟨BCurve 56 44 0xdbc805139bd4aeb01a553eb6860383188a4ab26f9e76119f6147c8821a495ba384f0d5f111a8a460cd4a03a36832572c6d79b8b40fab068900484685b9386d5a300000000000000fe49d838c790003000000000000036de66632b5b00080000000000000b8a95ae093480010008,decode 5 1 0x76bac69e76657c45979b0168c0000300002000010008,(AH 7 0x2bac079d9c0576015a80558000d17c4702bd80aea02b2000345e6dc1946064a818e8000d1bca7068981a1a0676000347729c29760a5282898000d168c).toArray⟩
theorem h9:check 4 9 d9=true:=by decide+kernel
def d10:Row:=⟨BCurve 56 44 0xe046921b0690aeac1a553eb686038b35243e2c9e1e5c119f6147c8821ce0e13c278e65ec11a8a460cd4a0637bff39d06697879881119071f0053e09a65410359e8000000000000129622530e790003000000000000040d0783332c500080000000000000dd219c68ae980010008,decode 5 1 0x76bab69e5c657b0597870167a0000300002000010008,(AH 7 0x2bab079718057a0156000335ec180afa02b2000335e1dc1956065281908000d1bae7069181a3a067e0003476adc29960a5a828c8000d167a).toArray⟩
theorem h10:check 4 10 d10=true:=by decide+kernel
def d11:Row:=⟨BCurve 56 44 0xe4c51f22714caea81a553eb686039351be31a6cc9e41119f6147c8821f7866d4ca2bf5e711a8a460cd4a08cc17b4e2e065773a5c128707b500604eb07f4a2f59a0000000000000157ca77e109e800300000000000004b968b713ac50008000000000000104e9e3a8cc400010008,decode 5 1 0x76baa69e416579c59773016680000300002000010008,(AH 7 0xaea81e416015e80568000cd79c702c180afa02b6000345dcdc1976065a81918000d1b927069981a5a0686000347631c29b60a62828e8000d1668).toArray⟩
theorem h11:check 4 11 d11=true:=by decide+kernel
def d12:Row:=⟨BCurve 56 44 0xe943ac29dc08aea41a553eb686039b6e582520fb1e27119f6147c88221fe4d0c250105e211a8a460cd4a0b4ec6d1c7ed1975eb3013f5084b006d90c80753f1595400000000000018982d0492e9800300000000000005730a01d435b00080000000000001300230a0ec400010008,decode 5 1 0x76ba969e27657885975e016550000300002000010008,(AH 7 0xaea41e276015e80568000cd788702c580b0a02b6000345d79c1986065e81938000d1b767069d81a6a068a0003475b5c29d60a6a82908000d1655).toArray⟩
theorem h12:check 4 12 d12=true:=by decide+kernel
def d13:Row:=⟨BCurve 56 44 0xedc2393146c4aea01a553eb68603a3709cd9e4a39e0b119f6147c8822495d2a4c79e95dcd1a8a460cd4a0de31e930dc71574ac04156308e1007ba6e0fd5e49590c0000000000001be8b2e6955a00030000000000000639eb6374c87000800000000000015e6a83510e980010008,decode 5 1 0x76ba869e0b657735974a016430000300002000010008,(AH 7 0x2ba80782dc0586015e80568000d1773702c580b0a02ba000345d29c19a6066681958000d1b5a706a581a8a0692000347535c29f60a7282928000d1643).toArray⟩
theorem h13:check 4 13 d13=true:=by decide+kernel
def d14:Row:=⟨BCurve 56 44 0xf240c638b180ae9c1a553eb68603ab8d36cd5ed21df0119f6147c882271bb8dc2273a5d7d1a8a460cd4a1065cdaff2d3c9735cd816d10977008a90fb61693758c00000000000001f6e392417f00003000000000000070e0cdbf5649000800000000000019022dbb933480010008,decode 5 1 0x76ba769df06575f59735016300000300002000010008,(AH 7 0xae9c1df06016280568000cd75f702c980b1a02be000345cd5c19b6066a81968000d1b3d706ad81aaa069a0003474b9c2a160a7a82948000d1630).toArray⟩
theorem h14:check 4 14 d14=true:=by decide+kernel
def d15:Row:=⟨BCurve 56 44 0xf6bf53401c3cae981a553eb68603b38f7b82227a9dd4119f6147c88229a19f137d48b5d291a8a460cd4a12fa257138adc5720dac183f0a0d009a4f173374bb58780000000000002328bfbd1aab800300000000000007ef6e6b560a100080000000000001c52b39d95a500010008,decode 5 1 0x76ba669dd46574a597200161e0000300002000010008,(AH 7 0x2ba6077518058a015e000335d2980b2a02be000335c81c19d6067281988000d1b21706b581aca06a2000347435c2a360a8282968000d161e).toArray⟩
theorem h15:check 4 15 d15=true:=by decide+kernel
def d16:Row:=⟨BCurve 56 44 0xfb3de04786f8ae941a553eb68603bb91c036e6231db8119f6147c8822c27854ad81dc5cd51a8a460cd4a157cd48e1dba7970be8019ad0aa300aae1347380d5582c000000000000271846b19d8c800300000000000008de101196b8f00080000000000001fd839db183b00010008,decode 5 1 0x76ba569db8657355970b0160b0000300002000010008,(AH 7 0x2ba5076e1c0596016280578000d1735702cd80b2a02c2000345c2dc19f6067a819a8000d1b04706b981ada06aa0003473b5c2a660a8e82988000d160b).toArray⟩
theorem h16:check 4 16 d16=true:=by decide+kernel
def d17:Row:=⟨BCurve 56 44 0xffbc6d4ef1b4ae901a553eb68603c39404eba9cb9d9b119f6147c8822ead6b8232f2d5c811a8a460cd4a17ff83ab02c72d6f6f541b1b0b3900bc4753218d8557e00000000000002b3cce01a093000300000000000009d9f1ceb771300080000000000002392c0741af680010008,decode 5 1 0x76ba469d9b65720596f6015f80000300002000010008,(AH 7 0xae901d9b6016680578000cd720702d180b3a02c2000345bd9c1a06067e819b8000d1ae6706c181afa06b2000347331c2a860a96829b8000d15f8).toArray⟩
theorem h17:check 4 17 d17=true:=by decide+kernel
def d18:Row:=⟨BCurve 56 45 0x20875f4acb8e15d181a553eb68603cb9649a06d741d7e08cfb0a3e4411899a8dcc6e3f2e1646a2918335286a08cb1f9f4f85b85f5b61a8bbdbcbebe060813422af2bee1e23f703f94913b460bdbe4e3d8140e4485e7806740b99ecd659c4a0000000000000be5956b48efc000c00000000000015c627457065a0010000000000000278247689dd78001000a,decode 5 1 0x76ba369d7e6570b596e1555e514e3d00e25000030000200001000a,(AH 7 0xae8c1d7e6016680588000cd70b702d180b3a02c6000345b85c1a260686819d8000d1ac9706c981b1a06ba0003472adc2aa60a9e829d8000d15e5).toArray⟩
theorem h18:check 4 18 d18=true:=by decide+kernel
def d19:Row:=⟨BCurve 56 45 0x211730ebb8e595d101a553eb68603d37e39167a969d6008cfb0a3e44119d3cc47d06a3adea46a29183352874138793338255b2e080b4561897dcdb144fb671eeae9412caf1375ffb63b34453bad9ce3c87e0efb86328070c7ca63d4539c480000000000000d09376d09c42000c00000000000017f2eb1b31fba00100000000000002ba6ceb8a0de0001000a,decode 5 1 0x76ba269d60656f5596cb555d214e3c00e24000030000200001000a,(AH 7 0x2ba207581c05a6016680588000d16f5702d580b4a02ca000345b2dc1a46068e819f8000d1aab706d181b3a06be000347229c2ac60aa6829f8000d15d2).toArray⟩
theorem h19:check 4 19 d19=true:=by decide+kernel
def d20:Row:=⟨BCurve 56 45 0x869c0a3298f4574206954fada180f6e01f72cf8fc750c233ec28f91046c5afd8df7530b7011a8a460cd4a1f75e85d5120016b686981c0dd557b7248a1943c192b7d0dddef9def0f5f8ba33cc5f9238ee258291c9f8dc04d65c900271e711c45fcfe2c3778644f90894d7ecca28e80fb2867d807ab8dbdfdb8c993e0000000000000e3a1985aaa1e000c0000000000001a3a2f1eb3a46001000000000000030005664240a0001000c,decode 5 1 0x76ba169d43656e0596b6555be14e3b18e2310ca200c9f000030000200001000c,(AH 7 0xae841d43701698059a0162000345b8180b5a02ca000335ad9c1a66069681a18000d1a8d706d981b5a06c60003471a5c2ae60aae82a28000d15be).toArray⟩
theorem h20:check 4 20 d20=true:=by decide+kernel
def d21:Row:=⟨BCurve 56 45 0x2236d42d939495d001a553eb68603e3686d414b619d2408cfb0a3e4411c50e2ce875b0ad9446a29183352887e25de8d8b2d5a822cb59b0d211feb60b04507696ad5c5c248bb8183f98858e3ecdcc4e3a8e0cefbd70a73ea04f5176ac09c451ab8e5713e0e7420a3ada948532863f229ad49afc57068fa47d4f8640c7fdba442b338f72f59b2d7a10c3b952106986c8808513ee12e310985c0000000000000f783bb52b890000c0000000000001c9bf34ff55fe0010000000000000348ede6b275b8001000e,decode 5 1 0x76ba069d24656ca596a0555ab14e3a18e2210ca12cc8108c3b00c2e000030000200001000e,(AH 7 0xae801d246016a80598000cd6ca702d980b5a02ce000345a81c1a86069a81a38000d1a6f706e181b7a06ce00034711dc2b160aba82a48000d15ab).toArray⟩
theorem h21:check 4 21 d21=true:=by decide+kernel
def d22:Row:=⟨BCurve 57 45 0x458d4b9d01d82b9f034aa7d6d0c03eb505cb758841d0508cfb0a3e4408ec5831cc870a96b4235148c19a9224699df2ba6c2168a8fc2b178bb3c1f439b936a7ae1597901a2b1f0e8c1b2b84836e3a2ce3992b93b08630bbe032bbbe22a88e2191f945abb713bb87e51e88a128ca09487d415c383a8f69a5b108608c8094c50e2a7db3a748f5cf2754e8c3a95f5f804a23371eeb39cb0e9f0c1696a986851d934743f85ea25648b4f9bc112087138047ec807e756fcabe0000000000000430e77ee31e6000300000000000003e306f5dee5c40020000000000000395266cdaad280010010,decode 5 1 0x76b9f69d05656b45968a5559714e3918e2110ca02cc8008c3a0cc1624b4f00abe0000300002000010010,(AH 7 0xae7c1d056016a80598000cd6b4702dd80b6a02d2000345a29c1a9606a281a58000d1a50706e981b9a06da000347095c2b360ac282a68000d1597).toArray⟩
theorem h22:check 4 22 d22=true:=by decide+kernel
def d23:Row:=⟨BCurve 57 45 0x46aceededc872b9e034aa7d6d0c03f3384c2d65a69ce608cfb0a3e4408f6294d24d33cd69e235148c19a9226ec4d0f9f78d56749457fc2e2e2c4118d5acfe181958494afc4c71a0c3ccc6badb5256ce3897658653557bdcb3d7cb7530c8e209696189ecf23da0553153fd310c9f994701766043c70a0abdfd3074c7f998ea7cca4fbc5945d294e96d0c399abf91a6c97b98d8799f57cdf4c159b7827802ef362306d6552b260b719d7cd0c5e6ab51164a18ef5f70abda2611d7875e804d840a4ef97cca6900000000000004871016335cd80030000000000000435df877721e400200000000000003e4aef8bae6f00010011,decode 5 1 0x76b9e69ce66569e596745558414e3818e2010c9f2cc7f08c390cc1524b7128abd00a690000300002000010011,(AH 7 0xae781ce67016d805aa0166000345a7980b7a02d20003359d1c1ab606aa81a68000d1a32706f181bba06e2000347009c2b560aca82a98000d1584).toArray⟩
theorem h23:check 4 23 d23=true:=by decide+kernel
def d24:Row:=⟨BCurve 57 45 0x47cc9220b7362b9d034aa7d6d0c03fb203ba372c91cc708cfb0a3e4408fffa687d1f6f1688235148c19a92295d538823b84165e98ed46e3a12462ebc4555c369557099455e6f25945e6b0e62c20f90e379c11d19e47ebfb622bd7743644e1f9b32eb91e73bf88072cf9019c0c9e9e062ed6fd03e51b231d55da20c7e9e58416ecc4be3dd5fed83bf1cc389f892b48f0cbbfc7e1e1ef0468c14a046c87b404b7d1a78ceb7af88b91a25c37863e9b63da5925668244abca90128e87a9805350947afdaf4a5000000000000004e088b33b9da8003000000000000048c081ec7605c0020000000000000437878a5323100010011,decode 5 1 0x76b9d69cc7656885965e5557014e3718e1f10c9e2cc7e08c380cc1424b9128abc00a500000300002000010011,(AH 7 0xae741cc76016e805a8000cd688702e180b7a02d6000345979c1ad606b281a88000d1a13706f981bda06ea000346f7dc2b860ad682ab8000d1570).toArray⟩
theorem h24:check 4 24 d24=true:=by decide+kernel
def d25:Row:=⟨BCurve 57 45 0x48ec356291e52b9c034aa7d6d0c0403082b197feb9ca808cfb0a3e440909cb83d56ba15672235148c19a922bce5a00a7f7ad6489d829199141484bc678c84649955c9ddaf817311480076ca2948798e36a0be1ce93a5c1a0e27dfdf3afce1e9fcfbe84ff4c16f9444d791144c9da2c55c3799cc0329e3791ab3e4c7da321db10f3940223fe1bc66d2cc37a452c4eb1813e700b8fa054770c13a515697651ab98021a9ad1a3a4bb0a73b9e4696937dfdd85dd96a3cabbafa134587f48059521f0282074a4f000000000000053d5155fbe0d000300000000000004e580bbcfa12c002000000000000048db021a361880010011,decode 5 1 0x76b9c69ca865672596485555c14e3618e1e10c9d2cc7d08c370cc1324bb028abb00a4f0000300002000010011,(AH 7 0xae701ca86016e805a8000cd672702e580b8a02da000345921c1af606ba81aa8000d19f37070181bfa06f2000346ef1c2ba60ade82ae8000d155c).toArray⟩
theorem h25:check 4 25 d25=true:=by decide+kernel
def d26:Row:=⟨BCurve 57 45 0x4a0bd8a46c942b9b034aa7d6d0c040ad5c550d6881c8a08cfb0a3e4409135621a898b1965b235148c19a922e2db7d4cb69d1631a217dc4e870ca68abf527713dd547a27091bf3c9ca1a1866d2cfe78e35a56a68342ccc38b7cbe4b63eece1da46c91781764356fc78efb1d8cc9ca7848998368c21364bd14b5c08c7ca7eb74b31ae4206837b417019cc36a91c5e8d3f640e274251e11970c12a9e40a71630bb2e752c9a063c0bcdac1b0506ee83981eedf900f4f4abab6413fc883f805f88a9e58684ca4e000000000000059d69fe7426500030000000000000542495e8fe45400200000000000004e728beaba2580010011,decode 5 1 0x76b9b69c8a6565b596315554714e3518e1d10c9c2cc7c08c360cc1224bcd28aba00a4e0000300002000010011,(AH 7 0xae6c1c8a70171805ba016a00034596d80b9a02de0003358c5c1b1606c281ac8000d19d37070d81c1a06fa000346e61c2bd60aea82b08000d1547).toArray⟩
theorem h26:check 4 26 d26=true:=by decide+kernel
def d27:Row:=⟨BCurve 57 45 0x4b2b7be647432b9a034aa7d6d0c0412a35f882d249c6d08cfb0a3e44091ce0bf7bc5c1d644235148c19a92309ebe4d4fa93d61aa6ad2703f9fcc856cba733d2b1533a7062b67481cc3395bc28b0344e34aa16b37f1f34575f17e5f90face1ca909646b2f7453e3fc9415dab0c9bac43b6f8d34c3f405c25e8036cc7bacb50e5542343eaa0cb6754c18c35ade5f82f66b435841418b38980c11aeb2ab6c746bcdca215b23efdcbe9b0fa6bc7467bb23d99f6dd74e8ab9bce14b3888a8065f435240b27ca4d0000000000000600d2aca46e2800300000000000005a262070829d40020000000000000543f1616be5800010011,decode 5 1 0x76b9a69c6d656445961a5553314e3418e1c10c9b2cc7b08c350cc1124be928ab900a4d0000300002000010011,(AH 7 0xae681c6d60172805b8000cd644702e980b9a02de000345869c1b3606ca81af8000d19b37071581c4a0706000346dd1c2bf60af282b38000d1533).toArray⟩
theorem h27:check 4 27 d27=true:=by decide+kernel
def d28:Row:=⟨BCurve 57 45 0x4c4b1f2821f22b99034aa7d6d0c041a70f9bf83c11c5008cfb0a3e4409266b5d4ef2d2162d235148c19a92330fc4c5d3e8a9603ab4271b96cf4ea208c8abb12bd51fab9bc50f53a4e4ceeca2af06e0e33aec2feca11a476040be3a81214e1bada6375e47847255e35cc97aa4c9ab102e45970145d481476f0dae0c7ab17ea7f7697c5ce97d22e11c68c34b2af91d18dfc5d0fffe8092ca4c10b3814c6785c3e8aa864f5c1d14c04b5d9d2879e6bcc59dc576e97a4ab8bbf9825876f3d535a554b949d8a4cc38156a88d5806c94c0be0ff04a0500000000000006678b608cb8580030000000000000605cab53871ac00200000000000005a40a09e42b000010012,decode 5 1 0x76b9969c506562d596035551f14e3318e1b10c9a2cc7a08c340cc1024c0428ab850a4c00a050000300002000010012,(AH 7 0x2b9907141c05d60172805b8000d162d702ed80baa02e200034580dc1b5606d281b18000d19937071d81c6a070e000346d41c2c260afa82b58000d151f).toArray⟩
theorem h28:check 4 28 d28=true:=by decide+kernel
def d29:Row:=⟨BCurve 57 45 0x4d6ac269fca12b98034aa7d6d0c04223e93f6da5d9c3208cfb0a3e44092ff5fb221fe25616235148c19a92356f2299f75acd5ecafd7bc6edfe50be801fd0c626150ab0315eb75f250662390d989870e32b36f4a15041494a6a7ddc313b8e1ab2430a515f9c90c57be9162f4cc99b5c211ba0cd47b4d74c46580bcc79b648419990cc7b2688f95ad308c33b84fed629724038881a6494130c0fbab93947f65be673b51ab4866cab7c116f1a58953eff3c8b6e4449ca4bca21621892080736a4cb394de4a0400000000000006d1941a2d04e0003000000000000066c836920bbdc002000000000000060772b81472d80010011,decode 5 1 0x76b9869c3265616595ec5550a14e3218e1a10c992cc7908c3324c0f28ab750a4b00a040000300002000010011,(AH 7 0xae601c3260176805b8000cd616702f180bba02e60003457b1c1b7606da81b38000d19727072581c8a0716000346cadc2c460b0682b88000d150a).toArray⟩
theorem h29:check 4 29 d29=true:=by decide+kernel
def d30:Row:=⟨BCurve 57 45 0x4e8a65abd7502b97034aa7d6d0c042a0c2e2e30fa1c1308cfb0a3e4409398098f54cf295ff235148c19a9237ce806e1accf15d5b46d072452dd2dad2bfe2833314f5b4c6f85f6aad27f341034828c8e31b81b955ff684b346ebd44a1498e19b6dfdd4477acaf32c638fb94e0c98ba813f1aa99c99507d0e4656a0c78bb11db3bb81499613039e20f80c32bd1e8e5da8841e64135feb314cc0ebf98a0084e54008b2440af6a5cab6c63460f29bb40aaf5d9b380194a4ad0c16d8896b807a74d90499f1ca03000000000000073eecd98553c000300000000000006d68c22c10864002000000000000066e2b6bfcbd080010011,decode 5 1 0x76b9769c13655ff595d5554f514e3118e1910c982cc7808c3224c0e28ab650a4a00a030000300002000010011,(AH 7 0x2b970704d805da01720003357fd80bca02ea000335755c1ba606e281b58000d19517073181cba0722000346c15c2c760b1282bb8000d14f5).toArray⟩
theorem h30:check 4 30 d30=true:=by decide+kernel
def d31:Row:=⟨BCurve 57 45 0x4faa08edb1ff2b96034aa7d6d0c0431bf7326d1109bf408cfb0a3e440942c4b9435ae0d5e7235148c19a923a2dde423e3f155bdb90251d9c5d54f700a8e0e4c694e0b95c9207762d49820483bd4720e30bcc7e0aae8f4d1e4d7c73d14b0e18bb7cb0378fbccd9dc24c79dd44c97bf406c7b465cb7512d5492faf8c77bfdb74dddf64b79972e4773240c31c1ed2f58b9dc393d3b7c41c294c0dc47806c8a6441aa029c95ef124ab5cb51d03fae1425686401b480c0a49d76178f89b68081b465b11f2aca0200000000000007af959e95a4f80030000000000000743e4e219574400200000000000006d834259d09900010011,decode 5 1 0x76b9669bf4655e7595bd554e014e3018e1810c972cc7708c3124c0d28ab550a4900a020000300002000010011,(AH 7 0x2b9606fd1c05e60176805c8000d15e7702f580bca02ea0003456f5c1bc606ee81b78000d192f7073981cda072a000346b81c2c960b1a82be8000d14e0).toArray⟩
theorem h31:check 4 31 d31=true:=by decide+kernel
def d32:Row:=⟨BCurve 57 45 0x50c9ac2f8cae2b95034aa7d6d0c04398d0d5e27ad1bd508cfb0a3e44094c4f571687f115d0235148c19a923c8d3c1661b1395a6bd979c8f38c571309dacbe75414cbbdf22baf81ad6b0e838ef82bd8e2fc1742bf5db5cf0806bb69be1ace17c019832aa7d4ec067023913a54c96c3ff99dbe31cd54f85974b9e8cc76c4a50e8006b4d5cf50f91a0b14c30c6bbd053cb3c5413f9fb4d4ab0c0cc9576d88fe3c34b2c5b4c36d14ab4d06f3f8cc07c401edbea59ea24a48d584fafb3aa4310e97cb28eb10a01de018468a01808928f2b92489499a00000000000008238e695df88800300000000000007b48da729a87c00200000000000007458ce4f558700010012,decode 5 1 0x76b9569bd5655d0595a6554cb14e2f18e1710c962cc7608c3024c0c28ab450a484ca010099a0000300002000010012,(AH 7 0xae541bd56017a805d8000cd5d0702f980bda02ee000345699c1be606f681ba8000d190d7074581d0a0736000346ae5c2cc60b2682c08000d14cb).toArray⟩
theorem h32:check 4 32 d32=true:=by decide+kernel
def d33:Row:=⟨BCurve 57 45 0x51e94f71675d2b94034aa7d6d0c0441405256c7c39bb508cfb0a3e44095593776495df55b8235148c19a923eec99ea85235d58ec22ce744abbd92eee55a391f3d4b6c287c5578d358c98be24f90f50e2ec6207740cdcd0f19a7a266e03ce16c4b6561dbfe50a6ccfbe414854c95c8bec73c7fe4f34b85d670721cc75c96ea8222dfcf402ca77ca69c8c2fcb8a714edc9c6ee84edd0d9eccc0bce36d449562c4ec2f802dc8be4ab3d58caed9d2dc5ad2c55527edb0a47dab66c3c906bcd954c8d57d7c8a00e4a18fd8a4c8090d2801caa0d4873000000000000089ad739de4e7000300000000000008288671f1fc0c00200000000000007b635aa05a9a80010012,decode 5 1 0x76b9469bb5655b85958e554b614e2e18e1610c952cc7508c2f24c0b28ab350a474ca00008730000300002000010012,(AH 7 0xae501bb56017a805d8000cd5b8702fd80bea02f2000345639c1c0606fe81bc8000d18eb7074d81d2a073e000346a4dc2cf60b3282c38000d14b6).toArray⟩
theorem h33:check 4 33 d33=true:=by decide+kernel
def d34:Row:=⟨BCurve 57 45 0x5308f2b3420c2b93034aa7d6d0c0448f3974f67da1b9508cfb0a3e44095e911a2d84ab95a0235148c19a92413a4f1a47c839575c6c231fa1eadb4aae1967dd8e94a0c71d5eff98b5ae20b445bf80cce2dcaccc28bc03d2db08b8a9dde08e15c9532910d7fd28d0e11c8a6af8c94cd7df49d1ca511452e1201142cc74ce3841c4554d1233df6088aebcc2ed0591249edf489ba3a21829420c0ad3163b09ae1c68d0c0b3aa76b8ab2daaa1e26e53c758420421eb374a46dfe7dd7de63384ef17a3e666e89ffeb419b48a978098b10ddbafb6c7970000000000000915701016a6b0003000000000000089fcf427251f4002000000000000082a2e74cdfd380010012,decode 5 1 0x76b9369b95655a059575554a014e2d18e1510c942cc7408c2e24c0a28ab250a464c9ff007970000300002000010012,(AH 7 0x2b9306e55c05f6017a805d8000d15a07030180bfa02f60003455d5c1c36070a81bf8000d18c87075981d5a074a0003469b1c2d260b3a82c68000d14a0).toArray⟩
theorem h34:check 4 34 d34=true:=by decide+kernel
def d35:Row:=⟨BCurve 57 45 0x542895f51cbb2b92034aa7d6d0c04508c8709516a9b7408cfb0a3e440967d53a7b9299d587235148c19a924388044a0a6d1555dcb577caf91a5d66492618d13a948acbb2f8a7a43dcfa665f14bf100e2ccf790dd6b2ad4c45176f40db0ce14cdeffc03f00d4732a43e6c3e9cc93d23d21fdb9652f3c7e49fdb57cc73d301db667c9530628fb354799cc2dd527b344ff54a489bbc8ac8040c09d7f5a1ca061482dc1fc72d56a8ab1dfc78d73f79c9032ecb13e3b68a45e5194ebf3bfb931d13ab3966d09fef1e1a6b8ae280a0c49bf63585c787000000000000099358ec070148003000000000000091a6818aaaa3400200000000000008a177454e53200010012,decode 5 1 0x76b9269b74655875955d5548a14e2c18e1410c932cc7308c2d24c0928ab150a454c9fe007870000300002000010012,(AH 7 0x2b9206dd1805fa017a00033561d80c0a02fa000335575c1c56071281c18000d18a57076581d7a0756000346911c2d460b4682c98000d148a).toArray⟩
theorem h35:check 4 35 d35=true:=by decide+kernel
def d36:Row:=⟨BCurve 57 45 0x55483936f76a2b91034aa7d6d0c04583fcc01f1811b5208cfb0a3e440970d2dd448166156f235148c19a9245e7621e2ddf39544cfecc7650495f81bf7bb665e25475d048924fafbdf129d3279def40e2bd4255921a51d6ad74b504fd74ce13d28ccef7081d65921923e6f50cc92d6fc4f5e562d4d31767e6686b8c72d7cb7508a3e54e8edb702e2ab0c2cd9f6544010b4bf56d3d28b3860c08dcd5088a5e049ce5153d64d980ab0e4e4fcc109fcaadf2aa2868590a44ea4ac00091c3a7d7c2233393349fdee73a186fe93a0fa6e9e4daa4c786f881b228b2d80a90d2a6c3b7a47680000000000000a1491cdaf5e38003000000000000099850f49b04cc002000000000000091c101b86ab600010013,decode 5 1 0x76b9169b526556f595445547514e2b18e1310c922cc7208c2c24c0828ab050a444c9fd04786007680000300002000010013,(AH 7 0x2b9106d49c0606017e805e8000d156f7030580c0a02fe000345511c1c86071a81c48000d18827076d81daa0762000346871c2d760b5282cc8000d1475).toArray⟩
theorem h36:check 4 36 d36=true:=by decide+kernel
def d37:Row:=⟨BCurve 57 45 0x5667dc78d2192b90034aa7d6d0c045fd8bbbbdb119b3008cfb0a3e440979d0800d70325556235148c19a9248236ea98fb6cd52bd482121a778e19d111a40a29b145ed4de2bf7bb4612aafbe8b5ec30e2ad8d1a46c97858967272dcaa084e12d729a1ea203583ef3fccfac014c91dbbb7cbef2ed6b2416af3b2680c71dc950eaacb356cb8c2971591d8c2bdec4f53b220cda21823f1e91c0c07e1b46f4ab5fcb6eba11651516caafea026c0e1c5cc588da15f791eca43ef7c3141e78bbc8fd80ea4ada49fcf3acf6f5adfbb5459674f04a5c785ff21bd98b7880b18ab93dc19447670000000000000a991ab50fbd800030000000000000a1989d64361bc0020000000000000999f8f77705f80010013,decode 5 1 0x76b9069b30655565952b5545e14e2a18e1210c912cc7108c2b24c0728aaf50a434c9fc04785007670000300002000010013,(AH 7 0xae401b3060182805f8000cd5567030980c1a02fe0003454adc1ca6072681c68000d185e7077981dda076e0003467cdc2da60b5e82cf8000d145e).toArray⟩
theorem h37:check 4 37 d37=true:=by decide+kernel
def d38:Row:=⟨BCurve 57 46 0x15e1dfeeab320ae3c06954fada1808cee356eb8944361a08cfb0a3e440982ce22d65efe953d11a8a460cd49253891eca92dd4a893645d733fa9f8ee0f806de013e5121b2e78b3f8d8c6853c06926ee71c52dd7defb789f5a7f4ab07b19b3ce116de33a6e9c22d1250c1cd39e14648381eaa87e3eb624517b71ef16231c1c2bd5099e4fb15c08a5014fde9854e3939636336cf4e9c70e66e1e0c067349eb0586f66877e1a8f936265573bc7f6d6cbb1380bfec2e4621a2909e95b45067aa7a28aaadb196c513f6f8e64c645d63c98e21d5c4b0a878482e0e4845e1c05d1ea43563e9e3b300000000000002c83ce88a07c8000c000000000000153c257b4782080040000000000000a1b31d91f62e80010013,decode 5 1 0x76b8f69b0d6553d595125544814e2918e1110c902cc7008c2a24c0628aae50a424c9fb04784007660000300002000010013,(AH 7 0xae3c1b0d60182805f8000cd53d7030d80c2a0302000345449c1cd6073281c98000d18397078581e0a077a000346725c2dd60b6a82d28000d1448).toArray⟩
theorem h38:check 4 38 d38=true:=by decide+kernel
def d39:Row:=⟨BCurve 57 46 0x1629c8bf21ddcae3806954fada1808dde08be1ef5935d408cfb0a3e44098bcbc59f4dcad52311a8a460cd49265f6c848a8042a7cb76b29e1575d974d18c86c185350c9bc12be8fa49cab4d00166e01c9c50e22a3b027c65c67fd6de049530e107031a3e8282ae0515134f64d84647b94e75e00b1d69c093c18a251d31bdcc5083de339b520ac6461aa479852e862373144cd0fafa24063fe00c0575b99e65b2f27578bdf8243e1a556bd0f52aa10493eb52360d506492905f3be27892637cbf0747fd759713f4fe1fa1d30cd3ddd410c0cafac87838630ea3c6074061926bf9a71c63b280000000000002eb07253e20c6000c000000000000164bd7557845480040000000000000a9fbac07fc2300010013,decode 5 1 0x76b8e69aea65523594f95543214e2818e1010c8f2cc6f08c2924c0528aad50a414c9fa04783007650000300002000010013,(AH 7 0xae381aea7018680608000cd5237031180c3a03060003453e5c1cf6073a81cc8000d18147079181e3a078600034667dc2e060b7682d58000d1432).toArray⟩
theorem h39:check 4 39 d39=true:=by decide+kernel
def d40:Row:=⟨BCurve 57 46 0x1671b18f98898ae3406954fada1808ed126b55c27a358a08cfb0a3e44099482eae31d75150a11a8a460cd49277d72ca3b6c0ca6fb8907c8eb4199fb8a6adacb359506dc53df1dfbb9cee41b6d9403161c4ee6d6864d6ed5e508aab0c38e60e0f72800d61b436ef7c6f2ee5873a6473a7e4138324d713b79cb104c7d31b9d5e3b722822b8e5039103b5709850ed30d82c56252a7313d515bb70c04782951c5deea82786578a9978e5563e56ae7d54e1455da45f4fdb052901fe210a0bd1c7f5510d0b8322b93f30358f741bc3bf217633602ed907828980eff462cc06620b3ebaa61a3b2000000000000030ea563603a5a000c0000000000001762293b190d380040000000000000b2793ad9823d00010013,decode 5 1 0x76b8d69ac56550a594df5541b14e2718e0f10c8e2cc6e08c2824c0428aac50a404c9f904782007640000300002000010013,(AH 7 0xae341ac56018680608000cd50a7031580c4a030a00034537dc1d26074681ce8000d17ef7079d81e6a07920003465d5c2e360b8282d88000d141b).toArray⟩
theorem h40:check 4 40 d40=true:=by decide+kernel
def d41:Row:=⟨BCurve 57 46 0x2d7334c01e6a95c600d2a9f5b43011f81f4098511e6a84119f6147c88133a74204dda3ea9e0235148c19a925136f21fd8afad4c5736b9e7821af5047436d3fdd40a0239cd24a5fa55a6263c9633cbc63899d705a330c28c071e4cffdd0d91c1ce99cedb6807dfd4ccc154232f4c8d775c1920b2fef16b93a762ffa8636bbeedd4cda1979521c55cefabb309de3fef24ecf0a8a683798f8df21806f5320a4c15c51eedb05512ae04aab7f3c14a132f2980b037ca9c09e51fc1107d91cfab03d58e8fc3990327e211249960d7580cb0326ad98848f030c5fe94a1fc3f065692e0a17d87638cd0f5ac652406ac97c0b6db9a38a000000000000033317a2f05484000c000000000000187f1b2c29d9d80040000000000000bb2bca06887c80010014,decode 5 1 0x76b8c69aa1654f0594c55540414e2618e0e10c8d2cc6d08c2724c0328aab50a3f4c9f80478148763007140000300002000010014,(AH 7 0xae301aa17018a80618000cd4f07031980c5a030e000345315c1d56075281d18000d17c9707a981e9a079e000346525c2e660b8e82dc8000d1404).toArray⟩
theorem h41:check 4 41 d41=true:=by decide+kernel
def d42:Row:=⟨BCurve 57 46 0x2e0306610bc215c580d2a9f5b430121619aa851d4869ec119f6147c88134be26ad5799329ac235148c19a925372feab3a87414ab75b643d2db27611c13c68b5bb49f6baf28b0ffd35ae83b133f0f4eb3895e05e39c6a75c442694970a9871c1aee39c0a998961b9e6b90526bf8c8c79bbafd1015f005f07b6db4da66363d2143b563ed80d9986419f8193099ed9c3444f1cabfe5744d2fdf61804fa11710c6dbd38e82c1b8721ecaaa81cacc47bc22a55976fbc82c4a51f425cd9e2251d0900555af4893427de1b97443e3628352c657e1086d0f0111c049c9537be605cc952911547629020fb64677c06f8cc458f124636d00000000000003585de3ee6f44000c00000000000019a2ad28aaab280040000000000000c413598f0ee180010014,decode 5 1 0x76b8b69a7b654d6594ab553ed14e2518e0d10c8c2cc6c08c2624c0228aaa50a3e4c9f70478048762006da0000300002000010014,(AH 7 0x2b8b069ed8062a018600033535980c6a03120003352adc1d86075e81d48000d17a2707b981eca07aa000346475c2ea60b9a82df8000d13ed).toArray⟩
theorem h42:check 4 42 d42=true:=by decide+kernel
def d43:Row:=⟨BCurve 57 46 0x2e92d801f91995c500d2a9f5b4301233aabf770f5a695c119f6147c88135cc3ba52daa3a976235148c19a92559d62923b918d4907800e92d94a371efbe673c1aa49eabc17f17a0017b6e094b45f9db43891e9b6d05c8c3c812a2c27108639c18f2d6939cb0a639edbccefb5618c8b7c1b46814fbf0f514fc4899b42635be53aa1dedbf88607b4ce856fb3095f739763b148af55dddc6d077a1802fef0d7ccc5ad52e03e44b038dcaa9845983ee4556b2a6a33bfb0cfa51ec3a936327a8f0e2a76030334e927da2609ef1b95085da35fa5ab4ce0eff1720aa488733f9842d70e092c87619371011c69d40746a8cd434a1e36c800000000000037e78265a8a9a000c0000000000001accdf309b81280040000000000000cd2fe973156c00010014,decode 5 1 0x76b8a69a57654bb59490553d514e2418e0c10c8b2cc6b08c2524c0128aa950a3d4c9f60477f48761006d90000300002000010014,(AH 7 0xae281a577018d8062a01860003452ed80c7a0316000335241c1db6076a81d78000d177b707c581f0a07ba0003463c1c2ed60baa82e28000d13d5).toArray⟩
theorem h43:check 4 43 d43=true:=by decide+kernel
def d44:Row:=⟨BCurve 57 46 0x2f22a9a2e67115c480d2a9f5b43012513bd469016c68d0119f6147c88136da509d03bb42940235148c19a9257d96f1d9d69214757a4b8e884e1b82c2434f51e1809df3d3d57e402f7bf3ce7177faa09388df30f66f2711cbe2913afee7269c16f773668fc8b6583abfd13d2308c8a7e7add319e231e426bd06e00c86353f86108677938fe6c5103a2f61309200d6b831373b2ad17405da52a180103d03e8d1da56cd5e6d08e44c4aa886e83b94ce86bff2883d423ad851e44f59282d0011353f087ef9c2227d6307c99f8f3d8861520e1a96460efd1c810ac7baec0cffde4870135876096c106d46c2c07962d57d3832236c00000000000003a5666a34a686000c0000000000001bfdb143fc5bd80040000000000000d68179b29c1c00010014,decode 5 1 0x76b8969a34654a059475553be14e2318e0b10c8a2cc6a08c2424c0028aa850a3c4c9f50477e48760006d80000300002000010014,(AH 7 0x2b89068d18063a018a00033528180c8a031a0003351d5c1de6077681da8000d1753707d581f3a07c600034630dc2f060bb682e68000d13be).toArray⟩
theorem h44:check 4 44 d44=true:=by decide+kernel
def d45:Row:=⟨BCurve 57 46 0x5f64f687a7912b8801a553eb686024dd99d2b5e6fcd080233ec28f91026fd0cb29b3989521446a291833524b407a6093ce6da8b4f92c67c60f2f272744fd99d1ad3a67cc57c9c0bb3925c546498b7fc7113e843b386f1dc797de7b841249385dfc67fd8855fcfb234b31a45d19c14fc103982e0ce7685749718046cc8980da73e1ec832d325bda884da2634c0b876ef0165976c75ae0f694d308e0a73fa2759fb6040370a4e1ae97ff08afa54d759586c925bf20f3b8aa78976f33b57b6cd3d25ff9dc9ce51dc641eed32573187cc4e9b9bedf27d23aef44d652a8ae81a9320b0860efb21e16b46eea42078df1bd7930075f9a110c8c6e8407e759e53fbd5236b80000000000003cd28af7cc308000c0000000000001d352362cd3b380040000000000000e0080a4da2f180010015,decode 5 1 0x76b8869a10654855945a553a614e2234e1718e0a10c892cc6908c2324bff28aa750a3b4c9f40477d4875f006d70000300002000010015,(AH 7 0xae201a10701918063a018a00034521580c9a031e000335169c1e16078281de8000d172a707e181f7a07d6000346251c2f460bc282e98000d13a6).toArray⟩
theorem h45:check 4 45 d45=true:=by decide+kernel
def d46:Row:=⟨BCurve 57 46 0x30424ce4c12015c380d2a9f5b430128c5dfe4ce59067b0119f6147c88138edaadc0bf9128d4235148c19a925c2e36eb9f7db943e7ee0d93dc10fa463dbf5acf81a9c73fa9a36e4f75cfee3a7050631b388605c0941e3add3818d2ac324639c1300ad0c75f8de94cddb208b96fcc88833a0a923ae33c211fe2d89a1a63441eadd578b399ef18d26681cbc308a14113c1d7cbb95aa26d42b7b297fd0d8f0c0dcd85a0b9fb10686eb4aa68c05aae1e0e6da867c830db9e051d478e4b237ae51da4f328619d2027ce4561efb3b188d6e8f896d073d0ef92741cbc6225c33ef2feb1711bc75e9d61124470dc083a2e7587f8ae36b00000000000003f5bef632e020000c0000000000001e73358d0e1f480040000000000000e9c39b4429ec80010014,decode 5 1 0x76b87699ec6546a5943e5538e34e2118e0910c882cc6808c2224bfe28aa650a3a4c9f30477c4875e006d60000300002000010014,(AH 7 0x2b87067b18064a018e0003351a980caa03220003350f9c1e46078e81e18000d1701707f181fba07e6000346195c2f760bd282ed8000d138e).toArray⟩
theorem h46:check 4 46 d46=true:=by decide+kernel
def d47:Row:=⟨BCurve 57 46 0x30d21e85ae7795c300d2a9f5b43012a985be43fd8a6718119f6147c88139f2f0233e25da89c235148c19a925e46f22e3fbabd422812b7e987a8bb532efb3f247d29bac0cf0ba42fcbd8440547ce177c38820f192ab41fad7509aa1f97c991c110549df6910eeb313f36d980c5cc878599a14289474b0eb7e95efe76633c31d43c0150da6760b79443db030861dae7e139f6bcb0f4363721e417fb126e72ce257dbaa866c464de98aa58e9462886a16e7ce8bc7920b0a51cc8daa773d05722cc7b43e736e527ca4fd49a911058ff4b0f0ff930c8ef72ca22c4556144762d0b62e8f9475da0b117fc7334088eab08ac353636a800000000000041f293e56fdce000c0000000000001fb7e7c2bf08080040000000000000f3b42c96310d00010014,decode 5 1 0x76b86699c66544e594225537534e2018e0810c872cc6708c2124bfd28aa550a394c9f20477b4875d006d50000300002000010014,(AH 7 0xae1819c67019680648000cd44e7033180cba0326000345089c1e86079a81e58000d16d77080181fea07f60003460d5c2fb60bde82f18000d1375).toArray⟩
theorem h47:check 4 47 d47=true:=by decide+kernel
def d48:Row:=⟨BCurve 57 46 0x3161f0269bcf15c280d2a9f5b43012c6ad7e3b15846680119f6147c8813af8356a7052a2864235148c19a926071561540c509406837623f33403c600ddb99c9f7e9aec1f473da1023e0993f01fd4b7e387e1871c14a048db1f5d18bd5afa1c0f09e6b25c2906d157bd7e3d9624c8687f937f2d7a759fb23ee1b4a2c633444faa289edfadf9f0a6a3c02b3082274bc009c22c006f8cb822ae897f9174dd98e7d6dd49468db15f198aa491231a2ef346f51553cd2abd4e51c4a2703c425c727f35d3c4a84b527c65a47456e6f3927a7ec9d85b518ef532028cc489cc5ad3c17d1e0c8875ca4011db4758c08e4cf9eac72ea36a00000000000004496787e91c12000c00000000000021033a03dff5780040000000000000fdd9be43b85300010014,decode 5 1 0x76b85699a065432594065535d34e1f18e0710c862cc6608c2024bfc28aa450a384c9f10477a4875c006d40000300002000010014,(AH 7 0xae1419a06019680648000cd4327033580cca032a000345019c1eb607aa81e88000d16ac708118202a0806000346011c2fe60bee82f48000d135d).toArray⟩
theorem h48:check 4 48 d48=true:=by decide+kernel
def d49:Row:=⟨BCurve 57 46 0x31f1c1c7892695c200d2a9f5b43012e36be937536665e4119f6147c8813bfd7ab1a27f6a82a235148c19a92628a1157e1020d3ea85c0c94ded7fd6cda606ac379c9a24319dc0ff079e8ede79edde310387a21ca57dfe96deedd48f0eb9429c0d0e83854f4116ef9939527bd124c858a58cea3260768e663f10d9582632c582109128b3b57d3cae86bc26307e30e901ffe4ec35cb02d23cd6d17f71c2d404ed565ee7e01547bf97caa393b1d1d57c7b025ad493d7e48a51bcb7360147b392d1999118b958327c264b9f04bce094fff913f758b08ef33762ed43bd8c6e42023fe5a3dc75ba751236c77e4093c9c3788b1ca369800000000000047479d2e93aec000c00000000000022552c5070e79800400000000000010834504cbfbe80010014,decode 5 1 0x76b846997965415593ea5534434e1e18e0610c852cc6508c1f24bfb28aa350a374c9f0047794875b006d30000300002000010014,(AH 7 0xae1019797019a80658000cd4157033980cda032e000344fa9c1ef607b681ec8000d1681708218207a0816000345f45c30260bfa82f88000d1344).toArray⟩
theorem h49:check 4 49 d49=true:=by decide+kernel
def d50:Row:=⟨BCurve 57 46 0x32819368767e15c180d2a9f5b430130093a92e6b606544119f6147c8813cf9f04830c7f27f2235148c19a92649123f62071c93cd880b6ea8a6f7e799489b20d7b0995443f4445d0d1f141ff1e6ffa4138762b22ee75ce4e2bc0104ed97729c0b13205842592f0dd866ea532084c848cb86553746b77d077f235f8b263246b476f9b287bcffef90ed25a6307a3a8643f6079c6b21a5b1c042017f5210ca70f2d560865303096a480aa29640897c05ab0f9f0e1b99590051b4cbfbc64d0ab323f2ec3aa61d627be6f2c9b292cd97851fcf5c8ed70ef13cc34dc2f14481ad92fe851efc75aaaa129247a3c099610d340f1d636900000000000004a0601f575a5c000c00000000000023adbea871de68004000000000000112c3e2b1474f80010014,decode 5 1 0x76b8369951653f9593cd5532a34e1d18e0510c842cc6408c1e24bfa28aa250a364c9ef047784875a006d20000300002000010014,(AH 7 0xae0c19516019a80658000cd3f97033d80cea0336000344f35c1f3607c681f08000d165470831820ba0826000345e79c30660c0a82fc8000d132a).toArray⟩
theorem h50:check 4 50 d50=true:=by decide+kernel
def d51:Row:=⟨BCurve 57 46 0x3311650963d595c100d2a9f5b430131ce8bf2fcf2a64a0119f6147c8813ded962e1b2c3a7b6235148c19a9266a9df38c0aecd3af8a5614036073f863c576fab830988c564ac7bb127f9958580b375053872347b850bb32e689e27a59f5899c0917bd2b35713f2c154645c32120c838f17fc03c2cb86b95ff1944346631c7e6dd623c59c482094dd6f0b03076442385ec2a5ca0737556ad9a517f325ec0dcf85462249f56f661b8caa198cf41228edb1ce200646f2e8e51ace0c18b5261d37641e52a6e9ac27ba799f46068bb9a09f2fc0801728eef4223ae4224fc951673b8fc9934759adf12edc7c9409f12d71d5330e36880000000000004cd1a6d337a62000c000000000000250cf10be2d9e800400000000000011d8875714f0600010014,decode 5 1 0x76b8269928653db593af5531134e1c18e0410c832cc6308c1d24bf928aa150a354c9ee0477748759006d10000300002000010014,(AH 7 0xae0819287019e80668000cd3db7034180cfa033a000344ebdc1f6607d681f48000d162770845820fa083a000345da9c30960c1a83008000d1311).toArray⟩
theorem h51:check 4 51 d51=true:=by decide+kernel
def d52:Row:=⟨BCurve 58 46 0x19d09b5528968ae0406954fada1804ce69ca8b034318ff0467d851f22027dc278280b2104ef846a29183352268b0f1d7001e893918ca0b95e19ea04968e4d1cd0564bde3450a58c8bf807a1eb16a1bd94e1b8f7506e865fdd4aef1dea79a8d380e38b3fc5112974a4fd764cc048cc82917792b4112dcad08df79452d8318a48ca1e563167300e279510d4e0c1c937031f893459ab80e382091532fe25596e91fba763c2c5110ea876caa09b5df8c918099511d5b72cb29c28d27ac3a82bdc74f2219efa04b41c9eda1047c38faa1391ce533f352511dda8f081d82b164a87ca46f4c1284758b14134947eec0526f909a2bab91b4000000000000013eaa2f1f66bf800300000000000004ce586f587b43000800000000000012882088cd6e200010014,decode 5 1 0x76b81698ff653be59391552f734e1b18e0310c822cc6208c1c24bf828aa050a344c9ed0477648758006d00000300002000010014,(AH 7 0xae0418ff6019e80668000cd3be7034580d0a033e000344e45c1fa607e681f88000d15f9708558214a084e000345cd1c30d60c2a83048000d12f7).toArray⟩
theorem h52:check 4 52 d52=true:=by decide+kernel
def d53:Row:=⟨BCurve 58 46 0x1a1884259f424ae0006954fada1804d57f100b5c3598d40467d851f22027fa9c3f3dfe994e8046a2918335226ab804753f8e453738eeb5eb8d3660cfaa7026ee4c84b763d7be73b8ea828eb7bb53b3568e1a91cb2c8ddf35dc4988c7b65659380a41eda23742c768881a476dfc50c8193d729645f8dd243d5f57977bf3186525d519a7ff74e11c55cd36d34c1b95d782761bf1a161135e1897bd2fde5f55b6a06a56560c4315239680a9f9decb06fa1399bb2079cabfe7d28ce85268aae880506b02c1ce4af949eca3a126f052593e253d52631aa51dd699c8de8118d4bbe02521738aec757b4913a4c814405562f5bc8dc811b3c00000000000014a42c34d6f0c000300000000000004fbe6bea29bdf0008000000000000133b09c03dee380010014,decode 5 1 0x76b80698d4653a059373552dd34e1a18e0210c812cc6108c1b24bf728a9f50a334c9ec0477548757006cf0000300002000010014,(AH 7 0x2b80063518068a019e000334e8180d2a0342000334dcdc1ff607f681fc8000d15c9708698219a0862000345bf1c31160c3a83088000d12dd).toArray⟩
theorem h53:check 4 53 d53=true:=by decide+kernel
def d54:Row:=⟨BCurve 58 46 0x1a606cf615ee0adfc06954fada1804dc7a004cfea218a80467d851f2202817f705e6ce9a4e0446a2918335226cad6e6f1e30b9354913604138cde155e2cdb737d3a4b0a46a728ea91684a32c7de9aaba4e1994215233586de3e389afe011f438064b27481d72e786be0eeda8a55cc809636c014adedd9b687f2799c7731825bf084dece976c12fe8ea3eb78c1a983ed2f3a4a1a8097e1cbddbc62fda691484211a466fe9cb7c119a5ca9ea07b68162a69a25195e2b57aea28ca8f896d3133951b3c20b33b99209eba63dd1a7aa0d432cee535f4d301dd2a4899f7f8044cf40f5cf730270756b7e14004839c058639af5cfedf1b380000000000001561057d6f77e0003000000000000052a490f5abd11000800000000000013f142fd6670a80010014,decode 5 1 0x76b7f698a86538159354552c234e1918e0110c802cc6008c1a24bf628a9e50a324c9eb0477448756006ce0000300002000010014,(AH 7 0xadfc18a8701a680688000cd3817035180d3a034a000344d51c2036080a82008000d15997087d821ea0876000345b11c31660c4a830d8000d12c2).toArray⟩
theorem h54:check 4 54 d54=true:=by decide+kernel
def d55:Row:=⟨BCurve 58 46 0x1aa855c68c99cadf806954fada1804e374f08ea10e987c0467d851f220283551cc8f9e9b4d8846a2918335226ea2d868fcd32d3359380a96e465a1dc11fd82ab5de4a9e4fd26a9994186b77cf92bfb03ce18967777d8d1a5eb7cf49724cd5d38025460ee03a307a4f1b5577c313cc7f989656c4fc51e128a3ee94cd17317e6583b8231d378a11d32a821fc8c199aa623712d51aeb14e741052d02fd672d351a1ca2689c4ea45b44174a9da30a1fbcb39da8f080894931cf28c699ec4fb3df252fc57cbd0970bc9eaa8da7c5f01c54833f836e7f8a01dceaf4a607de7b4e29f16794a7908755bb3145bc85f405b718045f21d31b3400000000000016212ecbc0015800300000000000005597f6180ded9000800000000000014aacc4046f5700010014,decode 5 1 0x76b7e6987c6536259335552a734e1818e0010c7f2cc5f08c1924bf528a9d50a314c9ea0477348755006cd0000300002000010014,(AH 7 0x14147b051a81108000d2b28061f18069a01a2000334d89c0d56035280d38000d1335708218206a081600034559dc225a088e000335a25c31a60c5a83118000d12a7).toArray⟩
theorem h55:check 4 55 d55=true:=by decide+kernel
def d56:Row:=⟨BCurve 58 46 0x1af03e9703458adf406954fada1804ea6fe0d0437b18510467d851f2202851929d23f2144d0c46a29183352270984262db75a131595cb4ec8ffd226237ff89472834a3258fdac4896d88cba92d1aab338e1798cd9d7e4addf315c97d84889537fe5d9a93e9d337c3230d84e8d164c7e9af5ed754ab1e89a29e9caf16d317a6f16eb676bc7a80e43306dda58c189d0d73eeb601b55884640ffcd92fd27c921f227a06a39d9f720bb490a9ca598d7633ccdaf8ec790670f5628c2a44f32368ab5444c403a4e36689e9ab77271659794d3a5afcfd0e4a1dcaba0b217c4f24f5fa871ef9eebc754be814b74884c05e8ca5acf455d1b3000000000000016e4a81fc88d28003000000000000058989b515013700080000000000001567a588df7c900010014,decode 5 1 0x76b7d6985165343593155528c34e1718dff10c7e2cc5e08c1824bf428a9c50a304c9e90477248754006cc0000300002000010014,(AH 7 0x5050ac140a042e00034a8c41851701aa80698000cd3437035980d5a0352000344c55c20c6082e820a8000d1534708a98229a08a2000345935c31e60c6e83168000d128c).toArray⟩
theorem h56:check 4 56 d56=true:=by decide+kernel
def d57:Row:=⟨BCurve 58 46 0x1b38276779f14adf006954fada1804f1507bd32f6198250467d851f220286dd36db8458d4c8c46a291833522727c03b8594acd2f59815f423b94e2e854d3cb0cf5949c26228edf79988adfb119b5b4494e169b23c323c411faae0862ff371f37fa66d439d00357e1521775ee22e0c7d9d5584259911f00b19e41c1593317678aa1eabba67c6084ea0677accc179f74c46c3eadbbff1fecbccf472fce8650eca329f6bd73eb01181c6ca9ba8278f09c5fdb62c6af80f1d6928beaeb214b9364558d06b2b09ea249e8ae13d1cdb12d524016a59e95851dc6c4cbe27ab695095347c081638c753c1d1512c8aa4061b50b2ad697d1b2c00000000000017ab7179891b5000300000000000005ba680a17242b00080000000000001627ced73006080010014,decode 5 1 0x76b7c6982565323592f55527034e1618dfe10c7d2cc5d08c1724bf328a9b50a2f4c9e80477148753006cb0000300002000010014,(AH 7 0x504f6c13ba041e00034a4ac1825701ae806a8000cd3237036180d7a035a000344bd5c21160842820f8000d1500708c1822fa08ba00034583dc32360c7e831a8000d1270).toArray⟩
theorem h57:check 4 57 d57=true:=by decide+kernel
def d58:Row:=⟨BCurve 58 46 0x1b801037f09d0adec06954fada1804f816c19764c217f80467d851f2202888fa48381c7e4c0846a291833522745fc50dd71ff92d49a60997e72c636e687a47fb03349526b542fa69c48cf394befd1d44ce159d79e8c93d4a0245b14794f1f537f6700ddfb63387ff7ed32a8c889cc7c9fb51ad5e775f77b73dd88459e3172823d51f008f7e3fff57a6ea188c16a1dc14e9c75dc2a5210e16df512fca900fba23d9d6d747ccf2d9278ca9aaab646b04f2dbcc96ac0415c0928bab914f73be1d56d51fd8f3c8bf09e7b0b07c8508e557452b30cc95a11dc2cf8ca3791e151ca9585de0f298752c52156e48cfc064eab0bf98e331b2800000000000018758ad901abd000300000000000005ec1a608747b5000800000000000016eb482b3891d80010014,decode 5 1 0x76b7b697f865302592d45525434e1518dfd10c7c2cc5c08c1624bf228a9a50a2e4c9e70477048752006ca0000300002000010014,(AH 7 0x14138b04da81028000d281805fe1806ba01aa000334c09c0d96036280d78000d12d4708598215a0852000345329c236a08d600033573dc32760c92831f8000d1254).toArray⟩
theorem h58:check 4 58 d58=true:=by decide+kernel
def d59:Row:=⟨BCurve 58 46 0x1bc7f9086748cade806954fada1804fedd075b9a2297ca0467d851f22028a42122b7f36f4b8446a2918335227631ddbef427dd2b39cab3ed92c423f472f3001313b48de747f71559ef8f07541cf0df270e149fd00e6eb68209dcc42b45ac9937f27947859c63a81da940a2c39fb8c7ba214b18635d5feeb37d60f6962316e8bd0853457980a3b9d6f6dcab4c15a4436567500dc94a87c81e225a2ffa99ce87a489c6f11945474f2768a99ad44fe56d85dc365c6e8fdcb3628b6c377d9be8d6581d0f766e61bcc9e6b34d273c60995c49989e86fffa1dbeda4d647785852ffcb8f7186594751c8715c9c8f540682d966b3b37f1b240000000000001942f43e323ea8003000000000000061ea0b8656bd5000800000000000017b21184f920000010014,decode 5 1 0x76b7a697ca652e1592b35523734e1418dfc10c7b2cc5b08c1524bfe28a9950a2d4c9e60476f48751006c90000300002000010014,(AH 7 0x14133b04c680fe8000d26f705f29806ca01ae000334b8580daa0366000334acdc21ca086a000335249c23da08f2000335631c32c60ca683248000d1237).toArray⟩
theorem h59:check 4 59 d59=true:=by decide+kernel
def d60:Row:=⟨BCurve 58 46 0x703f876377d22b7901a553eb6860141623df8463f45e68119f6147c880a2f8b81c8d37612bf11a8a460cd489e00fd9c044bf04a467bd790cf96e91e9d0f7cd4d92121a9f6aacc1286e446bbcce4403b9384e8898d050bee845cd0438459c34dfba0a04ae0a4f20ef457f7a4e66931ea91d120da10d819699736c633d8c5aa6aab5e4d8b9cfef541ad28dcb3052a38d552539a70ae853fe79ca90a98afd3b5fd618dca017f72446af028b2cddabc4138f5964d58b20699b89e5b5e9d1f3b851614d5eeecde3331dbae50e2575ecf5434d698c27d7a4750cbc1625491ac06b7dbc2dbd9611b200000000000001a13ada91ad3d80030000000000000651fb11b1908b0008000000000000187c2ae471b0800010013,decode 5 1 0x76b796979a652bf592915521a34e1318dfb10c7a2cc5a24c1428a9850a2c4c9e50476e48750006c80000300002000010013,(AH 7 0x1412eb04b280f98000d25c805e69c06da01b2000334afdc0dc6036e80da8000d12917088a82208000cd45870912c243a08e600034551dc33160cb683298000d121a).toArray⟩
theorem h60:check 4 60 d60=true:=by decide+kernel
def d61:Row:=⟨BCurve 58 46 0x715f2aa552812b7801a553eb68601430d3a19a5f5e5da4119f6147c880a35c83d5e8aee529d11a8a460cd489e7583c84b8de949ba8502263a7cd9401b16c86f6e091fda1b57d2ce91e4cb9980b75fc6d384a91f166e6a3b864249fbfe05354dfaa2eeb45a30fe167dcc377f29f131e69b4f7b9b4a683723f711baf1b4c59a91206626169d69386063436d6304ead4c22a5e99724b4f918596268a97b2626da3eac1d09c945c15451a28aed83d9ec3e485aac721709e05b49e4b8867cab100566507e21a130ab1db6efcee6745465569b6a1d0f48d074fcf11680c940406edb22071ffd91b1c0000000000001ae7b719bb6b600030000000000000686296c6bb5d7000800000000000019499449a243580010013,decode 5 1 0x76b78697696529d5926e551fd34e1218dfa10c792cc5924c1328a9750a2b4c9e40476d4874f006c70000300002000010013,(AH 7 0x504a6c128a03d600034922c1769a01b6000324a75c0de6037680dc8000d126e708a282268000cd41d70932c24ba08be0003453fdc33660cca832e8000d11fd).toArray⟩
theorem h61:check 4 61 d61=true:=by decide+kernel
def d62:Row:=⟨BCurve 58 46 0x727ecde72d302b7701a553eb6860144b1a0eb580b05cdc119f6147c880a3c04f8f44266927a11a8a460cd489ee59fcb7a9c90492e8e2cbba562c96196d2a2d44b551dfa4004d98a9ca5506e22b5958bf38469b49fd7c88988279e343e73b9cdf9a53d1dd3bd061e06ace83f99d431e2a4cdd65c83e854dbfee91b7e7cc58ab7956dfea19dd371d8a4312df304ab70af02699773e7f3494ed9d94a96b4f1254a73f1d73705a67045ed28aae2a081469015bf3e51a2ac5fc49e3bb23276267b96b52f63700efb31db2fa8fa772bbd569e6baa9ceb91874ed2616dc4965c07245c7f7626e71b180000000000001bbf109014054000300000000000006bb2bc893dbb900080000000000001a1a4db48ad8880010013,decode 5 1 0x76b77697376527a5924b551df34e1118df910c782cc5824c1228a9650a2a4c9e30476c4874e006c60000300002000010013,(AH 7 0x14125b048e80f18000d234105cdd806ea01b60003349e9c0dfa037a00033492dc22eb08b682268000d13df70952c253a089a0003452cdc33b60cde83348000d11df).toArray⟩
theorem h62:check 4 62 d62=true:=by decide+kernel
def d63:Row:=⟨BCurve 58 46 0x739e712907df2b7601a553eb68601464f726d5c7ea5c0c119f6147c880a41fb3704dabcd25611a8a460cd489f5151a59177e5489e9757511048a98310430c0338bd1c0a64b1e046a7a5d539b2dee34a23842a4a294126d78a0cccec45a231cdf8a78b874d490e258efa09e6426b31deae4c311dbd787291aebce83ac8c57ade0a75d72c5e3da1aa6ff17543046c0c9bda749575847067436a4c4a95b77fdcf0fd21ddd0d35155774c28a6ed0363c93ba5d3b2e94831a7e09e2bdbfd219bf717054c72eed27971daf0550687123457d2f5b3266287474dd5b1737c98b4075bdadfe84e8b1b140000000000001c99ba0c24a17800300000000000006f102262a023100080000000000001aee57252b70100010013,decode 5 1 0x76b76697036525659227551c034e1018df810c772cc5724c1128a9550a294c9e20476b4874d006c50000300002000010013,(AH 7 0x50482c11fa03ba0003487a01703601be806e8000cd2567038580e0a037e00034489dc235b08d2821e8000d139f70976c25ca087a00034518dc34060cf683398000d11c0).toArray⟩
theorem h63:check 4 63 d63=true:=by decide+kernel
def d64:Row:=⟨BCurve 58 46 0x74be146ae28e2b7501a553eb6860147e6ae9fb350c5b34119f6147c880a47aaf79053f1123111a8a460cd489fbd037fa8533a480aa081e67b2e99a4876803fca6d11a1a895ee702b26659fc313347426383eadfb2aa85258bf1d62413909d4df7a9d9f0c6d51a2d16b39c73300c31dab7ca8bdef6f89045068d20c60cc56b047f7dafb75ea7c7d5c68595e3042ca888b27f947720c6eb634a09ca94ba0e94978651e469fd5cc4d93828a2f766464be735e824e8612dde109e1c05c7cd117257555f10965c9be1dab1011296f8ab590754bb6d596ec74cd90179349b0c07942d41c876c51b100000000000001d77b38ded40080030000000000000727ac852e293f00080000000000001bc5b09b8409f00010013,decode 5 1 0x76b75696cd6523159202551a134e0f18df710c762cc5624c1028a9450a284c9e10476a4874c006c40000300002000010013,(AH 7 0x1411cb046e80ea8000d208205b35c070a01be0003348c5c0e36038a80e18000d1202708f6c23ca0856000344d72c266a0856000335041c34660d0a833f8000d11a1).toArray⟩
theorem h64:check 4 64 d64=true:=by decide+kernel
def d65:Row:=⟨BCurve 58 46 0x75ddb7acbd3d2b7401a553eb68601497dead20a22e5a64119f6147c880a4d143a96ae03520c11a8a460cd48a028b559bf2e8f4772a9ac7be61479c5fc418ac02509182aae0bedbebd66deb59db2c3338383ab753c13e3738dd6b9dba83efccdf6ac285a406122349dd99fe64a0a31d6c148e6a03078adf60659c55090c55b2af48588425f11e45aa7ece69303ed44758a8a9278bcf6d5ae73fd4a93bc9d4c3e0f81eb0283c8be6bb1289f01c928ce92c5fc944eeda1024c9e0c2f927886edd7a5673c66ae4c01da71ad1ea6df225a3b88c371d047c74bdc517eec9d6407cd53a5169f951b0c0000000000001e58fd156de0f0003000000000000075f2ae5a050e300080000000000001ca05a1794a6280010013,decode 5 1 0x76b74696996520c591dc5518234e0e18df610c752cc5524c0f28a9350a274c9e0047694874b006c30000300002000010013,(AH 7 0x50462c117a039a000347c341699701c680708000cd20c7039280e38000cd1dc70916c244a0836000344c56c271a0836000334ee1c34b60d2283458000d1182).toArray⟩
theorem h65:check 4 65 d65=true:=by decide+kernel
def d66:Row:=⟨BCurve 58 46 0x76fd5aee97ec2b7301a553eb686014b0e91b4b35385988119f6147c880a52370017e8f391e611a8a460cd48a08b92e1a5a34046d6b2d71150fa69e76ecfa04e23e5161ad2b8f47ac8276365f85d555ed3836c0ac57d41c08fbb781303aa328df5ae76c3b9ed2e3c246c143fa91131d2cac741616a08cba4ae22d60a88c54b51698d60cd1f7bf7391426be1303ade0626295917a59002624ed3a8a92bf2c03e498b5f19a6695423896289b0c2c0b513e5611011ced8b149c9dfc595d23fc6917f564f65fc6a051da32592ab6c5995b6f91cb33c712474adfa184a49fbc08074e09d2c8fb1b080000000000001f3d96a2a6843000300000000000007977d4780791d00080000000000001d7e53995d44b80010013,decode 5 1 0x76b7369662651e6591b55516134e0d18df510c742cc5424c0e28a9250a264c9df047684874a006c20000300002000010013,(AH 7 0x50452c113a038e00034762c1662701ca80718000cd1e67039a80e58000cd1b5b093682058000cd2cc509e2c274a0816000344d71c35160d3a834b8000d1161).toArray⟩
theorem h66:check 4 66 d66=true:=by decide+kernel
def d67:Row:=⟨BCurve 58 46 0x781cfe30729b2b7201a553eb686014c920df80141258a4119f6147c880a5759c59923e3d1be11a8a460cd48a0ee70698c17f1463abc01a6bbe04a08df1244a632ed140af765fb36d327e80d4132ff82f3832ca04ee6a00e91a010ca25d8798df4b0c52d33793643aa6af97f347731ced4459c22a388e950fde8529384c53b77de9539581fe600710b346eb3036e7c4f3aa08f7bf4e2dcc6b0ae8a91c1babb8b21e5f831a5c2502c272897168eedd3e9e6256b5260ec14fc9dec8327cf71e49845583e81a68241d9f30536c6ac115ca36fd2b33f7e8749e2f18a5ca21408421c6ffcf2f71b04000000000000202580359729c800300000000000007d0a3aacea1ed00080000000000001e5f9d20dde5a00010013,decode 5 1 0x76b7269629651be5918e5514034e0c18df410c732cc5324c0d28a9150a254c9de0476748749006c10000300002000010013,(AH 7 0x50442c10fa037e000346fec1629701ce80728000cd1be703a280e78000cd18eb095e81fd8000cd27e509bec26ba07f6000344bedc35760d5283518000d1140).toArray⟩
theorem h67:check 4 67 d67=true:=by decide+kernel
def d68:Row:=⟨BCurve 58 46 0x793ca1724d4a2b7101a553eb686014e158a3b4f2ec57b8119f6147c880a5bef90102090119611a8a460cd48a1514df1728ca24596c52c3c26c63a2a4d0977c8c28d11fb1c1301f2dde86cab7833bfe15382ed35d84ffe5c938484010ec6b40df3b31396ad053e4b2fd64fa4f89231caddc3f6e3dd0906faf5aa3b1bc0c52b9e539d11e3205000028d154f63032f183c12ab8d7d909ef993c0e28a90c4497331ab15fec8414fe85046289320f1d056957639d2ef47c4036c9ddcacf27ae75fd8954114cc4d0891d9b3b142d692885dd722d9f0362bc748e6419014a46c087dbed7951d891b000000000000002110b9ce3fd1b8003000000000000080a9e0f8acb5300080000000000001f4436ae1688e00010013,decode 5 1 0x76b71695ee65196591655511f34e0b18df310c722cc5224c0c28a9050a244c9dd0476648748006c00000300002000010013,(AH 7 0x50432c10ba037200034697415ee701d280738000cd196703aa80e98000cd165b098681f68000cd22d5099ac263a07da000344a59c35d60d6a83578000d111f).toArray⟩
theorem h68:check 4 68 d68=true:=by decide+kernel
def d69:Row:=⟨BCurve 58 46 0x7a5c44b427f92b7001a553eb686014f92712eef7ae56c0119f6147c880a603edd01fe1a516d11a8a460cd48a1ab5727289aaf44eece56d191ac1a4bb8b539b562690fcb40c008aee8e8f1409d5f98386382adcb61b95caa9568d1b7be74e20df2b5620026914a52b4ae16b101b131c6e74251a5169924a295688fd364c51bc4c8a4ea6e20b9f5ed99c9600302efb428eab68c7f2c347c8c205fca8fc6d82ad83446055e393e0aa4f1288f2b54b2d941064e37f3a212dfec9dccd6bd265cdb18e51f793fbaa7d1d9745d4ee678ff5f0aaae0eaaccac747e99195cca6c408ba35409b48b11afc00000000000021ff436ca07c0000300000000000008456c75b4f54f0008000000000000202c2041072e780010013,decode 5 1 0x76b70695b06516d5913b550fc34e0a18df210c712cc5124c0b28a8f50a234c9dc0476548747006bf0000300002000010013,(AH 7 0x14109b041e80d98000d18b1056c1c075a01d20003345b5c0eca03ae0003344ed425eb096e81ef8000d11d85097ac25ba07be0003448b1c36460d82835e8000d10fc).toArray⟩
theorem h69:check 4 69 d69=true:=by decide+kernel
def d70:Row:=⟨BCurve 58 46 0x7b7be7f602a82b6f01a553eb6860151022d833484055c0119f6147c880a6447ac6ebc82914211a8a460cd48a205605cdea8bc4442d78166fc920a6d22158a6c82d10d9b656d0f6af3a975ccb0b686c9d3826e60eb22baf8974cf9ee34e303cdf1b7b069a01d525a38f24ea3373331c2f0c0ac6650194247dd23505a18c50beb3dacc2f8e123e232314ff7c302b05015c2c18a80c7a365afca144a8ec966e27ebd760bf38d8cb72a29288b35b7955bec96629a5f6fd8aa7c9dbd0087d1d2569934f36bdbefd471d935095af65f76603e07e7a2a35b4746ece19b84a91c08f77fab0f746f1af800000000000022f11d10b928a000300000000000008810edd4d1fe10008000000000000211759d9afd6680010013,decode 5 1 0x76b6f695706514259110550d934e0918df110c702cc5024c0a28a8e50a224c9db0476448746006be0000300002000010013,(AH 7 0x14105b041280d68000d16f7055c1c076a01d6000334509c0efa03ba0003344414255b094a81e88000d117e50956c252a07a20003446f5c36b60d9e83658000d10d9).toArray⟩
theorem h70:check 4 70 d70=true:=by decide+kernel
def d71:Row:=⟨BCurve 58 46 0x7c9b8b37dd572b6e01a553eb68601526b5487cbeba54b8119f6147c880a67c380d13ca6d11611a8a460cd48a25aff697c8377438ee0abfc6777ea8e892a69edb37d0b5b8a1a1626fea9fa4fb2388d53e3822ef6748c19459930fca4720dfd8df0b9fed319a95a61bca2f77ba56a31befa3f072789995feaccda7ce00cc4fc11b2b49b83e18dc4d053aa68730270ec029acc898262ebb4fec3114a8dcbf59a2546a612883e3beddfee2887401a77de982676fa32b115631c9dad2a527d47d1d984bceca0eba5b1d8f5b5670645ed617139ee1819dd4745f031a13cab7409359e16f1a0c31af400000000000023e646ba89d79800300000000000008bd8546534b0900080000000000002205e3781080b00010013,decode 5 1 0x76b6e6952e65116590e3550b534e0818df010c6f2cc4f24c0928a8d50a214c9da0476348745006bd0000300002000010013,(AH 7 0x14102b040280d38000d1530054b9c077a01da000334459c0f1a03c200033438d424db092e81e18000d112150936c24ba0786000344529c37260dba836d8000d10b5).toArray⟩
theorem h71:check 4 71 d71=true:=by decide+kernel
def d72:Row:=⟨BCurve 58 46 0x7dbb2e79b8062b6d01a553eb6860153cde63cb5b1c53a8119f6147c880a6af8d7ae9da910e911a8a460cd48a2ac344d022ae042d6e9d691d25ddaafedf3d83964ad090baec71ce3096a7ec9a1e5aa186381ef8bfdf577939b14d9da75fc06cdefbc4d3c933566693fc0113a58a231bb03bd61e8c3297d8b648e159560c4ec3827bc740ee1f79dc800d80923023187ef72d78783fe0d6a7906464a8cce8451cbcfda191c4b4baed01928834a7d5a6143b68b576d65c909cc9d9d541d28bd4d59d47bfb8eaf0421d8b66173162c6462a440f44b10510744f381a6f4adcc0974908441cdad1af000000000000024dec06a1288e800300000000000008facfb0c776c7000800000000000022f7bd1c292d500010013,decode 5 1 0x76b6d694ea650e9590b55509034e0718def10c6e2cc4e24c0828a8c50a204c9d90476248744006bc0000300002000010013,(AH 7 0x140feb03f680d08000d135a053aac078a01da0003343a6c0f3a03b60003342d54246b090e81da8000d10c05091ac243a076a00034434dc37960dd683748000d1090).toArray⟩
theorem h72:check 4 72 d72=true:=by decide+kernel
def d73:Row:=⟨BCurve 58 46 0x1fb6b46ee4ad4adb006954fada1805548d354910d394a20467d851f22029b684ce07019d42e823428e38c6716821266ec69e8d08508d0a38e319c5cecb43ec22b49416ef301273d43bad15071d54f2625056bd374239f146b033a7fbdded56381b021875ed5e19cf8919040aa03cdeebe9ba60cc16e70c2499bdf384031b70d3bbca9fca99b29a43e1a19ccc4dc5e9cc44c99a2616d1938d8312301f223dc4ae285859908861e963b4a8bd1130972590a1fafb4bbf9e6f6287f54e03ce3ef469fb20f8df39e8c9d8d7de7d432c89a243098a5390741d8770d7f2612db63d71cfa3b86b60743f6d1acacb02409b456f2fffb2d1aec00000000000025da8a1f533c900030000000000000938ee1ca9a31b000800000000000023ece6c5f9dc480010014,decode 5 1 0x76b6c694a2650ba610855d05b5505634e0618dee10c6d2cc4d24c0728a8b50a1f4c9d80476148743006bb0000300002000010014,(AH 7 0x503eec0faa03360003445dc14a2b01e680758000cd0ba703dac0f5a03aa000344215423eb08ee81d48000d105b508fac23ba0752000344159c38160df6837c8000d106a).toArray⟩
theorem h73:check 4 73 d73=true:=by decide+kernel
def d74:Row:=⟨BCurve 58 46 0x7ffa74fd6d642b6b01a553eb68601566b89c877750515c119f6147c880a700311cfc403908903d4780806843ca7aa4524948f4152fc2bbca829aaf2b0a4612f681cf85bf8212a5b1f2b87a24bc129cd038170b710c8342f9edc23c5d217f48dedc0ea0f864d7a78443f976a5cdf31b316ba176b3639b8c58bea8acd90c4cc8511cc2524a2cb32c3fbac31d301b2bfc922ed848733dd07ef75784a8ad3a1c118e23a26427a8ccf2e60287b5f431f669ad6b40a192995215c9d7da7b27fa843da73dac3e48a2371d837b98b35f9526509cdffe97d0cc742fa21b264b27c09f4f1632c29431ae800000000000026d9a3da4bf2900030000000000000977e089f9d005000800000000000024e56075828d980010013,decode 5 1 0x76b6b69457650897105454f8534e0518ded10c6c2cc4c24c0628a8a50a1e4c9d70476048742006ba0000300002000010013,(AH 7 0x503e2c0f6a032a000343e141457701eec07aa01ce000344225c0f9b03e280e78000d1054508dec234a0736000343fc94237b08d281cd8000d0fd670e2683858000cd043).toArray⟩
theorem h74:check 4 74 d74=true:=by decide+kernel
def d75:Row:=⟨BCurve 58 46 0x811a183f48132b6a01a553eb6860157ad30eefd13a5024119f6147c880a7191778e6a39d05703d4780806843b383d07dff525408314c9a31927da0bf907b2a45d8cd86c33878ffd9827fc5a203dbade431af2038722c6fb9d65f1b93675078c4bcab86d3fdafa334eec84953628301735bb5faf88288ce8aefeb9eedca89d63078bf6b6a2cd49cbe2ea658287769a601e94666c85f8a38ad92409d6dd17d2b1dbf5ac37a7d4ca2cca1d7f8659745dfc9663c540554f3550741fd71b81cb4d40a365fd4c657ef1ae400000000000027dc0d9afcaae800300000000000009b7a6f8b7fd85000800000000000025e12a2ac341400010011,decode 5 1 0x76b6a69409650577102018d8610c6b2cc4b24c0528a8950a1d4c9d60475f48741006b90000300002000010011,(AH 7 0x140f5b03ce80c88000d0d8605026c07ca01c600033415dc0fcb03ee80e38000d1020508c2c22da071e000343e154230b08b681c78000d0f5070e46838d8000cd01b).toArray⟩
theorem h75:check 4 75 d75=true:=by decide+kernel
def d76:Row:=⟨BCurve 58 47 0x411cddc0916115b4806954fada1805636c6099e73713b70233ec28f91014e525c485a458204403d47808068439bb68267f3eed3fa99a3f7b7ac74c73d424c439a3565bcb3f7a2d303818a69123e1317aaca886c5f9832fa4d19b30da80c276e1438dd02391afc7db72c98aecf3c4c2755bf68fad267536261f89bb043563af3911a355c640676eaf0a7de98ec7408060deea5b96053c5123e743988d700000000000000a3871d8595966000c00000000000013f082d1c85736001000000000000026e043e5bbf740001000e,decode 5 1 0x76b69693b76502270fea24b7928a8850a1c4c9d50475e48740006b8000030000200001000e,(AH 7 0x503c6c0f0a0316000342de413b7701fac07da01c200034408ac0ffa0382000333fa94229b089a81c18000d0f14508a6c226a0706000343b19c39ab0e5e83828000d0ff1).toArray⟩
theorem h76:check 4 76 d76=true:=by decide+kernel
def d77:Row:=⟨BCurve 57 47 0x83595ec2fd712b6800d2a9f5b430159fbd4be9b44e4d8408cfb0a3e440a730751ecfbda4feb01ea3c040342383036830070463ec9bf35e3774ec6f102a2b1433e3495d7128941045b1b629a9a9728f5b1d75cded7b2d65c68a0df0f646168073f8208e1c65cc20abbb8bc44b7091adc00000000000029ead12d8622a00030000000000000a39afda7e5a47000800000000000027e2ada66caf98001000b,decode 5 1 0x76b686936164feb70fb24c95d0475d4873f006b7000030000200001000b,(AH 7 0xc0ef503bac0eda030e0003525741361b01fe806f8000ccfeb7040ec102a037a000343ec94222b087e81bc8000d0e9f5088ac21fa06f20003438e1c3a4b0e8283778000d0fc7).toArray⟩
theorem h77:check 4 77 d77=true:=by decide+kernel
def d78:Row:=⟨BCurve 57 47 0x84790204d8202b6700d2a9f5b43015b0f66b7617904c2008cfb0a3e440a72a84907c8228fb201ea3c04034236989259678c723dddd34ddbac997e9d2e414085784873483b0e4a25dee0affa33228e7771ad80000000000002af72aff5ee2000030000000000000a7bf24d868989000800000000000028e8676cd56a480010009,decode 5 1 0x76b676930864fb270f7748734006b60000300002000010009,(AH 7 0x140ecb03ae80c08000d073404c22c081a01b6000333ecac106a036e000333ddd421bb086681b68000d0e265086ec219a06da000343695c3aeb0eae836b8000d0f9a).toArray⟩
theorem h78:check 4 78 d78=true:=by decide+kernel
def d79:Row:=⟨BCurve 54 47 0x10b314a8d659e56cc01a553eb68615c0f38c11ec8a4aac08cfb0a3e44538de228c2b1367bb00f51e0201a1d3ce1a2eca4740f3a8558e77e5f1a5a230d4bd8c3d89fa000000000000b01b535bbe8ee000c00000000000157e1183f972c200100000000000029f17138f627500010008,decode 5 1 0x76b66692ab64f7670f3a004fd0000300002000010008,(AH 7 0x503a6c0e8a02fa0003413f412abb020e806c8000ccf765042ac109a0362000343ce94215b084a81b08000d0da950856c212a06c2000343435c3b8b0eda83608000d0f6c).toArray⟩
theorem h79:check 4 79 d79=true:=by decide+kernel
def d80:Row:=⟨BCurve 54 47 0x10d7091111afc56ca01a553eb68615d01e02b80d54492c08cfb0a3e44537fe644cc362879c00f51e0201a1cd044c67860180efa8700ea5a60465c4fa111da50a8570000000000000b4673ad0e19f2000c000000000001605e66fc1d39e0010000000000002afdcb0acee6b00010008,decode 5 1 0x76b656924b64f3870efa002b80000300002000010008,(AH 7 0x5039ac0e5a02ee000340ae0124bb020e806a8000ccf385041ec106a0356000343be9420eb083281ab8000d0d285083ac20ca06ae0003431c5c3c3b0f0a83568000d0f3c).toArray⟩
theorem h80:check 4 80 d80=true:=by decide+kernel
def d81:Row:=⟨BCurve 54 47 0x10fafd794d05a56c801a553eb68615de0c7a6d9fd647a008cfb0a3e44536d828883c8fa77b80f51e0201a1c6ad64b1327f38eb888a8ed3661725e82d4e34be228122000000000000b8c0625ce4b8c000c00000000000168f635e6635a60010000000000002c0d74e25fa8680010008,decode 5 1 0x76b64691e864ef770eb8000910000300002000010008,(AH 7 0x140e3b038a80b98000d0065047a14082b020680698000d0ef750412c103a034e000343ae14208b081a81a68000d0ca350822c206a069a000342f45c3cfb0f3a834b8000d0f0a).toArray⟩
theorem h81:check 4 81 d81=true:=by decide+kernel
def d82:Row:=⟨BCurve 54 47 0x111ef1e1885b856c601a553eb68615eb28482d7e28460008cfb0a3e4453548307c0709c75a00f51e0201a1c890f6dc1cfc88e738a50f012629e60bca8c02d7858120000000000000bd26c9ffc7dbc000c00000000000171a884fe698da0010000000000002d206ebfa86c780010008,decode 5 1 0x76b636918064eb470e73000900000300002000010008,(AH 7 0x50386c0e0a02de0003400001180b020280688000cceb450406c100a03420003439cd4202b080281a18000d0c1b5080ac200a0686000342cadc3dcb0f6e83418000d0ed6).toArray⟩
theorem h82:check 4 82 d82=true:=by decide+kernel
def d83:Row:=⟨BCurve 54 47 0x1142e649c3b1656c401a553eb68615f70816fcce32445408cfb0a3e4453371baeab261e73700f51e0201a1ca7489070779d8e2c8bf8f2ee63ca62fd1ca87f133811e000000000000c19a71b98b082000c0000000000017a7554442fd3a0010000000000002e36b8a2a932e00010008,decode 5 1 0x76b626911564e6e70e2c0008f0000300002000010008,(AH 7 0x5037ac0dda02d60003400001115501fec07ea019e0003439b940feb03f680ce8000d0e2c507f2c1faa0672000342e3941fcb07ea819c8000d0a82b0faa83378000ccea0).toArray⟩
theorem h83:check 4 83 d83=true:=by decide+kernel
def d84:Row:=⟨BCurve 54 47 0x1166dab1ff07456c201a553eb6861601abe6db8ff4429c08cfb0a3e44531318911af07071280f51e0201a1cc581b31f1f728de28da0f5ca64f66544309c40b2c811c000000000000c61b598a2e3de000c000000000001835ca3b7b62c60010000000000002f50528b61fba00010008,decode 5 1 0x76b61690a764e2570de20008e0000300002000010008,(AH 7 0x2c0dba02ca00033000010a7b01f680658000cce25503eec0faa032e00034378941f6b07d281978000d0afd507dac1f4a065e00034274d43edb0fa6832d8000d0e67).toArray⟩
theorem h84:check 4 84 d84=true:=by decide+kernel
def d85:Row:=⟨BCurve 54 47 0x118acf1a3a5d256c001a553eb686160b7d0cc49d8640d408cfb0a3e4452eaad9b38c8a26ed00f51e0201a1ce3bad5cdc7478d968f48f8a666226791e49b72570811a000000000000caa98171b17d0000c0000000000018c5e7358fc97e001000000000000306d3c79d2c6b80010008,decode 5 1 0x76b606903564dda70d960008d0000300002000010008,(AH 7 0x140d9b036280b08000d0000040d5407cb01ee80648000d0dda503e2c0f7a032600034365941f1b07be81928000d0a68507c6c1efa064a00034248143e2b0f7a83248000d0e2d).toArray⟩
theorem h85:check 4 85 d85=true:=by decide+kernel
def d86:Row:=⟨BCurve 54 47 0x11aec38275b3056be01a553eb68616147b88b7f6e83efc08cfb0a3e4452bba6e0dbb5a46c680f51e0201a1d02313ffcef84cd4790f0fb82674e69e638a613fff811a000000000000cf44e97014c58000c000000000001957ac32803162001000000000000318d766dfb94280010008,decode 5 1 0x76b5f68fbf64d8d70d470008d0000300002000010008,(AH 7 0x5035ec0d6a02ba0003400000fbfb01ea80638000ccd8d503d6c0f4a031a00034351d41ebb07a6818d8000d09d0507aec1e9a06360003421a543d7b0f4e831a8000d0df0).toArray⟩
theorem h86:check 4 86 d86=true:=by decide+kernel
def d87:Row:=⟨BCurve 54 47 0x11d2b7eab108e56bc01a553eb686161c3e05bac2023d1808cfb0a3e445286046203b77669e80f51e0201a1d206a62ab9759ccf59298fe5e687a6c412cbc25ad98118000000000000d3ed918558176000c0000000000019eb19324c9a7200100000000000032b10067dc63f00010008,decode 5 1 0x76b5e68f4664d3d70cf50008c0000300002000010008,(AH 7 0x50352c0d3a02b20003400000f46b01e680628000ccd3d503cec0f2a03120003433d541e6b079281898000d09335079ac1e4a0626000341eb543ccb0f2283118000d0db1).toArray⟩
theorem h87:check 4 87 d87=true:=by decide+kernel
def d88:Row:=⟨BCurve 54 47 0x11f6ac52ec5ec56ba01a553eb6861622c483ccfed43b2408cfb0a3e44524bfa0ad9c72867500f51e0201a1d3ea3855a3f2ecca19441013a69a66ea2c0dda75fe8116000000000000d8a379b17b72a000c000000000001a802e34f504ae00100000000000033d7da677536100010008,decode 5 1 0x76b5d68ec964cea70ca10008b0000300002000010008,(AH 7 0x140d2b034680aa8000d000003b254078b01de80618000d0cea503c2c0efa030a00034328541e0b077a81848000d089250782c1dea0612000341bb143c1b0ef683088000d0d70).toArray⟩
theorem h88:check 4 88 d88=true:=by decide+kernel
def d89:Row:=⟨BCurve 54 47 0x121aa0bb27b4a56b801a553eb68616287857e98776392408cfb0a3e44520b53ef34ebaa64a80f51e0201a1d5cdca808e703cc4a95e904166ad2710af50a9916e8114000000000000dd66a1f47ed74000c000000000001b16eb3a7970160010000000000003502046cc60a880010008,decode 5 1 0x76b5c68e4964c9570c4a0008a0000300002000010008,(AH 7 0x50342c0cfa02a20003400000e49b01da80608000ccc95503b6c0eca030200034312941dbb076681808000d07ee5076ec1d9a060200034189d43b7b0ece83008000d0d2d).toArray⟩
theorem h89:check 4 89 d89=true:=by decide+kernel
def d90:Row:=⟨BCurve 54 47 0x123e9523630a856b601a553eb686162cf02d1581d0371408cfb0a3e4451c645fb3e1e0c61e80f51e0201a1d7b15cab78ed8cbf1979106f26bfe7379c942fad298112000000000000e2370a4e62454000c000000000001baf5042d9dcaa001000000000000362f7e77cee1580010008,decode 5 1 0x76b5b68dc564c3d70bf1000890000300002000010008,(AH 7 0x2c0cda029a0003300000dc5b01d6805f8000ccc3d503aec0eaa02fa000342fc541d6b0752817c8000d07455075ac1d4a05f200034157543adb0ea682f78000d0ce7).toArray⟩
theorem h90:check 4 90 d90=true:=by decide+kernel
def d91:Row:=⟨BCurve 54 47 0x1262898b9e60656b401a553eb686163095584bc7fa34f408cfb0a3e44517a9c42cc653e5f180f51e0201a1d994eed6636adcb95993909ce6d2a75ef3d86cc92f8110000000000000e714b2bf25bca000c000000000001c495d4e164a6a001000000000000376048888fba800010008,decode 5 1 0x76b5a68d3d64be370b95000880000300002000010008,(AH 7 0x140cbb032a80a58000d0000034f54074b01ce805e8000d0be3503a2c0e7a02f2000342e5541d1b073e81788000d069950746c1cfa05e200034123d43a3b0e7e82ef8000d0c9f).toArray⟩
theorem h91:check 4 91 d91=true:=by decide+kernel
def d92:Row:=⟨BCurve 54 47 0x12867df3d9b6456b201a553eb6861632fe84917fdc32c808cfb0a3e44512a8ab208ba505c300f51e0201a1db7881014de82cb379ae10caa6e56786b51d60e580810e000000000000ebff9b46c93d6000c000000000001ce5125c2eb9560010000000000003894629f0896000010008,decode 5 1 0x76b5968cb264b8670b37000870000300002000010008,(AH 7 0x140c9b032280a38000d0000032c94073b01ca805d8000d0b865039ac0e5a02ea000342cdd41ccb072e81738000d05e850732c1cba05ce000340ef14399b0e5a82e78000d0c56).toArray⟩
theorem h92:check 4 92 d92=true:=by decide+kernel
def d93:Row:=⟨BCurve 54 47 0x12aa725c150c256b001a553eb68616349506e1838e308c08cfb0a3e4450d3dd5cca243259380f51e0201a1dd5c132c38657cad69c890f866f827aee0630c021c810c000000000000f0f7c3e54cc78000c000000000001d826f6d23296e00100000000000039cbccbb3973d80010008,decode 5 1 0x76b5868c2364b2770ad6000860000300002000010008,(AH 7 0x140c7b031a80a18000d00000308d4072b01c6805c8000d0b2750392c0e3a02e2000342b5941c8b071a816f8000d053450722c1c6a05be000340b914390b0e3282df8000d0c09).toArray⟩
theorem h93:check 4 93 d93=true:=by decide+kernel
def d94:Row:=⟨BCurve 54 47 0x12ce66c45062056ae01a553eb6861634ef8a40f8f82e4408cfb0a3e445076944310a2e456280f51e0201a1df3fa55722e2cca729e31126270ae7d775a96e1f03810a000000000000f5fd2c9ab05b0000c000000000001e217480f39ab20010000000000003b0686dd2254080010008,decode 5 1 0x76b5768b9164ac570a72000850000300002000010008,(AH 7 0x50316c0c4a027e0003400000b91b01c2805b8000ccac550386c0e0a02da0003429c941c3b0706816c8000d047b5070ec1c1a05b20003408214387b0e0e82d78000d0bbb).toArray⟩
theorem h94:check 4 94 d94=true:=by decide+kernel
def d95:Row:=⟨BCurve 54 47 0x12f25b2c8bb7e56ac01a553eb68616347763aaba322bf008cfb0a3e445014e351052f7653080f51e0201a1e1270bfa1566a0a0c9fd9153e71da80074f0873c35810a000000000000fb0fd566f3f7e000c000000000001ec22197a00d220010000000000003c449104c336900010008,decode 5 1 0x76b5668afc64a6170a0c000850000300002000010008,(AH 7 0x5030ec0c2a027a0003400000afcb01be805a8000cca615037ec0dea02d200034283141beb06f681688000d03bf506fac1bda05a200034049d437db0dea82cf8000d0b6b).toArray⟩
theorem h95:check 4 95 d95=true:=by decide+kernel
def d96:Row:=⟨BCurve 54 47 0x13164f94c70dc56aa01a553eb6861632c33e23ed24298c08cfb0a3e444fac969a7ed0d84fd00f51e0201a1e30a9e24ffe3f09a3a181181a7306829de385759b28108000000000001002fbe4a179e2000c000000000001f6476b12880be0010000000000003d85eb321c1b700010008,decode 5 1 0x76b5568a63649fa709a3000840000300002000010008,(AH 7 0x50306c0c0a02720003400000a63b01ba80598000cc9fa50376c0dca02ca00034268d41bab06e281648000d02fe506eac1b8a05920003401094374b0dc682c88000d0b18).toArray⟩
theorem h96:check 4 96 d96=true:=by decide+kernel
def d97:Row:=⟨BCurve 54 47 0x133a43fd0263a56a801a553eb686162fd319ac91ce271408cfb0a3e444f3fe20ba6801a4c800f51e0201a1e4ee304fea6140938a3291af67432853b180de777a8106000000000001055ce7441b4dc000c00000000000200873cd8cf5860010000000000003eca95652d02a80010008,decode 5 1 0x76b54689c56499070938000830000300002000010008,(AH 7 0x502fec0bea026a00034000009c5b01b680588000cc9905036ec0daa02c20003424e141b6b06d281608000d023a506dac1b4a0582000340001436cb0da282c18000d0ac3).toArray⟩
theorem h97:check 4 97 d97=true:=by decide+kernel
def d98:Row:=⟨BCurve 54 47 0x26bc70ca7b730ad4c08cfb0a3e444ecc91b853442c49200f51e0201a1e6d1c27ad4de908caa4d11dd2755e87deeca1c958d81040000000000010a975054ff06c000c0000000000020ae18eccd6b7a00100000000000040128f9df5ec380010007,decode 5 1 0x76b5364924708ca000820000300002000010007,(AH 7 0xb02f680998000cc00002492c06ca015e000332492c0d8a02ba00033232941b1b06c2815d8000d0171506c6c1b0a05760003400014363b0d8282b98000d0a6c).toArray⟩
theorem h98:check 4 98 d98=true:=by decide+kernel
def d99:Row:=⟨BCurve 54 47 0x2704599af21ecad4808cfb0a3e444e54d98cae161e43f80f51e0201a1e8b554a5bf5be085aa67920ae768a8a8961411b3eb81020000000000010fdef97cc2c92000c000000000002155660ee9e29a001000000000000415dd9dc76d8200010007,decode 5 1 0x76b526487f7085a000810000300002000010007,(AH 7 0xb02ee80978000cc000021fec06ba015a0003322dac0d6a02b200033216941adb06b281598000d00a5506b6c1aca0566000340001435bb0d6282b28000d0a13).toArray⟩
theorem h99:check 4 99 d99=true:=by decide+kernel
def d100:Row:=⟨BCurve 54 47 0x4e9884d6d19515a880f51e0201a1ea98e6d0a9d9307d7a821238a77b68d3a75ebdd29481000000000000011533e2bb6694e000c0000000000021fe5b33e25ae600100000000000042ac7420afc6600010006,decode 5 1 0x76b51707d7000800000300002000010006,(AH 7 0x140bab02e680968000d000001f5d406ab01a680558000d084550352c0d3a02ae000341f9d41a9b069e81568000d0000506a6c1a7a055a0003400014352b0d3e82ab8000d09b7).toArray⟩
theorem h100:check 4 100 d100=true:=by decide+kernel
def d101:Row:=⟨BCurve 54 47 0x4f285677beec95a800f51e0201a1ec804d739c5d0472ca9c9266678e28ff22aa20f18881000000000000011a960c10ea6a0000c0000000000022a8f85bb6d45e00100000000000043fe5e6aa0b6f80010006,decode 5 1 0x76b507072c000800000300002000010006,(AH 7 0x140b8b02de80948000d000001cb14069b01a280548000d07d15034ac0d1a02a6000341dc941a5b068e81528000d000050696c1a3a054a000340001434ab0d1e82a58000d0959).toArray⟩
theorem h101:check 4 101 d101=true:=by decide+kernel
def d102:Row:=⟨BCurve 54 47 0x4fb82818ac4415a780f51e0201a1ee63df9e86da5467eab7129427a0e92b07f63b10c780fe0000000000012005757d4e488000c0000000000023553d86674f02001000000000000455398ba49a9e80010006,decode 5 1 0x76b4f7067e0007f0000300002000010006,(AH 7 0x140b6b02d680938000d0000019f94068b019e80538000d075b50342c0cfa029e000341be941a1b067e814f8000d000050686c19fa053e0003400014342b0cfe829e8000d08fa).toArray⟩
theorem h102:check 4 102 d102=true:=by decide+kernel
def d103:Row:=⟨BCurve 54 47 0x5047f9b9999b95a700f51e0201a1f04771c97157a45ccad192c1e7b3a95757430c305180fc00000000000125821f0092306000c0000000000024032ab3f3cad200100000000000046ac230faa9f300010006,decode 5 1 0x76b4e705cc0007e0000300002000010006,(AH 7 0xb02d280918000cc00001732c067a014e000331b8ac0cea029a0003319fd419db0672814c8000d000050676c19ca0532000340001433bb0ce282988000d0898).toArray⟩
theorem h103:check 4 103 d103=true:=by decide+kernel
def d104:Row:=⟨BCurve 54 47 0x50d7cb5a86f315a680f51e0201a1f22b03f45bd4f4517aec12efa7c66984109094502680fa0000000000012b0c089ab621a000c0000000000024b2bfe45c47ce0010000000000004807fd6ac396d00010006,decode 5 1 0x76b4d705170007d0000300002000010006,(AH 7 0x140b3b02ca80908000d00000145ec066a014a00033199ac0cca02920003318094199b066281498000d000050666c198a05260003400014333b0cc282918000d0833).toArray⟩
theorem h104:check 4 104 d104=true:=by decide+kernel
def d105:Row:=⟨BCurve 54 47 0x28b3ce7dba254ad30008cc506efa851422d477a5a623780f51e0201a1f40e961f46524445db06931d67d929b133ded3704680f800000000000130a3324bba1c4000c000000000002563fd17a0c5f6001000000000000496727cb9490c80010007,decode 5 1 0x76b4c6c46f7045d0007c0000300002000010007,(AH 7 0x140b1b02c2808f8000d000001176c065a01460003317a6c0caa028e0003316094195b065281468000d000050656c194a051a000340001432bb0ca6828b8000d07cd).toArray⟩
theorem h105:check 4 105 d105=true:=by decide+kernel
def d106:Row:=⟨BCurve 54 47 0x28fbb74e30d10ad2c008cc506efa85030d2860d50e23700f51e0201a1f5f5fcc238d61839fb21134b27ebe9dec12dc990b180f800000000000136479c139e204000c000000000002616e24dc1454a0010000000000004ac9a2321d8d180010007,decode 5 1 0x76b4b6c46e7039f0007c0000300002000010007,(AH 7 0x2c0afa0236000330000039fb019280508000cc56850326c0c8a02860003414014192b064281438000d00005064ac190a050e0003400014324b0c8682858000d0764).toArray⟩
theorem h106:check 4 106 d106=true:=by decide+kernel
def d107:Row:=⟨BCurve 54 47 0x2943a01ea77ccad28008cc506efa84f16ab74314ce23700f51e0201a1f7d98eed2353682ddb3b9378e7feaa0cb87d76b16780f60000000000013bf945f2622da000c0000000000026cb6f86bdc5ca0010000000000004c2f6c9e5e8bc00010007,decode 5 1 0x76b4a6c46e702dd0007b0000300002000010007,(AH 7 0x502bac0ada023200034000002ddb018e80508000cc4e55031ec0c6a02820003411ed418eb0636813f8000d00005063ac18da04fe000340001431db0c6a827f8000d06f9).toArray⟩
theorem h107:check 4 107 d107=true:=by decide+kernel
def d108:Row:=⟨BCurve 54 47 0x298b88ef1e288ad24008cc506efa84df3b811e64e623700f51e0201a1f9bd21180dd0b8217b5613a6a8116a3b19cddad26880f400000000000141b82fe806446000c000000000002781a4c29647760010000000000004d988710578cc00010007,decode 5 1 0x76b496c46e702170007a0000300002000010007,(AH 7 0x2c0aca022e0003300000217b018a804f8000cc46050316c0c4a027a000340fd1418bb0626813d8000d00005062ec189a04f60003400014316b0c4e82798000d068c).toArray⟩
theorem h108:check 4 108 d108=true:=by decide+kernel
def d109:Row:=⟨BCurve 54 47 0x29d371bf94d44ad20008cc506efa84cca2b734814023680f51e0201a1fba0b342f84e0814eb7093d468242a69e51ef5f3b480f2000000000001478459f48a648000c00000000000283982014aca4e0010000000000004f04f1880890180010007,decode 5 1 0x76b486c46d7014e000790000300002000010007,(AH 7 0x140abb02aa80898000d00000053ac061a013a000330f62c0c3a0276000330da94187b061a813a8000d00005061ec186a04ea000340001430fb0c3282738000d061d).toArray⟩
theorem h109:check 4 109 d109=true:=by decide+kernel
def d110:Row:=⟨BCurve 54 47 0x2a1b5a900b800ad1c008cc506efa84b9a0598569dc23680f51e0201a1fd84456de2cb58082b8b14022836ea991a70c8154b80f00000000000014d5dc417ee8e0000c0000000000028f30742db4e520010000000000005074ac057195c80010007,decode 5 1 0x76b476c46d70082000780000300002000010007,(AH 7 0xb02a680888000cc000002094061b0182804d8000d034d5030ac0c1a026e000340b754184b060a81378000d000050612c182a04de0003400014308b0c16826e8000d05ab).toArray⟩
theorem h110:check 4 110 d110=true:=by decide+kernel
def d111:Row:=⟨BCurve 50 37 0xa98d0d8208af2b468cc506efacb133cc9bd7da236800000000258884dad0df8000c0000000012c3b5a86180180040000000009619471ad48380010005,decode 5 1 0x76b466c46d6c0036c0026c0010005,(AH 7 0x140a8b029e80878000d0000000014060b017e804d8000d02c050302c0bfa026a0003409394180b05fe81348000d000050602c17fa04d20003400014301b0bfa82688000d0538).toArray⟩
theorem h111:check 4 111 d111=true:=by decide+kernel
def d112:Row:=⟨BCurve 50 37 0xaaacb0c3e35e2b458cc506efacba3caf4e7eee23600000000025d0cbf066182000c0000000012e7d9332c1c68004000000000973a6371296600010005,decode 5 1 0x76b456c46c6c0036c0026c0010005,(AH 7 0xb029a80868000cc00000002c05fa01320003308c2c0bea02620003306f5417db05f281318000d0000505f6c17ca04c600034000142fab0be282628000d04c2).toArray⟩
theorem h112:check 4 112 d112=true:=by decide+kernel
def d113:Row:=⟨BCurve 50 37 0xabcc5405be0d2b448cc506efacc3459201260223600000000026191305fb50c000c00000000130bfcbdf6b8b8004000000000985b7fc77e4880010005,decode 5 1 0x76b446c46c6c0036c0026c0010005,(AH 7 0x50296c0a4a02160003400000000b017a804b8000cc19e502f6c0bca025e0003404a1417ab05e2812f8000d0000505eac178a04be00034000142f4b0bc6825d8000d044a).toArray⟩
theorem h113:check 4 113 d113=true:=by decide+kernel
def row (v:ℕ):Row:=match v with
 | 0=>d0
 | 1=>d1
 | 2=>d2
 | 3=>d3
 | 4=>d4
 | 5=>d5
 | 6=>d6
 | 7=>d7
 | 8=>d8
 | 9=>d9
 | 10=>d10
 | 11=>d11
 | 12=>d12
 | 13=>d13
 | 14=>d14
 | 15=>d15
 | 16=>d16
 | 17=>d17
 | 18=>d18
 | 19=>d19
 | 20=>d20
 | 21=>d21
 | 22=>d22
 | 23=>d23
 | 24=>d24
 | 25=>d25
 | 26=>d26
 | 27=>d27
 | 28=>d28
 | 29=>d29
 | 30=>d30
 | 31=>d31
 | 32=>d32
 | 33=>d33
 | 34=>d34
 | 35=>d35
 | 36=>d36
 | 37=>d37
 | 38=>d38
 | 39=>d39
 | 40=>d40
 | 41=>d41
 | 42=>d42
 | 43=>d43
 | 44=>d44
 | 45=>d45
 | 46=>d46
 | 47=>d47
 | 48=>d48
 | 49=>d49
 | 50=>d50
 | 51=>d51
 | 52=>d52
 | 53=>d53
 | 54=>d54
 | 55=>d55
 | 56=>d56
 | 57=>d57
 | 58=>d58
 | 59=>d59
 | 60=>d60
 | 61=>d61
 | 62=>d62
 | 63=>d63
 | 64=>d64
 | 65=>d65
 | 66=>d66
 | 67=>d67
 | 68=>d68
 | 69=>d69
 | 70=>d70
 | 71=>d71
 | 72=>d72
 | 73=>d73
 | 74=>d74
 | 75=>d75
 | 76=>d76
 | 77=>d77
 | 78=>d78
 | 79=>d79
 | 80=>d80
 | 81=>d81
 | 82=>d82
 | 83=>d83
 | 84=>d84
 | 85=>d85
 | 86=>d86
 | 87=>d87
 | 88=>d88
 | 89=>d89
 | 90=>d90
 | 91=>d91
 | 92=>d92
 | 93=>d93
 | 94=>d94
 | 95=>d95
 | 96=>d96
 | 97=>d97
 | 98=>d98
 | 99=>d99
 | 100=>d100
 | 101=>d101
 | 102=>d102
 | 103=>d103
 | 104=>d104
 | 105=>d105
 | 106=>d106
 | 107=>d107
 | 108=>d108
 | 109=>d109
 | 110=>d110
 | 111=>d111
 | 112=>d112
 | 113=>d113
 | _=>default
theorem checked (v:ℕ) (hv:4+v≤117):check 4 v (row v)=true:=by
 have hvl:v≤113:=by omega
 interval_cases v
 · exact h0
 · exact h1
 · exact h2
 · exact h3
 · exact h4
 · exact h5
 · exact h6
 · exact h7
 · exact h8
 · exact h9
 · exact h10
 · exact h11
 · exact h12
 · exact h13
 · exact h14
 · exact h15
 · exact h16
 · exact h17
 · exact h18
 · exact h19
 · exact h20
 · exact h21
 · exact h22
 · exact h23
 · exact h24
 · exact h25
 · exact h26
 · exact h27
 · exact h28
 · exact h29
 · exact h30
 · exact h31
 · exact h32
 · exact h33
 · exact h34
 · exact h35
 · exact h36
 · exact h37
 · exact h38
 · exact h39
 · exact h40
 · exact h41
 · exact h42
 · exact h43
 · exact h44
 · exact h45
 · exact h46
 · exact h47
 · exact h48
 · exact h49
 · exact h50
 · exact h51
 · exact h52
 · exact h53
 · exact h54
 · exact h55
 · exact h56
 · exact h57
 · exact h58
 · exact h59
 · exact h60
 · exact h61
 · exact h62
 · exact h63
 · exact h64
 · exact h65
 · exact h66
 · exact h67
 · exact h68
 · exact h69
 · exact h70
 · exact h71
 · exact h72
 · exact h73
 · exact h74
 · exact h75
 · exact h76
 · exact h77
 · exact h78
 · exact h79
 · exact h80
 · exact h81
 · exact h82
 · exact h83
 · exact h84
 · exact h85
 · exact h86
 · exact h87
 · exact h88
 · exact h89
 · exact h90
 · exact h91
 · exact h92
 · exact h93
 · exact h94
 · exact h95
 · exact h96
 · exact h97
 · exact h98
 · exact h99
 · exact h100
 · exact h101
 · exact h102
 · exact h103
 · exact h104
 · exact h105
 · exact h106
 · exact h107
 · exact h108
 · exact h109
 · exact h110
 · exact h111
 · exact h112
 · exact h113
end AYP
namespace AYS
open DZ CL
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
def d0:Row:=⟨BCurve 54 43 0xe02a53c51206aed034aa7d6d0c1aefb3dc0b50f2f72119f6147c88848cf6740c0c8581b940053000240094805600031afe40000000000000df008280051000c00000000000012a00b20007e00100000000000001f4012c000dc0010007,decode 5 1 0x76bb469ee46581b017f20000300002000010007,(AH 7 0xaed01ee46015680548000cd81b702b580aca02a6000345fc9c18e6063281888000d1c3f70671819ba065a000347931c28f60a3282818000d16db).toArray⟩
theorem h0:check 5 0 d0=true:=by decide+kernel
def d1:Row:=⟨BCurve 54 43 0xe4a8e0cc7cc2aecc34aa7d6d0c1b316b559cd696f66119f6147c888532d7da34b3e9808a4005b0002400c58070c003aafbc00000000000013900b400063000c0000000000001ce010d000a200100000000000002540164000fc0010007,decode 5 1 0x76bb369ecc65808017de0000300002000010007,(AH 7 0x2bb307b31c0566015680548000d1808702b580aca02aa000345f79c18f6063a81898000d1c2470675819ca06620003478bdc29160a3a82838000d16ca).toArray⟩
theorem h1:check 5 1 d1=true:=by decide+kernel
def d2:Row:=⟨BCurve 54 43 0xe9276dd3e77eaec834aa7d6d0c1b7322cf2e5c3af59919f6147c8885dd2118af4d6d7f5884101606c600b1b15e58966af9600000000000011f423c00f6a000c0000000000001b64376a180e001000000000000025c04ea822900010007,decode 5 1 0x76bb269eb3657f5017cb0000300002000010007,(AH 7 0xaec81eb36015a80548000cd7f5702b980ada02aa000345f2dc1906063e818b8000d1c0a7067d819ea066a000347845c29360a4282858000d16b8).toArray⟩
theorem h2:check 5 2 d2=true:=by decide+kernel
def d3:Row:=⟨BCurve 54 43 0xeda5fadb523aaec434aa7d6d0c1bb4079eca2daef4d119f6147c8886876a5729e6f17e1aa413b2083a00f181d138c5daf7000000000000018de304e149e000c00000000000027184cea2102001000000000000038e8727031900010007,decode 5 1 0x76bb169e9a657e1017b80000300002000010007,(AH 7 0x2bb107a698056a0156000335f8580aea02ae000335ee1c19260646818c8000d1bef70681819fa066e0003477d1c29560a4a82868000d16a7).toArray⟩
theorem h3:check 5 3 d3=true:=by decide+kernel
def d4:Row:=⟨BCurve 56 43 0x1e4490fc579ed5d806954fada180dfadf8c2dd9a97a048cfb0a3e4410e5a977aa51caaf9d1a8a460cd4a05eda5741c00a17a4cc4174e09ae004e7494a23ec6b4a800000000000020d83eaa1a8c000c0000000000000d3b19818ada8004000000000000050509d7043780010008,decode 5 1 0x76bb069e81657ce597a4016950000300002000010008,(AH 7 0x2bb007a05c0576015a80558000d17ce702bd80aea02ae000345e91c1936064a818e8000d1bd57068981a1a0676000347759c29760a5282888000d1695).toArray⟩
theorem h4:check 5 4 d4=true:=by decide+kernel
def d5:Row:=⟨BCurve 56 43 0x1ed4629d44f655d786954fada180e1b51f3fbc263799c8cfb0a3e4410fa65a46f66b72f751a8a460cd4a0881fd3561da9d790ee41aea0b220062a8b8924d8ab41800000000000029e24ed42134000c000000000000113820af8dd1800400000000000006bf8cfa858480010008,decode 5 1 0x76baf69e67657ba59790016830000300002000010008,(AH 7 0xaebc1e677015d8056a0156000345ee980afa02b2000335e41c19560652818f8000d1bba7069181a3a067a0003476e1c29960a5a828b8000d1683).toArray⟩
theorem h5:check 5 5 d5=true:=by decide+kernel
def d6:Row:=⟨BCurve 56 44 0xfb21a1f1926eaeb81a553eb686038ef116f26ac75e4e119f6147c88221e43a268f7475e991a8a460cd4a0b1654f6a7b49977c8820f43064b003c7e700f2ee159c40000000000000cff18330a25800300000000000002b7a5189224b000800000000000008be1091870000010008,decode 5 1 0x76bae69e4e657a65977c016710000300002000010008,(AH 7 0xaeb81e4e6015e80558000cd7a6702c180afa02b2000345df1c1966065681918000d1b9f7069581a4a0682000347669c29b60a62828d8000d1671).toArray⟩
theorem h6:check 5 6 d6=true:=by decide+kernel
def d7:Row:=⟨BCurve 56 44 0xffa02ef8fd2aaeb41a553eb68603970db0e5e4f5de33119f6147c882247bbfbf321205e491a8a460cd4a0daaacb7ed8e95768992111107050048b885a337b7597c0000000000000fc99d248c2c800300000000000003594638129ad00080000000000000b00949c08aa00010008,decode 5 1 0x76bad69e3365792597680165f0000300002000010008,(AH 7 0x2bad078cd8057a015a000335e4980b0a02b6000335da1c1986065e81928000d1b837069d81a6a068a0003475edc29d60a6a828f8000d165f).toArray⟩
theorem h7:check 5 7 d7=true:=by decide+kernel
def d8:Row:=⟨BCurve 56 44 0x1041ebc0067e6aeb01a553eb686039f2a4ad95f245e19119f6147c88227134557d4af95df91a8a460cd4a103f0479336891754aa212df07bf0056029d054147593400000000000012d822898e620003000000000000040be774731c900080000000000000d87191a0a8280010008,decode 5 1 0x76bac69e196577e597540164d0000300002000010008,(AH 7 0x2bac07865c0586015e80568000d177e702c580b0a02ba000345d51c1996066281948000d1b68706a581a7a068e000347571c29f60a7282918000d164d).toArray⟩
theorem h8:check 5 8 d8=true:=by decide+kernel
def d9:Row:=⟨BCurve 56 44 0x1089d4907d2a2aeac1a553eb68603a746e4ccd952ddfe119f6147c88229aacaf0774d25da91a8a460cd4a12d35c3a79428d740bb214ad087900645cb6354b9158ec000000000000162aa86210c6000300000000000004cf88cdb3a9f000800000000000010519e0b8c8980010008,decode 5 1 0x76bab69dfe6576a597400163b0000300002000010008,(AH 7 0xaeac1dfe6016280568000cd76a702c980b1a02ba000345d01c19b6066a81958000d1b4c706a981a9a06960003474f5c2a160a7a82938000d163b).toArray⟩
theorem h9:check 5 9 d9=true:=by decide+kernel
def d10:Row:=⟨BCurve 56 44 0x10d1bd60f3d5eaea81a553eb68603af4929819cfb5de3119f6147c8822c42508919eab5d551a8a460cd4a1567b3fbbf1c8972ccc2167b09330073c6d133569558a400000000000019c12eae1358800300000000000005a42a43d442f0008000000000000136023708ebf00010008,decode 5 1 0x76baa69de3657555972c016290000300002000010008,(AH 7 0xaea81de36016280578000cd755702c980b1a02be000345cb1c19c6066e81978000d1b30706b181aba069e000347479c2a360a8282958000d1629).toArray⟩
theorem h10:check 5 10 d10=true:=by decide+kernel
def d11:Row:=⟨BCurve 56 44 0x1119a6316a81aaea41a553eb68603b765c3751729ddc7119f6147c8822ec836c074bfc5d051a8a460cd4a17ea6318a4293d717dd2184909ed008440edff625358580000000000001d9bb56d961980030000000000000689cbd6d4e79000800000000000016b2a949112300010008,decode 5 1 0x76ba969dc76574159717016160000300002000010008,(AH 7 0xaea41dc76016280578000cd741702cd80b2a02be000345c5dc19e6067681998000d1b14706b981ada06a60003473fdc2a560a8a82978000d1616).toArray⟩
theorem h11:check 5 11 d11=true:=by decide+kernel
def d12:Row:=⟨BCurve 56 44 0x11618f01e12d6aea01a553eb68603bf680829dad25dab119f6147c882315fbc59175d55cb11a8a460cd4a1a7ebad9ea0339703ee21a170aa70095cb0c996ecb581000000000000021ba3ca09909000300000000000007806d86b597d00080000000000001a492f9513b580010008,decode 5 1 0x76ba869dab6572c59703016040000300002000010008,(AH 7 0xaea01dab701658058a015e000345cb180b3a02c2000335c0dc1a06067e819a8000d1af7706bd81aea06aa00034737dc2a760a9282998000d1604).toArray⟩
theorem h12:check 5 12 d12=true:=by decide+kernel
def d13:Row:=⟨BCurve 56 44 0x11a977d257d92ae9c1a553eb68603c784a21d5500dd8f119f6147c88233e5a290723265c611a8a460cd4a1d0169f6cf0fed6eef47e9ce0301e03516d457d86f57c7d53bea5233f7e56f6ed6cd170e41ff21be50b6100a8652d017bfd38a4000000000000261cc4471c27000300000000000008880f537653b00080000000000001e23b65496768001000a,decode 5 1 0x76ba769d8f65718596ee555f114e4100e29000030000200001000a,(AH 7 0xae9c1d8f6016680578000cd718702d180b3a02c6000345bb9c1a160682819c8000d1ada706c581b0a06b20003472fdc2a960a9a829b8000d15f1).toArray⟩
theorem h13:check 5 13 d13=true:=by decide+kernel
def d14:Row:=⟨BCurve 56 45 0x47c5828b3a13aba6034aa7d6d0c079f0dcda43152bae4119f6147c882366b88c7cd0775c0c8d4523066a50fc20c89da0e50b6cbfaa4cd2c583a6a2bd6e48bbad5de7fbd1772520747d6b62317c481c8103bbf2423bcd3fb1c801fbb7138a20c97ab6ede79dcf366b8a43a6653c16e9c5fea1f3723f23723fcecc418810ed9860d805e07a79bc4f4983a0000000000000ab0d31847dce000c0000000000001341627a2e366001000000000000022423d8799660001000d,decode 5 1 0x76ba669d7265703596d9555de14e4018e282cca708c4100c1d000030000200001000d,(AH 7 0x2ba6075c98059a0162000335c0d80b4a02c6000335b65c1a36068a819e8000d1abe706cd81b2a06ba000347279c2ab60aa2829e8000d15de).toArray⟩
theorem h14:check 5 14 d14=true:=by decide+kernel
def d15:Row:=⟨BCurve 56 45 0x91ca4b9a2985574a06954fada180f5e24ae1b71477554233ec28f910471e2ddfe4fb90b7711a8a460cd4a2206c8309929556c48469e4dafdf798dd2833784a0ab9709a56334bb0f25f4eb00c203438fe1c2913b0415b9151b02703504713c4328c5e2a335d1c904e7964d0ca68826d2e1fb8eb1cf21c4f6af3988113572ca4c55d35d634f93967f307229487ff6d8d8195588101ebd05ebc5fcdb1ddb2aecba5c9cee17fcac49090fc0866a806864b99dcc4794b00000000000000beb753ba8bba000c0000000000001594a6872fdca001000000000000026a4c52e1c8400010010,decode 5 1 0x76ba569d55656ee596c4555cb14e3f18e272cca608c400cc1c24bd728ac400a580000300002000010010,(AH 7 0x2ba507555c05a6016680588000d16ee702d580b4a02ca000345b11c1a56069281a08000d1aa0706d581b4a06c20003471f9c2ad60aaa82a08000d15cb).toArray⟩
theorem h15:check 5 15 d15=true:=by decide+kernel
def d16:Row:=⟨BCurve 56 45 0x12813243bbdc6ae900d2a9f5b4301efc5b81dcffd2e9c0467d851f2208eddd54da0ac656d9235148c19a944912ee9afc6c12d5f12fe6020e1dfc8df7d4ee83ef56e227a12f09a43f7864afcad8f2e71f461b485b8163946562056de584e268da4469cf126fd30378414212194b1ae0da0845adeaa22bde80dfc30fe3e8305e31e59091f340cc933860dc8ac8ebe072709ce15419336b0ac399110a786c7807349cc86d3f794ae0000000000000d37177be9a60000c0000000000001809eacdf19a200100000000000002b4b4d481fd08001000f,decode 5 1 0x76ba469d38656d9596af555b814e3e18e262cca508c3f24c1b28ac300a57000030000200001000f,(AH 7 0xae901d386016a80588000cd6d9702d980b5a02ce000345abdc1a76069681a18000d1a83706dd81b6a06ca000347175c2b060ab682a28000d15b8).toArray⟩
theorem h16:check 5 16 d16=true:=by decide+kernel
def d17:Row:=⟨BCurve 57 45 0x4b246c50ca20aba3034aa7d6d0c03e7735fb1ad1cdd1a08cfb0a3e4408f7ae703256f896c3235148c19a92270c266a6342bd6998e947b45e3dc17fe9f1c4209e55a58efde5ea748c14996cbd0b49b0e3d9162dc81f52bb69df602272dace2592e3747d8de3a0110f31c6bb90ca492ba07264a239c66e07692fec0c3e94ef62f3d8f33f1a7263a3413cc1a96b884bc663b26df2448acf808ac299ff55cee53b25525041d7ae0ca56a19118e8724803f5b702b6e024a0f00000000000003a4ee7642a700003000000000000035425e9ce6ddc00200000000000003035d5d5a34b80010010,decode 5 1 0x76ba369d1a656c359699555a514e3d18e252cca408c3e24c1a28ac250a5600a0f0000300002000010010,(AH 7 0x2ba307469805aa0166000335b0d80b6a02ce000335a65c1a86069e81a38000d1a65706e581b8a06d20003470f1c2b260abe82a58000d15a5).toArray⟩
theorem h17:check 5 17 d17=true:=by decide+kernel
def d18:Row:=⟨BCurve 57 45 0x4c440f92a4cfaba2034aa7d6d0c03ef75a46670c55cfc08cfb0a3e440901c6090fc24cd6ae235148c19a92298ed587484f7168493a9c67b56d43dc2d3735485655929413801280143a23bf0b4173fce3c968f284ce79bd8d3f1fb0ca7a0e249822a25e2aabc1876a9daf96c0ca39803a1487173be22915f537ba4c3d9a3e046eea4b5d0e54a821fd04c199c17ebfcbe3343ed89b23baeb8ac19f9cc59bf79b42fcb000636508a55aa112758781804555fa86f2374a0e00000000000004005714c2e76800300000000000003ab4e8116ab5c002000000000000035645ed6a6f500010010,decode 5 1 0x76ba269cfc656ae596845559214e3c18e242cca308c3d24c1928ac150a5500a0e0000300002000010010,(AH 7 0x2ba2073f1c05b6016a80598000d16ae702dd80b6a02d2000345a11c1aa606a681a58000d1a47706ed81baa06da000347069c2b460ac682a78000d1592).toArray⟩
theorem h18:check 5 18 d18=true:=by decide+kernel
def d19:Row:=⟨BCurve 57 45 0x4d63b2d47f7eaba1034aa7d6d0c03f75d93dc7de7dcdd08cfb0a3e44090b9724680e7f1698235148c19a922c1184a42d5c2566e98bf11b0c9c463847c58f1105957f99291a3a8b945fab8ce3fd2c14e3b9bbb7417da0bfb0755f01e20d0e239d61d03ec76be2fb2e05c44038ca29d4d3b6a98bbdfdb9db1e17e34c3c9f8ca5e9fbab7aff8d4f15afd4c18a177533d162360f9457e3f0814ac0a53a356909fb60a44140d7de34a54aa03c8835e02abc0bf336fee38a0db29135c87de804b948555f69ac79e000000000000045fffba7b2ab80030000000000000406b71f96ebc400200000000000003ad6e84b2acd00010011,decode 5 1 0x76ba169cdd656985966e5557f14e3b18e232cca208c3c24c1828ac050a544ca0d0079e0000300002000010011,(AH 7 0xae841cdd6016e80598000cd698702e180b7a02d60003459b9c1ac606ae81a78000d1a29706f581bca06e2000346fe1c2b660ace82a98000d157f).toArray⟩
theorem h19:check 5 19 d19=true:=by decide+kernel
def d20:Row:=⟨BCurve 57 45 0x4e8356165a2daba0034aa7d6d0c03ff4583528b0a5cbe08cfb0a3e440915683fc05ab15682235148c19a922e828b1cb19b916589dd45ce63cbc894399cd181ca156b9e3eb462971c8530d6473ee318e3aa0e7bfe2cc7c1d3821e15b9938e22a2a0fe1f642c046c596a04e8f0ca1a296d58cc00c0192056e3d6738c3ba4db47650d0b98ee1c587e2ea4c17a6d6ba7d6e137e0257acb72d78abfaad7a5361c5b7e490403351994a53afb53a44b3cac033625663c6bca0cbb11443883b80521710987b2cc79500000000000004c3e8676b70f000300000000000004665fc54f2f140020000000000000408d72332ed380010011,decode 5 1 0x76ba069cbe65682596585556b14e3a18e222cca108c3b24c1728abf50a534ca0c007950000300002000010011,(AH 7 0x2ba0072f9805ba016a000335a0980b8a02d6000335961c1ae606b681a98000d1a0b706fd81bea06ea000346f59c2b960ada82ac8000d156b).toArray⟩
theorem h20:check 5 20 d20=true:=by decide+kernel
def d21:Row:=⟨BCurve 57 45 0x4fa2f95834dcab9f034aa7d6d0c04072d72c8982cdca008cfb0a3e44091f395b18a6e3966c235148c19a9230f3919535dafd642a2e9a81bafacaf002bcfc93869557a3544e8aa29caab39b350627f8e39a6140badbeec3f6655cec510dce21a7e02c0000f425daecca71c1d0ca0a7e06faee7542345c89466d5f4c3aaa29e8e01e6bb6da01c45b7974c16ac3621bdc60b9b08c03da44824abeb07515032ebb9beaf8477b172ca52b566ac060992d74b3c0e9c0550a0bb9f0aacff99ad6e8e5a0c91930794ba08df671d8aa978ca2388c45c776c39152a88988058dd9c4e7fed46ee000000000000052c111b93ba1000300000000000004ca48723f754c00200000000000004687fc8eb30880010013,decode 5 1 0x76b9f69ca06566c596425555714e3918e212cca008c3a24c1628abe50a524ca0b0479448776006ee0000300002000010013,(AH 7 0x2b9f07281c05c6016e805a8000d166c702e580b8a02da000345909c1b0606be81ab8000d19ec7070581c0a06f2000346ed1c2bb60ae282ae8000d1557).toArray⟩
theorem h21:check 5 21 d21=true:=by decide+kernel
def d22:Row:=⟨BCurve 57 45 0x50c29c9a0f8bab9e034aa7d6d0c040f15623ea54f5c8308cfb0a3e4409290a7670f315d656235148c19a923364980dba1a6962ca7fef35122a4d4ba326104d575543a869e8b2ae24d033dbad536bbce38ab405778b1546191f1b85a5540e20ad1f59e09db44746e8270a6900c9fad2a09d10ea444f6e7245e2b18c39af788a5b2fc3d4c33d92ad654cc15b19588fe1dfbb80c7f3106058cabdb61284d04123b98a1e0da9ff1ca51bb181dc75f5aee603d3a0b31f4a0abfaa00bea902ed791d9ed5ae54793bfe940665142bf34569261cb8c775cc1161188f5805fe8287804dc46ed000000000000059879d6f406180030000000000000532712667be6c00200000000000004cc6875db76c00010013,decode 5 1 0x76b9e69c83656565962c5554314e3818e202cc9f08c3924c1528abd50a514ca0a0479348775006ed0000300002000010013,(AH 7 0xae781c8360172805a8000cd656702e980b9a02de0003458b1c1b2606c681ad8000d19cd7070d81c2a06fe000346e45c2be60aee82b18000d1543).toArray⟩
theorem h22:check 5 22 d22=true:=by decide+kernel
def d23:Row:=⟨BCurve 57 45 0x51e23fdbea3aab9d034aa7d6d0c0416fd51b4b271dc6708cfb0a3e440932db91c93f481640235148c19a9235d59e863e59d5616ad143e869594fa71ad80ca820d52fad7f82dab9a4f5b197b0263d5ce37b06ca343a3c483baf59e1bcb5ce1fb25e87c13a7468b04b7fcf0f70c9eb273a3f335f466a5611e23364cc38b4c72bd64123f2a9cfc374481cc14b6f4f03e75f3d50d9486dcb838abcbbaff49d5383d7267555c18110a50c0c98f88b523057265d8b14ca8a09c56356ad587304067926d42788792c5c9a1658502d4ecf2fcd2ed88774d4916f88952806736b51509f9c6ec000000000000060922998c5508003000000000000059ed9e1c80a740020000000000000534912a03bfe00010013,decode 5 1 0x76b9d69c6765640596165552f14e3718e1f2cc9e08c3824c1428abc50a504ca090479248774006ec0000300002000010013,(AH 7 0x2b9d0719d805ca016e00033590180baa02de000335859c1b4606ce81af8000d19ad7071581c4a0706000346db9c2c060af682b38000d152f).toArray⟩
theorem h23:check 5 23 d23=true:=by decide+kernel
def d24:Row:=⟨BCurve 57 45 0x5301e31dc4e9ab9c034aa7d6d0c041ecaebec090e5c4a08cfb0a3e44093c662f9c6c585629235148c19a923846a4fec299415ffb22989bc088d20269d2f1aafe551bb2951d02c5251b2ccf3d7ed564e36b598ef0e9634a5e161800940b4e1eb79db5a1d73c8a1716d4bfe5fcc9db7bd3e155d3c88513681b5c744c37ba15cd515284108db856aff6ecc13bc54577ecde3f20c003f280da8abbc14d646a65e3f4bffe1fc1c53ca4fc67b014a0aeb1c81b5ea8e556ca08cb1cac9c07db1a90f838c44924791cbaa0264b8baeaa29f62dbf2e4773dd117df89af806ec942258f45c6eb000000000000067e0b635ca6e0003000000000000060f82a460596400200000000000005a0f9e5640be80010013,decode 5 1 0x76b9c69c4a65629595ff5551b14e3618e1e2cc9d08c3724c1328abb50a4f4ca080479148773006eb0000300002000010013,(AH 7 0x2b9c07129c05d60172805b8000d1629702ed80baa02e20003457fdc1b6606d681b18000d198e7072181c7a070e000346d29c2c260afe82b68000d151b).toArray⟩
theorem h24:check 5 24 d24=true:=by decide+kernel
def d25:Row:=⟨BCurve 57 45 0x5421865f9f98ab9b034aa7d6d0c0426b2db621630dc2d08cfb0a3e440946374af4b88a9613235148c19a923ab7ab7746d8ad5e9b73ed4f17b7d45d9016bf4ed49507b7aab72ad0ad40a582555d6c44e35bac53ad988a4c805355e22b544e1dbcdce38273fcab7b4a25dc8ae4c9cbd06d837848ca9fa674f163e9cc36bf646ecc63dc2e6ef74c6046d0c12c1b3bebf25d40f07c259e82f18abac6ead43778441256b86baacb9ca4ecc2c730b60b3338e2d6fa24c40a07d0d6028ab74331189ad4a63104790d18a6363ec7300555bc47cf760772e5918c68a0c80769fcfa994c046ea00000000000006f7343464fba000300000000000006846b6e30ab3c0020000000000000611a2a7fc5ad80010013,decode 5 1 0x76b9b69c2d65613595e95550714e3518e1d2cc9c08c3624c1228aba50a4e4ca070479048772006ea0000300002000010013,(AH 7 0xae6c1c2d60176805c8000cd613702f180bba02e60003457a5c1b8606de81b38000d196e7072981c9a071a000346c99c2c560b0a82b88000d1507).toArray⟩
theorem h25:check 5 25 d25=true:=by decide+kernel
def d26:Row:=⟨BCurve 57 45 0x554129a17a47ab9a034aa7d6d0c042e8075996ccd5c0f08cfb0a3e44094fc1e8c7e59ad5fc235148c19a923d28b1efcb18195d2bc542026ee756b88da3759abe54f3bcc05152dc2d661bb0f7c19110e34bff186a47b14ea267138682910e1cc21c116310c4ccdce573255fe0c9bc2507259abd4cba0f386443bc0c35c4b31047753c4c4d8ca4858da4c11c71325ff7dcc2c00dad71d45c4ab9cc8844048aa42feaa4397c942ca4dd1dde4ccb67b4a97cc67ed3124a06d68f587966b3479d60fa79fce478fd76ac463202b16052821b5faf0771ee119ad8a69807eba5da11a6946e900000000000007749d0ca5534800300000000000006fd943f38fffc00200000000000006868b71ccacb00010013,decode 5 1 0x76b9a69c0f655fc595d2554f314e3418e1c2cc9b08c3524c1128ab950a4d4ca060478f48771006e90000300002000010013,(AH 7 0xae681c0f60176805c8000cd5fc702f580bca02ea000345749c1ba606e681b58000d194d7073181cba0722000346c09c2c760b1282bb8000d14f3).toArray⟩
theorem h26:check 5 26 d26=true:=by decide+kernel
def d27:Row:=⟨BCurve 57 45 0x5660cce354f6ab99034aa7d6d0c04364e0fd0c369dbf108cfb0a3e4409594c869b12ab15e5235148c19a923f880fc3ee8a3d5bbc1696b5c616591362791487a1d4dec1d5eb7ae7b58b8f5b24abb4ace33c51dd26f6d7d0c45150ed969b0e1bc75b3f43ad84ee3be8bc9a0344c9ac79a0c7bd324ed44db27401f38c34ca01b1c2869c6a29785f1fa074c10cc728d3fd5bc48f749b6c6ff3cab8d225b3d19d044d7bc189371ef0a4cd78f568e0c43619e92d36f0418a05dc48ae68161b5e1f4aaa3f713c78edd4b256253e32bb2047a86fd98770f691a948ac6808718ec0c2040c6e800000000000007f645ec1dadd8003000000000000077afd177957a400200000000000006ffb442d501700010013,decode 5 1 0x76b9969bf1655e5595bb554de14e3318e1b2cc9a08c3424c1028ab850a4c4ca050478e48770006e80000300002000010013,(AH 7 0xae641bf170179805da017200034579580bda02ea0003356edc1bc606ee81b88000d192d7073d81cea072a000346b75c2ca60b1e82be8000d14de).toArray⟩
theorem h27:check 5 27 d27=true:=by decide+kernel
def d28:Row:=⟨BCurve 57 45 0x578070252fa5ab98034aa7d6d0c043e1baa081a065bd208cfb0a3e44096290a6e9209955ce235148c19a9241e76d9811fc615a3c67eb691d45db6e0e979c1c9814c9c6eb85a2f335b10080dc1b663ce32ca4a1e3a5fed2e6120e176dbf4e1acc9a6d244a450f9854023aa5e8c99cce3a69dfa750ee61e3209b8c0c33cf50533d97f48802ba7c2e5468c0fd1d1f4802db465eb0ef8e5ade4ab7d7c3239eaf6c6b0a105ada93f8a4bdd40c84f620b78a280b227c520a04e2020456c58b749e57e3f6c99478de32b8661879b415bf0ceefff5c76fff11b7b8b23808fbb7aeaa646c6e7000000000000087c2ed2ce0b5000300000000000007fca5f6f1b234002000000000000077d1d1b1559180010013,decode 5 1 0x76b9869bd2655ce595a3554c914e3218e1a2cc9908c3324c0f28ab750a4b4ca040478d4876f006e70000300002000010013,(AH 7 0xae601bd26017a805d8000cd5ce702f980bda02ee00034568dc1be606f681ba8000d190c7074581d0a0736000346ae1c2cd60b2a82c18000d14c9).toArray⟩
theorem h28:check 5 28 d28=true:=by decide+kernel
def d29:Row:=⟨BCurve 57 46 0x162804d9c2952ae5c06954fada18088b9dde017439b76608cfb0a3e44096c1b44bc4da995b611a8a460cd49222365b61ab742ac632e50071d1d3772247fc314a2152d198023f95fd7bacde443c222d29c62cf766a05525d507a94b0404d74e1968eccd827386987913a203bc4864c348b5030086f4c212f29a8360830c9a93de97152a94bb2a5f763fe7981cd7315bc085a482dc2a9d78ff64ab66eb049b5e0e6444ac85733519052538bc8e842df4e3e8e58105dd0d280dcf76b48ae9e71635114f3f94d0f18e90be760bb535702ed1ef1003876e83c8e3145c0404c51051e563da373000000000000024195f02d9aec000c00000000000011051dbb441f5800400000000000007fec5fa8db3a80010013,decode 5 1 0x76b9769bb3655b65958c554b414e3118e192cc9808c3224c0e28ab650a4a4ca030478c4876e006e60000300002000010013,(AH 7 0xae5c1bb36017a805d8000cd5b6702fd80bea02f2000345631c1c1606fe81bc8000d18ea7075181d3a073e000346a49c2cf60b3282c38000d14b4).toArray⟩
theorem h29:check 5 29 d29=true:=by decide+kernel
def d30:Row:=⟨BCurve 57 46 0x166fedaa3940eae5806954fada18089b0467f2b466b72608cfb0a3e4409755f650a5b97d59e11a8a460cd49235314a02c7054aba342a533f2e91808bb2bd94c22d527da22d73e6147bf7b67dd518a9d9c60d4a2b5d044cd7291707b35be2ce186b8c6472c1e6a924b141000cd664bb5ddb6b8924354882da141777330c5b3db2c677569875a83bb54ec1981adc90c300dd949fca9ca4811ce8ab5717f019c6a16530f2141edba3c524ba28eaf48366e9a874b24f84572809dae9606848c74327b9ea755e60f16eeec485fef0b6ca6f96a8a002c76d8808ea4c5eec050e64d01196f23728000000000000265302d75b3be000c00000000000012196f9714e0180040000000000000884aee13e11200010013,decode 5 1 0x76b9669b936559e595745549f14e3018e182cc9708c3124c0d28ab550a494ca020478b4876d006e50000300002000010013,(AH 7 0x2b9606e4dc05f6017a805d8000d159e7030180bfa02f60003455d1c1c36070a81bf8000d18c87075981d5a074a0003469b1c2d260b3e82c68000d149f).toArray⟩
theorem h30:check 5 30 d30=true:=by decide+kernel
def d31:Row:=⟨BCurve 57 46 0x16b7d67aafecaae5406954fada1808aa9f9c61619fb6e608cfb0a3e44097ea385586986158711a8a460cd492482c38a3e2966aae356fa60c8b4d89f47aa29abe225229ac58a8362b8c4289ae831b2401c5ed9cf019b373d94a5b442572e20e176e2bfb631046b9cf02de125d0464b37301d411c155cee82f34e1a5630c1be786f5d9819c2fd0e442f1c21818e1f02a41358cbcb6650dfe2f8cab4744db982f34661d212ed9c84045243b954764d8d8ef674dc066e7252805e65c0c45a7977014a9998e7900f14f4cca95f22c3824815b1baff3876c8c48f18461d40559d951d9cb7e3720000000000000289da6c8bcd4a000c0000000000001336418155a6a8004000000000000090ed7cf2671800010013,decode 5 1 0x76b9569b73655875955c5548a14e2f18e172cc9608c3024c0c28ab450a484ca010478a4876c006e40000300002000010013,(AH 7 0x2b9506dcd805fa017a00033561d80c0a02fa000335571c1c56071281c18000d18a67076581d8a0756000346915c2d560b4a82c98000d148a).toArray⟩
theorem h31:check 5 31 d31=true:=by decide+kernel
def d32:Row:=⟨BCurve 57 46 0x16ffbf4b26986ae5006954fada1808b9d17bd534c0b6a408cfb0a3e440987e7a5a67774556e11a8a460cd4925a99e221f7bd4aa236b4f8d9e80b935c9fab435a5f51d1b683dc86428c8d57d64628ba31c5cdefb4d6629a5b6b76005a46afce1670cb92535eaaca7808793ac53064ab88283c9a5e965542f1fce36c930bdc915b253bad9fe9a4591f339c9816e74f91818d7cd99f83d9efe518ab3771c71697c7670939d5a3faee4523bd01a3d52e4af52570ab4c05762801f1ceb82306679cfbe05c8b2020f12faad0a5e567b97e641f483fd6076b9088f8bc64bc05a76dd73e017e37180000000000002af94ad6fe790000c000000000000145b937a067308004000000000000099d40c446d4c80010013,decode 5 1 0x76b9469b526556e595445547414e2e18e162cc9508c2f24c0b28ab350a474ca00047894876b006e30000300002000010013,(AH 7 0xae501b5270181805fa017a0003455b980c1a02fe000335511c1c86071a81c38000d18847076d81daa0762000346879c2d860b5682cc8000d1474).toArray⟩
theorem h32:check 5 32 d32=true:=by decide+kernel
def d33:Row:=⟨BCurve 57 46 0x1747a81b9d442ae4c06954fada1808c93805c674edb66008cfb0a3e4409912bc5f48562955611a8a460cd4926d94d0c3134e6a9637fa4ba744c79cc421d78e7a88517dc0af10d6599cd820f51e424dd9c5ae42799311c15d8c673c51dd968e15736b2943ad0adb1fc21279149a64a39d4ea522fbd6db93226c1c0c030b9d3b2f549dd9a3a3229a4a0ef71814ecaef8c1e574f685f908568fbcab279eb295005aa7f53c087d74edc5233e6e004583bcfae2dd72fedf4c27fdfd4164006547c9dd5e336b8f10f11008d6b5d8a3bad817e32e5162476a94c8fff467a405f722603e38f237100000000000002d65ef0220290000c000000000000158965812745380040000000000000a2fe9c09f3af80010013,decode 5 1 0x76b9369b30655565952c5545f14e2d18e152cc9408c2e24c0a28ab250a464c9ff047884876a006e20000300002000010013,(AH 7 0xae4c1b3060182805f8000cd5567030980c1a02fe0003454b1c1ca6072681c68000d18617077981dda076a0003467ddc2db60b5e82cf8000d145f).toArray⟩
theorem h33:check 5 33 d33=true:=by decide+kernel
def d34:Row:=⟨BCurve 57 46 0x2f1f21d827dfd5c900d2a9f5b43011b13d1f6f6a356c38119f6147c88133452d17ae85daa7c235148c19a9250004f48250ea9513727f3ce9430b4c56024ef875f0a24b95b48a4ce13a45ca1616cdfb338b1d2a7c9f81d0bf5a5df01868e19c28ec158067f6d5d78c5f539ac748c93764ea1b5731eec3b1810515864616bbca070800094eb8974f86fcf13025e41cc0047aca26d3893263ba91562f973c26d1db51c24f8ecc677dca457fb4b96bb25e013f282efee94c4ff411681fbb882fed72463c5e9e51e1e0cdb98b97be7863394d9bc24f0ed3240781532bec1fb4b64071c3b46e19909072c6a8c0648f6ecda71da36a00000000000002fe3934a21e4a000c00000000000016bfb796b81d380040000000000000ac6d2c42fa4100010014,decode 5 1 0x76b9269b0e6553e595135544914e2c18e142cc9308c2d24c0928ab150a454c9fe0478748769446e1006d40000300002000010014,(AH 7 0xae481b0e60182805f8000cd53e7030d80c2a030200034544dc1cd6073281c98000d183d7078581e0a077600034673dc2dd60b6a82d28000d1449).toArray⟩
theorem h34:check 5 34 d34=true:=by decide+kernel
def d35:Row:=⟨BCurve 57 46 0x2faef379153755c880d2a9f5b43011cfa0de5710776bb0119f6147c8813464e170cc5f62a4a235148c19a92524e0477e7b3854fa7509e283fc835f227b3618feaaa19baa0af2ed0f5adb48301b2f55638addd00618e01ec39b9a6712967e1c26f154ae48939df8d6a27e6f954cc9278f36ec686c6fd0279880622626163d1daf66c461562a3f031719a73021eedb8e852aba6095cd19043fd9560ff11323a3015399fa24bc71430a44828d724c5d420cb729319b8b084fec284d777645f0471e5e39adae01e1a189c5ab7e357b15e4d44de1bd0ed12a8439b133ebcf5b6b6dc066c06e09d490e646d74069ceb7d12ac363108000000000000327237af03abe000c00000000000017fe89bab8fb080040000000000000b61fbcef810100010014,decode 5 1 0x76b9169aec65525594fa5543314e2b18e132cc9208c2c24c0828ab050a444c9fd0478648768446e0006210000300002000010014,(AH 7 0xae441aec6018680608000cd5257031180c3a03060003453e9c1cf6073a81cb8000d18197079181e3a0782000346699c2e060b7682d58000d1433).toArray⟩
theorem h35:check 5 35 d35=true:=by decide+kernel
def d36:Row:=⟨BCurve 57 46 0x303ec51a028ed5c800d2a9f5b43011ee049d3eb6b96b24119f6147c881358495c9ea38eaa18235148c19a92549bb9a7aa58614e17794881eb5ff71edae647ec7eca0ebbe615b8d3d5b70bc3849a6e7f38a9e758f923e6cc7dc83dd9244019c24f693dc29305e1a1e4da57031d8c917b983bd79a6b0dc888b4a1af5c615be7157c588b95d9b3c4f44695c301df99a5d05da9a9a52bdc48e0b0155f04aea207427557177d2cb072bca4385662b2d0826182dbdedd3a3cc4fe43f32cf310390a0bf045ec36021e16245d1cb64ac7dc8325a73010d8ecf3100f20f3beb92503d150f0a746dfa189159c705c06f30010e6e8062cb00000000000003511dc30c57ec000c0000000000001945dbed29dea80040000000000000c0164e0f87ef80010014,decode 5 1 0x76b9069ac96550c594e15541d14e2a18e122cc9108c2b24c0728aaf50a434c9fc0478548767446df005960000300002000010014,(AH 7 0xae401ac96018680608000cd50c7031580c4a030a000345385c1d26074681ce8000d17f57079d81e6a078e0003465f5c2e360b8282d88000d141d).toArray⟩
theorem h36:check 5 36 d36=true:=by decide+kernel
def d37:Row:=⟨BCurve 57 46 0x30ce96baefe655c780d2a9f5b430120bff072b82e36a94119f6147c88136a44a230812729e4235148c19a9256d7c6330c2ff54c87a1f2db96f7784b79bda29990ea033d2b7c42d6b7c06262ea23675238a5f1b190b9cb9cc1d1a53976b241c22fbd30a09cd263b6360c89cfe4cc907e3d08e8ae131e8d4596242f6c6153fc500244d11650b8f340eec11301a04592b868a7ad40a5b35016e3155d0a4c11d454d5748c898f829378a42883ee40db30623a2e663a724904fdc561826ebc130fa5438aba02b41e12301ddeb4b23807a21e00b20418ecd377daa6d43eb62cb746dd7f7606dea5c91cd47344074b34a857254a293800000000000037c280cf675d4000c0000000000001a95ae2e0ac8180040000000000000ca50dfa30f0c80010014,decode 5 1 0x76b8f69aa5654f2594c85540614e2918e112cc9008c2a24c0628aae50a424c9fb0478448766446de005270000300002000010014,(AH 7 0x2b8f06a95c0626018680608000d14f27031980c5a030e000345321c1d56074e81d18000d17d0707a981e9a079a00034654dc2e760b8e82db8000d1406).toArray⟩
theorem h37:check 5 37 d37=true:=by decide+kernel
def d38:Row:=⟨BCurve 57 46 0x315e685bdd3dd5c700d2a9f5b430122a62c61329256a00119f6147c88137bb2ecb8207ba9b2235148c19a9259257b62ced4d14ae7ca9d35428f39780439719aab49f83e70e2ccd997c9b861324dc3ac38a1fc0a284fb07d05d5dc92218769c21011237ea69e65ca5dbe7f59954c8f80e1d5f9c1bb2f50b02c8d8a84614c118a88311676c7b37b176971930160f17fa073a6b0dbca56a5ebb7955b0fe981a1673591fec7743d7668a418b179cee5dea2f16a293162b664fd46cfd7ea67ef153ddfb204485a1e0e3bdea0b319a832bb365163f580ecb3dfa62cb4beb3c46a0faf5a7ec6ddaa09240c762c07a5894363640226580000000000003a84258ae9476000c0000000000001bee007d5bb7580040000000000000d4cf71aa165800010014,decode 5 1 0x76b8e69a80654d9594ae553f014e2818e102cc8f08c2924c0528aad50a414c9fa0478348765446dd004cb0000300002000010014,(AH 7 0x2b8e06a018062a018600033536580c6a03120003352b9c1d76075a81d48000d17ab707b581eca07aa0003464a1c2ea60b9a82df8000d13f0).toArray⟩
theorem h38:check 5 38 d38=true:=by decide+kernel
def d39:Row:=⟨BCurve 57 46 0x31ee39fcca9555c680d2a9f5b43012485d2ffff54f6974119f6147c88138d21373fbfd0297e235148c19a925b6187ee30ac654947f3478eee26faa47a59b4ee08c9ecbfb64956dc79d30dbe5d199fae389e0662bfe5955d49d4e3e3245b09c1f065165cb06a67de5bf037a339cc8e8386a30ad55f4012c877dda89c614426c50e1d5bf73ea35c77b7fcf301219d6c887ea4b47699c64a54eb15591586f16e799daf6e36dae14370a408df055cf08ce3a88f27c20a9464fcc83e2d6613c91ad5c4bbcaf82b1e0a479f62b181185dce6e9945e520ec944771b2953eb1d93f29a22023c6dcae492b4479140801fde20ba42e23f80000000000003d56ca634b3d2000c0000000000001d4ed2db1cac680040000000000000df9204249dd200010014,decode 5 1 0x76b8d69a5d654bf59494553d914e2718e0f2cc8e08c2824c0428aac50a404c9f90478248764446dc0047f0000300002000010014,(AH 7 0xae341a5d7018d8062a01860003452fd80c7a0316000335251c1da6076681d78000d1785707c181efa07b60003463f5c2ed60baa82e28000d13d9).toArray⟩
theorem h39:check 5 39 d39=true:=by decide+kernel
def d40:Row:=⟨BCurve 57 46 0x327e0b9db7ecd5c600d2a9f5b43012665799ecc17968ec119f6147c88139e8f81c75f24a94a235148c19a925d9d94799283f947a81bf1e899be7bd0dc1e6c91e489e140fbafe0df59dc627a6a86df39389a10bb577b7a3d8dcebb2c7f2d19c1d0b9093aba36e9f230a1b2afdbcc8d862b701be90750d38e7814b9c4613c3bff9409a177b5889761d9b84300e249597089a3b81114023d5cbf15571b24613b8bfdccdad7c36daac4a3f90c90eafb3b245f9d61ec69e2c4fc49ac82e1bfa5206cf2a80e20ef1e06536024afe88888dbc6d857d2f8ec74af3d3875beb04b932ed1f0e886dbb289327c7bfc086092844fe5ce21f8000000000000403a6f588d3e8000c0000000000001eb825474da7480040000000000000ea989712a57a80010014,decode 5 1 0x76b8c69a3b654a55947a553c214e2618e0e2cc8d08c2724c0328aab50a3f4c9f80478148763446db0043f0000300002000010014,(AH 7 0x2b8c068ed8063a018a00033529580c8a031a0003351e9c1dd6077281da8000d175e707d181f3a07c2000346345c2f060bb682e58000d13c2).toArray⟩
theorem h40:check 5 40 d40=true:=by decide+kernel
def d41:Row:=⟨BCurve 57 46 0x330ddd3ea54455c580d2a9f5b43012845203d98da36860119f6147c8813af70d144c0352916235148c19a925fc7f860938e4545f8449c4245563cfd29879889c829d54241166ae23be5b6955a959e6a38961b13ef115f1dd1c3626e31fda1c1b10cfc18c402ec05dbd2f079680c8c88d03d2cfcab6193022d328df26134513a19f5e6d82c632bd5cdf8f300a2f5465894a1bbab390a7ef8f3955520c1d1089e5dea44aa2de2d44ca3e93a1c7905e9651694d7b080a1a4fbcb1ad85d6b7f26036976cdb3de1e025f20e6ae4ff8b3e33f0e99bef8ec551708be563eaf030fe18b146e86dab6c939b47ee408c1472a3028e22040000000000000432f146aaf4b8000c0000000000002029f7c1eea7f80040000000000000f5e32a742d5180010014,decode 5 1 0x76b8b69a186548b5945f553aa14e2518e0d2cc8c08c2624c0228aaa50a3e4c9f70478048762446da004080000300002000010014,(AH 7 0xae2c1a18701918063a018a00034522d80c9a031e00033517dc1e06077e81dd8000d1737707dd81f6a07d2000346295c2f360bc282e98000d13aa).toArray⟩
theorem h41:check 5 41 d41=true:=by decide+kernel
def d42:Row:=⟨BCurve 57 46 0x339daedf929bd5c500d2a9f5b43012a1e318cb7fb567d4119f6147c8813c0df1bcc5f89a8e0235148c19a92620404ebf565d944586d469bf0edbe29629538d22a89c9c3867cf4e51bef0a0f2d45c1263892256c86a743ee15b2d9a83c6841c19160eef6cdceee195d83f102e7cc8b8b750a3e10537251239737552c612c66749fe22c58a33319d39614530063a133409f9fbf4508df0f2ea91553265f40d5b0be07abae1a40c004a3d967a8071097a5cd75890e4ed124fb4c892dd9175b2b99292809bfbf1dfe6ae1a8acb778dee4d73c0bdff8ec357ed44436beadefafa918aab806d9bb0940ec81cc09241bd3ac6d6a1ec00000000000004634b999b1642000c00000000000021a44a4affae7800400000000000010171be49355700010014,decode 5 1 0x76b8a699f565470594455539314e2418e0c2cc8b08c2524c0128aa950a3d4c9f60477f48761446d9003d80000300002000010014,(AH 7 0x2b8a067d58064a018e0003351c180caa0322000335115c1e46078a81e08000d170f707ed81f9a07de0003461ddc2f760bd282ec8000d1393).toArray⟩
theorem h42:check 5 42 d42=true:=by decide+kernel
def d43:Row:=⟨BCurve 57 46 0x342d80807ff355c480d2a9f5b43012bf742dbd71c76740119f6147c8813d133703f825628aa235148c19a92642e68d2f67025429895f0f59c857f5587474d6e9469bdc4cbe37ee7fdf85ce7e2976387388e2fc51e3d28ce599d20da9f35b9c171b4e1d4d79b702cb5b4b44f64cc8a8e19d74f23fb830df2b622f76e61247baf25ce71d919f8615b315fb300244d2028aa9ec2de837fee02fc95512bfcb0a2c31e250fe388876df4a3c99533951b45e6843f7605d47104facdf78354c335312e31bbc235cd1dfa76a26aab1ee909e08f60adc850ec15e69fca173eaecbb8da4239e686d8bf49482484b409891080c4b3661eb8000000000000494b5ee593886000c00000000000023271ce280bac800400000000000010d445291bd8b00010014,decode 5 1 0x76b89699d065455594295537b14e2318e0b2cc8a08c2424c0028aa850a3c4c9f50477e48760446d8003d70000300002000010014,(AH 7 0xae2419d0701958064a018e00034515580cba03260003350a5c1e76079681e38000d16e7707f981fda07ee000346125c2fa60bde82f08000d137b).toArray⟩
theorem h43:check 5 43 d43=true:=by decide+kernel
def d44:Row:=⟨BCurve 58 46 0x697aa442da95ab8801a553eb686012dd0542af63d966b0119f6147c8809f10a5fde71b3543a11a8a460cd489996332e7dde9c503a2fa6d3d207381032f3bacb6fa53638c229411d5ba04b1dda8ec80e8388a31e736537e1806b54d9d5ac9a8e208e876d74c369d3b04700ab4035382a411a965c2ce723fe4653a58cc4c8990bea460379dc9e4b7c4faae5c308e4874d5dd5b96642cc09b27cc24bff93e43442d6718cef51da36d7652a9e633440dfaaf642714a78b6de14a3b9c2bf2325f4139d794f4b88c0c27d27b2ec6837874db0a0cc7dc75ac77da098cb2a6195269accef8ff5dd1d7ec9cd69fef7d2fa78e278ed73d46d7c3894f5c879c04f81298bc7d6b0f58000000000000131cc113956e1000300000000000004964df10e399d00080000000000001195ae74dc5ed80010015,decode 5 1 0x76b88699ac6543a5940e5536314e2234e2018e0a2cc8908c2324bff28aa750a3b4c9f40477d4875f446d7003d60000300002000010015,(AH 7 0x2b88066b18065a01920003350e980cca032a000335039c1ea607a681e78000d16be708098201a07fe000346069c2fe60bea82f38000d1363).toArray⟩
theorem h44:check 5 44 d44=true:=by decide+kernel
def d45:Row:=⟨BCurve 58 46 0x1aa691e12d512ae1c06954fada1804be8b40a99ef4d9860467d851f22027e4d228600c66507846a291833522687187fc97b7753f28e745a8f3b4a0d6c9cc69ce36b4d2a3c12790280c82be26036528310e21911d935a3ca1dc2c43e50d998138264b98f21d6667452e995832227cc88936371714b45d241cd09575a86308a531218d37e5681d8bf41f83700bfe9693e7e3026d9420f24d2ee60c2a9a6e6f2079cfc65fcfe2eacf3834a3a9f04ab130a253f8c781610301427ce86a17260d754f158762aa1f7e077ca388fba9fb712bf8cbf1f032751d7ad6c6dabb07d30832f90fe82bc86d6c7c956948a84052cacf2e4a1dd0f5400000000000013eaea74fdfcf000300000000000004c8c8479a5c9b0008000000000000125b57c7d4e7e80010014,decode 5 1 0x76b87699866541e593f25534a34e2118e092cc8808c2224bfe28aa650a3a4c9f30477c4875e446d6003d50000300002000010014,(AH 7 0xae1c1986701998065a019200034507980cda032e000334fc9c1ed607b281ea8000d1694708198205a080e000345fa9c30160bfa82f78000d134a).toArray⟩
theorem h45:check 5 45 d45=true:=by decide+kernel
def d46:Row:=⟨BCurve 58 46 0x1aee7ab1a3fceae1806954fada1804c5d530a764f3595f0467d851f22028057ad14651ff500846a2918335226a9bebe398c1c13d690ff0029f4c216cbd9c2296ee44cca463dbbb18388510cee59d03afce2093b3b93fb5d9e4a79ac87af29c382256174dde9ff7665c5458eae7f8c8796083e825eedda9e392827743330865daf5bc9a1169f82144b3d6dd8bfd99439b832e659b51e858c41d792a9679aa0013f4867d2bacded02cb4a39a1dd63f3b5094540a514358fa027ca92141e3e362507a403175922d477ba6792c29954d31560ef3366ed31d76e3c04b7717d315e9d16913c6446d5cc095dcc8d6c0562574edac7090f5000000000000014bd53dd9e8eb800300000000000004fc529ff480530008000000000000132541220573e00010014,decode 5 1 0x76b866995f65402593d65533234e2018e082cc8708c2124bfd28aa550a394c9f20477b4875d446d5003d40000300002000010014,(AH 7 0xae18195f6019a80658000cd4027033d80cea0332000344f59c1f1607c281ee8000d166a708298209a081e000345ee5c30560c0a82fb8000d1332).toArray⟩
theorem h46:check 5 46 d46=true:=by decide+kernel
def d47:Row:=⟨BCurve 58 46 0x1b3663821aa8aae1406954fada1804cd1f20a52af1d9380467d851f2202826237a2c97984f9846a2918335226cb4a72638fec53ba9389a5c4ae3e202a73e1589a984c665068fe6086387634f807d3812ce1f9649df252f0ded224baaf33eff381e6095a99fd97787877755cf7c2cc8698ad0b937291e2f9fc216aef683082684c9ebfc3c6bd28bfb6f7461cbfc9bf34f235a5da28233fcf687e72a9284e4dfae19469a84a854b9e36ca38a4b61cd45fed4af41bef28aaaf27c69d86ca1b95051decb38e02317877aa9695ca92f2936b295f362aaf81d72f0b9bc3327d3239d6b847043446d4d04965049054059911ac9eecef0f4c0000000000001593fd4d7723680030000000000000530ecfa1ca4c5000800000000000013f36a836e02c00010014,decode 5 1 0x76b8569938653e6593ba5531934e1f18e072cc8608c2024bfc28aa450a384c9f10477a4875c446d4003d30000300002000010014,(AH 7 0xae1419387019e80668000cd3e67034180cfa0336000344ee9c1f5607ce81f28000d163e70839820da082e000345e1dc30960c1682ff8000d1319).toArray⟩
theorem h47:check 5 47 d47=true:=by decide+kernel
def d48:Row:=⟨BCurve 58 46 0x1b7e4c5291546ae1006954fada1804d44ebb643a6a59100467d851f2202845b22cfe60a94f2446a2918335226ecd6268d93bc939d96144b5f67b629886b242a4a464c025a94410f88f89b5a7d405cc5d4e1e98e0050aa845f59c568c7697b8381a6b1405611307a8b0024ee04018c859b51d8a48639eb5515f521e41e307e72e9e1b5e686daccc1852614f8bfb9ea302c38659a9b1d539c62f8e2a8e901fbf483e06b7dad54c8c5c54a37a78ed5b50ad150a6dca6e9814327c2a8f975f8f3d53432878e9ce8e8779ac598d28c9053c0e60f274e6e31d6efdb32cef37d3314dc761fda2cc6d3d4896c3c933c05d0dc0c31138f0f48000000000000166ee6c487bb000030000000000000566975612c9f1000800000000000014c5d3ec0e94880010014,decode 5 1 0x76b8469910653c95939d5530034e1e18e062cc8508c1f24bfb28aa350a374c9f0047794875b446d3003d20000300002000010014,(AH 7 0xae1019106019e80668000cd3c97034580d0a033e000344e75c1f8607de81f58000d16127084d8211a0842000345d51c30c60c2683038000d1300).toArray⟩
theorem h48:check 5 48 d48=true:=by decide+kernel
def d49:Row:=⟨BCurve 58 46 0x1bc6352308002ae0c06954fada1804db7e562349e2d8e70467d851f220286426e9bbad324eb046a29183352270d4750718ab8537f989ef0fa213232e5bf8a9e9a2b4b9a64bf83be8ba8c07d7e036b98c4e1d9b762af0217dfe15bb6d04f0403816759261224c87c9d5f5441cd2c4c849df6a5b599ddf7b249d868a273307a7d8724ac0946f86e19b5c9afd0c14a152b663b251b0e0cc0f32fffe2a8a9b5a9ee262c6d52e33c6479774a36aa678e95b5b55658e73b78135b27beb46c21d652a54a757f19296698778af49bda862e141696ff06d22941d6b0aac9dab47d33efae501bbe4d86d2d8c9737496240609b66d913ae90f44000000000000174e1042d05580003000000000000059d51b3d6efd70008000000000000159c7d5be729380010014,decode 5 1 0x76b83698e7653ac5937f552e634e1d18e052cc8408c1e24c1428aa250a364c9ef047784875a446d2003d10000300002000010014,(AH 7 0xae0c18e7701a280678000cd3ac7034980d1a0342000344dfdc1fc607ee81f98000d15e57085d8216a0856000345c81c31060c3683078000d12e6).toArray⟩
theorem h49:check 5 49 d49=true:=by decide+kernel
def d50:Row:=⟨BCurve 58 46 0x703877cdfaafab8201a553eb6860138a4e6e8e8b5562f4119f6147c880a20ed67235d90d38e11a8a460cd489cb6e1e95606d04d8a6ca65a536aa8f109c452d5b8352cc9bbab19b639a39677e94401a8b3872783143566ad81a39e932792258e04a0042f38e181fabe540d61592c320e882467a22c07160cc848e216acc1da4026a03de4db80f187d3d0da42a86a6957e7c8786f27ec3c1eb94c4a35ad40477660995c0a3bacd460f827babfdecdb3b18560b59a2da7c7ec777b239ee27fcbd46c3c2ed4b5e0b1d6717a60e6757d34ca4c463ab096c6d1dd097aac990c0643a0d0bf62fd0f40000000000000183179c850f2e800300000000000005d51c136916770008000000000000167766d2f7c0d00010013,decode 5 1 0x76b82698bd6538e59362552cc34e1c18e042cc8324c1d28aa150a354c9ee0477748759446d1003d00000300002000010013,(AH 7 0xae0818bd601a280678000cd38e7034d80d2a0346000344d89c201607fe81fe8000d15b770871821ba0866000345badc31460c46830b8000d12cc).toArray⟩
theorem h50:check 5 50 d50=true:=by decide+kernel
def d51:Row:=⟨BCurve 58 46 0x71581b0fd55eab8101a553eb686013a6a3848fef1f6248119f6147c880a288a9652b0b3137011a8a460cd489d38a690e5e2bf4d1276d0f0be50991679ff09bb88912b29e458247244642aefc8a46b278386e8289daec4fb83c1a4cad0a82ece03a2a3c6292fe6030684c8c68992320a92c1aa984eb733a8cd3e6f1f04c1ca6b21da40a45bf3cba83e444152a82b1d05e16ac570fcc853f787bfca34b01900570b7d61bad9fafe6a1827b6cb517991105576f2d8cc17d218776b52a1ea796994c1d59e90f99491d63249f7f2367d35a4b6587cb10846d0e14981e49bf4067e9b35bb8bcb0f3c00000000000019192355099338003000000000000060df674c93dd1000800000000000017569051405b500010013,decode 5 1 0x76b81698926537059344552b234e1b18e032cc8224c1c28aa050a344c9ed0477648758446d0003cf0000300002000010013,(AH 7 0x2b81062498069a01a2000334dc180d4a034a000334d11c2056080e82028000d1588708858220a087e000345ad1c31960c56830f8000d12b2).toArray⟩
theorem h51:check 5 51 d51=true:=by decide+kernel
def d52:Row:=⟨BCurve 58 46 0x7277be51b00dab8001a553eb686013c2f89a9152e9619c119f6147c880a2fe147fce4b3535211a8a460cd489dba6b3875beae4c9680fb872936793be7ae4f2b68e9298a0d052f2e4f64bf5d962eeca01386a8ce2728234885df81823c7b0b4e02a5435d197e460b4e0f8336adab32069d5eed8e717751422896711ddcc1ba961d144363dc669b22328ad882a7ebd0b3db0d1172d17783eedfdaca33b2f1b937b661676ac225f62ebc27b2d6c4256e6f358d2d3af479bfe0775b81a4f273079517634e3b9db1c1d5f3198efdf77d367eec86e1bfa246cfe589891c9edc06baa59c85b5530f380000000000001a050ce8fa36700030000000000000647e0d7f765e500080000000000001839f9d6c0f8b80010013,decode 5 1 0x76b806986765352593255529834e1a18e022cc8124c1b28a9f50a334c9ec0477548757446cf003ce0000300002000010013,(AH 7 0x2c146a048200033ad501867701aa80698000cd3527035980d5a0352000344c95c2096082282078000d1558708998225a08920003459edc31d60c6683148000d1298).toArray⟩
theorem h52:check 5 52 d52=true:=by decide+kernel
def d53:Row:=⟨BCurve 58 46 0x739761938abcab7f01a553eb686013dee45b97dc9b60f8119f6147c880a3737f9a718b3933311a8a460cd489e37c5b6ed674b4c1a8b261d941c696152d22325ca0d27da35b239ea5a2553c151e3845203866973b0a1819687fd34b96b10fc0e01a7e2f409cca61394f43cb1d1943202a7fc308494376ed8da50e7e8b8c1aac1184e46239cd95ff5b0a542d2a7ac8461d4af5d74a5f9cc04c4194a32b5ca721861456d19f42dbbaee427aee236d14bce05a364c0a6cd5688774bb0a7fa6ca5556ce53dd4a15e51d5b3e92609b87d3758eed169dc64c6cee9c99054a1c406f7c0051ddf950f340000000000001af5368422dc900030000000000000682db3cf38eb300080000000000001921a3637999080010013,decode 5 1 0x76b7f6983e65333593065527d34e1918e012cc8024c1a28a9e50a324c9eb0477448756446ce003cd0000300002000010013,(AH 7 0x50536c14ba046a00034a9b4183e601aa80698000cd3337035d80d6a0356000344c19c20e60832820b8000d1526708ad822aa08a6000345909c32160c7a83188000d127d).toArray⟩
theorem h53:check 5 53 d53=true:=by decide+kernel
def d54:Row:=⟨BCurve 58 46 0x74b704d5656bab7e01a553eb686013fad01c9e664d604c119f6147c880a3e482dcc2d91d31411a8a460cd489eb52035650fe84b9a9550b3ff024986bb6a85aa3b31262a5e5f44a66525e81afbc233fd83862a193a1adfe48a1abe705c66e08e00aa828afa1b0a1bdb32f538016631feb299737ab6e78c6ce26dd3551cc19aec138848e31d4c1a22b8923a12a76d380fce51a9767a4f2c39347aca31b8a32af90c2972c870124eea9127aaeda97d292ce5b99969e312d0c4773bdfab02664315c25b6d5c050741d574b8bd15797d3832bd3815074f86cdee09978ca4ac0735ea6f840a910f300000000000001be9a02683859800300000000000006bee5a3bdb83b00080000000000001a0d8cf76a3c400010013,decode 5 1 0x76b7e6981365314592e65526234e1818e002cc7f24c1928a9d50a314c9ea0477348755446cd003cc0000300002000010013,(AH 7 0x14148b051a81158000d29790604d806ba01aa000334c5180d8a035a000334b99c2136084682108000d14f4708c58230a08be000345819c32560c8a831d8000d1262).toArray⟩
theorem h54:check 5 54 d54=true:=by decide+kernel
def d55:Row:=⟨BCurve 58 46 0x75d6a817401aab7d01a553eb686014165288aa15e75f9c119f6147c880a455861f1427012f411a8a460cd489f2e108ac485334b1a9f7b4a69e839ac217776b92d21246a870c4f626fe67c6a93caf9e29385eabec3943e328c381ea7107cb88dffad2221ea696a2420cbacc924ed31fabd36b670d9a7a9fe40ed33b7f8c18b170ec24ba2ddbec9a94a530462a72debbdc7f3f5784e77a48c30ff8a30bb7be3d9b70d787635d3afe1c127a6f91c29068bb5cfcb36a949f3e8772c0eae0a5fe0d617c5dcd1c8ac91d5358854213a7d390c57bae34062c6ccf2499ec4a794077524dbb836470f2c0000000000001ce249d01c318800300000000000006fc000c55e27d00080000000000001afdb69292e2600010013,decode 5 1 0x76b7d697e7652f4592c65524634e1718dff2cc7e24c1828a9c50a304c9e90477248754446cc003cb0000300002000010013,(AH 7 0x5050ac140a044200034a1e017e7701b2806b8000cd2f47036980d9a0362000344b19c2186085a82158000d14c0708dd8236a08d6000345725c32a60c9e83228000d1246).toArray⟩
theorem h55:check 5 55 d55=true:=by decide+kernel
def d56:Row:=⟨BCurve 58 46 0x76f64b591ac9ab7c01a553eb686014316b9fbaeb695ee8119f6147c880a4c689616574e52d311a8a460cd489fa700e023fa7e4a9aa9a5e0d4ce19d184f8f6522f1522aaafb95a1e7ae710b019fdd7c10385ab644d0d9c7f8e55555d874f64cdfeafc1b8dab7ca2c65be6365484431f6c7d3f966fc67c78cf5cf08e6d4c17b4209fc4e625e316e8965e65bc2a6ee9f6bc196427a227334fdbc218a2fbe549cba61f17e234571de947627a3048ed4e3ea85e5fa26f972dd48771c3db112597e966d248c35ec4e51d4f657eb2cfb7d39e5be59d4879e46cbf689a5fcaa7c07b56f49ba62b70f280000000000001ddf3380ece060003000000000000073a2a76bc0d7900080000000000001bf22034f38b680010013,decode 5 1 0x76b7c697ba652d3592a65522a34e1618dfe2cc7d24c1728a9b50a2f4c9e80477148753446cb003ca0000300002000010013,(AH 7 0x1413db04ee810b8000d276805ee9806ca01ae000334b4dc0db6036a80d98000d12a670875821ca086e000345229c23ea08f2000335625c32f60cae83268000d122a).toArray⟩
theorem h56:check 5 56 d56=true:=by decide+kernel
def d57:Row:=⟨BCurve 58 46 0x7815ee9af578ab7b01a553eb6860144c84b6cbc0eb5e30119f6147c880a53324cb64d0a92b211a8a460cd48a01ff135836fc94a16b3d0773fb409f6e5ef0475b1c920ead86664da85a7a4eb8e5acbd913856c09d686facd90726293c0e5248dfdb2614fcb062e34aa0b190c778131f2d2713c5d1f17e519011352b748c16b6d053651221ea408c30b4d8602a6af5319bb388e7bf641dd8dd0ec8a2ec12d559b0cd583cf9eecdb02af279f100180c14965fc263ad38daa34770c6cb41a531c56c2777b886fec71d4b7278238bc7d3abef114e8dd0246cafac9ad34ad6407f6c9b98a8fe10f240000000000001ee05d38f59220003000000000000077964e2f0392f00080000000000001ceac9de8c37580010013,decode 5 1 0x76b7b6978c652b2592855520e34e1518dfd2cc7c24c1628a9a50a2e4c9e70477048752446ca003c90000300002000010013,(AH 7 0x504e2c136a041e00034992c178c601b6806c8000cd2b27037580dca036e000344a15c223a088600033514dc244a090e00033551dc33360cc2832b8000d120e).toArray⟩
theorem h57:check 5 57 d57=true:=by decide+kernel
def d58:Row:=⟨BCurve 58 46 0x793591dcd027ab7a01a553eb686014679dcddc966d5d70119f6147c880a59b585d123a4d29111a8a460cd48a0947761cab1c2498ebdfb0daa99ea1c4459a12344911f1b01136f9690a8391cf0e1d7ea83852caf6000591b928f4649bd3ad7cdfcb500e6bb548e3cedb1cdbe9a7631eedd0e7f5341d802a262ba117e24c15b98007053e19f1698563a873d72a67006c7b4dada7dc9e39e3c71daca2dc4060e7bb7b9897b4244a52c6b279b1b742c9ea836124f72379a201476fc9bb7224cba1717beaac95386f1d477f719447d7d3b97efec20408e86c9ff09b46cb04c0839342b28bdc50f200000000000001fe5c6f83646c800300000000000007b9af50f2659f00080000000000001de7b38f5ce6300010013,decode 5 1 0x76b7a6975c6529159263551f134e1418dfc2cc7b24c1528a9950a2d4c9e60476f48751446c9003c80000300002000010013,(AH 7 0x504cec131a040a000349480175c701ba806d8000cd2917037980dda037200034498dc228a089e000335069c24ca092a00033540dc33860cd683308000d11f1).toArray⟩
theorem h58:check 5 58 d58=true:=by decide+kernel
def d59:Row:=⟨BCurve 58 47 0x1e954d47aab5aade4034aa7d6d0c029049b1fe523aeb958119f6147c880a5ff24166db1d126f08d4523066a4508249b27ce034a480b20969055ff690680e3316d602474d65380f4a536d19a888325f46b6709ad54e979b76994ac007f7c507e8dfb5bd03ed5d17922985940bde4a818f4b9eaf0925926080a46b0d144403051785f754ad423f123a85e72849e54c30ba75ae7d267f9d5877099eec0a2c636f63ae314ec79317bc9e88d613cac9b9b61f01c58a1d7349661e5c1db999574548cafaed9f433f12e3ba3a838c6b0503e7d3c70badf7ab24346c881a4ddd2599a043e574f4a7631878e000000000000083bdc2fabbf96000c0000000000000ff6138185259200100000000000001ee8dd476597f00010013,decode 5 1 0x76b796972b6526f59240551d334e1318dfb2cc7a24c1428a9850a2c4c9e50476e48750446c8003c70000300002000010013,(AH 7 0x1412eb04b280fe8000d23e705cadc06fa01ba0003349bdc0e06037e80de8000d1240708be822d8000cd3e07094ec252a090a0003452edc33d60cea83368000d11d3).toArray⟩
theorem h59:check 5 59 d59=true:=by decide+kernel
def d60:Row:=⟨BCurve 58 47 0x1edd361821616ade0034aa7d6d0c0293927fa1b6652b7c0119f6147c880a662efcfc9295524c08d4523066a450bc8cc8a08131243ab4940ea0196e99be6321875ee846d96a4db0a1d4cd2c2c300dc68f407092dfa72f315b796c89134fe26190dfa5d200a4df8a926b9869a21f5f218f2bc92414fe1d20f6b4a4bbb5160304d7dbedc8b2c1bff72f126ce9be654bb16e23a81f728170a067f55820ca2b64dbc01e86c0ca68334551593893c8cc96611659798fa652e7621ef31db59f37a647feb2f8453922c756223a7b996475bff7d3d4951eef8322086c783c4e16e5b0e04609c89e78ddd878c000000000000087f56a317ee34000c000000000000107ae864c1815a00100000000000001fee4706a64c980010013,decode 5 1 0x76b78696f86524c5921d551b634e1218dfa2cc7924c1328a9750a2b4c9e40476d4874f446c7003c60000300002000010013,(AH 7 0x14129b04a280f98000d22a105be2806f8000c924c6038680e08000cd21d708d682348000cd3a370972c25ba08e60003451c5c34260cfe833b8000d11b6).toArray⟩
theorem h60:check 5 60 d60=true:=by decide+kernel
def d61:Row:=⟨BCurve 58 47 0x1f251ee8980d2addc034aa7d6d0c0296ce22a5bf4c6b628119f6147c880a6c253b0d2aeb922808d4523066a450f265b5abeedba3f2b71eb43ad2eaa31415339a87f9465d6f6351f956253eae95ae709f08708ae9ffc6c740498e4f86a42b8894df95e6fd5c61fd92ada60f30b872398f0bf39920d6a8216cba37f429c183049831e43cb840c0dc0e5206504da54b3221d1a1c1be8343bb70ff9d788a2a66481c8edc32cd3cf3bc6b075d13c6cf730c0db12d952e7b67da91191db1a5180747327302e9b70447d5a43a73a65de67c07d3e21b51a98c02606c685e4e50a5c82048369c56ba5e6878a00000000000008c3e118521d8c000c0000000000001101dd4b99de96001000000000000020f7f0cd1f04280010013,decode 5 1 0x76b77696c565228591f95519734e1118df92cc7824c1228a9650a2a4c9e30476c4874e446c6003c50000300002000010013,(AH 7 0x50496c123a03d600034853016c5601c2806f8000cd2287038e80e28000cd1f9708f2c23ba08be000344d8ec264a08be00033508dc34860d1683418000d1197).toArray⟩
theorem h61:check 5 61 d61=true:=by decide+kernel
def d62:Row:=⟨BCurve 58 47 0x1f6d07b90eb8eadd8034aa7d6d0c029a09c5a9c833ab490119f6147c880a721b791dc341d20408d4523066a451283ea2b75c8623aab9a959d58c62ac69246950351245e17478f350d785512fb9145dadf47082f4585e5d2529b01361f4a0e0b4df85fbfa13e470b2efae84b7a9e4618eec1e0e2caf3321e2b524b6719d03045887dab0bdc041c0d844b35e82054ab2d57f9b640b8516a99228716c0a2967b478ff31a4d0115921eb934393c4d24fb70508e59ab5eccacf7c1c1dadaaf86846662b0d8cbce39447243a6bb357573817d3ef9e4625c5c53c6c58804e8a65df604a6bf01d6be4c878800000000000009097b8f5a4d9e000c000000000000118af2360e3d4600100000000000002205da9acfbea00010013,decode 5 1 0x76b766969265204591d55517834e1018df82cc7724c1128a9550a294c9e20476b4874d446c5003c40000300002000010013,(AH 7 0x14120b047e80f18000d1fea05a498071a01c2000334811c0e56039280e38000d11d570912c243a089a000344c86c26ea089a000334f41c34e60d2a83468000d1178).toArray⟩
theorem h62:check 5 62 d62=true:=by decide+kernel
def d63:Row:=⟨BCurve 58 47 0x1fb4f0898564aadd4034aa7d6d0c029d383e0e75d7eb2e8119f6147c880a7784bc241d5411df08d4523066a4515e178fc2ca30a35ebc33ff7045deb5bd90c2a882554565798e94a858dd63af9a3f8d841e707afeb0f5f30a09d1d4a541423810df7610f6cb66e3b331b1ca36f2f4718ecc48833887be2258a56b028ca8730418ddd124c33f42a58cea7411d1654a33892d95065786e96acb6fcf09ca286920d56f8716d2e56375d2fcec13c2d52c61fc6099a03ca71040d1621da9b0d8c94599e3182e4ac0acb8303a63c050c7f427d3fd1dfc64306aa46c48a24ec425f6a04ca9c3f28d70f878600000000000009502608307e6a000c000000000000121627241e9d6a00100000000000002318046fb87c000010013,decode 5 1 0x76b756965d651df591af5515934e0f18df72cc7624c1028a9450a284c9e10476a4874c446c4003c30000300002000010013,(AH 7 0x50472c11ba03ba0003479e8165d701ca80718000cd1df7039d80e6a03960003446bdc24cb092e821e8000d12dc709e6c278a087a000344de9c35360d42834c8000d1159).toArray⟩
theorem h63:check 5 63 d63=true:=by decide+kernel
def d64:Row:=⟨BCurve 58 47 0xffe6cacfe08356e801a553eb68601502cc5e9e41c9589c08cfb0a3e44053e76ff953bb328dc846a2918335228c8ddb4210f1911895f5f52857fab5f88ad1fd1a9d12272bf521affed1ebb171c98002cb338398484c6c47774f9c9a84507c7526fb302bd16a35c3a07736ab85fd754c75625f382e956b373afdfae9403018e8c72f8446048e2ce8b0ad87a3ab303d933c798c8be438a2c43486b80e549b43cdb8ea8a388bbff1cd5b8cb0a276a8d31dfdc88d5b912b821445713c0d8090cf3b851a5c2aa382e9f821da5b6b92a44cd9b22ce609b9128c83a5bcd4a38b037d40a9a7464cbf28c6c38c44efde60de04ef017d61f02f87840000000000000997e082d4aff0000c00000000000012a37c15caff020010000000000000242e6e4bd93c480010014,decode 5 1 0x76b7469627651b9591895513934e0e18df610c752cc7424c0f28a9350a274c9e0047694874b446c3003c20000300002000010014,(AH 7 0x14118b045e80ea8000d1cfc0589dc073a01ca0003346e580e8a039e000334625c255b095282158000d129350a06c27da0856000344c7dc35960d5a83528000d1139).toArray⟩
theorem h64:check 5 64 d64=true:=by decide+kernel
def d65:Row:=⟨BCurve 58 47 0x10226115395e156e601a553eb6860151b6d77cdfabb57b808cfb0a3e440540e52393499a48c9046a2918335228e195161aac45516160a4a552dc696432407020628ba230c1dcebabadcec455caf2db08ef383589b1128f69e50aa7b1e784723a6fab0cf6bd898c6a2597238e3c3ea8c7463af03a6bc9d3b5a8c51e8d70818dcc9d6d5038d3e3446604383ba633039989be0cce3dc46eb64f306cd5654934f089884aef8a8e66865a2eaf4a266bf98e5031fad88c66e8d6698393bedae5b7eb1005ab47f64298d7e61da1bc998b4401532d6cfe744198ee3a53da43a96c47d41813ae27985d006c28e64f37a62520513eebc8209ac878200000000000009e0aaff46e230000c0000000000001332f10b13620e00100000000000002549182f31ff780010014,decode 5 1 0x76b73695ee65192591615511834e0d18df510c742cc6e24c0e28a9250a264c9df047684874a446c2003c10000300002000010014,(AH 7 0x14114b044e80e68000d1b70057b9c074a01ce000334649c0eb603aa80e98000d1161b097a820d8000cd247509e2c274a0836000344b01c35f60d7283598000d1118).toArray⟩
theorem h65:check 5 65 d65=true:=by decide+kernel
def d66:Row:=⟨BCurve 58 47 0x1046557d74b3f56e401a553eb68601533a53c02d99556cc08cfb0a3e440543534791578168b5046a2918335228fa4c78144971913961e9f820392568db8252405d4c21eec467bc576e7acd93d8305748cd38318edd5e5a5c4d1b846f881703da6fa31730646fbc8a44648a1f4dcdccc7364fecf1ee3cd3f79c7a86de7c018d2cc7e25c115ee3ba365721d041b30359dfb480d3bcc5532b0e2c13450548b5a43781ed3b8c60a107fd30b70a256d65eac0876cdb5f6007f26c7213bcddc262e267b9b0cc8b2f7f81da1d9dc279ec43350b380a244abe08a03a4be73d1a2857d42589a9ac95a9f86c19084f71663c6053963fc89238687800000000000000a2a857d87152a000c00000000000013c48603f7c68e001000000000000026680219c2c5900010014,decode 5 1 0x76b72695b36516a59139550f734e0c18df410c732cc6924c0d28a9150a254c9de0476748749446c1003c00000300002000010014,(AH 7 0x14110b043e80e38000d19d7056cdc075a01d20003345a9c0ed603b280eb8000d1139b09a282058000cd1f7509bec26ba0816000344971c36560d8a835f8000d10f7).toArray⟩
theorem h66:check 5 66 d66=true:=by decide+kernel
def d67:Row:=⟨BCurve 58 47 0x106a49e5b009d56e201a553eb6860154b73ab3cde5755d808cfb0a3e4405457aee0a464688a0846a291833522911e94fc7d9c9510f632f4aed95e36d8472c631a81f21aac6f28d032f2ad6d14450750838382d9409aa254ebd2c5fe126bfadfe6f9b216a0b55ecaa631aef25ebdf84c72664e9a970afd4398affe78786018c8cf25767e9e9a42ffc0395376423031a35aaf4d93c46378a803b615965483657e57b8f878e32aea1bebee1ca246ed24730dcdede31fe15754d2313bae09f0dd9bf71b65068fee2a4a61d99c85a4d4268c342a5d21f0677dc3a43f4368ae467d432fc66f3c3d9746c092a4fab2653a055f613d773dbd877e0000000000000a756ffd9548de000c00000000000014583b00782c820010000000000000278b2c0b8b8e900010014,decode 5 1 0x76b7169576651415910f550d534e0b18df310c722cc6424c0c28a9050a244c9dd0476648748446c0003bf0000300002000010014,(AH 7 0x1410cb042e80df8000d1830055d9c076a01d6000334505c0efa03ba00033443d4266b098e81fd8000d11a35099ac263a07f60003447cdc36c60da283668000d10d5).toArray⟩
theorem h67:check 5 67 d67=true:=by decide+kernel
def d68:Row:=⟨BCurve 58 47 0x108e3e4deb5fb56e001a553eb68601562d8c57c090154e008cfb0a3e440547a29483350ba88b846a2918335229286b9d355d4c90e564749dbaf29f722d11cbf434f9a164c97d5daeefd6e00e0f53342b4838299935f5f0412d3d3a06c37e57c06f932ba3b23c1cda82853b8ea5ac7cc71679e660f322f47b74554088eed98c0d1ccc73c274a4a5b70992725fa302da8ba168debb471bd4a55e54894547b70b937531d490048f539edba6ca23703ea3a13250e10441115f0b9593b8e37bb8d11725bbd38fb0c231b91d95ce3aae419c7b4d4007f11ae6a83a3c012ffba077d4406be5fd22eb786bf94c4fe4e66ae0585e67f4c5851877c0000000000000ac16a7f717d4c000c00000000000014ee10009493ea001000000000000028b296048c5a780010014,decode 5 1 0x76b706953865117590e5550b234e0a18df210c712cc6024c0b28a8f50a234c9dc0476548747446bf003be0000300002000010014,(AH 7 0x14109b041e80dc8000d167a054e1c077a01da00033445dc0f1a03c2000334395425eb096e81f68000d114b5097ac25ba07da000344619c37360dbe836d8000d10b2).toArray⟩
theorem h68:check 5 68 d68=true:=by decide+kernel
def d69:Row:=⟨BCurve 58 47 0x10b232b626b5956de01a553eb68601579d48ac0599353dc08cfb0a3e44054983bd7704aec876046a29183352293dd3605cd3fb50b965b9f0884f5d76d55f638811e6211ccc082e5ab086e94a393894cde238259e6241bb339d4e12e05e53011e6f8b35dd59224cfaa1102bea164f48c7068ee3187595f4bd587a91e1f5c98b6d47417f9affa51b676919808b23029ae197dce43a4800097d94ee19454737bf416ed42091d6431d9d82178a2271ab001187c2e3d628fbafa7ca93b6e65863c86eddc155ff451e37a21d91d41b0f40d03357d8c5c0fb54fe3a340e296c5c87d44dd826c8b2e0046be96e501ea682205acf3c2087342877a0000000000000b0e75031bb274000c000000000000158605044cfcc6001000000000000029de4004c529480010014,decode 5 1 0x76b6f694f7650ec590b95508e34e0918df110c702cc5b24c0a28a8e50a224c9db0476448746446be003bd0000300002000010014,(AH 7 0x50416c104a03660003452dc14f7a01e20003243b180f3a03ca0003342e54255b094a81ef8000d10ef50956c252a07be000344451c37a60dda83758000d108e).toArray⟩
theorem h69:check 5 69 d69=true:=by decide+kernel
def d70:Row:=⟨BCurve 58 47 0x10d6271e620b756dc01a553eb6860158ffda60ef5f552cc08cfb0a3e44054b1e68e5b52fe85f846a2918335229533b23844aaa108b66ff4355ac1b7b7d5b8ced37dea0d4ce92ff067132f285c20096d4233821a38e8d86260d5eea6df73daa1a6f83401700087d2abf841abb13a600c6f6a3dfcff80914ff376fdb935b898acd71b68b738a65910d222a613dd3025b378e50e9b9c8e42908df2f4d8546b872ef68766c93a7c9ffbab4abca2173175c81dd34e6a7b5d46721c193b4e9350ebfc691c6d7b7bbf6a7d41d8dd9fb704003eb62700b8ea7c2e23a2c1b22dd1897d45b41295673b7146bd99050586699605d48905ab8e9087780000000000000b5c8f8893e856000c00000000000016201a0ba1671600100000000000002b0e2a0c35fb000010014,decode 5 1 0x76b6e694b3650bf5908b5506a34e0818df010c6f2cc5624c0928a8d50a214c9da0476348745446bd003bc0000300002000010014,(AH 7 0x14102b040280d68000d12e6052ce80798000c90bf703dac0f5a03d200034422d424db092e81e88000d108f50936c24ba07a2000344279c38160dfa837c8000d106a).toArray⟩
theorem h70:check 5 70 d70=true:=by decide+kernel
def d71:Row:=⟨BCurve 58 47 0x87d0dc34eb0aab6d00d2a9f5b4300ad2aa0bb3ef13a8d80467d851f2202a64aeac8eb100424011a1471c6338b7306b1e20fb5082e023428e38c6717a5280187f38c902b6844962308d780250648239fdfa048d11dcfb231e2fbc0a9ab3a59ec381da8bad95118756fc0af8e3e39d66f7b4a50a6eead4adeb39c2b58f92cc6e6b8dc877a7c154111351d9c5f718a4d9c2b974c156606a834c515c963021b8d84c4ef38c9c833473d159dc54639269d6218b8957923f9f673630a207483b8f232a6e978e79b85797a13b2ec11b9b71e49cc58b9154b90da1d89dfdbd13f37ab6d05d95a203dc83a24281c4dd4a7d468a6eda66570ac6bc9b2509226b0a05fca64a35aa3b87760000000000000babba0fda1ef2000c00000000000016bc4f1691d2da00100000000000002c42541adecfa00010015,decode 5 1 0x76b6d6946c650906105c5d02b5502434e0718def10c6e2cc5224c0828a8c50a204c9d90476248744446bc003bb0000300002000010015,(AH 7 0x140feb03f680d38000d1108051b1c07bb01ea80788000d1090703e6c0f8a03c20003441714246b090e81e18000d102b5091ac243a0786000344091c38960e1a83858000d1044).toArray⟩
theorem h71:check 5 71 d71=true:=by decide+kernel
def d72:Row:=⟨BCurve 58 47 0x111e0feed8b7356d801a553eb686015ba4133c5ec41508808cfb0a3e44054dc6c4b8d7ee283000f51e0201a10f7cc86e4d55e0502b6989e8f0659584cc5f952b57f11e36d3a8a05df28f04faf0387f435f3819ade7251c0ae58095a52354e2106f73548a4dd4dd6afdd138e49de6f8c6d6cdd93efcef1582e5ca57fd61d989cdc6a0a324a0667c38a0e99d84e301dbe37b38f4b84aac2838aea3920545b9da4b5bbb04974a510c50be3d8a1f75f015628818ec49be510aaef513b0eeee64ae75fdd1d903511ce42b1d85e5bc323e6b63779a2f2364aac23a1c3515be90b7d4760973b8880ccc6bb9d450cbe6c7e06254b8fa6c64387740000000000000bfbf498ee5648000c000000000000175aa4251e401200100000000000002d7abe30bfa7280010014,decode 5 1 0x76b6c69422650607102b54f1b34e0618dee10c6d2cc4e24c0728a8b50a1f4c9d80476148743446bb003ba0000300002000010014,(AH 7 0x140fbb03ea80d08000d0f1b0508ac07ca01da000334182c0fba03b60003340ad423eb08ee81da8000d0fc3508fac23ba076a000343e91c39160e3a838d8000d101d).toArray⟩
theorem h72:check 5 72 d72=true:=by decide+kernel
def d73:Row:=⟨BCurve 58 47 0x4508115c503455b5806954fada18057396e98b918ad3d50233ec28f910153ac4d96aea69205c03d4780806843c8788f3f8be9b3fe1b31370e6fd5591694eb68189e469035ec3f4bb0d9b1e8c52e1402754c6c6e2d5f67f6235c4b52f8ab6c2e9898df115aefd2b26f1be6697f7c7c3019c3971acfa374b9007dd33d6a265453a8df9555d50991b5136c9953b4a1e775c71d2dd88ef1a39f4f6be8213aef1cb0fa5cdb1d758966f6aa90b1d81eb9c933d9f1b822d0cea75174a3a14420f2f4cc7d48368bb8cdb8b6c6ba9f65105a6df2064e78d5fee2a887720000000000000c4d3f23d08e58000c00000000000017fb193746aebe00100000000000002eb7684dd881980010012,decode 5 1 0x76b6b693d56502e70ff818d2010c6c2cc4c24c0628a8a50a1e4c9d70476048742446ba003b90000300002000010012,(AH 7 0x503e2c0f6a033600034348013d5b01f680758000cd02eb03fa80ea8000ccff8508dec234a0752000343d614237b08d281d48000d0f2170e6a83968000ccff6).toArray⟩
theorem h73:check 5 73 d73=true:=by decide+kernel
def d74:Row:=⟨BCurve 58 47 0x22cbf17e9ec5eada8034aa7d6d0c02bc346dd41d7ca9c20119f6147c880a9eaa54eefc48cffa01ea3c0403421d87bed45108441f86e1b8abad5b627673985d025e352c61c8f6820ffb64c73d234ccb012e544bb41a74eff9d9aec247960fad1ca1d78c8ce4332faf1ea5a8749af8193acf4a7ba9d2569dcd7727034e6bd1d7df17cf43cd2d38cbe72af51835c3a0c4f08a008d7d490c4c5235fec986b9a18513f66f6606782e1d3dff6a87700000000000000c9f99b080c722000c000000000000189dae4d0b1ede00100000000000002ff85272295ef0001000f,decode 5 1 0x76b6a6938464ffa70fc324b1828a8950a1d4c9d60475f48741446b9003b8000030000200001000f,(AH 7 0x503d6c0f3a032a000342c601384b01fe80738000ccffa7040ac101a039e000343f0d4230b08b681cd8000d0ee8508c2c22da0736000343a61c3a3b0e7e839b8000d0fcd).toArray⟩
theorem h74:check 5 74 d74=true:=by decide+kernel
def d75:Row:=⟨BCurve 57 47 0x2313da4f1571aada4034aa7d6d0c057d062347775bd3300233ec28f9102a7c7b126497dc3f1007a8f0100d08e6282ae4bd2e9cf8b7a352ab3886de974401006fc862409ef08cb28fa3f89565d4dee3af475e7dd7554f01a3cba73038fcf77e1d022e01086273ec9e1d907c1530486b8a3a5179270da0d44d6cac839130edc00000000000033cc10fbfc02980030000000000000ca131b335c8390008000000000000313d7c9db23f30001000c,decode 5 1 0x76b696933064fc470f8b4c9020475e48740446b8003b7000030000200001000c,(AH 7 0x503c6c0f0a0322000342408133070206c080a01c6000343f12c105a038e000333e2d4229b089a81c78000d0e74508a6c226a071e000343831c3acb0ea6838e8000d0fa2).toArray⟩
theorem h75:check 5 75 d75=true:=by decide+kernel
def d76:Row:=⟨BCurve 57 47 0x235bc31f8c1d6ada0034aa7d6d0c05816ec06946b252d80233ec28f9102a7d32daf8c20d3e3007a8f0100d08dfd8ec1e79b95cf527f4f6d8ece91d0ee6b19372d131b76347dc0c07becab731d96fb56806b7a5c51b2e724e0d9a615ce2740b0ed8000000000000351dfb3d2ceb900030000000000000cf49c41b401bd00080000000000003286e6d0732258001000a,decode 5 1 0x76b68692d864f8c70f52486dd446b7003b6000030000200001000a,(AH 7 0x303bd40eeb03b680c58000d46dd04b62c082a01c2000333e32c109a0382000333d494222b087e81c18000d0dfd5088ac21fa07060003435e9c3b6b0ece83828000d0f76).toArray⟩
theorem h76:check 5 76 d76=true:=by decide+kernel
def d77:Row:=⟨BCurve 57 47 0x8e8eafc00b24ab6700d2a9f5b430161621773bc9db49f408cfb0a3e440a9e60b2cebe878f5101ea3c0403423655f8cff37bda3c563afa791e83ecb8c56c74125f3c4aba7e51eca73c20df0fbf0caafbd0ed40000000000003674258595d7700030000000000000d4916d2003bfb000800000000000033d4910a6c08680010009,decode 5 1 0x76b676927d64f5170f15444ab003b50000300002000010009,(AH 7 0x503b2c0eba030e0003412ac127db0212806f8000ccf5150436c10ca037a000343c55421bb086681bc8000d0d815086ec219a06f2000343391c3c1b0efa83778000d0f49).toArray⟩
theorem h77:check 5 77 d77=true:=by decide+kernel
def d78:Row:=⟨BCurve 54 47 0x11f5ca603cba756cc01a553eb6861625b542dcc4bd487808cfb0a3e4454e73d9ea8723e78a00f51e0201a1d2a13bd0b1ca3ced6aa0522667536724534340761484d6000000000000df3a3f54db18e000c000000000001b3d42c834ede600100000000000035267b4b9cf1600010008,decode 5 1 0x76b666921e64f1470ed60026b0000300002000010008,(AH 7 0x140e9b03a280c08000d026b048794085b0212806d8000d0f145042ac109a036e000343b594215b084a81b68000d0d0250856c212a06da000343129c3ccb0f2a836b8000d0f19).toArray⟩
theorem h78:check 5 78 d78=true:=by decide+kernel
def d79:Row:=⟨BCurve 54 47 0x1219bec87810556ca01a553eb68616340d0f8d315746ec08cfb0a3e4454d70dce88fe2076a00f51e0201a1ccf2d8bbbf66a4e95ac25260276aa750b08f0294a780e0000000000000e4b4e8b03edfa000c000000000001bea77f005654a001000000000000367ca59405dd400010008,decode 5 1 0x76b65691bb64ed470e95000700000300002000010008,(AH 7 0x5039ac0e5a02fa00034007411bbb020e806c8000cced45041ec106a0362000343a55420eb083281b08000d0c7e5083ac20ca06c2000342eadc3d8b0f5e83608000d0ee8).toArray⟩
theorem h79:check 5 79 d79=true:=by decide+kernel
def d80:Row:=⟨BCurve 54 47 0x123db330b366356c801a553eb686164128dd4d0fa9455408cfb0a3e4454c04239ee9ed274880f51e0201a1ced66ae6a9e3f4e51ae45299e781e77d95dbabb39780de000000000000ea40922882b20000c000000000001c99cd1b71de2200100000000000037d70fe3a6cc080010008,decode 5 1 0x76b646915564e9170e510006f0000300002000010008,(AH 7 0x140e3b038a80bb8000d0000045554082b0206806a8000d0e9150412c103a03560003439454208b081a81ab8000d0bf750822c206a06ae000342c1dc3e5b0f9283568000d0eb5).toArray⟩
theorem h80:check 5 80 d80=true:=by decide+kernel
def d81:Row:=⟨BCurve 54 47 0x1261a798eebc156c601a553eb686164d72011739cb43ac08cfb0a3e4454a50ecd024d6472600f51e0201a1d0b9fd11946144e0bb0652d3a79927ab03293bd2e480dc000000000000efdd3bbda6900000c000000000001d4b424a7a586e0010000000000003935ba3a7fbdb80010008,decode 5 1 0x76b63690eb64e4c70e0b0006e0000300002000010008,(AH 7 0x140e1b038280b98000d0000043aec080a01a60003339314101b040280d38000d0e0b5080ac200a069a000342db14202b080281a68000d0a5fb0fce834b8000cce7f).toArray⟩
theorem h81:check 5 81 d81=true:=by decide+kernel
def d82:Row:=⟨BCurve 54 47 0x12859c012a11f56c401a553eb68616587f25f0d5a541f808cfb0a3e4454833f9b9b10c670200f51e0201a1d29d8f3c7ede94dc2b28530d67b067d8f877b2f28e80da000000000000f58ae56faa79a000c000000000001dfed77d1ed42e0010000000000003a98a49890b2500010008,decode 5 1 0x76b626907e64e0470dc20006d0000300002000010008,(AH 7 0x140deb037680b78000d0000041f9407fb01fa80688000d0e04503fac0fda034200034370941fcb07ea81a18000d0adc507f2c1faa06860003426c943f9b0fd283418000d0e48).toArray⟩
theorem h82:check 5 82 d82=true:=by decide+kernel
def d83:Row:=⟨BCurve 54 47 0x12a990696567d56c201a553eb6861662b9a0d4bd4f403408cfb0a3e44545ad4a5b8e8f86dd00f51e0201a1d484f5df716268d76b4a534727c7a80775c711129580da000000000000fb498f3e8e6ee000c000000000001eb48cb35f51620010000000000003bffcefdd9a9d00010008,decode 5 1 0x76b616900d64dba70d760006d0000300002000010008,(AH 7 0x2c0dba02d6000330000100db01f680678000ccdba503eec0faa033a0003435d941f6b07d2819c8000d0a49507dac1f4a067200034240543edb0fa683378000d0e0e).toArray⟩
theorem h83:check 5 83 d83=true:=by decide+kernel
def d84:Row:=⟨BCurve 54 47 0x12cd84d1a0bdb56c001a553eb686166c2171c2f0c93e6408cfb0a3e44542e01d784cf0a6b700f51e0201a1d668880a5bdfb8d28b6c5380e7dee8367b175632f980d80000000000010119392a526fc000c000000000001f6c61ed3bd00a0010000000000003d6b396a5aa4380010008,decode 5 1 0x76b6068f9964d6e70d280006c0000300002000010008,(AH 7 0x140d9b036280b28000d000003e65407cb01ee80658000d0d6e503e2c0f7a032e0003434a141f1b07be81978000d09b2507c6c1efa065e00034212d43e2b0f7a832d8000d0dd2).toArray⟩
theorem h84:check 5 84 d84=true:=by decide+kernel
def d85:Row:=⟨BCurve 54 47 0x12f17939dc13956be01a553eb6861673e3eec5bbe33c8408cfb0a3e4453fa9344d5c9ec68f00f51e0201a1d84c1a35465d08cd7b8e53baa7f6286608688253ba80d600000000000106f9e332f67c4000c000000000002026572ab450260010000000000003edae3de13a1880010008,decode 5 1 0x76b5f68f2164d1e70cd70006b0000300002000010008,(AH 7 0x5035ec0d6a02c20003400000f21b01ea80648000ccd1e503d6c0f4a032600034335d41ebb07a681928000d0916507aec1e9a064a000341e4143d7b0f4e83248000d0d94).toArray⟩
theorem h85:check 5 85 d85=true:=by decide+kernel
def d86:Row:=⟨BCurve 54 47 0x13156da21769756bc01a553eb686167b3d16cdace53a9408cfb0a3e4453c2bcd9d4d2ae66680f51e0201a1da2fac6030da58c84bb053f4680d68961dba9574d880d40000000000010ceb8d587a946000c0000000000020e26c6bc8d1b6001000000000000404ece5904a1c00010008,decode 5 1 0x76b5e68ea564ccd70c840006a0000300002000010008,(AH 7 0x50352c0d3a02ba0003400000ea5b01e680638000ccccd503cec0f2a031a00034321141e6b0792818d8000d08775079ac1e4a0636000341b4543ccb0f22831a8000d0d53).toArray⟩
theorem h86:check 5 86 d86=true:=by decide+kernel
def d87:Row:=⟨BCurve 54 47 0x1339620a52bf556ba01a553eb68616815a3fe50f9f389808cfb0a3e4453844aaa58f04063c80f51e0201a1dc133e8b1b57a8c2ebd2542e2824a8c6bb0d8f965380d200000000000112ee379adeb82000c0000000000021a0a1b07954ba00100000000000041c6f8db2da4e00010008,decode 5 1 0x76b5d68e2664c7970c2e000690000300002000010008,(AH 7 0x140d2b034680ac8000d0000038994078b01de80628000d0c79503c2c0efa03120003430b941e0b077a81898000d07d450782c1dea062600034183943c1b0ef683118000d0d11).toArray⟩
theorem h87:check 5 87 d87=true:=by decide+kernel
def d88:Row:=⟨BCurve 54 47 0x135d56728e15356b801a553eb68616863b6a0be411369008cfb0a3e44534170a28b1bb261100f51e0201a1ddf6d0b605d4f8bd6bf45467e83be8f7e06170b82b80d00000000000011901e1fa22e78000c000000000002260f6f8c5d932001000000000000434363648eaae80010008,decode 5 1 0x76b5c68da464c2270bd6000680000300002000010008,(AH 7 0x50342c0cfa02aa0003400000da4b01da80618000ccc22503b6c0eca030a000342f5941dbb076681848000d072d5076ec1d9a061200034151943b7b0ece83088000d0ccc).toArray⟩
theorem h88:check 5 88 d88=true:=by decide+kernel
def d89:Row:=⟨BCurve 54 47 0x13814adac96b156b601a553eb6861689e095422a3b347808cfb0a3e4452f7fad6425bf45e400f51e0201a1dfda62e0f05248b7bc1654a1a85329298db638da6080ce0000000000011f268c7647228000c0000000000023236c44ae5f1e00100000000000044c40df527b3d80010008,decode 5 1 0x76b5b68d1e64bc870b7b000670000300002000010008,(AH 7 0x2c0cda02a20003300000d1eb01d680608000ccbc8503aec0eaa0302000342ded41d6b075281808000d06825075ac1d4a06020003411e543adb0ea683008000d0c85).toArray⟩
theorem h89:check 5 89 d89=true:=by decide+kernel
def d90:Row:=⟨BCurve 54 47 0x13a53f4304c0f56b401a553eb686168d1c6b7d964d324c08cfb0a3e4452a7e9457eb1065b680f51e0201a1e1bdf50bdacf98b1dc3854db686a695bc30be7fcf280cc000000000001255c370f4b692000c0000000000023e8019432e67e0010000000000004648f88cf8bfb00010008,decode 5 1 0x76b5a68c9364b6d70b1d000660000300002000010008,(AH 7 0x140cbb032a80a68000d00000324d4074b01ce805f8000d0b6d503a2c0e7a02fa000342c7541d1b073e817c8000d05d350746c1cfa05f2000340ea143a3b0e7e82f78000d0c3c).toArray⟩
theorem h90:check 5 90 d90=true:=by decide+kernel
def d91:Row:=⟨BCurve 54 47 0x13c933ab4016d56b201a553eb686168eb2edcd99ff301808cfb0a3e4452536fdc6913f858700f51e0201a1e3a18736c54ce8abdc5a55152881a98e80627e1fe180ca0000000000012ba2e1c52fbb6000c0000000000024aeb6e7536f5200100000000000047d2232c01ce700010008,decode 5 1 0x76b5968c0664b0e70abd000650000300002000010008,(AH 7 0x140c9b032280a58000d0000030194073b01ca805e8000d0b0e5039ac0e5a02f2000342af541ccb072e81788000d052050732c1cba05e2000340b494399b0e5a82ef8000d0bf1).toArray⟩
theorem h91:check 5 91 d91=true:=by decide+kernel
def d92:Row:=⟨BCurve 54 47 0x13ed28137b6cb56b001a553eb686168f76c627e9812dd008cfb0a3e4451fa8e9b0184ca55680f51e0201a1e588edd9b7d0bca5bc7c554ee898e9c1c5b9fb432d80ca00000000000131fa8c97f4194000c0000000000025778c3e0ff99a001000000000000495f8dd242e0180010008,decode 5 1 0x76b5868b7464aad70a5b000650000300002000010008,(AH 7 0x140c7b031a80a38000d000002dd14072b01c6805d8000d0aad50392c0e3a02ea00034296d41c8b071a81738000d046950722c1c6a05ce0003407e14390b0e3282e78000d0ba3).toArray⟩
theorem h92:check 5 92 d92=true:=by decide+kernel
def d93:Row:=⟨BCurve 54 47 0x14111c7bb6c2956ae01a553eb686168f67f48c84d32b8008cfb0a3e445198dda8f6115c52500f51e0201a1e76c8004a24e0c9f5c9e5588a8b029f593125f66d680c8000000000001386337879882c000c00000000000264281986885560010000000000004af1387fbbf4a80010008,decode 5 1 0x76b5768ae064a4a709f5000640000300002000010008,(AH 7 0x50316c0c4a02860003400000ae0b01c2805c8000cca4a50386c0e0a02e20003427d541c3b0706816f8000d03ae5070ec1c1a05be0003404654387b0e0e82df8000d0b54).toArray⟩
theorem h93:check 5 93 d93=true:=by decide+kernel
def d94:Row:=⟨BCurve 54 47 0x143510e3f218756ac01a553eb686168e1d240091dd292408cfb0a3e445134f8cac1a4de4f200f51e0201a1e950122f8ccb5c98ecc055c268c76a29e86baa8adc80c60000000000013edce2941cf7e000c00000000000270f96f65d12860010000000000004c8723346d0c200010008,decode 5 1 0x76b5668a49649e47098e000630000300002000010008,(AH 7 0x5030ec0c2a027e0003400000a49b01be805b8000cc9e45037ec0dea02da00034263941beb06f6816c8000d02ef506fac1bda05b20003400d5437db0dea82d78000d0b02).toArray⟩
theorem h94:check 5 94 d94=true:=by decide+kernel
def d95:Row:=⟨BCurve 54 47 0x1459054c2d6e556aa01a553eb686168b965484109f26b808cfb0a3e4450c8443be954204bd80f51e0201a1eb33a45a7748ac923ce255fc28deaa5ec5c5dcaf3f80c400000000000145678dbd8178a000c0000000000027decc57eda12a0010000000000004e214df05626800010008,decode 5 1 0x76b55689ae6497b70923000620000300002000010008,(AH 7 0x50306c0c0a027a00034000009aeb01ba805a8000cc97b50376c0dca02d200034248d41bab06e281688000d022c506eac1b8a05a20003400014374b0dc682cf8000d0aae).toArray⟩
theorem h95:check 5 95 d95=true:=by decide+kernel
def d96:Row:=⟨BCurve 54 47 0x28f9f368d1886ad5008cfb0a3e4450595bc0e80a5248700f51e0201a1ed17368561c5fc8b7d045635e8f5ea942b20f5d3ff80c20000000000014c033903c6050000c0000000000028b021bd1a31420010000000000004fbfb8b37743c80010007,decode 5 1 0x76b546490e708b7000610000300002000010007,(AH 7 0x502fec0bea0272000340000090eb01b680598000cc9105036ec0daa02ca0003422dd41b6b06d281648000d0165506dac1b4a0592000340001436cb0da282c88000d0a57).toArray⟩
theorem h96:check 5 96 d96=true:=by decide+kernel
def d97:Row:=⟨BCurve 54 47 0x2941dc3948342ad4c08cfb0a3e444fe1a39542dc4443580f51e0201a1eefac8b04c434c847d26566fa90d2aca187cf5f91c80c000000000000152afe466ea9d0000c0000000000029839725e2c2ce0010000000000005162637dd063f80010007,decode 5 1 0x76b536486b70847000600000300002000010007,(AH 7 0xb02f6809a8000cc000021aec06ca016200033228ac0d8a02c200033211d41b1b06c281608000d009a506c6c1b0a05820003400014363b0d8282c18000d09ff).toArray⟩
theorem h97:check 5 97 d97=true:=by decide+kernel
def d98:Row:=⟨BCurve 54 47 0x53138a137dbfd5a900f51e0201a1f0e22f533ec7207c3d4856a969246b008dd9dd1e9680c0000000000001596d8fe6ef40a000c000000000002a592c924755ce00100000000000053094e4f6187100010006,decode 5 1 0x76b52707c3000600000300002000010006,(AH 7 0xb02ee80998000cc00001f0ec06ba015e0003320cac0d6a02ba000331f5541adb06b2815d8000d0000506b6c1aca0576000340001435bb0d6282b98000d09a4).toArray⟩
theorem h98:check 5 98 d98=true:=by decide+kernel
def d99:Row:=⟨BCurve 54 47 0x53a35bb46b1755a880f51e0201a1f2c5c17e294470719d6a56e3293bab378b37ab446d80be000000000001603c3b83d3efe000c000000000002b30e20247ea4200100000000000054b479282aad100010006,decode 5 1 0x76b51707190005f0000300002000010006,(AH 7 0x140bab02e680978000d000001c65406ab01a680568000d07bf50352c0d3a02b2000341d8541a9b069e81598000d0000506a6c1a7a05660003400014352b0d3e82b28000d0947).toArray⟩
theorem h99:check 5 99 d99=true:=by decide+kernel
def d100:Row:=⟨BCurve 54 47 0x54332d55586ed5a800f51e0201a1f4a953a913c1c066bd8c571ce952eb6f1096606aa180bc000000000001671be73d98aac000c000000000002c0ab775e4802a0010000000000005663e4082bd5f80010006,decode 5 1 0x76b507066b0005e0000300002000010006,(AH 7 0x140b8b02de80968000d0000019ad4069b01a280558000d074a5034ac0d1a02ae000341ba941a5b068e81568000d000050696c1a3a055a000340001434ab0d1e82ab8000d08e8).toArray⟩
theorem h100:check 5 100 d100=true:=by decide+kernel
def d101:Row:=⟨BCurve 54 47 0x54c2fef645c655a780f51e0201a1f68ce5d3fe3f105bbdae5756a96a2ba71df5fc913280ba0000000000016e0c93143d714000c000000000002ce6aced1d178600100000000000058178eef6501c80010006,decode 5 1 0x76b4f705bb0005d0000300002000010006,(AH 7 0x140b6b02d680948000d0000016ed4068b019e80548000d06d250342c0cfa02a60003419c141a1b067e81528000d000050686c19fa054a0003400014342b0cfe82a58000d0887).toArray⟩
theorem h101:check 5 101 d101=true:=by decide+kernel
def d102:Row:=⟨BCurve 54 47 0x2aa9684b998eead38008cc506efa8541e2dd5e866a2ca00f51e0201a1f87077fee8bc60507dd0579069816bdfb3567fb82080b8000000000001750e3f07c2436000c000000000002dc4c267f1b05600100000000000059cf79ddd630800010007,decode 5 1 0x76b4e6c594705070005c0000300002000010007,(AH 7 0xb02d280938000cc0000141ec067a014e000331962c0cea029e0003317d1419db0672814f8000d000050676c19ca053e000340001433bb0ce2829e8000d0823).toArray⟩
theorem h102:check 5 102 d102=true:=by decide+kernel
def d103:Row:=⟨BCurve 54 47 0x2af1511c103aaad34008cc506efa8531a058d21d4e2c980f51e0201a1fa57dea1db403444fdf257ca2998ac18d0b7e9df6b80b80000000000017c20eb1827212000c000000000002ea4f7e6624a9a0010000000000005b8ba4d37f62200010007,decode 5 1 0x76b4d6c5937044f0005c0000300002000010007,(AH 7 0x140b3b02ca80918000d00000113ec066a014e00033176ec0cca029a0003315d54199b0662814c8000d000050666c198a05320003400014333b0cc282988000d07be).toArray⟩
theorem h103:check 5 103 d103=true:=by decide+kernel
def d104:Row:=⟨BCurve 54 47 0x2b3939ec86e66ad30008cc506efa8520d10f3ec48a2c980f51e0201a1fc3b70ccc5bd84393e145803e9afec52761a3b071380b6000000000001834497456c0a8000c000000000002f874d686ee6520010000000000005d4c0fd06096a80010007,decode 5 1 0x76b4c6c593703930005b0000300002000010007,(AH 7 0x140b1b02c280908000d000000e4ec065a014a00033156ec0caa02920003313d14195b065281498000d000050656c194a0526000340001432bb0ca682918000d0756).toArray⟩
theorem h104:check 5 104 d104=true:=by decide+kernel
def d105:Row:=⟨BCurve 54 47 0x2b8122bcfd922ad2c008cc506efa850f9831e638082c980f51e0201a1fe1f02f7b03ad42d4e36583da9c72c8ca37d732f1880b40000000000018a79438f90ff8000c00000000000306bc2ee17837e0010000000000005f10bad479ce180010007,decode 5 1 0x76b4b6c593702d40005a0000300002000010007,(AH 7 0x2c0afa023e00033000002d4b019280518000cc4d950326c0c8a028e0003411c14192b064281468000d00005064ac190a051a0003400014324b0c86828b8000d06ec).toArray⟩
theorem h105:check 5 105 d105=true:=by decide+kernel
def d106:Row:=⟨BCurve 55 47 0xaf242e35d0f7ab4a00233141bbea09fb5ebc89ffe859201ea3c040343000295229ab824210e58587769de6663ac70c92bbd4059000000000000646fbbfda5800800300000000000062a4b0eeb8443c00200000000000060d9a5dfcb08700010007,decode 5 1 0x76b4a6c59270210000590000300002000010007,(AH 7 0x502bac0ada02360003400000210b018e80508000cc4555031ec0c6a0286000340fa9418eb063681438000d00005063ac18da050e000340001431db0c6a82858000d0680).toArray⟩
theorem h106:check 5 106 d106=true:=by decide+kernel
def d107:Row:=⟨BCurve 55 47 0xb043d177aba6ab4900233141bbea09d6738b39b07059201ea3c04034301e6274d853574148e7a58b129f5a6814b234c401cc0580000000000006645671e9ec31800300000000000064761c0879846400200000000000062a6d0f25445b00010007,decode 5 1 0x76b496c59270148000580000300002000010007,(AH 7 0x2c0aca02320003300000148b018a80508000cc3ce50316c0c4a0282000340d85418bb0626813f8000d00005062ec189a04fe0003400014316b0c4e827f8000d0611).toArray⟩
theorem h107:check 5 107 d107=true:=by decide+kernel
def d108:Row:=⟨BCurve 55 47 0xb16374b98655ab4800233141bbea09b06ecfdb81a859201ea3c04034303cd8df077b94807ce9c58eaea0ce69f2dd642d4aac058000000000000681f5246d00910003000000000000664bc72972c77400200000000000064783c0c1585d80010007,decode 5 1 0x76b486c5927007c000580000300002000010007,(AH 7 0x140abb02aa808b8000d0000001f2c061a013e000330d12c0c3a027a000330b554187b061a813d8000d00005061ec186a04f6000340001430fb0c3282798000d05a1).toArray⟩
theorem h108:check 5 108 d108=true:=by decide+kernel
def d109:Row:=⟨BCurve 50 37 0xb28317fb6104ab478cc506efacd09e028e964e2c88000000002683d68a66d32000c0000000013415e802c79e80040000000009a068dd92c5200010005,decode 5 1 0x76b476c5916c0036c0026c0010005,(AH 7 0xb02a680898000cc000000014061b0182804e8000d02b85030ac0c1a027600034091d4184b060a813a8000d000050612c182a04ea0003400014308b0c1682738000d052e).toArray⟩
theorem h109:check 5 109 d109=true:=by decide+kernel
def d110:Row:=⟨BCurve 50 37 0xb3a2bb3d3bb3ab468cc506efacd9a6e5413d622c880000000026cc1d9ffc0bc000c000000001365820af716380040000000009b27aa2f813480010005,decode 5 1 0x76b466c5916c0036c0026c0010005,(AH 7 0x140a8b029e80888000d0000000014060b017e804d8000d022950302c0bfa026e0003406d94180b05fe81378000d000050602c17fa04de0003400014301b0bfa826e8000d04b9).toArray⟩
theorem h110:check 5 110 d110=true:=by decide+kernel
def d111:Row:=⟨BCurve 50 37 0xb4c25e7f1662ab458cc506eface2afc7f3e4762c8800000000271464b591446000c000000001389a595c1b2880040000000009c48c685d61700010005,decode 5 1 0x76b456c5916c0036c0026c0010005,(AH 7 0xb029a80878000cc00000002c05fa0136000330662c0bea026a00033048d417db05f281348000d0000505f6c17ca04d200034000142fab0be282688000d0441).toArray⟩
theorem h111:check 5 111 d111=true:=by decide+kernel
def d112:Row:=⟨BCurve 50 37 0xb5e201c0f111ab448cc506efacebb8aaa68b8a2c8000000000275cabcb267d0000c0000000013adc9208c4ed80040000000009d69e2dc2af980010005,decode 5 1 0x76b446c5906c0036c0026c0010005,(AH 7 0x50296c0a4a021a0003400000000b017a804c8000cc104502f6c0bca0262000340235417ab05e281318000d0000505eac178a04c600034000142f4b0bc682628000d03c8).toArray⟩
theorem h112:check 5 112 d112=true:=by decide+kernel
def row (v:ℕ):Row:=match v with
 | 0=>d0
 | 1=>d1
 | 2=>d2
 | 3=>d3
 | 4=>d4
 | 5=>d5
 | 6=>d6
 | 7=>d7
 | 8=>d8
 | 9=>d9
 | 10=>d10
 | 11=>d11
 | 12=>d12
 | 13=>d13
 | 14=>d14
 | 15=>d15
 | 16=>d16
 | 17=>d17
 | 18=>d18
 | 19=>d19
 | 20=>d20
 | 21=>d21
 | 22=>d22
 | 23=>d23
 | 24=>d24
 | 25=>d25
 | 26=>d26
 | 27=>d27
 | 28=>d28
 | 29=>d29
 | 30=>d30
 | 31=>d31
 | 32=>d32
 | 33=>d33
 | 34=>d34
 | 35=>d35
 | 36=>d36
 | 37=>d37
 | 38=>d38
 | 39=>d39
 | 40=>d40
 | 41=>d41
 | 42=>d42
 | 43=>d43
 | 44=>d44
 | 45=>d45
 | 46=>d46
 | 47=>d47
 | 48=>d48
 | 49=>d49
 | 50=>d50
 | 51=>d51
 | 52=>d52
 | 53=>d53
 | 54=>d54
 | 55=>d55
 | 56=>d56
 | 57=>d57
 | 58=>d58
 | 59=>d59
 | 60=>d60
 | 61=>d61
 | 62=>d62
 | 63=>d63
 | 64=>d64
 | 65=>d65
 | 66=>d66
 | 67=>d67
 | 68=>d68
 | 69=>d69
 | 70=>d70
 | 71=>d71
 | 72=>d72
 | 73=>d73
 | 74=>d74
 | 75=>d75
 | 76=>d76
 | 77=>d77
 | 78=>d78
 | 79=>d79
 | 80=>d80
 | 81=>d81
 | 82=>d82
 | 83=>d83
 | 84=>d84
 | 85=>d85
 | 86=>d86
 | 87=>d87
 | 88=>d88
 | 89=>d89
 | 90=>d90
 | 91=>d91
 | 92=>d92
 | 93=>d93
 | 94=>d94
 | 95=>d95
 | 96=>d96
 | 97=>d97
 | 98=>d98
 | 99=>d99
 | 100=>d100
 | 101=>d101
 | 102=>d102
 | 103=>d103
 | 104=>d104
 | 105=>d105
 | 106=>d106
 | 107=>d107
 | 108=>d108
 | 109=>d109
 | 110=>d110
 | 111=>d111
 | 112=>d112
 | _=>default
theorem checked (v:ℕ) (hv:5+v≤117):check 5 v (row v)=true:=by
 have hvl:v≤112:=by omega
 interval_cases v
 · exact h0
 · exact h1
 · exact h2
 · exact h3
 · exact h4
 · exact h5
 · exact h6
 · exact h7
 · exact h8
 · exact h9
 · exact h10
 · exact h11
 · exact h12
 · exact h13
 · exact h14
 · exact h15
 · exact h16
 · exact h17
 · exact h18
 · exact h19
 · exact h20
 · exact h21
 · exact h22
 · exact h23
 · exact h24
 · exact h25
 · exact h26
 · exact h27
 · exact h28
 · exact h29
 · exact h30
 · exact h31
 · exact h32
 · exact h33
 · exact h34
 · exact h35
 · exact h36
 · exact h37
 · exact h38
 · exact h39
 · exact h40
 · exact h41
 · exact h42
 · exact h43
 · exact h44
 · exact h45
 · exact h46
 · exact h47
 · exact h48
 · exact h49
 · exact h50
 · exact h51
 · exact h52
 · exact h53
 · exact h54
 · exact h55
 · exact h56
 · exact h57
 · exact h58
 · exact h59
 · exact h60
 · exact h61
 · exact h62
 · exact h63
 · exact h64
 · exact h65
 · exact h66
 · exact h67
 · exact h68
 · exact h69
 · exact h70
 · exact h71
 · exact h72
 · exact h73
 · exact h74
 · exact h75
 · exact h76
 · exact h77
 · exact h78
 · exact h79
 · exact h80
 · exact h81
 · exact h82
 · exact h83
 · exact h84
 · exact h85
 · exact h86
 · exact h87
 · exact h88
 · exact h89
 · exact h90
 · exact h91
 · exact h92
 · exact h93
 · exact h94
 · exact h95
 · exact h96
 · exact h97
 · exact h98
 · exact h99
 · exact h100
 · exact h101
 · exact h102
 · exact h103
 · exact h104
 · exact h105
 · exact h106
 · exact h107
 · exact h108
 · exact h109
 · exact h110
 · exact h111
 · exact h112
end AYS
namespace AYA
open DZ CL
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
def d0:Row:=⟨BCurve 56 43 0x219ff2f7291a95d986954fada180e082a031369ee79b88cfb0a3e44110c1d4dded62f2f811a8a460cd4a0aa8e92e651441796d600760002c003a2021000108b45000000000000016600cd0006e000c00000000000007d80490002c0004000000000000036001f8001380010008,decode 5 1 0x76bb369e6e657c0597960168a0000300002000010008,(AH 7 0xaecc1e6e7015d8056a0156000345f0180afa02b2000335e59c19560652818f8000d1bc07068d81a2a067a0003476f9c29860a5a828a8000d168a).toArray⟩
theorem h0:check 6 0 d0=true:=by decide+kernel
def d1:Row:=⟨BCurve 56 43 0x222fc498167215d906954fada180e2905bfdc2cc079548cfb0a3e4411216675ae295faf5b1a8a460cd4a0d3d40efaaee3d783ea00800002c004b402a400134b3c00000000000001e5011200084000c0000000000000b8006900037000400000000000003ec0248001600010008,decode 5 1 0x76bb269e55657ad59783016780000300002000010008,(AH 7 0xaec81e556015e80558000cd7ad702c180afa02b2000345e0dc1966065681908000d1ba57069581a4a0682000347685c29a60a62828c8000d1678).toArray⟩
theorem h1:check 6 1 d1=true:=by decide+kernel
def d2:Row:=⟨BCurve 56 43 0x22bf963903c995d886954fada180e497827aa157a78ec8cfb0a3e44113622a2733e4c2f331a8a460cd4a1c3c2c45011ed976fbb0159a08f60040b07c7634a2b8d00000000000001a80336e15d6000c0000000000000a54145088ad800400000000000003b40775033800010008,decode 5 1 0x76bb169e3b657995976f0171a0000300002000010008,(AH 7 0x2bb1078ed8057a015a000335e6580b0a02b6000335dbdc1976065a81928000d1b8b7069d81a6a068600034760dc29c60a66828e8000d1666).toArray⟩
theorem h2:check 6 2 d2=true:=by decide+kernel
def d3:Row:=⟨BCurve 56 43 0x234f67d9f12115d806954fada180e69ea8f77fe3478848cfb0a3e44114b6bca42917caf0b1a8a460cd4a12779916976f7d75ce4819f60ab2005574a15243aab2a8000000000000239643ae1c7c000c0000000000000e391b598b91800400000000000005538a6e047280010008,decode 5 1 0x76bb069e21657855975c016550000300002000010008,(AH 7 0x2bb007885c0586015e80568000d1785702c580b0a02b6000345d71c1996066281938000d1b70706a181a7a068e000347595c29e60a6e82908000d1655).toArray⟩
theorem h3:check 6 3 d3=true:=by decide+kernel
def d4:Row:=⟨BCurve 56 44 0x11ef9cbd6f3c4aebc1a553eb68603a2b1931030419e07119f6147c8822c04fee0f4cd25dc91a8a460cd4a150bf0d7dd49797488700f29063700366865452a37590c0000000000000b7e1587090000030000000000000258846f31dc9000800000000000007460df285e480010008,decode 5 1 0x76baf69e076577259748016430000300002000010008,(AH 7 0x2baf0781d8058a015a000335dc980b1a02ba000335d21c19b6066681958000d1b55706a981a9a0696000347519c2a060a7682928000d1643).toArray⟩
theorem h4:check 6 4 d4=true:=by decide+kernel
def d5:Row:=⟨BCurve 56 44 0x1237858de5e80aeb81a553eb68603aace2d03aa701ded119f6147c8822e9c8479976ab5d791a8a460cd4a17a048992323757349bc115707150043627c0f337758c40000000000000e699aae0b18800300000000000002fea5961254d0008000000000000098b9202878e00010008,decode 5 1 0x76bae69ded6575e59734016310000300002000010008,(AH 7 0xaeb81ded6016280568000cd75e702c980b1a02be000345cd1c19c6066e81968000d1b39706b181aba069a0003474a1c2a260a7e82948000d1631).toArray⟩
theorem h5:check 6 5 d5=true:=by decide+kernel
def d6:Row:=⟨BCurve 56 44 0x127f6e5e5c93caeb41a553eb68603b2eac6f7249e9dd2119f6147c88231340a123a0845d291a8a460cd4a1a34a05a68fd71720b08138507f30051a895073d95587c00000000000011a820608d68800300000000000003b986dfd2daf00080000000000000c24169e096f00010008,decode 5 1 0x76bad69dd26574a597200161f0000300002000010008,(AH 7 0xaeb41dd26016280578000cd74a702cd80b2a02be000345c81c19e6067681988000d1b1e706b581aca06a2000347425c2a460a8682968000d161f).toArray⟩
theorem h6:check 6 6 d6=true:=by decide+kernel
def d7:Row:=⟨BCurve 56 44 0x12c7572ed33f8aeb01a553eb68603baed0babe8471db6119f6147c88233cb8faadca5d5cd51a8a460cd4a1cc8f81baed76d70cc5415b308d100613ab02d489158340000000000001539a69e8ff000030000000000000489284c736ef00080000000000000f0f9bc50b8780010008,decode 5 1 0x76bac69db6657355970c0160d0000300002000010008,(AH 7 0x2bac076d9c0596016280578000d1735702cd80b2a02c2000345c31c19f6067a819a8000d1b02706bd81aea06aa0003473a9c2a660a8e82988000d160d).toArray⟩
theorem h7:check 6 7 d7=true:=by decide+kernel
def d8:Row:=⟨BCurve 56 44 0x130f3fff49eb4aeac1a553eb68603c309a59f62759d9b119f6147c882365175e2377ae5c851a8a460cd4a1f4ba73893e4216f7da017e109af007218cd81546b57e8000000000000191e2d6812af0003000000000000056d89dbf410d0008000000000000124e21778dd780010008,decode 5 1 0x76bab69d9b65721596f7015fa0000300002000010008,(AH 7 0xaeac1d9b6016680578000cd721702d180b3a02c2000345bddc1a160682819b8000d1ae6706c581b0a06b200034732dc2a860a9a829a8000d15fa).toArray⟩
theorem h8:check 6 8 d8=true:=by decide+kernel
def d9:Row:=⟨BCurve 56 44 0x135728cfc0970aea81a553eb68603cb263f92dca41d7f119f6147c88238e8fb7ada1875c351a8a460cd4a21dffef9d9be1d6e3eec1a0f0a8d008442ed03612357a00000000000001d55b4bd15a580030000000000000666ab8e54c09000800000000000015dfa7b5905f00010008,decode 5 1 0x76baa69d7f6570d596e3015e80000300002000010008,(AH 7 0x2baa075fd8059a0162000335c3580b4a02c6000335b8dc1a360686819d8000d1aca706cd81b2a06b60003472b1c2aa60aa2829d8000d15e8).toArray⟩
theorem h9:check 6 9 d9=true:=by decide+kernel
def d10:Row:=⟨BCurve 56 45 0x273e23406e8595d481a553eb68603d3288447a04c9d6208cfb0a3e4411db770d91a76c2df046a291833528918ab85afb2b45b39f6eea4a09a5ccfb3e5962c746aeabf1b3372e1c797faa803c2505ce4381c0e1e85b5804bdc8759b75c9c5600000000000008780f276634e000c0000000000000ee91ac72afc6001000000000000019c42e7f131e0001000a,decode 5 1 0x76ba969d62656f8596ce555d514e4300e2b000030000200001000a,(AH 7 0x2ba907589c05a6016680588000d16f8702d580b4a02ca000345b39c1a46068e819f8000d1aad706d181b3a06be000347231c2ad60aaa829f8000d15d5).toArray⟩
theorem h10:check 6 10 d10=true:=by decide+kernel
def d11:Row:=⟨BCurve 56 45 0x4f9be9c2b7ba2ba8034aa7d6d0c07b65591f8c7ea3a8c119f6147c8823e06674ad78b15b8c8d4523066a5137b82ec025266b5d41a87a6eccc7c3b1422cc21eb15c383cc018dcf0f82ebdcc6b77781c850bc05a6129cda77828e1bf1d338aa1bff8812ee3a9f83e43203190654c332b07ff7a74d83b0ad6f89d4c438c20f35862480563d9948be96983e00000000000009af7142670e4000c000000000000112e5eb76c93600100000000000001dfbb5d416148001000d,decode 5 1 0x76ba869d46656e3596ba555c314e4218e2a2cca908c4300c1f000030000200001000d,(AH 7 0xaea01d466016a80588000cd6e3702d980b5a02ca000345ae9c1a66069681a08000d1a91706d981b5a06c60003471b1c2af60ab282a18000d15c3).toArray⟩
theorem h11:check 6 11 d11=true:=by decide+kernel
def d12:Row:=⟨BCurve 56 45 0x142ee341249a4ae9c0d2a9f5b4301f19686d893cece948467d851f220902313608c98096ce235148c19a9452f369e9d36302d4b11cc812618ffb5a4f0d422f8c56c2258670d76a5f57738269d9318720c5c63cbdc3a78f9e2e20bb8314e298cbf1065584ef19d3602721bd9951185df7442d2dcad23ef4ecab4310a3ad4eb8a5138de4bda4574b3460f4829cd799ee30439308ae0b264ac6968104c8693806144ac4ec63f94b40000000000000afb938047f58000c000000000000139d22ed6e462001000000000000022863db499428001000f,decode 5 1 0x76ba769d29656ce596a5555b014e4118e292cca808c4224c1e28ac600a5a000030000200001000f,(AH 7 0xae9c1d296016a80598000cd6ce702d980b5a02ce000345a95c1a86069e81a28000d1a74706e181b7a06ce000347131c2b160aba82a38000d15b0).toArray⟩
theorem h12:check 6 12 d12=true:=by decide+kernel
def d13:Row:=⟨BCurve 57 45 0x51db30466d182ba6034aa7d6d0c03eb2f5265eb461d0b08cfb0a3e44090c48cee634d4d6b9235148c19a922bfc6411cebe356908e7b8c487f74171e6acb99df1959d8ef736dde61414642dc1601e5ce409138c5c679bbb55b7a04f370bce28927e3ec5f50b9da9e1781db7f8ca791f896443de397e28a3694b258c419483dcdda5ab3cc6caccfc07ecc1d963302b395b3242fa8ecf4a668ac5985330e0d42b1d044aa2fb5fd0a59a0e11638702803678e035e72bca1200000000000003171d78423aa800300000000000002c6aced26029400200000000000002763c6209ca800010010,decode 5 1 0x76ba669d0b656b9596905559d14e4018e282cca708c4124c1d28ac550a5900a120000300002000010010,(AH 7 0xae981d0b6016a80598000cd6b9702dd80b6a02d2000345a41c1a9606a281a48000d1a57706e981b9a06d60003470adc2b360ac282a68000d159d).toArray⟩
theorem h13:check 6 13 d13=true:=by decide+kernel
def d14:Row:=⟨BCurve 57 45 0x52fad38847c72ba5034aa7d6d0c03f331971aaeee9ced08cfb0a3e44091619ea3e810716a4235148c19a922e7f132eb3cae967a9410d7fdf26440d0cdf0750f6d58a948cd185f1943dd726bfcadcece3f96e512116c2bdb15ede5175da0e27983d6d2691d3c2824feaee9240ca697c230e66533bd0da0197beff4c409a527ed8b70b5dc130b37e4570c1c9c126a73edab442337b13d8fd4ac49e70a12de68b3d8a814e852264a58a38e1b962fa2b727f1a3b02318a11ab4127a8771803ca26acfeb6f4816000000000000037486192a7b68003000000000000031ee585563fdc00200000000000002c944f18204500010011,decode 5 1 0x76ba569ced656a45967a5558a14e3f18e272cca608c4024c1c28ac450a584ca11008160000300002000010011,(AH 7 0xae941ced7016d805aa0166000345a9180b7a02d20003359e9c1ab606aa81a68000d1a39706f181bba06de000347029c2b560ace82a88000d158a).toArray⟩
theorem h14:check 6 14 d14=true:=by decide+kernel
def d15:Row:=⟨BCurve 57 45 0x541a76ca22762ba4034aa7d6d0c03fb33dbcf72971ccf08cfb0a3e44092031831bec5b568f235148c19a923101c24b98d79d66599a623b3655c6a8065a39ac11d5779a226c2dfd1c67475b487b9a78e3e9c915e5c5e9c00cd89c12749bce269dfc9b872e93e757e659ab3ac4ca59d8bcb888c7be235d165f0b32cc3fa02120d3c86b7eb8acfc354ef0c1ba1f1d234459b6413dcd7bb1bdcac3a48e117af8eb5e0da97bb7a728a57a9bf8dd7856aa8ebaeff7549b0a10ad7716f8ef72a086e88b84edec799b5a139187e080431ef5f56fea475f00000000000003d71ec2cabfa0003000000000000037c4e263e809c00200000000000003217d89b241980010012,decode 5 1 0x76ba469ccf6568f596655557714e3e18e262cca508c3f24c1b28ac350a574ca10487990075f0000300002000010012,(AH 7 0xae901ccf6016e805a8000cd68f702e180b7a02d6000345995c1ad606b281a88000d1a1c706f981bda06e6000346fa5c2b860ad682aa8000d1577).toArray⟩
theorem h15:check 6 15 d15=true:=by decide+kernel
def d16:Row:=⟨BCurve 57 45 0x553a1a0bfd252ba3034aa7d6d0c0403362084363f9cb108cfb0a3e44092a491bf957af967a235148c19a92338471687de4516509f3b6f68d854942d31e50abb315649fb806d6089c90b4cb5b71e5d0e3da23daaa7510c26824d99233514e25a3bbc9e7cb540c2aa4c453e288ca4a355662ab3cc075b1e1bf35ce8c3ea5efc2ced9c39fad3fa720f96cc1aa7d139f49d8b840198606d73ecac2aaab81c80b4b7e8dc32a92ee24a56aff10018db32c248be7c90e718a0fb3d77878232a93c2b17924eba4798c0014a8884f8049ee81a6749cc6f2000000000000043ee77523075000300000000000003dee6cfdec4d4002000000000000037ee62a9a82580010012,decode 5 1 0x76ba369cb16567a596505556414e3d18e252cca408c3e24c1a28ac250a564ca0f48798006f20000300002000010012,(AH 7 0xae8c1cb16016e805a8000cd67a702e580b8a02da000345941c1af606ba81aa8000d19fe7070181bfa06ee000346f1dc2ba60ade82ad8000d1564).toArray⟩
theorem h16:check 6 16 d16=true:=by decide+kernel
def d17:Row:=⟨BCurve 57 45 0x5659bd4dd7d42ba2034aa7d6d0c040b1e0ffa43621c9408cfb0a3e4409341a3751a3e1d664235148c19a9235f577e10223bd63aa4d0bb1e4b44bdd732b4c4c4b9550a54da17e1424ba1f76f8ae3018e3ca7e9f6f243744c34396d0aed1ce24a97af848681c30fa8b2ae8ba80ca3a91f00ccdb142c7d863b838c4cc3dabbe64c9eb23c09ee8b4419af0c19adb0a1b4f583a3ec6a4b54c158ac1b0c8f2151dab9f0ace5b16f750a55b622725a30fadba2b56ca37290a0eba37d9f756eaab92693a9f85dc797ca615bf88be8051110de2f986c6f100000000000004abe0303352780030000000000000446af82370c8400200000000000003e17ed43ac6900010012,decode 5 1 0x76ba269c94656645963a5555014e3c18e242cca308c3d24c1928ac150a554ca0e48797006f10000300002000010012,(AH 7 0xae881c9470171805ba016a00034599180b9a02da0003358e9c1b1606c281ac8000d19e07070981c1a06f6000346e99c2bc60aea82af8000d1550).toArray⟩
theorem h17:check 6 17 d17=true:=by decide+kernel
def d18:Row:=⟨BCurve 57 45 0x5779608fb2832ba1034aa7d6d0c041305ff7050849c7908cfb0a3e44093deb52a9f014164e235148c19a92387826fde73071624aa6606d3be3ce77e6812c94f9553daae33c261fa4e3875e20300830e3bad96433d35e471e34d3cded6ece23af3a26a904dc55c7998d6960c0ca2aee89b6f0264519d09c4a1a22cc3cb18d06c4fc83e18da823970874c18b39009754d73c3d4529870b16cac0b6e662623013bf84cb0d43eae4a54bc53e49b86c2f4f993cfacec18a0dc19db2c92daaf670246dfd1c4c796c0983b768aa2c35ef0f7720368778d4c16d6892d8058869aaafea846f0000000000000051e08f3fba11800300000000000004b3a83d4757ac00200000000000004494786930e400010013,decode 5 1 0x76ba169c796564e596245553d14e3b18e232cca208c3c24c1828ac050a544ca0d0479648778006f00000300002000010013,(AH 7 0xae841c7960172805b8000cd64e702e980b9a02de000345891c1b3606ca81ae8000d19c17071181c3a0702000346e11c2bf60af282b28000d153d).toArray⟩
theorem h18:check 6 18 d18=true:=by decide+kernel
def d19:Row:=⟨BCurve 57 45 0x589903d18d322ba0034aa7d6d0c041aedeee65da71c5d08cfb0a3e440947bc6e023c465638235148c19a923ae92d766b6fdd60eaffb5289312d1122d1ff17e9e9529b078d6ce2b2d0cec80d1f7df38e3ab3428f882854978f89089ebff4e22b4f95509a19c7a91cfebd6063cca1b4b2361129b476b9a8b74d6e14c3bb75ba8c00ddc02797df52116f8c17b96f7135a56be3b95147c196d4abfbd03d2af4273dffbb941197874a53c28556dcdc8b0e4d59a5ad53b4a0cc7d70937dd130f27170ec8f170795c6f89cf5be5adb2848af9c8008777df217ed899c80604f27fe840146ef000000000000059561c07bf3300030000000000000525d1010fa64c00200000000000004b64041a359680010013,decode 5 1 0x76ba069c5d656385960e5552914e3a18e222cca108c3b24c1728abf50a534ca0c0479548777006ef0000300002000010013,(AH 7 0xae801c5d60172805b8000cd638702ed80baa02e2000345839c1b5606d281b08000d19a27071981c5a070a000346d85c2c160afa82b48000d1529).toArray⟩
theorem h19:check 6 19 d19=true:=by decide+kernel
def d20:Row:=⟨BCurve 57 45 0x59b8a71367e12b9f034aa7d6d0c0422d5de5c6ac99c4008cfb0a3e4409518d895a88789622235148c19a923d5a33eeefaf495f8b5909e3ea4253ac47079b1058d515b60e717636ad364edf0e054414e39b8eedbd31ac4bd38ecd04aa83ce21bab8836a3e649f592e462edbe0ca0ba7bd0b350fc9bd3631386bfb8c3abd2a4abb1f3c23626a28e01c80c16bf4ed8f5fd5c039b6659471ef0abec32142fc54d4006f98f697c838a52c8b6c91e3253279e06eea4a95ca0bce105fa68c8327daed3946aaa8794cd58fe74f212f2ee70631efbc4776e9819048a0b80686ab5dd8991c6ee0000000000000611ea95b448c0003000000000000059d29cd8ff864002000000000000052869056ba8080010013,decode 5 1 0x76b9f69c4065622595f85551514e3918e212cca008c3a24c1628abe50a524ca0b0479448776006ee0000300002000010013,(AH 7 0xae7c1c4070175805ca016e00034588980bba02e20003357e1c1b7606da81b28000d19837072581c8a0712000346cf9c2c460b0682b78000d1515).toArray⟩
theorem h20:check 6 20 d20=true:=by decide+kernel
def d21:Row:=⟨BCurve 57 45 0x5ad84a5542902b9e034aa7d6d0c042abdcdd277ec1c2308cfb0a3e44095b5ea4b2d4aad60c235148c19a923fcb3a6773eeb55e2bb25e9f41715646343829430b1501bba40c1e42355fae78d458a7d8e38be9b281e0d34e2df7893e28fbce20c077b1cadb24c41db49c737fd4c9fc0456b55784cc0ea38d94df7c8c39c2f8ecb6309c44486cbed3ee04c15c52e40b6554c237a91cd017310abdc93eb349673420e06a2dbeda30a51cee83b5f881b40eb9baa92ed18a0ad449b6153beb408ba6ed760c44793d3b95ff425cb0ab16811f97698775f3e1a1b8a7a8070d944480f59c6ed0000000000000693a373a4a1c80030000000000000619b2a2c84df4002000000000000059fc1d1ebfa200010013,decode 5 1 0x76b9e69c236560c595e25550114e3818e202cc9f08c3924c1528abd50a514ca0a0479348775006ed0000300002000010013,(AH 7 0xae781c2360176805c8000cd60c702f180bba02e6000345789c1b9606e281b48000d19647072d81caa071a000346c6dc2c660b0e82b98000d1501).toArray⟩
theorem h21:check 6 21 d21=true:=by decide+kernel
def d22:Row:=⟨BCurve 57 45 0x5bf7ed971d3f2b9d034aa7d6d0c04328b6809ce889c0608cfb0a3e440964e9428601bb15f5235148c19a92423c40dff82e215cbc0bb35a98a0d8dff4b19c1dd1d4edc139a6c64db5890b4e24f19978e37c4477468ff9d08832c536643fce1fc636e02b77ece8df62eea453ecc9ec60f05f79f94e5fe2a08a2b594c38c8c78eb141f4652b85b6fc6098c14cb0da876ad444356d3a2f0bc74abccf5c23967994414e2ce68eae58a50d519ada0dde35a3617d9781ee0a09da830c83eb5b5939442b5751f0792da19c173598322712fbc2bf084774f2538ee2d333554a7245a2e9d86ecfe41b328ae980799ad33e155946aa000000000000071a8c5a4cfe48003000000000000069b6b80b8a6fc002000000000000061c4aa7244fb00010014,decode 5 1 0x76b9d69c06655f5595cb554ed14e3718e1f2cc9e08c3824c1428abc50a504ca090479248774446ec006aa0000300002000010014,(AH 7 0xae741c0660176805c8000cd5f5702f580bca02ea00034572dc1bb606ea81b68000d19447073581cca0726000346be1c2c960b1a82bc8000d14ed).toArray⟩
theorem h22:check 6 22 d22=true:=by decide+kernel
def d23:Row:=⟨BCurve 57 46 0x2e8bc86c7bf715ce00d2a9f5b43010e9cd5dff6eac6fa0119f6147c8812dd74bbbc9bdaabbe235148c19a9244ad47587c6d8d5b5632840af7e7edbcc439f9ccc88a6cb1b3d05b964f6c9957bff4227e38d993e78167e41a5c48101dac53e9c3ccbf60e8c14ad0d9e393cc0f65cc9d65ec504ce37285879b50c2ace261bb3a58c2b14d52182ed44567288304da1da206e0a68c66057b6295139576d57993e38bf461b8e1210744b8a4f6da58ff119d5b9bebdbdaa1f5e504382f18bca6b0dc78f13cba90021e45c0f445e51a76745b8ec36cd310ee6f95047c0db32cfe115624d78046eb8450e24c5ac404157b15fcdc822b200000000000001e9a9526b5790000c0000000000000e44a8cec206f8004000000000000069e038514a8b80010014,decode 5 1 0x76b9c69be8655df595b5554d914e3618e1e2cc9d08c3724c1328abb50a4f4ca080479148773446eb005640000300002000010014,(AH 7 0xae701be86017a805c8000cd5df702f980bda02ee0003456d5c1bd606f281b88000d19247073d81cea072e000346b51c2cb60b2282be8000d14d9).toArray⟩
theorem h23:check 6 23 d23=true:=by decide+kernel
def d24:Row:=⟨BCurve 57 46 0x2f1b9a0d694e95cd80d2a9f5b430110903c6dcc91e6f28119f6147c8812f089f762f5fb2b90235148c19a92471e4dd100acf959e65f2e68a37faf0977bf97deb22a62b3193705992f76ef2ad93d421838d59f4019fdc8faa784178c641e51c3ad1b53cecb16d325a3786c9980cc9c68d11d9df71a980eaf51fada0261b351934a9d92d29ba3eb37affe93049ad98efeeba59060d34eadb13f9574db9704309e5c822086dd28c564a4e70be4911c4b9c660e34813a654503b9bd6e58528ae2a2ca510bbd181e41cdb508e381e6a3ce5e0531c348ee5004d009ee3327d274933f68e606ea8980eb045e3c0460b796650ff624a800000000000020dfb9071706c000c0000000000000f5cdaad82c6e80040000000000000724ec6bbd05380010014,decode 5 1 0x76b9b69bca655c85959e554c514e3518e1d2cc9c08c3624c1228aba50a4e4ca070479048772446ea004950000300002000010014,(AH 7 0x2b9b06f29805ea017600033572180bea02ee000335679c1bf606fa81ba8000d19047074981d1a073a000346abdc2ce60b2e82c18000d14c5).toArray⟩
theorem h24:check 6 24 d24=true:=by decide+kernel
def d25:Row:=⟨BCurve 57 46 0x2fab6bae56a615cd00d2a9f5b43011283a2fba23906eb0119f6147c8813039f3309501bab62235148c19a92497daba5241f1d58768bd8c64f17305614e9a841184a58347e9daf9c1181444cd517e16738d1aa98b293addaf2ba6ef2f3e729c38d7746b4d4e3557135dccbe69ccc9b6bb5eaef0abeaa945107f9ca0861ab68cdd289d8331f0d5bb2cb5923045b957bf6f6a3945b43ee3f61c51572e1b4747db0bca2851e1af2e024a4d73d702326f9dd3017c8bf8a4525033b4bc3f3fe66e8cbdc47c9632f1e3dda75cbe1e956d33acd3da6b1b8ee30749b97ceb3244ac8f7b0692106e98eb0f3bc61b404ae8c1b294526202000000000000023399d0a58a26000c000000000000107f6c9db38dc800400000000000007b1055b1d65300010014,decode 5 1 0x76b9a69bac655b159587554b014e3418e1c2cc9b08c3524c1128ab950a4d4ca060478f48771446e9004040000300002000010014,(AH 7 0x2b9a06eb1c05f6017a805d8000d15b1702fd80bea02f200034561dc1c16070281bd8000d18e37075181d3a0742000346a2dc2d060b3682c48000d14b0).toArray⟩
theorem h25:check 6 25 d25=true:=by decide+kernel
def d26:Row:=⟨BCurve 57 46 0x303b3d4f43fd95cc80d2a9f5b43011477098977e026e30119f6147c8813162773a56bf82b34235148c19a924bdd097947914156f6b88323faaef1a29bb82af7882a4db5e404599ef18b98bdb383e43238cdb5f14b2992bb3deb16515bae79c36dd3399adeaf57bc9ac0e9f09f4c9a6e9ab8401e66bd188072bfad3861a380085a761db3a26b25b6ba8f43041c5168ef01a19855575a17abcb9570e7d1e4cac31cc2e6a6da65bd14a4c76efbb531a7ddfa08989590a3c502bcda198faa40eef42720f373641e39e7368ee050c702a0dc6ccb9e58ee10e46725af332457c256fbe11286e893e0fc74652c04fef8a4497c121f3800000000000025a841307a4be000c00000000000011ac5e9f545b9800400000000000008424e5335c8a00010014,decode 5 1 0x76b9969b8c6559a5956f5549b14e3318e1b2cc9a08c3424c1028ab850a4c4ca050478e48770446e8003e70000300002000010014,(AH 7 0xae641b8c6017e805e8000cd59a7030180bfa02f60003455bdc1c46070a81bf8000d18c27075d81d6a074e000346995c2d360b4282c78000d149b).toArray⟩
theorem h26:check 6 26 d26=true:=by decide+kernel
def d27:Row:=⟨BCurve 57 46 0x30cb0ef0315515cc00d2a9f5b43011663dac79fe5c6db4119f6147c8813293caf4bc618ab04235148c19a924e3c674d6b03655586e52d81a64672ef0c2b1ffe74ca4337496b03a1d395ec7d748166b038c9c149e3bf778b89160da79b0f71c34e2f2c80e87b5a07d224c6ba95cc99717f8591320acf9b3d924c5352619b9742e262633425bd49437cf56303dd0d55e70ca09c4f0d92369477956eedef5517d57ce345211b815c3ca4b7a087473c561ec3e0a4034f64c5023e686f2b561cf51baadc89fc981e35f3f751deb84732008b92a0c060edf15432b38fb3254ae454b3b4f686e79911052c68a40551fd31c5b4ba1f30000000000000282ba5797c034000c00000000000012e3b0b265305800400000000000008d8c754062f880010014,decode 5 1 0x76b9869b6d65582595585548614e3218e1a2cc9908c3324c0f28ab750a4b4ca040478d4876f446e7003e60000300002000010014,(AH 7 0xae601b6d6017e805e8000cd5827030580c0a02fa000345561c1c66071681c18000d18a17076581d8a0756000346901c2d660b4e82ca8000d1486).toArray⟩
theorem h27:check 6 27 d27=true:=by decide+kernel
def d28:Row:=⟨BCurve 57 46 0x315ae0911eac95cb80d2a9f5b430118574155758ce6d30119f6147c88133bc4efe7e1f52ad6235148c19a92509bc5218e7589540711d7df51de343b664287596aea38b8aed1ada4b3a03f8c18104cac38c5cca27c555c6bd43b54f5b2d3b1c32e8b1f66f247dc52dc0862478ccc98746452e245b2e21c88669fec946193ae7d6a4ea894a903c65911e013039dc942df179ea04866969c117e956cf40cc564e7dd03a08cde45bd94a4a7d212d947045f8d9feb08c5964501bff6c4c701f6fb42677a8cefec1e3200b814dd1fb76159daaf25a958edd1c3fe417033263dce6e8a9702c6e69e410de46c1c05a799c39def1e1f280000000000002ac3c9e55dc88000c000000000000142562d6e60c080040000000000000974705d8e99e80010014,decode 5 1 0x76b9769b4c6556b595405547114e3118e192cc9808c3224c0e28ab650a4a4ca030478c4876e446e6003e50000300002000010014,(AH 7 0x2b9706d31c0606017e805e8000d156b7030980c1a02fe000345501c1c86071e81c48000d187f7077181dba0762000346869c2d960b5a82cc8000d1471).toArray⟩
theorem h28:check 6 28 d28=true:=by decide+kernel
def d29:Row:=⟨BCurve 57 46 0x31eab2320c0415cb00d2a9f5b43011a4412939d9286cb0119f6147c88134e4d3083fdd1aaa6235148c19a9252fb22f5b1e7ad52873e823cfd75b587a9fe6104de0a2e3a143857a795aa91e99e30b25938c1d7fb14eb414c1f5aec3ba29661c30ee7124cfc13de9db86bbc916b0c9777492033595af49c60efba60de618bc5b7f23aee152c3e9cf77aa643035e852fd7229da4416267482d2a956afa2a35b1fa4523f8ea22b3092ca498039e6b51b2a057466da5f338450141851a62add301685cfafc5c3c1e2e0d78d7db872790acc9c25a9088edb233c9cf50b3273080a480873786e5a371169c6f9405ffce59d22b3e1f200000000000002d70ae741f9ba000c0000000000001571750cd6eea80040000000000000a15496fcf07c00010014,decode 5 1 0x76b9669b2c65553595285545c14e3018e182cc9708c3124c0d28ab550a494ca020478b4876d446e5003e40000300002000010014,(AH 7 0x2b9606cb18060a017e00033554d80c2a03020003354a1c1cb6072a81c68000d185d7077d81dea076e0003467cdc2db60b6282cf8000d145c).toArray⟩
theorem h29:check 6 29 d29=true:=by decide+kernel
def d30:Row:=⟨BCurve 57 46 0x327a83d2f95b95ca80d2a9f5b43011c30e3d1c59826c28119f6147c881360d5712019ae2a76235148c19a92555a80c9d559d151076b2c9aa90d76d3d75ead045a4a23bb799f01aa75b4e39606e27b8738bde353ad81262c6a74d3796a5791c2ef43053305dfe0e8674ed59b3d0c967a2ded846cff071ac72d9b98166183dcf27a273395af6dcd1eb69c63031f411ccf2d9ba83a01043add3215690047a5ff0ca5444e38e8c8eee8a4883529fd5c60e120d42bdad84ac500c3136ffe59ad078d8b5dd832af1e2a1a399ad9ee97bff958cc3f75e8ed92a3955d31332822faf695859486e4a8a11f54730c065a9af462691a1f1800000000000030325325c17ca000c00000000000016c7e75437d8380040000000000000abb528ac779100010014,decode 5 1 0x76b9569b0a6553b595105544714e2f18e172cc9608c3024c0c28ab450a484ca010478a4876c446e4003e30000300002000010014,(AH 7 0x2b9506c29c06160182805f8000d153b7030d80c2a0302000345441c1cd6073281c98000d183b7078581e0a0776000346731c2de60b6e82d28000d1447).toArray⟩
theorem h30:check 6 30 d30=true:=by decide+kernel
def d31:Row:=⟨BCurve 57 46 0x330a5573e6b315ca00d2a9f5b43011e1db50fed9dc6ba4119f6147c8813735db1bc358aaa46235148c19a9257a835f997fead4f8797d6f854a4f81fee636b5453ea18bcdf05abad57bf34915225c46338b9eeac46170b0cb5890aaf0a1729c2cf9ef8190fac6332e8b1ad680ecc957d12bad580a71997bb2043c272617bf42d02137916329156cec5c28302dffd09c7389aac32426d742bdd95670665164c1f0564a079308796d8a47866b58f670f21ea4925a774cde50044a1c59a05870db1f2a3207ab21e2626fa5dd85607ef3f87ccd45978ed731360eb11b329153d64c99219c6e3add1280c768406b7ff934ea8b21f100000000000003308b7fa436b8000c0000000000001828b9ad08c8b80040000000000000b668bae77edd80010014,decode 5 1 0x76b9469ae965523594f85543114e2e18e162cc9508c2f24c0b28ab350a474ca00047894876b446e3003e20000300002000010014,(AH 7 0xae501ae96018680608000cd5237031180c3a03060003453e1c1d06073a81cb8000d18187079181e3a0782000346695c2e160b7a82d58000d1431).toArray⟩
theorem h31:check 6 31 d31=true:=by decide+kernel
def d32:Row:=⟨BCurve 57 46 0x339a2714d40a95c980d2a9f5b43012003f0fe6801e6b18119f6147c88138558f74e13232a14235148c19a9259f5eb295aa3894df7c48156003cb96bef0c9bf8566a0dbe446c55b037c984db7ffa70c238b5fa04deacefdd009791dc8170a1c2affaeaff1978657d3c9443f1c88c947ff78826944b2c133cc7b2afc061740b6789ffbe76b5a93a07a76d8302a0b8f6bf4398b02a26a2f40ee595650c828699316584efaaf9ef00f8a46898412171bd62b3a55b0bc8c164ffc6301b35b16313d592cad53bae1e2233bb20d6bd781e7f56c4193b38ed53832c78f2332a0747ef1cacc7c6e2b30130c479fc0717fc3696ea061f0800000000000035f3dcf1a5684000c0000000000001993ec1749c0280040000000000000c16f4dae066180010014,decode 5 1 0x76b9369ac66550a594df5541b14e2d18e152cc9408c2e24c0a28ab250a464c9ff047884876a446e2003e10000300002000010014,(AH 7 0xae4c1ac66018680608000cd50a7031580c4a030a00034537dc1d26074681ce8000d17f47079d81e6a078e0003465f5c2e460b8682d88000d141b).toArray⟩
theorem h32:check 6 32 d32=true:=by decide+kernel
def d33:Row:=⟨BCurve 57 46 0x3429f8b5c16215c900d2a9f5b430121ea2cece26606a8c119f6147c881397543cdff0bba9e2235148c19a925c43a0591d48654c67f12bb3abd43ab7d95a3eecd68a02bfa9d2ffb319d3d47490609ccd38b2055d7742d4bd4ba06901d12d31c29056dde52344e7c762f6993e814c9382dc5577a7f33e8d4c23e8902c616c22a211ec03f738b576c95cf3a3026174e3b74e96b421ada4ba8b6e9563129ff6e643c5a53bce44ff2d50a458c9ccb37c6ba37ce8cc07d42584ff47be70d15d3d19f86bd4f666d01e1e407be3d524e84db8c5b20e1b28ed33f2f806d2b32af91a958ed59e06e1b831397c7d74077a90de3b2d161f0000000000000038f3c20be772e000c0000000000001b097e92fabe880040000000000000ccc8e1000e1d00010014,decode 5 1 0x76b9269aa3654f1594c65540514e2c18e142cc9308c2d24c0928ab150a454c9fe0478748769446e1003e00000300002000010014,(AH 7 0x2b9206a8dc0626018680608000d14f17031980c5a030e000345319c1d56075281d18000d17d0707a981e9a079a000346551c2e760b9282dc8000d1405).toArray⟩
theorem h33:check 6 33 d33=true:=by decide+kernel
def d34:Row:=⟨BCurve 57 46 0x34b9ca56aeb995c880d2a9f5b430123d068db5cca26a00119f6147c8813a94f8271ce5429b0235148c19a925e915588dfed414ad81dd611576bfc03ad4c54355f69f7c10f39a9b5f9de235c83582c5d38ae10b60fd8b99d96a3901ef8e831c270b2d0cb2d10ea115bd8ad48228c9285c122c8bb9b5105e934e54b9e616439dc99d84977bbb60d13e5a9d3022230d0af5995b818d772c7a69a156118bd67335625c584e311b81bd8a448fb58458719e44613789b96fa04fec94cc66d0919201a7dc1840ae91e1a4d3ca6d38c587cebd496b2f950ed1462c394b3332beab558200c9c86e0bd61423480ec07dfbd8a3b71e21ef80000000000003c086749098b6000c0000000000001c8971201bc3d80040000000000000d87574dd961000010014,decode 5 1 0x76b9169a80654d8594ad553ef14e2b18e132cc9208c2c24c0828ab050a444c9fd0478648768446e0003df0000300002000010014,(AH 7 0xae441a806018a80618000cd4d87031d80c6a03120003452b5c1d86075a81d38000d17ac707b581eca07a60003464adc2ea60b9e82df8000d13ef).toArray⟩
theorem h34:check 6 34 d34=true:=by decide+kernel
def d35:Row:=⟨BCurve 57 46 0x35499bf79c1115c800d2a9f5b430125b6a4c9d72e46974119f6147c8813bb4ac803abeca97e235148c19a9260df0ab8a2921d49484a806f03037d4f6ae2dbce65e9ecc274a053b8dbe8719358e13b9838aa1c0ea86e9e7de1a10733f8a1a9c2510ec3b136dcec5b273a8011b7cc9188a5f019cf3f637d13faa8ca0c615c511721c48ed83eaafce740e50301e2ecbda76493bc0fa40d1b5623955f1edad780688de5cae96019f488a4392ce3d791c8250f2560c7113f24fe4adb1c08b4f3263bc8907e19291e1659fd69d1f3c8ac18837207d5a8ecf4d28f2293b32cdc1836d051c386dfc2914aec84640847823a97b86a1ef00000000000003f31cca90bb1c000c0000000000001e13c3beacd0180040000000000000e47509469e3a80010014,decode 5 1 0x76b9069a5d654bf59494553d914e2a18e122cc9108c2b24c0728aaf50a434c9fc0478548767446df003de0000300002000010014,(AH 7 0x2b9006975c0636018a80618000d14bf7032180c7a0316000345251c1da6076681d68000d1787707c181efa07b6000346405c2ed60baa82e28000d13d9).toArray⟩
theorem h35:check 6 35 d35=true:=by decide+kernel
def d36:Row:=⟨BCurve 57 46 0x35d96d98896895c780d2a9f5b4301279ce0b85192668f0119f6147c8813cd460d958985294c235148c19a92631b17440469b147b8772accae9b3e9b121dd5bb7509e143da06fdbbbbf2bf1910fbae5838a627674104835e2c98ce40d05999c2316ab69740a96ea4c51c119e4b4c908b8abd6ae2e775f2cc75333b9061546851a9b0d458c19446436ffb3301a3a8aa9f6f92c0061373b5a44f155d24f847cd7aee060de130246774a4295e6f699c7665d81e848a42f4c4fdcc6971a460cd2c5c4c41e498fa1e1266be2cd05b48db3ed2440ce720ecd5425ab074332dcd43319fa51306dec7c153a487dc08b1deef5000ae1ee8000000000000426ff22bede60000c0000000000001fa8766eade3480040000000000000f0c79e3b269c80010014,decode 5 1 0x76b8f69a3c654a65947b553c214e2918e112cc9008c2a24c0628aae50a424c9fb0478448766446de003dd0000300002000010014,(AH 7 0x2b8f068f18063a018a00033529980c8a031a0003351edc1dd6077281d98000d1762707cd81f2a07c200034635dc2f060bb682e58000d13c2).toArray⟩
theorem h36:check 6 36 d36=true:=by decide+kernel
def d37:Row:=⟨BCurve 57 46 0x36693f3976c015c700d2a9f5b4301297c87571e5506868119f6147c8813deb4581d28d9a918235148c19a92655723cf6641454618a3d52a5a32bfe6a2fd41f90209d5c53f6da7be9dfd0bedaba7a0c238a232bfd99a682e778ae5457fab81c211c6a97d4a7570ee357d61e7c84c8f8e6f8abbf68b886712a4847012614c7f8c319d19d94471e92872415301646497977a90c3fc25a69686d9155b2b15b81a8d4e264dca81d79c90a4198ffafba724a6a0fee3e52c1ac4fd4df7c7400ca9327c08d5b791bf1e0e737eefcec2b90a5ec10cc1bfd0ecb5b2263e54b32ebe36488e068ac6ddccf15c5c8b54091ed3a8644aae1ee000000000000045c2d7d1b0282000c000000000000214789301efd680040000000000000fd6d33bb2f3600010014,decode 5 1 0x76b8e69a1a6548c59461553ab14e2818e102cc8f08c2924c0528aad50a414c9fa0478348765446dd003dc0000300002000010014,(AH 7 0xae381a1a701918063a018a00034523180c9a031e000335185c1e06077e81dc8000d173c707dd81f6a07ce0003462b1c2f460bc682e98000d13ab).toArray⟩
theorem h37:check 6 37 d37=true:=by decide+kernel
def d38:Row:=⟨BCurve 58 46 0x1b7c886d320bcae3406954fada1804ad70b7d7ac5e99f70467d851f22027e0454549905c51c846a2918335226793305ac818d94478d07f8805ca60990ec090454bb4e523526a28e0be81d6044a393dad0e278f861c8c1341d84ee98840ec0c383e44538c6a8827337785e70f1390c8e9154580d0a31cd6cf3444e4bd430a24b635cc4af9671d0f96591c330c049482123e16398fe3b54b7c05c82ab2626650cf3f56468aa5553393e4a409c1868db1d2d3b4e33f6be658b27e67c30e6ddc414e26bf92fdbd2b8782a00fecb34a89272f09f984d2d61d92c43e3986a662faef17b9b762b06dcd22165148ecc04c73032ea4b350f6c000000000000124a9f66949e08003000000000000045e1f806003cf000800000000000010a65c9c6b80700010014,decode 5 1 0x76b8d699f765472594475539414e2718e0f2cc8e08c2824c0428aac50a404c9f90478248764446dc003db0000300002000010014,(AH 7 0x2b8d067dd8064a018e0003351c980caa032200033511dc1e36078a81df8000d1716707e981f9a07de000346201c2f760bd282ec8000d1394).toArray⟩
theorem h38:check 6 38 d38=true:=by decide+kernel
def d39:Row:=⟨BCurve 58 46 0x1bc4713da8b78ae3006954fada1804b4d4fd1428e319d40467d851f220280207e444527d515c46a29183352269cf3ce629f06d42c8fd29e5b161e13ec0d4b8b65574df64051d7de22f8468e0e22cf3134e26925c42b18c79e1abc066cce277383a4fd1e92bc1b75808dbf3ebda78c8d9439255e1dd9d6a5a410bdcd23309e5700a0bad25692828ee33becbcc039771c61e423597ce64e2583b1e2aae6ea13169641666c471aa384d68a3f9f3121fbc8114193aaab1125c427e288a393bb22f4fae4b2928b4240781a3401d72e4652d116fd0476d791d8ed237ab42b66309f74cac7f3f386dbd7516dcc924405004293d071f10f680000000000001329b8e1753580003000000000000049499dcea28cf0008000000000000117b1605dc10f80010014,decode 5 1 0x76b8c699d4654575942c5537d14e2618e0e2cc8d08c2724c0328aab50a3f4c9f80478148763446db003da0000300002000010014,(AH 7 0xae3019d4701958064a018e00034515d80cba03260003350b1c1e66079681e38000d16ef707f981fda07ea000346151c2fa60bde82f08000d137d).toArray⟩
theorem h39:check 6 39 d39=true:=by decide+kernel
def d40:Row:=⟨BCurve 58 46 0x1c0c5a0e1f634ae2c06954fada1804bc53978f5bed99b10467d851f2202823ca833f149e50f446a2918335226bf9a0cd2afab9411929d4435cf9a1e467bb1a516334d964b7d0d2e39f86fb9132c5015c4e25953268d705b1eb07e14453d8b038365b5045ecfb377c9759fcb46ffcc8c971df2af317ddfdd9bb790aff3309a629de4b0f516b3313ac31ae248c029a6179fe6e2d9fb85a11c199352aaa7adc120388d686fb2f80e5c924a3ea249db1c72f547d85b3c21a18127de9516409881c5135a4f7eec5a78780a6704e327e4132f309a5e007e21d8ae0311cfec66318fc036137fe486dadc81768495bc053aa0f6e4998b0f64000000000000140e02650dd07000300000000000004cc603ba24ead00080000000000001254ff7804a4f80010014,decode 5 1 0x76b8b699b16543d594115536514e2518e0d2cc8c08c2624c0228aaa50a3e4c9f70478048762446da003d90000300002000010014,(AH 7 0x2b8b066c58065a01920003350f580cca032a000335045c1ea607a281e68000d16c7708058200a07fa000346099c2fe60bee82f38000d1365).toArray⟩
theorem h40:check 6 40 d40=true:=by decide+kernel
def d41:Row:=⟨BCurve 58 46 0x1c5442de960f0ae2806954fada1804c3b7dccbd872198c0467d851f22028458d2239d6bf508846a2918335226e35ad588cd24d3f69567ea10891228a0373b514b044d3a56a8427e510898e153c016f8e4e2498088efc7ee9f4634c20d5ceb7383266cea2ae34b7a12300016904c0c8b9a02c0004525e914da38c70c4a30966e3b28a717c6d3dcfd052e7930c019d512dde9a29a7a194d9b8348b2aa68716f29dada6a72eded93c2ee8a3da562943d1dd94e1c45a9efd8c227daa188ed75e0952bcccff4ff38f077fa9a07ef2181d38d3d77a4ea2111d86ee2a8ebad66327fd3bd7e19fdc6d9e1b17f3c993405764b5c26c2030f6000000000000014f77bf15e6ed80030000000000000505729c8875690008000000000000133418f2e53c700010014,decode 5 1 0x76b8a6998c65422593f65534e14e2418e0c2cc8b08c2524c0128aa950a3d4c9f60477f48761446d9003d80000300002000010014,(AH 7 0xae28198c701998065a019200034508980cda032e000334fd9c1ed607b281e98000d169f708158204a080a000345fe1c30160bfa82f78000d134e).toArray⟩
theorem h41:check 6 41 d41=true:=by decide+kernel
def d42:Row:=⟨BCurve 58 46 0x1c9c2baf0cbacae2406954fada1804cb1c220854f699670467d851f22028674fc13498e0501c46a2918335227060113f8ddc993db98328feb428e32f93fe89020124cda61d377ce6808c206cfde236a34e239adeb521f81dfdbe00fc52b803382e724cff6f6e47c5abce0209c954c8a9ce78d5158cdf24b5f9460d625309279d86c9d3a86f485d5a97706c0c00a040e1bec621af8a153a3bf8a42aa29351d337d266c75f7fb33b2f04a3ca87b4d5dc8bd545f69f47bcb8827d6adfb9a533f75443c33f4c3fb2877eacd0afb1b1f93eb3d94d933c061d82fc240076e66336faf6107c23f86d8e6e187f49cac05b341c396eb590f5c00000000000015e625866710b8003000000000000053fd0ff9c9d030008000000000000141862767dd7600010014,decode 5 1 0x76b896996765407593db5533614e2318e0b2cc8a08c2424c0028aa850a3c4c9f50477e48760446d8003d70000300002000010014,(AH 7 0x2b890659d8066a019600033501d80cea0332000334f6dc1f0607be81ed8000d1676708258208a081a000345f25c30560c0a82fa8000d1336).toArray⟩
theorem h42:check 6 42 d42=true:=by decide+kernel
def d43:Row:=⟨BCurve 58 46 0x1ce4147f83668ae2006954fada1804d26612061af519410467d851f2202887f86a1ade794fac46a2918335227278cc822e199d3bf9afd35c5fc063d5195b96179164c766eac91e38338eb1e4e740c4058e229db4db4771560717ffd6caada9382a7dcb5c30a7c7ea31c3fe965c94c899fcc5aa26c71fbf9050e57d2d9308e8575b0935d47152bc4aff4604cc02a330959ef219b771db334cefbd2a9e9f8cb3d1f726e78d120ee2f154a3bab94067e73a15aa1c81bc579d127d2ba6e47309e455ca87b7e3a661c77db000e0714bd544930f1fadd5c21d7f0a1d7232f66345f5320b078a9c6d7ec1190aca02405f1842d35158d0f5800000000000016d9ff2427b610003000000000000057b7b64dec57b00080000000000001501dc02ce75c80010014,decode 5 1 0x76b8869941653eb593bf5531d34e2218e0a2cc8908c2324c0228aa750a3b4c9f40477d4875f446d7003d60000300002000010014,(AH 7 0x2b8806505c0676019a80658000d13eb7034180cfa0336000344efdc1f4607ce81f08000d164c70835820ca082a000345e69c30960c1682fe8000d131d).toArray⟩
theorem h43:check 6 43 d43=true:=by decide+kernel
def d44:Row:=⟨BCurve 58 46 0x74aff53fe8492b8701a553eb68601366c0080f83ce6468119f6147c880a2a2844c0490493cf11a8a460cd489d28cc1a4bc8fa4e8e771f6e82d6091ea4e2b715c9593059e75f564a17e4507c0f4b2b80a3886822c05b3aa3841c522c0f68c78e09a2526e3c785603ad387dc3c7e632229112f489800735ceca18a685d8c22a620497f1e15bf58e6c4eb24132a9aabc7946c1be707b795ec3375d4a3aaeacbf9f1e8560e3601fcce39e27cec6e0f40dfd257511a69162b4c877cb3311130e5b14a7178f09e6f431d7b1816e3ef066354ebefc783d3c46d6f1419964a39c0631129901409f0f5400000000000017d308caa05ee000300000000000005b871cc4eeed1000800000000000015f08597d717a80010013,decode 5 1 0x76b876991a653cf593a35530534e2118e092cc8824c2228aa650a3a4c9f30477c4875e446d6003d50000300002000010013,(AH 7 0xae1c191a6019e80668000cd3cf7034580d0a033a000344e8dc1f7607da81f48000d1622708458210a083a000345da5c30c60c2683028000d1305).toArray⟩
theorem h44:check 6 44 d44=true:=by decide+kernel
def d45:Row:=⟨BCurve 58 46 0x75cf9881c2f82b8601a553eb68601383e7c8069bc863c8119f6147c880a32526ef9da6ad3b311a8a460cd489daefaeaf3d83b4e1e824a05edbbe94800a316efbe3d2eca140c650622a4f473d2ef3c38e38828d849e498f1867276e22ae6184e08a532056cc6b60ccd49fadcec55321e9cb0387fa2b7566ee5e38d4cd0c21a90ffd5f4a0dc73f37ef16812e2a96b802750640a727df0b4b2cbc8ca39b1c578bfc969672432009208f027cad353a0eb5bf58d77b52e3cac3877bb66141f07f91504f16c0650f601d77261055ab166363df2f45f0ff746d5f671a21ca7140671ed06fb6c8f0f5000000000000018d14279d10b2800300000000000005f6b435ed1905000800000000000016e45f3597bd000010013,decode 5 1 0x76b86698f2653b359387552ec34e2018e082cc8724c2128aa550a394c9f20477b4875d446d5003d40000300002000010013,(AH 7 0xae1818f2701a280678000cd3b37034980d1a0342000344e1dc1fb607ea81f88000d15f7708558214a084e000345cddc31060c3683068000d12ec).toArray⟩
theorem h45:check 6 45 d45=true:=by decide+kernel
def d46:Row:=⟨BCurve 58 46 0x76ef3bc39da72b8501a553eb686013a0a63302d9aa6324119f6147c880a3a361bae4caf139611a8a460cd489e3529bb9be77c4daa8d749d58a1d9715998051434052d3a40b973c22da5986084bc64eb2387e98dd36df73f88c86e1805235c8e07a8119c9d151615eca576f11092321aa84d7c75c577770c1810a90a60c20abffb13f7609cf24ceb1cf1b822a92c43d55a065674803722bcec574a38b4de31e0744d6d643dbe14e9c527c6dfc64dc8bad5a5daa754c8875477ab99172b0196d562be88f01a86d1d733409c767266372cef0864f0da86d4fba1aad4aa8c06b4137723995d0f4c00000000000019d4ac31b9bae8003000000000000063642a1b94417000800000000000017dd68dc1065d00010013,decode 5 1 0x76b85698c9653965936a552d334e1f18e072cc8624c2028aa450a384c9f10477a4875c446d4003d30000300002000010013,(AH 7 0xae1418c9601a280678000cd3967034d80d2a0346000344da9c1ff607fa81fc8000d15cb708698219a085e000345c11c31460c46830a8000d12d3).toArray⟩
theorem h46:check 6 46 d46=true:=by decide+kernel
def d47:Row:=⟨BCurve 58 47 0x1e03b7c15e158ae10034aa7d6d0c0277ac93bfe2f18c500119f6147c880a4219c862bef3537908d4523066a44f5b773195e1b5a69aa627cd30e1f266abf06060bc8b4ae54dacd04fc70cc7884496547ace70f2a435cf7558c8b1e37cd9e1d734e06557899e6b1bd0f85a57900205f990aacfab01afa0de5e99827fe64fb307d5ddeca3f4403ae13561a29bd3e551ad078363a8a376824ca8e19b850a375bfb75808f98b9d1c1ac2ac30f93e0bb0e3ea986696f8e9f414182d01de5798346df6692b80fdcb8e882823adb42033923366381bb33889dfe646d38068d9c65702037bc2f4bce38487a400000000000006b7517c969b88000c0000000000000cee3a1f66e00e001000000000000018dba28b4112180010013,decode 5 1 0x76b84698a0653795934d552b934e1e18e062cc8524c1f28aa350a374c9f0047794875b446d3003d20000300002000010013,(AH 7 0xae1018a0601a680688000cd3797035180d3a034a000344d35c2036080a82008000d159e7087d821da0872000345b41c31860c56830e8000d12b9).toArray⟩
theorem h47:check 6 47 d47=true:=by decide+kernel
def d48:Row:=⟨BCurve 58 47 0x1e4ba091d4c14ae0c034aa7d6d0c027b44611f6aadcc3b0119f6147c880a49b6f7921215935c08d4523066a44f9e8e99e9e956265ea8f2730b9b6a7100c7e30ef0114a8153427227486cdc03165a3f577470eaaf8e680b3da8d73d402f5da9f4e0556e8657ed8ed14149d3605324d9908afe2011882b9ee0f6fe45fafbd307963be31ff9bf3bddb9a01cfa97a5512dcb316d4aef7884314720d459ca365d87d210e50abcf10167a9eefe13debe2ae9e0de1d75a5cd8fbd555b1de17fe3a85e9a4ac3c6505179b3b43ad34ffcaadf466390a3f84cddd1a46d28300de2258be039e222efefac987a200000000000006fac3eeecc934000c0000000000000d7286ffb739aa001000000000000019df0c4329c1d80010013,decode 5 1 0x76b83698766535c5932f552a034e1d18e052cc8424c1e28aa250a364c9ef047784875a446d2003d10000300002000010013,(AH 7 0x2b83061d98069a01a2000334d7180d5a034e000334cbdc2076081a82048000d15707088d8222a0886000345a6dc31c60c6683128000d12a0).toArray⟩
theorem h48:check 6 48 d48=true:=by decide+kernel
def d49:Row:=⟨BCurve 58 47 0x1e9389624b6d0ae08034aa7d6d0c027ecf03df97270c270119f6147c880a515426c16537d33e08d4523066a44fdf70edb1d74da622abbd18e654e67b54ec894fc3cd4a1958d813fec9c4f07c85e34cfb4270e2bae700a12288fc942b80c57bf0e0458583117001d18a339f287c4241906b2c952160b69f6348d394e38213075699d99bff3ebcda2691a901022550ae8edf76ed3b7a85e4fd7a9951ca355f142ea13a7cc00fde1187f8af13dcc147951835d57bbc34c0a5a0ce1ddd864409ddce02cf7b2be7b6e4743acb5df61c9b56639f893ed30e876c6d18598e27e5a7a03c1276a58127d87a0000000000000073f826370f7be000c0000000000000df96be463950200100000000000001ae7a603ca75100010013,decode 5 1 0x76b826984e6533e593115528634e1c18e042cc8324c1d28aa150a354c9ee0477748759446d1003d00000300002000010013,(AH 7 0x2c146a04c600033ad3c184e601aa80698000cd33e7035d80d6a0356000344c45c20c6082a82098000d1541708a18227a089a000345995c32060c7683178000d1286).toArray⟩
theorem h49:check 6 49 d49=true:=by decide+kernel
def d50:Row:=⟨BCurve 58 47 0x1edb7232c218cae04034aa7d6d0c028259a69fc3a04c128119f6147c880a58f155f0b85a132008d4523066a4501e1e2cedab9c25e6ae87bec10e5e85a85e53231b8749ad5e6db5d64b2504f493317d9e4670dac63f9937076921e83ece194d24e0359c7fcaf274f1d317bae87dbef9904b5b0a3139419fe58f026c9f38530716f7d01804bdbdd67c3646ac8625502f528d808f877c8767cbeeea6cca3460a08b318feec32e57a9c4e02213dac464404f8d8981d1d4d3fa56781dd98ca46b5d01badb2e6f7ba014c03ac36bef8e576663ae6b071b301fbc6d08830e6da5c3603e4d2a6c82aa0879e00000000000007858cda232726000c0000000000000e82e8cd6bf21600100000000000001bf56fcd232bc00010013,decode 5 1 0x76b816982565320592f35526b34e1b18e032cc8224c1c28aa050a344c9ed0477648758446d0003cf0000300002000010013,(AH 7 0x2c14da04ae00033a9e41825701ae806a8000cd3207036180d7a035a000344bcdc2106083e820d8000d1511708b9822da08ae0003458b5c32460c86831b8000d126b).toArray⟩
theorem h50:check 6 50 d50=true:=by decide+kernel
def d51:Row:=⟨BCurve 58 47 0x1f235b0338c48ae00034aa7d6d0c0285d71ec094d68bfd8119f6147c880a6048079aec5a530108d4523066a4505f0080b59993a5a8b152649bc7da8ffb1d408913754945640357adcc7d196b3e44d1087670d2d19831ccec3947397a1758eb8ce025b37c8474e7f21bf626a056d951902b897f4111cc6067c98acd2d749306d755c6940a3d3ed2ba8df5ffb0a54fb0163b8a31d37e88b9b27dc7ab4a33622ce7c1e560c64c6e3060a55713d8c780eb86e54187e6adc9bb85081dd59304ccdc3572e6e01b0d3544983abb79e900137663bd495125429a906cf8ac8eb365df2040923e44f4332879c00000000000007cce35303576c000c0000000000000f0efdbad050e600100000000000001d08699f33e5e80010013,decode 5 1 0x76b80697fb65301592d45525134e1a18e022cc8124c1b28a9f50a334c9ec0477548757446cf003ce0000300002000010013,(AH 7 0x14153b054681258000d299505fed806ba01aa000334c0580d9a035e000334b51c2156084e82128000d14e0708cd8232a08c60003457cdc32960c9683208000d1251).toArray⟩
theorem h51:check 6 51 d51=true:=by decide+kernel
def d52:Row:=⟨BCurve 58 47 0x1f6b43d3af704adfc034aa7d6d0c02895496e1660ccbe80119f6147c880a67583bc0013892e208d4523066a4509b78ab6554392568b41d0a7681529a4d2951818f6248d56998f9854ddd2de0871d4771da70cadcf0ca62d1196c87dd5c84bb38e015ca793df75af264cee25007f221900bb7f450ea5760e9f86cb68f8ae30697b3bd100fbc3fcee198b6f7f4a54f30d9e993d4208089dab12733878a3263b944523ad2c96a21a55b484e13d6ca9d96be3cf58dfabfa1e91dd11dd199652e5b692af2902e9c7673fe3ab387e271cf8663cc241cf145f7ec6ce8d60ef925fae042e1b22ed5c33879a000000000000081585ce118890000c0000000000000f9daaac90b17200100000000000001e209379fca3880010013,decode 5 1 0x76b7f697d0652e2592b45523534e1918e012cc8024c1a28a9e50a324c9eb0477448756446ce003cd0000300002000010013,(AH 7 0x50536c14ba048200034a29017d0601b2806b8000cd2e27036d80daa0366000344ad1c21a6086282178000d14ae708e58238a08de0003456e1c32d60caa83248000d1235).toArray⟩
theorem h52:check 6 52 d52=true:=by decide+kernel
def d53:Row:=⟨BCurve 58 47 0x1fb32ca4261c0adf8034aa7d6d0c028cc4e462dc000bd20119f6147c880a6e686fe51616d2c208d4523066a450da25eaa12887a528b6e7b0513acea49e82860cab8348696f2e9b5ccf3542546dbae0a26a70c2e84962f8b5f991d3689d9c8a20e005e175f779ce12ada1edf7916a398febe66960c2e2616c1ba828c4d123065811b38c153bc0caf1568997df254eb19d979d766c828acac7eb290c0a316545a0e29044cc877208b4c90713d4cdba41f594a9940e0a5c8328291dcd9fc58fda9ce2fe3eaa2963a2ee3aab95dbe38b9663dafb6a7f3a37cc6cd8ff8f3ee616a0453b862a275a38798000000000000085f744b4dba92000c000000000000102eefa2ad13ba00100000000000001f3ded5d7d64a00010013,decode 5 1 0x76b7e697a4652c2592945521a34e1818e002cc7f24c1928a9d50a314c9ea0477348755446cd003cc0000300002000010013,(AH 7 0x50522c146a046a000349e9417a4701b6806c8000cd2c27037180dba036a000344a51c21f6087a821d8000d147a708fd823ea08f60003455edc33260cbe83298000d121a).toArray⟩
theorem h53:check 6 53 d53=true:=by decide+kernel
def d54:Row:=⟨BCurve 58 47 0x1ffb15749cc7cadf4034aa7d6d0c02903531e451f34bbb8119f6147c880a7578a40a2af512a208d4523066a451169e1550e32d24e8b9b2562bf446aeef28de2a4ba447f974c43d34509556c6f21d9cd22c70baf3a1fb8e9ad9b71c1bdaa05840dff5f872b0fc4112f66f4996f280018fcc14de709b6d21ee333d23cc9da306186faa081abac1c6e9c76ddce3654e326145a718b8848b89f6c9aab3ca3066d1fd72e5b6cfa45f5a6d278213d2d0d6ed2cec619a208df989ab651dc9a625f159d09b09eb8db3fcd16c3aa3a3d55547a663e9cf39cf1f5a346cc9290f84a63260479fba36e8f82879600000000000008aaaecab7ed72000c00000000000010c2cc9d2577be001000000000000020607749b629300010013,decode 5 1 0x76b7d69777652a259274551fe34e1718dff2cc7e24c1828a9c50a304c9e90477248754446cc003cb0000300002000010013,(AH 7 0x5050ac140a0456000349a641777a01b6000324a8980dda03720003349d1c2246088e82228000d1445709198245a09120003454f1c33660cce832e8000d11fe).toArray⟩
theorem h54:check 6 54 d54=true:=by decide+kernel
def d55:Row:=⟨BCurve 58 47 0x2042fe4513738adf0034aa7d6d0c02939854c66ca38ba40119f6147c880a7c425aaa20b1528108d4523066a451531640009dd2a4a6bc7cfc06adc2b93f1c59da8bf647897a59df0bd1ed6b3814457bc92070b2fefa94247fb9dc61f71390259cdfe60f6f6a7eb4333f36f52e2bf4f98fac43538073f822703f2ba7a843f305d8cda0842039c2c2caeb63c847c54db324f3b0bb04868c183dc2b87e8a2f685e5a033b28d2c0e99a8463bf13d0d3f398644415a0324a78fc98dd1dc5ac8652d9045b1596d93c420d0c3a9bb1cec703b663f89f8ae0f55f206cb9528fca664e204a0e4e551a9d0879400000000000008f7354c502130000c0000000000001159419bf9dd7e00100000000000002188313ea6f1380010013,decode 5 1 0x76b7c697486528159253551e234e1618dfe2cc7d24c1728a9b50a2f4c9e80477148753446cb003ca0000300002000010013,(AH 7 0x1413db04ee81108000d257f05d21806ea01b6000334a05c0df6037a80dd8000d1253708a98229a08a200034503dc24da092e0003353edc33b60ce283338000d11e2).toArray⟩
theorem h55:check 6 55 d55=true:=by decide+kernel
def d56:Row:=⟨BCurve 58 47 0x208ae7158a1f4adec034aa7d6d0c0296ee4d092c10cb8c0119f6147c880a82c593c4f74b925f08d4523066a4518d5956243ecf2462bf47a1e1673ac38e5cf91d504c47157fef80e3534d7fa7d4327dbf4270ab0a532cba648a01a4fa486bc044dfd6266c2401273387f8f0bd3d07b18f8c71c8904c8322f23f73b4571a3305992b970025b943be94c26b5b52254d33e8a1ba5d50888c759cd6526cca2e69eab693909ad5dd10c8fa7dbe93ced710439b9bcda6433fdadbff361dc1b2e6b458381321408cc2333aa03a93bfc838bfc664076c5db4bc46946ca97c10102669e04c874284bc48d8792000000000000094507d01655cc000c00000000000011f24e9f2a44fa001000000000000022b51b3c4fbcb80010013,decode 5 1 0x76b7b697186525f59231551c534e1518dfd2cc7c24c1628a9a50a2e4c9e70477048752446ca003c90000300002000010013,(AH 7 0x14138b04da810b8000d245805c61806fa01ba00033497dc0e16038280df8000d1231708c1822fa08ba000344f59c254a094e0003352ddc34060cf683388000d11c5).toArray⟩
theorem h56:check 6 56 d56=true:=by decide+kernel
def d57:Row:=⟨BCurve 58 47 0x20d2cfe600cb0ade8034aa7d6d0c029a44454beb7e0b738119f6147c880a8948ccdfcde5d23d08d4523066a451c79c6c47dfcba41ec21247bc20b6cddceabbf2b4d046a1858522bad4a5941631e4a27c9870a315abc550496a26e52579338c18dfc63d68dd839a33d0b53c442618e98f6ca03da0250e2374341549d920830559898d7c2b3844ba474c849376c54cb4ac4fc3ff9c8a8ca21404787e0a2d6b771323e60cd8f8d4e5cf757f93ccda2ceed2f381ac536e1f27cfcc1dbdb94715d76bcb2ce8a845d067c23a8bcdc1aa7bd6641635b24a7410906c99a59055e685a04f0a96c5cdfb98790000000000000099426560a8b46000c000000000000128df3a6b6ae32001000000000000023e73542b08bb00010013,decode 5 1 0x76b7a696e76523d5920f551a834e1418dfc2cc7b24c1528a9950a2d4c9e60476f48751446c9003c80000300002000010013,(AH 7 0x504cec131a041e000348c8816e7701c2806f8000cd23d7038980e1a038200034483dc236608d682348000d139c70972c25ba095a0003451c5c34560d0a833e8000d11a8).toArray⟩
theorem h57:check 6 57 d57=true:=by decide+kernel
def d58:Row:=⟨BCurve 58 47 0x211ab8b67776cade4034aa7d6d0c029d9a3d8eaaeb4b5b0119f6147c880a8f858875855e121b08d4523066a451ffaa6ddf671f23d8c4dced96da2ed82ac5a25a9d5946298b1ac4925605a8832d5bea3916709b21045de62e4a4c2278a5e75724dfb6546597060d54196bd7c2e789418f4cceb2affd98e3f61d10682dad430519e783f830b7c5b5e289af7341054c356ffdcda1e98c8c9da34d2d2bca2c6d036fb43b7edc1435f1034b0293cadd499a0a4b39b262d545e019421db9bfa777569f83388f2bc719946e3a83dbbb1c37e66424fb88a21cbd106c89cf109ba6a16051984b184fb54878e00000000000009e490de2cc19e000c000000000000132c30b29f19260010000000000000251e7f51c95e200010013,decode 5 1 0x76b79696b66521b591ec5518a34e1318dfb2cc7a24c1428a9850a2c4c9e50476e48750446c8003c70000300002000010013,(AH 7 0x1412eb04b281028000d21df05ad9c071a01c200033486dc0e46038e80e28000d11ec708f6823b8000cd36070992c263a093200034509dc34b60d1e83438000d118a).toArray⟩
theorem h58:check 6 58 d58=true:=by decide+kernel
def d59:Row:=⟨BCurve 58 47 0x2162a186ee228ade0034aa7d6d0c02a0d5e092b3d28b428119f6147c880a957bc6861db451f708d4523066a45237b86f76ee72a390c7a7937193aae277edac55260f45b190b06669d75dbceec69854bcd070932c5cf67c132a715cf3ce872170dfa66b6250888054621cc3398097698f2cfd27bfd623e477fa650f56139304da457a743636c6b16679ebf825e54bb633abd744358e8c684ab06b834a2b6e8fcc4490f0df2f33ea95fe4813c8e0664541a2edb871754f04ccf71db5c607d8d5d33b443417460ec0a83a7be9b48df3f66433bde0bbb64c186c79f890e166bd2054305f7c4175e878c0000000000000a3647687cf8d4000c00000000000013cd05c2e385d60010000000000000265af9699a34080010013,decode 5 1 0x76b7869685651f7591c85516c34e1218dfa2cc7924c1328a9750a2b4c9e40476d4874f446c7003c60000300002000010013,(AH 7 0x504a6c128a03fa00034823c1685a01c60003247ddc0e66039680e48000d11c870912c243a090a000344c86c26da090a000334f69c35060d3683498000d116c).toArray⟩
theorem h59:check 6 59 d59=true:=by decide+kernel
def d60:Row:=⟨BCurve 58 47 0x21aa8a5764ce4addc034aa7d6d0c02a4118396bcb9cb288119f6147c880a9b720496b60a91d308d4523066a4526d915c825c1d2348ca72394c4d22ecc462d9e232cc45359646084158bdd158fd99e23fae708b37b58f11f80a969496f312eaf0df96825f0a0af354aac7fea7f1a4118f0d2b9ccfaeaee4f9cc133f51a9d3049aa370f03bb5c7acd31d3a236ac54b36f759e0e681908c020a2e35fe0a2a701c28d4e662e249ced2878f4f93c6e382f078faa1be7f4e3a95f23c1db1cc683a5506f34fd76ac2afec6e3a73f7adffb00664427cba9740bda46c6a22112726d8e056d2d3f1a33d7878a0000000000000a8949f4fb30e8000c000000000000147072d783f4420010000000000000279ca38a230d680010013,decode 5 1 0x76b7769651651d3591a45514d34e1118df92cc7824c1228a9650a2a4c9e30476c4874e446c6003c50000300002000010013,(AH 7 0x50496c123a03e6000347cc01651601ca80718000cd1d36039e80e68000cd1a47092ec24aa08e6000344b82c277a08e6000334e25c35660d4e834f8000d114d).toArray⟩
theorem h60:check 6 60 d60=true:=by decide+kernel
def d61:Row:=⟨BCurve 58 47 0x21f27327db7a0add8034aa7d6d0c02a73ffbfb6a5e0b0e8119f6147c880aa121c5222f3ed1ae08d4523066a452a36a498dc9c7a2fecd3cdf27069ef710252b01dfb444b99bdbaa18da15e5c1d2609289ca7083430e27a7dcdabbc962138a81d4df86995bc38d6674f36d8a0e3b0fc18eed5a11df8739a57b921af81fc6d3045b01676c413548a8287399f655054ab7bb07ea88cd928b6ae1c68c9c0a2971a885653bd4e56406a8d7fe1893c4e69f9bb05259c48c600893905e1dadd2c89bd43aab5b79263cfd17c23a6c05a7716c166451381634bc11b86c5a4b916ce6f4a0597fa878750bf87880000000000000add9883a769da000c000000000000151677f080646a001000000000000028e37db363ea400010013,decode 5 1 0x76b766961d651ae5917f5512e34e1018df82cc7724c1128a9550a294c9e20476b4874d446c5003c40000300002000010013,(AH 7 0x50482c11fa03d6000347710161d601ce80728000cd1ae703a680e88000cd17f70952c253a08be000344a6ec282a08be000334ccdc35c60d6283558000d112e).toArray⟩
theorem h61:check 6 61 d61=true:=by decide+kernel
def d62:Row:=⟨BCurve 58 47 0x223a5bf85225cadd4034aa7d6d0c02aa6e746018024af30119f6147c880aa68b08288951118908d4523066a452d70e220d1dc922b2d0078501c017015b349fb410a54439a1714bf05b75fa2944ec65d306707b4e66c03dc1bae0fb552fee49d0df76b0587d0fd9753c0d656c5c19618ecd8886ef5fc4a5fd4c7c39c1bd23041b5f5de846b449a3667d0b6e5a254a387eb5f42b19948aa2d1796f5d0a287334e1f59144e87ddb6d8746ef13c2e9bc46e7aa0dca98aab8fd98c11da9d928fd536e63671949b4f642a03a6413a0e32826645feff3942848506c4a7511b2a710605c36dd10b6e1687860000000000000b33331481a3aa000c00000000000015bf150dd8d64e00100000000000002a2f87e55cca900010013,decode 5 1 0x76b75695e665189591595510e34e0f18df72cc7624c1028a9450a284c9e10476a4874c446c4003c30000300002000010013,(AH 7 0x1411cb046e80f18000d1c4b057998074a01ce000334625c0eba03aa000334565c25db097282268000d125450a2ac287a089a000344b69c36260d7a835b8000d110e).toArray⟩
theorem h62:check 6 62 d62=true:=by decide+kernel
def d63:Row:=⟨BCurve 58 47 0x228244c8c8d18add0034aa7d6d0c02ad8297860f208ad68119f6147c880aab675024a51f516208d4523066a4530ab1fa8c71caa262d2d22adc79930ba59137f8e1bf43b9a706edc7dcce0e8f553d5be384707359bf58d3a69b062a70483e1108df66c75536924c9584a790c25581f18eadb6fbff384fa67efb370436e37303dbbd54644c33ca9e8d398e8e044549b94263fdcd659689a9d946de414a2774c13e85e6b6eb974d2095713d13c0ecd8f21f01c5d0a42e4bd41a001da5df895ed2a21b72b7d52a9b6d0c3a5c219a54e436646ea452b58561706c3a9e91f8672c205ef871ba68bdc87840000000000000b8a19a789de58000c000000000000166a4a2f8d49ee00100000000000002b80c2200dae580010013,decode 5 1 0x76b74695ad6516259131550ee34e0e18df62cc7524c0f28a9350a274c9e0047694874b446c3003c20000300002000010013,(AH 7 0x50462c117a03ba000346b0c15ad601d680748000cd162703b680ec8000cd131b099a821e8000cd20850a06c27da087a0003449f1c36860d9283618000d10ee).toArray⟩
theorem h63:check 6 63 d63=true:=by decide+kernel
def d64:Row:=⟨BCurve 58 47 0x22ca2d993f7d4adcc034aa7d6d0c02b096baac063ecab98119f6147c880ab0439820c0ed913b08d4523066a45339eba9f3927a2212d59cd0b7330b15ef3af3d036e44331ac9c8f9f5e2e22f4035374f31e706b6517f1698b7b2b56b35c79d778df56de51f014bf95cd3c0c102688818e8de5710f10da67009e4b577e90a3039c1b4ae051b2cb999ca92352c9a5493a0612076fb298887ff92edbc08a26764d9b163c28eeb05bc202794d13beeff59d565979d6aeeac11705831da1e5e9c051d5db7e54c89deca4883a542f93c6a046647d553398d35d146c2ac8123e2747e061c466758aa1187820000000000000be24c3cc019e4000c000000000000171817559dbf4a00100000000000002cd72c637695980010013,decode 5 1 0x76b73695736513b59109550cc34e0d18df52cc7424c0e28a9250a264c9df047684874a446c2003c10000300002000010013,(AH 7 0x50452c113a03aa0003464b81573601da80758000cd13b703be80ee8000cd109b09c682158000cd1b9509e2c274a0856000344865c36e60dae83688000d10cc).toArray⟩
theorem h64:check 6 64 d64=true:=by decide+kernel
def d65:Row:=⟨BCurve 58 47 0x23121669b6290adc8034aa7d6d0c02b390889346d70a9b8119f6147c880ab4d96297bd99d11208d4523066a4536b5a6de6ccd2a1c0d8677691ec87203831d33a2c3042adb2323176df8637574f2eb0ca007063707089ff705b50801e6ca19d24df46f54ea997329615cad755cf8d918e6e13e61ee965678235b9339a16f3035c79415c5731cc9494cbc9bdef2548bac9c01111fe9a8725313162eb0a2577d9f7a6919af1c90751ce5f1f13bcf312488db12ddcb8e018c662961d9dec4a21d1099389f0240ee9ce0a3a4c3d8d385c56648c02963e123b406c1af19283e763a0649abb421c8b587800000000000000c3bcad424564e000c00000000000017c87c800a366200100000000000002e32c6af9780500010013,decode 5 1 0x76b726953765112590e0550ab34e0c18df42cc7324c0d28a9150a254c9de0476748749446c1003c00000300002000010013,(AH 7 0x14110b043e80e68000d178b054dd8077a01da00033444980f1a03c2000334381426fb09ae820d8000d1166509bec26ba08360003446c9c37560dc6836f8000d10ab).toArray⟩
theorem h65:check 6 65 d65=true:=by decide+kernel
def d66:Row:=⟨BCurve 58 47 0x2359ff3a2cd4cadc4034aa7d6d0c02b67d2bdb2c2c4a7d0119f6147c880ab928af899b2410e808d4523066a453985f08c1d3d9216cdb321c6ca5ff2a8075d636a5894221b7c7d34e60e64bb938cf0f9ff8705b7bc92295552b75a6b178b53040df370c4b6319a5b65e53f29350f1798e4e425b2ec1f06803c1809888cd53031cd737d85cb14d8f75a181d0b945483b8d6e1ab44a9c8599814e7638ca2479665436e70cf4e14fcff922b313baf62ef3c508e5e2c20e52e238801d99f2aa83503d4b9589e77d92f71a3a444b86aa1866649aac7aa541fbf46c0b1b12c9a77f60677b70201e7c8877e0000000000000c96956db69396000c000000000000187b79aed2af3600100000000000002f939104706e800010013,decode 5 1 0x76b71694fa650e8590b65508834e0b18df32cc7224c0c28a9050a244c9dd0476648748446c0003bf0000300002000010013,(AH 7 0x50432c10ba038e00034576814faa01e20003243a1c0f4a03ce0003342d94266b098e82058000d110f5099ac263a0816000344519c37c60de283768000d1088).toArray⟩
theorem h66:check 6 66 d66=true:=by decide+kernel
def d67:Row:=⟨BCurve 58 47 0x23a1e80aa3808adc0034aa7d6d0c02b95ca483b63e8a5d0119f6147c880abceb01713a6a50bd08d4523066a453c563a39cdadfa114ddfcc2475f7b34c806fcc5bf064195bd5d7525e23e6019c034913d3c70538721bb2b3a0b9aca6c80b4f464df2723481c9c18b6a6d75dc8a9f3818e2e70d03e9a7b288541a1864a0ab302dd352e5462304e8a3f2a4b889ee547bc511c2456969e83dce98615a98a237af2b0c73c7ef7f9353c82c40913b8f94b9efc6099e8ca756f6a78b21d95f90ae4cf7103a12212e9e81fb43a3c59801bd47664a952e0ce629f2c6bfb44930f679b206a66850f9074a877c0000000000000cf2ac0976d1bc000c00000000000019310ee1f729c6001000000000000030f98b620160280010013,decode 5 1 0x76b70694ba650bd5908a5506534e0a18df22cc7124c0b28a8f50a234c9dc0476548747446bf003be0000300002000010013,(AH 7 0x50426c107a037e00034506c14baa01e60003242f5c0f6a03d6000334229425eb096e81fd8000d10b55097ac25ba07f6000344359c38360dfe837d8000d1065).toArray⟩
theorem h67:check 6 67 d67=true:=by decide+kernel
def d68:Row:=⟨BCurve 58 47 0x11f4e86d8d16256de01a553eb686015e1779467286e51dc08cfb0a3e440560336ae9dd474848823428e38c671757c0d4b3760e105d08d4523066a453edfe155fae9420ace0c7682218f33f0ee546e75c934101c2f316fd639e7478e55f35d992704b927a53c11eebbfeb4f84a0b7c0df173a44d61e8bb6ef5518f5daf4018e0e9f454e73062906b61bfcdf2113029d9324d067afcf84f16626e828e5473d14ca2df8e2a081ef69d8413dca227c7f0d5791f0fb10b7976b432113b6fc684a33b851eed2156e5f31b91d91ff6b464ea4bbacb8a653e947dc3a3467798d908664b7f5c8b97424ec6beb6e135527b6e06d5bfa107273b877a0000000000000d500ea76510c0000c00000000000019e93c1977a61200100000000000003264b5c84a55480010014,decode 5 1 0x76b6f69477650916105d590565504034e0918df12cc7024c0a28a8e50a224c9db0476448746446be003bd0000300002000010014,(AH 7 0x14105b041280dc8000d124e051ddc07ba01ea000334245c0f9a03e20003341754255b094a81f68000d105650956c252a07da000344185c38a60e1e83858000d1040).toArray⟩
theorem h68:check 6 68 d68=true:=by decide+kernel
def d69:Row:=⟨BCurve 58 47 0x1218dcd5c86c056dc01a553eb686015f7375abaeab850c408cfb0a3e440561aad795fe376831823428e38c671745a00ed4bc1d502e046851c718ce3013411a4cfa8a9fe6e3920dfcd26f495510b49b9a433fa1c888b8d4e4fe88d6a84efd591870439dd2ec5703cbe5095a84787a5cdf0751418fa0fed737cd241ae453418deecdba5e4b9129881eeffc476763025df11b4c6d2ed07f8c5513eccec546bdd878379b2ea27fd10244f8f50a217e0b69e7e762fe27d6e0b29ffb93b4ff84f56b1005f4d8ee4fc0550a1d8e05cba7cdd873b84da1bb966f903a2c7572ff4c9664c6953266768d306bdb97939ae7d2a0705bcf22c479b87780000000000000daebd478150a2000c0000000000001aa4015554241a001000000000000033d510374b4de00010014,decode 5 1 0x76b6e69431650636102e5cff354fe834e0818df02cc6f24c0928a8d50a214c9da0476348745446bd003bc0000300002000010014,(AH 7 0x14102b040280d98000d1074050c5c07ca01ee00033418ec0fba03de0003340b9424db092e81ef8000d0ff350936c24ba07be000343fa1c39260e3e838d8000d101b).toArray⟩
theorem h69:check 6 69 d69=true:=by decide+kernel
def d70:Row:=⟨BCurve 58 47 0x2479a27c0783cadb4034aa7d6d0c02c1848ee31f1a49f40119f6147c880ac5fe0aff1f2d103301ea3c0403421f8d95eb7def171ffce65cb3d78be7539a8945e25c043a31ce1e5aac66569d330903e79fee703ba92b84ece8ac0a248d803c3c2cdef7683e492371d7803f7f37c550b98dcefc2f6e241bea097c1d84823503021e4f11c872add17a0ff71297d4a5463e9c26413d7ba47d81b2cc3f45ca207f97c6783cd502dd405d5fa04893b302a1a0a267bdfadf00138df12e1dbe0c2c094d0c2bc3e10520ef96d03a24836c7108a664d5311dd569d7fc6bcbc113e0a7ee60736604468686a87760000000000000e0eb7e9cb9162000c0000000000001b615e958ca3de0010000000000000354a9aaf0449f00010013,decode 5 1 0x76b6d693e86503370ffe54e8c34e0718def2cc6e24c0828a8c50a204c9d90476f48744446bc003bb0000300002000010013,(AH 7 0x140feb03f680d68000d0e8c04fa2c07da01ea0003340cec0fea03d2000333ff94246b090e81e88000d0f8d5091ac243a07a2000343da9c39a60e5e83968000d0ff5).toArray⟩
theorem h70:check 6 70 d70=true:=by decide+kernel
def d71:Row:=⟨BCurve 58 47 0x93062d31f8be2b6c00d2a9f5b4300b10541f3e166a27360467d851f2202b2065af200e9d400807a8f0100d087b68b94f929ada7e63b4841d82cd7c2f3ce877ebcb88c9677f3b02a5e4d7c8ac2a4c7e4ca98daf2aa47dfca6ea8acda49590db6301dead0844782d52747c4c22ea7ea545bf5fd44adfc7a67b017b6e0f434a1f812423089247083dc44de0609493b105be4bd9bf7200e44ab9c7f79d1e02128c6acc3fe3cf72d083f4bd9e3a1c9165e2c4b664e3c98b064e05506bbbea9426680a20767a997bb89a887740000000000000e6ffe8e43d300000c0000000000001c2153da21255e001000000000000036c5552f7549780010011,decode 5 1 0x76b6c6939b6500270fcc18c962cc6d24c0728a8b50a1f4c9d80478048743446bb003ba0000300002000010011,(AH 7 0x503eec0faa034e000343258139b701fec07ea01e200034400ac101a03c2000333f31423eb08ee81e18000d0f22508fac23ba0786000343b9dc3a360e82839f8000d0fcd).toArray⟩
theorem h71:check 6 71 d71=true:=by decide+kernel
def d72:Row:=⟨BCurve 58 47 0x2509741cf4db4adac034aa7d6d0c02c68b2b7d3594c9a60119f6147c880ac96154018abb8fcf01ea3c0403421e2012ea3d52ef1f2ef59198dd531eb0c13852f72b1c2a49f0afec07dac536ed15444e244e545402382548213a878505c2a6b640a1e82b07f98e7b90dabd46dd2ffa413af08daf711172606e8ce426e6f9d1e4618eccc4b739bdb0303e4a5e3f63a149f5f5480c664f25e79f92315286bac14146c2825e079998ec25ab5587720000000000000ed29134ea157c000c0000000000001ce3e12311a89a001000000000000038453fb89e4c78001000f,decode 5 1 0x76b6b6934c64fcf70f9724a9228a8a50a1e4c9d70479148742446ba003b9000030000200001000f,(AH 7 0x140f8b03da80d08000d0a9204d32c080a01da000333f3ec104a03b6000333e5d4237b08d281da8000d0eb4508dec234a076a000343985c3ac60ea683a88000d0fa5).toArray⟩
theorem h72:check 6 72 d72=true:=by decide+kernel
def d73:Row:=⟨BCurve 58 47 0x12a8ae76b5c3856d401a553eb68601646ce7a669e304be008cfb0a3e440565315f5af956e7cc80f51e0201a10eafa1d743f9e04f61843cdc293d2b13487ff441ccc291010bf7a2486ede0cec8aad81606d1e8e1f4d2dcaa753e6919f430309dc3a0cad58c63cd66500efeaade907886b9c3d94b1e841a07cc2e41a6cd7187700000000000000f366fddbe58d6000c0000000000001da906705e2d92001000000000000039ca5a4a7f52f0001000c,decode 5 1 0x76b6a692f864f9970f614c880047a348741446b9003b8000030000200001000c,(AH 7 0x140f5b03ce80cd8000d088004be2c082a01d6000333e66c108a03aa000333d854230b08b681d48000d0e42508c2c22da0752000343755c3b6b0eca83a78000d0f7b).toArray⟩
theorem h73:check 6 73 d73=true:=by decide+kernel
def d74:Row:=⟨BCurve 57 47 0x966516f788cb2b6900d2a9f5b4301658da43e8b5a24a8808cfb0a3e440aca90b0dafd3a0f6201ea3c0403423930765f8b13f73ca25da91bfc73350f7ddd249fdc6c661c6714f7a85d60ffed3307ddff90edc0000000000003e6e6a230274380030000000000000f3861e1035a2300080000000000003b54a4e5185ce00010009,decode 5 1 0x76b69692a264f6270f2844661003b70000300002000010009,(AH 7 0x140f1b03c280ca8000d066104a8ac084a01ce000333d8ac10ca039e000333ca14229b089a81cd8000d0dcb508a6c226a0736000343515c3c0b0ef6839b8000d0f4f).toArray⟩
theorem h74:check 6 74 d74=true:=by decide+kernel
def d75:Row:=⟨BCurve 57 47 0x9784ba39637a2b6800d2a9f5b430166940b97f64b4491c08cfb0a3e440ac9eb2a70aa604f2701ea3c0403423794089fe827fe3bb264a5d4da7b351e08515d4793d4433c90953d68792106695dfdc25ed0ed8000000000000400844d7c388900030000000000000f9d8c8c059e5b00080000000000003ce41f88696a480010009,decode 5 1 0x76b686924764f2770eec44433003b60000300002000010009,(AH 7 0xc0ef503bac0eda03220003510cc1247b021a80718000ccf2750442c10fa038e000343bb14222b087e81c78000d0d515088ac21fa071e0003432c5c3cab0f22838e8000d0f22).toArray⟩
theorem h75:check 6 75 d75=true:=by decide+kernel
def d76:Row:=⟨BCurve 54 47 0x13148baf67c5256ce01a553eb68616793dda1b39ae47a408cfb0a3e445645c547e0ca1477580f51e0201a1d7aca168ac9b60eaecba15832894e867d248b4365f83f0000000000001069d3e54f2818000c00000000000200806726bc6e20010000000000003e78ca34727b280010008,decode 5 1 0x76b67691e964eeb70eae001f80000300002000010008,(AH 7 0x503b2c0eba03160003407e011e9b021a80708000cceeb50436c10ca0382000343ab9421bb086681c18000d0cd35086ec219a0706000343061c3d6b0f5283828000d0ef4).toArray⟩
theorem h76:check 6 76 d76=true:=by decide+kernel
def d77:Row:=⟨BCurve 54 47 0x13388017a31b056cc01a553eb6861687fefbc68060462008cfb0a3e4456359577c155f675600f51e0201a1d36a16deb4a2c4e6dce395c8e8b0a89cffa2915a3780b80000000000010d2e296db6eea000c0000000000020d78bd12852ca0010000000000004012a4e9338f800010008,decode 5 1 0x76b666918864eac70e6d0005c0000300002000010008,(AH 7 0x140e9b03a280c38000d0000046214085b0212806f8000d0eac5042ac109a037a0003439b54215b084a81bc8000d0c5150856c212a06f2000342de9c3e2b0f8283778000d0ec3).toArray⟩
theorem h77:check 6 77 d77=true:=by decide+kernel
def d78:Row:=⟨BCurve 54 47 0x135c747fde70e56ca01a553eb6861695841e8138ca448c08cfb0a3e445620fdcf4fefb873500f51e0201a1d54da9099f2014e2ad0d160ea8cc68d2d2fd857e7e80b600000000000113d3d4a95b69a000c0000000000021a9a93440e06e00100000000000041b1afa6aca7500010008,decode 5 1 0x76b656912364e6a70e2a0005b0000300002000010008,(AH 7 0x5039ac0e5a03020003400001123b020e806d8000cce6a5041ec106a036e0003438a9420eb083281b68000d0bcb5083ac20ca06da000342b61c3efb0fba836b8000d0e90).toArray⟩
theorem h78:check 6 78 d78=true:=by decide+kernel
def d79:Row:=⟨BCurve 54 47 0x138068e819c6c56c801a553eb68616a23697463d0442e808cfb0a3e445605ca62639e4a71300f51e0201a1d7313b34899d64de4d36965468e829094c5990a33480b40000000000011a8e4007dff28000c00000000000227e5e9bb56fce0010000000000004355ea6cddc2980010008,decode 5 1 0x76b64690ba64e2670de40005a0000300002000010008,(AH 7 0x140e3b038a80be8000d0000042e94082b0206806c8000d0e2650412c103a03620003437914208b081a81b08000d0b4150822c206a06c20003428c5c3fdb0ff283608000d0e5c).toArray⟩
theorem h79:check 6 79 d79=true:=by decide+kernel
def d80:Row:=⟨BCurve 54 47 0x13a45d50551ca56c601a553eb68616adad111ab2f6413808cfb0a3e4455e62f1d255abc6ef80f51e0201a1d914cd5f741ab4d9cd60169a2903e9406bb6b2c85980b2000000000001215d6b8944894000c000000000002355ac078600ea00100000000000044ff553bc6e1580010008,decode 5 1 0x76b636904e64ddf70d9c000590000300002000010008,(AH 7 0x50386c0e0a02ee000340000104eb0202806a8000ccddf50406c100a03560003436714202b080281ab8000d0ab35080ac200a06ae0003426194405b100283568000d0e25).toArray⟩
theorem h80:check 6 80 d80=true:=by decide+kernel
def d81:Row:=⟨BCurve 54 47 0x13c851b89072856c401a553eb68616b7e78bfe9aa03f7c08cfb0a3e4455bff8136c2bfe6ca80f51e0201a1daf85f8a5e9804d51d8996dfe91fa9783114ebeded80b00000000000012841572d892de000c00000000000242f9177b293c200100000000000046adf0136803900010008,decode 5 1 0x76b6268fdf64d9570d51000580000300002000010008,(AH 7 0x140deb037680b98000d000003f7d407fb01fa80698000d0d95503fac0fda034e00034354541fcb07ea81a68000d0a21507f2c1faa069a00034235d43f9b0fd2834b8000d0deb).toArray⟩
theorem h81:check 6 81 d81=true:=by decide+kernel
def d82:Row:=⟨BCurve 54 47 0x13ec4620cbc8656c201a553eb68616c1b8b1e7a8323db008cfb0a3e4455955931610b206a500f51e0201a1dcdbf1b5491554d04db31725a93b69b09c743c13f080ae0000000000012f3a02f4ade06000c00000000000250c0eec3b28560010000000000004861baf3c129400010008,decode 5 1 0x76b6168f6c64d4a70d04000570000300002000010008,(AH 7 0x2c0dba02de0003300000f6cb01f680688000ccd4a503eec0faa034200034341141f6b07d281a18000d098b507dac1f4a068600034208943edb0fa683418000d0db0).toArray⟩
theorem h82:check 6 82 d82=true:=by decide+kernel
def d83:Row:=⟨BCurve 54 47 0x14103a89071e456c001a553eb68616c9e483e54d643bd008cfb0a3e4455641e8adaff1267d80f51e0201a1debf83e03392a4cb4ddc976b695729e9add4a33a6280ac00000000000136476edeb2a0c000c0000000000025eb24651fbea60010000000000004a1ab5dcd252680010008,decode 5 1 0x76b6068ef464cfb70cb4000560000300002000010008,(AH 7 0x140d9b036280b58000d000003bd1407cb01ee80678000d0cfb503e2c0f7a033a0003432d141f1b07be819c8000d08f1507c6c1efa0672000341da943e2b0f7a83378000d0d73).toArray⟩
theorem h83:check 6 83 d83=true:=by decide+kernel
def d84:Row:=⟨BCurve 54 47 0x14342ef14274256be01a553eb68616d13dabed3e6639e808cfb0a3e44552e7c0c0300e465500f51e0201a1e0a3160b1e0ff4c62e0617b12972ea23653621614380aa0000000000013d699aeb976f0000c0000000000026ccd1e26056b20010000000000004bd8e0ce9b7f080010008,decode 5 1 0x76b5f68e7a64caa70c62000550000300002000010008,(AH 7 0x5035ec0d6a02ca0003400000e7ab01ea80658000cccaa503d6c0f4a032e00034318941ebb07a681978000d0853507aec1e9a065e000341ab143d7b0f4e832d8000d0d33).toArray⟩
theorem h84:check 6 84 d84=true:=by decide+kernel
def d85:Row:=⟨BCurve 54 47 0x145823597dca056bc01a553eb68616d7c429ff7b3837f008cfb0a3e4454f23dc8b0178662b80f51e0201a1e286a836088d44c0de2f97f6e98eaa5dc298b6889380a800000000000144a0871b5c4b2000c0000000000027b11763fcf07a0010000000000004d9c3bc91caf200010008,decode 5 1 0x76b5e68dfc64c5770c0d000540000300002000010008,(AH 7 0x50352c0d3a02c20003400000dfcb01e680648000ccc57503cec0f2a032600034303541e6b079281928000d07b15079ac1e4a064a0003417a943ccb0f2283248000d0cf1).toArray⟩
theorem h85:check 6 85 d85=true:=by decide+kernel
def d86:Row:=⟨BCurve 54 47 0x147c17c1b91fe56ba01a553eb68616dd0ea92129c235ec08cfb0a3e4454af63c0e242f860080f51e0201a1e46e0ed8fb1118bb5e59183ca9aa6a98c5fc62b05280a80000000000014bec336e01352000c000000000002897f4e9f58bfe0010000000000004f64c6cc55e2b00010008,decode 5 1 0x76b5d68d7b64c0170bb5000540000300002000010008,(AH 7 0x140d2b034680ae8000d0000035ed4078b01de80638000d0c01503c2c0efa031a000342ed541e0b077a818d8000d070c50782c1dea063600034149143c1b0ef6831a8000d0cad).toArray⟩
theorem h86:check 6 86 d86=true:=by decide+kernel
def d87:Row:=⟨BCurve 54 47 0x14a00c29f475c56b801a553eb68616e1867e4d241c33d808cfb0a3e44546821e0c27c4a5d480f51e0201a1e651a103e58e68b5be82988269c62ad46f6125d88080a6000000000001534c9fe3862d0000c0000000000029816a744a293e001000000000000513281d84719b80010008,decode 5 1 0x76b5c68cf664ba970b5b000530000300002000010008,(AH 7 0x50342c0cfa02b20003400000cf6b01da80628000ccba9503b6c0eca0312000342d6d41dbb076681898000d06625076ec1d9a062600034116543b7b0ece83118000d0c67).toArray⟩
theorem h87:check 6 87 d87=true:=by decide+kernel
def d88:Row:=⟨BCurve 54 47 0x14c400922fcba56b601a553eb68616e4c25488902e31b808cfb0a3e44541c782850c37c5a700f51e0201a1e835332ed00bb8affeac18c829e1eb10bec700011d80a40000000000015ac1cc7beb32c000c000000000002a6d7802fac83a00100000000000053056cecf054380010008,decode 5 1 0x76b5b68c6e64b4e70aff000520000300002000010008,(AH 7 0x2c0cda02aa0003300000c6eb01d680618000ccb4e503aec0eaa030a000342bfd41d6b075281848000d05b45075ac1d4a0612000340e2543adb0ea683088000d0c1f).toArray⟩
theorem h88:check 6 88 d88=true:=by decide+kernel
def d89:Row:=⟨BCurve 54 47 0x14e7f4fa6b21856b401a553eb68616e6c22bd36df82f8408cfb0a3e4453c7febf3b266e57800f51e0201a1ea18c559ba8908a9fed5990de9fdab4db42df12a2980a2000000000001624bb93730466000c000000000002b5c1d960768f200100000000000054dd880a5192300010008,decode 5 1 0x76b5a68be164af070a9f000510000300002000010008,(AH 7 0x140cbb032a80a88000d000002f854074b01ce80608000d0af0503a2c0e7a0302000342a7d41d1b073e81808000d050350746c1cfa0602000340ad543a3b0e7e83008000d0bd4).toArray⟩
theorem h89:check 6 89 d89=true:=by decide+kernel
def d90:Row:=⟨BCurve 54 47 0x150be962a677656b201a553eb68616e7ef592897922d4408cfb0a3e4453715169fc905054800f51e0201a1ebfc5784a50658a3eeff1953aa196b8b4f95f953a480a000000000000169ea66155567e000c000000000002c4d5b2d700b6600100000000000056bad3306ad3a00010008,decode 5 1 0x76b5968b5164a9070a3e000500000300002000010008,(AH 7 0x140c9b032280a68000d000002d454073b01ca805f8000d0a905039ac0e5a02fa0003428f941ccb072e817c8000d044d50732c1cba05f20003407714399b0e5a82f78000d0b87).toArray⟩
theorem h90:check 6 90 d90=true:=by decide+kernel
def d91:Row:=⟨BCurve 54 47 0x152fddcae1cd456b001a553eb68616e7e0878d32e42af408cfb0a3e445311d4641a15f251680f51e0201a1eddfe9af8f83a89d9f2899996a352bc990ff187d8e809e000000000001719dd3165a974000c000000000002d4130c934af96001000000000000589d4e5f3c18880010008,decode 5 1 0x76b5868abd64a2d709d90004f0000300002000010008,(AH 7 0x140c7b031a80a58000d000002af54072b01c6805e8000d0a2d50392c0e3a02f200034276541c8b071a81788000d039350722c1c6a05e20003403fd4390b0e3282ef8000d0b38).toArray⟩
theorem h91:check 6 91 d91=true:=by decide+kernel
def d92:Row:=⟨BCurve 54 47 0x1553d2331d23256ae01a553eb68616e6ff0bfc1a06289c08cfb0a3e4452b023720ea2844e400f51e0201a1efc37bda7a00f8973f5219df2a50ec0878694ea7e7809c0000000000017966003a3fd48000c000000000002e379e695555820010000000000005a84f996c560e80010008,decode 5 1 0x76b5768a27649c8709730004e0000300002000010008,(AH 7 0x50316c0c4a028e0003400000a27b01c2805d8000cc9c850386c0e0a02ea0003425cd41c3b070681738000d02d65070ec1c1a05ce0003400754387b0e0e82e78000d0ae7).toArray⟩
theorem h92:check 6 92 d92=true:=by decide+kernel
def d93:Row:=⟨BCurve 54 47 0x1577c69b5879056ac01a553eb68616e4e1917a72e0263408cfb0a3e445245a2cf5f4ad64b000f51e0201a1f1aae27d6c84cc909f7b9a24ea6cac4805d49bd2af809c0000000000018142ed81051fa000c000000000002f30a40dd1fd2a0010000000000005c71d4d706acc00010008,decode 5 1 0x76b566898d64960709090004e0000300002000010008,(AH 7 0x5030ec0c2a0286000340000098db01be805c8000cc9605037ec0dea02e200034242541beb06f6816f8000d0214506fac1bda05be000340001437db0dea82df8000d0a94).toArray⟩
theorem h93:check 6 93 d93=true:=by decide+kernel
def d94:Row:=⟨BCurve 54 47 0x2b377607279dcad5408cfb0a3e4451d6ba545e010847800f51e0201a1f38e74a857021c89dfa51a6aaa886c883940fffde6809a00000000000189349aeaaa78a000c00000000000302c41b6aaa68e0010000000000005e63e01ffffc100010007,decode 5 1 0x76b55648f07089d0004d0000300002000010007,(AH 7 0x50306c0c0a027e00034000008f0b01ba805b8000cc8f650376c0dca02da00034227541bab06e2816c8000d014f506eac1b8a05b20003400014374b0dc682d78000d0a3e).toArray⟩
theorem h94:check 6 94 d94=true:=by decide+kernel
def d95:Row:=⟨BCurve 54 47 0x2b7f5ed79e498ad5008cfb0a3e4451636a010ac51a42700f51e0201a1f57206d3417f6c82ffce9ab06aa42cc912ae7b298c8098000000000001913b08772fdf8000c00000000000312a7763df51ae001000000000000605b1b71b14ed80010007,decode 5 1 0x76b546484e7082f0004c0000300002000010007,(AH 7 0x502fec0bea027a000340000084eb01b6805a8000cc8895036ec0daa02d20003420bd41b6b06d281688000d0086506dac1b4a05a2000340001436cb0da282cf8000d09e7).toArray⟩
theorem h95:check 6 95 d95=true:=by decide+kernel
def d96:Row:=⟨BCurve 54 47 0x578e8f5029ea95a980f51e0201a1f75598fe2bfcbc7a9ff81af62abfed0a921d0d55a180960000000000019956362695544000c00000000000322b45156ffe8a001000000000000625786cc1aa5180010006,decode 5 1 0x76b53707a90004b0000300002000010006,(AH 7 0xb02f6809c8000cc00001ea6c06ca016600033206ac0d8a02ca000331ef941b1b06c281648000d0000506c6c1b0a05920003400014363b0d8282c88000d098d).toArray⟩
theorem h96:check 6 96 d96=true:=by decide+kernel
def d97:Row:=⟨BCurve 54 48 0xb03cc1e22e842b5200f51e0201a1f9392b29167a0c6ff810cd9df56dd6a65bc65b4112c04a000000000000686188fe36b5b8003000000000000665d5596b95a440020000000000006459222f3bfed00010006,decode 5 1 0x76b52706ff0004a0000300002000010006,(AH 7 0xb02ee809a8000cc00001bfec06ba0162000331ea2c0d6a02c2000331d2941adb06b281608000d0000506b6c1aca0582000340001435bb0d6282c18000d0931).toArray⟩
theorem h97:check 6 97 d97=true:=by decide+kernel
def d98:Row:=⟨BCurve 54 48 0xb15c652409332b51001198a0ddf50af977fbd3dc886b900f51e0201a1fb2091cc08fde06528258dc0d57bb6c7c17ebb578c404a0000000000006a72b47b8019d80030000000000006869510b4abaec002000000000000665fed9b155c000010007,decode 5 1 0x76b516c6b9706520004a0000300002000010007,(AH 7 0x140bab02e680998000d000001949406ab01a680578000d073450352c0d3a02ba000341b5141a9b069e815d8000d0000506a6c1a7a05760003400014352b0d3e82b98000d08d2).toArray⟩
theorem h98:check 6 98 d98=true:=by decide+kernel
def d99:Row:=⟨BCurve 54 48 0xb27c0865e3e22b50001198a0ddf50adb2606d6c8f06b900f51e0201a1fd0423f6f37b305a283a4de3b58996e97a37a6ee3d40490000000000006c8910018181700030000000000006a7a7c88941f0c002000000000000686be90fa6bca80010007,decode 5 1 0x76b506c6b9705a2000490000300002000010007,(AH 7 0x140b8b02de80978000d0000016894069b01a280568000d06bd5034ac0d1a02b200034196d41a5b068e81598000d000050696c1a3a0566000340001434ab0d1e82b28000d0872).toArray⟩
theorem h99:check 6 99 d99=true:=by decide+kernel
def d100:Row:=⟨BCurve 54 48 0xb39baba7be912b4f001198a0ddf50abc00ea4f4ddc6b900f51e0201a1fee7b621ddf8804ef84f0e069597770b85f11e0525c0480000000000006ea49b903aec800030000000000006c90d80e9586a40020000000000006a7d148cf020c80010007,decode 5 1 0x76b4f6c6b9704ef000480000300002000010007,(AH 7 0x140b6b02d680968000d0000013bd4068b019e80558000d064450342c0cfa02ae00034178141a1b067e81568000d000050686c19fa055a0003400014342b0cfe82ab8000d080f).toArray⟩
theorem h100:check 6 100 d100=true:=by decide+kernel
def d101:Row:=⟨BCurve 55 48 0x2d2ed3ba66500ad380046628377d41538114c7ad698d7001ea3c04034300cb484cc875d0439863ce2975a55396f255904e22e0238000000000001c3155c9eb16c2000c000000000000dd58c73a9de3680040000000000006c937012f188600010007,decode 5 1 0x76b4e6c6b870439000470000300002000010007,(AH 7 0xb02d280948000cc000010e6c067a0152000331722c0cea02a6000331589419db067281528000d000050676c19ca054a000340001433bb0ce282a58000d07aa).toArray⟩
theorem h101:check 6 101 d101=true:=by decide+kernel
def d102:Row:=⟨BCurve 55 48 0x2d76bc8adcfbcad340046628377d414f5edb03b52d8d7001ea3c04034302aeda77b2f32037f8788e4c55b333a84b32d759cea0230000000000001cbad0b1f57342000c000000000000e19a3e6980c0780040000000000006eaefba1aaf3700010007,decode 5 1 0x76b4d6c6b87037f000460000300002000010007,(AH 7 0x140b3b02ca80938000d000000dfec066a014e000331526c0cca029e0003313894199b0662814f8000d000050666c198a053e0003400014333b0cc2829e8000d0743).toArray⟩
theorem h102:check 6 102 d102=true:=by decide+kernel
def d103:Row:=⟨BCurve 55 48 0x2dbea55b53a78ad300046628377d414b196ffe01078d7001ea3c0403430496411aa576f42c188d4e6f35c113b9cd9064259620230000000000001d45979c2dd0a0000c000000000000e5e615a9d3a47800400000000000070cfb7391c61f80010007,decode 5 1 0x76b4c6c6b8702c1000460000300002000010007,(AH 7 0x140b1b02c280918000d000000b06c065a014e000331322c0caa029a00033117d4195b0652814c8000d000050656c194a0532000340001432bb0ca682988000d06da).toArray⟩
theorem h103:check 6 103 d103=true:=by decide+kernel
def d104:Row:=⟨BCurve 55 48 0x2e068e2bca534ad2c0046628377d4146b0d3b690f78d6e01ea3c0403430679d3458ff4441ff8a20e9215cef3cb796e36b17960228000000000001dd1aa88942edc000c000000000000ea3c4cfb968f6800400000000000072f5a2d945d3f80010007,decode 5 1 0x76b4b6c6b7701ff000450000300002000010007,(AH 7 0x2c0afa024200033000001ffb019280528000cc44450326c0c8a0292000340f694192b064281498000d00005064ac190a05260003400014324b0c8682918000d066f).toArray⟩
theorem h104:check 6 104 d104=true:=by decide+kernel
def d105:Row:=⟨BCurve 55 48 0x2e4e76fc40ff0ad280046628377d414225062d64fd8d6e01ea3c040343085d65707a71941398b6ceb4f5dcd3dd4ecc4efd7860220000000000001e5f0977288df6000c000000000000ee9ce45ec981480040000000000007520be822749700010007,decode 5 1 0x76b4a6c6b770139000440000300002000010007,(AH 7 0x502bac0ada023e0003400000139b018e80518000cc3be5031ec0c6a028e000340d45418eb063681468000d00005063ac18da051a000340001431db0c6a828b8000d0601).toArray⟩
theorem h105:check 6 105 d105=true:=by decide+kernel
def d106:Row:=⟨BCurve 55 48 0x2e965fccb7aacad240046628377d413d7607627d198d6e01ea3c0403430a40f79b64eee406f8cb8ed7d5eab3ef4daaad099320218000000000001eedb467eaedee000c000000000000f307dbd36c7a1800400000000000077510a33c0c2600010007,decode 5 1 0x76b496c6b77006f000430000300002000010007,(AH 7 0x2c0aca0236000330000006fb018a80508000cc33550316c0c4a0286000340b1d418bb062681438000d00005062ec189a050e0003400014316b0c4e82858000d0591).toArray⟩
theorem h106:check 6 106 d106=true:=by decide+kernel
def d107:Row:=⟨BCurve 50 37 0xbb792274b95a2b488cc506efacf008388154c235b000000000277f2839fcc6c000c0000000013bf0757f773b80040000000009df3d497842080010005,decode 5 1 0x76b486c6b66c0036c0026c0010005,(AH 7 0x140abb02aa808c8000d000000002c061a0142000330aaac0c3a02820003308e94187b061a813f8000d00005061ec186a04fe000340001430fb0c32827f8000d051f).toArray⟩
theorem h107:check 6 107 d107=true:=by decide+kernel
def d108:Row:=⟨BCurve 50 37 0xbc98c5b694092b478cc506efacf9111b33fbd635b00000000027c76f4f91ff6000c0000000013e32ae2c210080040000000009f14f0edd90300010005,decode 5 1 0x76b476c6b66c0036c0026c0010005,(AH 7 0xb02a6808b8000cc000000014061b0182804f8000d021c5030ac0c1a027a0003406a94184b060a813d8000d000050612c182a04f60003400014308b0c1682798000d04ab).toArray⟩
theorem h108:check 6 108 d108=true:=by decide+kernel
def d109:Row:=⟨BCurve 50 37 0xbdb868f86eb82b468cc506efad0219fde6a2ea35b000000000280fb66527380000c0000000014074e6d8cac58004000000000a0360d442de580010005,decode 5 1 0x76b466c6b66c0036c0026c0010005,(AH 7 0x140a8b029e80898000d0000000014060b017e804e8000d018c50302c0bfa02760003404614180b05fe813a8000d000050602c17fa04ea0003400014301b0bfa82738000d0434).toArray⟩
theorem h109:check 6 109 d109=true:=by decide+kernel
def d110:Row:=⟨BCurve 50 37 0xbed80c3a49672b458cc506efad0b22e09949fe35a8000000002857fd7abc70a000c00000000142b71f85748a8004000000000a157299a82c800010005,decode 5 1 0x76b456c6b56c0036c0026c0010005,(AH 7 0xb029a80888000cc00000002c05fa01360003303e6c0bea026e00033020d417db05f281378000d0000505f6c17ca04de00034000142fab0be2826e8000d03bc).toArray⟩
theorem h110:check 6 110 d110=true:=by decide+kernel
def d111:Row:=⟨BCurve 50 37 0xbff7af7c24162b448cc506efad142bc34bf11235a80000000028a0449051a94000c00000000144f958321e4f8004000000000a27845f0d7aa80010005,decode 5 1 0x76b446c6b56c0036c0026c0010005,(AH 7 0x50296c0a4a021e0003400000000b017a804d8000cc064502f6c0bca026a000340001417ab05e281348000d0000505eac178a04d200034000142f4b0bc682688000d0341).toArray⟩
theorem h111:check 6 111 d111=true:=by decide+kernel
def row (v:ℕ):Row:=match v with
 | 0=>d0
 | 1=>d1
 | 2=>d2
 | 3=>d3
 | 4=>d4
 | 5=>d5
 | 6=>d6
 | 7=>d7
 | 8=>d8
 | 9=>d9
 | 10=>d10
 | 11=>d11
 | 12=>d12
 | 13=>d13
 | 14=>d14
 | 15=>d15
 | 16=>d16
 | 17=>d17
 | 18=>d18
 | 19=>d19
 | 20=>d20
 | 21=>d21
 | 22=>d22
 | 23=>d23
 | 24=>d24
 | 25=>d25
 | 26=>d26
 | 27=>d27
 | 28=>d28
 | 29=>d29
 | 30=>d30
 | 31=>d31
 | 32=>d32
 | 33=>d33
 | 34=>d34
 | 35=>d35
 | 36=>d36
 | 37=>d37
 | 38=>d38
 | 39=>d39
 | 40=>d40
 | 41=>d41
 | 42=>d42
 | 43=>d43
 | 44=>d44
 | 45=>d45
 | 46=>d46
 | 47=>d47
 | 48=>d48
 | 49=>d49
 | 50=>d50
 | 51=>d51
 | 52=>d52
 | 53=>d53
 | 54=>d54
 | 55=>d55
 | 56=>d56
 | 57=>d57
 | 58=>d58
 | 59=>d59
 | 60=>d60
 | 61=>d61
 | 62=>d62
 | 63=>d63
 | 64=>d64
 | 65=>d65
 | 66=>d66
 | 67=>d67
 | 68=>d68
 | 69=>d69
 | 70=>d70
 | 71=>d71
 | 72=>d72
 | 73=>d73
 | 74=>d74
 | 75=>d75
 | 76=>d76
 | 77=>d77
 | 78=>d78
 | 79=>d79
 | 80=>d80
 | 81=>d81
 | 82=>d82
 | 83=>d83
 | 84=>d84
 | 85=>d85
 | 86=>d86
 | 87=>d87
 | 88=>d88
 | 89=>d89
 | 90=>d90
 | 91=>d91
 | 92=>d92
 | 93=>d93
 | 94=>d94
 | 95=>d95
 | 96=>d96
 | 97=>d97
 | 98=>d98
 | 99=>d99
 | 100=>d100
 | 101=>d101
 | 102=>d102
 | 103=>d103
 | 104=>d104
 | 105=>d105
 | 106=>d106
 | 107=>d107
 | 108=>d108
 | 109=>d109
 | 110=>d110
 | 111=>d111
 | _=>default
theorem checked (v:ℕ) (hv:6+v≤117):check 6 v (row v)=true:=by
 have hvl:v≤111:=by omega
 interval_cases v
 · exact h0
 · exact h1
 · exact h2
 · exact h3
 · exact h4
 · exact h5
 · exact h6
 · exact h7
 · exact h8
 · exact h9
 · exact h10
 · exact h11
 · exact h12
 · exact h13
 · exact h14
 · exact h15
 · exact h16
 · exact h17
 · exact h18
 · exact h19
 · exact h20
 · exact h21
 · exact h22
 · exact h23
 · exact h24
 · exact h25
 · exact h26
 · exact h27
 · exact h28
 · exact h29
 · exact h30
 · exact h31
 · exact h32
 · exact h33
 · exact h34
 · exact h35
 · exact h36
 · exact h37
 · exact h38
 · exact h39
 · exact h40
 · exact h41
 · exact h42
 · exact h43
 · exact h44
 · exact h45
 · exact h46
 · exact h47
 · exact h48
 · exact h49
 · exact h50
 · exact h51
 · exact h52
 · exact h53
 · exact h54
 · exact h55
 · exact h56
 · exact h57
 · exact h58
 · exact h59
 · exact h60
 · exact h61
 · exact h62
 · exact h63
 · exact h64
 · exact h65
 · exact h66
 · exact h67
 · exact h68
 · exact h69
 · exact h70
 · exact h71
 · exact h72
 · exact h73
 · exact h74
 · exact h75
 · exact h76
 · exact h77
 · exact h78
 · exact h79
 · exact h80
 · exact h81
 · exact h82
 · exact h83
 · exact h84
 · exact h85
 · exact h86
 · exact h87
 · exact h88
 · exact h89
 · exact h90
 · exact h91
 · exact h92
 · exact h93
 · exact h94
 · exact h95
 · exact h96
 · exact h97
 · exact h98
 · exact h99
 · exact h100
 · exact h101
 · exact h102
 · exact h103
 · exact h104
 · exact h105
 · exact h106
 · exact h107
 · exact h108
 · exact h109
 · exact h110
 · exact h111
end AYA
namespace AYJ
open DZ CL
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
def d0:Row:=⟨BCurve 56 44 0x139d4dbad7fa2aec81a553eb68603a5cf864c2746ddf1119f6147c88230c1da463d9135d891a8a460cd4a19a3e34964c28973992004f8001a002ab017e000a958d8000000000000086404ba0023c003000000000000018700df000750008000000000000055c0310001a40010008,decode 5 1 0x76bb269df16576259739016360000300002000010008,(AH 7 0xaec81df16016280568000cd762702c980b1a02ba000345ce5c19c6066e81968000d1b3d706b181aba069a0003474adc2a260a7e82938000d1636).toArray⟩
theorem h0:check 7 0 d0=true:=by decide+kernel
def d1:Row:=⟨BCurve 56 44 0x13e5368b4ea5eaec41a553eb68603ae06757e57fb5dd7119f6147c88233595fdee02ec5d3d1a8a460cd4a1c383b0aaa9c857259e00558001a0036101df800c358900000000000000b0c0628002a4003000000000000022501348008f0008000000000000061c037c001d40010008,decode 5 1 0x76bb169dd76574f59725016240000300002000010008,(AH 7 0x2bb10775d8058a015e000335d3d80b2a02be000335c95c19e6067681988000d1b22706b581aca06a2000347435c2a460a8682958000d1624).toArray⟩
theorem h1:check 7 1 d1=true:=by decide+kernel
def d2:Row:=⟨BCurve 56 43 0x285a3eb78aa355d806954fada180ed88c3dc748a776f08cfb0a3e4411af872bbc1662ae771a8a460cd4a1ecc92cbf07681711f541bde0b6e0059c4a97a46d6b090000000000000253846ce1db4000c0000000000000ec71c6f8bfe800400000000000005790abc049180010008,decode 5 1 0x76bb069dbc6573b59711016120000300002000010008,(AH 7 0x2bb0076f1c0596016280578000d173b702cd80b2a02c2000345c45c19f6067a81998000d1b07706bd81aea06aa0003473bdc2a660a8e82988000d1612).toArray⟩
theorem h2:check 7 2 d2=true:=by decide+kernel
def d3:Row:=⟨BCurve 56 44 0x1475082c3bfd6aebc1a553eb68603be3fa9654c585da1119f6147c88238886b102569e5c9d1a8a460cd4a2160ea8d36507d6fd932107d06b90039e86b9d2ca958000000000000000c2d96c8097c0003000000000000027844aa31f37000800000000000007948e89861f80010008,decode 5 1 0x76baf69da165727596fd016000000300002000010008,(AH 7 0xaebc1da16016680578000cd727702d180b3a02c2000345bf5c1a160682819b8000d1aeb706c581b0a06ae000347341c2a860a96829a8000d1600).toArray⟩
theorem h3:check 7 3 d3=true:=by decide+kernel
def d4:Row:=⟨BCurve 56 44 0x14bcf0fcb2a92aeb81a553eb68603c65c4358c686dd86119f6147c8823b1ff0a8c80775c4d1a8a460cd4a23f5424e7c2a796e9aba130b07bb004876850b36e957b80000000000000f6f1c800bcb8003000000000000033025ef5277300080000000000000a1212fa87ee00010008,decode 5 1 0x76bae69d8665713596e9015ee0000300002000010008,(AH 7 0xaeb81d866016680588000cd713602d280b18000cd6e97068981a1a0676000346b4181b2a06b60003372c9c2aa60a9e829c8000d15ee).toArray⟩
theorem h4:check 7 4 d4=true:=by decide+kernel
def d5:Row:=⟨BCurve 56 44 0x1504d9cd2954eaeb41a553eb68603ce78dd4c40b55d6a119f6147c8823db776416aa505bfd1a8a460cd4a26899a0fc204756d5c42159908bd00588ca107422b57700000000000001312a2db8e5b80030000000000000400875d530b100080000000000000cf1980f09fd00010008,decode 5 1 0x76bad69d6a656ff596d5015dc0000300002000010008,(AH 7 0x2bad075a9c05a6016680588000d16ff702d580b4a02c6000345b55c1a46068e819e8000d1ab4706d181b3a06be00034724dc2ac60aaa829e8000d15dc).toArray⟩
theorem h5:check 7 5 d5=true:=by decide+kernel
def d6:Row:=⟨BCurve 56 44 0x154cc29da000aaeb01a553eb68603d67b2201045ddd4e119f6147c882404efbda0d4295ba91a8a460cd4a291df1d107de716c1dca182709bf006a2abf914e6f5728000000000000171829da912c000300000000000004e968f433af1000800000000000010331dc70c4c80010008,decode 5 1 0x76bac69d4e656ea596c1015ca0000300002000010008,(AH 7 0x2bac07539805aa0162000335ba980b5a02ca000335b05c1a66069681a08000d1a98706d981b5a06c60003471cdc2ae60ab282a08000d15ca).toArray⟩
theorem h6:check 7 6 d6=true:=by decide+kernel
def d7:Row:=⟨BCurve 56 44 0x1594ab6e16ac6aeac1a553eb68603de97bbf47e8c5d32119f6147c88242d4e2116817a5b591a8a460cd4a2bb249924db86d6acf521ab50ac1007d50e0a95bb556e00000000000001b7fb17d143d000300000000000005eacab3f4633000800000000000013d6a4228edc80010008,decode 5 1 0x76bab69d32656d6596ac015b80000300002000010008,(AH 7 0xaeac1d326016a80588000cd6d6702d980b5a02ce000345ab1c1a76069a81a28000d1a7c706e181b7a06ce000347151c2b060aba82a28000d15b8).toArray⟩
theorem h7:check 7 7 d7=true:=by decide+kernel
def d8:Row:=⟨BCurve 56 45 0xaee4a1f46ac1575406954fada180f9a6802a508d37454233ec28f91048ad8cf54156a6b6091a8a460cd4a2e34f8af32c52169886d0ea185e18048ff8227b4feab4a00000000000008124e70c5e3a000c0000000000000e0959392a4ee001000000000000017dc2b2191ad00010008,decode 5 1 0x76baa69d15656c159698015a50000300002000010008,(AH 7 0xaea81d156016a80598000cd6c1702dd80b6a02ce000345a61c1a9606a281a48000d1a60706e981b9a06d60003470d1c2b360ac282a58000d15a5).toArray⟩
theorem h8:check 7 8 d8=true:=by decide+kernel
def d9:Row:=⟨BCurve 56 45 0x5891f43c100faba9034aa7d6d0c07dd6d353978c6b9f0119f6147c88247f24de1658a45ab48d4523066a5185bd3e60be8eab41c5714ce58d87fac4f910286cd55928b708451579ff1c437d4d6b591c871b1d5715fc9e6e08ceaa7fb2e38ae3a64163970dc1d264608a4f9465546db90f118d37b67a71892b388c449310fe8866280541a9541bca39840000000000000095d30ab26c82000c000000000000106e1d5c2bf7a00100000000000001c43b2c414be0001000d,decode 5 1 0x76ba969cf8656ad596835559214e4318e2b2ccaa08c4400c20000030000200001000d,(AH 7 0xaea41cf87016d805aa0166000345ab580b7a02d2000335a0dc1ab606aa81a58000d1a43706f181bba06de000347051c2b560aca82a78000d1592).toArray⟩
theorem h9:check 7 9 d9=true:=by decide+kernel
def d10:Row:=⟨BCurve 57 45 0x59b1977deabeaba8034aa7d6d0c03f6b8df51800bdcda08cfb0a3e440929e0d063017d5698235148c19a92334bff8d5dabd166e90f7e6008dfc28670b044c8ae558091861f79631c263f3b9a8ae630e4293baf855f0bbc4c29f73824c88e2a94d8346ef8fbabe0ca3c4d788cca99400bd0458f3a403a1f720b1d4c4396e6f5c283c349560c7a36d970c1f988ce56b1d233026a7d3250c34ac799c4793fd57b242e1498f46754a5b9f5112f86e3802ffcd4d16264ca1400000000000002b024c399ef3000300000000000002607c3a1db8140020000000000000210d3b0a180f80010010,decode 5 1 0x76ba869cda656985966e5558014e4218e2a2cca908c4324c1f28ac750a5b00a140000300002000010010,(AH 7 0xaea01cda6016e80598000cd698702e180b7a02d60003459b9c1ad606b281a78000d1a26706f981bda06e6000346fd1c2b760ad282a98000d1580).toArray⟩
theorem h10:check 7 10 d10=true:=by decide+kernel
def d11:Row:=⟨BCurve 57 45 0x5ad13abfc56daba7034aa7d6d0c03febb240643b45cbd08cfb0a3e440933f869406cd19683235148c19a9235ceaeaa42b885659970d323600f4560611867b2a6556d979bbaa16ea4539956d4b0709ce4199e74520e32bedfff33810ab94e299b17634f95bbd419b3b332201cca89a4a5826803bcc9c783efc35bcc429d35983d95236d554c663139a8c1e9eec4dab751352fdb6559ccaecac6a061ea0ce7db478e53b464f7b4a5aab91276876480364e5fa566b84a13000000000000030f1d66a2306000300000000000002b954d2edf53c00200000000000002638c3f39ba180010010,decode 5 1 0x76ba769cbd65683596595556d14e4118e292cca808c4224c1e28ac650a5a00a130000300002000010010,(AH 7 0xae9c1cbd6016e805a8000cd683702e580b8a02d6000345965c1ae606b681a98000d1a097070181bfa06ee000346f4dc2b960ade82ac8000d156d).toArray⟩
theorem h11:check 7 11 d11=true:=by decide+kernel
def d12:Row:=⟨BCurve 57 45 0x5bf0de01a01caba6034aa7d6d0c0406bd68bb075cdca008cfb0a3e44093e10021dd825d66e235148c19a9238515dc727c5396449d227e6b73e483a20c96b3d94555a9db155c97a2480f06d98db88c8e40a01391ebd594173a2ef84ad73ce28a1569230327bfc4f8525c2c6ecca7a093f348a78bf53229f025a02cc41a3843ab8a683915162b42065e0c1da54bb5ebcd0375d19b3a0955acac5a6ff5ad9fa3b6aeb44513e4a48a59acacc26d029ab4a5d4b42a3feca12b7d13bd87e5803d01eb1ceb4c479b00000000000003743613e2759800300000000000003184d75f6366c00200000000000002bc64d809f7400010011,decode 5 1 0x76ba669ca06566e596445555a14e4018e282cca708c4124c1d28ac550a594ca120079b0000300002000010011,(AH 7 0xae981ca070171805ba016a0003459b980b9a02da000335911c1b0606be81ab8000d19eb7070981c1a06f6000346ec9c2bc60ae682ae8000d155a).toArray⟩
theorem h12:check 7 12 d12=true:=by decide+kernel
def d13:Row:=⟨BCurve 57 45 0x5d1081437acbaba5034aa7d6d0c040ea55831147f5c8508cfb0a3e440947e11d7624581658235148c19a923ad40ce40cd1ed62ea337caa0e6dcb13afc34f70989547a3c6f0f185acae447fe70c9ff4e3fa63fdeb6c804407152b43134c0e27a795c110cf4424823e93ff9dfcca6a6dd8e6aced41dc4b70a9c903cc40a9d2dd33b7dbb54a4f64043308c1cabab1e2c24fb98a256806ad5d0ac4ad9ccba70c9b8e44e66f805f10a58b35e352e5862d04368dd971848a11b6e6d10790429f4c88c0d4c42479ac41150488668044177737f020c6f400000000000003df6ecb5abed8003000000000000037d6623367ba4002000000000000031b5d7b1238700010012,decode 5 1 0x76ba569c85656585962e5554714e3f18e272cca608c4024c1c28ac450a584ca114879a006f40000300002000010012,(AH 7 0xae941c8560172805a8000cd658702e980b9a02de0003458b9c1b2606c681ad8000d19ce7071181c3a06fe000346e45c2be60aee82b08000d1547).toArray⟩
theorem h13:check 7 13 d13=true:=by decide+kernel
def d14:Row:=⟨BCurve 57 45 0x5e302485557aaba4034aa7d6d0c0416a79ce5d827dc6908cfb0a3e440951f8b6538fac5643235148c19a923d45135c911159619a94d16d659ccded0e061444939533a9dc8c19912cdb958dbf4344e4e3eac6c2b81ba7469a55e6bc39180e26add4eff16c044cb1dffde84348ca5ad27298cf62446541f8e6166d0c3fb0217faec93bd9401275dcf740c1bb20a866c7cebbb6fe828c0f894ac3b43a3c741f03b19b3a0f2b5e48a57ba0fa7efae2aebdda479badeb8a10bdc73306c3fab92b8bcd20b808799d05164b88e7804b8f03f67535c6f30000000000000450c78d0b0c2000300000000000003e89edaaec4e400200000000000003807628527da80010012,decode 5 1 0x76ba469c6965643596195553314e3e18e262cca508c3f24c1b28ac350a574ca1048799006f30000300002000010012,(AH 7 0xae901c6960172805b8000cd643702ed80baa02de000345865c1b4606ce81af8000d19b07071981c5a0706000346dc1c2c060afa82b38000d1533).toArray⟩
theorem h14:check 7 14 d14=true:=by decide+kernel
def d15:Row:=⟨BCurve 57 45 0x5f4fc7c73029aba3034aa7d6d0c041e8f8c5be54a5c4e08cfb0a3e44095bc9d1abdbde962d235148c19a923fc7c279761e0d603af62630bccc50c63b91b9c0a49520aff227419cb508e397217fe8d0e3db298784cace492d6521f01ed78e25b4141ed208c474de69637ce7d0ca4b370c4af1d746ee0637b73f374c3eb6702229da9bfd32abe9aa877cc1ab869eeacd4e3de3a50330c10b4ac2bad7ad413163d4ee3f303ef770a56c0c11ab103eb077487889574d8a0fc4a79505f7b2d3071ed484ab04798dc91792896880536891587a8b46f200000000000004c84058f35d700030000000000000459f79c5f122c00200000000000003ebaedfcac6e80010012,decode 5 1 0x76ba369c4e6562d596035552014e3d18e252cca408c3e24c1a28ac250a564ca0f48798006f20000300002000010012,(AH 7 0xae8c1c4e70175805ca016e0003458b580bba02e200033580dc1b6606d681b18000d19927072181c7a070e000346d39c2c360b0282b58000d1520).toArray⟩
theorem h15:check 7 15 d15=true:=by decide+kernel
def d16:Row:=⟨BCurve 57 45 0x606f6b090ad8aba2034aa7d6d0c042691d110a8f2dc3208cfb0a3e440965e16a894732d618235148c19a92424a71965b2ac15eeb577af413fb539f38663fddac950db607c269a835362e9c0dc21a84e3cb8c4c5179f54bc042dcdec48a8e24ba534db2a58c9d07dac4bdbc8cca3b9ba5fd144bc976982d1d405c0c3dbcbec4a4ebf421221bbf6cb8b0c19bec956ed2cd401018e9f4bcb7cac1c1751e0e43c3f83df5d2bb52cca55c7728d7259b32308120a27176ca0ecb87f7052b6aecdf41d7009d18797e8d18d989e9805ba41f5e002146f10000000000000545d92f13b2c800300000000000004d1706847637c002000000000000045d07a17b14300010012,decode 5 1 0x76ba269c3265618595ee5550d14e3c18e242cca308c3d24c1928ac150a554ca0e48797006f10000300002000010012,(AH 7 0xae881c3260176805b8000cd618702f180bba02e60003457b9c1b8606de81b38000d19737072981c9a0716000346cb1c2c560b0a82b88000d150d).toArray⟩
theorem h16:check 7 16 d16=true:=by decide+kernel
def d17:Row:=⟨BCurve 57 45 0x618f0e4ae587aba1034aa7d6d0c042e79c086b6155c1508cfb0a3e44096fb285e193651602235148c19a9244bb780edf6a2d5d8bb8cfb76b2ad6780483a6a2c9d4f9bc1d5d91b3bd63769c840a4b28e3bbef111e291bce52ef178827090e23c0927c93424cc52e3421aa5f90ca2c003faf36c0cbfef7d9181fe84c3cc30d671ffd54450e61f723e0e8c18c528bf2d84c423c5a36d80524cac0c8128edb56241b8a5df6a0705ca54ce240033af7b3e9843fe6fa810a0dd26859045f2306b3f4d4948e48796e988a284b27b31188e9f6b472c6f0f511a208a6a806441ae0705f7c6a100000000000005c9920f6c0c28003000000000000054f093e67b8d400200000000000004d4806d6365800010013,decode 5 1 0x76ba169c1565602595d8554f914e3b18e232cca208c3c24c1828ac050a544ca0d48796446f0006a10000300002000010013,(AH 7 0xae841c1560176805c8000cd602702f580bca02e6000345761c1ba606e681b58000d19557073181cba071e000346c25c2c860b1682ba8000d14f9).toArray⟩
theorem h17:check 7 17 d17=true:=by decide+kernel
def d18:Row:=⟨BCurve 57 46 0x18abac63300daae8006954fada18086cc35ff9866fb7f208cfb0a3e4409793d23b4c07555ec11a8a460cd4923963f43b1d4ccae0b06891eb096765427fa7b8237b53958465f1737e7b21773108b01341c74c51d5ead842d0e569d1ec4ca3ce226368d5b9ef8a76a8babd219960650b193658564d53a1c94ee9f5f3f30ed92b813361d68d1eefd219faa4982ecb88276ddcbc46868e9da9ce6cabf6757ffd434421f69bbcdf72810529b5355cbd4150d68947595bc9b12831b291760725b6410a6f9a80fd20f2af1055be2ba7a7e098a79d7a3006ef80a8db3c575c036a09ea9c60762758000000000000194dabe7f1a64000c0000000000000ba5843d8024680040000000000000552194383bad80010013,decode 5 1 0x76ba069bf9655ec595c1554e514e3a18e222cca108c3b24c1728abf50a534ca0c48795446ef004eb0000300002000010013,(AH 7 0x2ba006fe5c05e60176805c8000d15ec602f680ba8000cd5c1706f181bba06de0003464d981cea072a000336b9dc2ca60b1e82bd8000d14e5).toArray⟩
theorem h18:check 7 18 d18=true:=by decide+kernel
def d19:Row:=⟨BCurve 57 46 0x18f39533a6b96ae7c06954fada18087c5e946833a8b7b608cfb0a3e4409830e3f0d0ca795d511a8a460cd4924cec27ff3f482ad5b1ede4f8662570a42a64585c235345909127c3958b7bfb201d578e09c72cb49ab78769d377b30c0b32320e2166886d2a3dea8ab8cf6743ea1e6503325cc4deea9443c815331b87930e99f55582c401919bae318e0d4c982cd1e78fae34ac6944502fc7ed40abe6aa6b83abd76310ca161528d2052936e1b96d96c2dd6ba78fc964e2282dc0523a058d2674a6158208dbe0f28f8821540c27a1dccecd5dc0c886ee86c8e5745b6403b5166a1c93321fd00000000000001b8d8fbb132c0000c0000000000000cb93612a0df3800400000000000005d5d223dc14380010013,decode 5 1 0x76b9f69bdb655d5595ab554d114e3918e212cca008c3a24c1628abe50a524ca0b48794446ee003fa0000300002000010013,(AH 7 0xae7c1bdb6017a805d8000cd5d5702f980bda02ee0003456adc1be606f681b98000d19167074581d0a0732000346b0dc2cd60b2a82c08000d14d1).toArray⟩
theorem h19:check 7 19 d19=true:=by decide+kernel
def d20:Row:=⟨BCurve 57 46 0x64edf8107594ab9e01a553eb68602230b9cd5137b6dde8233ec28f91026337d6995636756fc46a291833524981d16f0d850e2b2acdcce0170b85f0144911ec62a94bd672f1784eb22f59e419182892271c345d7e10da4358272b17935ed03881a6a0126a312a7b1d603cf0e9f193ed2e0cc59e1f5396e92485dfcdcc396afca74898b658601d7502fb5060ab611bdfba32922ffba08f6c0572af5b7d5c2851a990ab77ed588fcc94a2e2385877b0d39134c68b92ee5ca0a7384bf80fd29cbacd892f9e8323c9ba1a5abaf3b4e45ce9b0f75a4a1e09ce12fe03f4a6a83adb5fc0f038eeafffece9eca7a28071bc6d09cc86ed8ce8efac5f6c040332eeb8c7f21f600000000000001de5f3b714c1e000c0000000000000dd927fc31a218004000000000000065fab0e6c71a00010015,decode 5 1 0x76b9e69bbd655bf59595554bd14e3818e202cc9f08c3924c1528abd50a514ca0a487930478248775446ed003ec0000300002000010015,(AH 7 0xae781bbd6017a805d8000cd5bf702fd80bea02f2000345655c1c0606fe81bb8000d18f77074d81d2a073e000346a81c2cf60b3282c28000d14bd).toArray⟩
theorem h20:check 7 20 d20=true:=by decide+kernel
def d21:Row:=⟨BCurve 57 46 0x3306cda92821d5ce80d2a9f5b4301137934f85f64d6e7c119f6147c88132cd3f0710bd42b50235148c19a924e7f91f0f067dd57e69f116263f3f0eca6e9040eb08a54b51cf28c7873861e1c7059171838ddaf448a1cb6fb13761fef27a539c3ed98f3815b55d65a8a96a1545d4c9e6c9533be049eb0f3fd56a14ec861c3711fc4310b33527f6aa6413b73051bd4cc05dc9295d6cacf3c57071578e288520f9faca89aed944ca4c0a507474e59c834dd65bcb255b9ba0504bbc8b0769f90eb10616de85ed31e49dbd3c2025c16dbc8c133a8cb58ee9077b87fcd27a388cda039aff986ec9308f9e4637404545f7870feb61f580000000000002056d7dbf667e000c0000000000000f0559fa326d0800400000000000006efa40334d3100010014,decode 5 1 0x76b9d69b9f655a85957e554a914e3718e1f2cc9e08c3824c1428abc50a504ca090479248774446ec003eb0000300002000010014,(AH 7 0x2b9d06e7dc05f6017a805d8000d15a87030180bfa02f60003455f9c1c26070681bd8000d18d77075981d5a07460003469f1c2d260b3e82c58000d14a9).toArray⟩
theorem h21:check 7 21 d21=true:=by decide+kernel
def d22:Row:=⟨BCurve 57 46 0x33969f4a157955ce00d2a9f5b4301156c9b86350bf6e04119f6147c88133fe92c1765f4ab22235148c19a9250deefc513da015676cfbbc40f8b7258932de90ac7ea4a36a259567b53916c56fa724d1938d9bb9d23b29bcb65acb7190bed79c3cdfce66f6521d8dbf8ab15de508c9d6fba014f1846c52f1f3dba925461bb8a5a4e1d5093e1f1432c3d20b304dca0b90de7909a2d53663be7629576e925c2dcb20ccbd6cd3f3d8d4ca4f77cd9efd2e31e41b86be49371a5043d7706324b6af1c3020d35cd781e45e9948600c3870f4fc6fdc0a4a0ee70ef8415ada7a490eda021644f46eb9929041c677c04a89c0745377e1f5000000000000022e03c29b81e0000c000000000000103dcc0ca340080040000000000000785bd023538880010014,decode 5 1 0x76b9c69b8165591595675549414e3618e1e2cc9d08c3724c1328abb50a4f4ca080479148773446eb003ea0000300002000010014,(AH 7 0x2b9c06e05805fa017a00033564580c0a02f600033559dc1c56071281c08000d18b67076181d7a074e000346961c2d460b4a82c88000d1494).toArray⟩
theorem h22:check 7 22 d22=true:=by decide+kernel
def d23:Row:=⟨BCurve 57 46 0x342670eb02d0d5cd80d2a9f5b4301176002140ab316d84119f6147c881352fe67bdc0152af4235148c19a92534ff63d98196d5507006625bb2333c467173e5ae96a403827c0207e359cb9d0670d02d038d5c7f5bd4880abb7dd1e3a489921c3ae60d95d6eeddb5d353f452837cc9c72decee02bead968aed97a98c461b3a394d80996147156753a0ce1a3049d6ca615f28f9e8376c97a16661574efc333a9c46cef0f5e6b973808a4e7b26585dd915f1d9961092499e503bf255bedf744f874cb8edfadac1e41f75549ff2af742cfecbe087c20ee51674fab8e27a598d1bc2426cd46ea9f490e546b8404ffe89b35724a1f48000000000000258220a059e44000c00000000000011827e33841b180040000000000000821f60b6da2080010014,decode 5 1 0x76b9b69b616557a595505548014e3518e1d2cc9c08c3624c1228aba50a4e4ca070479048772446ea003e90000300002000010014,(AH 7 0xae6c1b6170181805fa017a0003455e9c0c16030280be8000d15507071d81c6a070a00034625981daa075a0003368cdc2d760b5282ca8000d1480).toArray⟩
theorem h23:check 7 23 d23=true:=by decide+kernel
def d24:Row:=⟨BCurve 57 46 0x34b6428bf02855cd00d2a9f5b4301195368a1e05a36d08119f6147c88136613a3641a35aac6235148c19a9255af5411bb8b91539731108766baf53022a503fd4dca35b9ad26ea8115a80688b6291c0238d1d44e56de658c0a075552dd4339c38ec4cc4b78ba5dde40532f35204c9b76039c713f92eda0ac29e1926261abbccf61f5db9500af00cfafd2a3045e38931dfd8da2d934f8f6d9c31572f660a476d6cd1244a11959a4fca4d7e7f11be83f9ff95f91c36d32850340d3b1a9a320ff25bdf2e606e21e3e05160dfd9267764932748051d0ee31df1b416ea7a6a079f441f77386e9a569188c6f8c055a453441af1a1f40000000000000283c853fdbbaa000c00000000000012d3706ed4fe3800400000000000008c44f1ede0f900010014,decode 5 1 0x76b9a69b4265563595395546b14e3418e1c2cc9b08c3524c1128ab950a4d4ca060478f48771446e9003e80000300002000010014,(AH 7 0xae681b4260182805e8000cd5637030980c1a02fe0003454e5c1c96072281c48000d18757077581dca0766000346839c2da60b5e82cd8000d146b).toArray⟩
theorem h24:check 7 24 d24=true:=by decide+kernel
def d25:Row:=⟨BCurve 57 46 0x3546142cdd7fd5cc80d2a9f5b43011b46cf2fb60156c88119f6147c8813789be40036122a98235148c19a92580eb1e5defdb5521761bae91252769bc5d739f02eea2b3b328db483f7b3527fe7c6b4e838cde0a6f0744a6c5c2b5c62c9ebc9c36f28bf398286605f19e6d3feef4c9a79286a02533b01d7172eef670661a3d609ebe221158ffae5ed25f393041f048026088ca72e8df4b23bc61570fcfe1543e9353576954884fc34a4c81d7cb1f2ede0d50afe136d3bc502c28207654efb05d5d93948ca351e3a12d6d1fbf9d7a9bb98212825b8ee1256e6d74f27a7a7e6487ad64246e8ab8922c4739405b7b1d269edee1f380000000000002b0f6a083da12000c0000000000001430a2be95e968004000000000000096cc83c8681200010014,decode 5 1 0x76b9969b226554c595215545614e3318e1b2cc9a08c3424c1028ab850a4c4ca050478e48770446e8003e70000300002000010014,(AH 7 0xae641b2260182805f8000cd54c7030d80c2a0302000345485c1cc6072e81c78000d18537078181dfa076e0003467a1c2dd60b6a82d08000d1456).toArray⟩
theorem h25:check 7 25 d25=true:=by decide+kernel
def d26:Row:=⟨BCurve 57 46 0x35d5e5cdcad755cc00d2a9f5b43011d33a06dde06f6c04119f6147c88138bb11fa69032aa68235148c19a925a6e0fba026fd950a792654abdea380750ade03719aa20bcb7f47e86d7be9db5fbe5b14b38c9ecff8a0a2f4cae49336a0e92d1c34f8cb2278c5262dfc1fa3388b20c997c4d379366df160befe8a3fe94619bef4475ce66761f3a24926e990303dfd06d2e138aab8381bcac3223956f039b8610fb9558a53af918ed8ca4b8530847fd9c21b09ba5f924b5850244305d20fad70c851d620806881e36209795fa6147dd271dc3fff7c8edf2ceb26d2fa7a8af16b8cec33986e7b1a92cfc779c06182e75ae2ec61f300000000000002dfacef97f97c000c000000000000159a1522c6dca80040000000000000a1b616466f6b80010014,decode 5 1 0x76b9869b01655345950a5544114e3218e1a2cc9908c3324c0f28ab750a4b4ca040478d4876f446e7003e60000300002000010014,(AH 7 0xae601b01701858060a017e0003454d180c3a0306000335429c1ce6073681c98000d18327078981e1a077a000346709c2df60b7682d38000d1441).toArray⟩
theorem h26:check 7 26 d26=true:=by decide+kernel
def d27:Row:=⟨BCurve 57 46 0x3665b76eb82ed5cb80d2a9f5b43011f2706fbb3ae16b80119f6147c88139e396042ac0f2a3a235148c19a925ccd6d8e25e1fd4f27c30fac6981b972c328f6ce814a163e3d5b4889b9c9e82af2862d6038c5f95823a0141d0060da68aad389c32ff0a515961ee560388d4dd5754c987f7205247a872a3f3656ff894a6194087effbaabf6ae6cbcbf8b1a0303a09c5a361e89afd81050e4c726156d0a38f6de0df57bd0922b15a114a4a88893de084a628c118974939fa501c5deb2dca6b113338a6d23acfa1e322e5859f8c8b8108bc35d07c810edd3467e031027a9b60b453dbe5906e6b7c937347ba4067bbb1e0e71a21f2800000000000030feb413a19e8000c000000000000170fc79b67d7f80040000000000000ad01a967f70580010014,decode 5 1 0x76b9769ae06551d594f25542c14e3118e192cc9808c3224c0e28ab650a4a4ca030478c4876e446e6003e50000300002000010014,(AH 7 0x2b9706b818061a018200033547580c4a03060003353c9c1d06073e81cc8000d18107079581e4a0786000346671c2e260b7e82d68000d142c).toArray⟩
theorem h27:check 7 27 d27=true:=by decide+kernel
def d28:Row:=⟨BCurve 57 46 0x36f5890fa58655cb00d2a9f5b4301210d42ea2e1236af8119f6147c8813b0c1a0dec7ebaa08235148c19a925f2ccb624954214da7f3ba0e15197ade1d487db9f22a0bbfc2c2128c99d531decba80cf438c205b0bd35f8fd5272515e9f7781c3105498039feae7e07da022df1fcc978296d2b58e2b3e70ea7a01d6ee618c21b989a6f1773d92ae747acaf3036168473e2987b42c39b15bf084156b10d667ab20559ef89ade7b16d0a498be1f7412f8a3676ca885b9fa6501478d0898528b19e1205a9bc4fc1e2e3c191df7302843e988ec3f9688edb3be4998f0a7aabcc3edc7c7a106e5bde9416c7fac06e257cb8ab6821f20000000000000341b1956a3b56000c0000000000001891ba2878db580040000000000000b8af3d2cfee000010014,decode 5 1 0x76b9669abe65504594da5541714e3018e182cc9708c3124c0d28ab550a494ca020478b4876d446e5003e40000300002000010014,(AH 7 0x2b9606af9c0626018680608000d15047031580c4a030a000345369c1d36074a81cf8000d17ed707a181e7a07920003465d5c2e560b8a82d98000d1417).toArray⟩
theorem h28:check 7 28 d28=true:=by decide+kernel
def d29:Row:=⟨BCurve 57 46 0x37855ab092ddd5ca80d2a9f5b430122fa14285617d6a70119f6147c8813c349e17ae3c829d8235148c19a92617a80920bf8fd4c2824646fc0b0fc495f0c74f5e04a00c14828dc8f7be07ad1874b6c3838be120956cbdddda47d984bec19e9c2f0b88af1a9b76a609132b2abca4c9685bba046a1d352a10c51ab17b661843af4139336d7ccabf9b13d00a303223434463485b87ffdde11b36315691773d87832b5c21d5513494ebca488f3ab0a1da6e442ad032c97c5a500c93b5e53fe67208ddf2a7055fa1e2a49d9e1f5979877406e71a76330ed9436152ed127abc340b26cdf1146e4c4094ba483b4074c047e22fd661f18000000000000374ffec285dc6000c0000000000001a1fecc9f9e6c80040000000000000c4bed19586fb00010014,decode 5 1 0x76b9569a9c654ec594c25540114e2f18e172cc9608c3024c0c28ab450a484ca010478a4876c446e4003e30000300002000010014,(AH 7 0xae541a9c6018a80618000cd4ec7031980c5a030e000345309c1d66075681d18000d17ca707ad81eaa079e000346535c2e860b9682dc8000d1401).toArray⟩
theorem h29:check 7 29 d29=true:=by decide+kernel
def d30:Row:=⟨BCurve 57 46 0x38152c51803555ca00d2a9f5b430124e6e5667e1d769e4119f6147c8813d545270cc160a9a8235148c19a9263c835c1ce9dd94a98550ed16c48bdb48874dc85d789f5c2cd8fa6925bebc30325702efe38ba1e61f061c2bdf682af3090bac9c2d11c7ddfb3836ce07344fd355c4c9588e06dd7b57b66cf9bddfb3384617c542e9d7f7c585bb89e75d311a302e300214e3f84bcd35cd70614e595671e1149454515e53ec0c98048e0a4792936a02855251dd299692d0165004ae9b40faa412739c6dca1511b1e26579aa5f3ff18aa9073ed3f6528ed74ade0c4b1a7acc981932d04aa06e3ca2955dc87bc07b8c135d7464e1f100000000000003a9d645748138000c0000000000001bba5f7feafa480040000000000000d13066a18f5680010014,decode 5 1 0x76b9469a79654d4594a9553eb14e2e18e162cc9508c2f24c0b28ab350a474ca00047894876b446e3003e20000300002000010014,(AH 7 0xae501a796018a80618000cd4d47031d80c6a03120003452a5c1d86075e81d48000d17a7707b981eda07aa000346495c2eb60ba282df8000d13eb).toArray⟩
theorem h30:check 7 30 d30=true:=by decide+kernel
def d31:Row:=⟨BCurve 57 46 0x38a4fdf26d8cd5c980d2a9f5b430126cd2154f88196960119f6147c8813e7406c9e9ef92976235148c19a926615eaf19142b5490885b93317e03f1f9981b4664c29eac452f670953df70a73a616717138b62aba89f7a79e4881960c8d5a21c2b18070cdbd4f6f6023d7027ee24c948c053b68c91f7afc991ef2124661746d69276bc1d8eab89cc23c52a302a3cc0e564a82c126569c390ac5156524aeba12577e085cde01202d30a4695ec236330365f8dd6b3b79ada4ffcc9809cb561d2de4d7712ec5361e22655b69f26688ddd9995f072e28ed5525ac5a9227adcf869008386b06e2d04960148bc408288df2a7913a1f080000000000003e034a14ea5ac000c0000000000001d61124a4c15d80040000000000000de03fc5117f280010014,decode 5 1 0x76b9369a58654bb59490553d514e2d18e152cc9408c2e24c0a28ab250a464c9ff047884876a446e2003e10000300002000010014,(AH 7 0xae4c1a586018e80618000cd4bb7032180c7a0316000345241c1db6076a81d78000d1783707c581f0a07b60003463f5c2ee60bae82e28000d13d5).toArray⟩
theorem h31:check 7 31 d31=true:=by decide+kernel
def d32:Row:=⟨BCurve 58 46 0x1c9a67c9ad722ae4806954fada1804a2cd750dcb96da370467d851f22027f2776460f923528846a2918335226863a02153e7914778b66394c377e04549197e4d64c4efe2ec2e9d4c0e809448c24f85da0e2c8dc4c8e36319d34f499bfc326a38523c8c7778e3771dfa2e8c28b678c938f2a08f9dcc5c794020a47f21330b64351d8ac03965e6afd259e0624c09925fed7956058af1d65b553e8f2ac6569855bed3b62b77acba28abb8a459944dcc3db19369e6bc51bee5327fa7232fc380fb4d23c43a0628dd87879cc70b7c337d22237bd8dfdeac1da6b3aefe0e54f2ed54fa8fe7a5486e1d6696a4c8fcc044db55a49ef150f8000000000000010606bfedb2c8800300000000000003e280a523a72f00080000000000000eb3992a420cf00010014,decode 5 1 0x76b9269a37654a259477553bf14e2c18e142cc9308c2d24c0928ab150a454c9fe0478748769446e1003e00000300002000010014,(AH 7 0xae481a376018e80628000cd4a27032580c8a031a0003451ddc1de6077681d98000d175f707d181f3a07c2000346351c2f160bba82e68000d13bf).toArray⟩
theorem h32:check 7 32 d32=true:=by decide+kernel
def d33:Row:=⟨BCurve 58 46 0x1ce2509a241deae4406954fada1804aa6664c7b5275a160467d851f22028166def84b454522446a2918335226ab15551168c6d45e8e70df66f0f60fab9445a8fe254ea63aee2024d7f8365c453b9cf428e2b90daef48dc51dd8d9a7551c5f2384e490ad53a1cf745ef07a3d54d50c92924ed68af069d1a8ee5f6a3c7f30b24fef1da226568224a97ca1ee64c08958fa19981fd93963516b5904f2ac263d33758f8764e8f2cf499ec70a449c9d962485fd3d75160d09cabd27f67fa5aa156e94ece1cd057beab8786a0373c7bcd59288ae884a4d7591da2c2a870ca64f2fdadcde0fca6686e0dc89748493d40488abbdce168f0f7c00000000000011462582b3c668003000000000000041a67038bcca500080000000000000f8d1299aa9ec00010014,decode 5 1 0x76b9169a16654895945e553a914e2b18e132cc9208c2c24c0828ab050a444c9fd0478648768446e0003df0000300002000010014,(AH 7 0x2b9106859c0646018e80628000d14897032980c9a031e000345179c1e16078281dc8000d173a707dd81f6a07ce0003462a9c2f460bca82e98000d13a9).toArray⟩
theorem h33:check 7 33 d33=true:=by decide+kernel
def d34:Row:=⟨BCurve 58 46 0x1d2a396a9ac9aae4006954fada1804b1e4ff42e831d9f50467d851f22028394a8493f2fd51bc46a2918335226ced61dc786401444917b8581aa721b01d416efc6424e4a47195674eef86370f9dc4718c8e2a93f115ae5589e7cb254d92594a384a558932fb56776de0c8b72de36cc919573a41c0411dbbd118ee0007730ae5c8c62984916a5db2c359aa2a4c0798bf55b9adf59c39c96a9315102abe710e18f31d3671a35eb073ef5ca439ff64f8530e1444aea31a562ac27f28d1857f2cd650783f9f406f034785a3a76d7b67352ef1792f2fcfcc1d9ed1a1e38674f30e02e2f3c28a0c6dfe2a97ebc97dc04c52a23e03f0b0f780000000000001231ff10c464500030000000000000453d56481f31d0008000000000000106cac134b34980010014,decode 5 1 0x76b90699f56546f594445539214e2a18e122cc9108c2b24c0728aaf50a434c9fc0478548767446df003de0000300002000010014,(AH 7 0xae4019f56019280638000cd46f7032d80caa0322000345111c1e46078a81df8000d1715707e981f9a07de0003461fdc2f860bd682ec8000d1392).toArray⟩
theorem h34:check 7 34 d34=true:=by decide+kernel
def d35:Row:=⟨BCurve 58 46 0x1d72223b11756ae3c06954fada1804b97deefcd1c259d20467d851f220285d410fb7ae2e515846a2918335226f3b170c3b08dd42b94862b9c63ea2657510bb9124f4df253448cc506089082aa06f73c10e2997073c13cec1f207ea24bdec703846620790bc900795cf71c632a96cc90989871ad17b9e5d06b98a931f430aa6929a78e6bc6c98e855087f82cc069bef09d9d9f1a4dc9356edd7152aba7e48fa8d41f694b441edb6b478a42a34f08e5dbc54b1fe832eeb61e27ee9a8b05d02c352222ca6c03bbf0784a7179e7b011135572dd880c8061d9ae09b564284f31e5439c83950386dee8c988f49be40503308c8068890f740000000000001323f8a90d0640003000000000000048ecbc8061a9700080000000000001152659723ce780010014,decode 5 1 0x76b8f699d2654565942b5537c14e2918e112cc9008c2a24c0628aae50a424c9fb0478448766446de003dd0000300002000010014,(AH 7 0x2b8f06749c0656019280638000d14567033180cba03260003450adc1e76079681e38000d16ef707f981fda07ea000346151c2fb60be282f08000d137c).toArray⟩
theorem h35:check 7 35 d35=true:=by decide+kernel
def d36:Row:=⟨BCurve 58 46 0x1dba0b0b88212ae3806954fada1804c0fc897804ccd9af0467d851f220287f03aeb2704f50f046a291833522717723979ce0714109790d1b71d6631ac0b2404fe9e4d965f6fc3151d08bd9155bbaced74e289a1d627947f9fc43e8fad47f6438426e85ee7dc987bdbb02d0e33dfcc8f9bbd3f3e2b5defe2fc7cc5c4ef30a675c6ec848e86ed3eb4cd6a446cc059f1ebdfa05e9ad7e92dbc5c1d82ab68b83dc2766b6b7c1d6ac623bcca41a6a7c24686a951f41010e5c51427eaa7fdb3ad8b153cbe3e6d726b80783aa87cf7a9aed3bbc068097c0051d96ef94c8fe94f32ea1d25e60f8e86ddeee9932c9fec0542bef7ae93090f70000000000000141c124b8dac3800300000000000004cb4a2e1843130008000000000000123e3f25346c600010014,decode 5 1 0x76b8e699af6543c594105536514e2818e102cc8f08c2924c0528aad50a414c9fa0478348765446dd003dc0000300002000010014,(AH 7 0xae3819af6019680648000cd43c7033580cca032a000345041c1ea607a681e68000d16c8708058200a07fa0003460a5c2fe60bee82f38000d1365).toArray⟩
theorem h36:check 7 36 d36=true:=by decide+kernel
def d37:Row:=⟨BCurve 58 46 0x1e01f3dbfecceae3406954fada1804c860ceb48151598c0467d851f22028a1e043c1aef8508446a29183352273a1877e9deabd3f69a9b77d1d6de3d00025fd36edf4d366b9af9653418ea9cfcfa689d78e279d3388dec12e067f21cfd60599383e7b044c3f0307e5a37bd73fd1d0c8e9ee20ccf3f05f9f4c43b35d17330a28264317ab14710ebbaac415cb0c04a24e721a31e5b61fc7f91ae9dc2ab298bebdc18b86dacc1cec76ad34a40aa007ba7318d58c761cb8a8f8f27e6b570618ae9e5575655f852c3b8782adf8007a34c94220032774b7cb1d92fe8e3bbaa4f33eebacb63984206dcf5099d64a3f40583d5656abe8b0f6c000000000000151a4bf846563800300000000000005095096b86c910008000000000000133038bd7d0e500010014,decode 5 1 0x76b8d6998c65421593f65534d14e2718e0f2cc8e08c2824c0428aac50a404c9f90478248764446dc003db0000300002000010014,(AH 7 0x2b8d06631c0666019680648000d14217033980cda032e000344fd9c1ed607b281e98000d16a2708158204a0806000345ff1c30260bfe82f78000d134d).toArray⟩
theorem h37:check 7 37 d37=true:=by decide+kernel
def d38:Row:=⟨BCurve 58 46 0x1e49dcac7578aae3006954fada1804cfdf692fb45bd9680467d851f22028c3a2e2bc7119501c46a29183352275dd9409ffc2513db9da61dec905a485336bf247f604cda77c62fb54b1917a59fc329dba0e26a049af443a6610b994a3c2982c383a8782aa003c980d88dcd948957cc8da206da6052aa0405c2d3f93f79309e8f017670d407349596ed0d40f0c03a57e263a5dddbec032aeed3aa02aaea5f99f5bb046fdd314adf3b8e8a3fad593507dc715f99dd62dd158d27e2c2e30f6848c571eb110ca4ffb8781b1683179cea5488323cd17af571d8f0d87ae76b4f34f31c8cfc2f1e06dbfb29a79ca7fc05c673d5b4eb0f0f68000000000000161ea5af3704400030000000000000548df01e6971100080000000000001428525ffdb4480010014,decode 5 1 0x76b8c6996865407593db5533614e2618e0e2cc8d08c2724c0328aab50a3f4c9f80478148763446db003da0000300002000010014,(AH 7 0xae3019686019a80658000cd4077033d80cea0332000344f6dc1f0607be81ec8000d167a708258208a0816000345f3dc30560c0a82fa8000d1336).toArray⟩
theorem h38:check 7 38 d38=true:=by decide+kernel
def d39:Row:=⟨BCurve 58 47 0xf48e2be76123571601a553eb6860135d0eb9b0c381650808cfb0a3e44051cacb036e66749f6046a2918335227807f7f100cc9d3c050586203a4e929d2d420fc09ea263ca0fc59815886512acf857c380b389546bfab53673c35e682ed34551a706a940107c17618356b25d6fd27c8c8c5295d3f8b329070afc23881383184ca6e7aed9bdadd60f1263f371a23009515bb4b513ab8ebfa5fa797cca5552b33480f5d50720d6bdf0d986d0a3e5858f73443aab335c16b6eab8813eeb4156f5169e5631f1bea9a391b1e0169b0c4f2d10a9dcad0e3015b083b131c812132c4f35f7426aafd42246da80a4d8ea560203054d24468c4a87b200000000000005ca47dc17ed94000c0000000000000b13eadf458526001000000000000015268c0cb65e480010014,decode 5 1 0x76b8b69942653ec593c05531e14e2518e0d2cc8c08c2624c0228aaa50a3e4c9f70478048762446da003d90000300002000010014,(AH 7 0x2b8b06509c0676019a80658000d13ec7034180cfa0336000344f01c1f4607ca81f08000d165270835820ca0826000345e85c30960c1a82fe8000d131e).toArray⟩
theorem h39:check 7 39 d39=true:=by decide+kernel
def d40:Row:=⟨BCurve 58 47 0xf6cd726b1681571401a553eb6860137a9fcea2b593647408cfb0a3e440520e504163eab69e8846a2918335227a325bd801d6e93a551ddb51101a72f7bab74272443a60ca40727155e4a5c6b75fcaf78d338914cebf81e59ac4a585090b9797a7062a07f6582afa85d4a56d05de9e4c8b54283ac13cfd0e74d5f436382f184aaa0f0017465ddef7f4a520d0b2307957bb1cf56ba39ffd51c812fed2554ac06f628ff9c743d718b52816eca3d5a0553e4991cb69e2913c5aa0b93ecb7721ac8c19969c29c7467a3d71dfd709126f204c2aa8da2295f49363b0b2b7a93eed4f36fb2c647e874ec6d983b4de0658060328245ef9a38e87b0000000000000060e6e4ef01b1a000c0000000000000b9927bfd9de2e0010000000000000162ae5c3a70c500010014,decode 5 1 0x76b8a6991d653d1593a55530614e2418e0c2cc8b08c2524c1e28aa950a3d4c9f60477f48761446d9003d80000300002000010014,(AH 7 0xae28191d6019e80668000cd3d17034580d0a033a000344e95c1f7607da81f38000d162970845820fa0836000345dc9c30c60c2a83028000d1306).toArray⟩
theorem h40:check 7 40 d40=true:=by decide+kernel
def d41:Row:=⟨BCurve 58 47 0x1f21971dd97beae24034aa7d6d0c0272f8f1d339b1ac7b0119f6147c880a49f432660ebd13b508d4523066a44f8b97f7e05c26a712a6c6103cbcc66a4842b22701304bb94e23e952c814cf56b6acc83a4e711aa63089d29838bd912464293aece0b559fb8687d2510a4cdf8ad4f559914ad365154cf0de7e00c7ecb62c330915e1a8535c393b13968c6a6d2605542cdaa442a1e8766d424fadf693ca3c5bb1b094ee8eba0625aa73865113eabacec6401951706545e09187841df9777188f1387ab74ebb6d4936f23b033a7406aae4f37feda7a6848a3c6d886c4e3225a0a034bbf9af3bb5387ae00000000000006541cc45649a2000c0000000000000c2174a58a393a001000000000000017355f84cfbe600010013,decode 5 1 0x76b89698f6653b559389552ee14e2318e0b2cc8a24c2428aa850a3c4c9f50477e48760446d8003d70000300002000010013,(AH 7 0xae2418f6701a280678000cd3b57034980d1a033e000344e25c1fb607ea81f78000d15ff708558214a0846000345d0dc31060c3683068000d12ee).toArray⟩
theorem h41:check 7 41 d41=true:=by decide+kernel
def d42:Row:=⟨BCurve 58 47 0x1f697fee5027aae20034aa7d6d0c02769de9d21cb0ec678119f6147c880a521e5c9fa023539908d4523066a44fceaf603463c726daa9d0b657764275986b9f825a154b555538f639c434e5cd5e39328ebe7112b28923687d08e66e8fa28b4ffce0a572f8420a455159fee16c461561912b05da29257b9f0c759f0f31d2c308d6479ed761b8bc273eaf6352066553adae525c4435789cde2c1ffa58ca3b5d5e0d454400bd6db72f78405893e8be2b71b771057707182f17d55f1df57e51eaf06c32c40e1caebf243a3afb496d7966f4f39024cac6d182146d789d4e83e5c0e03701ed834d39987ac000000000000069b533c4a792c000c0000000000000cacd19056964a00100000000000001845f9503074780010013,decode 5 1 0x76b88698cf653995936d552d534e2218e0a2cc8924c2328aa750a3b4c9f40477d4875f446d7003d60000300002000010013,(AH 7 0xae2018cf601a280678000cd3997034d80d2a0346000344db5c1fe607f681fb8000d15d5708658218a085a000345c49c31460c46830a8000d12d5).toArray⟩
theorem h42:check 7 42 d42=true:=by decide+kernel
def d43:Row:=⟨BCurve 58 47 0x1fb168bec6d36ae1c034aa7d6d0c027a42e1d0ffb02c538119f6147c880a5a4886d93189937d08d4523066a45013fbdd148510a6a2acdb5c722fba80e7d1b06036f14af55b4e9891458cfc378a4b7519b6710abee1bcfe61e90f48e2dc999670e0958bf4fd8cb871a9aab3450f94f9910b384f3cfe069f9addcfb98153d30896ad955b6737bd3acd856bdbff65532e820075e6817acc4520a887c3ca3a5f0a69f59972c0d4dda2d3d82213e6c1881d2ec8bd7da8135ffa9c291df185324cef9fead0cbc5edc1110e3af35866ec2304f3a0582fa8cf5c706d68ce4ed5a5e1203954216bcec6087aa00000000000006e411b6cca9b8000c0000000000000d3b3e803ef55e0010000000000000195cb325c92e980010013,decode 5 1 0x76b87698a76537d59351552bd34e2118e092cc8824c2228aa650a3a4c9f30477c4875e446d6003d50000300002000010013,(AH 7 0xae1c18a7601a680688000cd37d7035180d3a034a000344d45c2026080681ff8000d15aa70875821ca086a000345b81c31860c56830e8000d12bd).toArray⟩
theorem h43:check 7 43 d43=true:=by decide+kernel
def d44:Row:=⟨BCurve 58 47 0x1ff9518f3d7f2ae18034aa7d6d0c027de7d9cfe2af6c3f0119f6147c880a622c338da3cdd36108d4523066a450571345688cb12668afe6028ce9368c3674e4c0b4084a9161643ae8c6ed12a03422baa3f27102cb3a569446c938201e1253dc1ce085a4f1b90f2b71f950551530b1f190eb6ac450d691a0293959eba404e30857138bdf6cb6be4e430e840c58a552af55ae8f88cd7cfb772d47a1520a3960b6c6a5eee4c43b9904864dad93e4c4e4c8a620718448377339cd231ded8c12aeeed3a2dd87b72a4efd6e3aeb67605edf14f3b087d64c7e19546d58ff4f276601603bb29568c05a887a8000000000000072e5833dcdb46000c0000000000000dccbb7543567600100000000000001a798d0599ecc00010013,decode 5 1 0x76b866987e6536159334552a434e2018e082cc8724c2128aa550a394c9f20477b4875d446d5003d40000300002000010013,(AH 7 0x2b86061f98069a01a2000334d8580d5a034e000334cd1c2066081682038000d157e708898221a087e000345ab9c31c60c6683128000d12a4).toArray⟩
theorem h44:check 7 44 d44=true:=by decide+kernel
def d45:Row:=⟨BCurve 58 47 0x20413a5fb42aeae14034aa7d6d0c02817fa72f6a6bac2b8119f6147c880a6a0fe0421612134408d4523066a45097f599307aa8a62eb2f0a8a7a2ae9784553ca3b5194a296779dd40484529075bbf02f54e70fad792f02a2ba960f44143ba2104e075bdee74919e7248efc6dca9cd6990cb9d3964af1c60b7883da5993bb3081779826372363f619f4aabe458e55230295ca92b197f2a7451fd47038a38626323564456c7a1e9548fa0fb13e2c841741d78298ae78468d577091de992f310ee075aea41f06468e95c3ae37659d19b24f3c0b3beb1ddb8bc6d49304f792621a03e1d497a21f7187a6000000000000077a26b37b0dd6000c0000000000000e61486f63b99200100000000000001b9c86efa2aef00010013,decode 5 1 0x76b856985765344593175528a34e1f18e072cc8624c2028aa450a384c9f10477a4875c446d4003d30000300002000010013,(AH 7 0xae141857601aa80698000cd3447035d80d6a0352000344c5dc20a6082682078000d15517089d8226a08920003459e9c32060c7683168000d128a).toArray⟩
theorem h45:check 7 45 d45=true:=by decide+kernel
def d46:Row:=⟨BCurve 58 47 0x208923302ad6aae10034aa7d6d0c02850a49ef96e4ec180119f6147c880a71f38cf68856532608d4523066a450db0d0184824925f4b5fb4ec25c2aa2d172b809566149c56d8f7f97c9a53f6d01204e45e870f2e3eb89c0107989c54c70cc3310e065d6eb301411929889089b7b485990abcfae7887a76145ca7ae7624cc307d7df78e777b54074e239e361724551b0fd0ac2cd6581593c8ec978d84a37640f800699c8cb07ce92efd20a93e0cb9e1f94cfdd9185fa40cd8b231de599d372ed3b12f6fa719c0ed4d63adb8553445734f3d0dbe8d8ee3aac6d39614fcae641e040943d9ff39bb87a400000000000007c77d35a74168000c0000000000000ef8e56ea01eb200100000000000001cc5a0e3e375280010013,decode 5 1 0x76b846983065326592fa5527134e1e18e062cc8524c1f28aa350a374c9f0047794875b446d3003d20000300002000010013,(AH 7 0x2c148a051600033ac6c1830701ae806a8000cd3267036180d7a035a000344be9c20e60836820c8000d1524708b1822ba08a6000345915c32460c86831a8000d1271).toArray⟩
theorem h46:check 7 46 d46=true:=by decide+kernel
def d47:Row:=⟨BCurve 58 47 0x20d10c00a1826ae0c034aa7d6d0c028894ecafc35e2c038119f6147c880a7990bc25db78930808d4523066a4511bef554c7040a5b8b905f4dd15a2ae1dcd56f17ba6495d73a521ef4afd55d124469c5da470eaf0442355f559b2933f998a7670e055efe7eb968492e81c1a51a460c9908c02238c603261d40011b0fe8dd30798456f6b7d34c1880bdc2a8632855131d0b8dc6fb18387cfe3ac36d04a3665bbdcb6ef3ace6d48bfa6e0dc13decefacb0c2791982398fb2210cc1de1a0b3d4ec6ecb03b13ad140bfdc3ad3944cb71344f3e10054c1af9f246d2992501ca66220431771da3548687a200000000000008165bba6175fc000c0000000000000f939272f885d600100000000000001df4dae25c3f680010013,decode 5 1 0x76b836980765308592dc5525734e1d18e052cc8424c1e28aa250a364c9ef047784875a446d2003d10000300002000010013,(AH 7 0x2c14ea04fa00033a9481807601ae806a8000cd3087036580d8a035e000344b71c2136084a82108000d14f5708c58230a08ba00034583dc32860c96831f8000d1257).toArray⟩
theorem h47:check 7 47 d47=true:=by decide+kernel
def d48:Row:=⟨BCurve 58 47 0x2118f4d1182e2ae08034aa7d6d0c028c1f8f6fefd76bef0119f6147c880a80e76dd00f78d2ea08d4523066a4515a9c9488448f257abc109af7cf1eb96965195c412048f179bac446cc5d6c33c531ed749e70e2fc9cbcebda39db5e1abdf4b90ce04608e4a718f7b337a8fbff25d8a1906c3498a038bd22622902026d54d30758ab65ef82b3c29b1c3181500c2550b2a466f611fe85b62e50a58366ca356768396744acd1d257dab4cd7013dcd25776837f499ec06097d30f5e1ddda79436eba28310664c03feaa6e3acba34629cf54f3f121026c21e6206d19c3506e66826045a6e628e6fd287a00000000000000866c241a9ab92000c00000000000010314f7c6ceefe00100000000000001f2a34eb0d0db00010013,decode 5 1 0x76b82697de652ea592bd5523c34e1c18e042cc8324c1d28aa150a354c9ee0477748759446d1003d00000300002000010013,(AH 7 0xb055281378000ce97d05f79806ca01ae000334ba980daa0362000334af5c2186085a82158000d14c5708d98235a08d200034575dc32d60caa83238000d123c).toArray⟩
theorem h48:check 7 48 d48=true:=by decide+kernel
def d49:Row:=⟨BCurve 58 47 0x2160dda18ed9eae04034aa7d6d0c028faa32301c50abda0119f6147c880a88849cff629b12cc08d4523066a4519b7ee8503286a53ebf1b41128896c4b439ff498a9948897fd0669e4db58294e3e24152be70db08f55681bf1a0425ddde0afae0e03621e1629b6ab3872fada3feee01904c670db4114822f0454bdbaff5f30719115c73883343ae1339e7c18c45503378150fb44a87e457d5b559a4ca34691496179a1ed536fbe41997c593dad5b421fad6fda55c5116e078261dd9ae7498ead6431d19a53448a22c3ac3b23f9c8b64f4013df1d8450fa46d09f450c026a2a048429a8c08b9f879e00000000000008b8b0cb7fe22a000c00000000000010d21c8afd5a2a00100000000000002065aefdf5e0000010013,decode 5 1 0x76b81697b4652cc5929f5522234e1b18e032cc8224c1c28aa050a344c9ed0477648758446d0003cf0000300002000010013,(AH 7 0x50566c157a04c600034a26c17b4701b6806c8000cd2cc7037180dba036a000344a7dc21c6086e821a8000d1494708f1823ba08ea000345679c33160cba83288000d1222).toArray⟩
theorem h49:check 7 49 d49=true:=by decide+kernel
def d50:Row:=⟨BCurve 58 47 0x21a8c6720585aae00034aa7d6d0c02931a7fb19243ebc40119f6147c880a8f94d124777952ac08d4523066a451da2c278c06d524fec225e72d4212cffe4c08b97445481d85e608f5cf1598f4805798301470d3154df017a3fa2cea88f9cd3bf0e0263ade1e1dddb3d6b02f403001e1902c9982c7e9d3237e54ef3cc5c71306d97752f78db244c0f0f55dd826054fb44bc32956968a124c72dbbc060a336ac0f2c7ef90d89b34dbd53fdd93d8d910cd722eb5abf76a784a59d51dd5b554faea09fb29cb46621e8bd63abbc1390f4774f411572306191bac6cfa255111e6c2e04aea8f039a7ed879c000000000000090c2757e419c4000c0000000000001175f99ea9c75a001000000000000021a7491b16b6580010013,decode 5 1 0x76b8069788652ac5927f5520734e1a18e022cc8124c1b28a9f50a334c9ec0477548757446cf003ce0000300002000010013,(AH 7 0x5054ec151a04ae000349eb01788601b6806c8000cd2ac7037580dca036e0003449fdc22160882821f8000d1462709098241a090200034558dc33560cca832c8000d1207).toArray⟩
theorem h50:check 7 50 d50=true:=by decide+kernel
def d51:Row:=⟨BCurve 58 47 0x21f0af427c316adfc034aa7d6d0c029697f7d2637a2bad8119f6147c880a96a505498c57928d08d4523066a45216a4523bc17aa4bec5308d47fb8adb479b35abe1f147ad8bfbab4d506daf529a91f1d49870cb21a689ad88ca55ac1c113b4a38e01653dad9a050d4262a80d3b97509900ccbf7dbc25e240c57ec25aec8230699dd497b933145d3b563e3951fe54f351f7142f8e28c400c2818aa8a8a326c6d4f784502dbff02c1e7c5b713d6dc6d78e98669b291acbc10a5bc1dd1bc355ce93db3367b2f8d80750c3ab3d032820384f4216c95f59e0a3c6cea565163a6e3204d9ec38f9c4bc879a000000000000096125e6d65260000c000000000000121ce6b772368e001000000000000022ef03426f90b80010013,decode 5 1 0x76b7f6975b6528d5925f551eb34e1918e012cc8024c1a28a9e50a324c9eb0477448756446ce003cd0000300002000010013,(AH 7 0x50536c14ba0496000349ac0175b601ba806d8000cd28d7037d80dea037600034497dc2276089a82248000d142f709218247a091a000345499c33a60cde83318000d11eb).toArray⟩
theorem h51:check 7 51 d51=true:=by decide+kernel
def d52:Row:=⟨BCurve 58 47 0x22389812f2dd2adf8034aa7d6d0c029a084553d96d6b970119f6147c880a9db5396ea135d26d08d4523066a452531c7ceb7c20247ec83b3362b506e690278620efd0473d92114da4d1cdc5af32914e784c70c32dff23436daa7e6a97245589c0e0066cd79522c3d4759ea25e9a85e18fecfe6cef9ae8e49a4e42966a4f63065a433fff98b0c6e6608578f9c0254eb5f31f5c9b2e8e6d96f56c25324a316e19ac289a72df62659651259993d4dfca2460de1db92b17e23363331dcdc315bee8716b432960b66e5dce3aabdf2bf4bf94f4317e4aa6d3db506cda8751b5670360505f38300e20c879800000000000009b7ac78568bfe000c00000000000012c6e3d556a7c60010000000000000243cdd74006f200010013,decode 5 1 0x76b7e6972e6526d5923f551cf34e1818e002cc7f24c1928a9d50a314c9ea0477348755446cd003cc0000300002000010013,(AH 7 0x50522c146a0482000349698172e701be806e8000cd26d7038180dfa037a0003448fdc22c608ae822a8000d13fa7093d824ea09360003453a1c33f60cf283368000d11cf).toArray⟩
theorem h52:check 7 52 d52=true:=by decide+kernel
def d53:Row:=⟨BCurve 58 47 0x228080e36988eadf4034aa7d6d0c029d6b6835f41dab7f8119f6147c880aa47ef00e96f2124c08d4523066a4528f94a79b36c5a43ccb45d97d6e7ef1d7f0fa1881b046cd9826effc5325dc0a4855ade33270bb3a57bcd9528aa725fa331bc884dff685d450a536d4c50c93e0d395318fcd30e2037373e52837f28ef9b083061aa936839e2fc7f8f25a1e037a254e36c6cd763d7a909aecdad62bfd0a306fc608d8efe4e2c55d591166f813d2e326cfd835d5bfc3abeab2998d1dc9c9f620e7a5234fd5d9dce8461c3aa3ee25677ba4f4418c4119ba8eec6ccab852072723a0532bece4effdd87960000000000000a0fbb0c64c69e000c0000000000001373f0f8571b0200100000000000002590d7afc951900010013,decode 5 1 0x76b7d696ff6524c5921e551b334e1718dff2cc7e24c1828a9c50a304c9e90477248754446cc003cb0000300002000010013,(AH 7 0x14142b0502811a8000d248f05bfe806f8000c924c7038980e1a0382000344879c232608c682308000d13c4709598255a095200034529dc34460d06833c8000d11b3).toArray⟩
theorem h53:check 7 53 d53=true:=by decide+kernel
def d54:Row:=⟨BCurve 58 47 0x116434d9f01a556f801a553eb686015067458c0766f5b3c08cfb0a3e440555811494b6c62915846a2918335229ab8e7062a10111fc0000000000000f6f02ed684846a3acce507f9827fafd1ef79192b3c041659e3c9253d485f263dbdf104d4670b346b0566f376acfde453d8e0680dfe69ed10c27a9f51474555a6503b98fad6357174bfee5b614fc0f5c41a305db0f2d07a3af490b6ae1d2b4da454db79a7b8fdfc792c80dd856c1654a2f717265894556e627ea0a28861893d0e6837b4f8d89c65b68d58e3a231dc5d0d682e6d8db5c809b00ee2df63a9bfd1eda37b4f45196794e5225106cbae95258e743e05604e1ae41e2f87940000000000000a6951a3010240000c00000000000014240e20739042001000000000000026eaf1f5ca38080010014,decode 8 1 0xed6f81a5b3c329158591fc6f23ac1541641a70b018dfe0598fa09305c1454d850a2f0993d0011dc4243a98446cb00079400000c000010000010014,(AH 7 0x1413db04ee81158000d236a05b3d8070a01be0003348adc0e36038a80e18000d11fc708e18237a08da000344e31c25da0972000335191c34960d1a83418000d1196).toArray⟩
theorem h54:check 7 54 d54=true:=by decide+kernel
def d55:Row:=⟨BCurve 58 47 0x118829422b70356f601a553eb68601521241ad671d95a8008cfb0a3e440558c2b12222134904846a2918335229c8affb74717f51da0000000000000fd0e4bf6e3d0fa372d15b25b2e17708653b4c8f77e94061a45234ab55de08bbed2d757e8e70ab5308f0051c4af8937843ac43b4dfd6b7cdc7aa1cf563d5e6cb4e0ff98f8d95cc2b2489a643e55f17915913059b75238ba92e4a1dca1c970b54854d386e29a9821394f4f9edede0764a2e731ec2399ac8e98a0ba99682fa93cee9e026c6e541ccf24ea2c6539b1dc1d7b6e4e60c936929a42280155e3a940c184cf3c4f4619cf3449a9db86cab1a52aaa7642058ea168c03d0287920000000000000ac4703c2b3ee4000c00000000000014d73b4dac07860010000000000000284b2c460322880010014,decode 8 1 0xed6f61a5a80329048591da6fa3721540601a70a818dfd0598f80930581454d050a2e0993ce011dc0243a90446ca00079200000c000010000010014,(AH 7 0x504e2c136a04420003488e016a0601c680708000cd2097039580e4a038e000344769c23fa08f6000334d49c265a0992000335079c34e60d2e83468000d1179).toArray⟩
theorem h55:check 7 55 d55=true:=by decide+kernel
def d56:Row:=⟨BCurve 58 47 0x11ac1daa66c6156f401a553eb6860153b6a87f1932b59c008cfb0a3e44055c044daf8d6068f3046a2918335229e5d1868641fd91b8000000000000103bb243ff74802338d465cbcd9aef13aabc2b0ec0173f65aa67d702d73e1f127c40ddaf0070a35f61899b011b21459345764e3cdfc6d0ca832c8ff5b33148338f1ab98f6dc8413efd14a6d1a91ba79a4a33055bdb1a0faead4b30100a6b082ee54cb941d7c3245f9721b11b9b8baa8a2d74cb1ee9f03aecebc2375b5d9f13cced3cd23e3cf5d3885d525ad74f1dbdde9746e5404b75d0f5419dfc523a8c1b11bfafd4f4719faefc93f8e46c9b4b52fc6784605bdb8b7e35c5687900000000000000b2116d7e37c8a000c000000000000158d78800080ce001000000000000029b186a07411100010014,decode 8 1 0xed6f41a59c0328f30591b8702338153f641a70a018dfc0598f60930541454c850a2d0993cc011dbc243a88446c900079000000c000010000010014,(AH 7 0x504cec131a042e0003483e01670701ca80718000cd1e66039a80e58000cd1b87091682448000cd316709bac26da0986000344f55c35460d42834c8000d115c).toArray⟩
theorem h56:check 7 56 d56=true:=by decide+kernel
def d57:Row:=⟨BCurve 58 47 0x11d01212a21bf56f201a553eb68601555b0f50cb47d58f808cfb0a3e44055eff6cb7d98b88e1846a291833522a01d8875205a7519400000000000010abf39787ccdd22fcd77071e8546b1eef7a2d10a8723e71b07d795a58963567891948a6aa709b6bba2330e5fb49f49642ec89ecdfb6e9c73eaf0316028679932884998f4dfab652d59fa75f6031bf766b53051c411093b42ccc423cab4eacaee54c3a1585dcc6ab994e33615fc3020a2c76777b9a45acf04d0db377160613caf0997db594adda1d94e44bd3e41db9e577a8e4740382768e5e47e2d23a842a0b326be4f4819eac763e369c6c8b7c534e27a4a05ed94084d7c2b878e0000000000000b7f457629bb32000c0000000000001646c5b770fc1a00100000000000002b1e01051d03a00010014,decode 8 1 0xed6f21a58f8328e185919470a2fc153e701a709818dfb0598f40930501454c050a2c0993ca011db8243a80446c800078e00000c000010000010014,(AH 7 0x504bac12ca041e000347eac163e701ce80728000cd1c3703a280e78000cd19470935824ca092e000344b62c277a095a000334e21c35960d5a83518000d113e).toArray⟩
theorem h57:check 7 57 d57=true:=by decide+kernel
def d58:Row:=⟨BCurve 58 47 0x11f4067add71d56f001a553eb6860156f8e0d2cfbb7582c08cfb0a3e440561fa8bc025b6a8cf846a291833522a1cc4fdd7bc7c9170000000000000112671928c6d9ba2beda7b18030de32a3375529514d33d81b6931bb1d9f64bbb13b6b69d7c70937812bcc6cadb72a0813c0ec4d4dfa702c3fa31761651d57aea198c518f2e2d2b66ae2a67ed0aa15f25130304dca70717b9abcd544fff41f649854bbae933f668f79b7a80bf3a867c8a2b7823d84a9b1ef3adee1de9ac2e93c8f3f6292cec61e0b1f558993ab81db5ec580ae3a7c38f1a6f787dd66c3a7c3904a527f4f49199ebb19956d46c7bad539fe7c4e061e3359fe9c81878c0000000000000bdefc16fdfadc000c000000000000170322f3fd796a00100000000000002c909b73fdfa380010014,decode 8 1 0xed6f01a582c328cf8591707122be153d801a709018dfa0598f209304c1454b850a2b0993c8011db4243a78446c700078c00000c000010000010014,(AH 7 0x14129b04a281028000d1e500582dc074a01ce00033467dc0ea603a680e88000d117070956c253a0932000344a5ec281a0932000334ce1c35f60d7283578000d111f).toArray⟩
theorem h58:check 7 58 d58=true:=by decide+kernel
def d59:Row:=⟨BCurve 58 47 0x1217fae318c7b56ee01a553eb686015896b254d42f1575808cfb0a3e440564d26c05e250c8bd846a291833522a37b1745d7351d14b00000000000011b1abf73b8de1a280dd85be1dc75f3576ad9b9c21603c99bca8be095b4e620d1c19275b88708b846b565cafbb9b495430dcfef8df971bc0b5b3e936a11e4c3862f3198f0e5fa07a86b5687aa86a86a79433049d0cfd9bbf2b4e664a0644e789854b3bbce2100b439da699352bd61a8a2a79d034faf090f70e6376b3201913c6f752d4a44415e7457eaf43131b1db1f3386ce2db7b9bbc98903fbc043a7447fe17e404f4a1916caea559986c6bde53f1a7e52064f96acf6bd58878a0000000000000c403aba603b88000c00000000000017c29035a5f8be00100000000000002e0955ed16f4d80010014,decode 8 1 0xed6ee1a5758328bd85914b71a280153c981a708818df90598f00930481454b050a2a0993c6011db0243a70446c600078a00000c000010000010014,(AH 7 0x50496c123a03fa0003473a015d6a01d20003245edc0ec603ae80ea8000d114b70976c25ca090a00034494ec28ca090a000334b91c36560d8a835e8000d1100).toArray⟩
theorem h59:check 7 59 d59=true:=by decide+kernel
def d60:Row:=⟨BCurve 58 47 0x123bef4b541d956ec01a553eb686015a2759377d5fb567c08cfb0a3e440567870d890f59e8aa846a291833522a5183609d1d5291250000000000001245e9e3aa785da240e090643880d740b9230825b1f53bb5c2be6060dcae785da2409b18b8708390c3eff2949bc3ef0f21573858df8734bd71365c36f060ed7e03f7c18eee92158e5f406908398d35fd4553045d72f41fc4aa4f782ac0577de4454abc909029ad909fd27cc333b4540a297b7c91ab4602fa6e6dbdd371c593c4faaf801b9bcdedd830e849645b1dadfa18cee20f33a85d09a58da1283a6c56f78aa014f4b1852f6d623ee06c5c0f5443680560681be0135deb087880000000000000ca30160507d36000c00000000000018850d7c6a7a1600100000000000002f88307067f3800010014,decode 8 1 0xed6ec1a567c328aa859125722240153bb41a708018df80598ee0930441454a850a290993c4011dac243a68446c500078800000c000010000010014,(AH 7 0x14120b047e80f98000d1b710567e80758000c9155703b980eda03b2000344495c266b099682398000d120d50a52c290a08e6000344a2dc36b60da283648000d10e0).toArray⟩
theorem h60:check 7 60 d60=true:=by decide+kernel
def d61:Row:=⟨BCurve 58 47 0x92ff1d9c7b9bab7500d2a9f5b4300addc000d13482aace0467d851f2202b50c3824d669044bc0000000000007dd4dba633907287f0000000000000e35e6dafb25ab0f9b0000000000001f7536e98ce41c9f32e39b0a533a534bfad59831e2b43ad9c8d402b85e068eaca62d119d26707b9d1c8988796bec91b20d7d3f18df774dba2cb8cf373f9d5ebafcfae98ecec48aa237cb2995be096d257d33041dd8eaa3ca295089f22d79ba9f254a3d643e434fdca1fe2b69521c380a287d28ee5b9b74fdce0cf34aa13493c2fe0c2b92f381f46a0c03ac1fde1daa00f930e142ebb4fbc2b86785d83a6465f0fd5c24f4c17533edd006ac6c4c4054952825a06b4a956bc008987860000000000000d075008cebfe6000c000000000000194a9ac84afd720010000000000000310d2afdf0f6300010015,decode 8 1 0x76b750d2ace1944bdca87f2f0f9b729f32153ad81a707818df70598ec0930401454a050a280993c2011da8243a60446c400078600000c000010000010015,(AH 7 0x50472c11ba03d60003467b81567a01da0003244bdc0f0a03be0003343f9c270b09be822f8000d11c250a2ac287a08be0003448b9c37160dba836a8000d10c0).toArray⟩
theorem h61:check 7 61 d61=true:=by decide+kernel
def d62:Row:=⟨BCurve 58 47 0x2507b0379592aadd0034aa7d6d0c02ba76f8bae8fbea970119f6147c880ad90d288f75725107000000000000206b00b43bfe9ba1ace6a5b06df3cb573bc54bc0977d3a05cee9a50fdf66a4fa27de8b20b47073a975231e5e4c15313cf54f76f0df6766b6e83b42578ed39fef4e5d018eaef6ffb610562a2335df2c218e6303de3ee127cfa8d19ba04dab9eff0549be37ec5cf228a429a52787103f4a277ed54b0bf0e7012d411718ae6513c10168d70a4b39fafb10016b543b1da607d992e076a3c198c3c8cd6a143a5c74ea701834f4d1617a2feeb1006c3c7154e6e845e06e858ad8922e387840000000000000d6d26b3db0398000c0000000000001a1338194782d2001000000000000032984595b1fce80010013,decode 8 1 0x1dadd034a970651077321ac153a041a707018df60598ea09303c14549850a270993c0011da4243a58446c300078400000c000010000010013,(AH 7 0x14118b045e80f18000d185c054ba80778000c9107703ca80f18000cd0d6b09ea82268000cd17450a06c27da089a000344731c37860dd283718000d109f).toArray⟩
theorem h62:check 7 62 d62=true:=by decide+kernel
def d63:Row:=⟨BCurve 58 47 0x953e642030f9ab7300d2a9f5b4300af5f7c506135ca9e60467d851f2202b768bcc19c87a437c0000000000008ba842dc475fb28568000000000000dce34e00c3aed0f5400000000000022ea10b711d7ec9e54e9b05688ad47627bf222d1ec6e3935d4ff476760bebb462755076b86706bb5cdbcb4432c3dcdafd8cdae00df577fb3a3bdb557de03b11af75d218e8f2974c9e8e12ab0a10e72f0cf93039ea4d7abd527d2ad3520ed287a25493f0b9a769474a654e9fdd29069ca268081a7bc4659048c0a293d995813bf04c58281a2ee018b3ce186f2dc1da20eb9f4dfaa5bce340cd6bf4ddc3a5483e3e2d444f4e14a0233be3ddc6c2ca25538a8662071ccc059d45be87820000000000000dd4856175484c000c0000000000001adee56f600a36001000000000000034298037ab07a80010015,decode 8 1 0x76b730d29e619437dce856af8f54739e541539341a706818df50598e809303814549050a260993be011da0243a50446c200078200000c000010000010015,(AH 7 0x50452c113a03ba000345af414f3a01e200032437d80f4a03ce0003342b54278b09d2821e8000d1122509e2c274a087a000344599c37e60dee83788000d107d).toArray⟩
theorem h63:check 7 63 d63=true:=by decide+kernel
def d64:Row:=⟨BCurve 58 47 0x259781d882ea2adc8034aa7d6d0c02c06a94896a2c6a5b0119f6147c880ae1f23ff84fa8d0b5000000000000186b289235eb002106ecbafca366bf6dbb5c1d65c56b3869db14e9bee21ed190a49086b5747063c226564a280c66670ab7f7e44cdf4798b05f4028582d2d923df85bb98e6f5be9ddc16c2b3dff97419340b3035f0ace2fdaa753beb0a73e599a0548bfdf489036c0a87ff9ec349cb74a25822e046c9bcb07ea6829b9620c93bd08222df8faa2081a92a3ff030e1d9e159a56dede13dacd9de23d31323a4c92dd559054f4f12ecbf93ead3c6c1cd3558a688660752035ef8691a87800000000000000e3d6c119d8e02000c0000000000001bada2ca94939e001000000000000035c0dae3dc16700010013,decode 8 1 0x1dadc834a5b0650b57421061538681a706018df40598e609303414548850a250993bc011d9c243a48446c100078000000c000010000010013,(AH 7 0x14110b043e80ea8000d1510052d9c07aa01e60003342d5c0f7a03da00033420d426fb09ae82158000d10cc509bec26ba08560003443f1c38560e0a83808000d105b).toArray⟩
theorem h64:check 7 64 d64=true:=by decide+kernel
def d65:Row:=⟨BCurve 58 47 0x977daaa3e657ab7100d2a9f5b4300b0d5cdf453e06a8ec0467d851f2202b97ec3d943844422c000000000000719b203959fdbc82c3ce7eefe00cec8efd4d92ce19d4db57b1ad1ac29b787c51435851b9318e4f8e5ef199f6ebcb5179980838e3031f70c4b3e02654d012e09f2fd5454840b2f6a9d90daaaad4f2ad379f8a2483da611cf13d0dbaa865d5826093bb0b7ed970525a0ea91148d38c171de61c7ab8de11cbe76576eb4714143a44a1d6c84c64f5010fd7806fff246c0d0455dc28a6a0787feb99a8cf7877e0000000000000ea7dac453d4ba000c0000000000001c7f702ae51f0a0010000000000000375e559a4529400010011,decode 8 1 0x76b710d28ec19422dd282c018db50598e409303014548050a240993ba011de4243a40446c000077e00000c000010000010011,(AH 7 0x1410cb042e80e68000d1356051d9c07ba01ea00033422dc0f9a03e20003341614266b098e820d8000d10725099ac263a0836000344231c38d60e2683878000d1038).toArray⟩
theorem h65:check 7 65 d65=true:=by decide+kernel
def d66:Row:=⟨BCurve 58 47 0x989d4de5c106ab7000d2a9f5b4300b18a61769f943a8680467d851f2202ba5db8f1e38d5417c00000000000099ae1077be9522815bdad78975f1bcb7907869501cd0d867caa9d6450e78cb6ec46a02b4b98e2fc0d4057281ec5896b576510a1302dfd6bb37e5a555e15bcd0fac70a547c186a4c37b59acd57b113c5c334a238586bdcd46af13dd265fba4f8893b90edb84e7aa0e1536b8d0047f671e36235b1add4583f3fb97f1dcf6823a3cb0d03b0874f510ed24c95233906bfd35562de8c6e07bebe1583b155877c0000000000000f13d179981c74000c0000000000001d544d9051ac7a00100000000000003901f05ae640180010011,decode 8 1 0x76b700d286819417dd4815818d860598e209302c14547850a230993b8011e34243a38446bf00077c00000c000010000010011,(AH 7 0x50426c107a038e0003446341434a01f200032417dc0fca03ee0003340ad425eb096e82058000d10155097ac25ba0816000344065c39460e46838f8000d1014).toArray⟩
theorem h66:check 7 66 d66=true:=by decide+kernel
def d67:Row:=⟨BCurve 58 47 0x4cde7893cddad5b7806954fada180591c2fd49ed3453ef0233ec28f91015d9587549de6f206203d4780806844170921b7c93e03ff40000000000008ad7e3bf9b53c47dbbe730230bd69ce0208b3b7e50d0d577e3a691c781791a8615730baec98e0ff349194b0cece5cf4adc6d0b3302a03cb1bbeb24d6f28b6c8fd0b08547425a52dd1da5aeffec47e20cea4a2287331a7d9c211a10cb15317b9f93b71238305f01c61bc3893991eb8d1e862a3b7cdc793c009000f5fed87c3a34bfc9adc484f520c6b3d3e54a846bed66567fa8e7207f64172b3d634877a0000000000000f8150316a6530000c0000000000001e2c3afada3bee00100000000000003aabab25bf5af80010012,decode 8 1 0x3b5b78693ef0ca0621c3ff5d67db818d570598e009302814547050a220993b6011e84243a30446be00077a00000c000010000010012,(AH 7 0x14105b041280df8000d0fb704fbe807d8000c9031a03fa000323ff54255b094a81fd8000d0fb350956c252a07f6000343e85c39c60e6683978000d0fef).toArray⟩
theorem h67:check 7 67 d67=true:=by decide+kernel
def d68:Row:=⟨BCurve 58 47 0x9adc94697664ab6e00d2a9f5b4300b2e3133404e81a74e0467d851f2202bbd5259e047d7400807a8f0100d088035fe10dc40e27e6bf388bca1bb7d08ad8609588408dd37fca34d49f499699736736d07998df025be2d2397ad72fb39ca5b93930260a2a83ff0a3d803a1bf1f9a0c2546c32e00f6bff1b12a28969e49c48a2188df772df193205596863b06a593b51594dbd6597a224f82857bc1fc1ed6311bdedbacfc0d22b1f7acc77c3a2ccec3208094f5309c84a02944006bdd9756d169076082e88d12afb9487780000000000000ff056ebcaaeee000c0000000000001f07386a7ecd6600100000000000003c5b85fad079e00010011,decode 5 1 0x76b6e693a76500270fcd18dd32cc6f24c0928a8d50a214c9da047b548745446bd003bc0000300002000010011,(AH 7 0x5040ac100a037200034374c13a7701fec07ea01f600034400ac101a03ee000333f35424db092e81f68000d0f4e50936c24ba07da000343c91c3a460e8683a08000d0fc9).toArray⟩
theorem h68:check 7 68 d68=true:=by decide+kernel
def d69:Row:=⟨BCurve 58 47 0x26ff0dead444eadb4034aa7d6d0c02ce29f05bd563a9ad8119f6147c880af16ff740f6700fd201ea3c0403421f5c7cb7a2cbea9f370583340fc22ae001a82401df4c2f8a1089ec3f62359149ec4bf0b0be5464401af10623db3542ffd7112c1ca208a8bd3de470526ab88b2d6f09a93b318f1874db13228daa4b3c2113f1f2637fc40dae0b419b3aaf6e6a88e3a24ddbc933ca4f5406e972e1e20006bcdc857232927a08679430e9217587760000000000001060e5a8b8f9ae000c0000000000001fe545df3f60e200100000000000003e1180da199cd0001000f,decode 5 1 0x76b6d6935b64fd270f9b24be228a8c50a204c9d9047c948744446bc003bb000030000200001000f,(AH 7 0x140feb03f680d98000d0be204d6ec080a01ee000333f4ac104a03de000333e6d4246b090e81ef8000d0ee45091ac243a07be000343a8dc3ad60eaa83a98000d0fa2).toArray⟩
theorem h69:check 7 69 d69=true:=by decide+kernel
def d70:Row:=⟨BCurve 58 47 0x9d1bdaed2bc2ab6c00d2a9f5b4300b428050261577a6180467d851f2202bcbf973fe72993e7c07a8f0100d087a912e27fded947b3c4d55d2a0489b57e027c5a67e289e28c38308e9c772cef938ee1926113b11c4e32c508e62f64efc464cacc1f723edca2da146c2642ebf3ac892c3a1cecb605f8b4f5503ceb7dc3de846bbdf95774e947e08a16391ee47d7877400000000000010d2fc68354570000c00000000000020c663591bf66200100000000000003fcd9bc39ac3c8001000d,decode 5 1 0x76b6c6930c64f9f70f67509e24c9d8047dc48743446bb003ba000030000200001000d,(AH 7 0x140fbb03ea80d68000d09e204c32c082a01ea000333e7dc108b041e80f48000d0f67508fac23ba07a20003439dd423eb08ee81e88000d0e1e70eda83b38000ccf79).toArray⟩
theorem h70:check 7 70 d70=true:=by decide+kernel
def d71:Row:=⟨BCurve 58 47 0x278edf8bc19c6adac034aa7d6d0c02d2fbe2787ed2295d0119f6147c880af3ffc7b404988f6a01ea3c0403421de5e1194f20491e631faade3c609a35ee63b763f5ea1f5645bd04d9482432d074edfe69563a14fbaf78b4c4f56007818f1a7f906bae2a57c6a968208dbf6f43a6eba877200000000000011469b2a3f9234000c00000000000021aa90d8148de60010000000000000418fd6b753eec8001000b,decode 5 1 0x76b6b692ba64f6a70f31047d548742446ba003b9000030000200001000b,(AH 7 0x503e2c0f6a034e000341f5412bab020e80788000ccf6ab042e80f08000ccf31508dec234a07860003438194237b08d281e18000d0d9470f0283bd8000ccf50).toArray⟩
theorem h71:check 7 71 d71=true:=by decide+kernel
def d72:Row:=⟨BCurve 57 47 0x9f5b2170e120ab6a00d2a9f5b43016a9eadd460e03499008cfb0a3e440af474375e2e46cf3301ea3c0403423a4185ad21738c3be6855475b86a7d6fce59622203245bae5b581869886122e9caf9b2c3d0ee000000000000046ef07bb5f7fe80030000000000001148e72e1493b70008000000000000435831b5451dd00010009,decode 5 1 0x76b6a6926464f3370ef9445ba003b80000300002000010009,(AH 7 0x140f5b03ce80d08000d05ba04992c085a01da000333ccec10fa03b6000333be54230b08b681da8000d0d90508c2c22da076a000343415c3cab0f1e83b48000d0f25).toArray⟩
theorem h72:check 7 72 d72=true:=by decide+kernel
def d73:Row:=⟨BCurve 54 47 0x140f58965779f56d201a553eb68616babaa7d7972d482c08cfb0a3e4457a0a973c7d47877c80f51e0201a1e2a7860e223ee0ebee8c586a29a8a95369bca7be03872200000000000123270b5fe2ec2000c00000000000237c1be559c2fa0010000000000004526acbd6e50e00010008,decode 5 1 0x76b696920b64ef970ebe003910000300002000010008,(AH 7 0x140f1b03c280cd8000d03910482ec087a01d6000333be6c113a03aa000333af94229b089a81d48000d0d17508a6c226a07520003431c9c3d5b0f4e83a78000d0ef8).toArray⟩
theorem h73:check 7 73 d73=true:=by decide+kernel
def d74:Row:=⟨BCurve 54 47 0x14334cfe92cfd56d001a553eb68616cab7c8736c2746b808cfb0a3e44579949544c449a75e80f51e0201a1dc172b4f565adce81ebd58bbe9c8e9904922c8e66982b60000000000012aaa77fb27e8c000c0000000000024697973a6608a00100000000000046fb47cfcf87f80010008,decode 5 1 0x76b68691ae64ebd70e810015b0000300002000010008,(AH 7 0x303bd40eeb03b680ca8000d415b046b94088b021e80738000d0ebd50446c10fa039e000343a054222b087e81cd8000d0c9a5088ac21fa0736000342f6dc3e1b0f7a839b8000d0eca).toArray⟩
theorem h74:check 7 74 d74=true:=by decide+kernel
def d75:Row:=⟨BCurve 54 47 0x14574166ce25b56ce01a553eb68616d9e23f198cf1453408cfb0a3e44578b4d7055c98c73f80f51e0201a1d9f84fd1da05fce41eee590da9e929cdec8a310f50809c000000000001324664bf4cf58000c000000000002559e7070f001e00100000000000048d602ec68c3180010008,decode 5 1 0x76b676914d64e7f70e410004e0000300002000010008,(AH 7 0x503b2c0eba0322000340000114db021a80718000cce7f50436c10ca038e000343905421bb086681c78000d0c1a5086ec219a071e000342cf9c3edb0fae838e8000d0e9a).toArray⟩
theorem h75:check 7 75 d75=true:=by decide+kernel
def d76:Row:=⟨BCurve 54 47 0x147b35cf097b956cc01a553eb68616e7d0b6cf1f7343a408cfb0a3e445776b5c7e4634e71f00f51e0201a1dbdbe1fcc4834cdfef1f595f6a096a0c53f2e038b8809a00000000000139fad1ac52126000c00000000000264d649f93a1b60010000000000004ab6de133a02400010008,decode 5 1 0x76b66690e964e3e70dfe0004d0000300002000010008,(AH 7 0x140e9b03a280c58000d0000043a54085b021280708000d0e3e5042ac109a03820003437f94215b084a81c18000d0b9550856c212a0706000342a79c3fab0fe683828000d0e68).toArray⟩
theorem h76:check 7 76 d76=true:=by decide+kernel
def d77:Row:=⟨BCurve 54 47 0x149f2a3744d1756ca01a553eb68616f4832f9423ad420808cfb0a3e44575db647210af06fd00f51e0201a1ddbf7427af009cdb9f5059b12a29aa4b7f5cd662a1809800000000000141c7bec2373f6000c000000000002743f23d3445520010000000000004c9dd9444345700010008,decode 5 1 0x76b656908264dfa70db90004c0000300002000010008,(AH 7 0x5039ac0e5a030e0003400001082b020e806f8000ccdfa5041ec106a037a0003436e5420eb083281bc8000d0b0c5083ac20ca06f20003427e5c408b101e83778000d0e34).toArray⟩
theorem h77:check 7 77 d77=true:=by decide+kernel
def d78:Row:=⟨BCurve 54 47 0x14c31e9f8027556c801a553eb686170062fe6373b7405c08cfb0a3e4457404eee0bc0726da00f51e0201a1dfa30652997decd72f815a02ea49ea8b6ec8138d0b809600000000000149ad2c00fc7c8000c00000000000283d8fdff0eaf20010000000000004e8af47f848ca80010008,decode 5 1 0x76b646901764db470d720004b0000300002000010008,(AH 7 0x140e3b038a80c08000d00000405d4082b0206806d8000d0db450412c103a036e0003435c94208b081a81b68000d0a7f50822c206a06da00034253d4411b1032836b8000d0dfd).toArray⟩
theorem h78:check 7 78 d78=true:=by decide+kernel
def d79:Row:=⟨BCurve 54 47 0x14e71307bb7d356c601a553eb686170b70233d0f913ea008cfb0a3e44571c4bd07b8ac46b600f51e0201a1e186987d83fb3cd28fb25a54aa6a2acc223497b7f6809400000000000151ab1968a1c9c000c00000000000293a3d87c99296001000000000000507e2fc4fdd7e80010008,decode 5 1 0x76b6368fa864d6c70d280004a0000300002000010008,(AH 7 0x50386c0e0a02fa0003400000fa8b0202806c8000ccd6c50406c100a03620003434a14202b080281b08000d09ee5080ac200a06c20003422854405b100283608000d0dc5).toArray⟩
theorem h79:check 7 79 d79=true:=by decide+kernel
def d80:Row:=⟨BCurve 54 47 0x150b076ff6d3156c401a553eb6861714d7f42b430b3cd808cfb0a3e4456f1acee7069e669000f51e0201a1e36a2aa86e788ccdbfe35aa66a8a6b0d99a262e362809200000000000159c186f927272000c000000000002a39fb34be3c3e00100000000000052778b14af27300010008,decode 5 1 0x76b6268f3664d2070cdb000490000300002000010008,(AH 7 0x140deb037680bb8000d000003cd9407fb01fa806a8000d0d20503fac0fda035600034336d41fcb07ea81ab8000d095a507f2c1faa06ae000341fb943f9b0fd283568000d0d8a).toArray⟩
theorem h80:check 7 80 d80=true:=by decide+kernel
def d81:Row:=⟨BCurve 54 48 0xa977dec19147ab61006954fada185c7759c07a71b4ec10119f6147c88ad854c6826add0cd300f51e0201a1e551914b60fc60c8c80a2d7c155555a7ea88ba87a7c049000000000000587c1d2ca32528003000000000000567991cd9dcfd40020000000000005477066e987a800010008,decode 5 1 0x76b6168ec164cd370c8c000490000300002000010008,(AH 7 0x2c0dba02e60003300000ec1b01f680698000cccd3503eec0faa034e00034323141f6b07d281a68000d08c1507dac1f4a069a000341cdd43edb0fa6834b8000d0d4d).toArray⟩
theorem h81:check 7 81 d81=true:=by decide+kernel
def d82:Row:=⟨BCurve 54 48 0xaa9782036bf6ab60006954fada185c9663b4859e1ce470119f6147c88ad1a076a76b174c8300f51e0201a1e73523764b79b0c3a822ada4f56575c96a40e71ddec0480000000000005a8df8a534849000300000000000058854d3bf72b34002000000000000567ca1d2b9d1d80010008,decode 5 1 0x76b6068e4764c8370c3a000480000300002000010008,(AH 7 0x140d9b036280b78000d00000391d407cb01ee80688000d0c83503e2c0f7a03420003430e941f1b07be81a18000d0825507c6c1efa06860003419ed43e2b0f7a83418000d0d0e).toArray⟩
theorem h82:check 7 82 d82=true:=by decide+kernel
def d83:Row:=⟨BCurve 54 48 0xabb7254546a5ab5f006954fada185cb07dacce9164dca0119f6147c88aca5f2bc22d0d8c3000f51e0201a1e918b5a135f700be683b2dcdd57595eb4bf9b7345640470000000000005ca5f427fde8000030000000000005a9728b4888a9c00200000000000058885d41132d380010008,decode 5 1 0x76b5f68dca64c3070be6000470000300002000010008,(AH 7 0x5035ec0d6a02d60003400000dcab01ea80678000ccc30503d6c0f4a033a000342f9941ebb07a6819c8000d0784507aec1e9a06720003416ed43d7b0f4e83378000d0ccd).toArray⟩
theorem h83:check 7 83 d83=true:=by decide+kernel
def d84:Row:=⟨BCurve 54 48 0xacd6c8872154ab5e006954fada185cc74cfd40b3ecd4a0119f6147c88ac24a684d919dcbdb00f51e0201a1eafc47cc207450b8f853adf6b585b60d8fb32acb0e40460000000000005ec40fb4ff4f780030000000000005caf243751ee0c0020000000000005a9a38b9a48ca00010008,decode 5 1 0x76b5e68d4a64bdb70b8f000460000300002000010008,(AH 7 0x50352c0d3a02ca0003400000d4ab01e680658000ccbdb503cec0f2a032e000342e3d41e6b079281978000d06e05079ac1e4a065e0003413d943ccb0f22832d8000d0c8a).toArray⟩
theorem h84:check 7 84 d84=true:=by decide+kernel
def d85:Row:=⟨BCurve 54 48 0xadf66bc8fc03ab5d006954fada185cd92c51f09d54cc60119f6147c88ab9a8a9ceb7ea0b8300f51e0201a1ecdfd9f70af1a0b3686c2e1f9595d630356d41e206c04500000000000060e84b4c38baf80030000000000005ecd3fc45355840020000000000005cb2343c6df0100010008,decode 5 1 0x76b5d68cc664b8370b36000450000300002000010008,(AH 7 0x140d2b034680b08000d0000033194078b01de80648000d0b83503c2c0efa0326000342cd941e0b077a81928000d063850782c1dea064a0003410b143c1b0ef683248000d0c44).toArray⟩
theorem h85:check 7 85 d85=true:=by decide+kernel
def d86:Row:=⟨BCurve 54 48 0xaf160f0ad6b2ab5c006954fada185ce7c0fec9b5fcc3f0119f6147c88ab03372c080d04b2900f51e0201a1eec36c21f56ef0ada884ae4875a5f6533d27fc793fc0440000000000006312a6edaa2a8000300000000000060f17b5b8cc1040020000000000005ed04fc96f57880010008,decode 5 1 0x76b5c68c3f64b2970ada000440000300002000010008,(AH 7 0x50342c0cfa02ba0003400000c3fb01da80638000ccb29503b6c0eca031a000342b6941dbb0766818d8000d058b5076ec1d9a0636000340d7943b7b0ece831a8000d0bfd).toArray⟩
theorem h86:check 7 86 d86=true:=by decide+kernel
def d87:Row:=⟨BCurve 54 48 0xb035b24cb161ab5b006954fada185cf165afe09584bb40119f6147c88aa63140a80b728acc00f51e0201a1f0a6fe4cdfec40a7c89d2e7155b61676a6e35a90b9404300000000000065432299539e10003000000000000631bd6fcfe308c00200000000000060f48b60a8c3080010008,decode 5 1 0x76b5b68bb464acc70a7c000430000300002000010008,(AH 7 0x2c0cda02b20003300000bb4b01d680628000ccacc503aec0eaa03120003429f141d6b075281898000d04db5075ac1d4a0626000340a3143adb0ea683118000d0bb3).toArray⟩
theorem h87:check 7 87 d87=true:=by decide+kernel
def d88:Row:=⟨BCurve 54 48 0xb155558e8c10ab5a006954fada185cf7bfb920a44cb260119f6147c88a9b5b960038aeca6d00f51e0201a1f28a9077ca6990a1b8b5ae9a35c6369a729f5c287340420000000000006779be4f3515a8003000000000000654c52a8a7a41c002000000000000631ee7021a32900010008,decode 5 1 0x76b5a68b2664a6d70a1b000420000300002000010008,(AH 7 0x140cbb032a80aa8000d000002c994074b01ce80618000d0a6d503a2c0e7a030a00034286d41d1b073e81848000d042750746c1cfa06120003406d543a3b0e7e83088000d0b67).toArray⟩
theorem h88:check 7 88 d88=true:=by decide+kernel
def d89:Row:=⟨BCurve 54 48 0xb274f8d066bfab59006954fada185cf929c69e79f4a930119f6147c88a8ff8f04e27a70a0b00f51e0201a1f471f71abced649b88ce2ec315d656bea05c01406dc04200000000000069b67a0f4e91480030000000000006782ee5e891bb4002000000000000654f62adc3a6200010008,decode 5 1 0x76b5968a9364a0b709b8000420000300002000010008,(AH 7 0x140c9b032280a88000d000002a4d4073b01ca80608000d0a0b5039ac0e5a03020003426e141ccb072e81808000d036f50732c1cba06020003403654399b0e5a83008000d0b19).toArray⟩
theorem h89:check 7 89 d89=true:=by decide+kernel
def d90:Row:=⟨BCurve 54 48 0xb3949c12416eab58006954fada185cf7492c457edc9fd0119f6147c88a83c2d20cb93949a700f51e0201a1f6558945a76ab49528e6aeebf5e676e3301949d8a8c0410000000000006bf955d9a010f000300000000000069bfaa1ea297540020000000000006785fe63a51db80010008,decode 5 1 0x76b58689fd649a770952000410000300002000010008,(AH 7 0x140c7b031a80a68000d0000027f54072b01c6805f8000d09a750392c0e3a02fa00034254941c8b071a817c8000d02b350722c1c6a05f20003400014390b0e3282f78000d0ac8).toArray⟩
theorem h90:check 7 90 d90=true:=by decide+kernel
def d91:Row:=⟨BCurve 54 48 0xb4b43f541c1dab57006954fada185cf078962a4aa49640119f6147c88a76b93b3bed65894000f51e0201a1f8391b7091e8048e98ff2f14d5f6970821d735f12440400000000000006e4251ae2994a00030000000000006c0285e8f416fc00200000000000069c2ba23be99580010008,decode 5 1 0x76b576896464940708e9000400000300002000010008,(AH 7 0x50316c0c4a02960003400000964b01c2805e8000cc94050386c0e0a02f20003423a541c3b070681788000d01f35070ec1c1a05e20003400014387b0e0e82ef8000d0a76).toArray⟩
theorem h91:check 7 91 d91=true:=by decide+kernel
def d92:Row:=⟨BCurve 54 48 0xb5d3e295f6ccab560119f6147c88a6922a960e34dc8c800f51e0201a1fa1cad9b7c655487e917af3db606b72d7595c589e0403f00000000000070916d8ceb1c580030000000000006e4b81bd7d9aac0020000000000006c0595ee1019000010007,decode 5 1 0x76b56648c87087e0003f0000300002000010007,(AH 7 0x5030ec0c2a028e00034000008c8b01be805d8000cc8d75037ec0dea02ea0003421f941beb06f681738000d012f506fac1bda05ce000340001437db0dea82e78000d0a21).toArray⟩
theorem h92:check 7 92 d92=true:=by decide+kernel
def d93:Row:=⟨BCurve 54 48 0xb6f385d7d17bab550119f6147c88a5aff1c7b9af2082800f51e0201a1fc003fc666e2a48119302f669616d7532b54f8a2dcc03e00000000000072e6a975e4a818003000000000000709a9d9c3f22640020000000000006e4e91c2999cb00010007,decode 5 1 0x76b5564828708110003e0000300002000010007,(AH 7 0x50306c0c0a02860003400000828b01ba805c8000cc86b50376c0dca02e200034204541bab06e2816f8000d0067506eac1b8a05be0003400014374b0dc682df8000d09ca).toArray⟩
theorem h93:check 7 93 d93=true:=by decide+kernel
def d94:Row:=⟨BCurve 54 48 0xb8132919ac2aab54001198a0ddf50b684a9e13f8887df00f51e0201a1fde3d1f1515ff4784948af8f7626f7794314cf3c19c03d000000000000754205691637e000300000000000072efd98538ae24002000000000000709dada15b24680010007,decode 5 1 0x76b546c7df707840003d0000300002000010007,(AH 7 0x502fec0bea027e0003400000784b01b6805b8000cc7fc5036ec0daa02da000341e8141b6b06d2816c8000d0000506dac1b4a05b2000340001436cb0da282d78000d0971).toArray⟩
theorem h94:check 7 94 d94=true:=by decide+kernel
def d95:Row:=⟨BCurve 54 48 0xb932cc5b86d9ab53001198a0ddf50b4c721fb61b647df00f51e0201a1ffcb389443e3c86dd9612fb85637179fbcd5495597403d00000000000077a381667fcbb0003000000000000754b35786a3dec00200000000000072f2e98a54b0280010007,decode 5 1 0x76b536c7df706dd0003d0000300002000010007,(AH 7 0xb02f6809e8000cc00001b76c06ca016a000331e2ec0d8a02d2000331cb941b1b06c281688000d0000506c6c1b0a05a20003400014363b0d8282cf8000d0915).toArray⟩
theorem h95:check 7 95 d95=true:=by decide+kernel
def d96:Row:=⟨BCurve 55 48 0x2e949be758622ad480046628377d4165e73698dce38fbc01ea3c04034301aecabf2e6118631979afe1364733e34c4b3377aaa01e0000000000001e82c75b8858e2000c000000000000ef5962eba7a378004000000000000754e457d863ff00010007,decode 5 1 0x76b526c7de706310003c0000300002000010007,(AH 7 0xb02ee809c8000cc000018c6c06ba0166000331c62c0d6a02ca000331ae141adb06b281648000d0000506b6c1aca0592000340001435bb0d6282c88000d08b8).toArray⟩
theorem h96:check 7 96 d96=true:=by decide+kernel
def d97:Row:=⟨BCurve 55 48 0x2edc84b7cf0dead440046628377d416225c449a96b0fbc01ea3c04034303925cea18de68582992300a165753f6eb2c1404a9e01d8000000000001f1e365ffebfda000c000000000000f4289afaead32800400000000000077afc17aefd3c00010007,decode 5 1 0x76b516c7de705820003b0000300002000010007,(AH 7 0x140bab02e6809a8000d000001609406ab01a680588000d06a250352c0d3a02c200034190541a9b069e81608000d0000506a6c1a7a05820003400014352b0d3e82c18000d0858).toArray⟩
theorem h97:check 7 97 d97=true:=by decide+kernel
def d98:Row:=⟨BCurve 55 48 0x2f246d8845b9aad400046628377d415e4120b8ba088fbc01ea3c0403430575ef15035bb84cf9aab032f667740abb0d4651c9601d0000000000001fbb2d670327d4000c000000000000f904131e9e0ae80040000000000007a175d82916b980010007,decode 5 1 0x76b506c7de704cf0003a0000300002000010007,(AH 7 0x140b8b02de80998000d00000133d4069b01a280578000d06295034ac0d1a02ba00034171941a5b068e815d8000d000050696c1a3a0576000340001434ab0d1e82b98000d07f6).toArray⟩
theorem h98:check 7 98 d98=true:=by decide+kernel
def d99:Row:=⟨BCurve 55 48 0x2f6c5658bc656ad3c0046628377d415a4218367db68fba01ea3c0403430759813fedd9084199c3305bd677941ebbeeca5f09201c8000000000002059ac709590d0000c000000000000fdebcb56c14ab80040000000000007c8519946b07780010007,decode 5 1 0x76b4f6c7dd70419000390000300002000010007,(AH 7 0x140b6b02d680978000d0000010654068b019e80568000d05ae50342c0cfa02b200034152541a1b067e81598000d000050686c19fa05660003400014342b0cfe82b28000d0792).toArray⟩
theorem h99:check 7 99 d99=true:=by decide+kernel
def d100:Row:=⟨BCurve 55 48 0x2fb43f2933112ad380046628377d4156317713636f8fba01ea3c0403430940e7e2e05cdc3619dbb084b687b432edd0a02c69201c80000000000020f9b37cb5face000c00000000000102dfc3a35492980040000000000007ef8f5b07ca7600010007,decode 5 1 0x76b4e6c7dd70361000390000300002000010007,(AH 7 0xb02d280968000cc00000d86c067a01560003314c6c0cea02ae000331329419db067281568000d000050676c19ca055a000340001433bb0ce282ab8000d072c).toArray⟩
theorem h100:check 7 100 d100=true:=by decide+kernel
def d101:Row:=⟨BCurve 55 48 0x2ffc27f9a9bcead340046628377d4151f4d85e1e440fba01ea3c0403430b247a0dcada2c2a49f430ad9697d44750b2c7b9e9601c000000000000219b428b6465ce000c00000000000107dffc0457e2880040000000000008172f1d6c64b500010007,decode 5 1 0x76b4d6c7dd702a4000380000300002000010007,(AH 7 0x140b3b02ca80948000d000000a92c066a01520003312c2c0cca02a60003311214199b066281528000d000050666c198a054a0003400014333b0cc282a58000d06c3).toArray⟩
theorem h101:check 7 101 d101=true:=by decide+kernel
def d102:Row:=⟨BCurve 55 48 0x304410ca2068aad300046628377d414d9dd4b78c290fb801ea3c0403430d080c38b5577c1e4a0cb0d676a7f45be495410789e01b800000000000223e599ca0d1d0000c0000000000010cec7479cb3a8800400000000000083f30e0747f3480010007,decode 5 1 0x76b4c6c7dc701e4000370000300002000010007,(AH 7 0x140b1b02c280938000d000000792c065a014e0003310bac0caa029e000330f0d4195b0652814f8000d000050656c194a053e000340001432bb0ca6829e8000d0659).toArray⟩
theorem h102:check 7 102 d102=true:=by decide+kernel
def d103:Row:=⟨BCurve 55 48 0x308bf99a97146ad2c0046628377d4149239fcf3e240fb801ea3c0403430eeb9e639fd4cc120a2530ff56b81470a9780c154aa01b00000000000022e2f8b06b3ed4000c00000000000112052d03ae9a9800400000000000086794a42019f480010007,decode 5 1 0x76b4b6c7dc70120000360000300002000010007,(AH 7 0x2c0afa02460003300000120b019280538000cc3a850326c0c8a029a000340cf14192b0642814c8000d00005064ac190a05320003400014324b0c8682988000d05ec).toArray⟩
theorem h103:check 7 103 d103=true:=by decide+kernel
def d104:Row:=⟨BCurve 55 48 0x30d3e26b0dc02ad280046628377d41448639a534350fb801ea3c04034310d305069258a0058a3db12836c834859f5b28e32ba01b00000000000023891fc6c3acda000c000000000001172a25a20202b80040000000000008905a686f34f500010007,decode 5 1 0x76b4a6c7dc70058000360000300002000010007,(AH 7 0x502bac0ada02420003400000058b018e80528000cc3215031ec0c6a0292000340ac9418eb063681498000d00005063ac18da0526000340001431db0c6a82918000d057d).toArray⟩
theorem h104:check 7 104 d104=true:=by decide+kernel
def d105:Row:=⟨BCurve 50 37 0xc46f2cee11afab498cc506efad0f726e7413363ed800000000287a79e992ba6000c00000000143cb02fc26d88004000000000a1e11b55dbef00010005,decode 5 1 0x76b496c7db6c0036c0026c0010005,(AH 7 0x2c0aca023e0003300000000b018a80518000cc29650316c0c4a028e000340899418bb062681468000d00005062ec189a051a0003400014316b0c4e828b8000d050b).toArray⟩
theorem h105:check 7 105 d105=true:=by decide+kernel
def d106:Row:=⟨BCurve 50 37 0xc58ed02fec5eab488cc506efad187b5126ba4a3ed80000000028c2c0ff27f30000c000000001460d3ba8d09d8004000000000a30237ac30d180010005,decode 5 1 0x76b486c7db6c0036c0026c0010005,(AH 7 0x140abb02aa808d8000d000000002c061a014200033082ac0c3a028600033065d4187b061a81438000d00005061ec186a050e000340001430fb0c3282858000d0498).toArray⟩
theorem h106:check 7 106 d106=true:=by decide+kernel
def d107:Row:=⟨BCurve 50 37 0xc6ae7371c70dab478cc506efad218433d9615e3ed800000000290b0814bd2ba000c000000001484f74557a628004000000000a423540285b400010005,decode 5 1 0x76b476c7db6c0036c0026c0010005,(AH 7 0xb02a6808c8000cc000000014061b018280508000d017a5030ac0c1a02820003404194184b060a813f8000d000050612c182a04fe0003400014308b0c16827f8000d0422).toArray⟩
theorem h107:check 7 107 d107=true:=by decide+kernel
def d108:Row:=⟨BCurve 50 37 0xc7ce16b3a1bcab468cc506efad2a8d168c08723ed00000000029534f2a52644000c0000000014a91ad0224278004000000000a5447058da9680010005,decode 5 1 0x76b466c7da6c0036c0026c0010005,(AH 7 0x140a8b029e808b8000d0000000014060b017e804f8000d00e850302c0bfa027a0003401c94180b05fe813d8000d000050602c17fa04f60003400014301b0bfa82798000d03ab).toArray⟩
theorem h108:check 7 108 d108=true:=by decide+kernel
def d109:Row:=⟨BCurve 50 37 0xc8edb9f57c6bab458cc506efad3395f93eaf863ed000000000299b963fe79ce000c0000000014cd3e5aecdec8004000000000a6658caf2f7900010005,decode 5 1 0x76b456c7da6c0036c0026c0010005,(AH 7 0xb029a80898000cc00000002c05fa013a000330152c0bea0276000330001417db05f2813a8000d0000505f6c17ca04ea00034000142fab0be282738000d0331).toArray⟩
theorem h109:check 7 109 d109=true:=by decide+kernel
def d110:Row:=⟨BCurve 50 37 0xca0d5d37571aab448cc506efad3c9edbf1569a3ed00000000029e3dd557cd58000c0000000014f161e5b77b18004000000000a786a905845b80010005,decode 5 1 0x76b446c7da6c0036c0026c0010005,(AH 7 0x50296c0a4a02220003400000000b017a804d8000cc000502f6c0bca026e000340001417ab05e281378000d0000505eac178a04de00034000142f4b0bc6826e8000d02b4).toArray⟩
theorem h110:check 7 110 d110=true:=by decide+kernel
def row (v:ℕ):Row:=match v with
 | 0=>d0
 | 1=>d1
 | 2=>d2
 | 3=>d3
 | 4=>d4
 | 5=>d5
 | 6=>d6
 | 7=>d7
 | 8=>d8
 | 9=>d9
 | 10=>d10
 | 11=>d11
 | 12=>d12
 | 13=>d13
 | 14=>d14
 | 15=>d15
 | 16=>d16
 | 17=>d17
 | 18=>d18
 | 19=>d19
 | 20=>d20
 | 21=>d21
 | 22=>d22
 | 23=>d23
 | 24=>d24
 | 25=>d25
 | 26=>d26
 | 27=>d27
 | 28=>d28
 | 29=>d29
 | 30=>d30
 | 31=>d31
 | 32=>d32
 | 33=>d33
 | 34=>d34
 | 35=>d35
 | 36=>d36
 | 37=>d37
 | 38=>d38
 | 39=>d39
 | 40=>d40
 | 41=>d41
 | 42=>d42
 | 43=>d43
 | 44=>d44
 | 45=>d45
 | 46=>d46
 | 47=>d47
 | 48=>d48
 | 49=>d49
 | 50=>d50
 | 51=>d51
 | 52=>d52
 | 53=>d53
 | 54=>d54
 | 55=>d55
 | 56=>d56
 | 57=>d57
 | 58=>d58
 | 59=>d59
 | 60=>d60
 | 61=>d61
 | 62=>d62
 | 63=>d63
 | 64=>d64
 | 65=>d65
 | 66=>d66
 | 67=>d67
 | 68=>d68
 | 69=>d69
 | 70=>d70
 | 71=>d71
 | 72=>d72
 | 73=>d73
 | 74=>d74
 | 75=>d75
 | 76=>d76
 | 77=>d77
 | 78=>d78
 | 79=>d79
 | 80=>d80
 | 81=>d81
 | 82=>d82
 | 83=>d83
 | 84=>d84
 | 85=>d85
 | 86=>d86
 | 87=>d87
 | 88=>d88
 | 89=>d89
 | 90=>d90
 | 91=>d91
 | 92=>d92
 | 93=>d93
 | 94=>d94
 | 95=>d95
 | 96=>d96
 | 97=>d97
 | 98=>d98
 | 99=>d99
 | 100=>d100
 | 101=>d101
 | 102=>d102
 | 103=>d103
 | 104=>d104
 | 105=>d105
 | 106=>d106
 | 107=>d107
 | 108=>d108
 | 109=>d109
 | 110=>d110
 | _=>default
theorem checked (v:ℕ) (hv:7+v≤117):check 7 v (row v)=true:=by
 have hvl:v≤110:=by omega
 interval_cases v
 · exact h0
 · exact h1
 · exact h2
 · exact h3
 · exact h4
 · exact h5
 · exact h6
 · exact h7
 · exact h8
 · exact h9
 · exact h10
 · exact h11
 · exact h12
 · exact h13
 · exact h14
 · exact h15
 · exact h16
 · exact h17
 · exact h18
 · exact h19
 · exact h20
 · exact h21
 · exact h22
 · exact h23
 · exact h24
 · exact h25
 · exact h26
 · exact h27
 · exact h28
 · exact h29
 · exact h30
 · exact h31
 · exact h32
 · exact h33
 · exact h34
 · exact h35
 · exact h36
 · exact h37
 · exact h38
 · exact h39
 · exact h40
 · exact h41
 · exact h42
 · exact h43
 · exact h44
 · exact h45
 · exact h46
 · exact h47
 · exact h48
 · exact h49
 · exact h50
 · exact h51
 · exact h52
 · exact h53
 · exact h54
 · exact h55
 · exact h56
 · exact h57
 · exact h58
 · exact h59
 · exact h60
 · exact h61
 · exact h62
 · exact h63
 · exact h64
 · exact h65
 · exact h66
 · exact h67
 · exact h68
 · exact h69
 · exact h70
 · exact h71
 · exact h72
 · exact h73
 · exact h74
 · exact h75
 · exact h76
 · exact h77
 · exact h78
 · exact h79
 · exact h80
 · exact h81
 · exact h82
 · exact h83
 · exact h84
 · exact h85
 · exact h86
 · exact h87
 · exact h88
 · exact h89
 · exact h90
 · exact h91
 · exact h92
 · exact h93
 · exact h94
 · exact h95
 · exact h96
 · exact h97
 · exact h98
 · exact h99
 · exact h100
 · exact h101
 · exact h102
 · exact h103
 · exact h104
 · exact h105
 · exact h106
 · exact h107
 · exact h108
 · exact h109
 · exact h110
end AYJ

end SubmissionLower
end ProximityPrize
end
