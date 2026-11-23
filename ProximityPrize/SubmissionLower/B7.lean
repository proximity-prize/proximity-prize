import ProximityPrize.SubmissionLower.E
import ProximityPrize.SubmissionLower.A
import ProximityPrize.SubmissionLower.B3
set_option Elab.async false
set_option autoImplicit true
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P2
noncomputable section
open Polynomial Matrix CoreDefinitions Code gR ProximityPrize.Benchmark
open scoped BigOperators NNReal
export P0 (K I e9 node p blockLength k kB nC aB8 ayo
 sZ aiE vn seed jH twist uO Ox Xb
 JO J9 Z4 ake)
abbrev a08:=P1.a08
abbrev target :a08:=⟨179935,336731609,1073741824,2365,0x3a5b3ea2263e00a,8352383558747982⟩
abbrev dw:=target.dw
abbrev ajO:ℤ:=target.aou
abbrev t:ℕ:=blockLength - dw
abbrev L:ℕ:=dw - k
abbrev DY:ℕ:=t+1 - L - 2
abbrev budget:ℕ:=0x3d0ed83eb28710f
abbrev a9J:=P1.a9J
abbrev B5:=a9J dw
def So (u:e9) :=AI p node (u 0) (u 1) L t
def R5 (u:e9) :=Bx.ay6 (So u)
structure qo (u:e9) where
 a :ℕ
 b:ℕ
 c:ℕ
 ab:a≤b
 active :b≤t
 inactive :t<c
 top:c≤k
 degreeSum:a+b+c=2*k+2
 nullitySum:R5 u+a+b=2*(t+1)
 level :kL.aKl
   (fun s j=>algebraMap K[X] kB (Principal.P8 p node (u 0) (u 1) s j))
   k a b c
def qo.height {u:e9} (T:qo u) :=(k+1) - T.c
abbrev FJ:=P1.FJ
abbrev bje := @P1.bje
abbrev FJ.iF := @P1.FJ.iF
abbrev FJ.label := @P1.FJ.label
abbrev FJ.wK := @P1.FJ.wK
abbrev FJ.decoder := @P1.FJ.decoder
abbrev jG:=FJ DY
abbrev mJ {u deleted} (M:jG u deleted) :=bje dw M
abbrev jG.iF {u deleted} (M:jG u deleted) :=FJ.iF M
abbrev jG.label {u deleted} (M:jG u deleted) :=FJ.label M
abbrev jG.wK {u deleted} (M:jG u deleted) :=FJ.wK M
abbrev jG.decoder {u deleted} (M:jG u deleted) {γ:K} (B:B5 u γ) :=
 FJ.decoder M B
abbrev aYT:=P1.aYT
inductive gJ where
 | h2366
 | Yl
 | l0
 | kP
 | kQ
 | sK
 | kV
 | kY
 | k6
 | l6
 | lR
 | l7
 | l8
 | l9
 | mj
 | m7
 | nT
 | n6
 | pA
 | qk
 | q8
 | rq
 | rC
 | rN
 | rQ
 | sY
 | s4
 | s5
 | tI
 | s6
 | tT
 | s7
 | sJ
 | tv
 | uH
 | lZ
 | om
 | wS
 | vX
 | vg
 | wI
 | vW
 | wO
 | wQ
def gJ.row:gJ→aYT
 | .h2366=>⟨2366,2379,93115474939138867,0x2527a38f00982c1⟩
 | .Yl=>⟨2380,2399,86963514617499853,0x1fccf32e289515b⟩
 | .l0=>⟨2400,2419,80141144427743360,0x1cdd60170fdc3a5⟩
 | .kP=>⟨2420,2439,75622379684181559,0x1ba53a4844c18cf⟩
 | .kQ=>⟨2440,2449,0xec6c9a01c501b4,0x16f8c08dfd144a0⟩
 | .sK=>⟨2450,2459,0xdf784c422b4446,95031637448831224⟩
 | .kV=>⟨2460,2479,0xd400aa56489568,87684038095193899⟩
 | .kY=>⟨2480,2499,0xc06b218c0e0594,73878593397754386⟩
 | .k6=>⟨2500,2519,0xae37b01afebac5,0xe7a9e01bb2e1cb⟩
 | .l6=>⟨2520,2529,0x97db23e85cf884,0xc76b58e77616e5⟩
 | .lR=>⟨2530,2539,0x8f4bd87e5f1747,0xba123f2a591e67⟩
 | .l7=>⟨2540,2549,0x87eccc7b933ab2,0xab638004c86172⟩
 | .l8=>⟨2550,2559,0x815ca68fc615d8,0xa0c4961e9227e7⟩
 | .l9=>⟨2560,2569,0x7b35caa13aa40d,0x94e4eee879f5fb⟩
 | .mj=>⟨2570,2584,0x75e6d9cedc8b78,0x8b925e6d61c3ef⟩
 | .m7=>⟨2585,2589,0x6e3d4eba25800e,0x7f9bedcfbffab2⟩
 | .nT=>⟨2590,2599,0x6beedc13cf3fce,0x7b4364c3ac8d1e⟩
 | .n6=>⟨2600,2600,0x67e2d7a116990b,0x742f5f37049655⟩
 | .pA=>⟨2601,2610,0x5e7d279c5cee1e,0x7864caf748b232⟩
 | .qk=>⟨2611,2620,0x5abc7f01347485,0x716683048d043d⟩
 | .q8=>⟨2621,2639,0x576c6e6f8f6fa7,0x6a9e19368e944e⟩
 | .rq=>⟨2640,2669,0x5249d9435f23f6,0x5eefb661488c92⟩
 | .rC=>⟨2670,2699,0x49f59157b93a46,0x4f9b17715a306e⟩
 | .rN=>⟨2700,2749,0x437a3712c2d445,0x442f4f0de3f4c6⟩
 | .rQ=>⟨2750,2799,0x3b336d17c1cb32,0x35272981f520f4⟩
 | .sY=>⟨2800,2899,0x375dab361799d4,0x284ddeae93503a⟩
 | .s4=>⟨2900,2949,0x2b6b6c50e8eb3d,7539989889497143⟩
 | .s5=>⟨2950,2979,8777438934015614,6750022438537705⟩
 | .tI=>⟨2980,2999,8232174646093835,6265299422480654⟩
 | .s6=>⟨3000,3049,7920769328756114,5914027083230035⟩
 | .tT=>⟨3050,3099,7233131619602069,5133838392304890⟩
 | .s7=>⟨3100,3199,5780812131934959,4711544557140173⟩
 | .sJ=>⟨3200,3399,4609990374200773,0xd4775ea2351fc⟩
 | .tv=>⟨3400,3554,0xc2cb28591a32b,0x91b1a34f0449e⟩
 | .uH=>⟨3555,3999,0x7bd73fd4c6710,0x7cc99261b72f8⟩
 | .lZ=>⟨4000,4799,0x3c1dcb06bed3a,0x4e1e3a877504e⟩
 | .om=>⟨4800,7744,456991479392525,705676274027289⟩
 | .wS=>⟨7745,7999,723244967547378,471048191238102⟩
 | .vX=>⟨8000,14499,651486155753195,425841080879578⟩
 | .vg=>⟨14500,21447,47471425797023,0x97983d103a57⟩
 | .wI=>⟨21448,23999,21281850144313,78255348716729⟩
 | .vW=>⟨24000,28299,19998784942889,63464881996079⟩
 | .wO=>⟨28300,32410,18715989025685,51455234429739⟩
 | .wQ=>⟨32411,33345,3323301173093,58347874659230⟩
end
end P2
end
section
namespace WN
noncomputable section
open P2 MvPolynomial
abbrev N7:=wT.N7
open wT (vO Qb ME MD RK oH Ko xx)
inductive Bank
 | Mi | w22Swapped | NK | Mh | Jj | Sb | YD | YJ | Y1 | w33Swapped
def Bank.dS:Bank→ℕ
 | .Mi | .w22Swapped | .Mh | .Sb=>2
 | .NK | .Jj=>1
 | .YD | .YJ | .Y1 | .w33Swapped=>3
def Bank.dT:Bank→ℕ
 | .Mi | .w22Swapped | .NK | .YJ=>2
 | .Mh | .YD =>1
 | .Jj | .Sb | .Y1 | .w33Swapped=>3
def Bank.s :Bank→ℕ
 | .NK=>16
 | .Jj=>8
 | .Mh=>10
 | .Mi=>11
 | .w22Swapped=>10
 | .Sb=>8
 | .YD =>7
 | .YJ=>6
 | .Y1=>6
 | .w33Swapped=>8
def Bank.t:Bank→ℕ
 | .NK=>10
 | .Jj=>7
 | .Mh=>16
 | .Mi=>10
 | .w22Swapped=>11
 | .Sb=>6
 | .YD =>8
 | .YJ=>8
 | .Y1=>8
 | .w33Swapped=>6
def Bank.a (b:Bank) :ℕ:=b.s+5*b.dS
def Bank.b (b:Bank) :ℕ:=b.t+5*(b.dT - 1)
def Bank.E (b:Bank) :ℕ:=b.a+b.b
def Bank.M (b:Bank) :ℕ:=(2*131071 - 1)*(b.E - 1)+1
def Bank.biR (b:Bank) :ℕ:=b.a+p*b.b
abbrev D4 :=wT.D4
def Bank.GA (b:Bank) (H :ℕ) :Fin 4→ℕ := ![131071+H,1,b.dS,b.dT]
structure asP (u:e9) {deleted:Finset I} (P:N7 deleted)
   (b:Bank) (H :ℕ) where
 L:MvPolynomial (Fin 5) K
 L_ne :L≠0
 degrees : ∀ j,L.weightedTotalDegree (vO 131071 j)=b.GA H j
 order_one : ∀ i:Fin P.N,
   (RK oH
     (Ko (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
       (u 0 (P.index i)^p) (u 1 (P.index i)^p) L)).natTrailingDegree=1
 numerator :MvPolynomial (Fin 4) K
 denominator :MvPolynomial (Fin 4) K
 ayD:denominator≠0
 linear :xx L =
   Polynomial.C denominator*Polynomial.X-Polynomial.C numerator
 primitive : (Polynomial.C denominator*Polynomial.X-Polynomial.C numerator).IsPrimitive
 numerator_Y:numerator.weightedTotalDegree Qb≤1
 denominator_Y:denominator.weightedTotalDegree Qb≤0
 numerator_S:numerator.weightedTotalDegree ME≤b.dS
 denominator_S:denominator.weightedTotalDegree ME≤b.dS
 numerator_T:numerator.weightedTotalDegree MD ≤b.dT
 denominator_T:denominator.weightedTotalDegree MD ≤b.dT - 1
abbrev LV:=wT.LV
end
end WN
end
section
namespace gW
noncomputable section
open Polynomial
open P2 (I K k node dw)
open aR (ao embed extend af Shape aO cK Dd wU qE)
open scoped BigOperators
abbrev gZ:ℕ:=k - 1+P2.ajO.toNat
abbrev bf :ℕ:=gZ+1
export Ds (wD Valid oL wP LN)
inductive Bank where
 | ag
 | dB
 deriving DecidableEq
abbrev Bank.m (_:Bank) :ℕ:=3000
def Bank.box :Bank→Shape
 | .ag=>⟨4016,1650,550⟩
 | .dB=>⟨4020,1650,550⟩
abbrev Ao:ℕ:=3000*dw - 1
def Dj (q:ℕ) :ℕ :=
 if q<3400 then min q 1650 else
 if q<3438 then 1600 else
 if q<3603 then 1550 else
 if q<3634 then 1500 else
 if q<3663 then 1450 else
 if q<3711 then 1400 else
 if q<3770 then 1350 else
 if q<3817 then 1300 else
 if q<3866 then 1250 else
 if q<3914 then 1200 else
 if q<3962 then 1150 else
 if q<4010 then 1100 else
 1050
def aRG (P:af 4) :Prop :=
 ∀ m∈P.support,m 1+m 2+m 3≤Dj (m.sum (fun _ a=>a))
def Contact (b:Bank) (w:I→K) (P:af 4) :Prop :=
  ∀ i (S:ao[X]),S.eval (embed (node i))=embed (w i) →
    (Polynomial.X - C (embed (node i)))^b.m∣cK P S
def aaA (q:Shape) :Prop :=
 aO q Bank.dB.box∧q.j≤q.b∧3*q.t≤q.j
structure aw1 where
 common :af 3
 residual:af 3
 common_ne :common≠0
 residual_ne :residual≠0
 common_total:common.totalDegree≤2332
 common_index :qE common≤886
 residual_total:residual.totalDegree≤340225000
 residual_index :qE residual≤115000000
def aw1.bqU (E :aw1) (S:ao[X]) :Prop :=
 cK E.common S=0∨wU E.residual S 32673
def V7 (cap index top:ℕ) :ℕ :=
  ∑ z∈Finset.range (min cap (min top (index/3))+1),
    ∑ y∈Finset.range (min (cap - z) ((index-3*z)/2)+1),
      (min (cap - z - y) (index-3*z - 2*y)+1)
def Gq (aV:Bank) (used :Shape) :ℕ :=
  let box :=aV.box
  if used.b≤box.b∧used.j≤box.j∧used.t≤box.t then
    ∑ r∈Finset.range (box.b - used.b+1),
      V7 (min r (Dj (r+used.b))) (box.j - used.j) (box.t - used.t)
  else 0
def PR (gH :Shape) (copies :ℕ) :Shape :=
 let b:=Bank.ag.box.b - copies*gH.b
 let j:=min (Bank.ag.box.j - copies*gH.j) (3*b)
 let t:=min (Bank.ag.box.t - copies*gH.t) (j/3)
 ⟨max b j,j,t⟩
def acr (b:Bank) (x :Shape) :Finset ℕ :=
 Finset.range (min (b.box.b/x.b) (min (b.box.j/x.j) (b.box.t/x.t))+1)
def aYp {n:ℕ} (s :K→K[X]) (f :Fin n→af 4) (i:Fin n) (γ:K) :Prop :=
 Dd (f i) (extend (s γ)) ∧ ∀ j,j< i→cK (f j) (extend (s γ))≠0
end
end gW
end
section
namespace gW
noncomputable section
open aR (af shape)
open Ex (X7)
open scoped BigOperators Polynomial
open MvPolynomial UniqueFactorizationMonoid
private theorem b7n (P:af 4) (w:Fin 4→ℕ) :
   (X7 P).weightedTotalDegree (fun i=>w i.castSucc)+w 3*(shape P).t ≤
     P.weightedTotalDegree w:= by
 have h:=aeA.biB (r :=3) w P _ (le_refl _)
 change (X7 P).weightedTotalDegree _+w 3*(Ex.YN P).natDegree≤_ at h
 rwa [Ex.aQU] at h
end
end gW
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace WN
noncomputable section
open P2 MvPolynomial
open Qo (graph)
open bju (afY XD dcH)
private theorem an2 (s d m b:ℕ) (hd:s*d≤b) (hm:b<s*m) :
  d< m:= by
 by_contra! h
 exact (not_lt_of_ge ((Nat.mul_le_mul_left s h).trans hd)) hm
private theorem c1z (q:ℕ) {u:e9} {deleted:Finset I}
   {P:N7 deleted} {U V:MvPolynomial (Fin 5) K} {G:nC}
   (hrel :Aj.ad9 q u deleted (graph q U) (graph q V) G) (i:Fin P.N) :
   XD q (afY (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
     (u 0 (P.index i)^q) (u 1 (P.index i)^q) U V)=G.eval (Polynomial.C (P.nodes i)) := by
 have hkeep:P.index i∉deleted:=(P.Z1 _).mp ⟨i,rfl⟩
 rw [dcH]
 exact hrel (P.index i) hkeep
end
end WN
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace WN
open P2 Finset
open wT (J)
open private po oN count cV xq from ProximityPrize.SubmissionLower.CQ
private theorem b0U:count 5 10 11=2002∧cV 5 10 11=6174 := by
 constructor
 · have r0:po 5 10 11 0=627:= by decide
   have r1 :po 5 10 11 1=500:= by decide
   have r2 :po 5 10 11 2=378:= by decide
   have r3:po 5 10 11 3=264 := by decide
   have r4 :po 5 10 11 4=161 := by decide
   have r5:po 5 10 11 5=72 := by decide
   simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
 · change (∑ i∈range 6,oN 5 10 11 i)=6174
   have r0:oN 5 10 11 0=1375:= by decide
   have r1 :oN 5 10 11 1=1400:= by decide
   have r2 :oN 5 10 11 2=1278:= by decide
   have r3:oN 5 10 11 3=1040:= by decide
   have r4 :oN 5 10 11 4=721 := by decide
   have r5:oN 5 10 11 5=360:= by decide
   simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
private theorem cWf :J 4 10 11=2301 := by
 change (∑ i∈range 4,xq 4 10 11 i)=2301
 have r0:xq 4 10 11 0=1210 := by decide
 have r1 :xq 4 10 11 1=680:= by decide
 have r2 :xq 4 10 11 2=315:= by decide
 have r3:xq 4 10 11 3=96:= by decide
 simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,zero_add]
private theorem b0S:count 4 8 9=985∧cV 4 8 9=2419:= by
 constructor
 · have r0:po 4 8 9 0=360:= by decide
   have r1 :po 4 8 9 1=272 := by decide
   have r2 :po 4 8 9 2=189:= by decide
   have r3:po 4 8 9 3=114 := by decide
   have r4 :po 4 8 9 4=50:= by decide
   simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
 · change (∑ i∈range 5,oN 4 8 9 i)=2419
   have r0:oN 4 8 9 0=630:= by decide
   have r1 :oN 4 8 9 1=640:= by decide
   have r2 :oN 4 8 9 2=553:= by decide
   have r3:oN 4 8 9 3=396:= by decide
   have r4 :oN 4 8 9 4=200:= by decide
   simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
private theorem cWd:J 3 8 9=806:= by
 change (∑ i∈range 3,xq 3 8 9 i)=806
 have r0:xq 3 8 9 0=504 := by decide
 have r1 :xq 3 8 9 1=232 := by decide
 have r2 :xq 3 8 9 2=70:= by decide
 simp only [sum_range_succ,sum_range_zero,r0,r1,r2,zero_add]
private theorem b0O:count 4 5 3=175∧cV 4 5 3=364 := by
 constructor
 · have r0:po 4 5 3 0=60:= by decide
   have r1 :po 4 5 3 1=50:= by decide
   have r2 :po 4 5 3 2=36:= by decide
   have r3:po 4 5 3 3=21 := by decide
   have r4 :po 4 5 3 4=8:= by decide
   simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
 · change (∑ i∈range 5,oN 4 5 3 i)=364
   have r0:oN 4 5 3 0=60:= by decide
   have r1 :oN 4 5 3 1=100:= by decide
   have r2 :oN 4 5 3 2=100:= by decide
   have r3:oN 4 5 3 3=72 := by decide
   have r4 :oN 4 5 3 4=32 := by decide
   simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
private theorem cV9:J 3 5 3=191 := by
 change (∑ i∈range 3,xq 3 5 3 i)=191
 have r0:xq 3 5 3 0=120:= by decide
 have r1 :xq 3 5 3 1=55:= by decide
 have r2 :xq 3 5 3 2=16:= by decide
 simp only [sum_range_succ,sum_range_zero,r0,r1,r2,zero_add]
end WN
end
section
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace WN
noncomputable section
open MvPolynomial
open wT (J vO WH aIi Ko RK oH aCL bx6 bnS brn)
abbrev akW (F:Type*) [Field F] (b:Bank) :=WH F 2 (b.s - b.dS) (b.t - b.dT)
variable {F:Type*} [Field F]
structure a9S (N :ℕ) (L:MvPolynomial (Fin 5) F) (b:Bank) where
 x :Fin N→F
 first:Fin N→F
 firstSlope :Fin N→F
 second:Fin N→F
 secondSlope :Fin N→F
 nonzero :L≠0
 degreeS:L.weightedTotalDegree (vO 1 2)≤b.dS
 degreeT:L.weightedTotalDegree (vO 1 3)≤b.dT
 order_one : ∀ i,(RK oH
   (Ko (x i) (first i) (firstSlope i) (second i) (secondSlope i) L)).natTrailingDegree=1
variable {N :ℕ} {L:MvPolynomial (Fin 5) F} {b:Bank} {H :ℕ} (D:a9S N L b)
def a9S.ic (i:Fin N) (Q:MvPolynomial (Fin 5) F) :=
 Ko (D.x i) (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i) Q
private theorem gqs (i:Fin N) :
  (D.ic i L).weightedTotalDegree (vO 1 2)≤b.dS:= by
 apply (aCL _ _ _ _ _ L).1.trans
 exact D.degreeS
private theorem gqt (i:Fin N) :
  (D.ic i L).weightedTotalDegree (vO 1 3)≤b.dT:= by
 apply (aCL _ _ _ _ _ L).2.trans
 exact D.degreeT
private theorem gqD (i:Fin N) :D.ic i L≠0:= by
 intro hz
 have hh:=D.order_one i
 change (RK oH (D.ic i L)).natTrailingDegree=1 at hh
 simp [hz] at hh
private theorem dyv (b:Bank) :b.s - b.dS+b.dS=b.s := by cases b <;> rfl
private theorem dyw (b:Bank) :b.t - b.dT+b.dT=b.t:= by cases b <;> rfl
private def aaZ (i:Fin N) :akW F b →ₗ[F] WH F 3 b.s b.t where
  toFun Q:=⟨weightedTruncation oH 4 (D.ic i L*Q.val),by
    simpa only [dyv,dyw] using
      bx6 2 (b.s-b.dS) (b.t-b.dT) b.dS b.dT (D.ic i L)
        (gqs D i) (gqt D i) Q⟩
  map_add' Q R:= by apply Subtype.ext; simp [mul_add]
  map_smul' a Q:= by apply Subtype.ext; simp
private theorem exE (i:Fin N) :
  Function.Injective (aaZ D i) := by
 apply LinearMap.ker_eq_bot.mp
 apply LinearMap.ker_eq_bot'.mpr
 intro Q hQ
 by_contra hn
 have hprod:weightedTruncation oH 4 (D.ic i L*Q.val)=0 :=
  congrArg (fun x :WH F 3 b.s b.t=>x.val) hQ
 have hhigh:=(weightedTruncation_eq_zero_iff _ _ _).mp hprod
 have hQn:Q.val≠0:= fun hz=>hn (Subtype.ext hz)
 exact bnS oH 4 (D.ic i L) Q.val
  (D.order_one i) (gqD D i) hQn (brn _ _ _ Q) hhigh
private abbrev IY (i:Fin N) :=
 (WH F 3 b.s b.t) ⧸ LinearMap.range (aaZ D i)
private theorem aIw (i:Fin N) :
  Module.finrank F (IY D i)=J 4 b.s b.t - J 3 (b.s-b.dS) (b.t-b.dT) := by
 have hq:=Submodule.finrank_quotient_add_finrank (LinearMap.range (aaZ D i))
 rw [LinearMap.finrank_range_of_inj (exE D i),aIi,
  aIi] at hq
 change Module.finrank F (IY D i)+J 3 (b.s-b.dS) (b.t-b.dT)=J 4 b.s b.t at hq
 omega
end
end WN
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace WN
noncomputable section
open P2 gR MvPolynomial
open wT (RK Ko bnR)
variable {u:e9} {deleted:Finset I} {P:N7 deleted} {b:Bank} {H :ℕ}
 (D:asP u P b H)
def asP.ic (_D:asP u P b H) (i:Fin P.N) (Q:MvPolynomial (Fin 5) K) :=
  Ko (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
    (u 0 (P.index i)^p) (u 1 (P.index i)^p) Q
private def cBm:a9S P.N D.L b where
 x :=P.nodes
 first:= fun i=>u 0 (P.index i)
 firstSlope := fun i=>u 1 (P.index i)
 second:= fun i=>u 0 (P.index i)^p
 secondSlope := fun i=>u 1 (P.index i)^p
 nonzero :=D.L_ne
 degreeS:=le_of_eq (D.degrees 2)
 degreeT:=le_of_eq (D.degrees 3)
 order_one :=D.order_one
private theorem cH3 {σ:Type*} (v :σ→ℕ) (L:MvPolynomial σ K)
  (hL: (RK v L).natTrailingDegree=1) :L∈restrictWeightedOrder v 1 := by
 apply (bnR v 1 L).mp
 apply Polynomial.X_pow_dvd_iff.mpr
 intro d hd
 apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
 omega
private theorem cCT (b:Bank) :1+(b.dT - 1)=b.dT:= by cases b <;> rfl
end
end WN
end
