import ProximityPrize.SubmissionLower.BR
import ProximityPrize.SubmissionLower.DG
set_option Elab.async false
open _root_ renaming aw9.total → zTo, ite_false → zMv, min_eq_right → zmZ, sub_zero → zTY, xE.denominator → ziF
set_option autoImplicit true
section
namespace aw9
set_option maxRecDepth 16000
set_option maxHeartbeats 0
private theorem dDx (s m n:ℕ) :
   zTo s (m+n)=zTo s m+total (s+m) n:= by
 induction n with
 | zero=>simp [total]
 | succ n ih =>
   change zTo s (m+n)+aDZ (s+(m+n)) =
    zTo s m+(zTo (s+m) n+aDZ (s+m+n))
   rw [ih,Nat.add_assoc s m n,add_assoc]
theorem join {s a b:Nat} {x y :Int}
  (h:zTo s a=x) (k :zTo (s+a) b=y) :zTo s (a+b)=x+y := by
 rw [dDx,h,k]
end aw9
end
section
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace aw9
private theorem c9k :zTo 2250 5=8045641830:= by decide +kernel
private theorem c9l:zTo 2255 5=8012814530:= by decide +kernel
private theorem c9m:zTo 2260 5=7979950150:= by decide +kernel
private theorem c9n:zTo 2265 5=7947049635:= by decide +kernel
private theorem c9o:zTo 2270 5=7914114845:= by decide +kernel
private theorem c9p:zTo 2275 5=7881146740:= by decide +kernel
private theorem c9q:zTo 2280 5=7848147165:= by decide +kernel
private theorem c9s :zTo 2285 5=7815117095:= by decide +kernel
private theorem c9t:zTo 2290 5=7782058360:= by decide +kernel
private theorem c9u:zTo 2295 5=7748971950:= by decide +kernel
private theorem c9v :zTo 2300 5=7715860865:= by decide +kernel
private theorem c9w:zTo 2305 5=7682740840:= by decide +kernel
private theorem c9x :zTo 2310 5=7649620815:= by decide +kernel
private theorem c9y :zTo 2315 5=7616500790:= by decide +kernel
private theorem c9A:zTo 2320 5=7583380765:= by decide +kernel
private theorem c9B:zTo 2325 5=7550260740:= by decide +kernel
private theorem c9C:zTo 2330 5=7517140715:= by decide +kernel
private theorem c9D:zTo 2335 5=7484020690:= by decide +kernel
private theorem c9E :zTo 2340 5=7450900665:= by decide +kernel
private theorem c9F:zTo 2345 5=7417780640:= by decide +kernel
private theorem c9G:zTo 2350 5=7384660615:= by decide +kernel
private theorem c9H :zTo 2355 5=7351540590:= by decide +kernel
private theorem c9I:zTo 2360 5=7318420565:= by decide +kernel
private theorem c9J:zTo 2365 5=7285300540:= by decide +kernel
private theorem aat :zTo 2370 5=7252180515:= by decide +kernel
private theorem c9K:zTo 2375 5=7219060490:= by decide +kernel
private theorem Yl:zTo 2380 5=7185940465:= by decide +kernel
private theorem c9L:zTo 2385 5=7152820440:= by decide +kernel
private theorem aaF:zTo 2390 5=7119700415:= by decide +kernel
private theorem c9M:zTo 2395 5=7086580390:= by decide +kernel
private theorem l0:zTo 2400 5=7053460365:= by decide +kernel
private theorem c9O:zTo 2405 5=7020340340:= by decide +kernel
private theorem aaT:zTo 2410 5=6987220315:= by decide +kernel
private theorem c9P:zTo 2415 5=6954100290:= by decide +kernel
private theorem kP:zTo 2420 5=6920980265:= by decide +kernel
private theorem c9Q:zTo 2425 5=6887860240:= by decide +kernel
private theorem c9R:zTo 2430 5=6854740215:= by decide +kernel
private theorem c9S:zTo 2435 5=6821620190:= by decide +kernel
private theorem kQ:zTo 2440 5=6788500165:= by decide +kernel
private theorem c9T:zTo 2445 5=6755380140:= by decide +kernel
private theorem sK:zTo 2450 5=6722260115:= by decide +kernel
private theorem c9U:zTo 2455 5=6689140090:= by decide +kernel
private theorem kV:zTo 2460 5=6656020065:= by decide +kernel
private theorem c9V:zTo 2465 5=6622900040:= by decide +kernel
private theorem c9W:zTo 2470 5=6589780015:= by decide +kernel
private theorem c9X:zTo 2475 5=6556659990:= by decide +kernel
private theorem kY:zTo 2480 5=6523539965:= by decide +kernel
private theorem c9Y:zTo 2485 5=6490419940:= by decide +kernel
private theorem c9Z:zTo 2490 5=6457299915:= by decide +kernel
private theorem c90:zTo 2495 5=6424179890:= by decide +kernel
theorem gMT:zTo 2250 250=361775827400 :=
 (join c9k <| join c9l <| join c9m <| join c9n <| join c9o <| join c9p <| join c9q <| join c9s <| join c9t <| join c9u <| join c9v <| join c9w <| join c9x <| join c9y <| join c9A <| join c9B <| join c9C <| join c9D <| join c9E <| join c9F <| join c9G <| join c9H <| join c9I <| join c9J <| join aat <| join c9K <| join Yl <| join c9L <| join aaF <| join c9M <| join l0 <| join c9O <| join aaT <| join c9P <| join kP <| join c9Q <| join c9R <| join c9S <| join kQ <| join c9T <| join sK <| join c9U <| join kV <| join c9V <| join c9W <| join c9X <| join kY <| join c9Y <| join c9Z <| c90 :)
end aw9
end
section
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace aw9
private theorem k6:zTo 2500 5=6391059865:= by decide +kernel
private theorem c94 :zTo 2505 5=6357939840:= by decide +kernel
private theorem c95:zTo 2510 5=6324819815:= by decide +kernel
private theorem c96:zTo 2515 5=6291699790:= by decide +kernel
private theorem l6:zTo 2520 5=6258579765:= by decide +kernel
private theorem c97:zTo 2525 5=6225459740:= by decide +kernel
private theorem lR:zTo 2530 5=6192339715:= by decide +kernel
private theorem c98:zTo 2535 5=6159219690:= by decide +kernel
private theorem l7:zTo 2540 5=6126099665:= by decide +kernel
private theorem c99:zTo 2545 5=6092979640:= by decide +kernel
private theorem l8:zTo 2550 5=6059859615:= by decide +kernel
private theorem daa :zTo 2555 5=6026739590:= by decide +kernel
private theorem l9:zTo 2560 5=5993619565:= by decide +kernel
private theorem dac:zTo 2565 5=5960499540:= by decide +kernel
private theorem mj:zTo 2570 5=5927379515:= by decide +kernel
private theorem dad:zTo 2575 5=5894259490:= by decide +kernel
private theorem dae :zTo 2580 5=5861139465:= by decide +kernel
private theorem m7:zTo 2585 5=5828019440:= by decide +kernel
private theorem nT:zTo 2590 5=5794899415:= by decide +kernel
private theorem daf :zTo 2595 5=5761779390:= by decide +kernel
private theorem n6:zTo 2600 5=5728659365:= by decide +kernel
private theorem dag:zTo 2605 5=5695539340:= by decide +kernel
private theorem dah:zTo 2610 5=5662419315:= by decide +kernel
private theorem dai:zTo 2615 5=5629299290:= by decide +kernel
private theorem daj:zTo 2620 5=5596179265:= by decide +kernel
private theorem dak :zTo 2625 5=5563059240:= by decide +kernel
private theorem dal:zTo 2630 5=5529939215:= by decide +kernel
private theorem dam:zTo 2635 5=5496819190:= by decide +kernel
private theorem rq:zTo 2640 5=5463699165:= by decide +kernel
private theorem dao:zTo 2645 5=5430579140:= by decide +kernel
private theorem dap:zTo 2650 5=5397459115:= by decide +kernel
private theorem daq:zTo 2655 5=5364339090:= by decide +kernel
private theorem dar :zTo 2660 5=5331219065:= by decide +kernel
private theorem das :zTo 2665 5=5298099040:= by decide +kernel
private theorem rC:zTo 2670 5=5264979015:= by decide +kernel
private theorem dau:zTo 2675 5=5231858990:= by decide +kernel
private theorem dav :zTo 2680 5=5198738965:= by decide +kernel
private theorem daw:zTo 2685 5=5165618940:= by decide +kernel
private theorem dax :zTo 2690 5=5132498915:= by decide +kernel
private theorem daz :zTo 2695 5=5099378890:= by decide +kernel
private theorem rN :zTo 2700 5=5066281874 := by decide +kernel
private theorem daA:zTo 2705 5=5033305546:= by decide +kernel
private theorem daB:zTo 2710 5=5000472624 := by decide +kernel
private theorem daC:zTo 2715 5=4967782796:= by decide +kernel
private theorem daE :zTo 2720 5=4935235749:= by decide +kernel
private theorem daF:zTo 2725 5=4902831171 := by decide +kernel
private theorem daG:zTo 2730 5=4870568749:= by decide +kernel
private theorem daH :zTo 2735 5=4838448171 := by decide +kernel
private theorem daI:zTo 2740 5=4806469124 := by decide +kernel
private theorem daJ:zTo 2745 5=4774631296:= by decide +kernel
theorem gMC:zTo 2500 250=279004802200 :=
 (join k6 <| join c94 <| join c95 <| join c96 <| join l6 <| join c97 <| join lR <| join c98 <| join l7 <| join c99 <| join l8 <| join daa <| join l9 <| join dac <| join mj <| join dad <| join dae <| join m7 <| join nT <| join daf <| join n6 <| join dag <| join dah <| join dai <| join daj <| join dak <| join dal <| join dam <| join rq <| join dao <| join dap <| join daq <| join dar <| join das <| join rC <| join dau <| join dav <| join daw <| join dax <| join daz <| join rN <| join daA <| join daB <| join daC <| join daE <| join daF <| join daG <| join daH <| join daI <| daJ :)
end aw9
end
section
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace aw9
private theorem dbh:zTo 3500 25=6885103589:= by decide +kernel
private theorem dbi:zTo 3525 25=6544223511 := by decide +kernel
private theorem dbj:zTo 3550 25=6214784839:= by decide +kernel
private theorem dbk :zTo 3575 25=5896592261 := by decide +kernel
private theorem dbl:zTo 3600 25=5589450464 := by decide +kernel
private theorem dbm:zTo 3625 25=5293164136:= by decide +kernel
private theorem dbn:zTo 3650 25=5007537964 := by decide +kernel
private theorem dbo:zTo 3675 25=4732376636:= by decide +kernel
private theorem dbp:zTo 3700 25=4467484839:= by decide +kernel
private theorem dbq:zTo 3725 25=4212667261 := by decide +kernel
theorem gMG:zTo 3500 250=54843385500 :=
 (join dbh <| join dbi <| join dbj <| join dbk <| join dbl <| join dbm <| join dbn <| join dbo <| join dbp <| dbq :)
end aw9
end
section
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace aw9
private theorem dbr :zTo 3750 25=3967728589:= by decide +kernel
private theorem dbs :zTo 3775 25=3732473511 := by decide +kernel
private theorem di4 :zTo 3800 25=3506706714 := by decide +kernel
private theorem di5:zTo 3825 25=3290232886:= by decide +kernel
private theorem di6:zTo 3850 25=3082856714 := by decide +kernel
private theorem di7:zTo 3875 25=2884382886:= by decide +kernel
private theorem dkZ:zTo 3900 25=2694616089:= by decide +kernel
private theorem dk0:zTo 3925 25=2513361011 := by decide +kernel
private theorem dk1 :zTo 3950 25=2340422339:= by decide +kernel
private theorem dk2 :zTo 3975 25=2175604761 := by decide +kernel
theorem gMH :zTo 3750 250=30188385500 :=
 (join dbr <| join dbs <| join di4 <| join di5 <| join di6 <| join di7 <| join dkZ <| join dk0 <| join dk1 <| dk2 :)
end aw9
end
section
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace aw9
private theorem lZ:zTo 4000 25=2018712964 := by decide +kernel
private theorem doW:zTo 4025 25=1869551636:= by decide +kernel
private theorem doX:zTo 4050 25=1727925464 := by decide +kernel
private theorem doY:zTo 4075 25=1593639136:= by decide +kernel
private theorem dut:zTo 4100 25=1466497339:= by decide +kernel
private theorem duu:zTo 4125 25=1346304761 := by decide +kernel
private theorem duw:zTo 4150 25=1232866089:= by decide +kernel
private theorem duJ:zTo 4175 25=1125986011 := by decide +kernel
private theorem dv8:zTo 4200 25=1025469214 := by decide +kernel
private theorem dv9:zTo 4225 25=931120386:= by decide +kernel
theorem gMI:zTo 4000 250=14338073000 :=
 (join lZ <| join doW <| join doX <| join doY <| join dut <| join duu <| join duw <| join duJ <| join dv8 <| dv9 :)
end aw9
end
section
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace aw9
private theorem dwa :zTo 4250 25=842744214 := by decide +kernel
private theorem dwO:zTo 4275 25=760145386:= by decide +kernel
private theorem dwR:zTo 4300 25=683128589:= by decide +kernel
private theorem dwT:zTo 4325 25=611498511 := by decide +kernel
private theorem dxA:zTo 4350 25=545059839:= by decide +kernel
private theorem dxB:zTo 4375 25=483617261 := by decide +kernel
private theorem dxC:zTo 4400 25=426975464 := by decide +kernel
private theorem dxD:zTo 4425 25=374939136:= by decide +kernel
private theorem dxE :zTo 4450 25=327312964 := by decide +kernel
private theorem dxF:zTo 4475 25=283901636:= by decide +kernel
theorem gMJ:zTo 4250 250=5339323000 :=
 (join dwa <| join dwO <| join dwR <| join dwT <| join dxA <| join dxB <| join dxC <| join dxD <| join dxE <| dxF :)
end aw9
end
section
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace aw9
private theorem rQ:zTo 2750 25=23400509839:= by decide +kernel
private theorem daL:zTo 2775 25=22625567261 := by decide +kernel
private theorem sY:zTo 2800 25=21867925464 := by decide +kernel
private theorem daN :zTo 2825 25=21127389136:= by decide +kernel
private theorem daO:zTo 2850 25=20403762964 := by decide +kernel
private theorem daP:zTo 2875 25=19696851636:= by decide +kernel
private theorem s4 :zTo 2900 25=19006459839:= by decide +kernel
private theorem daR:zTo 2925 25=18332392261 := by decide +kernel
private theorem s5:zTo 2950 25=17674453589:= by decide +kernel
private theorem daT:zTo 2975 25=17032448511 := by decide +kernel
theorem gMD:zTo 2750 250=201167760500 :=
 (join rQ <| join daL <| join sY <| join daN <| join daO <| join daP <| join s4 <| join daR <| join s5 <| daT :)
end aw9
end
section
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace aw9
private theorem da3:zTo 3250 25=10966150464 := by decide +kernel
private theorem da4 :zTo 3275 25=10500114136:= by decide +kernel
private theorem da9:zTo 3300 25=10047472339:= by decide +kernel
private theorem dba :zTo 3325 25=9608029761 := by decide +kernel
private theorem dbb:zTo 3350 25=9181591089:= by decide +kernel
private theorem dbd:zTo 3375 25=8767961011 := by decide +kernel
private theorem tv :zTo 3400 25=8366944214 := by decide +kernel
private theorem dbe :zTo 3425 25=7978345386:= by decide +kernel
private theorem dbf :zTo 3450 25=7601969214 := by decide +kernel
private theorem dbg:zTo 3475 25=7237620386:= by decide +kernel
theorem gMF:zTo 3250 250=90256198000 :=
 (join da3 <| join da4 <| join da9 <| join dba <| join dbb <| join dbd <| join tv <| join dbe <| join dbf <| dbg :)
end aw9
end
section
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace aw9
private theorem s6:zTo 3000 25=16406181714 := by decide +kernel
private theorem daU:zTo 3025 25=15795457886:= by decide +kernel
private theorem tT:zTo 3050 25=15200081714 := by decide +kernel
private theorem daW:zTo 3075 25=14619857886:= by decide +kernel
private theorem s7:zTo 3100 25=14054591089:= by decide +kernel
private theorem daY:zTo 3125 25=13504086011 := by decide +kernel
private theorem daZ:zTo 3150 25=12968147339:= by decide +kernel
private theorem da0:zTo 3175 25=12446579761 := by decide +kernel
private theorem sJ:zTo 3200 25=11939187964 := by decide +kernel
private theorem da2 :zTo 3225 25=11445776636:= by decide +kernel
theorem gME :zTo 3000 250=138379948000 :=
 (join s6 <| join daU <| join tT <| join daW <| join s7 <| join daY <| join daZ <| join da0 <| join sJ <| da2 :)
end aw9
end
section
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace aw9
private theorem dxG:zTo 4500 25=244509839:= by decide +kernel
private theorem dxH :zTo 4525 25=208942261 := by decide +kernel
private theorem dxI:zTo 4550 25=177003589:= by decide +kernel
private theorem dxJ:zTo 4575 25=148498511 := by decide +kernel
private theorem dx5:zTo 4600 25=123231714 := by decide +kernel
private theorem dx6:zTo 4625 25=101007886:= by decide +kernel
private theorem dx7:zTo 4650 25=81631714 := by decide +kernel
private theorem dx8:zTo 4675 25=64907886:= by decide +kernel
private theorem dx9:zTo 4700 25=50641089:= by decide +kernel
private theorem dya :zTo 4725 25=38636011 := by decide +kernel
theorem gMK:zTo 4500 250=1239010500 :=
 (join dxG <| join dxH <| join dxI <| join dxJ <| join dx5 <| join dx6 <| join dx7 <| join dx8 <| join dx9 <| dya :)
end aw9
end
section
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace aw9
private theorem dyb:zTo 4750 25=28697339:= by decide +kernel
private theorem dyc:zTo 4775 25=20629761 := by decide +kernel
private theorem om:zTo 4800 25=14237964 := by decide +kernel
private theorem dyG:zTo 4825 25=9326636:= by decide +kernel
private theorem dyH :zTo 4850 25=5700464 := by decide +kernel
private theorem dy5:zTo 4875 25=3164136:= by decide +kernel
private theorem dzg:zTo 4900 25=1522339:= by decide +kernel
private theorem dzh:zTo 4925 25=579761 := by decide +kernel
private theorem dzx :zTo 4950 25=141089:= by decide +kernel
private theorem dzy :zTo 4975 25=11011 := by decide +kernel
theorem gML:zTo 4750 250=84010500 :=
 (join dyb <| join dyc <| join om <| join dyG <| join dyH <| join dy5 <| join dzg <| join dzh <| join dzx <| dzy :)
end aw9
end
section
namespace acY
open xE GI
open scoped BigOperators
private def xY (u:ℤ) :ℤ :=
 if u<0 then 0 else (u*(u*(2*u+21)+66)+72)/72
private theorem XK (x :ℤ) :2*(x*(x - 1)/2)=x*(x - 1) := by
 have h: (2 :ℤ)∣x*(x - 1) := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx
  · exact dvd_mul_of_dvd_left (by omega : (2 :ℤ)∣x) _
  · exact dvd_mul_of_dvd_right (by omega : (2 :ℤ)∣x - 1) _
 rw [mul_comm,Int.ediv_mul_cancel h]
private theorem arn (u:ℤ) :xY u=ziF u:= by
 by_cases hu:u<0
 · simp [xY,ziF,hu]
 simp only [xY,ziF,hu,zMv]
 let q:=u/6
 let r :=u % 6
 have hr :0≤ r∧r<6:= by dsimp [r]; omega
 have hu' : u=6*q+r := by dsimp [q,r]; omega
 have h₁:=XK (r+1)
 rw [show (r+1)*(r+1 - 1)=r*(r+1) by ring] at h₁
 let d:=1+r*(r+1)/2+q*(22+7*r+r*(r - 1)/2) +
   (57+6*r)*(q*(q - 1)/2)+6*q*(q - 1)*(q - 2)
 change (u*(u*(2*u+21)+66)+72)/72=d
 have hpoly :u*(u*(2*u+21)+66)+72 =
     72*d+r*(r*(2*r - 15)+30) := by
   rw [hu']
   dsimp only [d]
   linear_combination -36*(h₁+q*XK r+(57+6*r)*XK q)
 rw [hpoly]
 have hc:0≤ r*(r*(2*r - 15)+30) ∧
     r*(r*(2*r - 15)+30)<72 := by
   obtain ⟨hr₀,hr₁⟩:=hr
   interval_cases r <;> norm_num
 omega
private def Cc (d u:ℤ) :ℤ :=
  if d<0 || u<0 then 0 else
    let v :=min u (3*d)
    let a :=xY v
    if v≤d then a else
      let x :=v - d
      let b:=a - xY (x - 1) - xY (x - 2) - xY (x-3)
      if x≤d+2 then b else
        let y :=x - d
        b + xY (y-3) + xY (y-4) + xY (y - 5)
private theorem afE (d u:ℤ) :Cc d u=gd d u:= by
 unfold Cc gd
 split
 · rfl
 rename_i h
 simp only [arn]
 have hden (x :ℤ) (hx :x<0) :ziF x=0:= by simp [ziF,hx]
 have hv :min u (3*d)≤3*d:=min_le_right _ _
 by_cases h₁:min u (3*d)≤d
 · simp (disch:=omega) only [h₁,ite_true,hden,zTY,add_zero]
 · simp only [h₁,zMv]
   rw [show min u (3*d) - d - d=min u (3*d) - 2*d by ring]
   by_cases h₂:min u (3*d) - d≤d+2
   · simp (disch:=omega) only [h₂,ite_true,hden,add_zero,zTY]
   · simp (disch:=omega) only [h₂,zMv,hden,zTY]
private def EH (d lower cap:ℤ) :ℤ :=
 Cc d (3*cap) - Cc d (min (3*cap) (lower - 1))
private theorem aUL (d lower cap order :ℤ) (hc:0≤ cap) :
   EH d lower cap=oldCount ⟨d,lower,3*cap,cap,order⟩:= by
 simp only [EH,afE,oldCount,U1,not_lt.mpr hc,zMv]
 have hz (u:ℤ) (h:u≤3*cap) :
     gd (d - cap - 1) (u-3*(cap+1))=0:= by
   have hu:u-3*(cap+1)<0:= by omega
   simp [gd,hu]
 rw [hz _ le_rfl,hz _ (min_le_left _ _),zTY,zTY]
private def Cd (d lower cap order :ℤ) :ℤ :=
  if d<0 || cap<0 then 0 else
    let a :=EH d lower cap
    let balance :=order - 1-lower+d
    if balance<0 then a else
      let jO:=min d (balance/4)+1
      let hi:=Cc d (3*cap)
      let adj:=if lower - 1≤3*cap then hi else a+Cc d (lower - 1)
      adj - Cc d (order - 1) +
        Cc (d - jO) (order - 1 - 3*jO) - Cc (d - jO) (lower - 1)
private theorem aDb (d lower cap order :ℤ) :
   Cd d lower cap order=m5 ⟨d,lower,3*cap,cap,order⟩:= by
 by_cases hd:d<0
 · simp [Cd,m5,hd]
 by_cases hc:cap<0
 · simp [Cd,m5,hc]
 have hu : ¬ 3*cap<0:= by omega
 simp only [Cd,m5,AO,hd,hc,hu,decide_false,Bool.or_false,
   Bool.false_eq_true,zMv]
 rw [← aUL _ _ _ _ (by omega)]
 by_cases hb:order - 1-lower+d<0
 · simp [hb]
 simp only [hb,zMv,EH,afE]
 by_cases h:lower - 1≤3*cap
 · simp only [h,ite_true,zmZ h]
   ring
 · simp only [h,zMv]
   ring
def Zr (s j:ℕ) (p:kJ) :ℕ :=
  let lower :ℤ:=1650 - j
  let order :ℤ:=4650 - s - j
  let old:=EH 1650 lower 550
  let initial :=max 0 (Cd 1650 lower 550 order)
  let residual:=Cd (1650-(p.value+(p.top:ℤ)+3*p.Ej))
    (lower-(3*(p.top:ℤ)+2*p.Ej)) (550-(p.top+(p.Ej:ℤ)))
    (order-(2*(p.top:ℤ)+3*p.Ej))
  (old - initial).toNat - (old - max initial residual).toNat
end acY
end
