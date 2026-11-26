import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdZ8H1fka
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Polynomial_Degree_IsMonicOfDegree
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_PowerSeries_Inverse
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Spectrum_Prime_Homeomorph

section Merged6967_DdZQtCuFa
set_option Elab.async false


set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming Fin.sum_univ_succ→c9,Finset.sum_le_sum→nI,Int.toNat_of_nonneg→lz,Module.finrank→mD,Nat.add_sub_cancel→nq,P5_8_1.blockFlags→lV,P5_8_1.flagSpace→lJ,P5_8_2.factorFlags→lI,P5_8_2.initialFlags→cy,ju.total→aU,mul_left_cancel₀→nX
section
set_option autoImplicit true
namespace P5_8_1

def pathCode (q u:ℕ) :ℕ :=
  if u=61-q∧14≤q∧q≤41 then
    if q≤22 then 0x1300+8*(25-q)+5
    else if q=23 then 0x1513
    else if q≤38 then 0x13
    else if q≤40 then 0x1613
    else 0x131e
  else match q with
  | 42=>if u=19 then 0x16131e else if u=20 then 0x16 else 0
  | 43=>if u=18 then 0x161326 else if u=19 then 0x16 else 0
  | 44=>if u=17 then 0x161326 else if u=18 then 0x1e else 0
  | 45=>if u=16 then 0x16132e else if u=17 then 0x161e else if u=18 then 0x16 else 0
  | 46=>if u=15 then 0x131e2e else if u=16 then 0x1626 else if u=17 then 0x16 else 0
  | 47=>if u=14 then 0x131e36 else if u=15 then 0x1626 else if u=16 then 0x1e else 0
  | 48=>if u=14 then 0x162e else if u=15 then 0x161e else if u=16 then 0x16 else 0
  | 49=>if u=13 then 0x1e2e else if u=14 then 0x1626 else if u=15 then 0x16 else 0
  | 50=>if u=13 then 0x1626 else if u=14 then 0x1e else 0
  | 51=>if u=12 then 0x162e else if u=13 then 0x161e else if u=14 then 0x16 else 0
  | 52=>if u=12 then 0x1626 else if u=13 then 0x16 else 0
  | 53=>if u=11 then 0x1626 else if u=12 then 0x1e else 0
  | 54=>if u=11 then 0x161e else if u=12 then 0x16 else 0
  | 55=>if u=10 then 0x1626 else if u=11 then 0x16 else 0
  | 56=>if u=10 then 0x1e else 0
  | 57=>if u=9 then 0x161e else if u=10 then 0x16 else 0
  | 58=>if u=9 then 0x16 else 0
  | 59=>if u=8 then 0x91e else 0
  | 60=>if u=8 then 0x16 else 0
  | 61=>if u=7 then 0x14090916 else 0
  | 62=>if u=7 then 0x9 else 0
  | 63=>if u=6 then 0x9161411 else 0
  | 64=>if u=6 then 0x140909 else 0
  | 65=>if u=5 then 0x1409091411 else if u=6 then 0x9 else 0
  | 66=>if u=5 then 0x91411 else 0
  | 67=>if u=4 then 0x914111411 else if u=5 then 0x140909 else 0
  | 68=>if u=4 then 0x1409091411 else if u=5 then 0x9 else 0
  | 69=>if u=3 then 0x14090914111411 else if u=4 then 0x91411 else 0
  | 70=>if u=3 then 0x914111411 else if u=4 then 0x140909 else 0
  | 71=>if u=2 then 0x14090914111c19 else if u=3 then 0x1409091411 else if u=4 then 0x9 else 0
  | 72=>if u=2 then 0x14090914111411 else if u=3 then 0x91411 else 0
  | 73=>if u=1 then 0x9141114111c19 else if u=2 then 0x914111411 else if u=3 then 0x140909 else 0
  | 74=>if u=1 then 0x14090914111c19 else if u=2 then 0x1409091411 else if u=3 then 0x9 else 0
  | 75=>if u=0 then 0x14090914111412111c19 else if u=1 then 0x14090914111411 else if u=2 then 0x91411 else 0
  | 76=>if u=0 then 0x914111412111c19 else if u=1 then 0x914111411 else if u=2 then 0x140909 else 0
  | 77=>if u=0 then 0x1409091412111c19 else if u=1 then 0x1409091411 else if u=2 then 0x9 else 0
  | 78=>if u=0 then 0x91411141219 else if u=1 then 0x140911 else if u=2 then 0x9 else 0
  | 79=>if u=0 then 0x140909141219 else if u=1 then 0x11 else if u=2 then 0x9 else 0
  | 80=>if u=0 then 0x14091219 else if u=1 then 0x11 else if u=2 then 0x9 else 0
  | 81=>if u=0 then 0x1219 else if u=1 then 0x11 else if u=2 then 0x9 else 0
  | 82=>if u=0 then 0x1219 else if u=1 then 0x11 else if u=2 then 0x9 else 0
  | 83=>if u=0 then 0x1219 else if u=1 then 0x11 else if u=2 then 0x9 else 0
  | _=>0
def decode :ℕ→ℕ→Steps
  | 0,_=>[]
  | n+1,z=>if z=0 then [] else
    (⟨(z%8-1)%6,Nat.mod_lt _ (by decide)⟩,(z%256)/8) :: decode n (z/256)
def ng (q u:ℕ) :ℕ :=
  let z :=pathCode q u
  min (rows q u) (cols q u - if z=0 then 0 else
    flagLower (iO q) (lV q u) (decode 10 z))
def cV (q:ℕ) :ℕ:=aU (ng q) (86-q)
private def c5W (q:ℕ) :ℕ:=aU (fun u =>
 let z :=pathCode q u
 min (c5X q u) (cols q u - if z=0 then 0 else
  flagLower (iO q) (lV q u) (decode 10 z))) (86-q)
private theorem yY (q:ℕ) :cV q=c5W q:= by
 unfold cV c5W
 congr 1
 funext u
 simp only [ng,eQo]
private theorem step {q r x y :ℕ} (hs :aU cV q=r)
  (hx :c5W q=x) (hy :r + x=y) :aU cV (q+1)=y := by
 rw [aU,hs,yY,hx,hy]
set_option quotPrecheck false in
local notation "az" prev "," value=>step prev (x :=value) (by decide +kernel) (by decide +kernel)
private theorem r0:aU cV 0=0:=rfl
private theorem r1 :aU cV 1=61 :=az r0,61
private theorem r2 :aU cV 2=241 :=az r1,180
private theorem r3:aU cV 3=595:=az r2,354
private theorem r4 :aU cV 4=1175:=az r3,580
private theorem r5:aU cV 5=2030:=az r4,855
private theorem r6:aU cV 6=3206:=az r5,1176
private theorem r7:aU cV 7=4746:=az r6,1540
private theorem r8:aU cV 8=6690:=az r7,1944
private theorem r9:aU cV 9=9075:=az r8,2385
private theorem dz :aU cV 10=11935:=az r9,2860
private theorem dD:aU cV 11=15301 :=az dz,3366
private theorem dK:aU cV 12=19201 :=az dD,3900
private theorem e8:aU cV 13=23611 :=az dK,4410
private theorem gD:aU cV 14=28507:=az e8,4896
private theorem gx :aU cV 15=33865:=az gD,5358
private theorem iu:aU cV 16=39615:=az gx,5750
private theorem kD:aU cV 17=45690:=az iu,6075
private theorem lH :aU cV 18=52026:=az kD,6336
private theorem kR:aU cV 19=58562 :=az lH,6536
private theorem jV:aU cV 20=65240:=az kR,6678
private theorem lp:aU cV 21=72005:=az jV,6765
private theorem kZ:aU cV 22=78805:=az lp,6800
private theorem lQ:aU cV 23=85591 :=az kZ,6786
private theorem nJ:aU cV 24=92317:=az lQ,6726
private theorem nP:aU cV 25=98940:=az nJ,6623
private theorem qA:aU cV 26=105420:=az nP,6480
private theorem tj:aU cV 27=111720:=az qA,6300
private theorem qH :aU cV 28=117840:=az tj,6120
private theorem oQ:aU cV 29=123780:=az qH,5940
private theorem xM:aU cV 30=129540:=az oQ,5760
private theorem xd:aU cV 31=135120:=az xM,5580
private theorem r32 :aU cV 32=140520:=az xd,5400
private theorem A4 :aU cV 33=145740:=az r32,5220
private theorem BY:aU cV 34=150780:=az A4,5040
private theorem Cp:aU cV 35=155640:=az BY,4860
private theorem EZ:aU cV 36=160320:=az Cp,4680
private theorem Iz :aU cV 37=164820:=az EZ,4500
private theorem IB:aU cV 38=169141 :=az Iz,4321
private theorem Ku:aU cV 39=173284 :=az IB,4143
private theorem Hz :aU cV 40=177250:=az Ku,3966
private theorem ID :aU cV 41=181041 :=az Hz,3791
private theorem LU:aU cV 42=184659:=az ID,3618
private theorem Vr :aU cV 43=188106:=az LU,3447
private theorem Xv :aU cV 44=191385:=az Vr,3279
private theorem Xw:aU cV 45=194499:=az Xv,3114
private theorem Cw:aU cV 46=197451 :=az Xw,2952
private theorem Cx :aU cV 47=200245:=az Cw,2794
private theorem zB:aU cV 48=202885:=az Cx,2640
private theorem CR:aU cV 49=205375:=az zB,2490
private theorem Db:aU cV 50=207719:=az CR,2344
private theorem LB:aU cV 51=209922 :=az Db,2203
private theorem De :aU cV 52=211987:=az LB,2065
private theorem LD:aU cV 53=213920:=az De,1933
private theorem OD:aU cV 54=215724 :=az LD,1804
private theorem OK :aU cV 55=217405:=az OD,1681
private theorem LH :aU cV 56=218966:=az OK,1561
private theorem Vb:aU cV 57=220413:=az LH,1447
private theorem Vc:aU cV 58=221749:=az Vb,1336
private theorem WV:aU cV 59=222980:=az Vc,1231
private theorem OL:aU cV 60=224109:=az WV,1129
private theorem OM:aU cV 61=225142 :=az OL,1033
private theorem OP:aU cV 62=226082 :=az OM,940
private theorem Vd:aU cV 63=226935:=az OP,853
private theorem r64 :aU cV 64=227704 :=az Vd,769
private theorem WZ:aU cV 65=228395:=az r64,691
private theorem r66:aU cV 66=229011 :=az WZ,616
private theorem r67:aU cV 67=229558:=az r66,547
private theorem r68:aU cV 68=230039:=az r67,481
private theorem r69:aU cV 69=230460:=az r68,421
private theorem r70:aU cV 70=230824 :=az r69,364
private theorem W7:aU cV 71=231137:=az r70,313
private theorem Vo:aU cV 72=231402 :=az W7,265
private theorem r73:aU cV 73=231625:=az Vo,223
private theorem r74 :aU cV 74=231809:=az r73,184
private theorem r75:aU cV 75=231959:=az r74,150
private theorem r76:aU cV 76=232079:=az r75,120
private theorem r77:aU cV 77=232173:=az r76,94
private theorem r78:aU cV 78=232245:=az r77,72
private theorem r79:aU cV 79=232296:=az r78,51
private theorem Xe :aU cV 80=232332 :=az r79,36
private theorem r81 :aU cV 81=232353:=az Xe,21
private theorem r82 :aU cV 82=232365:=az r81,12
private theorem r83:aU cV 83=232369:=az r82,4
theorem budget:aU cV 84=232369:=az r83,0
end P5_8_1
end
section
set_option autoImplicit true
namespace P5_8_1
open i4
open scoped BigOperators
def c1 :Prop :=
  ∀ q u:ℕ,q<84→u<86-q →
    (Bs q u).rank+Module.finrank F (lJ (iO q) (lV q u))≤ cols q u
def c2 :Prop :=
 ∀ (d:ℕ) (f :Flags),rawLower d f≤ mD F (lJ d f)
def c3:Prop :=
  ∀ (d:ℕ) (f :Flags) (i:Fin 6) (k :ℕ),k*yE i≤d →
    mD F (lJ (d-k*yE i) (remove f i k)) ≤
      mD F (lJ d f)
private theorem cY5 (hc:c2) (hm:c3) (xs :Steps) (d:ℕ) (f :Flags) :
   flagLower d f xs≤ mD F (lJ d f) := by
 induction xs generalizing d f with
 | nil=>exact hc d f
 | cons a xs ih =>
   rcases a with ⟨i,k⟩
   rw [flagLower]
   split
   · rename_i hk
     exact max_le (hc d f) ((ih _ _).trans (hm d f i k hk))
   · exact hc d f
private theorem cap (hp:c1) (hc:c2) (hm:c3) (q u:ℕ) (hq:q<84) (hu:u<86-q) :
   (Bs q u).rank≤ng q u:= by
 unfold ng
 apply le_min
 · exact (fTg q u).trans (min_le_left _ _)
 · split
   · rw [Nat.sub_zero]
     exact (fTg q u).trans (min_le_right _ _)
   · have h:=hp q u hq hu
     have hl:=cY5 hc hm (decode 10 (pathCode q u)) (iO q) (lV q u)
     omega
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :P5_8.c1 := by
 refine ⟨?_,bsK⟩
 change (∑ q∈Finset.range 84,∑ u∈Finset.range (86-q),
  (GU source q ((u:ℤ)-25)).rank)≤232369
 rw [← budget,ju.abt]
 apply nI
 intro q hq
 rw [cV,ju.abt]
 apply nI
 intro u hu
 exact (cDg q u).trans (cap h1 h2 h3 q u (Finset.mem_range.mp hq) (Finset.mem_range.mp hu))
end P5_8_1
end
section
set_option autoImplicit true
namespace qxVnKgd
open P5_8_2 Finset
private theorem tri_twice (n:ℕ) :tri n*2=n*(n+1) := by
 have h:tri n = ∑ i∈range (n+1),i:= by
  rw [sum_range_id,tri,nq,mul_comm]
 rw [h,sum_range_id_mul_two,nq,mul_comm]
theorem twice_T {x :ℤ} (hx :0≤x) :T x*2=x*(x+1) := by
 have h:=congrArg (fun n:ℕ=>(n:ℤ)) (tri_twice x.toNat)
 push_cast at h
 rwa [lz hx] at h
theorem H_nonpos {w:ℤ} (hw:w≤0) :H w=0:= by
 have h₁: ((w+1)/2).toNat=0:= by omega
 have h₂: (w/2).toNat=0:= by omega
 simp [H,T,h₁,h₂,tri]
private theorem col_half (v w:ℤ) (hv :v≤0) : (yC (v,w) :ℤ)=H w:= by
 by_cases hw:0≤w
 · have hu:max 0 (max v ((w+1)/2))=(w+1)/2 := by omega
   have hr :max ((w+1)/2) w-(w+1)/2=w/2 := by omega
   change (↑(tri (max 0 (max v ((w+1)/2))).toNat +
    tri (max (max 0 (max v ((w+1)/2))) w - max 0 (max v ((w+1)/2))).toNat) :ℤ)=H w
   rw [hu,hr]
   simp [H,T]
 · have hu:max 0 (max v ((w+1)/2))=0:= by omega
   have hw' : max 0 w=0:= by omega
   rw [H_nonpos (by omega :w≤0)]
   change (↑(tri (max 0 (max v ((w+1)/2))).toNat +
    tri (max (max 0 (max v ((w+1)/2))) w - max 0 (max v ((w+1)/2))).toNat) :ℤ)=0
   simp [hu,hw',tri]
private theorem col_square (r :ℤ) : (yC (r,2*r-1) :ℤ)=(max 0 r)^2 := by
 have hu:max 0 (max r ((2*r-1+1)/2))=max 0 r := by omega
 change (↑(tri (max 0 (max r ((2*r-1+1)/2))).toNat +
   tri (max (max 0 (max r ((2*r-1+1)/2))) (2*r-1) -
     max 0 (max r ((2*r-1+1)/2))).toNat) :ℤ)= _
 rw [hu]
 by_cases h:1≤ r
 · rw [max_eq_right (by omega :0≤ r)]
   have h' : max r (2*r-1)-r=r-1 := by omega
   rw [h',Nat.cast_add]
   change T r+T (r-1)= _
   have h₁:=twice_T (by omega :0≤ r)
   have h₂:=twice_T (by omega :0≤ r-1)
   apply nX  (by decide : (2:ℤ)≠0)
   linear_combination h₁+h₂
 · have hr :max 0 r=0:= by omega
   have hr' : max 0 (2*r-1)=0:= by omega
   simp [hr,hr',tri]
private theorem exp_le (d:ℕ) (flags :Flags) :
   T ((d:ℤ)+1)-(yC (flags 0)+(yC (flags 1) :ℤ)+yC (flags 2))
     ≤ (expected d flags :ℤ) := by
 simp only [T,expected]
 have ht: ((d:ℤ)+1).toNat=d+1 := by omega
 rw [ht]
 omega
theorem low_le {q u:ℕ} {e :ℤ} (hq:q<1959)
   (hp:P u≤0) (he :0≤e) (heq :e≤q) :
   low q ((q:ℤ)-e) (O q u-2*e)≤(m5 q u (line e.toNat) :ℤ) := by
 have hd:deg q=q:=min_eq_left hq.le
 have hc:cost (line e.toNat)=e.toNat := by
   simp [cost,line,yE,c9]
 have hcost:cost (line e.toNat)≤deg q:= by rw [hd,hc]; omega
 unfold m5
 rw [ite_eq_left hcost]
 have h:=exp_le (deg q - cost (line e.toNat)) (wD (cy q u) (line e.toNat))
 have h0:wD (cy q u) (line e.toNat) 0=(0,P u) := by
   simp [wD,cy ,P,offset,line,lI,c9]
 have h1 :wD (cy q u) (line e.toNat) 1 =
     ((q:ℤ)-979,2*((q:ℤ)-979)-1) := by
   simp [wD,cy ,line,lI,c9,hd]
   omega
 have h2 :wD (cy q u) (line e.toNat) 2=(-e,O q u-2*e) := by
   simp [wD,cy ,O,offset,line,lI,c9,lz he]
   ring
 have he' : (↑(deg q - cost (line e.toNat)) :ℤ)=q-e := by rw [hd,hc]; omega
 rw [he',h0,h1,h2,col_half 0 _ (le_refl _),H_nonpos hp,col_square,
   col_half _ _ (by omega : -e≤0),zero_add] at h
 simpa only [low,sub_sub] using h
theorem high_le {q u:ℕ} {a c:ℤ} (hq:1959≤q)
   (ha :0≤a) (hc:0≤ c) (hn:a+c≤979) :
   high (P u) (O q u) a c≤(m5 q u (pair a.toNat c.toNat) :ℤ) := by
 have hd:deg q=1959:=min_eq_right hq
 have hcost' : cost (pair a.toNat c.toNat)=a.toNat+a.toNat+c.toNat*2 := by
   simp [cost,pair,yE,c9]
   omega
 have hcost:cost (pair a.toNat c.toNat)≤deg q:= by rw [hd,hcost']; omega
 unfold m5
 rw [ite_eq_left hcost]
 have h:=exp_le (deg q - cost (pair a.toNat c.toNat))
   (wD (cy q u) (pair a.toNat c.toNat))
 have h0:wD (cy q u) (pair a.toNat c.toNat) 0 =
     (-a-c,P u-2*a-c) := by
   simp [wD,cy ,P,offset,pair,lI,c9,
     lz ha,lz hc]
   constructor <;> ring
 have h1 :wD (cy q u) (pair a.toNat c.toNat) 1 =
     (980-a-c,2*(980-a-c)-1) := by
   simp [wD,cy ,pair,lI,c9,hd,
     lz ha,lz hc]
   constructor <;> ring
 have h2 :wD (cy q u) (pair a.toNat c.toNat) 2 =
     (-a-c,O q u-a-2*c) := by
   simp [wD,cy ,O,offset,pair,lI,c9,
     lz ha,lz hc]
   constructor <;> ring
 let n:ℤ:=980-a-c
 have hn' : 1≤n:= by dsimp [n]; omega
 have hd' : (↑(deg q - cost (pair a.toNat c.toNat)) :ℤ)+1=2*n:= by
   rw [hd,hcost']; dsimp [n]; omega
 have ht:T (2*n)=n*(2*n+1) := by
   have h' := twice_T (by omega :0≤2*n)
   apply nX (by decide : (2:ℤ)≠0)
   linear_combination h'
 rw [hd',ht,h0,h1,h2,col_square,col_half _ _ (by omega : -a-c≤0),
   col_half _ _ (by omega : -a-c≤0)] at h
 change n*(n+1) - H (P u-2*a-c) - H (O q u-a-2*c)≤_
 rw [max_eq_right (by omega :0≤n)] at h
 convert h using 1
 ring
theorem high_swap (p o a c:ℤ) :high p o a c=high o p c a := by
 unfold high
 rw [show o-2*c-a=o-a-2*c by ring,show p-c-2*a=p-2*a-c by ring]
 ring
theorem high_both {s p:ℤ} (hs :s≤2939) :
  high p (s-p) (2*p+(s-p)-3919) (2*(s-p)+p-3919)=(2939-s)*(2940-s) := by
 let k :ℤ:=2939-s
 unfold high
 have h1 :p-2*(2*p+(s-p)-3919)-(2*(s-p)+p-3919)=4*k+1 := by dsimp [k]; ring
 have h2 :s-p-(2*p+(s-p)-3919)-2*(2*(s-p)+p-3919)=4*k+1 := by dsimp [k]; ring
 rw [h1,h2]
 have hH :H (4*k+1)=(2*k+1)^2 := by
  unfold H
  rw [show (4*k+1+1)/2=2*k+1 by omega,show (4*k+1)/2=2*k by omega]
  have hl:=twice_T (by dsimp [k]; omega :0≤2*k+1)
  have hr :=twice_T (by dsimp [k]; omega :0≤2*k)
  apply nX (by decide : (2:ℤ)≠0)
  linear_combination hl+hr
 rw [hH]
 dsimp [k]
 ring
end qxVnKgd
end

end Merged6967_DdZQtCuFa

section Merged6967_Fast063
set_option Elab.async false


set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3
open K1_13 K1_13_7_1 K1_13_7_1_1
open scoped Pointwise
theorem zero_mem_lattice (p : Shape) : 0 ∈ lattice p := by
  simp [lattice]
theorem mem_lattice_iff {p : Shape} {e : Exponent} :
    e ∈ lattice p ↔ (fun i => (e i : ℝ)) ∈ cap p := by
  change (_ ∧ _ ∧ _) ↔
    (∀ i, 0 ≤ (e i : ℝ)) ∧ ((e 0 : ℝ) + e 1 + e 2 + e 3 ≤ p.b) ∧
      ((e 1 : ℝ) + 2 * e 2 + 3 * e 3 ≤ p.j) ∧ (e 3 : ℝ) ≤ p.t
  simp only [Nat.cast_nonneg, implies_true, true_and]
  exact_mod_cast Iff.rfl
theorem lattice_zero : lattice ⟨0, 0, 0⟩ = 0 := by
  ext e
  rw [mem_lattice_iff, cap_zero, Set.mem_zero, Set.mem_zero]
  constructor
  · intro he
    ext i
    change e i = 0
    have hi : (e i : ℝ) = 0 := congrFun he i
    exact_mod_cast hi
  · rintro rfl
    funext i
    simp
private theorem split_weighted {x y A B : ℕ} (h : x + 2 * y ≤ A + B)
    (he : Even A ∨ Even B) :
    ∃ u ≤ x, ∃ v ≤ y, u + 2 * v ≤ A ∧ (x - u) + 2 * (y - v) ≤ B := by
  have hab : (A + B) / 2 = A / 2 + B / 2 := by
    rcases he with ⟨s, hs⟩ | ⟨s, hs⟩ <;> omega
  let v := min y (A / 2)
  have hvy : v ≤ y := min_le_left _ _
  have hvA : v ≤ A / 2 := min_le_right _ _
  have hvB : y - v ≤ B / 2 := by
    dsimp [v]
    omega
  let u := min x (A - 2 * v)
  have hux : u ≤ x := min_le_left _ _
  have huA : u ≤ A - 2 * v := min_le_right _ _
  refine ⟨u, hux, v, hvy, by omega, ?_⟩
  dsimp [u]
  omega
theorem lattice_add {p q : Shape} (hp : Chamber p) (hq : Chamber q)
    (hpj : Even p.j) (hpt : Even p.t) (hqj : Even q.j) :
    lattice (p.plus q) = lattice p + lattice q := by
  apply Set.Subset.antisymm
  · intro e he
    have hb : e 0 + e 1 + e 2 + e 3 ≤ p.b + q.b := he.1
    have hj : e 1 + 2 * e 2 + 3 * e 3 ≤ p.j + q.j := he.2.1
    have ht : e 3 ≤ p.t + q.t := he.2.2
    let z := min (e 3) p.t
    have hze : z ≤ e 3 := min_le_left _ _
    have hzp : z ≤ p.t := min_le_right _ _
    have hzq : e 3 - z ≤ q.t := by dsimp [z]; omega
    have hpz : 3 * z ≤ p.j := by have := hp.2; omega
    have hqz : 3 * (e 3 - z) ≤ q.j := by have := hq.2; omega
    let A := p.j - 3 * z
    let B := q.j - 3 * (e 3 - z)
    have heven : Even A ∨ Even B := by
      rcases le_total (e 3) p.t with h | h
      · have hz : z = e 3 := min_eq_left h
        exact Or.inr (by simpa [B, hz] using hqj)
      · have hz : z = p.t := min_eq_right h
        apply Or.inl
        obtain ⟨a, ha⟩ := hpj
        obtain ⟨b, hb'⟩ := hpt
        refine ⟨a - 3 * b, ?_⟩
        dsimp [A]
        omega
    obtain ⟨u, hu, v, hv, huvA, huvB⟩ :=
      split_weighted (x := e 1) (y := e 2) (A := A) (B := B)
        (by dsimp [A, B]; omega) heven
    change u + 2 * v ≤ p.j - 3 * z at huvA
    change (e 1 - u) + 2 * (e 2 - v) ≤ q.j - 3 * (e 3 - z) at huvB
    have hsumP : u + v + z ≤ p.b := by have := hp.1; omega
    have hsumQ : (e 1 - u) + (e 2 - v) + (e 3 - z) ≤ q.b := by have := hq.1; omega
    let x := min (e 0) (p.b - u - v - z)
    have hxe : x ≤ e 0 := min_le_left _ _
    have hxp : x ≤ p.b - u - v - z := min_le_right _ _
    have hxq : (e 0 - x) + (e 1 - u) + (e 2 - v) + (e 3 - z) ≤ q.b := by
      dsimp [x]
      omega
    let a : Exponent := Finsupp.equivFunOnFinite.symm ![x, u, v, z]
    have ha (i : Fin 4) : a i = (![x, u, v, z] : Fin 4 → ℕ) i := rfl
    have haP : a ∈ lattice p := by
      change a 0 + a 1 + a 2 + a 3 ≤ p.b ∧ a 1 + 2 * a 2 + 3 * a 3 ≤ p.j ∧ a 3 ≤ p.t
      rw [ha 0, ha 1, ha 2, ha 3]
      change x + u + v + z ≤ p.b ∧ u + 2 * v + 3 * z ≤ p.j ∧ z ≤ p.t
      omega
    have hae : a ≤ e := by
      intro i
      fin_cases i <;> rw [ha] <;> assumption
    have haQ : e - a ∈ lattice q := by
      change (e - a) 0 + (e - a) 1 + (e - a) 2 + (e - a) 3 ≤ q.b ∧
        (e - a) 1 + 2 * (e - a) 2 + 3 * (e - a) 3 ≤ q.j ∧ (e - a) 3 ≤ q.t
      simp only [Finsupp.tsub_apply, ha]
      change (e 0 - x) + (e 1 - u) + (e 2 - v) + (e 3 - z) ≤ q.b ∧
        (e 1 - u) + 2 * (e 2 - v) + 3 * (e 3 - z) ≤ q.j ∧ e 3 - z ≤ q.t
      omega
    exact Set.mem_add.mpr ⟨a, haP, e - a, haQ, add_tsub_cancel_of_le hae⟩
  · rintro e ⟨a, ha, b, hb, rfl⟩
    rw [mem_lattice_iff] at ha hb ⊢
    rw [cap_add hp hq]
    exact Set.mem_add.mpr ⟨_, ha, _, hb, by ext i; simp [Finsupp.add_apply]⟩
theorem chamber_scale {p : Shape} (hp : Chamber p) (n : ℕ) : Chamber (p.scale n) := by
  refine ⟨Nat.mul_le_mul_left n hp.1, ?_⟩
  change 3 * (n * p.t) ≤ n * p.j
  simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left n hp.2
theorem lattice_scale {p : Shape} (hp : Chamber p) (hj : Even p.j) (ht : Even p.t)
    (n : ℕ) : lattice (p.scale n) = n • lattice p := by
  induction n with
  | zero =>
    simpa [Shape.scale] using lattice_zero
  | succ n ih =>
    have he : Even (p.scale n).j := by
      change Even (n * p.j)
      exact hj.mul_left n
    have hs : p.scale (n + 1) = p.plus (p.scale n) := by
      cases p
      simp [Shape.scale, Shape.plus, Nat.add_mul, Nat.add_comm]
    rw [hs, lattice_add hp (chamber_scale hp n) hj ht he, ih, succ_nsmul']
end K1_13_6_1_4_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3
noncomputable section
open K1_13 K1_13_7_1 K1_13_7_1_1 MeasureTheory Filter Set
open scoped ENNReal Topology
private def unitCell (e : Exponent) : Set RealPoint :=
  univ.pi fun i => Ico (e i : ℝ) ((e i : ℝ) + 1)
private theorem unitCell_disjoint {e f : Exponent} (h : e ≠ f) :
    Disjoint (unitCell e) (unitCell f) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply h
  ext i
  have hxe := hx i (mem_univ i)
  have hxf := hy i (mem_univ i)
  change (e i : ℝ) ≤ x i ∧ x i < (e i : ℝ) + 1 at hxe
  change (f i : ℝ) ≤ x i ∧ x i < (f i : ℝ) + 1 at hxf
  have hef : (e i : ℝ) < (f i : ℝ) + 1 := hxe.1.trans_lt hxf.2
  have hfe : (f i : ℝ) < (e i : ℝ) + 1 := hxf.1.trans_lt hxe.2
  exact le_antisymm (Nat.lt_succ_iff.mp (by exact_mod_cast hef))
    (Nat.lt_succ_iff.mp (by exact_mod_cast hfe))
private def cells (p : Shape) : Set RealPoint :=
  ⋃ e ∈ (lattice_finite p).toFinset, unitCell e
private theorem volume_cells (p : Shape) : volume (cells p) = ((lattice p).ncard : ℝ≥0∞) := by
  rw [cells, measure_biUnion_finset
    (fun _ _ _ _ h => unitCell_disjoint h)
    (fun _ _ => MeasurableSet.univ_pi fun _ => measurableSet_Ico)]
  have hvol (e : Exponent) : volume (unitCell e) = 1 := by
    unfold unitCell
    rw [Real.volume_pi_Ico]
    simp
  simp only [hvol, Finset.sum_const, nsmul_one, Set.ncard_eq_toFinset_card _ (lattice_finite p)]
private theorem cap_subset_cells (p : Shape) : cap p ⊆ cells p := by
  intro x hx
  obtain ⟨hx, hb, hj, ht⟩ := hx
  let e : Exponent := Finsupp.equivFunOnFinite.symm (fun i => ⌊x i⌋₊)
  have he (i : Fin 4) : e i = ⌊x i⌋₊ := rfl
  have hlo (i : Fin 4) : (e i : ℝ) ≤ x i := by rw [he]; exact Nat.floor_le (hx i)
  have hhi (i : Fin 4) : x i < (e i : ℝ) + 1 := by rw [he]; exact Nat.lt_floor_add_one _
  have hm : e ∈ lattice p := by
    apply mem_lattice_iff.mpr
    exact ⟨fun _ => Nat.cast_nonneg _, by linarith [hlo 0, hlo 1, hlo 2, hlo 3],
      by linarith [hlo 1, hlo 2, hlo 3], (hlo 3).trans ht⟩
  exact mem_iUnion₂.mpr ⟨e, (lattice_finite p).mem_toFinset.mpr hm, fun i _ => ⟨hlo i, hhi i⟩⟩
private def padding : Shape := ⟨6, 6, 1⟩
private theorem cells_subset_cap (p : Shape) : cells p ⊆ cap (p.plus padding) := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
  have he' := mem_lattice_iff.mp ((lattice_finite p).mem_toFinset.mp he)
  obtain ⟨hn, hb, hj, ht⟩ := he'
  have hlo (i : Fin 4) : (e i : ℝ) ≤ x i := (hxe i (mem_univ i)).1
  have hhi (i : Fin 4) : x i < (e i : ℝ) + 1 := (hxe i (mem_univ i)).2
  refine ⟨fun i => (hn i).trans (hlo i), ?_, ?_, ?_⟩ <;>
    simp only [Shape.plus, padding, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] <;>
    linarith [hhi 0, hhi 1, hhi 2, hhi 3]
private theorem volume_cap_ne_top (p : Shape) : volume (cap p) ≠ ∞ := by
  let box : Set RealPoint := Icc 0 fun _ => (p.b : ℝ)
  have hs : cap p ⊆ box := by
    intro x hx
    obtain ⟨hx, hb, _, _⟩ := hx
    refine ⟨hx, ?_⟩
    intro i
    change x i ≤ (p.b : ℝ)
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    have h3 := hx 3
    fin_cases i
    · change x 0 ≤ (p.b : ℝ)
      linarith
    · change x 1 ≤ (p.b : ℝ)
      linarith
    · change x 2 ≤ (p.b : ℝ)
      linarith
    · change x 3 ≤ (p.b : ℝ)
      linarith
  have hfin : volume box ≠ ∞ := by
    change volume (Icc (0 : RealPoint) fun _ => (p.b : ℝ)) ≠ ∞
    rw [Real.volume_Icc_pi]
    exact ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  exact (measure_lt_top_of_subset hs hfin).ne
private theorem lattice_volume_bounds (p : Shape) :
    (volume (cap p)).toReal ≤ ((lattice p).ncard : ℝ) ∧
      ((lattice p).ncard : ℝ) ≤ (volume (cap (p.plus padding))).toReal := by
  have hlo := measure_mono (μ := volume) (cap_subset_cells p)
  have hhi := measure_mono (μ := volume) (cells_subset_cap p)
  rw [volume_cells] at hlo hhi
  exact ⟨by simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hlo,
    by simpa using ENNReal.toReal_mono (volume_cap_ne_top _) hhi⟩
private def volumeFormula (b j t : ℝ) : ℝ :=
  (8*b*j^2*t - 24*b*j*t^2 + 24*b*t^3 - 4*j^3*t + 14*j^2*t^2 - 20*j*t^3 + 9*t^4) / 32
private theorem volume_eq_formula (p : Shape) (hp : Chamber p) :
    (volume (cap p)).toReal = volumeFormula p.b p.j p.t := by
  have h := K1_13_6_1_4_3.cap_volume32 p hp
  unfold volume32 at h
  push_cast at h
  unfold volumeFormula
  linarith
private theorem ratio_volume (R p : Shape) (hR : Chamber R) (hp : Chamber p) :
    Tendsto (fun n : ℕ => (volume (cap (R.plus (p.scale n)))).toReal / (n : ℝ)^4)
      atTop (𝓝 (volume (cap p)).toReal) := by
  have hcoord (r s : ℕ) :
      Tendsto (fun n : ℕ => (s : ℝ) + (r : ℝ) / n) atTop (𝓝 (s : ℝ)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (r : ℝ)).const_add (s : ℝ)
  let f : ℝ × ℝ × ℝ → ℝ := fun y => volumeFormula y.1 y.2.1 y.2.2
  have hc : Continuous f := by unfold f volumeFormula; fun_prop
  have h := hc.continuousAt.tendsto.comp
    ((hcoord R.b p.b).prodMk_nhds ((hcoord R.j p.j).prodMk_nhds (hcoord R.t p.t)))
  rw [volume_eq_formula p hp]
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  rw [volume_eq_formula _ (chamber_plus hR (chamber_scale hp n))]
  simp only [f, Function.comp_apply, Shape.plus, Shape.scale, Nat.cast_add, Nat.cast_mul]
  unfold volumeFormula
  field_simp
  ring
theorem lattice_ratio (R p : Shape) (hR : Chamber R) (hp : Chamber p) :
    Tendsto (fun n : ℕ => ((lattice (R.plus (p.scale n))).ncard : ℝ) / (n : ℝ)^4)
      atTop (𝓝 (volume (cap p)).toReal) := by
  have hpad : Chamber padding := ⟨by decide, by decide⟩
  have hassoc (n : ℕ) : (R.plus (p.scale n)).plus padding = (R.plus padding).plus (p.scale n) := by
    cases R
    cases p
    simp [Shape.plus, Shape.scale, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (ratio_volume R p hR hp)
    (ratio_volume (R.plus padding) p (chamber_plus hR hpad) hp)
  · intro n
    exact div_le_div_of_nonneg_right (lattice_volume_bounds _).1 (by positivity)
  · intro n
    have hb := div_le_div_of_nonneg_right (lattice_volume_bounds (R.plus (p.scale n))).2
      (by positivity : 0 ≤ (n : ℝ)^4)
    simpa only [hassoc] using hb
end
end K1_13_6_1_4_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3
noncomputable section
open K1_13 K1_13_6_1_4_3_3 MvPolynomial
abbrev Degree := Fin 4 → ℕ
abbrev GenericJets (k : Type) [Field k] (P : Fin 4 → Shape) :=
  Jets (CoefficientField k P)
def auxiliary : Shape := ⟨6, 6, 2⟩
def shapeAt (P : Fin 4 → Shape) (b : ℕ) (d : Degree) : Shape :=
  (((((auxiliary.scale b).plus ((P 0).scale (d 0))).plus
    ((P 1).scale (d 1))).plus ((P 2).scale (d 2))).plus ((P 3).scale (d 3)))
def shift (d : Degree) (i : Fin 4) (n : ℕ) : Degree := d + Pi.single i n
def piece (k : Type) [Field k] (P : Fin 4 → Shape) (b : ℕ) (d : Degree) :
    Submodule (CoefficientField k P) (GenericJets k P) :=
  restrictSupport (CoefficientField k P) (lattice (shapeAt P b d))
def prefixIdeal (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ) :
    Ideal (GenericJets k P) :=
  Ideal.span (genericEquation k P '' {i : Fin 4 | i.val < r})
end
end K1_13_6_1_4_3_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3
noncomputable section
open K1_13 K1_13_7_1 K1_13_7_1_1 K1_13_6_1_4_3_3 MvPolynomial
open scoped Pointwise
private theorem auxiliary_admissible : Chamber auxiliary ∧ Even auxiliary.j ∧ Even auxiliary.t :=
  ⟨⟨by decide, by decide⟩, ⟨3, rfl⟩, ⟨1, rfl⟩⟩
private theorem scale_admissible {p : Shape} (hp : Chamber p ∧ Even p.j ∧ Even p.t)
    (n : ℕ) : Chamber (p.scale n) ∧ Even (p.scale n).j ∧ Even (p.scale n).t :=
  ⟨chamber_scale hp.1 n, hp.2.1.mul_left n, hp.2.2.mul_left n⟩
private theorem plus_admissible {p q : Shape} (hp : Chamber p ∧ Even p.j ∧ Even p.t)
    (hq : Chamber q ∧ Even q.j ∧ Even q.t) :
    Chamber (p.plus q) ∧ Even (p.plus q).j ∧ Even (p.plus q).t :=
  ⟨chamber_plus hp.1 hq.1, hp.2.1.add hq.2.1, hp.2.2.add hq.2.2⟩
private theorem shapePlus_comm (p q : Shape) : p.plus q = q.plus p := by
  cases p
  cases q
  simp [Shape.plus, Nat.add_comm]
theorem shapeAt_admissible {P : Fin 4 → Shape}
    (hP : ∀ i, Chamber (P i) ∧ Even (P i).j ∧ Even (P i).t) (b : ℕ) (d : Degree) :
    Chamber (shapeAt P b d) ∧ Even (shapeAt P b d).j ∧ Even (shapeAt P b d).t :=
  plus_admissible (plus_admissible (plus_admissible (plus_admissible
    (scale_admissible auxiliary_admissible b) (scale_admissible (hP 0) (d 0)))
    (scale_admissible (hP 1) (d 1))) (scale_admissible (hP 2) (d 2)))
    (scale_admissible (hP 3) (d 3))
theorem lattice_shapeAt {P : Fin 4 → Shape}
    (hP : ∀ i, Chamber (P i) ∧ Even (P i).j ∧ Even (P i).t) (b : ℕ) (d : Degree) :
    lattice (shapeAt P b d) = ((((b • lattice auxiliary + d 0 • lattice (P 0)) +
      d 1 • lattice (P 1)) + d 2 • lattice (P 2)) + d 3 • lattice (P 3)) := by
  have hA := scale_admissible auxiliary_admissible b
  have hS (i : Fin 4) := scale_admissible (hP i) (d i)
  have h0 := plus_admissible hA (hS 0)
  have h1 := plus_admissible h0 (hS 1)
  have h2 := plus_admissible h1 (hS 2)
  have hadd {p q : Shape} (hp : Chamber p ∧ Even p.j ∧ Even p.t)
      (hq : Chamber q ∧ Even q.j ∧ Even q.t) : lattice (p.plus q) = lattice p + lattice q :=
    lattice_add hp.1 hq.1 hp.2.1 hp.2.2 hq.2.1
  have hscale (i : Fin 4) := lattice_scale (hP i).1 (hP i).2.1 (hP i).2.2 (d i)
  unfold shapeAt
  rw [hadd h2 (hS 3), hadd h1 (hS 2), hadd h0 (hS 1), hadd hA (hS 0),
    lattice_scale auxiliary_admissible.1 auxiliary_admissible.2.1 auxiliary_admissible.2.2 b,
    hscale 0, hscale 1, hscale 2, hscale 3]
theorem shapeAt_shift (P : Fin 4 → Shape) (b : ℕ) (d : Degree) (i : Fin 4) (n : ℕ) :
    shapeAt P b (shift d i n) = (shapeAt P b d).plus ((P i).scale n) := by
  fin_cases i <;>
    simp [shapeAt, shift, Shape.plus, Shape.scale, Pi.single_eq_of_ne, Nat.add_mul] <;>
    omega
variable {k : Type} [Field k] {P : Fin 4 → Shape}
instance piece_finite (b : ℕ) (d : Degree) : Module.Finite (CoefficientField k P) (piece k P b d) :=
  FiniteDimensional.of_finite_basis (basisRestrictSupport _ _) (lattice_finite _)
private theorem generic_supported (i : Fin 4) :
    genericEquation k P i ∈ restrictSupport (CoefficientField k P) (lattice (P i)) := by
  classical
  unfold genericEquation
  apply Submodule.sum_mem
  intro e _
  exact (monomial_mem_restrictSupport _).mpr (Or.inl e.property)
theorem equation_mul_mem_piece (hP : ∀ i, Chamber (P i) ∧ Even (P i).j ∧ Even (P i).t)
    (b : ℕ) (d : Degree) (i : Fin 4) {p : GenericJets k P} (hp : p ∈ piece k P b d) :
    genericEquation k P i * p ∈ piece k P b (shift d i 1) := by
  have hd := shapeAt_admissible hP b d
  have h := Submodule.mul_mem_mul (generic_supported (k := k) (P := P) i) hp
  change genericEquation k P i * p ∈ restrictSupport _ _ * restrictSupport _ _ at h
  rw [← restrictSupport_add, ← lattice_add (hP i).1 hd.1 (hP i).2.1 (hP i).2.2 hd.2.1] at h
  unfold piece
  rw [shapeAt_shift, show (P i).scale 1 = P i from by cases P i; simp [Shape.scale]]
  rwa [shapePlus_comm] at h
private theorem lattice_mono {p q : Shape} (hb : p.b ≤ q.b) (hj : p.j ≤ q.j) (ht : p.t ≤ q.t) :
    lattice p ⊆ lattice q := fun _ h => ⟨h.1.trans hb, h.2.1.trans hj, h.2.2.trans ht⟩
theorem piece_mono {b c : ℕ} {d e : Degree} (hbc : b ≤ c) (hde : d ≤ e) :
    piece k P b d ≤ piece k P c e := by
  unfold piece
  apply restrictSupport_mono
  have h0 := hde 0
  have h1 := hde 1
  have h2 := hde 2
  have h3 := hde 3
  apply lattice_mono <;> simp only [shapeAt, Shape.plus, Shape.scale] <;> gcongr
theorem piece_exhaustive (p : GenericJets k P) : ∃ b : ℕ, p ∈ piece k P b (fun _ => 0) := by
  refine ⟨p.totalDegree, ?_⟩
  apply (mem_restrictSupport_iff _).mpr
  intro e he
  have hd := le_totalDegree (show e ∈ p.support from he)
  rw [Finsupp.sum_fintype e (fun _ m => m) (fun _ => rfl), Fin.sum_univ_four] at hd
  simp only [lattice, Set.mem_ofPred_eq, shapeAt, Shape.plus, Shape.scale, auxiliary,
    Nat.zero_mul, Nat.add_zero]
  omega
theorem finrank_piece (b : ℕ) (d : Degree) :
    Module.finrank (CoefficientField k P) (piece k P b d) = (lattice (shapeAt P b d)).ncard := by
  rw [piece, Module.finrank_eq_nat_card_basis (basisRestrictSupport _ _), Nat.card_coe_set_eq]
end
end K1_13_6_1_4_3_3_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_1_4_3_3_3
noncomputable section
open K1_13 K1_13_6_1_4_3_3 MvPolynomial
private theorem image_algebraic {k σ D : Type} [Field k] [Fintype σ]
    [CommRing D] [Algebra k D] [Algebra (FractionRing (MvPolynomial σ k)) D]
    [IsScalarTower k (FractionRing (MvPolynomial σ k)) D]
    (f : MvPolynomial σ k →ₐ[k] D)
    (c : σ → MvPolynomial σ k)
    (hc : ∀ i, f (c i) = algebraMap (FractionRing (MvPolynomial σ k)) D
      (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) (MvPolynomial.X i)))
    (x : MvPolynomial σ k) : IsAlgebraic (FractionRing (MvPolynomial σ k)) (f x) := by
  let B := MvPolynomial σ k
  let F := FractionRing B
  by_contra hx
  have hX : AlgebraicIndependent k (fun i : σ => algebraMap B F (MvPolynomial.X i)) :=
    (algebraicIndependent_X σ k).map'
      (f := IsScalarTower.toAlgHom k B F) (IsFractionRing.injective B F)
  have hx' : AlgebraicIndependent F (fun _ : Unit => f x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have h := hX.sumElim_comp hx'
  have h' : AlgebraicIndependent k (f ∘ Sum.elim (fun _ : Unit => x) c) := by
    convert h using 1
    funext i
    cases i with
    | inl _ => rfl
    | inr i => exact hc i
  have hle := (AlgebraicIndependent.of_comp f h').cardinalMk_le_trdeg
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype (Unit ⊕ σ),
    Cardinal.mk_fintype σ, Fintype.card_sum, Fintype.card_unit] at hle
  have : 1 + Fintype.card σ ≤ Fintype.card σ := by exact_mod_cast hle
  omega
theorem generic_finite (k : Type) [Field k] (P : Fin 4 → Shape) :
    Module.Finite (CoefficientField k P) (GenericAlgebra k P) := by
  classical
  let (i : Fin 4) : Fintype (lattice (P i)) := (lattice_finite (P i)).fintype
  let σ := Σ i : Fin 4, lattice (P i)
  let : Fintype σ := inferInstanceAs (Fintype (Σ i : Fin 4, lattice (P i)))
  let B := CoefficientRing k P
  let F := CoefficientField k P
  let J := CutIdeal (genericEquation k P)
  let D := GenericAlgebra k P
  let q : GenericJets k P →ₐ[F] D := Ideal.Quotient.mkₐ F J
  let p (i : Fin 4) : lattice (P i) := ⟨0, zero_mem_lattice _⟩
  let coord (i : Fin 4) : D := q (MvPolynomial.X i)
  let coeff (v : σ) : D := algebraMap F D (algebraMap B F (MvPolynomial.X v))
  let f : B →ₐ[k] D := aeval (fun v : σ => if v.2.val = 0 then coord v.1 else coeff v)
  let S := f.toRingHom.range
  have hcoord (i : Fin 4) : coord i ∈ S := by
    refine ⟨MvPolynomial.X ⟨i, p i⟩, ?_⟩
    change f (MvPolynomial.X ⟨i, p i⟩) = coord i
    dsimp only [f]
    rw [aeval_X, ite_eq_left (show (p i).val = 0 from rfl)]
  have hfree (i : Fin 4) (a : lattice (P i)) (ha : a.val ≠ 0) : coeff ⟨i, a⟩ ∈ S := by
    refine ⟨MvPolynomial.X ⟨i, a⟩, ?_⟩
    change f (MvPolynomial.X ⟨i, a⟩) = coeff ⟨i, a⟩
    dsimp only [f]
    rw [aeval_X, ite_eq_right ha]
  have hcoeff (v : σ) : coeff v ∈ S := by
    rcases v with ⟨i, a⟩
    by_cases ha : a.val = 0
    · have hap : a = p i := Subtype.ext ha
      subst a
      let term (e : lattice (P i)) : D :=
        coeff ⟨i, e⟩ * e.val.prod (fun j n => coord j ^ n)
      have ht (e : lattice (P i)) :
          q (monomial e.val (algebraMap B F (MvPolynomial.X ⟨i, e⟩))) = term e := by
        rw [monomial_eq, map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
          map_finsuppProd]
        simp only [term, coeff, coord, map_pow]
      have hz : q (genericEquation k P i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
      have hsum : q (genericEquation k P i) = ∑ e : lattice (P i), term e := by
        rw [genericEquation, map_sum]
        exact Finset.sum_congr rfl fun e _ => ht e
      rw [hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ (p i)),
        show term (p i) = coeff ⟨i, p i⟩ by simp [term, p]] at hz
      rw [eq_neg_of_add_eq_zero_right hz]
      apply S.neg_mem (S.sum_mem fun e he => ?_)
      have hne : e.val ≠ 0 := fun he0 => (Finset.mem_erase.mp he).1 (Subtype.ext he0)
      exact S.mul_mem (hfree i e hne)
        (S.prod_mem fun j _ => S.pow_mem (hcoord j) _)
    · exact hfree i a ha
  choose liftCoeff hliftCoeff using hcoeff
  have halg (i : Fin 4) : IsAlgebraic F (coord i) := by
    obtain ⟨x, hx⟩ := hcoord i
    change f x = coord i at hx
    rw [← hx]
    exact image_algebraic f liftCoeff hliftCoeff x
  have hadj : Algebra.adjoin F (Set.range coord) = ⊤ := by
    rw [show coord = q ∘ MvPolynomial.X from rfl, Set.range_comp, Algebra.adjoin_image,
      MvPolynomial.adjoin_range_X, Algebra.map_top,
      (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective F J)]
  have h := Algebra.isAlgebraic_adjoin_iff.mpr (Set.forall_mem_range.mpr halg)
  rw [hadj] at h
  let : Algebra.IsIntegral F D :=
    Algebra.isAlgebraic_iff_isIntegral.mp (Algebra.isAlgebraic_iff.mpr h)
  exact Algebra.IsIntegral.finite
end
end K1_13_6_1_4_3_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3
noncomputable section
open K1_13 K1_13_6_1_4_3_3
def degreeDifference (F : Degree → ℝ) (i : Fin 4) (n : ℕ) (d : Degree) : ℝ :=
  F (shift d i n) - F d
def degreeDifferences (n : ℕ) (F : Degree → ℝ) (is : List (Fin 4)) : Degree → ℝ :=
  is.foldl (fun H i => degreeDifference H i n) F
private theorem le_shift (d : Degree) (i : Fin 4) (n : ℕ) : d ≤ shift d i n :=
  fun _ => Nat.le_add_right _ _
private theorem shift_succ (d : Degree) (i : Fin 4) (n : ℕ) :
    shift d i (n + 1) = shift (shift d i n) i 1 := by
  funext j
  by_cases h : j = i <;> simp [shift, h, Pi.single_eq_of_ne, add_assoc]
private theorem shift_comm (d : Degree) (i j : Fin 4) (t n : ℕ) :
    shift (shift d j n) i t = shift (shift d i t) j n := by
  unfold shift
  ac_rfl
private theorem line_sum {F G : Degree → ℝ} {q : ℕ} {i : Fin 4}
    (h : ∀ d : Degree, (∀ j, q ≤ d j) → F (shift d i 1) - F d = G (shift d i 1))
    (n : ℕ) (d : Degree) (hd : ∀ j, q ≤ d j) :
    degreeDifference F i n d = ∑ t ∈ Finset.range n, G (shift d i (t + 1)) := by
  induction n with
  | zero => simp [degreeDifference, shift]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, degreeDifference, degreeDifference, shift_succ d i n,
      ← h (shift d i n) (fun j => (hd j).trans (le_shift d i n j))]
    ring
private theorem differences_sum {q : ℕ} {i : Fin 4} {U G : Degree → ℝ}
    (n : ℕ) (is : List (Fin 4))
    (h : ∀ d : Degree, (∀ j, q ≤ d j) → U d = ∑ t ∈ Finset.range n, G (shift d i (t + 1)))
    (d : Degree) (hd : ∀ j, q ≤ d j) :
    degreeDifferences n U is d =
      ∑ t ∈ Finset.range n, degreeDifferences n G is (shift d i (t + 1)) := by
  induction is generalizing U G d with
  | nil => exact h d hd
  | cons j is ih =>
    apply ih (U := degreeDifference U j n) (G := degreeDifference G j n) _ d hd
    intro e he
    simp only [degreeDifference, h (shift e j n) (fun l => (he l).trans (le_shift e j n l)),
      h e he, ← Finset.sum_sub_distrib, shift_comm e i j]
private theorem box_step {F G : Degree → ℝ} {q : ℕ} {i : Fin 4}
    (h : ∀ d : Degree, (∀ j, q ≤ d j) → F (shift d i 1) - F d = G (shift d i 1))
    (n : ℕ) (is : List (Fin 4)) (d : Degree) (hd : ∀ j, q ≤ d j) :
    degreeDifferences n F (i :: is) d =
      ∑ t ∈ Finset.range n, degreeDifferences n G is (shift d i (t + 1)) :=
  differences_sum n is (line_sum h n) d hd
theorem fourfold_telescoping (H : ℕ → Degree → ℝ) (C : ℝ) (q : ℕ)
    (hstep : ∀ (i : Fin 4) (d : Degree), (∀ j, q ≤ d j) →
      H i.val (shift d i 1) - H i.val d = H (i.val + 1) (shift d i 1))
    (htop : ∀ d : Degree, (∀ j, q ≤ d j) → H 4 d = C)
    (n : ℕ) (d : Degree) (hd : ∀ j, q ≤ d j) :
    degreeDifferences n (H 0) [0, 1, 2, 3] d = C * (n : ℝ)^4 := by
  let tail := List.finRange 4
  have htail (i : Fin 4) : tail.drop i.val = i :: tail.drop (i.val + 1) := by
    fin_cases i <;> decide
  have hbox (r : ℕ) (hr : r ≤ 4) : ∀ e : Degree, (∀ j, q ≤ e j) →
      degreeDifferences n (H r) (tail.drop r) e = C * (n : ℝ)^(4 - r) := by
    refine Nat.decreasingInduction' (m := r) (n := 4)
      (motive := fun l => ∀ e : Degree, (∀ j, q ≤ e j) →
        degreeDifferences n (H l) (tail.drop l) e = C * (n : ℝ)^(4 - l)) ?_ hr ?_
    · intro l hl _ ih e he
      let i : Fin 4 := ⟨l, hl⟩
      have ht : tail.drop l = i :: tail.drop (l + 1) := htail i
      rw [ht, box_step (hstep i) _ _ _ he]
      calc
        _ = ∑ _t ∈ Finset.range n, C * (n : ℝ)^(4 - (l + 1)) :=
          Finset.sum_congr rfl fun t _ =>
            ih (shift e i (t + 1)) (fun j => (he j).trans (le_shift e i (t + 1) j))
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [show 4 - l = (4 - (l + 1)) + 1 by omega, pow_succ]
          ring
    · intro e he
      simpa [degreeDifferences, tail, show (List.finRange 4).drop 4 = [] by decide] using htop e he
  exact hbox 0 (by decide) d hd
theorem shape_differences (P : Fin 4 → Shape) (b n : ℕ) (F : Shape → ℝ)
    (d : Degree) (is : List (Fin 4)) :
    degreeDifferences n (fun e => F (shapeAt P b e)) is d =
      is.foldl (fun G i => shapeDifference G ((P i).scale n)) F (shapeAt P b d) := by
  induction is generalizing F with
  | nil => rfl
  | cons i is ih =>
    have he : degreeDifference (fun e => F (shapeAt P b e)) i n =
        fun e => shapeDifference F ((P i).scale n) (shapeAt P b e) := by
      funext e
      simp only [degreeDifference, shapeAt_shift, shapeDifference]
    change degreeDifferences n (degreeDifference (fun e => F (shapeAt P b e)) i n) is d = _
    rw [he]
    exact ih _
end
end K1_13_6_1_4_3_3_3
end
section
namespace K1_13_6_1_3
noncomputable section
open Polynomial K1_13 K1_13_6
abbrev RationalJets := MvPolynomial (Fin 4) GenericField
def toRational : Row 4 →+* RationalJets :=
  MvPolynomial.map (algebraMap (Polynomial Geom) GenericField)
abbrev contractedPrime (surface : Ideal GeoJets) : Ideal RationalJets :=
  surface.comap (MvPolynomial.map (algebraMap GenericField GeoField))
def contractedLength (g P : Row 4) (surface : Ideal GeoJets) (hp : surface.IsPrime) : ℕ∞ := by
  letI := hp
  let L := Localization.AtPrime (contractedPrime surface)
  let J : Ideal L := (Ideal.span {toRational g, toRational P}).map (algebraMap RationalJets L)
  exact Order.coheight J
def NormalForm (g P : Row 4) (surface : Ideal GeoJets) (v : ℕ) : Prop :=
  ∃ t d u B : Row 4,
    toGeneric t ∈ surface ∧ toGeneric d ∉ surface ∧ toGeneric u ∉ surface ∧
    d * P = B * g + u * t ^ v ∧
    ∀ a : Row 4, toGeneric a ∈ surface →
      ∃ e C W : Row 4, toGeneric e ∉ surface ∧ e * a = C * g + W * t
end
end K1_13_6_1_3
end
section
namespace K1_13_6_1_3
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6 K1_13_6_1 K1_13_7_1
local notation "W" => MvPolynomial.weightedTotalDegree
private theorem pderiv_zero_of_weight_lt (w : Fin 4 → ℕ) (i : Fin 4) (P : Row 4)
    (h : W w P < w i) : pderiv i P = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv]
  have hz : P.coeff (m + Finsupp.single i 1) = 0 := by
    by_contra hn
    have hm := le_weightedTotalDegree w (MvPolynomial.mem_support_iff.mpr hn)
    rw [map_add, Finsupp.weight_single, one_smul] at hm
    omega
  simp [hz]
private theorem weight_coeff_deriv (w : Fin 4 → ℕ) (P : Row 4) :
    W w (coefficientDerivative P) ≤ W w P := by
  classical
  apply weight_le_of_support_subset
  intro m hm
  obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have h : j = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [MvPolynomial.coeff_monomial, ite_eq_right hne])
  exact h ▸ hj
private theorem partialFlow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    (P : Row 4) {d : ℕ} (hP : W w P ≤ d) : W w (partialFlow P) ≤ d + Δ := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((weight_coeff_deriv w P).trans (hP.trans (Nat.le_add_right _ _)))
  · apply Submodule.sum_mem
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    apply (weight_const_mul_le w _ _).trans
    by_cases h : w i.castSucc ≤ d
    · have hp := (weightedTotalDegree_pderiv_le_sub w i.castSucc P).trans
        (Nat.sub_le_sub_right hP (w i.castSucc))
      have he := hshift i
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (weight_X_le w _) hp).trans (by omega))
    · rw [pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)), mul_zero,
        weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem flow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hΔ : Δ ≤ B)
    (hg : W w g ≤ B) (hP : W w P ≤ d) :
    W w (flowNumerator g P) ≤ d + 2 * B := by
  have hsep (F : Row 4) : W w (separant F) ≤ W w F :=
    weightedTotalDegree_pderiv_le w 3 F
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    have h := Nat.add_le_add ((hsep g).trans hg) (partialFlow_bound w Δ hshift P hP)
    exact (weightedTotalDegree_mul_le _ _ _).trans (h.trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    have h := Nat.add_le_add (partialFlow_bound w Δ hshift g hg) ((hsep P).trans hP)
    exact (weightedTotalDegree_mul_le _ _ _).trans (h.trans (by omega))
private theorem tangent_weight (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hΔ : Δ ≤ B)
    (hg : W w g ≤ B) (hP : W w P ≤ d) (n : ℕ) :
    W w (tangentCut g P n) ≤ d + (2 * n) * B := by
  induction n with
  | zero => simpa [tangentCut] using hP
  | succ n ih =>
    rw [tangentCut, Function.iterate_succ_apply']
    change W w (flowNumerator g (tangentCut g P n)) ≤ _
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.add_assoc] using
      flow_bound w Δ hshift hΔ hg ih
theorem tangent_box {g P : Row 4} {a b : Shape} (hb : 0 < b.t) (hj : 0 < b.j)
    (hg : InBox (shape g) b) (hP : InBox (shape P) a) (n : ℕ) :
    InBox (shape (tangentCut g P n)) (a.plus (b.scale (2 * n))) := by
  have h₁ : W 1 g ≤ b.b := by simpa only [shape, weightedTotalDegree_one] using hg.1
  have h₂ : W Fin.val g ≤ b.j := by simpa only [shape, indexDegree_eq] using hg.2.1
  let w : Fin 4 → ℕ := Pi.single 3 1
  have h₃ : W w g ≤ b.t := by simpa only [w, shape, weightedTotalDegree_piSingle] using hg.2.2
  have hp₁ : W 1 P ≤ a.b := by simpa only [shape, weightedTotalDegree_one] using hP.1
  have hp₂ : W Fin.val P ≤ a.j := by simpa only [shape, indexDegree_eq] using hP.2.1
  have hp₃ : W w P ≤ a.t := by simpa only [w, shape, weightedTotalDegree_piSingle] using hP.2.2
  have hs₁ : ∀ i : Fin 3, (1 : Fin 4 → ℕ) i.succ ≤ (1 : Fin 4 → ℕ) i.castSucc + 0 := by
    intro i
    change (1 : ℕ) ≤ 1
    exact le_rfl
  have hs₂ : ∀ i : Fin 3, i.succ.val ≤ i.castSucc.val + 1 := fun _ => le_rfl
  have hs₃ : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + 1 := by
    intro i
    fin_cases i <;> decide
  refine ⟨?_, ?_, ?_⟩
  · simpa only [shape, Shape.plus, Shape.scale, weightedTotalDegree_one, Nat.mul_comm] using
      tangent_weight 1 0 hs₁ (Nat.zero_le _) h₁ hp₁ n
  · simpa only [shape, Shape.plus, Shape.scale, indexDegree_eq, Nat.mul_comm] using
      tangent_weight Fin.val 1 hs₂ hj h₂ hp₂ n
  · simpa only [w, shape, Shape.plus, Shape.scale, weightedTotalDegree_piSingle, Nat.mul_comm] using
      tangent_weight w 1 hs₃ hb h₃ hp₃ n
theorem anchor_fits (f : Row 4) : InBox (shape f) (anchorBox f) :=
  ⟨le_max_left _ _, le_rfl, le_rfl⟩
theorem derivative_fits (f : Row 4) (r : ℕ) :
    InBox (shape ((separant^[r]) f)) (anchorBox f) := by
  have d := derivative_in_box f r
  have a := anchor_fits f
  exact ⟨d.1.trans a.1, d.2.1.trans a.2.1, d.2.2.trans a.2.2⟩
end
end K1_13_6_1_3
end
section
namespace K1_13_6_1_3
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_1
open scoped BigOperators
@[simp] private theorem coeff_coefficientDerivative (P : Row 4) (m : Fin 4 →₀ ℕ) :
    (coefficientDerivative P).coeff m = derivative (P.coeff m) := by
  classical
  rw [coefficientDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coefficientDerivative_add (P Q : Row 4) :
    coefficientDerivative (P + Q) = coefficientDerivative P + coefficientDerivative Q := by
  ext m
  simp
private theorem coefficientDerivative_mul (P Q : Row 4) :
    coefficientDerivative (P * Q) = coefficientDerivative P * Q + P * coefficientDerivative Q := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coefficientDerivative]
  change derivative ((P * Q).coeff m) =
    (coefficientDerivative P * Q).coeff m + (P * coefficientDerivative Q).coeff m
  simp only [coeff_coefficientDerivative, MvPolynomial.coeff_mul, map_sum, derivative_mul,
    Finset.sum_add_distrib]
private theorem partialFlow_add (P Q : Row 4) :
    partialFlow (P + Q) = partialFlow P + partialFlow Q := by
  simp only [partialFlow, coefficientDerivative_add, map_add, mul_add, Finset.sum_add_distrib]
  abel
private theorem partialFlow_mul (P Q : Row 4) :
    partialFlow (P * Q) = partialFlow P * Q + P * partialFlow Q := by
  let a : Fin 3 → Row 4 := fun i =>
    MvPolynomial.C (C ((i.val + 1 : ℕ) : Geom)) * MvPolynomial.X i.succ
  change coefficientDerivative (P * Q) +
      (∑ i : Fin 3, a i * MvPolynomial.pderiv i.castSucc (P * Q)) =
    partialFlow P * Q + P * partialFlow Q
  have hs : (∑ i : Fin 3, a i * MvPolynomial.pderiv i.castSucc (P * Q)) =
      (∑ i : Fin 3, a i * MvPolynomial.pderiv i.castSucc P) * Q +
        P * (∑ i : Fin 3, a i * MvPolynomial.pderiv i.castSucc Q) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [MvPolynomial.pderiv_mul]
    ring
  rw [coefficientDerivative_mul, hs]
  change _ = (coefficientDerivative P + (∑ i : Fin 3, a i * MvPolynomial.pderiv i.castSucc P)) * Q +
    P * (coefficientDerivative Q + (∑ i : Fin 3, a i * MvPolynomial.pderiv i.castSucc Q))
  ring
private def delta (g : Row 4) : Row 4 →+ Row 4 where
  toFun := flowNumerator g
  map_add' P Q := by
    simp only [flowNumerator, partialFlow_add, separant, map_add]
    ring
  map_zero' := by
    simp [flowNumerator, separant, partialFlow, coefficientDerivative]
private theorem delta_mul (g x y : Row 4) :
    delta g (x * y) = delta g x * y + x * delta g y := by
  change flowNumerator g (x * y) = flowNumerator g x * y + x * flowNumerator g y
  simp only [flowNumerator, partialFlow_mul, separant, MvPolynomial.pderiv_mul]
  ring
section Iterates
variable {R S : Type*} [CommRing R] [CommRing S]
variable (D : R →+ R) (ρ : R →+* S)
variable (hD : ∀ x y, D (x * y) = D x * y + x * D y)
private theorem iterate_map_add (n : ℕ) (x y : R) :
    (D^[n]) (x + y) = (D^[n]) x + (D^[n]) y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]
include hD
private theorem iterate_mul_residue (n : ℕ) (x y : R)
    (hy : ∀ k < n, ρ ((D^[k]) y) = 0) :
    ρ ((D^[n]) (x * y)) = ρ x * ρ ((D^[n]) y) := by
  induction n generalizing x y with
  | zero => exact map_mul ρ _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply _ _ (x * y), hD, iterate_map_add D, map_add]
    rw [ih (D x) y (fun k hk => hy k (Nat.lt_succ_of_lt hk)), hy n (Nat.lt_succ_self n), mul_zero, zero_add]
    have hy' : ∀ k < n, ρ ((D^[k]) (D y)) = 0 := by
      intro k hk
      exact hy (k + 1) (Nat.succ_lt_succ hk)
    simpa only [Function.iterate_succ_apply] using ih x (D y) hy'
private theorem derivative_pow_succ (t : R) (n : ℕ) :
    D (t ^ (n + 1)) = ((n + 1 : ℕ) : R) * D t * t ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ t (n + 1), hD, ih, pow_succ t n]
    push_cast
    ring
private theorem iterate_power_order (t : R) (ht : ρ t = 0) (n : ℕ) :
    (∀ k < n, ∀ a : R, ρ ((D^[k]) (a * t ^ n)) = 0) ∧
    ∀ a : R, ρ ((D^[n]) (a * t ^ n)) = ρ a * (n.factorial : S) * (ρ (D t)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep (a : R) :
        D (a * t ^ (n + 1)) =
          (D a * t + a * ((n + 1 : ℕ) : R) * D t) * t ^ n := by
      rw [hD, derivative_pow_succ D hD, pow_succ' t n]
      ring
    constructor
    · intro k hk a
      cases k with
      | zero => simp [map_mul, ht]
      | succ k =>
        rw [Function.iterate_succ_apply, hstep]
        exact ih.1 k (Nat.lt_of_succ_lt_succ hk) _
    · intro a
      rw [Function.iterate_succ_apply, hstep, ih.2]
      simp only [map_add, map_mul, ht, mul_zero, zero_add, map_natCast, Nat.factorial_succ,
        Nat.cast_mul, pow_succ]
      ring
end Iterates
theorem tangent_proper {g P : Row 4} {surface : Ideal GeoJets} (hp : surface.IsPrime) {v : ℕ}
    (hg : toGeneric g ∈ surface) (hi : ¬ Invariant g surface) (hv : v < K1.p)
    (hn : NormalForm g P surface v) :
    toGeneric (tangentCut g P v) ∉ surface := by
  classical
  let _ : surface.IsPrime := hp
  let ρ : Row 4 →+* GeoJets ⧸ surface := (Ideal.Quotient.mk surface).comp (MvPolynomial.map genericCoeffs)
  have hρ (x : Row 4) : ρ x = 0 ↔ toGeneric x ∈ surface := Ideal.Quotient.eq_zero_iff_mem
  let D := delta g
  have hD (x y : Row 4) : D (x * y) = D x * y + x * D y := delta_mul g x y
  have hDg : D g = 0 := by
    change flowNumerator g g = 0
    unfold flowNumerator
    ring
  obtain ⟨t, d, u, B, ht, hd, hu, hP, hgen⟩ := hn
  have ht0 := (hρ t).mpr ht
  have hg0 := (hρ g).mpr hg
  have hd0 := fun h => hd ((hρ d).mp h)
  have hu0 := fun h => hu ((hρ u).mp h)
  have hDt : ρ (D t) ≠ 0 := by
    intro htD
    apply hi
    intro a ha
    obtain ⟨e, C, W, he, hEq⟩ := hgen a ha
    have h := congrArg (fun x => ρ (D x)) hEq
    simp only [map_add, hD, map_mul, hDg, hg0, ht0, htD, (hρ a).mpr ha,
      mul_zero, zero_add, add_zero] at h
    exact (hρ _).mp ((mul_eq_zero.mp h).resolve_left (fun h => he ((hρ e).mp h)))
  have iter_g (k : ℕ) : ∀ b : Row 4, ρ ((D^[k]) (b * g)) = 0 := by
    induction k with
    | zero => intro b; simp only [Function.iterate_zero_apply, map_mul, hg0, mul_zero]
    | succ k ih =>
      intro b
      rw [Function.iterate_succ_apply, hD, hDg, mul_zero, add_zero]
      exact ih _
  have iter_eq (k : ℕ) : ρ ((D^[k]) (d * P)) = ρ ((D^[k]) (u * t ^ v)) := by
    have h := congrArg (fun x => ρ ((D^[k]) x)) hP
    simpa only [iterate_map_add D, map_add, iter_g, zero_add] using h
  have hpow := iterate_power_order D ρ hD t ht0 v
  have hlower : ∀ k < v, ρ ((D^[k]) P) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk
      have h := iterate_mul_residue D ρ hD k d P (fun j hj => ih j hj (hj.trans hk))
      rw [iter_eq, hpow.1 k hk u] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hd0
  have htop := iterate_mul_residue D ρ hD v d P hlower
  rw [iter_eq, hpow.2 u] at htop
  let ψ : Geom →+* GeoJets ⧸ surface := ρ.comp (MvPolynomial.C.comp Polynomial.C)
  have hfact : (v.factorial : GeoJets ⧸ surface) ≠ 0 := by
    intro h
    apply K1_13_7_1.factorial_cast_ne_zero hv
    apply ψ.injective
    simpa only [map_natCast, map_zero] using h
  intro hz
  have hzero : ρ ((D^[v]) P) = 0 := (hρ _).mpr hz
  rw [hzero, mul_zero] at htop
  exact (mul_ne_zero (mul_ne_zero hu0 hfact) (pow_ne_zero _ hDt)) htop
end
end K1_13_6_1_3
end
section
namespace K1_13_6_1_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_1
def c1 : Prop :=
  ∀ f P Q surface, IsRelPrime (toGeneric f) (toGeneric P) →
    (intersectionIdeal f Q).IsMinimalPrime surface → toGeneric P ∈ surface →
    ∃ (hZ : (intersectionIdeal f P).IsMinimalPrime surface) (w : ℕ),
      0 < w ∧ w ≤ (shape f).b * (shape P).b ∧
        cycleLength (intersectionIdeal f P) surface hZ.isPrime = (w : ℕ∞)
def c2 : Prop :=
  ∀ g P surface (hZ : (intersectionIdeal g P).IsMinimalPrime surface) (v : ℕ),
    IsRelPrime (toGeneric g) (toGeneric P) → toGeneric (separant g) ∉ surface →
    0 < v → contractedLength g P surface hZ.isPrime = (v : ℕ∞) →
    NormalForm g P surface v
def c3 : Prop :=
  ∀ g P surface (hZ : (intersectionIdeal g P).IsMinimalPrime surface) (v : ℕ),
    cycleLength (intersectionIdeal g P) surface hZ.isPrime = (v : ℕ∞) →
    v < K1.p → contractedLength g P surface hZ.isPrime = (v : ℕ∞)
end
end K1_13_6_1_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_3_3
noncomputable section
open IsLocalRing
abbrev localLength {R : Type*} [CommRing R] (q : Ideal R) [q.IsPrime] (J : Ideal R) : ℕ∞ :=
  Module.length (Localization.AtPrime q)
    (Localization.AtPrime q ⧸ J.map (algebraMap R (Localization.AtPrime q)))
section Length
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsPrime]
theorem localLength_pos {J : Ideal S} (hJ : J ≤ Q) : 0 < localLength Q J := by
  apply Module.length_pos_iff.mpr
  apply Ideal.Quotient.nontrivial_iff.mpr
  exact ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top
    ((Ideal.map_mono hJ).trans_eq Localization.AtPrime.map_eq_maximalIdeal)
theorem localLength_eq_one_iff {J : Ideal S} :
    localLength Q J = 1 ↔
      J.map (algebraMap S (Localization.AtPrime Q)) = maximalIdeal (Localization.AtPrime Q) := by
  rw [localLength, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff]
theorem localLength_mono {I J : Ideal S} (h : I ≤ J) :
    localLength Q J ≤ localLength Q I := by
  simp only [localLength, Module.length_quotient]
  exact Order.coheight_anti (Ideal.map_mono h)
theorem localLength_map [Module.Flat R S] (J : Ideal R) :
    localLength Q (J.map (algebraMap R S)) =
      localLength (Q.comap (algebraMap R S)) J *
        localLength Q ((Q.comap (algebraMap R S)).map (algebraMap R S)) := by
  let q := Q.comap (algebraMap R S)
  let : q.IsPrime := Ideal.comap_isPrime _ _
  let : Q.LiesOver q := ⟨rfl⟩
  let A := Localization.AtPrime q
  let B := Localization.AtPrime Q
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver q Q
  have : IsLocalHom (algebraMap A B) := by
    change IsLocalHom (Localization.localRingHom q Q (algebraMap R S) rfl)
    infer_instance
  have hmap (I : Ideal R) :
      (I.map (algebraMap R A)).map (algebraMap A B) =
        (I.map (algebraMap R S)).map (algebraMap S B) := by
    rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq R A B,
      ← IsScalarTower.algebraMap_eq R S B]
  let I := J.map (algebraMap R A)
  change Module.length B (B ⧸ (J.map (algebraMap R S)).map (algebraMap S B)) =
    Module.length A (A ⧸ I) *
      Module.length B (B ⧸ (q.map (algebraMap R S)).map (algebraMap S B))
  rw [← hmap, ← hmap, Localization.AtPrime.map_eq_maximalIdeal]
  exact ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq).trans
    (IsLocalRing.length_baseChange A B (A ⧸ I))
end Length
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem polynomial_flat {k l σ : Type*} [Field k] [Field l] [Algebra k l] :
    Module.Flat (MvPolynomial σ k) (MvPolynomial σ l) := by
  have h : Algebra.IsPushout k (MvPolynomial σ k) l (MvPolynomial σ l) := inferInstance
  exact Module.Flat.isBaseChange k (MvPolynomial σ k) l (MvPolynomial σ l) h.out
theorem localLength_le_map {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (Q : Ideal S) [Q.IsPrime] (J : Ideal R) :
    localLength (Q.comap (algebraMap R S)) J ≤ localLength Q (J.map (algebraMap R S)) := by
  rw [localLength_map]
  exact ENat.self_le_mul_right _ (localLength_pos Q (Ideal.map_le_iff_le_comap.mpr le_rfl)).ne'
end
end K1_13_6_1_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_3_3
noncomputable section
open IsLocalRing Algebra
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
section FiniteScalarExtension
variable {k l σ : Type*} [Field k] [Field l] [Algebra k l] [FiniteDimensional k l]
variable (Q : Ideal (MvPolynomial σ l)) [Q.IsPrime]
theorem separable_fibre [Algebra.IsSeparable k l] :
    localLength Q ((Q.comap (algebraMap (MvPolynomial σ k) _)).map
      (algebraMap (MvPolynomial σ k) _)) = 1 := by
  let R := MvPolynomial σ k
  let S := MvPolynomial σ l
  let q := Q.comap (algebraMap R S)
  let : q.IsPrime := Ideal.comap_isPrime _ _
  let : Q.LiesOver q := ⟨rfl⟩
  let A := Localization.AtPrime q
  let B := Localization.AtPrime Q
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver q Q
  let : IsLocalHom (algebraMap A B) := by
    change IsLocalHom (Localization.localRingHom q Q (algebraMap R S) rfl)
    infer_instance
  let e := IsPushout.equiv k R l S
  have : Module.Finite R S := Module.Finite.of_surjective e.toLinearMap e.surjective
  have : FormallyUnramified k l := FormallyUnramified.of_isSeparable k l
  have : FormallyUnramified R S := FormallyUnramified.of_equiv e
  have : FormallyUnramified R B := by
    change FormallyUnramified R (Localization Q.primeCompl)
    infer_instance
  have : FormallyUnramified A B := FormallyUnramified.of_restrictScalars R A B
  have : EssFiniteType R B := by
    change EssFiniteType R (Localization Q.primeCompl)
    infer_instance
  have : EssFiniteType A B := EssFiniteType.of_comp R A B
  apply (localLength_eq_one_iff Q).mpr
  change (q.map (algebraMap R S)).map (algebraMap S B) = maximalIdeal B
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S B,
    IsScalarTower.algebraMap_eq R A B, ← Ideal.map_map,
    Localization.AtPrime.map_eq_maximalIdeal]
  exact FormallyUnramified.map_maximalIdeal
end FiniteScalarExtension
private theorem selfLength_congr {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  change Order.coheight (⊥ : Ideal R) = Order.coheight (⊥ : Ideal S)
  simpa using Order.coheight_orderIso e.idealComapOrderIso (⊥ : Ideal S)
section PurelyInseparable
variable {k l F : Type*} [Field k] [Field l] [Field F] [Algebra k l] [Algebra k F]
variable [IsPurelyInseparable k l]
private theorem tensor_selfLength_eq_one [FiniteDimensional k l]
    (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (h : Module.length (F ⊗[k] l) (F ⊗[k] l) < (p : ℕ∞)) :
    Module.length (F ⊗[k] l) (F ⊗[k] l) = 1 := by
  let T := F ⊗[k] l
  have : Subsingleton (PrimeSpectrum T) :=
    (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k l F).injective.subsingleton
  have : Subsingleton (MaximalSpectrum T) := MaximalSpectrum.toPrimeSpectrum_injective.subsingleton
  have : IsLocalRing T := IsLocalRing.of_singleton_maximalSpectrum
  have : IsLocalHom (algebraMap F T) := ⟨fun x hx ↦ isUnit_iff_ne_zero.mpr fun hz ↦
    by simp [hz] at hx⟩
  obtain ⟨a, ha⟩ := IsPurelyInseparable.finrank_eq_pow k l p
  have hd := IsLocalRing.length_restrictScalars F T T
  rw [Module.length_eq_finrank F T, Module.finrank_baseChange, ha] at hd
  have hdvd : (Module.length T T).toNat ∣ p ^ a := by
    refine ⟨(Module.length (ResidueField F) (ResidueField T)).toNat, ?_⟩
    simpa only [ENat.toNat_mul, ENat.toNat_natCast] using congrArg ENat.toNat hd
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  cases n with
  | zero => exact (ENat.toNat_eq_iff (by decide : (1 : ℕ) ≠ 0)).mp (by simpa using hn)
  | succ n =>
    have hle : p ≤ p ^ (n + 1) := Nat.le_pow (Nat.succ_pos n)
    have hlt : (Module.length T T).toNat < p := by
      exact ENat.natCast_lt_natCast.mp ((ENat.natCast_toNat_le_self _).trans_lt h)
    omega
end PurelyInseparable
section PolynomialFibre
variable {k l σ : Type*} [Field k] [Field l] [Algebra k l]
variable [IsPurelyInseparable k l]
variable (q : Ideal (MvPolynomial σ k)) [q.IsPrime]
variable (Q : Ideal (MvPolynomial σ l)) [Q.IsPrime] [Q.LiesOver q]
private abbrev fibreInclusion {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal R) [q.IsPrime] : S →+* q.Fiber S :=
  (Algebra.TensorProduct.includeRight (R := R) (A := q.ResidueField) (B := S)).toRingHom
set_option backward.isDefEq.respectTransparency false in
private theorem fibre_at_length {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal R) [q.IsPrime] (r : Ideal (q.Fiber S)) [r.IsPrime] :
    localLength (r.comap (fibreInclusion (S := S) q)) (q.map (algebraMap R S)) =
      Module.length (Localization.AtPrime r) (Localization.AtPrime r) := by
  let Q := r.comap (fibreInclusion (S := S) q)
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  let B := Localization.AtPrime Q
  let I := (q.map (algebraMap R S)).map (algebraMap S B)
  change Module.length B (B ⧸ I) = _
  have hsurj : Function.Surjective (algebraMap B (B ⧸ I)) :=
    Ideal.Quotient.mk_surjective
  have hquot := Module.length_eq_of_surjective (S := B) (R := B ⧸ I) (M := B ⧸ I) hsurj
  let e : Localization.AtPrime r ≃+* (B ⧸ I) :=
    (Ideal.Fiber.algEquivAux₂ (S := S) q r).toRingEquiv
  have he := selfLength_congr (R := B ⧸ I) (S := Localization.AtPrime r) e.symm
  exact hquot.trans he
set_option backward.isDefEq.respectTransparency false in
private theorem purely_inseparable_fibre_length :
    localLength Q (q.map (algebraMap (MvPolynomial σ k) (MvPolynomial σ l))) =
      Module.length (q.ResidueField ⊗[k] l) (q.ResidueField ⊗[k] l) := by
  let R := MvPolynomial σ k
  let S := MvPolynomial σ l
  let F := q.ResidueField
  let T := F ⊗[k] l
  let e₁ : q.Fiber S ≃ₐ[F] T :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F)
      ((IsPushout.equiv k R l S).symm)).trans
        (Algebra.TensorProduct.cancelBaseChange k R F F l)
  obtain ⟨z, hz⟩ := (PrimeSpectrum.primesOverOrderIsoFiber R S q).symm.surjective
    ⟨Q, inferInstance, inferInstance⟩
  let r := z.asIdeal
  have : r.IsPrime := z.isPrime
  have hQ : r.comap (fibreInclusion (S := S) q) = Q :=
    congrArg (fun w : q.primesOver S ↦ w.1) hz
  have hu : r.primeCompl ≤ IsUnit.submonoid (q.Fiber S) := by
    intro x hx
    obtain ⟨n, hn, y, hy⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct (e₁ x)
    have hxy : x ^ n = algebraMap F (q.Fiber S) y := by
      apply e₁.injective
      rw [map_pow, e₁.commutes, hy]
    have hy0 : y ≠ 0 := by
      intro hz
      apply hx
      exact (‹r.IsPrime›.pow_mem_iff_mem _ hn).mp (by simp [hxy, hz])
    change IsUnit x
    rw [← isUnit_pow_iff hn.ne', hxy]
    exact (isUnit_iff_ne_zero.mpr hy0).map (algebraMap F (q.Fiber S))
  let e₂ := IsLocalization.atUnits (q.Fiber S) r.primeCompl (S := Localization.AtPrime r) hu
  subst Q
  have h₁ := fibre_at_length (R := R) (S := S) q r
  let e : Localization.AtPrime r ≃+* T := e₂.symm.toRingEquiv.trans e₁.toRingEquiv
  have h₂ := selfLength_congr (R := Localization.AtPrime r) (S := T) e
  exact h₁.trans h₂
theorem purely_inseparable_fibre [FiniteDimensional k l] (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (h : localLength Q (q.map (algebraMap (MvPolynomial σ k) _)) < (p : ℕ∞)) :
    localLength Q (q.map (algebraMap (MvPolynomial σ k) _)) = 1 := by
  rw [purely_inseparable_fibre_length q Q] at h ⊢
  exact tensor_selfLength_eq_one p hp h
end PolynomialFibre
end
end K1_13_6_1_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_3_3
noncomputable section
open IsLocalRing
open K1_13 K1_13_6 K1_13_6_1_3
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem polynomial_tower {k E l σ : Type*} [Field k] [Field E] [Field l]
    [Algebra k E] [Algebra k l] [Algebra E l] [IsScalarTower k E l] :
    IsScalarTower (MvPolynomial σ k) (MvPolynomial σ E) (MvPolynomial σ l) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  simp only [MvPolynomial.algebraMap_def]
  change MvPolynomial.map (algebraMap k l) x =
    MvPolynomial.map (algebraMap E l) (MvPolynomial.map (algebraMap k E) x)
  rw [MvPolynomial.map_map, IsScalarTower.algebraMap_eq k E l]
private theorem finite_fibre {k l σ : Type*} [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] (Q : Ideal (MvPolynomial σ l)) [Q.IsPrime]
    (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (h : localLength Q ((Q.comap (algebraMap (MvPolynomial σ k) _)).map
      (algebraMap (MvPolynomial σ k) _)) < (p : ℕ∞)) :
    localLength Q ((Q.comap (algebraMap (MvPolynomial σ k) _)).map
      (algebraMap (MvPolynomial σ k) _)) = 1 := by
  let E := separableClosure k l
  let R := MvPolynomial σ k
  let T := MvPolynomial σ E
  let S := MvPolynomial σ l
  let q := Q.comap (algebraMap T S)
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver q := ⟨rfl⟩
  have : Module.Flat T S := polynomial_flat
  have : IsScalarTower R T S := polynomial_tower
  have hmap : ((q.comap (algebraMap R T)).map (algebraMap R T)).map (algebraMap T S) =
      (Q.comap (algebraMap R S)).map (algebraMap R S) := by
    simp only [q, Ideal.map_map, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R T S]
  rw [← hmap, localLength_map, separable_fibre (k := k) q, one_mul] at h ⊢
  exact purely_inseparable_fibre q Q p hp h
private theorem lift_polynomial {k l σ : Type*} [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] (x : MvPolynomial σ l) :
    ∃ (E : IntermediateField k l), FiniteDimensional k E ∧
      ∃ y : MvPolynomial σ E, algebraMap (MvPolynomial σ E) (MvPolynomial σ l) y = x := by
  classical
  let s := x.support.image x.coeff
  let E := IntermediateField.adjoin k (s : Set l)
  have : FiniteDimensional k E := IntermediateField.finiteDimensional_adjoin
    (fun z _ ↦ Algebra.IsIntegral.isIntegral (R := k) z)
  have hcoeff (m : σ →₀ ℕ) (hm : m ∈ x.support) : x.coeff m ∈ E :=
    IntermediateField.subset_adjoin k _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  let y : MvPolynomial σ E :=
    ∑ m ∈ x.support.attach, MvPolynomial.monomial m.1 ⟨x.coeff m.1, hcoeff m.1 m.2⟩
  refine ⟨E, inferInstance, y, ?_⟩
  simp only [y, map_sum, MvPolynomial.algebraMap_def, MvPolynomial.map_monomial,
    IntermediateField.algebraMap_apply]
  rw [Finset.sum_attach x.support (fun m ↦ MvPolynomial.monomial m (x.coeff m))]
  exact (MvPolynomial.as_sum x).symm
theorem algebraic_fibre {k l σ : Type*} [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] (Q : Ideal (MvPolynomial σ l)) [Q.IsPrime]
    (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (h : localLength Q ((Q.comap (algebraMap (MvPolynomial σ k) _)).map
      (algebraMap (MvPolynomial σ k) _)) < (p : ℕ∞)) :
    localLength Q ((Q.comap (algebraMap (MvPolynomial σ k) _)).map
      (algebraMap (MvPolynomial σ k) _)) = 1 := by
  let R := MvPolynomial σ k
  let S := MvPolynomial σ l
  let J := (Q.comap (algebraMap R S)).map (algebraMap R S)
  let B := Localization.AtPrime Q
  apply (localLength_eq_one_iff Q).mpr
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  change J.map (algebraMap S B) = Q.map (algebraMap S B)
  refine le_antisymm (Ideal.map_mono Ideal.map_comap_le) ?_
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  obtain ⟨E, hE, y, hy⟩ := lift_polynomial (k := k) x
  let T := MvPolynomial σ E
  let q := Q.comap (algebraMap T S)
  let J₀ := (q.comap (algebraMap R T)).map (algebraMap R T)
  let A := Localization.AtPrime q
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver q := ⟨rfl⟩
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver q Q
  have : IsScalarTower R T S := polynomial_tower
  have : Module.Flat T S := polynomial_flat
  have hmap : J₀.map (algebraMap T S) = J := by
    simp only [J₀, J, q, Ideal.map_map, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R T S]
  have h₀ : localLength q J₀ < (p : ℕ∞) := (localLength_le_map Q J₀).trans_lt (hmap ▸ h)
  have h₁ := (localLength_eq_one_iff q).mp (finite_fibre (k := k) q p hp h₀)
  have hyq : y ∈ q := by
    change algebraMap T S y ∈ Q
    exact hy.symm ▸ hx
  have hymem : algebraMap T A y ∈ J₀.map (algebraMap T A) := by
    rw [h₁, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hyq
  have hmem := Ideal.mem_map_of_mem (algebraMap A B) hymem
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq T A B,
    IsScalarTower.algebraMap_eq T S B, ← Ideal.map_map, hmap] at hmem
  change algebraMap S B x ∈ J.map (algebraMap S B)
  rw [← hy]
  change (algebraMap S B) ((algebraMap T S) y) ∈ J.map (algebraMap S B)
  rw [← IsScalarTower.algebraMap_apply T S B]
  rwa [← IsScalarTower.algebraMap_apply T A B] at hmem
theorem proof : K1_13_6_1_3.c3 := by
  intro g P surface hZ v hlen hv
  have : surface.IsPrime := hZ.isPrime
  change localLength surface (intersectionIdeal g P) = (v : ℕ∞) at hlen
  let q := contractedPrime surface
  have : q.IsPrime := Ideal.comap_isPrime _ _
  let J : Ideal RationalJets := Ideal.span {toRational g, toRational P}
  let f := algebraMap RationalJets GeoJets
  have hfg (U : Row 4) : f (toRational U) = toGeneric U := by
    change MvPolynomial.map (algebraMap GenericField GeoField) (toRational U) = _
    simp only [toRational, toGeneric, genericCoeffs, MvPolynomial.map_map]
  have hJ : J.map f = intersectionIdeal g P := by
    simp only [J, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hfg, intersectionIdeal]
  have hsmall : localLength surface (q.map f) < (K1.p : ℕ∞) := by
    have hle : (intersectionIdeal g P) ≤ q.map f := by
      rw [← hJ]
      apply Ideal.map_mono
      exact Ideal.map_le_iff_le_comap.mp (hJ.symm ▸ hZ.le)
    refine (localLength_mono surface hle).trans_lt ?_
    rw [hlen]
    exact ENat.natCast_lt_natCast.mpr hv
  have hp := CharP.char_is_prime_of_two_le K1.K K1.p (by decide)
  have : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  have : CharP (Polynomial Geom) K1.p :=
    charP_of_injective_ringHom Polynomial.C_injective K1.p
  have : CharP GenericField K1.p :=
    charP_of_injective_ringHom (IsFractionRing.injective (K := GenericField) (Polynomial Geom)) K1.p
  have : ExpChar GenericField K1.p := ExpChar.prime hp
  have hfib : localLength surface (q.map f) = 1 :=
    algebraic_fibre (k := GenericField) surface K1.p hp hsmall
  have : Module.Flat RationalJets GeoJets := polynomial_flat
  have hbase := localLength_map surface J
  change localLength surface (J.map f) = localLength q J * localLength surface (q.map f) at hbase
  rw [hJ, hfib, mul_one] at hbase
  change Order.coheight (J.map (algebraMap RationalJets (Localization.AtPrime q))) = _
  simpa only [localLength, Module.length_quotient] using hbase.symm.trans hlen
end
end K1_13_6_1_3_3
end
section
namespace K1_13_6_1_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_3 IsLocalRing
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem toGeneric_eq (a : Row 4) :
    MvPolynomial.map (algebraMap GenericField GeoField) (toRational a) = toGeneric a := by
  rw [toRational, toGeneric, genericCoeffs, MvPolynomial.map_map]
section Chart
variable (surface : Ideal GeoJets) [surface.IsPrime]
private abbrev A := Localization.AtPrime (contractedPrime surface)
private abbrev sourcePrime := (contractedPrime surface).comap (algebraMap (Row 4) RationalJets)
local instance : IsLocalization.AtPrime (A surface) (sourcePrime surface) :=
  IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    ((nonZeroDivisors (Polynomial Geom)).map (MvPolynomial.C (σ := Fin 4))) (A surface)
    (contractedPrime surface)
private abbrev loc := algebraMap (Row 4) (A surface)
private theorem loc_eq_rational (a : Row 4) :
    loc surface a = algebraMap RationalJets (A surface) (toRational a) := rfl
omit [surface.IsPrime] in
private theorem source_mem (a : Row 4) : a ∈ sourcePrime surface ↔ toGeneric a ∈ surface := by
  change (MvPolynomial.map (algebraMap GenericField GeoField) (toRational a) ∈ surface) ↔ _
  rw [toGeneric_eq]
private theorem loc_mem (a : Row 4) : loc surface a ∈ maximalIdeal (A surface) ↔ toGeneric a ∈ surface :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff (A surface) (sourcePrime surface) a).trans (source_mem surface a)
private theorem loc_unit (a : Row 4) : IsUnit (loc surface a) ↔ toGeneric a ∉ surface :=
  (IsLocalization.AtPrime.isUnit_to_map_iff (A surface) (sourcePrime surface) a).trans (not_congr (source_mem surface a))
private theorem loc_numerator (x : A surface) :
    ∃ a d : Row 4, toGeneric d ∉ surface ∧ x * loc surface d = loc surface a := by
  obtain ⟨⟨a, d⟩, h⟩ := IsLocalization.surj (sourcePrime surface).primeCompl x
  exact ⟨a, d, (not_congr (source_mem surface d)).mp d.2, h⟩
private theorem clear_mem {J : Ideal (Row 4)} {a : Row 4} (ha : loc surface a ∈ J.map (loc surface)) :
    ∃ d : Row 4, toGeneric d ∉ surface ∧ d * a ∈ J := by
  obtain ⟨d, hd, hda⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (sourcePrime surface).primeCompl (A surface) J a).mp ha
  exact ⟨d, (not_congr (source_mem surface d)).mp hd, hda⟩
omit [surface.IsPrime] in
private theorem separant_mem_of_sq {a : Row 4} (ha : a ∈ sourcePrime surface ^ 2) :
    separant a ∈ sourcePrime surface := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · rw [separant, MvPolynomial.pderiv_mul]
    exact (sourcePrime surface).add_mem ((sourcePrime surface).mul_mem_left _ hy)
      ((sourcePrime surface).mul_mem_right _ hx)
  · simpa only [separant, map_add] using (sourcePrime surface).add_mem hx hy
private theorem loc_not_sq {g : Row 4} (hg : toGeneric g ∈ surface)
    (hs : toGeneric (separant g) ∉ surface) :
    loc surface g ∉ maximalIdeal (A surface) ^ 2 := by
  intro h
  have hmap : (sourcePrime surface).map (loc surface) = maximalIdeal (A surface) := by
    rw [← IsLocalization.map_under (sourcePrime surface).primeCompl (A surface) (maximalIdeal (A surface)),
      IsLocalization.AtPrime.under_maximalIdeal (A surface) (sourcePrime surface)]
  rw [← hmap, ← Ideal.map_pow] at h
  obtain ⟨d, hd, hdg⟩ := clear_mem surface h
  have hder := separant_mem_of_sq surface hdg
  rw [separant, MvPolynomial.pderiv_mul] at hder
  have hother : MvPolynomial.pderiv 3 d * g ∈ sourcePrime surface :=
    (sourcePrime surface).mul_mem_left _ ((source_mem surface g).mpr hg)
  have hmul := ((sourcePrime surface).add_mem_iff_right hother).mp hder
  have hp : (sourcePrime surface).IsPrime := inferInstance
  exact (hp.mem_or_mem hmul).elim
    (fun h => hd ((source_mem surface d).mp h))
    (fun h => hs ((source_mem surface (separant g)).mp h))
private theorem loc_proper {g P : Row 4} (hg : toGeneric g ∈ surface)
    (hrel : IsRelPrime (toGeneric g) (toGeneric P)) :
    loc surface P ∉ Ideal.span {loc surface g} := by
  intro h
  have hm : (Ideal.span {g}).map (loc surface) = Ideal.span {loc surface g} := by
    rw [Ideal.map_span, Set.image_singleton]
  obtain ⟨d, hd, hdp⟩ := clear_mem surface (hm.symm ▸ h)
  have hdvd := map_dvd (MvPolynomial.map genericCoeffs) (Ideal.mem_span_singleton.mp hdp)
  rw [map_mul] at hdvd
  exact hd (surface.mem_of_dvd (hrel.dvd_of_dvd_mul_right hdvd) hg)
private theorem clear_order {g P : Row 4} {v : ℕ} {t' u' : A surface}
    (ht' : maximalIdeal (A surface) = Ideal.span {loc surface g, t'})
    (hu' : IsUnit u') (hP : loc surface P - u' * t' ^ v ∈ Ideal.span {loc surface g}) :
    NormalForm g P surface v := by
  obtain ⟨t, dt, hdt, ht⟩ := loc_numerator surface t'
  obtain ⟨u, du, hdu, hu⟩ := loc_numerator surface u'
  have ht_mem : t' ∈ maximalIdeal (A surface) := ht'.symm ▸ Ideal.subset_span (by simp)
  have htZ : toGeneric t ∈ surface := (loc_mem surface t).mp
    (ht ▸ (maximalIdeal (A surface)).mul_mem_right _ ht_mem)
  have huZ : toGeneric u ∉ surface := (loc_unit surface u).mp
    (hu ▸ hu'.mul ((loc_unit surface du).mpr hdu))
  let d := du * dt ^ v
  have hd : toGeneric d ∉ surface := (loc_unit surface d).mp (by
    change IsUnit (loc surface (du * dt ^ v))
    rw [map_mul, map_pow]
    exact ((loc_unit surface du).mpr hdu).mul (((loc_unit surface dt).mpr hdt).pow _))
  have hEq : loc surface (d * P - u * t ^ v) = loc surface d * (loc surface P - u' * t' ^ v) := by
    simp only [d, map_sub, map_mul, map_pow, ← ht, ← hu, mul_pow]
    ring
  have hmem : loc surface (d * P - u * t ^ v) ∈ (Ideal.span {g}).map (loc surface) := by
    rw [Ideal.map_span, Set.image_singleton, hEq]
    exact Ideal.mul_mem_left _ _ hP
  obtain ⟨s, hs, hsg⟩ := clear_mem surface hmem
  obtain ⟨B, hB⟩ := Ideal.mem_span_singleton'.mp hsg
  refine ⟨t, s * d, s * u, B, htZ, ?_, ?_, ?_, ?_⟩
  · exact (loc_unit surface _).mp (by rw [map_mul]; exact ((loc_unit surface s).mpr hs).mul ((loc_unit surface d).mpr hd))
  · exact (loc_unit surface _).mp (by rw [map_mul]; exact ((loc_unit surface s).mpr hs).mul ((loc_unit surface u).mpr huZ))
  · calc
      (s * d) * P = s * (d * P - u * t ^ v) + (s * u) * t ^ v := by ring
      _ = B * g + (s * u) * t ^ v := by rw [hB]
  · intro a ha
    have htm : maximalIdeal (A surface) = (Ideal.span {g, t}).map (loc surface) := by
      rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, ← ht, ht']
      simp only [Ideal.span_insert, Ideal.span_singleton_mul_right_unit ((loc_unit surface dt).mpr hdt)]
    obtain ⟨e, he, hea⟩ := clear_mem surface (htm ▸ (loc_mem surface a).mpr ha)
    obtain ⟨C, W, heq⟩ := Ideal.mem_span_pair.mp hea
    exact ⟨e, C, W, he, heq.symm⟩
end Chart
theorem proof : K1_13_6_1_3.c2 := by
  intro g P surface hZ v hrel hsep _ hlen
  have := hZ.isPrime
  have hg : toGeneric g ∈ surface := hZ.le (Ideal.subset_span (by simp))
  have hq : toGeneric P ∈ surface := hZ.le (Ideal.subset_span (by simp))
  have hlen' : Order.coheight (Ideal.span ({loc surface g, loc surface P} : Set (A surface))) = (v : ℕ∞) := by
    unfold contractedLength at hlen
    simpa only [loc_eq_rational, Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using hlen
  have hreg : IsRegularLocalRing (A surface) :=
    IsRegularRing.isRegularLocalRing_localization (contractedPrime surface)
  have hufd : UniqueFactorizationMonoid (A surface) :=
    UniqueFactorizationMonoid.of_isLocalization (contractedPrime surface).primeCompl (A surface)
  have hdom : IsDomain (A surface) := inferInstance
  have hg' := (loc_mem surface g).mpr hg
  have hq' := (loc_mem surface P).mpr hq
  have hgsq := loc_not_sq surface (g := g) hg hsep
  have hqf := loc_proper surface (g := g) (P := P) hg hrel
  obtain ⟨t, u, ht, hu, hP⟩ := @local_order (A surface) inferInstance hdom hreg hufd
    (loc surface g) (loc surface P) v hg' hq' hgsq hqf hlen'
  exact clear_order surface (g := g) (P := P) (v := v) (t' := t) (u' := u) ht hu hP
end
end K1_13_6_1_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_1 K1_13_6_1_3_3
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem proof : K1_13_6_3_1.c1 := by
  intro f Q P hz hlen
  have : P.IsPrime := hz.isPrime
  change localLength P (intersectionIdeal f Q) < (K1.p : ℕ∞) at hlen
  let J : Ideal SepJets := Ideal.span {rowToSep f, rowToSep Q}
  have hJ : J.map sepToGeo = intersectionIdeal f Q := by
    simp only [J, intersectionIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      sepToGeo_rowToSep]
  let const : K1.K →+* SepField :=
    (algebraMap GenericField SepField).comp
      ((algebraMap (Polynomial Geom) GenericField).comp (Polynomial.C.comp embed))
  have : CharP SepField K1.p := charP_of_injective_ringHom const.injective K1.p
  have hp := CharP.char_is_prime_of_two_le K1.K K1.p (by decide)
  have : ExpChar SepField K1.p := .prime hp
  have hle : intersectionIdeal f Q ≤ (P.comap sepToGeo).map sepToGeo := by
    rw [← hJ]
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mp (hJ.symm ▸ hz.le))
  have hsmall : localLength P ((P.comap sepToGeo).map sepToGeo) < (K1.p : ℕ∞) :=
    (localLength_mono P hle).trans_lt hlen
  have hone : localLength P ((P.comap sepToGeo).map sepToGeo) = 1 :=
    algebraic_fibre (k := SepField) P K1.p hp hsmall
  exact descent_of_local_equality (k := SepField) (E := GeoField) (R := SepJets) P
    ((localLength_eq_one_iff P).mp hone)
end
end K1_13_6_3_1_1
end
section
namespace K1_13_6_1_5
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
open scoped BigOperators
def markPoint (S : (Polynomial Geom)) : GeoPoint := fun i => genericCoeffs (jet S i)
theorem markPoint_injective : Function.Injective markPoint := by
  intro S T h
  have hzero := congrFun h (0 : Fin 4)
  simpa only [markPoint, jet, Fin.val_zero, hasseDeriv_zero', genericCoeffs_injective.eq_iff]
    using hzero
theorem coordinate_cut {C : Ideal GeoJets} (hp : C.IsPrime)
    (hdim : ringKrullDim (GeoJets ⧸ C) = 1) :
    ∃ (x : GeoPoint) (D : GeoJets), C ≤ RingHom.ker (MvPolynomial.eval x) ∧
      GeoFits D ⟨1, 3, 1⟩ ∧ D ∉ C ∧ MvPolynomial.eval x D = 0 := by
  classical
  obtain ⟨J, hJ, hCJ⟩ := Ideal.exists_le_maximal C hp.ne_top
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal GeoField hJ
  have hon : C ≤ RingHom.ker (MvPolynomial.eval x) := by
    intro P hP
    have h := hCJ hP
    rw [hx, MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_eq_eval] at h
    exact h
  have hcut : ∃ i : Fin 4, MvPolynomial.X i - MvPolynomial.C (x i) ∉ C := by
    by_contra! hall
    let q := Ideal.Quotient.mk C
    have hq : q = q.comp (MvPolynomial.C.comp (MvPolynomial.eval x)) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp
      · intro i
        simp only [RingHom.comp_apply, MvPolynomial.eval_X]
        exact sub_eq_zero.mp (by
          rw [← map_sub]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (hall i))
    have hsurj : Function.Surjective (q.comp MvPolynomial.C) := by
      intro b
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact ⟨MvPolynomial.eval x P, (RingHom.congr_fun hq P).symm⟩
    have hle := ringKrullDim_le_of_surjective _ hsurj
    rw [hdim, ringKrullDim_eq_zero_of_field] at hle
    exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hle
  obtain ⟨i, hi⟩ := hcut
  let D : GeoJets := MvPolynomial.X i - MvPolynomial.C (x i)
  refine ⟨x, D, hon, ⟨?_, ?_, ?_⟩, hi, by simp [D]⟩
  · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  · apply MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sub_mem
    · exact MvPolynomial.X_mem_restrictWeightedDegree _ _ _ (Nat.le_of_lt_succ i.isLt)
    · exact MvPolynomial.C_mem_restrictWeightedDegree _ _ _
  · apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
    simp only [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_C, max_zero]
    split <;> decide
end
end K1_13_6_1_5
end
section
namespace K1_13_6_1_5
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_1 K1_13_7 K1_13_7_1
def c2 : Prop :=
  ∀ (C : Ideal GeoJets) (p : Shape), C.IsPrime → ringKrullDim (GeoJets ⧸ C) = 1 →
    InBox ⟨1, 3, 1⟩ p →
    ∀ (D : GeoJets), GeoFits D p → D ∉ C →
      ∀ points : Finset GeoPoint,
        (∀ x ∈ points, C ≤ RingHom.ker (MvPolynomial.eval x) ∧ MvPolynomial.eval x D = 0) →
        6 * points.card ≤ sectionDegree C (p.scale 6)
end
end K1_13_6_1_5
end
section
set_option autoImplicit false
namespace K1_13_6_1_5_2
open K1_13 K1_13_6 K1_13_6_1
abbrev CutQuotient (C : Ideal GeoJets) (E : GeoJets) :=
  GeoJets ⧸ (C ⊔ Ideal.span {E})
abbrev GenericQuotient (C : Ideal GeoJets) (a : Shape) :=
  SectionJets a ⧸
    (C.map (MvPolynomial.map (algebraMap GeoField (SectionField a))) ⊔
      Ideal.span {genericSection a})
noncomputable def boxSection (a : Shape) (c : SectionIndex a → GeoField) : GeoJets :=
  ∑ m ∈ boxMonomials a, MvPolynomial.C (c m) * ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
end K1_13_6_1_5_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_5_2
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1 MvPolynomial
theorem fits_pow {D : GeoJets} {p : Shape} (hD : GeoFits D p) (n : ℕ) :
    GeoFits (D ^ n) (p.scale n) :=
  ⟨(totalDegree_pow D n).trans (Nat.mul_le_mul_left n hD.1),
    (weightedTotalDegree_pow_le _ D n).trans (Nat.mul_le_mul_left n hD.2.1),
    (degreeOf_pow_le _ D n).trans (Nat.mul_le_mul_left n hD.2.2)⟩
private noncomputable def exponent (a : Shape) : SectionIndex a ↪ (Fin 4 →₀ ℕ) where
  toFun m := Finsupp.equivFunOnFinite.symm fun i => (m i).val
  inj' := by
    intro x y h
    funext i
    apply Fin.ext
    exact DFunLike.congr_fun h i
theorem exists_boxSection {E : GeoJets} {a : Shape} (hE : GeoFits E a) :
    ∃ c : SectionIndex a → GeoField, boxSection a c = E := by
  classical
  refine ⟨fun m => E.coeff (exponent a m), ?_⟩
  have hexp (m : SectionIndex a) (i : Fin 4) : exponent a m i = (m i).val := rfl
  have hsupport : E.support ⊆ (boxMonomials a).map (exponent a) := by
    intro s hs
    have hb : (∑ i : Fin 4, s i) ≤ a.b := by
      simpa [Finsupp.sum_fintype] using (le_totalDegree hs).trans hE.1
    have hj : (∑ i : Fin 4, i.val * s i) ≤ a.j := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, nsmul_eq_mul, Nat.mul_comm] using
        (le_weightedTotalDegree Fin.val hs).trans hE.2.1
    have ht : s 3 ≤ a.t := (monomial_le_degreeOf 3 hs).trans hE.2.2
    let m : SectionIndex a := fun i =>
      ⟨s i, Nat.lt_succ_of_le ((Finset.single_le_sum
        (f := fun j : Fin 4 => s j) (fun j _ => Nat.zero_le (s j)) (Finset.mem_univ i)).trans hb)⟩
    refine Finset.mem_map.mpr ⟨m, ?_, Finsupp.ext fun _ => rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ m, hb, hj, ht⟩
  have hsum := Finset.sum_subset (f := fun s => monomial s (E.coeff s)) hsupport (by
    intro s _ hs
    rw [notMem_support_iff.mp hs, map_zero])
  rw [Finset.sum_map] at hsum
  calc
    boxSection a (fun m => E.coeff (exponent a m)) =
        ∑ m ∈ boxMonomials a, monomial (exponent a m) (E.coeff (exponent a m)) := by
      unfold boxSection
      apply Finset.sum_congr rfl
      intro m _
      rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp only [hexp]
    _ = E := hsum.symm.trans E.as_sum.symm
theorem cut_finite {C : Ideal GeoJets} [C.IsPrime]
    (hdim : ringKrullDim (GeoJets ⧸ C) = 1) {E : GeoJets} (hE : E ∉ C) :
    Module.Finite GeoField (CutQuotient C E) := by
  have hlt : C < C ⊔ Ideal.span {E} := by
    apply lt_of_le_of_ne le_sup_left
    intro h
    exact hE (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self E) :
      E ∈ C)
  have hd := Ideal.ringKrullDim_quotient_succ_le_of_lt hlt
  rw [hdim] at hd
  apply (Module.finite_iff_krullDimLE_zero GeoField _).mpr
  apply Ring.krullDimLE_iff.mpr
  exact ENat.WithBot.add_le_add_one_right_iff.mp (by simpa using hd)
theorem pow_not_mem {C : Ideal GeoJets} [C.IsPrime] {D : GeoJets} (hD : D ∉ C) (n : ℕ) :
    D ^ n ∉ C := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
  exact pow_ne_zero n (mt Ideal.Quotient.eq_zero_iff_mem.mp hD)
private theorem power_colon {C : Ideal GeoJets} [C.IsPrime] {D : GeoJets} (hD : D ∉ C)
    (n : ℕ) : (C ⊔ Ideal.span {D ^ (n + 1)}).colon {D} = C ⊔ Ideal.span {D ^ n} := by
  ext x
  let q := Ideal.Quotient.mk C
  have hqD : q D ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hD
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  constructor
  · intro hx
    obtain ⟨c, hc, y, hy, hsum⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hy
    have heq : q D * q x = q D * (q (D ^ n) * q r) := by
      have h := congrArg q hsum
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hc, zero_add, pow_succ,
        map_mul, map_mul, map_mul] at h
      linear_combination -h
    have hdiff : x - D ^ n * r ∈ C := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_mul, mul_left_cancel₀ hqD heq, sub_self]
    apply Submodule.mem_sup.mpr
    refine ⟨x - D ^ n * r, hdiff, D ^ n * r, Ideal.mem_span_singleton.mpr ⟨r, rfl⟩, ?_⟩
    exact sub_add_cancel _ _
  · intro hx
    obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hy
    rw [add_mul]
    apply Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right D C hc))
    apply Ideal.mem_sup_right
    exact Ideal.mem_span_singleton.mpr ⟨r, by rw [pow_succ]; ac_rfl⟩
private theorem sup_pow_succ {C : Ideal GeoJets} (D : GeoJets) (n : ℕ) :
    (C ⊔ Ideal.span {D ^ (n + 1)}) ⊔ Ideal.span {D} = C ⊔ Ideal.span {D} := by
  have hpow : (Ideal.span {D ^ (n + 1)} : Ideal GeoJets) ≤ Ideal.span {D} :=
    (Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_span_singleton.mpr ⟨D ^ n, by rw [pow_succ, mul_comm]⟩)
  rw [sup_assoc, sup_eq_right.mpr hpow]
set_option maxHeartbeats 800000 in
theorem finrank_power {C : Ideal GeoJets} [C.IsPrime] {D : GeoJets}
    (hdim : ringKrullDim (GeoJets ⧸ C) = 1) (hD : D ∉ C) (n : ℕ) :
    Module.finrank GeoField (CutQuotient C (D ^ n)) =
      n * Module.finrank GeoField (CutQuotient C D) := by
  induction n with
  | zero =>
    let : Subsingleton (CutQuotient C (D ^ 0)) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.span_singleton_one, sup_top_eq])
    simpa only [Nat.zero_mul] using
      (Module.finrank_zero_of_subsingleton : Module.finrank GeoField (CutQuotient C (D ^ 0)) = 0)
  | succ n ih =>
    let I : Ideal GeoJets := C ⊔ Ideal.span {D ^ (n + 1)}
    let J := I ⊔ Ideal.span {D}
    let : Module.Finite GeoField (GeoJets ⧸ I) := cut_finite hdim (pow_not_mem hD _)
    let q := (Submodule.factor (le_sup_left : I ≤ J)).restrictScalars GeoField
    let m := (K1_13_6_3_6.quotientMul I D).restrictScalars GeoField
    have hex : Function.Exact m q := K1_13_6_3_6.quotientMul_exact I D
    have he := (LinearMap.exact_iff.mp hex).symm
    have hr := q.finrank_range_add_finrank_ker
    have hq : Function.Surjective q := Submodule.factor_surjective (le_sup_left : I ≤ J)
    have hm : Function.Injective m := K1_13_6_3_6.quotientMul_injective I D
    rw [LinearMap.range_eq_top.mpr hq, finrank_top, ← he,
      ← (LinearEquiv.ofInjective m hm).finrank_eq] at hr
    change Module.finrank GeoField (GeoJets ⧸ ((C ⊔ Ideal.span {D ^ (n + 1)}) ⊔ Ideal.span {D})) +
      Module.finrank GeoField (GeoJets ⧸ (C ⊔ Ideal.span {D ^ (n + 1)}).colon {D}) =
      Module.finrank GeoField (CutQuotient C (D ^ (n + 1))) at hr
    rw [sup_pow_succ, power_colon hD] at hr
    change Module.finrank GeoField (CutQuotient C D) +
      Module.finrank GeoField (CutQuotient C (D ^ n)) = _ at hr
    rw [ih, add_comm, ← Nat.succ_mul] at hr
    exact hr.symm
theorem card_le_finrank {C : Ideal GeoJets} {D : GeoJets}
    [Module.Finite GeoField (CutQuotient C D)] (points : Finset GeoPoint)
    (hp : ∀ x ∈ points, C ≤ RingHom.ker (MvPolynomial.eval x) ∧ MvPolynomial.eval x D = 0) :
    points.card ≤ Module.finrank GeoField (CutQuotient C D) := by
  let I : Ideal GeoJets := C ⊔ Ideal.span {D}
  have hz : (points : Set GeoPoint) ⊆ zeroLocus GeoField I := by
    intro x hx
    have hx' := hp x hx
    have hI : I ≤ RingHom.ker (MvPolynomial.eval x) :=
      sup_le hx'.1 ((Ideal.span_singleton_le_iff_mem _).mpr hx'.2)
    intro E hE
    change MvPolynomial.eval x E = 0
    exact hI hE
  have hf : (zeroLocus GeoField I).Finite := finite_zeroLocus_of_finite_quotient I
  have hcard := Set.ncard_le_ncard hz hf
  rw [Set.ncard_coe_finset] at hcard
  exact hcard.trans (ncard_zeroLocus_le_finrank_quotient I)
end K1_13_6_1_5_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_5_2
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
def c1 : Prop :=
  ∀ (C : Ideal GeoJets) (a : Shape), C.IsPrime → ringKrullDim (GeoJets ⧸ C) = 1 →
    Module.Finite (SectionField a) (GenericQuotient C a)
def c2 : Prop :=
  ∀ (C : Ideal GeoJets) (a : Shape), C.IsPrime → ringKrullDim (GeoJets ⧸ C) = 1 →
    Module.Finite (SectionField a) (GenericQuotient C a) →
    ∀ c : SectionIndex a → GeoField, boxSection a c ∉ C →
      Module.Finite GeoField (CutQuotient C (boxSection a c)) →
      Module.finrank GeoField (CutQuotient C (boxSection a c)) ≤ sectionDegree C a
theorem of_children (h₁ : c1) (h₂ : c2) : K1_13_6_1_5.c2 := by
  intro C p hC hdim _ D hD hproper points hpoints
  let : C.IsPrime := hC
  let : Module.Finite GeoField (CutQuotient C D) := cut_finite hdim hproper
  obtain ⟨c, hc⟩ := exists_boxSection (fits_pow hD 6)
  have hne : boxSection (p.scale 6) c ∉ C := hc ▸ pow_not_mem hproper 6
  have hlength := h₂ C (p.scale 6) hC hdim (h₁ C (p.scale 6) hC hdim) c hne
    (cut_finite hdim hne)
  rw [hc, finrank_power hdim hproper] at hlength
  exact (Nat.mul_le_mul_left 6 (card_le_finrank points hpoints)).trans hlength
end K1_13_6_1_5_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_5_2_2
open MvPolynomial
theorem coefficients_eq_zero
    {k A D σ ι : Type*} [Field k] [CommRing A] [IsDomain A] [CommRing D]
    [Algebra k A] [Algebra k D] [Fintype ι]
    (q : A →ₐ[k] D) (v : ι → A) (hv : LinearIndependent k (q ∘ v))
    (r : ι → MvPolynomial σ k) (H Q : MvPolynomial σ A)
    (hne : constantCoeff H ≠ 0) (hq : q (constantCoeff H) = 0)
    (he : (∑ i, C (v i) * MvPolynomial.map (algebraMap k A) (r i)) = H * Q) :
    ∀ i, r i = 0 := by
  classical
  have h (n : ℕ) : ∀ m : σ →₀ ℕ, m.degree = n → Q.coeff m = 0 ∧ ∀ i, (r i).coeff m = 0 := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro m hm
      have hprod : (H * Q).coeff m = constantCoeff H * Q.coeff m := by
        rw [coeff_mul, Finset.sum_eq_single (0, m)]
        · rfl
        · intro p hp hne'
          have hadd := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          have hp₁ : p.1 ≠ 0 := by
            intro hz
            apply hne'
            exact Prod.ext hz (by simpa [hz] using hadd)
          have hdeg₁ : 0 < p.1.degree :=
            Nat.pos_of_ne_zero (fun hd => hp₁ ((Finsupp.degree_eq_zero_iff _).mp hd))
          have hdegs : p.1.degree + p.2.degree = n := by
            rw [← map_add, hadd, hm]
          rw [(ih p.2.degree (by omega) p.2 rfl).1, mul_zero]
        · exact fun hmiss => (hmiss (Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add m))).elim
      have hc := congrArg (fun P : MvPolynomial σ A => P.coeff m) he
      simp only [coeff_sum, coeff_C_mul, coeff_map, hprod] at hc
      have hrel : ∑ i, (r i).coeff m • (q ∘ v) i = 0 := by
        simpa only [map_sum, map_mul, AlgHom.commutes, hq, zero_mul, Function.comp_apply,
          Algebra.smul_def, mul_comm] using congrArg q hc
      have hzero := Fintype.linearIndependent_iff.mp hv _ hrel
      simp only [hzero, map_zero, mul_zero, Finset.sum_const_zero] at hc
      exact ⟨(mul_eq_zero.mp hc.symm).resolve_left hne, hzero⟩
  intro i
  ext m
  exact (h m.degree m rfl).2 i
end K1_13_6_1_5_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_5_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_5_2 MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private def translate {σ k : Type*} [CommRing k] (c : σ → k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval (fun i => MvPolynomial.X i + C (c i))
private theorem translate_injective {σ k : Type*} [CommRing k] (c : σ → k) :
    Function.Injective (translate c) := by
  have h : (translate (fun i => -c i)).comp (translate c) = AlgHom.id k _ := by
    ext i : 1
    simp [translate, MvPolynomial.algebraMap_eq, add_assoc]
  have hinv : Function.LeftInverse (translate (fun i => -c i)) (translate c) :=
    fun p => AlgHom.congr_fun h p
  exact hinv.injective
private theorem lift_independence
    (C₀ : Ideal GeoJets) [C₀.IsPrime] (a : Shape) (c : SectionIndex a → GeoField)
    (hproper : boxSection a c ∉ C₀)
    {ι : Type} [Fintype ι] (v : ι → GeoJets)
    (hv : LinearIndependent GeoField
      (fun i => Ideal.Quotient.mk (C₀ ⊔ Ideal.span {boxSection a c}) (v i))) :
    LinearIndependent (SectionField a) (fun i =>
      (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap GeoField (SectionField a)) (v i))
        : GenericQuotient C₀ a)) := by
  classical
  let k := GeoField
  let R := MvPolynomial (SectionIndex a) k
  let F := SectionField a
  let B := MvPolynomial (Fin 4) R
  let L := SectionJets a
  let j : GeoJets →+* B := MvPolynomial.map (algebraMap k R)
  let H₀ : B := ∑ m ∈ boxMonomials a,
    C (MvPolynomial.X m) * ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
  let I := C₀.map j ⊔ Ideal.span {H₀}
  let J : Ideal L := C₀.map (MvPolynomial.map (algebraMap k F)) ⊔ Ideal.span {genericSection a}
  let M : Submonoid B := (nonZeroDivisors R).map MvPolynomial.C
  have : IsLocalization M L := MvPolynomial.isLocalization (nonZeroDivisors R) F
  have hC (z : R) : algebraMap B L (C z) = C (algebraMap R F z) := by
    rw [MvPolynomial.algebraMap_def, map_C]
  have hX (i : Fin 4) : algebraMap B L (MvPolynomial.X i) = MvPolynomial.X i := by
    rw [MvPolynomial.algebraMap_def, map_X]
  have hj (p : GeoJets) : algebraMap B L (j p) =
      MvPolynomial.map (algebraMap k F) p := by
    rw [MvPolynomial.algebraMap_def]
    change MvPolynomial.map (algebraMap R F) (MvPolynomial.map (algebraMap k R) p) = _
    rw [MvPolynomial.map_map]
    rfl
  have hH : algebraMap B L H₀ = genericSection a := by
    simp only [H₀, genericSection, map_sum, map_mul, map_prod, map_pow, hC, hX]
    rfl
  have hJ : I.map (algebraMap B L) = J := by
    simp only [I, J, Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton, hH]
    rw [show (algebraMap B L).comp j = MvPolynomial.map (algebraMap k F) from RingHom.ext hj]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  change ∑ i, g i • Ideal.Quotient.mk J (MvPolynomial.map (algebraMap k F) (v i)) = 0 at hg
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) g
  choose r hr using hd
  have hr' (i : ι) : algebraMap R F (r i) = algebraMap R F (d : R) * g i := by
    simpa only [Algebra.smul_def] using hr i
  have hsum : (∑ i, C (g i) * MvPolynomial.map (algebraMap k F) (v i)) ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hscalar (x : SectionField a) :
        algebraMap (SectionField a) (L ⧸ J) x = Ideal.Quotient.mk J (C x) := rfl
    simpa only [map_sum, map_mul, Algebra.smul_def, hscalar] using hg
  have hclear : algebraMap B L (∑ i, C (r i) * j (v i)) ∈ I.map (algebraMap B L) := by
    rw [hJ]
    convert J.mul_mem_left (C (algebraMap R F (d : R))) hsum using 1
    simp only [map_sum, map_mul, hC, hj, hr', Finset.mul_sum, mul_assoc]
  obtain ⟨s, hs, hmem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M L I _).mp hclear
  obtain ⟨d', hd', rfl⟩ := Submonoid.mem_map.mp hs
  let A := GeoJets ⧸ C₀
  let q₀ := Ideal.Quotient.mk C₀
  let t := translate c
  let f₀ : R →+* MvPolynomial (SectionIndex a) A :=
    (MvPolynomial.map (algebraMap k A)).comp t.toRingHom
  let fX : Fin 4 → MvPolynomial (SectionIndex a) A :=
    fun i => C (q₀ (MvPolynomial.X i))
  let f : B →+* MvPolynomial (SectionIndex a) A :=
    eval₂Hom f₀ fX
  have hfC (p : R) : f (C p) = MvPolynomial.map (algebraMap k A) (t p) :=
    eval₂Hom_C f₀ fX p
  have hfX (i : Fin 4) : f (MvPolynomial.X i) = C (q₀ (MvPolynomial.X i)) :=
    eval₂Hom_X' f₀ fX i
  have hfj (p : GeoJets) : f (j p) = C (q₀ p) := by
    have he : f.comp j = MvPolynomial.C.comp q₀ := by
      apply MvPolynomial.ringHom_ext
      · intro z
        change f (MvPolynomial.map (algebraMap k R) (C z)) = C (q₀ (C z))
        rw [map_C, hfC, t.commutes]
        change MvPolynomial.map (algebraMap k A) (C z) = _
        rw [map_C]
        rfl
      · intro i
        change f (MvPolynomial.map (algebraMap k R) (MvPolynomial.X i)) = C (q₀ (MvPolynomial.X i))
        rw [map_X, hfX]
    exact DFunLike.congr_fun he p
  have hcut : constantCoeff (f H₀) = q₀ (boxSection a c) := by
    have htX (m : SectionIndex a) : t (MvPolynomial.X m) = MvPolynomial.X m + C (c m) :=
      aeval_X _ _
    simp only [H₀, boxSection, map_sum, map_mul, map_prod, map_pow,
      hfC, hfX, htX, map_add, map_X, map_C,
      constantCoeff_X, constantCoeff_C, zero_add, q₀]
    rfl
  have hI : I ≤ (Ideal.span {f H₀}).comap f := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      change f (j p) ∈ (Ideal.span {f H₀} : Ideal _)
      rw [hfj, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
      exact Ideal.zero_mem _
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact Ideal.mem_span_singleton_self _
  have hmultiple : f (C d' * ∑ i, C (r i) * j (v i)) ∈ (Ideal.span {f H₀} : Ideal _) :=
    hI hmem
  obtain ⟨Q, hQ⟩ := Ideal.mem_span_singleton.mp hmultiple
  let q : A →ₐ[k] CutQuotient C₀ (boxSection a c) :=
    Ideal.Quotient.factorₐ k (le_sup_left : C₀ ≤ C₀ ⊔ Ideal.span {boxSection a c})
  have he : (∑ i, C (q₀ (v i)) * MvPolynomial.map (algebraMap k A) (t (d' * r i))) =
      f H₀ * Q := by
    calc
      _ = f (C d' * ∑ i, C (r i) * j (v i)) := by
        simp only [map_mul, map_sum, hfC, hfj, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ac_rfl)
      _ = _ := hQ
  have hE : q (constantCoeff (f H₀)) = 0 := by
    rw [hcut]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hz := coefficients_eq_zero q (fun i => q₀ (v i)) hv
    (fun i => t (d' * r i)) (f H₀) Q (by rw [hcut]; exact mt Ideal.Quotient.eq_zero_iff_mem.mp hproper)
    hE he
  have hd'₀ : d' ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd'
  have hd₀ : algebraMap R F (d : R) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective R F).ne (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
  intro i
  have hdi : d' * r i = 0 := translate_injective c ((hz i).trans (map_zero t).symm)
  have hri := (mul_eq_zero.mp hdi).resolve_left hd'₀
  exact (mul_eq_zero.mp ((hr' i).symm.trans (by rw [hri, map_zero]))).resolve_left hd₀
theorem proof : K1_13_6_1_5_2.c2 := by
  classical
  intro C₀ a hprime _ hgeneric c hproper hfinite
  let : C₀.IsPrime := hprime
  let : Module.Finite (SectionField a) (GenericQuotient C₀ a) := hgeneric
  let : Module.Finite GeoField (CutQuotient C₀ (boxSection a c)) := hfinite
  let b := Module.finBasis GeoField (CutQuotient C₀ (boxSection a c))
  choose v hv using fun i => Ideal.Quotient.mk_surjective (b i)
  have hli := lift_independence C₀ a c hproper v
    (show LinearIndependent GeoField
      (fun i => Ideal.Quotient.mk (C₀ ⊔ Ideal.span {boxSection a c}) (v i)) by
      simpa only [hv] using b.linearIndependent)
  change _ ≤ Module.finrank (SectionField a) (GenericQuotient C₀ a)
  simpa only [Fintype.card_fin] using hli.fintype_card_le_finrank
end
end K1_13_6_1_5_2_2
end
section
namespace K1_13_6_1_4_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4_2 MvPolynomial
def combinedShape (a b h : Shape) (t : Fin 3 → ℕ) : Shape :=
  ((a.scale (t 0)).plus (b.scale (t 1))).plus (h.scale (t 2))
def boxHilbert (surface : Ideal GeoJets) (p : Shape) : ℕ :=
  Module.finrank GeoField
    ((restrictSupport GeoField (latticeIndices p)).map
      (Ideal.Quotient.mkₐ GeoField surface).toLinearMap)
def multiHilbert (surface : Ideal GeoJets) (a b h : Shape) (t : Fin 3 → ℕ) : ℕ :=
  boxHilbert surface (combinedShape a b h t)
abbrev SectionVariable (a b h : Shape) :=
  Σ l : Fin 3, latticeIndices (![a, b, h] l)
def blockDegree {σ : Type} (block : σ → Fin 3) (e : σ →₀ ℕ) : Fin 3 → ℕ :=
  fun l => e.sum fun v n => if block v = l then n else 0
def standardCount {σ : Type} (block : σ → Fin 3) (forbidden : Finset (σ →₀ ℕ))
    (t : Fin 3 → ℕ) : ℕ :=
  ({e | blockDegree block e = t ∧ ∀ f ∈ forbidden, ¬ f ≤ e} : Set (σ →₀ ℕ)).ncard
end
end K1_13_6_1_4_2_2
end
section
namespace K1_13_6_1_4_2_2
noncomputable section
open MvPolynomial
open scoped BigOperators
def rayPolynomial (P : MvPolynomial (Fin 3) ℚ) (t : Fin 3 → ℕ) (pad : ℕ) : Polynomial ℚ :=
  P.eval₂ Polynomial.C fun l => Polynomial.C (pad : ℚ) + Polynomial.C (t l : ℚ) * Polynomial.X
theorem eval_rayPolynomial (P : MvPolynomial (Fin 3) ℚ) (t : Fin 3 → ℕ) (pad n : ℕ) :
    (rayPolynomial P t pad).eval (n : ℚ) =
      MvPolynomial.eval (fun l => ((n * t l + pad : ℕ) : ℚ)) P := by
  let f := Polynomial.evalRingHom (n : ℚ)
  have hf : f.comp Polynomial.C = RingHom.id ℚ := by ext r; simp [f]
  change f (rayPolynomial P t pad) = _
  rw [rayPolynomial, MvPolynomial.eval₂_comp_left, hf, MvPolynomial.eval₂_id]
  apply congrArg (fun x => MvPolynomial.eval x P)
  funext l
  simp [f, Function.comp_apply, Nat.cast_add, Nat.cast_mul, add_comm, mul_comm]
private theorem product_degree_and_coeff {α : Type} (s : Finset α)
    (q : α → Polynomial ℚ) (d : α → ℕ) (hq : ∀ i ∈ s, (q i).natDegree ≤ d i) :
    (∏ i ∈ s, q i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, q i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (q i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hi' := hq i (Finset.mem_insert_self i s)
    obtain ⟨hd, hc⟩ := ih fun j hj => hq j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le hi' hd, hc]
    exact ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add hi' hd), rfl⟩
private theorem monomial_ray (e : Fin 3 →₀ ℕ) (r : ℚ) (t : Fin 3 → ℕ) (pad : ℕ) :
    (rayPolynomial (monomial e r) t pad).natDegree ≤ e.degree ∧
      (rayPolynomial (monomial e r) t pad).coeff e.degree =
        MvPolynomial.eval (fun i => (t i : ℚ)) (monomial e r) := by
  let f (i : Fin 3) := Polynomial.C (pad : ℚ) + Polynomial.C (t i : ℚ) * Polynomial.X
  have hf (i : Fin 3) : (f i).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  have hc (i : Fin 3) : (f i).coeff 1 = (t i : ℚ) := by
    simp [f]
  have hp (i : Fin 3) : ((f i) ^ e i).natDegree ≤ e i := by
    simpa using Polynomial.natDegree_pow_le_of_le (e i) (hf i)
  have hpc (i : Fin 3) : ((f i) ^ e i).coeff (e i) = (t i : ℚ) ^ e i := by
    simpa [hc] using
      (Polynomial.coeff_pow_of_natDegree_le (m := e i) (hf i))
  obtain ⟨hd, hcoeff⟩ := product_degree_and_coeff e.support (fun i => (f i) ^ e i) e
    (fun i _ => hp i)
  rw [rayPolynomial, MvPolynomial.eval₂_monomial, MvPolynomial.eval_monomial]
  change (Polynomial.C r * ∏ i ∈ e.support, (f i) ^ e i).natDegree ≤ _ ∧
    (Polynomial.C r * ∏ i ∈ e.support, (f i) ^ e i).coeff
      (∑ i ∈ e.support, e i) = r * ∏ i ∈ e.support, (t i : ℚ) ^ e i
  exact ⟨(Polynomial.natDegree_C_mul_le _ _).trans hd, by
    rw [Polynomial.coeff_C_mul, hcoeff]
    simp only [hpc]⟩
private theorem ray_as_sum (P : MvPolynomial (Fin 3) ℚ) (t : Fin 3 → ℕ) (pad : ℕ) :
    rayPolynomial P t pad = ∑ e ∈ P.support, rayPolynomial (monomial e (P.coeff e)) t pad := by
  unfold rayPolynomial
  simp only [← MvPolynomial.coe_eval₂Hom]
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
theorem degree_ray_le (P : MvPolynomial (Fin 3) ℚ) (t : Fin 3 → ℕ) (pad : ℕ) :
    (rayPolynomial P t pad).natDegree ≤ P.totalDegree := by
  rw [ray_as_sum]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun e he =>
    (monomial_ray e (P.coeff e) t pad).1.trans (le_totalDegree he)
theorem coeff_ray (P : MvPolynomial (Fin 3) ℚ) (t : Fin 3 → ℕ) (pad : ℕ) {d : ℕ}
    (hd : P.totalDegree ≤ d) :
    (rayPolynomial P t pad).coeff d =
      MvPolynomial.eval (fun i => (t i : ℚ)) (homogeneousComponent d P) := by
  classical
  rw [ray_as_sum, Polynomial.finsetSum_coeff, homogeneousComponent_apply, map_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨hdeg, hcoeff⟩ := monomial_ray e (P.coeff e) t pad
  by_cases hed : e.degree = d
  · simpa [hed] using hcoeff
  · simp only [hed, ↓reduceIte]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (hdeg.trans_lt (lt_of_le_of_ne ((le_totalDegree he).trans hd) hed))
private theorem eq_zero_of_eval_pos_nat (P : MvPolynomial (Fin 3) ℚ)
    (hp : ∀ t : Fin 3 → ℕ, (∀ i, 0 < t i) →
      MvPolynomial.eval (fun i => (t i : ℚ)) P = 0) : P = 0 := by
  let f : ℕ ↪ ℚ := ⟨fun n => ((n + 1 : ℕ) : ℚ), by
    intro a b hab
    exact Nat.add_right_cancel (Nat.cast_injective (R := ℚ) hab)⟩
  let s := (Finset.range (P.totalDegree + 1)).map f
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P (fun _ => s)
  · intro i
    simpa [s] using Nat.lt_succ_of_le (degreeOf_le_totalDegree P i)
  · intro x hx
    have hx' (i : Fin 3) : ∃ n : ℕ, n ∈ Finset.range (P.totalDegree + 1) ∧ f n = x i :=
      Finset.mem_map.mp (hx i)
    choose t _ ht using hx'
    have hcast : (fun i => (((t i + 1 : ℕ) : ℚ))) = x := funext ht
    rw [← hcast]
    exact hp (fun i => t i + 1) (fun _ => Nat.succ_pos _)
theorem degree_le_of_positive_rays (P : MvPolynomial (Fin 3) ℚ) (d : ℕ)
    (h : ∀ t : Fin 3 → ℕ, (∀ i, 0 < t i) → (rayPolynomial P t 0).natDegree ≤ d) :
    P.totalDegree ≤ d := by
  by_contra! hlt
  have hzero : homogeneousComponent P.totalDegree P = 0 := by
    apply eq_zero_of_eval_pos_nat
    intro t ht
    rw [← coeff_ray P t 0 le_rfl]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((h t ht).trans_lt hlt)
  have hsmall : P.totalDegree ≤ P.totalDegree - 1 := by
    apply Finset.sup_le
    intro e he
    change e.degree ≤ P.totalDegree - 1
    have hed : e.degree ≤ P.totalDegree := le_totalDegree he
    suffices e.degree ≠ P.totalDegree by omega
    intro heq
    have hz := congrArg (fun Q : MvPolynomial (Fin 3) ℚ => Q.coeff e) hzero
    exact (mem_support_iff.mp he) (by simpa [coeff_homogeneousComponent, heq] using hz)
  omega
def exponent (i j k : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![i, j, k]
private theorem exponent_degree (i j k : ℕ) : (exponent i j k).degree = i + j + k := by
  simp [exponent, Finsupp.degree_eq_sum, Fin.sum_univ_three]
private theorem exponent_eq_iff {i j k u v w : ℕ} :
    exponent i j k = exponent u v w ↔ i = u ∧ j = v ∧ k = w := by
  constructor
  · intro h
    exact ⟨congrArg (fun e : Fin 3 →₀ ℕ => e 0) h,
      congrArg (fun e : Fin 3 →₀ ℕ => e 1) h, congrArg (fun e : Fin 3 →₀ ℕ => e 2) h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl
private theorem exponent_cases {e : Fin 3 →₀ ℕ} (he : e.degree = 2) :
    e = exponent 2 0 0 ∨ e = exponent 0 2 0 ∨ e = exponent 0 0 2 ∨
      e = exponent 1 1 0 ∨ e = exponent 1 0 1 ∨ e = exponent 0 1 1 := by
  have heq {i j k : ℕ} (h : e 0 = i ∧ e 1 = j ∧ e 2 = k) : e = exponent i j k := by
    ext l
    fin_cases l
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  have hs : e 0 + e 1 + e 2 = 2 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_three] using he
  have hc :
      (e 0 = 2 ∧ e 1 = 0 ∧ e 2 = 0) ∨ (e 0 = 0 ∧ e 1 = 2 ∧ e 2 = 0) ∨
      (e 0 = 0 ∧ e 1 = 0 ∧ e 2 = 2) ∨ (e 0 = 1 ∧ e 1 = 1 ∧ e 2 = 0) ∨
      (e 0 = 1 ∧ e 1 = 0 ∧ e 2 = 1) ∨ (e 0 = 0 ∧ e 1 = 1 ∧ e 2 = 1) := by omega
  rcases hc with hc | hc | hc | hc | hc | hc
  · exact Or.inl (heq hc)
  · exact Or.inr (Or.inl (heq hc))
  · exact Or.inr (Or.inr (Or.inl (heq hc)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (heq hc))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (heq hc)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (heq hc)))))
theorem eval_homogeneous_two (P : MvPolynomial (Fin 3) ℚ) (x : Fin 3 → ℚ) :
    MvPolynomial.eval x (homogeneousComponent 2 P) =
      P.coeff (exponent 2 0 0) * (x 0)^2 + P.coeff (exponent 0 2 0) * (x 1)^2 +
      P.coeff (exponent 0 0 2) * (x 2)^2 +
      P.coeff (exponent 1 1 0) * (x 0) * (x 1) +
      P.coeff (exponent 1 0 1) * (x 0) * (x 2) +
      P.coeff (exponent 0 1 1) * (x 1) * (x 2) := by
  classical
  let m (i j k : ℕ) := monomial (exponent i j k) (P.coeff (exponent i j k))
  have hform : homogeneousComponent 2 P =
      m 2 0 0 + m 0 2 0 + m 0 0 2 + m 1 1 0 + m 1 0 1 + m 0 1 1 := by
    ext e
    simp only [coeff_homogeneousComponent, m, AddMonoidAlgebra.coeff_add]
    by_cases he : e.degree = 2
    · rcases exponent_cases he with he | he | he | he | he | he <;>
        rw [he] <;> norm_num [exponent_degree, exponent_eq_iff]
    · have hne (i j k : ℕ) (hd : i + j + k = 2) : exponent i j k ≠ e := by
        intro h
        exact he (by rw [← h, exponent_degree, hd])
      simp [he, hne 2 0 0 rfl, hne 0 2 0 rfl, hne 0 0 2 rfl,
        hne 1 1 0 rfl, hne 1 0 1 rfl, hne 0 1 1 rfl]
  have heval (i j k : ℕ) :
      MvPolynomial.eval x (m i j k) =
        P.coeff (exponent i j k) * (x 0 ^ i * x 1 ^ j * x 2 ^ k) := by
    change MvPolynomial.eval x (monomial (exponent i j k) (P.coeff (exponent i j k))) = _
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [Fin.prod_univ_three, exponent, mul_assoc]
  simp [hform, heval, mul_assoc]
end
end K1_13_6_1_4_2_2
end
section
namespace K1_13_6_1_4_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_7_1 MvPolynomial
def CapsLE (p q : Shape) : Prop :=
  p.b ≤ q.b ∧ p.j ≤ q.j ∧ p.t ≤ q.t
private theorem lattice_mono {p q : Shape} (hpq : CapsLE p q) :
    latticeIndices p ⊆ latticeIndices q := by
  intro e he
  obtain ⟨hb, hj, ht⟩ := hpq
  exact ⟨he.1.trans (Nat.mul_le_mul_left 6 hb),
    he.2.1.trans (Nat.mul_le_mul_left 6 hj), he.2.2.trans (Nat.mul_le_mul_left 6 ht)⟩
theorem boxHilbert_mono (surface : Ideal GeoJets) {p q : Shape} (hpq : CapsLE p q) :
    boxHilbert surface p ≤ boxHilbert surface q := by
  let := restrictSupport_finite (R := GeoField) (Set.toFinite (latticeIndices q))
  exact Submodule.finrank_mono (Submodule.map_mono (restrictSupport_mono GeoField (lattice_mono hpq)))
theorem combined_chamber {a b h : Shape} (ha : Chamber a) (hb : Chamber b) (hh : Chamber h)
    (t : Fin 3 → ℕ) : Chamber (combinedShape a b h t) :=
  chamber_plus (chamber_plus (chamber_scale ha _) (chamber_scale hb _)) (chamber_scale hh _)
theorem combined_full {a b h : Shape} (ha : FullChamber a) (hb : FullChamber b) (hh : FullChamber h)
    {t : Fin 3 → ℕ} (ht : 0 < t 0 + t 1 + t 2) : FullChamber (combinedShape a b h t) := by
  refine ⟨combined_chamber ha.1 hb.1 hh.1 t, ?_⟩
  change 0 < t 0 * a.t + t 1 * b.t + t 2 * h.t
  by_cases h0 : 0 < t 0
  · have := Nat.mul_pos h0 ha.2
    omega
  by_cases h1 : 0 < t 1
  · have := Nat.mul_pos h1 hb.2
    omega
  have := Nat.mul_pos (show 0 < t 2 by omega) hh.2
  omega
theorem combined_pad (a b h : Shape) (t : Fin 3 → ℕ) (n pad : ℕ) :
    combinedShape a b h (fun l => n * t l + pad) =
      ((combinedShape a b h t).scale n).plus ((combinedShape a b h (fun _ => 1)).scale pad) := by
  cases a
  cases b
  cases h
  simp only [combinedShape, Shape.scale, Shape.plus, Nat.one_mul]
  congr 1 <;> ring
theorem boxHilbert_pad (surface : Ideal GeoJets) {p q : Shape}
    (hp : FullChamber p) (hq : Chamber q) (n pad : ℕ) :
    boxHilbert surface (p.scale n) ≤ boxHilbert surface ((p.scale n).plus (q.scale pad)) ∧
      boxHilbert surface ((p.scale n).plus (q.scale pad)) ≤
        boxHilbert surface (p.scale (n + pad * q.b)) := by
  have ht : 0 < p.t := hp.2
  have hj : 0 < p.j := by have := hp.1.2; omega
  have hb : 0 < p.b := hj.trans_le hp.1.1
  have hqt : q.t ≤ q.b := by have := hq.1; have := hq.2; omega
  constructor
  · apply boxHilbert_mono
    exact ⟨Nat.le_add_right .., Nat.le_add_right .., Nat.le_add_right ..⟩
  · apply boxHilbert_mono
    dsimp [CapsLE, Shape.scale, Shape.plus]
    simp only [Nat.add_mul]
    exact ⟨Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hb) _,
      Nat.add_le_add_left ((Nat.mul_le_mul_left _ hq.1).trans (Nat.le_mul_of_pos_right _ hj)) _,
      Nat.add_le_add_left ((Nat.mul_le_mul_left _ hqt).trans (Nat.le_mul_of_pos_right _ ht)) _⟩
def boxIdeal (surface : Ideal GeoJets) (p : Shape) : Ideal (MvPolynomial (latticeIndices p) GeoField) :=
  surface.comap (monomialMap GeoField (latticeIndices p)).toRingHom
theorem boxHilbert_scale (surface : Ideal GeoJets) {p : Shape} (hp : Chamber p) (n : ℕ) :
    boxHilbert surface (p.scale n) = affineHilbertFunction (boxIdeal surface p) n := by
  let φ := monomialMap GeoField (latticeIndices p)
  let I := boxIdeal surface p
  let g : (MvPolynomial (latticeIndices p) GeoField ⧸ I) →ₐ[GeoField] (GeoJets ⧸ surface) :=
    Ideal.quotientMapₐ surface φ le_rfl
  have hg : Function.Injective g := Ideal.quotientMap_injective
  have hcomp : g.toLinearMap.comp (Ideal.Quotient.mkₐ GeoField I).toLinearMap =
      (Ideal.Quotient.mkₐ GeoField surface).toLinearMap.comp φ.toLinearMap := by
    ext x
    rfl
  unfold boxHilbert
  rw [← monomialMap_filtration hp, ← Submodule.map_comp, ← hcomp, Submodule.map_comp]
  exact (Submodule.equivMapOfInjective _ hg (quotientDegreeLE I n)).finrank_eq.symm
theorem boxHilbert_degree (surface : Ideal GeoJets) {p : Shape}
    (hdim : ringKrullDim (GeoJets ⧸ surface) = 2) (hp : FullChamber p) :
    (affineHilbertPolynomial (boxIdeal surface p)).natDegree ≤ 2 := by
  let φ := monomialMap GeoField (latticeIndices p)
  have hφ : Function.Surjective φ := monomialMap_surjective (latticeIndices_single hp)
  exact (natDegree_affineHilbertPolynomial_comap_of_surjective φ hφ surface).trans_le
    (K1_13_6_2_4_2.hilbert_degree_le (d := 2) hdim.le)
end
end K1_13_6_1_4_2_2
end
section
namespace K1_13_6_1_4_2_2
noncomputable section
open Filter K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_7_1 MvPolynomial
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (a b h : Shape),
    Chamber a → Chamber b → Chamber h →
    ∃ forbidden : Finset (SectionVariable a b h →₀ ℕ),
      ∀ t : Fin 3 → ℕ,
        multiHilbert surface a b h t = standardCount (fun v => v.1) forbidden t
def c2 : Prop :=
  ∀ {σ : Type} [Finite σ] (block : σ → Fin 3), Function.Surjective block →
    ∀ forbidden : Finset (σ →₀ ℕ),
      ∃ (P : MvPolynomial (Fin 3) ℚ) (N : ℕ),
        ∀ t : Fin 3 → ℕ, (∀ l, N ≤ t l) →
          MvPolynomial.eval (fun l => (t l : ℚ)) P = (standardCount block forbidden t : ℚ)
private theorem combined_scale (a b h : Shape) (t : Fin 3 → ℕ) (n : ℕ) :
    combinedShape a b h (fun l => n * t l) = (combinedShape a b h t).scale n := by
  simpa [Shape.scale, Shape.plus] using combined_pad a b h t n 0
private theorem polynomial_degree (surface : Ideal GeoJets) {a b h : Shape}
    (hdim : ringKrullDim (GeoJets ⧸ surface) = 2)
    (ha : FullChamber a) (hb : FullChamber b) (hh : FullChamber h)
    (P : MvPolynomial (Fin 3) ℚ) (N : ℕ)
    (hP : ∀ t : Fin 3 → ℕ, (∀ l, N ≤ t l) →
      MvPolynomial.eval (fun l => (t l : ℚ)) P = (multiHilbert surface a b h t : ℚ)) :
    P.totalDegree ≤ 2 := by
  apply degree_le_of_positive_rays
  intro t ht
  let p := combinedShape a b h t
  have hp : FullChamber p := combined_full ha hb hh (by have := ht 0; omega)
  have hpol : rayPolynomial P t 0 = affineHilbertPolynomial (boxIdeal surface p) := by
    apply Polynomial.eq_of_eventually_atTop_eval_natCast_eq
    filter_upwards [eventually_ge_atTop N, eventually_eval_affineHilbertPolynomial (boxIdeal surface p)]
      with n hn hH
    have htail (l : Fin 3) : N ≤ n * t l + 0 :=
      hn.trans (Nat.le_mul_of_pos_right n (ht l))
    rw [eval_rayPolynomial, hP _ htail, hH, multiHilbert]
    simp only [Nat.add_zero, combined_scale]
    rw [boxHilbert_scale surface hp.1]
  rw [hpol]
  exact boxHilbert_degree surface hdim hp
private theorem diagonal_coeff (surface : Ideal GeoJets) {a b h : Shape}
    (hdim : ringKrullDim (GeoJets ⧸ surface) = 2)
    (ha : FullChamber a) (hb : FullChamber b) (hh : FullChamber h)
    (P : MvPolynomial (Fin 3) ℚ) (N : ℕ) (hdeg : P.totalDegree ≤ 2)
    (hP : ∀ t : Fin 3 → ℕ, (∀ l, N ≤ t l) →
      MvPolynomial.eval (fun l => (t l : ℚ)) P = (multiHilbert surface a b h t : ℚ))
    (t : Fin 3 → ℕ) (ht : 0 < t 0 + t 1 + t 2) :
    (affineHilbertPolynomial (boxIdeal surface (combinedShape a b h t))).coeff 2 =
      (rayPolynomial P t N).coeff 2 := by
  let p := combinedShape a b h t
  let q := combinedShape a b h (fun _ => 1)
  let S := affineHilbertPolynomial (boxIdeal surface p)
  let R := rayPolynomial P t N
  let d := N * q.b
  have hp : FullChamber p := combined_full ha hb hh ht
  have hq : Chamber q := combined_chamber ha.1 hb.1 hh.1 _
  have hSdeg := boxHilbert_degree surface hdim hp
  have hRdeg : R.natDegree ≤ 2 := (degree_ray_le P t N).trans hdeg
  obtain ⟨M, hM⟩ := exists_eval_affineHilbertPolynomial (boxIdeal surface p)
  have hS (n : ℕ) (hn : M ≤ n) :
      S.eval (n : ℚ) = (boxHilbert surface (p.scale n) : ℚ) := by
    exact (hM n hn).trans (congrArg Nat.cast (boxHilbert_scale surface hp.1 n).symm)
  have hR (n : ℕ) :
      R.eval (n : ℚ) = (boxHilbert surface ((p.scale n).plus (q.scale N)) : ℚ) := by
    rw [show R = rayPolynomial P t N from rfl, eval_rayPolynomial,
      hP _ (fun l => Nat.le_add_left N (n * t l)), multiHilbert, combined_pad]
  have hbounds : ∀ᶠ n : ℕ in atTop,
      S.eval (n : ℚ) ≤ R.eval (n : ℚ) ∧
        R.eval (n : ℚ) ≤ (Polynomial.taylor (d : ℚ) S).eval (n : ℚ) := by
    filter_upwards [eventually_ge_atTop M] with n hn
    have hs : (Polynomial.taylor (d : ℚ) S).eval (n : ℚ) = S.eval ((n + d : ℕ) : ℚ) := by
      rw [Polynomial.taylor_apply, Polynomial.eval_comp]
      simp [Nat.cast_add]
    rw [hs, hS n hn, hR n, hS (n + d) (hn.trans (Nat.le_add_right n d))]
    obtain ⟨hlo, hhi⟩ := boxHilbert_pad surface hp hq n N
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hlo := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hSdeg hRdeg
    (hbounds.mono fun _ hn => hn.1)
  have hshift : (Polynomial.taylor (d : ℚ) S).natDegree ≤ 2 := by
    simpa only [Polynomial.natDegree_taylor] using hSdeg
  have hhi := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hRdeg hshift
    (hbounds.mono fun _ hn => hn.2)
  rw [Polynomial.coeff_taylor_of_natDegree_le _ hSdeg] at hhi
  exact le_antisymm hlo hhi
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_2.c2 := by
  intro surface a b h _ hdim ha hb hh
  obtain ⟨forbidden, hcount⟩ := h1 surface a b h ha.1 hb.1 hh.1
  let block : SectionVariable a b h → Fin 3 := fun v => v.1
  have hblock : Function.Surjective block := by
    intro l
    exact ⟨⟨l, ⟨0, latticeIndices_zero _⟩⟩, rfl⟩
  obtain ⟨P, N, hP⟩ := h2 block hblock forbidden
  have hval (t : Fin 3 → ℕ) (ht : ∀ l, N ≤ t l) :
      MvPolynomial.eval (fun l => (t l : ℚ)) P = (multiHilbert surface a b h t : ℚ) := by
    rw [hcount]
    exact hP t ht
  have hdeg := polynomial_degree surface hdim ha hb hh P N hval
  refine ⟨P.coeff (exponent 2 0 0), P.coeff (exponent 0 2 0), P.coeff (exponent 0 0 2),
    P.coeff (exponent 1 1 0), P.coeff (exponent 1 0 1), P.coeff (exponent 0 1 1), ?_⟩
  intro i j k hijk
  let t : Fin 3 → ℕ := ![i, j, k]
  change (affineHilbertPolynomial (boxIdeal surface (combinedShape a b h t))).coeff 2 = _
  rw [diagonal_coeff surface hdim ha hb hh P N hdeg hval t hijk, coeff_ray P t N hdeg,
    eval_homogeneous_two]
  rfl
end
end K1_13_6_1_4_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_2_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4_2 K1_13_6_1_4_2_2 K1_13_6_2_3_2 MvPolynomial
open K1_13_7_1 (Chamber)
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
private theorem weight_eq_blockDegree {σ : Type} (block : σ → Fin 3) (e : σ →₀ ℕ) :
    Finsupp.weight (step ∘ block) e = blockDegree block e := by
  funext i
  simp only [Finsupp.weight_apply, blockDegree, Finsupp.sum, Finset.sum_apply, step, Function.comp_apply,
    Pi.smul_apply, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro v _
  split <;> simp_all [eq_comm]
private theorem combined_add (a b h : Shape) (s t : Fin 3 → ℕ) :
    combinedShape a b h (s + t) = (combinedShape a b h s).plus (combinedShape a b h t) := by
  simp only [combinedShape, Shape.scale, Shape.plus, Pi.add_apply]
  congr 1 <;> ring
private theorem combined_slot (a b h : Shape) (i : Fin 3) (n : ℕ) :
    combinedShape a b h (n • step i) = (![a, b, h] i).scale n := by
  fin_cases i <;> simp [combinedShape, Shape.scale, Shape.plus, step, Pi.smul_apply]
private def exponentsMap (a b h : Shape) : (SectionVariable a b h →₀ ℕ) →+ (Fin 4 →₀ ℕ) :=
  Finsupp.weight fun v => v.2.val
private theorem exponent_mem {a b h : Shape} (ha : Chamber a) (hb : Chamber b)
    (hh : Chamber h) (e : SectionVariable a b h →₀ ℕ) :
    exponentsMap a b h e ∈
      latticeIndices (combinedShape a b h (Finsupp.weight (step ∘ fun v => v.1) e)) := by
  induction e using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using latticeIndices_zero (combinedShape a b h 0)
  | add e f he hf =>
      rw [map_add, map_add, combined_add,
        latticeIndices_plus (combined_chamber ha hb hh _) (combined_chamber ha hb hh _)]
      exact Set.add_mem_add he hf
  | single v n =>
      rw [Finsupp.weight_single, Function.comp_apply, combined_slot]
      have hch (i : Fin 3) : Chamber (![a, b, h] i) := by
        fin_cases i
        exacts [ha, hb, hh]
      rw [latticeIndices_scale (hch v.1), exponentsMap, Finsupp.weight_single]
      induction n with
      | zero => simp
      | succ n ih =>
          rw [succ_nsmul, succ_nsmul]
          exact Set.add_mem_add ih v.2.property
private theorem exponent_lift_slot {a b h : Shape} (i : Fin 3) (n : ℕ)
    {m : Fin 4 →₀ ℕ} (hm : m ∈ n • latticeIndices (![a, b, h] i)) :
    ∃ e : SectionVariable a b h →₀ ℕ,
      Finsupp.weight (step ∘ fun v => v.1) e = n • step i ∧ exponentsMap a b h e = m := by
  induction n generalizing m with
  | zero =>
      rw [zero_smul, Set.mem_zero] at hm
      subst m
      exact ⟨0, by simp, map_zero _⟩
  | succ n ih =>
      rw [succ_nsmul] at hm
      obtain ⟨u, hu, v, hv, rfl⟩ := hm
      obtain ⟨e, he, hexp⟩ := ih hu
      let w : SectionVariable a b h := ⟨i, ⟨v, hv⟩⟩
      refine ⟨e + Finsupp.single w 1, ?_, ?_⟩
      · rw [map_add, Finsupp.weight_single, one_smul, he, succ_nsmul]
        rfl
      · rw [map_add, hexp, exponentsMap, Finsupp.weight_single, one_smul]
private theorem exponent_lift {a b h : Shape} (ha : Chamber a) (hb : Chamber b)
    (hh : Chamber h) (t : Fin 3 → ℕ) {m : Fin 4 →₀ ℕ}
    (hm : m ∈ latticeIndices (combinedShape a b h t)) :
    ∃ e : SectionVariable a b h →₀ ℕ,
      Finsupp.weight (step ∘ fun v => v.1) e = t ∧ exponentsMap a b h e = m := by
  rw [combinedShape, latticeIndices_plus (chamber_plus (chamber_scale ha _) (chamber_scale hb _))
    (chamber_scale hh _), latticeIndices_plus (chamber_scale ha _) (chamber_scale hb _),
    latticeIndices_scale ha, latticeIndices_scale hb, latticeIndices_scale hh] at hm
  obtain ⟨_, ⟨u, hu, v, hv, rfl⟩, w, hw, rfl⟩ := hm
  obtain ⟨e₀, h₀, h₀'⟩ := exponent_lift_slot (a := a) (b := b) (h := h) 0 (t 0) hu
  obtain ⟨e₁, h₁, h₁'⟩ := exponent_lift_slot (a := a) (b := b) (h := h) 1 (t 1) hv
  obtain ⟨e₂, h₂, h₂'⟩ := exponent_lift_slot (a := a) (b := b) (h := h) 2 (t 2) hw
  refine ⟨e₀ + e₁ + e₂, ?_, by rw [map_add, map_add, h₀', h₁', h₂']⟩
  rw [map_add, map_add, h₀, h₁, h₂]
  funext i
  fin_cases i <;> simp [step]
private def sectionMap (a b h : Shape) :
    MvPolynomial (SectionVariable a b h) GeoField →ₐ[GeoField] GeoJets :=
  aeval fun v => monomial v.2.val 1
private theorem sectionMap_monomial (a b h : Shape) (e : SectionVariable a b h →₀ ℕ) :
    sectionMap a b h (monomial e 1) = monomial (exponentsMap a b h e) 1 := by
  rw [sectionMap, aeval_monomial, Finsupp.prod, exponentsMap, Finsupp.weight_apply, Finsupp.sum]
  simp only [monomial_pow, one_pow, ← monomial_sum_one, algebraMap_eq, C_mul_monomial, mul_one]
private theorem section_image {a b h : Shape} (ha : Chamber a) (hb : Chamber b)
    (hh : Chamber h) (t : Fin 3 → ℕ) :
    (weightedHomogeneousSubmodule GeoField (step ∘ fun v : SectionVariable a b h => v.1) t).map
      (sectionMap a b h).toLinearMap =
      restrictSupport GeoField (latticeIndices (combinedShape a b h t)) := by
  have hS : weightedHomogeneousSubmodule GeoField (step ∘ fun v : SectionVariable a b h => v.1) t =
      restrictSupport GeoField {e | Finsupp.weight (step ∘ fun v => v.1) e = t} :=
    weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, hS, restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    change sectionMap a b h (monomial e 1) ∈
      restrictSupport GeoField (latticeIndices (combinedShape a b h t))
    rw [sectionMap_monomial, monomial_mem_restrictSupport]
    exact Or.inl ((show Finsupp.weight (step ∘ fun v => v.1) e = t from he) ▸
      exponent_mem ha hb hh e)
  · rw [restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨e, he, rfl⟩ := exponent_lift ha hb hh t hm
    exact ⟨monomial e 1, isWeightedHomogeneous_monomial _ _ _ he, sectionMap_monomial a b h e⟩
private def degreeLexOrder (σ : Type) [Finite σ] : MonomialOrder σ := by
  let _ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  exact MonomialOrder.degLex
theorem proof : K1_13_6_1_4_2_2.c1 := by
  classical
  intro surface a b h ha hb hh
  let σ := SectionVariable a b h
  let block : σ → Fin 3 := Sigma.fst
  let S := weightedHomogeneousSubmodule GeoField (step ∘ block)
  let φ := sectionMap a b h
  let C := surface.comap φ
  let J := (C.homogeneousCore S).toIdeal
  have hhom : J.IsHomogeneous S := (C.homogeneousCore S).isHomogeneous
  have hgraded : Graded block J :=
    fun _ hp t => weightedHomogeneousComponent_mem_of_mem _ _ hhom hp t
  let order := degreeLexOrder σ
  obtain ⟨forbidden, hf⟩ := order.exists_finset_standardExponents_iff J
  refine ⟨forbidden, fun t => ?_⟩
  let W := (S t).map (Ideal.Quotient.mkₐ GeoField J).toLinearMap
  let f := Ideal.quotientMapₐ surface φ (Ideal.toIdeal_homogeneousCore_le S C)
  have hinj : Function.Injective (f.toLinearMap.domRestrict W) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨x, hx⟩ hx0
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    change Ideal.Quotient.mk surface (φ p) = 0 at hx0
    have hpsurface : φ p ∈ surface := Ideal.Quotient.eq_zero_iff_mem.mp hx0
    have hpJ : p ∈ J := Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨t, hp⟩
      (show p ∈ C from hpsurface)
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr hpJ)
  have himage : W.map f.toLinearMap =
      (restrictSupport GeoField (latticeIndices (combinedShape a b h t))).map
        (Ideal.Quotient.mkₐ GeoField surface).toLinearMap := by
    rw [← section_image ha hb hh]
    simp only [W, ← Submodule.map_comp, ← AlgHom.comp_toLinearMap, f]
    rfl
  have hrank : Module.finrank GeoField W = multiHilbert surface a b h t := by
    change _ = boxHilbert surface (combinedShape a b h t)
    rw [boxHilbert, ← himage, ← LinearMap.range_domRestrict W f.toLinearMap]
    exact (LinearEquiv.ofInjective _ hinj).finrank_eq
  have hs :
      ({e | e ∈ order.standardExponents J ∧ Finsupp.weight (step ∘ block) e = t} :
        Set (σ →₀ ℕ)) =
      {e | blockDegree block e = t ∧ ∀ u ∈ forbidden, ¬ u ≤ e} := by
    ext e
    simp only [Set.mem_ofPred_eq, hf, weight_eq_blockDegree, and_comm]
  have hcount : hilbert block J t = (standardCount block forbidden t : ℚ) := by
    simpa only [hs, standardCount] using standard_rank block order J hgraded t
  change (Module.finrank GeoField W : ℚ) = _ at hcount
  rw [hrank] at hcount
  exact_mod_cast hcount
end
end K1_13_6_1_4_2_2_1
end
section
namespace K1_13_6_1_4_2_2_2
noncomputable section
open Finset K1_13_6_1_4_2_2
open scoped BigOperators
private abbrev Block {σ : Type} (block : σ → Fin 3) (l : Fin 3) :=
  {v : σ // block v = l}
private abbrev Exact {σ : Type} (block : σ → Fin 3) (t : Fin 3 → ℕ) :=
  {e : σ →₀ ℕ // blockDegree block e = t}
section Count
variable {σ : Type} [Fintype σ] (block : σ → Fin 3)
  [∀ l, Fintype (Block block l)]
private theorem degree_eq_sum (e : σ →₀ ℕ) (l : Fin 3) :
    blockDegree block e l = ∑ v : Block block l, e v := by
  change e.sum (fun v n => if block v = l then n else 0) = _
  rw [Finsupp.sum_fintype _ _ (fun v => by simp), ← sum_filter]
  exact sum_subtype _ (by simp) _
private theorem degree_add (e f : σ →₀ ℕ) (l : Fin 3) :
    blockDegree block (e + f) l = blockDegree block e l + blockDegree block f l := by
  simp only [degree_eq_sum, Finsupp.add_apply, sum_add_distrib]
private theorem degree_mono {e f : σ →₀ ℕ} (hef : e ≤ f) (l : Fin 3) :
    blockDegree block e l ≤ blockDegree block f l := by
  simp only [degree_eq_sum]
  exact sum_le_sum fun v _ => Finsupp.le_def.mp hef v
private def exactEquiv [DecidableEq σ] (t : Fin 3 → ℕ) :
    Exact block t ≃ ∀ l : Fin 3, (univ : Finset (Block block l)).finsuppAntidiag (t l) where
  toFun e l := ⟨Finsupp.equivFunOnFinite.symm (fun v => e.1 (v : σ)), by
    rw [mem_finsuppAntidiag]
    exact ⟨(degree_eq_sum block e.1 l).symm.trans (congrFun e.2 l), subset_univ _⟩⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun v => (f (block v)).1 ⟨v, rfl⟩), by
    funext l
    rw [degree_eq_sum]
    calc
      _ = ∑ v : Block block l, (f l).1 v := by
        apply sum_congr rfl
        rintro ⟨v, hv⟩ -
        subst l
        rfl
      _ = t l := (mem_finsuppAntidiag.mp (f l).2).1⟩
  left_inv e := by
    apply Subtype.ext
    ext v
    rfl
  right_inv f := by
    funext l
    apply Subtype.ext
    ext v
    obtain ⟨v, hv⟩ := v
    subst l
    rfl
private theorem exact_card [DecidableEq σ] (hblock : Function.Surjective block) (t : Fin 3 → ℕ) :
    Nat.card (Exact block t) =
      ∏ l : Fin 3, (t l + (Fintype.card (Block block l) - 1)).choose
        (Fintype.card (Block block l) - 1) := by
  rw [Nat.card_congr (exactEquiv block t), Nat.card_eq_fintype_card, Fintype.card_pi]
  refine prod_congr rfl fun l _ => ?_
  rw [Fintype.card_coe, card_finsuppAntidiag_nat_eq_choose, card_univ]
  obtain ⟨v, hv⟩ := hblock l
  have hpos : 0 < Fintype.card (Block block l) :=
    Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
  have hadd : Fintype.card (Block block l) + t l - 1 =
      t l + (Fintype.card (Block block l) - 1) := by omega
  exact (Nat.choose_symm_of_eq_add hadd).trans (by rw [hadd])
private def coneEquiv (s : σ →₀ ℕ) (t : Fin 3 → ℕ)
    (hs : ∀ l, blockDegree block s l ≤ t l) :
    {e : σ →₀ ℕ // blockDegree block e = t ∧ s ≤ e} ≃
      Exact block (fun l => t l - blockDegree block s l) where
  toFun e := ⟨e.1 - s, by
    funext l
    have hadd := congrArg (fun f => blockDegree block f l) (tsub_add_cancel_of_le e.2.2)
    rw [degree_add, congrFun e.2.1 l] at hadd
    change blockDegree block (e.1 - s) l = t l - blockDegree block s l
    omega⟩
  invFun u := ⟨u.1 + s, ⟨by
    funext l
    rw [degree_add, congrFun u.2 l]
    exact Nat.sub_add_cancel (hs l), le_add_self⟩⟩
  left_inv e := Subtype.ext (tsub_add_cancel_of_le e.2.2)
  right_inv u := Subtype.ext (add_tsub_cancel_right u.1 s)
end Count
private theorem exact_filter_card {σ : Type} (block : σ → Fin 3) (t : Fin 3 → ℕ)
    [Fintype (Exact block t)] (p : (σ →₀ ℕ) → Prop) [DecidablePred p] :
    #(univ.filter fun e : Exact block t => p e.1) =
      ({e | blockDegree block e = t ∧ p e} : Set (σ →₀ ℕ)).ncard := by
  rw [← Nat.card_coe_set_eq]
  calc
    _ = Nat.card ↥(univ.filter fun e : Exact block t => p e.1) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = _ := Nat.card_congr
      { toFun := fun e => ⟨e.1.1, e.1.2, (mem_filter.mp e.2).2⟩
        invFun := fun e => ⟨⟨e.1, e.2.1⟩, mem_filter.mpr ⟨mem_univ _, e.2.2⟩⟩
        left_inv := fun e => Subtype.ext rfl
        right_inv := fun e => Subtype.ext rfl }
private theorem eval_blockPoly (t : Fin 3 → ℕ) (l : Fin 3) (d k : ℕ)
    (hk : k ≤ t l) :
    MvPolynomial.eval (fun l => (t l : ℚ))
        (Polynomial.aeval (MvPolynomial.X l) (Polynomial.preHilbertPoly ℚ d k)) =
      ((t l - k + d).choose d : ℚ) := by
  change MvPolynomial.aeval (fun i => (t i : ℚ))
    (Polynomial.aeval (MvPolynomial.X l) (Polynomial.preHilbertPoly ℚ d k)) = _
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
  change (Polynomial.preHilbertPoly ℚ d k).eval (t l : ℚ) = _
  rw [Polynomial.preHilbertPoly_eq_choose_add_sub ℚ d (hk.trans (Nat.le_add_right _ _)),
    Nat.sub_add_comm hk]
theorem proof : K1_13_6_1_4_2_2.c2 := by
  classical
  intro σ hσ block hblock forbidden
  let : Fintype σ := Fintype.ofFinite σ
  let (l : Fin 3) : Fintype (Block block l) := Fintype.ofFinite _
  let d (l : Fin 3) := Fintype.card (Block block l) - 1
  let N := univ.sup (blockDegree block (forbidden.sup id))
  let P : MvPolynomial (Fin 3) ℚ :=
    ∑ U ∈ forbidden.powerset,
      MvPolynomial.C ((-1 : ℚ) ^ #U) *
        ∏ l : Fin 3, Polynomial.aeval (MvPolynomial.X l)
          (Polynomial.preHilbertPoly ℚ (d l) (blockDegree block (U.sup id) l))
  refine ⟨P, N, ?_⟩
  intro t ht
  let : Fintype (Exact block t) := Fintype.ofEquiv _ (exactEquiv block t).symm
  let cone (s : σ →₀ ℕ) : Finset (Exact block t) := univ.filter fun e => s ≤ e.1
  have hinter (U : Finset (σ →₀ ℕ)) : U.inf cone = cone (U.sup id) := by
    ext e
    simp only [Finset.mem_inf, cone, mem_filter, mem_univ, true_and, Finset.sup_le_iff, id]
  have havoid : (forbidden.inf fun s => (cone s)ᶜ) =
      univ.filter (fun e : Exact block t => ∀ s ∈ forbidden, ¬ s ≤ e.1) := by
    ext e
    simp only [Finset.mem_inf, mem_compl, cone, mem_filter, mem_univ, true_and]
  have hcard : (#(forbidden.inf fun s => (cone s)ᶜ) : ℚ) =
      (standardCount block forbidden t : ℚ) := by
    rw [havoid]
    exact congrArg (fun n : ℕ => (n : ℚ))
      (exact_filter_card block t (fun e => ∀ s ∈ forbidden, ¬ s ≤ e))
  have hie := congrArg (Int.cast : ℤ → ℚ)
    (inclusion_exclusion_card_inf_compl forbidden cone)
  push_cast at hie
  simp only [P, map_sum, map_mul, MvPolynomial.eval_C, map_prod]
  rw [← hcard, hie]
  refine sum_congr rfl fun U hU => ?_
  have hshift (l : Fin 3) : blockDegree block (U.sup id) l ≤ t l := by
    exact (degree_mono block (sup_mono (mem_powerset.mp hU)) l).trans
      ((le_sup (f := blockDegree block (forbidden.sup id)) (mem_univ l)).trans (ht l))
  congr 1
  rw [hinter, show #(cone (U.sup id)) =
      Nat.card {e : σ →₀ ℕ // blockDegree block e = t ∧ U.sup id ≤ e} from
        exact_filter_card block t _,
    Nat.card_congr (coneEquiv block (U.sup id) t hshift), exact_card block hblock _]
  push_cast
  exact prod_congr rfl fun l _ => eval_blockPoly t l _ _ (hshift l)
end
end K1_13_6_1_4_2_2_2
end
section
namespace K1_13_6_1_2
noncomputable section
open K1_13 K1_13_6
theorem pair_height {f Q : GeoJets} {p : Ideal GeoJets}
    (hf : f ≠ 0) (hrel : IsRelPrime f Q) (hp : (Ideal.span {f, Q}).IsMinimalPrime p) :
    p.height = 2 := by
  let _ : p.IsPrime := hp.isPrime
  have hcount : ({f, Q} : Set GeoJets).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by simp)
  have hupper : p.height ≤ 2 :=
    (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hp).trans (by exact_mod_cast hcount)
  have hfmem : f ∈ p := hp.le (Ideal.subset_span (by simp))
  have hQmem : Q ∈ p := hp.le (Ideal.subset_span (by simp))
  have hpbot : p ≠ ⊥ := fun h => hf (Ideal.mem_bot.mp (h ▸ hfmem))
  have hone : 1 ≤ p.height := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hpbot)
    simpa [Ideal.height_bot] using h
  have hnot : p.height ≠ 1 := by
    intro h
    obtain ⟨z, hz⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one h).principal
    change p = Ideal.span {z} at hz
    have hzf : z ∣ f := Ideal.mem_span_singleton.mp (hz ▸ hfmem)
    have hzQ : z ∣ Q := Ideal.mem_span_singleton.mp (hz ▸ hQmem)
    exact hp.isPrime.ne_top (hz.trans (Ideal.span_singleton_eq_top.mpr (hrel hzf hzQ)))
  exact le_antisymm hupper ((ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr
    (lt_of_le_of_ne hone (Ne.symm hnot)))
private theorem length_ge_order {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R} {n : ℕ} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hh : 1 < (IsLocalRing.maximalIdeal R).height)
    (hy : y ∈ IsLocalRing.maximalIdeal R ^ n) :
    (n : ℕ∞) ≤ Module.length R (R ⧸ Ideal.span {x, y}) := by
  let m := IsLocalRing.maximalIdeal R
  let A : Ideal R := Ideal.span {x}
  have hno (i : ℕ) : ¬ m ^ i ≤ A := by
    intro h
    have hmin : m ∈ A.minimalPrimes := by
      refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem m).mpr hx⟩, ?_⟩
      intro P hP _
      exact fun z hz => hP.1.mem_of_pow_mem i (hP.2 (h (Ideal.pow_mem_pow hz i)))
    let _ : A.IsPrincipal := ⟨⟨x, rfl⟩⟩
    exact (not_le_of_gt hh)
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing A hmin)
  let I (i : ℕ) : Ideal R := A ⊔ m ^ i
  have hstep (i : ℕ) : I (i + 1) < I i := by
    refine lt_of_le_of_ne (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ i)) _) ?_
    intro he
    apply hno i
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := m) (IsNoetherian.noetherian _)
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · change m ^ i ≤ A ⊔ m • m ^ i
      rw [smul_eq_mul, ← pow_succ']
      change m ^ i ≤ I (i + 1)
      rw [he]
      exact le_sup_right
  have hcoheight (i : ℕ) : (i : ℕ∞) ≤ Order.coheight (I i : Submodule R R) := by
    induction i with
    | zero => simp
    | succ i ih =>
        rw [Nat.cast_succ]
        exact (add_le_add_left ih 1).trans
          (Order.coheight_add_one_le (show (I (i + 1) : Submodule R R) < I i from hstep i))
  rw [Module.length_quotient]
  apply (hcoheight n).trans
  apply Order.coheight_anti
  apply Ideal.span_le.mpr
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨Ideal.mem_sup_left (Ideal.mem_span_singleton_self x), Ideal.mem_sup_right hy⟩
theorem cycleLength_pos {J p : Ideal GeoJets} (hp : p.IsPrime) (hle : J ≤ p) :
    0 < cycleLength J p hp := by
  let _ : p.IsPrime := hp
  let L := Localization.AtPrime p
  let A := J.map (algebraMap GeoJets L)
  have hA : A ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal L).ne_top
    change J.map (algebraMap GeoJets L) ≤ IsLocalRing.maximalIdeal L
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p L]
    exact Ideal.map_mono hle
  change 0 < Module.length L (L ⧸ A)
  exact Module.length_pos_iff.mpr (Ideal.Quotient.nontrivial_iff.mpr hA)
theorem cycleLength_ge_order {f Q : Row 4} {p : Ideal GeoJets} [p.IsPrime] {n : ℕ}
    (hheight : p.height = 2)
    (hfp : toGeneric f ∈ p) (hQ : VanishesTo p (toGeneric Q) n) :
    (n : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) p ‹p.IsPrime› := by
  let L := Localization.AtPrime p
  let φ := algebraMap GeoJets L
  have hheight' : (IsLocalRing.maximalIdeal L).height = 2 := by
    apply WithBot.coe_injective
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      IsLocalization.AtPrime.ringKrullDim_eq_height p L, hheight]
  have hf : φ (toGeneric f) ∈ IsLocalRing.maximalIdeal L :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L p _).mpr hfp
  have hmap : (intersectionIdeal f Q).map φ =
      Ideal.span {φ (toGeneric f), φ (toGeneric Q)} := by
    rw [intersectionIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change (n : ℕ∞) ≤ Module.length L (L ⧸ (intersectionIdeal f Q).map φ)
  rw [hmap]
  exact length_ge_order hf (hheight' ▸ (by decide : (1 : ℕ∞) < 2)) hQ
end
end K1_13_6_1_2
end
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 160000
namespace K1_13_6_1_4_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_3
open MvPolynomial
open scoped BigOperators nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem quotient_isLocalization {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (M : Submonoid A) [IsLocalization M B] (I : Ideal A)
    (J' : Ideal B) (hJ : I.map (algebraMap A B) = J') :
    let f := Ideal.quotientMap J' (algebraMap A B) (Ideal.map_le_iff_le_comap.mp hJ.le)
    letI := f.toAlgebra
    IsLocalization (M.map (Ideal.Quotient.mk I)) (B ⧸ J') := by
  subst J'
  dsimp only
  let J := I.map (algebraMap A B)
  let f : A ⧸ I →+* B ⧸ J :=
    Ideal.quotientMap J (algebraMap A B) Ideal.le_comap_map
  let _ := f.toAlgebra
  change IsLocalization (M.map (Ideal.Quotient.mk I)) (B ⧸ J)
  have hm (m : M) : Ideal.Quotient.mk I m ∈ M.map (Ideal.Quotient.mk I) :=
    Submonoid.mem_map_of_mem _ m.property
  refine (isLocalization_iff (M.map (Ideal.Quotient.mk I)) (B ⧸ J)).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    exact (IsLocalization.map_units B ⟨m, hm⟩).map (Ideal.Quotient.mk J)
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨r, m⟩, e⟩ := IsLocalization.surj M z
    exact ⟨⟨Ideal.Quotient.mk I r, ⟨Ideal.Quotient.mk I m, hm m⟩⟩,
      by
        change Ideal.Quotient.mk J z * Ideal.Quotient.mk J (algebraMap A B m) =
          Ideal.Quotient.mk J (algebraMap A B r)
        simpa only [map_mul] using congrArg (Ideal.Quotient.mk J) e⟩
  · intro x y e
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk J (algebraMap A B x) =
      Ideal.Quotient.mk J (algebraMap A B y) at e
    have he : algebraMap A B (x - y) ∈ J := by
      rw [map_sub, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact e
    obtain ⟨m, hmM, hmem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M B I _).mp he
    refine ⟨⟨Ideal.Quotient.mk I m, hm ⟨m, hmM⟩⟩, ?_⟩
    rw [← map_mul, ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← mul_sub]
    exact hmem
private def eliminate {R σ : Type*} [CommRing R] [DecidableEq σ]
    (p q : σ) (hpq : p ≠ q) (u v : MvPolynomial {i // i ≠ p ∧ i ≠ q} R) :
    let ι := rename (R := R) (Subtype.val : {i // i ≠ p ∧ i ≠ q} → σ)
    (MvPolynomial σ R ⧸ Ideal.span {MvPolynomial.X p + ι u, MvPolynomial.X q + ι v}) ≃ₐ[R]
      MvPolynomial {i // i ≠ p ∧ i ≠ q} R := by
  let Free := {i // i ≠ p ∧ i ≠ q}
  let ι := rename (R := R) (Subtype.val : Free → σ)
  let I : Ideal (MvPolynomial σ R) := Ideal.span {MvPolynomial.X p + ι u, MvPolynomial.X q + ι v}
  let value (i : σ) : MvPolynomial Free R :=
    if h : i ≠ p ∧ i ≠ q then MvPolynomial.X ⟨i, h⟩ else if i = p then -u else -v
  let f : MvPolynomial σ R →ₐ[R] MvPolynomial Free R := aeval value
  have hι : f.comp ι = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    change f (ι (MvPolynomial.X i)) = MvPolynomial.X i
    simp [f, ι, value, i.property]
  have hfr (w : MvPolynomial Free R) : f (ι w) = w := AlgHom.congr_fun hι w
  have hfp : f (MvPolynomial.X p) = -u := by simp [f, value]
  have hfq : f (MvPolynomial.X q) = -v := by simp [f, value, hpq.symm]
  have hI : ∀ x ∈ I, f x = 0 := by
    have H : I ≤ RingHom.ker f.toRingHom := by
      simp [I, Ideal.span_le, Set.insert_subset_iff, hfp, hfq, hfr]
    exact fun _ hx => H hx
  let g := Ideal.Quotient.liftₐ I f hI
  let j := Ideal.Quotient.mkₐ R I
  change (MvPolynomial σ R ⧸ I) ≃ₐ[R] MvPolynomial Free R
  refine AlgEquiv.ofAlgHom g (j.comp ι) ?_ ?_
  · rw [← AlgHom.comp_assoc, show g.comp j = f from Ideal.Quotient.liftₐ_comp I f hI]
    exact hι
  · apply Ideal.Quotient.algHom_ext R
    simp only [AlgHom.comp_assoc, AlgHom.id_comp]
    ext i
    change j (ι (f (MvPolynomial.X i))) = j (MvPolynomial.X i)
    by_cases hi : i ≠ p ∧ i ≠ q
    · simp [f, value, hi, ι]
    · by_cases hip : i = p
      · subst i
        rw [hfp, map_neg, map_neg]
        have hz : j (MvPolynomial.X p + ι u) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
        exact (eq_neg_of_add_eq_zero_left (by simpa only [map_add] using hz)).symm
      · have hiq : i = q := by
          by_contra hn
          exact hi ⟨hip, hn⟩
        subst i
        rw [hfq, map_neg, map_neg]
        have hz : j (MvPolynomial.X q + ι v) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
        exact (eq_neg_of_add_eq_zero_left (by simpa only [map_add] using hz)).symm
abbrev sectionIdeal (a h : Shape) : Ideal (SliceJets a h) :=
  Ideal.span {firstSection a h, secondSection a h}
def UniversalSlice (a h : Shape) : Type := SliceJets a h ⧸ sectionIdeal a h
instance (a h : Shape) : CommRing (UniversalSlice a h) :=
  inferInstanceAs (CommRing (SliceJets a h ⧸ sectionIdeal a h))
instance (a h : Shape) : Algebra (PairSectionField a h) (UniversalSlice a h) :=
  inferInstanceAs (Algebra (PairSectionField a h) (SliceJets a h ⧸ sectionIdeal a h))
instance (a h : Shape) : Algebra GeoJets (UniversalSlice a h) :=
  inferInstanceAs (Algebra GeoJets (SliceJets a h ⧸ sectionIdeal a h))
def sliceEquiv (J : Ideal GeoJets) (a h : Shape) :
    (UniversalSlice a h ⧸ J.map (algebraMap GeoJets (UniversalSlice a h))) ≃ₐ[PairSectionField a h]
      SliceAlgebra J a h := by
  let F := PairSectionField a h
  let L := J.map (extendCoeffs a h)
  let proj : SliceJets a h →+* UniversalSlice a h := Ideal.Quotient.mk (sectionIdeal a h)
  have hmap : J.map (algebraMap GeoJets (UniversalSlice a h)) = L.map proj := by
    rw [Ideal.map_map]
    rfl
  have e : (UniversalSlice a h ⧸ L.map proj) ≃ₐ[F] (SliceJets a h ⧸ (sectionIdeal a h ⊔ L)) :=
    DoubleQuot.quotQuotEquivQuotSupₐ F (sectionIdeal a h) L
  exact (Ideal.quotientEquivAlgOfEq F hmap).trans
    (e.trans (Ideal.quotientEquivAlgOfEq F (sup_comm _ _)))
private def zeroIndex (b : Shape) : SectionIndex b := fun _ => 0
private abbrev CoeffRing (a h : Shape) := MvPolynomial (PairSectionIndex a h) GeoField
private abbrev IncidenceJets (a h : Shape) := MvPolynomial (Fin 4) (CoeffRing a h)
private def integralSection {σ : Type*} (p : Shape) (ι : SectionIndex p → σ) :
    MvPolynomial (Fin 4) (MvPolynomial σ GeoField) :=
  ∑ m ∈ boxMonomials p, C (MvPolynomial.X (ι m)) * ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
private abbrev incidenceIdeal (a h : Shape) : Ideal (IncidenceJets a h) :=
  Ideal.span {integralSection a Sum.inl, integralSection h Sum.inr}
private theorem coeffElimination (a h : Shape) :
    Module.Flat GeoJets (IncidenceJets a h ⧸ incidenceIdeal a h) := by
  classical
  let σ := PairSectionIndex a h
  let p : σ := Sum.inl (zeroIndex a)
  let q : σ := Sum.inr (zeroIndex h)
  have hpq : p ≠ q := Sum.inl_ne_inr
  let Free := {i : σ // i ≠ p ∧ i ≠ q}
  let ι := rename (R := GeoJets) (Subtype.val : Free → σ)
  let e : IncidenceJets a h ≃ₐ[GeoJets] MvPolynomial σ GeoJets :=
    AlgEquiv.ofRingEquiv (f := (commAlgEquiv GeoField (Fin 4) σ).toRingEquiv) (by
      intro r
      have he : (commAlgEquiv GeoField (Fin 4) σ).toRingHom.comp
          (MvPolynomial.map (C : GeoField →+* CoeffRing a h)) = C := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp
        · intro i
          simp
      exact DFunLike.congr_fun he r)
  have decompose (b : Shape) (i : SectionIndex b → σ)
      (hi : ∀ m, m ≠ zeroIndex b → i m ≠ p ∧ i m ≠ q) :
      ∃ u : MvPolynomial Free GeoJets, e (integralSection b i) = MvPolynomial.X (i (zeroIndex b)) + ι u := by
    let value : σ → MvPolynomial Free GeoJets :=
      fun j => if hj : j ≠ p ∧ j ≠ q then MvPolynomial.X ⟨j, hj⟩ else 0
    let rem : MvPolynomial σ GeoJets :=
      ∑ m ∈ (boxMonomials b).erase (zeroIndex b), MvPolynomial.X (i m) * C (∏ j : Fin 4, MvPolynomial.X j ^ (m j).val)
    refine ⟨aeval value rem, ?_⟩
    have he (m : SectionIndex b) :
        e (C (MvPolynomial.X (i m)) * ∏ j : Fin 4, MvPolynomial.X j ^ (m j).val) =
          MvPolynomial.X (i m) * C (∏ j : Fin 4, MvPolynomial.X j ^ (m j).val) := by
      change commAlgEquiv GeoField (Fin 4) σ
        (C (MvPolynomial.X (i m)) * ∏ j : Fin 4, MvPolynomial.X j ^ (m j).val) = _
      simp
    have hz : zeroIndex b ∈ boxMonomials b := by
      simp [boxMonomials, zeroIndex]
    simp only [integralSection, map_sum, he]
    rw [← Finset.sum_erase_add _ _ hz, add_comm]
    have hrem : ι (aeval value rem) = rem := by
      simp only [rem, map_sum, map_mul, aeval_X, aeval_C, algebraMap_eq]
      exact Finset.sum_congr rfl fun m hm => by
        simp [ι, value, hi m (Finset.mem_erase.mp hm).1]
    rw [hrem]
    simp [zeroIndex, rem]
  obtain ⟨u, hu⟩ := decompose a Sum.inl fun m hm =>
    ⟨fun he => hm (Sum.inl.inj he), Sum.inl_ne_inr⟩
  obtain ⟨v, hv⟩ := decompose h Sum.inr fun m hm =>
    ⟨Sum.inr_ne_inl, fun he => hm (Sum.inr.inj he)⟩
  have hI : Ideal.span {MvPolynomial.X p + ι u, MvPolynomial.X q + ι v} = (incidenceIdeal a h).map e.toRingHom := by
    simp [incidenceIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hu, hv, p, q]
  exact Module.Flat.of_linearEquiv
    (((Ideal.quotientEquivAlg _ _ e hI).trans (eliminate p q hpq u v)).toLinearEquiv)
theorem universalSlice_flat (a h : Shape) : Module.Flat GeoJets (UniversalSlice a h) := by
  let A := IncidenceJets a h
  let B := SliceJets a h
  let I := incidenceIdeal a h
  let M : Submonoid A := (nonZeroDivisors (CoeffRing a h)).map C
  have hloc : IsLocalization M B :=
    MvPolynomial.isLocalization _ (PairSectionField a h)
  have hsec (p : Shape) (i : SectionIndex p → PairSectionIndex a h) :
      algebraMap A B (integralSection p i) = sectionWith p i := by
    change MvPolynomial.map (algebraMap (CoeffRing a h) (PairSectionField a h))
      (integralSection p i) = _
    simp only [integralSection, sectionWith, map_sum, map_mul, map_prod, map_pow,
      MvPolynomial.map_C, MvPolynomial.map_X]
  have hI : I.map (algebraMap A B) = sectionIdeal a h := by
    simp only [I, incidenceIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hsec] <;> rfl
  let f : (A ⧸ I) →+* UniversalSlice a h :=
    Ideal.quotientMap (sectionIdeal a h) (algebraMap A B) (Ideal.map_le_iff_le_comap.mp hI.le)
  let _ := @RingHom.toAlgebra (A ⧸ I) (UniversalSlice a h) _ _ f
  let mkI : A →+* (A ⧸ I) := Ideal.Quotient.mk I
  let M' : Submonoid (A ⧸ I) := M.map mkI
  have hlocal : IsLocalization (R := A ⧸ I) M' (UniversalSlice a h) := by
    have hl := quotient_isLocalization M I (sectionIdeal a h) hI
    dsimp only at hl
    exact hl
  have hflat := coeffElimination a h
  have hflat' : Module.Flat (A ⧸ I) (UniversalSlice a h) :=
    IsLocalization.flat (R := A ⧸ I) _ M'
  have htower : IsScalarTower GeoJets (A ⧸ I) (UniversalSlice a h) := by
    refine IsScalarTower.of_algebraMap_eq (R := GeoJets) (S := A ⧸ I)
      (A := UniversalSlice a h) fun r => ?_
    change Ideal.Quotient.mk (sectionIdeal a h) (extendCoeffs a h r) =
      f (Ideal.Quotient.mk I (MvPolynomial.map C r))
    have he : extendCoeffs a h r = algebraMap A B (MvPolynomial.map C r) := by
      change MvPolynomial.map (algebraMap GeoField (PairSectionField a h)) r =
        MvPolynomial.map (algebraMap (CoeffRing a h) (PairSectionField a h)) (MvPolynomial.map C r)
      rw [IsScalarTower.algebraMap_eq GeoField (CoeffRing a h) (PairSectionField a h),
        MvPolynomial.map_map, MvPolynomial.algebraMap_eq]
    exact congrArg (Ideal.Quotient.mk (sectionIdeal a h)) he
  exact Module.Flat.trans GeoJets (A ⧸ I) (UniversalSlice a h)
end
end K1_13_6_1_4_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_2_1_2_1
noncomputable section
open K1_13 K1_13_7_1 K1_13_6_1_4_2 K1_13_6_1_4_2_1_2 MvPolynomial
open scoped Pointwise
variable {k : Type*} [Field k]
private abbrev degreeShape (a h : Shape) (d : ℕ × ℕ) : Shape :=
  (a.scale d.1).plus (h.scale d.2)
private theorem degreeShape_add (a h : Shape) (d e : ℕ × ℕ) :
    degreeShape a h (d + e) = (degreeShape a h d).plus (degreeShape a h e) := by
  cases a
  cases h
  simp [degreeShape, Shape.scale, Shape.plus, Nat.add_mul, add_assoc, add_left_comm]
private theorem splitExponent {a h : Shape} (ha : Chamber a) (hh : Chamber h)
    (d e : ℕ × ℕ) {m : Fin 4 →₀ ℕ}
    (hm : m ∈ latticeIndices (degreeShape a h (d + e))) :
    ∃ u ∈ latticeIndices (degreeShape a h d),
      ∃ v ∈ latticeIndices (degreeShape a h e), u + v = m := by
  rw [degreeShape_add, latticeIndices_plus
    (chamber_plus (chamber_scale ha d.1) (chamber_scale hh d.2))
    (chamber_plus (chamber_scale ha e.1) (chamber_scale hh e.2))] at hm
  exact hm
private theorem exponent_eq_zero {a h : Shape} {m : Fin 4 →₀ ℕ}
    (hm : m ∈ latticeIndices (degreeShape a h 0)) : m = 0 := by
  have hzero : degreeShape a h 0 = ⟨0, 0, 0⟩ := by
    simp [degreeShape, Shape.scale, Shape.plus]
  rw [hzero] at hm
  have he : (fun i => m i) ∈ exponents ⟨0, 0, 0⟩ := hm
  rw [exponents_zero, Set.mem_singleton_iff] at he
  ext i
  exact congrFun he i
private abbrev liftedMonomial (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (d : ℕ × ℕ) (m : Fin 4 →₀ ℕ) (hm : m ∈ latticeIndices (degreeShape a h d)) :
    rees I a h :=
  homogeneous d (Ideal.Quotient.mk I (monomial m 1)) (monomial_mem_box hm 1)
private theorem liftedMonomial_zero (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (hm : (0 : Fin 4 →₀ ℕ) ∈ latticeIndices (degreeShape a h 0)) :
    liftedMonomial I a h 0 0 hm = 1 := by
  apply (show Function.Injective (rees I a h).val from Subtype.val_injective)
  rw [show (rees I a h).val 1 = AddMonoidAlgebra.single 0 1 from rfl]
  simp only [liftedMonomial, val_homogeneous, monomial_zero', map_one]
private theorem liftedMonomial_add (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (d e : ℕ × ℕ) {u v : Fin 4 →₀ ℕ}
    (hu : u ∈ latticeIndices (degreeShape a h d))
    (hv : v ∈ latticeIndices (degreeShape a h e))
    (huv : u + v ∈ latticeIndices (degreeShape a h (d + e))) :
    liftedMonomial I a h (d + e) (u + v) huv =
      liftedMonomial I a h d u hu * liftedMonomial I a h e v hv := by
  apply (show Function.Injective (rees I a h).val from Subtype.val_injective)
  simp only [map_mul, liftedMonomial, val_homogeneous, AddMonoidAlgebra.single_mul_single]
  rw [← map_mul, monomial_mul_monomial, mul_one]
private theorem homogeneous_mem (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (d : ℕ × ℕ) (S : Submodule k (rees I a h))
    (hmon : ∀ m hm, liftedMonomial I a h d m hm ∈ S)
    (x : Affine I) (hx : x ∈ box I a h d) :
    homogeneous d x hx ∈ S := by
  obtain ⟨p, hp, rfl⟩ := hx
  let f : MvPolynomial (Fin 4) k →ₗ[k] AddMonoidAlgebra (Affine I) (ℕ × ℕ) :=
    (AddMonoidAlgebra.lsingle d).comp (Ideal.Quotient.mkₐ k I).toLinearMap
  let v := (rees I a h).val.toLinearMap
  have hle : restrictSupport k (latticeIndices (degreeShape a h d)) ≤ (S.map v).comap f := by
    rw [restrictSupport_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨liftedMonomial I a h d m hm, hmon m hm, rfl⟩
  obtain ⟨r, hr, heq⟩ := hle hp
  have heq' : r = homogeneous d (Ideal.Quotient.mk I p) ⟨p, hp, rfl⟩ :=
    Subtype.val_injective heq
  exact heq' ▸ hr
private def coordinateEval (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) :
    MvPolynomial (latticeIndices a ⊕ latticeIndices h) k →ₐ[k] rees I a h :=
  aeval (Sum.elim (leftGen I a h) (rightGen I a h))
private theorem leftGen_mem_range (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (m : latticeIndices a) : leftGen I a h m ∈ (coordinateEval I a h).range :=
  ⟨MvPolynomial.X (.inl m), by simp [coordinateEval]⟩
private theorem rightGen_mem_range (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (m : latticeIndices h) : rightGen I a h m ∈ (coordinateEval I a h).range :=
  ⟨MvPolynomial.X (.inr m), by simp [coordinateEval]⟩
private theorem liftedMonomial_mem_range (I : Ideal (MvPolynomial (Fin 4) k))
    (a h : Shape) (ha : Chamber a) (hh : Chamber h) (i j : ℕ) (m : Fin 4 →₀ ℕ)
    (hm : m ∈ latticeIndices (degreeShape a h (i, j))) :
    liftedMonomial I a h (i, j) m hm ∈ (coordinateEval I a h).range := by
  induction i generalizing m with
  | zero =>
    induction j generalizing m with
    | zero =>
      obtain rfl := exponent_eq_zero hm
      exact (liftedMonomial_zero I a h hm).symm ▸ (coordinateEval I a h).range.one_mem
    | succ j ih =>
      obtain ⟨u, hu, v, hv, rfl⟩ := splitExponent ha hh (0, j) (0, 1) hm
      have hv' : v ∈ latticeIndices h := by simpa only [degreeShape, right_axis] using hv
      exact (liftedMonomial_add I a h (0, j) (0, 1) hu hv hm).symm ▸
        (coordinateEval I a h).range.mul_mem (ih u hu) (rightGen_mem_range I a h ⟨v, hv'⟩)
  | succ i ih =>
    obtain ⟨u, hu, v, hv, rfl⟩ := splitExponent ha hh (i, j) (1, 0) hm
    have hv' : v ∈ latticeIndices a := by simpa only [degreeShape, left_axis] using hv
    exact (liftedMonomial_add I a h (i, j) (1, 0) hu hv hm).symm ▸
      (coordinateEval I a h).range.mul_mem (ih u hu) (leftGen_mem_range I a h ⟨v, hv'⟩)
private theorem rees_noetherian (I : Ideal (MvPolynomial (Fin 4) k))
    (a h : Shape) (ha : Chamber a) (hh : Chamber h) : IsNoetherianRing (rees I a h) := by
  classical
  apply isNoetherianRing_of_surjective _ _ (coordinateEval I a h).toRingHom
  intro p
  change p ∈ (coordinateEval I a h).range
  have hp : p = ∑ d ∈ p.val.coeff.support, homogeneous d (p.val.coeff d) (p.property d) := by
    apply (show Function.Injective (rees I a h).val from Subtype.val_injective)
    simp only [map_sum, val_homogeneous]
    exact (AddMonoidAlgebra.sum_coeff_single p.val).symm
  rw [hp]
  apply (coordinateEval I a h).range.sum_mem
  intro d _
  exact homogeneous_mem I a h d (coordinateEval I a h).range.toSubmodule
    (liftedMonomial_mem_range I a h ha hh d.1 d.2) _ _
private theorem liftedMonomial_mem_irrelevant (I : Ideal (MvPolynomial (Fin 4) k))
    (a h : Shape) (ha : Chamber a) (hh : Chamber h) (m : Fin 4 →₀ ℕ)
    (hm : m ∈ latticeIndices (degreeShape a h (1, 1))) :
    liftedMonomial I a h (1, 1) m hm ∈ irrelevant I a h := by
  obtain ⟨u, hu, v, hv, rfl⟩ := splitExponent ha hh (1, 0) (0, 1) hm
  have hu' : u ∈ latticeIndices a := by simpa only [degreeShape, left_axis] using hu
  have hv' : v ∈ latticeIndices h := by simpa only [degreeShape, right_axis] using hv
  exact (liftedMonomial_add I a h (1, 0) (0, 1) hu hv hm).symm ▸
    Ideal.subset_span (s := Set.range (pairGen I a h)) ⟨(⟨u, hu'⟩, ⟨v, hv'⟩), rfl⟩
private theorem liftedMonomial_mem_pow (I : Ideal (MvPolynomial (Fin 4) k))
    (a h : Shape) (ha : Chamber a) (hh : Chamber h) (i j : ℕ) (m : Fin 4 →₀ ℕ)
    (hm : m ∈ latticeIndices (degreeShape a h (i, j))) (n : ℕ) (hi : n ≤ i) (hj : n ≤ j) :
    liftedMonomial I a h (i, j) m hm ∈ irrelevant I a h ^ n := by
  induction n generalizing i j m with
  | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ n ih =>
    cases i with
    | zero => omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        obtain ⟨u, hu, v, hv, rfl⟩ := splitExponent ha hh (i, j) (1, 1) hm
        rw [Submodule.pow_succ]
        exact (liftedMonomial_add I a h (i, j) (1, 1) hu hv hm).symm ▸
          Ideal.mul_mem_mul (ih i j u hu (by omega) (by omega))
            (liftedMonomial_mem_irrelevant I a h ha hh v hv)
theorem proof : K1_13_6_1_4_2_1_2.c1 := by
  intro k _ I a h ha hh
  refine ⟨rees_noetherian I a h ha hh, ?_⟩
  intro i j x hx n hi hj
  exact homogeneous_mem I a h (i, j) ((irrelevant I a h ^ n).restrictScalars k)
    (fun m hm => liftedMonomial_mem_pow I a h ha hh i j m hm n hi hj) x hx
end
end K1_13_6_1_4_2_1_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_2
noncomputable section
open K1_13 K1_13_6_1_4_3_3 MvPolynomial
open scoped TensorProduct
section Coefficients
variable {k : Type} [Field k] (P : Fin 4 → Shape) (f : Fin 4 → Jets k)
private abbrev CoeffIndex := Σ i : Fin 4, lattice (P i)
private def center (a : CoeffIndex P) : k :=
  (f a.1).coeff a.2.1
private def coeffLine (a : CoeffIndex P) : Polynomial (CoefficientField k P) :=
  Polynomial.C (algebraMap k (CoefficientField k P) (center P f a)) +
    Polynomial.X * Polynomial.C
      (algebraMap (CoefficientRing k P) (CoefficientField k P) (MvPolynomial.X a))
def deformation (i : Fin 4) : K1_13_5_4_2_4_1.Total (CoefficientField k P) := by
  classical
  letI := (lattice_finite (P i)).fintype
  exact ∑ e : lattice (P i), monomial e.val (coeffLine P f ⟨i, e⟩)
private def coeffLineHom : CoefficientRing k P →+* Polynomial (CoefficientField k P) :=
  eval₂Hom (Polynomial.C.comp (algebraMap k (CoefficientField k P))) (coeffLine P f)
private theorem coeffLineHom_injective : Function.Injective (coeffLineHom P f) := by
  let shift : CoefficientRing k P →ₐ[k] CoefficientRing k P :=
    aeval fun a => C (center P f a) + MvPolynomial.X a
  let unshift : CoefficientRing k P →ₐ[k] CoefficientRing k P :=
    aeval fun a => MvPolynomial.X a - C (center P f a)
  have hshift : unshift.comp shift = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro a
    simp [shift, unshift, algebraMap_eq]
  have hleft : Function.LeftInverse unshift shift := fun p => AlgHom.congr_fun hshift p
  have heval : (Polynomial.evalRingHom 1).comp (coeffLineHom P f) =
      (algebraMap (CoefficientRing k P) (CoefficientField k P)).comp shift.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change Polynomial.eval 1 (coeffLineHom P f (C c)) =
        algebraMap (CoefficientRing k P) (CoefficientField k P) (shift (C c))
      rw [coeffLineHom, eval₂Hom_C, RingHom.comp_apply, Polynomial.eval_C, algHom_C]
      exact IsScalarTower.algebraMap_apply k (CoefficientRing k P) (CoefficientField k P) c
    · intro a
      change Polynomial.eval 1 (coeffLineHom P f (MvPolynomial.X a)) =
        algebraMap (CoefficientRing k P) (CoefficientField k P)
          (aeval (fun b => C (center P f b) + MvPolynomial.X b) (MvPolynomial.X a))
      rw [coeffLineHom, MvPolynomial.eval₂Hom_X', aeval_X]
      simp only [coeffLine, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, one_mul, map_add]
      rw [IsScalarTower.algebraMap_apply k (CoefficientRing k P) (CoefficientField k P)]
      rfl
  intro p q hpq
  apply hleft.injective
  apply IsFractionRing.injective (CoefficientRing k P) (CoefficientField k P)
  exact (RingHom.congr_fun heval p).symm.trans
    ((congrArg (Polynomial.evalRingHom 1) hpq).trans (RingHom.congr_fun heval q))
open K1_13_5_4_2_4_1 in
private def genericCoeffMap : CoefficientField k P →+* ParameterField (CoefficientField k P) :=
  IsFractionRing.lift (g := (algebraMap (Polynomial (CoefficientField k P))
      (ParameterField (CoefficientField k P))).comp (coeffLineHom P f))
    ((IsFractionRing.injective (Polynomial (CoefficientField k P)) (ParameterField (CoefficientField k P))).comp
      (coeffLineHom_injective P f))
open K1_13_5_4_2_4_1 in
private theorem genericCoeffMap_coeff (a : CoeffIndex P) :
    genericCoeffMap P f (algebraMap (CoefficientRing k P) (CoefficientField k P) (MvPolynomial.X a)) =
      algebraMap (Polynomial (CoefficientField k P)) (ParameterField (CoefficientField k P))
        (coeffLine P f a) := by
  rw [genericCoeffMap, IsFractionRing.lift_algebraMap]
  simp [coeffLineHom]
open K1_13_5_4_2_4_1 in
theorem deformation_reduce
    (hs : ∀ i, (↑(f i).support : Set Exponent) ⊆ lattice (P i)) (i : Fin 4) :
    reduce (deformation P f i) =
      MvPolynomial.map (algebraMap k (CoefficientField k P)) (f i) := by
  classical
  let := (lattice_finite (P i)).fintype
  ext e
  simp only [deformation, reduce, map_sum, map_monomial, coeff_map, coeff_sum, coeff_monomial, Finsupp.single_apply,
    coeffLine, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, zero_mul, add_zero, center]
  by_cases he : e ∈ lattice (P i)
  · rw [Finset.sum_eq_single (⟨e, he⟩ : lattice (P i))]
    · simp
    · intro a _ ha
      have hne : a.val ≠ e := fun h => ha (Subtype.ext h)
      simp [hne]
    · simp
  · have hcoeff : (f i).coeff e = 0 :=
      notMem_support_iff.mp fun h => he (hs i h)
    rw [hcoeff, map_zero]
    apply Finset.sum_eq_zero
    intro a _
    have hne : a.val ≠ e := fun h => he (h ▸ a.prop)
    simp [hne]
open K1_13_5_4_2_4_1 in
theorem finite_rank_map_ideal {L : Type} [Field L] [Algebra k L]
    (I : Ideal (Jets k)) [Module.Finite k (Jets k ⧸ I)] :
    Module.Finite L (Jets L ⧸ I.map (MvPolynomial.map (algebraMap k L))) ∧
    Module.finrank L (Jets L ⧸ I.map (MvPolynomial.map (algebraMap k L))) =
      Module.finrank k (Jets k ⧸ I) := by
  let e := (baseQuotient (L := L) I).toLinearEquiv
  exact ⟨Module.Finite.equiv e, e.finrank_eq.symm.trans Module.finrank_baseChange⟩
open K1_13_5_4_2_4_1 in
theorem deformation_generic (hf : Module.Finite (CoefficientField k P) (GenericAlgebra k P)) :
    Module.Finite (ParameterField (CoefficientField k P)) (GenericFiber (deformation P f)) ∧
    Module.finrank (ParameterField (CoefficientField k P)) (GenericFiber (deformation P f)) =
      Module.finrank (CoefficientField k P) (GenericAlgebra k P) := by
  let : Algebra (CoefficientField k P) (ParameterField (CoefficientField k P)) :=
    (genericCoeffMap P f).toAlgebra
  have hrow (i : Fin 4) :
      MvPolynomial.map (algebraMap (CoefficientField k P) (ParameterField (CoefficientField k P)))
          (genericEquation k P i) = toGeneric (deformation P f i) := by
    change MvPolynomial.map (genericCoeffMap P f) (genericEquation k P i) = _
    simp [genericEquation, toGeneric, deformation, genericCoeffMap_coeff]
  have hid :
      (CutIdeal (genericEquation k P)).map
          (MvPolynomial.map (algebraMap (CoefficientField k P) (ParameterField (CoefficientField k P)))) =
        (equationsIdeal (deformation P f)).map toGeneric := by
    simp only [CutIdeal, equationsIdeal, Ideal.map_span, ← Set.range_comp', hrow]
  have := hf
  have hbase := finite_rank_map_ideal (L := ParameterField (CoefficientField k P))
    (CutIdeal (genericEquation k P))
  rw [hid] at hbase
  exact hbase
end Coefficients
end
end K1_13_6_1_4_3_3_2
end
section
namespace K1_13_6_1_2
noncomputable section
open Polynomial K1_13 K1_13_6
open scoped BigOperators
def taylorHom {n : ℕ} {A : Type*} [CommSemiring A] :
    MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) (MvPolynomial (Fin n) A) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (fun i => MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i)
private theorem pow_taylor {n : ℕ} {A : Type*} [CommSemiring A] (i : Fin n) (k : ℕ)
    (f : A) :
    (MvPolynomial.C f + MvPolynomial.X i) ^ k =
      ∑ j ∈ Finset.range (k + 1), MvPolynomial.monomial (Finsupp.single i j)
        (f ^ (k - j) * (k.choose j : A)) := by
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [MvPolynomial.X_pow_eq_monomial, ← map_pow, ← MvPolynomial.C_eq_coe_nat,
    mul_assoc, ← map_mul, mul_comm, MvPolynomial.C_mul_monomial, mul_one]
private theorem taylor_monomial_coeff {n : ℕ} {A : Type*} [CommSemiring A]
    (m a : Fin n →₀ ℕ) (c : A) :
    (taylorHom (MvPolynomial.monomial m c)).coeff a =
      MvPolynomial.monomial (m - a) (c * ∏ i : Fin n, ((m i).choose (a i) : A)) := by
  classical
  unfold taylorHom
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_pow, RingHom.comp_apply,
    MvPolynomial.coeff_C_mul]
  simp_rw [pow_taylor]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_prod]
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  have hindex (b : Fin n → ℕ) :
      (∑ i : Fin n, Finsupp.single i (b i)) =
        Finsupp.equivFunOnFinite.symm b := by
    simpa using (Finsupp.univ_sum_single (Finsupp.equivFunOnFinite.symm b))
  simp_rw [hindex]
  by_cases ha : ∀ i, a i ≤ m i
  · have hmem : (a : Fin n → ℕ) ∈ Fintype.piFinset (fun i => Finset.range (m i + 1)) :=
      Fintype.mem_piFinset.mpr fun i => Finset.mem_range_succ_iff.mpr (ha i)
    rw [Finset.sum_eq_single_of_mem (a : Fin n → ℕ) hmem]
    · have hea : Finsupp.equivFunOnFinite.symm (a : Fin n → ℕ) = a :=
        Finsupp.equivFunOnFinite.symm_apply_apply a
      simp only [hea, ↓reduceIte]
      rw [MvPolynomial.monomial_eq, Finsupp.prod_pow, map_mul, map_prod,
        Finset.prod_mul_distrib]
      simp only [Finsupp.tsub_apply, map_natCast]
      ac_rfl
    · intro b _ hb
      have hba : Finsupp.equivFunOnFinite.symm b ≠ a := by
        intro h
        exact hb (by simpa using congrArg (fun x : Fin n →₀ ℕ => (x : Fin n → ℕ)) h)
      simp [hba]
  · push Not at ha
    obtain ⟨i, hi⟩ := ha
    have hzero : (∏ k : Fin n, ((m k).choose (a k) : A)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.choose_eq_zero_of_lt hi])
    rw [hzero, mul_zero, map_zero]
    suffices (∑ b ∈ Fintype.piFinset (fun i => Finset.range (m i + 1)),
        if Finsupp.equivFunOnFinite.symm b = a then
          ∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) A) ^ (m i - b i) *
            ((m i).choose (b i) : MvPolynomial (Fin n) A) else 0) = 0 by
      rw [this, mul_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have hn : Finsupp.equivFunOnFinite.symm b ≠ a := by
      intro h
      have hbi := Fintype.mem_piFinset.mp hb i
      have he : b i = a i := by
        simpa using congrArg (fun x : Fin n →₀ ℕ => x i) h
      exact (not_lt_of_ge (Finset.mem_range_succ_iff.mp (he ▸ hbi))) hi
    simp [hn]
theorem taylor_coeff {n : ℕ} {A : Type*} [CommSemiring A] (F : MvPolynomial (Fin n) A)
    (a : Fin n →₀ ℕ) : (taylorHom F).coeff a = hassePartial a F := by
  unfold hassePartial
  conv_lhs => rw [MvPolynomial.as_sum F, map_sum, MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun m _ => taylor_monomial_coeff m a (F.coeff m)
theorem map_hassePartial {n : ℕ} {A B : Type*} [CommSemiring A] [CommSemiring B]
    (φ : A →+* B) (a : Fin n →₀ ℕ) (P : MvPolynomial (Fin n) A) :
    MvPolynomial.map φ (hassePartial a P) = hassePartial a (MvPolynomial.map φ P) := by
  have h : (MvPolynomial.map (MvPolynomial.map φ)).comp (taylorHom (n := n)) =
      (taylorHom (A := B)).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [taylorHom]
  have hc := congrArg (fun F : MvPolynomial (Fin n) (MvPolynomial (Fin n) B) => F.coeff a)
    (RingHom.congr_fun h P)
  simpa only [RingHom.comp_apply, MvPolynomial.coeff_map, taylor_coeff] using hc
theorem atJet_hassePartial {n : ℕ} (a : Fin n →₀ ℕ) (P : Row n) (S : (Polynomial Geom)) :
    atJet (hassePartial a P) S = (shiftJet P S).coeff a := by
  let e : Row n →+* (Polynomial Geom) := MvPolynomial.eval (jet S)
  let shift : Row n →+* Row n :=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i))
  have h : (MvPolynomial.map e).comp taylorHom = shift := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e, shift, taylorHom]
    · intro i
      simp [e, shift, taylorHom, add_comm]
  change e (hassePartial a P) = (shift P).coeff a
  have hc := congrArg (fun F : Row n => F.coeff a) (RingHom.congr_fun h P)
  simpa only [RingHom.comp_apply, MvPolynomial.coeff_map, taylor_coeff] using hc
private theorem source_support {a : Fin 4 →₀ ℕ} {P : Row 4} {m : Fin 4 →₀ ℕ}
    (hm : m ∈ (hassePartial a P).support) : ∃ v ∈ P.support, m = v - a := by
  classical
  by_contra! h
  apply (MvPolynomial.mem_support_iff.mp hm)
  unfold hassePartial
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro v hv
  simp [MvPolynomial.coeff_monomial, Ne.symm (h v hv)]
private theorem weight_le (w : Fin 4 → ℕ) (v a : Fin 4 →₀ ℕ) :
    (v - a).sum (fun i k => w i * k) ≤ v.sum (fun i k => w i * k) := by
  simp only [Finsupp.sum_fintype _ _ (fun _ => Nat.mul_zero _)]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.sub_le _ _)
theorem hasse_inBox (a : Fin 4 →₀ ℕ) {P : Row 4} {B : Shape}
    (hP : InBox (shape P) B) : InBox (shape (hassePartial a P)) B := by
  refine ⟨?_, ?_, ?_⟩
  · change (hassePartial a P).totalDegree ≤ B.b
    apply Finset.sup_le
    intro m hm
    obtain ⟨v, hv, rfl⟩ := source_support hm
    exact (by simpa only [one_mul] using weight_le (fun _ => 1) v a :
      (v - a).sum (fun _ k => k) ≤ v.sum (fun _ k => k)).trans
      ((MvPolynomial.le_totalDegree hv).trans hP.1)
  · change indexDegree (hassePartial a P) ≤ B.j
    apply Finset.sup_le
    intro m hm
    obtain ⟨v, hv, rfl⟩ := source_support hm
    exact (weight_le Fin.val v a).trans ((Finset.le_sup (f := fun m =>
      m.sum (fun i k => i.val * k)) hv).trans hP.2.1)
  · change (hassePartial a P).degreeOf 3 ≤ B.t
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    obtain ⟨v, hv, rfl⟩ := source_support hm
    exact (Nat.sub_le _ _).trans ((MvPolynomial.le_degreeOf_of_mem_support 3 hv).trans hP.2.2)
theorem hasse_atJet_eq_zero {n : ℕ} {a : Fin n →₀ ℕ} {P : Row n} {S : (Polynomial Geom)} {l : ℕ}
    (ha : multiOrder a < l) (h : OrderAt P S l) : atJet (hassePartial a P) S = 0 := by
  rw [atJet_hassePartial]
  by_contra hn
  exact (not_le_of_gt ha) (h a (MvPolynomial.mem_support_iff.mpr hn))
end
end K1_13_6_1_2
end
section
namespace K1_13_6_1_2
noncomputable section
open K1_13 K1_13_6
def c1 : Prop :=
  ∀ (F G : GeoJets) (p : Ideal GeoJets) (hp : (Ideal.span {F, G}).IsMinimalPrime p),
    F ≠ 0 → IsRelPrime F G →
    cycleLength (Ideal.span {F, G}) p hp.isPrime ≤ (↑(F.totalDegree * G.totalDegree) : ℕ∞)
def c2 : Prop :=
  ∀ (F : GeoJets) (p : Ideal GeoJets) [p.IsPrime] (d : ℕ),
    p.height = 2 →
    (∀ a : Fin 4 →₀ ℕ, multiOrder a < d → hassePartial a F ∈ p) →
    VanishesTo p F d
end
end K1_13_6_1_2
end
section
namespace K1_13_6_1_2_2
noncomputable section
open K1_13_6 K1_13_6_1_2
open MvPolynomial
open scoped BigOperators
private theorem increment_prod_eq_zero {n : ℕ} {B : Type*} [CommRing B]
    {J : Ideal B} {d : ℕ} (hJ : J ^ d = ⊥) {t : Fin n → B} (ht : ∀ i, t i ∈ J)
    (a : Fin n →₀ ℕ) (ha : d ≤ multiOrder a) : (a.prod fun i k => t i ^ k) = 0 := by
  classical
  apply Ideal.mem_bot.mp
  rw [← hJ]
  apply Ideal.pow_le_pow_right ha
  have hp := Ideal.prod_mem_prod (s := a.support)
    (I := fun i => J ^ a i) (x := fun i => t i ^ a i)
    (fun i _ => Ideal.pow_mem_pow (ht i) (a i))
  rw [Finset.prod_pow_eq_pow_sum] at hp
  exact hp
private theorem eval_eq_zero_of_hasse {K B C : Type*} [CommRing K] [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C] [Algebra.FormallySmooth K C] {n : ℕ}
    (φ : MvPolynomial (Fin n) K →ₐ[K] B) (ρ : B →ₐ[K] C) (hρ : Function.Surjective ρ)
    (F : MvPolynomial (Fin n) K) (d : ℕ) (hJ : RingHom.ker ρ.toRingHom ^ d = ⊥)
    (h : ∀ a : Fin n →₀ ℕ, multiOrder a < d → ρ (φ (hassePartial a F)) = 0) :
    φ F = 0 := by
  classical
  let J := RingHom.ker ρ.toRingHom
  have hnil : IsNilpotent J := ⟨d, hJ⟩
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K C) ρ hρ hnil
  have hs (x : C) : ρ (s x) = x :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id K C) ρ hρ hnil x
  let r := ρ.comp φ
  let t (i : Fin n) : B := φ (MvPolynomial.X i) - s (r (MvPolynomial.X i))
  have ht (i : Fin n) : t i ∈ J := by
    change ρ (φ (MvPolynomial.X i) - s (r (MvPolynomial.X i))) = 0
    rw [map_sub, hs]
    exact sub_self _
  let ev : MvPolynomial (Fin n) (MvPolynomial (Fin n) K) →+* B :=
    eval₂Hom (s.toRingHom.comp r.toRingHom) t
  have heval : ev.comp taylorHom = φ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [ev, RingHom.comp_apply, taylorHom, eval₂Hom_C]
      change s (r (MvPolynomial.C c)) = φ (MvPolynomial.C c)
      rw [← MvPolynomial.algebraMap_eq, r.commutes, s.commutes, φ.commutes]
    · intro i
      simp [ev, taylorHom, t]
  have hzero : ev (taylorHom F) = 0 := by
    conv_lhs => rw [MvPolynomial.as_sum (taylorHom F), map_sum]
    apply Finset.sum_eq_zero
    intro a _
    have he : ev (monomial a ((taylorHom F).coeff a)) =
        s (r ((taylorHom F).coeff a)) * (a.prod fun i k => t i ^ k) :=
      eval₂Hom_monomial _ _ _ _
    rw [he]
    by_cases ha : multiOrder a < d
    · have hr : r (hassePartial a F) = 0 := h a ha
      rw [taylor_coeff, hr, map_zero, zero_mul]
    · rw [increment_prod_eq_zero hJ ht a (le_of_not_gt ha), mul_zero]
  exact (RingHom.congr_fun heval F).symm.trans hzero
private theorem local_mem_pow_of_hasse {K A : Type*} [CommRing K] [CommRing A]
    [Algebra K A] [IsLocalRing A] [Algebra.FormallySmooth K (IsLocalRing.ResidueField A)]
    {n : ℕ} (loc : MvPolynomial (Fin n) K →ₐ[K] A) (F : MvPolynomial (Fin n) K) (d : ℕ)
    (h : ∀ a : Fin n →₀ ℕ, multiOrder a < d → loc (hassePartial a F) ∈ IsLocalRing.maximalIdeal A) :
    loc F ∈ IsLocalRing.maximalIdeal A ^ d := by
  by_cases hd : d = 0
  · simp [hd, Ideal.one_eq_top]
  let m := IsLocalRing.maximalIdeal A
  have hm : m ^ d ≤ m := Ideal.pow_le_self hd
  let ρ : (A ⧸ m ^ d) →ₐ[K] IsLocalRing.ResidueField A := Ideal.Quotient.factorₐ K hm
  have hρ : Function.Surjective ρ := Ideal.Quotient.factor_surjective hm
  have hJ : RingHom.ker ρ.toRingHom ^ d = ⊥ := by
    change (RingHom.ker (Ideal.Quotient.factor hm)) ^ d = ⊥
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, Ideal.map_quotient_self]
  let φ := (Ideal.Quotient.mkₐ K (m ^ d)).comp loc
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  refine eval_eq_zero_of_hasse φ ρ hρ F d hJ fun a ha => ?_
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (h a ha)
theorem vanishesTo_of_hasse {K : Type*} [Field K] [PerfectField K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime]
    (d : ℕ) (h : ∀ a : Fin n →₀ ℕ, multiOrder a < d → hassePartial a F ∈ p) :
    VanishesTo p F d := by
  let L := Localization.AtPrime p
  have : Algebra.EssFiniteType (MvPolynomial (Fin n) K) L :=
    .of_isLocalization L p.primeCompl
  have : Algebra.EssFiniteType K L := .comp K (MvPolynomial (Fin n) K) L
  have : Algebra.EssFiniteType K (IsLocalRing.ResidueField L) := by
    change Algebra.EssFiniteType K (L ⧸ IsLocalRing.maximalIdeal L)
    infer_instance
  let loc : MvPolynomial (Fin n) K →ₐ[K] L := IsScalarTower.toAlgHom K _ L
  refine local_mem_pow_of_hasse loc F d fun a ha => ?_
  change algebraMap (MvPolynomial (Fin n) K) L (hassePartial a F) ∈ IsLocalRing.maximalIdeal L
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p)]
  exact Ideal.mem_map_of_mem _ (h a ha)
theorem proof : K1_13_6_1_2.c2 := by
  intro F p hp d _ h
  exact vanishesTo_of_hasse F p d h
end
end K1_13_6_1_2_2
end
section
namespace K1_13_2_3_4
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0
open K1_13_2
private def c4cDen (n : ℕ) : ℕ :=
  if n == 0 then 0 else
    let u := n - 1
    u * (u * (2 * u + 21) + 66) / 72 + 1
private theorem c4cTwiceHalf (n : ℤ) : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
  have h : (2 : ℤ) ∣ n * (n - 1) := by
    rcases Int.emod_two_eq_zero_or_one n with hn | hn
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ n) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ n - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem c4cDenPoly (u : ℤ) (hu : 0 ≤ u) :
    u * (u * (2 * u + 21) + 66) / 72 + 1 = denominator u := by
  rw [denominator, ite_eq_right (by omega)]
  let q := u / 6
  let r := u % 6
  let p := u * (u * (2 * u + 21) + 66)
  let v := 1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)
  change p / 72 + 1 = v
  suffices p + 47 ≤ 72 * v ∧ 72 * v ≤ p + 72 by omega
  have he : u = 6 * q + r := by dsimp [q, r]; omega
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by
    dsimp [r]
    omega
  have hq := c4cTwiceHalf q
  unfold p v
  rw [he]
  rcases hr with h | h | h | h | h | h <;> rw [h] <;> norm_num <;>
    constructor <;> nlinarith only [hq]
private theorem c4cDenEq (n : ℕ) :
    (c4cDen n : ℤ) = denominator ((n : ℤ) - 1) := by
  cases n with
  | zero => decide
  | succ n =>
    rw [c4cDen, ite_eq_right (by simp), Nat.succ_sub_one]
    push_cast
    rw [show (n : ℤ) + 1 - 1 = n by omega]
    exact c4cDenPoly n (by omega)
private theorem c4cDenSub (n k : ℕ) :
    (c4cDen (n - k) : ℤ) = denominator ((n : ℤ) - 1 - k) := by
  rw [c4cDenEq]
  by_cases h : k ≤ n
  · rw [Int.ofNat_sub h]
    congr 1
    omega
  · have hz : n - k = 0 := by omega
    simp [hz, denominator, show (n : ℤ) - 1 - k < 0 by omega]
private theorem c4cDenNeg (u : ℤ) (h : u < 0) : denominator u = 0 := by
  simp [denominator, h]
private theorem c4cCumNeg (d u : ℤ) (h : u < 0) : cumulative d u = 0 := by
  simp [cumulative, h]
private theorem c4cCumSmall (d u : ℤ) (h : u < d + 1) :
    cumulative d u = denominator u := by
  by_cases hu : u < 0
  · rw [c4cCumNeg _ _ hu, c4cDenNeg _ hu]
  have hd : ¬ d < 0 := by omega
  simp (disch := omega) [cumulative, hu, hd, c4cDenNeg]
private def c4cChart (s q k : ℤ) : Flag :=
  ⟨1650 - 3*k, s - 1350 - q - 2*k, 1650 - 3*k, 550 - k, 1650 - q - 3*k⟩
private theorem c4cCap (d u c : ℤ) (hc : 0 ≤ c) (hu : u ≤ d) (hd : d ≤ 3*c) :
    cappedCount d u c = denominator u := by
  rw [cappedCount, ite_eq_right (by omega), c4cCumNeg (d - c - 1) (u - 3*(c + 1)) (by omega),
    sub_zero, c4cCumSmall d u (by omega)]
private theorem c4cCounts (s q k : ℤ) (hs₀ : 1866 ≤ s) (hs₁ : s ≤ 1942)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 70) (hk₀ : 0 ≤ k) (hk₁ : k ≤ 300) :
    oldCount (c4cChart s q k) =
      denominator (1650 - 3*k) - denominator (s - 1350 - q - 2*k - 1) ∧
    kernelLower (c4cChart s q k) =
      denominator (1650 - 3*k) - denominator (s - 1350 - q - 2*k - 1) -
        denominator (1650 - q - 3*k - 1) := by
  let d := 1650 - 3*k
  let l := s - 1350 - q - 2*k
  let o := 1650 - q - 3*k
  let c := 550 - k
  let r := min d ((o - 1 - l + d) / 4) + 1
  have hr : r = (4649 - s) / 4 - k + 1 := by dsimp [r, d, o, l]; omega
  have hc : 0 ≤ c := by dsimp [c]; omega
  have hd : 0 ≤ d := by dsimp [d]; omega
  have hcap : d ≤ 3*c := by dsimp [d, c]; omega
  have hl : l - 1 ≤ d := by dsimp [d, l]; omega
  have hold : oldCount (c4cChart s q k) = denominator d - denominator (l - 1) := by
    change cappedCount d d c - cappedCount d (min d (l - 1)) c = _
    rw [min_eq_right hl, c4cCap _ _ _ hc (le_refl _) hcap, c4cCap _ _ _ hc hl hcap]
  refine ⟨hold, ?_⟩
  have ht : targetCount (c4cChart s q k) = denominator (o - 1) := by
    change (if o - 1 - l + d < 0 then 0 else cumulative d (o - 1) -
      cumulative (d - r) (o - 1 - 3*r) - cumulative d (l - 1) +
      cumulative (d - r) (l - 1)) = _
    rw [ite_eq_right (by dsimp [o, l, d]; omega),
      c4cCumNeg (d - r) (o - 1 - 3*r) (by rw [hr]; dsimp [o]; omega),
      c4cCumSmall d (o - 1) (by dsimp [o, d]; omega), c4cCumSmall d (l - 1) (by omega),
      c4cCumSmall (d - r) (l - 1) (by rw [hr]; dsimp [d, l]; omega), sub_zero, sub_add_cancel]
  change (if d < 0 || d < 0 || c < 0 then 0 else
    oldCount (c4cChart s q k) - targetCount (c4cChart s q k)) = _
  simp only [not_lt.mpr hd, not_lt.mpr hc, decide_false, Bool.false_or,
    Bool.false_eq_true, ite_false, hold, ht]
  rfl
private def c4cOld (s q k : ℕ) : ℕ :=
  c4cDen (1651 - 3*k) - c4cDen (s - (1350 + q + 2*k))
private def c4cPositive (s q k : ℕ) : ℕ :=
  c4cOld s q k - c4cDen (1650 - (q + 3*k))
private theorem c4cNatCounts (s q k : ℕ) (hs₀ : 1866 ≤ s) (hs₁ : s ≤ 1942)
    (hq : q ≤ 70) (hk : k ≤ 300) :
    (oldCount (c4cChart s q k)).toNat = c4cOld s q k ∧
    (kernelLower (c4cChart s q k)).toNat = c4cPositive s q k := by
  obtain ⟨ho, hp⟩ := c4cCounts s q k (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have hu : (c4cDen (1651 - 3*k) : ℤ) = denominator (1650 - 3*(k : ℤ)) := by
    rw [c4cDenSub]
    push_cast
    congr 1
  have hl : (c4cDen (s - (1350 + q + 2*k)) : ℤ) =
      denominator ((s : ℤ) - 1350 - q - 2*k - 1) := by
    rw [c4cDenSub]
    push_cast
    congr 1
    omega
  have ht : (c4cDen (1650 - (q + 3*k)) : ℤ) =
      denominator (1650 - (q : ℤ) - 3*k - 1) := by
    rw [c4cDenSub]
    push_cast
    congr 1
    omega
  rw [ho, hp, ← hu, ← hl, ← ht]
  unfold c4cPositive c4cOld
  omega
private theorem c4cSaving (a b c : ℤ) :
    (a - max 0 b).toNat - (a - max (max 0 b) c).toNat =
      min a.toNat c.toNat - b.toNat := by
  omega
private def c4cEntry (s q k : ℕ) : ℕ :=
  if k = 0 then 0 else if k ≤ 300 then
    min (c4cOld s q 0) (c4cPositive s q k) - c4cPositive s q 0
  else entry s q k
private theorem c4cEntryEq (s q k : ℕ) (hs₀ : 1866 ≤ s) (hs₁ : s ≤ 1942)
    (hq : q ≤ 70) : entry s q k = c4cEntry s q k := by
  let j := 3000 + q - s
  have hj : 993 ≤ j ∧ j ≤ 1581 := by dsimp [j]; omega
  by_cases hz : k = 0
  · simp [entry, cubicSavings, c4cEntry, hz]
  by_cases hk : k ≤ 300
  · have hw : windowFlag s j = c4cChart s q 0 := by
      unfold windowFlag c4cChart
      dsimp [j]
      congr 1 <;> omega
    have hr : cubicFlag (c4cChart s q 0) k = c4cChart s q k := by
      unfold cubicFlag c4cChart
      congr 1 <;> (try dsimp) <;> omega
    have h₀ := c4cNatCounts s q 0 hs₀ hs₁ hq (by decide)
    simp only [Nat.cast_zero] at h₀
    have h₁ := c4cNatCounts s q k hs₀ hs₁ hq hk
    change (if 993 ≤ j ∧ j ≤ 1581 then cubicSavings s j k else 0) = _
    rw [ite_eq_left hj, cubicSavings, ite_eq_right hz, c4cEntry, ite_eq_right hz, ite_eq_left hk]
    try dsimp only
    rw [hw, hr, c4cSaving, h₀.1, h₀.2, h₁.2]
  · simp only [c4cEntry, ite_eq_right hz, ite_eq_right hk]
private def c4cRow (s q code : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => c4cEntry s q (code % 512) + c4cRow s (q + 1) (code / 512) n
private theorem c4cRowEq (s q code n : ℕ) (hs₀ : 1866 ≤ s) (hs₁ : s ≤ 1942)
    (hq : q + n ≤ 71) : rowSum s q code n = c4cRow s q code n := by
  induction n generalizing q code with
  | zero => rfl
  | succ n ih =>
    rw [rowSum, c4cRow, c4cEntryEq _ _ _ hs₀ hs₁ (by omega),
      ih (q + 1) (code / 512) (by omega)]
private theorem c4cCheck {s code v : ℕ} (hs₀ : 1866 ≤ s) (hs₁ : s ≤ 1942)
    (hv : c4cRow s 0 code 71 = v) :
    [code].length = 1 ∧ rowsSum s [code] = v := by
  refine ⟨rfl, ?_⟩
  change rowSum s 0 code 71 + 0 = v
  rw [Nat.add_zero, c4cRowEq s 0 code 71 hs₀ hs₁ (by decide), hv]
private def rowsC1_row000 : List ℕ := [0x30403020130c06c4023140c0603420100804424130c06030180c86836201008040a1918904c26180c06030180c2643420100]
private theorem rowsC1_row000_checked :
    rowsC1_row000.length = 1 ∧ rowsSum 1866 rowsC1_row000 = 28404388 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row001 : List ℕ := [0x40403020140c0704024180c0603420100824624140c06030180c86836201008040a1918904c28180c06030180c2663420100]
private theorem rowsC1_row001_checked :
    rowsC1_row001.length = 1 ∧ rowsSum 1867 rowsC1_row001 = 28636056 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row002 : List ℕ := [0x2050483020180c0804024180c0623420100844626140c06030184cc683820100804122118904c28180c06030180c3663420100]
private theorem rowsC1_row002_checked :
    rowsC1_row002.length = 1 ∧ rowsSum 1868 rowsC1_row002 = 28875231 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row003 : List ℕ := [0x2060483422180c8804226180c0623620100844626140c06030184cc6c38201008041a2118904c28180c06030180c4663420100]
private theorem rowsC1_row003_checked :
    rowsC1_row003.length = 1 ∧ rowsSum 1869 rowsC1_row003 = 29121059 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row004 : List ℕ := [0x4060503824180d0804426180c0643620100864826180c06030188cc6c40201008041a2118904c28180c06030180c4663620100]
private theorem rowsC1_row004_checked :
    rowsC1_row004.length = 1 ∧ rowsSum 1870 rowsC1_row004 = 29305336 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row005 : List ℕ := [0x6070604024180d0804426180c0663620100864826180c06030188cc6c4020100804222120904c30180c06030180c4663620100]
private theorem rowsC1_row005_checked :
    rowsC1_row005.length = 1 ∧ rowsSum 1871 rowsC1_row005 = 29479343 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row006 : List ℕ := [0x6080604026180d8804628180c0663820100884826180c0603018cd06c4020100804222120904c30180c06030180c6663620100]
private theorem rowsC1_row006_checked :
    rowsC1_row006.length = 1 ∧ rowsSum 1872 rowsC1_row006 = 29714183 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row007 : List ℕ := [0x8080604028180e0804828180c0684020100884826180c06030190d06c4020100804223120984c30180c06030180c6663620100]
private theorem rowsC1_row007_checked :
    rowsC1_row007.length = 1 ∧ rowsSum 1873 rowsC1_row007 = 29944623 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row008 : List ℕ := [0x40a08060403018100804830180c06840201048c4826180c06030190d06c4020100814323120984c30180c06030180c6683620100]
private theorem rowsC1_row008_checked :
    rowsC1_row008.length = 1 ∧ rowsSum 1874 rowsC1_row008 = 30174338 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row009 : List ℕ := [0x40c09068443019100844830180c46c40201088c4c28180c06030190d06c4020100814323120984c30180c06030180c6683620100]
private theorem rowsC1_row009_checked :
    rowsC1_row009.length = 1 ∧ rowsSum 1875 rowsC1_row009 = 30418119 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1 : List ℕ :=
  rowsC1_row000 ++ rowsC1_row001 ++ rowsC1_row002 ++ rowsC1_row003
    ++ rowsC1_row004 ++ rowsC1_row005 ++ rowsC1_row006 ++ rowsC1_row007
    ++ rowsC1_row008 ++ rowsC1_row009
private theorem rowsC1_checked :
    rowsC1.length = 10 ∧ rowsSum 1866 rowsC1 = 294072676 := by
  constructor <;> simp only [rowsC1, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC1_row000_checked.1, rowsC1_row000_checked.2, rowsC1_row001_checked.1, rowsC1_row001_checked.2,
    rowsC1_row002_checked.1, rowsC1_row002_checked.2, rowsC1_row003_checked.1, rowsC1_row003_checked.2,
    rowsC1_row004_checked.1, rowsC1_row004_checked.2, rowsC1_row005_checked.1, rowsC1_row005_checked.2,
    rowsC1_row006_checked.1, rowsC1_row006_checked.2, rowsC1_row007_checked.1, rowsC1_row007_checked.2,
    rowsC1_row008_checked.1, rowsC1_row008_checked.2, rowsC1_row009_checked.1, rowsC1_row009_checked.2]
private def rowsC2_row000 : List ℕ := [0x80c0a070483019100844c30180c86c40201088c4c28180c06030998d0704020100824323120984c30180c06030180c8683620100]
private theorem rowsC2_row000_checked :
    rowsC2_row000.length = 1 ∧ rowsSum 1876 rowsC2_row000 = 30664326 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row001 : List ℕ := [0xc0c0c08048301a100884c30180c86c402010c904c30180c06030998d8704020100824423120985030180c06030182c8683620100]
private theorem rowsC2_row001_checked :
    rowsC2_row001.length = 1 ∧ rowsSum 1877 rowsC2_row001 = 30888547 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row002 : List ℕ := [0xc100c0804c301b1008c4c30180cc704020110904c30180c06031198d8804020100834423120985030180c06030182c8683620100]
private theorem rowsC2_row002_checked :
    rowsC2_row002.length = 1 ∧ rowsSum 1878 rowsC2_row002 = 31120790 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row003 : List ℕ := [0x10100c0804c301b1008c5030180d0704020110904c30180c060319a0d8804020100834423120985030180c06030184c8683620100]
private theorem rowsC2_row003_checked :
    rowsC2_row003.length = 1 ∧ rowsSum 1879 rowsC2_row003 = 31376287 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row004 : List ℕ := [0x814100c080603020100906030180d0804020910904c30180c060319a0d8804020100844424120985030180c06030184c8683620100]
private theorem rowsC2_row004_checked :
    rowsC2_row004.length = 1 ∧ rowsSum 1880 rowsC2_row004 = 31616683 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row005 : List ℕ := [0x818120d088603220108906030188d0804020918904c30180c060321a0d8804020100844424120986030180c06030186cc683620100]
private theorem rowsC2_row005_checked :
    rowsC2_row005.length = 1 ∧ rowsSum 1881 rowsC2_row005 = 31804404 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row006 : List ℕ := [0x1018140e088603220108986030188d8804021118985030180c060321a0d8804020100864624130986030180c06030188cc683620100]
private theorem rowsC2_row006_checked :
    rowsC2_row006.length = 1 ∧ rowsSum 1882 rowsC2_row006 = 32048882 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row007 : List ℕ := [0x18181810090603420110986030190d8804021118985030180c061331a0e0804020102864624130986030180c06030188cc683620100]
private theorem rowsC2_row007_checked :
    rowsC2_row007.length = 1 ∧ rowsSum 1883 rowsC2_row007 = 32294911 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row008 : List ℕ := [0x18201810098603620118986030198d8804021920986030180c061331b0e0804020104864624130986030180c06030188cc684020100]
private theorem rowsC2_row008_checked :
    rowsC2_row008.length = 1 ∧ rowsSum 1884 rowsC2_row008 = 32492899 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row009 : List ℕ := [0x20201810098603620118a06030198e0804022120986030180c062331b0e0804020104884624130986030180c0603018ccc6c4020100]
private theorem rowsC2_row009_checked :
    rowsC2_row009.length = 1 ∧ rowsSum 1885 rowsC2_row009 = 32746505 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2 : List ℕ :=
  rowsC2_row000 ++ rowsC2_row001 ++ rowsC2_row002 ++ rowsC2_row003
    ++ rowsC2_row004 ++ rowsC2_row005 ++ rowsC2_row006 ++ rowsC2_row007
    ++ rowsC2_row008 ++ rowsC2_row009
private theorem rowsC2_checked :
    rowsC2.length = 10 ∧ rowsSum 1876 rowsC2 = 317054234 := by
  constructor <;> simp only [rowsC2, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC2_row000_checked.1, rowsC2_row000_checked.2, rowsC2_row001_checked.1, rowsC2_row001_checked.2,
    rowsC2_row002_checked.1, rowsC2_row002_checked.2, rowsC2_row003_checked.1, rowsC2_row003_checked.2,
    rowsC2_row004_checked.1, rowsC2_row004_checked.2, rowsC2_row005_checked.1, rowsC2_row005_checked.2,
    rowsC2_row006_checked.1, rowsC2_row006_checked.2, rowsC2_row007_checked.1, rowsC2_row007_checked.2,
    rowsC2_row008_checked.1, rowsC2_row008_checked.2, rowsC2_row009_checked.1, rowsC2_row009_checked.2]
private def rowsC3_row000 : List ℕ := [0x10282018100c0603820120a060301a100804022120986030180c062331b100804020106884624130a06030180c0603018ccc6c4020100]
private theorem rowsC3_row000_checked :
    rowsC3_row000.length = 1 ∧ rowsSum 1886 rowsC3_row000 = 32973215 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row001 : List ℕ := [0x1030241a110c0644020120c060301a100804122120986030180c063341b100804020106884624130a06030180c0603018ccc6c4020100]
private theorem rowsC3_row001_checked :
    rowsC3_row001.length = 1 ∧ rowsSum 1887 rowsC3_row001 = 33225916 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row002 : List ℕ := [0x2030281c110c0644021130c060311b100804123120986030180c064341b100804020108884624130a06030180c0603018cd06c4020100]
private theorem rowsC3_row002_checked :
    rowsC3_row002.length = 1 ∧ rowsSum 1888 rowsC3_row002 = 33489779 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row003 : List ℕ := [0x30303020120c0684022130c060321b100804223130a06030180c064341b100804020108884824130a06030180c06030590d06c4020100]
private theorem rowsC3_row003_checked :
    rowsC3_row003.length = 1 ∧ rowsSum 1889 rowsC3_row003 = 33755809 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row004 : List ℕ := [0x30403020130c0684022130c060321b100804323130a06030180c064341b10080402010c884824130c06030180c06030590d06c4020100]
private theorem rowsC3_row004_checked :
    rowsC3_row004.length = 1 ∧ rowsSum 1890 rowsC3_row004 = 33963460 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row005 : List ℕ := [0x40403020130c06c4023130c060331b100804324130c06030180c266341c10080402050c8c4826130c06030180c06030990d06c4020100]
private theorem rowsC3_row005_checked :
    rowsC3_row005.length = 1 ∧ rowsSum 1891 rowsC3_row005 = 34212972 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row006 : List ℕ := [0x2050403020140c0704024140c060341c100804424130c06030180c466361c10080402050c8c4826130c06030180c06030990d06c4020100]
private theorem rowsC3_row006_checked :
    rowsC3_row006.length = 1 ∧ rowsSum 1892 rowsC3_row006 = 34469951 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row007 : List ℕ := [0x2060483422180c8804024180c0603420100804424130c06030180c466361c10080402090c8c4826130c06030180c06030d90d06c4020100]
private theorem rowsC3_row007_checked :
    rowsC3_row007.length = 1 ∧ rowsSum 1893 rowsC3_row007 = 34710054 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row008 : List ℕ := [0x4060503822180c8804224180c0623420100824624130c06030180c6683620100804020d108c4826130c06030180c06031198d06c4020100]
private theorem rowsC3_row008_checked :
    rowsC3_row008.length = 1 ∧ rowsSum 1894 rowsC3_row008 = 34951171 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3 : List ℕ :=
  rowsC3_row000 ++ rowsC3_row001 ++ rowsC3_row002 ++ rowsC3_row003
    ++ rowsC3_row004 ++ rowsC3_row005 ++ rowsC3_row006 ++ rowsC3_row007
    ++ rowsC3_row008
private theorem rowsC3_checked :
    rowsC3.length = 9 ∧ rowsSum 1886 rowsC3 = 305752327 := by
  constructor <;> simp only [rowsC3, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC3_row000_checked.1, rowsC3_row000_checked.2, rowsC3_row001_checked.1, rowsC3_row001_checked.2,
    rowsC3_row002_checked.1, rowsC3_row002_checked.2, rowsC3_row003_checked.1, rowsC3_row003_checked.2,
    rowsC3_row004_checked.1, rowsC3_row004_checked.2, rowsC3_row005_checked.1, rowsC3_row005_checked.2,
    rowsC3_row006_checked.1, rowsC3_row006_checked.2, rowsC3_row007_checked.1, rowsC3_row007_checked.2,
    rowsC3_row008_checked.1, rowsC3_row008_checked.2]
private def rowsC4_row000 : List ℕ := [0x6070604024180d0804426180c0623620100844624140c06030180c6683620100804020d108c4826140c06030180c06031198d06c4020100]
private theorem rowsC4_row000_checked :
    rowsC4_row000.length = 1 ∧ rowsSum 1895 rowsC4_row000 = 35215060 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row001 : List ℕ := [0x6080604026180d0804426180c0643620100844626140c06030180c86836201008040211108c4826140c06030180c06031198d06c4020100]
private theorem rowsC4_row001_checked :
    rowsC4_row001.length = 1 ∧ rowsSum 1896 rowsC4_row001 = 35482889 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row002 : List ℕ := [0x8080604026180d8804626180c0663620100864826140c06030180c8683620100804021110904826140c06030180c06031998d06c4020100]
private theorem rowsC4_row002_checked :
    rowsC4_row002.length = 1 ∧ rowsSum 1897 rowsC4_row002 = 35752024 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row003 : List ℕ := [0x40a080604028180e0804828180c0663820100884826180c06030184cc683820100804021910904826140c06030180c06031998d06c4020100]
private theorem rowsC4_row003_checked :
    rowsC4_row003.length = 1 ∧ rowsSum 1898 rowsC4_row003 = 35999170 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row004 : List ℕ := [0x80c09068443018100804830180c0684020100884826180c06030188cc6c38201008040a1918904c26180c06030180c06031998d86c4020100]
private theorem rowsC4_row004_checked :
    rowsC4_row004.length = 1 ∧ rowsSum 1899 rowsC4_row004 = 36195310 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row005 : List ℕ := [0x80c0a070443019100844830180c4684020104884826180c06030188cc6c3820100804121918904c26180c06030180c060b1998d8704020100]
private theorem rowsC4_row005_checked :
    rowsC4_row005.length = 1 ∧ rowsSum 1900 rowsC4_row005 = 36479131 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row006 : List ℕ := [0xc0e0c08048301a100884c30180c46c40201048c4826180c0603018cd06c4020100804121918904c26180c06030180c060b21a0d8804020100]
private theorem rowsC4_row006_checked :
    rowsC4_row006.length = 1 ∧ rowsSum 1901 rowsC4_row006 = 36712301 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row007 : List ℕ := [0x10100c0804c301a100884c30180c86c40201088c4c28180c0603018cd06c40201008041a2118904c26180c06030180c061321a0d8804020100]
private theorem rowsC4_row007_checked :
    rowsC4_row007.length = 1 ∧ rowsSum 1902 rowsC4_row007 = 36993294 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row008 : List ℕ := [0x10100c0804c301b1008c4c30180cc6c402010c8c4c28180c06030190d06c40201008041a2118904c26180c06030180c061321a0d8804020100]
private theorem rowsC4_row008_checked :
    rowsC4_row008.length = 1 ∧ rowsSum 1903 rowsC4_row008 = 37262321 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4 : List ℕ :=
  rowsC4_row000 ++ rowsC4_row001 ++ rowsC4_row002 ++ rowsC4_row003
    ++ rowsC4_row004 ++ rowsC4_row005 ++ rowsC4_row006 ++ rowsC4_row007
    ++ rowsC4_row008
private theorem rowsC4_checked :
    rowsC4.length = 9 ∧ rowsSum 1895 rowsC4 = 326091500 := by
  constructor <;> simp only [rowsC4, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC4_row000_checked.1, rowsC4_row000_checked.2, rowsC4_row001_checked.1, rowsC4_row001_checked.2,
    rowsC4_row002_checked.1, rowsC4_row002_checked.2, rowsC4_row003_checked.1, rowsC4_row003_checked.2,
    rowsC4_row004_checked.1, rowsC4_row004_checked.2, rowsC4_row005_checked.1, rowsC4_row005_checked.2,
    rowsC4_row006_checked.1, rowsC4_row006_checked.2, rowsC4_row007_checked.1, rowsC4_row007_checked.2,
    rowsC4_row008_checked.1, rowsC4_row008_checked.2]
private def rowsC5_row000 : List ℕ := [0x814120c08060301c1008c5030180cc70402010c904c28180c06030190d06c4020100804222118904c28180c06030180c061b21a0d8804020100]
private theorem rowsC5_row000_checked :
    rowsC5_row000.length = 1 ∧ rowsSum 1904 rowsC5_row000 = 37531039 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row001 : List ℕ := [0x1018120d088603020100906030180d0704020110904c30180c06030998d06c4020100804222118904c28180c06030180c061b21a0d8804020100]
private theorem rowsC5_row001_checked :
    rowsC5_row001.length = 1 ∧ rowsSum 1905 rowsC5_row001 = 37771999 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row002 : List ℕ := [0x1018140e088603220108906030180d0804020110904c30180c06031198d8704020100814322120904c28180c06030180c062331a0d8804020100]
private theorem rowsC5_row002_checked :
    rowsC5_row002.length = 1 ∧ rowsSum 1906 rowsC5_row002 = 38045448 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row003 : List ℕ := [0x181c1810090603420108986030188d8804020918904c30180c06031198d8704020100814323120984c28180c06030180c062331a0d8804020100]
private theorem rowsC5_row003_checked :
    rowsC5_row003.length = 1 ∧ rowsSum 1907 rowsC5_row003 = 38327971 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row004 : List ℕ := [0x20201810098603420110986030190d8804021118904c30180c060319a0d8804020100824323120984c30180c06030180c063331a0d8804020100]
private theorem rowsC5_row004_checked :
    rowsC5_row004.length = 1 ∧ rowsSum 1908 rowsC5_row004 = 38527726 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row005 : List ℕ := [0x1020201810098603620118986030190d8804021118985030180c060319a0d8804020100824323120984c30180c06030180c063331a0d8804020100]
private theorem rowsC5_row005_checked :
    rowsC5_row005.length = 1 ∧ rowsSum 1909 rowsC5_row005 = 38819639 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row006 : List ℕ := [0x10282418100c0603820118a06030198d8804021918985030180c060321a0d8804020100834423120984c30180c06030180c063331a0d8804020100]
private theorem rowsC5_row006_checked :
    rowsC5_row006.length = 1 ∧ rowsSum 1910 rowsC5_row006 = 39111484 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row007 : List ℕ := [0x2030241a110c0644020120a060301a0e0804022120986030180c060321a0d8804020100844423120984c30180c06030180c163331a0d8804020100]
private theorem rowsC5_row007_checked :
    rowsC5_row007.length = 1 ∧ rowsSum 1911 rowsC5_row007 = 39380995 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row008 : List ℕ := [0x3030301c120c0644021120c060301a100804022120986030180c061331a0d8804020100844423120984c30180c06030180c164331b0d8804020100]
private theorem rowsC5_row008_checked :
    rowsC5_row008.length = 1 ∧ rowsSum 1912 rowsC5_row008 = 39661353 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5 : List ℕ :=
  rowsC5_row000 ++ rowsC5_row001 ++ rowsC5_row002 ++ rowsC5_row003
    ++ rowsC5_row004 ++ rowsC5_row005 ++ rowsC5_row006 ++ rowsC5_row007
    ++ rowsC5_row008
private theorem rowsC5_checked :
    rowsC5.length = 9 ∧ rowsSum 1904 rowsC5 = 347177654 := by
  constructor <;> simp only [rowsC5, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC5_row000_checked.1, rowsC5_row000_checked.2, rowsC5_row001_checked.1, rowsC5_row001_checked.2,
    rowsC5_row002_checked.1, rowsC5_row002_checked.2, rowsC5_row003_checked.1, rowsC5_row003_checked.2,
    rowsC5_row004_checked.1, rowsC5_row004_checked.2, rowsC5_row005_checked.1, rowsC5_row005_checked.2,
    rowsC5_row006_checked.1, rowsC5_row006_checked.2, rowsC5_row007_checked.1, rowsC5_row007_checked.2,
    rowsC5_row008_checked.1, rowsC5_row008_checked.2]
private def rowsC6_row000 : List ℕ := [0x30383020120c0684021130c060311a100804122120986030180c062331b0e0804020100844424120985030180c06030180c264341b0d8804020101]
private theorem rowsC6_row000_checked :
    rowsC6_row000.length = 1 ∧ rowsSum 1913 rowsC6_row000 = 39942270 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row001 : List ℕ := [0x40403020130c0684022130c060321b100804123120986030180c062331b0e0804020102864424120985030180c06030180c264341b0e0804020102]
private theorem rowsC6_row001_checked :
    rowsC6_row001.length = 1 ∧ rowsSum 1914 rowsC6_row001 = 40226680 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row002 : List ℕ := [0x2040403020140c06c4023130c060321b100804223130a06030180c063341b100804020102864624120985030180c06030180c364341b100804020102]
private theorem rowsC6_row002_checked :
    rowsC6_row002.length = 1 ∧ rowsSum 1915 rowsC6_row002 = 40455650 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row003 : List ℕ := [0x2060483420180c0704023140c060331b100804323130a06030180c063341b100804020104864624130985030180c06030180c464341b100804020103]
private theorem rowsC6_row003_checked :
    rowsC6_row003.length = 1 ∧ rowsSum 1916 rowsC6_row003 = 40745788 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row004 : List ℕ := [0x4060503422180c8804024140c060341c100804324130a06030180c064341b100804020106884624130986030180c06030180c466341b100804020103]
private theorem rowsC6_row004_checked :
    rowsC6_row004.length = 1 ∧ rowsSum 1917 rowsC6_row004 = 40973542 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row005 : List ℕ := [0x6060603824180c8804224180c0603420100804424130c06030180c264341b100804020106884624130986030180c06030180c466341b100804020104]
private theorem rowsC6_row005_checked :
    rowsC6_row005.length = 1 ∧ rowsSum 1918 rowsC6_row005 = 41234803 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row006 : List ℕ := [0x6080604024180d0804226180c0623420100824424130c06030180c266341b100804020108884624130986030180c06030180c666341b100804020104]
private theorem rowsC6_row006_checked :
    rowsC6_row006.length = 1 ∧ rowsSum 1919 rowsC6_row006 = 41539927 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row007 : List ℕ := [0x8080604026180d8804426180c0643620100824624130c06030180c466361c100804020108884624130986030180c06030180c666341b100804020104]
private theorem rowsC6_row007_checked :
    rowsC6_row007.length = 1 ∧ rowsSum 1920 rowsC6_row007 = 41847978 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6 : List ℕ :=
  rowsC6_row000 ++ rowsC6_row001 ++ rowsC6_row002 ++ rowsC6_row003
    ++ rowsC6_row004 ++ rowsC6_row005 ++ rowsC6_row006 ++ rowsC6_row007
private theorem rowsC6_checked :
    rowsC6.length = 8 ∧ rowsSum 1913 rowsC6 = 326966638 := by
  constructor <;> simp only [rowsC6, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC6_row000_checked.1, rowsC6_row000_checked.2, rowsC6_row001_checked.1, rowsC6_row001_checked.2,
    rowsC6_row002_checked.1, rowsC6_row002_checked.2, rowsC6_row003_checked.1, rowsC6_row003_checked.2,
    rowsC6_row004_checked.1, rowsC6_row004_checked.2, rowsC6_row005_checked.1, rowsC6_row005_checked.2,
    rowsC6_row006_checked.1, rowsC6_row006_checked.2, rowsC6_row007_checked.1, rowsC6_row007_checked.2]
private def rowsC7_row000 : List ℕ := [0x40a080604028180d8804626180c0643620100844624130c06030180c466361c10080402050c884824130a06030180c06030182c666341b100804020106]
private theorem rowsC7_row000_checked :
    rowsC7_row000.length = 1 ∧ rowsSum 1921 rowsC7_row000 = 42158211 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row001 : List ℕ := [0x80c090684430180e0804628180c0663620100864626140c06030180c668362010080402050c8c4824130a06030180c06030182c666341b100804020106]
private theorem rowsC7_row001_checked :
    rowsC7_row001.length = 1 ∧ rowsSum 1922 rowsC7_row001 = 42435804 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row002 : List ℕ := [0x80c0a068443019100804828180c0663820100864826140c06030180c868362010080402090c8c4826130a06030180c06030184c866341b100804020106]
private theorem rowsC7_row002_checked :
    rowsC7_row002.length = 1 ∧ rowsSum 1923 rowsC7_row002 = 42727099 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row003 : List ℕ := [0xc0e0c080483019100844830180c0684020100884826180c06030180c868362010080402090c8c4826130a06030180c06030184c868361b100804020106]
private theorem rowsC7_row003_checked :
    rowsC7_row003.length = 1 ∧ rowsSum 1924 rowsC7_row003 = 42983291 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row004 : List ℕ := [0x10100c08048301a100884c30180c4684020100884826180c06030184c8683620100804020d108c4826130c06030180c06030186c868361b100804020108]
private theorem rowsC7_row004_checked :
    rowsC7_row004.length = 1 ∧ rowsSum 1925 rowsC7_row004 = 43217928 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row005 : List ℕ := [0x810100c0804c301b100884c30180c86c40201048c4826180c06030184cc6836201008040211108c4826130c06030180c06030186c868361c100804020108]
private theorem rowsC7_row005_checked :
    rowsC7_row005.length = 1 ∧ rowsSum 1926 rowsC7_row005 = 43524631 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row006 : List ℕ := [0x814120c08050301b1008c4c30180c86c40201088c4826180c06030188cc6c38201008040211108c4826130c06030180c06030188c868361c100804020108]
private theorem rowsC7_row006_checked :
    rowsC7_row006.length = 1 ∧ rowsSum 1927 rowsC7_row006 = 43833918 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row007 : List ℕ := [0x1018120d08860301c100905030180cc6c40201088c4c28180c0603018ccc6c38201008040211108c4826130c06030180c06030188cc683620100804020108]
private theorem rowsC7_row007_checked :
    rowsC7_row007.length = 1 ∧ rowsSum 1928 rowsC7_row007 = 44105101 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7 : List ℕ :=
  rowsC7_row000 ++ rowsC7_row001 ++ rowsC7_row002 ++ rowsC7_row003
    ++ rowsC7_row004 ++ rowsC7_row005 ++ rowsC7_row006 ++ rowsC7_row007
private theorem rowsC7_checked :
    rowsC7.length = 8 ∧ rowsSum 1921 rowsC7 = 344985983 := by
  constructor <;> simp only [rowsC7, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC7_row000_checked.1, rowsC7_row000_checked.2, rowsC7_row001_checked.1, rowsC7_row001_checked.2,
    rowsC7_row002_checked.1, rowsC7_row002_checked.2, rowsC7_row003_checked.1, rowsC7_row003_checked.2,
    rowsC7_row004_checked.1, rowsC7_row004_checked.2, rowsC7_row005_checked.1, rowsC7_row005_checked.2,
    rowsC7_row006_checked.1, rowsC7_row006_checked.2, rowsC7_row007_checked.1, rowsC7_row007_checked.2]
private def rowsC8_row000 : List ℕ := [0x1818140e088603220100906030180cc70402010c8c4c28180c0603018cd06c40201008040a1910904826140c06030180c0603018ccc683620100804020108]
private theorem rowsC8_row000_checked :
    rowsC8_row000.length = 1 ∧ rowsSum 1929 rowsC8_row000 = 44390104 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row001 : List ℕ := [0x181c1810090603420108906030180d0804020110904c28180c06030190d06c4020100804121918904826140c06030180c0603018ccc683620100804020108]
private theorem rowsC8_row001_checked :
    rowsC8_row001.length = 1 ∧ rowsSum 1930 rowsC8_row001 = 44705169 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row002 : List ℕ := [0x20201810098603420110986030188d0804020110904c30180c06030190d06c4020100804121918904c26140c06030180c0603058ccc68362010080402010c]
private theorem rowsC8_row002_checked :
    rowsC8_row002.length = 1 ∧ rowsSum 1931 rowsC8_row002 = 45006648 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row003 : List ℕ := [0x1028201810098603620110986030190d8804020910904c30180c06030998d06c40201008041a2118904c26140c06030180c0603058ccc68362010080402010c]
private theorem rowsC8_row003_checked :
    rowsC8_row003.length = 1 ∧ rowsSum 1932 rowsC8_row003 = 45312877 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row004 : List ℕ := [0x2030241a100c0603620118986030190d8804021118904c30180c06031198d07040201008041a2118904c26180c06030180c06030990cc68362010080402010c]
private theorem rowsC8_row004_checked :
    rowsC8_row004.length = 1 ∧ rowsSum 1933 rowsC8_row004 = 45547060 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row005 : List ℕ := [0x2030281a110c0604020120a06030198d8804021118985030180c06031198d8704020100804222118904c26180c06030180c06030d90cc68362010080402010c]
private theorem rowsC8_row005_checked :
    rowsC8_row005.length = 1 ∧ rowsSum 1934 rowsC8_row005 = 45856919 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row006 : List ℕ := [0x3038301c120c0644021120c06030198e0804021918985030180c06031998d8704020100804222118904c26180c06030180c06030d90d06c362010080402030c]
private theorem rowsC8_row006_checked :
    rowsC8_row006.length = 1 ∧ rowsSum 1935 rowsC8_row006 = 46164340 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row007 : List ℕ := [0x40403020120c0684021120c060301a100804022120985030180c060319a0d8804020100814322120904c26180c06030180c06031190d06c362010080402030c]
private theorem rowsC8_row007_checked :
    rowsC8_row007.length = 1 ∧ rowsSum 1936 rowsC8_row007 = 46453223 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8 : List ℕ :=
  rowsC8_row000 ++ rowsC8_row001 ++ rowsC8_row002 ++ rowsC8_row003
    ++ rowsC8_row004 ++ rowsC8_row005 ++ rowsC8_row006 ++ rowsC8_row007
private theorem rowsC8_checked :
    rowsC8.length = 8 ∧ rowsSum 1929 rowsC8 = 363436340 := by
  constructor <;> simp only [rowsC8, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC8_row000_checked.1, rowsC8_row000_checked.2, rowsC8_row001_checked.1, rowsC8_row001_checked.2,
    rowsC8_row002_checked.1, rowsC8_row002_checked.2, rowsC8_row003_checked.1, rowsC8_row003_checked.2,
    rowsC8_row004_checked.1, rowsC8_row004_checked.2, rowsC8_row005_checked.1, rowsC8_row005_checked.2,
    rowsC8_row006_checked.1, rowsC8_row006_checked.2, rowsC8_row007_checked.1, rowsC8_row007_checked.2]
private def rowsC9_row000 : List ℕ := [0x2040403020130c0684022130c060311a100804022120986030180c060321a0d8804020100824323120904c28180c06030180c06031190d06c362010080402050c]
private theorem rowsC9_row000_checked :
    rowsC9_row000.length = 1 ∧ rowsSum 1937 rowsC9_row000 = 46752489 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC9_row001 : List ℕ := [0x2050483020140c06c4022130c060321b100804122120986030180c061321a0d8804020100824323120904c28180c06030180c06031198d06c3820100804020510]
private theorem rowsC9_row001_checked :
    rowsC9_row001.length = 1 ∧ rowsSum 1938 rowsC9_row001 = 47081445 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC9_row002 : List ℕ := [0x4060483422180c0704023130c060321b100804223120986030180c061331a0d8804020100834423120984c28180c06030180c06031998d06c3820100804020710]
private theorem rowsC9_row002_checked :
    rowsC9_row002.length = 1 ∧ rowsSum 1939 rowsC9_row002 = 47411477 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC9_row003 : List ℕ := [0x6060503822180c8804024140c060331b100804223130986030180c062331b0e0804020100834423120984c28180c06030180c060b1998d06c4020100804020910]
private theorem rowsC9_row003_checked :
    rowsC9_row003.length = 1 ∧ rowsSum 1940 rowsC9_row003 = 47702936 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC9_row004 : List ℕ := [0x6070604024180c8804224180c060341c100804323130a06030180c063331b0e0804020100844423120984c30180c06030180c060b1998d06c4020100804020910]
private theorem rowsC9_row004_checked :
    rowsC9_row004.length = 1 ∧ rowsSum 1941 rowsC9_row004 = 47947008 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC9_row005 : List ℕ := [0x8080604026180d0804226180c0603420100804424130a06030180c063341b0e0804020100844423120984c30180c06030180c06132198d06c4020100804020910]
private theorem rowsC9_row005_checked :
    rowsC9_row005.length = 1 ∧ rowsSum 1942 rowsC9_row005 = 48258651 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC9 : List ℕ :=
  rowsC9_row000 ++ rowsC9_row001 ++ rowsC9_row002 ++ rowsC9_row003
    ++ rowsC9_row004 ++ rowsC9_row005
private theorem rowsC9_checked :
    rowsC9.length = 6 ∧ rowsSum 1937 rowsC9 = 285154006 := by
  constructor <;> simp only [rowsC9, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC9_row000_checked.1, rowsC9_row000_checked.2, rowsC9_row001_checked.1, rowsC9_row001_checked.2,
    rowsC9_row002_checked.1, rowsC9_row002_checked.2, rowsC9_row003_checked.1, rowsC9_row003_checked.2,
    rowsC9_row004_checked.1, rowsC9_row004_checked.2, rowsC9_row005_checked.1, rowsC9_row005_checked.2]
def rowsC : List ℕ := rowsC1 ++ rowsC2 ++ rowsC3 ++ rowsC4 ++ rowsC5 ++ rowsC6 ++ rowsC7 ++ rowsC8 ++ rowsC9
theorem rowsC_length : rowsC.length = 77 := by
  simp only [rowsC, List.length_append, Nat.reduceAdd,
    rowsC1_checked.1, rowsC2_checked.1, rowsC3_checked.1, rowsC4_checked.1,
    rowsC5_checked.1, rowsC6_checked.1, rowsC7_checked.1, rowsC8_checked.1,
    rowsC9_checked.1]
theorem rowsC_sum : rowsSum 1866 rowsC = 2910691358 := by
  simp only [rowsC, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC1_checked.1, rowsC2_checked.1, rowsC3_checked.1, rowsC4_checked.1,
    rowsC5_checked.1, rowsC6_checked.1, rowsC7_checked.1, rowsC8_checked.1,
    rowsC1_checked.2, rowsC2_checked.2, rowsC3_checked.2, rowsC4_checked.2,
    rowsC5_checked.2, rowsC6_checked.2, rowsC7_checked.2, rowsC8_checked.2,
    rowsC9_checked.2]
end K1_13_2_3_4
end
section
namespace K1_13_1_1
open K1_13 K1_13_1 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
private abbrev Local := LocalPolynomial Geom 3
private abbrev T : Local := MvPolynomial.X (localT 3)
def liftVar (j : Fin 4) : LocalVariable 3 := ![localE 3, localY 0, localY 1, localY 2] j
def liftPower (j : Fin 4) : ℕ := if j = 0 then 1 else j.val
def liftImage (j : Fin 4) : Local := T ^ liftPower j * MvPolynomial.X (liftVar j)
def liftJets : Form →ₐ[Geom] Local := bind₁ liftImage
theorem liftJets_X (j : Fin 4) : liftJets (MvPolynomial.X j) = liftImage j := bind₁_X_right _ _
theorem lift_value :
    liftJets valueForm = unscaledLocalSubstitution 3 0 0 (MvPolynomial.X (some 0)) := by
  rw [unscaledLocalSubstitution_Y_zero]
  simp only [valueForm, map_add, map_sub, liftJets_X, localCorrection, Fin.sum_univ_three]
  simp [liftImage, liftPower, liftVar]
  ring
theorem lift_order (j : Fin 4) :
    liftImage j ∈ restrictWeightedOrder (localContactWeight 3) (1 + targetOrder j) := by
  have h : liftPower j * 1 + localContactWeight 3 (liftVar j) = 1 + targetOrder j := by
    fin_cases j <;> decide
  rw [← h]
  exact mul_mem_restrictWeightedOrder
    (pow_mem_restrictWeightedOrder (X_mem_restrictWeightedOrder _ _ (localContactWeight_T 3).ge)
      (liftPower j))
    (X_mem_restrictWeightedOrder _ _ le_rfl)
theorem value_hom :
    valueForm.IsWeightedHomogeneous (fun _ => (1 : ℕ)) 1 := by
  let h := isWeightedHomogeneous_X Geom (fun _ : Fin 4 => (1 : ℕ))
  exact (((h 0).add (h 1)).sub (h 2)).add (h 3)
theorem lift_value_order :
    liftJets valueForm ∈ restrictWeightedOrder (localContactWeight 3) 1 := by
  have h (j : Fin 4) :
      liftImage j ∈ restrictWeightedOrder (localContactWeight 3) 1 :=
    restrictWeightedOrder_anti _ (Nat.le_add_right 1 (targetOrder j)) (lift_order j)
  simpa only [valueForm, map_add, map_sub, liftJets_X] using
    (add_mem (sub_mem (add_mem (h 0) (h 1)) (h 2)) (h 3))
private def postprocess (s : ℕ) (g : ℤ) : Form →ₗ[Geom] Local :=
  (projectLowContact 138).comp
    ((LinearMap.mulLeft Geom (T ^ (g + 48).toNat *
      (liftJets valueForm) ^ (s - residualDegree s))).comp liftJets.toLinearMap)
theorem project_monomial (cut : ℕ) (e : LocalVariable 3 →₀ ℕ) (a : Geom) :
    projectLowContact cut (monomial e a) =
      if localContactOrder 3 e < cut then monomial e a else 0 := by
  classical
  by_cases hc : localContactOrder 3 e < cut
  · rw [ite_eq_left hc]
    ext v
    by_cases h : e = v
    · subst v
      simp [coeff_projectLowContact, hc]
    · simp [coeff_projectLowContact, coeff_monomial, h]
  · rw [ite_eq_right hc]
    ext v
    by_cases h : e = v
    · subst v
      simp [coeff_projectLowContact, hc]
    · simp [coeff_projectLowContact, coeff_monomial, h]
theorem jet_index_formula (m : Fin 4 →₀ ℕ) :
    m.weight jetIndex = m 1 + 2 * m 2 + 3 * m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, jetIndex, Nat.mul_comm]
theorem source_monomial_expr (u : JetVariable 3 →₀ ℕ) (a : Geom) :
    monomial u a = MvPolynomial.C a * MvPolynomial.X none ^ u none *
      MvPolynomial.X (some 0) ^ u (some 0) * MvPolynomial.X (some 1) ^ u (some 1) *
      MvPolynomial.X (some 2) ^ u (some 2) * MvPolynomial.X (some 3) ^ u (some 3) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_option]
  change _ * (_ * ∏ i : Fin 4, MvPolynomial.X (some i) ^ u (some i)) = _
  rw [Fin.prod_univ_four]
  ring
theorem form_monomial_expr (m : Fin 4 →₀ ℕ) (a : Geom) :
    monomial m a = MvPolynomial.C a * MvPolynomial.X 0 ^ m 0 * MvPolynomial.X 1 ^ m 1 *
      MvPolynomial.X 2 ^ m 2 * MvPolynomial.X 3 ^ m 3 := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four]
  ring
def merge {ι : Type} [Fintype ι] {V : ι → Submodule Geom Form}
    (post : ι → Form →ₗ[Geom] Local) : (∀ i, V i) →ₗ[Geom] Local :=
  ∑ i, (post i).comp ((V i).subtype.comp (LinearMap.proj i))
theorem merge_single {ι : Type} [Fintype ι] [DecidableEq ι]
    {V : ι → Submodule Geom Form} (post : ι → Form →ₗ[Geom] Local) (i : ι) (v : V i) :
    merge post (Pi.single i v) = post i v := by
  rw [merge, LinearMap.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hj' : (Pi.single i v : (k : ι) → V k) j = 0 :=
      Pi.single_eq_of_ne (M := fun k => ↥(V k)) hj v
    simp [hj']
  · simp
end
end K1_13_1_1
end
section
namespace K1_14_5
open K1_14 Finset
open scoped BigOperators
theorem shape_sum_flip {M : Type} [AddCommMonoid M]
    (s : Shape) (f : ℕ → ℕ → M) :
    (∑ q ∈ range (s.B+1), ∑ j ∈ range (min q s.J+1), f q j) =
      ∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1), f q j := by
  calc
    _ = ∑ q ∈ range (s.B+1), ∑ j ∈ range (s.J+1),
        if j ≤ q then f q j else 0 := by
      apply sum_congr rfl
      intro q _
      rw [← sum_filter]
      congr 1
      ext j
      simp only [mem_range, mem_filter, Nat.lt_succ_iff, le_min_iff]
      tauto
    _ = ∑ j ∈ range (s.J+1), ∑ q ∈ range (s.B+1),
        if j ≤ q then f q j else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [← sum_filter]
      congr 1
      ext q
      simp only [mem_filter, mem_range, mem_Ico]
      tauto
end K1_14_5
end
section
namespace K1_13_7_4_2
noncomputable section
open scoped BigOperators Pointwise
section PowerScaling
variable {R ι : Type*} [CommRing R]
abbrev colength (I : Ideal R) : ℕ∞ := Module.length R (R ⧸ I)
private theorem mem_sup_span_singleton {I : Ideal R} {x y : R} :
    y ∈ I ⊔ Ideal.span {x} ↔ ∃ z, y - x * z ∈ I := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hb
    exact ⟨z, by simpa using ha⟩
  · rintro ⟨z, hz⟩
    exact ⟨y - x * z, hz, x * z, Ideal.mem_span_singleton.mpr ⟨z, rfl⟩,
      sub_add_cancel _ _⟩
private theorem span_power_colength (I : Ideal R) (x : R)
    (hreg : ∀ y, x * y ∈ I → y ∈ I) (k : ℕ) :
    colength (I ⊔ Ideal.span {x ^ k}) = (k : ℕ∞) * colength (I ⊔ Ideal.span {x}) := by
  let P : ℕ → Ideal R := fun t => I ⊔ Ideal.span {x ^ t}
  have hmem (t : ℕ) (y : R) : y ∈ P t ↔ ∃ z, y - x ^ t * z ∈ I :=
    mem_sup_span_singleton
  have hstep (t : ℕ) (y : R) : x * y ∈ P (t + 1) ↔ y ∈ P t := by
    rw [hmem, hmem]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, hreg _ ?_⟩
      simpa only [pow_succ', mul_sub, mul_assoc] using hz
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      simpa only [pow_succ', mul_sub, mul_assoc] using I.mul_mem_left x hz
  have hP1 : P 1 = I ⊔ Ideal.span {x} := by simp [P]
  rw [← hP1]
  change colength (P k) = (k : ℕ∞) * colength (P 1)
  induction k with
  | zero =>
    have htop : P 0 = ⊤ := by simp [P]
    rw [htop]
    simp [Module.length_eq_zero]
  | succ k ih =>
    have hmap : (P k : Submodule R R) ≤
        Submodule.comap (LinearMap.mulLeft R x) (P (k + 1)) :=
      fun y hy => (hstep k y).2 hy
    have hle : P (k + 1) ≤ P 1 := by
      have hp : Ideal.span {x ^ (k + 1)} ≤ Ideal.span {x ^ 1} := by
        apply (Ideal.span_singleton_le_iff_mem _).mpr
        exact Ideal.mem_span_singleton.mpr ⟨x ^ k, by simp [pow_succ']⟩
      exact sup_le_sup_left hp _
    let f : (R ⧸ P k) →ₗ[R] (R ⧸ P (k + 1)) :=
      (P k).mapQ (P (k + 1)) (LinearMap.mulLeft R x) hmap
    let g : (R ⧸ P (k + 1)) →ₗ[R] (R ⧸ P 1) := Submodule.factor hle
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      obtain ⟨r, rfl⟩ := (P k).mkQ_surjective y
      rw [show f ((P k).mkQ r) = (P (k + 1)).mkQ (x * r) from rfl,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using (hstep k r).mp hy
    have hex : Function.Exact f g := by
      intro y
      obtain ⟨r, rfl⟩ := (P (k + 1)).mkQ_surjective y
      change (P 1).mkQ r = 0 ↔ ∃ t, f t = (P (k + 1)).mkQ r
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmem]
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨(P k).mkQ z, ?_⟩
        change Ideal.Quotient.mk (P (k + 1)) (x * z) =
          Ideal.Quotient.mk (P (k + 1)) r
        have hz' : r - x * z ∈ I := by simpa only [pow_one] using hz
        exact (Ideal.Quotient.eq.mpr (Submodule.mem_sup_left hz')).symm
      · rintro ⟨t, ht⟩
        obtain ⟨z, rfl⟩ := (P k).mkQ_surjective t
        change Ideal.Quotient.mk (P (k + 1)) (x * z) =
          Ideal.Quotient.mk (P (k + 1)) r at ht
        have hr : r - x * z ∈ P 1 := hle (Ideal.Quotient.eq.mp ht.symm)
        obtain ⟨w, hw⟩ := (hmem 1 _).mp hr
        exact ⟨z + w, by simpa only [pow_one, mul_add, sub_sub] using hw⟩
    calc
      colength (P (k + 1)) = colength (P k) + colength (P 1) :=
        Module.length_eq_add_of_exact f g hf (Submodule.factor_surjective hle) hex
      _ = _ := by rw [ih, Nat.cast_succ, add_mul, one_mul]
private theorem span_range_eq_remaining_sup (f : ι → R) (i : ι) :
    Ideal.span (Set.range f) = remainingIdeal f i ⊔ Ideal.span {f i} := by
  classical
  rw [remainingIdeal, ← Ideal.span_union]
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    by_cases h : j = i
    · exact Or.inr (by simp [h])
    · exact Or.inl ⟨j, h, rfl⟩
  · rintro (⟨j, _, rfl⟩ | h)
    · exact ⟨j, rfl⟩
    · exact ⟨i, h.symm⟩
theorem power_colength {n : ℕ} (f : Fin n → R) (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (hreg : ∀ (e : Fin n → ℕ), (∀ j, 0 < e j) → ∀ i y,
      f i * y ∈ remainingIdeal (fun j => f j ^ e j) i →
      y ∈ remainingIdeal (fun j => f j ^ e j) i) :
    colength (Ideal.span (Set.range fun i => f i ^ b i)) =
      (↑(∏ i, b i) : ℕ∞) * colength (Ideal.span (Set.range f)) := by
  classical
  let e (s : Finset (Fin n)) (j : Fin n) : ℕ := if j ∈ s then b j else 1
  let F (s : Finset (Fin n)) (j : Fin n) : R := f j ^ e s j
  have he (s : Finset (Fin n)) : ∀ j, 0 < e s j := by
    intro j
    by_cases hj : j ∈ s <;> simp [e, hj, hb j]
  have hs (s : Finset (Fin n)) :
      colength (Ideal.span (Set.range (F s))) =
        (↑(∏ i ∈ s, b i) : ℕ∞) * colength (Ideal.span (Set.range f)) := by
    induction s using Finset.induction_on with
    | empty => simp [F, e]
    | @insert i s hi ih =>
      have hsame : remainingIdeal (F (insert i s)) i = remainingIdeal (F s) i := by
        unfold remainingIdeal
        congr 1
        exact Set.image_congr fun j hj => by
          have hji : j ≠ i := hj
          simp [F, e, hji]
      have hnew : F (insert i s) i = f i ^ b i := by simp [F, e]
      have hold : F s i = f i := by simp [F, e, hi]
      rw [span_range_eq_remaining_sup _ i, hsame, hnew,
        span_power_colength _ _ (hreg (e s) (he s) i) (b i),
        ← hold, ← span_range_eq_remaining_sup, ih, Finset.prod_insert hi, Nat.cast_mul, mul_assoc]
  simpa [F, e] using hs Finset.univ
theorem radical_span_powers (f : ι → R) (e : ι → ℕ) (he : ∀ i, 0 < e i) :
    (Ideal.span (Set.range fun i => f i ^ e i)).radical =
      (Ideal.span (Set.range f)).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi : f i ∈ Ideal.span (Set.range f) := Ideal.subset_span (Set.mem_range_self i)
    exact Ideal.pow_mem_of_mem _ hi _ (he i)
  · apply (Ideal.radical_le_radical_iff).mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨e i, Ideal.subset_span ⟨i, rfl⟩⟩
end PowerScaling
section PowerLayers
variable {R : Type*} [CommRing R]
theorem colength_le_of_le {I J : Ideal R} (h : I ≤ J) : colength J ≤ colength I :=
  Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)
private def monomial {ι : Type*} (f : ι → R) {k : ℕ} (m : Sym ι k) : R :=
  (m.val.map f).prod
private theorem span_monomial {ι : Type*} (f : ι → R) (k : ℕ) :
    Ideal.span (Set.range (monomial f (k := k))) = Ideal.span (Set.range f) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    apply (Ideal.eq_top_iff_one _).mpr
    exact Ideal.subset_span ⟨Sym.nil, rfl⟩
  | succ k ih =>
    rw [pow_succ', ← ih, Ideal.span_mul_span]
    congr 1
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      obtain ⟨i, m, rfl⟩ := m.exists_eq_cons_of_succ
      exact ⟨f i, ⟨i, rfl⟩, monomial f m, ⟨m, rfl⟩, by simp [monomial, Sym.coe_cons]⟩
    · rintro ⟨_, ⟨i, rfl⟩, _, ⟨m, rfl⟩, rfl⟩
      exact ⟨Sym.cons i m, by simp [monomial, Sym.coe_cons]⟩
private theorem colength_pow_succ {n : ℕ} (f : Fin n → R) (k : ℕ) :
    colength (Ideal.span (Set.range f) ^ (k + 1)) ≤
      colength (Ideal.span (Set.range f) ^ k) +
        (n.multichoose k : ℕ∞) * colength (Ideal.span (Set.range f)) := by
  classical
  let I := Ideal.span (Set.range f)
  let A : Submodule R R := I ^ (k + 1)
  let B : Submodule R R := I ^ k
  have hAB : A ≤ B := Ideal.pow_le_pow_right (Nat.le_succ k)
  let g : (R ⧸ A) →ₗ[R] (R ⧸ B) := Submodule.factor hAB
  let N := LinearMap.ker g
  let m := monomial f (k := k)
  have hspan : Ideal.span (Set.range m) = I ^ k := span_monomial f k
  have hm (u : Sym (Fin n) k) : m u ∈ I ^ k := hspan ▸ Ideal.subset_span ⟨u, rfl⟩
  let v (u : Sym (Fin n) k) : N :=
    ⟨A.mkQ (m u), by
      change B.mkQ (m u) = 0
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hm u⟩
  let L (u : Sym (Fin n) k) : R ⧸ I →ₗ[R] N :=
    (I : Submodule R R).liftQ (LinearMap.id.smulRight (v u)) (by
      intro r hr
      change r • v u = 0
      apply Subtype.ext
      change A.mkQ (r * m u) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      change r * m u ∈ I ^ (k + 1)
      rw [pow_succ']
      exact Ideal.mul_mem_mul hr (hm u))
  let e : (Sym (Fin n) k →₀ R ⧸ I) →ₗ[R] N := Finsupp.lsum R L
  have hsurj : Function.Surjective e := by
    have hgen : (I ^ k : Submodule R R) ≤
        (LinearMap.range (N.subtype.comp e)).comap A.mkQ := by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨u, rfl⟩
      refine ⟨Finsupp.single u ((I : Submodule R R).mkQ 1), ?_⟩
      simp only [LinearMap.comp_apply, e, Finsupp.lsum_single, L, Submodule.liftQ_apply,
        Submodule.mkQ_apply, LinearMap.smulRight_apply, LinearMap.id_apply, one_smul]
      rfl
    intro z
    obtain ⟨r, hr⟩ := A.mkQ_surjective (z : R ⧸ A)
    have hzr : B.mkQ r = 0 := by
      have hz : g z = 0 := z.property
      simpa only [← hr, g, Submodule.factor_mk] using hz
    have hmem : r ∈ (I ^ k : Submodule R R) := by
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hzr
    obtain ⟨w, hw⟩ := hgen hmem
    exact ⟨w, Subtype.ext (hw.trans hr)⟩
  have hlen := Module.length_le_of_surjective e hsurj
  rw [Module.length_finsupp, ENat.card_eq_coe_fintype_card, Sym.card_sym_eq_multichoose,
    Fintype.card_fin] at hlen
  change Module.length R (R ⧸ A) ≤ Module.length R (R ⧸ B) + _
  rw [Module.length_eq_add_of_exact N.subtype g N.subtype_injective
    (Submodule.factor_surjective hAB) (LinearMap.exact_subtype_ker_map g), add_comm]
  exact add_le_add_right hlen _
theorem colength_pow_le {n : ℕ} (f : Fin n → R) {t : ℕ} (ht : 0 < t) :
    colength (Ideal.span (Set.range f) ^ t) ≤
      ((t + n - 1).choose n : ℕ∞) * colength (Ideal.span (Set.range f)) := by
  let I := Ideal.span (Set.range f)
  have h (k : ℕ) : colength (I ^ k) ≤
      (∑ j ∈ Finset.range k, (n.multichoose j : ℕ∞)) * colength I := by
    induction k with
    | zero => simp [Module.length_eq_zero]
    | succ k ih =>
      rw [Finset.sum_range_succ, add_mul]
      exact (colength_pow_succ f k).trans (add_le_add ih le_rfl)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simpa only [← Nat.cast_sum, Nat.sum_range_multichoose,
    show k + 1 + n - 1 = k + n by omega] using h (k + 1)
end PowerLayers
section GrowthComparison
private theorem ascFactorial_le {n : ℕ} (hn : n = 2 ∨ n = 3) {t : ℕ} (ht : 0 < t) :
    t.ascFactorial n ≤ t ^ n + 5 * t ^ (n - 1) := by
  rcases hn with rfl | rfl
  · calc
      t.ascFactorial 2 = t ^ 2 + t := by
        simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
        ring
      _ ≤ t ^ 2 + 5 * t ^ (2 - 1) := by simp only [Nat.reduceSub, pow_one]; omega
  · have h : 2 * t ≤ 2 * t ^ 2 := by
      apply Nat.mul_le_mul_left
      simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left t ht
    calc
      t.ascFactorial 3 = t ^ 3 + (3 * t ^ 2 + 2 * t) := by
        simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
        ring
      _ ≤ t ^ 3 + (3 * t ^ 2 + 2 * t ^ 2) := Nat.add_le_add_left (Nat.add_le_add_left h _) _
      _ = t ^ 3 + 5 * t ^ (3 - 1) := by ring
private theorem power_le_of_growth {n : ℕ} (hn : n = 2 ∨ n = 3) (M C : ℕ)
    (h : ∀ t : ℕ, 0 < t →
      (M * t + n - 1).choose n ≤ (t + n - 1).choose n * C) :
    M ^ n ≤ C := by
  by_contra! hc
  let t := 5 * C + 1
  have ht : 0 < t := Nat.succ_pos _
  have hnpos : 0 < n := by omega
  have hpow : 0 < t ^ (n - 1) := Nat.pow_pos ht
  have hnat : (M * t).ascFactorial n ≤ C * t.ascFactorial n := by
    simp only [Nat.ascFactorial_eq_factorial_mul_choose']
    exact (Nat.mul_le_mul_left _ (h t ht)).trans_eq (by ac_rfl)
  have hsmall : C * t.ascFactorial n < (C + 1) * t ^ n := calc
    C * t.ascFactorial n ≤ C * (t ^ n + 5 * t ^ (n - 1)) :=
      Nat.mul_le_mul_left _ (ascFactorial_le hn ht)
    _ = C * t ^ n + (5 * C) * t ^ (n - 1) := by ring
    _ < C * t ^ n + t * t ^ (n - 1) :=
      Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hpow) _
    _ = (C + 1) * t ^ n := by
      have he : n - 1 + 1 = n := by omega
      rw [← pow_succ', he, add_mul, one_mul]
  have hlarge : (C + 1) * t ^ n ≤ (M * t).ascFactorial n := calc
    (C + 1) * t ^ n ≤ M ^ n * t ^ n := Nat.mul_le_mul_right _ hc
    _ = (M * t) ^ n := (mul_pow _ _ _).symm
    _ ≤ (M * t).ascFactorial n := Nat.pow_succ_le_ascFactorial _ _
  exact (not_lt_of_ge (hlarge.trans hnat)) hsmall
theorem colength_ge_of_growth {R : Type*} [CommRing R] {n M : ℕ}
    (hn : n = 2 ∨ n = 3) (m : Ideal R) (f : Fin n → R)
    (hcontain : Ideal.span (Set.range f) ≤ m ^ M)
    (hgrow : ∀ t : ℕ, 0 < t → ((t + n - 1).choose n : ℕ∞) ≤ colength (m ^ t)) :
    (↑(M ^ n) : ℕ∞) ≤ colength (Ideal.span (Set.range f)) := by
  let I := Ideal.span (Set.range f)
  change (↑(M ^ n) : ℕ∞) ≤ colength I
  by_cases htop : colength I = ⊤
  · simp [htop]
  let C := (colength I).toNat
  have hC : (C : ℕ∞) = colength I := ENat.natCast_toNat htop
  rw [← hC, ENat.natCast_le_natCast]
  by_cases hM : M = 0
  · have hn0 : n ≠ 0 := by omega
    simp [hM, zero_pow hn0]
  have hMpos := Nat.pos_of_ne_zero hM
  apply power_le_of_growth hn M C
  intro t ht
  have hp : I ^ t ≤ m ^ (M * t) :=
    (Ideal.pow_right_mono hcontain t).trans_eq (pow_mul m M t).symm
  have h := (hgrow (M * t) (Nat.mul_pos hMpos ht)).trans
    ((colength_le_of_le hp).trans (colength_pow_le f ht))
  change (↑((M * t + n - 1).choose n) : ℕ∞) ≤
    ↑((t + n - 1).choose n) * colength I at h
  rw [← hC, ← ENat.natCast_mul] at h
  exact ENat.natCast_le_natCast.mp h
end GrowthComparison
end
end K1_13_7_4_2
end
section
namespace K1_13_2_3_4
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0
open K1_13_2
private theorem bDenNeg {u : ℤ} (hu : u < 0) : denominator u = 0 := by
  simp [denominator, hu]
private theorem bCumNeg {d u : ℤ} (hu : u < 0) : cumulative d u = 0 := by
  simp [cumulative, hu]
private theorem bCumLow {d u : ℤ} (hd : 0 ≤ d) (hu : u ≤ d) :
    cumulative d u = denominator u := by
  by_cases hn : u < 0
  · rw [bCumNeg hn, bDenNeg hn]
  simp (disch := omega) [cumulative, hn, bDenNeg]
  omega
private theorem bCapLow {d u c : ℤ} (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hu : u ≤ d) (ht : u < 3 * (c + 1)) :
    cappedCount d u c = denominator u := by
  simp (disch := omega) [cappedCount, bCumLow, bCumNeg]
  omega
private def bFlag (s q k : ℤ) : Flag :=
  ⟨1650 - 3 * k, s - 1350 - q - 2 * k, 1650 - 3 * k, 550 - k, 1650 - q - 3 * k⟩
private theorem bOld (s q k : ℤ) (hs : 1758 ≤ s) (hs' : s ≤ 1865)
    (hq : 0 ≤ q) (hq' : q ≤ 70) (hk : 0 ≤ k) (hk' : k ≤ 256) :
    oldCount (bFlag s q k) = denominator (1650 - 3 * k) - denominator (s - 1350 - q - 2 * k - 1) := by
  simp (disch := omega) [oldCount, bFlag, bCapLow]
private theorem bTarget (s q k : ℤ) (hs : 1758 ≤ s) (hs' : s ≤ 1865)
    (hq : 0 ≤ q) (hq' : q ≤ 70) (hk : 0 ≤ k) (hk' : k ≤ 256) :
    targetCount (bFlag s q k) = denominator (1650 - q - 3 * k - 1) := by
  simp (disch := omega) [targetCount, bFlag, bCumNeg, bCumLow]
  omega
private theorem bKernel (s q k : ℤ) (hs : 1758 ≤ s) (hs' : s ≤ 1865)
    (hq : 0 ≤ q) (hq' : q ≤ 70) (hk : 0 ≤ k) (hk' : k ≤ 256) :
    kernelLower (bFlag s q k) =
      denominator (1650 - 3 * k) - denominator (s - 1350 - q - 2 * k - 1) - denominator (1650 - q - 3 * k - 1) := by
  have h := bOld s q k hs hs' hq hq' hk hk'
  have t := bTarget s q k hs hs' hq hq' hk hk'
  unfold kernelLower
  rw [ite_eq_right, h, t]
  simp [bFlag]
  omega
private def bDen (i : ℕ) : ℕ := (((2 * i + 15) * i + 30) * i + 25) / 72
private theorem bTwiceHalf (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem bTwiceDen (u : ℤ) (hu : 0 ≤ u) :
    let a := u / 6
    let b := u % 6
    2 * denominator u = ((12 * a + 21 + 6 * b) * a + 11 + (7 + b) * b) * a + b * (b + 1) + 2 := by
  let a := u / 6
  let b := u % 6
  simp only [denominator, ite_eq_right (not_lt.mpr hu)]
  change 2 * (1 + b * (b + 1) / 2 + a * (22 + 7 * b + b * (b - 1) / 2) +
    (57 + 6 * b) * (a * (a - 1) / 2) + 6 * a * (a - 1) * (a - 2)) =
      ((12 * a + 21 + 6 * b) * a + 11 + (7 + b) * b) * a + b * (b + 1) + 2
  have h := bTwiceHalf (b + 1)
  rw [show (b + 1) * (b + 1 - 1) = b * (b + 1) by ring] at h
  linear_combination h + a * bTwiceHalf b + (57 + 6 * b) * bTwiceHalf a
private theorem bRound (a b v : ℤ) (hb : 0 ≤ b) (hb' : b ≤ 5)
    (hv : 2 * v = ((12 * a + 21 + 6 * b) * a + 11 + (7 + b) * b) * a + b * (b + 1) + 2) :
    v = (((2 * (6 * a + b + 1) + 15) * (6 * a + b + 1) + 30) * (6 * a + b + 1) + 25) / 72 := by
  let r := ((2 * b + 21) * b + 66) * b + 72 - 36 * (b * (b + 1) + 2)
  have he : ((2 * (6 * a + b + 1) + 15) * (6 * a + b + 1) + 30) * (6 * a + b + 1) + 25 =
      72 * v + r := by
    dsimp only [r]
    linear_combination -36 * hv
  have hr : 0 ≤ r ∧ r < 72 := by
    dsimp only [r]
    interval_cases b <;> decide
  omega
private theorem bDenNat (u : ℕ) : denominator u = (bDen (u + 1) : ℤ) := by
  simp only [bDen, Int.natCast_ediv, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  have h := bRound ((u : ℤ) / 6) ((u : ℤ) % 6) (denominator u)
    (by omega) (by omega) (bTwiceDen (u : ℤ) (by omega))
  rwa [show 6 * ((u : ℤ) / 6) + (u : ℤ) % 6 = u by omega] at h
private theorem bDenInt (u : ℤ) : denominator u = (bDen (u + 1).toNat : ℤ) := by
  by_cases h : u < 0
  · rw [bDenNeg h, show (u + 1).toNat = 0 by omega]
    rfl
  have hh := bDenNat u.toNat
  rwa [show (u.toNat : ℤ) = u by omega, show u.toNat + 1 = (u + 1).toNat by omega] at hh
private def bSavings (s q k : ℕ) : ℕ :=
  let old := bDen 1651 - bDen (s - (1350 + q))
  let lower := old - bDen (1650 - q)
  let after := bDen (1651 - 3 * k) - bDen (s - (1350 + q + 2 * k)) - bDen (1650 - q - 3 * k)
  (old - lower) - (old - max lower after)
private theorem bClip (a b t c d v : ℕ) :
    let old := (a : ℤ) - b
    let lower := max 0 (old - t)
    (old - lower).toNat - (old - max lower ((c : ℤ) - d - v)).toNat =
      let old' := a - b
      let lower' := old' - t
      (old' - lower') - (old' - max lower' (c - d - v)) := by
  dsimp only
  have subNat (x y : ℤ) (hy : 0 ≤ y) : (x - y).toNat = x.toNat - y.toNat := by omega
  have maxNat (x y : ℤ) : (max x y).toNat = max x.toNat y.toNat := by omega
  simp (disch := omega) only [subNat, maxNat, Int.toNat_natCast, Int.toNat_zero, Nat.zero_max]
private theorem bSavings_eq {s q k : ℕ} (hs : 1758 ≤ s) (hs' : s ≤ 1865)
    (hq : q ≤ 70) (hk : k ≤ 256) (hk0 : k ≠ 0) : entry s q k = bSavings s q k := by
  have hj : 993 ≤ 3000 + q - s ∧ 3000 + q - s ≤ 1581 := by omega
  have hw : windowFlag s (3000 + q - s) = bFlag s q 0 := by
    simp only [windowFlag, bFlag]
    congr 1 <;> omega
  have hc : cubicFlag (bFlag s q 0) k = bFlag s q k := by
    simp [bFlag, cubicFlag]
  simp only [entry, ite_eq_left hj, cubicSavings, ite_eq_right hk0, hw, hc]
  have ho := bOld s q 0 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide)
  have hbase := bKernel s q 0 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide)
  have hres := bKernel s q k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [ho, hbase, hres]
  simp (disch := omega) only [bDenInt]
  have h1 : ((1650 : ℤ) - 3 * 0 + 1).toNat = 1651 := by decide
  have h2 : ((s : ℤ) - 1350 - q - 2 * 0 - 1 + 1).toNat = s - (1350 + q) := by omega
  have h3 : ((1650 : ℤ) - q - 3 * 0 - 1 + 1).toNat = 1650 - q := by omega
  have h4 : ((1650 : ℤ) - 3 * k + 1).toNat = 1651 - 3 * k := by omega
  have h5 : ((s : ℤ) - 1350 - q - 2 * k - 1 + 1).toNat = s - (1350 + q + 2 * k) := by omega
  have h6 : ((1650 : ℤ) - q - 3 * k - 1 + 1).toNat = 1650 - q - 3 * k := by omega
  simp only [h1, h2, h3, h4, h5, h6]
  apply bClip
private theorem bZeroRow (s q n : ℕ) : rowSum s q 0 n = 0 := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have hz : entry s q 0 = 0 := by simp [entry, cubicSavings]
    simp [rowSum, hz, ih]
private def bRow (s q code : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if code = 0 then 0 else
      let k := code % 512
      (if k = 0 then 0 else if k ≤ 256 then bSavings s q k else entry s q k) +
        bRow s (q + 1) (code / 512) n
private theorem bRow_eq (s q code n : ℕ) (hs : 1758 ≤ s) (hs' : s ≤ 1865)
    (hq : q + n ≤ 71) : rowSum s q code n = bRow s q code n := by
  induction n generalizing q code with
  | zero => rfl
  | succ n ih =>
    by_cases hz : code = 0
    · subst code
      rw [bZeroRow]
      simp [bRow]
    rw [rowSum, bRow, ite_eq_right hz, ih _ _ (by omega)]
    by_cases hk0 : code % 512 = 0
    · simp [hk0, entry, cubicSavings]
    by_cases hk : code % 512 ≤ 256
    · simp only [ite_eq_right hk0, ite_eq_left hk, bSavings_eq (q := q) hs hs' (by omega) hk hk0]
    · simp only [ite_eq_right hk0, ite_eq_right hk]
private def bRows (s : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: cs => bRow s 0 c 71 + bRows (s + 1) cs
private theorem bRows_eq (s : ℕ) (cs : List ℕ) (lo : 1758 ≤ s)
    (hi : s + cs.length ≤ 1866) : rowsSum s cs = bRows s cs := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.length_cons] at hi
    rw [rowsSum, bRows, bRow_eq _ _ _ _ lo (by omega) (by decide), ih _ (by omega) (by omega)]
private def rowsB1_chunk000 : List ℕ := [
  0x30403022180d0804830180c8704021120986030180c86c4020100864826180c0,
  0x40403422180d8804830180cc804021920986030180c86c4020100884826180c0,
  0x40483424180d8804830180d0804021920986030180cc6c4020100884826180c0,
  0x50483824180e0844c30180d0804022120a06030180cc6c4020102884826180c0]
private theorem rowsB1_chunk000_checked :
    rowsB1_chunk000.length = 4 ∧ rowsSum 1758 rowsB1_chunk000 = 43976193 := by
  constructor
  · rfl
  · rw [bRows_eq 1758 rowsB1_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB1_chunk004 : List ℕ := [
  0x206050402618100844c30180d0804022120a06030180cc6c4020102884826180c0,
  0x406060402818100884c30180d8804022130c06030184d06c4020104884826180c0,
  0x407060403019100885030188d8804023130c06030184d06c40201048c4826180c0,
  0x6080604030191008c5030188d8804123130c06030188d07040201068c4828180c0]
private theorem rowsB1_chunk004_checked :
    rowsB1_chunk004.length = 4 ∧ rowsSum 1762 rowsB1_chunk004 = 45785842 := by
  constructor
  · rfl
  · rw [bRows_eq 1762 rowsB1_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB1_chunk008 : List ℕ := [
  0x60806044301a1008c6030190e0804123130c0603018cd07040201088c4830180c0,
  0x80806844301b100906030198e0804224130c0603018cd08040201088c4c30180c0,
  0xa0907048301b10090603019900804224130c06030190d08040201088c4c30180c0,
  0x40c0a0804c301c1089860301a100804324130c06030190d880402010c8c4c30180c0]
private theorem rowsB1_chunk008_checked :
    rowsB1_chunk008.length = 4 ∧ rowsSum 1766 rowsB1_chunk008 = 47566533 := by
  constructor
  · rfl
  · rw [bRows_eq 1766 rowsB1_chunk008 (by decide) (by decide)]
    decide +kernel
private def rowsB1_chunk012 : List ℕ := [
  0x40c0c0804c30201089860301a100804424140c06030190d880402010c8c4c30180c0,
  0x80c0c0805030201109860301b100804424140c06030198d880402010c8c4c30180c0,
  0xc0e0c080603220110a060311b100804426140c06030198d880402010c904c30180c0]
private theorem rowsB1_chunk012_checked :
    rowsB1_chunk012.length = 3 ∧ rowsSum 1770 rowsB1_chunk012 = 37033122 := by
  constructor
  · rfl
  · rw [bRows_eq 1770 rowsB1_chunk012 (by decide) (by decide)]
    decide +kernel
private def rowsB1 : List ℕ := rowsB1_chunk000 ++ rowsB1_chunk004 ++ rowsB1_chunk008 ++ rowsB1_chunk012
private theorem rowsB1_checked :
    rowsB1.length = 15 ∧ rowsSum 1758 rowsB1 = 174361690 := by
  constructor
  · simp only [rowsB1, List.length_append, Nat.reduceAdd, rowsB1_chunk000_checked.1,
      rowsB1_chunk004_checked.1, rowsB1_chunk008_checked.1, rowsB1_chunk012_checked.1]
  · simp only [rowsB1, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB1_chunk000_checked.1, rowsB1_chunk004_checked.1, rowsB1_chunk008_checked.1,
      rowsB1_chunk000_checked.2, rowsB1_chunk004_checked.2, rowsB1_chunk008_checked.2,
      rowsB1_chunk012_checked.2]
private def rowsB2_chunk000 : List ℕ := [
  0xc100c088603420118a060311b100804626180c06030998d8804020110904c30180c0,
  0x10100d088603420120c060321b100824626180c060309a0d8804020510904c30180c0,
  0x10120d090603620120c060321c100824626180c060311a0d8804020510904c30180c0,
  0x814120e090603620120c0603320100844826180c060311a0e0804020910904c30180c0]
private theorem rowsB2_chunk000_checked :
    rowsB2_chunk000.length = 4 ∧ rowsSum 1773 rowsB2_chunk000 = 51174475 := by
  constructor
  · rfl
  · rw [bRows_eq 1773 rowsB2_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB2_chunk004 : List ℕ := [
  0x8181810098604021130c0603420100864826180c060319a0e0804020910904c30180c0,
  0x101818100a0604021130c0603420100864826180c060321a0e0804020d18904c30180c0,
  0x101c18100c0644022130c0603420100884828180c060321b100804021118904c30180c0,
  0x182018100c0644022140c0623620100884828180c060321b100804021118904c30180c0]
private theorem rowsB2_chunk004_checked :
    rowsB2_chunk004.length = 4 ∧ rowsSum 1777 rowsB2_chunk004 = 53211888 := by
  constructor
  · rfl
  · rw [bRows_eq 1777 rowsB2_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB2_chunk008 : List ℕ := [
  0x202018110c0684023140c0623620100884c28180c060331b100804021118904c30180c0,
  0x20241a110c0684024180c06436201008c4c30180c060331b100804021918985030180c0,
  0x1028241c120c06c4024180c06438201048c4c30180c061331b100804021918985030180c0,
  0x10302820130c0704024180c06638201088c4c30180c061331b100804021918986030180c0]
private theorem rowsB2_chunk008_checked :
    rowsB2_chunk008.length = 4 ∧ rowsSum 1781 rowsB2_chunk008 = 55266253 := by
  constructor
  · rfl
  · rw [bRows_eq 1781 rowsB2_chunk008 (by decide) (by decide)]
    decide +kernel
private def rowsB2_chunk012 : List ℕ := [
  0x20303020130c0804226180c0684020108904c30180c062341b100804021920986030180c0,
  0x20383020140c0804226180c068402010c904c30180c062341b1008040a2120986030180c0]
private theorem rowsB2_chunk012_checked :
    rowsB2_chunk012.length = 2 ∧ rowsSum 1785 rowsB2_chunk012 = 28420456 := by
  constructor
  · rfl
  · rw [bRows_eq 1785 rowsB2_chunk012 (by decide) (by decide)]
    decide +kernel
private def rowsB2 : List ℕ := rowsB2_chunk000 ++ rowsB2_chunk004 ++ rowsB2_chunk008 ++ rowsB2_chunk012
private theorem rowsB2_checked :
    rowsB2.length = 14 ∧ rowsSum 1773 rowsB2 = 188073072 := by
  constructor
  · simp only [rowsB2, List.length_append, Nat.reduceAdd, rowsB2_chunk000_checked.1,
      rowsB2_chunk004_checked.1, rowsB2_chunk008_checked.1, rowsB2_chunk012_checked.1]
  · simp only [rowsB2, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB2_chunk000_checked.1, rowsB2_chunk004_checked.1, rowsB2_chunk008_checked.1,
      rowsB2_chunk000_checked.2, rowsB2_chunk004_checked.2, rowsB2_chunk008_checked.2,
      rowsB2_chunk012_checked.2]
private def rowsB3_chunk000 : List ℕ := [
  0x30403020180c8804426180c068402010c904c30180c063341c1008040a2120986030180c0,
  0x40403022180d0804628180c46c4020110905030180c064341c100804122120986030180c0,
  0x40483422180d0804628180c46c4020110905030180c0643420100804122120986030180c0,
  0x2050483824180d8804830180c86c4020118985030180c06436201008041a2120986030180c1]
private theorem rowsB3_chunk000_checked :
    rowsB3_chunk000.length = 4 ∧ rowsSum 1787 rowsB3_chunk000 = 58605477 := by
  constructor
  · rfl
  · rw [bRows_eq 1787 rowsB3_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB3_chunk004 : List ℕ := [
  0x2060504026180d8804830180c8704020918986030180c06636201008041a3120986030180c1,
  0x406060402618100844c30180cc704020918986030180c0663620100804223120986030180c2,
  0x407060402818100844c30180d0804021118986030180c2663620100804223120986030180c2,
  0x608060403019100884c30180d0804021920986030180c4683620100804323120986030180c3]
private theorem rowsB3_chunk004_checked :
    rowsB3_chunk004.length = 4 ∧ rowsSum 1791 rowsB3_chunk004 = 60830669 := by
  constructor
  · rfl
  · rw [bRows_eq 1791 rowsB3_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB3_chunk008 : List ℕ := [
  0x808060443019100884c30180d0804021920986030180c4683620100804323120986030180c3,
  0x80906844301a1008c5030188d8804022120986030180c6683620100804323130986030180c4,
  0x40a0906848301b100906030188d8804022120a06030180c6683820100804323130a06030180c4,
  0x40c0a08048301b100906030190d8804022120a06030180c8683820100814424130a06030180c6]
private theorem rowsB3_chunk008_checked :
    rowsB3_chunk008.length = 4 ∧ rowsSum 1795 rowsB3_chunk008 = 63192444 := by
  constructor
  · rfl
  · rw [bRows_eq 1795 rowsB3_chunk008 (by decide) (by decide)]
    decide +kernel
private def rowsB3_chunk012 : List ℕ := [
  0x80c0c0804c301c100906030190e0804123130a06030180c8683820100824424130c06030180c6,
  0x80e0c080503020108986030198e0804123130c06030180c86c4020100824424130c06030180c6]
private theorem rowsB3_chunk012_checked :
    rowsB3_chunk012.length = 2 ∧ rowsSum 1799 rowsB3_chunk012 = 32409390 := by
  constructor
  · rfl
  · rw [bRows_eq 1799 rowsB3_chunk012 (by decide) (by decide)]
    decide +kernel
private def rowsB3 : List ℕ := rowsB3_chunk000 ++ rowsB3_chunk004 ++ rowsB3_chunk008 ++ rowsB3_chunk012
private theorem rowsB3_checked :
    rowsB3.length = 14 ∧ rowsSum 1787 rowsB3 = 215037980 := by
  constructor
  · simp only [rowsB3, List.length_append, Nat.reduceAdd, rowsB3_chunk000_checked.1,
      rowsB3_chunk004_checked.1, rowsB3_chunk008_checked.1, rowsB3_chunk012_checked.1]
  · simp only [rowsB3, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB3_chunk000_checked.1, rowsB3_chunk004_checked.1, rowsB3_chunk008_checked.1,
      rowsB3_chunk000_checked.2, rowsB3_chunk004_checked.2, rowsB3_chunk008_checked.2,
      rowsB3_chunk012_checked.2]
private def rowsB4_chunk000 : List ℕ := [
  0xc100c0806032201089860301a100804223130c06030180cc6c4020100834424130c06030180c6,
  0x10100c0886032201109860301a100804224130c06030184cc6c4020100834424130c06030180c8,
  0x10120d088603420118a060301a100804324130c06030184cc6c4020100844624130c06030180c8,
  0x814120d090603420118a060311b100804424130c06030188d06c4020100844624130c06030180c8]
private theorem rowsB4_chunk000_checked :
    rowsB4_chunk000.length = 4 ∧ rowsSum 1801 rowsB4_chunk000 = 66698494 := by
  constructor
  · rfl
  · rw [bRows_eq 1801 rowsB4_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB4_chunk004 : List ℕ := [
  0x8181410090603620120c060311b100804424140c06030188d06c4020100844624130c06030180c8,
  0x10181810098603820120c060321b100804424140c0603018cd06c4020100864624130c06030180c8,
  0x181c18100a0604021130c060331c100824626140c06030190d0704020100864624130c06030180c8,
  0x182018100c0644021130c060331c100824626180c06030190d0704020100864624130c06030180cc]
private theorem rowsB4_chunk004_checked :
    rowsB4_chunk004.length = 4 ∧ rowsSum 1805 rowsB4_chunk004 = 69282112 := by
  constructor
  · rfl
  · rw [bRows_eq 1805 rowsB4_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB4_chunk008 : List ℕ := [
  0x202018110c0644022130c0603420100844626180c06030190d8804020102884626130c06030180cc,
  0x20241a110c0684022130c0603420100844826180c06030198d8804020104884826130c06030180cc,
  0x1030241c120c0684023140c0623620100864826180c06030998d8804020104884826140c06030180cc,
  0x20302820120c06c4024180c0623620100884826180c06030998d8804020106884826140c06030180cc]
private theorem rowsB4_chunk008_checked :
    rowsB4_chunk008.length = 4 ∧ rowsSum 1809 rowsB4_chunk008 = 71729271 := by
  constructor
  · rfl
  · rw [bRows_eq 1809 rowsB4_chunk008 (by decide) (by decide)]
    decide +kernel
private def rowsB4_chunk012 : List ℕ := [
  0x20303020130c0704024180c0643620100884826180c060311a0d8804020106884826180c06030180cc]
private theorem rowsB4_chunk012_checked :
    rowsB4_chunk012.length = 1 ∧ rowsSum 1813 rowsB4_chunk012 = 18309315 := by
  constructor
  · rfl
  · rw [bRows_eq 1813 rowsB4_chunk012 (by decide) (by decide)]
    decide +kernel
private def rowsB4 : List ℕ := rowsB4_chunk000 ++ rowsB4_chunk004 ++ rowsB4_chunk008 ++ rowsB4_chunk012
private theorem rowsB4_checked :
    rowsB4.length = 13 ∧ rowsSum 1801 rowsB4 = 226019192 := by
  constructor
  · simp only [rowsB4, List.length_append, Nat.reduceAdd, rowsB4_chunk000_checked.1,
      rowsB4_chunk004_checked.1, rowsB4_chunk008_checked.1, rowsB4_chunk012_checked.1]
  · simp only [rowsB4, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB4_chunk000_checked.1, rowsB4_chunk004_checked.1, rowsB4_chunk008_checked.1,
      rowsB4_chunk000_checked.2, rowsB4_chunk004_checked.2, rowsB4_chunk008_checked.2,
      rowsB4_chunk012_checked.2]
private def rowsB5_chunk000 : List ℕ := [
  0x30383020140c0804224180c0643620100884828180c060311a0d8804020108884826180c06030182cc,
  0x30403020180c8804226180c06638201048c4c28180c060319a0d88040201088c4826180c06030182cc,
  0x40403022180c8804426180c06840201048c4c28180c060321a0e08040201088c4826180c06030184d0,
  0x2050483422180d0804426180c06840201088c4c30180c060321a0e080402010c8c4826180c06030184d0]
private theorem rowsB5_chunk000_checked :
    rowsB5_chunk000.length = 4 ∧ rowsSum 1814 rowsB5_chunk000 = 74964634 := by
  constructor
  · rfl
  · rw [bRows_eq 1814 rowsB5_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB5_chunk004 : List ℕ := [
  0x2060483824180d0804628180c068402010c904c30180c060321b0e080402010c8c4826180c06030186d0,
  0x4060604024180d8804830180c46c402010c904c30180c060331b10080402050c8c4826180c06030186d0,
  0x4070604026180e0804830180c46c4020110904c30180c061331b1008040205108c4826180c06030188d0,
  0x608060402818100804830180c86c4020110904c30180c061331b1008040209108c4c26180c06030188d0]
private theorem rowsB5_chunk004_checked :
    rowsB5_chunk004.length = 4 ∧ rowsSum 1818 rowsB5_chunk004 = 77713468 := by
  constructor
  · rfl
  · rw [bRows_eq 1818 rowsB5_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB5_chunk008 : List ℕ := [
  0x808060403019100844c30180cc704020110905030180c062341b100804020910904c26180c06030188d0,
  0x808068443019100884c30180cc704020918985030180c063341b100804020d10904c28180c0603018cd0,
  0x40a0906844301a100884c30180d0804020918985030180c063341b100804021110904c28180c0603018cd0,
  0x40c0a07048301a1008c5030180d0804021118986030180c064341c100804021118904c28180c0603018cd0]
private theorem rowsB5_chunk008_checked :
    rowsB5_chunk008.length = 4 ∧ rowsSum 1822 rowsB5_chunk008 = 80477410 := by
  constructor
  · rfl
  · rw [bRows_eq 1822 rowsB5_chunk008 (by decide) (by decide)]
    decide +kernel
private def rowsB5 : List ℕ := rowsB5_chunk000 ++ rowsB5_chunk004 ++ rowsB5_chunk008
private theorem rowsB5_checked :
    rowsB5.length = 12 ∧ rowsSum 1814 rowsB5 = 233155512 := by
  constructor
  · simp only [rowsB5, List.length_append, Nat.reduceAdd, rowsB5_chunk000_checked.1,
      rowsB5_chunk004_checked.1, rowsB5_chunk008_checked.1]
  · simp only [rowsB5, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB5_chunk000_checked.1, rowsB5_chunk004_checked.1, rowsB5_chunk000_checked.2,
      rowsB5_chunk004_checked.2, rowsB5_chunk008_checked.2]
private def rowsB6_chunk000 : List ℕ := [
  0x80c0c0804c301b100905030188d8804021920986030180c064341c100804021118904c30180c0603018cd0,
  0xc0e0c0804c301c100906030188d8804021920986030180c064361c100804021918904c30180c06030190d8,
  0xc100c080503020100906030190d8804022120986030180c0663620100804021918904c30180c06030190d8,
  0x10100c080603220108986030190d8804022120986030180c26636201008040a1918904c30180c06030190d8]
private theorem rowsB6_chunk000_checked :
    rowsB6_chunk000.length = 4 ∧ rowsSum 1826 rowsB6_chunk000 = 83124628 := by
  constructor
  · rfl
  · rw [bRows_eq 1826 rowsB6_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB6_chunk004 : List ℕ := [
  0x14120d088603220110986030198e0804123120a06030180c46636201008040a1918904c30180c06030190d8,
  0x818120d0906034201109860301a100804123130a06030180c4683620100804122118904c30180c06030190d8,
  0x10181410090603420118a060301a100804223130a06030180c6683620100804122120984c30180c06030198d8,
  0x10181810098603620120a060311a100804223130c06030180c66836201008041a2120984c30180c06030598d8]
private theorem rowsB6_chunk004_checked :
    rowsB6_chunk004.length = 4 ∧ rowsSum 1830 rowsB6_chunk004 = 86155640 := by
  constructor
  · rfl
  · rw [bRows_eq 1830 rowsB6_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB6_chunk008 : List ℕ := [
  0x18201810098603820120c060311b100804324130c06030180c8683820100804222120984c30180c06030598d8,
  0x202018100c0604021120c060321b100804424130c06030180c8683820100804222120985030180c06030998d8,
  0x202018100c0644021130c060321b100804424130c06030180cc6c3820100804223120985030180c0603099900,
  0x1028241a110c0644022130c060331c100804424130c06030184cc6c4020100804323120985030180c06030d9900]
private theorem rowsB6_chunk008_checked :
    rowsB6_chunk008.length = 4 ∧ rowsSum 1834 rowsB6_chunk008 = 89076513 := by
  constructor
  · rfl
  · rw [bRows_eq 1834 rowsB6_chunk008 (by decide) (by decide)]
    decide +kernel
private def rowsB6 : List ℕ := rowsB6_chunk000 ++ rowsB6_chunk004 ++ rowsB6_chunk008
private theorem rowsB6_checked :
    rowsB6.length = 12 ∧ rowsSum 1826 rowsB6 = 258356781 := by
  constructor
  · simp only [rowsB6, List.length_append, Nat.reduceAdd, rowsB6_chunk000_checked.1,
      rowsB6_chunk004_checked.1, rowsB6_chunk008_checked.1]
  · simp only [rowsB6, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB6_chunk000_checked.1, rowsB6_chunk004_checked.1, rowsB6_chunk000_checked.2,
      rowsB6_chunk004_checked.2, rowsB6_chunk008_checked.2]
private def rowsB7_chunk000 : List ℕ := [
  0x1030281c120c0684022130c0603420100824624140c06030184cc6c4020100804323120986030180c06030d9900,
  0x20303020120c06c4023140c0603420100824626140c06030188cc6c4020100814323120986030180c0603119900,
  0x30383020130c06c4024140c0603420100844626180c0603018cd06c4020100814423120986030180c060311a100,
  0x30403020140c0704024180c0623620100864826180c0603018cd06c4020100824423120986030180c060311a100]
private theorem rowsB7_chunk000_checked :
    rowsB7_chunk000.length = 4 ∧ rowsSum 1838 rowsB7_chunk000 = 91876466 := by
  constructor
  · rfl
  · rw [bRows_eq 1838 rowsB7_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB7_chunk004 : List ℕ := [
  0x40403020180c0804224180c0643620100864826180c06030190d06c4020100834423120986030180c060319a100,
  0x2050483422180c8804226180c0643620100884826180c06030190d0704020100834424130986030180c060319a100,
  0x2060483422180d0804426180c0663820100884826180c06030198d0704020100844424130986030180c060319a100,
  0x4060503824180d0804626180c06838201048c4828180c06030998d8704020100844424130986030180c060321a100]
private theorem rowsB7_chunk004_checked :
    rowsB7_chunk004.length = 4 ∧ rowsSum 1842 rowsB7_chunk004 = 95136682 := by
  constructor
  · rfl
  · rw [bRows_eq 1842 rowsB7_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB7_chunk008 : List ℕ := [
  0x6070604026180d8804628180c06840201048c4c28180c06030998d8804020100844624130986030180c060321a100,
  0x6080604026180d8804830180c06840201088c4c28180c06031198d8804020100864624130a06030180c060321a100,
  0x808060402818100804830180c46c40201088c4c30180c060319a0d8804020102864624130a06030180c060321a100]
private theorem rowsB7_chunk008_checked :
    rowsB7_chunk008.length = 3 ∧ rowsSum 1846 rowsB7_chunk008 = 73419578 := by
  constructor
  · rfl
  · rw [bRows_eq 1846 rowsB7_chunk008 (by decide) (by decide)]
    decide +kernel
private def rowsB7 : List ℕ := rowsB7_chunk000 ++ rowsB7_chunk004 ++ rowsB7_chunk008
private theorem rowsB7_checked :
    rowsB7.length = 11 ∧ rowsSum 1838 rowsB7 = 260432726 := by
  constructor
  · simp only [rowsB7, List.length_append, Nat.reduceAdd, rowsB7_chunk000_checked.1,
      rowsB7_chunk004_checked.1, rowsB7_chunk008_checked.1]
  · simp only [rowsB7, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB7_chunk000_checked.1, rowsB7_chunk004_checked.1, rowsB7_chunk000_checked.2,
      rowsB7_chunk004_checked.2, rowsB7_chunk008_checked.2]
private def rowsB8_chunk000 : List ℕ := [
  0x808060403019100844c30180c86c402010c904c30180c060319a0d8804020102864624130a06030180c060321a100,
  0x40c09068443019100844c30180c86c4020110904c30180c060321a0d8804020104884624130c06030180c060b21a100,
  0x80c0a07048301a100884c30180cc704020110904c30180c060321a0e0804020104884624130c06030180c061331b100,
  0x80c0c08048301a1008c4c30180d0704020110904c30180c060321a0e0804020106884624130c06030180c061331b100]
private theorem rowsB8_chunk000_checked :
    rowsB8_chunk000.length = 4 ∧ rowsSum 1849 rowsB8_chunk000 = 100580370 := by
  constructor
  · rfl
  · rw [bRows_eq 1849 rowsB8_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB8_chunk004 : List ℕ := [
  0xc0e0c0804c301b1008c5030180d0804020918905030180c061331b0e0804020108884826130c06030180c061b31b100,
  0x10100c08050301c100906030188d0804021118985030180c061331b100804020108884826130c06030180c061b31b100,
  0x10100c080603020100906030188d8804021118985030180c062331b1008040201088c4826130c06030180c062331b100,
  0x814120d088603220108986030190d8804021920986030180c063341b10080402010c8c4826130c06030180c062331b100]
private theorem rowsB8_chunk004_checked :
    rowsB8_chunk004.length = 4 ∧ rowsSum 1853 rowsB8_chunk004 = 103896094 := by
  constructor
  · rfl
  · rw [bRows_eq 1853 rowsB8_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB8_chunk008 : List ℕ := [
  0x1018120d088603420110986030190d8804022120986030180c063341b10080402050c8c4826140c06030180c062331b100,
  0x10181810090603420110986030198e0804022120986030180c064341b10080402050c8c4826140c06030180c063341b100,
  0x181c1810098603620118a060301a0e0804022120986030180c064341b1008040209108c4826140c06030180c063341b100]
private theorem rowsB8_chunk008_checked :
    rowsB8_chunk008.length = 3 ∧ rowsSum 1857 rowsB8_chunk008 = 80211996 := by
  constructor
  · rfl
  · rw [bRows_eq 1857 rowsB8_chunk008 (by decide) (by decide)]
    decide +kernel
private def rowsB8 : List ℕ := rowsB8_chunk000 ++ rowsB8_chunk004 ++ rowsB8_chunk008
private theorem rowsB8_checked :
    rowsB8.length = 11 ∧ rowsSum 1849 rowsB8 = 284688460 := by
  constructor
  · simp only [rowsB8, List.length_append, Nat.reduceAdd, rowsB8_chunk000_checked.1,
      rowsB8_chunk004_checked.1, rowsB8_chunk008_checked.1]
  · simp only [rowsB8, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB8_chunk000_checked.1, rowsB8_chunk004_checked.1, rowsB8_chunk000_checked.2,
      rowsB8_chunk004_checked.2, rowsB8_chunk008_checked.2]
private def rowsB9_chunk000 : List ℕ := [
  0x18201810098603620120a060301a100804123120a06030180c064341c1008040209108c4826140c06030180c063341b100,
  0x202018100a0604020120c060311a100804223130a06030180c266361c100804020d108c4826180c06030180c064341b100,
  0x1028241a110c0644021120c060311b100804223130a06030180c2663620100804021110904826180c06030180c064341b100,
  0x1030241a110c0644021130c060321b100804324130c06030180c4663620100804021110904c26180c06030180c064341b100]
private theorem rowsB9_chunk000_checked :
    rowsB9_chunk000.length = 4 ∧ rowsSum 1860 rowsB9_chunk000 = 109742129 := by
  constructor
  · rfl
  · rw [bRows_eq 1860 rowsB9_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB9_chunk004 : List ℕ := [
  0x2030281c120c0684022130c060331b100804324130c06030180c6683620100804021110904c26180c06030180c1643420100,
  0x30383020130c06c4023130c060331c100804424130c06030180c6683620100804021918904c26180c06030180c1643420100]
private theorem rowsB9_chunk004_checked :
    rowsB9_chunk004.length = 2 ∧ rowsSum 1864 rowsB9_chunk004 = 56116171 := by
  constructor
  · rfl
  · rw [bRows_eq 1864 rowsB9_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB9 : List ℕ := rowsB9_chunk000 ++ rowsB9_chunk004
private theorem rowsB9_checked :
    rowsB9.length = 6 ∧ rowsSum 1860 rowsB9 = 165858300 := by
  constructor
  · simp only [rowsB9, List.length_append, Nat.reduceAdd, rowsB9_chunk000_checked.1,
      rowsB9_chunk004_checked.1]
  · simp only [rowsB9, rowsSum_append, Nat.reduceAdd, rowsB9_chunk000_checked.1,
      rowsB9_chunk000_checked.2, rowsB9_chunk004_checked.2]
def rowsB : List ℕ := rowsB1 ++ rowsB2 ++ rowsB3 ++ rowsB4 ++ rowsB5 ++ rowsB6 ++ rowsB7 ++ rowsB8 ++ rowsB9
theorem rowsB_length : rowsB.length = 108 := by
  simp only [rowsB, List.length_append, Nat.reduceAdd,
    rowsB1_checked.1, rowsB2_checked.1, rowsB3_checked.1, rowsB4_checked.1,
    rowsB5_checked.1, rowsB6_checked.1, rowsB7_checked.1, rowsB8_checked.1,
    rowsB9_checked.1]
theorem rowsB_sum : rowsSum 1758 rowsB = 2005983713 := by
  simp only [rowsB, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsB1_checked.1, rowsB2_checked.1, rowsB3_checked.1, rowsB4_checked.1,
    rowsB5_checked.1, rowsB6_checked.1, rowsB7_checked.1, rowsB8_checked.1,
    rowsB1_checked.2, rowsB2_checked.2, rowsB3_checked.2, rowsB4_checked.2,
    rowsB5_checked.2, rowsB6_checked.2, rowsB7_checked.2, rowsB8_checked.2,
    rowsB9_checked.2]
end K1_13_2_3_4
end
section
namespace K1_13_2_3_4
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0
open K1_13_2
private theorem ddDenNeg {v : ℤ} (hv : v < 0) : denominator v = 0 := by
  simp [denominator, hv]
private theorem ddCumNeg {d v : ℤ} (hv : v < 0) : cumulative d v = 0 := by
  simp [cumulative, hv]
private theorem ddCum {d v : ℤ} (hd : 0 ≤ d) (hv : v ≤ d) :
    cumulative d v = denominator v := by
  by_cases h : v < 0
  · rw [ddCumNeg h, ddDenNeg h]
  simp only [cumulative, show ¬ d < 0 by omega, h, decide_false, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, min_eq_left (show v ≤ 3 * d by omega)]
  simp only [ddDenNeg (show v - d - 1 < 0 by omega),
    ddDenNeg (show v - d - 2 < 0 by omega), ddDenNeg (show v - d - 3 < 0 by omega),
    ddDenNeg (show v - 2 * d - 3 < 0 by omega),
    ddDenNeg (show v - 2 * d - 4 < 0 by omega),
    ddDenNeg (show v - 2 * d - 5 < 0 by omega),
    ddDenNeg (show v - 3 * d - 6 < 0 by omega), sub_zero, add_zero]
private theorem ddCumBelow {d v : ℤ} (hv : v ≤ d) : cumulative d v = denominator v := by
  by_cases hd : 0 ≤ d
  · exact ddCum hd hv
  · rw [ddCumNeg (by omega), ddDenNeg (by omega)]
private theorem ddCap {d v c : ℤ} (hd : 0 ≤ d) (hc : 0 ≤ c) (hv : v ≤ d)
    (hcap : v < 3 * (c + 1)) : cappedCount d v c = denominator v := by
  simp [cappedCount, show ¬ c < 0 by omega, ddCum hd hv,
    ddCumNeg (show v - 3 * (c + 1) < 0 by omega)]
private def ddFlag (s q k : ℤ) : Flag :=
  ⟨1650 - 3 * k, s - 1350 - q - 2 * k, 1650 - 3 * k, 550 - k, 1650 - q - 3 * k⟩
private def ddOld (s q k : ℤ) : ℤ :=
  denominator (1650 - 3 * k) - denominator (s - 1350 - q - 2 * k - 1)
private def ddTarget (q k : ℤ) : ℤ := denominator (1650 - q - 3 * k - 1)
private theorem ddOldEq {s q k : ℤ} (hs : s ≤ 2007) (hq : 0 ≤ q)
    (hk : 0 ≤ k) (hk' : k < 512) : oldCount (ddFlag s q k) = ddOld s q k := by
  dsimp only [oldCount, ddFlag, ddOld]
  rw [min_eq_right (by omega), ddCap (by omega) (by omega) (by omega) (by omega),
    ddCap (by omega) (by omega) (by omega) (by omega)]
private theorem ddTargetEq {s q k : ℤ} (hs : 1943 ≤ s) (hs' : s ≤ 2007)
    (hq : 0 ≤ q) (hq' : q ≤ 70) (hk : 0 ≤ k) (hk' : k < 512) :
    targetCount (ddFlag s q k) = ddTarget q k := by
  dsimp only [targetCount, ddFlag, ddTarget]
  rw [ite_eq_right (by omega)]
  let removed := min (1650 - 3 * k)
    ((1650 - q - 3 * k - 1 - (s - 1350 - q - 2 * k) + (1650 - 3 * k)) / 4) + 1
  have hv : 1650 - q - 3 * k - 1 - 3 * removed < 0 := by
    dsimp [removed]
    omega
  rw [ddCumNeg hv, ddCumBelow (by omega), ddCumBelow (by omega), ddCumBelow (by omega)]
  omega
private theorem ddKernelEq {s q k : ℤ} (hs : 1943 ≤ s) (hs' : s ≤ 2007)
    (hq : 0 ≤ q) (hq' : q ≤ 70) (hk : 0 ≤ k) (hk' : k < 512) :
    kernelLower (ddFlag s q k) = ddOld s q k - ddTarget q k := by
  simp only [kernelLower, ddFlag, show ¬ (1650 : ℤ) - 3 * k < 0 by omega,
    show ¬ (550 : ℤ) - k < 0 by omega, decide_false, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte]
  rw [← ddOldEq hs' hq hk hk', ← ddTargetEq hs hs' hq hq' hk hk']
  rfl
private theorem ddWindow {s q : ℕ} (hs : 1943 ≤ s) (hs' : s ≤ 2007) :
    windowFlag s (3000 + q - s) = ddFlag s q 0 := by
  simp only [windowFlag, ddFlag, mul_zero, sub_zero]
  congr 1 <;> omega
private theorem ddCubic (s q : ℤ) (k : ℕ) : cubicFlag (ddFlag s q 0) k = ddFlag s q k := by
  simp [ddFlag, cubicFlag]
private def ddSaving (s q k : ℕ) : ℕ :=
  let old := ddOld s q 0
  let lower := max 0 (old - ddTarget q 0)
  (old - lower).toNat -
    (old - max lower (ddOld s q k - ddTarget q k)).toNat
private theorem ddSavingEq {s q k : ℕ} (hs : 1943 ≤ s) (hs' : s ≤ 2007)
    (hq' : q ≤ 70) (hk' : k < 512) :
    entry s q k = ddSaving s q k := by
  have hj : 993 ≤ 3000 + q - s ∧ 3000 + q - s ≤ 1581 := by omega
  by_cases hk : k = 0
  · subst k
    simp [entry, cubicSavings, ddSaving]
  simp only [entry, hj, and_self, ↓reduceIte, cubicSavings, hk, ddWindow hs hs', ddCubic, ddSaving]
  rw [ddKernelEq (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    ddKernelEq (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    ddOldEq (by omega) (by omega) (by omega) (by omega)]
private def ddDenNat (u : ℕ) : ℕ := (((2 * u + 21) * u + 66) * u + 72) / 72
private theorem ddEvenPair (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have hm : x * (x - 1) % 2 = 0 := by
    rw [Int.mul_emod, Int.sub_emod]
    rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with h | h <;> norm_num [h]
  omega
private theorem ddDenPoly (x r : ℤ) :
    1 + r * (r + 1) / 2 + x * (22 + 7 * r + r * (r - 1) / 2) + (57 + 6 * r) * (x * (x - 1) / 2) +
      6 * x * (x - 1) * (x - 2) =
    (((12 * x + 21 + 6 * r) * x + 11 + 7 * r + r * r) * x + 2 + r + r * r) / 2 := by
  have hp : 2 * (r * (r + 1) / 2) = r * (r + 1) := by
    simpa only [add_sub_cancel_right, mul_comm (r + 1) r] using ddEvenPair (r + 1)
  have he : 2 * (1 + r * (r + 1) / 2 + x * (22 + 7 * r + r * (r - 1) / 2) + (57 + 6 * r) * (x * (x - 1) / 2) +
      6 * x * (x - 1) * (x - 2)) = (((12 * x + 21 + 6 * r) * x + 11 + 7 * r + r * r) * x + 2 + r + r * r) := by
    linear_combination hp + x * ddEvenPair r + (57 + 6 * r) * ddEvenPair x
  omega
private theorem ddRoundCubic (x r : ℤ) (hr : 0 ≤ r) (hr' : r < 6) :
    (((12 * x + 21 + 6 * r) * x + 11 + 7 * r + r * r) * x + 2 + r + r * r) / 2 =
      (((2 * (6 * x + r) + 21) * (6 * x + r) + 66) * (6 * x + r) + 72) / 72 := by
  have hc : 0 ≤ 2 * r ^ 3 - 15 * r ^ 2 + 30 * r ∧ 2 * r ^ 3 - 15 * r ^ 2 + 30 * r < 36 := by
    interval_cases r <;> decide
  have he : ((2 * (6 * x + r) + 21) * (6 * x + r) + 66) * (6 * x + r) + 72 =
      36 * (((12 * x + 21 + 6 * r) * x + 11 + 7 * r + r * r) * x + 2 + r + r * r) + (2 * r ^ 3 - 15 * r ^ 2 + 30 * r) := by ring
  rw [he]
  omega
private theorem ddDenCorrect (i : ℕ) : denominator (i : ℤ) = ddDenNat i := by
  simp only [denominator, ddDenNat, show ¬ (i : ℤ) < 0 by omega, ↓reduceIte,
    Int.natCast_ediv, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add]
  rw [ddDenPoly, ddRoundCubic _ _ (by omega) (by omega),
    show 6 * ((i : ℤ) / 6) + (i : ℤ) % 6 = i by omega]
private def ddBefore (u : ℕ) : ℕ := (((2 * u + 15) * u + 30) * u + 25) / 72
private theorem ddBeforeSucc (u : ℕ) : ddBefore (u + 1) = ddDenNat u := by
  unfold ddBefore ddDenNat
  congr 1
  ring
private theorem ddBeforeEq (a b : ℕ) :
    denominator ((a : ℤ) - b - 1) = (ddBefore (a - b) : ℤ) := by
  by_cases h : a ≤ b
  · simp only [Nat.sub_eq_zero_of_le h, ddDenNeg (show (a : ℤ) - b - 1 < 0 by omega),
      show ddBefore 0 = 0 from rfl, Nat.cast_zero]
  · have he : (a : ℤ) - b - 1 = ((a - b - 1 : ℕ) : ℤ) := by omega
    rw [he, ddDenCorrect, ← ddBeforeSucc, show a - b - 1 + 1 = a - b by omega]
private def ddNatSaving (s q k : ℕ) : ℕ :=
  let old := ddDenNat 1650 - ddBefore (s - (1350 + q))
  let lower := old - ddDenNat (1649 - q)
  let other := ddDenNat (1650 - 3 * k) - ddBefore (s - (1350 + q + 2 * k)) - ddDenNat (1649 - q - 3 * k)
  (old - lower) - (old - max lower other)
private theorem ddNatSavingEq {s q k : ℕ} (hq : q ≤ 70) (hk : k < 512) :
    ddSaving s q k = ddNatSaving s q k := by
  have h₁ : ∀ c : ℕ, c < 512 → ddOld s q c =
      (ddDenNat (1650 - 3 * c) : ℤ) - ddBefore (s - (1350 + q + 2 * c)) := by
    intro c hc
    unfold ddOld
    rw [show (1650 : ℤ) - 3 * c = ((1650 - 3 * c : ℕ) : ℤ) by omega, ddDenCorrect,
      show (s : ℤ) - 1350 - q - 2 * c = (s : ℤ) - ((1350 + q + 2 * c : ℕ) : ℤ) by omega,
      ddBeforeEq]
  have h₂ : ∀ c : ℕ, c < 512 → ddTarget q c = ddDenNat (1649 - q - 3 * c) := by
    intro c hc
    unfold ddTarget
    rw [show (1650 : ℤ) - q - 3 * c - 1 = ((1649 - q - 3 * c : ℕ) : ℤ) by omega, ddDenCorrect]
  have hb := h₁ 0 (by omega)
  have ht := h₂ 0 (by omega)
  simp only [Nat.cast_zero, Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hb ht
  simp only [ddSaving, ddNatSaving, hb, ht, h₁ k hk, h₂ k hk]
  omega
private def ddPrefix (s code : ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => ddNatSaving s q ((code >>> (9 * q)) % 512) + ddPrefix s code q
private theorem ddPrefixEq {s : ℕ} (hs : 1943 ≤ s) (hs' : s ≤ 2007)
    (code q n : ℕ) (hq : q + n ≤ 71) :
    rowSum s q (code / 512 ^ q) n + ddPrefix s code q = ddPrefix s code (q + n) := by
  induction n generalizing q with
  | zero => simp [rowSum]
  | succ n ih =>
    have hk := Nat.mod_lt (code / 512 ^ q) (by decide : 0 < 512)
    rw [rowSum, ddSavingEq hs hs' (by omega) hk, ddNatSavingEq (by omega) hk,
      Nat.div_div_eq_div_mul, ← pow_succ]
    have hi := ih (q + 1) (by omega)
    have hd : code >>> (9 * q) = code / 512 ^ q := by
      simp only [Nat.shiftRight_eq_div_pow, pow_mul, show (2 : ℕ) ^ 9 = 512 from rfl]
    rw [ddPrefix, hd] at hi
    rw [show q + (n + 1) = q + 1 + n by omega]
    omega
private theorem ddSingle {s code total : ℕ}
    (h : 1943 ≤ s ∧ s ≤ 2007 ∧ ddPrefix s code 71 = total) :
    [code].length = 1 ∧ rowsSum s [code] = total := by
  have he := ddPrefixEq h.1 h.2.1 code 0 71 (by decide)
  simp only [pow_zero, Nat.div_one, Nat.zero_add, show ddPrefix s code 0 = 0 from rfl,
    Nat.add_zero] at he
  exact ⟨rfl, (Nat.add_zero _).trans (he.trans h.2.2)⟩
private def rowsD1_row1943 : List ℕ := [
  0x40a080604026180d8804426180c0623420100804424130c06030180c064341b100804020102864423120984c30180c06030180c06132198d06c4020100804020d10]
private theorem rowsD1_row1943_checked :
    rowsD1_row1943.length = 1 ∧ rowsSum 1943 rowsD1_row1943 = 48532032 := ddSingle (by decide +kernel)
private def rowsD1_row1944 : List ℕ := [
  0x80c090604028180d8804626180c0643620100824424130c06030180c064341b100804020102864624120984c30180c06030180c061b2198d06c4020100804020d10]
private theorem rowsD1_row1944_checked :
    rowsD1_row1944.length = 1 ∧ rowsSum 1944 rowsD1_row1944 = 48859683 := ddSingle (by decide +kernel)
private def rowsD1_row1945 : List ℕ := [
  0x80c0a0684430180e0804628180c0643620100844624130c06030180c266341b100804020104864624120985030180c06030180c062321a0d86c4020100804020d10]
private theorem rowsD1_row1945_checked :
    rowsD1_row1945.length = 1 ∧ rowsSum 1945 rowsD1_row1945 = 49189053 := ddSingle (by decide +kernel)
private def rowsD1_row1946 : List ℕ := [
  0xc0e0c070443019100804828180c0663620100844624130c06030180c466341b100804020106884624130985030180c06030180c062321a0d86c4020100804020d10]
private theorem rowsD1_row1946_checked :
    rowsD1_row1946.length = 1 ∧ rowsSum 1946 rowsD1_row1946 = 49521319 := ddSingle (by decide +kernel)
private def rowsD1_row1947 : List ℕ := [
  0x10100c080483019100844830180c0683820100864626140c06030180c466361c100804020106884624130985030180c06030180c062331a0d86c4020100804021110]
private theorem rowsD1_row1947_checked :
    rowsD1_row1947.length = 1 ∧ rowsSum 1947 rowsD1_row1947 = 49852962 := ddSingle (by decide +kernel)
private def rowsD1_row1948 : List ℕ := [
  0x810100c0804c301a100884c30180c0684020100884826140c06030180c666361c100804020108884624130985030180c06030180c063331a0d86c4020100804021110]
private theorem rowsD1_row1948_checked :
    rowsD1_row1948.length = 1 ∧ rowsSum 1948 rowsD1_row1948 = 50188791 := ddSingle (by decide +kernel)
private def rowsD1_row1949 : List ℕ := [
  0x814120c0804c301b100884c30180c4684020100884826180c06030180c8683620100804020108884624130986030180c06030180c163331a0d8704020100804021110]
private theorem rowsD1_row1949_checked :
    rowsD1_row1949.length = 1 ∧ rowsSum 1949 rowsD1_row1949 = 50412605 := ddSingle (by decide +kernel)
private def rowsD1_row1950 : List ℕ := [
  0x1018120d08060301b1008c4c30180c86c4020104884826180c06030180c868362010080402050c884624130986030180c06030180c163331a0d8704020100804021118]
private theorem rowsD1_row1950_checked :
    rowsD1_row1950.length = 1 ∧ rowsSum 1950 rowsD1_row1950 = 50748619 := ddSingle (by decide +kernel)
private def rowsD1 : List ℕ :=
    rowsD1_row1943 ++ rowsD1_row1944 ++ rowsD1_row1945 ++
    rowsD1_row1946 ++ rowsD1_row1947 ++ rowsD1_row1948 ++
    rowsD1_row1949 ++ rowsD1_row1950
private theorem rowsD1_checked :
    rowsD1.length = 8 ∧ rowsSum 1943 rowsD1 = 397305064 := by
  constructor <;> simp only [rowsD1, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD1_row1943_checked.1, rowsD1_row1943_checked.2,
    rowsD1_row1944_checked.1, rowsD1_row1944_checked.2,
    rowsD1_row1945_checked.1, rowsD1_row1945_checked.2,
    rowsD1_row1946_checked.1, rowsD1_row1946_checked.2,
    rowsD1_row1947_checked.1, rowsD1_row1947_checked.2,
    rowsD1_row1948_checked.1, rowsD1_row1948_checked.2,
    rowsD1_row1949_checked.1, rowsD1_row1949_checked.2,
    rowsD1_row1950_checked.1, rowsD1_row1950_checked.2]
private def rowsD2_row1951 : List ℕ := [
  0x1818140d088603020100905030180c86c40201088c4826180c06030184c868362010080402090c8c4824130986030180c06030180c264331a0d8704020100804021118]
private theorem rowsD2_row1951_checked :
    rowsD2_row1951.length = 1 ∧ rowsSum 1951 rowsD2_row1951 = 51076092 := ddSingle (by decide +kernel)
private def rowsD2_row1952 : List ℕ := [
  0x181c1810090603220100905030180cc6c40201088c4826180c06030184cc68362010080402090c8c4824130a06030180c06030180c264331a0d8804020100804061118]
private theorem rowsD2_row1952_checked :
    rowsD2_row1952.length = 1 ∧ rowsSum 1952 rowsD2_row1952 = 51364774 := ddSingle (by decide +kernel)
private def rowsD2_row1953 : List ℕ := [
  0x20201810090603420108906030180d070402010c8c4c28180c06030188cc6c3820100804020d108c4826130a06030180c06030180c364331a0d8804020100804061918]
private theorem rowsD2_row1953_checked :
    rowsD2_row1953.length = 1 ∧ rowsSum 1953 rowsD2_row1953 = 51696017 := ddSingle (by decide +kernel)
private def rowsD2_row1954 : List ℕ := [
  0x1028201810098603420110986030188d0804020110904c28180c0603018ccc6c3820100804020d108c4826130a06030180c06030180c464341a0d88040201008040a1918]
private theorem rowsD2_row1954_checked :
    rowsD2_row1954.length = 1 ∧ rowsSum 1954 rowsD2_row1954 = 52031837 := ddSingle (by decide +kernel)
private def rowsD2_row1955 : List ℕ := [
  0x2030241a100a0603620110986030188d8804020110904c28180c0603018cd06c38201008040211108c4826130a06030180c06030180c464341b0d88040201008040a1918]
private theorem rowsD2_row1955_checked :
    rowsD2_row1955.length = 1 ∧ rowsSum 1955 rowsD2_row1955 = 52377791 := ddSingle (by decide +kernel)
private def rowsD2_row1956 : List ℕ := [
  0x2030281a110c0603820118986030190d8804020910904c30180c06030190d06c40201008040211108c4826130c06030180c06030180c464341b0d88040201008040e1918]
private theorem rowsD2_row1956_checked :
    rowsD2_row1956.length = 1 ∧ rowsSum 1956 rowsD2_row1956 = 52601764 := ddSingle (by decide +kernel)
private def rowsD2_row1957 : List ℕ := [
  0x3038301c110c0644020120a06030198d8804021118904c30180c06030990d06c40201008040a19108c4826130c06030180c06030180c666341b0d88040201008040e1918]
private theorem rowsD2_row1957_checked :
    rowsD2_row1957.length = 1 ∧ rowsSum 1957 rowsD2_row1957 = 52957221 := ddSingle (by decide +kernel)
private def rowsD2 : List ℕ :=
    rowsD2_row1951 ++ rowsD2_row1952 ++ rowsD2_row1953 ++
    rowsD2_row1954 ++ rowsD2_row1955 ++ rowsD2_row1956 ++
    rowsD2_row1957
private theorem rowsD2_checked :
    rowsD2.length = 7 ∧ rowsSum 1951 rowsD2 = 364105496 := by
  constructor <;> simp only [rowsD2, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD2_row1951_checked.1, rowsD2_row1951_checked.2,
    rowsD2_row1952_checked.1, rowsD2_row1952_checked.2,
    rowsD2_row1953_checked.1, rowsD2_row1953_checked.2,
    rowsD2_row1954_checked.1, rowsD2_row1954_checked.2,
    rowsD2_row1955_checked.1, rowsD2_row1955_checked.2,
    rowsD2_row1956_checked.1, rowsD2_row1956_checked.2,
    rowsD2_row1957_checked.1, rowsD2_row1957_checked.2]
private def rowsD3_row1958 : List ℕ := [
  0x40403020120c0644021120c06030198e0804021118904c30180c06030998d06c4020100804121918904826130c06030180c06030182c666341b0d8804020100804121918]
private theorem rowsD3_row1958_checked :
    rowsD3_row1958.length = 1 ∧ rowsSum 1958 rowsD3_row1958 = 53310127 := ddSingle (by decide +kernel)
private def rowsD3_row1959 : List ℕ := [
  0x2040403020130c0684021130c060301a0e0804021918985030180c06031198d06c4020100804121918904826140c06030180c06030182c666341b0e0804020100804121918]
private theorem rowsD3_row1959_checked :
    rowsD3_row1959.length = 1 ∧ rowsSum 1959 rowsD3_row1959 = 53653364 := ddSingle (by decide +kernel)
private def rowsD3_row1960 : List ℕ := [
  0x2060483020130c06c4022130c060311a100804022120985030180c06031998d87040201008041a2118904826140c06030180c06030184c866341b0e08040201008041a2118]
private theorem rowsD3_row1960_checked :
    rowsD3_row1960.length = 1 ∧ rowsSum 1960 rowsD3_row1960 = 53987134 := ddSingle (by decide +kernel)
private def rowsD3_row1961 : List ℕ := [
  0x4060483420180c06c4023130c060311b100804022120985030180c060319a0d8704020100804222118904c26140c06030180c06030186c866341b0e08040201008041a2118]
private theorem rowsD3_row1961_checked :
    rowsD3_row1961.length = 1 ∧ rowsSum 1961 rowsD3_row1961 = 54330098 := ddSingle (by decide +kernel)
private def rowsD3_row1962 : List ℕ := [
  0x6060503822180c0804023140c060321b100804122120986030180c060321a0d8804020100804222118904c26140c06030180c06030186c866341b1008040201008041a2118]
private theorem rowsD3_row1962_checked :
    rowsD3_row1962.length = 1 ∧ rowsSum 1962 rowsD3_row1962 = 54579573 := ddSingle (by decide +kernel)
private def rowsD3_row1963 : List ℕ := [
  0x6080604024180c8804024140c060331b100804223120986030180c061321a0d8804020100814222118904c26140c06030180c06030188c866341b1008040201008041a2118]
private theorem rowsD3_row1963_checked :
    rowsD3_row1963.length = 1 ∧ rowsSum 1963 rowsD3_row1963 = 54934116 := ddSingle (by decide +kernel)
private def rowsD3_row1964 : List ℕ := [
  0x408080604024180d0804224180c060331c100804223130986030180c061331a0d8804020100814322118904c26180c06030180c06030188c868341b100804020100804222118]
private theorem rowsD3_row1964_checked :
    rowsD3_row1964.length = 1 ∧ rowsSum 1964 rowsD3_row1964 = 55210710 := ddSingle (by decide +kernel)
private def rowsD3 : List ℕ :=
    rowsD3_row1958 ++ rowsD3_row1959 ++ rowsD3_row1960 ++
    rowsD3_row1961 ++ rowsD3_row1962 ++ rowsD3_row1963 ++
    rowsD3_row1964
private theorem rowsD3_checked :
    rowsD3.length = 7 ∧ rowsSum 1958 rowsD3 = 380005122 := by
  constructor <;> simp only [rowsD3, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD3_row1958_checked.1, rowsD3_row1958_checked.2,
    rowsD3_row1959_checked.1, rowsD3_row1959_checked.2,
    rowsD3_row1960_checked.1, rowsD3_row1960_checked.2,
    rowsD3_row1961_checked.1, rowsD3_row1961_checked.2,
    rowsD3_row1962_checked.1, rowsD3_row1962_checked.2,
    rowsD3_row1963_checked.1, rowsD3_row1963_checked.2,
    rowsD3_row1964_checked.1, rowsD3_row1964_checked.2]
private def rowsD4_row1965 : List ℕ := [
  0x40a080604026180d0804426180c060341c100804323130a06030180c062331a0d8804020100824323120904c26180c06030180c06030188cc68361b100804020100804222120]
private theorem rowsD4_row1965_checked :
    rowsD4_row1965.length = 1 ∧ rowsSum 1965 rowsD4_row1965 = 55576301 := ddSingle (by decide +kernel)
private def rowsD4_row1966 : List ℕ := [
  0x80c090684028180d8804426180c0623420100804424130a06030180c062331b0e0804020100834323120904c26180c06030180c0603058ccc68361b100804020100804222120]
private theorem rowsD4_row1966_checked :
    rowsD4_row1966.length = 1 ∧ rowsSum 1966 rowsD4_row1966 = 55938580 := ddSingle (by decide +kernel)
private def rowsD4_row1967 : List ℕ := [
  0xc0c0a0684430180e0804626180c0643620100824424130c06030180c063331b0e0804020100834423120904c28180c06030180c0603058ccc68361b10080402010080c222120]
private theorem rowsD4_row1967_checked :
    rowsD4_row1967.length = 1 ∧ rowsSum 1967 rowsD4_row1967 = 56277297 := ddSingle (by decide +kernel)
private def rowsD4_row1968 : List ℕ := [
  0xc0e0c070483019100804828180c0643620100824624130c06030180c064341b0e0804020100844423120984c28180c06030180c0603098ccc68361b10080402010080c222120]
private theorem rowsD4_row1968_checked :
    rowsD4_row1968.length = 1 ∧ rowsSum 1968 rowsD4_row1968 = 56624711 := ddSingle (by decide +kernel)
private def rowsD4_row1969 : List ℕ := [
  0x10100c080483019100844830180c0663620100844624130c06030180c064341b100804020100844423120984c28180c06030180c06030990cc68361c100804020100814222120]
private theorem rowsD4_row1969_checked :
    rowsD4_row1969.length = 1 ∧ rowsSum 1969 rowsD4_row1969 = 56945987 := ddSingle (by decide +kernel)
private def rowsD4_row1970 : List ℕ := [
  0x814100c0804c301a100844c30180c0683820100864626130c06030180c264341b100804020102864423120984c28180c06030180c06030d90cc68361c100804020100814322120]
private theorem rowsD4_row1970_checked :
    rowsD4_row1970.length = 1 ∧ rowsSum 1970 rowsD4_row1970 = 57303937 := ddSingle (by decide +kernel)
private def rowsD4_row1971 : List ℕ := [
  0x1018120c08050301b100884c30180c4684020100864626140c06030180c466341b100804020104864423120984c30180c06030180c06031190cc68361c10080402010081c323120]
private theorem rowsD4_row1971_checked :
    rowsD4_row1971.length = 1 ∧ rowsSum 1971 rowsD4_row1971 = 57581502 := ddSingle (by decide +kernel)
private def rowsD4 : List ℕ :=
    rowsD4_row1965 ++ rowsD4_row1966 ++ rowsD4_row1967 ++
    rowsD4_row1968 ++ rowsD4_row1969 ++ rowsD4_row1970 ++
    rowsD4_row1971
private theorem rowsD4_checked :
    rowsD4.length = 7 ∧ rowsSum 1965 rowsD4 = 396248315 := by
  constructor <;> simp only [rowsD4, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD4_row1965_checked.1, rowsD4_row1965_checked.2,
    rowsD4_row1966_checked.1, rowsD4_row1966_checked.2,
    rowsD4_row1967_checked.1, rowsD4_row1967_checked.2,
    rowsD4_row1968_checked.1, rowsD4_row1968_checked.2,
    rowsD4_row1969_checked.1, rowsD4_row1969_checked.2,
    rowsD4_row1970_checked.1, rowsD4_row1970_checked.2,
    rowsD4_row1971_checked.1, rowsD4_row1971_checked.2]
private def rowsD5_row1972 : List ℕ := [
  0x1018120d08860301b1008c4c30180c46c4020100884826140c06030180c466361c100804020104864624120984c30180c06030180c06031190d0683620100804020100824323120]
private theorem rowsD5_row1972_checked :
    rowsD5_row1972.length = 1 ∧ rowsSum 1972 rowsD5_row1972 = 57898819 := ddSingle (by decide +kernel)
private def rowsD5_row1973 : List ℕ := [
  0x181c180e0886032201008c4c30180c86c4020104884826180c06030180c666361c100804020106864624120984c30180c06030180c06031190d0683620100804020100824323120]
private theorem rowsD5_row1973_checked :
    rowsD5_row1973.length = 1 ∧ rowsSum 1973 rowsD5_row1973 = 58241930 := ddSingle (by decide +kernel)
private def rowsD5_row1974 : List ℕ := [
  0x20201810090603220100905030180cc6c40201048c4826180c06030180c868361c100804020106884624130985030180c06030180c060b1998d06c3620100804020100824323120]
private theorem rowsD5_row1974_checked :
    rowsD5_row1974.length = 1 ∧ rowsSum 1974 rowsD5_row1974 = 58621160 := ddSingle (by decide +kernel)
private def rowsD5_row1975 : List ℕ := [
  0x1020201810098603420108906030180cc6c40201088c4826180c06030180c8683620100804020108884624130985030180c06030180c060b1998d06c3620100804020100834323120]
private theorem rowsD5_row1975_checked :
    rowsD5_row1975.length = 1 ∧ rowsSum 1975 rowsD5_row1975 = 58973106 := ddSingle (by decide +kernel)
private def rowsD5_row1976 : List ℕ := [
  0x2030241810098603620110986030180d070402010c8c4c28180c06030184c8683620100804020508884624130985030180c06030180c06131998d06c3620100804020100834323120]
private theorem rowsD5_row1976_checked :
    rowsD5_row1976.length = 1 ∧ rowsSum 1976 rowsD5_row1976 = 59337501 := ddSingle (by decide +kernel)
private def rowsD5_row1977 : List ℕ := [
  0x2030241a100c0603620110986030188d080402010c904c28180c06030188cc68362010080402050c884624130985030180c06030180c06132198d06c3620100804020100834423180]
private theorem rowsD5_row1977_checked :
    rowsD5_row1977.length = 1 ∧ rowsSum 1977 rowsD5_row1977 = 59662769 := ddSingle (by decide +kernel)
private def rowsD5_row1978 : List ℕ := [
  0x3030281c110c0603820118986030190d8804020110904c28180c06030188cc6c382010080402090c8c4824130986030180c06030180c061b2198d06c3620100804020100834423180]
private theorem rowsD5_row1978_checked :
    rowsD5_row1978.length = 1 ∧ rowsSum 1978 rowsD5_row1978 = 59950487 := ddSingle (by decide +kernel)
private def rowsD5 : List ℕ :=
    rowsD5_row1972 ++ rowsD5_row1973 ++ rowsD5_row1974 ++
    rowsD5_row1975 ++ rowsD5_row1976 ++ rowsD5_row1977 ++
    rowsD5_row1978
private theorem rowsD5_checked :
    rowsD5.length = 7 ∧ rowsSum 1972 rowsD5 = 412685772 := by
  constructor <;> simp only [rowsD5, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD5_row1972_checked.1, rowsD5_row1972_checked.2,
    rowsD5_row1973_checked.1, rowsD5_row1973_checked.2,
    rowsD5_row1974_checked.1, rowsD5_row1974_checked.2,
    rowsD5_row1975_checked.1, rowsD5_row1975_checked.2,
    rowsD5_row1976_checked.1, rowsD5_row1976_checked.2,
    rowsD5_row1977_checked.1, rowsD5_row1977_checked.2,
    rowsD5_row1978_checked.1, rowsD5_row1978_checked.2]
private def rowsD6_row1979 : List ℕ := [
  0x40403020120c0644020120a06030190d8804020910904c30180c0603018ccc6c3820100804020d0c8c4824130986030180c06030180c06232198d06c3820100804020100844423180]
private theorem rowsD6_row1979_checked :
    rowsD6_row1979.length = 1 ∧ rowsSum 1979 rowsD6_row1979 = 60292859 := ddSingle (by decide +kernel)
private def rowsD6_row1980 : List ℕ := [
  0x2040403020120c0684021120c06030198d8804021118904c30180c06030190d06c3820100804020d108c4824130986030180c06030180c06232198d06c3820100804020101844423180]
private theorem rowsD6_row1980_checked :
    rowsD6_row1980.length = 1 ∧ rowsSum 1980 rowsD6_row1980 = 60662595 := ddSingle (by decide +kernel)
private def rowsD6_row1981 : List ℕ := [
  0x2050403020130c0684021130c060301a0e0804021118904c30180c06030190d06c40201008040211108c4826130a06030180c06030180c062321a0d06c3820100804020101844423180]
private theorem rowsD6_row1981_checked :
    rowsD6_row1981.length = 1 ∧ rowsSum 1981 rowsD6_row1981 = 61019904 := ddSingle (by decide +kernel)
private def rowsD6_row1982 : List ℕ := [
  0x4060483420140c06c4022130c060311a0e0804021918985030180c06030990d06c40201008040211108c4826130a06030180c06030180c163331a0d06c4020100804020102844423180]
private theorem rowsD6_row1982_checked :
    rowsD6_row1982.length = 1 ∧ rowsSum 1982 rowsD6_row1982 = 61356710 := ddSingle (by decide +kernel)
private def rowsD6_row1983 : List ℕ := [
  0x6060503422180c0704023130c060311a100804022120985030180c06031198d06c40201008040a19108c4826130a06030180c06030180c163331a0d86c4020100804020102844423180]
private theorem rowsD6_row1983_checked :
    rowsD6_row1983.length = 1 ∧ rowsSum 1983 rowsD6_row1983 = 61740488 := ddSingle (by decide +kernel)
private def rowsD6_row1984 : List ℕ := [
  0x6070604024180c8804023140c060321b100804122120985030180c06031198d86c40201008041219108c4826130a06030180c06030180c263331a0d86c4020100804020103864423180]
private theorem rowsD6_row1984_checked :
    rowsD6_row1984.length = 1 ∧ rowsSum 1984 rowsD6_row1984 = 62116571 := ddSingle (by decide +kernel)
private def rowsD6_row1985 : List ℕ := [
  0x408080604024180c8804224140c060331b100804122120986030180c06031998d8704020100804121918904826130c06030180c06030180c264331a0d86c4020100804020104864423180]
private theorem rowsD6_row1985_checked :
    rowsD6_row1985.length = 1 ∧ rowsSum 1985 rowsD6_row1985 = 62380616 := ddSingle (by decide +kernel)
private def rowsD6 : List ℕ :=
    rowsD6_row1979 ++ rowsD6_row1980 ++ rowsD6_row1981 ++
    rowsD6_row1982 ++ rowsD6_row1983 ++ rowsD6_row1984 ++
    rowsD6_row1985
private theorem rowsD6_checked :
    rowsD6.length = 7 ∧ rowsSum 1979 rowsD6 = 429569743 := by
  constructor <;> simp only [rowsD6, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD6_row1979_checked.1, rowsD6_row1979_checked.2,
    rowsD6_row1980_checked.1, rowsD6_row1980_checked.2,
    rowsD6_row1981_checked.1, rowsD6_row1981_checked.2,
    rowsD6_row1982_checked.1, rowsD6_row1982_checked.2,
    rowsD6_row1983_checked.1, rowsD6_row1983_checked.2,
    rowsD6_row1984_checked.1, rowsD6_row1984_checked.2,
    rowsD6_row1985_checked.1, rowsD6_row1985_checked.2]
private def rowsD7_row1986 : List ℕ := [
  0x40a080604026180d0804224180c060331b100804223120986030180c060321a0d87040201008041a1918904826130c06030180c06030180c364331a0d86c4020100804020104864424180]
private theorem rowsD7_row1986_checked :
    rowsD7_row1986.length = 1 ∧ rowsSum 1986 rowsD7_row1986 = 62750730 := ddSingle (by decide +kernel)
private def rowsD7_row1987 : List ℕ := [
  0x80c090684028180d8804426180c060341c100804323120986030180c060321a0d8804020100804222118904826140c06030180c06030180c464331a0d8704020100804020104864424180]
private theorem rowsD7_row1987_checked :
    rowsD7_row1987.length = 1 ∧ rowsSum 1987 rowsD7_row1987 = 63106578 := ddSingle (by decide +kernel)
private def rowsD7_row1988 : List ℕ := [
  0xc0c0a0684430180d8804626180c0623420100804323130a06030180c061321a0d8804020100804222118904c26140c06030180c06030180c464331a0d8704020100804020106864624180]
private theorem rowsD7_row1988_checked :
    rowsD7_row1988.length = 1 ∧ rowsSum 1988 rowsD7_row1988 = 63484853 := ddSingle (by decide +kernel)
private def rowsD7_row1989 : List ℕ := [
  0xc0e0c070443018100804626180c0643620100804424130a06030180c062331a0d8804020100814222118904c26140c06030180c06030180c464341a0d8704020100804020106864624180]
private theorem rowsD7_row1989_checked :
    rowsD7_row1989.length = 1 ∧ rowsSum 1989 rowsD7_row1989 = 63874545 := ddSingle (by decide +kernel)
private def rowsD7_row1990 : List ℕ := [
  0x10100c080483019100804828180c0643620100824424130a06030180c062331b0d8804020100814322118904c26140c06030180c06030182c666341a0d8704020100804020106864624180]
private theorem rowsD7_row1990_checked :
    rowsD7_row1990.length = 1 ∧ rowsSum 1990 rowsD7_row1990 = 64269789 := ddSingle (by decide +kernel)
private def rowsD7_row1991 : List ℕ := [
  0x814100c0804c301a100844830180c0663620100844624130c06030180c063331b0e0804020100824323120904c26140c06030180c06030182c666341b0d8804020100804020106884624180]
private theorem rowsD7_row1991_checked :
    rowsD7_row1991.length = 1 ∧ rowsSum 1991 rowsD7_row1991 = 64582414 := ddSingle (by decide +kernel)
private def rowsD7_row1992 : List ℕ := [
  0x1018120c0804c301b100884c30180c0683820100844624130c06030180c064341b0e0804020100834323120904c26180c06030180c06030184c666341b0d8804020100804020308884624180]
private theorem rowsD7_row1992_checked :
    rowsD7_row1992.length = 1 ∧ rowsSum 1992 rowsD7_row1992 = 64894000 := ddSingle (by decide +kernel)
private def rowsD7 : List ℕ :=
    rowsD7_row1986 ++ rowsD7_row1987 ++ rowsD7_row1988 ++
    rowsD7_row1989 ++ rowsD7_row1990 ++ rowsD7_row1991 ++
    rowsD7_row1992
private theorem rowsD7_checked :
    rowsD7.length = 7 ∧ rowsSum 1986 rowsD7 = 446962909 := by
  constructor <;> simp only [rowsD7, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD7_row1986_checked.1, rowsD7_row1986_checked.2,
    rowsD7_row1987_checked.1, rowsD7_row1987_checked.2,
    rowsD7_row1988_checked.1, rowsD7_row1988_checked.2,
    rowsD7_row1989_checked.1, rowsD7_row1989_checked.2,
    rowsD7_row1990_checked.1, rowsD7_row1990_checked.2,
    rowsD7_row1991_checked.1, rowsD7_row1991_checked.2,
    rowsD7_row1992_checked.1, rowsD7_row1992_checked.2]
private def rowsD8_row1993 : List ℕ := [
  0x1818140d08860301b100884c30180c4683820100864626130c06030180c264341b100804020100834423120904c26180c06030180c06030186c866341b0d8804020100804020308884624180]
private theorem rowsD8_row1993_checked :
    rowsD8_row1993.length = 1 ∧ rowsSum 1993 rowsD8_row1993 = 65248059 := ddSingle (by decide +kernel)
private def rowsD8_row1994 : List ℕ := [
  0x181c180e08860301c1008c4c30180c4684020100884826140c06030180c266341b100804020100844423120984c28180c06030180c06030186c866341b0d8804020100804020508884624180]
private theorem rowsD8_row1994_checked :
    rowsD8_row1994.length = 1 ∧ rowsSum 1994 rowsD8_row1994 = 65628090 := ddSingle (by decide +kernel)
private def rowsD8_row1995 : List ℕ := [
  0x20201810090603220100905030180c86c4020104884826140c06030180c466341b100804020102844423120984c28180c06030180c06030188c866341b0d8804020100804020508884624180]
private theorem rowsD8_row1995_checked :
    rowsD8_row1995.length = 1 ∧ rowsSum 1995 rowsD8_row1995 = 66018413 := ddSingle (by decide +kernel)
private def rowsD8_row1996 : List ℕ := [
  0x1028201810098603420108905030180cc6c4020104884826180c06030180c666361b100804020102864423120984c28180c06030180c06030188c866341b0e0804020100804020708884624180]
private theorem rowsD8_row1996_checked :
    rowsD8_row1996.length = 1 ∧ rowsSum 1996 rowsD8_row1996 = 66385371 := ddSingle (by decide +kernel)
private def rowsD8_row1997 : List ℕ := [
  0x2030241810098603420108986030180cc6c40201088c4826180c06030180c666361c100804020104864423120984c28180c06030180c06030188c868341b0e080402010080402090c884624180]
private theorem rowsD8_row1997_checked :
    rowsD8_row1997.length = 1 ∧ rowsSum 1997 rowsD8_row1997 = 66779004 := ddSingle (by decide +kernel)
private def rowsD8_row1998 : List ℕ := [
  0x2030241a100a0603620110986030180d07040201088c4826180c06030180c868361c100804020106864624120984c30180c06030180c0603058ccc68341b0e080402010080402090c884624180]
private theorem rowsD8_row1998_checked :
    rowsD8_row1998.length = 1 ∧ rowsSum 1998 rowsD8_row1998 = 67102115 := ddSingle (by decide +kernel)
private def rowsD8_row1999 : List ℕ := [
  0x3038301c110c0603820118986030188d080402010c8c4c28180c06030184c8683620100804020106884624120984c30180c06030180c0603098ccc68361b10080402010080402090c884624180]
private theorem rowsD8_row1999_checked :
    rowsD8_row1999.length = 1 ∧ rowsSum 1999 rowsD8_row1999 = 67423880 := ddSingle (by decide +kernel)
private def rowsD8 : List ℕ :=
    rowsD8_row1993 ++ rowsD8_row1994 ++ rowsD8_row1995 ++
    rowsD8_row1996 ++ rowsD8_row1997 ++ rowsD8_row1998 ++
    rowsD8_row1999
private theorem rowsD8_checked :
    rowsD8.length = 7 ∧ rowsSum 1993 rowsD8 = 464584932 := by
  constructor <;> simp only [rowsD8, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD8_row1993_checked.1, rowsD8_row1993_checked.2,
    rowsD8_row1994_checked.1, rowsD8_row1994_checked.2,
    rowsD8_row1995_checked.1, rowsD8_row1995_checked.2,
    rowsD8_row1996_checked.1, rowsD8_row1996_checked.2,
    rowsD8_row1997_checked.1, rowsD8_row1997_checked.2,
    rowsD8_row1998_checked.1, rowsD8_row1998_checked.2,
    rowsD8_row1999_checked.1, rowsD8_row1999_checked.2]
private def rowsD9_row2000 : List ℕ := [
  0x40403020120c0644020118a06030190d8804020110904c28180c06030184cc683620100804020108884624120984c30180c06030180c0603098ccc68361b100804020100804020d0c884624180]
private theorem rowsD9_row2000_checked :
    rowsD9_row2000.length = 1 ∧ rowsSum 2000 rowsD9_row2000 = 67821210 := ddSingle (by decide +kernel)
private def rowsD9_row2001 : List ℕ := [
  0x2050403020120c0684021120a06030190d8804020910904c28180c06030188cc683620100804020508884624130985030180c06030180c06030d90cc68361b100804020100804020d0c884624180]
private theorem rowsD9_row2001_checked :
    rowsD9_row2001.length = 1 ∧ rowsSum 2001 rowsD9_row2001 = 68213984 := ddSingle (by decide +kernel)
private def rowsD9_row2002 : List ℕ := [
  0x4060483020130c0684021120c06030198d8804021118904c30180c0603018ccc6c382010080402050c884624130985030180c06030180c06030d90cc68361b100804020100804020d0c8c4624180]
private theorem rowsD9_row2002_checked :
    rowsD9_row2002.length = 1 ∧ rowsSum 2002 rowsD9_row2002 = 68573887 := ddSingle (by decide +kernel)
private def rowsD9_row2003 : List ℕ := [
  0x4060483420140c06c4022130c060301a0e0804021118904c30180c0603018cd06c382010080402090c884624130985030180c06030180c06031190cc68361b100804020100804060d0c8c4824180]
private theorem rowsD9_row2003_checked :
    rowsD9_row2003.length = 1 ∧ rowsSum 2003 rowsD9_row2003 = 68976045 := ddSingle (by decide +kernel)
private def rowsD9_row2004 : List ℕ := [
  0x6070603822180c0704023130c060311a100804021918984c30180c06030190d06c3820100804020d0c8c4824130985030180c06030180c06031190cc68361b1008040201008040611108c4824180]
private theorem rowsD9_row2004_checked :
    rowsD9_row2004.length = 1 ∧ rowsSum 2004 rowsD9_row2004 = 69370983 := ddSingle (by decide +kernel)
private def rowsD9_row2005 : List ℕ := [
  0x8080604024180c8804023130c060321b100804022120985030180c06030990d06c4020100804020d108c4824130986030180c06030180c060b1990d068361c1008040201008040a11108c4824180]
private theorem rowsD9_row2005_checked :
    rowsD9_row2005.length = 1 ∧ rowsSum 2005 rowsD9_row2005 = 69671945 := ddSingle (by decide +kernel)
private def rowsD9 : List ℕ :=
    rowsD9_row2000 ++ rowsD9_row2001 ++ rowsD9_row2002 ++
    rowsD9_row2003 ++ rowsD9_row2004 ++ rowsD9_row2005
private theorem rowsD9_checked :
    rowsD9.length = 6 ∧ rowsSum 2000 rowsD9 = 412628054 := by
  constructor <;> simp only [rowsD9, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD9_row2000_checked.1, rowsD9_row2000_checked.2,
    rowsD9_row2001_checked.1, rowsD9_row2001_checked.2,
    rowsD9_row2002_checked.1, rowsD9_row2002_checked.2,
    rowsD9_row2003_checked.1, rowsD9_row2003_checked.2,
    rowsD9_row2004_checked.1, rowsD9_row2004_checked.2,
    rowsD9_row2005_checked.1, rowsD9_row2005_checked.2]
private def rowsD10_row2006 : List ℕ := [
  0x408080604024180c8804024140c060321b100804122120985030180c06031198d06c40201008040211108c4824130986030180c06030180c060b1998d068361c1008040201008040a11108c4824180]
private theorem rowsD10_row2006_checked :
    rowsD10_row2006.length = 1 ∧ rowsSum 2006 rowsD10_row2006 = 70092207 := ddSingle (by decide +kernel)
private def rowsD10_row2007 : List ℕ := [
  0x80c090604026180d0804224180c060331b100804122120986030180c06031198d06c40201008040a11108c4826130a06030180c06030180c06131998d06c361c1008040201008040e11108c4824180]
private theorem rowsD10_row2007_checked :
    rowsD10_row2007.length = 1 ∧ rowsSum 2007 rowsD10_row2007 = 70478169 := ddSingle (by decide +kernel)
private def rowsD10 : List ℕ :=
    rowsD10_row2006 ++ rowsD10_row2007
private theorem rowsD10_checked :
    rowsD10.length = 2 ∧ rowsSum 2006 rowsD10 = 140570376 := by
  constructor <;> simp only [rowsD10, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD10_row2006_checked.1, rowsD10_row2006_checked.2,
    rowsD10_row2007_checked.1, rowsD10_row2007_checked.2]
def rowsD : List ℕ := rowsD1 ++ rowsD2 ++ rowsD3 ++ rowsD4 ++ rowsD5 ++ rowsD6 ++ rowsD7 ++ rowsD8 ++ rowsD9 ++ rowsD10
theorem rowsD_length : rowsD.length = 65 := by
  simp only [rowsD, List.length_append, Nat.reduceAdd,
    rowsD1_checked.1, rowsD2_checked.1, rowsD3_checked.1, rowsD4_checked.1,
    rowsD5_checked.1, rowsD6_checked.1, rowsD7_checked.1, rowsD8_checked.1,
    rowsD9_checked.1, rowsD10_checked.1]
theorem rowsD_sum : rowsSum 1943 rowsD = 3844665783 := by
  simp only [rowsD, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD1_checked.1, rowsD2_checked.1, rowsD3_checked.1, rowsD4_checked.1,
    rowsD5_checked.1, rowsD6_checked.1, rowsD7_checked.1, rowsD8_checked.1,
    rowsD9_checked.1, rowsD1_checked.2, rowsD2_checked.2, rowsD3_checked.2,
    rowsD4_checked.2, rowsD5_checked.2, rowsD6_checked.2, rowsD7_checked.2,
    rowsD8_checked.2, rowsD9_checked.2, rowsD10_checked.2]
end K1_13_2_3_4
end
section
namespace K1_14_4
open K1_14 Finset
def gradeWidth (k B W j : ℕ) : ℕ :=
  min (B + 1) ((W + j) / k + 1) - j
end K1_14_4
end

end Merged6967_Fast063

section Merged6967_Fast065
set_option Elab.async false

set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators Polynomial
abbrev SeedPoly := MvPolynomial (Fin 2) L
abbrev SeedField := FractionRing SeedPoly
abbrev Source := Polynomial (Polynomial (Polynomial SeedPoly))
abbrev RawSource := Polynomial (Polynomial (Polynomial SeedField))
def otherBlock (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0
structure PoleData (h : ℕ) where
  block : Fin 2 → (Polynomial L)
  offset : Fin 2 → (Polynomial L)
  constant : Fin 2 → (Polynomial L)
  slope : Fin 2 → (Polynomial L)
  monic : ∀ i, (block i).Monic
  degree : ∀ i, (block i).natDegree = h
  coprime : IsCoprime (block 0) (block 1)
  determinant : ∀ i, IsCoprime (offset i * constant i) (block i)
def poleProduct {h} (D : PoleData h) : (Polynomial L) := D.block 0 * D.block 1
structure CRTLift {h : ℕ} (D : PoleData h) where
  denominator : Fin 2 → (Polynomial L)
  numerator : Fin 2 → Polynomial (Polynomial L)
  denominator_ne_zero : ∀ i, denominator i ≠ 0
  numerator_degree : ∀ i, (numerator i).degree < (2 * h : ℕ)
  other_dvd : ∀ i, (D.block (otherBlock i)).map (Polynomial.C (R := L)) ∣ numerator i
  congruence : ∀ i, (D.block i).map (Polynomial.C (R := L)) ∣
      ((D.constant i).map (Polynomial.C (R := L)) +
        (@Polynomial.C (Polynomial L) _) (Polynomial.X (R := L)) * (D.slope i).map (Polynomial.C (R := L))) * numerator i +
        (@Polynomial.C (Polynomial L) _) (denominator i * Polynomial.X) * (D.offset i).map (Polynomial.C (R := L))
  regular : ∀ i z, IsCoprime (D.constant i + C z * D.slope i) (D.block i) →
    (denominator i).eval z ≠ 0
def seedInField (i : Fin 2) : (Polynomial L) →ₐ[L] SeedField :=
  Polynomial.aeval (algebraMap SeedPoly SeedField (MvPolynomial.X i))
def crtPolynomial {h} {D : PoleData h} (Crt : CRTLift D) : (Polynomial SeedField) :=
  ∑ i, (seedInField i (Crt.denominator i))⁻¹ • (Crt.numerator i).map (seedInField i)
def jetConstant {R : Type*} [CommSemiring R] :
    R →+* Polynomial (Polynomial R) :=
  C.comp C
private def jetSubstitute {R S A : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring A] [Algebra R S] [Algebra R A]
    (base : S →ₐ[R] A) (y v : A) : Polynomial (Polynomial S) →ₐ[R] A :=
  eval₂AlgHom (eval₂AlgHom base y (fun _ => Commute.all _ _))
    v (fun _ => Commute.all _ _)
def genericCoefficients : (Polynomial SeedPoly) →ₐ[L] (Polynomial SeedField) :=
  Polynomial.mapAlgHom (IsScalarTower.toAlgHom L SeedPoly SeedField)
def rawBlock {h} (D : PoleData h) : (Polynomial SeedField) :=
  (poleProduct D).map (algebraMap L SeedField)
def forward {h} {D : PoleData h} (Crt : CRTLift D) : Source →ₐ[L] RawSource :=
  let H := rawBlock D
  let lift := crtPolynomial Crt
  let c : (Polynomial SeedField) →+* RawSource := jetConstant
  let rawOrd : RawSource := (@Polynomial.C (Polynomial (Polynomial SeedField)) _)
    (Polynomial.X (R := Polynomial SeedField))
  let rawDeriv : RawSource := Polynomial.X
  jetSubstitute (R := L) (S := (Polynomial SeedPoly)) (A := RawSource)
    ((IsScalarTower.toAlgHom L (Polynomial SeedField) RawSource).comp genericCoefficients)
    (c H * rawOrd + c lift) (c H * rawDeriv + c H.derivative * rawOrd + c lift.derivative)
def atPhysical (x r : L) : Source →ₐ[L] Source :=
  let c : (Polynomial SeedPoly) →+* Source := jetConstant
  let base : (Polynomial SeedPoly) →ₐ[L] (Polynomial SeedPoly) :=
    eval₂AlgHom (IsScalarTower.toAlgHom L SeedPoly (Polynomial SeedPoly))
      (Polynomial.X (R := SeedPoly) + (@Polynomial.C SeedPoly _) (MvPolynomial.C x))
      (fun _ => Commute.all _ _)
  let η : Source := (@Polynomial.C (Polynomial (Polynomial SeedPoly)) _)
    (Polynomial.X (R := Polynomial SeedPoly))
  let deriv : Source := Polynomial.X
  jetSubstitute (R := L) (S := (Polynomial SeedPoly)) (A := Source)
    ((IsScalarTower.toAlgHom L (Polynomial SeedPoly) Source).comp base)
    (c ((@Polynomial.C SeedPoly _) (MvPolynomial.C r)) + c (Polynomial.X (R := SeedPoly)) * deriv + η) deriv
def coeffAt (P : Source) (j i a : ℕ) (e : Fin 2 →₀ ℕ) : L :=
  (((P.coeff j).coeff i).coeff a).coeff e
def seedWeight (e : Fin 2 →₀ ℕ) : ℕ := e.sum fun _ n => n
def trueEligible (h : ℕ) (s : Shape) (W j i a : ℕ) (e : Fin 2 →₀ ℕ) : Prop :=
  i + j ≤ s.B ∧ j ≤ s.J ∧ seedWeight e ≤ s.U ∧
    a + (i+j)*(131071+h) ≤ W + (s.B+s.J)*(2*h) + j
def ambient (h : ℕ) (s : Shape) (W : ℕ) : Submodule L Source where
  carrier := {P | ∀ j i a e, ¬ trueEligible h s W j i a e → coeffAt P j i a e = 0}
  zero_mem' := by simp [coeffAt]
  add_mem' := by
    intro P Q hP hQ j i a e he
    have hp := hP j i a e he
    have hq := hQ j i a e he
    unfold coeffAt at hp hq ⊢
    simp [hp, hq]
  smul_mem' := by
    intro b P hP j i a e he
    have hp := hP j i a e he
    unfold coeffAt at hp ⊢
    simp [Polynomial.coeff_smul, hp]
def nodeL (i : I) : L := algebraMap K L (node i)
def physical (word : I → L) (s : Shape) : Submodule L Source where
  carrier := {P | ∀ i a b j e, a + 2*b < s.m →
    coeffAt (atPhysical (nodeL i) (word i) P) j b a e = 0}
  zero_mem' := by simp [coeffAt]
  add_mem' := by
    intro P Q hP hQ i a b j e he
    have hp := hP i a b j e he
    have hq := hQ i a b j e he
    unfold coeffAt at hp hq ⊢
    simp [hp, hq]
  smul_mem' := by
    intro b P hP i a k j e he
    have hp := hP i a k j e he
    unfold coeffAt at hp ⊢
    simp [Polynomial.coeff_smul, hp]
def poleSpace {h} {D : PoleData h} (Crt : CRTLift D) (s : Shape) : Submodule L Source where
  carrier := {P | (jetConstant ((rawBlock D) ^ (s.B+s.J)) : RawSource) ∣ forward Crt P}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ
    change _ ∣ forward Crt (P + Q)
    rw [map_add]
    exact dvd_add hP hQ
  smul_mem' := by
    intro b P hP
    change _ ∣ forward Crt (b • P)
    rw [map_smul, Algebra.smul_def]
    exact dvd_mul_of_dvd_right hP _
def contacted (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) : Submodule L Source :=
  ambient h s W ⊓ physical word s
def complete {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) : Submodule L Source :=
  contacted h word s W ⊓ poleSpace Crt s
def centerEval : Source →ₐ[L] Jet :=
  let ξ := algebraMap (Polynomial L) FX (Polynomial.X (R := L))
  let base : (Polynomial SeedPoly) →ₐ[L] Seeds :=
    eval₂AlgHom (MvPolynomial.mapAlgHom (Algebra.ofId L FX))
      (MvPolynomial.C ξ) (fun _ => Commute.all _ _)
  Polynomial.mapAlgHom (Polynomial.mapAlgHom base)
def evaluated {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L) : Banks :=
  fun s W => Submodule.span FX (centerEval '' (complete Crt word s W : Set Source))
def rawWidthCond (h : ℕ) (s : Shape) (W : ℕ) : Prop :=
  ∀ q ≤ s.B, ∀ j ≤ min q s.J, q*(131071-h) ≤ W+1+j
def rawVolumeAt (h : ℕ) (s : Shape) (W : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => W+1+j - q*(131071-h))
def poleCredit (h : ℕ) (s : Shape) : ℕ :=
  triangle s.U * (2*h) * shapeSum s (fun q _ => s.B+s.J-q)
def physicalDebit (s : Shape) : ℕ :=
  triangle s.U * 262144 * shapeSum s (fun q i => s.m + min q s.J - (q + 2*i))
def seedPair (z : K) : Fin 2 → L :=
  ![algebraMap K L z, (algebraMap K L z)^p]
def residueAt {h} (D : PoleData h) (i : Fin 2) (z : L) : (Polynomial L) :=
  D.constant i + (@Polynomial.C L _) z * D.slope i
def MarkResidues {h} (D : PoleData h) (z : K) (S : (Polynomial K)) : Prop :=
  ∀ i, IsCoprime (residueAt D i (seedPair z i)) (D.block i) ∧
    D.block i ∣ residueAt D i (seedPair z i) * liftPoly S +
      (@Polynomial.C L _) (seedPair z i) * D.offset i
end
end K1_14_1
end
section
namespace K1_14_1
noncomputable section
open K1 K1_14 Polynomial
open scoped Polynomial
theorem complete_mono {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s s' : Shape} (hm : s.m = s'.m) (hB : s.B = s'.B) (hJ : s.J = s'.J)
    (hU : s.U ≤ s'.U) {W W' : ℕ} (hW : W ≤ W') :
    complete Crt word s W ≤ complete Crt word s' W' := by
  intro P hP
  rcases SetLike.mem_coe.mp hP with ⟨⟨ha, hp⟩, hc⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j i a e hn
    apply ha j i a e
    intro ⟨hb, hj, hu, hw⟩
    apply hn
    exact ⟨hB ▸ hb, hJ ▸ hj, hu.trans hU, by
      rw [← hB, ← hJ]
      omega⟩
  · intro i a b j e he
    exact hp i a b j e (hm ▸ he)
  · change (jetConstant ((rawBlock D) ^ (s'.B+s'.J)) : RawSource) ∣ forward Crt P
    rw [← hB, ← hJ]
    exact hc
theorem evaluated_mono {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s s' : Shape} (hm : s.m = s'.m) (hB : s.B = s'.B) (hJ : s.J = s'.J)
    (hU : s.U ≤ s'.U) {W W' : ℕ} (hW : W ≤ W') :
    evaluated Crt word s W ≤ evaluated Crt word s' W' :=
  Submodule.span_mono (Set.image_mono (complete_mono Crt word hm hB hJ hU hW))
def centerCoeff (j i : ℕ) (e : Fin 2 →₀ ℕ) : Jet →ₗ[FX] FX where
  toFun P := ((P.coeff j).coeff i).coeff e
  map_add' P Q := by simp
  map_smul' b P := by simp [Polynomial.coeff_smul]
theorem centerCoeff_eval (P : Source) (j i : ℕ) (e : Fin 2 →₀ ℕ)
    (hz : ∀ a, coeffAt P j i a e = 0) :
    centerCoeff j i e (centerEval P) = 0 := by
  let ξ := algebraMap (Polynomial L) FX (Polynomial.X (R := L))
  let g := (P.coeff j).coeff i
  change (((centerEval P).coeff j).coeff i).coeff e = 0
  simp only [centerEval, Polynomial.coeff_mapAlgHom_apply]
  change (g.eval₂ (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C ξ)).coeff e = 0
  rw [Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro a _
  have he : (g.coeff a).coeff e = 0 := hz a
  rw [← map_pow, mul_comm, MvPolynomial.coeff_C_mul]
  change ξ^a * (MvPolynomial.map (algebraMap L FX) (g.coeff a)).coeff e = 0
  rw [MvPolynomial.coeff_map, he, map_zero, mul_zero]
private theorem centerCoeff_zero {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s W P} (hP : P ∈ evaluated Crt word s W)
    (j i : ℕ) (e : Fin 2 →₀ ℕ) (hf : ¬ (i+j ≤ s.B ∧ j ≤ s.J ∧ seedWeight e ≤ s.U)) :
    centerCoeff j i e P = 0 := by
  have hsub : evaluated Crt word s W ≤ LinearMap.ker (centerCoeff j i e) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨Q, hQ, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply centerCoeff_eval
      intro a
      exact hQ.1.1 j i a e (fun hh => hf ⟨hh.1, hh.2.1, hh.2.2.1⟩))
  exact LinearMap.mem_ker.mp (hsub hP)
theorem evaluated_shape {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s W P} (hP : P ∈ evaluated Crt word s W) (j i : ℕ)
    (hne : ((P.coeff j).coeff i) ≠ 0) :
    i+j ≤ s.B ∧ j ≤ s.J ∧ ((P.coeff j).coeff i).totalDegree ≤ s.U := by
  classical
  let g := (P.coeff j).coeff i
  have he (e) (hes : e ∈ g.support) :
      i+j ≤ s.B ∧ j ≤ s.J ∧ seedWeight e ≤ s.U := by
    by_contra hbad
    exact (MvPolynomial.mem_support_iff.mp hes) (centerCoeff_zero Crt word hP j i e hbad)
  obtain ⟨e, heS⟩ := Finset.nonempty_iff_ne_empty.mpr (by simpa [g] using hne :
    g.support ≠ ∅)
  refine ⟨(he e heS).1, (he e heS).2.1, ?_⟩
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  exact fun a ha => (he a ha).2.2
end
end K1_14_1
end
section
namespace K1_14_1
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators
end
end K1_14_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 16
namespace K1_14_1_2
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators
def evalThree {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v : R) : Polynomial (Polynomial (Polynomial A)) →+* R :=
  eval₂RingHom (eval₂RingHom (eval₂RingHom f x) y) v
def composed (t : Fin 2 → L) (S : (Polynomial L)) : Source →+* (Polynomial L) :=
  evalThree (C.comp (MvPolynomial.eval t)) Polynomial.X S S.derivative
theorem evalThree_ext {A R : Type*} [CommSemiring A] [CommSemiring R]
    {f g : Polynomial (Polynomial (Polynomial A)) →+* R}
    (hc : ∀ a : A, f (C (C (C a))) = g (C (C (C a))))
    (hx : f (C (C Polynomial.X)) = g (C (C Polynomial.X)))
    (hy : f (C Polynomial.X) = g (C Polynomial.X))
    (hv : f Polynomial.X = g Polynomial.X) : f = g := by
  apply Polynomial.ringHom_ext _ hv
  have hbase : (f.comp C).comp C = (g.comp C).comp C :=
    Polynomial.ringHom_ext hc hx
  have hinner : f.comp C = g.comp C :=
    Polynomial.ringHom_ext (DFunLike.congr_fun hbase) hy
  exact DFunLike.congr_fun hinner
@[simp] theorem evalThree_const {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v : R) (a : A) :
    evalThree f x y v (C (C (C a))) = f a := by
  simp [evalThree]
@[simp] theorem evalThree_X {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v : R) :
    evalThree f x y v (C (C Polynomial.X)) = x := by
  simp [evalThree]
@[simp] theorem evalThree_Y {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v : R) :
    evalThree f x y v (C Polynomial.X) = y := by
  simp [evalThree]
@[simp] theorem evalThree_V {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v : R) :
    evalThree f x y v Polynomial.X = v := by
  simp [evalThree]
theorem evalThree_sum {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v : R) (P : Polynomial (Polynomial (Polynomial A))) :
    evalThree f x y v P =
      ∑ j ∈ P.support, (∑ i ∈ (P.coeff j).support, (∑ a ∈ ((P.coeff j).coeff i).support,
        f (((P.coeff j).coeff i).coeff a) * x ^ a) * y ^ i) * v ^ j := by
  simp only [evalThree, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum]
theorem composed_degree {h : ℕ} {s : Shape} {W : ℕ} {P : Source}
    (hP : P ∈ ambient h s W) (t : Fin 2 → L) (S : (Polynomial L))
    (hd : S.natDegree ≤ 131071+h) :
    (composed t S P).natDegree ≤ W+(s.B+s.J)*(2*h) := by
  let d := 131071+h
  change S.natDegree ≤ d at hd
  have hd' : S.derivative.natDegree ≤ d-1 :=
    (natDegree_derivative_le S).trans (Nat.sub_le_sub_right hd _)
  have hpred : d-1+1 = d := by dsimp [d]; omega
  rw [composed, evalThree_sum]
  apply natDegree_sum_le_of_forall_le
  intro j _
  rw [Finset.sum_mul]
  apply natDegree_sum_le_of_forall_le
  intro i _
  rw [Finset.sum_mul, Finset.sum_mul]
  apply natDegree_sum_le_of_forall_le
  intro a ha
  have hne : ((P.coeff j).coeff i).coeff a ≠ 0 :=
    mem_support_iff.mp ha
  have hw : a+(i+j)*d ≤ W+(s.B+s.J)*(2*h)+j := by
    by_contra hn
    apply hne
    ext e
    exact hP j i a e (fun he => hn he.2.2.2)
  refine (natDegree_mul_le_of_le (natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (by simp : (C _ : (Polynomial L)).natDegree ≤ 0) (by simp : (Polynomial.X ^ a : (Polynomial L)).natDegree ≤ a))
    (natDegree_pow_le_of_le i hd)) (natDegree_pow_le_of_le j hd')).trans ?_
  have hj : j*(d-1)+j = j*d := by rw [← Nat.mul_succ, Nat.succ_eq_add_one, hpred]
  rw [Nat.add_mul] at hw
  omega
theorem composed_center (z : K) (S : (Polynomial K)) (P : Source) :
    jetAt (centerEval P) z S = algebraMap (Polynomial L) FX (composed (seedPair z) (liftPoly S) P) := by
  let ev := eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
  let f := algebraMap (Polynomial L) FX
  change (ev.comp centerEval.toRingHom) P = (f.comp (composed (seedPair z) (liftPoly S))) P
  apply DFunLike.congr_fun
  apply evalThree_ext
  · intro g
    have he :
        (graphEval z).comp (MvPolynomial.map (algebraMap L FX)) =
          (f.comp C).comp (MvPolynomial.eval (seedPair z)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [graphEval, RingHom.comp_apply, f]
        rfl
      · intro i
        fin_cases i <;> simp [graphEval, seedPair, seedEmbedding, f]
    simpa [RingHom.comp_apply, centerEval, ev, composed] using DFunLike.congr_fun he g
  · simp [RingHom.comp_apply, centerEval, ev, composed, graphEval, f]
  · simp [RingHom.comp_apply, centerEval, ev, composed, f, atX]
  · simp [RingHom.comp_apply, centerEval, ev, composed, f, atX, liftPoly, derivative_map]
theorem span_vanish {h : ℕ} {D : PoleData h} {Crt : CRTLift D}
    {word : I → L} {s : Shape} {W : ℕ} (z : K) (S : (Polynomial K))
    (hz : ∀ P ∈ complete Crt word s W, composed (seedPair z) (liftPoly S) P = 0)
    {P : Jet} (hP : P ∈ evaluated Crt word s W) : jetAt P z S = 0 := by
  let ev := eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
  change P ∈ Submodule.span FX _ at hP
  change ev P = 0
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨Q, hQ, rfl⟩ := hP
    change jetAt (centerEval Q) z S = 0
    rw [composed_center, hz Q hQ, map_zero]
  | zero => exact map_zero ev
  | add A B _ _ hA hB => rw [map_add, hA, hB, add_zero]
  | smul r A _ hA => rw [Algebra.smul_def, map_mul, hA, mul_zero]
private theorem physical_substitute (t : Fin 2 → L) (S : (Polynomial L)) (x r : L) :
    (evalThree (C.comp (MvPolynomial.eval t)) (Polynomial.X-C x)
      (S-C r-(Polynomial.X-C x)*S.derivative) S.derivative).comp (atPhysical x r).toRingHom =
      composed t S := by
  let δ : (Polynomial L) := Polynomial.X-C x
  let η : (Polynomial L) := S-C r-δ*S.derivative
  let E := evalThree (C.comp (MvPolynomial.eval t)) δ η S.derivative
  let c : (Polynomial SeedPoly) →+* Source := jetConstant
  let u : (Polynomial SeedPoly) := Polynomial.X + C (MvPolynomial.C x)
  let b : (Polynomial SeedPoly) →+* Source := c.comp (eval₂RingHom C u)
  let y : Source := c (C (MvPolynomial.C r)) + c Polynomial.X * Polynomial.X + C Polynomial.X
  let _ : CommSemiring Source := inferInstanceAs (CommSemiring (Polynomial (Polynomial (Polynomial SeedPoly))))
  have hform : (atPhysical x r).toRingHom = eval₂RingHom (eval₂RingHom b y) Polynomial.X := rfl
  change E.comp (atPhysical x r).toRingHom = composed t S
  rw [hform]
  apply evalThree_ext
  · intro g
    simp [E, composed, b, c, jetConstant, RingHom.comp_apply]
  · simp [E, composed, b, c, u, δ, jetConstant, RingHom.comp_apply]
  · simp [E, composed, y, c, η, jetConstant, RingHom.comp_apply]
  · simp [E, composed, RingHom.comp_apply]
private theorem remainder_order_two (S : (Polynomial L)) (x r : L) (hx : S.eval x = r) :
    (Polynomial.X-C x)^2 ∣ S-C r-(Polynomial.X-C x)*S.derivative := by
  rw [X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero]
  intro k hk
  have he : k = 0 ∨ k = 1 := by omega
  rcases he with rfl | rfl
  · simp [hx]
  · simp [hasseDeriv_one, derivative_sub, derivative_mul]
theorem composed_contact {word : I → L} {s : Shape} {P : Source}
    (hP : P ∈ physical word s) (t : Fin 2 → L) (S : (Polynomial L))
    (k : I) (hk : S.eval (nodeL k) = word k) :
    (Polynomial.X-C (nodeL k)) ^ s.m ∣ composed t S P := by
  let x := nodeL k
  let r := word k
  let δ : (Polynomial L) := Polynomial.X-C x
  let η : (Polynomial L) := S-C r-δ*S.derivative
  let E := evalThree (C.comp (MvPolynomial.eval t)) δ η S.derivative
  let Q := atPhysical x r P
  change δ ^ s.m ∣ composed t S P
  have he : E Q = composed t S P :=
    DFunLike.congr_fun (physical_substitute t S x r) P
  rw [← he]
  dsimp only [E]
  rw [evalThree_sum]
  apply Finset.dvd_sum
  intro j _
  apply Dvd.dvd.mul_right
  apply Finset.dvd_sum
  intro b _
  rw [Finset.sum_mul]
  apply Finset.dvd_sum
  intro a ha
  have hw : s.m ≤ a+2*b := by
    by_contra hn
    apply mem_support_iff.mp ha
    ext e
    exact hP k a b j e (by omega)
  have hη : δ ^ 2 ∣ η := remainder_order_two S x r hk
  have hpow : δ ^ (a+2*b) ∣ δ ^ a * η ^ b := by
    rw [pow_add, pow_mul]
    exact mul_dvd_mul_left _ (pow_dvd_pow_of_dvd hη b)
  exact (pow_dvd_pow _ hw).trans (by simpa only [mul_assoc] using hpow.mul_left _)
def markedLift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (t : Fin 2 → L) : (Polynomial L) :=
  ∑ i, C (((Crt.denominator i).eval (t i))⁻¹) * (Crt.numerator i).map (evalRingHom (t i))
private theorem map_eval_C (t : L) (P : (Polynomial L)) :
    (P.map (C : L →+* (Polynomial L))).map (evalRingHom t) = P := by
  rw [map_map]
  have he : (evalRingHom t).comp (C : L →+* (Polynomial L)) = RingHom.id L := by ext a; simp
  simp [he]
theorem markedLift_residue {h : ℕ} {D : PoleData h} (Crt : CRTLift D)
    {z : K} {S : (Polynomial K)} (hm : MarkResidues D z S) :
    poleProduct D ∣ liftPoly S - markedLift Crt (seedPair z) := by
  let t := seedPair z
  let d (i : Fin 2) := (Crt.denominator i).eval (t i)
  let N (i : Fin 2) := (Crt.numerator i).map (evalRingHom (t i))
  let U (i : Fin 2) := C (d i)⁻¹ * N i
  have hd (i : Fin 2) : d i ≠ 0 := Crt.regular i (t i) (hm i).1
  have hc (i : Fin 2) : D.block i ∣ residueAt D i (t i) * U i + C (t i) * D.offset i := by
    have h0 := map_dvd (mapRingHom (evalRingHom (t i))) (Crt.congruence i)
    have h1 : D.block i ∣ residueAt D i (t i) * N i + C (d i * t i) * D.offset i := by
      simpa [residueAt, N, d, map_eval_C] using h0
    have he : (C (d i)⁻¹ : (Polynomial L)) * C (d i * t i) = C (t i) := by
      rw [← map_mul, ← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]
    simpa only [mul_add, ← mul_assoc, mul_comm (C (d i)⁻¹) (residueAt D i (t i)), he, U] using
      h1.mul_left (C (d i)⁻¹)
  have ho (i : Fin 2) : D.block (otherBlock i) ∣ U i := by
    apply Dvd.dvd.mul_left
    simpa [N, map_eval_C] using map_dvd (mapRingHom (evalRingHom (t i))) (Crt.other_dvd i)
  have hsum (i : Fin 2) : markedLift Crt t = U i + U (otherBlock i) := by
    rw [markedLift, Fin.sum_univ_two]
    fin_cases i
    · rfl
    · exact add_comm _ _
  have hblock (i : Fin 2) : D.block i ∣ liftPoly S - markedLift Crt t := by
    apply (hm i).1.symm.dvd_of_dvd_mul_left
    have hoi : D.block i ∣ U (otherBlock i) := by
      have hother : otherBlock (otherBlock i) = i := by fin_cases i <;> decide
      simpa only [hother] using ho (otherBlock i)
    have hmark : D.block i ∣ residueAt D i (t i) * markedLift Crt t + C (t i) * D.offset i := by
      rw [hsum, mul_add, add_right_comm]
      exact dvd_add (hc i) (hoi.mul_left _)
    have hactual : D.block i ∣ residueAt D i (t i) * liftPoly S + C (t i) * D.offset i :=
      (hm i).2
    change D.block i ∣ residueAt D i (t i) * (liftPoly S - markedLift Crt t)
    simpa only [mul_sub, add_sub_add_right_eq_sub] using dvd_sub hactual hmark
  exact D.coprime.mul_dvd (hblock 0) (hblock 1)
def regularSeeds (t : Fin 2 → L) : Submonoid SeedPoly where
  carrier := {a | MvPolynomial.eval t a ≠ 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change MvPolynomial.eval t (a*b) ≠ 0
    exact (map_mul (MvPolynomial.eval t) a b).symm ▸ mul_ne_zero ha hb
abbrev RegularRing (t : Fin 2 → L) := Localization (regularSeeds t)
def specialize (t : Fin 2 → L) : RegularRing t →+* L :=
  IsLocalization.lift (g := MvPolynomial.eval t)
    (fun a : regularSeeds t => isUnit_iff_ne_zero.mpr a.property)
def includeGeneric (t : Fin 2 → L) : RegularRing t →+* SeedField :=
  IsLocalization.lift (g := algebraMap SeedPoly SeedField)
    (fun a : regularSeeds t => isUnit_iff_ne_zero.mpr
      (fun he => a.property (by
        have hzero := (IsFractionRing.injective SeedPoly SeedField) (he.trans (map_zero _).symm)
        simp [hzero])))
theorem includeGeneric_injective (t : Fin 2 → L) :
    Function.Injective (includeGeneric t) := by
  unfold includeGeneric
  apply (IsLocalization.lift_injective_iff _).mpr
  intro a b
  have h : regularSeeds t ≤ nonZeroDivisors SeedPoly := fun x hx =>
    mem_nonZeroDivisors_iff_ne_zero.mpr (fun he => hx (by simp [he]))
  rw [(IsLocalization.injective (RegularRing t) h).eq_iff,
    (IsFractionRing.injective SeedPoly SeedField).eq_iff]
private def seedPolynomial (i : Fin 2) : (Polynomial L) →+* SeedPoly :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X i)
private theorem map_seedPolynomial (i : Fin 2) :
    (algebraMap SeedPoly SeedField).comp (seedPolynomial i) = (seedInField i).toRingHom := by
  apply Polynomial.ringHom_ext <;>
    simp [seedPolynomial, seedInField, aeval_def, RingHom.comp_apply, MvPolynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply L SeedPoly SeedField]
private theorem eval_seedPolynomial (t : Fin 2 → L) (i : Fin 2) :
    (MvPolynomial.eval t).comp (seedPolynomial i) = evalRingHom (t i) := by
  apply Polynomial.ringHom_ext <;> simp [seedPolynomial, RingHom.comp_apply]
def localLift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (t : Fin 2 → L)
    (hd : ∀ i, (Crt.denominator i).eval (t i) ≠ 0) : (Polynomial (RegularRing t)) :=
  ∑ i, C (IsLocalization.mk' (RegularRing t) 1
      (⟨seedPolynomial i (Crt.denominator i), by
        change (MvPolynomial.eval t).comp (seedPolynomial i) (Crt.denominator i) ≠ 0
        rw [eval_seedPolynomial]
        exact hd i⟩ : regularSeeds t)) *
    (Crt.numerator i).map ((algebraMap SeedPoly (RegularRing t)).comp (seedPolynomial i))
theorem map_localLift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (t : Fin 2 → L)
    (hd : ∀ i, (Crt.denominator i).eval (t i) ≠ 0) :
    (localLift Crt t hd).map (includeGeneric t) = crtPolynomial Crt := by
  rw [localLift, crtPolynomial, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : algebraMap SeedPoly SeedField (seedPolynomial i (Crt.denominator i)) =
      seedInField i (Crt.denominator i) :=
    RingHom.congr_fun (map_seedPolynomial i) (Crt.denominator i)
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, includeGeneric,
    IsLocalization.lift_mk', IsLocalization.lift_comp, ← RingHom.comp_assoc, map_seedPolynomial,
    smul_eq_C_mul, map_one, Units.val_inv_eq_inv_val, one_mul,
    IsUnit.liftRight_apply, IsUnit.unit_spec, MonoidHom.domRestrict_apply]
  change C ((algebraMap SeedPoly SeedField (seedPolynomial i (Crt.denominator i)))⁻¹) * _ = _
  rw [he]
  rfl
theorem specialize_localLift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (t : Fin 2 → L)
    (hd : ∀ i, (Crt.denominator i).eval (t i) ≠ 0) :
    (localLift Crt t hd).map (specialize t) = markedLift Crt t := by
  rw [localLift, markedLift, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : MvPolynomial.eval t (seedPolynomial i (Crt.denominator i)) =
      (Crt.denominator i).eval (t i) :=
    RingHom.congr_fun (eval_seedPolynomial t i) (Crt.denominator i)
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, specialize,
    IsLocalization.lift_mk', IsLocalization.lift_comp, ← RingHom.comp_assoc, eval_seedPolynomial,
    map_one, Units.val_inv_eq_inv_val, one_mul, IsUnit.liftRight_apply, IsUnit.unit_spec,
    MonoidHom.domRestrict_apply]
  change C ((MvPolynomial.eval t (seedPolynomial i (Crt.denominator i)))⁻¹) * _ = _
  rw [he]
private def rawEval (T : (Polynomial SeedField)) : RawSource →+* (Polynomial SeedField) :=
  eval₂RingHom (eval₂RingHom (RingHom.id _) T) T.derivative
private theorem forward_eval {h : ℕ} {D : PoleData h} (Crt : CRTLift D)
    (T : (Polynomial SeedField)) :
    (rawEval T).comp (forward Crt).toRingHom =
      evalThree (C.comp (algebraMap SeedPoly SeedField)) Polynomial.X
        (rawBlock D*T + crtPolynomial Crt)
        (rawBlock D*T.derivative + (rawBlock D).derivative*T + (crtPolynomial Crt).derivative) := by
  let c : (Polynomial SeedField) →+* RawSource := jetConstant
  let H := rawBlock D
  let lift := crtPolynomial Crt
  let o : RawSource := C (Polynomial.X (R := Polynomial SeedField))
  let v : RawSource := Polynomial.X
  let b : (Polynomial SeedPoly) →+* RawSource := c.comp (mapRingHom (algebraMap SeedPoly SeedField))
  let _ : CommSemiring RawSource := inferInstanceAs (CommSemiring (Polynomial (Polynomial (Polynomial SeedField))))
  have hf : (forward Crt).toRingHom =
      eval₂RingHom (eval₂RingHom b (c H*o+c lift)) (c H*v+c H.derivative*o+c lift.derivative) := rfl
  rw [hf]
  apply evalThree_ext <;> simp [rawEval, c, jetConstant, H, lift, o, v, b, RingHom.comp_apply]
private theorem evalThree_map {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (jetY jetV : (Polynomial A)) :
    (mapRingHom g).comp (evalThree (C.comp f) Polynomial.X jetY jetV) =
      evalThree (C.comp (g.comp f)) Polynomial.X (jetY.map g) (jetV.map g) := by
  apply evalThree_ext <;> simp [RingHom.comp_apply]
theorem specialized_poles {h : ℕ} {D : PoleData h} (Crt : CRTLift D)
    {z : K} {S : (Polynomial K)} (hm : MarkResidues D z S) {s : Shape} {P : Source}
    (hP : P ∈ poleSpace Crt s) :
    poleProduct D ^ (s.B+s.J) ∣ composed (seedPair z) (liftPoly S) P := by
  let t := seedPair z
  let A := RegularRing t
  let f := algebraMap SeedPoly A
  let e := specialize t
  let g := includeGeneric t
  let j : L →+* A := f.comp MvPolynomial.C
  have hef : e.comp f = MvPolynomial.eval t := IsLocalization.lift_comp _
  have hgf : g.comp f = algebraMap SeedPoly SeedField := IsLocalization.lift_comp _
  have hej : e.comp j = RingHom.id L := by
    change (e.comp f).comp MvPolynomial.C = _
    rw [hef]
    ext a
    simp
  have hgj : g.comp j = algebraMap L SeedField := by
    change (g.comp f).comp MvPolynomial.C = _
    rw [hgf]
    ext a
    simp [IsScalarTower.algebraMap_apply L SeedPoly SeedField, MvPolynomial.algebraMap_eq]
  have hd (i : Fin 2) : (Crt.denominator i).eval (t i) ≠ 0 := Crt.regular i _ (hm i).1
  obtain ⟨T, hT⟩ := markedLift_residue Crt hm
  have hS : poleProduct D*T + markedLift Crt t = liftPoly S := by
    rw [← hT]
    abel
  let H := (poleProduct D).map j
  let U := T.map j
  let lift := localLift Crt t hd
  let jetY := H*U + lift
  let Q := evalThree (C.comp f) Polynomial.X jetY jetY.derivative P
  let F := H^(s.B+s.J)
  have hFm : F.Monic := ((D.monic 0).mul (D.monic 1) |>.map j).pow _
  have egH : H.map g = rawBlock D := by rw [map_map, hgj]; rfl
  have eeH : H.map e = poleProduct D := by rw [map_map, hej, map_id]
  have eeU : U.map e = T := by rw [map_map, hej, map_id]
  have egY : jetY.map g = rawBlock D * U.map g + crtPolynomial Crt := by
    rw [Polynomial.map_add, Polynomial.map_mul, egH, map_localLift]
  have eeY : jetY.map e = liftPoly S := by
    rw [Polynomial.map_add, Polynomial.map_mul, eeH, eeU, specialize_localLift, hS]
  have hgQ :
      Q.map g = rawEval (U.map g) (forward Crt P) := by
    change ((mapRingHom g).comp (evalThree (C.comp f) Polynomial.X jetY jetY.derivative)) P =
      ((rawEval (U.map g)).comp (forward Crt).toRingHom) P
    rw [evalThree_map, hgf, ← derivative_map, egY, forward_eval, derivative_add, derivative_mul]
    rw [add_comm (derivative (rawBlock D) * map g U)]
  have hgF : F.map g = rawBlock D ^ (s.B+s.J) := by rw [Polynomial.map_pow, egH]
  have hdiv : F.map g ∣ Q.map g := by
    rw [hgF, hgQ]
    have h := map_dvd (rawEval (U.map g)) hP
    simpa [rawEval, jetConstant, eval₂_pow] using h
  have hlocal : F ∣ Q := by
    apply (modByMonic_eq_zero_iff_dvd hFm).mp
    apply map_injective g (includeGeneric_injective t)
    rw [map_modByMonic g hFm, Polynomial.map_zero]
    exact (modByMonic_eq_zero_iff_dvd (hFm.map g)).mpr hdiv
  have heQ : Q.map e = composed t (liftPoly S) P := by
    change ((mapRingHom e).comp (evalThree (C.comp f) Polynomial.X jetY jetY.derivative)) P = _
    rw [evalThree_map, hef, ← derivative_map, eeY]
    rfl
  have heF : F.map e = poleProduct D^(s.B+s.J) := by rw [Polynomial.map_pow, eeH]
  have hmapped := map_dvd (mapRingHom e) hlocal
  change F.map e ∣ Q.map e at hmapped
  rwa [heF, heQ] at hmapped
end
end K1_14_1_2
end
section
namespace K1_14_1_3
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial
def translation {R : Type*} [CommSemiring R] (i : Fin 2) :
    MvPolynomial (Fin 2) R →ₐ[R] (Polynomial (MvPolynomial (Fin 2) R)) :=
  MvPolynomial.aeval fun j =>
    C (MvPolynomial.X j) + if j = i then Polynomial.X else 0
def seedCoeff {R : Type*} [CommSemiring R] (i : Fin 2) (r : ℕ) :
    MvPolynomial (Fin 2) R →ₗ[R] MvPolynomial (Fin 2) R where
  toFun P := (translation i P).coeff r
  map_add' P Q := by simp
  map_smul' a P := by simp
def mapCoeffs {R A B : Type*} [Semiring R] [Semiring A] [Semiring B]
    [Module R A] [Module R B] (f : A →ₗ[R] B) : (Polynomial A) →ₗ[R] (Polynomial B) :=
  Polynomial.lsum fun n =>
    { toFun := fun a => monomial n (f a)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun c a => by rw [map_smul, ← smul_monomial]; rfl }
@[simp] theorem mapCoeffs_coeff {R A B : Type*} [Semiring R] [Semiring A] [Semiring B]
    [Module R A] [Module R B] (f : A →ₗ[R] B) (Q : (Polynomial A)) (n : ℕ) :
    (mapCoeffs f Q).coeff n = f (Q.coeff n) := by
  change (Q.sum fun j a => monomial j (f a)).coeff n = f (Q.coeff n)
  classical
  simp only [Polynomial.sum, Polynomial.finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq']
  split
  · rfl
  next h => rw [notMem_support_iff.mp h, map_zero]
@[simp] theorem mapCoeffs_monomial {R A B : Type*} [Semiring R] [Semiring A] [Semiring B]
    [Module R A] [Module R B] (f : A →ₗ[R] B) (n : ℕ) (a : A) :
    mapCoeffs f (monomial n a) = monomial n (f a) := by
  ext m
  simp only [mapCoeffs_coeff, coeff_monomial, Finsupp.single_apply]
  split <;> simp
def sourceHasse (i : Fin 2) (r : ℕ) : Source →ₗ[L] Source :=
  mapCoeffs (mapCoeffs (mapCoeffs (seedCoeff i r)))
def sourceX (E : (Polynomial L)) : (Polynomial SeedPoly) :=
  E.map MvPolynomial.C
def cleared {h : ℕ} (D : PoleData h) (i : Fin 2) (r : ℕ) (Q : Source) : Source :=
  jetConstant (sourceX (D.block i ^ (2*r))) * sourceHasse i r Q
end
end K1_14_1_3
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_1_3
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators Polynomial
private theorem seedCoeff_totalDegree (i : Fin 2) (r : ℕ) (P : SeedPoly) :
    (seedCoeff i r P).totalDegree ≤ P.totalDegree := by
  classical
  let g : Fin 2 → MvPolynomial (Option (Fin 2)) L :=
    fun j => MvPolynomial.X (some j) + if j = i then MvPolynomial.X none else 0
  let f : SeedPoly →ₐ[L] MvPolynomial (Option (Fin 2)) L := MvPolynomial.aeval g
  have htrans : translation i = (MvPolynomial.optionEquivLeft L (Fin 2)).toAlgHom.comp f := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = i <;> simp [translation, f, g, hj]
  have hg (j : Fin 2) : (g j).totalDegree ≤ 1 := by
    by_cases hj : j = i
    · simpa [g, hj] using (MvPolynomial.totalDegree_add
        (MvPolynomial.X (some j) : MvPolynomial (Option (Fin 2)) L)
        (MvPolynomial.X none))
    · simp [g, hj]
  have hf : (f P).totalDegree ≤ P.totalDegree := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro m hm
    change (MvPolynomial.aeval g (MvPolynomial.monomial m (P.coeff m))).totalDegree ≤ _
    rw [MvPolynomial.aeval_monomial]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) (MvPolynomial.le_totalDegree hm)
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m j) (hg j))
  change ((translation i P).coeff r).totalDegree ≤ _
  rw [htrans]
  exact (MvPolynomial.totalDegree_coeff_optionEquivLeft_le L (Fin 2) (f P) r).trans hf
theorem ambient_cleared {h : ℕ} (D : PoleData h) {s : Shape} {W : ℕ} {Q : Source}
    (hQ : Q ∈ ambient h s W) (i : Fin 2) (r : ℕ) :
    cleared D i r Q ∈ ambient h s (W+2*h*r) := by
  classical
  intro j k a e he
  simp only [cleared, coeffAt, jetConstant, RingHom.comp_apply]
  rw [coeff_C_mul, coeff_C_mul, coeff_mul, MvPolynomial.coeff_sum]
  simp only [sourceX, coeff_map, MvPolynomial.coeff_C_mul, sourceHasse, mapCoeffs_coeff]
  apply Finset.sum_eq_zero
  rintro ⟨b, c⟩ hbc
  by_cases hb : (D.block i ^ (2*r)).coeff b = 0
  · simp [hb]
  have hbdeg : b ≤ 2*h*r := by
    have hb' := le_natDegree_of_ne_zero hb
    rw [natDegree_pow, D.degree] at hb'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hb'
  have hbc' : b + c = a := by
    simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using hbc
  let A := ((Q.coeff j).coeff k).coeff c
  change (D.block i ^ (2*r)).coeff b * (seedCoeff i r A).coeff e = 0
  by_contra hne
  have hseed : (seedCoeff i r A).coeff e ≠ 0 := fun hz => hne (by simp [hz])
  have ht : seedWeight e ≤ A.totalDegree :=
    (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hseed)).trans
      (seedCoeff_totalDegree i r A)
  have hAnz : A ≠ 0 := fun hz => hseed (by simp [hz])
  have hshape : ∃ d, trueEligible h s W j k c d := by
    by_contra hall
    apply hAnz
    apply MvPolynomial.ext
    intro d
    simpa [coeffAt, A] using hQ j k c d (fun hd => hall ⟨d, hd⟩)
  obtain ⟨d, hs, hj, _, hw⟩ := hshape
  have hseedCap : A.totalDegree ≤ s.U := by
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    intro d hd
    by_contra hbad
    exact (MvPolynomial.mem_support_iff.mp hd) (hQ j k c d (fun hd' => hbad hd'.2.2.1))
  exact he ⟨hs, hj, ht.trans hseedCap, by omega⟩
end
end K1_14_1_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators Polynomial
abbrev Seed (R : Type) [CommSemiring R] := MvPolynomial (Fin 2) R
abbrev SeedFrac (F : Type) [Field F] := FractionRing (Seed F)
abbrev JetPolys (R : Type) [Semiring R] := Polynomial (Polynomial (Polynomial R))
abbrev TrueSource (R : Type) [CommSemiring R] := JetPolys (Seed R)
abbrev Exponent := Fin 2 →₀ ℕ
def sourceCoeff {R : Type} [CommSemiring R] (P : TrueSource R)
    (j i a : ℕ) (e : Exponent) : R :=
  (((P.coeff j).coeff i).coeff a).coeff e
def Shaped {R : Type} [CommSemiring R] (s : Shape) (P : TrueSource R) : Prop :=
  ∀ j i a e, sourceCoeff P j i a e ≠ 0 → i + j ≤ s.B ∧ j ≤ s.J ∧ seedWeight e ≤ s.U
def mapSource {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    TrueSource R →+* TrueSource S :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom (MvPolynomial.map f)))
def SeedWindow {F : Type} [Field F] (U d : ℕ) (side : Fin 2) (g : Seed F) : Prop :=
  ∀ e, g.coeff e ≠ 0 → e (otherBlock side) ≤ U ∧ e side + e (otherBlock side) ≤ U + d
private def substituteJets {R S A : Type} [CommSemiring R] [CommSemiring S]
    [CommSemiring A] [Algebra R S] [Algebra R A]
    (base : S →ₐ[R] A) (y v : A) : Polynomial (Polynomial S) →ₐ[R] A :=
  eval₂AlgHom (eval₂AlgHom base y (fun _ => Commute.all _ _))
    v (fun _ => Commute.all _ _)
def forward {F : Type} [Field F] (H : (Polynomial F)) (lift : (Polynomial (SeedFrac F))) :
    TrueSource F →ₐ[F] JetPolys (SeedFrac F) :=
  let H' := H.map (algebraMap F (SeedFrac F))
  let c : (Polynomial (SeedFrac F)) →+* JetPolys (SeedFrac F) := jetConstant
  let rawY : JetPolys (SeedFrac F) := C (Polynomial.X (R := Polynomial (SeedFrac F)))
  let rawV : JetPolys (SeedFrac F) := Polynomial.X
  let coeffs : (Polynomial (Seed F)) →ₐ[F] (Polynomial (SeedFrac F)) :=
    Polynomial.mapAlgHom (IsScalarTower.toAlgHom F (Seed F) (SeedFrac F))
  let base := (IsScalarTower.toAlgHom F (Polynomial (SeedFrac F)) (JetPolys (SeedFrac F))).comp coeffs
  substituteJets base (c H' * rawY + c lift)
    (c H' * rawV + c H'.derivative * rawY + c lift.derivative)
def PoleTest {F : Type} [Field F] (s : Shape) (H : (Polynomial F))
    (lift : (Polynomial (SeedFrac F))) (P : TrueSource F) : Prop :=
  (jetConstant ((H.map (algebraMap F (SeedFrac F))) ^ (s.B + s.J)) :
    JetPolys (SeedFrac F)) ∣ forward H lift P
abbrev Grade (s : Shape) := Fin (s.B + 1)
abbrev GradeSlot (s : Shape) (q : ℕ) := Fin (min q s.J + 1)
abbrev LocalJet (s : Shape) := Fin (s.B + s.J)
abbrev LocalRow (s : Shape) (q : ℕ) := Fin (s.B + s.J - q) × GradeSlot s q
abbrev ZeroRows (F : Type) (s : Shape) (q : ℕ) :=
  LocalRow s q → GradeSlot s q → LocalJet s → F
def zeroGrade {F : Type} [Field F] (s : Shape) (q : ℕ)
    (f : GradeSlot s q → (Polynomial F)) (k : GradeSlot s q) : (Polynomial F) :=
  ∑ j, if k.val ≤ j.val then
    f j * Polynomial.C (R := F) (j.val.choose k.val : F) *
      (Polynomial.X (R := F)) ^ (q - j.val + k.val) else 0
def ZeroRowsValid {F : Type} [Field F] (s : Shape) (q : ℕ)
    (rows : ZeroRows F s q) : Prop :=
  ∀ f : GradeSlot s q → (Polynomial (SeedFrac F)),
    (∀ k, (Polynomial.X (R := SeedFrac F)) ^ (s.B + s.J) ∣ zeroGrade s q f k) ↔
      ∀ r, ∑ j, ∑ a, algebraMap F (SeedFrac F) (rows r j a) * (f j).coeff a.val = 0
def residue {F : Type} [Field F] (side : Fin 2) (a b c : F) : SeedFrac F :=
  let z := algebraMap (Seed F) (SeedFrac F) (MvPolynomial.X side)
  algebraMap F (SeedFrac F) a * z /
    (algebraMap F (SeedFrac F) b + algebraMap F (SeedFrac F) c * z)
structure SimplePoles {F : Type} [Field F] (h : ℕ) (H : (Polynomial F))
    (lift : (Polynomial (SeedFrac F))) where
  root : Fin (2 * h) → F
  side : Fin (2 * h) → Fin 2
  a : Fin (2 * h) → F
  b : Fin (2 * h) → F
  c : Fin (2 * h) → F
  distinct : Function.Injective root
  factorization : H = ∏ t, (Polynomial.X (R := F) - Polynomial.C (root t))
  vanishes : ∀ t, H.eval (root t) = 0
  simple : ∀ t, H.derivative.eval (root t) ≠ 0
  b_ne : ∀ t, b t ≠ 0
  centre : ∀ t, lift.eval (algebraMap F (SeedFrac F) (root t)) =
    residue (side t) (a t) (b t) (c t)
abbrev Parameter := (Polynomial L)
abbrev GenericField := AlgebraicClosure (FractionRing Parameter)
def specialPoint : Parameter →+* L := Polynomial.evalRingHom 0
def genericPoint : Parameter →+* GenericField :=
  (algebraMap (FractionRing Parameter) GenericField).comp
    (algebraMap Parameter (FractionRing Parameter))
def liftAt {F : Type} [Field F] (point : Parameter →+* F) (num : (Polynomial (Seed Parameter)))
    (den : Seed Parameter) : (Polynomial (SeedFrac F)) :=
  (algebraMap (Seed F) (SeedFrac F) (MvPolynomial.map point den))⁻¹ •
    num.map ((algebraMap (Seed F) (SeedFrac F)).comp (MvPolynomial.map point))
structure RegularDeformation {h : ℕ} (D : PoleData h) (Crt : CRTLift D) where
  H : (Polynomial Parameter)
  num : (Polynomial (Seed Parameter))
  den : Seed Parameter
  monic : H.Monic
  specialH : H.map specialPoint = poleProduct D
  specialDen : MvPolynomial.map specialPoint den ≠ 0
  specialLift : liftAt specialPoint num den = crtPolynomial Crt
  genericDen : MvPolynomial.map genericPoint den ≠ 0
  genericPoles : SimplePoles h (H.map genericPoint) (liftAt genericPoint num den)
end
end K1_14_1_7
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators Polynomial
def readCoeff {F : Type} [Field F] (j i a : ℕ) (e : Exponent) :
    TrueSource F →ₗ[F] F where
  toFun P := sourceCoeff P j i a e
  map_add' P Q := by simp [sourceCoeff]
  map_smul' b P := by simp [sourceCoeff, Polynomial.coeff_smul]
theorem shaped_map {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {s : Shape} {P : TrueSource R} (h : Shaped s P) :
    Shaped s (mapSource f P) := by
  intro j i a e hne
  apply h j i a e
  intro hz
  apply hne
  simpa [sourceCoeff, mapSource, Polynomial.coeff_map, MvPolynomial.coeff_map] using
    (congrArg f hz).trans (map_zero f)
theorem shaped_combination {F ι : Type} [Field F] [Fintype ι]
    {s : Shape} {P : ι → TrueSource F} (hP : ∀ i, Shaped s (P i)) (v : ι → F) :
    Shaped s (Fintype.linearCombination F P v) := by
  intro j i a e hne
  by_contra hbad
  apply hne
  change readCoeff j i a e (Fintype.linearCombination F P v) = 0
  rw [Fintype.linearCombination_apply, map_sum]
  apply Finset.sum_eq_zero
  intro k _
  have he : sourceCoeff (P k) j i a e = 0 := by
    by_contra hz
    exact hbad (hP k j i a e hz)
  rw [map_smul]
  change v k • sourceCoeff (P k) j i a e = 0
  rw [he, smul_zero]
private abbrev CoeffBox (B M U : ℕ) :=
  Fin (B + 1) × Fin (B + 1) × Fin (M + 1) × (Fin 2 → Fin (U + 1))
theorem contacted_finite (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) :
    Module.Finite L (contacted h word s W) := by
  classical
  let M := W + (s.B+s.J)*(2*h) + s.J
  let f : contacted h word s W →ₗ[L] (CoeffBox s.B M s.U → L) :=
    LinearMap.pi fun u =>
      (readCoeff u.1.val u.2.1.val u.2.2.1.val
        (Finsupp.equivFunOnFinite.symm fun k => (u.2.2.2 k).val)).comp
          (contacted h word s W).subtype
  have hzero (Q : contacted h word s W) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    have hA : P ∈ ambient h s W := hP.1
    apply Subtype.ext
    change P = 0
    apply Polynomial.ext
    intro j
    rw [Polynomial.coeff_zero]
    apply Polynomial.ext
    intro i
    rw [Polynomial.coeff_zero]
    apply Polynomial.ext
    intro a
    rw [Polynomial.coeff_zero]
    apply MvPolynomial.ext
    intro e
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    change coeffAt P j i a e = 0
    by_cases he : trueEligible h s W j i a e
    · obtain ⟨hB, hJ, hU, hW⟩ := he
      have hM : a ≤ M := by dsimp [M]; omega
      have hU' (k : Fin 2) : e k ≤ s.U := by
        apply le_trans _ hU
        rw [seedWeight, Finsupp.sum_fintype _ _ (by simp)]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      let u : CoeffBox s.B M s.U :=
        (⟨j, by omega⟩, ⟨i, by omega⟩, ⟨a, by omega⟩,
          fun k => ⟨e k, Nat.lt_succ_of_le (hU' k)⟩)
      have hz := congrFun hQ u
      change coeffAt P j i a (Finsupp.equivFunOnFinite.symm (fun k => e k)) = 0 at hz
      exact (Finsupp.equivFunOnFinite.symm_apply_apply e) ▸ hz
    · exact hA j i a e he
  apply Module.Finite.of_injective f
  intro P Q hPQ
  apply sub_eq_zero.mp
  exact hzero (P - Q) (by rw [map_sub, hPQ, sub_self])
theorem contacted_shaped {h : ℕ} {word : I → L} {s : Shape} {W : ℕ}
    {P : Source} (hP : P ∈ contacted h word s W) : Shaped s P := by
  intro j i a e hn
  have he : trueEligible h s W j i a e := by
    by_contra hf
    exact hn (hP.1 j i a e hf)
  exact ⟨he.1, he.2.1, he.2.2.1⟩
private abbrev WindowSlots (U d : ℕ) :=
  Σ k : Fin (U + 1), Fin (d + k.val + 1)
private def windowExponent {U d : ℕ} (side : Fin 2) (k : WindowSlots U d) : Exponent :=
  Finsupp.equivFunOnFinite.symm (fun t => if t = side then k.2.val else U - k.1.val)
private theorem windowCoeff_card (U d : ℕ) :
    Fintype.card (WindowSlots U d) = triangle U + (U+1)*d := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp_rw [show ∀ k : Fin (U+1), d + k.val + 1 = (k.val + 1) + d by omega]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => k + 1)]
  have hsum := Finset.sum_range_id (U+2)
  rw [Finset.sum_range_succ'] at hsum
  simpa [triangle, Nat.mul_comm (U+2) (U+1), Nat.add_comm 1] using hsum
theorem seedWindow_read (F : Type) [Field F] (U d : ℕ) (side : Fin 2) :
    ∃ read : Seed F →ₗ[F] (Fin (triangle U + (U+1)*d) → F),
      ∀ g, SeedWindow U d side g → read g = 0 → g = 0 := by
  classical
  let eq := Fintype.equivFinOfCardEq (windowCoeff_card U d)
  let read : Seed F →ₗ[F] (Fin (triangle U + (U+1)*d) → F) :=
    LinearMap.pi fun k => MvPolynomial.lcoeff F (windowExponent side (eq.symm k))
  refine ⟨read, ?_⟩
  intro g hg hzero
  apply MvPolynomial.ext
  intro e
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hn
  obtain ⟨ho, ht⟩ := hg e hn
  let k : WindowSlots U d :=
    ⟨⟨U - e (otherBlock side), by omega⟩, ⟨e side, by dsimp; omega⟩⟩
  have he : windowExponent side k = e := by
    ext t
    simp only [windowExponent, Finsupp.coe_equivFunOnFinite_symm]
    by_cases hts : t = side
    · simp [hts, k]
    · have hto : t = otherBlock side := by
        fin_cases t <;> fin_cases side <;> simp_all [otherBlock]
      rw [ite_eq_right hts, hto]
      exact Nat.sub_sub_self ho
  have hz := congrFun hzero (eq k)
  change g.coeff (windowExponent side (eq.symm (eq k))) = 0 at hz
  rw [eq.symm_apply_apply, he] at hz
  exact hn hz
end
end K1_14_1_7
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_1_3
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial
def c1 : Prop :=
  ∀ h (D : PoleData h) (word : I → L) s, ∀ Q ∈ physical word s, ∀ i r,
    cleared D i r Q ∈ physical word s
def c2 : Prop :=
  ∀ h (D : PoleData h) (Crt : CRTLift D) s, ∀ Q ∈ poleSpace Crt s, ∀ i r,
    cleared D i r Q ∈ poleSpace Crt s
def evaluatedHasse (i : Fin 2) (r : ℕ) : Jet →ₗ[FX] Jet :=
  mapCoeffs (mapCoeffs (seedCoeff i r))
theorem evaluatedHasse_eq (i : Fin 2) (r : ℕ) (P : Jet) :
    evaluatedHasse i r P = seedHasse i r P := rfl
private theorem translation_natural {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (i : Fin 2) (P : MvPolynomial (Fin 2) R) :
    (translation i P).map (MvPolynomial.map f) = translation i (MvPolynomial.map f P) := by
  let a := (Polynomial.mapRingHom (MvPolynomial.map f)).comp (translation (R := R) i).toRingHom
  let b := (translation (R := S) i).toRingHom.comp (MvPolynomial.map f)
  have hab : a = b := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [a, b, translation, MvPolynomial.algebraMap_eq]
    · intro j
      by_cases hj : j = i <;> simp [a, b, translation, hj]
  exact DFunLike.congr_fun hab P
private theorem seedCoeff_natural {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (i : Fin 2) (r : ℕ) (P : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (seedCoeff i r P) = seedCoeff i r (MvPolynomial.map f P) := by
  change MvPolynomial.map f ((translation i P).coeff r) =
    (translation i (MvPolynomial.map f P)).coeff r
  rw [← coeff_map, translation_natural]
private def ξ : FX := algebraMap (Polynomial L) FX (Polynomial.X (R := L))
private def centerBase : (Polynomial SeedPoly) →ₐ[L] Seeds :=
  eval₂AlgHom (MvPolynomial.mapAlgHom (Algebra.ofId L FX))
    (MvPolynomial.C ξ) (fun _ => Commute.all _ _)
private theorem centerBase_hasse (i : Fin 2) (r : ℕ) (Q : (Polynomial SeedPoly)) :
    centerBase (mapCoeffs (seedCoeff i r) Q) = seedCoeff i r (centerBase Q) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hp hq =>
    rw [map_add, map_add, map_add, map_add, hp, hq]
  | monomial n a =>
    rw [mapCoeffs_monomial]
    change (monomial n (seedCoeff i r a)).eval₂ (MvPolynomial.map (algebraMap L FX))
      (MvPolynomial.C ξ) = seedCoeff i r
      ((monomial n a).eval₂ (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C ξ))
    rw [eval₂_monomial, eval₂_monomial, ← map_pow]
    simp only [mul_comm _ (MvPolynomial.C (ξ ^ n)), ← MvPolynomial.smul_eq_C_mul,
      map_smul, seedCoeff_natural]
private theorem centerEval_hasse (i : Fin 2) (r : ℕ) (Q : Source) :
    centerEval (sourceHasse i r Q) = evaluatedHasse i r (centerEval Q) := by
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro k
  change ((Polynomial.mapAlgHom (Polynomial.mapAlgHom centerBase)
    (sourceHasse i r Q)).coeff j).coeff k =
      ((evaluatedHasse i r (Polynomial.mapAlgHom (Polynomial.mapAlgHom centerBase) Q)).coeff j).coeff k
  simp only [sourceHasse, evaluatedHasse, coeff_mapAlgHom_apply, mapCoeffs_coeff]
  exact centerBase_hasse i r ((Q.coeff j).coeff k)
private theorem centerBase_sourceX (E : (Polynomial L)) :
    centerBase (sourceX E) = MvPolynomial.C (algebraMap (Polynomial L) FX E) := by
  change (E.map MvPolynomial.C).eval₂ (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C ξ) = _
  rw [eval₂_map]
  have hc : (MvPolynomial.map (algebraMap L FX)).comp
      (MvPolynomial.C : L →+* SeedPoly) = MvPolynomial.C.comp (algebraMap L FX) := by
    ext a
    simp
  rw [hc]
  exact eval₂_algebraMap_X E
    ((IsScalarTower.toAlgHom L FX Seeds).comp (IsScalarTower.toAlgHom L (Polynomial L) FX))
theorem centerEval_clear {h : ℕ} (D : PoleData h) (i : Fin 2) (r : ℕ) (Q : Source) :
    centerEval (cleared D i r Q) =
      (algebraMap (Polynomial L) FX (D.block i ^ (2*r))) • evaluatedHasse i r (centerEval Q) := by
  rw [cleared, map_mul, centerEval_hasse]
  change Polynomial.map (Polynomial.mapRingHom centerBase.toRingHom)
    (C (C (sourceX (D.block i ^ (2*r))))) * _ = _
  rw [Polynomial.map_C]
  change C (Polynomial.map centerBase.toRingHom (C (sourceX (D.block i ^ (2*r))))) * _ = _
  rw [Polynomial.map_C]
  change C (C (centerBase (sourceX (D.block i ^ (2*r))))) * _ = _
  rw [centerBase_sourceX, Algebra.smul_def]
  rfl
end
end K1_14_1_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7
noncomputable section
open K1_14 Polynomial
theorem specialization_rank_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) Parameter) :
    (M.map specialPoint).rank ≤ (M.map genericPoint).rank := by
  classical
  let B := M.map specialPoint
  let f := B.mulVecLin
  let k := B.rank
  let e : LinearMap.range f ≃ₗ[L] (Fin k → L) :=
    (Module.finBasis L (LinearMap.range f)).equivFun
  obtain ⟨right, hr⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨left, hl⟩ := (LinearMap.range f).subtype.exists_leftInverse_of_injective
    (LinearMap.range f).ker_subtype
  let U : Matrix (Fin k) (Fin m) L := (e.toLinearMap.comp left).toMatrix'
  let V : Matrix (Fin n) (Fin k) L := (right.comp e.symm.toLinearMap).toMatrix'
  have hB : U * B * V = 1 := by
    apply (Matrix.toLin' (R := L)).injective
    rw [Matrix.toLin'_one, Matrix.toLin'_mul, Matrix.toLin'_mul]
    simp only [U, V, Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    change e (left (f (right (e.symm v)))) = v
    have hright := LinearMap.congr_fun hr (e.symm v)
    have hleft := LinearMap.congr_fun hl (e.symm v)
    change f.rangeRestrict (right (e.symm v)) = e.symm v at hright
    change left (f.range.subtype (e.symm v)) = e.symm v at hleft
    change e (left (f.range.subtype (f.rangeRestrict (right (e.symm v))))) = v
    rw [hright, hleft, e.apply_symm_apply]
  let U₀ := U.map (Polynomial.C (R := L))
  let V₀ := V.map (Polynomial.C (R := L))
  let S := U₀ * M * V₀
  have hS : S.map specialPoint = 1 := by
    rw [Matrix.map_mul, Matrix.map_mul]
    have hU : U₀.map specialPoint = U := by
      ext i j
      simp [U₀, Matrix.map_apply, specialPoint]
    have hV : V₀.map specialPoint = V := by
      ext i j
      simp [V₀, Matrix.map_apply, specialPoint]
    rw [hU, hV]
    exact hB
  have hdet : S.det ≠ 0 := by
    intro hz
    have he := specialPoint.map_det S
    change specialPoint S.det = (S.map specialPoint).det at he
    rw [hS, hz, map_zero, Matrix.det_one] at he
    exact zero_ne_one he
  have hg : (S.map genericPoint).det ≠ 0 := by
    change (genericPoint.mapMatrix S).det ≠ 0
    rw [← genericPoint.map_det]
    have hinj : Function.Injective genericPoint :=
      (algebraMap (FractionRing Parameter) GenericField).injective.comp
        (IsFractionRing.injective Parameter (FractionRing Parameter))
    intro hz
    exact hdet (hinj (hz.trans (map_zero genericPoint).symm))
  calc
    B.rank = (S.map genericPoint).rank := by
      rw [Matrix.rank_of_det_ne_zero hg, Fintype.card_fin]
    _ ≤ (M.map genericPoint).rank := by
      rw [Matrix.map_mul, Matrix.map_mul]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
end
end K1_14_1_7
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators Polynomial
def c4 : Prop :=
  ∀ {h : ℕ} {D : PoleData h} {Crt : CRTLift D} (E : RegularDeformation D Crt)
    (s : Shape) (ι : Type) [Fintype ι] (P : ι → Source),
    (∀ k, Shaped s (P k)) →
    ∃ n : ℕ, ∃ M : Matrix (Fin n) ι Parameter,
      (∀ v : ι → L, (M.map specialPoint).mulVec v = 0 ↔
        PoleTest s (poleProduct D) (crtPolynomial Crt) (Fintype.linearCombination L P v)) ∧
      ∀ v : ι → GenericField, (M.map genericPoint).mulVec v = 0 ↔
        PoleTest s (E.H.map genericPoint) (liftAt genericPoint E.num E.den)
          (Fintype.linearCombination GenericField (fun k => mapSource (genericPoint.comp (Polynomial.C (R := L))) (P k)) v)
theorem poleTest_of_local {F : Type} [Field F] (s : Shape) {h : ℕ}
    {H : (Polynomial F)} {lift : (Polynomial (SeedFrac F))} (G : SimplePoles h H lift)
    (P : TrueSource F)
    (hd : ∀ t, (jetConstant ((Polynomial.X (R := SeedFrac F) -
        Polynomial.C (algebraMap F (SeedFrac F) (G.root t))) ^ (s.B+s.J)) :
      JetPolys (SeedFrac F)) ∣ forward H lift P) :
    PoleTest s H lift P := by
  let r : Fin (2*h) → (Polynomial (SeedFrac F)) := fun t =>
    Polynomial.X - Polynomial.C (algebraMap F (SeedFrac F) (G.root t))
  have hr : Pairwise (Function.onFun IsCoprime r) :=
    Polynomial.pairwise_coprime_X_sub_C
      ((algebraMap F (SeedFrac F)).injective.comp G.distinct)
  have hcop : Pairwise (Function.onFun IsCoprime
      (fun t => (jetConstant (r t ^ (s.B+s.J)) : JetPolys (SeedFrac F)))) := by
    intro t u hne
    exact ((hr hne).pow).map jetConstant
  have hp := Fintype.prod_dvd_of_coprime hcop hd
  have hprod : H.map (algebraMap F (SeedFrac F)) = ∏ t, r t := by
    rw [G.factorization, Polynomial.map_prod]
    simp [r]
  unfold PoleTest
  rw [hprod, ← Finset.prod_pow, map_prod]
  exact hp
end
end K1_14_1_7
end
section
namespace K1_14_1_3_2
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_3 Polynomial
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
def seriesPolynomial {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* PowerSeries B) : (Polynomial A) →+* PowerSeries ((Polynomial B)) :=
  eval₂RingHom ((PowerSeries.map Polynomial.C).comp f) (PowerSeries.C Polynomial.X)
@[simp] theorem seriesPolynomial_C {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* PowerSeries B) (a : A) :
    seriesPolynomial f (C a) = PowerSeries.map Polynomial.C (f a) :=
  eval₂_C _ _
@[simp] theorem seriesPolynomial_X {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* PowerSeries B) :
    seriesPolynomial f Polynomial.X = PowerSeries.C Polynomial.X :=
  eval₂_X _ _
theorem seriesPolynomial_coeff {A B R : Type*} [CommSemiring A] [CommSemiring B]
    [Semiring R] [Module R A] [Module R B]
    (f : A →+* PowerSeries B) (g : A →ₗ[R] B) (r : ℕ)
    (hg : ∀ a, PowerSeries.coeff r (f a) = g a) (P : (Polynomial A)) :
    PowerSeries.coeff r (seriesPolynomial f P) = mapCoeffs g P := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    rw [mapCoeffs_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, seriesPolynomial_C,
      seriesPolynomial_X, ← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_map, hg,
      C_mul_X_pow_eq_monomial]
theorem seriesPolynomial_fixed {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : B →+* PowerSeries B) (g : A →+* B)
    (hf : ∀ a, f (g a) = PowerSeries.C (g a)) (P : (Polynomial A)) :
    seriesPolynomial f (P.map g) = PowerSeries.C (P.map g) := by
  have he : (seriesPolynomial f).comp (Polynomial.mapRingHom g) =
      PowerSeries.C.comp (Polynomial.mapRingHom g) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [hf]
    · simp
  exact DFunLike.congr_fun he P
theorem seriesPolynomial_constantCoeff {A : Type*} [CommSemiring A]
    (f : A →+* PowerSeries A) (hf : ∀ a, PowerSeries.constantCoeff (f a) = a)
    (P : (Polynomial A)) : PowerSeries.constantCoeff (seriesPolynomial f P) = P := by
  have he : PowerSeries.constantCoeff.comp (seriesPolynomial f) = RingHom.id (Polynomial A) := by
    apply Polynomial.ringHom_ext
    · intro a
      have hfa : PowerSeries.coeff 0 (f a) = a :=
        (PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (hf a)
      simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hfa]
    · simp
  exact DFunLike.congr_fun he P
def sourceSeedShift (i : Fin 2) : SeedPoly →+* PowerSeries SeedPoly :=
  Polynomial.coeToPowerSeries.ringHom.comp (translation i).toRingHom
def sourceShift (i : Fin 2) : Source →+* PowerSeries Source :=
  seriesPolynomial (seriesPolynomial (seriesPolynomial (sourceSeedShift i)))
theorem sourceShift_coeff (i : Fin 2) (r : ℕ) (Q : Source) :
    PowerSeries.coeff r (sourceShift i Q) = sourceHasse i r Q := by
  unfold sourceShift sourceHasse
  apply seriesPolynomial_coeff (R := L)
  intro P
  apply seriesPolynomial_coeff (R := L)
  intro p
  apply seriesPolynomial_coeff (R := L)
  intro a
  exact Polynomial.coeff_coe (φ := translation i a) r
def genericSeedShift (i : Fin 2) : SeedPoly →+* PowerSeries SeedField :=
  (PowerSeries.map (algebraMap SeedPoly SeedField)).comp (sourceSeedShift i)
theorem genericSeedShift_constantCoeff (i : Fin 2) (P : SeedPoly) :
    PowerSeries.constantCoeff (genericSeedShift i P) = algebraMap SeedPoly SeedField P := by
  have he : PowerSeries.constantCoeff.comp (genericSeedShift i) =
      algebraMap SeedPoly SeedField := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [genericSeedShift, sourceSeedShift, translation, MvPolynomial.algebraMap_eq]
    · intro j
      by_cases hj : j = i <;> simp [genericSeedShift, sourceSeedShift, translation, hj]
  exact DFunLike.congr_fun he P
def seedShift (i : Fin 2) : SeedField →+* PowerSeries SeedField :=
  IsLocalization.lift (M := nonZeroDivisors SeedPoly) (S := SeedField)
    (g := genericSeedShift i) fun a =>
      PowerSeries.isUnit_iff_constantCoeff.mpr (by
        rw [genericSeedShift_constantCoeff, isUnit_iff_ne_zero]
        simpa only [map_zero] using
          (IsFractionRing.injective SeedPoly SeedField).ne (nonZeroDivisors.ne_zero a.prop))
@[simp] theorem seedShift_algebraMap (i : Fin 2) (a : SeedPoly) :
    seedShift i (algebraMap SeedPoly SeedField a) = genericSeedShift i a :=
  IsLocalization.lift_eq _ _
theorem seedShift_constantCoeff (i : Fin 2) (a : SeedField) :
    PowerSeries.constantCoeff (seedShift i a) = a := by
  have he : PowerSeries.constantCoeff.comp (seedShift i) = RingHom.id SeedField := by
    apply IsLocalization.ringHom_ext (M := nonZeroDivisors SeedPoly)
    apply RingHom.ext
    intro P
    simp [genericSeedShift_constantCoeff]
  exact DFunLike.congr_fun he a
theorem seedShift_base (i : Fin 2) (a : L) :
    seedShift i (algebraMap L SeedField a) = PowerSeries.C (algebraMap L SeedField a) := by
  rw [IsScalarTower.algebraMap_apply L SeedPoly SeedField, seedShift_algebraMap]
  simp [genericSeedShift, sourceSeedShift, translation, MvPolynomial.algebraMap_eq]
theorem seedShift_other (i j : Fin 2) (hji : j ≠ i) (P : (Polynomial L)) :
    seedShift i (seedInField j P) = PowerSeries.C (seedInField j P) := by
  have he : (seedShift i).comp (seedInField j).toRingHom =
      PowerSeries.C.comp (seedInField j).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change seedShift i (seedInField j (C a)) = PowerSeries.C (seedInField j (C a))
      simpa [seedInField] using seedShift_base i a
    · change seedShift i (seedInField j Polynomial.X) = PowerSeries.C (seedInField j Polynomial.X)
      simp [seedInField, genericSeedShift, sourceSeedShift, translation, hji]
  exact DFunLike.congr_fun he P
theorem seedShift_inv_fixed (i : Fin 2) (a : SeedField)
    (ha : seedShift i a = PowerSeries.C a) :
    seedShift i a⁻¹ = PowerSeries.C a⁻¹ := by
  by_cases hz : a = 0
  · simp [hz]
  apply (isUnit_iff_ne_zero.mpr hz |>.map (PowerSeries.C (R := SeedField))).mul_left_cancel
  rw [← ha, ← map_mul, mul_inv_cancel₀ hz, map_one, ha, ← map_mul, mul_inv_cancel₀ hz, map_one]
theorem rescale_C {R : Type*} [CommSemiring R] (a b : R) :
    PowerSeries.rescale a (PowerSeries.C b) = PowerSeries.C b := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [PowerSeries.coeff_C]
theorem rescale_difference {R : Type*} [CommRing R] (a b : R)
    (F : PowerSeries R) (hF : PowerSeries.constantCoeff F = b) :
    ∃ B, PowerSeries.rescale a F = PowerSeries.C b + PowerSeries.C a * B := by
  have hd : (PowerSeries.X : PowerSeries R) ∣ F - PowerSeries.C b := by
    rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, hF, sub_self]
  obtain ⟨U, hU⟩ := hd
  have he := congrArg (PowerSeries.rescale a) hU
  rw [map_sub, rescale_C, map_mul, PowerSeries.rescale_X, mul_assoc] at he
  exact ⟨PowerSeries.X * PowerSeries.rescale a U, by rw [← he]; ring⟩
end
end K1_14_1_3_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_3
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
def movingBlock {h : ℕ} (D : PoleData h) (i : Fin 2) : (Polynomial Parameter) :=
  (D.block i).map C + C (Polynomial.X (R := L))
def movingProduct {h : ℕ} (D : PoleData h) : (Polynomial Parameter) :=
  movingBlock D 0 * movingBlock D 1
theorem movingBlock_spec {h : ℕ} (D : PoleData h) (i : Fin 2) :
    (movingBlock D i).map specialPoint = D.block i := by
  have hc : specialPoint.comp (C (R := L)) = RingHom.id L :=
    RingHom.ext fun a => eval_C
  rw [movingBlock, Polynomial.map_add, map_map, hc, map_id, Polynomial.map_C]
  simp [specialPoint]
theorem movingBlock_degree {h : ℕ} (hh : 0 < h) (D : PoleData h) (i : Fin 2) :
    IsMonicOfDegree (movingBlock D i) h := by
  have hb : IsMonicOfDegree ((D.block i).map (C (R := L))) h :=
    ⟨((D.monic i).natDegree_map _).trans (D.degree i), (D.monic i).map _⟩
  exact hb.add_right (by simpa using hh)
theorem generic_injective : Function.Injective genericPoint :=
  (algebraMap (FractionRing Parameter) GenericField).injective.comp
    (IsFractionRing.injective Parameter (FractionRing Parameter))
abbrev constGeneric : L →+* GenericField := genericPoint.comp (C (R := L))
abbrev genericBlock {h : ℕ} (D : PoleData h) (i : Fin 2) : (Polynomial GenericField) :=
  (movingBlock D i).map genericPoint
private theorem genericBlock_eq {h : ℕ} (D : PoleData h) (i : Fin 2) :
    genericBlock D i = (D.block i).map constGeneric + C (genericPoint Polynomial.X) := by
  unfold genericBlock movingBlock
  rw [Polynomial.map_add, map_map, Polynomial.map_C]
theorem other_invol (i : Fin 2) : otherBlock (otherBlock i) = i := by
  fin_cases i <;> decide
theorem sum_other {R : Type*} [AddCommMonoid R] (f : Fin 2 → R) (i : Fin 2) :
    (∑ j, f j) = f i + f (otherBlock i) := by
  rw [Fin.sum_univ_two]
  fin_cases i
  · rfl
  · exact add_comm _ _
theorem coprime_other {h : ℕ} (D : PoleData h) (i : Fin 2) :
    IsCoprime (D.block i) (D.block (otherBlock i)) := by
  fin_cases i
  · exact D.coprime
  · exact D.coprime.symm
private theorem derivative_block_ne_zero {h : ℕ} (hlo : 0 < h) (hhi : h < K1.p)
    (D : PoleData h) (i : Fin 2) : (D.block i).derivative ≠ 0 := by
  let _ : CharP L K1.p := charP_of_injective_ringHom (algebraMap K L).injective K1.p
  have hn : (h : L) ≠ 0 := fun hz =>
    (not_le_of_gt hhi) (Nat.le_of_dvd hlo ((CharP.cast_eq_zero_iff _ _ _).mp hz))
  intro hd
  have he := congrArg (fun f : (Polynomial L) => f.coeff (h - 1)) hd
  have hh : h - 1 + 1 = h := by omega
  have hlead : (D.block i).coeff h = 1 := by
    simpa only [← coeff_natDegree, D.degree i] using (D.monic i).leadingCoeff
  rw [coeff_derivative, hh, hlead, one_mul, coeff_zero] at he
  have hcast : ((h - 1 : ℕ) : L) + 1 = (h : L) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : L)) hh
  exact hn (hcast.symm.trans he)
private theorem root_not_const {h : ℕ} (D : PoleData h) (i : Fin 2) (x : L) :
    (genericBlock D i).eval (constGeneric x) ≠ 0 := by
  rw [genericBlock_eq, eval_add, eval_map_apply, eval_C]
  change genericPoint (C ((D.block i).eval x)) + genericPoint Polynomial.X ≠ 0
  rw [← map_add, ← map_zero K1_14_1_7.genericPoint]
  intro he
  have hc := congrArg (fun P : Parameter => P.coeff 1) (generic_injective he)
  simp at hc
private theorem fixed_eval_ne_zero {h : ℕ} (D : PoleData h) (i : Fin 2)
    {α : GenericField} (hr : (genericBlock D i).eval α = 0)
    {f : (Polynomial L)} (hf : f ≠ 0) : (f.map constGeneric).eval α ≠ 0 := by
  intro he
  obtain ⟨x, rfl⟩ := (IsAlgClosed.splits f).mem_range_of_isRoot hf he
  exact root_not_const D i x hr
theorem other_eval_ne_zero {h : ℕ} (hh : 0 < h) (D : PoleData h)
    (i : Fin 2) {α : GenericField} (hr : (genericBlock D i).eval α = 0) :
    (genericBlock D (otherBlock i)).eval α ≠ 0 := by
  have hdiff : D.block i - D.block (otherBlock i) ≠ 0 := by
    intro he
    have hu := coprime_other D i
    rw [← sub_eq_zero.mp he] at hu
    exact not_isUnit_of_natDegree_pos _ (by simpa [D.degree] using hh) (isCoprime_self.mp hu)
  intro ho
  apply fixed_eval_ne_zero D i hr hdiff
  rw [Polynomial.map_sub, eval_sub]
  rw [genericBlock_eq, eval_add, eval_C] at hr ho
  exact sub_eq_zero.mpr (add_right_cancel (hr.trans ho.symm))
theorem deriv_eval_ne_zero {h : ℕ} (hlo : 0 < h) (hhi : h < K1.p)
    (D : PoleData h) (i : Fin 2) {α : GenericField}
    (hr : (genericBlock D i).eval α = 0) : (genericBlock D i).derivative.eval α ≠ 0 := by
  rw [genericBlock_eq, derivative_add, derivative_C, add_zero, derivative_map]
  exact fixed_eval_ne_zero D i hr (derivative_block_ne_zero hlo hhi D i)
theorem constant_eval_ne_zero {h : ℕ} (hh : 0 < h) (D : PoleData h)
    (i : Fin 2) {α : GenericField} (hr : (genericBlock D i).eval α = 0) :
    ((D.constant i).map constGeneric).eval α ≠ 0 := by
  refine fixed_eval_ne_zero D i hr ?_
  intro he
  have hc := (D.determinant i).of_mul_left_right
  rw [he, isCoprime_zero_left] at hc
  exact not_isUnit_of_natDegree_pos _ (by simpa [D.degree] using hh) hc
def simplePoles {h : ℕ} (hlo : 0 < h) (hhi : h < K1.p) (D : PoleData h)
    (lift : (Polynomial (SeedFrac GenericField)))
    (hcentre : ∀ i α, (genericBlock D i).eval α = 0 →
      ((D.constant i).map constGeneric).eval α ≠ 0 →
      lift.eval (algebraMap GenericField (SeedFrac GenericField) α) =
        residue i (-((D.offset i).map constGeneric).eval α)
          (((D.constant i).map constGeneric).eval α) (((D.slope i).map constGeneric).eval α)) :
    SimplePoles h ((movingProduct D).map genericPoint) lift := by
  classical
  let H := (movingProduct D).map genericPoint
  have hblocks : H = genericBlock D 0 * genericBlock D 1 := by
    simp only [H, movingProduct, Polynomial.map_mul]
  have hmonic : H.Monic :=
    (((movingBlock_degree hlo D 0).monic.mul (movingBlock_degree hlo D 1).monic).map _)
  have hdegree : H.natDegree = 2 * h := by
    have hd (i : Fin 2) : (genericBlock D i).natDegree = h :=
      ((movingBlock_degree hlo D i).monic.natDegree_map _).trans
        (movingBlock_degree hlo D i).natDegree_eq
    have hm (i : Fin 2) : (genericBlock D i).Monic :=
      (movingBlock_degree hlo D i).monic.map _
    rw [hblocks, natDegree_mul (hm 0).ne_zero (hm 1).ne_zero, hd, hd]
    omega
  have hside (α : GenericField) (hr : H.eval α = 0) :
      ∃ i, (genericBlock D i).eval α = 0 := by
    rw [hblocks, eval_mul, mul_eq_zero] at hr
    exact hr.elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)
  have hsimple (α : GenericField) (hr : H.eval α = 0) : H.derivative.eval α ≠ 0 := by
    obtain ⟨i, hi⟩ := hside α hr
    have hn := deriv_eval_ne_zero hlo hhi D i hi
    have ho := other_eval_ne_zero hlo D i hi
    rw [hblocks, derivative_mul, eval_add, eval_mul, eval_mul]
    fin_cases i
    · change (genericBlock D 0).eval α = 0 at hi
      change (genericBlock D 1).eval α ≠ 0 at ho
      rw [hi, zero_mul, add_zero]
      exact mul_ne_zero hn ho
    · change (genericBlock D 1).eval α = 0 at hi
      change (genericBlock D 0).eval α ≠ 0 at ho
      rw [hi, mul_zero, zero_add]
      exact mul_ne_zero ho hn
  have hsep : H.Separable := by
    apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed GenericField GenericField H H.derivative).mpr
    intro α
    by_cases he : H.eval α = 0
    · exact Or.inr (by simpa using hsimple α he)
    · exact Or.inl (by simpa using he)
  let s := H.roots.toFinset
  have hcard : Fintype.card s = 2 * h := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      ← (IsAlgClosed.splits H).natDegree_eq_card_roots, hdegree]
  let e : Fin (2 * h) ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  let α : Fin (2 * h) → GenericField := fun t => (e t).val
  have hroot (t : Fin (2 * h)) : H.eval (α t) = 0 :=
    (mem_roots hmonic.ne_zero).mp (Multiset.mem_toFinset.mp (e t).property)
  choose i hi using fun t => hside (α t) (hroot t)
  refine ⟨α, i, _, _, _, Subtype.val_injective.comp e.injective, ?_, hroot,
    fun t => hsimple _ (hroot t), fun t => constant_eval_ne_zero hlo D _ (hi t),
    fun t => hcentre _ _ (hi t) (constant_eval_ne_zero hlo D _ (hi t))⟩
  rw [e.prod_comp (fun x => Polynomial.X - C x.val)]
  rw [Finset.prod_coe_sort s (fun x => Polynomial.X - C x)]
  have hs : s.val = H.roots := by
    exact (Multiset.toFinset_val _).trans (nodup_roots hsep).dedup
  simpa only [Finset.prod, hs] using (IsAlgClosed.splits H).eq_prod_roots_of_monic hmonic
end
end K1_14_1_7_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
def substitute {R A : Type*} [CommSemiring R] [CommSemiring A]
    (base : R →+* A) (y v : A) : (Polynomial (Polynomial R)) →+* A :=
  eval₂RingHom (eval₂RingHom base y) v
def centered {F : Type} [Field F] (α : F) (z : SeedFrac F) :
    TrueSource F →+* JetPolys (SeedFrac F) :=
  let xα := algebraMap F (SeedFrac F) α
  let coeffs := (Polynomial.taylorAlgHom xα).toRingHom.comp
    (Polynomial.mapRingHom (algebraMap (Seed F) (SeedFrac F)))
  substitute (jetConstant.comp coeffs)
    (Polynomial.C Polynomial.X + jetConstant (Polynomial.C z)) Polynomial.X
def zeroSubst {R : Type} [CommSemiring R] : JetPolys R →+* JetPolys R :=
  let x := jetConstant (Polynomial.X (R := R))
  let y : JetPolys R := Polynomial.C Polynomial.X
  substitute jetConstant (x * y) (x * Polynomial.X + y)
def packGrades {R : Type} [CommSemiring R] (s : Shape)
    (f : (q : Grade s) → GradeSlot s q.val → (Polynomial R)) : JetPolys R :=
  ∑ q : Grade s, ∑ j : GradeSlot s q.val,
    Polynomial.C (Polynomial.C (f q j) * Polynomial.X ^ (q.val - j.val)) *
      Polynomial.X ^ j.val
abbrev Shift (s : Shape) (q : Grade s) := Fin (s.B - q.val + 1)
def inputOrdinate {s : Shape} (q : Grade s) (j : GradeSlot s q.val)
    (p : Shift s q) : ℕ :=
  q.val - j.val + p.val
def inputTaylor {F : Type} [Field F] (α : F) (P : TrueSource F) (j i : ℕ) : (Polynomial (Seed F)) :=
  Polynomial.taylor (algebraMap F (Seed F) α) ((P.coeff j).coeff i)
def localSlots {F : Type} [Field F] (s : Shape) (α : F) (z : SeedFrac F)
    (P : TrueSource F) (q : Grade s) (j : GradeSlot s q.val) : (Polynomial (SeedFrac F)) :=
  ∑ p : Shift s q,
    Polynomial.C ((Nat.choose (inputOrdinate q j p) (q.val - j.val) : SeedFrac F) * z ^ p.val) *
      (inputTaylor α P j.val (inputOrdinate q j p)).map (algebraMap (Seed F) (SeedFrac F))
def inputTaylorCoeff {F : Type} [Field F] (α : F) (j i t : ℕ) :
    TrueSource F →ₗ[F] Seed F :=
  ((Polynomial.lcoeff (Seed F) t).restrictScalars F).comp
    (((Polynomial.taylor (algebraMap F (Seed F) α)).restrictScalars F).comp
      (((Polynomial.lcoeff ((Polynomial (Seed F))) i).restrictScalars F).comp
        ((Polynomial.lcoeff ((Polynomial ((Polynomial (Seed F))))) j).restrictScalars F)))
end
end K1_14_1_7_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_3
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 Module Polynomial
open scoped Polynomial
private def quotientBasis {R : Type*} [CommRing R] {b : (Polynomial R)} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) : Basis (Fin n) R (AdjoinRoot b) :=
  (AdjoinRoot.powerBasisAux' hb).reindex (finCongr hd)
private def mulMatrix {R : Type*} [CommRing R] {b : (Polynomial R)} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) (a : (Polynomial R)) : Matrix (Fin n) (Fin n) R :=
  Algebra.leftMulMatrix (quotientBasis hb hd) (AdjoinRoot.mk b a)
private theorem mulMatrix_entry {R : Type*} [CommRing R] {b : (Polynomial R)} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) (a : (Polynomial R)) (i j : Fin n) :
    mulMatrix hb hd a i j = ((a * Polynomial.X (R := R) ^ (j : ℕ)) %ₘ b).coeff i := by
  have hpow (k : Fin b.natDegree) :
      (AdjoinRoot.powerBasisAux' hb) k = AdjoinRoot.root b ^ (k : ℕ) :=
    (AdjoinRoot.powerBasis' hb).basis_eq_pow k
  unfold mulMatrix
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  unfold quotientBasis
  rw [Basis.reindex_apply, hpow, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul,
    Basis.repr_reindex_apply, AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk]
  rfl
private theorem regularInverse {R S : Type*} [CommRing R] [Field S]
    (point : R →+* S) {b a : (Polynomial R)} (hb : b.Monic)
    (hcop : IsCoprime (a.map point) (b.map point)) :
    ∃ (d : R) (u : (Polynomial R)), point d ≠ 0 ∧ b ∣ a * u - C d := by
  let basis := quotientBasis hb rfl
  let M := mulMatrix hb rfl a
  let d := M.det
  let d' := (hb.natDegree_map point)
  have hmap : M.map point = mulMatrix (hb.map point) d' (a.map point) := by
    ext i j
    change point (mulMatrix hb rfl a i j) = _
    rw [mulMatrix_entry, mulMatrix_entry, ← coeff_map, map_modByMonic point hb,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  obtain ⟨v, w, hvw⟩ := hcop
  have hinv : AdjoinRoot.mk (b.map point) v * AdjoinRoot.mk (b.map point) (a.map point) = 1 := by
    simpa only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero, map_one] using
      congrArg (AdjoinRoot.mk (b.map point)) hvw
  have hmat : mulMatrix (hb.map point) d' v * M.map point = 1 := by
    rw [hmap]
    unfold mulMatrix
    rw [← map_mul, hinv, map_one]
  have hd : point d ≠ 0 := by
    have he := congrArg Matrix.det hmat
    rw [Matrix.det_mul, Matrix.det_one] at he
    change _ * (point.mapMatrix M).det = 1 at he
    rw [← point.map_det] at he
    intro hz
    change point M.det = 0 at hz
    rw [hz, mul_zero] at he
    exact zero_ne_one he
  let x := basis.equivFun.symm (M.cramer (basis.equivFun 1))
  have hsol : AdjoinRoot.mk b a * x = d • (1 : AdjoinRoot b) := by
    apply basis.equivFun.injective
    have hv := Algebra.leftMulMatrix_mulVec_repr basis (AdjoinRoot.mk b a) x
    change M.mulVec (basis.repr x) = ⇑(basis.repr (AdjoinRoot.mk b a * x)) at hv
    rw [← Basis.equivFun_apply, ← Basis.equivFun_apply,
      show basis.equivFun x = M.cramer (basis.equivFun 1) from basis.equivFun.apply_symm_apply _,
      Matrix.mulVec_cramer] at hv
    rw [map_smul]
    exact hv.symm
  obtain ⟨u, hu⟩ := AdjoinRoot.mk_surjective x
  refine ⟨d, u, hd, AdjoinRoot.mk_eq_zero.mp ?_⟩
  rw [map_sub, map_mul, hu, hsol, AdjoinRoot.mk_C, Algebra.smul_def, mul_one]
  exact sub_self _
abbrev specialSeed : Seed Parameter →+* Seed L := MvPolynomial.map specialPoint
private abbrev liftSeed : Seed L →+* Seed Parameter := MvPolynomial.map (C (R := L))
private theorem special_liftSeed : specialSeed.comp liftSeed = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext <;> simp [RingHom.comp_apply, specialPoint]
private theorem map_liftSeed (f : (Polynomial (Seed L))) :
    (f.map liftSeed).map specialSeed = f := by
  rw [map_map, special_liftSeed, map_id]
def seedEmbed {F : Type} [Field F] (point : Parameter →+* F) :
    Seed Parameter →+* SeedFrac F :=
  (algebraMap (Seed F) (SeedFrac F)).comp (MvPolynomial.map point)
theorem seedEmbed_ne_zero {F : Type} [Field F] (point : Parameter →+* F)
    {d : Seed Parameter} (hd : MvPolynomial.map point d ≠ 0) : seedEmbed point d ≠ 0 :=
  fun hz => hd ((IsFractionRing.injective (Seed F) (SeedFrac F))
    (hz.trans (map_zero (algebraMap (Seed F) (SeedFrac F))).symm))
private theorem cancel_scalar {F : Type*} [Field F] {a b : F} (ha : a ≠ 0)
    (P : (Polynomial F)) : C ((a * b)⁻¹) * (C a * P) = C (b⁻¹) * P := by
  rw [← mul_assoc, ← map_mul]
  congr 2
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ ha, mul_one]
theorem liftAt_add {F : Type} [Field F] (point : Parameter →+* F)
    (N M : (Polynomial (Seed Parameter))) (d e : Seed Parameter)
    (hd : MvPolynomial.map point d ≠ 0) (he : MvPolynomial.map point e ≠ 0) :
    liftAt point (C e * N + C d * M) (d * e) =
      liftAt point N d + liftAt point M e := by
  simp only [liftAt, smul_eq_C_mul]
  change C ((seedEmbed point (d * e))⁻¹) * (C e * N + C d * M).map (seedEmbed point) =
    C ((seedEmbed point d)⁻¹) * N.map (seedEmbed point) +
    C ((seedEmbed point e)⁻¹) * M.map (seedEmbed point)
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_C, map_mul (seedEmbed point), mul_add]
  congr 1
  · rw [mul_comm (seedEmbed point d) (seedEmbed point e), cancel_scalar (seedEmbed_ne_zero point he)]
  · exact cancel_scalar (seedEmbed_ne_zero point hd) _
abbrev familyBlock {h : ℕ} (D : PoleData h) (i : Fin 2) : (Polynomial (Seed Parameter)) :=
  (movingBlock D i).map MvPolynomial.C
abbrev constSeed : L →+* Seed Parameter := MvPolynomial.C.comp (C (R := L))
def familyAmplitude {h : ℕ} (D : PoleData h) (i : Fin 2) : (Polynomial (Seed Parameter)) :=
  (D.constant i).map constSeed + C (MvPolynomial.X i) * (D.slope i).map constSeed
def familyOffset {h : ℕ} (D : PoleData h) (i : Fin 2) : (Polynomial (Seed Parameter)) :=
  C (MvPolynomial.X i) * (D.offset i).map constSeed
private theorem map_familyBlock {h : ℕ} (D : PoleData h) (i : Fin 2) :
    (familyBlock D i).map specialSeed = (D.block i).map MvPolynomial.C := by
  have hc : specialSeed.comp (MvPolynomial.C : Parameter →+* Seed Parameter) =
      (MvPolynomial.C : L →+* Seed L).comp specialPoint :=
    RingHom.ext fun x => MvPolynomial.map_C specialPoint x
  rw [familyBlock, map_map, hc, ← map_map, movingBlock_spec]
private theorem special_constSeed :
    specialSeed.comp constSeed = (MvPolynomial.C : L →+* Seed L) := by
  ext x
  simp [RingHom.comp_apply, specialPoint]
private def zeroSeeds : Seed L →+* L := MvPolynomial.eval fun _ => 0
private theorem zeroSeeds_constants (f : (Polynomial L)) :
    (f.map MvPolynomial.C).map zeroSeeds = f := by
  have h : zeroSeeds.comp MvPolynomial.C = RingHom.id L :=
    RingHom.ext fun c => MvPolynomial.eval_C _
  rw [map_map, h, map_id]
private def seedPolynomial (i : Fin 2) : (Polynomial L) →+* Seed L :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X i)
private theorem frac_seedPolynomial (i : Fin 2) :
    (algebraMap (Seed L) (SeedFrac L)).comp (seedPolynomial i) = (seedInField i).toRingHom := by
  apply Polynomial.ringHom_ext <;>
    simp [seedPolynomial, seedInField, aeval_def, RingHom.comp_apply, MvPolynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply L (Seed L) (SeedFrac L)]
private theorem zero_seedPolynomial (i : Fin 2) :
    zeroSeeds.comp (seedPolynomial i) = evalRingHom 0 := by
  apply Polynomial.ringHom_ext <;> simp [zeroSeeds, seedPolynomial, RingHom.comp_apply]
structure BlockLift {h : ℕ} (D : PoleData h) (Crt : CRTLift D) (i : Fin 2) where
  den : Seed Parameter
  num : (Polynomial (Seed Parameter))
  specialDen : specialSeed den ≠ 0
  other_dvd : familyBlock D (otherBlock i) ∣ num
  congruence : familyBlock D i ∣ familyAmplitude D i * num + C den * familyOffset D i
  specialLift : liftAt specialPoint num den =
    (seedInField i (Crt.denominator i))⁻¹ • (Crt.numerator i).map (seedInField i)
set_option maxHeartbeats 800000 in
def blockLift {h : ℕ} (hh : 0 < h) (D : PoleData h) (Crt : CRTLift D) (i : Fin 2) :
    BlockLift D Crt i := Classical.choice (by
  let b := familyBlock D i
  let e := familyBlock D (otherBlock i)
  let a := familyAmplitude D i * e
  let q := familyOffset D i
  let z := zeroSeeds.comp specialSeed
  let d₀ := seedPolynomial i (Crt.denominator i)
  let N₀ := (Crt.numerator i).map (seedPolynomial i)
  have hconst := (D.determinant i).of_mul_left_right
  have hd₀ : d₀ ≠ 0 := by
    intro he
    have hz : zeroSeeds d₀ = (Crt.denominator i).eval 0 :=
      DFunLike.congr_fun (zero_seedPolynomial i) _
    rw [he, map_zero] at hz
    exact Crt.regular i 0 (by simpa using hconst) hz.symm
  have hb : b.Monic := (movingBlock_degree hh D i).monic.map _
  have hzb (j : Fin 2) : (familyBlock D j).map z = D.block j := by
    change (familyBlock D j).map (zeroSeeds.comp specialSeed) = _
    rw [← map_map, map_familyBlock, zeroSeeds_constants]
  have hza : a.map z = D.constant i * D.block (otherBlock i) := by
    have hc : z.comp constSeed = RingHom.id L := by
      change (zeroSeeds.comp specialSeed).comp constSeed = RingHom.id L
      rw [RingHom.comp_assoc, special_constSeed]
      exact RingHom.ext fun c => MvPolynomial.eval_C _
    have hX : z (MvPolynomial.X i) = 0 := by simp [z, zeroSeeds]
    simp only [a, e, familyAmplitude, Polynomial.map_mul, Polynomial.map_add, map_map,
      Polynomial.map_C, hc, map_id, hX, C_0, zero_mul, add_zero, hzb]
  have hc : IsCoprime (a.map z) (b.map z) := by
    change IsCoprime (a.map z) ((familyBlock D i).map z)
    rw [hza, hzb i]
    exact hconst.mul_left (coprime_other D i).symm
  obtain ⟨d, u, hd, hu⟩ := regularInverse z hb hc
  have hds : specialSeed d ≠ 0 := fun he => hd (by simp [z, he])
  have hseedConst : (seedPolynomial i).comp C = (MvPolynomial.C : L →+* Seed L) := by
    ext c
    simp [seedPolynomial]
  have hseedX : seedPolynomial i Polynomial.X = MvPolynomial.X i := by simp [seedPolynomial]
  obtain ⟨t₀, ht₀⟩ : e.map specialSeed ∣ N₀ := by
    change (familyBlock D (otherBlock i)).map specialSeed ∣ N₀
    rw [map_familyBlock]
    simpa only [coe_mapRingHom, map_map, hseedConst, N₀] using
      map_dvd (mapRingHom (seedPolynomial i)) (Crt.other_dvd i)
  obtain ⟨w₀, hw₀⟩ : b.map specialSeed ∣ a.map specialSeed * t₀ + C d₀ * q.map specialSeed := by
    have he : (familyAmplitude D i).map specialSeed =
        (D.constant i).map MvPolynomial.C +
          C (MvPolynomial.X i) * (D.slope i).map MvPolynomial.C := by
      simp [familyAmplitude, Polynomial.map_add, Polynomial.map_mul, map_map, special_constSeed]
    have hq : q.map specialSeed = C (MvPolynomial.X i) * (D.offset i).map MvPolynomial.C := by
      simp [q, familyOffset, Polynomial.map_mul, map_map, special_constSeed]
    dsimp only [a, b]
    rw [Polynomial.map_mul, mul_assoc, ← ht₀, he, hq, map_familyBlock,
      ← mul_assoc (C d₀), ← map_mul C]
    simpa only [coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      map_map, hseedConst, map_mul (seedPolynomial i), hseedX, N₀, d₀] using
      map_dvd (mapRingHom (seedPolynomial i)) (Crt.congruence i)
  let r := a * t₀.map liftSeed + C (liftSeed d₀) * q - b * w₀.map liftSeed
  let t := C d * t₀.map liftSeed - u * r
  let N := e * t
  let den := d * liftSeed d₀
  have hseed (c : Seed L) : specialSeed (liftSeed c) = c :=
    DFunLike.congr_fun special_liftSeed c
  have hden : specialSeed den = specialSeed d * d₀ := by
    dsimp only [den]
    rw [map_mul, hseed]
  have hr : r.map specialSeed = 0 := by
    simp only [r, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      map_liftSeed, hseed, hw₀, sub_self]
  have hN : N.map specialSeed = C (specialSeed d) * N₀ := by
    simp only [N, t, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, hr, mul_zero,
      sub_zero, map_liftSeed, ht₀]
    ring
  refine ⟨⟨den, N, by rw [hden]; exact mul_ne_zero hds hd₀, dvd_mul_right _ _, ?_, ?_⟩⟩
  · change b ∣ familyAmplitude D i * N + C den * q
    have he : familyAmplitude D i * N + C den * q =
        b * (C d * w₀.map liftSeed) - (a * u - C d) * r := by
      simp only [N, den, t, r, a, map_mul]
      ring
    rw [he]
    exact dvd_sub (dvd_mul_right _ _) (hu.mul_right _)
  · have hfd := seedEmbed_ne_zero specialPoint hds
    rw [liftAt, smul_eq_C_mul, ← map_map]
    let f := algebraMap (Seed L) (SeedFrac L)
    change f (specialSeed d) ≠ 0 at hfd
    change C ((f (specialSeed den))⁻¹) * (N.map specialSeed).map f = _
    rw [hden, hN, map_mul f, Polynomial.map_mul, Polynomial.map_C, cancel_scalar hfd]
    dsimp only [N₀, d₀]
    rw [map_map, smul_eq_C_mul]
    change C (((f.comp (seedPolynomial i)) (Crt.denominator i))⁻¹) * _ = _
    rw [frac_seedPolynomial]
    rfl)
end
end K1_14_1_7_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_4
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
abbrev jetMap {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    JetPolys R →+* JetPolys S :=
  mapRingHom (mapRingHom (mapRingHom f))
abbrev seedAt {F : Type} [Field F] (point : Parameter →+* F) :
    Seed Parameter →+* SeedFrac F :=
  (algebraMap (Seed F) (SeedFrac F)).comp (MvPolynomial.map point)
abbrev scalarJet {R : Type} [CommSemiring R] (d : R) : JetPolys R :=
  jetConstant (Polynomial.C d)
private abbrev ordinate {R : Type} [CommSemiring R] : JetPolys R :=
  Polynomial.C (Polynomial.X (R := (Polynomial R)))
private def ordinateImage {R : Type} [CommSemiring R] (H N : (Polynomial R)) : JetPolys R :=
  jetConstant H * ordinate + jetConstant N
private def velocityImage {R : Type} [CommSemiring R] (H N : (Polynomial R)) : JetPolys R :=
  jetConstant H * Polynomial.X + jetConstant H.derivative * ordinate + jetConstant N.derivative
private def clearedOrdinate {R : Type} [CommSemiring R] (H N : (Polynomial R)) (d : R) : JetPolys R :=
  scalarJet d * (jetConstant H * ordinate) + jetConstant N
private def clearedVelocity {R : Type} [CommSemiring R] (H N : (Polynomial R)) (d : R) : JetPolys R :=
  scalarJet d * (jetConstant H * Polynomial.X + jetConstant H.derivative * ordinate) +
    jetConstant N.derivative
def cleared (s : Shape) (H : (Polynomial Parameter)) (N : (Polynomial (Seed Parameter)))
    (d : Seed Parameter) (P : Source) : TrueSource Parameter :=
  let h := H.map (MvPolynomial.C (σ := Fin 2))
  let y := clearedOrdinate h N d
  let v := clearedVelocity h N d
  ∑ j ∈ P.support, ∑ i ∈ (P.coeff j).support,
    scalarJet d ^ (s.B - (i + j)) *
      (jetConstant (((P.coeff j).coeff i).map (MvPolynomial.map (Polynomial.C (R := L)))) *
        y ^ i * v ^ j)
private theorem jetMap_constant {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (q : (Polynomial R)) :
    jetMap f (jetConstant q) = jetConstant (q.map f) := by
  simp only [jetMap, jetConstant, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C]
private theorem jetMap_ordinate {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) :
    jetMap f (ordinate : JetPolys R) = (ordinate : JetPolys S) := by
  simp only [jetMap, coe_mapRingHom, Polynomial.map_C, Polynomial.map_X]
private theorem jetMap_velocity {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) :
    jetMap f (Polynomial.X : JetPolys R) = (Polynomial.X : JetPolys S) :=
  Polynomial.map_X _
private theorem forward_constant {F : Type} [Field F] (H : (Polynomial F)) (N : (Polynomial (SeedFrac F)))
    (q : (Polynomial (Seed F))) :
    K1_14_1_7.forward H N (jetConstant q) =
      jetConstant (q.map (algebraMap (Seed F) (SeedFrac F))) := by
  change (C (C q)).eval₂ _ _ = _
  rw [eval₂_C]
  change (C q).eval₂ _ _ = _
  rw [eval₂_C]
  rfl
private theorem forward_ordinate {F : Type} [Field F] (H : (Polynomial F)) (N : (Polynomial (SeedFrac F))) :
    K1_14_1_7.forward H N ordinate =
      ordinateImage (H.map (algebraMap F (SeedFrac F))) N := by
  change (C (Polynomial.X (R := (Polynomial (Seed F))))).eval₂ _ _ = _
  rw [eval₂_C]
  change Polynomial.X.eval₂ _ _ = _
  rw [eval₂_X]
  rfl
private theorem forward_velocity {F : Type} [Field F] (H : (Polynomial F)) (N : (Polynomial (SeedFrac F))) :
    K1_14_1_7.forward H N Polynomial.X =
      velocityImage (H.map (algebraMap F (SeedFrac F))) N := by
  change Polynomial.X.eval₂ _ _ = _
  rw [eval₂_X]
  rfl
private theorem eval_expansion {A T : Type} [CommSemiring A] [CommSemiring T]
    (f : JetPolys A →+* T) (P : JetPolys A) :
    f P = ∑ j ∈ P.support, ∑ i ∈ (P.coeff j).support,
      f (jetConstant ((P.coeff j).coeff i)) * f ordinate ^ i * f Polynomial.X ^ j := by
  conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul]
  congr 1
  conv_lhs => rw [(P.coeff j).as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, jetConstant, RingHom.comp_apply, ordinate]
private theorem degree_of_shaped {s : Shape} {P : Source} (hP : Shaped s P)
    {j i : ℕ} (hi : i ∈ (P.coeff j).support) : i + j ≤ s.B := by
  let q := (P.coeff j).coeff i
  have hn : q ≠ 0 := Polynomial.mem_support_iff.mp hi
  by_contra hb
  apply hn
  apply Polynomial.ext
  intro a
  rw [Polynomial.coeff_zero]
  apply MvPolynomial.ext
  intro e
  change sourceCoeff P j i a e = (0 : Seed L).coeff e
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra he
  exact hb (hP j i a e he).1
private theorem lift_cancel {F : Type} [Field F] (point : Parameter →+* F)
    (N : (Polynomial (Seed Parameter))) (d : Seed Parameter) (hd : MvPolynomial.map point d ≠ 0) :
    Polynomial.C (seedAt point d) * liftAt point N d = N.map (seedAt point) := by
  have hz : seedAt point d ≠ 0 :=
    fun h => hd (IsFractionRing.injective (Seed F) (SeedFrac F) (h.trans (map_zero _).symm))
  change C (seedAt point d) * ((seedAt point d)⁻¹ • N.map (seedAt point)) =
    N.map (seedAt point)
  rw [Polynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hz, map_one, one_mul]
theorem map_abscissa {F : Type} [Field F] (point : Parameter →+* F) (H : (Polynomial Parameter)) :
    (H.map (MvPolynomial.C (σ := Fin 2))).map (seedAt point) =
      (H.map point).map (algebraMap F (SeedFrac F)) := by
  simp only [Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro a
  simp only [seedAt, RingHom.comp_apply, MvPolynomial.map_C]
  exact (IsScalarTower.algebraMap_apply F (Seed F) (SeedFrac F) (point a)).symm
private theorem scale_term {R : Type} [CommSemiring R] (d c y v : R)
    {B i j : ℕ} (hb : i + j ≤ B) :
    d ^ (B - (i + j)) * (c * (d * y) ^ i * (d * v) ^ j) =
      d ^ B * (c * y ^ i * v ^ j) := by
  have he : B - (i + j) + i + j = B := by omega
  conv_rhs => rw [← he, pow_add d (B - (i + j) + i), pow_add d (B - (i + j))]
  rw [mul_pow, mul_pow]
  ring
set_option maxHeartbeats 800000 in
theorem cleared_specializes {F : Type} [Field F] (point : Parameter →+* F)
    (s : Shape) (H : (Polynomial Parameter)) (N : (Polynomial (Seed Parameter)))
    (d : Seed Parameter) (hd : MvPolynomial.map point d ≠ 0) (P : Source) (hP : Shaped s P) :
    jetMap (seedAt point) (cleared s H N d P) =
      scalarJet (seedAt point d) ^ s.B *
        K1_14_1_7.forward (H.map point) (liftAt point N d)
          (mapSource (point.comp (Polynomial.C (R := L))) P) := by
  let f := seedAt point
  let A' := (H.map point).map (algebraMap F (SeedFrac F))
  let N' := liftAt point N d
  let D := scalarJet (f d)
  have hA : (H.map (MvPolynomial.C (σ := Fin 2))).map f = A' := map_abscissa point H
  have hN : jetConstant (N.map f) = D * jetConstant N' := by
    rw [← lift_cancel point N d hd]
    exact map_mul jetConstant _ _
  have hdN : jetConstant (N.derivative.map f) = D * jetConstant N'.derivative := by
    have he := congrArg Polynomial.derivative (lift_cancel point N d hd)
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_map] at he
    rw [← he]
    exact map_mul jetConstant _ _
  have hy : jetMap f (clearedOrdinate (H.map MvPolynomial.C) N d) = D * ordinateImage A' N' := by
    simp only [clearedOrdinate, ordinateImage, map_add, map_mul, scalarJet, jetMap_constant,
      Polynomial.map_C, jetMap_ordinate, hA, hN, D, mul_add]
  have hv : jetMap f (clearedVelocity (H.map MvPolynomial.C) N d) = D * velocityImage A' N' := by
    simp only [clearedVelocity, velocityImage, map_add, map_mul, scalarJet, jetMap_constant,
      Polynomial.map_C, jetMap_ordinate, jetMap_velocity, ← derivative_map (H.map MvPolynomial.C) f, hA, hdN,
      D, mul_add, add_assoc]
  let g := (K1_14_1_7.forward (H.map point) N').toRingHom.comp
    (mapSource (point.comp (Polynomial.C (R := L))))
  have hgC (q : (Polynomial (Seed L))) :
      g (jetConstant q) =
        jetConstant ((q.map (MvPolynomial.map (Polynomial.C (R := L)))).map f) := by
    change (K1_14_1_7.forward (H.map point) N')
      (jetMap (MvPolynomial.map (point.comp (Polynomial.C (R := L)))) (jetConstant q)) = _
    rw [jetMap_constant, forward_constant]
    congr 1
    apply Polynomial.ext
    intro a
    simp only [Polynomial.coeff_map, f, RingHom.comp_apply, MvPolynomial.map_map]
  have hgy : g ordinate = ordinateImage A' N' := by
    change (K1_14_1_7.forward (H.map point) N')
      (jetMap (MvPolynomial.map (point.comp (Polynomial.C (R := L)))) ordinate) = _
    rw [jetMap_ordinate, forward_ordinate]
  have hgv : g Polynomial.X = velocityImage A' N' := by
    change (K1_14_1_7.forward (H.map point) N')
      (jetMap (MvPolynomial.map (point.comp (Polynomial.C (R := L)))) Polynomial.X) = _
    rw [jetMap_velocity, forward_velocity]
  change jetMap f (cleared s H N d P) = D ^ s.B * g P
  rw [eval_expansion g P]
  simp only [cleared, map_sum, map_mul, map_pow, scalarJet, jetMap_constant,
    Polynomial.map_C, hy, hv, hgC, hgy, hgv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i hi
  exact scale_term D _ _ _ (degree_of_shaped hP hi)
end
end K1_14_1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
@[simp] theorem inputTaylorCoeff_apply {F : Type} [Field F] (α : F) (j i t : ℕ)
    (P : TrueSource F) :
    inputTaylorCoeff α j i t P = (inputTaylor α P j i).coeff t := rfl
end
end K1_14_1_7_2
end
section
namespace K1_14_1_3_2
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
abbrev Abscissa := (Polynomial SeedField)
def basePolynomial (P : (Polynomial L)) : Abscissa :=
  P.map (algebraMap L SeedField)
def scaledShift (i : Fin 2) (E : Abscissa) :
    Abscissa →+* PowerSeries Abscissa :=
  (PowerSeries.rescale (E^2)).comp (seriesPolynomial (seedShift i))
theorem scaledShift_base (i : Fin 2) (E : Abscissa) (P : (Polynomial L)) :
    scaledShift i E (basePolynomial P) = PowerSeries.C (basePolynomial P) := by
  unfold scaledShift basePolynomial
  rw [RingHom.comp_apply, seriesPolynomial_fixed _ _ (seedShift_base i), rescale_C]
theorem scaledShift_base_derivative (i : Fin 2) (E : Abscissa) (P : (Polynomial L)) :
    scaledShift i E (basePolynomial P).derivative =
      PowerSeries.C (basePolynomial P).derivative := by
  change scaledShift i E ((P.map _).derivative) = PowerSeries.C ((P.map _).derivative)
  rw [derivative_map]
  exact scaledShift_base i E P.derivative
private def crtTerm {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (j : Fin 2) : Abscissa :=
  C (seedInField j (Crt.denominator j))⁻¹ * (Crt.numerator j).map (seedInField j).toRingHom
private theorem crt_add {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i : Fin 2) :
    crtPolynomial Crt = crtTerm Crt i + crtTerm Crt (otherBlock i) := by
  have he (j : Fin 2) :
      (seedInField j (Crt.denominator j))⁻¹ • (Crt.numerator j).map (seedInField j) =
        crtTerm Crt j := Polynomial.smul_eq_C_mul _
  simp only [crtPolynomial, Fin.sum_univ_two, he]
  fin_cases i
  · rfl
  · exact add_comm _ _
private theorem crtTerm_factor {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i : Fin 2) :
    ∃ W, crtTerm Crt i = basePolynomial (D.block (otherBlock i)) * W := by
  obtain ⟨N, hN⟩ := Crt.other_dvd i
  have hf : (seedInField i).toRingHom.comp (C (R := L)) = algebraMap L SeedField := by
    apply RingHom.ext
    intro a
    exact (seedInField i).commutes a
  refine ⟨C (seedInField i (Crt.denominator i))⁻¹ * N.map (seedInField i).toRingHom, ?_⟩
  rw [crtTerm, hN, Polynomial.map_mul, Polynomial.map_map, hf, basePolynomial]
  exact mul_left_comm _ _ _
private theorem crtTerm_fixed {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i j : Fin 2)
    (hji : j ≠ i) (E : Abscissa) :
    scaledShift i E (crtTerm Crt j) = PowerSeries.C (crtTerm Crt j) ∧
    scaledShift i E (crtTerm Crt j).derivative = PowerSeries.C (crtTerm Crt j).derivative := by
  have hd : seedShift i (seedInField j (Crt.denominator j))⁻¹ =
      PowerSeries.C (seedInField j (Crt.denominator j))⁻¹ :=
    seedShift_inv_fixed _ _ (seedShift_other i j hji _)
  have hm (P : Polynomial (Polynomial L)) :
      scaledShift i E (C (seedInField j (Crt.denominator j))⁻¹ * P.map (seedInField j).toRingHom) =
        PowerSeries.C (C (seedInField j (Crt.denominator j))⁻¹ * P.map (seedInField j).toRingHom) := by
    have hmap := seriesPolynomial_fixed (seedShift i) (seedInField j).toRingHom
      (seedShift_other i j hji) P
    simp only [scaledShift, RingHom.comp_apply, map_mul, seriesPolynomial_C, hd,
      PowerSeries.map_C, hmap, rescale_C]
  exact ⟨hm _, by
    simp only [crtTerm, derivative_mul, derivative_C, zero_mul, zero_add, derivative_map]
    exact hm _⟩
private theorem rawBlock_factor {h : ℕ} (D : PoleData h) (i : Fin 2) :
    rawBlock D = basePolynomial (D.block i) * basePolynomial (D.block (otherBlock i)) := by
  fin_cases i <;> simp [rawBlock, poleProduct, basePolynomial, otherBlock, Polynomial.map_mul,
    mul_comm]
theorem crt_corrections {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i : Fin 2) :
    let E := basePolynomial (D.block i)
    let H := rawBlock D
    let ρ := scaledShift i E
    let C₀ := PowerSeries.C (R := Abscissa)
    ∃ B B₁ : PowerSeries Abscissa,
      ρ (crtPolynomial Crt) = C₀ (crtPolynomial Crt) + C₀ H * C₀ E * B ∧
      ρ (crtPolynomial Crt).derivative = C₀ (crtPolynomial Crt).derivative +
        (C₀ H.derivative * C₀ E - C₀ H * C₀ E.derivative) * B + C₀ H * C₀ E * B₁ := by
  dsimp only
  let E := basePolynomial (D.block i)
  let G := basePolynomial (D.block (otherBlock i))
  let ρ := scaledShift i E
  let C₀ := PowerSeries.C (R := Abscissa)
  have hH : rawBlock D = E * G := rawBlock_factor D i
  obtain ⟨W, hW⟩ := crtTerm_factor Crt i
  have heq : crtPolynomial Crt = G * W + crtTerm Crt (otherBlock i) :=
    (crt_add Crt i).trans (congrArg (· + crtTerm Crt (otherBlock i)) hW)
  have hne : otherBlock i ≠ i := by fin_cases i <;> decide
  obtain ⟨hfixed, hfixed'⟩ := crtTerm_fixed Crt i (otherBlock i) hne E
  have hG : ρ G = C₀ G := scaledShift_base _ _ _
  have hG' : ρ G.derivative = C₀ G.derivative := scaledShift_base_derivative _ _ _
  have hc (P : Abscissa) : ∃ U, ρ P = C₀ P + C₀ (E^2) * U :=
    rescale_difference _ _ _
      (seriesPolynomial_constantCoeff _ (seedShift_constantCoeff i) P)
  obtain ⟨B, hB⟩ := hc W
  obtain ⟨B₁, hB₁⟩ := hc W.derivative
  change ρ _ = _ at hfixed hfixed'
  change ∃ U V, ρ _ = C₀ _ + C₀ _ * C₀ _ * U ∧ ρ _ = _ + _ * U + _ * V
  refine ⟨B, B₁, ?_, ?_⟩
  · rw [heq, hH, map_add ρ, map_mul ρ, hG, hB, hfixed]
    simp only [map_add, map_mul, map_pow]
    ring
  · rw [heq, hH, derivative_add, derivative_mul, derivative_mul]
    simp only [map_add, map_mul, hG, hG', hB, hB₁, hfixed', map_pow]
    ring
end
end K1_14_1_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_1_3_1
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_3 Polynomial
open scoped Polynomial
private abbrev sx : Source := C (C (Polynomial.X (R := SeedPoly)))
private abbrev sy : Source := C (Polynomial.X (R := (Polynomial SeedPoly)))
private abbrev sv : Source := Polynomial.X
private abbrev seedC : SeedPoly →+* Source := C.comp (C.comp C)
private theorem physical_x (x y : L) : atPhysical x y sx = sx + algebraMap L Source x := by
  change Polynomial.eval₂ _ _ (C (C (Polynomial.X (R := SeedPoly)))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (C (Polynomial.X (R := SeedPoly))) = _
  rw [eval₂_C]
  change (algebraMap (Polynomial SeedPoly) Source)
    (Polynomial.eval₂ _ _ (Polynomial.X (R := SeedPoly))) = _
  rw [eval₂_X, map_add]
  rfl
private theorem physical_y (x y : L) :
    atPhysical x y sy = algebraMap L Source y + sx * sv + sy := by
  change Polynomial.eval₂ _ _ (C (Polynomial.X (R := (Polynomial SeedPoly)))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (Polynomial.X (R := (Polynomial SeedPoly))) = _
  rw [eval₂_X]
  rfl
private theorem physical_v (x y : L) : atPhysical x y sv = sv := by
  change Polynomial.eval₂ _ _ (Polynomial.X : Source) = _
  rw [eval₂_X]
private theorem physical_seed (x y : L) (p : SeedPoly) :
    atPhysical x y (seedC p) = seedC p := by
  change Polynomial.eval₂ _ _ (C (C (C p))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (C (C p)) = _
  rw [eval₂_C]
  change (algebraMap (Polynomial SeedPoly) Source) (Polynomial.eval₂ _ _ (C p)) = _
  rw [eval₂_C]
  rfl
private theorem source_ext {T : Type*} [Semiring T] {f g : Source →+* T}
    (hSeed : ∀ p, f (seedC p) = g (seedC p)) (hX : f sx = g sx)
    (hY : f sy = g sy) (hV : f sv = g sv) : f = g := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · exact Polynomial.ringHom_ext hSeed hX
    · exact hY
  · exact hV
private def extendTranslation {A S : Type*} [CommSemiring A] [CommSemiring S]
    (f : A →+* (Polynomial S)) : (Polynomial A) →+* Polynomial (Polynomial S) :=
  eval₂RingHom ((mapRingHom (C : S →+* (Polynomial S))).comp f) (C (Polynomial.X : (Polynomial S)))
@[simp] private theorem extendTranslation_C {A S : Type*} [CommSemiring A] [CommSemiring S]
    (f : A →+* (Polynomial S)) (a : A) :
    extendTranslation f (C a) = (f a).map (C : S →+* (Polynomial S)) := by
  simp [extendTranslation]
@[simp] private theorem extendTranslation_X {A S : Type*} [CommSemiring A] [CommSemiring S]
    (f : A →+* (Polynomial S)) : extendTranslation f Polynomial.X = C (Polynomial.X : (Polynomial S)) := by
  simp [extendTranslation]
private theorem extendTranslation_coeff {A S : Type*} [CommSemiring A] [CommSemiring S]
    [Module L A] [Module L S] {f : A →+* (Polynomial S)} {g : A →ₗ[L] S} {r : ℕ}
    (hg : ∀ a, (f a).coeff r = g a) (P : (Polynomial A)) :
    (extendTranslation f P).coeff r = mapCoeffs g P := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => rw [map_add, coeff_add, map_add, hp, hq]
  | monomial n a =>
    rw [mapCoeffs_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow,
      extendTranslation_C, extendTranslation_X,
      ← (C : (Polynomial S) →+* Polynomial (Polynomial S)).map_pow, coeff_mul_C, coeff_map, hg,
      C_mul_X_pow_eq_monomial]
private def translateSource (i : Fin 2) : Source →+* (Polynomial Source) :=
  extendTranslation (extendTranslation (extendTranslation (translation i).toRingHom))
private theorem translateSource_coeff (i : Fin 2) (r : ℕ) (P : Source) :
    (translateSource i P).coeff r = sourceHasse i r P := by
  unfold translateSource sourceHasse
  apply extendTranslation_coeff
  intro Q
  apply extendTranslation_coeff
  intro q
  apply extendTranslation_coeff
  intro a
  rfl
private theorem translateSource_seed (i : Fin 2) (p : SeedPoly) :
    translateSource i (seedC p) = (translation i p).map seedC := by
  simp only [translateSource, seedC, RingHom.comp_apply, extendTranslation_C,
    Polynomial.map_map]
  rfl
private theorem translateSource_scalar (i : Fin 2) (x : L) :
    translateSource i (algebraMap L Source x) = C (algebraMap L Source x) := by
  change translateSource i (seedC (MvPolynomial.C x)) = C (seedC (MvPolynomial.C x))
  rw [translateSource_seed]
  have h : translation i (MvPolynomial.C x) = C (MvPolynomial.C x) := by
    simp [translation, MvPolynomial.algebraMap_eq]
  rw [h, Polynomial.map_C]
private theorem translateSource_x (i : Fin 2) : translateSource i sx = C sx := by
  simp only [translateSource, sx, extendTranslation_C, extendTranslation_X, map_C]
private theorem translateSource_y (i : Fin 2) : translateSource i sy = C sy := by
  simp only [translateSource, sy, extendTranslation_C, extendTranslation_X, map_C]
private theorem translateSource_v (i : Fin 2) : translateSource i sv = C sv :=
  extendTranslation_X _
private theorem physical_hasse (x y : L) (i : Fin 2) (r : ℕ) (P : Source) :
    atPhysical x y (sourceHasse i r P) = sourceHasse i r (atPhysical x y P) := by
  let f := (mapRingHom (atPhysical x y).toRingHom).comp (translateSource i)
  let g := (translateSource i).comp (atPhysical x y).toRingHom
  have hfg : f = g := by
    apply source_ext
    · intro p
      change (translateSource i (seedC p)).map (atPhysical x y).toRingHom =
        translateSource i (atPhysical x y (seedC p))
      rw [physical_seed, translateSource_seed, Polynomial.map_map]
      have hseed : (atPhysical x y).toRingHom.comp seedC = seedC :=
        RingHom.ext (physical_seed x y)
      rw [hseed]
    · change (translateSource i sx).map (atPhysical x y).toRingHom =
        translateSource i (atPhysical x y sx)
      rw [translateSource_x, Polynomial.map_C]
      change C (atPhysical x y sx) = _
      simp only [physical_x, map_add, translateSource_x, translateSource_scalar]
    · change (translateSource i sy).map (atPhysical x y).toRingHom =
        translateSource i (atPhysical x y sy)
      rw [translateSource_y, Polynomial.map_C]
      change C (atPhysical x y sy) = _
      simp only [physical_y, map_add, map_mul, translateSource_scalar, translateSource_x,
        translateSource_y, translateSource_v]
    · change (translateSource i sv).map (atPhysical x y).toRingHom =
        translateSource i (atPhysical x y sv)
      rw [translateSource_v, Polynomial.map_C]
      change C (atPhysical x y sv) = _
      rw [physical_v, translateSource_v]
  have h := congrArg (fun F : Source →+* (Polynomial Source) => (F P).coeff r) hfg
  change ((translateSource i P).map (atPhysical x y).toRingHom).coeff r =
    (translateSource i (atPhysical x y P)).coeff r at h
  rw [coeff_map] at h
  change atPhysical x y ((translateSource i P).coeff r) =
    (translateSource i (atPhysical x y P)).coeff r at h
  simpa only [translateSource_coeff] using h
private def shiftAbscissa (x : L) (P : (Polynomial SeedPoly)) : (Polynomial SeedPoly) :=
  P.eval₂ C (Polynomial.X + C (MvPolynomial.C x))
private theorem physical_jetConstant (x y : L) (P : (Polynomial SeedPoly)) :
    atPhysical x y (jetConstant P) = jetConstant (shiftAbscissa x P) := by
  change Polynomial.eval₂ _ _ (C (C P)) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (C P) = _
  rw [eval₂_C]
  rfl
theorem proof : K1_14_1_3.c1 := by
  classical
  intro h D word s Q hQ i r t a b j e hab
  rw [cleared, map_mul, physical_jetConstant, physical_hasse]
  simp only [coeffAt, jetConstant, RingHom.comp_apply]
  rw [coeff_C_mul, coeff_C_mul, coeff_mul, MvPolynomial.coeff_sum]
  simp only [sourceHasse, mapCoeffs_coeff]
  apply Finset.sum_eq_zero
  rintro ⟨u, v⟩ huv
  have huv' : u + v = a := by simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using huv
  have hv : (((atPhysical (nodeL t) (word t) Q).coeff j).coeff b).coeff v = 0 := by
    apply MvPolynomial.ext
    intro d
    exact hQ t v b j d (by omega)
  simp [hv]
end
end K1_14_1_3_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped Polynomial
@[simp] theorem substitute_base {R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (y v : A) (p : R) : substitute f y v (jetConstant p) = f p := by
  simp [substitute, jetConstant]
@[simp] theorem substitute_ordinate {R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (y v : A) :
    substitute f y v (C (Polynomial.X (R := R))) = y := by
  simp [substitute]
@[simp] theorem substitute_velocity {R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (y v : A) :
    substitute f y v (Polynomial.X (R := (Polynomial R))) = v := by
  simp [substitute]
theorem jetHom_ext {R A : Type*} [CommSemiring R] [CommSemiring A]
    {f g : (Polynomial (Polynomial R)) →+* A}
    (hbase : ∀ p : R, f (jetConstant p) = g (jetConstant p))
    (hy : f (C Polynomial.X) = g (C Polynomial.X)) (hv : f Polynomial.X = g Polynomial.X) :
    f = g := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · exact hbase
    · exact hy
  · exact hv
theorem forward_as_substitute {F : Type} [Field F] (H : (Polynomial F)) (lift : (Polynomial (SeedFrac F))) :
    let h := H.map (algebraMap F (SeedFrac F))
    let c : (Polynomial (SeedFrac F)) →+* JetPolys (SeedFrac F) := jetConstant
    let y : JetPolys (SeedFrac F) := C Polynomial.X
    (K1_14_1_7.forward H lift).toRingHom = substitute
      (c.comp (Polynomial.mapRingHom (algebraMap (Seed F) (SeedFrac F))))
      (c h * y + c lift) (c h * Polynomial.X + c h.derivative * y + c lift.derivative) := by
  rfl
theorem transfer_dvd {F : Type} [Field F] (H : (Polynomial F)) (lift : (Polynomial (SeedFrac F)))
    (α : F) (z : SeedFrac F) (N : ℕ) (P : TrueSource F)
    (hH : H.eval α = 0) (hz : lift.eval (algebraMap F (SeedFrac F) α) = z)
    (hd : (jetConstant ((Polynomial.X - C (algebraMap F (SeedFrac F) α)) ^ N) :
      JetPolys (SeedFrac F)) ∣ K1_14_1_7.forward (Polynomial.X - C α) (C z) P) :
    (jetConstant ((Polynomial.X - C (algebraMap F (SeedFrac F) α)) ^ N) :
      JetPolys (SeedFrac F)) ∣ K1_14_1_7.forward H lift P := by
  let x : (Polynomial (SeedFrac F)) := Polynomial.X - C (algebraMap F (SeedFrac F) α)
  let h := H.map (algebraMap F (SeedFrac F))
  have hh : x ∣ h := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [h, Polynomial.IsRoot, hH]
  have hl : x ∣ lift - C z := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [Polynomial.IsRoot, hz]
  obtain ⟨u, hu⟩ := hh
  obtain ⟨δ, hδ⟩ := hl
  have hlift : lift = x * δ + C z := by
    rw [← hδ, sub_add_cancel]
  let c : (Polynomial (SeedFrac F)) →+* JetPolys (SeedFrac F) := jetConstant
  let y : JetPolys (SeedFrac F) := C Polynomial.X
  let v : JetPolys (SeedFrac F) := Polynomial.X
  let E := substitute c (c u * y + c δ) (c u * v + c u.derivative * y + c δ.derivative)
  have hx : x.derivative = 1 := by simp [x]
  have hmap : (Polynomial.X - C α).map (algebraMap F (SeedFrac F)) = x := by simp [x]
  have hnorm := forward_as_substitute (Polynomial.X - C α) (C z)
  dsimp only at hnorm
  rw [hmap, hx, Polynomial.derivative_C, map_one, map_zero, one_mul, add_zero] at hnorm
  have he : E.comp (K1_14_1_7.forward (Polynomial.X - C α) (C z)).toRingHom =
      (K1_14_1_7.forward H lift).toRingHom := by
    rw [hnorm, forward_as_substitute]
    apply jetHom_ext
    · intro g
      simp [E, c]
    · change E _ = _
      simp only [substitute_ordinate]
      change E (c x * y + c (C z)) = c h * y + c lift
      rw [map_add, map_mul, hu, hlift]
      simp only [E, c, y, substitute_base, substitute_ordinate, map_mul, map_add]
      ring
    · change E _ = _
      simp only [substitute_velocity]
      change E (c x * v + y) = c h * v + c h.derivative * y + c lift.derivative
      rw [map_add, map_mul, hu, hlift, Polynomial.derivative_add, Polynomial.derivative_mul,
        Polynomial.derivative_mul, Polynomial.derivative_C, hx]
      simp only [E, c, y, v, substitute_base, substitute_ordinate, substitute_velocity,
        map_mul, map_add, map_one, map_zero]
      ring
  have hp := map_dvd E hd
  rw [show E (jetConstant (x ^ N)) = jetConstant (x ^ N) from substitute_base ..] at hp
  exact (DFunLike.congr_fun he P) ▸ hp
private def undoTaylor {R : Type} [CommRing R] (a : R) : JetPolys R →+* JetPolys R :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.taylorAlgHom (-a)).toRingHom)
private theorem undoTaylor_base {R : Type} [CommRing R] (a : R) (g : (Polynomial R)) :
    undoTaylor a (jetConstant g) = jetConstant (Polynomial.taylor (-a) g) := by
  simp [undoTaylor, jetConstant]
private theorem undoTaylor_ordinate {R : Type} [CommRing R] (a : R) :
    undoTaylor a (Polynomial.C (Polynomial.X (R := (Polynomial R)))) = Polynomial.C Polynomial.X := by
  simp [undoTaylor]
private theorem undoTaylor_velocity {R : Type} [CommRing R] (a : R) :
    undoTaylor a (Polynomial.X (R := (Polynomial (Polynomial R)))) = Polynomial.X := by
  simp [undoTaylor]
theorem linear_pole_dvd {F : Type} [Field F] (α : F) (z : SeedFrac F) (N : ℕ)
    (P : TrueSource F)
    (hd : (jetConstant ((Polynomial.X (R := SeedFrac F)) ^ N) :
      JetPolys (SeedFrac F)) ∣ zeroSubst (centered α z P)) :
    (jetConstant ((Polynomial.X - C (algebraMap F (SeedFrac F) α)) ^ N) :
      JetPolys (SeedFrac F)) ∣ K1_14_1_7.forward (Polynomial.X - C α) (C z) P := by
  let a := algebraMap F (SeedFrac F) α
  let x : (Polynomial (SeedFrac F)) := Polynomial.X - C a
  have hx : x.derivative = 1 := by simp [x]
  have ht : Polynomial.taylor (-a) Polynomial.X = x := by
    simp [x, sub_eq_add_neg]
  have hmap : (Polynomial.X - C α).map (algebraMap F (SeedFrac F)) = x := by simp [x, a]
  have hnorm := forward_as_substitute (Polynomial.X - C α) (C z)
  dsimp only at hnorm
  rw [hmap, hx, Polynomial.derivative_C, map_one, map_zero, one_mul, add_zero] at hnorm
  have he : (undoTaylor a).comp (zeroSubst.comp (centered α z)) =
      (K1_14_1_7.forward (Polynomial.X - C α) (C z)).toRingHom := by
    rw [hnorm]
    apply jetHom_ext
    · intro g
      simp only [RingHom.comp_apply, centered, zeroSubst, substitute_base, undoTaylor_base,
        coe_mapRingHom]
      change jetConstant (Polynomial.taylor (-a) (Polynomial.taylor a _)) = jetConstant _
      rw [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
    · simp only [RingHom.comp_apply, centered, zeroSubst, substitute_ordinate, map_add,
        substitute_base, map_mul, undoTaylor_base, ht, undoTaylor_ordinate, Polynomial.taylor_C]
    · simp only [RingHom.comp_apply, centered, zeroSubst, substitute_velocity, map_add,
        map_mul, undoTaylor_base, ht, undoTaylor_ordinate, undoTaylor_velocity]
  have hp := map_dvd (undoTaylor a) hd
  rw [undoTaylor_base, Polynomial.taylor_pow, ht] at hp
  exact (DFunLike.congr_fun he P) ▸ hp
end
end K1_14_1_7_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
namespace K1_14_1_8
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial BigOperators
private theorem affine_coeff {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : S) (P : (Polynomial R)) :
    (P.eval₂ (C.comp f) (C a * (Polynomial.X (R := S)) + C b)).coeff P.natDegree =
      f P.leadingCoeff * a ^ P.natDegree := by
  let Q : (Polynomial S) := C a * (Polynomial.X (R := S)) + C b
  change (P.eval₂ (C.comp f) Q).coeff P.natDegree = _
  have hQ : Q.natDegree ≤ 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    simp [Q, coeff_C_mul, coeff_X, coeff_C, show 1 ≠ k by omega, show k ≠ 0 by omega]
  rw [eval₂_eq_sum_range, Polynomial.finsetSum_coeff, Finset.sum_range_succ]
  have hz : ∑ k ∈ Finset.range P.natDegree,
      (C (f (P.coeff k)) * Q ^ k).coeff P.natDegree = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    apply coeff_eq_zero_of_natDegree_lt
    refine natDegree_mul_le.trans_lt ?_
    simp only [natDegree_C, zero_add]
    exact natDegree_pow_le.trans_lt
      ((Nat.mul_le_mul_left k hQ).trans_lt (by simpa using Finset.mem_range.mp hk))
  simp only [RingHom.comp_apply] at ⊢
  rw [hz, zero_add, coeff_C_mul, coeff_natDegree]
  have hp := coeff_pow_of_natDegree_le (m := P.natDegree) hQ
  simpa [Q, coeff_C_mul, coeff_C] using congrArg (f P.leadingCoeff * ·) hp
theorem leading_forward {h} {D : PoleData h} (Crt : CRTLift D) (P : Source) :
    let j := P.natDegree
    let i := P.leadingCoeff.natDegree
    ((forward Crt P).coeff j).coeff i =
      genericCoefficients P.leadingCoeff.leadingCoeff * rawBlock D ^ (i+j) := by
  let H := rawBlock D
  let A := crtPolynomial Crt
  let x := Polynomial.X (R := (Polynomial SeedField))
  let y : (Polynomial ((Polynomial SeedField))) := C H * x + C A
  let v₀ : (Polynomial ((Polynomial SeedField))) := C H.derivative * x + C A.derivative
  let f : (Polynomial SeedPoly) →+* (Polynomial ((Polynomial SeedField))) := C.comp genericCoefficients.toRingHom
  let g := eval₂RingHom f y
  let c : (Polynomial SeedField) →+* RawSource := jetConstant
  let g' : Polynomial ((Polynomial SeedPoly)) →+* RawSource :=
    eval₂RingHom (R := (Polynomial SeedPoly)) (S := RawSource)
      ((Polynomial.C (R := (Polynomial ((Polynomial SeedField))))).comp f)
      (c H * C x + c A)
  change ((P.eval₂ g' (c H * Polynomial.X + c H.derivative * C x + c A.derivative)).coeff
    P.natDegree).coeff P.leadingCoeff.natDegree = _
  have hg : g' = C.comp g := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [g', g, eval₂_C]
    · simp only [g', g, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
      simp [c, jetConstant, y, map_add, map_mul]
  have hv : c H * Polynomial.X + c H.derivative * C x + c A.derivative =
      C (C H) * Polynomial.X + C v₀ := by
    rw [add_assoc]
    simp [c, jetConstant, v₀, map_add, map_mul]
  rw [hg, hv, affine_coeff g]
  change ((P.leadingCoeff.eval₂ f y) * C H ^ P.natDegree).coeff
    P.leadingCoeff.natDegree = _
  rw [← C_pow, coeff_mul_C]
  unfold f y x
  rw [affine_coeff genericCoefficients.toRingHom]
  simp [H, pow_add, mul_assoc]
end
end K1_14_1_8
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
theorem taylor_seed_degree {F : Type} [Field F] (s : Shape) (α : F)
    (P : TrueSource F) (hP : Shaped s P) (j i t : ℕ) :
    ((inputTaylor α P j i).coeff t).totalDegree ≤ s.U := by
  have hc (a : ℕ) : (((P.coeff j).coeff i).coeff a).totalDegree ≤ s.U := by
    apply Finset.sup_le
    intro e he
    exact (hP j i a e (MvPolynomial.mem_support_iff.mp he)).2.2
  rw [inputTaylor, taylor_coeff, eval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  rw [hasseDeriv_coeff]
  have he :
      ((k + t).choose t : Seed F) * ((P.coeff j).coeff i).coeff (k + t) *
          (algebraMap F (Seed F) α) ^ k =
        MvPolynomial.C (((k + t).choose t : F) * α ^ k) *
          ((P.coeff j).coeff i).coeff (k + t) := by
    simp only [MvPolynomial.algebraMap_eq, map_mul, map_pow, map_natCast]
    ring
  rw [he]
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa only [MvPolynomial.totalDegree_C, zero_add] using hc (k + t))
theorem seedWeight_add (side : Fin 2) (e : Exponent) :
    seedWeight e = e side + e (otherBlock side) := by
  rw [seedWeight, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  fin_cases side <;> simp [otherBlock, Nat.add_comm]
theorem window_sum {F ι : Type} [Field F] [Fintype ι]
    {U d : ℕ} {side : Fin 2} (g : ι → Seed F) (hg : ∀ i, SeedWindow U d side (g i)) :
    SeedWindow U d side (∑ i, g i) := by
  intro e he
  by_contra h
  apply he
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_eq_zero fun i _ => not_imp_comm.mp (hg i e) h
end
end K1_14_1_7_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_4
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial BigOperators
def Bounded {R : Type*} [Semiring R] (u v N : ℕ)
    (P : Polynomial (Polynomial (Polynomial R))) : Prop :=
  ∀ j i a, (((P.coeff j).coeff i).coeff a) ≠ 0 → a + u*i + v*j ≤ N
theorem bounded_mono {R : Type*} [Semiring R] {u v N M : ℕ}
    {P : Polynomial (Polynomial (Polynomial R))} (hp : Bounded u v N P) (hn : N ≤ M) :
    Bounded u v M P :=
  fun j i a ha => (hp j i a ha).trans hn
theorem bounded_add {R : Type*} [Semiring R] {u v N : ℕ}
    {P Q : Polynomial (Polynomial (Polynomial R))} (hp : Bounded u v N P) (hq : Bounded u v N Q) :
    Bounded u v N (P + Q) := by
  intro j i a h
  by_contra hn
  simp only [coeff_add, not_imp_comm.mp (hp j i a) hn, not_imp_comm.mp (hq j i a) hn,
    add_zero] at h
  exact h rfl
theorem bounded_sum {R ι : Type*} [Semiring R] {u v N : ℕ}
    (T : Finset ι) (P : ι → Polynomial (Polynomial (Polynomial R)))
    (hp : ∀ t ∈ T, Bounded u v N (P t)) : Bounded u v N (∑ t ∈ T, P t) := by
  intro j i a hn
  by_contra hx
  apply hn
  simp only [finsetSum_coeff]
  exact Finset.sum_eq_zero fun t ht => not_imp_comm.mp (hp t ht j i a) hx
theorem bounded_mul {R : Type*} [Semiring R] {u v N M : ℕ}
    {P Q : Polynomial (Polynomial (Polynomial R))}
    (hp : Bounded u v N P) (hq : Bounded u v M Q) : Bounded u v (N+M) (P*Q) := by
  intro j i a hn
  by_contra! hx
  apply hn
  rw [coeff_mul]
  simp only [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro ij hj
  rw [coeff_mul, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro ii hi
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ia ha
  by_contra hprod
  have h₁ := hp ij.1 ii.1 ia.1 (left_ne_zero_of_mul hprod)
  have h₂ := hq ij.2 ii.2 ia.2 (right_ne_zero_of_mul hprod)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hj hi ha
  rw [← hj, ← hi, ← ha, Nat.mul_add, Nat.mul_add] at hx
  omega
theorem bounded_jetConstant {R : Type*} [CommSemiring R] {u v N : ℕ}
    {p : (Polynomial R)} (hp : p.natDegree ≤ N) : Bounded u v N (jetConstant p) := by
  intro j i a ha
  have hj : j = 0 := by by_contra hj; simp [jetConstant, coeff_C, hj] at ha
  have hi : i = 0 := by subst j; by_contra hi; simp [jetConstant, coeff_C, hi] at ha
  subst j i
  simp only [jetConstant, RingHom.comp_apply, coeff_C_zero, mul_zero, add_zero] at *
  exact (le_natDegree_of_ne_zero ha).trans hp
abbrev ordinate {R : Type*} [Semiring R] : Polynomial (Polynomial R) :=
  (@Polynomial.C (Polynomial R) _) (Polynomial.X (R := R))
theorem bounded_y {R : Type*} [CommSemiring R] (u v : ℕ) :
    Bounded u v u (ordinate (R := (Polynomial R))) := by
  intro j i a ha
  have hj : j = 0 := by by_contra hj; simp [coeff_C, hj] at ha
  have hi : i = 1 := by subst j; by_contra hi; simp [coeff_X, Ne.symm hi] at ha
  subst j i
  have ha₀ : a = 0 := by by_contra h; simp [coeff_X, coeff_one, h] at ha
  simp [ha₀]
theorem bounded_v {R : Type*} [CommSemiring R] (u v : ℕ) :
    Bounded u v v (Polynomial.X : Polynomial (Polynomial (Polynomial R))) := by
  intro j i a ha
  have hj : j = 1 := by by_contra hj; simp [coeff_X, Ne.symm hj] at ha
  have hi : i = 0 := by subst j; by_contra hi; simp [coeff_one, hi] at ha
  subst j i
  have ha₀ : a = 0 := by by_contra h; simp [coeff_one, h] at ha
  simp [ha₀]
theorem bounded_pow {R : Type*} [CommSemiring R] {u v N : ℕ}
    {P : Polynomial (Polynomial (Polynomial R))} (hp : Bounded u v N P) (n : ℕ) :
    Bounded u v (N*n) (P^n) := by
  induction n with
  | zero => simpa using (bounded_jetConstant (u := u) (v := v) (N := 0)
      (p := (1 : (Polynomial R))) (by simp))
  | succ n ih => simpa [pow_succ, Nat.mul_succ] using bounded_mul ih hp
def substitute {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (y v : Polynomial (Polynomial B)) :
    Polynomial (Polynomial A) →+* Polynomial (Polynomial B) :=
  eval₂RingHom (eval₂RingHom ((jetConstant (R := B)).comp f) y) v
@[simp] theorem substitute_C {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (y v : Polynomial (Polynomial B)) (g : (Polynomial A)) :
    substitute f y v (C g) = eval₂RingHom ((jetConstant (R := B)).comp f) y g := by
  simp [substitute]
@[simp] theorem substitute_X {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (y v : Polynomial (Polynomial B)) :
    substitute f y v (Polynomial.X : Polynomial (Polynomial A)) = v := by
  simp [substitute]
def rawOrdinate {h} (D : PoleData h) (Crt : CRTLift D) : RawSource :=
  jetConstant (rawBlock D) * ordinate + jetConstant (crtPolynomial Crt)
def rawVelocity {h} (D : PoleData h) (Crt : CRTLift D) : RawSource :=
  jetConstant (rawBlock D) * Polynomial.X + jetConstant (rawBlock D).derivative * ordinate +
    jetConstant (crtPolynomial Crt).derivative
theorem forward_apply {h} {D : PoleData h} (Crt : CRTLift D) (P : Source) :
    forward Crt P =
      substitute genericCoefficients.toRingHom (rawOrdinate D Crt) (rawVelocity D Crt) P :=
  rfl
theorem rawBlock_monic {h} (D : PoleData h) : (rawBlock D).Monic :=
  ((D.monic 0).mul (D.monic 1)).map _
theorem rawBlock_degree {h} (D : PoleData h) : (rawBlock D).natDegree = 2*h := by
  rw [rawBlock, poleProduct, ((D.monic 0).mul (D.monic 1)).natDegree_map,
    (D.monic 0).natDegree_mul (D.monic 1),
    D.degree, D.degree, two_mul]
theorem crt_degree {h} (D : PoleData h) (Crt : CRTLift D) :
    (crtPolynomial Crt).natDegree ≤ 2*h := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  refine (natDegree_smul_le _ _).trans (natDegree_map_le.trans ?_)
  exact natDegree_le_iff_degree_le.mpr (Crt.numerator_degree i).le
theorem ambient_degree {h s W P} (hp : P ∈ ambient h s W) {j i : ℕ}
    (hij : (P.coeff j).coeff i ≠ 0) :
    ((P.coeff j).coeff i).natDegree + (i+j)*(131071+h) ≤ W+(s.B+s.J)*(2*h)+j := by
  have hc := leadingCoeff_ne_zero.mpr hij
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr
    (show (((P.coeff j).coeff i).leadingCoeff).support ≠ ∅ by simpa using hc)
  have hne := MvPolynomial.mem_support_iff.mp he
  have hel : trueEligible h s W j i ((P.coeff j).coeff i).natDegree e := by
    by_contra nh
    exact hne (hp j i _ e nh)
  exact hel.2.2.2
theorem quotient_positions {h} {D : PoleData h} (s : Shape) (W : ℕ) {F Q : RawSource}
    (hF : Bounded (131071-h) (131071-h-1) (W+(s.B+s.J)*(2*h)) F)
    (he : F = jetConstant ((rawBlock D)^(s.B+s.J)) * Q) :
    ∀ j i, W < (131071-h)*i+(131071-h-1)*j → (Q.coeff j).coeff i = 0 := by
  intro j i hw
  by_contra hn
  let G := (F.coeff j).coeff i
  have hc : G = (rawBlock D)^(s.B+s.J) * (Q.coeff j).coeff i := by
    dsimp [G]
    rw [he]
    change ((C (C ((rawBlock D)^(s.B+s.J))) * Q).coeff j).coeff i = _
    rw [coeff_C_mul, coeff_C_mul]
  have hd : G.natDegree = (s.B+s.J)*(2*h) + ((Q.coeff j).coeff i).natDegree := by
    rw [hc, ((rawBlock_monic D).pow _).natDegree_mul' hn, natDegree_pow, rawBlock_degree]
  have hne : G ≠ 0 := by
    rw [hc]
    exact mul_ne_zero ((rawBlock_monic D).pow _).ne_zero hn
  have hb := hF j i G.natDegree (leadingCoeff_ne_zero.mpr hne)
  rw [hd] at hb
  omega
end
end K1_14_1_4
end
section
namespace K1_14_1_5
noncomputable section
open K1_14 K1_14_1
open scoped BigOperators
def trueWidth (h : ℕ) (s : Shape) (W q j : ℕ) : ℕ :=
  W + (s.B + s.J) * (2 * h) + j + 1 - q * (131071 + h)
theorem lt_trueWidth_iff (h : ℕ) (s : Shape) (W q j a : ℕ) :
    a < trueWidth h s W q j ↔
      a + q * (131071 + h) ≤ W + (s.B + s.J) * (2 * h) + j := by
  unfold trueWidth
  omega
private abbrev SeedIndex (U : ℕ) := Σ t : Fin (U + 1), Fin (t.val + 1)
private def seedExponent {U : ℕ} (b : SeedIndex U) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![b.1.val - b.2.val, b.2.val]
private theorem seedExponent_zero {U : ℕ} (b : SeedIndex U) :
    seedExponent b 0 = b.1.val - b.2.val := by
  simp [seedExponent]
private theorem seedExponent_one {U : ℕ} (b : SeedIndex U) :
    seedExponent b 1 = b.2.val := by
  simp [seedExponent]
theorem seedWeight_eq (e : Fin 2 →₀ ℕ) : seedWeight e = e 0 + e 1 := by
  unfold seedWeight
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
private theorem seedWeight_seedExponent {U : ℕ} (b : SeedIndex U) :
    seedWeight (seedExponent b) = b.1.val := by
  rw [seedWeight_eq, seedExponent_zero, seedExponent_one]
  have := b.2.isLt
  omega
private theorem seedExponent_injective (U : ℕ) :
    Function.Injective (seedExponent (U := U)) := by
  rintro ⟨t, b⟩ ⟨t', b'⟩ he
  have ht := congrArg seedWeight he
  simp only [seedWeight_seedExponent] at ht
  have htotal : t = t' := Fin.ext ht
  subst t'
  have hb := congrArg (fun e : Fin 2 →₀ ℕ => e 1) he
  simp only [seedExponent_one] at hb
  have hlast : b = b' := Fin.ext hb
  subst b'
  rfl
private theorem exists_seedIndex {U : ℕ} (e : Fin 2 →₀ ℕ) (he : seedWeight e ≤ U) :
    ∃ b : SeedIndex U, seedExponent b = e := by
  let t : Fin (U + 1) := ⟨seedWeight e, by omega⟩
  have ht : t.val = e 0 + e 1 := seedWeight_eq e
  let b : Fin (t.val + 1) := ⟨e 1, by omega⟩
  refine ⟨⟨t, b⟩, Finsupp.ext fun k => ?_⟩
  fin_cases k
  · change seedExponent (⟨t, b⟩ : SeedIndex U) 0 = e 0
    rw [seedExponent_zero]
    change t.val - e 1 = e 0
    omega
  · exact seedExponent_one ⟨t, b⟩
private theorem card_seedIndex (U : ℕ) : Fintype.card (SeedIndex U) = triangle U := by
  simp only [SeedIndex, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => t + 1)]
  have hsum := Finset.sum_range_succ' (fun t : ℕ => t) (U + 1)
  simp only [add_zero] at hsum
  rw [← hsum]
  simp [Finset.sum_range_id, triangle, Nat.mul_comm]
private abbrev MonomialIndex (h : ℕ) (s : Shape) (W : ℕ) :=
  Σ q : Fin (s.B + 1), Σ j : Fin (min q.val s.J + 1),
    Fin (trueWidth h s W q.val j.val) × SeedIndex s.U
abbrev Exponents := ℕ × ℕ × ℕ × (Fin 2 →₀ ℕ)
private def exponents {h : ℕ} {s : Shape} {W : ℕ} (k : MonomialIndex h s W) : Exponents :=
  ⟨k.2.1.val, k.1.val - k.2.1.val, k.2.2.1.val, seedExponent k.2.2.2⟩
private theorem exponents_eligible {h : ℕ} {s : Shape} {W : ℕ} (k : MonomialIndex h s W) :
    trueEligible h s W (exponents k).1 (exponents k).2.1 (exponents k).2.2.1
      (exponents k).2.2.2 := by
  rcases k with ⟨q, j, a, b⟩
  have hq := q.isLt
  have hj := j.isLt
  have hjq := Nat.min_le_left q.val s.J
  have hjJ := Nat.min_le_right q.val s.J
  have hgrade : q.val - j.val + j.val = q.val := by omega
  have hb := b.1.isLt
  simp only [exponents, trueEligible, hgrade, seedWeight_seedExponent]
  exact ⟨by omega, by omega, by omega, (lt_trueWidth_iff h s W _ _ _).mp a.isLt⟩
private theorem exists_monomialIndex {h : ℕ} {s : Shape} {W j i a : ℕ} {e : Fin 2 →₀ ℕ}
    (hel : trueEligible h s W j i a e) :
    ∃ k : MonomialIndex h s W, exponents k = (j, i, a, e) := by
  obtain ⟨hq, hj, he, ha⟩ := hel
  obtain ⟨b, hb⟩ := exists_seedIndex e he
  let q : Fin (s.B + 1) := ⟨i + j, by omega⟩
  let v : Fin (min q.val s.J + 1) := ⟨j, by
    have h : j ≤ min (i + j) s.J := le_min (by omega) hj
    exact Nat.lt_succ_of_le h⟩
  let x : Fin (trueWidth h s W q.val v.val) :=
    ⟨a, (lt_trueWidth_iff h s W _ _ _).mpr ha⟩
  refine ⟨⟨q, v, x, b⟩, ?_⟩
  simp [exponents, q, v, x, hb]
private theorem exponents_injective (h : ℕ) (s : Shape) (W : ℕ) :
    Function.Injective (exponents (h := h) (s := s) (W := W)) := by
  rintro ⟨q, j, a, b⟩ ⟨q', j', a', b'⟩ he
  have hj := congrArg (fun p : Exponents => p.1) he
  have hi := congrArg (fun p : Exponents => p.2.1) he
  change j.val = j'.val at hj
  change q.val - j.val = q'.val - j'.val at hi
  have hlt := j.isLt
  have hlt' := j'.isLt
  have hmin := Nat.min_le_left q.val s.J
  have hmin' := Nat.min_le_left q'.val s.J
  have hq : q = q' := Fin.ext (by omega)
  subst q'
  have hv : j = j' := Fin.ext hj
  subst j'
  have hx : a = a' := Fin.ext (congrArg (fun p : Exponents => p.2.2.1) he)
  subst a'
  have hb : b = b' := seedExponent_injective s.U (congrArg (fun p : Exponents => p.2.2.2) he)
  subst b'
  rfl
def monomialAt (k : Exponents) : Source :=
  Polynomial.monomial k.1 (Polynomial.monomial k.2.1
    (Polynomial.monomial k.2.2.1 (MvPolynomial.monomial k.2.2.2 1)))
theorem coeffAt_monomialAt (k d : Exponents) :
    coeffAt (monomialAt k) d.1 d.2.1 d.2.2.1 d.2.2.2 = if k = d then 1 else 0 := by
  classical
  rcases k with ⟨j, i, a, e⟩
  rcases d with ⟨j', i', a', e'⟩
  by_cases hj : j = j'
  · subst j'
    by_cases hi : i = i'
    · subst i'
      by_cases ha : a = a'
      · subst a'
        simp [coeffAt, monomialAt]
      · simp [coeffAt, monomialAt, Polynomial.coeff_monomial, ha]
    · simp [coeffAt, monomialAt, Polynomial.coeff_monomial, hi]
  · simp [coeffAt, monomialAt, Polynomial.coeff_monomial, hj]
private def ambientMonomial {h : ℕ} {s : Shape} {W : ℕ} (k : MonomialIndex h s W) :
    ambient h s W := by
  refine ⟨monomialAt (exponents k), ?_⟩
  intro j i a e hbad
  rw [coeffAt_monomialAt (exponents k) (j, i, a, e), ite_eq_right]
  intro he
  apply hbad
  simpa only [he] using exponents_eligible k
private def coordinates (h : ℕ) (s : Shape) (W : ℕ) :
    ambient h s W →ₗ[L] (MonomialIndex h s W → L) where
  toFun P k := coeffAt P (exponents k).1 (exponents k).2.1 (exponents k).2.2.1 (exponents k).2.2.2
  map_add' P Q := by
    funext k
    simp [coeffAt]
  map_smul' b P := by
    funext k
    simp [coeffAt, Polynomial.coeff_smul]
private theorem coordinates_monomial {h : ℕ} {s : Shape} {W : ℕ} (k d : MonomialIndex h s W) :
    coordinates h s W (ambientMonomial k) d = if k = d then 1 else 0 := by
  classical
  change coeffAt (monomialAt (exponents k)) (exponents d).1 (exponents d).2.1
    (exponents d).2.2.1 (exponents d).2.2.2 = _
  simp only [coeffAt_monomialAt, (exponents_injective h s W).eq_iff]
private def coordinateEquiv (h : ℕ) (s : Shape) (W : ℕ) :
    ambient h s W ≃ₗ[L] (MonomialIndex h s W → L) := by
  classical
  refine LinearEquiv.ofBijective (coordinates h s W) ⟨?_, ?_⟩
  · intro P Q hPQ
    apply Subtype.ext
    apply Polynomial.ext
    intro j
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro a
    apply MvPolynomial.ext
    intro e
    change coeffAt P j i a e = coeffAt Q j i a e
    by_cases he : trueEligible h s W j i a e
    · obtain ⟨k, hk⟩ := exists_monomialIndex he
      have hcoeff := congrFun hPQ k
      change coeffAt P (exponents k).1 (exponents k).2.1 (exponents k).2.2.1
          (exponents k).2.2.2 =
        coeffAt Q (exponents k).1 (exponents k).2.1 (exponents k).2.2.1
          (exponents k).2.2.2 at hcoeff
      simpa only [hk] using hcoeff
    · exact (P.property j i a e he).trans (Q.property j i a e he).symm
  · intro f
    refine ⟨∑ k, f k • ambientMonomial k, ?_⟩
    funext d
    rw [map_sum]
    simp [Finset.sum_apply, coordinates_monomial, mul_ite]
theorem finrank_ambient (h : ℕ) (s : Shape) (W : ℕ) :
    Module.finrank L (ambient h s W) = triangle s.U * shapeSum s (trueWidth h s W) := by
  rw [(coordinateEquiv h s W).finrank_eq, Module.finrank_pi]
  unfold MonomialIndex
  rw [Fintype.card_sigma]
  calc
    _ = ∑ q : Fin (s.B + 1), ∑ j : Fin (min q.val s.J + 1),
        triangle s.U * trueWidth h s W q j := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.card_prod, Fintype.card_fin, card_seedIndex, Nat.mul_comm]
    _ = _ := by
      unfold shapeSum
      simp only [Finset.mul_sum]
      rw [Fin.sum_univ_eq_sum_range (fun q => ∑ j : Fin (min q s.J + 1),
        triangle s.U * trueWidth h s W q j)]
      apply Finset.sum_congr rfl
      intro q _
      exact Fin.sum_univ_eq_sum_range (fun j => triangle s.U * trueWidth h s W q j)
        (min q s.J + 1)
theorem trueWidth_eq_add {h : ℕ} {s : Shape} {W q j : ℕ} (hh : h ≤ 131071)
    (hw : rawWidthCond h s W) (hq : q ≤ s.B) (hj : j ≤ min q s.J) :
    trueWidth h s W q j = W + 1 + j - q * (131071 - h) + 2 * h * (s.B + s.J - q) := by
  have hdegree : 131071 + h = (131071 - h) + 2 * h := by omega
  have hcredit : q * (2 * h) + (s.B + s.J - q) * (2 * h) = (s.B + s.J) * (2 * h) := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hraw := hw q hq j hj
  rw [trueWidth, hdegree, Nat.mul_add, Nat.mul_comm (2 * h) (s.B + s.J - q)]
  omega
end
end K1_14_1_5
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1200000
namespace K1_14_1_6
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators Polynomial
abbrev sx : Source := Polynomial.C (Polynomial.C (Polynomial.X (R := SeedPoly)))
abbrev sy : Source := Polynomial.C (Polynomial.X (R := (Polynomial SeedPoly)))
abbrev sv : Source := Polynomial.X
abbrev shiftedY : Source := sy + sx * sv
abbrev seedC : SeedPoly →+* Source := C.comp (C.comp C)
theorem physical_x (x r : L) : atPhysical x r sx = sx + algebraMap L Source x := by
  change Polynomial.eval₂ _ _ (Polynomial.C (Polynomial.C (Polynomial.X (R := SeedPoly)))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (Polynomial.C (Polynomial.X (R := SeedPoly))) = _
  rw [eval₂_C]
  change (algebraMap (Polynomial SeedPoly) Source) (Polynomial.eval₂ _ _ (Polynomial.X (R := SeedPoly))) = _
  rw [eval₂_X, map_add]
  rfl
theorem physical_y (x r : L) :
    atPhysical x r sy = shiftedY + algebraMap L Source r := by
  change Polynomial.eval₂ _ _ (Polynomial.C (Polynomial.X (R := (Polynomial SeedPoly)))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (Polynomial.X (R := (Polynomial SeedPoly))) = _
  rw [eval₂_X]
  change algebraMap L Source r + sx * sv + sy = shiftedY + algebraMap L Source r
  dsimp only [shiftedY]
  ac_rfl
theorem physical_v (x r : L) : atPhysical x r sv = sv := by
  change Polynomial.eval₂ _ _ (Polynomial.X : Source) = _
  rw [eval₂_X]
theorem physical_seed (x r : L) (p : SeedPoly) :
    atPhysical x r (seedC p) = seedC p := by
  change Polynomial.eval₂ _ _ (C (C (C p))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (C (C p)) = _
  rw [eval₂_C]
  change (algebraMap (Polynomial SeedPoly) Source) (Polynomial.eval₂ _ _ (C p)) = _
  rw [eval₂_C]
  rfl
theorem product_eq_monomial (p : SeedPoly) (a b j : ℕ) :
    seedC p * sx^a * sy^b * sv^j =
      monomial j (monomial b (monomial a p)) := by
  simp only [seedC, RingHom.comp_apply, sx, sy, sv, ← map_pow, ← map_mul,
    C_mul_X_pow_eq_monomial]
theorem seed_scalar (e : Fin 2 →₀ ℕ) (c : L) :
    seedC (MvPolynomial.monomial e c) = c • seedC (MvPolynomial.monomial e 1) := by
  rw [Algebra.smul_def]
  change _ = seedC (MvPolynomial.C c) * _
  rw [← map_mul, MvPolynomial.C_mul_monomial, mul_one]
theorem mem_of_monomials (M : Submodule L Source) (P : Source)
    (H : ∀ j b a e, coeffAt P j b a e ≠ 0 →
      monomial j (monomial b (monomial a (MvPolynomial.monomial e
        (coeffAt P j b a e)))) ∈ M) : P ∈ M := by
  rw [P.as_sum_support]
  apply M.sum_mem
  intro j _
  rw [show monomial j (P.coeff j) =
      monomial j (∑ b ∈ (P.coeff j).support, monomial b ((P.coeff j).coeff b)) from
    congrArg _ (P.coeff j).as_sum_support, map_sum]
  apply M.sum_mem
  intro b _
  let p := (P.coeff j).coeff b
  change monomial j (monomial b p) ∈ M
  rw [show p = ∑ a ∈ p.support, monomial a (p.coeff a) from p.as_sum_support]
  simp only [map_sum]
  apply M.sum_mem
  intro a _
  rw [show monomial a (p.coeff a) =
      monomial a (∑ e ∈ (p.coeff a).support, MvPolynomial.monomial e ((p.coeff a).coeff e)) from
    congrArg _ (p.coeff a).as_sum]
  simp only [map_sum]
  apply M.sum_mem
  intro e he
  exact H j b a e (MvPolynomial.mem_support_iff.mp he)
theorem mul_add_pow_mem (M : Submodule L Source) (p u v : Source)
    (n : ℕ) (H : ∀ k ≤ n, p * u^k * v^(n-k) ∈ M) :
    p * (u+v)^n ∈ M := by
  rw [add_pow u v n, Finset.mul_sum]
  apply M.sum_mem
  intro k hk
  have h := M.smul_mem (n.choose k : L) (H k (by simpa using hk))
  rw [Algebra.smul_def, map_natCast] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h
theorem mul_shift_pow_mem (M : Submodule L Source) (p u : Source)
    (r : L) (n : ℕ) (H : ∀ k ≤ n, p * u^k ∈ M) :
    p * (u + algebraMap L Source r)^n ∈ M := by
  apply mul_add_pow_mem
  intro k hk
  rw [mul_comm (p * u^k), ← map_pow, ← Algebra.smul_def]
  exact M.smul_mem _ (H k hk)
structure Low (m : ℕ) where
  j : ℕ
  b : ℕ
  a : ℕ
  e : Fin 2 →₀ ℕ
  low : a + 2*b < m
def cut (s : Shape) : Source →ₗ[L] (Low s.m → L) where
  toFun P z := coeffAt P z.j z.b z.a z.e
  map_add' P Q := by
    funext z
    simp [coeffAt]
  map_smul' c P := by
    funext z
    simp [coeffAt, Polynomial.coeff_smul]
private abbrev SeedIdx (U : ℕ) := Σ a : Fin (U+1), Fin (U+1-a.val)
private def seedExp {U : ℕ} (i : SeedIdx U) : Fin 2 →₀ ℕ :=
  (finTwoArrowEquiv' ℕ).symm (i.1.val, i.2.val)
private theorem exists_seedIdx {U : ℕ} {e : Fin 2 →₀ ℕ} (he : seedWeight e ≤ U) :
    ∃ i : SeedIdx U, seedExp i = e := by
  let pair := finTwoArrowEquiv' ℕ e
  have hw : pair.1 + pair.2 ≤ U := by
    simpa only [pair, seedWeight, Equiv.symm_apply_apply, ← finTwoArrowEquiv'_sum_eq (d := pair)]
      using he
  refine ⟨⟨⟨pair.1, by omega⟩, ⟨pair.2, ?_⟩⟩, ?_⟩
  · change pair.2 < U+1-pair.1
    omega
  · exact (finTwoArrowEquiv' ℕ).symm_apply_apply e
private theorem seed_card (U : ℕ) : Fintype.card (SeedIdx U) = triangle U := by
  simp only [SeedIdx, Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_eq_sum_range]
  calc
    (∑ a ∈ Finset.range (U+1), (U+1-a)) = (∑ a ∈ Finset.range (U+1), (a+1)) := by
      rw [← Finset.sum_range_reflect (fun a => U+1-a) (U+1)]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [Finset.mem_range] at ha
      omega
    _ = (∑ a ∈ Finset.range (U+2), a) := by
      simpa only [Nat.add_zero] using (Finset.sum_range_succ' (fun a : ℕ => a) (U+1)).symm
    _ = triangle U := by
      rw [Finset.sum_range_id, triangle, show U+2-1 = U+1 by omega, Nat.mul_comm]
private abbrev GenIdx (s : Shape) :=
  (Σ q : Fin (s.B+1), Σ k : Fin (min q.val s.J+1),
    Fin (s.m + min q.val s.J - (q.val + 2*k.val))) × SeedIdx s.U
private theorem gen_card (s : Shape) :
    Fintype.card (GenIdx s) =
      shapeSum s (fun q k => s.m + min q s.J - (q + 2*k)) * triangle s.U := by
  unfold GenIdx
  rw [Fintype.card_prod, seed_card, shapeSum]
  congr 1
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range
    (fun q : ℕ => ∑ k : Fin (min q s.J+1), (s.m + min q s.J - (q + 2*k.val)))]
  refine Finset.sum_congr rfl ?_
  intro q _
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => s.m + min q s.J - (q + 2*k)) (min q s.J+1)
def localGen (q d k a : ℕ) (e : Fin 2 →₀ ℕ) : Source :=
  seedC (MvPolynomial.monomial e 1) * sx^a * sy^k * sv^(d-k) * shiftedY^(q-d)
def generators (s : Shape) (i : GenIdx s) : Low s.m → L :=
  cut s (localGen i.1.1.val (min i.1.1.val s.J) i.1.2.1.val i.1.2.2.val (seedExp i.2))
def localSpan (s : Shape) : Submodule L (Low s.m → L) :=
  Submodule.span L (Set.range (generators s))
private abbrev preimage (s : Shape) : Submodule L Source := (localSpan s).comap (cut s)
private theorem high_mono (s : Shape) (e : Fin 2 →₀ ℕ) (a b j : ℕ)
    (h : s.m ≤ a+2*b) :
    seedC (MvPolynomial.monomial e 1) * sx^a * sy^b * sv^j ∈ LinearMap.ker (cut s) := by
  apply LinearMap.mem_ker.mpr
  funext z
  change coeffAt _ z.j z.b z.a z.e = 0
  rw [product_eq_monomial]
  have hz := z.low
  by_cases hj : j = z.j
  · by_cases hb : b = z.b
    · by_cases ha : a = z.a
      · omega
      · simp [coeffAt, Polynomial.coeff_monomial, hj, hb, ha]
    · simp [coeffAt, Polynomial.coeff_monomial, hj, hb]
  · simp [coeffAt, Polynomial.coeff_monomial, hj]
private theorem collect_powers {R : Type*} [CommMonoid R] (c x y v : R)
    (a k j t n : ℕ) :
    (c * x^a * y^k * v^j) * y^t * (x*v)^n = c * x^(a+n) * y^(k+t) * v^(j+n) := by
  simp only [pow_add, mul_pow]
  ac_rfl
theorem collect_adapted {R : Type*} [CommMonoid R] (c x y v A : R)
    (a j k n : ℕ) :
    (c * x^a * v^j * A) * y^k * (x*v)^n = c * x^(a+n) * y^k * v^(j+n) * A := by
  simp only [pow_add, mul_pow]
  ac_rfl
theorem move_v {R : Type*} [CommMonoid R] (c v x y : R) :
    c * v * x * y = c * x * y * v := by ac_rfl
theorem high_gen (s : Shape) (q d k a : ℕ) (e : Fin 2 →₀ ℕ)
    (h : s.m ≤ a+(q-d)+2*k) : localGen q d k a e ∈ LinearMap.ker (cut s) := by
  unfold localGen
  change _ * (sy + sx * sv)^(q-d) ∈ _
  apply mul_add_pow_mem
  intro t ht
  have ht' := high_mono s e (a+(q-d-t)) (k+t) (d-k+(q-d-t)) (by omega)
  rw [collect_powers]
  exact ht'
private theorem gen_mem (s : Shape) (q k a : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : q ≤ s.B) (hk : k ≤ min q s.J) (he : seedWeight e ≤ s.U) :
    localGen q (min q s.J) k a e ∈ preimage s := by
  change cut s _ ∈ localSpan s
  have hd : min q s.J ≤ q := min_le_left _ _
  by_cases ha : a < s.m + min q s.J - (q+2*k)
  · obtain ⟨i, rfl⟩ := exists_seedIdx he
    exact Submodule.subset_span
      ⟨(⟨⟨q, Nat.lt_succ_of_le hq⟩, ⟨⟨k, Nat.lt_succ_of_le hk⟩, ⟨a, ha⟩⟩⟩, i), rfl⟩
  · rw [LinearMap.mem_ker.mp (high_gen s q (min q s.J) k a e (by omega))]
    exact (localSpan s).zero_mem
private theorem shifted_mono_mem (s : Shape) (a b j : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : b+j ≤ s.B) (hj : j ≤ s.J) (he : seedWeight e ≤ s.U) :
    seedC (MvPolynomial.monomial e 1) * sx^a * shiftedY^b * sv^j ∈ preimage s := by
  let q := b+j
  let d := min q s.J
  have hd : d ≤ q := min_le_left _ _
  have hjd : j ≤ d := le_min (Nat.le_add_left _ _) hj
  let p := seedC (MvPolynomial.monomial e 1) * sx^a * sv^j * shiftedY^(q-d)
  have hpow : shiftedY^b = shiftedY^(q-d) * shiftedY^(d-j) := by
    rw [← pow_add, show q-d+(d-j) = b by dsimp only [q] at *; omega]
  have hexpand : p * (sy + sx*sv)^(d-j) ∈ preimage s := by
    apply mul_add_pow_mem
    intro k hk
    have hV : d-k = j+(d-j-k) := by omega
    have hgen := gen_mem s q k (a+(d-j-k)) e hq (by omega) he
    change localGen q d k (a+(d-j-k)) e ∈ _ at hgen
    rw [localGen, hV] at hgen
    dsimp only [p]
    rw [collect_adapted]
    exact hgen
  dsimp only [p] at hexpand
  change (seedC (MvPolynomial.monomial e 1) * sx^a * sv^j * shiftedY^(q-d)) *
    shiftedY^(d-j) ∈ preimage s at hexpand
  rw [move_v (seedC (MvPolynomial.monomial e 1) * sx^a), mul_assoc
    (seedC (MvPolynomial.monomial e 1) * sx^a), ← hpow] at hexpand
  exact hexpand
private theorem translated_mono_mem (s : Shape) (x r : L) (a b j : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : b+j ≤ s.B) (hj : j ≤ s.J) (he : seedWeight e ≤ s.U) :
    seedC (MvPolynomial.monomial e 1) * (sx + algebraMap L Source x)^a *
      (shiftedY + algebraMap L Source r)^b * sv^j ∈ preimage s := by
  let p := seedC (MvPolynomial.monomial e 1) * sv^j
  have h : (p * (shiftedY + algebraMap L Source r)^b) *
      (sx + algebraMap L Source x)^a ∈ preimage s := by
    apply mul_shift_pow_mem
    intro t _
    have h' : (p * sx^t) * (shiftedY + algebraMap L Source r)^b ∈ preimage s := by
      apply mul_shift_pow_mem
      intro k hk
      dsimp only [p]
      rw [move_v]
      exact shifted_mono_mem s t k j e (by omega) hj he
    rw [mul_right_comm]
    exact h'
  rw [mul_right_comm p] at h
  dsimp only [p] at h
  rw [move_v] at h
  exact h
private theorem atPhysical_mem (h : ℕ) (s : Shape) (W : ℕ) (x r : L)
    (P : ambient h s W) : cut s (atPhysical x r P.val) ∈ localSpan s := by
  change P.val ∈ (preimage s).comap (atPhysical x r).toLinearMap
  apply mem_of_monomials
  intro j b a e hne
  have hel : trueEligible h s W j b a e := by
    by_contra hn
    exact hne (P.property j b a e hn)
  obtain ⟨hq, hj, he, _⟩ := hel
  change atPhysical x r _ ∈ preimage s
  rw [← product_eq_monomial, seed_scalar, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, map_smul]
  apply (preimage s).smul_mem
  simp only [map_mul, map_pow, physical_x, physical_y, physical_v, physical_seed]
  exact translated_mono_mem s x r a b j e hq hj he
def nodeMap (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) (i : I) :
    ambient h s W →ₗ[L] localSpan s :=
  LinearMap.codRestrict (localSpan s)
    (((cut s).comp (atPhysical (nodeL i) (word i)).toLinearMap).domRestrict (ambient h s W))
    (atPhysical_mem h s W (nodeL i) (word i))
theorem localSpan_finrank (s : Shape) :
    Module.finrank L (localSpan s) ≤
      shapeSum s (fun q k => s.m + min q s.J - (q + 2*k)) * triangle s.U := by
  rw [← gen_card]
  exact finrank_range_le_card (R := L) (generators s)
end
end K1_14_1_6
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
def c1 : Prop :=
  ∀ (F : Type) [Field F] (s : Shape) (α : F) (z : SeedFrac F) (P : TrueSource F),
    Shaped s P → centered α z P = packGrades s (localSlots s α z P)
def c2 : Prop :=
  ∀ (F : Type) [Field F] (s : Shape)
    (f : (q : Grade s) → GradeSlot s q.val → (Polynomial (SeedFrac F))),
    (∀ q k, (Polynomial.X (R := SeedFrac F)) ^ (s.B+s.J) ∣ zeroGrade s q.val (f q) k) →
    (jetConstant ((Polynomial.X (R := SeedFrac F)) ^ (s.B+s.J)) : JetPolys (SeedFrac F)) ∣
      zeroSubst (packGrades s f)
end
end K1_14_1_7_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
namespace K1_14_1_8
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial BigOperators nonZeroDivisors
abbrev Position := ℕ × ℕ × (Fin 2 →₀ ℕ)
private def scalarPoly (e : Fin 2 →₀ ℕ) (g : (Polynomial SeedPoly)) : (Polynomial L) :=
  ⟨(AddMonoidAlgebra.coeff g).mapRange (fun p => p.coeff e) (by simp)⟩
@[simp] private theorem scalarPoly_coeff (e : Fin 2 →₀ ℕ) (g : (Polynomial SeedPoly)) (a : ℕ) :
    (scalarPoly e g).coeff a = (g.coeff a).coeff e := rfl
def sourceCoord (P : Source) (t : Position) : (Polynomial L) :=
  scalarPoly t.2.2 ((P.coeff t.1).coeff t.2.1)
def jetCoords : Jet →ₗ[FX] (Position → FX) :=
  LinearMap.pi fun t => {
    toFun P := ((P.coeff t.1).coeff t.2.1).coeff t.2.2
    map_add' P Q := by simp
    map_smul' r P := by simp }
theorem coords_center (P : Source) (t : Position) :
    jetCoords (centerEval P) t = algebraMap (Polynomial L) FX (sourceCoord P t) := by
  let ξ := algebraMap (Polynomial L) FX (Polynomial.X (R := L))
  let g := (P.coeff t.1).coeff t.2.1
  let e := t.2.2
  change (((centerEval P).coeff t.1).coeff t.2.1).coeff e = _
  simp only [centerEval, Polynomial.coeff_mapAlgHom_apply]
  change (g.eval₂ (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C ξ)).coeff e =
    (IsScalarTower.toAlgHom L (Polynomial L) FX) (scalarPoly e g)
  have hdeg : (scalarPoly e g).natDegree ≤ g.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro a ha
    simp [coeff_eq_zero_of_natDegree_lt ha]
  rw [← Polynomial.eval₂_algebraMap_X (scalarPoly e g) (IsScalarTower.toAlgHom L (Polynomial L) FX),
    Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hdeg), Polynomial.eval₂_eq_sum_range]
  simp only [MvPolynomial.coeff_sum, scalarPoly_coeff]
  apply Finset.sum_congr rfl
  intro a _
  rw [← map_pow, mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm]
  rfl
private def coeffLin (j i a : ℕ) (e : Fin 2 →₀ ℕ) : Source →ₗ[L] L where
  toFun P := coeffAt P j i a e
  map_add' P Q := by simp [coeffAt]
  map_smul' r P := by simp [coeffAt]
private theorem source_ext {P Q : Source}
    (heq : ∀ j i a e, coeffAt P j i a e = coeffAt Q j i a e) : P = Q :=
  Polynomial.ext fun j => Polynomial.ext fun i => Polynomial.ext fun a =>
    MvPolynomial.ext _ _ fun e => heq j i a e
private theorem seed_exp_le (e : Fin 2 →₀ ℕ) (k : Fin 2) : e k ≤ seedWeight e := by
  rw [seedWeight, Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (e i)) (Finset.mem_univ k)
instance completeFinite {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) : Module.Finite L (complete Crt word s W) := by
  classical
  let A := W + (s.B+s.J)*(2*h) + s.J
  let T := Fin (s.J+1) × Fin (s.B+1) × Fin (A+1) × (Fin 2 → Fin (s.U+1))
  let f : complete Crt word s W →ₗ[L] (T → L) :=
    LinearMap.pi fun t => (coeffLin t.1 t.2.1 t.2.2.1
      (Finsupp.equivFunOnFinite.symm fun k => (t.2.2.2 k : ℕ))).comp
      (complete Crt word s W).subtype
  apply Module.Finite.of_injective f
  intro P Q hPQ
  apply Subtype.ext
  apply source_ext
  intro j i a e
  by_cases he : trueEligible h s W j i a e
  · obtain ⟨hB, hJ, hU, hA⟩ := he
    let t : T := ⟨⟨j, by omega⟩, ⟨i, by omega⟩, ⟨a, by dsimp [A]; omega⟩,
      fun k => ⟨e k, Nat.lt_succ_of_le ((seed_exp_le e k).trans hU)⟩⟩
    have ht := congrFun hPQ t
    change coeffAt (P : Source) j i a (Finsupp.equivFunOnFinite.symm (e : Fin 2 → ℕ)) =
      coeffAt (Q : Source) j i a (Finsupp.equivFunOnFinite.symm (e : Fin 2 → ℕ)) at ht
    simpa only [Finsupp.equivFunOnFinite_symm_coe] using ht
  · exact (P.property.1.1 j i a e he).trans (Q.property.1.1 j i a e he).symm
private instance evaluatedFinite {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) : Module.Finite FX (evaluated Crt word s W) := by
  change Module.Finite FX
    (Submodule.span FX ((complete Crt word s W).map centerEval.toLinearMap : Set Jet))
  exact Module.Finite.of_fg ((Module.Finite.iff_fg.mp inferInstance).span (A := FX))
def boundaryDegree (h : ℕ) (s : Shape) (W : ℕ) (t : Position) : ℕ :=
  W + (s.B+s.J)*(2*h) + t.1 - (t.2.1+t.1)*(131071+h)
def boundaryMap {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) : complete Crt word s W →ₗ[L] (Position → L) :=
  LinearMap.pi fun t =>
    (coeffLin t.1 t.2.1 (boundaryDegree h s W t) t.2.2).comp (complete Crt word s W).subtype
theorem sourceCoord_degree {h} {D : PoleData h} {Crt : CRTLift D} {word : I → L}
    {s W} (P : complete Crt word s W) (t : Position) :
    (sourceCoord (P : Source) t).natDegree ≤ boundaryDegree h s W t := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro a ha
  change coeffAt (P : Source) t.1 t.2.1 a t.2.2 = 0
  apply P.property.1.1
  intro he
  have hw := he.2.2.2
  unfold boundaryDegree at ha
  omega
theorem independent_at_fraction {ι σ : Type*} [Fintype ι]
    (v : ι → σ → (Polynomial L)) (d : σ → ℕ) (hd : ∀ k t, (v k t).natDegree ≤ d t)
    (hli : LinearIndependent L (fun k t => (v k t).coeff (d t))) :
    LinearIndependent FX (fun k t => algebraMap (Polynomial L) FX (v k t)) := by
  classical
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite ((Polynomial L))⁰ c
  choose f hf using hb
  let n := Finset.univ.sup fun k => (f k).natDegree
  have hn (k : ι) : (f k).natDegree ≤ n :=
    Finset.le_sup (f := fun k => (f k).natDegree) (Finset.mem_univ k)
  have hinj := IsFractionRing.injective (Polynomial L) FX
  have hsum (t : σ) : ∑ k, f k * v k t = 0 := by
    apply hinj
    rw [map_sum, map_zero]
    simp only [map_mul, hf, Algebra.smul_def, mul_assoc, ← Finset.mul_sum]
    have ht := congrFun hc t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ht
    rw [ht, mul_zero]
  have hlead : ∑ k, (f k).coeff n • (fun t => (v k t).coeff (d t)) = 0 := by
    funext t
    simpa only [Polynomial.finsetSum_coeff, coeff_mul_add_eq_of_natDegree_le (hn _) (hd _ _),
      coeff_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      congrArg (fun Q : (Polynomial L) => Q.coeff (n+d t)) (hsum t)
  have hzero := hli _ hlead
  have hfn (k : ι) : f k = 0 := by
    by_contra hk
    have hlt : (f k).natDegree < n :=
      lt_of_le_of_ne (hn k) (fun he => hk (leadingCoeff_eq_zero.mp (by
        rw [← coeff_natDegree, he, hzero])))
    have hn0 : n ≠ 0 := by omega
    have hprev : n ≤ n - 1 := Finset.sup_le fun k' _ => by
      have hbd := hn k'
      by_cases hq : f k' = 0
      · simp [hq]
      · have hne : (f k').natDegree ≠ n := fun he =>
          hq (leadingCoeff_eq_zero.mp (by rw [← coeff_natDegree, he, hzero]))
        omega
    omega
  intro k
  have hk := hf k
  rw [hfn k, map_zero, Algebra.smul_def] at hk
  have hb0 : algebraMap (Polynomial L) FX (b : (Polynomial L)) ≠ 0 :=
    fun hz => nonZeroDivisors.coe_ne_zero b (hinj (hz.trans (map_zero _).symm))
  exact (mul_eq_zero.mp hk.symm).resolve_left hb0
theorem boundary_rank_le {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) :
    Module.finrank L (boundaryMap Crt word s W).range ≤
      Module.finrank FX (evaluated Crt word s W) := by
  classical
  let F := boundaryMap Crt word s W
  let b := Module.finBasis L F.range
  have hex (k : Fin (Module.finrank L F.range)) :
      ∃ P : complete Crt word s W, F P = (b k : Position → L) := (b k).property
  choose P hP using hex
  have hli : LinearIndependent L (fun k t =>
      (sourceCoord (P k : Source) t).coeff (boundaryDegree h s W t)) := by
    change LinearIndependent L (F ∘ P)
    have heq : F ∘ P = fun k => ((b k : F.range) : Position → L) := funext hP
    rw [heq]
    exact b.linearIndependent.map' F.range.subtype F.range.ker_subtype
  have heval : LinearIndependent FX (fun k => centerEval (P k : Source)) := by
    apply LinearIndependent.of_comp jetCoords
    have hf : jetCoords ∘ (fun k => centerEval (P k : Source)) =
        fun k t => algebraMap (Polynomial L) FX (sourceCoord (P k : Source) t) :=
      funext fun k => funext fun t => coords_center (P k : Source) t
    rw [hf]
    exact independent_at_fraction (fun k => sourceCoord (P k : Source))
        (boundaryDegree h s W) (fun k => sourceCoord_degree (P k)) hli
  let u (k : Fin (Module.finrank L F.range)) : evaluated Crt word s W :=
    ⟨centerEval (P k : Source), Submodule.subset_span ⟨_, (P k).property, rfl⟩⟩
  have hu : LinearIndependent FX u :=
    LinearIndependent.of_comp (evaluated Crt word s W).subtype heval
  simpa [F] using hu.fintype_card_le_finrank
theorem strict_of_ker {h} {D : PoleData h} {Crt : CRTLift D} {word : I → L} {s W}
    (P : (boundaryMap Crt word s W).ker) {j i a e} (hn : coeffAt (P.1 : Source) j i a e ≠ 0) :
    a+(i+j)*(131071+h) < W+(s.B+s.J)*(2*h)+j := by
  have he : trueEligible h s W j i a e := by
    by_contra hh
    exact hn (P.1.property.1.1 j i a e hh)
  have hw := he.2.2.2
  by_contra hlt
  have ha : a = boundaryDegree h s W (j,i,e) := by
    unfold boundaryDegree
    dsimp
    omega
  exact hn (by rw [ha]; exact congrFun (LinearMap.mem_ker.mp P.property) (j,i,e))
theorem ker_step_le {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) : Module.finrank L (boundaryMap Crt word s (W+1)).ker ≤
      Module.finrank L (complete Crt word s W) := by
  let F := boundaryMap Crt word s (W+1)
  have hm (P : F.ker) : (P.1 : Source) ∈ complete Crt word s W := by
    refine ⟨⟨?_, P.1.property.1.2⟩, P.1.property.2⟩
    intro j i a e hb
    by_contra hn
    have he : trueEligible h s (W+1) j i a e := by
      by_contra hh
      exact hn (P.1.property.1.1 j i a e hh)
    have hl := strict_of_ker P hn
    exact hb ⟨he.1, he.2.1, he.2.2.1, by omega⟩
  let f := ((complete Crt word s (W+1)).subtype.comp F.ker.subtype).codRestrict
    (complete Crt word s W) hm
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  intro P Q he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : complete Crt word s W => (x : Source)) he
end
end K1_14_1_8
end
section
namespace K1_14_1_1
noncomputable section
open K1_14 K1_14_1 Module Polynomial
open scoped Polynomial
def quotientBasis {R : Type*} [CommRing R] {b : (Polynomial R)} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) : Basis (Fin n) R (AdjoinRoot b) :=
  (AdjoinRoot.powerBasisAux' hb).reindex (finCongr hd)
def mulMatrix {R : Type*} [CommRing R] {b : (Polynomial R)} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) (a : (Polynomial R)) : Matrix (Fin n) (Fin n) R :=
  Algebra.leftMulMatrix (quotientBasis hb hd) (AdjoinRoot.mk b a)
theorem mulMatrix_entry {R : Type*} [CommRing R] {b : (Polynomial R)} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) (a : (Polynomial R)) (i j : Fin n) :
    mulMatrix hb hd a i j = ((a * Polynomial.X (R := R) ^ (j : ℕ)) %ₘ b).coeff i := by
  have hpow (k : Fin b.natDegree) :
      (AdjoinRoot.powerBasisAux' hb) k = AdjoinRoot.root b ^ (k : ℕ) :=
    (AdjoinRoot.powerBasis' hb).basis_eq_pow k
  unfold mulMatrix
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  unfold quotientBasis
  rw [Basis.reindex_apply, hpow, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul,
    Basis.repr_reindex_apply, AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk]
  rfl
theorem mulMatrix_specialize {R S : Type*} [CommRing R] [CommRing S]
    {b a : (Polynomial R)} {b' a' : (Polynomial S)} {n : ℕ} (f : R →+* S)
    (hb : b.Monic) (hd : b.natDegree = n) (hb' : b'.Monic) (hd' : b'.natDegree = n)
    (hmapb : b.map f = b') (hmapa : a.map f = a') :
    f (mulMatrix hb hd a).det = (mulMatrix hb' hd' a').det := by
  rw [f.map_det]
  congr 1
  ext i j
  change f (mulMatrix hb hd a i j) = mulMatrix hb' hd' a' i j
  rw [mulMatrix_entry, mulMatrix_entry, ← Polynomial.coeff_map, Polynomial.map_modByMonic f hb,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, hmapa, hmapb]
theorem mulMatrix_det_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    {b a : (Polynomial R)} {n : ℕ} (hb : b.Monic) (hd : b.natDegree = n)
    (hcop : IsCoprime a b) : (mulMatrix hb hd a).det ≠ 0 := by
  obtain ⟨u, v, huv⟩ := hcop
  have hinv : AdjoinRoot.mk b u * AdjoinRoot.mk b a = 1 := by
    have h := congrArg (AdjoinRoot.mk b) huv
    simpa only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero, map_one] using h
  have hmat : mulMatrix hb hd u * mulMatrix hb hd a = 1 := by
    unfold mulMatrix
    rw [← map_mul, hinv, map_one]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  intro hz
  rw [hz, mul_zero] at hdet
  exact zero_ne_one hdet
private theorem clearedSolution {R : Type*} [CommRing R] [Nontrivial R]
    {b : (Polynomial R)} {n : ℕ} (hb : b.Monic) (hd : b.natDegree = n) (a q : (Polynomial R)) :
    ∃ t : (Polynomial R), t.degree < b.degree ∧ b ∣ a * t + C (mulMatrix hb hd a).det * q := by
  let basis := quotientBasis hb hd
  let matrix := mulMatrix hb hd a
  let target := AdjoinRoot.mk b (-q)
  let solution := basis.equivFun.symm (matrix.cramer (basis.equivFun target))
  have hcoord : basis.equivFun solution = matrix.cramer (basis.equivFun target) :=
    basis.equivFun.apply_symm_apply _
  have hsol : AdjoinRoot.mk b a * solution = matrix.det • target := by
    apply basis.equivFun.injective
    have hvec := Algebra.leftMulMatrix_mulVec_repr basis (AdjoinRoot.mk b a) solution
    change matrix.mulVec (basis.repr solution) = ⇑(basis.repr (AdjoinRoot.mk b a * solution)) at hvec
    rw [← Basis.equivFun_apply, ← Basis.equivFun_apply, hcoord, Matrix.mulVec_cramer] at hvec
    rw [map_smul]
    exact hvec.symm
  obtain ⟨t, ht⟩ := AdjoinRoot.mk_surjective solution
  have hrep : AdjoinRoot.mk b (t %ₘ b) = solution := by
    rw [← AdjoinRoot.modByMonicHom_mk hb, AdjoinRoot.mk_leftInverse hb, ht]
  refine ⟨t %ₘ b, degree_modByMonic_lt _ hb, AdjoinRoot.mk_eq_zero.mp ?_⟩
  change AdjoinRoot.mk b (a * (t %ₘ b) + C matrix.det * q) = 0
  rw [map_add, map_mul, map_mul, hrep, hsol, AdjoinRoot.mk_C]
  simp [target, Algebra.smul_def]
theorem eval_map_constants {F : Type*} [Field F] (z : F) (g : (Polynomial F)) :
    (g.map (C : F →+* (Polynomial F))).map (evalRingHom z) = g := by
  have hc : (evalRingHom z).comp (C : F →+* (Polynomial F)) = RingHom.id F :=
    RingHom.ext fun x => eval_C
  rw [Polynomial.map_map, hc, Polynomial.map_id]
theorem blockContribution {h : ℕ} (D : PoleData h) (i : Fin 2) :
    ∃ (d : (Polynomial L)) (N : Polynomial (Polynomial L)),
      d ≠ 0 ∧ N.degree < (2 * h : ℕ) ∧
      (D.block (otherBlock i)).map C ∣ N ∧
      (D.block i).map C ∣
        ((D.constant i).map C + C (Polynomial.X (R := L)) * (D.slope i).map C) * N +
          C (d * Polynomial.X (R := L)) * (D.offset i).map C ∧
      ∀ z, IsCoprime (D.constant i + C z * D.slope i) (D.block i) → d.eval z ≠ 0 := by
  let b := (D.block i).map (C : L →+* (Polynomial L))
  let e := (D.block (otherBlock i)).map (C : L →+* (Polynomial L))
  let amplitude := (D.constant i).map (C : L →+* (Polynomial L)) +
    C (Polynomial.X (R := L)) * (D.slope i).map (C : L →+* (Polynomial L))
  let a := amplitude * e
  let q := C (Polynomial.X (R := L)) * (D.offset i).map (C : L →+* (Polynomial L))
  have hb : b.Monic := (D.monic i).map _
  have he : e.Monic := (D.monic (otherBlock i)).map _
  have hbd : b.natDegree = h := ((D.monic i).natDegree_map _).trans (D.degree i)
  have hed : e.natDegree = h :=
    ((D.monic (otherBlock i)).natDegree_map _).trans (D.degree (otherBlock i))
  have hcop : IsCoprime (D.block (otherBlock i)) (D.block i) := by
    fin_cases i
    · exact D.coprime.symm
    · exact D.coprime
  let d := (mulMatrix hb hbd a).det
  have hregular (z : L) (hz : IsCoprime (D.constant i + C z * D.slope i) (D.block i)) :
      d.eval z ≠ 0 := by
    have hmapa : a.map (evalRingHom z) =
        (D.constant i + C z * D.slope i) * D.block (otherBlock i) := by
      simp only [a, amplitude, e, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        eval_map_constants, coe_evalRingHom, eval_X]
    change (evalRingHom z) (mulMatrix hb hbd a).det ≠ 0
    rw [mulMatrix_specialize (evalRingHom z) hb hbd (D.monic i) (D.degree i)
      (eval_map_constants z (D.block i)) hmapa]
    exact mulMatrix_det_ne_zero _ _ (hz.mul_left hcop)
  have hd : d ≠ 0 := by
    have hc : IsCoprime (D.constant i) (D.block i) := (D.determinant i).of_mul_left_right
    intro hd
    exact hregular 0 (by simpa using hc) (by simp [hd])
  obtain ⟨t, ht, hdiv⟩ := clearedSolution hb hbd a q
  refine ⟨d, e * t, hd, ?_, dvd_mul_right _ _, ?_, hregular⟩
  · by_cases ht0 : t = 0
    · rw [ht0, mul_zero, degree_zero]
      exact WithBot.bot_lt_coe _
    have htn : t.natDegree < h := by
      rw [degree_eq_natDegree ht0, degree_eq_natDegree hb.ne_zero, hbd, Nat.cast_lt] at ht
      exact ht
    apply (degree_mul_le e t).trans_lt
    rw [degree_eq_natDegree he.ne_zero, degree_eq_natDegree ht0, hed, ← Nat.cast_add, Nat.cast_lt]
    omega
  · change b ∣ amplitude * (e * t) + C (d * Polynomial.X (R := L)) * (D.offset i).map C
    simpa only [a, q, ← mul_assoc, ← map_mul] using hdiv
end
end K1_14_1_1
end
section
namespace K1_14_1_3_2
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_3 Polynomial
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxHeartbeats 1000000
private def jetHom {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y v : B) : Polynomial (Polynomial A) →+* B :=
  eval₂RingHom (eval₂RingHom base y) v
@[simp] private theorem jetHom_base {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y v : B) (a : A) :
    jetHom base y v (C (C a)) = base a := by
  simp [jetHom]
@[simp] private theorem jetHom_y {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y v : B) :
    jetHom base y v (C Polynomial.X) = y := by
  simp [jetHom]
@[simp] private theorem jetHom_v {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y v : B) :
    jetHom base y v Polynomial.X = v := by
  simp [jetHom]
private abbrev rawY : RawSource := C (Polynomial.X (R := Abscissa))
private abbrev rawV : RawSource := Polynomial.X
private abbrev rawC : Abscissa →+* RawSource := jetConstant
private abbrev rawSeriesC : PowerSeries Abscissa →+* PowerSeries RawSource :=
  PowerSeries.map rawC
private theorem forward_def {h : ℕ} {D : PoleData h} (Crt : CRTLift D) :
    (forward Crt).toRingHom = jetHom (rawC.comp genericCoefficients.toRingHom)
      (rawC (rawBlock D) * rawY + rawC (crtPolynomial Crt))
      (rawC (rawBlock D) * rawV + rawC (rawBlock D).derivative * rawY +
        rawC (crtPolynomial Crt).derivative) :=
  rfl
private theorem forward_base {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (P : (Polynomial SeedPoly)) :
    forward Crt (C (C P)) = rawC (genericCoefficients P) := by
  change (forward Crt).toRingHom (C (C P)) = _
  rw [forward_def, jetHom_base, RingHom.comp_apply]
  rfl
private theorem forward_seed {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (a : SeedPoly) :
    (forward Crt).toRingHom (C (C (C a))) = rawC (C (algebraMap SeedPoly SeedField a)) := by
  change forward Crt _ = _
  rw [forward_base]
  change rawC ((C a).map (algebraMap SeedPoly SeedField)) = _
  rw [Polynomial.map_C]
private def rawShift (i : Fin 2) (E : Abscissa) (B B₁ : PowerSeries Abscissa) :
    RawSource →+* PowerSeries RawSource :=
  jetHom (rawSeriesC.comp (scaledShift i E))
    (PowerSeries.C rawY - rawSeriesC (PowerSeries.C E * B))
    (PowerSeries.C rawV + rawSeriesC (PowerSeries.C E.derivative * B - PowerSeries.C E * B₁))
private theorem rawShift_y (i : Fin 2) (E : Abscissa) (B B₁ : PowerSeries Abscissa) :
    rawShift i E B B₁ rawY = PowerSeries.C rawY - rawSeriesC (PowerSeries.C E * B) :=
  jetHom_y _ _ _
private theorem rawShift_v (i : Fin 2) (E : Abscissa) (B B₁ : PowerSeries Abscissa) :
    rawShift i E B B₁ rawV =
      PowerSeries.C rawV + rawSeriesC (PowerSeries.C E.derivative * B - PowerSeries.C E * B₁) :=
  jetHom_v _ _ _
private theorem rawShift_constants (i : Fin 2) (E : Abscissa) (B B₁ : PowerSeries Abscissa)
    (P : Abscissa) (hP : scaledShift i E P = PowerSeries.C P) :
    rawShift i E B B₁ (rawC P) = PowerSeries.C (rawC P) := by
  change rawShift i E B B₁ (C (C P)) = _
  simp [rawShift, hP]
private theorem cancel_ordinate {R : Type*} [CommRing R] (H E T l B : R) :
    H * (T - E * B) + (l + H * E * B) = H * T + l := by ring
private theorem cancel_velocity {R : Type*} [CommRing R] (H H' E E' T V l B B₁ : R) :
    H * (V + (E' * B - E * B₁)) + H' * (T - E * B) +
      (l + (H' * E - H * E') * B + H * E * B₁) = H * V + H' * T + l := by ring
private theorem forward_shift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i : Fin 2)
    (B B₁ : PowerSeries Abscissa)
    (hY : scaledShift i (basePolynomial (D.block i)) (crtPolynomial Crt) =
      PowerSeries.C (crtPolynomial Crt) + PowerSeries.C (rawBlock D) *
        PowerSeries.C (basePolynomial (D.block i)) * B)
    (hV : scaledShift i (basePolynomial (D.block i)) (crtPolynomial Crt).derivative =
      PowerSeries.C (crtPolynomial Crt).derivative +
        (PowerSeries.C (rawBlock D).derivative * PowerSeries.C (basePolynomial (D.block i)) -
          PowerSeries.C (rawBlock D) * PowerSeries.C (basePolynomial (D.block i)).derivative) * B +
        PowerSeries.C (rawBlock D) * PowerSeries.C (basePolynomial (D.block i)) * B₁) :
    let E := basePolynomial (D.block i)
    (rawShift i E B B₁).comp (forward Crt).toRingHom =
      (PowerSeries.rescale (rawC (E^2))).comp
        ((PowerSeries.map (forward Crt).toRingHom).comp (sourceShift i)) := by
  let E := basePolynomial (D.block i)
  let F := (forward Crt).toRingHom
  let Φ := rawShift i E B B₁
  let S := PowerSeries.rescale (rawC (E^2))
  have hH : scaledShift i E (rawBlock D) = PowerSeries.C (rawBlock D) :=
    scaledShift_base i E (poleProduct D)
  have hH' : scaledShift i E (rawBlock D).derivative = PowerSeries.C (rawBlock D).derivative :=
    scaledShift_base_derivative i E (poleProduct D)
  have hbase (P : Abscissa) (hp : scaledShift i E P = PowerSeries.C P) :
      Φ (rawC P) = PowerSeries.C (rawC P) := rawShift_constants _ _ _ _ _ hp
  change Φ.comp F = S.comp ((PowerSeries.map F).comp (sourceShift i))
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a
        change Φ (F (C (C (C a)))) = S (PowerSeries.map F (sourceShift i (C (C (C a)))))
        rw [show F (C (C (C a))) = _ from forward_seed Crt a]
        change rawShift i E B B₁ (C (C (C (algebraMap SeedPoly SeedField a)))) = _
        apply PowerSeries.ext
        intro n
        simp only [rawShift, jetHom_base, RingHom.comp_apply, scaledShift, seriesPolynomial_C,
          seedShift_algebraMap, genericSeedShift, sourceShift, S, PowerSeries.coeff_rescale,
          PowerSeries.coeff_map, F, forward_seed, map_mul, map_pow]
      · change Φ (F (C (C Polynomial.X))) = S (PowerSeries.map F (sourceShift i (C (C Polynomial.X))))
        rw [show F (C (C Polynomial.X)) = rawC Polynomial.X from
          (forward_base Crt _).trans (congrArg rawC (Polynomial.map_X _))]
        simp only [sourceShift, seriesPolynomial_C, seriesPolynomial_X, PowerSeries.map_C]
        change Φ (rawC Polynomial.X) = S (PowerSeries.C (F (C (C Polynomial.X))))
        rw [show F (C (C Polynomial.X)) = rawC Polynomial.X from
          (forward_base Crt _).trans (congrArg rawC (Polynomial.map_X _)), rescale_C]
        exact hbase _ (by simp [scaledShift, rescale_C])
    · change Φ (F (C Polynomial.X)) = S (PowerSeries.map F (sourceShift i (C Polynomial.X)))
      simp only [sourceShift, seriesPolynomial_C, seriesPolynomial_X, PowerSeries.map_C, S,
        rescale_C]
      change Φ (F (C Polynomial.X)) = PowerSeries.C (F (C Polynomial.X))
      simp only [F, forward_def, jetHom_y, map_add, map_mul, hbase _ hH]
      change scaledShift i E _ = _ at hY
      have he : Φ (rawC (crtPolynomial Crt)) =
          rawSeriesC (scaledShift i E (crtPolynomial Crt)) :=
        jetHom_base _ _ _ _
      rw [he, hY, show Φ rawY = _ from rawShift_y i E B B₁]
      simp only [map_add, map_mul, PowerSeries.map_C]
      exact cancel_ordinate _ _ _ _ _
  · change Φ (F Polynomial.X) = S (PowerSeries.map F (sourceShift i Polynomial.X))
    simp only [sourceShift, seriesPolynomial_X, PowerSeries.map_C, S, rescale_C]
    simp only [F, forward_def, jetHom_v, map_add, map_mul, hbase _ hH, hbase _ hH']
    change scaledShift i E _ = _ at hV
    have he : Φ (rawC (crtPolynomial Crt).derivative) =
        rawSeriesC (scaledShift i E (crtPolynomial Crt).derivative) :=
      jetHom_base _ _ _ _
    rw [he, hV, show Φ rawV = _ from rawShift_v i E B B₁,
      show Φ rawY = _ from rawShift_y i E B B₁]
    simp only [map_add, map_mul, map_sub, PowerSeries.map_C]
    exact cancel_velocity _ _ _ _ _ _ _ _ _
private theorem generic_sourceX (P : (Polynomial L)) :
    genericCoefficients (sourceX P) = basePolynomial P := by
  change (P.map MvPolynomial.C).map (algebraMap SeedPoly SeedField) =
    P.map (algebraMap L SeedField)
  rw [Polynomial.map_map]
  have h : (algebraMap SeedPoly SeedField).comp (MvPolynomial.C : L →+* SeedPoly) =
      algebraMap L SeedField := by
    apply RingHom.ext
    intro a
    rw [RingHom.comp_apply, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [h]
theorem proof : K1_14_1_3.c2 := by
  intro h D Crt s Q hQ i r
  let E := basePolynomial (D.block i)
  let H := rawBlock D
  let m := s.B + s.J
  obtain ⟨B, B₁, hY, hV⟩ := crt_corrections Crt i
  let Φ := rawShift i E B B₁
  have hcompat := RingHom.congr_fun (forward_shift Crt i B B₁ hY hV) Q
  have hr := congrArg (PowerSeries.coeff r) hcompat
  change PowerSeries.coeff r (Φ (forward Crt Q)) =
    PowerSeries.coeff r (PowerSeries.rescale (rawC (E^2))
      (PowerSeries.map (forward Crt).toRingHom (sourceShift i Q))) at hr
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map, sourceShift_coeff] at hr
  have hrow : forward Crt (cleared D i r Q) =
      (rawC (E^2)) ^ r * forward Crt (sourceHasse i r Q) := by
    rw [cleared, map_mul]
    change forward Crt (C (C (sourceX (D.block i ^ (2*r))))) * _ = _
    rw [forward_base, generic_sourceX, basePolynomial, Polynomial.map_pow, pow_mul, map_pow]
    rfl
  change rawC (H^m) ∣ forward Crt Q at hQ
  obtain ⟨W, hW⟩ := hQ
  have hfix : Φ (rawC (H^m)) = PowerSeries.C (rawC (H^m)) := by
    apply rawShift_constants
    rw [map_pow, show scaledShift i E H = PowerSeries.C H from
      scaledShift_base i E (poleProduct D), map_pow]
  rw [hW, map_mul, hfix, PowerSeries.coeff_C_mul] at hr
  change rawC (H^m) ∣ forward Crt (cleared D i r Q)
  exact ⟨PowerSeries.coeff r (Φ W), hrow.trans hr.symm⟩
end
end K1_14_1_3_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2_1
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 K1_14_1_7_2 Polynomial
open scoped BigOperators Polynomial
private theorem substitute_fixed_velocity {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (y : (Polynomial S)) :
    substitute (jetConstant.comp f) (C y) Polynomial.X =
      Polynomial.mapRingHom (Polynomial.eval₂RingHom (C.comp f) y) := by
  apply jetHom_ext
  · intro a
    rw [substitute_base]
    simp [jetConstant]
  · simp
  · simp
private theorem centered_row {F : Type} [Field F] (α : F) (z : SeedFrac F)
    (P : TrueSource F) (j : ℕ) :
    let f := (Polynomial.taylorAlgHom (algebraMap F (SeedFrac F) α)).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap (Seed F) (SeedFrac F)))
    ((centered α z P).coeff j) =
      Polynomial.eval₂RingHom (C.comp f) (Polynomial.X + C (C z)) (P.coeff j) := by
  dsimp only
  unfold centered
  rw [show (C Polynomial.X + jetConstant (C z) : JetPolys (SeedFrac F)) =
    C (Polynomial.X + C (C z)) by simp [jetConstant], substitute_fixed_velocity,
    coe_mapRingHom, Polynomial.coeff_map]
private theorem source_slot_eq_zero {F : Type} [Field F] {s : Shape}
    {P : TrueSource F} (hP : Shaped s P) {i j : ℕ}
    (h : ¬ (i + j ≤ s.B ∧ j ≤ s.J)) : (P.coeff j).coeff i = 0 := by
  apply Polynomial.ext
  intro a
  rw [Polynomial.coeff_zero]
  apply MvPolynomial.ext
  intro e
  change sourceCoeff P j i a e = 0
  by_contra hn
  exact h ⟨(hP j i a e hn).1, (hP j i a e hn).2.1⟩
private theorem centered_coeff_sum {F : Type} [Field F] (α : F) (z : SeedFrac F)
    (P : TrueSource F) (i j N : ℕ) (hN : (P.coeff j).natDegree < N) :
    ((centered α z P).coeff j).coeff i =
      ∑ n ∈ Finset.range N,
        C ((n.choose i : SeedFrac F) * z ^ (n - i)) *
          (inputTaylor α P j n).map (algebraMap (Seed F) (SeedFrac F)) := by
  rw [centered_row]
  conv_lhs => rw [(P.coeff j).as_sum_range_C_mul_X_pow' hN]
  simp only [coe_eval₂RingHom, eval₂_finsetSum, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    finsetSum_coeff, coeff_C_mul, coeff_X_add_C_pow, RingHom.comp_apply, coe_mapRingHom]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hc : algebraMap (Seed F) (SeedFrac F) (algebraMap F (Seed F) α) =
      algebraMap F (SeedFrac F) α :=
    (IsScalarTower.algebraMap_apply F (Seed F) (SeedFrac F) α).symm
  rw [inputTaylor, map_taylor, hc, ← (C (R := SeedFrac F)).map_pow,
    ← map_natCast (C (R := SeedFrac F)), ← map_mul (C (R := SeedFrac F)),
    mul_comm (z ^ (n - i)), mul_comm]
  rfl
private theorem pack_coeff_term {R : Type} [CommSemiring R] {s : Shape}
    (f : (q : Grade s) → GradeSlot s q.val → (Polynomial R)) (q : Grade s)
    (k : GradeSlot s q.val) (i j : ℕ) :
    ((C (C (f q k) * Polynomial.X ^ (q.val - k.val)) * Polynomial.X ^ k.val).coeff j).coeff i =
      if j = k.val ∧ i + j = q.val then f q k else 0 := by
  have hk : k.val ≤ q.val := (Nat.lt_succ_iff.mp k.isLt).trans (min_le_left ..)
  by_cases hj : j = k.val
  · have hi : i = q.val - k.val ↔ i + j = q.val := by omega
    simp only [coeff_C_mul_X_pow, hj, ite_true, true_and, hi]
  · simp only [coeff_C_mul_X_pow, hj, ite_false, false_and, Polynomial.coeff_zero]
private theorem pack_coeff {R : Type} [CommSemiring R] (s : Shape)
    (f : (q : Grade s) → GradeSlot s q.val → (Polynomial R)) (i j : ℕ)
    (hq : i + j ≤ s.B) (hj : j ≤ s.J) :
    ((packGrades s f).coeff j).coeff i =
      f ⟨i + j, Nat.lt_succ_of_le hq⟩
        ⟨j, Nat.lt_succ_of_le (le_min (show j ≤ i + j by omega) hj)⟩ := by
  let q : Grade s := ⟨i + j, Nat.lt_succ_of_le hq⟩
  let k : GradeSlot s q.val := ⟨j, Nat.lt_succ_of_le (le_min (by dsimp [q]; omega) hj)⟩
  change _ = f q k
  simp only [packGrades, finsetSum_coeff, pack_coeff_term]
  rw [Finset.sum_eq_single_of_mem q (Finset.mem_univ q)]
  · rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
    · simp [q, k]
    · intro k' _ hne
      have hval : j ≠ k'.val := fun he => hne (Fin.ext he.symm)
      simp [hval]
  · intro q' _ hne
    have hval : i + j ≠ q'.val := fun he => hne (Fin.ext he.symm)
    simp [hval]
private theorem pack_coeff_eq_zero {R : Type} [CommSemiring R] (s : Shape)
    (f : (q : Grade s) → GradeSlot s q.val → (Polynomial R)) (i j : ℕ)
    (h : ¬ (i + j ≤ s.B ∧ j ≤ s.J)) :
    ((packGrades s f).coeff j).coeff i = 0 := by
  simp only [packGrades, finsetSum_coeff, pack_coeff_term]
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun k _ => ?_
  have hq : q.val ≤ s.B := Nat.lt_succ_iff.mp q.isLt
  have hk : k.val ≤ s.J := (Nat.lt_succ_iff.mp k.isLt).trans (min_le_right ..)
  have hn : ¬ (j = k.val ∧ i + j = q.val) := by omega
  simp [hn]
theorem proof : K1_14_1_7_2.c1 := by
  intro F _ s α z P hP
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro i
  have hN : (P.coeff j).natDegree < s.B - j + 1 := by
    apply Nat.lt_succ_of_le
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    exact source_slot_eq_zero hP (by omega)
  by_cases h : i + j ≤ s.B ∧ j ≤ s.J
  · rcases h with ⟨hq, hj⟩
    rw [pack_coeff s _ i j hq hj]
    rw [centered_coeff_sum α z P i j (s.B - j + 1) hN]
    let term (n : ℕ) := C ((n.choose i : SeedFrac F) * z ^ (n - i)) *
      (inputTaylor α P j n).map (algebraMap (Seed F) (SeedFrac F))
    change (∑ n ∈ Finset.range (s.B - j + 1), term n) = _
    have hs := Finset.sum_range_add term i (s.B - (i + j) + 1)
    rw [show i + (s.B - (i + j) + 1) = s.B - j + 1 by omega] at hs
    have hzero : (∑ n ∈ Finset.range i, term n) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      simp [term, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hn)]
    rw [hs, hzero, zero_add]
    rw [← Fin.sum_univ_eq_sum_range (fun n => term (i + n)) (s.B - (i + j) + 1)]
    unfold localSlots
    refine Finset.sum_congr rfl fun n _ => ?_
    have hi : i + j - j = i := by omega
    simp only [term, inputOrdinate, hi, Nat.add_sub_cancel_left]
  · rw [pack_coeff_eq_zero s _ i j h]
    by_cases hj : j ≤ s.B ∧ j ≤ s.J
    · rw [centered_coeff_sum α z P i j (s.B - j + 1) hN]
      refine Finset.sum_eq_zero fun n hn => ?_
      have hn' := Finset.mem_range.mp hn
      simp [Nat.choose_eq_zero_of_lt (show n < i by omega)]
    · have hrow : P.coeff j = 0 := by
        exact Polynomial.ext fun n => (source_slot_eq_zero hP (by omega)).trans
          (Polynomial.coeff_zero n).symm
      rw [centered_row, hrow, map_zero, Polynomial.coeff_zero]
end
end K1_14_1_7_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_4
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
private abbrev Row := ℕ × ℕ × ℕ × Exponent
private def readRow {R : Type} [CommRing R] (Q : TrueSource R) (G : (Polynomial (Seed R)))
    (r : Row) : R :=
  ((((Q.coeff r.1).coeff r.2.1) %ₘ G).coeff r.2.2.1).coeff r.2.2.2
private def rowsOfColumn (Q : TrueSource Parameter) (G : (Polynomial (Seed Parameter))) :
    Finset Row :=
  Q.support.biUnion fun j => (Q.coeff j).support.biUnion fun i =>
    let p := (Q.coeff j).coeff i %ₘ G
    p.support.biUnion fun a => (p.coeff a).support.image fun e => (j, i, a, e)
private theorem mem_rowsOfColumn (Q : TrueSource Parameter) (G : (Polynomial (Seed Parameter)))
    (r : Row) (hr : readRow Q G r ≠ 0) : r ∈ rowsOfColumn Q G := by
  obtain ⟨j, i, a, e⟩ := r
  refine Finset.mem_biUnion.mpr ⟨j, Polynomial.mem_support_iff.mpr ?_, ?_⟩
  · intro h
    exact hr (by simp [readRow, h])
  refine Finset.mem_biUnion.mpr ⟨i, Polynomial.mem_support_iff.mpr ?_, ?_⟩
  · intro h
    exact hr (by simp [readRow, h])
  refine Finset.mem_biUnion.mpr ⟨a, Polynomial.mem_support_iff.mpr ?_, ?_⟩
  · intro h
    exact hr (by simp [readRow, h])
  exact Finset.mem_image.mpr ⟨e, MvPolynomial.mem_support_iff.mpr hr, rfl⟩
private theorem readRow_map {F : Type} [Field F] (point : Parameter →+* F)
    (Q : TrueSource Parameter) {G : (Polynomial (Seed Parameter))} (hG : G.Monic) (r : Row) :
    readRow (mapSource point Q) (G.map (MvPolynomial.map point)) r =
      point (readRow Q G r) := by
  simp only [readRow, mapSource, coe_mapRingHom, Polynomial.coeff_map,
    ← map_modByMonic (MvPolynomial.map point) hG, MvPolynomial.coeff_map]
private def readRowLinear {F : Type} [Field F] (G : (Polynomial (Seed F)))
    (r : Row) : TrueSource F →ₗ[F] F :=
  (MvPolynomial.lcoeff F r.2.2.2).comp <|
    ((Polynomial.lcoeff (Seed F) r.2.2.1).restrictScalars F).comp <|
    ((Polynomial.modByMonicHom G).restrictScalars F).comp <|
    ((Polynomial.lcoeff (Polynomial (Seed F)) r.2.1).restrictScalars F).comp <|
    (Polynomial.lcoeff (Polynomial ((Polynomial (Seed F)))) r.1).restrictScalars F
private theorem readRow_sum {F ι : Type} [Field F] [Fintype ι]
    (Q : ι → TrueSource F) (v : ι → F) (G : (Polynomial (Seed F))) (r : Row) :
    readRow (∑ k, v k • Q k) G r = ∑ k, v k * readRow (Q k) G r := by
  change readRowLinear G r (∑ k, v k • Q k) = ∑ k, v k • readRowLinear G r (Q k)
  simp only [map_sum, map_smul]
private theorem dvd_iff_read {F : Type} [Field F] (Q : TrueSource F)
    {G : (Polynomial (Seed F))} (hG : G.Monic) :
    (jetConstant (G.map (algebraMap (Seed F) (SeedFrac F))) : JetPolys (SeedFrac F)) ∣
      jetMap (algebraMap (Seed F) (SeedFrac F)) Q ↔
      ∀ r, readRow Q G r = 0 := by
  let f := algebraMap (Seed F) (SeedFrac F)
  have h : (jetConstant (G.map f) : JetPolys (SeedFrac F)) ∣ jetMap f Q ↔
      ∀ j i, (Q.coeff j).coeff i %ₘ G = 0 := by
    simp only [jetConstant, RingHom.comp_apply, C_dvd_iff_dvd_coeff,
      jetMap, coe_mapRingHom, Polynomial.coeff_map]
    apply forall_congr'
    intro j
    apply forall_congr'
    intro i
    rw [← modByMonic_eq_zero_iff_dvd (hG.map f), ← map_modByMonic f hG,
      Polynomial.map_eq_zero_iff (IsFractionRing.injective (Seed F) (SeedFrac F))]
  rw [h]
  constructor
  · intro hz r
    simp [readRow, hz]
  · intro hz j i
    apply Polynomial.ext
    intro a
    rw [Polynomial.coeff_zero]
    apply MvPolynomial.ext
    intro e
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact hz (j, i, a, e)
private theorem matrix_of_columns {ι : Type} [Fintype ι]
    (Q : ι → TrueSource Parameter) (G : (Polynomial (Seed Parameter))) (hG : G.Monic) :
    ∃ n : ℕ, ∃ M : Matrix (Fin n) ι Parameter,
      ∀ (F : Type) [Field F] (point : Parameter →+* F) (v : ι → F),
        (M.map point).mulVec v = 0 ↔
          (jetConstant (G.map (seedAt point)) : JetPolys (SeedFrac F)) ∣
            ∑ k, v k • jetMap (seedAt point) (Q k) := by
  classical
  let rows := Finset.univ.biUnion fun k => rowsOfColumn (Q k) G
  let e : Fin rows.card ≃ ↥rows := (Fintype.equivFinOfCardEq (Fintype.card_coe rows)).symm
  let M : Matrix (Fin rows.card) ι Parameter := fun r k => readRow (Q k) G (e r).val
  refine ⟨rows.card, M, ?_⟩
  intro F _ point v
  let inc := algebraMap (Seed F) (SeedFrac F)
  let incAlg : TrueSource F →ₐ[F] JetPolys (SeedFrac F) :=
    mapAlgHom (mapAlgHom (mapAlgHom (IsScalarTower.toAlgHom F (Seed F) (SeedFrac F))))
  let G' := G.map (MvPolynomial.map point)
  let Q' : ι → TrueSource F := fun k => mapSource point (Q k)
  let q := ∑ k, v k • Q' k
  have hcomp (k : ι) : incAlg (Q' k) = jetMap (seedAt point) (Q k) := by
    change jetMap inc (jetMap (MvPolynomial.map point) (Q k)) = _
    apply Polynomial.ext
    intro j
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro a
    simp only [jetMap, coe_mapRingHom, Polynomial.coeff_map, seedAt, inc, RingHom.comp_apply]
  have hq : jetMap inc q = ∑ k, v k • jetMap (seedAt point) (Q k) := by
    change incAlg (∑ k, v k • Q' k) = _
    simp only [map_sum, map_smul, hcomp]
  rw [← hq, ← Polynomial.map_map (MvPolynomial.map point) inc, dvd_iff_read q (hG.map _)]
  have hread (r : Row) : readRow q G' r = ∑ k, v k * point (readRow (Q k) G r) := by
    rw [readRow_sum]
    simp only [Q', G', readRow_map point _ hG]
  have heval (r : Fin rows.card) : ((M.map point).mulVec v) r = readRow q G' (e r).val := by
    rw [hread]
    change ∑ k, point (readRow (Q k) G (e r).val) * v k = _
    simp only [mul_comm]
  change (M.map point).mulVec v = 0 ↔ ∀ r, readRow q G' r = 0
  constructor
  · intro hv r
    by_cases hr : r ∈ rows
    · have he := congrFun hv (e.symm ⟨r, hr⟩)
      rw [heval] at he
      simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using he
    · rw [hread]
      apply Finset.sum_eq_zero
      intro k _
      have hz : readRow (Q k) G r = 0 := by
        by_contra hn
        exact hr (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, mem_rowsOfColumn _ _ _ hn⟩)
      rw [hz, map_zero, mul_zero]
  · intro hv
    funext r
    exact (heval r).trans (hv (e r).val)
theorem proof : K1_14_1_7.c4 := by
  classical
  intro h D Crt E s ι _ P hP
  let G := (E.H.map (MvPolynomial.C (σ := Fin 2))) ^ (s.B + s.J)
  obtain ⟨n, M, hM⟩ := matrix_of_columns (fun k => cleared s E.H E.num E.den (P k)) G
    ((E.monic.map _).pow _)
  have fibre {F : Type} [Field F] (point : Parameter →+* F)
      (hd : MvPolynomial.map point E.den ≠ 0) (v : ι → F) :
      (M.map point).mulVec v = 0 ↔
        PoleTest s (E.H.map point) (liftAt point E.num E.den)
          (Fintype.linearCombination F (fun k => mapSource (point.comp (Polynomial.C (R := L))) (P k)) v) := by
    let f := K1_14_1_7.forward (E.H.map point) (liftAt point E.num E.den)
    let d := scalarJet (seedAt point E.den)
    have hu : IsUnit d := by
      have hn : seedAt point E.den ≠ 0 := by
        intro hzero
        exact hd (IsFractionRing.injective (Seed F) (SeedFrac F) (hzero.trans (map_zero _).symm))
      exact (isUnit_iff_ne_zero.mpr hn).map (jetConstant.comp Polynomial.C)
    rw [hM F point v]
    simp only [cleared_specializes point s E.H E.num E.den hd _ (hP _)]
    have hsum : (∑ k, v k • (d ^ s.B * f (mapSource (point.comp (Polynomial.C (R := L))) (P k)))) =
        d ^ s.B * f (Fintype.linearCombination F
          (fun k => mapSource (point.comp (Polynomial.C (R := L))) (P k)) v) := by
      simp only [Fintype.linearCombination_apply, map_sum, map_smul, Finset.mul_sum,
        mul_smul_comm]
    have hG : G.map (seedAt point) =
        ((E.H.map point).map (algebraMap F (SeedFrac F))) ^ (s.B + s.J) := by
      simp only [G, Polynomial.map_pow, map_abscissa]
    rw [hsum, (hu.pow s.B).dvd_mul_left, hG]
    rfl
  refine ⟨n, M, ?_, fibre genericPoint E.genericDen⟩
  intro v
  have hpoint : specialPoint.comp (Polynomial.C (R := L)) = RingHom.id L := by
    ext a
    simp [specialPoint]
  have hmap (Q : Source) : mapSource (RingHom.id L) Q = Q := by
    apply Polynomial.ext
    intro j
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro a
    simp only [mapSource, coe_mapRingHom, Polynomial.coeff_map, MvPolynomial.map_id]
  simpa only [E.specialH, E.specialLift, hpoint, hmap] using fibre specialPoint E.specialDen v
end
end K1_14_1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2_2
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 K1_14_1_7_2 Polynomial
open scoped BigOperators Polynomial
private def slot {R : Type} [CommSemiring R] (a : (Polynomial R)) (i k : ℕ) : JetPolys R :=
  jetConstant a * (C (Polynomial.X (R := (Polynomial R)))) ^ i * Polynomial.X ^ k
private theorem pack_eq_sum {R : Type} [CommSemiring R] (s : Shape)
    (f : (q : Grade s) → GradeSlot s q.val → (Polynomial R)) :
    packGrades s f = ∑ q : Grade s, ∑ j : GradeSlot s q.val,
      slot (f q j) (q.val - j.val) j.val := by
  simp only [packGrades, slot, jetConstant, RingHom.comp_apply, map_mul, map_pow]
private theorem zeroSubst_slot {R : Type} [CommSemiring R] (a : (Polynomial R)) (i j : ℕ) :
    zeroSubst (slot a i j) = ∑ k ∈ Finset.range (j + 1),
      slot (a * C (j.choose k : R) * Polynomial.X ^ (i + k)) (i + (j - k)) k := by
  simp only [slot, map_mul, map_pow, zeroSubst, substitute_base,
    substitute_ordinate, substitute_velocity]
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_pow, pow_add, map_natCast]
  ac_rfl
private theorem sum_range_eq_slots {M : Type*} [AddCommMonoid M] {s : Shape} {q : ℕ}
    (j : GradeSlot s q) (g : ℕ → M) :
    (∑ k ∈ Finset.range (j.val + 1), g k) =
      ∑ k : GradeSlot s q, if k.val ≤ j.val then g k.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ j.val then g k else 0)]
  calc
    _ = ∑ k ∈ Finset.range (j.val + 1), (if k ≤ j.val then g k else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    _ = _ := by
      refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt j.isLt)) ?_
      intro k _ hk
      exact ite_eq_right (fun h => hk (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
private theorem zeroSubst_grade_slot {E : Type} [Field E] (s : Shape) (q : ℕ)
    (f : GradeSlot s q → (Polynomial E)) (j : GradeSlot s q) :
    zeroSubst (slot (f j) (q - j.val) j.val) =
      ∑ k : GradeSlot s q, if k.val ≤ j.val then
        slot (f j * C (j.val.choose k.val : E) * Polynomial.X ^ (q - j.val + k.val))
          (q - k.val) k.val else 0 := by
  rw [zeroSubst_slot, sum_range_eq_slots j]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : k.val ≤ j.val
  · have hj : j.val ≤ q := (Nat.le_of_lt_succ j.isLt).trans (min_le_left _ _)
    simp only [ite_eq_left h, show q - j.val + (j.val - k.val) = q - k.val by omega]
  · simp only [ite_eq_right h]
private theorem zeroSubst_packGrades {E : Type} [Field E] (s : Shape)
    (f : (q : Grade s) → GradeSlot s q.val → (Polynomial E)) :
    zeroSubst (packGrades s f) = packGrades s (fun q k => zeroGrade s q.val (f q) k) := by
  simp only [pack_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [zeroSubst_grade_slot s q.val (f q)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [zeroGrade, slot, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp
theorem proof : K1_14_1_7_2.c2 := by
  intro F _ s f h
  rw [zeroSubst_packGrades, pack_eq_sum]
  apply Finset.dvd_sum
  intro q _
  apply Finset.dvd_sum
  intro k _
  unfold slot
  have hc : (jetConstant (Polynomial.X ^ (s.B + s.J)) : JetPolys (SeedFrac F)) ∣
      jetConstant (zeroGrade s q.val (f q) k) :=
    _root_.map_dvd jetConstant (h q k)
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hc _) _
end
end K1_14_1_7_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_4
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial
private abbrev CentreField := FractionRing Seeds
private abbrev CentreJet := Polynomial (Polynomial CentreField)
def doubleMap {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) :
    Polynomial (Polynomial A) →+* Polynomial (Polynomial B) :=
  mapRingHom (mapRingHom f)
theorem map_substitute {A B C' : Type*} [CommSemiring A] [CommSemiring B]
    [CommSemiring C'] (f : A →+* B) (g : B →+* C') (y v : Polynomial (Polynomial B)) :
    (doubleMap g).comp (substitute f y v) =
      substitute (g.comp f) (doubleMap g y) (doubleMap g v) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro a
      simp [substitute, doubleMap, jetConstant]
    · simp [substitute]
  · simp
theorem substitute_map {A B C' : Type*} [CommSemiring A] [CommSemiring B]
    [CommSemiring C'] (f : A →+* B) (g : B →+* C') (y v : Polynomial (Polynomial C')) :
    (substitute g y v).comp (doubleMap f) = substitute (g.comp f) y v := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro a
      simp [substitute, doubleMap]
    · simp [substitute, doubleMap]
  · simp [doubleMap]
private def seedMap : SeedPoly →+* Seeds :=
  MvPolynomial.map (algebraMap L FX)
private abbrev ξ : FX := algebraMap (Polynomial L) FX (Polynomial.X : (Polynomial L))
def centerBase : (Polynomial SeedPoly) →+* Seeds :=
  eval₂RingHom seedMap (MvPolynomial.C ξ)
theorem centerEval_apply (P : Source) : centerEval P = doubleMap centerBase P := rfl
private def liftSeeds : SeedField →+* CentreField :=
  IsFractionRing.lift (g := (algebraMap Seeds CentreField).comp seedMap)
    ((IsFractionRing.injective Seeds CentreField).comp
      (MvPolynomial.map_injective (algebraMap L FX) (FaithfulSMul.algebraMap_injective L FX)))
def evalRaw : (Polynomial SeedField) →+* FractionRing Seeds :=
  eval₂RingHom liftSeeds (algebraMap FX CentreField ξ)
theorem evalRaw_generic :
    evalRaw.comp genericCoefficients.toRingHom = (algebraMap Seeds CentreField).comp centerBase := by
  apply Polynomial.ringHom_ext
  · intro a
    change evalRaw ((C a).map (algebraMap SeedPoly SeedField)) =
      algebraMap Seeds CentreField (centerBase (C a))
    simp [evalRaw, centerBase, liftSeeds]
  · change evalRaw ((Polynomial.X : (Polynomial SeedPoly)).map (algebraMap SeedPoly SeedField)) =
      algebraMap Seeds CentreField (centerBase Polynomial.X)
    simp only [Polynomial.map_X, evalRaw, centerBase, coe_eval₂RingHom, eval₂_X]
    rfl
theorem evalRaw_physical : evalRaw.comp (mapRingHom (algebraMap L SeedField)) =
    (algebraMap FX CentreField).comp (algebraMap (Polynomial L) FX) := by
  apply Polynomial.ringHom_ext
  · intro a
    change evalRaw ((C a).map (algebraMap L SeedField)) =
      algebraMap FX CentreField (algebraMap (Polynomial L) FX (C a))
    simp only [Polynomial.map_C, evalRaw, coe_eval₂RingHom, eval₂_C]
    change liftSeeds (algebraMap SeedPoly SeedField (MvPolynomial.C a)) = _
    simp only [liftSeeds, IsFractionRing.lift_algebraMap, RingHom.comp_apply, seedMap,
      MvPolynomial.map_C]
    rfl
  · change evalRaw ((Polynomial.X : (Polynomial L)).map (algebraMap L SeedField)) =
      algebraMap FX CentreField ξ
    simp [evalRaw]

theorem evalRaw_seed (i : Fin 2) :
    evalRaw (C (algebraMap SeedPoly SeedField (MvPolynomial.X i))) =
    algebraMap Seeds CentreField (MvPolynomial.X i) := by
  simp only [evalRaw,coe_eval₂RingHom,eval₂_C,liftSeeds,IsFractionRing.lift_algebraMap,
    RingHom.comp_apply,seedMap,MvPolynomial.map_X]

private theorem evalRaw_block {h} (D : PoleData h) :
    evalRaw (rawBlock D) = algebraMap FX CentreField (algebraMap (Polynomial L) FX (poleProduct D)) := by
  exact RingHom.congr_fun evalRaw_physical (poleProduct D)
theorem evalRaw_block_ne_zero {h} (D : PoleData h) : evalRaw (rawBlock D) ≠ 0 := by
  rw [evalRaw_block]
  have hne := ((IsFractionRing.injective (Polynomial L) FX).ne ((D.monic 0).mul (D.monic 1)).ne_zero)
  exact (map_ne_zero (algebraMap FX CentreField)).2 (by simpa only [poleProduct, map_zero] using hne)
def specialized {h} {D : PoleData h} (Crt : CRTLift D) : Jet →ₐ[FX] CentreJet where
  toRingHom := substitute (algebraMap Seeds CentreField)
    (doubleMap evalRaw (rawOrdinate D Crt)) (doubleMap evalRaw (rawVelocity D Crt))
  commutes' x := by
    change substitute _ _ _ (jetConstant (MvPolynomial.C x)) =
      jetConstant (algebraMap FX CentreField x)
    simp [substitute, jetConstant]
    rfl
theorem specialized_center {h} {D : PoleData h} (Crt : CRTLift D) (P : Source) :
    specialized Crt (centerEval P) = doubleMap evalRaw (forward Crt P) := by
  rw [centerEval_apply, forward_apply]
  change ((substitute _ _ _).comp (doubleMap centerBase)) P =
     ((doubleMap evalRaw).comp (substitute genericCoefficients.toRingHom _ _)) P
  rw [map_substitute, substitute_map, evalRaw_generic]
private def innerEval {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (y : (Polynomial B)) : (Polynomial A) →+* (Polynomial B) :=
  eval₂RingHom (C.comp f) y
private theorem innerEval_apply {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (y : (Polynomial B)) (p : (Polynomial A)) :
    innerEval f y p = (p.map f).comp y := by
  change _ = (p.map f).eval₂ C y
  rw [eval₂_map]
  rfl
private theorem substitute_affine {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (y : (Polynomial B)) (v : Polynomial (Polynomial B)) (P : Polynomial (Polynomial A)) :
    substitute f (C y) v P = (P.map (innerEval f y)).comp v := by
  change P.eval₂ (eval₂RingHom ((jetConstant (R := B)).comp f) (C y)) v =
    (P.map (innerEval f y)).eval₂ C v
  rw [eval₂_map]
  congr 1
  apply Polynomial.ringHom_ext <;> simp [innerEval, jetConstant]
theorem affine_leading {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Injective f) {a b : B} (ha : a ≠ 0)
    (c : (Polynomial B)) {P : Polynomial (Polynomial A)} (hP : P ≠ 0) :
    let Q := substitute f (C (C a * Polynomial.X + C b)) (C (C a) * Polynomial.X + C c) P
    Q.natDegree = P.natDegree ∧ Q.leadingCoeff.natDegree = P.leadingCoeff.natDegree ∧ Q ≠ 0 := by
  let y : (Polynomial B) := C a * Polynomial.X + C b
  let v : Polynomial (Polynomial B) := C (C a) * Polynomial.X + C c
  let ev := innerEval f y
  have ev_degree (p : (Polynomial A)) : (ev p).natDegree = p.natDegree := by
    rw [innerEval_apply, natDegree_comp, natDegree_linear ha, mul_one, natDegree_map_eq_of_injective hf]
  have ev_inj : Function.Injective ev := by
    apply (injective_iff_map_eq_zero ev).mpr
    intro p hp
    by_contra hn
    have hel : (p.map f).leadingCoeff ≠ 0 := by
      apply leadingCoeff_ne_zero.mpr
      intro hz
      apply hn
      exact map_injective f hf (by simpa only [Polynomial.map_zero] using hz)
    have he := leadingCoeff_comp (p := p.map f) (q := y) (by rw [show y.natDegree = 1 from natDegree_linear ha]; decide)
    rw [show (p.map f).comp y = ev p from (innerEval_apply f y p).symm, hp,
      leadingCoeff_zero, leadingCoeff_linear ha] at he
    exact (mul_ne_zero hel (pow_ne_zero _ ha)) he.symm
  have ha' : (C a : (Polynomial B)) ≠ 0 := C_ne_zero.mpr ha
  have hv : v.natDegree = 1 := natDegree_linear ha'
  have hlead : ((P.map ev).comp v).leadingCoeff = ev P.leadingCoeff * C (a^P.natDegree) := by
    rw [leadingCoeff_comp (by rw [hv]; decide), leadingCoeff_linear ha',
      leadingCoeff_map_of_injective ev_inj, natDegree_map_eq_of_injective ev_inj, map_pow]
  change (substitute f (C y) v P).natDegree = _ ∧
    (substitute f (C y) v P).leadingCoeff.natDegree = _ ∧ substitute f (C y) v P ≠ 0
  rw [substitute_affine, natDegree_comp, hv, mul_one, natDegree_map_eq_of_injective ev_inj,
    hlead, natDegree_mul_C (pow_ne_zero _ ha), ev_degree]
  refine ⟨rfl, rfl, leadingCoeff_ne_zero.mp ?_⟩
  rw [hlead]
  apply mul_ne_zero _ (C_ne_zero.mpr (pow_ne_zero _ ha))
  simpa only [map_zero] using ev_inj.ne (leadingCoeff_ne_zero.mpr hP)
theorem specialized_formula {h} {D:PoleData h} (Crt:CRTLift D) :
    (specialized Crt).toRingHom=substitute (algebraMap Seeds (FractionRing Seeds))
      (C (C (evalRaw (rawBlock D))*Polynomial.X+C (evalRaw (crtPolynomial Crt))))
      (C (C (evalRaw (rawBlock D)))*Polynomial.X+
        C (C (evalRaw (rawBlock D).derivative)*Polynomial.X+C (evalRaw (crtPolynomial Crt).derivative))) := by
  change substitute _ (doubleMap evalRaw (rawOrdinate D Crt)) (doubleMap evalRaw (rawVelocity D Crt))=_
  simp [rawOrdinate,rawVelocity,jetConstant,doubleMap,map_add,map_mul,add_assoc]

/-- The generic physical chart, with all four scalars available for extension
of the coefficient field. The diagonal stays nonzero before any extension. -/
theorem specialized_affine_form {h} {D : PoleData h} (Crt : CRTLift D) :
    ∃ a b u d : FractionRing Seeds, a≠0 ∧ (specialized Crt).toRingHom =
      substitute (algebraMap Seeds (FractionRing Seeds)) (C (C a * Polynomial.X + C b))
        (C (C a) * Polynomial.X + C (C u * Polynomial.X + C d)) := by
  refine ⟨evalRaw (rawBlock D),evalRaw (crtPolynomial Crt),evalRaw (rawBlock D).derivative,
    evalRaw (crtPolynomial Crt).derivative,evalRaw_block_ne_zero D,?_⟩
  exact specialized_formula Crt

theorem specialized_leading {h} {D : PoleData h} (Crt : CRTLift D) {P : Jet}
    (hP : P ≠ 0) :
    (specialized Crt P).natDegree = P.natDegree ∧
    (specialized Crt P).leadingCoeff.natDegree = P.leadingCoeff.natDegree ∧ specialized Crt P ≠ 0 := by
  let a := evalRaw (rawBlock D)
  let b := evalRaw (crtPolynomial Crt)
  let c : (Polynomial CentreField) := C (evalRaw (rawBlock D).derivative) * Polynomial.X +
    C (evalRaw (crtPolynomial Crt).derivative)
  have heY : doubleMap evalRaw (rawOrdinate D Crt) = C (C a * Polynomial.X + C b) := by
    simp [rawOrdinate, jetConstant, doubleMap, a, b]
  have heV : doubleMap evalRaw (rawVelocity D Crt) = C (C a) * Polynomial.X + C c := by
    simp [rawVelocity, jetConstant, doubleMap, a, c, map_add, map_mul, add_assoc]
  change (substitute _ _ _ P).natDegree = _ ∧ (substitute _ _ _ P).leadingCoeff.natDegree = _ ∧
    substitute _ _ _ P ≠ 0
  rw [heY, heV]
  exact affine_leading _ (IsFractionRing.injective Seeds CentreField) (evalRaw_block_ne_zero D) c hP
def rawPosition {h} {D : PoleData h} (Crt : CRTLift D) (j i : ℕ) : Jet →ₗ[FX] CentreField where
  toFun P := ((specialized Crt P).coeff j).coeff i
  map_add' P Q := by simp
  map_smul' b P := by simp [Polynomial.coeff_smul]
end
end K1_14_1_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_1
open K1_14 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
theorem coeff_zeroGrade {E : Type} [Field E] (s : Shape) (q : ℕ)
    (f : GradeSlot s q → (Polynomial E)) (k : GradeSlot s q) (l : ℕ) :
    (zeroGrade s q f k).coeff l =
      ∑ j : GradeSlot s q,
        if k.val ≤ j.val ∧ q - j.val + k.val ≤ l then
          (j.val.choose k.val : E) * (f j).coeff (l - (q - j.val + k.val))
        else 0 := by
  rw [zeroGrade, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : k.val ≤ j.val
  · rw [ite_eq_left hj, coeff_mul_X_pow', coeff_mul_C]
    by_cases hl : q - j.val + k.val ≤ l
    · simp only [hj, hl, and_self, ite_true, mul_comm]
    · simp [hj, hl]
  · simp [hj]
end K1_14_1_7_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_3
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
private abbrev G := GenericField
private abbrev F := SeedFrac G
private abbrev g : Parameter →+* G := K1_14_1_7.genericPoint
private abbrev inc : G →+* F := algebraMap G F
theorem generic_den {d : Seed Parameter} (hd : specialSeed d ≠ 0) :
    MvPolynomial.map g d ≠ 0 :=
  fun hz => hd (by
    rw [(MvPolynomial.map_injective g generic_injective)
      (hz.trans (map_zero (MvPolynomial.map g)).symm), map_zero])
theorem generic_centre {h : ℕ} {D : PoleData h} {Crt : CRTLift D}
    (B : ∀ i, BlockLift D Crt i) (i : Fin 2) (α : G)
    (hr : (genericBlock D i).eval α = 0) (hb : ((D.constant i).map constGeneric).eval α ≠ 0) :
    (∑ j, liftAt g (B j).num (B j).den).eval (inc α) =
      residue i (-((D.offset i).map constGeneric).eval α)
        (((D.constant i).map constGeneric).eval α) (((D.slope i).map constGeneric).eval α) := by
  let ev := eval₂RingHom (seedEmbed g) (inc α)
  let z := algebraMap (Seed G) F (MvPolynomial.X i)
  let b := ((D.constant i).map constGeneric).eval α
  let c := ((D.slope i).map constGeneric).eval α
  let a := ((D.offset i).map constGeneric).eval α
  have hcomp : (seedEmbed g).comp MvPolynomial.C = inc.comp g := by
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, seedEmbed, MvPolynomial.map_C]
    rw [IsScalarTower.algebraMap_apply G (Seed G) F, MvPolynomial.algebraMap_eq]
  have hparam (P : (Polynomial Parameter)) :
      ev (P.map MvPolynomial.C) = inc ((P.map g).eval α) := by
    change (P.map MvPolynomial.C).eval₂ (seedEmbed g) (inc α) = _
    rw [← eval_map, map_map, hcomp, ← map_map, eval_map_apply]
  have hL (P : (Polynomial L)) : ev (P.map constSeed) = inc ((P.map constGeneric).eval α) := by
    rw [constSeed, ← map_map, hparam, map_map]
  have hC (x : Seed Parameter) : ev (C x) = seedEmbed g x := eval₂_C _ _
  have hX : ev (C (MvPolynomial.X i)) = z := by rw [hC]; simp [seedEmbed, z]
  have hA : ev (familyAmplitude D i) = inc b + z * inc c := by
    rw [familyAmplitude, map_add, map_mul, hL, hL]
    exact congrArg (fun x => inc b + x * inc c) hX
  have hQ : ev (familyOffset D i) = z * inc a := by
    rw [familyOffset, map_mul, hL]
    exact congrArg (fun x => x * inc a) hX
  have hne : inc b + z * inc c ≠ 0 := by
    have hf : (MvPolynomial.C b + MvPolynomial.X i * MvPolynomial.C c : Seed G) ≠ 0 := by
      intro he
      have hv := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : G))) he
      exact hb (by simpa [b] using hv)
    have he : algebraMap (Seed G) F (MvPolynomial.C b + MvPolynomial.X i * MvPolynomial.C c) ≠ 0 :=
      fun hz => hf ((IsFractionRing.injective (Seed G) F)
        (hz.trans (map_zero (algebraMap (Seed G) F)).symm))
    have hinc (x : G) : algebraMap (Seed G) F (MvPolynomial.C x) = inc x :=
      (IsScalarTower.algebraMap_apply G (Seed G) F x).symm
    simpa only [map_add, map_mul, z, hinc] using he
  have hzero : ev (familyBlock D i) = 0 := by rw [familyBlock, hparam, hr, map_zero]
  have hnot : ev (B (otherBlock i)).num = 0 := by
    have he := map_dvd ev (B (otherBlock i)).other_dvd
    rw [other_invol, hzero, zero_dvd_iff] at he
    exact he
  have hval (j : Fin 2) : (liftAt g (B j).num (B j).den).eval (inc α) =
      (seedEmbed g (B j).den)⁻¹ * ev (B j).num := by
    rw [liftAt, smul_eq_C_mul, eval_mul, eval_C, eval_map]
    rfl
  have he := map_dvd ev (B i).congruence
  rw [hzero, zero_dvd_iff, map_add, map_mul, map_mul, hA, hQ, hC] at he
  have hd := seedEmbed_ne_zero g (generic_den (B i).specialDen)
  rw [sum_other _ i, eval_add, hval, hval, hnot, mul_zero, add_zero]
  unfold residue
  change _ = inc (-a) * z / (inc b + inc c * z)
  rw [mul_comm (inc c) z, map_neg]
  apply (eq_div_iff hne).mpr
  calc
    _ = (seedEmbed g (B i).den)⁻¹ * ((inc b + z * inc c) * ev (B i).num) := by ring
    _ = -inc a * z := by
      rw [eq_neg_of_add_eq_zero_left he, mul_neg, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
      ring
end
end K1_14_1_7_3
end
section
namespace K1_14_3_4_5
noncomputable section
open K1_14 K1_14_3 Polynomial
abbrev Plane (F : Type*) [Semiring F] := Polynomial (Polynomial F)
def inner {R : Type*} [Semiring R] : Plane R := Polynomial.C (R := Polynomial R) (Polynomial.X (R := R))
def outer {R : Type*} [Semiring R] : Plane R := Polynomial.X (R := Polynomial R)
def parameter (i : Fin 4) : SectionField :=
  algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i)
def parameterInPlane (i : Fin 4) : Plane SectionField := C (C (parameter i))
def seedValues (k : Slice) : Fin 2 → Plane SectionField :=
  match k with
  | .seed => ![parameterInPlane 2, parameterInPlane 3]
  | .ordinate | .mixed => ![parameterInPlane 2 - parameterInPlane 0 * inner, inner]
  | .jets => ![inner, outer]
def derivativeValue (k : Slice) : Plane SectionField :=
  match k with
  | .jets => parameterInPlane 3
  | _ => outer
def evalRow {F R : Type*} [CommRing F] [CommRing R] (a : F →+* R)
    (t : Fin 2 → R) (y v : R) : Polynomial (Polynomial (MvPolynomial (Fin 2) F)) →+* R :=
  eval₂RingHom (eval₂RingHom (MvPolynomial.eval₂Hom a t) y) v
end
end K1_14_3_4_5
end
section
namespace K1_14_3_4_5
noncomputable section
open K1_14 K1_14_3 K1_14_3_4 Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 8
local instance sectionRing : CommRing SectionJet := AddMonoidAlgebra.commRing
@[simp] theorem evalRow_const {F R : Type*} [CommRing F] [CommRing R]
    (a : F →+* R) (t : Fin 2 → R) (y v : R) (c : F) :
    evalRow a t y v (C (C (MvPolynomial.C c))) = a c := by
  simp [evalRow]
@[simp] theorem evalRow_seed {F R : Type*} [CommRing F] [CommRing R]
    (a : F →+* R) (t : Fin 2 → R) (y v : R) (i : Fin 2) :
    evalRow a t y v (C (C (MvPolynomial.X i))) = t i := by
  simp [evalRow]
@[simp] theorem evalRow_y {F R : Type*} [CommRing F] [CommRing R]
    (a : F →+* R) (t : Fin 2 → R) (y v : R) :
    evalRow a t y v (C (R := Polynomial (MvPolynomial (Fin 2) F)) (Polynomial.X (R := MvPolynomial (Fin 2) F))) = y := by
  simp [evalRow]
@[simp] theorem evalRow_v {F R : Type*} [CommRing F] [CommRing R]
    (a : F →+* R) (t : Fin 2 → R) (y v : R) :
    evalRow a t y v (Polynomial.X (R := Polynomial (MvPolynomial (Fin 2) F))) = v := by
  simp [evalRow]
theorem rowHom_ext {F R : Type*} [CommRing F] [CommRing R]
    {f g : Polynomial (Polynomial (MvPolynomial (Fin 2) F)) →+* R}
    (hc : ∀ c : F, f (C (C (MvPolynomial.C c))) = g (C (C (MvPolynomial.C c))))
    (ht : ∀ i, f (C (C (MvPolynomial.X i))) = g (C (C (MvPolynomial.X i))))
    (hy : f (C (R := Polynomial (MvPolynomial (Fin 2) F)) (Polynomial.X (R := MvPolynomial (Fin 2) F))) =
      g (C (R := Polynomial (MvPolynomial (Fin 2) F)) (Polynomial.X (R := MvPolynomial (Fin 2) F))))
    (hv : f (Polynomial.X (R := Polynomial (MvPolynomial (Fin 2) F))) =
      g (Polynomial.X (R := Polynomial (MvPolynomial (Fin 2) F)))) : f = g := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext <;> assumption
    · exact hy
  · exact hv
end
@[local simp] private theorem single_zero_eq_C' {R : Type*} [Semiring R] (a : R) :
    AddMonoidAlgebra.single 0 a = (Polynomial.C a : Polynomial R) := rfl
end K1_14_3_4_5
end
section
namespace K1_14_3_4_5_1
noncomputable section
open K1_14 K1_14_3 K1_14_3_2 K1_14_3_4_5 Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 8
private abbrev Extended := MvPolynomial (Fin 2) Jet
private abbrev Parameters := MvPolynomial (Fin 4) FX
private abbrev RawPlane := Plane Parameters
private def rawParameter (i : Fin 4) : RawPlane := C (C (MvPolynomial.X i))
private def rawSeeds (k : Slice) : Fin 2 → RawPlane :=
  match k with
  | .seed => ![rawParameter 2, rawParameter 3]
  | .ordinate | .mixed => ![rawParameter 2 - rawParameter 0 * K1_14_3_4_5.inner, K1_14_3_4_5.inner]
  | .jets => ![K1_14_3_4_5.inner, outer]
private def rawY (k : Slice) : RawPlane :=
  match k with
  | .seed => K1_14_3_4_5.inner
  | .ordinate => rawParameter 3
  | .mixed => rawParameter 3 - rawParameter 1 * outer
  | .jets => rawParameter 2
private def rawV (k : Slice) : RawPlane :=
  match k with
  | .jets => rawParameter 3
  | _ => outer
private def rawRow (k : Slice) : Jet →+* RawPlane :=
  evalRow (C.comp (C.comp MvPolynomial.C)) (rawSeeds k) (rawY k) (rawV k)
private def slopeIndex (i : Fin 2) : Fin 4 := Fin.castLE (by decide) i
private def forward (k : Slice) : Extended →+* RawPlane :=
  MvPolynomial.eval₂Hom (rawRow k) (fun i => rawParameter (slopeIndex i))
private abbrev oldSeed (i : Fin 2) : Extended :=
  MvPolynomial.C (C (C (MvPolynomial.X i)))
private abbrev oldY : Extended := MvPolynomial.C (C (Polynomial.X (R := Seeds)))
private abbrev oldV : Extended :=
  MvPolynomial.C (Polynomial.X (R := Polynomial Seeds))
private abbrev slope (i : Fin 2) : Extended := MvPolynomial.X i
private def parameterBack (k : Slice) : Fin 4 → Extended :=
  match k with
  | .seed => ![slope 0, slope 1, oldSeed 0, oldSeed 1]
  | .ordinate => ![slope 0, slope 1, oldSeed 0 + slope 0 * oldSeed 1, oldY]
  | .mixed => ![slope 0, slope 1, oldSeed 0 + slope 0 * oldSeed 1, oldY + slope 1 * oldV]
  | .jets => ![slope 0, slope 1, oldY, oldV]
private def innerBack (k : Slice) : Extended :=
  match k with
  | .seed => oldY
  | .ordinate | .mixed => oldSeed 1
  | .jets => oldSeed 0
private def outerBack (k : Slice) : Extended :=
  match k with
  | .jets => oldSeed 1
  | _ => oldV
private def back (k : Slice) : RawPlane →+* Extended :=
  eval₂RingHom
    (eval₂RingHom
      (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (C.comp (C.comp MvPolynomial.C)))
        (parameterBack k)) (innerBack k)) (outerBack k)
@[simp] private theorem forward_const (k : Slice) (c : FX) :
    forward k (MvPolynomial.C (C (C (MvPolynomial.C c)))) =
      C (C (MvPolynomial.C c)) := by
  simp [forward, rawRow]
@[simp] private theorem forward_seed (k : Slice) (i : Fin 2) :
    forward k (oldSeed i) = rawSeeds k i := by
  simp [forward, rawRow]
@[simp] private theorem forward_y (k : Slice) : forward k oldY = rawY k := by
  simp [forward, rawRow]
@[simp] private theorem forward_v (k : Slice) : forward k oldV = rawV k := by
  simp [forward, rawRow]
@[simp] private theorem forward_slope (k : Slice) (i : Fin 2) :
    forward k (slope i) = rawParameter (slopeIndex i) := by
  simp [forward]
@[simp] private theorem back_const (k : Slice) (c : FX) :
    back k (C (C (MvPolynomial.C c))) = MvPolynomial.C (C (C (MvPolynomial.C c))) := by
  simp [back]
@[simp] private theorem back_parameter (k : Slice) (i : Fin 4) :
    back k (rawParameter i) = parameterBack k i := by
  simp [back, rawParameter]
@[simp] private theorem back_inner (k : Slice) :
    back k K1_14_3_4_5.inner = innerBack k := by
  simp [back, K1_14_3_4_5.inner]
@[simp] private theorem back_outer (k : Slice) :
    back k outer = outerBack k := by
  simp [back, outer]
private theorem forward_back (k : Slice) : (forward k).comp (back k) = RingHom.id RawPlane := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro c
        change forward k (back k (C (C (MvPolynomial.C c)))) = _
        simp
      · intro i
        change forward k (back k (rawParameter i)) = rawParameter i
        fin_cases i <;> cases k <;>
          simp [parameterBack, slopeIndex, rawSeeds, rawY, rawV]
    · change forward k (back k K1_14_3_4_5.inner) = K1_14_3_4_5.inner
      cases k <;> simp [innerBack, rawSeeds, rawY]
  · change forward k (back k outer) = outer
    cases k <;> simp [outerBack, rawSeeds, rawV]
private theorem back_forward (k : Slice) : (back k).comp (forward k) = RingHom.id Extended := by
  apply MvPolynomial.ringHom_ext'
  · apply K1_14_3_4_5.rowHom_ext
    · intro c
      change back k (forward k (MvPolynomial.C (C (C (MvPolynomial.C c))))) = _
      simp
    · intro i
      change back k (forward k (oldSeed i)) = oldSeed i
      fin_cases i <;> cases k <;> simp [rawSeeds, parameterBack, innerBack, outerBack]
    · change back k (forward k oldY) = oldY
      cases k <;> simp [rawY, parameterBack, innerBack, outerBack]
    · change back k (forward k oldV) = oldV
      cases k <;> simp [rawV, parameterBack, outerBack]
  · intro i
    change back k (forward k (slope i)) = slope i
    fin_cases i <;> cases k <;> simp [slopeIndex, parameterBack]
private def coordinates (k : Slice) : Extended ≃+* RawPlane :=
  RingEquiv.ofRingHom (forward k) (back k) (forward_back k) (back_forward k)
@[simp] private theorem coordinates_C (k : Slice) (x : Jet) :
    coordinates k (MvPolynomial.C x) = rawRow k x := by
  change forward k (MvPolynomial.C x) = _
  simp [forward]
attribute [local instance] Polynomial.algebra
private abbrev denominators : Submonoid RawPlane :=
  ((nonZeroDivisors Parameters).map (C : Parameters →+* Polynomial Parameters)).map
    (C : Polynomial Parameters →+* RawPlane)
private instance : IsLocalization denominators (Plane SectionField) := by
  let := Polynomial.isLocalization (nonZeroDivisors Parameters) SectionField
  exact Polynomial.isLocalization
    ((nonZeroDivisors Parameters).map (C : Parameters →+* Polynomial Parameters))
      (Polynomial SectionField)
end
end K1_14_3_4_5_1
end
section
set_option autoImplicit false
namespace K1_11
noncomputable section
open K1 MvPolynomial
structure IndependentLift {u : Words} {T : TwoActive u} (R : Relation T) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  omitted : U.degreeOf 1 = 0 ∧ U.degreeOf 2 = 0 ∧
    V.degreeOf 1 = 0 ∧ V.degreeOf 2 = 0
  heights : U.degreeOf 0 ≤ T.height ∧ V.degreeOf 0 ≤ T.height
  boxes : U.degreeOf 3 ≤ 1 ∧ U.degreeOf 4 ≤ 2 ∧ V.degreeOf 3 ≤ 2 ∧ V.degreeOf 4 ≤ 1
  primitive : ∀ q : MvPolynomial (Fin 2) K,
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ U →
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ V → IsUnit q
  content : Polynomial K
  content_ne : content ≠ 0
  graphU : aeval ![Polynomial.X, 0, 0, seed, seed ^ p] U =
    Polynomial.C content * leftU R
  graphV : aeval ![Polynomial.X, 0, 0, seed, seed ^ p] V =
    Polynomial.C content * leftV R
  original_height : 24597 ≤ T.height
structure Puncture (deleted : Finset I) where
  N : ℕ
  index : Fin N ↪ I
  retained : ∀ i, i ∈ Set.range index ↔ i ∉ deleted
  size : N + deleted.card = 262144
def Puncture.nodes {deleted : Finset I} (P : Puncture deleted) (i : Fin P.N) : K :=
  node (P.index i)
structure Marks (u : Words) (deleted : Finset I) (Γ : Finset K) where
  mark : ∀ γ ∈ Γ, BadMark u γ
  survives : ∀ γ (hγ : γ ∈ Γ) i, i ∈ (mark γ hγ).support → i ∉ deleted
inductive Bank
  | symmetric
  | lowS
  | lowT
def Bank.dS : Bank → ℕ
  | .symmetric => 2
  | .lowS => 1
  | .lowT => 2
def Bank.dT : Bank → ℕ
  | .symmetric => 2
  | .lowS => 2
  | .lowT => 1
def Bank.s : Bank → ℕ
  | .symmetric => 10
  | .lowS => 14
  | .lowT => 9
def Bank.t : Bank → ℕ
  | .symmetric => 10
  | .lowS => 9
  | .lowT => 14
def Bank.a (b : Bank) : ℕ := b.s + 5 * b.dS
def Bank.b (b : Bank) : ℕ := b.t + 5 * (b.dT - 1)
def Bank.E (b : Bank) : ℕ := b.a + b.b
def Bank.M (b : Bank) : ℕ := (2 * 131071 - 1) * (b.E - 1) + 1
def Bank.relationBounds (b : Bank) (H : ℕ) : Fin 4 → ℕ := ![131071 + H, 1, b.dS, b.dT]
structure ContactInput (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (b : Bank) (H : ℕ) where
  L : MvPolynomial (Fin 5) K
  L_ne : L ≠ 0
  degrees : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = b.relationBounds H j
  order_one : ∀ i : Fin P.N,
    (contactLift contactWeight
      (contactShift (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i) ^ p) (u 1 (P.index i) ^ p) L)).natTrailingDegree = 1
  numerator : MvPolynomial (Fin 4) K
  denominator : MvPolynomial (Fin 4) K
  denominator_ne : denominator ≠ 0
  linear : polynomialView L =
    Polynomial.C denominator * Polynomial.X - Polynomial.C numerator
  primitive : (Polynomial.C denominator * Polynomial.X - Polynomial.C numerator).IsPrimitive
  numerator_Y : numerator.weightedTotalDegree scalarWeightY ≤ 1
  denominator_Y : denominator.weightedTotalDegree scalarWeightY ≤ 0
  numerator_S : numerator.weightedTotalDegree scalarWeightYS ≤ b.dS
  denominator_S : denominator.weightedTotalDegree scalarWeightYS ≤ b.dS
  numerator_T : numerator.weightedTotalDegree scalarWeightT ≤ b.dT
  denominator_T : denominator.weightedTotalDegree scalarWeightT ≤ b.dT - 1
def scalarWeightTotal : Fin 4 → ℕ := ![0, 1, 1, 1]
structure Annihilator {u : Words} {deleted : Finset I} {Γ : Finset K}
    (F : Marks u deleted Γ) (b : Bank) where
  Q : MvPolynomial (Fin 4) K
  nonzero : Q ≠ 0
  degreeY : Q.weightedTotalDegree scalarWeightY ≤ 5
  degreeS : Q.weightedTotalDegree scalarWeightYS ≤ b.a
  degreeT : Q.weightedTotalDegree scalarWeightT ≤ b.b
  degreeTotal : Q.weightedTotalDegree scalarWeightTotal ≤ b.E
  vanishes : ∀ γ (hγ : γ ∈ Γ),
    aeval (scalarImages (F.mark γ hγ).decoder γ (γ ^ p)) Q = 0
def nodeCut (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (numerator : Polynomial (MvPolynomial (Fin 3) Frac)) (denominator : MvPolynomial (Fin 3) Frac)
    (i : Fin P.N) : MvPolynomial (Fin 3) Frac :=
  numerator.eval (C (algebraMap K Frac (P.nodes i))) -
    denominator * (C (algebraMap K Frac (u 0 (P.index i))) +
      MvPolynomial.X 1 * C (algebraMap K Frac (u 1 (P.index i))))
structure TaylorChart (u : Words) {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank) (Λ : Finset K) where
  subset : Λ ⊆ Γ
  equation : MvPolynomial (Fin 3) Frac
  equation_ne : equation ≠ 0
  equation_degree : equation.totalDegree ≤ b.E
  numerator : Polynomial (MvPolynomial (Fin 3) Frac)
  numerator_degree : numerator.natDegree ≤ 131071
  denominator : MvPolynomial (Fin 3) Frac
  cut_degree : ∀ i, (nodeCut u P numerator denominator i).totalDegree ≤ b.M
  point : K → Fin 3 → Frac
  slope : ∀ γ ∈ Λ, point γ 1 = algebraMap K Frac γ
  on_equation : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) equation = 0
  regular : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) denominator ≠ 0
  reconstruction : ∀ γ (hγ : γ ∈ Λ),
    numerator.map (MvPolynomial.eval (point γ)) =
      Polynomial.C (MvPolynomial.eval (point γ) denominator) *
        (F.mark γ (subset hγ)).decoder.map (algebraMap K Frac)
end
end K1_11
end
section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace K1_11
noncomputable section
open MvPolynomial
theorem exists_kernel_outside {F E G : Type*} [Field F]
    [AddCommGroup E] [Module F E] [Module.Finite F E]
    [AddCommGroup G] [Module F G] [Module.Finite F G]
    (f : E →ₗ[F] G) (R : Submodule F E)
    (hdim : Module.finrank F G + Module.finrank F R < Module.finrank F E) :
    ∃ q : E, f q = 0 ∧ q ∉ R := by
  by_contra hn
  have hle : LinearMap.ker f ≤ R := by
    intro q hq
    by_contra hnot
    exact hn ⟨q, LinearMap.mem_ker.mp hq, hnot⟩
  have hk := Submodule.finrank_mono hle
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hr := (LinearMap.range f).finrank_le
  omega
variable {F : Type*} [Field F]
structure ContactData (N : ℕ) (L : MvPolynomial (Fin 5) F) (b : Bank) where
  x : Fin N → F
  first : Fin N → F
  firstSlope : Fin N → F
  second : Fin N → F
  secondSlope : Fin N → F
  nonzero : L ≠ 0
  degreeS : L.weightedTotalDegree (sourceWeights 1 2) ≤ b.dS
  degreeT : L.weightedTotalDegree (sourceWeights 1 3) ≤ b.dT
  order_one : ∀ i, (contactLift contactWeight
    (contactShift (x i) (first i) (firstSlope i) (second i) (secondSlope i) L)).natTrailingDegree = 1
variable {N : ℕ} {L : MvPolynomial (Fin 5) F} {b : Bank} {H : ℕ} (D : ContactData N L b)
end
end K1_11
end
section
set_option autoImplicit false
namespace K1_11_1
noncomputable section
open Polynomial Matrix FrobeniusLocator
abbrev Seeds (F : Type) [Field F] := MvPolynomial (Fin 2) F
abbrev PlaneField (F : Type) [Field F] := FractionRing (Seeds F)
def graph {F : Type} [Field F] (p : ℕ) : Seeds F →ₐ[F] (Polynomial F) :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.X ^ p]
def coefficientPrimitive {A ι : Type} [CommMonoid A] (v : ι → A) : Prop :=
  ∀ q : A, (∀ i, q ∣ v i) → IsUnit q
def planePair {F : Type} [Field F] {h : ℕ}
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2) : (Polynomial (Seeds F)) :=
  Principal.assemble (fun j => Q (b, j))
def blockDegree {F : Type} [Field F] {h : ℕ}
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b i : Fin 2) : ℕ :=
  Finset.univ.sup (fun j : Fin (h + 1) => (Q (b, j)).degreeOf i)
def planeSyndrome {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (b : Fin 2) (j : ℕ) : Seeds F :=
  if b = 0 then
    MvPolynomial.C (syndrome x u j) + MvPolynomial.X b * MvPolynomial.C (syndrome x v j)
  else
    MvPolynomial.C (syndrome x u j ^ p) + MvPolynomial.X b * MvPolynomial.C (syndrome x v j ^ p)
def planeSlice {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (m h : ℕ) :
    Matrix (Fin (m - h)) (Fin 2 × Fin (h + 1)) (Seeds F) :=
  fun j b => planeSyndrome p x u v b.1 (b.2.val + j.val)
def planeStack {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (L t : ℕ) : Matrix (Fin 2 × Fin L) (Fin (t + 1)) (Seeds F) :=
  fun b j => planeSyndrome p x u v b.1 (b.2.val + j.val)
def seedPositions : Fin 2 → Fin 5 := ![3, 4]
def intoFive {F : Type} [Field F] : (Polynomial (Seeds F)) →+* MvPolynomial (Fin 5) F :=
  Polynomial.eval₂RingHom (MvPolynomial.rename seedPositions).toRingHom (MvPolynomial.X 0)
end
end K1_11_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_11_1
noncomputable section
open MvPolynomial Finset Polynomial
open FrobeniusLocator
variable {F : Type} [Field F]
def graphExponent (p : ℕ) (e : Fin 2 →₀ ℕ) : ℕ := e 0+p*e 1
theorem graphExponent_injOn (p : ℕ) (hp : 0<p) :
    Set.InjOn (graphExponent p) {e : Fin 2 →₀ ℕ | e 0<p} := by
  intro e he f hf h
  have hm := congrArg (fun n : ℕ => n%p) h
  simp only [graphExponent,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hf] at hm
  have hmul : p*e 1=p*f 1 := by unfold graphExponent at h; omega
  have h1 : e 1=f 1 := Nat.eq_of_mul_eq_mul_left hp hmul
  ext i
  fin_cases i <;> assumption
theorem graph_monomial (p : ℕ) (e : Fin 2 →₀ ℕ) (a : F) :
    graph p (monomial e a)=Polynomial.monomial (graphExponent p e) a := by
  rw [graph,MvPolynomial.aeval_monomial]
  simp [Finsupp.prod_fintype,Fin.prod_univ_succ,graphExponent,← pow_mul,← pow_add,Polynomial.C_mul_X_pow_eq_monomial]
theorem graph_coeff (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hdegree : Q.degreeOf 0 < p) (e : Fin 2 →₀ ℕ) (he : e∈Q.support) :
    (graph p Q).coeff (graphExponent p e)=Q.coeff e := by
  classical
  have hex : graph p Q=∑ f∈Q.support,Polynomial.monomial (graphExponent p f) (Q.coeff f) := by
    conv_lhs => rw [Q.as_sum]
    simp only [map_sum,graph_monomial]
  rw [hex,Polynomial.finsetSum_coeff]
  trans ((Polynomial.monomial (graphExponent p e) (Q.coeff e)).coeff (graphExponent p e))
  · apply Finset.sum_eq_single_of_mem e he
    intro f hf hfe
    rw [Polynomial.coeff_monomial, Finsupp.single_apply,ite_eq_right]
    intro h
    apply hfe
    apply graphExponent_injOn p hp
    · exact (le_degreeOf_of_mem_support 0 hf).trans_lt hdegree
    · exact (le_degreeOf_of_mem_support 0 he).trans_lt hdegree
    · exact h
  · simp
theorem graph_ne_zero (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hQ : Q≠0) (hdegree : Q.degreeOf 0 < p) : graph p Q≠0 := by
  obtain ⟨e,he⟩ := support_nonempty.mpr hQ
  intro hz
  have hh := graph_coeff p hp Q hdegree e he
  rw [hz,Polynomial.coeff_zero] at hh
  exact (mem_support_iff.mp he) hh.symm
section Rank
open Matrix
variable {r H J : ℕ}
private theorem exists_rank_minor {ι κ E : Type} [Fintype ι] [Fintype κ] [Field E]
    (A : Matrix ι κ E) :
    ∃ (rows : Fin A.rank → ι) (cols : Fin A.rank → κ), (A.submatrix rows cols).det ≠ 0 := by
  classical
  obtain ⟨B⟩ := NormalFiber.exists_rowBasis
    (Polynomial.evalRingHom (0 : E)) (A.map Polynomial.C) A.rank (by
      have heq : (A.map Polynomial.C).map (Polynomial.evalRingHom (0 : E)) = A := by
        ext i j
        simp
      rw [heq])
  refine ⟨B.rows, B.cols, ?_⟩
  intro h
  apply B.minor_ne
  change ((A.submatrix B.rows B.cols).map Polynomial.C).det = 0
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
private theorem minor_degree {υ : Type} [Fintype υ] [DecidableEq υ]
    (i : Fin 2) (A : Matrix υ υ (Seeds F)) (d : υ → ℕ)
    (hd : ∀ j k, (A j k).degreeOf i ≤ d k) :
    A.det.degreeOf i ≤ ∑ k, d k := by
  classical
  rw [Matrix.det_apply']
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro σ _
  have hc : ((↑↑(Equiv.Perm.sign σ) : Seeds F)).degreeOf i = 0 := by
    rw [← map_intCast (MvPolynomial.C : F →+* Seeds F), degreeOf_C]
  apply (degreeOf_mul_le _ _ _).trans
  rw [hc, zero_add]
  exact (degreeOf_prod_le _ _ _).trans (Finset.sum_le_sum (fun k _ => hd (σ k) k))
private theorem graph_minor_ne_zero (p : ℕ) (hp : 0 < p) (hH : H < p)
    (A : Matrix (Fin J) (Fin 2 × Fin H) (Seeds F))
    (hd : ∀ j k, (A j k).degreeOf 0 ≤ if k.1 = 0 then 1 else 0)
    (rows : Fin r → Fin J) (cols : Fin r → Fin 2 × Fin H)
    (hminor : (A.submatrix rows cols).det ≠ 0) :
    graph p (A.submatrix rows cols).det ≠ 0 := by
  classical
  have hinj : Function.Injective cols := by
    intro j k hjk
    by_contra hne
    exact hminor (Matrix.det_zero_of_column_eq hne (by
      intro l
      change A (rows l) (cols j) = A (rows l) (cols k)
      rw [hjk]))
  apply graph_ne_zero p hp _ hminor
  apply (minor_degree 0 (A.submatrix rows cols) (fun k => if (cols k).1 = 0 then 1 else 0)
    (fun j k => hd (rows j) (cols k))).trans_lt
  apply lt_of_le_of_lt _ hH
  let S : Finset (Fin r) := Finset.univ.filter (fun k => (cols k).1 = 0)
  have hsum : (∑ k, if (cols k).1 = 0 then 1 else 0) = S.card := by
    simp [S, Finset.sum_boole]
  rw [hsum]
  have hle : S.card ≤ Fintype.card (Fin H) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_le_of_injective (fun k : S => (cols k.val).2) ?_
    intro j k hjk
    apply Subtype.ext
    apply hinj
    have hj : (cols j.val).1 = 0 := (Finset.mem_filter.mp j.property).2
    have hk : (cols k.val).1 = 0 := (Finset.mem_filter.mp k.property).2
    exact Prod.ext (hj.trans hk.symm) hjk
  simpa only [Fintype.card_fin] using hle
theorem rank_graph (q : ℕ) (hq : 0 < q) (hH : H < q)
    (A : Matrix (Fin J) (Fin 2 × Fin H) (Seeds F))
    (hd : ∀ j k, (A j k).degreeOf 0 ≤ if k.1 = 0 then 1 else 0) :
    (A.map (algebraMap (Seeds F) (PlaneField F))).rank =
      (A.map ((algebraMap (Polynomial F) (FrobeniusLocator.GenericLayer.GenericField F)).comp
        (graph q).toRingHom)).rank := by
  let f := algebraMap (Seeds F) (PlaneField F)
  let g := (algebraMap (Polynomial F) (FrobeniusLocator.GenericLayer.GenericField F)).comp
    (graph (F := F) q).toRingHom
  have hdet {E : Type} [Field E] (φ : Seeds F →+* E) {s : ℕ} (rows : Fin s → Fin J) (cols : Fin s → Fin 2 × Fin H) :
      ((A.map φ).submatrix rows cols).det = φ (A.submatrix rows cols).det := by
    have he := φ.map_det (A.submatrix rows cols)
    rw [RingHom.mapMatrix_apply] at he
    exact he.symm
  change (A.map f).rank = (A.map g).rank
  apply le_antisymm
  · obtain ⟨rows, cols, hn⟩ := exists_rank_minor (A.map f)
    rw [hdet f] at hn
    have hn' : (A.submatrix rows cols).det ≠ 0 := fun h => hn (by rw [h, map_zero])
    have hg : ((A.map g).submatrix rows cols).det ≠ 0 := by
      rw [hdet g]
      change algebraMap (Polynomial F) (GenericLayer.GenericField F) (graph q _) ≠ 0
      rw [← map_zero (algebraMap (Polynomial F) (GenericLayer.GenericField F))]
      exact (IsFractionRing.injective (Polynomial F) _).ne
        (graph_minor_ne_zero q hq hH A hd rows cols hn')
    have h := Matrix.rank_submatrix_le (A.map g) rows cols
    rwa [Matrix.rank_of_det_ne_zero hg, Fintype.card_fin] at h
  · obtain ⟨rows, cols, hn⟩ := exists_rank_minor (A.map g)
    rw [hdet g] at hn
    have hn' : (A.submatrix rows cols).det ≠ 0 := fun h => hn (by rw [h, map_zero])
    have hf : ((A.map f).submatrix rows cols).det ≠ 0 := by
      rw [hdet f]
      rw [← map_zero f]
      exact (IsFractionRing.injective (Seeds F) _).ne hn'
    have h := Matrix.rank_submatrix_le (A.map f) rows cols
    rwa [Matrix.rank_of_det_ne_zero hf, Fintype.card_fin] at h
end Rank
end
end K1_11_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace K1_11
noncomputable section
open K1 MvPolynomial
variable {u : Words} {deleted : Finset I} {P : Puncture deleted} {b : Bank} {H : ℕ}
    (D : ContactInput u P b H)
def correctOn (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (Q Q' : Polynomial K) (s t : K) (S : Finset (Fin P.N)) : Prop :=
  ∀ i ∈ S, Q.eval (P.nodes i) = u 0 (P.index i) + s * u 1 (P.index i) ∧
    Q'.eval (P.nodes i) = u 0 (P.index i) ^ p + t * u 1 (P.index i) ^ p
theorem nodes_injective : Function.Injective P.nodes :=
  ProximityPrize.Benchmark.IRSProfile.domain.injective.comp P.index.injective
end
end K1_11
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_11_1
noncomputable section
open Polynomial Matrix FrobeniusLocator
open scoped BigOperators nonZeroDivisors
theorem mulVec_map {A B ι κ : Type} [CommRing A] [CommRing B] [Fintype κ]
    (f : A →+* B) (M : Matrix ι κ A) (v : κ → A) :
    (M.map f).mulVec (fun j => f (v j)) = fun i => f (M.mulVec v i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
private theorem primitive_vector {A κ : Type} [CommRing A] [IsDomain A]
    [NormalizedGCDMonoid A] [Fintype κ] (v : κ → A) (hv : v ≠ 0) :
    ∃ (g : A) (Q : κ → A), g ≠ 0 ∧ v = g • Q ∧ coefficientPrimitive Q := by
  classical
  let g := Finset.univ.gcd v
  have hdiv (i : κ) : g ∣ v i := Finset.gcd_dvd (Finset.mem_univ i)
  have hg : g ≠ 0 := by
    intro he
    apply hv
    funext i
    simpa only [he, zero_dvd_iff, Pi.zero_apply] using hdiv i
  choose Q hQ using hdiv
  refine ⟨g, Q, hg, funext hQ, fun q hq => ?_⟩
  have hd : g * q ∣ g := Finset.dvd_gcd (fun i _ => by
    rw [hQ i, mul_dvd_mul_iff_left hg]
    exact hq i)
  apply isUnit_iff_dvd_one.mpr
  apply (mul_dvd_mul_iff_left hg).mp
  simpa only [mul_one] using hd
theorem plane_generator {F ι κ : Type} [Field F] [Fintype κ]
    (M : Matrix ι κ (Seeds F))
    (hn : 0 < Module.finrank (PlaneField F)
      (LinearMap.ker (M.map (algebraMap (Seeds F) (PlaneField F))).mulVecLin)) :
    ∃ Q : κ → Seeds F, Q ≠ 0 ∧ M.mulVec Q = 0 ∧ coefficientPrimitive Q := by
  classical
  let N := M.map (algebraMap (Seeds F) (PlaneField F))
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hn
  let v : κ → PlaneField F := w.val
  have hv : v ≠ 0 := fun he => hw (Subtype.ext he)
  have hk : N.mulVec v = 0 := w.property
  let D := (Seeds F)⁰
  let g := IsLocalization.commonDenom D Finset.univ v
  let W (i : κ) : Seeds F := IsLocalization.integerMultiple D Finset.univ v ⟨i, Finset.mem_univ i⟩
  have hW (i : κ) : algebraMap (Seeds F) (PlaneField F) (W i) =
      algebraMap (Seeds F) (PlaneField F) (g : Seeds F) * v i := by
    have he := IsLocalization.map_integerMultiple D Finset.univ v ⟨i, Finset.mem_univ i⟩
    change _ = (g : Seeds F) • v i at he
    simpa only [Algebra.smul_def] using he
  have hg : algebraMap (Seeds F) (PlaneField F) (g : Seeds F) ≠ 0 :=
    fun hz => (mem_nonZeroDivisors_iff_ne_zero.mp g.property)
      (IsFractionRing.injective (Seeds F) (PlaneField F) (hz.trans (map_zero _).symm))
  have hWne : W ≠ 0 := by
    intro he
    apply hv
    funext i
    have hf := hW i
    rw [he, Pi.zero_apply, map_zero] at hf
    exact (mul_eq_zero.mp hf.symm).resolve_left hg
  have hWM : M.mulVec W = 0 := by
    have h := mulVec_map (algebraMap (Seeds F) (PlaneField F)) M W
    simp only [hW] at h
    change N.mulVec ((algebraMap (Seeds F) (PlaneField F) (g : Seeds F)) • v) = _ at h
    rw [Matrix.mulVec_smul, hk, smul_zero] at h
    funext i
    apply IsFractionRing.injective (Seeds F) (PlaneField F)
    rw [Pi.zero_apply, map_zero]
    exact (congrFun h i).symm
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α := Seeds F)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid (Seeds F)
  obtain ⟨a, Q, ha, he, hp⟩ := primitive_vector W hWne
  refine ⟨Q, ?_, ?_, hp⟩
  · intro hz
    rw [hz, smul_zero] at he
    exact hWne he
  · rw [he, Matrix.mulVec_smul] at hWM
    funext i
    exact (mul_eq_zero.mp (congrFun hWM i)).resolve_left ha
theorem shifts_annihilate {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (h L s t : ℕ) (hs : h + s = L)
    (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (hQ : (planeSlice p x u v (L + t) h).mulVec Q = 0) :
    (K1_6.shifts (planePair Q) L s).transpose * planeStack p x u v L t = 0 := by
  classical
  apply Matrix.ext
  intro d j
  let e : Fin 2 × Fin (h + 1) ↪ Fin 2 × Fin L :=
    ⟨fun z => (z.1, ⟨z.2.val + d.val, by have := z.2.isLt; have := d.isLt; omega⟩),
      fun a b hab => Prod.ext (congrArg (fun z : Fin 2 × Fin L => z.1) hab)
        (Fin.ext (by
          have he := congrArg (fun z : Fin 2 × Fin L => z.2.val) hab
          exact Nat.add_right_cancel he))⟩
  let jd : Fin (L + t - h) := ⟨j.val + d.val, by have := j.isLt; have := d.isLt; omega⟩
  have hshift (z : Fin 2 × Fin (h + 1)) :
      (K1_6.shifts (planePair Q) L s) (e z) d = Q z := by
    change (planePair Q z.1 * Polynomial.X ^ d.val).coeff (z.2.val + d.val) = Q z
    rw [coeff_mul_X_pow, planePair, Principal.assemble_coeff]
  have hzero (z : Fin 2 × Fin L) (hz : z ∉ Set.range e) :
      (K1_6.shifts (planePair Q) L s) z d = 0 := by
    change (planePair Q z.1 * Polynomial.X ^ d.val).coeff z.2.val = 0
    by_cases hlo : z.2.val < d.val
    · rw [coeff_mul_X_pow', ite_eq_right (not_le.mpr hlo)]
    · have hhi : h < z.2.val - d.val := by
        by_contra! hh
        apply hz
        refine ⟨(z.1, ⟨z.2.val - d.val, by omega⟩), Prod.ext rfl (Fin.ext ?_)⟩
        change z.2.val - d.val + d.val = z.2.val
        omega
      have he : z.2.val - d.val + d.val = z.2.val := Nat.sub_add_cancel (by omega)
      rw [← he, coeff_mul_X_pow]
      exact coeff_eq_zero_of_natDegree_lt ((Principal.assemble_natDegree_le _).trans_lt hhi)
  change (∑ z, K1_6.shifts (planePair Q) L s z d * planeStack p x u v L t z j) = 0
  have hsum : (∑ z : Fin 2 × Fin L, K1_6.shifts (planePair Q) L s z d * planeStack p x u v L t z j) =
      ∑ z : Fin 2 × Fin (h + 1), K1_6.shifts (planePair Q) L s (e z) d *
        planeStack p x u v L t (e z) j := by
    let f (z : Fin 2 × Fin L) := K1_6.shifts (planePair Q) L s z d * planeStack p x u v L t z j
    calc
      _ = ∑ z ∈ Finset.univ.map e, f z := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro z _ hz
        change K1_6.shifts (planePair Q) L s z d * planeStack p x u v L t z j = 0
        rw [hzero z (fun hm => hz (by
          obtain ⟨w, rfl⟩ := hm
          exact Finset.mem_map.mpr ⟨w, Finset.mem_univ _, rfl⟩)), zero_mul]
      _ = _ := Finset.sum_map _ e f
  rw [hsum]
  have hk := congrFun hQ jd
  change (∑ z, planeSlice p x u v (L + t) h jd z * Q z) = 0 at hk
  rw [← hk]
  apply Finset.sum_congr rfl
  intro z _
  rw [hshift, mul_comm]
  congr 1
  change planeSyndrome p x u v z.1 (z.2.val + d.val + j.val) =
    planeSyndrome p x u v z.1 (z.2.val + (j.val + d.val))
  congr 1
  omega
end
end K1_11_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000
namespace K1_11_1
noncomputable section
open Polynomial Matrix FrobeniusLocator K1 ProximityPrize.Benchmark
open scoped BigOperators
private theorem graph_syndrome {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (b : Fin 2) (j : ℕ) :
    graph q (planeSyndrome q x u v b j) = Principal.parameterSyndromes q x u v b j := by
  fin_cases b <;> simp [graph, planeSyndrome, Principal.parameterSyndromes]
theorem syndrome_degree {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (b i : Fin 2) (j : ℕ) :
    (planeSyndrome q x u v b j).degreeOf i ≤ if b = i then 1 else 0 := by
  have h (a c : F) :
      (MvPolynomial.C a + MvPolynomial.X b * MvPolynomial.C c).degreeOf i ≤
        if b = i then 1 else 0 := by
    apply (MvPolynomial.degreeOf_add_le i _ _).trans
    apply max_le
    · simp
    · apply (MvPolynomial.degreeOf_mul_C_le _ _ _).trans
      rw [MvPolynomial.degreeOf_X]
      by_cases he : b = i
      · simp [he]
      · simp [he, Ne.symm he]
  unfold planeSyndrome
  by_cases hb : b = 0
  · simpa only [hb, ite_true] using h (syndrome x u j) (syndrome x v j)
  · simpa only [hb, ite_false] using h (syndrome x u j ^ q) (syndrome x v j ^ q)
theorem graph_slice_map {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (m h : ℕ) :
    (planeSlice q x u v m h).map
        ((algebraMap (Polynomial F) (GenericLayer.GenericField F)).comp (graph q).toRingHom) =
      (Strata.parameterRelation q x u v m h).map (algebraMap (Polynomial F) (GenericLayer.GenericField F)) := by
  apply Matrix.ext
  intro j b
  change algebraMap (Polynomial F) (GenericLayer.GenericField F)
      (graph q (planeSyndrome q x u v b.1 (b.2.val + j.val))) =
    algebraMap (Polynomial F) (GenericLayer.GenericField F)
      (Principal.parameterSyndromes q x u v b.1 (b.2.val + j.val))
  rw [graph_syndrome]
theorem graph_stack_map {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (L t : ℕ) :
    (planeStack q x u v L t).map
        ((algebraMap (Polynomial F) (GenericLayer.GenericField F)).comp (graph q).toRingHom) =
      (stacked q x u v L t).map (algebraMap (Polynomial F) (GenericLayer.GenericField F)) := by
  apply Matrix.ext
  intro b j
  change algebraMap (Polynomial F) (GenericLayer.GenericField F)
      (graph q (planeSyndrome q x u v b.1 (b.2.val + j.val))) =
    algebraMap (Polynomial F) (GenericLayer.GenericField F)
      (Principal.parameterSyndromes q x u v b.1 (b.2.val + j.val))
  rw [graph_syndrome]
private theorem map_syndrome {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (f : F →+* E)
    (x w : ι → F) (j : ℕ) :
    f (syndrome x w j) = syndrome (fun i => f (x i)) (fun i => f (w i)) j := by
  simp only [syndrome, weight, map_sum, map_mul, map_pow, map_inv₀, map_prod, map_sub]
theorem certificate_kernel {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) [ExpChar F q] (x u v : ι → F) (hx : Function.Injective x)
    (hfix : ∀ i, x i ^ q = x i) (k m h : ℕ)
    (hkm : k + m = Fintype.card ι)
    (R : Strata.PolynomialRelationCertificate q x u v k h) :
    ((Strata.parameterRelation q x u v m h).map
      (algebraMap (Polynomial F) (GenericLayer.GenericField F))).mulVec
      (fun j => algebraMap (Polynomial F) (GenericLayer.GenericField F) (R.coefficients j)) = 0 := by
  classical
  let E := GenericLayer.GenericField F
  let φ := algebraMap (Polynomial F) E
  let f := φ.comp Polynomial.C
  let y := fun i => f (x i)
  let z := φ Polynomial.X
  let w : Fin 2 → ι → E := fun b i =>
    if b = 0 then f (u i) + z * f (v i)
    else f (u i ^ q) + z ^ q * f (v i ^ q)
  let P (b : Fin 2) : (Polynomial E) := (Principal.assemble (fun j => R.coefficients (b, j))).map φ
  have hmoment (b : Fin 2) (j : ℕ) :
      φ (Principal.parameterSyndromes q x u v b j) = syndrome y (w b) j := by
    by_cases hb : b = 0
    · simp only [Principal.parameterSyndromes, hb, ite_true, map_add, map_mul]
      change f (syndrome x u j) + z * f (syndrome x v j) = _
      rw [map_syndrome, map_syndrome]
      simpa only [w, hb, ite_true, one_mul] using
        (Principal.syndrome_linear y (fun i => f (u i)) (fun i => f (v i)) 1 z j).symm
    · simp only [Principal.parameterSyndromes, hb, ite_false, map_add, map_mul]
      rw [φ.map_pow Polynomial.X]
      change f (syndrome x u j ^ q) + z ^ q * f (syndrome x v j ^ q) = _
      rw [← syndrome_frobenius q x hfix, ← syndrome_frobenius q x hfix,
        map_syndrome, map_syndrome]
      simpa only [w, hb, ite_false, one_mul] using
        (Principal.syndrome_linear y (fun i => f (u i ^ q)) (fun i => f (v i ^ q)) 1 (z ^ q) j).symm
  have hnodes (i : ι) :
      (P 0).eval (y i) * w 0 i + (P 1).eval (y i) * w 1 i =
        (R.output.map φ).eval (y i) := by
    have he := congrArg φ (R.nodes i)
    simpa only [P, y, f, RingHom.comp_apply, z, w, zero_ne_one, one_ne_zero,
      ite_true, ite_false, map_add, map_mul, map_pow, eval_map_apply] using he
  have hP (b : Fin 2) : (P b).natDegree ≤ h := natDegree_map_le.trans (R.x_degree b)
  rw [Strata.parameterRelation_map]
  apply (Strata.relation_equations _ m h _).mpr
  intro j
  have hcoeff (b : Fin 2) (l : Fin (h + 1)) :
      φ (R.coefficients (b, l)) = (P b).coeff l.val := by
    change φ (R.coefficients (b, l)) =
      ((Principal.assemble (fun j => R.coefficients (b, j))).map φ).coeff l.val
    rw [coeff_map, Principal.assemble_coeff]
  change (∑ b : Fin 2, ∑ l : Fin (h + 1),
    φ (R.coefficients (b, l)) * φ (Principal.parameterSyndromes q x u v b (l.val + j.val))) = 0
  simp only [Fin.sum_univ_two, hmoment, hcoeff]
  change (∑ l : Fin (h + 1), (P 0).coeff l.val * syndrome y (w 0) (l.val + j.val)) +
    (∑ l : Fin (h + 1), (P 1).coeff l.val * syndrome y (w 1) (l.val + j.val)) = 0
  rw [← Strata.syndrome_polynomial_multiple y (w 0) _ _ _ (hP 0),
    ← Strata.syndrome_polynomial_multiple y (w 1) _ _ _ (hP 1)]
  have hlin := Principal.syndrome_linear y
    (fun i => (P 0).eval (y i) * w 0 i) (fun i => (P 1).eval (y i) * w 1 i) 1 1 j.val
  simp only [one_mul] at hlin
  rw [← hlin]
  simp_rw [hnodes]
  exact Strata.syndrome_eval_zero y (f.injective.comp hx) _ (k + h) j.val
    (degree_map_le.trans_lt R.output_degree) (by have := j.isLt; omega)
end
end K1_11_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_11
noncomputable section
open K1 FrobeniusLocator
def nativePuncture (deleted : Finset I) : Puncture deleted := by
  classical
  let kept := Finset.univ \ deleted
  let idx := kept.equivFin.symm
  refine ⟨kept.card, idx.toEmbedding.trans (Function.Embedding.subtype _), ?_, ?_⟩
  · intro i
    constructor
    · rintro ⟨j, rfl⟩
      exact (Finset.mem_sdiff.mp (idx j).property).2
    · intro hi
      let old : kept := ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩
      exact ⟨idx.symm old, congrArg Subtype.val (idx.apply_symm_apply old)⟩
  · simpa only [kept, Finset.card_univ, ProximityPrize.Benchmark.IRSProfile.card_index] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ deleted)
def indexedSupport {deleted : Finset I} (P : Puncture deleted) (S : Finset I) : Finset (Fin P.N) :=
  Finset.univ.filter fun i => P.index i ∈ S
theorem mem_indexedSupport {deleted : Finset I} (P : Puncture deleted) (S : Finset I)
    (i : Fin P.N) : i ∈ indexedSupport P S ↔ P.index i ∈ S := by simp [indexedSupport]
theorem indexedSupport_card {deleted : Finset I} (P : Puncture deleted) (S : Finset I)
    (hS : ∀ i ∈ S, i ∉ deleted) : (indexedSupport P S).card = S.card := by
  have heq : (indexedSupport P S).map P.index = S := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact (mem_indexedSupport P S j).mp hj
    · intro hi
      obtain ⟨j, hj⟩ := (P.retained i).mpr (hS i hi)
      refine Finset.mem_map.mpr ⟨j, (mem_indexedSupport P S j).mpr ?_, hj⟩
      rwa [hj]
  calc
    (indexedSupport P S).card = ((indexedSupport P S).map P.index).card := (Finset.card_map _).symm
    _ = S.card := congrArg Finset.card heq
end
end K1_11
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace K1_11_2
noncomputable section
open K1 K1_11 MvPolynomial
def OmitsMessages {F : Type*} [Field F] (Q : MvPolynomial (Fin 5) F) : Prop :=
  Q.degreeOf 1 = 0 ∧ Q.degreeOf 2 = 0
def graph {F : Type*} [Field F] (q : ℕ) :
    MvPolynomial (Fin 5) F →ₐ[F] Polynomial (Polynomial F) :=
  aeval ![Polynomial.X, 0, 0, Polynomial.C Polynomial.X, (Polynomial.C Polynomial.X)^q]
def nodeWordImages {F : Type*} [Field F] (x a b c d : F) : Fin 5 → MvPolynomial (Fin 5) F :=
  ![MvPolynomial.C x, MvPolynomial.C a + MvPolynomial.X 3 * MvPolynomial.C b,
    MvPolynomial.C c + MvPolynomial.X 4 * MvPolynomial.C d, MvPolynomial.X 3, MvPolynomial.X 4]
def nodeWordMap {F : Type*} [Field F] (x a b c d : F) :
    MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval (nodeWordImages x a b c d)
def sWeight {F : Type*} [Field F] (U V : MvPolynomial (Fin 5) F) : ℕ :=
  max (1 + U.degreeOf 3) (V.degreeOf 3)
def tWeight {F : Type*} [Field F] (U V : MvPolynomial (Fin 5) F) : ℕ :=
  max (U.degreeOf 4) (1 + V.degreeOf 4)
structure ReducedPair {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : IndependentLift R) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : OmitsMessages U
  V_omits : OmitsMessages V
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  relPrime : IsRelPrime U V
  height : max (U.degreeOf 0) (V.degreeOf 0) = D.height
  boxes : U.degreeOf 3 ≤ 1 ∧ U.degreeOf 4 ≤ 2 ∧ V.degreeOf 3 ≤ 2 ∧ V.degreeOf 4 ≤ 1
  graphU : graph p U = Polynomial.C A.content * D.U
  graphV : graph p V = Polynomial.C A.content * D.V
structure PlaneOutput (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (H : ℕ) (U V : MvPolynomial (Fin 5) K) where
  W : MvPolynomial (Fin 5) K
  omits : OmitsMessages W
  height : W.degreeOf 0 ≤ 131071 + H
  degreeS : W.degreeOf 3 ≤ sWeight U V
  degreeT : W.degreeOf 4 ≤ tWeight U V
  node : ∀ i : Fin P.N,
    nodeWordMap (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
      (u 0 (P.index i)^p) (u 1 (P.index i)^p) (U * MvPolynomial.X 1 + V * MvPolynomial.X 2 - W) = 0
end
end K1_11_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K1_11_2
noncomputable section
open K1_11 MvPolynomial
variable {F : Type*} [Field F]
def contactConstant : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval ![0,0,0,MvPolynomial.X 3,MvPolynomial.X 4]
theorem contactConstant_monomial (e : Fin 5 →₀ ℕ) (a : F) :
    contactConstant (monomial e a)=if e.weight contactWeight<1 then monomial e a else 0 := by
  classical
  rw [contactConstant,aeval_monomial]
  by_cases h0 : e 0=0 <;> by_cases h1 : e 1=0 <;> by_cases h2 : e 2=0 <;>
    simp [Finsupp.prod_fintype,Fin.prod_univ_succ,contactWeight,weight5,
      h0,h1,h2,monomial_eq]
theorem truncation_one_monomial (e : Fin 5 →₀ ℕ) (a : F) :
    weightedTruncation contactWeight 1 (monomial e a)=
      if e.weight contactWeight<1 then monomial e a else 0 := by
  classical
  ext f
  by_cases hfe : e=f
  · subst f
    split_ifs <;> simp_all [coeff_weightedTruncation,MvPolynomial.coeff_monomial]
  · split_ifs <;> simp_all [coeff_weightedTruncation,MvPolynomial.coeff_monomial]
theorem contactConstant_eq_truncation (P : MvPolynomial (Fin 5) F) :
    contactConstant P=weightedTruncation contactWeight 1 P := by
  induction P using MvPolynomial.induction_on' with
  | monomial e a => rw [contactConstant_monomial,truncation_one_monomial]
  | add P Q hp hq => simp only [map_add,hp,hq]
theorem exact_contact_one_of_gradient (P : MvPolynomial (Fin 5) F) (i : Fin 5)
    (hi : contactWeight i=1) (hvalue : contactConstant P=0)
    (hgradient : contactConstant (pderiv i P)≠0) :
    (contactLift contactWeight P).natTrailingDegree=1 := by
  have hzero : P∈restrictWeightedOrder contactWeight 1 := by
    apply (weightedTruncation_eq_zero_iff _ _ _).mp
    rwa [← contactConstant_eq_truncation]
  obtain ⟨e,he⟩ := support_nonempty.mpr hgradient
  have hec := mem_support_iff.mp he
  rw [contactConstant_eq_truncation,coeff_weightedTruncation] at hec
  have heweight : e.weight contactWeight<1 := by
    by_contra hn
    exact hec (ite_eq_right hn)
  rw [ite_eq_left heweight,coeff_pderiv] at hec
  have hcoeff : P.coeff (e+Finsupp.single i 1)≠0 := left_ne_zero_of_mul hec
  have hweight : (e+Finsupp.single i 1).weight contactWeight=1 := by
    rw [map_add,Finsupp.weight_single,one_smul,hi]
    omega
  exact contact_order_one_of_coefficient contactWeight P hzero _ hweight hcoeff
theorem pderiv_zero_of_degree_zero (i : Fin 5) (P : MvPolynomial (Fin 5) F)
    (hP : P.degreeOf i=0) : pderiv i P=0 := by
  ext e
  rw [coeff_pderiv]
  have hc : P.coeff (e+Finsupp.single i 1)=0 := by
    apply notMem_support_iff.mp
    apply notMem_support_of_degreeOf_lt i
    simp [hP]
  simp [hc]
theorem linear_form_message_derivatives (U V R : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hR : OmitsMessages R) :
    pderiv 1 (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R)=U ∧ pderiv 2 (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R)=V := by
  constructor <;> simp [pderiv_zero_of_degree_zero _ U hU.1,
    pderiv_zero_of_degree_zero _ U hU.2,pderiv_zero_of_degree_zero _ V hV.1,
    pderiv_zero_of_degree_zero _ V hV.2,pderiv_zero_of_degree_zero _ R hR.1,
    pderiv_zero_of_degree_zero _ R hR.2]
theorem contactShift_message_derivative (x a b c d : F) (P : MvPolynomial (Fin 5) F)
    (i : Fin 5) (hi : i=1 ∨ i=2) :
    pderiv i (contactShift x a b c d P)=contactShift x a b c d (pderiv i P) := by
  have hvar (j : Fin 5) : pderiv i (contactShift x a b c d (MvPolynomial.X j))=
      contactShift x a b c d (pderiv i (MvPolynomial.X j)) := by
    rcases hi with rfl | rfl
    all_goals fin_cases j <;> simp [contactShift,shiftImages]
  induction P using MvPolynomial.induction_on with
  | C r => simp [contactShift]
  | add P Q hp hq => simp only [map_add,hp,hq]
  | mul_X P j hp => simp only [map_mul,pderiv_mul,map_add,hp,hvar]
theorem linear_relation_node_contact_one (x a b c d : F)
    (U V R : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hR : OmitsMessages R)
    (hnode : contactConstant (contactShift x a b c d (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R))=0)
    (hnonzero : contactConstant (contactShift x a b c d U)≠0 ∨
      contactConstant (contactShift x a b c d V)≠0) :
    (contactLift contactWeight (contactShift x a b c d (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R))).natTrailingDegree=1 := by
  have hd := linear_form_message_derivatives U V R hU hV hR
  rcases hnonzero with hu | hv
  · apply exact_contact_one_of_gradient _ 1 (by decide) hnode
    rw [contactShift_message_derivative x a b c d _ 1 (Or.inl rfl),hd.1]
    exact hu
  · apply exact_contact_one_of_gradient _ 2 (by decide) hnode
    rw [contactShift_message_derivative x a b c d _ 2 (Or.inr rfl),hd.2]
    exact hv
def messageTag (P : MvPolynomial (Fin 5) F) (a b : ℕ) : Prop :=
  ∀ e∈P.support,e 1=a ∧ e 2=b
theorem omitted_message_tag (P : MvPolynomial (Fin 5) F) (hP : OmitsMessages P) : messageTag P 0 0 := by
  rcases hP with ⟨hP1,hP2⟩
  intro e he
  have h1 := le_degreeOf_of_mem_support 1 he
  have h2 := le_degreeOf_of_mem_support 2 he
  exact ⟨by omega,by omega⟩
theorem relatively_prime_not_both_eval_zero {R : Type*} [CommRing R] [IsDomain R]
    (U V : Polynomial R) (hUV : IsRelPrime U V) (x : R) : U.eval x≠0 ∨ V.eval x≠0 := by
  by_contra hn
  push Not at hn
  have hu : Polynomial.X-Polynomial.C x∣U := Polynomial.dvd_iff_isRoot.mpr hn.1
  have hv : Polynomial.X-Polynomial.C x∣V := Polynomial.dvd_iff_isRoot.mpr hn.2
  exact Polynomial.not_isUnit_X_sub_C x (hUV hu hv)
def partialXMap (x : F) : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval ![C x,MvPolynomial.X 1,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]
theorem contactConstant_shift (x a b c d : F) (P : MvPolynomial (Fin 5) F) :
    contactConstant (contactShift x a b c d P)=nodeWordMap x a b c d P := by
  rw [contactShift,aeval_eq_bind₁,contactConstant,aeval_bind₁]
  have hf : (fun i => aeval ![0,0,0,MvPolynomial.X 3,MvPolynomial.X 4] (shiftImages x a b c d i))=
      nodeWordImages x a b c d := by
    funext i
    fin_cases i <;> simp [shiftImages,nodeWordImages]
  rw [hf]
  rfl
theorem nodeWord_omitted_eq_partialX (x a b c d : F) (P : MvPolynomial (Fin 5) F)
    (hP : OmitsMessages P) : nodeWordMap x a b c d P=partialXMap x P := by
  change eval₂ C (nodeWordImages x a b c d) P=eval₂ C ![C x,MvPolynomial.X 1,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4] P
  apply eval₂_congr
  intro i e hi hc
  have he : e∈P.support := mem_support_iff.mpr hc
  have ht := omitted_message_tag P hP e he
  have hin : e i≠0 := Finsupp.mem_support_iff.mp hi
  have h1 : i≠1 := by intro hi1; subst i; exact hin ht.1
  have h2 : i≠2 := by intro hi2; subst i; exact hin ht.2
  fin_cases i <;> simp [nodeWordImages] at *
theorem partialX_via_polynomial (x : F) (P : MvPolynomial (Fin 5) F) :
    partialXMap x P=rename Fin.succ ((finSuccEquiv F 4 P).eval (C x)) := by
  have heq : (partialXMap x).toRingHom=
      (rename (Fin.succ : Fin 4 → Fin 5)).toRingHom.comp ((Polynomial.evalRingHom (C x)).comp (finSuccEquiv F 4).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [partialXMap,finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [partialXMap, finSuccEquiv_X_zero]
      · change partialXMap x (MvPolynomial.X j.succ) =
          rename Fin.succ ((finSuccEquiv F 4 (MvPolynomial.X j.succ)).eval (C x))
        rw [finSuccEquiv_X_succ, Polynomial.eval_C, rename_X]
        fin_cases j <;> simp [partialXMap]
  exact RingHom.congr_fun heq P
theorem relatively_prime_polynomial_view (U V : MvPolynomial (Fin 5) F)
    (hUV : IsRelPrime U V) : IsRelPrime (finSuccEquiv F 4 U) (finSuccEquiv F 4 V) := by
  intro d hdU hdV
  have hu : (finSuccEquiv F 4).symm d∣U := by
    obtain ⟨q,hq⟩ := hdU
    refine ⟨(finSuccEquiv F 4).symm q,?_⟩
    apply (finSuccEquiv F 4).injective
    simpa only [map_mul,AlgEquiv.apply_symm_apply] using hq
  have hv : (finSuccEquiv F 4).symm d∣V := by
    obtain ⟨q,hq⟩ := hdV
    refine ⟨(finSuccEquiv F 4).symm q,?_⟩
    apply (finSuccEquiv F 4).injective
    simpa only [map_mul,AlgEquiv.apply_symm_apply] using hq
  have hu' := (hUV hu hv).map (finSuccEquiv F 4).toRingHom
  change IsUnit ((finSuccEquiv F 4) ((finSuccEquiv F 4).symm d)) at hu'
  simpa only [AlgEquiv.apply_symm_apply] using hu'
theorem relatively_prime_node_nondegenerate (x a b c d : F)
    (U V : MvPolynomial (Fin 5) F) (hUV : IsRelPrime U V)
    (hU : OmitsMessages U) (hV : OmitsMessages V) :
    nodeWordMap x a b c d U≠0 ∨ nodeWordMap x a b c d V≠0 := by
  have hn := relatively_prime_not_both_eval_zero (finSuccEquiv F 4 U) (finSuccEquiv F 4 V)
    (relatively_prime_polynomial_view U V hUV) (C x)
  rw [nodeWord_omitted_eq_partialX x a b c d U hU,
    nodeWord_omitted_eq_partialX x a b c d V hV,partialX_via_polynomial,partialX_via_polynomial]
  have hinj : Function.Injective (rename (R:=F) (Fin.succ : Fin 4 → Fin 5)) :=
    rename_injective _ (Fin.succ_injective 4)
  rcases hn with hu | hv
  · left
    exact fun hz => hu (hinj (hz.trans (map_zero _).symm))
  · right
    exact fun hz => hv (hinj (hz.trans (map_zero _).symm))
theorem linear_relation_contact_order_one (x a b c d : F)
    (U V R : MvPolynomial (Fin 5) F) (hUV : IsRelPrime U V)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hR : OmitsMessages R)
    (hnode : nodeWordMap x a b c d (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R)=0) :
    (contactLift contactWeight (contactShift x a b c d (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R))).natTrailingDegree=1 := by
  apply linear_relation_node_contact_one x a b c d U V R hU hV hR
  · rwa [contactConstant_shift]
  · simpa only [contactConstant_shift] using relatively_prime_node_nondegenerate x a b c d U V hUV hU hV
end
end K1_11_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace K1_11
noncomputable section
open K1 FrobeniusLocator MvPolynomial
open scoped BigOperators
variable {u : Words} {deleted : Finset I} {P : Puncture deleted}
  {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}
theorem seed_eq_of_mismatch {F : Type*} [Field F] {s t a b c d : F}
    (hs : a + s * b = c + s * d) (ht : a + t * b = c + t * d)
    (hm : a ≠ c ∨ b ≠ d) : s = t := by
  have hz : (s - t) * (b - d) = 0 := by linear_combination hs - ht
  rcases mul_eq_zero.mp hz with h | h
  · exact sub_eq_zero.mp h
  · have hb := sub_eq_zero.mp h
    exact False.elim (hm.elim
      (fun hne => hne (by simpa only [hb, add_left_inj] using hs))
      (fun hne => hne hb))
variable (chart : TaylorChart u P F b Λ)
end
end K1_11
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_11_1
noncomputable section
open Polynomial FrobeniusLocator
open scoped BigOperators
variable {F : Type} [Field F]
theorem degreeOf_coordinate {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (b i : Fin 2) (j : Fin (h + 1)) : (Q (b, j)).degreeOf i ≤ blockDegree Q b i :=
  Finset.le_sup (f := fun j : Fin (h + 1) => (Q (b, j)).degreeOf i) (Finset.mem_univ j)
theorem seedPositions_injective : Function.Injective seedPositions := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | contradiction
private theorem rename_degree_zero (a : Seeds F) (i : Fin 5) (hi : i ∉ Set.range seedPositions) :
    (MvPolynomial.rename seedPositions a).degreeOf i = 0 := by
  by_contra h
  obtain ⟨j, _, hej⟩ := MvPolynomial.mem_vars_rename seedPositions a
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr h)
  exact hi ⟨j, hej⟩
private theorem intoFive_degree {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (b : Fin 2) (i : Fin 5) (a d : ℕ)
    (ha : ∀ j : Fin (h + 1), (MvPolynomial.rename seedPositions (Q (b, j))).degreeOf i ≤ a)
    (hd : ∀ j : Fin (h + 1), ((MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) F) ^ j.val).degreeOf i ≤ d) :
    (intoFive (planePair Q b)).degreeOf i ≤ a + d := by
  classical
  simp only [planePair, Principal.assemble, map_sum, intoFive, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_monomial, AlgHom.toRingHom_eq_coe]
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  exact Finset.sup_le fun j _ => (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add (ha j) (hd j))
theorem intoFive_height {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2) :
    (intoFive (planePair Q b)).degreeOf 0 ≤ h := by
  simpa only [zero_add] using intoFive_degree Q b 0 0 h
    (fun j => (rename_degree_zero (Q (b, j)) 0 (by
      rintro ⟨i, hi⟩
      fin_cases i <;> contradiction)).le)
    (fun j => by rw [MvPolynomial.degreeOf_X_self_pow]; omega)
theorem intoFive_seed_degree {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (b i : Fin 2) :
    (intoFive (planePair Q b)).degreeOf (seedPositions i) ≤ blockDegree Q b i := by
  simpa only [add_zero] using intoFive_degree Q b (seedPositions i) (blockDegree Q b i) 0
    (fun j => by rw [MvPolynomial.degreeOf_rename_of_injective seedPositions_injective]; exact degreeOf_coordinate Q b i j)
    (fun j => (MvPolynomial.degreeOf_X_pow_of_ne _ (by fin_cases i <;> decide)).le)
theorem intoFive_omitted {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2)
    (i : Fin 5) (hi : i = 1 ∨ i = 2) :
    (intoFive (planePair Q b)).degreeOf i = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [zero_add] using intoFive_degree Q b i 0 0
    (fun j => (rename_degree_zero (Q (b, j)) i (by
      rintro ⟨l, rfl⟩
      fin_cases l <;> rcases hi with he | he <;> contradiction)).le)
    (fun j => (MvPolynomial.degreeOf_X_pow_of_ne _ (by rcases hi with rfl | rfl <;> decide)).le)
private def fromFive : MvPolynomial (Fin 5) F →ₐ[F] (Polynomial (Seeds F)) :=
  MvPolynomial.aeval ![Polynomial.X, 0, 0, Polynomial.C (MvPolynomial.X 0), Polynomial.C (MvPolynomial.X 1)]
private theorem fromFive_rename (a : Seeds F) :
    fromFive (MvPolynomial.rename seedPositions a) = Polynomial.C a := by
  have he : (fromFive (F := F)).toRingHom.comp (MvPolynomial.rename seedPositions).toRingHom =
      Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [fromFive]
    · intro i
      fin_cases i <;> simp [fromFive, seedPositions]
  exact RingHom.congr_fun he a
private theorem fromFive_intoFive (A : (Polynomial (Seeds F))) : fromFive (intoFive A) = A := by
  have he : (fromFive (F := F)).toRingHom.comp intoFive = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a
      change fromFive (intoFive (Polynomial.C a)) = Polynomial.C a
      rw [intoFive, coe_eval₂RingHom, eval₂_C]
      exact fromFive_rename a
    · simp [fromFive, intoFive]
  exact RingHom.congr_fun he A
theorem intoFive_primitive {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (hQ : coefficientPrimitive Q) (a : Seeds F)
    (hU : MvPolynomial.rename seedPositions a ∣ intoFive (planePair Q 0))
    (hV : MvPolynomial.rename seedPositions a ∣ intoFive (planePair Q 1)) :
    IsUnit a := by
  have hd (b : Fin 2) : Polynomial.C a ∣ planePair Q b := by
    have hb : MvPolynomial.rename seedPositions a ∣ intoFive (planePair Q b) := by
      fin_cases b
      · exact hU
      · exact hV
    have ht := map_dvd (fromFive (F := F)) hb
    simpa only [fromFive_rename, fromFive_intoFive] using ht
  apply hQ
  rintro ⟨b, j⟩
  simpa only [planePair, Principal.assemble_coeff] using
    (Polynomial.C_dvd_iff_dvd_coeff _ _).mp (hd b) j.val
private def graphFive (q : ℕ) : MvPolynomial (Fin 5) F →ₐ[F] (Polynomial (Polynomial F)) :=
  MvPolynomial.aeval ![Polynomial.X, 0, 0, Polynomial.C (Polynomial.X : (Polynomial F)),
    (Polynomial.C (Polynomial.X : (Polynomial F))) ^ q]
private theorem graphFive_rename (q : ℕ) (a : Seeds F) :
    graphFive q (MvPolynomial.rename seedPositions a) = Polynomial.C (graph q a) := by
  have he : (graphFive (F := F) q).toRingHom.comp (MvPolynomial.rename seedPositions).toRingHom =
      Polynomial.C.comp (graph q).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [graphFive, graph]
    · intro i
      fin_cases i <;> simp [graphFive, graph, seedPositions]
  exact RingHom.congr_fun he a
theorem graph_intoFive (q : ℕ) (A : (Polynomial (Seeds F))) :
    MvPolynomial.aeval ![Polynomial.X, 0, 0, Polynomial.C (Polynomial.X : (Polynomial F)),
      (Polynomial.C (Polynomial.X : (Polynomial F))) ^ q] (intoFive A) =
      A.map (graph q).toRingHom := by
  change graphFive q (intoFive A) = _
  have he : (graphFive (F := F) q).toRingHom.comp intoFive = Polynomial.mapRingHom (graph q).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change graphFive q (intoFive (Polynomial.C a)) = (Polynomial.C a).map (graph q).toRingHom
      rw [intoFive, coe_eval₂RingHom, eval₂_C, Polynomial.map_C]
      exact graphFive_rename q a
    · simp [graphFive, intoFive]
  exact RingHom.congr_fun he A
end
end K1_11_1
end
section
set_option autoImplicit false
namespace K1_11_3
noncomputable section
open K1 K1_11 MvPolynomial
def derivativeChart {F : Type*} [CommRing F] (G : MvPolynomial (Fin 4) F) (j : ℕ) :
    MvPolynomial (Fin 4) F :=
  (fun H : MvPolynomial (Fin 4) F => pderiv 1 H)^[j] G
def SimpleRoot {F : Type*} [Field F] (G : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) : Prop :=
  aeval (scalarImages D s t) G = 0 ∧
    aeval (scalarImages D s t) (pderiv 1 G) ≠ 0
def implicitDeriv {F : Type*} [CommRing F] (G H : MvPolynomial (Fin 4) F) :
    MvPolynomial (Fin 4) F :=
  pderiv 1 G * pderiv 0 H - pderiv 0 G * pderiv 1 H
def implicitNumerator {F : Type*} [CommRing F] (G : MvPolynomial (Fin 4) F) :
    ℕ → MvPolynomial (Fin 4) F
  | 0 => -pderiv 0 G
  | n + 1 =>
    pderiv 1 G * implicitDeriv G (implicitNumerator G n) -
      C (↑(2 * n + 1) : F) * implicitNumerator G n * implicitDeriv G (pderiv 1 G)
def paddedTaylorCoeff {F : Type*} [Field F] (G : MvPolynomial (Fin 4) F)
    (w : ℕ) : ℕ → MvPolynomial (Fin 4) F
  | 0 => MvPolynomial.X 1 * pderiv 1 G ^ (2 * w - 1)
  | n + 1 =>
    C ((↑(Nat.factorial (n + 1)) : F)⁻¹) *
      implicitNumerator G n * pderiv 1 G ^ (2 * w - 1 - (2 * n + 1))
end
end K1_11_3
end

end Merged6967_Fast065
