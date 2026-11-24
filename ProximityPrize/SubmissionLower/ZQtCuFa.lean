import ProximityPrize.SubmissionLower.Z8H1fka
import ProximityPrize.SubmissionLower.ZqZuDUb
set_option Elab.async false
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
