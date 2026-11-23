import ProximityPrize.SubmissionLower.ZZekYUb
import ProximityPrize.SubmissionLower.ZbbSEle
import ProximityPrize.SubmissionLower.ZCuFj9c
import ProximityPrize.SubmissionLower.Z4ukc6a
import ProximityPrize.SubmissionLower.CmpCSum
import ProximityPrize.SubmissionLower.ZjZ6ihd
set_option Elab.async false
section
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace qG2jkNc
open aR (Shape)
open qmb8rCe (sumN sumN_eq fullCost)
open qOPkAYa (Filed base checked countedRank fastMass fastPart flags part_tail sum_add)
private abbrev a :Shape :=⟨164,50,19⟩
private abbrev stock :=base a
private abbrev rank :=countedRank a
private abbrev full:=fullCost a 163
private abbrev part:=fastPart a 163
local notation "ck!" fn:arg start:arg count:arg ans:arg prev:arg =>
 checked (f :=fn) (n:=start) (k :=count) (y :=ans) prev rfl
private theorem s0:sumN stock 0=0:=rfl
private theorem s10 :sumN stock 10=45595:=ck! stock 0 10 45595 s0
private theorem s20:sumN stock 20=307615:=ck! stock 10 10 262020 s10
private theorem s30:sumN stock 30=912365:=ck! stock 20 10 604750 s20
private theorem s40:sumN stock 40=1822905:=ck! stock 30 10 910540 s30
private theorem stock_prefix :sumN stock 50=2869920:=ck! stock 40 10 1047015 s40
private theorem r0:sumN rank 0=0:=rfl
private theorem r5:sumN rank 5=7385:=ck! rank 0 5 7385 r0
private theorem dz :sumN rank 10=45595:=ck! rank 5 5 38210 r5
private theorem gx :sumN rank 15=138380:=ck! rank 10 5 92785 dz
private theorem jV:sumN rank 20=307615:=ck! rank 15 5 169235 gx
private theorem nP:sumN rank 25=566615:=ck! rank 20 5 259000 jV
private theorem xM:sumN rank 30=912365:=ck! rank 25 5 345750 nP
private theorem Cp:sumN rank 35=1338060:=ck! rank 30 5 425695 xM
private theorem Hz :sumN rank 40=1822905:=ck! rank 35 5 484845 Cp
private theorem Xw:sumN rank 45=2341400:=ck! rank 40 5 518495 Hz
private theorem rank_prefix :sumN rank 50=2869920:=ck! rank 45 5 528520 Xw
private theorem f0:sumN full 0=0:=rfl
private theorem f5:sumN full 5=1859816:=ck! full 0 5 1859816 f0
private theorem Zd:sumN full 10=11510807:=ck! full 5 5 9650991 f5
private theorem f15:sumN full 15=35025848:=ck! full 10 5 23515041 Zd
private theorem f20:sumN full 20=78074689:=ck! full 15 5 43048841 f15
private theorem f25:sumN full 25=0x894cbf0:=ck! full 20 5 65894575 f20
private theorem f30:sumN full 30=0xdca2331 :=ck! full 25 5 87381825 f25
private theorem f35:sumN full 35=0x14229780:=ck! full 30 5 0x658744f f30
private theorem f40:sumN full 40=0x1b3c05c3:=ck! full 35 5 0x7196e43 f35
private theorem f45:sumN full 45=0x22a32b24 :=ck! full 40 5 0x7672561 f40
private theorem full_prefix :sumN full 50=0x29f17b32 :=ck! full 45 5 0x74e500e f45
private theorem p0:sumN part 0=0:=rfl
private theorem p8:sumN part 8=1724694 :=ck! part 0 8 1724694 p0
private theorem p14 :sumN part 14=7112476:=ck! part 8 6 5387782 p8
private theorem p19:sumN part 19=15101618:=ck! part 14 5 7989142 p14
private theorem p23:sumN part 23=23680638:=ck! part 19 4 8579020 p19
private theorem p27:sumN part 27=33781818:=ck! part 23 4 10101180 p23
private theorem p30:sumN part 30=42098093:=ck! part 27 3 8316275 p27
private theorem p33:sumN part 33=50857806:=ck! part 30 3 8759713 p30
private theorem p35:sumN part 35=56862576:=ck! part 33 2 6004770 p33
private theorem p37:sumN part 37=62948146:=ck! part 35 2 6085570 p35
private theorem p39:sumN part 39=69076730:=ck! part 37 2 6128584 p37
private theorem p41 :sumN part 41=75215694 :=ck! part 39 2 6138964 p39
private theorem p43:sumN part 43=81337332 :=ck! part 41 2 6121638 p41
private theorem p45:sumN part 45=87418642 :=ck! part 43 2 6081310 p43
private theorem p46:sumN part 46=90438217:=ck! part 45 1 3019575 p45
private theorem p47:sumN part 47=93441102 :=ck! part 46 1 3002885 p46
private theorem p48:sumN part 48=96425645:=ck! part 47 1 2984543 p47
private theorem p49:sumN part 49=99390446:=ck! part 48 1 2964801 p48
private theorem part_prefix :sumN part 50=0x6197f8e :=ck! part 49 1 2943904 p49
private theorem sum_const (n x :ℕ) :sumN (fun _=>x) n=n*x := by
 rw [sumN_eq,Finset.sum_const,Finset.card_range]
 rfl
private theorem sum_mul (x n:ℕ) (f :ℕ→ℕ) :
  sumN (fun i=>x*f i) n=x*sumN f n:= by
 simp only [sumN_eq,Finset.mul_sum]
private abbrev slots (f :ℕ→ℕ→ℕ) :=
 sumN (fun c=>sumN (f c) (51-2*c)) 20
private theorem slots_eq (f :ℕ→ℕ→ℕ) {q:ℕ} (hq:50≤q) :
   sumN (fun c=>sumN (f c) (min (q-c) (50-2*c)+1))
     (min q 19+1)=slots f := by
 rw [min_eq_right (by omega :19≤q)]
 simp only [slots,sumN_eq]
 refine Finset.sum_congr rfl fun c hc => ?_
 have hc' := Finset.mem_range.mp hc
 rw [min_eq_right (by omega :50-2*c≤q-c),show 50-2*c+1=51-2*c by omega]
private theorem slot_add (f g:ℕ→ℕ→ℕ) :
  slots (fun c b=>f c b+g c b)=slots f+slots g:= by
 simp only [slots,sumN_eq,Finset.sum_add_distrib]
private theorem slot_mul (x :ℕ) (f :ℕ→ℕ→ℕ) :
  slots (fun c b=>x*f c b)=x*slots f := by
 simp only [slots,sumN_eq,← Finset.mul_sum]
private theorem slot_one :slots (fun _ _=>1)=640:=rfl
private theorem slot_index :slots (fun c b=>b+2*c)=20750:=rfl
private theorem slot_linear :slots (fun c b=>3*b+5*c)=57500:=rfl
private theorem slot_cross :slots (fun c b=>(b+2*c)*(b+c))=594590:=rfl
private theorem slot_const (x :ℕ) :slots (fun _ _=>x)=640*x := by
 calc
  _=slots (fun _ _=>x*1) := by simp only [mul_one]
  _ = _:= by rw [slot_mul,slot_one,Nat.mul_comm]
private theorem slot_full (x :ℕ) :
   slots (fun c b=>(x+(b+2*c))*(2*x+(b+c))) =
     1280*(x*x)+57500*x+594590:= by
 have h (c b:ℕ) : (x+(b+2*c))*(2*x+(b+c)) =
     (2*x*x)*1 + x*(3*b+5*c)+(b+2*c)*(b+c) := by ring
 simp only [h,slot_add]
 rw [slot_mul (2*x*x) (fun _ _=>1),slot_one,
   slot_mul x (fun c b=>3*b+5*c),slot_linear,slot_cross]
 ring
private theorem mass50:fastMass a 50 0=11250:=rfl
private theorem flags50:flags a 50=357090:=rfl
private theorem stock_tail (q:ℕ) (hq:50≤q) (hb:q≤164) :
    stock q=0*((164-q)*(164-q))+640*(164-q)+32000:= by
  change sumN (fun c=>(min (q-c) (50-2*c)+1)*(214-q)) (min q 19+1)= _
  calc
    _=sumN (fun c=>sumN (fun _=>(164-q)+50) (min (q-c) (50-2*c)+1))
          (min q 19+1) := by
        simp only [sum_const,show 214-q=(164-q)+50 by omega]
    _ = _:= by rw [slots_eq _ hq,slot_const]; ring
private theorem rank_tail (q:ℕ) (hq:50≤q) (_:q≤164) :
   rank q=0*((164-q)*(164-q))+640*(164-q)+32000:= by
 change
   sumN (fun c=>sumN (fun b=>164-q+(b+2*c)) (min (q-c) (50-2*c)+1))
     (min q 19+1)+fastMass a (min q 50) 0= _
 rw [min_eq_right hq,mass50,slots_eq _ hq,slot_add,slot_const,slot_index]
 ring
private theorem full_tail (q:ℕ) (hq:50≤q) (_:q≤164) :
  full q=1280*((164-q)*(164-q))+57500*(164-q)+594590:= by
 change sumN (fun c=>sumN (fun b=>(164-q+(b+2*c))*(328-2*q+(b+c)))
  (min (q-c) (50-2*c)+1)) (min q 19+1)= _
 rw [show 328-2*q=2*(164-q) by omega,slots_eq _ hq,slot_full]
private theorem part_tail_eq (q:ℕ) (hq:50≤q) (_:q≤164) :
  part q=0*((164-q)*(164-q))+22500*(164-q)+357090:= by
 change fastPart a 163 q= _
 rw [part_tail (a :=a) (U:=163) hq mass50 flags50]
 change (328-2*q)*11250+357090= _
 rw [show 328-2*q=2*(164-q) by omega]
 ring
private theorem squares (n:ℕ) :
   6*sumN (fun i=>i*i) (n+1)=n*(n+1)*(2*n+1) := by
 induction n with
 | zero=>rfl
 | succ n ih =>
   rw [sumN,Nat.mul_add,ih]
   ring
private theorem aoV (p l c:ℕ) :
  sumN (fun i=>p*(i*i)+l*i+c) 115=p*500365+l*6555+115*c:= by
 have hs :sumN (fun i=>i*i) 115=500365 :=
  Nat.eq_of_mul_eq_mul_left (by decide :0<6) ((squares 114).trans (by decide))
 have hl:sumN (fun i=>i) 115=6555:= by
  rw [sumN_eq,Finset.sum_range_id]
 rw [sum_add (fun i=>p*(i*i)+l*i) (fun _=>c),
  sum_add (fun i=>p*(i*i)) (fun i=>l*i),sum_mul p _ (fun i=>i*i),hs,
  sum_mul l _ (fun i=>i),hl,sum_const]
private theorem tail {f :ℕ→ℕ} (p l c:ℕ)
  (h : ∀ q,50≤q→q≤164→f q=p*((164-q)*(164-q))+l*(164-q)+c) :
  sumN (fun i=>f (50+i)) 115=p*500365+l*6555+115*c:= by
 rw [← aoV]
 simp only [sumN_eq]
 rw [← Finset.sum_range_reflect (fun i=>p*(i*i)+l*i+c) 115]
 refine Finset.sum_congr rfl fun i hi => ?_
 have hi' := Finset.mem_range.mp hi
 rw [h _ (by omega) (by omega),show 164-(50+i)=115-1-i by omega]
private theorem stock_all:sumN stock 165=10745120 :=
 checked stock_prefix (tail 0 640 32000 stock_tail)
private theorem rank_all:sumN rank 165=10745120 :=
 checked rank_prefix (tail 0 640 32000 rank_tail)
private theorem full_all:sumN full 165=0x6aa8d3a0 :=
 checked full_prefix (tail 1280 57500 594590 full_tail)
private theorem part_all:sumN part 165=0x11569620 :=
 checked part_prefix (tail 0 22500 357090 part_tail_eq)
private theorem filed_of_values {s :Shape} {d n r f p:ℕ}
  (hn:sumN (base s) (s.b+1)=n)
  (hr :sumN (countedRank s) (s.b+1)=r)
  (hf :sumN (fullCost s (s.b-1)) (s.b+1)=f)
  (hp:sumN (fastPart s (s.b-1)) (s.b+1)=p)
  (h₁:r≤n) (h₂:f+p≤ s.b*n+d) :Filed s d:= by
 unfold Filed
 dsimp only
 rw [hn,hr,hf,hp]
 exact ⟨h₁,h₂⟩
theorem proof :qOPkAYa.c2 :=
 filed_of_values (s :=a) (d:=0x13094c39)
  stock_all rank_all full_all part_all le_rfl (by decide)
end qG2jkNc
end
section
set_option autoImplicit true
namespace q5HD6ae
open qqf9uAa.GradeSigns (append)
theorem proof :qqf9uAa.c3:= by
 intro b hlo hhi
 cases b
 case rQ =>
  exact ⟨ordinary2750,append grades2750A (append grades2750B (append grades2750C grades2750D))⟩
 case daL =>
  exact ⟨ordinary2775,append grades2775A (append grades2775B
    (append grades2775C (append grades2775D
    (append grades2775E (append grades2775F
    (append grades2775G (append grades2775H
    (append grades2775I (append grades2775J grades2775K)))))))))⟩
 all_goals first
  | exact ((Nat.not_le_of_lt (by decide)) hlo).elim
  | exact ((Nat.not_lt_of_ge (by decide)) hhi).elim
end q5HD6ae
end
