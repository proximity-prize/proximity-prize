import ProximityPrize.SubmissionLower.Z3BnLje
import ProximityPrize.SubmissionLower.ZfPVEHa
set_option Elab.async false
section
set_option autoImplicit true
namespace qaQQvid
open xE (Flag)

open aFM (aM3)

open private count save from ProximityPrize.SubmissionLower.ZfPVEHa


private def countN (d n:ℕ) :ℕ :=
 let (a,b) :=aM3 d n
 a-b
private theorem min_toNat (a b:ℤ) : (min a b).toNat=min a.toNat b.toNat := by omega
private def core (d u l o m:ℕ) :ℕ :=
 let a :=countN d u
 if m=0 then a - countN d (min u l) else
  let Bp:= fun n=>if d< m then 0 else countN (d-m) n
  let b:=Bp (o-3*m)
  let c:=countN d o+Bp l
  if l≤u then a+b-c else b+countN d l-c
private theorem count_eq_countN (d u:ℤ) :
 count d u=if d<0 then 0 else countN d.toNat (u+1).toNat :=rfl
private theorem count_kept (d x m:ℤ) (hd:0≤d) (hm:0≤ m) :
   count (d-m) x =
     if d.toNat< m.toNat then 0 else countN (d.toNat-m.toNat) (x+1).toNat := by
 rw [count_eq_countN]
 have h:d-m<0↔d.toNat< m.toNat := by omega
 simp only [h,show (d-m).toNat=d.toNat-m.toNat by omega]
private theorem core_eq (F:Flag) (hd:0≤F.degree) (hu:0≤F.upper) (hc:0≤F.cap) :
   save F=core F.degree.toNat (F.upper+1).toNat F.lower.toNat F.order.toNat
     (min (F.degree+1).toNat ((F.order+3-F.lower+F.degree).toNat/4)) := by
 let d:=F.degree
 let u:=F.upper
 let l:=F.lower-1
 let o:=F.order-1
 let z :=o-F.lower+d
 let mt:ℤ:=min d (z/4)+1
 let mn:=min (d+1).toNat ((z+4).toNat/4)
 have hz :z<0↔mn=0:= by dsimp [mn]; omega
 have hm : ¬ z<0→(mt:ℤ)=mn:= by
   dsimp [mn,mt]
   omega
 have hbalance :F.order+3-F.lower+F.degree=z+4 := by dsimp [z,o,d]; ring
 have ho: (o+1).toNat=F.order.toNat := by dsimp [o]; omega
 have hl: (l+1).toNat=F.lower.toNat := by dsimp [l]; omega
 have hmin: (min u l+1).toNat=min (u+1).toNat F.lower.toNat := by
   rw [← hl,← min_toNat]
   congr 1
   omega
 simp only [save,core,hbalance,not_lt.mpr hd,not_lt.mpr hu,not_lt.mpr hc,decide_false,
   Bool.or_self,Bool.false_eq_true,ite_false]
 change (if z<0 then _ else _)=(if mn=0 then _ else _)
 have hdd : ¬ d<0:=not_lt.mpr hd
 by_cases hh:z<0
 · simp only [hh,hz.mp hh,ite_true]
   change count d u - count d (min u l) =
     countN d.toNat (u+1).toNat - countN d.toNat (min (u+1).toNat F.lower.toNat)
   simp only [count_eq_countN d,hdd,ite_false,hmin]
 rw [ite_eq_right hh,ite_eq_right (fun h=>hh (hz.mpr h))]
 have hmt: (mt:ℤ)=mn:=hm hh
 have hmn:mt.toNat=mn:= by omega
 have hl' : l≤u↔F.lower.toNat≤(u+1).toNat := by omega
 have ho' : (o-3*mt+1).toNat=F.order.toNat-3*mn:= by omega
 let k (n:ℕ) :=if d.toNat< mn then 0 else countN (d.toNat-mn) n
 let a :=count d u
 let b:=count (d-mt) (o-3*mt)
 let c:=count d o+count (d-mt) l
 let A:=countN d.toNat (u+1).toNat
 let B:=k (F.order.toNat-3*mn)
 let C:=countN d.toNat F.order.toNat+k F.lower.toNat
 change (if l≤u then a+b-c else a+b+count d l-(c+a)) =
   (if F.lower.toNat≤(u+1).toNat then A+B-C else B+countN d.toNat F.lower.toNat-C)
 have hk (x :ℤ) :count (d-mt) x=k (x+1).toNat := by
   simpa only [k,hmn] using count_kept d x mt hd (by omega)
 have ha :a=A:= by simp only [a,A,count_eq_countN d,hdd,ite_false]
 have hb:b=B:= by
   change count (d-mt) (o-3*mt)=k (F.order.toNat-3*mn)
   rw [hk,ho']
 have hc' : c=C:= by
   change count d o+count (d-mt) l=countN d.toNat F.order.toNat+k F.lower.toNat
   rw [count_eq_countN d o,ite_eq_right hdd,ho,hk,hl]
 have hcl:count d l=countN d.toNat F.lower.toNat := by
   rw [count_eq_countN d l,ite_eq_right hdd,hl]
 simp only [hl',ha,hb,hc',hcl]
 split <;> omega
end qaQQvid
end
