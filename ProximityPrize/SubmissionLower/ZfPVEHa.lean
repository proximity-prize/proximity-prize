import ProximityPrize.SubmissionLower.ZJCauJe
set_option Elab.async false
set_option autoImplicit true
namespace qaQQvid
open xE (Flag gd)

open aFM (aM3)
open private bDu aIX from ProximityPrize.SubmissionLower.B




open private bGw from ProximityPrize.SubmissionLower.BK
private def count (d u:ℤ) :ℕ :=
 if d<0 then 0 else
  let (a,b) :=aM3 d.toNat (u+1).toNat
  a-b
private theorem count_eq (d u:ℤ) : (count d u:ℤ)=gd d u:= by
 by_cases h:d<0
 · simp [count,gd,h]
 lift d to ℕ using le_of_not_gt h
 have hp:=(bDu d u).trans (bGw _ _)
 have hn:0≤gd d u:= by rw [← aw7.proof _ _]; exact Int.natCast_nonneg _
 rcases he :aM3 d (u+1).toNat with ⟨a,b⟩
 simp only [he,aIX] at hp
 simp only [count,not_lt.mpr (Int.natCast_nonneg d),ite_false,Int.toNat_natCast,he]
 omega
private def save (F:Flag) :ℕ :=
 if F.degree<0 || F.upper<0 || F.cap<0 then 0 else
   let d:=F.degree
   let u:=F.upper
   let l:=F.lower-1
   let o:=F.order-1
   let z :=o-F.lower+d
   let a :=count d u
   if z<0 then a - count d (min u l) else
     let m:=min d (z/4)+1
     let b:=count (d-m) (o-3*m)
     let c:=count d o+count (d-m) l
     if l≤u then a+b-c else a+b+count d l-(c+a)
end qaQQvid
