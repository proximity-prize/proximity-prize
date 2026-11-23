import ProximityPrize.SubmissionLower.ZskDvCd
set_option Elab.async false
set_option autoImplicit true
section
namespace ba2


open xE (Flag oldCount m5 BH gd denominator)
open aAZ (Jc)
open aR (ao)
open akL (KP aDd)
open private aOG from ProximityPrize.SubmissionLower.AR




local notation "D" => denominator
def triple (u:ℤ) :ℤ:=D (u-1)+D (u-2)+D (u-3)
local notation "S" => triple
private theorem gEx (x :ℤ) (hx :x≤0) :S x=0:= by
 simp only [triple,Jc (x-1) (by omega),
  Jc (x-2) (by omega),
  Jc (x-3) (by omega),add_zero]
private theorem bZd {d u:ℤ} (hd:2≤d) (hu:u≤3*d) :
   gd d u=D u - triple (u-d)+triple (u-2*d-2) := by
 by_cases hn:u<0
 · simp only [gd,hn,decide_true,Bool.or_true,ite_true,triple,
     Jc u hn,Jc (u-d-1) (by omega),
     Jc (u-d-2) (by omega),Jc (u-d-3) (by omega),
     Jc (u-2*d-2-1) (by omega),Jc (u-2*d-2-2) (by omega),
     Jc (u-2*d-2-3) (by omega),add_zero,sub_zero]
 simp only [gd,triple,show ¬ d<0 by omega,hn,decide_false,Bool.false_or,
   Bool.false_eq_true,ite_false,min_eq_left hu,Jc (u-3*d-6) (by omega),sub_zero]
 rw [show u-2*d-2-1=u-2*d-3 by ring,show u-2*d-2-2=u-2*d-4 by ring,
     show u-2*d-2-3=u-2*d-5 by ring]
 ring
private theorem bDB {d u:ℤ} (hd:2≤d) (hu:u≤2*d+2) :
  gd d u=D u - S (u-d) := by
 rw [bZd hd (by omega),gEx (u-2*d-2) (by omega),add_zero]
private theorem fWE (F:Flag) (p:Fin 11→ℕ) :
  0≤oldCount F - m5 (BH F p) := by
 let R:=BH F p
 have hc:=bjv.proof aw7.proof
 have ht:=aYY.proof aw7.proof
 have hk :=aOG R (hc R) (ht R)
 obtain ⟨f,hf⟩:=bjw.proof F p
 have hi:=LinearMap.finrank_le_finrank_of_injective (f :=f) hf
 have hn:=(KP F).finrank_range_add_finrank_ker
 rw [aDd] at hn
 rw [← hc F]
 change 0≤_ - m5 R
 change Module.finrank ao (LinearMap.ker (KP R))≤_ at hi
 omega
end ba2
end
section
namespace ba2
open Finset


open xE (denominator)
open aRR (DW)
open aAZ (azV Jc)
open private xY arn from ProximityPrize.SubmissionLower.CM
open scoped BigOperators
local notation "D" => denominator
local notation "S" => triple
private def Ej (u:ℤ) :ℤ:=u*(u*(2*u+21)+66)
private theorem cIE {u:ℤ} (hu:0≤u) :
  Ej u≤72*D u∧72*D u≤Ej u+72 := by
 rw [← arn]
 simp only [xY,not_lt.mpr hu,ite_false]
 change Ej u≤72*((Ej u+72)/72) ∧
  72*((Ej u+72)/72)≤Ej u+72
 omega
private def primitive (a m z :ℤ) :ℤ :=
 let k :=z*(z-1)
 6*z*Ej a-3*k*m*(6*a*a+42*a+66)+k*(2*z-1)*m*m*(6*a+21)-3*k*k*m*m*m
private theorem eOo (a m:ℤ) (z :ℕ) :
   6*(∑ j∈range z,Ej (a-m*j))=primitive a m z := by
 induction z with
 | zero=>simp [primitive]
 | succ z ih =>
   rw [sum_range_succ,mul_add,ih,Nat.cast_succ]
   unfold primitive Ej
   ring
private def count (a :ℤ) (m t:ℕ) :ℕ:=if a<0 then 0 else min t (a.toNat/m+1)
private def lower (a :ℤ) (m t:ℕ) :ℤ:=primitive a m (count a m t)
private def upper (a :ℤ) (m t:ℕ) :ℤ:=lower a m t+432*count a m t
private theorem aJD (a :ℤ) {m:ℕ} (hm:0< m) (t:ℕ) :
   lower a m t≤432*(∑ j∈range t,D (a-m*j)) ∧
     432*(∑ j∈range t,D (a-m*j))≤upper a m t:= by
 let z :=count a m t
 have hz :z≤t:= by unfold z count; split <;> omega
 have hcut (j:ℕ) :j<z↔j<t∧(m:ℤ)*j≤a := by
   by_cases ha :a<0
   · have hpos :0≤(m:ℤ)*j:= by positivity
     simp only [z,count,ite_eq_left ha]
     omega
   have he : (m:ℤ)*j≤a↔j≤a.toNat/m:= by
     rw [Nat.le_div_iff_mul_le hm,← Int.toNat_of_nonneg (by omega :0≤a)]
     exact_mod_cast (show m*j≤a.toNat↔j*m≤a.toNat by rw [Nat.mul_comm m j])
   simp only [z,count,ite_eq_right ha,lt_min_iff,he,Nat.lt_succ_iff]
 have hs : (∑ j∈range t,D (a-m*j)) = ∑ j∈range z,D (a-m*j) := by
   symm
   apply sum_subset (range_mono hz)
   intro j ht hj
   rw [mem_range] at ht hj
   exact Jc _ (by have h:=hcut j; omega)
 have hlo:=sum_le_sum (s :=range z)
   (f := fun j:ℕ=>Ej (a-m*j)) (g:= fun j:ℕ=>72*D (a-m*j))
   (fun j hj=>(cIE (sub_nonneg.mpr ((hcut j).mp (mem_range.mp hj)).2)).1)
 have hup:=sum_le_sum (s :=range z)
   (f := fun j:ℕ=>72*D (a-m*j)) (g:= fun j:ℕ=>Ej (a-m*j)+72)
   (fun j hj=>(cIE (sub_nonneg.mpr ((hcut j).mp (mem_range.mp hj)).2)).2)
 simp only [← mul_sum,sum_add_distrib,sum_const,card_range,nsmul_eq_mul] at hlo hup
 have hp:=eOo a m z
 rw [hs]
 change primitive a m z≤_∧_≤primitive a m z+432*(z :ℤ)
 omega
private def one (a :ℤ) (t:ℕ) :ℤ:=18*(DW (a+1) - DW (a+1-t))
private theorem c2u (a :ℤ) (t:ℕ) :432*(∑ j∈range t,D (a-j))=one a t:= by
 induction t with
 | zero=>simp [one]
 | succ t ih =>
   rw [sum_range_succ,mul_add,ih]
   simp only [one,Nat.cast_succ]
   have h:=azV (a+1) t
   rw [show a+1-1-(t:ℤ)=a-t by ring] at h
   linear_combination -18*h
private def HD (f :ℤ→ℕ→ℕ→ℤ) (a :ℤ) (m t:ℕ) :ℤ :=
 f (a-1) m t+f (a-2) m t+f (a-3) m t
private theorem bPh (a :ℤ) {m:ℕ} (hm:0< m) (t:ℕ) :
  HD lower a m t≤432*(∑ j∈range t,triple (a-m*j)) ∧
   432*(∑ j∈range t,triple (a-m*j))≤HD upper a m t:= by
 have shift (j c:ℤ) :a-m*j-c=a-c-m*j:=sub_right_comm ..
 simp only [HD,triple,shift,sum_add_distrib,mul_add]
 have h₁:=aJD (a-1) hm t
 have h₂:=aJD (a-2) hm t
 have h₃:=aJD (a-3) hm t
 omega
private def cui (a :ℤ) (t:ℕ) :ℤ :=
 one (a-1) t+one (a-2) t+one (a-3) t
private theorem gEr (a :ℤ) (t:ℕ) :
  432*(∑ j∈range t,S (a-j))=cui a t:= by
 have h (j:ℤ) (c:ℤ) :a-j-c=a-c-j:=sub_right_comm ..
 simp only [cui,triple,fun j=>h j 1,fun j=>h j 2,fun j=>h j 3,sum_add_distrib,mul_add,c2u]
end ba2
end
