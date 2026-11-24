import ProximityPrize.SubmissionLower.ZeuEwuc
set_option Elab.async false
set_option autoImplicit true
namespace qwbsesc
open P6_6_2 (rankBand)
open xE (gd denominator)
open aAZ (Jc)
open private aAD bPo from ProximityPrize.SubmissionLower.BH
open Finset
open scoped BigOperators
private def antiderivative (f :ℤ→ℤ) (n:ℤ) :ℤ :=
  120*n*f 0+60*n*(n-1)*(f 1 - f 0) +
  20*n*(n-1)*(n-2)*(f 2 - 2*f 1+f 0) +
  5*n*(n-1)*(n-2)*(n-3)*(f 3-3*f 2 + 3*f 1 - f 0) +
  n*(n-1)*(n-2)*(n-3)*(n-4)*(f 4-4*f 3+6*f 2 - 4*f 1+f 0)
private def HE (w a s r k :ℤ) :ℤ :=
  (w-6*k)*aAD (a - s*k) r
private theorem sum_poly (w a s r :ℤ) (n:ℕ) :
    120*(∑ k∈range n,HE w a s r k) =
      antiderivative (HE w a s r) n:= by
  induction n with
  | zero=>simp [antiderivative]
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih,Nat.cast_succ]
    unfold antiderivative HE aAD
    ring
private def width (u s :ℤ) (n:ℕ) :ℕ :=
  if s=0 then if u<0 then 0 else n else min n (u/(6*s)+1).toNat
private def evalSum (w u s :ℤ) (n:ℕ) :ℤ :=
  antiderivative (HE w (u/6) s (u % 6)) (width u s n)
private theorem sum_den (w u s :ℤ) (n:ℕ) (hs :s=0∨s=1∨s=2) :
    240*(∑ k∈range n,(w-6*(k :ℤ))*denominator (u-6*(s*k))) =
      evalSum w u s n:= by
  let m:=width u s n
  have hm:m≤n:= by
    unfold m width
    split
    · split <;> omega
    · exact min_le_left _ _
  have hleft (k :ℕ) (hk :k< m) :0≤u-6*(s*k) := by
    rcases hs with rfl | rfl | rfl <;> by_cases hu:u<0 <;>
      simp [m,width,hu] at hk ⊢ <;> omega
  have hright (k :ℕ) (hk :m≤k) (hn:k<n) :u-6*(s*k)<0:= by
    rcases hs with rfl | rfl | rfl <;> by_cases hu:u<0 <;>
      simp [m,width,hu] at hk ⊢ <;> omega
  have he (k :ℕ) (hk :k< m) :
      2*denominator (u-6*(s*k))=aAD (u/6 - s*k) (u%6) := by
    rw [bPo _ (hleft k hk)]
    congr 1 <;> omega
  have htrim :
      (∑ k∈range m,(w-6*(k :ℤ))*denominator (u-6*(s*k))) =
        ∑ k∈range n,(w-6*(k :ℤ))*denominator (u-6*(s*k)) := by
    apply sum_subset (range_mono hm)
    intro k hkn hkm
    rw [Jc _ (hright k (by simpa only [mem_range,not_lt] using hkm)
      (mem_range.mp hkn)),mul_zero]
  have hrow :
      (∑ k∈range m,2*((w-6*(k :ℤ))*denominator (u-6*(s*k)))) =
        ∑ k∈range m,HE w (u/6) s (u%6) k := by
    refine sum_congr rfl fun k hk => ?_
    rw [mul_left_comm,he k (mem_range.mp hk)]
    rfl
  calc
    _=120*(2*(∑ k∈range m,(w-6*(k :ℤ))*denominator (u-6*(s*k)))) := by
      rw [htrim,← mul_assoc]
      rfl
    _ = _:= by rw [mul_sum,hrow,sum_poly]; rfl
private theorem cum_eq (q:ℕ) (hq:571≤q) :
    gd q 1710=denominator 1710 - denominator (1709-(q:ℤ)) -
      denominator (1708-(q:ℤ)) - denominator (1707-(q:ℤ)) +
      denominator (1707 - 2*(q:ℤ))+denominator (1706 - 2*(q:ℤ)) +
      denominator (1705 - 2*(q:ℤ)) := by
  simp only [gd,show ¬ (q:ℤ)<0 by omega,show ¬ (1710 :ℤ)<0 by decide,
    decide_false,Bool.false_or,Bool.false_eq_true,ite_false,min_eq_left (by omega : (1710 :ℤ)≤3*q),
    Jc (1710-3*(q:ℤ)-6) (by omega),sub_zero]
  rw [show (1710 :ℤ)-q-1=1709-(q:ℤ) by ring,show (1710 :ℤ)-q-2=1708-(q:ℤ) by ring,
    show (1710 :ℤ)-q-3=1707-(q:ℤ) by ring,show (1710 :ℤ)-2*q-3=1707-2*q by ring,
    show (1710 :ℤ)-2*q-4=1706-2*q by ring,show (1710 :ℤ)-2*q-5=1705-2*q by ring]
private theorem sum_six (f :ℕ→ℤ) (n:ℕ) :
    (∑ k∈range (6*n),f k) = ∑ r :Fin 6,∑ k∈range n,f (6*k+r.val) := by
  induction n with
  | zero=>simp
  | succ n ih =>
    rw [Nat.mul_succ,sum_range_add,ih]
    have h (r :Fin 6) : (∑ k∈range (n+1),f (6*k+r.val)) =
        (∑ k∈range n,f (6*k+r.val))+f (6*n+r.val) :=sum_range_succ _ _
    simp_rw [h]
    rw [sum_add_distrib]
    congr 1
private def residue (r :ℕ) :ℤ :=
  let w:ℤ:=2429-(r :ℤ)
  evalSum w 1710 0 120-evalSum w (1138-(r :ℤ)) 1 120 -
    evalSum w (1137-(r :ℤ)) 1 120-evalSum w (1136-(r :ℤ)) 1 120 +
    evalSum w (565 - 2*(r :ℤ)) 2 120+evalSum w (564 - 2*(r :ℤ)) 2 120 +
    evalSum w (563 - 2*(r :ℤ)) 2 120
private def colRank (q:ℕ) :ℤ :=
  (3000-(q:ℤ))*gd q 1710
private theorem residue_sum (r :ℕ) :
    240*(∑ k∈range 120,colRank (571+(6*k+r)))=residue r := by
  have h (k :ℕ) :colRank (571+(6*k+r)) =
      let w:ℤ:=2429-(r :ℤ)-6*(k :ℤ)
      w*(denominator 1710 - denominator (1138-(r :ℤ)-6*(k :ℤ)) -
        denominator (1137-(r :ℤ)-6*(k :ℤ)) - denominator (1136-(r :ℤ)-6*(k :ℤ)) +
        denominator (565 - 2*(r :ℤ)-6*(2*(k :ℤ))) +
        denominator (564 - 2*(r :ℤ)-6*(2*(k :ℤ))) +
        denominator (563 - 2*(r :ℤ)-6*(2*(k :ℤ)))) := by
    unfold colRank
    rw [cum_eq _ (by omega)]
    push_cast
    ring_nf
  simp_rw [h,mul_add,mul_sub,sum_add_distrib,sum_sub_distrib]
  simp only [mul_add,mul_sub]
  unfold residue
  have h0:=sum_den (2429-(r :ℤ)) 1710 0 120 (Or.inl rfl)
  simp only [zero_mul,sub_zero,mul_zero] at h0
  rw [h0]
  have h1 (u:ℤ) :=sum_den (2429-(r :ℤ)) u 1 120 (Or.inr (Or.inl rfl))
  simp only [one_mul] at h1
  rw [h1,h1,h1,sum_den _ _ 2 120 (Or.inr (Or.inr rfl)),
    sum_den _ _ 2 120 (Or.inr (Or.inr rfl)),sum_den _ _ 2 120 (Or.inr (Or.inr rfl))]
theorem shoulder_cap:aak 571 1291 0x7a01f11e79e5:= by
  refine ⟨fun _ _ _=>0,?_⟩
  have h:240*(∑ q∈Ico 571 1291,colRank q)=240*0x7a01f11e79e5:= by
    rw [sum_Ico_eq_sum_range]
    change 240*(∑ k∈range (6*120),colRank (571+k))= _
    rw [sum_six,mul_sum]
    simp_rw [residue_sum]
    simp only [Fin.sum_univ_succ,Fin.val_succ,Fin.val_zero,Fin.sum_univ_zero,add_zero]
    rw [show residue 0=0x13026d3937c100 from rfl,
      show residue 1=0x1307ff76fb6040 from rfl,
      show residue 2=0x130d8dc4c17c40 from rfl,
      show residue 3=0x13131820b1a7c0 from rfl,
      show residue 4=0x13189e857f40f0 from rfl,
      show residue 5=0x131e20f16cc080 from rfl]
    rfl
  have hb: (rankBand (fun _ _ _=>0) 571 1291 :ℤ) ≤ ∑ q∈Ico 571 1291,colRank q:= by
    rw [rankBand,Nat.cast_sum]
    exact sum_le_sum fun q hq=>prefix_grade_le q (by have :=(mem_Ico.mp hq).2; omega) _
  exact Int.ofNat_le.mp (show (rankBand (fun _ _ _=>0) 571 1291 :ℤ) ≤
    ((0x7a01f11e79e5:ℕ) :ℤ) from by omega)
end qwbsesc
