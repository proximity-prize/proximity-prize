import ProximityPrize.SubmissionLower.ZGSvmVd
import ProximityPrize.SubmissionLower.Z3gZttb
set_option Elab.async false
section
set_option autoImplicit true
namespace qcIhqIe
open P6_6_2 qwbsesc Finset
open xE (denominator gd)
open aRR (DW afw b0n)
open aAZ (Jc)
open private antiderivative evalSum sum_den sum_six cum_eq from ProximityPrize.SubmissionLower.ZF5THYd
open private c5h from ProximityPrize.SubmissionLower.BH
open scoped BigOperators
private def base (n:ℕ) :ℤ :=
  (1709-(n:ℤ))*(denominator 1710 - denominator (418-(n:ℤ)) -
    denominator (417-(n:ℤ)) - denominator (416-(n:ℤ)))
private theorem base_eq (n:ℕ) :
    (3000-((1291+n:ℕ) :ℤ))*gd (1291+n:ℕ) 1710=base n:= by
  rw [cum_eq _ (by omega),Jc _ (by omega : (1707:ℤ) - 2*↑(1291+n:ℕ)<0),
    Jc _ (by omega : (1706:ℤ) - 2*↑(1291+n:ℕ)<0),
    Jc _ (by omega : (1705:ℤ) - 2*↑(1291+n:ℕ)<0)]
  unfold base
  push_cast
  simp only [add_zero]
  ring_nf
private def baseResidue (r :ℕ) :ℤ :=
  let w:ℤ:=1709-(r :ℤ)
  evalSum w 1710 0 70-evalSum w (418-(r :ℤ)) 1 70 -
    evalSum w (417-(r :ℤ)) 1 70-evalSum w (416-(r :ℤ)) 1 70
private theorem base_residue (r :ℕ) :
    240*(∑ k∈range 70,base (6*k+r))=baseResidue r := by
  have he (k :ℕ) :base (6*k+r) =
      let w:ℤ:=1709-(r :ℤ)-6*(k :ℤ)
      w*(denominator 1710 - denominator (418-(r :ℤ)-6*(k :ℤ)) -
        denominator (417-(r :ℤ)-6*(k :ℤ)) - denominator (416-(r :ℤ)-6*(k :ℤ))) := by
    unfold base
    push_cast
    ring_nf
  simp_rw [he,mul_sub,sum_sub_distrib]
  simp only [mul_sub]
  unfold baseResidue
  have h0:=sum_den (1709-(r :ℤ)) 1710 0 70 (Or.inl rfl)
  have h1 (u:ℤ) :=sum_den (1709-(r :ℤ)) u 1 70 (Or.inr (Or.inl rfl))
  simp only [zero_mul,mul_zero,sub_zero] at h0
  simp only [one_mul] at h1
  rw [h0,h1,h1,h1]
private theorem six_rows {f :Fin 6→ℤ} (a b c d e g:ℤ)
    (h : ∀ r,f r=(![a,b,c,d,e,g] :Fin 6→ℤ) r) :
    (∑ r,f r)=a+b+c+d+e+g:= by
  simp_rw [h]
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
  ring
private theorem base_total: (∑ k∈range 419,base k)=0x4eea685cca2a := by
  have h:240*(∑ k∈range 420,base k)=0x4a231b92335340:= by
    change 240*(∑ k∈range (6*70),base k)= _
    rw [sum_six,mul_sum]
    simp_rw [base_residue]
    rw [six_rows (f := fun r=>baseResidue r.val) 0xc5f8d16a207b0 0xc5dcefaf8f6a0 0xc5c1019e9b2e0
      0xc5a5075466780 0xc58900d6036d0 0xc56cee40803c0 (by intro r; fin_cases r <;> rfl)]
    rfl
  change 240*(∑ k∈range (419+1),base k)= _ at h
  rw [sum_range_succ,show base 419=0x29f9503962 from rfl] at h
  omega
private theorem sum_layers (s N :ℕ) (hs :0<s) :
    24*(∑ n∈range N,∑ j∈range (n+1),denominator ((n:ℤ)+1-(s :ℤ)*((j:ℤ)+1))) =
      ∑ j∈range N,DW ((N :ℤ)+1-(s :ℤ)*((j:ℤ)+1)) := by
  have pad (n:ℕ) (hn:n∈range N) :
      (∑ j∈range (n+1),denominator ((n:ℤ)+1-(s :ℤ)*((j:ℤ)+1))) =
        ∑ j∈range N,denominator ((n:ℤ)+1-(s :ℤ)*((j:ℤ)+1)) := by
    apply sum_subset (range_mono (by have :=mem_range.mp hn; omega))
    intro j _ hj
    rw [mem_range] at hj
    have h: (j:ℤ)+1≤(s :ℤ)*((j:ℤ)+1) :=le_mul_of_one_le_left (by omega) (by omega)
    exact Jc _ (by omega)
  rw [sum_congr rfl pad,sum_comm,mul_sum]
  apply sum_congr rfl
  intro j _
  let a :ℤ:=1-(s :ℤ)*((j:ℤ)+1)
  have hj: (j:ℤ)+1≤(s :ℤ)*((j:ℤ)+1) :=le_mul_of_one_le_left (by omega) (by omega)
  have ha :a≤0:= by dsimp [a]; omega
  simp_rw [show ∀ n:ℕ,(n:ℤ)+1-(s :ℤ)*((j:ℤ)+1)=a+(n:ℤ)
    by intro n; dsimp [a]; ring]
  rw [b0n,afw a ha,sub_zero]
private def dO (u s k :ℤ) :ℤ:=c5h (u/6-s*k) (u%6)
private theorem sum_piece (u s :ℤ) (m:ℕ) :
    120*(∑ k∈range m,dO u s k)=antiderivative (dO u s) m:= by
  induction m with
  | zero=>simp [antiderivative]
  | succ m ih =>
    rw [sum_range_succ,mul_add,ih,Nat.cast_succ]
    unfold antiderivative dO c5h
    ring
private def width (u s :ℤ) (n:ℕ) :ℕ:=min n (u/(6*s)+1).toNat
private def prefixResidue (u s :ℤ) (n:ℕ) :ℤ :=
  antiderivative (dO u s) (width u s n)
private theorem prefix_residue (u s :ℤ) (n:ℕ) (hs :s=1∨s=4) :
    120*(∑ k∈range n,DW (u-6*(s*k)))=prefixResidue u s n:= by
  let m:=width u s n
  have hm:m≤n:=min_le_left _ _
  have ht: (∑ k∈range m,DW (u-6*(s*k))) =
      ∑ k∈range n,DW (u-6*(s*k)) := by
    apply sum_subset (range_mono hm)
    intro k hkn hkm
    rw [mem_range] at hkn hkm
    apply afw
    rcases hs with rfl | rfl <;> simp only [m,width] at hkm <;> omega
  change 120*(∑ k∈range n,DW (u-6*(s*k)))=antiderivative (dO u s) (m:ℤ)
  rw [← ht,← sum_piece u s m]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  have h0:0≤u-6*(s*k) := by
    rcases hs with rfl | rfl <;> simp only [m,width] at hk' <;> omega
  simp only [DW,not_lt.mpr h0,ite_false,dO]
  congr 1 <;> omega
private theorem premium_total: (∑ n∈range 419,premium (n+1))=0x348bda9ff := by
  have hs (u s :ℤ) (n:ℕ) (hh:s=1∨s=4) :
      120*(∑ j∈range (6*n),DW (u-s*j)) =
        ∑ r :Fin 6,prefixResidue (u-s*r.val) s n:= by
    rw [sum_six,mul_sum]
    apply sum_congr rfl
    intro r _
    have he (k :ℕ) :u-s*((6*k+r.val :ℕ) :ℤ)=u-s*r.val-6*(s*k) := by
      push_cast
      ring
    simp_rw [he,prefix_residue _ _ _ hh]
  have h1 :120*(∑ j∈range 419,DW (419-(j:ℤ)))=0x30f929686d40:= by
    have h:=hs 419 1 70 (Or.inl rfl)
    change 120*(∑ j∈range (419+1),DW (419-1*(j:ℤ)))= _ at h
    rw [sum_range_succ] at h
    simp only [one_mul] at h
    rw [show DW ((419:ℤ)-((419:ℕ) :ℤ))=0 from rfl,add_zero,
      six_rows (f := fun r=>prefixResidue (419-r.val) 1 70) 0x867bcdaddc0 0x84e8a227140
        0x83593fd0040 0x81cd9fd5680 0x8045bb63fc0 0x7ec18ba87c0
        (by intro r; fin_cases r <;> rfl)] at h
    exact h
  have h4 :120*(∑ j∈range 419,DW (416-4*(j:ℤ)))=0xc06d3aff880:= by
    have ht: (∑ j∈range 108,DW (416-4*(j:ℤ))) =
        ∑ j∈range 419,DW (416-4*(j:ℤ)) := by
      apply sum_subset (range_mono (by decide))
      intro j _ hj
      rw [mem_range] at hj
      exact afw _ (by omega)
    rw [← ht]
    change 120*(∑ j∈range (6*18),DW (416-4*(j:ℤ)))= _
    rw [hs _ _ _ (Or.inr rfl)]
    rw [six_rows (f := fun r=>prefixResidue (416-4*r.val) 4 18) 0x23f99a96c00 0x2255a9c7f80
      0x20c12dc8280 0x1f3bb864880 0x1dc4dd7bc40 0x1c5c32f85c0 (by intro r; fin_cases r <;> rfl)]
    rfl
  have hl1 :=sum_layers 1 419 (by decide)
  have hl4 :=sum_layers 4 419 (by decide)
  simp only [premium,Nat.cast_add,Nat.cast_one,sum_sub_distrib]
  simp_rw [show ∀ n j:ℕ,(n:ℤ)+1-1-j=(n:ℤ)+1-1*((j:ℤ)+1) by intros; ring]
  simp_rw [Nat.cast_one,Nat.cast_ofNat,show ∀ j:ℕ,(419:ℤ)+1-1*((j:ℤ)+1)=419-j by intros; ring] at hl1
  simp_rw [Nat.cast_ofNat,show ∀ j:ℕ,(419:ℤ)+1-4*((j:ℤ)+1)=416-4*j by intros; ring] at hl4
  omega
theorem proof :qwbsesc.c1 := by
  refine ⟨fun _ _ _=>0,Int.ofNat_le.mp ?_⟩
  rw [rankBand,Nat.cast_sum,sum_Ico_eq_sum_range]
  have hb (n:ℕ) (hn:n∈range 419) :
      (al2 (1291+n) (fun _ _=>0) :ℤ)≤base n+premium (n+1) := by
    have h:=aH4 (1291+n) (by omega) (by have :=mem_range.mp hn; omega) (fun _ _=>0)
    rwa [base_eq,show 1291+n-1290=n+1 by omega] at h
  change (∑ n∈range 419,(al2 (1291+n) (fun _ _=>0) :ℤ))≤_
  refine (sum_le_sum hb).trans ?_
  rw [sum_add_distrib,base_total,premium_total]
  rfl
end qcIhqIe
end
section
set_option autoImplicit true
namespace qeUg7Fa
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
local notation "r!" z "," p=>asA (v :=z) (by rfl) p
private theorem xL6fj0:total 2865 4=0x8324a14a480:=r! 0x20de7b4dc20,r! 0x20d04a4ff60,r! 0x20c20486bf0,r! 0x20b3d725d10,rfl
private theorem xL6fj1:total 2869 4=0x82416a10d30:=r! 0x20a59842aa0,r! 0x2097785e5f0,r! 0x20893978a40,r! 0x207b1ff7260,rfl
private theorem xL6fj2:total 2873 4=0x815efe85c20:=r! 0x206ce815c30,r! 0x205ed5014d0,r! 0x2050a9e5ea0,r! 0x20429788c80,rfl
private theorem r1:total 2865 12=0x186c509e0dd0:=total_append xL6fj0 (total_append xL6fj1 xL6fj2)
private theorem xL6fj3:total 2877 4=0x807d9374450:=r! 0x2034734bda0,r! 0x20266b359a0,r! 0x201868f3560,r! 0x200a4bff7b0,rfl
private theorem xL6fj4:total 2881 4=0x7f9cf9c0830:=r! 0x1ffc5179ac0,r! 0x1fee36b9110,r! 0x1fe0429f3c0,r! 0x1fd22eee8a0,rfl
private theorem xL6fj5:total 2885 4=0x7ebd1a7de90:=r! 0x1fc44557df0,r! 0x1fb6385e000,r! 0x1fa85169890,r! 0x1f9a4b5e810,rfl
private theorem r2:total 2877 12=0x17ed7a7b2b10:=total_append xL6fj3 (total_append xL6fj4 xL6fj5)
private theorem xL6fj6:total 2889 4=0x7dde1339510:=r! 0x1f8c6f7da90,r! 0x1f7e6fae770,r! 0x1f709669160,r! 0x1f629da41b0,rfl
private theorem xL6fj7:total 2893 4=0x7cffde3a670:=r! 0x1f54cac19c0,r! 0x1f46dccc150,r! 0x1f391106330,r! 0x1f2b25a6830,rfl
private theorem xL6fj8:total 2897 3=0x5d2ea235810:=r! 0x1f1d64cc170,r! 0x1f0f7bed890,r! 0x1f01c17be10,rfl
private theorem r3:total 2889 11=0x1580c93a9390:=total_append xL6fj6 (total_append xL6fj7 xL6fj8)
theorem fZA:total 2865 35=0x45da9453cc70 :=
  (total_append r1 (total_append r2 r3))
end qeUg7Fa
end
