import ProximityPrize.SubmissionLower.E
set_option Elab.async false
set_option autoImplicit true
namespace P1_6_2_2
open xE (gd BH)



open scoped BigOperators
private theorem df6 (d a n:ℕ) (ha :a<n) :
  (∑ j∈Finset.range n,gd (d:ℤ) ((a :ℤ)-(j:ℤ))) =
    ∑ j∈Finset.range (a+1),gd (d:ℤ) j:= by
 calc
  _ = ∑ j∈Finset.range (a+1),gd (d:ℤ) ((a :ℤ)-(j:ℤ)) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hja
    have hlt: (a :ℤ)-(j:ℤ)<0:= by rw [Finset.mem_range] at hja; omega
    simp [gd,hlt]
  _ = _:= by
    conv_rhs=>rw [← Finset.sum_range_reflect (fun j=>gd (d:ℤ) (j:ℤ)) (a+1)]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    have hja :=Finset.mem_range.mp hj
    rw [show a+1 - 1 - j=a - j by omega,Nat.cast_sub (by omega)]
open private coH coI from ProximityPrize.SubmissionLower.BH
private theorem scaled_affine (q a b:ℤ) (h:0≤6*(a*q)+b) :
  2*xE.denominator (6*(a*q)+b)=coH (a*q+b/6) (b % 6) := by
 rw [coI _ h]
 congr 1 <;> omega
private theorem saturated (s :ℕ) :
   6*gd s (3*(s :ℤ))=((s :ℤ)+1)*(s+2)*(s+3) := by
 by_cases hs :s<6
 · interval_cases s <;> decide
 let q:=(s :ℤ)/6
 let r :=(s :ℤ) % 6
 have hq:1≤q:= by dsimp [q]; omega
 have hr₀:0≤ r := by dsimp [r]; omega
 have hr₁:r<6:= by dsimp [r]; omega
 have hsr : (s :ℤ)=6*q+r := by dsimp [q,r]; omega
 have h0:=scaled_affine q 3 (3*r) (by omega)
 have h1 :=scaled_affine q 2 (2*r - 1) (by omega)
 have h2 :=scaled_affine q 2 (2*r - 2) (by omega)
 have h3:=scaled_affine q 2 (2*r-3) (by omega)
 have h4 :=scaled_affine q 1 (r-3) (by omega)
 have h5:=scaled_affine q 1 (r-4) (by omega)
 have h6:=scaled_affine q 1 (r - 5) (by omega)
 simp only [gd,show ¬ (s :ℤ)<0 by omega,show ¬ 3*(s :ℤ)<0 by omega,
   Bool.false_or,decide_false,Bool.false_eq_true,ite_false,min_self]
 rw [show 3*(s :ℤ)-3*s-6 = -6 by ring]
 simp only [show xE.denominator (-6)=0 by decide,sub_zero]
 rw [hsr]
 rw [show 3*(6*q+r)-(6*q+r) - 1=6*(2*q)+(2*r - 1) by ring,
   show 3*(6*q+r)-(6*q+r) - 2=6*(2*q)+(2*r - 2) by ring,
   show 3*(6*q+r)-(6*q+r)-3=6*(2*q)+(2*r-3) by ring,
   show 3*(6*q+r) - 2*(6*q+r)-3=6*(1*q)+(r-3) by ring,
   show 3*(6*q+r) - 2*(6*q+r)-4=6*(1*q)+(r-4) by ring,
   show 3*(6*q+r) - 2*(6*q+r) - 5=6*(1*q)+(r - 5) by ring,
   show 3*(6*q+r)=6*(3*q)+3*r by ring]
 generalize r=t at h0 h1 h2 h3 h4 h5 h6 hr₀ hr₁ ⊢
 interval_cases t <;>
   norm_num [coH] at h0 h1 h2 h3 h4 h5 h6 ⊢ <;>
   linear_combination 3*(h0 - h1 - h2 - h3+h4+h5+h6)
end P1_6_2_2
