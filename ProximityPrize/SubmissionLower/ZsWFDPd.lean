import ProximityPrize.SubmissionLower.Z3lRrWc
import ProximityPrize.SubmissionLower.Ztdy5wb
import ProximityPrize.SubmissionLower.ZGcgEBb
import ProximityPrize.SubmissionLower.ZhNzRYc
import ProximityPrize.SubmissionLower.ZTeGCOe
import ProximityPrize.SubmissionLower.ZNGQJQc
import ProximityPrize.SubmissionLower.ZwtWMfa
import ProximityPrize.SubmissionLower.ZXLxXWd
import ProximityPrize.SubmissionLower.Zmk5EEe
import ProximityPrize.SubmissionLower.ZAJiURc
set_option Elab.async false
section
set_option autoImplicit true
namespace qbi2Fye
theorem proof :q1FwQGc.c1 :=
  qA0rFHd.of_children qYur1ad.proof qnKm5Ba.proof qWpt85c.proof
end qbi2Fye
end
section
set_option autoImplicit true
namespace qBLYDld
open aR (ao)
open aFN (Slot)
open qzLARrc (derivativeIndex)
open qmb8rCe (box cutMatrix)
open Polynomial
open scoped Polynomial BigOperators
noncomputable section
private abbrev S:=Slot box 27
private abbrev P:=ao[X][X]
private abbrev x :ao[X] :=Polynomial.X
private abbrev v :P:=C (1 + x)
private abbrev w:P:=Polynomial.X+C x
private abbrev z :P:=Polynomial.X+C (-(x^2))
private def proj (h:ℕ) :P →ₗ[ao] (S→ao) where
  toFun f r :=if derivativeIndex r<h then (f.coeff r.1.val).coeff r.2.val else 0
  map_add' f g:= by
    funext r
    by_cases hr :derivativeIndex r<h <;> simp [hr,coeff_add]
  map_smul' a f := by
    funext r
    by_cases hr :derivativeIndex r<h <;> simp [hr,coeff_smul]
private theorem column (d h:ℕ) (s :S) :
    (cutMatrix box 27 d h).col s =
      if d≤ s.1.val+s.2.val then proj h (v^s.2.val*w^s.1.val) else 0:= by
  funext r
  by_cases hd:d≤ s.1.val+s.2.val
  · rw [ite_eq_left hd]
    change cutMatrix box 27 d h r s=if derivativeIndex r<h then
      ((C (1+x)^s.2.val*w^s.1.val :P).coeff r.1.val).coeff r.2.val else 0
    rw [cutMatrix]
    by_cases hh:derivativeIndex r<h
    · simp only [hd,hh,true_and,ite_true,w,← (C:ao[X] →+* P).map_pow,coeff_C_mul,
        coeff_X_add_C_pow]
      simp only [← mul_assoc,← C_eq_natCast,coeff_mul_C,coeff_mul_X_pow',
        coeff_one_add_X_pow]
      by_cases hc:r.1.val≤ s.1.val
      · simp only [hc,true_and]
        split <;> simp [mul_comm]
      · simp [hc,Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hc)]
    · simp [hd,hh]
  · rw [ite_eq_right hd]
    change cutMatrix box 27 d h r s=0
    simp [cutMatrix,hd]
private def src (n c:ℕ) :P:=(C x)^(n-c)*w^c*v^(27-n-c)
private def dst (n j:ℕ) :P:=(C x)^(n-j)*z^j*v^(27-n-j)
private theorem dst_zero (h n j:ℕ) (hj:j≤n) (hn:h≤n+j) :
    proj h (dst n j)=0:= by
  funext r
  by_cases hr :derivativeIndex r<h
  · change (if derivativeIndex r<h then ((dst n j).coeff r.1.val).coeff r.2.val else 0)=0
    rw [ite_eq_left hr,dst,mul_right_comm,← (C:ao[X] →+* P).map_pow,
      ← (C:ao[X] →+* P).map_pow,← (C:ao[X] →+* P).map_mul,coeff_C_mul,z,
      coeff_X_add_C_pow]
    by_cases hc:r.1.val≤j
    · rw [neg_pow,← pow_mul]
      have he (a b:ℕ) (f g k :ao[X]) :
          x^a*f*(g*x^b*k)=x^(a+b)*(f*g*k) := by
        rw [pow_add]
        ac_rfl
      rw [he,coeff_X_pow_mul']
      have hrs :r.2.val+2*r.1.val<h:=hr
      rw [ite_eq_right (show ¬ (n-j)+2*(j-r.1.val)≤ r.2.val by omega)]
    · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hc)]
  · simp [proj,hr]
private theorem binom_mem (h:ℕ) (T:Submodule ao (S→ao))
    (a b p:P) (k :ℕ)
    (H : ∀ j≤k,proj h (p*(a^j*b^(k-j)))∈T) :
    proj h (p*(a+b)^k)∈T:= by
  rw [add_pow,Finset.mul_sum,map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [← mul_assoc,mul_comm _ (↑(k.choose j) :P),← nsmul_eq_mul,map_nsmul]
  exact T.nsmul_mem (H j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) _
private theorem src_mem (h:ℕ) (T:Submodule ao (S→ao))
    (n c:ℕ) (hc:c≤n) (hn:n+c≤27)
    (H : ∀ j≤ c,proj h (dst n j)∈T) :
    proj h (src n c)∈T:= by
  have he :w=z+C x*v := by
    change Polynomial.X+C x=Polynomial.X+C (-(x^2))+C x*C (1+x)
    rw [← (C:ao[X] →+* P).map_mul,add_assoc,← (C:ao[X] →+* P).map_add]
    congr 1
    rw [mul_add,mul_one,pow_two,add_comm x (x*x),neg_add_cancel_left]
  rw [src,mul_right_comm,he]
  apply binom_mem
  intro j hj
  have hs :n-c+(c-j)=n-j:= by omega
  have ht:27-n-c+(c-j)=27-n-j:= by omega
  convert H j hj using 2
  rw [dst,mul_pow,← hs,← ht,pow_add,pow_add]
  ring_nf
private theorem eIj (h:ℕ) (T:Submodule ao (S→ao))
    (b c:ℕ) (hb:b+2*c≤27)
    (H : ∀ i≤27-b-2*c,proj h (src (c+i) c)∈T) :
    proj h (v^b*w^c)∈T:= by
  have hv : -C x+v=(1 :P) := by
    rw [← map_neg,← map_add]
    simp
  have hl:=binom_mem h T (-C x) v (v^b*w^c) (27-b-2*c)
  rw [hv,one_pow,mul_one] at hl
  apply hl
  intro i hi
  have ht:b+(27-b-2*c-i)=27-(c+i)-c:= by omega
  have hs :c+i-c=i:= by omega
  rw [neg_pow (C x :P) i]
  have he : (-1 :P)^i=algebraMap ao P ((-1 :ao)^i) := by simp
  rw [he]
  have hf : (v^b*w^c) *
      ((algebraMap ao P ((-1 :ao)^i)*(C x)^i)*v^(27-b-2*c-i)) =
      ((-1 :ao)^i)•src (c+i) c:= by
    rw [Algebra.smul_def,src,hs,← ht,pow_add]
    ac_rfl
  rw [hf,map_smul]
  exact T.smul_mem _ (H i hi)
private abbrev lo (d n:ℕ) :=n-(27-d)
private abbrev up (n:ℕ) :=min 12 (min n (27-n))
private abbrev sc (d n:ℕ) :=up n+1-lo d n
private abbrev tc (h n:ℕ) :=min 12 (min n (h-1-n))+1
private abbrev len (d h:ℕ) :=min (28-d) h
private abbrev Count (d h:ℕ) :=Σ n:Fin (len d h),Fin (min (sc d n) (tc h n))
private def gen (d h:ℕ) (k :Count d h) :S→ao :=
  proj h (if sc d k.1≤tc h k.1 then src k.1 (lo d k.1+k.2.val)
    else dst k.1 k.2.val)
private theorem mem_gen (d h n c:ℕ) (hn:n<len d h)
    (hl:lo d n≤ c) (hu:c≤up n) :
    proj h (src n c)∈Submodule.span ao (Set.range (gen d h)) := by
  have hc:c≤12∧c≤n∧c≤27-n:= by
    simpa only [up,le_min_iff] using hu
  have hq:n≤27:= by
    have hn' := hn.trans_le (min_le_left (28-d) h)
    omega
  let k :Fin (len d h) :=⟨n,hn⟩
  by_cases hs :sc d n≤tc h n
  · apply Submodule.subset_span
    have hi:c-lo d n< min (sc d n) (tc h n) := by
      rw [min_eq_left hs]
      change c-lo d n< up n+1-lo d n
      omega
    refine ⟨⟨k,⟨c-lo d n,hi⟩⟩,?_⟩
    have he :lo d n+(c-lo d n)=c:= by omega
    simp [gen,k,hs,he]
  · apply src_mem h _ n c hc.2.1 (by omega)
    intro j hj
    by_cases hh:n+j<h
    · apply Submodule.subset_span
      have hi:j< min (sc d n) (tc h n) := by
        rw [min_eq_right (le_of_not_ge hs),Nat.lt_succ_iff,le_min_iff,le_min_iff]
        omega
      exact ⟨⟨k,⟨j,hi⟩⟩,by simp [gen,k,hs]⟩
    · rw [dst_zero h n j (hj.trans hc.2.1) (Nat.le_of_not_gt hh)]
      exact Submodule.zero_mem _
end
end qBLYDld
end
section
set_option autoImplicit true
namespace qUSrEZc
theorem proof :q1FwQGc.c2 :=
  qmb8rCe.of_children qY7pQzb.proof qoRVxvd.proof qBLYDld.proof
end qUSrEZc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qfgfioe
open private tame from ProximityPrize.SubmissionLower.ZNGQJQc
theorem proof :qylJznc.c2 :=tame
end qfgfioe
end
section
set_option autoImplicit true
namespace qnWPwNa
theorem proof :qylJznc.c3:=qJFdYUc.proof
end qnWPwNa
end
section
set_option autoImplicit true
namespace qruM3Id
theorem proof :qO4n7sd.c1 :=
  qypA4Sc.of_children qWnROxa.proof qlcyGcd.proof qrrOjma.proof
end qruM3Id
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qhye6Fd
theorem proof :qO4n7sd.c2 :=
  qoCymac.of_children q5eiIAb.proof
    (qhFwyvc.of_children P5_7_1_7Q4332.proof1 P5_7_1_7Q4332.proof)
    qvOlzpd.proof q6hv5Ed.proof qpI7nyd.proof
    qIGP9Qa.proof
end qhye6Fd
end
