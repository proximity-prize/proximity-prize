import ProximityPrize.SubmissionLower.ZL8vffb
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option autoImplicit true
namespace qZyoMPc
open Finset
open cu (Shape ku triangle)
open agU (arY)
open P5_7_4 (poleRank)
open private bcT dfW auf from ProximityPrize.SubmissionLower.A2
private theorem bye (u:ℕ) :
    2*(triangle u:ℤ)=((u:ℤ)+1)*(u+2) := by
  have h:2*((u+1)*(u+2)/2)=(u+1)*(u+2) :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_succ_self (u+1)))
  change (2 :ℤ) * ↑((u+1)*(u+2)/2 :ℕ)= _
  exact_mod_cast h
private def entry (B J U q d j:ℤ) :ℤ :=
  let x :=U-q+1
  let y :=2*(B-q)+U-q+2
  (B+J-q-d+2*j)*(x+j)*(y+j)-(B+J-q)*(U+1)*(U+2)
private def slice (B J U q d:ℤ) :ℤ :=
  let x :=U-q+1
  let y :=2*(B-q)+U-q+2
  let l:=B+J-q-d
  bcT (l*x*y-(B+J-q)*(U+1)*(U+2)) (l*(x+y)+2*x*y) (l+2*(x+y)) 2 (d+1)
private theorem slice_eq (B J U q:ℤ) (d:ℕ) :
    12*(∑ j∈range (d+1),entry B J U q d j)=slice B J U q d:= by
  unfold slice
  rw [← Nat.cast_succ,← dfW]
  congr 1
  apply sum_congr rfl
  intro j _
  unfold entry
  ring
private def profile (B J U start offset slope i:ℤ) :ℤ :=
  slice B J U (start+i) (offset+slope*i)
private theorem sum_profile (B J U start offset slope :ℤ) (n:ℕ) :
    120*(∑ i∈range n,profile B J U start offset slope i) =
      auf (profile B J U start offset slope) n:= by
  have hstep (i:ℤ) :
      auf (profile B J U start offset slope) (i+1) =
      auf (profile B J U start offset slope) i +
        120*profile B J U start offset slope i:= by
    unfold auf profile slice bcT
    ring
  induction n with
  | zero=>simp [auf]
  | succ n ih=>rw [Nat.cast_succ,hstep,sum_range_succ,mul_add,ih]
def aP4 (B J U:ℕ) :ℤ :=
  auf (profile B J U 0 0 1) J +
    auf (profile B J U J J 0) (B+1-J:ℕ)
private theorem oB (s :Shape) (q d j:ℕ) (hq:q≤ s.B)
    (hd:d≤ s.J) (hj:j≤q) (hu:s.B≤ s.U) :
    2*((s.B+s.J-q-d+2*j:ℕ) *
      ((s.U-(q-j)+1 :ℕ)*(s.B-q:ℕ)+(triangle (s.U-(q-j)) :ℤ)) -
        (triangle s.U:ℤ)*(s.B+s.J-q:ℕ))=entry s.B s.J s.U q d j:= by
  have hq' : q≤ s.B+s.J:= by omega
  have hd' : d≤ s.B+s.J-q:= by omega
  have hu' : q-j≤ s.U:= by omega
  have h₁:=bye (s.U-(q-j))
  have h₂:=bye s.U
  push_cast [Nat.cast_sub hq,Nat.cast_sub hq',Nat.cast_sub hd',
    Nat.cast_sub hj,Nat.cast_sub hu'] at h₁ ⊢
  unfold entry
  linear_combination ((s.B:ℤ)+s.J-q-d+2*j)*h₁-((s.B:ℤ)+s.J-q)*h₂
private theorem entry_sum (s :Shape) (hu:s.B≤ s.U) :
    2*((poleRank s :ℤ)-(triangle s.U:ℤ)*(arY s :ℤ)) =
      ∑ q∈range (s.B+1),∑ j∈range (min q s.J+1),entry s.B s.J s.U q ↑(min q s.J) j:= by
  unfold poleRank arY ku
  simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_sum,← sum_sub_distrib]
  refine sum_congr rfl fun q hq=>sum_congr rfl fun j hj => ?_
  have hq' := Nat.lt_succ_iff.mp (mem_range.mp hq)
  have hj' := Nat.lt_succ_iff.mp (mem_range.mp hj)
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] using
    oB s q (min q s.J) j hq' (min_le_right ..) (hj'.trans (min_le_left ..)) hu
theorem scaledDebit_eq (s :Shape) (hj:s.J≤ s.B) (hu:s.B≤ s.U) :
    aP4 s.B s.J s.U =
      2880*((poleRank s :ℤ)-(triangle s.U:ℤ)*(arY s :ℤ)) := by
  let f := fun q:ℕ=>slice s.B s.J s.U q ↑(min q s.J)
  have hgrades :
      (∑ q∈range (s.B+1),f q) =
        24*((poleRank s :ℤ)-(triangle s.U:ℤ)*(arY s :ℤ)) := by
    rw [show (24 :ℤ)=12*2 by decide,mul_assoc,entry_sum s hu,mul_sum]
    apply sum_congr rfl
    intro q _
    exact (slice_eq s.B s.J s.U q (min q s.J)).symm
  have hsplit :=sum_range_add f s.J (s.B+1-s.J)
  rw [Nat.add_sub_of_le (show s.J≤ s.B+1 by omega)] at hsplit
  have hlo: (∑ q∈range s.J,f q) = ∑ q∈range s.J,profile s.B s.J s.U 0 0 1 q:= by
    apply sum_congr rfl
    intro q hq
    simp only [f,profile,min_eq_left (mem_range.mp hq).le,zero_add,one_mul]
  have hhi: (∑ i∈range (s.B+1-s.J),f (s.J+i)) =
      ∑ i∈range (s.B+1-s.J),profile s.B s.J s.U s.J s.J 0 i:= by
    apply sum_congr rfl
    intro i _
    simp only [f,profile,Nat.cast_add,min_eq_right (Nat.le_add_right _ _),zero_mul,add_zero]
  rw [aP4,show (2880:ℤ)=120*24 by decide,mul_assoc,← hgrades,hsplit,mul_add,hlo,hhi,
    sum_profile,sum_profile]
theorem bound (s :Shape) (v :ℕ) (hj:s.J≤ s.B) (hu:s.B≤ s.U)
    (h:aP4 s.B s.J s.U≤2880*(v :ℤ)) :
    poleRank s≤triangle s.U*arY s+v := by
  rw [scaledDebit_eq s hj hu] at h
  apply Int.ofNat_le.mp
  push_cast
  omega
end qZyoMPc
