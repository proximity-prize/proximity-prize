import ProximityPrize.SubmissionBinaryLower.B6402ProfileCosts

namespace ProximityPrize.SubmissionBinaryLower.B6402OrderProfile
open B6402ProfileCosts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {I : Type*} [Fintype I]

noncomputable def count (k : I → ℕ) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun i => min (k i) 3=j).card
def totalExcess (k : I → ℕ) := ∑ i,(k i-3)
def primaryOrder (m b k : ℕ) := if k=2 then m else m-b

private theorem weighted_count (k : I → ℕ) (j : ℕ) (c : ℤ) :
    (∑ i,if min (k i) 3=j then c else 0)=(count k j:ℤ)*c := by
  rw [←Finset.sum_filter]
  simp [count,smul_eq_mul]

theorem sum_fees (k : I → ℕ) (m b s q T H : ℕ) (ht : H≤T) :
    (∑ i,fee (primaryOrder m b (k i)) s q T H (k i)) ≤
      (count k 0:ℤ)*fee (m-b) s q T H 0+(count k 1:ℤ)*fee (m-b) s q T H 1+
      (count k 2:ℤ)*fee m s q T H 2+(count k 3:ℤ)*fee (m-b) s q T H 3+
      (totalExcess k:ℤ)*inc (m-b) s T := by
  have point (i : I) : fee (primaryOrder m b (k i)) s q T H (k i) ≤
      (if min (k i) 3=0 then fee (m-b) s q T H 0 else 0)+
      (if min (k i) 3=1 then fee (m-b) s q T H 1 else 0)+
      (if min (k i) 3=2 then fee m s q T H 2 else 0)+
      (if min (k i) 3=3 then fee (m-b) s q T H 3 else 0)+
      (k i-3:ℕ)*inc (m-b) s T := by
    rcases (show k i=0 ∨ k i=1 ∨ k i=2 ∨ 3≤k i by omega) with e|e|e|e
    · simp [e,primaryOrder]
    · simp [e,primaryOrder]
    · simp [e,primaryOrder]
    · have ne : k i≠2 := by omega
      simpa [primaryOrder,ne,Nat.min_eq_right e] using tail (m-b) s q T H (k i) ht e
  have h := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset I)) => point i)
  simp only [Finset.sum_add_distrib,weighted_count,←Finset.sum_mul] at h
  simpa only [totalExcess,Nat.cast_sum] using h

#print axioms sum_fees
end ProximityPrize.SubmissionBinaryLower.B6402OrderProfile
