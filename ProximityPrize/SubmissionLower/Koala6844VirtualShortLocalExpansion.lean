import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1900000

variable {R : Type*} [CommRing R]

theorem local_column_double_expansion
    (lead base A Z B shift T C mon : R) (L q d j : ℕ)
    (hdL : d ≤ L) (hjq : j ≤ q)
    (hA : lead*Z = A-base) (hB : lead*B = T*C+A*shift) :
    lead^(L+q)*A^(q-j)*(mon*Z^d)*B^j =
      ∑ i ∈ Finset.range (j+1), ∑ k ∈ Finset.range (d+1),
        (lead^(L-d+q-j) * (j.choose i : R) * (d.choose k : R) *
          shift^(j-i) * (-base)^(d-k)) * (A^(q-i+k) * T^i * C^i * mon) := by
  have hpow : L+q = (L-d+q-j)+j+d := by omega
  calc
    _ = lead^(L-d+q-j) * A^(q-j) * mon * (lead*B)^j * (lead*Z)^d := by
      rw [hpow, pow_add, pow_add, mul_pow, mul_pow]
      ring
    _ = _ := by
      rw [hB, hA, sub_eq_add_neg, add_pow, add_pow]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k _
      have hi := Finset.mem_range.mp hi
      have hiq : q-j+(j-i)+k = q-i+k := by omega
      rw [← hiq, pow_add, pow_add, mul_pow, mul_pow]
      ring

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
