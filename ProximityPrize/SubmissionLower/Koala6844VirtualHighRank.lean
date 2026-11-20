import ProximityPrize.SubmissionLower.Koala6844VirtualHighBoxes
import ProximityPrize.SubmissionLower.Koala6844VirtualHighRankSum



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped BigOperators

private def rectangleCap (y b : ℕ) : Fin 3 → ℕ := ![y,b,b]
def singleSeedWidth (second : Bool) : Fin 3 → ℕ :=
  if second then ![1,0,1] else ![1,1,0]

private theorem rectangleCap_product (y b : ℕ) :
    (∏ i : Fin 3, (rectangleCap y b i + 1)) = (y+1)*(b+1)*(b+1) := by
  simp [rectangleCap, Fin.prod_univ_three, Nat.mul_assoc]

private theorem reduced_rectangle_product (y b k : ℕ) (second : Bool) :
    (∏ i : Fin 3, (rectangleCap y b i - k * singleSeedWidth second i + 1)) =
      (y-k+1)*(b-k+1)*(b+1) := by
  cases second <;>
    simp [rectangleCap, singleSeedWidth, Fin.prod_univ_three, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc]

private theorem reduced_rectangle_le (y b k : ℕ) :
    (y-k+1)*(b-k+1)*(b+1) ≤ (y+1)*(b+1)*(b+1) := by
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.sub_le _ _) _) (Nat.add_le_add_right (Nat.sub_le _ _) _))

private theorem loss_cast {y b k : ℕ} (hy : k ≤ y) (hb : k ≤ b) :
    (((y+1)*(b+1)*(b+1) - (y-k+1)*(b-k+1)*(b+1) : ℕ) : ℤ) =
      ((b : ℤ)+1) * lostMonomials y b k := by
  simp only [Nat.cast_sub (reduced_rectangle_le y b k), Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub hy, Nat.cast_sub hb, lostMonomials]
  ring

theorem sharp_virtual_quotient_rank {K : Type*} [Field K]
    (l : ℕ) (hl : 0 < l) (m y b : ℕ) (hym : m ≤ y) (hbm : m ≤ b) (second : Bool)
    (q : Polynomial (SeedValue K)) (q0 : q.coeff 0 ≠ 0)
    (qDegree : ∀ n i, (q.coeff n).degreeOf i ≤ singleSeedWidth second i) :
    6 * (Module.finrank K
      (RectangleJet (K := K) (l*m) (rectangleCap y b) ⧸
        virtualContactSpace (K := K) (l*m) l m q (rectangleCap y b)) : ℤ) ≤
      (l : ℤ) * (b+1) * m * (m+1) * (3*(y+b+1)-2*((m : ℤ)-1)) := by
  classical
  let order (i : Fin (l*m)) := m - (i:ℕ)/l
  have hvalid (i : Fin (l*m)) : order i ≤ m ∧ l * (m-order i) ≤ (i:ℕ) :=
    order_from_layer l m i
  have hcap (i : Fin (l*m)) (j : Fin 3) :
      order i * singleSeedWidth second j ≤ rectangleCap y b j := by
    have hy := (hvalid i).1.trans hym
    have hb := (hvalid i).1.trans hbm
    cases second <;> fin_cases j <;> simp_all [rectangleCap, singleSeedWidth]
  have rank := quotient_rank_le (l*m) l m (rectangleCap y b) (singleSeedWidth second)
    q q0 order hvalid hcap qDegree
  simp only [rectangleCap_product, reduced_rectangle_product] at rank
  let full := (y+1)*(b+1)*(b+1)
  let reduced (i : Fin (l*m)) := (y-order i+1)*(b-order i+1)*(b+1)
  have splitSum : l*m*full - (∑ i : Fin (l*m), reduced i) =
      ∑ i : Fin (l*m), (full-reduced i) := by
    have constant : l*m*full = ∑ _i : Fin (l*m), full := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [constant]
    symm
    apply Finset.sum_tsub_distrib
    exact fun i _ => reduced_rectangle_le y b (order i)
  change _ ≤ l*m*full - (∑ i : Fin (l*m), reduced i) at rank
  rw [splitSum] at rank
  calc
    _ ≤ (6:ℤ) * (∑ i : Fin (l*m), (full-reduced i) : ℕ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast rank) (by norm_num)
    _ = 6 * ∑ i ∈ Finset.range (l*m), ((b:ℤ)+1) * lostMonomials y b (m-i/l) := by
      rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact loss_cast ((hvalid i).1.trans hym) ((hvalid i).1.trans hbm)
    _ = _ := sharp_rank_sum l hl m y b

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
