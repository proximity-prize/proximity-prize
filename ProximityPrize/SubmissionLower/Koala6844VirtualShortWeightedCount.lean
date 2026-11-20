import ProximityPrize.SubmissionLower.Koala6844VirtualShortSeedlessArithmetic


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open Koala6844Receipts

set_option autoImplicit false
set_option maxHeartbeats 3200000

private def trianglePairs (h : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (h+1)) ×ˢ (Finset.range (h+1))).filter (fun p => p.1+p.2 ≤ h)

private theorem mem_trianglePairs (p : ℕ × ℕ) (h : ℕ) : p ∈ trianglePairs h ↔ p.1+p.2 ≤ h := by
  simp only [trianglePairs,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
  omega

private def weight (z : ℕ) (p : ℕ × ℕ) : ℕ := z-p.1-p.2

private def diagonal (h : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (h+1)) ×ˢ (Finset.range (h+1))).filter (fun p => p.2≤p.1)

private theorem diagonalSum (h z : ℕ) :
    ∑ p ∈ trianglePairs h, weight z p = ∑ d ∈ Finset.range (h+1), (d+1)*(z-d) := by
  have hdiag : ∑ p ∈ trianglePairs h, weight z p = ∑ p ∈ diagonal h, (z-p.1) := by
    apply Finset.sum_bij (fun p _ => (p.1+p.2,p.1))
    · intro p hp
      have hh := (mem_trianglePairs p h).mp hp
      simp only [diagonal,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
      omega
    · intro p hp q hq he
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      apply Prod.ext <;> dsimp only at h₁ h₂ ⊢ <;> omega
    · intro p hp
      simp only [diagonal,Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hp
      refine ⟨(p.2,p.1-p.2),(mem_trianglePairs _ h).mpr (by dsimp; omega),?_⟩
      apply Prod.ext <;> dsimp <;> omega
    · intro p hp
      simp [weight, Nat.sub_sub]
  rw [hdiag]
  unfold diagonal
  rw [Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := Finset.mem_range.mp hd
  have hx : (∑ j ∈ Finset.range (h+1), if j ≤ d then z-d else 0) =
       ∑ j ∈ Finset.range (d+1), (if j ≤ d then z-d else 0) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hnot
    have hnd : ¬j ≤ d := fun hj => hnot (Finset.mem_range.mpr (by omega))
    simp [hnd]
  rw [hx]
  calc
    _ = ∑ _ ∈ Finset.range (d+1), (z-d) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact ite_eq_left (by have := Finset.mem_range.mp hj; omega)
    _ = _ := by simp

private theorem triangular_sum (h : ℕ) :
    (∑ d ∈ Finset.range (h+1), (d+1)) = triangle h := by
  have hs := SecondJetCounts.sum_fin_val (h+2)
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i),Finset.sum_range_succ'] at hs
  simpa [triangle,Nat.mul_comm] using hs

private theorem sum_consecutive_products (h : ℕ) :
    (∑ d ∈ Finset.range (h+1), (d+1)*d) = h*(h+1)*(h+2)/3 := by
  induction h with
  | zero => decide
  | succ h ih =>
    rw [Finset.sum_range_succ, ih]
    have he : (h+1)*(h+1+1)*(h+1+2) = h*(h+1)*(h+2)+(h+1+1)*(h+1)*3 := by ring
    change _ = (h+1)*(h+1+1)*(h+1+2)/3
    rw [he,Nat.add_mul_div_right _ _ (by decide)]

private theorem sum_trianglePairs (h z : ℕ) (hz : h ≤ z) :
    ∑ p ∈ trianglePairs h, weight z p = weightedTriangle h z := by
  rw [diagonalSum,weightedTriangle,←triangular_sum,←sum_consecutive_products,Finset.sum_mul]
  rw [← Finset.sum_tsub_distrib]
  · apply Finset.sum_congr rfl
    intro d hd
    exact Nat.mul_sub_left_distrib (d+1) z d
  · intro d hd
    exact Nat.mul_le_mul_left _ ((Nat.le_of_lt_succ (Finset.mem_range.mp hd)).trans hz)

private def shiftPairs (h a b : ℕ) : Finset (ℕ × ℕ) :=
  (trianglePairs h).filter (fun p => a≤p.1 ∧ b≤p.2)

private theorem sum_shiftPairs (h z a b : ℕ) (hz : h ≤ z) :
    ∑ p ∈ shiftPairs h a b, weight z p = shiftedWeightedTriangle h z (a+b) := by
  unfold shiftedWeightedTriangle
  by_cases hp : a+b ≤ h
  · rw [ite_eq_left hp,←sum_trianglePairs _ _ (by omega)]
    apply Finset.sum_bij (fun p _ => (p.1-a,p.2-b))
    · intro p hmem
      simp only [shiftPairs,Finset.mem_filter,mem_trianglePairs] at hmem
      exact (mem_trianglePairs _ _).mpr (by dsimp; omega)
    · intro p hp q hq he
      simp only [shiftPairs,Finset.mem_filter,mem_trianglePairs] at hp hq
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      apply Prod.ext <;> dsimp only at h₁ h₂ ⊢ <;> omega
    · intro p hmem
      have hh := (mem_trianglePairs _ _).mp hmem
      refine ⟨(p.1+a,p.2+b),?_,?_⟩
      · simp only [shiftPairs,Finset.mem_filter,mem_trianglePairs]; omega
      · apply Prod.ext <;> dsimp <;> omega
    · intro p hmem
      simp only [shiftPairs,Finset.mem_filter,mem_trianglePairs] at hmem
      change z-p.1-p.2 = z-(a+b)-(p.1-a)-(p.2-b)
      omega
  · rw [ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro p hmem
    simp only [shiftPairs,Finset.mem_filter,mem_trianglePairs] at hmem
    omega

private def weightedPairs (h a b : ℕ) : Finset (ℕ × ℕ) :=
  (trianglePairs h).filter (fun p => p.1<a ∧ p.2<b)

private theorem weightedRectangle_eq_filter (a b z h : ℕ) (hz : h ≤ z) :
    weightedRectangle a b z h = ∑ p ∈ weightedPairs h a b, weight z p := by
  let rect := weightedPairs h a b
  change _ = ∑ p ∈ rect, weight z p
  have hpart : (∑ p ∈ trianglePairs h, weight z p)+(∑ p ∈ shiftPairs h a b, weight z p) =
      (∑ p ∈ shiftPairs h a 0, weight z p)+(∑ p ∈ shiftPairs h 0 b, weight z p)+
      (∑ p ∈ rect, weight z p) := by
    simp only [rect,weightedPairs,shiftPairs,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : a ≤ p.1 <;> by_cases hq : b ≤ p.2 <;>
      simp [hp,hq,show (p.1<a) ↔ ¬ a≤p.1 by omega,show (p.2<b) ↔ ¬ b≤p.2 by omega]
  rw [sum_trianglePairs h z hz, sum_shiftPairs h z a b hz,
    sum_shiftPairs h z a 0 hz,sum_shiftPairs h z 0 b hz,Nat.add_zero,Nat.zero_add] at hpart
  unfold weightedRectangle
  omega


theorem weightedRectangle_eq_sum (a b z h : ℕ) (hz : h ≤ z) :
    weightedRectangle a b z h =
      ∑ i : Fin a, ∑ j : Fin b, if i.val+j.val ≤ h then z-i.val-j.val else 0 := by
  rw [weightedRectangle_eq_filter a b z h hz]
  let rect := weightedPairs h a b
  have hrect : ∑ p ∈ rect, weight z p =
      ∑ i : Fin a, ∑ j : Fin b, if i.val+j.val ≤ h then z-i.val-j.val else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j : Fin b, if i+j.val≤h then z-i-j.val else 0)]
    have hinner (i : ℕ) : (∑ j : Fin b, if i+j.val≤h then z-i-j.val else 0) =
        ∑ j ∈ Finset.range b, if i+j≤h then z-i-j else 0 :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ => if i+j≤h then z-i-j else 0) b
    simp_rw [hinner]
    let orig := ((Finset.range a) ×ˢ (Finset.range b)).filter (fun p : ℕ×ℕ => p.1+p.2 ≤ h)
    have he : rect = orig := by
      ext p
      simp only [rect,weightedPairs,orig,Finset.mem_filter,mem_trianglePairs,Finset.mem_product,Finset.mem_range]
      exact and_comm
    rw [he]
    simp only [orig,Finset.sum_filter,Finset.sum_product,weight]
  exact hrect

theorem weightedRectangle_mono {a a' b b' z z' h h' : ℕ}
    (ha : a'≤a) (hb : b'≤b) (hz : z'≤z) (hh : h'≤h) (hzc : h≤z) (hzc' : h'≤z') :
    weightedRectangle a' b' z' h' ≤ weightedRectangle a b z h := by
  rw [weightedRectangle_eq_filter _ _ _ _ hzc',weightedRectangle_eq_filter _ _ _ _ hzc]
  calc
    _ ≤ ∑ p ∈ weightedPairs h' a' b', weight z p := Finset.sum_le_sum fun p _ => by
      unfold weight
      omega
    _ ≤ _ := Finset.sum_le_sum_of_subset (by
      intro p hp
      simp only [weightedPairs,Finset.mem_filter,mem_trianglePairs] at hp ⊢
      omega)

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
