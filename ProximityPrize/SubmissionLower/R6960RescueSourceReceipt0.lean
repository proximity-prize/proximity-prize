import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic

-- merged module R6960RescueSourceArithmetic
section Merged_R6960RescueSourceArithmetic
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.RescueSource
open Finset
open K1_14 (Shape slots)
open P1_7_6 (Quad intervalProduct intervalProduct_eq)
open P1_7_1_3 (evaluate evaluate_eq)
open HelperSource (column column_eq phaseLayer compressedPhase)
open K1_14_2_1 (twice_sum_linear)
def triangularWidth (C D L H U : ℕ) : ℤ :=
  intervalProduct (Quad.ofLines U (-1) (2*(C : ℤ)-D*((U : ℤ)-1)) (2-(D : ℤ)))
    ⟨1,0,0⟩ L (min H U)
private theorem twice_width_row (C D j U : ℕ) (hj : j≤U) :
    2*(∑ q ∈ Ico j U, ((C : ℤ)+j-D*(q : ℤ))) =
      ((U : ℤ)-j)*(2*C-D*((U : ℤ)-1)+(2-(D : ℤ))*j) := by
  rw [sum_Ico_eq_sum_range]
  simp only [Nat.cast_add]
  have he (a : ℕ) : (C : ℤ)+j-D*((j : ℤ)+a) = ((C : ℤ)+j-D*(j : ℤ))+(-(D : ℤ))*a := by ring
  simp_rw [he, twice_sum_linear, Nat.cast_sub hj]
  ring
private theorem triangularWidth_eq (C D L H U : ℕ) :
    triangularWidth C D L H U =
      120*(∑ j ∈ Ico L H, ∑ q ∈ Ico j U, ((C : ℤ)+j-D*(q : ℤ))) := by
  unfold triangularWidth
  rw [← intervalProduct_eq]
  have hs : (Ico L (min H U)) ⊆ Ico L H := fun j hj =>
    mem_Ico.mpr ⟨(mem_Ico.mp hj).1, (mem_Ico.mp hj).2.trans_le (min_le_left _ _)⟩
  rw [← sum_subset hs (f := fun j => ∑ q ∈ Ico j U, ((C : ℤ)+j-D*(q : ℤ))) (by
    intro j hj hnot
    have hU : U≤j := by
      simp only [mem_Ico, lt_min_iff] at hj hnot
      omega
    rw [Ico_eq_empty_of_le hU, sum_empty])]
  have hr :
      (∑ j ∈ Ico L (min H U),
        (Quad.ofLines U (-1) (2*(C : ℤ)-D*((U : ℤ)-1)) (2-(D : ℤ))).eval ↑j *
          (⟨1,0,0⟩ : Quad).eval ↑j) =
      ∑ j ∈ Ico L (min H U), 2*(∑ q ∈ Ico j U, ((C : ℤ)+j-D*(q : ℤ))) := by
    apply sum_congr rfl
    intro j hj
    have hu := (mem_Ico.mp hj).2.trans_le (min_le_right H U)
    rw [twice_width_row C D j U hu.le, Quad.eval_ofLines]
    simp [Quad.eval, sub_eq_add_neg]
  rw [hr, ← mul_sum]
  ring
private theorem division_split (C D j : ℕ) (hd : 0<D) (hj : j<D) :
    (C-1+j)/D =
      if j < D-(C-1)%D then (C-1)/D else (C-1)/D+1 := by
  let a := (C-1)/D
  let b := (C-1)%D
  have hb : b<D := Nat.mod_lt _ hd
  have he : b+D*a=C-1 := Nat.mod_add_div _ _
  change (C-1+j)/D = if j < D-b then a else a+1
  by_cases ht : j<D-b
  · rw [ite_eq_left ht]
    apply Nat.le_antisymm
    · apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul hd).2
      change C-1+j < (a+1)*D
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm a D]
      omega
    · apply (Nat.le_div_iff_mul_le hd).2
      rw [Nat.mul_comm a D]
      omega
  · rw [ite_eq_right ht]
    apply Nat.le_antisymm
    · apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul hd).2
      change C-1+j < (a+2)*D
      rw [Nat.add_mul, Nat.mul_comm a D, Nat.two_mul]
      omega
    · apply (Nat.le_div_iff_mul_le hd).2
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm a D]
      omega
private theorem clipped_column (C D j R : ℕ) (hc : 0<C) (hd : 0<D) :
    ((∑ q ∈ Ico j R, (C+j-q*D) : ℕ) : ℤ) =
      ∑ q ∈ Ico j (min R ((C-1+j)/D+1)), ((C : ℤ)+j-D*(q : ℤ)) := by
  have hs : Ico j (min R ((C-1+j)/D+1)) ⊆ Ico j R := fun q hq =>
    mem_Ico.mpr ⟨(mem_Ico.mp hq).1, (mem_Ico.mp hq).2.trans_le (min_le_left _ _)⟩
  have hw (q : ℕ) : q<(C-1+j)/D+1 ↔ q*D<C+j := by
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd]
    omega
  rw [← sum_subset hs (f := fun q => C+j-q*D) (by
    intro q hq hn
    have hless : ¬ q < (C-1+j)/D+1 := by
      intro h
      exact hn (mem_Ico.mpr ⟨(mem_Ico.mp hq).1, lt_min ((mem_Ico.mp hq).2) h⟩)
    exact Nat.sub_eq_zero_of_le (by have := mt (hw q).mpr hless; omega))]
  rw [Nat.cast_sum]
  apply sum_congr rfl
  intro q hq
  have hq' := (hw q).1 ((mem_Ico.mp hq).2.trans_le (min_le_right _ _))
  rw [Nat.cast_sub hq'.le]
  push_cast
  ring
private theorem sum_split (L H T : ℕ) (f : ℕ → ℤ) :
    (∑ j ∈ Ico L H, f j) =
      (∑ j ∈ Ico L (min H T), f j) + ∑ j ∈ Ico (max L T) H, f j := by
  have hl : (Ico L H).filter (· < T) = Ico L (min H T) := by
    ext j
    simp only [mem_filter, mem_Ico, lt_min_iff]
    tauto
  have hr : (Ico L H).filter (fun j => ¬ j < T) = Ico (max L T) H := by
    ext j
    simp only [mem_filter, mem_Ico, max_le_iff, not_lt]
    tauto
  rw [← hl, ← hr, sum_filter_add_sum_filter_not]
def layerWidth (C D L H R : ℕ) : ℤ :=
  let a := (C-1)/D+1
  let T := D-(C-1)%D
  triangularWidth C D L (min H T) (min R a) +
    triangularWidth C D (max L T) H (min R (a+1))
theorem layerWidth_eq (C D L H R : ℕ) (hc : 0<C) (hd : 0<D) (hH : H≤D) :
    layerWidth C D L H R =
      120*((∑ j ∈ Ico L H, ∑ q ∈ Ico j R, (C+j-q*D) : ℕ) : ℤ) := by
  unfold layerWidth
  simp only [triangularWidth_eq, Nat.cast_sum, clipped_column C D _ R hc hd, ← mul_add]
  congr 1
  let a := (C-1)/D+1
  let T := D-(C-1)%D
  rw [sum_split L H T]
  congr 1
  · apply sum_congr rfl
    intro j hj
    have hj' := (mem_Ico.mp hj).2
    have ht : j<T := hj'.trans_le (min_le_right _ _)
    have hD : j<D := hj'.trans_le ((min_le_left _ _).trans hH)
    rw [division_split C D j hd hD, ite_eq_left ht]
  · apply sum_congr rfl
    intro j hj
    have ht : ¬ j<T := not_lt_of_ge ((le_max_right _ _).trans (mem_Ico.mp hj).1)
    have hD : j<D := (mem_Ico.mp hj).2.trans_le hH
    rw [division_split C D j hd hD, ite_eq_right ht]
def fastLayer (s : Shape) (A h r d c v δ i : ℕ) : ℕ :=
  slots s.U ((i+δ)*v) *
    ((layerWidth (s.m*A-2*h*(r+i)) (131071-h) ((i+δ)*d) (s.J+1) (s.B+1-(i+δ)*c)).toNat / 120)
theorem fastLayer_eq (s : Shape) (A h r d c v δ i : ℕ)
    (hJ : s.J<131071-h) (hi : 2*h*(r+i)<s.m*A) :
    fastLayer s A h r d c v δ i = phaseLayer s A h r d c v δ i := by
  unfold fastLayer phaseLayer
  rw [evaluate_eq, ← sum_Ico_eq_sum_range,
    layerWidth_eq _ _ _ _ _ (by omega) (by omega) (by omega)]
  have hc (n : ℕ) : (120*(n : ℤ)).toNat/120 = n := by
    have he : (120 : ℤ)*(n : ℤ) = ((120*n : ℕ) : ℤ) :=
      (Nat.cast_mul (α := ℤ) 120 n).symm
    rw [he, Int.toNat_natCast, Nat.mul_div_cancel_left _ (by decide)]
  rw [hc]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [column_eq]
  apply sum_congr rfl
  intro q _
  omega
def fastPhase (s : Shape) (A h r d c v δ : ℕ) : ℕ :=
  evaluate (fastLayer s A h r d c v δ) (s.J/d+1)
theorem fastPhase_eq (s : Shape) (A h r d c v δ : ℕ)
    (hJ : s.J<131071-h) (hi : 2*h*(r+s.J/d)<s.m*A) :
    fastPhase s A h r d c v δ = compressedPhase s A h r d c v δ := by
  unfold fastPhase compressedPhase
  simp only [evaluate_eq]
  apply sum_congr rfl
  intro i hi'
  have hle : i≤s.J/d := Nat.le_of_lt_succ (mem_range.mp hi')
  exact fastLayer_eq s A h r d c v δ i hJ
    ((Nat.mul_le_mul_left (2*h) (Nat.add_le_add_left hle r)).trans_lt hi)
#print axioms fastPhase_eq
end Lower6960.RescueSource

end Merged_R6960RescueSourceArithmetic

