import ProximityPrize.SubmissionLower.R6966ProofSpreadGain

set_option Elab.async false

namespace Research6966.SpreadWindow
open Finset
open K1_14 (Shape shapeSum)
open K1_14_4 (gradeWidth gradeWidth_card shapeSum_swap)
open PadeFiltered (physicalWindow)
open KoalaRect (area rectCapacity rectPower rectGrade)
set_option maxHeartbeats 1000000

def size (B J : ℕ) : ℕ :=
  let j := min B J
  (j+1)*(B+1)-j*(j+1)/2

def boundary (B J step W : ℕ) : ℕ :=
  let q := min B (W/step)
  size q J + if q < B then min J (q+1)+1-((q+1)*step-W) else 0

def lex (B J e k : ℕ) : ℕ :=
  size B J-SpreadLines.minSum (B+1) 1 (k*e) e (min k (min (J+1) (B+1)))

theorem size_eq (B J : ℕ) : size B J = ∑ j ∈ range (J+1), (B+1-j) := by
  let t := min B J
  have tj : t≤J := min_le_right _ _
  have cut : (∑ j ∈ range (t+1), (B+1-j)) = ∑ j ∈ range (J+1), (B+1-j) := by
    apply sum_subset (range_mono (Nat.succ_le_succ tj))
    intro j mem out
    simp only [mem_range] at mem out
    dsimp only [t] at out
    omega
  rw [← cut]
  have eq : (∑ j ∈ range (t+1), (B+1-j)) + ∑ j ∈ range (t+1), j = (t+1)*(B+1) := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _j ∈ range (t+1), (B+1) := by
        apply sum_congr rfl
        intro j hj
        have bound := (mem_range.mp hj).le.trans (Nat.succ_le_succ (min_le_left B J))
        exact Nat.sub_add_cancel bound
      _ = _ := by simp
  rw [sum_range_id,Nat.add_sub_cancel,Nat.mul_comm (t+1) t] at eq
  unfold size
  change (t+1)*(B+1)-t*(t+1)/2 = _
  omega

private theorem shape_size (B J : ℕ) :
    (∑ q ∈ range (B+1), (min q J+1)) = size B J := by
  let s : Shape := ⟨0,B,J,0⟩
  have e := shapeSum_swap s (fun _ _ => 1)
  simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.mul_one, card_range, shapeSum, s] at e
  exact e.symm.trans (size_eq B J).symm

theorem weight_iff (step j i W : ℕ) (pos : 0 < step) :
    step*i+(step-1)*j≤W ↔ (j+i)*step≤W+j := by
  have v := congrArg (fun t => t*j) (Nat.sub_add_cancel pos : step-1+1=step)
  rw [Nat.add_mul,Nat.one_mul] at v
  rw [Nat.add_mul, Nat.mul_comm j step, Nat.mul_comm i step]
  omega

private theorem card_slope (B J step W : ℕ) (wp : 0 < step) :
    (physicalWindow B J step W).card = ∑ j ∈ range (J+1), gradeWidth step B W j := by
  classical
  rw [physicalWindow,PadeRank.positions,filter_filter,card_filter,sum_product]
  apply sum_congr rfl
  intro j _
  rw [← card_filter]
  have row : ((range (B+1)).filter (fun i =>
      j+i<B+1 ∧ step*i+(step-1)*j≤W)) = range (gradeWidth step B W j) := by
    ext i
    simp only [mem_filter,mem_range,weight_iff step j i W wp,gradeWidth,
      ← Nat.le_div_iff_mul_le wp]
    omega
  rw [row,card_range]

private theorem card_grade (B J step W : ℕ) (wp : 0 < step) :
    (physicalWindow B J step W).card =
      ∑ q ∈ range (B+1), ∑ j ∈ range (min q J+1), if q*step≤W+j then 1 else 0 := by
  let s : Shape := ⟨0,B,J,0⟩
  rw [card_slope B J step W wp]
  simp_rw [gradeWidth_card step B W _ wp]
  exact shapeSum_swap s (fun q j => if q*step≤W+j then 1 else 0)

theorem boundary_eq (B J step W : ℕ) (small : J < step) :
    boundary B J step W = (physicalWindow B J step W).card := by
  classical
  have wp : 0 < step := by omega
  rw [card_grade B J step W wp]
  let q := min B (W/step)
  let slots (i : ℕ) := ∑ j ∈ range (min i J+1), if i*step≤W+j then 1 else 0
  change size q J+(if q < B then min J (q+1)+1-((q+1)*step-W) else 0) =
    ∑ i ∈ range (B+1), slots i
  have qb : q≤B := min_le_left _ _
  have full : q*step≤W := (Nat.le_div_iff_mul_le wp).mp (min_le_right ..)
  have complete : (∑ i ∈ range (q+1), slots i) = size q J := by
    rw [← shape_size]
    apply sum_congr rfl
    intro i hi
    unfold slots
    have ready := (Nat.mul_le_mul_right step (Nat.lt_succ_iff.mp (mem_range.mp hi))).trans full
    have ready' (j : ℕ) : i*step≤W+j := ready.trans (Nat.le_add_right _ _)
    simp [ready']
  rw [← sum_range_add_sum_Ico slots (Nat.succ_le_succ qb),complete]
  congr 1
  by_cases next : q < B
  · rw [ite_eq_left next, sum_eq_single (q+1)]
    · have test (j : ℕ) : (q+1)*step≤W+j ↔ (q+1)*step-W≤j := by omega
      unfold slots
      simp only [test]
      rw [← card_filter]
      have eq : ((range (min (q+1) J+1)).filter (fun j => (q+1)*step-W≤j)) =
          Ico ((q+1)*step-W) (min (q+1) J+1) := by
        ext j
        simp [and_comm]
      rw [eq,Nat.card_Ico,min_comm]
    · intro i hi ne
      have qi : q+2 ≤ i := by have hh := (mem_Ico.mp hi).1; omega
      have exactQ : q=W/step := by dsimp only [q] at next ⊢; omega
      have strong : W<(q+1)*step := (Nat.div_lt_iff_lt_mul wp).mp (by omega)
      have width := Nat.mul_le_mul_right step qi
      rw [show q+2=(q+1)+1 by omega,Nat.add_mul,Nat.one_mul] at width
      apply sum_eq_zero
      intro j hj
      have jle := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans (min_le_right i J)
      rw [ite_eq_right (by omega)]
    · intro bad
      exact (bad (mem_Ico.mpr ⟨le_rfl,Nat.succ_lt_succ next⟩)).elim
  · rw [ite_eq_right next, show q=B by omega, Ico_self,sum_empty]

private theorem lex_loss_le (B J e k : ℕ) :
    SpreadLines.minSum (B+1) 1 (k*e) e (min k (min (J+1) (B+1))) ≤
      ∑ j ∈ range (J+1), min (B+1-j) ((k-j)*e) := by
  let m := min k (min (J+1) (B+1))
  have mj : m≤J+1 := (min_le_right _ _).trans (min_le_left _ _)
  refine (SpreadLines.minSum_le ..).trans ?_
  have eq (j : ℕ) : k*e-e*j=(k-j)*e := by
    rw [Nat.mul_comm k e,← Nat.mul_sub_left_distrib,Nat.mul_comm e (k-j)]
  simp only [Nat.one_mul,eq]
  exact sum_le_sum_of_subset_of_nonneg (range_mono mj) (by intros; exact Nat.zero_le _)

theorem lex_ge (B J e k : ℕ) :
    (∑ j ∈ range (J+1), ((B+1-j)-(k-j)*e)) ≤ lex B J e k := by
  have whole : (∑ j ∈ range (J+1), ((B+1-j)-(k-j)*e)) +
      (∑ j ∈ range (J+1), min (B+1-j) ((k-j)*e)) = size B J := by
    rw [size_eq,← sum_add_distrib]
    exact sum_congr rfl (fun j _ => by omega)
  have paid := lex_loss_le B J e k
  unfold lex
  omega

theorem rect_lex (A h e k W B : ℕ) (s : Shape) (U : Fin 2 → ℕ)
    (wp : 0 < 131071-h) (ep : 0 < e) (layer : rectPower A h s W = k)
    (cap : ∀ j ≤ s.J, gradeWidth (131071-h) s.B W j ≤ B+1-j) :
    rectCapacity A h s e U (fun _ => 0) W ≤ lex B s.J e k*area U := by
  rw [← KoalaRect.rectCapacity_eq A h s e U (fun _ => 0) W wp ep]
  have slots (r : ℕ) : KoalaRect.rectSlots U (fun _ => 0) r = area U := by
    simp [KoalaRect.rectSlots,area]
  simp only [rectGrade,layer,slots]
  rw [← sum_mul]
  refine Nat.mul_le_mul_right _ ((sum_le_sum (fun j hj =>
    Nat.sub_le_sub_right (cap j (Nat.lt_succ_iff.mp (mem_range.mp hj))) _)).trans (lex_ge ..))

theorem rect_zero (A h e W : ℕ) (s : Shape) (U : Fin 2 → ℕ)
    (wp : 0 < 131071-h) (ep : 0 < e)
    (far : s.J+s.B/e+1 < rectPower A h s W) :
    rectCapacity A h s e U (fun _ => 0) W = 0 := by
  rw [← KoalaRect.rectCapacity_eq A h s e U (fun _ => 0) W wp ep]
  apply sum_eq_zero
  intro j hj
  have jle := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have r : s.B/e < rectPower A h s W-j := by omega
  have gone := (Nat.div_lt_iff_lt_mul ep).mp r
  have cap : gradeWidth (131071-h) s.B W j ≤ s.B+1 := by unfold gradeWidth; omega
  unfold rectGrade
  dsimp only
  rw [Nat.sub_eq_zero_of_le (cap.trans (Nat.succ_le_of_lt gone)),Nat.zero_mul]

end Research6966.SpreadWindow
