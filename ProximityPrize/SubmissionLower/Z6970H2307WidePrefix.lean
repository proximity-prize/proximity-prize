import ProximityPrize.SubmissionLower.Z6970ExpandedColumns
import ProximityPrize.SubmissionLower.Fast068

set_option autoImplicit false
set_option Elab.async false

namespace Height2307WidePrefix
open K1_13_2 K1_13_2_2 K1_13_8_1 Finset
open scoped BigOperators

noncomputable section

private abbrev Slot := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ
private def slots (b j : ℕ) : Finset Slot :=
  (Finset.range (min b (j / 3) + 1)).sigma (fun z =>
    (Finset.range (min (b - z) ((j - 3 * z) / 2) + 1)).sigma (fun y =>
      (Finset.range (min (b - z - y) (j - 3 * z - 2 * y) + 1)).sigma (fun x =>
        Finset.range (b - z - y - x + 1))))
private def slotGrade (q : Slot) : ℕ := q.2.2.2 + q.2.2.1 + q.2.1 + q.1
private def slotWeight (q : Slot) : ℕ := q.2.2.1 + 2 * q.2.1 + 3 * q.1
private theorem mem_slots (q : Slot) (b j : ℕ) :
    q ∈ slots b j ↔ slotGrade q ≤ b ∧ slotWeight q ≤ j := by
  rcases q with ⟨z, y, x, a⟩
  simp only [slots, Finset.mem_sigma, Finset.mem_range, slotGrade, slotWeight]
  constructor
  · rintro ⟨hz, hy, hx, ha⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨hb, hj⟩
    exact ⟨by omega, by omega, by omega, by omega⟩
private theorem card_slots (b j : ℕ) : (slots b j).card = K1_13.symbols b j := by
  simp only [slots, K1_13.symbols, Finset.card_sigma, Finset.card_range]
private def slotOf (e : JetExp) : Slot := ⟨e 3, e 2, e 1, e 0⟩
private def exponentOf (q : Slot) : JetExp :=
  Finsupp.equivFunOnFinite.symm ![q.2.2.2, q.2.2.1, q.2.1, q.1]
private theorem grade_eq (e : JetExp) : e.weight gradeWeight = slotGrade (slotOf e) := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_succ, gradeWeight, slotGrade, slotOf, Nat.add_assoc]
private theorem weight_eq (e : JetExp) : e.weight oldWeight = slotWeight (slotOf e) := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_succ, oldWeight, slotWeight, slotOf]
  ring
private theorem exponentOf_slotOf (e : JetExp) : exponentOf (slotOf e) = e := by
  ext i
  fin_cases i <;> simp [exponentOf, slotOf]
private theorem slotOf_exponentOf (q : Slot) : slotOf (exponentOf q) = q := by
  rcases q with ⟨z, y, x, a⟩
  simp [slotOf, exponentOf]
private theorem card_slot_fiber (b j d : ℕ) (hd : d ≤ b) :
    ((slots b j).filter (fun q => slotGrade q = d)).card =
      (cumulativeColumns d j).card := by
  apply Finset.card_nbij' exponentOf slotOf
  · intro q hq
    obtain ⟨hmem, hgrade⟩ := Finset.mem_filter.mp hq
    have hw := (mem_slots q b j).mp hmem
    apply mem_cumulativeColumns.mpr
    change ((exponentOf q).weight gradeWeight : ℤ) = d ∧
      ((exponentOf q).weight oldWeight : ℤ) ≤ j
    rw [grade_eq, weight_eq, slotOf_exponentOf]
    exact ⟨by exact_mod_cast hgrade, by exact_mod_cast hw.2⟩
  · intro e he
    have hmem := mem_cumulativeColumns.mp he
    change (e.weight gradeWeight : ℤ) = d ∧ (e.weight oldWeight : ℤ) ≤ j at hmem
    rw [grade_eq, weight_eq] at hmem
    refine Finset.mem_filter.mpr ⟨(mem_slots _ b j).mpr ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · omega
  · exact fun q _ => slotOf_exponentOf q
  · exact fun e _ => exponentOf_slotOf e
private theorem symbols_eq_sum (b j : ℕ) :
    (K1_13.symbols b j : ℤ) =
      ∑ d ∈ Finset.range (b + 1), ((cumulativeColumns d j).card : ℤ) := by
  rw [← Nat.cast_sum]
  congr 1
  rw [← card_slots]
  calc
    _ = ∑ d ∈ Finset.range (b + 1), ((slots b j).filter (fun q => slotGrade q = d)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro q hq
      have hg := ((mem_slots q b j).mp hq).1
      exact Finset.mem_range.mpr (by omega)
    _ = _ := Finset.sum_congr rfl fun d hd =>
      card_slot_fiber b j d (by simpa using Finset.mem_range.mp hd)

theorem cumulative_fast (b j : ℕ) :
    ∑ d ∈ range (b+1), cumulative (d : ℤ) (j : ℤ) = K1_13_8.fastSymbols b j := by
  rw [← symbols_eq_fast]
  rw [symbols_eq_sum]
  apply sum_congr rfl
  intro d _
  exact (K1_13_2_2_2.proof d j).symm

private theorem cumulative_of_index_le {d j : ℤ} (h0 : 0 ≤ j) (h : j ≤ d) :
    cumulative d j = denominator j := by
  have hd : ¬ d < 0 := by omega
  have hj : ¬ j < 0 := by omega
  have hmin : min j (3*d) = j := min_eq_left (by omega)
  have h1 : j-d-1 < 0 := by omega
  have h2 : j-d-2 < 0 := by omega
  have h3 : j-d-3 < 0 := by omega
  have h4 : j-2*d-3 < 0 := by omega
  have h5 : j-2*d-4 < 0 := by omega
  have h6 : j-2*d-5 < 0 := by omega
  have h7 : j-3*d-6 < 0 := by omega
  simp [cumulative,hd,hj,hmin,denominator,h1,h2,h3,h4,h5,h6,h7]

theorem capped_stable {d q j : ℕ} (hj : j ≤ d) (hd : d ≤ q) :
    cappedCount (d : ℤ) (j : ℤ) 500 = cappedCount (q : ℤ) (j : ℤ) 500 := by
  have hdj : (j : ℤ) ≤ (d : ℤ) := by exact_mod_cast hj
  have hdq : (d : ℤ) ≤ (q : ℤ) := by exact_mod_cast hd
  have h0 : 0 ≤ (j : ℤ) := by positivity
  unfold cappedCount
  rw [if_neg (by norm_num : ¬ (500 : ℤ) < 0),
    cumulative_of_index_le h0 hdj, cumulative_of_index_le h0 (hdj.trans hdq)]
  congr 1
  by_cases h : (j : ℤ) - 3*(500+1) < 0
  · have hjneg : j < 1503 := by omega
    simp [cumulative, hjneg]
  · rw [cumulative_of_index_le (by omega : 0 ≤ (j : ℤ) - 3*(500+1)) (by omega),
        cumulative_of_index_le (by omega : 0 ≤ (j : ℤ) - 3*(500+1)) (by omega)]

private theorem shift_grade (b j : ℕ) :
    (∑ q ∈ range (b+1), cumulative ((q : ℤ)-501) ((j : ℤ)-1503)) =
      if 501 ≤ b ∧ 1503 ≤ j then (K1_13_8.fastSymbols (b-501) (j-1503) : ℤ) else 0 := by
  by_cases hj : 1503 ≤ j
  · by_cases hb : 501 ≤ b
    · have hB : b+1 = 501+(b-501+1) := by omega
      rw [if_pos ⟨hb,hj⟩, hB, sum_range_add]
      have hzero : (∑ q ∈ range 501, cumulative ((q : ℤ)-501) ((j : ℤ)-1503)) = 0 := by
        apply sum_eq_zero
        intro q hq
        have he := mem_range.mp hq
        simp [cumulative, show (q : ℤ)-501 < 0 by omega]
      rw [hzero,zero_add,← cumulative_fast]
      apply sum_congr rfl
      intro q _
      have hq : (((501+q : ℕ) : ℤ)-501) = q := by omega
      rw [hq, Int.ofNat_sub hj]
      rfl
    · rw [if_neg (fun h => hb h.1)]
      apply sum_eq_zero
      intro q hq
      have he := mem_range.mp hq
      simp [cumulative, show (q : ℤ)-501 < 0 by omega]
  · rw [if_neg (fun h => hj h.2)]
    apply sum_eq_zero
    intro q _
    simp [cumulative, show (j : ℤ)-1503 < 0 by omega]

def fastPrefix (b j : ℕ) : ℤ :=
  (K1_13_8.fastSymbols b j : ℤ) -
    (if 501 ≤ b ∧ 1503 ≤ j then (K1_13_8.fastSymbols (b-501) (j-1503) : ℤ) else 0)

theorem exact_prefix (b j : ℕ) (hb : b ≤ 3513) (hj : j ≤ 1679) :
    (∑ q ∈ range (b+1), cappedCount (ExpandedColumns6970.gradeCap q) j 500) = fastPrefix b j := by
  calc
    _ = ∑ q ∈ range (b+1), cappedCount (q : ℤ) j 500 := by
      apply sum_congr rfl
      intro q hq
      have hq' := mem_range.mp hq
      rw [ExpandedColumns6970.gradeCap, ExpandedTaper6970.cap, if_pos (show q < 3514 by omega)]
      by_cases hq0 : q ≤ 1679
      · rw [min_eq_left hq0]
      · rw [min_eq_right (by omega : 1679 ≤ q)]
        exact capped_stable hj (by omega)
    _ = _ := by
      unfold fastPrefix
      rw [← cumulative_fast, ← shift_grade]
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro q _
      unfold cappedCount
      norm_num <;> congr 1 <;> ring

end
end Height2307WidePrefix
