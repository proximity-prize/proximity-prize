import ProximityPrize.SubmissionLower.Z6970ExpandedColumns

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ExpandedColumns6970
open Finset
open K1_13_2 (cappedCount cumulative)
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open scoped BigOperators

private theorem mem_band {d u t : ℤ} {e : JetExp} :
    e ∈ cappedColumns d u t ↔
      (e.weight gradeWeight : ℤ) = d ∧ (e.weight oldWeight : ℤ) ≤ u ∧ (e 3 : ℤ) ≤ t := by
  rw [mem_cappedColumns, K1_13_2_2.mem_cumulativeColumns]
  change (((e.weight gradeWeight : ℤ) = d ∧ (e.weight oldWeight : ℤ) ≤ u) ∧
    (e 3 : ℤ) ≤ t) ↔ _
  exact and_assoc

def indexMoment (d : ℕ) : ℤ :=
  24 * (1679 * cappedCount (d : ℤ) 1679 500 -
    ∑ u ∈ Finset.range 1679, cappedCount (d : ℤ) (u : ℤ) 500)

def sourceCount : ℤ := ∑ q ∈ range 4025, cappedCount (gradeCap q) 1679 500

def sourceDegree : ℤ := ∑ q ∈ range 4025, (q : ℤ) * cappedCount (gradeCap q) 1679 500

def sourceIndex24 : ℤ := ∑ q ∈ range 4025, indexMoment (gradeCap q)

private theorem count_range_ge (v j : ℕ) :
    (∑ u ∈ range j, if v ≤ u then (1 : ℕ) else 0) = j-v := by
  have hset : (range j).filter (fun u => v ≤ u) = Ico v j := by
    ext x
    simp [and_comm]
  rw [← sum_filter, ← card_eq_sum_ones, hset, Nat.card_Ico]

theorem indexMoment_eq (d : ℕ) :
    indexMoment d = 24 * ∑ e ∈ cappedColumns d 1679 500, (e.weight oldWeight : ℤ) := by
  let F := cappedColumns d 1679 500
  have hfilter (u : ℕ) (hu : u < 1679) :
      cappedColumns d u 500 = F.filter (fun m => m.weight oldWeight ≤ u) := by
    ext m
    simp only [F, mem_filter, mem_band]
    change ((m.weight K1_13_2_2.gradeWeight : ℤ) = d ∧ (m.weight oldWeight : ℤ) ≤ u ∧ (m 3 : ℤ) ≤ 500) ↔
      (((m.weight K1_13_2_2.gradeWeight : ℤ) = d ∧ (m.weight oldWeight : ℤ) ≤ 1679 ∧ (m 3 : ℤ) ≤ 500) ∧
        m.weight oldWeight ≤ u)
    constructor
    · rintro ⟨ha,hb,hc⟩; exact ⟨⟨ha, by omega, hc⟩, by omega⟩
    · rintro ⟨⟨ha,hb,hc⟩,hd⟩; exact ⟨ha, by omega, hc⟩
  have hswap : (∑ u ∈ range 1679, (cappedColumns d u 500).card) =
      ∑ e ∈ F, (1679 - e.weight oldWeight) := by
    calc
      _ = ∑ u ∈ range 1679, ∑ e ∈ F, if e.weight oldWeight ≤ u then 1 else 0 := by
        apply sum_congr rfl
        intro u hu
        rw [hfilter u (mem_range.mp hu), card_eq_sum_ones, sum_filter]
      _ = _ := by
        rw [sum_comm]
        exact sum_congr rfl fun e _ => count_range_ge _ _
  have hcast : (∑ u ∈ range 1679, cappedCount d (u : ℤ) 500) =
      ∑ e ∈ F, (1679 - (e.weight oldWeight : ℤ)) := by
    have hu (u : ℕ) := capped_card K1_13_2_2_2.proof (d : ℤ) (u : ℤ) 500
    simp_rw [← hu]
    rw [← Nat.cast_sum, hswap, Nat.cast_sum]
    apply sum_congr rfl
    intro e he
    have h := (mem_band.mp he).2.1
    rw [Nat.cast_sub (by exact_mod_cast h), Nat.cast_ofNat]
  unfold indexMoment
  rw [hcast, ← capped_card K1_13_2_2_2.proof d 1679 500]
  have hF : (cappedColumns d 1679 500).card = F.card := rfl
  rw [hF, sum_sub_distrib]
  simp only [sum_const, nsmul_eq_mul]
  ring

private theorem scaled_grade_columns (A D q : ℕ)
    (hb : D*q ≤ 3000*A) :
    24 * (∑ e ∈ cappedColumns (gradeCap q) 1679 500, (width A D q e : ℤ)) =
      (24 * (3000*(A : ℤ) - (D : ℤ)*q)) * cappedCount (gradeCap q) 1679 500 +
        indexMoment (gradeCap q) := by
  let d := gradeCap q
  have hwidth (e : JetExp) :
      (width A D q e : ℤ) = ((3000 : ℤ)*A - D*q) + e.weight oldWeight := by
    have hsub : D*q ≤ 3000*A + e.weight oldWeight := by omega
    simp only [width, Nat.cast_sub hsub, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  simp_rw [hwidth]
  rw [Finset.sum_add_distrib, mul_add]
  rw [indexMoment_eq, ← capped_card K1_13_2_2_2.proof (gradeCap q : ℤ) 1679 500]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem scaled_columns (A D : ℕ) (hA : 0<A) (hD : 3<D) (hb : D*4024 ≤ 3000*A) :
    24 * ((columns A D hD).card : ℤ) =
      24*(3000*(A : ℤ))*sourceCount - (24*(D : ℤ))*sourceDegree + sourceIndex24 := by
  rw [card_columns A D hA hD]
  simp only [tuples, card_sigma, card_range, Nat.cast_sum]
  rw [mul_sum]
  have hsum : (∑ q ∈ range 4025,
      24 * (∑ e ∈ cappedColumns (gradeCap q) 1679 500, (width A D q e : ℤ))) =
      ∑ q ∈ range 4025,
        (24*(3000*(A : ℤ))*cappedCount (gradeCap q) 1679 500 -
          (24*(D : ℤ))*((q : ℤ)*cappedCount (gradeCap q) 1679 500) + indexMoment (gradeCap q)) := by
    apply sum_congr rfl
    intro q hq
    have hq' : q ≤ 4024 := by have := mem_range.mp hq; omega
    rw [scaled_grade_columns A D q
      ((Nat.mul_le_mul_left D hq').trans hb)]
    ring
  rw [hsum, sum_add_distrib, sum_sub_distrib]
  simp only [sourceCount, sourceDegree, sourceIndex24, mul_sum]

end ExpandedColumns6970
