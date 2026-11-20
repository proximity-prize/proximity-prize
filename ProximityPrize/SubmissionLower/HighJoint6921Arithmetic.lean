import ProximityPrize.SubmissionLower.HighJoint6921Mass

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace HighJoint6921

open K1_14 Finset
open scoped BigOperators

private theorem sum_if_Ico (j n a c : ℕ) (hja : j ≤ a) :
    (∑ q ∈ Ico j n, if a ≤ q then c else 0) = (n - a) * c := by
  rw [← Finset.sum_filter]
  have hfilter : (Ico j n).filter (fun q => a ≤ q) = Ico a n := by
    ext q
    simp only [mem_filter, mem_Ico]
    omega
  rw [hfilter, Finset.sum_const, Nat.card_Ico, smul_eq_mul]

/-- Ignore the true-weight cutoff in each surviving ordinate. This preserves
a useful uniform upper bound on the quotient dimensions. -/
private theorem ordinate_positions (s : Shape) (h W j e step : ℕ) :
    (width s h W j - forcedPower s h W j * e) *
        slots s.U (forcedPower s h W j * step) ≤
      ∑ q ∈ Ico j (s.B + 1),
        if j + forcedPower s h W j * e ≤ q then
          slots s.U (forcedPower s h W j * step) else 0 := by
  rw [sum_if_Ico _ _ _ _ (Nat.le_add_right _ _)]
  apply Nat.mul_le_mul_right
  unfold width
  omega

/-- A positive forced power has at most one full cutoff block of width H.
The zero power uses the j blocks preceding it. -/
private theorem sum_cutoff_blocks (T H j R : ℕ) (hH : 0 < H) (g : ℕ → ℕ) :
    (∑ W ∈ range T,
        if 1 + (T - 1 - W) / H - j ≤ R then g (1 + (T - 1 - W) / H - j) else 0) ≤
      H * (j * g 0 + ∑ r ∈ range R, g (r + 1)) := by
  let S := (range T).filter (fun W => 1 + (T - 1 - W) / H - j ≤ R)
  let pair (W : ℕ) : ℕ × ℕ := ((T - 1 - W) / H, (T - 1 - W) % H)
  have hi : Set.InjOn pair (S : Set ℕ) := by
    intro W hW V hV he
    have hWt := mem_range.mp (mem_filter.mp hW).1
    have hVt := mem_range.mp (mem_filter.mp hV).1
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    change (T - 1 - W) / H = (T - 1 - V) / H at h₁
    change (T - 1 - W) % H = (T - 1 - V) % H at h₂
    have heq := Nat.mod_add_div (T - 1 - W) H
    rw [h₁, h₂, Nat.mod_add_div] at heq
    omega
  have hp : ∀ W ∈ S, pair W ∈ range (j + R) ×ˢ range H := by
    intro W hW
    have h := (mem_filter.mp hW).2
    apply mem_product.mpr
    exact ⟨mem_range.mpr (by change (T - 1 - W) / H < _; omega),
      mem_range.mpr (Nat.mod_lt _ hH)⟩
  have hsplit : (∑ d ∈ range (j + R), g (1 + d - j)) =
      j * g 0 + ∑ r ∈ range R, g (r + 1) := by
    rw [Finset.sum_range_add]
    congr 1
    · calc
        _ = ∑ _d ∈ range j, g 0 := by
          apply sum_congr rfl
          intro d hd
          have hd' := mem_range.mp hd
          congr 1
          omega
        _ = _ := by simp
    · apply sum_congr rfl
      intro r _
      congr 1
      omega
  rw [← sum_filter]
  calc
    _ ≤ ∑ p ∈ range (j + R) ×ˢ range H, g (1 + p.1 - j) := by
      apply Finset.sum_le_sum_of_injOn pair hi
      · intro p hp'
        obtain ⟨W, hW, rfl⟩ := mem_image.mp hp'
        exact hp W hW
      · intro W hW
        exact le_rfl
      · intro p _ _
        exact Nat.zero_le _
    _ = _ := by
      rw [Finset.sum_product]
      simp only [sum_const, card_range, smul_eq_mul, ← Finset.mul_sum, hsplit]

private theorem quotient_at_position (s : Shape) (h e step j q : ℕ)
    (hh : 0 < h) (he : 0 < e) (hjq : j ≤ q) :
    (∑ W ∈ range (top s),
      if j + forcedPower s h W j * e ≤ q then slots s.U (forcedPower s h W j * step) else 0) ≤
      (2*h) * (j * triangle s.U +
        ∑ r ∈ range ((q - j)/e), slots s.U ((r+1)*step)) := by
  have htest (d : ℕ) : j + d * e ≤ q ↔ d ≤ (q-j)/e := by
    rw [Nat.le_div_iff_mul_le he]
    omega
  simp only [htest, forcedPower]
  have hzero : slots s.U (0 * step) = triangle s.U := by simp [slots]
  have hh' : 0 < 2*h := Nat.mul_pos (by decide) hh
  simpa only [hzero] using
    (sum_cutoff_blocks (top s) (2*h) j ((q-j)/e) hh' (fun d => slots s.U (d*step)))

private def positivePrefix (M L : ℕ) : ℕ :=
  let n := min M L
  n * M - n * (n-1) / 2

private theorem sum_falling (M L : ℕ) :
    (∑ j ∈ range L, (M-j)) = positivePrefix M L := by
  let n := min M L
  have htrim : (∑ j ∈ range n, (M-j)) = ∑ j ∈ range L, (M-j) := by
    apply sum_subset (range_mono (min_le_right _ _))
    intro j hj hnj
    have hJL := mem_range.mp hj
    simp only [mem_range, not_lt, min_le_iff] at hnj
    omega
  rw [← htrim]
  have hsum : (∑ j ∈ range n, (M-j)) + (∑ j ∈ range n, j) = n*M := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _j ∈ range n, M := by
        apply sum_congr rfl
        intro j hj
        have h := (mem_range.mp hj).le.trans (min_le_left M L)
        omega
      _ = _ := by simp
  rw [Finset.sum_range_id] at hsum
  change _ = n * M - n * (n-1)/2
  omega

def seedPenalty (s : Shape) (e step : ℕ) : ℕ :=
  ∑ r ∈ range (s.B/e), slots s.U ((r+1)*step) *
    positivePrefix (s.B + 1 - (r+1)*e) (s.J+1)

private theorem seed_sum (s : Shape) (e step : ℕ) (he : 0 < e) :
    (∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1),
      ∑ r ∈ range ((q-j)/e), slots s.U ((r+1)*step)) = seedPenalty s e step := by
  have point {j q : ℕ} (hq : q ∈ Ico j (s.B+1)) :
      (∑ r ∈ range ((q-j)/e), slots s.U ((r+1)*step)) =
        ∑ r ∈ range (s.B/e), if j+(r+1)*e ≤ q then slots s.U ((r+1)*step) else 0 := by
    have hq' := mem_Ico.mp hq
    have hdiv (r : ℕ) : j+(r+1)*e ≤ q ↔ r < (q-j)/e := by
      rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le he]
      change _ ↔ (r+1)*e ≤ q-j
      omega
    simp only [hdiv, ← Finset.sum_filter, ← mem_range]
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr]
    exact range_mono (Nat.div_le_div_right (by omega))
  calc
    _ = ∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1), ∑ r ∈ range (s.B/e),
        if j+(r+1)*e ≤ q then slots s.U ((r+1)*step) else 0 := by
      exact sum_congr rfl fun j _ => sum_congr rfl fun q hq => point hq
    _ = ∑ r ∈ range (s.B/e), ∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1),
        if j+(r+1)*e ≤ q then slots s.U ((r+1)*step) else 0 := by
      calc
        _ = ∑ j ∈ range (s.J+1), ∑ r ∈ range (s.B/e), ∑ q ∈ Ico j (s.B+1),
            if j+(r+1)*e ≤ q then slots s.U ((r+1)*step) else 0 :=
          sum_congr rfl fun _ _ => sum_comm
        _ = _ := sum_comm
    _ = _ := by
      unfold seedPenalty
      apply sum_congr rfl
      intro r _
      have hsub (j : ℕ) : s.B+1-(j+(r+1)*e) = s.B+1-(r+1)*e-j := by omega
      simp_rw [sum_if_Ico _ _ _ _ (Nat.le_add_right _ _), hsub]
      rw [← Finset.sum_mul, sum_falling, Nat.mul_comm]

private theorem shape_sum_flip (s : Shape) (g : ℕ → ℕ → ℕ) :
    shapeSum s g = ∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1), g q j := by
  unfold shapeSum
  calc
    _ = ∑ q ∈ range (s.B+1), ∑ j ∈ range (s.J+1), if j ≤ q then g q j else 0 := by
      apply sum_congr rfl
      intro q _
      rw [← sum_filter]
      congr 1
      ext j
      simp only [mem_range, mem_filter, Nat.lt_succ_iff, le_min_iff]
      omega
    _ = ∑ j ∈ range (s.J+1), ∑ q ∈ range (s.B+1), if j ≤ q then g q j else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [← sum_filter]
      congr 1
      ext q
      simp only [mem_filter, mem_range, mem_Ico]
      omega

def columnCount (s : Shape) : ℕ := ∑ q ∈ range (s.B+1), (min q s.J+1)

def gradeMoment (s : Shape) : ℕ := ∑ q ∈ range (s.B+1), q * (min q s.J+1)

def indexMoment (s : Shape) : ℕ := ∑ q ∈ range (s.B+1), (min q s.J+1) * min q s.J / 2

def ordinatePenalty (s : Shape) (e step : ℕ) : ℕ :=
  triangle s.U * indexMoment s + seedPenalty s e step

theorem quotient_le (s : Shape) (h e step : ℕ) (hh : 0 < h) (he : 0 < e) :
    quotientVolume s h e step ≤ 2*h * ordinatePenalty s e step := by
  unfold quotientVolume
  calc
    _ ≤ ∑ W ∈ range (top s), ∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1),
          if j+forcedPower s h W j*e ≤ q then slots s.U (forcedPower s h W j*step)
          else 0 :=
      sum_le_sum fun W _ => sum_le_sum fun j _ => ordinate_positions s h W j e step
    _ = ∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1), ∑ W ∈ range (top s),
          if j+forcedPower s h W j*e ≤ q then slots s.U (forcedPower s h W j*step)
          else 0 := by
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_comm
    _ ≤ ∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1),
          2*h * (j * triangle s.U + ∑ r ∈ range ((q-j)/e), slots s.U ((r+1)*step)) :=
      sum_le_sum fun j _ => sum_le_sum fun q hq =>
        quotient_at_position s h e step j q hh he (mem_Ico.mp hq).1
    _ = _ := by
      have hm : (∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1), j * triangle s.U) =
          indexMoment s * triangle s.U := by
        have hindex : shapeSum s (fun _ j => j) = indexMoment s := by
          unfold shapeSum indexMoment
          simp [Finset.sum_range_id]
        rw [← hindex, shape_sum_flip]
        simp only [Finset.sum_mul]
      calc
        _ = 2*h * ((∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1), j * triangle s.U) +
            (∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1),
              ∑ r ∈ range ((q-j)/e), slots s.U ((r+1)*step))) := by
          simp only [Nat.mul_add, Finset.mul_sum, Finset.sum_add_distrib]
        _ = _ := by
          rw [hm, seed_sum s e step he]
          simp only [ordinatePenalty, Nat.mul_comm (indexMoment s)]

theorem raw_add_grade (s : Shape) (h : ℕ) (hwidth : s.B * base h ≤ top s) :
    rawVolume s h + triangle s.U * (base h * gradeMoment s) =
      triangle s.U * (top s * columnCount s + indexMoment s) := by
  unfold rawVolume
  rw [← Nat.mul_add]
  congr 1
  unfold shapeSum gradeMoment columnCount indexMoment
  simp only [Finset.mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  have hq' : q ≤ s.B := Nat.le_of_lt_succ (mem_range.mp hq)
  have hb := (Nat.mul_le_mul_right (base h) hq').trans hwidth
  have hsum :
      (∑ j ∈ range (min q s.J + 1), rawWidth s h q j) +
        (∑ _j ∈ range (min q s.J + 1), q * base h) =
      (∑ _j ∈ range (min q s.J + 1), top s) + ∑ j ∈ range (min q s.J+1), j := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    unfold rawWidth
    omega
  rw [Finset.sum_range_id] at hsum
  simpa only [sum_const, card_range, smul_eq_mul, Nat.add_sub_cancel, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm] using hsum

end HighJoint6921
