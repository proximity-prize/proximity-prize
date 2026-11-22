import ProximityPrize.SubmissionLower.Fast040
set_option autoImplicit true
section
namespace K1_13_1_1
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 6000
private theorem sumRange_succ (n : ℕ) (f : ℕ → ℕ) :
    sumRange (n + 1) f = sumRange n f + f n := rfl
theorem sumRange_add (a b : ℕ) (f : ℕ → ℕ) :
    sumRange (a + b) f = sumRange a f + sumRange b (fun i => f (i + a)) := by
  induction b with
  | zero => simp [sumRange]
  | succ b ih =>
    rw [Nat.add_succ, sumRange_succ, ih, sumRange_succ, Nat.add_assoc, Nat.add_comm a b]
private theorem sumRange_succ_left (n : ℕ) (f : ℕ → ℕ) :
    sumRange (n + 1) f = f 0 + sumRange n (fun i => f (i + 1)) := by
  rw [Nat.add_comm n 1, sumRange_add]
  simp [sumRange]
private theorem sumRange_zero (n : ℕ) (f : ℕ → ℕ) (h : ∀ i < n, f i = 0) :
    sumRange n f = 0 := by
  rw [sumRange_eq_sum]
  exact Finset.sum_eq_zero fun i hi => h i (Finset.mem_range.mp hi)
private theorem sumRange_congr (n : ℕ) {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) :
    sumRange n f = sumRange n g := by
  simp only [sumRange_eq_sum]
  exact Finset.sum_congr rfl fun i hi => h i (Finset.mem_range.mp hi)
private theorem sumRange_prefix (n k : ℕ) (f : ℕ → ℕ) (hk : k ≤ n)
    (h : ∀ i, k ≤ i → i < n → f i = 0) :
    sumRange n f = sumRange k f := by
  conv_lhs => rw [← Nat.add_sub_of_le hk, sumRange_add]
  rw [sumRange_zero (n - k) (fun i => f (i + k)) (fun i hi => h _ (by omega) (by omega)),
    add_zero]
private theorem sumRange_suffix (n k : ℕ) (f : ℕ → ℕ) (hk : k ≤ n)
    (h : ∀ i < k, f i = 0) :
    sumRange n f = sumRange (n - k) (fun i => f (i + k)) := by
  conv_lhs => rw [← Nat.add_sub_of_le hk, sumRange_add]
  rw [sumRange_zero k f h, zero_add]
theorem remainingCap_eq (n start cap : ℕ) (f : ℕ → ℕ) :
    remainingCap f n start cap = cap - sumRange n (fun i => f (i + start)) := by
  induction n generalizing start cap with
  | zero => simp [remainingCap, sumRange]
  | succ n ih =>
    by_cases h : cap = 0
    · simp [remainingCap, h]
    rw [remainingCap, ite_eq_right h, ih, sumRange_succ_left]
    simp only [zero_add, Nat.add_assoc, Nat.add_comm 1 start]
    omega
private theorem sumToCap_eq (n start cap : ℕ) (f : ℕ → ℕ) :
    sumToCap f n start cap = min cap (sumRange n (fun i => f (i + start))) := by
  unfold sumToCap
  rw [remainingCap_eq]
  omega
private theorem activeNatCount_eq (d : ℕ) (lo hi : ℤ) (hhi : 0 ≤ hi) :
    bandCount d lo hi 10 = activeNatCount d lo.toNat hi.toNat := by
  unfold bandCount activeNatCount
  rw [sumRange_prefix (min d 10 + 1) (min (min d 10) (hi.toNat / 3) + 1)]
  · apply sumRange_congr
    intro f hf
    have hf' : 3 * f ≤ hi.toNat := by omega
    have hdiv : ((hi - 3 * (f : ℤ)) / 2).toNat = (hi.toNat - 3 * f) / 2 := by omega
    rw [hdiv]
    apply sumRange_congr
    intro c hc
    unfold intervalSize
    omega
  · omega
  · intro f hlo hf
    apply sumRange_zero
    intro c _
    unfold intervalSize
    omega
private theorem natLine_eq (d : ℕ) (lo order : ℤ) (ho : 0 ≤ order) (b c : ℕ)
    (hbc : b + c ≤ d) :
    lineBound d lo order b c = natLine d lo.toNat order.toNat b c := by
  let lower := max 0 ((lo - (b : ℤ) - 2 * (min c 24 : ℕ) + 2) / 3)
  let lowerNat := (lo.toNat - (b + 2 * min c 24) + 2) / 3
  have hlow : lower = (lowerNat : ℤ) := by dsimp [lower, lowerNat]; omega
  unfold lineBound natLine
  dsimp only
  change min (intervalSize lower _) (intervalSize (max lower _) _) =
    min (min d 10 + 1 - lowerNat) (d - b - c + 1 - max lowerNat _)
  rw [hlow]
  congr 1 <;> unfold intervalSize <;> omega
private theorem natPairs_eq (d : ℕ) (lo : ℤ) (b : ℕ) :
    pairBound d lo b = natPairs d lo.toNat b := by
  unfold pairBound natPairs
  apply sumRange_congr
  intro f hf
  unfold intervalSize
  omega
private theorem natLine_zero (d lo order b c : ℕ) (hbc : b + c ≤ d)
    (h : c < 2 * (d - b) + 1 - order) : natLine d lo order b c = 0 := by
  unfold natLine
  dsimp only
  omega
private theorem innerSlice_eq (d lo order b : ℕ) (hb : b ≤ d) :
    (let startC := 2 * (d - b) + 1 - order
     sumToCap (natLine d lo order b) (d - b + 1 - startC) startC (natPairs d lo b)) =
     min (natPairs d lo b) (sumRange (d - b + 1) (natLine d lo order b)) := by
  let startC := 2 * (d - b) + 1 - order
  change sumToCap (natLine d lo order b) (d - b + 1 - startC) startC _ = _
  rw [sumToCap_eq]
  congr 1
  by_cases hc : startC ≤ d - b + 1
  · symm
    apply sumRange_suffix _ _ _ hc
    intro c h
    exact natLine_zero d lo order b c (by omega) h
  · rw [show d - b + 1 - startC = 0 by omega]
    symm
    apply sumRange_zero
    intro c h
    exact natLine_zero d lo order b c (by omega) (by omega)
private theorem fastPascal_eq (s r : ℕ) (h : s + r < 138) :
    fastPascal s r = pascalBound s (offset r) := by
  let d := residualDegree s
  let lo := -(offset r)
  let order := orderCutoff s (offset r)
  let hi := activeIndex (offset r)
  have hl : lo.toNat = 48 - r := by dsimp [lo, offset]; omega
  have ho : order.toNat = 138 - (s + r) := by dsimp [order, orderCutoff, offset]; omega
  have hpos : 0 < order := by dsimp [order, orderCutoff, offset]; omega
  have hh : hi.toNat = min 48 (137 - r) := by dsimp [hi, activeIndex, offset]; omega
  have hhi : 0 ≤ hi := by dsimp [hi, activeIndex, offset]; omega
  let startB := d + 1 - order.toNat
  change (sumToCap (fun b =>
      let startC := 2 * (d - b) + 1 - (138 - (s + r))
      sumToCap (natLine d (48 - r) (138 - (s + r)) b) (d - b + 1 - startC)
        startC (natPairs d (48 - r) b))
      (d + 1 - (d + 1 - (138 - (s + r)))) (d + 1 - (138 - (s + r)))
      (activeNatCount d (48 - r) (min 48 (137 - r)))) =
    min (bandCount d lo hi 10) (sumRange (d + 1) fun b =>
      min (pairBound d lo b) (sumRange (d - b + 1) (lineBound d lo order b)))
  rw [← hl, ← ho, ← hh, ← activeNatCount_eq d lo hi hhi, sumToCap_eq]
  congr 1
  change sumRange (d + 1 - startB) _ = _
  symm
  rw [sumRange_suffix (d + 1) startB _ (Nat.sub_le _ _)]
  · apply sumRange_congr
    intro i hi
    simp only [natPairs_eq]
    have hb : i + startB ≤ d := by omega
    rw [innerSlice_eq d lo.toNat order.toNat _ hb]
    congr 1
    apply sumRange_congr
    intro c hc
    exact natLine_eq d lo order hpos.le _ c (by omega)
  · intro b hb
    have hz : sumRange (d - b + 1) (lineBound d lo order b) = 0 := by
      apply sumRange_zero
      intro c hc
      have hbc : b + c ≤ d := by dsimp [startB] at hb; omega
      rw [natLine_eq d lo order hpos.le b c hbc]
      apply natLine_zero _ _ _ _ _ hbc
      dsimp [startB] at hb
      omega
    simp [hz]
private theorem fastBlock_eq (s r : ℕ) : fastBlock s r = blockBudget s (offset r) := by
  have h : offset r < 90 - (s : ℤ) ↔ s + r < 138 := by unfold offset; omega
  by_cases hr : s + r < 138
  · cases hc : selectedFactors s (offset r) <;>
      simp [fastBlock, blockBudget, hr, h.mpr hr, fastPascal_eq s r hr, hc]
  · have hg : ¬ offset r < 90 - (s : ℤ) := fun hg => hr (h.mp hg)
    simp [fastBlock, blockBudget, hr, hg]
theorem fastGrade_eq (s : ℕ) : fastGrade s = gradeBudget s := by
  unfold fastGrade gradeBudget
  exact sumRange_congr _ (fun i _ => fastBlock_eq s i)
end K1_13_1_1
end
