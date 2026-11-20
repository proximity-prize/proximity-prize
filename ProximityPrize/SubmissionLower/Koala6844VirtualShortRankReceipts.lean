import ProximityPrize.SubmissionLower.Koala6844VirtualShortSeedlessArithmetic
import ProximityPrize.SubmissionLower.Koala6844VirtualShortContactRank
import ProximityPrize.SubmissionLower.Koala6844VirtualShortWeightedCount


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open Koala6844Receipts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

private theorem sumRange_eq_finset_range (n : Nat) (f : Nat → Nat) :
    sumRange n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, List.range_succ, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at ih ⊢
    rw [ih, Finset.sum_range_succ]

private theorem sumRange_eq_fin_sum (n : Nat) (f : Nat → Nat) :
    sumRange n f = ∑ i : Fin n, f i.val := by
  rw [sumRange_eq_finset_range, Fin.sum_univ_eq_sum_range]

private theorem rectangle_card_mono {a a' b b' h h' : ℕ}
    (ha : a' ≤ a) (hb : b' ≤ b) (hh : h' ≤ h) :
    Fintype.card (SeedlessRectangle a' b' h') ≤ Fintype.card (SeedlessRectangle a b h) := by
  apply Fintype.card_le_of_injective
    (fun (ij : SeedlessRectangle a' b' h') =>
      (⟨⟨Fin.castLE ha ij.val.1, Fin.castLE hb ij.val.2⟩,ij.property.trans hh⟩ : SeedlessRectangle a b h))
  intro i j hij
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg (fun t : SeedlessRectangle a b h => t.val.1.val) hij
  · exact congrArg (fun t : SeedlessRectangle a b h => t.val.2.val) hij

theorem seedlessRankBudget_eq_auxiliaryRankSlice (src : SourceShape) (j : ℕ)
    (hsB : 2*src.s ≤ src.B) (hj : j ≤ src.U) :
    seedlessRankBudget (src.m-j) src.B src.s (src.U-j) = auxiliaryRankSlice src j := by
  let m := src.m-j
  let U := src.U-j
  let B := src.B
  let s := src.s
  let cell (t h : ℕ) := if h ≤ U then
    Fintype.card (SeedlessRectangle (t+1) (B-2*h+1) (U-h)) else 0
  let stratum (t h : ℕ) := Fintype.card (SeedlessKernelBlock m B s U t h)
  have hm (t : Fin m) (h : Fin (s+1)) : stratum t h ≤ cell t h := by
    dsimp only [stratum]
    rw [card_seedlessKernelBlock m B s U t h (by omega) (by omega)]
    dsimp only [cell]
    split_ifs with h₁ h₂
    · exact rectangle_card_mono (by omega) (by omega) (by omega)
    · omega
    · exact Nat.zero_le _
    · rfl
  have hrank : seedlessRankBudget m B s U = ∑ t : Fin m, ∑ h : Fin (s+1), (cell t h-stratum t h) := by
    unfold seedlessRankBudget
    rw [card_seedlessIndex m B s U hsB]
    change ((∑ t : Fin m, ∑ h : Fin (s+1), cell t h) -
      ∑ t : Fin m, ∑ h : Fin (s+1), stratum t h) = _
    rw [← Finset.sum_tsub_distrib Finset.univ (fun t _ => Finset.sum_le_sum (fun h _ => hm t h))]
    apply Finset.sum_congr rfl
    intro t _
    exact (Finset.sum_tsub_distrib Finset.univ (fun h _ => hm t h)).symm
  change seedlessRankBudget m B s U = auxiliaryRankSlice src j
  rw [hrank, auxiliaryRankSlice, ite_eq_left hj, sumRange_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fin.sum_univ_eq_sum_range (fun h : ℕ => cell t h-stratum t h), sumRange_eq_finset_range]
  change _ = ∑ h ∈ Finset.range (min s U+1), _
  calc
    _ = ∑ h ∈ Finset.range (min s U+1), (cell t h-stratum t h) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (min_le_left s U)))
      intro h hh he
      have hh' : U < h := by
        have hlt := Finset.mem_range.mp hh
        have hn : ¬h < min s U+1 := fun hn => he (Finset.mem_range.mpr hn)
        omega
      simp [cell, show ¬h ≤ U by omega]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      have hh' := Finset.mem_range.mp hh
      have hhU : h ≤ U := by omega
      have hhs : h ≤ s := by omega
      dsimp only [cell,stratum]
      rw [ite_eq_left hhU,
        card_seedlessKernelBlock m B s U t.val h (by omega) hhs]
      simp only [card_seedlessRectangle]
      change _ = (let k := localKernelOrder m t s h
         let all := seedlessRectangle (t+1) (B+1-2*h) (U-h)
         if k ≤ t ∧ m-t+2*h ≤ B then
           if k ≤ U-h then all-seedlessRectangle (t-k+1) (B+1-2*h-k) (U-h-k) else all
         else all)
      dsimp only
      have hq : localKernelOrder m t s h = SecondJetRelaxedRank.q m s t h := rfl
      rw [hq]
      generalize hkeq : SecondJetRelaxedRank.q m s t h = k
      have hb : 2*h ≤ B := by omega
      have hb₁ : B-2*h+1 = B+1-2*h := by omega
      rw [hb₁]
      by_cases hx : k ≤ t ∧ m-t+2*h ≤ B
      · by_cases hy : k ≤ U-h
        · have hc : k ≤ m-t := by rw [←hkeq]; unfold SecondJetRelaxedRank.q; omega
          have hh' : h+k ≤ U := by omega
          have hz : B-2*h-k+1 = B+1-2*h-k := by omega
          have hp : k ≤ t ∧ m-t+2*h ≤ B ∧ h+k ≤ U := ⟨hx.1,hx.2,hh'⟩
          simp only [ite_eq_left hx, ite_eq_left hy, ite_eq_left hp,hz]
        · have hh' : ¬ h+k ≤ U := by omega
          have hn : ¬ (k ≤ t ∧ m-t+2*h ≤ B ∧ h+k ≤ U) := fun h => hh' h.2.2
          simp only [ite_eq_left hx, ite_eq_right hy, ite_eq_right hn, Nat.sub_zero]
      · have hn : ¬ (k ≤ t ∧ m-t+2*h ≤ B ∧ h+k ≤ U) :=
          fun h => hx ⟨h.1,h.2.1⟩
        simp only [ite_eq_right hx, ite_eq_right hn, Nat.sub_zero]

theorem ordinaryRankBound_eq (src : SourceShape) (caps : ℕ → ℕ) (hsB : 2*src.s ≤ src.B)
    (hsU : src.s ≤ src.U) (hUL : src.U ≤ src.L) (hcaps : ∀ h ≤ src.s, src.U ≤ caps h) :
    SecondJetRelaxedGlobalMap.rankBound src.m src.L src.B src.s src.U caps = ordinaryRankBound src := by
  let m := src.m
  let L := src.L
  let B := src.B
  let s := src.s
  let U := src.U
  let cell (t h : ℕ) := weightedRectangle (t+1) (B-2*h+1) (L+1-h) (U-h)
  let stratum (t h : ℕ) := if SecondJetRelaxedRank.q m s t h ≤ t ∧ m-t+2*h ≤ B ∧
      h+SecondJetRelaxedRank.q m s t h ≤ U then
    weightedRectangle (t-SecondJetRelaxedRank.q m s t h+1)
      (B-2*h-SecondJetRelaxedRank.q m s t h+1) (L+1-h-SecondJetRelaxedRank.q m s t h)
      (U-h-SecondJetRelaxedRank.q m s t h) else 0
  have hcell (t : Fin m) (h : Fin (s+1)) : cell t h =
      ∑ i : Fin (t.val+1), ∑ j : Fin (B-2*h.val+1),
        if h.val+i.val+j.val ≤ U then L+1-h.val-i.val-j.val else 0 := by
    dsimp only [cell]
    have hh : h.val ≤ U := (Nat.le_of_lt_succ h.isLt).trans hsU
    rw [weightedRectangle_eq_sum _ _ _ _ (by omega)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have he : i.val+j.val ≤ U-h.val ↔ h.val+i.val+j.val ≤ U := by omega
    simp only [he]
  have hstratum (t : Fin m) (h : Fin (s+1)) :
      Fintype.card (SecondJetRelaxedRank.Block m L B s U caps t.val h.val) = stratum t h := by
    dsimp only [stratum]
    set k := SecondJetRelaxedRank.q m s t.val h.val
    by_cases hk : k ≤ t.val ∧ m-t.val+2*h.val ≤ B
    · rw [SecondJetRelaxedKernelCounts.card_block_of_le m L B s U caps t.val h.val
        (Nat.le_of_lt t.isLt) (Nat.le_of_lt_succ h.isLt) hk.1 hk.2 hcaps]
      by_cases hb : h.val+k ≤ U
      · rw [ite_eq_left ⟨hk.1,hk.2,hb⟩, weightedRectangle_eq_sum _ _ _ _ (by omega)]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change (if h.val+k+i.val+j.val ≤ U then L+1-h.val-k-i.val-j.val else 0) =
          if i.val+j.val ≤ U-h.val-k then L+1-h.val-k-i.val-j.val else 0
        have he : h.val+k+i.val+j.val ≤ U ↔ i.val+j.val ≤ U-h.val-k := by omega
        simp only [he]
      · have hn : ¬ (k ≤ t.val ∧ m-t.val+2*h.val ≤ B ∧ h.val+k ≤ U) := fun hh => hb hh.2.2
        rw [ite_eq_right hn]
        apply Finset.sum_eq_zero
        intro i _
        apply Finset.sum_eq_zero
        intro j _
        exact ite_eq_right (by omega)
    · have hn : ¬ (k ≤ t.val ∧ m-t.val+2*h.val ≤ B ∧ h.val+k ≤ U) := fun hh => hk ⟨hh.1,hh.2.1⟩
      rw [SecondJetRelaxedKernelCounts.card_block_of_not_le _ _ _ _ _ _ _ _ hk,ite_eq_right hn]
  have hle (t : Fin m) (h : Fin (s+1)) : stratum t h ≤ cell t h := by
    dsimp only [stratum,cell]
    split_ifs with hk
    · exact weightedRectangle_mono (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact Nat.zero_le _
  have hsum : SecondJetRelaxedGlobalMap.rankBound m L B s U caps =
      ∑ t : Fin m, ∑ h : Fin (s+1), (cell t h-stratum t h) := by
    unfold SecondJetRelaxedGlobalMap.rankBound
    have hs₁ : Fintype.card (SecondJetRelaxedSpace.Index m L B s U caps) =
        ∑ t : Fin m, ∑ h : Fin (s+1), cell t h := by
      rw [SecondJetRelaxedSourceCounts.card_source _ _ _ _ _ _ hsB hcaps]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro h _
      exact (hcell t h).symm
    have hs₂ : (∑ t : Fin m, ∑ h : Fin (s+1),
        Fintype.card (SecondJetRelaxedRank.Block m L B s U caps t.val h.val)) =
        ∑ t : Fin m, ∑ h : Fin (s+1), stratum t h := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro h _
      exact hstratum t h
    rw [hs₁,hs₂]
    rw [← Finset.sum_tsub_distrib Finset.univ (fun t _ => Finset.sum_le_sum (fun h _ => hle t h))]
    apply Finset.sum_congr rfl
    intro t _
    exact (Finset.sum_tsub_distrib Finset.univ (fun h _ => hle t h)).symm
  rw [hsum,ordinaryRankBound,min_eq_left hsU,sumRange_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [sumRange_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro h _
  change cell t h - stratum t h = ordinaryRankRow src t.val h.val
  dsimp only [cell,stratum,ordinaryRankRow]
  have hq : localKernelOrder src.m t.val src.s h.val = SecondJetRelaxedRank.q m s t.val h.val := rfl
  rw [hq]
  generalize hkeq : SecondJetRelaxedRank.q m s t.val h.val = k
  change _ = if k ≤ t.val ∧ m-t.val+2*h.val ≤ B then
    if k ≤ U-h.val then _ else _ else _
  have hh : h.val ≤ s := Nat.le_of_lt_succ h.isLt
  have hB : 2*h.val ≤ B := by omega
  have hU : h.val ≤ U := hh.trans hsU
  have heq : B-2*h.val+1 = B+1-2*h.val := by omega
  rw [heq]
  by_cases hk : k ≤ t.val ∧ m-t.val+2*h.val ≤ B
  · by_cases ht : k ≤ U-h.val
    · have hp : k ≤ t.val ∧ m-t.val+2*h.val ≤ B ∧ h.val+k ≤ U := ⟨hk.1,hk.2,by omega⟩
      have hb : k ≤ m-t.val := by rw [← hkeq]; unfold SecondJetRelaxedRank.q; omega
      have he : B-2*h.val-k+1 = B+1-2*h.val-k := by omega
      have ht' : t.val-k+1 = t.val+1-k := by omega
      simp only [ite_eq_left hk,ite_eq_left ht,ite_eq_left hp,he,ht']
      rfl
    · have hn : ¬ (k ≤ t.val ∧ m-t.val+2*h.val ≤ B ∧ h.val+k ≤ U) := fun p => ht (by have := p.2.2; omega)
      simp only [ite_eq_left hk,ite_eq_right ht,ite_eq_right hn,Nat.sub_zero]
      rfl
  · have hn : ¬ (k ≤ t.val ∧ m-t.val+2*h.val ≤ B ∧ h.val+k ≤ U) := fun p => hk ⟨p.1,p.2.1⟩
    simp only [ite_eq_right hk,ite_eq_right hn,Nat.sub_zero]
    rfl

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
