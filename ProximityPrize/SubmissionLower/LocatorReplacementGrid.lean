import ProximityPrize.SubmissionLower.LocatorFactorReplacement

namespace ProximityPrize.SubmissionLower.LocatorReplacementGrid
open RCN095 LocatorFactorAggregate LocatorFactorReplacement

set_option maxRecDepth 2048
set_option maxHeartbeats 300000

abbrev Cell := Fin 8 × Fin 60 × Fin 57

def r (c : Cell) : ℕ := c.1.val + 7
def ylo (c : Cell) : ℕ := r c + c.2.1.val
def yhi (c : Cell) : ℕ := min 66 (ylo c)
def tlo (c : Cell) : ℕ := 32 * c.2.2.val
def thi (c : Cell) : ℕ := min 1796 (tlo c + 31)

def Valid (c : Cell) : Prop := ylo c ≤ 66 ∧ ylo c ≤ thi c

instance (c : Cell) : Decidable (Valid c) := inferInstanceAs
  (Decidable (ylo c ≤ 66 ∧ ylo c ≤ thi c))

def ordinaryCap (c : Cell) : FlagDegree := cap (thi c) (min (yhi c) (thi c)) (r c)
def ordinaryCost (c : Cell) : ℕ := paddedCost 131072 131073 (ordinaryCap c)

/-- These are residual budgets, not the flag of a putative polynomial of
degrees (tlo,ylo,r); indeed tlo can be smaller than ylo. -/
def gridRestCap (c : Cell) : FlagDegree :=
  cap (1796 - tlo c) (min (66 - ylo c) (1796 - tlo c))
    (min (14 - r c) (min (66 - ylo c) (1796 - tlo c)))

def gridRestCost (c : Cell) : ℕ :=
  if (gridRestCap c).all = 0 then 0 else paddedCost 131072 131073 (gridRestCap c)

structure InCell (p : FlagDegree) (c : Cell) : Prop where
  all_eq : p.all = r c
  ylo_le : ylo c ≤ middle p
  middle_le_yhi : middle p ≤ yhi c
  tlo_le : tlo c ≤ total p
  total_le_thi : total p ≤ thi c

def cellOf (p : FlagDegree) (hslo : 7 ≤ p.all) (hshi : p.all ≤ 14)
    (hy : middle p ≤ 66) (ht : total p ≤ 1796) : Cell :=
  (⟨p.all - 7, by omega⟩,
    ⟨middle p - p.all, by omega⟩,
    ⟨total p / 32, by omega⟩)

theorem cellOf_bounds (p : FlagDegree) (hslo : 7 ≤ p.all) (hshi : p.all ≤ 14)
    (hy : middle p ≤ 66) (ht : total p ≤ 1796) :
    InCell p (cellOf p hslo hshi hy ht) := by
  have hmy := all_le_middle p
  constructor
  · change p.all = p.all - 7 + 7
    omega
  · change (p.all - 7 + 7) + (middle p - p.all) ≤ middle p
    omega
  · change middle p ≤ min 66 ((p.all - 7 + 7) + (middle p - p.all))
    exact le_min hy (by omega)
  · change 32 * (total p / 32) ≤ total p
    omega
  · change total p ≤ min 1796 (32 * (total p / 32) + 31)
    exact le_min ht (by omega)

theorem ylo_le_thi_of_inCell (p : FlagDegree) (c : Cell) (h : InCell p c) :
    ylo c ≤ thi c :=
  (h.ylo_le.trans (middle_le_total p)).trans h.total_le_thi

theorem valid_of_inCell (p : FlagDegree) (c : Cell) (h : InCell p c) : Valid c := by
  have hyhi : yhi c ≤ 66 := Nat.min_le_left _ _
  exact ⟨(h.ylo_le.trans h.middle_le_yhi).trans hyhi, ylo_le_thi_of_inCell p c h⟩

theorem cellOf_valid (p : FlagDegree) (hslo : 7 ≤ p.all) (hshi : p.all ≤ 14)
    (hy : middle p ≤ 66) (ht : total p ≤ 1796) :
    Valid (cellOf p hslo hshi hy ht) :=
  valid_of_inCell p _ (cellOf_bounds p hslo hshi hy ht)

theorem ordinaryCap_cumulative (c : Cell) (h : Valid c) :
    (ordinaryCap c).all = r c ∧
      middle (ordinaryCap c) = min (yhi c) (thi c) ∧ total (ordinaryCap c) = thi c := by
  have hry : r c ≤ ylo c := by dsimp [ylo]; omega
  have hryhi : r c ≤ yhi c :=
    le_min (hry.trans h.1) (by omega)
  exact cap_cumulative _ _ _ (le_min hryhi (hry.trans h.2)) (Nat.min_le_right _ _)

theorem below_ordinaryCap (p : FlagDegree) (c : Cell) (h : InCell p c) :
    Below p (ordinaryCap c) := by
  have hc := ordinaryCap_cumulative c (valid_of_inCell p c h)
  unfold Below
  rw [hc.1, hc.2.1, hc.2.2]
  exact ⟨h.all_eq.le, le_min h.middle_le_yhi
    ((middle_le_total p).trans h.total_le_thi), h.total_le_thi⟩

theorem paddedCost_le_ordinaryCost (p : FlagDegree) (c : Cell) (h : InCell p c) :
    paddedCost 131072 131073 p ≤ ordinaryCost c :=
  paddedCost_mono 131072 131073 (below_ordinaryCap p c h)

theorem count_le_ordinaryCost (p : FlagDegree) (c : Cell) (count : ℕ)
    (h : InCell p c) (hstage : count ≤ paddedCost 131072 131073 p) :
    count ≤ ordinaryCost c := hstage.trans (paddedCost_le_ordinaryCost p c h)

theorem gridRestCap_cumulative (c : Cell) :
    (gridRestCap c).all = min (14 - r c) (min (66 - ylo c) (1796 - tlo c)) ∧
      middle (gridRestCap c) = min (66 - ylo c) (1796 - tlo c) ∧
      total (gridRestCap c) = 1796 - tlo c :=
  cap_cumulative _ _ _ (Nat.min_le_right _ _) (Nat.min_le_right _ _)

theorem remainingCap_below_gridRestCap (p : FlagDegree) (c : Cell) (h : InCell p c) :
    Below (remainingCap 1796 66 14 p) (gridRestCap c) := by
  have heq := h.all_eq
  have hylo := h.ylo_le
  have htlo := h.tlo_le
  have hr : 14 - p.all ≤ 14 - r c := by omega
  have hy : 66 - middle p ≤ 66 - ylo c := by omega
  have ht : 1796 - total p ≤ 1796 - tlo c := by omega
  have hp := remainingCap_cumulative 1796 66 14 p
  have hg := gridRestCap_cumulative c
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hg.1, hg.2.1, hg.2.2]
  exact ⟨min_le_min hr (min_le_min hy ht), min_le_min hy ht, ht⟩

theorem remainingCost_le_gridRestCost (p : FlagDegree) (c : Cell) (h : InCell p c) :
    remainingCost 1796 66 14 131072 131073 p ≤ gridRestCost c := by
  have hb := remainingCap_below_gridRestCap p c h
  by_cases hg : (gridRestCap c).all = 0
  · have hp : (remainingCap 1796 66 14 p).all = 0 := by
      have hs := hb.1
      omega
    rw [remainingCost, gridRestCost, if_pos hp, if_pos hg]
  · by_cases hp : (remainingCap 1796 66 14 p).all = 0
    · rw [remainingCost, if_pos hp]
      exact Nat.zero_le _
    · rw [remainingCost, gridRestCost, if_neg hp, if_neg hg]
      exact paddedCost_mono 131072 131073 hb

/-- The numeric certificate pays for the chosen whole-equation cost plus
the grid remainder. The actual factor may also use its ordinary cost. -/
theorem cellCost_le_of_grid_bound {bound : ℕ} (p : FlagDegree) (c : Cell) (q : ℕ)
    (h : InCell p c) (hq : q + gridRestCost c ≤ bound) :
    cellCost 1796 66 14 131072 131073 p q ≤ bound := by
  calc
    _ = min (paddedCost 131072 131073 p) q +
        remainingCost 1796 66 14 131072 131073 p := rfl
    _ ≤ q + gridRestCost c := Nat.add_le_add (Nat.min_le_right _ _)
      (remainingCost_le_gridRestCost p c h)
    _ ≤ bound := hq

theorem cellCost_le_of_q_le_grid {bound : ℕ} (p : FlagDegree) (c : Cell) (q gridQ : ℕ)
    (h : InCell p c) (hq : q ≤ gridQ) (hgrid : gridQ + gridRestCost c ≤ bound) :
    cellCost 1796 66 14 131072 131073 p q ≤ bound :=
  cellCost_le_of_grid_bound p c q h ((Nat.add_le_add_right hq _).trans hgrid)

theorem cellCost_le_of_choice {bound : ℕ} (chosen : Cell → ℕ)
    (hgrid : ∀ c, Valid c → chosen c + gridRestCost c ≤ bound)
    (p : FlagDegree) (hslo : 7 ≤ p.all) (hshi : p.all ≤ 14)
    (hy : middle p ≤ 66) (ht : total p ≤ 1796) :
    cellCost 1796 66 14 131072 131073 p (chosen (cellOf p hslo hshi hy ht)) ≤ bound :=
  cellCost_le_of_grid_bound p _ _ (cellOf_bounds p hslo hshi hy ht)
    (hgrid _ (cellOf_valid p hslo hshi hy ht))

end ProximityPrize.SubmissionLower.LocatorReplacementGrid
