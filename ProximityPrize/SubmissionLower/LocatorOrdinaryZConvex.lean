import ProximityPrize.SubmissionLower.LocatorPhase6800Oracle

/-! Packed from ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex. -/
section PackedLocator_LocatorOrdinaryZConvex

namespace ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex

open RCN095 LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1 LocatorHybridCostC2

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def rawCost (r v z : ℕ) : ℕ := ordinaryCostOf ⟨z, v, r⟩

theorem hybridApplies_raw (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    HybridAppliesC2 (⟨z, v, r⟩ : FlagDegree) := by
  change 3 ≤ r ∧ r + 2 ≤ v + r
  omega

theorem padS_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) :
    padS (⟨z, v, r⟩ : FlagDegree) = r := by
  simp only [padS]
  omega

theorem padY_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    padY (⟨z, v, r⟩ : FlagDegree) = r + v := by
  simp only [padY, middle, padS_raw_hybrid r v z hr]
  omega

theorem padT_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    padT (⟨z, v, r⟩ : FlagDegree) = r + v + z := by
  simp only [padT, total, padY_raw_hybrid r v z hr hv]
  omega

theorem sharp_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    sharpTail (⟨z, v, r⟩ : FlagDegree) =
      ⟨2 * z * 131072, 1 + (2 * v - 1) * 131072,
        (2 * r - 1) * 131072⟩ := by
  unfold sharpTail
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem reduced_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    reducedTail (⟨z, v, r⟩ : FlagDegree) =
      ⟨2 * z * 131072, 1 + 2 * v * 131072, 2 * (r - 1) * 131072⟩ := by
  unfold reducedTail paddedTail
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem rational_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    rationalFlag (⟨z, v, r⟩ : FlagDegree) =
      ⟨131074 * z, 131074 * (v - 1) + 2, 131074 * (r - 2) + 3⟩ := by
  unfold rationalFlag
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem moving_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    movingFiber (⟨z, v, r⟩ : FlagDegree) = ⟨z, v, r + 1⟩ := by
  unfold movingFiber
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem hybridCostC2_raw_affine (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    2 * hybridCostC2 (⟨z + 1, v, r⟩ : FlagDegree) =
      hybridCostC2 ⟨z, v, r⟩ + hybridCostC2 ⟨z + 2, v, r⟩ := by
  have hr2 : 2 ≤ r := by omega
  unfold hybridCostC2 hybridCoordinateC1 movingCut
  rw [reduced_raw_hybrid r v z hr2 hv,
    reduced_raw_hybrid r v (z + 1) hr2 hv,
    reduced_raw_hybrid r v (z + 2) hr2 hv,
    rational_raw_hybrid r v z hr2 hv,
    rational_raw_hybrid r v (z + 1) hr2 hv,
    rational_raw_hybrid r v (z + 2) hr2 hv,
    moving_raw_hybrid r v z hr2 hv,
    moving_raw_hybrid r v (z + 1) hr2 hv,
    moving_raw_hybrid r v (z + 2) hr2 hv]
  unfold flagMixed
  simp only [add_zOnly, add_yz, add_all]
  ring

theorem rawCost_affine_of_hybrid (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    2 * rawCost r v (z + 1) = rawCost r v z + rawCost r v (z + 2) := by
  rw [rawCost, rawCost, rawCost]
  simp only [ordinaryCostOf, if_pos (hybridApplies_raw r v z hr hv),
    if_pos (hybridApplies_raw r v (z + 1) hr hv),
    if_pos (hybridApplies_raw r v (z + 2) hr hv)]
  exact hybridCostC2_raw_affine r v z hr hv

theorem paddedTail_raw_of_r_two_v_pos (r v z d : ℕ)
    (hr : 2 ≤ r) (hv : 1 ≤ v) :
    paddedTail (⟨z, v, r⟩ : FlagDegree) d =
      ⟨2 * z * d, 1 + 2 * v * d, 2 * (r - 1) * d⟩ := by
  unfold paddedTail
  have hs : padS (⟨z, v, r⟩ : FlagDegree) = r := by
    simp only [padS]
    omega
  have hy : padY (⟨z, v, r⟩ : FlagDegree) = r + v := by
    simp only [padY, middle, hs]
    omega
  have ht : padT (⟨z, v, r⟩ : FlagDegree) = r + v + z := by
    simp only [padT, total, hy]
    omega
  rw [hs, hy, ht]
  congr <;> omega

theorem paddedCost_raw_affine_of_r_two_v_pos (r v z : ℕ)
    (hr : 2 ≤ r) (hv : 1 ≤ v) :
    2 * paddedCost 131072 131073 (⟨z + 1, v, r⟩ : FlagDegree) =
      paddedCost 131072 131073 ⟨z, v, r⟩ +
        paddedCost 131072 131073 ⟨z + 2, v, r⟩ := by
  unfold paddedCost
  rw [paddedTail_raw_of_r_two_v_pos r v z 131072 hr hv,
    paddedTail_raw_of_r_two_v_pos r v z 131073 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 1) 131072 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 1) 131073 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 2) 131072 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 2) 131073 hr hv]
  unfold flagMixed
  ring

theorem rawCost_affine_of_r_two_v_one (r z : ℕ) (hr : 2 ≤ r) :
    2 * rawCost r 1 (z + 1) = rawCost r 1 z + rawCost r 1 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 1, r⟩ : FlagDegree) := by
    intro h
    have hbad := h.2
    change r + 2 ≤ 1 + r at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_two_v_pos r 1 z hr (by decide)

theorem rawCost_affine_of_r_two_v_two (v z : ℕ) (hv : 2 ≤ v) :
    2 * rawCost 2 v (z + 1) = rawCost 2 v z + rawCost 2 v (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, v, 2⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 2 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_two_v_pos 2 v z (le_refl 2) (by omega)

theorem paddedTail_raw_of_r_one_v_two (v z d : ℕ) (hv : 2 ≤ v) :
    paddedTail (⟨z, v, 1⟩ : FlagDegree) d =
      ⟨2 * z * d, 1 + 2 * (v - 1) * d, 2 * d⟩ := by
  have hs : padS (⟨z, v, 1⟩ : FlagDegree) = 2 := by rfl
  have hy : padY (⟨z, v, 1⟩ : FlagDegree) = v + 1 := by
    unfold padY
    rw [hs]
    change max (v + 1) 3 = v + 1
    omega
  have ht : padT (⟨z, v, 1⟩ : FlagDegree) = v + 1 + z := by
    unfold padT
    rw [hy]
    change max (z + v + 1) (v + 1) = v + 1 + z
    omega
  change (⟨2 * (padT (⟨z, v, 1⟩ : FlagDegree) -
      padY ⟨z, v, 1⟩) * d,
    1 + 2 * (padY (⟨z, v, 1⟩ : FlagDegree) -
      padS ⟨z, v, 1⟩) * d,
    2 * (padS (⟨z, v, 1⟩ : FlagDegree) - 1) * d⟩ : FlagDegree) = _
  rw [ht, hy, hs]
  have hz : v + 1 + z - (v + 1) = z := by omega
  have hvsub : v + 1 - 2 = v - 1 := by omega
  rw [hz, hvsub]

theorem paddedCost_raw_affine_of_r_one_v_two (v z : ℕ) (hv : 2 ≤ v) :
    2 * paddedCost 131072 131073 (⟨z + 1, v, 1⟩ : FlagDegree) =
      paddedCost 131072 131073 ⟨z, v, 1⟩ +
        paddedCost 131072 131073 ⟨z + 2, v, 1⟩ := by
  unfold paddedCost
  rw [paddedTail_raw_of_r_one_v_two v z 131072 hv,
    paddedTail_raw_of_r_one_v_two v z 131073 hv,
    paddedTail_raw_of_r_one_v_two v (z + 1) 131072 hv,
    paddedTail_raw_of_r_one_v_two v (z + 1) 131073 hv,
    paddedTail_raw_of_r_one_v_two v (z + 2) 131072 hv,
    paddedTail_raw_of_r_one_v_two v (z + 2) 131073 hv]
  unfold flagMixed
  ring

theorem rawCost_affine_of_r_one_v_two (v z : ℕ) (hv : 2 ≤ v) :
    2 * rawCost 1 v (z + 1) = rawCost 1 v z + rawCost 1 v (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, v, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_one_v_two v z hv

theorem paddedTail_raw_of_r_two_v_zero (r z d : ℕ)
    (hr : 2 ≤ r) (hz : 1 ≤ z) :
    paddedTail (⟨z, 0, r⟩ : FlagDegree) d =
      ⟨2 * (z - 1) * d, 1 + 2 * d, 2 * (r - 1) * d⟩ := by
  have hs : padS (⟨z, 0, r⟩ : FlagDegree) = r := by
    unfold padS
    change max r 2 = r
    omega
  have hy : padY (⟨z, 0, r⟩ : FlagDegree) = r + 1 := by
    unfold padY middle
    rw [hs]
    change max (0 + r) (r + 1) = r + 1
    omega
  have ht : padT (⟨z, 0, r⟩ : FlagDegree) = r + z := by
    unfold padT total
    rw [hy]
    change max (z + 0 + r) (r + 1) = r + z
    omega
  change (⟨2 * (padT (⟨z, 0, r⟩ : FlagDegree) -
      padY ⟨z, 0, r⟩) * d,
    1 + 2 * (padY (⟨z, 0, r⟩ : FlagDegree) -
      padS ⟨z, 0, r⟩) * d,
    2 * (padS (⟨z, 0, r⟩ : FlagDegree) - 1) * d⟩ : FlagDegree) = _
  rw [ht, hy, hs]
  have hzsub : r + z - (r + 1) = z - 1 := by omega
  rw [hzsub]
  congr <;> omega

theorem paddedCost_raw_affine_of_r_two_v_zero (r z : ℕ)
    (hr : 2 ≤ r) (hz : 1 ≤ z) :
    2 * paddedCost 131072 131073 (⟨z + 1, 0, r⟩ : FlagDegree) =
      paddedCost 131072 131073 ⟨z, 0, r⟩ +
        paddedCost 131072 131073 ⟨z + 2, 0, r⟩ := by
  unfold paddedCost
  rw [paddedTail_raw_of_r_two_v_zero r z 131072 hr hz,
    paddedTail_raw_of_r_two_v_zero r z 131073 hr hz,
    paddedTail_raw_of_r_two_v_zero r (z + 1) 131072 hr (by omega),
    paddedTail_raw_of_r_two_v_zero r (z + 1) 131073 hr (by omega),
    paddedTail_raw_of_r_two_v_zero r (z + 2) 131072 hr (by omega),
    paddedTail_raw_of_r_two_v_zero r (z + 2) 131073 hr (by omega)]
  have h1 : z + 1 - 1 = z := by omega
  have h2 : z + 2 - 1 = z + 1 := by omega
  rw [h1, h2]
  have hzsplit : z = (z - 1) + 1 := by omega
  rw [hzsplit]
  simp only [Nat.add_sub_cancel]
  unfold flagMixed
  ring

theorem rawCost_affine_of_r_two_v_zero (r z : ℕ)
    (hr : 2 ≤ r) (hz : 1 ≤ z) :
    2 * rawCost r 0 (z + 1) = rawCost r 0 z + rawCost r 0 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 0, r⟩ : FlagDegree) := by
    intro h
    have hbad := h.2
    change r + 2 ≤ 0 + r at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_two_v_zero r z hr hz

theorem paddedTail_raw_r_two_v_zero_boundary (r d : ℕ) (hr : 2 ≤ r) :
    paddedTail (⟨0, 0, r⟩ : FlagDegree) d =
        ⟨0, 1 + 2 * d, 2 * (r - 1) * d⟩ ∧
      paddedTail (⟨1, 0, r⟩ : FlagDegree) d =
        ⟨0, 1 + 2 * d, 2 * (r - 1) * d⟩ := by
  constructor
  · unfold paddedTail padT padY padS middle total
    simp only [Nat.zero_add]
    have hm : max r 2 = r := by omega
    rw [hm]
    have hm' : max r (r + 1) = r + 1 := by omega
    rw [hm']
    norm_num
  · simpa using paddedTail_raw_of_r_two_v_zero r 1 d hr (by decide)

theorem rawCost_convex_r_two_v_zero_boundary (r : ℕ) (hr : 2 ≤ r) :
    2 * rawCost r 0 1 ≤ rawCost r 0 0 + rawCost r 0 2 := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 0, r⟩ : FlagDegree) := by
    intro h
    have hbad := h.2
    change r + 2 ≤ 0 + r at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn 0), if_neg (hn 1),
    if_neg (hn 2)]
  unfold paddedCost
  rw [(paddedTail_raw_r_two_v_zero_boundary r 131072 hr).1,
    (paddedTail_raw_r_two_v_zero_boundary r 131073 hr).1,
    (paddedTail_raw_r_two_v_zero_boundary r 131072 hr).2,
    (paddedTail_raw_r_two_v_zero_boundary r 131073 hr).2,
    paddedTail_raw_of_r_two_v_zero r 2 131072 hr (by decide),
    paddedTail_raw_of_r_two_v_zero r 2 131073 hr (by decide)]
  unfold flagMixed
  ring_nf
  omega

theorem paddedTail_raw_r_one_v_one (z d : ℕ) (hz : 1 ≤ z) :
    paddedTail (⟨z, 1, 1⟩ : FlagDegree) d =
      ⟨2 * (z - 1) * d, 1 + 2 * d, 2 * d⟩ := by
  unfold paddedTail padT padY padS middle total
  norm_num
  have hm : max (z + 2) 3 = z + 2 := by omega
  rw [hm]
  congr <;> omega

theorem rawCost_convex_r_one_v_one (z : ℕ) :
    2 * rawCost 1 1 (z + 1) ≤ rawCost 1 1 z + rawCost 1 1 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 1, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  by_cases hz : z = 0
  · subst z
    norm_num [paddedCost, paddedTail, padT, padY, padS, middle, total, flagMixed]
  · have hzpos : 1 ≤ z := by omega
    have hEq : 2 * paddedCost 131072 131073
          (⟨z + 1, 1, 1⟩ : FlagDegree) =
        paddedCost 131072 131073 ⟨z, 1, 1⟩ +
          paddedCost 131072 131073 ⟨z + 2, 1, 1⟩ := by
      unfold paddedCost
      rw [paddedTail_raw_r_one_v_one z 131072 hzpos,
        paddedTail_raw_r_one_v_one z 131073 hzpos,
        paddedTail_raw_r_one_v_one (z + 1) 131072 (by omega),
        paddedTail_raw_r_one_v_one (z + 1) 131073 (by omega),
        paddedTail_raw_r_one_v_one (z + 2) 131072 (by omega),
        paddedTail_raw_r_one_v_one (z + 2) 131073 (by omega)]
      have h1 : z + 1 - 1 = z := by omega
      have h2 : z + 2 - 1 = z + 1 := by omega
      rw [h1, h2]
      have hzsplit : z = (z - 1) + 1 := by omega
      rw [hzsplit]
      simp only [Nat.add_sub_cancel]
      unfold flagMixed
      ring
    exact hEq.le

theorem paddedTail_raw_r_one_v_zero (z d : ℕ) (hz : 2 ≤ z) :
    paddedTail (⟨z, 0, 1⟩ : FlagDegree) d =
      ⟨2 * (z - 2) * d, 1 + 2 * d, 2 * d⟩ := by
  unfold paddedTail padT padY padS middle total
  norm_num
  have hm : max (z + 1) 3 = z + 1 := by omega
  rw [hm]
  congr <;> omega

theorem rawCost_convex_r_one_v_zero (z : ℕ) :
    2 * rawCost 1 0 (z + 1) ≤ rawCost 1 0 z + rawCost 1 0 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 0, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  by_cases hz0 : z = 0
  · subst z
    norm_num [paddedCost, paddedTail, padT, padY, padS, middle, total, flagMixed]
  · by_cases hz1 : z = 1
    · subst z
      norm_num [paddedCost, paddedTail, padT, padY, padS, middle, total, flagMixed]
    · have hz : 2 ≤ z := by omega
      unfold paddedCost
      rw [paddedTail_raw_r_one_v_zero z 131072 hz,
        paddedTail_raw_r_one_v_zero z 131073 hz,
        paddedTail_raw_r_one_v_zero (z + 1) 131072 (by omega),
        paddedTail_raw_r_one_v_zero (z + 1) 131073 (by omega),
        paddedTail_raw_r_one_v_zero (z + 2) 131072 (by omega),
        paddedTail_raw_r_one_v_zero (z + 2) 131073 (by omega)]
      have h1 : z + 1 - 2 = z - 1 := by omega
      have h2 : z + 2 - 2 = z := by omega
      rw [h1, h2]
      have hzsplit : z = (z - 2) + 2 := by omega
      rw [hzsplit]
      norm_num
      unfold flagMixed
      ring_nf
      exact le_rfl

theorem rawCost_discreteConvex (r v z : ℕ) (hr : 1 ≤ r) :
    2 * rawCost r v (z + 1) ≤ rawCost r v z + rawCost r v (z + 2) := by
  by_cases hr1 : r = 1
  · subst r
    by_cases hv0 : v = 0
    · subst v
      exact rawCost_convex_r_one_v_zero z
    · by_cases hv1 : v = 1
      · subst v
        exact rawCost_convex_r_one_v_one z
      · exact (rawCost_affine_of_r_one_v_two v z (by omega)).le
  · have hr2 : 2 ≤ r := by omega
    by_cases hv0 : v = 0
    · subst v
      by_cases hz : z = 0
      · subst z
        exact rawCost_convex_r_two_v_zero_boundary r hr2
      · exact (rawCost_affine_of_r_two_v_zero r z hr2 (by omega)).le
    · by_cases hv1 : v = 1
      · subst v
        exact (rawCost_affine_of_r_two_v_one r z hr2).le
      · by_cases hr3 : r = 2
        · subst hr3
          exact (rawCost_affine_of_r_two_v_two v z (by omega)).le
        · exact (rawCost_affine_of_hybrid r v z (by omega) (by omega)).le

theorem rawBelow_of_z_le (r v z₁ z₂ : ℕ) (hz : z₁ ≤ z₂) :
    Below (⟨z₁, v, r⟩ : FlagDegree) ⟨z₂, v, r⟩ := by
  change r ≤ r ∧ v + r ≤ v + r ∧ z₁ + v + r ≤ z₂ + v + r
  omega

theorem rawCost_mono_z (r v : ℕ) : Monotone (rawCost r v) := by
  intro z₁ z₂ hz
  have hb := rawBelow_of_z_le r v z₁ z₂ hz
  by_cases ha : HybridAppliesC2 (⟨z₁, v, r⟩ : FlagDegree)
  · have ha' : HybridAppliesC2 (⟨z₂, v, r⟩ : FlagDegree) := by
      rcases ha with ⟨hr, hv⟩
      exact ⟨hr, hv⟩
    simp only [rawCost, ordinaryCostOf, if_pos ha, if_pos ha']
    exact hybridCostC2_mono hb
  · have ha' : ¬ HybridAppliesC2 (⟨z₂, v, r⟩ : FlagDegree) := by
      intro h
      apply ha
      rcases h with ⟨hr, hv⟩
      exact ⟨hr, hv⟩
    simp only [rawCost, ordinaryCostOf, if_neg ha, if_neg ha']
    exact paddedCost_mono 131072 131073 hb

def forwardDiff (f : ℕ → ℕ) (n : ℕ) : ℕ := f (n + 1) - f n

theorem forwardDiff_mono_of_discreteConvex
    (f : ℕ → ℕ) (hmono : Monotone f)
    (hconvex : ∀ n, 2 * f (n + 1) ≤ f n + f (n + 2)) (n : ℕ) :
    forwardDiff f n ≤ forwardDiff f (n + 1) := by
  have h₀ := hmono (Nat.le_add_right n 1)
  have h₁ := hmono (Nat.le_add_right (n + 1) 1)
  have hc := hconvex n
  unfold forwardDiff
  rw [show n + 1 + 1 = n + 2 by omega]
  omega

theorem move_one_right
    (f g : ℕ → ℕ) (hf : Monotone f) (hg : Monotone g)
    (a b : ℕ) (hcross : forwardDiff f a ≤ forwardDiff g b) :
    f (a + 1) + g b ≤ f a + g (b + 1) := by
  have hfa := hf (Nat.le_add_right a 1)
  have hgb := hg (Nat.le_add_right b 1)
  unfold forwardDiff at hcross
  omega

theorem transfer_all_right
    (f g : ℕ → ℕ) (hf : Monotone f) (hg : Monotone g)
    (hdf : ∀ n, forwardDiff f n ≤ forwardDiff f (n + 1))
    (hdg : ∀ n, forwardDiff g n ≤ forwardDiff g (n + 1)) :
    ∀ a b, forwardDiff f a ≤ forwardDiff g b →
      f (a + 1) + g b ≤ f 0 + g (a + 1 + b) := by
  intro a
  induction a with
  | zero =>
      intro b hcross
      simpa only [Nat.zero_add, Nat.add_comm] using
        move_one_right f g hf hg 0 b hcross
  | succ a ih =>
      intro b hcross
      have hcross' : forwardDiff f a ≤ forwardDiff g (b + 1) :=
        (hdf a).trans (hcross.trans (hdg b))
      calc
        f (a + 1 + 1) + g b ≤ f (a + 1) + g (b + 1) :=
          move_one_right f g hf hg (a + 1) b hcross
        _ ≤ f 0 + g (a + 1 + (b + 1)) := ih (b + 1) hcross'
        _ = f 0 + g (a + 1 + 1 + b) := by
          rw [show a + 1 + (b + 1) = a + 1 + 1 + b by omega]

theorem two_discreteConvex_endpoint
    (f g : ℕ → ℕ) (hf : Monotone f) (hg : Monotone g)
    (hcf : ∀ n, 2 * f (n + 1) ≤ f n + f (n + 2))
    (hcg : ∀ n, 2 * g (n + 1) ≤ g n + g (n + 2))
    (a b : ℕ) :
    f a + g b ≤ max (f (a + b) + g 0) (f 0 + g (a + b)) := by
  have hdf (n : ℕ) : forwardDiff f n ≤ forwardDiff f (n + 1) :=
    forwardDiff_mono_of_discreteConvex f hf hcf n
  have hdg (n : ℕ) : forwardDiff g n ≤ forwardDiff g (n + 1) :=
    forwardDiff_mono_of_discreteConvex g hg hcg n
  rcases a with _ | a
  · simpa only [Nat.zero_add] using
      (le_max_right (f b + g 0) (f 0 + g b))
  rcases b with _ | b
  · simpa only [Nat.add_zero] using
      (le_max_left (f (a + 1) + g 0) (f 0 + g (a + 1)))
  by_cases hcross : forwardDiff f a ≤ forwardDiff g (b + 1)
  · have h := transfer_all_right f g hf hg hdf hdg a (b + 1) hcross
    have h' : f (a + 1) + g (b + 1) ≤
        f 0 + g (a + 1 + (b + 1)) := h
    apply h'.trans
    apply le_max_of_le_right
    rfl
  · have hcross' : forwardDiff g b ≤ forwardDiff f (a + 1) :=
      (hdg b).trans ((Nat.lt_of_not_ge hcross).le.trans (hdf a))
    have h := transfer_all_right g f hg hf hdg hdf b (a + 1) hcross'
    have h' : f (a + 1) + g (b + 1) ≤
        f (b + 1 + (a + 1)) + g 0 := by
      simpa only [Nat.add_comm] using h
    have h'' : f (a + 1) + g (b + 1) ≤
        f ((a + 1) + (b + 1)) + g 0 := by
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
    apply h''.trans
    apply le_max_of_le_left
    rfl

theorem rawCost_affine_r_one_v_one (z : ℕ) (hz : 1 ≤ z) :
    2 * rawCost 1 1 (z + 1) = rawCost 1 1 z + rawCost 1 1 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 1, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  unfold paddedCost
  rw [paddedTail_raw_r_one_v_one z 131072 hz,
    paddedTail_raw_r_one_v_one z 131073 hz,
    paddedTail_raw_r_one_v_one (z + 1) 131072 (by omega),
    paddedTail_raw_r_one_v_one (z + 1) 131073 (by omega),
    paddedTail_raw_r_one_v_one (z + 2) 131072 (by omega),
    paddedTail_raw_r_one_v_one (z + 2) 131073 (by omega)]
  have h1 : z + 1 - 1 = z := by omega
  have h2 : z + 2 - 1 = z + 1 := by omega
  rw [h1, h2]
  have hzsplit : z = (z - 1) + 1 := by omega
  rw [hzsplit]
  simp only [Nat.add_sub_cancel]
  unfold flagMixed
  ring

theorem rawCost_affine_r_one_v_zero (z : ℕ) (hz : 2 ≤ z) :
    2 * rawCost 1 0 (z + 1) = rawCost 1 0 z + rawCost 1 0 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 0, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  unfold paddedCost
  rw [paddedTail_raw_r_one_v_zero z 131072 hz,
    paddedTail_raw_r_one_v_zero z 131073 hz,
    paddedTail_raw_r_one_v_zero (z + 1) 131072 (by omega),
    paddedTail_raw_r_one_v_zero (z + 1) 131073 (by omega),
    paddedTail_raw_r_one_v_zero (z + 2) 131072 (by omega),
    paddedTail_raw_r_one_v_zero (z + 2) 131073 (by omega)]
  have h1 : z + 1 - 2 = z - 1 := by omega
  have h2 : z + 2 - 2 = z := by omega
  rw [h1, h2]
  have hzsplit : z = (z - 2) + 2 := by omega
  rw [hzsplit]
  norm_num
  unfold flagMixed
  ring

theorem rawCost_affine_step_from_two (r v z : ℕ)
    (hr : 1 ≤ r) (hz : 2 ≤ z) :
    2 * rawCost r v (z + 1) = rawCost r v z + rawCost r v (z + 2) := by
  by_cases hr1 : r = 1
  · subst r
    by_cases hv0 : v = 0
    · subst v
      exact rawCost_affine_r_one_v_zero z hz
    · by_cases hv1 : v = 1
      · subst v
        exact rawCost_affine_r_one_v_one z (by omega)
      · exact rawCost_affine_of_r_one_v_two v z (by omega)
  · have hr2 : 2 ≤ r := by omega
    by_cases hv0 : v = 0
    · subst v
      exact rawCost_affine_of_r_two_v_zero r z hr2 (by omega)
    · by_cases hv1 : v = 1
      · subst v
        exact rawCost_affine_of_r_two_v_one r z hr2
      · by_cases hr3 : r = 2
        · subst hr3
          exact rawCost_affine_of_r_two_v_two v z (by omega)
        · exact rawCost_affine_of_hybrid r v z (by omega) (by omega)

theorem forwardDiff_eq_next_of_affine
    (f : ℕ → ℕ) (hmono : Monotone f)
    (n : ℕ) (hstep : 2 * f (n + 1) = f n + f (n + 2)) :
    forwardDiff f n = forwardDiff f (n + 1) := by
  have h₀ := hmono (Nat.le_add_right n 1)
  have h₁ := hmono (Nat.le_add_right (n + 1) 1)
  unfold forwardDiff
  rw [show n + 1 + 1 = n + 2 by omega]
  omega

theorem affine_formula_from_three
    (f : ℕ → ℕ) (hmono : Monotone f)
    (hstep : ∀ n, 2 ≤ n → 2 * f (n + 1) = f n + f (n + 2))
    (z : ℕ) (hz : 3 ≤ z) :
    f z = f 3 + (f 4 - f 3) * (z - 3) := by
  have hdiffStep (n : ℕ) (hn : 2 ≤ n) :
      forwardDiff f n = forwardDiff f (n + 1) :=
    forwardDiff_eq_next_of_affine f hmono n (hstep n hn)
  have hdiff : ∀ n, 3 ≤ n → forwardDiff f n = forwardDiff f 3 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact (hdiffStep n (by omega)).symm.trans ih
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hmn := hmono (Nat.le_add_right n 1)
      have hd := hdiff n hn
      have hd' : f (n + 1) - f n = f 4 - f 3 := by
        simpa only [forwardDiff, show 3 + 1 = 4 by decide] using hd
      calc
        f (n + 1) = f n + (f (n + 1) - f n) :=
          (Nat.add_sub_of_le hmn).symm
        _ = f n + (f 4 - f 3) := by rw [hd']
        _ = (f 3 + (f 4 - f 3) * (n - 3)) + (f 4 - f 3) := by
          rw [ih]
        _ = f 3 + (f 4 - f 3) * (n + 1 - 3) := by
          have hnsub : n + 1 - 3 = (n - 3) + 1 := by omega
          rw [hnsub]
          ring

theorem rawCost_affine_from_three (r v z : ℕ)
    (hr : 1 ≤ r) (hz : 3 ≤ z) :
    rawCost r v z = rawCost r v 3 +
      (rawCost r v 4 - rawCost r v 3) * (z - 3) := by
  exact affine_formula_from_three (rawCost r v) (rawCost_mono_z r v)
    (fun n hn => rawCost_affine_step_from_two r v n hr hn) z hz

end ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex
end PackedLocator_LocatorOrdinaryZConvex

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier15 : True := by trivial
end ProximityPrize.SubmissionLower

