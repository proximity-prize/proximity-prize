import ProximityPrize.SubmissionLower.LocatorC2Arithmetic

namespace ProximityPrize.SubmissionLower.LocatorOrdinaryZConvexC2

open RCN095 LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1
  LocatorHybridCostC2 LocatorC2Arithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

def rawCost (r v z : ℕ) : ℕ := ordinaryCostOfC2 ⟨z, v, r⟩

theorem hybridApplies_raw (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    HybridAppliesC2 (⟨z, v, r⟩ : FlagDegree) := by
  change 3 ≤ r ∧ r + 2 ≤ v + r
  omega

theorem reduced_raw_hybrid (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    reducedTail (⟨z, v, r⟩ : FlagDegree) =
      ⟨2 * z * 131072, 1 + 2 * v * 131072,
        2 * (r - 1) * 131072⟩ := by
  exact LocatorOrdinaryZConvex.paddedTail_raw_of_r_two_v_pos
    r v z 131072 (by omega) (by omega)

theorem hybridCost_raw_affine (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    2 * hybridCostC2 (⟨z + 1, v, r⟩ : FlagDegree) =
      hybridCostC2 ⟨z, v, r⟩ + hybridCostC2 ⟨z + 2, v, r⟩ := by
  unfold hybridCostC2 hybridCoordinateC1 movingCut
  rw [reduced_raw_hybrid r v z hr hv,
    reduced_raw_hybrid r v (z + 1) hr hv,
    reduced_raw_hybrid r v (z + 2) hr hv,
    LocatorOrdinaryZConvex.rational_raw_hybrid r v z (by omega) hv,
    LocatorOrdinaryZConvex.rational_raw_hybrid r v (z + 1) (by omega) hv,
    LocatorOrdinaryZConvex.rational_raw_hybrid r v (z + 2) (by omega) hv,
    LocatorOrdinaryZConvex.moving_raw_hybrid r v z (by omega) hv,
    LocatorOrdinaryZConvex.moving_raw_hybrid r v (z + 1) (by omega) hv,
    LocatorOrdinaryZConvex.moving_raw_hybrid r v (z + 2) (by omega) hv]
  unfold flagMixed
  simp only [add_zOnly, add_yz, add_all]
  ring

theorem rawCost_affine_of_hybrid (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    2 * rawCost r v (z + 1) = rawCost r v z + rawCost r v (z + 2) := by
  simp only [rawCost,
    ordinaryCostOfC2_eq_hybrid _ (hybridApplies_raw r v z hr hv),
    ordinaryCostOfC2_eq_hybrid _ (hybridApplies_raw r v (z + 1) hr hv),
    ordinaryCostOfC2_eq_hybrid _ (hybridApplies_raw r v (z + 2) hr hv)]
  exact hybridCost_raw_affine r v z hr hv

theorem not_hybrid_of_r_lt_three (r v z : ℕ) (hr : r < 3) :
    ¬HybridAppliesC2 (⟨z, v, r⟩ : FlagDegree) := by
  intro h
  exact (not_le_of_gt hr) h.1

theorem not_hybrid_of_v_lt_two (r v z : ℕ) (hv : v < 2) :
    ¬HybridAppliesC2 (⟨z, v, r⟩ : FlagDegree) := by
  intro h
  have := h.2
  change r + 2 ≤ v + r at this
  omega

theorem rawCost_eq_padded_of_not_hybrid (r v z : ℕ)
    (h : ¬HybridAppliesC2 (⟨z, v, r⟩ : FlagDegree)) :
    rawCost r v z = paddedCost 131072 131073 ⟨z, v, r⟩ := by
  simp only [rawCost, ordinaryCostOfC2, if_neg h]

theorem originalRawCost_eq_padded_of_r_lt_two (r v z : ℕ) (hr : r < 2) :
    LocatorOrdinaryZConvex.rawCost r v z =
      paddedCost 131072 131073 ⟨z, v, r⟩ := by
  unfold LocatorOrdinaryZConvex.rawCost ordinaryCostOf
  rw [if_neg]
  intro h
  exact (not_le_of_gt hr) h.1

theorem originalRawCost_eq_padded_of_v_lt_two (r v z : ℕ) (hv : v < 2) :
    LocatorOrdinaryZConvex.rawCost r v z =
      paddedCost 131072 131073 ⟨z, v, r⟩ := by
  unfold LocatorOrdinaryZConvex.rawCost ordinaryCostOf
  rw [if_neg]
  intro h
  have := h.2
  change r + 2 ≤ v + r at this
  omega

theorem rawCost_discreteConvex (r v z : ℕ) (hr : 1 ≤ r) :
    2 * rawCost r v (z + 1) ≤ rawCost r v z + rawCost r v (z + 2) := by
  by_cases hr3 : 3 ≤ r
  · by_cases hv2 : 2 ≤ v
    · exact (rawCost_affine_of_hybrid r v z hr3 hv2).le
    · have hv : v = 0 ∨ v = 1 := by omega
      rcases hv with rfl | rfl
      · simp only [rawCost, ordinaryCostOfC2,
          if_neg (not_hybrid_of_v_lt_two r 0 z (by decide)),
          if_neg (not_hybrid_of_v_lt_two r 0 (z + 1) (by decide)),
          if_neg (not_hybrid_of_v_lt_two r 0 (z + 2) (by decide))]
        by_cases hz0 : z = 0
        · subst z
          simpa only [originalRawCost_eq_padded_of_v_lt_two r 0 0 (by decide),
            originalRawCost_eq_padded_of_v_lt_two r 0 1 (by decide),
            originalRawCost_eq_padded_of_v_lt_two r 0 2 (by decide)] using
              LocatorOrdinaryZConvex.rawCost_convex_r_two_v_zero_boundary r
                (by omega)
        · exact (LocatorOrdinaryZConvex.paddedCost_raw_affine_of_r_two_v_zero
            r z (by omega) (by omega)).le
      · simp only [rawCost, ordinaryCostOfC2,
          if_neg (not_hybrid_of_v_lt_two r 1 z (by decide)),
          if_neg (not_hybrid_of_v_lt_two r 1 (z + 1) (by decide)),
          if_neg (not_hybrid_of_v_lt_two r 1 (z + 2) (by decide))]
        exact (LocatorOrdinaryZConvex.paddedCost_raw_affine_of_r_two_v_pos
          r 1 z (by omega) (by decide)).le
  · have hrCases : r = 1 ∨ r = 2 := by omega
    rcases hrCases with rfl | rfl
    · have h0 (x : ℕ) : ¬HybridAppliesC2 (⟨x, v, 1⟩ : FlagDegree) :=
        not_hybrid_of_r_lt_three 1 v x (by decide)
      simp only [rawCost, ordinaryCostOfC2, if_neg (h0 z), if_neg (h0 (z + 1)),
        if_neg (h0 (z + 2))]
      simpa only [originalRawCost_eq_padded_of_r_lt_two 1 v z (by decide),
        originalRawCost_eq_padded_of_r_lt_two 1 v (z + 1) (by decide),
        originalRawCost_eq_padded_of_r_lt_two 1 v (z + 2) (by decide)] using
          LocatorOrdinaryZConvex.rawCost_discreteConvex 1 v z (by decide)
    · have h0 (x : ℕ) : ¬HybridAppliesC2 (⟨x, v, 2⟩ : FlagDegree) :=
        not_hybrid_of_r_lt_three 2 v x (by decide)
      simp only [rawCost, ordinaryCostOfC2, if_neg (h0 z), if_neg (h0 (z + 1)),
        if_neg (h0 (z + 2))]
      by_cases hv0 : v = 0
      · subst v
        simpa only [originalRawCost_eq_padded_of_v_lt_two 2 0 z (by decide),
          originalRawCost_eq_padded_of_v_lt_two 2 0 (z + 1) (by decide),
          originalRawCost_eq_padded_of_v_lt_two 2 0 (z + 2) (by decide)] using
            LocatorOrdinaryZConvex.rawCost_discreteConvex 2 0 z (by decide)
      · exact (LocatorOrdinaryZConvex.paddedCost_raw_affine_of_r_two_v_pos
          2 v z (by decide) (by omega)).le

theorem rawBelow_of_z_le (r v z₁ z₂ : ℕ) (hz : z₁ ≤ z₂) :
    Below (⟨z₁, v, r⟩ : FlagDegree) ⟨z₂, v, r⟩ :=
  LocatorOrdinaryZConvex.rawBelow_of_z_le r v z₁ z₂ hz

theorem rawCost_mono_z (r v : ℕ) : Monotone (rawCost r v) := by
  intro z₁ z₂ hz
  have hb := rawBelow_of_z_le r v z₁ z₂ hz
  by_cases ha : HybridAppliesC2 (⟨z₁, v, r⟩ : FlagDegree)
  · have ha' : HybridAppliesC2 (⟨z₂, v, r⟩ : FlagDegree) := by
      rcases ha with ⟨hr, hv⟩
      exact ⟨hr, hv⟩
    simp only [rawCost, ordinaryCostOfC2_eq_hybrid _ ha,
      ordinaryCostOfC2_eq_hybrid _ ha']
    exact hybridCostC2_mono hb
  · have ha' : ¬HybridAppliesC2 (⟨z₂, v, r⟩ : FlagDegree) := by
      intro h
      apply ha
      rcases h with ⟨hr, hv⟩
      exact ⟨hr, hv⟩
    simp only [rawCost, ordinaryCostOfC2, if_neg ha, if_neg ha']
    exact paddedCost_mono 131072 131073 hb

theorem rawCost_affine_step_from_two (r v z : ℕ)
    (hr : 1 ≤ r) (hz : 2 ≤ z) :
    2 * rawCost r v (z + 1) = rawCost r v z + rawCost r v (z + 2) := by
  by_cases hr3 : 3 ≤ r
  · by_cases hv2 : 2 ≤ v
    · exact rawCost_affine_of_hybrid r v z hr3 hv2
    · have hv : v = 0 ∨ v = 1 := by omega
      rcases hv with rfl | rfl
      · simp only [rawCost, ordinaryCostOfC2,
          if_neg (not_hybrid_of_v_lt_two r 0 z (by decide)),
          if_neg (not_hybrid_of_v_lt_two r 0 (z + 1) (by decide)),
          if_neg (not_hybrid_of_v_lt_two r 0 (z + 2) (by decide))]
        exact LocatorOrdinaryZConvex.paddedCost_raw_affine_of_r_two_v_zero
          r z (by omega) (by omega)
      · simp only [rawCost, ordinaryCostOfC2,
          if_neg (not_hybrid_of_v_lt_two r 1 z (by decide)),
          if_neg (not_hybrid_of_v_lt_two r 1 (z + 1) (by decide)),
          if_neg (not_hybrid_of_v_lt_two r 1 (z + 2) (by decide))]
        exact LocatorOrdinaryZConvex.paddedCost_raw_affine_of_r_two_v_pos
          r 1 z (by omega) (by decide)
  · have hrCases : r = 1 ∨ r = 2 := by omega
    rcases hrCases with rfl | rfl
    · simp only [rawCost, ordinaryCostOfC2,
        if_neg (not_hybrid_of_r_lt_three 1 v z (by decide)),
        if_neg (not_hybrid_of_r_lt_three 1 v (z + 1) (by decide)),
        if_neg (not_hybrid_of_r_lt_three 1 v (z + 2) (by decide))]
      by_cases hv0 : v = 0
      · subst v
        simpa only [originalRawCost_eq_padded_of_r_lt_two 1 0 z (by decide),
          originalRawCost_eq_padded_of_r_lt_two 1 0 (z + 1) (by decide),
          originalRawCost_eq_padded_of_r_lt_two 1 0 (z + 2) (by decide)] using
            LocatorOrdinaryZConvex.rawCost_affine_r_one_v_zero z hz
      · by_cases hv1 : v = 1
        · subst v
          simpa only [originalRawCost_eq_padded_of_r_lt_two 1 1 z (by decide),
            originalRawCost_eq_padded_of_r_lt_two 1 1 (z + 1) (by decide),
            originalRawCost_eq_padded_of_r_lt_two 1 1 (z + 2) (by decide)] using
              LocatorOrdinaryZConvex.rawCost_affine_r_one_v_one z (by omega)
        · exact LocatorOrdinaryZConvex.paddedCost_raw_affine_of_r_one_v_two
            v z (by omega)
    · simp only [rawCost, ordinaryCostOfC2,
        if_neg (not_hybrid_of_r_lt_three 2 v z (by decide)),
        if_neg (not_hybrid_of_r_lt_three 2 v (z + 1) (by decide)),
        if_neg (not_hybrid_of_r_lt_three 2 v (z + 2) (by decide))]
      by_cases hv0 : v = 0
      · subst v
        exact LocatorOrdinaryZConvex.paddedCost_raw_affine_of_r_two_v_zero
          2 z (by decide) (by omega)
      · exact LocatorOrdinaryZConvex.paddedCost_raw_affine_of_r_two_v_pos
          2 v z (by decide) (by omega)

theorem rawCost_affine_from_three (r v z : ℕ)
    (hr : 1 ≤ r) (hz : 3 ≤ z) :
    rawCost r v z = rawCost r v 3 +
      (rawCost r v 4 - rawCost r v 3) * (z - 3) := by
  exact LocatorOrdinaryZConvex.affine_formula_from_three
    (rawCost r v) (rawCost_mono_z r v)
    (fun n hn => rawCost_affine_step_from_two r v n hr hn) z hz

end ProximityPrize.SubmissionLower.LocatorOrdinaryZConvexC2
