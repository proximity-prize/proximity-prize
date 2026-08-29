import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research

/-! .










 -/

namespace ProximityPrize.SubmissionLower.ContactFlagPoleInequality6543Research

open scoped Classical BigOperators WithZero
open ContactLocalPoleBound ContactSparsePoleSupportResearch
open ContactFlagBezout6543Research

noncomputable section

/-- . -/
theorem exponent_weight_le_flag_bound
    (p : FlagDegree) (d : Fin 3 →₀ ℕ) (q : Fin 3 → ℤ)
    (hd : InFlag p d) (hq : ∀ i, 0 ≤ q i) :
    (∑ i, (d i : ℤ) * q i) ≤
      (p.zOnly : ℤ) * q 2 +
        (p.yz : ℤ) * max (q 0) (q 2) +
        (p.all : ℤ) * max (q 1) (max (q 0) (q 2)) := by
  let m₁ : ℤ := max (q 0) (q 2)
  let m₂ : ℤ := max (q 1) m₁
  have hq0m₁ : q 0 ≤ m₁ := le_max_left _ _
  have hq2m₁ : q 2 ≤ m₁ := le_max_right _ _
  have hq1m₂ : q 1 ≤ m₂ := le_max_left _ _
  have hm₁m₂ : m₁ ≤ m₂ := le_max_right _ _
  have hreplace0 : (d 0 : ℤ) * q 0 ≤ (d 0 : ℤ) * m₁ :=
    mul_le_mul_of_nonneg_left hq0m₁ (by positivity)
  have hreplace1 : (d 1 : ℤ) * q 1 ≤ (d 1 : ℤ) * m₂ :=
    mul_le_mul_of_nonneg_left hq1m₂ (by positivity)
  have htotal : ((d 0 + d 1 + d 2 : ℕ) : ℤ) ≤
      ((p.zOnly + p.yz + p.all : ℕ) : ℤ) := by
    exact_mod_cast hd.2.2
  have hys : ((d 0 + d 1 : ℕ) : ℤ) ≤
      ((p.yz + p.all : ℕ) : ℤ) := by
    exact_mod_cast hd.2.1
  have hs : (d 1 : ℤ) ≤ (p.all : ℤ) := by
    exact_mod_cast hd.1
  have hdiff₁ : 0 ≤ m₁ - q 2 := sub_nonneg.mpr hq2m₁
  have hdiff₂ : 0 ≤ m₂ - m₁ := sub_nonneg.mpr hm₁m₂
  have hcap :
      ((d 0 + d 1 + d 2 : ℕ) : ℤ) * q 2 +
          ((d 0 + d 1 : ℕ) : ℤ) * (m₁ - q 2) +
          (d 1 : ℤ) * (m₂ - m₁) ≤
        ((p.zOnly + p.yz + p.all : ℕ) : ℤ) * q 2 +
          ((p.yz + p.all : ℕ) : ℤ) * (m₁ - q 2) +
          (p.all : ℤ) * (m₂ - m₁) := by
    exact add_le_add
      (add_le_add (mul_le_mul_of_nonneg_right htotal (hq 2))
        (mul_le_mul_of_nonneg_right hys hdiff₁))
      (mul_le_mul_of_nonneg_right hs hdiff₂)
  calc
    (∑ i, (d i : ℤ) * q i) =
        (d 0 : ℤ) * q 0 + (d 1 : ℤ) * q 1 + (d 2 : ℤ) * q 2 := by
      simp [Fin.sum_univ_three]
    _ ≤ (d 0 : ℤ) * m₁ + (d 1 : ℤ) * m₂ + (d 2 : ℤ) * q 2 :=
      add_le_add (add_le_add hreplace0 hreplace1) le_rfl
    _ = ((d 0 + d 1 + d 2 : ℕ) : ℤ) * q 2 +
          ((d 0 + d 1 : ℕ) : ℤ) * (m₁ - q 2) +
          (d 1 : ℤ) * (m₂ - m₁) := by
      push_cast
      ring
    _ ≤ ((p.zOnly + p.yz + p.all : ℕ) : ℤ) * q 2 +
          ((p.yz + p.all : ℕ) : ℤ) * (m₁ - q 2) +
          (p.all : ℤ) * (m₂ - m₁) := hcap
    _ = (p.zOnly : ℤ) * q 2 + (p.yz : ℤ) * m₁ +
          (p.all : ℤ) * m₂ := by
      push_cast
      ring
    _ = _ := rfl

variable {L : Type*} [Field L]

/-- .
 -/
theorem exponentSetPoleWeight_flagSupport_le
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x : Fin 3 → L)
    (p : FlagDegree) :
    exponentSetPoleWeight v x (flagSupport p) ≤
      (p.zOnly : ℤ) * poleOrder v (x 2) +
        (p.yz : ℤ) * max (poleOrder v (x 0)) (poleOrder v (x 2)) +
        (p.all : ℤ) * max (poleOrder v (x 1))
          (max (poleOrder v (x 0)) (poleOrder v (x 2))) := by
  classical
  unfold exponentSetPoleWeight
  apply Finset.max'_le
  intro z hz
  obtain rfl | hz := Finset.mem_insert.mp hz
  · have h0 : ∀ i : Fin 3, 0 ≤ poleOrder v (x i) := fun i ↦ by
      unfold poleOrder
      exact le_max_left _ _
    exact add_nonneg
      (add_nonneg (mul_nonneg (by positivity) (h0 2))
        (mul_nonneg (by positivity)
          ((h0 0).trans (le_max_left _ _))))
      (mul_nonneg (by positivity)
        ((h0 1).trans (le_max_left _ _)))
  · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
    exact exponent_weight_le_flag_bound p d (fun i ↦ poleOrder v (x i))
      ((mem_flagSupport_iff p d).mp hd)
      (fun i ↦ by unfold poleOrder; exact le_max_left _ _)

theorem exponentPoleWeight_single
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x : Fin 3 → L)
    (i : Fin 3) :
    exponentPoleWeight v x (Finsupp.single i 1) = poleOrder v (x i) := by
  classical
  fin_cases i <;> simp [exponentPoleWeight, Fin.sum_univ_three]

private theorem poleOrder_le_support_of_mem
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x : Fin 3 → L)
    (p : FlagDegree) (i : Fin 3)
    (hi : Finsupp.single i 1 ∈ flagSupport p) :
    poleOrder v (x i) ≤ exponentSetPoleWeight v x (flagSupport p) := by
  rw [← exponentPoleWeight_single v x i]
  unfold exponentSetPoleWeight
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨Finsupp.single i 1, hi, rfl⟩)

/-- . -/
theorem exponentSetPoleWeight_unitZ
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x : Fin 3 → L) :
    exponentSetPoleWeight v x (flagSupport unitZFlag) = poleOrder v (x 2) := by
  apply le_antisymm
  · simpa [unitZFlag] using exponentSetPoleWeight_flagSupport_le v x unitZFlag
  · apply poleOrder_le_support_of_mem v x unitZFlag 2
    rw [mem_flagSupport_iff]
    simp [InFlag, unitZFlag]

theorem exponentSetPoleWeight_unitYZ
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x : Fin 3 → L) :
    exponentSetPoleWeight v x (flagSupport unitYZFlag) =
      max (poleOrder v (x 0)) (poleOrder v (x 2)) := by
  apply le_antisymm
  · simpa [unitYZFlag] using exponentSetPoleWeight_flagSupport_le v x unitYZFlag
  · apply max_le
    · apply poleOrder_le_support_of_mem v x unitYZFlag 0
      rw [mem_flagSupport_iff]
      simp [InFlag, unitYZFlag]
    · apply poleOrder_le_support_of_mem v x unitYZFlag 2
      rw [mem_flagSupport_iff]
      simp [InFlag, unitYZFlag]

theorem exponentSetPoleWeight_unitAll
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x : Fin 3 → L) :
    exponentSetPoleWeight v x (flagSupport unitAllFlag) =
      max (poleOrder v (x 1))
        (max (poleOrder v (x 0)) (poleOrder v (x 2))) := by
  apply le_antisymm
  · simpa [unitAllFlag] using exponentSetPoleWeight_flagSupport_le v x unitAllFlag
  · apply max_le
    · apply poleOrder_le_support_of_mem v x unitAllFlag 1
      rw [mem_flagSupport_iff]
      simp [InFlag, unitAllFlag]
    · apply max_le
      · apply poleOrder_le_support_of_mem v x unitAllFlag 0
        rw [mem_flagSupport_iff]
        simp [InFlag, unitAllFlag]
      · apply poleOrder_le_support_of_mem v x unitAllFlag 2
        rw [mem_flagSupport_iff]
        simp [InFlag, unitAllFlag]

/-- .
 -/
theorem exponentSetPoleWeight_flagSupport_le_three
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x : Fin 3 → L)
    (p : FlagDegree) :
    exponentSetPoleWeight v x (flagSupport p) ≤
      (p.zOnly : ℤ) * exponentSetPoleWeight v x (flagSupport unitZFlag) +
      (p.yz : ℤ) * exponentSetPoleWeight v x (flagSupport unitYZFlag) +
      (p.all : ℤ) * exponentSetPoleWeight v x (flagSupport unitAllFlag) := by
  rw [exponentSetPoleWeight_unitZ, exponentSetPoleWeight_unitYZ,
    exponentSetPoleWeight_unitAll]
  exact exponentSetPoleWeight_flagSupport_le v x p

end

end ProximityPrize.SubmissionLower.ContactFlagPoleInequality6543Research
