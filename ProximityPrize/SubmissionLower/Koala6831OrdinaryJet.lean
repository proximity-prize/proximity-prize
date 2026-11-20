import ProximityPrize.SubmissionLower.Koala6831OrdinaryWeights
import ProximityPrize.SubmissionLower.Koala6831Quotient
import ProximityPrize.SubmissionLower.Koala6831QuotientBoxes



namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open MvPolynomial Koala6831Quotient
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

def codeWeights (w : ℕ) : Fin 5 → ℕ := ![1, w, w, 0, 0]
def germWeights : Fin 5 → ℕ := codeWeights 1
def valueWeights : Fin 5 → ℕ := ![0, 1, 1, 0, 0]
def totalWeights : Fin 5 → ℕ := ![0, 1, 1, 1, 1]

@[simp] theorem code_weight (w : ℕ) (d : Fin 5 →₀ ℕ) :
    Finsupp.weight (codeWeights w) d = d 0 + w * (d 1 + d 2) := by
  simp [weight_five, codeWeights, Nat.mul_add, Nat.mul_comm, Nat.add_assoc]

@[simp] theorem germ_weight (d : Fin 5 →₀ ℕ) :
    Finsupp.weight germWeights d = d 0 + d 1 + d 2 := by
  simp [germWeights, Nat.add_assoc]

@[simp] theorem value_weight (d : Fin 5 →₀ ℕ) :
    Finsupp.weight valueWeights d = d 1 + d 2 := by
  simp [weight_five, valueWeights]

@[simp] theorem total_weight (d : Fin 5 →₀ ℕ) :
    Finsupp.weight totalWeights d = d 1 + d 2 + d 3 + d 4 := by
  simp [weight_five, totalWeights]

theorem ordinaryBox_iff_weights {D w y L : ℕ} (positive : 0 < D) (P : Poly K) :
    P ∈ ordinaryBox K D w y L ↔
      weightDegree (codeWeights w) P < D ∧ weightDegree valueWeights P ≤ y ∧
        weightDegree totalWeights P ≤ L := by
  rw [MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro supported
    refine ⟨?_, Finset.sup_le ?_, Finset.sup_le ?_⟩
    · have code_bound : weightDegree (codeWeights w) P ≤ D - 1 := by
        apply Finset.sup_le
        intro d hd
        have h := (supported hd).1
        rw [code_weight]
        change d 0 + w * (d 1 + d 2) < D at h
        omega
      omega
    · intro d hd
      exact (value_weight d).trans_le (supported hd).2.1
    · intro d hd
      exact (total_weight d).trans_le (supported hd).2.2
  · intro ⟨hD, hy, hL⟩ d hd
    change d 0 + w * (d 1 + d 2) < D ∧ d 1 + d 2 ≤ y ∧
      d 1 + d 2 + d 3 + d 4 ≤ L
    refine ⟨?_, ?_, ?_⟩
    · simpa only [code_weight] using (le_weightedTotalDegree (codeWeights w) hd).trans_lt hD
    · simpa only [value_weight] using (le_weightedTotalDegree valueWeights hd).trans hy
    · simpa only [total_weight] using (le_weightedTotalDegree totalWeights hd).trans hL

theorem center_total_le (x u₀ v₀ u₁ v₁ : K) (P : Poly K) :
    weightDegree totalWeights (centerAtNode x u₀ v₀ u₁ v₁ P) ≤ weightDegree totalWeights P := by
  let v : Fin 5 → Poly K :=
    ![X 0 + C x, X 1 + C u₀ + X 3 * C v₀,
      X 2 + C u₁ + X 4 * C v₁, X 3, X 4]
  change weightDegree totalWeights (aeval v P) ≤ weightDegree totalWeights P
  apply weight_eval_le totalWeights totalWeights
  have seed_bound (i : Fin 5) (h : totalWeights i = 1) (a : K) :
      weightDegree totalWeights ((X i : Poly K) * C a) ≤ 1 := by
    simpa only [weight_X, weight_C, h, add_zero] using weight_mul_le totalWeights (X i) (C a)
  have shift_bound (i : Fin 5) (a : K) :
      weightDegree totalWeights ((X i : Poly K) + C a) ≤ totalWeights i := by
    simpa only [weight_X, weight_C, max_zero] using weight_add_le totalWeights (X i) (C a)
  intro i
  fin_cases i
  · change weightDegree totalWeights (X 0 + C x) ≤ totalWeights 0
    exact shift_bound 0 x
  · change weightDegree totalWeights (X 1 + C u₀ + X 3 * C v₀) ≤ 1
    exact (weight_add_le totalWeights _ _).trans (max_le (shift_bound 1 u₀) (seed_bound 3 rfl v₀))
  · change weightDegree totalWeights (X 2 + C u₁ + X 4 * C v₁) ≤ 1
    exact (weight_add_le totalWeights _ _).trans (max_le (shift_bound 2 u₁) (seed_bound 4 rfl v₁))
  · change weightDegree totalWeights (X 3 : Poly K) ≤ totalWeights 3
    rw [weight_X]
  · change weightDegree totalWeights (X 4 : Poly K) ≤ totalWeights 4
    rw [weight_X]

def truncate (m : ℕ) : Poly K →ₗ[K] Poly K :=
  ∑ r ∈ Finset.range m, weightedHomogeneousComponent germWeights r

theorem truncate_coeff (m : ℕ) (P : Poly K) (d : Fin 5 →₀ ℕ) :
    (truncate m P).coeff d = if Finsupp.weight germWeights d < m then P.coeff d else 0 := by
  classical
  rw [truncate, LinearMap.sum_apply, MvPolynomial.coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  by_cases low : Finsupp.weight germWeights d < m
  · rw [ite_eq_left low, Finset.sum_eq_single (Finsupp.weight germWeights d)]
    · simp
    · intro r _ hr
      exact ite_eq_right (Ne.symm hr)
    · exact fun h => (h (Finset.mem_range.mpr low)).elim
  · rw [ite_eq_right low]
    apply Finset.sum_eq_zero
    intro r hr
    have hne : Finsupp.weight germWeights d ≠ r := fun he => low (he.symm ▸ Finset.mem_range.mp hr)
    exact ite_eq_right hne

theorem support_truncate (m : ℕ) (P : Poly K) {d : Fin 5 →₀ ℕ}
    (hd : d ∈ (truncate m P).support) :
    d ∈ P.support ∧ Finsupp.weight germWeights d < m := by
  rw [mem_support_iff, truncate_coeff] at hd
  split_ifs at hd with h
  · exact ⟨mem_support_iff.mpr hd, h⟩
  · exact False.elim (hd rfl)

theorem truncate_mem_box (m L : ℕ) (P : Poly K) (total : weightDegree totalWeights P ≤ L) :
    truncate m P ∈ ordinaryBox K m 1 (m - 1) L := by
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro d hd
  obtain ⟨in_P, low⟩ := support_truncate m P hd
  have ht := (le_weightedTotalDegree totalWeights in_P).trans total
  simp only [germ_weight] at low
  simp only [total_weight] at ht
  refine ⟨?_, ?_, ht⟩ <;> omega

theorem high_of_truncate_eq (m : ℕ) (P R : Poly K) (equal : truncate m P = truncate m R) :
    ∀ d ∈ (P - R).support, m ≤ Finsupp.weight germWeights d := by
  intro d hd
  by_contra! low
  have equal_coeff := congrArg (fun X : Poly K => X.coeff d) equal
  simp only [truncate_coeff, ite_eq_left low] at equal_coeff
  apply mem_support_iff.mp hd
  rw [MvPolynomial.coeff_sub, equal_coeff, sub_self]

theorem power_dvd_lift_of_high (m : ℕ) (P : Poly K)
    (high : ∀ d ∈ P.support, m ≤ Finsupp.weight germWeights d) :
    Polynomial.X ^ m ∣ weightLift germWeights P := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro r hr
  rw [weightLift_coeff]
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with degree
  · apply notMem_support_iff.mp
    intro hd
    exact (Nat.not_le_of_gt hr) (by simpa only [degree] using high d hd)
  · rfl

theorem germ_order_one_of_components (P : Poly K)
    (constant_zero : weightedHomogeneousComponent germWeights 0 P = 0)
    (linear_nonzero : weightedHomogeneousComponent germWeights 1 P ≠ 0) :
    (weightLift germWeights P).natTrailingDegree = 1 := by
  let f := weightLift germWeights P
  have f₀ : f.coeff 0 = 0 := by rw [show f = weightLift germWeights P from rfl, weightLift_coeff, constant_zero]
  have f₁ : f.coeff 1 ≠ 0 := by simpa only [f, weightLift_coeff] using linear_nonzero
  have f_ne : f ≠ 0 := fun h => f₁ (by simp [h])
  have order_le := Polynomial.natTrailingDegree_le_of_ne_zero f₁
  have order_ne : f.natTrailingDegree ≠ 0 := by
    intro eq
    exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr f_ne) (eq.symm ▸ f₀)
  exact (show f.natTrailingDegree = 1 by omega)

abbrev LocalBox (K : Type*) [Field K] (m L : ℕ) := ordinaryBox K m 1 (m - 1) L

def leftMultiply (q : Poly K) : Poly K →ₗ[K] Poly K where
  toFun P := q * P
  map_add' P R := mul_add q P R
  map_smul' a P := by simp

def truncateMultiplier (m L c : ℕ) (m_pos : 2 ≤ m) (c_le : c ≤ L)
    (row : Poly K) (row_total : weightDegree totalWeights row ≤ c) :
    LocalBox K (m - 1) (L - c) →ₗ[K] LocalBox K m L :=
  ((truncate m).comp ((leftMultiply row).comp (LocalBox K (m - 1) (L - c)).subtype)).codRestrict _
    (fun B => by
      change truncate m (row * B.val) ∈ LocalBox K m L
      apply truncate_mem_box
      have mult_total := ((ordinaryBox_iff_weights (by omega) B.val).mp B.property).2.2
      exact (weight_mul_le totalWeights row B.val).trans
        ((Nat.add_le_add row_total mult_total).trans (by omega)))

theorem truncateMultiplier_injective (m L c : ℕ) (m_pos : 2 ≤ m) (c_le : c ≤ L)
    (row : Poly K) (row_total : weightDegree totalWeights row ≤ c)
    (order : (weightLift germWeights row).natTrailingDegree = 1) :
    Function.Injective (truncateMultiplier m L c m_pos c_le row row_total) := by
  intro B R equal
  apply Subtype.ext
  have hrow : weightLift germWeights row ≠ 0 := by
    intro zero
    simp [zero] at order
  have same : truncate m (row * B.val) = truncate m (row * R.val) := congrArg Subtype.val equal
  have diff_high := high_of_truncate_eq m _ _ same
  have divides := power_dvd_lift_of_high m _ diff_high
  rw [map_sub, map_mul, map_mul] at divides
  have small (P : LocalBox K (m - 1) (L - c)) :
      (weightLift germWeights P.val).degree < (↑(m - 1) : WithBot ℕ) := by
    have hcode := ((ordinaryBox_iff_weights (by omega) P.val).mp P.property).1
    have nat_lt : (weightLift germWeights P.val).natDegree < m - 1 := by
      rwa [weightLift_natDegree]
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast nat_lt)
  have eq_hom := local_multiplier_injective m hrow order (small B) (small R) divides
  apply sub_eq_zero.mp
  by_contra nonzero
  exact weightLift_ne_zero germWeights nonzero (by rw [map_sub, eq_hom, sub_self])

def truncateGerm (D w y L m : ℕ) (D_pos : 0 < D) (x u₀ v₀ u₁ v₁ : K) :
    ordinaryBox K D w y L →ₗ[K] LocalBox K m L :=
  ((truncate m).comp ((centerAtNode x u₀ v₀ u₁ v₁).toLinearMap.comp
    (ordinaryBox K D w y L).subtype)).codRestrict _
    (fun P => by
      change truncate m (centerAtNode x u₀ v₀ u₁ v₁ P.val) ∈ LocalBox K m L
      exact truncate_mem_box _ _ _ ((center_total_le _ _ _ _ _ _).trans
        ((ordinaryBox_iff_weights D_pos P.val).mp P.property).2.2))

end

end ProximityPrize.SubmissionLower.Koala6831Ordinary
