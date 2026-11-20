import ProximityPrize.SubmissionLower.Koala6844HighOrdinaryPrimitiveLift



namespace ProximityPrize.SubmissionLower.Koala6844Comparison

open MvPolynomial Koala6844HighOrdinary
open scoped BigOperators Classical

noncomputable section

variable {K : Type*} [Field K]

private def fullCoefficientCoordinates : Option (Fin 2) → Fin 5
  | none => 0
  | some i => ![(3 : Fin 5), 4] i

private theorem fullCoefficientCoordinates_injective :
    Function.Injective fullCoefficientCoordinates := by
  intro i j h
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some j => fin_cases j <;> simp [fullCoefficientCoordinates] at h
  | some i =>
      cases j with
      | none => fin_cases i <;> simp [fullCoefficientCoordinates] at h
      | some j =>
          fin_cases i <;> fin_cases j <;>
            first | rfl | (simp [fullCoefficientCoordinates] at h)

private theorem fullCoefficientCoordinates_not_value₀ : (1 : Fin 5) ∉ Set.range fullCoefficientCoordinates := by
  rintro ⟨i, hi⟩
  cases i with
  | none => simp [fullCoefficientCoordinates] at hi
  | some i => fin_cases i <;> simp [fullCoefficientCoordinates] at hi

private theorem fullCoefficientCoordinates_not_value₁ : (2 : Fin 5) ∉ Set.range fullCoefficientCoordinates := by
  rintro ⟨i, hi⟩
  cases i with
  | none => simp [fullCoefficientCoordinates] at hi
  | some i => fin_cases i <;> simp [fullCoefficientCoordinates] at hi

private def addMissingValues (P : SeedCoefficients K) : Koala6844HighOrdinary.Poly K :=
  retainCarrier (carrierOfSeedCoefficients P)

private theorem addMissingValues_eq_rename (P : SeedCoefficients K) :
    addMissingValues P = MvPolynomial.rename fullCoefficientCoordinates
      ((MvPolynomial.optionEquivLeft K (Fin 2)).symm P) := by
  rw [addMissingValues, retainCarrier, carrierOfSeedCoefficients]
  change MvPolynomial.rename carrierCoordinates (MvPolynomial.rename _ _) = _
  have h : carrierCoordinates ∘ carrierCoefficientCoordinates = fullCoefficientCoordinates := by
    funext i
    cases i with
    | none => rfl
    | some i => fin_cases i <;> rfl
  rw [MvPolynomial.rename_rename, h]
  rfl

private theorem addMissingValues_injective : Function.Injective (addMissingValues (K := K)) := by
  intro P Q h
  rw [addMissingValues_eq_rename, addMissingValues_eq_rename] at h
  apply (MvPolynomial.optionEquivLeft K (Fin 2)).symm.injective
  exact MvPolynomial.rename_injective _ fullCoefficientCoordinates_injective h

theorem carrierOfSeedCoefficients_injective :
    Function.Injective (carrierOfSeedCoefficients (K := K)) := by
  intro P Q h
  exact addMissingValues_injective (congrArg (retainCarrier (K := K)) h)

theorem carrierOfSeedCoefficients_ne_zero {P : SeedCoefficients K} (h : P ≠ 0) :
    carrierOfSeedCoefficients P ≠ 0 := by
  intro hz
  exact h (carrierOfSeedCoefficients_injective (by rw [hz, map_zero]))

private theorem addMissingValues_ne_zero {P : SeedCoefficients K} (h : P ≠ 0) :
    addMissingValues P ≠ 0 := by
  intro hz
  exact h (addMissingValues_injective (by simpa [addMissingValues] using hz))

theorem liftedCoefficient_support_shape (P : SeedCoefficients K) (e : Fin 5 →₀ ℕ)
    (he : e ∈ (retainCarrier (carrierOfSeedCoefficients P)).support) :
    e 1 = 0 ∧ e 2 = 0 ∧ e 0 ∈ P.support ∧
      ∃ z ∈ (P.coeff (e 0)).support, z 0 = e 3 ∧ z 1 = e 4 := by
  change e ∈ (addMissingValues P).support at he
  rw [addMissingValues_eq_rename, MvPolynomial.support_rename_of_injective
    fullCoefficientCoordinates_injective] at he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  have h₀ : (Finsupp.mapDomain fullCoefficientCoordinates d) 0 = d none :=
    Finsupp.mapDomain_apply_of_injective fullCoefficientCoordinates_injective d none
  have h₃ : (Finsupp.mapDomain fullCoefficientCoordinates d) 3 = d (some 0) :=
    Finsupp.mapDomain_apply_of_injective fullCoefficientCoordinates_injective d (some 0)
  have h₄ : (Finsupp.mapDomain fullCoefficientCoordinates d) 4 = d (some 1) :=
    Finsupp.mapDomain_apply_of_injective fullCoefficientCoordinates_injective d (some 1)
  refine ⟨Finsupp.mapDomain_of_notMem_range d _ fullCoefficientCoordinates_not_value₀,
    Finsupp.mapDomain_of_notMem_range d _ fullCoefficientCoordinates_not_value₁, ?_, ?_⟩
  · rw [h₀]
    have hs := MvPolynomial.support_optionEquivLeft K
      ((MvPolynomial.optionEquivLeft K (Fin 2)).symm P)
    rw [AlgEquiv.apply_symm_apply] at hs
    rw [hs]
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  · rw [h₀, h₃, h₄]
    refine ⟨d.some, ?_, rfl, rfl⟩
    have hp : d.some.optionElim (d none) ∈
        ((MvPolynomial.optionEquivLeft K (Fin 2)).symm P).support := by
      rwa [Finsupp.optionElim_some]
    have hz := (MvPolynomial.mem_support_coeff_optionEquivLeft (R := K)).mpr hp
    rwa [AlgEquiv.apply_symm_apply] at hz

theorem liftedCoefficient_value_weight (P : SeedCoefficients K) :
    weightDegree valueWeights (retainCarrier (carrierOfSeedCoefficients P)) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro e he
  obtain ⟨h₁, h₂, _⟩ := liftedCoefficient_support_shape P e he
  simp [h₁, h₂]

theorem liftedCoefficient_total_weight_le (P : SeedCoefficients K) (b₀ b₁ : ℕ)
    (h₀ : ∀ j, (P.coeff j).degreeOf 0 ≤ b₀) (h₁ : ∀ j, (P.coeff j).degreeOf 1 ≤ b₁) :
    weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients P)) ≤ b₀ + b₁ := by
  apply Finset.sup_le
  intro e he
  obtain ⟨hval₀, hval₁, _, z, hz, hz₀, hz₁⟩ := liftedCoefficient_support_shape P e he
  have hseed₀ := (MvPolynomial.le_degreeOf_of_mem_support (0 : Fin 2) hz).trans (h₀ (e 0))
  have hseed₁ := (MvPolynomial.le_degreeOf_of_mem_support (1 : Fin 2) hz).trans (h₁ (e 0))
  simp only [total_weight, hval₀, hval₁, zero_add]
  omega

theorem liftedCoefficient_code_weight (w : ℕ) (P : SeedCoefficients K) :
    weightDegree (codeWeights w) (retainCarrier (carrierOfSeedCoefficients P)) = P.natDegree := by
  apply le_antisymm
  · apply Finset.sup_le
    intro e he
    obtain ⟨h₁, h₂, hX, _⟩ := liftedCoefficient_support_shape P e he
    simp only [code_weight, h₁, h₂, Nat.mul_zero, add_zero]
    exact Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hX)
  · by_cases hP : P = 0
    · simp [hP]
    let r := (MvPolynomial.optionEquivLeft K (Fin 2)).symm P
    have hr : P.support = Finset.image (fun m => m none) r.support := by
      have hh := MvPolynomial.support_optionEquivLeft K r
      simpa [r] using hh
    have hns : P.natDegree ∈ P.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP)
    rw [hr] at hns
    obtain ⟨d, hd, hdn⟩ := Finset.mem_image.mp hns
    let e := Finsupp.mapDomain fullCoefficientCoordinates d
    have he : e ∈ (addMissingValues P).support := by
      rw [addMissingValues_eq_rename, MvPolynomial.support_rename_of_injective
        fullCoefficientCoordinates_injective]
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have hc : e 0 = P.natDegree :=
      (Finsupp.mapDomain_apply_of_injective fullCoefficientCoordinates_injective d none).trans hdn
    obtain ⟨h₁, h₂, _⟩ := liftedCoefficient_support_shape P e he
    have hl := MvPolynomial.le_weightedTotalDegree (codeWeights w) he
    simpa only [code_weight, h₁, h₂, Nat.mul_zero, add_zero, hc, addMissingValues] using hl

private theorem support_add_eq_of_disjoint (P Q : Koala6844HighOrdinary.Poly K)
    (h : Disjoint P.support Q.support) : (P + Q).support = P.support ∪ Q.support := by
  ext e
  by_cases hP : P.coeff e = 0
  · simp [MvPolynomial.mem_support_iff, hP]
  · have hQ : Q.coeff e = 0 := by
      by_contra hne
      exact Finset.disjoint_left.mp h (MvPolynomial.mem_support_iff.mpr hP)
        (MvPolynomial.mem_support_iff.mpr hne)
    simp [MvPolynomial.mem_support_iff, hP, hQ]

private theorem weighted_support_add (w : Fin 5 → ℕ) (P Q : Koala6844HighOrdinary.Poly K)
    (h : Disjoint P.support Q.support) :
    weightDegree w (P + Q) = max (weightDegree w P) (weightDegree w Q) := by
  rw [show weightDegree w (P + Q) = (P + Q).support.sup (Finsupp.weight w) from rfl,
    support_add_eq_of_disjoint P Q h, Finset.sup_union]
  rfl

private theorem value_shifted_support_shape (P : SeedCoefficients K) (j : Fin 5)
    (e : Fin 5 →₀ ℕ) (he : e ∈ (addMissingValues P * MvPolynomial.X j).support) :
    e 1 = (if (1 : Fin 5) = j then 1 else 0) ∧ e 2 = (if (2 : Fin 5) = j then 1 else 0) := by
  rw [MvPolynomial.support_mul_X] at he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
  obtain ⟨h₁, h₂, _⟩ := liftedCoefficient_support_shape P d hd
  simp [h₁, h₂, Finsupp.single_apply, eq_comm]

private theorem primitiveRowLift_weight (q : SymbolicRow (SeedRing K)) (w : Fin 5 → ℕ) :
    weightDegree w (primitiveRowLift q) =
      max (max (weightDegree w (addMissingValues q.beta))
        (weightDegree w (addMissingValues q.first * MvPolynomial.X 1)))
        (weightDegree w (addMissingValues q.second * MvPolynomial.X 2)) := by
  let B := addMissingValues q.beta
  let C₀ := addMissingValues q.first * MvPolynomial.X 1
  let C₁ := addMissingValues q.second * MvPolynomial.X 2
  change weightDegree w (B + C₀ + C₁) = _
  have hB₀ : Disjoint B.support C₀.support := by
    rw [Finset.disjoint_left]
    intro d hd hC
    have h₀ := (liftedCoefficient_support_shape q.beta d hd).1
    have h₁ := (value_shifted_support_shape q.first 1 d hC).1
    simp only [ite_true] at h₁
    omega
  have hBC : Disjoint (B + C₀).support C₁.support := by
    rw [support_add_eq_of_disjoint B C₀ hB₀, Finset.disjoint_left]
    intro d hd hC
    have h₁ := (value_shifted_support_shape q.second 2 d hC).2
    simp only [ite_true] at h₁
    rcases Finset.mem_union.mp hd with hB | hC₀
    · have h₀ := (liftedCoefficient_support_shape q.beta d hB).2.1
      omega
    · have h₀ := (value_shifted_support_shape q.first 1 d hC₀).2
      change d 2 = 0 at h₀
      omega
  rw [weighted_support_add w _ _ hBC, weighted_support_add w _ _ hB₀]

theorem primitiveRowLift_weight_max (q : SymbolicRow (SeedRing K)) (w : Fin 5 → ℕ) :
    weightDegree w (primitiveRowLift q) =
      max (max (weightDegree w (retainCarrier (carrierOfSeedCoefficients q.beta)))
        (weightDegree w (retainCarrier (carrierOfSeedCoefficients q.first) * MvPolynomial.X 1)))
        (weightDegree w (retainCarrier (carrierOfSeedCoefficients q.second) * MvPolynomial.X 2)) :=
  primitiveRowLift_weight q w

theorem primitiveRowLift_code_weight_of_two_sided (q : SymbolicRow (SeedRing K)) (w : ℕ)
    (h₀ : q.first ≠ 0) (h₁ : q.second ≠ 0) :
    weightDegree (codeWeights w) (primitiveRowLift q) = w + primitiveExcess w q := by
  have hx₀ : (MvPolynomial.X 1 : Koala6844HighOrdinary.Poly K) ≠ 0 := MvPolynomial.X_ne_zero _
  have hx₁ : (MvPolynomial.X 2 : Koala6844HighOrdinary.Poly K) ≠ 0 := MvPolynomial.X_ne_zero _
  rw [primitiveRowLift_weight, weight_mul_eq _ (addMissingValues_ne_zero h₀) hx₀,
    weight_mul_eq _ (addMissingValues_ne_zero h₁) hx₁, weight_X, weight_X]
  simp only [addMissingValues]
  rw [liftedCoefficient_code_weight, liftedCoefficient_code_weight, liftedCoefficient_code_weight]
  change max (max q.beta.natDegree (q.first.natDegree + w)) (q.second.natDegree + w) =
    w + max (q.beta.natDegree - w) (max q.first.natDegree q.second.natDegree)
  omega

theorem primitiveRowLift_value_weight_of_two_sided (q : SymbolicRow (SeedRing K))
    (h₀ : q.first ≠ 0) (h₁ : q.second ≠ 0) :
    weightDegree valueWeights (primitiveRowLift q) = 1 := by
  rw [primitiveRowLift_weight, weight_mul_eq _ (addMissingValues_ne_zero h₀) (MvPolynomial.X_ne_zero _),
    weight_mul_eq _ (addMissingValues_ne_zero h₁) (MvPolynomial.X_ne_zero _), weight_X, weight_X]
  simp only [addMissingValues, liftedCoefficient_value_weight]
  simp [valueWeights]

theorem primitiveRowLift_total_weight_caps (q : SymbolicRow (SeedRing K))
    (h₀ : q.first ≠ 0) (h₁ : q.second ≠ 0) :
    let c := weightDegree totalWeights (primitiveRowLift q)
    weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.beta)) ≤ c ∧
      weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.first)) ≤ c - 1 ∧
      weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.second)) ≤ c - 1 := by
  rw [primitiveRowLift_weight, weight_mul_eq _ (addMissingValues_ne_zero h₀) (MvPolynomial.X_ne_zero _),
    weight_mul_eq _ (addMissingValues_ne_zero h₁) (MvPolynomial.X_ne_zero _), weight_X, weight_X]
  let b := weightDegree totalWeights (addMissingValues q.beta)
  let a₀ := weightDegree totalWeights (addMissingValues q.first)
  let a₁ := weightDegree totalWeights (addMissingValues q.second)
  change b ≤ max (max b (a₀ + 1)) (a₁ + 1) ∧
    a₀ ≤ max (max b (a₀ + 1)) (a₁ + 1) - 1 ∧ a₁ ≤ max (max b (a₀ + 1)) (a₁ + 1) - 1
  omega

theorem primitiveRowLift_total_weight_le_ten_of_seed_boxes (q : SymbolicRow (SeedRing K))
    (h : ∀ j, ((q.beta.coeff j).degreeOf 0 ≤ 5 ∧ (q.beta.coeff j).degreeOf 1 ≤ 5) ∧
      ((q.first.coeff j).degreeOf 0 ≤ 4 ∧ (q.first.coeff j).degreeOf 1 ≤ 5) ∧
      ((q.second.coeff j).degreeOf 0 ≤ 5 ∧ (q.second.coeff j).degreeOf 1 ≤ 4)) :
    weightDegree totalWeights (primitiveRowLift q) ≤ 10 := by
  have hβ := liftedCoefficient_total_weight_le q.beta 5 5 (fun n => (h n).1.1) (fun n => (h n).1.2)
  have ha := liftedCoefficient_total_weight_le q.first 4 5 (fun n => (h n).2.1.1) (fun n => (h n).2.1.2)
  have hb := liftedCoefficient_total_weight_le q.second 5 4 (fun n => (h n).2.2.1) (fun n => (h n).2.2.2)
  change weightDegree totalWeights (addMissingValues q.first) ≤ 4 + 5 at ha
  change weightDegree totalWeights (addMissingValues q.second) ≤ 5 + 4 at hb
  rw [primitiveRowLift_weight]
  apply max_le
  · apply max_le hβ
    exact (weight_mul_le _ _ _).trans (by rw [weight_X]; change _ + 1 ≤ 10; omega)
  · exact (weight_mul_le _ _ _).trans (by rw [weight_X]; change _ + 1 ≤ 10; omega)


end

end ProximityPrize.SubmissionLower.Koala6844Comparison
