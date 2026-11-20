/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Koala6831SeparatedDegreeOne
import ProximityPrize.SubmissionLower.Koala6831SeparationNormalForm

/- Support transport and component weight calculation adapted from Lucieno's PR 618
as carried in the authors' 68.32 release. Direct construction of the normal form below. -/
namespace ProximityPrize.SubmissionLower.FrontierGeometry
open MvPolynomial Koala6831Ordinary Koala6831Comparison Koala6831Separation
open Koala6831SeparationFactors (affine)
open Koala6831CoefficientSystem (coefficientPolynomial)
open scoped BigOperators Matrix Polynomial
noncomputable section
variable {K : Type*} [Field K]
private theorem from_seed_support (P : SeedCoefficients K) (j : ℕ) (z : Fin 2 →₀ ℕ)
    (hz : z ∈ (P.coeff j).support) :
    ∃ e ∈ (retainCarrier (carrierOfSeedCoefficients P)).support, e 3 = z 0 ∧ e 4 = z 1 := by
  let R := (MvPolynomial.optionEquivLeft K (Fin 2)).symm P
  let f := carrierCoordinates ∘ carrierCoefficientCoordinates
  let d := z.optionElim j
  have hdf : d ∈ R.support := by
    apply MvPolynomial.mem_support_iff.mpr
    have he := MvPolynomial.optionEquivLeft_coeff_coeff K R j z
    change ((((MvPolynomial.optionEquivLeft K (Fin 2))
      ((MvPolynomial.optionEquivLeft K (Fin 2)).symm P)).coeff j).coeff z) = R.coeff d at he
    rw [AlgEquiv.apply_symm_apply] at he
    exact he ▸ MvPolynomial.mem_support_iff.mp hz
  have hf : Function.Injective f := by
    change ∀ i j : Option (Fin 2), f i = f j → i = j
    decide
  have hLift : retainCarrier (carrierOfSeedCoefficients P) = MvPolynomial.rename f R := by
    rw [retainCarrier, carrierOfSeedCoefficients]
    change MvPolynomial.rename carrierCoordinates (MvPolynomial.rename carrierCoefficientCoordinates R) = _
    rw [MvPolynomial.rename_rename]
  refine ⟨Finsupp.mapDomain f d, ?_, ?_, ?_⟩
  · rw [hLift, MvPolynomial.support_rename_of_injective hf]
    exact Finset.mem_image.mpr ⟨d, hdf, rfl⟩
  · change Finsupp.mapDomain f d (f (some 0)) = _
    rw [Finsupp.mapDomain_apply_of_injective hf]
    simp [d]
  · change Finsupp.mapDomain f d (f (some 1)) = _
    rw [Finsupp.mapDomain_apply_of_injective hf]
    simp [d]

private theorem coefficientPolynomial_zero_off_constant (P : SeedCoefficients K)
    (hwt : weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients P)) = 0)
    (z : Fin 2 →₀ ℕ) (hz : z ≠ 0) (δ : ℕ) : coefficientPolynomial P z δ = 0 := by
  unfold coefficientPolynomial
  apply Finset.sum_eq_zero
  intro j _
  suffices (P.coeff j).coeff z = 0 by rw [this, Polynomial.monomial_zero_right]
  by_contra h
  obtain ⟨e, he, h₀, h₁⟩ := from_seed_support P j z (MvPolynomial.mem_support_iff.mpr h)
  have hdegree := MvPolynomial.le_weightedTotalDegree totalWeights he
  change Finsupp.weight totalWeights e ≤ weightDegree totalWeights
    (retainCarrier (carrierOfSeedCoefficients P)) at hdegree
  rw [hwt, total_weight, h₀, h₁] at hdegree
  apply hz
  ext i
  fin_cases i
  · change z 0 = 0
    omega
  · change z 1 = 0
    omega

private theorem value_coefficient_weights_zero (q : SymbolicRow (SeedRing K))
    (hf : q.first ≠ 0) (hs : q.second ≠ 0)
    (hdegree : weightDegree totalWeights (primitiveRowLift q) ≤ 1) :
    weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.first)) = 0 ∧
      weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.second)) = 0 ∧
      weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.beta)) ≤ 1 := by
  have hfirst : retainCarrier (carrierOfSeedCoefficients q.first) ≠ 0 := fun hz =>
    carrierOfSeedCoefficients_ne_zero hf (retainCarrier_injective (by simpa using hz))
  have hsecond : retainCarrier (carrierOfSeedCoefficients q.second) ≠ 0 := fun hz =>
    carrierOfSeedCoefficients_ne_zero hs (retainCarrier_injective (by simpa using hz))
  rw [primitiveRowLift_weight_max, weight_mul_eq _ hfirst (MvPolynomial.X_ne_zero _),
    weight_mul_eq _ hsecond (MvPolynomial.X_ne_zero _), weight_X, weight_X] at hdegree
  change max (max (weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.beta)))
    (weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.first)) + 1))
    (weightDegree totalWeights (retainCarrier (carrierOfSeedCoefficients q.second)) + 1) ≤ 1 at hdegree
  exact ⟨by omega, by omega, by omega⟩

private theorem constant_regroup (P : SeedCoefficients K) (h : weightDegree totalWeights
    (retainCarrier (carrierOfSeedCoefficients P)) = 0) (δ : ℕ) (hp : P.natDegree ≤ δ) :
    regroup P = C (coefficientPolynomial P 0 δ) := by
  ext z
  rw [coeff_regroup_eq _ _ _ hp, coeff_C]
  by_cases hz : z = 0
  · simp [hz]
  · simp [coefficientPolynomial_zero_off_constant P h z hz δ, Ne.symm hz]

private theorem zero_high (P : SeedCoefficients K) (h : weightDegree totalWeights
    (retainCarrier (carrierOfSeedCoefficients P)) ≤ 1)
    (z : Fin 2 →₀ ℕ) (hz : 1 < z 0 + z 1) (δ : ℕ) :
    coefficientPolynomial P z δ = 0 := by
  unfold coefficientPolynomial
  apply Finset.sum_eq_zero
  intro j _
  suffices (P.coeff j).coeff z = 0 by rw [this, Polynomial.monomial_zero_right]
  by_contra! hne
  obtain ⟨e, he, h₀, h₁⟩ := from_seed_support P j z (MvPolynomial.mem_support_iff.mpr hne)
  have hdegree := (MvPolynomial.le_weightedTotalDegree totalWeights he).trans h
  rw [total_weight, h₀, h₁] at hdegree
  omega

private theorem small_key (z : Fin 2 →₀ ℕ) (hz : z 0 + z 1 ≤ 1) :
    z = 0 ∨ z = Finsupp.single 0 1 ∨ z = Finsupp.single 1 1 := by
  by_cases h₀ : z 0 = 0
  · by_cases h₁ : z 1 = 0
    · left; ext i; fin_cases i <;> assumption
    · right; right; ext i; fin_cases i <;> simp <;> omega
  · right; left; ext i; fin_cases i <;> simp <;> omega

private theorem affine_regroup (P : SeedCoefficients K) (h : weightDegree totalWeights
    (retainCarrier (carrierOfSeedCoefficients P)) ≤ 1) (D : ℕ) (hp : P.natDegree ≤ D) :
    let b := fun k => coefficientPolynomial P k D
    regroup P = affine 0 (b 0) (b (Finsupp.single 0 1)) +
      affine 1 0 (b (Finsupp.single 1 1)) := by
  dsimp only
  ext z
  rw [coeff_regroup_eq _ _ _ hp]
  have h01 : (Finsupp.single (0:Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro he
    have he' := DFunLike.congr_fun he 0
    simp at he'
  have zn (i : Fin 2) : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro he
    have hh := DFunLike.congr_fun he i
    simp at hh
  by_cases hz : z 0 + z 1 ≤ 1
  · rcases small_key z hz with rfl | rfl | rfl <;>
      simp [affine, coeff_X, h01, Ne.symm h01, zn]
  · have h0 : z ≠ 0 := by rintro rfl; simp at hz
    have hl : z ≠ Finsupp.single 0 1 := by rintro rfl; simp at hz
    have hr : z ≠ Finsupp.single 1 1 := by rintro rfl; simp at hz
    rw [zero_high P h z (by omega) D]
    simp [affine, coeff_X, Ne.symm h0, Ne.symm hl, Ne.symm hr]

/-- The linear combined-degree branch has a normal form over every field, for every
excess and length. No node-count or singular-minor assumption occurs. -/
theorem linear_normal_form (q : SymbolicRow (SeedRing K)) (w δ : ℕ)
    (hf : q.first ≠ 0) (hs : q.second ≠ 0) (hfdeg : q.first.natDegree ≤ δ)
    (hsdeg : q.second.natDegree ≤ δ) (hbdeg : q.beta.natDegree ≤ w+δ)
    (hdegree : weightDegree totalWeights (primitiveRowLift q) ≤ 1) :
    Nonempty (NormalForm q w δ) := by
  obtain ⟨ha,hb,hc⟩ := value_coefficient_weights_zero q hf hs hdegree
  let a := coefficientPolynomial q.first 0 δ
  let b := coefficientPolynomial q.second 0 δ
  let c := fun k => coefficientPolynomial q.beta k (w+δ)
  have hfirst := constant_regroup q.first ha δ hfdeg
  have hsecond := constant_regroup q.second hb δ hsdeg
  have na : a ≠ 0 := by
    intro hz
    apply hf
    apply regroup_injective
    change regroup q.first = regroup 0
    rw [hfirst, ← show a = coefficientPolynomial q.first 0 δ from rfl, hz, map_zero, map_zero]
  have nb : b ≠ 0 := by
    intro hz
    apply hs
    apply regroup_injective
    change regroup q.second = regroup 0
    rw [hsecond, ← show b = coefficientPolynomial q.second 0 δ from rfl, hz, map_zero, map_zero]
  have da : a.natDegree ≤ δ := Koala6831CoefficientSystem.coefficientPolynomial_degree _ _ _
  have db : b.natDegree ≤ δ := Koala6831CoefficientSystem.coefficientPolynomial_degree _ _ _
  have dc (k) : (c k).natDegree ≤ w+δ := Koala6831CoefficientSystem.coefficientPolynomial_degree _ _ _
  refine ⟨⟨![1,0], ![1,0], ![c 0,c (Finsupp.single 0 1)], ![0,c (Finsupp.single 1 1)],
    a, -b, na, neg_ne_zero.mpr nb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact isCoprime_one_left
  · exact isCoprime_one_left
  · simpa [affine, a] using hfirst
  · simpa [affine, b] using hsecond
  · simpa [affine, c] using affine_regroup q.beta hc (w+δ) hbdeg
  · simpa [pairDegree] using da
  · simpa [pairDegree] using db
  · simp [pairDegree, dc]
  · simp [pairDegree, dc]

#print axioms linear_normal_form
end
end ProximityPrize.SubmissionLower.FrontierGeometry
