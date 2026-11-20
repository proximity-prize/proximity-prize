import ProximityPrize.SubmissionLower.Koala6844NormalizationData



namespace ProximityPrize.SubmissionLower.Koala6844VirtualCRT

open Polynomial
open Koala6844Normalization

noncomputable section

set_option autoImplicit false

private theorem residue_of_split {K : Type} [Field K]
    {d D A Q U θ R : Polynomial K} (hd : d ∣ D)
    (hdecomp : Q = θ + D * R) (hresidue : d ∣ A * Q - U) :
    d ∣ A * θ - U := by
  have hmul : d ∣ A * (D * R) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd R) A
  have hEq : A * Q - U - A * (D * R) = A * θ - U := by rw [hdecomp]; ring
  rw [← hEq]
  exact dvd_sub hresidue hmul

theorem trim_of_congruences {K : Type} [Field K]
    (d₀ d₁ A B U V Q : Polynomial K) (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0)
    (h₀ : d₀ ∣ A * Q - U) (h₁ : d₁ ∣ B * Q - V) :
    let D := d₀ * d₁
    let θ := Q % D
    let R := Q / D
    Q = θ + D * R ∧ θ.degree < D.degree ∧ d₀ ∣ A * θ - U ∧
      d₁ ∣ B * θ - V ∧ R.natDegree ≤ Q.natDegree - D.natDegree := by
  dsimp only
  let D := d₀ * d₁
  let θ := Q % D
  let R := Q / D
  have hD : D ≠ 0 := mul_ne_zero hd₀ hd₁
  have hsplit : Q = θ + D * R := (EuclideanDomain.mod_add_div Q D).symm
  change Q = θ + D * R ∧ θ.degree < D.degree ∧ d₀ ∣ A * θ - U ∧
    d₁ ∣ B * θ - V ∧ R.natDegree ≤ Q.natDegree - D.natDegree
  refine ⟨hsplit, Polynomial.degree_mod_lt Q hD,
    residue_of_split (dvd_mul_right d₀ d₁) hsplit h₀,
    residue_of_split (dvd_mul_left d₁ d₀) hsplit h₁, ?_⟩
  by_cases hR : R = 0
  · simp [hR]
  have htheta : θ.natDegree ≤ Q.natDegree := by
    simp only [θ, Polynomial.mod_def]
    exact Polynomial.natDegree_modByMonic_le_left
  have hmul : D * R = Q - θ := by rw [hsplit]; ring
  have hdeg := Polynomial.natDegree_sub_le Q θ
  rw [← hmul, Polynomial.natDegree_mul hD hR, max_eq_left htheta] at hdeg
  omega


theorem centered_trim {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
    {w agreement errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ w agreement errors excess)
    (g : K) (hg : g ∈ data.seeds) :
    let D := data.d0 * data.d1
    let θ := data.normalized g % D
    let R := data.normalized g / D
    data.normalized g = θ + D * R ∧ θ.degree < D.degree ∧
      data.d0 ∣ specializeAffine data.A0 g * θ - C g * data.C1 ∧
      data.d1 ∣ (specializeAffine data.A0 g).map σ.toRingHom * θ - C (σ g) * data.D1 ∧
      R.natDegree ≤ w - (data.d0.natDegree + affineDegree data.A0) := by
  dsimp only
  have h₀ : data.d0 ∣ specializeAffine data.A0 g * data.normalized g - C g * data.C1 := by
    rw [data.equation0 g hg, add_sub_cancel_right]
    exact dvd_mul_right _ _
  have h₁ : data.d1 ∣ (specializeAffine data.A0 g).map σ.toRingHom * data.normalized g -
      C (σ g) * data.D1 := by
    rw [data.equation1 g hg, add_sub_cancel_right]
    exact dvd_mul_right _ _
  obtain ⟨hsplit, hθ, hθ₀, hθ₁, hR⟩ := trim_of_congruences data.d0 data.d1
    (specializeAffine data.A0 g) ((specializeAffine data.A0 g).map σ.toRingHom)
    (C g * data.C1) (C (σ g) * data.D1) (data.normalized g) data.d0_ne data.d1_ne h₀ h₁
  refine ⟨hsplit, hθ, hθ₀, hθ₁, hR.trans ?_⟩
  rw [Polynomial.natDegree_mul data.d0_ne data.d1_ne, data.degree_content]
  have h := data.normalized_degree g hg
  omega

end

end ProximityPrize.SubmissionLower.Koala6844VirtualCRT

