import ProximityPrize.SubmissionLower.Numeric2Aux

set_option autoImplicit false

namespace H2429ConstantSlopes

open Polynomial P1
open scoped Polynomial

/-- The constant amplitudes give a Möbius coordinate for the labels. -/
structure Coordinate {cap : ℕ} {u : Words} {del : Finset I}
    (M : ModelAt cap u del) (Γ : Finset K) where
  a₀ : K
  a₁ : K
  first : M.A₀ = C a₀
  second : M.A₁ = C a₁
  first_nonzero : a₀ ≠ 0
  denominator_nonzero : ∀ γ ∈ Γ, a₀ + M.label γ * a₁ ≠ 0

noncomputable def Coordinate.denominator {cap : ℕ} {u : Words} {del : Finset I}
    {M : ModelAt cap u del} {Γ : Finset K} (D : Coordinate M Γ) (γ : K) : K :=
  D.a₀ + M.label γ * D.a₁

noncomputable def Coordinate.slope {cap : ℕ} {u : Words} {del : Finset I}
    {M : ModelAt cap u del} {Γ : Finset K} (D : Coordinate M Γ) (γ : K) : K :=
  -M.label γ / D.denominator γ

theorem Coordinate.amplitude_eq {cap : ℕ} {u : Words} {del : Finset I}
    {M : ModelAt cap u del} {Γ : Finset K} (D : Coordinate M Γ) (γ : K) :
    M.amplitude γ = C (D.denominator γ) := by
  simp only [ModelAt.amplitude, Coordinate.denominator, D.first, D.second, map_add, map_mul]

theorem exists_coordinate {cap : ℕ} {u : Words} {del : Finset I} {Γ : Finset K}
    (M : ModelAt cap u del) (F : FamilyAt 179876 M Γ)
    (active : amplitudeDegree M.A₀ M.A₁ = 0) (positive : 0 < M.E.natDegree) :
    Nonempty (Coordinate M Γ) := by
  let a₀ := M.A₀.coeff 0
  let a₁ := M.A₁.coeff 0
  have h₀ : M.A₀ = C a₀ := eq_C_of_natDegree_le_zero ((le_max_left _ _).trans_eq active)
  have h₁ : M.A₁ = C a₁ := eq_C_of_natDegree_le_zero ((le_max_right _ _).trans_eq active)
  have hunit : ¬ IsUnit M.E := fun h => (Nat.ne_of_gt positive) (natDegree_eq_zero_of_isUnit h)
  have first_nonzero : a₀ ≠ 0 := by
    intro ha
    have hc := M.first_amplitude_unit
    rw [h₀, ha, map_zero] at hc
    exact hunit (isCoprime_zero_left.mp hc)
  refine ⟨⟨a₀, a₁, h₀, h₁, first_nonzero, ?_⟩⟩
  intro γ hγ hzero
  have hc := (F.mark γ hγ).pole_unit
  have ha : M.amplitude γ = 0 := by
    unfold ModelAt.amplitude
    rw [h₀, h₁, ← map_mul, ← map_add, hzero, map_zero]
  rw [ha] at hc
  exact hunit (isCoprime_zero_left.mp hc)

theorem Coordinate.denominator_mul_slope {cap : ℕ} {u : Words} {del : Finset I}
    {M : ModelAt cap u del} {Γ : Finset K} (D : Coordinate M Γ) {γ : K} (hγ : γ ∈ Γ) :
    D.denominator γ * D.slope γ = -M.label γ := by
  have hden : D.denominator γ ≠ 0 := D.denominator_nonzero γ hγ
  unfold Coordinate.slope
  rw [mul_comm, div_mul_cancel₀ _ hden]

theorem Coordinate.slope_injective {cap : ℕ} {u : Words} {del : Finset I}
    {M : ModelAt cap u del} {Γ : Finset K} (D : Coordinate M Γ) :
    Set.InjOn D.slope (Γ : Set K) := by
  intro γ₀ h₀ γ₁ h₁ heq
  have h := (div_eq_div_iff (D.denominator_nonzero γ₀ h₀)
    (D.denominator_nonzero γ₁ h₁)).mp heq
  have labels : M.label γ₀ = M.label γ₁ := by
    apply mul_left_cancel₀ D.first_nonzero
    linear_combination -h
  exact sub_left_inj.mp labels

theorem Coordinate.has_nonzero {cap : ℕ} {u : Words} {del : Finset I}
    {M : ModelAt cap u del} {Γ : Finset K} (D : Coordinate M Γ) (many : 1 < Γ.card) :
    ∃ γ ∈ Γ, D.slope γ ≠ 0 := by
  by_contra! hz
  apply (not_le_of_gt many)
  apply Finset.card_le_one_iff.mpr
  intro a b ha hb
  exact D.slope_injective ha hb (by rw [hz _ ha, hz _ hb])

theorem Coordinate.residue {cap : ℕ} {u : Words} {del : Finset I}
    {M : ModelAt cap u del} {Γ : Finset K} (D : Coordinate M Γ)
    (F : FamilyAt 179876 M Γ) (factor : M.factor = 1) {γ : K} (hγ : γ ∈ Γ) :
    M.E ∣ F.scalar γ - C (D.slope γ) * M.Q := by
  let B := F.mark γ hγ
  have hden : D.denominator γ ≠ 0 := D.denominator_nonzero γ hγ
  use C ((D.denominator γ)⁻¹) * M.decoder B.bad
  have eq : M.E * M.decoder B.bad - C (M.label γ) * M.Q =
      C (D.denominator γ) * F.scalar γ := by
    simpa only [factor, one_mul, D.amplitude_eq] using B.identity
  have product : C (D.denominator γ) * (F.scalar γ - C (D.slope γ) * M.Q) =
      M.E * M.decoder B.bad := by
    rw [mul_sub, ← eq, ← mul_assoc, ← map_mul, D.denominator_mul_slope hγ, map_neg]
    ring
  calc
    _ = C ((D.denominator γ)⁻¹) *
        (C (D.denominator γ) * (F.scalar γ - C (D.slope γ) * M.Q)) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hden, map_one, one_mul]
    _ = _ := by rw [product]; ring

end H2429ConstantSlopes
