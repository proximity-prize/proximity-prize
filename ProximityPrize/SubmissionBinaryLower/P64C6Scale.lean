import ProximityPrize.SubmissionBinaryLower.P64C6Positive

/-!
# Integer scaling for the auxiliary count

These lemmas separate the leading quadratic term from the finite lower-order
costs. They also allow zero line weights, used for a single-line application.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Scale

open P64C6Boxes P64C6Counts

theorem net_count_le_all (s q d μ e : ℕ) (he : q * s + d ≤ e) :
    6 * ((conditions s q e).card : ℤ) -
      6 * ((conditions (s - μ) q (e - d)).card : ℤ) ≤ netUpper6 s q d μ e := by
  by_cases hμ : μ ≤ s
  · exact net_count_le s q d μ e hμ he
  have hsm : s ≤ μ := by omega
  have hb := net_count_le s q d s e le_rfl he
  have hzero : (conditions (s - μ) q (e - d)).card = 0 := by
    simp [conditions, box, Nat.sub_eq_zero_of_le hsm]
  have hz : (conditions (s - s) q (e - d)).card = 0 := by simp [conditions, box]
  rw [hzero, Nat.cast_zero, mul_zero, sub_zero]
  rw [hz, Nat.cast_zero, mul_zero, sub_zero] at hb
  apply hb.trans
  apply le_of_sub_nonneg
  have hp : (0 : ℤ) ≤ ((μ : ℤ) - s) *
      (6 * s * e + 3 * d * (μ + s) + 3 * q * s * μ + 6 * s) :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hsm)) (by positivity)
  convert hp using 1 <;> unfold netUpper6 <;> ring

def quadraticCost (q d E σ μ : ℕ) : ℤ :=
  6 * μ * σ * E + 3 * ((d : ℤ) - q * μ) * σ ^ 2

def linearCost (q d σ μ : ℕ) : ℕ :=
  6 * μ * σ + 3 * d * σ + 3 * q * σ * μ ^ 2

def constantCost (d μ : ℕ) : ℕ := 3 * d * μ ^ 2

theorem netUpper6_scaled (T q d E σ μ : ℕ) :
    netUpper6 (T * σ) q d μ (T * E) =
      (T : ℤ) ^ 2 * quadraticCost q d E σ μ + T * linearCost q d σ μ + constantCost d μ := by
  unfold netUpper6 quadraticCost linearCost constantCost
  push_cast
  ring

/-- An integral positive leading gap dominates every fixed linear and constant cost. -/
theorem exists_large_scale (A : ℤ) (L B C T₀ : ℕ) (hAL : A < L) :
    ∃ T : ℕ, T₀ ≤ T ∧ 0 < T ∧
      (T : ℤ) ^ 2 * A + T * B + C < (T : ℤ) ^ 2 * L := by
  let T := T₀ + B + C + 1
  have hT : (0 : ℤ) < T := by dsimp [T]; positivity
  have hBC : (B : ℤ) + C < T := by dsimp [T]; push_cast; omega
  have hC : (C : ℤ) ≤ T * C := by
    have hone : (1 : ℤ) ≤ T := by omega
    simpa using mul_le_mul_of_nonneg_right hone (Nat.cast_nonneg C)
  have hlower : (T : ℤ) * B + C < T ^ 2 := by
    have hm := mul_lt_mul_of_pos_left hBC hT
    nlinarith
  have hlead : A + 1 ≤ (L : ℤ) := by omega
  refine ⟨T, by dsimp [T]; omega, by dsimp [T]; omega, ?_⟩
  calc (T : ℤ) ^ 2 * A + T * B + C < T ^ 2 * A + T ^ 2 := by linarith
    _ = T ^ 2 * (A + 1) := by ring
    _ ≤ T ^ 2 * L := mul_le_mul_of_nonneg_left hlead (sq_nonneg _)

/-- A positive leading dimension surplus gives arbitrarily large valid integral scales. -/
theorem exists_dimension_scale {ι : Type*} [Fintype ι]
    (D q d h U E T₀ : ℕ) (σ μ : ι → ℕ) (hU : 0 < U) (hE : 0 < E)
    (hσ : ∀ i, q * σ i < E)
    (hlead : (∑ i, quadraticCost q d E (σ i) (μ i)) < 6 * (h : ℤ) * U * E) :
    ∃ T : ℕ, T₀ ≤ T ∧ 0 < T ∧ d ≤ T * E ∧
      (∑ i, (conditions (T * σ i) q (T * E)).card) <
        (auxiliary D (T * U) q (T * E) h).card +
          ∑ i, (conditions (T * σ i - μ i) q (T * E - d)).card := by
  classical
  let A : ℤ := ∑ i, quadraticCost q d E (σ i) (μ i)
  let L : ℕ := 6 * h * U * E
  let B : ℕ := ∑ i, linearCost q d (σ i) (μ i)
  let C : ℕ := ∑ i, constantCost d (μ i)
  let K : ℕ := 6 * h * h * (D * E + q * U)
  have hAL : A < (L : ℤ) := by simpa [A, L] using hlead
  obtain ⟨T, hT, hTpos, hgap⟩ := exists_large_scale A L (B + K) C
    (T₀ + h * D + q * h + d + 1) hAL
  have hTU : h * D ≤ T * U := by
    have hm := Nat.mul_le_mul_left T (Nat.succ_le_of_lt hU)
    omega
  have hTE : q * h ≤ T * E := by
    have hm := Nat.mul_le_mul_left T (Nat.succ_le_of_lt hE)
    omega
  have hde : d ≤ T * E := by
    have hm := Nat.mul_le_mul_left T (Nat.succ_le_of_lt hE)
    omega
  have he : ∀ i, q * (T * σ i) + d ≤ T * E := by
    intro i
    calc q * (T * σ i) + d ≤ q * (T * σ i) + T := Nat.add_le_add_left (by omega) _
      _ = T * (q * σ i + 1) := by ring
      _ ≤ T * E := Nat.mul_le_mul_left T (Nat.succ_le_of_lt (hσ i))
  have hsum : (∑ i, netUpper6 (T * σ i) q d (μ i) (T * E)) =
      (T : ℤ) ^ 2 * A + T * B + C := by
    simp only [netUpper6_scaled, Finset.sum_add_distrib, ← Finset.mul_sum, A, B, C,
      Nat.cast_sum]
  have hrect : 6 * (h : ℤ) * (T * U - h * D : ℕ) * (T * E - q * h : ℕ) =
      (T : ℤ) ^ 2 * L - T * K + 6 * q * (h : ℤ) ^ 3 * D := by
    rw [Nat.cast_sub hTU, Nat.cast_sub hTE]
    dsimp [L, K]
    push_cast
    ring
  have hnum : (∑ i, netUpper6 (T * σ i) q d (μ i) (T * E)) <
      6 * (h : ℤ) * (T * U - h * D : ℕ) * (T * E - q * h : ℕ) := by
    rw [hsum, hrect]
    have hp : (0 : ℤ) ≤ 6 * q * (h : ℤ) ^ 3 * D := by positivity
    push_cast at hgap
    nlinarith
  refine ⟨T, by omega, hTpos, hde, ?_⟩
  have hn := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    net_count_le_all (T * σ i) q d (μ i) (T * E) (he i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hn
  have hl : (h : ℤ) * (T * U - h * D : ℕ) * (T * E - q * h : ℕ) ≤
      (auxiliary D (T * U) q (T * E) h).card := by
    exact_mod_cast auxiliary_lower D (T * U) q (T * E) h
  have hx : (∑ i, ((conditions (T * σ i) q (T * E)).card : ℤ)) <
      (auxiliary D (T * U) q (T * E) h).card +
        ∑ i, ((conditions (T * σ i - μ i) q (T * E - d)).card : ℤ) := by
    linarith
  exact_mod_cast hx

end P64C6Scale
end ProximityPrize.SubmissionBinaryLower
