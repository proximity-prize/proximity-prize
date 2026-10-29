import ProximityPrize.SubmissionBinaryLower.P64C7Step
import ProximityPrize.SubmissionBinaryLower.P64C6Bessel

/-!
# Integral scaling of the residual auxiliary dimension

The local rank bound has an explicit quadratic leading term and a linear
remainder. A positive leading surplus supplies arbitrarily large valid scales.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Scale

open P64C6Boxes

def quadraticCost (h q d μ E σ : ℕ) : ℕ :=
  σ * (h - μ) * E + (d - q * μ) * σ * σ

def linearCost (h q μ ν E σ : ℕ) : ℕ :=
  σ * (h + q * μ * ν + q * μ * μ) + μ * μ * E

theorem upper_scaled (T h q d μ ν E σ : ℕ) :
    P64C7Counts.upper (T * σ) h q d μ ν (T * E) =
      T ^ 2 * quadraticCost h q d μ E σ + T * linearCost h q μ ν E σ := by
  unfold P64C7Counts.upper quadraticCost linearCost
  ring

theorem exists_dimension_scale (D q d h μ ν U E σ T₀ : ℕ)
    (hU : 0 < U) (hE : 0 < E) (hσ : 0 < σ)
    (hlead : quadraticCost h q d μ E σ < h * U * E) :
    ∃ T : ℕ, T₀ ≤ T ∧ 0 < T ∧ μ ≤ T * σ ∧ ν ≤ T * σ ∧
      P64C7Counts.upper (T * σ) h q d μ ν (T * E) <
        (auxiliary D (T * U) q (T * E) h).card := by
  let A := quadraticCost h q d μ E σ
  let B := linearCost h q μ ν E σ
  let L := h * U * E
  let K := h * h * (D * E + q * U)
  have hAL : (A : ℤ) < L := by exact_mod_cast hlead
  obtain ⟨T, hT, hTpos, hgap⟩ := P64C6Scale.exists_large_scale A L (B + K) 0
    (T₀ + h * D + q * h + μ + ν + 1) hAL
  have hTU : h * D ≤ T * U := by
    have hm := Nat.mul_le_mul_left T (Nat.succ_le_of_lt hU)
    omega
  have hTE : q * h ≤ T * E := by
    have hm := Nat.mul_le_mul_left T (Nat.succ_le_of_lt hE)
    omega
  have hTs : T ≤ T * σ := by simpa using Nat.mul_le_mul_left T (Nat.succ_le_of_lt hσ)
  have hrect : (h : ℤ) * (T * U - h * D : ℕ) * (T * E - q * h : ℕ) =
      (T : ℤ) ^ 2 * L - T * K + q * (h : ℤ) ^ 3 * D := by
    rw [Nat.cast_sub hTU, Nat.cast_sub hTE]
    dsimp [L, K]
    push_cast
    ring
  have hnum : (P64C7Counts.upper (T * σ) h q d μ ν (T * E) : ℤ) <
      (h : ℤ) * (T * U - h * D : ℕ) * (T * E - q * h : ℕ) := by
    rw [upper_scaled, hrect]
    have hp : (0 : ℤ) ≤ q * (h : ℤ) ^ 3 * D := by positivity
    push_cast at hgap ⊢
    change (T : ℤ) ^ 2 * A + T * B < _
    nlinarith
  refine ⟨T, by omega, hTpos, by omega, by omega, ?_⟩
  have hl : (h : ℤ) * (T * U - h * D : ℕ) * (T * E - q * h : ℕ) ≤
      (auxiliary D (T * U) q (T * E) h).card := by
    exact_mod_cast auxiliary_lower D (T * U) q (T * E) h
  exact_mod_cast hnum.trans_le hl

end P64C7Scale
end ProximityPrize.SubmissionBinaryLower
