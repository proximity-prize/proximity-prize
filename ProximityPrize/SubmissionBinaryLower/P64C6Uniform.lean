import ProximityPrize.SubmissionBinaryLower.P64C6Bessel

/-!
# Uniform line weights for the positive-bias class

Weights `4h` and spatial coefficient `4*sum(mu)+beta` give an integral
parameter choice. A coarse numerical bound leaves ample room in the ledger.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Uniform

open P64C6Scale

def parameter (h q Q β : ℕ) : ℕ := 8 * h * Q / β + 4 * q * h + 1

lemma parameter_pos (h q Q β : ℕ) : 0 < parameter h q Q β := by
  exact Nat.succ_pos _

lemma parameter_weight (h q Q β : ℕ) : q * (4 * h) < parameter h q Q β := by
  calc q * (4 * h) = 4 * q * h := by ring
    _ ≤ 8 * h * Q / β + 4 * q * h := Nat.le_add_left _ _
    _ < parameter h q Q β := Nat.lt_succ_self _

lemma parameter_above (h q Q β : ℕ) (hβ : 0 < β) : 8 * h * Q < β * parameter h q Q β := by
  have hm := Nat.mod_lt (8 * h * Q) hβ
  calc 8 * h * Q = β * (8 * h * Q / β) + (8 * h * Q) % β := (Nat.div_add_mod _ _).symm
    _ < β * (8 * h * Q / β) + β := Nat.add_lt_add_left hm _
    _ = β * (8 * h * Q / β + 1) := by ring
    _ ≤ β * parameter h q Q β := Nat.mul_le_mul_left β (by unfold parameter; omega)

theorem leading_positive {ι : Type*} [Fintype ι] (h q d Q β : ℕ) (μ : ι → ℕ)
    (hh : 0 < h) (hβ : 0 < β)
    (hQ : (Q : ℤ) = ∑ i, ((d : ℤ) - q * μ i)) :
    (∑ i, quadraticCost q d (parameter h q Q β) (4 * h) (μ i)) <
      6 * (h : ℤ) * (4 * (∑ i, μ i) + β) * parameter h q Q β := by
  let E := parameter h q Q β
  have heq : ∀ i, quadraticCost q d E (4 * h) (μ i) =
      24 * (h : ℤ) * E * μ i + 48 * (h : ℤ) ^ 2 * ((d : ℤ) - q * μ i) := by
    intro i
    unfold quadraticCost
    push_cast
    ring
  change (∑ i, quadraticCost q d E (4 * h) (μ i)) < _
  rw [Finset.sum_congr rfl (fun i _ => heq i), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← hQ]
  have hp : 8 * (h : ℤ) * Q < β * E := by exact_mod_cast parameter_above h q Q β hβ
  have hmul := mul_lt_mul_of_pos_left hp (show 0 < 6 * (h : ℤ) by positivity)
  push_cast
  nlinarith

/-- The retained slopes fit a `16*n*d` charge at the protected radius. -/
theorem retained_numerical (h q d Q β n N c : ℕ)
    (hh : 0 < h) (hβ : 1000 * h ≤ β) (hd : 1 ≤ d) (hqh : q * h ≤ d)
    (hQ : Q ≤ n * d) (hn : 625 ≤ n) (hN : N ≤ 500000)
    (hc : c * β ≤ h * (2 * N) * parameter h q Q β) : c ≤ 16 * n * d := by
  let k := 8 * h * Q / β
  let E := parameter h q Q β
  have hk : 1000 * k ≤ 8 * Q := by
    apply le_of_mul_le_mul_left (a := h) ?_ hh
    calc h * (1000 * k) = (1000 * h) * k := by ring
      _ ≤ β * k := Nat.mul_le_mul_right k hβ
      _ ≤ 8 * h * Q := Nat.mul_div_le _ _
      _ = h * (8 * Q) := by ring
  have hE : 1000 * E ≤ 8 * Q + 1000 * (4 * q * h + 1) := by
    change 1000 * (k + 4 * q * h + 1) ≤ _
    omega
  have hcard : 1000 * c ≤ 2 * N * E := by
    apply le_of_mul_le_mul_left (a := h) ?_ hh
    calc h * (1000 * c) = c * (1000 * h) := by ring
      _ ≤ c * β := Nat.mul_le_mul_left c hβ
      _ ≤ h * (2 * N) * E := hc
      _ = h * (2 * N * E) := by ring
  have hinside : 8 * Q + 1000 * (4 * q * h + 1) ≤ 16 * n * d := by
    have h1 := Nat.mul_le_mul_left 8 hQ
    have h2 : 1000 * (4 * q * h + 1) ≤ 5000 * d := by nlinarith
    have h3 : 5000 * d ≤ 8 * n * d := Nat.mul_le_mul_right d (by omega)
    nlinarith
  have htotal : 1000000 * c ≤ 1000000 * (16 * n * d) := by
    calc 1000000 * c = 1000 * (1000 * c) := by ring
      _ ≤ 1000 * (2 * N * E) := Nat.mul_le_mul_left 1000 hcard
      _ = (2 * N) * (1000 * E) := by ring
      _ ≤ (2 * N) * (8 * Q + 1000 * (4 * q * h + 1)) := Nat.mul_le_mul_left _ hE
      _ ≤ _ := Nat.mul_le_mul (by omega) hinside
  exact le_of_mul_le_mul_left htotal (by norm_num)

end P64C6Uniform
end ProximityPrize.SubmissionBinaryLower
