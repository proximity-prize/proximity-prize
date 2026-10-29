import ProximityPrize.SubmissionBinaryLower.P64C6Scale

/-!
# An integral weighted order bound

Clearing denominators in the line weights and forced orders turns the final
comparison into a finite integer contradiction. No analytic limit is needed.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Bessel

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6Finite P64C6Scale
  BCHKSSubstitutionVanish

lemma scaled_forcing (n b : ℤ) (C T a ρ : ℕ) (hn : 0 ≤ n) (hb : 0 < b)
    (hC : 0 < C) (hT : 0 < T) (ha : 2 * (a : ℤ) * n ≤ C * b) (hρ : ρ < T * a) :
    2 * (ρ : ℤ) * n < T * C * b := by
  by_cases hn0 : n = 0
  · rw [hn0, mul_zero]
    positivity
  have hn' : 0 < n := by omega
  have hρ' : (ρ : ℤ) < T * a := by exact_mod_cast hρ
  have hm := mul_lt_mul_of_pos_right hρ' (show 0 < 2 * n by positivity)
  have hl := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg T)
  nlinarith

variable {F ι : Type*} [Field F] [Fintype ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

noncomputable def normalDefect (R : Tri) (ω : ι ↪ F) (y : ι → F[X])
    (A : Finset ι) (w D : ℕ) : ℤ :=
  (w : ℤ) - D - ∑ i ∈ A, ((lineOrd R (ω i) (y i) - 1 : ℕ) : ℤ)

def bias (σ : ι → ℕ) (A : Finset ι) (U : ℕ) : ℤ := (∑ i ∈ A, (σ i : ℤ)) - U

/-- Integer weights whose order slopes fit the biases have bounded total weight. -/
theorem weighted_orders_le (R : Tri) (hirr : Irreducible R)
    (D w q d U E C : ℕ) (hRw : wd R D ≤ w) (hRyz : WtLE 0 q 1 d R)
    (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ i, (y i).natDegree ≤ q) (σ : ι → ℕ)
    (hU : 0 < U) (hE : 0 < E) (hC : 0 < C) (hσ : ∀ i, q * σ i < E)
    (hlead : (∑ i, quadraticCost q d E (σ i) (lineOrd R (ω i) (y i))) <
      6 * (R.natDegree : ℤ) * U * E)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι) (a : F → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ D)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hμ : ∀ z ∈ S, ∀ i ∈ A z, 1 ≤ lineOrd R (ω i) (y i))
    (hmatch : ∀ z ∈ S, ∀ i ∈ A z, (P z).eval (ω i) = (y i).eval z)
    (hb : ∀ z ∈ S, 0 < bias σ (A z) U)
    (hslope : ∀ z ∈ S, 2 * (a z : ℤ) * normalDefect R ω y (A z) w D ≤
      C * bias σ (A z) U) :
    ∑ z ∈ S, a z ≤ R.natDegree * C * E := by
  classical
  let μ : ι → ℕ := fun i => lineOrd R (ω i) (y i)
  have hqC : ∀ i, q * (C * σ i) < C * E := by
    intro i
    simpa [Nat.mul_left_comm] using Nat.mul_lt_mul_of_pos_left (hσ i) hC
  have hscaled : (∑ i, quadraticCost q d (C * E) (C * σ i) (μ i)) <
      6 * (R.natDegree : ℤ) * (C * U) * (C * E) := by
    have heq : ∀ i, quadraticCost q d (C * E) (C * σ i) (μ i) =
        (C : ℤ) ^ 2 * quadraticCost q d E (σ i) (μ i) := by
      intro i
      unfold quadraticCost
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun i _ => heq i), ← Finset.mul_sum]
    have hh := mul_lt_mul_of_pos_left hlead (show 0 < (C : ℤ) ^ 2 by positivity)
    convert hh using 1 <;> push_cast <;> ring
  let B := (R.natDegree - 1) * d
  obtain ⟨T, hTB, hT, hde, hdim⟩ := exists_dimension_scale D q d R.natDegree
    (C * U) (C * E) (B + 1) (fun i => C * σ i) μ
    (Nat.mul_pos hC hU) (Nat.mul_pos hC hE) hqC hscaled
  let m := T * ∑ z ∈ S, a z
  have hN : ∀ z ∈ S, 0 ≤ normalDefect R ω y (A z) w D := by
    intro z hz
    exact normal_defect_nonneg R (P z) z D w hRw (hP z hz) (hderiv z hz) ω y (A z) μ
      (fun i _ => ordGE_lineOrd R (ω i) (y i)) (hmatch z hz)
  have hc := forced_orders_of_dimension R hirr D w (T * (C * U)) q (T * (C * E)) d m
    hRw hRyz hde ω y hy (fun i => T * (C * σ i)) hdim S P A (fun z => T * a z)
    hP hcurve hderiv (fun z hz => ?_) hμ hmatch (fun z hz ρ hρ => ?_)
  · rw [← Finset.mul_sum] at hc
    change T * (∑ z ∈ S, a z) ≤ B + R.natDegree * (T * (C * E)) at hc
    rw [show R.natDegree * (T * (C * E)) = T * (R.natDegree * C * E) by ring] at hc
    by_contra hn
    have hstep : R.natDegree * C * E + 1 ≤ ∑ z ∈ S, a z := by omega
    have hmul := Nat.mul_le_mul_left T hstep
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  · have hsingle : a z ≤ ∑ z ∈ S, a z := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hz
    have hh := Nat.mul_le_mul_left T hsingle
    dsimp [m]
    omega
  · have heq : (∑ i ∈ A z, ((T * (C * σ i) : ℕ) : ℤ)) - (T * (C * U) : ℕ) =
        (T : ℤ) * C * bias σ (A z) U := by
      unfold bias
      simp only [Nat.cast_mul, ← Finset.mul_sum]
      ring
    rw [heq]
    exact scaled_forcing (normalDefect R ω y (A z) w D) (bias σ (A z) U)
      C T (a z) ρ (hN z hz) (hb z hz) hC hT (hslope z hz) hρ

end P64C6Bessel
end ProximityPrize.SubmissionBinaryLower
