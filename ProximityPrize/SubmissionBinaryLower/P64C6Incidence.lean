import ProximityPrize.SubmissionBinaryLower.P64C6Retained
import ProximityPrize.SubmissionBinaryLower.P64Incidence

/-!
# Missing agreement positions for weighted polynomial lines
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Incidence

open Polynomial P64Found P64LineOrder P64Incidence P64C6Weights P64C6Finite
  BCHKSSubstitutionVanish

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

lemma lineEval_degree (R : Tri) (x : F) (y : F[X]) (q d : ℕ)
    (hR : WtLE 0 q 1 d R) (hy : y.natDegree ≤ q) : (lineEval R x y).natDegree ≤ d := by
  rw [lineEval_eq_coeff]
  exact coefficient_parameter_degree _ q d (lineShift_weight R x y q d hR hy) 0 0

theorem card_missing_le (R : Tri) (hR : R ≠ 0) (q d n : ℕ) (hw : WtLE 0 q 1 d R)
    (hn : Fintype.card ι ≤ n) (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ i, (y i).natDegree ≤ q)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hmatch : ∀ z ∈ S, ∀ i ∈ A z, (P z).eval (ω i) = (y i).eval z) :
    (S.filter fun z => ¬ A z ⊆ lam ω y R).card ≤ n * d := by
  classical
  have hsum := sum_card_sdiff_le_of_degree ω y R hR d
    (fun i => lineEval_degree R (ω i) (y i) q d hw (hy i)) S P A hcurve hmatch
  have hcard : (S.filter fun z => ¬ A z ⊆ lam ω y R).card ≤
      ∑ z ∈ S, (A z \ lam ω y R).card := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : A z ⊆ lam ω y R
    · simp [hz]
    · have hne : (A z \ lam ω y R).Nonempty := Finset.sdiff_nonempty.mpr hz
      simpa [hz] using (Finset.card_pos.mpr hne : 0 < (A z \ lam ω y R).card)
  have hlines : (Finset.univ \ lam ω y R).card ≤ n := (Finset.card_le_univ _).trans hn
  exact hcard.trans (hsum.trans (Nat.mul_le_mul_right d hlines))

end P64C6Incidence
end ProximityPrize.SubmissionBinaryLower
