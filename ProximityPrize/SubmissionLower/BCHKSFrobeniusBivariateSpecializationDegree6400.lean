import ProximityPrize.SubmissionLower.BCHKSReceivedBivariateSpecialize6400

/-! # Locator-degree bound after Frobenius bivariate specialization -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem score6400FrobeniusReceivedBivariate_natDegree_lt
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) :
    (score6400FrobeniusReceivedBivariate f₀ f₁).natDegree < 262144 := by
  rw [score6400FrobeniusReceivedBivariate, bchksInterpolationSeal_def]
  have hdegree := algebraLagrangeInterpolate_natDegree_lt_card
    Finset.univ (fun i : IRSProfile.Index ↦ IRSProfile.domain i)
    (score6400FrobeniusReceivedNode f₀ f₁)
    IRSProfile.domain.injective.injOn Finset.univ_nonempty
  have hcard : (Finset.univ : Finset IRSProfile.Index).card = 262144 := by
    norm_num [IRSProfile.Index]
  rw [hcard] at hdegree
  exact hdegree

theorem score6400FrobeniusReceivedBivariate_map_eval_degree_lt
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) :
    ((score6400FrobeniusReceivedBivariate f₀ f₁).map
      (Polynomial.evalRingHom z)).degree <
        (Fintype.card IRSProfile.Index : WithBot Nat) := by
  have hnat :
      ((score6400FrobeniusReceivedBivariate f₀ f₁).map
        (Polynomial.evalRingHom z)).natDegree < 262144 :=
    Polynomial.natDegree_map_le.trans_lt
      (score6400FrobeniusReceivedBivariate_natDegree_lt f₀ f₁)
  have hcard : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  by_cases hzero :
      (score6400FrobeniusReceivedBivariate f₀ f₁).map
        (Polynomial.evalRingHom z) = 0
  · rw [hzero]
    exact WithBot.bot_lt_coe _
  · rw [Polynomial.degree_eq_natDegree hzero, hcard]
    exact WithBot.coe_lt_coe.mpr hnat

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
