import ProximityPrize.SubmissionLower.BCHKSReceivedBivariateSpecialize6400

/-! # Degree of the mapped sealed received interpolator -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem score6400SealedReceivedInterpolator_map_frobenius_degree_lt
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) :
    ((score6400SealedReceivedInterpolator f₀ f₁ z).map
      koalaSexticFrobenius.toRingHom).degree <
        (Fintype.card IRSProfile.Index : WithBot Nat) := by
  have hnat :
      ((score6400SealedReceivedInterpolator f₀ f₁ z).map
        koalaSexticFrobenius.toRingHom).natDegree < 262144 :=
    Polynomial.natDegree_map_le.trans_lt
      (score6400SealedReceivedInterpolator_natDegree_lt f₀ f₁ z)
  have hcard : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  by_cases hzero :
      (score6400SealedReceivedInterpolator f₀ f₁ z).map
        koalaSexticFrobenius.toRingHom = 0
  · rw [hzero]
    exact WithBot.bot_lt_coe _
  · rw [Polynomial.degree_eq_natDegree hzero, hcard]
    exact WithBot.coe_lt_coe.mpr hnat

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
