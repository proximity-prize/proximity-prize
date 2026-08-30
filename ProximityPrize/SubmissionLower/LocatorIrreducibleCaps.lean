import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.LocatorIrreducibleContact
import ProximityPrize.SubmissionLower.LocatorMultiSlopeQuotient

/-!
The A70 and auxiliary A63 bounds apply to irreducible
whole-kernel divisors.
They are factorwise bounds, not bounds on a possibly reducible whole gcd.
The actual weighted, total, and R degree differences are retained until
the final finite-coordinate embedding.
-/
namespace ProximityPrize.SubmissionLower.LocatorIrreducibleCaps

open scoped BigOperators
open ProximityPrize.Benchmark
open RCN081 RCN100 RCN130 RCN156 RCN180 RCN234
open LocatorCaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : CharP K 2130706433 := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

theorem r13_collar_sum :
    (∑ j ∈ Finset.range 50, ∑ r ∈ Finset.range 8,
      (99953 - j - r) * min 131074 (6444615 - 131071 * j - 131070 * r)) =
        4785319978824 := by decide

theorem r12_collar_sum :
    (∑ j ∈ Finset.range 45, ∑ r ∈ Finset.range 9,
      (99948 - j - r) * min 131074 (5789259 - 131071 * j - 131070 * r)) =
        4735011312804 := by decide

theorem r11_collar_sum :
    (∑ j ∈ Finset.range 42, ∑ r ∈ Finset.range 10,
      (99945 - j - r) * min 131074 (5396045 - 131071 * j - 131070 * r)) =
        4802627858570 := by decide

theorem r10_collar_sum :
    (∑ j ∈ Finset.range 28, ∑ r ∈ Finset.range 9,
      (99941 - j - r) * min 131074 (3598159 - 131071 * j - 131070 * r)) =
        2764503484284 := by decide

/-- The abstract collar bound is supplied with the proved irreducible
low-prefix exclusion, rather than with an independent rank hypothesis. -/
private theorem rank_le_small_sum
    (D L s m : ℕ) (hm : 1 ≤ m)
    (u0 u1 : I → K) (F : P4) (hF : Irreducible F)
    (hdiv : ∀ v : ConstraintKernel (K := K) D 131071 L s m IRSProfile.domain u0 u1,
      F ∣ reconstruct K D 131071 L s v.1)
    (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hlt : F.degreeOf (2 : Fin 4) < 2130706433)
    (hhalf : s < 2 * F.degreeOf (2 : Fin 4))
    (Dcap Lcap qcap J : ℕ)
    (hD : D - wt (contactWeights 131071) F ≤ Dcap)
    (hL : L - wt residualTotalWeights F ≤ Lcap)
    (hq : s - wt residualSWeights F ≤ qcap)
    (hJ : Dcap ≤ 131071 * J) :
    Module.finrank K
        (ConstraintKernel (K := K) D 131071 L s m IRSProfile.domain u0 u1) ≤
      ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range (qcap + 1),
        (Lcap + 1 - j - r) *
          min 131074 (Dcap - 131071 * j - 131070 * r) := by
  have hzero : ∀
      (v : ConstraintKernel (K := K) D 131071 L s m IRSProfile.domain u0 u1) (P : P4),
      reconstruct K D 131071 L s v.1 = F * P →
      P ∈ globalCoefficientBox K
        (D - wt (contactWeights 131071) F - 131074) 131071
        (L - wt residualTotalWeights F) (s - wt residualSWeights F) →
      P = 0 := by
    intro v P hprod hprefix
    exact LocatorIrreducibleContact.irreducible_half_slope_quotient_eq_zero_of_mem_prefix
      D 131071 L s m 131074 2130706433 IRSProfile.domain u0 u1
      F hF hdiv hpos hlt hhalf hm
      (by norm_num [I, IRSProfile.Index]) v P hprod hprefix
  have h := LocatorMultiSlopeQuotient.whole_kernel_finrank_le_small_sum
    D 131071 L s m 131074 IRSProfile.domain u0 u1
    F hF.ne_zero hdiv hzero Dcap Lcap qcap J hD hL hq hJ
  simpa only [show 131071 - 1 = 131070 by decide] using h

/-- An irreducible R13 factor dividing the entire A70 kernel has YS<=47. -/
theorem full_A_r13_factor_ys_le
    (u0 u1 : I → K) (F : P4) (hF : Irreducible F)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 12736010 131071 100000 20 v.1)
    (hR : F.degreeOf (2 : Fin 4) = 13) :
    wt residualYSWeights F ≤ 47 := by
  by_contra hnot
  have hYS : 48 ≤ wt residualYSWeights F := by omega
  have hRwt : wt residualSWeights F = 13 :=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hweighted := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc : 6291395 ≤ wt (contactWeights 131071) F := by omega
  have ht : 48 ≤ wt residualTotalWeights F :=
    hYS.trans (residual_weight_nested F).2
  have hD : 12736010 - wt (contactWeights 131071) F ≤ 6444615 := by omega
  have hL : 100000 - wt residualTotalWeights F ≤ 99952 := by omega
  have hq : 20 - wt residualSWeights F ≤ 7 := by omega
  have hupper := rank_le_small_sum 12736010 100000 20 70 (by decide) u0 u1 F hF hdiv
    (by rw [hR]; decide) (by rw [hR]; decide) (by rw [hR]; decide)
    6444615 99952 7 50 hD hL hq (by decide)
  simp only [show 7 + 1 = 8 by decide, show 99952 + 1 = 99953 by decide,
    r13_collar_sum] at hupper
  change Module.finrank K (AKernel u0 u1) ≤ 4785319978824 at hupper
  have hlower := constraintKernel_finrank_lower_bound (K := K)
    12736010 131071 100000 20 70 IRSProfile.domain u0 u1
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    LocatorArithmetic.kernelA_nullity] at hlower
  change 4824150093847 ≤ Module.finrank K (AKernel u0 u1) at hlower
  omega

/-- An irreducible R12 factor dividing the entire A70 kernel has YS<=52. -/
theorem full_A_r12_factor_ys_le
    (u0 u1 : I → K) (F : P4) (hF : Irreducible F)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 12736010 131071 100000 20 v.1)
    (hR : F.degreeOf (2 : Fin 4) = 12) :
    wt residualYSWeights F ≤ 52 := by
  by_contra hnot
  have hYS : 53 ≤ wt residualYSWeights F := by omega
  have hRwt : wt residualSWeights F = 12 :=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hweighted := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc : 6946751 ≤ wt (contactWeights 131071) F := by omega
  have ht : 53 ≤ wt residualTotalWeights F :=
    hYS.trans (residual_weight_nested F).2
  have hD : 12736010 - wt (contactWeights 131071) F ≤ 5789259 := by omega
  have hL : 100000 - wt residualTotalWeights F ≤ 99947 := by omega
  have hq : 20 - wt residualSWeights F ≤ 8 := by omega
  have hupper := rank_le_small_sum 12736010 100000 20 70 (by decide) u0 u1 F hF hdiv
    (by rw [hR]; decide) (by rw [hR]; decide) (by rw [hR]; decide)
    5789259 99947 8 45 hD hL hq (by decide)
  simp only [show 8 + 1 = 9 by decide, show 99947 + 1 = 99948 by decide,
    r12_collar_sum] at hupper
  change Module.finrank K (AKernel u0 u1) ≤ 4735011312804 at hupper
  have hlower := constraintKernel_finrank_lower_bound (K := K)
    12736010 131071 100000 20 70 IRSProfile.domain u0 u1
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    LocatorArithmetic.kernelA_nullity] at hlower
  change 4824150093847 ≤ Module.finrank K (AKernel u0 u1) at hlower
  omega

/-- An irreducible R11 factor dividing the entire A70 kernel has YS<=55. -/
theorem full_A_r11_factor_ys_le
    (u0 u1 : I → K) (F : P4) (hF : Irreducible F)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 12736010 131071 100000 20 v.1)
    (hR : F.degreeOf (2 : Fin 4) = 11) :
    wt residualYSWeights F ≤ 55 := by
  by_contra hnot
  have hYS : 56 ≤ wt residualYSWeights F := by omega
  have hRwt : wt residualSWeights F = 11 :=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hweighted := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc : 7339965 ≤ wt (contactWeights 131071) F := by omega
  have ht : 56 ≤ wt residualTotalWeights F :=
    hYS.trans (residual_weight_nested F).2
  have hD : 12736010 - wt (contactWeights 131071) F ≤ 5396045 := by omega
  have hL : 100000 - wt residualTotalWeights F ≤ 99944 := by omega
  have hq : 20 - wt residualSWeights F ≤ 9 := by omega
  have hupper := rank_le_small_sum 12736010 100000 20 70 (by decide) u0 u1 F hF hdiv
    (by rw [hR]; decide) (by rw [hR]; decide) (by rw [hR]; decide)
    5396045 99944 9 42 hD hL hq (by decide)
  simp only [show 9 + 1 = 10 by decide, show 99944 + 1 = 99945 by decide,
    r11_collar_sum] at hupper
  change Module.finrank K (AKernel u0 u1) ≤ 4802627858570 at hupper
  have hlower := constraintKernel_finrank_lower_bound (K := K)
    12736010 131071 100000 20 70 IRSProfile.domain u0 u1
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    LocatorArithmetic.kernelA_nullity] at hlower
  change 4824150093847 ≤ Module.finrank K (AKernel u0 u1) at hlower
  omega

/-- The auxiliary A63 kernel gives the R10 factor bound YS<=59. -/
theorem full_Aux_r10_factor_ys_le
    (u0 u1 : I → K) (F : P4) (hF : Irreducible F)
    (hdiv : ∀ v : AuxKernel u0 u1,
      F ∣ reconstruct K 11462409 131071 100000 18 v.1)
    (hR : F.degreeOf (2 : Fin 4) = 10) :
    wt residualYSWeights F ≤ 59 := by
  by_contra hnot
  have hYS : 60 ≤ wt residualYSWeights F := by omega
  have hRwt : wt residualSWeights F = 10 :=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hweighted := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc : 7864250 ≤ wt (contactWeights 131071) F := by omega
  have ht : 60 ≤ wt residualTotalWeights F :=
    hYS.trans (residual_weight_nested F).2
  have hD : 11462409 - wt (contactWeights 131071) F ≤ 3598159 := by omega
  have hL : 100000 - wt residualTotalWeights F ≤ 99940 := by omega
  have hq : 18 - wt residualSWeights F ≤ 8 := by omega
  have hupper := rank_le_small_sum 11462409 100000 18 63 (by decide) u0 u1 F hF hdiv
    (by rw [hR]; decide) (by rw [hR]; decide) (by rw [hR]; decide)
    3598159 99940 8 28 hD hL hq (by decide)
  simp only [show 8 + 1 = 9 by decide, show 99940 + 1 = 99941 by decide,
    r10_collar_sum] at hupper
  change Module.finrank K (AuxKernel u0 u1) ≤ 2764503484284 at hupper
  have hlower := constraintKernel_finrank_lower_bound (K := K)
    11462409 131071 100000 18 63 IRSProfile.domain u0 u1
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    LocatorArithmetic.kernelAux_nullity] at hlower
  change 2854282575775 ≤ Module.finrank K (AuxKernel u0 u1) at hlower
  omega

end
end ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
