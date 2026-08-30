import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.LocatorIrreducibleContact
import ProximityPrize.SubmissionLower.LocatorMultiSlopeQuotient
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
   (∑ j ∈ Finset.range 6, ∑ r ∈ Finset.range 1,
     (99944 - j - r) * min 131074 (716851 - 131071 * j - 131070 * r)) =
       71644837284 := by decide
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
theorem full_C_r13_factor_ys_le
   (u0 u1 : I → K) (F : P4) (hF : Irreducible F)
   (hdiv : ∀ v : CKernel u0 u1,
     F ∣ reconstruct K 8187885 131071 100000 13 v.1)
   (hR : F.degreeOf (2 : Fin 4) = 13) :
   wt residualYSWeights F ≤ 56 := by
 by_contra hnot
 have hYS : 57 ≤ wt residualYSWeights F := by omega
 have hRwt : wt residualSWeights F = 13 :=
   (LocatorContact.slope_weight_eq_degreeR F).trans hR
 have hweighted := residualYS_mul_le_contact_add_slope F 131071 (by decide)
 have hc : 7471034 ≤ wt (contactWeights 131071) F := by omega
 have ht : 57 ≤ wt residualTotalWeights F :=
   hYS.trans (residual_weight_nested F).2
 have hD : 8187885 - wt (contactWeights 131071) F ≤ 716851 := by omega
 have hL : 100000 - wt residualTotalWeights F ≤ 99943 := by omega
 have hq : 13 - wt residualSWeights F ≤ 0 := by omega
 have hupper := rank_le_small_sum 8187885 100000 13 45 (by decide) u0 u1 F hF hdiv
   (by rw [hR]; decide) (by rw [hR]; decide) (by rw [hR]; decide)
   716851 99943 0 6 hD hL hq (by decide)
 simp only [show 0 + 1 = 1 by decide, show 99943 + 1 = 99944 by decide,
   r13_collar_sum] at hupper
 change Module.finrank K (CKernel u0 u1) ≤ 71644837284 at hupper
 have hlower := constraintKernel_finrank_lower_bound (K := K)
   8187885 131071 100000 13 45 IRSProfile.domain u0 u1
 simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
   LocatorArithmetic.kernelC_nullity] at hlower
 change 76094548201 ≤ Module.finrank K (CKernel u0 u1) at hlower
 omega
end
end ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
