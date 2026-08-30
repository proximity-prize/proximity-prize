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
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:CharP K 2130706433:=by
 change CharP KoalaBear.Ext6 2130706433
 exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
private theorem rank_le_small_sum
   (D L s m:ℕ) (hm:1 ≤ m)
   (u0 u1:I → K) (F:P4) (hF:Irreducible F)
   (hdiv:∀ v:ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1,
     F ∣ reconstruct K D 131071 L s v.1)
   (hpos:0 < F.degreeOf (2:Fin 4))
   (hlt:F.degreeOf (2:Fin 4) < 2130706433)
   (hhalf:s < 2 * F.degreeOf (2:Fin 4))
   (Dcap Lcap qcap J:ℕ)
   (hD:D - wt (contactWeights 131071) F ≤ Dcap)
   (hL:L - wt residualTotalWeights F ≤ Lcap)
   (hq:s - wt residualSWeights F ≤ qcap)
   (hJ:Dcap ≤ 131071 * J) :
   Module.finrank K
       (ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1) ≤
     ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range (qcap + 1),
       (Lcap + 1 - j - r) *
         min 131074 (Dcap - 131071 * j - 131070 * r):=by
 have hzero:∀
     (v:ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1) (P:P4),
     reconstruct K D 131071 L s v.1 = F * P →
     P ∈ globalCoefficientBox K
       (D - wt (contactWeights 131071) F - 131074) 131071
       (L - wt residualTotalWeights F) (s - wt residualSWeights F) →
     P = 0:=by
   intro v P hprod hprefix
   exact LocatorIrreducibleContact.irreducible_half_slope_quotient_eq_zero_of_mem_prefix
     D 131071 L s m 131074 2130706433 IRSProfile.domain u0 u1
     F hF hdiv hpos hlt hhalf hm
     (by norm_num [I, IRSProfile.Index]) v P hprod hprefix
 have h:=LocatorMultiSlopeQuotient.whole_kernel_finrank_le_small_sum
   D 131071 L s m 131074 IRSProfile.domain u0 u1
   F hF.ne_zero hdiv hzero Dcap Lcap qcap J hD hL hq hJ
 simpa only [show 131071 - 1 = 131070 by decide] using h
private theorem full_C_factor_ys_lt
   (u0 u1:I → K) (F:P4) (hF:Irreducible F)
   (hdiv:∀ v:CKernel u0 u1,
     F ∣ reconstruct K 8551321 131071 100000 13 v.1)
   (r y Dcap Lcap qcap J upper:ℕ)
   (hR:F.degreeOf (2:Fin 4) = r) (hr7:7 ≤ r) (hr13:r ≤ 13)
   (hDcap:8551321 - (131071 * y - r) = Dcap)
   (hLcap:100000 - y = Lcap) (hqcap:13 - r = qcap)
   (hJ:Dcap ≤ 131071 * J)
   (hsum:(∑ j ∈ Finset.range J, ∑ q ∈ Finset.range (qcap + 1),
     (Lcap + 1 - j - q) * min 131074
       (Dcap - 131071 * j - 131070 * q)) = upper)
   (hlt:upper < 145020357300):wt residualYSWeights F < y:=by
 by_contra hnot
 have hYS:y ≤ wt residualYSWeights F:=by omega
 have hRwt:wt residualSWeights F = r :=
   (LocatorContact.slope_weight_eq_degreeR F).trans hR
 have hweighted:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
 have hc:131071 * y - r ≤ wt (contactWeights 131071) F:=by omega
 have ht:y ≤ wt residualTotalWeights F :=
   hYS.trans (residual_weight_nested F).2
 have hD:8551321 - wt (contactWeights 131071) F ≤ Dcap:=by omega
 have hL:100000 - wt residualTotalWeights F ≤ Lcap:=by omega
 have hq:13 - wt residualSWeights F ≤ qcap:=by omega
 have hupper:=rank_le_small_sum 8551321 100000 13 47 (by decide) u0 u1 F hF hdiv
   (by rw [hR]; omega) (by rw [hR]; omega) (by rw [hR]; omega)
   Dcap Lcap qcap J hD hL hq hJ
 rw [hsum] at hupper
 change Module.finrank K (CKernel u0 u1) ≤ upper at hupper
 have hlower:=constraintKernel_finrank_lower_bound (K:=K)
   8551321 131071 100000 13 47 IRSProfile.domain u0 u1
 simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
   LocatorArithmetic.kernelC_nullity] at hlower
 change 145020357300 ≤ Module.finrank K (CKernel u0 u1) at hlower
 omega
theorem full_C_factor_r7_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
   (hdiv:∀ v:CKernel u0 u1, F ∣ reconstruct K 8551321 131071 100000 13 v.1)
   (hR:F.degreeOf (2:Fin 4) = 7):wt residualYSWeights F ≤ 61:=by
 have h:=full_C_factor_ys_lt u0 u1 F hF hdiv 7 62 424926 99938 6 4
   91273059412 hR (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) (by decide)
 omega
theorem full_C_factor_r8_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
   (hdiv:∀ v:CKernel u0 u1, F ∣ reconstruct K 8551321 131071 100000 13 v.1)
   (hR:F.degreeOf (2:Fin 4) = 8):wt residualYSWeights F ≤ 61:=by
 have h:=full_C_factor_ys_lt u0 u1 F hF hdiv 8 62 424927 99938 5 4
   91273459156 hR (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) (by decide)
 omega
theorem full_C_factor_r9_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
   (hdiv:∀ v:CKernel u0 u1, F ∣ reconstruct K 8551321 131071 100000 13 v.1)
   (hR:F.degreeOf (2:Fin 4) = 9):wt residualYSWeights F ≤ 61:=by
 have h:=full_C_factor_ys_lt u0 u1 F hF hdiv 9 62 424928 99938 4 4
   91273858900 hR (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) (by decide)
 omega
theorem full_C_factor_r10_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
   (hdiv:∀ v:CKernel u0 u1, F ∣ reconstruct K 8551321 131071 100000 13 v.1)
   (hR:F.degreeOf (2:Fin 4) = 10):wt residualYSWeights F ≤ 60:=by
 have h:=full_C_factor_ys_lt u0 u1 F hF hdiv 10 61 556000 99939 3 5
   143671614440 hR (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) (by decide)
 omega
theorem full_C_factor_r11_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
   (hdiv:∀ v:CKernel u0 u1, F ∣ reconstruct K 8551321 131071 100000 13 v.1)
   (hR:F.degreeOf (2:Fin 4) = 11):wt residualYSWeights F ≤ 60:=by
 have h:=full_C_factor_ys_lt u0 u1 F hF hdiv 11 61 556001 99939 2 5
   127402901926 hR (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) (by decide)
 omega
theorem full_C_factor_r12_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
   (hdiv:∀ v:CKernel u0 u1, F ∣ reconstruct K 8551321 131071 100000 13 v.1)
   (hR:F.degreeOf (2:Fin 4) = 12):wt residualYSWeights F ≤ 59:=by
 have h:=full_C_factor_ys_lt u0 u1 F hF hdiv 12 60 687073 99940 1 6
   124234018258 hR (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) (by decide)
 omega
theorem full_C_factor_r13_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
   (hdiv:∀ v:CKernel u0 u1, F ∣ reconstruct K 8551321 131071 100000 13 v.1)
   (hR:F.degreeOf (2:Fin 4) = 13):wt residualYSWeights F ≤ 54:=by
 have h:=full_C_factor_ys_lt u0 u1 F hF hdiv 13 55 1342429 99945 0 11
   134167191694 hR (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) (by decide)
 omega
end
end ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
