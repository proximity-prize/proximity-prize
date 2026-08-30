import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.LocatorIrreducibleContact
import ProximityPrize.SubmissionLower.LocatorMultiSlopeQuotient
import ProximityPrize.SubmissionLower.LocatorSquareWitness

namespace ProximityPrize.SubmissionLower.LocatorIrreducibleCaps

open scoped BigOperators
open ProximityPrize.Benchmark
open RCN081 RCN100 RCN130 RCN156 RCN180 RCN234
open LocatorCaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:CharP K 2130706433:=by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

theorem r10_ys_collar_sum:
    (∑ j∈Finset.range 49,∑ r∈Finset.range 13,
      (47940-j-r)*min 131074 (6357391-131071*j-131070*r))=
        3470093313232:=by decide

theorem r11_ys_collar_sum:
    (∑ j∈Finset.range 53,∑ r∈Finset.range 12,
      (138108-j-r)*min 131074 (6881676-131071*j-131070*r))=
        10208387483272:=by decide

theorem r12_ys_collar_sum:
    (∑ j∈Finset.range 60,∑ r∈Finset.range 11,
      (94950-j-r)*min 131074 (7769867-131071*j-131070*r))=
        7428457357739:=by decide

theorem r13_ys_collar_sum:
    (∑ j∈Finset.range 64,∑ r∈Finset.range 10,
      (94954-j-r)*min 131074 (8294152-131071*j-131070*r))=
        7313175542305:=by decide

theorem total_r9_ys60_collar_sum:
    (∑ j∈Finset.range 107,∑ r∈Finset.range 29,
      (1253-j-r)*min 131074 (13970109-131071*j-131070*r))=
        420054319213:=by decide

theorem total_r10_ys40_collar_sum:
    (∑ j∈Finset.range 127,∑ r∈Finset.range 28,
      (1099-j-r)*min 131074 (16591530-131071*j-131070*r))=
        427372930614:=by decide

theorem total_r11_ys36_collar_sum:
    (∑ j∈Finset.range 131,∑ r∈Finset.range 27,
      (1098-j-r)*min 131074 (17115815-131071*j-131070*r))=
        427351775616:=by decide

theorem total_r12_ys32_collar_sum:
    (∑ j∈Finset.range 135,∑ r∈Finset.range 26,
      (1100-j-r)*min 131074 (17640100-131071*j-131070*r))=
        427365672162:=by decide

theorem total_r13_ys27_collar_sum:
    (∑ j∈Finset.range 140,∑ r∈Finset.range 25,
      (1097-j-r)*min 131074 (18295456-131071*j-131070*r))=
        427235213050:=by decide

private theorem rank_le_small_sum
    (D L s m:ℕ) (hm:1≤m)
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1,
      F∣reconstruct K D 131071 L s v.1)
    (hpos:0<F.degreeOf (2:Fin 4))
    (hlt:F.degreeOf (2:Fin 4)<2130706433)
    (hhalf:s<2*F.degreeOf (2:Fin 4))
    (Dcap Lcap qcap J:ℕ)
    (hD:D - wt (contactWeights 131071) F≤Dcap)
    (hL:L - wt residualTotalWeights F≤Lcap)
    (hq:s - wt residualSWeights F≤qcap)
    (hJ:Dcap≤131071*J):
    Module.finrank K
        (ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1)≤
      ∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
        (Lcap+1 - j - r)*
          min 131074 (Dcap - 131071*j - 131070*r):=by
  have hzero:∀
      (v:ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1) (P:P4),
      reconstruct K D 131071 L s v.1=F*P →
      P∈globalCoefficientBox K
        (D - wt (contactWeights 131071) F - 131074) 131071
        (L - wt residualTotalWeights F) (s - wt residualSWeights F) →
      P=0:=by
    intro v P hprod hprefix
    exact LocatorIrreducibleContact.irreducible_half_slope_quotient_eq_zero_of_mem_prefix
      D 131071 L s m 131074 2130706433 IRSProfile.domain u0 u1
      F hF hdiv hpos hlt hhalf hm
      (by norm_num [I,IRSProfile.Index]) v P hprod hprefix
  have h:=LocatorMultiSlopeQuotient.whole_kernel_finrank_le_small_sum
    D 131071 L s m 131074 IRSProfile.domain u0 u1
    F hF.ne_zero hdiv hzero Dcap Lcap qcap J hD hL hq hJ
  simpa only [show 131071 - 1=131070 by decide] using h

theorem full_R10_r10_factor_ys_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:R10Kernel u0 u1,
      F∣reconstruct K 13828428 131071 47996 22 v.1)
    (hR:F.degreeOf (2:Fin 4)=10):wt residualYSWeights F≤56:=by
  apply LocatorSquareWitness.factor_ys_le_of_square_collar
    13828428 131071 47996 22 76 131074 2130706433 10 56 105
    6357391 47939 12 49 IRSProfile.domain u0 u1 F hF hdiv hR
    (by decide) (by decide) (by decide) (by decide)
    (by norm_num [I,IRSProfile.Index])
    (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro Q hQ hbox
    have hc:=((mem_flagGlobalCoefficientBox_iff Q 13828428 131071 47996 22
      (by decide)).mp hbox).2.2
    have hs:=((mem_flagGlobalCoefficientBox_iff Q 13828428 131071 47996 22
      (by decide)).mp hbox).2.1
    have hy:=residualYS_mul_le_contact_add_slope Q 131071 (by decide)
    omega
  · rw [show 12+1=13 by decide,show 47939+1=47940 by decide,
      r10_ys_collar_sum,
      show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      LocatorArithmetic.kernelR10_nullity]
    decide

theorem full_R11_r11_factor_ys_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:R11Kernel u0 u1,
      F∣reconstruct K 13828428 131071 138160 22 v.1)
    (hR:F.degreeOf (2:Fin 4)=11):wt residualYSWeights F≤52:=by
  apply LocatorSquareWitness.factor_ys_le_of_square_collar
    13828428 131071 138160 22 76 131074 2130706433 11 52 105
    6881676 138107 11 53 IRSProfile.domain u0 u1 F hF hdiv hR
    (by decide) (by decide) (by decide) (by decide)
    (by norm_num [I,IRSProfile.Index])
    (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro Q hQ hbox
    have hc:=((mem_flagGlobalCoefficientBox_iff Q 13828428 131071 138160 22
      (by decide)).mp hbox).2.2
    have hs:=((mem_flagGlobalCoefficientBox_iff Q 13828428 131071 138160 22
      (by decide)).mp hbox).2.1
    have hy:=residualYS_mul_le_contact_add_slope Q 131071 (by decide)
    omega
  · rw [show 11+1=12 by decide,show 138107+1=138108 by decide,
      r11_ys_collar_sum,
      show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      LocatorArithmetic.kernelR11_nullity]
    decide

private theorem r1213_factor_ys_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:R1213Kernel u0 u1,
      F∣reconstruct K 14192334 131071 94998 22 v.1)
    (R ycap Dcap Lcap qcap J upper:ℕ)
    (hR:F.degreeOf (2:Fin 4)=R) (hY:ycap≤wt residualYSWeights F)
    (hRpos:0<R) (hRchar:R<2130706433) (hhalf:22<2*R)
    (hDnum:14192334 - (131071*ycap - R)≤Dcap)
    (hLnum:94998 - ycap≤Lcap) (hqnum:22 - R≤qcap)
    (hJnum:Dcap≤131071*J)
    (hsum:(∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
      (Lcap+1-j-r)*min 131074 (Dcap-131071*j-131070*r))=upper)
    (hlt:upper<7428458607485):False:=by
  have hRwt:wt residualSWeights F=R:=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hm:=Nat.mul_le_mul_left 131071 hY
  have hc:131071*ycap - R≤wt (contactWeights 131071) F:=by omega
  have ht:=hY.trans (residual_weight_nested F).2
  have hD:14192334 - wt (contactWeights 131071) F≤Dcap:=
    (Nat.sub_le_sub_left hc _).trans hDnum
  have hL:94998 - wt residualTotalWeights F≤Lcap:=
    (Nat.sub_le_sub_left ht _).trans hLnum
  have hq:22 - wt residualSWeights F≤qcap:=by omega
  have hu:=rank_le_small_sum 14192334 94998 22 78 (by decide)
    u0 u1 F hF hdiv
    (by rw [hR]; exact hRpos) (by rw [hR]; exact hRchar)
    (by rw [hR]; exact hhalf)
    Dcap Lcap qcap J hD hL hq hJnum
  rw [hsum] at hu
  have hl:=constraintKernel_finrank_lower_bound (K:=K)
    14192334 131071 94998 22 78 IRSProfile.domain u0 u1
  simp only [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
    LocatorArithmetic.kernelR1213_nullity] at hl
  omega

theorem full_R1213_r12_factor_ys_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:R1213Kernel u0 u1,
      F∣reconstruct K 14192334 131071 94998 22 v.1)
    (hR:F.degreeOf (2:Fin 4)=12):wt residualYSWeights F≤48:=by
  by_contra h
  exact r1213_factor_ys_le u0 u1 F hF hdiv 12 49
    7769867 94949 10 60 7428457357739 hR (by omega)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    r12_ys_collar_sum (by decide)

theorem full_R1213_r13_factor_ys_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:R1213Kernel u0 u1,
      F∣reconstruct K 14192334 131071 94998 22 v.1)
    (hR:F.degreeOf (2:Fin 4)=13):wt residualYSWeights F≤44:=by
  by_contra h
  exact r1213_factor_ys_le u0 u1 F hF hdiv 13 45
    8294152 94953 9 64 7313175542305 hR (by omega)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    r13_ys_collar_sum (by decide)

private theorem total_factor_total_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:TotalKernel u0 u1,
      F∣reconstruct K 21834360 131071 2505 37 v.1)
    (R yLower cap Dcap Lcap qcap J upper:ℕ)
    (hR:F.degreeOf (2:Fin 4)=R)
    (hY:yLower≤wt residualYSWeights F)
    (hRpos:0<R) (hRchar:R<2130706433)
    (hsum:(∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
      (Lcap+1-j-r)*min 131074 (Dcap-131071*j-131070*r))=upper)
    (hnum:upper<427501371914)
    (hD:21834360-(131071*yLower-R)≤Dcap)
    (hL:2505-(cap+1)≤Lcap) (hq:37-R≤qcap)
    (hJ:Dcap≤131071*J) (hsq:2505<2*(cap+1)):
    wt residualTotalWeights F≤cap:=by
  apply LocatorSquareWitness.factor_total_le_of_ys_square_collar
    21834360 131071 2505 37 120 131074 2130706433
    R yLower cap Dcap Lcap qcap J IRSProfile.domain u0 u1 F hF hdiv
    hR hY hRpos hRchar (by decide) (by decide) (by decide)
    (by norm_num [I,IRSProfile.Index]) hD hL hq hJ hsq
  rw [hsum,show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
    LocatorArithmetic.kernelTotal_nullity]
  exact hnum

theorem full_Total_r9_ys60_factor_total_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:TotalKernel u0 u1,
      F∣reconstruct K 21834360 131071 2505 37 v.1)
    (hR:F.degreeOf (2:Fin 4)=9)
    (hY:60≤wt residualYSWeights F):
    wt residualTotalWeights F≤1252:=
  total_factor_total_le u0 u1 F hF hdiv 9 60 1252
    13970109 1252 28 107 420054319213 hR hY
    (by decide) (by decide) total_r9_ys60_collar_sum
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem full_Total_r10_ys40_factor_total_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:TotalKernel u0 u1,
      F∣reconstruct K 21834360 131071 2505 37 v.1)
    (hR:F.degreeOf (2:Fin 4)=10)
    (hY:40≤wt residualYSWeights F):
    wt residualTotalWeights F≤1406:=
  total_factor_total_le u0 u1 F hF hdiv 10 40 1406
    16591530 1098 27 127 427372930614 hR hY
    (by decide) (by decide) total_r10_ys40_collar_sum
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem full_Total_r11_ys36_factor_total_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:TotalKernel u0 u1,
      F∣reconstruct K 21834360 131071 2505 37 v.1)
    (hR:F.degreeOf (2:Fin 4)=11)
    (hY:36≤wt residualYSWeights F):
    wt residualTotalWeights F≤1407:=
  total_factor_total_le u0 u1 F hF hdiv 11 36 1407
    17115815 1097 26 131 427351775616 hR hY
    (by decide) (by decide) total_r11_ys36_collar_sum
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem full_Total_r12_ys32_factor_total_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:TotalKernel u0 u1,
      F∣reconstruct K 21834360 131071 2505 37 v.1)
    (hR:F.degreeOf (2:Fin 4)=12)
    (hY:32≤wt residualYSWeights F):
    wt residualTotalWeights F≤1405:=
  total_factor_total_le u0 u1 F hF hdiv 12 32 1405
    17640100 1099 25 135 427365672162 hR hY
    (by decide) (by decide) total_r12_ys32_collar_sum
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem full_Total_r13_ys27_factor_total_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:TotalKernel u0 u1,
      F∣reconstruct K 21834360 131071 2505 37 v.1)
    (hR:F.degreeOf (2:Fin 4)=13)
    (hY:27≤wt residualYSWeights F):
    wt residualTotalWeights F≤1408:=
  total_factor_total_le u0 u1 F hF hdiv 13 27 1408
    18295456 1096 24 140 427235213050 hR hY
    (by decide) (by decide) total_r13_ys27_collar_sum
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end
end ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
