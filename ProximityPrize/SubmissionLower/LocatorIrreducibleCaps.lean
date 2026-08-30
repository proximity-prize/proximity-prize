import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.LocatorIrreducibleContact
import ProximityPrize.SubmissionLower.LocatorMultiSlopeQuotient
import ProximityPrize.SubmissionLower.LocatorSquareWitness
namespace ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
open scoped BigOperators
open ProximityPrize.Benchmark
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234
open LocatorCaps
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:CharP K 2130706433:=by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem aux11_r11_sum:
    (∑ j∈Finset.range 49,∑ r∈Finset.range 11,
      (98827-j-r)*min 131074 (6386699-131071*j-131070*r))=6229017484096:=by decide
theorem aux23_r12_sum:
    (∑ j∈Finset.range 64,∑ r∈Finset.range 12,
      (70500-j-r)*min 131074 (8315726-131071*j-131070*r))=6422294363590:=by decide
theorem aux23_r13_sum:
    (∑ j∈Finset.range 68,∑ r∈Finset.range 11,
      (70504-j-r)*min 131074 (8840011-131071*j-131070*r))=6344499821341:=by decide
theorem thin_r10_sum:
    (∑ j∈Finset.range 56,∑ r∈Finset.range 15,
      (62260-j-r)*min 131074 (7267156-131071*j-131070*r))=5927179461470:=by decide
theorem trade_r10_sum:
    (∑ j∈Finset.range 70,∑ r∈Finset.range 18,
      (1374-j-r)*min 131074 (9115993-131071*j-131070*r))=192389842401:=by decide
theorem trade_r11_sum:
    (∑ j∈Finset.range 73,∑ r∈Finset.range 17,
      (1374-j-r)*min 131074 (9509207-131071*j-131070*r))=191933726162:=by decide
theorem trade_r12_sum:
    (∑ j∈Finset.range 77,∑ r∈Finset.range 16,
      (1370-j-r)*min 131074 (10033492-131071*j-131070*r))=192399490384:=by decide
theorem trade_r13_sum:
    (∑ j∈Finset.range 80,∑ r∈Finset.range 15,
      (1374-j-r)*min 131074 (10426706-131071*j-131070*r))=189906004040:=by decide
private theorem rank_le_small_sum
    (D L s m:ℕ) (hm:1≤m) (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1,
      F∣reconstruct K D 131071 L s v.1)
    (hpos:0<F.degreeOf (2:Fin 4)) (hlt:F.degreeOf (2:Fin 4)<2130706433)
    (hhalf:s<2*F.degreeOf (2:Fin 4))
    (Dcap Lcap qcap J:ℕ) (hD:D-wt (contactWeights 131071) F≤Dcap)
    (hL:L-wt residualTotalWeights F≤Lcap)
    (hq:s-wt residualSWeights F≤qcap) (hJ:Dcap≤131071*J):
    Module.finrank K
        (ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1)≤
      ∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
        (Lcap+1-j-r)*min 131074 (Dcap-131071*j-131070*r):=by
  have hzero:∀ (v:ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1)
      (P:P4),reconstruct K D 131071 L s v.1=F*P →
      P∈globalCoefficientBox K
        (D-wt (contactWeights 131071) F-131074) 131071
        (L-wt residualTotalWeights F) (s-wt residualSWeights F) → P=0:=by
    intro v P hp hP
    exact LocatorIrreducibleContact.irreducible_half_slope_quotient_eq_zero_of_mem_prefix
      D 131071 L s m 131074 2130706433 IRSProfile.domain u0 u1 F hF hdiv
      hpos hlt hhalf hm (by norm_num [I,IRSProfile.Index]) v P hp hP
  simpa only [show 131071-1=131070 by decide] using
    LocatorMultiSlopeQuotient.whole_kernel_finrank_le_small_sum
      D 131071 L s m 131074 IRSProfile.domain u0 u1 F hF.ne_zero hdiv hzero
      Dcap Lcap qcap J hD hL hq hJ
private theorem factor_ys_le
    (D L s m nullity R cap Dcap Lcap qcap J upper:ℕ)
    (hnull:coefficientCount D 131071 L s-
      262144*localRankBound m L s=nullity)
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1,
      F∣reconstruct K D 131071 L s v.1)
    (hR:F.degreeOf (2:Fin 4)=R)
    (hm:1≤m) (hRpos:0<R) (hRchar:R<2130706433) (hhalf:s<2*R)
    (hDnum:D-(131071*(cap+1)-R)≤Dcap)
    (hLnum:L-(cap+1)≤Lcap) (hqnum:s-R≤qcap)
    (hJnum:Dcap≤131071*J)
    (hsum:(∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
      (Lcap+1-j-r)*min 131074 (Dcap-131071*j-131070*r))=upper)
    (hlt:upper<nullity):wt residualYSWeights F≤cap:=by
  by_contra h
  have hY:cap+1≤wt residualYSWeights F:=by omega
  have hS:wt residualSWeights F=R:=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc:131071*(cap+1)-R≤wt (contactWeights 131071) F:=by
    have hm:=Nat.mul_le_mul_left 131071 hY
    omega
  have ht:=hY.trans (residual_weight_nested F).2
  have hu:=rank_le_small_sum D L s m hm u0 u1 F hF hdiv
    (by rw [hR]; exact hRpos) (by rw [hR]; exact hRchar)
    (by rw [hR]; exact hhalf) Dcap Lcap qcap J
    ((Nat.sub_le_sub_left hc D).trans hDnum)
    ((Nat.sub_le_sub_left ht L).trans hLnum) (by rw [hS]; exact hqnum) hJnum
  rw [hsum] at hu
  have hl:=constraintKernel_finrank_lower_bound (K:=K)
    D 131071 L s m IRSProfile.domain u0 u1
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],hnull] at hl
  omega
theorem full_A_r11_factor_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:AuxKernel u0 u1,F∣reconstruct K 13464522 131071 98880 21 v.1)
    (hR:F.degreeOf (2:Fin 4)=11):wt residualYSWeights F≤53:=
  factor_ys_le 13464522 98880 21 74 6230152930364 11 53
    6386699 98826 10 49 6229017484096 LocatorArithmetic.kernelAux_nullity
    u0 u1 F hF hdiv hR (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) aux11_r11_sum (by decide)
theorem full_A_r12_factor_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:Aux23Kernel u0 u1,F∣reconstruct K 14738193 131071 70548 23 v.1)
    (hR:F.degreeOf (2:Fin 4)=12):wt residualYSWeights F≤48:=
  factor_ys_le 14738193 70548 23 81 6523987449670 12 48
    8315726 70499 11 64 6422294363590 LocatorArithmetic.kernelAux23_nullity
    u0 u1 F hF hdiv hR (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) aux23_r12_sum (by decide)
theorem full_A_r13_factor_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:Aux23Kernel u0 u1,F∣reconstruct K 14738193 131071 70548 23 v.1)
    (hR:F.degreeOf (2:Fin 4)=13):wt residualYSWeights F≤44:=
  factor_ys_le 14738193 70548 23 81 6523987449670 13 44
    8840011 70503 10 68 6344499821341 LocatorArithmetic.kernelAux23_nullity
    u0 u1 F hF hdiv hR (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) aux23_r13_sum (by decide)
theorem full_Aux_r10_factor_ys_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:ThinKernel u0 u1,F∣reconstruct K 14738193 131071 62316 24 v.1)
    (hR:F.degreeOf (2:Fin 4)=10):wt residualYSWeights F≤56:=by
  apply LocatorSquareWitness.factor_ys_le_of_square_collar
    14738193 131071 62316 24 81 131074 2130706433 10 56 112
    7267156 62259 14 56 IRSProfile.domain u0 u1 F hF hdiv hR
    (by decide) (by decide) (by decide) (by decide)
    (by norm_num [I,IRSProfile.Index]) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  · intro Q hQ hbox
    have hc:=((mem_flagGlobalCoefficientBox_iff Q 14738193 131071 62316 24
      (by decide)).mp hbox).2.2
    have hs:=((mem_flagGlobalCoefficientBox_iff Q 14738193 131071 62316 24
      (by decide)).mp hbox).2.1
    have hy:=residualYS_mul_le_contact_add_slope Q 131071 (by decide)
    omega
  · rw [show 14+1=15 by decide,show 62259+1=62260 by decide,
      thin_r10_sum,show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      LocatorArithmetic.kernelThin_nullity]
    decide
private theorem trade
    (R yCap totalCap Dcap Lcap qcap J upper:ℕ)
    (hsum:(∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
      (Lcap+1-j-r)*min 131074 (Dcap-131071*j-131070*r))=upper)
    (hRpos:0<R) (hRchar:R<2130706433)
    (hDnum:16193817-(131071*(yCap+1)-R)≤Dcap)
    (hLnum:2748-(totalCap+1)≤Lcap) (hqnum:27-R≤qcap)
    (hJnum:Dcap≤131071*J) (hsq:2748<2*(totalCap+1))
    (hupper:upper<192439923067)
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:TradeKernel u0 u1,F∣reconstruct K 16193817 131071 2748 27 v.1)
    (hR:F.degreeOf (2:Fin 4)=R):
    wt residualYSWeights F≤yCap ∨ wt residualTotalWeights F≤totalCap:=by
  apply LocatorSquareWitness.factor_ys_or_total_le_of_square_collar
    16193817 131071 2748 27 89 131074 2130706433 R yCap totalCap
    Dcap Lcap qcap J IRSProfile.domain u0 u1 F hF hdiv hR
    hRpos hRchar (by decide) (by decide) (by decide)
    (by norm_num [I,IRSProfile.Index]) hDnum hLnum hqnum hJnum hsq
  rw [hsum,show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
    LocatorArithmetic.kernelTrade_nullity]
  exact hupper
theorem full_Trade_r10 (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:TradeKernel u0 u1,F∣reconstruct K 16193817 131071 2748 27 v.1)
    (hR:F.degreeOf (2:Fin 4)=10):
    wt residualYSWeights F≤53 ∨ wt residualTotalWeights F≤1374:=
  trade 10 53 1374 9115993 1373 17 70 192389842401 trade_r10_sum
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    u0 u1 F hF hdiv hR
theorem full_Trade_r11 (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:TradeKernel u0 u1,F∣reconstruct K 16193817 131071 2748 27 v.1)
    (hR:F.degreeOf (2:Fin 4)=11):
    wt residualYSWeights F≤50 ∨ wt residualTotalWeights F≤1374:=
  trade 11 50 1374 9509207 1373 16 73 191933726162 trade_r11_sum
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    u0 u1 F hF hdiv hR
theorem full_Trade_r12 (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:TradeKernel u0 u1,F∣reconstruct K 16193817 131071 2748 27 v.1)
    (hR:F.degreeOf (2:Fin 4)=12):
    wt residualYSWeights F≤46 ∨ wt residualTotalWeights F≤1378:=
  trade 12 46 1378 10033492 1369 15 77 192399490384 trade_r12_sum
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    u0 u1 F hF hdiv hR
theorem full_Trade_r13 (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:TradeKernel u0 u1,F∣reconstruct K 16193817 131071 2748 27 v.1)
    (hR:F.degreeOf (2:Fin 4)=13):
    wt residualYSWeights F≤43 ∨ wt residualTotalWeights F≤1374:=
  trade 13 43 1374 10426706 1373 14 80 189906004040 trade_r13_sum
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    u0 u1 F hF hdiv hR
end
end ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
