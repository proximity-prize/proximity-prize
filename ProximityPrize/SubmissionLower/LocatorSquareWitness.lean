import ProximityPrize.SubmissionLower.LocatorIrreducibleContact
import ProximityPrize.SubmissionLower.LocatorMultiSlopeQuotient

namespace ProximityPrize.SubmissionLower.LocatorSquareWitness

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {K I:Type} [Field K] [Fintype I]
local instance:DecidableEq K:=Classical.decEq _

theorem exists_square_witness_of_collar
    (D w L s m c p R Dcap Lcap qcap J:ℕ) [CharP K p]
    (nodes u0 u1:I → K) (F:MvPolynomial (Fin 4) K)
    (hF:Irreducible F)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F∣reconstruct K D w L s v.1)
    (hR:F.degreeOf (2:Fin 4)=R)
    (hRpos:0<R) (hRchar:R<p) (hm:1≤m)
    (hcost:Fintype.card I≤c+(w - 1))
    (hD:D - wt (contactWeights w) F≤Dcap)
    (hL:L - wt residualTotalWeights F≤Lcap)
    (hq:s - wt residualSWeights F≤qcap)
    (hJ:Dcap≤w*J)
    (hcollar:
      (∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
        (Lcap+1 - j - r)*min c (Dcap - w*j - (w - 1)*r))<
      coefficientCount D w L s - Fintype.card I*localRankBound m L s):
    ∃ Q:MvPolynomial (Fin 4) K,
      Q≠0 ∧ F ^ 2∣Q ∧ Q∈globalCoefficientBox K D w L s:=by
  have hex:∃ (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
      (P:MvPolynomial (Fin 4) K),P≠0 ∧
        reconstruct K D w L s v.1=F*P ∧
        P∈globalCoefficientBox K
          (D - wt (contactWeights w) F - c) w
          (L - wt residualTotalWeights F) (s - wt residualSWeights F):=by
    by_contra hn
    have hzero:∀ (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
        (P:MvPolynomial (Fin 4) K),
        reconstruct K D w L s v.1=F*P →
        P∈globalCoefficientBox K
          (D - wt (contactWeights w) F - c) w
          (L - wt residualTotalWeights F) (s - wt residualSWeights F) → P=0:=by
      intro v P hprod hprefix
      by_contra hP
      exact hn ⟨v,P,hP,hprod,hprefix⟩
    have hu:=LocatorMultiSlopeQuotient.whole_kernel_finrank_le_small_sum
      D w L s m c nodes u0 u1 F hF.ne_zero hdiv hzero
      Dcap Lcap qcap J hD hL hq hJ
    have hl:=constraintKernel_finrank_lower_bound (K:=K)
      D w L s m nodes u0 u1
    exact (not_lt_of_ge hu) (hcollar.trans_le hl)
  obtain ⟨v,P,hP,hprod,hprefix⟩:=hex
  have hFP:=LocatorIrreducibleContact.irreducible_dvd_quotient_of_mem_prefix
    D w L s m c p nodes u0 u1 F hF hdiv
    (by rw [hR]; exact hRpos) (by rw [hR]; exact hRchar) hm hcost
    v P hprod hprefix
  obtain ⟨G,hG⟩:=hFP
  have hGne:G≠0:=by
    intro hz
    apply hP
    rw [hG,hz,mul_zero]
  have hQ:reconstruct K D w L s v.1≠0:=by
    rw [hprod,hG]
    exact mul_ne_zero hF.ne_zero (mul_ne_zero hF.ne_zero hGne)
  refine ⟨reconstruct K D w L s v.1,hQ,?_,
    reconstruct_mem_globalCoefficientBox K D w L s v.1⟩
  refine ⟨G,?_⟩
  rw [pow_two]
  calc
    reconstruct K D w L s v.1=F*P:=hprod
    _=F*(F*G):=by rw [hG]
    _=F*F*G:=(mul_assoc F F G).symm

theorem factor_total_le_of_square_collar
    (D w L s m c p R cap Dcap Lcap qcap J:ℕ) [CharP K p]
    (nodes u0 u1:I → K) (F:MvPolynomial (Fin 4) K)
    (hF:Irreducible F)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F∣reconstruct K D w L s v.1)
    (hR:F.degreeOf (2:Fin 4)=R)
    (hRpos:0<R) (hRchar:R<p) (hm:1≤m)
    (hwpos:1≤w) (hDpos:0<D)
    (hcost:Fintype.card I≤c+(w - 1))
    (hD:D - (w*R - R)≤Dcap)
    (hL:L - (cap+1)≤Lcap) (hq:s - R≤qcap)
    (hJ:Dcap≤w*J) (hsquare:L<2*(cap+1))
    (hcollar:
      (∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
        (Lcap+1 - j - r)*min c (Dcap - w*j - (w - 1)*r))<
      coefficientCount D w L s - Fintype.card I*localRankBound m L s):
    wt residualTotalWeights F≤cap:=by
  by_contra hnot
  have htotal:cap+1≤wt residualTotalWeights F:=by omega
  have hS:wt residualSWeights F=R:=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hYS:R≤wt residualYSWeights F:=by
    rw [← hS]
    exact (residual_weight_nested F).1
  have hw:=residualYS_mul_le_contact_add_slope F w hwpos
  have hmul:=Nat.mul_le_mul_left w hYS
  have hcontact:w*R - R≤wt (contactWeights w) F:=by omega
  have hD':D - wt (contactWeights w) F≤Dcap:=
    (Nat.sub_le_sub_left hcontact D).trans hD
  have hL':L - wt residualTotalWeights F≤Lcap:=
    (Nat.sub_le_sub_left htotal L).trans hL
  have hq':s - wt residualSWeights F≤qcap:=by omega
  obtain ⟨Q,hQ,hsqdvd,hbox⟩:=exists_square_witness_of_collar
    D w L s m c p R Dcap Lcap qcap J nodes u0 u1 F hF hdiv hR
    hRpos hRchar hm hcost hD' hL' hq' hJ hcollar
  have hTQ:=((mem_flagGlobalCoefficientBox_iff Q D w L s hDpos).mp hbox).1
  have hsq:=weightedTotalDegree_le_of_dvd residualTotalWeights (F ^ 2) Q hsqdvd hQ
  have hpow:=weightedTotalDegree_mul residualTotalWeights F F hF.ne_zero hF.ne_zero
  change wt residualTotalWeights (F ^ 2)≤wt residualTotalWeights Q at hsq
  change wt residualTotalWeights (F*F)=
    wt residualTotalWeights F+wt residualTotalWeights F at hpow
  rw [pow_two,hpow] at hsq
  omega

theorem factor_ys_le_of_square_collar
    (D w L s m c p R cap sourceCap Dcap Lcap qcap J:ℕ) [CharP K p]
    (nodes u0 u1:I → K) (F:MvPolynomial (Fin 4) K)
    (hF:Irreducible F)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F∣reconstruct K D w L s v.1)
    (hR:F.degreeOf (2:Fin 4)=R)
    (hRpos:0<R) (hRchar:R<p) (hm:1≤m)
    (hwpos:1≤w) (hcost:Fintype.card I≤c+(w - 1))
    (hD:D - (w*(cap+1) - R)≤Dcap)
    (hL:L - (cap+1)≤Lcap) (hq:s - R≤qcap)
    (hJ:Dcap≤w*J) (hsquare:sourceCap<2*(cap+1))
    (hsource:∀ Q:MvPolynomial (Fin 4) K,Q≠0 →
      Q∈globalCoefficientBox K D w L s → wt residualYSWeights Q≤sourceCap)
    (hcollar:
      (∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
        (Lcap+1 - j - r)*min c (Dcap - w*j - (w - 1)*r))<
      coefficientCount D w L s - Fintype.card I*localRankBound m L s):
    wt residualYSWeights F≤cap:=by
  by_contra hnot
  have hYS:cap+1≤wt residualYSWeights F:=by omega
  have hS:wt residualSWeights F=R:=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have htotal:cap+1≤wt residualTotalWeights F:=
    hYS.trans (residual_weight_nested F).2
  have hw:=residualYS_mul_le_contact_add_slope F w hwpos
  have hmul:=Nat.mul_le_mul_left w hYS
  have hcontact:w*(cap+1) - R≤wt (contactWeights w) F:=by omega
  have hD':D - wt (contactWeights w) F≤Dcap:=
    (Nat.sub_le_sub_left hcontact D).trans hD
  have hL':L - wt residualTotalWeights F≤Lcap:=
    (Nat.sub_le_sub_left htotal L).trans hL
  have hq':s - wt residualSWeights F≤qcap:=by omega
  obtain ⟨Q,hQ,hsqdvd,hbox⟩:=exists_square_witness_of_collar
    D w L s m c p R Dcap Lcap qcap J nodes u0 u1 F hF hdiv hR
    hRpos hRchar hm hcost hD' hL' hq' hJ hcollar
  have hQYS:=hsource Q hQ hbox
  have hsq:=weightedTotalDegree_le_of_dvd residualYSWeights (F ^ 2) Q hsqdvd hQ
  have hpow:=weightedTotalDegree_mul residualYSWeights F F hF.ne_zero hF.ne_zero
  change wt residualYSWeights (F ^ 2)≤wt residualYSWeights Q at hsq
  change wt residualYSWeights (F*F)=
    wt residualYSWeights F+wt residualYSWeights F at hpow
  rw [pow_two,hpow] at hsq
  omega

theorem factor_ys_or_total_le_of_square_collar
    (D w L s m c p R yCap totalCap Dcap Lcap qcap J:ℕ) [CharP K p]
    (nodes u0 u1:I → K) (F:MvPolynomial (Fin 4) K)
    (hF:Irreducible F)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F∣reconstruct K D w L s v.1)
    (hR:F.degreeOf (2:Fin 4)=R)
    (hRpos:0<R) (hRchar:R<p) (hm:1≤m)
    (hwpos:1≤w) (hDpos:0<D)
    (hcost:Fintype.card I≤c+(w - 1))
    (hD:D - (w*(yCap+1) - R)≤Dcap)
    (hL:L - (totalCap+1)≤Lcap) (hq:s - R≤qcap)
    (hJ:Dcap≤w*J) (hsquare:L<2*(totalCap+1))
    (hcollar:
      (∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
        (Lcap+1-j-r)*min c (Dcap-w*j-(w-1)*r))<
      coefficientCount D w L s-Fintype.card I*localRankBound m L s):
    wt residualYSWeights F≤yCap ∨
      wt residualTotalWeights F≤totalCap:=by
  by_cases hy:wt residualYSWeights F≤yCap
  · exact Or.inl hy
  right
  by_contra ht
  have hy':yCap+1≤wt residualYSWeights F:=by omega
  have ht':totalCap+1≤wt residualTotalWeights F:=by omega
  have hS:wt residualSWeights F=R:=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hw:=residualYS_mul_le_contact_add_slope F w hwpos
  have hm':=Nat.mul_le_mul_left w hy'
  have hc:w*(yCap+1)-R≤wt (contactWeights w) F:=by omega
  have hD':D-wt (contactWeights w) F≤Dcap:=
    (Nat.sub_le_sub_left hc D).trans hD
  have hL':L-wt residualTotalWeights F≤Lcap:=
    (Nat.sub_le_sub_left ht' L).trans hL
  have hq':s-wt residualSWeights F≤qcap:=by omega
  obtain ⟨Q,hQ,hsqdvd,hbox⟩:=exists_square_witness_of_collar
    D w L s m c p R Dcap Lcap qcap J nodes u0 u1 F hF hdiv hR
    hRpos hRchar hm hcost hD' hL' hq' hJ hcollar
  have hQtotal:=((mem_flagGlobalCoefficientBox_iff Q D w L s hDpos).mp hbox).1
  have hsq:=weightedTotalDegree_le_of_dvd residualTotalWeights (F^2) Q hsqdvd hQ
  have hpow:=weightedTotalDegree_mul residualTotalWeights F F hF.ne_zero hF.ne_zero
  change wt residualTotalWeights (F^2)≤wt residualTotalWeights Q at hsq
  change wt residualTotalWeights (F*F)=
    wt residualTotalWeights F+wt residualTotalWeights F at hpow
  rw [pow_two,hpow] at hsq
  omega

end
end ProximityPrize.SubmissionLower.LocatorSquareWitness
