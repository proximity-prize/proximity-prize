import ProximityPrize.SubmissionLower.LocatorNestedProjection
import ProximityPrize.SubmissionLower.LocatorContact
namespace ProximityPrize.SubmissionLower.LocatorLowQuotient
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
variable {K I:Type*} [Field K] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
theorem quotient_box_of_full_divisor
    (D w L s m c t r:ℕ) (nodes u0 u1:I→K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ kernelReconstructLinear (K:=K) D w L s m nodes u0 u1 v)
    (hc:c ≤ wt (contactWeights w) F)
    (ht:t ≤ wt residualTotalWeights F) (hr:r ≤ wt residualSWeights F) :
    ∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      quotientPolynomial (kernelReconstructLinear (K:=K) D w L s m nodes u0 u1)
        F hdiv v ∈ globalCoefficientBox K (D - c) w (L - t) (s - r):=by
  let recon:=kernelReconstructLinear (K:=K) D w L s m nodes u0 u1
  intro v
  by_cases hv:v=0
  · subst v
    have hz:quotientPolynomial recon F hdiv 0=0 :=
      (quotientLinear recon F hF hdiv).map_zero
    rw [hz]
    exact (globalCoefficientBox K _ _ _ _).zero_mem
  · have hQ:recon v ≠ 0:=by
      intro hz
      apply hv
      apply kernelReconstructLinear_injective (K:=K) D w L s m nodes u0 u1
      simpa only [map_zero] using hz
    have heq:=recon_eq_mul_quotientPolynomial recon F hdiv v
    have hq:quotientPolynomial recon F hdiv v ≠ 0:=by
      intro hz
      exact hQ (by rw [heq,hz,mul_zero])
    have hReconBox:recon v ∈ globalCoefficientBox K D w L s:=by
      change reconstruct K D w L s v.1 ∈ globalCoefficientBox K D w L s
      exact reconstruct_mem_globalCoefficientBox K D w L s v.1
    exact quotient_mem_flagGlobalCoefficientBox_of_mul_eq
      (recon v) F (quotientPolynomial recon F hdiv v)
      D w L s c t r hQ hF hq hReconBox heq hc ht hr
theorem exists_fixed_low_quotient_finrank
    (D w L s m Ysrc delta:ℕ) (nodes u0 u1:I→K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hw:1 ≤ w) (hshape:D+s ≤ w*(Ysrc+1))
    (hsource:delta*channelCount
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) <
      Module.finrank K (ConstraintKernel (K:=K) D w L s m nodes u0 u1)) :
    ∃ (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
      (Q:MvPolynomial (Fin 4) K),
      v ≠ 0∧Q ≠ 0∧F*Q=reconstruct K D w L s v.1 ∧
      Q ∈ nestedCoefficientBox K (D - delta - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) ∧
      F*Q ∈ globalCoefficientBox K (D - delta) w L s:=by
  classical
  let recon:=kernelReconstructLinear (K:=K) D w L s m nodes u0 u1
  have hdivK:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ recon v:=by
    intro v
    simpa only [recon,kernelReconstructLinear_apply] using hdiv v
  let q:=quotientLinear recon F hF hdivK
  have hqinj:Function.Injective q :=
    quotientLinear_injective recon
      (kernelReconstructLinear_injective (K:=K) D w L s m nodes u0 u1)
      F hF hdivK
  have hprod (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1) :
      recon v=F*q v:=recon_eq_mul_quotientPolynomial recon F hdivK v
  have hqbox:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      q v ∈ globalCoefficientBox K (D - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (s - wt residualSWeights F) :=
    quotient_box_of_full_divisor D w L s m
      (wt (contactWeights w) F) (wt residualTotalWeights F) (wt residualSWeights F)
      nodes u0 u1 F hF hdivK le_rfl le_rfl le_rfl
  have hqYS (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1) :
      wt residualYSWeights (q v) ≤ Ysrc - wt residualYSWeights F:=by
    by_cases hv:v=0
    · subst v
      simp [wt,MvPolynomial.weightedTotalDegree]
    · have hqv:q v ≠ 0:=by
        intro hz
        apply hv
        apply hqinj
        simpa only [map_zero] using hz
      have hsrc:wt residualYSWeights (recon v) ≤ Ysrc:=by
        apply flag_box_ys_bound D w L s Ysrc hw hshape
        change reconstruct K D w L s v.1 ∈ globalCoefficientBox K D w L s
        exact reconstruct_mem_globalCoefficientBox K D w L s v.1
      have hmul:=weightedTotalDegree_mul residualYSWeights F (q v) hF hqv
      rw [← hprod v] at hmul
      simp only [wt] at hsrc ⊢
      omega
  have hqNested:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      q v ∈ nestedCoefficientBox K (D - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F):=by
    intro v d hd
    have hb:=hqbox v hd
    have hy:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans (hqYS v)
    rw [weight_fin4] at hy
    simp only [residualYSWeights] at hy
    refine ⟨hb.1,?_,hb.2.1,hb.2.2⟩
    simpa [residualYSWeights] using hy
  have hwidth:D - wt (contactWeights w) F ≤
      (D - delta - wt (contactWeights w) F)+delta:=by omega
  obtain ⟨v,hv,hQ,hlow⟩:=exists_nonzero_image_mem_low
    (D - wt (contactWeights w) F) (D - delta - wt (contactWeights w) F)
    w delta (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
      (s - wt residualSWeights F) hwidth q hqinj hqNested hsource
  have heq:F*q v=reconstruct K D w L s v.1:=by
    simpa only [recon,kernelReconstructLinear_apply] using (hprod v).symm
  refine ⟨v,q v,hv,hQ,heq,hlow,?_⟩
  have hsourceBox:F*q v ∈ globalCoefficientBox K D w L s:=by
    rw [heq]
    exact reconstruct_mem_globalCoefficientBox K D w L s v.1
  have hparent:0<D - delta:=by
    have h:=(nested_mem_weights hlow hQ).2.2.2
    omega
  have hD:0<D:=by omega
  have hsrc:=(mem_flagGlobalCoefficientBox_iff (F*q v) D w L s hD).mp hsourceBox
  have hqc:=(nested_mem_weights hlow hQ).2.2.2
  have hmul:=weightedTotalDegree_mul (contactWeights w) F (q v) hF hQ
  apply (mem_flagGlobalCoefficientBox_iff (F*q v) (D - delta) w L s hparent).mpr
  refine ⟨hsrc.1,hsrc.2.1,?_⟩
  simp only [wt] at hqc ⊢
  omega
theorem exists_fixed_low_quotient
    (D w L s m Ysrc delta:ℕ) (nodes u0 u1:I→K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hw:1 ≤ w) (hshape:D+s ≤ w*(Ysrc+1))
    (hsource:delta*channelCount
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) <
      coefficientCount D w L s - Fintype.card I*localRankBound m L s) :
    ∃ (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
      (Q:MvPolynomial (Fin 4) K),
      v ≠ 0∧Q ≠ 0∧F*Q=reconstruct K D w L s v.1 ∧
      Q ∈ nestedCoefficientBox K (D - delta - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) ∧
      F*Q ∈ globalCoefficientBox K (D - delta) w L s :=
  exists_fixed_low_quotient_finrank D w L s m Ysrc delta nodes u0 u1 F hF hdiv hw hshape
    (hsource.trans_le (constraintKernel_finrank_lower_bound D w L s m nodes u0 u1))
theorem specialization_pderiv_R_eq_zero_of_kernel_low_box
    (D Dlow w L s m:ℕ) (nodes:I ↪ K) (u0 u1:I→K)
    (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
    (hlow:reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P:Polynomial K) (gamma:K) (support:Finset I)
    (hw:1 ≤ w) (hP:P.natDegree ≤ w)
    (hcapacity:Dlow ≤ (m - 1)*support.card+(w - 1))
    (hvalues:∀ i ∈ support,P.eval (nodes i)=u0 i+gamma*u1 i) :
    RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2:Fin 4) (reconstruct K D w L s v.1))=0:=by
  classical
  let H:=reconstruct K D w L s v.1
  by_contra hne
  have hH:H ≠ 0:=by
    intro hz
    apply hne
    change RCN319.specialization K P gamma (MvPolynomial.pderiv (2:Fin 4) H)=0
    simp only [hz,map_zero]
  have hDlow:0<Dlow:=by
    obtain ⟨d,hd⟩:=MvPolynomial.support_nonempty.mpr hH
    have h:=(hlow hd).2.2
    omega
  have hcaps:=(mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow
  have hdegree:=ContactOrderBridge.specialized_R_derivative_degree
    K H P gamma w (Dlow - 1) hP hcaps.2.2 hne
  rw [RCN101.specialization_eq_ordinary] at hdegree
  have hdegreeStrict :
      (RCN122.specialization K P gamma (MvPolynomial.pderiv (2:Fin 4) H)).natDegree <
        (m - 1)*support.card:=by
    rw [RCN101.specialization_eq_ordinary]
    omega
  have hcontact:∀ i ∈ support,∀ r:ℕ,
      slopeDifference K ^ (m - 1 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2:Fin 4) H)).coeff r:=by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 1) _).mp
    apply ContactOrderBridge.contactAtLeast_pderiv_R K (nodes i) (u0 i) (u1 i) m H
    exact ContactOrderBridge.contactAtLeast_of_mem_kernel
      K D w L s m nodes u0 u1 v.1 v.2 i
  have hz:=RCN122.specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2:Fin 4) H) P gamma nodes u0 u1 support (m - 1)
    hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H,RCN101.specialization_eq_ordinary] using hz
theorem exists_fixed_quotient_with_derivative_vanishing
    (D w L s m Ysrc delta agreements:ℕ) (nodes:I ↪ K) (u0 u1:I→K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hw:1 ≤ w) (hshape:D+s ≤ w*(Ysrc+1))
    (hsource:delta*channelCount
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) <
      coefficientCount D w L s - Fintype.card I*localRankBound m L s)
    (hcapacity:D - delta ≤ (m - 1)*agreements+(w - 1))
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ w)
    (hagreement:∀ gamma ∈ Gamma,agreements ≤
      ((Finset.univ:Finset I).filter (fun i =>
        (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card) :
    ∃ (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
      (Q:MvPolynomial (Fin 4) K),
      v ≠ 0∧Q ≠ 0∧F*Q=reconstruct K D w L s v.1 ∧
      Q ∈ nestedCoefficientBox K (D - delta - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) ∧
      F*Q ∈ globalCoefficientBox K (D - delta) w L s ∧
      ∀ gamma ∈ Gamma,RCN319.specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2:Fin 4) (F*Q))=0:=by
  obtain ⟨v,Q,hv,hQ,heq,hbox,hprod⟩ :=
    exists_fixed_low_quotient D w L s m Ysrc delta nodes u0 u1
      F hF hdiv hw hshape hsource
  refine ⟨v,Q,hv,hQ,heq,hbox,hprod,?_⟩
  intro gamma hgamma
  let support:=(Finset.univ:Finset I).filter (fun i =>
    (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)
  have hcard:agreements ≤ support.card:=hagreement gamma hgamma
  have hcap:D - delta ≤ (m - 1)*support.card+(w - 1) :=
    hcapacity.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (m - 1) hcard) _)
  have hvalues:∀ i ∈ support,
      (selected gamma).eval (nodes i)=u0 i+gamma*u1 i:=by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hvbox:reconstruct K D w L s v.1 ∈ globalCoefficientBox K (D - delta) w L s:=by
    rw [← heq]
    exact hprod
  rw [heq]
  exact specialization_pderiv_R_eq_zero_of_kernel_low_box
    D (D - delta) w L s m nodes u0 u1 v hvbox (selected gamma) gamma support
    hw (hdegree gamma hgamma) hcap hvalues
end
end ProximityPrize.SubmissionLower.LocatorLowQuotient
