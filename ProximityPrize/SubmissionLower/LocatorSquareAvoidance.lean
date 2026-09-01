import ProximityPrize.SubmissionLower.LocatorLowQuotient
namespace ProximityPrize.SubmissionLower.LocatorSquareAvoidance
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 LocatorLowQuotient
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

variable {K V:Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance:DecidableEq K:=Classical.decEq K

theorem exists_nonzero_image_mem_low_not_dvd
    (Dhigh Dlow w delta T YS S squareBound:ℕ)
    (hwidth:Dhigh ≤ Dlow + delta)
    (q:V →ₗ[K] MvPolynomial (Fin 4) K) (hq:Function.Injective q)
    (hmem: ∀ v,q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hsquare:coefficientCount (Dlow - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (S - wt residualSWeights F) ≤
      squareBound)
    (hsource:delta * channelCount T YS S + squareBound <
      Module.finrank K V) :
    ∃ v:V,v ≠ 0 ∧ q v ≠ 0 ∧
      q v ∈ nestedCoefficientBox K Dlow w T YS S ∧ ¬ F ∣ q v:=by
  classical
  let band:= (highBandMap (K:=K) w Dlow delta T YS S).comp q
  let low:=LinearMap.ker band
  have hrange:Module.finrank K band.range ≤
      delta * channelCount T YS S:=by
    calc
      Module.finrank K band.range ≤
          Module.finrank K (HighBandIndex delta T YS S → K) :=
        band.range.finrank_le
      _=delta * channelCount T YS S:=by
        rw [Module.finrank_fintype_fun_eq_card,highBandIndex_card]
  have hlow:squareBound < Module.finrank K low:=by
    have hsum:=band.finrank_range_add_finrank_ker
    change Module.finrank K band.range + Module.finrank K low=
      Module.finrank K V at hsum
    omega
  let qlow:low →ₗ[K] MvPolynomial (Fin 4) K:=q.comp low.subtype
  have hqlow:Function.Injective qlow:=by
    intro a b hab
    apply Subtype.ext
    apply hq
    simpa only [qlow,LinearMap.comp_apply,Submodule.coe_subtype] using hab
  let bad:Submodule K low:= {
    carrier:= {v | F ∣ qlow v}
    zero_mem':=by simp [qlow]
    add_mem':=by
      intro a b ha hb
      change F ∣ qlow (a + b)
      rw [map_add]
      exact dvd_add ha hb
    smul_mem':=by
      intro a v hv
      change F ∣ qlow (a • v)
      rw [map_smul,MvPolynomial.smul_eq_C_mul]
      exact dvd_mul_of_dvd_right hv _}
  have hbad:bad ≠ ⊤ :=by
    intro htop
    have hdiv: ∀ v:low,F ∣ qlow v:=by
      intro v
      have hv:v ∈ bad:=by rw [htop]; trivial
      exact hv
    have hqbox: ∀ v:low,
        quotientPolynomial qlow F hdiv v ∈
          globalCoefficientBox K (Dlow - wt (contactWeights w) F) w
            (T - wt residualTotalWeights F) (S - wt residualSWeights F) :=by
      intro v
      by_cases hv:v=0
      · subst v
        have hz:quotientPolynomial qlow F hdiv 0=0:=
          (quotientLinear qlow F hF hdiv).map_zero
        rw [hz]
        exact (globalCoefficientBox K _ _ _ _).zero_mem
      · have hqv:qlow v ≠ 0:=by
          intro hz
          apply hv
          apply hqlow
          simpa only [map_zero] using hz
        have hhigh:qlow v ∈ nestedCoefficientBox K Dhigh w T YS S:=by
          simpa only [qlow,LinearMap.comp_apply,Submodule.coe_subtype] using
            hmem v.1
        have hzero:highBandMap w Dlow delta T YS S (qlow v) =0:=by
          have hvker:=v.2
          change band v.1=0 at hvker
          simpa only [band,qlow,LinearMap.comp_apply,
            Submodule.coe_subtype] using hvker
        have hlowbox:qlow v ∈ nestedCoefficientBox K Dlow w T YS S:=
          mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
            (qlow v) hhigh hzero
        have heq:qlow v=F * quotientPolynomial qlow F hdiv v:=
          recon_eq_mul_quotientPolynomial qlow F hdiv v
        have hquot:quotientPolynomial qlow F hdiv v ≠ 0:=by
          intro hz
          exact hqv (by rw [heq,hz,mul_zero])
        exact quotient_mem_flagGlobalCoefficientBox_of_mul_eq
          (qlow v) F (quotientPolynomial qlow F hdiv v)
          Dlow w T S (wt (contactWeights w) F)
          (wt residualTotalWeights F) (wt residualSWeights F)
          hqv hF hquot (nested_mem_global hlowbox) heq le_rfl le_rfl le_rfl
    have hle:=finrank_le_quotient_box qlow hqlow F hF hdiv
      (globalCoefficientBox K (Dlow - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (S - wt residualSWeights F)) hqbox
    rw [globalCoefficientBox_finrank] at hle
    exact (not_lt_of_ge (hle.trans hsquare)) hlow
  have hex: ∃ v:low,v ∉ bad:=by
    by_contra hn
    apply hbad
    ext v
    simp only [Submodule.mem_top,iff_true]
    by_contra hv
    exact hn ⟨v,hv⟩
  obtain ⟨v,hvbad⟩ :=hex
  have hv:v.1 ≠ 0:=by
    intro hz
    apply hvbad
    have hv0:v=0:=Subtype.ext hz
    rw [hv0]
    exact bad.zero_mem
  have hqv:q v.1 ≠ 0:=by
    intro hz
    apply hv
    apply hq
    simpa only [map_zero] using hz
  have hhigh:q v.1 ∈ nestedCoefficientBox K Dhigh w T YS S:=hmem v.1
  have hzero:highBandMap w Dlow delta T YS S (q v.1) =0:=by
    have hvker:=v.2
    change band v.1=0 at hvker
    simpa only [band,LinearMap.comp_apply,Submodule.coe_subtype] using hvker
  have hlowbox:q v.1 ∈ nestedCoefficientBox K Dlow w T YS S:=
    mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
      (q v.1) hhigh hzero
  refine ⟨v.1,hv,hqv,hlowbox, ?_⟩
  change ¬ F ∣ qlow v at hvbad
  simpa only [qlow,LinearMap.comp_apply,Submodule.coe_subtype] using hvbad

theorem exists_fixed_low_quotient_not_dvd_finrank
    {I:Type*} [Fintype I]
    (D w L s m Ysrc delta squareBound:ℕ) (nodes u0 u1:I → K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv: ∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hw:1 ≤ w) (hshape:D + s ≤ w * (Ysrc + 1))
    (hsquare:coefficientCount
        (D - delta - wt (contactWeights w) F - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F - wt residualTotalWeights F)
        (s - wt residualSWeights F - wt residualSWeights F) ≤ squareBound)
    (hsource:delta * channelCount
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) + squareBound <
      Module.finrank K
        (ConstraintKernel (K:=K) D w L s m nodes u0 u1)) :
    ∃ (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
      (Q:MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ Q ≠ 0 ∧ F * Q=reconstruct K D w L s v.1 ∧
      Q ∈ nestedCoefficientBox K (D - delta - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) ∧
      F * Q ∈ globalCoefficientBox K (D - delta) w L s ∧ ¬ F ∣ Q:=by
  classical
  let recon:=kernelReconstructLinear (K:=K) D w L s m nodes u0 u1
  have hdivK: ∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ recon v:=by
    intro v
    simpa only [recon,kernelReconstructLinear_apply] using hdiv v
  let q:=quotientLinear recon F hF hdivK
  have hqinj:Function.Injective q:=
    quotientLinear_injective recon
      (kernelReconstructLinear_injective (K:=K) D w L s m nodes u0 u1)
      F hF hdivK
  have hprod (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1) :
      recon v=F * q v:=
    recon_eq_mul_quotientPolynomial recon F hdivK v
  have hqbox: ∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      q v ∈ globalCoefficientBox K (D - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (s - wt residualSWeights F) :=
    quotient_box_of_full_divisor D w L s m
      (wt (contactWeights w) F) (wt residualTotalWeights F)
      (wt residualSWeights F) nodes u0 u1 F hF hdivK le_rfl le_rfl le_rfl
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
  have hqNested: ∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      q v ∈ nestedCoefficientBox K (D - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) :=by
    intro v d hd
    have hb:=hqbox v hd
    have hy:= (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans (hqYS v)
    rw [weight_fin4] at hy
    simp only [residualYSWeights] at hy
    refine ⟨hb.1, ?_,hb.2.1,hb.2.2⟩
    simpa [residualYSWeights] using hy
  have hwidth:D - wt (contactWeights w) F ≤
      (D - delta - wt (contactWeights w) F) + delta:=by omega
  obtain ⟨v,hv,hQ,hlow,hnot⟩ :=exists_nonzero_image_mem_low_not_dvd
    (D - wt (contactWeights w) F) (D - delta - wt (contactWeights w) F)
    w delta (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
      (s - wt residualSWeights F) squareBound hwidth q hqinj hqNested F hF
      hsquare hsource
  have heq:F * q v=reconstruct K D w L s v.1:=by
    simpa only [recon,kernelReconstructLinear_apply] using (hprod v).symm
  refine ⟨v,q v,hv,hQ,heq,hlow, ?_,hnot⟩
  have hsourceBox:F * q v ∈ globalCoefficientBox K D w L s:=by
    rw [heq]
    exact reconstruct_mem_globalCoefficientBox K D w L s v.1
  have hparent:0 < D - delta:=by
    have h:= (nested_mem_weights hlow hQ).2.2.2
    omega
  have hD:0 < D:=by omega
  have hsrc:=
    (mem_flagGlobalCoefficientBox_iff (F * q v) D w L s hD).mp hsourceBox
  have hqc:= (nested_mem_weights hlow hQ).2.2.2
  have hmul:=weightedTotalDegree_mul (contactWeights w) F (q v) hF hQ
  apply (mem_flagGlobalCoefficientBox_iff
    (F * q v) (D - delta) w L s hparent).mpr
  refine ⟨hsrc.1,hsrc.2.1, ?_⟩
  simp only [wt] at hqc ⊢
  omega

theorem exists_fixed_low_quotient_not_dvd
    {I:Type*} [Fintype I]
    (D w L s m Ysrc delta squareBound:ℕ) (nodes u0 u1:I → K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv: ∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hw:1 ≤ w) (hshape:D + s ≤ w * (Ysrc + 1))
    (hsquare:coefficientCount
        (D - delta - wt (contactWeights w) F - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F - wt residualTotalWeights F)
        (s - wt residualSWeights F - wt residualSWeights F) ≤ squareBound)
    (hsource:delta * channelCount
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) + squareBound <
      coefficientCount D w L s - Fintype.card I * localRankBound m L s) :
    ∃ (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
      (Q:MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ Q ≠ 0 ∧ F * Q=reconstruct K D w L s v.1 ∧
      Q ∈ nestedCoefficientBox K (D - delta - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) ∧
      F * Q ∈ globalCoefficientBox K (D - delta) w L s ∧ ¬ F ∣ Q:=
  exists_fixed_low_quotient_not_dvd_finrank D w L s m Ysrc delta squareBound
    nodes u0 u1 F hF hdiv hw hshape hsquare
      (hsource.trans_le
        (constraintKernel_finrank_lower_bound D w L s m nodes u0 u1))

theorem exists_fixed_quotient_with_derivative_vanishing_not_dvd
    {I:Type*} [Fintype I]
    (D w L s m Ysrc delta squareBound agreements:ℕ)
    (nodes:I ↪ K) (u0 u1:I → K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv: ∀ v:ConstraintKernel (K:=K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hw:1 ≤ w) (hshape:D + s ≤ w * (Ysrc + 1))
    (hsquare:coefficientCount
        (D - delta - wt (contactWeights w) F - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F - wt residualTotalWeights F)
        (s - wt residualSWeights F - wt residualSWeights F) ≤ squareBound)
    (hsource:delta * channelCount
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) + squareBound <
      coefficientCount D w L s - Fintype.card I * localRankBound m L s)
    (hcapacity:D - delta ≤ (m - 1) * agreements + (w - 1))
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree: ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement: ∀ gamma ∈ Gamma,agreements ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (nodes i) =u0 i + gamma * u1 i)).card) :
    ∃ (v:ConstraintKernel (K:=K) D w L s m nodes u0 u1)
      (Q:MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ Q ≠ 0 ∧ F * Q=reconstruct K D w L s v.1 ∧
      Q ∈ nestedCoefficientBox K (D - delta - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) ∧
      F * Q ∈ globalCoefficientBox K (D - delta) w L s ∧
      (∀ gamma ∈ Gamma,RCN319.specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2:Fin 4) (F * Q)) =0) ∧
      ¬ F ∣ Q:=by
  obtain ⟨v,Q,hv,hQ,heq,hbox,hprod,hnot⟩ :=
    exists_fixed_low_quotient_not_dvd D w L s m Ysrc delta squareBound
      nodes u0 u1 F hF hdiv hw hshape hsquare hsource
  refine ⟨v,Q,hv,hQ,heq,hbox,hprod, ?_,hnot⟩
  intro gamma hgamma
  let support:= (Finset.univ:Finset I).filter (fun i=>
    (selected gamma).eval (nodes i) =u0 i + gamma * u1 i)
  have hcard:agreements ≤ support.card:=hagreement gamma hgamma
  have hcap:D - delta ≤ (m - 1) * support.card + (w - 1) :=
    hcapacity.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left (m - 1) hcard) _)
  have hvalues: ∀ i ∈ support,
      (selected gamma).eval (nodes i) =u0 i + gamma * u1 i:=by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hvbox:reconstruct K D w L s v.1 ∈
      globalCoefficientBox K (D - delta) w L s:=by
    rw [← heq]
    exact hprod
  rw [heq]
  exact specialization_pderiv_R_eq_zero_of_kernel_low_box
    D (D - delta) w L s m nodes u0 u1 v hvbox (selected gamma) gamma
      support hw (hdegree gamma hgamma) hcap hvalues

end
end ProximityPrize.SubmissionLower.LocatorSquareAvoidance
