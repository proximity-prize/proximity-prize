import ProximityPrize.SubmissionLower.MergedInfra6815_29
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingSourceTwoProfiles6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000
open MvPolynomial SecondJetCoefficients SecondJetClearedHelper
open WholeSpaceSourceCounts6814 WholeSpaceSourceKernel6814
open MovingFiberThreeSources6811 MovingSourceCarrierField6814
open RCN234 RCN156

variable {K N : Type} [Field K] [Fintype N]

def Profile {F : MvPolynomial (Fin 4) K} (S : Source F) (B U T s k n0 : ℕ) : Prop :=
  S.B=B ∧ S.U=U ∧ S.T=T ∧ S.s=s ∧ S.k=k ∧ S.n0=n0

theorem source_nonzero (F : MvPolynomial (Fin 4) K) (S : Source F) : S.P≠0 := by
  intro hz
  have hh := S.hn
  rw [hz,map_zero,Polynomial.natDegree_zero] at hh
  have hd := S.hdn
  omega

theorem canonical_source_power [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (S : Source F)
    (hT : S.T<wt residualTotalWeights F) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hk : S.k<2130706433) :
    (asS S.P).map (carrierMap F)≠0 ∧
      (Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap F) F))^S.d ∣
        (asS S.P).map (carrierMap F) := by
  have hn := carrier_polynomial_nonzero F S.P (source_nonzero F S) S.T
    (fun e he => (S.hshape e he).2.2) hT
  exact ⟨hn,SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd S.P F (carrierMap F)
    S.s S.k S.hS (carrierMap_self F) (carrier_H_nonzero F hpos hsmall) hn
    (SecondJetOwnShape.factorial_ne S.k hk) S.hdiv⟩

end
end ProximityPrize.SubmissionLower.MovingSourceTwoProfiles6814
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.MovingSourceOwnerRouting6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open MvPolynomial SecondJetCoefficients SecondJetCarrierDichotomy
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingFiberThreeSources6811
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 MovingSourceOwnerSplit6814
open MovingSourceNativeEnvelope6814 MovingSourceTwoProfiles6814
open RCN234 RCN156

variable {K : Type} [Field K]

theorem source_caps (F : MvPolynomial (Fin 4) K) (S : Source F) :
    weightedTotalDegree slopeWeights S.P≤S.B ∧ weightedTotalDegree middleWeights S.P≤S.U ∧
      weightedTotalDegree totalWeights S.P≤S.T ∧ S.P.degreeOf 1≤S.s := by
  refine ⟨Finset.sup_le ?_,Finset.sup_le ?_,Finset.sup_le ?_,MvPolynomial.degreeOf_le_iff.mpr S.hS⟩
  · intro e he
    simpa [weight_coords,slopeWeights,Nat.mul_comm] using (S.hshape e he).1
  · intro e he
    simpa [weight_coords,middleWeights] using (S.hshape e he).2.1
  · intro e he
    simpa [weight_coords,totalWeights] using (S.hshape e he).2.2

end
end ProximityPrize.SubmissionLower.MovingSourceOwnerRouting6814
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.MovingSourceLinearFlow6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open scoped BigOperators
open MvPolynomial SecondJetCoefficients SecondJetClearedHelper SecondJetHelperWeights
open MovingSourceNativeFactor6814 MovingSourceCarrierField6814 MovingSourceCarrierZeros6814
open RCN234 RCN156

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 4) K

def linearH (J : WholeSpaceCube6814.Poly (K:=K)) : Poly := (asS J).coeff 1
def linearG (J : WholeSpaceCube6814.Poly (K:=K)) : Poly := -2*(asS J).coeff 0

def flow (H G : Poly) : Derivation K Poly Poly :=
  H • RCN055.horizontalDerivation+G • MvPolynomial.pderiv (2 : Fin 4)

theorem flow_apply (H G P : Poly) :
    flow H G P=H*(MvPolynomial.pderiv 0 P+MvPolynomial.X 2*MvPolynomial.pderiv 1 P)+
      G*MvPolynomial.pderiv 2 P := by
  simp only [flow,RCN055.horizontalDerivation,Derivation.add_apply,Derivation.smul_apply,smul_eq_mul]

theorem helper_linear (J : WholeSpaceCube6814.Poly (K:=K)) (F : Poly) :
    helper J F 1 0=linearH J*RCN313.polyG K F-linearG J*RCN313.polyH K F := by
  change (∑ j : Fin 2, (asS J).coeff j.val*(2*RCN313.polyH K F)^(1-j.val)*(RCN313.polyG K F)^j.val)=_
  rw [Fin.sum_univ_two]
  norm_num [linearH,linearG]
  ring

theorem linear_coefficient_weights (J : WholeSpaceCube6814.Poly (K:=K)) (B U T : ℕ)
    (hshape : ∀ e ∈ J.support, 2*e 1+e 3≤B ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T) :
    (wt residualSWeights (linearH J)≤B-2 ∧ wt residualYSWeights (linearH J)≤U-1 ∧
      wt residualTotalWeights (linearH J)≤T-1) ∧
    (wt residualSWeights (linearG J)≤B ∧ wt residualYSWeights (linearG J)≤U ∧
      wt residualTotalWeights (linearG J)≤T) := by
  have hh := derivative_coefficient_weights J B U T 0 1 hshape
  have hg := derivative_coefficient_weights J B U T 0 0 hshape
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hh hg
  have hscale (w : Fin 4 → ℕ) : wt w (linearG J)≤wt w ((asS J).coeff 0) := by
    have hb := wt_mul_le w (-2 : Poly) ((asS J).coeff 0)
    have ht : wt w (2 : Poly)=0 := wt_natCast w 2
    rw [wt_neg,ht,zero_add] at hb
    exact hb
  exact ⟨hh,⟨(hscale _).trans hg.1,(hscale _).trans hg.2.1,(hscale _).trans hg.2.2⟩⟩

theorem linearH_nonzero_on_carrier
    (J : WholeSpaceCube6814.Poly (K:=K)) (hJ : J≠0) (hs : J.degreeOf 1=1)
    (F : Poly) [Fact (Irreducible F)] (T : ℕ)
    (hshape : ∀ e ∈ J.support, e 1+e 2+e 3+e 4≤T) (hFT : T<wt residualTotalWeights F) :
    carrierMap F (linearH J)≠0 := by
  have hh := SecondJetTotalAvoidance.leading_not_dvd J hJ F T hshape hFT
  have he : linearH J=(asS J).leadingCoeff := by
    rw [Polynomial.leadingCoeff,asS_natDegree,hs]
    rfl
  rw [he]
  exact fun hz => hh.2 ((carrierMap_zero_iff F _).mp hz)

theorem carrier_cross_identity [CharP K 2130706433]
    (J : WholeSpaceCube6814.Poly (K:=K)) (hs : J.degreeOf 1=1)
    (F : Poly) [Fact (Irreducible F)]
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hroot : ((asS J).map (carrierMap F)).eval (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=0) :
    F∣linearH J*RCN313.polyG K F-linearG J*RCN313.polyH K F := by
  rw [←helper_linear]
  exact helper_dvd_of_generic_root J F (carrierMap F) (carrierMap_zero_iff F) 1
    (MvPolynomial.degreeOf_le_iff.mp hs.le) (carrier_H_nonzero F hpos hsmall) hroot

theorem flow_carrier (F H G : Poly) :
    flow H G F= -(H*RCN313.polyG K F-G*RCN313.polyH K F) := by
  rw [flow_apply]
  unfold RCN313.polyG RCN313.polyH
  ring

theorem flow_preserves_carrier (F H G : Poly)
    (hcross : F∣H*RCN313.polyG K F-G*RCN313.polyH K F) :
    ∀ P, F∣P → F∣flow H G P := by
  intro P hP
  obtain ⟨Q,rfl⟩ := hP
  rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul]
  apply dvd_add
  · exact dvd_mul_right _ _
  · apply dvd_mul_of_dvd_right
    rw [flow_carrier]
    exact dvd_neg.mpr hcross

end
end ProximityPrize.SubmissionLower.MovingSourceLinearFlow6814
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingSourceFlowNumerator6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN313 MovingSourceLinearFlow6814

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 4) K

def step (H G : Poly) (n : ℕ) (P : Poly) : Poly :=
  clearedStep (2*n) P (pderiv 0 P) (pderiv 1 P) (pderiv 2 P)
    (MvPolynomial.X 2) G H (pderiv 0 H) (pderiv 1 H) (pderiv 2 H)

def numerators (H G : Poly) : ℕ → Poly
  | 0 => MvPolynomial.X 1
  | n+1 => step H G n (numerators H G n)

theorem step_eq (H G P : Poly) (n : ℕ) :
    step H G n P=H*flow H G P-(2*n : ℕ)*P*flow H G H := by
  simp only [step,clearedStep,flow_apply]
  ring

theorem old_numerators (F : Poly) (n : ℕ) :
    numerators (polyH K F) (polyG K F) n=numerator K F n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [numerators,ih,numerator_succ]
    rfl

theorem iterate_eq_fraction
    {E : Type} [Field E] [Algebra K E]
    (D : Derivation K E E) (phi : Poly →+* E) (H G : Poly) (hH : phi H≠0)
    (hchain : ∀ P, D (phi P)=phi (pderiv 0 P)+phi (MvPolynomial.X 2)*phi (pderiv 1 P)+
      phi G*(phi H)⁻¹*phi (pderiv 2 P)) (n : ℕ) :
    D^[n] (phi (MvPolynomial.X 1))=phi (numerators H G n)*(phi H)⁻¹^(2*n) := by
  induction n with
  | zero => simp [numerators]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,numerators,step,map_clearedStep]
    have hu : D ((phi H)⁻¹)= -((phi H)⁻¹^2*
        (phi (pderiv 0 H)+phi (MvPolynomial.X 2)*phi (pderiv 1 H)+
          phi G*(phi H)⁻¹*phi (pderiv 2 H))) := by
      rw [D.leibniz_inv,hchain H]
      simp only [smul_eq_mul,neg_mul]
    have hh := differentiated_fraction_step D (2*n)
      (phi (numerators H G n)) (phi (pderiv 0 (numerators H G n)))
      (phi (pderiv 1 (numerators H G n))) (phi (pderiv 2 (numerators H G n)))
      (phi (MvPolynomial.X 2)) (phi G) (phi H)
      (phi (pderiv 0 H)) (phi (pderiv 1 H)) (phi (pderiv 2 H)) ((phi H)⁻¹)
      (mul_inv_cancel₀ hH) (hchain _) hu
    simpa only [show 2*(n+1)=2*n+2 by omega] using hh

theorem numerator_cross_eq
    {E : Type} [Field E] [Algebra K E]
    (D : Derivation K E E) (phi : Poly →+* E) (H G H' G' : Poly)
    (hH : phi H≠0) (hH' : phi H'≠0)
    (hchain : ∀ P, D (phi P)=phi (pderiv 0 P)+phi (MvPolynomial.X 2)*phi (pderiv 1 P)+
      phi G*(phi H)⁻¹*phi (pderiv 2 P))
    (hchain' : ∀ P, D (phi P)=phi (pderiv 0 P)+phi (MvPolynomial.X 2)*phi (pderiv 1 P)+
      phi G'*(phi H')⁻¹*phi (pderiv 2 P)) (n : ℕ) :
    phi (numerators H G n)*(phi H')^(2*n)=phi (numerators H' G' n)*(phi H)^(2*n) := by
  have hh := (iterate_eq_fraction D phi H G hH hchain n).symm.trans
    (iterate_eq_fraction D phi H' G' hH' hchain' n)
  have he : phi (numerators H G n)/(phi H)^(2*n)=
      phi (numerators H' G' n)/(phi H')^(2*n) := by
    simpa only [div_eq_mul_inv,inv_pow] using hh
  exact (div_eq_div_iff (pow_ne_zero _ hH) (pow_ne_zero _ hH')).mp he

end
end ProximityPrize.SubmissionLower.MovingSourceFlowNumerator6814
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingSourceDenominatorChange6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN313
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814 MovingSourceCarrierField6814

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 4) K

theorem old_flow_stable (F : Poly) :
    ∀ P ∈ Ideal.span ({F} : Set Poly), flow (polyH K F) (polyG K F) P∈Ideal.span ({F} : Set Poly) := by
  intro P hP
  rw [Ideal.mem_span_singleton] at hP ⊢
  apply flow_preserves_carrier F (polyH K F) (polyG K F) ?_ P hP
  rw [mul_comm (polyH K F),sub_self]
  exact dvd_zero F

def quotientD (F : Poly) : Derivation K (CarrierRing F) (CarrierRing F) :=
  RCN077.quotientDerivation (flow (polyH K F) (polyG K F)) _ (old_flow_stable F)

def carrierD (F : Poly) [Fact (Irreducible F)] : Derivation K (CarrierField F) (CarrierField F) :=
  (carrierMap F (polyH K F))⁻¹ •
    RCN188.localizationDerivation (nonZeroDivisors (CarrierRing F)) (quotientD F)

theorem carrierD_apply (F : Poly) [Fact (Irreducible F)]
    (hH : carrierMap F (polyH K F)≠0) (P : Poly) :
    carrierD F (carrierMap F P)=carrierMap F (pderiv 0 P)+
      carrierMap F (MvPolynomial.X 2)*carrierMap F (pderiv 1 P)+
      carrierMap F (polyG K F)*(carrierMap F (polyH K F))⁻¹*carrierMap F (pderiv 2 P) := by
  change (carrierMap F (polyH K F))⁻¹*
    RCN188.localizationDerivation (nonZeroDivisors (CarrierRing F)) (quotientD F)
      (algebraMap (CarrierRing F) (CarrierField F) (Ideal.Quotient.mk _ P))=_
  rw [RCN188.localizationDerivation_algebraMap,quotientD,RCN077.quotientDerivation_mk]
  change (carrierMap F (polyH K F))⁻¹*carrierMap F (flow (polyH K F) (polyG K F) P)=_
  rw [flow_apply]
  simp only [map_add,map_mul]
  field_simp

theorem carrierD_new_flow (F : Poly) [Fact (Irreducible F)] (H G : Poly)
    (hOld : carrierMap F (polyH K F)≠0) (hNew : carrierMap F H≠0)
    (hcross : F∣H*polyG K F-G*polyH K F) (P : Poly) :
    carrierD F (carrierMap F P)=carrierMap F (pderiv 0 P)+
      carrierMap F (MvPolynomial.X 2)*carrierMap F (pderiv 1 P)+
      carrierMap F G*(carrierMap F H)⁻¹*carrierMap F (pderiv 2 P) := by
  have hh := (carrierMap_zero_iff F _).mpr hcross
  simp only [map_sub,map_mul] at hh
  have he : carrierMap F (polyG K F)*(carrierMap F (polyH K F))⁻¹=
      carrierMap F G*(carrierMap F H)⁻¹ := by
    field_simp
    linear_combination hh
  rw [carrierD_apply F hOld P,he]

theorem denominator_change (F : Poly) [Fact (Irreducible F)] (H G : Poly)
    (hOld : carrierMap F (polyH K F)≠0) (hNew : carrierMap F H≠0)
    (hcross : F∣H*polyG K F-G*polyH K F) (n : ℕ) :
    F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n := by
  apply (carrierMap_zero_iff F _).mp
  simp only [map_sub,map_mul,map_pow]
  have hh := numerator_cross_eq (carrierD F) (carrierMap F) (polyH K F) (polyG K F)
    H G hOld hNew (carrierD_apply F hOld) (carrierD_new_flow F H G hOld hNew hcross) n
  rw [old_numerators] at hh
  linear_combination hh

theorem linear_denominator_change [CharP K 2130706433]
    (J : WholeSpaceCube6814.Poly (K:=K)) (hJ : J≠0) (hs : J.degreeOf 1=1)
    (F : Poly) [Fact (Irreducible F)]
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (T : ℕ) (hshape : ∀ e ∈ J.support, e 1+e 2+e 3+e 4≤T)
    (hFT : T<RCN234.wt RCN156.residualTotalWeights F)
    (hroot : ((SecondJetCoefficients.asS J).map (carrierMap F)).eval
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=0) (n : ℕ) :
    F∣(linearH J)^(2*n)*numerator K F n-
      (polyH K F)^(2*n)*numerators (linearH J) (linearG J) n := by
  have hH : carrierMap F (polyH K F)≠0 := by
    intro hz
    apply carrier_H_nonzero F hpos hsmall
    rw [map_mul,hz,mul_zero]
  exact denominator_change F (linearH J) (linearG J) hH
    (linearH_nonzero_on_carrier J hJ hs F T hshape hFT)
    (carrier_cross_identity J hs F hpos hsmall hroot) n

theorem tails_associated {R : Type} [CommRing R] [IsDomain R]
    (ev : Poly →+* R) (F H G : Poly) (n : ℕ) (hF : ev F=0)
    (hOld : IsUnit (ev (polyH K F))) (hNew : IsUnit (ev H))
    (hdiv : F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n) :
    Associated (ev (numerator K F n)) (ev (numerators H G n)) := by
  have hh := map_dvd ev hdiv
  rw [hF,zero_dvd_iff,map_sub,map_mul,map_mul,map_pow,map_pow,sub_eq_zero] at hh
  have he : ev (numerator K F n)*(ev H)^(2*n)=
      ev (numerators H G n)*(ev (polyH K F))^(2*n) := by simpa only [mul_comm] using hh
  apply associated_of_dvd_dvd
  · apply (hOld.pow (2*n)).dvd_mul_right.mp
    rw [←he]
    exact dvd_mul_right _ _
  · apply (hNew.pow (2*n)).dvd_mul_right.mp
    rw [he]
    exact dvd_mul_right _ _

end
end ProximityPrize.SubmissionLower.MovingSourceDenominatorChange6814
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.MovingSourceReducedTailWeights6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN234 RCN156
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 4) K

theorem product_derivative_weight
    (w : Fin 4 → ℕ) (A P : Poly) (i : Fin 4) (c d : ℕ)
    (hA : wt w A≤d+w i) (hP : wt w P≤c) :
    wt w (A*pderiv i P)≤c+d := by
  by_cases hi : w i≤c
  · have hp := wt_pderiv_le w P i c hP
    have hm := wt_mul_le w A (pderiv i P)
    omega
  · have hz : pderiv i P=0 := RCN262.pderiv_eq_zero_of_wt_lt w P i (hP.trans_lt (by omega))
    rw [hz,mul_zero]
    simp [wt,MvPolynomial.weightedTotalDegree]

theorem flow_weight
    (w : Fin 4 → ℕ) (H G P : Poly) (c h d : ℕ)
    (hH : wt w H≤h) (hG : wt w G≤d+w 2)
    (hx : h≤d+w 0) (hy : w 2+h≤d+w 1) (hP : wt w P≤c) :
    wt w (flow H G P)≤c+d := by
  have hRH : wt w (MvPolynomial.X 2*H)≤d+w 1 := by
    have hh := wt_mul_le w (MvPolynomial.X 2) H
    rw [wt_X] at hh
    omega
  have h0 := product_derivative_weight w H P 0 c d (hH.trans hx) hP
  have h1 := product_derivative_weight w (MvPolynomial.X 2*H) P 1 c d hRH hP
  have h2 := product_derivative_weight w G P 2 c d hG hP
  have he : flow H G P=H*pderiv 0 P+(MvPolynomial.X 2*H)*pderiv 1 P+G*pderiv 2 P := by
    rw [flow_apply]
    ring
  rw [he]
  exact (wt_add_le w _ _).trans (max_le
    ((wt_add_le w _ _).trans (max_le h0 h1)) h2)

theorem step_weight
    (w : Fin 4 → ℕ) (H G P : Poly) (c h d n : ℕ)
    (hH : wt w H≤h) (hG : wt w G≤d+w 2)
    (hx : h≤d+w 0) (hy : w 2+h≤d+w 1) (hP : wt w P≤c) :
    wt w (step H G n P)≤c+(h+d) := by
  have hDP := flow_weight w H G P c h d hH hG hx hy hP
  have hDH := flow_weight w H G H h h d hH hG hx hy hH
  have hleft := wt_mul_le w H (flow H G P)
  have hscale := wt_mul_le w ((2*n : ℕ) : Poly) P
  rw [wt_natCast,zero_add] at hscale
  have hright := wt_mul_le w (((2*n : ℕ) : Poly)*P) (flow H G H)
  rw [step_eq]
  exact (wt_sub_le w _ _).trans (max_le (by omega) (by omega))

theorem numerator_weight
    (w : Fin 4 → ℕ) (H G : Poly) (h d : ℕ)
    (hH : wt w H≤h) (hG : wt w G≤d+w 2)
    (hx : h≤d+w 0) (hy : w 2+h≤d+w 1) (n : ℕ) :
    wt w (numerators H G n)≤w 1+n*(h+d) := by
  induction n with
  | zero => simp [numerators,wt_X]
  | succ n ih =>
    have hh := step_weight w H G (numerators H G n) (w 1+n*(h+d)) h d n hH hG hx hy ih
    change wt w (step H G n (numerators H G n))≤_
    convert hh using 1; ring

end
end ProximityPrize.SubmissionLower.MovingSourceReducedTailWeights6814
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN086 RCN136 RCN313
open MovingSourceFlowNumerator6814 MovingSourceDenominatorChange6814

variable {K Ω R : Type} [Field K] [Field Ω] [CommRing R] [IsDomain R]
local notation "Poly" => MvPolynomial (Fin 4) K

theorem global_tails_associated
    (phi : Polynomial K →+* Ω) (hphi : Function.Injective phi)
    (ev : MvPolynomial (Fin 3) Ω →+* R) (F H G : Poly) (n : ℕ)
    (hF : ev (surfaceMap phi F)=0)
    (hOld : IsUnit (ev (surfaceMap phi (polyH K F)))) (hNew : IsUnit (ev (surfaceMap phi H)))
    (hdiv : F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n) :
    Associated (ev (globalTailCut phi F n)) (ev (surfaceMap phi (numerators H G n))) := by
  have hh := tails_associated (ev.comp (surfaceMap phi)) F H G n hF hOld hNew hdiv
  have hu : IsUnit ((-phi Polynomial.X)^n) :=
    isUnit_iff_ne_zero.mpr (tail_scalar_ne_zero phi hphi n)
  have hu' : IsUnit (ev (MvPolynomial.C ((-phi Polynomial.X)^n))) :=
    (hu.map (MvPolynomial.C : Ω →+* MvPolynomial (Fin 3) Ω)).map ev
  rw [globalTailCut_eq,map_mul]
  exact (associated_mul_unit_left _ _ hu').trans hh

end
end ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.MovingSourceReducedPrimary6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
open RCN135 RCN136 RCN074 RCN086 RCN095 RCN244 RCN245 RCN246 RCN248
open RCN002 RCN011 RCN021 RCN093 RCN106 RCN107 RCN120 RCN313
open MovingSourceFlowNumerator6814

theorem primary_cross_transfer
    {R : Type*} [CommRing R] (J : Ideal R) [J.IsMaximal]
    (surface oldTail newTail a b : R) (n : ℕ) (hn : 1≤n)
    (hsurface : surface∈J) (hb : b∉J)
    (hold : oldTail∈Ideal.span {surface} ⊔ J^n)
    (hcross : a*oldTail-b*newTail∈Ideal.span {surface}) :
    newTail∈Ideal.span {surface} ⊔ J^n := by
  let Q := Ideal.span {surface} ⊔ J^n
  have hprod : b*newTail∈Q := by
    have hc : a*oldTail-b*newTail∈Q :=
      (show Ideal.span {surface}≤Q from le_sup_left) hcross
    simpa only [sub_sub_cancel] using Q.sub_mem (Q.mul_mem_left a hold) hc
  exact RCN310.mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
    surface newTail b J hsurface n hn hb hprod

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

theorem reduced_tail_mem_projected_primary
    {B : Type*} [CommRing B]
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (C : FirstTailComponent S)
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (f : MvPolynomial (Fin 4) K →+* B)
    (surface : B) (J : Ideal B) [J.IsMaximal]
    (hfactor : f (originalData S C).factor∈Ideal.span {surface})
    (hsurface : surface∈J)
    (hcontract : Ideal.comap f J=componentPrime S C) :
    f (numerators H G (RCN326.w+1))∈Ideal.span {surface} ⊔
      J^localMultiplicity S (canonicalLocalDVRFamily S hfirst) C := by
  have hold := proper_global_tail_mem_projected_primary S hfirst C f surface
    (f (numerator K S.F (RCN326.w+1))) 1 J hfactor hsurface hcontract (mul_one _).symm
  have hF : f S.F∈Ideal.span {surface} := by
    rw [(originalData S C).product,map_mul]
    exact (Ideal.span {surface}).mul_mem_right _ hfactor
  have hdiff := (Ideal.span {surface}).mem_of_dvd (map_dvd f hcross) hF
  simp only [map_sub,map_mul,map_pow] at hdiff
  have hH : f (polyH K S.F)∉J := by
    intro hh
    have hp : polyH K S.F∈componentPrime S C := by
      rw [←hcontract]
      exact hh
    exact RCN312.firstTailComponent_regularity_not_mem S C hp
  have hpow : (f (polyH K S.F))^(2*(RCN326.w+1))∉J := by
    intro hh
    exact hH ((inferInstance : J.IsPrime).mem_of_pow_mem _ hh)
  exact primary_cross_transfer J surface _ _ _ _ _
    (one_le_localMultiplicity S hfirst C) hsurface hpow hold hdiff

theorem indexed_reduced_tail_mem_primary
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    {A : Type} [Fintype A] (component : A → StageComponent S)
    (lam mu nu : GenericField K) (order : Fin 3 ≃ Fin 3)
    (ht : ∀ a, Transcendental (GenericField K)
      (flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 0))))
    (hfinite : ∀ a,
      letI := flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
      FiniteDimensional (RatFunc (GenericField K)) (CoordinateField (GenericField K) (component a).1))
    (hgen : ∀ a,
      letI := flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
      IntermediateField.adjoin (RatFunc (GenericField K))
        ({flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 2)),
          flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 1))} :
          Set (CoordinateField (GenericField K) (component a).1))=⊤)
    (q : Polynomial (RatFunc (GenericField K))) (hq : Irreducible q)
    (a : IndexedFactorFiber component lam mu nu order ht q) :
    indexedFiberTail q hq
        (RCN113.flagPlaneMap (GenericField K) lam mu nu order
          (surfaceMap (polynomialEmbedding K) (numerators H G (RCN326.w+1))))∈
      Ideal.span {indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)} ⊔
        indexedFiberRelation component lam mu nu order ht q hq a^
          localMultiplicity S (canonicalLocalDVRFamily S hfirst) (component a.1) := by
  let D := indexedFiberProjectionData S component lam mu nu order ht hfinite hgen q hq a
  letI : (indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal := D.relationMax
  exact reduced_tail_mem_projected_primary S hfirst (component a.1) H G hcross
    (stageFiberTargetMap S lam mu nu order q hq)
    (indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)) _
    D.factor_mem D.surface_mem D.contract

end
end ProximityPrize.SubmissionLower.MovingSourceReducedPrimary6814
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.MovingSourceReducedCycle6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN135 RCN136 RCN074 RCN086 RCN095 RCN244 RCN245 RCN246 RCN249 RCN252
open RCN002 RCN011 RCN021 RCN093 RCN106 RCN107 RCN108 RCN109 RCN111 RCN112 RCN113
open RCN120 RCN125 RCN313 RCN333 RCN102
open MovingSourceFlowNumerator6814 MovingSourceReducedPrimary6814

theorem plane_not_dvd_replacement
    {Ω : Type} [Field Ω] {F T R : MvPolynomial (Fin 3) Ω}
    (C : RCN264.RegularComponent Ω F T R)
    (lam mu nu : Ω) (order : Fin 3 ≃ Fin 3)
    (ht : Transcendental Ω
      (flagEvaluation Ω C.1 lam mu nu (MvPolynomial.X (order 0))))
    (hF : Irreducible F) (N : MvPolynomial (Fin 3) Ω) (hN : ¬F∣N) :
    ¬flagPlaneMap Ω lam mu nu order F∣flagPlaneMap Ω lam mu nu order N := by
  have hroot : flagEvaluation Ω C.1 lam mu nu (flagAlgHom lam mu nu F)=0 := by
    rw [flagEvaluation_flag]
    change F∈RingHom.ker (coordinateEvaluation Ω C.1).toRingHom
    rw [coordinateEvaluation_ker]
    exact RCN264.regularComponent_G_mem Ω F T R C
  intro hd
  have hh := (planeMap_dvd_iff_of_evaluation Ω (CoordinateField Ω C.1) order
    (flagEvaluation Ω C.1 lam mu nu) (flagAlgHom lam mu nu F) (flagAlgHom lam mu nu N)
    ((flag_irreducible_iff lam mu nu F).mpr hF) hroot ht).mp hd
  exact hN ((flag_dvd_iff lam mu nu F N).mp hh)

theorem resultant_ne_replacement
    {Ω : Type} [Field Ω] {F T R : MvPolynomial (Fin 3) Ω}
    (C : RCN264.RegularComponent Ω F T R)
    (lam mu nu : Ω) (order : Fin 3 ≃ Fin 3)
    (ht : Transcendental Ω
      (flagEvaluation Ω C.1 lam mu nu (MvPolynomial.X (order 0))))
    (hF : Irreducible F) (N : MvPolynomial (Fin 3) Ω) (hN : ¬F∣N)
    (hpos : 0<(flagPlaneMap Ω lam mu nu order F).natDegree) :
    flagPlaneResultant lam mu nu order F N≠0 := by
  classical
  have hi := RCN103.transformedSurface_irreducible lam mu nu order hF C ht
  have hn := plane_not_dvd_replacement C lam mu nu order ht hF N hN
  exact RCN362.irreducible_resultant_ne_zero_of_not_dvd _ _ hi hpos hn

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

def reducedTailSurface (H G : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 3) (GenericField K) :=
  surfaceMap (polynomialEmbedding K) (numerators H G (RCN326.w+1))

theorem reduced_resultant_ne
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    {A : Type} [Fintype A] (F : StageIndexedFlagFamily S A) (a : A)
    (H G : MvPolynomial (Fin 4) K) (hproper : ¬S.G∣reducedTailSurface H G) :
    flagPlaneResultant F.lam F.mu F.nu F.order S.G (reducedTailSurface H G)≠0 := by
  exact resultant_ne_replacement (F.component a) F.lam F.mu F.nu F.order (F.ht a)
    S.irreducible_G (reducedTailSurface H G) hproper F.positive

theorem reduced_grouped_power_dvd
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hproper : ¬S.G∣reducedTailSurface H G)
    {A : Type} [Fintype A] (F : StageIndexedFlagFamily S A) (W : StageIndexedFactor S A F) :
    W.q^stageFamilyGroupedExponent S A hfirst F W.q∣
      flagPlaneResultant F.lam F.mu F.nu F.order S.G (reducedTailSurface H G) := by
  let surface := stageSurfacePlane S F.lam F.mu F.nu F.order
  let oldTail := stageTailPlane S F.lam F.mu F.nu F.order
  let newTail := flagPlaneMap (GenericField K) F.lam F.mu F.nu F.order (reducedTailSurface H G)
  letI : (Ideal.span {indexedFiberSurface W.q W.irreducible surface}).IsPrime :=
    indexedFiberSurface_span_isPrime F.component F.lam F.mu F.nu F.order F.ht
      S.irreducible_G W.q W.irreducible W.witness
  have hsurface := indexedStageSurface_mem_relation S F.component F.lam F.mu F.nu F.order F.ht
  have holdRoot : ∀ a : IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q,
      oldTail∈relationKernel (GenericField K) (CoordinateField (GenericField K) (F.component a.1).1)
        F.order (flagEvaluation (GenericField K) (F.component a.1).1 F.lam F.mu F.nu) (F.ht a.1) := by
    intro a
    exact flagPlaneMap_mem_relation (F.component a.1).1 F.lam F.mu F.nu F.order (F.ht a.1)
      (RCN264.regularComponent_T_mem (GenericField K) S.G _ _ (F.component a.1))
  have holdProper : indexedFiberTail W.q W.irreducible oldTail∉
      Ideal.span {indexedFiberSurface W.q W.irreducible surface} :=
    indexedFiberTail_not_mem_surface F.component F.lam F.mu F.nu F.order F.ht
      S.irreducible_G hfirst W.q W.irreducible W.witness
  have hbar := indexedFiberRelationBar_ne_bot F.component F.lam F.mu F.nu F.order F.ht
    W.q W.irreducible surface oldTail holdRoot holdProper
  have htail := indexed_reduced_tail_mem_primary S hfirst H G hcross F.component
    F.lam F.mu F.nu F.order F.ht F.finite F.generates W.q W.irreducible
  have hres : Polynomial.resultant surface newTail surface.natDegree newTail.natDegree≠0 :=
    reduced_resultant_ne S F W.witness.1 H G hproper
  have hmod : (indexedFiberSurface W.q W.irreducible surface).map
      (IsLocalRing.residue (FiberCoefficient W.q W.irreducible))≠0 :=
    stageFamily_surface_mod_ne S F W
  exact indexedFixedFactor_grouped_resultant_power_dvd_of_geometry F.component F.injective
    F.lam F.mu F.nu F.order F.ht F.finite F.generates W.q W.irreducible W.monic
    surface newTail surface.natDegree newTail.natDegree
    (fun a => hsurface a.1) hbar
    (fun a => localMultiplicity S (canonicalLocalDVRFamily S hfirst) (F.component a.1))
    htail Polynomial.natDegree_map_le Polynomial.natDegree_map_le hres hmod

theorem reduced_projection_sum_le
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hproper : ¬S.G∣reducedTailSurface H G)
    {A : Type} [Fintype A] (F : StageIndexedFlagFamily S A)
    (hgate : ∀ a, ∀ hx : Transcendental (GenericField K)
        (flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu
          (MvPolynomial.X (F.order 0))),
      (letI := flagBaseAlgebra (GenericField K) (F.component a).1 F.lam F.mu F.nu F.order hx;
        FiniteDimensional (RatFunc (GenericField K)) (CoordinateField (GenericField K) (F.component a).1)) ∧
      (letI := flagBaseAlgebra (GenericField K) (F.component a).1 F.lam F.mu F.nu F.order hx;
        Algebra.IsSeparable (RatFunc (GenericField K)) (CoordinateField (GenericField K) (F.component a).1)))
    (axis : MovingSourceProjectionFamily6814.Axis) (horder : F.order=axis.order)
    (surfaceFlag tailFlag : FlagDegree)
    (hSflag : RCN095.PolynomialInFlag surfaceFlag S.G)
    (hTflag : RCN095.PolynomialInFlag tailFlag (reducedTailSurface H G)) :
    (∑ a, localMultiplicity S (canonicalLocalDVRFamily S hfirst) (F.component a)*
      RCN344.coordinateDegree (GenericField K) (CoordinateField (GenericField K) (F.component a).1)
        (RCN042.coordinateOfGate
          (flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu
            (MvPolynomial.X (F.order 0))) (hgate a))) ≤
      RCN095.flagMixed surfaceFlag tailFlag axis.flag := by
  classical
  by_cases hA : Nonempty A
  · let a0 : A := Classical.choice hA
    have hres := reduced_resultant_ne S F a0 H G hproper
    have hTne : reducedTailSurface H G≠0 := fun hz => hproper (hz ▸ dvd_zero _)
    have hdegree : (flagPlaneResultant F.lam F.mu F.nu F.order S.G
        (reducedTailSurface H G)).natDegree ≤ RCN095.flagMixed surfaceFlag tailFlag axis.flag := by
      rw [horder]
      exact MovingSourceProjectionFamily6814.flag_resultant_degree_le axis F.lam F.mu F.nu
        S.G (reducedTailSurface H G) surfaceFlag tailFlag hSflag hTflag hTne
    let channel := RCN104.indexedWeightedFlagPlaneChannel_of_fixedFactors F.component F.lam F.mu F.nu
      F.order F.ht F.finite F.generates hgate
      (fun a => localMultiplicity S (canonicalLocalDVRFamily S hfirst) (F.component a))
      (flagPlaneResultant F.lam F.mu F.nu F.order S.G (reducedTailSurface H G))
      (RCN095.flagMixed surfaceFlag tailFlag axis.flag) hres hdegree
      (fun q hq hmonic a => reduced_grouped_power_dvd S hfirst H G hcross hproper F
        ⟨q,hq,hmonic,a⟩)
    exact channel.sum_mul_cost_le
  · letI : IsEmpty A := ⟨fun a => hA ⟨a⟩⟩
    simp

end
end ProximityPrize.SubmissionLower.MovingSourceReducedCycle6814
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.MovingSourceReducedGamma6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
open RCN135 RCN136 RCN074 RCN086 RCN095 RCN244 RCN264 RCN313
open RCN002 RCN022 RCN037 RCN042 RCN093 RCN341
open MovingSourceFlowNumerator6814 MovingSourceReducedCycle6814
open MovingSourceProjectionFamily6814 MovingSourceAutomaticProjection6814
open MovingSourceLinearFlow6814

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

theorem reducedTail_mem_old_component
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (C : FirstTailComponent S) : reducedTailSurface H G∈C.1 := by
  let ev := surfaceMap (polynomialEmbedding K)
  have hF : ev S.F∈C.1 := RCN312.firstTailComponent_surface_mem S C
  have hold : ev (numerator K S.F (RCN326.w+1))∈C.1 :=
    (RCN330.globalTailCut_mem_iff (polynomialEmbedding K) (polynomialEmbedding_injective K)
      S.F (RCN326.w+1) C.1).mp
      (regularComponent_T_mem (GenericField K) S.G _ _ C)
  have hc := C.1.mem_of_dvd (map_dvd ev hcross) hF
  simp only [map_sub,map_mul,map_pow] at hc
  have hm := C.1.sub_mem (C.1.mul_mem_left ((ev H)^(2*(RCN326.w+1))) hold) hc
  simp only [sub_sub_cancel] at hm
  have hprime : C.1.IsPrime := inferInstance
  have hOld : (ev (polyH K S.F))^(2*(RCN326.w+1))∉C.1 := by
    intro hh
    exact RCN312.firstTailComponent_regularity_not_mem S C
      (hprime.mem_of_pow_mem _ hh)
  exact (hprime.mem_or_mem hm).resolve_left hOld

theorem reducedTail_proper
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hH : ¬S.G∣surfaceMap (polynomialEmbedding K) H) : ¬S.G∣reducedTailSurface H G := by
  let ev := surfaceMap (polynomialEmbedding K)
  have hc := S.G_dvd_surface.trans (map_dvd ev hcross)
  simp only [map_sub,map_mul,map_pow] at hc
  intro hd
  change S.G∣ev (numerators H G (RCN326.w+1)) at hd
  have hprod := hc.add (dvd_mul_of_dvd_right hd ((ev (polyH K S.F))^(2*(RCN326.w+1))))
  rw [sub_add_cancel] at hprod
  have hpow : ¬S.G∣(ev H)^(2*(RCN326.w+1)) :=
    fun hh => hH (S.irreducible_G.prime.dvd_of_dvd_pow hh)
  have hraw := (S.irreducible_G.prime.dvd_or_dvd hprod).resolve_left hpow
  apply hfirst
  rw [globalTailCut_eq]
  exact dvd_mul_of_dvd_left hraw _

theorem surface_flag_of_caps
    {Ω : Type} [Field Ω] (phi : Polynomial K →+* Ω)
    (N : MvPolynomial (Fin 4) K) (B A C : ℕ) (hBA : B≤A) (hAC : A≤C)
    (hB : RCN234.wt RCN156.residualSWeights N≤B)
    (hA : RCN234.wt RCN156.residualYSWeights N≤A)
    (hC : RCN234.wt RCN156.residualTotalWeights N≤C) :
    PolynomialInFlag ⟨C-A,A-B,B⟩ (surfaceMap phi N) := by
  intro e he
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp (support_surfaceMap_subset phi N he)
  have hb := (MvPolynomial.le_weightedTotalDegree RCN156.residualSWeights hd).trans hB
  have ha := (MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights hd).trans hA
  have hc := (MvPolynomial.le_weightedTotalDegree RCN156.residualTotalWeights hd).trans hC
  rw [RCN081.weight_fin4] at hb ha hc
  simp [RCN156.residualSWeights,RCN156.residualYSWeights,RCN156.residualTotalWeights] at hb ha hc
  change d 2≤B ∧ d 1+d 2≤A-B+B ∧ d 1+d 2+d 3≤C-A+(A-B)+B
  omega

theorem reduced_gamma_gate
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hproper : ¬S.G∣reducedTailSurface H G)
    (surfaceFlag tailFlag : FlagDegree)
    (hS : PolynomialInFlag surfaceFlag S.G)
    (hT : PolynomialInFlag tailFlag (reducedTailSurface H G))
    (hsmall : flagMixed surfaceFlag tailFlag unitZFlag<p)
    (C : FirstTailComponent S) : LiteralProjectionGate C 2 := by
  intro ht
  have ht' : Transcendental (GenericField K)
      (flagEvaluation (GenericField K) C.1 0 0 0 (MvPolynomial.X (Axis.z.order 0))) := by
    simpa [Axis.order,RCN125.zOrder] using ht
  have he := RCN116.elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.zOrder])
  have hh := prime_projection_gate C.1 .z 0 0 0 ht' S.G (reducedTailSurface H G)
    S.irreducible_G.ne_zero (fun hz => hproper (hz ▸ dvd_zero _))
    (S.irreducible_G.isRelPrime_iff_not_dvd.mpr hproper)
    (regularComponent_G_mem (GenericField K) S.G _ _ C)
    (reducedTail_mem_old_component S H G hcross C) surfaceFlag tailFlag hS hT p hsmall
  rw [he] at hh
  exact hh

end
end ProximityPrize.SubmissionLower.MovingSourceReducedGamma6814
end MergedPart9
section MergedPart10
namespace ProximityPrize.SubmissionLower.MovingSourceGammaProjections6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped Classical WithZero
open RCN002 RCN022 RCN035 RCN042 RCN044 RCN093 RCN096 RCN099 RCN116 RCN341 RCN344

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem affine_poles_everywhere
    (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (base : SeparableLiteralCoordinate P)
    (a : Ω) (ha : a≠0) (x y : CoordinateField Ω P)
    (hval : ∀ v∈literalRelevantPlaces base, v.val (x+a • y)=max (v.val x) (v.val y))
    (hout : ∀ v : Place Ω (CoordinateField Ω P), v∉literalRelevantPlaces base →
      RCN187.poleOrder v.val x=0 ∧ RCN187.poleOrder v.val y=0)
    (v : Place Ω (CoordinateField Ω P)) :
    RCN187.poleOrder v.val (x+a • y)=max (RCN187.poleOrder v.val x) (RCN187.poleOrder v.val y) := by
  by_cases hv : v∈literalRelevantPlaces base
  · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (hval v hv)
  · obtain ⟨hx,hy⟩ := hout v hv
    have hxle := valuation_le_one_of_poleOrder_eq_zero v.val _ hx
    have hyle := valuation_le_one_of_poleOrder_eq_zero v.val _ hy
    letI : v.val.IsTrivialOn Ω := v.property.2
    have hs : v.val (a • y)=v.val y := by
      rw [Algebra.smul_def,map_mul,Valuation.IsTrivialOn.eq_one a ha,one_mul]
    have hle : v.val (x+a • y)≤1 :=
      (v.val.map_add _ _).trans (by rw [hs]; exact max_le hxle hyle)
    have hzero : RCN187.poleOrder v.val (x+a • y)=0 :=
      RCN346.poleOrder_eq_zero_of_le_one Ω (CoordinateField Ω P) v _ hle
    rw [hzero,hx,hy]
    rfl

structure GammaFrame {A : Type} [Fintype A]
    (P : A → Ideal (MvPolynomial (Fin 3) Ω)) [∀ a,(P a).IsPrime]
    (surface : MvPolynomial (Fin 3) Ω) where
  lam : Ω
  mu : Ω
  lam_ne : lam≠0
  mu_ne : mu≠0
  uTranscendental : ∀ a, Transcendental Ω (affineU Ω (P a) lam)
  vTranscendental : ∀ a, Transcendental Ω (affineV Ω (P a) mu (mu*lam))
  uFinite : ∀ a,
    letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (affineU Ω (P a) lam)
      (uTranscendental a)).toRingHom.toAlgebra
    FiniteDimensional (RatFunc Ω) (CoordinateField Ω (P a))
  uSeparable : ∀ a,
    letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (affineU Ω (P a) lam)
      (uTranscendental a)).toRingHom.toAlgebra
    Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (P a))
  vFinite : ∀ a,
    letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (affineV Ω (P a) mu (mu*lam))
      (vTranscendental a)).toRingHom.toAlgebra
    FiniteDimensional (RatFunc Ω) (CoordinateField Ω (P a))
  vSeparable : ∀ a,
    letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (affineV Ω (P a) mu (mu*lam))
      (vTranscendental a)).toRingHom.toAlgebra
    Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (P a))
  uPole : ∀ a (v : Place Ω (CoordinateField Ω (P a))),
    RCN187.poleOrder v.val (affineU Ω (P a) lam)=
      max (RCN187.poleOrder v.val (coordinate Ω (P a) 0))
        (RCN187.poleOrder v.val (coordinate Ω (P a) 2))
  vPole : ∀ a (v : Place Ω (CoordinateField Ω (P a))),
    RCN187.poleOrder v.val (affineV Ω (P a) mu (mu*lam))=
      max (RCN187.poleOrder v.val (coordinate Ω (P a) 1))
        (max (RCN187.poleOrder v.val (coordinate Ω (P a) 0))
          (RCN187.poleOrder v.val (coordinate Ω (P a) 2)))
  directional : MvPolynomial.pderiv (0 : Fin 3) surface-
    MvPolynomial.C mu*MvPolynomial.pderiv (1 : Fin 3) surface≠0

theorem exists_gamma_frame
    {A : Type} [Fintype A]
    (P : A → Ideal (MvPolynomial (Fin 3) Ω)) [∀ a,(P a).IsPrime]
    (hz : ∀ a, Transcendental Ω (coordinate Ω (P a) 2))
    (hgate : ∀ a,
      (letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
        (hz a)).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc Ω) (CoordinateField Ω (P a))) ∧
      (letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
        (hz a)).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (P a))))
    (surface : MvPolynomial (Fin 3) Ω) (hderiv : MvPolynomial.pderiv (1 : Fin 3) surface≠0) :
    Nonempty (GammaFrame P surface) := by
  classical
  let base (a : A) : SeparableLiteralCoordinate (P a) := ⟨2,hz a,(hgate a).1,(hgate a).2⟩
  let E (a : A) := CoordinateField Ω (P a)
  let z (a : A) : E a := coordinate Ω (P a) 2
  let y (a : A) : E a := coordinate Ω (P a) 0
  let r (a : A) : E a := coordinate Ω (P a) 1
  let W (a : A) := literalRelevantPlaces (base a)
  let bases (a : A) := literalToSeparableCoordinate (base a)
  have hzD (a : A) : KaehlerDifferential.D Ω (E a) (z a)≠0 :=
    differential_ne_zero_of_gate _ (hz a) (hgate a)
  obtain ⟨lam,hlam0,hlam⟩ := exists_common_exact_finite_separable_affine_adaptive
    E y z W bases (fun a => Or.inr (hzD a))
  let U (a : A) : E a := y a+lam • z a
  have huPole (a : A) (v : Place Ω (E a)) :
      RCN187.poleOrder v.val (U a)=max (RCN187.poleOrder v.val (y a)) (RCN187.poleOrder v.val (z a)) := by
    exact affine_poles_everywhere (P a) (base a) lam hlam0 (y a) (z a)
      (hlam a).choose_spec.2.2
      (fun v hv => ⟨coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant (base a) v hv 0,
        coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant (base a) v hv 2⟩) v
  have huD (a : A) : KaehlerDifferential.D Ω (E a) (U a)≠0 :=
    differential_ne_zero_of_gate _ (hlam a).choose
      ⟨(hlam a).choose_spec.1,(hlam a).choose_spec.2.1⟩
  let Extra (mu : Ω) := MvPolynomial.pderiv (0 : Fin 3) surface-
    MvPolynomial.C mu*MvPolynomial.pderiv (1 : Fin 3) surface=0
  have hextra : ∀ {a b}, Extra a → Extra b → a=b :=
    directional_bad_coefficient_subsingleton surface hderiv
  obtain ⟨mu,hmu0,hdir,hmu⟩ := exists_common_exact_finite_separable_affine_adaptive_avoiding_one
    E r U W Extra hextra bases (fun a => Or.inr (huD a))
  let V (a : A) : E a := r a+mu • U a
  have hvPole (a : A) (v : Place Ω (E a)) :
      RCN187.poleOrder v.val (V a)=max (RCN187.poleOrder v.val (r a)) (RCN187.poleOrder v.val (U a)) := by
    apply affine_poles_everywhere (P a) (base a) mu hmu0 (r a) (U a) (hmu a).choose_spec.2.2 ?_ v
    intro v hv
    refine ⟨coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant (base a) v hv 1,?_⟩
    rw [huPole a v]
    rw [coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant (base a) v hv 0,
      coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant (base a) v hv 2]
    rfl
  have hvEq (a : A) : affineV Ω (P a) mu (mu*lam)=V a := by
    simp only [V,U,r,y,z,affineV,smul_add,smul_smul,add_assoc]
  have hvt (a : A) : Transcendental Ω (affineV Ω (P a) mu (mu*lam)) :=
    hvEq a ▸ (hmu a).choose
  have hev (a : A) :
      elementEmbedding Ω (E a) (affineV Ω (P a) mu (mu*lam)) (hvt a)=
        elementEmbedding Ω (E a) (V a) (hmu a).choose :=
    elementEmbedding_congr (hvt a) (hmu a).choose (hvEq a)
  refine ⟨{
    lam := lam, mu := mu, lam_ne := hlam0, mu_ne := hmu0
    uTranscendental := fun a => (hlam a).choose
    vTranscendental := hvt
    uFinite := fun a => (hlam a).choose_spec.1
    uSeparable := fun a => (hlam a).choose_spec.2.1
    vFinite := ?_, vSeparable := ?_, uPole := huPole
    vPole := ?_, directional := hdir }⟩
  · intro a
    rw [hev a]
    exact (hmu a).choose_spec.1
  · intro a
    rw [hev a]
    exact (hmu a).choose_spec.2.1
  · intro a v
    rw [hvEq a,hvPole a v,huPole a v]

end
end ProximityPrize.SubmissionLower.MovingSourceGammaProjections6814
end MergedPart10
section MergedPart11
namespace ProximityPrize.SubmissionLower.MovingSourceLinearCycleFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators
open RCN002 RCN022 RCN042 RCN093 RCN095 RCN116 RCN117 RCN125
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814
open MovingSourceGammaProjections6814

section General
variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
variable {A : Type} [Fintype A]
variable {P : A → Ideal (MvPolynomial (Fin 3) Ω)} [∀ a,(P a).IsPrime]
variable {surface : MvPolynomial (Fin 3) Ω}

theorem frame_trans (D : GammaFrame P surface)
    (hz : ∀ a, Transcendental Ω (coordinate Ω (P a) 2)) (axis : Axis) (a : A) :
    Transcendental Ω (flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam)
      (MvPolynomial.X (axis.order 0))) := by
  cases axis with
  | z => simpa [Axis.order,zOrder] using hz a
  | u => simpa [Axis.order,uOrder] using D.uTranscendental a
  | v => simpa [Axis.order,vOrder] using D.vTranscendental a

theorem frame_gate (D : GammaFrame P surface)
    (hz : ∀ a, Transcendental Ω (coordinate Ω (P a) 2))
    (hgate : ∀ a,
      (letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
        (hz a)).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc Ω) (CoordinateField Ω (P a))) ∧
      (letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
        (hz a)).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (P a))))
    (axis : Axis) (a : A)
    (ht : Transcendental Ω (flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam)
      (MvPolynomial.X (axis.order 0)))) :
    (letI := (elementEmbedding Ω (CoordinateField Ω (P a))
      (flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0)))
      ht).toRingHom.toAlgebra;
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω (P a))) ∧
    (letI := (elementEmbedding Ω (CoordinateField Ω (P a))
      (flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0)))
      ht).toRingHom.toAlgebra;
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (P a))) := by
  cases axis with
  | z =>
    have he := elementEmbedding_congr ht (hz a) (by simp [Axis.order,zOrder])
    rw [he]
    exact hgate a
  | u =>
    have he := elementEmbedding_congr ht (D.uTranscendental a) (by simp [Axis.order,uOrder])
    rw [he]
    exact ⟨D.uFinite a,D.uSeparable a⟩
  | v =>
    have he := elementEmbedding_congr ht (D.vTranscendental a) (by simp [Axis.order,vOrder])
    rw [he]
    exact ⟨D.vFinite a,D.vSeparable a⟩

def frameCost (D : GammaFrame P surface)
    (hz : ∀ a, Transcendental Ω (coordinate Ω (P a) 2)) (axis : Axis) (a : A) : ℕ :=
  letI := (elementEmbedding Ω (CoordinateField Ω (P a))
    (flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0)))
    (frame_trans D hz axis a)).toRingHom.toAlgebra
  Module.finrank (RatFunc Ω) (CoordinateField Ω (P a))
end General

open RCN135 RCN136 RCN074 RCN086 RCN244 RCN245 RCN249 RCN313
open MovingSourceFlowNumerator6814 MovingSourceReducedCycle6814 MovingSourceReducedGamma6814
variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

theorem exists_reduced_cycle_family
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hH : ¬S.G∣surfaceMap (polynomialEmbedding K) H)
    {A : Type} [Fintype A] (component : A → FirstTailComponent S)
    (hinj : Function.Injective component)
    (hz : ∀ a, Transcendental (GenericField K) (coordinate (GenericField K) (component a).1 2))
    (surfaceFlag tailFlag : FlagDegree)
    (hS : RCN095.PolynomialInFlag surfaceFlag S.G)
    (hT : RCN095.PolynomialInFlag tailFlag (reducedTailSurface H G))
    (hsmall : flagMixed surfaceFlag tailFlag unitZFlag<p) :
    ∃ D : GammaFrame (fun a => (component a).1) S.G, ∀ axis : Axis,
      (∑ a, localMultiplicity S (canonicalLocalDVRFamily S hfirst) (component a)*frameCost D hz axis a) ≤
        flagMixed surfaceFlag tailFlag axis.flag := by
  classical
  have hproper := reducedTail_proper S hfirst H G hcross hH
  have hgate (a : A) := reduced_gamma_gate S H G hcross hproper surfaceFlag tailFlag hS hT hsmall
    (component a) (hz a)
  have hderiv := RCN315.residualStage_pderiv_one_ne_zero_of_support S
  obtain ⟨D⟩ := exists_gamma_frame (fun a => (component a).1) hz hgate S.G hderiv
  refine ⟨D,fun axis => ?_⟩
  let F : StageIndexedFlagFamily S A := {
    component := component, injective := hinj
    lam := D.lam, mu := D.mu, nu := D.mu*D.lam, order := axis.order
    ht := frame_trans D hz axis
    finite := fun a => (frame_gate D hz hgate axis a (frame_trans D hz axis a)).1
    generates := fun a => flag_generators_axis (GenericField K) (component a).1
      axis D.lam D.mu (D.mu*D.lam) (frame_trans D hz axis a)
    positive := by
      cases axis with
      | z => exact (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hderiv).2
      | u => exact (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hderiv).1
      | v => exact flag_v_outer_positive_of_directional D.lam D.mu S.G D.directional }
  have hb := reduced_projection_sum_le S hfirst H G hcross hproper F
    (frame_gate D hz hgate axis) axis rfl surfaceFlag tailFlag hS hT
  have he (a : A) :
      RCN344.coordinateDegree (GenericField K) (CoordinateField (GenericField K) (component a).1)
        (coordinateOfGate
          (flagEvaluation (GenericField K) (component a).1 D.lam D.mu (D.mu*D.lam)
            (MvPolynomial.X (axis.order 0))) (frame_gate D hz hgate axis a))=frameCost D hz axis a :=
    coordinateOfGate_degree_of_transcendental _ _ (frame_trans D hz axis a)
  simpa only [F,he] using hb

end
end ProximityPrize.SubmissionLower.MovingSourceLinearCycleFamily6814
end MergedPart11
section MergedPart12
namespace ProximityPrize.SubmissionLower.MovingSourceFrameZeroCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators WithZero
open RCN002 RCN022 RCN042 RCN093 RCN095 RCN114 RCN165 RCN295 RCN341 RCN344
open MovingSourceProjectionFamily6814 MovingSourceGammaProjections6814
open MovingSourceLinearCycleFamily6814

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
variable {A : Type} [Fintype A]
variable {P : A → Ideal (MvPolynomial (Fin 3) Ω)} [∀ a,(P a).IsPrime]
variable {surface : MvPolynomial (Fin 3) Ω}
variable (D : GammaFrame P surface)
variable (hz : ∀ a, Transcendental Ω (coordinate Ω (P a) 2))
variable (hgate : ∀ a,
  (letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
    (hz a)).toRingHom.toAlgebra;
    FiniteDimensional (RatFunc Ω) (CoordinateField Ω (P a))) ∧
  (letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
    (hz a)).toRingHom.toAlgebra;
    Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (P a))))

include hgate in
theorem frame_unit_poles (axis : Axis) (a : A)
    (W : Finset (Place Ω (CoordinateField Ω (P a)))) :
    (∑ v∈W, exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport axis.flag)) ≤
      (frameCost D hz axis a : ℤ) := by
  let projection := coordinateOfGate
    (flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0)))
    (frame_gate D hz hgate axis a)
  have he : coordinateDegree Ω (CoordinateField Ω (P a)) projection=frameCost D hz axis a :=
    coordinateOfGate_degree_of_transcendental _ _ (frame_trans D hz axis a)
  have hp (v : Place Ω (CoordinateField Ω (P a))) :
      exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport axis.flag)=
        RCN346.poleOrder Ω (CoordinateField Ω (P a)) v
          (coordinateValue Ω (CoordinateField Ω (P a)) projection) := by
    dsimp only [projection]
    rw [coordinateOfGate_value]
    change _=RCN187.poleOrder v.val _
    cases axis with
    | z => simp only [Axis.flag,Axis.order,RCN125.zOrder,Equiv.swap_apply_left,
        flagEvaluation_X_two,exponentSetPoleWeight_unitZ]
    | u =>
      simp only [Axis.flag,Axis.order,RCN125.uOrder,Equiv.refl_apply,
        flagEvaluation_X_zero,exponentSetPoleWeight_unitYZ]
      exact (D.uPole a v).symm
    | v =>
      simp only [Axis.flag,Axis.order,RCN125.vOrder,Equiv.swap_apply_left,
        flagEvaluation_X_one,exponentSetPoleWeight_unitAll]
      exact (D.vPole a v).symm
  calc
    _=∑ v∈W, RCN346.poleOrder Ω (CoordinateField Ω (P a)) v
        (coordinateValue Ω (CoordinateField Ω (P a)) projection) :=
      Finset.sum_congr rfl (fun v _ => hp v)
    _≤(coordinateDegree Ω (CoordinateField Ω (P a)) projection : ℤ) :=
      finite_sum_coordinate_pole_le_degree Ω (CoordinateField Ω (P a)) projection W
    _= _ := by rw [he]

def frameFlagCost (a : A) (r : FlagDegree) : ℕ :=
  r.zOnly*frameCost D hz .z a+r.yz*frameCost D hz .u a+r.all*frameCost D hz .v a

def frame_prime_budget (a : A) : PrimeFlagZeroBudget (P a) (frameFlagCost D hz a) := by
  classical
  let base : SeparableLiteralCoordinate (P a) := ⟨2,hz a,(hgate a).1,(hgate a).2⟩
  refine ⟨?_⟩
  intro r N hN hproper points hpointsP hpointsN
  have hpole : ∀ W : Finset (Place Ω (CoordinateField Ω (P a))),
      (∑ v∈W, exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport r)) ≤
        (frameFlagCost D hz a r : ℤ) := by
    intro W
    have hz' := frame_unit_poles D hz hgate .z a W
    have hu' := frame_unit_poles D hz hgate .u a W
    have hv' := frame_unit_poles D hz hgate .v a W
    calc
      _≤∑ v∈W, ((r.zOnly : ℤ)*exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitZFlag)+
          (r.yz : ℤ)*exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitYZFlag)+
          (r.all : ℤ)*exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitAllFlag)) :=
        Finset.sum_le_sum (fun v _ => exponentSetPoleWeight_flagSupport_le_three v.val (coordinate Ω (P a)) r)
      _=(r.zOnly : ℤ)*(∑ v∈W, exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitZFlag))+
          (r.yz : ℤ)*(∑ v∈W, exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitYZFlag))+
          (r.all : ℤ)*(∑ v∈W, exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitAllFlag)) := by
        simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _≤(r.zOnly : ℤ)*(frameCost D hz .z a : ℤ)+
          (r.yz : ℤ)*(frameCost D hz .u a : ℤ)+(r.all : ℤ)*(frameCost D hz .v a : ℤ) :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hz' (by positivity))
          (mul_le_mul_of_nonneg_left hu' (by positivity)))
          (mul_le_mul_of_nonneg_left hv' (by positivity))
      _= _ := by simp only [frameFlagCost,Nat.cast_add,Nat.cast_mul]
  exact finite_zero_points_le_exponentSet_of_literalCoordinate (P a) base
    (flagSupport r) (frameFlagCost D hz a r) hpole N
    ((support_subset_flagSupport_iff r N).mpr hN) hproper points hpointsP hpointsN

end
end ProximityPrize.SubmissionLower.MovingSourceFrameZeroCount6814
end MergedPart12
section MergedPart13
namespace ProximityPrize.SubmissionLower.MovingSourceReducedSeedTails6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
open RCN002 RCN135 RCN136 RCN074 RCN086 RCN095 RCN238 RCN243 RCN244 RCN264 RCN313 RCN330
open MovingSourceFlowNumerator6814 MovingSourceLinearTailTransport6814
open MovingSourceReducedGamma6814 MovingSourceLinearFlow6814

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

theorem reduced_selected_tail_zero
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (H G : MvPolynomial (Fin 4) K) (n : ℕ) (hn : RCN326.w<n)
    (hcross : S.F∣H^(2*n)*numerator K S.F n-(polyH K S.F)^(2*n)*numerators H G n)
    (gamma : K) (hgamma : gamma∈Gamma) :
    MvPolynomial.aeval (selectedPoint (polynomialEmbedding K) S.selected gamma)
      (surfaceMap (polynomialEmbedding K) (numerators H G n))=0 := by
  let f : MvPolynomial (Fin 3) (GenericField K) →+* GenericField K :=
    (MvPolynomial.aeval (selectedPoint (polynomialEmbedding K) S.selected gamma)).toRingHom
  let ev := f.comp (surfaceMap (polynomialEmbedding K))
  have hF : ev S.F=0 := by
    have hh := map_dvd f S.G_dvd_surface
    have hG : f S.G=0 := S.on_component gamma hgamma
    rw [hG,zero_dvd_iff] at hh
    exact hh
  have holdGlobal : globalTailCut (polynomialEmbedding K) S.F n∈RingHom.ker f :=
    selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F S.selected gamma RCN326.w n
      (S.degree_le gamma hgamma) (S.solution gamma hgamma) hn
  have hold : ev (numerator K S.F n)=0 :=
    (globalTailCut_mem_iff (polynomialEmbedding K) (polynomialEmbedding_injective K)
      S.F n (RingHom.ker f)).mp holdGlobal
  have hOld : ev (polyH K S.F)≠0 := by
    change MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
      (surfaceMap (polynomialEmbedding K) (MvPolynomial.pderiv (2 : Fin 4) S.F))≠0
    rw [selectedPoint_evaluation]
    exact S.regular gamma hgamma
  have he := map_dvd ev hcross
  rw [hF,zero_dvd_iff,map_sub,map_mul,map_mul,map_pow,map_pow,hold,mul_zero,
    zero_sub,neg_eq_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hOld)

theorem reduced_tail_proper_on_component
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (C : FirstTailComponent S) (H G : MvPolynomial (Fin 4) K) (n : ℕ)
    (hcross : S.F∣H^(2*n)*numerator K S.F n-(polyH K S.F)^(2*n)*numerators H G n)
    (hH : surfaceMap (polynomialEmbedding K) H∉C.1)
    (hproper : globalTailCut (polynomialEmbedding K) S.F n∉C.1) :
    surfaceMap (polynomialEmbedding K) (numerators H G n)∉C.1 := by
  let ev := (coordinateEvaluation (GenericField K) C.1).toRingHom
  have he (N : MvPolynomial (Fin 3) (GenericField K)) : ev N=0 ↔ N∈C.1 := by
    change N∈RingHom.ker (coordinateEvaluation (GenericField K) C.1).toRingHom ↔ N∈C.1
    rw [coordinateEvaluation_ker]
  have hF := (he _).mpr (RCN312.firstTailComponent_surface_mem S C)
  have hold : IsUnit (ev (surfaceMap (polynomialEmbedding K) (polyH K S.F))) :=
    isUnit_iff_ne_zero.mpr ((he _).not.mpr (RCN312.firstTailComponent_regularity_not_mem S C))
  have hnew : IsUnit (ev (surfaceMap (polynomialEmbedding K) H)) :=
    isUnit_iff_ne_zero.mpr ((he _).not.mpr hH)
  have hassoc := global_tails_associated (polynomialEmbedding K) (polynomialEmbedding_injective K)
    ev S.F H G n hF hold hnew hcross
  intro hmem
  have hh := hassoc.symm.dvd
  rw [(he _).mpr hmem,zero_dvd_iff] at hh
  exact hproper ((he _).mp hh)

end
end ProximityPrize.SubmissionLower.MovingSourceReducedSeedTails6814
end MergedPart13
section MergedPart14
namespace ProximityPrize.SubmissionLower.MovingSourceProperSeedCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN042 RCN074 RCN086 RCN095 RCN121 RCN135 RCN136 RCN238 RCN243 RCN244 RCN264
open MovingSourceGammaProjections6814 MovingSourceLinearCycleFamily6814 MovingSourceProjectionFamily6814
open MovingSourceFrameZeroCount6814 MovingSourceReducedSeedTails6814 MovingSourceReducedGamma6814
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814

private theorem sum_weighted_three {A : Type} [Fintype A]
    (m z u v : A → ℕ) (a b c : ℕ) :
    (∑ i, m i*(a*z i+b*u i+c*v i))=
      a*(∑ i, m i*z i)+b*(∑ i, m i*u i)+c*(∑ i, m i*v i) := by
  simp only [Nat.mul_add,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_left_comm]

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

abbrev stageSeeds (S : Stage K I Gamma x p flag errorCap stageSupport) (C : FirstTailComponent S) :=
  componentSeeds (GenericField K) S.G (globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (regularitySurface (polynomialEmbedding K) S.F) Gamma
    (selectedPoint (polynomialEmbedding K) S.selected) C

abbrev ProperLinearComponent
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H : MvPolynomial (Fin 4) K) :=
  {C : FirstTailComponent S //
    Transcendental (GenericField K) (coordinate (GenericField K) C.1 2) ∧
    surfaceMap (polynomialEmbedding K) H∉C.1 ∧
    ∃ delay, 1≤delay ∧ delay≤localMultiplicity S (canonicalLocalDVRFamily S hfirst) C ∧
      globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1+delay)∉C.1}

end
end ProximityPrize.SubmissionLower.MovingSourceProperSeedCount6814
end MergedPart14
section MergedPart15
namespace ProximityPrize.SubmissionLower.MovingSourceConstantSeeds6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN093 RCN095 RCN135 RCN136 RCN238 RCN243 RCN264
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814
open MovingSourceProperSeedCount6814 MovingSourceReducedGamma6814
open MovingSourceLinearFlow6814

theorem constant_parameter_seeds_le_one
    {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
    (phi : Polynomial K →+* Ω) (selected : K → Polynomial K) (seeds : Finset K)
    (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (hconstant : IsAlgebraic Ω (coordinate Ω P 2))
    (hon : ∀ gamma∈seeds, P≤RingHom.ker (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom) :
    seeds.card≤1 := by
  obtain ⟨c,hc⟩ := RCN370.eq_algebraMap_of_isAlgebraic Ω (CoordinateField Ω P) _ hconstant
  have hmem : MvPolynomial.X (2 : Fin 3)-MvPolynomial.C c∈P := by
    rw [←coordinateEvaluation_ker Ω P]
    change coordinateEvaluation Ω P (MvPolynomial.X 2-MvPolynomial.C c)=0
    rw [coordinateEvaluation_eq_aeval]
    simpa using sub_eq_zero.mpr hc.symm
  have hvalue (gamma : K) (hgamma : gamma∈seeds) : (phi.comp Polynomial.C) gamma=c := by
    have hh := hon gamma hgamma hmem
    change MvPolynomial.aeval (selectedPoint phi selected gamma)
      (MvPolynomial.X (2 : Fin 3)-MvPolynomial.C c)=0 at hh
    simpa only [map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
      Algebra.algebraMap_self,RingHom.id_apply,selectedPoint_seed,sub_eq_zero] using hh
  apply Finset.card_le_one.mpr
  intro gamma hgamma eta heta
  exact (phi.comp Polynomial.C).injective ((hvalue gamma hgamma).trans (hvalue eta heta).symm)

theorem card_primes_le_direction
    {Ω : Type} [Field Ω] {A : Type} [Fintype A]
    (P : A → Ideal (MvPolynomial (Fin 3) Ω)) [∀ a,(P a).IsPrime]
    (hinj : Function.Injective P) (axis : Axis)
    (ht : ∀ a, Transcendental Ω
      (flagEvaluation Ω (P a) 0 0 0 (MvPolynomial.X (axis.order 0))))
    (F N : MvPolynomial (Fin 3) Ω) (hF : F≠0) (hN : N≠0) (hrel : IsRelPrime F N)
    (hFmem : ∀ a,F∈P a) (hNmem : ∀ a,N∈P a)
    (p q : FlagDegree) (hp : PolynomialInFlag p F) (hq : PolynomialInFlag q N) :
    Fintype.card A≤flagMixed p q axis.flag := by
  letI : ∀ a, Algebra (RatFunc Ω) (CoordinateField Ω (P a)) := fun a =>
    (elementEmbedding Ω (CoordinateField Ω (P a))
      (flagEvaluation Ω (P a) 0 0 0 (MvPolynomial.X (axis.order 0))) (ht a)).toRingHom.toAlgebra
  have hb := finite_sum_prime_fields Ω axis 0 0 0 P hinj ht F N hF hN hrel hFmem hNmem p q hp hq
  calc
    Fintype.card A=∑ _ : A, 1 := by simp
    _≤∑ a : A, Module.finrank (RatFunc Ω) (CoordinateField Ω (P a)) := by
      apply Finset.sum_le_sum
      intro a _
      letI := hb.1 a
      exact Module.finrank_pos
    _≤_ := hb.2

theorem constant_prime_family_card_le
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] {A : Type} [Fintype A]
    (P : A → Ideal (MvPolynomial (Fin 3) Ω)) [∀ a,(P a).IsPrime]
    (hinj : Function.Injective P)
    (hnonpoint : ∀ a, ∀ v : Fin 3 → Ω, P a≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hconstant : ∀ a, IsAlgebraic Ω (coordinate Ω (P a) 2))
    (F N : MvPolynomial (Fin 3) Ω) (hF : F≠0) (hN : N≠0) (hrel : IsRelPrime F N)
    (hFmem : ∀ a,F∈P a) (hNmem : ∀ a,N∈P a)
    (p q : FlagDegree) (hp : PolynomialInFlag p F) (hq : PolynomialInFlag q N) :
    Fintype.card A≤flagMixed p q unitYZFlag+flagMixed p q unitAllFlag := by
  let activeY (a : A) := Transcendental Ω (coordinate Ω (P a) 0)
  have hr (a : A) (ha : ¬activeY a) : Transcendental Ω (coordinate Ω (P a) 1) := by
    obtain ⟨i,hi⟩ := exists_transcendental_coordinate_of_ne_point_kernel Ω (P a) (hnonpoint a)
    fin_cases i
    · exact False.elim (ha hi)
    · exact hi
    · exact False.elim (hi (hconstant a))
  have hycap : Fintype.card {a : A // activeY a}≤flagMixed p q unitYZFlag :=
    card_primes_le_direction (fun a : {a : A // activeY a} => P a.1)
      (fun a b h => Subtype.ext (hinj h)) .u
      (fun a => by simpa [Axis.order,RCN125.uOrder,affineU] using a.2)
      F N hF hN hrel (fun a => hFmem a.1) (fun a => hNmem a.1) p q hp hq
  have hrcap : Fintype.card {a : A // ¬activeY a}≤flagMixed p q unitAllFlag :=
    card_primes_le_direction (fun a : {a : A // ¬activeY a} => P a.1)
      (fun a b h => Subtype.ext (hinj h)) .v
      (fun a => by simpa [Axis.order,RCN125.vOrder,affineV] using hr a.1 a.2)
      F N hF hN hrel (fun a => hFmem a.1) (fun a => hNmem a.1) p q hp hq
  have hcomp := Fintype.card_subtype_compl activeY
  have hle : Fintype.card {a : A // activeY a}≤Fintype.card A :=
    Fintype.card_le_of_injective (fun a : {a : A // activeY a} => a.1) Subtype.val_injective
  omega

open RCN074 RCN086 RCN244
variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

abbrev ConstantComponent (S : Stage K I Gamma x p flag errorCap stageSupport) :=
  {C : FirstTailComponent S // IsAlgebraic (GenericField K) (coordinate (GenericField K) C.1 2)}

end
end ProximityPrize.SubmissionLower.MovingSourceConstantSeeds6814
end MergedPart15
