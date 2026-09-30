import ProximityPrize.SubmissionLower.MovingSourceOwnerRouting6814
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
