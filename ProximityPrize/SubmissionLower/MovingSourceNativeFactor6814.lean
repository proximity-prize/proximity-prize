import ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814

/-! Turn an actual curvature-root factor into the existing native source
record. Its helper divisibilities are proved from root multiplicity in
the faithful carrier field, not postulated as a counting supplier. -/
namespace ProximityPrize.SubmissionLower.MovingSourceNativeFactor6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial SecondJetCoefficients SecondJetClearedHelper SecondJetCarrierDichotomy
open MovingFiberThreeSources6811 MovingSourceCarrierField6814

variable {K E : Type} [Field K] [Field E]

theorem asS_natDegree (P : SecondJetSupport.Poly (K:=K)) :
    (asS P).natDegree=P.degreeOf 1 := by
  change (MvPolynomial.finSuccEquiv K 4 (MvPolynomial.rename (Equiv.swap (0 : Fin 5) 1) P)).natDegree=_
  rw [MvPolynomial.natDegree_finSuccEquiv]
  simpa only [Equiv.swap_apply_right] using
    (MvPolynomial.degreeOf_rename_of_injective (p:=P) (Equiv.swap (0 : Fin 5) 1).injective 1)

theorem source_of_root_multiplicity
    (J : SecondJetSupport.Poly (K:=K)) (F : MvPolynomial (Fin 4) K)
    (phi : MvPolynomial (Fin 4) K →+* E) (hker : ∀ P, phi P=0 ↔ F∣P)
    (hH : phi (2*RCN313.polyH K F)≠0)
    (m s B U T : ℕ) (hm : 0<m) (hs : J.degreeOf 1=s)
    (h2s : 2*s≤B) (hBU : B≤U) (hUT : U≤T)
    (hshape : ∀ e ∈ J.support, 2*e 1+e 3≤B ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (hroot : ((asS J).map phi).rootMultiplicity (ratio phi F)=m) :
    ∃ S : Source F, S.P=J ∧ S.d=m ∧
      S.flag=SecondJetRelaxedFlag.budgetFlag B U T m s := by
  have hne : (asS J).map phi≠0 := by
    intro hz
    rw [hz,Polynomial.rootMultiplicity_zero] at hroot
    omega
  have hpow : (Polynomial.X-Polynomial.C (ratio phi F))^m ∣ (asS J).map phi := by
    rw [←hroot]
    exact Polynomial.pow_rootMultiplicity_dvd _ _
  have hms : m≤s := by
    have hh := Polynomial.natDegree_le_of_dvd hpow hne
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hh
    exact hh.trans (Polynomial.natDegree_map_le.trans_eq ((asS_natDegree J).trans hs))
  have hS : ∀ e ∈ J.support, e 1≤s := MvPolynomial.degreeOf_le_iff.mp hs.le
  have hdiv (d : ℕ) (hd : d≤m-1) : F∣helper J F (s-d) d := by
    apply (hker _).mp
    rw [mapped_helper J F phi s d hS hH]
    have hz : ((Polynomial.derivative)^[d] ((asS J).map phi)).eval (ratio phi F)=0 :=
      Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (by rw [hroot]; omega)
    rw [hz,mul_zero]
  let S : Source F := {
    P := J, B := B, U := U, T := T, s := s, k := m-1, n0 := s
    hS := hS
    hshape := hshape
    hBU := hBU
    hUT := hUT
    hdn := by omega
    hB := by omega
    hn := by rw [asS_natDegree,hs]
    hdiv := hdiv }
  have hd : S.d=m := by dsimp [S,Source.d]; omega
  exact ⟨S,rfl,hd,by simp only [Source.flag,hd]; rfl⟩

theorem canonical_source_of_root [CharP K 2130706433]
    (J : SecondJetSupport.Poly (K:=K)) (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (m s B U T : ℕ) (hm : 0<m) (hs : J.degreeOf 1=s)
    (h2s : 2*s≤B) (hBU : B≤U) (hUT : U≤T)
    (hshape : ∀ e ∈ J.support, 2*e 1+e 3≤B ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (hroot : ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)=m) :
    ∃ S : Source F, S.P=J ∧ S.d=m ∧ S.flag=SecondJetRelaxedFlag.budgetFlag B U T m s :=
  source_of_root_multiplicity J F (carrierMap F) (carrierMap_zero_iff F)
    (carrier_H_nonzero F hpos hsmall) m s B U T hm hs h2s hBU hUT hshape hroot

#print axioms source_of_root_multiplicity
#print axioms canonical_source_of_root
end
end ProximityPrize.SubmissionLower.MovingSourceNativeFactor6814
