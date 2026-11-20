import ProximityPrize.SubmissionLower.Koala6844VirtualShortFirstJet


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators Pointwise
open SecondJetSupport SecondJetCoefficients SecondJetGlobalSupport SecondJetDifferentiation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]

private abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K
private abbrev E4 := Fin 4 →₀ ℕ

private def rescaleExponent : E4 →+ E4 where
  toFun e := e + Finsupp.single 0 (2*e 1)
  map_zero' := by simp
  map_add' e f := by
    ext i
    by_cases hi : 0 = i
    · subst i
      simp [Finsupp.add_apply,mul_add]
      omega
    · simp [Finsupp.add_apply,hi]

private theorem rescaleExponent_injective : Function.Injective rescaleExponent := by
  intro e f h
  have h1 := congrArg (fun n : E4 => n 1) h
  simp [rescaleExponent] at h1
  ext i
  have hi := congrArg (fun n : E4 => n i) h
  simp only [rescaleExponent,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Finsupp.add_apply] at hi
  rw [h1] at hi
  exact Nat.add_right_cancel hi

private def rescale : P4 K →ₐ[K] P4 K := AddMonoidAlgebra.mapDomainAlgHom K K rescaleExponent

private theorem rescale_monomial (d : E4) (c : K) :
    rescale (MvPolynomial.monomial d c) = MvPolynomial.monomial (rescaleExponent d) c :=
  AddMonoidAlgebra.mapDomain_single

private theorem rescale_X (i : Fin 4) :
    rescale (MvPolynomial.X i : P4 K) = MvPolynomial.X i*MvPolynomial.X 0^(if i = 1 then 2 else 0) := by
  rw [MvPolynomial.X_pow_eq_monomial]
  conv_lhs => rw [MvPolynomial.X]
  rw [rescale_monomial]
  conv_rhs => rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial]
  congr 1
  · ext j
    fin_cases i <;> simp [rescaleExponent,Fin.ext_iff]
  · simp

private theorem contact_of_rescale_dvd (m : ℕ) (P : P4 K)
    (h : MvPolynomial.X 0^m ∣ rescale P) : ContactOrderBridge.AtLeast ContactOrderBridge.localWeights m P := by
  intro e he
  have hcoeff : (rescale P).coeff (rescaleExponent e) = P.coeff e :=
    Finsupp.mapDomain_apply_of_injective rescaleExponent_injective _ _
  have hnot : rescaleExponent e ∈ (rescale P).support := by
    rw [MvPolynomial.mem_support_iff,hcoeff]
    exact MvPolynomial.mem_support_iff.mp he
  obtain ⟨Q,hQ⟩ := h
  rw [hQ] at hnot
  obtain ⟨l,hl,r,hr,heq⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hnot)
  simp only [MvPolynomial.support_X_pow,Finset.mem_singleton] at hl
  subst l
  have ht := congrArg (fun d : E4 => d 0) heq
  simp [rescaleExponent,Finsupp.add_apply] at ht
  have hw : Finsupp.weight ContactOrderBridge.localWeights e = e 0+2*e 1 := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fin.sum_univ_four]
    change e 0*1+e 1*2+e 2*0+e 3*0 = _
    omega
  rw [hw]
  omega

private def liftJet : P4 K →ₐ[K] Poly (K := K) := MvPolynomial.rename ![0,2,3,4]

private theorem asS_liftJet (P : P4 K) : asS (liftJet P) = Polynomial.C P := by
  have h : (asS (K := K)).toAlgHom.comp liftJet = Polynomial.CAlgHom (R := K) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [liftJet,asS,Equiv.swap_apply_def,MvPolynomial.finSuccEquiv_apply] <;> rfl
  exact DFunLike.congr_fun h P

private theorem liftJet_toFirstJet (P : Poly (K := K)) (hs : ∀ e ∈ P.support, e 1 = 0) :
    liftJet (toFirstJet P) = P := by
  have hdeg : (asS P).natDegree ≤ 0 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    apply MvPolynomial.support_eq_empty.mp
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    have hf := hs _ (coefficient_support P j d hd)
    rw [(lift_coordinates j d).2.1] at hf
    omega
  apply (asS (K := K)).injective
  rw [asS_liftJet,toFirstJet_apply]
  exact (Polynomial.eq_C_of_natDegree_le_zero hdeg).symm

private def keepFirstContact : Poly (K := K) →ₐ[K] P4 K :=
  MvPolynomial.aeval ![MvPolynomial.X 0,-MvPolynomial.X 1,0,MvPolynomial.X 2,MvPolynomial.X 3]

private theorem firstContact_eq (x u0 u1 : K) :
    rescale.comp (ContactOrderBridge.localize K x u0 u1) =
      keepFirstContact.comp (substitute.comp ((localize x u0 u1).comp liftJet)) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [rescale_X,keepFirstContact,substitute,localize,liftJet,
      ContactOrderBridge.localize,ContactOrderBridge.localVariables] <;> ring

theorem toFirstJet_contact (x u0 u1 : K) (m : ℕ) (P : Poly (K := K))
    (hs : ∀ e ∈ P.support, e 1 = 0)
    (hcontact : Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
      (flatEquiv (K := K) (localize x u0 u1 P))) :
    ContactOrderBridge.ContactAtLeast K x u0 u1 m (toFirstJet P) := by
  apply contact_of_rescale_dvd
  have h := DFunLike.congr_fun (firstContact_eq x u0 u1) (toFirstJet P)
  change rescale (ContactOrderBridge.localize K x u0 u1 (toFirstJet P)) =
    keepFirstContact (substitute (localize x u0 u1 (liftJet (toFirstJet P)))) at h
  rw [h,liftJet_toFirstJet P hs]
  have hd := map_dvd keepFirstContact.toRingHom
    (SecondJetGlobalDifferentiation.nested_to_flat_contact (localize x u0 u1 P) m hcontact)
  simpa [keepFirstContact] using hd

theorem firstJetKernel_contact {I : Type*} (D : ℕ → ℕ) (w wQ m L B U q : ℕ)
    (hUL : U ≤ L) (hqU : q ≤ U) (A₀ A₁ d C₁ : Polynomial K) (x u0 u1 : I → K)
    (c : (jointContactMap D w wQ L B 0 U q m (normalizedDenominator A₀ A₁)
      (normalizedNumerator d C₁) x u0 u1).ker) (i : I) :
    ContactOrderBridge.ContactAtLeast K (x i) (u0 i) (u1 i) m (firstJetClearedLinear D w wQ L B U q
      (normalizedDenominator A₀ A₁) (normalizedNumerator d C₁) c.val) := by
  let A := normalizedDenominator A₀ A₁
  let N := normalizedNumerator d C₁
  let P := reconstructNormalized (K := K) D w wQ L B 0 U q c.val
  let F := clearAux A N q P
  have hsupp (j e) (he : e ∈ (P.coeff j).support) :=
    reconstructed_normalized_bounds D w wQ L B 0 U q (by omega) hUL hqU c.val j e he
  have hshape := clear_normalized_support A₀ A₁ d C₁ B 0 U L q P
    (fun j e he => ⟨(hsupp j e he).2.1,(hsupp j e he).2.2.1,
      (hsupp j e he).2.2.2.1,(hsupp j e he).2.2.2.2.1⟩)
  exact toFirstJet_contact (x i) (u0 i) (u1 i) m F
    (fun e he => Nat.eq_zero_of_le_zero (hshape e he).2.1)
    (normalizedContactKernel_contact D w wQ L B 0 U q m A N x u0 u1 c i)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
