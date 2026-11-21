import ProximityPrize.SubmissionLower.Rect51TangentSection

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace Rect51Tangent
noncomputable section
open HighCore82706Tangent (Input ResidueLift Factors)
open HighCore82706Tangent_3 (JetRing ordinate rootIdeal tangentEquation graphIdeal
  saturate openFactor jetCommRing)
open HighCore82706Tangent_3_1 (velocity coefficientDerivative jetSeparant)
open K1_14 (Seeds Equation)
open K1_14_6_1 (flatten partialX coeff_partialX)
open private inversePart inversePart_bound tangent_glue
  from ProximityPrize.SubmissionLower.HighCore82706TangentDeps

private theorem ordinate_derivative_bound (f : Equation) :
    (coefficientDerivative f).natDegree ≤ f.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  apply MvPolynomial.ext
  intro m
  change ((MvPolynomial.optionEquivLeft K1_14.FX (Fin 2) (partialX (flatten f))).coeff k).coeff m = _
  rw [MvPolynomial.optionEquivLeft_coeff_coeff, coeff_partialX,
    ← MvPolynomial.optionEquivLeft_coeff_coeff K1_14.FX (flatten f) k m,
    AlgEquiv.apply_symm_apply, Polynomial.coeff_eq_zero_of_natDegree_lt hk]
  simp

private theorem rectangular_proper {J : Input} {B : ResidueLift J} (D : Factors J B)
    {v : Axes} (hf : SeedBound J.f v) : SeedBound D.proper v := by
  have hz : J.f ≠ 0 := fun h => (Nat.ne_of_gt J.reduced.1) (by simp [h])
  have hp := HighCore82706Tangent_3_2.proper_ne_zero D
  have hprod : (∏ j, D.flat j) ≠ 0 := right_ne_zero_of_mul (D.product ▸ hz)
  apply (SeedBound.flatten_iff _ _).mpr
  intro i
  have h := (SeedBound.flatten_iff _ _).mp hf i
  rw [D.product] at h
  change MvPolynomial.degreeOf (some i)
    ((MvPolynomial.optionEquivLeft K1_14.FX (Fin 2)).symm (D.proper * ∏ j, D.flat j)) ≤ v i at h
  have hne (q : Equation) (hq : q ≠ 0) : flatten q ≠ 0 := by
    apply (map_ne_zero_iff _ (MvPolynomial.optionEquivLeft K1_14.FX (Fin 2)).symm.injective).mpr hq
  rw [map_mul, MvPolynomial.degreeOf_mul_eq (n := some i) (hne _ hp) (hne _ hprod)] at h
  change MvPolynomial.degreeOf (some i) ((MvPolynomial.optionEquivLeft K1_14.FX (Fin 2)).symm D.proper) ≤ v i
  exact (Nat.le_add_right _ _).trans h

theorem root_section (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Axes} (hf : SeedBound J.f v) :
    Represented (⊥ : Ideal JetRing) J.e 0 v (Polynomial.C D.proper) := by
  have hz : J.f ≠ 0 := fun h => (Nat.ne_of_gt J.reduced.1) (by simp [h])
  have hd : D.proper.natDegree ≤ J.e := Polynomial.natDegree_le_of_dvd ⟨_,D.product⟩ hz
  exact Represented.absolute (Bounded.C (rectangular_proper D hf)) (Weighted.C (by simpa using hd))

theorem inversePart_seedBound (J : Input) {v : Axes} (hf : SeedBound J.f v) :
    SeedBound (inversePart J) v := by
  have hY : SeedBound (Polynomial.X : Equation) 0 := by
    have h := Bounded.ordinate.2 0
    rwa [ordinate, Polynomial.coeff_C_zero] at h
  have heC : SeedBound (Polynomial.C (J.e : Seeds)) 0 := by
    have h := SeedBound.scalar (J.e : K1_14.FX)
    rw [map_natCast] at h
    exact h
  unfold inversePart
  exact SeedBound.sub (by simpa only [zero_add] using hY.mul hf.derivative)
    (by simpa only [zero_add] using heC.mul hf)

theorem tangent_section (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Axes} (hf : SeedBound J.f v) :
    Represented (rootIdeal D) (J.e-2) 1 v (tangentEquation J.f) := by
  let F := Polynomial.C (coefficientDerivative J.f)
  let G := Polynomial.C (inversePart J)
  let T := F+velocity*jetSeparant J.f
  let R := ordinate*F+velocity*G
  have hd : J.e-2+2*1+1 = J.e+1 := by have he : 3 ≤ J.e := J.sheets; omega
  have ht : tangentEquation J.f = T := rfl
  have hFx : SeedBound (coefficientDerivative J.f) v := hf.coeffDiff
  have hG : SeedBound (inversePart J) v := inversePart_seedBound J hf
  have hA : Bounded F 0 v := Bounded.C hFx
  have hB : Bounded (jetSeparant J.f) 0 v := Bounded.C hf.derivative
  have hC : Bounded G 0 v := Bounded.C hG
  have hT : Bounded T 1 v := by
    exact (hA.mono (by decide) (fun _ => le_rfl)).add (by
      simpa only [Nat.add_zero,zero_add] using Bounded.velocity.mul hB)
  have hR : Bounded R 1 v := by
    exact (Bounded.mono (Bounded.ordinate.mul hA) (by decide) (by intro i; simp)).add (by
      simpa only [Nat.add_zero,zero_add] using Bounded.velocity.mul hC)
  have wa : Weighted F J.e := Weighted.C (ordinate_derivative_bound J.f)
  have wb : Weighted (jetSeparant J.f) (J.e-1) := Weighted.C (Polynomial.natDegree_derivative_le _)
  have wc : Weighted G (J.e-1) := Weighted.C (inversePart_bound J).1
  have wt : Weighted T (J.e+1) :=
    (wa.mono (by omega)).add ((Weighted.velocity.mul wb).mono (by omega))
  have wr : Weighted R (J.e+1) :=
    ((Weighted.ordinate.mul wa).mono (by omega)).add ((Weighted.velocity.mul wc).mono (by omega))
  refine ⟨⟨1,T,R,hT,hR,hd ▸ wt,hd ▸ wr,?_⟩,ht.symm⟩
  rw [pow_one]
  have heq : ordinate*T-R =
      velocity*(Polynomial.C (Polynomial.C (J.e : Seeds))*Polynomial.C J.f) := by
    exact @tangent_glue Equation JetRing (@Polynomial.commRing Seeds inferInstance) jetCommRing
      Polynomial.C Polynomial.X (Polynomial.C (J.e : Seeds)) J.f J.f.derivative
      velocity F
  rw [heq]
  have hf0 : Polynomial.C J.f ∈ rootIdeal D := by
    rw [D.product, Polynomial.C_mul]
    exact (rootIdeal D).mul_mem_right _ (Ideal.subset_span (Set.mem_singleton _))
  exact (rootIdeal D).mul_mem_left _ ((rootIdeal D).mul_mem_left _ hf0)

theorem graph_sections (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Axes} (hf : SeedBound J.f v) :
    ∃ (F : Section (⊥ : Ideal JetRing) J.e 0 v) (T : Section (rootIdeal D) (J.e-2) 1 v),
      F.affine = Polynomial.C D.proper ∧ T.affine = tangentEquation J.f ∧
      graphIdeal J B D = saturate (Ideal.span {F.affine,T.affine}) (openFactor J B) := by
  obtain ⟨F,hF⟩ := root_section J B D hf
  obtain ⟨T,hT⟩ := tangent_section J B D hf
  exact ⟨F,T,hF,hT,by rw [hF,hT]; rfl⟩

#print axioms graph_sections
end
end Rect51Tangent
