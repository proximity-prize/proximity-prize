import ProximityPrize.SubmissionLower.LowerGeometry


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open RCN081 RCN156 RCN234 RCN082 LocatorDerivativeChain LocatorLowQuotient
open scoped Classical Matrix BigOperators

noncomputable section

set_option maxHeartbeats 1500000

variable {K : Type} [Field K]

private def skipSlope : Fin 3 → Fin 4 := ![0,1,3]

private theorem skipSlope_injective : Function.Injective skipSlope := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [skipSlope] at h ⊢

private theorem skipSlope_range (i : Fin 4) (hi : i ≠ 2) : i ∈ Set.range skipSlope := by
  fin_cases i
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact False.elim (hi rfl)
  · exact ⟨2,rfl⟩

theorem exists_direct_of_slope_degree_zero (F : MvPolynomial (Fin 4) K)
    (hF : F ≠ 0) (hR : F.degreeOf 2 = 0) (y t : ℕ)
    (hy : wt residualYSWeights F ≤ y) (ht : wt residualTotalWeights F ≤ t) :
    ∃ J : MvPolynomial (Fin 3) K, J ≠ 0 ∧
      (∀ e ∈ J.support, e 1 ≤ y ∧ e 1+e 2 ≤ t) ∧
      ∀ (P : Polynomial K) (g : K),
        MvPolynomial.aeval ![Polynomial.X,P,Polynomial.C g] J =
          RCN319.specialization K P g F := by
  have supported : ↑F.vars ⊆ Set.range skipSlope := by
    intro i hi
    apply skipSlope_range i
    intro he
    subst i
    exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hR
  obtain ⟨J,hJ⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range F skipSlope
    skipSlope_injective supported
  refine ⟨J,fun h => hF (by rw [← hJ,h,map_zero]),?_,?_⟩
  · intro e he
    let ex := e.mapDomain skipSlope
    have hex : ex ∈ F.support := by
      rw [← hJ, MvPolynomial.support_rename_of_injective skipSlope_injective]
      exact Finset.mem_image.mpr ⟨e,he,rfl⟩
    have eY : ex 1 = e 1 := Finsupp.mapDomain_apply_of_injective skipSlope_injective e 1
    have eZ : ex 3 = e 2 := Finsupp.mapDomain_apply_of_injective skipSlope_injective e 2
    have wy := (MvPolynomial.le_weightedTotalDegree residualYSWeights hex).trans hy
    have wt' := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hex).trans ht
    simp only [weight_fin4,residualYSWeights,residualTotalWeights] at wy wt'
    change ex 0*0 + ex 1*1 + ex 2*1 + ex 3*0 ≤ y at wy
    change ex 0*0 + ex 1*1 + ex 2*1 + ex 3*1 ≤ t at wt'
    simp only [mul_zero,mul_one,zero_add,add_zero,eY,eZ] at wy wt'
    omega
  · intro P g
    have hcoords : (![Polynomial.X,P,P.derivative,Polynomial.C g] : Fin 4 → Polynomial K) ∘ skipSlope =
        ![Polynomial.X,P,Polynomial.C g] := by
      funext i
      fin_cases i <;> rfl
    rw [← hJ, RCN319.specialization, MvPolynomial.aeval_rename,hcoords]

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
