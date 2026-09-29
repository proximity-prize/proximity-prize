import ProximityPrize.SubmissionLower.MovingSourceExtendedPoleFamily6814

/-! Distinct regular slice components cannot hide the same prime under
different geometric factor labels. This is the injectivity needed to sum
their generic moving degrees against one shared pair budget. -/
namespace ProximityPrize.SubmissionLower.MovingSourceSlicePrimeFamily6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
open scoped Classical
open MvPolynomial RCN084 RCN137 RCN264 WeightedSliceAssignment6807

variable {E : Type} [Field E] [IsAlgClosed E]
local notation "Poly" => MvPolynomial (Fin 3) E

theorem derivative_mem_of_two_factors (F G H : Poly) (P : Ideal Poly)
    (hprod : G*H∣F) (hG : G∈P) (hH : H∈P) : pderiv (1 : Fin 3) F∈P := by
  obtain ⟨Q,rfl⟩ := hprod
  rw [pderiv_mul,pderiv_mul]
  exact P.add_mem
    (P.mul_mem_right Q (P.add_mem (P.mul_mem_left _ hH) (P.mul_mem_right _ hG)))
    (P.mul_mem_right _ (P.mul_mem_right H hG))

theorem slice_prime_injective (F N R : Poly) (hFne : F≠0)
    (hR : R∈Ideal.span ({F,pderiv (1 : Fin 3) F} : Set Poly)) :
    Function.Injective (fun a : SliceComponent F N R => a.2.1) := by
  classical
  rintro ⟨ga,Ca⟩ ⟨gb,Cb⟩ he
  change Ca.1=Cb.1 at he
  have hga := activeFactors_spec F N ga
  have hgb := activeFactors_spec F N gb
  have hgeq : ga=gb := by
    apply Subtype.ext
    by_contra hne
    have hsubset : ({ga.1,gb.1} : Finset Poly)⊆normalizedFactorSet F := by
      intro P0 hP0
      simp only [Finset.mem_insert,Finset.mem_singleton] at hP0
      rcases hP0 with rfl | rfl
      · exact (Finset.mem_filter.mp ga.2).1
      · exact (Finset.mem_filter.mp gb.2).1
    have hprod : ga.1*gb.1∣F := by
      have hh := (Finset.prod_dvd_prod_of_subset {ga.1,gb.1} (normalizedFactorSet F) id hsubset).trans
        (normalizedFactorSet_product_dvd F hFne)
      simpa only [Finset.prod_pair hne,id_eq] using hh
    have ha : ga.1∈Ca.1 := regularComponent_G_mem E ga.1 N R Ca
    have hb : gb.1∈Ca.1 := by rw [he]; exact regularComponent_G_mem E gb.1 N R Cb
    have hF : F∈Ca.1 := Ca.1.mem_of_dvd hga.2.1 ha
    have hd := derivative_mem_of_two_factors F ga.1 gb.1 Ca.1 hprod ha hb
    have hspan : Ideal.span ({F,pderiv (1 : Fin 3) F} : Set Poly)≤Ca.1 := by
      apply Ideal.span_le.mpr
      intro P0 hP0
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hP0
      rcases hP0 with rfl | rfl
      · exact hF
      · exact hd
    exact regularComponent_H_not_mem E ga.1 N R Ca (hspan hR)
  cases hgeq
  exact congrArg (fun C : RegularComponent E ga.1 N R => (⟨ga,C⟩ : SliceComponent F N R)) (Subtype.ext he)

#print axioms slice_prime_injective
end
end ProximityPrize.SubmissionLower.MovingSourceSlicePrimeFamily6814
