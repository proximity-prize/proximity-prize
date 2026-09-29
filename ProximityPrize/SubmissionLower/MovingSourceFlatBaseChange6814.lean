import ProximityPrize.SubmissionLower.MovingSourceProperness6814

/-! Transport properness through the injective flat coefficient changes
used by the generic moving-fiber construction. -/
namespace ProximityPrize.SubmissionLower.MovingSourceFlatBaseChange6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open UniqueFactorizationMonoid

section Flat
variable {A B : Type*} [CommRing A] [IsDomain A]
  [UniqueFactorizationMonoid A]
  [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B] [IsNoetherianRing B]
  [Algebra A B] [Module.Flat A B]

theorem map_isRelPrime_of_flat (hinj : Function.Injective (algebraMap A B))
    (P Q : A) (hP : P≠0) (hrel : IsRelPrime P Q) :
    IsRelPrime (algebraMap A B P) (algebraMap A B Q) := by
  classical
  apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
  · rintro ⟨hz,_⟩
    exact hP (hinj (by simpa only [map_zero] using hz))
  intro g hg hgP hgQ
  let I : Ideal B := Ideal.span {g}
  haveI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hg.prime
  let psi : A →+* B ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap A B)
  have hz : psi P=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hgP)
  obtain ⟨factors,hfactors,hprod⟩ := WfDvdMonoid.exists_factors P hP
  have hassoc := Associated.map psi hprod
  rw [hz] at hassoc
  have hp : psi factors.prod=0 := (associated_zero_iff_eq_zero _).mp hassoc
  rw [map_multiset_prod] at hp
  obtain ⟨f,hf,hfzero⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
  have hfi : Irreducible f := hfactors f hf
  have hgf : g ∣ algebraMap A B f :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hfzero)
  have he := RCN350.under_prime_factor_eq hinj f hfi.prime g hg.prime hgf
  have hQmem : Q ∈ (Ideal.span ({g} : Set B)).under A := Ideal.mem_span_singleton.mpr hgQ
  rw [he] at hQmem
  exact hfi.not_isUnit (hrel ((Multiset.dvd_prod hf).trans hprod.dvd) (Ideal.mem_span_singleton.mp hQmem))

end Flat

section Coefficients
variable {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Flat R S]
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coefficient_map_flat : Module.Flat (MvPolynomial σ R) (MvPolynomial σ S) := by
  exact Module.Flat.of_linearEquiv
    (Algebra.IsPushout.equiv R (MvPolynomial σ R) S (MvPolynomial σ S)).symm.toLinearEquiv

end Coefficients

section Equivalence
variable {A B : Type*} [CommRing A] [CommRing B]

theorem isRelPrime_equiv (e : A ≃+* B) (P Q : A) (h : IsRelPrime P Q) :
    IsRelPrime (e P) (e Q) := by
  intro d hdP hdQ
  have hP := map_dvd e.symm hdP
  have hQ := map_dvd e.symm hdQ
  simp only [RingEquiv.symm_apply_apply] at hP hQ
  have hu := (h hP hQ).map e.toMonoidHom
  change IsUnit (e (e.symm d)) at hu
  simpa only [RingEquiv.apply_symm_apply] using hu

end Equivalence

#print axioms map_isRelPrime_of_flat
#print axioms coefficient_map_flat
end
end ProximityPrize.SubmissionLower.MovingSourceFlatBaseChange6814
