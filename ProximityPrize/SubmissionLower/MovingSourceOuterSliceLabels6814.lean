import ProximityPrize.SubmissionLower.MovingSourceOuterCommonFrame6814

/-! Every regular assigned prime slice belongs to one original geometric
factor label. This permits applying the existing local multiplicity
theorem without mixing multiplicities from different Stages. -/
namespace ProximityPrize.SubmissionLower.MovingSourceOuterSliceLabels6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open MvPolynomial RCN137 MovingSourceSlicePrimeFamily6814

variable {Omega E I : Type} [Field Omega] [IsAlgClosed Omega] [Field E]
local notation "Poly" => MvPolynomial (Fin 3) Omega
local notation "PE" => MvPolynomial (Fin 3) E

theorem regular_point_unique_factor (F G H : Poly) (hF : F≠0)
    (hG : G∈normalizedFactorSet F) (hH : H∈normalizedFactorSet F)
    (psi : Poly →+* E) (hGzero : psi G=0) (hHzero : psi H=0)
    (hregular : psi (pderiv (1 : Fin 3) F)≠0) : G=H := by
  by_contra hne
  have hsub : ({G,H} : Finset Poly)⊆normalizedFactorSet F := by
    intro P hP
    simp only [Finset.mem_insert,Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact hG
    · exact hH
  have hprod : G*H∣F := by
    have hh := (Finset.prod_dvd_prod_of_subset {G,H} (normalizedFactorSet F) id hsub).trans
      (normalizedFactorSet_product_dvd F hF)
    simpa only [Finset.prod_pair hne,id_eq] using hh
  have hd := derivative_mem_of_two_factors F G H (RingHom.ker psi) hprod hGzero hHzero
  exact hregular hd

theorem assigned_slice_label_constant
    (phi : Omega →+* E) (F : Poly) (hF : F≠0)
    (D : Ideal PE) [D.IsPrime] (hFD : MvPolynomial.map phi F∈D)
    (point : I → Fin 3 → E)
    (hpoint : ∀ i, D≤RingHom.ker (MvPolynomial.aeval (point i) : PE →ₐ[E] E).toRingHom)
    (label : I → ↥(normalizedFactorSet F))
    (hroot : ∀ i, MvPolynomial.eval (point i) (MvPolynomial.map phi (label i).val)=0)
    (hregular : ∀ i, MvPolynomial.eval (point i) (MvPolynomial.map phi (pderiv (1 : Fin 3) F))≠0) :
    ∃ g : ↥(normalizedFactorSet F), ∀ i, label i=g := by
  let psi : Poly →+* PE ⧸ D := (Ideal.Quotient.mk D).comp (MvPolynomial.map phi)
  have hz : psi F=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hFD
  obtain ⟨g,hg,hgz⟩ := exists_normalizedFactorSet_zero psi F hF hz
  have hmem : MvPolynomial.map phi g∈D := Ideal.Quotient.eq_zero_iff_mem.mp hgz
  refine ⟨⟨g,hg⟩,fun i => Subtype.ext ?_⟩
  have hgi : MvPolynomial.eval (point i) (MvPolynomial.map phi g)=0 := hpoint i hmem
  exact regular_point_unique_factor F (label i).val g hF (label i).property hg
    ((MvPolynomial.eval (point i)).comp (MvPolynomial.map phi)) (hroot i) hgi (hregular i)

#print axioms assigned_slice_label_constant
end
end ProximityPrize.SubmissionLower.MovingSourceOuterSliceLabels6814
