import ProximityPrize.SubmissionLower.R6960ChartIntegrality

noncomputable section
set_option Elab.async false
namespace Lower6960.TwoRulings
open Polynomial
open scoped Polynomial

variable {k : Type*} [Field k]
abbrev Plane (k : Type*) [Field k] := Polynomial k[X]

/-- A scalar denominator in one ruling is relatively prime to a nonzero
denominator in the other, even if their zero curves intersect on the plane. -/
theorem independent_denominators (a b : k[X]) (an : a≠0) (bn : b≠0) :
    IsRelPrime (C a : Plane k) (b.map (C : k→+*k[X])) := by
  intro d da db
  have cd := natDegree_le_of_dvd da (C_ne_zero.mpr an)
  rw [natDegree_C] at cd
  have eq := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero cd)
  rw [eq] at db ⊢
  apply isUnit_C.mpr
  have dvd := (C_dvd_iff_dvd_coeff _ _).mp db b.natDegree
  rw [coeff_map,coeff_natDegree] at dvd
  exact isUnit_of_dvd_unit dvd (isUnit_C.mpr (leadingCoeff_ne_zero.mpr bn).isUnit)

variable {E : Type*} [Field E] [Algebra (Plane k) E]

/-- Integrality on the affine plane is detected on its two one-variable
generic rulings. Local monic coordinate charts in the two directions may
use independent denominators. -/
theorem affine_iff (F : Type*) [Field F] [Algebra (Plane k) F] [IsFractionRing (Plane k) F]
    [Algebra F E] [IsScalarTower (Plane k) F E] [FiniteDimensional F E] (x : E) :
    IsIntegral (Plane k) x ↔
      (∃ a:k[X], a≠0 ∧ IsIntegral (Plane k) (algebraMap (Plane k) E (C a)*x)) ∧
      (∃ b:k[X], b≠0 ∧ IsIntegral (Plane k) (algebraMap (Plane k) E (b.map (C : k→+*k[X]))*x)) := by
  constructor
  · intro h
    exact ⟨⟨1,one_ne_zero,by simpa using h⟩,⟨1,one_ne_zero,by simpa using h⟩⟩
  · rintro ⟨⟨a,an,ai⟩,⟨b,bn,bi⟩⟩
    exact NormalizedFiber.integral_of_coprime_clearings F (C_ne_zero.mpr an)
      ((Polynomial.map_ne_zero_iff C_injective).mpr bn) (independent_denominators a b an bn) x ai bi

#print axioms affine_iff

/-- The base localizations which keep the other coordinate polynomial. -/
def innerDenominators (k : Type*) [Field k] : Submonoid (Plane k) :=
  (nonZeroDivisors k[X]).map (C : k[X]→+*Plane k).toMonoidHom

def outerDenominators (k : Type*) [Field k] : Submonoid (Plane k) :=
  (nonZeroDivisors k[X]).map (mapRingHom (C : k→+*k[X])).toMonoidHom

/-- The intersection formula for actual integral closures of the two
localized rings. It also applies after changing either coordinate to its
inverse in a projective chart. -/
theorem two_generic_lines (F : Type*) [Field F] [Algebra (Plane k) F] [IsFractionRing (Plane k) F]
    [Algebra F E] [IsScalarTower (Plane k) F E] [FiniteDimensional F E]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra (Plane k) R] [Algebra (Plane k) S]
    [IsLocalization (innerDenominators k) R] [IsLocalization (outerDenominators k) S]
    [Algebra R E] [Algebra S E] [IsScalarTower (Plane k) R E] [IsScalarTower (Plane k) S E]
    (x : E) : IsIntegral (Plane k) x ↔ IsIntegral R x ∧ IsIntegral S x := by
  constructor
  · intro i; exact ⟨i.tower_top,i.tower_top⟩
  · rintro ⟨hR,hS⟩
    apply (affine_iff F x).mpr
    obtain ⟨d,good⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (innerDenominators k) x hR
    obtain ⟨a,ha,eq⟩ := d.property
    obtain ⟨d',good'⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (outerDenominators k) x hS
    obtain ⟨b,hb,eq'⟩ := d'.property
    refine ⟨⟨a,mem_nonZeroDivisors_iff_ne_zero.mp ha,?_⟩,
      ⟨b,mem_nonZeroDivisors_iff_ne_zero.mp hb,?_⟩⟩
    · change C a=d.val at eq
      rw [eq]
      simpa only [Submonoid.smul_def,Algebra.smul_def] using good
    · change b.map C=d'.val at eq'
      rw [eq']
      simpa only [Submonoid.smul_def,Algebra.smul_def] using good'

#print axioms two_generic_lines

/-- An actual generic ruling over a PID has a field basis whose
coordinates test integrality one at a time. These are the finite linear
functionals needed when passing to Laurent coordinates on the four charts. -/
theorem ruling_basis (A F E : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [Field F] [Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) F E),n=Module.finrank F E ∧
      ∀ x : E, IsIntegral A x ↔ ∀ i, b.repr x i∈Set.range (algebraMap A F) := by
  classical
  let S:=integralClosure A E
  have : Module.IsTorsionFree A E := .trans_faithfulSMul A F E
  have : Module.Free A S := IsIntegralClosure.module_free A F E S
  have : Module.Finite A S := IsIntegralClosure.finite A F E S
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors A)) E :=
    IsIntegralClosure.isLocalization A F E S
  let j:=Module.Free.ChooseBasisIndex A S
  let a:=(Module.Free.chooseBasis A S).reindex (Fintype.equivFin j)
  let b:=Module.Basis.localizationLocalization F (nonZeroDivisors A) E a
  refine ⟨Fintype.card j,b,by simpa using (Module.finrank_eq_card_basis b).symm,?_⟩
  intro x
  constructor
  · intro hx i
    let y : S:=⟨x,hx⟩
    refine ⟨a.repr y i,?_⟩
    exact (a.localizationLocalization_repr_algebraMap F (nonZeroDivisors A) E y i).symm
  · intro all
    choose c value using all
    rw [←b.sum_repr x]
    apply IsIntegral.sum
    intro i _
    rw [←value i,Algebra.smul_def,←IsScalarTower.algebraMap_apply]
    have int : IsIntegral A (b i) := by
      rw [show b i=algebraMap S E (a i) from a.localizationLocalization_apply F (nonZeroDivisors A) E i]
      exact (a i).property
    exact isIntegral_algebraMap.mul int

#print axioms ruling_basis
end Lower6960.TwoRulings
