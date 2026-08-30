import ProximityPrize.SubmissionLower.ContactGeometricFirstTail

namespace ProximityPrize.SubmissionLower.ContactGeometricFactorCover

open UniqueFactorizationMonoid ContactGenericSurface ContactFactorCover
open ContactGenericInitialPoint ContactGeometricFirstTail
open ContactInterpolation ContactTranslation

noncomputable section

section ArbitraryVariables

variable {σ A : Type*} [Field A]

local instance : StrongNormalizationMonoid (MvPolynomial σ A) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

def normalizedFactorSet (Q : MvPolynomial σ A) : Finset (MvPolynomial σ A) := by
  classical
  exact (normalizedFactors Q).toFinset

theorem normalizedFactorSet_spec (Q F : MvPolynomial σ A)
    (hF : F ∈ normalizedFactorSet Q) : Irreducible F ∧ F ∣ Q := by
  classical
  have hm : F ∈ normalizedFactors Q := Multiset.mem_toFinset.mp hF
  exact ⟨irreducible_of_normalized_factor F hm, dvd_of_mem_normalizedFactors hm⟩

theorem normalizedFactorSet_product_dvd (Q : MvPolynomial σ A) (hQ : Q ≠ 0) :
    (∏ F ∈ normalizedFactorSet Q, F) ∣ Q := by
  classical
  exact (normalizedFactors Q).toFinset_prod_dvd_prod.trans (prod_normalizedFactors hQ).dvd

theorem coordinate_degree_le_of_dvd (i : σ) (F Q : MvPolynomial σ A)
    (hdiv : F ∣ Q) (hQ : Q ≠ 0) : F.degreeOf i ≤ Q.degreeOf i := by
  rcases hdiv with ⟨G, rfl⟩
  rcases mul_ne_zero_iff.mp hQ with ⟨hF, hG⟩
  rw [MvPolynomial.degreeOf_mul_eq hF hG]
  exact Nat.le_add_right _ _

theorem sum_coordinate_degrees_le_of_prod_dvd {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial σ A) (Q : MvPolynomial σ A)
    (hQ : Q ≠ 0) (hdiv : (∏ j ∈ I, f j) ∣ Q) (i : σ) :
    (∑ j ∈ I, (f j).degreeOf i) ≤ Q.degreeOf i := by
  classical
  have hprod : (∏ j ∈ I, f j) ≠ 0 := by
    intro hz
    rcases hdiv with ⟨G, hG⟩
    apply hQ
    rw [hG, hz, zero_mul]
  have hf : ∀ j ∈ I, f j ≠ 0 := Finset.prod_ne_zero_iff.mp hprod
  calc
    (∑ j ∈ I, (f j).degreeOf i) = (∏ j ∈ I, f j).degreeOf i :=
      (MvPolynomial.degreeOf_prod_eq (n := i) I f hf).symm
    _ ≤ Q.degreeOf i := coordinate_degree_le_of_dvd i _ Q hdiv hQ

theorem normalizedFactorSet_degree_budget
    (Q : MvPolynomial σ A) (hQ : Q ≠ 0) (i : σ) :
    (∑ F ∈ normalizedFactorSet Q, F.degreeOf i) ≤ Q.degreeOf i :=
  sum_coordinate_degrees_le_of_prod_dvd (normalizedFactorSet Q) id Q hQ
    (normalizedFactorSet_product_dvd Q hQ) i

theorem exists_normalizedFactorSet_zero
    {B : Type*} [CommRing B] [IsDomain B]
    (ψ : MvPolynomial σ A →+* B) (Q : MvPolynomial σ A)
    (hQ : Q ≠ 0) (hzero : ψ Q = 0) :
    ∃ F ∈ normalizedFactorSet Q, ψ F = 0 := by
  classical
  have ha := Associated.map ψ (prod_normalizedFactors hQ)
  rw [hzero] at ha
  have hp : ψ (normalizedFactors Q).prod = 0 := (associated_zero_iff_eq_zero _).mp ha
  rw [map_multiset_prod] at hp
  obtain ⟨F, hm, hz⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
  exact ⟨F, Multiset.mem_toFinset.mpr hm, hz⟩

end ArbitraryVariables

section SurfaceFamilies

variable {K L : Type*} [Field K] [Field L]

def surfaceFactors (φ : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K) :
    Finset (MvPolynomial (Fin 3) L) := normalizedFactorSet (surfaceMap φ F)

theorem surfaceFactors_spec (φ : Polynomial K →+* L)
    (F : MvPolynomial (Fin 4) K) (g : MvPolynomial (Fin 3) L)
    (hg : g ∈ surfaceFactors φ F) : Irreducible g ∧ g ∣ surfaceMap φ F :=
  normalizedFactorSet_spec (surfaceMap φ F) g hg

theorem exists_surfaceFactor_zero
    (φ : Polynomial K →+* L) (hφ : Function.Injective φ)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) (v : Fin 3 → L)
    (hzero : MvPolynomial.eval v (surfaceMap φ F) = 0) :
    ∃ g ∈ surfaceFactors φ F, MvPolynomial.eval v g = 0 :=
  exists_normalizedFactorSet_zero (MvPolynomial.eval v) (surfaceMap φ F)
    (surfaceMap_ne_zero φ hφ F hF) hzero

theorem surfaceFactors_degree_budget
    (φ : Polynomial K →+* L) (hφ : Function.Injective φ)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) (i : Fin 3) :
    (∑ g ∈ surfaceFactors φ F, g.degreeOf i) ≤ F.degreeOf i.succ :=
  (normalizedFactorSet_degree_budget (surfaceMap φ F)
    (surfaceMap_ne_zero φ hφ F hF) i).trans (surfaceMap_degreeOf_le φ F i)

theorem irreducible_positive_surface_degree
    (g : MvPolynomial (Fin 3) L) (hg : Irreducible g) :
    0 < g.degreeOf 0 + g.degreeOf 1 + g.degreeOf 2 := by
  by_contra h
  have heq : g = MvPolynomial.C (g.coeff 0) := by
    apply eq_C_of_all_degreeOf_zero
    intro i
    fin_cases i
    · change g.degreeOf (0 : Fin 3) = 0
      omega
    · change g.degreeOf (1 : Fin 3) = 0
      omega
    · change g.degreeOf (2 : Fin 3) = 0
      omega
  have hc : g.coeff 0 ≠ 0 := by
    intro hzero
    apply hg.ne_zero
    rw [heq, hzero, map_zero]
  apply hg.not_isUnit
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

end SurfaceFamilies

section CanonicalPoints

variable (K : Type*) [Field K]

end CanonicalPoints

end
end ProximityPrize.SubmissionLower.ContactGeometricFactorCover
