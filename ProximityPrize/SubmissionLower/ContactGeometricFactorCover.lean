import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGeometricFirstTail

/-! .











 -/

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

/-- . -/
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

/-- . -/
theorem exists_geometric_component_of_surface_zero
    (φ : Polynomial K →+* L) (hφ : Function.Injective φ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (v : Fin 3 → L)
    (hzero : MvPolynomial.eval v (surfaceMap φ Q) = 0) :
    ∃ F ∈ activeFactors Q, ∃ g ∈ surfaceFactors φ F,
      Irreducible F ∧ Irreducible g ∧ F ∣ Q ∧ g ∣ surfaceMap φ F ∧
      MvPolynomial.eval v g = 0 := by
  obtain ⟨F, hF, hzF⟩ := exists_active_factor_of_surface_zero φ hφ Q hQ v hzero
  have hsF := activeFactors_spec Q F hF
  obtain ⟨g, hg, hzg⟩ := exists_surfaceFactor_zero φ hφ F hsF.1.ne_zero v hzF
  have hsg := surfaceFactors_spec φ F g hg
  exact ⟨F, hF, g, hg, hsF.1, hsg.1, hsF.2.1, hsg.2, hzg⟩

/-- .
 -/
theorem surfaceFactor_family_degree_budget
    (φ : Polynomial K →+* L) (hφ : Function.Injective φ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (i : Fin 3) :
    (∑ F ∈ activeFactors Q, ∑ g ∈ surfaceFactors φ F, g.degreeOf i) ≤
      Q.degreeOf i.succ := by
  classical
  calc
    (∑ F ∈ activeFactors Q, ∑ g ∈ surfaceFactors φ F, g.degreeOf i) ≤
        ∑ F ∈ activeFactors Q, F.degreeOf i.succ := by
      apply Finset.sum_le_sum
      intro F hF
      exact surfaceFactors_degree_budget φ hφ F (activeFactors_spec Q F hF).1.ne_zero i
    _ ≤ Q.degreeOf i.succ :=
      sum_coordinate_degrees_le_of_prod_dvd (activeFactors Q) id Q hQ
        (activeFactors_product_dvd Q hQ) i.succ

theorem surfaceFactor_family_input_budgets
    (φ : Polynomial K →+* L) (hφ : Function.Injective φ)
    (Q : MvPolynomial (Fin 4) K) (D w zcap s : ℕ) (hw : 0 < w) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D w zcap s) :
    (∑ F ∈ activeFactors Q, ∑ g ∈ surfaceFactors φ F, g.degreeOf (0 : Fin 3)) ≤ (D - 1) / w ∧
    (∑ F ∈ activeFactors Q, ∑ g ∈ surfaceFactors φ F, g.degreeOf (1 : Fin 3)) ≤ s ∧
    (∑ F ∈ activeFactors Q, ∑ g ∈ surfaceFactors φ F, g.degreeOf (2 : Fin 3)) ≤ zcap := by
  have hc := ContactFactorCaps.degree_bounds_of_mem_box Q D w zcap s hw hbox
  exact ⟨(surfaceFactor_family_degree_budget φ hφ Q hQ 0).trans hc.1,
    (surfaceFactor_family_degree_budget φ hφ Q hQ 1).trans hc.2.1,
    (surfaceFactor_family_degree_budget φ hφ Q hQ 2).trans hc.2.2⟩

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

theorem surfaceFactor_card_le_degree_sum
    (φ : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K) :
    (surfaceFactors φ F).card ≤
      ∑ g ∈ surfaceFactors φ F, (g.degreeOf 0 + g.degreeOf 1 + g.degreeOf 2) := by
  classical
  calc
    (surfaceFactors φ F).card = ∑ _g ∈ surfaceFactors φ F, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun g hg =>
      irreducible_positive_surface_degree g (surfaceFactors_spec φ F g hg).1

theorem surfaceFactor_family_card_budget
    (φ : Polynomial K →+* L) (hφ : Function.Injective φ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    (∑ F ∈ activeFactors Q, (surfaceFactors φ F).card) ≤
      Q.degreeOf 1 + Q.degreeOf 2 + Q.degreeOf 3 := by
  classical
  have hcount := Finset.sum_le_sum
    (s := activeFactors Q) (fun F _ => surfaceFactor_card_le_degree_sum φ F)
  simp only [Finset.sum_add_distrib] at hcount
  have h0 : (∑ F ∈ activeFactors Q, ∑ g ∈ surfaceFactors φ F, g.degreeOf (0 : Fin 3)) ≤
      Q.degreeOf (1 : Fin 4) := surfaceFactor_family_degree_budget φ hφ Q hQ 0
  have h1 : (∑ F ∈ activeFactors Q, ∑ g ∈ surfaceFactors φ F, g.degreeOf (1 : Fin 3)) ≤
      Q.degreeOf (2 : Fin 4) := surfaceFactor_family_degree_budget φ hφ Q hQ 1
  have h2 : (∑ F ∈ activeFactors Q, ∑ g ∈ surfaceFactors φ F, g.degreeOf (2 : Fin 3)) ≤
      Q.degreeOf (3 : Fin 4) := surfaceFactor_family_degree_budget φ hφ Q hQ 2
  omega

end SurfaceFamilies

section CanonicalPoints

variable (K : Type*) [Field K]

/-- .
 -/
theorem exists_component_at_actual_initial_point
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (P : Polynomial K) (γ : K) (hsolution : specialization K P γ Q = 0) :
    ∃ F ∈ activeFactors Q, ∃ g ∈ surfaceFactors (polynomialEmbedding K) F,
      Irreducible F ∧ Irreducible g ∧ F ∣ Q ∧
      g ∣ surfaceMap (polynomialEmbedding K) F ∧
      MvPolynomial.eval (fun i : Fin 3 => initialPoint K P γ i.succ) g = 0 := by
  have hz := (actual_generic_initial_zero_iff K P γ Q).mpr hsolution
  rw [canonical_geometricSurfaceMap] at hz
  exact exists_geometric_component_of_surface_zero
    (polynomialEmbedding K) (polynomialEmbedding_injective K) Q hQ
    (fun i : Fin 3 => initialPoint K P γ i.succ) hz

end CanonicalPoints


end
end ProximityPrize.SubmissionLower.ContactGeometricFactorCover
