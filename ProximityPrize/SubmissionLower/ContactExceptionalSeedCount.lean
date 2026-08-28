import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactExceptionalSeedAuxiliary


/-!
# Actual finite exceptional-seed count

Model label: gpt-5.

A seed-only generic surface is projected to a genuine univariate polynomial.
Variable-support congruence proves reconstruction, hence nonzero status;
the actual monomial expansion proves its degree cap. Distinct embedded seeds
are then actual roots, so the standard polynomial root count applies.

The final theorem bounds the real exceptional solutions of the constructed
auxiliary by 2*j^2. No free injective projection, coefficient selection,
genericity premise, geometric point count, or new axiom is supplied.
-/

namespace ProximityPrize.SubmissionLower.ContactExceptionalSeedCount

open ContactGenericSurface ContactExceptionalSeedAuxiliary ContactTranslation

noncomputable section

section SeedProjection

variable {T : Type*} [Field T]

def seedProjection (T : Type*) [Field T] : MvPolynomial (Fin 3) T →+* Polynomial T :=
  MvPolynomial.eval₂Hom Polynomial.C ![0, 0, Polynomial.X]

def seedEmbedding (T : Type*) [Field T] : Polynomial T →+* MvPolynomial (Fin 3) T :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 3))

theorem seed_only_vars (S : MvPolynomial (Fin 3) T)
    (hY : S.degreeOf 0 = 0) (hR : S.degreeOf 1 = 0)
    (i : Fin 3) (hi : i ∈ S.vars) : i = 2 := by
  fin_cases i
  · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hY)
  · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hR)
  · rfl

/-- This is an actual left inverse on the seed-only support subspace. -/
theorem seedProjection_reconstruct (S : MvPolynomial (Fin 3) T)
    (hY : S.degreeOf 0 = 0) (hR : S.degreeOf 1 = 0) :
    seedEmbedding T (seedProjection T S) = S := by
  change ((seedEmbedding T).comp (seedProjection T)) S = (RingHom.id _) S
  apply MvPolynomial.hom_congr_vars
  · ext a
    simp [seedEmbedding, seedProjection]
  · intro i hi _
    rw [seed_only_vars S hY hR i hi]
    simp [seedEmbedding, seedProjection]
  · rfl

theorem seedProjection_nonzero (S : MvPolynomial (Fin 3) T) (hS : S ≠ 0)
    (hY : S.degreeOf 0 = 0) (hR : S.degreeOf 1 = 0) : seedProjection T S ≠ 0 := by
  intro hz
  apply hS
  rw [← seedProjection_reconstruct S hY hR, hz, map_zero]

theorem monomial_fin3 (d : Fin 3 →₀ ℕ) (a : T) :
    MvPolynomial.monomial d a = MvPolynomial.C a * MvPolynomial.X 0 ^ d 0 *
      MvPolynomial.X 1 ^ d 1 * MvPolynomial.X 2 ^ d 2 := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) + Finsupp.single 2 (d 2) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hd]
  rw [MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial]

theorem seedProjection_monomial (d : Fin 3 →₀ ℕ) (a : T) :
    seedProjection T (MvPolynomial.monomial d a) =
      Polynomial.C a * 0 ^ d 0 * 0 ^ d 1 * Polynomial.X ^ d 2 := by
  rw [monomial_fin3]
  simp [seedProjection]

theorem seedProjection_monomial_natDegree_le (d : Fin 3 →₀ ℕ) (a : T) :
    (seedProjection T (MvPolynomial.monomial d a)).natDegree ≤ d 2 := by
  rw [seedProjection_monomial]
  have hc : (Polynomial.C a).natDegree ≤ 0 := by simp
  have h0 : ((0 : Polynomial T) ^ d 0).natDegree ≤ 0 := by
    simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 0)
      (show (0 : Polynomial T).natDegree ≤ 0 by simp)
  have h1 : ((0 : Polynomial T) ^ d 1).natDegree ≤ 0 := by
    simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 1)
      (show (0 : Polynomial T).natDegree ≤ 0 by simp)
  have hx : ((Polynomial.X : Polynomial T) ^ d 2).natDegree ≤ d 2 := by simp
  have hh := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le hc h0) h1) hx
  simpa using hh

theorem seedProjection_natDegree_le (S : MvPolynomial (Fin 3) T) :
    (seedProjection T S).natDegree ≤ S.degreeOf 2 := by
  classical
  have hsum : seedProjection T S =
      ∑ d ∈ S.support, seedProjection T (MvPolynomial.monomial d (S.coeff d)) := by
    rw [← map_sum, MvPolynomial.support_sum_monomial_coeff]
  rw [hsum]
  exact Polynomial.natDegree_sum_le_of_forall_le S.support _ (fun d hd =>
    (seedProjection_monomial_natDegree_le d (S.coeff d)).trans (MvPolynomial.monomial_le_degreeOf 2 hd))

theorem seedProjection_eval (S : MvPolynomial (Fin 3) T)
    (hY : S.degreeOf 0 = 0) (hR : S.degreeOf 1 = 0) (v : Fin 3 → T) :
    (seedProjection T S).eval (v 2) = MvPolynomial.eval v S := by
  change ((Polynomial.evalRingHom (v 2)).comp (seedProjection T)) S = (MvPolynomial.eval v) S
  apply MvPolynomial.hom_congr_vars
  · ext a
    simp [seedProjection]
  · intro i hi _
    rw [seed_only_vars S hY hR i hi]
    simp [seedProjection]
  · rfl

end SeedProjection

section GenericSurface

variable {K T : Type*} [Field K] [Field T]

def auxiliarySeedPolynomial (φ : Polynomial K →+* T) (H : MvPolynomial (Fin 4) K) : Polynomial T :=
  seedProjection T (surfaceMap φ H)

theorem surface_seed_only (φ : Polynomial K →+* T) (H : MvPolynomial (Fin 4) K)
    (hY : H.degreeOf 1 = 0) (hR : H.degreeOf 2 = 0) :
    (surfaceMap φ H).degreeOf 0 = 0 ∧ (surfaceMap φ H).degreeOf 1 = 0 :=
  ⟨Nat.eq_zero_of_le_zero ((surfaceMap_degreeOf_le φ H 0).trans_eq hY),
    Nat.eq_zero_of_le_zero ((surfaceMap_degreeOf_le φ H 1).trans_eq hR)⟩

theorem auxiliarySeedPolynomial_nonzero
    (φ : Polynomial K →+* T) (hφ : Function.Injective φ)
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    (hY : H.degreeOf 1 = 0) (hR : H.degreeOf 2 = 0) : auxiliarySeedPolynomial φ H ≠ 0 := by
  have hs := surface_seed_only φ H hY hR
  exact seedProjection_nonzero (surfaceMap φ H) (surfaceMap_ne_zero φ hφ H hH) hs.1 hs.2

theorem auxiliarySeedPolynomial_natDegree_le
    (φ : Polynomial K →+* T) (H : MvPolynomial (Fin 4) K) :
    (auxiliarySeedPolynomial φ H).natDegree ≤ H.degreeOf 3 :=
  (seedProjection_natDegree_le (surfaceMap φ H)).trans (surfaceMap_degreeOf_le φ H 2)

theorem auxiliarySeedPolynomial_eval
    (φ : Polynomial K →+* T) (H : MvPolynomial (Fin 4) K)
    (hY : H.degreeOf 1 = 0) (hR : H.degreeOf 2 = 0) (v : Fin 3 → T) :
    (auxiliarySeedPolynomial φ H).eval (v 2) = MvPolynomial.eval v (surfaceMap φ H) := by
  have hs := surface_seed_only φ H hY hR
  exact seedProjection_eval (surfaceMap φ H) hs.1 hs.2 v

/-- The seeds, not unverified geometric points, are mapped injectively
to roots of the actual nonzero univariate polynomial. -/
theorem card_surface_seeds_le
    (φ : Polynomial K →+* T) (hφ : Function.Injective φ)
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    (hY : H.degreeOf 1 = 0) (hR : H.degreeOf 2 = 0) (seeds : Finset K)
    (hsolutions : ∀ γ ∈ seeds, ∃ v : Fin 3 → T,
      v 2 = φ (Polynomial.C γ) ∧ MvPolynomial.eval v (surfaceMap φ H) = 0) :
    seeds.card ≤ H.degreeOf 3 := by
  classical
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableEq T := Classical.decEq T
  let q : Polynomial T := auxiliarySeedPolynomial φ H
  let c : K →+* T := φ.comp Polynomial.C
  have hq : q ≠ 0 := auxiliarySeedPolynomial_nonzero φ hφ H hH hY hR
  have hroots : ∀ z ∈ seeds.image c, z ∈ q.roots := by
    intro z hz
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v, hv, hzero⟩ := hsolutions γ hγ
    apply (Polynomial.mem_roots hq).mpr
    change q.eval (φ (Polynomial.C γ)) = 0
    rw [← hv]
    exact (auxiliarySeedPolynomial_eval φ H hY hR v).trans hzero
  calc
    seeds.card = (seeds.image c).card := (Finset.card_image_of_injOn c.injective.injOn).symm
    _ ≤ q.natDegree := Polynomial.card_le_degree_of_subset_roots hroots
    _ ≤ H.degreeOf 3 := auxiliarySeedPolynomial_natDegree_le φ H

end GenericSurface

section ActualSolutions

variable {K : Type*} [Field K]

theorem card_actual_solution_seeds_le
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    (hY : H.degreeOf 1 = 0) (hR : H.degreeOf 2 = 0) (seeds : Finset K)
    (hsolutions : ∀ γ ∈ seeds, ∃ P : Polynomial K, specialization K P γ H = 0) :
    seeds.card ≤ H.degreeOf 3 := by
  apply card_surface_seeds_le (ContactGenericInitialPoint.polynomialEmbedding K)
    (ContactGenericInitialPoint.polynomialEmbedding_injective K) H hH hY hR seeds
  intro γ hγ
  obtain ⟨P, hP⟩ := hsolutions γ hγ
  refine ⟨fun i => ContactGenericInitialPoint.initialPoint K P γ i.succ, ?_, ?_⟩
  · rfl
  · have hh := (ContactGeometricFirstTail.actual_generic_initial_zero_iff K P γ H).mpr hP
    simpa only [ContactGeometricFirstTail.canonical_geometricSurfaceMap] using hh

/-- The previously constructed exceptional branch has at most 2*j^2
actual seeds, including both seed-only factors and Y-singular solutions. -/
theorem exceptional_solution_seed_card_le
    (J : MvPolynomial (Fin 4) K) (hJ : J ≠ 0) (hR : J.degreeOf 2 = 0)
    (j p : ℕ) [CharP K p] (hj : 1 ≤ j) (hsmall : j < p)
    (hY : J.degreeOf 1 ≤ j) (hZ : J.degreeOf 3 ≤ j) (seeds : Finset K)
    (hsolutions : ∀ γ ∈ seeds, ∃ P : Polynomial K,
      specialization K P γ (exceptionalAuxiliary J) = 0) : seeds.card ≤ 2 * j ^ 2 := by
  have hd := exceptionalAuxiliary_data J hJ hR j p hj hsmall hY hZ
  exact (card_actual_solution_seeds_le (exceptionalAuxiliary J) hd.1 hd.2.1 hd.2.2.1
    seeds hsolutions).trans hd.2.2.2.2

#print axioms seedProjection_reconstruct
#print axioms seedProjection_nonzero
#print axioms seedProjection_natDegree_le
#print axioms seedProjection_eval
#print axioms auxiliarySeedPolynomial_nonzero
#print axioms card_surface_seeds_le
#print axioms card_actual_solution_seeds_le
#print axioms exceptional_solution_seed_card_le

end ActualSolutions

end
end ProximityPrize.SubmissionLower.ContactExceptionalSeedCount
