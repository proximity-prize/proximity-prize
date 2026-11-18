import ProximityPrize.SubmissionLower.Koala6831OrdinarySurface
import Mathlib.RingTheory.Localization.Integer

namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open RCN136 MvPolynomial
open scoped Classical Polynomial BigOperators

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

private theorem collectX_monomial (d : Fin 4 →₀ ℕ) (a : K) :
    collectX K (MvPolynomial.monomial d a) =
      MvPolynomial.monomial d.tail (Polynomial.monomial (d 0) a) := by
  simp only [MvPolynomial.monomial_eq, Finsupp.prod_pow, map_mul, map_prod, map_pow]
  rw [Fin.prod_univ_succ]
  simp only [collectX_C, collectX_X_zero, collectX_X_succ, Finsupp.tail_apply,
    ← mul_assoc, ← map_pow, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]

private theorem collectX_coeff_coeff (F : Carrier K) (d : Fin 4 →₀ ℕ) :
    ((collectX K F).coeff d.tail).coeff (d 0) = F.coeff d := by
  induction F using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Polynomial.coeff_add, hP, hQ]
  | monomial e a =>
    simp only [collectX_monomial, MvPolynomial.coeff_monomial]
    by_cases ht : e.tail = d.tail
    · by_cases h₀ : e 0 = d 0
      · have he : e = d := by
          rw [← Finsupp.cons_tail e, ← Finsupp.cons_tail d, ht, h₀]
        subst e
        simp
      · have hne : e ≠ d := fun h => h₀ (congrArg (fun s : Fin 4 →₀ ℕ => s 0) h)
        simp [ht, h₀, hne, Polynomial.coeff_monomial]
    · have hne : e ≠ d := fun h => ht (congrArg Finsupp.tail h)
      simp [ht, hne]

private theorem ordinarySurface_map_collect {E : Type*} [Field E]
    (φ : K[X] →+* E) (F : Carrier K) :
    ordinarySurface φ F = MvPolynomial.map φ
      (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) (collectX K F)) := by
  change MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1)
    (MvPolynomial.map φ (collectX K F)) = _
  rw [MvPolynomial.map_rename]

private theorem project_support_ordinarySurface {E : Type*} [Field E]
    (φ : K[X] →+* E) (hφ : Function.Injective φ)
    (F : Carrier K) (d : Fin 4 →₀ ℕ) (hd : d ∈ F.support) :
    Finsupp.mapDomain (Equiv.swap (0 : Fin 3) 1) d.tail ∈ (ordinarySurface φ F).support := by
  have hd' : (collectX K F).coeff d.tail ≠ 0 := by
    intro hzero
    have hc := collectX_coeff_coeff F d
    rw [hzero, Polynomial.coeff_zero] at hc
    exact (MvPolynomial.mem_support_iff.mp hd) hc.symm
  apply MvPolynomial.mem_support_iff.mpr
  rw [ordinarySurface_map_collect, MvPolynomial.coeff_map,
    MvPolynomial.coeff_rename_mapDomain _ (Equiv.swap (0 : Fin 3) 1).injective]
  exact fun hz => hd' (hφ (hz.trans φ.map_zero.symm))

private theorem clear_ratfunc_coefficients (H : MvPolynomial (Fin 3) (RatFunc K)) :
    ∃ (N : MvPolynomial (Fin 3) K[X]) (D : K[X]), D ≠ 0 ∧
      MvPolynomial.map (algebraMap K[X] (RatFunc K)) N =
        MvPolynomial.C (algebraMap K[X] (RatFunc K) D) * H := by
  let S := nonZeroDivisors K[X]
  let D := IsLocalization.commonDenom S H.support (fun d => H.coeff d)
  let N : MvPolynomial (Fin 3) K[X] :=
    ∑ d : H.support, MvPolynomial.monomial (d : Fin 3 →₀ ℕ)
      (IsLocalization.integerMultiple S H.support (fun e => H.coeff e) d)
  refine ⟨N, D, nonZeroDivisors.ne_zero D.property, ?_⟩
  calc
    _ = ∑ d : H.support, MvPolynomial.C (algebraMap K[X] (RatFunc K) D) *
          MvPolynomial.monomial (d : Fin 3 →₀ ℕ) (H.coeff d) := by
      rw [show MvPolynomial.map (algebraMap K[X] (RatFunc K)) N =
        ∑ d : H.support, MvPolynomial.map (algebraMap K[X] (RatFunc K))
          (MvPolynomial.monomial (d : Fin 3 →₀ ℕ)
            (IsLocalization.integerMultiple S H.support (fun e => H.coeff e) d)) by
        unfold N
        rw [map_sum]]
      apply Finset.sum_congr rfl
      intro d _
      simp only [MvPolynomial.map_monomial, IsLocalization.map_integerMultiple, MvPolynomial.C_mul_monomial]
      change MvPolynomial.monomial (d : Fin 3 →₀ ℕ) ((D : K[X]) • H.coeff d) = _
      rw [Algebra.smul_def]
    _ = _ := by
      have hsum : (∑ d : H.support, MvPolynomial.monomial (d : Fin 3 →₀ ℕ) (H.coeff d)) = H :=
        (Finset.sum_coe_sort H.support (fun d => MvPolynomial.monomial d (H.coeff d))).trans
          (MvPolynomial.as_sum H).symm
      rw [← Finset.mul_sum, hsum]

theorem exists_integral_carrier_lift (H : MvPolynomial (Fin 3) (RatFunc K)) :
    ∃ (F : Carrier K) (D : K[X]), D ≠ 0 ∧
      ordinarySurface (algebraMap K[X] (RatFunc K)) F =
        MvPolynomial.C (algebraMap K[X] (RatFunc K) D) * H ∧
      ∀ d ∈ F.support, d 1 ≤ H.degreeOf (1 : Fin 3) ∧
        d 1 + d 2 + d 3 ≤ H.totalDegree := by
  obtain ⟨N, D, hD, hN⟩ := clear_ratfunc_coefficients H
  let swap := MvPolynomial.renameEquiv K[X] (Equiv.swap (0 : Fin 3) 1)
  let F := (collectX K).symm (swap.symm N)
  have hcollect : swap (collectX K F) = N := by simp [F]
  have hsurface : ordinarySurface (algebraMap K[X] (RatFunc K)) F =
      MvPolynomial.C (algebraMap K[X] (RatFunc K) D) * H := by
    rw [ordinarySurface_map_collect]
    change MvPolynomial.map (algebraMap K[X] (RatFunc K)) (swap (collectX K F)) = _
    rw [hcollect, hN]
  refine ⟨F, D, hD, hsurface, ?_⟩
  intro d hd
  let e := Finsupp.mapDomain (Equiv.swap (0 : Fin 3) 1) d.tail
  have he : e ∈ H.support := by
    have h := project_support_ordinarySurface (algebraMap K[X] (RatFunc K))
      (IsFractionRing.injective _ _) F d hd
    change e ∈ (ordinarySurface (algebraMap K[X] (RatFunc K)) F).support at h
    rw [hsurface] at h
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    have hnonzero := MvPolynomial.mem_support_iff.mp h
    rw [MvPolynomial.coeff_C_mul, hz, mul_zero] at hnonzero
    exact hnonzero rfl
  have h₀ : e 0 = d 2 := by rw [show e = Finsupp.mapDomain (Equiv.swap (0 : Fin 3) 1) d.tail from rfl, Finsupp.mapDomain_equiv_apply]; rfl
  have h₁ : e 1 = d 1 := by rw [show e = Finsupp.mapDomain (Equiv.swap (0 : Fin 3) 1) d.tail from rfl, Finsupp.mapDomain_equiv_apply]; rfl
  have h₂ : e 2 = d 3 := by rw [show e = Finsupp.mapDomain (Equiv.swap (0 : Fin 3) 1) d.tail from rfl, Finsupp.mapDomain_equiv_apply]; rfl
  refine ⟨h₁ ▸ MvPolynomial.monomial_le_degreeOf (1 : Fin 3) he, ?_⟩
  have htotal := MvPolynomial.le_totalDegree he
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at htotal
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at htotal
  change e 0 + (e 1 + e 2) ≤ H.totalDegree at htotal
  rw [h₀, h₁, h₂] at htotal
  omega

end

end ProximityPrize.SubmissionLower.Koala6831Ordinary
