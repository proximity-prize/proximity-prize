import ProximityPrize.SubmissionLower.Koala6844VirtualHighResultant
import ProximityPrize.SubmissionLower.Koala6844VirtualHighCount


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open RCN136 RCN132 Koala6844BivariateSeeds
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

variable {K : Type} [Field K]

private theorem collectX_monomial (d : Fin 4 →₀ ℕ) (a : K) :
    collectX K (MvPolynomial.monomial d a) =
      MvPolynomial.monomial d.tail (Polynomial.monomial (d 0) a) := by
  simp only [MvPolynomial.monomial_eq, Finsupp.prod_pow, map_mul, map_prod, map_pow]
  rw [Fin.prod_univ_succ]
  simp only [collectX_C, collectX_X_zero, collectX_X_succ, Finsupp.tail_apply,
    ← mul_assoc, ← map_pow, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]

private theorem collectX_coeff_coeff (F : MvPolynomial (Fin 4) K) (d : Fin 4 →₀ ℕ) :
    ((collectX K F).coeff d.tail).coeff (d 0) = F.coeff d := by
  induction F using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Polynomial.coeff_add, hP, hQ]
  | monomial e a =>
    simp only [collectX_monomial, MvPolynomial.coeff_monomial]
    by_cases ht : e.tail = d.tail
    · by_cases h₀ : e 0 = d 0
      · have he : e = d := by rw [← Finsupp.cons_tail e, ← Finsupp.cons_tail d, ht, h₀]
        subst e
        simp
      · have hne : e ≠ d := fun h => h₀ (congrArg (fun s : Fin 4 →₀ ℕ => s 0) h)
        simp [ht, h₀, hne, Polynomial.coeff_monomial]
    · have hne : e ≠ d := fun h => ht (congrArg Finsupp.tail h)
      simp [ht, hne]

theorem rationalSurface_degreeOf (F : MvPolynomial (Fin 4) K) (i : Fin 3) :
    (rationalSurfaceMap K F).degreeOf i = F.degreeOf i.succ := by
  apply le_antisymm
  · exact surfaceMap_degreeOf_le _ F i
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have hcol : (collectX K F).coeff d.tail ≠ 0 := by
      intro hz
      have he := collectX_coeff_coeff F d
      rw [hz,Polynomial.coeff_zero] at he
      exact (MvPolynomial.mem_support_iff.mp hd) he.symm
    have hs : d.tail ∈ (rationalSurfaceMap K F).support := by
      apply MvPolynomial.mem_support_iff.mpr
      change (MvPolynomial.map (algebraMap (Polynomial K) (RationalCoefficients K))
        (collectX K F)).coeff d.tail ≠ 0
      rw [MvPolynomial.coeff_map]
      exact fun hz => hcol (IsFractionRing.injective (Polynomial K) (RationalCoefficients K)
        (hz.trans (map_zero _).symm))
    exact MvPolynomial.monomial_le_degreeOf i hs

theorem coeff_collectValue_degree_le {E : Type} [Field E]
    (F : MvPolynomial (Fin 3) E) (j : ℕ) (i : Fin 2) :
    ((MvPolynomial.finSuccEquiv E 2 F).coeff j).degreeOf i ≤ F.degreeOf i.succ := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  have hh := MvPolynomial.mem_support_coeff_finSuccEquiv.mp he
  simpa only [Finsupp.cons_succ] using MvPolynomial.monomial_le_degreeOf i.succ hh

theorem eval₂_collectValue {E : Type} [Field E]
    (F : MvPolynomial (Fin 3) E) (v : E) (z : Fin 2 → E) :
    (MvPolynomial.finSuccEquiv E 2 F).eval₂ (MvPolynomial.eval z) v =
      MvPolynomial.eval (Fin.cases v z) F := by
  have h : (Polynomial.eval₂RingHom (MvPolynomial.eval z) v).comp
      (MvPolynomial.finSuccEquiv E 2).toRingHom = MvPolynomial.eval (Fin.cases v z) := by
    apply MvPolynomial.ringHom_ext
    · simp [MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [MvPolynomial.finSuccEquiv_X_zero]
      · simp [MvPolynomial.finSuccEquiv_X_succ]
  exact DFunLike.congr_fun h F

def integralRectangle (F : MvPolynomial (Fin 4) K) : Rectangle :=
  ⟨F.degreeOf 1, F.degreeOf 2, F.degreeOf 3⟩

theorem cardinal_resolved_integral_pair {Seed : Type} [Field Seed]
    (embed : Seed →+* RationalCoefficients K) (p : ℕ)
    (F H : MvPolynomial (Fin 4) K)
    (hirr : Irreducible F) (hpos : 0 < F.degreeOf 1) (hproper : ¬ F ∣ H)
    (hsmall : F.degreeOf 1 * H.degreeOf 2 + H.degreeOf 1 * F.degreeOf 2 < p)
    (seeds : Finset Seed) (values : Seed → RationalCoefficients K)
    (hf : ∀ g ∈ seeds, MvPolynomial.eval (Fin.cases (values g)
      (coordinates (embed g) ((embed g)^p))) (rationalSurfaceMap K F) = 0)
    (hh : ∀ g ∈ seeds, MvPolynomial.eval (Fin.cases (values g)
      (coordinates (embed g) ((embed g)^p))) (rationalSurfaceMap K H) = 0) :
    seeds.card ≤ resultantCharge p (integralRectangle F) (integralRectangle H) := by
  let pack := MvPolynomial.finSuccEquiv (RationalCoefficients K) 2
  let F' := pack (rationalSurfaceMap K F)
  let H' := pack (rationalSurfaceMap K H)
  have hpositive : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 := by omega
  have hF' : Irreducible F' := (MulEquiv.irreducible_iff pack).mpr
    (rationalSurfaceMap_irreducible K F hirr hpositive)
  have hproper' : ¬ F' ∣ H' := fun hd => hproper ((rationalSurfaceMap_dvd_iff K F H hirr hpositive).mp
    ((map_dvd_iff pack).mp hd))
  have hout (P : MvPolynomial (Fin 4) K) :
      (pack (rationalSurfaceMap K P)).natDegree = P.degreeOf 1 := by
    rw [MvPolynomial.natDegree_finSuccEquiv, rationalSurface_degreeOf]
    rfl
  let a (i : Fin 2) := F.degreeOf i.succ.succ
  let b (i : Fin 2) := H.degreeOf i.succ.succ
  have hcap (P : MvPolynomial (Fin 4) K) (j : ℕ) (i : Fin 2) :
      ((pack (rationalSurfaceMap K P)).coeff j).degreeOf i ≤ P.degreeOf i.succ.succ := by
    exact (coeff_collectValue_degree_le (rationalSurfaceMap K P) j i).trans_eq
      (rationalSurface_degreeOf P i.succ)
  have hn := card_le_of_resolved_pair embed p F' H' hF'
    ((hout F).symm ▸ hpos) hproper' a b (hcap F) (hcap H)
    (by rw [show F'.natDegree = F.degreeOf 1 from hout F,
      show H'.natDegree = H.degreeOf 1 from hout H]
        exact hsmall)
    seeds values
    (fun g hg => (eval₂_collectValue _ _ _).trans (hf g hg))
    (fun g hg => (eval₂_collectValue _ _ _).trans (hh g hg))
  rw [show F'.natDegree = F.degreeOf 1 from hout F,
    show H'.natDegree = H.degreeOf 1 from hout H] at hn
  exact hn

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

