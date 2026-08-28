import ProximityPrize.SubmissionLower.ActualPlaneCoordinateCaps
import ProximityPrize.SubmissionLower.ContactSparseResultantDegree

/-!
# Sparse coordinate caps for actual plane maps

This transports a two-variable Newton-trapezoid cap through the actual
`MvPolynomial (Fin 2)` to nested-polynomial equivalence and applies the sparse
Sylvester bound.  The hypothesis is deliberately stated on the collected
rational map; later contact-specific code supplies it from the joint seed cap.
-/

namespace ProximityPrize.SubmissionLower.ActualPlaneSparseCoordinateCaps

open ActualPlaneCoordinateKernel ActualPlaneCoordinateCaps
open TrivariateRationalCollection

noncomputable section

variable {A : Type} [Field A]

theorem totalDegree_le_of_fin2_support_cap
    (f : MvPolynomial (Fin 2) A) (L : ℕ)
    (hcap : ∀ d ∈ f.support, d 0 + d 1 ≤ L) :
    f.totalDegree ≤ L := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro d hd
  simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using hcap d hd

theorem bivariateEquiv_coeff_natDegree_add_le
    (f : MvPolynomial (Fin 2) A) (L n k : ℕ)
    (hn : n ≤ L) (hk : k ≤ n)
    (htotal : f.totalDegree ≤ L) :
    ((bivariateEquiv A f).coeff k).natDegree + k ≤ L := by
  classical
  have heq : (bivariateEquiv A f).coeff k =
      MvPolynomial.uniqueAlgEquiv A (Fin 1)
        ((MvPolynomial.finSuccEquiv A 1 f).coeff k) := by
    simp [bivariateEquiv]
  by_cases hz : (MvPolynomial.finSuccEquiv A 1 f).coeff k = 0
  · simp [heq, hz]
    exact hk.trans hn
  · have hnat :
        (MvPolynomial.uniqueAlgEquiv A (Fin 1)
          ((MvPolynomial.finSuccEquiv A 1 f).coeff k)).natDegree ≤
            ((MvPolynomial.finSuccEquiv A 1 f).coeff k).totalDegree :=
      (uniqueAlgEquiv_natDegree_le A _).trans
        (MvPolynomial.degreeOf_le_totalDegree _ 0)
    have hcoeff := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le f k hz
    rw [heq]
    omega

variable (K : Type) [Field K]

theorem rationalMap_support_pair_cap
    (order : Fin 3 ≃ Fin 3) (F : Original K) (L : ℕ)
    (hcap : ∀ d ∈ F.support, d (order 1) + d (order 2) ≤ L) :
    ∀ e ∈ (rationalMap K order F).support, e 0 + e 1 ≤ L := by
  classical
  rw [rationalMap_eq_firstMap]
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
    (support_firstMap_subset K (algebraMap (Polynomial K) (RatFunc K))
      (MvPolynomial.rename order.symm F) he)
  rw [MvPolynomial.support_rename_of_injective order.symm.injective] at hd
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hd
  simpa [Finsupp.tail_apply] using hcap u hu

theorem planeMap_resultant_natDegree_add_mul_le_of_rational_support_caps
    (order : Fin 3 ≃ Fin 3) (G H : Original K) (LG LH : ℕ)
    (hGcap : ∀ d ∈ (rationalMap K order G).support, d 0 + d 1 ≤ LG)
    (hHcap : ∀ d ∈ (rationalMap K order H).support, d 0 + d 1 ≤ LH) :
    (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree +
        (planeMap K order G).natDegree * (planeMap K order H).natDegree ≤
      (planeMap K order H).natDegree * LG +
        (planeMap K order G).natDegree * LH := by
  let g := rationalMap K order G
  let h := rationalMap K order H
  have hgTotal : g.totalDegree ≤ LG :=
    totalDegree_le_of_fin2_support_cap g LG hGcap
  have hhTotal : h.totalDegree ≤ LH :=
    totalDegree_le_of_fin2_support_cap h LH hHcap
  have hgOuter : (planeMap K order G).natDegree ≤ LG := by
    rw [show planeMap K order G = bivariateEquiv (RatFunc K) g by rfl,
      bivariateEquiv_natDegree]
    exact (MvPolynomial.degreeOf_le_totalDegree g 0).trans hgTotal
  have hhOuter : (planeMap K order H).natDegree ≤ LH := by
    rw [show planeMap K order H = bivariateEquiv (RatFunc K) h by rfl,
      bivariateEquiv_natDegree]
    exact (MvPolynomial.degreeOf_le_totalDegree h 0).trans hhTotal
  apply ContactSparseResultantDegree.bivariate_resultant_natDegree_add_mul_le
    (planeMap K order G) (planeMap K order H)
    (planeMap K order G).natDegree (planeMap K order H).natDegree LG LH
    hhOuter hgOuter
  · intro k hk
    exact bivariateEquiv_coeff_natDegree_add_le h LH
      (planeMap K order H).natDegree k hhOuter hk hhTotal
  · intro k hk
    exact bivariateEquiv_coeff_natDegree_add_le g LG
      (planeMap K order G).natDegree k hgOuter hk hgTotal

theorem sparse_expression_mono
    (n m NG MH LG LH : ℕ)
    (hn : n ≤ NG) (hm : m ≤ MH) (hMH : MH ≤ LH) (hNG : NG ≤ LG) :
    m * LG + n * LH + NG * MH ≤ MH * LG + NG * LH + n * m := by
  have hn' : n + (NG - n) = NG := Nat.add_sub_of_le hn
  have hm' : m + (MH - m) = MH := Nat.add_sub_of_le hm
  have hnonneg₁ : 0 ≤ (NG - n) * (LH - m) := Nat.zero_le _
  have hnonneg₂ : 0 ≤ (MH - m) * (LG - NG) := Nat.zero_le _
  have hLH : m + (LH - m) = LH := Nat.add_sub_of_le (hm.trans hMH)
  have hLG : NG + (LG - NG) = LG := Nat.add_sub_of_le hNG
  nlinarith

theorem planeMap_resultant_natDegree_lt_of_sparse_caps
    (order : Fin 3 ≃ Fin 3) (G H : Original K)
    (NG MH LG LH p : ℕ)
    (hNG : (planeMap K order G).natDegree ≤ NG)
    (hMH : (planeMap K order H).natDegree ≤ MH)
    (hNGjoint : NG ≤ LG) (hMHjoint : MH ≤ LH)
    (hGcap : ∀ d ∈ (rationalMap K order G).support, d 0 + d 1 ≤ LG)
    (hHcap : ∀ d ∈ (rationalMap K order H).support, d 0 + d 1 ≤ LH)
    (hgate : MH * LG + NG * LH < p + NG * MH) :
    (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree < p := by
  have hres := planeMap_resultant_natDegree_add_mul_le_of_rational_support_caps
    K order G H LG LH hGcap hHcap
  have hmono := sparse_expression_mono
    (planeMap K order G).natDegree (planeMap K order H).natDegree
    NG MH LG LH hNG hMH hMHjoint hNGjoint
  omega

end

#print axioms totalDegree_le_of_fin2_support_cap
#print axioms bivariateEquiv_coeff_natDegree_add_le
#print axioms rationalMap_support_pair_cap
#print axioms planeMap_resultant_natDegree_add_mul_le_of_rational_support_caps
#print axioms sparse_expression_mono
#print axioms planeMap_resultant_natDegree_lt_of_sparse_caps

end ProximityPrize.SubmissionLower.ActualPlaneSparseCoordinateCaps
