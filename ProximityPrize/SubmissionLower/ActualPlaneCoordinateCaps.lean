import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel
import ProximityPrize.SubmissionLower.BCHKSResultantDegree


/-!
# Original separated caps for the actual coordinate projection

Model label: gpt-5.

The common ordering is (t,R,Y). This file bounds the actual outer degree,
inner degree, and resultant degree after collection and rational
localization by the ORIGINAL trivariate separated degrees. Support
projection and the actual nested-polynomial equivalence provide the
bounds; no degree-preservation or projection-budget hypothesis is used.

Positive outer degree, choice of an ordering, and the geometric field
degree application are separate steps.
-/

namespace ProximityPrize.SubmissionLower.ActualPlaneCoordinateCaps

open TrivariateRationalCollection ActualPlaneCoordinateKernel

noncomputable section

variable (K : Type) [Field K]

section FirstCoordinate

variable {A : Type} [Field A]

def firstMap (φ : Polynomial K →+* A) :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) A :=
  (MvPolynomial.map φ).comp (collectFirst K).toRingHom

@[simp] theorem firstMap_C (φ : Polynomial K →+* A) (a : K) :
    firstMap K φ (MvPolynomial.C a) = MvPolynomial.C (φ (Polynomial.C a)) := by
  simp [firstMap, collectFirst, MvPolynomial.renameEquiv_apply]

@[simp] theorem firstMap_X_zero (φ : Polynomial K →+* A) :
    firstMap K φ (MvPolynomial.X (0 : Fin 3)) = MvPolynomial.C (φ Polynomial.X) := by
  simp [firstMap, collectFirst, MvPolynomial.renameEquiv_apply]

@[simp] theorem firstMap_X_succ (φ : Polynomial K →+* A) (i : Fin 2) :
    firstMap K φ (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [firstMap, collectFirst, MvPolynomial.renameEquiv_apply]

theorem firstMap_eq_eval₂Hom (φ : Polynomial K →+* A) :
    firstMap K φ =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (φ.comp Polynomial.C))
        (Fin.cases (MvPolynomial.C (φ Polynomial.X)) MvPolynomial.X) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem firstMap_monomial (φ : Polynomial K →+* A)
    (d : Fin 3 →₀ ℕ) (a : K) :
    firstMap K φ (MvPolynomial.monomial d a) =
      MvPolynomial.monomial d.tail (φ (Polynomial.C a) * (φ Polynomial.X) ^ d 0) := by
  rw [firstMap_eq_eval₂Hom, MvPolynomial.eval₂Hom_monomial]
  simp only [RingHom.comp_apply, Finsupp.prod_pow, Fin.prod_univ_succ, Fin.cases_zero,
    Fin.cases_succ, MvPolynomial.monomial_eq, Finsupp.tail_apply, map_mul, map_pow]
  ring

theorem support_firstMap_subset (φ : Polynomial K →+* A)
    (F : MvPolynomial (Fin 3) K) :
    (firstMap K φ F).support ⊆ F.support.image Finsupp.tail := by
  classical
  have hsum : firstMap K φ F =
      ∑ d ∈ F.support, firstMap K φ (MvPolynomial.monomial d (MvPolynomial.coeff d F)) := by
    rw [← map_sum, MvPolynomial.support_sum_monomial_coeff]
  intro e he
  rw [hsum] at he
  obtain ⟨d, hd, hed⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  rw [firstMap_monomial] at hed
  have heq : e = d.tail := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)
  exact Finset.mem_image.mpr ⟨d, hd, heq.symm⟩

theorem firstMap_degreeOf_le (φ : Polynomial K →+* A)
    (F : MvPolynomial (Fin 3) K) (i : Fin 2) :
    (firstMap K φ F).degreeOf i ≤ F.degreeOf i.succ := by
  classical
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_firstMap_subset K φ F he)
  exact MvPolynomial.monomial_le_degreeOf i.succ hd

end FirstCoordinate

theorem rationalMap_eq_firstMap (order : Fin 3 ≃ Fin 3) (F : Original K) :
    rationalMap K order F = firstMap K (algebraMap (Polynomial K) (RatFunc K))
      (MvPolynomial.rename order.symm F) := rfl

theorem rationalMap_degreeOf_le (order : Fin 3 ≃ Fin 3) (F : Original K) (i : Fin 2) :
    (rationalMap K order F).degreeOf i ≤ F.degreeOf (order i.succ) := by
  rw [rationalMap_eq_firstMap]
  calc
    _ ≤ (MvPolynomial.rename order.symm F).degreeOf i.succ :=
      firstMap_degreeOf_le K _ _ i
    _ = F.degreeOf (order i.succ) := by
      simpa only [Equiv.symm_apply_apply] using
        (MvPolynomial.degreeOf_rename_of_injective (p := F) order.symm.injective
          (order i.succ))

section NestedDegrees

variable (A : Type) [Field A]

theorem bivariateEquiv_natDegree (f : MvPolynomial (Fin 2) A) :
    (bivariateEquiv A f).natDegree = f.degreeOf 0 := by
  change (Polynomial.map (MvPolynomial.uniqueAlgEquiv A (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv A 1 f)).natDegree = f.degreeOf 0
  rw [Polynomial.natDegree_map_eq_of_injective (MvPolynomial.uniqueAlgEquiv A (Fin 1)).injective]
  exact MvPolynomial.natDegree_finSuccEquiv f

theorem uniqueAlgEquiv_natDegree_le (f : MvPolynomial (Fin 1) A) :
    (MvPolynomial.uniqueAlgEquiv A (Fin 1) f).natDegree ≤ f.degreeOf 0 := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  by_contra hne
  have hd := MvPolynomial.monomial_le_degreeOf (0 : Fin 1)
    (MvPolynomial.mem_support_iff.mpr hne)
  have hdefault : (default : Fin 1) = 0 := Subsingleton.elim _ _
  simp only [hdefault, Finsupp.single_eq_same] at hd
  omega

theorem bivariateEquiv_degreeX_le (f : MvPolynomial (Fin 2) A) :
    Polynomial.Bivariate.degreeX (bivariateEquiv A f) ≤ f.degreeOf 1 := by
  classical
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro j _
  rw [show (bivariateEquiv A f).coeff j =
    MvPolynomial.uniqueAlgEquiv A (Fin 1) ((MvPolynomial.finSuccEquiv A 1 f).coeff j) by
    simp [bivariateEquiv]]
  exact (uniqueAlgEquiv_natDegree_le A _).trans
    (MvPolynomial.degreeOf_coeff_finSuccEquiv f (0 : Fin 1) j)

end NestedDegrees

theorem planeMap_natDegree_le (order : Fin 3 ≃ Fin 3) (F : Original K) :
    (planeMap K order F).natDegree ≤ F.degreeOf (order 1) := by
  change (bivariateEquiv (RatFunc K) (rationalMap K order F)).natDegree ≤ _
  rw [bivariateEquiv_natDegree]
  exact rationalMap_degreeOf_le K order F (0 : Fin 2)

theorem planeMap_degreeX_le (order : Fin 3 ≃ Fin 3) (F : Original K) :
    Polynomial.Bivariate.degreeX (planeMap K order F) ≤ F.degreeOf (order 2) := by
  exact (bivariateEquiv_degreeX_le (RatFunc K) (rationalMap K order F)).trans
    (rationalMap_degreeOf_le K order F (1 : Fin 2))

/-- The ORIGINAL two-coordinate mixed budget bounds the actual ordinary
resultant over the selected rational-function coefficient field. -/
theorem planeMap_resultant_natDegree_le (order : Fin 3 ≃ Fin 3) (G H : Original K) :
    (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree ≤
      H.degreeOf (order 1) * G.degreeOf (order 2) +
        G.degreeOf (order 1) * H.degreeOf (order 2) := by
  exact (bivariate_resultant_natDegree_le (planeMap K order G) (planeMap K order H)
    (planeMap K order G).natDegree (planeMap K order H).natDegree).trans
      (Nat.add_le_add
        (Nat.mul_le_mul (planeMap_natDegree_le K order H) (planeMap_degreeX_le K order G))
        (Nat.mul_le_mul (planeMap_natDegree_le K order G) (planeMap_degreeX_le K order H)))

theorem original_characteristic_gates (order : Fin 3 ≃ Fin 3) (G H : Original K) (p : ℕ)
    (houter : G.degreeOf (order 1) < p)
    (hmixed : H.degreeOf (order 1) * G.degreeOf (order 2) +
      G.degreeOf (order 1) * H.degreeOf (order 2) < p) :
    (planeMap K order G).natDegree < p ∧
      (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree < p :=
  ⟨(planeMap_natDegree_le K order G).trans_lt houter,
    (planeMap_resultant_natDegree_le K order G H).trans_lt hmixed⟩

end


end ProximityPrize.SubmissionLower.ActualPlaneCoordinateCaps
