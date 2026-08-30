import ProximityPrize.SubmissionLower.ActualPlanePositiveOrder
import ProximityPrize.SubmissionLower.BCHKSSparseResultantDegree

namespace ProximityPrize.SubmissionLower.ActualPlaneJointProjection

open Polynomial Polynomial.Bivariate
open ActualCurveCoordinateField ActualCurveRationalProjection TrivariateRationalCollection
open ActualPlaneCoordinateKernel ActualPlaneCoordinateCaps
open ActualPlanePositiveOrder

noncomputable section

variable {A : Type} [Field A]

theorem bivariateEquiv_coeff_natDegree_le_of_support
    (f : MvPolynomial (Fin 2) A) (height : ℕ → ℕ)
    (hsupport : ∀ d ∈ f.support, d 1 ≤ height (d 0)) (i : ℕ) :
    ((bivariateEquiv A f).coeff i).natDegree ≤ height i := by
  rw [show (bivariateEquiv A f).coeff i =
      MvPolynomial.uniqueAlgEquiv A (Fin 1)
        ((MvPolynomial.finSuccEquiv A 1 f).coeff i) by
    simp [bivariateEquiv]]
  apply (uniqueAlgEquiv_natDegree_le A _).trans
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hs := hsupport (d.cons i)
    (MvPolynomial.mem_support_coeff_finSuccEquiv.mp hd)
  simpa only [show (1 : Fin 2) = (0 : Fin 1).succ by decide,
    Finsupp.cons_succ, Finsupp.cons_zero] using hs

theorem bivariateEquiv_totalDegree_le_of_support
    (f : MvPolynomial (Fin 2) A) (cap : ℕ)
    (hsupport : ∀ d ∈ f.support, d 0 + d 1 ≤ cap) :
    totalDegree (bivariateEquiv A f) ≤ cap := by
  classical
  have houter : f.degreeOf 0 ≤ cap := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (Nat.le_add_right (d 0) (d 1)).trans (hsupport d hd)
  unfold totalDegree
  apply Finset.sup_le
  intro i hi
  have hiCap : i ≤ cap := by
    exact (Polynomial.le_natDegree_of_mem_supp i hi).trans
      ((bivariateEquiv_natDegree A f).trans_le houter)
  have hcoeff : ((bivariateEquiv A f).coeff i).natDegree ≤ cap - i := by
    apply bivariateEquiv_coeff_natDegree_le_of_support f (fun j => cap - j)
    intro d hd
    have hs := hsupport d hd
    omega
  omega

variable (K : Type) [Field K]

theorem planeMap_totalDegree_le_of_rational_support
    (order : Fin 3 ≃ Fin 3) (F : Original K) (cap : ℕ)
    (hsupport : ∀ d ∈ (rationalMap K order F).support,
      d 0 + d 1 ≤ cap) :
    totalDegree (planeMap K order F) ≤ cap := by
  exact bivariateEquiv_totalDegree_le_of_support
    (rationalMap K order F) cap hsupport

theorem rationalMap_joint_support_of_original
    (order : Fin 3 ≃ Fin 3) (F : Original K) (cap : ℕ)
    (hsupport : ∀ d ∈ F.support,
      d (order 1) + d (order 2) ≤ cap) :
    ∀ e ∈ (rationalMap K order F).support, e 0 + e 1 ≤ cap := by
  classical
  intro e he
  rw [rationalMap_eq_firstMap] at he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
    (support_firstMap_subset K
      (algebraMap (Polynomial K) (RatFunc K))
      (MvPolynomial.rename order.symm F) he)
  rw [MvPolynomial.support_rename_of_injective order.symm.injective] at hd
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hd
  simpa only [Finsupp.tail_apply, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm,
    show (0 : Fin 2).succ = (1 : Fin 3) by decide,
    show (1 : Fin 2).succ = (2 : Fin 3) by decide] using hsupport u hu

theorem ordinary_resultant_natDegree_le_totalDegree
    (B H : A[X][Y]) (n mCap totalB totalH cap : ℕ)
    (hHne : H ≠ 0) (hBouter : B.natDegree ≤ n)
    (hHouter : H.natDegree ≤ mCap)
    (hBtotal : totalDegree B ≤ totalB)
    (hHtotal : totalDegree H ≤ totalH)
    (hbudget : ∀ m, m ≤ mCap →
      m * totalB + n * totalH - m * n ≤ cap) :
    (Polynomial.resultant B H).natDegree ≤ cap := by
  by_cases hres : Polynomial.resultant B H = 0
  · simp [hres]
  · have hfixed := bivariate_resultant_natDegree_le_totalDegree
      B H n H.natDegree
    have hdegreeCap :
        H.natDegree * totalDegree B + n * totalDegree H - H.natDegree * n ≤
          H.natDegree * totalB + n * totalH - H.natDegree * n := by
      exact Nat.sub_le_sub_right
        (Nat.add_le_add (Nat.mul_le_mul_left H.natDegree hBtotal)
          (Nat.mul_le_mul_left n hHtotal)) _
    have hfixedCap :
        (Polynomial.resultant B H n H.natDegree).natDegree ≤ cap :=
      hfixed.trans (hdegreeCap.trans (hbudget H.natDegree hHouter))
    have hcoeff : H.coeff H.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hHne
    let factor : A[X] :=
      (-1) ^ (H.natDegree * (n - B.natDegree)) *
        H.coeff H.natDegree ^ (n - B.natDegree)
    have hfactor : factor ≠ 0 := by
      apply _root_.mul_ne_zero
      · exact pow_ne_zero _ (by norm_num)
      · exact pow_ne_zero _ hcoeff
    have hpad := Polynomial.resultant_add_left_deg
      (f := B) (g := H) (m := B.natDegree)
      (k := n - B.natDegree) (n := H.natDegree) le_rfl
    have hsum : B.natDegree + (n - B.natDegree) = n :=
      Nat.add_sub_of_le hBouter
    rw [hsum] at hpad
    change Polynomial.resultant B H n H.natDegree =
      factor * Polynomial.resultant B H at hpad
    calc
      (Polynomial.resultant B H).natDegree ≤
          (factor * Polynomial.resultant B H).natDegree := by
        rw [Polynomial.natDegree_mul hfactor hres]
        omega
      _ = (Polynomial.resultant B H n H.natDegree).natDegree := by rw [hpad]
      _ ≤ cap := hfixedCap

theorem planeMap_trapezoid_resultant_natDegree_le
    (order : Fin 3 ≃ Fin 3) (G T : Original K)
    (n mCap totalG totalT cap : ℕ) (hTne : T ≠ 0)
    (hGouter : (planeMap K order G).natDegree ≤ n)
    (hTouter : (planeMap K order T).natDegree ≤ mCap)
    (hGsupport : ∀ d ∈ (rationalMap K order G).support,
      d 0 + d 1 ≤ totalG)
    (hTsupport : ∀ d ∈ (rationalMap K order T).support,
      d 0 + d 1 ≤ totalT)
    (hbudget : ∀ m, m ≤ mCap →
      m * totalG + n * totalT - m * n ≤ cap) :
    (Polynomial.resultant (planeMap K order G)
      (planeMap K order T)).natDegree ≤ cap := by
  apply ordinary_resultant_natDegree_le_totalDegree
    (planeMap K order G) (planeMap K order T)
      n mCap totalG totalT cap
  · intro hzero
    apply hTne
    apply planeMap_injective K order
    simpa only [map_zero] using hzero
  · exact hGouter
  · exact hTouter
  · exact planeMap_totalDegree_le_of_rational_support
      K order G totalG hGsupport
  · exact planeMap_totalDegree_le_of_rational_support
      K order T totalT hTsupport
  · exact hbudget

end

end ProximityPrize.SubmissionLower.ActualPlaneJointProjection
