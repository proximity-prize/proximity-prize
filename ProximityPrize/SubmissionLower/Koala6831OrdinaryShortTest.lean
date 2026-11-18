import ProximityPrize.SubmissionLower.Koala6831OrdinaryFullTest

namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open Koala6831Intrinsic (implicitRegularity)
open Koala6831OrdinaryIncidence (ordinaryFlag cutFlag)
open RCN095 RCN234 MvPolynomial
open scoped Classical Polynomial BigOperators

set_option autoImplicit false

variable {K E L : Type*} [Field K] [Field E] [Field L]

noncomputable def shortOrdinaryTest (φ : K[X] →+* E) (F : Carrier K)
    (u : ℕ) (weights : ℕ → E) (a b : E) : MvPolynomial (Fin 3) E :=
  (∑ j ∈ Finset.range (u + 1),
      MvPolynomial.C (weights j) * ordinarySurface φ (clearedTaylorCoeff F u j)) -
    ordinarySurface φ (implicitRegularity F) ^ (2 * u) *
      (MvPolynomial.C a + MvPolynomial.X 0 * MvPolynomial.C b)

theorem eval_shortOrdinaryTest [Algebra E L] (φ : K[X] →+* E) (F : Carrier K)
    (u : ℕ) (weights : ℕ → E) (a b : E) (v : Fin 3 → L)
    (hreg : MvPolynomial.aeval v (ordinarySurface φ (implicitRegularity F)) ≠ 0) :
    MvPolynomial.aeval v (shortOrdinaryTest φ F u weights a b) =
      (MvPolynomial.aeval v (ordinarySurface φ (implicitRegularity F))) ^ (2 * u) *
        ((∑ j ∈ Finset.range (u + 1), algebraMap E L (weights j) * ordinaryJet φ F v j) -
          (algebraMap E L a + v 0 * algebraMap E L b)) := by
  simp only [shortOrdinaryTest, map_sub, map_sum, map_mul, map_pow, map_add,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [eval_clearedTaylorCoeff φ F v u j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hreg]
  ring

private theorem short_separant_weight_le (weights : Fin 4 → ℕ) (F : Carrier K) (cap : ℕ)
    (hy : weights 1 = 1) (hF : wt weights F ≤ cap) :
    wt weights (implicitRegularity F) ≤ cap - 1 := by
  apply (RCN081.weightedTotalDegree_le_iff weights _ _).mpr
  intro d hd
  have h := (MvPolynomial.le_weightedTotalDegree weights
    (RCN313.support_before_pderiv 1 F d hd)).trans hF
  simp only [map_add, Finsupp.weight_single, one_nsmul, hy] at h
  omega

theorem shortOrdinaryTest_in_cutFlag (φ : K[X] →+* E) (F : Carrier K)
    (u : ℕ) (weights : ℕ → E) (a b : E) (y t : ℕ)
    (hy : 1 ≤ y) (hyt : y ≤ t)
    (hcap : ∀ d ∈ F.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t) :
    PolynomialInFlag (cutFlag 1 u y t) (shortOrdinaryTest φ F u weights a b) := by
  let vW : Fin 4 → ℕ := ![0, 1, 0, 0]
  let tW : Fin 4 → ℕ := ![0, 1, 1, 1]
  let yBound := 1 + 2 * u * (y - 1)
  let tBound := 1 + 2 * u * (t - 1)
  have hVy : wt vW F ≤ y := by
    apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa [vW] using (hcap d hd).1
  have hTt : wt tW F ≤ t := by
    apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa [tW] using (hcap d hd).2
  have hsurface (G : Carrier K) (Ycap Tcap : ℕ) (hY : wt vW G ≤ Ycap) (hT : wt tW G ≤ Tcap) :
      (ordinarySurface φ G).degreeOf 1 ≤ Ycap ∧ (ordinarySurface φ G).totalDegree ≤ Tcap := by
    apply ordinarySurface_degree_caps
    intro d hd
    have hY' := (MvPolynomial.le_weightedTotalDegree vW hd).trans hY
    have hT' := (MvPolynomial.le_weightedTotalDegree tW hd).trans hT
    rw [RCN081.weight_fin4] at hY' hT'
    exact ⟨by simpa [vW] using hY', by simpa [tW] using hT'⟩
  let term (j : ℕ) := MvPolynomial.C (weights j) * ordinarySurface φ (clearedTaylorCoeff F u j)
  have hterm (j : ℕ) (hj : j ≤ u) :
      (term j).degreeOf 1 ≤ yBound ∧ (term j).totalDegree ≤ tBound := by
    have hs := hsurface (clearedTaylorCoeff F u j) yBound tBound
      (clearedTaylorCoeff_wt_le vW F u j y rfl rfl hy hVy hj)
      (clearedTaylorCoeff_wt_le tW F u j t rfl rfl (hy.trans hyt) hTt hj)
    exact ⟨(MvPolynomial.degreeOf_mul_le _ _ _).trans (by simpa [term] using hs.1),
      (MvPolynomial.totalDegree_mul _ _).trans (by simpa [term] using hs.2)⟩
  have hsumY : (∑ j ∈ Finset.range (u + 1), term j).degreeOf 1 ≤ yBound := by
    refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le ?_)
    intro j hj
    exact (hterm j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).1
  have hsumT : (∑ j ∈ Finset.range (u + 1), term j).totalDegree ≤ tBound := by
    exact MvPolynomial.totalDegree_finsetSum_le
      (fun j hj => (hterm j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).2)
  let target : MvPolynomial (Fin 3) E := MvPolynomial.C a + MvPolynomial.X 0 * MvPolynomial.C b
  have htY : target.degreeOf 1 ≤ 0 := by
    refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le (by simp) ?_)
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    simp [MvPolynomial.degreeOf_X_of_ne (show (1 : Fin 3) ≠ 0 by decide)]
  have htT : target.totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) ?_)
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  let separant := ordinarySurface φ (implicitRegularity F)
  have hsep : (separant ^ (2 * u)).degreeOf 1 ≤ 2 * u * (y - 1) ∧
      (separant ^ (2 * u)).totalDegree ≤ 2 * u * (t - 1) := by
    change ((ordinarySurface φ (implicitRegularity F)) ^ (2 * u)).degreeOf 1 ≤ _ ∧
      ((ordinarySurface φ (implicitRegularity F)) ^ (2 * u)).totalDegree ≤ _
    rw [← map_pow]
    exact hsurface _ _ _
      ((wt_pow_le _ _ _).trans (Nat.mul_le_mul_left _ (short_separant_weight_le _ _ _ rfl hVy)))
      ((wt_pow_le _ _ _).trans (Nat.mul_le_mul_left _ (short_separant_weight_le _ _ _ rfl hTt)))
  have hrightY : (separant ^ (2 * u) * target).degreeOf 1 ≤ yBound := by
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ((Nat.add_le_add hsep.1 htY).trans ?_)
    simp [yBound]
  have hrightT : (separant ^ (2 * u) * target).totalDegree ≤ tBound := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ((Nat.add_le_add hsep.2 htT).trans ?_)
    simp [tBound, Nat.add_comm]
  have hY : (shortOrdinaryTest φ F u weights a b).degreeOf 1 ≤ yBound :=
    (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le hsumY hrightY)
  have hT : (shortOrdinaryTest φ F u weights a b).totalDegree ≤ tBound :=
    (MvPolynomial.totalDegree_sub _ _).trans (max_le hsumT hrightT)
  have hBound : yBound ≤ tBound := Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hyt _)) _
  have hFlag : cutFlag 1 u y t = ordinaryFlag yBound tBound := by
    unfold cutFlag
    congr 1 <;> dsimp [yBound, tBound] <;> ring
  rw [hFlag]
  intro d hd
  have hdy := (MvPolynomial.monomial_le_degreeOf (1 : Fin 3) hd).trans hY
  have hdt := (MvPolynomial.le_totalDegree hd).trans hT
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hdt
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hdt
  change d 0 + (d 1 + d 2) ≤ tBound at hdt
  change d 1 ≤ yBound ∧ d 0 + d 1 ≤ tBound - yBound + yBound ∧
    d 0 + d 1 + d 2 ≤ 0 + (tBound - yBound) + yBound
  rw [zero_add, Nat.sub_add_cancel hBound]
  exact ⟨hdy, by omega, by omega⟩

end ProximityPrize.SubmissionLower.Koala6831Ordinary
