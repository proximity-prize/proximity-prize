import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactExceptionalSeedCount

/-!
# Actual implicit factor pairs and their summed coordinate budgets

Model label: gpt-5.

The base factors are the actual swapped-normalization factor family,
filtered only by nonzero Y derivative. Each base factor is paired with the
actual positive-R factors of its contact lift. The finite sigma family is
constructed here, not supplied as a component-list hypothesis.

Its three elementary elimination costs sum to at most J_Z, 2*J_Y*J_Z,
and J_Y respectively. These are algebraic degree ledgers, not yet a theorem
about geometric component degrees or numbers of selected seeds.
-/

namespace ProximityPrize.SubmissionLower.ContactImplicitPairBudgets

open ContactExceptionalSeedAuxiliary ContactImplicitContactLift
open ContactFactorCaps ContactRegularFactorGate ContactInterpolation

noncomputable section

variable {K : Type*} [Field K]

def implicitBaseFactors (J : MvPolynomial (Fin 4) K) :
    Finset (MvPolynomial (Fin 4) K) := by
  classical
  exact (originalImplicitFactors J).filter
    (fun A => MvPolynomial.pderiv (1 : Fin 4) A ≠ 0)

theorem implicitBaseFactors_subset (J : MvPolynomial (Fin 4) K) :
    implicitBaseFactors J ⊆ originalImplicitFactors J := by
  classical
  exact Finset.filter_subset _ _

theorem implicitBaseFactors_spec (J A : MvPolynomial (Fin 4) K)
    (hJ : J ≠ 0) (hR : J.degreeOf 2 = 0) (hA : A ∈ implicitBaseFactors J) :
    Irreducible A ∧ A ∣ J ∧ A.degreeOf 2 = 0 ∧
      MvPolynomial.pderiv (1 : Fin 4) A ≠ 0 := by
  classical
  obtain ⟨hm, hy⟩ := Finset.mem_filter.mp hA
  have hs := originalImplicitFactors_spec J A hm
  have hr := ContactFactorCaps.degreeOf_le_of_dvd (2 : Fin 4) A J hs.2 hJ
  exact ⟨hs.1, hs.2, by omega, hy⟩

theorem implicitBaseFactors_degree_budgets
    (J : MvPolynomial (Fin 4) K) (hJ : J ≠ 0) :
    (∑ A ∈ implicitBaseFactors J, A.degreeOf (1 : Fin 4)) ≤ J.degreeOf 1 ∧
      (∑ A ∈ implicitBaseFactors J, A.degreeOf (3 : Fin 4)) ≤ J.degreeOf 3 := by
  classical
  have hb := originalImplicitFactors_degree_budgets J hJ
  exact ⟨(Finset.sum_le_sum_of_subset (implicitBaseFactors_subset J)).trans hb.1,
    (Finset.sum_le_sum_of_subset (implicitBaseFactors_subset J)).trans hb.2⟩

def implicitPairSet (J : MvPolynomial (Fin 4) K) :
    Finset ((A : MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K) :=
  (implicitBaseFactors J).sigma (fun A => positiveRFactors (implicitLift A))

theorem mem_implicitPairSet (J A G : MvPolynomial (Fin 4) K) :
    (⟨A, G⟩ : (A : MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K) ∈
        implicitPairSet J ↔
      A ∈ implicitBaseFactors J ∧ G ∈ positiveRFactors (implicitLift A) := by
  classical
  exact Finset.mem_sigma

theorem implicitPair_spec (J A G : MvPolynomial (Fin 4) K)
    (hJ : J ≠ 0) (hR : J.degreeOf 2 = 0)
    (hpair : (⟨A, G⟩ : (A : MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K) ∈
      implicitPairSet J) :
    Irreducible A ∧ A ∣ J ∧ A.degreeOf 2 = 0 ∧
      MvPolynomial.pderiv (1 : Fin 4) A ≠ 0 ∧
      Irreducible G ∧ G ∣ implicitLift A ∧ G.degreeOf 2 = 1 ∧ ¬ G ∣ A := by
  obtain ⟨hA, hG⟩ := (mem_implicitPairSet J A G).mp hpair
  obtain ⟨hiA, hdA, hrA, hyA⟩ := implicitBaseFactors_spec J A hJ hR hA
  obtain ⟨hiG, hdG, hrG⟩ := positiveRFactors_spec (implicitLift A) G hG
  have hF := implicitLift_nonzero A hrA hyA
  have hgcap := (ContactFactorCaps.degreeOf_le_of_dvd (2 : Fin 4)
    G (implicitLift A) hdG hF).trans (implicitLift_R_degree_le A hrA)
  refine ⟨hiA, hdA, hrA, hyA, hiG, hdG, by omega, ?_⟩
  intro hd
  have hh := ContactFactorCaps.degreeOf_le_of_dvd (2 : Fin 4) G A hd hiA.ne_zero
  omega

theorem sum_products_le_product_sums {ι : Type*} (I : Finset ι) (f g : ι → ℕ) :
    (∑ i ∈ I, f i * g i) ≤ (∑ i ∈ I, f i) * (∑ i ∈ I, g i) := by
  calc
    _ ≤ ∑ i ∈ I, f i * (∑ j ∈ I, g j) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left (f i) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)
    _ = _ := (Finset.sum_mul I f (∑ j ∈ I, g j)).symm

theorem implicitBaseFactors_product_degree_budget
    (J : MvPolynomial (Fin 4) K) (hJ : J ≠ 0) :
    (∑ A ∈ implicitBaseFactors J, A.degreeOf (1 : Fin 4) * A.degreeOf (3 : Fin 4)) ≤
      J.degreeOf 1 * J.degreeOf 3 := by
  have hb := implicitBaseFactors_degree_budgets J hJ
  exact (sum_products_le_product_sums (implicitBaseFactors J)
    (fun A => A.degreeOf 1) (fun A => A.degreeOf 3)).trans (Nat.mul_le_mul hb.1 hb.2)

/-- Coordinate order is the original Y,R,Z. These are the actual elementary
pair costs used by the subsequent plane/resultant projection adapters. -/
def pairYCost (q : (A : MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K) : ℕ :=
  q.2.degreeOf 2 * q.1.degreeOf 3

def pairRCost (q : (A : MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K) : ℕ :=
  q.2.degreeOf 1 * q.1.degreeOf 3 + q.2.degreeOf 3 * q.1.degreeOf 1

def pairZCost (q : (A : MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K) : ℕ :=
  q.2.degreeOf 2 * q.1.degreeOf 1

theorem implicitPair_degree_budgets
    (J : MvPolynomial (Fin 4) K) (hJ : J ≠ 0) (hR : J.degreeOf 2 = 0) :
    (∑ q ∈ implicitPairSet J, pairYCost q) ≤ J.degreeOf 3 ∧
      (∑ q ∈ implicitPairSet J, pairRCost q) ≤ 2 * J.degreeOf 1 * J.degreeOf 3 ∧
      (∑ q ∈ implicitPairSet J, pairZCost q) ≤ J.degreeOf 1 := by
  classical
  have hlocal (A : MvPolynomial (Fin 4) K) (hA : A ∈ implicitBaseFactors J) :
      (∑ G ∈ positiveRFactors (implicitLift A), G.degreeOf (2 : Fin 4)) ≤ 1 ∧
        (∑ G ∈ positiveRFactors (implicitLift A), G.degreeOf (1 : Fin 4)) ≤ A.degreeOf 1 ∧
        (∑ G ∈ positiveRFactors (implicitLift A), G.degreeOf (3 : Fin 4)) ≤ A.degreeOf 3 := by
    obtain ⟨_, _, hr, hy⟩ := implicitBaseFactors_spec J A hJ hR hA
    exact lift_positive_factor_budgets A hr hy
  have hb := implicitBaseFactors_degree_budgets J hJ
  have hy : (∑ q ∈ implicitPairSet J, pairYCost q) ≤
      ∑ A ∈ implicitBaseFactors J, A.degreeOf (3 : Fin 4) := by
    rw [implicitPairSet, Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro A hA
    change (∑ G ∈ positiveRFactors (implicitLift A), G.degreeOf 2 * A.degreeOf 3) ≤ _
    rw [← Finset.sum_mul]
    simpa only [one_mul] using Nat.mul_le_mul_right (A.degreeOf 3) (hlocal A hA).1
  have hz : (∑ q ∈ implicitPairSet J, pairZCost q) ≤
      ∑ A ∈ implicitBaseFactors J, A.degreeOf (1 : Fin 4) := by
    rw [implicitPairSet, Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro A hA
    change (∑ G ∈ positiveRFactors (implicitLift A), G.degreeOf 2 * A.degreeOf 1) ≤ _
    rw [← Finset.sum_mul]
    simpa only [one_mul] using Nat.mul_le_mul_right (A.degreeOf 1) (hlocal A hA).1
  have hr : (∑ q ∈ implicitPairSet J, pairRCost q) ≤
      ∑ A ∈ implicitBaseFactors J, 2 * (A.degreeOf (1 : Fin 4) * A.degreeOf (3 : Fin 4)) := by
    rw [implicitPairSet, Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro A hA
    change (∑ G ∈ positiveRFactors (implicitLift A),
      (G.degreeOf 1 * A.degreeOf 3 + G.degreeOf 3 * A.degreeOf 1)) ≤ _
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    calc
      _ ≤ A.degreeOf 1 * A.degreeOf 3 + A.degreeOf 3 * A.degreeOf 1 :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (hlocal A hA).2.1)
          (Nat.mul_le_mul_right _ (hlocal A hA).2.2)
      _ = _ := by ring
  refine ⟨hy.trans hb.2, ?_, hz.trans hb.1⟩
  calc
    _ ≤ ∑ A ∈ implicitBaseFactors J, 2 * (A.degreeOf (1 : Fin 4) * A.degreeOf (3 : Fin 4)) := hr
    _ = 2 * (∑ A ∈ implicitBaseFactors J, A.degreeOf (1 : Fin 4) * A.degreeOf (3 : Fin 4)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * (J.degreeOf 1 * J.degreeOf 3) :=
      Nat.mul_le_mul_left 2 (implicitBaseFactors_product_degree_budget J hJ)
    _ = _ := by ring

theorem implicitPair_input_budgets
    (J : MvPolynomial (Fin 4) K) (hJ : J ≠ 0)
    (D w j : ℕ) (hw : 0 < w) (hbox : J ∈ globalCoefficientBox K D w j 0) :
    (∑ q ∈ implicitPairSet J, pairYCost q) ≤ j ∧
      (∑ q ∈ implicitPairSet J, pairRCost q) ≤ 2 * ((D - 1) / w) * j ∧
      (∑ q ∈ implicitPairSet J, pairZCost q) ≤ (D - 1) / w := by
  have hR : J.degreeOf 2 = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (hbox hd).2.1
  have hcaps := degree_bounds_of_mem_box J D w j 0 hw hbox
  have hy : J.degreeOf 1 ≤ (D - 1) / w := hcaps.1
  have hz : J.degreeOf 3 ≤ j := hcaps.2.2
  have hb := implicitPair_degree_budgets J hJ hR
  exact ⟨hb.1.trans hz,
    hb.2.1.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hy) hz), hb.2.2.trans hy⟩

#print axioms implicitBaseFactors_spec
#print axioms implicitBaseFactors_degree_budgets
#print axioms implicitPair_spec
#print axioms sum_products_le_product_sums
#print axioms implicitBaseFactors_product_degree_budget
#print axioms implicitPair_degree_budgets
#print axioms implicitPair_input_budgets

end
end ProximityPrize.SubmissionLower.ContactImplicitPairBudgets
