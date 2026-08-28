import ProximityPrize.SubmissionLower.BCHKSLocatorDeterminantIncidence6400

/-!
# Coarse polynomial-kernel-basis budgets at score 64

For the `76781`-square diagonal locator matrix, every entry has challenge
degree at most the base characteristic `p = 2130706433`.  A standard
minimal-index estimate therefore gives the deliberately coarse total basis
degree budget `76781 * p`.  This module does not assume that algebraic
estimate; it verifies that, if supplied, its coarse value already fits both
remaining counting regimes.

For nullity `9` or `10`, the weighted determinant extraction costs at most
`9` times the total basis budget and still forces the fixed `49622`-coordinate
container.  For nullity at least `11`, retaining at most `1070` basis vectors
makes the obstruction's `X`-degree strictly smaller than every retained error
support, while its challenge degree stays below the number of retained
slopes.  Thus the later algebra need not prove the much sharper `2D` estimate.
-/

namespace ProximityPrize.SubmissionLower

set_option autoImplicit false

open Polynomial

/-- Coarse total degree allowed for a polynomial kernel basis of the
`76781`-square degree-`p` locator matrix. -/
abbrev score6400KernelBasisTotalDegree : ℕ := 76781 * 2130706433

theorem score6400_kernelBasisTotalDegree_eq :
    score6400KernelBasisTotalDegree = 163597770632173 := by
  norm_num [score6400KernelBasisTotalDegree]

/-- The worst small-large-nullity transition (`L = 10`) uses nine weighted
pair determinants. -/
theorem score6400_nine_kernelBasis_budgets_eq :
    9 * score6400KernelBasisTotalDegree = 1472379935689557 := by
  norm_num [score6400KernelBasisTotalDegree]

/-- A uniform Cramer cap for every rank-two branch: at most nine selected
high rows give ten generator factors. -/
theorem score6400_ten_kernelBasis_budgets_eq :
    10 * score6400KernelBasisTotalDegree = 1635977706321730 := by
  norm_num [score6400KernelBasisTotalDegree]

/-- Even the coarse nine-budget obstruction has ample incidence room after
reserving every slope covered by the accepted score-63.99 theorem. -/
theorem score6400_nine_kernelBasis_budgets_incidence
    (tcard : ℕ) (ht : 174972148031419760 < tcard) :
    262144 * (9 * score6400KernelBasisTotalDegree) <
      (76771 - 49621) * tcard := by
  norm_num [score6400KernelBasisTotalDegree] at ht ⊢
  nlinarith

theorem score6400_ten_kernelBasis_budgets_incidence
    (tcard : ℕ) (ht : 174972148031419760 < tcard) :
    262144 * (10 * score6400KernelBasisTotalDegree) <
      (76771 - 49621) * tcard := by
  norm_num [score6400KernelBasisTotalDegree] at ht ⊢
  nlinarith

/-- Eleven retained basis vectors suffice in every nullity-at-least-eleven
rank-two branch.  The Cramer cap has more than a hundredfold root margin. -/
theorem score6400_ten_kernelBasis_budgets_lt_slopes :
    10 * score6400KernelBasisTotalDegree < 174972148031419761 := by
  norm_num [score6400KernelBasisTotalDegree]

theorem score6400_ten_kernelBasis_budget_margin :
    174972148031419761 -
      10 * score6400KernelBasisTotalDegree = 173336170325098031 := by
  norm_num [score6400KernelBasisTotalDegree]

/-- At most `1070` basis vectors may be retained without spending the
available high-error slope count on challenge roots. -/
theorem score6400_1069_kernelBasis_budgets_lt_slopes :
    1069 * score6400KernelBasisTotalDegree < 174972148031419761 := by
  norm_num [score6400KernelBasisTotalDegree]

theorem score6400_1069_kernelBasis_budget_margin :
    174972148031419761 -
      1069 * score6400KernelBasisTotalDegree = 86131225626824 := by
  norm_num [score6400KernelBasisTotalDegree]

/-- Any retained basis size from `11` through `1070` has challenge budget
strictly below the minimum retained slope count. -/
theorem score6400_kernelBasis_parameter_budget_lt_slopes
    (s : ℕ) (hs : s ≤ 1070) :
    (s - 1) * score6400KernelBasisTotalDegree < 174972148031419761 := by
  have hweight : s - 1 ≤ 1069 := by omega
  calc
    (s - 1) * score6400KernelBasisTotalDegree ≤
        1069 * score6400KernelBasisTotalDegree :=
      Nat.mul_le_mul_right score6400KernelBasisTotalDegree hweight
    _ < 174972148031419761 :=
      score6400_1069_kernelBasis_budgets_lt_slopes

/-- Starting at nullity eleven, the dimension-rebated obstruction has fewer
possible `X`-roots than every retained actual error support. -/
theorem score6400_kernelBasis_xDegree_lt_errorSupport
    (s : ℕ) (hs : 11 ≤ s) :
    76781 - s < 76771 := by
  omega

theorem score6400_kernelBasis_1070_xDegree_eq :
    76781 - 1070 = 75711 := by
  norm_num

theorem score6400_kernelBasis_eleven_xDegree_eq :
    76781 - 11 = 76770 := by
  norm_num

/-- Ready-to-use fixed-container incidence with the coarse nine-budget cap. -/
theorem score6400_pairDet_gives_fixed_container_of_kernelBasisBudget
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (T : Finset F) (E : F → Finset I) (G : I → F[X])
    (hn : Fintype.card I = 262144)
    (hT : 174972148031419760 < T.card)
    (hEcard : ∀ z ∈ T, 76771 ≤ (E z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ E z, (G i).eval z = 0)
    (hdegree : ∀ i,
      (G i).natDegree ≤ 9 * score6400KernelBasisTotalDegree) :
    49622 ≤ (Finset.univ.filter fun i : I => G i = 0).card := by
  exact score6400_pairDet_gives_fixed_container_of_cap
    T E G (9 * score6400KernelBasisTotalDegree) hn hEcard hroot hdegree
      (score6400_nine_kernelBasis_budgets_incidence T.card hT)

/-- Uniform container incidence for the ten-factor Cramer cap. -/
theorem score6400_pairDet_gives_fixed_container_of_tenKernelBasisBudgets
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (T : Finset F) (E : F → Finset I) (G : I → F[X])
    (hn : Fintype.card I = 262144)
    (hT : 174972148031419760 < T.card)
    (hEcard : ∀ z ∈ T, 76771 ≤ (E z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ E z, (G i).eval z = 0)
    (hdegree : ∀ i,
      (G i).natDegree ≤ 10 * score6400KernelBasisTotalDegree) :
    49622 ≤ (Finset.univ.filter fun i : I => G i = 0).card := by
  exact score6400_pairDet_gives_fixed_container_of_cap
    T E G (10 * score6400KernelBasisTotalDegree) hn hEcard hroot hdegree
      (score6400_ten_kernelBasis_budgets_incidence T.card hT)

end ProximityPrize.SubmissionLower
