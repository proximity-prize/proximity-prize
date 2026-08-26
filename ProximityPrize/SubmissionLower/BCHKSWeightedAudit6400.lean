import ProximityPrize.SubmissionLower.BCHKSParameters6400

namespace ProximityPrize.SubmissionLower

/-!
Arithmetic audit for the weighted-interpolation 64.00 lane.

These are not yet wired into the submission.  They record the first standard
GS parameter point whose *effective* agreement is only seven coordinates above
the guaranteed agreement and whose universal seed ledger fits the absolute
128-bit field budget.  The extra dimension slack is reserved for a
hypergraph-dependent perturbation of the coordinate multiplicities.
-/

def bchksWeightedMultiplicity6400 : ℕ := 5150
def bchksWeightedEffectiveAgreement6400 : ℕ := 185371
def bchksWeightedXCap6400 : ℕ := 954660650
def bchksWeightedYCap6400 : ℕ := 7284
def bchksWeightedZCap6400 : ℕ := 29830000
def bchksWeightedNumerator6400 : ℕ := 274979000000000000

/-- Safe near-maximal numerator for a residual-comparison continuation. -/
def bchksResidualNumerator6400 : ℕ := 274980700000000000

/-- Dimension of the exact factorization residue (`natDegree ≤ 36049`). -/
def bchksResidualDimension6400 : ℕ := 36050

def bchksWeightedVariableCount6400 : ℕ :=
  103714378617196277534

def bchksWeightedUniformConstraintCount6400 : ℕ :=
  103713901013899673600

def bchksWeightedPerturbationAllowance6400 : ℕ :=
  477603296603933

/-- In a perfectly coordinate-balanced family of `185364`-sets, summing the
row constraints forces this many units of total multiplicity above the
uniform `5150` baseline. -/
def bchksWeightedBalancedExtra6400 : ℕ := 50983

/-- Discrete derivative `Φ(5151)-Φ(5150)` of the per-coordinate constraint
cost. -/
def bchksWeightedNextCost6400 : ℕ := 153641066175

/-- Number of scalar shift-coefficient constraints contributed by one
coordinate of multiplicity `r`.  The `r ≤ DZ` side condition in
`BCHKSWeightedMultiplicityFeasible6400` makes every truncated subtraction in
this formula an honest difference. -/
def bchksWeightedCoordinateCost6400 (r : ℕ) : ℕ :=
  ∑ t ∈ Finset.range r,
    (r - t) * (bchksWeightedZCap6400 - t)

/-- Exact primal certificate needed by the weighted-interpolation lane.

* `μ i ≤ DZ` makes the weighted constraint index valid;
* every agreement row has root weight at least `DX`;
* the total number of interpolation constraints is below the number of
  coefficient variables.

This predicate is intentionally only an interface.  The exact Johnson bound
does not, by itself, prove that it is inhabited for every agreement
hypergraph. -/
def BCHKSWeightedMultiplicityFeasible6400
    {ι ζ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq ζ]
    (S : Finset ζ) (A : ζ → Finset ι) (μ : ι → ℕ) : Prop :=
  (∀ i, μ i ≤ bchksWeightedZCap6400) ∧
  (∀ z ∈ S, bchksWeightedXCap6400 ≤ ∑ i ∈ A z, μ i) ∧
  (∑ i, bchksWeightedCoordinateCost6400 (μ i)) <
    bchksWeightedVariableCount6400

lemma bchksWeightedXCap_eq :
    bchksWeightedXCap6400 =
      bchksWeightedMultiplicity6400 *
        bchksWeightedEffectiveAgreement6400 := by
  norm_num [bchksWeightedXCap6400, bchksWeightedMultiplicity6400,
    bchksWeightedEffectiveAgreement6400]

/-- The target root sum is only `5150 * 7 = 36050` above the root sum
provided by uniform multiplicity on an agreement set of size `185364`. -/
lemma bchksWeightedRootBoost6400 :
    bchksWeightedXCap6400 -
        bchksWeightedMultiplicity6400 * 185364 = 36050 := by
  norm_num [bchksWeightedXCap6400, bchksWeightedMultiplicity6400]

/-- Exact ceiling forced by a balanced `185364`-uniform incidence matrix:
`ceil(262144 * DX / 185364) - 262144 * 5150 = 50983`. -/
lemma bchksWeightedBalancedExtra_eq6400 :
    (262144 * bchksWeightedXCap6400 + 185364 - 1) / 185364 -
        262144 * bchksWeightedMultiplicity6400 =
      bchksWeightedBalancedExtra6400 := by
  norm_num [bchksWeightedXCap6400, bchksWeightedMultiplicity6400,
    bchksWeightedBalancedExtra6400]

/-- Exact first discrete cost above the uniform baseline. -/
lemma bchksWeightedNextCost_eq6400 :
    (bchksWeightedMultiplicity6400 + 1) * bchksWeightedZCap6400 -
        bchksWeightedMultiplicity6400 *
          (bchksWeightedMultiplicity6400 + 1) / 2 =
      bchksWeightedNextCost6400 := by
  norm_num [bchksWeightedMultiplicity6400, bchksWeightedZCap6400,
    bchksWeightedNextCost6400]

/-- Arithmetic obstruction for the balanced-design branch.  Once discrete
convexity converts the forced total excess into at least `50983` first
increments, the interpolation constraint count already exceeds the entire
variable space (by more than sixteen times the available perturbation
allowance). -/
lemma bchksWeightedBalancedCost_obstruction6400 :
    bchksWeightedVariableCount6400 <
      bchksWeightedUniformConstraintCount6400 +
        bchksWeightedBalancedExtra6400 * bchksWeightedNextCost6400 := by
  norm_num [bchksWeightedVariableCount6400,
    bchksWeightedUniformConstraintCount6400,
    bchksWeightedBalancedExtra6400, bchksWeightedNextCost6400]

/-- Exact dimension headroom available for nonuniform coordinate constraints. -/
lemma bchksWeightedDimensionAllowance6400 :
    bchksWeightedUniformConstraintCount6400 +
        bchksWeightedPerturbationAllowance6400 <
      bchksWeightedVariableCount6400 := by
  norm_num [bchksWeightedUniformConstraintCount6400,
    bchksWeightedPerturbationAllowance6400,
    bchksWeightedVariableCount6400]

/-- Closed-form uniform per-coordinate multiplicity cost, multiplied by the
block length.  A generalized interpolant may replace this uniform cost by the
sum of the corresponding per-coordinate costs. -/
lemma bchksWeightedUniformConstraintFormula6400 :
    262144 *
        (bchksWeightedMultiplicity6400 *
            (bchksWeightedMultiplicity6400 + 1) / 2 *
              bchksWeightedZCap6400 -
          bchksWeightedMultiplicity6400 *
            (bchksWeightedMultiplicity6400 - 1) *
            (bchksWeightedMultiplicity6400 + 1) / 6) =
      bchksWeightedUniformConstraintCount6400 := by
  norm_num [bchksWeightedMultiplicity6400, bchksWeightedZCap6400,
    bchksWeightedUniformConstraintCount6400]

/-- The downstream universal-resultant ledger fits at the weighted candidate
caps. -/
lemma bchksWeightedSeedBudget6400 :
    bchksIncidenceCoefficient6400 *
          (bchksWeightedYCap6400 - 1) *
          (bchksWeightedZCap6400 - 1) +
        (bchksErrors6400 + 1) * (bchksWeightedYCap6400 - 1) +
        2 * bchksWeightedZCap6400 * (bchksWeightedYCap6400 - 1) +
        bchksWeightedZCap6400 <
      bchksWeightedNumerator6400 := by
  norm_num [bchksIncidenceCoefficient6400, bchksWeightedYCap6400,
    bchksWeightedZCap6400, bchksErrors6400,
    bchksWeightedNumerator6400]

/-- The weighted candidate numerator plus the exact boundary list term stays
inside the final field-capacity inequality. -/
lemma bchksWeightedFieldBudget6400 :
    2 ^ (128 : ℕ) *
        (bchksWeightedNumerator6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksWeightedNumerator6400, bchksListBound6400]

/-- There is just enough field-selection room, at a safe near-maximal
numerator, for two hypothetical coherent residual coefficient families of
`Z`-degree below `DZ`.  The missing issue is algebraic coherence: the actual
residue is divided by the challenge-dependent locator `G_z^5150`. -/
lemma bchksResidualTwoFamilySeedBudget6400 :
    bchksIncidenceCoefficient6400 *
          (bchksWeightedYCap6400 - 1) *
          (bchksWeightedZCap6400 - 1) +
        (bchksErrors6400 + 1) * (bchksWeightedYCap6400 - 1) +
        2 * bchksWeightedZCap6400 * (bchksWeightedYCap6400 - 1) +
        bchksWeightedZCap6400 +
        2 * bchksResidualDimension6400 * bchksWeightedZCap6400 <
      bchksResidualNumerator6400 := by
  norm_num [bchksIncidenceCoefficient6400, bchksWeightedYCap6400,
    bchksWeightedZCap6400, bchksErrors6400,
    bchksResidualDimension6400, bchksResidualNumerator6400]

lemma bchksResidualFieldBudget6400 :
    2 ^ (128 : ℕ) *
        (bchksResidualNumerator6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksResidualNumerator6400, bchksListBound6400]

end ProximityPrize.SubmissionLower
