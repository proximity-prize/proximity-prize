import ProximityPrize.SubmissionLower.LocatorGroupedDerivativeUniformCaps6803
import ProximityPrize.SubmissionLower.LocatorExactDerivativeChain6803

/-!
# Assembly of grouped derivative chains and their common terminal tail

The non-regular part of the exact factor cover has two populations: all
nonterminal exact derivative strata, and all terminal/R-free strata.  The
first population is charged by the grouped incidence estimate, while the
second is contained in the zero set of one aggregate terminal product.

An additional exceptional population is deliberately left abstract.  Its
cap is an additive input, so fixed and residual locators can use different
exceptional-flag ledgers without changing this assembly.
-/

namespace ProximityPrize.SubmissionLower.LocatorGroupedNonRegularAssembly6803

open scoped Classical BigOperators
open RCN052 RCN081 RCN135 RCN136 RCN137 RCN138 RCN156 RCN167 RCN174 RCN234
  RCN238 RCN286 RCN319
open LocatorDerivativeChain LocatorExactDerivativeChain6803
  LocatorGroupedDerivativeFactor6803
  LocatorPositiveFactorGroupedAggregate6803
  LocatorAggregateTerminalProduct6803
  LocatorGroupedDerivativeUniformCaps6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000

variable {K Iota : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota

/-- The whole non-regular part of the exact factor cover, after replacing all
individual derivative tails and the R-free population by one terminal set. -/
def allGroupedNonRegularSeeds
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  allPositiveExactChainSeeds Q selected Gamma ∪
    aggregateTerminalSeeds Q selected Gamma

/-- The exact cover, with all derivative tails and R-free seeds folded into
the aggregate terminal set. -/
theorem cover_regular_or_allGroupedNonRegularSeeds
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (s : ℕ) (hsmall : s < p)
    (hR : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ s)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hQsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hTsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma T = 0) :
    Gamma ⊆
      (Finset.univ.biUnion fun F : RegularIndex Q ↦
        regularPairSeeds Q T selected Gamma F) ∪
      allGroupedNonRegularSeeds Q selected Gamma := by
  classical
  have hcover := cover_exact Q T hQ p s hsmall hR selected Gamma
    hQsolution hTsolution
  intro gamma hgamma
  have hg := hcover hgamma
  simp only [Finset.mem_union, allGroupedNonRegularSeeds] at hg ⊢
  rcases hg with ((hregular | hexact) | htail) | hrfree
  · exact Or.inl hregular
  · exact Or.inr (Or.inl (by
      simpa only [allPositiveExactChainSeeds, exactChainUnion] using hexact))
  · apply Or.inr
    apply Or.inr
    apply all_tailSeeds_subset_aggregateTerminalSeeds Q selected Gamma
    exact Finset.mem_union_left _ htail
  · apply Or.inr
    apply Or.inr
    apply all_tailSeeds_subset_aggregateTerminalSeeds Q selected Gamma
    exact Finset.mem_union_right _ hrfree

/-- The common grouped-incidence numerator.  Naming it keeps the assembly API
readable and makes the fixed/residual instantiations differ only in their box
parameters. -/
def groupedDerivativeNumerator
    (nodesCard w a errors yCap sCap lCap : ℕ) : ℕ :=
  (nodesCard - w) *
      (∑ j, activeCarrierAgreementCap w yCap sCap lCap j *
        positiveDerivativeMixedBudget yCap sCap lCap j) +
    (errors + 1) * (a - w) *
      positiveDerivativeMixedBudget yCap sCap lCap 2 +
    (a - w) *
      (∑ j, activeEscapeSurfaceCap yCap sCap lCap j *
        positiveDerivativeMixedBudget yCap sCap lCap j)

/-- Pure cardinality assembly.  `exceptionalSeeds` is independent of the
grouped first-escape exceptional branch, which is already included in the
grouped numerator.  It represents any extra exceptional-flag population in a
caller's outer ledger. -/
theorem allGroupedNonRegularSeeds_union_exceptional_scaled_card_le
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma exceptionalSeeds : Finset K)
    (gap groupedCap terminalCap exceptionalCap : ℕ)
    (hgrouped :
      (allPositiveExactChainSeeds Q selected Gamma).card * gap ≤ groupedCap)
    (hterminal :
      (aggregateTerminalSeeds Q selected Gamma).card ≤ terminalCap)
    (hexceptional : exceptionalSeeds.card ≤ exceptionalCap) :
    (allGroupedNonRegularSeeds Q selected Gamma ∪ exceptionalSeeds).card * gap ≤
      groupedCap + (terminalCap + exceptionalCap) * gap := by
  have hcard :
      (allGroupedNonRegularSeeds Q selected Gamma ∪ exceptionalSeeds).card ≤
        (allPositiveExactChainSeeds Q selected Gamma).card +
          (aggregateTerminalSeeds Q selected Gamma).card +
          exceptionalSeeds.card := by
    unfold allGroupedNonRegularSeeds
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  calc
    (allGroupedNonRegularSeeds Q selected Gamma ∪ exceptionalSeeds).card * gap
        ≤ ((allPositiveExactChainSeeds Q selected Gamma).card +
          (aggregateTerminalSeeds Q selected Gamma).card +
          exceptionalSeeds.card) * gap := Nat.mul_le_mul_right gap hcard
    _ = (allPositiveExactChainSeeds Q selected Gamma).card * gap +
          ((aggregateTerminalSeeds Q selected Gamma).card +
            exceptionalSeeds.card) * gap := by
      simp only [Nat.add_mul, Nat.add_assoc]
    _ ≤ groupedCap + (terminalCap + exceptionalCap) * gap := by
      exact Nat.add_le_add hgrouped
        (Nat.mul_le_mul_right gap (Nat.add_le_add hterminal hexceptional))

/-- The aggregate terminal product is the single certificate needed by the
tail counter: it is nonzero, R-free, belongs to the descended common box, and
covers every individual tail and every R-free seed. -/
theorem aggregateTerminal_certificate
    (w contactCap totalCap : ℕ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (hsmall : Q.degreeOf (2 : Fin 4) < p)
    (hpositive : (positiveRFactors Q).Nonempty)
    (hcontact : wt (contactWeights w) Q ≤ contactCap)
    (htotal : wt residualTotalWeights Q ≤ totalCap)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    aggregateTerminalProduct Q ≠ 0 ∧
      (aggregateTerminalProduct Q).degreeOf (2 : Fin 4) = 0 ∧
      aggregateTerminalProduct Q ∈ globalCoefficientBox K
        (contactCap - (w - 1) + 1) w (totalCap - 1) 1 ∧
      ((positiveRFactors Q).biUnion fun F ↦ tailSeeds F selected Gamma) ∪
          rfreeSeeds Q selected Gamma ⊆
        aggregateTerminalSeeds Q selected Gamma := by
  exact ⟨aggregateTerminalProduct_ne_zero Q hQ p hsmall,
    aggregateTerminalProduct_R_degree Q,
    aggregateTerminalProduct_mem_tail_box w contactCap totalCap Q hQ p hsmall
      hpositive hcontact htotal,
    all_tailSeeds_subset_aggregateTerminalSeeds Q selected Gamma⟩

/-- Main reusable assembly.  The grouped term is discharged from the
cumulative locator caps.  The caller supplies only a counter for a nonzero,
R-free polynomial in the one descended terminal box, plus its independent
exceptional-flag cap. -/
theorem allGroupedNonRegularSeeds_of_cumulativeCaps
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (selected : K → Polynomial K) (Gamma exceptionalSeeds : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (p w a errors yCap sCap lCap contactCap totalCap : ℕ) [CharP K p]
    (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a)
    (han : a ≤ nodes.card) (hsCap : 2 ≤ sCap)
    (hY : wt residualYSWeights Q ≤ yCap)
    (hS : wt residualSWeights Q ≤ sCap)
    (hL : wt residualTotalWeights Q ≤ lCap)
    (hySmall : yCap < p) (hsSmall : sCap < p) (hlSmall : lCap < p)
    (hmixed : ∀ j k : Fin 3, j ≠ k →
      firstDerivativeSurfaceCap yCap sCap lCap j *
          originalSurfaceCap yCap sCap lCap k +
        originalSurfaceCap yCap sCap lCap j *
          firstDerivativeSurfaceCap yCap sCap lCap k < p)
    (hdegree : ∀ gamma ∈ allPositiveExactChainSeeds Q selected Gamma,
      (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ allPositiveExactChainSeeds Q selected Gamma,
      a ≤ (nodes.filter fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i).card)
    (hnoPencil : NoLargeSelectedPencil selected
      (allPositiveExactChainSeeds Q selected Gamma) w errors)
    (hRsmall : Q.degreeOf (2 : Fin 4) < p)
    (hpositive : (positiveRFactors Q).Nonempty)
    (hcontact : wt (contactWeights w) Q ≤ contactCap)
    (htotal : wt residualTotalWeights Q ≤ totalCap)
    (terminalCap exceptionalCap : ℕ)
    (htailCounter : ∀ J : MvPolynomial (Fin 4) K, J ≠ 0 →
      J.degreeOf (2 : Fin 4) = 0 →
      J ∈ globalCoefficientBox K
        (contactCap - (w - 1) + 1) w (totalCap - 1) 1 →
      (Gamma.filter fun gamma ↦
        specialization K (selected gamma) gamma J = 0).card ≤ terminalCap)
    (hexceptional : exceptionalSeeds.card ≤ exceptionalCap) :
    (allGroupedNonRegularSeeds Q selected Gamma ∪ exceptionalSeeds).card *
        (a - w) ≤
      groupedDerivativeNumerator nodes.card w a errors yCap sCap lCap +
        (terminalCap + exceptionalCap) * (a - w) := by
  apply allGroupedNonRegularSeeds_union_exceptional_scaled_card_le
    Q selected Gamma exceptionalSeeds (a - w)
    (groupedDerivativeNumerator nodes.card w a errors yCap sCap lCap)
    terminalCap exceptionalCap
  · simpa only [groupedDerivativeNumerator] using
      (allPositiveExactChainSeeds_grouped_of_cumulativeCaps Q hQ selected Gamma
        nodes x u0 u1 hinj p w a errors yCap sCap lCap hw hchar hwa han hsCap
        hY hS hL hySmall hsSmall hlSmall hmixed hdegree hagreement hnoPencil)
  · unfold aggregateTerminalSeeds
    apply htailCounter (aggregateTerminalProduct Q)
    · exact aggregateTerminalProduct_ne_zero Q hQ p hRsmall
    · exact aggregateTerminalProduct_R_degree Q
    · exact aggregateTerminalProduct_mem_tail_box w contactCap totalCap Q hQ
        p hRsmall hpositive hcontact htotal
  · exact hexceptional

end

end ProximityPrize.SubmissionLower.LocatorGroupedNonRegularAssembly6803
