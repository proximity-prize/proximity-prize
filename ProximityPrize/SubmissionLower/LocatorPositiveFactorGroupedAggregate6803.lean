import ProximityPrize.SubmissionLower.LocatorGroupedDerivativeAggregate6803
import ProximityPrize.SubmissionLower.LocatorAggregateTerminalProduct6803

/-!
# Grouped derivative incidence over all positive-R factors

Ordinary regular seeds may split a locator into selected and complementary
factors.  Singular derivative chains do not need that split: sum the one-chain
bound over every irreducible positive-`R` factor, then aggregate all geometric
mixed-degree budgets before applying the common coordinate caps.
-/

namespace ProximityPrize.SubmissionLower.LocatorPositiveFactorGroupedAggregate6803

open scoped Classical BigOperators
open RCN001 RCN052 RCN081 RCN082 RCN135 RCN136 RCN137 RCN138 RCN167 RCN222
  RCN238 RCN243 RCN264 RCN286 RCN319
open LocatorDerivativeChain LocatorGroupedDerivativeFactor6803
  LocatorGroupedDerivativeIncidence6803 LocatorGroupedDerivativeAggregate6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000

variable {K Iota : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota

def allPositiveExactChainSeeds
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  (positiveRFactors Q).biUnion fun F ↦ exactChainUnion F selected Gamma

/-- Sum the grouped chain estimate over the original irreducible factors.
There is no multiplier by the number of factors or by chain length. -/
theorem allPositiveExactChainSeeds_grouped_card_le
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (p w a errors : ℕ) [CharP K p]
    (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a)
    (han : a ≤ nodes.card)
    (hdegree : ∀ gamma ∈ allPositiveExactChainSeeds Q selected Gamma,
      (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ allPositiveExactChainSeeds Q selected Gamma,
      a ≤ (nodes.filter fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i).card)
    (hnoPencil : NoLargeSelectedPencil selected
      (allPositiveExactChainSeeds Q selected Gamma) w errors)
    (hproper : ∀ F ∈ positiveRFactors Q, ∀ g : GeometricFactor K F,
      ¬ g.1 ∣ surfaceMap (polynomialEmbedding K) (dR 1 F))
    (hGdegree : ∀ F ∈ positiveRFactors Q,
      ∀ g : GeometricFactor K F, ∀ j : Fin 3, g.1.degreeOf j < p)
    (hcutDegree : ∀ F ∈ positiveRFactors Q,
      ∀ g : GeometricFactor K F, ∀ j k : Fin 3, j ≠ k →
        (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf j *
            g.1.degreeOf k +
          g.1.degreeOf j *
            (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf k < p)
    (agreementCap escapeCap budget : Fin 3 → ℕ)
    (hagreementCap : ∀ F ∈ positiveRFactors Q,
      ∀ g : GeometricFactor K F, ∀ C : InitialComponent F g,
      (componentGenericSeeds F selected Gamma g C ∪
        componentExceptionalSeeds F selected Gamma g C).Nonempty →
      ∀ i ∈ nodes, ∀ j,
        (agreementPolynomial (polynomialEmbedding K)
          (componentCarrier F selected Gamma g C) w
          (x i) (u0 i) (u1 i)).degreeOf j ≤ agreementCap j)
    (hescapeCap : ∀ F ∈ positiveRFactors Q,
      ∀ g : GeometricFactor K F, ∀ C : InitialComponent F g,
      (componentGenericSeeds F selected Gamma g C ∪
        componentExceptionalSeeds F selected Gamma g C).Nonempty →
      ∀ j,
        (surfaceMap (polynomialEmbedding K)
          (MvPolynomial.pderiv (2 : Fin 4)
            (componentCarrier F selected Gamma g C))).degreeOf j ≤
              escapeCap j)
    (hbudget : ∀ j,
      (∑ F ∈ positiveRFactors Q, ∑ g : GeometricFactor K F,
        coordinateMixedDegree (GenericField K) g.1
          (surfaceMap (polynomialEmbedding K) (dR 1 F)) j) ≤ budget j) :
    (allPositiveExactChainSeeds Q selected Gamma).card * (a - w) ≤
      (nodes.card - w) * (∑ j, agreementCap j * budget j) +
      (errors + 1) * (a - w) * budget 2 +
      (a - w) * (∑ j, escapeCap j * budget j) := by
  classical
  let S := allPositiveExactChainSeeds Q selected Gamma
  letI : CharP (GenericField K) p := genericField_charP K p
  have hsingle (F : MvPolynomial (Fin 4) K)
      (hF : F ∈ positiveRFactors Q) :
      (exactChainUnion F selected Gamma).card * (a - w) ≤
        (nodes.card - w) * (∑ j, agreementCap j *
          (∑ g : GeometricFactor K F,
            coordinateMixedDegree (GenericField K) g.1
              (surfaceMap (polynomialEmbedding K) (dR 1 F)) j)) +
        (errors + 1) * (a - w) *
          (∑ g : GeometricFactor K F,
            coordinateMixedDegree (GenericField K) g.1
              (surfaceMap (polynomialEmbedding K) (dR 1 F)) 2) +
        (a - w) * (∑ j, escapeCap j *
          (∑ g : GeometricFactor K F,
            coordinateMixedDegree (GenericField K) g.1
              (surfaceMap (polynomialEmbedding K) (dR 1 F)) j)) := by
    have hsub : exactChainUnion F selected Gamma ⊆ S := by
      intro gamma hgamma
      exact Finset.mem_biUnion.mpr ⟨F, hF, hgamma⟩
    exact exactChainUnion_grouped_card_le F
      (positiveRFactors_spec Q F hF).1.ne_zero selected Gamma
      nodes x u0 u1 hinj p w a errors hw hchar hwa han
      (fun gamma hgamma ↦ hdegree gamma (hsub hgamma))
      (fun gamma hgamma ↦ hagreement gamma (hsub hgamma))
      (noLargeSelectedPencil_mono selected S
        (exactChainUnion F selected Gamma) w errors hsub hnoPencil)
      (hproper F hF) (hGdegree F hF) (hcutDegree F hF)
      agreementCap escapeCap
      (fun j ↦ ∑ g : GeometricFactor K F,
        coordinateMixedDegree (GenericField K) g.1
          (surfaceMap (polynomialEmbedding K) (dR 1 F)) j)
      (fun g C hactive i hi j ↦ hagreementCap F hF g C hactive i hi j)
      (fun g C hactive j ↦ hescapeCap F hF g C hactive j)
      (fun _ ↦ le_rfl)
  have hcover : S.card ≤
      ∑ F ∈ positiveRFactors Q,
        (exactChainUnion F selected Gamma).card := by
    exact Finset.card_biUnion_le
  have hfubiniAgreement :
      (∑ F ∈ positiveRFactors Q, ∑ j : Fin 3, agreementCap j *
        (∑ g : GeometricFactor K F,
          coordinateMixedDegree (GenericField K) g.1
            (surfaceMap (polynomialEmbedding K) (dR 1 F)) j)) =
      ∑ j : Fin 3, agreementCap j *
        (∑ F ∈ positiveRFactors Q, ∑ g : GeometricFactor K F,
          coordinateMixedDegree (GenericField K) g.1
            (surfaceMap (polynomialEmbedding K) (dR 1 F)) j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  have hfubiniEscape :
      (∑ F ∈ positiveRFactors Q, ∑ j : Fin 3, escapeCap j *
        (∑ g : GeometricFactor K F,
          coordinateMixedDegree (GenericField K) g.1
            (surfaceMap (polynomialEmbedding K) (dR 1 F)) j)) =
      ∑ j : Fin 3, escapeCap j *
        (∑ F ∈ positiveRFactors Q, ∑ g : GeometricFactor K F,
          coordinateMixedDegree (GenericField K) g.1
            (surfaceMap (polynomialEmbedding K) (dR 1 F)) j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  calc
    S.card * (a - w) ≤
        (∑ F ∈ positiveRFactors Q,
          (exactChainUnion F selected Gamma).card) * (a - w) :=
      Nat.mul_le_mul_right (a - w) hcover
    _ = ∑ F ∈ positiveRFactors Q,
        (exactChainUnion F selected Gamma).card * (a - w) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ F ∈ positiveRFactors Q,
        ((nodes.card - w) * (∑ j, agreementCap j *
          (∑ g : GeometricFactor K F,
            coordinateMixedDegree (GenericField K) g.1
              (surfaceMap (polynomialEmbedding K) (dR 1 F)) j)) +
        (errors + 1) * (a - w) *
          (∑ g : GeometricFactor K F,
            coordinateMixedDegree (GenericField K) g.1
              (surfaceMap (polynomialEmbedding K) (dR 1 F)) 2) +
        (a - w) * (∑ j, escapeCap j *
          (∑ g : GeometricFactor K F,
            coordinateMixedDegree (GenericField K) g.1
              (surfaceMap (polynomialEmbedding K) (dR 1 F)) j))) :=
      Finset.sum_le_sum fun F hF ↦ hsingle F hF
    _ = (nodes.card - w) * (∑ j, agreementCap j *
          (∑ F ∈ positiveRFactors Q, ∑ g : GeometricFactor K F,
            coordinateMixedDegree (GenericField K) g.1
              (surfaceMap (polynomialEmbedding K) (dR 1 F)) j)) +
        (errors + 1) * (a - w) *
          (∑ F ∈ positiveRFactors Q, ∑ g : GeometricFactor K F,
            coordinateMixedDegree (GenericField K) g.1
              (surfaceMap (polynomialEmbedding K) (dR 1 F)) 2) +
        (a - w) * (∑ j, escapeCap j *
          (∑ F ∈ positiveRFactors Q, ∑ g : GeometricFactor K F,
            coordinateMixedDegree (GenericField K) g.1
              (surfaceMap (polynomialEmbedding K) (dR 1 F)) j)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        hfubiniAgreement, hfubiniEscape]
    _ ≤ (nodes.card - w) * (∑ j, agreementCap j * budget j) +
        (errors + 1) * (a - w) * budget 2 +
        (a - w) * (∑ j, escapeCap j * budget j) := by
      gcongr
      · exact hbudget j
      · exact hbudget 2
      · exact hbudget j

end

end ProximityPrize.SubmissionLower.LocatorPositiveFactorGroupedAggregate6803
