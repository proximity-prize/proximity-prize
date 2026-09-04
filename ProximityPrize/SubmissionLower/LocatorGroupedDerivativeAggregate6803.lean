import ProximityPrize.SubmissionLower.LocatorGroupedDerivativeIncidence6803

/-!
# Aggregate grouped derivative incidence over geometric factors

The component argument charges the whole exact derivative chain once on each
geometric factor of the original surface.  This file performs the remaining
finite-geometry aggregation: geometric factors cover all exact-chain seeds,
and their mixed degrees add up before the common agreement and exceptional
caps are applied.
-/

namespace ProximityPrize.SubmissionLower.LocatorGroupedDerivativeAggregate6803

open scoped Classical BigOperators
open RCN001 RCN052 RCN135 RCN136 RCN137 RCN167 RCN222 RCN238 RCN243 RCN264
  RCN286 RCN319
open LocatorDerivativeChain LocatorGroupedDerivativeFactor6803
  LocatorGroupedDerivativeIncidence6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {K Iota : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Sum the one-charge component estimate over every geometric factor of
`surfaceMap F`.  All hypotheses below are local gates or uniform degree caps;
there is no factor-count or derivative-chain-length multiplier in the result. -/
theorem exactChainUnion_grouped_card_le
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (p w a errors : ℕ) [CharP K p]
    (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a)
    (han : a ≤ nodes.card)
    (hdegree : ∀ gamma ∈ exactChainUnion F selected Gamma,
      (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ exactChainUnion F selected Gamma,
      a ≤ (nodes.filter fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i).card)
    (hnoPencil : NoLargeSelectedPencil selected
      (exactChainUnion F selected Gamma) w errors)
    (hproper : ∀ g : GeometricFactor K F,
      ¬ g.1 ∣ surfaceMap (polynomialEmbedding K) (dR 1 F))
    (hGdegree : ∀ g : GeometricFactor K F, ∀ j : Fin 3,
      g.1.degreeOf j < p)
    (hcutDegree : ∀ g : GeometricFactor K F, ∀ j k : Fin 3, j ≠ k →
      (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf j *
          g.1.degreeOf k +
        g.1.degreeOf j *
          (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf k < p)
    (agreementCap escapeCap budget : Fin 3 → ℕ)
    (hagreementCap : ∀ g : GeometricFactor K F,
      ∀ C : InitialComponent F g,
      (componentGenericSeeds F selected Gamma g C ∪
        componentExceptionalSeeds F selected Gamma g C).Nonempty →
      ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial (polynomialEmbedding K)
        (componentCarrier F selected Gamma g C) w
        (x i) (u0 i) (u1 i)).degreeOf j ≤ agreementCap j)
    (hescapeCap : ∀ g : GeometricFactor K F,
      ∀ C : InitialComponent F g,
      (componentGenericSeeds F selected Gamma g C ∪
        componentExceptionalSeeds F selected Gamma g C).Nonempty →
      ∀ j,
      (surfaceMap (polynomialEmbedding K)
        (MvPolynomial.pderiv (2 : Fin 4)
          (componentCarrier F selected Gamma g C))).degreeOf j ≤
            escapeCap j)
    (hbudget : ∀ j,
      (∑ g : GeometricFactor K F,
        coordinateMixedDegree (GenericField K) g.1
          (surfaceMap (polynomialEmbedding K) (dR 1 F)) j) ≤ budget j) :
    (exactChainUnion F selected Gamma).card * (a - w) ≤
      (nodes.card - w) * (∑ j, agreementCap j * budget j) +
      (errors + 1) * (a - w) * budget 2 +
      (a - w) * (∑ j, escapeCap j * budget j) := by
  classical
  let S := exactChainUnion F selected Gamma
  let T1 := surfaceMap (polynomialEmbedding K) (dR 1 F)
  letI : CharP (GenericField K) p := genericField_charP K p
  have hsolutions : ∀ gamma ∈ S,
      specialization K (selected gamma) gamma F = 0 := by
    intro gamma hgamma
    simpa only [dR_zero] using
      exactChainUnion_history F selected Gamma hgamma 0 (by omega)
  have hcover := card_le_sum_geometricSeeds K F hF selected S hsolutions
  have hsingle (g : GeometricFactor K F) :
      (geometricExactSeeds F selected Gamma g).card * (a - w) ≤
        (nodes.card - w) * (∑ j, agreementCap j *
          coordinateMixedDegree (GenericField K) g.1 T1 j) +
        (errors + 1) * (a - w) *
          coordinateMixedDegree (GenericField K) g.1 T1 2 +
        (a - w) * (∑ j, escapeCap j *
          coordinateMixedDegree (GenericField K) g.1 T1 j) := by
    have hsub : geometricExactSeeds F selected Gamma g ⊆ S :=
      geometricExactSeeds_subset_union F selected Gamma g
    exact geometricExactSeeds_grouped_card_le F selected Gamma g
      (hproper g) nodes x u0 u1 hinj p w a errors hw hchar hwa han
      (hGdegree g) (hcutDegree g)
      (fun gamma hgamma ↦ hdegree gamma (hsub hgamma))
      (fun gamma hgamma ↦ hagreement gamma (hsub hgamma))
      (noLargeSelectedPencil_mono selected S
        (geometricExactSeeds F selected Gamma g) w errors hsub hnoPencil)
      agreementCap escapeCap (hagreementCap g) (hescapeCap g)
  have hfubiniAgreement :
      (∑ g : GeometricFactor K F, ∑ j : Fin 3,
        agreementCap j * coordinateMixedDegree (GenericField K) g.1 T1 j) =
      ∑ j : Fin 3, agreementCap j *
        (∑ g : GeometricFactor K F,
          coordinateMixedDegree (GenericField K) g.1 T1 j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  have hfubiniEscape :
      (∑ g : GeometricFactor K F, ∑ j : Fin 3,
        escapeCap j * coordinateMixedDegree (GenericField K) g.1 T1 j) =
      ∑ j : Fin 3, escapeCap j *
        (∑ g : GeometricFactor K F,
          coordinateMixedDegree (GenericField K) g.1 T1 j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  calc
    S.card * (a - w) ≤
        (∑ g : GeometricFactor K F,
          (geometricExactSeeds F selected Gamma g).card) * (a - w) :=
      Nat.mul_le_mul_right (a - w) hcover
    _ = ∑ g : GeometricFactor K F,
        (geometricExactSeeds F selected Gamma g).card * (a - w) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K F,
        ((nodes.card - w) * (∑ j, agreementCap j *
            coordinateMixedDegree (GenericField K) g.1 T1 j) +
          (errors + 1) * (a - w) *
            coordinateMixedDegree (GenericField K) g.1 T1 2 +
          (a - w) * (∑ j, escapeCap j *
            coordinateMixedDegree (GenericField K) g.1 T1 j)) :=
      Finset.sum_le_sum fun g _ ↦ hsingle g
    _ = (nodes.card - w) * (∑ j, agreementCap j *
          (∑ g : GeometricFactor K F,
            coordinateMixedDegree (GenericField K) g.1 T1 j)) +
        (errors + 1) * (a - w) *
          (∑ g : GeometricFactor K F,
            coordinateMixedDegree (GenericField K) g.1 T1 2) +
        (a - w) * (∑ j, escapeCap j *
          (∑ g : GeometricFactor K F,
            coordinateMixedDegree (GenericField K) g.1 T1 j)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        hfubiniAgreement, hfubiniEscape]
    _ ≤ (nodes.card - w) * (∑ j, agreementCap j * budget j) +
        (errors + 1) * (a - w) * budget 2 +
        (a - w) * (∑ j, escapeCap j * budget j) := by
      gcongr
      · simpa only [T1] using hbudget j
      · simpa only [T1] using hbudget 2
      · simpa only [T1] using hbudget j

end

end ProximityPrize.SubmissionLower.LocatorGroupedDerivativeAggregate6803
