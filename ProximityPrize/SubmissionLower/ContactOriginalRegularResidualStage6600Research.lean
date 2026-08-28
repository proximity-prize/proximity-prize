import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount
import ProximityPrize.SubmissionLower.ContactRegularFactorFlag6600Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualIterationResearch
import ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch
import ProximityPrize.SubmissionLower.ContactWeightedRegularFactor6600Research

/-!
# Initial residual stages for actual score-66 regular factors

An original positive-`R` factor is covered by its actual geometric surface
factors over the constructed algebraic closure of `K(X)`.  This module turns
each such geometric factor into the exact initial `ResidualStage` consumed by
the nested actual-identity theorem, and aggregates its factorwise ledger back
to the original rectangular flag.
-/

namespace ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6600Research

open scoped Classical BigOperators
open ContactParameters6600Research
open ContactGenericInitialPoint ContactGenericSurface ContactGeometricFirstTail
open ContactGeometricFactorCover ContactRegularFactorGate ContactFactorCaps
open ContactPrimeSeedIncidence ContactPolynomialSolutions ContactInterpolation
open ContactTranslation ContactProperCutSeedCount
open ContactOriginalRegularSeedCount
open ContactRegularFactorFlag6600Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactFlagBezout6543Research
open ContactNearPencil6600FactorLedgerResearch
open ContactWeightedRegularFactor6600Research

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

variable (K : Type) [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

/-- Exact Newton-support flag of one geometric factor. -/
def geometricFlag {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : FlagDegree :=
  weightedFlag g.1

theorem polynomialIn_geometricFlag {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : PolynomialInFlag (geometricFlag K g) g.1 := by
  exact polynomialIn_weightedFlag g.1

/-- The interpolation box supplies exactly the three global support values
preserved by residualization. -/
theorem residual_surface_weights_of_box
    (F : MvPolynomial (Fin 4) K)
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap) :
    wt residualSWeights F ≤ 8 ∧
      wt residualYSWeights F ≤ 43 ∧
      wt residualTotalWeights F ≤ 522 := by
  constructor
  · apply (weightedTotalDegree_le_iff residualSWeights F 8).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ seedTotalCap ∧ d 2 ≤ slopeCap ∧
        d 0 + w * d 1 + (w - 1) * d 2 < weightedCap := hbox hd
    rw [weight_fin4]
    rw [show residualSWeights 0 = 0 by rfl,
      show residualSWeights 1 = 0 by rfl,
      show residualSWeights 2 = 1 by rfl,
      show residualSWeights 3 = 0 by rfl]
    simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
    simpa only [slopeCap] using hb.2.1
  · constructor
    · apply (weightedTotalDegree_le_iff residualYSWeights F 43).mpr
      intro d hd
      have hb : d 1 + d 3 ≤ seedTotalCap ∧ d 2 ≤ slopeCap ∧
          d 0 + w * d 1 + (w - 1) * d 2 < weightedCap := hbox hd
      rw [weight_fin4]
      rw [show residualYSWeights 0 = 0 by rfl,
        show residualYSWeights 1 = 1 by rfl,
        show residualYSWeights 2 = 1 by rfl,
        show residualYSWeights 3 = 0 by rfl]
      simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add]
      norm_num [weightedCap, ContactParameters6600Research.multiplicity,
        agreements, n, errors, w] at hb
      omega
    · apply (weightedTotalDegree_le_iff residualTotalWeights F 522).mpr
      intro d hd
      have hb : d 1 + d 3 ≤ seedTotalCap ∧ d 2 ≤ slopeCap ∧
          d 0 + w * d 1 + (w - 1) * d 2 < weightedCap := hbox hd
      rw [weight_fin4]
      rw [show residualTotalWeights 0 = 0 by rfl,
        show residualTotalWeights 1 = 1 by rfl,
        show residualTotalWeights 2 = 1 by rfl,
        show residualTotalWeights 3 = 1 by rfl]
      simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add]
      norm_num [seedTotalCap, slopeCap] at hb
      omega

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Canonical initial outer residual state on one actual geometric factor. -/
def geometricResidualStage
    [CharP K prime]
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (hRpos : 0 < F.degreeOf (2 : Fin 4))
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolutions : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (g : GeometricFactor K F) :
    letI : CharP (GenericField K) prime := genericField_charP K prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K F selected Gamma g) x prime errors
      (geometricFlag K g) w := by
  classical
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hgspec := surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
  have hgirred := hgspec.1
  have hgdiv := hgspec.2
  have hRsmall : F.degreeOf (2 : Fin 4) < prime :=
    (degreeOf_R_le_of_mem_box F weightedCap w seedTotalCap slopeCap hbox).trans_lt
      (by norm_num [slopeCap, prime])
  have hgate := geometric_factor_regular_gate K (GenericField K) F hF prime
    hRpos hRsmall g.1 hgirred
    (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
  have hsub := geometricSeeds_subset K F selected Gamma g
  have hwts := residual_surface_weights_of_box K F hbox
  exact {
    nodes := nodes
    u0 := u0
    u1 := u1
    selected := selected
    F := F
    G := g.1
    irreducible_G := hgirred
    G_dvd_surface := hgdiv
    y_dependent := hgate.1
    regular_proper := by
      simpa only [canonical_geometricSurfaceMap] using hgate.2.2.2.2
    flag_support := polynomialIn_geometricFlag K g
    surface_s_weight := hwts.1
    surface_ys_weight := hwts.2.1
    surface_total_weight := hwts.2.2
    x_injective := hinj
    degree_le := fun gamma hgamma ↦ hdegree gamma (hsub hgamma)
    solution := fun gamma hgamma ↦ hsolutions gamma (hsub hgamma)
    regular := fun gamma hgamma ↦
      selectedPoint_regular_of_specialization K F selected gamma
        (hregular gamma (hsub hgamma))
    on_component := fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2
    no_large_pencil := noLargeSelectedPencil_mono selected Gamma _ w errors
      hsub hnoPencil
    characteristic_bound := by norm_num [w, prime]
  }

/-- Once every geometric factor has its recursive factor-ledger bound, the
actual original factor is charged only by its three Newton support values. -/
theorem original_regular_seed_bound_of_geometric_factor_counts
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hsolutions : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hcount : ∀ g : GeometricFactor K F,
      (geometricSeeds K F selected Gamma g).card * gap ^ 2 ≤
        factorRegularLedger (geometricFlag K g)) :
    Gamma.card * gap ^ 2 ≤
      weightedLedger
        (MvPolynomial.weightedTotalDegree residualTotalWeights F)
        (MvPolynomial.weightedTotalDegree residualYSWeights F)
        (MvPolynomial.weightedTotalDegree residualSWeights F) := by
  have hcover := card_le_sum_geometricSeeds K F hF.ne_zero selected Gamma
    hsolutions
  calc
    Gamma.card * gap ^ 2 ≤
        (∑ g : GeometricFactor K F,
          (geometricSeeds K F selected Gamma g).card) * gap ^ 2 :=
      Nat.mul_le_mul_right _ hcover
    _ = ∑ g : GeometricFactor K F,
        (geometricSeeds K F selected Gamma g).card * gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K F,
        factorRegularLedger (geometricFlag K g) :=
      Finset.sum_le_sum (fun g _ ↦ hcount g)
    _ ≤ weightedLedger
        (MvPolynomial.weightedTotalDegree residualTotalWeights F)
        (MvPolynomial.weightedTotalDegree residualYSWeights F)
        (MvPolynomial.weightedTotalDegree residualSWeights F) := by
      change (∑ g : GeometricFactor K F,
        factorRegularLedger (weightedFlag g.1)) ≤ _
      have hsum := sum_surfaceFactor_ledgers_le (polynomialEmbedding K)
        (polynomialEmbedding_injective K) F hF.ne_zero
      rw [← Finset.sum_coe_sort] at hsum
      exact hsum

end


end ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6600Research

#print axioms ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6600Research.geometricResidualStage
#print axioms ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6600Research.original_regular_seed_bound_of_geometric_factor_counts
