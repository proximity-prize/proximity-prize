import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTetraGeometricSeedCover6622Research
import ProximityPrize.SubmissionLower.ContactRegularFactorFlag6600Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualIterationResearch
import ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch
import ProximityPrize.SubmissionLower.ContactSharpFactorAggregationPost6600Research

/-!
# Initial residual stages for actual score-66.11 regular factors

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
open ContactTetraGeometricSeedCover6622Research
open ContactRegularFactorFlag6600Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactFlagBezout6543Research
open ContactNearPencil6600FactorLedgerResearch
open ContactSharpFactorAggregationPost6600Research

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

variable (K : Type) [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

/-- Rectangular nested flag of one geometric factor, in the literal
`(Z,Y,R)` degree order. -/
def geometricFlag {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : FlagDegree :=
  ⟨g.1.degreeOf (2 : Fin 3), g.1.degreeOf (0 : Fin 3),
    g.1.degreeOf (1 : Fin 3)⟩

theorem polynomialIn_geometricFlag {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : PolynomialInFlag (geometricFlag K g) g.1 := by
  intro d hd
  have h0 := MvPolynomial.monomial_le_degreeOf (0 : Fin 3) hd
  have h1 := MvPolynomial.monomial_le_degreeOf (1 : Fin 3) hd
  have h2 := MvPolynomial.monomial_le_degreeOf (2 : Fin 3) hd
  change d 1 ≤ g.1.degreeOf 1 ∧
    d 0 + d 1 ≤ g.1.degreeOf 0 + g.1.degreeOf 1 ∧
    d 0 + d 1 + d 2 ≤
      g.1.degreeOf 2 + g.1.degreeOf 0 + g.1.degreeOf 1
  omega

/-- The interpolation box supplies exactly the three global support values
preserved by residualization. -/
theorem residual_surface_weights_of_box
    (F : MvPolynomial (Fin 4) K)
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (htetra : ∀ d ∈ F.support, d 1 + d 2 + d 3 ≤ seedTotalCap) :
    wt residualSWeights F ≤ 9 ∧
      wt residualYSWeights F ≤ 44 ∧
      wt residualTotalWeights F ≤ 464 := by
  constructor
  · apply (weightedTotalDegree_le_iff residualSWeights F 9).mpr
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
    · apply (weightedTotalDegree_le_iff residualYSWeights F 44).mpr
      intro d hd
      have hb : d 1 + d 3 ≤ seedTotalCap ∧ d 2 ≤ slopeCap ∧
          d 0 + w * d 1 + (w - 1) * d 2 < weightedCap := hbox hd
      rw [weight_fin4]
      rw [show residualYSWeights 0 = 0 by rfl,
        show residualYSWeights 1 = 1 by rfl,
        show residualYSWeights 2 = 1 by rfl,
        show residualYSWeights 3 = 0 by rfl]
      simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
      norm_num [weightedCap, ContactParameters6600Research.multiplicity,
        agreements, n, errors, w] at hb
      omega
    · apply (weightedTotalDegree_le_iff residualTotalWeights F 464).mpr
      intro d hd
      rw [weight_fin4]
      rw [show residualTotalWeights 0 = 0 by rfl,
        show residualTotalWeights 1 = 1 by rfl,
        show residualTotalWeights 2 = 1 by rfl,
        show residualTotalWeights 3 = 1 by rfl]
      simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
      simpa only [seedTotalCap] using htetra d hd

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Canonical initial outer residual state on one actual geometric factor. -/
def geometricResidualStage
    [CharP K prime]
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (hRpos : 0 < F.degreeOf (2 : Fin 4))
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (htetra : ∀ d ∈ F.support, d 1 + d 2 + d 3 ≤ seedTotalCap)
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
      (sharpGeometricFlag K g) w := by
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
  have hwts := residual_surface_weights_of_box K F hbox htetra
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
    flag_support := polynomialIn_sharpGeometricFlag F g
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

end


end ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6600Research

#print axioms ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6600Research.geometricResidualStage
