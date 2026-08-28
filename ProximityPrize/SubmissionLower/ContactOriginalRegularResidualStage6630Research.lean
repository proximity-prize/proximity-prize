import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactParameters6630Research
import ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount
import ProximityPrize.SubmissionLower.ContactRegularFactorFlag6630Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualIteration6630Research
import ProximityPrize.SubmissionLower.ContactNearPencil6630FactorLedgerResearch

/-!
# Initial residual stages and geometric-factor aggregation at score 66.30

The geometric factors are charged by their actual nested Newton degrees
`R`, `Y+R`, and `Y+R+Z`.  Additivity of weighted degree across the actual
factor product transfers these cumulative degrees back to the original
factor without rectangular overcount.
-/

namespace ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6630Research

set_option autoImplicit false

open scoped Classical BigOperators
open ContactParameters6630Research
open ContactGenericInitialPoint ContactGenericSurface ContactGeometricFirstTail
open ContactGeometricFactorCover ContactRegularFactorGate ContactFactorCaps
open ContactPrimeSeedIncidence ContactPolynomialSolutions ContactInterpolation
open ContactTranslation ContactProperCutSeedCount
open ContactOriginalRegularSeedCount
open ContactRegularFactorFlag6630Research
open ContactIdentityResidualIteration6630Research
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactFlagBezout6543Research
open ContactFlagTriangularProjectionResearch
open ContactCumulativeWeightedDegreeResearch
open ContactNearPencil6630FactorLedgerResearch

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

variable (K : Type) [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

theorem geometric_weight_nested
    (G : MvPolynomial (Fin 3) (GenericField K)) :
    MvPolynomial.weightedTotalDegree sWeight G ≤
        MvPolynomial.weightedTotalDegree ysWeight G ∧
      MvPolynomial.weightedTotalDegree ysWeight G ≤
        MvPolynomial.weightedTotalDegree totalWeight G := by
  constructor
  · unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro d hd
    calc
      Finsupp.weight sWeight d ≤ Finsupp.weight ysWeight d := by
        rw [TrivariateShearResearch.weight_fin3,
          TrivariateShearResearch.weight_fin3]
        simp [sWeight, ysWeight]
      _ ≤ G.support.sup (Finsupp.weight ysWeight) := Finset.le_sup hd
  · unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro d hd
    calc
      Finsupp.weight ysWeight d ≤ Finsupp.weight totalWeight d := by
        rw [TrivariateShearResearch.weight_fin3,
          TrivariateShearResearch.weight_fin3]
        simp [ysWeight, totalWeight]
      _ ≤ G.support.sup (Finsupp.weight totalWeight) := Finset.le_sup hd

/-- Exact nested-increment flag of one geometric surface factor. -/
def geometricFlag6630 {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : FlagDegree :=
  let inner := MvPolynomial.weightedTotalDegree sWeight g.1
  let middle := MvPolynomial.weightedTotalDegree ysWeight g.1
  let total := MvPolynomial.weightedTotalDegree totalWeight g.1
  ⟨total - middle, middle - inner, inner⟩

theorem geometricFlag6630_cumulative {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) :
    (geometricFlag6630 K g).all =
        MvPolynomial.weightedTotalDegree sWeight g.1 ∧
      (geometricFlag6630 K g).yz + (geometricFlag6630 K g).all =
        MvPolynomial.weightedTotalDegree ysWeight g.1 ∧
      (geometricFlag6630 K g).zOnly + (geometricFlag6630 K g).yz +
          (geometricFlag6630 K g).all =
        MvPolynomial.weightedTotalDegree totalWeight g.1 := by
  have hn := geometric_weight_nested K g.1
  refine ⟨rfl, ?_, ?_⟩
  · exact Nat.sub_add_cancel hn.1
  · simp only [geometricFlag6630]
    rw [Nat.add_assoc, Nat.sub_add_cancel hn.1,
      Nat.sub_add_cancel hn.2]

theorem polynomialIn_geometricFlag6630 {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) :
    ContactFlagBezout6543Research.PolynomialInFlag
      (geometricFlag6630 K g) g.1 := by
  intro d hd
  have hs := MvPolynomial.le_weightedTotalDegree sWeight hd
  have hys := MvPolynomial.le_weightedTotalDegree ysWeight hd
  have htotal := MvPolynomial.le_weightedTotalDegree totalWeight hd
  rw [TrivariateShearResearch.weight_fin3] at hs hys htotal
  simp [sWeight, ysWeight, totalWeight] at hs hys htotal
  have hc := geometricFlag6630_cumulative K g
  change d 1 ≤ (geometricFlag6630 K g).all ∧
    d 0 + d 1 ≤
      (geometricFlag6630 K g).yz + (geometricFlag6630 K g).all ∧
    d 0 + d 1 + d 2 ≤
      (geometricFlag6630 K g).zOnly + (geometricFlag6630 K g).yz +
        (geometricFlag6630 K g).all
  simp only [sWeight, ysWeight, totalWeight] at hs hys htotal hc
  rw [← hc.1] at hs
  rw [← hc.2.1] at hys
  rw [← hc.2.2] at htotal
  omega

/-- Dropping the coefficient variable preserves each of the three nested
support functionals. -/
theorem surfaceMap_nested_weights_le
    {L : Type} [Field L] (phi : Polynomial K →+* L)
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.weightedTotalDegree sWeight (surfaceMap phi F) ≤
        MvPolynomial.weightedTotalDegree residualSWeights F ∧
      MvPolynomial.weightedTotalDegree ysWeight (surfaceMap phi F) ≤
        MvPolynomial.weightedTotalDegree residualYSWeights F ∧
      MvPolynomial.weightedTotalDegree totalWeight (surfaceMap phi F) ≤
        MvPolynomial.weightedTotalDegree residualTotalWeights F := by
  refine ⟨?_, ?_, ?_⟩
  · unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
      (support_surfaceMap_subset phi F he)
    have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
    rw [TrivariateShearResearch.weight_fin3]
    rw [ContactFactorCaps.weight_fin4] at h
    simp [sWeight, residualSWeights] at h ⊢
    exact h
  · unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
      (support_surfaceMap_subset phi F he)
    have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
    rw [TrivariateShearResearch.weight_fin3]
    rw [ContactFactorCaps.weight_fin4] at h
    simp [ysWeight, residualYSWeights] at h ⊢
    exact h
  · unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
      (support_surfaceMap_subset phi F he)
    have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
    rw [TrivariateShearResearch.weight_fin3]
    rw [ContactFactorCaps.weight_fin4] at h
    simp [totalWeight, residualTotalWeights] at h ⊢
    exact h

/-- Nested flag of an original four-variable factor. -/
def originalFlag6630 (F : MvPolynomial (Fin 4) K) : FlagDegree :=
  let inner := MvPolynomial.weightedTotalDegree residualSWeights F
  let middle := MvPolynomial.weightedTotalDegree residualYSWeights F
  let total := MvPolynomial.weightedTotalDegree residualTotalWeights F
  ⟨total - middle, middle - inner, inner⟩

theorem originalFlag6630_eq_regularFlag
    {Q : MvPolynomial (Fin 4) K} (R : RegularIndex Q) :
    originalFlag6630 K R.1 = regularFlag6630 Q R := rfl

/-- Actual geometric factors consume at most the original factor's three
cumulative Newton degrees. -/
theorem geometricFlag6630_budgets
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) :
    (∑ g : GeometricFactor K F, (geometricFlag6630 K g).all) ≤
        (originalFlag6630 K F).all ∧
      (∑ g : GeometricFactor K F,
        ((geometricFlag6630 K g).yz + (geometricFlag6630 K g).all)) ≤
        (originalFlag6630 K F).yz + (originalFlag6630 K F).all ∧
      (∑ g : GeometricFactor K F,
        ((geometricFlag6630 K g).zOnly + (geometricFlag6630 K g).yz +
          (geometricFlag6630 K g).all)) ≤
        (originalFlag6630 K F).zOnly + (originalFlag6630 K F).yz +
          (originalFlag6630 K F).all := by
  classical
  let phi := polynomialEmbedding K
  let SF := surfaceMap phi F
  have hSF : SF ≠ 0 := surfaceMap_ne_zero phi
    (polynomialEmbedding_injective K) F hF
  have hprod := normalizedFactorSet_product_dvd SF hSF
  have hs := sum_weightedTotalDegree_le_of_prod_dvd_fin3 sWeight
    (surfaceFactors phi F) id SF hSF hprod
  have hys := sum_weightedTotalDegree_le_of_prod_dvd_fin3 ysWeight
    (surfaceFactors phi F) id SF hSF hprod
  have htotal := sum_weightedTotalDegree_le_of_prod_dvd_fin3 totalWeight
    (surfaceFactors phi F) id SF hSF hprod
  have hmap := surfaceMap_nested_weights_le K phi F
  have hn := residual_weight_nested F
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_congr rfl (fun g _ ↦
        (geometricFlag6630_cumulative K g).1), Finset.sum_coe_sort]
    exact hs.trans hmap.1
  · rw [Finset.sum_congr rfl (fun g _ ↦
        (geometricFlag6630_cumulative K g).2.1), Finset.sum_coe_sort]
    have hbound := hys.trans hmap.2.1
    simp only [phi, id_eq] at hbound
    simp only [originalFlag6630, Nat.sub_add_cancel hn.1]
    omega
  · rw [Finset.sum_congr rfl (fun g _ ↦
        (geometricFlag6630_cumulative K g).2.2), Finset.sum_coe_sort]
    have hc : (originalFlag6630 K F).zOnly +
        (originalFlag6630 K F).yz + (originalFlag6630 K F).all =
        MvPolynomial.weightedTotalDegree residualTotalWeights F := by
      simp only [originalFlag6630]
      rw [Nat.add_assoc, Nat.sub_add_cancel hn.1,
        Nat.sub_add_cancel hn.2]
    rw [hc]
    exact htotal.trans hmap.2.2

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Canonical initial score-66.30 residual state on one actual geometric
factor. -/
def geometricResidualStage6630
    [CharP K prime]
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (hRpos : 0 < F.degreeOf (2 : Fin 4))
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hsurface :
      MvPolynomial.weightedTotalDegree residualSWeights F ≤ 10 ∧
      MvPolynomial.weightedTotalDegree residualYSWeights F ≤ 48 ∧
      MvPolynomial.weightedTotalDegree residualTotalWeights F ≤ 814)
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
    ResidualStage6630 (polynomialEmbedding K)
      (geometricSeeds K F selected Gamma g) x prime errors
      (geometricFlag6630 K g) w := by
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
    flag_support := polynomialIn_geometricFlag6630 K g
    surface_s_weight := hsurface.1
    surface_ys_weight := hsurface.2.1
    surface_total_weight := hsurface.2.2
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

/-- Geometric recursive bounds aggregate sharply to the original factor's
nested Newton ledger. -/
theorem original_regular_seed_bound_of_geometric_counts6630
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hsolutions : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hcount : ∀ g : GeometricFactor K F,
      (geometricSeeds K F selected Gamma g).card * gap ^ 2 ≤
        factorRegularLedgerYZ (geometricFlag6630 K g)) :
    Gamma.card * gap ^ 2 ≤
      factorRegularLedgerYZ (originalFlag6630 K F) := by
  have hcover := card_le_sum_geometricSeeds K F hF.ne_zero selected Gamma
    hsolutions
  have hcaps := geometricFlag6630_budgets K F hF.ne_zero
  calc
    Gamma.card * gap ^ 2 ≤
        (∑ g : GeometricFactor K F,
          (geometricSeeds K F selected Gamma g).card) * gap ^ 2 :=
      Nat.mul_le_mul_right _ hcover
    _ = ∑ g : GeometricFactor K F,
        (geometricSeeds K F selected Gamma g).card * gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K F,
        factorRegularLedgerYZ (geometricFlag6630 K g) :=
      Finset.sum_le_sum (fun g _ ↦ hcount g)
    _ ≤ factorRegularLedgerYZ (originalFlag6630 K F) :=
      sum_factorRegularLedgerYZ_le_flag (geometricFlag6630 K)
        (originalFlag6630 K F) hcaps.1 hcaps.2.1 hcaps.2.2

end


end ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6630Research
