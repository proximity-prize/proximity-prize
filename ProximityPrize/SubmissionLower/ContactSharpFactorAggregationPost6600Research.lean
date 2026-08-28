import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactParameters6600Research
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition
import ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch
import ProximityPrize.SubmissionLower.ContactSingularDegreeBounds
import ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount
import ProximityPrize.SubmissionLower.TrivariateShearResearch

/-!
# Sound sharp-flag aggregation for the post-score-66 regular factors

The three additive resources of a factor are the nested support functions

* `R`,
* `Y + R`, and
* `Y + R + Z`.

Their differences give a sharp flag for one factor, but those differences
must not be bounded coordinatewise after summing.  Instead this file rewrites
the linear regular ledger in the three raw resources.  All coefficients in
that rewrite are nonnegative, so the genuine divisor-product bounds aggregate
directly.  The tetrahedral global raw cap is
`(slopeCap,yCap,seedTotalCap)`, whose nested differences are exactly
the sharp surface flag used by the active parameter row.
-/

namespace ProximityPrize.SubmissionLower.ContactSharpFactorAggregationPost6600Research

open scoped BigOperators
open ContactParameters6600Research
open ContactSelectedSeedDecomposition ContactImplicitContactLift
open ContactInterpolation ContactGenericSurface ContactFactorCaps
open ContactSingularDegreeBounds
open ContactIdentityResidualGlobalFlagResearch
open ContactFlagBezout6543Research
open ContactNearPencil6600FlagResearch
open ContactNearPencil6600FactorLedgerResearch
open ContactOriginalRegularSeedCount ContactGeometricFactorCover
open ContactGenericInitialPoint ContactTranslation

noncomputable section

set_option maxHeartbeats 300000
set_option maxRecDepth 30000

variable {K Omega : Type} [Field K] [Field Omega]

abbrev RegularIndex (Q : MvPolynomial (Fin 4) K) :=
  ↥(positiveRFactors Q)

/-- Raw `R` support value of an actual positive-`R` factor. -/
def factorRawR (Q : MvPolynomial (Fin 4) K) (F : RegularIndex Q) : ℕ :=
  MvPolynomial.weightedTotalDegree residualSWeights F.1

/-- Raw `Y+R` support value of an actual positive-`R` factor. -/
def factorRawYR (Q : MvPolynomial (Fin 4) K) (F : RegularIndex Q) : ℕ :=
  MvPolynomial.weightedTotalDegree residualYSWeights F.1

/-- Raw `Y+R+Z` support value of an actual positive-`R` factor. -/
def factorRawTotal (Q : MvPolynomial (Fin 4) K) (F : RegularIndex Q) : ℕ :=
  MvPolynomial.weightedTotalDegree residualTotalWeights F.1

@[simp] theorem residualS_weight (d : Fin 4 →₀ ℕ) :
    Finsupp.weight residualSWeights d = d 2 := by
  rw [weight_fin4]
  rw [show residualSWeights 0 = 0 by rfl,
    show residualSWeights 1 = 0 by rfl,
    show residualSWeights 2 = 1 by rfl,
    show residualSWeights 3 = 0 by rfl]
  simp

@[simp] theorem residualYS_weight (d : Fin 4 →₀ ℕ) :
    Finsupp.weight residualYSWeights d = d 1 + d 2 := by
  rw [weight_fin4]
  rw [show residualYSWeights 0 = 0 by rfl,
    show residualYSWeights 1 = 1 by rfl,
    show residualYSWeights 2 = 1 by rfl,
    show residualYSWeights 3 = 0 by rfl]
  simp

@[simp] theorem residualTotal_weight (d : Fin 4 →₀ ℕ) :
    Finsupp.weight residualTotalWeights d = d 1 + d 2 + d 3 := by
  rw [weight_fin4]
  rw [show residualTotalWeights 0 = 0 by rfl,
    show residualTotalWeights 1 = 1 by rfl,
    show residualTotalWeights 2 = 1 by rfl,
    show residualTotalWeights 3 = 1 by rfl]
  simp

theorem factorRawR_le_factorRawYR
    (Q : MvPolynomial (Fin 4) K) (F : RegularIndex Q) :
    factorRawR Q F ≤ factorRawYR Q F := by
  unfold factorRawR factorRawYR
  apply (weightedTotalDegree_le_iff residualSWeights F.1 (factorRawYR Q F)).mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [residualS_weight]
  rw [residualYS_weight] at h
  exact (Nat.le_add_left _ _).trans h

theorem factorRawYR_le_factorRawTotal
    (Q : MvPolynomial (Fin 4) K) (F : RegularIndex Q) :
    factorRawYR Q F ≤ factorRawTotal Q F := by
  unfold factorRawYR factorRawTotal
  apply (weightedTotalDegree_le_iff residualYSWeights F.1 (factorRawTotal Q F)).mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [residualYS_weight]
  rw [residualTotal_weight] at h
  exact (Nat.le_add_right _ _).trans h

/-- The sharp nested flag attached to one factor.  The differences are used
only to describe that factor's support; aggregation below is performed in the
three raw facets. -/
def sharpRegularFlag (Q : MvPolynomial (Fin 4) K) (F : RegularIndex Q) :
    FlagDegree :=
  ⟨factorRawTotal Q F - factorRawYR Q F,
    factorRawYR Q F - factorRawR Q F,
    factorRawR Q F⟩

/-- Mapping `X` into the coefficient field preserves all three raw facets,
so the actual factor surface lies in its sharp nested flag. -/
theorem surfaceMap_in_sharpRegularFlag
    (phi : Polynomial K →+* Omega)
    (Q : MvPolynomial (Fin 4) K) (F : RegularIndex Q) :
    PolynomialInFlag (sharpRegularFlag Q F) (surfaceMap phi F.1) := by
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi F.1 he)
  have hR := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  have hYR := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  have hTotal := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [residualS_weight] at hR
  rw [residualYS_weight] at hYR
  rw [residualTotal_weight] at hTotal
  change d 2 ≤ factorRawR Q F at hR
  change d 1 + d 2 ≤ factorRawYR Q F at hYR
  change d 1 + d 2 + d 3 ≤ factorRawTotal Q F at hTotal
  have hRQ := factorRawR_le_factorRawYR Q F
  have hQT := factorRawYR_le_factorRawTotal Q F
  change d 2 ≤ factorRawR Q F ∧
    d 1 + d 2 ≤ (factorRawYR Q F - factorRawR Q F) + factorRawR Q F ∧
    d 1 + d 2 + d 3 ≤
      (factorRawTotal Q F - factorRawYR Q F) +
        (factorRawYR Q F - factorRawR Q F) + factorRawR Q F
  omega

/-- The interpolation coefficient box supplies the three raw global support
bounds `(R,Y+R,Y+R+Z) ≤ (slopeCap,yCap,seedTotalCap)`. -/
theorem global_raw_facets_of_box
    (Q : MvPolynomial (Fin 4) K)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (htetra : ∀ d ∈ Q.support, d 1 + d 2 + d 3 ≤ seedTotalCap) :
    MvPolynomial.weightedTotalDegree residualSWeights Q ≤ slopeCap ∧
      MvPolynomial.weightedTotalDegree residualYSWeights Q ≤ yCap ∧
      MvPolynomial.weightedTotalDegree residualTotalWeights Q ≤ seedTotalCap := by
  refine ⟨?_, ?_, ?_⟩
  · apply (weightedTotalDegree_le_iff residualSWeights Q slopeCap).mpr
    intro d hd
    have hb := hbox hd
    rw [residualS_weight]
    exact hb.2.1
  · apply (weightedTotalDegree_le_iff residualYSWeights Q yCap).mpr
    intro d hd
    have hb := hbox hd
    rw [residualYS_weight]
    have hc := hb.2.2
    have hy : ContactParameters6600Research.yCap = 44 := by
      norm_num [ContactParameters6600Research.yCap,
        ContactParameters6600Research.weightedCap,
        ContactParameters6600Research.multiplicity,
        ContactParameters6600Research.agreements,
        ContactParameters6600Research.n,
        ContactParameters6600Research.errors,
        ContactParameters6600Research.w]
    rw [hy]
    norm_num [ContactParameters6600Research.weightedCap,
      ContactParameters6600Research.multiplicity,
      ContactParameters6600Research.agreements,
      ContactParameters6600Research.n,
      ContactParameters6600Research.errors,
      ContactParameters6600Research.w] at hc
    omega
  · apply (weightedTotalDegree_le_iff residualTotalWeights Q seedTotalCap).mpr
    intro d hd
    rw [residualTotal_weight]
    exact htetra d hd

/-- Genuine divisor-product additivity gives the three factor-family raw
budgets.  No difference of support values is summed or bounded here. -/
theorem positiveRFactor_raw_budgets
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (htetra : ∀ d ∈ Q.support, d 1 + d 2 + d 3 ≤ seedTotalCap) :
    (∑ F : RegularIndex Q, factorRawR Q F) ≤ slopeCap ∧
      (∑ F : RegularIndex Q, factorRawYR Q F) ≤ yCap ∧
      (∑ F : RegularIndex Q, factorRawTotal Q F) ≤ seedTotalCap := by
  classical
  have hdiv := positiveRFactors_product_dvd Q hQ
  have hRsum := sum_weighted_degrees_le_of_prod_dvd residualSWeights
    (positiveRFactors Q) id Q hQ hdiv
  have hYRsum := sum_weighted_degrees_le_of_prod_dvd residualYSWeights
    (positiveRFactors Q) id Q hQ hdiv
  have hTotalsum := sum_weighted_degrees_le_of_prod_dvd residualTotalWeights
    (positiveRFactors Q) id Q hQ hdiv
  obtain ⟨hR, hYR, hTotal⟩ := global_raw_facets_of_box Q hbox htetra
  simp only [factorRawR, factorRawYR, factorRawTotal, Finset.sum_coe_sort]
  exact ⟨hRsum.trans hR, hYRsum.trans hYR, hTotalsum.trans hTotal⟩

/-- Raw-facet form of the linear factor ledger.  The successive coefficient
differences are nonnegative at the score-66 agreement flag. -/
def rawFactorLedger (r q t : ℕ) : ℕ :=
  t * factorRegularLedger unitZFlag +
    q * (factorRegularLedger unitYZFlag - factorRegularLedger unitZFlag) +
    r * (factorRegularLedger unitAllFlag - factorRegularLedger unitYZFlag)

theorem unit_factorRegularLedger_order :
    factorRegularLedger unitZFlag ≤ factorRegularLedger unitYZFlag ∧
      factorRegularLedger unitYZFlag ≤ factorRegularLedger unitAllFlag := by
  norm_num [factorRegularLedger, factorPrimary, factorZTail, factorAllTail,
    flagMixed, agreementDirection6600, unitZFlag, unitYZFlag, unitAllFlag,
    ContactNearPencil6600ArithmeticResearch.degreeIncidence,
    ContactNearPencil6600ArithmeticResearch.unitIncidence,
    ContactNearPencil6600ArithmeticResearch.errors,
    ContactNearPencil6600ArithmeticResearch.gap,
    ContactNearPencil6600ArithmeticResearch.agreements,
    ContactNearPencil6600ArithmeticResearch.n,
    ContactNearPencil6600ArithmeticResearch.w]

/-- Generic algebra behind the raw-facet rewrite.  The proof uses the four
order hypotheses only to cancel natural-number subtractions, and is
independent of all score constants. -/
theorem nested_difference_linear
    (r q t A B C : ℕ)
    (hrq : r ≤ q) (hqt : q ≤ t) (hAB : A ≤ B) (hBC : B ≤ C) :
    (t - q) * A + (q - r) * B + r * C =
      t * A + q * (B - A) + r * (C - B) := by
  have htA : t * A = (t - q) * A + q * A := by
    conv_lhs => rw [← Nat.sub_add_cancel hqt]
    ring
  have hqB : q * B = (q - r) * B + r * B := by
    conv_lhs => rw [← Nat.sub_add_cancel hrq]
    ring
  have hB : A + (B - A) = B := by omega
  have hC : B + (C - B) = C := by omega
  symm
  calc
    t * A + q * (B - A) + r * (C - B) =
        ((t - q) * A + q * A) + q * (B - A) + r * (C - B) := by
      rw [htA]
    _ = (t - q) * A + q * (A + (B - A)) + r * (C - B) := by ring
    _ = (t - q) * A + q * B + r * (C - B) := by rw [hB]
    _ = (t - q) * A + ((q - r) * B + r * B) + r * (C - B) := by rw [hqB]
    _ = (t - q) * A + (q - r) * B + r * (B + (C - B)) := by ring
    _ = (t - q) * A + (q - r) * B + r * C := by rw [hC]

/-- Ledger rewrite for any three ordered raw facets. -/
theorem factorRegularLedger_nested_eq_raw
    (r q t : ℕ) (hrq : r ≤ q) (hqt : q ≤ t) :
    factorRegularLedger ⟨t - q, q - r, r⟩ = rawFactorLedger r q t := by
  rw [factorRegularLedger_projection_decomposition]
  unfold rawFactorLedger
  obtain ⟨hZU, hUA⟩ := unit_factorRegularLedger_order
  exact nested_difference_linear _ _ _ _ _ _ hrq hqt hZU hUA

/-- The ledger of a sharp factor flag equals its positive raw-facet linear
form. -/
theorem factorRegularLedger_sharp_eq_raw
    (Q : MvPolynomial (Fin 4) K) (F : RegularIndex Q) :
    factorRegularLedger (sharpRegularFlag Q F) =
      rawFactorLedger (factorRawR Q F) (factorRawYR Q F)
        (factorRawTotal Q F) := by
  exact factorRegularLedger_nested_eq_raw _ _ _
    (factorRawR_le_factorRawYR Q F) (factorRawYR_le_factorRawTotal Q F)

theorem sum_rawFactorLedger
    {I : Type} [Fintype I] (r q t : I → ℕ) :
    (∑ i, rawFactorLedger (r i) (q i) (t i)) =
      rawFactorLedger (∑ i, r i) (∑ i, q i) (∑ i, t i) := by
  simp [rawFactorLedger, Finset.sum_add_distrib, Finset.sum_mul]

theorem rawFactorLedger_mono
    {r q t R Q T : ℕ} (hr : r ≤ R) (hq : q ≤ Q) (ht : t ≤ T) :
    rawFactorLedger r q t ≤ rawFactorLedger R Q T := by
  unfold rawFactorLedger
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.mul_le_mul_right _ ht)
      (Nat.mul_le_mul_right _ hq))
    (Nat.mul_le_mul_right _ hr)

/-- Abstract sound aggregation theorem in the three additive raw facets. -/
theorem sum_factorRegularLedger_sharp_le_raw_cap
    {I : Type} [Fintype I] (r q t : I → ℕ)
    (p : I → FlagDegree)
    (hp : ∀ i, p i = ⟨t i - q i, q i - r i, r i⟩)
    (hrq : ∀ i, r i ≤ q i) (hqt : ∀ i, q i ≤ t i)
    (R Q T : ℕ)
    (hr : (∑ i, r i) ≤ R) (hq : (∑ i, q i) ≤ Q)
    (ht : (∑ i, t i) ≤ T) :
    (∑ i, factorRegularLedger (p i)) ≤ rawFactorLedger R Q T := by
  calc
    (∑ i, factorRegularLedger (p i)) =
        ∑ i, rawFactorLedger (r i) (q i) (t i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hp i]
      exact factorRegularLedger_nested_eq_raw _ _ _ (hrq i) (hqt i)
    _ = rawFactorLedger (∑ i, r i) (∑ i, q i) (∑ i, t i) :=
      sum_rawFactorLedger r q t
    _ ≤ rawFactorLedger R Q T := rawFactorLedger_mono hr hq ht

/-- The sharp flag obtained by differencing the three global raw facets. -/
def additiveSurfaceFlag : FlagDegree :=
  ⟨seedTotalCap - yCap, yCap - slopeCap, slopeCap⟩

theorem additiveSurfaceFlag_eq_surfaceFlag :
    additiveSurfaceFlag = surfaceFlag6600 := by
  norm_num [additiveSurfaceFlag, surfaceFlag6600,
    ContactParameters6600Research.seedTotalCap,
    ContactParameters6600Research.slopeCap,
    ContactParameters6600Research.yCap,
    ContactParameters6600Research.weightedCap,
    ContactParameters6600Research.multiplicity,
    ContactParameters6600Research.agreements,
    ContactParameters6600Research.n,
    ContactParameters6600Research.errors,
    ContactParameters6600Research.w]

/-- Exact raw-to-flag identity for the active global cap. -/
theorem rawFactorLedger_global_eq_sharp :
    rawFactorLedger slopeCap yCap seedTotalCap =
      factorRegularLedger surfaceFlag6600 := by
  rw [← additiveSurfaceFlag_eq_surfaceFlag]
  apply (factorRegularLedger_nested_eq_raw _ _ _ ?_ ?_).symm
  · norm_num [ContactParameters6600Research.seedTotalCap,
      ContactParameters6600Research.slopeCap,
      ContactParameters6600Research.yCap,
      ContactParameters6600Research.weightedCap,
      ContactParameters6600Research.multiplicity,
      ContactParameters6600Research.agreements,
      ContactParameters6600Research.n,
      ContactParameters6600Research.errors,
      ContactParameters6600Research.w]
  · norm_num [ContactParameters6600Research.seedTotalCap,
      ContactParameters6600Research.slopeCap,
      ContactParameters6600Research.yCap,
      ContactParameters6600Research.weightedCap,
      ContactParameters6600Research.multiplicity,
      ContactParameters6600Research.agreements,
      ContactParameters6600Research.n,
      ContactParameters6600Research.errors,
      ContactParameters6600Research.w]

/-- The actual positive-`R` factors consume at most the sharp global regular
ledger, using only additive raw facet budgets. -/
theorem sum_actual_sharp_factorRegularLedger_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (htetra : ∀ d ∈ Q.support, d 1 + d 2 + d 3 ≤ seedTotalCap) :
    (∑ F : RegularIndex Q, factorRegularLedger (sharpRegularFlag Q F)) ≤
      factorRegularLedger surfaceFlag6600 := by
  obtain ⟨hR, hYR, hTotal⟩ := positiveRFactor_raw_budgets Q hQ hbox htetra
  calc
    _ ≤ rawFactorLedger slopeCap yCap seedTotalCap :=
      sum_factorRegularLedger_sharp_le_raw_cap
        (fun F : RegularIndex Q ↦ factorRawR Q F)
        (fun F : RegularIndex Q ↦ factorRawYR Q F)
        (fun F : RegularIndex Q ↦ factorRawTotal Q F)
        (fun F : RegularIndex Q ↦ sharpRegularFlag Q F)
        (fun _ ↦ rfl)
        (fun F ↦ factorRawR_le_factorRawYR Q F)
        (fun F ↦ factorRawYR_le_factorRawTotal Q F)
        slopeCap yCap seedTotalCap hR hYR hTotal
    _ = factorRegularLedger surfaceFlag6600 := rawFactorLedger_global_eq_sharp

/-! ## The geometric-factor seam -/

/-- Nested raw weights in the geometric `(Y,R,Z)` variables. -/
def geometricRWeights : Fin 3 → ℕ := ![0, 1, 0]
def geometricYRWeights : Fin 3 → ℕ := ![1, 1, 0]
def geometricTotalWeights : Fin 3 → ℕ := ![1, 1, 1]

@[simp] theorem geometricR_weight (d : Fin 3 →₀ ℕ) :
    Finsupp.weight geometricRWeights d = d 1 := by
  rw [TrivariateShearResearch.weight_fin3]
  change d 0 * 0 + d 1 * 1 + d 2 * 0 = d 1
  omega

@[simp] theorem geometricYR_weight (d : Fin 3 →₀ ℕ) :
    Finsupp.weight geometricYRWeights d = d 0 + d 1 := by
  rw [TrivariateShearResearch.weight_fin3]
  change d 0 * 1 + d 1 * 1 + d 2 * 0 = d 0 + d 1
  omega

@[simp] theorem geometricTotal_weight (d : Fin 3 →₀ ℕ) :
    Finsupp.weight geometricTotalWeights d = d 0 + d 1 + d 2 := by
  rw [TrivariateShearResearch.weight_fin3]
  change d 0 * 1 + d 1 * 1 + d 2 * 1 = d 0 + d 1 + d 2
  omega

theorem weightedTotalDegree_le_iff3
    {A : Type*} [CommSemiring A] (weights : Fin 3 → ℕ)
    (P : MvPolynomial (Fin 3) A) (cap : ℕ) :
    MvPolynomial.weightedTotalDegree weights P ≤ cap ↔
      ∀ d ∈ P.support, Finsupp.weight weights d ≤ cap := by
  simp only [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]

variable (K) in
def geometricRawR {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : ℕ :=
  MvPolynomial.weightedTotalDegree geometricRWeights g.1

variable (K) in
def geometricRawYR {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : ℕ :=
  MvPolynomial.weightedTotalDegree geometricYRWeights g.1

variable (K) in
def geometricRawTotal {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : ℕ :=
  MvPolynomial.weightedTotalDegree geometricTotalWeights g.1

variable (K) in
def sharpGeometricFlag {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : FlagDegree :=
  ⟨geometricRawTotal K g - geometricRawYR K g,
    geometricRawYR K g - geometricRawR K g,
    geometricRawR K g⟩

theorem geometricRawR_le_geometricRawYR
    (F : MvPolynomial (Fin 4) K) (g : GeometricFactor K F) :
    geometricRawR K g ≤ geometricRawYR K g := by
  unfold geometricRawR geometricRawYR
  apply (weightedTotalDegree_le_iff3 geometricRWeights g.1
    (MvPolynomial.weightedTotalDegree geometricYRWeights g.1)).mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree geometricYRWeights hd
  rw [geometricR_weight]
  rw [geometricYR_weight] at h
  exact (Nat.le_add_left _ _).trans h

theorem geometricRawYR_le_geometricRawTotal
    (F : MvPolynomial (Fin 4) K) (g : GeometricFactor K F) :
    geometricRawYR K g ≤ geometricRawTotal K g := by
  unfold geometricRawYR geometricRawTotal
  apply (weightedTotalDegree_le_iff3 geometricYRWeights g.1
    (MvPolynomial.weightedTotalDegree geometricTotalWeights g.1)).mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree geometricTotalWeights hd
  rw [geometricYR_weight]
  rw [geometricTotal_weight] at h
  exact (Nat.le_add_right _ _).trans h

/-- Every actual geometric factor is contained in its sharp nested flag. -/
theorem polynomialIn_sharpGeometricFlag
    (F : MvPolynomial (Fin 4) K) (g : GeometricFactor K F) :
    PolynomialInFlag (sharpGeometricFlag K g) g.1 := by
  intro d hd
  have hR := MvPolynomial.le_weightedTotalDegree geometricRWeights hd
  have hYR := MvPolynomial.le_weightedTotalDegree geometricYRWeights hd
  have hTotal := MvPolynomial.le_weightedTotalDegree geometricTotalWeights hd
  rw [geometricR_weight] at hR
  rw [geometricYR_weight] at hYR
  rw [geometricTotal_weight] at hTotal
  change d 1 ≤ geometricRawR K g at hR
  change d 0 + d 1 ≤ geometricRawYR K g at hYR
  change d 0 + d 1 + d 2 ≤ geometricRawTotal K g at hTotal
  have hRQ := geometricRawR_le_geometricRawYR F g
  have hQT := geometricRawYR_le_geometricRawTotal F g
  change d 1 ≤ geometricRawR K g ∧
    d 0 + d 1 ≤
      (geometricRawYR K g - geometricRawR K g) + geometricRawR K g ∧
    d 0 + d 1 + d 2 ≤
      (geometricRawTotal K g - geometricRawYR K g) +
        (geometricRawYR K g - geometricRawR K g) + geometricRawR K g
  omega

/-- Fin-three analogue of the exact weighted divisor-product budget. -/
theorem sum_trivariate_weighted_degrees_le_of_prod_dvd
    {A : Type} {I : Type*} [Field A] (weights : Fin 3 → ℕ)
    (S : Finset I) (f : I → MvPolynomial (Fin 3) A)
    (P : MvPolynomial (Fin 3) A) (hP : P ≠ 0)
    (hdiv : (∏ i ∈ S, f i) ∣ P) :
    (∑ i ∈ S, MvPolynomial.weightedTotalDegree weights (f i)) ≤
      MvPolynomial.weightedTotalDegree weights P := by
  classical
  have hprod : (∏ i ∈ S, f i) ≠ 0 := by
    intro hz
    obtain ⟨T, hT⟩ := hdiv
    exact hP (by rw [hT, hz, zero_mul])
  have hf : ∀ i ∈ S, f i ≠ 0 := Finset.prod_ne_zero_iff.mp hprod
  have hlift (i : I) (hi : i ∈ S) :
      TrivariateShearResearch.weightedLift weights (f i) ≠ 0 := by
    intro hz
    exact hf i hi (TrivariateShearResearch.weightedLift_injective weights
      (by simpa only [map_zero] using hz))
  have hmap :
      (∏ i ∈ S, TrivariateShearResearch.weightedLift weights (f i)) ∣
        TrivariateShearResearch.weightedLift weights P := by
    obtain ⟨T, hT⟩ := hdiv
    refine ⟨TrivariateShearResearch.weightedLift weights T, ?_⟩
    rw [hT, map_mul, map_prod]
  have hPmap : TrivariateShearResearch.weightedLift weights P ≠ 0 := by
    intro hz
    exact hP (TrivariateShearResearch.weightedLift_injective weights
      (by simpa only [map_zero] using hz))
  calc
    (∑ i ∈ S, MvPolynomial.weightedTotalDegree weights (f i)) =
        ∑ i ∈ S,
          (TrivariateShearResearch.weightedLift weights (f i)).degreeOf
            (3 : Fin 4) := by
      simp only [TrivariateShearResearch.degree_weightedLift]
    _ = (∏ i ∈ S,
        TrivariateShearResearch.weightedLift weights (f i)).degreeOf
          (3 : Fin 4) :=
      (MvPolynomial.degreeOf_prod_eq S _ hlift).symm
    _ ≤ (TrivariateShearResearch.weightedLift weights P).degreeOf
        (3 : Fin 4) :=
      coordinate_degree_le_of_dvd (3 : Fin 4) _ _ hmap hPmap
    _ = MvPolynomial.weightedTotalDegree weights P :=
      TrivariateShearResearch.degree_weightedLift weights P

theorem surfaceMap_geometricR_le_original
    (phi : Polynomial K →+* Omega) (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.weightedTotalDegree geometricRWeights (surfaceMap phi F) ≤
      MvPolynomial.weightedTotalDegree residualSWeights F := by
  apply (weightedTotalDegree_le_iff3 geometricRWeights (surfaceMap phi F) _).mpr
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_surfaceMap_subset phi F he)
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [geometricR_weight]
  rw [residualS_weight] at h
  change d (2 : Fin 4) ≤ _
  exact h

theorem surfaceMap_geometricYR_le_original
    (phi : Polynomial K →+* Omega) (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.weightedTotalDegree geometricYRWeights (surfaceMap phi F) ≤
      MvPolynomial.weightedTotalDegree residualYSWeights F := by
  apply (weightedTotalDegree_le_iff3 geometricYRWeights (surfaceMap phi F) _).mpr
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_surfaceMap_subset phi F he)
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [geometricYR_weight]
  rw [residualYS_weight] at h
  change d (1 : Fin 4) + d (2 : Fin 4) ≤ _
  exact h

theorem surfaceMap_geometricTotal_le_original
    (phi : Polynomial K →+* Omega) (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.weightedTotalDegree geometricTotalWeights (surfaceMap phi F) ≤
      MvPolynomial.weightedTotalDegree residualTotalWeights F := by
  apply (weightedTotalDegree_le_iff3 geometricTotalWeights (surfaceMap phi F) _).mpr
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_surfaceMap_subset phi F he)
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [geometricTotal_weight]
  rw [residualTotal_weight] at h
  change d (1 : Fin 4) + d (2 : Fin 4) + d (3 : Fin 4) ≤ _
  exact h

/-- The actual normalized geometric factors consume no more of any raw facet
than their original factor. -/
theorem geometricFactor_raw_budgets
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) :
    (∑ g : GeometricFactor K F, geometricRawR K g) ≤
        MvPolynomial.weightedTotalDegree residualSWeights F ∧
      (∑ g : GeometricFactor K F, geometricRawYR K g) ≤
        MvPolynomial.weightedTotalDegree residualYSWeights F ∧
      (∑ g : GeometricFactor K F, geometricRawTotal K g) ≤
        MvPolynomial.weightedTotalDegree residualTotalWeights F := by
  classical
  let phi := polynomialEmbedding K
  have hmap : surfaceMap phi F ≠ 0 :=
    surfaceMap_ne_zero phi (polynomialEmbedding_injective K) F hF
  have hdiv := normalizedFactorSet_product_dvd (surfaceMap phi F) hmap
  have hR := sum_trivariate_weighted_degrees_le_of_prod_dvd geometricRWeights
    (surfaceFactors phi F) id (surfaceMap phi F) hmap hdiv
  have hYR := sum_trivariate_weighted_degrees_le_of_prod_dvd geometricYRWeights
    (surfaceFactors phi F) id (surfaceMap phi F) hmap hdiv
  have hTotal := sum_trivariate_weighted_degrees_le_of_prod_dvd geometricTotalWeights
    (surfaceFactors phi F) id (surfaceMap phi F) hmap hdiv
  simp only [geometricRawR, geometricRawYR, geometricRawTotal,
    Finset.sum_coe_sort]
  exact ⟨hR.trans (surfaceMap_geometricR_le_original phi F),
    hYR.trans (surfaceMap_geometricYR_le_original phi F),
    hTotal.trans (surfaceMap_geometricTotal_le_original phi F)⟩

/-- This is the exact consumer seam: geometric recursive counts stated in
their sharp flags aggregate to the sharp flag of the containing actual
positive-`R` factor. -/
theorem original_regular_seed_bound_of_sharp_geometric_factor_counts
    (Q : MvPolynomial (Fin 4) K) (R : RegularIndex Q)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hsolutions : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma R.1 = 0)
    (hcount : ∀ g : GeometricFactor K R.1,
      (geometricSeeds K R.1 selected Gamma g).card * gap ^ 2 ≤
        factorRegularLedger (sharpGeometricFlag K g)) :
    Gamma.card * gap ^ 2 ≤
      factorRegularLedger (sharpRegularFlag Q R) := by
  have hRdata := positiveRFactors_spec Q R.1 R.2
  have hcover := card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero
    selected Gamma hsolutions
  have hcaps := geometricFactor_raw_budgets R.1 hRdata.1.ne_zero
  calc
    Gamma.card * gap ^ 2 ≤
        (∑ g : GeometricFactor K R.1,
          (geometricSeeds K R.1 selected Gamma g).card) * gap ^ 2 :=
      Nat.mul_le_mul_right _ hcover
    _ = ∑ g : GeometricFactor K R.1,
        (geometricSeeds K R.1 selected Gamma g).card * gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K R.1,
        factorRegularLedger (sharpGeometricFlag K g) :=
      Finset.sum_le_sum (fun g _ ↦ hcount g)
    _ ≤ rawFactorLedger (factorRawR Q R) (factorRawYR Q R)
        (factorRawTotal Q R) :=
      sum_factorRegularLedger_sharp_le_raw_cap
        (fun g : GeometricFactor K R.1 ↦ geometricRawR K g)
        (fun g : GeometricFactor K R.1 ↦ geometricRawYR K g)
        (fun g : GeometricFactor K R.1 ↦ geometricRawTotal K g)
        (fun g : GeometricFactor K R.1 ↦ sharpGeometricFlag K g)
        (fun _ ↦ rfl)
        (fun g ↦ geometricRawR_le_geometricRawYR R.1 g)
        (fun g ↦ geometricRawYR_le_geometricRawTotal R.1 g)
        (factorRawR Q R) (factorRawYR Q R) (factorRawTotal Q R)
        hcaps.1 hcaps.2.1 hcaps.2.2
    _ = factorRegularLedger (sharpRegularFlag Q R) :=
      (factorRegularLedger_sharp_eq_raw Q R).symm

end

end ProximityPrize.SubmissionLower.ContactSharpFactorAggregationPost6600Research

#print axioms ProximityPrize.SubmissionLower.ContactSharpFactorAggregationPost6600Research.surfaceMap_in_sharpRegularFlag
#print axioms ProximityPrize.SubmissionLower.ContactSharpFactorAggregationPost6600Research.positiveRFactor_raw_budgets
#print axioms ProximityPrize.SubmissionLower.ContactSharpFactorAggregationPost6600Research.factorRegularLedger_sharp_eq_raw
#print axioms ProximityPrize.SubmissionLower.ContactSharpFactorAggregationPost6600Research.sum_actual_sharp_factorRegularLedger_le
#print axioms ProximityPrize.SubmissionLower.ContactSharpFactorAggregationPost6600Research.polynomialIn_sharpGeometricFlag
#print axioms ProximityPrize.SubmissionLower.ContactSharpFactorAggregationPost6600Research.geometricFactor_raw_budgets
#print axioms ProximityPrize.SubmissionLower.ContactSharpFactorAggregationPost6600Research.original_regular_seed_bound_of_sharp_geometric_factor_counts
