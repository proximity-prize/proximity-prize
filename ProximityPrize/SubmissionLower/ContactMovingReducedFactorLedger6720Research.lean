import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingReducedPositiveLedger6720Research
import ProximityPrize.SubmissionLower.ContactMovingFactorLedger6719Research

/-! # Factor ledger for reduced-static/moving-sharp cuts -/

namespace ProximityPrize.SubmissionLower.ContactMovingReducedFactorLedger6720Research

open scoped Classical BigOperators
open ContactFlagBezout6543Research ContactRobustFixedMeet6656Research
open ContactGCDCumulativeFlagsResearch ContactResidualSupportParametersResearch
open ContactOriginalRegularSeedCount ContactRegularFactorFlag6600Research
open ContactTranslation
open ContactMovingReducedPositiveLedger6720Research

noncomputable section
set_option maxHeartbeats 2000000

def factorDegreeCost (p : Profile) (support : ResidualSupportParameters)
    (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  p.degreeIncidence * degreeSlope support a b s flag +
    p.unitIncidence * unitSlope support a b s flag +
    (p.errors + 1) * p.gap * (zSlope support flag + yzSlope support flag)

def factorUnitCost (p : Profile) (support : ResidualSupportParameters)
    (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  p.degreeIncidence * degreeBase a b s flag +
    p.unitIncidence * unitBase a b s flag +
    (p.errors + 1) * p.gap * (zBase flag + yzBase flag)

def regularLedger (p : Profile) (support : ResidualSupportParameters)
    (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  p.degreeIncidence * factorDegreeCost p support a b s flag +
    p.unitIncidence * factorUnitCost p support a b s flag

theorem terminal_affine (p : Profile) (support : ResidualSupportParameters)
    (a b s d : ℕ) (flag : FlagDegree) :
    p.degreeIncidence *
        (ContactMovingPositiveLedger6719Research.weightedMixed flag
            (reducedCut support d)
            (ContactMovingPositiveLedger6719Research.normalFlag a b s) +
          flagMixed flag
            (ContactMovingPositiveLedger6719Research.fiberFlag a b s)
            (ContactMovingPositiveLedger6719Research.centreFlag a b s +
              d • ContactMovingPositiveLedger6719Research.surfaceFlag a b s)) +
      p.unitIncidence *
        ContactMovingPositiveLedger6719Research.weightedMixed flag
          (reducedCut support d)
          (ContactMovingPositiveLedger6719Research.centreFlag a b s) +
      (p.errors + 1) * p.gap *
        (flagMixed flag (reducedCut support d) unitZFlag +
          flagMixed flag (reducedCut support d) unitYZFlag) =
      d * factorDegreeCost p support a b s flag +
        factorUnitCost p support a b s flag := by
  rw [degree_affine, unit_affine, z_affine, yz_affine]
  simp only [factorDegreeCost, factorUnitCost]
  ring

theorem regularLedger_expanded (p : Profile)
    (support : ResidualSupportParameters) (a b s : ℕ) (flag : FlagDegree) :
    regularLedger p support a b s flag =
      degreeSlope support a b s flag * p.degreeIncidence ^ 2 +
      (degreeBase a b s flag + unitSlope support a b s flag) *
        p.degreeIncidence * p.unitIncidence +
      unitBase a b s flag * p.unitIncidence ^ 2 +
      (p.errors + 1) * p.gap *
        (zSlope support flag * p.degreeIncidence + zBase flag * p.unitIncidence) +
      (p.errors + 1) * p.gap *
        (yzSlope support flag * p.degreeIncidence + yzBase flag * p.unitIncidence) := by
  simp only [regularLedger, factorDegreeCost, factorUnitCost]
  ring

theorem sum_regularLedger_le {I : Type*} [Fintype I]
    (p : Profile) (support : ResidualSupportParameters) (a b s : ℕ)
    (flags : I → FlagDegree) (cap : FlagDegree)
    (hi : (∑ i, (flags i).all) ≤ cap.all)
    (hm : (∑ i, ((flags i).yz + (flags i).all)) ≤ cap.yz + cap.all)
    (ht : (∑ i, ((flags i).zOnly + (flags i).yz + (flags i).all)) ≤
      cap.zOnly + cap.yz + cap.all) :
    (∑ i, regularLedger p support a b s (flags i)) ≤
      regularLedger p support a b s cap := by
  simp only [regularLedger, factorDegreeCost, factorUnitCost,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  gcongr
  all_goals first
    | exact sum_degreeSlope_le flags cap hi hm ht support a b s
    | exact sum_degreeBase_le flags cap hi hm ht a b s
    | exact sum_unitSlope_le flags cap hi hm ht support a b s
    | exact sum_unitBase_le flags cap hi hm ht a b s
    | exact sum_zSlope_le flags cap hi hm ht support
    | exact sum_yzSlope_le flags cap hi hm ht support
    | exact sum_zBase_le flags cap hi hm ht
    | exact sum_yzBase_le flags cap hi hm ht

variable {K : Type} [Field K]

theorem sum_regular_counts_le
    (p : Profile) (support : ResidualSupportParameters) (a b s : ℕ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {box : ResidualSupportParameters} (H : ResidualSupportData box Q)
    (count : RegularIndex Q → ℕ)
    (hcount : ∀ R, count R * p.gap ^ 2 ≤
      regularLedger p support a b s (regularCumulativeFlag Q R)) :
    (∑ R, count R) * p.gap ^ 2 ≤
      regularLedger p support a b s (supportCumulativeFlag box) := by
  have hc := regularCumulativeFlag_budgets Q hQ H
  have hp := flagFromCaps_cumulative box.total box.ys box.s
    box.s_le_ys box.ys_le_total
  calc
    _ = ∑ R, count R * p.gap ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ∑ R, regularLedger p support a b s (regularCumulativeFlag Q R) :=
      Finset.sum_le_sum (fun R _ ↦ hcount R)
    _ ≤ _ := sum_regularLedger_le p support a b s (regularCumulativeFlag Q)
      (supportCumulativeFlag box)
      (by simpa only [supportCumulativeFlag, hp.1] using hc.1)
      (by simpa only [supportCumulativeFlag, hp.2.1] using hc.2.1)
      (by simpa only [supportCumulativeFlag, hp.2.2] using hc.2.2)

theorem geometric_seed_counts_le
    (p : Profile) (support : ResidualSupportParameters) (a b s : ℕ)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (selected : K → Polynomial K) (Γ : Finset K)
    (hsolutions : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hcount : ∀ g : GeometricFactor K F,
      (geometricSeeds K F selected Γ g).card * p.gap ^ 2 ≤
        regularLedger p support a b s (geometricCumulativeFlag K g)) :
    Γ.card * p.gap ^ 2 ≤
      regularLedger p support a b s (originalCumulativeFlag F) := by
  have hc := geometricCumulativeFlag_budgets F hF
  calc
    _ ≤ (∑ g : GeometricFactor K F,
        (geometricSeeds K F selected Γ g).card) * p.gap ^ 2 :=
      Nat.mul_le_mul_right _ (card_le_sum_geometricSeeds K F hF selected Γ hsolutions)
    _ = ∑ g : GeometricFactor K F,
        (geometricSeeds K F selected Γ g).card * p.gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K F,
        regularLedger p support a b s (geometricCumulativeFlag K g) :=
      Finset.sum_le_sum (fun g _ ↦ hcount g)
    _ ≤ _ := sum_regularLedger_le p support a b s (geometricCumulativeFlag K)
      (originalCumulativeFlag F) hc.1 hc.2.1 hc.2.2

end

end ProximityPrize.SubmissionLower.ContactMovingReducedFactorLedger6720Research
