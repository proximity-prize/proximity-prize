import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRegularFactorFlag6600Research

/-! .












 -/

namespace ProximityPrize.SubmissionLower.ContactRobustFixedMeet6656Research

open scoped BigOperators
open ContactInterpolation ContactSelectedSeedDecomposition
open ContactFlagBezout6543Research
open ContactRegularFactorFlag6600Research

set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

/-- . -/
structure Profile where
  n : ℕ
  w : ℕ
  agreements : ℕ
  weightedCap : ℕ
  seedTotalCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq, Repr

namespace Profile

def errors (p : Profile) : ℕ := p.n - p.agreements
def gap (p : Profile) : ℕ := p.agreements - p.w
def yCap (p : Profile) : ℕ := (p.weightedCap - 1) / p.w

def degreeIncidence (p : Profile) : ℕ :=
  (p.n * p.gap * p.w + p.agreements - 1) / p.agreements

def unitIncidence (p : Profile) : ℕ := p.n - p.w

/-- . -/
def surfaceFlag (p : Profile) : FlagDegree :=
  ⟨p.seedTotalCap + p.slopeCap - p.yCap,
    p.yCap - p.slopeCap, p.slopeCap⟩

def derivativeFlag (p : Profile) : FlagDegree :=
  ⟨p.surfaceFlag.zOnly, p.surfaceFlag.yz, p.surfaceFlag.all - 1⟩

def agreementDirection (p : Profile) : FlagDegree :=
  p.surfaceFlag + p.derivativeFlag

/-- .
 -/
def rectangularSurfaceFlag (p : Profile) : FlagDegree :=
  ⟨p.seedTotalCap, p.yCap, p.slopeCap⟩

def factorPrimary (p : Profile) (flag : FlagDegree) : ℕ :=
  flagMixed flag p.agreementDirection p.agreementDirection * p.degreeIncidence ^ 2 +
    2 * flagMixed flag p.agreementDirection unitYZFlag *
      p.degreeIncidence * p.unitIncidence +
    flagMixed flag unitYZFlag unitYZFlag * p.unitIncidence ^ 2

def factorZTail (p : Profile) (flag : FlagDegree) : ℕ :=
  (p.errors + 1) * p.gap *
    (flagMixed flag p.agreementDirection unitZFlag * p.degreeIncidence +
      flagMixed flag unitYZFlag unitZFlag * p.unitIncidence)

def factorAllTail (p : Profile) (flag : FlagDegree) : ℕ :=
  (p.errors + 1) * p.gap *
    (flagMixed flag p.agreementDirection unitAllFlag * p.degreeIncidence +
      flagMixed flag unitYZFlag unitAllFlag * p.unitIncidence)

def factorRegularLedger (p : Profile) (flag : FlagDegree) : ℕ :=
  p.factorPrimary flag + p.factorZTail flag + p.factorAllTail flag

def regularNumerator (p : Profile) : ℕ :=
  p.factorRegularLedger p.rectangularSurfaceFlag

structure DegreeVector where
  y : ℕ
  r : ℕ
  z : ℕ
  deriving DecidableEq, Repr

def mixed (a b c : DegreeVector) : ℕ :=
  a.y * b.r * c.z + a.y * b.z * c.r +
    a.r * b.y * c.z + a.r * b.z * c.y +
    a.z * b.y * c.r + a.z * b.r * c.y

def algebraicCap (p : Profile) : ℕ :=
  (2 * p.slopeCap - 1) * p.seedTotalCap

def implicitWeightedCap (p : Profile) : ℕ :=
  (2 * p.slopeCap - 1) * p.weightedCap

def implicitYCap (p : Profile) : ℕ :=
  (p.implicitWeightedCap - 1) / p.w

def liftedSurface (p : Profile) : DegreeVector :=
  ⟨p.implicitYCap, 1, p.algebraicCap⟩

def implicitCut (p : Profile) : DegreeVector :=
  ⟨p.implicitYCap, 0, p.algebraicCap⟩

def liftedLast (p : Profile) : DegreeVector :=
  ⟨1 + 2 * p.implicitWeightedCap * p.implicitYCap,
    p.implicitWeightedCap,
    2 * p.implicitWeightedCap * p.algebraicCap⟩

def liftedAgreement (p : Profile) : DegreeVector :=
  ⟨1 + 2 * p.w * p.implicitYCap,
    p.w, 2 * p.w * p.algebraicCap + 1⟩

def unitZ : DegreeVector := ⟨0, 0, 1⟩

/-- .
 -/
def retainedSingularContribution (p : Profile) : ℕ :=
  p.gap *
    (p.gap *
      (p.algebraicCap + 2 * p.algebraicCap ^ 2 +
        mixed p.liftedSurface p.implicitCut p.liftedLast +
        (p.errors + 1) * mixed p.liftedSurface p.implicitCut unitZ) +
      (p.n - p.w) *
        mixed p.liftedSurface p.implicitCut p.liftedAgreement)

def totalNumerator (p : Profile) : ℕ :=
  p.regularNumerator + p.retainedSingularContribution

def fixedCost (p : Profile) : ℕ :=
  (p.totalNumerator + p.gap ^ 2 - 1) / p.gap ^ 2

end Profile

/-- . -/
theorem factorRegularLedger_projection_decomposition
    (p : Profile) (flag : FlagDegree) :
    p.factorRegularLedger flag =
      flag.zOnly * p.factorRegularLedger unitZFlag +
      flag.yz * p.factorRegularLedger unitYZFlag +
      flag.all * p.factorRegularLedger unitAllFlag := by
  cases flag
  simp [Profile.factorRegularLedger, Profile.factorPrimary,
    Profile.factorZTail, Profile.factorAllTail, flagMixed,
    unitZFlag, unitYZFlag, unitAllFlag]
  ring

/-- .
 -/
theorem sum_factorRegularLedger_le_flag
    {I : Type} [Fintype I] (p : Profile)
    (flag : I → FlagDegree) (cap : FlagDegree)
    (hz : (∑ i, (flag i).zOnly) ≤ cap.zOnly)
    (hyz : (∑ i, (flag i).yz) ≤ cap.yz)
    (hall : (∑ i, (flag i).all) ≤ cap.all) :
    (∑ i, p.factorRegularLedger (flag i)) ≤
      p.factorRegularLedger cap := by
  classical
  calc
    (∑ i, p.factorRegularLedger (flag i)) =
        ∑ i, ((flag i).zOnly * p.factorRegularLedger unitZFlag +
          (flag i).yz * p.factorRegularLedger unitYZFlag +
          (flag i).all * p.factorRegularLedger unitAllFlag) := by
      apply Finset.sum_congr rfl
      intro i _
      exact factorRegularLedger_projection_decomposition p (flag i)
    _ = (∑ i, (flag i).zOnly) * p.factorRegularLedger unitZFlag +
        (∑ i, (flag i).yz) * p.factorRegularLedger unitYZFlag +
        (∑ i, (flag i).all) * p.factorRegularLedger unitAllFlag := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ cap.zOnly * p.factorRegularLedger unitZFlag +
        cap.yz * p.factorRegularLedger unitYZFlag +
        cap.all * p.factorRegularLedger unitAllFlag :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ hz)
          (Nat.mul_le_mul_right _ hyz))
        (Nat.mul_le_mul_right _ hall)
    _ = p.factorRegularLedger cap :=
      (factorRegularLedger_projection_decomposition p cap).symm

noncomputable section

variable {K : Type} [Field K]

/-- .
 -/
theorem regularFlag_budgets
    (p : Profile) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hw : 0 < p.w)
    (hbox : Q ∈ globalCoefficientBox K p.weightedCap p.w
      p.seedTotalCap p.slopeCap) :
    (∑ F : RegularIndex Q, (regularFlag Q F).zOnly) ≤ p.seedTotalCap ∧
      (∑ F : RegularIndex Q, (regularFlag Q F).yz) ≤ p.yCap ∧
      (∑ F : RegularIndex Q, (regularFlag Q F).all) ≤ p.slopeCap := by
  classical
  have hb := directFactor_input_budgets Q hQ p.weightedCap p.w
    p.seedTotalCap p.slopeCap hw hbox
  simp only [regularFlag, Finset.sum_coe_sort]
  exact ⟨hb.2.2, hb.1, hb.2.1⟩

/-- .

 -/
theorem sum_factor_counts_rectangular_le
    (p : Profile) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hw : 0 < p.w)
    (hbox : Q ∈ globalCoefficientBox K p.weightedCap p.w
      p.seedTotalCap p.slopeCap)
    (count : RegularIndex Q → ℕ)
    (hcount : ∀ F, count F * p.gap ^ 2 ≤
      p.factorRegularLedger (regularFlag Q F)) :
    (∑ F, count F) * p.gap ^ 2 ≤ p.regularNumerator := by
  have hcaps := regularFlag_budgets p Q hQ hw hbox
  calc
    (∑ F, count F) * p.gap ^ 2 = ∑ F, count F * p.gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ F, p.factorRegularLedger (regularFlag Q F) :=
      Finset.sum_le_sum (fun F _ ↦ hcount F)
    _ ≤ p.factorRegularLedger p.rectangularSurfaceFlag :=
      sum_factorRegularLedger_le_flag p (regularFlag Q)
        p.rectangularSurfaceFlag hcaps.1 hcaps.2.1 hcaps.2.2
    _ = p.regularNumerator := rfl

end

/-- . -/
theorem combined_fixed_scaled_bound
    (p : Profile) (regularCount singularCount : ℕ)
    (hregular : regularCount * p.gap ^ 2 ≤ p.regularNumerator)
    (hsingular : singularCount * p.gap ^ 2 ≤
      p.retainedSingularContribution) :
    (regularCount + singularCount) * p.gap ^ 2 ≤ p.totalNumerator := by
  calc
    (regularCount + singularCount) * p.gap ^ 2 =
        regularCount * p.gap ^ 2 + singularCount * p.gap ^ 2 := by ring
    _ ≤ p.regularNumerator + p.retainedSingularContribution :=
      Nat.add_le_add hregular hsingular
    _ = p.totalNumerator := rfl

/-- .
 -/
def meetProfile : Profile where
  n := 262144
  w := 131071
  agreements := 182807
  weightedCap := 4570175
  seedTotalCap := 598
  slopeCap := 6

theorem meet_parameter_values :
    meetProfile.errors = 79337 ∧ meetProfile.gap = 51736 ∧
      meetProfile.yCap = 34 ∧ meetProfile.degreeIncidence = 9724036071 ∧
      meetProfile.unitIncidence = 131073 ∧
      meetProfile.surfaceFlag = ⟨570, 28, 6⟩ ∧
      meetProfile.agreementDirection = ⟨1140, 56, 11⟩ ∧
      meetProfile.rectangularSurfaceFlag = ⟨598, 34, 6⟩ := by
  norm_num [meetProfile, Profile.errors, Profile.gap, Profile.yCap,
    Profile.degreeIncidence, Profile.unitIncidence, Profile.surfaceFlag,
    Profile.derivativeFlag, Profile.agreementDirection,
    Profile.rectangularSurfaceFlag] <;> rfl

theorem meet_regular_numerator_exact :
    meetProfile.regularNumerator = 254256809306954333411326320 := by
  norm_num [Profile.regularNumerator, Profile.factorRegularLedger,
    Profile.factorPrimary, Profile.factorZTail, Profile.factorAllTail,
    Profile.rectangularSurfaceFlag, Profile.agreementDirection,
    Profile.derivativeFlag, Profile.surfaceFlag, Profile.degreeIncidence,
    Profile.unitIncidence, Profile.errors, Profile.gap, Profile.yCap,
    meetProfile, flagMixed, unitZFlag, unitYZFlag, unitAllFlag]

theorem meet_singular_contribution_exact :
    meetProfile.retainedSingularContribution =
      2047455364091186323290168 := by
  norm_num [Profile.retainedSingularContribution, Profile.mixed,
    Profile.liftedSurface, Profile.implicitCut, Profile.liftedLast,
    Profile.liftedAgreement, Profile.unitZ, Profile.algebraicCap,
    Profile.implicitWeightedCap, Profile.implicitYCap,
    Profile.errors, Profile.gap, meetProfile]

theorem meet_total_numerator_exact :
    meetProfile.totalNumerator = 256304264671045519734616488 := by
  rw [show meetProfile.totalNumerator = meetProfile.regularNumerator +
      meetProfile.retainedSingularContribution by rfl,
    meet_regular_numerator_exact, meet_singular_contribution_exact]

theorem meet_fixed_cost_exact :
    meetProfile.fixedCost = 95756912943422943 := by
  rw [show meetProfile.fixedCost =
      (meetProfile.totalNumerator + meetProfile.gap ^ 2 - 1) /
        meetProfile.gap ^ 2 by rfl,
    meet_total_numerator_exact]
  norm_num [Profile.gap, meetProfile]

theorem meet_fixed_cost_lt_budget :
    meetProfile.fixedCost < 100000000000000000 := by
  rw [meet_fixed_cost_exact]
  norm_num

end ProximityPrize.SubmissionLower.ContactRobustFixedMeet6656Research
