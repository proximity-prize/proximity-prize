import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagParameters6641Research

/-! # Shared score-66.75 row for the downstream geometry

The local definitions remain transparent for downstream arithmetic.  Exact
finite-sum certificates are shared with the identical flag-parameter row
instead of being expanded a second time.
-/

namespace ProximityPrize.SubmissionLower.ContactParameters6630Research

open Finset

set_option maxRecDepth 100000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def alignmentBudget : ℕ := 274980727751395087
def errors : ℕ := 79520
def agreements : ℕ := n - errors
def multiplicity : ℕ := 35
def seedTotalCap : ℕ := 825
def slopeCap : ℕ := 10
def weightedCap : ℕ := multiplicity * agreements
def yCap : ℕ := (weightedCap - 1) / w
def gap : ℕ := agreements - w
def algebraicCap : ℕ := (2 * slopeCap - 1) * seedTotalCap
def implicitWeightedCap : ℕ := (2 * slopeCap - 1) * weightedCap
def implicitYCap : ℕ := (implicitWeightedCap - 1) / w

def coefficientCount : ℕ :=
  ∑ i ∈ range (seedTotalCap + 1),
    ∑ j ∈ range (slopeCap + 1),
      (seedTotalCap + 1 - i - j) *
        (weightedCap - w * i - (w - 1) * j)

def contactExponent (r : ℕ) : ℕ := min (r + 1) (multiplicity - r)

def localContactRank : ℕ :=
  ∑ r ∈ range multiplicity,
    ((∑ f ∈ range (min r seedTotalCap + 1),
        ∑ j ∈ range (slopeCap + 1),
          (seedTotalCap + 1 - f - j)) -
      (∑ f ∈ range (min r seedTotalCap + 1 - contactExponent r),
        ∑ j ∈ range (slopeCap + 1 - contactExponent r),
          (seedTotalCap + 1 - contactExponent r - f - j)))

def totalContactRank : ℕ := n * localContactRank
def rankMargin : ℕ := coefficientCount - totalContactRank

structure DegreeVector where
  y : ℕ
  r : ℕ
  z : ℕ
  deriving DecidableEq

def mixed (a b c : DegreeVector) : ℕ :=
  a.y * b.r * c.z + a.y * b.z * c.r +
  a.r * b.y * c.z + a.r * b.z * c.y +
  a.z * b.y * c.r + a.z * b.r * c.y

def unitZ : DegreeVector := ⟨0, 0, 1⟩
def liftedSurface : DegreeVector := ⟨implicitYCap, 1, algebraicCap⟩
def implicitCut : DegreeVector := ⟨implicitYCap, 0, algebraicCap⟩
def liftedLast : DegreeVector :=
  ⟨1 + 2 * implicitWeightedCap * implicitYCap,
    implicitWeightedCap,
    2 * implicitWeightedCap * algebraicCap⟩
def liftedAgreement : DegreeVector :=
  ⟨1 + 2 * w * implicitYCap,
    w,
    2 * w * algebraicCap + 1⟩

theorem parameter_values :
    agreements = 182624 ∧ weightedCap = 6391840 ∧ yCap = 48 ∧
    gap = 51553 ∧ algebraicCap = 15675 ∧
    implicitWeightedCap = 121444960 ∧ implicitYCap = 926 :=
  ContactFlagParameters6641Research.parameter_values

theorem coefficient_count_exact : coefficientCount = 1145793371723 :=
  ContactFlagParameters6641Research.coefficient_count_exact

theorem local_contact_rank_exact : localContactRank = 4370850 :=
  ContactFlagParameters6641Research.local_contact_rank_exact

theorem total_contact_rank_exact : totalContactRank = 1145792102400 :=
  ContactFlagParameters6641Research.total_contact_rank_exact

theorem rank_margin_exact : rankMargin = 1269323 :=
  ContactFlagParameters6641Research.rank_margin_exact

theorem interpolation_gate : totalContactRank < coefficientCount :=
  ContactFlagParameters6641Research.interpolation_gate

theorem characteristic_gates :
    weightedCap < prime ∧ implicitWeightedCap < prime ∧
      algebraicCap < prime ∧ slopeCap < prime :=
  ContactFlagParameters6641Research.characteristic_gates

end ProximityPrize.SubmissionLower.ContactParameters6630Research
