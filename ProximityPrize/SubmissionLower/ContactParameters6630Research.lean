import ProximityPrize.Benchmark.TargetLower

/-!
# Exact flag-complete interpolation parameters for the 66.74 row

This module freezes `(errors,m,s,L) = (79514,35,10,814)` and checks the
coefficient count and translated contact rank from their defining finite
sums.  It contains no geometric or decoding premise.
-/

namespace ProximityPrize.SubmissionLower.ContactParameters6630Research

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def alignmentBudget : ℕ := 274980727761395087

def errors : ℕ := 79514
def agreements : ℕ := n - errors
def multiplicity : ℕ := 35
def seedTotalCap : ℕ := 814
def slopeCap : ℕ := 10
def weightedCap : ℕ := multiplicity * agreements
def yCap : ℕ := (weightedCap - 1) / w
def gap : ℕ := agreements - w
def algebraicCap : ℕ := (2 * slopeCap - 1) * seedTotalCap
def implicitWeightedCap : ℕ := (2 * slopeCap - 1) * weightedCap
def implicitYCap : ℕ := (implicitWeightedCap - 1) / w

/-- Number of monomials in the strict weighted interpolation box. -/
def coefficientCount : ℕ :=
  ∑ i ∈ range (seedTotalCap + 1),
    ∑ j ∈ range (slopeCap + 1),
      (seedTotalCap + 1 - i - j) *
        (weightedCap - w * i - (w - 1) * j)

def contactExponent (r : ℕ) : ℕ := min (r + 1) (multiplicity - r)

/-- Exact rank bound of one translated order-`multiplicity` contact block. -/
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
    agreements = 182630 ∧ weightedCap = 6392050 ∧ yCap = 48 ∧
    gap = 51559 ∧ algebraicCap = 15466 ∧
    implicitWeightedCap = 121448950 ∧ implicitYCap = 926 := by
  norm_num [agreements, n, errors, weightedCap, multiplicity, yCap, w,
    gap, algebraicCap, slopeCap, seedTotalCap, implicitWeightedCap,
    implicitYCap]

theorem coefficient_count_exact : coefficientCount = 1130256329994 := by
  norm_num [coefficientCount, seedTotalCap, slopeCap, weightedCap,
    multiplicity, agreements, n, errors, w, Finset.sum_range_succ]

theorem local_contact_rank_exact : localContactRank = 4311560 := by
  norm_num [localContactRank, contactExponent, multiplicity, seedTotalCap,
    slopeCap, Finset.sum_range_succ]

theorem total_contact_rank_exact : totalContactRank = 1130249584640 := by
  rw [show totalContactRank = n * localContactRank by rfl,
    local_contact_rank_exact]
  norm_num [n]

theorem rank_margin_exact : rankMargin = 6745354 := by
  rw [show rankMargin = coefficientCount - totalContactRank by rfl,
    coefficient_count_exact, total_contact_rank_exact]

theorem interpolation_gate : totalContactRank < coefficientCount := by
  rw [coefficient_count_exact, total_contact_rank_exact]
  norm_num

theorem characteristic_gates :
    weightedCap < prime ∧ implicitWeightedCap < prime ∧
      algebraicCap < prime ∧ slopeCap < prime := by
  norm_num [weightedCap, multiplicity, agreements, n, errors,
    implicitWeightedCap, algebraicCap, slopeCap, seedTotalCap, prime]

end ProximityPrize.SubmissionLower.ContactParameters6630Research
