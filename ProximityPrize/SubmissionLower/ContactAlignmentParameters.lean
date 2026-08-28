import ProximityPrize.Benchmark.TargetLower

/-!
# Exact arithmetic for the direct-contact alignment candidate

Model label: gpt-5.

The definitions below evaluate the actual coefficient and local-contact-rank
formulas, followed by the conservative mixed-degree ledger. They do not assert
the interpolation rank theorem, the polynomiality-locus theorem, or mixed
Bezout. Those mathematical obligations remain separate. In particular this
module is not itself a ProtocolClaim or a complete competition submission.

Only ordinary kernel-checked tactics are used; no native evaluation axiom is
introduced. Compile on the authorized remote backend, never locally.
-/

namespace ProximityPrize.SubmissionLower.ContactAlignmentParameters

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def n : ℕ := 262144
def w : ℕ := 131071
def agreements : ℕ := 184465
def prime : ℕ := 2130706433
def errors : ℕ := n - agreements
def alignmentBudget : ℕ := 100000000000000000
def multiplicity : ℕ := 19
def seedTotalCap : ℕ := 170
def slopeCap : ℕ := 6
def weightedCap : ℕ := multiplicity * agreements
def yCap : ℕ := (weightedCap - 1) / w
def gap : ℕ := agreements - w
def algebraicCap : ℕ := (2 * slopeCap - 1) * seedTotalCap

/-- The specialized coefficient support additionally satisfies `i + j + z ≤ L`.
Nat subtraction is the positive part of each strict weighted cap. -/
def coefficientCount : ℕ :=
  ∑ i ∈ range (seedTotalCap + 1),
    ∑ j ∈ range (slopeCap + 1),
      (seedTotalCap + 1 - i - j) *
        (weightedCap - w * i - (w - 1) * j)

def contactExponent (r : ℕ) : ℕ := min (r + 1) (multiplicity - r)

/-- The local source has `y ≤ M`, `y + r + z ≤ L`, and `r ≤ s`.
The certified kernel quotient has the three caps reduced by the contact
exponent. Writing the range lengths with subtraction after `+1` makes the
quotient empty whenever that exponent exceeds an available cap. -/
def localContactRank : ℕ :=
  ∑ r ∈ range multiplicity,
    ((∑ f ∈ range (min r seedTotalCap + 1),
        ∑ j ∈ range (slopeCap + 1),
          (seedTotalCap + 1 - f - j)) -
      (∑ f ∈ range (min r seedTotalCap + 1 - contactExponent r),
        ∑ j ∈ range (slopeCap + 1 - contactExponent r),
          (seedTotalCap + 1 - contactExponent r - f - j)))

structure DegreeVector where
  y : ℕ
  r : ℕ
  z : ℕ
  deriving DecidableEq

/-- The coefficient of the product of three distinct hyperplane classes. -/
def mixed (a b c : DegreeVector) : ℕ :=
  a.y * b.r * c.z + a.y * b.z * c.r +
  a.r * b.y * c.z + a.r * b.z * c.y +
  a.z * b.y * c.r + a.z * b.r * c.y

def unitY : DegreeVector := ⟨1, 0, 0⟩
def unitR : DegreeVector := ⟨0, 1, 0⟩
def unitZ : DegreeVector := ⟨0, 0, 1⟩

def tailVector (h : ℕ) : DegreeVector :=
  ⟨1 + 2 * h * yCap, h * (2 * slopeCap - 1), 2 * h * seedTotalCap⟩

def firstTail : DegreeVector := tailVector (w + 1)
def lastTail : DegreeVector := tailVector weightedCap
def agreementVector : DegreeVector :=
  ⟨1 + w * (2 * yCap - 1), w * (2 * slopeCap - 1), 2 * w * seedTotalCap + 1⟩

/-- Numerator of the early-cut branch over the common denominator `gap^2`. -/
def cutNumerator (v : DegreeVector) : ℕ :=
  gap ^ 2 * mixed v firstTail lastTail +
  n * gap * mixed v firstTail agreementVector +
  (errors + 1) * gap ^ 2 * mixed v firstTail unitZ

/-- Numerator of the whole-polynomial-surface branch over `gap^2`. -/
def wholeNumerator (v : DegreeVector) : ℕ :=
  (n - w) ^ 2 * mixed v agreementVector agreementVector +
  (errors + 1) * (n - w) * gap * mixed v agreementVector unitZ

def regularNumerator : ℕ :=
  yCap * wholeNumerator unitY +
  slopeCap * wholeNumerator unitR +
  seedTotalCap * wholeNumerator unitZ

/-- Numerator of the algebraic/singular branch over `gap`. -/
def singularNumerator : ℕ :=
  gap * (algebraicCap + 2 * algebraicCap ^ 2 +
      algebraicCap * (1 + 2 * (w + 1) * (algebraicCap - 1)) +
      (errors + 1) * algebraicCap) +
    n * algebraicCap * (1 + 2 * w * (algebraicCap - 1))

def totalNumerator : ℕ := regularNumerator + gap * singularNumerator

theorem parameter_values :
    weightedCap = 3504835 ∧ yCap = 26 ∧ gap = 53394 ∧
    errors = 77679 ∧ algebraicCap = 1870 := by
  norm_num [weightedCap, multiplicity, agreements, yCap, w, gap, errors,
    n, algebraicCap, slopeCap, seedTotalCap]

theorem coefficient_count_exact : coefficientCount = 43589272650 := by
  norm_num [coefficientCount, seedTotalCap, slopeCap, weightedCap,
    multiplicity, agreements, w, Finset.sum_range_succ]

theorem contact_rank_exact : localContactRank = 166278 := by
  norm_num [localContactRank, contactExponent, multiplicity, seedTotalCap,
    slopeCap, Finset.sum_range_succ]

theorem interpolation_gate : n * localContactRank < coefficientCount := by
  rw [coefficient_count_exact, contact_rank_exact]
  norm_num [n]

theorem characteristic_gates :
    w < weightedCap ∧ (2 * slopeCap - 1) * weightedCap < prime ∧
    algebraicCap < prime ∧ slopeCap < prime := by
  norm_num [w, weightedCap, multiplicity, agreements, slopeCap, prime,
    algebraicCap, seedTotalCap]

theorem branch_dominance :
    wholeNumerator unitY ≤ cutNumerator unitY ∧
    wholeNumerator unitR ≤ cutNumerator unitR ∧
    wholeNumerator unitZ ≤ cutNumerator unitZ := by
  norm_num [wholeNumerator, cutNumerator, unitY, unitR, unitZ, mixed,
    firstTail, lastTail, tailVector, agreementVector, yCap, weightedCap,
    multiplicity, agreements, w, gap, n, errors, slopeCap, seedTotalCap]

theorem ledger_numerator_exact :
    totalNumerator = 175168892304488157872254404 := by
  norm_num [totalNumerator, regularNumerator, singularNumerator,
    wholeNumerator, cutNumerator, unitY, unitR, unitZ, mixed,
    firstTail, lastTail, tailVector, agreementVector, yCap, weightedCap,
    multiplicity, agreements, w, gap, n, errors, slopeCap, seedTotalCap,
    algebraicCap]

theorem denominator_exact : gap ^ 2 = 2850919236 := by
  norm_num [gap, agreements, w]

theorem division_certificate :
    totalNumerator = 61442951484749867 * gap ^ 2 + 1393512792 ∧
    1393512792 < gap ^ 2 := by
  rw [ledger_numerator_exact, denominator_exact]
  norm_num

theorem strict_ledger_budget : totalNumerator < alignmentBudget * gap ^ 2 := by
  rw [ledger_numerator_exact, denominator_exact]
  norm_num [alignmentBudget]

/-- This arithmetic finish retains the missing geometric cardinal estimate
as an explicit hypothesis. It is not a proof of that estimate. -/
theorem below_budget_of_scaled_cardinality_bound
    (cardinality : ℕ) (h : cardinality * gap ^ 2 ≤ totalNumerator) :
    cardinality < alignmentBudget := by
  have hstrict := h.trans_lt strict_ledger_budget
  rw [denominator_exact] at hstrict
  exact Nat.lt_of_mul_lt_mul_right hstrict

end ProximityPrize.SubmissionLower.ContactAlignmentParameters

#print axioms ProximityPrize.SubmissionLower.ContactAlignmentParameters.coefficient_count_exact
#print axioms ProximityPrize.SubmissionLower.ContactAlignmentParameters.contact_rank_exact
#print axioms ProximityPrize.SubmissionLower.ContactAlignmentParameters.interpolation_gate
#print axioms ProximityPrize.SubmissionLower.ContactAlignmentParameters.ledger_numerator_exact
#print axioms ProximityPrize.SubmissionLower.ContactAlignmentParameters.strict_ledger_budget
#print axioms ProximityPrize.SubmissionLower.ContactAlignmentParameters.below_budget_of_scaled_cardinality_bound
