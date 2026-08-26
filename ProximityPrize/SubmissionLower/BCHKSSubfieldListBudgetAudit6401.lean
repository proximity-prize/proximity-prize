import ProximityPrize.SubmissionLower.BCHKSParameters6401

/-!
# Subfield-evaluation list theorem and field-budget audit at score 64.01

Kumar--Ron-Zewi, ECCC TR26-032, Section 4.3 gives the following bound for
the *full* Reed--Solomon code over `F_(q^s)` evaluated at base-field points:
using `r` Frobenius terms, the output is an affine `F_q`-space of dimension
at most `(r-1)k`, hence has size at most `q^((r-1)k)`.

For the benchmark, `q=2130706433`, `s=6`, `n=262144`, and `k=131072`.
The first parameter that reaches `185354` agreements is `r=2`, so the
smallest theorem-level full-code bound is `q^131072`.  Even `q^2` already
exceeds the entire score-64.01 numerator budget.

Section 5.3 obtains constant lists only after replacing the full message
space by a periodic-evasive coefficient subspace.  The benchmark is the
unrestricted code, so that result is inapplicable without changing the
code.  The squared/interleaved code does not help: its sixteen extension
symbols can be packed `F_q`-linearly into one degree-96 extension symbol,
and the same full-code theorem still gives `q^131072`.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSSubfieldListBudgetAudit6401

def q6401 : Nat := 2130706433
def extensionDegree6401 : Nat := 6
def squaredInterleaving6401 : Nat := 2 * 8
def packedExtensionDegree6401 : Nat :=
  extensionDegree6401 * squaredInterleaving6401
def n6401 : Nat := 262144
def k6401 : Nat := 131072
def a6401 : Nat := 185354

/-- Integer agreement threshold for the `r=1` interpolation equation. -/
def r1AgreementThreshold6401 : Nat := 196608

/-- The `r=2` rectangle has substituted degree at most `174762`; hence this
is its strict integer agreement threshold. -/
def r2AgreementThreshold6401 : Nat := 174763

def smallestApplicableFrobeniusTerms6401 : Nat := 2
def fullCodeTheoremExponent6401 : Nat :=
  (smallestApplicableFrobeniusTerms6401 - 1) * k6401
def fullCodeTheoremListBound6401 : Nat :=
  q6401 ^ fullCodeTheoremExponent6401

/-- Exact numerator available after division by `2^128`. -/
def exactFieldNumerator6401 : Nat := 274980728111395087

/-- The conservative MCA numerator used in the current endpoint audits. -/
def currentConservativeMCANumerator6401 : Nat := 274980700000000000

def illustrativeListReserve6401 : Nat := 10000000000000000
def maxMCAWithIllustrativeListReserve6401 : Nat :=
  exactFieldNumerator6401 - illustrativeListReserve6401

theorem subfield_fullCode_parameters_exact6401 :
    packedExtensionDegree6401 = 96 ∧
      r1AgreementThreshold6401 = 196608 ∧
      a6401 < r1AgreementThreshold6401 ∧
      r2AgreementThreshold6401 = 174763 ∧
      r2AgreementThreshold6401 ≤ a6401 ∧
      smallestApplicableFrobeniusTerms6401 = 2 ∧
      fullCodeTheoremExponent6401 = 131072 := by
  norm_num [packedExtensionDegree6401, extensionDegree6401,
    squaredInterleaving6401, r1AgreementThreshold6401,
    r2AgreementThreshold6401, a6401,
    smallestApplicableFrobeniusTerms6401,
    fullCodeTheoremExponent6401, k6401]

/-- The Section 4.3 bound for the unrestricted code is numerically unusable:
already its second power is larger than the complete field numerator, while
the actual theorem exponent is `131072`. -/
theorem fullCode_subfield_bound_does_not_fit6401 :
    q6401 ^ 2 = 4539909903627583489 ∧
      exactFieldNumerator6401 < q6401 ^ 2 ∧
      q6401 ^ 2 ≤ fullCodeTheoremListBound6401 ∧
      exactFieldNumerator6401 < fullCodeTheoremListBound6401 := by
  have hbase : 1 ≤ q6401 := by norm_num [q6401]
  have hexp : 2 ≤ fullCodeTheoremExponent6401 := by
    norm_num [fullCodeTheoremExponent6401,
      smallestApplicableFrobeniusTerms6401, k6401]
  have hpow : q6401 ^ 2 ≤ q6401 ^ fullCodeTheoremExponent6401 :=
    Nat.pow_le_pow_right hbase hexp
  constructor
  · norm_num [q6401]
  constructor
  · norm_num [q6401, exactFieldNumerator6401]
  constructor
  · simpa [fullCodeTheoremListBound6401] using hpow
  · exact (by norm_num [q6401, exactFieldNumerator6401] :
        exactFieldNumerator6401 < q6401 ^ 2) |>.trans_le
      (by simpa [fullCodeTheoremListBound6401] using hpow)

/-- Exact budget split.  Keeping the current conservative MCA numerator
leaves only `28,111,395,087`.  Reserving `10^16` for a new unconditional
list theorem would instead require lowering MCA by just under `10^16`.
This is arithmetic only; no such list theorem is claimed here. -/
theorem field_budget_split_exact6401 :
    exactFieldNumerator6401 - currentConservativeMCANumerator6401 =
        28111395087 ∧
      maxMCAWithIllustrativeListReserve6401 = 264980728111395087 ∧
      currentConservativeMCANumerator6401 -
          maxMCAWithIllustrativeListReserve6401 = 9999971888604913 ∧
      maxMCAWithIllustrativeListReserve6401 +
          illustrativeListReserve6401 = exactFieldNumerator6401 := by
  norm_num [exactFieldNumerator6401,
    currentConservativeMCANumerator6401,
    maxMCAWithIllustrativeListReserve6401,
    illustrativeListReserve6401]

end BCHKSSubfieldListBudgetAudit6401
end ProximityPrize.SubmissionLower
