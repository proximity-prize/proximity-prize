import ProximityPrize.SubmissionLower.L1
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.Z8
import ProximityPrize.SubmissionLower.D1

/- Arithmetic for the proposed regular-colon refinement.
   Not an exported ProtocolClaim. The polynomial-space bound is separate. -/
namespace ProximityPrize.SubmissionLower.RegularColonArithmetic
open scoped BigOperators
open RCN119 RCN100
open RCN302
open RCN095 RCN263
open RCN198
open RCN206
open RCN318 RCN260

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def agreements : ℕ := 182032
def gap : ℕ := 50961
def budget : ℕ := 274980727111395087

def regularQuotientBound (D L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range ((D - 1) / w + 1),
    min (D - w * j) (gap + 1 + j * (n - w)) * (L + 1 - j)

theorem kernelA_rank : localRankBound 42 240000 12 = 2186963688 := by decide
theorem kernelB_rank : localRankBound 81 1283 25 = 81799679 := by decide

theorem kernelA_nullity :
    coefficientCount 7645344 131071 240000 12 -
      262144 * localRankBound 42 240000 12 = 181392944031 := by
  rw [kernelA_rank]
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    7645344 131071 240000 12 59 (by decide) (by decide)]
  decide

theorem kernelB_nullity :
    coefficientCount 14744592 131071 1283 25 -
      262144 * localRankBound 81 1283 25 = 47959470 := by
  rw [kernelB_rank]
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    14744592 131071 1283 25 113 (by decide) (by decide)]
  decide

theorem regular_quotient_exact :
    regularQuotientBound 567522 239946 = 181380207354 := by decide

theorem regular_quotient_lt_kernel :
    regularQuotientBound 567522 239946 <
      coefficientCount 7645344 131071 240000 12 -
        262144 * localRankBound 42 240000 12 := by
  rw [regular_quotient_exact, kernelA_nullity]
  decide

def fixedCost (a b s : ℕ) : ℕ :=
  flagMixed (surfaceFlag a b s)
    (reducedResidualAgreementFlag (support a b s) (w + 1))
    (reducedResidualAgreementFlag (support a b s) (w + 2))

def fixedSingular (T : ℕ) : TightParameters :=
  ⟨n, w, agreements, 42 * agreements, T, 12⟩

def residualStage (lt : ℕ) : UnequalParameters :=
  ⟨n, w, agreements, 112, 25, 1283 - lt, 58, 12, 240000 - lt⟩

def residualSingular (lt : ℕ) : TightParameters :=
  ⟨n, w, agreements, 81 * agreements, 1283 - lt, 25⟩

def ledger (T lt : ℕ) : ℕ :=
  fixedCost (T - 53) 40 10 + (fixedSingular T).countCap +
    (residualStage lt).regularCountCap + (residualSingular lt).countCap + 1

theorem low_ledger_exact : ledger 1280 0 = 274790150551512177 := by decide
theorem high_ledger_exact : ledger 1282 1281 = 274516952973709728 := by decide
theorem low_ledger_lt : ledger 1280 0 < budget := by
  rw [low_ledger_exact]
  decide
theorem high_ledger_lt : ledger 1282 1281 < budget := by
  rw [high_ledger_exact]
  decide

end ProximityPrize.SubmissionLower.RegularColonArithmetic
