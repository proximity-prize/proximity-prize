import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_052
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source56 : Parameters := ⟨98,1108,43,20,134,3,4⟩
theorem shape56 : Shape source56 := by constructor <;> decide +kernel
theorem middle56 (h : ℕ) (hh : h≤20) : 134≤(source56.cutoff h+43-1)/131071 := by
  simp only [source56,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients56 :
    SecondJetRelaxedGlobalCounts.coefficientCount source56.cutoff 131071 1108 43 20 134=450670682287266 := by
  decide +kernel
theorem rank56 : SecondJetRelaxedCounts.rankBound 98 1108 43 20 134=1719158121 := by decide +kernel
theorem dimension56 : Dimension source56 3695815842 := by
  exact dimension_of_counts source56 3695815842 450670682287266 1719158121
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle56 coefficients56 rank56 (by decide)
def source57 : Parameters := ⟨100,2306,42,19,136,4,5⟩
theorem shape57 : Shape source57 := by constructor <;> decide +kernel
theorem middle57 (h : ℕ) (hh : h≤19) : 136≤(source57.cutoff h+42-1)/131071 := by
  simp only [source57,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients57 :
    SecondJetRelaxedGlobalCounts.coefficientCount source57.cutoff 131071 2306 42 19 136=966978954449281 := by
  decide +kernel
theorem rank57 : SecondJetRelaxedCounts.rankBound 100 2306 42 19 136=3687036866 := by decide +kernel
theorem dimension57 : Dimension source57 444362248577 := by
  exact dimension_of_counts source57 444362248577 966978954449281 3687036866
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle57 coefficients57 rank57 (by decide)
def source58 : Parameters := ⟨102,1051,45,21,139,3,4⟩
theorem shape58 : Shape source58 := by constructor <;> decide +kernel
theorem middle58 (h : ℕ) (hh : h≤21) : 139≤(source58.cutoff h+45-1)/131071 := by
  simp only [source58,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients58 :
    SecondJetRelaxedGlobalCounts.coefficientCount source58.cutoff 131071 1051 45 21 139=501699250739077 := by
  decide +kernel
theorem rank58 : SecondJetRelaxedCounts.rankBound 102 1051 45 21 139=1913816931 := by decide +kernel
theorem dimension58 : Dimension source58 3625179013 := by
  exact dimension_of_counts source58 3625179013 501699250739077 1913816931
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle58 coefficients58 rank58 (by decide)
def source59 : Parameters := ⟨108,1003,47,21,148,3,4⟩
theorem shape59 : Shape source59 := by constructor <;> decide +kernel
theorem middle59 (h : ℕ) (hh : h≤21) : 148≤(source59.cutoff h+47-1)/131071 := by
  simp only [source59,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients59 :
    SecondJetRelaxedGlobalCounts.coefficientCount source59.cutoff 131071 1003 47 21 148=579050041635048 := by
  decide +kernel
theorem rank59 : SecondJetRelaxedCounts.rankBound 108 1003 47 21 148=2208888878 := by decide +kernel
theorem dimension59 : Dimension source59 3075600616 := by
  exact dimension_of_counts source59 3075600616 579050041635048 2208888878
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle59 coefficients59 rank59 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
