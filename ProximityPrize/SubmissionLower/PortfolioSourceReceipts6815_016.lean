import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_012
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source16 : Parameters := ⟨66,2096,26,11,90,2,3⟩
theorem shape16 : Shape source16 := by constructor <;> decide +kernel
theorem middle16 (h : ℕ) (hh : h≤11) : 90≤(source16.cutoff h+26-1)/131071 := by
  simp only [source16,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients16 :
    SecondJetRelaxedGlobalCounts.coefficientCount source16.cutoff 131071 2096 26 11 90=159118184298649 := by
  decide +kernel
theorem rank16 : SecondJetRelaxedCounts.rankBound 66 2096 26 11 90=606301662 := by decide +kernel
theorem dimension16 : Dimension source16 179841415321 := by
  exact dimension_of_counts source16 179841415321 159118184298649 606301662
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle16 coefficients16 rank16 (by decide)
def source17 : Parameters := ⟨66,2052,26,12,90,2,3⟩
theorem shape17 : Shape source17 := by constructor <;> decide +kernel
theorem middle17 (h : ℕ) (hh : h≤12) : 90≤(source17.cutoff h+26-1)/131071 := by
  simp only [source17,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients17 :
    SecondJetRelaxedGlobalCounts.coefficientCount source17.cutoff 131071 2052 26 12 90=158127796652254 := by
  decide +kernel
theorem rank17 : SecondJetRelaxedCounts.rankBound 66 2052 26 12 90=602544606 := by decide +kernel
theorem dimension17 : Dimension source17 174343456990 := by
  exact dimension_of_counts source17 174343456990 158127796652254 602544606
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle17 coefficients17 rank17 (by decide)
def source18 : Parameters := ⟨66,1587,28,12,90,2,3⟩
theorem shape18 : Shape source18 := by constructor <;> decide +kernel
theorem middle18 (h : ℕ) (hh : h≤12) : 90≤(source18.cutoff h+28-1)/131071 := by
  simp only [source18,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients18 :
    SecondJetRelaxedGlobalCounts.coefficientCount source18.cutoff 131071 1587 28 12 90=134412007266975 := by
  decide +kernel
theorem rank18 : SecondJetRelaxedCounts.rankBound 66 1587 28 12 90=512363070 := by decide +kernel
theorem dimension18 : Dimension source18 99102644895 := by
  exact dimension_of_counts source18 99102644895 134412007266975 512363070
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle18 coefficients18 rank18 (by decide)
def source19 : Parameters := ⟨66,1345,28,14,90,2,3⟩
theorem shape19 : Shape source19 := by constructor <;> decide +kernel
theorem middle19 (h : ℕ) (hh : h≤14) : 90≤(source19.cutoff h+28-1)/131071 := by
  simp only [source19,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients19 :
    SecondJetRelaxedGlobalCounts.coefficientCount source19.cutoff 131071 1345 28 14 90=115450031410280 := by
  decide +kernel
theorem rank19 : SecondJetRelaxedCounts.rankBound 66 1345 28 14 90=440400205 := by decide +kernel
theorem dimension19 : Dimension source19 1760070760 := by
  exact dimension_of_counts source19 1760070760 115450031410280 440400205
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle19 coefficients19 rank19 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
