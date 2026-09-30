import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_028
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source32 : Parameters := ⟨78,869,34,16,107,2,3⟩
theorem shape32 : Shape source32 := by constructor <;> decide +kernel
theorem middle32 (h : ℕ) (hh : h≤16) : 107≤(source32.cutoff h+34-1)/131071 := by
  simp only [source32,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients32 :
    SecondJetRelaxedGlobalCounts.coefficientCount source32.cutoff 131071 869 34 16 107=144486472762713 := by
  decide +kernel
theorem rank32 : SecondJetRelaxedCounts.rankBound 78 869 34 16 107=551168281 := by decide +kernel
theorem dimension32 : Dimension source32 1014908249 := by
  exact dimension_of_counts source32 1014908249 144486472762713 551168281
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle32 coefficients32 rank32 (by decide)
def source33 : Parameters := ⟨80,858,34,15,109,2,3⟩
theorem shape33 : Shape source33 := by constructor <;> decide +kernel
theorem middle33 (h : ℕ) (hh : h≤15) : 109≤(source33.cutoff h+34-1)/131071 := by
  simp only [source33,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients33 :
    SecondJetRelaxedGlobalCounts.coefficientCount source33.cutoff 131071 858 34 15 109=149756332333356 := by
  decide +kernel
theorem rank33 : SecondJetRelaxedCounts.rankBound 80 858 34 15 109=571271326 := by decide +kernel
theorem dimension33 : Dimension source33 981850412 := by
  exact dimension_of_counts source33 981850412 149756332333356 571271326
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle33 coefficients33 rank33 (by decide)
def source34 : Parameters := ⟨80,2375,34,15,109,3,4⟩
theorem shape34 : Shape source34 := by constructor <;> decide +kernel
theorem middle34 (h : ℕ) (hh : h≤15) : 109≤(source34.cutoff h+34-1)/131071 := by
  simp only [source34,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients34 :
    SecondJetRelaxedGlobalCounts.coefficientCount source34.cutoff 131071 2375 34 15 109=427110830117556 := by
  decide +kernel
theorem rank34 : SecondJetRelaxedCounts.rankBound 80 2375 34 15 109=1628406429 := by decide +kernel
theorem dimension34 : Dimension source34 233855193780 := by
  exact dimension_of_counts source34 233855193780 427110830117556 1628406429
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle34 coefficients34 rank34 (by decide)
def source35 : Parameters := ⟨80,856,34,16,109,2,3⟩
theorem shape35 : Shape source35 := by constructor <;> decide +kernel
theorem middle35 (h : ℕ) (hh : h≤16) : 109≤(source35.cutoff h+34-1)/131071 := by
  simp only [source35,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients35 :
    SecondJetRelaxedGlobalCounts.coefficientCount source35.cutoff 131071 856 34 16 109=150774571919226 := by
  decide +kernel
theorem rank35 : SecondJetRelaxedCounts.rankBound 80 856 34 16 109=575153964 := by decide +kernel
theorem dimension35 : Dimension source35 1411180410 := by
  exact dimension_of_counts source35 1411180410 150774571919226 575153964
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle35 coefficients35 rank35 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
