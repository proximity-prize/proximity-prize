import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_048
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source52 : Parameters := ⟨90,1306,39,18,123,3,4⟩
theorem shape52 : Shape source52 := by constructor <;> decide +kernel
theorem middle52 (h : ℕ) (hh : h≤18) : 123≤(source52.cutoff h+39-1)/131071 := by
  simp only [source52,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients52 :
    SecondJetRelaxedGlobalCounts.coefficientCount source52.cutoff 131071 1306 39 18 123=377676224938019 := by
  decide +kernel
theorem rank52 : SecondJetRelaxedCounts.rankBound 90 1306 39 18 123=1440718864 := by decide +kernel
theorem dimension52 : Dimension source52 419053603 := by
  exact dimension_of_counts source52 419053603 377676224938019 1440718864
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle52 coefficients52 rank52 (by decide)
def source53 : Parameters := ⟨92,1638,38,17,126,3,4⟩
theorem shape53 : Shape source53 := by constructor <;> decide +kernel
theorem middle53 (h : ℕ) (hh : h≤17) : 126≤(source53.cutoff h+38-1)/131071 := by
  simp only [source53,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients53 :
    SecondJetRelaxedGlobalCounts.coefficientCount source53.cutoff 131071 1638 38 17 126=480785075798691 := by
  decide +kernel
theorem rank53 : SecondJetRelaxedCounts.rankBound 92 1638 38 17 126=1831370378 := by decide +kernel
theorem dimension53 : Dimension source53 702319428259 := by
  exact dimension_of_counts source53 702319428259 480785075798691 1831370378
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle53 coefficients53 rank53 (by decide)
def source54 : Parameters := ⟨92,739,42,19,126,2,3⟩
theorem shape54 : Shape source54 := by constructor <;> decide +kernel
theorem middle54 (h : ℕ) (hh : h≤19) : 126≤(source54.cutoff h+42-1)/131071 := by
  simp only [source54,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients54 :
    SecondJetRelaxedGlobalCounts.coefficientCount source54.cutoff 131071 739 42 19 126=244164806276923 := by
  decide +kernel
theorem rank54 : SecondJetRelaxedCounts.rankBound 92 739 42 19 126=931401896 := by decide +kernel
theorem dimension54 : Dimension source54 3387651899 := by
  exact dimension_of_counts source54 3387651899 244164806276923 931401896
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle54 coefficients54 rank54 (by decide)
def source55 : Parameters := ⟨94,1190,41,19,128,3,4⟩
theorem shape55 : Shape source55 := by constructor <;> decide +kernel
theorem middle55 (h : ℕ) (hh : h≤19) : 128≤(source55.cutoff h+41-1)/131071 := by
  simp only [source55,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients55 :
    SecondJetRelaxedGlobalCounts.coefficientCount source55.cutoff 131071 1190 41 19 128=409652509445663 := by
  decide +kernel
theorem rank55 : SecondJetRelaxedCounts.rankBound 94 1190 41 19 128=1562699433 := by decide +kernel
theorem dimension55 : Dimension source55 229281311 := by
  exact dimension_of_counts source55 229281311 409652509445663 1562699433
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle55 coefficients55 rank55 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
