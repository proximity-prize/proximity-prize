import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_044
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source48 : Parameters := ⟨86,1968,38,17,117,3,4⟩
theorem shape48 : Shape source48 := by constructor <;> decide +kernel
theorem middle48 (h : ℕ) (hh : h≤17) : 117≤(source48.cutoff h+38-1)/131071 := by
  simp only [source48,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients48 :
    SecondJetRelaxedGlobalCounts.coefficientCount source48.cutoff 131071 1968 38 17 117=496097610795480 := by
  decide +kernel
theorem rank48 : SecondJetRelaxedCounts.rankBound 86 1968 38 17 117=1889829174 := by decide +kernel
theorem dimension48 : Dimension source48 690231806424 := by
  exact dimension_of_counts source48 690231806424 496097610795480 1889829174
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle48 coefficients48 rank48 (by decide)
def source49 : Parameters := ⟨87,775,38,17,119,2,3⟩
theorem shape49 : Shape source49 := by constructor <;> decide +kernel
theorem middle49 (h : ℕ) (hh : h≤17) : 119≤(source49.cutoff h+38-1)/131071 := by
  simp only [source49,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients49 :
    SecondJetRelaxedGlobalCounts.coefficientCount source49.cutoff 131071 775 38 17 119=193675372140288 := by
  decide +kernel
theorem rank49 : SecondJetRelaxedCounts.rankBound 87 775 38 17 119=738807891 := by decide +kernel
theorem dimension49 : Dimension source49 1316361984 := by
  exact dimension_of_counts source49 1316361984 193675372140288 738807891
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle49 coefficients49 rank49 (by decide)
def source50 : Parameters := ⟨87,1430,38,17,119,3,4⟩
theorem shape50 : Shape source50 := by constructor <;> decide +kernel
theorem middle50 (h : ℕ) (hh : h≤17) : 119≤(source50.cutoff h+38-1)/131071 := by
  simp only [source50,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients50 :
    SecondJetRelaxedGlobalCounts.coefficientCount source50.cutoff 131071 1430 38 17 119=366765095606388 := by
  decide +kernel
theorem rank50 : SecondJetRelaxedCounts.rankBound 87 1430 38 17 119=1399093086 := by decide +kernel
theorem dimension50 : Dimension source50 1237670004 := by
  exact dimension_of_counts source50 1237670004 366765095606388 1399093086
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle50 coefficients50 rank50 (by decide)
def source51 : Parameters := ⟨88,1895,36,17,120,3,4⟩
theorem shape51 : Shape source51 := by constructor <;> decide +kernel
theorem middle51 (h : ℕ) (hh : h≤17) : 120≤(source51.cutoff h+36-1)/131071 := by
  simp only [source51,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients51 :
    SecondJetRelaxedGlobalCounts.coefficientCount source51.cutoff 131071 1895 36 17 120=466759464986876 := by
  decide +kernel
theorem rank51 : SecondJetRelaxedCounts.rankBound 88 1895 36 17 120=1778166957 := by decide +kernel
theorem dimension51 : Dimension source51 623666211068 := by
  exact dimension_of_counts source51 623666211068 466759464986876 1778166957
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle51 coefficients51 rank51 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
