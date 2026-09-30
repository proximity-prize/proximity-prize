import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_024
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source28 : Parameters := ⟨76,926,32,15,104,2,3⟩
theorem shape28 : Shape source28 := by constructor <;> decide +kernel
theorem middle28 (h : ℕ) (hh : h≤15) : 104≤(source28.cutoff h+32-1)/131071 := by
  simp only [source28,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients28 :
    SecondJetRelaxedGlobalCounts.coefficientCount source28.cutoff 131071 926 32 15 104=132618459635252 := by
  decide +kernel
theorem rank28 : SecondJetRelaxedCounts.rankBound 76 926 32 15 104=505898841 := by decide +kernel
theorem dimension28 : Dimension source28 113860148 := by
  exact dimension_of_counts source28 113860148 132618459635252 505898841
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle28 coefficients28 rank28 (by decide)
def source29 : Parameters := ⟨76,903,34,15,104,2,3⟩
theorem shape29 : Shape source29 := by constructor <;> decide +kernel
theorem middle29 (h : ℕ) (hh : h≤15) : 104≤(source29.cutoff h+34-1)/131071 := by
  simp only [source29,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients29 :
    SecondJetRelaxedGlobalCounts.coefficientCount source29.cutoff 131071 903 34 15 104=140328946797756 := by
  decide +kernel
theorem rank29 : SecondJetRelaxedCounts.rankBound 76 903 34 15 104=535310235 := by decide +kernel
theorem dimension29 : Dimension source29 580553916 := by
  exact dimension_of_counts source29 580553916 140328946797756 535310235
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle29 coefficients29 rank29 (by decide)
def source30 : Parameters := ⟨76,900,34,16,104,2,3⟩
theorem shape30 : Shape source30 := by constructor <;> decide +kernel
theorem middle30 (h : ℕ) (hh : h≤16) : 104≤(source30.cutoff h+34-1)/131071 := by
  simp only [source30,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients30 :
    SecondJetRelaxedGlobalCounts.coefficientCount source30.cutoff 131071 900 34 16 104=141135973397016 := by
  decide +kernel
theorem rank30 : SecondJetRelaxedCounts.rankBound 76 900 34 16 104=538388096 := by decide +kernel
theorem dimension30 : Dimension source30 764359192 := by
  exact dimension_of_counts source30 764359192 141135973397016 538388096
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle30 coefficients30 rank30 (by decide)
def source31 : Parameters := ⟨78,871,34,15,107,2,3⟩
theorem shape31 : Shape source31 := by constructor <;> decide +kernel
theorem middle31 (h : ℕ) (hh : h≤15) : 107≤(source31.cutoff h+34-1)/131071 := by
  simp only [source31,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients31 :
    SecondJetRelaxedGlobalCounts.coefficientCount source31.cutoff 131071 871 34 15 107=143505368808972 := by
  decide +kernel
theorem rank31 : SecondJetRelaxedCounts.rankBound 78 871 34 15 107=547429171 := by decide +kernel
theorem dimension31 : Dimension source31 96206348 := by
  exact dimension_of_counts source31 96206348 143505368808972 547429171
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle31 coefficients31 rank31 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
