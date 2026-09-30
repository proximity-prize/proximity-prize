import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_008
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source12 : Parameters := ⟨60,591,26,12,82,1,2⟩
theorem shape12 : Shape source12 := by constructor <;> decide +kernel
theorem middle12 (h : ℕ) (hh : h≤12) : 82≤(source12.cutoff h+26-1)/131071 := by
  simp only [source12,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients12 :
    SecondJetRelaxedGlobalCounts.coefficientCount source12.cutoff 131071 591 26 12 82=35232518006560 := by
  decide +kernel
theorem rank12 : SecondJetRelaxedCounts.rankBound 60 591 26 12 82=134399718 := by decide +kernel
theorem dimension12 : Dimension source12 438331168 := by
  exact dimension_of_counts source12 438331168 35232518006560 134399718
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle12 coefficients12 rank12 (by decide)
def source13 : Parameters := ⟨62,573,27,12,85,1,2⟩
theorem shape13 : Shape source13 := by constructor <;> decide +kernel
theorem middle13 (h : ℕ) (hh : h≤12) : 85≤(source13.cutoff h+27-1)/131071 := by
  simp only [source13,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients13 :
    SecondJetRelaxedGlobalCounts.coefficientCount source13.cutoff 131071 573 27 12 85=38667129105566 := by
  decide +kernel
theorem rank13 : SecondJetRelaxedCounts.rankBound 62 573 27 12 85=147501133 := by decide +kernel
theorem dimension13 : Dimension source13 592096414 := by
  exact dimension_of_counts source13 592096414 38667129105566 147501133
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle13 coefficients13 rank13 (by decide)
def source14 : Parameters := ⟨64,2220,26,11,87,2,3⟩
theorem shape14 : Shape source14 := by constructor <;> decide +kernel
theorem middle14 (h : ℕ) (hh : h≤11) : 87≤(source14.cutoff h+26-1)/131071 := by
  simp only [source14,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients14 :
    SecondJetRelaxedGlobalCounts.coefficientCount source14.cutoff 131071 2220 26 11 87=157100588035857 := by
  decide +kernel
theorem rank14 : SecondJetRelaxedCounts.rankBound 64 2220 26 11 87=598723817 := by decide +kernel
theorem dimension14 : Dimension source14 148731752209 := by
  exact dimension_of_counts source14 148731752209 157100588035857 598723817
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle14 coefficients14 rank14 (by decide)
def source15 : Parameters := ⟨64,2167,26,12,87,2,3⟩
theorem shape15 : Shape source15 := by constructor <;> decide +kernel
theorem middle15 (h : ℕ) (hh : h≤12) : 87≤(source15.cutoff h+26-1)/131071 := by
  simp only [source15,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients15 :
    SecondJetRelaxedGlobalCounts.coefficientCount source15.cutoff 131071 2167 26 12 87=155659118846414 := by
  decide +kernel
theorem rank15 : SecondJetRelaxedCounts.rankBound 64 2167 26 12 87=593244562 := by decide +kernel
theorem dimension15 : Dimension source15 143616385486 := by
  exact dimension_of_counts source15 143616385486 155659118846414 593244562
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle15 coefficients15 rank15 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
