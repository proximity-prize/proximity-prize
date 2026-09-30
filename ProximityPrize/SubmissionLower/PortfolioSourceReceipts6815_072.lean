import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_068
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source72 : Parameters := ⟨140,1180,60,28,192,4,5⟩
theorem shape72 : Shape source72 := by constructor <;> decide +kernel
theorem middle72 (h : ℕ) (hh : h≤28) : 192≤(source72.cutoff h+60-1)/131071 := by
  simp only [source72,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients72 :
    SecondJetRelaxedGlobalCounts.coefficientCount source72.cutoff 131071 1180 60 28 192=1837057575374750 := by
  decide +kernel
theorem rank72 : SecondJetRelaxedCounts.rankBound 140 1180 60 28 192=7007654645 := by decide +kernel
theorem dimension72 : Dimension source72 42956115870 := by
  exact dimension_of_counts source72 42956115870 1837057575374750 7007654645
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle72 coefficients72 rank72 (by decide)
def source73 : Parameters := ⟨140,1150,62,29,192,4,5⟩
theorem shape73 : Shape source73 := by constructor <;> decide +kernel
theorem middle73 (h : ℕ) (hh : h≤29) : 192≤(source73.cutoff h+62-1)/131071 := by
  simp only [source73,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients73 :
    SecondJetRelaxedGlobalCounts.coefficientCount source73.cutoff 131071 1150 62 29 192=1880918003468055 := by
  decide +kernel
theorem rank73 : SecondJetRelaxedCounts.rankBound 140 1150 62 29 192=7175068992 := by decide +kernel
theorem dimension73 : Dimension source73 16717629207 := by
  exact dimension_of_counts source73 16717629207 1880918003468055 7175068992
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle73 coefficients73 rank73 (by decide)
def source74 : Parameters := ⟨160,1119,70,33,219,4,5⟩
theorem shape74 : Shape source74 := by constructor <;> decide +kernel
theorem middle74 (h : ℕ) (hh : h≤33) : 219≤(source74.cutoff h+70-1)/131071 := by
  simp only [source74,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients74 :
    SecondJetRelaxedGlobalCounts.coefficientCount source74.cutoff 131071 1119 70 33 219=3003373702637497 := by
  decide +kernel
theorem rank74 : SecondJetRelaxedCounts.rankBound 160 1119 70 33 219=11456869645 := by decide +kernel
theorem dimension74 : Dimension source74 24066418617 := by
  exact dimension_of_counts source74 24066418617 3003373702637497 11456869645
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle74 coefficients74 rank74 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
