import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_040
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source44 : Parameters := ⟨84,2259,36,17,115,3,4⟩
theorem shape44 : Shape source44 := by constructor <;> decide +kernel
theorem middle44 (h : ℕ) (hh : h≤17) : 115≤(source44.cutoff h+36-1)/131071 := by
  simp only [source44,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients44 :
    SecondJetRelaxedGlobalCounts.coefficientCount source44.cutoff 131071 2259 36 17 115=501344101678086 := by
  decide +kernel
theorem rank44 : SecondJetRelaxedCounts.rankBound 84 2259 36 17 115=1909716285 := by decide +kernel
theorem dimension44 : Dimension source44 723435863046 := by
  exact dimension_of_counts source44 723435863046 501344101678086 1909716285
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle44 coefficients44 rank44 (by decide)
def source45 : Parameters := ⟨85,790,37,17,116,2,3⟩
theorem shape45 : Shape source45 := by constructor <;> decide +kernel
theorem middle45 (h : ℕ) (hh : h≤17) : 116≤(source45.cutoff h+37-1)/131071 := by
  simp only [source45,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients45 :
    SecondJetRelaxedGlobalCounts.coefficientCount source45.cutoff 131071 790 37 17 116=180634115711951 := by
  decide +kernel
theorem rank45 : SecondJetRelaxedCounts.rankBound 85 790 37 17 116=689060217 := by decide +kernel
theorem dimension45 : Dimension source45 1114186703 := by
  exact dimension_of_counts source45 1114186703 180634115711951 689060217
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle45 coefficients45 rank45 (by decide)
def source46 : Parameters := ⟨86,2117,36,16,117,3,4⟩
theorem shape46 : Shape source46 := by constructor <;> decide +kernel
theorem middle46 (h : ℕ) (hh : h≤16) : 117≤(source46.cutoff h+36-1)/131071 := by
  simp only [source46,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients46 :
    SecondJetRelaxedGlobalCounts.coefficientCount source46.cutoff 131071 2117 36 16 117=491578540988262 := by
  decide +kernel
theorem rank46 : SecondJetRelaxedCounts.rankBound 86 2117 36 16 117=1872282170 := by decide +kernel
theorem dimension46 : Dimension source46 771003815782 := by
  exact dimension_of_counts source46 771003815782 491578540988262 1872282170
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle46 coefficients46 rank46 (by decide)
def source47 : Parameters := ⟨86,2108,36,17,117,3,4⟩
theorem shape47 : Shape source47 := by constructor <;> decide +kernel
theorem middle47 (h : ℕ) (hh : h≤17) : 117≤(source47.cutoff h+36-1)/131071 := by
  simp only [source47,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients47 :
    SecondJetRelaxedGlobalCounts.coefficientCount source47.cutoff 131071 2108 36 17 117=493507628530001 := by
  decide +kernel
theorem rank47 : SecondJetRelaxedCounts.rankBound 86 2108 36 17 117=1879663641 := by decide +kernel
theorem dimension47 : Dimension source47 765083023697 := by
  exact dimension_of_counts source47 765083023697 493507628530001 1879663641
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle47 coefficients47 rank47 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
