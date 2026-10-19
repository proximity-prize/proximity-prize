import ProximityPrize.SubmissionLower.MergedInfra6815_35
set_option Elab.async false
section MergedPart0
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source0 : Parameters := ⟨48,1122,20,9,65,1,2⟩
theorem shape0 : Shape source0 := by constructor <;> decide +kernel
theorem middle0 (h : ℕ) (hh : h≤9) : 65≤(source0.cutoff h+20-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source0, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients0 :
    SecondJetRelaxedGlobalCounts.coefficientCount source0.cutoff 131071 1122 20 9 65=27720790276737 := by
  decide +kernel
theorem rank0 : SecondJetRelaxedCounts.rankBound 48 1122 20 9 65=105705598 := by decide +kernel
theorem dimension0 : Dimension source0 10701994625 := by
  exact dimension_of_counts source0 10701994625 27720790276737 105705598
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle0 coefficients0 rank0 (by decide)
def source1 : Parameters := ⟨50,1038,20,9,68,1,2⟩
theorem shape1 : Shape source1 := by constructor <;> decide +kernel
theorem middle1 (h : ℕ) (hh : h≤9) : 68≤(source1.cutoff h+20-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source1, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients1 :
    SecondJetRelaxedGlobalCounts.coefficientCount source1.cutoff 131071 1038 20 9 68=28118224644489 := by
  decide +kernel
theorem rank1 : SecondJetRelaxedCounts.rankBound 50 1038 20 9 68=107197185 := by decide +kernel
theorem dimension1 : Dimension source1 17125779849 := by
  exact dimension_of_counts source1 17125779849 28118224644489 107197185
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle1 coefficients1 rank1 (by decide)
def source2 : Parameters := ⟨52,949,22,10,71,1,2⟩
theorem shape2 : Shape source2 := by constructor <;> decide +kernel
theorem middle2 (h : ℕ) (hh : h≤10) : 71≤(source2.cutoff h+22-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source2, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients2 :
    SecondJetRelaxedGlobalCounts.coefficientCount source2.cutoff 131071 949 22 10 71=32365601879810 := by
  decide +kernel
theorem rank2 : SecondJetRelaxedCounts.rankBound 52 949 22 10 71=123296314 := by decide +kernel
theorem dimension2 : Dimension source2 44212942594 := by
  exact dimension_of_counts source2 44212942594 32365601879810 123296314
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle2 coefficients2 rank2 (by decide)
def source3 : Parameters := ⟨56,800,25,12,77,1,2⟩
theorem shape3 : Shape source3 := by constructor <;> decide +kernel
theorem middle3 (h : ℕ) (hh : h≤12) : 77≤(source3.cutoff h+25-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source3, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients3 :
    SecondJetRelaxedGlobalCounts.coefficientCount source3.cutoff 131071 800 25 12 77=39103092696213 := by
  decide +kernel
theorem rank3 : SecondJetRelaxedCounts.rankBound 56 800 25 12 77=148924194 := by decide +kernel
theorem dimension3 : Dimension source3 63508784277 := by
  exact dimension_of_counts source3 63508784277 39103092696213 148924194
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle3 coefficients3 rank3 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart0
section MergedPart1
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source4 : Parameters := ⟨56,1000,25,12,77,1,2⟩
theorem shape4 : Shape source4 := by constructor <;> decide +kernel
theorem middle4 (h : ℕ) (hh : h≤12) : 77≤(source4.cutoff h+25-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source4, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients4 :
    SecondJetRelaxedGlobalCounts.coefficientCount source4.cutoff 131071 1000 25 12 77=49287363174413 := by
  decide +kernel
theorem rank4 : SecondJetRelaxedCounts.rankBound 56 1000 25 12 77=187451594 := by decide +kernel
theorem dimension4 : Dimension source4 148052516877 := by
  exact dimension_of_counts source4 148052516877 49287363174413 187451594
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle4 coefficients4 rank4 (by decide)
def source5 : Parameters := ⟨56,1200,25,12,77,1,2⟩
theorem shape5 : Shape source5 := by constructor <;> decide +kernel
theorem middle5 (h : ℕ) (hh : h≤12) : 77≤(source5.cutoff h+25-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source5, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients5 :
    SecondJetRelaxedGlobalCounts.coefficientCount source5.cutoff 131071 1200 25 12 77=59471633652613 := by
  decide +kernel
theorem rank5 : SecondJetRelaxedCounts.rankBound 56 1200 25 12 77=225978994 := by decide +kernel
theorem dimension5 : Dimension source5 232596249477 := by
  exact dimension_of_counts source5 232596249477 59471633652613 225978994
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle5 coefficients5 rank5 (by decide)
def source6 : Parameters := ⟨56,1400,25,12,77,1,2⟩
theorem shape6 : Shape source6 := by constructor <;> decide +kernel
theorem middle6 (h : ℕ) (hh : h≤12) : 77≤(source6.cutoff h+25-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source6, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients6 :
    SecondJetRelaxedGlobalCounts.coefficientCount source6.cutoff 131071 1400 25 12 77=69655904130813 := by
  decide +kernel
theorem rank6 : SecondJetRelaxedCounts.rankBound 56 1400 25 12 77=264506394 := by decide +kernel
theorem dimension6 : Dimension source6 317139982077 := by
  exact dimension_of_counts source6 317139982077 69655904130813 264506394
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle6 coefficients6 rank6 (by decide)
def source7 : Parameters := ⟨58,620,25,11,79,1,2⟩
theorem shape7 : Shape source7 := by constructor <;> decide +kernel
theorem middle7 (h : ℕ) (hh : h≤11) : 79≤(source7.cutoff h+25-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source7, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients7 :
    SecondJetRelaxedGlobalCounts.coefficientCount source7.cutoff 131071 620 25 11 79=32110419773839 := by
  decide +kernel
theorem rank7 : SecondJetRelaxedCounts.rankBound 58 620 25 11 79=122489797 := by decide +kernel
theorem dimension7 : Dimension source7 454429071 := by
  exact dimension_of_counts source7 454429071 32110419773839 122489797
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle7 coefficients7 rank7 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart1
section MergedPart2
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source8 : Parameters := ⟨58,800,25,11,79,1,2⟩
theorem shape8 : Shape source8 := by constructor <;> decide +kernel
theorem middle8 (h : ℕ) (hh : h≤11) : 79≤(source8.cutoff h+25-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source8, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients8 :
    SecondJetRelaxedGlobalCounts.coefficientCount source8.cutoff 131071 800 25 11 79=41957371084639 := by
  decide +kernel
theorem rank8 : SecondJetRelaxedCounts.rankBound 58 800 25 11 79=159703717 := by decide +kernel
theorem dimension8 : Dimension source8 91999895391 := by
  exact dimension_of_counts source8 91999895391 41957371084639 159703717
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle8 coefficients8 rank8 (by decide)
def source9 : Parameters := ⟨58,1000,25,11,79,1,2⟩
theorem shape9 : Shape source9 := by constructor <;> decide +kernel
theorem middle9 (h : ℕ) (hh : h≤11) : 79≤(source9.cutoff h+25-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source9, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients9 :
    SecondJetRelaxedGlobalCounts.coefficientCount source9.cutoff 131071 1000 25 11 79=52898428096639 := by
  decide +kernel
theorem rank9 : SecondJetRelaxedCounts.rankBound 58 1000 25 11 79=201052517 := by decide +kernel
theorem dimension9 : Dimension source9 193717080191 := by
  exact dimension_of_counts source9 193717080191 52898428096639 201052517
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle9 coefficients9 rank9 (by decide)
def source10 : Parameters := ⟨58,1200,25,11,79,1,2⟩
theorem shape10 : Shape source10 := by constructor <;> decide +kernel
theorem middle10 (h : ℕ) (hh : h≤11) : 79≤(source10.cutoff h+25-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source10, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients10 :
    SecondJetRelaxedGlobalCounts.coefficientCount source10.cutoff 131071 1200 25 11 79=63839485108639 := by
  decide +kernel
theorem rank10 : SecondJetRelaxedCounts.rankBound 58 1200 25 11 79=242401317 := by decide +kernel
theorem dimension10 : Dimension source10 295434264991 := by
  exact dimension_of_counts source10 295434264991 63839485108639 242401317
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle10 coefficients10 rank10 (by decide)
def source11 : Parameters := ⟨60,1000,25,12,82,1,2⟩
theorem shape11 : Shape source11 := by constructor <;> decide +kernel
theorem middle11 (h : ℕ) (hh : h≤12) : 82≤(source11.cutoff h+25-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source11, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients11 :
    SecondJetRelaxedGlobalCounts.coefficientCount source11.cutoff 131071 1000 25 12 82=57843985150588 := by
  decide +kernel
theorem rank11 : SecondJetRelaxedCounts.rankBound 60 1000 25 12 82=219762148 := by decide +kernel
theorem dimension11 : Dimension source11 234656625276 := by
  exact dimension_of_counts source11 234656625276 57843985150588 219762148
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle11 coefficients11 rank11 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart2
section MergedPart3
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source12 : Parameters := ⟨60,591,26,12,82,1,2⟩
theorem shape12 : Shape source12 := by constructor <;> decide +kernel
theorem middle12 (h : ℕ) (hh : h≤12) : 82≤(source12.cutoff h+26-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source12, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source13, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source14, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source15, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients15 :
    SecondJetRelaxedGlobalCounts.coefficientCount source15.cutoff 131071 2167 26 12 87=155659118846414 := by
  decide +kernel
theorem rank15 : SecondJetRelaxedCounts.rankBound 64 2167 26 12 87=593244562 := by decide +kernel
theorem dimension15 : Dimension source15 143616385486 := by
  exact dimension_of_counts source15 143616385486 155659118846414 593244562
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle15 coefficients15 rank15 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart3
section MergedPart4
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source16 : Parameters := ⟨66,2096,26,11,90,2,3⟩
theorem shape16 : Shape source16 := by constructor <;> decide +kernel
theorem middle16 (h : ℕ) (hh : h≤11) : 90≤(source16.cutoff h+26-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source16, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source17, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source18, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source19, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients19 :
    SecondJetRelaxedGlobalCounts.coefficientCount source19.cutoff 131071 1345 28 14 90=115450031410280 := by
  decide +kernel
theorem rank19 : SecondJetRelaxedCounts.rankBound 66 1345 28 14 90=440400205 := by decide +kernel
theorem dimension19 : Dimension source19 1760070760 := by
  exact dimension_of_counts source19 1760070760 115450031410280 440400205
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle19 coefficients19 rank19 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart4
section MergedPart5
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source20 : Parameters := ⟨68,1340,27,13,93,2,3⟩
theorem shape20 : Shape source20 := by constructor <;> decide +kernel
theorem middle20 (h : ℕ) (hh : h≤13) : 93≤(source20.cutoff h+27-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source20, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients20 :
    SecondJetRelaxedGlobalCounts.coefficientCount source20.cutoff 131071 1340 27 13 93=116475846429012 := by
  decide +kernel
theorem rank20 : SecondJetRelaxedCounts.rankBound 68 1340 27 13 93=444319938 := by decide +kernel
theorem dimension20 : Dimension source20 40601940 := by
  exact dimension_of_counts source20 40601940 116475846429012 444319938
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle20 coefficients20 rank20 (by decide)
def source21 : Parameters := ⟨68,1400,27,13,93,2,3⟩
theorem shape21 : Shape source21 := by constructor <;> decide +kernel
theorem middle21 (h : ℕ) (hh : h≤13) : 93≤(source21.cutoff h+27-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source21, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients21 :
    SecondJetRelaxedGlobalCounts.coefficientCount source21.cutoff 131071 1400 27 13 93=121844346691872 := by
  decide +kernel
theorem rank21 : SecondJetRelaxedCounts.rankBound 68 1400 27 13 93=464694078 := by decide +kernel
theorem dimension21 : Dimension source21 27582308640 := by
  exact dimension_of_counts source21 27582308640 121844346691872 464694078
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle21 coefficients21 rank21 (by decide)
def source22 : Parameters := ⟨68,1500,27,13,93,2,3⟩
theorem shape22 : Shape source22 := by constructor <;> decide +kernel
theorem middle22 (h : ℕ) (hh : h≤13) : 93≤(source22.cutoff h+27-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source22, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients22 :
    SecondJetRelaxedGlobalCounts.coefficientCount source22.cutoff 131071 1500 27 13 93=130791847129972 := by
  decide +kernel
theorem rank22 : SecondJetRelaxedCounts.rankBound 68 1500 27 13 93=498650978 := by decide +kernel
theorem dimension22 : Dimension source22 73485153140 := by
  exact dimension_of_counts source22 73485153140 130791847129972 498650978
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle22 coefficients22 rank22 (by decide)
def source23 : Parameters := ⟨68,1600,27,13,93,2,3⟩
theorem shape23 : Shape source23 := by constructor <;> decide +kernel
theorem middle23 (h : ℕ) (hh : h≤13) : 93≤(source23.cutoff h+27-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source23, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients23 :
    SecondJetRelaxedGlobalCounts.coefficientCount source23.cutoff 131071 1600 27 13 93=139739347568072 := by
  decide +kernel
theorem rank23 : SecondJetRelaxedCounts.rankBound 68 1600 27 13 93=532607878 := by decide +kernel
theorem dimension23 : Dimension source23 119387997640 := by
  exact dimension_of_counts source23 119387997640 139739347568072 532607878
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle23 coefficients23 rank23 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart5
section MergedPart6
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source24 : Parameters := ⟨68,1640,27,13,93,2,3⟩
theorem shape24 : Shape source24 := by constructor <;> decide +kernel
theorem middle24 (h : ℕ) (hh : h≤13) : 93≤(source24.cutoff h+27-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source24, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients24 :
    SecondJetRelaxedGlobalCounts.coefficientCount source24.cutoff 131071 1640 27 13 93=143318347743312 := by
  decide +kernel
theorem rank24 : SecondJetRelaxedCounts.rankBound 68 1640 27 13 93=546190638 := by decide +kernel
theorem dimension24 : Dimension source24 137749135440 := by
  exact dimension_of_counts source24 137749135440 143318347743312 546190638
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle24 coefficients24 rank24 (by decide)
def source25 : Parameters := ⟨68,1680,27,13,93,2,3⟩
theorem shape25 : Shape source25 := by constructor <;> decide +kernel
theorem middle25 (h : ℕ) (hh : h≤13) : 93≤(source25.cutoff h+27-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source25, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients25 :
    SecondJetRelaxedGlobalCounts.coefficientCount source25.cutoff 131071 1680 27 13 93=146897347918552 := by
  decide +kernel
theorem rank25 : SecondJetRelaxedCounts.rankBound 68 1680 27 13 93=559773398 := by decide +kernel
theorem dimension25 : Dimension source25 156110273240 := by
  exact dimension_of_counts source25 156110273240 146897347918552 559773398
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle25 coefficients25 rank25 (by decide)
def source26 : Parameters := ⟨68,1683,28,12,93,2,3⟩
theorem shape26 : Shape source26 := by constructor <;> decide +kernel
theorem middle26 (h : ℕ) (hh : h≤12) : 93≤(source26.cutoff h+28-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source26, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients26 :
    SecondJetRelaxedGlobalCounts.coefficientCount source26.cutoff 131071 1683 28 12 93=153003835417819 := by
  decide +kernel
theorem rank26 : SecondJetRelaxedCounts.rankBound 68 1683 28 12 93=582826619 := by decide +kernel
theorem dimension26 : Dimension source26 219334206683 := by
  exact dimension_of_counts source26 219334206683 153003835417819 582826619
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle26 coefficients26 rank26 (by decide)
def source27 : Parameters := ⟨76,967,31,14,104,2,3⟩
theorem shape27 : Shape source27 := by constructor <;> decide +kernel
theorem middle27 (h : ℕ) (hh : h≤14) : 104≤(source27.cutoff h+31-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source27, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients27 :
    SecondJetRelaxedGlobalCounts.coefficientCount source27.cutoff 131071 967 31 14 104=131575175268415 := by
  decide +kernel
theorem rank27 : SecondJetRelaxedCounts.rankBound 76 967 31 14 104=501917624 := by decide +kernel
theorem dimension27 : Dimension source27 481642559 := by
  exact dimension_of_counts source27 481642559 131575175268415 501917624
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle27 coefficients27 rank27 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart6
section MergedPart7
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source28 : Parameters := ⟨76,926,32,15,104,2,3⟩
theorem shape28 : Shape source28 := by constructor <;> decide +kernel
theorem middle28 (h : ℕ) (hh : h≤15) : 104≤(source28.cutoff h+32-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source28, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source29, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source30, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source31, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients31 :
    SecondJetRelaxedGlobalCounts.coefficientCount source31.cutoff 131071 871 34 15 107=143505368808972 := by
  decide +kernel
theorem rank31 : SecondJetRelaxedCounts.rankBound 78 871 34 15 107=547429171 := by decide +kernel
theorem dimension31 : Dimension source31 96206348 := by
  exact dimension_of_counts source31 96206348 143505368808972 547429171
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle31 coefficients31 rank31 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart7
section MergedPart8
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source32 : Parameters := ⟨78,869,34,16,107,2,3⟩
theorem shape32 : Shape source32 := by constructor <;> decide +kernel
theorem middle32 (h : ℕ) (hh : h≤16) : 107≤(source32.cutoff h+34-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source32, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source33, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source34, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source35, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients35 :
    SecondJetRelaxedGlobalCounts.coefficientCount source35.cutoff 131071 856 34 16 109=150774571919226 := by
  decide +kernel
theorem rank35 : SecondJetRelaxedCounts.rankBound 80 856 34 16 109=575153964 := by decide +kernel
theorem dimension35 : Dimension source35 1411180410 := by
  exact dimension_of_counts source35 1411180410 150774571919226 575153964
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle35 coefficients35 rank35 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart8
section MergedPart9
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source36 : Parameters := ⟨82,2232,34,15,112,3,4⟩
theorem shape36 : Shape source36 := by constructor <;> decide +kernel
theorem middle36 (h : ℕ) (hh : h≤15) : 112≤(source36.cutoff h+34-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source36, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients36 :
    SecondJetRelaxedGlobalCounts.coefficientCount source36.cutoff 131071 2232 34 15 112=424697136587660 := by
  decide +kernel
theorem rank36 : SecondJetRelaxedCounts.rankBound 82 2232 34 15 112=1618876085 := by decide +kernel
theorem dimension36 : Dimension source36 318484161420 := by
  exact dimension_of_counts source36 318484161420 424697136587660 1618876085
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle36 coefficients36 rank36 (by decide)
def source37 : Parameters := ⟨82,815,36,16,112,2,3⟩
theorem shape37 : Shape source37 := by constructor <;> decide +kernel
theorem middle37 (h : ℕ) (hh : h≤16) : 112≤(source37.cutoff h+36-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source37, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients37 :
    SecondJetRelaxedGlobalCounts.coefficientCount source37.cutoff 131071 815 36 16 112=163990216271279 := by
  decide +kernel
theorem rank37 : SecondJetRelaxedCounts.rankBound 82 815 36 16 112=625567910 := by decide +kernel
theorem dimension37 : Dimension source37 1342072239 := by
  exact dimension_of_counts source37 1342072239 163990216271279 625567910
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle37 coefficients37 rank37 (by decide)
def source38 : Parameters := ⟨82,2103,36,16,112,3,4⟩
theorem shape38 : Shape source38 := by constructor <;> decide +kernel
theorem middle38 (h : ℕ) (hh : h≤16) : 112≤(source38.cutoff h+36-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source38, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients38 :
    SecondJetRelaxedGlobalCounts.coefficientCount source38.cutoff 131071 2103 36 16 112=436710695110703 := by
  decide +kernel
theorem rank38 : SecondJetRelaxedCounts.rankBound 82 2103 36 16 112=1664811318 := by decide +kernel
theorem dimension38 : Dimension source38 290396964911 := by
  exact dimension_of_counts source38 290396964911 436710695110703 1664811318
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle38 coefficients38 rank38 (by decide)
def source39 : Parameters := ⟨84,2213,34,15,115,3,4⟩
theorem shape39 : Shape source39 := by constructor <;> decide +kernel
theorem middle39 (h : ℕ) (hh : h≤15) : 115≤(source39.cutoff h+34-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source39, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients39 :
    SecondJetRelaxedGlobalCounts.coefficientCount source39.cutoff 131071 2213 34 15 115=445273896268892 := by
  decide +kernel
theorem rank39 : SecondJetRelaxedCounts.rankBound 84 2213 34 15 115=1696905609 := by decide +kernel
theorem dimension39 : Dimension source39 440272303196 := by
  exact dimension_of_counts source39 440272303196 445273896268892 1696905609
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle39 coefficients39 rank39 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart9
section MergedPart10
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source40 : Parameters := ⟨84,1623,36,16,115,3,4⟩
theorem shape40 : Shape source40 := by constructor <;> decide +kernel
theorem middle40 (h : ℕ) (hh : h≤16) : 115≤(source40.cutoff h+36-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source40, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients40 :
    SecondJetRelaxedGlobalCounts.coefficientCount source40.cutoff 131071 1623 36 16 115=354171654136457 := by
  decide +kernel
theorem rank40 : SecondJetRelaxedCounts.rankBound 84 1623 36 16 115=1351056981 := by decide +kernel
theorem dimension40 : Dimension source40 172909193 := by
  exact dimension_of_counts source40 172909193 354171654136457 1351056981
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle40 coefficients40 rank40 (by decide)
def source41 : Parameters := ⟨84,1902,36,16,115,3,4⟩
theorem shape41 : Shape source41 := by constructor <;> decide +kernel
theorem middle41 (h : ℕ) (hh : h≤16) : 115≤(source41.cutoff h+36-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source41, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients41 :
    SecondJetRelaxedGlobalCounts.coefficientCount source41.cutoff 131071 1902 36 16 115=416920853559563 := by
  decide +kernel
theorem rank41 : SecondJetRelaxedCounts.rankBound 84 1902 36 16 115=1589225610 := by decide +kernel
theorem dimension41 : Dimension source41 314895251723 := by
  exact dimension_of_counts source41 314895251723 416920853559563 1589225610
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle41 coefficients41 rank41 (by decide)
def source42 : Parameters := ⟨84,2138,36,16,115,3,4⟩
theorem shape42 : Shape source42 := by constructor <;> decide +kernel
theorem middle42 (h : ℕ) (hh : h≤16) : 115≤(source42.cutoff h+36-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source42, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients42 :
    SecondJetRelaxedGlobalCounts.coefficientCount source42.cutoff 131071 2138 36 16 115=469999029415667 := by
  decide +kernel
theorem rank42 : SecondJetRelaxedCounts.rankBound 84 2138 36 16 115=1790687246 := by decide +kernel
theorem dimension42 : Dimension source42 581112000243 := by
  exact dimension_of_counts source42 581112000243 469999029415667 1790687246
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle42 coefficients42 rank42 (by decide)
def source43 : Parameters := ⟨84,2131,36,17,115,3,4⟩
theorem shape43 : Shape source43 := by constructor <;> decide +kernel
theorem middle43 (h : ℕ) (hh : h≤17) : 115≤(source43.cutoff h+36-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source43, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients43 :
    SecondJetRelaxedGlobalCounts.coefficientCount source43.cutoff 131071 2131 36 17 115=472316662530566 := by
  decide +kernel
theorem rank43 : SecondJetRelaxedCounts.rankBound 84 2131 36 17 115=1799540541 := by decide +kernel
theorem dimension43 : Dimension source43 577906950662 := by
  exact dimension_of_counts source43 577906950662 472316662530566 1799540541
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle43 coefficients43 rank43 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart10
section MergedPart11
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source44 : Parameters := ⟨84,2259,36,17,115,3,4⟩
theorem shape44 : Shape source44 := by constructor <;> decide +kernel
theorem middle44 (h : ℕ) (hh : h≤17) : 115≤(source44.cutoff h+36-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source44, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source45, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source46, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source47, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients47 :
    SecondJetRelaxedGlobalCounts.coefficientCount source47.cutoff 131071 2108 36 17 117=493507628530001 := by
  decide +kernel
theorem rank47 : SecondJetRelaxedCounts.rankBound 86 2108 36 17 117=1879663641 := by decide +kernel
theorem dimension47 : Dimension source47 765083023697 := by
  exact dimension_of_counts source47 765083023697 493507628530001 1879663641
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle47 coefficients47 rank47 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart11
section MergedPart12
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source48 : Parameters := ⟨86,1968,38,17,117,3,4⟩
theorem shape48 : Shape source48 := by constructor <;> decide +kernel
theorem middle48 (h : ℕ) (hh : h≤17) : 117≤(source48.cutoff h+38-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source48, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source49, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source50, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source51, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients51 :
    SecondJetRelaxedGlobalCounts.coefficientCount source51.cutoff 131071 1895 36 17 120=466759464986876 := by
  decide +kernel
theorem rank51 : SecondJetRelaxedCounts.rankBound 88 1895 36 17 120=1778166957 := by decide +kernel
theorem dimension51 : Dimension source51 623666211068 := by
  exact dimension_of_counts source51 623666211068 466759464986876 1778166957
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle51 coefficients51 rank51 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart12
section MergedPart13
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source52 : Parameters := ⟨90,1306,39,18,123,3,4⟩
theorem shape52 : Shape source52 := by constructor <;> decide +kernel
theorem middle52 (h : ℕ) (hh : h≤18) : 123≤(source52.cutoff h+39-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source52, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source53, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source54, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source55, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients55 :
    SecondJetRelaxedGlobalCounts.coefficientCount source55.cutoff 131071 1190 41 19 128=409652509445663 := by
  decide +kernel
theorem rank55 : SecondJetRelaxedCounts.rankBound 94 1190 41 19 128=1562699433 := by decide +kernel
theorem dimension55 : Dimension source55 229281311 := by
  exact dimension_of_counts source55 229281311 409652509445663 1562699433
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle55 coefficients55 rank55 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart13
section MergedPart14
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source56 : Parameters := ⟨98,1108,43,20,134,3,4⟩
theorem shape56 : Shape source56 := by constructor <;> decide +kernel
theorem middle56 (h : ℕ) (hh : h≤20) : 134≤(source56.cutoff h+43-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source56, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source57, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source58, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source59, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients59 :
    SecondJetRelaxedGlobalCounts.coefficientCount source59.cutoff 131071 1003 47 21 148=579050041635048 := by
  decide +kernel
theorem rank59 : SecondJetRelaxedCounts.rankBound 108 1003 47 21 148=2208888878 := by decide +kernel
theorem dimension59 : Dimension source59 3075600616 := by
  exact dimension_of_counts source59 3075600616 579050041635048 2208888878
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle59 coefficients59 rank59 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart14
section MergedPart15
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source60 : Parameters := ⟨112,3686,45,20,152,5,7⟩
theorem shape60 : Shape source60 := by constructor <;> decide +kernel
theorem middle60 (h : ℕ) (hh : h≤20) : 152≤(source60.cutoff h+45-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source60, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients60 :
    SecondJetRelaxedGlobalCounts.coefficientCount source60.cutoff 131071 3686 45 20 152=2249479125216988 := by
  decide +kernel
theorem rank60 : SecondJetRelaxedCounts.rankBound 112 3686 45 20 152=8581076106 := by decide +kernel
theorem dimension60 : Dimension source60 1510485724 := by
  exact dimension_of_counts source60 1510485724 2249479125216988 8581076106
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle60 coefficients60 rank60 (by decide)
def source61 : Parameters := ⟨113,3378,46,21,153,5,7⟩
theorem shape61 : Shape source61 := by constructor <;> decide +kernel
theorem middle61 (h : ℕ) (hh : h≤21) : 153≤(source61.cutoff h+46-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source61, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients61 :
    SecondJetRelaxedGlobalCounts.coefficientCount source61.cutoff 131071 3378 46 21 153=2184636438284102 := by
  decide +kernel
theorem rank61 : SecondJetRelaxedCounts.rankBound 113 3378 46 21 153=8333726260 := by decide +kernel
theorem dimension61 : Dimension source61 101582662 := by
  exact dimension_of_counts source61 101582662 2184636438284102 8333726260
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle61 coefficients61 rank61 (by decide)
def source62 : Parameters := ⟨114,3146,47,21,154,5,7⟩
theorem shape62 : Shape source62 := by constructor <;> decide +kernel
theorem middle62 (h : ℕ) (hh : h≤21) : 154≤(source62.cutoff h+47-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source62, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients62 :
    SecondJetRelaxedGlobalCounts.coefficientCount source62.cutoff 131071 3146 47 21 154=2137585483518867 := by
  decide +kernel
theorem rank62 : SecondJetRelaxedCounts.rankBound 114 3146 47 21 154=8154240246 := by decide +kernel
theorem dimension62 : Dimension source62 328471443 := by
  exact dimension_of_counts source62 328471443 2137585483518867 8154240246
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle62 coefficients62 rank62 (by decide)
def source63 : Parameters := ⟨120,1405,54,25,164,4,5⟩
theorem shape63 : Shape source63 := by constructor <;> decide +kernel
theorem middle63 (h : ℕ) (hh : h≤25) : 164≤(source63.cutoff h+54-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source63, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients63 :
    SecondJetRelaxedGlobalCounts.coefficientCount source63.cutoff 131071 1405 54 25 164=1311372005594373 := by
  decide +kernel
theorem rank63 : SecondJetRelaxedCounts.rankBound 120 1405 54 25 164=4999133419 := by decide +kernel
theorem dimension63 : Dimension source63 879174604037 := by
  exact dimension_of_counts source63 879174604037 1311372005594373 4999133419
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle63 coefficients63 rank63 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart15
section MergedPart16
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source64 : Parameters := ⟨128,3734,53,24,174,6,8⟩
theorem shape64 : Shape source64 := by constructor <;> decide +kernel
theorem middle64 (h : ℕ) (hh : h≤24) : 174≤(source64.cutoff h+53-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source64, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients64 :
    SecondJetRelaxedGlobalCounts.coefficientCount source64.cutoff 131071 3734 53 24 174=4029055746580152 := by
  decide +kernel
theorem rank64 : SecondJetRelaxedCounts.rankBound 128 3734 53 24 174=15369613990 := by decide +kernel
theorem dimension64 : Dimension source64 3656785592 := by
  exact dimension_of_counts source64 3656785592 4029055746580152 15369613990
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle64 coefficients64 rank64 (by decide)
def source65 : Parameters := ⟨129,3680,53,25,175,6,8⟩
theorem shape65 : Shape source65 := by constructor <;> decide +kernel
theorem middle65 (h : ℕ) (hh : h≤25) : 175≤(source65.cutoff h+53-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source65, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients65 :
    SecondJetRelaxedGlobalCounts.coefficientCount source65.cutoff 131071 3680 53 25 175=4063748936792714 := by
  decide +kernel
theorem rank65 : SecondJetRelaxedCounts.rankBound 129 3680 53 25 175=15501968380 := by decide +kernel
theorem dimension65 : Dimension source65 937785994 := by
  exact dimension_of_counts source65 937785994 4063748936792714 15501968380
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle65 coefficients65 rank65 (by decide)
def source66 : Parameters := ⟨130,3618,53,24,176,6,8⟩
theorem shape66 : Shape source66 := by constructor <;> decide +kernel
theorem middle66 (h : ℕ) (hh : h≤24) : 176≤(source66.cutoff h+53-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source66, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients66 :
    SecondJetRelaxedGlobalCounts.coefficientCount source66.cutoff 131071 3618 53 24 176=4045135712180991 := by
  decide +kernel
theorem rank66 : SecondJetRelaxedCounts.rankBound 130 3618 53 24 176=15430961278 := by decide +kernel
theorem dimension66 : Dimension source66 1798920959 := by
  exact dimension_of_counts source66 1798920959 4045135712180991 15430961278
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle66 coefficients66 rank66 (by decide)
def source67 : Parameters := ⟨130,3543,53,24,177,6,8⟩
theorem shape67 : Shape source67 := by constructor <;> decide +kernel
theorem middle67 (h : ℕ) (hh : h≤24) : 177≤(source67.cutoff h+53-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source67, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients67 :
    SecondJetRelaxedGlobalCounts.coefficientCount source67.cutoff 131071 3543 53 24 177=3959844937245224 := by
  decide +kernel
theorem rank67 : SecondJetRelaxedCounts.rankBound 130 3543 53 24 177=15105604012 := by decide +kernel
theorem dimension67 : Dimension source67 1479123496 := by
  exact dimension_of_counts source67 1479123496 3959844937245224 15105604012
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle67 coefficients67 rank67 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart16
section MergedPart17
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source68 : Parameters := ⟨140,1226,58,27,192,4,5⟩
theorem shape68 : Shape source68 := by constructor <;> decide +kernel
theorem middle68 (h : ℕ) (hh : h≤27) : 192≤(source68.cutoff h+58-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source68, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients68 :
    SecondJetRelaxedGlobalCounts.coefficientCount source68.cutoff 131071 1226 58 27 192=1814324904887663 := by
  decide +kernel
theorem rank68 : SecondJetRelaxedCounts.rankBound 140 1226 58 27 192=6921026674 := by decide +kernel
theorem dimension68 : Dimension source68 19288458607 := by
  exact dimension_of_counts source68 19288458607 1814324904887663 6921026674
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle68 coefficients68 rank68 (by decide)
def source69 : Parameters := ⟨140,1231,58,27,192,4,5⟩
theorem shape69 : Shape source69 := by constructor <;> decide +kernel
theorem middle69 (h : ℕ) (hh : h≤27) : 192≤(source69.cutoff h+58-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source69, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients69 :
    SecondJetRelaxedGlobalCounts.coefficientCount source69.cutoff 131071 1231 58 27 192=1822246912208023 := by
  decide +kernel
theorem rank69 : SecondJetRelaxedCounts.rankBound 140 1231 58 27 192=6950888619 := by decide +kernel
theorem dimension69 : Dimension source69 113166068887 := by
  exact dimension_of_counts source69 113166068887 1822246912208023 6950888619
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle69 coefficients69 rank69 (by decide)
def source70 : Parameters := ⟨140,1178,60,28,192,4,5⟩
theorem shape70 : Shape source70 := by constructor <;> decide +kernel
theorem middle70 (h : ℕ) (hh : h≤28) : 192≤(source70.cutoff h+60-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source70, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients70 :
    SecondJetRelaxedGlobalCounts.coefficientCount source70.cutoff 131071 1178 60 28 192=1833713039376830 := by
  decide +kernel
theorem rank70 : SecondJetRelaxedCounts.rankBound 140 1178 60 28 192=6995050875 := by decide +kernel
theorem dimension70 : Dimension source70 2422800830 := by
  exact dimension_of_counts source70 2422800830 1833713039376830 6995050875
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle70 coefficients70 rank70 (by decide)
def source71 : Parameters := ⟨140,1179,60,28,192,4,5⟩
theorem shape71 : Shape source71 := by constructor <;> decide +kernel
theorem middle71 (h : ℕ) (hh : h≤28) : 192≤(source71.cutoff h+60-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source71, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients71 :
    SecondJetRelaxedGlobalCounts.coefficientCount source71.cutoff 131071 1179 60 28 192=1835385307375790 := by
  decide +kernel
theorem rank71 : SecondJetRelaxedCounts.rankBound 140 1179 60 28 192=7001352760 := by decide +kernel
theorem dimension71 : Dimension source71 22689458350 := by
  exact dimension_of_counts source71 22689458350 1835385307375790 7001352760
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle71 coefficients71 rank71 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart17
section MergedPart18
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source72 : Parameters := ⟨140,1180,60,28,192,4,5⟩
theorem shape72 : Shape source72 := by constructor <;> decide +kernel
theorem middle72 (h : ℕ) (hh : h≤28) : 192≤(source72.cutoff h+60-1)/131071 := by
  interval_cases h <;>
    first
      | decide
      | norm_num [source72, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source73, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
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
  interval_cases h <;>
    first
      | decide
      | norm_num [source74, Parameters.cutoff,
          SecondJetRelaxedDifferentiation.reserve]
theorem coefficients74 :
    SecondJetRelaxedGlobalCounts.coefficientCount source74.cutoff 131071 1119 70 33 219=3003373702637497 := by
  decide +kernel
theorem rank74 : SecondJetRelaxedCounts.rankBound 160 1119 70 33 219=11456869645 := by decide +kernel
theorem dimension74 : Dimension source74 24066418617 := by
  exact dimension_of_counts source74 24066418617 3003373702637497 11456869645
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle74 coefficients74 rank74 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
end MergedPart18
