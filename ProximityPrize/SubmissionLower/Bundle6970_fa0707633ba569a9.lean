import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0643

section Pack_R6970Height2313CommonRanks24

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks24_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2789_614 :
    P1_7_1.groupedPoleMoment 2789 614 ≤ 1684443651648 :=
  _root_.PoleAffine6970.certified 2789 614 1684443651648 (by decide) (by decide +kernel)

private theorem pole_2789_630 :
    P1_7_1.groupedPoleMoment 2789 630 ≤ 1718433691636 :=
  _root_.Research6969.PackedRanks.TerminalRanks20To23.moment2789_630

private theorem pole_2790_630 :
    P1_7_1.groupedPoleMoment 2790 630 ≤ 1720419448636 :=
  _root_.Research6969.PackedRanks.TerminalRanks20To23.moment2790_630

private theorem pole_2862_622 :
    P1_7_1.groupedPoleMoment 2862 622 ≤ 1849053003955 :=
  _root_.PoleAffine6970.certified 2862 622 1849053003955 (by decide) (by decide +kernel)

private theorem pole_2897_645 :
    P1_7_1.groupedPoleMoment 2897 645 ≤ 1977925731872 :=
  _root_.PoleAffine6970.certified 2897 645 1977925731872 (by decide) (by decide +kernel)

private theorem pole_2898_632 :
    P1_7_1.groupedPoleMoment 2898 632 ≤ 1949015201860 :=
  _root_.PoleAffine6970.certified 2898 632 1949015201860 (by decide) (by decide +kernel)

private theorem pole_2898_645 :
    P1_7_1.groupedPoleMoment 2898 645 ≤ 1980125251083 :=
  _root_.PoleAffine6970.certified 2898 645 1980125251083 (by decide) (by decide +kernel)

private theorem pole_2906_632 :
    P1_7_1.groupedPoleMoment 2906 632 ≤ 1966383525068 :=
  _root_.PoleAffine6970.certified 2906 632 1966383525068 (by decide) (by decide +kernel)

private theorem pole_2913_645 :
    P1_7_1.groupedPoleMoment 2913 645 ≤ 2013318131288 :=
  _root_.PoleAffine6970.certified 2913 645 2013318131288 (by decide) (by decide +kernel)

private theorem pole_2914_622 :
    P1_7_1.groupedPoleMoment 2914 622 ≤ 1959329457697 :=
  _root_.PoleAffine6970.certified 2914 622 1959329457697 (by decide) (by decide +kernel)

theorem bank_2008_2789_614 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2008,2789,614,u⟩,246075572879360,1684443651648⟩ :=
  pack_R6970Height2313CommonRanks24_bank_checked 2008 2789 614 u 246075572879360 1684443651648
    (by decide) (by decide) (by decide) (by decide) pole_2789_614

theorem bank_2007_2789_630 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2007,2789,630,u⟩,250638203092992,1718433691636⟩ :=
  pack_R6970Height2313CommonRanks24_bank_checked 2007 2789 630 u 250638203092992 1718433691636
    (by decide) (by decide) (by decide) (by decide) pole_2789_630

theorem bank_2006_2790_630 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2006,2790,630,u⟩,250358324527104,1720419448636⟩ :=
  pack_R6970Height2313CommonRanks24_bank_checked 2006 2790 630 u 250358324527104 1720419448636
    (by decide) (by decide) (by decide) (by decide) pole_2790_630

theorem bank_2060_2862_622 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2060,2862,622,u⟩,263139991224320,1849053003955⟩ :=
  pack_R6970Height2313CommonRanks24_bank_checked 2060 2862 622 u 263139991224320 1849053003955
    (by decide) (by decide) (by decide) (by decide) pole_2862_622

theorem bank_2087_2897_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2087,2897,645,u⟩,278496867254272,1977925731872⟩ :=
  pack_R6970Height2313CommonRanks24_bank_checked 2087 2897 645 u 278496867254272 1977925731872
    (by decide) (by decide) (by decide) (by decide) pole_2897_645

theorem bank_2077_2898_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2077,2898,632,u⟩,271293581361152,1949015201860⟩ :=
  pack_R6970Height2313CommonRanks24_bank_checked 2077 2898 632 u 271293581361152 1949015201860
    (by decide) (by decide) (by decide) (by decide) pole_2898_632

theorem bank_2086_2898_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2086,2898,632,u⟩,273930986455040,1949015201860⟩ :=
  pack_R6970Height2313CommonRanks24_bank_checked 2086 2898 632 u 273930986455040 1949015201860
    (by decide) (by decide) (by decide) (by decide) pole_2898_632

theorem bank_2087_2898_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2087,2898,645,u⟩,278496867254272,1980125251083⟩ :=
  pack_R6970Height2313CommonRanks24_bank_checked 2087 2898 645 u 278496867254272 1980125251083
    (by decide) (by decide) (by decide) (by decide) pole_2898_645

theorem bank_2085_2906_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2085,2906,632,u⟩,273637277696000,1966383525068⟩ :=
  pack_R6970Height2313CommonRanks24_bank_checked 2085 2906 632 u 273637277696000 1966383525068
    (by decide) (by decide) (by decide) (by decide) pole_2906_632

theorem bank_2101_2913_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2101,2913,645,u⟩,282697978609664,2013318131288⟩ :=
  pack_R6970Height2313CommonRanks24_bank_checked 2101 2913 645 u 282697978609664 2013318131288
    (by decide) (by decide) (by decide) (by decide) pole_2913_645

theorem bank_2100_2913_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2100,2913,645,u⟩,282396798484480,2013318131288⟩ :=
  pack_R6970Height2313CommonRanks24_bank_checked 2100 2913 645 u 282396798484480 2013318131288
    (by decide) (by decide) (by decide) (by decide) pole_2913_645

theorem bank_2088_2914_622 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2088,2914,622,u⟩,271204194451456,1959329457697⟩ :=
  pack_R6970Height2313CommonRanks24_bank_checked 2088 2914 622 u 271204194451456 1959329457697
    (by decide) (by decide) (by decide) (by decide) pole_2914_622

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks24

section Pack_R6970Height2313CommonRanks29

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks29_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3177_702 :
    P1_7_1.groupedPoleMoment 3177 702 ≤ 2843261695012 :=
  _root_.PoleAffine6970.certified 3177 702 2843261695012 (by decide) (by decide +kernel)

private theorem pole_3180_702 :
    P1_7_1.groupedPoleMoment 3180 702 ≤ 2851915272809 :=
  _root_.PoleAffine6970.certified 3180 702 2851915272809 (by decide) (by decide +kernel)

private theorem pole_3182_702 :
    P1_7_1.groupedPoleMoment 3182 702 ≤ 2857694270952 :=
  _root_.PoleAffine6970.certified 3182 702 2857694270952 (by decide) (by decide +kernel)

private theorem pole_3190_708 :
    P1_7_1.groupedPoleMoment 3190 708 ≤ 2900018359096 :=
  _root_.PoleAffine6970.certified 3190 708 2900018359096 (by decide) (by decide +kernel)

private theorem pole_3194_710 :
    P1_7_1.groupedPoleMoment 3194 710 ≤ 2918134856643 :=
  _root_.PoleAffine6970.certified 3194 710 2918134856643 (by decide) (by decide +kernel)

private theorem pole_3199_701 :
    P1_7_1.groupedPoleMoment 3199 701 ≤ 2903914168659 :=
  _root_.PoleAffine6970.certified 3199 701 2903914168659 (by decide) (by decide +kernel)

private theorem pole_3199_702 :
    P1_7_1.groupedPoleMoment 3199 702 ≤ 2907137852544 :=
  _root_.PoleAffine6970.certified 3199 702 2907137852544 (by decide) (by decide +kernel)

private theorem pole_3201_702 :
    P1_7_1.groupedPoleMoment 3201 702 ≤ 2912992731804 :=
  _root_.Research6969.PackedRanks.TerminalRanks20To23.moment3201_702

private theorem pole_3202_702 :
    P1_7_1.groupedPoleMoment 3202 702 ≤ 2915923177462 :=
  _root_.PoleAffine6970.certified 3202 702 2915923177462 (by decide) (by decide +kernel)

private theorem pole_3202_704 :
    P1_7_1.groupedPoleMoment 3202 704 ≤ 2922386046475 :=
  _root_.PoleAffine6970.certified 3202 704 2922386046475 (by decide) (by decide +kernel)

theorem bank_2288_3177_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2288,3177,702,u⟩,364872686370816,2843261695012⟩ :=
  pack_R6970Height2313CommonRanks29_bank_checked 2288 3177 702 u 364872686370816 2843261695012
    (by decide) (by decide) (by decide) (by decide) pole_3177_702

theorem bank_2290_3180_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2290,3180,702,u⟩,365587167969280,2851915272809⟩ :=
  pack_R6970Height2313CommonRanks29_bank_checked 2290 3180 702 u 365587167969280 2851915272809
    (by decide) (by decide) (by decide) (by decide) pole_3180_702

theorem bank_2292_3182_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2292,3182,702,u⟩,366302386716672,2857694270952⟩ :=
  pack_R6970Height2313CommonRanks29_bank_checked 2292 3182 702 u 366302386716672 2857694270952
    (by decide) (by decide) (by decide) (by decide) pole_3182_702

theorem bank_2302_3190_708 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2302,3190,708,u⟩,372287251152896,2900018359096⟩ :=
  pack_R6970Height2313CommonRanks29_bank_checked 2302 3190 708 u 372287251152896 2900018359096
    (by decide) (by decide) (by decide) (by decide) pole_3190_708

theorem bank_2301_3194_710 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2301,3194,710,u⟩,372721737007104,2918134856643⟩ :=
  pack_R6970Height2313CommonRanks29_bank_checked 2301 3194 710 u 372721737007104 2918134856643
    (by decide) (by decide) (by decide) (by decide) pole_3194_710

theorem bank_2296_3199_701 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2296,3199,701,u⟩,367337109454848,2903914168659⟩ :=
  pack_R6970Height2313CommonRanks29_bank_checked 2296 3199 701 u 367337109454848 2903914168659
    (by decide) (by decide) (by decide) (by decide) pole_3199_701

theorem bank_2303_3199_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2303,3199,702,u⟩,370249266364416,2907137852544⟩ :=
  pack_R6970Height2313CommonRanks29_bank_checked 2303 3199 702 u 370249266364416 2907137852544
    (by decide) (by decide) (by decide) (by decide) pole_3199_702

theorem bank_2305_3201_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2305,3201,702,u⟩,370969276579840,2912992731804⟩ :=
  pack_R6970Height2313CommonRanks29_bank_checked 2305 3201 702 u 370969276579840 2912992731804
    (by decide) (by decide) (by decide) (by decide) pole_3201_702

theorem bank_2305_3202_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2305,3202,702,u⟩,370969276579840,2915923177462⟩ :=
  pack_R6970Height2313CommonRanks29_bank_checked 2305 3202 702 u 370969276579840 2915923177462
    (by decide) (by decide) (by decide) (by decide) pole_3202_702

theorem bank_2306_3202_704 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2306,3202,704,u⟩,372133088460800,2922386046475⟩ :=
  pack_R6970Height2313CommonRanks29_bank_checked 2306 3202 704 u 372133088460800 2922386046475
    (by decide) (by decide) (by decide) (by decide) pole_3202_704

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks29
