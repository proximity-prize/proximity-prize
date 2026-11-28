import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0644
import ProximityPrize.SubmissionLower.Z6969Pack0650

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3206_724 :
    P1_7_1.groupedPoleMoment 3206 724 ≤ 2998712046218 :=
  _root_.Research6969.PackedRanks.TerminalRanks28To31.moment3206_724

private theorem pole_3207_702 :
    P1_7_1.groupedPoleMoment 3207 702 ≤ 2930605494152 :=
  _root_.Research6969.PackedRanks.TerminalRanks28To31.moment3207_702

private theorem pole_3207_710 :
    P1_7_1.groupedPoleMoment 3207 710 ≤ 2956554353577 :=
  _root_.PoleAffine6970.certified 3207 710 2956554353577 (by decide) (by decide +kernel)

private theorem pole_3207_714 :
    P1_7_1.groupedPoleMoment 3207 714 ≤ 2969491350551 :=
  _root_.PoleAffine6970.certified 3207 714 2969491350551 (by decide) (by decide +kernel)

private theorem pole_3207_720 :
    P1_7_1.groupedPoleMoment 3207 720 ≤ 2988850718069 :=
  _root_.PoleAffine6970.certified 3207 720 2988850718069 (by decide) (by decide +kernel)

private theorem pole_3207_722 :
    P1_7_1.groupedPoleMoment 3207 722 ≤ 2995291656973 :=
  _root_.PoleAffine6970.certified 3207 722 2995291656973 (by decide) (by decide +kernel)

private theorem pole_3207_724 :
    P1_7_1.groupedPoleMoment 3207 724 ≤ 3001726552718 :=
  _root_.Research6969.PackedRanks.TerminalRanks32To35.moment3207_724

private theorem pole_3208_703 :
    P1_7_1.groupedPoleMoment 3208 703 ≤ 2936800480322 :=
  _root_.PoleAffine6970.certified 3208 703 2936800480322 (by decide) (by decide +kernel)

private theorem pole_3208_724 :
    P1_7_1.groupedPoleMoment 3208 724 ≤ 3004743122568 :=
  _root_.Research6969.PackedRanks.TerminalRanks32To35.moment3208_724

private theorem pole_3209_702 :
    P1_7_1.groupedPoleMoment 3209 702 ≤ 2936492475204 :=
  _root_.Research6969.PackedRanks.TerminalRanks36To39.moment3209_702

theorem bank_2305_3206_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2305,3206,724,u⟩,379747886694400,2998712046218⟩ :=
  bank_checked 2305 3206 724 u 379747886694400 2998712046218
    (by decide) (by decide) (by decide) (by decide) pole_3206_724

theorem bank_2308_3206_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2308,3206,724,u⟩,380856854118400,2998712046218⟩ :=
  bank_checked 2308 3206 724 u 380856854118400 2998712046218
    (by decide) (by decide) (by decide) (by decide) pole_3206_724

theorem bank_2312_3206_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2312,3206,724,u⟩,382338138112000,2998712046218⟩ :=
  bank_checked 2312 3206 724 u 382338138112000 2998712046218
    (by decide) (by decide) (by decide) (by decide) pole_3206_724

theorem bank_2302_3206_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2302,3206,724,u⟩,378640629760000,2998712046218⟩ :=
  bank_checked 2302 3206 724 u 378640629760000 2998712046218
    (by decide) (by decide) (by decide) (by decide) pole_3206_724

theorem bank_2302_3207_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2302,3207,702,u⟩,369889537687552,2930605494152⟩ :=
  bank_checked 2302 3207 702 u 369889537687552 2930605494152
    (by decide) (by decide) (by decide) (by decide) pole_3207_702

theorem bank_2303_3207_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2303,3207,702,u⟩,370249266364416,2930605494152⟩ :=
  bank_checked 2303 3207 702 u 370249266364416 2930605494152
    (by decide) (by decide) (by decide) (by decide) pole_3207_702

theorem bank_2306_3207_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2306,3207,702,u⟩,371329558118400,2930605494152⟩ :=
  bank_checked 2306 3207 702 u 371329558118400 2930605494152
    (by decide) (by decide) (by decide) (by decide) pole_3207_702

theorem bank_2305_3207_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2305,3207,702,u⟩,370969276579840,2930605494152⟩ :=
  bank_checked 2305 3207 702 u 370969276579840 2930605494152
    (by decide) (by decide) (by decide) (by decide) pole_3207_702

theorem bank_2307_3207_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2307,3207,702,u⟩,371690023944192,2930605494152⟩ :=
  bank_checked 2307 3207 702 u 371690023944192 2930605494152
    (by decide) (by decide) (by decide) (by decide) pole_3207_702

theorem bank_2304_3207_710 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2304,3207,710,u⟩,373810967347200,2956554353577⟩ :=
  bank_checked 2304 3207 710 u 373810967347200 2956554353577
    (by decide) (by decide) (by decide) (by decide) pole_3207_710

theorem bank_2311_3207_714 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2311,3207,714,u⟩,377966061158400,2969491350551⟩ :=
  bank_checked 2311 3207 714 u 377966061158400 2969491350551
    (by decide) (by decide) (by decide) (by decide) pole_3207_714

theorem bank_2311_3207_720 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2311,3207,720,u⟩,380369684660224,2988850718069⟩ :=
  bank_checked 2311 3207 720 u 380369684660224 2988850718069
    (by decide) (by decide) (by decide) (by decide) pole_3207_720

theorem bank_2311_3207_722 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2311,3207,722,u⟩,381169062379520,2995291656973⟩ :=
  bank_checked 2311 3207 722 u 381169062379520 2995291656973
    (by decide) (by decide) (by decide) (by decide) pole_3207_722

theorem bank_2303_3207_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2303,3207,724,u⟩,379009525350400,3001726552718⟩ :=
  bank_checked 2303 3207 724 u 379009525350400 3001726552718
    (by decide) (by decide) (by decide) (by decide) pole_3207_724

theorem bank_2306_3207_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2306,3207,724,u⟩,380117352448000,3001726552718⟩ :=
  bank_checked 2306 3207 724 u 380117352448000 3001726552718
    (by decide) (by decide) (by decide) (by decide) pole_3207_724

theorem bank_2312_3207_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2312,3207,724,u⟩,382338138112000,3001726552718⟩ :=
  bank_checked 2312 3207 724 u 382338138112000 3001726552718
    (by decide) (by decide) (by decide) (by decide) pole_3207_724

theorem bank_2302_3207_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2302,3207,724,u⟩,378640629760000,3001726552718⟩ :=
  bank_checked 2302 3207 724 u 378640629760000 3001726552718
    (by decide) (by decide) (by decide) (by decide) pole_3207_724

theorem bank_2308_3207_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2308,3207,724,u⟩,380856854118400,3001726552718⟩ :=
  bank_checked 2308 3207 724 u 380856854118400 3001726552718
    (by decide) (by decide) (by decide) (by decide) pole_3207_724

theorem bank_2307_3207_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2307,3207,724,u⟩,380487008256000,3001726552718⟩ :=
  bank_checked 2307 3207 724 u 380487008256000 3001726552718
    (by decide) (by decide) (by decide) (by decide) pole_3207_724

theorem bank_2305_3207_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2305,3207,724,u⟩,379747886694400,3001726552718⟩ :=
  bank_checked 2305 3207 724 u 379747886694400 3001726552718
    (by decide) (by decide) (by decide) (by decide) pole_3207_724

theorem bank_2309_3208_703 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2309,3208,703,u⟩,372814653685760,2936800480322⟩ :=
  bank_checked 2309 3208 703 u 372814653685760 2936800480322
    (by decide) (by decide) (by decide) (by decide) pole_3208_703

theorem bank_2305_3208_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2305,3208,724,u⟩,379747886694400,3004743122568⟩ :=
  bank_checked 2305 3208 724 u 379747886694400 3004743122568
    (by decide) (by decide) (by decide) (by decide) pole_3208_724

theorem bank_2313_3208_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2313,3208,724,u⟩,382708934246400,3004743122568⟩ :=
  bank_checked 2313 3208 724 u 382708934246400 3004743122568
    (by decide) (by decide) (by decide) (by decide) pole_3208_724

theorem bank_2302_3208_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2302,3208,724,u⟩,378640629760000,3004743122568⟩ :=
  bank_checked 2302 3208 724 u 378640629760000 3004743122568
    (by decide) (by decide) (by decide) (by decide) pole_3208_724

theorem bank_2303_3208_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2303,3208,724,u⟩,379009525350400,3004743122568⟩ :=
  bank_checked 2303 3208 724 u 379009525350400 3004743122568
    (by decide) (by decide) (by decide) (by decide) pole_3208_724

theorem bank_2307_3209_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2307,3209,702,u⟩,371690023944192,2936492475204⟩ :=
  bank_checked 2307 3209 702 u 371690023944192 2936492475204
    (by decide) (by decide) (by decide) (by decide) pole_3209_702

end Research6970.Height2313.CommonBankRanks
