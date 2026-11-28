import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0598
import ProximityPrize.SubmissionLower.Z6969Pack0599

section Pack_R6970Height2313CommonRanks57

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks57_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_4461_967 :
    P1_7_1.groupedPoleMoment 4461 967 ≤ 10880883913449 :=
  _root_.PoleAffine6970.certified 4461 967 10880883913449 (by decide) (by decide +kernel)

private theorem pole_4462_963 :
    P1_7_1.groupedPoleMoment 4462 963 ≤ 10853588681502 :=
  _root_.PoleAffine6970.certified 4462 963 10853588681502 (by decide) (by decide +kernel)

private theorem pole_4462_982 :
    P1_7_1.groupedPoleMoment 4462 982 ≤ 11020095796464 :=
  _root_.Research6969.PackedRanks.PackedRanks294To296.moment4462_982

private theorem pole_4462_990 :
    P1_7_1.groupedPoleMoment 4462 990 ≤ 11089873652459 :=
  _root_.PoleAffine6970.certified 4462 990 11089873652459 (by decide) (by decide +kernel)

private theorem pole_4463_982 :
    P1_7_1.groupedPoleMoment 4463 982 ≤ 11028049925768 :=
  _root_.Research6969.PackedRanks.PackedRanks297To299.moment4463_982

private theorem pole_4463_1008 :
    P1_7_1.groupedPoleMoment 4463 1008 ≤ 11254299374432 :=
  _root_.Research6969.PackedRanks.PackedRanks297To299.moment4463_1008

private theorem pole_4464_963 :
    P1_7_1.groupedPoleMoment 4464 963 ≤ 10869251283552 :=
  _root_.Research6969.PackedRanks.PackedRanks297To299.moment4464_963

private theorem pole_4464_967 :
    P1_7_1.groupedPoleMoment 4464 967 ≤ 10904451073769 :=
  _root_.PoleAffine6970.certified 4464 967 10904451073769 (by decide) (by decide +kernel)

private theorem pole_4464_982 :
    P1_7_1.groupedPoleMoment 4464 982 ≤ 11036007960531 :=
  _root_.Research6969.PackedRanks.PackedRanks300To302.moment4464_982

private theorem pole_4464_986 :
    P1_7_1.groupedPoleMoment 4464 986 ≤ 11070973355058 :=
  _root_.PoleAffine6970.certified 4464 986 11070973355058 (by decide) (by decide +kernel)

theorem bank_3200_4461_967 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3200,4461,967,u⟩,986158795325440,10880883913449⟩ :=
  pack_R6970Height2313CommonRanks57_bank_checked 3200 4461 967 u 986158795325440 10880883913449
    (by decide) (by decide) (by decide) (by decide) pole_4461_967

theorem bank_3200_4462_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3200,4462,963,u⟩,983050615259136,10853588681502⟩ :=
  pack_R6970Height2313CommonRanks57_bank_checked 3200 4462 963 u 983050615259136 10853588681502
    (by decide) (by decide) (by decide) (by decide) pole_4462_963

theorem bank_3204_4462_982 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3204,4462,982,u⟩,1000562368970752,11020095796464⟩ :=
  pack_R6970Height2313CommonRanks57_bank_checked 3204 4462 982 u 1000562368970752 11020095796464
    (by decide) (by decide) (by decide) (by decide) pole_4462_982

theorem bank_3215_4462_990 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3215,4462,990,u⟩,1014500834672640,11089873652459⟩ :=
  pack_R6970Height2313CommonRanks57_bank_checked 3215 4462 990 u 1014500834672640 11089873652459
    (by decide) (by decide) (by decide) (by decide) pole_4462_990

theorem bank_3210_4463_982 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3210,4463,982,u⟩,1004762418380800,11028049925768⟩ :=
  pack_R6970Height2313CommonRanks57_bank_checked 3210 4463 982 u 1004762418380800 11028049925768
    (by decide) (by decide) (by decide) (by decide) pole_4463_982

theorem bank_3205_4463_1008 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3205,4463,1008,u⟩,1021287165853696,11254299374432⟩ :=
  pack_R6970Height2313CommonRanks57_bank_checked 3205 4463 1008 u 1021287165853696 11254299374432
    (by decide) (by decide) (by decide) (by decide) pole_4463_1008

theorem bank_3202_4464_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3202,4464,963,u⟩,984425340338176,10869251283552⟩ :=
  pack_R6970Height2313CommonRanks57_bank_checked 3202 4464 963 u 984425340338176 10869251283552
    (by decide) (by decide) (by decide) (by decide) pole_4464_963

theorem bank_3212_4464_967 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3212,4464,967,u⟩,994450506514432,10904451073769⟩ :=
  pack_R6970Height2313CommonRanks57_bank_checked 3212 4464 967 u 994450506514432 10904451073769
    (by decide) (by decide) (by decide) (by decide) pole_4464_967

theorem bank_3204_4464_982 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3204,4464,982,u⟩,1000562368970752,11036007960531⟩ :=
  pack_R6970Height2313CommonRanks57_bank_checked 3204 4464 982 u 1000562368970752 11036007960531
    (by decide) (by decide) (by decide) (by decide) pole_4464_982

theorem bank_3215_4464_986 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3215,4464,986,u⟩,1011387794980864,11070973355058⟩ :=
  pack_R6970Height2313CommonRanks57_bank_checked 3215 4464 986 u 1011387794980864 11070973355058
    (by decide) (by decide) (by decide) (by decide) pole_4464_986

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks57

section Pack_R6970Height2313CommonRanks58

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks58_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_4464_1008 :
    P1_7_1.groupedPoleMoment 4464 1008 ≤ 11262426748352 :=
  _root_.Research6969.PackedRanks.PackedRanks300To302.moment4464_1008

private theorem pole_4465_955 :
    P1_7_1.groupedPoleMoment 4465 955 ≤ 10806484661095 :=
  _root_.PoleAffine6970.certified 4465 955 10806484661095 (by decide) (by decide +kernel)

private theorem pole_4465_963 :
    P1_7_1.groupedPoleMoment 4465 963 ≤ 10877088344236 :=
  _root_.Research6969.PackedRanks.PackedRanks303To305.moment4465_963

private theorem pole_4465_971 :
    P1_7_1.groupedPoleMoment 4465 971 ≤ 10947490647200 :=
  _root_.PoleAffine6970.certified 4465 971 10947490647200 (by decide) (by decide +kernel)

private theorem pole_4465_982 :
    P1_7_1.groupedPoleMoment 4465 982 ≤ 11043969901736 :=
  _root_.Research6969.PackedRanks.PackedRanks303To305.moment4465_982

private theorem pole_4467_961 :
    P1_7_1.groupedPoleMoment 4467 961 ≤ 10875115635131 :=
  _root_.PoleAffine6970.certified 4467 961 10875115635131 (by decide) (by decide +kernel)

private theorem pole_4467_963 :
    P1_7_1.groupedPoleMoment 4467 963 ≤ 10892773989742 :=
  _root_.PoleAffine6970.certified 4467 963 10892773989742 (by decide) (by decide +kernel)

private theorem pole_4468_963 :
    P1_7_1.groupedPoleMoment 4468 963 ≤ 10900622576492 :=
  _root_.PoleAffine6970.certified 4468 963 10900622576492 (by decide) (by decide +kernel)

private theorem pole_4469_963 :
    P1_7_1.groupedPoleMoment 4469 963 ≤ 10908475007192 :=
  _root_.PoleAffine6970.certified 4469 963 10908475007192 (by decide) (by decide +kernel)

private theorem pole_4472_971 :
    P1_7_1.groupedPoleMoment 4472 971 ≤ 11002827304772 :=
  _root_.PoleAffine6970.certified 4472 971 11002827304772 (by decide) (by decide +kernel)

theorem bank_3210_4464_1008 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3210,4464,1008,u⟩,1024863250415616,11262426748352⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3210 4464 1008 u 1024863250415616 11262426748352
    (by decide) (by decide) (by decide) (by decide) pole_4464_1008

theorem bank_3200_4465_955 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3200,4465,955,u⟩,976818203525120,10806484661095⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3200 4465 955 u 976818203525120 10806484661095
    (by decide) (by decide) (by decide) (by decide) pole_4465_955

theorem bank_3202_4465_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3202,4465,963,u⟩,984425340338176,10877088344236⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3202 4465 963 u 984425340338176 10877088344236
    (by decide) (by decide) (by decide) (by decide) pole_4465_963

theorem bank_3207_4465_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3207,4465,963,u⟩,987866575405056,10877088344236⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3207 4465 963 u 987866575405056 10877088344236
    (by decide) (by decide) (by decide) (by decide) pole_4465_963

theorem bank_3208_4465_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3208,4465,963,u⟩,988555580538880,10877088344236⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3208 4465 963 u 988555580538880 10877088344236
    (by decide) (by decide) (by decide) (by decide) pole_4465_963

theorem bank_3212_4465_971 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3212,4465,971,u⟩,997581528760320,10947490647200⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3212 4465 971 u 997581528760320 10947490647200
    (by decide) (by decide) (by decide) (by decide) pole_4465_971

theorem bank_3208_4465_982 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3208,4465,982,u⟩,1003361371160576,11043969901736⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3208 4465 982 u 1003361371160576 11043969901736
    (by decide) (by decide) (by decide) (by decide) pole_4465_982

theorem bank_3214_4465_982 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3214,4465,982,u⟩,1007567605071872,11043969901736⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3214 4465 982 u 1007567605071872 11043969901736
    (by decide) (by decide) (by decide) (by decide) pole_4465_982

theorem bank_3202_4467_961 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3202,4467,961,u⟩,982866902384640,10875115635131⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3202 4467 961 u 982866902384640 10875115635131
    (by decide) (by decide) (by decide) (by decide) pole_4467_961

theorem bank_3203_4467_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3203,4467,963,u⟩,985113081937920,10892773989742⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3203 4467 963 u 985113081937920 10892773989742
    (by decide) (by decide) (by decide) (by decide) pole_4467_963

theorem bank_3203_4468_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3203,4468,963,u⟩,985113081937920,10900622576492⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3203 4468 963 u 985113081937920 10900622576492
    (by decide) (by decide) (by decide) (by decide) pole_4468_963

theorem bank_3204_4469_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3204,4469,963,u⟩,985801076244480,10908475007192⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3204 4469 963 u 985801076244480 10908475007192
    (by decide) (by decide) (by decide) (by decide) pole_4469_963

theorem bank_3217_4472_971 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3217,4472,971,u⟩,1001058965913600,11002827304772⟩ :=
  pack_R6970Height2313CommonRanks58_bank_checked 3217 4472 971 u 1001058965913600 11002827304772
    (by decide) (by decide) (by decide) (by decide) pole_4472_971

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks58
