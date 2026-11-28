import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0616
import ProximityPrize.SubmissionLower.Z6969Pack0618

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

private theorem pole_9626_2093 :
    P1_7_1.groupedPoleMoment 9626 2093 ≤ 236219430732676 :=
  _root_.PoleAffine6970.certified 9626 2093 236219430732676 (by decide) (by decide +kernel)

private theorem pole_9626_2118 :
    P1_7_1.groupedPoleMoment 9626 2118 ≤ 238415548481346 :=
  _root_.Research6969.PackedRanks.PackedRanks354To356.moment9626_2118

private theorem pole_9628_2081 :
    P1_7_1.groupedPoleMoment 9628 2081 ≤ 235319397536554 :=
  _root_.PoleAffine6970.certified 9628 2081 235319397536554 (by decide) (by decide +kernel)

private theorem pole_9628_2083 :
    P1_7_1.groupedPoleMoment 9628 2083 ≤ 235495887116840 :=
  _root_.PoleAffine6970.certified 9628 2083 235495887116840 (by decide) (by decide +kernel)

private theorem pole_9628_2118 :
    P1_7_1.groupedPoleMoment 9628 2118 ≤ 238575106344005 :=
  _root_.Research6969.PackedRanks.PackedRanks360To362.moment9628_2118

private theorem pole_9658_2118 :
    P1_7_1.groupedPoleMoment 9658 2118 ≤ 240977200495410 :=
  _root_.PoleAffine6970.certified 9658 2118 240977200495410 (by decide) (by decide +kernel)

private theorem pole_9820_2118 :
    P1_7_1.groupedPoleMoment 9820 2118 ≤ 254233369236069 :=
  _root_.PoleAffine6970.certified 9820 2118 254233369236069 (by decide) (by decide +kernel)

private theorem pole_10107_2223 :
    P1_7_1.groupedPoleMoment 10107 2223 ≤ 289664566465168 :=
  _root_.PoleAffine6970.certified 10107 2223 289664566465168 (by decide) (by decide +kernel)

private theorem pole_10109_2180 :
    P1_7_1.groupedPoleMoment 10109 2180 ≤ 285467749372798 :=
  _root_.PoleAffine6970.certified 10109 2180 285467749372798 (by decide) (by decide +kernel)

private theorem pole_11513_2548 :
    P1_7_1.groupedPoleMoment 11513 2548 ≤ 490019965668423 :=
  _root_.PoleAffine6970.certified 11513 2548 490019965668423 (by decide) (by decide +kernel)

theorem bank_6920_9626_2093 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6920,9626,2093,u⟩,9971549386571776,236219430732676⟩ :=
  bank_checked 6920 9626 2093 u 9971549386571776 236219430732676
    (by decide) (by decide) (by decide) (by decide) pole_9626_2093

theorem bank_6926_9626_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6926,9626,2118,u⟩,10081590085419008,238415548481346⟩ :=
  bank_checked 6926 9626 2118 u 10081590085419008 238415548481346
    (by decide) (by decide) (by decide) (by decide) pole_9626_2118

theorem bank_6929_9626_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6929,9626,2118,u⟩,10091370476994560,238415548481346⟩ :=
  bank_checked 6929 9626 2118 u 10091370476994560 238415548481346
    (by decide) (by decide) (by decide) (by decide) pole_9626_2118

theorem bank_6902_9628_2081 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6902,9628,2081,u⟩,9870275941498880,235319397536554⟩ :=
  bank_checked 6902 9628 2081 u 9870275941498880 235319397536554
    (by decide) (by decide) (by decide) (by decide) pole_9628_2081

theorem bank_6905_9628_2083 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6905,9628,2083,u⟩,9887111783120896,235495887116840⟩ :=
  bank_checked 6905 9628 2083 u 9887111783120896 235495887116840
    (by decide) (by decide) (by decide) (by decide) pole_9628_2083

theorem bank_6931_9628_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6931,9628,2118,u⟩,10097893515460608,238575106344005⟩ :=
  bank_checked 6931 9628 2118 u 10097893515460608 238575106344005
    (by decide) (by decide) (by decide) (by decide) pole_9628_2118

theorem bank_6954_9658_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6954,9658,2118,u⟩,10173068159221760,240977200495410⟩ :=
  bank_checked 6954 9658 2118 u 10173068159221760 240977200495410
    (by decide) (by decide) (by decide) (by decide) pole_9658_2118

theorem bank_7041_9820_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨7041,9820,2118,u⟩,10460082407211008,254233369236069⟩ :=
  bank_checked 7041 9820 2118 u 10460082407211008 254233369236069
    (by decide) (by decide) (by decide) (by decide) pole_9820_2118

theorem bank_7040_9820_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨7040,9820,2118,u⟩,10456759507091456,254233369236069⟩ :=
  bank_checked 7040 9820 2118 u 10456759507091456 254233369236069
    (by decide) (by decide) (by decide) (by decide) pole_9820_2118

theorem bank_7244_10107_2223 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨7244,10107,2223,u⟩,11565308219228160,289664566465168⟩ :=
  bank_checked 7244 10107 2223 u 11565308219228160 289664566465168
    (by decide) (by decide) (by decide) (by decide) pole_10107_2223

theorem bank_7246_10109_2180 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨7246,10109,2180,u⟩,11401696470892544,285467749372798⟩ :=
  bank_checked 7246 10109 2180 u 11401696470892544 285467749372798
    (by decide) (by decide) (by decide) (by decide) pole_10109_2180

theorem bank_8294_11513_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8294,11513,2548,u⟩,17371550689525760,490019965668423⟩ :=
  bank_checked 8294 11513 2548 u 17371550689525760 490019965668423
    (by decide) (by decide) (by decide) (by decide) pole_11513_2548

end Research6970.Height2313.CommonBankRanks
