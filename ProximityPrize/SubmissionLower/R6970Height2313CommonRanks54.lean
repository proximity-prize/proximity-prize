import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0589

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

private theorem pole_4172_896 :
    P1_7_1.groupedPoleMoment 4172 896 ≤ 8264657754455 :=
  _root_.PoleAffine6970.certified 4172 896 8264657754455 (by decide) (by decide +kernel)

private theorem pole_4175_897 :
    P1_7_1.groupedPoleMoment 4175 897 ≤ 8291009592869 :=
  _root_.PoleAffine6970.certified 4175 897 8291009592869 (by decide) (by decide +kernel)

private theorem pole_4175_898 :
    P1_7_1.groupedPoleMoment 4175 898 ≤ 8298222886581 :=
  _root_.PoleAffine6970.certified 4175 898 8298222886581 (by decide) (by decide +kernel)

private theorem pole_4178_897 :
    P1_7_1.groupedPoleMoment 4178 897 ≤ 8310192816141 :=
  _root_.PoleAffine6970.certified 4178 897 8310192816141 (by decide) (by decide +kernel)

private theorem pole_4178_900 :
    P1_7_1.groupedPoleMoment 4178 900 ≤ 8331876423452 :=
  _root_.PoleAffine6970.certified 4178 900 8331876423452 (by decide) (by decide +kernel)

private theorem pole_4180_898 :
    P1_7_1.groupedPoleMoment 4180 898 ≤ 8330240596276 :=
  _root_.PoleAffine6970.certified 4180 898 8330240596276 (by decide) (by decide +kernel)

private theorem pole_4180_900 :
    P1_7_1.groupedPoleMoment 4180 900 ≤ 8344716709602 :=
  _root_.PoleAffine6970.certified 4180 900 8344716709602 (by decide) (by decide +kernel)

private theorem pole_4184_900 :
    P1_7_1.groupedPoleMoment 4184 900 ≤ 8370437628682 :=
  _root_.Research6969.SpreadMomentProof.moment4184_900

private theorem pole_4399_982 :
    P1_7_1.groupedPoleMoment 4399 982 ≤ 10526816118216 :=
  _root_.PoleAffine6970.certified 4399 982 10526816118216 (by decide) (by decide +kernel)

private theorem pole_4401_947 :
    P1_7_1.groupedPoleMoment 4401 947 ≤ 10248469804329 :=
  _root_.PoleAffine6970.certified 4401 947 10248469804329 (by decide) (by decide +kernel)

theorem bank_2992_4172_896 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2992,4172,896,u⟩,800631134617600,8264657754455⟩ :=
  bank_checked 2992 4172 896 u 800631134617600 8264657754455
    (by decide) (by decide) (by decide) (by decide) pole_4172_896

theorem bank_3002_4175_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3002,4175,897,u⟩,807312748183552,8291009592869⟩ :=
  bank_checked 3002 4175 897 u 807312748183552 8291009592869
    (by decide) (by decide) (by decide) (by decide) pole_4175_897

theorem bank_3000_4175_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3000,4175,897,u⟩,806110768660480,8291009592869⟩ :=
  bank_checked 3000 4175 897 u 806110768660480 8291009592869
    (by decide) (by decide) (by decide) (by decide) pole_4175_897

theorem bank_3000_4175_898 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3000,4175,898,u⟩,806795987910656,8298222886581⟩ :=
  bank_checked 3000 4175 898 u 806795987910656 8298222886581
    (by decide) (by decide) (by decide) (by decide) pole_4175_898

theorem bank_3004_4175_898 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3004,4175,898,u⟩,809203095306240,8298222886581⟩ :=
  bank_checked 3004 4175 898 u 809203095306240 8298222886581
    (by decide) (by decide) (by decide) (by decide) pole_4175_898

theorem bank_3004_4178_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3004,4178,897,u⟩,808515669327872,8310192816141⟩ :=
  bank_checked 3004 4178 897 u 808515669327872 8310192816141
    (by decide) (by decide) (by decide) (by decide) pole_4178_897

theorem bank_2998_4178_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2998,4178,897,u⟩,804909730758656,8310192816141⟩ :=
  bank_checked 2998 4178 897 u 804909730758656 8310192816141
    (by decide) (by decide) (by decide) (by decide) pole_4178_897

theorem bank_2995_4178_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2995,4178,897,u⟩,803109939445760,8310192816141⟩ :=
  bank_checked 2995 4178 897 u 803109939445760 8310192816141
    (by decide) (by decide) (by decide) (by decide) pole_4178_897

theorem bank_3006_4178_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3006,4178,900,u⟩,811784174567424,8331876423452⟩ :=
  bank_checked 3006 4178 900 u 811784174567424 8331876423452
    (by decide) (by decide) (by decide) (by decide) pole_4178_900

theorem bank_2998_4178_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2998,4178,900,u⟩,806961139154944,8331876423452⟩ :=
  bank_checked 2998 4178 900 u 806961139154944 8331876423452
    (by decide) (by decide) (by decide) (by decide) pole_4178_900

theorem bank_3005_4178_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3005,4178,900,u⟩,811180468469760,8331876423452⟩ :=
  bank_checked 3005 4178 900 u 811180468469760 8331876423452
    (by decide) (by decide) (by decide) (by decide) pole_4178_900

theorem bank_2997_4180_898 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2997,4180,898,u⟩,804993131872256,8330240596276⟩ :=
  bank_checked 2997 4180 898 u 804993131872256 8330240596276
    (by decide) (by decide) (by decide) (by decide) pole_4180_898

theorem bank_2997_4180_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2997,4180,900,u⟩,806359322591232,8344716709602⟩ :=
  bank_checked 2997 4180 900 u 806359322591232 8344716709602
    (by decide) (by decide) (by decide) (by decide) pole_4180_900

theorem bank_3001_4180_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3001,4180,900,u⟩,808768005996544,8344716709602⟩ :=
  bank_checked 3001 4180 900 u 808768005996544 8344716709602
    (by decide) (by decide) (by decide) (by decide) pole_4180_900

theorem bank_3000_4184_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3000,4184,900,u⟩,808165480857600,8370437628682⟩ :=
  bank_checked 3000 4184 900 u 808165480857600 8370437628682
    (by decide) (by decide) (by decide) (by decide) pole_4184_900

theorem bank_3003_4184_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3003,4184,900,u⟩,809973764849664,8370437628682⟩ :=
  bank_checked 3003 4184 900 u 809973764849664 8370437628682
    (by decide) (by decide) (by decide) (by decide) pole_4184_900

theorem bank_3170_4399_982 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3170,4399,982,u⟩,976937316515840,10526816118216⟩ :=
  bank_checked 3170 4399 982 u 976937316515840 10526816118216
    (by decide) (by decide) (by decide) (by decide) pole_4399_982

theorem bank_3154_4401_947 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3154,4401,947,u⟩,939653185667072,10248469804329⟩ :=
  bank_checked 3154 4401 947 u 939653185667072 10248469804329
    (by decide) (by decide) (by decide) (by decide) pole_4401_947

end Research6970.Height2313.CommonBankRanks
