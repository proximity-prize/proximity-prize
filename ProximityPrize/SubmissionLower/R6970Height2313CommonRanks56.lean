import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0598

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

private theorem pole_4449_982 :
    P1_7_1.groupedPoleMoment 4449 982 ≤ 10917047065016 :=
  _root_.PoleAffine6970.certified 4449 982 10917047065016 (by decide) (by decide +kernel)

private theorem pole_4453_963 :
    P1_7_1.groupedPoleMoment 4453 963 ≤ 10783296850152 :=
  _root_.PoleAffine6970.certified 4453 963 10783296850152 (by decide) (by decide +kernel)

private theorem pole_4454_982 :
    P1_7_1.groupedPoleMoment 4454 982 ≤ 10956603240596 :=
  _root_.PoleAffine6970.certified 4454 982 10956603240596 (by decide) (by decide +kernel)

private theorem pole_4456_967 :
    P1_7_1.groupedPoleMoment 4456 967 ≤ 10841682323769 :=
  _root_.PoleAffine6970.certified 4456 967 10841682323769 (by decide) (by decide +kernel)

private theorem pole_4457_963 :
    P1_7_1.groupedPoleMoment 4457 963 ≤ 10814499327412 :=
  _root_.PoleAffine6970.certified 4457 963 10814499327412 (by decide) (by decide +kernel)

private theorem pole_4457_971 :
    P1_7_1.groupedPoleMoment 4457 971 ≤ 10884480876152 :=
  _root_.PoleAffine6970.certified 4457 971 10884480876152 (by decide) (by decide +kernel)

private theorem pole_4459_1008 :
    P1_7_1.groupedPoleMoment 4459 1008 ≤ 11221829825062 :=
  _root_.Research6969.PackedRanks.PackedRanks294To296.moment4459_1008

private theorem pole_4460_967 :
    P1_7_1.groupedPoleMoment 4460 967 ≤ 10873035897009 :=
  _root_.PoleAffine6970.certified 4460 967 10873035897009 (by decide) (by decide +kernel)

private theorem pole_4461_955 :
    P1_7_1.groupedPoleMoment 4461 955 ≤ 10775370705171 :=
  _root_.PoleAffine6970.certified 4461 955 10775370705171 (by decide) (by decide +kernel)

private theorem pole_4461_963 :
    P1_7_1.groupedPoleMoment 4461 963 ≤ 10845763138208 :=
  _root_.PoleAffine6970.certified 4461 963 10845763138208 (by decide) (by decide +kernel)

theorem bank_3200_4449_982 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3200,4449,982,u⟩,997767489781760,10917047065016⟩ :=
  bank_checked 3200 4449 982 u 997767489781760 10917047065016
    (by decide) (by decide) (by decide) (by decide) pole_4449_982

theorem bank_3191_4453_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3191,4453,963,u⟩,976876861390848,10783296850152⟩ :=
  bank_checked 3191 4453 963 u 976876861390848 10783296850152
    (by decide) (by decide) (by decide) (by decide) pole_4453_963

theorem bank_3208_4454_982 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3208,4454,982,u⟩,1003361371160576,10956603240596⟩ :=
  bank_checked 3208 4454 982 u 1003361371160576 10956603240596
    (by decide) (by decide) (by decide) (by decide) pole_4454_982

theorem bank_3207_4456_967 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3207,4456,967,u⟩,990991186132992,10841682323769⟩ :=
  bank_checked 3207 4456 967 u 990991186132992 10841682323769
    (by decide) (by decide) (by decide) (by decide) pole_4456_967

theorem bank_3202_4457_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3202,4457,963,u⟩,984425340338176,10814499327412⟩ :=
  bank_checked 3202 4457 963 u 984425340338176 10814499327412
    (by decide) (by decide) (by decide) (by decide) pole_4457_963

theorem bank_3208_4457_971 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3208,4457,971,u⟩,994804165509120,10884480876152⟩ :=
  bank_checked 3208 4457 971 u 994804165509120 10884480876152
    (by decide) (by decide) (by decide) (by decide) pole_4457_971

theorem bank_3211_4459_1008 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3211,4459,1008,u⟩,1025579260837888,11221829825062⟩ :=
  bank_checked 3211 4459 1008 u 1025579260837888 11221829825062
    (by decide) (by decide) (by decide) (by decide) pole_4459_1008

theorem bank_3213_4459_1008 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3213,4459,1008,u⟩,1027012075192320,11221829825062⟩ :=
  bank_checked 3213 4459 1008 u 1027012075192320 11221829825062
    (by decide) (by decide) (by decide) (by decide) pole_4459_1008

theorem bank_3205_4460_967 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3205,4460,967,u⟩,989609234268160,10873035897009⟩ :=
  bank_checked 3205 4460 967 u 989609234268160 10873035897009
    (by decide) (by decide) (by decide) (by decide) pole_4460_967

theorem bank_3197_4461_955 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3197,4461,955,u⟩,974772100923392,10775370705171⟩ :=
  bank_checked 3197 4461 955 u 974772100923392 10775370705171
    (by decide) (by decide) (by decide) (by decide) pole_4461_955

theorem bank_3199_4461_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3199,4461,963,u⟩,982363631779840,10845763138208⟩ :=
  bank_checked 3199 4461 963 u 982363631779840 10845763138208
    (by decide) (by decide) (by decide) (by decide) pole_4461_963

end Research6970.Height2313.CommonBankRanks
