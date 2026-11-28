import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0618
import ProximityPrize.SubmissionLower.Z6969Pack0619

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

private theorem pole_11517_2498 :
    P1_7_1.groupedPoleMoment 11517 2498 ≤ 483050333667183 :=
  _root_.PoleAffine6970.certified 11517 2498 483050333667183 (by decide) (by decide +kernel)

private theorem pole_11547_2548 :
    P1_7_1.groupedPoleMoment 11547 2548 ≤ 494696176813958 :=
  _root_.PoleAffine6970.certified 11547 2548 494696176813958 (by decide) (by decide +kernel)

private theorem pole_11557_2498 :
    P1_7_1.groupedPoleMoment 11557 2498 ≤ 488471451219103 :=
  _root_.PoleAffine6970.certified 11557 2498 488471451219103 (by decide) (by decide +kernel)

private theorem pole_11558_2498 :
    P1_7_1.groupedPoleMoment 11558 2498 ≤ 488607506616833 :=
  _root_.PoleAffine6970.certified 11558 2498 488607506616833 (by decide) (by decide +kernel)

private theorem pole_11559_2615 :
    P1_7_1.groupedPoleMoment 11559 2615 ≤ 506472061276259 :=
  _root_.PoleAffine6970.certified 11559 2615 506472061276259 (by decide) (by decide +kernel)

private theorem pole_11569_2514 :
    P1_7_1.groupedPoleMoment 11569 2514 ≤ 492553799321867 :=
  _root_.PoleAffine6970.certified 11569 2514 492553799321867 (by decide) (by decide +kernel)

private theorem pole_11573_2506 :
    P1_7_1.groupedPoleMoment 11573 2506 ≤ 491877509700364 :=
  _root_.PoleAffine6970.certified 11573 2506 491877509700364 (by decide) (by decide +kernel)

private theorem pole_11575_2548 :
    P1_7_1.groupedPoleMoment 11575 2548 ≤ 498569901356632 :=
  _root_.Research6969.PackedRanks.PackedRanks360To362.moment11575_2548

private theorem pole_11575_2607 :
    P1_7_1.groupedPoleMoment 11575 2607 ≤ 507525945959908 :=
  _root_.PoleAffine6970.certified 11575 2607 507525945959908 (by decide) (by decide +kernel)

private theorem pole_11575_2615 :
    P1_7_1.groupedPoleMoment 11575 2615 ≤ 508734991702659 :=
  _root_.Research6969.PackedRanks.PackedRanks363To365.moment11575_2615

theorem bank_8281_11517_2498 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8281,11517,2498,u⟩,17051587732307968,483050333667183⟩ :=
  bank_checked 8281 11517 2498 u 17051587732307968 483050333667183
    (by decide) (by decide) (by decide) (by decide) pole_11517_2498

theorem bank_8317_11547_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8317,11547,2548,u⟩,17479623502462976,494696176813958⟩ :=
  bank_checked 8317 11547 2548 u 17479623502462976 494696176813958
    (by decide) (by decide) (by decide) (by decide) pole_11547_2548

theorem bank_8306_11557_2498 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8306,11557,2498,u⟩,17166966842195968,488471451219103⟩ :=
  bank_checked 8306 11557 2498 u 17166966842195968 488471451219103
    (by decide) (by decide) (by decide) (by decide) pole_11557_2498

theorem bank_8289_11558_2498 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8289,11558,2498,u⟩,17088464500817920,488607506616833⟩ :=
  bank_checked 8289 11558 2498 u 17088464500817920 488607506616833
    (by decide) (by decide) (by decide) (by decide) pole_11558_2498

theorem bank_8336_11559_2615 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8336,11559,2615,u⟩,17918546588729344,506472061276259⟩ :=
  bank_checked 8336 11559 2615 u 17918546588729344 506472061276259
    (by decide) (by decide) (by decide) (by decide) pole_11559_2615

theorem bank_8300_11569_2514 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8300,11569,2514,u⟩,17222821613404160,492553799321867⟩ :=
  bank_checked 8300 11569 2514 u 17222821613404160 492553799321867
    (by decide) (by decide) (by decide) (by decide) pole_11569_2514

theorem bank_8328_11573_2506 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8328,11573,2506,u⟩,17310999549050880,491877509700364⟩ :=
  bank_checked 8328 11573 2506 u 17310999549050880 491877509700364
    (by decide) (by decide) (by decide) (by decide) pole_11573_2506

theorem bank_8328_11575_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8328,11575,2548,u⟩,17531435454300160,498569901356632⟩ :=
  bank_checked 8328 11575 2548 u 17531435454300160 498569901356632
    (by decide) (by decide) (by decide) (by decide) pole_11575_2548

theorem bank_8305_11575_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8305,11575,2548,u⟩,17423193585483776,498569901356632⟩ :=
  bank_checked 8305 11575 2548 u 17423193585483776 498569901356632
    (by decide) (by decide) (by decide) (by decide) pole_11575_2548

theorem bank_8347_11575_2607 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8347,11575,2607,u⟩,17929957132992512,507525945959908⟩ :=
  bank_checked 8347 11575 2607 u 17929957132992512 507525945959908
    (by decide) (by decide) (by decide) (by decide) pole_11575_2607

theorem bank_8339_11575_2615 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8339,11575,2615,u⟩,17933010479349760,508734991702659⟩ :=
  bank_checked 8339 11575 2615 u 17933010479349760 508734991702659
    (by decide) (by decide) (by decide) (by decide) pole_11575_2615

end Research6970.Height2313.CommonBankRanks
