import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0614
import ProximityPrize.SubmissionLower.Z6969Pack0615
import ProximityPrize.SubmissionLower.Z6969Pack0616

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

private theorem pole_9619_2126 :
    P1_7_1.groupedPoleMoment 9619 2126 ≤ 238556846527736 :=
  _root_.PoleAffine6970.certified 9619 2126 238556846527736 (by decide) (by decide +kernel)

private theorem pole_9621_2118 :
    P1_7_1.groupedPoleMoment 9621 2118 ≤ 238016971510476 :=
  _root_.Research6969.PackedRanks.PackedRanks348To350.moment9621_2118

private theorem pole_9621_2174 :
    P1_7_1.groupedPoleMoment 9621 2174 ≤ 242895948111878 :=
  _root_.Research6969.PackedRanks.PackedRanks348To350.moment9621_2174

private theorem pole_9623_2118 :
    P1_7_1.groupedPoleMoment 9623 2118 ≤ 238176347849000 :=
  _root_.Research6969.PackedRanks.PackedRanks351To353.moment9623_2118

private theorem pole_9623_2174 :
    P1_7_1.groupedPoleMoment 9623 2174 ≤ 243058712908678 :=
  _root_.Research6969.PackedRanks.PackedRanks351To353.moment9623_2174

private theorem pole_9625_2118 :
    P1_7_1.groupedPoleMoment 9625 2118 ≤ 238335796784464 :=
  _root_.Research6969.PackedRanks.PackedRanks351To353.moment9625_2118

private theorem pole_9625_2134 :
    P1_7_1.groupedPoleMoment 9625 2134 ≤ 239736170913945 :=
  _root_.PoleAffine6970.certified 9625 2134 239736170913945 (by decide) (by decide +kernel)

private theorem pole_9625_2174 :
    P1_7_1.groupedPoleMoment 9625 2174 ≤ 243221551977378 :=
  _root_.Research6969.PackedRanks.PackedRanks354To356.moment9625_2174

private theorem pole_9626_2077 :
    P1_7_1.groupedPoleMoment 9626 2077 ≤ 234809190715807 :=
  _root_.Research6969.PackedRanks.PackedRanks354To356.moment9626_2077

private theorem pole_9626_2085 :
    P1_7_1.groupedPoleMoment 9626 2085 ≤ 235514775615310 :=
  _root_.PoleAffine6970.certified 9626 2085 235514775615310 (by decide) (by decide +kernel)

theorem bank_6928_9619_2126 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6928,9619,2126,u⟩,10117055495536640,238556846527736⟩ :=
  bank_checked 6928 9619 2126 u 10117055495536640 238556846527736
    (by decide) (by decide) (by decide) (by decide) pole_9619_2126

theorem bank_6929_9621_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6929,9621,2118,u⟩,10091370476994560,238016971510476⟩ :=
  bank_checked 6929 9621 2118 u 10091370476994560 238016971510476
    (by decide) (by decide) (by decide) (by decide) pole_9621_2118

theorem bank_6908_9621_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6908,9621,2118,u⟩,10023012722278400,238016971510476⟩ :=
  bank_checked 6908 9621 2118 u 10023012722278400 238016971510476
    (by decide) (by decide) (by decide) (by decide) pole_9621_2118

theorem bank_6930_9621_2174 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6930,9621,2174,u⟩,10296459014963200,242895948111878⟩ :=
  bank_checked 6930 9621 2174 u 10296459014963200 242895948111878
    (by decide) (by decide) (by decide) (by decide) pole_9621_2174

theorem bank_6906_9621_2174 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6906,9621,2174,u⟩,10216661254144000,242895948111878⟩ :=
  bank_checked 6906 9621 2174 u 10216661254144000 242895948111878
    (by decide) (by decide) (by decide) (by decide) pole_9621_2174

theorem bank_6934_9621_2174 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6934,9621,2174,u⟩,10309790570905600,242895948111878⟩ :=
  bank_checked 6934 9621 2174 u 10309790570905600 242895948111878
    (by decide) (by decide) (by decide) (by decide) pole_9621_2174

theorem bank_6938_9621_2174 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6938,9621,2174,u⟩,10323131249459200,242895948111878⟩ :=
  bank_checked 6938 9621 2174 u 10323131249459200 242895948111878
    (by decide) (by decide) (by decide) (by decide) pole_9621_2174

theorem bank_6923_9623_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6923,9623,2118,u⟩,10071814693191680,238176347849000⟩ :=
  bank_checked 6923 9623 2118 u 10071814693191680 238176347849000
    (by decide) (by decide) (by decide) (by decide) pole_9623_2118

theorem bank_6939_9623_2174 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6939,9623,2174,u⟩,10326467844505600,243058712908678⟩ :=
  bank_checked 6939 9623 2174 u 10326467844505600 243058712908678
    (by decide) (by decide) (by decide) (by decide) pole_9623_2174

theorem bank_6907_9623_2174 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6907,9623,2174,u⟩,10219979603968000,243058712908678⟩ :=
  bank_checked 6907 9623 2174 u 10219979603968000 243058712908678
    (by decide) (by decide) (by decide) (by decide) pole_9623_2174

theorem bank_6931_9623_2174 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6931,9623,2174,u⟩,10299791048704000,243058712908678⟩ :=
  bank_checked 6931 9623 2174 u 10299791048704000 243058712908678
    (by decide) (by decide) (by decide) (by decide) pole_9623_2174

theorem bank_6924_9625_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6924,9625,2118,u⟩,10075072601784320,238335796784464⟩ :=
  bank_checked 6924 9625 2118 u 10075072601784320 238335796784464
    (by decide) (by decide) (by decide) (by decide) pole_9625_2118

theorem bank_6934_9625_2134 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6934,9625,2134,u⟩,10165649691115520,239736170913945⟩ :=
  bank_checked 6934 9625 2134 u 10165649691115520 239736170913945
    (by decide) (by decide) (by decide) (by decide) pole_9625_2134

theorem bank_6932_9625_2174 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6932,9625,2174,u⟩,10303123652608000,243221551977378⟩ :=
  bank_checked 6932 9625 2174 u 10303123652608000 243221551977378
    (by decide) (by decide) (by decide) (by decide) pole_9625_2174

theorem bank_6908_9626_2077 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6908,9626,2077,u⟩,9874987794825216,234809190715807⟩ :=
  bank_checked 6908 9626 2077 u 9874987794825216 234809190715807
    (by decide) (by decide) (by decide) (by decide) pole_9626_2077

theorem bank_6914_9626_2077 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6914,9626,2077,u⟩,9894183174930432,234809190715807⟩ :=
  bank_checked 6914 9626 2077 u 9894183174930432 234809190715807
    (by decide) (by decide) (by decide) (by decide) pole_9626_2077

theorem bank_6919_9626_2085 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6919,9626,2085,u⟩,9939282828984320,235514775615310⟩ :=
  bank_checked 6919 9626 2085 u 9939282828984320 235514775615310
    (by decide) (by decide) (by decide) (by decide) pole_9626_2085

end Research6970.Height2313.CommonBankRanks
