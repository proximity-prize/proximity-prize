import ProximityPrize.SubmissionLower.Cases6921
import ProximityPrize.SubmissionLower.Middle6921
import ProximityPrize.SubmissionLower.Low6921
import ProximityPrize.SubmissionLower.Protocol6921
set_option Elab.async false
theorem Cases6921.K21_2_1 : K21_2.c1 := K21_2_1.proof
theorem Cases6921.K21_2_2_1 : K21_2_2.c1 := K21_2_2_1.proof
theorem Cases6921.K21_2_2_2 : K21_2_2.c2 := K21_2_2_2.proof
theorem Cases6921.K21_2_2 : K21_2.c2 := K21_2_2.of_children Cases6921.K21_2_2_1 Cases6921.K21_2_2_2
theorem Cases6921.K21_2_3 : K21_2.c3 := K21_2_3.proof
theorem Cases6921.K21_2_4_1_1 : K21_2_4_1.c1 := K21_2_4_1_1.proof
theorem Cases6921.K21_2_4_1_2 : K21_2_4_1.c2 := K21_2_4_1_2.proof
theorem Cases6921.K21_2_4_1 : K21_2_4.c1 := K21_2_4_1.of_children Cases6921.K21_2_4_1_1 Cases6921.K21_2_4_1_2
theorem Cases6921.K21_2_4_2 : K21_2_4.c2 := K21_2_4_2.proof
theorem Cases6921.K21_2_4_3 : K21_2_4.c3 := K21_2_4_3.proof
theorem Cases6921.K21_2_4 : K21_2.c4 := K21_2_4.of_children Cases6921.K21_2_4_1 Cases6921.K21_2_4_2 Cases6921.K21_2_4_3
theorem Cases6921.K21_2 : K21.c2 := K21_2.of_children Cases6921.K21_2_1 Cases6921.K21_2_2 Cases6921.K21_2_3 Cases6921.K21_2_4

namespace Assembly6921
theorem protocol_of_high (high : K21.c14) :
    ProximityPrize.Benchmark.ProtocolClaim 6930 335972916 1073741824 :=
  Protocol6921.protocolClaim_of_scalarCap
    (K21.of_children Cases6921.K21_1 Cases6921.K21_2 Cases6921.K21_3
      Cases6921.K21_4 Cases6921.K21_5 Cases6921.K21_6 Cases6921.K21_7
      Cases6921.K21_8 Cases6921.K21_9 Cases6921.K21_10 Cases6921.K21_11
      Cases6921.K21_12 Low6921.count high)
end Assembly6921
