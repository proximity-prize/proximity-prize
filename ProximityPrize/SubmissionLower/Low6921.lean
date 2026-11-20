import ProximityPrize.SubmissionLower.PortLow5
import ProximityPrize.SubmissionLower.PortLow7
import ProximityPrize.SubmissionLower.PortLow8

set_option Elab.async false

namespace Low6921

theorem P0_9_1 : P0_9.c1 := P0_9_1.proof
theorem P0_9_2 : P0_9.c2 := P0_9_2.proof
theorem P0_9_3_1 : P0_9_3.c1 := P0_9_3_1.proof
theorem P0_9_3_2 : P0_9_3.c2 := P0_9_3_2.proof
theorem P0_9_3 : P0_9.c3 := P0_9_3.of_children P0_9_3_1 P0_9_3_2
theorem P0_9_4_1 : P0_9_4.c1 := P0_9_4_1.proof
theorem P0_9_4_2 : P0_9_4.c2 := P0_9_4_2.proof
theorem P0_9_4 : P0_9.c4 := P0_9_4.of_children P0_9_4_1 P0_9_4_2
theorem P0_9_5_1_1 : P0_9_5_1.c1 := P0_9_5_1_1.proof
theorem P0_9_5_1_2_1 : P0_9_5_1_2.c1 := P0_9_5_1_2_1.proof
theorem P0_9_5_1_2_2 : P0_9_5_1_2.c2 := P0_9_5_1_2_2.proof
theorem P0_9_5_1_2_3 : P0_9_5_1_2.c3 := P0_9_5_1_2_3.proof
theorem P0_9_5_1_2 : P0_9_5_1.c2 := P0_9_5_1_2.of_children P0_9_5_1_2_1 P0_9_5_1_2_2 P0_9_5_1_2_3
theorem P0_9_5_1_3 : P0_9_5_1.c3 := P0_9_5_1_3.proof
theorem P0_9_5_1_4 : P0_9_5_1.c4 := P0_9_5_1_4.proof
theorem P0_9_5_1 : P0_9_5.c1 := P0_9_5_1.of_children P0_9_5_1_1 P0_9_5_1_2 P0_9_5_1_3 P0_9_5_1_4
theorem P0_9_5_2 : P0_9_5.c2 := P0_9_5_2.proof
theorem P0_9_5 : P0_9.c5 := P0_9_5.of_children P0_9_5_1 P0_9_5_2
theorem P0_9_6_1_1 : P0_9_6_1.c1 := P0_9_6_1_1.proof
theorem P0_9_6_1_2 : P0_9_6_1.c2 := P0_9_6_1_2.proof
theorem P0_9_6_1 : P0_9_6.c1 := P0_9_6_1.of_children P0_9_6_1_1 P0_9_6_1_2
theorem P0_9_6_2_1 : P0_9_6_2.c1 := P0_9_6_2_1.proof
theorem P0_9_6_2_2 : P0_9_6_2.c2 := P0_9_6_2_2.proof
theorem P0_9_6_2_3_1 : P0_9_6_2_3.c1 := P0_9_6_2_3_1.proof
theorem P0_9_6_2_3_2 : P0_9_6_2_3.c2 := P0_9_6_2_3_2.proof
theorem P0_9_6_2_3 : P0_9_6_2.c3 := P0_9_6_2_3.of_children P0_9_6_2_3_1 P0_9_6_2_3_2
theorem P0_9_6_2 : P0_9_6.c2 := P0_9_6_2.of_children P0_9_6_2_1 P0_9_6_2_2 P0_9_6_2_3
theorem P0_9_6_3_1 : P0_9_6_3.c1 := P0_9_6_3_1.proof
theorem P0_9_6_3_2 : P0_9_6_3.c2 := P0_9_6_3_2.proof
theorem P0_9_6_3 : P0_9_6.c3 := P0_9_6_3.of_children P0_9_6_3_1 P0_9_6_3_2
theorem P0_9_6 : P0_9.c6 := P0_9_6.of_children P0_9_6_1 P0_9_6_2 P0_9_6_3
theorem P0_9_7_1 : P0_9_7.c1 := P0_9_7_1.proof
theorem P0_9_7_2_1 : P0_9_7_2.c1 := P0_9_7_2_1.proof
theorem P0_9_7_2_2 : P0_9_7_2.c2 := P0_9_7_2_2.proof
theorem P0_9_7_2_3_1 : P0_9_7_2_3.c1 := P0_9_7_2_3_1.proof
theorem P0_9_7_2_3_2_1 : P0_9_7_2_3_2.c1 := P0_9_7_2_3_2_1.proof
theorem P0_9_7_2_3_2_2 : P0_9_7_2_3_2.c2 := P0_9_7_2_3_2_2.proof
theorem P0_9_7_2_3_2 : P0_9_7_2_3.c2 := P0_9_7_2_3_2.of_children P0_9_7_2_3_2_1 P0_9_7_2_3_2_2
theorem P0_9_7_2_3_3 : P0_9_7_2_3.c3 := P0_9_7_2_3_3.proof
theorem P0_9_7_2_3 : P0_9_7_2.c3 := P0_9_7_2_3.of_children P0_9_7_2_3_1 P0_9_7_2_3_2 P0_9_7_2_3_3
theorem P0_9_7_2 : P0_9_7.c2 := P0_9_7_2.of_children P0_9_7_2_1 P0_9_7_2_2 P0_9_7_2_3
theorem P0_9_7_3_1 : P0_9_7_3.c1 := P0_9_7_3_1.proof
theorem P0_9_7_3_2 : P0_9_7_3.c2 := P0_9_7_3_2.proof
theorem P0_9_7_3 : P0_9_7.c3 := P0_9_7_3.of_children P0_9_7_3_1 P0_9_7_3_2
theorem P0_9_7 : P0_9.c7 := P0_9_7.of_children P0_9_7_1 P0_9_7_2 P0_9_7_3

theorem of_bellman (h8 : P0_9.c8) : K21.c13 :=
  P0_9.of_children P0_9_1 P0_9_2 P0_9_3 P0_9_4 P0_9_5 P0_9_6 P0_9_7 h8

theorem count : K21.c13 := of_bellman P0_9_8.complete

end Low6921
