import ProximityPrize.SubmissionLower.PortFrontB
import ProximityPrize.SubmissionLower.PortHighFinish
import ProximityPrize.SubmissionLower.PortLow5
import ProximityPrize.SubmissionLower.PortLow8
set_option Elab.async false

section PackSource_Asm_P0
set_option autoImplicit true
theorem Asm.P0_1_1 : P0_1.c1 := P0_1_1.proof
theorem Asm.P0_1_2 : P0_1.c2 := P0_1_2.proof
theorem Asm.P0_1 : P0.c1 := P0_1.of_children Asm.P0_1_1 Asm.P0_1_2
theorem Asm.P0_2 : P0.c2 := P0_2.proof
theorem Asm.P0_3 : P0.c3 := P0_3.proof
theorem Asm.P0_4 : P0.c4 := P0_4.proof
theorem Asm.P0_5 : P0.c5 := P0_5.proof
theorem Asm.P0_6_1 : P0_6.c1 := P0_6_1.proof
theorem Asm.P0_6_2 : P0_6.c2 := P0_6_2.proof
theorem Asm.P0_6 : P0.c6 := P0_6.of_children Asm.P0_6_1 Asm.P0_6_2
theorem Asm.P0_7_1 : P0_7.c1 := P0_7_1.proof
theorem Asm.P0_7_2 : P0_7.c2 := P0_7_2.proof
theorem Asm.P0_7 : P0.c7 := P0_7.of_children Asm.P0_7_1 Asm.P0_7_2
theorem Asm.P0_8_1 : P0_8.c1 := P0_8_1.proof
theorem Asm.P0_8_2 : P0_8.c2 := P0_8_2.proof
theorem Asm.P0_8_3 : P0_8.c3 := P0_8_3.proof
theorem Asm.P0_8 : P0.c8 := P0_8.of_children Asm.P0_8_1 Asm.P0_8_2 Asm.P0_8_3
theorem Asm.P0_9_1 : P0_9.c1 := P0_9_1.proof
theorem Asm.P0_9_2 : P0_9.c2 := P0_9_2.proof
theorem Asm.P0_9_3_1 : P0_9_3.c1 := P0_9_3_1.proof
theorem Asm.P0_9_3_2 : P0_9_3.c2 := P0_9_3_2.proof
theorem Asm.P0_9_3 : P0_9.c3 := P0_9_3.of_children Asm.P0_9_3_1 Asm.P0_9_3_2
theorem Asm.P0_9_4_1 : P0_9_4.c1 := P0_9_4_1.proof
theorem Asm.P0_9_4_2 : P0_9_4.c2 := P0_9_4_2.proof
theorem Asm.P0_9_4 : P0_9.c4 := P0_9_4.of_children Asm.P0_9_4_1 Asm.P0_9_4_2
theorem Asm.P0_9_5_1_1 : P0_9_5_1.c1 := P0_9_5_1_1.proof
theorem Asm.P0_9_5_1_2_1 : P0_9_5_1_2.c1 := P0_9_5_1_2_1.proof
theorem Asm.P0_9_5_1_2_2 : P0_9_5_1_2.c2 := P0_9_5_1_2_2.proof
theorem Asm.P0_9_5_1_2_3 : P0_9_5_1_2.c3 := P0_9_5_1_2_3.proof
theorem Asm.P0_9_5_1_2 : P0_9_5_1.c2 := P0_9_5_1_2.of_children Asm.P0_9_5_1_2_1 Asm.P0_9_5_1_2_2 Asm.P0_9_5_1_2_3
theorem Asm.P0_9_5_1_3 : P0_9_5_1.c3 := P0_9_5_1_3.proof
theorem Asm.P0_9_5_1_4 : P0_9_5_1.c4 := P0_9_5_1_4.proof
theorem Asm.P0_9_5_1 : P0_9_5.c1 := P0_9_5_1.of_children Asm.P0_9_5_1_1 Asm.P0_9_5_1_2 Asm.P0_9_5_1_3 Asm.P0_9_5_1_4
theorem Asm.P0_9_5_2 : P0_9_5.c2 := P0_9_5_2.proof
theorem Asm.P0_9_5 : P0_9.c5 := P0_9_5.of_children Asm.P0_9_5_1 Asm.P0_9_5_2
theorem Asm.P0_9_6_1_1 : P0_9_6_1.c1 := P0_9_6_1_1.proof
theorem Asm.P0_9_6_1_2 : P0_9_6_1.c2 := P0_9_6_1_2.proof
theorem Asm.P0_9_6_1 : P0_9_6.c1 := P0_9_6_1.of_children Asm.P0_9_6_1_1 Asm.P0_9_6_1_2
theorem Asm.P0_9_6_2_1 : P0_9_6_2.c1 := P0_9_6_2_1.proof
theorem Asm.P0_9_6_2_2 : P0_9_6_2.c2 := P0_9_6_2_2.proof
theorem Asm.P0_9_6_2_3_1 : P0_9_6_2_3.c1 := P0_9_6_2_3_1.proof
theorem Asm.P0_9_6_2_3_2 : P0_9_6_2_3.c2 := P0_9_6_2_3_2.proof
theorem Asm.P0_9_6_2_3 : P0_9_6_2.c3 := P0_9_6_2_3.of_children Asm.P0_9_6_2_3_1 Asm.P0_9_6_2_3_2
theorem Asm.P0_9_6_2 : P0_9_6.c2 := P0_9_6_2.of_children Asm.P0_9_6_2_1 Asm.P0_9_6_2_2 Asm.P0_9_6_2_3
theorem Asm.P0_9_6_3_1 : P0_9_6_3.c1 := P0_9_6_3_1.proof
theorem Asm.P0_9_6_3_2 : P0_9_6_3.c2 := P0_9_6_3_2.proof
theorem Asm.P0_9_6_3 : P0_9_6.c3 := P0_9_6_3.of_children Asm.P0_9_6_3_1 Asm.P0_9_6_3_2
theorem Asm.P0_9_6 : P0_9.c6 := P0_9_6.of_children Asm.P0_9_6_1 Asm.P0_9_6_2 Asm.P0_9_6_3
theorem Asm.P0_9_7_1 : P0_9_7.c1 := P0_9_7_1.proof
theorem Asm.P0_9_7_2_1 : P0_9_7_2.c1 := P0_9_7_2_1.proof
theorem Asm.P0_9_7_2_2 : P0_9_7_2.c2 := P0_9_7_2_2.proof
theorem Asm.P0_9_7_2_3_1 : P0_9_7_2_3.c1 := P0_9_7_2_3_1.proof
theorem Asm.P0_9_7_2_3_2_1 : P0_9_7_2_3_2.c1 := P0_9_7_2_3_2_1.proof
theorem Asm.P0_9_7_2_3_2_2 : P0_9_7_2_3_2.c2 := P0_9_7_2_3_2_2.proof
theorem Asm.P0_9_7_2_3_2 : P0_9_7_2_3.c2 := P0_9_7_2_3_2.of_children Asm.P0_9_7_2_3_2_1 Asm.P0_9_7_2_3_2_2
theorem Asm.P0_9_7_2_3_3 : P0_9_7_2_3.c3 := P0_9_7_2_3_3.proof
theorem Asm.P0_9_7_2_3 : P0_9_7_2.c3 := P0_9_7_2_3.of_children Asm.P0_9_7_2_3_1 Asm.P0_9_7_2_3_2 Asm.P0_9_7_2_3_3
theorem Asm.P0_9_7_2 : P0_9_7.c2 := P0_9_7_2.of_children Asm.P0_9_7_2_1 Asm.P0_9_7_2_2 Asm.P0_9_7_2_3
theorem Asm.P0_9_7_3_1 : P0_9_7_3.c1 := P0_9_7_3_1.proof
theorem Asm.P0_9_7_3_2 : P0_9_7_3.c2 := P0_9_7_3_2.proof
theorem Asm.P0_9_7_3 : P0_9_7.c3 := P0_9_7_3.of_children Asm.P0_9_7_3_1 Asm.P0_9_7_3_2
theorem Asm.P0_9_7 : P0_9.c7 := P0_9_7.of_children Asm.P0_9_7_1 Asm.P0_9_7_2 Asm.P0_9_7_3
theorem Asm.P0_9_8_1 : P0_9_8.c1 := P0_9_8_1.proof
theorem Asm.P0_9_8_2 : P0_9_8.c2 := P0_9_8_2.proof
theorem Asm.P0_9_8_3 : P0_9_8.c3 := P0_9_8_3.proof
theorem Asm.P0_9_8_4 : P0_9_8.c4 := P0_9_8_4.proof
theorem Asm.P0_9_8_5 : P0_9_8.c5 := P0_9_8_5.proof
theorem Asm.P0_9_8_6 : P0_9_8.c6 := P0_9_8_6.proof
theorem Asm.P0_9_8_7 : P0_9_8.c7 := P0_9_8_7.proof
theorem Asm.P0_9_8 : P0_9.c8 := P0_9_8.of_children Asm.P0_9_8_1 Asm.P0_9_8_2 Asm.P0_9_8_3 Asm.P0_9_8_4 Asm.P0_9_8_5 Asm.P0_9_8_6 Asm.P0_9_8_7
theorem Asm.P0_9 : P0.c9 := P0_9.of_children Asm.P0_9_1 Asm.P0_9_2 Asm.P0_9_3 Asm.P0_9_4 Asm.P0_9_5 Asm.P0_9_6 Asm.P0_9_7 Asm.P0_9_8
theorem Asm.P0_10_1_1 : P0_10_1.c1 := P0_10_1_1.proof
theorem Asm.P0_10_1_2 : P0_10_1.c2 := P0_10_1_2.proof
theorem Asm.P0_10_1 : P0_10.c1 := P0_10_1.of_children Asm.P0_10_1_1 Asm.P0_10_1_2
theorem Asm.P0_10_2 : P0_10.c2 := P0_10_2.proof
theorem Asm.P0_10_5 : P0_10.c5 := P0_10_5.proof
theorem Asm.P0_10R_1 : P0_10R.c1 := P0_10R_1.proof
theorem Asm.P0_10R_2 : P0_10R.c2 := P0_10R_2.proof
theorem Asm.P0_10R_3 : P0_10R.c3 := P0_10R_3.proof
theorem Asm.P0_10R_4 : P0_10R.c4 := P0_10R_4.proof
theorem Asm.P0_10R_5 : P0_10R.c5 := P0_10R_5.proof
theorem Asm.P0_10R : P0.c10 := P0_10R.of_children Asm.P0_10_1 Asm.P0_10_2 Asm.P0_10_5 Asm.P0_10R_1 Asm.P0_10R_2 Asm.P0_10R_3 Asm.P0_10R_4 Asm.P0_10R_5
theorem Asm.P0_10 : P0.c10 := Asm.P0_10R
theorem Asm.P0_11 : P0.c11 := P0_11.proof
theorem Asm.P0 : ProximityPrize.Benchmark.ProtocolClaim 6921 335613951 1073741824 := P0.of_children Asm.P0_1 Asm.P0_2 Asm.P0_3 Asm.P0_4 Asm.P0_5 Asm.P0_6 Asm.P0_7 Asm.P0_8 Asm.P0_9 Asm.P0_10 Asm.P0_11
end PackSource_Asm_P0

theorem ProximityPrize.Benchmark.candidate : ProximityPrize.Benchmark.ProtocolClaim 6921 335613951 1073741824 :=
  Asm.P0
