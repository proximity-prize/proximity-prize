import ProximityPrize.SubmissionLower.GoldBranch7N3
import ProximityPrize.SubmissionLower.GoldBranch7N5
import ProximityPrize.SubmissionLower.SixRows6
import ProximityPrize.SubmissionLower.SixRows7
set_option Elab.async false
set_option autoImplicit true
section
theorem Asm.P3_1 : P3.c1 := P3_1.proof
theorem Asm.P3_2 : P3.c2 := P3_2.proof
theorem Asm.P3_3_1 : P3_3.c1 := P3_3_1.proof
theorem Asm.P3_3_2 : P3_3.c2 := P3_3_2.proof
theorem Asm.P3_3 : P3.c3 := P3_3.of_children Asm.P3_3_1 Asm.P3_3_2
theorem Asm.P3_4_1 : P3_4.c1 := P3_4_1.proof
theorem Asm.P3_4_2 : P3_4.c2 := P3_4_2.proof
theorem Asm.P3_4 : P3.c4 := P3_4.of_children Asm.P3_4_1 Asm.P3_4_2
theorem Asm.P3_5 : P3.c5 := P3_5.proof
theorem Asm.P3_6_1 : P3_6.c1 := P3_6_1.proof
theorem Asm.P3_6_2 : P3_6.c2 := P3_6_2.proof
theorem Asm.P3_6_3_1 : P3_6_3.c1 := P3_6_3_1.proof
theorem Asm.P3_6_3_2 : P3_6_3.c2 := P3_6_3_2.proof
theorem Asm.P3_6_3_3 : P3_6_3.c3 := P3_6_3_3.proof
theorem Asm.P3_6_3 : P3_6.c3 := P3_6_3.of_children Asm.P3_6_3_1 Asm.P3_6_3_2 Asm.P3_6_3_3
theorem Asm.P3_6_4_1 : P3_6_4.c1 := P3_6_4_1.proof
theorem Asm.P3_6_4_2 : P3_6_4.c2 := P3_6_4_2.proof
theorem Asm.P3_6_4_3 : P3_6_4.c3 := P3_6_4_3.proof
theorem Asm.P3_6_4 : P3_6.c4 := P3_6_4.of_children Asm.P3_6_4_1 Asm.P3_6_4_2 Asm.P3_6_4_3
theorem Asm.P3_6_5_1_1_1 : P3_6_5_1_1.c1 := P3_6_5_1_1_1.proof
theorem Asm.P3_6_5_1_1_2 : P3_6_5_1_1.c2 := P3_6_5_1_1_2.proof
theorem Asm.P3_6_5_1_1_3 : P3_6_5_1_1.c3 := P3_6_5_1_1_3.proof
theorem Asm.P3_6_5_1_1 : P3_6_5_1.c1 := P3_6_5_1_1.of_children Asm.P3_6_5_1_1_1 Asm.P3_6_5_1_1_2 Asm.P3_6_5_1_1_3
theorem Asm.P3_6_5_1_2 : P3_6_5_1.c2 := P3_6_5_1_2.proof
theorem Asm.P3_6_5_1_3 : P3_6_5_1.c3 := P3_6_5_1_3.proof
theorem Asm.P3_6_5_1 : P3_6_5.c1 := P3_6_5_1.of_children Asm.P3_6_5_1_1 Asm.P3_6_5_1_2 Asm.P3_6_5_1_3
theorem Asm.P3_6_5_2 : P3_6_5.c2 := P3_6_5_2.proof
theorem Asm.P3_6_5 : P3_6.c5 := P3_6_5.of_children Asm.P3_6_5_1 Asm.P3_6_5_2
theorem Asm.P3_6_6_1 : P3_6_6.c1 := P3_6_6_1.proof
theorem Asm.P3_6_6_2_1 : P3_6_6_2.c1 := P3_6_6_2_1.proof
theorem Asm.P3_6_6_2_2 : P3_6_6_2.c2 := P3_6_6_2_2.proof
theorem Asm.P3_6_6_2_3_1 : P3_6_6_2_3.c1 := P3_6_6_2_3_1.proof
theorem Asm.P3_6_6_2_3_2 : P3_6_6_2_3.c2 := P3_6_6_2_3_2.proof
theorem Asm.P3_6_6_2_3 : P3_6_6_2.c3 := P3_6_6_2_3.of_children Asm.P3_6_6_2_3_1 Asm.P3_6_6_2_3_2
theorem Asm.P3_6_6_2 : P3_6_6.c2 := P3_6_6_2.of_children Asm.P3_6_6_2_1 Asm.P3_6_6_2_2 Asm.P3_6_6_2_3
theorem Asm.P3_6_6_3_1 : P3_6_6_3.c1 := P3_6_6_3_1.proof
theorem Asm.P3_6_6_3_2 : P3_6_6_3.c2 := P3_6_6_3_2.proof
theorem Asm.P3_6_6_3 : P3_6_6.c3 := P3_6_6_3.of_children Asm.P3_6_6_3_1 Asm.P3_6_6_3_2
theorem Asm.P3_6_6 : P3_6.c6 := P3_6_6.of_children Asm.P3_6_6_1 Asm.P3_6_6_2 Asm.P3_6_6_3
theorem Asm.P3_6_7_1 : P3_6_7.c1 := P3_6_7_1.proof
theorem Asm.P3_6_7_2_1 : P3_6_7_2.c1 := P3_6_7_2_1.proof
theorem Asm.P3_6_7_2_2 : P3_6_7_2.c2 := P3_6_7_2_2.proof
theorem Asm.P3_6_7_2_3_1 : P3_6_7_2_3.c1 := P3_6_7_2_3_1.proof
theorem Asm.P3_6_7_2_3_2 : P3_6_7_2_3.c2 := P3_6_7_2_3_2.proof
theorem Asm.P3_6_7_2_3_3 : P3_6_7_2_3.c3 := P3_6_7_2_3_3.proof
theorem Asm.P3_6_7_2_3 : P3_6_7_2.c3 := P3_6_7_2_3.of_children Asm.P3_6_7_2_3_1 Asm.P3_6_7_2_3_2 Asm.P3_6_7_2_3_3
theorem Asm.P3_6_7_2 : P3_6_7.c2 := P3_6_7_2.of_children Asm.P3_6_7_2_1 Asm.P3_6_7_2_2 Asm.P3_6_7_2_3
theorem Asm.P3_6_7_3 : P3_6_7.c3 := P3_6_7_3.proof
theorem Asm.P3_6_7 : P3_6.c7 := P3_6_7.of_children Asm.P3_6_7_1 Asm.P3_6_7_2 Asm.P3_6_7_3
theorem Asm.P3_6_8_1 : P3_6_8.c1 := P3_6_8_1.proof
theorem Asm.P3_6_8_2 : P3_6_8.c2 := P3_6_8_2.proof
theorem Asm.P3_6_8_3 : P3_6_8.c3 := P3_6_8_3.proof
theorem Asm.P3_6_8_4 : P3_6_8.c4 := P3_6_8_4.proof
theorem Asm.P3_6_8_5 : P3_6_8.c5 := P3_6_8_5.proof
theorem Asm.P3_6_8_6 : P3_6_8.c6 := P3_6_8_6.proof
theorem Asm.P3_6_8_7 : P3_6_8.c7 := P3_6_8_7.proof
theorem Asm.P3_6_8_8 : P3_6_8.c8 := P3_6_8_8.proof
theorem Asm.P3_6_8 : P3_6.c8 := P3_6_8.of_children Asm.P3_6_8_1 Asm.P3_6_8_2 Asm.P3_6_8_3 Asm.P3_6_8_4 Asm.P3_6_8_5 Asm.P3_6_8_6 Asm.P3_6_8_7 Asm.P3_6_8_8
theorem Asm.P3_6 : P3.c6 := P3_6.of_children Asm.P3_6_1 Asm.P3_6_2 Asm.P3_6_3 Asm.P3_6_4 Asm.P3_6_5 Asm.P3_6_6 Asm.P3_6_7 Asm.P3_6_8
theorem Asm.P3_7_1 : P3_7.c1 := P3_7_1.proof
theorem Asm.P3_7_2 : P3_7.c2 := P3_7_2.proof
theorem Asm.P3_7_3_1 : P3_7_3.c1 := P3_7_3_1.proof
theorem Asm.P3_7_3_2 : P3_7_3.c2 := P3_7_3_2.proof
theorem Asm.P3_7_3_3 : P3_7_3.c3 := P3_7_3_3.proof
theorem Asm.P3_7_3_4 : P3_7_3.c4 := P3_7_3_4.proof
theorem Asm.P3_7_3 : P3_7.c3 := P3_7_3.of_children Asm.P3_7_3_1 Asm.P3_7_3_2 Asm.P3_7_3_3 Asm.P3_7_3_4
theorem Asm.P3_7_4_1 : P3_7_4.c1 := P3_7_4_1.proof
theorem Asm.P3_7_4_2 : P3_7_4.c2 := P3_7_4_2.proof
theorem Asm.P3_7_4 : P3_7.c4 := P3_7_4.of_children Asm.P3_7_4_1 Asm.P3_7_4_2
theorem Asm.P3_7_5_1 : P3_7_5.c1 := P3_7_5_1.proof
theorem Asm.P3_7_5_2_1 : P3_7_5_2.c1 := P3_7_5_2_1.proof
theorem Asm.P3_7_5_2_2 : P3_7_5_2.c2 := P3_7_5_2_2.proof
theorem Asm.P3_7_5_2 : P3_7_5.c2 := P3_7_5_2.of_children Asm.P3_7_5_2_1 Asm.P3_7_5_2_2
theorem Asm.P3_7_5 : P3_7.c5 := P3_7_5.of_children Asm.P3_7_5_1 Asm.P3_7_5_2
theorem Asm.P3_7 : P3.c7 := P3_7.of_children Asm.P3_7_1 Asm.P3_7_2 Asm.P3_7_3 Asm.P3_7_4 Asm.P3_7_5
theorem Asm.CJ6_1 : CJ6.c1 := CJ6_1.proof
theorem Asm.CJ6_2 : CJ6.c2 := CJ6_2.proof
theorem Asm.CJ6_3 : CJ6.c3 := CJ6_3.proof
theorem Asm.CJ6_4 : CJ6.c4 := CJ6_4.proof
theorem Asm.CJ6_5 : CJ6.c5 := CJ6_5.proof
theorem Asm.CJ6_6 : CJ6.c6 := CJ6_6.proof
theorem Asm.CJ6_7 : CJ6.c7 := CJ6_7.proof
theorem Asm.CJ6_8 : CJ6.c8 := CJ6_8.proof
theorem Asm.CJ6 : CJ6.Cert := CJ6.of_children Asm.CJ6_1 Asm.CJ6_2 Asm.CJ6_3 Asm.CJ6_4 Asm.CJ6_5 Asm.CJ6_6 Asm.CJ6_7 Asm.CJ6_8
theorem Asm.P3 : ProximityPrize.Benchmark.ProtocolClaim 6944 336532029 1073741824 := P3.of_children Asm.P3_1 Asm.P3_2 Asm.P3_3 Asm.P3_4 Asm.P3_5 Asm.P3_6 Asm.P3_7 Asm.CJ6
end
theorem ProximityPrize.Benchmark.candidate : ProximityPrize.Benchmark.ProtocolClaim 6944 336532029 1073741824 :=
  Asm.P3
