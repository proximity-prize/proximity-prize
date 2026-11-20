import ProximityPrize.SubmissionLower.Fast000
import ProximityPrize.SubmissionLower.Fast004
import ProximityPrize.SubmissionLower.Fast001
import ProximityPrize.SubmissionLower.Fast002
import ProximityPrize.SubmissionLower.Fast005
import ProximityPrize.SubmissionLower.Fast006
import ProximityPrize.SubmissionLower.Fast003
import ProximityPrize.SubmissionLower.Fast007
import ProximityPrize.SubmissionLower.Fast008
import ProximityPrize.SubmissionLower.Fast009
import ProximityPrize.SubmissionLower.Fast010
import ProximityPrize.SubmissionLower.Fast011
import ProximityPrize.SubmissionLower.Fast012
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Fast013
import ProximityPrize.SubmissionLower.Fast015
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast076
import ProximityPrize.SubmissionLower.Fast050
import ProximityPrize.SubmissionLower.Fast054
import ProximityPrize.SubmissionLower.Fast072
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast051
import ProximityPrize.SubmissionLower.Fast022
import ProximityPrize.SubmissionLower.Numeric6Defs
import ProximityPrize.SubmissionLower.Numeric6AuxCert
import ProximityPrize.SubmissionLower.Fast060
import ProximityPrize.SubmissionLower.Numeric2Aux
import ProximityPrize.SubmissionLower.Numeric5Defs
import ProximityPrize.SubmissionLower.Numeric5Certificate
import ProximityPrize.SubmissionLower.Fast049
import ProximityPrize.SubmissionLower.Fast061
import ProximityPrize.SubmissionLower.Fast074
import ProximityPrize.SubmissionLower.Fast048
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast066
import ProximityPrize.SubmissionLower.Fast019
import ProximityPrize.SubmissionLower.Fast020
import ProximityPrize.SubmissionLower.Pack_K1_13_6_1_4Geometry
import ProximityPrize.SubmissionLower.Fast063
import ProximityPrize.SubmissionLower.Fast071
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast065
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split
import ProximityPrize.SubmissionLower.Pack_K1_14_2_2Split
import ProximityPrize.SubmissionLower.Fast032
import ProximityPrize.SubmissionLower.Pack_K1_14_2_2_4Split
import ProximityPrize.SubmissionLower.Fast062
import ProximityPrize.SubmissionLower.Pack_K1_14_3Split
import ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter
import ProximityPrize.SubmissionLower.Fast052
import ProximityPrize.SubmissionLower.Fast053
import ProximityPrize.SubmissionLower.Fast057
import ProximityPrize.SubmissionLower.Fast035
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2Split
import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_5_3Proof
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_3Aux3
import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_7Proof
import ProximityPrize.SubmissionLower.Fast073
import ProximityPrize.SubmissionLower.Fast040
import ProximityPrize.SubmissionLower.Fast058
import ProximityPrize.SubmissionLower.Fast059
import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast056
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
import ProximityPrize.SubmissionLower.Fast064
import ProximityPrize.SubmissionLower.Fast070
import ProximityPrize.SubmissionLower.Fast067
import ProximityPrize.SubmissionLower.Fast077
import ProximityPrize.SubmissionLower.Fast044
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_3Split
import ProximityPrize.SubmissionLower.Fast069
import ProximityPrize.SubmissionLower.Fast075
set_option Elab.async false

theorem Asm.K1_1 : K1.c1 := K1_1.proof
theorem Asm.K1_2_1 : K1_2.c1 := K1_2_1.proof
theorem Asm.K1_2_2_1 : K1_2_2.c1 := K1_2_2_1.proof
theorem Asm.K1_2_2_2 : K1_2_2.c2 := K1_2_2_2.proof
theorem Asm.K1_2_2 : K1_2.c2 := K1_2_2.of_children Asm.K1_2_2_1 Asm.K1_2_2_2
theorem Asm.K1_2_3 : K1_2.c3 := K1_2_3.proof
theorem Asm.K1_2_4_1_1 : K1_2_4_1.c1 := K1_2_4_1_1.proof
theorem Asm.K1_2_4_1_2 : K1_2_4_1.c2 := K1_2_4_1_2.proof
theorem Asm.K1_2_4_1 : K1_2_4.c1 := K1_2_4_1.of_children Asm.K1_2_4_1_1 Asm.K1_2_4_1_2
theorem Asm.K1_2_4_2 : K1_2_4.c2 := K1_2_4_2.proof
theorem Asm.K1_2_4_3 : K1_2_4.c3 := K1_2_4_3.proof
theorem Asm.K1_2_4 : K1_2.c4 := K1_2_4.of_children Asm.K1_2_4_1 Asm.K1_2_4_2 Asm.K1_2_4_3
theorem Asm.K1_2 : K1.c2 := K1_2.of_children Asm.K1_2_1 Asm.K1_2_2 Asm.K1_2_3 Asm.K1_2_4
theorem Asm.K1_3 : K1.c3 := K1_3.proof
theorem Asm.K1_4 : K1.c4 := K1_4.proof
theorem Asm.K1_5 : K1.c5 := K1_5.proof
theorem Asm.K1_6_1 : K1_6.c1 := K1_6_1.proof
theorem Asm.K1_6_2 : K1_6.c2 := K1_6_2.proof
theorem Asm.K1_6 : K1.c6 := K1_6.of_children Asm.K1_6_1 Asm.K1_6_2
theorem Asm.K1_7 : K1.c7 := K1_7.proof
theorem Asm.K1_8_1 : K1_8.c1 := K1_8_1.proof
theorem Asm.K1_8_2 : K1_8.c2 := K1_8_2.proof
theorem Asm.K1_8 : K1.c8 := K1_8.of_children Asm.K1_8_1 Asm.K1_8_2
theorem Asm.K1_9_1 : K1_9.c1 := K1_9_1.proof
theorem Asm.K1_9_2 : K1_9.c2 := K1_9_2.proof
theorem Asm.K1_9 : K1.c9 := K1_9.of_children Asm.K1_9_1 Asm.K1_9_2
theorem Asm.K1_10_1_1 : K1_10_1.c1 := K1_10_1_1.proof
theorem Asm.K1_10_1_2 : K1_10_1.c2 := K1_10_1_2.proof
theorem Asm.K1_10_1_3 : K1_10_1.c3 := K1_10_1_3.proof
theorem Asm.K1_10_1 : K1_10.c1 := K1_10_1.of_children Asm.K1_10_1_1 Asm.K1_10_1_2 Asm.K1_10_1_3
theorem Asm.K1_10_2_1 : K1_10_2.c1 := K1_10_2_1.proof
theorem Asm.K1_10_2_2 : K1_10_2.c2 := K1_10_2_2.proof
theorem Asm.K1_10_2 : K1_10.c2 := K1_10_2.of_children Asm.K1_10_2_1 Asm.K1_10_2_2
theorem Asm.K1_10 : K1.c10 := K1_10.of_children Asm.K1_10_1 Asm.K1_10_2
theorem Asm.K1_11_1_1 : K1_11_1.c1 := K1_11_1_1.proof
theorem Asm.K1_11_1_2 : K1_11_1.c2 := K1_11_1_2.proof
theorem Asm.K1_11_1 : K1_11.c1 := K1_11_1.of_children Asm.K1_11_1_1 Asm.K1_11_1_2
theorem Asm.K1_11_2_1 : K1_11_2.c1 := K1_11_2_1.proof
theorem Asm.K1_11_2_2 : K1_11_2.c2 := K1_11_2_2.proof
theorem Asm.K1_11_2 : K1_11.c2 := K1_11_2.of_children Asm.K1_11_2_1 Asm.K1_11_2_2
theorem Asm.K1_11_3_1 : K1_11_3.c1 := K1_11_3_1.proof
theorem Asm.K1_11_3_2 : K1_11_3.c2 := K1_11_3_2.proof
theorem Asm.K1_11_3 : K1_11.c3 := K1_11_3.of_children Asm.K1_11_3_1 Asm.K1_11_3_2
theorem Asm.K1_11 : K1.c11 := K1_11.of_children Asm.K1_11_1 Asm.K1_11_2 Asm.K1_11_3
theorem Asm.K1_12_1 : K1_12.c1 := K1_12_1.proof
theorem Asm.K1_12_2 : K1_12.c2 := K1_12_2.proof
theorem Asm.K1_12 : K1.c12 := K1_12.of_children Asm.K1_12_1 Asm.K1_12_2
theorem Asm.K1_13_1_1_1 : K1_13_1_1.c1 := K1_13_1_1_1.proof
theorem Asm.K1_13_1_1_2 : K1_13_1_1.c2 := K1_13_1_1_2.proof
theorem Asm.K1_13_1_1_3 : K1_13_1_1.c3 := K1_13_1_1_3.proof
theorem Asm.K1_13_1_1 : K1_13_1.c1 := K1_13_1_1.of_children Asm.K1_13_1_1_1 Asm.K1_13_1_1_2 Asm.K1_13_1_1_3
theorem Asm.K1_13_1_2 : K1_13_1.c2 := K1_13_1_2.proof
theorem Asm.K1_13_1 : K1_13.c1 := K1_13_1.of_children Asm.K1_13_1_1 Asm.K1_13_1_2
theorem Asm.K1_13_2_1 : K1_13_2.c1 := K1_13_2_1.proof
theorem Asm.K1_13_2_2_1 : K1_13_2_2.c1 := K1_13_2_2_1.proof
theorem Asm.K1_13_2_2_2 : K1_13_2_2.c2 := K1_13_2_2_2.proof
theorem Asm.K1_13_2_2_3 : K1_13_2_2.c3 := K1_13_2_2_3.proof
theorem Asm.K1_13_2_2_4 : K1_13_2_2.c4 := K1_13_2_2_4.proof
theorem Asm.K1_13_2_2_5 : K1_13_2_2.c5 := K1_13_2_2_5.proof
theorem Asm.K1_13_2_2 : K1_13_2.c2 := K1_13_2_2.of_children Asm.K1_13_2_2_1 Asm.K1_13_2_2_2 Asm.K1_13_2_2_3 Asm.K1_13_2_2_4 Asm.K1_13_2_2_5
theorem Asm.K1_13_2_3_1 : K1_13_2_3.c1 := K1_13_2_3_1.proof
theorem Asm.K1_13_2_3_2 : K1_13_2_3.c2 := K1_13_2_3_2.proof
theorem Asm.K1_13_2_3_3 : K1_13_2_3.c3 := K1_13_2_3_3.proof
theorem Asm.K1_13_2_3_4 : K1_13_2_3.c4 := K1_13_2_3_4.proof
theorem Asm.K1_13_2_3_5 : K1_13_2_3.c5 := K1_13_2_3_5.proof
theorem Asm.K1_13_2_3_6 : K1_13_2_3.c6 := K1_13_2_3_6.proof
theorem Asm.K1_13_2_3_7 : K1_13_2_3.c7 := K1_13_2_3_7.proof
theorem Asm.K1_13_2_3 : K1_13_2.c3 := K1_13_2_3.of_children Asm.K1_13_2_3_1 Asm.K1_13_2_3_2 Asm.K1_13_2_3_3 Asm.K1_13_2_3_4 Asm.K1_13_2_3_5 Asm.K1_13_2_3_6 Asm.K1_13_2_3_7
theorem Asm.K1_13_2 : K1_13.c2 := K1_13_2.of_children Asm.K1_13_2_1 Asm.K1_13_2_2 Asm.K1_13_2_3
theorem Asm.K1_13_3_1 : K1_13_3.c1 := K1_13_3_1.proof
theorem Asm.K1_13_3_2 : K1_13_3.c2 := K1_13_3_2.proof
theorem Asm.K1_13_3 : K1_13.c3 := K1_13_3.of_children Asm.K1_13_3_1 Asm.K1_13_3_2
theorem Asm.K1_13_4_1 : K1_13_4.c1 := K1_13_4_1.proof
theorem Asm.K1_13_4_2_1 : K1_13_4_2.c1 := K1_13_4_2_1.proof
theorem Asm.K1_13_4_2_2_1 : K1_13_4_2_2.c1 := K1_13_4_2_2_1.proof
theorem Asm.K1_13_4_2_2_2 : K1_13_4_2_2.c2 := K1_13_4_2_2_2.proof
theorem Asm.K1_13_4_2_2_3 : K1_13_4_2_2.c3 := K1_13_4_2_2_3.proof
theorem Asm.K1_13_4_2_2_4 : K1_13_4_2_2.c4 := K1_13_4_2_2_4.proof
theorem Asm.K1_13_4_2_2_5 : K1_13_4_2_2.c5 := K1_13_4_2_2_5.proof
theorem Asm.K1_13_4_2_2_6 : K1_13_4_2_2.c6 := K1_13_4_2_2_6.proof
theorem Asm.K1_13_4_2_2 : K1_13_4_2.c2 := K1_13_4_2_2.of_children Asm.K1_13_4_2_2_1 Asm.K1_13_4_2_2_2 Asm.K1_13_4_2_2_3 Asm.K1_13_4_2_2_4 Asm.K1_13_4_2_2_5 Asm.K1_13_4_2_2_6
theorem Asm.K1_13_4_2_3_1 : K1_13_4_2_3.c1 := K1_13_4_2_3_1.proof
theorem Asm.K1_13_4_2_3_2 : K1_13_4_2_3.c2 := K1_13_4_2_3_2.proof
theorem Asm.K1_13_4_2_3 : K1_13_4_2.c3 := K1_13_4_2_3.of_children Asm.K1_13_4_2_3_1 Asm.K1_13_4_2_3_2
theorem Asm.K1_13_4_2_4_1 : K1_13_4_2_4.c1 := K1_13_4_2_4_1.proof
theorem Asm.K1_13_4_2_4_2 : K1_13_4_2_4.c2 := K1_13_4_2_4_2.proof
theorem Asm.K1_13_4_2_4 : K1_13_4_2.c4 := K1_13_4_2_4.of_children Asm.K1_13_4_2_4_1 Asm.K1_13_4_2_4_2
theorem Asm.K1_13_4_2 : K1_13_4.c2 := K1_13_4_2.of_children Asm.K1_13_4_2_1 Asm.K1_13_4_2_2 Asm.K1_13_4_2_3 Asm.K1_13_4_2_4
theorem Asm.K1_13_4_3_1 : K1_13_4_3.c1 := K1_13_4_3_1.proof
theorem Asm.K1_13_4_3_2 : K1_13_4_3.c2 := K1_13_4_3_2.proof
theorem Asm.K1_13_4_3_3 : K1_13_4_3.c3 := K1_13_4_3_3.proof
theorem Asm.K1_13_4_3 : K1_13_4.c3 := K1_13_4_3.of_children Asm.K1_13_4_3_1 Asm.K1_13_4_3_2 Asm.K1_13_4_3_3
theorem Asm.K1_13_4_4_1 : K1_13_4_4.c1 := K1_13_4_4_1.proof
theorem Asm.K1_13_4_4_2 : K1_13_4_4.c2 := K1_13_4_4_2.proof
theorem Asm.K1_13_4_4 : K1_13_4.c4 := K1_13_4_4.of_children Asm.K1_13_4_4_1 Asm.K1_13_4_4_2
theorem Asm.K1_13_4_5_1 : K1_13_4_5.c1 := K1_13_4_5_1.proof
theorem Asm.K1_13_4_5_2 : K1_13_4_5.c2 := K1_13_4_5_2.proof
theorem Asm.K1_13_4_5 : K1_13_4.c5 := K1_13_4_5.of_children Asm.K1_13_4_5_1 Asm.K1_13_4_5_2
theorem Asm.K1_13_4_6 : K1_13_4.c6 := K1_13_4_6.proof
theorem Asm.K1_13_4_7 : K1_13_4.c7 := K1_13_4_7.proof
theorem Asm.K1_13_4 : K1_13.c4 := K1_13_4.of_children Asm.K1_13_4_1 Asm.K1_13_4_2 Asm.K1_13_4_3 Asm.K1_13_4_4 Asm.K1_13_4_5 Asm.K1_13_4_6 Asm.K1_13_4_7
theorem Asm.K1_13_5_1 : K1_13_5.c1 := K1_13_5_1.proof
theorem Asm.K1_13_5_2 : K1_13_5.c2 := K1_13_5_2.proof
theorem Asm.K1_13_5_3 : K1_13_5.c3 := K1_13_5_3.proof
theorem Asm.K1_13_5_4_1_1 : K1_13_5_4_1.c1 := K1_13_5_4_1_1.proof
theorem Asm.K1_13_5_4_1_2 : K1_13_5_4_1.c2 := K1_13_5_4_1_2.proof
theorem Asm.K1_13_5_4_1 : K1_13_5_4.c1 := K1_13_5_4_1.of_children Asm.K1_13_5_4_1_1 Asm.K1_13_5_4_1_2
theorem Asm.K1_13_5_4_2_1 : K1_13_5_4_2.c1 := K1_13_5_4_2_1.proof
theorem Asm.K1_13_5_4_2_2_1 : K1_13_5_4_2_2.c1 := K1_13_5_4_2_2_1.proof
theorem Asm.K1_13_5_4_2_2_2 : K1_13_5_4_2_2.c2 := K1_13_5_4_2_2_2.proof
theorem Asm.K1_13_5_4_2_2_3 : K1_13_5_4_2_2.c3 := K1_13_5_4_2_2_3.proof
theorem Asm.K1_13_5_4_2_2 : K1_13_5_4_2.c2 := K1_13_5_4_2_2.of_children Asm.K1_13_5_4_2_2_1 Asm.K1_13_5_4_2_2_2 Asm.K1_13_5_4_2_2_3
theorem Asm.K1_13_5_4_2_3_1 : K1_13_5_4_2_3.c1 := K1_13_5_4_2_3_1.proof
theorem Asm.K1_13_5_4_2_3_2 : K1_13_5_4_2_3.c2 := K1_13_5_4_2_3_2.proof
theorem Asm.K1_13_5_4_2_3 : K1_13_5_4_2.c3 := K1_13_5_4_2_3.of_children Asm.K1_13_5_4_2_3_1 Asm.K1_13_5_4_2_3_2
theorem Asm.K1_13_5_4_2_4_1_1 : K1_13_5_4_2_4_1.c1 := K1_13_5_4_2_4_1_1.proof
theorem Asm.K1_13_5_4_2_4_1_2 : K1_13_5_4_2_4_1.c2 := K1_13_5_4_2_4_1_2.proof
theorem Asm.K1_13_5_4_2_4_1 : K1_13_5_4_2_4.c1 := K1_13_5_4_2_4_1.of_children Asm.K1_13_5_4_2_4_1_1 Asm.K1_13_5_4_2_4_1_2
theorem Asm.K1_13_5_4_2_4_2_1 : K1_13_5_4_2_4_2.c1 := K1_13_5_4_2_4_2_1.proof
theorem Asm.K1_13_5_4_2_4_2_2 : K1_13_5_4_2_4_2.c2 := K1_13_5_4_2_4_2_2.proof
theorem Asm.K1_13_5_4_2_4_2_3_1 : K1_13_5_4_2_4_2_3.c1 := K1_13_5_4_2_4_2_3_1.proof
theorem Asm.K1_13_5_4_2_4_2_3_2 : K1_13_5_4_2_4_2_3.c2 := K1_13_5_4_2_4_2_3_2.proof
theorem Asm.K1_13_5_4_2_4_2_3 : K1_13_5_4_2_4_2.c3 := K1_13_5_4_2_4_2_3.of_children Asm.K1_13_5_4_2_4_2_3_1 Asm.K1_13_5_4_2_4_2_3_2
theorem Asm.K1_13_5_4_2_4_2 : K1_13_5_4_2_4.c2 := K1_13_5_4_2_4_2.of_children Asm.K1_13_5_4_2_4_2_1 Asm.K1_13_5_4_2_4_2_2 Asm.K1_13_5_4_2_4_2_3
theorem Asm.K1_13_5_4_2_4_3 : K1_13_5_4_2_4.c3 := K1_13_5_4_2_4_3.proof
theorem Asm.K1_13_5_4_2_4 : K1_13_5_4_2.c4 := K1_13_5_4_2_4.of_children Asm.K1_13_5_4_2_4_1 Asm.K1_13_5_4_2_4_2 Asm.K1_13_5_4_2_4_3
theorem Asm.K1_13_5_4_2_5_1_1_1 : K1_13_5_4_2_5_1_1.c1 := K1_13_5_4_2_5_1_1_1.proof
theorem Asm.K1_13_5_4_2_5_1_1_2 : K1_13_5_4_2_5_1_1.c2 := K1_13_5_4_2_5_1_1_2.proof
theorem Asm.K1_13_5_4_2_5_1_1 : K1_13_5_4_2_5_1.c1 := K1_13_5_4_2_5_1_1.of_children Asm.K1_13_5_4_2_5_1_1_1 Asm.K1_13_5_4_2_5_1_1_2
theorem Asm.K1_13_5_4_2_5_1_2 : K1_13_5_4_2_5_1.c2 := K1_13_5_4_2_5_1_2.proof
theorem Asm.K1_13_5_4_2_5_1 : K1_13_5_4_2_5.c1 := K1_13_5_4_2_5_1.of_children Asm.K1_13_5_4_2_5_1_1 Asm.K1_13_5_4_2_5_1_2
theorem Asm.K1_13_5_4_2_5_2_1_1 : K1_13_5_4_2_5_2_1.c1 := K1_13_5_4_2_5_2_1_1.proof
theorem Asm.K1_13_5_4_2_5_2_1_2 : K1_13_5_4_2_5_2_1.c2 := K1_13_5_4_2_5_2_1_2.proof
theorem Asm.K1_13_5_4_2_5_2_1 : K1_13_5_4_2_5_2.c1 := K1_13_5_4_2_5_2_1.of_children Asm.K1_13_5_4_2_5_2_1_1 Asm.K1_13_5_4_2_5_2_1_2
theorem Asm.K1_13_5_4_2_5_2_2 : K1_13_5_4_2_5_2.c2 := K1_13_5_4_2_5_2_2.proof
theorem Asm.K1_13_5_4_2_5_2 : K1_13_5_4_2_5.c2 := K1_13_5_4_2_5_2.of_children Asm.K1_13_5_4_2_5_2_1 Asm.K1_13_5_4_2_5_2_2
theorem Asm.K1_13_5_4_2_5 : K1_13_5_4_2.c5 := K1_13_5_4_2_5.of_children Asm.K1_13_5_4_2_5_1 Asm.K1_13_5_4_2_5_2
theorem Asm.K1_13_5_4_2 : K1_13_5_4.c2 := K1_13_5_4_2.of_children Asm.K1_13_5_4_2_1 Asm.K1_13_5_4_2_2 Asm.K1_13_5_4_2_3 Asm.K1_13_5_4_2_4 Asm.K1_13_5_4_2_5
theorem Asm.K1_13_5_4_3_1 : K1_13_5_4_3.c1 := K1_13_5_4_3_1.proof
theorem Asm.K1_13_5_4_3_2 : K1_13_5_4_3.c2 := K1_13_5_4_3_2.proof
theorem Asm.K1_13_5_4_3_3 : K1_13_5_4_3.c3 := K1_13_5_4_3_3.proof
theorem Asm.K1_13_5_4_3_4 : K1_13_5_4_3.c4 := K1_13_5_4_3_4.proof
theorem Asm.K1_13_5_4_3 : K1_13_5_4.c3 := K1_13_5_4_3.of_children Asm.K1_13_5_4_3_1 Asm.K1_13_5_4_3_2 Asm.K1_13_5_4_3_3 Asm.K1_13_5_4_3_4
theorem Asm.K1_13_5_4_4_1_1 : K1_13_5_4_4_1.c1 := K1_13_5_4_4_1_1.proof
theorem Asm.K1_13_5_4_4_1_2 : K1_13_5_4_4_1.c2 := K1_13_5_4_4_1_2.proof
theorem Asm.K1_13_5_4_4_1 : K1_13_5_4_4.c1 := K1_13_5_4_4_1.of_children Asm.K1_13_5_4_4_1_1 Asm.K1_13_5_4_4_1_2
theorem Asm.K1_13_5_4_4_2 : K1_13_5_4_4.c2 := K1_13_5_4_4_2.proof
theorem Asm.K1_13_5_4_4 : K1_13_5_4.c4 := K1_13_5_4_4.of_children Asm.K1_13_5_4_4_1 Asm.K1_13_5_4_4_2
theorem Asm.K1_13_5_4 : K1_13_5.c4 := K1_13_5_4.of_children Asm.K1_13_5_4_1 Asm.K1_13_5_4_2 Asm.K1_13_5_4_3 Asm.K1_13_5_4_4
theorem Asm.K1_13_5_5_1_1 : K1_13_5_5_1.c1 := K1_13_5_5_1_1.proof
theorem Asm.K1_13_5_5_1_2 : K1_13_5_5_1.c2 := K1_13_5_5_1_2.proof
theorem Asm.K1_13_5_5_1_3 : K1_13_5_5_1.c3 := K1_13_5_5_1_3.proof
theorem Asm.K1_13_5_5_1 : K1_13_5_5.c1 := K1_13_5_5_1.of_children Asm.K1_13_5_5_1_1 Asm.K1_13_5_5_1_2 Asm.K1_13_5_5_1_3
theorem Asm.K1_13_5_5_2_1_1_1 : K1_13_5_5_2_1_1.c1 := K1_13_5_5_2_1_1_1.proof
theorem Asm.K1_13_5_5_2_1_1_2 : K1_13_5_5_2_1_1.c2 := K1_13_5_5_2_1_1_2.proof
theorem Asm.K1_13_5_5_2_1_1_3 : K1_13_5_5_2_1_1.c3 := K1_13_5_5_2_1_1_3.proof
theorem Asm.K1_13_5_5_2_1_1 : K1_13_5_5_2_1.c1 := K1_13_5_5_2_1_1.of_children Asm.K1_13_5_5_2_1_1_1 Asm.K1_13_5_5_2_1_1_2 Asm.K1_13_5_5_2_1_1_3
theorem Asm.K1_13_5_5_2_1_2 : K1_13_5_5_2_1.c2 := K1_13_5_5_2_1_2.proof
theorem Asm.K1_13_5_5_2_1_3 : K1_13_5_5_2_1.c3 := K1_13_5_5_2_1_3.proof
theorem Asm.K1_13_5_5_2_1_4_1 : K1_13_5_5_2_1_4.c1 := K1_13_5_5_2_1_4_1.proof
theorem Asm.K1_13_5_5_2_1_4_2 : K1_13_5_5_2_1_4.c2 := K1_13_5_5_2_1_4_2.proof
theorem Asm.K1_13_5_5_2_1_4 : K1_13_5_5_2_1.c4 := K1_13_5_5_2_1_4.of_children Asm.K1_13_5_5_2_1_4_1 Asm.K1_13_5_5_2_1_4_2
theorem Asm.K1_13_5_5_2_1_5 : K1_13_5_5_2_1.c5 := K1_13_5_5_2_1_5.proof
theorem Asm.K1_13_5_5_2_1_6 : K1_13_5_5_2_1.c6 := K1_13_5_5_2_1_6.proof
theorem Asm.K1_13_5_5_2_1 : K1_13_5_5_2.c1 := K1_13_5_5_2_1.of_children Asm.K1_13_5_5_2_1_1 Asm.K1_13_5_5_2_1_2 Asm.K1_13_5_5_2_1_3 Asm.K1_13_5_5_2_1_4 Asm.K1_13_5_5_2_1_5 Asm.K1_13_5_5_2_1_6
theorem Asm.K1_13_5_5_2_2_1 : K1_13_5_5_2_2.c1 := K1_13_5_5_2_2_1.proof
theorem Asm.K1_13_5_5_2_2_2 : K1_13_5_5_2_2.c2 := K1_13_5_5_2_2_2.proof
theorem Asm.K1_13_5_5_2_2 : K1_13_5_5_2.c2 := K1_13_5_5_2_2.of_children Asm.K1_13_5_5_2_2_1 Asm.K1_13_5_5_2_2_2
theorem Asm.K1_13_5_5_2_3_1 : K1_13_5_5_2_3.c1 := K1_13_5_5_2_3_1.proof
theorem Asm.K1_13_5_5_2_3_2 : K1_13_5_5_2_3.c2 := K1_13_5_5_2_3_2.proof
theorem Asm.K1_13_5_5_2_3_3 : K1_13_5_5_2_3.c3 := K1_13_5_5_2_3_3.proof
theorem Asm.K1_13_5_5_2_3 : K1_13_5_5_2.c3 := K1_13_5_5_2_3.of_children Asm.K1_13_5_5_2_3_1 Asm.K1_13_5_5_2_3_2 Asm.K1_13_5_5_2_3_3
theorem Asm.K1_13_5_5_2 : K1_13_5_5.c2 := K1_13_5_5_2.of_children Asm.K1_13_5_5_2_1 Asm.K1_13_5_5_2_2 Asm.K1_13_5_5_2_3
theorem Asm.K1_13_5_5 : K1_13_5.c5 := K1_13_5_5.of_children Asm.K1_13_5_5_1 Asm.K1_13_5_5_2
theorem Asm.K1_13_5 : K1_13.c5 := K1_13_5.of_children Asm.K1_13_5_1 Asm.K1_13_5_2 Asm.K1_13_5_3 Asm.K1_13_5_4 Asm.K1_13_5_5
theorem Asm.K1_13_6_1_1 : K1_13_6_1.c1 := K1_13_6_1_1.proof
theorem Asm.K1_13_6_1_2_1 : K1_13_6_1_2.c1 := K1_13_6_1_2_1.proof
theorem Asm.K1_13_6_1_2_2 : K1_13_6_1_2.c2 := K1_13_6_1_2_2.proof
theorem Asm.K1_13_6_1_2 : K1_13_6_1.c2 := K1_13_6_1_2.of_children Asm.K1_13_6_1_2_1 Asm.K1_13_6_1_2_2
theorem Asm.K1_13_6_1_3_1 : K1_13_6_1_3.c1 := K1_13_6_1_3_1.proof
theorem Asm.K1_13_6_1_3_2 : K1_13_6_1_3.c2 := K1_13_6_1_3_2.proof
theorem Asm.K1_13_6_1_3_3 : K1_13_6_1_3.c3 := K1_13_6_1_3_3.proof
theorem Asm.K1_13_6_1_3 : K1_13_6_1.c3 := K1_13_6_1_3.of_children Asm.K1_13_6_1_3_1 Asm.K1_13_6_1_3_2 Asm.K1_13_6_1_3_3
theorem Asm.K1_13_6_1_4_1_1 : K1_13_6_1_4_1.c1 := K1_13_6_1_4_1_1.proof
theorem Asm.K1_13_6_1_4_1_2 : K1_13_6_1_4_1.c2 := K1_13_6_1_4_1_2.proof
theorem Asm.K1_13_6_1_4_1 : K1_13_6_1_4.c1 := K1_13_6_1_4_1.of_children Asm.K1_13_6_1_4_1_1 Asm.K1_13_6_1_4_1_2
theorem Asm.K1_13_6_1_4_2_1_1_1 : K1_13_6_1_4_2_1_1.c1 := K1_13_6_1_4_2_1_1_1.proof
theorem Asm.K1_13_6_1_4_2_1_1_2 : K1_13_6_1_4_2_1_1.c2 := K1_13_6_1_4_2_1_1_2.proof
theorem Asm.K1_13_6_1_4_2_1_1 : K1_13_6_1_4_2_1.c1 := K1_13_6_1_4_2_1_1.of_children Asm.K1_13_6_1_4_2_1_1_1 Asm.K1_13_6_1_4_2_1_1_2
theorem Asm.K1_13_6_1_4_2_1_2_1 : K1_13_6_1_4_2_1_2.c1 := K1_13_6_1_4_2_1_2_1.proof
theorem Asm.K1_13_6_1_4_2_1_2_2_1 : K1_13_6_1_4_2_1_2_2.c1 := K1_13_6_1_4_2_1_2_2_1.proof
theorem Asm.K1_13_6_1_4_2_1_2_2_2 : K1_13_6_1_4_2_1_2_2.c2 := K1_13_6_1_4_2_1_2_2_2.proof
theorem Asm.K1_13_6_1_4_2_1_2_2 : K1_13_6_1_4_2_1_2.c2 := K1_13_6_1_4_2_1_2_2.of_children Asm.K1_13_6_1_4_2_1_2_2_1 Asm.K1_13_6_1_4_2_1_2_2_2
theorem Asm.K1_13_6_1_4_2_1_2 : K1_13_6_1_4_2_1.c2 := K1_13_6_1_4_2_1_2.of_children Asm.K1_13_6_1_4_2_1_2_1 Asm.K1_13_6_1_4_2_1_2_2
theorem Asm.K1_13_6_1_4_2_1 : K1_13_6_1_4_2.c1 := K1_13_6_1_4_2_1.of_children Asm.K1_13_6_1_4_2_1_1 Asm.K1_13_6_1_4_2_1_2
theorem Asm.K1_13_6_1_4_2_2_1 : K1_13_6_1_4_2_2.c1 := K1_13_6_1_4_2_2_1.proof
theorem Asm.K1_13_6_1_4_2_2_2 : K1_13_6_1_4_2_2.c2 := K1_13_6_1_4_2_2_2.proof
theorem Asm.K1_13_6_1_4_2_2 : K1_13_6_1_4_2.c2 := K1_13_6_1_4_2_2.of_children Asm.K1_13_6_1_4_2_2_1 Asm.K1_13_6_1_4_2_2_2
theorem Asm.K1_13_6_1_4_2 : K1_13_6_1_4.c2 := K1_13_6_1_4_2.of_children Asm.K1_13_6_1_4_2_1 Asm.K1_13_6_1_4_2_2
theorem Asm.K1_13_6_1_4_3_1 : K1_13_6_1_4_3.c1 := K1_13_6_1_4_3_1.proof
theorem Asm.K1_13_6_1_4_3_2 : K1_13_6_1_4_3.c2 := K1_13_6_1_4_3_2.proof
theorem Asm.K1_13_6_1_4_3_3_1_1 : K1_13_6_1_4_3_3_1.c1 := K1_13_6_1_4_3_3_1_1.proof
theorem Asm.K1_13_6_1_4_3_3_1_2 : K1_13_6_1_4_3_3_1.c2 := K1_13_6_1_4_3_3_1_2.proof
theorem Asm.K1_13_6_1_4_3_3_1 : K1_13_6_1_4_3_3.c1 := K1_13_6_1_4_3_3_1.of_children Asm.K1_13_6_1_4_3_3_1_1 Asm.K1_13_6_1_4_3_3_1_2
theorem Asm.K1_13_6_1_4_3_3_2_1 : K1_13_6_1_4_3_3_2.c1 := K1_13_6_1_4_3_3_2_1.proof
theorem Asm.K1_13_6_1_4_3_3_2_2 : K1_13_6_1_4_3_3_2.c2 := K1_13_6_1_4_3_3_2_2.proof
theorem Asm.K1_13_6_1_4_3_3_2 : K1_13_6_1_4_3_3.c2 := K1_13_6_1_4_3_3_2.of_children Asm.K1_13_6_1_4_3_3_2_1 Asm.K1_13_6_1_4_3_3_2_2
theorem Asm.K1_13_6_1_4_3_3_3_1 : K1_13_6_1_4_3_3_3.c1 := K1_13_6_1_4_3_3_3_1.proof
theorem Asm.K1_13_6_1_4_3_3_3_2_1 : K1_13_6_1_4_3_3_3_2.c1 := K1_13_6_1_4_3_3_3_2_1.proof
theorem Asm.K1_13_6_1_4_3_3_3_2_2 : K1_13_6_1_4_3_3_3_2.c2 := K1_13_6_1_4_3_3_3_2_2.proof
theorem Asm.K1_13_6_1_4_3_3_3_2 : K1_13_6_1_4_3_3_3.c2 := K1_13_6_1_4_3_3_3_2.of_children Asm.K1_13_6_1_4_3_3_3_2_1 Asm.K1_13_6_1_4_3_3_3_2_2
theorem Asm.K1_13_6_1_4_3_3_3 : K1_13_6_1_4_3_3.c3 := K1_13_6_1_4_3_3_3.of_children Asm.K1_13_6_1_4_3_3_3_1 Asm.K1_13_6_1_4_3_3_3_2
theorem Asm.K1_13_6_1_4_3_3 : K1_13_6_1_4_3.c3 := K1_13_6_1_4_3_3.of_children Asm.K1_13_6_1_4_3_3_1 Asm.K1_13_6_1_4_3_3_2 Asm.K1_13_6_1_4_3_3_3
theorem Asm.K1_13_6_1_4_3 : K1_13_6_1_4.c3 := K1_13_6_1_4_3.of_children Asm.K1_13_6_1_4_3_1 Asm.K1_13_6_1_4_3_2 Asm.K1_13_6_1_4_3_3
theorem Asm.K1_13_6_1_4 : K1_13_6_1.c4 := K1_13_6_1_4.of_children Asm.K1_13_6_1_4_1 Asm.K1_13_6_1_4_2 Asm.K1_13_6_1_4_3
theorem Asm.K1_13_6_1_5_1 : K1_13_6_1_5.c1 := K1_13_6_1_5_1.proof
theorem Asm.K1_13_6_1_5_2_1 : K1_13_6_1_5_2.c1 := K1_13_6_1_5_2_1.proof
theorem Asm.K1_13_6_1_5_2_2 : K1_13_6_1_5_2.c2 := K1_13_6_1_5_2_2.proof
theorem Asm.K1_13_6_1_5_2 : K1_13_6_1_5.c2 := K1_13_6_1_5_2.of_children Asm.K1_13_6_1_5_2_1 Asm.K1_13_6_1_5_2_2
theorem Asm.K1_13_6_1_5 : K1_13_6_1.c5 := K1_13_6_1_5.of_children Asm.K1_13_6_1_5_1 Asm.K1_13_6_1_5_2
theorem Asm.K1_13_6_1 : K1_13_6.c1 := K1_13_6_1.of_children Asm.K1_13_6_1_1 Asm.K1_13_6_1_2 Asm.K1_13_6_1_3 Asm.K1_13_6_1_4 Asm.K1_13_6_1_5
theorem Asm.K1_13_6_2_1 : K1_13_6_2.c1 := K1_13_6_2_1.proof
theorem Asm.K1_13_6_2_2_1 : K1_13_6_2_2.c1 := K1_13_6_2_2_1.proof
theorem Asm.K1_13_6_2_2_2 : K1_13_6_2_2.c2 := K1_13_6_2_2_2.proof
theorem Asm.K1_13_6_2_2 : K1_13_6_2.c2 := K1_13_6_2_2.of_children Asm.K1_13_6_2_2_1 Asm.K1_13_6_2_2_2
theorem Asm.K1_13_6_2_3_1 : K1_13_6_2_3.c1 := K1_13_6_2_3_1.proof
theorem Asm.K1_13_6_2_3_2_1 : K1_13_6_2_3_2.c1 := K1_13_6_2_3_2_1.proof
theorem Asm.K1_13_6_2_3_2_2 : K1_13_6_2_3_2.c2 := K1_13_6_2_3_2_2.proof
theorem Asm.K1_13_6_2_3_2_3 : K1_13_6_2_3_2.c3 := K1_13_6_2_3_2_3.proof
theorem Asm.K1_13_6_2_3_2_4 : K1_13_6_2_3_2.c4 := K1_13_6_2_3_2_4.proof
theorem Asm.K1_13_6_2_3_2_5 : K1_13_6_2_3_2.c5 := K1_13_6_2_3_2_5.proof
theorem Asm.K1_13_6_2_3_2_6 : K1_13_6_2_3_2.c6 := K1_13_6_2_3_2_6.proof
theorem Asm.K1_13_6_2_3_2 : K1_13_6_2_3.c2 := K1_13_6_2_3_2.of_children Asm.K1_13_6_2_3_2_1 Asm.K1_13_6_2_3_2_2 Asm.K1_13_6_2_3_2_3 Asm.K1_13_6_2_3_2_4 Asm.K1_13_6_2_3_2_5 Asm.K1_13_6_2_3_2_6
theorem Asm.K1_13_6_2_3_3_1 : K1_13_6_2_3_3.c1 := K1_13_6_2_3_3_1.proof
theorem Asm.K1_13_6_2_3_3_2_1 : K1_13_6_2_3_3_2.c1 := K1_13_6_2_3_3_2_1.proof
theorem Asm.K1_13_6_2_3_3_2_2 : K1_13_6_2_3_3_2.c2 := K1_13_6_2_3_3_2_2.proof
theorem Asm.K1_13_6_2_3_3_2 : K1_13_6_2_3_3.c2 := K1_13_6_2_3_3_2.of_children Asm.K1_13_6_2_3_3_2_1 Asm.K1_13_6_2_3_3_2_2
theorem Asm.K1_13_6_2_3_3 : K1_13_6_2_3.c3 := K1_13_6_2_3_3.of_children Asm.K1_13_6_2_3_3_1 Asm.K1_13_6_2_3_3_2
theorem Asm.K1_13_6_2_3 : K1_13_6_2.c3 := K1_13_6_2_3.of_children Asm.K1_13_6_2_3_1 Asm.K1_13_6_2_3_2 Asm.K1_13_6_2_3_3
theorem Asm.K1_13_6_2_4_1_1 : K1_13_6_2_4_1.c1 := K1_13_6_2_4_1_1.proof
theorem Asm.K1_13_6_2_4_1_2 : K1_13_6_2_4_1.c2 := K1_13_6_2_4_1_2.proof
theorem Asm.K1_13_6_2_4_1 : K1_13_6_2_4.c1 := K1_13_6_2_4_1.of_children Asm.K1_13_6_2_4_1_1 Asm.K1_13_6_2_4_1_2
theorem Asm.K1_13_6_2_4_2_1 : K1_13_6_2_4_2.c1 := K1_13_6_2_4_2_1.proof
theorem Asm.K1_13_6_2_4_2_2_1 : K1_13_6_2_4_2_2.c1 := K1_13_6_2_4_2_2_1.proof
theorem Asm.K1_13_6_2_4_2_2_2 : K1_13_6_2_4_2_2.c2 := K1_13_6_2_4_2_2_2.proof
theorem Asm.K1_13_6_2_4_2_2 : K1_13_6_2_4_2.c2 := K1_13_6_2_4_2_2.of_children Asm.K1_13_6_2_4_2_2_1 Asm.K1_13_6_2_4_2_2_2
theorem Asm.K1_13_6_2_4_2 : K1_13_6_2_4.c2 := K1_13_6_2_4_2.of_children Asm.K1_13_6_2_4_2_1 Asm.K1_13_6_2_4_2_2
theorem Asm.K1_13_6_2_4_3_1 : K1_13_6_2_4_3.c1 := K1_13_6_2_4_3_1.proof
theorem Asm.K1_13_6_2_4_3_2 : K1_13_6_2_4_3.c2 := K1_13_6_2_4_3_2.proof
theorem Asm.K1_13_6_2_4_3 : K1_13_6_2_4.c3 := K1_13_6_2_4_3.of_children Asm.K1_13_6_2_4_3_1 Asm.K1_13_6_2_4_3_2
theorem Asm.K1_13_6_2_4_4 : K1_13_6_2_4.c4 := K1_13_6_2_4_4.proof
theorem Asm.K1_13_6_2_4_5 : K1_13_6_2_4.c5 := K1_13_6_2_4_5.proof
theorem Asm.K1_13_6_2_4 : K1_13_6_2.c4 := K1_13_6_2_4.of_children Asm.K1_13_6_2_4_1 Asm.K1_13_6_2_4_2 Asm.K1_13_6_2_4_3 Asm.K1_13_6_2_4_4 Asm.K1_13_6_2_4_5
theorem Asm.K1_13_6_2 : K1_13_6.c2 := K1_13_6_2.of_children Asm.K1_13_6_2_1 Asm.K1_13_6_2_2 Asm.K1_13_6_2_3 Asm.K1_13_6_2_4
theorem Asm.K1_13_6_3_1_1 : K1_13_6_3_1.c1 := K1_13_6_3_1_1.proof
theorem Asm.K1_13_6_3_1_2 : K1_13_6_3_1.c2 := K1_13_6_3_1_2.proof
theorem Asm.K1_13_6_3_1 : K1_13_6_3.c1 := K1_13_6_3_1.of_children Asm.K1_13_6_3_1_1 Asm.K1_13_6_3_1_2
theorem Asm.K1_13_6_3_2_1 : K1_13_6_3_2.c1 := K1_13_6_3_2_1.proof
theorem Asm.K1_13_6_3_2_2 : K1_13_6_3_2.c2 := K1_13_6_3_2_2.proof
theorem Asm.K1_13_6_3_2_3 : K1_13_6_3_2.c3 := K1_13_6_3_2_3.proof
theorem Asm.K1_13_6_3_2 : K1_13_6_3.c2 := K1_13_6_3_2.of_children Asm.K1_13_6_3_2_1 Asm.K1_13_6_3_2_2 Asm.K1_13_6_3_2_3
theorem Asm.K1_13_6_3_3_1 : K1_13_6_3_3.c1 := K1_13_6_3_3_1.proof
theorem Asm.K1_13_6_3_3_2 : K1_13_6_3_3.c2 := K1_13_6_3_3_2.proof
theorem Asm.K1_13_6_3_3 : K1_13_6_3.c3 := K1_13_6_3_3.of_children Asm.K1_13_6_3_3_1 Asm.K1_13_6_3_3_2
theorem Asm.K1_13_6_3_4_1 : K1_13_6_3_4.c1 := K1_13_6_3_4_1.proof
theorem Asm.K1_13_6_3_4_2 : K1_13_6_3_4.c2 := K1_13_6_3_4_2.proof
theorem Asm.K1_13_6_3_4_3 : K1_13_6_3_4.c3 := K1_13_6_3_4_3.proof
theorem Asm.K1_13_6_3_4 : K1_13_6_3.c4 := K1_13_6_3_4.of_children Asm.K1_13_6_3_4_1 Asm.K1_13_6_3_4_2 Asm.K1_13_6_3_4_3
theorem Asm.K1_13_6_3_5_1_1 : K1_13_6_3_5_1.c1 := K1_13_6_3_5_1_1.proof
theorem Asm.K1_13_6_3_5_1_2 : K1_13_6_3_5_1.c2 := K1_13_6_3_5_1_2.proof
theorem Asm.K1_13_6_3_5_1 : K1_13_6_3_5.c1 := K1_13_6_3_5_1.of_children Asm.K1_13_6_3_5_1_1 Asm.K1_13_6_3_5_1_2
theorem Asm.K1_13_6_3_5_2 : K1_13_6_3_5.c2 := K1_13_6_3_5_2.proof
theorem Asm.K1_13_6_3_5_3_1 : K1_13_6_3_5_3.c1 := K1_13_6_3_5_3_1.proof
theorem Asm.K1_13_6_3_5_3_2_1 : K1_13_6_3_5_3_2.c1 := K1_13_6_3_5_3_2_1.proof
theorem Asm.K1_13_6_3_5_3_2_2 : K1_13_6_3_5_3_2.c2 := K1_13_6_3_5_3_2_2.proof
theorem Asm.K1_13_6_3_5_3_2 : K1_13_6_3_5_3.c2 := K1_13_6_3_5_3_2.of_children Asm.K1_13_6_3_5_3_2_1 Asm.K1_13_6_3_5_3_2_2
theorem Asm.K1_13_6_3_5_3_3_1 : K1_13_6_3_5_3_3.c1 := K1_13_6_3_5_3_3_1.proof
theorem Asm.K1_13_6_3_5_3_3_2 : K1_13_6_3_5_3_3.c2 := K1_13_6_3_5_3_3_2.proof
theorem Asm.K1_13_6_3_5_3_3_3 : K1_13_6_3_5_3_3.c3 := K1_13_6_3_5_3_3_3.proof
theorem Asm.K1_13_6_3_5_3_3_4 : K1_13_6_3_5_3_3.c4 := K1_13_6_3_5_3_3_4.proof
theorem Asm.K1_13_6_3_5_3_3 : K1_13_6_3_5_3.c3 := K1_13_6_3_5_3_3.of_children Asm.K1_13_6_3_5_3_3_1 Asm.K1_13_6_3_5_3_3_2 Asm.K1_13_6_3_5_3_3_3 Asm.K1_13_6_3_5_3_3_4
theorem Asm.K1_13_6_3_5_3_4 : K1_13_6_3_5_3.c4 := K1_13_6_3_5_3_4.proof
theorem Asm.K1_13_6_3_5_3_5 : K1_13_6_3_5_3.c5 := K1_13_6_3_5_3_5.proof
theorem Asm.K1_13_6_3_5_3_6 : K1_13_6_3_5_3.c6 := K1_13_6_3_5_3_6.proof
theorem Asm.K1_13_6_3_5_3 : K1_13_6_3_5.c3 := K1_13_6_3_5_3.of_children Asm.K1_13_6_3_5_3_1 Asm.K1_13_6_3_5_3_2 Asm.K1_13_6_3_5_3_3 Asm.K1_13_6_3_5_3_4 Asm.K1_13_6_3_5_3_5 Asm.K1_13_6_3_5_3_6
theorem Asm.K1_13_6_3_5_4 : K1_13_6_3_5.c4 := K1_13_6_3_5_4.proof
theorem Asm.K1_13_6_3_5_5_1 : K1_13_6_3_5_5.c1 := K1_13_6_3_5_5_1.proof
theorem Asm.K1_13_6_3_5_5_2 : K1_13_6_3_5_5.c2 := K1_13_6_3_5_5_2.proof
theorem Asm.K1_13_6_3_5_5_3 : K1_13_6_3_5_5.c3 := K1_13_6_3_5_5_3.proof
theorem Asm.K1_13_6_3_5_5_4 : K1_13_6_3_5_5.c4 := K1_13_6_3_5_5_4.proof
theorem Asm.K1_13_6_3_5_5 : K1_13_6_3_5.c5 := K1_13_6_3_5_5.of_children Asm.K1_13_6_3_5_5_1 Asm.K1_13_6_3_5_5_2 Asm.K1_13_6_3_5_5_3 Asm.K1_13_6_3_5_5_4
theorem Asm.K1_13_6_3_5 : K1_13_6_3.c5 := K1_13_6_3_5.of_children Asm.K1_13_6_3_5_1 Asm.K1_13_6_3_5_2 Asm.K1_13_6_3_5_3 Asm.K1_13_6_3_5_4 Asm.K1_13_6_3_5_5
theorem Asm.K1_13_6_3_6 : K1_13_6_3.c6 := K1_13_6_3_6.proof
theorem Asm.K1_13_6_3 : K1_13_6.c3 := K1_13_6_3.of_children Asm.K1_13_6_3_1 Asm.K1_13_6_3_2 Asm.K1_13_6_3_3 Asm.K1_13_6_3_4 Asm.K1_13_6_3_5 Asm.K1_13_6_3_6
theorem Asm.K1_13_6 : K1_13.c6 := K1_13_6.of_children Asm.K1_13_6_1 Asm.K1_13_6_2 Asm.K1_13_6_3
theorem Asm.K1_13_7_1_1_1_1_1 : K1_13_7_1_1_1_1.c1 := K1_13_7_1_1_1_1_1.proof
theorem Asm.K1_13_7_1_1_1_1_2 : K1_13_7_1_1_1_1.c2 := K1_13_7_1_1_1_1_2.proof
theorem Asm.K1_13_7_1_1_1_1 : K1_13_7_1_1_1.c1 := K1_13_7_1_1_1_1.of_children Asm.K1_13_7_1_1_1_1_1 Asm.K1_13_7_1_1_1_1_2
theorem Asm.K1_13_7_1_1_1_2_1 : K1_13_7_1_1_1_2.c1 := K1_13_7_1_1_1_2_1.proof
theorem Asm.K1_13_7_1_1_1_2_2 : K1_13_7_1_1_1_2.c2 := K1_13_7_1_1_1_2_2.proof
theorem Asm.K1_13_7_1_1_1_2 : K1_13_7_1_1_1.c2 := K1_13_7_1_1_1_2.of_children Asm.K1_13_7_1_1_1_2_1 Asm.K1_13_7_1_1_1_2_2
theorem Asm.K1_13_7_1_1_1 : K1_13_7_1_1.c1 := K1_13_7_1_1_1.of_children Asm.K1_13_7_1_1_1_1 Asm.K1_13_7_1_1_1_2
theorem Asm.K1_13_7_1_1_2 : K1_13_7_1_1.c2 := K1_13_7_1_1_2.proof
theorem Asm.K1_13_7_1_1 : K1_13_7_1.c1 := K1_13_7_1_1.of_children Asm.K1_13_7_1_1_1 Asm.K1_13_7_1_1_2
theorem Asm.K1_13_7_1_2_1 : K1_13_7_1_2.c1 := K1_13_7_1_2_1.proof
theorem Asm.K1_13_7_1_2_2_1_1 : K1_13_7_1_2_2_1.c1 := K1_13_7_1_2_2_1_1.proof
theorem Asm.K1_13_7_1_2_2_1_2 : K1_13_7_1_2_2_1.c2 := K1_13_7_1_2_2_1_2.proof
theorem Asm.K1_13_7_1_2_2_1 : K1_13_7_1_2_2.c1 := K1_13_7_1_2_2_1.of_children Asm.K1_13_7_1_2_2_1_1 Asm.K1_13_7_1_2_2_1_2
theorem Asm.K1_13_7_1_2_2_2_1 : K1_13_7_1_2_2_2.c1 := K1_13_7_1_2_2_2_1.proof
theorem Asm.K1_13_7_1_2_2_2_2 : K1_13_7_1_2_2_2.c2 := K1_13_7_1_2_2_2_2.proof
theorem Asm.K1_13_7_1_2_2_2 : K1_13_7_1_2_2.c2 := K1_13_7_1_2_2_2.of_children Asm.K1_13_7_1_2_2_2_1 Asm.K1_13_7_1_2_2_2_2
theorem Asm.K1_13_7_1_2_2 : K1_13_7_1_2.c2 := K1_13_7_1_2_2.of_children Asm.K1_13_7_1_2_2_1 Asm.K1_13_7_1_2_2_2
theorem Asm.K1_13_7_1_2 : K1_13_7_1.c2 := K1_13_7_1_2.of_children Asm.K1_13_7_1_2_1 Asm.K1_13_7_1_2_2
theorem Asm.K1_13_7_1 : K1_13_7.c1 := K1_13_7_1.of_children Asm.K1_13_7_1_1 Asm.K1_13_7_1_2
theorem Asm.K1_13_7_2_1_1 : K1_13_7_2_1.c1 := K1_13_7_2_1_1.proof
theorem Asm.K1_13_7_2_1_2 : K1_13_7_2_1.c2 := K1_13_7_2_1_2.proof
theorem Asm.K1_13_7_2_1 : K1_13_7_2.c1 := K1_13_7_2_1.of_children Asm.K1_13_7_2_1_1 Asm.K1_13_7_2_1_2
theorem Asm.K1_13_7_2_2 : K1_13_7_2.c2 := K1_13_7_2_2.proof
theorem Asm.K1_13_7_2_3_1_1 : K1_13_7_2_3_1.c1 := K1_13_7_2_3_1_1.proof
theorem Asm.K1_13_7_2_3_1_2_1 : K1_13_7_2_3_1_2.c1 := K1_13_7_2_3_1_2_1.proof
theorem Asm.K1_13_7_2_3_1_2_2 : K1_13_7_2_3_1_2.c2 := K1_13_7_2_3_1_2_2.proof
theorem Asm.K1_13_7_2_3_1_2 : K1_13_7_2_3_1.c2 := K1_13_7_2_3_1_2.of_children Asm.K1_13_7_2_3_1_2_1 Asm.K1_13_7_2_3_1_2_2
theorem Asm.K1_13_7_2_3_1_3 : K1_13_7_2_3_1.c3 := K1_13_7_2_3_1_3.proof
theorem Asm.K1_13_7_2_3_1 : K1_13_7_2_3.c1 := K1_13_7_2_3_1.of_children Asm.K1_13_7_2_3_1_1 Asm.K1_13_7_2_3_1_2 Asm.K1_13_7_2_3_1_3
theorem Asm.K1_13_7_2_3_2 : K1_13_7_2_3.c2 := K1_13_7_2_3_2.of_children Asm.K1_13_6_1_5_2_1 Asm.K1_13_6_1_5_2_2
theorem Asm.K1_13_7_2_3 : K1_13_7_2.c3 := K1_13_7_2_3.of_children Asm.K1_13_7_2_3_1 Asm.K1_13_7_2_3_2
theorem Asm.K1_13_7_2_4_1 : K1_13_7_2_4.c1 := K1_13_7_2_4_1.proof
theorem Asm.K1_13_7_2_4_2 : K1_13_7_2_4.c2 := K1_13_7_2_4_2.proof
theorem Asm.K1_13_7_2_4_3 : K1_13_7_2_4.c3 := K1_13_7_2_4_3.proof
theorem Asm.K1_13_7_2_4 : K1_13_7_2.c4 := K1_13_7_2_4.of_children Asm.K1_13_7_2_4_1 Asm.K1_13_7_2_4_2 Asm.K1_13_7_2_4_3
theorem Asm.K1_13_7_2_5_1 : K1_13_7_2_5.c1 := K1_13_7_2_5_1.proof
theorem Asm.K1_13_7_2_5_2_1 : K1_13_7_2_5_2.c1 := K1_13_7_2_5_2_1.proof
theorem Asm.K1_13_7_2_5_2_2 : K1_13_7_2_5_2.c2 := K1_13_7_2_5_2_2.proof
theorem Asm.K1_13_7_2_5_2 : K1_13_7_2_5.c2 := K1_13_7_2_5_2.of_children Asm.K1_13_7_2_5_2_1 Asm.K1_13_7_2_5_2_2
theorem Asm.K1_13_7_2_5_3 : K1_13_7_2_5.c3 := K1_13_7_2_5_3.of_children Asm.K1_13_6_3_5_1 Asm.K1_13_6_3_5_2 Asm.K1_13_6_3_5_3 Asm.K1_13_6_3_5_4 Asm.K1_13_6_3_5_5
theorem Asm.K1_13_7_2_5_4_1_1 : K1_13_7_2_5_4_1.c1 := K1_13_7_2_5_4_1_1.proof
theorem Asm.K1_13_7_2_5_4_1_2 : K1_13_7_2_5_4_1.c2 := K1_13_7_2_5_4_1_2.proof
theorem Asm.K1_13_7_2_5_4_1 : K1_13_7_2_5_4.c1 := K1_13_7_2_5_4_1.of_children Asm.K1_13_7_2_5_4_1_1 Asm.K1_13_7_2_5_4_1_2
theorem Asm.K1_13_7_2_5_4_2 : K1_13_7_2_5_4.c2 := K1_13_7_2_5_4_2.proof
theorem Asm.K1_13_7_2_5_4 : K1_13_7_2_5.c4 := K1_13_7_2_5_4.of_children Asm.K1_13_7_2_5_4_1 Asm.K1_13_7_2_5_4_2
theorem Asm.K1_13_7_2_5 : K1_13_7_2.c5 := K1_13_7_2_5.of_children Asm.K1_13_7_2_5_1 Asm.K1_13_7_2_5_2 Asm.K1_13_7_2_5_3 Asm.K1_13_7_2_5_4
theorem Asm.K1_13_7_2 : K1_13_7.c2 := K1_13_7_2.of_children Asm.K1_13_7_2_1 Asm.K1_13_7_2_2 Asm.K1_13_7_2_3 Asm.K1_13_7_2_4 Asm.K1_13_7_2_5
theorem Asm.K1_13_7_3_1 : K1_13_7_3.c1 := K1_13_7_3_1.proof
theorem Asm.K1_13_7_3_2 : K1_13_7_3.c2 := K1_13_7_3_2.proof
theorem Asm.K1_13_7_3 : K1_13_7.c3 := K1_13_7_3.of_children Asm.K1_13_7_3_1 Asm.K1_13_7_3_2
theorem Asm.K1_13_7_4_1 : K1_13_7_4.c1 := K1_13_7_4_1.proof
theorem Asm.K1_13_7_4_2_1 : K1_13_7_4_2.c1 := K1_13_7_4_2_1.proof
theorem Asm.K1_13_7_4_2_2 : K1_13_7_4_2.c2 := K1_13_7_4_2_2.proof
theorem Asm.K1_13_7_4_2 : K1_13_7_4.c2 := K1_13_7_4_2.of_children Asm.K1_13_7_4_2_1 Asm.K1_13_7_4_2_2
theorem Asm.K1_13_7_4 : K1_13_7.c4 := K1_13_7_4.of_children Asm.K1_13_7_4_1 Asm.K1_13_7_4_2
theorem Asm.K1_13_7_5_1 : K1_13_7_5.c1 := K1_13_7_5_1.proof
theorem Asm.K1_13_7_5_2 : K1_13_7_5.c2 := K1_13_7_5_2.proof
theorem Asm.K1_13_7_5_3_1_1 : K1_13_7_5_3_1.c1 := K1_13_7_5_3_1_1.proof
theorem Asm.K1_13_7_5_3_1_2 : K1_13_7_5_3_1.c2 := K1_13_7_5_3_1_2.proof
theorem Asm.K1_13_7_5_3_1 : K1_13_7_5_3.c1 := K1_13_7_5_3_1.of_children Asm.K1_13_7_5_3_1_1 Asm.K1_13_7_5_3_1_2
theorem Asm.K1_13_7_5_3_2 : K1_13_7_5_3.c2 := K1_13_7_5_3_2.proof
theorem Asm.K1_13_7_5_3_3_1 : K1_13_7_5_3_3.c1 := K1_13_7_5_3_3_1.proof
theorem Asm.K1_13_7_5_3_3_2_1 : K1_13_7_5_3_3_2.c1 := K1_13_7_5_3_3_2_1.proof
theorem Asm.K1_13_7_5_3_3_2_2 : K1_13_7_5_3_3_2.c2 := K1_13_7_5_3_3_2_2.proof
theorem Asm.K1_13_7_5_3_3_2 : K1_13_7_5_3_3.c2 := K1_13_7_5_3_3_2.of_children Asm.K1_13_7_5_3_3_2_1 Asm.K1_13_7_5_3_3_2_2
theorem Asm.K1_13_7_5_3_3_3_1 : K1_13_7_5_3_3_3.c1 := K1_13_7_5_3_3_3_1.proof
theorem Asm.K1_13_7_5_3_3_3_2 : K1_13_7_5_3_3_3.c2 := K1_13_7_5_3_3_3_2.proof
theorem Asm.K1_13_7_5_3_3_3 : K1_13_7_5_3_3.c3 := K1_13_7_5_3_3_3.of_children Asm.K1_13_7_5_3_3_3_1 Asm.K1_13_7_5_3_3_3_2
theorem Asm.K1_13_7_5_3_3_4 : K1_13_7_5_3_3.c4 := K1_13_7_5_3_3_4.proof
theorem Asm.K1_13_7_5_3_3 : K1_13_7_5_3.c3 := K1_13_7_5_3_3.of_children Asm.K1_13_7_5_3_3_1 Asm.K1_13_7_5_3_3_2 Asm.K1_13_7_5_3_3_3 Asm.K1_13_7_5_3_3_4
theorem Asm.K1_13_7_5_3_4 : K1_13_7_5_3.c4 := K1_13_7_5_3_4.proof
theorem Asm.K1_13_7_5_3 : K1_13_7_5.c3 := K1_13_7_5_3.of_children Asm.K1_13_7_5_3_1 Asm.K1_13_7_5_3_2 Asm.K1_13_7_5_3_3 Asm.K1_13_7_5_3_4
theorem Asm.K1_13_7_5 : K1_13_7.c5 := K1_13_7_5.of_children Asm.K1_13_7_5_1 Asm.K1_13_7_5_2 Asm.K1_13_7_5_3
theorem Asm.K1_13_7_6_1 : K1_13_7_6.c1 := K1_13_7_6_1.proof
theorem Asm.K1_13_7_6_2_1 : K1_13_7_6_2.c1 := K1_13_7_6_2_1.proof
theorem Asm.K1_13_7_6_2_2 : K1_13_7_6_2.c2 := K1_13_7_6_2_2.proof
theorem Asm.K1_13_7_6_2 : K1_13_7_6.c2 := K1_13_7_6_2.of_children Asm.K1_13_7_6_2_1 Asm.K1_13_7_6_2_2
theorem Asm.K1_13_7_6 : K1_13_7.c6 := K1_13_7_6.of_children Asm.K1_13_7_6_1 Asm.K1_13_7_6_2
theorem Asm.K1_13_7 : K1_13.c7 := K1_13_7.of_children Asm.K1_13_7_1 Asm.K1_13_7_2 Asm.K1_13_7_3 Asm.K1_13_7_4 Asm.K1_13_7_5 Asm.K1_13_7_6
theorem Asm.K1_13_8_1 : K1_13_8.c1 := K1_13_8_1.proof
theorem Asm.K1_13_8_2 : K1_13_8.c2 := K1_13_8_2.proof
theorem Asm.K1_13_8_3 : K1_13_8.c3 := K1_13_8_3.proof
theorem Asm.K1_13_8_4 : K1_13_8.c4 := K1_13_8_4.proof
theorem Asm.K1_13_8 : K1_13.c8 := K1_13_8.of_children Asm.K1_13_8_1 Asm.K1_13_8_2 Asm.K1_13_8_3 Asm.K1_13_8_4
theorem Asm.K1_13 : K1.c13 := K1_13.of_children Asm.K1_13_1 Asm.K1_13_2 Asm.K1_13_3 Asm.K1_13_4 Asm.K1_13_5 Asm.K1_13_6 Asm.K1_13_7 Asm.K1_13_8
theorem Asm.K1_14_1_1 : K1_14_1.c1 := K1_14_1_1.proof
theorem Asm.K1_14_1_2 : K1_14_1.c2 := K1_14_1_2.proof
theorem Asm.K1_14_1_3_1 : K1_14_1_3.c1 := K1_14_1_3_1.proof
theorem Asm.K1_14_1_3_2 : K1_14_1_3.c2 := K1_14_1_3_2.proof
theorem Asm.K1_14_1_3 : K1_14_1.c3 := K1_14_1_3.of_children Asm.K1_14_1_3_1 Asm.K1_14_1_3_2
theorem Asm.K1_14_1_4 : K1_14_1.c4 := K1_14_1_4.proof
theorem Asm.K1_14_1_5 : K1_14_1.c5 := K1_14_1_5.proof
theorem Asm.K1_14_1_6 : K1_14_1.c6 := K1_14_1_6.proof
theorem Asm.K1_14_1_7_1 : K1_14_1_7.c1 := K1_14_1_7_1.proof
theorem Asm.K1_14_1_7_2_1 : K1_14_1_7_2.c1 := K1_14_1_7_2_1.proof
theorem Asm.K1_14_1_7_2_2 : K1_14_1_7_2.c2 := K1_14_1_7_2_2.proof
theorem Asm.K1_14_1_7_2 : K1_14_1_7.c2 := K1_14_1_7_2.of_children Asm.K1_14_1_7_2_1 Asm.K1_14_1_7_2_2
theorem Asm.K1_14_1_7_3 : K1_14_1_7.c3 := K1_14_1_7_3.proof
theorem Asm.K1_14_1_7_4 : K1_14_1_7.c4 := K1_14_1_7_4.proof
theorem Asm.K1_14_1_7 : K1_14_1.c7 := K1_14_1_7.of_children Asm.K1_14_1_7_1 Asm.K1_14_1_7_2 Asm.K1_14_1_7_3 Asm.K1_14_1_7_4
theorem Asm.K1_14_1_8 : K1_14_1.c8 := K1_14_1_8.proof
theorem Asm.K1_14_1 : K1_14.c1 := K1_14_1.of_children Asm.K1_14_1_1 Asm.K1_14_1_2 Asm.K1_14_1_3 Asm.K1_14_1_4 Asm.K1_14_1_5 Asm.K1_14_1_6 Asm.K1_14_1_7 Asm.K1_14_1_8
theorem Asm.K1_14_2_1_1 : K1_14_2_1.c1 := K1_14_2_1_1.proof
theorem Asm.K1_14_2_1_2 : K1_14_2_1.c2 := K1_14_2_1_2.proof
theorem Asm.K1_14_2_1 : K1_14_2.c1 := K1_14_2_1.of_children Asm.K1_14_2_1_1 Asm.K1_14_2_1_2
theorem Asm.K1_14_2_2_2_1 : K1_14_2_2_2.c1 := K1_14_2_2_2_1.proof
theorem Asm.K1_14_2_2_2_3 : K1_14_2_2_2.c3 := K1_14_2_2_2_3.proof
theorem Asm.K1_14_2_2_2_4_1 : K1_14_2_2_2_4.c1 := K1_14_2_2_2_4_1.proof
theorem Asm.K1_14_2_2_2_4_2 : K1_14_2_2_2_4.c2 := K1_14_2_2_2_4_2.proof
theorem Asm.K1_14_2_2_2_4_3 : K1_14_2_2_2_4.c3 := K1_14_2_2_2_4_3.proof
theorem Asm.K1_14_2_2_2_4 : K1_14_2_2_2.c4 := K1_14_2_2_2_4.of_children Asm.K1_14_2_2_2_4_1 Asm.K1_14_2_2_2_4_2 Asm.K1_14_2_2_2_4_3
theorem Asm.K1_14_2_2_2_6_1 : K1_14_2_2_2_6.c1 := K1_14_2_2_2_6_1.proof
theorem Asm.K1_14_2_2_2_6_2 : K1_14_2_2_2_6.c2 := K1_14_2_2_2_6_2.proof
theorem Asm.K1_14_2_2_2_6 : K1_14_2_2_2.c6 := K1_14_2_2_2_6.of_children Asm.K1_14_2_2_2_6_1 Asm.K1_14_2_2_2_6_2
theorem Asm.K1_14_2_2_2R : K1_14_2_2.c2 := K1_14_2_2_2R.of_children Asm.K1_14_2_2_2_1 Asm.K1_14_2_2_2_3 Asm.K1_14_2_2_2_4 Asm.K1_14_2_2_2_6
theorem Asm.K1_14_2_2_2 : K1_14_2_2.c2 := Asm.K1_14_2_2_2R
theorem Asm.K1_14_2_2_3_1 : K1_14_2_2_3.c1 := K1_14_2_2_3_1.proof
theorem Asm.K1_14_2_2_3_2 : K1_14_2_2_3.c2 := K1_14_2_2_3_2.proof
theorem Asm.K1_14_2_2_3 : K1_14_2_2.c3 := K1_14_2_2_3.of_children Asm.K1_14_2_2_3_1 Asm.K1_14_2_2_3_2
theorem Asm.K1_14_2_2_4_1 : K1_14_2_2_4.c1 := K1_14_2_2_4_1.proof
theorem Asm.K1_14_2_2_4_3_1 : K1_14_2_2_4_3.c1 := K1_14_2_2_4_3_1.proof
theorem Asm.K1_14_2_2_4_3_2 : K1_14_2_2_4_3.c2 := K1_14_2_2_4_3_2.proof
theorem Asm.K1_14_2_2_4_3 : K1_14_2_2_4.c3 := K1_14_2_2_4_3.of_children Asm.K1_14_2_2_4_3_1 Asm.K1_14_2_2_4_3_2
theorem Asm.K1_14_2_2_4_4 : K1_14_2_2_4.c4 := K1_14_2_2_4_4.proof
theorem Asm.K1_14_2_2_4_5_1 : K1_14_2_2_4_5.c1 := K1_14_2_2_4_5_1.proof
theorem Asm.K1_14_2_2_4_5_2 : K1_14_2_2_4_5.c2 := K1_14_2_2_4_5_2.proof
theorem Asm.K1_14_2_2_4_5_3 : K1_14_2_2_4_5.c3 := K1_14_2_2_4_5_3.proof
theorem Asm.K1_14_2_2_4_5_4 : K1_14_2_2_4_5.c4 := K1_14_2_2_4_5_4.proof
theorem Asm.K1_14_2_2_4_5_5 : K1_14_2_2_4_5.c5 := K1_14_2_2_4_5_5.proof
theorem Asm.K1_14_2_2_4_5 : K1_14_2_2_4.c5 := K1_14_2_2_4_5.of_children Asm.K1_14_2_2_4_5_1 Asm.K1_14_2_2_4_5_2 Asm.K1_14_2_2_4_5_3 Asm.K1_14_2_2_4_5_4 Asm.K1_14_2_2_4_5_5
theorem Asm.K1_14_2_2_5_1 : K1_14_2_2_5.c1 := K1_14_2_2_5_1.proof
theorem Asm.K1_14_2_2_5_2 : K1_14_2_2_5.c2 := K1_14_2_2_5_2.proof
theorem Asm.K1_14_2_2_5 : K1_14_2_2.c5 := K1_14_2_2_5.of_children Asm.K1_14_2_2_5_1 Asm.K1_14_2_2_5_2
theorem Asm.K1_14_2_2_7_1 : K1_14_2_2_7.c1 := K1_14_2_2_7_1.proof
theorem Asm.K1_14_2_2_7_2_1 : K1_14_2_2_7_2.c1 := K1_14_2_2_7_2_1.proof
theorem Asm.K1_14_2_2_7_2_2_1 : K1_14_2_2_7_2_2.c1 := K1_14_2_2_7_2_2_1.proof
theorem Asm.K1_14_2_2_7_2_2_2 : K1_14_2_2_7_2_2.c2 := K1_14_2_2_7_2_2_2.proof
theorem Asm.K1_14_2_2_7_2_2_3 : K1_14_2_2_7_2_2.c3 := K1_14_2_2_7_2_2_3.proof
theorem Asm.K1_14_2_2_7_2_2 : K1_14_2_2_7_2.c2 := K1_14_2_2_7_2_2.of_children Asm.K1_14_2_2_7_2_2_1 Asm.K1_14_2_2_7_2_2_2 Asm.K1_14_2_2_7_2_2_3
theorem Asm.K1_14_2_2_7_2_3 : K1_14_2_2_7_2.c3 := K1_14_2_2_7_2_3.proof
theorem Asm.K1_14_2_2_7_2_4 : K1_14_2_2_7_2.c4 := K1_14_2_2_7_2_4.proof
theorem Asm.K1_14_2_2_7_2_5 : K1_14_2_2_7_2.c5 := K1_14_2_2_7_2_5.proof
theorem Asm.K1_14_2_2_7_2 : K1_14_2_2_7.c2 := K1_14_2_2_7_2.of_children Asm.K1_14_2_2_7_2_1 Asm.K1_14_2_2_7_2_2 Asm.K1_14_2_2_7_2_3 Asm.K1_14_2_2_7_2_4 Asm.K1_14_2_2_7_2_5
theorem Asm.K1_14_2_2_7_3_1 : K1_14_2_2_7_3.c1 := K1_14_2_2_7_3_1.proof
theorem Asm.K1_14_2_2_7_3_2 : K1_14_2_2_7_3.c2 := K1_14_2_2_7_3_2.proof
theorem Asm.K1_14_2_2_7_3_3_1_1 : K1_14_2_2_7_3_3_1.c1 := K1_14_2_2_7_3_3_1_1.proof
theorem Asm.K1_14_2_2_7_3_3_1_2 : K1_14_2_2_7_3_3_1.c2 := K1_14_2_2_7_3_3_1_2.proof
theorem Asm.K1_14_2_2_7_3_3_1_3 : K1_14_2_2_7_3_3_1.c3 := K1_14_2_2_7_3_3_1_3.proof
theorem Asm.K1_14_2_2_7_3_3_1_4 : K1_14_2_2_7_3_3_1.c4 := K1_14_2_2_7_3_3_1_4.proof
theorem Asm.K1_14_2_2_7_3_3_1 : K1_14_2_2_7_3_3.c1 := K1_14_2_2_7_3_3_1.of_children Asm.K1_14_2_2_7_3_3_1_1 Asm.K1_14_2_2_7_3_3_1_2 Asm.K1_14_2_2_7_3_3_1_3 Asm.K1_14_2_2_7_3_3_1_4
theorem Asm.K1_14_2_2_7_3_3_2 : K1_14_2_2_7_3_3.c2 := K1_14_2_2_7_3_3_2.proof
theorem Asm.K1_14_2_2_7_3_3 : K1_14_2_2_7_3.c3 := K1_14_2_2_7_3_3.of_children Asm.K1_14_2_2_7_3_3_1 Asm.K1_14_2_2_7_3_3_2
theorem Asm.K1_14_2_2_7_3 : K1_14_2_2_7.c3 := K1_14_2_2_7_3.of_children Asm.K1_14_2_2_7_3_1 Asm.K1_14_2_2_7_3_2 Asm.K1_14_2_2_7_3_3
theorem Asm.K1_14_2_2_7_4_1 : K1_14_2_2_7_4.c1 := K1_14_2_2_7_4_1.proof
theorem Asm.K1_14_2_2_7_4_2 : K1_14_2_2_7_4.c2 := K1_14_2_2_7_4_2.proof
theorem Asm.K1_14_2_2_7_4_3 : K1_14_2_2_7_4.c3 := K1_14_2_2_7_4_3.proof
theorem Asm.K1_14_2_2_7_4_4_1 : K1_14_2_2_7_4_4.c1 := K1_14_2_2_7_4_4_1.proof
theorem Asm.K1_14_2_2_7_4_4_2 : K1_14_2_2_7_4_4.c2 := K1_14_2_2_7_4_4_2.proof
theorem Asm.K1_14_2_2_7_4_4_3 : K1_14_2_2_7_4_4.c3 := K1_14_2_2_7_4_4_3.proof
theorem Asm.K1_14_2_2_7_4_4_4 : K1_14_2_2_7_4_4.c4 := K1_14_2_2_7_4_4_4.proof
theorem Asm.K1_14_2_2_7_4_4_5 : K1_14_2_2_7_4_4.c5 := K1_14_2_2_7_4_4_5.proof
theorem Asm.K1_14_2_2_7_4_4_6 : K1_14_2_2_7_4_4.c6 := K1_14_2_2_7_4_4_6.proof
theorem Asm.K1_14_2_2_7_4_4_7_1 : K1_14_2_2_7_4_4_7.c1 := K1_14_2_2_7_4_4_7_1.proof
theorem Asm.K1_14_2_2_7_4_4_7_2 : K1_14_2_2_7_4_4_7.c2 := K1_14_2_2_7_4_4_7_2.proof
theorem Asm.K1_14_2_2_7_4_4_7 : K1_14_2_2_7_4_4.c7 := K1_14_2_2_7_4_4_7.of_children Asm.K1_14_2_2_7_4_4_7_1 Asm.K1_14_2_2_7_4_4_7_2
theorem Asm.K1_14_2_2_7_4_4_8 : K1_14_2_2_7_4_4.c8 := K1_14_2_2_7_4_4_8.proof
theorem Asm.K1_14_2_2_7_4_4 : K1_14_2_2_7_4.c4 := K1_14_2_2_7_4_4.of_children Asm.K1_14_2_2_7_4_4_1 Asm.K1_14_2_2_7_4_4_2 Asm.K1_14_2_2_7_4_4_3 Asm.K1_14_2_2_7_4_4_4 Asm.K1_14_2_2_7_4_4_5 Asm.K1_14_2_2_7_4_4_6 Asm.K1_14_2_2_7_4_4_7 Asm.K1_14_2_2_7_4_4_8
theorem Asm.K1_14_2_2_7_4 : K1_14_2_2_7.c4 := K1_14_2_2_7_4.of_children Asm.K1_14_2_2_7_4_1 Asm.K1_14_2_2_7_4_2 Asm.K1_14_2_2_7_4_3 Asm.K1_14_2_2_7_4_4
theorem Asm.K1_14_2_2_7 : K1_14_2_2.c7 := K1_14_2_2_7.of_children Asm.K1_14_2_2_7_1 Asm.K1_14_2_2_7_2 Asm.K1_14_2_2_7_3 Asm.K1_14_2_2_7_4
theorem Asm.K1_14_2_2R : K1_14_2.c2 := K1_14_2_2R.of_children Asm.K1_14_2_2_2 Asm.K1_14_2_2_3 Asm.K1_14_2_2_4_1 Asm.K1_14_2_2_4_3 Asm.K1_14_2_2_4_4 Asm.K1_14_2_2_4_5 Asm.K1_14_2_2_5 Asm.K1_14_2_2_7
theorem Asm.K1_14_2_2 : K1_14_2.c2 := Asm.K1_14_2_2R
theorem Asm.K1_14_2_3_1 : K1_14_2_3.c1 := K1_14_2_3_1.proof
theorem Asm.K1_14_2_3_2_1 : K1_14_2_3_2.c1 := K1_14_2_3_2_1.proof
theorem Asm.K1_14_2_3_2_2 : K1_14_2_3_2.c2 := K1_14_2_3_2_2.proof
theorem Asm.K1_14_2_3_2 : K1_14_2_3.c2 := K1_14_2_3_2.of_children Asm.K1_14_2_3_2_1 Asm.K1_14_2_3_2_2
theorem Asm.K1_14_2_3 : K1_14_2.c3 := K1_14_2_3.of_children Asm.K1_14_2_3_1 Asm.K1_14_2_3_2
theorem Asm.K1_14_2_4_1_1_1 : K1_14_2_4_1_1.c1 := K1_14_2_4_1_1_1.proof
theorem Asm.K1_14_2_4_1_1_2 : K1_14_2_4_1_1.c2 := K1_14_2_4_1_1_2.proof
theorem Asm.K1_14_2_4_1_1 : K1_14_2_4_1.c1 := K1_14_2_4_1_1.of_children Asm.K1_14_2_4_1_1_1 Asm.K1_14_2_4_1_1_2
theorem Asm.K1_14_2_4_1_2_1 : K1_14_2_4_1_2.c1 := K1_14_2_4_1_2_1.proof
theorem Asm.K1_14_2_4_1_2_2 : K1_14_2_4_1_2.c2 := K1_14_2_4_1_2_2.proof
theorem Asm.K1_14_2_4_1_2 : K1_14_2_4_1.c2 := K1_14_2_4_1_2.of_children Asm.K1_14_2_4_1_2_1 Asm.K1_14_2_4_1_2_2
theorem Asm.K1_14_2_4_1_3_1 : K1_14_2_4_1_3.c1 := K1_14_2_4_1_3_1.proof
theorem Asm.K1_14_2_4_1_3_2_1 : K1_14_2_4_1_3_2.c1 := K1_14_2_4_1_3_2_1.proof
theorem Asm.K1_14_2_4_1_3_2_2 : K1_14_2_4_1_3_2.c2 := K1_14_2_4_1_3_2_2.proof
theorem Asm.K1_14_2_4_1_3_2 : K1_14_2_4_1_3.c2 := K1_14_2_4_1_3_2.of_children Asm.K1_14_2_4_1_3_2_1 Asm.K1_14_2_4_1_3_2_2
theorem Asm.K1_14_2_4_1_3_3_1 : K1_14_2_4_1_3_3.c1 := K1_14_2_4_1_3_3_1.proof
theorem Asm.K1_14_2_4_1_3_3_2 : K1_14_2_4_1_3_3.c2 := K1_14_2_4_1_3_3_2.proof
theorem Asm.K1_14_2_4_1_3_3_3 : K1_14_2_4_1_3_3.c3 := K1_14_2_4_1_3_3_3.proof
theorem Asm.K1_14_2_4_1_3_3 : K1_14_2_4_1_3.c3 := K1_14_2_4_1_3_3.of_children Asm.K1_14_2_4_1_3_3_1 Asm.K1_14_2_4_1_3_3_2 Asm.K1_14_2_4_1_3_3_3
theorem Asm.K1_14_2_4_1_3 : K1_14_2_4_1.c3 := K1_14_2_4_1_3.of_children Asm.K1_14_2_4_1_3_1 Asm.K1_14_2_4_1_3_2 Asm.K1_14_2_4_1_3_3
theorem Asm.K1_14_2_4_1_4_1 : K1_14_2_4_1_4.c1 := K1_14_2_4_1_4_1.proof
theorem Asm.K1_14_2_4_1_4_2 : K1_14_2_4_1_4.c2 := K1_14_2_4_1_4_2.proof
theorem Asm.K1_14_2_4_1_4_3 : K1_14_2_4_1_4.c3 := K1_14_2_4_1_4_3.proof
theorem Asm.K1_14_2_4_1_4 : K1_14_2_4_1.c4 := K1_14_2_4_1_4.of_children Asm.K1_14_2_4_1_4_1 Asm.K1_14_2_4_1_4_2 Asm.K1_14_2_4_1_4_3
theorem Asm.K1_14_2_4_1_5_1 : K1_14_2_4_1_5.c1 := K1_14_2_4_1_5_1.proof
theorem Asm.K1_14_2_4_1_5_2 : K1_14_2_4_1_5.c2 := K1_14_2_4_1_5_2.proof
theorem Asm.K1_14_2_4_1_5 : K1_14_2_4_1.c5 := K1_14_2_4_1_5.of_children Asm.K1_14_2_4_1_5_1 Asm.K1_14_2_4_1_5_2
theorem Asm.K1_14_2_4_1 : K1_14_2_4.c1 := K1_14_2_4_1.of_children Asm.K1_14_2_4_1_1 Asm.K1_14_2_4_1_2 Asm.K1_14_2_4_1_3 Asm.K1_14_2_4_1_4 Asm.K1_14_2_4_1_5
theorem Asm.K1_14_2_4_2 : K1_14_2_4.c2 := K1_14_2_4_2.proof
theorem Asm.K1_14_2_4_3_1_1 : K1_14_2_4_3_1.c1 := K1_14_2_4_3_1_1.proof
theorem Asm.K1_14_2_4_3_1_2 : K1_14_2_4_3_1.c2 := K1_14_2_4_3_1_2.proof
theorem Asm.K1_14_2_4_3_1 : K1_14_2_4_3.c1 := K1_14_2_4_3_1.of_children Asm.K1_14_2_4_3_1_1 Asm.K1_14_2_4_3_1_2
theorem Asm.K1_14_2_4_3_2_1 : K1_14_2_4_3_2.c1 := K1_14_2_4_3_2_1.proof
theorem Asm.K1_14_2_4_3_2_2 : K1_14_2_4_3_2.c2 := K1_14_2_4_3_2_2.proof
theorem Asm.K1_14_2_4_3_2 : K1_14_2_4_3.c2 := K1_14_2_4_3_2.of_children Asm.K1_14_2_4_3_2_1 Asm.K1_14_2_4_3_2_2
theorem Asm.K1_14_2_4_3 : K1_14_2_4.c3 := K1_14_2_4_3.of_children Asm.K1_14_2_4_3_1 Asm.K1_14_2_4_3_2
theorem Asm.K1_14_2_4 : K1_14_2.c4 := K1_14_2_4.of_children Asm.K1_14_2_4_1 Asm.K1_14_2_4_2 Asm.K1_14_2_4_3
theorem Asm.K1_14_2_5 : K1_14_2.c5 := K1_14_2_5.proof
theorem Asm.K1_14_2_6_1 : K1_14_2_6.c1 := K1_14_2_6_1.proof
theorem Asm.K1_14_2_6_2 : K1_14_2_6.c2 := K1_14_2_6_2.proof
theorem Asm.K1_14_2_6 : K1_14_2.c6 := K1_14_2_6.of_children Asm.K1_14_2_6_1 Asm.K1_14_2_6_2
theorem Asm.K1_14_2_7 : K1_14_2.c7 := K1_14_2_7.proof
theorem Asm.K1_14_2 : K1_14.c2 := K1_14_2.of_children Asm.K1_14_2_1 Asm.K1_14_2_2 Asm.K1_14_2_3 Asm.K1_14_2_4 Asm.K1_14_2_5 Asm.K1_14_2_6 Asm.K1_14_2_7
theorem Asm.K1_14_3_2_5_1 : K1_14_3_2_5.c1 := K1_14_3_2_5_1.proof
theorem Asm.K1_14_3_2_5_2 : K1_14_3_2_5.c2 := K1_14_3_2_5_2.proof
theorem Asm.K1_14_3_2_5_3 : K1_14_3_2_5.c3 := K1_14_3_2_5_3.proof
theorem Asm.K1_14_3_2_5 : K1_14_3_2.c5 := K1_14_3_2_5.of_children Asm.K1_14_3_2_5_1 Asm.K1_14_3_2_5_2 Asm.K1_14_3_2_5_3
theorem Asm.K1_14_3_2_6_1 : K1_14_3_2_6.c1 := K1_14_3_2_6_1.proof
theorem Asm.K1_14_3_2_6_2_1 : K1_14_3_2_6_2.c1 := K1_14_3_2_6_2_1.proof
theorem Asm.K1_14_3_2_6_2_2 : K1_14_3_2_6_2.c2 := K1_14_3_2_6_2_2.proof
theorem Asm.K1_14_3_2_6_2_3 : K1_14_3_2_6_2.c3 := K1_14_3_2_6_2_3.proof
theorem Asm.K1_14_3_2_6_2_4 : K1_14_3_2_6_2.c4 := K1_14_3_2_6_2_4.proof
theorem Asm.K1_14_3_2_6_2 : K1_14_3_2_6.c2 := K1_14_3_2_6_2.of_children Asm.K1_14_3_2_6_2_1 Asm.K1_14_3_2_6_2_2 Asm.K1_14_3_2_6_2_3 Asm.K1_14_3_2_6_2_4
theorem Asm.K1_14_3_2_6 : K1_14_3_2.c6 := K1_14_3_2_6.of_children Asm.K1_14_3_2_6_1 Asm.K1_14_3_2_6_2
theorem Asm.K1_14_3_2R : K1_14_3.c2 := K1_14_3_2R.of_children Asm.K1_14_3_2_5 Asm.K1_14_3_2_6
theorem Asm.K1_14_3_2 : K1_14_3.c2 := Asm.K1_14_3_2R
theorem Asm.K1_14_3R_1 : K1_14_3R.c1 := K1_14_3R_1.proof
theorem Asm.K1_14_3R_2_1 : K1_14_3R_2.c1 := K1_14_3R_2_1.proof
theorem Asm.K1_14_3R_2_2 : K1_14_3R_2.c2 := K1_14_3R_2_2.proof
theorem Asm.K1_14_3R_2_3 : K1_14_3R_2.c3 := K1_14_3R_2_3.proof
theorem Asm.K1_14_3R_2_4 : K1_14_3R_2.c4 := K1_14_3R_2_4.proof
theorem Asm.K1_14_3R_2 : K1_14_3R.c2 := K1_14_3R_2.of_children Asm.K1_14_3R_2_1 Asm.K1_14_3R_2_2 Asm.K1_14_3R_2_3 Asm.K1_14_3R_2_4
theorem Asm.K1_14_3R_3_1_1 : K1_14_3R_3_1.c1 := K1_14_3R_3_1_1.proof
theorem Asm.K1_14_3R_3_1_2_1 : K1_14_3R_3_1_2.c1 := K1_14_3R_3_1_2_1.proof
theorem Asm.K1_14_3R_3_1_2_2 : K1_14_3R_3_1_2.c2 := K1_14_3R_3_1_2_2.proof
theorem Asm.K1_14_3R_3_1_2_3 : K1_14_3R_3_1_2.c3 := K1_14_3R_3_1_2_3.proof
theorem Asm.K1_14_3R_3_1_2 : K1_14_3R_3_1.c2 := K1_14_3R_3_1_2.of_children Asm.K1_14_3R_3_1_2_1 Asm.K1_14_3R_3_1_2_2 Asm.K1_14_3R_3_1_2_3
theorem Asm.K1_14_3R_3_1_3_1 : K1_14_3R_3_1_3.c1 := K1_14_3R_3_1_3_1.proof
theorem Asm.K1_14_3R_3_1_3_2 : K1_14_3R_3_1_3.c2 := K1_14_3R_3_1_3_2.proof
theorem Asm.K1_14_3R_3_1_3_3 : K1_14_3R_3_1_3.c3 := K1_14_3R_3_1_3_3.proof
theorem Asm.K1_14_3R_3_1_3_4 : K1_14_3R_3_1_3.c4 := K1_14_3R_3_1_3_4.proof
theorem Asm.K1_14_3R_3_1_3_5 : K1_14_3R_3_1_3.c5 := K1_14_3R_3_1_3_5.proof
theorem Asm.K1_14_3R_3_1_3 : K1_14_3R_3_1.c3 := K1_14_3R_3_1_3.of_children Asm.K1_14_3R_3_1_3_1 Asm.K1_14_3R_3_1_3_2 Asm.K1_14_3R_3_1_3_3 Asm.K1_14_3R_3_1_3_4 Asm.K1_14_3R_3_1_3_5
theorem Asm.K1_14_3R_3_1_4 : K1_14_3R_3_1.c4 := K1_14_3R_3_1_4.proof
theorem Asm.K1_14_3R_3_1 : K1_14_3R_3.c1 := K1_14_3R_3_1.of_children Asm.K1_14_3R_3_1_1 Asm.K1_14_3R_3_1_2 Asm.K1_14_3R_3_1_3 Asm.K1_14_3R_3_1_4
theorem Asm.K1_14_3R_3_2_1 : K1_14_3R_3_2.c1 := K1_14_3R_3_2_1.proof
theorem Asm.K1_14_3R_3_2_2 : K1_14_3R_3_2.c2 := K1_14_3R_3_2_2.proof
theorem Asm.K1_14_3R_3_2_3_1 : K1_14_3R_3_2_3.c1 := K1_14_3R_3_2_3_1.proof
theorem Asm.K1_14_3R_3_2_3_2 : K1_14_3R_3_2_3.c2 := K1_14_3R_3_2_3_2.proof
theorem Asm.K1_14_3R_3_2_3 : K1_14_3R_3_2.c3 := K1_14_3R_3_2_3.of_children Asm.K1_14_3R_3_2_3_1 Asm.K1_14_3R_3_2_3_2
theorem Asm.K1_14_3R_3_2_4 : K1_14_3R_3_2.c4 := K1_14_3R_3_2_4.proof
theorem Asm.K1_14_3R_3_2 : K1_14_3R_3.c2 := K1_14_3R_3_2.of_children Asm.K1_14_3R_3_2_1 Asm.K1_14_3R_3_2_2 Asm.K1_14_3R_3_2_3 Asm.K1_14_3R_3_2_4
theorem Asm.K1_14_3R_3_3 : K1_14_3R_3.c3 := K1_14_3R_3_3.proof
theorem Asm.K1_14_3R_3_4 : K1_14_3R_3.c4 := K1_14_3R_3_4.proof
theorem Asm.K1_14_3R_3 : K1_14_3R.c3 := K1_14_3R_3.of_children Asm.K1_14_3R_3_1 Asm.K1_14_3R_3_2 Asm.K1_14_3R_3_3 Asm.K1_14_3R_3_4
theorem Asm.K1_14_3_6_1 : K1_14_3_6.c1 := K1_14_3_6_1.proof
theorem Asm.K1_14_3_6_2 : K1_14_3_6.c2 := K1_14_3_6_2.proof
theorem Asm.K1_14_3_6 : K1_14_3.c6 := K1_14_3_6.of_children Asm.K1_14_3_6_1 Asm.K1_14_3_6_2
theorem Asm.K1_14_3R : K1_14.c3 := K1_14_3R.of_children Asm.K1_14_2_1_1 Asm.K1_14_2_1_2 Asm.K1_14_3_2 Asm.K1_14_3R_1 Asm.K1_14_3R_2 Asm.K1_14_3R_3 Asm.K1_14_3_6
theorem Asm.K1_14_3 : K1_14.c3 := Asm.K1_14_3R
theorem Asm.K1_14_4 : K1_14.c4 := K1_14_4.proof
theorem Asm.K1_14_5 : K1_14.c5 := K1_14_5.proof
theorem Asm.K1_14_6_1 : K1_14_6.c1 := K1_14_6_1.proof
theorem Asm.K1_14_6_2 : K1_14_6.c2 := K1_14_6_2.proof
theorem Asm.K1_14_6 : K1_14.c6 := K1_14_6.of_children Asm.K1_14_6_1 Asm.K1_14_6_2
theorem Asm.K1_14 : K1.c14 := K1_14.of_children Asm.K1_14_1 Asm.K1_14_2 Asm.K1_14_3 Asm.K1_14_4 Asm.K1_14_5 Asm.K1_14_6
theorem Asm.K1 : FrobeniusLocator.Native.ScalarMCACap6915 := K1.of_children Asm.K1_1 Asm.K1_2 Asm.K1_3 Asm.K1_4 Asm.K1_5 Asm.K1_6 Asm.K1_7 Asm.K1_8 Asm.K1_9 Asm.K1_10 Asm.K1_11 Asm.K1_12 Asm.K1_13 Asm.K1_14

theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6916 81889 262144 :=
  FrobeniusLocator.Native.protocolClaim6915_of_scalarCap Asm.K1
