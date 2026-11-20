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
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace LowPrice6921.Geometry

theorem K1_13_5_1 : K1_13_5.c1 := K1_13_5_1.proof
theorem K1_13_5_2 : K1_13_5.c2 := K1_13_5_2.proof
theorem K1_13_5_4_1_1 : K1_13_5_4_1.c1 := K1_13_5_4_1_1.proof
theorem K1_13_5_4_1_2 : K1_13_5_4_1.c2 := K1_13_5_4_1_2.proof
theorem K1_13_5_4_1 : K1_13_5_4.c1 := K1_13_5_4_1.of_children Geometry.K1_13_5_4_1_1 Geometry.K1_13_5_4_1_2
theorem K1_13_5_4_2_1 : K1_13_5_4_2.c1 := K1_13_5_4_2_1.proof
theorem K1_13_5_4_2_2_1 : K1_13_5_4_2_2.c1 := K1_13_5_4_2_2_1.proof
theorem K1_13_5_4_2_2_2 : K1_13_5_4_2_2.c2 := K1_13_5_4_2_2_2.proof
theorem K1_13_5_4_2_2_3 : K1_13_5_4_2_2.c3 := K1_13_5_4_2_2_3.proof
theorem K1_13_5_4_2_2 : K1_13_5_4_2.c2 := K1_13_5_4_2_2.of_children Geometry.K1_13_5_4_2_2_1 Geometry.K1_13_5_4_2_2_2 Geometry.K1_13_5_4_2_2_3
theorem K1_13_5_4_2_3_1 : K1_13_5_4_2_3.c1 := K1_13_5_4_2_3_1.proof
theorem K1_13_5_4_2_3_2 : K1_13_5_4_2_3.c2 := K1_13_5_4_2_3_2.proof
theorem K1_13_5_4_2_3 : K1_13_5_4_2.c3 := K1_13_5_4_2_3.of_children Geometry.K1_13_5_4_2_3_1 Geometry.K1_13_5_4_2_3_2
theorem K1_13_5_4_2_4_1_1 : K1_13_5_4_2_4_1.c1 := K1_13_5_4_2_4_1_1.proof
theorem K1_13_5_4_2_4_1_2 : K1_13_5_4_2_4_1.c2 := K1_13_5_4_2_4_1_2.proof
theorem K1_13_5_4_2_4_1 : K1_13_5_4_2_4.c1 := K1_13_5_4_2_4_1.of_children Geometry.K1_13_5_4_2_4_1_1 Geometry.K1_13_5_4_2_4_1_2
theorem K1_13_5_4_2_4_2_1 : K1_13_5_4_2_4_2.c1 := K1_13_5_4_2_4_2_1.proof
theorem K1_13_5_4_2_4_2_2 : K1_13_5_4_2_4_2.c2 := K1_13_5_4_2_4_2_2.proof
theorem K1_13_5_4_2_4_2_3_1 : K1_13_5_4_2_4_2_3.c1 := K1_13_5_4_2_4_2_3_1.proof
theorem K1_13_5_4_2_4_2_3_2 : K1_13_5_4_2_4_2_3.c2 := K1_13_5_4_2_4_2_3_2.proof
theorem K1_13_5_4_2_4_2_3 : K1_13_5_4_2_4_2.c3 := K1_13_5_4_2_4_2_3.of_children Geometry.K1_13_5_4_2_4_2_3_1 Geometry.K1_13_5_4_2_4_2_3_2
theorem K1_13_5_4_2_4_2 : K1_13_5_4_2_4.c2 := K1_13_5_4_2_4_2.of_children Geometry.K1_13_5_4_2_4_2_1 Geometry.K1_13_5_4_2_4_2_2 Geometry.K1_13_5_4_2_4_2_3
theorem K1_13_5_4_2_4_3 : K1_13_5_4_2_4.c3 := K1_13_5_4_2_4_3.proof
theorem K1_13_5_4_2_4 : K1_13_5_4_2.c4 := K1_13_5_4_2_4.of_children Geometry.K1_13_5_4_2_4_1 Geometry.K1_13_5_4_2_4_2 Geometry.K1_13_5_4_2_4_3
theorem K1_13_5_4_2_5_1_1_1 : K1_13_5_4_2_5_1_1.c1 := K1_13_5_4_2_5_1_1_1.proof
theorem K1_13_5_4_2_5_1_1_2 : K1_13_5_4_2_5_1_1.c2 := K1_13_5_4_2_5_1_1_2.proof
theorem K1_13_5_4_2_5_1_1 : K1_13_5_4_2_5_1.c1 := K1_13_5_4_2_5_1_1.of_children Geometry.K1_13_5_4_2_5_1_1_1 Geometry.K1_13_5_4_2_5_1_1_2
theorem K1_13_5_4_2_5_1_2 : K1_13_5_4_2_5_1.c2 := K1_13_5_4_2_5_1_2.proof
theorem K1_13_5_4_2_5_1 : K1_13_5_4_2_5.c1 := K1_13_5_4_2_5_1.of_children Geometry.K1_13_5_4_2_5_1_1 Geometry.K1_13_5_4_2_5_1_2
theorem K1_13_5_4_2_5_2_1_1 : K1_13_5_4_2_5_2_1.c1 := K1_13_5_4_2_5_2_1_1.proof
theorem K1_13_5_4_2_5_2_1_2 : K1_13_5_4_2_5_2_1.c2 := K1_13_5_4_2_5_2_1_2.proof
theorem K1_13_5_4_2_5_2_1 : K1_13_5_4_2_5_2.c1 := K1_13_5_4_2_5_2_1.of_children Geometry.K1_13_5_4_2_5_2_1_1 Geometry.K1_13_5_4_2_5_2_1_2
theorem K1_13_5_4_2_5_2_2 : K1_13_5_4_2_5_2.c2 := K1_13_5_4_2_5_2_2.proof
theorem K1_13_5_4_2_5_2 : K1_13_5_4_2_5.c2 := K1_13_5_4_2_5_2.of_children Geometry.K1_13_5_4_2_5_2_1 Geometry.K1_13_5_4_2_5_2_2
theorem K1_13_5_4_2_5 : K1_13_5_4_2.c5 := K1_13_5_4_2_5.of_children Geometry.K1_13_5_4_2_5_1 Geometry.K1_13_5_4_2_5_2
theorem K1_13_5_4_2 : K1_13_5_4.c2 := K1_13_5_4_2.of_children Geometry.K1_13_5_4_2_1 Geometry.K1_13_5_4_2_2 Geometry.K1_13_5_4_2_3 Geometry.K1_13_5_4_2_4 Geometry.K1_13_5_4_2_5
theorem K1_13_5_4_3_1 : K1_13_5_4_3.c1 := K1_13_5_4_3_1.proof
theorem K1_13_5_4_3_2 : K1_13_5_4_3.c2 := K1_13_5_4_3_2.proof
theorem K1_13_5_4_3_3 : K1_13_5_4_3.c3 := K1_13_5_4_3_3.proof
theorem K1_13_5_4_3_4 : K1_13_5_4_3.c4 := K1_13_5_4_3_4.proof
theorem K1_13_5_4_3 : K1_13_5_4.c3 := K1_13_5_4_3.of_children Geometry.K1_13_5_4_3_1 Geometry.K1_13_5_4_3_2 Geometry.K1_13_5_4_3_3 Geometry.K1_13_5_4_3_4
theorem K1_13_5_4_4_1_1 : K1_13_5_4_4_1.c1 := K1_13_5_4_4_1_1.proof
theorem K1_13_5_4_4_1_2 : K1_13_5_4_4_1.c2 := K1_13_5_4_4_1_2.proof
theorem K1_13_5_4_4_1 : K1_13_5_4_4.c1 := K1_13_5_4_4_1.of_children Geometry.K1_13_5_4_4_1_1 Geometry.K1_13_5_4_4_1_2
theorem K1_13_5_4_4_2 : K1_13_5_4_4.c2 := K1_13_5_4_4_2.proof
theorem K1_13_5_4_4 : K1_13_5_4.c4 := K1_13_5_4_4.of_children Geometry.K1_13_5_4_4_1 Geometry.K1_13_5_4_4_2
theorem K1_13_5_5_1_1 : K1_13_5_5_1.c1 := K1_13_5_5_1_1.proof
theorem K1_13_5_5_1_2 : K1_13_5_5_1.c2 := K1_13_5_5_1_2.proof
theorem K1_13_5_5_1_3 : K1_13_5_5_1.c3 := K1_13_5_5_1_3.proof
theorem K1_13_5_5_1 : K1_13_5_5.c1 := K1_13_5_5_1.of_children Geometry.K1_13_5_5_1_1 Geometry.K1_13_5_5_1_2 Geometry.K1_13_5_5_1_3
theorem K1_13_5_5_2_1_1_1 : K1_13_5_5_2_1_1.c1 := K1_13_5_5_2_1_1_1.proof
theorem K1_13_5_5_2_1_1_2 : K1_13_5_5_2_1_1.c2 := K1_13_5_5_2_1_1_2.proof
theorem K1_13_5_5_2_1_1_3 : K1_13_5_5_2_1_1.c3 := K1_13_5_5_2_1_1_3.proof
theorem K1_13_5_5_2_1_1 : K1_13_5_5_2_1.c1 := K1_13_5_5_2_1_1.of_children Geometry.K1_13_5_5_2_1_1_1 Geometry.K1_13_5_5_2_1_1_2 Geometry.K1_13_5_5_2_1_1_3
theorem K1_13_5_5_2_1_2 : K1_13_5_5_2_1.c2 := K1_13_5_5_2_1_2.proof
theorem K1_13_5_5_2_1_3 : K1_13_5_5_2_1.c3 := K1_13_5_5_2_1_3.proof
theorem K1_13_5_5_2_1_4_1 : K1_13_5_5_2_1_4.c1 := K1_13_5_5_2_1_4_1.proof
theorem K1_13_5_5_2_1_4_2 : K1_13_5_5_2_1_4.c2 := K1_13_5_5_2_1_4_2.proof
theorem K1_13_5_5_2_1_4 : K1_13_5_5_2_1.c4 := K1_13_5_5_2_1_4.of_children Geometry.K1_13_5_5_2_1_4_1 Geometry.K1_13_5_5_2_1_4_2
theorem K1_13_5_5_2_1_5 : K1_13_5_5_2_1.c5 := K1_13_5_5_2_1_5.proof
theorem K1_13_5_5_2_1_6 : K1_13_5_5_2_1.c6 := K1_13_5_5_2_1_6.proof
theorem K1_13_5_5_2_1 : K1_13_5_5_2.c1 := K1_13_5_5_2_1.of_children Geometry.K1_13_5_5_2_1_1 Geometry.K1_13_5_5_2_1_2 Geometry.K1_13_5_5_2_1_3 Geometry.K1_13_5_5_2_1_4 Geometry.K1_13_5_5_2_1_5 Geometry.K1_13_5_5_2_1_6
theorem K1_13_5_5_2_2_1 : K1_13_5_5_2_2.c1 := K1_13_5_5_2_2_1.proof
theorem K1_13_5_5_2_2_2 : K1_13_5_5_2_2.c2 := K1_13_5_5_2_2_2.proof
theorem K1_13_5_5_2_2 : K1_13_5_5_2.c2 := K1_13_5_5_2_2.of_children Geometry.K1_13_5_5_2_2_1 Geometry.K1_13_5_5_2_2_2
theorem K1_13_5_5_2_3_1 : K1_13_5_5_2_3.c1 := K1_13_5_5_2_3_1.proof
theorem K1_13_5_5_2_3_2 : K1_13_5_5_2_3.c2 := K1_13_5_5_2_3_2.proof
theorem K1_13_5_5_2_3_3 : K1_13_5_5_2_3.c3 := K1_13_5_5_2_3_3.proof
theorem K1_13_5_5_2_3 : K1_13_5_5_2.c3 := K1_13_5_5_2_3.of_children Geometry.K1_13_5_5_2_3_1 Geometry.K1_13_5_5_2_3_2 Geometry.K1_13_5_5_2_3_3
theorem K1_13_5_5_2 : K1_13_5_5.c2 := K1_13_5_5_2.of_children Geometry.K1_13_5_5_2_1 Geometry.K1_13_5_5_2_2 Geometry.K1_13_5_5_2_3
theorem K1_13_6_1_1 : K1_13_6_1.c1 := K1_13_6_1_1.proof
theorem K1_13_6_1_2_1 : K1_13_6_1_2.c1 := K1_13_6_1_2_1.proof
theorem K1_13_6_1_2_2 : K1_13_6_1_2.c2 := K1_13_6_1_2_2.proof
theorem K1_13_6_1_2 : K1_13_6_1.c2 := K1_13_6_1_2.of_children Geometry.K1_13_6_1_2_1 Geometry.K1_13_6_1_2_2
theorem K1_13_6_1_3_1 : K1_13_6_1_3.c1 := K1_13_6_1_3_1.proof
theorem K1_13_6_1_3_2 : K1_13_6_1_3.c2 := K1_13_6_1_3_2.proof
theorem K1_13_6_1_3_3 : K1_13_6_1_3.c3 := K1_13_6_1_3_3.proof
theorem K1_13_6_1_3 : K1_13_6_1.c3 := K1_13_6_1_3.of_children Geometry.K1_13_6_1_3_1 Geometry.K1_13_6_1_3_2 Geometry.K1_13_6_1_3_3
theorem K1_13_6_1_4_1_1 : K1_13_6_1_4_1.c1 := K1_13_6_1_4_1_1.proof
theorem K1_13_6_1_4_1_2 : K1_13_6_1_4_1.c2 := K1_13_6_1_4_1_2.proof
theorem K1_13_6_1_4_1 : K1_13_6_1_4.c1 := K1_13_6_1_4_1.of_children Geometry.K1_13_6_1_4_1_1 Geometry.K1_13_6_1_4_1_2
theorem K1_13_6_1_4_2_1_1_1 : K1_13_6_1_4_2_1_1.c1 := K1_13_6_1_4_2_1_1_1.proof
theorem K1_13_6_1_4_2_1_1_2 : K1_13_6_1_4_2_1_1.c2 := K1_13_6_1_4_2_1_1_2.proof
theorem K1_13_6_1_4_2_1_1 : K1_13_6_1_4_2_1.c1 := K1_13_6_1_4_2_1_1.of_children Geometry.K1_13_6_1_4_2_1_1_1 Geometry.K1_13_6_1_4_2_1_1_2
theorem K1_13_6_1_4_2_1_2_1 : K1_13_6_1_4_2_1_2.c1 := K1_13_6_1_4_2_1_2_1.proof
theorem K1_13_6_1_4_2_1_2_2_1 : K1_13_6_1_4_2_1_2_2.c1 := K1_13_6_1_4_2_1_2_2_1.proof
theorem K1_13_6_1_4_2_1_2_2_2 : K1_13_6_1_4_2_1_2_2.c2 := K1_13_6_1_4_2_1_2_2_2.proof
theorem K1_13_6_1_4_2_1_2_2 : K1_13_6_1_4_2_1_2.c2 := K1_13_6_1_4_2_1_2_2.of_children Geometry.K1_13_6_1_4_2_1_2_2_1 Geometry.K1_13_6_1_4_2_1_2_2_2
theorem K1_13_6_1_4_2_1_2 : K1_13_6_1_4_2_1.c2 := K1_13_6_1_4_2_1_2.of_children Geometry.K1_13_6_1_4_2_1_2_1 Geometry.K1_13_6_1_4_2_1_2_2
theorem K1_13_6_1_4_2_1 : K1_13_6_1_4_2.c1 := K1_13_6_1_4_2_1.of_children Geometry.K1_13_6_1_4_2_1_1 Geometry.K1_13_6_1_4_2_1_2
theorem K1_13_6_1_4_2_2_1 : K1_13_6_1_4_2_2.c1 := K1_13_6_1_4_2_2_1.proof
theorem K1_13_6_1_4_2_2_2 : K1_13_6_1_4_2_2.c2 := K1_13_6_1_4_2_2_2.proof
theorem K1_13_6_1_4_2_2 : K1_13_6_1_4_2.c2 := K1_13_6_1_4_2_2.of_children Geometry.K1_13_6_1_4_2_2_1 Geometry.K1_13_6_1_4_2_2_2
theorem K1_13_6_1_4_2 : K1_13_6_1_4.c2 := K1_13_6_1_4_2.of_children Geometry.K1_13_6_1_4_2_1 Geometry.K1_13_6_1_4_2_2
theorem K1_13_6_1_4_3_1 : K1_13_6_1_4_3.c1 := K1_13_6_1_4_3_1.proof
theorem K1_13_6_1_4_3_2 : K1_13_6_1_4_3.c2 := K1_13_6_1_4_3_2.proof
theorem K1_13_6_1_4_3_3_1_1 : K1_13_6_1_4_3_3_1.c1 := K1_13_6_1_4_3_3_1_1.proof
theorem K1_13_6_1_4_3_3_1_2 : K1_13_6_1_4_3_3_1.c2 := K1_13_6_1_4_3_3_1_2.proof
theorem K1_13_6_1_4_3_3_1 : K1_13_6_1_4_3_3.c1 := K1_13_6_1_4_3_3_1.of_children Geometry.K1_13_6_1_4_3_3_1_1 Geometry.K1_13_6_1_4_3_3_1_2
theorem K1_13_6_1_4_3_3_2_1 : K1_13_6_1_4_3_3_2.c1 := K1_13_6_1_4_3_3_2_1.proof
theorem K1_13_6_1_4_3_3_2_2 : K1_13_6_1_4_3_3_2.c2 := K1_13_6_1_4_3_3_2_2.proof
theorem K1_13_6_1_4_3_3_2 : K1_13_6_1_4_3_3.c2 := K1_13_6_1_4_3_3_2.of_children Geometry.K1_13_6_1_4_3_3_2_1 Geometry.K1_13_6_1_4_3_3_2_2
theorem K1_13_6_1_4_3_3_3_1 : K1_13_6_1_4_3_3_3.c1 := K1_13_6_1_4_3_3_3_1.proof
theorem K1_13_6_1_4_3_3_3_2_1 : K1_13_6_1_4_3_3_3_2.c1 := K1_13_6_1_4_3_3_3_2_1.proof
theorem K1_13_6_1_4_3_3_3_2_2 : K1_13_6_1_4_3_3_3_2.c2 := K1_13_6_1_4_3_3_3_2_2.proof
theorem K1_13_6_1_4_3_3_3_2 : K1_13_6_1_4_3_3_3.c2 := K1_13_6_1_4_3_3_3_2.of_children Geometry.K1_13_6_1_4_3_3_3_2_1 Geometry.K1_13_6_1_4_3_3_3_2_2
theorem K1_13_6_1_4_3_3_3 : K1_13_6_1_4_3_3.c3 := K1_13_6_1_4_3_3_3.of_children Geometry.K1_13_6_1_4_3_3_3_1 Geometry.K1_13_6_1_4_3_3_3_2
theorem K1_13_6_1_4_3_3 : K1_13_6_1_4_3.c3 := K1_13_6_1_4_3_3.of_children Geometry.K1_13_6_1_4_3_3_1 Geometry.K1_13_6_1_4_3_3_2 Geometry.K1_13_6_1_4_3_3_3
theorem K1_13_6_1_4_3 : K1_13_6_1_4.c3 := K1_13_6_1_4_3.of_children Geometry.K1_13_6_1_4_3_1 Geometry.K1_13_6_1_4_3_2 Geometry.K1_13_6_1_4_3_3
theorem K1_13_6_1_4 : K1_13_6_1.c4 := K1_13_6_1_4.of_children Geometry.K1_13_6_1_4_1 Geometry.K1_13_6_1_4_2 Geometry.K1_13_6_1_4_3
theorem K1_13_6_1_5_1 : K1_13_6_1_5.c1 := K1_13_6_1_5_1.proof
theorem K1_13_6_1_5_2_1 : K1_13_6_1_5_2.c1 := K1_13_6_1_5_2_1.proof
theorem K1_13_6_1_5_2_2 : K1_13_6_1_5_2.c2 := K1_13_6_1_5_2_2.proof
theorem K1_13_6_1_5_2 : K1_13_6_1_5.c2 := K1_13_6_1_5_2.of_children Geometry.K1_13_6_1_5_2_1 Geometry.K1_13_6_1_5_2_2
theorem K1_13_6_1_5 : K1_13_6_1.c5 := K1_13_6_1_5.of_children Geometry.K1_13_6_1_5_1 Geometry.K1_13_6_1_5_2
theorem K1_13_6_1 : K1_13_6.c1 := K1_13_6_1.of_children Geometry.K1_13_6_1_1 Geometry.K1_13_6_1_2 Geometry.K1_13_6_1_3 Geometry.K1_13_6_1_4 Geometry.K1_13_6_1_5
theorem K1_13_6_2_1 : K1_13_6_2.c1 := K1_13_6_2_1.proof
theorem K1_13_6_2_2_1 : K1_13_6_2_2.c1 := K1_13_6_2_2_1.proof
theorem K1_13_6_2_2_2 : K1_13_6_2_2.c2 := K1_13_6_2_2_2.proof
theorem K1_13_6_2_2 : K1_13_6_2.c2 := K1_13_6_2_2.of_children Geometry.K1_13_6_2_2_1 Geometry.K1_13_6_2_2_2
theorem K1_13_6_2_3_1 : K1_13_6_2_3.c1 := K1_13_6_2_3_1.proof
theorem K1_13_6_2_3_2_1 : K1_13_6_2_3_2.c1 := K1_13_6_2_3_2_1.proof
theorem K1_13_6_2_3_2_2 : K1_13_6_2_3_2.c2 := K1_13_6_2_3_2_2.proof
theorem K1_13_6_2_3_2_3 : K1_13_6_2_3_2.c3 := K1_13_6_2_3_2_3.proof
theorem K1_13_6_2_3_2_4 : K1_13_6_2_3_2.c4 := K1_13_6_2_3_2_4.proof
theorem K1_13_6_2_3_2_5 : K1_13_6_2_3_2.c5 := K1_13_6_2_3_2_5.proof
theorem K1_13_6_2_3_2_6 : K1_13_6_2_3_2.c6 := K1_13_6_2_3_2_6.proof
theorem K1_13_6_2_3_2 : K1_13_6_2_3.c2 := K1_13_6_2_3_2.of_children Geometry.K1_13_6_2_3_2_1 Geometry.K1_13_6_2_3_2_2 Geometry.K1_13_6_2_3_2_3 Geometry.K1_13_6_2_3_2_4 Geometry.K1_13_6_2_3_2_5 Geometry.K1_13_6_2_3_2_6
theorem K1_13_6_2_3_3_1 : K1_13_6_2_3_3.c1 := K1_13_6_2_3_3_1.proof
theorem K1_13_6_2_3_3_2_1 : K1_13_6_2_3_3_2.c1 := K1_13_6_2_3_3_2_1.proof
theorem K1_13_6_2_3_3_2_2 : K1_13_6_2_3_3_2.c2 := K1_13_6_2_3_3_2_2.proof
theorem K1_13_6_2_3_3_2 : K1_13_6_2_3_3.c2 := K1_13_6_2_3_3_2.of_children Geometry.K1_13_6_2_3_3_2_1 Geometry.K1_13_6_2_3_3_2_2
theorem K1_13_6_2_3_3 : K1_13_6_2_3.c3 := K1_13_6_2_3_3.of_children Geometry.K1_13_6_2_3_3_1 Geometry.K1_13_6_2_3_3_2
theorem K1_13_6_2_3 : K1_13_6_2.c3 := K1_13_6_2_3.of_children Geometry.K1_13_6_2_3_1 Geometry.K1_13_6_2_3_2 Geometry.K1_13_6_2_3_3
theorem K1_13_6_2_4_1_1 : K1_13_6_2_4_1.c1 := K1_13_6_2_4_1_1.proof
theorem K1_13_6_2_4_1_2 : K1_13_6_2_4_1.c2 := K1_13_6_2_4_1_2.proof
theorem K1_13_6_2_4_1 : K1_13_6_2_4.c1 := K1_13_6_2_4_1.of_children Geometry.K1_13_6_2_4_1_1 Geometry.K1_13_6_2_4_1_2
theorem K1_13_6_2_4_2_1 : K1_13_6_2_4_2.c1 := K1_13_6_2_4_2_1.proof
theorem K1_13_6_2_4_2_2_1 : K1_13_6_2_4_2_2.c1 := K1_13_6_2_4_2_2_1.proof
theorem K1_13_6_2_4_2_2_2 : K1_13_6_2_4_2_2.c2 := K1_13_6_2_4_2_2_2.proof
theorem K1_13_6_2_4_2_2 : K1_13_6_2_4_2.c2 := K1_13_6_2_4_2_2.of_children Geometry.K1_13_6_2_4_2_2_1 Geometry.K1_13_6_2_4_2_2_2
theorem K1_13_6_2_4_2 : K1_13_6_2_4.c2 := K1_13_6_2_4_2.of_children Geometry.K1_13_6_2_4_2_1 Geometry.K1_13_6_2_4_2_2
theorem K1_13_6_2_4_3_1 : K1_13_6_2_4_3.c1 := K1_13_6_2_4_3_1.proof
theorem K1_13_6_2_4_3_2 : K1_13_6_2_4_3.c2 := K1_13_6_2_4_3_2.proof
theorem K1_13_6_2_4_3 : K1_13_6_2_4.c3 := K1_13_6_2_4_3.of_children Geometry.K1_13_6_2_4_3_1 Geometry.K1_13_6_2_4_3_2
theorem K1_13_6_2_4_4 : K1_13_6_2_4.c4 := K1_13_6_2_4_4.proof
theorem K1_13_6_2_4_5 : K1_13_6_2_4.c5 := K1_13_6_2_4_5.proof
theorem K1_13_6_2_4 : K1_13_6_2.c4 := K1_13_6_2_4.of_children Geometry.K1_13_6_2_4_1 Geometry.K1_13_6_2_4_2 Geometry.K1_13_6_2_4_3 Geometry.K1_13_6_2_4_4 Geometry.K1_13_6_2_4_5
theorem K1_13_6_2 : K1_13_6.c2 := K1_13_6_2.of_children Geometry.K1_13_6_2_1 Geometry.K1_13_6_2_2 Geometry.K1_13_6_2_3 Geometry.K1_13_6_2_4
theorem K1_13_6_3_1_1 : K1_13_6_3_1.c1 := K1_13_6_3_1_1.proof
theorem K1_13_6_3_1_2 : K1_13_6_3_1.c2 := K1_13_6_3_1_2.proof
theorem K1_13_6_3_1 : K1_13_6_3.c1 := K1_13_6_3_1.of_children Geometry.K1_13_6_3_1_1 Geometry.K1_13_6_3_1_2
theorem K1_13_6_3_2_1 : K1_13_6_3_2.c1 := K1_13_6_3_2_1.proof
theorem K1_13_6_3_2_2 : K1_13_6_3_2.c2 := K1_13_6_3_2_2.proof
theorem K1_13_6_3_2_3 : K1_13_6_3_2.c3 := K1_13_6_3_2_3.proof
theorem K1_13_6_3_2 : K1_13_6_3.c2 := K1_13_6_3_2.of_children Geometry.K1_13_6_3_2_1 Geometry.K1_13_6_3_2_2 Geometry.K1_13_6_3_2_3
theorem K1_13_6_3_3_1 : K1_13_6_3_3.c1 := K1_13_6_3_3_1.proof
theorem K1_13_6_3_3_2 : K1_13_6_3_3.c2 := K1_13_6_3_3_2.proof
theorem K1_13_6_3_3 : K1_13_6_3.c3 := K1_13_6_3_3.of_children Geometry.K1_13_6_3_3_1 Geometry.K1_13_6_3_3_2
theorem K1_13_6_3_4_1 : K1_13_6_3_4.c1 := K1_13_6_3_4_1.proof
theorem K1_13_6_3_4_2 : K1_13_6_3_4.c2 := K1_13_6_3_4_2.proof
theorem K1_13_6_3_4_3 : K1_13_6_3_4.c3 := K1_13_6_3_4_3.proof
theorem K1_13_6_3_4 : K1_13_6_3.c4 := K1_13_6_3_4.of_children Geometry.K1_13_6_3_4_1 Geometry.K1_13_6_3_4_2 Geometry.K1_13_6_3_4_3
theorem K1_13_6_3_5_1_1 : K1_13_6_3_5_1.c1 := K1_13_6_3_5_1_1.proof
theorem K1_13_6_3_5_1_2 : K1_13_6_3_5_1.c2 := K1_13_6_3_5_1_2.proof
theorem K1_13_6_3_5_1 : K1_13_6_3_5.c1 := K1_13_6_3_5_1.of_children Geometry.K1_13_6_3_5_1_1 Geometry.K1_13_6_3_5_1_2
theorem K1_13_6_3_5_2 : K1_13_6_3_5.c2 := K1_13_6_3_5_2.proof
theorem K1_13_6_3_5_3_1 : K1_13_6_3_5_3.c1 := K1_13_6_3_5_3_1.proof
theorem K1_13_6_3_5_3_2_1 : K1_13_6_3_5_3_2.c1 := K1_13_6_3_5_3_2_1.proof
theorem K1_13_6_3_5_3_2_2 : K1_13_6_3_5_3_2.c2 := K1_13_6_3_5_3_2_2.proof
theorem K1_13_6_3_5_3_2 : K1_13_6_3_5_3.c2 := K1_13_6_3_5_3_2.of_children Geometry.K1_13_6_3_5_3_2_1 Geometry.K1_13_6_3_5_3_2_2
theorem K1_13_6_3_5_3_3_1 : K1_13_6_3_5_3_3.c1 := K1_13_6_3_5_3_3_1.proof
theorem K1_13_6_3_5_3_3_2 : K1_13_6_3_5_3_3.c2 := K1_13_6_3_5_3_3_2.proof
theorem K1_13_6_3_5_3_3_3 : K1_13_6_3_5_3_3.c3 := K1_13_6_3_5_3_3_3.proof
theorem K1_13_6_3_5_3_3_4 : K1_13_6_3_5_3_3.c4 := K1_13_6_3_5_3_3_4.proof
theorem K1_13_6_3_5_3_3 : K1_13_6_3_5_3.c3 := K1_13_6_3_5_3_3.of_children Geometry.K1_13_6_3_5_3_3_1 Geometry.K1_13_6_3_5_3_3_2 Geometry.K1_13_6_3_5_3_3_3 Geometry.K1_13_6_3_5_3_3_4
theorem K1_13_6_3_5_3_4 : K1_13_6_3_5_3.c4 := K1_13_6_3_5_3_4.proof
theorem K1_13_6_3_5_3_5 : K1_13_6_3_5_3.c5 := K1_13_6_3_5_3_5.proof
theorem K1_13_6_3_5_3_6 : K1_13_6_3_5_3.c6 := K1_13_6_3_5_3_6.proof
theorem K1_13_6_3_5_3 : K1_13_6_3_5.c3 := K1_13_6_3_5_3.of_children Geometry.K1_13_6_3_5_3_1 Geometry.K1_13_6_3_5_3_2 Geometry.K1_13_6_3_5_3_3 Geometry.K1_13_6_3_5_3_4 Geometry.K1_13_6_3_5_3_5 Geometry.K1_13_6_3_5_3_6
theorem K1_13_6_3_5_4 : K1_13_6_3_5.c4 := K1_13_6_3_5_4.proof
theorem K1_13_6_3_5_5_1 : K1_13_6_3_5_5.c1 := K1_13_6_3_5_5_1.proof
theorem K1_13_6_3_5_5_2 : K1_13_6_3_5_5.c2 := K1_13_6_3_5_5_2.proof
theorem K1_13_6_3_5_5_3 : K1_13_6_3_5_5.c3 := K1_13_6_3_5_5_3.proof
theorem K1_13_6_3_5_5_4 : K1_13_6_3_5_5.c4 := K1_13_6_3_5_5_4.proof
theorem K1_13_6_3_5_5 : K1_13_6_3_5.c5 := K1_13_6_3_5_5.of_children Geometry.K1_13_6_3_5_5_1 Geometry.K1_13_6_3_5_5_2 Geometry.K1_13_6_3_5_5_3 Geometry.K1_13_6_3_5_5_4
theorem K1_13_6_3_5 : K1_13_6_3.c5 := K1_13_6_3_5.of_children Geometry.K1_13_6_3_5_1 Geometry.K1_13_6_3_5_2 Geometry.K1_13_6_3_5_3 Geometry.K1_13_6_3_5_4 Geometry.K1_13_6_3_5_5
theorem K1_13_6_3_6 : K1_13_6_3.c6 := K1_13_6_3_6.proof
theorem K1_13_6_3 : K1_13_6.c3 := K1_13_6_3.of_children Geometry.K1_13_6_3_1 Geometry.K1_13_6_3_2 Geometry.K1_13_6_3_3 Geometry.K1_13_6_3_4 Geometry.K1_13_6_3_5 Geometry.K1_13_6_3_6
theorem K1_13_7_1_1_1_1_1 : K1_13_7_1_1_1_1.c1 := K1_13_7_1_1_1_1_1.proof
theorem K1_13_7_1_1_1_1_2 : K1_13_7_1_1_1_1.c2 := K1_13_7_1_1_1_1_2.proof
theorem K1_13_7_1_1_1_1 : K1_13_7_1_1_1.c1 := K1_13_7_1_1_1_1.of_children Geometry.K1_13_7_1_1_1_1_1 Geometry.K1_13_7_1_1_1_1_2
theorem K1_13_7_1_1_1_2_1 : K1_13_7_1_1_1_2.c1 := K1_13_7_1_1_1_2_1.proof
theorem K1_13_7_1_1_1_2_2 : K1_13_7_1_1_1_2.c2 := K1_13_7_1_1_1_2_2.proof
theorem K1_13_7_1_1_1_2 : K1_13_7_1_1_1.c2 := K1_13_7_1_1_1_2.of_children Geometry.K1_13_7_1_1_1_2_1 Geometry.K1_13_7_1_1_1_2_2
theorem K1_13_7_1_1_1 : K1_13_7_1_1.c1 := K1_13_7_1_1_1.of_children Geometry.K1_13_7_1_1_1_1 Geometry.K1_13_7_1_1_1_2
theorem K1_13_7_1_1_2 : K1_13_7_1_1.c2 := K1_13_7_1_1_2.proof
theorem K1_13_7_1_1 : K1_13_7_1.c1 := K1_13_7_1_1.of_children Geometry.K1_13_7_1_1_1 Geometry.K1_13_7_1_1_2
theorem K1_13_7_1_2_1 : K1_13_7_1_2.c1 := K1_13_7_1_2_1.proof
theorem K1_13_7_1_2_2_1_1 : K1_13_7_1_2_2_1.c1 := K1_13_7_1_2_2_1_1.proof
theorem K1_13_7_1_2_2_1_2 : K1_13_7_1_2_2_1.c2 := K1_13_7_1_2_2_1_2.proof
theorem K1_13_7_1_2_2_1 : K1_13_7_1_2_2.c1 := K1_13_7_1_2_2_1.of_children Geometry.K1_13_7_1_2_2_1_1 Geometry.K1_13_7_1_2_2_1_2
theorem K1_13_7_1_2_2_2_1 : K1_13_7_1_2_2_2.c1 := K1_13_7_1_2_2_2_1.proof
theorem K1_13_7_1_2_2_2_2 : K1_13_7_1_2_2_2.c2 := K1_13_7_1_2_2_2_2.proof
theorem K1_13_7_1_2_2_2 : K1_13_7_1_2_2.c2 := K1_13_7_1_2_2_2.of_children Geometry.K1_13_7_1_2_2_2_1 Geometry.K1_13_7_1_2_2_2_2
theorem K1_13_7_1_2_2 : K1_13_7_1_2.c2 := K1_13_7_1_2_2.of_children Geometry.K1_13_7_1_2_2_1 Geometry.K1_13_7_1_2_2_2
theorem K1_13_7_1_2 : K1_13_7_1.c2 := K1_13_7_1_2.of_children Geometry.K1_13_7_1_2_1 Geometry.K1_13_7_1_2_2
theorem K1_13_7_2_1_1 : K1_13_7_2_1.c1 := K1_13_7_2_1_1.proof
theorem K1_13_7_2_1_2 : K1_13_7_2_1.c2 := K1_13_7_2_1_2.proof
theorem K1_13_7_2_1 : K1_13_7_2.c1 := K1_13_7_2_1.of_children Geometry.K1_13_7_2_1_1 Geometry.K1_13_7_2_1_2
theorem K1_13_7_2_2 : K1_13_7_2.c2 := K1_13_7_2_2.proof
theorem K1_13_7_2_3_1_1 : K1_13_7_2_3_1.c1 := K1_13_7_2_3_1_1.proof
theorem K1_13_7_2_3_1_2_1 : K1_13_7_2_3_1_2.c1 := K1_13_7_2_3_1_2_1.proof
theorem K1_13_7_2_3_1_2_2 : K1_13_7_2_3_1_2.c2 := K1_13_7_2_3_1_2_2.proof
theorem K1_13_7_2_3_1_2 : K1_13_7_2_3_1.c2 := K1_13_7_2_3_1_2.of_children Geometry.K1_13_7_2_3_1_2_1 Geometry.K1_13_7_2_3_1_2_2
theorem K1_13_7_2_3_1_3 : K1_13_7_2_3_1.c3 := K1_13_7_2_3_1_3.proof
theorem K1_13_7_2_3_1 : K1_13_7_2_3.c1 := K1_13_7_2_3_1.of_children Geometry.K1_13_7_2_3_1_1 Geometry.K1_13_7_2_3_1_2 Geometry.K1_13_7_2_3_1_3
theorem K1_13_7_2_3_2 : K1_13_7_2_3.c2 := K1_13_7_2_3_2.of_children Geometry.K1_13_6_1_5_2_1 Geometry.K1_13_6_1_5_2_2
theorem K1_13_7_2_3 : K1_13_7_2.c3 := K1_13_7_2_3.of_children Geometry.K1_13_7_2_3_1 Geometry.K1_13_7_2_3_2
theorem K1_13_7_2_4_1 : K1_13_7_2_4.c1 := K1_13_7_2_4_1.proof
theorem K1_13_7_2_4_2 : K1_13_7_2_4.c2 := K1_13_7_2_4_2.proof
theorem K1_13_7_2_4_3 : K1_13_7_2_4.c3 := K1_13_7_2_4_3.proof
theorem K1_13_7_2_4 : K1_13_7_2.c4 := K1_13_7_2_4.of_children Geometry.K1_13_7_2_4_1 Geometry.K1_13_7_2_4_2 Geometry.K1_13_7_2_4_3
theorem K1_13_7_2_5_1 : K1_13_7_2_5.c1 := K1_13_7_2_5_1.proof
theorem K1_13_7_2_5_2_1 : K1_13_7_2_5_2.c1 := K1_13_7_2_5_2_1.proof
theorem K1_13_7_2_5_2_2 : K1_13_7_2_5_2.c2 := K1_13_7_2_5_2_2.proof
theorem K1_13_7_2_5_2 : K1_13_7_2_5.c2 := K1_13_7_2_5_2.of_children Geometry.K1_13_7_2_5_2_1 Geometry.K1_13_7_2_5_2_2
theorem K1_13_7_2_5_3 : K1_13_7_2_5.c3 := K1_13_7_2_5_3.of_children Geometry.K1_13_6_3_5_1 Geometry.K1_13_6_3_5_2 Geometry.K1_13_6_3_5_3 Geometry.K1_13_6_3_5_4 Geometry.K1_13_6_3_5_5
theorem K1_13_7_2_5_4_1_1 : K1_13_7_2_5_4_1.c1 := K1_13_7_2_5_4_1_1.proof
theorem K1_13_7_2_5_4_1_2 : K1_13_7_2_5_4_1.c2 := K1_13_7_2_5_4_1_2.proof
theorem K1_13_7_2_5_4_1 : K1_13_7_2_5_4.c1 := K1_13_7_2_5_4_1.of_children Geometry.K1_13_7_2_5_4_1_1 Geometry.K1_13_7_2_5_4_1_2
theorem K1_13_7_2_5_4_2 : K1_13_7_2_5_4.c2 := K1_13_7_2_5_4_2.proof
theorem K1_13_7_2_5_4 : K1_13_7_2_5.c4 := K1_13_7_2_5_4.of_children Geometry.K1_13_7_2_5_4_1 Geometry.K1_13_7_2_5_4_2
theorem K1_13_7_2_5 : K1_13_7_2.c5 := K1_13_7_2_5.of_children Geometry.K1_13_7_2_5_1 Geometry.K1_13_7_2_5_2 Geometry.K1_13_7_2_5_3 Geometry.K1_13_7_2_5_4
theorem K1_13_7_3_1 : K1_13_7_3.c1 := K1_13_7_3_1.proof
theorem K1_13_7_3_2 : K1_13_7_3.c2 := K1_13_7_3_2.proof
theorem K1_13_7_3 : K1_13_7.c3 := K1_13_7_3.of_children Geometry.K1_13_7_3_1 Geometry.K1_13_7_3_2
theorem K1_13_7_4_1 : K1_13_7_4.c1 := K1_13_7_4_1.proof
theorem K1_13_7_4_2_1 : K1_13_7_4_2.c1 := K1_13_7_4_2_1.proof
theorem K1_13_7_4_2_2 : K1_13_7_4_2.c2 := K1_13_7_4_2_2.proof
theorem K1_13_7_4_2 : K1_13_7_4.c2 := K1_13_7_4_2.of_children Geometry.K1_13_7_4_2_1 Geometry.K1_13_7_4_2_2
theorem K1_13_7_4 : K1_13_7.c4 := K1_13_7_4.of_children Geometry.K1_13_7_4_1 Geometry.K1_13_7_4_2
theorem K1_13_7_5_1 : K1_13_7_5.c1 := K1_13_7_5_1.proof
theorem K1_13_7_5_2 : K1_13_7_5.c2 := K1_13_7_5_2.proof
theorem K1_13_7_5_3_1_1 : K1_13_7_5_3_1.c1 := K1_13_7_5_3_1_1.proof
theorem K1_13_7_5_3_1_2 : K1_13_7_5_3_1.c2 := K1_13_7_5_3_1_2.proof
theorem K1_13_7_5_3_1 : K1_13_7_5_3.c1 := K1_13_7_5_3_1.of_children Geometry.K1_13_7_5_3_1_1 Geometry.K1_13_7_5_3_1_2
theorem K1_13_7_5_3_2 : K1_13_7_5_3.c2 := K1_13_7_5_3_2.proof
theorem K1_13_7_5_3_3_1 : K1_13_7_5_3_3.c1 := K1_13_7_5_3_3_1.proof
theorem K1_13_7_5_3_3_2_1 : K1_13_7_5_3_3_2.c1 := K1_13_7_5_3_3_2_1.proof
theorem K1_13_7_5_3_3_2_2 : K1_13_7_5_3_3_2.c2 := K1_13_7_5_3_3_2_2.proof
theorem K1_13_7_5_3_3_2 : K1_13_7_5_3_3.c2 := K1_13_7_5_3_3_2.of_children Geometry.K1_13_7_5_3_3_2_1 Geometry.K1_13_7_5_3_3_2_2
theorem K1_13_7_5_3_3_3_1 : K1_13_7_5_3_3_3.c1 := K1_13_7_5_3_3_3_1.proof
theorem K1_13_7_5_3_3_3_2 : K1_13_7_5_3_3_3.c2 := K1_13_7_5_3_3_3_2.proof
theorem K1_13_7_5_3_3_3 : K1_13_7_5_3_3.c3 := K1_13_7_5_3_3_3.of_children Geometry.K1_13_7_5_3_3_3_1 Geometry.K1_13_7_5_3_3_3_2
theorem K1_13_7_5_3_3_4 : K1_13_7_5_3_3.c4 := K1_13_7_5_3_3_4.proof
theorem K1_13_7_5_3_3 : K1_13_7_5_3.c3 := K1_13_7_5_3_3.of_children Geometry.K1_13_7_5_3_3_1 Geometry.K1_13_7_5_3_3_2 Geometry.K1_13_7_5_3_3_3 Geometry.K1_13_7_5_3_3_4
theorem K1_13_7_5_3_4 : K1_13_7_5_3.c4 := K1_13_7_5_3_4.proof
theorem K1_13_7_5_3 : K1_13_7_5.c3 := K1_13_7_5_3.of_children Geometry.K1_13_7_5_3_1 Geometry.K1_13_7_5_3_2 Geometry.K1_13_7_5_3_3 Geometry.K1_13_7_5_3_4
theorem K1_13_7_6_1 : K1_13_7_6.c1 := K1_13_7_6_1.proof
theorem K1_13_7_6_2_1 : K1_13_7_6_2.c1 := K1_13_7_6_2_1.proof
theorem K1_13_7_6_2_2 : K1_13_7_6_2.c2 := K1_13_7_6_2_2.proof
theorem K1_13_7_6_2 : K1_13_7_6.c2 := K1_13_7_6_2.of_children Geometry.K1_13_7_6_2_1 Geometry.K1_13_7_6_2_2
theorem K1_13_7_6 : K1_13_7.c6 := K1_13_7_6.of_children Geometry.K1_13_7_6_1 Geometry.K1_13_7_6_2

end LowPrice6921.Geometry
