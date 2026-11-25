import ProximityPrize.SubmissionLower.R6966ProofHelperRescueChecked0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueChecked1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueChecked2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueChecked3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueChecked4

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem route0 (stage : Fin 17) : Checked (request 0 stage) := by
  fin_cases stage
  · exact step0_verified
  · exact step1_verified
  · exact step2_verified
  · exact step3_verified
  · exact step4_verified
  · exact step5_verified
  · exact step6_verified
  · exact step7_verified
  · exact step8_verified
  · exact step7_verified
  · exact step9_verified
  · exact step11_verified
  · exact step10_verified
  · exact step12_verified
  · exact step12_verified
  · exact step12_verified
  · exact step12_verified
#print axioms route0

theorem route1 (stage : Fin 17) : Checked (request 1 stage) := by
  fin_cases stage
  · exact step13_verified
  · exact step14_verified
  · exact step15_verified
  · exact step16_verified
  · exact step17_verified
  · exact step18_verified
  · exact step19_verified
  · exact step20_verified
  · exact step21_verified
  · exact step20_verified
  · exact step22_verified
  · exact step24_verified
  · exact step23_verified
  · exact step25_verified
  · exact step25_verified
  · exact step25_verified
  · exact step25_verified
#print axioms route1

theorem route2 (stage : Fin 17) : Checked (request 2 stage) := by
  fin_cases stage
  · exact step26_verified
  · exact step27_verified
  · exact step28_verified
  · exact step29_verified
  · exact step30_verified
  · exact step31_verified
  · exact step32_verified
  · exact step33_verified
  · exact step34_verified
  · exact step33_verified
  · exact step35_verified
  · exact step37_verified
  · exact step36_verified
  · exact step38_verified
  · exact step38_verified
  · exact step38_verified
  · exact step38_verified
#print axioms route2

theorem route3 (stage : Fin 17) : Checked (request 3 stage) := by
  fin_cases stage
  · exact step39_verified
  · exact step40_verified
  · exact step41_verified
  · exact step42_verified
  · exact step43_verified
  · exact step44_verified
  · exact step45_verified
  · exact step46_verified
  · exact step47_verified
  · exact step46_verified
  · exact step48_verified
  · exact step50_verified
  · exact step49_verified
  · exact step51_verified
  · exact step51_verified
  · exact step51_verified
  · exact step51_verified
#print axioms route3

theorem route4 (stage : Fin 17) : Checked (request 4 stage) := by
  fin_cases stage
  · exact step52_verified
  · exact step53_verified
  · exact step54_verified
  · exact step55_verified
  · exact step56_verified
  · exact step57_verified
  · exact step58_verified
  · exact step59_verified
  · exact step60_verified
  · exact step59_verified
  · exact step61_verified
  · exact step63_verified
  · exact step62_verified
  · exact step64_verified
  · exact step65_verified
  · exact step66_verified
  · exact step67_verified
#print axioms route4

theorem route5 (stage : Fin 17) : Checked (request 5 stage) := by
  fin_cases stage
  · exact step68_verified
  · exact step69_verified
  · exact step70_verified
  · exact step71_verified
  · exact step72_verified
  · exact step73_verified
  · exact step74_verified
  · exact step75_verified
  · exact step76_verified
  · exact step75_verified
  · exact step77_verified
  · exact step79_verified
  · exact step78_verified
  · exact step80_verified
  · exact step80_verified
  · exact step80_verified
  · exact step80_verified
#print axioms route5

end Research6966.HelperRescueCatalogue
