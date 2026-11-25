import ProximityPrize.SubmissionLower.R6966ProofHelperRescueRoutes0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueRoutes1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueRoutes2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueRoutes3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueRoutes4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueRoutes5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueRoutes6
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueRoutes7
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueRoutes8
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSelection

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem all_verified (r : Fin 54) : ∀ i, Checked (request r i) := by
  fin_cases r
  · exact route0
  · exact route1
  · exact route2
  · exact route3
  · exact route4
  · exact route5
  · exact route6
  · exact route7
  · exact route8
  · exact route9
  · exact route10
  · exact route11
  · exact route12
  · exact route13
  · exact route14
  · exact route15
  · exact route16
  · exact route17
  · exact route18
  · exact route19
  · exact route20
  · exact route21
  · exact route22
  · exact route23
  · exact route24
  · exact route25
  · exact route26
  · exact route27
  · exact route28
  · exact route29
  · exact route30
  · exact route31
  · exact route32
  · exact route33
  · exact route34
  · exact route35
  · exact route36
  · exact route37
  · exact route38
  · exact route39
  · exact route40
  · exact route41
  · exact route42
  · exact route43
  · exact route44
  · exact route45
  · exact route46
  · exact route47
  · exact route48
  · exact route49
  · exact route50
  · exact route51
  · exact route52
  · exact route53

abbrev rescue (r : Fin 54) := @HelperRescueSource.prepare r (all_verified r)

abbrev avoiding (r : Fin 54) := @HelperRescueSource.avoiding_rows r (all_verified r)

abbrev selected := @HelperRescueSelection.prepare_selected all_verified

#print axioms all_verified
#print axioms rescue
#print axioms avoiding
#print axioms selected
end Research6966.HelperRescueCatalogue
