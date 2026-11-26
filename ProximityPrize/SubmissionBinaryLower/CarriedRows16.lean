import ProximityPrize.SubmissionBinaryLower.CarriedRows15
open ProximityPrize.SubmissionBinaryLower B6402BucketBudget B6402GridRouting Native6402Grid
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace Binary6402Dispatch
open Binary6402Carried
theorem C236_1 : Ordinary (key 236) 1 := ⟨carried236,carried236_ok,by decide +kernel,by decide +kernel⟩
theorem C236_2 : Ordinary (key 236) 2 := ⟨carried236,carried236_ok,by decide +kernel,by decide +kernel⟩
end Binary6402Dispatch
