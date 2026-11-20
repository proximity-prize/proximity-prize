/- Apache-2.0. Bome2017. Connect the finite incidence and partition certificates
   to the original KoalaBear hard family. Built on Lucieno and BitWonka. -/
import ProximityPrize.SubmissionLower.JointProtocol6836
import ProximityPrize.SubmissionLower.ActualBudget6836
import ProximityPrize.SubmissionLower.Night6836PhysicalPrice
import ProximityPrize.SubmissionLower.Night6836RoomBridge
namespace ProximityPrize.SubmissionLower.KoalaOriginal6836
open ProximityPrize.Benchmark Genuine6969
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 30000

theorem original_slabs : Night6836Terminal.SlabBudget := by
  apply family_of_prices
  intro H Γ sel u v D live p r e z pos eq cap
  let _ : CharP F 2130706433 := Koala6831BenchmarkField.characteristic
  exact Night6836PhysicalPrice.factor_bounds live p pos eq cap

theorem protocol : ProtocolClaim 6836 332210175 1073741824 :=
  JointProtocol6836.protocol_of_joint_short (Night6836Terminal.short_of_slabs original_slabs)
#print axioms original_slabs
#print axioms protocol
end
end ProximityPrize.SubmissionLower.KoalaOriginal6836
