import ProximityPrize.SubmissionLower.FrontCore82258Model
import ProximityPrize.SubmissionLower.UpperBranch6
import ProximityPrize.SubmissionLower.KoalaRectCutoff
import ProximityPrize.SubmissionLower.R6960TerminalReceipts
import ProximityPrize.SubmissionLower.R6966ProofFarChart
import ProximityPrize.SubmissionLower.R6960RetainedSurfaceClass
import ProximityPrize.SubmissionLower.R6960RetainedCrossingLift
import ProximityPrize.SubmissionLower.R6960MarkedProtocol
import ProximityPrize.SubmissionLower.R6960RetainedCompressionPureNodes
import ProximityPrize.SubmissionLower.Z6969Pack0424
import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks
import ProximityPrize.SubmissionLower.R6960RescueGeometryBills
import ProximityPrize.SubmissionLower.HighCore82258PrefixProcess
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.R6960MarkedEvaluationLedger
import ProximityPrize.SubmissionLower.R6960TerminalDegrees
import ProximityPrize.SubmissionLower.Z6969Pack0724
import ProximityPrize.SubmissionLower.Z6969Pack0760
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0720
import ProximityPrize.SubmissionLower.Z6969Pack0669
import ProximityPrize.SubmissionLower.Z6969Pack0671
import ProximityPrize.SubmissionLower.Z6969Pack0672
import ProximityPrize.SubmissionLower.Z6969Pack0673
import ProximityPrize.SubmissionLower.Z6969Pack0674
import ProximityPrize.SubmissionLower.Z6969Pack0676
import ProximityPrize.SubmissionLower.Z6969Pack0677
import ProximityPrize.SubmissionLower.Z6969Pack0678
import ProximityPrize.SubmissionLower.Z6969Pack0679
import ProximityPrize.SubmissionLower.Z6969Pack0681
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0683
import ProximityPrize.SubmissionLower.Z6969Pack0684
import ProximityPrize.SubmissionLower.Z6969Pack0686
import ProximityPrize.SubmissionLower.Z6969Pack0687
import ProximityPrize.SubmissionLower.Z6969Pack0688
import ProximityPrize.SubmissionLower.Z6969Pack0689
import ProximityPrize.SubmissionLower.Z6969Pack0700

set_option Elab.async false

-- Source: Research6969.HighEndpoint
section Z6969Source2541
set_option autoImplicit true
namespace Research6969.HighEndpoint
open Lower6960
open Far6969RescueGeometry (Model Family)
open K1_14_1 (poleProduct nodeL)
open ProximityPrize.Benchmark
open Polynomial

/-- Everything outside the selected large-degree normal packets is
discharged on the concrete lower-track model. -/
theorem count (high:HighPackets.Goal) {u del} (M:Model u del) {Γ}
    (F:Family M Γ) (lo:2314≤M.overhead) (hi:M.overhead≤2411):
    Γ.card≤274779381266040419 := by
  obtain ⟨D,⟨Crt⟩,safe,res⟩:=Far6969PoleChart.of_family M F
  obtain ⟨out⟩:=Prefix6969Early.route F Crt (by omega) (by omega) safe res
  exact HighPackets.from_outcome high F Crt (by omega) (by omega) (fun i=>by
    change (poleProduct D).eval (nodeL i)≠0
    rw [poleProduct,eval_mul];exact mul_ne_zero (safe 0 i) (safe 1 i)) res out

end Research6969.HighEndpoint
end Z6969Source2541

-- Source: Research6969.FinalCoverage
section Z6969Source2542
set_option autoImplicit true
namespace Research6969.FinalCoverage
open ProximityPrize.Benchmark
structure Remaining : Prop where
  seed1:HighPendingSeed1.Required
  seed2:HighPendingSeed2.Required
  seed3:HighPendingSeed3.Required
  seed4:HighPendingSeed4.Required
  seed5:HighPendingSeed5.Required
  seed6:HighPendingSeed6.Required
  seed7:HighPendingSeed7.Required
  seed8:HighPendingSeed8.Required
  seed9:HighPendingSeed9.Required
  seed10:HighPendingSeed10.Required
  seed11:HighPendingSeed11.Required
  seed12:HighPendingSeed12.Required
  seed13:HighPendingSeed13.Required
  seed14:HighPendingSeed14.Required
  seed15:HighPendingSeed15.Required
  seed16:HighPendingSeed16.Required
  seed17:HighPendingSeed17.Required
  seed18:HighPendingSeed18.Required

theorem high (proof:Remaining):HighPackets.Goal:=by
  intro i
  fin_cases i
  · exact HighDispatchSeed1.count proof.seed1
  · exact HighDispatchSeed2.count proof.seed2
  · exact HighDispatchSeed3.count proof.seed3
  · exact HighDispatchSeed4.count proof.seed4
  · exact HighDispatchSeed5.count proof.seed5
  · exact HighDispatchSeed6.count proof.seed6
  · exact HighDispatchSeed7.count proof.seed7
  · exact HighDispatchSeed8.count proof.seed8
  · exact HighDispatchSeed9.count proof.seed9
  · exact HighDispatchSeed10.count proof.seed10
  · exact HighDispatchSeed11.count proof.seed11
  · exact HighDispatchSeed12.count proof.seed12
  · exact HighDispatchSeed13.count proof.seed13
  · exact HighDispatchSeed14.count proof.seed14
  · exact HighDispatchSeed15.count proof.seed15
  · exact HighDispatchSeed16.count proof.seed16
  · exact HighDispatchSeed17.count proof.seed17
  · exact HighDispatchSeed18.count proof.seed18

theorem count (proof:Remaining) {u del}
    (M:Lower6960.Far6969RescueGeometry.Model u del) {Γ}
    (F:Lower6960.Far6969RescueGeometry.Family M Γ)
    (lo:2314≤M.overhead) (hi:M.overhead≤2557) : Γ.card≤274779381266040419 := by
  by_cases early : M.overhead≤2411
  · exact HighEndpoint.count (high proof) M F lo early
  · exact MiddleBand.count M F (by omega) hi

end Research6969.FinalCoverage
end Z6969Source2542
