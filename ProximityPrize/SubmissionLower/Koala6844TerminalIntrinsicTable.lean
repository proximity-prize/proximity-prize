import ProximityPrize.SubmissionLower.Koala6844TerminalIntrinsic
import ProximityPrize.SubmissionLower.Koala6844ReceiptsEndpoints


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 60000
set_option Elab.async false

private theorem intrinsicBlock00 : endpointBlock00.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock01 : endpointBlock01.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock02 : endpointBlock02.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock03 : endpointBlock03.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock04 : endpointBlock04.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock05 : endpointBlock05.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock06 : endpointBlock06.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock07 : endpointBlock07.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock08 : endpointBlock08.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock09 : endpointBlock09.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock10 : endpointBlock10.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock11 : endpointBlock11.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock12 : endpointBlock12.all intrinsicRawMetadata = true := by
  decide +kernel

private theorem intrinsicBlock13 : endpointBlock13.all intrinsicRawMetadata = true := by
  decide +kernel

theorem terminal_endpoints_intrinsic_raw (e : CertifiedEndpoint) (he : e ∈ terminalEndpoints) :
    intrinsicRawMetadata e = true := by
  apply (List.all_eq_true.mp ?_) e he
  simp only [terminalEndpoints,List.all_append,
    intrinsicBlock00, intrinsicBlock01, intrinsicBlock02, intrinsicBlock03, intrinsicBlock04, intrinsicBlock05, intrinsicBlock06,
    intrinsicBlock07, intrinsicBlock08, intrinsicBlock09, intrinsicBlock10, intrinsicBlock11, intrinsicBlock12, intrinsicBlock13]
  decide

end ProximityPrize.SubmissionLower.Koala6844Terminal
