import ProximityPrize.SubmissionLower.Koala6844TerminalEndpointMeta
import ProximityPrize.SubmissionLower.Koala6844ReceiptsEndpoints

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 60000

private theorem checkedBlock00 : endpointBlock00.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock01 : endpointBlock01.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock02 : endpointBlock02.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock03 : endpointBlock03.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock04 : endpointBlock04.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock05 : endpointBlock05.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock06 : endpointBlock06.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock07 : endpointBlock07.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock08 : endpointBlock08.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock09 : endpointBlock09.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock10 : endpointBlock10.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock11 : endpointBlock11.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock12 : endpointBlock12.all terminalMetadata = true := by
  decide +kernel

private theorem checkedBlock13 : endpointBlock13.all terminalMetadata = true := by
  decide +kernel

theorem terminal_endpoints_metadata (e : CertifiedEndpoint) (he : e ∈ terminalEndpoints) :
    terminalMetadata e = true := by
  have h : terminalEndpoints.all terminalMetadata = true := by
    simp only [terminalEndpoints,List.all_append,checkedBlock00, checkedBlock01, checkedBlock02, checkedBlock03, checkedBlock04, checkedBlock05, checkedBlock06, checkedBlock07, checkedBlock08, checkedBlock09, checkedBlock10, checkedBlock11, checkedBlock12, checkedBlock13] <;> decide
  exact (List.all_eq_true.mp h) e he

end ProximityPrize.SubmissionLower.Koala6844Receipts
