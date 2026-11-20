import ProximityPrize.SubmissionLower.Koala6844ReceiptsEndpoints
import ProximityPrize.SubmissionLower.Koala6844ReceiptsTerminalFlagReference


namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 3000000

private theorem endpointBlock00_flags :
    endpointBlock00.map CertifiedEndpoint.flag = terminalFlagReference00 := rfl

private theorem endpointBlock01_flags :
    endpointBlock01.map CertifiedEndpoint.flag = terminalFlagReference01 := rfl

private theorem endpointBlock02_flags :
    endpointBlock02.map CertifiedEndpoint.flag = terminalFlagReference02 := rfl

private theorem endpointBlock03_flags :
    endpointBlock03.map CertifiedEndpoint.flag = terminalFlagReference03 := rfl

private theorem endpointBlock04_flags :
    endpointBlock04.map CertifiedEndpoint.flag = terminalFlagReference04 := rfl

private theorem endpointBlock05_flags :
    endpointBlock05.map CertifiedEndpoint.flag = terminalFlagReference05 := rfl

private theorem endpointBlock06_flags :
    endpointBlock06.map CertifiedEndpoint.flag = terminalFlagReference06 := rfl

private theorem endpointBlock07_flags :
    endpointBlock07.map CertifiedEndpoint.flag = terminalFlagReference07 := rfl

private theorem endpointBlock08_flags :
    endpointBlock08.map CertifiedEndpoint.flag = terminalFlagReference08 := rfl

private theorem endpointBlock09_flags :
    endpointBlock09.map CertifiedEndpoint.flag = terminalFlagReference09 := rfl

private theorem endpointBlock10_flags :
    endpointBlock10.map CertifiedEndpoint.flag = terminalFlagReference10 := rfl

private theorem endpointBlock11_flags :
    endpointBlock11.map CertifiedEndpoint.flag = terminalFlagReference11 := rfl

private theorem endpointBlock12_flags :
    endpointBlock12.map CertifiedEndpoint.flag = terminalFlagReference12 := rfl

private theorem endpointBlock13_flags :
    endpointBlock13.map CertifiedEndpoint.flag = terminalFlagReference13 := rfl

theorem terminalEndpoints_flags :
    terminalEndpoints.map CertifiedEndpoint.flag = terminalFlagReference := by
  simp only [terminalEndpoints,terminalFlagReference,List.map_append,
    endpointBlock00_flags,
    endpointBlock01_flags,
    endpointBlock02_flags,
    endpointBlock03_flags,
    endpointBlock04_flags,
    endpointBlock05_flags,
    endpointBlock06_flags,
    endpointBlock07_flags,
    endpointBlock08_flags,
    endpointBlock09_flags,
    endpointBlock10_flags,
    endpointBlock11_flags,
    endpointBlock12_flags,
    endpointBlock13_flags]


end ProximityPrize.SubmissionLower.Koala6844Receipts
