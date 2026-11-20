import ProximityPrize.SubmissionLower.Koala6844ReceiptsEndpointCover
import ProximityPrize.SubmissionLower.Koala6844ReceiptsBandProof

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem terminalGate_24_stop :
    bandCovers secondAdaptiveFlag ⟨24, 37, 37⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 37, 37⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_24 :
    bandCovers secondAdaptiveFlag ⟨24, 24, 710⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 24, 710⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_25 :
    bandCovers secondAdaptiveFlag ⟨24, 25, 662⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 25, 662⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_26 :
    bandCovers secondAdaptiveFlag ⟨24, 26, 612⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 26, 612⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_27 :
    bandCovers secondAdaptiveFlag ⟨24, 27, 563⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 27, 563⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_28 :
    bandCovers secondAdaptiveFlag ⟨24, 28, 512⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 28, 512⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_29 :
    bandCovers secondAdaptiveFlag ⟨24, 29, 462⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 29, 462⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_30 :
    bandCovers secondAdaptiveFlag ⟨24, 30, 410⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 30, 410⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_31 :
    bandCovers secondAdaptiveFlag ⟨24, 31, 358⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 31, 358⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_32 :
    bandCovers secondAdaptiveFlag ⟨24, 32, 305⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 32, 305⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_33 :
    bandCovers secondAdaptiveFlag ⟨24, 33, 252⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 33, 252⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_34 :
    bandCovers secondAdaptiveFlag ⟨24, 34, 198⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 34, 198⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_35 :
    bandCovers secondAdaptiveFlag ⟨24, 35, 144⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 35, 144⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_24_36 :
    bandCovers secondAdaptiveFlag ⟨24, 36, 88⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨24, 36, 88⟩ secondAdaptiveGap
    [⟨770, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape24 : TerminalSlopeTape 24 24 :=  TerminalSlopeTape.row (r := 24) (y := 24) 709 (by decide) terminalGate_24_24 (
  TerminalSlopeTape.row (r := 24) (y := 25) 661 (by decide) terminalGate_24_25 (
  TerminalSlopeTape.row (r := 24) (y := 26) 611 (by decide) terminalGate_24_26 (
  TerminalSlopeTape.row (r := 24) (y := 27) 562 (by decide) terminalGate_24_27 (
  TerminalSlopeTape.row (r := 24) (y := 28) 511 (by decide) terminalGate_24_28 (
  TerminalSlopeTape.row (r := 24) (y := 29) 461 (by decide) terminalGate_24_29 (
  TerminalSlopeTape.row (r := 24) (y := 30) 409 (by decide) terminalGate_24_30 (
  TerminalSlopeTape.row (r := 24) (y := 31) 357 (by decide) terminalGate_24_31 (
  TerminalSlopeTape.row (r := 24) (y := 32) 304 (by decide) terminalGate_24_32 (
  TerminalSlopeTape.row (r := 24) (y := 33) 251 (by decide) terminalGate_24_33 (
  TerminalSlopeTape.row (r := 24) (y := 34) 197 (by decide) terminalGate_24_34 (
  TerminalSlopeTape.row (r := 24) (y := 35) 143 (by decide) terminalGate_24_35 (
  TerminalSlopeTape.row (r := 24) (y := 36) 87 (by decide) terminalGate_24_36 (
  TerminalSlopeTape.stop (r := 24) (y := 37) terminalGate_24_stop)))))))))))))

private theorem terminalGate_25_stop :
    bandCovers secondAdaptiveFlag ⟨25, 28, 28⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨25, 28, 28⟩ secondAdaptiveGap
    [⟨739, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_25_25 :
    bandCovers secondAdaptiveFlag ⟨25, 25, 142⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨25, 25, 142⟩ secondAdaptiveGap
    [⟨739, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_25_26 :
    bandCovers secondAdaptiveFlag ⟨25, 26, 90⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨25, 26, 90⟩ secondAdaptiveGap
    [⟨739, true, true⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_25_27 :
    bandCovers secondAdaptiveFlag ⟨25, 27, 38⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨25, 27, 38⟩ secondAdaptiveGap
    [⟨739, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape25 : TerminalSlopeTape 25 25 :=  TerminalSlopeTape.row (r := 25) (y := 25) 141 (by decide) terminalGate_25_25 (
  TerminalSlopeTape.row (r := 25) (y := 26) 89 (by decide) terminalGate_25_26 (
  TerminalSlopeTape.row (r := 25) (y := 27) 37 (by decide) terminalGate_25_27 (
  TerminalSlopeTape.stop (r := 25) (y := 28) terminalGate_25_stop)))

private theorem terminalGate_26_stop :
    bandCovers secondAdaptiveFlag ⟨26, 26, 26⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨26, 26, 26⟩ secondAdaptiveGap
    [⟨710, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape26 : TerminalSlopeTape 26 26 :=
  TerminalSlopeTape.stop (r := 26) (y := 26) terminalGate_26_stop

private theorem terminalGate_27_stop :
    bandCovers secondAdaptiveFlag ⟨27, 27, 27⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨27, 27, 27⟩ secondAdaptiveGap
    [⟨684, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape27 : TerminalSlopeTape 27 27 :=
  TerminalSlopeTape.stop (r := 27) (y := 27) terminalGate_27_stop

private theorem terminalGate_28_stop :
    bandCovers secondAdaptiveFlag ⟨28, 28, 28⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨28, 28, 28⟩ secondAdaptiveGap
    [⟨660, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape28 : TerminalSlopeTape 28 28 :=
  TerminalSlopeTape.stop (r := 28) (y := 28) terminalGate_28_stop

private theorem terminalGate_29_stop :
    bandCovers secondAdaptiveFlag ⟨29, 29, 29⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨29, 29, 29⟩ secondAdaptiveGap
    [⟨637, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape29 : TerminalSlopeTape 29 29 :=
  TerminalSlopeTape.stop (r := 29) (y := 29) terminalGate_29_stop

private theorem terminalGate_30_stop :
    bandCovers secondAdaptiveFlag ⟨30, 30, 30⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨30, 30, 30⟩ secondAdaptiveGap
    [⟨616, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape30 : TerminalSlopeTape 30 30 :=
  TerminalSlopeTape.stop (r := 30) (y := 30) terminalGate_30_stop

private theorem terminalGate_31_stop :
    bandCovers secondAdaptiveFlag ⟨31, 31, 31⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨31, 31, 31⟩ secondAdaptiveGap
    [⟨596, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape31 : TerminalSlopeTape 31 31 :=
  TerminalSlopeTape.stop (r := 31) (y := 31) terminalGate_31_stop

private theorem terminalGate_32_stop :
    bandCovers secondAdaptiveFlag ⟨32, 32, 32⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨32, 32, 32⟩ secondAdaptiveGap
    [⟨577, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape32 : TerminalSlopeTape 32 32 :=
  TerminalSlopeTape.stop (r := 32) (y := 32) terminalGate_32_stop

private theorem terminalGate_33_stop :
    bandCovers secondAdaptiveFlag ⟨33, 33, 33⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨33, 33, 33⟩ secondAdaptiveGap
    [⟨560, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape33 : TerminalSlopeTape 33 33 :=
  TerminalSlopeTape.stop (r := 33) (y := 33) terminalGate_33_stop

private theorem terminalGate_34_stop :
    bandCovers secondAdaptiveFlag ⟨34, 34, 34⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨34, 34, 34⟩ secondAdaptiveGap
    [⟨543, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape34 : TerminalSlopeTape 34 34 :=
  TerminalSlopeTape.stop (r := 34) (y := 34) terminalGate_34_stop

private theorem terminalGate_35_stop :
    bandCovers secondAdaptiveFlag ⟨35, 35, 35⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨35, 35, 35⟩ secondAdaptiveGap
    [⟨528, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape35 : TerminalSlopeTape 35 35 :=
  TerminalSlopeTape.stop (r := 35) (y := 35) terminalGate_35_stop

private theorem terminalGate_36_stop :
    bandCovers secondAdaptiveFlag ⟨36, 36, 36⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨36, 36, 36⟩ secondAdaptiveGap
    [⟨513, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape36 : TerminalSlopeTape 36 36 :=
  TerminalSlopeTape.stop (r := 36) (y := 36) terminalGate_36_stop

private theorem terminalGate_37_stop :
    bandCovers secondAdaptiveFlag ⟨37, 37, 37⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨37, 37, 37⟩ secondAdaptiveGap
    [⟨499, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape37 : TerminalSlopeTape 37 37 :=
  TerminalSlopeTape.stop (r := 37) (y := 37) terminalGate_37_stop

private theorem terminalGate_38_stop :
    bandCovers secondAdaptiveFlag ⟨38, 38, 38⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨38, 38, 38⟩ secondAdaptiveGap
    [⟨486, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape38 : TerminalSlopeTape 38 38 :=
  TerminalSlopeTape.stop (r := 38) (y := 38) terminalGate_38_stop

private theorem terminalGate_39_stop :
    bandCovers secondAdaptiveFlag ⟨39, 39, 39⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨39, 39, 39⟩ secondAdaptiveGap
    [⟨473, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape39 : TerminalSlopeTape 39 39 :=
  TerminalSlopeTape.stop (r := 39) (y := 39) terminalGate_39_stop

private theorem terminalGate_40_stop :
    bandCovers secondAdaptiveFlag ⟨40, 40, 40⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨40, 40, 40⟩ secondAdaptiveGap
    [⟨462, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape40 : TerminalSlopeTape 40 40 :=
  TerminalSlopeTape.stop (r := 40) (y := 40) terminalGate_40_stop

private theorem terminalGate_41_stop :
    bandCovers secondAdaptiveFlag ⟨41, 41, 41⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨41, 41, 41⟩ secondAdaptiveGap
    [⟨450, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape41 : TerminalSlopeTape 41 41 :=
  TerminalSlopeTape.stop (r := 41) (y := 41) terminalGate_41_stop

private theorem terminalGate_42_stop :
    bandCovers secondAdaptiveFlag ⟨42, 42, 42⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨42, 42, 42⟩ secondAdaptiveGap
    [⟨440, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape42 : TerminalSlopeTape 42 42 :=
  TerminalSlopeTape.stop (r := 42) (y := 42) terminalGate_42_stop

private theorem terminalGate_43_stop :
    bandCovers secondAdaptiveFlag ⟨43, 43, 43⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨43, 43, 43⟩ secondAdaptiveGap
    [⟨429, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape43 : TerminalSlopeTape 43 43 :=
  TerminalSlopeTape.stop (r := 43) (y := 43) terminalGate_43_stop

private theorem terminalGate_44_stop :
    bandCovers secondAdaptiveFlag ⟨44, 44, 44⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨44, 44, 44⟩ secondAdaptiveGap
    [⟨420, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape44 : TerminalSlopeTape 44 44 :=
  TerminalSlopeTape.stop (r := 44) (y := 44) terminalGate_44_stop

private theorem terminalGate_45_stop :
    bandCovers secondAdaptiveFlag ⟨45, 45, 45⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨45, 45, 45⟩ secondAdaptiveGap
    [⟨410, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape45 : TerminalSlopeTape 45 45 :=
  TerminalSlopeTape.stop (r := 45) (y := 45) terminalGate_45_stop

private theorem terminalGate_46_stop :
    bandCovers secondAdaptiveFlag ⟨46, 46, 46⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨46, 46, 46⟩ secondAdaptiveGap
    [⟨401, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape46 : TerminalSlopeTape 46 46 :=
  TerminalSlopeTape.stop (r := 46) (y := 46) terminalGate_46_stop

private theorem terminalGate_47_stop :
    bandCovers secondAdaptiveFlag ⟨47, 47, 47⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨47, 47, 47⟩ secondAdaptiveGap
    [⟨393, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape47 : TerminalSlopeTape 47 47 :=
  TerminalSlopeTape.stop (r := 47) (y := 47) terminalGate_47_stop

private theorem terminalGate_48_stop :
    bandCovers secondAdaptiveFlag ⟨48, 48, 48⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨48, 48, 48⟩ secondAdaptiveGap
    [⟨385, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape48 : TerminalSlopeTape 48 48 :=
  TerminalSlopeTape.stop (r := 48) (y := 48) terminalGate_48_stop

private theorem terminalGate_49_stop :
    bandCovers secondAdaptiveFlag ⟨49, 49, 49⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨49, 49, 49⟩ secondAdaptiveGap
    [⟨377, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape49 : TerminalSlopeTape 49 49 :=
  TerminalSlopeTape.stop (r := 49) (y := 49) terminalGate_49_stop

private theorem terminalGate_50_stop :
    bandCovers secondAdaptiveFlag ⟨50, 50, 50⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨50, 50, 50⟩ secondAdaptiveGap
    [⟨369, true, true⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape50 : TerminalSlopeTape 50 50 :=
  TerminalSlopeTape.stop (r := 50) (y := 50) terminalGate_50_stop

def terminalTapeGroup08 : List TerminalCoveredSlope := [
  ⟨24, terminalSlopeTape24⟩,
  ⟨25, terminalSlopeTape25⟩,
  ⟨26, terminalSlopeTape26⟩,
  ⟨27, terminalSlopeTape27⟩,
  ⟨28, terminalSlopeTape28⟩,
  ⟨29, terminalSlopeTape29⟩,
  ⟨30, terminalSlopeTape30⟩,
  ⟨31, terminalSlopeTape31⟩,
  ⟨32, terminalSlopeTape32⟩,
  ⟨33, terminalSlopeTape33⟩,
  ⟨34, terminalSlopeTape34⟩,
  ⟨35, terminalSlopeTape35⟩,
  ⟨36, terminalSlopeTape36⟩,
  ⟨37, terminalSlopeTape37⟩,
  ⟨38, terminalSlopeTape38⟩,
  ⟨39, terminalSlopeTape39⟩,
  ⟨40, terminalSlopeTape40⟩,
  ⟨41, terminalSlopeTape41⟩,
  ⟨42, terminalSlopeTape42⟩,
  ⟨43, terminalSlopeTape43⟩,
  ⟨44, terminalSlopeTape44⟩,
  ⟨45, terminalSlopeTape45⟩,
  ⟨46, terminalSlopeTape46⟩,
  ⟨47, terminalSlopeTape47⟩,
  ⟨48, terminalSlopeTape48⟩,
  ⟨49, terminalSlopeTape49⟩,
  ⟨50, terminalSlopeTape50⟩
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
