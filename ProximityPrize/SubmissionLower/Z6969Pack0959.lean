import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0671
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0954
import ProximityPrize.SubmissionLower.Z6969Pack0955
import ProximityPrize.SubmissionLower.Z6969Pack0953
import ProximityPrize.SubmissionLower.Z6969Pack0956
import ProximityPrize.SubmissionLower.Z6969Pack0957
import ProximityPrize.SubmissionLower.Z6969Pack0958

set_option Elab.async false

-- Source: Research6969.HardFit3At140
set_option autoImplicit true
namespace Research6969.HardFit3At140
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes31:PairRoute.Done (2:Fin 18) ⟨⟨50,50,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6420 1),
    (PairReceipts.route6420 2),
    (PairReceipts.route6420 3),
    (PairReceipts.route6420 4),
    (PairReceipts.route6420 5),
    (PairReceipts.route6420 6),
    (PairReceipts.route6420 7),
    (PairReceipts.route6420 8),
    (PairReceipts.route6420 9),
    (PairReceipts.route6420 10),
    PairLeaves.three PairReceipts.cell6436 PairReceipts.check6436 (by decide) (none),
    PairLeaves.three PairReceipts.cell6437 PairReceipts.check6437 (by decide) (none),
    PairLeaves.three PairReceipts.cell6438 PairReceipts.check6438 (by decide) (none),
    PairLeaves.three PairReceipts.cell6439 PairReceipts.check6439 (by decide) (none),
    PairLeaves.three PairReceipts.cell6440 PairReceipts.check6440 (by decide) (none),
    PairLeaves.three PairReceipts.cell6441 PairReceipts.check6441 (by decide) (none),
    trivial⟩)
private theorem allAxes63:PairRoute.Done (2:Fin 18) ⟨⟨51,51,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6442 0),
    (PairReceipts.route6442 1),
    (PairReceipts.route6442 2),
    (PairReceipts.route6442 3),
    (PairReceipts.route6442 4),
    (PairReceipts.route6442 5),
    (PairReceipts.route6442 6),
    (PairReceipts.route6442 7),
    (PairReceipts.route6442 8),
    (PairReceipts.route6442 9),
    (PairReceipts.route6442 10),
    PairLeaves.three PairReceipts.cell6453 PairReceipts.check6453 (by decide) (none),
    PairLeaves.three PairReceipts.cell6454 PairReceipts.check6454 (by decide) (none),
    PairLeaves.three PairReceipts.cell6455 PairReceipts.check6455 (by decide) (none),
    PairLeaves.three PairReceipts.cell6456 PairReceipts.check6456 (by decide) (none),
    PairLeaves.three PairReceipts.cell6457 PairReceipts.check6457 (by decide) (none),
    trivial⟩)
private theorem allAxes95:PairRoute.Done (2:Fin 18) ⟨⟨52,52,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6442 11),
    (PairReceipts.route6442 12),
    (PairReceipts.route6460 0),
    (PairReceipts.route6460 1),
    (PairReceipts.route6460 2),
    (PairReceipts.route6460 3),
    (PairReceipts.route6460 4),
    (PairReceipts.route6460 5),
    (PairReceipts.route6460 6),
    (PairReceipts.route6460 7),
    (PairReceipts.route6460 8),
    PairLeaves.three PairReceipts.cell6469 PairReceipts.check6469 (by decide) (none),
    PairLeaves.three PairReceipts.cell6470 PairReceipts.check6470 (by decide) (none),
    PairLeaves.three PairReceipts.cell6471 PairReceipts.check6471 (by decide) (none),
    PairLeaves.three PairReceipts.cell6472 PairReceipts.check6472 (by decide) (none),
    PairLeaves.three PairReceipts.cell6473 PairReceipts.check6473 (by decide) (none),
    trivial⟩)
private theorem allAxes127:PairRoute.Done (2:Fin 18) ⟨⟨53,53,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6460 9),
    (PairReceipts.route6460 10),
    (PairReceipts.route6460 11),
    (PairReceipts.route6460 12),
    (PairReceipts.route6460 13),
    (PairReceipts.route6460 14),
    (PairReceipts.route6480 0),
    (PairReceipts.route6480 1),
    (PairReceipts.route6480 2),
    (PairReceipts.route6480 3),
    (PairReceipts.route6480 4),
    PairLeaves.three PairReceipts.cell6485 PairReceipts.check6485 (by decide) (none),
    PairLeaves.three PairReceipts.cell6486 PairReceipts.check6486 (by decide) (none),
    PairLeaves.three PairReceipts.cell6487 PairReceipts.check6487 (by decide) (none),
    PairLeaves.three PairReceipts.cell6488 PairReceipts.check6488 (by decide) (none),
    PairLeaves.three PairReceipts.cell6489 PairReceipts.check6489 (by decide) (none),
    trivial⟩)
private theorem allAxes159:PairRoute.Done (2:Fin 18) ⟨⟨54,54,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6480 5),
    (PairReceipts.route6480 6),
    (PairReceipts.route6480 7),
    (PairReceipts.route6480 8),
    (PairReceipts.route6480 9),
    (PairReceipts.route6480 10),
    (PairReceipts.route6480 11),
    (PairReceipts.route6480 12),
    (PairReceipts.route6480 13),
    (PairReceipts.route6480 14),
    (PairReceipts.route6500 0),
    PairLeaves.three PairReceipts.cell6501 PairReceipts.check6501 (by decide) (none),
    PairLeaves.three PairReceipts.cell6502 PairReceipts.check6502 (by decide) (none),
    PairLeaves.three PairReceipts.cell6503 PairReceipts.check6503 (by decide) (none),
    PairLeaves.three PairReceipts.cell6504 PairReceipts.check6504 (by decide) (none),
    PairLeaves.three PairReceipts.cell6505 PairReceipts.check6505 (by decide) (none),
    trivial⟩)
private theorem allAxes191:PairRoute.Done (2:Fin 18) ⟨⟨55,55,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6500 1),
    (PairReceipts.route6500 2),
    (PairReceipts.route6500 3),
    (PairReceipts.route6500 4),
    (PairReceipts.route6500 5),
    (PairReceipts.route6500 6),
    (PairReceipts.route6500 7),
    (PairReceipts.route6500 8),
    (PairReceipts.route6500 9),
    (PairReceipts.route6500 10),
    (PairReceipts.route6500 11),
    PairLeaves.three PairReceipts.cell6517 PairReceipts.check6517 (by decide) (none),
    PairLeaves.three PairReceipts.cell6518 PairReceipts.check6518 (by decide) (none),
    PairLeaves.three PairReceipts.cell6519 PairReceipts.check6519 (by decide) (none),
    PairLeaves.three PairReceipts.cell6520 PairReceipts.check6520 (by decide) (none),
    PairLeaves.three PairReceipts.cell6521 PairReceipts.check6521 (by decide) (none),
    trivial⟩)
private theorem allAxes223:PairRoute.Done (2:Fin 18) ⟨⟨56,56,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6522 0),
    (PairReceipts.route6522 1),
    (PairReceipts.route6522 2),
    (PairReceipts.route6522 3),
    (PairReceipts.route6522 4),
    (PairReceipts.route6522 5),
    (PairReceipts.route6522 6),
    (PairReceipts.route6522 7),
    (PairReceipts.route6522 8),
    (PairReceipts.route6522 9),
    (PairReceipts.route6522 10),
    (PairReceipts.route6522 11),
    PairLeaves.three PairReceipts.cell6534 PairReceipts.check6534 (by decide) (none),
    PairLeaves.three PairReceipts.cell6535 PairReceipts.check6535 (by decide) (none),
    PairLeaves.three PairReceipts.cell6536 PairReceipts.check6536 (by decide) (none),
    PairLeaves.three PairReceipts.cell6537 PairReceipts.check6537 (by decide) (none),
    trivial⟩)
private theorem allAxes255:PairRoute.Done (2:Fin 18) ⟨⟨57,57,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6522 12),
    (PairReceipts.route6522 13),
    (PairReceipts.route6540 0),
    (PairReceipts.route6540 1),
    (PairReceipts.route6540 2),
    (PairReceipts.route6540 3),
    (PairReceipts.route6540 4),
    (PairReceipts.route6540 5),
    (PairReceipts.route6540 6),
    (PairReceipts.route6540 7),
    (PairReceipts.route6540 8),
    (PairReceipts.route6540 9),
    PairLeaves.three PairReceipts.cell6550 PairReceipts.check6550 (by decide) (none),
    PairLeaves.three PairReceipts.cell6551 PairReceipts.check6551 (by decide) (none),
    PairLeaves.three PairReceipts.cell6552 PairReceipts.check6552 (by decide) (none),
    PairLeaves.three PairReceipts.cell6553 PairReceipts.check6553 (by decide) (none),
    trivial⟩)
private theorem allAxes287:PairRoute.Done (2:Fin 18) ⟨⟨58,58,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6540 10),
    (PairReceipts.route6540 11),
    (PairReceipts.route6540 12),
    (PairReceipts.route6540 13),
    (PairReceipts.route6540 14),
    (PairReceipts.route6540 15),
    (PairReceipts.route6560 0),
    (PairReceipts.route6560 1),
    (PairReceipts.route6560 2),
    (PairReceipts.route6560 3),
    (PairReceipts.route6560 4),
    (PairReceipts.route6560 5),
    PairLeaves.three PairReceipts.cell6566 PairReceipts.check6566 (by decide) (none),
    PairLeaves.three PairReceipts.cell6567 PairReceipts.check6567 (by decide) (none),
    PairLeaves.three PairReceipts.cell6568 PairReceipts.check6568 (by decide) (none),
    PairLeaves.three PairReceipts.cell6569 PairReceipts.check6569 (by decide) (none),
    trivial⟩)
private theorem allAxes319:PairRoute.Done (2:Fin 18) ⟨⟨59,59,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6560 6),
    (PairReceipts.route6560 7),
    (PairReceipts.route6560 8),
    (PairReceipts.route6560 9),
    (PairReceipts.route6560 10),
    (PairReceipts.route6560 11),
    (PairReceipts.route6560 12),
    (PairReceipts.route6560 13),
    (PairReceipts.route6560 14),
    (PairReceipts.route6560 15),
    (PairReceipts.route6580 0),
    (PairReceipts.route6580 1),
    PairLeaves.three PairReceipts.cell6582 PairReceipts.check6582 (by decide) (none),
    PairLeaves.three PairReceipts.cell6583 PairReceipts.check6583 (by decide) (none),
    PairLeaves.three PairReceipts.cell6584 PairReceipts.check6584 (by decide) (none),
    PairLeaves.three PairReceipts.cell6585 PairReceipts.check6585 (by decide) (none),
    trivial⟩)
private theorem allAxes351:PairRoute.Done (2:Fin 18) ⟨⟨60,60,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6580 2),
    (PairReceipts.route6580 3),
    (PairReceipts.route6580 4),
    (PairReceipts.route6580 5),
    (PairReceipts.route6580 6),
    (PairReceipts.route6580 7),
    (PairReceipts.route6580 8),
    (PairReceipts.route6580 9),
    (PairReceipts.route6580 10),
    (PairReceipts.route6580 11),
    (PairReceipts.route6580 12),
    (PairReceipts.route6580 13),
    PairLeaves.three PairReceipts.cell6598 PairReceipts.check6598 (by decide) (none),
    PairLeaves.three PairReceipts.cell6599 PairReceipts.check6599 (by decide) (none),
    PairLeaves.three PairReceipts.cell6600 PairReceipts.check6600 (by decide) (none),
    PairLeaves.three PairReceipts.cell6601 PairReceipts.check6601 (by decide) (none),
    trivial⟩)
private theorem allAxes383:PairRoute.Done (2:Fin 18) ⟨⟨61,61,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6602 0),
    (PairReceipts.route6602 1),
    (PairReceipts.route6602 2),
    (PairReceipts.route6602 3),
    (PairReceipts.route6602 4),
    (PairReceipts.route6602 5),
    (PairReceipts.route6602 6),
    (PairReceipts.route6602 7),
    (PairReceipts.route6602 8),
    (PairReceipts.route6602 9),
    (PairReceipts.route6602 10),
    (PairReceipts.route6602 11),
    PairLeaves.three PairReceipts.cell6614 PairReceipts.check6614 (by decide) (none),
    PairLeaves.three PairReceipts.cell6615 PairReceipts.check6615 (by decide) (none),
    PairLeaves.three PairReceipts.cell6616 PairReceipts.check6616 (by decide) (none),
    PairLeaves.three PairReceipts.cell6617 PairReceipts.check6617 (by decide) (none),
    trivial⟩)
private theorem allAxes415:PairRoute.Done (2:Fin 18) ⟨⟨62,62,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6602 12),
    (PairReceipts.route6602 13),
    (PairReceipts.route6620 0),
    (PairReceipts.route6620 1),
    (PairReceipts.route6620 2),
    (PairReceipts.route6620 3),
    (PairReceipts.route6620 4),
    (PairReceipts.route6620 5),
    (PairReceipts.route6620 6),
    (PairReceipts.route6620 7),
    (PairReceipts.route6620 8),
    (PairReceipts.route6620 9),
    PairLeaves.three PairReceipts.cell6630 PairReceipts.check6630 (by decide) (none),
    PairLeaves.three PairReceipts.cell6631 PairReceipts.check6631 (by decide) (none),
    PairLeaves.three PairReceipts.cell6632 PairReceipts.check6632 (by decide) (none),
    PairLeaves.three PairReceipts.cell6633 PairReceipts.check6633 (by decide) (none),
    trivial⟩)
private theorem allAxes447:PairRoute.Done (2:Fin 18) ⟨⟨63,63,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6620 10),
    (PairReceipts.route6620 11),
    (PairReceipts.route6620 12),
    (PairReceipts.route6620 13),
    (PairReceipts.route6620 14),
    (PairReceipts.route6620 15),
    (PairReceipts.route6640 0),
    (PairReceipts.route6640 1),
    (PairReceipts.route6640 2),
    (PairReceipts.route6640 3),
    (PairReceipts.route6640 4),
    (PairReceipts.route6640 5),
    PairLeaves.three PairReceipts.cell6646 PairReceipts.check6646 (by decide) (none),
    PairLeaves.three PairReceipts.cell6647 PairReceipts.check6647 (by decide) (none),
    PairLeaves.three PairReceipts.cell6648 PairReceipts.check6648 (by decide) (none),
    PairLeaves.three PairReceipts.cell6649 PairReceipts.check6649 (by decide) (none),
    trivial⟩)
private def grade448 := PairRoute.grade 62 allAxes415 allAxes447
private def grade449 := PairRoute.grade 61 allAxes383 grade448
private def grade450 := PairRoute.grade 60 allAxes351 grade449
private def grade451 := PairRoute.grade 59 allAxes319 grade450
private def grade452 := PairRoute.grade 58 allAxes287 grade451
private def grade453 := PairRoute.grade 57 allAxes255 grade452
private def grade454 := PairRoute.grade 56 allAxes223 grade453
private def grade455 := PairRoute.grade 55 allAxes191 grade454
private def grade456 := PairRoute.grade 54 allAxes159 grade455
private def grade457 := PairRoute.grade 53 allAxes127 grade456
private def grade458 := PairRoute.grade 52 allAxes95 grade457
private def grade459 := PairRoute.grade 51 allAxes63 grade458
private def grade460 := PairRoute.grade 50 allAxes31 grade459
theorem case140: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,15,some 15⟩:=PairRoute.start _ grade460
private theorem allAxes494:PairRoute.Done (2:Fin 18) ⟨⟨50,50,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6180 2),
    (PairReceipts.route6180 3),
    (PairReceipts.route6180 4),
    (PairReceipts.route6180 5),
    (PairReceipts.route6180 6),
    (PairReceipts.route6180 7),
    (PairReceipts.route6180 8),
    (PairReceipts.route6180 9),
    (PairReceipts.route6180 10),
    (PairReceipts.route6180 11),
    PairLeaves.three PairReceipts.cell6198 PairReceipts.check6198 (by decide) (none),
    PairLeaves.three PairReceipts.cell6199 PairReceipts.check6199 (by decide) (none),
    PairLeaves.three PairReceipts.cell6200 PairReceipts.check6200 (by decide) (none),
    PairLeaves.three PairReceipts.cell6201 PairReceipts.check6201 (by decide) (none),
    PairLeaves.three PairReceipts.cell6202 PairReceipts.check6202 (by decide) (none),
    PairLeaves.three PairReceipts.cell6203 PairReceipts.check6203 (by decide) (none),
    PairLeaves.three PairReceipts.cell6204 PairReceipts.check6204 (by decide) (none),
    trivial⟩)
private theorem allAxes528:PairRoute.Done (2:Fin 18) ⟨⟨51,51,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6205 0),
    (PairReceipts.route6205 1),
    (PairReceipts.route6205 2),
    (PairReceipts.route6205 3),
    (PairReceipts.route6205 4),
    (PairReceipts.route6205 5),
    (PairReceipts.route6205 6),
    (PairReceipts.route6205 7),
    (PairReceipts.route6205 8),
    (PairReceipts.route6205 9),
    (PairReceipts.route6205 10),
    PairLeaves.three PairReceipts.cell6216 PairReceipts.check6216 (by decide) (none),
    PairLeaves.three PairReceipts.cell6217 PairReceipts.check6217 (by decide) (none),
    PairLeaves.three PairReceipts.cell6218 PairReceipts.check6218 (by decide) (none),
    PairLeaves.three PairReceipts.cell6219 PairReceipts.check6219 (by decide) (none),
    PairLeaves.three PairReceipts.cell6220 PairReceipts.check6220 (by decide) (none),
    PairLeaves.three PairReceipts.cell6221 PairReceipts.check6221 (by decide) (none),
    trivial⟩)
private theorem allAxes562:PairRoute.Done (2:Fin 18) ⟨⟨52,52,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6222 0),
    (PairReceipts.route6222 1),
    (PairReceipts.route6222 2),
    (PairReceipts.route6222 3),
    (PairReceipts.route6222 4),
    (PairReceipts.route6222 5),
    (PairReceipts.route6222 6),
    (PairReceipts.route6222 7),
    (PairReceipts.route6222 8),
    (PairReceipts.route6222 9),
    (PairReceipts.route6222 10),
    PairLeaves.three PairReceipts.cell6233 PairReceipts.check6233 (by decide) (none),
    PairLeaves.three PairReceipts.cell6234 PairReceipts.check6234 (by decide) (none),
    PairLeaves.three PairReceipts.cell6235 PairReceipts.check6235 (by decide) (none),
    PairLeaves.three PairReceipts.cell6236 PairReceipts.check6236 (by decide) (none),
    PairLeaves.three PairReceipts.cell6237 PairReceipts.check6237 (by decide) (none),
    PairLeaves.three PairReceipts.cell6238 PairReceipts.check6238 (by decide) (none),
    trivial⟩)
private theorem allAxes596:PairRoute.Done (2:Fin 18) ⟨⟨53,53,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6222 11),
    (PairReceipts.route6240 0),
    (PairReceipts.route6240 1),
    (PairReceipts.route6240 2),
    (PairReceipts.route6240 3),
    (PairReceipts.route6240 4),
    (PairReceipts.route6240 5),
    (PairReceipts.route6240 6),
    (PairReceipts.route6240 7),
    (PairReceipts.route6240 8),
    (PairReceipts.route6240 9),
    PairLeaves.three PairReceipts.cell6250 PairReceipts.check6250 (by decide) (none),
    PairLeaves.three PairReceipts.cell6251 PairReceipts.check6251 (by decide) (none),
    PairLeaves.three PairReceipts.cell6252 PairReceipts.check6252 (by decide) (none),
    PairLeaves.three PairReceipts.cell6253 PairReceipts.check6253 (by decide) (none),
    PairLeaves.three PairReceipts.cell6254 PairReceipts.check6254 (by decide) (none),
    PairLeaves.three PairReceipts.cell6255 PairReceipts.check6255 (by decide) (none),
    trivial⟩)
private theorem allAxes630:PairRoute.Done (2:Fin 18) ⟨⟨54,54,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6240 10),
    (PairReceipts.route6240 11),
    (PairReceipts.route6240 12),
    (PairReceipts.route6240 13),
    (PairReceipts.route6260 0),
    (PairReceipts.route6260 1),
    (PairReceipts.route6260 2),
    (PairReceipts.route6260 3),
    (PairReceipts.route6260 4),
    (PairReceipts.route6260 5),
    (PairReceipts.route6260 6),
    PairLeaves.three PairReceipts.cell6267 PairReceipts.check6267 (by decide) (none),
    PairLeaves.three PairReceipts.cell6268 PairReceipts.check6268 (by decide) (none),
    PairLeaves.three PairReceipts.cell6269 PairReceipts.check6269 (by decide) (none),
    PairLeaves.three PairReceipts.cell6270 PairReceipts.check6270 (by decide) (none),
    PairLeaves.three PairReceipts.cell6271 PairReceipts.check6271 (by decide) (none),
    PairLeaves.three PairReceipts.cell6272 PairReceipts.check6272 (by decide) (none),
    trivial⟩)
private theorem allAxes664:PairRoute.Done (2:Fin 18) ⟨⟨55,55,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6260 7),
    (PairReceipts.route6260 8),
    (PairReceipts.route6260 9),
    (PairReceipts.route6260 10),
    (PairReceipts.route6260 11),
    (PairReceipts.route6260 12),
    (PairReceipts.route6260 13),
    (PairReceipts.route6280 0),
    (PairReceipts.route6280 1),
    (PairReceipts.route6280 2),
    (PairReceipts.route6280 3),
    PairLeaves.three PairReceipts.cell6284 PairReceipts.check6284 (by decide) (none),
    PairLeaves.three PairReceipts.cell6285 PairReceipts.check6285 (by decide) (none),
    PairLeaves.three PairReceipts.cell6286 PairReceipts.check6286 (by decide) (none),
    PairLeaves.three PairReceipts.cell6287 PairReceipts.check6287 (by decide) (none),
    PairLeaves.three PairReceipts.cell6288 PairReceipts.check6288 (by decide) (none),
    PairLeaves.three PairReceipts.cell6289 PairReceipts.check6289 (by decide) (none),
    trivial⟩)
private theorem allAxes698:PairRoute.Done (2:Fin 18) ⟨⟨56,56,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6280 4),
    (PairReceipts.route6280 5),
    (PairReceipts.route6280 6),
    (PairReceipts.route6280 7),
    (PairReceipts.route6280 8),
    (PairReceipts.route6280 9),
    (PairReceipts.route6280 10),
    (PairReceipts.route6280 11),
    (PairReceipts.route6280 12),
    (PairReceipts.route6280 13),
    (PairReceipts.route6300 0),
    (PairReceipts.route6300 1),
    PairLeaves.three PairReceipts.cell6302 PairReceipts.check6302 (by decide) (none),
    PairLeaves.three PairReceipts.cell6303 PairReceipts.check6303 (by decide) (none),
    PairLeaves.three PairReceipts.cell6304 PairReceipts.check6304 (by decide) (none),
    PairLeaves.three PairReceipts.cell6305 PairReceipts.check6305 (by decide) (none),
    PairLeaves.three PairReceipts.cell6306 PairReceipts.check6306 (by decide) (none),
    trivial⟩)
private theorem allAxes732:PairRoute.Done (2:Fin 18) ⟨⟨57,57,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6300 2),
    (PairReceipts.route6300 3),
    (PairReceipts.route6300 4),
    (PairReceipts.route6300 5),
    (PairReceipts.route6300 6),
    (PairReceipts.route6300 7),
    (PairReceipts.route6300 8),
    (PairReceipts.route6300 9),
    (PairReceipts.route6300 10),
    (PairReceipts.route6300 11),
    (PairReceipts.route6300 12),
    (PairReceipts.route6300 13),
    PairLeaves.three PairReceipts.cell6319 PairReceipts.check6319 (by decide) (none),
    PairLeaves.three PairReceipts.cell6320 PairReceipts.check6320 (by decide) (none),
    PairLeaves.three PairReceipts.cell6321 PairReceipts.check6321 (by decide) (none),
    PairLeaves.three PairReceipts.cell6322 PairReceipts.check6322 (by decide) (none),
    PairLeaves.three PairReceipts.cell6323 PairReceipts.check6323 (by decide) (none),
    trivial⟩)
private theorem allAxes766:PairRoute.Done (2:Fin 18) ⟨⟨58,58,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6324 0),
    (PairReceipts.route6324 1),
    (PairReceipts.route6324 2),
    (PairReceipts.route6324 3),
    (PairReceipts.route6324 4),
    (PairReceipts.route6324 5),
    (PairReceipts.route6324 6),
    (PairReceipts.route6324 7),
    (PairReceipts.route6324 8),
    (PairReceipts.route6324 9),
    (PairReceipts.route6324 10),
    (PairReceipts.route6324 11),
    PairLeaves.three PairReceipts.cell6336 PairReceipts.check6336 (by decide) (none),
    PairLeaves.three PairReceipts.cell6337 PairReceipts.check6337 (by decide) (none),
    PairLeaves.three PairReceipts.cell6338 PairReceipts.check6338 (by decide) (none),
    PairLeaves.three PairReceipts.cell6339 PairReceipts.check6339 (by decide) (none),
    PairLeaves.three PairReceipts.cell6340 PairReceipts.check6340 (by decide) (none),
    trivial⟩)
private theorem allAxes800:PairRoute.Done (2:Fin 18) ⟨⟨59,59,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6341 0),
    (PairReceipts.route6341 1),
    (PairReceipts.route6341 2),
    (PairReceipts.route6341 3),
    (PairReceipts.route6341 4),
    (PairReceipts.route6341 5),
    (PairReceipts.route6341 6),
    (PairReceipts.route6341 7),
    (PairReceipts.route6341 8),
    (PairReceipts.route6341 9),
    (PairReceipts.route6341 10),
    (PairReceipts.route6341 11),
    PairLeaves.three PairReceipts.cell6353 PairReceipts.check6353 (by decide) (none),
    PairLeaves.three PairReceipts.cell6354 PairReceipts.check6354 (by decide) (none),
    PairLeaves.three PairReceipts.cell6355 PairReceipts.check6355 (by decide) (none),
    PairLeaves.three PairReceipts.cell6356 PairReceipts.check6356 (by decide) (none),
    PairLeaves.three PairReceipts.cell6357 PairReceipts.check6357 (by decide) (none),
    trivial⟩)
private theorem allAxes834:PairRoute.Done (2:Fin 18) ⟨⟨60,60,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6341 12),
    (PairReceipts.route6341 13),
    (PairReceipts.route6360 0),
    (PairReceipts.route6360 1),
    (PairReceipts.route6360 2),
    (PairReceipts.route6360 3),
    (PairReceipts.route6360 4),
    (PairReceipts.route6360 5),
    (PairReceipts.route6360 6),
    (PairReceipts.route6360 7),
    (PairReceipts.route6360 8),
    (PairReceipts.route6360 9),
    PairLeaves.three PairReceipts.cell6370 PairReceipts.check6370 (by decide) (none),
    PairLeaves.three PairReceipts.cell6371 PairReceipts.check6371 (by decide) (none),
    PairLeaves.three PairReceipts.cell6372 PairReceipts.check6372 (by decide) (none),
    PairLeaves.three PairReceipts.cell6373 PairReceipts.check6373 (by decide) (none),
    PairLeaves.three PairReceipts.cell6374 PairReceipts.check6374 (by decide) (none),
    trivial⟩)
private theorem allAxes868:PairRoute.Done (2:Fin 18) ⟨⟨61,61,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6360 10),
    (PairReceipts.route6360 11),
    (PairReceipts.route6360 12),
    (PairReceipts.route6360 13),
    (PairReceipts.route6360 14),
    (PairReceipts.route6380 0),
    (PairReceipts.route6380 1),
    (PairReceipts.route6380 2),
    (PairReceipts.route6380 3),
    (PairReceipts.route6380 4),
    (PairReceipts.route6380 5),
    (PairReceipts.route6380 6),
    PairLeaves.three PairReceipts.cell6387 PairReceipts.check6387 (by decide) (none),
    PairLeaves.three PairReceipts.cell6388 PairReceipts.check6388 (by decide) (none),
    PairLeaves.three PairReceipts.cell6389 PairReceipts.check6389 (by decide) (none),
    PairLeaves.three PairReceipts.cell6390 PairReceipts.check6390 (by decide) (none),
    PairLeaves.three PairReceipts.cell6391 PairReceipts.check6391 (by decide) (none),
    trivial⟩)
private theorem allAxes902:PairRoute.Done (2:Fin 18) ⟨⟨62,62,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6380 7),
    (PairReceipts.route6380 8),
    (PairReceipts.route6380 9),
    (PairReceipts.route6380 10),
    (PairReceipts.route6380 11),
    (PairReceipts.route6380 12),
    (PairReceipts.route6380 13),
    (PairReceipts.route6380 14),
    (PairReceipts.route6400 0),
    (PairReceipts.route6400 1),
    (PairReceipts.route6400 2),
    (PairReceipts.route6400 3),
    PairLeaves.three PairReceipts.cell6404 PairReceipts.check6404 (by decide) (none),
    PairLeaves.three PairReceipts.cell6405 PairReceipts.check6405 (by decide) (none),
    PairLeaves.three PairReceipts.cell6406 PairReceipts.check6406 (by decide) (none),
    PairLeaves.three PairReceipts.cell6407 PairReceipts.check6407 (by decide) (none),
    PairLeaves.three PairReceipts.cell6408 PairReceipts.check6408 (by decide) (none),
    trivial⟩)
private theorem allAxes936:PairRoute.Done (2:Fin 18) ⟨⟨63,63,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6400 4),
    (PairReceipts.route6400 5),
    (PairReceipts.route6400 6),
    (PairReceipts.route6400 7),
    (PairReceipts.route6400 8),
    (PairReceipts.route6400 9),
    (PairReceipts.route6400 10),
    (PairReceipts.route6400 11),
    (PairReceipts.route6400 12),
    (PairReceipts.route6400 13),
    (PairReceipts.route6400 14),
    (PairReceipts.route6420 0),
    PairLeaves.three PairReceipts.cell6421 PairReceipts.check6421 (by decide) (none),
    PairLeaves.three PairReceipts.cell6422 PairReceipts.check6422 (by decide) (none),
    PairLeaves.three PairReceipts.cell6423 PairReceipts.check6423 (by decide) (none),
    PairLeaves.three PairReceipts.cell6424 PairReceipts.check6424 (by decide) (none),
    PairLeaves.three PairReceipts.cell6425 PairReceipts.check6425 (by decide) (none),
    trivial⟩)
private def grade937 := PairRoute.grade 62 allAxes902 allAxes936
private def grade938 := PairRoute.grade 61 allAxes868 grade937
private def grade939 := PairRoute.grade 60 allAxes834 grade938
private def grade940 := PairRoute.grade 59 allAxes800 grade939
private def grade941 := PairRoute.grade 58 allAxes766 grade940
private def grade942 := PairRoute.grade 57 allAxes732 grade941
private def grade943 := PairRoute.grade 56 allAxes698 grade942
private def grade944 := PairRoute.grade 55 allAxes664 grade943
private def grade945 := PairRoute.grade 54 allAxes630 grade944
private def grade946 := PairRoute.grade 53 allAxes596 grade945
private def grade947 := PairRoute.grade 52 allAxes562 grade946
private def grade948 := PairRoute.grade 51 allAxes528 grade947
private def grade949 := PairRoute.grade 50 allAxes494 grade948
theorem case141: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,16,some 16⟩:=PairRoute.start _ grade949
private theorem allAxes985:PairRoute.Done (2:Fin 18) ⟨⟨50,50,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route5936 0),
    (PairReceipts.route5936 1),
    (PairReceipts.route5936 2),
    (PairReceipts.route5936 3),
    (PairReceipts.route5940 0),
    (PairReceipts.route5940 1),
    (PairReceipts.route5940 2),
    (PairReceipts.route5940 3),
    (PairReceipts.route5940 4),
    (PairReceipts.route5940 5),
    PairLeaves.three PairReceipts.cell5946 PairReceipts.check5946 (by decide) (none),
    PairLeaves.three PairReceipts.cell5947 PairReceipts.check5947 (by decide) (none),
    PairLeaves.three PairReceipts.cell5948 PairReceipts.check5948 (by decide) (none),
    PairLeaves.three PairReceipts.cell5949 PairReceipts.check5949 (by decide) (none),
    PairLeaves.three PairReceipts.cell5950 PairReceipts.check5950 (by decide) (none),
    PairLeaves.three PairReceipts.cell5951 PairReceipts.check5951 (by decide) (none),
    PairLeaves.three PairReceipts.cell5952 PairReceipts.check5952 (by decide) (none),
    PairLeaves.three PairReceipts.cell5953 PairReceipts.check5953 (by decide) (none),
    trivial⟩)
private theorem allAxes1021:PairRoute.Done (2:Fin 18) ⟨⟨51,51,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route5940 6),
    (PairReceipts.route5940 7),
    (PairReceipts.route5940 8),
    (PairReceipts.route5940 9),
    (PairReceipts.route5940 10),
    (PairReceipts.route5940 11),
    (PairReceipts.route5960 0),
    (PairReceipts.route5960 1),
    (PairReceipts.route5960 2),
    (PairReceipts.route5960 3),
    (PairReceipts.route5960 4),
    PairLeaves.three PairReceipts.cell5965 PairReceipts.check5965 (by decide) (none),
    PairLeaves.three PairReceipts.cell5966 PairReceipts.check5966 (by decide) (none),
    PairLeaves.three PairReceipts.cell5967 PairReceipts.check5967 (by decide) (none),
    PairLeaves.three PairReceipts.cell5968 PairReceipts.check5968 (by decide) (none),
    PairLeaves.three PairReceipts.cell5969 PairReceipts.check5969 (by decide) (none),
    PairLeaves.three PairReceipts.cell5970 PairReceipts.check5970 (by decide) (none),
    PairLeaves.three PairReceipts.cell5971 PairReceipts.check5971 (by decide) (none),
    trivial⟩)
private theorem allAxes1057:PairRoute.Done (2:Fin 18) ⟨⟨52,52,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route5960 5),
    (PairReceipts.route5960 6),
    (PairReceipts.route5960 7),
    (PairReceipts.route5960 8),
    (PairReceipts.route5960 9),
    (PairReceipts.route5960 10),
    (PairReceipts.route5960 11),
    (PairReceipts.route5960 12),
    (PairReceipts.route5980 0),
    (PairReceipts.route5980 1),
    (PairReceipts.route5980 2),
    PairLeaves.three PairReceipts.cell5983 PairReceipts.check5983 (by decide) (none),
    PairLeaves.three PairReceipts.cell5984 PairReceipts.check5984 (by decide) (none),
    PairLeaves.three PairReceipts.cell5985 PairReceipts.check5985 (by decide) (none),
    PairLeaves.three PairReceipts.cell5986 PairReceipts.check5986 (by decide) (none),
    PairLeaves.three PairReceipts.cell5987 PairReceipts.check5987 (by decide) (none),
    PairLeaves.three PairReceipts.cell5988 PairReceipts.check5988 (by decide) (none),
    PairLeaves.three PairReceipts.cell5989 PairReceipts.check5989 (by decide) (none),
    trivial⟩)
private theorem allAxes1093:PairRoute.Done (2:Fin 18) ⟨⟨53,53,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route5980 3),
    (PairReceipts.route5980 4),
    (PairReceipts.route5980 5),
    (PairReceipts.route5980 6),
    (PairReceipts.route5980 7),
    (PairReceipts.route5980 8),
    (PairReceipts.route5980 9),
    (PairReceipts.route5980 10),
    (PairReceipts.route5980 11),
    (PairReceipts.route5980 12),
    (PairReceipts.route6000 0),
    PairLeaves.three PairReceipts.cell6001 PairReceipts.check6001 (by decide) (none),
    PairLeaves.three PairReceipts.cell6002 PairReceipts.check6002 (by decide) (none),
    PairLeaves.three PairReceipts.cell6003 PairReceipts.check6003 (by decide) (none),
    PairLeaves.three PairReceipts.cell6004 PairReceipts.check6004 (by decide) (none),
    PairLeaves.three PairReceipts.cell6005 PairReceipts.check6005 (by decide) (none),
    PairLeaves.three PairReceipts.cell6006 PairReceipts.check6006 (by decide) (none),
    PairLeaves.three PairReceipts.cell6007 PairReceipts.check6007 (by decide) (none),
    trivial⟩)
private theorem allAxes1129:PairRoute.Done (2:Fin 18) ⟨⟨54,54,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6000 1),
    (PairReceipts.route6000 2),
    (PairReceipts.route6000 3),
    (PairReceipts.route6000 4),
    (PairReceipts.route6000 5),
    (PairReceipts.route6000 6),
    (PairReceipts.route6000 7),
    (PairReceipts.route6000 8),
    (PairReceipts.route6000 9),
    (PairReceipts.route6000 10),
    (PairReceipts.route6000 11),
    PairLeaves.three PairReceipts.cell6019 PairReceipts.check6019 (by decide) (none),
    PairLeaves.three PairReceipts.cell6020 PairReceipts.check6020 (by decide) (none),
    PairLeaves.three PairReceipts.cell6021 PairReceipts.check6021 (by decide) (none),
    PairLeaves.three PairReceipts.cell6022 PairReceipts.check6022 (by decide) (none),
    PairLeaves.three PairReceipts.cell6023 PairReceipts.check6023 (by decide) (none),
    PairLeaves.three PairReceipts.cell6024 PairReceipts.check6024 (by decide) (none),
    PairLeaves.three PairReceipts.cell6025 PairReceipts.check6025 (by decide) (none),
    trivial⟩)
private theorem allAxes1165:PairRoute.Done (2:Fin 18) ⟨⟨55,55,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6026 0),
    (PairReceipts.route6026 1),
    (PairReceipts.route6026 2),
    (PairReceipts.route6026 3),
    (PairReceipts.route6026 4),
    (PairReceipts.route6026 5),
    (PairReceipts.route6026 6),
    (PairReceipts.route6026 7),
    (PairReceipts.route6026 8),
    (PairReceipts.route6026 9),
    (PairReceipts.route6026 10),
    PairLeaves.three PairReceipts.cell6037 PairReceipts.check6037 (by decide) (none),
    PairLeaves.three PairReceipts.cell6038 PairReceipts.check6038 (by decide) (none),
    PairLeaves.three PairReceipts.cell6039 PairReceipts.check6039 (by decide) (none),
    PairLeaves.three PairReceipts.cell6040 PairReceipts.check6040 (by decide) (none),
    PairLeaves.three PairReceipts.cell6041 PairReceipts.check6041 (by decide) (none),
    PairLeaves.three PairReceipts.cell6042 PairReceipts.check6042 (by decide) (none),
    PairLeaves.three PairReceipts.cell6043 PairReceipts.check6043 (by decide) (none),
    trivial⟩)
private theorem allAxes1201:PairRoute.Done (2:Fin 18) ⟨⟨56,56,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6044 0),
    (PairReceipts.route6044 1),
    (PairReceipts.route6044 2),
    (PairReceipts.route6044 3),
    (PairReceipts.route6044 4),
    (PairReceipts.route6044 5),
    (PairReceipts.route6044 6),
    (PairReceipts.route6044 7),
    (PairReceipts.route6044 8),
    (PairReceipts.route6044 9),
    (PairReceipts.route6044 10),
    (PairReceipts.route6044 11),
    PairLeaves.three PairReceipts.cell6056 PairReceipts.check6056 (by decide) (none),
    PairLeaves.three PairReceipts.cell6057 PairReceipts.check6057 (by decide) (none),
    PairLeaves.three PairReceipts.cell6058 PairReceipts.check6058 (by decide) (none),
    PairLeaves.three PairReceipts.cell6059 PairReceipts.check6059 (by decide) (none),
    PairLeaves.three PairReceipts.cell6060 PairReceipts.check6060 (by decide) (none),
    PairLeaves.three PairReceipts.cell6061 PairReceipts.check6061 (by decide) (none),
    trivial⟩)
private theorem allAxes1237:PairRoute.Done (2:Fin 18) ⟨⟨57,57,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6062 0),
    (PairReceipts.route6062 1),
    (PairReceipts.route6062 2),
    (PairReceipts.route6062 3),
    (PairReceipts.route6062 4),
    (PairReceipts.route6062 5),
    (PairReceipts.route6062 6),
    (PairReceipts.route6062 7),
    (PairReceipts.route6062 8),
    (PairReceipts.route6062 9),
    (PairReceipts.route6062 10),
    (PairReceipts.route6062 11),
    PairLeaves.three PairReceipts.cell6074 PairReceipts.check6074 (by decide) (none),
    PairLeaves.three PairReceipts.cell6075 PairReceipts.check6075 (by decide) (none),
    PairLeaves.three PairReceipts.cell6076 PairReceipts.check6076 (by decide) (none),
    PairLeaves.three PairReceipts.cell6077 PairReceipts.check6077 (by decide) (none),
    PairLeaves.three PairReceipts.cell6078 PairReceipts.check6078 (by decide) (none),
    PairLeaves.three PairReceipts.cell6079 PairReceipts.check6079 (by decide) (none),
    trivial⟩)
private theorem allAxes1273:PairRoute.Done (2:Fin 18) ⟨⟨58,58,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6080 0),
    (PairReceipts.route6080 1),
    (PairReceipts.route6080 2),
    (PairReceipts.route6080 3),
    (PairReceipts.route6080 4),
    (PairReceipts.route6080 5),
    (PairReceipts.route6080 6),
    (PairReceipts.route6080 7),
    (PairReceipts.route6080 8),
    (PairReceipts.route6080 9),
    (PairReceipts.route6080 10),
    (PairReceipts.route6080 11),
    PairLeaves.three PairReceipts.cell6092 PairReceipts.check6092 (by decide) (none),
    PairLeaves.three PairReceipts.cell6093 PairReceipts.check6093 (by decide) (none),
    PairLeaves.three PairReceipts.cell6094 PairReceipts.check6094 (by decide) (none),
    PairLeaves.three PairReceipts.cell6095 PairReceipts.check6095 (by decide) (none),
    PairLeaves.three PairReceipts.cell6096 PairReceipts.check6096 (by decide) (none),
    PairLeaves.three PairReceipts.cell6097 PairReceipts.check6097 (by decide) (none),
    trivial⟩)
private theorem allAxes1309:PairRoute.Done (2:Fin 18) ⟨⟨59,59,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6080 12),
    (PairReceipts.route6080 13),
    (PairReceipts.route6100 0),
    (PairReceipts.route6100 1),
    (PairReceipts.route6100 2),
    (PairReceipts.route6100 3),
    (PairReceipts.route6100 4),
    (PairReceipts.route6100 5),
    (PairReceipts.route6100 6),
    (PairReceipts.route6100 7),
    (PairReceipts.route6100 8),
    (PairReceipts.route6100 9),
    PairLeaves.three PairReceipts.cell6110 PairReceipts.check6110 (by decide) (none),
    PairLeaves.three PairReceipts.cell6111 PairReceipts.check6111 (by decide) (none),
    PairLeaves.three PairReceipts.cell6112 PairReceipts.check6112 (by decide) (none),
    PairLeaves.three PairReceipts.cell6113 PairReceipts.check6113 (by decide) (none),
    PairLeaves.three PairReceipts.cell6114 PairReceipts.check6114 (by decide) (none),
    PairLeaves.three PairReceipts.cell6115 PairReceipts.check6115 (by decide) (none),
    trivial⟩)
private theorem allAxes1345:PairRoute.Done (2:Fin 18) ⟨⟨60,60,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6100 10),
    (PairReceipts.route6100 11),
    (PairReceipts.route6100 12),
    (PairReceipts.route6100 13),
    (PairReceipts.route6120 0),
    (PairReceipts.route6120 1),
    (PairReceipts.route6120 2),
    (PairReceipts.route6120 3),
    (PairReceipts.route6120 4),
    (PairReceipts.route6120 5),
    (PairReceipts.route6120 6),
    (PairReceipts.route6120 7),
    PairLeaves.three PairReceipts.cell6128 PairReceipts.check6128 (by decide) (none),
    PairLeaves.three PairReceipts.cell6129 PairReceipts.check6129 (by decide) (none),
    PairLeaves.three PairReceipts.cell6130 PairReceipts.check6130 (by decide) (none),
    PairLeaves.three PairReceipts.cell6131 PairReceipts.check6131 (by decide) (none),
    PairLeaves.three PairReceipts.cell6132 PairReceipts.check6132 (by decide) (none),
    PairLeaves.three PairReceipts.cell6133 PairReceipts.check6133 (by decide) (none),
    trivial⟩)
private theorem allAxes1381:PairRoute.Done (2:Fin 18) ⟨⟨61,61,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6120 8),
    (PairReceipts.route6120 9),
    (PairReceipts.route6120 10),
    (PairReceipts.route6120 11),
    (PairReceipts.route6120 12),
    (PairReceipts.route6120 13),
    (PairReceipts.route6140 0),
    (PairReceipts.route6140 1),
    (PairReceipts.route6140 2),
    (PairReceipts.route6140 3),
    (PairReceipts.route6140 4),
    (PairReceipts.route6140 5),
    PairLeaves.three PairReceipts.cell6146 PairReceipts.check6146 (by decide) (none),
    PairLeaves.three PairReceipts.cell6147 PairReceipts.check6147 (by decide) (none),
    PairLeaves.three PairReceipts.cell6148 PairReceipts.check6148 (by decide) (none),
    PairLeaves.three PairReceipts.cell6149 PairReceipts.check6149 (by decide) (none),
    PairLeaves.three PairReceipts.cell6150 PairReceipts.check6150 (by decide) (none),
    PairLeaves.three PairReceipts.cell6151 PairReceipts.check6151 (by decide) (none),
    trivial⟩)
private theorem allAxes1417:PairRoute.Done (2:Fin 18) ⟨⟨62,62,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6140 6),
    (PairReceipts.route6140 7),
    (PairReceipts.route6140 8),
    (PairReceipts.route6140 9),
    (PairReceipts.route6140 10),
    (PairReceipts.route6140 11),
    (PairReceipts.route6140 12),
    (PairReceipts.route6140 13),
    (PairReceipts.route6160 0),
    (PairReceipts.route6160 1),
    (PairReceipts.route6160 2),
    (PairReceipts.route6160 3),
    PairLeaves.three PairReceipts.cell6164 PairReceipts.check6164 (by decide) (none),
    PairLeaves.three PairReceipts.cell6165 PairReceipts.check6165 (by decide) (none),
    PairLeaves.three PairReceipts.cell6166 PairReceipts.check6166 (by decide) (none),
    PairLeaves.three PairReceipts.cell6167 PairReceipts.check6167 (by decide) (none),
    PairLeaves.three PairReceipts.cell6168 PairReceipts.check6168 (by decide) (none),
    PairLeaves.three PairReceipts.cell6169 PairReceipts.check6169 (by decide) (none),
    trivial⟩)
private theorem allAxes1453:PairRoute.Done (2:Fin 18) ⟨⟨63,63,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6160 4),
    (PairReceipts.route6160 5),
    (PairReceipts.route6160 6),
    (PairReceipts.route6160 7),
    (PairReceipts.route6160 8),
    (PairReceipts.route6160 9),
    (PairReceipts.route6160 10),
    (PairReceipts.route6160 11),
    (PairReceipts.route6160 12),
    (PairReceipts.route6160 13),
    (PairReceipts.route6180 0),
    (PairReceipts.route6180 1),
    PairLeaves.three PairReceipts.cell6182 PairReceipts.check6182 (by decide) (none),
    PairLeaves.three PairReceipts.cell6183 PairReceipts.check6183 (by decide) (none),
    PairLeaves.three PairReceipts.cell6184 PairReceipts.check6184 (by decide) (none),
    PairLeaves.three PairReceipts.cell6185 PairReceipts.check6185 (by decide) (none),
    PairLeaves.three PairReceipts.cell6186 PairReceipts.check6186 (by decide) (none),
    PairLeaves.three PairReceipts.cell6187 PairReceipts.check6187 (by decide) (none),
    trivial⟩)
private def grade1454 := PairRoute.grade 62 allAxes1417 allAxes1453
private def grade1455 := PairRoute.grade 61 allAxes1381 grade1454
private def grade1456 := PairRoute.grade 60 allAxes1345 grade1455
private def grade1457 := PairRoute.grade 59 allAxes1309 grade1456
private def grade1458 := PairRoute.grade 58 allAxes1273 grade1457
private def grade1459 := PairRoute.grade 57 allAxes1237 grade1458
private def grade1460 := PairRoute.grade 56 allAxes1201 grade1459
private def grade1461 := PairRoute.grade 55 allAxes1165 grade1460
private def grade1462 := PairRoute.grade 54 allAxes1129 grade1461
private def grade1463 := PairRoute.grade 53 allAxes1093 grade1462
private def grade1464 := PairRoute.grade 52 allAxes1057 grade1463
private def grade1465 := PairRoute.grade 51 allAxes1021 grade1464
private def grade1466 := PairRoute.grade 50 allAxes985 grade1465
theorem case142: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,17,some 17⟩:=PairRoute.start _ grade1466
private theorem allAxes1504:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,18,some 18⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 18 ⟨
    (PairReceipts.route3360 7),
    (PairReceipts.route3360 8),
    (PairReceipts.route3360 9),
    (PairReceipts.route3360 10),
    (PairReceipts.route3360 11),
    (PairReceipts.route3360 12),
    (PairReceipts.route3360 13),
    (PairReceipts.route3360 14),
    (PairReceipts.route3360 15),
    (PairReceipts.route3360 16),
    (PairReceipts.route3360 17),
    (PairReceipts.route3360 18),
    (PairReceipts.route3360 19),
    (PairReceipts.route3380 0),
    (PairReceipts.route3380 1),
    (PairReceipts.route3380 2),
    (PairReceipts.route3380 3),
    (PairReceipts.route3380 4),
    (PairReceipts.route3380 5),
    trivial⟩)
theorem case143: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,18,some 18⟩:=PairRoute.start _ allAxes1504
private theorem allAxes1544:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route3340 7),
    (PairReceipts.route3340 8),
    (PairReceipts.route3340 9),
    (PairReceipts.route3340 10),
    (PairReceipts.route3340 11),
    (PairReceipts.route3340 12),
    (PairReceipts.route3340 13),
    (PairReceipts.route3340 14),
    (PairReceipts.route3340 15),
    (PairReceipts.route3340 16),
    (PairReceipts.route3340 17),
    (PairReceipts.route3340 18),
    (PairReceipts.route3340 19),
    (PairReceipts.route3360 0),
    (PairReceipts.route3360 1),
    (PairReceipts.route3360 2),
    (PairReceipts.route3360 3),
    (PairReceipts.route3360 4),
    (PairReceipts.route3360 5),
    (PairReceipts.route3360 6),
    trivial⟩)
theorem case144: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,19,some 19⟩:=PairRoute.start _ allAxes1544
private theorem allAxes1586:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,20,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route3320 6),
    (PairReceipts.route3320 7),
    (PairReceipts.route3320 8),
    (PairReceipts.route3320 9),
    (PairReceipts.route3320 10),
    (PairReceipts.route3320 11),
    (PairReceipts.route3320 12),
    (PairReceipts.route3320 13),
    (PairReceipts.route3320 14),
    (PairReceipts.route3320 15),
    (PairReceipts.route3320 16),
    (PairReceipts.route3320 17),
    (PairReceipts.route3320 18),
    (PairReceipts.route3320 19),
    (PairReceipts.route3340 0),
    (PairReceipts.route3340 1),
    (PairReceipts.route3340 2),
    (PairReceipts.route3340 3),
    (PairReceipts.route3340 4),
    (PairReceipts.route3340 5),
    (PairReceipts.route3340 6),
    trivial⟩)
theorem case145: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,20,some 20⟩:=PairRoute.start _ allAxes1586
private theorem allAxes1630:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,21,some 21⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 21 ⟨
    (PairReceipts.route3300 4),
    (PairReceipts.route3300 5),
    (PairReceipts.route3300 6),
    (PairReceipts.route3300 7),
    (PairReceipts.route3300 8),
    (PairReceipts.route3300 9),
    (PairReceipts.route3300 10),
    (PairReceipts.route3300 11),
    (PairReceipts.route3300 12),
    (PairReceipts.route3300 13),
    (PairReceipts.route3300 14),
    (PairReceipts.route3300 15),
    (PairReceipts.route3300 16),
    (PairReceipts.route3300 17),
    (PairReceipts.route3300 18),
    (PairReceipts.route3300 19),
    (PairReceipts.route3320 0),
    (PairReceipts.route3320 1),
    (PairReceipts.route3320 2),
    (PairReceipts.route3320 3),
    (PairReceipts.route3320 4),
    (PairReceipts.route3320 5),
    trivial⟩)
theorem case146: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,21,some 21⟩:=PairRoute.start _ allAxes1630
private theorem allAxes1676:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,22,some 22⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 22 ⟨
    (PairReceipts.route3280 1),
    (PairReceipts.route3280 2),
    (PairReceipts.route3280 3),
    (PairReceipts.route3280 4),
    (PairReceipts.route3280 5),
    (PairReceipts.route3280 6),
    (PairReceipts.route3280 7),
    (PairReceipts.route3280 8),
    (PairReceipts.route3280 9),
    (PairReceipts.route3280 10),
    (PairReceipts.route3280 11),
    (PairReceipts.route3280 12),
    (PairReceipts.route3280 13),
    (PairReceipts.route3280 14),
    (PairReceipts.route3280 15),
    (PairReceipts.route3280 16),
    (PairReceipts.route3280 17),
    (PairReceipts.route3280 18),
    (PairReceipts.route3280 19),
    (PairReceipts.route3300 0),
    (PairReceipts.route3300 1),
    (PairReceipts.route3300 2),
    (PairReceipts.route3300 3),
    trivial⟩)
theorem case147: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,22,some 22⟩:=PairRoute.start _ allAxes1676
private theorem allAxes1724:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,23,some 23⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 23 ⟨
    (PairReceipts.route3240 17),
    (PairReceipts.route3240 18),
    (PairReceipts.route3240 19),
    (PairReceipts.route3260 0),
    (PairReceipts.route3260 1),
    (PairReceipts.route3260 2),
    (PairReceipts.route3260 3),
    (PairReceipts.route3260 4),
    (PairReceipts.route3260 5),
    (PairReceipts.route3260 6),
    (PairReceipts.route3260 7),
    (PairReceipts.route3260 8),
    (PairReceipts.route3260 9),
    (PairReceipts.route3260 10),
    (PairReceipts.route3260 11),
    (PairReceipts.route3260 12),
    (PairReceipts.route3260 13),
    (PairReceipts.route3260 14),
    (PairReceipts.route3260 15),
    (PairReceipts.route3260 16),
    (PairReceipts.route3260 17),
    (PairReceipts.route3260 18),
    (PairReceipts.route3260 19),
    (PairReceipts.route3280 0),
    trivial⟩)
theorem case148: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,23,some 23⟩:=PairRoute.start _ allAxes1724
private def leaf1725 := (PairReceipts.route3240 16)
theorem case149: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,24,some 24⟩:=PairRoute.start _ leaf1725
end Research6969.HardFit3At140
