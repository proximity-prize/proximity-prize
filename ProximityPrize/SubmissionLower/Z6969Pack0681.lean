import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.Z6969Pack0680
import ProximityPrize.SubmissionLower.Z6969Pack0669
import ProximityPrize.SubmissionLower.Z6969Pack0641
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0640
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0667

set_option Elab.async false

-- Source: Research6969.HighDispatch10Band6
section Z6969Source1236
set_option autoImplicit true
namespace Research6969.HighDispatch10Band6
open NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem leaf1_129:Done (9:Fin 18) ⟨50,63,10,1,129,none⟩:=entire WholeRows.cell1528 WholeRows.checked1528
private theorem tail1_129 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 1 129:=leaf1_129
private theorem leaf1_0:Done (9:Fin 18) ⟨50,63,10,1,0,some 128⟩:=entire WholeRows.cell1527 WholeRows.checked1527
private theorem tail1_0 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 1 0:=join (leaf1_0) (tail1_129 needed)
private theorem leaf2_65:Done (9:Fin 18) ⟨50,63,10,2,65,none⟩:=entire WholeRows.cell1533 WholeRows.checked1533
private theorem tail2_65 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 2 65:=leaf2_65
private theorem leaf2_49 (needed:HighPendingSeed10.Required):Done (9:Fin 18) ⟨50,63,10,2,49,some 64⟩:=needed ⟨20,by decide⟩
private theorem tail2_49 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 2 49:=join (leaf2_49 needed) (tail2_65 needed)
private theorem leaf2_41:Done (9:Fin 18) ⟨50,63,10,2,41,some 48⟩:=entire WholeRows.cell1532 WholeRows.checked1532
private theorem tail2_41 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 2 41:=join (leaf2_41) (tail2_49 needed)
private theorem leaf2_33:Done (9:Fin 18) ⟨50,63,10,2,33,some 40⟩:=entire WholeRows.cell1531 WholeRows.checked1531
private theorem tail2_33 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 2 33:=join (leaf2_33) (tail2_41 needed)
private theorem leaf2_29:Done (9:Fin 18) ⟨50,63,10,2,29,some 32⟩:=entire WholeRows.cell1530 WholeRows.checked1530
private theorem tail2_29 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 2 29:=join (leaf2_29) (tail2_33 needed)
private theorem leaf2_25 (needed:HighPendingSeed10.Required):Done (9:Fin 18) ⟨50,63,10,2,25,some 28⟩:=needed ⟨19,by decide⟩
private theorem tail2_25 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 2 25:=join (leaf2_25 needed) (tail2_29 needed)
private theorem leaf2_21 (needed:HighPendingSeed10.Required):Done (9:Fin 18) ⟨50,63,10,2,21,some 24⟩:=needed ⟨18,by decide⟩
private theorem tail2_21 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 2 21:=join (leaf2_21 needed) (tail2_25 needed)
private theorem leaf2_17 (needed:HighPendingSeed10.Required):Done (9:Fin 18) ⟨50,63,10,2,17,some 20⟩:=needed ⟨17,by decide⟩
private theorem tail2_17 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 2 17:=join (leaf2_17 needed) (tail2_21 needed)
private theorem leaf2_13 (needed:HighPendingSeed10.Required):Done (9:Fin 18) ⟨50,63,10,2,13,some 16⟩:=needed ⟨16,by decide⟩
private theorem tail2_13 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 2 13:=join (leaf2_13 needed) (tail2_17 needed)
private theorem leaf2_9 (needed:HighPendingSeed10.Required):Done (9:Fin 18) ⟨50,63,10,2,9,some 12⟩:=needed ⟨15,by decide⟩
private theorem tail2_9 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 2 9:=join (leaf2_9 needed) (tail2_13 needed)
private theorem leaf2_0:Done (9:Fin 18) ⟨50,63,10,2,0,some 8⟩:=entire WholeRows.cell1529 WholeRows.checked1529
private theorem tail2_0 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 2 0:=join (leaf2_0) (tail2_9 needed)
private theorem leaf3_129:Done (9:Fin 18) ⟨50,63,10,3,129,none⟩:=entire WholeRows.cell1544 WholeRows.checked1544
private theorem tail3_129 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 129:=leaf3_129
private theorem leaf3_65:Done (9:Fin 18) ⟨50,63,10,3,65,some 128⟩:=entire WholeRows.cell1543 WholeRows.checked1543
private theorem tail3_65 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 65:=join (leaf3_65) (tail3_129 needed)
private theorem leaf3_49:Done (9:Fin 18) ⟨50,63,10,3,49,some 64⟩:=power _ 385979 (by decide) PowerReceipts.power48 (by decide) (by decide) (by decide)
private theorem tail3_49 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 49:=join (leaf3_49) (tail3_65 needed)
private theorem leaf3_41:Done (9:Fin 18) ⟨50,63,10,3,41,some 48⟩:=entire WholeRows.cell1542 WholeRows.checked1542
private theorem tail3_41 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 41:=join (leaf3_41) (tail3_49 needed)
private theorem leaf3_33:Done (9:Fin 18) ⟨50,63,10,3,33,some 40⟩:=entire WholeRows.cell1541 WholeRows.checked1541
private theorem tail3_33 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 33:=join (leaf3_33) (tail3_41 needed)
private theorem leaf3_25:Done (9:Fin 18) ⟨50,63,10,3,25,some 32⟩:=
  NormalRoute.splitSeed 31 (entire WholeRows.cell1540 WholeRows.checked1540) (entire WholeRows.cell1540b WholeRows.checked1540b)
private theorem tail3_25 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 25:=join (leaf3_25) (tail3_33 needed)
private theorem leaf3_21:Done (9:Fin 18) ⟨50,63,10,3,21,some 24⟩:=entire WholeRows.cell1539 WholeRows.checked1539
private theorem tail3_21 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 21:=join (leaf3_21) (tail3_25 needed)
private theorem leaf3_17:Done (9:Fin 18) ⟨50,63,10,3,17,some 20⟩:=entire WholeRows.cell1538 WholeRows.checked1538
private theorem tail3_17 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 17:=join (leaf3_17) (tail3_21 needed)
private theorem leaf3_13:Done (9:Fin 18) ⟨50,63,10,3,13,some 16⟩:=entire WholeRows.cell1537 WholeRows.checked1537
private theorem tail3_13 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 13:=join (leaf3_13) (tail3_17 needed)
private theorem leaf3_9:Done (9:Fin 18) ⟨50,63,10,3,9,some 12⟩:=entire WholeRows.cell1536 WholeRows.checked1536
private theorem tail3_9 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 9:=join (leaf3_9) (tail3_13 needed)
private theorem leaf3_4:Done (9:Fin 18) ⟨50,63,10,3,4,some 8⟩:=entire WholeRows.cell1535 WholeRows.checked1535
private theorem tail3_4 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 4:=join (leaf3_4) (tail3_9 needed)
private theorem leaf3_0:Done (9:Fin 18) ⟨50,63,10,3,0,some 3⟩:=entire WholeRows.cell1534 WholeRows.checked1534
private theorem tail3_0 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 0:=join (leaf3_0) (tail3_4 needed)
theorem allDegrees (needed:HighPendingSeed10.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (9:Fin 18) 50 63 10 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6969.HighDispatch10Band6
end Z6969Source1236

-- Source: Research6969.HighDispatch10Band7
section Z6969Source1237
set_option autoImplicit true
namespace Research6969.HighDispatch10Band7
open NormalRoute WholeRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false

theorem allDegrees (needed:HighPendingSeed10.Required) (a:ℕ) (lo:0<a) (hi:a≤2):
    Tail (9:Fin 18) 64 650 12 a 0:=by
  interval_cases a
  · exact
      join (entire cell1545 checked1545) <|
      entire cell1546 checked1546
  · exact
      join (entire cell1547 checked1547) <|
      join (needed ⟨21,by decide⟩) <|
      join (needed ⟨22,by decide⟩) <|
      join (needed ⟨23,by decide⟩) <|
      join (needed ⟨24,by decide⟩) <|
      join (needed ⟨25,by decide⟩) <|
      join (needed ⟨26,by decide⟩) <|
      join (needed ⟨27,by decide⟩) <|
      join (needed ⟨28,by decide⟩) <|
      join (needed ⟨29,by decide⟩) <|
      entire cell1548 checked1548
end Research6969.HighDispatch10Band7
end Z6969Source1237

-- Source: Research6969.HighDispatchSeed10
section Z6969Source1238
set_option autoImplicit true
namespace Research6969.HighDispatchSeed10
open NormalRoute HighPackets
open TransitionPacket.NormalCatalogue
theorem count (need:HighPendingSeed10.Required) (s:State (9:Fin 18)):s.labels.card≤CertifiedCell.target:=by
  let b:=TransitionClassification.band s.f.natDegree
  have first:=TransitionClassification.lower_bound s.high
  have last:=OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤TransitionClassification.maxGraph b): Tail (9:Fin 18) (TransitionClassification.grade b) (OrdinaryComplete.upper (savedMainGrade 9+savedRescueGrade 9) b) (TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch10Band0.allDegrees need a p h
    · exact HighDispatch10Band1.allDegrees need a p h
    · exact HighDispatch10Band2.allDegrees need a p h
    · exact HighDispatch10Band3.allDegrees need a p h
    · exact HighDispatch10Band4.allDegrees need a p h
    · exact HighDispatch10Band5.allDegrees need a p h
    · exact HighDispatch10Band6.allDegrees need a p h
    · exact HighDispatch10Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6969.HighDispatchSeed10
end Z6969Source1238

-- Source: Research6969.HighPendingSeed11
section Z6969Source1239
set_option autoImplicit true
namespace Research6969.HighPendingSeed11
open NormalRoute
def regions:Array Region:=#[⟨28,32,9,2,13,some 16⟩,⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 24⟩,⟨28,32,9,2,25,some 28⟩,⟨33,40,9,2,13,some 16⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 24⟩,⟨33,40,9,2,25,some 28⟩,⟨41,49,9,2,13,some 16⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 24⟩,⟨41,49,9,2,25,some 28⟩,⟨50,63,10,2,13,some 16⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 24⟩,⟨50,63,10,2,25,some 28⟩,⟨50,63,10,2,49,some 64⟩,⟨64,654,12,2,9,some 12⟩,⟨64,654,12,2,13,some 16⟩,⟨64,654,12,2,17,some 20⟩,⟨64,654,12,2,21,some 24⟩,⟨64,654,12,2,25,some 28⟩,⟨64,654,12,2,29,some 32⟩,⟨64,654,12,2,33,some 40⟩,⟨64,654,12,2,41,some 48⟩,⟨64,654,12,2,49,some 56⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (10:Fin 18) (atIndex j)
end Research6969.HighPendingSeed11
end Z6969Source1239

-- Source: Research6969.SharedGradeInvoice11
section Z6969Source1240
set_option autoImplicit true
namespace Research6969.SharedGradeInvoice11
open NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
theorem counted (r : Region) (grade : r.gradeHi ≤ 28) : Done (10 : Fin 18) r := by
  apply small r 28 grade (by decide) (by decide +kernel) (by decide +kernel)
  change ∀ i j : Fin 29, i.val + j.val ≤ 28 → JointLedger.Pass SmallCertificates.primary11 SmallCertificates.rescue11
    (JointRouted.seedWeight 133482 11) (JointRouted.ordWeight 133482 1) CertifiedCell.target i.val j.val
  rw [SmallCertificates.seed_price11, SmallCertificates.ordinate_price]
  exact ExtendedJointBills.bill11
end Research6969.SharedGradeInvoice11
end Z6969Source1240

-- Source: Research6969.HighDispatch11Band0
section Z6969Source1241
set_option autoImplicit true
namespace Research6969.HighDispatch11Band0
open NormalRoute
theorem allDegrees (_ : HighPendingSeed11.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (10 : Fin 18) 22 22 9 a 0 :=
  SharedGradeInvoice11.counted _ (by decide : 22 ≤ 28)
end Research6969.HighDispatch11Band0
end Z6969Source1241

-- Source: Research6969.HighDispatch11Band1
section Z6969Source1242
set_option autoImplicit true
namespace Research6969.HighDispatch11Band1
open NormalRoute
theorem allDegrees (_ : HighPendingSeed11.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (10 : Fin 18) 23 24 9 a 0 :=
  SharedGradeInvoice11.counted _ (by decide : 24 ≤ 28)
end Research6969.HighDispatch11Band1
end Z6969Source1242

-- Source: Research6969.HighDispatch11Band2
section Z6969Source1243
set_option autoImplicit true
namespace Research6969.HighDispatch11Band2
open NormalRoute
theorem allDegrees (_ : HighPendingSeed11.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 5) :
    Tail (10 : Fin 18) 25 27 9 a 0 :=
  SharedGradeInvoice11.counted _ (by decide : 27 ≤ 28)
end Research6969.HighDispatch11Band2
end Z6969Source1243

-- Source: Research6969.WholeGraphCases050
section Z6969Source1244
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell1600: Row := ⟨25,27,9,3,4,some 12,[test671],.surface⟩
theorem checked1600: cell1600.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1601: Row := ⟨25,27,9,3,13,some 16,[test770],.surface⟩
theorem checked1601: cell1601.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1602: Row := ⟨25,27,9,3,17,some 24,[test821],.marked⟩
theorem checked1602: cell1602.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1603: Row := ⟨25,27,9,3,25,some 96,[test924],.marked⟩
theorem checked1603: cell1603.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1604: Row := ⟨25,27,9,3,97,some 512,[test1149],.marked⟩
theorem checked1604: cell1604.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1605: Row := ⟨25,27,9,3,513,some 2048,[test1154,test1155],.marked⟩
theorem checked1605: cell1605.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1606: Row := ⟨25,27,9,3,2049,none,[test1158],.excluded⟩
theorem checked1606: cell1606.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1607: Row := ⟨25,27,9,4,0,some 3,[],.surface⟩
theorem checked1607: cell1607.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1608: Row := ⟨25,27,9,4,4,some 96,[test1237],.marked⟩
theorem checked1608: cell1608.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1609: Row := ⟨25,27,9,4,97,some 512,[test1372],.marked⟩
theorem checked1609: cell1609.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1610: Row := ⟨25,27,9,4,513,some 1024,[test1377,test1378],.marked⟩
theorem checked1610: cell1610.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1611: Row := ⟨25,27,9,4,1025,some 2048,[test1379,test1380],.marked⟩
theorem checked1611: cell1611.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1612: Row := ⟨25,27,9,4,2049,none,[test1382],.excluded⟩
theorem checked1612: cell1612.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1613: Row := ⟨25,27,9,5,0,some 3,[],.surface⟩
theorem checked1613: cell1613.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1614: Row := ⟨28,32,9,1,0,some 128,[],.affine⟩
theorem checked1614: cell1614.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1615: Row := ⟨28,32,9,1,129,some 1024,[test11,test12],.marked⟩
theorem checked1615: cell1615.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1616: Row := ⟨28,32,9,1,1025,none,[test18],.excluded⟩
theorem checked1616: cell1616.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1617: Row := ⟨28,32,9,2,0,some 12,[],.surface⟩
theorem checked1617: cell1617.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1618: Row := ⟨28,32,9,2,29,some 40,[test39],.surface⟩
theorem checked1618: cell1618.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1619: Row := ⟨28,32,9,2,41,some 128,[test50],.marked⟩
theorem checked1619: cell1619.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1620: Row := ⟨28,32,9,2,129,some 1024,[test90,test91],.marked⟩
theorem checked1620: cell1620.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1621: Row := ⟨28,32,9,2,1025,none,[test96],.excluded⟩
theorem checked1621: cell1621.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1622: Row := ⟨28,32,9,3,0,some 3,[],.surface⟩
theorem checked1622: cell1622.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1623: Row := ⟨28,32,9,3,4,some 12,[test671],.surface⟩
theorem checked1623: cell1623.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1624: Row := ⟨28,32,9,3,13,some 16,[test770],.surface⟩
theorem checked1624: cell1624.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1625: Row := ⟨28,32,9,3,17,some 20,[test821],.surface⟩
theorem checked1625: cell1625.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1626: Row := ⟨28,32,9,3,21,some 28,[test869],.surface⟩
theorem checked1626: cell1626.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1627: Row := ⟨28,32,9,3,29,some 64,[test977],.marked⟩
theorem checked1627: cell1627.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1628: Row := ⟨28,32,9,3,65,some 256,[test1147],.marked⟩
theorem checked1628: cell1628.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1629: Row := ⟨28,32,9,3,257,some 1024,[test1152,test1153],.marked⟩
theorem checked1629: cell1629.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1630: Row := ⟨28,32,9,3,1025,none,[test1156],.excluded⟩
theorem checked1630: cell1630.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1631: Row := ⟨28,32,9,4,0,some 3,[],.surface⟩
theorem checked1631: cell1631.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1244

-- Source: Research6969.WholeGraphCases051
section Z6969Source1245
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell1632: Row := ⟨28,32,9,4,4,some 32,[test1237],.marked⟩
theorem checked1632: cell1632.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1633: Row := ⟨28,32,9,4,33,some 128,[test1298],.marked⟩
theorem checked1633: cell1633.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1634: Row := ⟨28,32,9,4,129,some 512,[test1374],.marked⟩
theorem checked1634: cell1634.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1635: Row := ⟨28,32,9,4,513,some 1024,[test1377,test1378],.marked⟩
theorem checked1635: cell1635.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1636: Row := ⟨28,32,9,4,1025,none,[test1379],.excluded⟩
theorem checked1636: cell1636.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1637: Row := ⟨33,40,9,1,0,some 128,[],.affine⟩
theorem checked1637: cell1637.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1638: Row := ⟨33,40,9,1,129,none,[test12],.excluded⟩
theorem checked1638: cell1638.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1639: Row := ⟨33,40,9,2,0,some 12,[],.surface⟩
theorem checked1639: cell1639.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1640: Row := ⟨33,40,9,2,29,some 40,[test39],.surface⟩
theorem checked1640: cell1640.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1641: Row := ⟨33,40,9,2,41,some 64,[test50],.marked⟩
theorem checked1641: cell1641.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1642: Row := ⟨33,40,9,2,65,some 128,[test87],.marked⟩
theorem checked1642: cell1642.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1643: Row := ⟨33,40,9,2,129,none,[test91],.excluded⟩
theorem checked1643: cell1643.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1644: Row := ⟨33,40,9,3,0,some 3,[],.surface⟩
theorem checked1644: cell1644.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1645: Row := ⟨33,40,9,3,4,some 12,[test671],.surface⟩
theorem checked1645: cell1645.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1646: Row := ⟨33,40,9,3,13,some 16,[test770],.surface⟩
theorem checked1646: cell1646.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1647: Row := ⟨33,40,9,3,17,some 20,[test821],.surface⟩
theorem checked1647: cell1647.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1648: Row := ⟨33,40,9,3,21,some 24,[test869],.surface⟩
theorem checked1648: cell1648.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1649: Row := ⟨33,40,9,3,25,some 32,[test924],.surface⟩
theorem checked1649: cell1649.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1650: Row := ⟨33,40,9,3,33,some 64,[test1029],.marked⟩
theorem checked1650: cell1650.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1651: Row := ⟨33,40,9,3,65,some 128,[test1147],.marked⟩
theorem checked1651: cell1651.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1652: Row := ⟨33,40,9,3,129,some 512,[test1150,test1151],.marked⟩
theorem checked1652: cell1652.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1653: Row := ⟨33,40,9,3,513,none,[test1154],.excluded⟩
theorem checked1653: cell1653.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1654: Row := ⟨33,40,9,4,0,some 3,[],.surface⟩
theorem checked1654: cell1654.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1655: Row := ⟨33,40,9,4,4,some 20,[test1237],.surface⟩
theorem checked1655: cell1655.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1656: Row := ⟨33,40,9,4,21,some 48,[test1270],.marked⟩
theorem checked1656: cell1656.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1657: Row := ⟨33,40,9,4,49,some 128,[test1353],.marked⟩
theorem checked1657: cell1657.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1658: Row := ⟨33,40,9,4,129,some 512,[test1373,test1374],.marked⟩
theorem checked1658: cell1658.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1659: Row := ⟨33,40,9,4,513,none,[test1377],.excluded⟩
theorem checked1659: cell1659.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1660: Row := ⟨41,49,9,1,0,some 128,[],.affine⟩
theorem checked1660: cell1660.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1661: Row := ⟨41,49,9,1,129,none,[test12],.excluded⟩
theorem checked1661: cell1661.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1662: Row := ⟨41,49,9,2,0,some 12,[],.surface⟩
theorem checked1662: cell1662.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1663: Row := ⟨41,49,9,2,29,some 40,[test39],.surface⟩
theorem checked1663: cell1663.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1245

-- Source: Research6969.HighDispatch11Band3
section Z6969Source1246
set_option autoImplicit true
namespace Research6969.HighDispatch11Band3
open NormalRoute WholeRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false

theorem allDegrees (needed:HighPendingSeed11.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (10:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact
      join (entire cell1614 checked1614) <|
      join (entire cell1615 checked1615) <|
      entire cell1616 checked1616
  · exact
      join (entire cell1617 checked1617) <|
      join (needed ⟨0,by decide⟩) <|
      join (needed ⟨1,by decide⟩) <|
      join (needed ⟨2,by decide⟩) <|
      join (needed ⟨3,by decide⟩) <|
      join (entire cell1618 checked1618) <|
      join (entire cell1619 checked1619) <|
      join (entire cell1620 checked1620) <|
      entire cell1621 checked1621
  · exact
      join (entire cell1622 checked1622) <|
      join (entire cell1623 checked1623) <|
      join (entire cell1624 checked1624) <|
      join (entire cell1625 checked1625) <|
      join (entire cell1626 checked1626) <|
      join (entire cell1627 checked1627) <|
      join (entire cell1628 checked1628) <|
      join (entire cell1629 checked1629) <|
      entire cell1630 checked1630
  · exact
      join (entire cell1631 checked1631) <|
      join (entire cell1632 checked1632) <|
      join (entire cell1633 checked1633) <|
      join (entire cell1634 checked1634) <|
      join (entire cell1635 checked1635) <|
      entire cell1636 checked1636
end Research6969.HighDispatch11Band3
end Z6969Source1246

-- Source: Research6969.HighDispatch11Band4
section Z6969Source1247
set_option autoImplicit true
namespace Research6969.HighDispatch11Band4
open NormalRoute WholeRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false

theorem allDegrees (needed:HighPendingSeed11.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (10:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact
      join (entire cell1637 checked1637) <|
      entire cell1638 checked1638
  · exact
      join (entire cell1639 checked1639) <|
      join (needed ⟨4,by decide⟩) <|
      join (needed ⟨5,by decide⟩) <|
      join (needed ⟨6,by decide⟩) <|
      join (needed ⟨7,by decide⟩) <|
      join (entire cell1640 checked1640) <|
      join (entire cell1641 checked1641) <|
      join (entire cell1642 checked1642) <|
      entire cell1643 checked1643
  · exact
      join (entire cell1644 checked1644) <|
      join (entire cell1645 checked1645) <|
      join (entire cell1646 checked1646) <|
      join (entire cell1647 checked1647) <|
      join (entire cell1648 checked1648) <|
      join (entire cell1649 checked1649) <|
      join (entire cell1650 checked1650) <|
      join (entire cell1651 checked1651) <|
      join (entire cell1652 checked1652) <|
      entire cell1653 checked1653
  · exact
      join (entire cell1654 checked1654) <|
      join (entire cell1655 checked1655) <|
      join (entire cell1656 checked1656) <|
      join (entire cell1657 checked1657) <|
      join (entire cell1658 checked1658) <|
      entire cell1659 checked1659
end Research6969.HighDispatch11Band4
end Z6969Source1247
