import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.Z6969Pack0640
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0667

set_option Elab.async false

-- Source: Research6969.HighPendingSeed10
section Z6969Source1224
set_option autoImplicit true
namespace Research6969.HighPendingSeed10
open NormalRoute
def regions:Array Region:=#[⟨28,32,9,2,9,some 12⟩,⟨28,32,9,2,13,some 16⟩,⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 24⟩,⟨28,32,9,2,25,some 28⟩,⟨33,40,9,2,9,some 12⟩,⟨33,40,9,2,13,some 16⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 24⟩,⟨33,40,9,2,25,some 28⟩,⟨41,49,9,2,9,some 12⟩,⟨41,49,9,2,13,some 16⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 24⟩,⟨41,49,9,2,25,some 28⟩,⟨50,63,10,2,9,some 12⟩,⟨50,63,10,2,13,some 16⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 24⟩,⟨50,63,10,2,25,some 28⟩,⟨50,63,10,2,49,some 64⟩,⟨64,650,12,2,9,some 12⟩,⟨64,650,12,2,13,some 16⟩,⟨64,650,12,2,17,some 20⟩,⟨64,650,12,2,21,some 24⟩,⟨64,650,12,2,25,some 28⟩,⟨64,650,12,2,29,some 32⟩,⟨64,650,12,2,33,some 40⟩,⟨64,650,12,2,41,some 48⟩,⟨64,650,12,2,49,some 56⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (9:Fin 18) (atIndex j)
end Research6969.HighPendingSeed10
end Z6969Source1224

-- Source: Research6969.SharedGradeInvoice10
section Z6969Source1225
set_option autoImplicit true
namespace Research6969.SharedGradeInvoice10
open NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
theorem counted (r : Region) (grade : r.gradeHi ≤ 27) : Done (9 : Fin 18) r := by
  apply small r 27 grade (by decide) (by decide +kernel) (by decide +kernel)
  change ∀ i j : Fin 28, i.val + j.val ≤ 27 → JointLedger.Pass SmallCertificates.primary10 SmallCertificates.rescue10
    (JointRouted.seedWeight 133482 10) (JointRouted.ordWeight 133482 1) CertifiedCell.target i.val j.val
  rw [SmallCertificates.seed_price10, SmallCertificates.ordinate_price]
  exact ExtendedJointBills.bill10
end Research6969.SharedGradeInvoice10
end Z6969Source1225

-- Source: Research6969.HighDispatch10Band0
section Z6969Source1226
set_option autoImplicit true
namespace Research6969.HighDispatch10Band0
open NormalRoute
theorem allDegrees (_ : HighPendingSeed10.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (9 : Fin 18) 22 22 9 a 0 :=
  SharedGradeInvoice10.counted _ (by decide : 22 ≤ 27)
end Research6969.HighDispatch10Band0
end Z6969Source1226

-- Source: Research6969.HighDispatch10Band1
section Z6969Source1227
set_option autoImplicit true
namespace Research6969.HighDispatch10Band1
open NormalRoute
theorem allDegrees (_ : HighPendingSeed10.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (9 : Fin 18) 23 24 9 a 0 :=
  SharedGradeInvoice10.counted _ (by decide : 24 ≤ 27)
end Research6969.HighDispatch10Band1
end Z6969Source1227

-- Source: Research6969.HighDispatch10Band2
section Z6969Source1228
set_option autoImplicit true
namespace Research6969.HighDispatch10Band2
open NormalRoute
theorem allDegrees (_ : HighPendingSeed10.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 5) :
    Tail (9 : Fin 18) 25 27 9 a 0 :=
  SharedGradeInvoice10.counted _ (by decide : 27 ≤ 27)
end Research6969.HighDispatch10Band2
end Z6969Source1228

-- Source: Research6969.WholeGraphCases045
section Z6969Source1229
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell1440: Row := ⟨25,27,9,1,0,some 128,[],.affine⟩
theorem checked1440: cell1440.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1441: Row := ⟨25,27,9,1,129,some 1024,[test11,test12],.marked⟩
theorem checked1441: cell1441.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1442: Row := ⟨25,27,9,1,1025,none,[test18],.excluded⟩
theorem checked1442: cell1442.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1443: Row := ⟨25,27,9,2,0,some 8,[],.surface⟩
theorem checked1443: cell1443.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1444: Row := ⟨25,27,9,2,29,some 48,[test39],.marked⟩
theorem checked1444: cell1444.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1445: Row := ⟨25,27,9,2,49,some 256,[test62],.marked⟩
theorem checked1445: cell1445.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1446: Row := ⟨25,27,9,2,257,some 2048,[test92,test93],.marked⟩
theorem checked1446: cell1446.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1447: Row := ⟨25,27,9,2,2049,none,[test99],.excluded⟩
theorem checked1447: cell1447.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1448: Row := ⟨25,27,9,3,0,some 3,[],.surface⟩
theorem checked1448: cell1448.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1449: Row := ⟨25,27,9,3,4,some 12,[test671],.surface⟩
theorem checked1449: cell1449.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1450: Row := ⟨25,27,9,3,13,some 16,[test770],.surface⟩
theorem checked1450: cell1450.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1451: Row := ⟨25,27,9,3,17,some 20,[test821],.surface⟩
theorem checked1451: cell1451.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1452: Row := ⟨25,27,9,3,21,some 48,[test869],.marked⟩
theorem checked1452: cell1452.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1453: Row := ⟨25,27,9,3,49,some 256,[test1142],.marked⟩
theorem checked1453: cell1453.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1454: Row := ⟨25,27,9,3,257,some 1024,[test1152,test1153],.marked⟩
theorem checked1454: cell1454.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1455: Row := ⟨25,27,9,3,1025,none,[test1156],.excluded⟩
theorem checked1455: cell1455.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1456: Row := ⟨25,27,9,4,0,some 3,[],.surface⟩
theorem checked1456: cell1456.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1457: Row := ⟨25,27,9,4,4,some 96,[test1237],.marked⟩
theorem checked1457: cell1457.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1458: Row := ⟨25,27,9,4,97,some 512,[test1372],.marked⟩
theorem checked1458: cell1458.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1459: Row := ⟨25,27,9,4,513,some 1024,[test1377,test1378],.marked⟩
theorem checked1459: cell1459.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1460: Row := ⟨25,27,9,4,1025,some 2048,[test1379,test1380],.marked⟩
theorem checked1460: cell1460.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1461: Row := ⟨25,27,9,4,2049,none,[test1382],.excluded⟩
theorem checked1461: cell1461.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1462: Row := ⟨25,27,9,5,0,some 1,[],.surface⟩
theorem checked1462: cell1462.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1463: Row := ⟨28,32,9,1,0,some 128,[],.affine⟩
theorem checked1463: cell1463.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1464: Row := ⟨28,32,9,1,129,some 1024,[test11,test12],.marked⟩
theorem checked1464: cell1464.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1465: Row := ⟨28,32,9,1,1025,none,[test18],.excluded⟩
theorem checked1465: cell1465.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1466: Row := ⟨28,32,9,2,0,some 8,[],.surface⟩
theorem checked1466: cell1466.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1467: Row := ⟨28,32,9,2,29,some 40,[test39],.surface⟩
theorem checked1467: cell1467.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1468: Row := ⟨28,32,9,2,41,some 128,[test50],.marked⟩
theorem checked1468: cell1468.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1469: Row := ⟨28,32,9,2,129,some 512,[test90,test91],.marked⟩
theorem checked1469: cell1469.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1470: Row := ⟨28,32,9,2,513,none,[test94],.excluded⟩
theorem checked1470: cell1470.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1471: Row := ⟨28,32,9,3,0,some 3,[],.surface⟩
theorem checked1471: cell1471.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1229

-- Source: Research6969.WholeGraphCases046
section Z6969Source1230
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell1472: Row := ⟨28,32,9,3,4,some 12,[test671],.surface⟩
theorem checked1472: cell1472.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1473: Row := ⟨28,32,9,3,13,some 16,[test770],.surface⟩
theorem checked1473: cell1473.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1474: Row := ⟨28,32,9,3,17,some 20,[test821],.surface⟩
theorem checked1474: cell1474.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1475: Row := ⟨28,32,9,3,21,some 24,[test869],.surface⟩
theorem checked1475: cell1475.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1476: Row := ⟨28,32,9,3,25,some 48,[test924],.marked⟩
theorem checked1476: cell1476.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1477: Row := ⟨28,32,9,3,49,some 256,[test1142],.marked⟩
theorem checked1477: cell1477.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1478: Row := ⟨28,32,9,3,257,some 1024,[test1152,test1153],.marked⟩
theorem checked1478: cell1478.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1479: Row := ⟨28,32,9,3,1025,none,[test1156],.excluded⟩
theorem checked1479: cell1479.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1480: Row := ⟨28,32,9,4,0,some 3,[],.surface⟩
theorem checked1480: cell1480.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1481: Row := ⟨28,32,9,4,4,some 32,[test1237],.marked⟩
theorem checked1481: cell1481.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1482: Row := ⟨28,32,9,4,33,some 128,[test1298],.marked⟩
theorem checked1482: cell1482.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1483: Row := ⟨28,32,9,4,129,some 512,[test1374],.marked⟩
theorem checked1483: cell1483.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1484: Row := ⟨28,32,9,4,513,some 1024,[test1377,test1378],.marked⟩
theorem checked1484: cell1484.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1485: Row := ⟨28,32,9,4,1025,none,[test1379],.excluded⟩
theorem checked1485: cell1485.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1486: Row := ⟨33,40,9,1,0,some 128,[],.affine⟩
theorem checked1486: cell1486.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1487: Row := ⟨33,40,9,1,129,none,[test12],.excluded⟩
theorem checked1487: cell1487.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1488: Row := ⟨33,40,9,2,0,some 8,[],.surface⟩
theorem checked1488: cell1488.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1489: Row := ⟨33,40,9,2,29,some 40,[test39],.surface⟩
theorem checked1489: cell1489.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1490: Row := ⟨33,40,9,2,41,some 64,[test50],.marked⟩
theorem checked1490: cell1490.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1491: Row := ⟨33,40,9,2,65,some 128,[test87],.marked⟩
theorem checked1491: cell1491.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1492: Row := ⟨33,40,9,2,129,none,[test91],.excluded⟩
theorem checked1492: cell1492.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1493: Row := ⟨33,40,9,3,0,some 3,[],.surface⟩
theorem checked1493: cell1493.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1494: Row := ⟨33,40,9,3,4,some 12,[test671],.surface⟩
theorem checked1494: cell1494.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1495: Row := ⟨33,40,9,3,13,some 16,[test770],.surface⟩
theorem checked1495: cell1495.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1496: Row := ⟨33,40,9,3,17,some 20,[test821],.surface⟩
theorem checked1496: cell1496.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1497: Row := ⟨33,40,9,3,21,some 24,[test869],.surface⟩
theorem checked1497: cell1497.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1498: Row := ⟨33,40,9,3,25,some 32,[test924],.surface⟩
theorem checked1498: cell1498.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1499: Row := ⟨33,40,9,3,33,some 64,[test1029],.marked⟩
theorem checked1499: cell1499.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1500: Row := ⟨33,40,9,3,65,some 128,[test1147],.marked⟩
theorem checked1500: cell1500.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1501: Row := ⟨33,40,9,3,129,some 512,[test1150,test1151],.marked⟩
theorem checked1501: cell1501.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1502: Row := ⟨33,40,9,3,513,none,[test1154],.excluded⟩
theorem checked1502: cell1502.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1503: Row := ⟨33,40,9,4,0,some 3,[],.surface⟩
theorem checked1503: cell1503.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1230

-- Source: Research6969.HighDispatch10Band3
section Z6969Source1231
set_option autoImplicit true
namespace Research6969.HighDispatch10Band3
open NormalRoute WholeRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false

theorem allDegrees (needed:HighPendingSeed10.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (9:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact
      join (entire cell1463 checked1463) <|
      join (entire cell1464 checked1464) <|
      entire cell1465 checked1465
  · exact
      join (entire cell1466 checked1466) <|
      join (needed ⟨0,by decide⟩) <|
      join (needed ⟨1,by decide⟩) <|
      join (needed ⟨2,by decide⟩) <|
      join (needed ⟨3,by decide⟩) <|
      join (needed ⟨4,by decide⟩) <|
      join (entire cell1467 checked1467) <|
      join (entire cell1468 checked1468) <|
      join (entire cell1469 checked1469) <|
      entire cell1470 checked1470
  · exact
      join (entire cell1471 checked1471) <|
      join (entire cell1472 checked1472) <|
      join (entire cell1473 checked1473) <|
      join (entire cell1474 checked1474) <|
      join (entire cell1475 checked1475) <|
      join (entire cell1476 checked1476) <|
      join (entire cell1477 checked1477) <|
      join (entire cell1478 checked1478) <|
      entire cell1479 checked1479
  · exact
      join (entire cell1480 checked1480) <|
      join (entire cell1481 checked1481) <|
      join (entire cell1482 checked1482) <|
      join (entire cell1483 checked1483) <|
      join (entire cell1484 checked1484) <|
      entire cell1485 checked1485
end Research6969.HighDispatch10Band3
end Z6969Source1231

-- Source: Research6969.WholeGraphCases047
section Z6969Source1232
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell1504: Row := ⟨33,40,9,4,4,some 20,[test1237],.surface⟩
theorem checked1504: cell1504.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1505: Row := ⟨33,40,9,4,21,some 48,[test1270],.marked⟩
theorem checked1505: cell1505.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1506: Row := ⟨33,40,9,4,49,some 128,[test1353],.marked⟩
theorem checked1506: cell1506.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1507: Row := ⟨33,40,9,4,129,some 512,[test1373,test1374],.marked⟩
theorem checked1507: cell1507.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1508: Row := ⟨33,40,9,4,513,none,[test1377],.excluded⟩
theorem checked1508: cell1508.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1509: Row := ⟨41,49,9,1,0,some 128,[],.affine⟩
theorem checked1509: cell1509.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1510: Row := ⟨41,49,9,1,129,none,[test12],.excluded⟩
theorem checked1510: cell1510.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1511: Row := ⟨41,49,9,2,0,some 8,[],.surface⟩
theorem checked1511: cell1511.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1512: Row := ⟨41,49,9,2,29,some 40,[test39],.surface⟩
theorem checked1512: cell1512.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1513: Row := ⟨41,49,9,2,41,some 48,[test50],.surface⟩
theorem checked1513: cell1513.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1514: Row := ⟨41,49,9,2,49,some 64,[test62],.marked⟩
theorem checked1514: cell1514.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1515: Row := ⟨41,49,9,2,65,some 128,[test86,test87],.marked⟩
theorem checked1515: cell1515.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1516: Row := ⟨41,49,9,2,129,none,[test91],.excluded⟩
theorem checked1516: cell1516.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1517: Row := ⟨41,49,9,3,0,some 3,[],.surface⟩
theorem checked1517: cell1517.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1518: Row := ⟨41,49,9,3,4,some 12,[test671],.surface⟩
theorem checked1518: cell1518.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1519: Row := ⟨41,49,9,3,13,some 16,[test770],.surface⟩
theorem checked1519: cell1519.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1520: Row := ⟨41,49,9,3,17,some 20,[test821],.surface⟩
theorem checked1520: cell1520.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1521: Row := ⟨41,49,9,3,21,some 24,[test869],.surface⟩
theorem checked1521: cell1521.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1522: Row := ⟨41,49,9,3,25,some 32,[test924],.surface⟩
theorem checked1522: cell1522.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1523: Row := ⟨41,49,9,3,33,some 40,[test1029],.surface⟩
theorem checked1523: cell1523.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1524: Row := ⟨41,49,9,3,41,some 64,[test1133],.marked⟩
theorem checked1524: cell1524.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1525: Row := ⟨41,49,9,3,65,some 128,[test1146,test1147],.marked⟩
theorem checked1525: cell1525.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1526: Row := ⟨41,49,9,3,129,none,[test1150],.excluded⟩
theorem checked1526: cell1526.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1527: Row := ⟨50,63,10,1,0,some 128,[],.affine⟩
theorem checked1527: cell1527.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1528: Row := ⟨50,63,10,1,129,none,[test12],.excluded⟩
theorem checked1528: cell1528.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1529: Row := ⟨50,63,10,2,0,some 8,[],.surface⟩
theorem checked1529: cell1529.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1530: Row := ⟨50,63,10,2,29,some 32,[test39],.surface⟩
theorem checked1530: cell1530.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1531: Row := ⟨50,63,10,2,33,some 40,[test44],.surface⟩
theorem checked1531: cell1531.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1532: Row := ⟨50,63,10,2,41,some 48,[test50],.surface⟩
theorem checked1532: cell1532.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1533: Row := ⟨50,63,10,2,65,none,[test86],.excluded⟩
theorem checked1533: cell1533.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1534: Row := ⟨50,63,10,3,0,some 3,[],.surface⟩
theorem checked1534: cell1534.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1535: Row := ⟨50,63,10,3,4,some 8,[test671],.surface⟩
theorem checked1535: cell1535.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1232

-- Source: Research6969.HighDispatch10Band4
section Z6969Source1233
set_option autoImplicit true
namespace Research6969.HighDispatch10Band4
open NormalRoute WholeRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false

theorem allDegrees (needed:HighPendingSeed10.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (9:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact
      join (entire cell1486 checked1486) <|
      entire cell1487 checked1487
  · exact
      join (entire cell1488 checked1488) <|
      join (needed ⟨5,by decide⟩) <|
      join (needed ⟨6,by decide⟩) <|
      join (needed ⟨7,by decide⟩) <|
      join (needed ⟨8,by decide⟩) <|
      join (needed ⟨9,by decide⟩) <|
      join (entire cell1489 checked1489) <|
      join (entire cell1490 checked1490) <|
      join (entire cell1491 checked1491) <|
      entire cell1492 checked1492
  · exact
      join (entire cell1493 checked1493) <|
      join (entire cell1494 checked1494) <|
      join (entire cell1495 checked1495) <|
      join (entire cell1496 checked1496) <|
      join (entire cell1497 checked1497) <|
      join (entire cell1498 checked1498) <|
      join (entire cell1499 checked1499) <|
      join (entire cell1500 checked1500) <|
      join (entire cell1501 checked1501) <|
      entire cell1502 checked1502
  · exact
      join (entire cell1503 checked1503) <|
      join (entire cell1504 checked1504) <|
      join (entire cell1505 checked1505) <|
      join (entire cell1506 checked1506) <|
      join (entire cell1507 checked1507) <|
      entire cell1508 checked1508
end Research6969.HighDispatch10Band4
end Z6969Source1233

-- Source: Research6969.HighDispatch10Band5
section Z6969Source1234
set_option autoImplicit true
namespace Research6969.HighDispatch10Band5
open NormalRoute WholeRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false

theorem allDegrees (needed:HighPendingSeed10.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (9:Fin 18) 41 49 9 a 0:=by
  interval_cases a
  · exact
      join (entire cell1509 checked1509) <|
      entire cell1510 checked1510
  · exact
      join (entire cell1511 checked1511) <|
      join (needed ⟨10,by decide⟩) <|
      join (needed ⟨11,by decide⟩) <|
      join (needed ⟨12,by decide⟩) <|
      join (needed ⟨13,by decide⟩) <|
      join (needed ⟨14,by decide⟩) <|
      join (entire cell1512 checked1512) <|
      join (entire cell1513 checked1513) <|
      join (entire cell1514 checked1514) <|
      join (entire cell1515 checked1515) <|
      entire cell1516 checked1516
  · exact
      join (entire cell1517 checked1517) <|
      join (entire cell1518 checked1518) <|
      join (entire cell1519 checked1519) <|
      join (entire cell1520 checked1520) <|
      join (entire cell1521 checked1521) <|
      join (entire cell1522 checked1522) <|
      join (entire cell1523 checked1523) <|
      join (entire cell1524 checked1524) <|
      join (entire cell1525 checked1525) <|
      entire cell1526 checked1526
end Research6969.HighDispatch10Band5
end Z6969Source1234

-- Source: Research6969.WholeGraphCases048
section Z6969Source1235
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell1536: Row := ⟨50,63,10,3,9,some 12,[test724],.surface⟩
theorem checked1536: cell1536.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1537: Row := ⟨50,63,10,3,13,some 16,[test770],.surface⟩
theorem checked1537: cell1537.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1538: Row := ⟨50,63,10,3,17,some 20,[test821],.surface⟩
theorem checked1538: cell1538.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1539: Row := ⟨50,63,10,3,21,some 24,[test869],.surface⟩
theorem checked1539: cell1539.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1540: Row := ⟨50,63,10,3,25,some 31,[test924],.surface⟩
theorem checked1540: cell1540.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1540b: Row := ⟨50,63,10,3,32,some 32,[test1005],.surface⟩
theorem checked1540b: cell1540b.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1541: Row := ⟨50,63,10,3,33,some 40,[test1029],.surface⟩
theorem checked1541: cell1541.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1542: Row := ⟨50,63,10,3,41,some 48,[test1133],.surface⟩
theorem checked1542: cell1542.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1543: Row := ⟨50,63,10,3,65,some 128,[test1146,test1147],.marked⟩
theorem checked1543: cell1543.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1544: Row := ⟨50,63,10,3,129,none,[test1150],.excluded⟩
theorem checked1544: cell1544.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1545: Row := ⟨64,650,12,1,0,some 128,[],.affine⟩
theorem checked1545: cell1545.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1546: Row := ⟨64,650,12,1,129,none,[test12],.excluded⟩
theorem checked1546: cell1546.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1547: Row := ⟨64,650,12,2,0,some 8,[],.surface⟩
theorem checked1547: cell1547.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1548: Row := ⟨64,650,12,2,57,none,[test78],.excluded⟩
theorem checked1548: cell1548.check SmallCertificates.primary10 SmallCertificates.rescue10 :=
  FastCell.checked (by decide +kernel)
def cell1549: Row := ⟨22,22,9,1,0,some 128,[],.affine⟩
theorem checked1549: cell1549.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1550: Row := ⟨22,22,9,1,129,some 1024,[test11,test12],.marked⟩
theorem checked1550: cell1550.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1551: Row := ⟨22,22,9,1,1025,none,[test18],.excluded⟩
theorem checked1551: cell1551.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1552: Row := ⟨22,22,9,2,0,some 12,[],.surface⟩
theorem checked1552: cell1552.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1553: Row := ⟨22,22,9,2,29,some 128,[test39],.marked⟩
theorem checked1553: cell1553.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1554: Row := ⟨22,22,9,2,129,some 1024,[test90],.marked⟩
theorem checked1554: cell1554.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1555: Row := ⟨22,22,9,2,1025,some 4096,[test96,test97],.marked⟩
theorem checked1555: cell1555.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1556: Row := ⟨22,22,9,2,4097,none,[test100],.excluded⟩
theorem checked1556: cell1556.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1557: Row := ⟨22,22,9,3,0,some 3,[],.surface⟩
theorem checked1557: cell1557.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1558: Row := ⟨22,22,9,3,4,some 12,[test671],.surface⟩
theorem checked1558: cell1558.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1559: Row := ⟨22,22,9,3,13,some 64,[test770],.marked⟩
theorem checked1559: cell1559.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1560: Row := ⟨22,22,9,3,65,some 512,[test1147],.marked⟩
theorem checked1560: cell1560.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1561: Row := ⟨22,22,9,3,513,some 2048,[test1154,test1155],.marked⟩
theorem checked1561: cell1561.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1562: Row := ⟨22,22,9,3,2049,some 4096,[test1158,test1159],.marked⟩
theorem checked1562: cell1562.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1563: Row := ⟨22,22,9,3,8193,none,[test1162],.excluded⟩
theorem checked1563: cell1563.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1564: Row := ⟨22,22,9,4,0,some 3,[],.surface⟩
theorem checked1564: cell1564.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1565: Row := ⟨22,22,9,4,4,some 128,[test1237],.marked⟩
theorem checked1565: cell1565.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1566: Row := ⟨22,22,9,4,129,some 1024,[test1374],.marked⟩
theorem checked1566: cell1566.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
def cell1567: Row := ⟨22,22,9,4,1025,some 2048,[test1379,test1380],.marked⟩
theorem checked1567: cell1567.check SmallCertificates.primary11 SmallCertificates.rescue11 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1235
