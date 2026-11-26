import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.Z6969Pack0640
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0667

set_option Elab.async false

-- Source: Research6969.HighPendingSeed14
section Z6969Source1284
set_option autoImplicit true
namespace Research6969.HighPendingSeed14
open NormalRoute
def regions:Array Region:=#[⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 24⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 24⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 24⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 24⟩,⟨64,628,12,2,13,some 16⟩,⟨64,628,12,2,17,some 20⟩,⟨64,628,12,2,21,some 24⟩,⟨64,628,12,2,25,some 28⟩,⟨64,628,12,2,29,some 32⟩,⟨64,628,12,2,49,some 64⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (13:Fin 18) (atIndex j)
end Research6969.HighPendingSeed14
end Z6969Source1284

-- Source: Research6969.SharedGradeInvoice14
section Z6969Source1285
set_option autoImplicit true
namespace Research6969.SharedGradeInvoice14
open NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
theorem counted (r : Region) (grade : r.gradeHi ≤ 30) : Done (13 : Fin 18) r := by
  apply small r 30 grade (by decide) (by decide +kernel) (by decide +kernel)
  change ∀ i j : Fin 31, i.val + j.val ≤ 30 → JointLedger.Pass SmallCertificates.primary14 SmallCertificates.rescue14
    (JointRouted.seedWeight 133460 14) (JointRouted.ordWeight 133460 1) CertifiedCell.target i.val j.val
  rw [SmallCertificates.seed_price14, SmallCertificates.ordinate_price]
  exact ExtendedJointBills.bill14
end Research6969.SharedGradeInvoice14
end Z6969Source1285

-- Source: Research6969.HighDispatch14Band0
section Z6969Source1286
set_option autoImplicit true
namespace Research6969.HighDispatch14Band0
open NormalRoute
theorem allDegrees (_ : HighPendingSeed14.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (13 : Fin 18) 22 22 9 a 0 :=
  SharedGradeInvoice14.counted _ (by decide : 22 ≤ 30)
end Research6969.HighDispatch14Band0
end Z6969Source1286

-- Source: Research6969.HighDispatch14Band1
section Z6969Source1287
set_option autoImplicit true
namespace Research6969.HighDispatch14Band1
open NormalRoute
theorem allDegrees (_ : HighPendingSeed14.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (13 : Fin 18) 23 24 9 a 0 :=
  SharedGradeInvoice14.counted _ (by decide : 24 ≤ 30)
end Research6969.HighDispatch14Band1
end Z6969Source1287

-- Source: Research6969.HighDispatch14Band2
section Z6969Source1288
set_option autoImplicit true
namespace Research6969.HighDispatch14Band2
open NormalRoute
theorem allDegrees (_ : HighPendingSeed14.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 5) :
    Tail (13 : Fin 18) 25 27 9 a 0 :=
  SharedGradeInvoice14.counted _ (by decide : 27 ≤ 30)
end Research6969.HighDispatch14Band2
end Z6969Source1288

-- Source: Research6969.WholeGraphCases063
section Z6969Source1289
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell2016: Row := ⟨23,24,9,3,65,some 512,[test1147],.marked⟩
theorem checked2016: cell2016.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2017: Row := ⟨23,24,9,3,513,some 2048,[test1154,test1155],.marked⟩
theorem checked2017: cell2017.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2018: Row := ⟨23,24,9,3,2049,some 4096,[test1158,test1159],.marked⟩
theorem checked2018: cell2018.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2019: Row := ⟨23,24,9,3,4097,none,[test1161],.excluded⟩
theorem checked2019: cell2019.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2020: Row := ⟨23,24,9,4,0,some 3,[],.surface⟩
theorem checked2020: cell2020.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2021: Row := ⟨23,24,9,4,4,some 128,[test1237],.marked⟩
theorem checked2021: cell2021.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2022: Row := ⟨23,24,9,4,129,some 1024,[test1374],.marked⟩
theorem checked2022: cell2022.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2023: Row := ⟨23,24,9,4,1025,some 2048,[test1379,test1380],.marked⟩
theorem checked2023: cell2023.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2024: Row := ⟨23,24,9,4,2049,some 4096,[test1381,test1382],.marked⟩
theorem checked2024: cell2024.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2025: Row := ⟨23,24,9,5,0,some 3,[],.surface⟩
theorem checked2025: cell2025.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2026: Row := ⟨23,24,9,6,0,some 3,[],.surface⟩
theorem checked2026: cell2026.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2027: Row := ⟨25,27,9,1,0,some 128,[],.affine⟩
theorem checked2027: cell2027.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2028: Row := ⟨25,27,9,1,129,some 1024,[test11,test12],.marked⟩
theorem checked2028: cell2028.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2029: Row := ⟨25,27,9,1,1025,none,[test18],.excluded⟩
theorem checked2029: cell2029.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2030: Row := ⟨25,27,9,2,0,some 16,[],.surface⟩
theorem checked2030: cell2030.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2031: Row := ⟨25,27,9,2,25,some 28,[test36],.surface⟩
theorem checked2031: cell2031.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2032: Row := ⟨25,27,9,2,29,some 64,[test39],.marked⟩
theorem checked2032: cell2032.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2033: Row := ⟨25,27,9,2,65,some 512,[test86],.marked⟩
theorem checked2033: cell2033.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2034: Row := ⟨25,27,9,2,513,none,[test94],.excluded⟩
theorem checked2034: cell2034.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2035: Row := ⟨25,27,9,3,0,some 8,[],.surface⟩
theorem checked2035: cell2035.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2036: Row := ⟨25,27,9,3,9,some 16,[test724],.surface⟩
theorem checked2036: cell2036.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2037: Row := ⟨25,27,9,3,17,some 48,[test821],.marked⟩
theorem checked2037: cell2037.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2038: Row := ⟨25,27,9,3,49,some 256,[test1142],.marked⟩
theorem checked2038: cell2038.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2039: Row := ⟨25,27,9,3,257,some 1024,[test1152,test1153],.marked⟩
theorem checked2039: cell2039.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2040: Row := ⟨25,27,9,3,1025,none,[test1156],.excluded⟩
theorem checked2040: cell2040.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2041: Row := ⟨25,27,9,4,0,some 3,[],.surface⟩
theorem checked2041: cell2041.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2042: Row := ⟨25,27,9,4,4,some 128,[test1237],.marked⟩
theorem checked2042: cell2042.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2043: Row := ⟨25,27,9,4,129,some 1024,[test1374],.marked⟩
theorem checked2043: cell2043.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2044: Row := ⟨25,27,9,4,1025,some 2048,[test1379,test1380],.marked⟩
theorem checked2044: cell2044.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2045: Row := ⟨25,27,9,4,2049,none,[test1382],.excluded⟩
theorem checked2045: cell2045.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2046: Row := ⟨25,27,9,5,0,some 3,[],.surface⟩
theorem checked2046: cell2046.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2047: Row := ⟨28,32,9,1,0,some 128,[],.affine⟩
theorem checked2047: cell2047.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1289

-- Source: Research6969.WholeGraphCases064
section Z6969Source1290
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell2048: Row := ⟨28,32,9,1,129,some 1024,[test11,test12],.marked⟩
theorem checked2048: cell2048.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2049: Row := ⟨28,32,9,1,1025,none,[test18],.excluded⟩
theorem checked2049: cell2049.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2050: Row := ⟨28,32,9,2,0,some 16,[],.surface⟩
theorem checked2050: cell2050.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2051: Row := ⟨28,32,9,2,25,some 28,[test36],.surface⟩
theorem checked2051: cell2051.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2052: Row := ⟨28,32,9,2,29,some 48,[test39],.surface⟩
theorem checked2052: cell2052.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2053: Row := ⟨28,32,9,2,49,some 256,[test62],.marked⟩
theorem checked2053: cell2053.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2054: Row := ⟨28,32,9,2,257,none,[test92],.excluded⟩
theorem checked2054: cell2054.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2055: Row := ⟨28,32,9,3,0,some 8,[],.surface⟩
theorem checked2055: cell2055.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2056: Row := ⟨28,32,9,3,9,some 16,[test724],.surface⟩
theorem checked2056: cell2056.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2057: Row := ⟨28,32,9,3,17,some 24,[test821],.surface⟩
theorem checked2057: cell2057.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2058: Row := ⟨28,32,9,3,25,some 64,[test924],.marked⟩
theorem checked2058: cell2058.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2059: Row := ⟨28,32,9,3,65,some 256,[test1147],.marked⟩
theorem checked2059: cell2059.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2060: Row := ⟨28,32,9,3,257,some 1024,[test1152,test1153],.marked⟩
theorem checked2060: cell2060.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2061: Row := ⟨28,32,9,3,1025,none,[test1156],.excluded⟩
theorem checked2061: cell2061.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2062: Row := ⟨28,32,9,4,0,some 3,[],.surface⟩
theorem checked2062: cell2062.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2063: Row := ⟨28,32,9,4,4,some 64,[test1237],.marked⟩
theorem checked2063: cell2063.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2064: Row := ⟨28,32,9,4,65,some 256,[test1369],.marked⟩
theorem checked2064: cell2064.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2065: Row := ⟨28,32,9,4,257,some 1024,[test1375,test1376],.marked⟩
theorem checked2065: cell2065.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2066: Row := ⟨28,32,9,4,1025,none,[test1379],.excluded⟩
theorem checked2066: cell2066.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2067: Row := ⟨33,40,9,1,0,some 128,[],.affine⟩
theorem checked2067: cell2067.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2068: Row := ⟨33,40,9,1,129,none,[test12],.excluded⟩
theorem checked2068: cell2068.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2069: Row := ⟨33,40,9,2,0,some 16,[],.surface⟩
theorem checked2069: cell2069.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2070: Row := ⟨33,40,9,2,25,some 28,[test36],.surface⟩
theorem checked2070: cell2070.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2071: Row := ⟨33,40,9,2,29,some 48,[test39],.surface⟩
theorem checked2071: cell2071.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2072: Row := ⟨33,40,9,2,49,some 128,[test62],.marked⟩
theorem checked2072: cell2072.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2073: Row := ⟨33,40,9,2,129,none,[test91],.excluded⟩
theorem checked2073: cell2073.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2074: Row := ⟨33,40,9,3,0,some 8,[],.surface⟩
theorem checked2074: cell2074.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2075: Row := ⟨33,40,9,3,9,some 16,[test724],.surface⟩
theorem checked2075: cell2075.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2076: Row := ⟨33,40,9,3,17,some 24,[test821],.surface⟩
theorem checked2076: cell2076.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2077: Row := ⟨33,40,9,3,25,some 32,[test924],.surface⟩
theorem checked2077: cell2077.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2078: Row := ⟨33,40,9,3,33,some 64,[test1029],.marked⟩
theorem checked2078: cell2078.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2079: Row := ⟨33,40,9,3,65,some 256,[test1147],.marked⟩
theorem checked2079: cell2079.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1290

-- Source: Research6969.HighDispatch14Band3
section Z6969Source1291
set_option autoImplicit true
namespace Research6969.HighDispatch14Band3
open NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem leaf1_1025:Done (13:Fin 18) ⟨28,32,9,1,1025,none⟩:=entire WholeRows.cell2049 WholeRows.checked2049
private theorem tail1_1025 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 1 1025:=leaf1_1025
private theorem leaf1_129:Done (13:Fin 18) ⟨28,32,9,1,129,some 1024⟩:=entire WholeRows.cell2048 WholeRows.checked2048
private theorem tail1_129 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 1 129:=join (leaf1_129) (tail1_1025 needed)
private theorem leaf1_0:Done (13:Fin 18) ⟨28,32,9,1,0,some 128⟩:=entire WholeRows.cell2047 WholeRows.checked2047
private theorem tail1_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 1 0:=join (leaf1_0) (tail1_129 needed)
private theorem leaf2_257:Done (13:Fin 18) ⟨28,32,9,2,257,none⟩:=entire WholeRows.cell2054 WholeRows.checked2054
private theorem tail2_257 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 2 257:=leaf2_257
private theorem leaf2_49:Done (13:Fin 18) ⟨28,32,9,2,49,some 256⟩:=entire WholeRows.cell2053 WholeRows.checked2053
private theorem tail2_49 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 2 49:=join (leaf2_49) (tail2_257 needed)
private theorem leaf2_29:Done (13:Fin 18) ⟨28,32,9,2,29,some 48⟩:=entire WholeRows.cell2052 WholeRows.checked2052
private theorem tail2_29 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 2 29:=join (leaf2_29) (tail2_49 needed)
private theorem leaf2_25:Done (13:Fin 18) ⟨28,32,9,2,25,some 28⟩:=entire WholeRows.cell2051 WholeRows.checked2051
private theorem tail2_25 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 2 25:=join (leaf2_25) (tail2_29 needed)
private theorem leaf2_21 (needed:HighPendingSeed14.Required):Done (13:Fin 18) ⟨28,32,9,2,21,some 24⟩:=needed ⟨1,by decide⟩
private theorem tail2_21 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 2 21:=join (leaf2_21 needed) (tail2_25 needed)
private theorem leaf2_17 (needed:HighPendingSeed14.Required):Done (13:Fin 18) ⟨28,32,9,2,17,some 20⟩:=needed ⟨0,by decide⟩
private theorem tail2_17 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 2 17:=join (leaf2_17 needed) (tail2_21 needed)
private theorem leaf2_0:Done (13:Fin 18) ⟨28,32,9,2,0,some 16⟩:=entire WholeRows.cell2050 WholeRows.checked2050
private theorem tail2_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 2 0:=join (leaf2_0) (tail2_17 needed)
private theorem leaf3_1025:Done (13:Fin 18) ⟨28,32,9,3,1025,none⟩:=entire WholeRows.cell2061 WholeRows.checked2061
private theorem tail3_1025 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 3 1025:=leaf3_1025
private theorem leaf3_257:Done (13:Fin 18) ⟨28,32,9,3,257,some 1024⟩:=entire WholeRows.cell2060 WholeRows.checked2060
private theorem tail3_257 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 3 257:=join (leaf3_257) (tail3_1025 needed)
private theorem leaf3_65:Done (13:Fin 18) ⟨28,32,9,3,65,some 256⟩:=entire WholeRows.cell2059 WholeRows.checked2059
private theorem tail3_65 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 3 65:=join (leaf3_65) (tail3_257 needed)
private theorem leaf3_25:Done (13:Fin 18) ⟨28,32,9,3,25,some 64⟩:=entire WholeRows.cell2058 WholeRows.checked2058
private theorem tail3_25 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 3 25:=join (leaf3_25) (tail3_65 needed)
private theorem leaf3_17:Done (13:Fin 18) ⟨28,32,9,3,17,some 24⟩:=entire WholeRows.cell2057 WholeRows.checked2057
private theorem tail3_17 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 3 17:=join (leaf3_17) (tail3_25 needed)
private theorem leaf3_9:Done (13:Fin 18) ⟨28,32,9,3,9,some 16⟩:=entire WholeRows.cell2056 WholeRows.checked2056
private theorem tail3_9 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 3 9:=join (leaf3_9) (tail3_17 needed)
private theorem leaf3_0:Done (13:Fin 18) ⟨28,32,9,3,0,some 8⟩:=entire WholeRows.cell2055 WholeRows.checked2055
private theorem tail3_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 3 0:=join (leaf3_0) (tail3_9 needed)
private theorem leaf4_1025:Done (13:Fin 18) ⟨28,32,9,4,1025,none⟩:=entire WholeRows.cell2066 WholeRows.checked2066
private theorem tail4_1025 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 4 1025:=leaf4_1025
private theorem leaf4_257:Done (13:Fin 18) ⟨28,32,9,4,257,some 1024⟩:=entire WholeRows.cell2065 WholeRows.checked2065
private theorem tail4_257 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 4 257:=join (leaf4_257) (tail4_1025 needed)
private theorem leaf4_65:Done (13:Fin 18) ⟨28,32,9,4,65,some 256⟩:=entire WholeRows.cell2064 WholeRows.checked2064
private theorem tail4_65 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 4 65:=join (leaf4_65) (tail4_257 needed)
private theorem leaf4_4:Done (13:Fin 18) ⟨28,32,9,4,4,some 64⟩:=entire WholeRows.cell2063 WholeRows.checked2063
private theorem tail4_4 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 4 4:=join (leaf4_4) (tail4_65 needed)
private theorem leaf4_0:Done (13:Fin 18) ⟨28,32,9,4,0,some 3⟩:=entire WholeRows.cell2062 WholeRows.checked2062
private theorem tail4_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 28 32 9 4 0:=join (leaf4_0) (tail4_4 needed)
theorem allDegrees (needed:HighPendingSeed14.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (13:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6969.HighDispatch14Band3
end Z6969Source1291

-- Source: Research6969.WholeGraphCases065
section Z6969Source1292
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell2080: Row := ⟨33,40,9,3,257,none,[test1152],.excluded⟩
theorem checked2080: cell2080.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2081: Row := ⟨33,40,9,4,0,some 3,[],.surface⟩
theorem checked2081: cell2081.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2082: Row := ⟨33,40,9,4,4,some 24,[test1237],.surface⟩
theorem checked2082: cell2082.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2083: Row := ⟨33,40,9,4,25,some 64,[test1272],.marked⟩
theorem checked2083: cell2083.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2084: Row := ⟨33,40,9,4,65,some 256,[test1369],.marked⟩
theorem checked2084: cell2084.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2085: Row := ⟨33,40,9,4,257,none,[test1375],.excluded⟩
theorem checked2085: cell2085.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2086: Row := ⟨41,49,9,1,0,some 128,[],.affine⟩
theorem checked2086: cell2086.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2087: Row := ⟨41,49,9,1,129,none,[test12],.excluded⟩
theorem checked2087: cell2087.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2088: Row := ⟨41,49,9,2,0,some 16,[],.surface⟩
theorem checked2088: cell2088.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2089: Row := ⟨41,49,9,2,25,some 28,[test36],.surface⟩
theorem checked2089: cell2089.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2090: Row := ⟨41,49,9,2,29,some 40,[test39],.surface⟩
theorem checked2090: cell2090.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2091: Row := ⟨41,49,9,2,41,some 64,[test50],.surface⟩
theorem checked2091: cell2091.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2092: Row := ⟨41,49,9,2,65,some 128,[test86,test87],.marked⟩
theorem checked2092: cell2092.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2093: Row := ⟨41,49,9,2,129,none,[test91],.excluded⟩
theorem checked2093: cell2093.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2094: Row := ⟨41,49,9,3,0,some 8,[],.surface⟩
theorem checked2094: cell2094.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2095: Row := ⟨41,49,9,3,9,some 16,[test724],.surface⟩
theorem checked2095: cell2095.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2096: Row := ⟨41,49,9,3,17,some 24,[test821],.surface⟩
theorem checked2096: cell2096.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2097: Row := ⟨41,49,9,3,25,some 32,[test924],.surface⟩
theorem checked2097: cell2097.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2098: Row := ⟨41,49,9,3,33,some 48,[test1029],.surface⟩
theorem checked2098: cell2098.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2099: Row := ⟨41,49,9,3,49,some 96,[test1143],.marked⟩
theorem checked2099: cell2099.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2100: Row := ⟨41,49,9,3,97,none,[test1148],.excluded⟩
theorem checked2100: cell2100.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2101: Row := ⟨50,63,10,1,0,some 128,[],.affine⟩
theorem checked2101: cell2101.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2102: Row := ⟨50,63,10,1,129,none,[test12],.excluded⟩
theorem checked2102: cell2102.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2103: Row := ⟨50,63,10,2,0,some 16,[],.surface⟩
theorem checked2103: cell2103.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2104: Row := ⟨50,63,10,2,25,some 28,[test36],.surface⟩
theorem checked2104: cell2104.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2105: Row := ⟨50,63,10,2,29,some 40,[test39],.surface⟩
theorem checked2105: cell2105.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2106: Row := ⟨50,63,10,2,41,some 48,[test50],.surface⟩
theorem checked2106: cell2106.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2107: Row := ⟨50,63,10,2,49,some 64,[test62,test63],.surface⟩
theorem checked2107: cell2107.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2108: Row := ⟨50,63,10,2,65,none,[test86],.excluded⟩
theorem checked2108: cell2108.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2109: Row := ⟨50,63,10,3,0,some 8,[],.surface⟩
theorem checked2109: cell2109.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2110: Row := ⟨50,63,10,3,9,some 16,[test724],.surface⟩
theorem checked2110: cell2110.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2111: Row := ⟨50,63,10,3,17,some 24,[test821],.surface⟩
theorem checked2111: cell2111.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1292

-- Source: Research6969.HighDispatch14Band4
section Z6969Source1293
set_option autoImplicit true
namespace Research6969.HighDispatch14Band4
open NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem leaf1_129:Done (13:Fin 18) ⟨33,40,9,1,129,none⟩:=entire WholeRows.cell2068 WholeRows.checked2068
private theorem tail1_129 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 1 129:=leaf1_129
private theorem leaf1_0:Done (13:Fin 18) ⟨33,40,9,1,0,some 128⟩:=entire WholeRows.cell2067 WholeRows.checked2067
private theorem tail1_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 1 0:=join (leaf1_0) (tail1_129 needed)
private theorem leaf2_129:Done (13:Fin 18) ⟨33,40,9,2,129,none⟩:=entire WholeRows.cell2073 WholeRows.checked2073
private theorem tail2_129 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 2 129:=leaf2_129
private theorem leaf2_49:Done (13:Fin 18) ⟨33,40,9,2,49,some 128⟩:=entire WholeRows.cell2072 WholeRows.checked2072
private theorem tail2_49 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 2 49:=join (leaf2_49) (tail2_129 needed)
private theorem leaf2_29:Done (13:Fin 18) ⟨33,40,9,2,29,some 48⟩:=entire WholeRows.cell2071 WholeRows.checked2071
private theorem tail2_29 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 2 29:=join (leaf2_29) (tail2_49 needed)
private theorem leaf2_25:Done (13:Fin 18) ⟨33,40,9,2,25,some 28⟩:=entire WholeRows.cell2070 WholeRows.checked2070
private theorem tail2_25 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 2 25:=join (leaf2_25) (tail2_29 needed)
private theorem leaf2_21 (needed:HighPendingSeed14.Required):Done (13:Fin 18) ⟨33,40,9,2,21,some 24⟩:=needed ⟨3,by decide⟩
private theorem tail2_21 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 2 21:=join (leaf2_21 needed) (tail2_25 needed)
private theorem leaf2_17 (needed:HighPendingSeed14.Required):Done (13:Fin 18) ⟨33,40,9,2,17,some 20⟩:=needed ⟨2,by decide⟩
private theorem tail2_17 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 2 17:=join (leaf2_17 needed) (tail2_21 needed)
private theorem leaf2_0:Done (13:Fin 18) ⟨33,40,9,2,0,some 16⟩:=entire WholeRows.cell2069 WholeRows.checked2069
private theorem tail2_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 2 0:=join (leaf2_0) (tail2_17 needed)
private theorem leaf3_257:Done (13:Fin 18) ⟨33,40,9,3,257,none⟩:=entire WholeRows.cell2080 WholeRows.checked2080
private theorem tail3_257 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 3 257:=leaf3_257
private theorem leaf3_65:Done (13:Fin 18) ⟨33,40,9,3,65,some 256⟩:=entire WholeRows.cell2079 WholeRows.checked2079
private theorem tail3_65 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 3 65:=join (leaf3_65) (tail3_257 needed)
private theorem leaf3_33:Done (13:Fin 18) ⟨33,40,9,3,33,some 64⟩:=entire WholeRows.cell2078 WholeRows.checked2078
private theorem tail3_33 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 3 33:=join (leaf3_33) (tail3_65 needed)
private theorem leaf3_25:Done (13:Fin 18) ⟨33,40,9,3,25,some 32⟩:=entire WholeRows.cell2077 WholeRows.checked2077
private theorem tail3_25 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 3 25:=join (leaf3_25) (tail3_33 needed)
private theorem leaf3_17:Done (13:Fin 18) ⟨33,40,9,3,17,some 24⟩:=entire WholeRows.cell2076 WholeRows.checked2076
private theorem tail3_17 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 3 17:=join (leaf3_17) (tail3_25 needed)
private theorem leaf3_9:Done (13:Fin 18) ⟨33,40,9,3,9,some 16⟩:=entire WholeRows.cell2075 WholeRows.checked2075
private theorem tail3_9 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 3 9:=join (leaf3_9) (tail3_17 needed)
private theorem leaf3_0:Done (13:Fin 18) ⟨33,40,9,3,0,some 8⟩:=entire WholeRows.cell2074 WholeRows.checked2074
private theorem tail3_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 3 0:=join (leaf3_0) (tail3_9 needed)
private theorem leaf4_257:Done (13:Fin 18) ⟨33,40,9,4,257,none⟩:=entire WholeRows.cell2085 WholeRows.checked2085
private theorem tail4_257 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 4 257:=leaf4_257
private theorem leaf4_65:Done (13:Fin 18) ⟨33,40,9,4,65,some 256⟩:=entire WholeRows.cell2084 WholeRows.checked2084
private theorem tail4_65 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 4 65:=join (leaf4_65) (tail4_257 needed)
private theorem leaf4_25:Done (13:Fin 18) ⟨33,40,9,4,25,some 64⟩:=entire WholeRows.cell2083 WholeRows.checked2083
private theorem tail4_25 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 4 25:=join (leaf4_25) (tail4_65 needed)
private theorem leaf4_4:Done (13:Fin 18) ⟨33,40,9,4,4,some 24⟩:=entire WholeRows.cell2082 WholeRows.checked2082
private theorem tail4_4 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 4 4:=join (leaf4_4) (tail4_25 needed)
private theorem leaf4_0:Done (13:Fin 18) ⟨33,40,9,4,0,some 3⟩:=entire WholeRows.cell2081 WholeRows.checked2081
private theorem tail4_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 33 40 9 4 0:=join (leaf4_0) (tail4_4 needed)
theorem allDegrees (needed:HighPendingSeed14.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (13:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6969.HighDispatch14Band4
end Z6969Source1293

-- Source: Research6969.HighDispatch14Band5
section Z6969Source1294
set_option autoImplicit true
namespace Research6969.HighDispatch14Band5
open NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem leaf1_129:Done (13:Fin 18) ⟨41,49,9,1,129,none⟩:=entire WholeRows.cell2087 WholeRows.checked2087
private theorem tail1_129 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 1 129:=leaf1_129
private theorem leaf1_0:Done (13:Fin 18) ⟨41,49,9,1,0,some 128⟩:=entire WholeRows.cell2086 WholeRows.checked2086
private theorem tail1_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 1 0:=join (leaf1_0) (tail1_129 needed)
private theorem leaf2_129:Done (13:Fin 18) ⟨41,49,9,2,129,none⟩:=entire WholeRows.cell2093 WholeRows.checked2093
private theorem tail2_129 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 2 129:=leaf2_129
private theorem leaf2_65:Done (13:Fin 18) ⟨41,49,9,2,65,some 128⟩:=entire WholeRows.cell2092 WholeRows.checked2092
private theorem tail2_65 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 2 65:=join (leaf2_65) (tail2_129 needed)
private theorem leaf2_41:Done (13:Fin 18) ⟨41,49,9,2,41,some 64⟩:=entire WholeRows.cell2091 WholeRows.checked2091
private theorem tail2_41 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 2 41:=join (leaf2_41) (tail2_65 needed)
private theorem leaf2_29:Done (13:Fin 18) ⟨41,49,9,2,29,some 40⟩:=entire WholeRows.cell2090 WholeRows.checked2090
private theorem tail2_29 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 2 29:=join (leaf2_29) (tail2_41 needed)
private theorem leaf2_25:Done (13:Fin 18) ⟨41,49,9,2,25,some 28⟩:=entire WholeRows.cell2089 WholeRows.checked2089
private theorem tail2_25 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 2 25:=join (leaf2_25) (tail2_29 needed)
private theorem leaf2_21 (needed:HighPendingSeed14.Required):Done (13:Fin 18) ⟨41,49,9,2,21,some 24⟩:=needed ⟨5,by decide⟩
private theorem tail2_21 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 2 21:=join (leaf2_21 needed) (tail2_25 needed)
private theorem leaf2_17 (needed:HighPendingSeed14.Required):Done (13:Fin 18) ⟨41,49,9,2,17,some 20⟩:=needed ⟨4,by decide⟩
private theorem tail2_17 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 2 17:=join (leaf2_17 needed) (tail2_21 needed)
private theorem leaf2_0:Done (13:Fin 18) ⟨41,49,9,2,0,some 16⟩:=entire WholeRows.cell2088 WholeRows.checked2088
private theorem tail2_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 2 0:=join (leaf2_0) (tail2_17 needed)
private theorem leaf3_97:Done (13:Fin 18) ⟨41,49,9,3,97,none⟩:=entire WholeRows.cell2100 WholeRows.checked2100
private theorem tail3_97 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 3 97:=leaf3_97
private theorem leaf3_49:Done (13:Fin 18) ⟨41,49,9,3,49,some 96⟩:=entire WholeRows.cell2099 WholeRows.checked2099
private theorem tail3_49 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 3 49:=join (leaf3_49) (tail3_97 needed)
private theorem leaf3_33:Done (13:Fin 18) ⟨41,49,9,3,33,some 48⟩:=entire WholeRows.cell2098 WholeRows.checked2098
private theorem tail3_33 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 3 33:=join (leaf3_33) (tail3_49 needed)
private theorem leaf3_25:Done (13:Fin 18) ⟨41,49,9,3,25,some 32⟩:=entire WholeRows.cell2097 WholeRows.checked2097
private theorem tail3_25 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 3 25:=join (leaf3_25) (tail3_33 needed)
private theorem leaf3_17:Done (13:Fin 18) ⟨41,49,9,3,17,some 24⟩:=entire WholeRows.cell2096 WholeRows.checked2096
private theorem tail3_17 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 3 17:=join (leaf3_17) (tail3_25 needed)
private theorem leaf3_9:Done (13:Fin 18) ⟨41,49,9,3,9,some 16⟩:=entire WholeRows.cell2095 WholeRows.checked2095
private theorem tail3_9 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 3 9:=join (leaf3_9) (tail3_17 needed)
private theorem leaf3_0:Done (13:Fin 18) ⟨41,49,9,3,0,some 8⟩:=entire WholeRows.cell2094 WholeRows.checked2094
private theorem tail3_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 41 49 9 3 0:=join (leaf3_0) (tail3_9 needed)
theorem allDegrees (needed:HighPendingSeed14.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (13:Fin 18) 41 49 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6969.HighDispatch14Band5
end Z6969Source1294

-- Source: Research6969.WholeGraphCases066
section Z6969Source1295
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell2112: Row := ⟨50,63,10,3,25,some 32,[test924],.surface⟩
theorem checked2112: cell2112.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2113: Row := ⟨50,63,10,3,33,some 48,[test1029],.surface⟩
theorem checked2113: cell2113.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2114: Row := ⟨50,63,10,3,65,some 128,[test1146,test1147],.marked⟩
theorem checked2114: cell2114.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2115: Row := ⟨50,63,10,3,129,none,[test1150],.excluded⟩
theorem checked2115: cell2115.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2116: Row := ⟨64,628,12,1,0,some 128,[],.affine⟩
theorem checked2116: cell2116.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2117: Row := ⟨64,628,12,1,129,none,[test12],.excluded⟩
theorem checked2117: cell2117.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2118: Row := ⟨64,628,12,2,0,some 12,[],.surface⟩
theorem checked2118: cell2118.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2119: Row := ⟨64,628,12,2,33,some 40,[test43,test44],.surface⟩
theorem checked2119: cell2119.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2120: Row := ⟨64,628,12,2,41,some 48,[test49,test50],.surface⟩
theorem checked2120: cell2120.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2121: Row := ⟨64,628,12,2,65,none,[test86],.excluded⟩
theorem checked2121: cell2121.check SmallCertificates.primary14 SmallCertificates.rescue14 :=
  FastCell.checked (by decide +kernel)
def cell2122: Row := ⟨22,22,9,1,0,some 128,[],.affine⟩
theorem checked2122: cell2122.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2123: Row := ⟨22,22,9,1,129,some 1024,[test11,test12],.marked⟩
theorem checked2123: cell2123.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2124: Row := ⟨22,22,9,1,1025,none,[test18],.excluded⟩
theorem checked2124: cell2124.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2125: Row := ⟨22,22,9,2,0,some 16,[],.surface⟩
theorem checked2125: cell2125.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2126: Row := ⟨22,22,9,2,25,some 40,[test36],.marked⟩
theorem checked2126: cell2126.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2127: Row := ⟨22,22,9,2,41,some 512,[test49],.marked⟩
theorem checked2127: cell2127.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2128: Row := ⟨22,22,9,2,513,none,[test94],.marked⟩
theorem checked2128: cell2128.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2129: Row := ⟨22,22,9,3,0,some 8,[],.surface⟩
theorem checked2129: cell2129.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2130: Row := ⟨22,22,9,3,9,some 48,[test724],.marked⟩
theorem checked2130: cell2130.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2131: Row := ⟨22,22,9,3,49,some 512,[test1142],.marked⟩
theorem checked2131: cell2131.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2132: Row := ⟨22,22,9,3,513,some 2048,[test1154,test1155],.marked⟩
theorem checked2132: cell2132.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2133: Row := ⟨22,22,9,3,2049,none,[test1158],.marked⟩
theorem checked2133: cell2133.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2134: Row := ⟨22,22,9,4,0,some 3,[],.surface⟩
theorem checked2134: cell2134.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2135: Row := ⟨22,22,9,4,4,some 256,[test1237],.marked⟩
theorem checked2135: cell2135.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2136: Row := ⟨22,22,9,4,257,some 2048,[test1376],.marked⟩
theorem checked2136: cell2136.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2137: Row := ⟨22,22,9,4,2049,some 4096,[test1381,test1382],.marked⟩
theorem checked2137: cell2137.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2138: Row := ⟨22,22,9,5,0,some 3,[],.surface⟩
theorem checked2138: cell2138.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2139: Row := ⟨22,22,9,6,0,some 3,[],.surface⟩
theorem checked2139: cell2139.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2140: Row := ⟨23,24,9,1,0,some 128,[],.affine⟩
theorem checked2140: cell2140.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2141: Row := ⟨23,24,9,1,129,some 1024,[test11,test12],.marked⟩
theorem checked2141: cell2141.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2142: Row := ⟨23,24,9,1,1025,none,[test18],.excluded⟩
theorem checked2142: cell2142.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
def cell2143: Row := ⟨23,24,9,2,0,some 16,[],.surface⟩
theorem checked2143: cell2143.check SmallCertificates.primary15 SmallCertificates.rescue15 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1295
