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
    (JointRouted.seedWeight 133482 14) (JointRouted.ordWeight 133482 1) CertifiedCell.target i.val j.val
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
open NormalRoute WholeRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false

theorem allDegrees (needed:HighPendingSeed14.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (13:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact
      join (entire cell2047 checked2047) <|
      join (entire cell2048 checked2048) <|
      entire cell2049 checked2049
  · exact
      join (entire cell2050 checked2050) <|
      join (needed ⟨0,by decide⟩) <|
      join (needed ⟨1,by decide⟩) <|
      join (entire cell2051 checked2051) <|
      join (entire cell2052 checked2052) <|
      join (entire cell2053 checked2053) <|
      entire cell2054 checked2054
  · exact
      join (entire cell2055 checked2055) <|
      join (entire cell2056 checked2056) <|
      join (entire cell2057 checked2057) <|
      join (entire cell2058 checked2058) <|
      join (entire cell2059 checked2059) <|
      join (entire cell2060 checked2060) <|
      entire cell2061 checked2061
  · exact
      join (entire cell2062 checked2062) <|
      join (entire cell2063 checked2063) <|
      join (entire cell2064 checked2064) <|
      join (entire cell2065 checked2065) <|
      entire cell2066 checked2066
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
open NormalRoute WholeRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false

theorem allDegrees (needed:HighPendingSeed14.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (13:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact
      join (entire cell2067 checked2067) <|
      entire cell2068 checked2068
  · exact
      join (entire cell2069 checked2069) <|
      join (needed ⟨2,by decide⟩) <|
      join (needed ⟨3,by decide⟩) <|
      join (entire cell2070 checked2070) <|
      join (entire cell2071 checked2071) <|
      join (entire cell2072 checked2072) <|
      entire cell2073 checked2073
  · exact
      join (entire cell2074 checked2074) <|
      join (entire cell2075 checked2075) <|
      join (entire cell2076 checked2076) <|
      join (entire cell2077 checked2077) <|
      join (entire cell2078 checked2078) <|
      join (entire cell2079 checked2079) <|
      entire cell2080 checked2080
  · exact
      join (entire cell2081 checked2081) <|
      join (entire cell2082 checked2082) <|
      join (entire cell2083 checked2083) <|
      join (entire cell2084 checked2084) <|
      entire cell2085 checked2085
end Research6969.HighDispatch14Band4
end Z6969Source1293

-- Source: Research6969.HighDispatch14Band5
section Z6969Source1294
set_option autoImplicit true
namespace Research6969.HighDispatch14Band5
open NormalRoute WholeRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false

theorem allDegrees (needed:HighPendingSeed14.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (13:Fin 18) 41 49 9 a 0:=by
  interval_cases a
  · exact
      join (entire cell2086 checked2086) <|
      entire cell2087 checked2087
  · exact
      join (entire cell2088 checked2088) <|
      join (needed ⟨4,by decide⟩) <|
      join (needed ⟨5,by decide⟩) <|
      join (entire cell2089 checked2089) <|
      join (entire cell2090 checked2090) <|
      join (entire cell2091 checked2091) <|
      join (entire cell2092 checked2092) <|
      entire cell2093 checked2093
  · exact
      join (entire cell2094 checked2094) <|
      join (entire cell2095 checked2095) <|
      join (entire cell2096 checked2096) <|
      join (entire cell2097 checked2097) <|
      join (entire cell2098 checked2098) <|
      join (entire cell2099 checked2099) <|
      entire cell2100 checked2100
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
