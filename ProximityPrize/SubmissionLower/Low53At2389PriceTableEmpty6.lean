import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty6
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top6
private def b0 : PaidBatch .empty 6 := ⟨[
  .rectangle 6 18 67 26 23,
  .rectangle 9 27 69 35 29,
  .rectangle 12 36 70 44 35], by decide +kernel⟩
private def b1 : PaidBatch .empty 6 := ⟨[
  .rectangle 15 45 70 53 39,
  .rectangle 68 18 129 22 31,
  .rectangle 68 23 129 26 34], by decide +kernel⟩
private def b2 : PaidBatch .empty 6 := ⟨[
  .rectangle 70 32 99 35 35,
  .rectangle 70 27 129 31 42,
  .rectangle 71 45 85 49 41], by decide +kernel⟩
private def b3 : PaidBatch .empty 6 := ⟨[
  .rectangle 71 50 85 53 43,
  .rectangle 71 36 100 40 41,
  .rectangle 71 41 100 44 43], by decide +kernel⟩
private def b4 : PaidBatch .empty 6 := ⟨[
  .rectangle 86 45 100 47 45,
  .rectangle 86 48 100 49 45,
  .rectangle 86 50 100 51 47], by decide +kernel⟩
private def b5 : PaidBatch .empty 6 := ⟨[
  .rectangle 86 52 100 53 48,
  .rectangle 100 32 129 35 45,
  .rectangle 101 53 101 53 48], by decide +kernel⟩
private def b6 : PaidBatch .empty 6 := ⟨[
  .rectangle 101 52 102 52 48,
  .rectangle 101 50 104 50 47,
  .rectangle 101 51 104 51 48], by decide +kernel⟩
private def b7 : PaidBatch .empty 6 := ⟨[
  .rectangle 101 45 108 47 48,
  .rectangle 101 48 108 48 47,
  .rectangle 101 49 108 49 48], by decide +kernel⟩
private def b8 : PaidBatch .empty 6 := ⟨[
  .rectangle 101 36 115 38 42,
  .rectangle 101 39 115 40 43,
  .rectangle 101 41 115 42 45], by decide +kernel⟩
private def b9 : PaidBatch .empty 6 := ⟨[
  .rectangle 101 43 115 44 47,
  .point 102 53 45,
  .rectangle 103 52 103 52 48], by decide +kernel⟩
private def b10 : PaidBatch .empty 6 := ⟨[
  .point 103 53 46,
  .point 104 52 45,
  .rectangle 104 53 104 53 49], by decide +kernel⟩
private def b11 : PaidBatch .empty 6 := ⟨[
  .rectangle 105 51 105 51 48,
  .point 105 52 46,
  .point 105 53 47], by decide +kernel⟩
private def b12 : PaidBatch .empty 6 := ⟨[
  .rectangle 105 50 106 50 48,
  .point 106 51 45,
  .point 106 52 46], by decide +kernel⟩
private def b13 : PaidBatch .empty 6 := ⟨[
  .point 106 53 47,
  .rectangle 107 50 107 50 48,
  .point 107 51 46], by decide +kernel⟩
private def b14 : PaidBatch .empty 6 := ⟨[
  .point 107 52 47,
  .point 107 53 48,
  .point 108 50 45], by decide +kernel⟩
private def b15 : PaidBatch .empty 6 := ⟨[
  .point 108 51 46,
  .point 108 52 47,
  .point 108 53 48], by decide +kernel⟩
private def b16 : PaidBatch .empty 6 := ⟨[
  .rectangle 109 49 109 49 48,
  .point 109 50 46,
  .point 109 51 47], by decide +kernel⟩
private def b17 : PaidBatch .empty 6 := ⟨[
  .point 109 52 48,
  .point 109 53 48,
  .rectangle 109 48 110 48 48], by decide +kernel⟩
private def b18 : PaidBatch .empty 6 := ⟨[
  .rectangle 109 47 112 47 48,
  .rectangle 109 45 115 45 47,
  .rectangle 109 46 115 46 48], by decide +kernel⟩
private def b19 : PaidBatch .empty 6 := ⟨[
  .point 110 49 45,
  .point 110 50 46,
  .point 110 51 47], by decide +kernel⟩
private def b20 : PaidBatch .empty 6 := ⟨[
  .point 110 52 48,
  .point 110 53 49,
  .rectangle 111 48 111 48 48], by decide +kernel⟩
private def b21 : PaidBatch .empty 6 := ⟨[
  .point 111 49 46,
  .point 111 50 47,
  .point 111 51 48], by decide +kernel⟩
private def b22 : PaidBatch .empty 6 := ⟨[
  .point 111 52 48,
  .point 111 53 49,
  .point 112 48 45], by decide +kernel⟩
private def b23 : PaidBatch .empty 6 := ⟨[
  .point 112 49 46,
  .point 112 50 47,
  .point 112 51 48], by decide +kernel⟩
private def b24 : PaidBatch .empty 6 := ⟨[
  .point 112 52 49,
  .shared 112 53 33 ⟨.tilted, 1, 2, true, 186362719992101385⟩,
  .rectangle 113 47 113 47 48], by decide +kernel⟩
private def b25 : PaidBatch .empty 6 := ⟨[
  .point 113 48 46,
  .point 113 49 47,
  .point 113 50 48], by decide +kernel⟩
private def b26 : PaidBatch .empty 6 := ⟨[
  .point 113 51 48,
  .point 113 52 49,
  .shared 113 53 34 ⟨.tilted, 1, 2, true, 188029900760625461⟩], by decide +kernel⟩
private def b27 : PaidBatch .empty 6 := ⟨[
  .point 114 47 45,
  .point 114 48 46,
  .point 114 49 47], by decide +kernel⟩
private def b28 : PaidBatch .empty 6 := ⟨[
  .point 114 50 48,
  .shared 114 51 32 ⟨.tilted, 1, 2, true, 176055708910364183⟩,
  .shared 114 52 33 ⟨.tilted, 1, 2, true, 182828287716993508⟩], by decide +kernel⟩
private def b29 : PaidBatch .empty 6 := ⟨[
  .shared 114 53 34 ⟨.tilted, 1, 2, true, 189697081529149537⟩,
  .point 115 47 46,
  .point 115 48 47], by decide +kernel⟩
private def b30 : PaidBatch .empty 6 := ⟨[
  .point 115 49 48,
  .point 115 50 48,
  .shared 115 51 33 ⟨.tilted, 1, 2, true, 177594650505935795⟩], by decide +kernel⟩
private def b31 : PaidBatch .empty 6 := ⟨[
  .shared 115 52 34 ⟨.tilted, 1, 2, true, 184430707703283356⟩,
  .shared 115 53 35 ⟨.tilted, 1, 2, true, 191364262297673613⟩,
  .rectangle 116 46 116 46 48], by decide +kernel⟩
private def b32 : PaidBatch .empty 6 := ⟨[
  .point 116 47 46,
  .point 116 48 47,
  .point 116 49 48], by decide +kernel⟩
private def b33 : PaidBatch .empty 6 := ⟨[
  .shared 116 50 32 ⟨.tilted, 1, 2, true, 172334759889274284⟩,
  .shared 116 51 33 ⟨.tilted, 1, 2, true, 179133592101507407⟩,
  .shared 116 52 34 ⟨.tilted, 1, 2, true, 186033127689573204⟩], by decide +kernel⟩
private def b34 : PaidBatch .empty 6 := ⟨[
  .shared 116 53 36 ⟨.tilted, 1, 2, true, 193031443066197689⟩,
  .rectangle 116 45 117 45 48,
  .rectangle 116 44 119 44 48], by decide +kernel⟩
private def b35 : PaidBatch .empty 6 := ⟨[
  .rectangle 116 39 122 40 46,
  .rectangle 116 41 122 41 46,
  .rectangle 116 42 122 42 47], by decide +kernel⟩
private def b36 : PaidBatch .empty 6 := ⟨[
  .rectangle 116 43 122 43 48,
  .rectangle 116 36 129 38 47,
  .point 117 46 45], by decide +kernel⟩
private def b37 : PaidBatch .empty 6 := ⟨[
  .point 117 47 46,
  .point 117 48 47,
  .point 117 49 48], by decide +kernel⟩
private def b38 : PaidBatch .empty 6 := ⟨[
  .shared 117 50 33 ⟨.tilted, 1, 2, true, 173811505485643652⟩,
  .shared 117 51 34 ⟨.tilted, 1, 2, true, 180672533697079019⟩,
  .shared 117 52 35 ⟨.tilted, 1, 2, true, 187635547675863052⟩], by decide +kernel⟩
private def b39 : PaidBatch .empty 6 := ⟨[
  .shared 117 53 36 ⟨.tilted, 1, 2, true, 194698623834721765⟩,
  .rectangle 118 45 118 45 48,
  .point 118 46 46], by decide +kernel⟩
private def b40 : PaidBatch .empty 6 := ⟨[
  .point 118 47 47,
  .point 118 48 48,
  .shared 118 49 32 ⟨.tilted, 1, 2, true, 168470218617514057⟩], by decide +kernel⟩
private def b41 : PaidBatch .empty 6 := ⟨[
  .shared 118 50 33 ⟨.tilted, 1, 2, true, 175288251082013020⟩,
  .shared 118 51 34 ⟨.tilted, 1, 2, true, 182211475292650631⟩,
  .shared 118 52 36 ⟨.tilted, 1, 2, true, 189237967662152900⟩], by decide +kernel⟩
private def b42 : PaidBatch .empty 6 := ⟨[
  .shared 118 53 37 ⟨.tilted, 1, 2, true, 196365804603245841⟩,
  .point 119 45 45,
  .point 119 46 46], by decide +kernel⟩
private def b43 : PaidBatch .empty 6 := ⟨[
  .point 119 47 47,
  .point 119 48 48,
  .shared 119 49 32 ⟨.tilted, 1, 2, true, 169886050606197173⟩], by decide +kernel⟩
private def b44 : PaidBatch .empty 6 := ⟨[
  .shared 119 50 34 ⟨.tilted, 1, 2, true, 176764996678382388⟩,
  .shared 119 51 35 ⟨.tilted, 1, 2, true, 183750416888222243⟩,
  .shared 119 52 36 ⟨.tilted, 1, 2, true, 190840387648442748⟩], by decide +kernel⟩
private def b45 : PaidBatch .empty 6 := ⟨[
  .shared 119 53 37 ⟨.tilted, 1, 2, true, 198032985371769917⟩,
  .point 120 45 46,
  .point 120 46 47], by decide +kernel⟩
private def b46 : PaidBatch .empty 6 := ⟨[
  .point 120 47 48,
  .shared 120 48 37 ⟨.tilted, 1, 1, false, 150816801269666748⟩,
  .shared 120 49 33 ⟨.tilted, 1, 2, true, 171301882594880289⟩], by decide +kernel⟩
private def b47 : PaidBatch .empty 6 := ⟨[
  .shared 120 50 34 ⟨.tilted, 1, 2, true, 178241742274751756⟩,
  .shared 120 51 35 ⟨.tilted, 1, 2, true, 185289358483793855⟩,
  .shared 120 52 37 ⟨.tilted, 1, 2, true, 192442807634732596⟩], by decide +kernel⟩
private def b48 : PaidBatch .empty 6 := ⟨[
  .shared 120 53 38 ⟨.tilted, 1, 2, true, 199700166140293993⟩,
  .rectangle 120 44 121 44 48,
  .point 121 45 46], by decide +kernel⟩
private def b49 : PaidBatch .empty 6 := ⟨[
  .point 121 46 47,
  .point 121 47 48,
  .shared 121 48 37 ⟨.tilted, 1, 1, false, 152035073741555496⟩], by decide +kernel⟩
private def b50 : PaidBatch .empty 6 := ⟨[
  .shared 121 49 34 ⟨.tilted, 1, 2, true, 172717714583563405⟩,
  .shared 121 50 35 ⟨.tilted, 1, 2, true, 179718487871121124⟩,
  .shared 121 51 36 ⟨.tilted, 1, 2, true, 186828300079365467⟩], by decide +kernel⟩
private def b51 : PaidBatch .empty 6 := ⟨[
  .shared 121 52 37 ⟨.tilted, 1, 2, true, 194045227621022444⟩,
  .shared 121 53 39 ⟨.tilted, 1, 2, true, 201367346908818069⟩,
  .point 122 44 45], by decide +kernel⟩
private def b52 : PaidBatch .empty 6 := ⟨[
  .point 122 45 46,
  .point 122 46 47,
  .point 122 47 48], by decide +kernel⟩
private def b53 : PaidBatch .empty 6 := ⟨[
  .shared 122 48 38 ⟨.tilted, 0, 1, false, 153253346213444244⟩,
  .shared 122 49 34 ⟨.tilted, 1, 2, true, 174133546572246521⟩,
  .shared 122 50 35 ⟨.tilted, 1, 2, true, 181195233467490492⟩], by decide +kernel⟩
private def b54 : PaidBatch .empty 6 := ⟨[
  .shared 122 51 37 ⟨.tilted, 1, 2, true, 188367241674937079⟩,
  .shared 122 52 38 ⟨.tilted, 1, 2, true, 195647647607312292⟩,
  .shared 122 53 39 ⟨.tilted, 1, 2, true, 203034527677342145⟩], by decide +kernel⟩
private def b55 : PaidBatch .empty 6 := ⟨[
  .rectangle 123 43 123 43 48,
  .point 123 44 46,
  .point 123 45 47], by decide +kernel⟩
private def b56 : PaidBatch .empty 6 := ⟨[
  .point 123 46 48,
  .shared 123 47 37 ⟨.tilted, 0, 1, false, 148456532406803005⟩,
  .shared 123 48 33 ⟨.tilted, 0, 2, true, 168540305348992008⟩], by decide +kernel⟩
private def b57 : PaidBatch .empty 6 := ⟨[
  .shared 123 49 35 ⟨.tilted, 1, 2, true, 175549378560929637⟩,
  .shared 123 50 36 ⟨.tilted, 1, 2, true, 182671979063859860⟩,
  .shared 123 51 37 ⟨.tilted, 1, 2, true, 189906183270508691⟩], by decide +kernel⟩
private def b58 : PaidBatch .empty 6 := ⟨[
  .shared 123 52 39 ⟨.tilted, 1, 2, true, 197250067593602140⟩,
  .shared 123 53 40 ⟨.tilted, 1, 2, true, 204701708445866221⟩,
  .rectangle 123 42 126 42 48], by decide +kernel⟩
private def b59 : PaidBatch .empty 6 := ⟨[
  .rectangle 123 39 129 39 46,
  .rectangle 123 40 129 40 47,
  .rectangle 123 41 129 41 48], by decide +kernel⟩
private def b60 : PaidBatch .empty 6 := ⟨[
  .point 124 43 45,
  .point 124 44 46,
  .point 124 45 47], by decide +kernel⟩
private def b61 : PaidBatch .empty 6 := ⟨[
  .point 124 46 48,
  .shared 124 47 38 ⟨.tilted, 0, 1, false, 149625699958480930⟩,
  .shared 124 48 34 ⟨.tilted, 0, 2, true, 169896506121504864⟩], by decide +kernel⟩
private def b62 : PaidBatch .empty 6 := ⟨[
  .shared 124 49 35 ⟨.tilted, 1, 2, true, 176965210549612753⟩,
  .shared 124 50 37 ⟨.tilted, 1, 2, true, 184148724660229228⟩,
  .shared 124 51 38 ⟨.tilted, 1, 2, true, 191445124866080303⟩], by decide +kernel⟩
private def b63 : PaidBatch .empty 6 := ⟨[
  .shared 124 52 39 ⟨.tilted, 1, 2, true, 198852487579891988⟩,
  .shared 124 53 41 ⟨.tilted, 1, 2, true, 206368889214390297⟩,
  .point 125 43 45], by decide +kernel⟩
private def b64 : PaidBatch .empty 6 := ⟨[
  .point 125 44 46,
  .point 125 45 47,
  .shared 125 46 37 ⟨.tilted, 0, 1, false, 144777091766928432⟩], by decide +kernel⟩
private def b65 : PaidBatch .empty 6 := ⟨[
  .shared 125 47 38 ⟨.tilted, 0, 1, false, 150794867510158855⟩,
  .shared 125 48 34 ⟨.tilted, 0, 2, true, 171252706894017720⟩,
  .shared 125 49 36 ⟨.tilted, 0, 2, true, 178381042538295869⟩], by decide +kernel⟩
private def b66 : PaidBatch .empty 6 := ⟨[
  .shared 125 50 37 ⟨.tilted, 1, 2, true, 185625470256598596⟩,
  .shared 125 51 39 ⟨.tilted, 1, 2, true, 192984066461651915⟩,
  .shared 125 52 40 ⟨.tilted, 1, 2, true, 200454907566181836⟩], by decide +kernel⟩
private def b67 : PaidBatch .empty 6 := ⟨[
  .shared 125 53 42 ⟨.tilted, 1, 2, true, 208036069982914373⟩,
  .point 126 43 46,
  .point 126 44 47], by decide +kernel⟩
private def b68 : PaidBatch .empty 6 := ⟨[
  .point 126 45 48,
  .shared 126 46 37 ⟨.tilted, 0, 1, false, 145898116192032528⟩,
  .shared 126 47 38 ⟨.tilted, 0, 1, false, 151964035061836780⟩], by decide +kernel⟩
private def b69 : PaidBatch .empty 6 := ⟨[
  .shared 126 48 35 ⟨.tilted, 0, 2, true, 172608907666530576⟩,
  .shared 126 49 36 ⟨.tilted, 0, 2, true, 179796874526978985⟩,
  .shared 126 50 38 ⟨.tilted, 1, 2, true, 187102215852967964⟩], by decide +kernel⟩
private def b70 : PaidBatch .empty 6 := ⟨[
  .shared 126 51 39 ⟨.tilted, 1, 2, true, 194523008057223527⟩,
  .shared 126 52 41 ⟨.tilted, 1, 2, true, 202057327552471684⟩,
  .shared 126 53 42 ⟨.tilted, 1, 2, true, 209703250751438449⟩], by decide +kernel⟩
private def b71 : PaidBatch .empty 6 := ⟨[
  .point 127 42 45,
  .point 127 43 46,
  .point 127 44 47], by decide +kernel⟩
private def b72 : PaidBatch .empty 6 := ⟨[
  .point 127 45 48,
  .shared 127 46 38 ⟨.tilted, 0, 1, false, 147019140617136624⟩,
  .shared 127 47 39 ⟨.tilted, 0, 1, false, 153133202613514705⟩], by decide +kernel⟩
private def b73 : PaidBatch .empty 6 := ⟨[
  .shared 127 48 36 ⟨.tilted, 0, 2, true, 173965108439043432⟩,
  .shared 127 49 37 ⟨.tilted, 0, 2, true, 181212706515662101⟩,
  .shared 127 50 38 ⟨.tilted, 1, 2, true, 188578961449337332⟩], by decide +kernel⟩
private def b74 : PaidBatch .empty 6 := ⟨[
  .shared 127 51 40 ⟨.tilted, 1, 2, true, 196061949652795139⟩,
  .shared 127 52 42 ⟨.tilted, 1, 2, true, 203659747538761532⟩,
  .shared 127 53 43 ⟨.tilted, 1, 2, true, 211370431519962525⟩], by decide +kernel⟩
private def b75 : PaidBatch .empty 6 := ⟨[
  .point 128 42 45,
  .point 128 43 46,
  .point 128 44 48], by decide +kernel⟩
private def b76 : PaidBatch .empty 6 := ⟨[
  .shared 128 45 37 ⟨.tilted, 0, 1, false, 142077808366376493⟩,
  .shared 128 46 38 ⟨.tilted, 0, 1, false, 148140165042240720⟩,
  .shared 128 47 39 ⟨.tilted, 0, 1, false, 154302370165192630⟩], by decide +kernel⟩
private def b77 : PaidBatch .empty 6 := ⟨[
  .shared 128 48 36 ⟨.tilted, 0, 2, true, 175321309211556288⟩,
  .shared 128 49 38 ⟨.tilted, 0, 2, true, 182628538504345217⟩,
  .shared 128 50 39 ⟨.tilted, 0, 2, true, 190055707045706700⟩], by decide +kernel⟩
private def b78 : PaidBatch .empty 6 := ⟨[
  .shared 128 51 41 ⟨.tilted, 1, 2, true, 197600891248366751⟩,
  .shared 128 52 42 ⟨.tilted, 1, 2, true, 205262167525051380⟩,
  .shared 128 53 44 ⟨.tilted, 1, 2, true, 213037612288486601⟩], by decide +kernel⟩
private def b79 : PaidBatch .empty 6 := ⟨[
  .point 129 42 46,
  .point 129 43 47,
  .point 129 44 48], by decide +kernel⟩
private def b80 : PaidBatch .empty 6 := ⟨[
  .shared 129 45 38 ⟨.tilted, 0, 1, false, 143151651458543754⟩,
  .shared 129 46 39 ⟨.tilted, 0, 1, false, 149261189467344816⟩,
  .shared 129 47 40 ⟨.tilted, 0, 1, false, 155471537716870555⟩], by decide +kernel⟩
private def b81 : PaidBatch .empty 6 := ⟨[
  .shared 129 48 37 ⟨.tilted, 0, 2, true, 176677509984069144⟩,
  .shared 129 49 38 ⟨.tilted, 0, 2, true, 184044370493028333⟩,
  .shared 129 50 40 ⟨.tilted, 0, 2, true, 191532452642076068⟩], by decide +kernel⟩
private def b82 : PaidBatch .empty 6 := ⟨[
  .shared 129 51 41 ⟨.tilted, 1, 2, true, 199139832843938363⟩,
  .shared 129 52 43 ⟨.tilted, 1, 2, true, 206864587511341228⟩,
  .shared 129 53 45 ⟨.tilted, 1, 2, true, 214704793057010677⟩], by decide +kernel⟩
private def batches : List (PaidBatch .empty 6) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 129 18 2 = true := by decide +kernel
private theorem i20 : checks tiles 129 20 2 = true := by decide +kernel
private theorem i22 : checks tiles 129 22 2 = true := by decide +kernel
private theorem i24 : checks tiles 129 24 2 = true := by decide +kernel
private theorem i26 : checks tiles 129 26 2 = true := by decide +kernel
private theorem i28 : checks tiles 129 28 2 = true := by decide +kernel
private theorem i30 : checks tiles 129 30 2 = true := by decide +kernel
private theorem i32 : checks tiles 129 32 2 = true := by decide +kernel
private theorem i34 : checks tiles 129 34 2 = true := by decide +kernel
private theorem i36 : checks tiles 129 36 2 = true := by decide +kernel
private theorem i38 : checks tiles 129 38 2 = true := by decide +kernel
private theorem i40 : checks tiles 129 40 2 = true := by decide +kernel
private theorem i42 : checks tiles 129 42 2 = true := by decide +kernel
private theorem i44 : checks tiles 129 44 2 = true := by decide +kernel
private theorem i46 : checks tiles 129 46 2 = true := by decide +kernel
private theorem i48 : checks tiles 129 48 2 = true := by decide +kernel
private theorem i50 : checks tiles 129 50 2 = true := by decide +kernel
private theorem i52 : checks tiles 129 52 2 = true := by decide +kernel
def receipt : Certificate .empty 6 := ⟨batches, checks_join i18 (checks_join i20 (checks_join i22 (checks_join i24 (checks_join i26 (checks_join i28 (checks_join i30 (checks_join i32 (checks_join i34 (checks_join i36 (checks_join i38 (checks_join i40 (checks_join i42 (checks_join i44 (checks_join i46 (checks_join i48 (checks_join i50 i52))))))))))))))))⟩
end Top6


end Low53At2389PriceTableEmpty6
