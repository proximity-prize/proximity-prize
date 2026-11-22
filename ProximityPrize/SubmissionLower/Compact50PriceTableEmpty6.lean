import ProximityPrize.SubmissionLower.Compact50Cover
import ProximityPrize.SubmissionLower.Compact50PriceTableEmpty4 -- serialize candidate build

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableEmpty6
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top6
private def batch0 : PaidBatch .empty 6 := ⟨[
  .rectangle 6 18 99 25 31,
  .rectangle 9 26 97 33 37,
  .rectangle 12 34 82 41 37,
  .rectangle 14 42 85 49 44,
  .rectangle 17 50 88 53 44,
  .rectangle 83 34 114 38 44], by decide +kernel⟩
private def batch1 : PaidBatch .empty 6 := ⟨[
  .rectangle 83 39 107 42 44,
  .rectangle 86 43 103 46 46,
  .rectangle 86 47 98 50 47,
  .rectangle 89 51 96 53 47,
  .rectangle 97 51 103 51 47,
  .rectangle 97 52 101 52 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 6 := ⟨[
  .rectangle 97 53 100 53 47,
  .rectangle 98 26 126 31 42,
  .rectangle 98 32 123 36 45,
  .rectangle 99 47 107 48 47,
  .rectangle 99 49 103 50 47,
  .rectangle 100 18 126 25 39], by decide +kernel⟩
private def batch3 : PaidBatch .empty 6 := ⟨[
  .rectangle 101 53 102 53 48,
  .rectangle 102 52 103 52 48,
  .point 103 53 48,
  .rectangle 104 43 113 44 46,
  .rectangle 104 45 111 46 47,
  .rectangle 104 49 107 49 47], by decide +kernel⟩
private def batch4 : PaidBatch .empty 6 := ⟨[
  .rectangle 104 50 105 50 47,
  .point 104 51 47,
  .point 104 52 48,
  .point 104 53 48,
  .rectangle 105 51 105 51 48,
  .point 105 52 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 6 := ⟨[
  .point 105 53 48,
  .point 106 50 47,
  .point 106 51 48,
  .point 106 52 48,
  .point 106 53 48,
  .point 107 50 47], by decide +kernel⟩
private def batch6 : PaidBatch .empty 6 := ⟨[
  .point 107 51 48,
  .point 107 52 48,
  .point 107 53 48,
  .rectangle 108 39 124 40 46,
  .rectangle 108 41 118 42 46,
  .rectangle 108 47 111 47 47], by decide +kernel⟩
private def batch7 : PaidBatch .empty 6 := ⟨[
  .rectangle 108 48 109 48 47,
  .point 108 49 47,
  .point 108 50 47,
  .point 108 51 48,
  .point 108 52 48,
  .point 108 53 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 6 := ⟨[
  .point 109 49 47,
  .point 109 50 47,
  .point 109 51 48,
  .point 109 52 48,
  .point 109 53 48,
  .point 110 48 47], by decide +kernel⟩
private def batch9 : PaidBatch .empty 6 := ⟨[
  .point 110 49 47,
  .point 110 50 47,
  .point 110 51 48,
  .point 110 52 48,
  .shared 110 53 48 ⟨.tilted, 1, 2, true, 183031101328955966⟩,
  .point 111 48 47], by decide +kernel⟩
private def batch10 : PaidBatch .empty 6 := ⟨[
  .point 111 49 47,
  .point 111 50 48,
  .point 111 51 48,
  .point 111 52 48,
  .shared 111 53 48 ⟨.tilted, 1, 2, true, 184698307081951858⟩,
  .rectangle 112 45 116 45 47], by decide +kernel⟩
private def batch11 : PaidBatch .empty 6 := ⟨[
  .rectangle 112 46 113 46 47,
  .point 112 47 47,
  .point 112 48 47,
  .point 112 49 47,
  .point 112 50 48,
  .point 112 51 48], by decide +kernel⟩
private def batch12 : PaidBatch .empty 6 := ⟨[
  .shared 112 52 48 ⟨.tilted, 1, 2, true, 179626139592117276⟩,
  .shared 112 53 48 ⟨.tilted, 1, 2, true, 186365512834947750⟩,
  .point 113 47 47,
  .point 113 48 47,
  .point 113 49 47,
  .point 113 50 48], by decide +kernel⟩
private def batch13 : PaidBatch .empty 6 := ⟨[
  .point 113 51 48,
  .shared 113 52 48 ⟨.tilted, 1, 2, true, 181228583592369860⟩,
  .shared 113 53 48 ⟨.tilted, 1, 2, true, 188032718587943642⟩,
  .rectangle 114 43 121 43 47,
  .rectangle 114 44 118 44 47,
  .point 114 46 47], by decide +kernel⟩
private def batch14 : PaidBatch .empty 6 := ⟨[
  .point 114 47 47,
  .point 114 48 47,
  .point 114 49 47,
  .point 114 50 48,
  .shared 114 51 48 ⟨.tilted, 1, 2, true, 176058347291716040⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, true, 182831027592622444⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 6 := ⟨[
  .shared 114 53 48 ⟨.tilted, 1, 2, true, 189699924340939534⟩,
  .rectangle 115 37 129 38 46,
  .point 115 46 47,
  .point 115 47 47,
  .point 115 48 47,
  .point 115 49 47], by decide +kernel⟩
private def batch16 : PaidBatch .empty 6 := ⟨[
  .point 115 50 48,
  .shared 115 51 48 ⟨.tilted, 1, 2, true, 177597311949959308⟩,
  .shared 115 52 48 ⟨.tilted, 1, 2, true, 184433471592875028⟩,
  .shared 115 53 48 ⟨.tilted, 1, 2, true, 191367130093935426⟩,
  .point 116 46 47,
  .point 116 47 47], by decide +kernel⟩
private def batch17 : PaidBatch .empty 6 := ⟨[
  .point 116 48 47,
  .point 116 49 48,
  .shared 116 50 48 ⟨.tilted, 1, 2, true, 172337342508257196⟩,
  .shared 116 51 48 ⟨.tilted, 1, 2, true, 179136276608202576⟩,
  .shared 116 52 48 ⟨.tilted, 1, 2, true, 186035915593127612⟩,
  .shared 116 53 48 ⟨.tilted, 1, 2, true, 193034335846931318⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 6 := ⟨[
  .point 117 45 47,
  .point 117 46 47,
  .point 117 47 47,
  .point 117 48 47,
  .point 117 49 48,
  .shared 117 50 48 ⟨.tilted, 1, 2, true, 173814110235225140⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 6 := ⟨[
  .shared 117 51 48 ⟨.tilted, 1, 2, true, 180675241266445844⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 187638359593380196⟩,
  .shared 117 53 48 ⟨.tilted, 1, 2, true, 194701541599927210⟩,
  .point 118 45 47,
  .point 118 46 47,
  .point 118 47 47], by decide +kernel⟩
private def batch20 : PaidBatch .empty 6 := ⟨[
  .shared 118 48 47 ⟨.tilted, 1, 1, false, 155072102791060714⟩,
  .shared 118 49 48 ⟨.tilted, 1, 2, true, 168472743322245686⟩,
  .shared 118 50 48 ⟨.tilted, 1, 2, true, 175290877962193084⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, true, 182214205924689112⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, true, 189240803593632780⟩,
  .shared 118 53 48 ⟨.tilted, 1, 2, true, 196368747352923102⟩], by decide +kernel⟩
private def batch21 : PaidBatch .empty 6 := ⟨[
  .rectangle 119 41 127 41 47,
  .rectangle 119 42 124 42 47,
  .point 119 44 47,
  .point 119 45 47,
  .point 119 46 47,
  .point 119 47 47], by decide +kernel⟩
private def batch22 : PaidBatch .empty 6 := ⟨[
  .shared 119 48 47 ⟨.tilted, 1, 1, false, 156359358703866716⟩,
  .shared 119 49 48 ⟨.tilted, 1, 2, true, 169888596528672298⟩,
  .shared 119 50 48 ⟨.tilted, 1, 2, true, 176767645689161028⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 183753170582932380⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, true, 190843247593885364⟩,
  .shared 119 53 48 ⟨.tilted, 1, 2, true, 198035953105918994⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 6 := ⟨[
  .point 120 44 47,
  .point 120 45 47,
  .point 120 46 47,
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 151353346617988264⟩,
  .shared 120 48 47 ⟨.tilted, 1, 1, false, 157646614616672718⟩,
  .shared 120 49 48 ⟨.tilted, 1, 2, true, 171304449735098910⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 6 := ⟨[
  .shared 120 50 48 ⟨.tilted, 1, 2, true, 178244413416128972⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 185292135241175648⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, true, 192445691594137948⟩,
  .shared 120 53 48 ⟨.tilted, 1, 2, true, 199703158858914886⟩,
  .point 121 44 47,
  .point 121 45 47], by decide +kernel⟩
private def batch25 : PaidBatch .empty 6 := ⟨[
  .point 121 46 47,
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 152586874853207512⟩,
  .shared 121 48 47 ⟨.tilted, 1, 1, false, 158933870529478720⟩,
  .shared 121 49 48 ⟨.tilted, 1, 2, true, 172720302941525522⟩,
  .shared 121 50 48 ⟨.tilted, 1, 2, true, 179721181143096916⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, true, 186831099899418916⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 6 := ⟨[
  .shared 121 52 48 ⟨.tilted, 1, 2, true, 194048135594390532⟩,
  .shared 121 53 48 ⟨.tilted, 1, 2, true, 201370364611910778⟩,
  .point 122 43 47,
  .point 122 44 47,
  .point 122 45 47,
  .point 122 46 47], by decide +kernel⟩
private def batch27 : PaidBatch .empty 6 := ⟨[
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 153820403088426759⟩,
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 160221126442284722⟩,
  .shared 122 49 48 ⟨.tilted, 1, 2, true, 174136156147952134⟩,
  .shared 122 50 48 ⟨.tilted, 1, 2, true, 181197948870064860⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, true, 188370064557662184⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, true, 195650579594643116⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 6 := ⟨[
  .shared 122 53 48 ⟨.tilted, 1, 2, true, 203037570364906670⟩,
  .point 123 43 47,
  .point 123 44 47,
  .point 123 45 47,
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 148704967500009288⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 155053931323646007⟩], by decide +kernel⟩
private def batch29 : PaidBatch .empty 6 := ⟨[
  .shared 123 48 48 ⟨.tilted, 0, 2, true, 168542831104044264⟩,
  .shared 123 49 48 ⟨.tilted, 1, 2, true, 175552009354378746⟩,
  .shared 123 50 48 ⟨.tilted, 1, 2, true, 182674716597032804⟩,
  .shared 123 51 48 ⟨.tilted, 1, 2, true, 189909029215905452⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, true, 197253023594895700⟩,
  .shared 123 53 48 ⟨.tilted, 1, 2, true, 204704776117902562⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 6 := ⟨[
  .rectangle 124 32 129 35 45,
  .rectangle 124 36 129 37 46,
  .point 124 43 47,
  .point 124 44 47,
  .point 124 45 47,
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 149885890167034024⟩], by decide +kernel⟩
private def batch31 : PaidBatch .empty 6 := ⟨[
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 156287459558865254⟩,
  .shared 124 48 48 ⟨.tilted, 0, 2, true, 169899052200663536⟩,
  .shared 124 49 48 ⟨.tilted, 1, 2, true, 176967862560805358⟩,
  .shared 124 50 48 ⟨.tilted, 1, 2, true, 184151484324000748⟩,
  .shared 124 51 48 ⟨.tilted, 1, 2, true, 191447993874148720⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 198855467595148284⟩], by decide +kernel⟩
private def batch32 : PaidBatch .empty 6 := ⟨[
  .shared 124 53 48 ⟨.tilted, 1, 2, true, 206371981870898454⟩,
  .rectangle 125 39 129 39 46,
  .rectangle 125 40 129 40 47,
  .point 125 42 47,
  .point 125 43 47,
  .point 125 44 47], by decide +kernel⟩
private def batch33 : PaidBatch .empty 6 := ⟨[
  .point 125 45 47,
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 151066812834058760⟩,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 157520987794084502⟩,
  .shared 125 48 48 ⟨.tilted, 0, 2, true, 171255273297282808⟩,
  .shared 125 49 48 ⟨.tilted, 0, 2, true, 178383715767231970⟩,
  .shared 125 50 48 ⟨.tilted, 1, 2, true, 185628252050968692⟩], by decide +kernel⟩
private def batch34 : PaidBatch .empty 6 := ⟨[
  .shared 125 51 48 ⟨.tilted, 1, 2, true, 192986958532391988⟩,
  .shared 125 52 48 ⟨.tilted, 1, 2, true, 200457911595400868⟩,
  .shared 125 53 48 ⟨.tilted, 1, 2, true, 208039187623894346⟩,
  .point 126 42 47,
  .point 126 43 47,
  .point 126 44 47], by decide +kernel⟩
private def batch35 : PaidBatch .empty 6 := ⟨[
  .shared 126 45 47 ⟨.tilted, 0, 1, false, 145851491672936337⟩,
  .shared 126 46 47 ⟨.tilted, 0, 1, false, 152247735501083496⟩,
  .shared 126 47 47 ⟨.tilted, 0, 1, false, 158754516029303749⟩,
  .shared 126 48 48 ⟨.tilted, 0, 2, true, 172611494393902080⟩,
  .shared 126 49 48 ⟨.tilted, 0, 2, true, 179799568973658582⟩,
  .shared 126 50 48 ⟨.tilted, 1, 2, true, 187105019777936636⟩], by decide +kernel⟩
private def batch36 : PaidBatch .empty 6 := ⟨[
  .shared 126 51 48 ⟨.tilted, 1, 2, true, 194525923190635256⟩,
  .shared 126 52 48 ⟨.tilted, 1, 2, true, 202060355595653452⟩,
  .shared 126 53 48 ⟨.tilted, 1, 2, true, 209706393376890238⟩,
  .rectangle 127 18 129 24 39,
  .rectangle 127 25 129 30 42,
  .rectangle 127 31 129 34 45], by decide +kernel⟩
private def batch37 : PaidBatch .empty 6 := ⟨[
  .point 127 42 47,
  .point 127 43 47,
  .point 127 44 47,
  .shared 127 45 47 ⟨.tilted, 0, 1, false, 146980930881158804⟩,
  .shared 127 46 47 ⟨.tilted, 0, 1, false, 153428658168108232⟩,
  .shared 127 47 47 ⟨.tilted, 0, 1, false, 159988044264522997⟩], by decide +kernel⟩
private def batch38 : PaidBatch .empty 6 := ⟨[
  .shared 127 48 48 ⟨.tilted, 0, 2, true, 173967715490521352⟩,
  .shared 127 49 48 ⟨.tilted, 0, 2, true, 181215422180085194⟩,
  .shared 127 50 48 ⟨.tilted, 1, 2, true, 188581787504904580⟩,
  .shared 127 51 48 ⟨.tilted, 1, 2, true, 196064887848878524⟩,
  .shared 127 52 48 ⟨.tilted, 1, 2, true, 203662799595906036⟩,
  .shared 127 53 48 ⟨.tilted, 1, 2, true, 211373599129886130⟩], by decide +kernel⟩
private def batch39 : PaidBatch .empty 6 := ⟨[
  .point 128 41 47,
  .point 128 42 47,
  .point 128 43 47,
  .point 128 44 47,
  .shared 128 45 47 ⟨.tilted, 0, 1, false, 148110370089381272⟩,
  .shared 128 46 47 ⟨.tilted, 0, 1, false, 154609580835132968⟩], by decide +kernel⟩
private def batch40 : PaidBatch .empty 6 := ⟨[
  .shared 128 47 47 ⟨.tilted, 0, 1, false, 161221572499742244⟩,
  .shared 128 48 48 ⟨.tilted, 0, 2, true, 175323936587140624⟩,
  .shared 128 49 48 ⟨.tilted, 0, 2, true, 182631275386511806⟩,
  .shared 128 50 48 ⟨.tilted, 0, 2, true, 190058555231872524⟩,
  .shared 128 51 48 ⟨.tilted, 1, 2, true, 197603852507121792⟩,
  .shared 128 52 48 ⟨.tilted, 1, 2, true, 205265243596158620⟩], by decide +kernel⟩
private def batch41 : PaidBatch .empty 6 := ⟨[
  .shared 128 53 48 ⟨.tilted, 1, 2, true, 213040804882882022⟩,
  .point 129 41 47,
  .point 129 42 47,
  .point 129 43 47,
  .shared 129 44 47 ⟨.tilted, 0, 1, false, 142804701285387960⟩,
  .shared 129 45 47 ⟨.tilted, 0, 1, false, 149239809297603739⟩], by decide +kernel⟩
private def batch42 : PaidBatch .empty 6 := ⟨[
  .shared 129 46 47 ⟨.tilted, 0, 1, false, 155790503502157704⟩,
  .shared 129 47 47 ⟨.tilted, 0, 1, false, 162455100734961492⟩,
  .shared 129 48 48 ⟨.tilted, 0, 2, true, 176680157683759896⟩,
  .shared 129 49 48 ⟨.tilted, 0, 2, true, 184047128592938418⟩,
  .shared 129 50 48 ⟨.tilted, 0, 2, true, 191535322958840468⟩,
  .shared 129 51 48 ⟨.tilted, 1, 2, true, 199142817165365060⟩], by decide +kernel⟩
private def batch43 : PaidBatch .empty 6 := ⟨[
  .shared 129 52 48 ⟨.tilted, 1, 2, true, 206867687596411204⟩,
  .shared 129 53 49 ⟨.tilted, 1, 2, true, 214708010635877914⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 6) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32, batch33, batch34, batch35, batch36, batch37, batch38, batch39, batch40, batch41, batch42, batch43]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 129 18 10 = true := by decide +kernel
private theorem index28 : checks tiles 129 28 10 = true := by decide +kernel
theorem index38 : checks tiles 129 38 10 = true := by decide +kernel
theorem index48 : checks tiles 129 48 6 = true := by decide +kernel
private theorem covers : checks tiles 129 18 36 = true :=
  checks_join (checks_join (checks_join (index18) index28) index38) index48

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 6 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7
private def batch0 : PaidBatch .empty 7 := ⟨[
  .rectangle 7 21 92 28 31,
  .rectangle 10 29 90 36 37,
  .rectangle 13 37 76 44 37,
  .rectangle 15 45 80 52 44,
  .rectangle 18 53 91 53 44,
  .rectangle 77 37 106 41 44], by decide +kernel⟩
private def batch1 : PaidBatch .empty 7 := ⟨[
  .rectangle 77 42 100 45 44,
  .rectangle 81 46 99 49 47,
  .rectangle 81 50 96 52 47,
  .rectangle 91 29 127 33 43,
  .rectangle 91 34 120 37 44,
  .rectangle 92 53 98 53 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 7 := ⟨[
  .rectangle 93 21 129 27 40,
  .rectangle 93 28 129 32 43,
  .rectangle 97 50 103 50 47,
  .rectangle 97 51 101 51 47,
  .rectangle 97 52 100 52 47,
  .rectangle 99 53 100 53 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 7 := ⟨[
  .rectangle 100 46 107 47 47,
  .rectangle 100 48 108 48 47,
  .rectangle 100 49 105 49 47,
  .rectangle 101 42 115 43 46,
  .rectangle 101 44 112 45 47,
  .rectangle 101 52 102 52 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 7 := ⟨[
  .point 101 53 48,
  .point 102 51 47,
  .point 102 53 48,
  .point 103 51 47,
  .point 103 52 48,
  .point 103 53 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 7 := ⟨[
  .point 104 50 47,
  .point 104 51 47,
  .point 104 52 48,
  .point 104 53 48,
  .point 105 50 47,
  .point 105 51 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 7 := ⟨[
  .point 105 52 48,
  .point 105 53 48,
  .point 106 49 47,
  .point 106 50 47,
  .point 106 51 48,
  .point 106 52 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 7 := ⟨[
  .point 106 53 48,
  .rectangle 107 38 120 40 46,
  .rectangle 107 41 117 42 46,
  .point 107 49 47,
  .point 107 50 47,
  .point 107 51 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 7 := ⟨[
  .point 107 52 48,
  .point 107 53 48,
  .rectangle 108 46 112 46 47,
  .rectangle 108 47 110 47 47,
  .point 108 49 47,
  .point 108 50 47], by decide +kernel⟩
private def batch9 : PaidBatch .empty 7 := ⟨[
  .point 108 51 48,
  .point 108 52 48,
  .shared 108 53 48 ⟨.tilted, 1, 2, true, 184279321312510336⟩,
  .point 109 48 47,
  .point 109 49 47,
  .point 109 50 47], by decide +kernel⟩
private def batch10 : PaidBatch .empty 7 := ⟨[
  .point 109 51 48,
  .point 109 52 48,
  .shared 109 53 48 ⟨.tilted, 1, 2, true, 185946527065506228⟩,
  .point 110 48 47,
  .point 110 49 47,
  .point 110 50 47], by decide +kernel⟩
private def batch11 : PaidBatch .empty 7 := ⟨[
  .point 110 51 48,
  .shared 110 52 48 ⟨.tilted, 1, 2, true, 180729180043474368⟩,
  .shared 110 53 48 ⟨.tilted, 1, 2, true, 187613732818502120⟩,
  .point 111 47 47,
  .point 111 48 47,
  .point 111 49 47], by decide +kernel⟩
private def batch12 : PaidBatch .empty 7 := ⟨[
  .point 111 50 48,
  .point 111 51 48,
  .shared 111 52 48 ⟨.tilted, 1, 2, true, 182331624043726952⟩,
  .shared 111 53 48 ⟨.tilted, 1, 2, true, 189280938571498012⟩,
  .point 112 47 47,
  .point 112 48 47], by decide +kernel⟩
private def batch13 : PaidBatch .empty 7 := ⟨[
  .point 112 49 47,
  .point 112 50 48,
  .shared 112 51 48 ⟨.tilted, 1, 2, true, 177022139360520565⟩,
  .shared 112 52 48 ⟨.tilted, 1, 2, true, 183934068043979536⟩,
  .shared 112 53 48 ⟨.tilted, 1, 2, true, 190948144324493904⟩,
  .rectangle 113 44 117 44 47], by decide +kernel⟩
private def batch14 : PaidBatch .empty 7 := ⟨[
  .rectangle 113 45 115 45 47,
  .point 113 46 47,
  .point 113 47 47,
  .point 113 48 47,
  .point 113 49 47,
  .point 113 50 48], by decide +kernel⟩
private def batch15 : PaidBatch .empty 7 := ⟨[
  .shared 113 51 48 ⟨.tilted, 1, 2, true, 178561104018763833⟩,
  .shared 113 52 48 ⟨.tilted, 1, 2, true, 185536512044232120⟩,
  .shared 113 53 48 ⟨.tilted, 1, 2, true, 192615350077489796⟩,
  .point 114 46 47,
  .point 114 47 47,
  .point 114 48 47], by decide +kernel⟩
private def batch16 : PaidBatch .empty 7 := ⟨[
  .shared 114 49 47 ⟨.tilted, 1, 1, false, 160775151539115618⟩,
  .shared 114 50 48 ⟨.tilted, 1, 2, true, 173167817344153869⟩,
  .shared 114 51 48 ⟨.tilted, 1, 2, true, 180100068677007101⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, true, 187138956044484704⟩,
  .shared 114 53 48 ⟨.tilted, 1, 2, true, 194282555830485688⟩,
  .point 115 46 47], by decide +kernel⟩
private def batch17 : PaidBatch .empty 7 := ⟨[
  .point 115 47 47,
  .point 115 48 47,
  .shared 115 49 47 ⟨.tilted, 1, 2, true, 169838432724454746⟩,
  .shared 115 50 48 ⟨.tilted, 1, 2, true, 174644585071121813⟩,
  .shared 115 51 48 ⟨.tilted, 1, 2, true, 181639033335250369⟩,
  .shared 115 52 48 ⟨.tilted, 1, 2, true, 188741400044737288⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 7 := ⟨[
  .shared 115 53 48 ⟨.tilted, 1, 2, true, 195949761583481580⟩,
  .rectangle 116 43 120 43 47,
  .point 116 45 47,
  .point 116 46 47,
  .point 116 47 47,
  .shared 116 48 47 ⟨.tilted, 1, 1, false, 157035467207293674⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 7 := ⟨[
  .point 116 49 48,
  .shared 116 50 48 ⟨.tilted, 1, 2, true, 176121352798089757⟩,
  .shared 116 51 48 ⟨.tilted, 1, 2, true, 183177997993493637⟩,
  .shared 116 52 48 ⟨.tilted, 1, 2, true, 190343844044989872⟩,
  .shared 116 53 48 ⟨.tilted, 1, 2, true, 197616967336477472⟩,
  .point 117 45 47], by decide +kernel⟩
private def batch20 : PaidBatch .empty 7 := ⟨[
  .point 117 46 47,
  .point 117 47 47,
  .shared 117 48 47 ⟨.tilted, 1, 1, false, 158336108280534210⟩,
  .shared 117 49 48 ⟨.tilted, 1, 2, true, 170591685281305830⟩,
  .shared 117 50 48 ⟨.tilted, 1, 2, true, 177598120525057701⟩,
  .shared 117 51 48 ⟨.tilted, 1, 2, true, 184716962651736905⟩], by decide +kernel⟩
private def batch21 : PaidBatch .empty 7 := ⟨[
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 191946288045242456⟩,
  .shared 117 53 48 ⟨.tilted, 1, 2, true, 199284173089473364⟩,
  .rectangle 118 41 126 41 47,
  .rectangle 118 42 123 42 47,
  .point 118 44 47,
  .point 118 45 47], by decide +kernel⟩
private def batch22 : PaidBatch .empty 7 := ⟨[
  .point 118 46 47,
  .point 118 47 47,
  .shared 118 48 47 ⟨.tilted, 1, 1, false, 159636749353774745⟩,
  .shared 118 49 48 ⟨.tilted, 1, 2, true, 172007538487732442⟩,
  .shared 118 50 48 ⟨.tilted, 1, 2, true, 179074888252025645⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, true, 186255927309980173⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 7 := ⟨[
  .shared 118 52 48 ⟨.tilted, 1, 2, true, 193548732045495040⟩,
  .shared 118 53 48 ⟨.tilted, 1, 2, true, 200951378842469256⟩,
  .point 119 44 47,
  .point 119 45 47,
  .point 119 46 47,
  .shared 119 47 47 ⟨.tilted, 1, 1, false, 154427021016258281⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 7 := ⟨[
  .shared 119 48 47 ⟨.tilted, 1, 1, false, 160937390427015281⟩,
  .shared 119 49 48 ⟨.tilted, 1, 2, true, 173423391694159054⟩,
  .shared 119 50 48 ⟨.tilted, 1, 2, true, 180551655978993589⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 187794891968223441⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, true, 195151176045747624⟩,
  .shared 119 53 48 ⟨.tilted, 1, 2, true, 202618584595465148⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 7 := ⟨[
  .point 120 44 47,
  .point 120 45 47,
  .point 120 46 47,
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 155673453507886815⟩,
  .shared 120 48 47 ⟨.tilted, 1, 1, false, 162238031500255816⟩,
  .shared 120 49 48 ⟨.tilted, 1, 2, true, 174839244900585666⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 7 := ⟨[
  .shared 120 50 48 ⟨.tilted, 1, 2, true, 182028423705961533⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 189333856626466709⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, true, 196753620046000208⟩,
  .shared 120 53 48 ⟨.tilted, 1, 2, true, 204285790348461040⟩,
  .rectangle 121 34 129 36 45,
  .rectangle 121 37 129 38 46], by decide +kernel⟩
private def batch27 : PaidBatch .empty 7 := ⟨[
  .rectangle 121 39 129 39 46,
  .rectangle 121 40 129 40 47,
  .point 121 43 47,
  .point 121 44 47,
  .point 121 45 47,
  .point 121 46 47], by decide +kernel⟩
private def batch28 : PaidBatch .empty 7 := ⟨[
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 156919885999515349⟩,
  .shared 121 48 47 ⟨.tilted, 1, 1, false, 163538672573496352⟩,
  .shared 121 49 48 ⟨.tilted, 1, 2, true, 176255098107012278⟩,
  .shared 121 50 48 ⟨.tilted, 1, 2, true, 183505191432929477⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, true, 190872821284709977⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, true, 198356064046252792⟩], by decide +kernel⟩
private def batch29 : PaidBatch .empty 7 := ⟨[
  .shared 121 53 48 ⟨.tilted, 1, 2, true, 205952996101456932⟩,
  .point 122 43 47,
  .point 122 44 47,
  .point 122 45 47,
  .shared 122 46 47 ⟨.tilted, 0, 1, false, 151605623350383212⟩,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 158166318491143883⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 7 := ⟨[
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 164839313646736887⟩,
  .shared 122 49 48 ⟨.tilted, 1, 2, true, 177670951313438890⟩,
  .shared 122 50 48 ⟨.tilted, 1, 2, true, 184981959159897421⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, true, 192411785942953245⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, true, 199958508046505376⟩,
  .shared 122 53 48 ⟨.tilted, 1, 2, true, 207620201854452824⟩], by decide +kernel⟩
private def batch31 : PaidBatch .empty 7 := ⟨[
  .point 123 43 47,
  .point 123 44 47,
  .point 123 45 47,
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 152798969369791987⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 159412750982772417⟩,
  .shared 123 48 48 ⟨.tilted, 0, 2, true, 171836907116297914⟩], by decide +kernel⟩
private def batch32 : PaidBatch .empty 7 := ⟨[
  .shared 123 49 48 ⟨.tilted, 1, 2, true, 179086804519865502⟩,
  .shared 123 50 48 ⟨.tilted, 1, 2, true, 186458726886865365⟩,
  .shared 123 51 48 ⟨.tilted, 1, 2, true, 193950750601196513⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, true, 201560952046757960⟩,
  .shared 123 53 48 ⟨.tilted, 1, 2, true, 209287407607448716⟩,
  .point 124 42 47], by decide +kernel⟩
private def batch33 : PaidBatch .empty 7 := ⟨[
  .point 124 43 47,
  .point 124 44 47,
  .shared 124 45 47 ⟨.tilted, 0, 1, false, 147441674701705756⟩,
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 153992315389200763⟩,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 160659183474400951⟩,
  .shared 124 48 48 ⟨.tilted, 0, 2, true, 173193128212917186⟩], by decide +kernel⟩
private def batch34 : PaidBatch .empty 7 := ⟨[
  .shared 124 49 48 ⟨.tilted, 1, 2, true, 180502657726292114⟩,
  .shared 124 50 48 ⟨.tilted, 1, 2, true, 187935494613833309⟩,
  .shared 124 51 48 ⟨.tilted, 1, 2, true, 195489715259439781⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 203163396047010544⟩,
  .shared 124 53 48 ⟨.tilted, 1, 2, true, 210954613360444608⟩,
  .point 125 42 47], by decide +kernel⟩
private def batch35 : PaidBatch .empty 7 := ⟨[
  .point 125 43 47,
  .point 125 44 47,
  .shared 125 45 47 ⟨.tilted, 0, 1, false, 148583056358287016⟩,
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 155185661408609538⟩,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 161905615966029485⟩,
  .shared 125 48 48 ⟨.tilted, 0, 2, true, 174549349309536458⟩], by decide +kernel⟩
private def batch36 : PaidBatch .empty 7 := ⟨[
  .shared 125 49 48 ⟨.tilted, 0, 2, true, 181918510932718726⟩,
  .shared 125 50 48 ⟨.tilted, 1, 2, true, 189412262340801253⟩,
  .shared 125 51 48 ⟨.tilted, 1, 2, true, 197028679917683049⟩,
  .shared 125 52 48 ⟨.tilted, 1, 2, true, 204765840047263128⟩,
  .shared 125 53 48 ⟨.tilted, 1, 2, true, 212621819113440500⟩,
  .point 126 42 47], by decide +kernel⟩
private def batch37 : PaidBatch .empty 7 := ⟨[
  .point 126 43 47,
  .point 126 44 47,
  .shared 126 45 47 ⟨.tilted, 0, 1, false, 149724438014868276⟩,
  .shared 126 46 47 ⟨.tilted, 0, 1, false, 156379007428018314⟩,
  .shared 126 47 47 ⟨.tilted, 0, 1, false, 163152048457658019⟩,
  .shared 126 48 48 ⟨.tilted, 0, 2, true, 175905570406155730⟩], by decide +kernel⟩
private def batch38 : PaidBatch .empty 7 := ⟨[
  .shared 126 49 48 ⟨.tilted, 0, 2, true, 183334364139145338⟩,
  .shared 126 50 48 ⟨.tilted, 1, 2, true, 190889030067769197⟩,
  .shared 126 51 48 ⟨.tilted, 1, 2, true, 198567644575926317⟩,
  .shared 126 52 48 ⟨.tilted, 1, 2, true, 206368284047515712⟩,
  .shared 126 53 48 ⟨.tilted, 1, 2, true, 214289024866436392⟩,
  .point 127 41 47], by decide +kernel⟩
private def batch39 : PaidBatch .empty 7 := ⟨[
  .point 127 42 47,
  .point 127 43 47,
  .shared 127 44 47 ⟨.tilted, 0, 1, false, 144280562785442260⟩,
  .shared 127 45 47 ⟨.tilted, 0, 1, false, 150865819671449536⟩,
  .shared 127 46 47 ⟨.tilted, 0, 1, false, 157572353447427089⟩,
  .shared 127 47 47 ⟨.tilted, 0, 1, false, 164398480949286553⟩], by decide +kernel⟩
private def batch40 : PaidBatch .empty 7 := ⟨[
  .shared 127 48 48 ⟨.tilted, 0, 2, true, 177261791502775002⟩,
  .shared 127 49 48 ⟨.tilted, 0, 2, true, 184750217345571950⟩,
  .shared 127 50 48 ⟨.tilted, 1, 2, true, 192365797794737141⟩,
  .shared 127 51 48 ⟨.tilted, 1, 2, true, 200106609234169585⟩,
  .shared 127 52 48 ⟨.tilted, 1, 2, true, 207970728047768296⟩,
  .shared 127 53 48 ⟨.tilted, 1, 2, true, 215956230619432284⟩], by decide +kernel⟩
private def batch41 : PaidBatch .empty 7 := ⟨[
  .rectangle 128 33 129 35 45,
  .point 128 41 47,
  .point 128 42 47,
  .point 128 43 47,
  .shared 128 44 47 ⟨.tilted, 0, 1, false, 145371102188588247⟩,
  .shared 128 45 47 ⟨.tilted, 0, 1, false, 152007201328030796⟩], by decide +kernel⟩
private def batch42 : PaidBatch .empty 7 := ⟨[
  .shared 128 46 47 ⟨.tilted, 0, 1, false, 158765699466835865⟩,
  .shared 128 47 47 ⟨.tilted, 0, 1, false, 165644913440915087⟩,
  .shared 128 48 48 ⟨.tilted, 0, 2, true, 178618012599394274⟩,
  .shared 128 49 48 ⟨.tilted, 0, 2, true, 186166070551998562⟩,
  .shared 128 50 48 ⟨.tilted, 0, 2, true, 193842565521705085⟩,
  .shared 128 51 48 ⟨.tilted, 1, 2, true, 201645573892412853⟩], by decide +kernel⟩
private def batch43 : PaidBatch .empty 7 := ⟨[
  .shared 128 52 48 ⟨.tilted, 1, 2, true, 209573172048020880⟩,
  .shared 128 53 48 ⟨.tilted, 1, 2, true, 217623436372428176⟩,
  .point 129 41 47,
  .point 129 42 47,
  .point 129 43 47,
  .shared 129 44 47 ⟨.tilted, 0, 1, false, 146461641591734235⟩], by decide +kernel⟩
private def batch44 : PaidBatch .empty 7 := ⟨[
  .shared 129 45 47 ⟨.tilted, 0, 1, false, 153148582984612056⟩,
  .shared 129 46 47 ⟨.tilted, 0, 1, false, 159959045486244640⟩,
  .shared 129 47 47 ⟨.tilted, 0, 1, false, 166891345932543621⟩,
  .shared 129 48 48 ⟨.tilted, 0, 2, true, 179974233696013546⟩,
  .shared 129 49 48 ⟨.tilted, 0, 2, true, 187581923758425174⟩,
  .shared 129 50 48 ⟨.tilted, 0, 2, true, 195319333248673029⟩], by decide +kernel⟩
private def batch45 : PaidBatch .empty 7 := ⟨[
  .shared 129 51 48 ⟨.tilted, 1, 2, true, 203184538550656121⟩,
  .shared 129 52 48 ⟨.tilted, 1, 2, true, 211175616048273464⟩,
  .shared 129 53 49 ⟨.tilted, 1, 2, true, 219290642125424068⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 7) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32, batch33, batch34, batch35, batch36, batch37, batch38, batch39, batch40, batch41, batch42, batch43, batch44, batch45]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 129 21 10 = true := by decide +kernel
private theorem index31 : checks tiles 129 31 10 = true := by decide +kernel
theorem index41 : checks tiles 129 41 10 = true := by decide +kernel
theorem index51 : checks tiles 129 51 3 = true := by decide +kernel
private theorem covers : checks tiles 129 21 33 = true :=
  checks_join (checks_join (checks_join (index21) index31) index41) index51

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 7 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

end Compact50PriceTableEmpty6
