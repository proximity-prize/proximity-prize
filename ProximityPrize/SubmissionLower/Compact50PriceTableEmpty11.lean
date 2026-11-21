import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableEmpty11
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top11

private def batch0 : PaidBatch .empty 11 := ⟨[
  .rectangle 11 33 68 42 34,
  .rectangle 15 43 70 52 42,
  .rectangle 69 33 97 37 36,
  .rectangle 69 38 97 42 41,
  .rectangle 71 48 84 52 44,
  .rectangle 71 43 98 47 46], by decide +kernel⟩
private def batch1 : PaidBatch .empty 11 := ⟨[
  .rectangle 85 51 91 52 45,
  .rectangle 85 48 98 50 47,
  .rectangle 92 51 98 51 46,
  .rectangle 92 52 98 52 47,
  .rectangle 98 38 111 40 42,
  .rectangle 98 41 111 42 43], by decide +kernel⟩
private def batch2 : PaidBatch .empty 11 := ⟨[
  .rectangle 98 33 125 35 41,
  .rectangle 98 36 125 37 42,
  .rectangle 99 51 100 51 47,
  .rectangle 99 52 100 52 48,
  .rectangle 99 50 102 50 47,
  .rectangle 99 43 105 45 45], by decide +kernel⟩
private def batch3 : PaidBatch .empty 11 := ⟨[
  .rectangle 99 46 105 47 46,
  .rectangle 99 48 105 48 46,
  .rectangle 99 49 105 49 47,
  .point 101 51 45,
  .rectangle 101 52 101 52 48,
  .point 102 51 45], by decide +kernel⟩
private def batch4 : PaidBatch .empty 11 := ⟨[
  .point 102 52 46,
  .rectangle 103 50 103 50 47,
  .point 103 51 46,
  .point 103 52 46,
  .point 104 50 45,
  .point 104 51 46], by decide +kernel⟩
private def batch5 : PaidBatch .empty 11 := ⟨[
  .point 104 52 47,
  .point 105 50 45,
  .point 105 51 46,
  .point 105 52 47,
  .point 106 49 45,
  .point 106 50 46], by decide +kernel⟩
private def batch6 : PaidBatch .empty 11 := ⟨[
  .point 106 51 47,
  .point 106 52 48,
  .rectangle 106 48 107 48 47,
  .rectangle 106 47 109 47 47,
  .rectangle 106 43 112 44 46,
  .rectangle 106 45 112 45 46], by decide +kernel⟩
private def batch7 : PaidBatch .empty 11 := ⟨[
  .rectangle 106 46 112 46 47,
  .point 107 49 45,
  .point 107 50 46,
  .point 107 51 47,
  .point 107 52 48,
  .rectangle 108 48 108 48 47], by decide +kernel⟩
private def batch8 : PaidBatch .empty 11 := ⟨[
  .point 108 49 46,
  .point 108 50 47,
  .point 108 51 48,
  .shared 108 52 48 ⟨.tilted, 1, 1, false, 186408702870307792⟩,
  .point 109 48 45,
  .point 109 49 46], by decide +kernel⟩
private def batch9 : PaidBatch .empty 11 := ⟨[
  .point 109 50 47,
  .point 109 51 48,
  .shared 109 52 48 ⟨.tilted, 1, 1, false, 188015393522295413⟩,
  .rectangle 110 47 110 47 47,
  .point 110 48 45,
  .point 110 49 46], by decide +kernel⟩
private def batch10 : PaidBatch .empty 11 := ⟨[
  .point 110 50 47,
  .point 110 51 48,
  .shared 110 52 48 ⟨.tilted, 1, 2, true, 195615863086740073⟩,
  .point 111 47 45,
  .point 111 48 46,
  .point 111 49 47], by decide +kernel⟩
private def batch11 : PaidBatch .empty 11 := ⟨[
  .point 111 50 48,
  .shared 111 51 48 ⟨.tilted, 1, 1, false, 184027006786100551⟩,
  .shared 111 52 48 ⟨.tilted, 1, 2, true, 196918697304190081⟩,
  .point 112 47 45,
  .point 112 48 46,
  .point 112 49 47], by decide +kernel⟩
private def batch12 : PaidBatch .empty 11 := ⟨[
  .point 112 50 48,
  .shared 112 51 48 ⟨.tilted, 1, 1, false, 185574230964940351⟩,
  .shared 112 52 48 ⟨.tilted, 1, 2, true, 198588260027756923⟩,
  .rectangle 112 41 118 42 46,
  .rectangle 112 38 125 39 45,
  .rectangle 112 40 125 40 45], by decide +kernel⟩
private def batch13 : PaidBatch .empty 11 := ⟨[
  .rectangle 113 46 113 46 47,
  .point 113 47 45,
  .point 113 48 46,
  .shared 113 49 47 ⟨.tilted, 1, 1, false, 172814111143204792⟩,
  .shared 113 50 48 ⟨.tilted, 1, 1, false, 179911625809841033⟩,
  .shared 113 51 48 ⟨.tilted, 1, 1, false, 187121455143780152⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 11 := ⟨[
  .shared 113 52 48 ⟨.tilted, 1, 2, true, 200257822751323765⟩,
  .rectangle 113 45 116 45 47,
  .rectangle 113 43 119 43 46,
  .rectangle 113 44 119 44 47,
  .point 114 46 45,
  .point 114 47 46], by decide +kernel⟩
private def batch15 : PaidBatch .empty 11 := ⟨[
  .point 114 48 47,
  .shared 114 49 47 ⟨.tilted, 1, 1, false, 174245288405301453⟩,
  .shared 114 50 48 ⟨.tilted, 1, 1, false, 181400345525383846⟩,
  .shared 114 51 48 ⟨.tilted, 1, 1, false, 188668679322619952⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, false, 196048846782233521⟩,
  .point 115 46 45], by decide +kernel⟩
private def batch16 : PaidBatch .empty 11 := ⟨[
  .point 115 47 46,
  .point 115 48 47,
  .shared 115 49 47 ⟨.tilted, 1, 1, false, 175676465667398113⟩,
  .shared 115 50 48 ⟨.tilted, 1, 1, false, 182889065240926660⟩,
  .shared 115 51 48 ⟨.tilted, 1, 2, true, 195554937355608643⟩,
  .shared 115 52 48 ⟨.tilted, 1, 2, false, 197655537434221142⟩], by decide +kernel⟩
private def batch17 : PaidBatch .empty 11 := ⟨[
  .point 116 46 45,
  .point 116 47 47,
  .shared 116 48 47 ⟨.tilted, 0, 1, false, 169954144614151707⟩,
  .shared 116 49 48 ⟨.tilted, 1, 1, false, 177107642929494774⟩,
  .shared 116 50 48 ⟨.tilted, 1, 1, false, 184377784956469473⟩,
  .shared 116 51 48 ⟨.tilted, 1, 2, true, 197158361890807905⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 11 := ⟨[
  .shared 116 52 48 ⟨.tilted, 1, 2, false, 199262228086208764⟩,
  .point 117 45 45,
  .point 117 46 46,
  .point 117 47 47,
  .shared 117 48 47 ⟨.tilted, 0, 1, false, 171328741432653048⟩,
  .shared 117 49 48 ⟨.tilted, 1, 1, false, 178538820191591434⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 11 := ⟨[
  .shared 117 50 48 ⟨.tilted, 1, 1, false, 185866504672012287⟩,
  .shared 117 51 48 ⟨.tilted, 1, 2, true, 198761786426007168⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, false, 200868918738196385⟩,
  .point 118 45 45,
  .point 118 46 46,
  .point 118 47 47], by decide +kernel⟩
private def batch20 : PaidBatch .empty 11 := ⟨[
  .shared 118 48 47 ⟨.tilted, 0, 1, false, 172703338251154390⟩,
  .shared 118 49 48 ⟨.tilted, 0, 1, false, 179969997453688095⟩,
  .shared 118 50 48 ⟨.tilted, 1, 1, false, 187355224387555100⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, false, 194857576037979154⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, false, 202475609390184007⟩,
  .point 119 45 45], by decide +kernel⟩
private def batch21 : PaidBatch .empty 11 := ⟨[
  .point 119 46 47,
  .shared 119 47 47 ⟨.tilted, 0, 1, false, 166875668179487092⟩,
  .shared 119 48 47 ⟨.tilted, 0, 1, false, 174077935069655731⟩,
  .shared 119 49 48 ⟨.tilted, 0, 1, false, 181401174715784755⟩,
  .shared 119 50 48 ⟨.tilted, 1, 1, false, 188843944103097914⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, false, 196404800216818955⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 11 := ⟨[
  .shared 119 52 48 ⟨.tilted, 1, 2, false, 204082300042171628⟩,
  .rectangle 119 41 125 41 46,
  .rectangle 119 42 125 42 47,
  .point 120 44 45,
  .point 120 45 46,
  .point 120 46 47], by decide +kernel⟩
private def batch23 : PaidBatch .empty 11 := ⟨[
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 168194646564243948⟩,
  .shared 120 48 47 ⟨.tilted, 0, 1, false, 175452531888157073⟩,
  .shared 120 49 48 ⟨.tilted, 0, 1, false, 182832351977881416⟩,
  .shared 120 50 48 ⟨.tilted, 0, 1, false, 190332663818640727⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, false, 197952024395658755⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, false, 205688990694159250⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 11 := ⟨[
  .rectangle 120 43 122 43 47,
  .point 121 44 45,
  .point 121 45 46,
  .point 121 46 47,
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 169513624949000805⟩,
  .shared 121 48 47 ⟨.tilted, 0, 1, false, 176827128706658414⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 11 := ⟨[
  .shared 121 49 48 ⟨.tilted, 0, 1, false, 184263529239978076⟩,
  .shared 121 50 48 ⟨.tilted, 0, 2, true, 196886513276475566⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, false, 199499248574498556⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, false, 207295681346146871⟩,
  .point 122 44 45,
  .point 122 45 46], by decide +kernel⟩
private def batch26 : PaidBatch .empty 11 := ⟨[
  .shared 122 46 47 ⟨.tilted, 0, 1, false, 163588782942644705⟩,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 170832603333757661⟩,
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 178201725525159756⟩,
  .shared 122 49 48 ⟨.tilted, 0, 1, false, 185694706502074737⟩,
  .shared 122 50 48 ⟨.tilted, 0, 2, true, 198425135748100075⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, false, 201046472753338356⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 11 := ⟨[
  .shared 122 52 48 ⟨.tilted, 1, 2, false, 208902371998134493⟩,
  .point 123 43 45,
  .point 123 44 46,
  .point 123 45 47,
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 164853104903507911⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 172151581718514518⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 11 := ⟨[
  .shared 123 48 48 ⟨.tilted, 0, 1, false, 179576322343661097⟩,
  .shared 123 49 48 ⟨.tilted, 0, 1, false, 187125883764171397⟩,
  .shared 123 50 48 ⟨.tilted, 0, 2, true, 199963758219724583⟩,
  .shared 123 51 48 ⟨.tilted, 0, 2, false, 202593696932178157⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, false, 210509062650122114⟩,
  .point 124 43 45], by decide +kernel⟩
private def batch29 : PaidBatch .empty 11 := ⟨[
  .point 124 44 46,
  .point 124 45 47,
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 166117426864371116⟩,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 173470560103271374⟩,
  .shared 124 48 48 ⟨.tilted, 0, 1, false, 180950919162162439⟩,
  .shared 124 49 48 ⟨.tilted, 0, 1, false, 188557061026268058⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 11 := ⟨[
  .shared 124 50 48 ⟨.tilted, 0, 2, false, 196730679925018635⟩,
  .shared 124 51 48 ⟨.tilted, 0, 2, false, 204140921111017957⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, false, 212115753302109736⟩,
  .point 125 43 45,
  .point 125 44 46,
  .shared 125 45 47 ⟨.tilted, 0, 1, false, 160103590007058303⟩], by decide +kernel⟩
private def batch31 : PaidBatch .empty 11 := ⟨[
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 167381748825234322⟩,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 174789538488028231⟩,
  .shared 125 48 48 ⟨.tilted, 0, 1, false, 182325515980663780⟩,
  .shared 125 49 48 ⟨.tilted, 0, 1, false, 189988238288364718⟩,
  .shared 125 50 48 ⟨.tilted, 0, 2, false, 197776262396354795⟩,
  .shared 125 51 48 ⟨.tilted, 0, 2, false, 205688145289857758⟩], by decide +kernel⟩
private def batch32 : PaidBatch .empty 11 := ⟨[
  .shared 125 52 48 ⟨.tilted, 0, 2, false, 213722443954097357⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 11) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 125 33 8 = true := by decide +kernel
private theorem index41 : checks tiles 125 41 8 = true := by decide +kernel
private theorem index49 : checks tiles 125 49 4 = true := by decide +kernel
private theorem covers : checks tiles 125 33 20 = true :=
  checks_join index33 (checks_join index41 index49)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 11 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12

private def batch0 : PaidBatch .empty 12 := ⟨[
  .rectangle 12 36 68 44 35,
  .rectangle 15 45 68 52 39,
  .rectangle 69 49 83 52 43,
  .rectangle 69 36 97 40 39,
  .rectangle 69 41 97 44 42,
  .rectangle 69 45 97 48 46], by decide +kernel⟩
private def batch1 : PaidBatch .empty 12 := ⟨[
  .rectangle 84 51 90 52 45,
  .rectangle 84 49 97 50 46,
  .rectangle 91 51 97 51 46,
  .rectangle 91 52 97 52 47,
  .rectangle 98 51 99 51 47,
  .rectangle 98 52 99 52 48], by decide +kernel⟩
private def batch2 : PaidBatch .empty 12 := ⟨[
  .rectangle 98 50 101 50 47,
  .rectangle 98 45 104 46 45,
  .rectangle 98 47 104 48 47,
  .rectangle 98 49 104 49 47,
  .rectangle 98 41 111 42 43,
  .rectangle 98 43 111 44 45], by decide +kernel⟩
private def batch3 : PaidBatch .empty 12 := ⟨[
  .rectangle 98 36 125 38 45,
  .rectangle 98 39 125 40 46,
  .rectangle 100 51 100 51 47,
  .rectangle 100 52 100 52 48,
  .point 101 51 45,
  .point 101 52 46], by decide +kernel⟩
private def batch4 : PaidBatch .empty 12 := ⟨[
  .point 102 51 45,
  .point 102 52 46,
  .rectangle 102 50 103 50 47,
  .point 103 51 46,
  .point 103 52 47,
  .point 104 50 45], by decide +kernel⟩
private def batch5 : PaidBatch .empty 12 := ⟨[
  .point 104 51 46,
  .point 104 52 47,
  .rectangle 105 49 105 49 47,
  .point 105 50 45,
  .point 105 51 46,
  .point 105 52 47], by decide +kernel⟩
private def batch6 : PaidBatch .empty 12 := ⟨[
  .rectangle 105 47 108 47 46,
  .rectangle 105 48 108 48 47,
  .rectangle 105 45 111 45 45,
  .rectangle 105 46 111 46 47,
  .point 106 49 45,
  .point 106 50 46], by decide +kernel⟩
private def batch7 : PaidBatch .empty 12 := ⟨[
  .point 106 51 47,
  .point 106 52 48,
  .point 107 49 45,
  .point 107 50 46,
  .point 107 51 47,
  .point 107 52 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 12 := ⟨[
  .point 108 49 46,
  .point 108 50 47,
  .point 108 51 48,
  .shared 108 52 48 ⟨.tilted, 1, 1, false, 189216617331876114⟩,
  .point 109 48 45,
  .point 109 49 46], by decide +kernel⟩
private def batch9 : PaidBatch .empty 12 := ⟨[
  .point 109 50 47,
  .point 109 51 48,
  .shared 109 52 48 ⟨.tilted, 1, 1, false, 190842200784697037⟩,
  .rectangle 109 47 110 47 47,
  .point 110 48 45,
  .point 110 49 46], by decide +kernel⟩
private def batch10 : PaidBatch .empty 12 := ⟨[
  .point 110 50 47,
  .point 110 51 48,
  .shared 110 52 48 ⟨.tilted, 1, 2, true, 199829509108257540⟩,
  .point 111 47 45,
  .point 111 48 46,
  .point 111 49 47], by decide +kernel⟩
private def batch11 : PaidBatch .empty 12 := ⟨[
  .point 111 50 48,
  .shared 111 51 48 ⟨.tilted, 1, 1, false, 186666382480183120⟩,
  .shared 111 52 48 ⟨.tilted, 1, 2, false, 196618664604136458⟩,
  .point 112 47 45,
  .point 112 48 46,
  .point 112 49 47], by decide +kernel⟩
private def batch12 : PaidBatch .empty 12 := ⟨[
  .point 112 50 48,
  .shared 112 51 48 ⟨.tilted, 1, 1, false, 188231377115030249⟩,
  .shared 112 52 48 ⟨.tilted, 1, 2, false, 195718951143159806⟩,
  .rectangle 112 46 113 46 47,
  .rectangle 112 45 115 45 47,
  .rectangle 112 41 118 42 46], by decide +kernel⟩
private def batch13 : PaidBatch .empty 12 := ⟨[
  .rectangle 112 43 118 43 46,
  .rectangle 112 44 118 44 47,
  .point 113 47 45,
  .point 113 48 46,
  .shared 113 49 47 ⟨.tilted, 2, 1, false, 175055027744282450⟩,
  .shared 113 50 48 ⟨.tilted, 1, 1, false, 182366055127719201⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 12 := ⟨[
  .shared 113 51 48 ⟨.tilted, 1, 1, false, 189796371749877378⟩,
  .shared 113 52 48 ⟨.tilted, 1, 2, false, 197344534595980729⟩,
  .point 114 46 45,
  .point 114 47 46,
  .point 114 48 47,
  .shared 114 49 47 ⟨.tilted, 2, 1, false, 176501730772734493⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 12 := ⟨[
  .shared 114 50 48 ⟨.tilted, 1, 1, false, 183871422954443370⟩,
  .shared 114 51 48 ⟨.tilted, 1, 1, false, 191361366384724507⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, false, 198970118048801652⟩,
  .point 115 46 45,
  .point 115 47 46,
  .point 115 48 47], by decide +kernel⟩
private def batch16 : PaidBatch .empty 12 := ⟨[
  .shared 115 49 47 ⟨.tilted, 2, 1, false, 177948433801186536⟩,
  .shared 115 50 48 ⟨.tilted, 1, 1, false, 185376790781167539⟩,
  .shared 115 51 48 ⟨.tilted, 1, 2, true, 196596416503200385⟩,
  .shared 115 52 48 ⟨.tilted, 1, 2, false, 200595701501622575⟩,
  .rectangle 116 45 116 45 47,
  .point 116 46 45], by decide +kernel⟩
private def batch17 : PaidBatch .empty 12 := ⟨[
  .point 116 47 47,
  .shared 116 48 47 ⟨.tilted, 2, 1, false, 172031733334435628⟩,
  .shared 116 49 48 ⟨.tilted, 2, 1, false, 179395136829638579⟩,
  .shared 116 50 48 ⟨.tilted, 1, 1, false, 186882158607891708⟩,
  .shared 116 51 48 ⟨.tilted, 1, 2, false, 194491355654418765⟩,
  .shared 116 52 48 ⟨.tilted, 1, 2, false, 202221284954443498⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 12 := ⟨[
  .point 117 45 45,
  .point 117 46 46,
  .point 117 47 47,
  .shared 117 48 47 ⟨.tilted, 2, 1, false, 173420733574466379⟩,
  .shared 117 49 48 ⟨.tilted, 2, 1, false, 180841839858090622⟩,
  .shared 117 50 48 ⟨.tilted, 1, 1, false, 188387526434615877⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 12 := ⟨[
  .shared 117 51 48 ⟨.tilted, 1, 2, false, 196056350289265894⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, false, 203846868407264421⟩,
  .point 118 45 45,
  .point 118 46 46,
  .point 118 47 47,
  .shared 118 48 47 ⟨.tilted, 2, 1, false, 174809733814497130⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 12 := ⟨[
  .shared 118 49 48 ⟨.tilted, 2, 1, false, 182288542886542665⟩,
  .shared 118 50 48 ⟨.tilted, 1, 1, false, 189892894261340046⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, false, 197621344924113023⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, false, 205472451860085344⟩,
  .rectangle 119 44 119 44 47,
  .point 119 45 45], by decide +kernel⟩
private def batch21 : PaidBatch .empty 12 := ⟨[
  .point 119 46 47,
  .shared 119 47 47 ⟨.tilted, 2, 1, false, 168790169521439986⟩,
  .shared 119 48 47 ⟨.tilted, 2, 1, false, 176198734054527881⟩,
  .shared 119 49 48 ⟨.tilted, 2, 1, false, 183735245914994708⟩,
  .shared 119 50 48 ⟨.tilted, 1, 1, false, 191398262088064215⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, false, 199186339558960152⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 12 := ⟨[
  .shared 119 52 48 ⟨.tilted, 1, 2, false, 207098035312906267⟩,
  .rectangle 119 43 122 43 47,
  .rectangle 119 41 125 41 46,
  .rectangle 119 42 125 42 47,
  .point 120 44 45,
  .point 120 45 46], by decide +kernel⟩
private def batch23 : PaidBatch .empty 12 := ⟨[
  .point 120 46 47,
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 170122428982900279⟩,
  .shared 120 48 47 ⟨.tilted, 0, 1, false, 177587734294558632⟩,
  .shared 120 49 48 ⟨.tilted, 0, 1, false, 185181948943446751⟩,
  .shared 120 50 48 ⟨.tilted, 0, 1, false, 192903629914788384⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, false, 200751334193807281⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 12 := ⟨[
  .shared 120 52 48 ⟨.tilted, 1, 2, false, 208723618765727190⟩,
  .point 121 44 45,
  .point 121 45 46,
  .point 121 46 47,
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 171454688444360572⟩,
  .shared 121 48 47 ⟨.tilted, 0, 1, false, 178976734534589383⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 12 := ⟨[
  .shared 121 49 48 ⟨.tilted, 0, 1, false, 186628651971898794⟩,
  .shared 121 50 48 ⟨.tilted, 0, 2, false, 194408997741512553⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, false, 202316328828654410⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, false, 210349202218548113⟩,
  .point 122 44 45,
  .point 122 45 46], by decide +kernel⟩
private def batch26 : PaidBatch .empty 12 := ⟨[
  .shared 122 46 47 ⟨.tilted, 0, 1, false, 165340437408729280⟩,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 172786947905820865⟩,
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 180365734774620134⟩,
  .shared 122 49 48 ⟨.tilted, 0, 1, false, 188075355000350837⟩,
  .shared 122 50 48 ⟨.tilted, 0, 2, false, 195914365568236722⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, false, 203881323463501539⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 12 := ⟨[
  .shared 122 52 48 ⟨.tilted, 1, 2, false, 211974785671369036⟩,
  .point 123 43 44,
  .point 123 44 46,
  .point 123 45 47,
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 166616918101469949⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 174119207367281158⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 12 := ⟨[
  .shared 123 48 48 ⟨.tilted, 0, 1, false, 181754735014650885⟩,
  .shared 123 49 48 ⟨.tilted, 0, 1, false, 189522058028802880⟩,
  .shared 123 50 48 ⟨.tilted, 0, 2, false, 197419733394960891⟩,
  .shared 123 51 48 ⟨.tilted, 0, 2, false, 205446318098348668⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, false, 213600369124189959⟩,
  .point 124 43 45], by decide +kernel⟩
private def batch29 : PaidBatch .empty 12 := ⟨[
  .point 124 44 46,
  .point 124 45 47,
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 167893398794210618⟩,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 175451466828741451⟩,
  .shared 124 48 48 ⟨.tilted, 0, 1, false, 183143735254681636⟩,
  .shared 124 49 48 ⟨.tilted, 0, 1, false, 190968761057254923⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 12 := ⟨[
  .shared 124 50 48 ⟨.tilted, 0, 2, false, 198925101221685060⟩,
  .shared 124 51 48 ⟨.tilted, 0, 2, false, 207011312733195797⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, false, 215225952577010882⟩,
  .point 125 43 45,
  .point 125 44 46,
  .point 125 45 47], by decide +kernel⟩
private def batch31 : PaidBatch .empty 12 := ⟨[
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 169169879486951287⟩,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 176783726290201744⟩,
  .shared 125 48 48 ⟨.tilted, 0, 1, false, 184532735494712387⟩,
  .shared 125 49 48 ⟨.tilted, 0, 1, false, 192415464085706966⟩,
  .shared 125 50 48 ⟨.tilted, 0, 2, false, 200430469048409229⟩,
  .shared 125 51 48 ⟨.tilted, 0, 2, false, 208576307368042926⟩], by decide +kernel⟩
private def batch32 : PaidBatch .empty 12 := ⟨[
  .shared 125 52 48 ⟨.tilted, 0, 2, false, 216851536029831805⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 12) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 125 36 8 = true := by decide +kernel
private theorem index44 : checks tiles 125 44 8 = true := by decide +kernel
private theorem index52 : checks tiles 125 52 1 = true := by decide +kernel
private theorem covers : checks tiles 125 36 17 = true :=
  checks_join index36 (checks_join index44 index52)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 12 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

end Compact50PriceTableEmpty11
