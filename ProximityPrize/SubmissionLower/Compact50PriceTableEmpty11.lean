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
  .rectangle 11 33 68 42 39,
  .rectangle 15 43 70 52 45,
  .rectangle 69 33 97 37 46,
  .rectangle 69 38 97 42 46,
  .rectangle 71 48 84 52 48,
  .rectangle 71 43 98 47 48], by decide +kernel⟩
private def batch1 : PaidBatch .empty 11 := ⟨[
  .rectangle 85 51 91 52 48,
  .rectangle 85 48 98 50 48,
  .rectangle 92 51 98 51 48,
  .rectangle 92 52 98 52 48,
  .rectangle 98 38 111 40 47,
  .rectangle 98 41 111 42 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 11 := ⟨[
  .rectangle 98 33 125 35 46,
  .rectangle 98 36 125 37 47,
  .rectangle 99 51 100 51 48,
  .rectangle 99 52 100 52 49,
  .rectangle 99 50 102 50 48,
  .rectangle 99 43 105 45 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 11 := ⟨[
  .rectangle 99 46 105 47 48,
  .rectangle 99 48 105 48 48,
  .rectangle 99 49 105 49 48,
  .point 101 51 48,
  .rectangle 101 52 101 52 49,
  .point 102 51 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 11 := ⟨[
  .point 102 52 49,
  .rectangle 103 50 103 50 48,
  .point 103 51 48,
  .point 103 52 49,
  .point 104 50 48,
  .point 104 51 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 11 := ⟨[
  .point 104 52 49,
  .point 105 50 48,
  .point 105 51 49,
  .point 105 52 49,
  .point 106 49 48,
  .point 106 50 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 11 := ⟨[
  .point 106 51 49,
  .point 106 52 49,
  .rectangle 106 48 107 48 48,
  .rectangle 106 47 109 47 48,
  .rectangle 106 43 112 44 48,
  .rectangle 106 45 112 45 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 11 := ⟨[
  .rectangle 106 46 112 46 48,
  .point 107 49 48,
  .point 107 50 48,
  .point 107 51 49,
  .point 107 52 49,
  .rectangle 108 48 108 48 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 11 := ⟨[
  .point 108 49 48,
  .point 108 50 48,
  .point 108 51 49,
  .shared 108 52 49 ⟨.tilted, 1, 1, false, 186333293893674697⟩,
  .point 109 48 48,
  .point 109 49 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 11 := ⟨[
  .point 109 50 48,
  .point 109 51 49,
  .shared 109 52 49 ⟨.tilted, 1, 1, false, 187939334581907498⟩,
  .rectangle 110 47 110 47 48,
  .point 110 48 48,
  .point 110 49 48], by decide +kernel⟩
private def batch10 : PaidBatch .empty 11 := ⟨[
  .point 110 50 48,
  .point 110 51 49,
  .shared 110 52 49 ⟨.tilted, 1, 2, true, 195536729491468153⟩,
  .point 111 47 48,
  .point 111 48 48,
  .point 111 49 48], by decide +kernel⟩
private def batch11 : PaidBatch .empty 11 := ⟨[
  .point 111 50 49,
  .shared 111 51 49 ⟨.tilted, 1, 1, false, 183952561290737267⟩,
  .shared 111 52 49 ⟨.tilted, 1, 2, true, 196839036658583911⟩,
  .point 112 47 48,
  .point 112 48 48,
  .point 112 49 48], by decide +kernel⟩
private def batch12 : PaidBatch .empty 11 := ⟨[
  .point 112 50 49,
  .shared 112 51 49 ⟨.tilted, 1, 1, false, 185499159562136502⟩,
  .shared 112 52 49 ⟨.tilted, 1, 2, true, 198507923984388103⟩,
  .rectangle 112 41 118 42 48,
  .rectangle 112 38 125 39 47,
  .rectangle 112 40 125 40 47], by decide +kernel⟩
private def batch13 : PaidBatch .empty 11 := ⟨[
  .rectangle 113 46 113 46 48,
  .point 113 47 48,
  .point 113 48 48,
  .shared 113 49 48 ⟨.tilted, 1, 1, false, 172744201664890281⟩,
  .shared 113 50 49 ⟨.tilted, 1, 1, false, 179838845133211220⟩,
  .shared 113 51 49 ⟨.tilted, 1, 1, false, 187045757833535736⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 11 := ⟨[
  .shared 113 52 49 ⟨.tilted, 1, 2, true, 200176811310192295⟩,
  .rectangle 113 45 116 45 48,
  .rectangle 113 43 119 43 48,
  .rectangle 113 44 119 44 48,
  .point 114 46 48,
  .point 114 47 48], by decide +kernel⟩
private def batch15 : PaidBatch .empty 11 := ⟨[
  .point 114 48 48,
  .shared 114 49 48 ⟨.tilted, 1, 1, false, 174174799964672635⟩,
  .shared 114 50 49 ⟨.tilted, 1, 1, false, 181326962608460305⟩,
  .shared 114 51 49 ⟨.tilted, 1, 1, false, 188592356104934971⟩,
  .shared 114 52 49 ⟨.tilted, 1, 2, false, 195969538023071506⟩,
  .point 115 46 48], by decide +kernel⟩
private def batch16 : PaidBatch .empty 11 := ⟨[
  .point 115 47 48,
  .point 115 48 48,
  .shared 115 49 48 ⟨.tilted, 1, 1, false, 175605398264454990⟩,
  .shared 115 50 49 ⟨.tilted, 1, 1, false, 182815080083709391⟩,
  .shared 115 51 49 ⟨.tilted, 1, 2, true, 195475828399784615⟩,
  .shared 115 52 49 ⟨.tilted, 1, 2, false, 197575578711304307⟩], by decide +kernel⟩
private def batch17 : PaidBatch .empty 11 := ⟨[
  .point 116 46 48,
  .point 116 47 48,
  .shared 116 48 48 ⟨.tilted, 0, 1, false, 169885392094595172⟩,
  .shared 116 49 49 ⟨.tilted, 1, 1, false, 177035996564237344⟩,
  .shared 116 50 49 ⟨.tilted, 1, 1, false, 184303197558958476⟩,
  .shared 116 51 49 ⟨.tilted, 1, 2, true, 197078604292483328⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 11 := ⟨[
  .shared 116 52 49 ⟨.tilted, 1, 2, false, 199181619399537109⟩,
  .point 117 45 48,
  .point 117 46 48,
  .point 117 47 48,
  .shared 117 48 48 ⟨.tilted, 0, 1, false, 171259432839594213⟩,
  .shared 117 49 49 ⟨.tilted, 1, 1, false, 178466594864019699⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 11 := ⟨[
  .shared 117 50 49 ⟨.tilted, 1, 1, false, 185791315034207562⟩,
  .shared 117 51 49 ⟨.tilted, 1, 2, true, 198681380185182040⟩,
  .shared 117 52 49 ⟨.tilted, 1, 2, false, 200787660087769910⟩,
  .point 118 45 48,
  .point 118 46 48,
  .point 118 47 48], by decide +kernel⟩
private def batch20 : PaidBatch .empty 11 := ⟨[
  .shared 118 48 48 ⟨.tilted, 0, 1, false, 172633473584593255⟩,
  .shared 118 49 49 ⟨.tilted, 0, 1, false, 179897193163802053⟩,
  .shared 118 50 49 ⟨.tilted, 1, 1, false, 187279432509456647⟩,
  .shared 118 51 49 ⟨.tilted, 1, 2, false, 194778749190531909⟩,
  .shared 118 52 49 ⟨.tilted, 1, 2, false, 202393700776002712⟩,
  .point 119 45 48], by decide +kernel⟩
private def batch21 : PaidBatch .empty 11 := ⟨[
  .point 119 46 48,
  .shared 119 47 48 ⟨.tilted, 0, 1, false, 166808161013754524⟩,
  .shared 119 48 48 ⟨.tilted, 0, 1, false, 174007514329592296⟩,
  .shared 119 49 49 ⟨.tilted, 0, 1, false, 181327791463584408⟩,
  .shared 119 50 49 ⟨.tilted, 1, 1, false, 188767549984705733⟩,
  .shared 119 51 49 ⟨.tilted, 1, 2, false, 196325347461931143⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 11 := ⟨[
  .shared 119 52 49 ⟨.tilted, 1, 2, false, 203999741464235513⟩,
  .rectangle 119 41 125 41 48,
  .rectangle 119 42 125 42 48,
  .point 120 44 48,
  .point 120 45 48,
  .point 120 46 48], by decide +kernel⟩
private def batch23 : PaidBatch .empty 11 := ⟨[
  .shared 120 47 48 ⟨.tilted, 0, 1, false, 168126605824653671⟩,
  .shared 120 48 48 ⟨.tilted, 0, 1, false, 175381555074591338⟩,
  .shared 120 49 49 ⟨.tilted, 0, 1, false, 182758389763366762⟩,
  .shared 120 50 49 ⟨.tilted, 0, 1, false, 190255667459954818⟩,
  .shared 120 51 49 ⟨.tilted, 1, 2, false, 197871945733330378⟩,
  .shared 120 52 49 ⟨.tilted, 1, 2, false, 205605782152468315⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 11 := ⟨[
  .rectangle 120 43 122 43 48,
  .point 121 44 48,
  .point 121 45 48,
  .point 121 46 48,
  .shared 121 47 48 ⟨.tilted, 0, 1, false, 169445050635552817⟩,
  .shared 121 48 48 ⟨.tilted, 0, 1, false, 176755595819590379⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 11 := ⟨[
  .shared 121 49 49 ⟨.tilted, 0, 1, false, 184188988063149117⟩,
  .shared 121 50 49 ⟨.tilted, 0, 2, true, 196806865650811196⟩,
  .shared 121 51 49 ⟨.tilted, 1, 2, false, 199418544004729612⟩,
  .shared 121 52 49 ⟨.tilted, 1, 2, false, 207211822840701116⟩,
  .point 122 44 48,
  .point 122 45 48], by decide +kernel⟩
private def batch26 : PaidBatch .empty 11 := ⟨[
  .shared 122 46 48 ⟨.tilted, 0, 1, false, 163522605439544228⟩,
  .shared 122 47 48 ⟨.tilted, 0, 1, false, 170763495446451964⟩,
  .shared 122 48 49 ⟨.tilted, 0, 1, false, 178129636564589421⟩,
  .shared 122 49 49 ⟨.tilted, 0, 1, false, 185619586362931471⟩,
  .shared 122 50 49 ⟨.tilted, 0, 2, true, 198344865694686955⟩,
  .shared 122 51 49 ⟨.tilted, 1, 2, false, 200965142276128847⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 11 := ⟨[
  .shared 122 52 49 ⟨.tilted, 1, 2, false, 208817863528933918⟩,
  .point 123 43 48,
  .point 123 44 48,
  .point 123 45 48,
  .shared 123 46 48 ⟨.tilted, 0, 1, false, 164786415937026898⟩,
  .shared 123 47 48 ⟨.tilted, 0, 1, false, 172081940257351110⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 11 := ⟨[
  .shared 123 48 49 ⟨.tilted, 0, 1, false, 179503677309588462⟩,
  .shared 123 49 49 ⟨.tilted, 0, 1, false, 187050184662713826⟩,
  .shared 123 50 49 ⟨.tilted, 0, 2, true, 199882865738562713⟩,
  .shared 123 51 49 ⟨.tilted, 0, 2, false, 202511740547528081⟩,
  .shared 123 52 49 ⟨.tilted, 1, 2, false, 210423904217166719⟩,
  .point 124 43 48], by decide +kernel⟩
private def batch29 : PaidBatch .empty 11 := ⟨[
  .point 124 44 48,
  .point 124 45 48,
  .shared 124 46 48 ⟨.tilted, 0, 1, false, 166050226434509567⟩,
  .shared 124 47 48 ⟨.tilted, 0, 1, false, 173400385068250257⟩,
  .shared 124 48 49 ⟨.tilted, 0, 1, false, 180877718054587504⟩,
  .shared 124 49 49 ⟨.tilted, 0, 1, false, 188480782962496180⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 11 := ⟨[
  .shared 124 50 49 ⟨.tilted, 0, 2, false, 196651095333591669⟩,
  .shared 124 51 49 ⟨.tilted, 0, 2, false, 204058338818927316⟩,
  .shared 124 52 49 ⟨.tilted, 1, 2, false, 212029944905399521⟩,
  .point 125 43 48,
  .point 125 44 48,
  .shared 125 45 48 ⟨.tilted, 0, 1, false, 160038822389140172⟩], by decide +kernel⟩
private def batch31 : PaidBatch .empty 11 := ⟨[
  .shared 125 46 48 ⟨.tilted, 0, 1, false, 167314036931992237⟩,
  .shared 125 47 48 ⟨.tilted, 0, 1, false, 174718829879149403⟩,
  .shared 125 48 49 ⟨.tilted, 0, 1, false, 182251758799586545⟩,
  .shared 125 49 49 ⟨.tilted, 0, 1, false, 189911381262278535⟩,
  .shared 125 50 49 ⟨.tilted, 0, 2, false, 197696254836200246⟩,
  .shared 125 51 49 ⟨.tilted, 0, 2, false, 205604937090326550⟩], by decide +kernel⟩
def batch32 : PaidBatch .empty 11 := ⟨[
  .shared 125 52 49 ⟨.tilted, 0, 2, false, 213635985593632322⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 11) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 125 33 8 = true := by decide +kernel
theorem index41 : checks tiles 125 41 8 = true := by decide +kernel
theorem index49 : checks tiles 125 49 4 = true := by decide +kernel
private theorem covers : checks tiles 125 33 20 = true :=
  checks_join index33 (checks_join index41 index49)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 11 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12

private def batch0 : PaidBatch .empty 12 := ⟨[
  .rectangle 12 36 68 44 39,
  .rectangle 15 45 68 52 45,
  .rectangle 69 49 83 52 48,
  .rectangle 69 36 97 40 46,
  .rectangle 69 41 97 44 46,
  .rectangle 69 45 97 48 48], by decide +kernel⟩
private def batch1 : PaidBatch .empty 12 := ⟨[
  .rectangle 84 51 90 52 48,
  .rectangle 84 49 97 50 48,
  .rectangle 91 51 97 51 48,
  .rectangle 91 52 97 52 48,
  .rectangle 98 51 99 51 48,
  .rectangle 98 52 99 52 49], by decide +kernel⟩
private def batch2 : PaidBatch .empty 12 := ⟨[
  .rectangle 98 50 101 50 48,
  .rectangle 98 45 104 46 48,
  .rectangle 98 47 104 48 48,
  .rectangle 98 49 104 49 48,
  .rectangle 98 41 111 42 47,
  .rectangle 98 43 111 44 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 12 := ⟨[
  .rectangle 98 36 125 38 47,
  .rectangle 98 39 125 40 47,
  .rectangle 100 51 100 51 48,
  .rectangle 100 52 100 52 49,
  .point 101 51 48,
  .point 101 52 49], by decide +kernel⟩
private def batch4 : PaidBatch .empty 12 := ⟨[
  .point 102 51 48,
  .point 102 52 49,
  .rectangle 102 50 103 50 48,
  .point 103 51 48,
  .point 103 52 49,
  .point 104 50 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 12 := ⟨[
  .point 104 51 48,
  .point 104 52 49,
  .rectangle 105 49 105 49 48,
  .point 105 50 48,
  .point 105 51 49,
  .point 105 52 49], by decide +kernel⟩
private def batch6 : PaidBatch .empty 12 := ⟨[
  .rectangle 105 47 108 47 48,
  .rectangle 105 48 108 48 48,
  .rectangle 105 45 111 45 48,
  .rectangle 105 46 111 46 48,
  .point 106 49 48,
  .point 106 50 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 12 := ⟨[
  .point 106 51 49,
  .point 106 52 49,
  .point 107 49 48,
  .point 107 50 48,
  .point 107 51 49,
  .point 107 52 49], by decide +kernel⟩
private def batch8 : PaidBatch .empty 12 := ⟨[
  .point 108 49 48,
  .point 108 50 48,
  .point 108 51 49,
  .shared 108 52 49 ⟨.tilted, 1, 1, false, 189140072453187006⟩,
  .point 109 48 48,
  .point 109 49 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 12 := ⟨[
  .point 109 50 48,
  .point 109 51 49,
  .shared 109 52 49 ⟨.tilted, 1, 1, false, 190764998299438223⟩,
  .rectangle 109 47 110 47 48,
  .point 110 48 48,
  .point 110 49 48], by decide +kernel⟩
private def batch10 : PaidBatch .empty 12 := ⟨[
  .point 110 50 48,
  .point 110 51 49,
  .shared 110 52 49 ⟨.tilted, 1, 2, true, 199748670942022860⟩,
  .point 111 47 48,
  .point 111 48 48,
  .point 111 49 48], by decide +kernel⟩
private def batch11 : PaidBatch .empty 12 := ⟨[
  .point 111 50 49,
  .shared 111 51 49 ⟨.tilted, 1, 1, false, 186590869262730258⟩,
  .shared 111 52 49 ⟨.tilted, 1, 2, false, 196539125337011982⟩,
  .point 112 47 48,
  .point 112 48 48,
  .point 112 49 48], by decide +kernel⟩
private def batch12 : PaidBatch .empty 12 := ⟨[
  .point 112 50 49,
  .shared 112 51 49 ⟨.tilted, 1, 1, false, 188155230801350587⟩,
  .shared 112 52 49 ⟨.tilted, 1, 2, false, 195639775838191874⟩,
  .rectangle 112 46 113 46 48,
  .rectangle 112 45 115 45 48,
  .rectangle 112 41 118 42 48], by decide +kernel⟩
private def batch13 : PaidBatch .empty 12 := ⟨[
  .rectangle 112 43 118 43 48,
  .rectangle 112 44 118 44 48,
  .point 113 47 48,
  .point 113 48 48,
  .shared 113 49 48 ⟨.tilted, 2, 1, false, 174984211734851386⟩,
  .shared 113 50 49 ⟨.tilted, 1, 1, false, 182292281546431971⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 12 := ⟨[
  .shared 113 51 49 ⟨.tilted, 1, 1, false, 189719592339970916⟩,
  .shared 113 52 49 ⟨.tilted, 1, 2, false, 197264701684443091⟩,
  .point 114 46 48,
  .point 114 47 48,
  .point 114 48 48,
  .shared 114 49 48 ⟨.tilted, 2, 1, false, 176430329520260193⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 12 := ⟨[
  .shared 114 50 49 ⟨.tilted, 1, 1, false, 183797040398104830⟩,
  .shared 114 51 49 ⟨.tilted, 1, 1, false, 191283953878591245⟩,
  .shared 114 52 49 ⟨.tilted, 1, 2, false, 198889627530694308⟩,
  .point 115 46 48,
  .point 115 47 48,
  .point 115 48 48], by decide +kernel⟩
private def batch16 : PaidBatch .empty 12 := ⟨[
  .shared 115 49 48 ⟨.tilted, 2, 1, false, 177876447305669000⟩,
  .shared 115 50 49 ⟨.tilted, 1, 1, false, 185301799249777689⟩,
  .shared 115 51 49 ⟨.tilted, 1, 2, true, 196516886231697198⟩,
  .shared 115 52 49 ⟨.tilted, 1, 2, false, 200514553376945525⟩,
  .rectangle 116 45 116 45 48,
  .point 116 46 48], by decide +kernel⟩
private def batch17 : PaidBatch .empty 12 := ⟨[
  .point 116 47 48,
  .shared 116 48 48 ⟨.tilted, 2, 1, false, 171962140355738804⟩,
  .shared 116 49 49 ⟨.tilted, 2, 1, false, 179322565091077807⟩,
  .shared 116 50 49 ⟨.tilted, 1, 1, false, 186806558101450548⟩,
  .shared 116 51 49 ⟨.tilted, 1, 2, false, 194412676955831903⟩,
  .shared 116 52 49 ⟨.tilted, 1, 2, false, 202139479223196742⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 12 := ⟨[
  .point 117 45 48,
  .point 117 46 48,
  .point 117 47 48,
  .shared 117 48 48 ⟨.tilted, 2, 1, false, 173350578695566977⟩,
  .shared 117 49 49 ⟨.tilted, 2, 1, false, 180768682876486614⟩,
  .shared 117 50 49 ⟨.tilted, 1, 1, false, 188311316953123407⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 12 := ⟨[
  .shared 117 51 49 ⟨.tilted, 1, 2, false, 195977038494452232⟩,
  .shared 117 52 49 ⟨.tilted, 1, 2, false, 203764405069447959⟩,
  .point 118 45 48,
  .point 118 46 48,
  .point 118 47 48,
  .shared 118 48 48 ⟨.tilted, 2, 1, false, 174739017035395150⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 12 := ⟨[
  .shared 118 49 49 ⟨.tilted, 2, 1, false, 182214800661895421⟩,
  .shared 118 50 49 ⟨.tilted, 1, 1, false, 189816075804796266⟩,
  .shared 118 51 49 ⟨.tilted, 1, 2, false, 197541400033072561⟩,
  .shared 118 52 49 ⟨.tilted, 1, 2, false, 205389330915699176⟩,
  .rectangle 119 44 119 44 48,
  .point 119 45 48], by decide +kernel⟩
private def batch21 : PaidBatch .empty 12 := ⟨[
  .point 119 46 48,
  .shared 119 47 48 ⟨.tilted, 2, 1, false, 168721887871251540⟩,
  .shared 119 48 48 ⟨.tilted, 2, 1, false, 176127455375223323⟩,
  .shared 119 49 49 ⟨.tilted, 2, 1, false, 183660918447304228⟩,
  .shared 119 50 49 ⟨.tilted, 1, 1, false, 191320834656469125⟩,
  .shared 119 51 49 ⟨.tilted, 1, 2, false, 199105761571692890⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 12 := ⟨[
  .shared 119 52 49 ⟨.tilted, 1, 2, false, 207014256761950393⟩,
  .rectangle 119 43 122 43 48,
  .rectangle 119 41 125 41 48,
  .rectangle 119 42 125 42 48,
  .point 120 44 48,
  .point 120 45 48], by decide +kernel⟩
private def batch23 : PaidBatch .empty 12 := ⟨[
  .point 120 46 48,
  .shared 120 47 48 ⟨.tilted, 0, 1, false, 170053608386182497⟩,
  .shared 120 48 48 ⟨.tilted, 0, 1, false, 177515893715051496⟩,
  .shared 120 49 49 ⟨.tilted, 0, 1, false, 185107036232713035⟩,
  .shared 120 50 49 ⟨.tilted, 0, 1, false, 192825593508141984⟩,
  .shared 120 51 49 ⟨.tilted, 1, 2, false, 200670123110313219⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 12 := ⟨[
  .shared 120 52 49 ⟨.tilted, 1, 2, false, 208639182608201610⟩,
  .point 121 44 48,
  .point 121 45 48,
  .point 121 46 48,
  .shared 121 47 48 ⟨.tilted, 0, 1, false, 171385328901113454⟩,
  .shared 121 48 48 ⟨.tilted, 0, 1, false, 178904332054879669⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 12 := ⟨[
  .shared 121 49 49 ⟨.tilted, 0, 1, false, 186553154018121842⟩,
  .shared 121 50 49 ⟨.tilted, 0, 2, false, 194330352359814843⟩,
  .shared 121 51 49 ⟨.tilted, 1, 2, false, 202234484648933548⟩,
  .shared 121 52 49 ⟨.tilted, 1, 2, false, 210264108454452827⟩,
  .point 122 44 48,
  .point 122 45 48], by decide +kernel⟩
private def batch26 : PaidBatch .empty 12 := ⟨[
  .shared 122 46 48 ⟨.tilted, 0, 1, false, 165273551298565480⟩,
  .shared 122 47 48 ⟨.tilted, 0, 1, false, 172717049416044411⟩,
  .shared 122 48 49 ⟨.tilted, 0, 1, false, 180292770394707842⟩,
  .shared 122 49 49 ⟨.tilted, 0, 1, false, 187999271803530649⟩,
  .shared 122 50 49 ⟨.tilted, 0, 2, false, 195835111211487702⟩,
  .shared 122 51 49 ⟨.tilted, 1, 2, false, 203798846187553877⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 12 := ⟨[
  .shared 122 52 49 ⟨.tilted, 1, 2, false, 211889034300704044⟩,
  .point 123 43 48,
  .point 123 44 48,
  .point 123 45 48,
  .shared 123 46 48 ⟨.tilted, 0, 1, false, 166549515609282639⟩,
  .shared 123 47 48 ⟨.tilted, 0, 1, false, 174048769930975368⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 12 := ⟨[
  .shared 123 48 49 ⟨.tilted, 0, 1, false, 181681208734536015⟩,
  .shared 123 49 49 ⟨.tilted, 0, 1, false, 189445389588939456⟩,
  .shared 123 50 49 ⟨.tilted, 0, 2, false, 197339870063160561⟩,
  .shared 123 51 49 ⟨.tilted, 0, 2, false, 205363207726174206⟩,
  .shared 123 52 49 ⟨.tilted, 1, 2, false, 213513960146955261⟩,
  .point 124 43 48], by decide +kernel⟩
private def batch29 : PaidBatch .empty 12 := ⟨[
  .point 124 44 48,
  .point 124 45 48,
  .shared 124 46 48 ⟨.tilted, 0, 1, false, 167825479919999798⟩,
  .shared 124 47 48 ⟨.tilted, 0, 1, false, 175380490445906325⟩,
  .shared 124 48 49 ⟨.tilted, 0, 1, false, 183069647074364188⟩,
  .shared 124 49 49 ⟨.tilted, 0, 1, false, 190891507374348263⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 12 := ⟨[
  .shared 124 50 49 ⟨.tilted, 0, 2, false, 198844628914833420⟩,
  .shared 124 51 49 ⟨.tilted, 0, 2, false, 206927569264794535⟩,
  .shared 124 52 49 ⟨.tilted, 1, 2, false, 215138885993206478⟩,
  .point 125 43 48,
  .point 125 44 48,
  .point 125 45 48], by decide +kernel⟩
private def batch31 : PaidBatch .empty 12 := ⟨[
  .shared 125 46 48 ⟨.tilted, 0, 1, false, 169101444230716957⟩,
  .shared 125 47 48 ⟨.tilted, 0, 1, false, 176712210960837282⟩,
  .shared 125 48 49 ⟨.tilted, 0, 1, false, 184458085414192361⟩,
  .shared 125 49 49 ⟨.tilted, 0, 1, false, 192337625159757070⟩,
  .shared 125 50 49 ⟨.tilted, 0, 2, false, 200349387766506279⟩,
  .shared 125 51 49 ⟨.tilted, 0, 2, false, 208491930803414864⟩], by decide +kernel⟩
def batch32 : PaidBatch .empty 12 := ⟨[
  .shared 125 52 49 ⟨.tilted, 0, 2, false, 216763811839457695⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 12) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 125 36 8 = true := by decide +kernel
theorem index44 : checks tiles 125 44 8 = true := by decide +kernel
theorem index52 : checks tiles 125 52 1 = true := by decide +kernel
private theorem covers : checks tiles 125 36 17 = true :=
  checks_join index36 (checks_join index44 index52)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 12 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

end Compact50PriceTableEmpty11
