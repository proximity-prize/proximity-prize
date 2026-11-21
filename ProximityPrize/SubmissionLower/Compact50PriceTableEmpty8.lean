import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableEmpty8
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top8

private def batch0 : PaidBatch .empty 8 := ⟨[
  .rectangle 8 24 66 38 37,
  .rectangle 13 39 69 52 44,
  .rectangle 67 32 96 38 39,
  .rectangle 67 24 125 27 33,
  .rectangle 67 28 125 31 38,
  .rectangle 70 50 83 52 41], by decide +kernel⟩
private def batch1 : PaidBatch .empty 8 := ⟨[
  .rectangle 70 39 97 42 40,
  .rectangle 70 43 97 45 42,
  .rectangle 70 46 97 49 46,
  .rectangle 84 50 90 52 44,
  .rectangle 91 50 97 51 46,
  .rectangle 91 52 97 52 46], by decide +kernel⟩
private def batch2 : PaidBatch .empty 8 := ⟨[
  .rectangle 97 32 125 35 43,
  .rectangle 97 36 125 38 45,
  .rectangle 98 51 101 51 47,
  .rectangle 98 52 101 52 48,
  .rectangle 98 43 104 45 44,
  .rectangle 98 46 104 47 45], by decide +kernel⟩
private def batch3 : PaidBatch .empty 8 := ⟨[
  .rectangle 98 48 104 49 47,
  .rectangle 98 50 104 50 47,
  .rectangle 98 39 111 42 45,
  .rectangle 102 51 102 51 47,
  .rectangle 102 52 103 52 48,
  .point 103 51 45], by decide +kernel⟩
private def batch4 : PaidBatch .empty 8 := ⟨[
  .point 104 51 45,
  .point 104 52 46,
  .point 105 50 45,
  .rectangle 105 51 105 51 48,
  .point 105 52 46,
  .rectangle 105 49 106 49 47], by decide +kernel⟩
private def batch5 : PaidBatch .empty 8 := ⟨[
  .rectangle 105 48 108 48 47,
  .rectangle 105 43 111 45 47,
  .rectangle 105 46 111 46 46,
  .rectangle 105 47 111 47 47,
  .point 106 50 45,
  .point 106 51 46], by decide +kernel⟩
private def batch6 : PaidBatch .empty 8 := ⟨[
  .point 106 52 47,
  .rectangle 107 49 107 49 47,
  .point 107 50 45,
  .point 107 51 46,
  .point 107 52 47,
  .point 108 49 45], by decide +kernel⟩
private def batch7 : PaidBatch .empty 8 := ⟨[
  .point 108 50 46,
  .point 108 51 47,
  .point 108 52 48,
  .rectangle 109 48 109 48 47,
  .point 109 49 45,
  .point 109 50 46], by decide +kernel⟩
private def batch8 : PaidBatch .empty 8 := ⟨[
  .point 109 51 47,
  .point 109 52 48,
  .point 110 48 45,
  .point 110 49 46,
  .point 110 50 47,
  .point 110 51 47], by decide +kernel⟩
private def batch9 : PaidBatch .empty 8 := ⟨[
  .point 110 52 48,
  .point 111 48 45,
  .point 111 49 46,
  .point 111 50 47,
  .point 111 51 48,
  .shared 111 52 48 ⟨.tilted, 1, 2, true, 190356411348748949⟩], by decide +kernel⟩
private def batch10 : PaidBatch .empty 8 := ⟨[
  .point 112 47 44,
  .point 112 48 45,
  .point 112 49 46,
  .point 112 50 47,
  .point 112 51 48,
  .shared 112 52 48 ⟨.tilted, 1, 2, true, 192025974072315790⟩], by decide +kernel⟩
private def batch11 : PaidBatch .empty 8 := ⟨[
  .rectangle 112 46 113 46 47,
  .rectangle 112 45 115 45 47,
  .rectangle 112 41 118 42 46,
  .rectangle 112 43 118 43 46,
  .rectangle 112 44 118 44 47,
  .rectangle 112 39 125 40 46], by decide +kernel⟩
private def batch12 : PaidBatch .empty 8 := ⟨[
  .point 113 47 45,
  .point 113 48 46,
  .point 113 49 47,
  .point 113 50 48,
  .shared 113 51 48 ⟨.tilted, 1, 1, false, 174472003776675253⟩,
  .shared 113 52 48 ⟨.tilted, 1, 2, true, 193695536795882632⟩], by decide +kernel⟩
private def batch13 : PaidBatch .empty 8 := ⟨[
  .rectangle 114 46 114 46 47,
  .point 114 47 45,
  .point 114 48 46,
  .point 114 49 47,
  .point 114 50 48,
  .shared 114 51 48 ⟨.tilted, 1, 2, true, 187944253021154493⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 8 := ⟨[
  .shared 114 52 48 ⟨.tilted, 1, 2, true, 195365099519449474⟩,
  .point 115 46 45,
  .point 115 47 46,
  .point 115 48 47,
  .shared 115 49 47 ⟨.tilted, 1, 1, false, 164460008012463947⟩,
  .shared 115 50 48 ⟨.tilted, 1, 1, false, 170893059012145447⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 8 := ⟨[
  .shared 115 51 48 ⟨.tilted, 1, 2, true, 189547677556353755⟩,
  .shared 115 52 48 ⟨.tilted, 1, 2, true, 197034662243016315⟩,
  .rectangle 116 45 116 45 47,
  .point 116 46 45,
  .point 116 47 46,
  .point 116 48 47], by decide +kernel⟩
private def batch16 : PaidBatch .empty 8 := ⟨[
  .point 116 49 48,
  .shared 116 50 48 ⟨.tilted, 1, 1, false, 172311632187276680⟩,
  .shared 116 51 48 ⟨.tilted, 1, 2, true, 191151102091553018⟩,
  .shared 116 52 48 ⟨.tilted, 1, 2, true, 198704224966583157⟩,
  .point 117 45 44,
  .point 117 46 45], by decide +kernel⟩
private def batch17 : PaidBatch .empty 8 := ⟨[
  .point 117 47 46,
  .point 117 48 47,
  .point 117 49 48,
  .shared 117 50 48 ⟨.tilted, 1, 1, false, 173730205362407913⟩,
  .shared 117 51 48 ⟨.tilted, 1, 2, true, 192754526626752280⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 200373787690149999⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 8 := ⟨[
  .point 118 45 45,
  .point 118 46 46,
  .point 118 47 47,
  .shared 118 48 47 ⟨.tilted, 0, 1, false, 162055268041444402⟩,
  .shared 118 49 48 ⟨.tilted, 0, 1, false, 168553201280952944⟩,
  .shared 118 50 48 ⟨.tilted, 1, 1, false, 175148778537539146⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 8 := ⟨[
  .shared 118 51 48 ⟨.tilted, 1, 2, true, 194357951161951543⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, true, 202043350413716840⟩,
  .rectangle 119 44 119 44 47,
  .point 119 45 45,
  .point 119 46 46,
  .point 119 47 47], by decide +kernel⟩
private def batch20 : PaidBatch .empty 8 := ⟨[
  .shared 119 48 47 ⟨.tilted, 0, 1, false, 163366452388490001⟩,
  .shared 119 49 48 ⟨.tilted, 0, 1, false, 169917599037115943⟩,
  .shared 119 50 48 ⟨.tilted, 1, 1, false, 176567351712670379⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 195961375697150805⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, true, 203712913137283682⟩,
  .rectangle 119 43 122 43 47], by decide +kernel⟩
private def batch21 : PaidBatch .empty 8 := ⟨[
  .rectangle 119 41 125 41 46,
  .rectangle 119 42 125 42 47,
  .point 120 44 44,
  .point 120 45 45,
  .point 120 46 46,
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 158174287729347838⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 8 := ⟨[
  .shared 120 48 47 ⟨.tilted, 0, 1, false, 164677636735535600⟩,
  .shared 120 49 48 ⟨.tilted, 0, 1, false, 171281996793278942⟩,
  .shared 120 50 48 ⟨.tilted, 0, 1, false, 177985924887801612⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 197564800232350068⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, true, 205382475860850524⟩,
  .point 121 44 45], by decide +kernel⟩
private def batch23 : PaidBatch .empty 8 := ⟨[
  .point 121 45 46,
  .point 121 46 47,
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 159433220677126871⟩,
  .shared 121 48 47 ⟨.tilted, 0, 1, false, 165988821082581199⟩,
  .shared 121 49 48 ⟨.tilted, 0, 1, false, 172646394549441941⟩,
  .shared 121 50 48 ⟨.tilted, 0, 2, true, 191409427712260379⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 8 := ⟨[
  .shared 121 51 48 ⟨.tilted, 1, 2, true, 199168224767549330⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, true, 207052038584417365⟩,
  .point 122 44 45,
  .point 122 45 46,
  .point 122 46 47,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 160692153624905904⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 8 := ⟨[
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 167300005429626798⟩,
  .shared 122 49 48 ⟨.tilted, 0, 1, false, 174010792305604940⟩,
  .shared 122 50 48 ⟨.tilted, 0, 2, true, 192948050183884887⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, true, 200771649302748593⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, true, 208721601307984207⟩,
  .point 123 43 44], by decide +kernel⟩
private def batch26 : PaidBatch .empty 8 := ⟨[
  .point 123 44 45,
  .point 123 45 46,
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 155396323464581809⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 161951086572684937⟩,
  .shared 123 48 48 ⟨.tilted, 0, 1, false, 168611189776672397⟩,
  .shared 123 49 48 ⟨.tilted, 0, 1, false, 175375190061767939⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 8 := ⟨[
  .shared 123 50 48 ⟨.tilted, 0, 2, true, 194486672655509395⟩,
  .shared 123 51 48 ⟨.tilted, 0, 2, true, 202375073837947855⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, true, 210391164031551049⟩,
  .point 124 43 45,
  .point 124 44 46,
  .point 124 45 47], by decide +kernel⟩
private def batch28 : PaidBatch .empty 8 := ⟨[
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 156603967022945110⟩,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 163210019520463970⟩,
  .shared 124 48 48 ⟨.tilted, 0, 1, false, 169922374123717996⟩,
  .shared 124 49 48 ⟨.tilted, 0, 1, false, 176739587817930938⟩,
  .shared 124 50 48 ⟨.tilted, 0, 2, true, 196025295127133904⟩,
  .shared 124 51 48 ⟨.tilted, 0, 2, true, 203978498373147118⟩], by decide +kernel⟩
private def batch29 : PaidBatch .empty 8 := ⟨[
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 212060726755117890⟩,
  .point 125 43 45,
  .point 125 44 46,
  .point 125 45 47,
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 157811610581308411⟩,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 164468952468243003⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 8 := ⟨[
  .shared 125 48 48 ⟨.tilted, 0, 1, false, 171233558470763595⟩,
  .shared 125 49 48 ⟨.tilted, 0, 1, false, 178103985574093937⟩,
  .shared 125 50 48 ⟨.tilted, 0, 2, true, 197563917598758412⟩,
  .shared 125 51 48 ⟨.tilted, 0, 2, true, 205581922908346380⟩,
  .shared 125 52 48 ⟨.tilted, 0, 2, true, 213730289478684732⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 8) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 125 24 8 = true := by decide +kernel
private theorem index32 : checks tiles 125 32 8 = true := by decide +kernel
private theorem index40 : checks tiles 125 40 8 = true := by decide +kernel
private theorem index48 : checks tiles 125 48 5 = true := by decide +kernel
private theorem covers : checks tiles 125 24 29 = true :=
  checks_join index24 (checks_join index32 (checks_join index40 index48))

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 8 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9

private def batch0 : PaidBatch .empty 9 := ⟨[
  .rectangle 9 27 67 39 35,
  .rectangle 14 40 69 52 44,
  .rectangle 68 34 96 39 39,
  .rectangle 68 27 125 30 37,
  .rectangle 68 31 125 33 39,
  .rectangle 70 47 83 52 44], by decide +kernel⟩
private def batch1 : PaidBatch .empty 9 := ⟨[
  .rectangle 70 40 97 43 41,
  .rectangle 70 44 97 46 43,
  .rectangle 84 50 90 52 45,
  .rectangle 84 47 97 49 45,
  .rectangle 91 50 97 51 46,
  .rectangle 91 52 97 52 46], by decide +kernel⟩
private def batch2 : PaidBatch .empty 9 := ⟨[
  .rectangle 97 34 125 36 43,
  .rectangle 97 37 125 39 46,
  .rectangle 98 51 101 51 47,
  .rectangle 98 52 101 52 48,
  .rectangle 98 44 104 46 46,
  .rectangle 98 47 104 48 47], by decide +kernel⟩
private def batch3 : PaidBatch .empty 9 := ⟨[
  .rectangle 98 49 104 49 47,
  .rectangle 98 50 104 50 47,
  .rectangle 98 40 111 41 42,
  .rectangle 98 42 111 43 44,
  .point 102 51 45,
  .rectangle 102 52 102 52 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 9 := ⟨[
  .point 103 51 45,
  .point 103 52 46,
  .point 104 51 45,
  .point 104 52 46,
  .point 105 50 45,
  .point 105 51 46], by decide +kernel⟩
private def batch5 : PaidBatch .empty 9 := ⟨[
  .point 105 52 47,
  .rectangle 105 49 106 49 47,
  .rectangle 105 48 108 48 47,
  .rectangle 105 44 111 45 46,
  .rectangle 105 46 111 46 46,
  .rectangle 105 47 111 47 47], by decide +kernel⟩
private def batch6 : PaidBatch .empty 9 := ⟨[
  .point 106 50 45,
  .point 106 51 46,
  .point 106 52 47,
  .point 107 49 45,
  .point 107 50 46,
  .point 107 51 47], by decide +kernel⟩
private def batch7 : PaidBatch .empty 9 := ⟨[
  .point 107 52 48,
  .point 108 49 45,
  .point 108 50 46,
  .point 108 51 47,
  .point 108 52 48,
  .point 109 48 45], by decide +kernel⟩
private def batch8 : PaidBatch .empty 9 := ⟨[
  .point 109 49 46,
  .point 109 50 47,
  .point 109 51 47,
  .point 109 52 48,
  .point 110 48 45,
  .point 110 49 46], by decide +kernel⟩
private def batch9 : PaidBatch .empty 9 := ⟨[
  .point 110 50 47,
  .point 110 51 48,
  .shared 110 52 48 ⟨.tilted, 1, 2, true, 191454155354328608⟩,
  .point 111 48 45,
  .point 111 49 46,
  .point 111 50 47], by decide +kernel⟩
private def batch10 : PaidBatch .empty 9 := ⟨[
  .point 111 51 48,
  .shared 111 52 48 ⟨.tilted, 1, 2, true, 193123718077895450⟩,
  .point 112 47 45,
  .point 112 48 46,
  .point 112 49 47,
  .point 112 50 48], by decide +kernel⟩
private def batch11 : PaidBatch .empty 9 := ⟨[
  .shared 112 51 48 ⟨.tilted, 1, 1, false, 178027194205510459⟩,
  .shared 112 52 48 ⟨.tilted, 1, 2, true, 194793280801462291⟩,
  .rectangle 112 46 113 46 47,
  .rectangle 112 45 115 45 47,
  .rectangle 112 40 118 41 45,
  .rectangle 112 42 118 43 47], by decide +kernel⟩
private def batch12 : PaidBatch .empty 9 := ⟨[
  .rectangle 112 44 118 44 47,
  .point 113 47 45,
  .point 113 48 46,
  .point 113 49 47,
  .point 113 50 48,
  .shared 113 51 48 ⟨.tilted, 1, 1, false, 179528776368901846⟩], by decide +kernel⟩
private def batch13 : PaidBatch .empty 9 := ⟨[
  .shared 113 52 48 ⟨.tilted, 1, 2, true, 196462843525029133⟩,
  .point 114 46 44,
  .point 114 47 46,
  .point 114 48 47,
  .shared 114 49 47 ⟨.tilted, 1, 1, false, 167611733358807437⟩,
  .shared 114 50 48 ⟨.tilted, 1, 1, false, 174271382178392025⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 9 := ⟨[
  .shared 114 51 48 ⟨.tilted, 1, 2, true, 196068155645420100⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, true, 198132406248595975⟩,
  .point 115 46 45,
  .point 115 47 46,
  .point 115 48 47,
  .shared 115 49 47 ⟨.tilted, 1, 1, false, 169001757984759575⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 9 := ⟨[
  .shared 115 50 48 ⟨.tilted, 1, 1, false, 175716704568138370⟩,
  .shared 115 51 48 ⟨.tilted, 1, 2, true, 192105123645624963⟩,
  .shared 115 52 48 ⟨.tilted, 1, 2, true, 199801968972162816⟩,
  .rectangle 116 45 116 45 47,
  .point 116 46 45,
  .point 116 47 46], by decide +kernel⟩
private def batch16 : PaidBatch .empty 9 := ⟨[
  .point 116 48 47,
  .point 116 49 48,
  .shared 116 50 48 ⟨.tilted, 1, 1, false, 177162026957884716⟩,
  .shared 116 51 48 ⟨.tilted, 1, 2, true, 193708548180824225⟩,
  .shared 116 52 48 ⟨.tilted, 1, 2, true, 201471531695729658⟩,
  .point 117 45 45], by decide +kernel⟩
private def batch17 : PaidBatch .empty 9 := ⟨[
  .point 117 46 46,
  .point 117 47 47,
  .shared 117 48 47 ⟨.tilted, 0, 1, false, 165059921704342017⟩,
  .shared 117 49 48 ⟨.tilted, 1, 1, false, 171781807236663852⟩,
  .shared 117 50 48 ⟨.tilted, 1, 1, false, 178607349347631061⟩,
  .shared 117 51 48 ⟨.tilted, 1, 2, true, 195311972716023488⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 9 := ⟨[
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 203141094419296500⟩,
  .point 118 45 45,
  .point 118 46 46,
  .point 118 47 47,
  .shared 118 48 47 ⟨.tilted, 0, 1, false, 166395610576350782⟩,
  .shared 118 49 48 ⟨.tilted, 0, 1, false, 173171831862615991⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 9 := ⟨[
  .shared 118 50 48 ⟨.tilted, 1, 1, false, 180052671737377407⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, true, 196915397251222750⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, true, 204810657142863341⟩,
  .rectangle 119 44 119 44 47,
  .point 119 45 45,
  .point 119 46 46], by decide +kernel⟩
private def batch20 : PaidBatch .empty 9 := ⟨[
  .point 119 47 47,
  .shared 119 48 47 ⟨.tilted, 0, 1, false, 167731299448359548⟩,
  .shared 119 49 48 ⟨.tilted, 0, 1, false, 174561856488568129⟩,
  .shared 119 50 48 ⟨.tilted, 1, 1, false, 181497994127123752⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 198518821786422013⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, true, 206480219866430183⟩], by decide +kernel⟩
private def batch21 : PaidBatch .empty 9 := ⟨[
  .rectangle 119 43 122 43 47,
  .rectangle 119 40 125 41 47,
  .rectangle 119 42 125 42 47,
  .point 120 44 45,
  .point 120 45 46,
  .point 120 46 47], by decide +kernel⟩
private def batch22 : PaidBatch .empty 9 := ⟨[
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 162290081149190484⟩,
  .shared 120 48 47 ⟨.tilted, 0, 1, false, 169066988320368313⟩,
  .shared 120 49 48 ⟨.tilted, 0, 1, false, 175951881114520268⟩,
  .shared 120 50 48 ⟨.tilted, 0, 1, false, 182943316516870098⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 200122246321621275⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, true, 208149782589997025⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 9 := ⟨[
  .point 121 44 45,
  .point 121 45 46,
  .point 121 46 47,
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 163572396277106711⟩,
  .shared 121 48 47 ⟨.tilted, 0, 1, false, 170402677192377079⟩,
  .shared 121 49 48 ⟨.tilted, 0, 1, false, 177341905740472406⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 9 := ⟨[
  .shared 121 50 48 ⟨.tilted, 0, 2, true, 193765297135371808⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, true, 201725670856820538⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, true, 209819345313563866⟩,
  .point 122 44 45,
  .point 122 45 46,
  .point 122 46 47], by decide +kernel⟩
private def batch25 : PaidBatch .empty 9 := ⟨[
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 164854711405022937⟩,
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 171738366064385844⟩,
  .shared 122 49 48 ⟨.tilted, 0, 1, false, 178731930366424545⟩,
  .shared 122 50 48 ⟨.tilted, 0, 2, true, 195303919606996316⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, true, 203329095392019800⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, true, 211488908037130708⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 9 := ⟨[
  .point 123 43 44,
  .point 123 44 46,
  .point 123 45 47,
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 159312312796786597⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 166137026532939164⟩,
  .shared 123 48 48 ⟨.tilted, 0, 1, false, 173074054936394610⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 9 := ⟨[
  .shared 123 49 48 ⟨.tilted, 0, 1, false, 180121954992376683⟩,
  .shared 123 50 48 ⟨.tilted, 0, 2, true, 196842542078620825⟩,
  .shared 123 51 48 ⟨.tilted, 0, 2, true, 204932519927219063⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, true, 213158470760697550⟩,
  .point 124 43 45,
  .point 124 44 46], by decide +kernel⟩
private def batch28 : PaidBatch .empty 9 := ⟨[
  .point 124 45 47,
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 160542216190461119⟩,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 167419341660855390⟩,
  .shared 124 48 48 ⟨.tilted, 0, 1, false, 174409743808403375⟩,
  .shared 124 49 48 ⟨.tilted, 0, 1, false, 181511979618328822⟩,
  .shared 124 50 48 ⟨.tilted, 0, 2, true, 198381164550245333⟩], by decide +kernel⟩
private def batch29 : PaidBatch .empty 9 := ⟨[
  .shared 124 51 48 ⟨.tilted, 0, 2, true, 206535944462418325⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 214828033484264391⟩,
  .point 125 43 45,
  .point 125 44 46,
  .point 125 45 47,
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 161772119584135640⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 9 := ⟨[
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 168701656788771617⟩,
  .shared 125 48 48 ⟨.tilted, 0, 1, false, 175745432680412141⟩,
  .shared 125 49 48 ⟨.tilted, 0, 1, false, 182902004244280960⟩,
  .shared 125 50 48 ⟨.tilted, 0, 2, true, 199919787021869841⟩,
  .shared 125 51 48 ⟨.tilted, 0, 2, true, 208139368997617588⟩,
  .shared 125 52 48 ⟨.tilted, 0, 2, false, 211988352609718754⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 9) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 125 27 8 = true := by decide +kernel
private theorem index35 : checks tiles 125 35 8 = true := by decide +kernel
private theorem index43 : checks tiles 125 43 8 = true := by decide +kernel
private theorem index51 : checks tiles 125 51 2 = true := by decide +kernel
private theorem covers : checks tiles 125 27 26 = true :=
  checks_join index27 (checks_join index35 (checks_join index43 index51))

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 9 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10

private def batch0 : PaidBatch .empty 10 := ⟨[
  .rectangle 10 30 67 41 35,
  .rectangle 14 42 69 52 42,
  .rectangle 68 30 96 35 35,
  .rectangle 68 36 96 41 41,
  .rectangle 70 48 83 52 44,
  .rectangle 70 42 97 44 41], by decide +kernel⟩
private def batch1 : PaidBatch .empty 10 := ⟨[
  .rectangle 70 45 97 47 44,
  .rectangle 84 48 97 50 47,
  .rectangle 84 51 97 52 47,
  .rectangle 97 39 111 41 43,
  .rectangle 97 30 125 32 38,
  .rectangle 97 33 125 35 41], by decide +kernel⟩
private def batch2 : PaidBatch .empty 10 := ⟨[
  .rectangle 97 36 125 38 45,
  .rectangle 98 50 101 50 46,
  .rectangle 98 51 101 51 47,
  .rectangle 98 52 101 52 48,
  .rectangle 98 42 104 44 44,
  .rectangle 98 45 104 47 47], by decide +kernel⟩
private def batch3 : PaidBatch .empty 10 := ⟨[
  .rectangle 98 48 104 48 46,
  .rectangle 98 49 104 49 47,
  .point 102 51 45,
  .point 102 52 46,
  .rectangle 102 50 103 50 47,
  .point 103 51 45], by decide +kernel⟩
private def batch4 : PaidBatch .empty 10 := ⟨[
  .point 103 52 46,
  .point 104 50 45,
  .point 104 51 46,
  .point 104 52 47,
  .rectangle 105 49 105 49 47,
  .point 105 50 45], by decide +kernel⟩
private def batch5 : PaidBatch .empty 10 := ⟨[
  .point 105 51 46,
  .point 105 52 47,
  .rectangle 105 47 108 47 46,
  .rectangle 105 48 108 48 47,
  .rectangle 105 42 111 43 44,
  .rectangle 105 44 111 44 44], by decide +kernel⟩
private def batch6 : PaidBatch .empty 10 := ⟨[
  .rectangle 105 45 111 45 45,
  .rectangle 105 46 111 46 47,
  .point 106 49 45,
  .point 106 50 46,
  .point 106 51 47,
  .point 106 52 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 10 := ⟨[
  .point 107 49 45,
  .point 107 50 46,
  .point 107 51 47,
  .point 107 52 48,
  .point 108 49 45,
  .point 108 50 46], by decide +kernel⟩
private def batch8 : PaidBatch .empty 10 := ⟨[
  .point 108 51 47,
  .point 108 52 48,
  .point 109 48 45,
  .point 109 49 46,
  .point 109 50 47,
  .point 109 51 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 10 := ⟨[
  .shared 109 52 48 ⟨.tilted, 1, 2, true, 202593160948242890⟩,
  .rectangle 109 47 110 47 47,
  .point 110 48 45,
  .point 110 49 46,
  .point 110 50 47,
  .point 110 51 48], by decide +kernel⟩
private def batch10 : PaidBatch .empty 10 := ⟨[
  .shared 110 52 48 ⟨.tilted, 1, 2, true, 193616732084995774⟩,
  .point 111 47 45,
  .point 111 48 46,
  .point 111 49 47,
  .point 111 50 48,
  .shared 111 51 48 ⟨.tilted, 1, 1, false, 180669918377320121⟩], by decide +kernel⟩
private def batch11 : PaidBatch .empty 10 := ⟨[
  .shared 111 52 48 ⟨.tilted, 1, 2, true, 195286294808562615⟩,
  .point 112 47 45,
  .point 112 48 46,
  .point 112 49 47,
  .point 112 50 48,
  .shared 112 51 48 ⟨.tilted, 1, 1, false, 182196005065674674⟩], by decide +kernel⟩
private def batch12 : PaidBatch .empty 10 := ⟨[
  .shared 112 52 48 ⟨.tilted, 1, 2, true, 196955857532129457⟩,
  .rectangle 112 46 113 46 47,
  .rectangle 112 45 115 45 47,
  .rectangle 112 42 118 43 47,
  .rectangle 112 44 118 44 47,
  .rectangle 112 39 125 40 46], by decide +kernel⟩
private def batch13 : PaidBatch .empty 10 := ⟨[
  .rectangle 112 41 125 41 46,
  .point 113 47 45,
  .point 113 48 46,
  .point 113 49 47,
  .point 113 50 48,
  .shared 113 51 48 ⟨.tilted, 1, 1, false, 183722091754029227⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 10 := ⟨[
  .shared 113 52 48 ⟨.tilted, 1, 2, true, 198625420255696299⟩,
  .point 114 46 45,
  .point 114 47 46,
  .point 114 48 47,
  .shared 114 49 47 ⟨.tilted, 1, 1, false, 171305124337900020⟩,
  .shared 114 50 48 ⟨.tilted, 1, 1, false, 178223500337274316⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 10 := ⟨[
  .shared 114 51 48 ⟨.tilted, 1, 2, true, 204106012726202055⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, true, 200294982979263140⟩,
  .point 115 46 45,
  .point 115 47 46,
  .point 115 48 47,
  .shared 115 49 47 ⟨.tilted, 1, 1, false, 172717408799163379⟩], by decide +kernel⟩
private def batch16 : PaidBatch .empty 10 := ⟨[
  .shared 115 50 48 ⟨.tilted, 1, 1, false, 179692204907157855⟩,
  .shared 115 51 48 ⟨.tilted, 1, 2, true, 194082691657563380⟩,
  .shared 115 52 48 ⟨.tilted, 1, 2, true, 201964545702829982⟩,
  .rectangle 116 45 116 45 47,
  .point 116 46 45,
  .point 116 47 46], by decide +kernel⟩
private def batch17 : PaidBatch .empty 10 := ⟨[
  .shared 116 48 47 ⟨.tilted, 0, 1, false, 167208146184025166⟩,
  .shared 116 49 48 ⟨.tilted, 1, 1, false, 174129693260426738⟩,
  .shared 116 50 48 ⟨.tilted, 1, 1, false, 181160909477041394⟩,
  .shared 116 51 48 ⟨.tilted, 1, 2, true, 195686116192762643⟩,
  .shared 116 52 48 ⟨.tilted, 1, 2, true, 203634108426396824⟩,
  .point 117 45 45], by decide +kernel⟩
private def batch18 : PaidBatch .empty 10 := ⟨[
  .point 117 46 46,
  .point 117 47 47,
  .shared 117 48 47 ⟨.tilted, 0, 1, false, 168564972546519179⟩,
  .shared 117 49 48 ⟨.tilted, 1, 1, false, 175541977721690097⟩,
  .shared 117 50 48 ⟨.tilted, 1, 1, false, 182629614046924933⟩,
  .shared 117 51 48 ⟨.tilted, 1, 2, true, 197289540727961905⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 10 := ⟨[
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 205303671149963665⟩,
  .point 118 45 45,
  .point 118 46 46,
  .point 118 47 47,
  .shared 118 48 47 ⟨.tilted, 0, 1, false, 169921798909013192⟩,
  .shared 118 49 48 ⟨.tilted, 0, 1, false, 176954262182953456⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 10 := ⟨[
  .shared 118 50 48 ⟨.tilted, 1, 1, false, 184098318616808472⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, true, 198892965263161168⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, false, 198715438905157762⟩,
  .rectangle 119 44 119 44 47,
  .point 119 45 45,
  .point 119 46 46], by decide +kernel⟩
private def batch21 : PaidBatch .empty 10 := ⟨[
  .shared 119 47 47 ⟨.tilted, 0, 1, false, 164304702083339435⟩,
  .shared 119 48 47 ⟨.tilted, 0, 1, false, 171278625271507205⟩,
  .shared 119 49 48 ⟨.tilted, 0, 1, false, 178366546644216815⟩,
  .shared 119 50 48 ⟨.tilted, 1, 1, false, 185567023186692011⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 200496389798360430⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, false, 200299869721834163⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 10 := ⟨[
  .rectangle 119 43 122 43 47,
  .rectangle 119 42 125 42 47,
  .point 120 44 45,
  .point 120 45 46,
  .point 120 46 47,
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 165607032356914936⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 10 := ⟨[
  .shared 120 48 47 ⟨.tilted, 0, 1, false, 172635451634001218⟩,
  .shared 120 49 48 ⟨.tilted, 0, 1, false, 179778831105480174⟩,
  .shared 120 50 48 ⟨.tilted, 0, 1, false, 187035727756575550⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 202099814333559693⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, false, 201884300538510564⟩,
  .point 121 44 45], by decide +kernel⟩
private def batch24 : PaidBatch .empty 10 := ⟨[
  .point 121 45 46,
  .point 121 46 47,
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 166909362630490437⟩,
  .shared 121 48 47 ⟨.tilted, 0, 1, false, 173992277996495231⟩,
  .shared 121 49 48 ⟨.tilted, 0, 1, false, 181191115566743533⟩,
  .shared 121 50 48 ⟨.tilted, 0, 2, true, 195566140402296992⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 10 := ⟨[
  .shared 121 51 48 ⟨.tilted, 1, 2, true, 203703238868758955⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, false, 203468731355186965⟩,
  .point 122 44 45,
  .point 122 45 46,
  .shared 122 46 47 ⟨.tilted, 0, 1, false, 161192608678013222⟩,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 168211692904065938⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 10 := ⟨[
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 175349104358989244⟩,
  .shared 122 49 48 ⟨.tilted, 0, 1, false, 182603400028006892⟩,
  .shared 122 50 48 ⟨.tilted, 0, 2, true, 197104762873921500⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, false, 198114328853055297⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, false, 205053162171863366⟩,
  .point 123 43 45], by decide +kernel⟩
private def batch27 : PaidBatch .empty 10 := ⟨[
  .point 123 44 46,
  .point 123 45 47,
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 162441404872521045⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 169514023177641439⟩,
  .shared 123 48 48 ⟨.tilted, 0, 1, false, 176705930721483257⟩,
  .shared 123 49 48 ⟨.tilted, 0, 1, false, 184015684489270251⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 10 := ⟨[
  .shared 123 50 48 ⟨.tilted, 0, 2, true, 198643385345546009⟩,
  .shared 123 51 48 ⟨.tilted, 0, 2, false, 198982958637574757⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, false, 206637592988539767⟩,
  .point 124 43 45,
  .point 124 44 46,
  .point 124 45 47], by decide +kernel⟩
private def batch29 : PaidBatch .empty 10 := ⟨[
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 163690201067028868⟩,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 170816353451216940⟩,
  .shared 124 48 48 ⟨.tilted, 0, 1, false, 178062757083977270⟩,
  .shared 124 49 48 ⟨.tilted, 0, 1, false, 185427968950533610⟩,
  .shared 124 50 48 ⟨.tilted, 0, 2, true, 200182007817170517⟩,
  .shared 124 51 48 ⟨.tilted, 0, 2, false, 200509045325929310⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 10 := ⟨[
  .shared 124 52 48 ⟨.tilted, 1, 2, false, 208222023805216168⟩,
  .point 125 43 45,
  .point 125 44 46,
  .point 125 45 47,
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 164938997261536691⟩,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 172118683724792441⟩], by decide +kernel⟩
private def batch31 : PaidBatch .empty 10 := ⟨[
  .shared 125 48 48 ⟨.tilted, 0, 1, false, 179419583446471283⟩,
  .shared 125 49 48 ⟨.tilted, 0, 1, false, 186840253411796969⟩,
  .shared 125 50 48 ⟨.tilted, 0, 2, true, 201720630288795025⟩,
  .shared 125 51 48 ⟨.tilted, 0, 2, false, 202035132014283863⟩,
  .shared 125 52 48 ⟨.tilted, 0, 2, false, 209806454621892569⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 10) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 125 30 8 = true := by decide +kernel
private theorem index38 : checks tiles 125 38 8 = true := by decide +kernel
private theorem index46 : checks tiles 125 46 7 = true := by decide +kernel
private theorem covers : checks tiles 125 30 23 = true :=
  checks_join index30 (checks_join index38 index46)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 10 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

end Compact50PriceTableEmpty8
