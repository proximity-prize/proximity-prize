import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableEmpty4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top4
private def batch0 : PaidBatch .empty 4 := ⟨[
  .rectangle 4 12 75 19 20,
  .rectangle 7 20 95 27 31,
  .rectangle 10 28 95 35 37,
  .rectangle 12 36 83 43 37,
  .rectangle 15 44 88 51 44,
  .rectangle 18 52 96 53 44], by decide +kernel⟩
private def batch1 : PaidBatch .empty 4 := ⟨[
  .rectangle 76 12 129 19 36,
  .rectangle 84 36 112 40 44,
  .rectangle 84 41 102 45 44,
  .rectangle 89 46 101 50 47,
  .rectangle 89 51 100 53 47,
  .rectangle 96 20 129 26 40], by decide +kernel⟩
private def batch2 : PaidBatch .empty 4 := ⟨[
  .rectangle 96 27 127 32 43,
  .rectangle 96 33 126 36 44,
  .rectangle 101 51 104 52 47,
  .rectangle 101 53 106 53 48,
  .rectangle 102 46 113 47 47,
  .rectangle 102 48 109 49 47], by decide +kernel⟩
private def batch3 : PaidBatch .empty 4 := ⟨[
  .rectangle 102 50 109 50 47,
  .rectangle 103 41 116 43 46,
  .rectangle 103 44 117 45 47,
  .rectangle 105 51 110 51 48,
  .rectangle 105 52 108 52 48,
  .point 107 53 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 4 := ⟨[
  .point 108 53 48,
  .point 109 52 48,
  .point 109 53 48,
  .rectangle 110 48 113 48 47,
  .rectangle 110 49 111 49 47,
  .point 110 50 47], by decide +kernel⟩
private def batch5 : PaidBatch .empty 4 := ⟨[
  .point 110 52 48,
  .point 110 53 48,
  .rectangle 111 50 111 50 48,
  .point 111 51 48,
  .point 111 52 48,
  .point 111 53 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 4 := ⟨[
  .point 112 49 47,
  .point 112 50 48,
  .point 112 51 48,
  .point 112 52 48,
  .point 112 53 48,
  .rectangle 113 37 126 39 46], by decide +kernel⟩
private def batch7 : PaidBatch .empty 4 := ⟨[
  .rectangle 113 40 124 41 46,
  .point 113 49 47,
  .point 113 50 48,
  .point 113 51 48,
  .point 113 52 48,
  .point 113 53 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 4 := ⟨[
  .rectangle 114 46 117 46 47,
  .rectangle 114 47 115 47 47,
  .point 114 48 47,
  .point 114 49 47,
  .point 114 50 48,
  .point 114 51 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 4 := ⟨[
  .point 114 52 48,
  .point 114 53 48,
  .point 115 48 47,
  .point 115 49 47,
  .point 115 50 48,
  .point 115 51 48], by decide +kernel⟩
private def batch10 : PaidBatch .empty 4 := ⟨[
  .point 115 52 48,
  .shared 115 53 48 ⟨.tilted, 1, 2, true, 179500148555645243⟩,
  .point 116 47 47,
  .point 116 48 47,
  .point 116 49 48,
  .point 116 50 48], by decide +kernel⟩
private def batch11 : PaidBatch .empty 4 := ⟨[
  .point 116 51 48,
  .point 116 52 48,
  .shared 116 53 48 ⟨.tilted, 1, 2, true, 181167354308641135⟩,
  .rectangle 117 42 127 42 47,
  .rectangle 117 43 124 43 47,
  .point 117 47 47], by decide +kernel⟩
private def batch12 : PaidBatch .empty 4 := ⟨[
  .point 117 48 47,
  .point 117 49 48,
  .point 117 50 48,
  .point 117 51 48,
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 176397247870472076⟩,
  .shared 117 53 48 ⟨.tilted, 1, 2, true, 182834560061637027⟩], by decide +kernel⟩
private def batch13 : PaidBatch .empty 4 := ⟨[
  .rectangle 118 44 122 44 47,
  .rectangle 118 45 119 45 47,
  .point 118 46 47,
  .point 118 47 47,
  .point 118 48 47,
  .point 118 49 48], by decide +kernel⟩
private def batch14 : PaidBatch .empty 4 := ⟨[
  .point 118 50 48,
  .point 118 51 48,
  .shared 118 52 48 ⟨.tilted, 1, 2, true, 177999691870724660⟩,
  .shared 118 53 48 ⟨.tilted, 1, 2, true, 184501765814632919⟩,
  .point 119 46 47,
  .point 119 47 47], by decide +kernel⟩
private def batch15 : PaidBatch .empty 4 := ⟨[
  .point 119 48 47,
  .point 119 49 48,
  .point 119 50 48,
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 173120936733180929⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, true, 179602135870977244⟩,
  .shared 119 53 48 ⟨.tilted, 1, 2, true, 186168971567628811⟩], by decide +kernel⟩
private def batch16 : PaidBatch .empty 4 := ⟨[
  .point 120 45 47,
  .point 120 46 47,
  .point 120 47 47,
  .point 120 48 47,
  .point 120 49 48,
  .point 120 50 48], by decide +kernel⟩
private def batch17 : PaidBatch .empty 4 := ⟨[
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 174659901391424197⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, true, 181204579871229828⟩,
  .shared 120 53 48 ⟨.tilted, 1, 2, true, 187836177320624703⟩,
  .point 121 45 47,
  .point 121 46 47,
  .point 121 47 47], by decide +kernel⟩
private def batch18 : PaidBatch .empty 4 := ⟨[
  .point 121 48 47,
  .point 121 49 48,
  .shared 121 50 48 ⟨.tilted, 1, 2, true, 169680833224276740⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, true, 176198866049667465⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, true, 182807023871482412⟩,
  .shared 121 53 48 ⟨.tilted, 1, 2, true, 189503383073620595⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 4 := ⟨[
  .point 122 45 47,
  .point 122 46 47,
  .point 122 47 47,
  .point 122 48 48,
  .point 122 49 48,
  .shared 122 50 48 ⟨.tilted, 1, 2, true, 171157600951244684⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 4 := ⟨[
  .shared 122 51 48 ⟨.tilted, 1, 2, true, 177737830707910733⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, true, 184409467871734996⟩,
  .shared 122 53 48 ⟨.tilted, 1, 2, true, 191170588826616487⟩,
  .point 123 44 47,
  .point 123 45 47,
  .point 123 46 47], by decide +kernel⟩
private def batch21 : PaidBatch .empty 4 := ⟨[
  .point 123 47 47,
  .point 123 48 48,
  .shared 123 49 48 ⟨.tilted, 1, 2, true, 166086555424264451⟩,
  .shared 123 50 48 ⟨.tilted, 1, 2, true, 172634368678212628⟩,
  .shared 123 51 48 ⟨.tilted, 1, 2, true, 179276795366154001⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, true, 186011911871987580⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 4 := ⟨[
  .shared 123 53 48 ⟨.tilted, 1, 2, true, 192837794579612379⟩,
  .point 124 44 47,
  .point 124 45 47,
  .point 124 46 47,
  .point 124 47 47,
  .point 124 48 48], by decide +kernel⟩
private def batch23 : PaidBatch .empty 4 := ⟨[
  .shared 124 49 48 ⟨.tilted, 1, 2, true, 167502408630691063⟩,
  .shared 124 50 48 ⟨.tilted, 1, 2, true, 174111136405180572⟩,
  .shared 124 51 48 ⟨.tilted, 1, 2, true, 180815760024397269⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 187614355872240164⟩,
  .shared 124 53 48 ⟨.tilted, 1, 2, true, 194505000332608271⟩,
  .rectangle 125 40 129 40 47], by decide +kernel⟩
private def batch24 : PaidBatch .empty 4 := ⟨[
  .rectangle 125 41 129 41 47,
  .point 125 43 47,
  .point 125 44 47,
  .point 125 45 47,
  .point 125 46 47,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 146099546000792577⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 4 := ⟨[
  .shared 125 48 48 ⟨.tilted, 0, 2, true, 162347721413649000⟩,
  .shared 125 49 48 ⟨.tilted, 0, 2, true, 168918261837117675⟩,
  .shared 125 50 48 ⟨.tilted, 1, 2, true, 175587904132148516⟩,
  .shared 125 51 48 ⟨.tilted, 1, 2, true, 182354724682640537⟩,
  .shared 125 52 48 ⟨.tilted, 1, 2, true, 189216799872492748⟩,
  .shared 125 53 48 ⟨.tilted, 1, 2, true, 196172206085604163⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 4 := ⟨[
  .point 126 43 47,
  .point 126 44 47,
  .point 126 45 47,
  .point 126 46 47,
  .shared 126 47 47 ⟨.tilted, 0, 1, false, 147302937586966029⟩,
  .shared 126 48 48 ⟨.tilted, 0, 2, true, 163703942510268272⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 4 := ⟨[
  .shared 126 49 48 ⟨.tilted, 0, 2, true, 170334115043544287⟩,
  .shared 126 50 48 ⟨.tilted, 1, 2, true, 177064671859116460⟩,
  .shared 126 51 48 ⟨.tilted, 1, 2, true, 183893689340883805⟩,
  .shared 126 52 48 ⟨.tilted, 1, 2, true, 190819243872745332⟩,
  .shared 126 53 48 ⟨.tilted, 1, 2, true, 197839411838600055⟩,
  .rectangle 127 33 129 36 45], by decide +kernel⟩
private def batch28 : PaidBatch .empty 4 := ⟨[
  .rectangle 127 37 129 38 46,
  .rectangle 127 39 129 39 46,
  .point 127 43 47,
  .point 127 44 47,
  .point 127 45 47,
  .shared 127 46 47 ⟨.tilted, 0, 1, false, 142553282847439036⟩], by decide +kernel⟩
private def batch29 : PaidBatch .empty 4 := ⟨[
  .shared 127 47 47 ⟨.tilted, 0, 1, false, 148506329173139480⟩,
  .shared 127 48 48 ⟨.tilted, 0, 2, true, 165060163606887544⟩,
  .shared 127 49 48 ⟨.tilted, 0, 2, true, 171749968249970899⟩,
  .shared 127 50 48 ⟨.tilted, 1, 2, true, 178541439586084404⟩,
  .shared 127 51 48 ⟨.tilted, 1, 2, true, 185432653999127073⟩,
  .shared 127 52 48 ⟨.tilted, 1, 2, true, 192421687872997916⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 4 := ⟨[
  .shared 127 53 48 ⟨.tilted, 1, 2, true, 199506617591595947⟩,
  .rectangle 128 27 129 31 43,
  .rectangle 128 32 129 35 45,
  .point 128 42 47,
  .point 128 43 47,
  .point 128 44 47], by decide +kernel⟩
private def batch31 : PaidBatch .empty 4 := ⟨[
  .point 128 45 47,
  .shared 128 46 47 ⟨.tilted, 0, 1, false, 143705030673468470⟩,
  .shared 128 47 47 ⟨.tilted, 0, 1, false, 149709720759312932⟩,
  .shared 128 48 48 ⟨.tilted, 0, 2, true, 166416384703506816⟩,
  .shared 128 49 48 ⟨.tilted, 0, 2, true, 173165821456397511⟩,
  .shared 128 50 48 ⟨.tilted, 0, 2, true, 180018207313052348⟩], by decide +kernel⟩
private def batch32 : PaidBatch .empty 4 := ⟨[
  .shared 128 51 48 ⟨.tilted, 1, 2, true, 186971618657370341⟩,
  .shared 128 52 48 ⟨.tilted, 1, 2, true, 194024131873250500⟩,
  .shared 128 53 48 ⟨.tilted, 1, 2, true, 201173823344591839⟩,
  .point 129 42 47,
  .point 129 43 47,
  .point 129 44 47], by decide +kernel⟩
private def batch33 : PaidBatch .empty 4 := ⟨[
  .point 129 45 47,
  .shared 129 46 47 ⟨.tilted, 0, 1, false, 144856778499497904⟩,
  .shared 129 47 47 ⟨.tilted, 0, 1, false, 150913112345486383⟩,
  .shared 129 48 48 ⟨.tilted, 0, 2, true, 167772605800126088⟩,
  .shared 129 49 48 ⟨.tilted, 0, 2, true, 174581674662824123⟩,
  .shared 129 50 48 ⟨.tilted, 0, 2, true, 181494975040020292⟩], by decide +kernel⟩
private def batch34 : PaidBatch .empty 4 := ⟨[
  .shared 129 51 48 ⟨.tilted, 1, 2, true, 188510583315613609⟩,
  .shared 129 52 48 ⟨.tilted, 1, 2, true, 195626575873503084⟩,
  .shared 129 53 49 ⟨.tilted, 1, 2, true, 202841029097587731⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 4) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32, batch33, batch34]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 129 12 10 = true := by decide +kernel
theorem index22 : checks tiles 129 22 10 = true := by decide +kernel
theorem index32 : checks tiles 129 32 10 = true := by decide +kernel
theorem index42 : checks tiles 129 42 10 = true := by decide +kernel
theorem index52 : checks tiles 129 52 2 = true := by decide +kernel
private theorem covers : checks tiles 129 12 42 = true :=
  checks_join (checks_join (checks_join (checks_join (index12) index22) index32) index42) index52

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 4 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5
private def batch0 : PaidBatch .empty 5 := ⟨[
  .rectangle 5 15 94 22 27,
  .rectangle 8 23 87 30 31,
  .rectangle 11 31 88 38 37,
  .rectangle 13 39 91 46 44,
  .rectangle 16 47 85 53 44,
  .rectangle 86 47 100 50 47], by decide +kernel⟩
private def batch1 : PaidBatch .empty 5 := ⟨[
  .rectangle 86 51 98 53 47,
  .rectangle 88 23 124 29 41,
  .rectangle 88 30 124 34 43,
  .rectangle 89 35 113 39 44,
  .rectangle 92 40 111 42 44,
  .rectangle 92 43 110 45 46], by decide +kernel⟩
private def batch2 : PaidBatch .empty 5 := ⟨[
  .rectangle 92 46 106 48 47,
  .rectangle 95 15 126 22 36,
  .rectangle 99 51 105 51 47,
  .rectangle 99 52 102 53 48,
  .rectangle 101 49 105 50 47,
  .rectangle 103 52 105 52 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 5 := ⟨[
  .rectangle 103 53 104 53 48,
  .point 105 53 48,
  .rectangle 106 49 109 49 47,
  .rectangle 106 50 107 50 47,
  .rectangle 106 51 107 51 48,
  .point 106 52 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 5 := ⟨[
  .point 106 53 48,
  .rectangle 107 46 115 46 47,
  .rectangle 107 47 113 47 47,
  .rectangle 107 48 111 48 47,
  .point 107 52 48,
  .point 107 53 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 5 := ⟨[
  .point 108 50 47,
  .point 108 51 48,
  .point 108 52 48,
  .point 108 53 48,
  .point 109 50 47,
  .point 109 51 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 5 := ⟨[
  .point 109 52 48,
  .point 109 53 48,
  .point 110 49 47,
  .point 110 50 47,
  .point 110 51 48,
  .point 110 52 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 5 := ⟨[
  .point 110 53 48,
  .rectangle 111 43 117 44 47,
  .rectangle 111 45 117 45 47,
  .point 111 49 47,
  .point 111 50 48,
  .point 111 51 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 5 := ⟨[
  .point 111 52 48,
  .point 111 53 48,
  .rectangle 112 40 122 41 46,
  .rectangle 112 42 119 43 47,
  .point 112 48 47,
  .point 112 49 47], by decide +kernel⟩
private def batch9 : PaidBatch .empty 5 := ⟨[
  .point 112 50 48,
  .point 112 51 48,
  .point 112 52 48,
  .shared 112 53 48 ⟨.tilted, 1, 2, true, 180907796405673728⟩,
  .point 113 48 47,
  .point 113 49 47], by decide +kernel⟩
private def batch10 : PaidBatch .empty 5 := ⟨[
  .point 113 50 48,
  .point 113 51 48,
  .point 113 52 48,
  .shared 113 53 48 ⟨.tilted, 1, 2, true, 182575002158669620⟩,
  .rectangle 114 35 128 37 45,
  .rectangle 114 38 128 39 46], by decide +kernel⟩
private def batch11 : PaidBatch .empty 5 := ⟨[
  .point 114 47 47,
  .point 114 48 47,
  .point 114 49 47,
  .point 114 50 48,
  .point 114 51 48,
  .shared 114 52 48 ⟨.tilted, 1, 2, true, 177673502114370409⟩], by decide +kernel⟩
private def batch12 : PaidBatch .empty 5 := ⟨[
  .shared 114 53 48 ⟨.tilted, 1, 2, true, 184242207911665512⟩,
  .point 115 47 47,
  .point 115 48 47,
  .point 115 49 47,
  .point 115 50 48,
  .point 115 51 48], by decide +kernel⟩
private def batch13 : PaidBatch .empty 5 := ⟨[
  .shared 115 52 48 ⟨.tilted, 1, 2, true, 179275946114622993⟩,
  .shared 115 53 48 ⟨.tilted, 1, 2, true, 185909413664661404⟩,
  .point 116 46 47,
  .point 116 47 47,
  .point 116 48 47,
  .point 116 49 48], by decide +kernel⟩
private def batch14 : PaidBatch .empty 5 := ⟨[
  .point 116 50 48,
  .shared 116 51 48 ⟨.tilted, 1, 2, true, 174270446109859829⟩,
  .shared 116 52 48 ⟨.tilted, 1, 2, true, 180878390114875577⟩,
  .shared 116 53 48 ⟨.tilted, 1, 2, true, 187576619417657296⟩,
  .point 117 46 47,
  .point 117 47 47], by decide +kernel⟩
private def batch15 : PaidBatch .empty 5 := ⟨[
  .point 117 48 47,
  .point 117 49 48,
  .point 117 50 48,
  .shared 117 51 48 ⟨.tilted, 1, 2, true, 175809410768103097⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 182480834115128161⟩,
  .shared 117 53 48 ⟨.tilted, 1, 2, true, 189243825170653188⟩], by decide +kernel⟩
private def batch16 : PaidBatch .empty 5 := ⟨[
  .rectangle 118 44 120 44 47,
  .point 118 45 47,
  .point 118 46 47,
  .point 118 47 47,
  .point 118 48 47,
  .point 118 49 48], by decide +kernel⟩
private def batch17 : PaidBatch .empty 5 := ⟨[
  .shared 118 50 48 ⟨.tilted, 1, 2, true, 170708246472646930⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, true, 177348375426346365⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, true, 184083278115380745⟩,
  .shared 118 53 48 ⟨.tilted, 1, 2, true, 190911030923649080⟩,
  .point 119 45 47,
  .point 119 46 47], by decide +kernel⟩
private def batch18 : PaidBatch .empty 5 := ⟨[
  .point 119 47 47,
  .point 119 48 47,
  .point 119 49 48,
  .shared 119 50 48 ⟨.tilted, 1, 2, true, 172185014199614874⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 178887340084589633⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, true, 185685722115633329⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 5 := ⟨[
  .shared 119 53 48 ⟨.tilted, 1, 2, true, 192578236676644972⟩,
  .rectangle 120 42 125 42 47,
  .rectangle 120 43 122 43 47,
  .point 120 45 47,
  .point 120 46 47,
  .point 120 47 47], by decide +kernel⟩
private def batch20 : PaidBatch .empty 5 := ⟨[
  .shared 120 48 47 ⟨.tilted, 1, 1, false, 152178830381026254⟩,
  .shared 120 49 48 ⟨.tilted, 1, 2, true, 166996521283236650⟩,
  .shared 120 50 48 ⟨.tilted, 1, 2, true, 173661781926582818⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 180426304742832901⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, true, 187288166115885913⟩,
  .shared 120 53 48 ⟨.tilted, 1, 2, true, 194245442429640864⟩], by decide +kernel⟩
private def batch21 : PaidBatch .empty 5 := ⟨[
  .point 121 44 47,
  .point 121 45 47,
  .point 121 46 47,
  .point 121 47 47,
  .shared 121 48 47 ⟨.tilted, 1, 1, false, 153451258421321981⟩,
  .shared 121 49 48 ⟨.tilted, 1, 2, true, 168412374489663262⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 5 := ⟨[
  .shared 121 50 48 ⟨.tilted, 1, 2, true, 175138549653550762⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, true, 181965269401076169⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, true, 188890610116138497⟩,
  .shared 121 53 48 ⟨.tilted, 1, 2, true, 195912648182636756⟩,
  .point 122 44 47,
  .point 122 45 47], by decide +kernel⟩
private def batch23 : PaidBatch .empty 5 := ⟨[
  .point 122 46 47,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 148619520562769759⟩,
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 154723686461617709⟩,
  .shared 122 49 48 ⟨.tilted, 1, 2, true, 169828227696089874⟩,
  .shared 122 50 48 ⟨.tilted, 1, 2, true, 176615317380518706⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, true, 183504234059319437⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 5 := ⟨[
  .shared 122 52 48 ⟨.tilted, 1, 2, true, 190493054116391081⟩,
  .shared 122 53 48 ⟨.tilted, 1, 2, true, 197579853935632648⟩,
  .rectangle 123 40 129 40 47,
  .rectangle 123 41 128 41 47,
  .point 123 43 47,
  .point 123 44 47], by decide +kernel⟩
private def batch25 : PaidBatch .empty 5 := ⟨[
  .point 123 45 47,
  .point 123 46 47,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 149838701829503979⟩,
  .shared 123 48 48 ⟨.tilted, 0, 2, true, 164501109718753203⟩,
  .shared 123 49 48 ⟨.tilted, 1, 2, true, 171244080902516486⟩,
  .shared 123 50 48 ⟨.tilted, 1, 2, true, 178092085107486650⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 5 := ⟨[
  .shared 123 51 48 ⟨.tilted, 1, 2, true, 185043198717562705⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, true, 192095498116643665⟩,
  .shared 123 53 48 ⟨.tilted, 1, 2, true, 199247059688628540⟩,
  .point 124 43 47,
  .point 124 44 47,
  .point 124 45 47], by decide +kernel⟩
private def batch27 : PaidBatch .empty 5 := ⟨[
  .point 124 46 47,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 151057883096238199⟩,
  .shared 124 48 48 ⟨.tilted, 0, 2, true, 165857330815372475⟩,
  .shared 124 49 48 ⟨.tilted, 1, 2, true, 172659934108943098⟩,
  .shared 124 50 48 ⟨.tilted, 1, 2, true, 179568852834454594⟩,
  .shared 124 51 48 ⟨.tilted, 1, 2, true, 186582163375805973⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 5 := ⟨[
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 193697942116896249⟩,
  .shared 124 53 48 ⟨.tilted, 1, 2, true, 200914265441624432⟩,
  .rectangle 125 23 129 28 41,
  .rectangle 125 29 129 33 44,
  .rectangle 125 34 129 36 45,
  .point 125 43 47], by decide +kernel⟩
private def batch29 : PaidBatch .empty 5 := ⟨[
  .point 125 44 47,
  .point 125 45 47,
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 146112954653615858⟩,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 152277064362972419⟩,
  .shared 125 48 48 ⟨.tilted, 0, 2, true, 167213551911991747⟩,
  .shared 125 49 48 ⟨.tilted, 0, 2, true, 174075787315369710⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 5 := ⟨[
  .shared 125 50 48 ⟨.tilted, 1, 2, true, 181045620561422538⟩,
  .shared 125 51 48 ⟨.tilted, 1, 2, true, 188121128034049241⟩,
  .shared 125 52 48 ⟨.tilted, 1, 2, true, 195300386117148833⟩,
  .shared 125 53 48 ⟨.tilted, 1, 2, true, 202581471194620324⟩,
  .point 126 42 47,
  .point 126 43 47], by decide +kernel⟩
private def batch31 : PaidBatch .empty 5 := ⟨[
  .point 126 44 47,
  .point 126 45 47,
  .shared 126 46 47 ⟨.tilted, 0, 1, false, 147280011256180813⟩,
  .shared 126 47 47 ⟨.tilted, 0, 1, false, 153496245629706639⟩,
  .shared 126 48 48 ⟨.tilted, 0, 2, true, 168569773008611019⟩,
  .shared 126 49 48 ⟨.tilted, 0, 2, true, 175491640521796322⟩], by decide +kernel⟩
private def batch32 : PaidBatch .empty 5 := ⟨[
  .shared 126 50 48 ⟨.tilted, 1, 2, true, 182522388288390482⟩,
  .shared 126 51 48 ⟨.tilted, 1, 2, true, 189660092692292509⟩,
  .shared 126 52 48 ⟨.tilted, 1, 2, true, 196902830117401417⟩,
  .shared 126 53 48 ⟨.tilted, 1, 2, true, 204248676947616216⟩,
  .rectangle 127 15 129 21 36,
  .rectangle 127 22 129 27 41], by decide +kernel⟩
private def batch33 : PaidBatch .empty 5 := ⟨[
  .point 127 42 47,
  .point 127 43 47,
  .point 127 44 47,
  .shared 127 45 47 ⟨.tilted, 0, 1, false, 142282432714099438⟩,
  .shared 127 46 47 ⟨.tilted, 0, 1, false, 148447067858745769⟩,
  .shared 127 47 47 ⟨.tilted, 0, 1, false, 154715426896440859⟩], by decide +kernel⟩
private def batch34 : PaidBatch .empty 5 := ⟨[
  .shared 127 48 48 ⟨.tilted, 0, 2, true, 169925994105230291⟩,
  .shared 127 49 48 ⟨.tilted, 0, 2, true, 176907493728222934⟩,
  .shared 127 50 48 ⟨.tilted, 1, 2, true, 183999156015358426⟩,
  .shared 127 51 48 ⟨.tilted, 1, 2, true, 191199057350535777⟩,
  .shared 127 52 48 ⟨.tilted, 1, 2, true, 198505274117654001⟩,
  .shared 127 53 48 ⟨.tilted, 1, 2, true, 205915882700612108⟩], by decide +kernel⟩
private def batch35 : PaidBatch .empty 5 := ⟨[
  .point 128 42 47,
  .point 128 43 47,
  .point 128 44 47,
  .shared 128 45 47 ⟨.tilted, 0, 1, false, 143398486761887372⟩,
  .shared 128 46 47 ⟨.tilted, 0, 1, false, 149614124461310724⟩,
  .shared 128 47 47 ⟨.tilted, 0, 1, false, 155934608163175079⟩], by decide +kernel⟩
private def batch36 : PaidBatch .empty 5 := ⟨[
  .shared 128 48 48 ⟨.tilted, 0, 2, true, 171282215201849563⟩,
  .shared 128 49 48 ⟨.tilted, 0, 2, true, 178323346934649546⟩,
  .shared 128 50 48 ⟨.tilted, 0, 2, true, 185475923742326370⟩,
  .shared 128 51 48 ⟨.tilted, 1, 2, true, 192738022008779045⟩,
  .shared 128 52 48 ⟨.tilted, 1, 2, true, 200107718117906585⟩,
  .shared 128 53 48 ⟨.tilted, 1, 2, true, 207583088453608000⟩], by decide +kernel⟩
private def batch37 : PaidBatch .empty 5 := ⟨[
  .rectangle 129 37 129 38 46,
  .rectangle 129 39 129 39 46,
  .point 129 41 47,
  .point 129 42 47,
  .point 129 43 47,
  .point 129 44 47], by decide +kernel⟩
private def batch38 : PaidBatch .empty 5 := ⟨[
  .shared 129 45 47 ⟨.tilted, 0, 1, false, 144514540809675306⟩,
  .shared 129 46 47 ⟨.tilted, 0, 1, false, 150781181063875680⟩,
  .shared 129 47 47 ⟨.tilted, 0, 1, false, 157153789429909299⟩,
  .shared 129 48 48 ⟨.tilted, 0, 2, true, 172638436298468835⟩,
  .shared 129 49 48 ⟨.tilted, 0, 2, true, 179739200141076158⟩,
  .shared 129 50 48 ⟨.tilted, 0, 2, true, 186952691469294314⟩], by decide +kernel⟩
private def batch39 : PaidBatch .empty 5 := ⟨[
  .shared 129 51 48 ⟨.tilted, 1, 2, true, 194276986667022313⟩,
  .shared 129 52 48 ⟨.tilted, 1, 2, true, 201710162118159169⟩,
  .shared 129 53 49 ⟨.tilted, 1, 2, true, 209250294206603892⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 5) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32, batch33, batch34, batch35, batch36, batch37, batch38, batch39]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 129 15 10 = true := by decide +kernel
theorem index25 : checks tiles 129 25 10 = true := by decide +kernel
theorem index35 : checks tiles 129 35 10 = true := by decide +kernel
theorem index45 : checks tiles 129 45 9 = true := by decide +kernel
private theorem covers : checks tiles 129 15 39 = true :=
  checks_join (checks_join (checks_join (index15) index25) index35) index45

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 5 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

end Compact50PriceTableEmpty4
