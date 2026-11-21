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
  .rectangle 8 24 66 38 39,
  .rectangle 13 39 69 52 45,
  .rectangle 67 32 96 38 44,
  .rectangle 67 24 125 27 43,
  .rectangle 67 28 125 31 44,
  .rectangle 70 50 83 52 48], by decide +kernel⟩
private def batch1 : PaidBatch .empty 8 := ⟨[
  .rectangle 70 39 97 42 46,
  .rectangle 70 43 97 45 46,
  .rectangle 70 46 97 49 48,
  .rectangle 84 50 90 52 48,
  .rectangle 91 50 97 51 48,
  .rectangle 91 52 97 52 48], by decide +kernel⟩
private def batch2 : PaidBatch .empty 8 := ⟨[
  .rectangle 97 32 125 35 46,
  .rectangle 97 36 125 38 47,
  .rectangle 98 51 101 51 48,
  .rectangle 98 52 101 52 49,
  .rectangle 98 43 104 45 48,
  .rectangle 98 46 104 47 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 8 := ⟨[
  .rectangle 98 48 104 49 48,
  .rectangle 98 50 104 50 48,
  .rectangle 98 39 111 42 47,
  .rectangle 102 51 102 51 48,
  .rectangle 102 52 103 52 49,
  .point 103 51 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 8 := ⟨[
  .point 104 51 48,
  .point 104 52 49,
  .point 105 50 48,
  .rectangle 105 51 105 51 49,
  .point 105 52 49,
  .rectangle 105 49 106 49 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 8 := ⟨[
  .rectangle 105 48 108 48 48,
  .rectangle 105 43 111 45 48,
  .rectangle 105 46 111 46 48,
  .rectangle 105 47 111 47 48,
  .point 106 50 48,
  .point 106 51 49], by decide +kernel⟩
private def batch6 : PaidBatch .empty 8 := ⟨[
  .point 106 52 49,
  .rectangle 107 49 107 49 48,
  .point 107 50 48,
  .point 107 51 49,
  .point 107 52 49,
  .point 108 49 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 8 := ⟨[
  .point 108 50 48,
  .point 108 51 49,
  .point 108 52 49,
  .rectangle 109 48 109 48 48,
  .point 109 49 48,
  .point 109 50 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 8 := ⟨[
  .point 109 51 49,
  .point 109 52 49,
  .point 110 48 48,
  .point 110 49 48,
  .point 110 50 48,
  .point 110 51 49], by decide +kernel⟩
private def batch9 : PaidBatch .empty 8 := ⟨[
  .point 110 52 49,
  .point 111 48 48,
  .point 111 49 48,
  .point 111 50 49,
  .point 111 51 49,
  .shared 111 52 49 ⟨.tilted, 1, 2, true, 190279405383064979⟩], by decide +kernel⟩
private def batch10 : PaidBatch .empty 8 := ⟨[
  .point 112 47 48,
  .point 112 48 48,
  .point 112 49 48,
  .point 112 50 49,
  .point 112 51 49,
  .shared 112 52 49 ⟨.tilted, 1, 2, true, 191948292708869170⟩], by decide +kernel⟩
private def batch11 : PaidBatch .empty 8 := ⟨[
  .rectangle 112 46 113 46 48,
  .rectangle 112 45 115 45 48,
  .rectangle 112 41 118 42 48,
  .rectangle 112 43 118 43 48,
  .rectangle 112 44 118 44 48,
  .rectangle 112 39 125 40 47], by decide +kernel⟩
private def batch12 : PaidBatch .empty 8 := ⟨[
  .point 113 47 48,
  .point 113 48 48,
  .point 113 49 48,
  .point 113 50 49,
  .shared 113 51 49 ⟨.tilted, 1, 1, false, 174401423622812259⟩,
  .shared 113 52 49 ⟨.tilted, 1, 2, true, 193617180034673362⟩], by decide +kernel⟩
private def batch13 : PaidBatch .empty 8 := ⟨[
  .rectangle 114 46 114 46 48,
  .point 114 47 48,
  .point 114 48 48,
  .point 114 49 48,
  .point 114 50 49,
  .shared 114 51 49 ⟨.tilted, 1, 2, true, 187868222859791335⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 8 := ⟨[
  .shared 114 52 49 ⟨.tilted, 1, 2, true, 195286067360477554⟩,
  .point 115 46 48,
  .point 115 47 48,
  .point 115 48 48,
  .shared 115 49 48 ⟨.tilted, 1, 1, false, 164393478068631415⟩,
  .shared 115 50 49 ⟨.tilted, 1, 1, false, 170823926669352973⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 8 := ⟨[
  .shared 115 51 49 ⟨.tilted, 1, 2, true, 189470998752490048⟩,
  .shared 115 52 49 ⟨.tilted, 1, 2, true, 196954954686281745⟩,
  .rectangle 116 45 116 45 48,
  .point 116 46 48,
  .point 116 47 48,
  .point 116 48 48], by decide +kernel⟩
private def batch16 : PaidBatch .empty 8 := ⟨[
  .point 116 49 49,
  .shared 116 50 49 ⟨.tilted, 1, 1, false, 172241925980978960⟩,
  .shared 116 51 49 ⟨.tilted, 1, 2, true, 191073774645188760⟩,
  .shared 116 52 49 ⟨.tilted, 1, 2, true, 198623842012085937⟩,
  .point 117 45 48,
  .point 117 46 48], by decide +kernel⟩
private def batch17 : PaidBatch .empty 8 := ⟨[
  .point 117 47 48,
  .point 117 48 48,
  .point 117 49 49,
  .shared 117 50 49 ⟨.tilted, 1, 1, false, 173659925292604947⟩,
  .shared 117 51 49 ⟨.tilted, 1, 2, true, 192676550537887473⟩,
  .shared 117 52 49 ⟨.tilted, 1, 2, true, 200292729337890129⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 8 := ⟨[
  .point 118 45 48,
  .point 118 46 48,
  .point 118 47 48,
  .shared 118 48 48 ⟨.tilted, 0, 1, false, 161989710900920662⟩,
  .shared 118 49 49 ⟨.tilted, 0, 1, false, 168485015494285072⟩,
  .shared 118 50 49 ⟨.tilted, 1, 1, false, 175077924604230934⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 8 := ⟨[
  .shared 118 51 49 ⟨.tilted, 1, 2, true, 194279326430586185⟩,
  .shared 118 52 49 ⟨.tilted, 1, 2, true, 201961616663694320⟩,
  .rectangle 119 44 119 44 48,
  .point 119 45 48,
  .point 119 46 48,
  .point 119 47 48], by decide +kernel⟩
private def batch20 : PaidBatch .empty 8 := ⟨[
  .shared 119 48 48 ⟨.tilted, 0, 1, false, 163300364827080531⟩,
  .shared 119 49 49 ⟨.tilted, 0, 1, false, 169848861302836291⟩,
  .shared 119 50 49 ⟨.tilted, 1, 1, false, 176495923915856921⟩,
  .shared 119 51 49 ⟨.tilted, 1, 2, true, 195882102323284898⟩,
  .shared 119 52 49 ⟨.tilted, 1, 2, true, 203630503989498512⟩,
  .rectangle 119 43 122 43 48], by decide +kernel⟩
private def batch21 : PaidBatch .empty 8 := ⟨[
  .rectangle 119 41 125 41 48,
  .rectangle 119 42 125 42 48,
  .point 120 44 48,
  .point 120 45 48,
  .point 120 46 48,
  .shared 120 47 48 ⟨.tilted, 0, 1, false, 158110300584066708⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 8 := ⟨[
  .shared 120 48 48 ⟨.tilted, 0, 1, false, 164611018753240400⟩,
  .shared 120 49 49 ⟨.tilted, 0, 1, false, 171212707111387510⟩,
  .shared 120 50 49 ⟨.tilted, 0, 1, false, 177913923227482908⟩,
  .shared 120 51 49 ⟨.tilted, 1, 2, true, 197484878215983610⟩,
  .shared 120 52 49 ⟨.tilted, 1, 2, true, 205299391315302704⟩,
  .point 121 44 48], by decide +kernel⟩
private def batch23 : PaidBatch .empty 8 := ⟨[
  .point 121 45 48,
  .point 121 46 48,
  .shared 121 47 48 ⟨.tilted, 0, 1, false, 159368724248518645⟩,
  .shared 121 48 48 ⟨.tilted, 0, 1, false, 165921672679400269⟩,
  .shared 121 49 49 ⟨.tilted, 0, 1, false, 172576552919938729⟩,
  .shared 121 50 49 ⟨.tilted, 0, 2, true, 191331995764086029⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 8 := ⟨[
  .shared 121 51 49 ⟨.tilted, 1, 2, true, 199087654108682323⟩,
  .shared 121 52 49 ⟨.tilted, 1, 2, true, 206968278641106895⟩,
  .point 122 44 48,
  .point 122 45 48,
  .point 122 46 48,
  .shared 122 47 48 ⟨.tilted, 0, 1, false, 160627147912970582⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 8 := ⟨[
  .shared 122 48 49 ⟨.tilted, 0, 1, false, 167232326605560138⟩,
  .shared 122 49 49 ⟨.tilted, 0, 1, false, 173940398728489948⟩,
  .shared 122 50 49 ⟨.tilted, 0, 2, true, 192869995807961787⟩,
  .shared 122 51 49 ⟨.tilted, 1, 2, true, 200690430001381035⟩,
  .shared 122 52 49 ⟨.tilted, 1, 2, true, 208637165966911087⟩,
  .point 123 43 48], by decide +kernel⟩
private def batch26 : PaidBatch .empty 8 := ⟨[
  .point 123 44 48,
  .point 123 45 48,
  .shared 123 46 48 ⟨.tilted, 0, 1, false, 155333460105173827⟩,
  .shared 123 47 48 ⟨.tilted, 0, 1, false, 161885571577422519⟩,
  .shared 123 48 49 ⟨.tilted, 0, 1, false, 168542980531720007⟩,
  .shared 123 49 49 ⟨.tilted, 0, 1, false, 175304244537041167⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 8 := ⟨[
  .shared 123 50 49 ⟨.tilted, 0, 2, true, 194407995851837545⟩,
  .shared 123 51 49 ⟨.tilted, 0, 2, true, 202293205894079748⟩,
  .shared 123 52 49 ⟨.tilted, 1, 2, true, 210306053292715279⟩,
  .point 124 43 48,
  .point 124 44 48,
  .point 124 45 48], by decide +kernel⟩
private def batch28 : PaidBatch .empty 8 := ⟨[
  .shared 124 46 48 ⟨.tilted, 0, 1, false, 156540615128601250⟩,
  .shared 124 47 48 ⟨.tilted, 0, 1, false, 163143995241874456⟩,
  .shared 124 48 49 ⟨.tilted, 0, 1, false, 169853634457879876⟩,
  .shared 124 49 49 ⟨.tilted, 0, 1, false, 176668090345592386⟩,
  .shared 124 50 49 ⟨.tilted, 0, 2, true, 195945995895713304⟩,
  .shared 124 51 49 ⟨.tilted, 0, 2, true, 203895981786778460⟩], by decide +kernel⟩
private def batch29 : PaidBatch .empty 8 := ⟨[
  .shared 124 52 49 ⟨.tilted, 1, 2, true, 211974940618519470⟩,
  .point 125 43 48,
  .point 125 44 48,
  .point 125 45 48,
  .shared 125 46 48 ⟨.tilted, 0, 1, false, 157747770152028673⟩,
  .shared 125 47 48 ⟨.tilted, 0, 1, false, 164402418906326393⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 8 := ⟨[
  .shared 125 48 49 ⟨.tilted, 0, 1, false, 171164288384039745⟩,
  .shared 125 49 49 ⟨.tilted, 0, 1, false, 178031936154143605⟩,
  .shared 125 50 49 ⟨.tilted, 0, 2, true, 197483995939589062⟩,
  .shared 125 51 49 ⟨.tilted, 0, 2, true, 205498757679477173⟩,
  .shared 125 52 49 ⟨.tilted, 0, 2, true, 213643827944323662⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 8) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 125 24 8 = true := by decide +kernel
theorem index32 : checks tiles 125 32 8 = true := by decide +kernel
theorem index40 : checks tiles 125 40 8 = true := by decide +kernel
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
  .rectangle 9 27 67 39 39,
  .rectangle 14 40 69 52 45,
  .rectangle 68 34 96 39 46,
  .rectangle 68 27 125 30 44,
  .rectangle 68 31 125 33 45,
  .rectangle 70 47 83 52 48], by decide +kernel⟩
private def batch1 : PaidBatch .empty 9 := ⟨[
  .rectangle 70 40 97 43 46,
  .rectangle 70 44 97 46 46,
  .rectangle 84 50 90 52 48,
  .rectangle 84 47 97 49 48,
  .rectangle 91 50 97 51 48,
  .rectangle 91 52 97 52 48], by decide +kernel⟩
private def batch2 : PaidBatch .empty 9 := ⟨[
  .rectangle 97 34 125 36 46,
  .rectangle 97 37 125 39 47,
  .rectangle 98 51 101 51 48,
  .rectangle 98 52 101 52 49,
  .rectangle 98 44 104 46 48,
  .rectangle 98 47 104 48 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 9 := ⟨[
  .rectangle 98 49 104 49 48,
  .rectangle 98 50 104 50 48,
  .rectangle 98 40 111 41 47,
  .rectangle 98 42 111 43 47,
  .point 102 51 48,
  .rectangle 102 52 102 52 49], by decide +kernel⟩
private def batch4 : PaidBatch .empty 9 := ⟨[
  .point 103 51 48,
  .point 103 52 49,
  .point 104 51 48,
  .point 104 52 49,
  .point 105 50 48,
  .point 105 51 49], by decide +kernel⟩
private def batch5 : PaidBatch .empty 9 := ⟨[
  .point 105 52 49,
  .rectangle 105 49 106 49 48,
  .rectangle 105 48 108 48 48,
  .rectangle 105 44 111 45 48,
  .rectangle 105 46 111 46 48,
  .rectangle 105 47 111 47 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 9 := ⟨[
  .point 106 50 48,
  .point 106 51 49,
  .point 106 52 49,
  .point 107 49 48,
  .point 107 50 48,
  .point 107 51 49], by decide +kernel⟩
private def batch7 : PaidBatch .empty 9 := ⟨[
  .point 107 52 49,
  .point 108 49 48,
  .point 108 50 48,
  .point 108 51 49,
  .point 108 52 49,
  .point 109 48 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 9 := ⟨[
  .point 109 49 48,
  .point 109 50 48,
  .point 109 51 49,
  .point 109 52 49,
  .point 110 48 48,
  .point 110 49 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 9 := ⟨[
  .point 110 50 48,
  .point 110 51 49,
  .shared 110 52 49 ⟨.tilted, 1, 2, true, 191376705311646428⟩,
  .point 111 48 48,
  .point 111 49 48,
  .point 111 50 49], by decide +kernel⟩
private def batch10 : PaidBatch .empty 9 := ⟨[
  .point 111 51 49,
  .shared 111 52 49 ⟨.tilted, 1, 2, true, 193045592637450620⟩,
  .point 112 47 48,
  .point 112 48 48,
  .point 112 49 48,
  .point 112 50 49], by decide +kernel⟩
private def batch11 : PaidBatch .empty 9 := ⟨[
  .shared 112 51 49 ⟨.tilted, 1, 1, false, 177955175849552202⟩,
  .shared 112 52 49 ⟨.tilted, 1, 2, true, 194714479963254811⟩,
  .rectangle 112 46 113 46 48,
  .rectangle 112 45 115 45 48,
  .rectangle 112 40 118 41 47,
  .rectangle 112 42 118 43 48], by decide +kernel⟩
private def batch12 : PaidBatch .empty 9 := ⟨[
  .rectangle 112 44 118 44 48,
  .point 113 47 48,
  .point 113 48 48,
  .point 113 49 48,
  .point 113 50 49,
  .shared 113 51 49 ⟨.tilted, 1, 1, false, 179456150569333358⟩], by decide +kernel⟩
private def batch13 : PaidBatch .empty 9 := ⟨[
  .shared 113 52 49 ⟨.tilted, 1, 2, true, 196383367289059003⟩,
  .point 114 46 48,
  .point 114 47 48,
  .point 114 48 48,
  .shared 114 49 48 ⟨.tilted, 1, 1, false, 167543928428959587⟩,
  .shared 114 50 49 ⟨.tilted, 1, 1, false, 174200883182648334⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 9 := ⟨[
  .shared 114 51 49 ⟨.tilted, 1, 2, true, 195988839084515610⟩,
  .shared 114 52 49 ⟨.tilted, 1, 2, true, 198052254614863195⟩,
  .point 115 46 48,
  .point 115 47 48,
  .point 115 48 48,
  .shared 115 49 48 ⟨.tilted, 1, 1, false, 168933390740313148⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 9 := ⟨[
  .shared 115 50 49 ⟨.tilted, 1, 1, false, 175645620887873983⟩,
  .shared 115 51 49 ⟨.tilted, 1, 2, true, 192027410263145935⟩,
  .shared 115 52 49 ⟨.tilted, 1, 2, true, 199721141940667386⟩,
  .rectangle 116 45 116 45 48,
  .point 116 46 48,
  .point 116 47 48], by decide +kernel⟩
private def batch16 : PaidBatch .empty 9 := ⟨[
  .point 116 48 48,
  .point 116 49 49,
  .shared 116 50 49 ⟨.tilted, 1, 1, false, 177090358593099633⟩,
  .shared 116 51 49 ⟨.tilted, 1, 2, true, 193630186155844648⟩,
  .shared 116 52 49 ⟨.tilted, 1, 2, true, 201390029266471578⟩,
  .point 117 45 48], by decide +kernel⟩
private def batch17 : PaidBatch .empty 9 := ⟨[
  .point 117 46 48,
  .point 117 47 48,
  .shared 117 48 48 ⟨.tilted, 0, 1, false, 164993149073568072⟩,
  .shared 117 49 49 ⟨.tilted, 1, 1, false, 171712315363020269⟩,
  .shared 117 50 49 ⟨.tilted, 1, 1, false, 178535096298325282⟩,
  .shared 117 51 49 ⟨.tilted, 1, 2, true, 195232962048543360⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 9 := ⟨[
  .shared 117 52 49 ⟨.tilted, 1, 2, true, 203058916592275770⟩,
  .point 118 45 48,
  .point 118 46 48,
  .point 118 47 48,
  .shared 118 48 48 ⟨.tilted, 0, 1, false, 166328297611732961⟩,
  .shared 118 49 49 ⟨.tilted, 0, 1, false, 173101777674373829⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 9 := ⟨[
  .shared 118 50 49 ⟨.tilted, 1, 1, false, 179979834003550932⟩,
  .shared 118 51 49 ⟨.tilted, 1, 2, true, 196835737941242073⟩,
  .shared 118 52 49 ⟨.tilted, 1, 2, true, 204727803918079961⟩,
  .rectangle 119 44 119 44 48,
  .point 119 45 48,
  .point 119 46 48], by decide +kernel⟩
private def batch20 : PaidBatch .empty 9 := ⟨[
  .point 119 47 48,
  .shared 119 48 48 ⟨.tilted, 0, 1, false, 167663446149897851⟩,
  .shared 119 49 49 ⟨.tilted, 0, 1, false, 174491239985727390⟩,
  .shared 119 50 49 ⟨.tilted, 1, 1, false, 181424571708776581⟩,
  .shared 119 51 49 ⟨.tilted, 1, 2, true, 198438513833940785⟩,
  .shared 119 52 49 ⟨.tilted, 1, 2, true, 206396691243884153⟩], by decide +kernel⟩
private def batch21 : PaidBatch .empty 9 := ⟨[
  .rectangle 119 43 122 43 48,
  .rectangle 119 40 125 41 48,
  .rectangle 119 42 125 42 48,
  .point 120 44 48,
  .point 120 45 48,
  .point 120 46 48], by decide +kernel⟩
private def batch22 : PaidBatch .empty 9 := ⟨[
  .shared 120 47 48 ⟨.tilted, 0, 1, false, 162224429017972727⟩,
  .shared 120 48 48 ⟨.tilted, 0, 1, false, 168998594688062740⟩,
  .shared 120 49 49 ⟨.tilted, 0, 1, false, 175880702297080950⟩,
  .shared 120 50 49 ⟨.tilted, 0, 1, false, 182869309414002231⟩,
  .shared 120 51 49 ⟨.tilted, 1, 2, true, 200041289726639498⟩,
  .shared 120 52 49 ⟨.tilted, 1, 2, true, 208065578569688345⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 9 := ⟨[
  .point 121 44 48,
  .point 121 45 48,
  .point 121 46 48,
  .shared 121 47 48 ⟨.tilted, 0, 1, false, 163506225403632363⟩,
  .shared 121 48 48 ⟨.tilted, 0, 1, false, 170333743226227630⟩,
  .shared 121 49 49 ⟨.tilted, 0, 1, false, 177270164608434511⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 9 := ⟨[
  .shared 121 50 49 ⟨.tilted, 0, 2, true, 193686912153563818⟩,
  .shared 121 51 49 ⟨.tilted, 1, 2, true, 201644065619338210⟩,
  .shared 121 52 49 ⟨.tilted, 1, 2, true, 209734465895492536⟩,
  .point 122 44 48,
  .point 122 45 48,
  .point 122 46 48], by decide +kernel⟩
private def batch25 : PaidBatch .empty 9 := ⟨[
  .shared 122 47 48 ⟨.tilted, 0, 1, false, 164788021789292000⟩,
  .shared 122 48 49 ⟨.tilted, 0, 1, false, 171668891764392519⟩,
  .shared 122 49 49 ⟨.tilted, 0, 1, false, 178659626919788071⟩,
  .shared 122 50 49 ⟨.tilted, 0, 2, true, 195224912197439576⟩,
  .shared 122 51 49 ⟨.tilted, 1, 2, true, 203246841512036923⟩,
  .shared 122 52 49 ⟨.tilted, 1, 2, true, 211403353221296728⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 9 := ⟨[
  .point 123 43 48,
  .point 123 44 48,
  .point 123 45 48,
  .shared 123 46 48 ⟨.tilted, 0, 1, false, 159247865279349442⟩,
  .shared 123 47 48 ⟨.tilted, 0, 1, false, 166069818174951636⟩,
  .shared 123 48 49 ⟨.tilted, 0, 1, false, 173004040302557409⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 9 := ⟨[
  .shared 123 49 49 ⟨.tilted, 0, 1, false, 180049089231141632⟩,
  .shared 123 50 49 ⟨.tilted, 0, 2, true, 196762912241315335⟩,
  .shared 123 51 49 ⟨.tilted, 0, 2, true, 204849617404735635⟩,
  .shared 123 52 49 ⟨.tilted, 1, 2, true, 213072240547100920⟩,
  .point 124 43 48,
  .point 124 44 48], by decide +kernel⟩
private def batch28 : PaidBatch .empty 9 := ⟨[
  .point 124 45 48,
  .shared 124 46 48 ⟨.tilted, 0, 1, false, 160477271133187244⟩,
  .shared 124 47 48 ⟨.tilted, 0, 1, false, 167351614560611273⟩,
  .shared 124 48 49 ⟨.tilted, 0, 1, false, 174339188840722298⟩,
  .shared 124 49 49 ⟨.tilted, 0, 1, false, 181438551542495192⟩,
  .shared 124 50 49 ⟨.tilted, 0, 2, true, 198300912285191093⟩], by decide +kernel⟩
private def batch29 : PaidBatch .empty 9 := ⟨[
  .shared 124 51 49 ⟨.tilted, 0, 2, true, 206452393297434348⟩,
  .shared 124 52 49 ⟨.tilted, 1, 2, true, 214741127872905111⟩,
  .point 125 43 48,
  .point 125 44 48,
  .point 125 45 48,
  .shared 125 46 48 ⟨.tilted, 0, 1, false, 161706676987025045⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 9 := ⟨[
  .shared 125 47 48 ⟨.tilted, 0, 1, false, 168633410946270909⟩,
  .shared 125 48 49 ⟨.tilted, 0, 1, false, 175674337378887188⟩,
  .shared 125 49 49 ⟨.tilted, 0, 1, false, 182828013853848753⟩,
  .shared 125 50 49 ⟨.tilted, 0, 2, true, 199838912329066851⟩,
  .shared 125 51 49 ⟨.tilted, 0, 2, true, 208055169190133060⟩,
  .shared 125 52 49 ⟨.tilted, 0, 2, false, 211902595722983489⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 9) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 125 27 8 = true := by decide +kernel
theorem index35 : checks tiles 125 35 8 = true := by decide +kernel
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
  .rectangle 10 30 67 41 39,
  .rectangle 14 42 69 52 45,
  .rectangle 68 30 96 35 45,
  .rectangle 68 36 96 41 46,
  .rectangle 70 48 83 52 48,
  .rectangle 70 42 97 44 46], by decide +kernel⟩
private def batch1 : PaidBatch .empty 10 := ⟨[
  .rectangle 70 45 97 47 48,
  .rectangle 84 48 97 50 48,
  .rectangle 84 51 97 52 48,
  .rectangle 97 39 111 41 47,
  .rectangle 97 30 125 32 46,
  .rectangle 97 33 125 35 46], by decide +kernel⟩
private def batch2 : PaidBatch .empty 10 := ⟨[
  .rectangle 97 36 125 38 47,
  .rectangle 98 50 101 50 48,
  .rectangle 98 51 101 51 48,
  .rectangle 98 52 101 52 49,
  .rectangle 98 42 104 44 47,
  .rectangle 98 45 104 47 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 10 := ⟨[
  .rectangle 98 48 104 48 48,
  .rectangle 98 49 104 49 48,
  .point 102 51 48,
  .point 102 52 49,
  .rectangle 102 50 103 50 48,
  .point 103 51 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 10 := ⟨[
  .point 103 52 49,
  .point 104 50 48,
  .point 104 51 48,
  .point 104 52 49,
  .rectangle 105 49 105 49 48,
  .point 105 50 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 10 := ⟨[
  .point 105 51 49,
  .point 105 52 49,
  .rectangle 105 47 108 47 48,
  .rectangle 105 48 108 48 48,
  .rectangle 105 42 111 43 47,
  .rectangle 105 44 111 44 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 10 := ⟨[
  .rectangle 105 45 111 45 48,
  .rectangle 105 46 111 46 48,
  .point 106 49 48,
  .point 106 50 48,
  .point 106 51 49,
  .point 106 52 49], by decide +kernel⟩
private def batch7 : PaidBatch .empty 10 := ⟨[
  .point 107 49 48,
  .point 107 50 48,
  .point 107 51 49,
  .point 107 52 49,
  .point 108 49 48,
  .point 108 50 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 10 := ⟨[
  .point 108 51 49,
  .point 108 52 49,
  .point 109 48 48,
  .point 109 49 48,
  .point 109 50 48,
  .point 109 51 49], by decide +kernel⟩
private def batch9 : PaidBatch .empty 10 := ⟨[
  .shared 109 52 49 ⟨.tilted, 1, 2, true, 202511204788214090⟩,
  .rectangle 109 47 110 47 48,
  .point 110 48 48,
  .point 110 49 48,
  .point 110 50 48,
  .point 110 51 49], by decide +kernel⟩
private def batch10 : PaidBatch .empty 10 := ⟨[
  .shared 110 52 49 ⟨.tilted, 1, 2, true, 193538407202497774⟩,
  .point 111 47 48,
  .point 111 48 48,
  .point 111 49 48,
  .point 111 50 49,
  .shared 111 51 49 ⟨.tilted, 1, 1, false, 180596830944543180⟩], by decide +kernel⟩
private def batch11 : PaidBatch .empty 10 := ⟨[
  .shared 111 52 49 ⟨.tilted, 1, 2, true, 195207294528301965⟩,
  .point 112 47 48,
  .point 112 48 48,
  .point 112 49 48,
  .point 112 50 49,
  .shared 112 51 49 ⟨.tilted, 1, 1, false, 182122300276329357⟩], by decide +kernel⟩
private def batch12 : PaidBatch .empty 10 := ⟨[
  .shared 112 52 49 ⟨.tilted, 1, 2, true, 196876181854106157⟩,
  .rectangle 112 46 113 46 48,
  .rectangle 112 45 115 45 48,
  .rectangle 112 42 118 43 48,
  .rectangle 112 44 118 44 48,
  .rectangle 112 39 125 40 47], by decide +kernel⟩
private def batch13 : PaidBatch .empty 10 := ⟨[
  .rectangle 112 41 125 41 48,
  .point 113 47 48,
  .point 113 48 48,
  .point 113 49 48,
  .point 113 50 49,
  .shared 113 51 49 ⟨.tilted, 1, 1, false, 183647769608115534⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 10 := ⟨[
  .shared 113 52 49 ⟨.tilted, 1, 2, true, 198545069179910349⟩,
  .point 114 46 48,
  .point 114 47 48,
  .point 114 48 48,
  .shared 114 49 48 ⟨.tilted, 1, 1, false, 171235825299031417⟩,
  .shared 114 50 49 ⟨.tilted, 1, 1, false, 178151402568100456⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 10 := ⟨[
  .shared 114 51 49 ⟨.tilted, 1, 2, true, 204023444563930005⟩,
  .shared 114 52 49 ⟨.tilted, 1, 2, true, 200213956505714540⟩,
  .point 115 46 48,
  .point 115 47 48,
  .point 115 48 48,
  .shared 115 49 48 ⟨.tilted, 1, 1, false, 172647538440795356⟩], by decide +kernel⟩
private def batch16 : PaidBatch .empty 10 := ⟨[
  .shared 115 50 49 ⟨.tilted, 1, 1, false, 179619512994533805⟩,
  .shared 115 51 49 ⟨.tilted, 1, 2, true, 194004178277922493⟩,
  .shared 115 52 49 ⟨.tilted, 1, 2, true, 201882843831518732⟩,
  .rectangle 116 45 116 45 48,
  .point 116 46 48,
  .point 116 47 48], by decide +kernel⟩
private def batch17 : PaidBatch .empty 10 := ⟨[
  .shared 116 48 48 ⟨.tilted, 0, 1, false, 167140504519275614⟩,
  .shared 116 49 49 ⟨.tilted, 1, 1, false, 174059251582559295⟩,
  .shared 116 50 49 ⟨.tilted, 1, 1, false, 181087623420967154⟩,
  .shared 116 51 49 ⟨.tilted, 1, 2, true, 195606954170621205⟩,
  .shared 116 52 49 ⟨.tilted, 1, 2, true, 203551731157322924⟩,
  .point 117 45 48], by decide +kernel⟩
private def batch18 : PaidBatch .empty 10 := ⟨[
  .point 117 46 48,
  .point 117 47 48,
  .shared 117 48 48 ⟨.tilted, 0, 1, false, 168496781997053561⟩,
  .shared 117 49 49 ⟨.tilted, 1, 1, false, 175470964724323234⟩,
  .shared 117 50 49 ⟨.tilted, 1, 1, false, 182555733847400503⟩,
  .shared 117 51 49 ⟨.tilted, 1, 2, true, 197209730063319918⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 10 := ⟨[
  .shared 117 52 49 ⟨.tilted, 1, 2, true, 205220618483127115⟩,
  .point 118 45 48,
  .point 118 46 48,
  .point 118 47 48,
  .shared 118 48 48 ⟨.tilted, 0, 1, false, 169853059474831508⟩,
  .shared 118 49 49 ⟨.tilted, 0, 1, false, 176882677866087173⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 10 := ⟨[
  .shared 118 50 49 ⟨.tilted, 1, 1, false, 184023844273833852⟩,
  .shared 118 51 49 ⟨.tilted, 1, 2, true, 198812505956018630⟩,
  .shared 118 52 49 ⟨.tilted, 1, 2, false, 198635051414699746⟩,
  .rectangle 119 44 119 44 48,
  .point 119 45 48,
  .point 119 46 48], by decide +kernel⟩
private def batch21 : PaidBatch .empty 10 := ⟨[
  .shared 119 47 48 ⟨.tilted, 0, 1, false, 164238234965567358⟩,
  .shared 119 48 48 ⟨.tilted, 0, 1, false, 171209336952609455⟩,
  .shared 119 49 49 ⟨.tilted, 0, 1, false, 178294391007851112⟩,
  .shared 119 50 49 ⟨.tilted, 1, 1, false, 185491954700267201⟩,
  .shared 119 51 49 ⟨.tilted, 1, 2, true, 200415281848717343⟩,
  .shared 119 52 49 ⟨.tilted, 1, 2, false, 200218841272522169⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 10 := ⟨[
  .rectangle 119 43 122 43 48,
  .rectangle 119 42 125 42 48,
  .point 120 44 48,
  .point 120 45 48,
  .point 120 46 48,
  .shared 120 47 48 ⟨.tilted, 0, 1, false, 165540038400042731⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 10 := ⟨[
  .shared 120 48 48 ⟨.tilted, 0, 1, false, 172565614430387402⟩,
  .shared 120 49 49 ⟨.tilted, 0, 1, false, 179706104149615051⟩,
  .shared 120 50 49 ⟨.tilted, 0, 1, false, 186960065126700550⟩,
  .shared 120 51 49 ⟨.tilted, 1, 2, true, 202018057741416055⟩,
  .shared 120 52 49 ⟨.tilted, 1, 2, false, 201802631130344592⟩,
  .point 121 44 48], by decide +kernel⟩
private def batch24 : PaidBatch .empty 10 := ⟨[
  .point 121 45 48,
  .point 121 46 48,
  .shared 121 47 48 ⟨.tilted, 0, 1, false, 166841841834518104⟩,
  .shared 121 48 48 ⟨.tilted, 0, 1, false, 173921891908165349⟩,
  .shared 121 49 49 ⟨.tilted, 0, 1, false, 181117817291378990⟩,
  .shared 121 50 49 ⟨.tilted, 0, 2, true, 195487026914817242⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 10 := ⟨[
  .shared 121 51 49 ⟨.tilted, 1, 2, true, 203620833634114768⟩,
  .shared 121 52 49 ⟨.tilted, 1, 2, false, 203386420988167015⟩,
  .point 122 44 48,
  .point 122 45 48,
  .shared 122 46 48 ⟨.tilted, 0, 1, false, 161127400513318598⟩,
  .shared 122 47 48 ⟨.tilted, 0, 1, false, 168143645268993477⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 10 := ⟨[
  .shared 122 48 49 ⟨.tilted, 0, 1, false, 175278169385943296⟩,
  .shared 122 49 49 ⟨.tilted, 0, 1, false, 182529530433142929⟩,
  .shared 122 50 49 ⟨.tilted, 0, 2, true, 197025026958693000⟩,
  .shared 122 51 49 ⟨.tilted, 1, 2, false, 198034184505028383⟩,
  .shared 122 52 49 ⟨.tilted, 1, 2, false, 204970210845989438⟩,
  .point 123 43 48], by decide +kernel⟩
private def batch27 : PaidBatch .empty 10 := ⟨[
  .point 123 44 48,
  .point 123 45 48,
  .shared 123 46 48 ⟨.tilted, 0, 1, false, 162375691525174815⟩,
  .shared 123 47 48 ⟨.tilted, 0, 1, false, 169445448703468850⟩,
  .shared 123 48 49 ⟨.tilted, 0, 1, false, 176634446863721243⟩,
  .shared 123 49 49 ⟨.tilted, 0, 1, false, 183941243574906868⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 10 := ⟨[
  .shared 123 50 49 ⟨.tilted, 0, 2, true, 198563027002568759⟩,
  .shared 123 51 49 ⟨.tilted, 0, 2, false, 198902462925977304⟩,
  .shared 123 52 49 ⟨.tilted, 1, 2, false, 206554000703811861⟩,
  .point 124 43 48,
  .point 124 44 48,
  .point 124 45 48], by decide +kernel⟩
private def batch29 : PaidBatch .empty 10 := ⟨[
  .shared 124 46 48 ⟨.tilted, 0, 1, false, 163623982537031032⟩,
  .shared 124 47 48 ⟨.tilted, 0, 1, false, 170747252137944223⟩,
  .shared 124 48 49 ⟨.tilted, 0, 1, false, 177990724341499190⟩,
  .shared 124 49 49 ⟨.tilted, 0, 1, false, 185352956716670807⟩,
  .shared 124 50 49 ⟨.tilted, 0, 2, true, 200101027046444517⟩,
  .shared 124 51 49 ⟨.tilted, 0, 2, false, 200427932257763481⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 10 := ⟨[
  .shared 124 52 49 ⟨.tilted, 1, 2, false, 208137790561634284⟩,
  .point 125 43 48,
  .point 125 44 48,
  .point 125 45 48,
  .shared 125 46 48 ⟨.tilted, 0, 1, false, 164872273548887249⟩,
  .shared 125 47 48 ⟨.tilted, 0, 1, false, 172049055572419596⟩], by decide +kernel⟩
private def batch31 : PaidBatch .empty 10 := ⟨[
  .shared 125 48 49 ⟨.tilted, 0, 1, false, 179347001819277137⟩,
  .shared 125 49 49 ⟨.tilted, 0, 1, false, 186764669858434746⟩,
  .shared 125 50 49 ⟨.tilted, 0, 2, true, 201639027090320275⟩,
  .shared 125 51 49 ⟨.tilted, 0, 2, false, 201953401589549658⟩,
  .shared 125 52 49 ⟨.tilted, 0, 2, false, 209721580419456707⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 10) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 125 30 8 = true := by decide +kernel
private theorem index38 : checks tiles 125 38 8 = true := by decide +kernel
theorem index46 : checks tiles 125 46 7 = true := by decide +kernel
private theorem covers : checks tiles 125 30 23 = true :=
  checks_join index30 (checks_join index38 index46)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 10 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

end Compact50PriceTableEmpty8
