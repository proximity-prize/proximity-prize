import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableEmpty13
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top13

private def batch0 : PaidBatch .empty 13 := ⟨[
  .rectangle 13 39 69 45 34,
  .rectangle 16 46 69 52 39,
  .rectangle 70 46 83 49 41,
  .rectangle 70 50 83 52 42,
  .rectangle 70 39 97 42 40,
  .rectangle 70 43 97 45 42], by decide +kernel⟩
private def batch1 : PaidBatch .empty 13 := ⟨[
  .rectangle 84 50 90 52 46,
  .rectangle 84 46 97 49 47,
  .rectangle 91 50 97 51 47,
  .rectangle 91 52 97 52 47,
  .rectangle 98 51 99 51 47,
  .rectangle 98 52 99 52 48], by decide +kernel⟩
private def batch2 : PaidBatch .empty 13 := ⟨[
  .rectangle 98 50 101 50 47,
  .rectangle 98 43 104 45 45,
  .rectangle 98 46 104 47 46,
  .rectangle 98 48 104 48 46,
  .rectangle 98 49 104 49 47,
  .rectangle 98 41 111 42 43], by decide +kernel⟩
private def batch3 : PaidBatch .empty 13 := ⟨[
  .rectangle 98 39 125 40 46,
  .rectangle 100 51 100 51 47,
  .rectangle 100 52 100 52 48,
  .point 101 51 45,
  .point 101 52 46,
  .point 102 51 45], by decide +kernel⟩
private def batch4 : PaidBatch .empty 13 := ⟨[
  .point 102 52 46,
  .rectangle 102 50 103 50 47,
  .point 103 51 46,
  .point 103 52 47,
  .point 104 50 45,
  .point 104 51 46], by decide +kernel⟩
private def batch5 : PaidBatch .empty 13 := ⟨[
  .point 104 52 47,
  .rectangle 105 49 105 49 47,
  .point 105 50 45,
  .point 105 51 46,
  .point 105 52 48,
  .rectangle 105 47 108 47 46], by decide +kernel⟩
private def batch6 : PaidBatch .empty 13 := ⟨[
  .rectangle 105 48 108 48 47,
  .rectangle 105 43 111 45 47,
  .rectangle 105 46 111 46 46,
  .point 106 49 45,
  .point 106 50 46,
  .point 106 51 47], by decide +kernel⟩
private def batch7 : PaidBatch .empty 13 := ⟨[
  .point 106 52 48,
  .point 107 49 45,
  .point 107 50 46,
  .point 107 51 47,
  .point 107 52 48,
  .point 108 49 46], by decide +kernel⟩
private def batch8 : PaidBatch .empty 13 := ⟨[
  .point 108 50 47,
  .point 108 51 48,
  .shared 108 52 48 ⟨.tilted, 2, 2, false, 206574875935367892⟩,
  .point 109 48 45,
  .point 109 49 46,
  .point 109 50 47], by decide +kernel⟩
private def batch9 : PaidBatch .empty 13 := ⟨[
  .point 109 51 48,
  .shared 109 52 48 ⟨.tilted, 2, 2, false, 200816842930664633⟩,
  .rectangle 109 47 110 47 47,
  .point 110 48 45,
  .point 110 49 46,
  .point 110 50 47], by decide +kernel⟩
private def batch10 : PaidBatch .empty 13 := ⟨[
  .shared 110 51 48 ⟨.tilted, 2, 1, false, 187078152614914046⟩,
  .shared 110 52 48 ⟨.tilted, 2, 2, false, 195058809925961375⟩,
  .point 111 47 45,
  .point 111 48 46,
  .point 111 49 47,
  .point 111 50 48], by decide +kernel⟩
private def batch11 : PaidBatch .empty 13 := ⟨[
  .shared 111 51 48 ⟨.tilted, 2, 1, false, 188657550671290585⟩,
  .shared 111 52 48 ⟨.tilted, 2, 2, false, 196287706992350394⟩,
  .point 112 47 45,
  .point 112 48 46,
  .point 112 49 47,
  .point 112 50 48], by decide +kernel⟩
private def batch12 : PaidBatch .empty 13 := ⟨[
  .shared 112 51 48 ⟨.tilted, 2, 2, false, 204725504858511833⟩,
  .shared 112 52 48 ⟨.tilted, 2, 2, false, 197928816211526699⟩,
  .rectangle 112 46 113 46 47,
  .rectangle 112 45 115 45 47,
  .rectangle 112 41 118 42 46,
  .rectangle 112 43 118 43 46], by decide +kernel⟩
private def batch13 : PaidBatch .empty 13 := ⟨[
  .rectangle 112 44 118 44 47,
  .point 113 47 45,
  .point 113 48 46,
  .shared 113 49 47 ⟨.tilted, 2, 1, false, 176685094891592390⟩,
  .shared 113 50 48 ⟨.tilted, 2, 1, false, 184187588932748040⟩,
  .shared 113 51 48 ⟨.tilted, 2, 2, false, 199675796428186537⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 13 := ⟨[
  .shared 113 52 48 ⟨.tilted, 2, 2, false, 199569925430703005⟩,
  .point 114 46 45,
  .point 114 47 46,
  .point 114 48 47,
  .shared 114 49 47 ⟨.tilted, 2, 1, false, 178143956651921897⟩,
  .shared 114 50 48 ⟨.tilted, 2, 1, false, 185706237836175646⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 13 := ⟨[
  .shared 114 51 48 ⟨.tilted, 2, 2, false, 194626087997861240⟩,
  .shared 114 52 48 ⟨.tilted, 2, 2, false, 201211034649879310⟩,
  .point 115 46 45,
  .point 115 47 46,
  .point 115 48 47,
  .shared 115 49 47 ⟨.tilted, 2, 1, false, 179602818412251403⟩], by decide +kernel⟩
private def batch16 : PaidBatch .empty 13 := ⟨[
  .shared 115 50 48 ⟨.tilted, 2, 1, false, 187224886739603251⟩,
  .shared 115 51 48 ⟨.tilted, 2, 2, false, 194975142896796739⟩,
  .shared 115 52 48 ⟨.tilted, 2, 2, false, 202852143869055616⟩,
  .rectangle 116 45 116 45 47,
  .point 116 46 45,
  .point 116 47 46], by decide +kernel⟩
private def batch17 : PaidBatch .empty 13 := ⟨[
  .shared 116 48 47 ⟨.tilted, 2, 1, false, 173510417556599688⟩,
  .shared 116 49 48 ⟨.tilted, 2, 1, false, 181061680172580910⟩,
  .shared 116 50 48 ⟨.tilted, 2, 2, false, 207115508243511537⟩,
  .shared 116 51 48 ⟨.tilted, 2, 2, false, 196554540953173277⟩,
  .shared 116 52 48 ⟨.tilted, 2, 2, false, 204493253088231921⟩,
  .point 117 45 45], by decide +kernel⟩
private def batch18 : PaidBatch .empty 13 := ⟨[
  .point 117 46 46,
  .point 117 47 47,
  .shared 117 48 47 ⟨.tilted, 2, 1, false, 174910454183681930⟩,
  .shared 117 49 48 ⟨.tilted, 2, 1, false, 182520541932910416⟩,
  .shared 117 50 48 ⟨.tilted, 2, 2, false, 202737888671971063⟩,
  .shared 117 51 48 ⟨.tilted, 2, 2, false, 198133939009549816⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 13 := ⟨[
  .shared 117 52 48 ⟨.tilted, 2, 2, false, 206134362307408227⟩,
  .point 118 45 45,
  .point 118 46 46,
  .point 118 47 47,
  .shared 118 48 47 ⟨.tilted, 2, 1, false, 176310490810764171⟩,
  .shared 118 49 48 ⟨.tilted, 2, 1, false, 183979403693239923⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 13 := ⟨[
  .shared 118 50 48 ⟨.tilted, 2, 2, false, 198360269100430588⟩,
  .shared 118 51 48 ⟨.tilted, 2, 2, false, 199713337065926354⟩,
  .shared 118 52 48 ⟨.tilted, 2, 2, false, 207775471526584532⟩,
  .rectangle 119 44 119 44 47,
  .point 119 45 45,
  .point 119 46 46], by decide +kernel⟩
private def batch21 : PaidBatch .empty 13 := ⟨[
  .shared 119 47 47 ⟨.tilted, 2, 1, false, 170117711320920874⟩,
  .shared 119 48 47 ⟨.tilted, 2, 1, false, 177710527437846413⟩,
  .shared 119 49 48 ⟨.tilted, 2, 1, false, 185438265453569429⟩,
  .shared 119 50 48 ⟨.tilted, 2, 2, false, 193982649528890114⟩,
  .shared 119 51 48 ⟨.tilted, 2, 2, false, 201292735122302893⟩,
  .shared 119 52 48 ⟨.tilted, 2, 2, false, 209416580745760838⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 13 := ⟨[
  .rectangle 119 43 122 43 47,
  .rectangle 119 41 125 41 46,
  .rectangle 119 42 125 42 47,
  .point 120 44 44,
  .point 120 45 46,
  .point 120 46 47], by decide +kernel⟩
private def batch23 : PaidBatch .empty 13 := ⟨[
  .shared 120 47 47 ⟨.tilted, 2, 1, false, 171459884824606684⟩,
  .shared 120 48 47 ⟨.tilted, 2, 1, false, 179110564064928654⟩,
  .shared 120 49 48 ⟨.tilted, 2, 1, false, 186897127213898936⟩,
  .shared 120 50 48 ⟨.tilted, 2, 2, false, 194818131256741279⟩,
  .shared 120 51 48 ⟨.tilted, 2, 2, false, 202872133178679431⟩,
  .shared 120 52 48 ⟨.tilted, 2, 2, false, 211057689964937143⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 13 := ⟨[
  .point 121 44 45,
  .point 121 45 46,
  .point 121 46 47,
  .shared 121 47 47 ⟨.tilted, 2, 1, false, 172802058328292495⟩,
  .shared 121 48 47 ⟨.tilted, 2, 1, false, 180510600692010896⟩,
  .shared 121 49 48 ⟨.tilted, 2, 1, false, 188355988974228442⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 13 := ⟨[
  .shared 121 50 48 ⟨.tilted, 2, 2, false, 196336780160168884⟩,
  .shared 121 51 48 ⟨.tilted, 2, 2, false, 204451531235055970⟩,
  .shared 121 52 48 ⟨.tilted, 2, 2, false, 212698799184113449⟩,
  .point 122 44 45,
  .point 122 45 46,
  .shared 122 46 47 ⟨.tilted, 2, 1, false, 166517077287989705⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 13 := ⟨[
  .shared 122 47 47 ⟨.tilted, 2, 1, false, 174144231831978305⟩,
  .shared 122 48 48 ⟨.tilted, 2, 1, false, 181910637319093137⟩,
  .shared 122 49 48 ⟨.tilted, 2, 2, false, 205772171073162028⟩,
  .shared 122 50 48 ⟨.tilted, 2, 2, false, 197855429063596490⟩,
  .shared 122 51 48 ⟨.tilted, 2, 2, false, 206030929291432508⟩,
  .shared 122 52 48 ⟨.tilted, 2, 2, false, 214339908403289754⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 13 := ⟨[
  .rectangle 123 43 123 43 47,
  .point 123 44 46,
  .point 123 45 47,
  .shared 123 46 47 ⟨.tilted, 2, 1, false, 167802349678129918⟩,
  .shared 123 47 47 ⟨.tilted, 2, 1, false, 175486405335664116⟩,
  .shared 123 48 48 ⟨.tilted, 2, 1, false, 183310673946175379⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 13 := ⟨[
  .shared 123 49 48 ⟨.tilted, 2, 2, false, 202030404644813235⟩,
  .shared 123 50 48 ⟨.tilted, 2, 2, false, 199374077967024095⟩,
  .shared 123 51 48 ⟨.tilted, 2, 2, false, 207610327347809047⟩,
  .shared 123 52 48 ⟨.tilted, 2, 2, false, 215981017622466060⟩,
  .point 124 43 45,
  .point 124 44 46], by decide +kernel⟩
private def batch29 : PaidBatch .empty 13 := ⟨[
  .point 124 45 47,
  .shared 124 46 47 ⟨.tilted, 2, 1, false, 169087622068270132⟩,
  .shared 124 47 47 ⟨.tilted, 2, 1, false, 176828578839349926⟩,
  .shared 124 48 48 ⟨.tilted, 2, 1, false, 184710710573257620⟩,
  .shared 124 49 48 ⟨.tilted, 2, 2, false, 198288638216464443⟩,
  .shared 124 50 48 ⟨.tilted, 2, 2, false, 200892726870451701⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 13 := ⟨[
  .shared 124 51 48 ⟨.tilted, 2, 2, false, 209189725404185585⟩,
  .shared 124 52 48 ⟨.tilted, 2, 2, false, 217622126841642365⟩,
  .point 125 43 45,
  .point 125 44 46,
  .point 125 45 47,
  .shared 125 46 47 ⟨.tilted, 2, 1, false, 170372894458410345⟩], by decide +kernel⟩
private def batch31 : PaidBatch .empty 13 := ⟨[
  .shared 125 47 47 ⟨.tilted, 2, 1, false, 178170752343035737⟩,
  .shared 125 48 48 ⟨.tilted, 2, 1, false, 186110747200339862⟩,
  .shared 125 49 48 ⟨.tilted, 2, 2, false, 195463338115630171⟩,
  .shared 125 50 48 ⟨.tilted, 2, 2, false, 202411375773879306⟩,
  .shared 125 51 48 ⟨.tilted, 2, 2, false, 210769123460562124⟩,
  .shared 125 52 48 ⟨.tilted, 2, 2, false, 219263236060818671⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 13) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31]
private abbrev tiles := tilesOf batches

private theorem index39 : checks tiles 125 39 8 = true := by decide +kernel
private theorem index47 : checks tiles 125 47 6 = true := by decide +kernel
private theorem covers : checks tiles 125 39 14 = true :=
  checks_join index39 index47

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 13)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 13 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top13

namespace Top14

private def batch0 : PaidBatch .empty 14 := ⟨[
  .rectangle 14 42 69 52 43,
  .rectangle 70 48 83 52 44,
  .rectangle 70 42 97 44 41,
  .rectangle 70 45 97 47 44,
  .rectangle 84 51 90 52 45,
  .rectangle 84 48 97 50 47], by decide +kernel⟩
private def batch1 : PaidBatch .empty 14 := ⟨[
  .rectangle 91 51 97 51 46,
  .rectangle 91 52 97 52 47,
  .rectangle 98 51 99 51 47,
  .rectangle 98 52 99 52 48,
  .rectangle 98 50 101 50 47,
  .rectangle 98 45 104 47 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 14 := ⟨[
  .rectangle 98 48 104 48 46,
  .rectangle 98 49 104 49 47,
  .rectangle 98 42 111 44 46,
  .rectangle 100 51 100 51 47,
  .rectangle 100 52 100 52 48,
  .point 101 51 45], by decide +kernel⟩
private def batch3 : PaidBatch .empty 14 := ⟨[
  .point 101 52 46,
  .point 102 51 45,
  .point 102 52 46,
  .rectangle 102 50 103 50 47,
  .point 103 51 46,
  .point 103 52 47], by decide +kernel⟩
private def batch4 : PaidBatch .empty 14 := ⟨[
  .point 104 50 45,
  .point 104 51 46,
  .point 104 52 47,
  .rectangle 105 49 105 49 47,
  .point 105 50 45,
  .point 105 51 46], by decide +kernel⟩
private def batch5 : PaidBatch .empty 14 := ⟨[
  .point 105 52 48,
  .rectangle 105 48 108 48 47,
  .rectangle 105 45 111 46 47,
  .rectangle 105 47 111 47 47,
  .point 106 49 45,
  .point 106 50 46], by decide +kernel⟩
private def batch6 : PaidBatch .empty 14 := ⟨[
  .point 106 51 47,
  .point 106 52 48,
  .point 107 49 45,
  .point 107 50 46,
  .point 107 51 47,
  .point 107 52 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 14 := ⟨[
  .point 108 49 46,
  .point 108 50 47,
  .point 108 51 48,
  .shared 108 52 48 ⟨.tilted, 2, 2, false, 199479635723667160⟩,
  .point 109 48 45,
  .point 109 49 46], by decide +kernel⟩
private def batch8 : PaidBatch .empty 14 := ⟨[
  .point 109 50 47,
  .point 109 51 48,
  .shared 109 52 48 ⟨.tilted, 2, 2, false, 197389187030324995⟩,
  .point 110 48 45,
  .point 110 49 46,
  .point 110 50 47], by decide +kernel⟩
private def batch9 : PaidBatch .empty 14 := ⟨[
  .shared 110 51 48 ⟨.tilted, 2, 2, false, 201922214179356788⟩,
  .shared 110 52 48 ⟨.tilted, 2, 2, false, 196228029992974174⟩,
  .point 111 48 46,
  .point 111 49 47,
  .point 111 50 48,
  .shared 111 51 48 ⟨.tilted, 2, 2, false, 200167417980084395⟩], by decide +kernel⟩
private def batch10 : PaidBatch .empty 14 := ⟨[
  .shared 111 52 48 ⟨.tilted, 2, 2, false, 197881297944027943⟩,
  .point 112 47 45,
  .point 112 48 46,
  .point 112 49 47,
  .point 112 50 48,
  .shared 112 51 48 ⟨.tilted, 2, 2, false, 198412621780812003⟩], by decide +kernel⟩
private def batch11 : PaidBatch .empty 14 := ⟨[
  .shared 112 52 48 ⟨.tilted, 2, 2, false, 199534565895081712⟩,
  .rectangle 112 46 113 46 47,
  .rectangle 112 45 115 45 47,
  .rectangle 112 42 118 43 47,
  .rectangle 112 44 118 44 47,
  .point 113 47 45], by decide +kernel⟩
private def batch12 : PaidBatch .empty 14 := ⟨[
  .point 113 48 46,
  .shared 113 49 47 ⟨.tilted, 2, 1, false, 177773817796857370⟩,
  .shared 113 50 48 ⟨.tilted, 2, 1, false, 185445732436650305⟩,
  .shared 113 51 48 ⟨.tilted, 2, 2, false, 196657825581539610⟩,
  .shared 113 52 48 ⟨.tilted, 2, 2, false, 201187833846135481⟩,
  .point 114 46 45], by decide +kernel⟩
private def batch13 : PaidBatch .empty 14 := ⟨[
  .point 114 47 46,
  .point 114 48 47,
  .shared 114 49 47 ⟨.tilted, 2, 1, false, 179241471254586421⟩,
  .shared 114 50 48 ⟨.tilted, 2, 2, false, 202139430568094316⟩,
  .shared 114 51 48 ⟨.tilted, 2, 2, false, 194903029382267218⟩,
  .shared 114 52 48 ⟨.tilted, 2, 2, false, 202841101797189250⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 14 := ⟨[
  .point 115 46 45,
  .point 115 47 46,
  .point 115 48 47,
  .shared 115 49 47 ⟨.tilted, 2, 1, false, 180709124712315472⟩,
  .shared 115 50 48 ⟨.tilted, 2, 2, false, 200700725990318875⟩,
  .shared 115 51 48 ⟨.tilted, 2, 2, false, 196431754344857818⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 14 := ⟨[
  .shared 115 52 48 ⟨.tilted, 2, 2, false, 204494369748243019⟩,
  .rectangle 116 45 116 45 47,
  .point 116 46 45,
  .point 116 47 46,
  .shared 116 48 47 ⟨.tilted, 2, 1, false, 174459702492366642⟩,
  .shared 116 49 48 ⟨.tilted, 2, 1, false, 182176778170044523⟩], by decide +kernel⟩
private def batch16 : PaidBatch .empty 14 := ⟨[
  .shared 116 50 48 ⟨.tilted, 2, 2, false, 199262021412543434⟩,
  .shared 116 51 48 ⟨.tilted, 2, 2, false, 198022188788285847⟩,
  .shared 116 52 48 ⟨.tilted, 2, 2, false, 206147637699296788⟩,
  .point 117 45 44,
  .point 117 46 46,
  .point 117 47 47], by decide +kernel⟩
private def batch17 : PaidBatch .empty 14 := ⟨[
  .shared 117 48 47 ⟨.tilted, 2, 1, false, 175867408472022455⟩,
  .shared 117 49 48 ⟨.tilted, 2, 1, false, 183644431627773574⟩,
  .shared 117 50 48 ⟨.tilted, 2, 2, false, 197823316834767993⟩,
  .shared 117 51 48 ⟨.tilted, 2, 2, false, 199612623231713876⟩,
  .shared 117 52 48 ⟨.tilted, 2, 2, false, 207800905650350557⟩,
  .point 118 45 45], by decide +kernel⟩
private def batch18 : PaidBatch .empty 14 := ⟨[
  .point 118 46 46,
  .point 118 47 47,
  .shared 118 48 47 ⟨.tilted, 2, 1, false, 177275114451678268⟩,
  .shared 118 49 48 ⟨.tilted, 2, 1, false, 185112085085502625⟩,
  .shared 118 50 48 ⟨.tilted, 2, 2, false, 196384612256992552⟩,
  .shared 118 51 48 ⟨.tilted, 2, 2, false, 201203057675141905⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 14 := ⟨[
  .shared 118 52 48 ⟨.tilted, 2, 2, false, 209454173601404326⟩,
  .point 119 45 45,
  .point 119 46 46,
  .shared 119 47 47 ⟨.tilted, 2, 1, false, 170927798789652512⟩,
  .shared 119 48 47 ⟨.tilted, 2, 1, false, 178682820431334081⟩,
  .shared 119 49 48 ⟨.tilted, 2, 2, false, 202905936667979682⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 14 := ⟨[
  .shared 119 50 48 ⟨.tilted, 2, 2, false, 194945907679217111⟩,
  .shared 119 51 48 ⟨.tilted, 2, 2, false, 202793492118569934⟩,
  .shared 119 52 48 ⟨.tilted, 2, 2, false, 211107441552458095⟩,
  .rectangle 119 44 120 44 47,
  .rectangle 119 43 122 43 47,
  .rectangle 119 42 125 42 47], by decide +kernel⟩
private def batch21 : PaidBatch .empty 14 := ⟨[
  .point 120 45 46,
  .point 120 46 47,
  .shared 120 47 47 ⟨.tilted, 2, 1, false, 172276519301085921⟩,
  .shared 120 48 47 ⟨.tilted, 2, 1, false, 180090526410989894⟩,
  .shared 120 49 48 ⟨.tilted, 2, 2, false, 201763762839128371⟩,
  .shared 120 50 48 ⟨.tilted, 2, 2, false, 196145673056222166⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 14 := ⟨[
  .shared 120 51 48 ⟨.tilted, 2, 2, false, 204383926561997963⟩,
  .shared 120 52 48 ⟨.tilted, 2, 2, false, 212760709503511864⟩,
  .shared 121 44 47 ⟨.ordinary, 2, 1, false, 204714992083375675⟩,
  .point 121 45 46,
  .point 121 46 47,
  .shared 121 47 47 ⟨.tilted, 2, 1, false, 173625239812519330⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 14 := ⟨[
  .shared 121 48 47 ⟨.tilted, 2, 1, false, 181498232390645707⟩,
  .shared 121 49 48 ⟨.tilted, 2, 2, false, 200621589010277061⟩,
  .shared 121 50 48 ⟨.tilted, 2, 2, false, 197674236001875289⟩,
  .shared 121 51 48 ⟨.tilted, 2, 2, false, 205974361005425992⟩,
  .shared 121 52 48 ⟨.tilted, 2, 2, false, 214413977454565633⟩,
  .shared 122 44 47 ⟨.ordinary, 2, 1, false, 206310392674571810⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 14 := ⟨[
  .point 122 45 46,
  .point 122 46 47,
  .shared 122 47 47 ⟨.tilted, 2, 1, false, 174973960323952739⟩,
  .shared 122 48 48 ⟨.tilted, 2, 1, false, 182905938370301520⟩,
  .shared 122 49 48 ⟨.tilted, 2, 2, false, 199479415181425750⟩,
  .shared 122 50 48 ⟨.tilted, 2, 2, false, 199202798947528412⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 14 := ⟨[
  .shared 122 51 48 ⟨.tilted, 2, 2, false, 207564795448854021⟩,
  .shared 122 52 48 ⟨.tilted, 2, 2, false, 216067245405619402⟩,
  .rectangle 123 43 123 43 47,
  .shared 123 44 47 ⟨.ordinary, 2, 1, false, 207905793265767945⟩,
  .point 123 45 47,
  .shared 123 46 47 ⟨.tilted, 2, 1, false, 168478904845210573⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 14 := ⟨[
  .shared 123 47 47 ⟨.tilted, 2, 1, false, 176322680835386148⟩,
  .shared 123 48 48 ⟨.tilted, 2, 1, false, 184313644349957333⟩,
  .shared 123 49 48 ⟨.tilted, 2, 2, false, 198337241352574440⟩,
  .shared 123 50 48 ⟨.tilted, 2, 2, false, 200731361893181535⟩,
  .shared 123 51 48 ⟨.tilted, 2, 2, false, 209155229892282050⟩,
  .shared 123 52 48 ⟨.tilted, 2, 2, false, 217720513356673171⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 14 := ⟨[
  .shared 124 43 47 ⟨.ordinary, 2, 1, false, 199472940729877738⟩,
  .shared 124 44 47 ⟨.ordinary, 2, 1, false, 209501193856964080⟩,
  .point 124 45 47,
  .shared 124 46 47 ⟨.tilted, 2, 1, false, 169769601898272412⟩,
  .shared 124 47 47 ⟨.tilted, 2, 1, false, 177671401346819557⟩,
  .shared 124 48 48 ⟨.tilted, 2, 1, false, 185721350329613146⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 14 := ⟨[
  .shared 124 49 48 ⟨.tilted, 2, 2, false, 197195067523723129⟩,
  .shared 124 50 48 ⟨.tilted, 2, 2, false, 202259924838834658⟩,
  .shared 124 51 48 ⟨.tilted, 2, 2, false, 210745664335710079⟩,
  .shared 124 52 48 ⟨.tilted, 2, 2, false, 219373781307726940⟩,
  .shared 125 43 47 ⟨.ordinary, 2, 1, false, 200994225736821163⟩,
  .shared 125 44 47 ⟨.ordinary, 2, 1, false, 211096594448160215⟩], by decide +kernel⟩
private def batch29 : PaidBatch .empty 14 := ⟨[
  .point 125 45 47,
  .shared 125 46 47 ⟨.tilted, 2, 1, false, 171060298951334251⟩,
  .shared 125 47 47 ⟨.tilted, 2, 1, false, 179020121858252966⟩,
  .shared 125 48 48 ⟨.tilted, 2, 2, false, 204788570328333729⟩,
  .shared 125 49 48 ⟨.tilted, 2, 2, false, 196052893694871819⟩,
  .shared 125 50 48 ⟨.tilted, 2, 2, false, 203788487784487781⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 14 := ⟨[
  .shared 125 51 48 ⟨.tilted, 2, 2, false, 212336098779138108⟩,
  .shared 125 52 48 ⟨.tilted, 2, 2, false, 221027049258780709⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 14) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30]
private abbrev tiles := tilesOf batches

private theorem index42 : checks tiles 125 42 8 = true := by decide +kernel
private theorem index50 : checks tiles 125 50 3 = true := by decide +kernel
private theorem covers : checks tiles 125 42 11 = true :=
  checks_join index42 index50

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 14)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 14 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top14

end Compact50PriceTableEmpty13
