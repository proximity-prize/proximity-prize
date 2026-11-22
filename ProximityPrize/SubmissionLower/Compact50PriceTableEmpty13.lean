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
  .rectangle 13 39 69 45 45,
  .rectangle 16 46 69 52 45,
  .rectangle 70 46 83 49 48,
  .rectangle 70 50 83 52 48,
  .rectangle 70 39 97 42 46,
  .rectangle 70 43 97 45 46], by decide +kernel⟩
private def batch1 : PaidBatch .empty 13 := ⟨[
  .rectangle 84 50 90 52 48,
  .rectangle 84 46 97 49 48,
  .rectangle 91 50 97 51 48,
  .rectangle 91 52 97 52 48,
  .rectangle 98 51 99 51 48,
  .rectangle 98 52 99 52 49], by decide +kernel⟩
private def batch2 : PaidBatch .empty 13 := ⟨[
  .rectangle 98 50 101 50 48,
  .rectangle 98 43 104 45 48,
  .rectangle 98 46 104 47 48,
  .rectangle 98 48 104 48 48,
  .rectangle 98 49 104 49 48,
  .rectangle 98 41 111 42 47], by decide +kernel⟩
private def batch3 : PaidBatch .empty 13 := ⟨[
  .rectangle 98 39 125 40 47,
  .rectangle 100 51 100 51 48,
  .rectangle 100 52 100 52 49,
  .point 101 51 48,
  .point 101 52 49,
  .point 102 51 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 13 := ⟨[
  .point 102 52 49,
  .rectangle 102 50 103 50 48,
  .point 103 51 48,
  .point 103 52 49,
  .point 104 50 48,
  .point 104 51 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 13 := ⟨[
  .point 104 52 49,
  .rectangle 105 49 105 49 48,
  .point 105 50 48,
  .point 105 51 49,
  .point 105 52 49,
  .rectangle 105 47 108 47 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 13 := ⟨[
  .rectangle 105 48 108 48 48,
  .rectangle 105 43 111 45 48,
  .rectangle 105 46 111 46 48,
  .point 106 49 48,
  .point 106 50 48,
  .point 106 51 49], by decide +kernel⟩
private def batch7 : PaidBatch .empty 13 := ⟨[
  .point 106 52 49,
  .point 107 49 48,
  .point 107 50 48,
  .point 107 51 49,
  .point 107 52 49,
  .point 108 49 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 13 := ⟨[
  .point 108 50 48,
  .point 108 51 49,
  .shared 108 52 49 ⟨.tilted, 2, 2, false, 206491309024765353⟩,
  .point 109 48 48,
  .point 109 49 48,
  .point 109 50 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 13 := ⟨[
  .point 109 51 49,
  .shared 109 52 49 ⟨.tilted, 2, 2, false, 200735605349849294⟩,
  .rectangle 109 47 110 47 48,
  .point 110 48 48,
  .point 110 49 48,
  .point 110 50 48], by decide +kernel⟩
private def batch10 : PaidBatch .empty 13 := ⟨[
  .shared 110 51 49 ⟨.tilted, 2, 1, false, 187002472821449641⟩,
  .shared 110 52 49 ⟨.tilted, 2, 2, false, 194979901674933236⟩,
  .point 111 47 48,
  .point 111 48 48,
  .point 111 49 48,
  .point 111 50 49], by decide +kernel⟩
private def batch11 : PaidBatch .empty 13 := ⟨[
  .shared 111 51 49 ⟨.tilted, 2, 1, false, 188581231954899101⟩,
  .shared 111 52 49 ⟨.tilted, 2, 2, false, 196208301605022405⟩,
  .point 112 47 48,
  .point 112 48 48,
  .point 112 49 48,
  .point 112 50 49], by decide +kernel⟩
private def batch12 : PaidBatch .empty 13 := ⟨[
  .shared 112 51 49 ⟨.tilted, 2, 2, false, 204642686083665073⟩,
  .shared 112 52 49 ⟨.tilted, 2, 2, false, 197848746936900074⟩,
  .rectangle 112 46 113 46 48,
  .rectangle 112 45 115 45 48,
  .rectangle 112 41 118 42 48,
  .rectangle 112 43 118 43 48], by decide +kernel⟩
private def batch13 : PaidBatch .empty 13 := ⟨[
  .rectangle 112 44 118 44 48,
  .point 113 47 48,
  .point 113 48 48,
  .shared 113 49 48 ⟨.tilted, 2, 1, false, 176613619461527743⟩,
  .shared 113 50 49 ⟨.tilted, 2, 1, false, 184113078475706313⟩,
  .shared 113 51 49 ⟨.tilted, 2, 2, false, 199595020440542444⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 13 := ⟨[
  .shared 113 52 49 ⟨.tilted, 2, 2, false, 199489192268777744⟩,
  .point 114 46 48,
  .point 114 47 48,
  .point 114 48 48,
  .shared 114 49 48 ⟨.tilted, 2, 1, false, 178071891060171039⟩,
  .shared 114 50 49 ⟨.tilted, 2, 1, false, 185631113031410983⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 13 := ⟨[
  .shared 114 51 49 ⟨.tilted, 2, 2, false, 194547354797419816⟩,
  .shared 114 52 49 ⟨.tilted, 2, 2, false, 201129637600655413⟩,
  .point 115 46 48,
  .point 115 47 48,
  .point 115 48 48,
  .shared 115 49 48 ⟨.tilted, 2, 1, false, 179530162658814336⟩], by decide +kernel⟩
private def batch16 : PaidBatch .empty 13 := ⟨[
  .shared 115 50 49 ⟨.tilted, 2, 1, false, 187149147587115652⟩,
  .shared 115 51 49 ⟨.tilted, 2, 2, false, 194896268488696943⟩,
  .shared 115 52 49 ⟨.tilted, 2, 2, false, 202770082932533083⟩,
  .rectangle 116 45 116 45 48,
  .point 116 46 48,
  .point 116 47 48], by decide +kernel⟩
private def batch17 : PaidBatch .empty 13 := ⟨[
  .shared 116 48 48 ⟨.tilted, 2, 1, false, 173440226397083463⟩,
  .shared 116 49 49 ⟨.tilted, 2, 1, false, 180988434257457632⟩,
  .shared 116 50 49 ⟨.tilted, 2, 2, false, 207031722626107752⟩,
  .shared 116 51 49 ⟨.tilted, 2, 2, false, 196475027622146404⟩,
  .shared 116 52 49 ⟨.tilted, 2, 2, false, 204410528264410752⟩,
  .point 117 45 48], by decide +kernel⟩
private def batch18 : PaidBatch .empty 13 := ⟨[
  .point 117 46 48,
  .point 117 47 48,
  .shared 117 48 48 ⟨.tilted, 2, 1, false, 174839696659348805⟩,
  .shared 117 49 49 ⟨.tilted, 2, 1, false, 182446705856100929⟩,
  .shared 117 50 49 ⟨.tilted, 2, 2, false, 202655873957827018⟩,
  .shared 117 51 49 ⟨.tilted, 2, 2, false, 198053786755595864⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 13 := ⟨[
  .shared 117 52 49 ⟨.tilted, 2, 2, false, 206050973596288422⟩,
  .point 118 45 48,
  .point 118 46 48,
  .point 118 47 48,
  .shared 118 48 48 ⟨.tilted, 2, 1, false, 176239166921614146⟩,
  .shared 118 49 49 ⟨.tilted, 2, 1, false, 183904977454744225⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 13 := ⟨[
  .shared 118 50 49 ⟨.tilted, 2, 2, false, 198280025289546283⟩,
  .shared 118 51 49 ⟨.tilted, 2, 2, false, 199632545889045325⟩,
  .shared 118 52 49 ⟨.tilted, 2, 2, false, 207691418928166091⟩,
  .rectangle 119 44 119 44 48,
  .point 119 45 48,
  .point 119 46 48], by decide +kernel⟩
private def batch21 : PaidBatch .empty 13 := ⟨[
  .shared 119 47 48 ⟨.tilted, 2, 1, false, 170048892632435354⟩,
  .shared 119 48 48 ⟨.tilted, 2, 1, false, 177638637183879488⟩,
  .shared 119 49 49 ⟨.tilted, 2, 1, false, 185363249053387522⟩,
  .shared 119 50 49 ⟨.tilted, 2, 2, false, 193904176621265549⟩,
  .shared 119 51 49 ⟨.tilted, 2, 2, false, 201211305022494785⟩,
  .shared 119 52 49 ⟨.tilted, 2, 2, false, 209331864260043761⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 13 := ⟨[
  .rectangle 119 43 122 43 48,
  .rectangle 119 41 125 41 48,
  .rectangle 119 42 125 42 48,
  .point 120 44 48,
  .point 120 45 48,
  .point 120 46 48], by decide +kernel⟩
private def batch23 : PaidBatch .empty 13 := ⟨[
  .shared 120 47 48 ⟨.tilted, 2, 1, false, 171390523179006159⟩,
  .shared 120 48 48 ⟨.tilted, 2, 1, false, 179038107446144829⟩,
  .shared 120 49 49 ⟨.tilted, 2, 1, false, 186821520652030818⟩,
  .shared 120 50 49 ⟨.tilted, 2, 2, false, 194739320365639000⟩,
  .shared 120 51 49 ⟨.tilted, 2, 2, false, 202790064155944246⟩,
  .shared 120 52 49 ⟨.tilted, 2, 2, false, 210972309591921430⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 13 := ⟨[
  .point 121 44 48,
  .point 121 45 48,
  .point 121 46 48,
  .shared 121 47 48 ⟨.tilted, 2, 1, false, 172732153725576963⟩,
  .shared 121 48 48 ⟨.tilted, 2, 1, false, 180437577708410171⟩,
  .shared 121 49 49 ⟨.tilted, 2, 1, false, 188279792250674115⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 13 := ⟨[
  .shared 121 50 49 ⟨.tilted, 2, 2, false, 196257354921343669⟩,
  .shared 121 51 49 ⟨.tilted, 2, 2, false, 204368823289393706⟩,
  .shared 121 52 49 ⟨.tilted, 2, 2, false, 212612754923799100⟩,
  .point 122 44 48,
  .point 122 45 48,
  .shared 122 46 48 ⟨.tilted, 2, 1, false, 166449715184759306⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 13 := ⟨[
  .shared 122 47 48 ⟨.tilted, 2, 1, false, 174073784272147768⟩,
  .shared 122 48 49 ⟨.tilted, 2, 1, false, 181837047970675512⟩,
  .shared 122 49 49 ⟨.tilted, 2, 2, false, 205688928882466901⟩,
  .shared 122 50 49 ⟨.tilted, 2, 2, false, 197775389477048339⟩,
  .shared 122 51 49 ⟨.tilted, 2, 2, false, 205947582422843167⟩,
  .shared 122 52 49 ⟨.tilted, 2, 2, false, 214253200255676769⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 13 := ⟨[
  .rectangle 123 43 123 43 48,
  .point 123 44 48,
  .point 123 45 48,
  .shared 123 46 48 ⟨.tilted, 2, 1, false, 167734467636318991⟩,
  .shared 123 47 48 ⟨.tilted, 2, 1, false, 175415414818718572⟩,
  .shared 123 48 49 ⟨.tilted, 2, 1, false, 183236518232940854⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 13 := ⟨[
  .shared 123 49 49 ⟨.tilted, 2, 2, false, 201948676132076525⟩,
  .shared 123 50 49 ⟨.tilted, 2, 2, false, 199293424032753008⟩,
  .shared 123 51 49 ⟨.tilted, 2, 2, false, 207526341556292627⟩,
  .shared 123 52 49 ⟨.tilted, 2, 2, false, 215893645587554439⟩,
  .point 124 43 48,
  .point 124 44 48], by decide +kernel⟩
private def batch29 : PaidBatch .empty 13 := ⟨[
  .point 124 45 48,
  .shared 124 46 48 ⟨.tilted, 2, 1, false, 169019220087878677⟩,
  .shared 124 47 48 ⟨.tilted, 2, 1, false, 176757045365289377⟩,
  .shared 124 48 49 ⟨.tilted, 2, 1, false, 184635988495206195⟩,
  .shared 124 49 49 ⟨.tilted, 2, 2, false, 198208423381686148⟩,
  .shared 124 50 49 ⟨.tilted, 2, 2, false, 200811458588457678⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 13 := ⟨[
  .shared 124 51 49 ⟨.tilted, 2, 2, false, 209105100689742088⟩,
  .shared 124 52 49 ⟨.tilted, 2, 2, false, 217534090919432108⟩,
  .point 125 43 48,
  .point 125 44 48,
  .point 125 45 48,
  .shared 125 46 48 ⟨.tilted, 2, 1, false, 170303972539438362⟩], by decide +kernel⟩
private def batch31 : PaidBatch .empty 13 := ⟨[
  .shared 125 47 48 ⟨.tilted, 2, 1, false, 178098675911860181⟩,
  .shared 125 48 49 ⟨.tilted, 2, 1, false, 186035458757471537⟩,
  .shared 125 49 49 ⟨.tilted, 2, 2, false, 195384266215484112⟩,
  .shared 125 50 49 ⟨.tilted, 2, 2, false, 202329493144162347⟩,
  .shared 125 51 49 ⟨.tilted, 2, 2, false, 210683859823191548⟩,
  .shared 125 52 49 ⟨.tilted, 2, 2, false, 219174536251309778⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 13) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31]
private abbrev tiles := tilesOf batches

private theorem index39 : checks tiles 125 39 8 = true := by decide +kernel
theorem index47 : checks tiles 125 47 6 = true := by decide +kernel
private theorem covers : checks tiles 125 39 14 = true :=
  checks_join index39 index47

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 13)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 13 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top13

namespace Top14

private def batch0 : PaidBatch .empty 14 := ⟨[
  .rectangle 14 42 69 52 45,
  .rectangle 70 48 83 52 48,
  .rectangle 70 42 97 44 46,
  .rectangle 70 45 97 47 48,
  .rectangle 84 51 90 52 48,
  .rectangle 84 48 97 50 48], by decide +kernel⟩
private def batch1 : PaidBatch .empty 14 := ⟨[
  .rectangle 91 51 97 51 48,
  .rectangle 91 52 97 52 48,
  .rectangle 98 51 99 51 48,
  .rectangle 98 52 99 52 49,
  .rectangle 98 50 101 50 48,
  .rectangle 98 45 104 47 48], by decide +kernel⟩
private def batch2 : PaidBatch .empty 14 := ⟨[
  .rectangle 98 48 104 48 48,
  .rectangle 98 49 104 49 48,
  .rectangle 98 42 111 44 47,
  .rectangle 100 51 100 51 48,
  .rectangle 100 52 100 52 49,
  .point 101 51 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 14 := ⟨[
  .point 101 52 49,
  .point 102 51 48,
  .point 102 52 49,
  .rectangle 102 50 103 50 48,
  .point 103 51 48,
  .point 103 52 49], by decide +kernel⟩
private def batch4 : PaidBatch .empty 14 := ⟨[
  .point 104 50 48,
  .point 104 51 48,
  .point 104 52 49,
  .rectangle 105 49 105 49 48,
  .point 105 50 48,
  .point 105 51 49], by decide +kernel⟩
private def batch5 : PaidBatch .empty 14 := ⟨[
  .point 105 52 49,
  .rectangle 105 48 108 48 48,
  .rectangle 105 45 111 46 48,
  .rectangle 105 47 111 47 48,
  .point 106 49 48,
  .point 106 50 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 14 := ⟨[
  .point 106 51 49,
  .point 106 52 49,
  .point 107 49 48,
  .point 107 50 48,
  .point 107 51 49,
  .point 107 52 49], by decide +kernel⟩
private def batch7 : PaidBatch .empty 14 := ⟨[
  .point 108 49 48,
  .point 108 50 48,
  .point 108 51 49,
  .shared 108 52 49 ⟨.tilted, 2, 2, false, 199398939089194612⟩,
  .point 109 48 48,
  .point 109 49 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 14 := ⟨[
  .point 109 50 48,
  .point 109 51 49,
  .shared 109 52 49 ⟨.tilted, 2, 2, false, 197309336056907857⟩,
  .point 110 48 48,
  .point 110 49 48,
  .point 110 50 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 14 := ⟨[
  .shared 110 51 49 ⟨.tilted, 2, 2, false, 201840529434438947⟩,
  .shared 110 52 49 ⟨.tilted, 2, 2, false, 196148648746883134⟩,
  .point 111 48 48,
  .point 111 49 48,
  .point 111 50 49,
  .shared 111 51 49 ⟨.tilted, 2, 2, false, 200086443112801277⟩], by decide +kernel⟩
private def batch10 : PaidBatch .empty 14 := ⟨[
  .shared 111 52 49 ⟨.tilted, 2, 2, false, 197801247891995293⟩,
  .point 112 47 48,
  .point 112 48 48,
  .point 112 49 48,
  .point 112 50 49,
  .shared 112 51 49 ⟨.tilted, 2, 2, false, 198332356791163608⟩], by decide +kernel⟩
private def batch11 : PaidBatch .empty 14 := ⟨[
  .shared 112 52 49 ⟨.tilted, 2, 2, false, 199453847037107452⟩,
  .rectangle 112 46 113 46 48,
  .rectangle 112 45 115 45 48,
  .rectangle 112 42 118 43 48,
  .rectangle 112 44 118 44 48,
  .point 113 47 48], by decide +kernel⟩
private def batch12 : PaidBatch .empty 14 := ⟨[
  .point 113 48 48,
  .shared 113 49 48 ⟨.tilted, 2, 1, false, 177701901939296303⟩,
  .shared 113 50 49 ⟨.tilted, 2, 1, false, 185370713015411195⟩,
  .shared 113 51 49 ⟨.tilted, 2, 2, false, 196578270469525938⟩,
  .shared 113 52 49 ⟨.tilted, 2, 2, false, 201106446182219611⟩,
  .point 114 46 48], by decide +kernel⟩
private def batch13 : PaidBatch .empty 14 := ⟨[
  .point 114 47 48,
  .point 114 48 48,
  .shared 114 49 48 ⟨.tilted, 2, 1, false, 179168961678782126⟩,
  .shared 114 50 49 ⟨.tilted, 2, 2, false, 202057657950994104⟩,
  .shared 114 51 49 ⟨.tilted, 2, 2, false, 194824184147888269⟩,
  .shared 114 52 49 ⟨.tilted, 2, 2, false, 202759045327331770⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 14 := ⟨[
  .point 115 46 48,
  .point 115 47 48,
  .point 115 48 48,
  .shared 115 49 48 ⟨.tilted, 2, 1, false, 180636021418267949⟩,
  .shared 115 50 49 ⟨.tilted, 2, 2, false, 200619535380504625⟩,
  .shared 115 51 49 ⟨.tilted, 2, 2, false, 196352290685167265⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 14 := ⟨[
  .shared 115 52 49 ⟨.tilted, 2, 2, false, 204411644472443929⟩,
  .rectangle 116 45 116 45 48,
  .point 116 46 48,
  .point 116 47 48,
  .shared 116 48 48 ⟨.tilted, 2, 1, false, 174389127313006098⟩,
  .shared 116 49 49 ⟨.tilted, 2, 1, false, 182103081157753772⟩], by decide +kernel⟩
private def batch16 : PaidBatch .empty 14 := ⟨[
  .shared 116 50 49 ⟨.tilted, 2, 2, false, 199181412810015146⟩,
  .shared 116 51 49 ⟨.tilted, 2, 2, false, 197942081741053894⟩,
  .shared 116 52 49 ⟨.tilted, 2, 2, false, 206064243617556088⟩,
  .point 117 45 48,
  .point 117 46 48,
  .point 117 47 48], by decide +kernel⟩
private def batch17 : PaidBatch .empty 14 := ⟨[
  .shared 117 48 48 ⟨.tilted, 2, 1, false, 175796263825316645⟩,
  .shared 117 49 49 ⟨.tilted, 2, 1, false, 183570140897239595⟩,
  .shared 117 50 49 ⟨.tilted, 2, 2, false, 197743290239525667⟩,
  .shared 117 51 49 ⟨.tilted, 2, 2, false, 199531872796940523⟩,
  .shared 117 52 49 ⟨.tilted, 2, 2, false, 207716842762668247⟩,
  .point 118 45 48], by decide +kernel⟩
private def batch18 : PaidBatch .empty 14 := ⟨[
  .point 118 46 48,
  .point 118 47 48,
  .shared 118 48 48 ⟨.tilted, 2, 1, false, 177203400337627192⟩,
  .shared 118 49 49 ⟨.tilted, 2, 1, false, 185037200636725418⟩,
  .shared 118 50 49 ⟨.tilted, 2, 2, false, 196305167669036188⟩,
  .shared 118 51 49 ⟨.tilted, 2, 2, false, 201121663852827152⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 14 := ⟨[
  .shared 118 52 49 ⟨.tilted, 2, 2, false, 209369441907780406⟩,
  .point 119 45 48,
  .point 119 46 48,
  .shared 119 47 48 ⟨.tilted, 2, 1, false, 170858652391682919⟩,
  .shared 119 48 48 ⟨.tilted, 2, 1, false, 178610536849937739⟩,
  .shared 119 49 49 ⟨.tilted, 2, 2, false, 202823853971329329⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 14 := ⟨[
  .shared 119 50 49 ⟨.tilted, 2, 2, false, 194867045098546709⟩,
  .shared 119 51 49 ⟨.tilted, 2, 2, false, 202711454908713781⟩,
  .shared 119 52 49 ⟨.tilted, 2, 2, false, 211022041052892565⟩,
  .rectangle 119 44 120 44 48,
  .rectangle 119 43 122 43 48,
  .rectangle 119 42 125 42 48], by decide +kernel⟩
private def batch21 : PaidBatch .empty 14 := ⟨[
  .point 120 45 48,
  .point 120 46 48,
  .shared 120 47 48 ⟨.tilted, 2, 1, false, 172206827297501608⟩,
  .shared 120 48 48 ⟨.tilted, 2, 1, false, 180017673362248286⟩,
  .shared 120 49 49 ⟨.tilted, 2, 2, false, 201682142192487145⟩,
  .shared 120 50 49 ⟨.tilted, 2, 2, false, 196066325126822814⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 14 := ⟨[
  .shared 120 51 49 ⟨.tilted, 2, 2, false, 204301245964600410⟩,
  .shared 120 52 49 ⟨.tilted, 2, 2, false, 212674640198004724⟩,
  .shared 121 44 48 ⟨.ordinary, 2, 1, false, 204632180453322820⟩,
  .point 121 45 48,
  .point 121 46 48,
  .shared 121 47 48 ⟨.tilted, 2, 1, false, 173555002203320297⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 14 := ⟨[
  .shared 121 48 48 ⟨.tilted, 2, 1, false, 181424809874558833⟩,
  .shared 121 49 49 ⟨.tilted, 2, 2, false, 200540430413644962⟩,
  .shared 121 50 49 ⟨.tilted, 2, 2, false, 197594269714167331⟩,
  .shared 121 51 49 ⟨.tilted, 2, 2, false, 205891037020487039⟩,
  .shared 121 52 49 ⟨.tilted, 2, 2, false, 214327239343116883⟩,
  .shared 122 44 48 ⟨.ordinary, 2, 1, false, 206226935670556370⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 14 := ⟨[
  .point 122 45 48,
  .point 122 46 48,
  .shared 122 47 48 ⟨.tilted, 2, 1, false, 174903177109138986⟩,
  .shared 122 48 49 ⟨.tilted, 2, 1, false, 182831946386869380⟩,
  .shared 122 49 49 ⟨.tilted, 2, 2, false, 199398718634802778⟩,
  .shared 122 50 49 ⟨.tilted, 2, 2, false, 199122214301511848⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 14 := ⟨[
  .shared 122 51 49 ⟨.tilted, 2, 2, false, 207480828076373668⟩,
  .shared 122 52 49 ⟨.tilted, 2, 2, false, 215979838488229042⟩,
  .rectangle 123 43 123 43 48,
  .shared 123 44 48 ⟨.ordinary, 2, 1, false, 207821690887789920⟩,
  .point 123 45 48,
  .shared 123 46 48 ⟨.tilted, 2, 1, false, 168410749112512903⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 14 := ⟨[
  .shared 123 47 48 ⟨.tilted, 2, 1, false, 176251352014957675⟩,
  .shared 123 48 49 ⟨.tilted, 2, 1, false, 184239082899179927⟩,
  .shared 123 49 49 ⟨.tilted, 2, 2, false, 198257006855960595⟩,
  .shared 123 50 49 ⟨.tilted, 2, 2, false, 200650158888856365⟩,
  .shared 123 51 49 ⟨.tilted, 2, 2, false, 209070619132260297⟩,
  .shared 123 52 49 ⟨.tilted, 2, 2, false, 217632437633341201⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 14 := ⟨[
  .shared 124 43 48 ⟨.ordinary, 2, 1, false, 199392249622992785⟩,
  .shared 124 44 48 ⟨.ordinary, 2, 1, false, 209416446105023470⟩,
  .point 124 45 48,
  .shared 124 46 48 ⟨.tilted, 2, 1, false, 169700924032523152⟩,
  .shared 124 47 48 ⟨.tilted, 2, 1, false, 177599526920776364⟩,
  .shared 124 48 49 ⟨.tilted, 2, 1, false, 185646219411490474⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 14 := ⟨[
  .shared 124 49 49 ⟨.tilted, 2, 2, false, 197115295077118411⟩,
  .shared 124 50 49 ⟨.tilted, 2, 2, false, 202178103476200882⟩,
  .shared 124 51 49 ⟨.tilted, 2, 2, false, 210660410188146926⟩,
  .shared 124 52 49 ⟨.tilted, 2, 2, false, 219285036778453360⟩,
  .shared 125 43 48 ⟨.ordinary, 2, 1, false, 200912919237329285⟩,
  .shared 125 44 48 ⟨.ordinary, 2, 1, false, 211011201322257020⟩], by decide +kernel⟩
private def batch29 : PaidBatch .empty 14 := ⟨[
  .point 125 45 48,
  .shared 125 46 48 ⟨.tilted, 2, 1, false, 170991098952533401⟩,
  .shared 125 47 48 ⟨.tilted, 2, 1, false, 178947701826595053⟩,
  .shared 125 48 49 ⟨.tilted, 2, 2, false, 204705726038621739⟩,
  .shared 125 49 49 ⟨.tilted, 2, 2, false, 195973583298276228⟩,
  .shared 125 50 49 ⟨.tilted, 2, 2, false, 203706048063545399⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 14 := ⟨[
  .shared 125 51 49 ⟨.tilted, 2, 2, false, 212250201244033555⟩,
  .shared 125 52 49 ⟨.tilted, 2, 2, false, 220937635923565519⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 14) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30]
private abbrev tiles := tilesOf batches

theorem index42 : checks tiles 125 42 8 = true := by decide +kernel
private theorem index50 : checks tiles 125 50 3 = true := by decide +kernel
private theorem covers : checks tiles 125 42 11 = true :=
  checks_join index42 index50

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 14)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 14 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top14

end Compact50PriceTableEmpty13
