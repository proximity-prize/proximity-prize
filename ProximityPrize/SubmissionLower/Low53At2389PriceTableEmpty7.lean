import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top7
private def b0 : PaidBatch .empty 7 := ⟨[
  .rectangle 7 21 68 29 26,
  .rectangle 10 30 69 37 30,
  .rectangle 13 38 71 45 36], by decide +kernel⟩
private def b1 : PaidBatch .empty 7 := ⟨[
  .rectangle 16 46 71 53 40,
  .rectangle 69 21 129 25 34,
  .rectangle 69 26 129 29 38], by decide +kernel⟩
private def b2 : PaidBatch .empty 7 := ⟨[
  .rectangle 70 34 99 37 37,
  .rectangle 70 30 129 33 43,
  .rectangle 72 46 86 49 41], by decide +kernel⟩
private def b3 : PaidBatch .empty 7 := ⟨[
  .rectangle 72 50 86 53 44,
  .rectangle 72 38 100 41 41,
  .rectangle 72 42 100 45 45], by decide +kernel⟩
private def b4 : PaidBatch .empty 7 := ⟨[
  .rectangle 87 52 93 53 46,
  .rectangle 87 46 100 47 44,
  .rectangle 87 48 100 49 46], by decide +kernel⟩
private def b5 : PaidBatch .empty 7 := ⟨[
  .rectangle 87 50 100 51 48,
  .rectangle 94 52 100 52 48,
  .rectangle 94 53 100 53 48], by decide +kernel⟩
private def b6 : PaidBatch .empty 7 := ⟨[
  .rectangle 100 34 129 35 42,
  .rectangle 100 36 129 37 45,
  .point 101 53 46], by decide +kernel⟩
private def b7 : PaidBatch .empty 7 := ⟨[
  .rectangle 101 51 102 51 48,
  .rectangle 101 52 102 52 48,
  .rectangle 101 50 104 50 48], by decide +kernel⟩
private def b8 : PaidBatch .empty 7 := ⟨[
  .rectangle 101 44 108 45 46,
  .rectangle 101 46 108 47 48,
  .rectangle 101 48 108 48 48], by decide +kernel⟩
private def b9 : PaidBatch .empty 7 := ⟨[
  .rectangle 101 49 108 49 48,
  .rectangle 101 40 115 41 44,
  .rectangle 101 42 115 43 47], by decide +kernel⟩
private def b10 : PaidBatch .empty 7 := ⟨[
  .rectangle 101 38 129 39 47,
  .point 102 53 46,
  .rectangle 103 51 103 51 48], by decide +kernel⟩
private def b11 : PaidBatch .empty 7 := ⟨[
  .point 103 52 46,
  .point 103 53 47,
  .point 104 51 45], by decide +kernel⟩
private def b12 : PaidBatch .empty 7 := ⟨[
  .point 104 52 46,
  .point 104 53 47,
  .rectangle 105 50 105 50 48], by decide +kernel⟩
private def b13 : PaidBatch .empty 7 := ⟨[
  .point 105 51 46,
  .point 105 52 47,
  .point 105 53 48], by decide +kernel⟩
private def b14 : PaidBatch .empty 7 := ⟨[
  .point 106 50 45,
  .point 106 51 46,
  .point 106 52 47], by decide +kernel⟩
private def b15 : PaidBatch .empty 7 := ⟨[
  .point 106 53 48,
  .point 107 50 46,
  .point 107 51 47], by decide +kernel⟩
private def b16 : PaidBatch .empty 7 := ⟨[
  .point 107 52 48,
  .point 107 53 48,
  .point 108 50 46], by decide +kernel⟩
private def b17 : PaidBatch .empty 7 := ⟨[
  .point 108 51 47,
  .point 108 52 48,
  .point 108 53 49], by decide +kernel⟩
private def b18 : PaidBatch .empty 7 := ⟨[
  .point 109 49 46,
  .point 109 50 47,
  .point 109 51 48], by decide +kernel⟩
private def b19 : PaidBatch .empty 7 := ⟨[
  .point 109 52 48,
  .point 109 53 49,
  .rectangle 109 48 110 48 48], by decide +kernel⟩
private def b20 : PaidBatch .empty 7 := ⟨[
  .rectangle 109 46 112 46 47,
  .rectangle 109 47 112 47 48,
  .rectangle 109 44 115 44 46], by decide +kernel⟩
private def b21 : PaidBatch .empty 7 := ⟨[
  .rectangle 109 45 115 45 48,
  .point 110 49 46,
  .point 110 50 47], by decide +kernel⟩
private def b22 : PaidBatch .empty 7 := ⟨[
  .point 110 51 48,
  .point 110 52 49,
  .shared 110 53 33 ⟨.tilted, 1, 2, true, 187610921270017556⟩], by decide +kernel⟩
private def b23 : PaidBatch .empty 7 := ⟨[
  .point 111 48 46,
  .point 111 49 47,
  .point 111 50 47], by decide +kernel⟩
private def b24 : PaidBatch .empty 7 := ⟨[
  .point 111 51 48,
  .point 111 52 49,
  .shared 111 53 34 ⟨.tilted, 1, 2, true, 189278102038541632⟩], by decide +kernel⟩
private def b25 : PaidBatch .empty 7 := ⟨[
  .point 112 48 46,
  .point 112 49 47,
  .point 112 50 48], by decide +kernel⟩
private def b26 : PaidBatch .empty 7 := ⟨[
  .shared 112 51 32 ⟨.tilted, 1, 2, true, 177019486535922015⟩,
  .shared 112 52 33 ⟨.tilted, 1, 2, true, 183931311638349779⟩,
  .shared 112 53 34 ⟨.tilted, 1, 2, true, 190945282807065708⟩], by decide +kernel⟩
private def b27 : PaidBatch .empty 7 := ⟨[
  .point 113 47 45,
  .point 113 48 46,
  .point 113 49 47], by decide +kernel⟩
private def b28 : PaidBatch .empty 7 := ⟨[
  .point 113 50 48,
  .shared 113 51 32 ⟨.tilted, 1, 2, true, 178558428131493627⟩,
  .shared 113 52 34 ⟨.tilted, 1, 2, true, 185533731624639627⟩], by decide +kernel⟩
private def b29 : PaidBatch .empty 7 := ⟨[
  .shared 113 53 35 ⟨.tilted, 1, 2, true, 192612463575589784⟩,
  .rectangle 113 46 114 46 48,
  .point 114 47 46], by decide +kernel⟩
private def b30 : PaidBatch .empty 7 := ⟨[
  .point 114 48 47,
  .point 114 49 48,
  .shared 114 50 32 ⟨.tilted, 1, 2, true, 173165222279795142⟩], by decide +kernel⟩
private def b31 : PaidBatch .empty 7 := ⟨[
  .shared 114 51 33 ⟨.tilted, 1, 2, true, 180097369727065239⟩,
  .shared 114 52 34 ⟨.tilted, 1, 2, true, 187136151610929475⟩,
  .shared 114 53 35 ⟨.tilted, 1, 2, true, 194279644344113860⟩], by decide +kernel⟩
private def b32 : PaidBatch .empty 7 := ⟨[
  .point 115 46 45,
  .point 115 47 46,
  .point 115 48 47], by decide +kernel⟩
private def b33 : PaidBatch .empty 7 := ⟨[
  .point 115 49 48,
  .shared 115 50 32 ⟨.tilted, 1, 2, true, 174641967876164510⟩,
  .shared 115 51 34 ⟨.tilted, 1, 2, true, 181636311322636851⟩], by decide +kernel⟩
private def b34 : PaidBatch .empty 7 := ⟨[
  .shared 115 52 35 ⟨.tilted, 1, 2, true, 188738571597219323⟩,
  .shared 115 53 36 ⟨.tilted, 1, 2, true, 195946825112637936⟩,
  .point 116 46 46], by decide +kernel⟩
private def b35 : PaidBatch .empty 7 := ⟨[
  .point 116 47 47,
  .point 116 48 48,
  .shared 116 49 32 ⟨.tilted, 1, 2, true, 169173296833759402⟩], by decide +kernel⟩
private def b36 : PaidBatch .empty 7 := ⟨[
  .shared 116 50 33 ⟨.tilted, 1, 2, true, 176118713472533878⟩,
  .shared 116 51 34 ⟨.tilted, 1, 2, true, 183175252918208463⟩,
  .shared 116 52 35 ⟨.tilted, 1, 2, true, 190340991583509171⟩], by decide +kernel⟩
private def b37 : PaidBatch .empty 7 := ⟨[
  .shared 116 53 37 ⟨.tilted, 1, 2, true, 197614005881162012⟩,
  .rectangle 116 45 117 45 48,
  .rectangle 116 44 119 44 48], by decide +kernel⟩
private def b38 : PaidBatch .empty 7 := ⟨[
  .rectangle 116 40 122 41 47,
  .rectangle 116 42 122 42 47,
  .rectangle 116 43 122 43 48], by decide +kernel⟩
private def b39 : PaidBatch .empty 7 := ⟨[
  .point 117 46 46,
  .point 117 47 47,
  .point 117 48 48], by decide +kernel⟩
private def b40 : PaidBatch .empty 7 := ⟨[
  .shared 117 49 32 ⟨.tilted, 1, 2, true, 170589128822442518⟩,
  .shared 117 50 33 ⟨.tilted, 1, 2, true, 177595459068903246⟩,
  .shared 117 51 35 ⟨.tilted, 1, 2, true, 184714194513780075⟩], by decide +kernel⟩
private def b41 : PaidBatch .empty 7 := ⟨[
  .shared 117 52 36 ⟨.tilted, 1, 2, true, 191943411569799019⟩,
  .shared 117 53 37 ⟨.tilted, 1, 2, true, 199281186649686088⟩,
  .point 118 45 45], by decide +kernel⟩
private def b42 : PaidBatch .empty 7 := ⟨[
  .point 118 46 46,
  .point 118 47 47,
  .point 118 48 48], by decide +kernel⟩
private def b43 : PaidBatch .empty 7 := ⟨[
  .shared 118 49 33 ⟨.tilted, 1, 2, true, 172004960811125634⟩,
  .shared 118 50 34 ⟨.tilted, 1, 2, true, 179072204665272614⟩,
  .shared 118 51 35 ⟨.tilted, 1, 2, true, 186253136109351687⟩], by decide +kernel⟩
private def b44 : PaidBatch .empty 7 := ⟨[
  .shared 118 52 37 ⟨.tilted, 1, 2, true, 193545831556088867⟩,
  .shared 118 53 38 ⟨.tilted, 1, 2, true, 200948367418210164⟩,
  .point 119 45 46], by decide +kernel⟩
private def b45 : PaidBatch .empty 7 := ⟨[
  .point 119 46 47,
  .point 119 47 48,
  .shared 119 48 37 ⟨.tilted, 1, 1, false, 155460428385017043⟩], by decide +kernel⟩
private def b46 : PaidBatch .empty 7 := ⟨[
  .shared 119 49 33 ⟨.tilted, 1, 2, true, 173420792799808750⟩,
  .shared 119 50 35 ⟨.tilted, 1, 2, true, 180548950261641982⟩,
  .shared 119 51 36 ⟨.tilted, 1, 2, true, 187792077704923299⟩], by decide +kernel⟩
private def b47 : PaidBatch .empty 7 := ⟨[
  .shared 119 52 37 ⟨.tilted, 1, 2, true, 195148251542378715⟩,
  .shared 119 53 39 ⟨.tilted, 1, 2, true, 202615548186734240⟩,
  .rectangle 120 44 120 44 48], by decide +kernel⟩
private def b48 : PaidBatch .empty 7 := ⟨[
  .point 120 45 46,
  .point 120 46 47,
  .point 120 47 48], by decide +kernel⟩
private def b49 : PaidBatch .empty 7 := ⟨[
  .shared 120 48 38 ⟨.tilted, 1, 1, false, 156705470776599132⟩,
  .shared 120 49 34 ⟨.tilted, 1, 2, true, 174836624788491866⟩,
  .shared 120 50 35 ⟨.tilted, 1, 2, true, 182025695858011350⟩], by decide +kernel⟩
private def b50 : PaidBatch .empty 7 := ⟨[
  .shared 120 51 37 ⟨.tilted, 1, 2, true, 189331019300494911⟩,
  .shared 120 52 38 ⟨.tilted, 1, 2, true, 196750671528668563⟩,
  .shared 120 53 39 ⟨.tilted, 1, 2, true, 204282728955258316⟩], by decide +kernel⟩
private def b51 : PaidBatch .empty 7 := ⟨[
  .point 121 44 45,
  .point 121 45 46,
  .point 121 46 48], by decide +kernel⟩
private def b52 : PaidBatch .empty 7 := ⟨[
  .shared 121 47 37 ⟨.tilted, 0, 1, false, 151722282782743757⟩,
  .shared 121 48 38 ⟨.tilted, 1, 1, false, 157950513168181221⟩,
  .shared 121 49 34 ⟨.tilted, 1, 2, true, 176252456777174982⟩], by decide +kernel⟩
private def b53 : PaidBatch .empty 7 := ⟨[
  .shared 121 50 36 ⟨.tilted, 1, 2, true, 183502441454380718⟩,
  .shared 121 51 37 ⟨.tilted, 1, 2, true, 190869960896066523⟩,
  .shared 121 52 39 ⟨.tilted, 1, 2, true, 198353091514958411⟩], by decide +kernel⟩
private def b54 : PaidBatch .empty 7 := ⟨[
  .shared 121 53 40 ⟨.tilted, 1, 2, true, 205949909723782392⟩,
  .point 122 44 46,
  .point 122 45 47], by decide +kernel⟩
private def b55 : PaidBatch .empty 7 := ⟨[
  .point 122 46 48,
  .shared 122 47 38 ⟨.tilted, 0, 1, false, 152917258460478029⟩,
  .shared 122 48 39 ⟨.tilted, 0, 1, false, 159195555559763310⟩], by decide +kernel⟩
private def b56 : PaidBatch .empty 7 := ⟨[
  .shared 122 49 35 ⟨.tilted, 1, 2, true, 177668288765858098⟩,
  .shared 122 50 36 ⟨.tilted, 1, 2, true, 184979187050750086⟩,
  .shared 122 51 38 ⟨.tilted, 1, 2, true, 192408902491638135⟩], by decide +kernel⟩
private def b57 : PaidBatch .empty 7 := ⟨[
  .shared 122 52 39 ⟨.tilted, 1, 2, true, 199955511501248259⟩,
  .shared 122 53 41 ⟨.tilted, 1, 2, true, 207617090492306468⟩,
  .point 123 43 45], by decide +kernel⟩
private def b58 : PaidBatch .empty 7 := ⟨[
  .point 123 44 46,
  .point 123 45 47,
  .point 123 46 48], by decide +kernel⟩
private def b59 : PaidBatch .empty 7 := ⟨[
  .shared 123 47 38 ⟨.tilted, 0, 1, false, 154112234138212301⟩,
  .shared 123 48 34 ⟨.tilted, 0, 2, true, 171834331996749017⟩,
  .shared 123 49 36 ⟨.tilted, 1, 2, true, 179084120754541214⟩], by decide +kernel⟩
private def b60 : PaidBatch .empty 7 := ⟨[
  .shared 123 50 37 ⟨.tilted, 1, 2, true, 186455932647119454⟩,
  .shared 123 51 38 ⟨.tilted, 1, 2, true, 193947844087209747⟩,
  .shared 123 52 40 ⟨.tilted, 1, 2, true, 201557931487538107⟩], by decide +kernel⟩
private def b61 : PaidBatch .empty 7 := ⟨[
  .shared 123 53 41 ⟨.tilted, 1, 2, true, 209284271260830544⟩,
  .rectangle 123 42 124 42 48,
  .rectangle 123 40 129 40 47], by decide +kernel⟩
private def b62 : PaidBatch .empty 7 := ⟨[
  .rectangle 123 41 129 41 48,
  .point 124 43 45,
  .point 124 44 47], by decide +kernel⟩
private def b63 : PaidBatch .empty 7 := ⟨[
  .point 124 45 48,
  .shared 124 46 37 ⟨.tilted, 0, 1, false, 149030711622266828⟩,
  .shared 124 47 39 ⟨.tilted, 0, 1, false, 155307209815946573⟩], by decide +kernel⟩
private def b64 : PaidBatch .empty 7 := ⟨[
  .shared 124 48 35 ⟨.tilted, 0, 2, true, 173190532769261873⟩,
  .shared 124 49 36 ⟨.tilted, 1, 2, true, 180499952743224330⟩,
  .shared 124 50 38 ⟨.tilted, 1, 2, true, 187932678243488822⟩], by decide +kernel⟩
private def b65 : PaidBatch .empty 7 := ⟨[
  .shared 124 51 39 ⟨.tilted, 1, 2, true, 195486785682781359⟩,
  .shared 124 52 41 ⟨.tilted, 1, 2, true, 203160351473827955⟩,
  .shared 124 53 42 ⟨.tilted, 1, 2, true, 210951452029354620⟩], by decide +kernel⟩
private def b66 : PaidBatch .empty 7 := ⟨[
  .rectangle 125 42 125 42 48,
  .point 125 43 46,
  .point 125 44 47], by decide +kernel⟩
private def b67 : PaidBatch .empty 7 := ⟨[
  .point 125 45 48,
  .shared 125 46 38 ⟨.tilted, 0, 1, false, 150176582379790277⟩,
  .shared 125 47 39 ⟨.tilted, 0, 1, false, 156502185493680845⟩], by decide +kernel⟩
private def b68 : PaidBatch .empty 7 := ⟨[
  .shared 125 48 35 ⟨.tilted, 0, 2, true, 174546733541774729⟩,
  .shared 125 49 37 ⟨.tilted, 0, 2, true, 181915784731907446⟩,
  .shared 125 50 38 ⟨.tilted, 1, 2, true, 189409423839858190⟩], by decide +kernel⟩
private def b69 : PaidBatch .empty 7 := ⟨[
  .shared 125 51 40 ⟨.tilted, 1, 2, true, 197025727278352971⟩,
  .shared 125 52 41 ⟨.tilted, 1, 2, true, 204762771460117803⟩,
  .shared 125 53 43 ⟨.tilted, 1, 2, true, 212618632797878696⟩], by decide +kernel⟩
private def b70 : PaidBatch .empty 7 := ⟨[
  .point 126 42 45,
  .point 126 43 46,
  .point 126 44 47], by decide +kernel⟩
private def b71 : PaidBatch .empty 7 := ⟨[
  .point 126 45 48,
  .shared 126 46 38 ⟨.tilted, 0, 1, false, 151322453137313726⟩,
  .shared 126 47 40 ⟨.tilted, 0, 1, false, 157697161171415117⟩], by decide +kernel⟩
private def b72 : PaidBatch .empty 7 := ⟨[
  .shared 126 48 36 ⟨.tilted, 0, 2, true, 175902934314287585⟩,
  .shared 126 49 37 ⟨.tilted, 0, 2, true, 183331616720590562⟩,
  .shared 126 50 39 ⟨.tilted, 1, 2, true, 190886169436227558⟩], by decide +kernel⟩
private def b73 : PaidBatch .empty 7 := ⟨[
  .shared 126 51 40 ⟨.tilted, 1, 2, true, 198564668873924583⟩,
  .shared 126 52 42 ⟨.tilted, 1, 2, true, 206365191446407651⟩,
  .shared 126 53 44 ⟨.tilted, 1, 2, true, 214285813566402772⟩], by decide +kernel⟩
private def b74 : PaidBatch .empty 7 := ⟨[
  .point 127 42 45,
  .point 127 43 46,
  .point 127 44 48], by decide +kernel⟩
private def b75 : PaidBatch .empty 7 := ⟨[
  .shared 127 45 38 ⟨.tilted, 0, 1, false, 146150771345192604⟩,
  .shared 127 46 39 ⟨.tilted, 0, 1, false, 152468323894837175⟩,
  .shared 127 47 40 ⟨.tilted, 0, 1, false, 158892136849149389⟩], by decide +kernel⟩
private def b76 : PaidBatch .empty 7 := ⟨[
  .shared 127 48 36 ⟨.tilted, 0, 2, true, 177259135086800441⟩,
  .shared 127 49 38 ⟨.tilted, 0, 2, true, 184747448709273678⟩,
  .shared 127 50 39 ⟨.tilted, 1, 2, true, 192362915032596926⟩], by decide +kernel⟩
private def b77 : PaidBatch .empty 7 := ⟨[
  .shared 127 51 41 ⟨.tilted, 1, 2, true, 200103610469496195⟩,
  .shared 127 52 43 ⟨.tilted, 1, 2, true, 207967611432697499⟩,
  .shared 127 53 45 ⟨.tilted, 1, 2, true, 215952994334926848⟩], by decide +kernel⟩
private def b78 : PaidBatch .empty 7 := ⟨[
  .point 128 42 46,
  .point 128 43 47,
  .point 128 44 48], by decide +kernel⟩
private def b79 : PaidBatch .empty 7 := ⟨[
  .shared 128 45 38 ⟨.tilted, 0, 1, false, 147248498976142224⟩,
  .shared 128 46 39 ⟨.tilted, 0, 1, false, 153614194652360624⟩,
  .shared 128 47 40 ⟨.tilted, 0, 1, false, 160087112526883661⟩], by decide +kernel⟩
private def b80 : PaidBatch .empty 7 := ⟨[
  .shared 128 48 37 ⟨.tilted, 0, 2, true, 178615335859313297⟩,
  .shared 128 49 38 ⟨.tilted, 0, 2, true, 186163280697956794⟩,
  .shared 128 50 40 ⟨.tilted, 0, 2, true, 193839660628966294⟩], by decide +kernel⟩
private def b81 : PaidBatch .empty 7 := ⟨[
  .shared 128 51 42 ⟨.tilted, 1, 2, true, 201642552065067807⟩,
  .shared 128 52 43 ⟨.tilted, 1, 2, true, 209570031418987347⟩,
  .shared 128 53 45 ⟨.tilted, 1, 2, true, 217620175103450924⟩], by decide +kernel⟩
private def b82 : PaidBatch .empty 7 := ⟨[
  .point 129 42 46,
  .point 129 43 47,
  .point 129 44 48], by decide +kernel⟩
private def b83 : PaidBatch .empty 7 := ⟨[
  .shared 129 45 38 ⟨.tilted, 0, 1, false, 148346226607091844⟩,
  .shared 129 46 40 ⟨.tilted, 0, 1, false, 154760065409884073⟩,
  .shared 129 47 41 ⟨.tilted, 0, 1, false, 161282088204617933⟩], by decide +kernel⟩
private def b84 : PaidBatch .empty 7 := ⟨[
  .shared 129 48 37 ⟨.tilted, 0, 2, true, 179971536631826153⟩,
  .shared 129 49 39 ⟨.tilted, 0, 2, true, 187579112686639910⟩,
  .shared 129 50 41 ⟨.tilted, 0, 2, true, 195316406225335662⟩], by decide +kernel⟩
private def b85 : PaidBatch .empty 7 := ⟨[
  .shared 129 51 42 ⟨.tilted, 1, 2, true, 203181493660639419⟩,
  .shared 129 52 44 ⟨.tilted, 1, 2, true, 211172451405277195⟩,
  .shared 129 53 46 ⟨.tilted, 1, 2, true, 219287355871975000⟩], by decide +kernel⟩
private def batches : List (PaidBatch .empty 7) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82, b83, b84, b85]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 129 21 2 = true := by decide +kernel
private theorem i23 : checks tiles 129 23 2 = true := by decide +kernel
private theorem i25 : checks tiles 129 25 2 = true := by decide +kernel
private theorem i27 : checks tiles 129 27 2 = true := by decide +kernel
private theorem i29 : checks tiles 129 29 2 = true := by decide +kernel
private theorem i31 : checks tiles 129 31 2 = true := by decide +kernel
private theorem i33 : checks tiles 129 33 2 = true := by decide +kernel
private theorem i35 : checks tiles 129 35 2 = true := by decide +kernel
private theorem i37 : checks tiles 129 37 2 = true := by decide +kernel
private theorem i39 : checks tiles 129 39 2 = true := by decide +kernel
private theorem i41 : checks tiles 129 41 2 = true := by decide +kernel
private theorem i43 : checks tiles 129 43 2 = true := by decide +kernel
private theorem i45 : checks tiles 129 45 2 = true := by decide +kernel
private theorem i47 : checks tiles 129 47 2 = true := by decide +kernel
private theorem i49 : checks tiles 129 49 2 = true := by decide +kernel
private theorem i51 : checks tiles 129 51 2 = true := by decide +kernel
private theorem i53 : checks tiles 129 53 1 = true := by decide +kernel
def receipt : Certificate .empty 7 := ⟨batches, checks_join i21 (checks_join i23 (checks_join i25 (checks_join i27 (checks_join i29 (checks_join i31 (checks_join i33 (checks_join i35 (checks_join i37 (checks_join i39 (checks_join i41 (checks_join i43 (checks_join i45 (checks_join i47 (checks_join i49 (checks_join i51 i53)))))))))))))))⟩
end Top7


end Low53At2389PriceTableEmpty7
