import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty10
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top10
private def b0 : PaidBatch .empty 10 := ⟨[
  .rectangle 10 30 69 41 37,
  .rectangle 14 42 71 47 36,
  .rectangle 16 48 71 53 40], by decide +kernel⟩
private def b1 : PaidBatch .empty 10 := ⟨[
  .rectangle 70 30 99 35 37,
  .rectangle 70 36 99 41 43,
  .rectangle 72 48 86 50 43], by decide +kernel⟩
private def b2 : PaidBatch .empty 10 := ⟨[
  .rectangle 72 51 86 53 45,
  .rectangle 72 42 100 44 43,
  .rectangle 72 45 100 47 46], by decide +kernel⟩
private def b3 : PaidBatch .empty 10 := ⟨[
  .rectangle 87 48 93 50 46,
  .rectangle 87 51 93 53 48,
  .rectangle 94 52 97 52 47], by decide +kernel⟩
private def b4 : PaidBatch .empty 10 := ⟨[
  .rectangle 94 53 97 53 48,
  .rectangle 94 48 100 49 47,
  .rectangle 94 50 100 50 47], by decide +kernel⟩
private def b5 : PaidBatch .empty 10 := ⟨[
  .rectangle 94 51 100 51 48,
  .point 98 53 46,
  .rectangle 98 52 99 52 48], by decide +kernel⟩
private def b6 : PaidBatch .empty 10 := ⟨[
  .point 99 53 46,
  .point 100 52 46,
  .point 100 53 47], by decide +kernel⟩
private def b7 : PaidBatch .empty 10 := ⟨[
  .rectangle 100 36 114 38 42,
  .rectangle 100 39 114 41 45,
  .rectangle 100 30 129 32 40], by decide +kernel⟩
private def b8 : PaidBatch .empty 10 := ⟨[
  .rectangle 100 33 129 35 43,
  .rectangle 101 51 101 51 48,
  .point 101 52 46], by decide +kernel⟩
private def b9 : PaidBatch .empty 10 := ⟨[
  .point 101 53 47,
  .rectangle 101 50 102 50 48,
  .rectangle 101 49 104 49 48], by decide +kernel⟩
private def b10 : PaidBatch .empty 10 := ⟨[
  .rectangle 101 45 108 46 47,
  .rectangle 101 47 108 47 47,
  .rectangle 101 48 108 48 48], by decide +kernel⟩
private def b11 : PaidBatch .empty 10 := ⟨[
  .rectangle 101 42 115 43 47,
  .rectangle 101 44 115 44 47,
  .point 102 51 46], by decide +kernel⟩
private def b12 : PaidBatch .empty 10 := ⟨[
  .point 102 52 47,
  .point 102 53 48,
  .rectangle 103 50 103 50 48], by decide +kernel⟩
private def b13 : PaidBatch .empty 10 := ⟨[
  .point 103 51 46,
  .point 103 52 47,
  .point 103 53 48], by decide +kernel⟩
private def b14 : PaidBatch .empty 10 := ⟨[
  .point 104 50 46,
  .point 104 51 47,
  .point 104 52 48], by decide +kernel⟩
private def b15 : PaidBatch .empty 10 := ⟨[
  .point 104 53 49,
  .rectangle 105 49 105 49 48,
  .point 105 50 46], by decide +kernel⟩
private def b16 : PaidBatch .empty 10 := ⟨[
  .point 105 51 47,
  .point 105 52 48,
  .point 105 53 49], by decide +kernel⟩
private def b17 : PaidBatch .empty 10 := ⟨[
  .point 106 49 46,
  .point 106 50 47,
  .point 106 51 48], by decide +kernel⟩
private def b18 : PaidBatch .empty 10 := ⟨[
  .shared 106 52 32 ⟨.tilted, 1, 2, true, 182907503577036348⟩,
  .point 106 53 49,
  .point 107 49 46], by decide +kernel⟩
private def b19 : PaidBatch .empty 10 := ⟨[
  .point 107 50 47,
  .point 107 51 48,
  .shared 107 52 32 ⟨.tilted, 1, 2, true, 184509923563326196⟩], by decide +kernel⟩
private def b20 : PaidBatch .empty 10 := ⟨[
  .shared 107 53 33 ⟨.tilted, 1, 2, true, 191871262395674011⟩,
  .point 108 49 46,
  .point 108 50 47], by decide +kernel⟩
private def b21 : PaidBatch .empty 10 := ⟨[
  .point 108 51 48,
  .shared 108 52 33 ⟨.tilted, 1, 2, true, 186112343549616044⟩,
  .shared 108 53 34 ⟨.tilted, 1, 2, false, 192520127427626764⟩], by decide +kernel⟩
private def b22 : PaidBatch .empty 10 := ⟨[
  .point 109 48 46,
  .point 109 49 47,
  .point 109 50 48], by decide +kernel⟩
private def b23 : PaidBatch .empty 10 := ⟨[
  .shared 109 51 32 ⟨.tilted, 1, 2, true, 180347689562210153⟩,
  .shared 109 52 33 ⟨.tilted, 1, 2, true, 187714763535905892⟩,
  .shared 109 53 33 ⟨.tilted, 1, 2, false, 188209690497063950⟩], by decide +kernel⟩
private def b24 : PaidBatch .empty 10 := ⟨[
  .rectangle 109 47 110 47 48,
  .rectangle 109 46 112 46 48,
  .rectangle 109 45 115 45 48], by decide +kernel⟩
private def b25 : PaidBatch .empty 10 := ⟨[
  .point 110 48 46,
  .point 110 49 47,
  .point 110 50 48], by decide +kernel⟩
private def b26 : PaidBatch .empty 10 := ⟨[
  .shared 110 51 32 ⟨.tilted, 1, 2, true, 181886631157781765⟩,
  .shared 110 52 34 ⟨.tilted, 1, 2, true, 189317183522195740⟩,
  .shared 110 53 34 ⟨.tilted, 1, 2, false, 189796917740609075⟩], by decide +kernel⟩
private def b27 : PaidBatch .empty 10 := ⟨[
  .point 111 47 46,
  .point 111 48 47,
  .point 111 49 48], by decide +kernel⟩
private def b28 : PaidBatch .empty 10 := ⟨[
  .shared 111 50 32 ⟨.tilted, 1, 2, true, 177444979155540620⟩,
  .shared 111 51 33 ⟨.tilted, 1, 2, true, 183425572753353377⟩,
  .shared 111 52 34 ⟨.tilted, 1, 2, false, 189338398901651948⟩], by decide +kernel⟩
private def b29 : PaidBatch .empty 10 := ⟨[
  .shared 111 53 34 ⟨.tilted, 1, 2, false, 191384144984154200⟩,
  .point 112 47 46,
  .point 112 48 47], by decide +kernel⟩
private def b30 : PaidBatch .empty 10 := ⟨[
  .point 112 49 48,
  .shared 112 50 32 ⟨.tilted, 1, 2, true, 177536562388017036⟩,
  .shared 112 51 34 ⟨.tilted, 1, 2, true, 184964514348924989⟩], by decide +kernel⟩
private def b31 : PaidBatch .empty 10 := ⟨[
  .shared 112 52 34 ⟨.tilted, 1, 2, false, 185883227177122664⟩,
  .shared 112 53 35 ⟨.tilted, 1, 2, false, 192971372227699325⟩,
  .rectangle 113 46 113 46 48], by decide +kernel⟩
private def b32 : PaidBatch .empty 10 := ⟨[
  .point 113 47 46,
  .point 113 48 47,
  .point 113 49 48], by decide +kernel⟩
private def b33 : PaidBatch .empty 10 := ⟨[
  .shared 113 50 33 ⟨.tilted, 1, 2, true, 179013307984386404⟩,
  .shared 113 51 34 ⟨.tilted, 1, 2, true, 186503455944496601⟩,
  .shared 113 52 34 ⟨.tilted, 1, 2, false, 187412693357724020⟩], by decide +kernel⟩
private def b34 : PaidBatch .empty 10 := ⟨[
  .shared 113 53 36 ⟨.tilted, 1, 2, false, 194558599471244450⟩,
  .point 114 46 46,
  .point 114 47 47], by decide +kernel⟩
private def b35 : PaidBatch .empty 10 := ⟨[
  .point 114 48 48,
  .shared 114 49 38 ⟨.tilted, 1, 1, false, 167980261960582565⟩,
  .shared 114 50 33 ⟨.tilted, 1, 2, true, 180490053580755772⟩], by decide +kernel⟩
private def b36 : PaidBatch .empty 10 := ⟨[
  .shared 114 51 35 ⟨.tilted, 1, 2, true, 188042397540068213⟩,
  .shared 114 52 35 ⟨.tilted, 1, 2, false, 188942159538325376⟩,
  .shared 114 53 36 ⟨.tilted, 1, 2, false, 196145826714789575⟩], by decide +kernel⟩
private def b37 : PaidBatch .empty 10 := ⟨[
  .point 115 46 46,
  .point 115 47 47,
  .point 115 48 48], by decide +kernel⟩
private def b38 : PaidBatch .empty 10 := ⟨[
  .shared 115 49 39 ⟨.tilted, 1, 1, false, 169342215714174578⟩,
  .shared 115 50 34 ⟨.tilted, 1, 2, true, 181966799177125140⟩,
  .shared 115 51 34 ⟨.tilted, 1, 2, false, 183318381471460395⟩], by decide +kernel⟩
private def b39 : PaidBatch .empty 10 := ⟨[
  .shared 115 52 35 ⟨.tilted, 1, 2, false, 190471625718926732⟩,
  .shared 115 53 37 ⟨.tilted, 1, 2, false, 197733053958334700⟩,
  .rectangle 115 39 122 40 46], by decide +kernel⟩
private def b40 : PaidBatch .empty 10 := ⟨[
  .rectangle 115 41 122 41 46,
  .rectangle 115 36 129 38 47,
  .rectangle 116 45 116 45 48], by decide +kernel⟩
private def b41 : PaidBatch .empty 10 := ⟨[
  .point 116 46 46,
  .point 116 47 47,
  .shared 116 48 38 ⟨.tilted, 1, 1, false, 163830219450462300⟩], by decide +kernel⟩
private def b42 : PaidBatch .empty 10 := ⟨[
  .shared 116 49 33 ⟨.tilted, 1, 2, true, 178068098426475763⟩,
  .shared 116 50 34 ⟨.tilted, 1, 2, true, 183443544773494508⟩,
  .shared 116 51 35 ⟨.tilted, 1, 2, false, 184791048382754976⟩], by decide +kernel⟩
private def b43 : PaidBatch .empty 10 := ⟨[
  .shared 116 52 36 ⟨.tilted, 1, 2, false, 192001091899528088⟩,
  .shared 116 53 37 ⟨.tilted, 1, 2, false, 199320281201879825⟩,
  .rectangle 116 44 119 44 48], by decide +kernel⟩
private def b44 : PaidBatch .empty 10 := ⟨[
  .rectangle 116 42 122 42 47,
  .rectangle 116 43 122 43 48,
  .point 117 45 46], by decide +kernel⟩
private def b45 : PaidBatch .empty 10 := ⟨[
  .point 117 46 47,
  .point 117 47 48,
  .shared 117 48 38 ⟨.tilted, 1, 1, false, 165138259315658520⟩], by decide +kernel⟩
private def b46 : PaidBatch .empty 10 := ⟨[
  .shared 117 49 34 ⟨.tilted, 1, 2, true, 177319251142741147⟩,
  .shared 117 50 35 ⟨.tilted, 1, 2, true, 184920290369863876⟩,
  .shared 117 51 35 ⟨.tilted, 1, 2, false, 186263715294049557⟩], by decide +kernel⟩
private def b47 : PaidBatch .empty 10 := ⟨[
  .shared 117 52 37 ⟨.tilted, 1, 2, false, 193530558080129444⟩,
  .shared 117 53 38 ⟨.tilted, 1, 2, false, 200907508445424950⟩,
  .point 118 45 46], by decide +kernel⟩
private def b48 : PaidBatch .empty 10 := ⟨[
  .point 118 46 47,
  .point 118 47 48,
  .shared 118 48 39 ⟨.tilted, 1, 1, false, 166446299180854740⟩], by decide +kernel⟩
private def b49 : PaidBatch .empty 10 := ⟨[
  .shared 118 49 34 ⟨.tilted, 1, 2, true, 178735083131424263⟩,
  .shared 118 50 36 ⟨.tilted, 1, 2, true, 186397035966233244⟩,
  .shared 118 51 36 ⟨.tilted, 1, 2, false, 187736382205344138⟩], by decide +kernel⟩
private def b50 : PaidBatch .empty 10 := ⟨[
  .shared 118 52 37 ⟨.tilted, 1, 2, false, 195060024260730800⟩,
  .shared 118 53 39 ⟨.tilted, 1, 2, false, 202494735688970075⟩,
  .point 119 45 46], by decide +kernel⟩
private def b51 : PaidBatch .empty 10 := ⟨[
  .point 119 46 47,
  .shared 119 47 38 ⟨.tilted, 1, 1, false, 160836449291870861⟩,
  .shared 119 48 39 ⟨.tilted, 1, 1, false, 167754339046050960⟩], by decide +kernel⟩
private def b52 : PaidBatch .empty 10 := ⟨[
  .shared 119 49 35 ⟨.tilted, 1, 2, true, 180150915120107379⟩,
  .shared 119 50 35 ⟨.tilted, 1, 2, false, 181942081648890380⟩,
  .shared 119 51 36 ⟨.tilted, 1, 2, false, 189209049116638719⟩], by decide +kernel⟩
private def b53 : PaidBatch .empty 10 := ⟨[
  .shared 119 52 38 ⟨.tilted, 1, 2, false, 196589490441332156⟩,
  .shared 119 53 39 ⟨.tilted, 1, 2, false, 204081962932515200⟩,
  .point 120 44 46], by decide +kernel⟩
private def b54 : PaidBatch .empty 10 := ⟨[
  .point 120 45 47,
  .point 120 46 48,
  .shared 120 47 38 ⟨.tilted, 0, 1, false, 162091537062308282⟩], by decide +kernel⟩
private def b55 : PaidBatch .empty 10 := ⟨[
  .shared 120 48 40 ⟨.tilted, 1, 1, false, 169062378911247180⟩,
  .shared 120 49 35 ⟨.tilted, 1, 2, true, 181566747108790495⟩,
  .shared 120 50 36 ⟨.tilted, 1, 2, false, 183358911084515180⟩], by decide +kernel⟩
private def b56 : PaidBatch .empty 10 := ⟨[
  .shared 120 51 37 ⟨.tilted, 1, 2, false, 190681716027933300⟩,
  .shared 120 52 38 ⟨.tilted, 1, 2, false, 198118956621933512⟩,
  .shared 120 53 40 ⟨.tilted, 1, 2, false, 205669190176060325⟩], by decide +kernel⟩
private def b57 : PaidBatch .empty 10 := ⟨[
  .point 121 44 46,
  .point 121 45 47,
  .point 121 46 48], by decide +kernel⟩
private def b58 : PaidBatch .empty 10 := ⟨[
  .shared 121 47 39 ⟨.tilted, 0, 1, false, 163346624832745703⟩,
  .shared 121 48 40 ⟨.tilted, 1, 1, false, 170370418776443400⟩,
  .shared 121 49 36 ⟨.tilted, 1, 2, true, 182982579097473611⟩], by decide +kernel⟩
private def b59 : PaidBatch .empty 10 := ⟨[
  .shared 121 50 36 ⟨.tilted, 1, 2, false, 184775740520139980⟩,
  .shared 121 51 38 ⟨.tilted, 1, 2, false, 192154382939227881⟩,
  .shared 121 52 39 ⟨.tilted, 1, 2, false, 199648422802534868⟩], by decide +kernel⟩
private def b60 : PaidBatch .empty 10 := ⟨[
  .shared 121 53 41 ⟨.tilted, 1, 2, false, 207256417419605450⟩,
  .point 122 44 46,
  .point 122 45 47], by decide +kernel⟩
private def b61 : PaidBatch .empty 10 := ⟨[
  .shared 122 46 38 ⟨.tilted, 0, 1, false, 157647096564404672⟩,
  .shared 122 47 39 ⟨.tilted, 0, 1, false, 164601712603183124⟩,
  .shared 122 48 41 ⟨.tilted, 0, 1, false, 171678458641639620⟩], by decide +kernel⟩
private def b62 : PaidBatch .empty 10 := ⟨[
  .shared 122 49 36 ⟨.tilted, 1, 2, true, 184398411086156727⟩,
  .shared 122 50 37 ⟨.tilted, 1, 2, false, 186192569955764780⟩,
  .shared 122 51 38 ⟨.tilted, 1, 2, false, 193627049850522462⟩], by decide +kernel⟩
private def b63 : PaidBatch .empty 10 := ⟨[
  .shared 122 52 40 ⟨.tilted, 1, 2, false, 201177888983136224⟩,
  .shared 122 53 41 ⟨.tilted, 1, 2, false, 208843644663150575⟩,
  .point 123 43 45], by decide +kernel⟩
private def b64 : PaidBatch .empty 10 := ⟨[
  .point 123 44 47,
  .point 123 45 48,
  .shared 123 46 39 ⟨.tilted, 0, 1, false, 158850194033720288⟩], by decide +kernel⟩
private def b65 : PaidBatch .empty 10 := ⟨[
  .shared 123 47 40 ⟨.tilted, 0, 1, false, 165856800373620545⟩,
  .shared 123 48 35 ⟨.tilted, 0, 2, true, 177995232867765984⟩,
  .shared 123 49 36 ⟨.tilted, 1, 2, false, 182701848165890276⟩], by decide +kernel⟩
private def b66 : PaidBatch .empty 10 := ⟨[
  .shared 123 50 37 ⟨.tilted, 1, 2, false, 187609399391389580⟩,
  .shared 123 51 39 ⟨.tilted, 1, 2, false, 195099716761817043⟩,
  .shared 123 52 40 ⟨.tilted, 1, 2, false, 202707355163737580⟩], by decide +kernel⟩
private def b67 : PaidBatch .empty 10 := ⟨[
  .shared 123 53 42 ⟨.tilted, 1, 2, false, 210430871906695700⟩,
  .rectangle 123 42 124 42 48,
  .rectangle 123 41 126 41 47], by decide +kernel⟩
private def b68 : PaidBatch .empty 10 := ⟨[
  .rectangle 123 39 129 39 46,
  .rectangle 123 40 129 40 47,
  .point 124 43 46], by decide +kernel⟩
private def b69 : PaidBatch .empty 10 := ⟨[
  .point 124 44 47,
  .point 124 45 48,
  .shared 124 46 39 ⟨.tilted, 0, 1, false, 160053291503035904⟩], by decide +kernel⟩
private def b70 : PaidBatch .empty 10 := ⟨[
  .shared 124 47 40 ⟨.tilted, 0, 1, false, 167111888144057966⟩,
  .shared 124 48 36 ⟨.tilted, 0, 2, true, 179351433640278840⟩,
  .shared 124 49 36 ⟨.tilted, 1, 2, false, 181599799496502695⟩], by decide +kernel⟩
private def b71 : PaidBatch .empty 10 := ⟨[
  .shared 124 50 38 ⟨.tilted, 1, 2, false, 189026228827014380⟩,
  .shared 124 51 39 ⟨.tilted, 1, 2, false, 196572383673111624⟩,
  .shared 124 52 41 ⟨.tilted, 1, 2, false, 204236821344338936⟩], by decide +kernel⟩
private def b72 : PaidBatch .empty 10 := ⟨[
  .shared 124 53 43 ⟨.tilted, 1, 2, false, 212018099150240825⟩,
  .rectangle 125 42 125 42 48,
  .point 125 43 46], by decide +kernel⟩
private def b73 : PaidBatch .empty 10 := ⟨[
  .point 125 44 47,
  .shared 125 45 38 ⟨.tilted, 0, 1, false, 154272260101252170⟩,
  .shared 125 46 39 ⟨.tilted, 0, 1, false, 161256388972351520⟩], by decide +kernel⟩
private def b74 : PaidBatch .empty 10 := ⟨[
  .shared 125 47 41 ⟨.tilted, 0, 1, false, 168366975914495387⟩,
  .shared 125 48 36 ⟨.tilted, 0, 2, true, 180707634412791696⟩,
  .shared 125 49 37 ⟨.tilted, 0, 2, false, 182961753250094708⟩], by decide +kernel⟩
private def b75 : PaidBatch .empty 10 := ⟨[
  .shared 125 50 38 ⟨.tilted, 1, 2, false, 190443058262639180⟩,
  .shared 125 51 40 ⟨.tilted, 1, 2, false, 198045050584406205⟩,
  .shared 125 52 42 ⟨.tilted, 1, 2, false, 205766287524940292⟩], by decide +kernel⟩
private def b76 : PaidBatch .empty 10 := ⟨[
  .shared 125 53 43 ⟨.tilted, 1, 2, false, 213605326393785950⟩,
  .point 126 42 45,
  .point 126 43 47], by decide +kernel⟩
private def b77 : PaidBatch .empty 10 := ⟨[
  .point 126 44 48,
  .shared 126 45 39 ⟨.tilted, 0, 1, false, 155424329063082975⟩,
  .shared 126 46 40 ⟨.tilted, 0, 1, false, 162459486441667136⟩], by decide +kernel⟩
private def b78 : PaidBatch .empty 10 := ⟨[
  .shared 126 47 41 ⟨.tilted, 0, 1, false, 169622063684932808⟩,
  .shared 126 48 37 ⟨.tilted, 0, 2, true, 182063835185304552⟩,
  .shared 126 49 37 ⟨.tilted, 0, 2, false, 184323707003686721⟩], by decide +kernel⟩
private def b79 : PaidBatch .empty 10 := ⟨[
  .shared 126 50 39 ⟨.tilted, 1, 2, false, 191859887698263980⟩,
  .shared 126 51 41 ⟨.tilted, 1, 2, false, 199517717495700786⟩,
  .shared 126 52 42 ⟨.tilted, 1, 2, false, 207295753705541648⟩], by decide +kernel⟩
private def b80 : PaidBatch .empty 10 := ⟨[
  .shared 126 53 44 ⟨.tilted, 1, 2, false, 215192553637331075⟩,
  .point 127 42 46,
  .point 127 43 47], by decide +kernel⟩
private def b81 : PaidBatch .empty 10 := ⟨[
  .point 127 44 48,
  .shared 127 45 39 ⟨.tilted, 0, 1, false, 156576398024913780⟩,
  .shared 127 46 40 ⟨.tilted, 0, 1, false, 163662583910982752⟩], by decide +kernel⟩
private def b82 : PaidBatch .empty 10 := ⟨[
  .shared 127 47 42 ⟨.tilted, 0, 1, false, 170877151455370229⟩,
  .shared 127 48 38 ⟨.tilted, 0, 2, true, 183420035957817408⟩,
  .shared 127 49 38 ⟨.tilted, 0, 2, false, 185685660757278734⟩], by decide +kernel⟩
private def b83 : PaidBatch .empty 10 := ⟨[
  .shared 127 50 40 ⟨.tilted, 1, 2, false, 193276717133888780⟩,
  .shared 127 51 41 ⟨.tilted, 1, 2, false, 200990384406995367⟩,
  .shared 127 52 43 ⟨.tilted, 1, 2, false, 208825219886143004⟩], by decide +kernel⟩
private def b84 : PaidBatch .empty 10 := ⟨[
  .shared 127 53 45 ⟨.tilted, 1, 2, false, 216779780880876200⟩,
  .rectangle 127 41 128 41 48,
  .point 128 42 46], by decide +kernel⟩
private def b85 : PaidBatch .empty 10 := ⟨[
  .point 128 43 47,
  .point 128 44 48,
  .shared 128 45 39 ⟨.tilted, 0, 1, false, 157728466986744585⟩], by decide +kernel⟩
private def b86 : PaidBatch .empty 10 := ⟨[
  .shared 128 46 41 ⟨.tilted, 0, 1, false, 164865681380298368⟩,
  .shared 128 47 42 ⟨.tilted, 0, 1, false, 172132239225807650⟩,
  .shared 128 48 38 ⟨.tilted, 0, 2, true, 184776236730330264⟩], by decide +kernel⟩
private def b87 : PaidBatch .empty 10 := ⟨[
  .shared 128 49 39 ⟨.tilted, 0, 2, false, 187047614510870747⟩,
  .shared 128 50 40 ⟨.tilted, 0, 2, false, 194693546569513580⟩,
  .shared 128 51 42 ⟨.tilted, 1, 2, false, 202463051318289948⟩], by decide +kernel⟩
private def b88 : PaidBatch .empty 10 := ⟨[
  .shared 128 52 44 ⟨.tilted, 1, 2, false, 210354686066744360⟩,
  .shared 128 53 45 ⟨.tilted, 1, 2, false, 218367008124421325⟩,
  .point 129 41 45], by decide +kernel⟩
private def b89 : PaidBatch .empty 10 := ⟨[
  .point 129 42 46,
  .point 129 43 48,
  .shared 129 44 39 ⟨.tilted, 0, 1, false, 151824040983584780⟩], by decide +kernel⟩
private def b90 : PaidBatch .empty 10 := ⟨[
  .shared 129 45 40 ⟨.tilted, 0, 1, false, 158880535948575390⟩,
  .shared 129 46 41 ⟨.tilted, 0, 1, false, 166068778849613984⟩,
  .shared 129 47 43 ⟨.tilted, 0, 1, false, 173387326996245071⟩], by decide +kernel⟩
private def b91 : PaidBatch .empty 10 := ⟨[
  .shared 129 48 39 ⟨.tilted, 0, 2, true, 186132437502843120⟩,
  .shared 129 49 39 ⟨.tilted, 0, 2, false, 188409568264462760⟩,
  .shared 129 50 41 ⟨.tilted, 0, 2, false, 196110376005138380⟩], by decide +kernel⟩
private def b92 : PaidBatch .empty 10 := ⟨[
  .shared 129 51 43 ⟨.tilted, 1, 2, false, 203935718229584529⟩,
  .shared 129 52 44 ⟨.tilted, 1, 2, false, 211884152247345716⟩,
  .shared 129 53 46 ⟨.tilted, 1, 2, false, 219954235367966450⟩], by decide +kernel⟩
private def batches : List (PaidBatch .empty 10) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82, b83, b84, b85, b86, b87, b88, b89, b90, b91, b92]
private abbrev tiles := tilesOf batches
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
def receipt : Certificate .empty 10 := ⟨batches, checks_join i30 (checks_join i32 (checks_join i34 (checks_join i36 (checks_join i38 (checks_join i40 (checks_join i42 (checks_join i44 (checks_join i46 (checks_join i48 (checks_join i50 i52))))))))))⟩
end Top10


end Low53At2389PriceTableEmpty10
