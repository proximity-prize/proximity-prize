import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty11
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top11
private def b0 : PaidBatch .empty 11 := ⟨[
  .rectangle 11 33 70 43 38,
  .rectangle 15 44 72 53 45,
  .rectangle 71 33 100 38 40], by decide +kernel⟩
private def b1 : PaidBatch .empty 11 := ⟨[
  .rectangle 71 39 100 43 44,
  .rectangle 73 44 87 48 43,
  .rectangle 73 49 87 53 48], by decide +kernel⟩
private def b2 : PaidBatch .empty 11 := ⟨[
  .rectangle 88 49 94 51 47,
  .rectangle 88 52 94 53 48,
  .rectangle 88 44 101 46 46], by decide +kernel⟩
private def b3 : PaidBatch .empty 11 := ⟨[
  .rectangle 88 47 101 48 47,
  .rectangle 95 53 96 53 48,
  .rectangle 95 52 98 52 48], by decide +kernel⟩
private def b4 : PaidBatch .empty 11 := ⟨[
  .rectangle 95 49 101 50 48,
  .rectangle 95 51 101 51 48,
  .point 97 53 46], by decide +kernel⟩
private def b5 : PaidBatch .empty 11 := ⟨[
  .point 98 53 46,
  .point 99 52 46,
  .point 99 53 47], by decide +kernel⟩
private def b6 : PaidBatch .empty 11 := ⟨[
  .point 100 52 46,
  .point 100 53 47,
  .point 101 52 47], by decide +kernel⟩
private def b7 : PaidBatch .empty 11 := ⟨[
  .point 101 53 48,
  .rectangle 101 36 115 38 42,
  .rectangle 101 39 115 41 46], by decide +kernel⟩
private def b8 : PaidBatch .empty 11 := ⟨[
  .rectangle 101 42 115 43 47,
  .rectangle 101 33 129 35 43,
  .point 102 51 46], by decide +kernel⟩
private def b9 : PaidBatch .empty 11 := ⟨[
  .point 102 52 47,
  .point 102 53 48,
  .rectangle 102 50 103 50 48], by decide +kernel⟩
private def b10 : PaidBatch .empty 11 := ⟨[
  .rectangle 102 49 105 49 48,
  .rectangle 102 44 108 45 46,
  .rectangle 102 46 108 46 46], by decide +kernel⟩
private def b11 : PaidBatch .empty 11 := ⟨[
  .rectangle 102 47 108 47 47,
  .rectangle 102 48 108 48 48,
  .point 103 51 46], by decide +kernel⟩
private def b12 : PaidBatch .empty 11 := ⟨[
  .point 103 52 47,
  .point 103 53 48,
  .point 104 50 46], by decide +kernel⟩
private def b13 : PaidBatch .empty 11 := ⟨[
  .point 104 51 47,
  .point 104 52 48,
  .point 104 53 49], by decide +kernel⟩
private def b14 : PaidBatch .empty 11 := ⟨[
  .point 105 50 46,
  .point 105 51 47,
  .point 105 52 48], by decide +kernel⟩
private def b15 : PaidBatch .empty 11 := ⟨[
  .point 105 53 49,
  .point 106 49 46,
  .point 106 50 47], by decide +kernel⟩
private def b16 : PaidBatch .empty 11 := ⟨[
  .point 106 51 48,
  .shared 106 52 32 ⟨.tilted, 1, 2, true, 184581656234520897⟩,
  .shared 106 53 32 ⟨.tilted, 1, 2, false, 186958109416853196⟩], by decide +kernel⟩
private def b17 : PaidBatch .empty 11 := ⟨[
  .point 107 49 46,
  .point 107 50 47,
  .point 107 51 48], by decide +kernel⟩
private def b18 : PaidBatch .empty 11 := ⟨[
  .shared 107 52 32 ⟨.tilted, 1, 2, true, 186184076220810745⟩,
  .shared 107 53 33 ⟨.tilted, 1, 2, false, 188565374024632704⟩,
  .point 108 49 47], by decide +kernel⟩
private def b19 : PaidBatch .empty 11 := ⟨[
  .point 108 50 48,
  .shared 108 51 32 ⟨.tilted, 1, 2, true, 180318647672409543⟩,
  .shared 108 52 32 ⟨.tilted, 1, 2, false, 183072150636629080⟩], by decide +kernel⟩
private def b20 : PaidBatch .empty 11 := ⟨[
  .shared 108 53 33 ⟨.tilted, 1, 2, false, 190172638632412212⟩,
  .point 109 48 46,
  .point 109 49 47], by decide +kernel⟩
private def b21 : PaidBatch .empty 11 := ⟨[
  .point 109 50 48,
  .shared 109 51 32 ⟨.tilted, 1, 2, true, 181857589267981155⟩,
  .shared 109 52 33 ⟨.tilted, 1, 2, false, 184620692387827825⟩], by decide +kernel⟩
private def b22 : PaidBatch .empty 11 := ⟨[
  .shared 109 53 34 ⟨.tilted, 1, 2, false, 191779903240191720⟩,
  .rectangle 109 47 110 47 48,
  .rectangle 109 46 112 46 48], by decide +kernel⟩
private def b23 : PaidBatch .empty 11 := ⟨[
  .rectangle 109 44 115 44 47,
  .rectangle 109 45 115 45 48,
  .point 110 48 46], by decide +kernel⟩
private def b24 : PaidBatch .empty 11 := ⟨[
  .point 110 49 47,
  .point 110 50 48,
  .shared 110 51 33 ⟨.tilted, 1, 2, true, 183396530863552767⟩], by decide +kernel⟩
private def b25 : PaidBatch .empty 11 := ⟨[
  .shared 110 52 33 ⟨.tilted, 1, 2, false, 186169234139026570⟩,
  .shared 110 53 34 ⟨.tilted, 1, 2, false, 193387167847971228⟩,
  .point 111 47 46], by decide +kernel⟩
private def b26 : PaidBatch .empty 11 := ⟨[
  .point 111 48 47,
  .point 111 49 48,
  .shared 111 50 33 ⟨.tilted, 1, 2, true, 182376102200544854⟩], by decide +kernel⟩
private def b27 : PaidBatch .empty 11 := ⟨[
  .shared 111 51 33 ⟨.tilted, 1, 2, false, 180552829893310503⟩,
  .shared 111 52 34 ⟨.tilted, 1, 2, false, 187717775890225315⟩,
  .shared 111 53 35 ⟨.tilted, 1, 2, false, 194994432455750736⟩], by decide +kernel⟩
private def b28 : PaidBatch .empty 11 := ⟨[
  .point 112 47 46,
  .point 112 48 47,
  .point 112 49 48], by decide +kernel⟩
private def b29 : PaidBatch .empty 11 := ⟨[
  .shared 112 50 32 ⟨.tilted, 1, 2, true, 178890704985867940⟩,
  .shared 112 51 33 ⟨.tilted, 1, 2, false, 182043610581565479⟩,
  .shared 112 52 34 ⟨.tilted, 1, 2, false, 189266317641424060⟩], by decide +kernel⟩
private def b30 : PaidBatch .empty 11 := ⟨[
  .shared 112 53 36 ⟨.tilted, 1, 2, false, 196601697063530244⟩,
  .rectangle 113 46 113 46 48,
  .point 113 47 46], by decide +kernel⟩
private def b31 : PaidBatch .empty 11 := ⟨[
  .point 113 48 47,
  .shared 113 49 38 ⟨.tilted, 1, 1, false, 169320128253691510⟩,
  .shared 113 50 33 ⟨.tilted, 1, 2, true, 180367450582237308⟩], by decide +kernel⟩
private def b32 : PaidBatch .empty 11 := ⟨[
  .shared 113 51 34 ⟨.tilted, 1, 2, false, 183534391269820455⟩,
  .shared 113 52 35 ⟨.tilted, 1, 2, false, 190814859392622805⟩,
  .shared 113 53 36 ⟨.tilted, 1, 2, false, 198208961671309752⟩], by decide +kernel⟩
private def b33 : PaidBatch .empty 11 := ⟨[
  .point 114 46 46,
  .point 114 47 47,
  .point 114 48 48], by decide +kernel⟩
private def b34 : PaidBatch .empty 11 := ⟨[
  .shared 114 49 38 ⟨.tilted, 1, 1, false, 170698272196969930⟩,
  .shared 114 50 34 ⟨.tilted, 1, 2, true, 181844196178606676⟩,
  .shared 114 51 34 ⟨.tilted, 1, 2, false, 185025171958075431⟩], by decide +kernel⟩
private def b35 : PaidBatch .empty 11 := ⟨[
  .shared 114 52 35 ⟨.tilted, 1, 2, false, 192363401143821550⟩,
  .shared 114 53 37 ⟨.tilted, 1, 2, false, 199816226279089260⟩,
  .point 115 46 46], by decide +kernel⟩
private def b36 : PaidBatch .empty 11 := ⟨[
  .point 115 47 47,
  .point 115 48 48,
  .shared 115 49 39 ⟨.tilted, 1, 1, false, 172076416140248350⟩], by decide +kernel⟩
private def b37 : PaidBatch .empty 11 := ⟨[
  .shared 115 50 33 ⟨.tilted, 1, 2, false, 179236962831254595⟩,
  .shared 115 51 35 ⟨.tilted, 1, 2, false, 186515952646330407⟩,
  .shared 115 52 36 ⟨.tilted, 1, 2, false, 193911942895020295⟩], by decide +kernel⟩
private def b38 : PaidBatch .empty 11 := ⟨[
  .shared 115 53 37 ⟨.tilted, 1, 2, false, 201423490886868768⟩,
  .rectangle 116 45 116 45 48,
  .point 116 46 46], by decide +kernel⟩
private def b39 : PaidBatch .empty 11 := ⟨[
  .point 116 47 48,
  .shared 116 48 38 ⟨.tilted, 1, 1, false, 166359023525012796⟩,
  .shared 116 49 34 ⟨.tilted, 1, 2, true, 182736224339937490⟩], by decide +kernel⟩
private def b40 : PaidBatch .empty 11 := ⟨[
  .shared 116 50 34 ⟨.tilted, 1, 2, false, 180670944250202796⟩,
  .shared 116 51 35 ⟨.tilted, 1, 2, false, 188006733334585383⟩,
  .shared 116 52 37 ⟨.tilted, 1, 2, false, 195460484646219040⟩], by decide +kernel⟩
private def b41 : PaidBatch .empty 11 := ⟨[
  .shared 116 53 38 ⟨.tilted, 1, 2, false, 203030755494648276⟩,
  .rectangle 116 44 119 44 48,
  .rectangle 116 39 122 40 46], by decide +kernel⟩
private def b42 : PaidBatch .empty 11 := ⟨[
  .rectangle 116 41 122 41 46,
  .rectangle 116 42 122 42 47,
  .rectangle 116 43 122 43 48], by decide +kernel⟩
private def b43 : PaidBatch .empty 11 := ⟨[
  .rectangle 116 36 129 38 47,
  .point 117 45 46,
  .point 117 46 47], by decide +kernel⟩
private def b44 : PaidBatch .empty 11 := ⟨[
  .point 117 47 48,
  .shared 117 48 39 ⟨.tilted, 1, 1, false, 167682291786258429⟩,
  .shared 117 49 34 ⟨.tilted, 1, 2, true, 178526132476465398⟩], by decide +kernel⟩
private def b45 : PaidBatch .empty 11 := ⟨[
  .shared 117 50 34 ⟨.tilted, 1, 2, false, 182104925669150997⟩,
  .shared 117 51 36 ⟨.tilted, 1, 2, false, 189497514022840359⟩,
  .shared 117 52 37 ⟨.tilted, 1, 2, false, 197009026397417785⟩], by decide +kernel⟩
private def b46 : PaidBatch .empty 11 := ⟨[
  .shared 117 53 39 ⟨.tilted, 1, 2, false, 204638020102427784⟩,
  .point 118 45 46,
  .point 118 46 47], by decide +kernel⟩
private def b47 : PaidBatch .empty 11 := ⟨[
  .point 118 47 48,
  .shared 118 48 39 ⟨.tilted, 1, 1, false, 169005560047504062⟩,
  .shared 118 49 34 ⟨.tilted, 1, 2, true, 179941964465148514⟩], by decide +kernel⟩
private def b48 : PaidBatch .empty 11 := ⟨[
  .shared 118 50 35 ⟨.tilted, 1, 2, false, 183538907088099198⟩,
  .shared 118 51 36 ⟨.tilted, 1, 2, false, 190988294711095335⟩,
  .shared 118 52 38 ⟨.tilted, 1, 2, false, 198557568148616530⟩], by decide +kernel⟩
private def b49 : PaidBatch .empty 11 := ⟨[
  .shared 118 53 39 ⟨.tilted, 1, 2, false, 206245284710207292⟩,
  .point 119 45 46,
  .point 119 46 48], by decide +kernel⟩
private def b50 : PaidBatch .empty 11 := ⟨[
  .shared 119 47 38 ⟨.tilted, 1, 1, false, 163193840383665885⟩,
  .shared 119 48 40 ⟨.tilted, 1, 1, false, 170328828308749695⟩,
  .shared 119 49 34 ⟨.tilted, 1, 2, false, 177588991913362030⟩], by decide +kernel⟩
private def b51 : PaidBatch .empty 11 := ⟨[
  .shared 119 50 36 ⟨.tilted, 1, 2, false, 184972888507047399⟩,
  .shared 119 51 37 ⟨.tilted, 1, 2, false, 192479075399350311⟩,
  .shared 119 52 38 ⟨.tilted, 1, 2, false, 200106109899815275⟩], by decide +kernel⟩
private def b52 : PaidBatch .empty 11 := ⟨[
  .shared 119 53 40 ⟨.tilted, 1, 2, false, 207852549317986800⟩,
  .point 120 44 46,
  .point 120 45 47], by decide +kernel⟩
private def b53 : PaidBatch .empty 11 := ⟨[
  .point 120 46 48,
  .shared 120 47 39 ⟨.tilted, 0, 1, false, 164463194756515725⟩,
  .shared 120 48 40 ⟨.tilted, 1, 1, false, 171652096569995328⟩], by decide +kernel⟩
private def b54 : PaidBatch .empty 11 := ⟨[
  .shared 120 49 35 ⟨.tilted, 1, 2, false, 178967135856640450⟩,
  .shared 120 50 36 ⟨.tilted, 1, 2, false, 186406869925995600⟩,
  .shared 120 51 38 ⟨.tilted, 1, 2, false, 193969856087605287⟩], by decide +kernel⟩
private def b55 : PaidBatch .empty 11 := ⟨[
  .shared 120 52 39 ⟨.tilted, 1, 2, false, 201654651651014020⟩,
  .shared 120 53 41 ⟨.tilted, 1, 2, false, 209459813925766308⟩,
  .point 121 44 46], by decide +kernel⟩
private def b56 : PaidBatch .empty 11 := ⟨[
  .point 121 45 47,
  .point 121 46 48,
  .shared 121 47 39 ⟨.tilted, 0, 1, false, 165732549129365565⟩], by decide +kernel⟩
private def b57 : PaidBatch .empty 11 := ⟨[
  .shared 121 48 41 ⟨.tilted, 1, 1, false, 172975364831240961⟩,
  .shared 121 49 35 ⟨.tilted, 1, 2, false, 180345279799918870⟩,
  .shared 121 50 37 ⟨.tilted, 1, 2, false, 187840851344943801⟩], by decide +kernel⟩
private def b58 : PaidBatch .empty 11 := ⟨[
  .shared 121 51 38 ⟨.tilted, 1, 2, false, 195460636775860263⟩,
  .shared 121 52 40 ⟨.tilted, 1, 2, false, 203203193402212765⟩,
  .shared 121 53 41 ⟨.tilted, 1, 2, false, 211067078533545816⟩], by decide +kernel⟩
private def b59 : PaidBatch .empty 11 := ⟨[
  .point 122 44 46,
  .point 122 45 47,
  .shared 122 46 38 ⟨.tilted, 0, 1, false, 159834677662839214⟩], by decide +kernel⟩
private def b60 : PaidBatch .empty 11 := ⟨[
  .shared 122 47 40 ⟨.tilted, 0, 1, false, 167001903502215405⟩,
  .shared 122 48 41 ⟨.tilted, 0, 1, false, 174298633092486594⟩,
  .shared 122 49 36 ⟨.tilted, 1, 2, false, 181723423743197290⟩], by decide +kernel⟩
private def b61 : PaidBatch .empty 11 := ⟨[
  .shared 122 50 37 ⟨.tilted, 1, 2, false, 189274832763892002⟩,
  .shared 122 51 39 ⟨.tilted, 1, 2, false, 196951417464115239⟩,
  .shared 122 52 40 ⟨.tilted, 1, 2, false, 204751735153411510⟩], by decide +kernel⟩
private def b62 : PaidBatch .empty 11 := ⟨[
  .shared 122 53 42 ⟨.tilted, 1, 2, false, 212674343141325324⟩,
  .point 123 43 45,
  .point 123 44 47], by decide +kernel⟩
private def b63 : PaidBatch .empty 11 := ⟨[
  .point 123 45 48,
  .shared 123 46 39 ⟨.tilted, 0, 1, false, 161051079940930255⟩,
  .shared 123 47 40 ⟨.tilted, 0, 1, false, 168271257875065245⟩], by decide +kernel⟩
private def b64 : PaidBatch .empty 11 := ⟨[
  .shared 123 48 35 ⟨.tilted, 0, 2, true, 179063348781157031⟩,
  .shared 123 49 36 ⟨.tilted, 1, 2, false, 183101567686475710⟩,
  .shared 123 50 38 ⟨.tilted, 1, 2, false, 190708814182840203⟩], by decide +kernel⟩
private def b65 : PaidBatch .empty 11 := ⟨[
  .shared 123 51 39 ⟨.tilted, 1, 2, false, 198442198152370215⟩,
  .shared 123 52 41 ⟨.tilted, 1, 2, false, 206300276904610255⟩,
  .shared 123 53 43 ⟨.tilted, 1, 2, false, 214281607749104832⟩], by decide +kernel⟩
private def b66 : PaidBatch .empty 11 := ⟨[
  .rectangle 123 42 124 42 48,
  .rectangle 123 39 129 39 46,
  .rectangle 123 40 129 40 47], by decide +kernel⟩
private def b67 : PaidBatch .empty 11 := ⟨[
  .rectangle 123 41 129 41 48,
  .point 124 43 46,
  .point 124 44 47], by decide +kernel⟩
private def b68 : PaidBatch .empty 11 := ⟨[
  .point 124 45 48,
  .shared 124 46 39 ⟨.tilted, 0, 1, false, 162267482219021296⟩,
  .shared 124 47 41 ⟨.tilted, 0, 1, false, 169540612247915085⟩], by decide +kernel⟩
private def b69 : PaidBatch .empty 11 := ⟨[
  .shared 124 48 36 ⟨.tilted, 0, 2, true, 180419549553669887⟩,
  .shared 124 49 37 ⟨.tilted, 1, 2, false, 184479711629754130⟩,
  .shared 124 50 38 ⟨.tilted, 1, 2, false, 192142795601788404⟩], by decide +kernel⟩
private def b70 : PaidBatch .empty 11 := ⟨[
  .shared 124 51 40 ⟨.tilted, 1, 2, false, 199932978840625191⟩,
  .shared 124 52 42 ⟨.tilted, 1, 2, false, 207848818655809000⟩,
  .shared 124 53 43 ⟨.tilted, 1, 2, false, 215888872356884340⟩], by decide +kernel⟩
private def b71 : PaidBatch .empty 11 := ⟨[
  .rectangle 125 42 125 42 48,
  .point 125 43 46,
  .point 125 44 47], by decide +kernel⟩
private def b72 : PaidBatch .empty 11 := ⟨[
  .shared 125 45 38 ⟨.tilted, 0, 1, false, 156291634195721220⟩,
  .shared 125 46 40 ⟨.tilted, 0, 1, false, 163483884497112337⟩,
  .shared 125 47 41 ⟨.tilted, 0, 1, false, 170809966620764925⟩], by decide +kernel⟩
private def b73 : PaidBatch .empty 11 := ⟨[
  .shared 125 48 37 ⟨.tilted, 0, 2, true, 181775750326182743⟩,
  .shared 125 49 37 ⟨.tilted, 0, 2, false, 185857855573032550⟩,
  .shared 125 50 39 ⟨.tilted, 1, 2, false, 193576777020736605⟩], by decide +kernel⟩
private def b74 : PaidBatch .empty 11 := ⟨[
  .shared 125 51 41 ⟨.tilted, 1, 2, false, 201423759528880167⟩,
  .shared 125 52 42 ⟨.tilted, 1, 2, false, 209397360407007745⟩,
  .shared 125 53 44 ⟨.tilted, 1, 2, false, 217496136964663848⟩], by decide +kernel⟩
private def b75 : PaidBatch .empty 11 := ⟨[
  .point 126 42 45,
  .point 126 43 46,
  .point 126 44 48], by decide +kernel⟩
private def b76 : PaidBatch .empty 11 := ⟨[
  .shared 126 45 39 ⟨.tilted, 0, 1, false, 157456046172690456⟩,
  .shared 126 46 40 ⟨.tilted, 0, 1, false, 164700286775203378⟩,
  .shared 126 47 42 ⟨.tilted, 0, 1, false, 172079320993614765⟩], by decide +kernel⟩
private def b77 : PaidBatch .empty 11 := ⟨[
  .shared 126 48 36 ⟨.tilted, 0, 2, false, 179591706137469126⟩,
  .shared 126 49 38 ⟨.tilted, 0, 2, false, 187235999516310970⟩,
  .shared 126 50 40 ⟨.tilted, 1, 2, false, 195010758439684806⟩], by decide +kernel⟩
private def b78 : PaidBatch .empty 11 := ⟨[
  .shared 126 51 41 ⟨.tilted, 1, 2, false, 202914540217135143⟩,
  .shared 126 52 43 ⟨.tilted, 1, 2, false, 210945902158206490⟩,
  .shared 126 53 45 ⟨.tilted, 1, 2, false, 219103401572443356⟩], by decide +kernel⟩
private def b79 : PaidBatch .empty 11 := ⟨[
  .point 127 42 46,
  .point 127 43 47,
  .point 127 44 48], by decide +kernel⟩
private def b80 : PaidBatch .empty 11 := ⟨[
  .shared 127 45 39 ⟨.tilted, 0, 1, false, 158620458149659692⟩,
  .shared 127 46 41 ⟨.tilted, 0, 1, false, 165916689053294419⟩,
  .shared 127 47 42 ⟨.tilted, 0, 1, false, 173348675366464605⟩], by decide +kernel⟩
private def b81 : PaidBatch .empty 11 := ⟨[
  .shared 127 48 37 ⟨.tilted, 0, 2, false, 180914974398714759⟩,
  .shared 127 49 39 ⟨.tilted, 0, 2, false, 188614143459589390⟩,
  .shared 127 50 40 ⟨.tilted, 1, 2, false, 196444739858633007⟩], by decide +kernel⟩
private def b82 : PaidBatch .empty 11 := ⟨[
  .shared 127 51 42 ⟨.tilted, 1, 2, false, 204405320905390119⟩,
  .shared 127 52 44 ⟨.tilted, 1, 2, false, 212494443909405235⟩,
  .shared 127 53 46 ⟨.tilted, 1, 2, false, 220710666180222864⟩], by decide +kernel⟩
private def b83 : PaidBatch .empty 11 := ⟨[
  .point 128 42 46,
  .point 128 43 47,
  .point 128 44 48], by decide +kernel⟩
private def b84 : PaidBatch .empty 11 := ⟨[
  .shared 128 45 40 ⟨.tilted, 0, 1, false, 159784870126628928⟩,
  .shared 128 46 41 ⟨.tilted, 0, 1, false, 167133091331385460⟩,
  .shared 128 47 43 ⟨.tilted, 0, 1, false, 174618029739314445⟩], by decide +kernel⟩
private def b85 : PaidBatch .empty 11 := ⟨[
  .shared 128 48 37 ⟨.tilted, 0, 2, false, 182238242659960392⟩,
  .shared 128 49 39 ⟨.tilted, 0, 2, false, 189992287402867810⟩,
  .shared 128 50 41 ⟨.tilted, 0, 2, false, 197878721277581208⟩], by decide +kernel⟩
private def b86 : PaidBatch .empty 11 := ⟨[
  .shared 128 51 43 ⟨.tilted, 1, 2, false, 205896101593645095⟩,
  .shared 128 52 44 ⟨.tilted, 1, 2, false, 214042985660603980⟩,
  .shared 128 53 46 ⟨.tilted, 1, 2, false, 222317930788002372⟩], by decide +kernel⟩
private def b87 : PaidBatch .empty 11 := ⟨[
  .point 129 42 46,
  .point 129 43 47,
  .shared 129 44 39 ⟨.tilted, 0, 1, false, 153688192284984765⟩], by decide +kernel⟩
private def b88 : PaidBatch .empty 11 := ⟨[
  .shared 129 45 40 ⟨.tilted, 0, 1, false, 160949282103598164⟩,
  .shared 129 46 42 ⟨.tilted, 0, 1, false, 168349493609476501⟩,
  .shared 129 47 43 ⟨.tilted, 0, 1, false, 175887384112164285⟩], by decide +kernel⟩
private def b89 : PaidBatch .empty 11 := ⟨[
  .shared 129 48 38 ⟨.tilted, 0, 2, false, 183561510921206025⟩,
  .shared 129 49 40 ⟨.tilted, 0, 2, false, 191370431346146230⟩,
  .shared 129 50 41 ⟨.tilted, 0, 2, false, 199312702696529409⟩], by decide +kernel⟩
private def b90 : PaidBatch .empty 11 := ⟨[
  .shared 129 51 43 ⟨.tilted, 1, 2, false, 207386882281900071⟩,
  .shared 129 52 45 ⟨.tilted, 1, 2, false, 215591527411802725⟩,
  .shared 129 53 47 ⟨.tilted, 1, 2, false, 223925195395781880⟩], by decide +kernel⟩
private def batches : List (PaidBatch .empty 11) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82, b83, b84, b85, b86, b87, b88, b89, b90]
private abbrev tiles := tilesOf batches
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
def receipt : Certificate .empty 11 := ⟨batches, checks_join i33 (checks_join i35 (checks_join i37 (checks_join i39 (checks_join i41 (checks_join i43 (checks_join i45 (checks_join i47 (checks_join i49 (checks_join i51 i53)))))))))⟩
end Top11


end Low53At2389PriceTableEmpty11
