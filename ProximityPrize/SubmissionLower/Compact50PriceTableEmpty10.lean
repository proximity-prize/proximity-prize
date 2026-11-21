import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableEmpty10
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top10
private def batch0 : PaidBatch .empty 10 := ⟨[
  .rectangle 10 30 88 37 37,
  .rectangle 13 38 73 45 37,
  .rectangle 16 46 76 53 44,
  .rectangle 74 38 103 42 44,
  .rectangle 74 43 96 47 46,
  .rectangle 77 48 89 52 47], by decide +kernel⟩
private def batch1 : PaidBatch .empty 10 := ⟨[
  .rectangle 77 53 95 53 47,
  .rectangle 89 30 124 34 43,
  .rectangle 89 35 117 38 44,
  .rectangle 90 48 101 49 47,
  .rectangle 90 50 97 51 47,
  .rectangle 90 52 97 52 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 10 := ⟨[
  .point 96 53 47,
  .rectangle 97 43 111 44 46,
  .rectangle 97 45 108 46 47,
  .rectangle 97 47 103 48 47,
  .point 97 53 47,
  .rectangle 98 50 101 50 47], by decide +kernel⟩
private def batch3 : PaidBatch .empty 10 := ⟨[
  .rectangle 98 51 99 51 47,
  .rectangle 98 52 99 52 48,
  .point 98 53 48,
  .point 99 53 48,
  .point 100 51 47,
  .point 100 52 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 10 := ⟨[
  .point 100 53 48,
  .point 101 51 47,
  .point 101 52 48,
  .point 101 53 48,
  .rectangle 102 49 103 49 47,
  .point 102 50 47], by decide +kernel⟩
private def batch5 : PaidBatch .empty 10 := ⟨[
  .point 102 51 47,
  .point 102 52 48,
  .point 102 53 48,
  .point 103 50 47,
  .point 103 51 47,
  .point 103 52 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 10 := ⟨[
  .point 103 53 48,
  .rectangle 104 39 117 41 46,
  .rectangle 104 42 114 43 46,
  .rectangle 104 47 108 47 47,
  .rectangle 104 48 106 48 47,
  .point 104 49 47], by decide +kernel⟩
private def batch7 : PaidBatch .empty 10 := ⟨[
  .point 104 50 47,
  .point 104 51 47,
  .point 104 52 48,
  .shared 104 53 48 ⟨.tilted, 1, 2, true, 186872520530940760⟩,
  .point 105 49 47,
  .point 105 50 47], by decide +kernel⟩
private def batch8 : PaidBatch .empty 10 := ⟨[
  .point 105 51 48,
  .point 105 52 48,
  .shared 105 53 48 ⟨.tilted, 1, 2, true, 188539726283936652⟩,
  .point 106 49 47,
  .point 106 50 47,
  .point 106 51 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 10 := ⟨[
  .point 106 52 48,
  .shared 106 53 48 ⟨.tilted, 1, 2, true, 190206932036932544⟩,
  .point 107 48 47,
  .point 107 49 47,
  .point 107 50 47,
  .point 107 51 48], by decide +kernel⟩
private def batch10 : PaidBatch .empty 10 := ⟨[
  .shared 107 52 48 ⟨.tilted, 1, 2, true, 184512688640107468⟩,
  .shared 107 53 48 ⟨.tilted, 1, 2, true, 191874137789928436⟩,
  .point 108 48 47,
  .point 108 49 47,
  .point 108 50 47,
  .point 108 51 48], by decide +kernel⟩
private def batch11 : PaidBatch .empty 10 := ⟨[
  .shared 108 52 48 ⟨.tilted, 1, 2, true, 186115132640360052⟩,
  .shared 108 53 48 ⟨.tilted, 1, 2, true, 193541343542924328⟩,
  .rectangle 109 45 113 45 47,
  .rectangle 109 46 111 46 47,
  .point 109 47 47,
  .point 109 48 47], by decide +kernel⟩
private def batch12 : PaidBatch .empty 10 := ⟨[
  .point 109 49 47,
  .shared 109 50 47 ⟨.tilted, 1, 1, false, 170442610670655436⟩,
  .shared 109 51 48 ⟨.tilted, 1, 2, true, 180350392263496566⟩,
  .shared 109 52 48 ⟨.tilted, 1, 2, true, 187717576640612636⟩,
  .shared 109 53 48 ⟨.tilted, 1, 2, true, 195208549295920220⟩,
  .point 110 47 47], by decide +kernel⟩
private def batch13 : PaidBatch .empty 10 := ⟨[
  .point 110 48 47,
  .point 110 49 47,
  .shared 110 50 47 ⟨.tilted, 1, 2, true, 188480652140169500⟩,
  .shared 110 51 48 ⟨.tilted, 1, 2, true, 181889356921739834⟩,
  .shared 110 52 48 ⟨.tilted, 1, 2, true, 189320020640865220⟩,
  .shared 110 53 48 ⟨.tilted, 1, 2, true, 196875755048916112⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 10 := ⟨[
  .point 111 47 47,
  .point 111 48 47,
  .shared 111 49 47 ⟨.tilted, 1, 1, false, 166361823026086450⟩,
  .shared 111 50 48 ⟨.tilted, 1, 2, true, 177447638356354700⟩,
  .shared 111 51 48 ⟨.tilted, 1, 2, true, 183428321579983102⟩,
  .shared 111 52 48 ⟨.tilted, 1, 2, true, 190922464641117804⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 10 := ⟨[
  .shared 111 53 48 ⟨.tilted, 1, 2, true, 198542960801912004⟩,
  .rectangle 112 44 116 44 47,
  .point 112 46 47,
  .point 112 47 47,
  .point 112 48 47,
  .shared 112 49 47 ⟨.tilted, 1, 1, false, 167750736711256126⟩], by decide +kernel⟩
private def batch16 : PaidBatch .empty 10 := ⟨[
  .shared 112 50 48 ⟨.tilted, 1, 2, true, 177539222961576828⟩,
  .shared 112 51 48 ⟨.tilted, 1, 2, true, 184967286238226370⟩,
  .shared 112 52 48 ⟨.tilted, 1, 2, true, 192524908641370388⟩,
  .shared 112 53 48 ⟨.tilted, 1, 2, true, 200210166554907896⟩,
  .point 113 46 47,
  .point 113 47 47], by decide +kernel⟩
private def batch17 : PaidBatch .empty 10 := ⟨[
  .point 113 48 47,
  .shared 113 49 47 ⟨.tilted, 1, 1, false, 169139650396425801⟩,
  .shared 113 50 48 ⟨.tilted, 1, 2, true, 179015990688544772⟩,
  .shared 113 51 48 ⟨.tilted, 1, 2, true, 186506250896469638⟩,
  .shared 113 52 48 ⟨.tilted, 1, 2, true, 194127352641622972⟩,
  .shared 113 53 48 ⟨.tilted, 1, 2, true, 201877372307903788⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 10 := ⟨[
  .point 114 45 47,
  .point 114 46 47,
  .point 114 47 47,
  .shared 114 48 47 ⟨.tilted, 1, 1, false, 163504233065093382⟩,
  .shared 114 49 47 ⟨.tilted, 1, 1, false, 170528564081595477⟩,
  .shared 114 50 48 ⟨.tilted, 1, 2, true, 180492758415512716⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 10 := ⟨[
  .shared 114 51 48 ⟨.tilted, 1, 2, true, 188045215554712906⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, true, 195729796641875556⟩,
  .shared 114 53 48 ⟨.tilted, 1, 2, true, 203544578060899680⟩,
  .rectangle 115 42 123 42 47,
  .rectangle 115 43 119 43 47,
  .point 115 45 47], by decide +kernel⟩
private def batch20 : PaidBatch .empty 10 := ⟨[
  .point 115 46 47,
  .point 115 47 47,
  .shared 115 48 47 ⟨.tilted, 1, 1, false, 164836373347183072⟩,
  .shared 115 49 47 ⟨.tilted, 1, 1, false, 171917477766765152⟩,
  .shared 115 50 48 ⟨.tilted, 1, 2, true, 181969526142480660⟩,
  .shared 115 51 48 ⟨.tilted, 1, 2, true, 189584180212956174⟩], by decide +kernel⟩
private def batch21 : PaidBatch .empty 10 := ⟨[
  .shared 115 52 48 ⟨.tilted, 1, 2, true, 197332240642128140⟩,
  .shared 115 53 48 ⟨.tilted, 1, 2, false, 201473900505806111⟩,
  .point 116 45 47,
  .point 116 46 47,
  .point 116 47 47,
  .shared 116 48 47 ⟨.tilted, 1, 1, false, 166168513629272762⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 10 := ⟨[
  .shared 116 49 48 ⟨.tilted, 1, 2, true, 178070766965381948⟩,
  .shared 116 50 48 ⟨.tilted, 1, 2, true, 183446293869448604⟩,
  .shared 116 51 48 ⟨.tilted, 1, 2, true, 191123144871199442⟩,
  .shared 116 52 48 ⟨.tilted, 1, 2, true, 198934684642380724⟩,
  .shared 116 53 48 ⟨.tilted, 1, 2, false, 203101128897218159⟩,
  .point 117 44 47], by decide +kernel⟩
private def batch23 : PaidBatch .empty 10 := ⟨[
  .point 117 45 47,
  .point 117 46 47,
  .shared 117 47 47 ⟨.tilted, 1, 1, false, 160434813738652881⟩,
  .shared 117 48 47 ⟨.tilted, 1, 1, false, 167500653911362452⟩,
  .shared 117 49 48 ⟨.tilted, 1, 2, true, 177321908459655812⟩,
  .shared 117 50 48 ⟨.tilted, 1, 2, true, 184923061596416548⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 10 := ⟨[
  .shared 117 51 48 ⟨.tilted, 1, 2, true, 192662109529442710⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 200537128642633308⟩,
  .shared 117 53 48 ⟨.tilted, 1, 2, false, 204728357288630206⟩,
  .rectangle 118 35 127 37 45,
  .rectangle 118 38 127 39 46,
  .rectangle 118 40 127 40 46], by decide +kernel⟩
private def batch25 : PaidBatch .empty 10 := ⟨[
  .rectangle 118 41 126 41 47,
  .point 118 44 47,
  .point 118 45 47,
  .point 118 46 47,
  .shared 118 47 47 ⟨.tilted, 1, 1, false, 161711302727054828⟩,
  .shared 118 48 47 ⟨.tilted, 1, 1, false, 168832794193452142⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 10 := ⟨[
  .shared 118 49 48 ⟨.tilted, 1, 2, true, 178737761666082424⟩,
  .shared 118 50 48 ⟨.tilted, 1, 2, true, 186399829323384492⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, true, 194201074187685978⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, false, 198601260042404974⟩,
  .shared 118 53 48 ⟨.tilted, 1, 2, false, 206355585680042254⟩,
  .point 119 44 47], by decide +kernel⟩
private def batch27 : PaidBatch .empty 10 := ⟨[
  .point 119 45 47,
  .point 119 46 47,
  .shared 119 47 47 ⟨.tilted, 1, 1, false, 162987791715456776⟩,
  .shared 119 48 47 ⟨.tilted, 1, 1, false, 170164934475541832⟩,
  .shared 119 49 48 ⟨.tilted, 1, 2, true, 180153614872509036⟩,
  .shared 119 50 48 ⟨.tilted, 1, 2, true, 187876597050352436⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 10 := ⟨[
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 195740038845929246⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, false, 200167226593168064⟩,
  .shared 119 53 48 ⟨.tilted, 1, 2, false, 207982814071454301⟩,
  .point 120 43 47,
  .point 120 44 47,
  .point 120 45 47], by decide +kernel⟩
private def batch29 : PaidBatch .empty 10 := ⟨[
  .shared 120 46 47 ⟨.tilted, 0, 1, false, 157165347195383496⟩,
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 164264280703858723⟩,
  .shared 120 48 47 ⟨.tilted, 1, 1, false, 171497074757631522⟩,
  .shared 120 49 48 ⟨.tilted, 1, 2, true, 181569468078935648⟩,
  .shared 120 50 48 ⟨.tilted, 1, 2, true, 189353364777320380⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 197279003504172514⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 10 := ⟨[
  .shared 120 52 48 ⟨.tilted, 1, 2, false, 201733193143931154⟩,
  .shared 120 53 48 ⟨.tilted, 1, 2, false, 209610042462866349⟩,
  .point 121 43 47,
  .point 121 44 47,
  .point 121 45 47,
  .shared 121 46 47 ⟨.tilted, 0, 1, false, 158387306999489944⟩], by decide +kernel⟩
private def batch31 : PaidBatch .empty 10 := ⟨[
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 165540769692260671⟩,
  .shared 121 48 47 ⟨.tilted, 1, 1, false, 172829215039721212⟩,
  .shared 121 49 48 ⟨.tilted, 1, 2, true, 182985321285362260⟩,
  .shared 121 50 48 ⟨.tilted, 1, 2, true, 190830132504288324⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, false, 196933095257202648⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, false, 203299159694694244⟩], by decide +kernel⟩
private def batch32 : PaidBatch .empty 10 := ⟨[
  .shared 121 53 48 ⟨.tilted, 1, 2, false, 211237270854278396⟩,
  .point 122 43 47,
  .point 122 44 47,
  .point 122 45 47,
  .shared 122 46 47 ⟨.tilted, 0, 1, false, 159609266803596392⟩,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 166817258680662618⟩], by decide +kernel⟩
private def batch33 : PaidBatch .empty 10 := ⟨[
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 174161355321810902⟩,
  .shared 122 49 48 ⟨.tilted, 1, 2, true, 184401174491788872⟩,
  .shared 122 50 48 ⟨.tilted, 1, 2, true, 192306900231256268⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, false, 196993442188864461⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, false, 204865126245457334⟩,
  .shared 122 53 48 ⟨.tilted, 1, 2, false, 212864499245690444⟩], by decide +kernel⟩
private def batch34 : PaidBatch .empty 10 := ⟨[
  .point 123 43 47,
  .point 123 44 47,
  .shared 123 45 47 ⟨.tilted, 0, 1, false, 153707615583903781⟩,
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 160831226607702840⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 168093747669064566⟩,
  .shared 123 48 48 ⟨.tilted, 0, 2, true, 177997900314977120⟩], by decide +kernel⟩
private def batch35 : PaidBatch .empty 10 := ⟨[
  .shared 123 49 48 ⟨.tilted, 1, 2, true, 185817027698215484⟩,
  .shared 123 50 48 ⟨.tilted, 1, 2, true, 193783667958224212⟩,
  .shared 123 51 48 ⟨.tilted, 1, 2, false, 198499269008370837⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, false, 206431092796220424⟩,
  .shared 123 53 48 ⟨.tilted, 1, 2, false, 214491727637102491⟩,
  .point 124 42 47], by decide +kernel⟩
private def batch36 : PaidBatch .empty 10 := ⟨[
  .point 124 43 47,
  .point 124 44 47,
  .shared 124 45 47 ⟨.tilted, 0, 1, false, 154876168313106973⟩,
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 162053186411809288⟩,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 169370236657466513⟩,
  .shared 124 48 48 ⟨.tilted, 0, 2, true, 179354121411596392⟩], by decide +kernel⟩
private def batch37 : PaidBatch .empty 10 := ⟨[
  .shared 124 49 48 ⟨.tilted, 1, 2, true, 187232880904642096⟩,
  .shared 124 50 48 ⟨.tilted, 1, 2, true, 195260435685192156⟩,
  .shared 124 51 48 ⟨.tilted, 1, 2, false, 200005095827877212⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, false, 207997059346983514⟩,
  .shared 124 53 48 ⟨.tilted, 1, 2, false, 216118956028514539⟩,
  .rectangle 125 30 129 33 44], by decide +kernel⟩
private def batch38 : PaidBatch .empty 10 := ⟨[
  .rectangle 125 34 129 36 45,
  .point 125 42 47,
  .point 125 43 47,
  .point 125 44 47,
  .shared 125 45 47 ⟨.tilted, 0, 1, false, 156044721042310164⟩,
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 163275146215915736⟩], by decide +kernel⟩
private def batch39 : PaidBatch .empty 10 := ⟨[
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 170646725645868461⟩,
  .shared 125 48 48 ⟨.tilted, 0, 2, true, 180710342508215664⟩,
  .shared 125 49 48 ⟨.tilted, 0, 2, true, 188648734111068708⟩,
  .shared 125 50 48 ⟨.tilted, 1, 2, false, 195995952240828500⟩,
  .shared 125 51 48 ⟨.tilted, 1, 2, false, 201510922647383588⟩,
  .shared 125 52 48 ⟨.tilted, 1, 2, false, 209563025897746604⟩], by decide +kernel⟩
private def batch40 : PaidBatch .empty 10 := ⟨[
  .shared 125 53 48 ⟨.tilted, 1, 2, false, 217746184419926586⟩,
  .point 126 42 47,
  .point 126 43 47,
  .shared 126 44 47 ⟨.tilted, 0, 1, false, 150073401052832286⟩,
  .shared 126 45 47 ⟨.tilted, 0, 1, false, 157213273771513356⟩,
  .shared 126 46 47 ⟨.tilted, 0, 1, false, 164497106020022184⟩], by decide +kernel⟩
private def batch41 : PaidBatch .empty 10 := ⟨[
  .shared 126 47 47 ⟨.tilted, 0, 1, false, 171923214634270408⟩,
  .shared 126 48 48 ⟨.tilted, 0, 2, true, 182066563604834936⟩,
  .shared 126 49 48 ⟨.tilted, 0, 2, true, 190064587317495320⟩,
  .shared 126 50 48 ⟨.tilted, 1, 2, false, 195038367030567804⟩,
  .shared 126 51 48 ⟨.tilted, 1, 2, false, 203016749466889963⟩,
  .shared 126 52 48 ⟨.tilted, 1, 2, false, 211128992448509694⟩], by decide +kernel⟩
private def batch42 : PaidBatch .empty 10 := ⟨[
  .shared 126 53 48 ⟨.tilted, 1, 2, false, 219373412811338634⟩,
  .point 127 41 47,
  .point 127 42 47,
  .point 127 43 47,
  .shared 127 44 47 ⟨.tilted, 0, 1, false, 151189668816524464⟩,
  .shared 127 45 47 ⟨.tilted, 0, 1, false, 158381826500716547⟩], by decide +kernel⟩
private def batch43 : PaidBatch .empty 10 := ⟨[
  .shared 127 46 47 ⟨.tilted, 0, 1, false, 165719065824128632⟩,
  .shared 127 47 47 ⟨.tilted, 0, 1, false, 173199703622672356⟩,
  .shared 127 48 48 ⟨.tilted, 0, 2, true, 183422784701454208⟩,
  .shared 127 49 48 ⟨.tilted, 0, 2, true, 191480440523921932⟩,
  .shared 127 50 48 ⟨.tilted, 1, 2, false, 196485176228209708⟩,
  .shared 127 51 48 ⟨.tilted, 1, 2, false, 204522576286396339⟩], by decide +kernel⟩
private def batch44 : PaidBatch .empty 10 := ⟨[
  .shared 127 52 48 ⟨.tilted, 1, 2, false, 212694958999272784⟩,
  .shared 127 53 48 ⟨.tilted, 1, 2, false, 221000641202750681⟩,
  .rectangle 128 37 129 38 46,
  .rectangle 128 39 129 39 46,
  .rectangle 128 40 129 40 47,
  .point 128 41 47], by decide +kernel⟩
private def batch45 : PaidBatch .empty 10 := ⟨[
  .point 128 42 47,
  .point 128 43 47,
  .shared 128 44 47 ⟨.tilted, 0, 1, false, 152305936580216642⟩,
  .shared 128 45 47 ⟨.tilted, 0, 1, false, 159550379229919739⟩,
  .shared 128 46 47 ⟨.tilted, 0, 1, false, 166941025628235080⟩,
  .shared 128 47 47 ⟨.tilted, 0, 1, false, 174476192611074303⟩], by decide +kernel⟩
private def batch46 : PaidBatch .empty 10 := ⟨[
  .shared 128 48 48 ⟨.tilted, 0, 2, true, 184779005798073480⟩,
  .shared 128 49 48 ⟨.tilted, 0, 2, true, 192896293730348544⟩,
  .shared 128 50 48 ⟨.tilted, 0, 2, false, 197931985425851612⟩,
  .shared 128 51 48 ⟨.tilted, 1, 2, false, 206028403105902714⟩,
  .shared 128 52 48 ⟨.tilted, 1, 2, false, 214260925550035874⟩,
  .shared 128 53 48 ⟨.tilted, 1, 2, false, 222627869594162729⟩], by decide +kernel⟩
private def batch47 : PaidBatch .empty 10 := ⟨[
  .point 129 41 47,
  .point 129 42 47,
  .point 129 43 47,
  .shared 129 44 47 ⟨.tilted, 0, 1, false, 153422204343908820⟩,
  .shared 129 45 47 ⟨.tilted, 0, 1, false, 160718931959122930⟩,
  .shared 129 46 47 ⟨.tilted, 0, 1, false, 168162985432341528⟩], by decide +kernel⟩
private def batch48 : PaidBatch .empty 10 := ⟨[
  .shared 129 47 47 ⟨.tilted, 0, 1, false, 175752681599476251⟩,
  .shared 129 48 48 ⟨.tilted, 0, 2, true, 186135226894692752⟩,
  .shared 129 49 48 ⟨.tilted, 0, 2, true, 194312146936775156⟩,
  .shared 129 50 48 ⟨.tilted, 0, 2, false, 199378794623493516⟩,
  .shared 129 51 48 ⟨.tilted, 1, 2, false, 207534229925409090⟩,
  .shared 129 52 48 ⟨.tilted, 1, 2, false, 215826892100798964⟩], by decide +kernel⟩
def batch49 : PaidBatch .empty 10 := ⟨[
  .shared 129 53 49 ⟨.tilted, 1, 2, false, 224255097985574776⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 10) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32, batch33, batch34, batch35, batch36, batch37, batch38, batch39, batch40, batch41, batch42, batch43, batch44, batch45, batch46, batch47, batch48, batch49]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 129 30 10 = true := by decide +kernel
private theorem index40 : checks tiles 129 40 10 = true := by decide +kernel
theorem index50 : checks tiles 129 50 4 = true := by decide +kernel
private theorem covers : checks tiles 129 30 24 = true :=
  checks_join (checks_join (index30) index40) index50

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 10 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11
private def batch0 : PaidBatch .empty 11 := ⟨[
  .rectangle 11 33 82 40 37,
  .rectangle 14 41 83 48 44,
  .rectangle 17 49 80 53 44,
  .rectangle 81 49 94 51 47,
  .rectangle 81 52 92 53 47,
  .rectangle 83 33 117 37 44], by decide +kernel⟩
private def batch1 : PaidBatch .empty 11 := ⟨[
  .rectangle 83 38 109 41 44,
  .rectangle 84 42 103 44 44,
  .rectangle 84 45 103 47 47,
  .rectangle 84 48 96 50 47,
  .rectangle 93 52 96 52 47,
  .rectangle 93 53 94 53 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 11 := ⟨[
  .rectangle 95 51 98 51 47,
  .point 95 53 47,
  .point 96 53 47,
  .rectangle 97 48 101 49 47,
  .rectangle 97 50 101 50 47,
  .point 97 52 47], by decide +kernel⟩
private def batch3 : PaidBatch .empty 11 := ⟨[
  .point 97 53 47,
  .rectangle 98 52 99 52 48,
  .point 98 53 48,
  .point 99 51 47,
  .point 99 53 48,
  .point 100 51 47], by decide +kernel⟩
private def batch4 : PaidBatch .empty 11 := ⟨[
  .point 100 52 48,
  .point 100 53 48,
  .point 101 51 47,
  .point 101 52 48,
  .point 101 53 48,
  .rectangle 102 48 105 48 47], by decide +kernel⟩
private def batch5 : PaidBatch .empty 11 := ⟨[
  .rectangle 102 49 103 49 47,
  .point 102 50 47,
  .point 102 51 47,
  .point 102 52 48,
  .point 102 53 48,
  .point 103 50 47], by decide +kernel⟩
private def batch6 : PaidBatch .empty 11 := ⟨[
  .point 103 51 47,
  .point 103 52 48,
  .point 103 53 48,
  .rectangle 104 42 114 43 46,
  .rectangle 104 44 111 45 47,
  .rectangle 104 46 111 46 47], by decide +kernel⟩
private def batch7 : PaidBatch .empty 11 := ⟨[
  .rectangle 104 47 108 47 47,
  .point 104 49 47,
  .point 104 50 47,
  .point 104 51 47,
  .point 104 52 48,
  .shared 104 53 48 ⟨.tilted, 1, 2, true, 188719449661718176⟩], by decide +kernel⟩
private def batch8 : PaidBatch .empty 11 := ⟨[
  .point 105 49 47,
  .point 105 50 47,
  .point 105 51 48,
  .point 105 52 48,
  .shared 105 53 48 ⟨.tilted, 1, 2, true, 190386655414714068⟩,
  .point 106 48 47], by decide +kernel⟩
private def batch9 : PaidBatch .empty 11 := ⟨[
  .point 106 49 47,
  .point 106 50 47,
  .point 106 51 48,
  .shared 106 52 48 ⟨.tilted, 1, 2, true, 184584422386300770⟩,
  .shared 106 53 48 ⟨.tilted, 1, 2, true, 192053861167709960⟩,
  .point 107 48 47], by decide +kernel⟩
private def batch10 : PaidBatch .empty 11 := ⟨[
  .point 107 49 47,
  .point 107 50 47,
  .point 107 51 48,
  .shared 107 52 48 ⟨.tilted, 1, 2, true, 186186866386553354⟩,
  .shared 107 53 48 ⟨.tilted, 1, 2, true, 193721066920705852⟩,
  .point 108 48 47], by decide +kernel⟩
private def batch11 : PaidBatch .empty 11 := ⟨[
  .point 108 49 47,
  .point 108 50 47,
  .point 108 51 48,
  .shared 108 52 48 ⟨.tilted, 1, 2, true, 187789310386805938⟩,
  .shared 108 53 48 ⟨.tilted, 1, 2, true, 195388272673701744⟩,
  .point 109 47 47], by decide +kernel⟩
private def batch12 : PaidBatch .empty 11 := ⟨[
  .point 109 48 47,
  .point 109 49 47,
  .shared 109 50 47 ⟨.tilted, 1, 1, false, 172549357053408014⟩,
  .shared 109 51 48 ⟨.tilted, 1, 2, true, 181860314596723617⟩,
  .shared 109 52 48 ⟨.tilted, 1, 2, true, 189391754387058522⟩,
  .shared 109 53 48 ⟨.tilted, 1, 2, false, 194419127846006116⟩], by decide +kernel⟩
private def batch13 : PaidBatch .empty 11 := ⟨[
  .rectangle 110 38 127 39 46,
  .rectangle 110 40 120 41 46,
  .point 110 47 47,
  .point 110 48 47,
  .point 110 49 47,
  .shared 110 50 47 ⟨.tilted, 1, 2, true, 193718452002052283⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 11 := ⟨[
  .shared 110 51 48 ⟨.tilted, 1, 2, true, 183399279254966885⟩,
  .shared 110 52 48 ⟨.tilted, 1, 2, true, 190994198387311106⟩,
  .shared 110 53 48 ⟨.tilted, 1, 2, false, 196056375069675968⟩,
  .point 111 47 47,
  .point 111 48 47,
  .shared 111 49 47 ⟨.tilted, 1, 1, false, 168300012572012574⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 11 := ⟨[
  .shared 111 50 48 ⟨.tilted, 1, 2, true, 182378835299493125⟩,
  .shared 111 51 48 ⟨.tilted, 1, 2, true, 184938243913210153⟩,
  .shared 111 52 48 ⟨.tilted, 1, 2, true, 192596642387563690⟩,
  .shared 111 53 48 ⟨.tilted, 1, 2, false, 197693622293345820⟩,
  .rectangle 112 44 116 44 47,
  .rectangle 112 45 113 45 47], by decide +kernel⟩
private def batch16 : PaidBatch .empty 11 := ⟨[
  .point 112 46 47,
  .point 112 47 47,
  .point 112 48 47,
  .shared 112 49 47 ⟨.tilted, 1, 1, false, 169697021473339066⟩,
  .shared 112 50 48 ⟨.tilted, 1, 2, true, 178893385852697743⟩,
  .shared 112 51 48 ⟨.tilted, 1, 2, true, 186477208571453421⟩], by decide +kernel⟩
private def batch17 : PaidBatch .empty 11 := ⟨[
  .shared 112 52 48 ⟨.tilted, 1, 2, false, 191734120192806584⟩,
  .shared 112 53 48 ⟨.tilted, 1, 2, false, 199330869517015672⟩,
  .point 113 46 47,
  .point 113 47 47,
  .point 113 48 47,
  .shared 113 49 47 ⟨.tilted, 1, 1, false, 171094030374665558⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 11 := ⟨[
  .shared 113 50 48 ⟨.tilted, 1, 2, true, 180370153579665687⟩,
  .shared 113 51 48 ⟨.tilted, 1, 2, true, 188016173229696689⟩,
  .shared 113 52 48 ⟨.tilted, 1, 2, false, 193309624671802232⟩,
  .shared 113 53 48 ⟨.tilted, 1, 2, false, 200968116740685524⟩,
  .point 114 45 47,
  .point 114 46 47], by decide +kernel⟩
private def batch19 : PaidBatch .empty 11 := ⟨[
  .point 114 47 47,
  .shared 114 48 47 ⟨.tilted, 1, 1, false, 165287491386640210⟩,
  .shared 114 49 47 ⟨.tilted, 1, 1, false, 172491039275992050⟩,
  .shared 114 50 48 ⟨.tilted, 1, 2, true, 181846921306633631⟩,
  .shared 114 51 48 ⟨.tilted, 1, 2, true, 189555137887939957⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, false, 194885129150797879⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 11 := ⟨[
  .shared 114 53 48 ⟨.tilted, 1, 2, false, 202605363964355376⟩,
  .rectangle 115 42 123 42 47,
  .rectangle 115 43 120 43 47,
  .point 115 45 47,
  .point 115 46 47,
  .point 115 47 47], by decide +kernel⟩
private def batch21 : PaidBatch .empty 11 := ⟨[
  .shared 115 48 47 ⟨.tilted, 1, 1, false, 166627245980861470⟩,
  .shared 115 49 47 ⟨.tilted, 1, 1, false, 173888048177318542⟩,
  .shared 115 50 48 ⟨.tilted, 1, 2, true, 183323689033601575⟩,
  .shared 115 51 48 ⟨.tilted, 1, 2, false, 188806425165872935⟩,
  .shared 115 52 48 ⟨.tilted, 1, 2, false, 196460633629793527⟩,
  .shared 115 53 48 ⟨.tilted, 1, 2, false, 204242611188025228⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 11 := ⟨[
  .point 116 45 47,
  .point 116 46 47,
  .point 116 47 47,
  .shared 116 48 47 ⟨.tilted, 1, 1, false, 167967000575082729⟩,
  .shared 116 49 48 ⟨.tilted, 1, 2, true, 182738962835686330⟩,
  .shared 116 50 48 ⟨.tilted, 1, 2, true, 184800456760569519⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 11 := ⟨[
  .shared 116 51 48 ⟨.tilted, 1, 2, false, 190321309009586621⟩,
  .shared 116 52 48 ⟨.tilted, 1, 2, false, 198036138108789174⟩,
  .shared 116 53 48 ⟨.tilted, 1, 2, false, 205879858411695080⟩,
  .point 117 44 47,
  .point 117 45 47,
  .point 117 46 47], by decide +kernel⟩
private def batch24 : PaidBatch .empty 11 := ⟨[
  .shared 117 47 47 ⟨.tilted, 1, 1, false, 162068190328085505⟩,
  .shared 117 48 47 ⟨.tilted, 1, 1, false, 169306755169303989⟩,
  .shared 117 49 48 ⟨.tilted, 1, 2, true, 178528807879783286⟩,
  .shared 117 50 48 ⟨.tilted, 1, 2, true, 186277224487537463⟩,
  .shared 117 51 48 ⟨.tilted, 1, 2, false, 191836192853300307⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, false, 199611642587784822⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 11 := ⟨[
  .shared 117 53 48 ⟨.tilted, 1, 2, false, 207517105635364932⟩,
  .rectangle 118 33 128 36 45,
  .rectangle 118 37 129 38 46,
  .point 118 44 47,
  .point 118 45 47,
  .point 118 46 47], by decide +kernel⟩
private def batch26 : PaidBatch .empty 11 := ⟨[
  .shared 118 47 47 ⟨.tilted, 1, 1, false, 163351812724593775⟩,
  .shared 118 48 47 ⟨.tilted, 1, 1, false, 170646509763525248⟩,
  .shared 118 49 48 ⟨.tilted, 1, 2, true, 179944661086209898⟩,
  .shared 118 50 48 ⟨.tilted, 1, 2, true, 187753992214505407⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, false, 193351076697013993⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, false, 201187147066780469⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 11 := ⟨[
  .shared 118 53 48 ⟨.tilted, 1, 2, false, 209154352859034784⟩,
  .point 119 44 47,
  .point 119 45 47,
  .point 119 46 47,
  .shared 119 47 47 ⟨.tilted, 1, 1, false, 164635435121102045⟩,
  .shared 119 48 47 ⟨.tilted, 1, 1, false, 171986264357746508⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 11 := ⟨[
  .shared 119 49 48 ⟨.tilted, 1, 2, true, 181360514292636510⟩,
  .shared 119 50 48 ⟨.tilted, 1, 2, false, 187103210231647689⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, false, 194865960540727679⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, false, 202762651545776117⟩,
  .shared 119 53 48 ⟨.tilted, 1, 2, false, 210791600082704636⟩,
  .point 120 44 47], by decide +kernel⟩
private def batch29 : PaidBatch .empty 11 := ⟨[
  .point 120 45 47,
  .shared 120 46 47 ⟨.tilted, 0, 1, false, 158653891544967012⟩,
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 165919057517610315⟩,
  .shared 120 48 47 ⟨.tilted, 1, 1, false, 173326018951967767⟩,
  .shared 120 49 48 ⟨.tilted, 1, 2, true, 182776367499063122⟩,
  .shared 120 50 48 ⟨.tilted, 1, 2, false, 188558595549471657⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 11 := ⟨[
  .shared 120 51 48 ⟨.tilted, 1, 2, false, 196380844384441365⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, false, 204338156024771764⟩,
  .shared 120 53 48 ⟨.tilted, 1, 2, false, 212428847306374488⟩,
  .rectangle 121 40 129 40 47,
  .rectangle 121 41 126 41 47,
  .point 121 43 47], by decide +kernel⟩
private def batch31 : PaidBatch .empty 11 := ⟨[
  .point 121 44 47,
  .point 121 45 47,
  .shared 121 46 47 ⟨.tilted, 0, 1, false, 159882503853154535⟩,
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 167202679914118585⟩,
  .shared 121 48 47 ⟨.tilted, 1, 1, false, 174665773546189027⟩,
  .shared 121 49 48 ⟨.tilted, 1, 2, true, 184192220705489734⟩], by decide +kernel⟩
private def batch32 : PaidBatch .empty 11 := ⟨[
  .shared 121 50 48 ⟨.tilted, 1, 2, false, 190013980867295624⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, false, 197895728228155051⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, false, 205913660503767412⟩,
  .shared 121 53 48 ⟨.tilted, 1, 2, false, 214066094530044340⟩,
  .point 122 43 47,
  .point 122 44 47], by decide +kernel⟩
private def batch33 : PaidBatch .empty 11 := ⟨[
  .point 122 45 47,
  .shared 122 46 47 ⟨.tilted, 0, 1, false, 161111116161342059⟩,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 168486302310626855⟩,
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 176005528140410286⟩,
  .shared 122 49 48 ⟨.tilted, 1, 2, true, 185608073911916346⟩,
  .shared 122 50 48 ⟨.tilted, 1, 2, false, 191469366185119592⟩], by decide +kernel⟩
private def batch34 : PaidBatch .empty 11 := ⟨[
  .shared 122 51 48 ⟨.tilted, 1, 2, false, 199410612071868737⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, false, 207489164982763059⟩,
  .shared 122 53 48 ⟨.tilted, 1, 2, false, 215703341753714192⟩,
  .point 123 43 47,
  .point 123 44 47,
  .shared 123 45 47 ⟨.tilted, 0, 1, false, 155056377185903280⟩], by decide +kernel⟩
private def batch35 : PaidBatch .empty 11 := ⟨[
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 162339728469529582⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 169769924707135125⟩,
  .shared 123 48 48 ⟨.tilted, 0, 2, true, 179066032235223852⟩,
  .shared 123 49 48 ⟨.tilted, 1, 2, true, 187023927118342958⟩,
  .shared 123 50 48 ⟨.tilted, 1, 2, false, 192924751502943559⟩,
  .shared 123 51 48 ⟨.tilted, 1, 2, false, 200925495915582423⟩], by decide +kernel⟩
private def batch36 : PaidBatch .empty 11 := ⟨[
  .shared 123 52 48 ⟨.tilted, 1, 2, false, 209064669461758707⟩,
  .shared 123 53 48 ⟨.tilted, 1, 2, false, 217340588977384044⟩,
  .point 124 42 47,
  .point 124 43 47,
  .point 124 44 47,
  .shared 124 45 47 ⟨.tilted, 0, 1, false, 156231101515162300⟩], by decide +kernel⟩
private def batch37 : PaidBatch .empty 11 := ⟨[
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 163568340777717106⟩,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 171053547103643395⟩,
  .shared 124 48 48 ⟨.tilted, 0, 2, true, 180422253331843124⟩,
  .shared 124 49 48 ⟨.tilted, 1, 2, false, 186461128289256970⟩,
  .shared 124 50 48 ⟨.tilted, 1, 2, false, 194380136820767527⟩,
  .shared 124 51 48 ⟨.tilted, 1, 2, false, 202440379759296109⟩], by decide +kernel⟩
private def batch38 : PaidBatch .empty 11 := ⟨[
  .shared 124 52 48 ⟨.tilted, 1, 2, false, 210640173940754354⟩,
  .shared 124 53 48 ⟨.tilted, 1, 2, false, 218977836201053896⟩,
  .point 125 42 47,
  .point 125 43 47,
  .point 125 44 47,
  .shared 125 45 47 ⟨.tilted, 0, 1, false, 157405825844421320⟩], by decide +kernel⟩
private def batch39 : PaidBatch .empty 11 := ⟨[
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 164796953085904629⟩,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 172337169500151665⟩,
  .shared 125 48 48 ⟨.tilted, 0, 2, true, 181778474428462396⟩,
  .shared 125 49 48 ⟨.tilted, 0, 2, false, 187858137190583462⟩,
  .shared 125 50 48 ⟨.tilted, 1, 2, false, 195835522138591494⟩,
  .shared 125 51 48 ⟨.tilted, 1, 2, false, 203955263603009795⟩], by decide +kernel⟩
private def batch40 : PaidBatch .empty 11 := ⟨[
  .shared 125 52 48 ⟨.tilted, 1, 2, false, 212215678419750002⟩,
  .shared 125 53 48 ⟨.tilted, 1, 2, false, 220615083424723748⟩,
  .point 126 42 47,
  .point 126 43 47,
  .shared 126 44 47 ⟨.tilted, 0, 1, false, 151287429399512863⟩,
  .shared 126 45 47 ⟨.tilted, 0, 1, false, 158580550173680340⟩], by decide +kernel⟩
private def batch41 : PaidBatch .empty 11 := ⟨[
  .shared 126 46 47 ⟨.tilted, 0, 1, false, 166025565394092153⟩,
  .shared 126 47 47 ⟨.tilted, 0, 1, false, 173620791896659935⟩,
  .shared 126 48 48 ⟨.tilted, 0, 2, true, 183134695525081668⟩,
  .shared 126 49 48 ⟨.tilted, 0, 2, false, 189255146091909954⟩,
  .shared 126 50 48 ⟨.tilted, 1, 2, false, 197290907456415462⟩,
  .shared 126 51 48 ⟨.tilted, 1, 2, false, 205470147446723481⟩], by decide +kernel⟩
private def batch42 : PaidBatch .empty 11 := ⟨[
  .shared 126 52 48 ⟨.tilted, 1, 2, false, 213791182898745649⟩,
  .shared 126 53 48 ⟨.tilted, 1, 2, false, 222252330648393600⟩,
  .point 127 41 47,
  .point 127 42 47,
  .point 127 43 47,
  .shared 127 44 47 ⟨.tilted, 0, 1, false, 152409387859235623⟩], by decide +kernel⟩
private def batch43 : PaidBatch .empty 11 := ⟨[
  .shared 127 45 47 ⟨.tilted, 0, 1, false, 159755274502939360⟩,
  .shared 127 46 47 ⟨.tilted, 0, 1, false, 167254177702279676⟩,
  .shared 127 47 47 ⟨.tilted, 0, 1, false, 174904414293168205⟩,
  .shared 127 48 48 ⟨.tilted, 0, 2, true, 184490916621700940⟩,
  .shared 127 49 48 ⟨.tilted, 0, 2, false, 190652154993236446⟩,
  .shared 127 50 48 ⟨.tilted, 1, 2, false, 198746292774239429⟩], by decide +kernel⟩
private def batch44 : PaidBatch .empty 11 := ⟨[
  .shared 127 51 48 ⟨.tilted, 1, 2, false, 206985031290437167⟩,
  .shared 127 52 48 ⟨.tilted, 1, 2, false, 215366687377741297⟩,
  .shared 127 53 48 ⟨.tilted, 1, 2, false, 223889577872063452⟩,
  .rectangle 128 39 129 39 46,
  .point 128 41 47,
  .point 128 42 47], by decide +kernel⟩
private def batch45 : PaidBatch .empty 11 := ⟨[
  .point 128 43 47,
  .shared 128 44 47 ⟨.tilted, 0, 1, false, 153531346318958382⟩,
  .shared 128 45 47 ⟨.tilted, 0, 1, false, 160929998832198380⟩,
  .shared 128 46 47 ⟨.tilted, 0, 1, false, 168482790010467200⟩,
  .shared 128 47 47 ⟨.tilted, 0, 1, false, 176188036689676475⟩,
  .shared 128 48 48 ⟨.tilted, 0, 2, true, 185847137718320212⟩], by decide +kernel⟩
private def batch46 : PaidBatch .empty 11 := ⟨[
  .shared 128 49 48 ⟨.tilted, 0, 2, false, 192049163894562938⟩,
  .shared 128 50 48 ⟨.tilted, 0, 2, false, 200201678092063397⟩,
  .shared 128 51 48 ⟨.tilted, 1, 2, false, 208499915134150853⟩,
  .shared 128 52 48 ⟨.tilted, 1, 2, false, 216942191856736944⟩,
  .shared 128 53 48 ⟨.tilted, 1, 2, false, 225526825095733304⟩,
  .rectangle 129 33 129 35 45], by decide +kernel⟩
private def batch47 : PaidBatch .empty 11 := ⟨[
  .rectangle 129 36 129 37 46,
  .point 129 41 47,
  .point 129 42 47,
  .point 129 43 47,
  .shared 129 44 47 ⟨.tilted, 0, 1, false, 154653304778681142⟩,
  .shared 129 45 47 ⟨.tilted, 0, 1, false, 162104723161457400⟩], by decide +kernel⟩
private def batch48 : PaidBatch .empty 11 := ⟨[
  .shared 129 46 47 ⟨.tilted, 0, 1, false, 169711402318654723⟩,
  .shared 129 47 47 ⟨.tilted, 0, 1, false, 177471659086184745⟩,
  .shared 129 48 48 ⟨.tilted, 0, 2, true, 187203358814939484⟩,
  .shared 129 49 48 ⟨.tilted, 0, 2, false, 193446172795889430⟩,
  .shared 129 50 48 ⟨.tilted, 0, 2, false, 201657063409887364⟩,
  .shared 129 51 48 ⟨.tilted, 1, 2, false, 210014798977864539⟩], by decide +kernel⟩
def batch49 : PaidBatch .empty 11 := ⟨[
  .shared 129 52 48 ⟨.tilted, 1, 2, false, 218517696335732592⟩,
  .shared 129 53 49 ⟨.tilted, 1, 2, false, 227164072319403156⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 11) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32, batch33, batch34, batch35, batch36, batch37, batch38, batch39, batch40, batch41, batch42, batch43, batch44, batch45, batch46, batch47, batch48, batch49]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 129 33 10 = true := by decide +kernel
private theorem index43 : checks tiles 129 43 10 = true := by decide +kernel
private theorem index53 : checks tiles 129 53 1 = true := by decide +kernel
private theorem covers : checks tiles 129 33 21 = true :=
  checks_join (checks_join (index33) index43) index53

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 11 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

end Compact50PriceTableEmpty10
