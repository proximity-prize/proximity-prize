import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty8
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top8
private def b0 : PaidBatch .empty 8 := ⟨[
  .rectangle 8 24 68 31 26,
  .rectangle 11 32 68 38 29,
  .rectangle 13 39 71 46 37], by decide +kernel⟩
private def b1 : PaidBatch .empty 8 := ⟨[
  .rectangle 16 47 71 53 40,
  .rectangle 69 32 99 38 42,
  .rectangle 69 24 129 27 35], by decide +kernel⟩
private def b2 : PaidBatch .empty 8 := ⟨[
  .rectangle 69 28 129 31 40,
  .rectangle 72 47 86 50 43,
  .rectangle 72 51 86 53 44], by decide +kernel⟩
private def b3 : PaidBatch .empty 8 := ⟨[
  .rectangle 72 39 100 42 42,
  .rectangle 72 43 100 46 46,
  .rectangle 87 51 93 53 48], by decide +kernel⟩
private def b4 : PaidBatch .empty 8 := ⟨[
  .rectangle 87 47 100 48 46,
  .rectangle 87 49 100 50 47,
  .rectangle 94 53 97 53 48], by decide +kernel⟩
private def b5 : PaidBatch .empty 8 := ⟨[
  .rectangle 94 51 100 51 47,
  .rectangle 94 52 100 52 48,
  .rectangle 98 53 98 53 48], by decide +kernel⟩
private def b6 : PaidBatch .empty 8 := ⟨[
  .point 99 53 46,
  .point 100 53 46,
  .rectangle 100 36 114 38 42], by decide +kernel⟩
private def b7 : PaidBatch .empty 8 := ⟨[
  .rectangle 100 32 129 35 45,
  .point 101 52 46,
  .point 101 53 46], by decide +kernel⟩
private def b8 : PaidBatch .empty 8 := ⟨[
  .rectangle 101 51 102 51 48,
  .rectangle 101 49 104 49 47,
  .rectangle 101 50 104 50 48], by decide +kernel⟩
private def b9 : PaidBatch .empty 8 := ⟨[
  .rectangle 101 43 108 44 45,
  .rectangle 101 45 108 46 47,
  .rectangle 101 47 108 47 47], by decide +kernel⟩
private def b10 : PaidBatch .empty 8 := ⟨[
  .rectangle 101 48 108 48 48,
  .rectangle 101 39 115 40 44,
  .rectangle 101 41 115 42 46], by decide +kernel⟩
private def b11 : PaidBatch .empty 8 := ⟨[
  .point 102 52 46,
  .point 102 53 47,
  .point 103 51 46], by decide +kernel⟩
private def b12 : PaidBatch .empty 8 := ⟨[
  .point 103 52 46,
  .point 103 53 47,
  .point 104 51 46], by decide +kernel⟩
private def b13 : PaidBatch .empty 8 := ⟨[
  .point 104 52 47,
  .point 104 53 48,
  .point 105 50 45], by decide +kernel⟩
private def b14 : PaidBatch .empty 8 := ⟨[
  .point 105 51 46,
  .point 105 52 47,
  .point 105 53 48], by decide +kernel⟩
private def b15 : PaidBatch .empty 8 := ⟨[
  .rectangle 105 49 106 49 48,
  .point 106 50 46,
  .point 106 51 47], by decide +kernel⟩
private def b16 : PaidBatch .empty 8 := ⟨[
  .point 106 52 48,
  .point 106 53 49,
  .point 107 49 45], by decide +kernel⟩
private def b17 : PaidBatch .empty 8 := ⟨[
  .point 107 50 46,
  .point 107 51 47,
  .point 107 52 48], by decide +kernel⟩
private def b18 : PaidBatch .empty 8 := ⟨[
  .point 107 53 49,
  .point 108 49 46,
  .point 108 50 47], by decide +kernel⟩
private def b19 : PaidBatch .empty 8 := ⟨[
  .point 108 51 48,
  .shared 108 52 32 ⟨.tilted, 1, 2, true, 181056373886801964⟩,
  .shared 108 53 33 ⟨.tilted, 1, 2, true, 188060513316228998⟩], by decide +kernel⟩
private def b20 : PaidBatch .empty 8 := ⟨[
  .rectangle 109 48 109 48 48,
  .point 109 49 46,
  .point 109 50 47], by decide +kernel⟩
private def b21 : PaidBatch .empty 8 := ⟨[
  .point 109 51 48,
  .shared 109 52 32 ⟨.tilted, 1, 2, true, 182658793873091812⟩,
  .shared 109 53 33 ⟨.tilted, 1, 2, true, 189727694084753074⟩], by decide +kernel⟩
private def b22 : PaidBatch .empty 8 := ⟨[
  .rectangle 109 47 110 47 48,
  .rectangle 109 46 112 46 48,
  .rectangle 109 43 115 44 48], by decide +kernel⟩
private def b23 : PaidBatch .empty 8 := ⟨[
  .rectangle 109 45 115 45 48,
  .point 110 48 46,
  .point 110 49 47], by decide +kernel⟩
private def b24 : PaidBatch .empty 8 := ⟨[
  .point 110 50 48,
  .shared 110 51 32 ⟨.tilted, 1, 2, true, 177235629992535800⟩,
  .point 110 52 49], by decide +kernel⟩
private def b25 : PaidBatch .empty 8 := ⟨[
  .shared 110 53 34 ⟨.tilted, 1, 2, true, 191394874853277150⟩,
  .rectangle 111 47 111 47 48,
  .point 111 48 46], by decide +kernel⟩
private def b26 : PaidBatch .empty 8 := ⟨[
  .point 111 49 47,
  .point 111 50 48,
  .shared 111 51 32 ⟨.tilted, 1, 2, true, 178774571588107412⟩], by decide +kernel⟩
private def b27 : PaidBatch .empty 8 := ⟨[
  .shared 111 52 33 ⟨.tilted, 1, 2, true, 185863633845671508⟩,
  .shared 111 53 35 ⟨.tilted, 1, 2, true, 193062055621801226⟩,
  .point 112 47 45], by decide +kernel⟩
private def b28 : PaidBatch .empty 8 := ⟨[
  .point 112 48 46,
  .point 112 49 47,
  .point 112 50 48], by decide +kernel⟩
private def b29 : PaidBatch .empty 8 := ⟨[
  .shared 112 51 33 ⟨.tilted, 1, 2, true, 180313513183679024⟩,
  .shared 112 52 34 ⟨.tilted, 1, 2, true, 187466053831961356⟩,
  .shared 112 53 35 ⟨.tilted, 1, 2, true, 194729236390325302⟩], by decide +kernel⟩
private def b30 : PaidBatch .empty 8 := ⟨[
  .point 113 47 46,
  .point 113 48 47,
  .point 113 49 48], by decide +kernel⟩
private def b31 : PaidBatch .empty 8 := ⟨[
  .shared 113 50 32 ⟨.tilted, 1, 2, true, 174750283629121660⟩,
  .shared 113 51 33 ⟨.tilted, 1, 2, true, 181852454779250636⟩,
  .shared 113 52 34 ⟨.tilted, 1, 2, true, 189068473818251204⟩], by decide +kernel⟩
private def b32 : PaidBatch .empty 8 := ⟨[
  .shared 113 53 36 ⟨.tilted, 1, 2, true, 196396417158849378⟩,
  .rectangle 113 46 114 46 48,
  .point 114 47 46], by decide +kernel⟩
private def b33 : PaidBatch .empty 8 := ⟨[
  .point 114 48 47,
  .point 114 49 48,
  .shared 114 50 33 ⟨.tilted, 1, 2, true, 176227029225491028⟩], by decide +kernel⟩
private def b34 : PaidBatch .empty 8 := ⟨[
  .shared 114 51 34 ⟨.tilted, 1, 2, true, 183391396374822248⟩,
  .shared 114 52 35 ⟨.tilted, 1, 2, true, 190670893804541052⟩,
  .shared 114 53 36 ⟨.tilted, 1, 2, true, 198063597927373454⟩], by decide +kernel⟩
private def b35 : PaidBatch .empty 8 := ⟨[
  .point 115 46 46,
  .point 115 47 47,
  .point 115 48 48], by decide +kernel⟩
private def b36 : PaidBatch .empty 8 := ⟨[
  .shared 115 49 37 ⟨.tilted, 1, 1, false, 161626103377400944⟩,
  .shared 115 50 33 ⟨.tilted, 1, 2, true, 177703774821860396⟩,
  .shared 115 51 34 ⟨.tilted, 1, 2, true, 184930337970393860⟩], by decide +kernel⟩
private def b37 : PaidBatch .empty 8 := ⟨[
  .shared 115 52 36 ⟨.tilted, 1, 2, true, 192273313790830900⟩,
  .shared 115 53 37 ⟨.tilted, 1, 2, true, 199730778695897530⟩,
  .rectangle 115 36 129 38 47], by decide +kernel⟩
private def b38 : PaidBatch .empty 8 := ⟨[
  .rectangle 116 45 116 45 48,
  .point 116 46 46,
  .point 116 47 47], by decide +kernel⟩
private def b39 : PaidBatch .empty 8 := ⟨[
  .point 116 48 48,
  .shared 116 49 32 ⟨.tilted, 1, 2, true, 172011379921187614⟩,
  .shared 116 50 34 ⟨.tilted, 1, 2, true, 179180520418229764⟩], by decide +kernel⟩
private def b40 : PaidBatch .empty 8 := ⟨[
  .shared 116 51 35 ⟨.tilted, 1, 2, true, 186469279565965472⟩,
  .shared 116 52 36 ⟨.tilted, 1, 2, true, 193875733777120748⟩,
  .shared 116 53 38 ⟨.tilted, 1, 2, true, 201397959464421606⟩], by decide +kernel⟩
private def b41 : PaidBatch .empty 8 := ⟨[
  .rectangle 116 44 119 44 48,
  .rectangle 116 39 122 40 46,
  .rectangle 116 41 122 41 46], by decide +kernel⟩
private def b42 : PaidBatch .empty 8 := ⟨[
  .rectangle 116 42 122 42 47,
  .rectangle 116 43 122 43 48,
  .point 117 45 45], by decide +kernel⟩
private def b43 : PaidBatch .empty 8 := ⟨[
  .point 117 46 46,
  .point 117 47 47,
  .point 117 48 48], by decide +kernel⟩
private def b44 : PaidBatch .empty 8 := ⟨[
  .shared 117 49 33 ⟨.tilted, 1, 2, true, 173427211909870730⟩,
  .shared 117 50 34 ⟨.tilted, 1, 2, true, 180657266014599132⟩,
  .shared 117 51 36 ⟨.tilted, 1, 2, true, 188008221161537084⟩], by decide +kernel⟩
private def b45 : PaidBatch .empty 8 := ⟨[
  .shared 117 52 37 ⟨.tilted, 1, 2, true, 195478153763410596⟩,
  .shared 117 53 38 ⟨.tilted, 1, 2, true, 203065140232945682⟩,
  .point 118 45 46], by decide +kernel⟩
private def b46 : PaidBatch .empty 8 := ⟨[
  .point 118 46 47,
  .point 118 47 48,
  .shared 118 48 38 ⟨.tilted, 1, 1, false, 159123346676594736⟩], by decide +kernel⟩
private def b47 : PaidBatch .empty 8 := ⟨[
  .shared 118 49 33 ⟨.tilted, 1, 2, true, 174843043898553846⟩,
  .shared 118 50 35 ⟨.tilted, 1, 2, true, 182134011610968500⟩,
  .shared 118 51 36 ⟨.tilted, 1, 2, true, 189547162757108696⟩], by decide +kernel⟩
private def b48 : PaidBatch .empty 8 := ⟨[
  .shared 118 52 38 ⟨.tilted, 1, 2, true, 197080573749700444⟩,
  .shared 118 53 39 ⟨.tilted, 1, 2, true, 204732321001469758⟩,
  .point 119 45 46], by decide +kernel⟩
private def b49 : PaidBatch .empty 8 := ⟨[
  .point 119 46 47,
  .point 119 47 48,
  .shared 119 48 38 ⟨.tilted, 1, 1, false, 160392273606959184⟩], by decide +kernel⟩
private def b50 : PaidBatch .empty 8 := ⟨[
  .shared 119 49 34 ⟨.tilted, 1, 2, true, 176258875887236962⟩,
  .shared 119 50 35 ⟨.tilted, 1, 2, true, 183610757207337868⟩,
  .shared 119 51 37 ⟨.tilted, 1, 2, true, 191086104352680308⟩], by decide +kernel⟩
private def b51 : PaidBatch .empty 8 := ⟨[
  .shared 119 52 38 ⟨.tilted, 1, 2, true, 198682993735990292⟩,
  .shared 119 53 40 ⟨.tilted, 1, 2, true, 206399501769993834⟩,
  .point 120 44 45], by decide +kernel⟩
private def b52 : PaidBatch .empty 8 := ⟨[
  .point 120 45 46,
  .point 120 46 48,
  .shared 120 47 38 ⟨.tilted, 0, 1, false, 155195727759329712⟩], by decide +kernel⟩
private def b53 : PaidBatch .empty 8 := ⟨[
  .shared 120 48 39 ⟨.tilted, 1, 1, false, 161661200537323632⟩,
  .shared 120 49 34 ⟨.tilted, 1, 2, true, 177674707875920078⟩,
  .shared 120 50 36 ⟨.tilted, 1, 2, true, 185087502803707236⟩], by decide +kernel⟩
private def b54 : PaidBatch .empty 8 := ⟨[
  .shared 120 51 37 ⟨.tilted, 1, 2, true, 192625045948251920⟩,
  .shared 120 52 39 ⟨.tilted, 1, 2, true, 200285413722280140⟩,
  .shared 120 53 40 ⟨.tilted, 1, 2, true, 208066682538517910⟩], by decide +kernel⟩
private def b55 : PaidBatch .empty 8 := ⟨[
  .point 121 44 46,
  .point 121 45 47,
  .point 121 46 48], by decide +kernel⟩
private def b56 : PaidBatch .empty 8 := ⟨[
  .shared 121 47 38 ⟨.tilted, 0, 1, false, 156413626182209349⟩,
  .shared 121 48 39 ⟨.tilted, 1, 1, false, 162930127467688080⟩,
  .shared 121 49 35 ⟨.tilted, 1, 2, true, 179090539864603194⟩], by decide +kernel⟩
private def b57 : PaidBatch .empty 8 := ⟨[
  .shared 121 50 36 ⟨.tilted, 1, 2, true, 186564248400076604⟩,
  .shared 121 51 38 ⟨.tilted, 1, 2, true, 194163987543823532⟩,
  .shared 121 52 39 ⟨.tilted, 1, 2, true, 201887833708569988⟩], by decide +kernel⟩
private def b58 : PaidBatch .empty 8 := ⟨[
  .shared 121 53 41 ⟨.tilted, 1, 2, true, 209733863307041986⟩,
  .point 122 44 46,
  .point 122 45 47], by decide +kernel⟩
private def b59 : PaidBatch .empty 8 := ⟨[
  .point 122 46 48,
  .shared 122 47 38 ⟨.tilted, 0, 1, false, 157631524605088986⟩,
  .shared 122 48 40 ⟨.tilted, 0, 1, false, 164199054398052528⟩], by decide +kernel⟩
private def b60 : PaidBatch .empty 8 := ⟨[
  .shared 122 49 36 ⟨.tilted, 1, 2, true, 180506371853286310⟩,
  .shared 122 50 37 ⟨.tilted, 1, 2, true, 188040993996445972⟩,
  .shared 122 51 39 ⟨.tilted, 1, 2, true, 195702929139395144⟩], by decide +kernel⟩
private def b61 : PaidBatch .empty 8 := ⟨[
  .shared 122 52 40 ⟨.tilted, 1, 2, true, 203490253694859836⟩,
  .shared 122 53 42 ⟨.tilted, 1, 2, true, 211401044075566062⟩,
  .point 123 43 45], by decide +kernel⟩
private def b62 : PaidBatch .empty 8 := ⟨[
  .point 123 44 46,
  .point 123 45 48,
  .shared 123 46 38 ⟨.tilted, 0, 1, false, 152339209018401400⟩], by decide +kernel⟩
private def b63 : PaidBatch .empty 8 := ⟨[
  .shared 123 47 39 ⟨.tilted, 0, 1, false, 158849423027968623⟩,
  .shared 123 48 35 ⟨.tilted, 0, 2, true, 174457187069703000⟩,
  .shared 123 49 36 ⟨.tilted, 1, 2, true, 181922203841969426⟩], by decide +kernel⟩
private def b64 : PaidBatch .empty 8 := ⟨[
  .shared 123 50 38 ⟨.tilted, 1, 2, true, 189517739592815340⟩,
  .shared 123 51 39 ⟨.tilted, 1, 2, true, 197241870734966756⟩,
  .shared 123 52 41 ⟨.tilted, 1, 2, true, 205092673681149684⟩], by decide +kernel⟩
private def b65 : PaidBatch .empty 8 := ⟨[
  .shared 123 53 42 ⟨.tilted, 1, 2, true, 213068224844090138⟩,
  .rectangle 123 42 124 42 48,
  .rectangle 123 41 126 41 47], by decide +kernel⟩
private def b66 : PaidBatch .empty 8 := ⟨[
  .rectangle 123 39 129 39 46,
  .rectangle 123 40 129 40 47,
  .point 124 43 46], by decide +kernel⟩
private def b67 : PaidBatch .empty 8 := ⟨[
  .point 124 44 47,
  .point 124 45 48,
  .shared 124 46 38 ⟨.tilted, 0, 1, false, 153507040727433220⟩], by decide +kernel⟩
private def b68 : PaidBatch .empty 8 := ⟨[
  .shared 124 47 39 ⟨.tilted, 0, 1, false, 160067321450848260⟩,
  .shared 124 48 35 ⟨.tilted, 0, 2, true, 175813387842215856⟩,
  .shared 124 49 37 ⟨.tilted, 1, 2, true, 183338035830652542⟩], by decide +kernel⟩
private def b69 : PaidBatch .empty 8 := ⟨[
  .shared 124 50 38 ⟨.tilted, 1, 2, true, 190994485189184708⟩,
  .shared 124 51 40 ⟨.tilted, 1, 2, true, 198780812330538368⟩,
  .shared 124 52 41 ⟨.tilted, 1, 2, true, 206695093667439532⟩], by decide +kernel⟩
private def b70 : PaidBatch .empty 8 := ⟨[
  .shared 124 53 43 ⟨.tilted, 1, 2, true, 214735405612614214⟩,
  .rectangle 125 42 125 42 48,
  .point 125 43 46], by decide +kernel⟩
private def b71 : PaidBatch .empty 8 := ⟨[
  .point 125 44 47,
  .point 125 45 48,
  .shared 125 46 39 ⟨.tilted, 0, 1, false, 154674872436465040⟩], by decide +kernel⟩
private def b72 : PaidBatch .empty 8 := ⟨[
  .shared 125 47 40 ⟨.tilted, 0, 1, false, 161285219873727897⟩,
  .shared 125 48 36 ⟨.tilted, 0, 2, true, 177169588614728712⟩,
  .shared 125 49 37 ⟨.tilted, 0, 2, true, 184753867819335658⟩], by decide +kernel⟩
private def b73 : PaidBatch .empty 8 := ⟨[
  .shared 125 50 39 ⟨.tilted, 1, 2, true, 192471230785554076⟩,
  .shared 125 51 40 ⟨.tilted, 1, 2, true, 200319753926109980⟩,
  .shared 125 52 42 ⟨.tilted, 1, 2, true, 208297513653729380⟩], by decide +kernel⟩
private def b74 : PaidBatch .empty 8 := ⟨[
  .shared 125 53 43 ⟨.tilted, 1, 2, false, 211750885514575182⟩,
  .point 126 42 45,
  .point 126 43 46], by decide +kernel⟩
private def b75 : PaidBatch .empty 8 := ⟨[
  .point 126 44 48,
  .shared 126 45 38 ⟨.tilted, 0, 1, false, 149294962356633789⟩,
  .shared 126 46 39 ⟨.tilted, 0, 1, false, 155842704145496860⟩], by decide +kernel⟩
private def b76 : PaidBatch .empty 8 := ⟨[
  .shared 126 47 40 ⟨.tilted, 0, 1, false, 162503118296607534⟩,
  .shared 126 48 36 ⟨.tilted, 0, 2, true, 178525789387241568⟩,
  .shared 126 49 38 ⟨.tilted, 0, 2, true, 186169699808018774⟩], by decide +kernel⟩
private def b77 : PaidBatch .empty 8 := ⟨[
  .shared 126 50 39 ⟨.tilted, 1, 2, true, 193947976381923444⟩,
  .shared 126 51 41 ⟨.tilted, 1, 2, true, 201858695521681592⟩,
  .shared 126 52 43 ⟨.tilted, 1, 2, true, 209899933640019228⟩], by decide +kernel⟩
private def b78 : PaidBatch .empty 8 := ⟨[
  .shared 126 53 42 ⟨.tilted, 1, 2, false, 208679949643215596⟩,
  .point 127 42 46,
  .point 127 43 47], by decide +kernel⟩
private def b79 : PaidBatch .empty 8 := ⟨[
  .point 127 44 48,
  .shared 127 45 38 ⟨.tilted, 0, 1, false, 150413689145454786⟩,
  .shared 127 46 39 ⟨.tilted, 0, 1, false, 157010535854528680⟩], by decide +kernel⟩
private def b80 : PaidBatch .empty 8 := ⟨[
  .shared 127 47 41 ⟨.tilted, 0, 1, false, 163721016719487171⟩,
  .shared 127 48 37 ⟨.tilted, 0, 2, true, 179881990159754424⟩,
  .shared 127 49 38 ⟨.tilted, 0, 2, true, 187585531796701890⟩], by decide +kernel⟩
private def b81 : PaidBatch .empty 8 := ⟨[
  .shared 127 50 40 ⟨.tilted, 1, 2, true, 195424721978292812⟩,
  .shared 127 51 42 ⟨.tilted, 1, 2, true, 203397637117253204⟩,
  .shared 127 52 44 ⟨.tilted, 1, 2, true, 211502353626309076⟩], by decide +kernel⟩
private def b82 : PaidBatch .empty 8 := ⟨[
  .shared 127 53 42 ⟨.tilted, 1, 2, false, 206289428517307158⟩,
  .rectangle 127 41 128 41 48,
  .point 128 42 46], by decide +kernel⟩
private def b83 : PaidBatch .empty 8 := ⟨[
  .point 128 43 47,
  .point 128 44 48,
  .shared 128 45 39 ⟨.tilted, 0, 1, false, 151532415934275783⟩], by decide +kernel⟩
private def b84 : PaidBatch .empty 8 := ⟨[
  .shared 128 46 40 ⟨.tilted, 0, 1, false, 158178367563560500⟩,
  .shared 128 47 41 ⟨.tilted, 0, 1, false, 164938915142366808⟩,
  .shared 128 48 37 ⟨.tilted, 0, 2, true, 181238190932267280⟩], by decide +kernel⟩
private def b85 : PaidBatch .empty 8 := ⟨[
  .shared 128 49 39 ⟨.tilted, 0, 2, true, 189001363785385006⟩,
  .shared 128 50 41 ⟨.tilted, 0, 2, true, 196901467574662180⟩,
  .shared 128 51 43 ⟨.tilted, 1, 2, true, 204936578712824816⟩], by decide +kernel⟩
private def b86 : PaidBatch .empty 8 := ⟨[
  .shared 128 52 44 ⟨.tilted, 1, 2, true, 213104773612598924⟩,
  .shared 128 53 43 ⟨.tilted, 1, 2, false, 207827924889650571⟩,
  .point 129 41 45], by decide +kernel⟩
private def b87 : PaidBatch .empty 8 := ⟨[
  .point 129 42 46,
  .point 129 43 47,
  .shared 129 44 38 ⟨.tilted, 0, 1, false, 146073086607215316⟩], by decide +kernel⟩
private def b88 : PaidBatch .empty 8 := ⟨[
  .shared 129 45 39 ⟨.tilted, 0, 1, false, 152651142723096780⟩,
  .shared 129 46 40 ⟨.tilted, 0, 1, false, 159346199272592320⟩,
  .shared 129 47 42 ⟨.tilted, 0, 1, false, 166156813565246445⟩], by decide +kernel⟩
private def b89 : PaidBatch .empty 8 := ⟨[
  .shared 129 48 38 ⟨.tilted, 0, 2, true, 182594391704780136⟩,
  .shared 129 49 40 ⟨.tilted, 0, 2, true, 190417195774068122⟩,
  .shared 129 50 41 ⟨.tilted, 0, 2, true, 198378213171031548⟩], by decide +kernel⟩
private def b90 : PaidBatch .empty 8 := ⟨[
  .shared 129 51 43 ⟨.tilted, 1, 2, true, 206475520308396428⟩,
  .shared 129 52 44 ⟨.tilted, 1, 2, false, 209889625971400156⟩,
  .shared 129 53 44 ⟨.tilted, 1, 2, false, 209366421261993984⟩], by decide +kernel⟩
private def batches : List (PaidBatch .empty 8) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82, b83, b84, b85, b86, b87, b88, b89, b90]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 129 24 2 = true := by decide +kernel
private theorem i26 : checks tiles 129 26 2 = true := by decide +kernel
private theorem i28 : checks tiles 129 28 2 = true := by decide +kernel
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
def receipt : Certificate .empty 8 := ⟨batches, checks_join i24 (checks_join i26 (checks_join i28 (checks_join i30 (checks_join i32 (checks_join i34 (checks_join i36 (checks_join i38 (checks_join i40 (checks_join i42 (checks_join i44 (checks_join i46 (checks_join i48 (checks_join i50 i52)))))))))))))⟩
end Top8


end Low53At2389PriceTableEmpty8
