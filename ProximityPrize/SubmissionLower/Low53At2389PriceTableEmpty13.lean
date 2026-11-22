import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty13
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top13
private def b0 : PaidBatch .empty 13 := ⟨[
  .rectangle 13 39 71 46 37,
  .rectangle 16 47 71 53 42,
  .rectangle 72 47 86 50 44], by decide +kernel⟩
private def b1 : PaidBatch .empty 13 := ⟨[
  .rectangle 72 51 86 53 45,
  .rectangle 72 39 100 42 42,
  .rectangle 72 43 100 46 46], by decide +kernel⟩
private def b2 : PaidBatch .empty 13 := ⟨[
  .rectangle 87 51 93 52 47,
  .rectangle 87 53 93 53 47,
  .rectangle 87 47 100 48 46], by decide +kernel⟩
private def b3 : PaidBatch .empty 13 := ⟨[
  .rectangle 87 49 100 50 48,
  .rectangle 94 53 95 53 48,
  .rectangle 94 52 97 52 48], by decide +kernel⟩
private def b4 : PaidBatch .empty 13 := ⟨[
  .rectangle 94 51 100 51 48,
  .rectangle 96 53 96 53 48,
  .point 97 53 46], by decide +kernel⟩
private def b5 : PaidBatch .empty 13 := ⟨[
  .rectangle 98 52 98 52 48,
  .point 98 53 46,
  .point 99 52 46], by decide +kernel⟩
private def b6 : PaidBatch .empty 13 := ⟨[
  .point 99 53 47,
  .point 100 52 46,
  .point 100 53 47], by decide +kernel⟩
private def b7 : PaidBatch .empty 13 := ⟨[
  .point 101 51 46,
  .point 101 52 47,
  .point 101 53 48], by decide +kernel⟩
private def b8 : PaidBatch .empty 13 := ⟨[
  .rectangle 101 50 102 50 48,
  .rectangle 101 49 104 49 48,
  .rectangle 101 43 108 44 45], by decide +kernel⟩
private def b9 : PaidBatch .empty 13 := ⟨[
  .rectangle 101 45 108 46 47,
  .rectangle 101 47 108 47 47,
  .rectangle 101 48 108 48 48], by decide +kernel⟩
private def b10 : PaidBatch .empty 13 := ⟨[
  .rectangle 101 39 115 40 43,
  .rectangle 101 41 115 42 45,
  .point 102 51 46], by decide +kernel⟩
private def b11 : PaidBatch .empty 13 := ⟨[
  .point 102 52 47,
  .point 102 53 48,
  .rectangle 103 50 103 50 48], by decide +kernel⟩
private def b12 : PaidBatch .empty 13 := ⟨[
  .point 103 51 47,
  .point 103 52 48,
  .shared 103 53 31 ⟨.tilted, 1, 2, false, 186976130983545356⟩], by decide +kernel⟩
private def b13 : PaidBatch .empty 13 := ⟨[
  .point 104 50 46,
  .point 104 51 47,
  .point 104 52 48], by decide +kernel⟩
private def b14 : PaidBatch .empty 13 := ⟨[
  .point 104 53 49,
  .rectangle 105 49 105 49 48,
  .point 105 50 46], by decide +kernel⟩
private def b15 : PaidBatch .empty 13 := ⟨[
  .point 105 51 47,
  .point 105 52 48,
  .shared 105 53 32 ⟨.tilted, 1, 2, false, 190253497370576012⟩], by decide +kernel⟩
private def b16 : PaidBatch .empty 13 := ⟨[
  .point 106 49 46,
  .point 106 50 47,
  .point 106 51 48], by decide +kernel⟩
private def b17 : PaidBatch .empty 13 := ⟨[
  .shared 106 52 32 ⟨.tilted, 1, 2, false, 184495460203918184⟩,
  .shared 106 53 33 ⟨.tilted, 1, 2, false, 191892180564091340⟩,
  .point 107 49 46], by decide +kernel⟩
private def b18 : PaidBatch .empty 13 := ⟨[
  .point 107 50 47,
  .point 107 51 48,
  .shared 107 52 32 ⟨.tilted, 1, 2, false, 186073496953578761⟩], by decide +kernel⟩
private def b19 : PaidBatch .empty 13 := ⟨[
  .shared 107 53 34 ⟨.tilted, 1, 2, false, 193530863757606668⟩,
  .point 108 49 47,
  .point 108 50 48], by decide +kernel⟩
private def b20 : PaidBatch .empty 13 := ⟨[
  .shared 108 51 32 ⟨.tilted, 2, 2, false, 180257093145490215⟩,
  .shared 108 52 33 ⟨.tilted, 1, 2, false, 187651533703239338⟩,
  .shared 108 53 34 ⟨.tilted, 1, 2, false, 195169546951121996⟩], by decide +kernel⟩
private def b21 : PaidBatch .empty 13 := ⟨[
  .point 109 48 46,
  .point 109 49 47,
  .point 109 50 48], by decide +kernel⟩
private def b22 : PaidBatch .empty 13 := ⟨[
  .shared 109 51 32 ⟨.tilted, 2, 2, false, 181775445244933035⟩,
  .shared 109 52 33 ⟨.tilted, 1, 2, false, 189229570452899915⟩,
  .shared 109 53 35 ⟨.tilted, 1, 2, false, 196808230144637324⟩], by decide +kernel⟩
private def b23 : PaidBatch .empty 13 := ⟨[
  .rectangle 109 47 110 47 48,
  .rectangle 109 46 112 46 48,
  .rectangle 109 43 115 44 48], by decide +kernel⟩
private def b24 : PaidBatch .empty 13 := ⟨[
  .rectangle 109 45 115 45 48,
  .point 110 48 46,
  .point 110 49 47], by decide +kernel⟩
private def b25 : PaidBatch .empty 13 := ⟨[
  .point 110 50 48,
  .shared 110 51 33 ⟨.tilted, 2, 2, false, 183293797344375855⟩,
  .shared 110 52 34 ⟨.tilted, 1, 2, false, 190807607202560492⟩], by decide +kernel⟩
private def b26 : PaidBatch .empty 13 := ⟨[
  .shared 110 53 35 ⟨.tilted, 1, 2, false, 198446913338152652⟩,
  .point 111 47 46,
  .point 111 48 47], by decide +kernel⟩
private def b27 : PaidBatch .empty 13 := ⟨[
  .point 111 49 48,
  .shared 111 50 32 ⟨.tilted, 2, 2, false, 180292857430920313⟩,
  .shared 111 51 33 ⟨.tilted, 2, 2, false, 184812149443818675⟩], by decide +kernel⟩
private def b28 : PaidBatch .empty 13 := ⟨[
  .shared 111 52 34 ⟨.tilted, 1, 2, false, 192385643952221069⟩,
  .shared 111 53 36 ⟨.tilted, 1, 2, false, 200085596531667980⟩,
  .point 112 47 46], by decide +kernel⟩
private def b29 : PaidBatch .empty 13 := ⟨[
  .point 112 48 47,
  .point 112 49 48,
  .shared 112 50 32 ⟨.tilted, 2, 2, false, 178826184939778346⟩], by decide +kernel⟩
private def b30 : PaidBatch .empty 13 := ⟨[
  .shared 112 51 34 ⟨.tilted, 2, 2, false, 186330501543261495⟩,
  .shared 112 52 35 ⟨.tilted, 1, 2, false, 193963680701881646⟩,
  .shared 112 53 36 ⟨.tilted, 1, 2, false, 201724279725183308⟩], by decide +kernel⟩
private def b31 : PaidBatch .empty 13 := ⟨[
  .rectangle 113 46 113 46 48,
  .point 113 47 46,
  .point 113 48 47], by decide +kernel⟩
private def b32 : PaidBatch .empty 13 := ⟨[
  .shared 113 49 34 ⟨.tilted, 2, 2, false, 190106796417377609⟩,
  .shared 113 50 33 ⟨.tilted, 2, 2, false, 180285814182640403⟩,
  .shared 113 51 34 ⟨.tilted, 2, 2, false, 187848853642704315⟩], by decide +kernel⟩
private def b33 : PaidBatch .empty 13 := ⟨[
  .shared 113 52 36 ⟨.tilted, 1, 2, false, 195541717451542223⟩,
  .shared 113 53 37 ⟨.tilted, 1, 2, false, 203362962918698636⟩,
  .point 114 46 46], by decide +kernel⟩
private def b34 : PaidBatch .empty 13 := ⟨[
  .point 114 47 47,
  .point 114 48 48,
  .shared 114 49 34 ⟨.tilted, 2, 2, false, 185629216884154586⟩], by decide +kernel⟩
private def b35 : PaidBatch .empty 13 := ⟨[
  .shared 114 50 33 ⟨.tilted, 2, 2, false, 181745443425502460⟩,
  .shared 114 51 35 ⟨.tilted, 2, 2, false, 189367205742147135⟩,
  .shared 114 52 36 ⟨.tilted, 1, 2, false, 197119754201202800⟩], by decide +kernel⟩
private def b36 : PaidBatch .empty 13 := ⟨[
  .shared 114 53 38 ⟨.tilted, 1, 2, false, 205001646112213964⟩,
  .point 115 46 46,
  .point 115 47 47], by decide +kernel⟩
private def b37 : PaidBatch .empty 13 := ⟨[
  .point 115 48 48,
  .shared 115 49 33 ⟨.tilted, 2, 2, false, 181151637350931563⟩,
  .shared 115 50 34 ⟨.tilted, 2, 2, false, 183205072668364517⟩], by decide +kernel⟩
private def b38 : PaidBatch .empty 13 := ⟨[
  .shared 115 51 35 ⟨.tilted, 2, 2, false, 190885557841589955⟩,
  .shared 115 52 37 ⟨.tilted, 1, 2, false, 198697790950863377⟩,
  .shared 115 53 38 ⟨.tilted, 1, 2, false, 206640329305729292⟩], by decide +kernel⟩
private def b39 : PaidBatch .empty 13 := ⟨[
  .rectangle 116 45 116 45 48,
  .point 116 46 46,
  .point 116 47 47], by decide +kernel⟩
private def b40 : PaidBatch .empty 13 := ⟨[
  .shared 116 48 38 ⟨.tilted, 2, 1, false, 169590185802491070⟩,
  .shared 116 49 33 ⟨.tilted, 2, 2, false, 177059646301560842⟩,
  .shared 116 50 34 ⟨.tilted, 2, 2, false, 184664701911226574⟩], by decide +kernel⟩
private def b41 : PaidBatch .empty 13 := ⟨[
  .shared 116 51 36 ⟨.tilted, 2, 2, false, 192403909941032775⟩,
  .shared 116 52 37 ⟨.tilted, 1, 2, false, 200275827700523954⟩,
  .shared 116 53 39 ⟨.tilted, 1, 2, false, 208279012499244620⟩], by decide +kernel⟩
private def b42 : PaidBatch .empty 13 := ⟨[
  .rectangle 116 44 119 44 48,
  .rectangle 116 41 122 41 46,
  .rectangle 116 42 122 42 47], by decide +kernel⟩
private def b43 : PaidBatch .empty 13 := ⟨[
  .rectangle 116 43 122 43 48,
  .rectangle 116 39 129 39 46,
  .rectangle 116 40 129 40 47], by decide +kernel⟩
private def b44 : PaidBatch .empty 13 := ⟨[
  .point 117 45 45,
  .point 117 46 47,
  .point 117 47 48], by decide +kernel⟩
private def b45 : PaidBatch .empty 13 := ⟨[
  .shared 117 48 39 ⟨.tilted, 2, 1, false, 170935254713102583⟩,
  .shared 117 49 34 ⟨.tilted, 2, 2, false, 178461514481479130⟩,
  .shared 117 50 35 ⟨.tilted, 2, 2, false, 186124331154088631⟩], by decide +kernel⟩
private def b46 : PaidBatch .empty 13 := ⟨[
  .shared 117 51 36 ⟨.tilted, 2, 2, false, 193922262040475595⟩,
  .shared 117 52 38 ⟨.tilted, 1, 2, false, 201853864450184531⟩,
  .shared 117 53 40 ⟨.tilted, 1, 2, false, 209917695692759948⟩], by decide +kernel⟩
private def b47 : PaidBatch .empty 13 := ⟨[
  .point 118 45 46,
  .point 118 46 47,
  .point 118 47 48], by decide +kernel⟩
private def b48 : PaidBatch .empty 13 := ⟨[
  .shared 118 48 36 ⟨.tilted, 2, 2, false, 189578490614957042⟩,
  .shared 118 49 34 ⟨.tilted, 2, 2, false, 179863382661397418⟩,
  .shared 118 50 36 ⟨.tilted, 2, 2, false, 187583960396950688⟩], by decide +kernel⟩
private def b49 : PaidBatch .empty 13 := ⟨[
  .shared 118 51 37 ⟨.tilted, 2, 2, false, 195440614139918415⟩,
  .shared 118 52 39 ⟨.tilted, 1, 2, false, 203431901199845108⟩,
  .shared 118 53 40 ⟨.tilted, 1, 2, false, 211556378886275276⟩], by decide +kernel⟩
private def b50 : PaidBatch .empty 13 := ⟨[
  .point 119 45 46,
  .point 119 46 47,
  .shared 119 47 38 ⟨.tilted, 2, 1, false, 166125457409297945⟩], by decide +kernel⟩
private def b51 : PaidBatch .empty 13 := ⟨[
  .shared 119 48 35 ⟨.tilted, 2, 2, false, 185726558101240061⟩,
  .shared 119 49 35 ⟨.tilted, 2, 2, false, 181265250841315706⟩,
  .shared 119 50 36 ⟨.tilted, 2, 2, false, 189043589639812745⟩], by decide +kernel⟩
private def b52 : PaidBatch .empty 13 := ⟨[
  .shared 119 51 38 ⟨.tilted, 2, 2, false, 196958966239361235⟩,
  .shared 119 52 39 ⟨.tilted, 1, 2, false, 205009937949505685⟩,
  .shared 119 53 41 ⟨.tilted, 1, 2, false, 213195062079790604⟩], by decide +kernel⟩
private def b53 : PaidBatch .empty 13 := ⟨[
  .point 120 44 45,
  .point 120 45 47,
  .point 120 46 48], by decide +kernel⟩
private def b54 : PaidBatch .empty 13 := ⟨[
  .shared 120 47 39 ⟨.tilted, 2, 1, false, 167414688844239677⟩,
  .shared 120 48 35 ⟨.tilted, 2, 2, false, 181874625587523080⟩,
  .shared 120 49 35 ⟨.tilted, 2, 2, false, 182667119021233994⟩], by decide +kernel⟩
private def b55 : PaidBatch .empty 13 := ⟨[
  .shared 120 50 37 ⟨.tilted, 2, 2, false, 190503218882674802⟩,
  .shared 120 51 38 ⟨.tilted, 2, 2, false, 198477318338804055⟩,
  .shared 120 52 40 ⟨.tilted, 1, 2, false, 206587974699166262⟩], by decide +kernel⟩
private def b56 : PaidBatch .empty 13 := ⟨[
  .shared 120 53 42 ⟨.tilted, 1, 2, false, 214833745273305932⟩,
  .point 121 44 46,
  .point 121 45 47], by decide +kernel⟩
private def b57 : PaidBatch .empty 13 := ⟨[
  .point 121 46 48,
  .shared 121 47 39 ⟨.tilted, 2, 1, false, 168703920279181409⟩,
  .shared 121 48 34 ⟨.tilted, 2, 2, false, 178022693073806099⟩], by decide +kernel⟩
private def b58 : PaidBatch .empty 13 := ⟨[
  .shared 121 49 36 ⟨.tilted, 2, 2, false, 184068987201152282⟩,
  .shared 121 50 37 ⟨.tilted, 2, 2, false, 191962848125536859⟩,
  .shared 121 51 39 ⟨.tilted, 2, 2, false, 199995670438246875⟩], by decide +kernel⟩
private def b59 : PaidBatch .empty 13 := ⟨[
  .shared 121 52 41 ⟨.tilted, 1, 2, false, 208166011448826839⟩,
  .shared 121 53 42 ⟨.tilted, 1, 2, false, 216472428466821260⟩,
  .point 122 44 46], by decide +kernel⟩
private def b60 : PaidBatch .empty 13 := ⟨[
  .point 122 45 47,
  .shared 122 46 38 ⟨.tilted, 2, 1, false, 162469955415415040⟩,
  .shared 122 47 40 ⟨.tilted, 2, 1, false, 169993151714123141⟩], by decide +kernel⟩
private def b61 : PaidBatch .empty 13 := ⟨[
  .shared 122 48 35 ⟨.tilted, 2, 2, false, 177660599266160148⟩,
  .shared 122 49 36 ⟨.tilted, 2, 2, false, 185470855381070570⟩,
  .shared 122 50 38 ⟨.tilted, 2, 2, false, 193422477368398916⟩], by decide +kernel⟩
private def b62 : PaidBatch .empty 13 := ⟨[
  .shared 122 51 40 ⟨.tilted, 2, 2, false, 201514022537689695⟩,
  .shared 122 52 41 ⟨.tilted, 1, 2, false, 209744048198487416⟩,
  .shared 122 53 43 ⟨.tilted, 1, 2, false, 218111111660336588⟩], by decide +kernel⟩
private def b63 : PaidBatch .empty 13 := ⟨[
  .rectangle 123 43 123 43 48,
  .point 123 44 46,
  .point 123 45 48], by decide +kernel⟩
private def b64 : PaidBatch .empty 13 := ⟨[
  .shared 123 46 39 ⟨.tilted, 2, 1, false, 163704311168323985⟩,
  .shared 123 47 40 ⟨.tilted, 2, 1, false, 171282383149064873⟩,
  .shared 123 48 35 ⟨.tilted, 2, 2, false, 179005668176771661⟩], by decide +kernel⟩
private def b65 : PaidBatch .empty 13 := ⟨[
  .shared 123 49 37 ⟨.tilted, 2, 2, false, 186872723560988858⟩,
  .shared 123 50 38 ⟨.tilted, 2, 2, false, 194882106611260973⟩,
  .shared 123 51 40 ⟨.tilted, 2, 2, false, 203032374637132515⟩], by decide +kernel⟩
private def b66 : PaidBatch .empty 13 := ⟨[
  .shared 123 52 42 ⟨.tilted, 1, 2, false, 211322084948147993⟩,
  .shared 123 53 44 ⟨.tilted, 1, 2, false, 219749794853851916⟩,
  .rectangle 123 42 126 42 48], by decide +kernel⟩
private def b67 : PaidBatch .empty 13 := ⟨[
  .rectangle 123 41 129 41 48,
  .point 124 43 46,
  .point 124 44 47], by decide +kernel⟩
private def b68 : PaidBatch .empty 13 := ⟨[
  .point 124 45 48,
  .shared 124 46 39 ⟨.tilted, 2, 1, false, 164938666921232930⟩,
  .shared 124 47 38 ⟨.tilted, 2, 2, false, 190266034400344886⟩], by decide +kernel⟩
private def b69 : PaidBatch .empty 13 := ⟨[
  .shared 124 48 36 ⟨.tilted, 2, 2, false, 180350737087383174⟩,
  .shared 124 49 37 ⟨.tilted, 2, 2, false, 188274591740907146⟩,
  .shared 124 50 39 ⟨.tilted, 2, 2, false, 196341735854123030⟩], by decide +kernel⟩
private def b70 : PaidBatch .empty 13 := ⟨[
  .shared 124 51 41 ⟨.tilted, 2, 2, false, 204550726736575335⟩,
  .shared 124 52 43 ⟨.tilted, 1, 2, false, 212900121697808570⟩,
  .shared 124 53 45 ⟨.tilted, 1, 2, false, 221388478047367244⟩], by decide +kernel⟩
private def b71 : PaidBatch .empty 13 := ⟨[
  .point 125 43 46,
  .point 125 44 47,
  .point 125 45 48], by decide +kernel⟩
private def b72 : PaidBatch .empty 13 := ⟨[
  .shared 125 46 40 ⟨.tilted, 2, 1, false, 166173022674141875⟩,
  .shared 125 47 37 ⟨.tilted, 2, 2, false, 187003521334596707⟩,
  .shared 125 48 36 ⟨.tilted, 2, 2, false, 181695805997994687⟩], by decide +kernel⟩
private def b73 : PaidBatch .empty 13 := ⟨[
  .shared 125 49 38 ⟨.tilted, 2, 2, false, 189676459920825434⟩,
  .shared 125 50 40 ⟨.tilted, 2, 2, false, 197801365096985087⟩,
  .shared 125 51 41 ⟨.tilted, 2, 2, false, 206069078836018155⟩], by decide +kernel⟩
private def b74 : PaidBatch .empty 13 := ⟨[
  .shared 125 52 43 ⟨.tilted, 1, 2, false, 214478158447469147⟩,
  .shared 125 53 45 ⟨.tilted, 1, 2, false, 223027161240882572⟩,
  .point 126 43 46], by decide +kernel⟩
private def b75 : PaidBatch .empty 13 := ⟨[
  .point 126 44 48,
  .shared 126 45 39 ⟨.tilted, 2, 1, false, 159814220518543944⟩,
  .shared 126 46 40 ⟨.tilted, 2, 1, false, 167407378427050820⟩], by decide +kernel⟩
private def b76 : PaidBatch .empty 13 := ⟨[
  .shared 126 47 37 ⟨.tilted, 2, 2, false, 183741008268848528⟩,
  .shared 126 48 37 ⟨.tilted, 2, 2, false, 183040874908606200⟩,
  .shared 126 49 38 ⟨.tilted, 2, 2, false, 191078328100743722⟩], by decide +kernel⟩
private def b77 : PaidBatch .empty 13 := ⟨[
  .shared 126 50 40 ⟨.tilted, 2, 2, false, 199260994339847144⟩,
  .shared 126 51 42 ⟨.tilted, 2, 2, false, 207587430935460975⟩,
  .shared 126 52 44 ⟨.tilted, 1, 2, false, 216056195197129724⟩], by decide +kernel⟩
private def b78 : PaidBatch .empty 13 := ⟨[
  .shared 126 53 46 ⟨.tilted, 1, 2, false, 224665844434397900⟩,
  .point 127 42 45,
  .point 127 43 47], by decide +kernel⟩
private def b79 : PaidBatch .empty 13 := ⟨[
  .point 127 44 48,
  .shared 127 45 39 ⟨.tilted, 2, 1, false, 160994662383057096⟩,
  .shared 127 46 41 ⟨.tilted, 2, 1, false, 168641734179959765⟩], by decide +kernel⟩
private def b80 : PaidBatch .empty 13 := ⟨[
  .shared 127 47 36 ⟨.tilted, 2, 2, false, 180478495203100349⟩,
  .shared 127 48 37 ⟨.tilted, 2, 2, false, 184385943819217713⟩,
  .shared 127 49 39 ⟨.tilted, 2, 2, false, 192480196280662010⟩], by decide +kernel⟩
private def b81 : PaidBatch .empty 13 := ⟨[
  .shared 127 50 41 ⟨.tilted, 2, 2, false, 200720623582709201⟩,
  .shared 127 51 43 ⟨.tilted, 2, 2, false, 209105783034903795⟩,
  .shared 127 52 45 ⟨.tilted, 1, 2, false, 217634231946790301⟩], by decide +kernel⟩
private def b82 : PaidBatch .empty 13 := ⟨[
  .shared 127 53 47 ⟨.tilted, 1, 2, false, 226304527627913228⟩,
  .point 128 42 46,
  .point 128 43 47], by decide +kernel⟩
private def b83 : PaidBatch .empty 13 := ⟨[
  .point 128 44 48,
  .shared 128 45 40 ⟨.tilted, 2, 1, false, 162175104247570248⟩,
  .shared 128 46 41 ⟨.tilted, 2, 1, false, 169876089932868710⟩], by decide +kernel⟩
private def b84 : PaidBatch .empty 13 := ⟨[
  .shared 128 47 37 ⟨.tilted, 2, 2, false, 181250753334008115⟩,
  .shared 128 48 38 ⟨.tilted, 2, 2, false, 185731012729829226⟩,
  .shared 128 49 40 ⟨.tilted, 2, 2, false, 193882064460580298⟩], by decide +kernel⟩
private def b85 : PaidBatch .empty 13 := ⟨[
  .shared 128 50 41 ⟨.tilted, 2, 2, false, 202180252825571258⟩,
  .shared 128 51 43 ⟨.tilted, 2, 2, false, 210624135134346615⟩,
  .shared 128 52 45 ⟨.tilted, 1, 2, false, 219212268696450878⟩], by decide +kernel⟩
private def b86 : PaidBatch .empty 13 := ⟨[
  .shared 128 53 48 ⟨.tilted, 1, 2, false, 227943210821428556⟩,
  .point 129 42 46,
  .point 129 43 47], by decide +kernel⟩
private def b87 : PaidBatch .empty 13 := ⟨[
  .shared 129 44 39 ⟨.tilted, 2, 1, false, 155754515728087991⟩,
  .shared 129 45 40 ⟨.tilted, 2, 1, false, 163355546112083400⟩,
  .shared 129 46 42 ⟨.tilted, 2, 1, false, 171110445685777655⟩], by decide +kernel⟩
private def b88 : PaidBatch .empty 13 := ⟨[
  .shared 129 47 38 ⟨.tilted, 2, 2, false, 182829965704247070⟩,
  .shared 129 48 38 ⟨.tilted, 2, 2, false, 187076081640440739⟩,
  .shared 129 49 40 ⟨.tilted, 2, 2, false, 195283932640498586⟩], by decide +kernel⟩
private def b89 : PaidBatch .empty 13 := ⟨[
  .shared 129 50 42 ⟨.tilted, 2, 2, false, 203639882068433315⟩,
  .shared 129 51 44 ⟨.tilted, 2, 2, false, 212142487233789435⟩,
  .shared 129 52 46 ⟨.tilted, 1, 2, false, 220790305446111455⟩], by decide +kernel⟩
private def b90 : PaidBatch .empty 13 := ⟨[
  .shared 129 53 48 ⟨.tilted, 1, 2, false, 229581894014943884⟩], by decide +kernel⟩
private def batches : List (PaidBatch .empty 13) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82, b83, b84, b85, b86, b87, b88, b89, b90]
private abbrev tiles := tilesOf batches
private theorem i39 : checks tiles 129 39 2 = true := by decide +kernel
private theorem i41 : checks tiles 129 41 2 = true := by decide +kernel
private theorem i43 : checks tiles 129 43 2 = true := by decide +kernel
private theorem i45 : checks tiles 129 45 2 = true := by decide +kernel
private theorem i47 : checks tiles 129 47 2 = true := by decide +kernel
private theorem i49 : checks tiles 129 49 2 = true := by decide +kernel
private theorem i51 : checks tiles 129 51 2 = true := by decide +kernel
private theorem i53 : checks tiles 129 53 1 = true := by decide +kernel
def receipt : Certificate .empty 13 := ⟨batches, checks_join i39 (checks_join i41 (checks_join i43 (checks_join i45 (checks_join i47 (checks_join i49 (checks_join i51 i53))))))⟩
end Top13


end Low53At2389PriceTableEmpty13
