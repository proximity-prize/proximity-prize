import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty9
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top9
private def b0 : PaidBatch .empty 9 := ⟨[
  .rectangle 9 27 69 40 39,
  .rectangle 14 41 71 47 37,
  .rectangle 16 48 71 53 40], by decide +kernel⟩
private def b1 : PaidBatch .empty 9 := ⟨[
  .rectangle 70 34 99 40 43,
  .rectangle 70 27 129 30 39,
  .rectangle 70 31 129 33 41], by decide +kernel⟩
private def b2 : PaidBatch .empty 9 := ⟨[
  .rectangle 72 48 86 53 47,
  .rectangle 72 41 100 44 44,
  .rectangle 72 45 100 47 46], by decide +kernel⟩
private def b3 : PaidBatch .empty 9 := ⟨[
  .rectangle 87 48 93 50 45,
  .rectangle 87 51 93 53 48,
  .rectangle 94 52 97 52 47], by decide +kernel⟩
private def b4 : PaidBatch .empty 9 := ⟨[
  .rectangle 94 53 97 53 48,
  .rectangle 94 48 100 49 47,
  .rectangle 94 50 100 50 47], by decide +kernel⟩
private def b5 : PaidBatch .empty 9 := ⟨[
  .rectangle 94 51 100 51 48,
  .point 98 53 46,
  .rectangle 98 52 99 52 48], by decide +kernel⟩
private def b6 : PaidBatch .empty 9 := ⟨[
  .point 99 53 46,
  .point 100 52 46,
  .point 100 53 46], by decide +kernel⟩
private def b7 : PaidBatch .empty 9 := ⟨[
  .rectangle 100 38 114 40 44,
  .rectangle 100 34 129 35 42,
  .rectangle 100 36 129 37 45], by decide +kernel⟩
private def b8 : PaidBatch .empty 9 := ⟨[
  .rectangle 101 51 101 51 48,
  .point 101 52 46,
  .point 101 53 47], by decide +kernel⟩
private def b9 : PaidBatch .empty 9 := ⟨[
  .rectangle 101 49 104 49 48,
  .rectangle 101 50 104 50 48,
  .rectangle 101 43 108 44 45], by decide +kernel⟩
private def b10 : PaidBatch .empty 9 := ⟨[
  .rectangle 101 45 108 46 47,
  .rectangle 101 47 108 47 47,
  .rectangle 101 48 108 48 48], by decide +kernel⟩
private def b11 : PaidBatch .empty 9 := ⟨[
  .rectangle 101 41 115 42 46,
  .point 102 51 46,
  .point 102 52 46], by decide +kernel⟩
private def b12 : PaidBatch .empty 9 := ⟨[
  .point 102 53 47,
  .point 103 51 46,
  .point 103 52 47], by decide +kernel⟩
private def b13 : PaidBatch .empty 9 := ⟨[
  .point 103 53 48,
  .point 104 51 46,
  .point 104 52 47], by decide +kernel⟩
private def b14 : PaidBatch .empty 9 := ⟨[
  .point 104 53 48,
  .point 105 50 46,
  .point 105 51 47], by decide +kernel⟩
private def b15 : PaidBatch .empty 9 := ⟨[
  .point 105 52 48,
  .point 105 53 49,
  .rectangle 105 49 106 49 48], by decide +kernel⟩
private def b16 : PaidBatch .empty 9 := ⟨[
  .point 106 50 46,
  .point 106 51 47,
  .point 106 52 48], by decide +kernel⟩
private def b17 : PaidBatch .empty 9 := ⟨[
  .point 106 53 49,
  .point 107 49 46,
  .point 107 50 47], by decide +kernel⟩
private def b18 : PaidBatch .empty 9 := ⟨[
  .point 107 51 48,
  .shared 107 52 32 ⟨.tilted, 1, 2, true, 182292036987940328⟩,
  .shared 107 53 33 ⟨.tilted, 1, 2, true, 189455139493400808⟩], by decide +kernel⟩
private def b19 : PaidBatch .empty 9 := ⟨[
  .point 108 49 46,
  .point 108 50 47,
  .point 108 51 48], by decide +kernel⟩
private def b20 : PaidBatch .empty 9 := ⟨[
  .shared 108 52 32 ⟨.tilted, 1, 2, true, 183894456974230176⟩,
  .shared 108 53 33 ⟨.tilted, 1, 2, true, 191122320261924884⟩,
  .point 109 48 46], by decide +kernel⟩
private def b21 : PaidBatch .empty 9 := ⟨[
  .point 109 49 47,
  .point 109 50 48,
  .shared 109 51 32 ⟨.tilted, 1, 2, true, 178319543469918171⟩], by decide +kernel⟩
private def b22 : PaidBatch .empty 9 := ⟨[
  .shared 109 52 33 ⟨.tilted, 1, 2, true, 185496876960520024⟩,
  .shared 109 53 34 ⟨.tilted, 1, 2, true, 192789501030448960⟩,
  .rectangle 109 47 110 47 48], by decide +kernel⟩
private def b23 : PaidBatch .empty 9 := ⟨[
  .rectangle 109 46 112 46 48,
  .rectangle 109 43 115 44 48,
  .rectangle 109 45 115 45 48], by decide +kernel⟩
private def b24 : PaidBatch .empty 9 := ⟨[
  .point 110 48 46,
  .point 110 49 47,
  .point 110 50 48], by decide +kernel⟩
private def b25 : PaidBatch .empty 9 := ⟨[
  .shared 110 51 32 ⟨.tilted, 1, 2, true, 179858485065489783⟩,
  .shared 110 52 33 ⟨.tilted, 1, 2, true, 187099296946809872⟩,
  .shared 110 53 35 ⟨.tilted, 1, 2, true, 194456681798973036⟩], by decide +kernel⟩
private def b26 : PaidBatch .empty 9 := ⟨[
  .rectangle 111 47 111 47 48,
  .point 111 48 46,
  .point 111 49 47], by decide +kernel⟩
private def b27 : PaidBatch .empty 9 := ⟨[
  .point 111 50 48,
  .shared 111 51 33 ⟨.tilted, 1, 2, true, 181397426661061395⟩,
  .shared 111 52 34 ⟨.tilted, 1, 2, true, 188701716933099720⟩], by decide +kernel⟩
private def b28 : PaidBatch .empty 9 := ⟨[
  .shared 111 53 35 ⟨.tilted, 1, 2, true, 196123862567497112⟩,
  .point 112 47 46,
  .point 112 48 47], by decide +kernel⟩
private def b29 : PaidBatch .empty 9 := ⟨[
  .point 112 49 48,
  .shared 112 50 32 ⟨.tilted, 1, 2, true, 175689660935025495⟩,
  .shared 112 51 33 ⟨.tilted, 1, 2, true, 182936368256633007⟩], by decide +kernel⟩
private def b30 : PaidBatch .empty 9 := ⟨[
  .shared 112 52 34 ⟨.tilted, 1, 2, true, 190304136919389568⟩,
  .shared 112 53 36 ⟨.tilted, 1, 2, true, 197791043336021188⟩,
  .rectangle 113 46 113 46 48], by decide +kernel⟩
private def b31 : PaidBatch .empty 9 := ⟨[
  .point 113 47 46,
  .point 113 48 47,
  .point 113 49 48], by decide +kernel⟩
private def b32 : PaidBatch .empty 9 := ⟨[
  .shared 113 50 32 ⟨.tilted, 1, 2, true, 177166406531394863⟩,
  .shared 113 51 34 ⟨.tilted, 1, 2, true, 184475309852204619⟩,
  .shared 113 52 35 ⟨.tilted, 1, 2, true, 191906556905679416⟩], by decide +kernel⟩
private def b33 : PaidBatch .empty 9 := ⟨[
  .shared 113 53 36 ⟨.tilted, 1, 2, true, 199458224104545264⟩,
  .point 114 46 45,
  .point 114 47 47], by decide +kernel⟩
private def b34 : PaidBatch .empty 9 := ⟨[
  .point 114 48 48,
  .shared 114 49 38 ⟨.tilted, 1, 1, false, 164539944784489002⟩,
  .shared 114 50 33 ⟨.tilted, 1, 2, true, 178643152127764231⟩], by decide +kernel⟩
private def b35 : PaidBatch .empty 9 := ⟨[
  .shared 114 51 34 ⟨.tilted, 1, 2, true, 186014251447776231⟩,
  .shared 114 52 36 ⟨.tilted, 1, 2, true, 193508976891969264⟩,
  .shared 114 53 37 ⟨.tilted, 1, 2, false, 199452363899241470⟩], by decide +kernel⟩
private def b36 : PaidBatch .empty 9 := ⟨[
  .point 115 46 46,
  .point 115 47 47,
  .point 115 48 48], by decide +kernel⟩
private def b37 : PaidBatch .empty 9 := ⟨[
  .shared 115 49 38 ⟨.tilted, 1, 1, false, 165882822967483626⟩,
  .shared 115 50 34 ⟨.tilted, 1, 2, true, 180119897724133599⟩,
  .shared 115 51 35 ⟨.tilted, 1, 2, true, 187553193043347843⟩], by decide +kernel⟩
private def b38 : PaidBatch .empty 9 := ⟨[
  .shared 115 52 36 ⟨.tilted, 1, 2, true, 195111396878259112⟩,
  .shared 115 53 36 ⟨.tilted, 1, 2, false, 195532046867889775⟩,
  .rectangle 115 38 129 39 47], by decide +kernel⟩
private def b39 : PaidBatch .empty 9 := ⟨[
  .rectangle 115 40 129 40 47,
  .rectangle 116 45 116 45 48,
  .point 116 46 46], by decide +kernel⟩
private def b40 : PaidBatch .empty 9 := ⟨[
  .point 116 47 47,
  .point 116 48 48,
  .shared 116 49 33 ⟨.tilted, 1, 2, true, 174229266496573482⟩], by decide +kernel⟩
private def b41 : PaidBatch .empty 9 := ⟨[
  .shared 116 50 34 ⟨.tilted, 1, 2, true, 181596643320502967⟩,
  .shared 116 51 35 ⟨.tilted, 1, 2, true, 189092134638919455⟩,
  .shared 116 52 37 ⟨.tilted, 1, 2, true, 196713816864548960⟩], by decide +kernel⟩
private def b42 : PaidBatch .empty 9 := ⟨[
  .shared 116 53 37 ⟨.tilted, 1, 2, false, 194789397018431788⟩,
  .rectangle 116 44 119 44 48,
  .rectangle 116 41 122 41 46], by decide +kernel⟩
private def b43 : PaidBatch .empty 9 := ⟨[
  .rectangle 116 42 122 42 47,
  .rectangle 116 43 122 43 48,
  .point 117 45 46], by decide +kernel⟩
private def b44 : PaidBatch .empty 9 := ⟨[
  .point 117 46 47,
  .point 117 47 48,
  .shared 117 48 38 ⟨.tilted, 1, 1, false, 161886346809907323⟩], by decide +kernel⟩
private def b45 : PaidBatch .empty 9 := ⟨[
  .shared 117 49 33 ⟨.tilted, 1, 2, true, 175645098485256598⟩,
  .shared 117 50 35 ⟨.tilted, 1, 2, true, 183073388916872335⟩,
  .shared 117 51 36 ⟨.tilted, 1, 2, true, 190631076234491067⟩], by decide +kernel⟩
private def b46 : PaidBatch .empty 9 := ⟨[
  .shared 117 52 38 ⟨.tilted, 1, 2, false, 198289984728454703⟩,
  .shared 117 53 37 ⟨.tilted, 1, 2, false, 196353701516831548⟩,
  .point 118 45 46], by decide +kernel⟩
private def b47 : PaidBatch .empty 9 := ⟨[
  .point 118 46 47,
  .point 118 47 48,
  .shared 118 48 38 ⟨.tilted, 1, 1, false, 163176272898143148⟩], by decide +kernel⟩
private def b48 : PaidBatch .empty 9 := ⟨[
  .shared 118 49 34 ⟨.tilted, 1, 2, true, 177060930473939714⟩,
  .shared 118 50 35 ⟨.tilted, 1, 2, true, 184550134513241703⟩,
  .shared 118 51 37 ⟨.tilted, 1, 2, true, 192170017830062679⟩], by decide +kernel⟩
private def b49 : PaidBatch .empty 9 := ⟨[
  .shared 118 52 37 ⟨.tilted, 1, 2, false, 193526697662233562⟩,
  .shared 118 53 38 ⟨.tilted, 1, 2, false, 197918006015231308⟩,
  .point 119 45 46], by decide +kernel⟩
private def b50 : PaidBatch .empty 9 := ⟨[
  .point 119 46 47,
  .point 119 47 48,
  .shared 119 48 39 ⟨.tilted, 1, 1, false, 164466198986378973⟩], by decide +kernel⟩
private def b51 : PaidBatch .empty 9 := ⟨[
  .shared 119 49 34 ⟨.tilted, 1, 2, true, 178476762462622830⟩,
  .shared 119 50 36 ⟨.tilted, 1, 2, true, 186026880109611071⟩,
  .shared 119 51 37 ⟨.tilted, 1, 2, true, 193708959425634291⟩], by decide +kernel⟩
private def b52 : PaidBatch .empty 9 := ⟨[
  .shared 119 52 37 ⟨.tilted, 1, 2, false, 192266887996724361⟩,
  .shared 119 53 38 ⟨.tilted, 1, 2, false, 199482310513631068⟩,
  .point 120 44 46], by decide +kernel⟩
private def b53 : PaidBatch .empty 9 := ⟨[
  .point 120 45 47,
  .point 120 46 48,
  .shared 120 47 38 ⟨.tilted, 0, 1, false, 159026426237504461⟩], by decide +kernel⟩
private def b54 : PaidBatch .empty 9 := ⟨[
  .shared 120 48 39 ⟨.tilted, 1, 1, false, 165756125074614798⟩,
  .shared 120 49 35 ⟨.tilted, 1, 2, true, 179892594451305946⟩,
  .shared 120 50 36 ⟨.tilted, 1, 2, true, 187503625705980439⟩], by decide +kernel⟩
private def b55 : PaidBatch .empty 9 := ⟨[
  .shared 120 51 38 ⟨.tilted, 1, 2, true, 195247901021205903⟩,
  .shared 120 52 38 ⟨.tilted, 1, 2, false, 193774393225817346⟩,
  .shared 120 53 39 ⟨.tilted, 1, 2, false, 201046615012030828⟩], by decide +kernel⟩
private def b56 : PaidBatch .empty 9 := ⟨[
  .point 121 44 46,
  .point 121 45 47,
  .point 121 46 48], by decide +kernel⟩
private def b57 : PaidBatch .empty 9 := ⟨[
  .shared 121 47 39 ⟨.tilted, 0, 1, false, 160264362024618481⟩,
  .shared 121 48 40 ⟨.tilted, 1, 1, false, 167046051162850623⟩,
  .shared 121 49 35 ⟨.tilted, 1, 2, true, 181308426439989062⟩], by decide +kernel⟩
private def b58 : PaidBatch .empty 9 := ⟨[
  .shared 121 50 37 ⟨.tilted, 1, 2, true, 188980371302349807⟩,
  .shared 121 51 38 ⟨.tilted, 1, 2, false, 195318678149631675⟩,
  .shared 121 52 38 ⟨.tilted, 1, 2, false, 195281898454910331⟩], by decide +kernel⟩
private def b59 : PaidBatch .empty 9 := ⟨[
  .shared 121 53 40 ⟨.tilted, 1, 2, false, 202610919510430588⟩,
  .point 122 44 46,
  .point 122 45 47], by decide +kernel⟩
private def b60 : PaidBatch .empty 9 := ⟨[
  .point 122 46 48,
  .shared 122 47 39 ⟨.tilted, 0, 1, false, 161502297811732501⟩,
  .shared 122 48 40 ⟨.tilted, 0, 1, false, 168335977251086448⟩], by decide +kernel⟩
private def b61 : PaidBatch .empty 9 := ⟨[
  .shared 122 49 36 ⟨.tilted, 1, 2, true, 182724258428672178⟩,
  .shared 122 50 38 ⟨.tilted, 1, 2, true, 190457116898719175⟩,
  .shared 122 51 37 ⟨.tilted, 1, 2, false, 189511126155359919⟩], by decide +kernel⟩
private def b62 : PaidBatch .empty 9 := ⟨[
  .shared 122 52 39 ⟨.tilted, 1, 2, false, 196789403684003316⟩,
  .shared 122 53 40 ⟨.tilted, 1, 2, false, 204175224008830348⟩,
  .point 123 43 45], by decide +kernel⟩
private def b63 : PaidBatch .empty 9 := ⟨[
  .point 123 44 47,
  .point 123 45 48,
  .shared 123 46 38 ⟨.tilted, 0, 1, false, 155970281900468853⟩], by decide +kernel⟩
private def b64 : PaidBatch .empty 9 := ⟨[
  .shared 123 47 39 ⟨.tilted, 0, 1, false, 162740233598846521⟩,
  .shared 123 48 35 ⟨.tilted, 0, 2, true, 176485333161994982⟩,
  .shared 123 49 37 ⟨.tilted, 1, 2, true, 184140090417355294⟩], by decide +kernel⟩
private def b65 : PaidBatch .empty 9 := ⟨[
  .shared 123 50 38 ⟨.tilted, 1, 2, true, 191933862495088543⟩,
  .shared 123 51 38 ⟨.tilted, 1, 2, false, 190962793908783123⟩,
  .shared 123 52 39 ⟨.tilted, 1, 2, false, 198296908913096301⟩], by decide +kernel⟩
private def b66 : PaidBatch .empty 9 := ⟨[
  .shared 123 53 41 ⟨.tilted, 1, 2, false, 205739528507230108⟩,
  .rectangle 123 42 124 42 48,
  .rectangle 123 41 126 41 48], by decide +kernel⟩
private def b67 : PaidBatch .empty 9 := ⟨[
  .point 124 43 46,
  .point 124 44 47,
  .point 124 45 48], by decide +kernel⟩
private def b68 : PaidBatch .empty 9 := ⟨[
  .shared 124 46 39 ⟨.tilted, 0, 1, false, 157157189180098062⟩,
  .shared 124 47 40 ⟨.tilted, 0, 1, false, 163978169385960541⟩,
  .shared 124 48 36 ⟨.tilted, 0, 2, true, 177841533934507838⟩], by decide +kernel⟩
private def b69 : PaidBatch .empty 9 := ⟨[
  .shared 124 49 37 ⟨.tilted, 1, 2, true, 185555922406038410⟩,
  .shared 124 50 39 ⟨.tilted, 1, 2, true, 193410608091457911⟩,
  .shared 124 51 39 ⟨.tilted, 1, 2, false, 192414461662206327⟩], by decide +kernel⟩
private def b70 : PaidBatch .empty 9 := ⟨[
  .shared 124 52 40 ⟨.tilted, 1, 2, false, 199804414142189286⟩,
  .shared 124 53 42 ⟨.tilted, 1, 2, false, 207303833005629868⟩,
  .rectangle 125 42 125 42 48], by decide +kernel⟩
private def b71 : PaidBatch .empty 9 := ⟨[
  .point 125 43 46,
  .point 125 44 47,
  .point 125 45 48], by decide +kernel⟩
private def b72 : PaidBatch .empty 9 := ⟨[
  .shared 125 46 39 ⟨.tilted, 0, 1, false, 158344096459727271⟩,
  .shared 125 47 40 ⟨.tilted, 0, 1, false, 165216105173074561⟩,
  .shared 125 48 36 ⟨.tilted, 0, 2, true, 179197734707020694⟩], by decide +kernel⟩
private def b73 : PaidBatch .empty 9 := ⟨[
  .shared 125 49 38 ⟨.tilted, 0, 2, true, 186971754394721526⟩,
  .shared 125 50 39 ⟨.tilted, 1, 2, true, 194887353687827279⟩,
  .shared 125 51 39 ⟨.tilted, 1, 2, false, 193866129415629531⟩], by decide +kernel⟩
private def b74 : PaidBatch .empty 9 := ⟨[
  .shared 125 52 41 ⟨.tilted, 1, 2, false, 201311919371282271⟩,
  .shared 125 53 42 ⟨.tilted, 1, 2, false, 208868137504029628⟩,
  .point 126 42 45], by decide +kernel⟩
private def b75 : PaidBatch .empty 9 := ⟨[
  .point 126 43 47,
  .point 126 44 48,
  .shared 126 45 38 ⟨.tilted, 0, 1, false, 152728012631988936⟩], by decide +kernel⟩
private def b76 : PaidBatch .empty 9 := ⟨[
  .shared 126 46 40 ⟨.tilted, 0, 1, false, 159531003739356480⟩,
  .shared 126 47 41 ⟨.tilted, 0, 1, false, 166454040960188581⟩,
  .shared 126 48 37 ⟨.tilted, 0, 2, true, 180553935479533550⟩], by decide +kernel⟩
private def b77 : PaidBatch .empty 9 := ⟨[
  .shared 126 49 38 ⟨.tilted, 0, 2, true, 188387586383404642⟩,
  .shared 126 50 38 ⟨.tilted, 1, 2, false, 188636273508904039⟩,
  .shared 126 51 40 ⟨.tilted, 1, 2, false, 195317797169052735⟩], by decide +kernel⟩
private def b78 : PaidBatch .empty 9 := ⟨[
  .shared 126 52 41 ⟨.tilted, 1, 2, false, 202819424600375256⟩,
  .shared 126 53 43 ⟨.tilted, 1, 2, false, 210432442002429388⟩,
  .point 127 42 46], by decide +kernel⟩
private def b79 : PaidBatch .empty 9 := ⟨[
  .point 127 43 47,
  .point 127 44 48,
  .shared 127 45 39 ⟨.tilted, 0, 1, false, 153864853197770328⟩], by decide +kernel⟩
private def b80 : PaidBatch .empty 9 := ⟨[
  .shared 127 46 40 ⟨.tilted, 0, 1, false, 160717911018985689⟩,
  .shared 127 47 41 ⟨.tilted, 0, 1, false, 167691976747302601⟩,
  .shared 127 48 37 ⟨.tilted, 0, 2, true, 181910136252046406⟩], by decide +kernel⟩
private def b81 : PaidBatch .empty 9 := ⟨[
  .shared 127 49 39 ⟨.tilted, 0, 2, true, 189803418372087758⟩,
  .shared 127 50 39 ⟨.tilted, 1, 2, false, 189325794470307733⟩,
  .shared 127 51 40 ⟨.tilted, 1, 2, false, 196769464922475939⟩], by decide +kernel⟩
private def b82 : PaidBatch .empty 9 := ⟨[
  .shared 127 52 42 ⟨.tilted, 1, 2, false, 204326929829468241⟩,
  .shared 127 53 44 ⟨.tilted, 1, 2, false, 211996746500829148⟩,
  .rectangle 127 41 128 41 48], by decide +kernel⟩
private def b83 : PaidBatch .empty 9 := ⟨[
  .point 128 42 46,
  .point 128 43 47,
  .point 128 44 48], by decide +kernel⟩
private def b84 : PaidBatch .empty 9 := ⟨[
  .shared 128 45 39 ⟨.tilted, 0, 1, false, 155001693763551720⟩,
  .shared 128 46 40 ⟨.tilted, 0, 1, false, 161904818298614898⟩,
  .shared 128 47 42 ⟨.tilted, 0, 1, false, 168929912534416621⟩], by decide +kernel⟩
private def b85 : PaidBatch .empty 9 := ⟨[
  .shared 128 48 38 ⟨.tilted, 0, 2, true, 183266337024559262⟩,
  .shared 128 49 40 ⟨.tilted, 0, 2, true, 191219250360770874⟩,
  .shared 128 50 39 ⟨.tilted, 0, 2, false, 190722586541698150⟩], by decide +kernel⟩
private def b86 : PaidBatch .empty 9 := ⟨[
  .shared 128 51 41 ⟨.tilted, 1, 2, false, 198221132675899143⟩,
  .shared 128 52 43 ⟨.tilted, 1, 2, false, 205834435058561226⟩,
  .shared 128 53 44 ⟨.tilted, 1, 2, false, 213561050999228908⟩], by decide +kernel⟩
private def b87 : PaidBatch .empty 9 := ⟨[
  .point 129 41 45,
  .point 129 42 46,
  .point 129 43 48], by decide +kernel⟩
private def b88 : PaidBatch .empty 9 := ⟨[
  .shared 129 44 38 ⟨.tilted, 0, 1, false, 149309717265253147⟩,
  .shared 129 45 40 ⟨.tilted, 0, 1, false, 156138534329333112⟩,
  .shared 129 46 41 ⟨.tilted, 0, 1, false, 163091725578244107⟩], by decide +kernel⟩
private def b89 : PaidBatch .empty 9 := ⟨[
  .shared 129 47 42 ⟨.tilted, 0, 1, false, 170167848321530641⟩,
  .shared 129 48 38 ⟨.tilted, 0, 2, true, 184622537797072118⟩,
  .shared 129 49 40 ⟨.tilted, 0, 2, true, 192635082349453990⟩], by decide +kernel⟩
private def b90 : PaidBatch .empty 9 := ⟨[
  .shared 129 50 40 ⟨.tilted, 0, 2, false, 192119378613088567⟩,
  .shared 129 51 42 ⟨.tilted, 1, 2, false, 199672800429322347⟩,
  .shared 129 52 43 ⟨.tilted, 1, 2, false, 207341940287654211⟩], by decide +kernel⟩
private def b91 : PaidBatch .empty 9 := ⟨[
  .shared 129 53 45 ⟨.tilted, 1, 2, false, 215125355497628668⟩], by decide +kernel⟩
private def batches : List (PaidBatch .empty 9) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82, b83, b84, b85, b86, b87, b88, b89, b90, b91]
private abbrev tiles := tilesOf batches
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
def receipt : Certificate .empty 9 := ⟨batches, checks_join i27 (checks_join i29 (checks_join i31 (checks_join i33 (checks_join i35 (checks_join i37 (checks_join i39 (checks_join i41 (checks_join i43 (checks_join i45 (checks_join i47 (checks_join i49 (checks_join i51 i53))))))))))))⟩
end Top9


end Low53At2389PriceTableEmpty9
