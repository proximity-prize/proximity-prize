import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty12
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top12
private def b0 : PaidBatch .empty 12 := ⟨[
  .rectangle 12 36 70 44 36,
  .rectangle 15 45 70 53 43,
  .rectangle 71 45 85 49 43], by decide +kernel⟩
private def b1 : PaidBatch .empty 12 := ⟨[
  .rectangle 71 50 85 53 46,
  .rectangle 71 36 100 40 41,
  .rectangle 71 41 100 44 44], by decide +kernel⟩
private def b2 : PaidBatch .empty 12 := ⟨[
  .rectangle 86 50 93 51 46,
  .rectangle 86 52 93 53 48,
  .rectangle 86 45 100 47 46], by decide +kernel⟩
private def b3 : PaidBatch .empty 12 := ⟨[
  .rectangle 86 48 100 49 47,
  .rectangle 94 53 95 53 48,
  .rectangle 94 52 97 52 48], by decide +kernel⟩
private def b4 : PaidBatch .empty 12 := ⟨[
  .rectangle 94 50 100 50 47,
  .rectangle 94 51 100 51 48,
  .rectangle 96 53 96 53 48], by decide +kernel⟩
private def b5 : PaidBatch .empty 12 := ⟨[
  .point 97 53 46,
  .rectangle 98 52 98 52 48,
  .point 98 53 46], by decide +kernel⟩
private def b6 : PaidBatch .empty 12 := ⟨[
  .point 99 52 46,
  .point 99 53 47,
  .point 100 52 46], by decide +kernel⟩
private def b7 : PaidBatch .empty 12 := ⟨[
  .point 100 53 47,
  .point 101 51 46,
  .point 101 52 47], by decide +kernel⟩
private def b8 : PaidBatch .empty 12 := ⟨[
  .point 101 53 48,
  .rectangle 101 50 102 50 48,
  .rectangle 101 49 104 49 48], by decide +kernel⟩
private def b9 : PaidBatch .empty 12 := ⟨[
  .rectangle 101 43 108 44 45,
  .rectangle 101 45 108 46 47,
  .rectangle 101 47 108 47 47], by decide +kernel⟩
private def b10 : PaidBatch .empty 12 := ⟨[
  .rectangle 101 48 108 48 48,
  .rectangle 101 36 115 38 42,
  .rectangle 101 39 115 40 43], by decide +kernel⟩
private def b11 : PaidBatch .empty 12 := ⟨[
  .rectangle 101 41 115 42 46,
  .point 102 51 46,
  .point 102 52 47], by decide +kernel⟩
private def b12 : PaidBatch .empty 12 := ⟨[
  .point 102 53 48,
  .rectangle 103 50 103 50 48,
  .point 103 51 47], by decide +kernel⟩
private def b13 : PaidBatch .empty 12 := ⟨[
  .point 103 52 48,
  .shared 103 53 31 ⟨.tilted, 1, 2, false, 184875538735173874⟩,
  .point 104 50 46], by decide +kernel⟩
private def b14 : PaidBatch .empty 12 := ⟨[
  .point 104 51 47,
  .point 104 52 48,
  .point 104 53 49], by decide +kernel⟩
private def b15 : PaidBatch .empty 12 := ⟨[
  .rectangle 105 49 105 49 48,
  .point 105 50 46,
  .point 105 51 47], by decide +kernel⟩
private def b16 : PaidBatch .empty 12 := ⟨[
  .point 105 52 48,
  .point 105 53 49,
  .point 106 49 46], by decide +kernel⟩
private def b17 : PaidBatch .empty 12 := ⟨[
  .point 106 50 47,
  .point 106 51 48,
  .shared 106 52 31 ⟨.tilted, 1, 2, false, 182547365663441292⟩], by decide +kernel⟩
private def b18 : PaidBatch .empty 12 := ⟨[
  .shared 106 53 33 ⟨.tilted, 1, 2, false, 189748788508482601⟩,
  .point 107 49 46,
  .point 107 50 47], by decide +kernel⟩
private def b19 : PaidBatch .empty 12 := ⟨[
  .point 107 51 48,
  .shared 107 52 32 ⟨.tilted, 1, 2, false, 184112097604326444⟩,
  .shared 107 53 33 ⟨.tilted, 1, 2, false, 191373205099585510⟩], by decide +kernel⟩
private def b20 : PaidBatch .empty 12 := ⟨[
  .point 108 49 47,
  .point 108 50 48,
  .shared 108 51 32 ⟨.tilted, 1, 2, true, 181386763585800590⟩], by decide +kernel⟩
private def b21 : PaidBatch .empty 12 := ⟨[
  .shared 108 52 33 ⟨.tilted, 1, 2, false, 185676829545211596⟩,
  .shared 108 53 34 ⟨.tilted, 1, 2, false, 192997621690688419⟩,
  .point 109 48 46], by decide +kernel⟩
private def b22 : PaidBatch .empty 12 := ⟨[
  .point 109 49 47,
  .point 109 50 48,
  .shared 109 51 32 ⟨.tilted, 1, 2, false, 179978245422955743⟩], by decide +kernel⟩
private def b23 : PaidBatch .empty 12 := ⟨[
  .shared 109 52 33 ⟨.tilted, 1, 2, false, 187241561486096748⟩,
  .shared 109 53 34 ⟨.tilted, 1, 2, false, 194622038281791328⟩,
  .rectangle 109 47 110 47 48], by decide +kernel⟩
private def b24 : PaidBatch .empty 12 := ⟨[
  .rectangle 109 46 112 46 48,
  .rectangle 109 43 115 44 48,
  .rectangle 109 45 115 45 48], by decide +kernel⟩
private def b25 : PaidBatch .empty 12 := ⟨[
  .point 110 48 46,
  .point 110 49 47,
  .point 110 50 48], by decide +kernel⟩
private def b26 : PaidBatch .empty 12 := ⟨[
  .shared 110 51 32 ⟨.tilted, 1, 2, false, 181484254507260132⟩,
  .shared 110 52 34 ⟨.tilted, 1, 2, false, 188806293426981900⟩,
  .shared 110 53 35 ⟨.tilted, 1, 2, false, 196246454872894237⟩], by decide +kernel⟩
private def b27 : PaidBatch .empty 12 := ⟨[
  .point 111 47 46,
  .point 111 48 47,
  .point 111 49 48], by decide +kernel⟩
private def b28 : PaidBatch .empty 12 := ⟨[
  .shared 111 50 33 ⟨.tilted, 1, 2, true, 185791278483795772⟩,
  .shared 111 51 33 ⟨.tilted, 1, 2, false, 182990263591564521⟩,
  .shared 111 52 34 ⟨.tilted, 1, 2, false, 190371025367867052⟩], by decide +kernel⟩
private def b29 : PaidBatch .empty 12 := ⟨[
  .shared 111 53 36 ⟨.tilted, 1, 2, false, 197870871463997146⟩,
  .point 112 47 46,
  .point 112 48 47], by decide +kernel⟩
private def b30 : PaidBatch .empty 12 := ⟨[
  .point 112 49 48,
  .shared 112 50 33 ⟨.tilted, 1, 2, true, 179828551322719228⟩,
  .shared 112 51 33 ⟨.tilted, 1, 2, false, 184496272675868910⟩], by decide +kernel⟩
private def b31 : PaidBatch .empty 12 := ⟨[
  .shared 112 52 35 ⟨.tilted, 1, 2, false, 191935757308752204⟩,
  .shared 112 53 36 ⟨.tilted, 1, 2, false, 199495288055100055⟩,
  .rectangle 113 46 113 46 48], by decide +kernel⟩
private def b32 : PaidBatch .empty 12 := ⟨[
  .point 113 47 46,
  .point 113 48 47,
  .shared 113 49 38 ⟨.tilted, 1, 1, false, 171374661264371802⟩], by decide +kernel⟩
private def b33 : PaidBatch .empty 12 := ⟨[
  .shared 113 50 33 ⟨.tilted, 1, 2, false, 178626524868266284⟩,
  .shared 113 51 34 ⟨.tilted, 1, 2, false, 186002281760173299⟩,
  .shared 113 52 35 ⟨.tilted, 1, 2, false, 193500489249637356⟩], by decide +kernel⟩
private def b34 : PaidBatch .empty 12 := ⟨[
  .shared 113 53 37 ⟨.tilted, 1, 2, false, 201119704646202964⟩,
  .point 114 46 46,
  .point 114 47 47], by decide +kernel⟩
private def b35 : PaidBatch .empty 12 := ⟨[
  .point 114 48 48,
  .shared 114 49 39 ⟨.tilted, 1, 1, false, 172766110016425647⟩,
  .shared 114 50 33 ⟨.tilted, 1, 2, false, 180074772889626904⟩], by decide +kernel⟩
private def b36 : PaidBatch .empty 12 := ⟨[
  .shared 114 51 35 ⟨.tilted, 1, 2, false, 187508290844477688⟩,
  .shared 114 52 36 ⟨.tilted, 1, 2, false, 195065221190522508⟩,
  .shared 114 53 37 ⟨.tilted, 1, 2, false, 202744121237305873⟩], by decide +kernel⟩
private def b37 : PaidBatch .empty 12 := ⟨[
  .point 115 46 46,
  .point 115 47 47,
  .point 115 48 48], by decide +kernel⟩
private def b38 : PaidBatch .empty 12 := ⟨[
  .shared 115 49 39 ⟨.tilted, 1, 1, false, 174157558768479492⟩,
  .shared 115 50 34 ⟨.tilted, 1, 2, false, 181523020910987524⟩,
  .shared 115 51 35 ⟨.tilted, 1, 2, false, 189014299928782077⟩], by decide +kernel⟩
private def b39 : PaidBatch .empty 12 := ⟨[
  .shared 115 52 37 ⟨.tilted, 1, 2, false, 196629953131407660⟩,
  .shared 115 53 38 ⟨.tilted, 1, 2, false, 204368537828408782⟩,
  .rectangle 116 45 116 45 48], by decide +kernel⟩
private def b40 : PaidBatch .empty 12 := ⟨[
  .point 116 46 46,
  .point 116 47 47,
  .shared 116 48 38 ⟨.tilted, 1, 1, false, 168254967468097536⟩], by decide +kernel⟩
private def b41 : PaidBatch .empty 12 := ⟨[
  .shared 116 49 35 ⟨.tilted, 1, 2, true, 185892731582230328⟩,
  .shared 116 50 34 ⟨.tilted, 1, 2, false, 182971268932348144⟩,
  .shared 116 51 36 ⟨.tilted, 1, 2, false, 190520309013086466⟩], by decide +kernel⟩
private def b42 : PaidBatch .empty 12 := ⟨[
  .shared 116 52 37 ⟨.tilted, 1, 2, false, 198194685072292812⟩,
  .shared 116 53 39 ⟨.tilted, 1, 2, false, 205992954419511691⟩,
  .rectangle 116 44 119 44 48], by decide +kernel⟩
private def b43 : PaidBatch .empty 12 := ⟨[
  .rectangle 116 41 122 41 46,
  .rectangle 116 42 122 42 47,
  .rectangle 116 43 122 43 48], by decide +kernel⟩
private def b44 : PaidBatch .empty 12 := ⟨[
  .rectangle 116 36 129 38 47,
  .rectangle 116 39 129 39 46,
  .rectangle 116 40 129 40 47], by decide +kernel⟩
private def b45 : PaidBatch .empty 12 := ⟨[
  .point 117 45 46,
  .point 117 46 47,
  .point 117 47 48], by decide +kernel⟩
private def b46 : PaidBatch .empty 12 := ⟨[
  .shared 117 48 39 ⟨.tilted, 1, 1, false, 169590578744481600⟩,
  .shared 117 49 33 ⟨.tilted, 1, 2, false, 176940456272587182⟩,
  .shared 117 50 35 ⟨.tilted, 1, 2, false, 184419516953708764⟩], by decide +kernel⟩
private def b47 : PaidBatch .empty 12 := ⟨[
  .shared 117 51 36 ⟨.tilted, 1, 2, false, 192026318097390855⟩,
  .shared 117 52 38 ⟨.tilted, 1, 2, false, 199759417013177964⟩,
  .shared 117 53 39 ⟨.tilted, 1, 2, false, 207617371010614600⟩], by decide +kernel⟩
private def b48 : PaidBatch .empty 12 := ⟨[
  .point 118 45 46,
  .point 118 46 47,
  .point 118 47 48], by decide +kernel⟩
private def b49 : PaidBatch .empty 12 := ⟨[
  .shared 118 48 39 ⟨.tilted, 1, 1, false, 170926190020865664⟩,
  .shared 118 49 34 ⟨.tilted, 1, 2, false, 178331905024641027⟩,
  .shared 118 50 35 ⟨.tilted, 1, 2, false, 185867764975069384⟩], by decide +kernel⟩
private def b50 : PaidBatch .empty 12 := ⟨[
  .shared 118 51 37 ⟨.tilted, 1, 2, false, 193532327181695244⟩,
  .shared 118 52 38 ⟨.tilted, 1, 2, false, 201324148954063116⟩,
  .shared 118 53 40 ⟨.tilted, 1, 2, false, 209241787601717509⟩], by decide +kernel⟩
private def b51 : PaidBatch .empty 12 := ⟨[
  .point 119 45 46,
  .point 119 46 47,
  .shared 119 47 38 ⟨.tilted, 2, 1, false, 164932798248550063⟩], by decide +kernel⟩
private def b52 : PaidBatch .empty 12 := ⟨[
  .shared 119 48 40 ⟨.tilted, 1, 1, false, 172261801297249728⟩,
  .shared 119 49 34 ⟨.tilted, 1, 2, false, 179723353776694872⟩,
  .shared 119 50 36 ⟨.tilted, 1, 2, false, 187316012996430004⟩], by decide +kernel⟩
private def b53 : PaidBatch .empty 12 := ⟨[
  .shared 119 51 37 ⟨.tilted, 1, 2, false, 195038336265999633⟩,
  .shared 119 52 39 ⟨.tilted, 1, 2, false, 202888880894948268⟩,
  .shared 119 53 41 ⟨.tilted, 1, 2, false, 210866204192820418⟩], by decide +kernel⟩
private def b54 : PaidBatch .empty 12 := ⟨[
  .point 120 44 45,
  .point 120 45 47,
  .point 120 46 48], by decide +kernel⟩
private def b55 : PaidBatch .empty 12 := ⟨[
  .shared 120 47 39 ⟨.tilted, 2, 1, false, 166213533842901340⟩,
  .shared 120 48 40 ⟨.tilted, 1, 1, false, 173597412573633792⟩,
  .shared 120 49 35 ⟨.tilted, 1, 2, false, 181114802528748717⟩], by decide +kernel⟩
private def b56 : PaidBatch .empty 12 := ⟨[
  .shared 120 50 36 ⟨.tilted, 1, 2, false, 188764261017790624⟩,
  .shared 120 51 38 ⟨.tilted, 1, 2, false, 196544345350304022⟩,
  .shared 120 52 40 ⟨.tilted, 1, 2, false, 204453612835833420⟩], by decide +kernel⟩
private def b57 : PaidBatch .empty 12 := ⟨[
  .shared 120 53 41 ⟨.tilted, 1, 2, false, 212490620783923327⟩,
  .point 121 44 46,
  .point 121 45 47], by decide +kernel⟩
private def b58 : PaidBatch .empty 12 := ⟨[
  .point 121 46 48,
  .shared 121 47 39 ⟨.tilted, 2, 1, false, 167494269437252617⟩,
  .shared 121 48 41 ⟨.tilted, 1, 1, false, 174933023850017856⟩], by decide +kernel⟩
private def b59 : PaidBatch .empty 12 := ⟨[
  .shared 121 49 35 ⟨.tilted, 1, 2, false, 182506251280802562⟩,
  .shared 121 50 37 ⟨.tilted, 1, 2, false, 190212509039151244⟩,
  .shared 121 51 39 ⟨.tilted, 1, 2, false, 198050354434608411⟩], by decide +kernel⟩
private def b60 : PaidBatch .empty 12 := ⟨[
  .shared 121 52 40 ⟨.tilted, 1, 2, false, 206018344776718572⟩,
  .shared 121 53 42 ⟨.tilted, 1, 2, false, 214115037375026236⟩,
  .point 122 44 46], by decide +kernel⟩
private def b61 : PaidBatch .empty 12 := ⟨[
  .point 122 45 47,
  .shared 122 46 38 ⟨.tilted, 0, 1, false, 161418252438917820⟩,
  .shared 122 47 40 ⟨.tilted, 0, 1, false, 168775005031603894⟩], by decide +kernel⟩
private def b62 : PaidBatch .empty 12 := ⟨[
  .shared 122 48 41 ⟨.tilted, 0, 1, false, 176268635126401920⟩,
  .shared 122 49 36 ⟨.tilted, 1, 2, false, 183897700032856407⟩,
  .shared 122 50 38 ⟨.tilted, 1, 2, false, 191660757060511864⟩], by decide +kernel⟩
private def b63 : PaidBatch .empty 12 := ⟨[
  .shared 122 51 39 ⟨.tilted, 1, 2, false, 199556363518912800⟩,
  .shared 122 52 41 ⟨.tilted, 1, 2, false, 207583076717603724⟩,
  .shared 122 53 43 ⟨.tilted, 1, 2, false, 215739453966129145⟩], by decide +kernel⟩
private def b64 : PaidBatch .empty 12 := ⟨[
  .point 123 43 45,
  .point 123 44 47,
  .point 123 45 48], by decide +kernel⟩
private def b65 : PaidBatch .empty 12 := ⟨[
  .shared 123 46 39 ⟨.tilted, 0, 1, false, 162645074144873304⟩,
  .shared 123 47 40 ⟨.tilted, 0, 1, false, 170055740625955171⟩,
  .shared 123 48 35 ⟨.tilted, 0, 2, false, 177604246402785984⟩], by decide +kernel⟩
private def b66 : PaidBatch .empty 12 := ⟨[
  .shared 123 49 37 ⟨.tilted, 1, 2, false, 185289148784910252⟩,
  .shared 123 50 38 ⟨.tilted, 1, 2, false, 193109005081872484⟩,
  .shared 123 51 40 ⟨.tilted, 1, 2, false, 201062372603217189⟩], by decide +kernel⟩
private def b67 : PaidBatch .empty 12 := ⟨[
  .shared 123 52 42 ⟨.tilted, 1, 2, false, 209147808658488876⟩,
  .shared 123 53 43 ⟨.tilted, 1, 2, false, 217363870557232054⟩,
  .rectangle 123 42 126 42 48], by decide +kernel⟩
private def b68 : PaidBatch .empty 12 := ⟨[
  .rectangle 123 41 129 41 48,
  .point 124 43 46,
  .point 124 44 47], by decide +kernel⟩
private def b69 : PaidBatch .empty 12 := ⟨[
  .point 124 45 48,
  .shared 124 46 39 ⟨.tilted, 0, 1, false, 163871895850828788⟩,
  .shared 124 47 41 ⟨.tilted, 0, 1, false, 171336476220306448⟩], by decide +kernel⟩
private def b70 : PaidBatch .empty 12 := ⟨[
  .shared 124 48 36 ⟨.tilted, 0, 2, false, 178939857679170048⟩,
  .shared 124 49 37 ⟨.tilted, 1, 2, false, 186680597536964097⟩,
  .shared 124 50 39 ⟨.tilted, 1, 2, false, 194557253103233104⟩], by decide +kernel⟩
private def b71 : PaidBatch .empty 12 := ⟨[
  .shared 124 51 40 ⟨.tilted, 1, 2, false, 202568381687521578⟩,
  .shared 124 52 42 ⟨.tilted, 1, 2, false, 210712540599374028⟩,
  .shared 124 53 44 ⟨.tilted, 1, 2, false, 218988287148334963⟩], by decide +kernel⟩
private def b72 : PaidBatch .empty 12 := ⟨[
  .point 125 43 46,
  .point 125 44 47,
  .point 125 45 48], by decide +kernel⟩
private def b73 : PaidBatch .empty 12 := ⟨[
  .shared 125 46 40 ⟨.tilted, 0, 1, false, 165098717556784272⟩,
  .shared 125 47 41 ⟨.tilted, 0, 1, false, 172617211814657725⟩,
  .shared 125 48 36 ⟨.tilted, 0, 2, false, 180275468955554112⟩], by decide +kernel⟩
private def b74 : PaidBatch .empty 12 := ⟨[
  .shared 125 49 38 ⟨.tilted, 0, 2, false, 188072046289017942⟩,
  .shared 125 50 39 ⟨.tilted, 1, 2, false, 196005501124593724⟩,
  .shared 125 51 41 ⟨.tilted, 1, 2, false, 204074390771825967⟩], by decide +kernel⟩
private def b75 : PaidBatch .empty 12 := ⟨[
  .shared 125 52 43 ⟨.tilted, 1, 2, false, 212277272540259180⟩,
  .shared 125 53 45 ⟨.tilted, 1, 2, false, 220612703739437872⟩,
  .point 126 43 46], by decide +kernel⟩
private def b76 : PaidBatch .empty 12 := ⟨[
  .point 126 44 48,
  .shared 126 45 39 ⟨.tilted, 0, 1, false, 158895298483585929⟩,
  .shared 126 46 40 ⟨.tilted, 0, 1, false, 166325539262739756⟩], by decide +kernel⟩
private def b77 : PaidBatch .empty 12 := ⟨[
  .shared 126 47 42 ⟨.tilted, 0, 1, false, 173897947409009002⟩,
  .shared 126 48 37 ⟨.tilted, 0, 2, false, 181611080231938176⟩,
  .shared 126 49 38 ⟨.tilted, 0, 2, false, 189463495041071787⟩], by decide +kernel⟩
private def b78 : PaidBatch .empty 12 := ⟨[
  .shared 126 50 40 ⟨.tilted, 1, 2, false, 197453749145954344⟩,
  .shared 126 51 42 ⟨.tilted, 1, 2, false, 205580399856130356⟩,
  .shared 126 52 44 ⟨.tilted, 1, 2, false, 213842004481144332⟩], by decide +kernel⟩
private def b79 : PaidBatch .empty 12 := ⟨[
  .shared 126 53 46 ⟨.tilted, 1, 2, false, 222237120330540781⟩,
  .point 127 42 45,
  .point 127 43 47], by decide +kernel⟩
private def b80 : PaidBatch .empty 12 := ⟨[
  .point 127 44 48,
  .shared 127 45 39 ⟨.tilted, 0, 1, false, 160069168094782614⟩,
  .shared 127 46 41 ⟨.tilted, 0, 1, false, 167552360968695240⟩], by decide +kernel⟩
private def b81 : PaidBatch .empty 12 := ⟨[
  .shared 127 47 42 ⟨.tilted, 0, 1, false, 175178683003360279⟩,
  .shared 127 48 37 ⟨.tilted, 0, 2, false, 182946691508322240⟩,
  .shared 127 49 39 ⟨.tilted, 0, 2, false, 190854943793125632⟩], by decide +kernel⟩
private def b82 : PaidBatch .empty 12 := ⟨[
  .shared 127 50 41 ⟨.tilted, 1, 2, false, 198901997167314964⟩,
  .shared 127 51 42 ⟨.tilted, 1, 2, false, 207086408940434745⟩,
  .shared 127 52 44 ⟨.tilted, 1, 2, false, 215406736422029484⟩], by decide +kernel⟩
private def b83 : PaidBatch .empty 12 := ⟨[
  .shared 127 53 46 ⟨.tilted, 1, 2, false, 223861536921643690⟩,
  .point 128 42 46,
  .point 128 43 47], by decide +kernel⟩
private def b84 : PaidBatch .empty 12 := ⟨[
  .point 128 44 48,
  .shared 128 45 40 ⟨.tilted, 0, 1, false, 161243037705979299⟩,
  .shared 128 46 41 ⟨.tilted, 0, 1, false, 168779182674650724⟩], by decide +kernel⟩
private def b85 : PaidBatch .empty 12 := ⟨[
  .shared 128 47 43 ⟨.tilted, 0, 1, false, 176459418597711556⟩,
  .shared 128 48 38 ⟨.tilted, 0, 2, false, 184282302784706304⟩,
  .shared 128 49 39 ⟨.tilted, 0, 2, false, 192246392545179477⟩], by decide +kernel⟩
private def b86 : PaidBatch .empty 12 := ⟨[
  .shared 128 50 41 ⟨.tilted, 0, 2, false, 200350245188675584⟩,
  .shared 128 51 43 ⟨.tilted, 1, 2, false, 208592418024739134⟩,
  .shared 128 52 45 ⟨.tilted, 1, 2, false, 216971468362914636⟩], by decide +kernel⟩
private def b87 : PaidBatch .empty 12 := ⟨[
  .shared 128 53 47 ⟨.tilted, 1, 2, false, 225485953512746599⟩,
  .point 129 42 46,
  .point 129 43 47], by decide +kernel⟩
private def b88 : PaidBatch .empty 12 := ⟨[
  .shared 129 44 39 ⟨.tilted, 0, 1, false, 154974305692227652⟩,
  .shared 129 45 40 ⟨.tilted, 0, 1, false, 162416907317175984⟩,
  .shared 129 46 42 ⟨.tilted, 0, 1, false, 170006004380606208⟩], by decide +kernel⟩
private def b89 : PaidBatch .empty 12 := ⟨[
  .shared 129 47 43 ⟨.tilted, 0, 1, false, 177740154192062833⟩,
  .shared 129 48 38 ⟨.tilted, 0, 2, false, 185617914061090368⟩,
  .shared 129 49 40 ⟨.tilted, 0, 2, false, 193637841297233322⟩], by decide +kernel⟩
private def b90 : PaidBatch .empty 12 := ⟨[
  .shared 129 50 42 ⟨.tilted, 0, 2, false, 201798493210036204⟩,
  .shared 129 51 44 ⟨.tilted, 1, 2, false, 210098427109043523⟩,
  .shared 129 52 46 ⟨.tilted, 1, 2, false, 218536200303799788⟩], by decide +kernel⟩
private def b91 : PaidBatch .empty 12 := ⟨[
  .shared 129 53 48 ⟨.tilted, 1, 2, false, 227110370103849508⟩], by decide +kernel⟩
private def batches : List (PaidBatch .empty 12) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82, b83, b84, b85, b86, b87, b88, b89, b90, b91]
private abbrev tiles := tilesOf batches
private theorem i36 : checks tiles 129 36 2 = true := by decide +kernel
private theorem i38 : checks tiles 129 38 2 = true := by decide +kernel
private theorem i40 : checks tiles 129 40 2 = true := by decide +kernel
private theorem i42 : checks tiles 129 42 2 = true := by decide +kernel
private theorem i44 : checks tiles 129 44 2 = true := by decide +kernel
private theorem i46 : checks tiles 129 46 2 = true := by decide +kernel
private theorem i48 : checks tiles 129 48 2 = true := by decide +kernel
private theorem i50 : checks tiles 129 50 2 = true := by decide +kernel
private theorem i52 : checks tiles 129 52 2 = true := by decide +kernel
def receipt : Certificate .empty 12 := ⟨batches, checks_join i36 (checks_join i38 (checks_join i40 (checks_join i42 (checks_join i44 (checks_join i46 (checks_join i48 (checks_join i50 i52)))))))⟩
end Top12


end Low53At2389PriceTableEmpty12
