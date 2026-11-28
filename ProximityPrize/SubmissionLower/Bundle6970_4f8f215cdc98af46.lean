import ProximityPrize.SubmissionLower.Bundle6970_b40f827c7a689676

section Pack_Z6970PlateauChunkedBatch180

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range180To182 : chunk 180 2 = 1393050097538 :=
  join_chunk (f := 180) (a := 1) (b := 1) (u := 697979259998) (v := 695070837540) oneChunk180 oneChunk181

theorem range183To185 : chunk 183 2 = 1375631704610 :=
  join_chunk (f := 183) (a := 1) (b := 1) (u := 689264710234) (v := 686366994376) oneChunk183 oneChunk184

theorem range182To185 : chunk 182 3 = 2067796842060 :=
  join_chunk (f := 182) (a := 1) (b := 2) (u := 692165137450) (v := 1375631704610) oneChunk182 range183To185

theorem range180To185 : chunk 180 5 = 3460846939598 :=
  join_chunk (f := 180) (a := 2) (b := 3) (u := 1393050097538) (v := 2067796842060) range180To182 range182To185

theorem range185To187 : chunk 185 2 = 1364059337590 :=
  join_chunk (f := 185) (a := 1) (b := 1) (u := 683474543620) (v := 680584793970) oneChunk185 oneChunk186

theorem range188To190 : chunk 188 2 = 1346760456978 :=
  join_chunk (f := 188) (a := 1) (b := 1) (u := 674818502502) (v := 671941954476) oneChunk188 oneChunk189

theorem range187To190 : chunk 187 3 = 2024460759410 :=
  join_chunk (f := 187) (a := 1) (b := 2) (u := 677700302432) (v := 1346760456978) oneChunk187 range188To190

theorem range185To190 : chunk 185 5 = 3388520097000 :=
  join_chunk (f := 185) (a := 2) (b := 3) (u := 1364059337590) (v := 2024460759410) range185To187 range187To190

theorem range180To190 : chunk 180 10 = 6849367036598 :=
  join_chunk (f := 180) (a := 5) (b := 5) (u := 3460846939598) (v := 3388520097000) range180To185 range185To190

theorem range190To192 : chunk 190 2 = 1335267559956 :=
  join_chunk (f := 190) (a := 1) (b := 1) (u := 669068089318) (v := 666199470638) oneChunk190 oneChunk191

theorem range193To195 : chunk 193 2 = 1318087615450 :=
  join_chunk (f := 193) (a := 1) (b := 1) (u := 660472824878) (v := 657614790572) oneChunk193 oneChunk194

theorem range192To195 : chunk 192 3 = 1981421142292 :=
  join_chunk (f := 192) (a := 1) (b := 2) (u := 663333526842) (v := 1318087615450) oneChunk192 range193To195

theorem range190To195 : chunk 190 5 = 3316688702248 :=
  join_chunk (f := 190) (a := 2) (b := 3) (u := 1335267559956) (v := 1981421142292) range190To192 range192To195

theorem range195To197 : chunk 195 2 = 1306673853318 :=
  join_chunk (f := 195) (a := 1) (b := 1) (u := 654761994234) (v := 651911859084) oneChunk195 oneChunk196

theorem range198To200 : chunk 198 2 = 1289612415856 :=
  join_chunk (f := 198) (a := 1) (b := 1) (u := 646224714030) (v := 643387701826) oneChunk198 oneChunk199

theorem range197To200 : chunk 197 3 = 1938679374676 :=
  join_chunk (f := 197) (a := 1) (b := 2) (u := 649066958820) (v := 1289612415856) oneChunk197 range198To200

theorem range195To200 : chunk 195 5 = 3245353227994 :=
  join_chunk (f := 195) (a := 2) (b := 3) (u := 1306673853318) (v := 1938679374676) range195To197 range197To200

theorem range190To200 : chunk 190 10 = 6562041930242 :=
  join_chunk (f := 190) (a := 5) (b := 5) (u := 3316688702248) (v := 3245353227994) range190To195 range195To200

theorem range180To200 : chunk 180 20 = 13411408966840 :=
  join_chunk (f := 180) (a := 10) (b := 10) (u := 6849367036598) (v := 6562041930242) range180To190 range190To200

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch180

section Pack_Z6970PlateauChunkedBatch200

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range200To202 : chunk 200 2 = 1278277549656 :=
  join_chunk (f := 200) (a := 1) (b := 1) (u := 640553340138) (v := 637724209518) oneChunk200 oneChunk201

theorem range203To205 : chunk 203 2 = 1261334331378 :=
  join_chunk (f := 203) (a := 1) (b := 1) (u := 632076471240) (v := 629257860138) oneChunk203 oneChunk204

theorem range202To205 : chunk 202 3 = 1896232056592 :=
  join_chunk (f := 202) (a := 1) (b := 2) (u := 634897725214) (v := 1261334331378) oneChunk202 range203To205

theorem range200To205 : chunk 200 5 = 3174509606248 :=
  join_chunk (f := 200) (a := 2) (b := 3) (u := 1278277549656) (v := 1896232056592) range200To202 range202To205

theorem range205To207 : chunk 205 2 = 1250078218278 :=
  join_chunk (f := 205) (a := 1) (b := 1) (u := 626444479410) (v := 623633738868) oneChunk205 oneChunk206

theorem range208To210 : chunk 208 2 = 1233253078596 :=
  join_chunk (f := 208) (a := 1) (b := 1) (u := 618025358438) (v := 615227720158) oneChunk208 oneChunk209

theorem range207To210 : chunk 207 3 = 1854081308122 :=
  join_chunk (f := 207) (a := 1) (b := 2) (u := 620828229526) (v := 1233253078596) oneChunk207 range208To210

theorem range205To210 : chunk 205 5 = 3104159526400 :=
  join_chunk (f := 205) (a := 2) (b := 3) (u := 1250078218278) (v := 1854081308122) range205To207 range207To210

theorem range200To210 : chunk 200 10 = 6278669132648 :=
  join_chunk (f := 200) (a := 5) (b := 5) (u := 3174509606248) (v := 3104159526400) range200To205 range205To210

theorem range210To212 : chunk 210 2 = 1222075671914 :=
  join_chunk (f := 210) (a := 1) (b := 1) (u := 612432718958) (v := 609642952956) oneChunk210 oneChunk211

theorem range213To215 : chunk 213 2 = 1205368611318 :=
  join_chunk (f := 213) (a := 1) (b := 1) (u := 604073932644) (v := 601294678674) oneChunk213 oneChunk214

theorem range212To215 : chunk 212 3 = 1812224434934 :=
  join_chunk (f := 212) (a := 1) (b := 2) (u := 606855823616) (v := 1205368611318) oneChunk212 range213To215

theorem range210To215 : chunk 210 5 = 3034300106848 :=
  join_chunk (f := 210) (a := 2) (b := 3) (u := 1222075671914) (v := 1812224434934) range210To212 range212To215

theorem range215To217 : chunk 215 2 = 1194269960496 :=
  join_chunk (f := 215) (a := 1) (b := 1) (u := 598520667024) (v := 595749293472) oneChunk215 oneChunk216

theorem range218To220 : chunk 218 2 = 1177681126874 :=
  join_chunk (f := 218) (a := 1) (b := 1) (u := 590219680426) (v := 587461446448) oneChunk218 oneChunk219

theorem range217To220 : chunk 217 3 = 1770664293848 :=
  join_chunk (f := 217) (a := 1) (b := 2) (u := 592983166974) (v := 1177681126874) oneChunk217 range218To220

theorem range215To220 : chunk 215 5 = 2964934254344 :=
  join_chunk (f := 215) (a := 2) (b := 3) (u := 1194269960496) (v := 1770664293848) range215To217 range217To220

theorem range210To220 : chunk 210 10 = 5999234361192 :=
  join_chunk (f := 210) (a := 5) (b := 5) (u := 3034300106848) (v := 2964934254344) range210To215 range215To220

theorem range200To220 : chunk 200 20 = 12277903493840 :=
  join_chunk (f := 200) (a := 10) (b := 10) (u := 6278669132648) (v := 5999234361192) range200To210 range210To220

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch200

section Pack_Z6970PlateauChunkedBatch220

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range220To222 : chunk 220 2 = 1166661377504 :=
  join_chunk (f := 220) (a := 1) (b := 1) (u := 584705855028) (v := 581955522476) oneChunk220 oneChunk221

theorem range223To225 : chunk 223 2 = 1150191059696 :=
  join_chunk (f := 223) (a := 1) (b := 1) (u := 576465415166) (v := 573725644530) oneChunk223 oneChunk224

theorem range222To225 : chunk 222 3 = 1729398895544 :=
  join_chunk (f := 222) (a := 1) (b := 2) (u := 579207835848) (v := 1150191059696) oneChunk222 range223To225

theorem range220To225 : chunk 220 5 = 2896060273048 :=
  join_chunk (f := 220) (a := 2) (b := 3) (u := 1166661377504) (v := 1729398895544) range220To222 range222To225

theorem range225To227 : chunk 225 2 = 1139250453496 :=
  join_chunk (f := 225) (a := 1) (b := 1) (u := 570991147700) (v := 568259305796) oneChunk225 oneChunk226

theorem range228To230 : chunk 228 2 = 1122899087864 :=
  join_chunk (f := 228) (a := 1) (b := 1) (u := 562808847444) (v := 560090240420) oneChunk228 oneChunk229

theorem range227To230 : chunk 227 3 = 1688431834204 :=
  join_chunk (f := 227) (a := 1) (b := 2) (u := 565532746340) (v := 1122899087864) oneChunk227 range228To230

theorem range225To230 : chunk 225 5 = 2827682287700 :=
  join_chunk (f := 225) (a := 2) (b := 3) (u := 1139250453496) (v := 1688431834204) range225To227 range227To230

theorem range220To230 : chunk 220 10 = 5723742560748 :=
  join_chunk (f := 220) (a := 5) (b := 5) (u := 2896060273048) (v := 2827682287700) range220To225 range225To230

theorem range230To232 : chunk 230 2 = 1112037962702 :=
  join_chunk (f := 230) (a := 1) (b := 1) (u := 557374300348) (v := 554663662354) oneChunk230 oneChunk231

theorem range233To235 : chunk 233 2 = 1095806126436 :=
  join_chunk (f := 233) (a := 1) (b := 1) (u := 549253047630) (v := 546553078806) oneChunk233 oneChunk234

theorem range232To235 : chunk 232 3 = 1647761824896 :=
  join_chunk (f := 232) (a := 1) (b := 2) (u := 551955698460) (v := 1095806126436) oneChunk232 range233To235

theorem range230To235 : chunk 230 5 = 2759799787598 :=
  join_chunk (f := 230) (a := 2) (b := 3) (u := 1112037962702) (v := 1647761824896) range230To232 range232To235

theorem range235To237 : chunk 235 2 = 1085024916304 :=
  join_chunk (f := 235) (a := 1) (b := 1) (u := 543858434814) (v := 541166481490) oneChunk235 oneChunk236

theorem range238To240 : chunk 238 2 = 1068913334242 :=
  join_chunk (f := 238) (a := 1) (b := 1) (u := 535795949692) (v := 533117384550) oneChunk238 oneChunk239

theorem range237To240 : chunk 237 3 = 1607393199790 :=
  join_chunk (f := 237) (a := 1) (b := 2) (u := 538479865548) (v := 1068913334242) oneChunk237 range238To240

theorem range235To240 : chunk 235 5 = 2692418116094 :=
  join_chunk (f := 235) (a := 2) (b := 3) (u := 1085024916304) (v := 1607393199790) range235To237 range237To240

theorem range230To240 : chunk 230 10 = 5452217903692 :=
  join_chunk (f := 230) (a := 5) (b := 5) (u := 2759799787598) (v := 2692418116094) range230To235 range235To240

theorem range220To240 : chunk 220 20 = 11175960464440 :=
  join_chunk (f := 220) (a := 10) (b := 10) (u := 5723742560748) (v := 5452217903692) range220To230 range230To240

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch220

section Pack_Z6970PlateauChunkedBatch240

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range240To242 : chunk 240 2 = 1058212569282 :=
  join_chunk (f := 240) (a := 1) (b := 1) (u := 530441529668) (v := 527771039614) oneChunk240 oneChunk241

theorem range243To245 : chunk 243 2 = 1042222106964 :=
  join_chunk (f := 243) (a := 1) (b := 1) (u := 522440881612) (v := 519781225352) oneChunk243 oneChunk244

theorem range242To245 : chunk 242 3 = 1567325377716 :=
  join_chunk (f := 242) (a := 1) (b := 2) (u := 525103270752) (v := 1042222106964) oneChunk242 range243To245

theorem range240To245 : chunk 240 5 = 2625537946998 :=
  join_chunk (f := 240) (a := 2) (b := 3) (u := 1058212569282) (v := 1567325377716) range240To242 range242To245

theorem range245To247 : chunk 245 2 = 1031602413444 :=
  join_chunk (f := 245) (a := 1) (b := 1) (u := 517126964490) (v := 514475448954) oneChunk245 oneChunk246

theorem range248To250 : chunk 248 2 = 1015734084182 :=
  join_chunk (f := 248) (a := 1) (b := 1) (u := 509186000120) (v := 506548084062) oneChunk248 oneChunk249

theorem range247To250 : chunk 247 3 = 1527563429456 :=
  join_chunk (f := 247) (a := 1) (b := 2) (u := 511829345274) (v := 1015734084182) oneChunk247 range248To250

theorem range245To250 : chunk 245 5 = 2559165842900 :=
  join_chunk (f := 245) (a := 2) (b := 3) (u := 1031602413444) (v := 1527563429456) range245To247 range247To250

theorem range240To250 : chunk 240 10 = 5184703789898 :=
  join_chunk (f := 240) (a := 5) (b := 5) (u := 2625537946998) (v := 2559165842900) range240To245 range245To250

theorem range250To252 : chunk 250 2 = 1005196184520 :=
  join_chunk (f := 250) (a := 1) (b := 1) (u := 503912940488) (v := 501283244032) oneChunk250 oneChunk251

theorem range253To255 : chunk 253 2 = 989451142204 :=
  join_chunk (f := 253) (a := 1) (b := 1) (u := 496034891436) (v := 493416250768) oneChunk253 oneChunk254

theorem range252To255 : chunk 252 3 = 1488107476978 :=
  join_chunk (f := 252) (a := 1) (b := 2) (u := 498656334774) (v := 989451142204) oneChunk252 range253To255

theorem range250To255 : chunk 250 5 = 2493303661498 :=
  join_chunk (f := 250) (a := 2) (b := 3) (u := 1005196184520) (v := 1488107476978) range250To252 range252To255

theorem range255To257 : chunk 255 2 = 978995854942 :=
  join_chunk (f := 255) (a := 1) (b := 1) (u := 490803095604) (v := 488192759338) oneChunk255 oneChunk256

theorem range258To260 : chunk 258 2 = 963375401360 :=
  join_chunk (f := 258) (a := 1) (b := 1) (u := 482985934428) (v := 480389466932) oneChunk258 oneChunk259

theorem range257To260 : chunk 257 3 = 1448963330302 :=
  join_chunk (f := 257) (a := 1) (b := 2) (u := 485587928942) (v := 963375401360) oneChunk257 range258To260

theorem range255To260 : chunk 255 5 = 2427959185244 :=
  join_chunk (f := 255) (a := 2) (b := 3) (u := 978995854942) (v := 1448963330302) range255To257 range257To260

theorem range250To260 : chunk 250 10 = 4921262846742 :=
  join_chunk (f := 250) (a := 5) (b := 5) (u := 2493303661498) (v := 2427959185244) range250To255 range255To260

theorem range240To260 : chunk 240 20 = 10105966636640 :=
  join_chunk (f := 240) (a := 10) (b := 10) (u := 5184703789898) (v := 4921262846742) range240To250 range250To260

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch240

section Pack_Z6970PlateauChunkedBatch260

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range260To262 : chunk 260 2 = 953003641190 :=
  join_chunk (f := 260) (a := 1) (b := 1) (u := 477795853058) (v := 475207788132) oneChunk260 oneChunk261

theorem range263To265 : chunk 263 2 = 937509218582 :=
  join_chunk (f := 263) (a := 1) (b := 1) (u := 470042974178) (v := 467466244404) oneChunk263 oneChunk264

theorem range262To265 : chunk 262 3 = 1410131813908 :=
  join_chunk (f := 262) (a := 1) (b := 2) (u := 472622595326) (v := 937509218582) oneChunk262 range263To265

theorem range260To265 : chunk 260 5 = 2363135455098 :=
  join_chunk (f := 260) (a := 2) (b := 3) (u := 953003641190) (v := 1410131813908) range260To262 range262To265

theorem range265To267 : chunk 265 2 = 927221996322 :=
  join_chunk (f := 265) (a := 1) (b := 1) (u := 464895109780) (v := 462326886542) oneChunk265 oneChunk266

theorem range268To270 : chunk 268 2 = 911855194950 :=
  join_chunk (f := 268) (a := 1) (b := 1) (u := 457204611066) (v := 454650583884) oneChunk268 oneChunk269

theorem range267To270 : chunk 267 3 = 1371619477678 :=
  join_chunk (f := 267) (a := 1) (b := 2) (u := 459764282728) (v := 911855194950) oneChunk267 range268To270

theorem range265To270 : chunk 265 5 = 2298841474000 :=
  join_chunk (f := 265) (a := 2) (b := 3) (u := 927221996322) (v := 1371619477678) range265To267 range267To270

theorem range260To270 : chunk 260 10 = 4661976929098 :=
  join_chunk (f := 260) (a := 5) (b := 5) (u := 2363135455098) (v := 2298841474000) range260To265 range265To270

theorem range270To272 : chunk 270 2 = 901653617568 :=
  join_chunk (f := 270) (a := 1) (b := 1) (u := 452099510378) (v := 449554107190) oneChunk270 oneChunk271

theorem range273To275 : chunk 273 2 = 886416168022 :=
  join_chunk (f := 273) (a := 1) (b := 1) (u := 444474949662) (v := 441941218360) oneChunk273 oneChunk274

theorem range272To275 : chunk 272 3 = 1333427847980 :=
  join_chunk (f := 272) (a := 1) (b := 2) (u := 447011679958) (v := 886416168022) oneChunk272 range273To275

theorem range270To275 : chunk 270 5 = 2235081465548 :=
  join_chunk (f := 270) (a := 2) (b := 3) (u := 901653617568) (v := 1333427847980) range270To272 range272To275

theorem range275To277 : chunk 275 2 = 876301438610 :=
  join_chunk (f := 275) (a := 1) (b := 1) (u := 439413211394) (v := 436888227216) oneChunk275 oneChunk276

theorem range278To280 : chunk 278 2 = 861195219628 :=
  join_chunk (f := 278) (a := 1) (b := 1) (u := 431852811234) (v := 429342408394) oneChunk278 oneChunk279

theorem range277To280 : chunk 277 3 = 1295564215184 :=
  join_chunk (f := 277) (a := 1) (b := 2) (u := 434368995556) (v := 861195219628) oneChunk277 range278To280

theorem range275To280 : chunk 275 5 = 2171865653794 :=
  join_chunk (f := 275) (a := 2) (b := 3) (u := 876301438610) (v := 1295564215184) range275To277 range277To280

theorem range270To280 : chunk 270 10 = 4406947119342 :=
  join_chunk (f := 270) (a := 5) (b := 5) (u := 2235081465548) (v := 2171865653794) range270To275 range275To280

theorem range260To280 : chunk 260 20 = 9068924048440 :=
  join_chunk (f := 260) (a := 10) (b := 10) (u := 4661976929098) (v := 4406947119342) range260To270 range270To280

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch260

section Pack_Z6970PlateauChunkedBatch280

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range280To282 : chunk 280 2 = 851168637428 :=
  join_chunk (f := 280) (a := 1) (b := 1) (u := 426835078198) (v := 424333559230) oneChunk280 oneChunk281

theorem range283To285 : chunk 283 2 = 836195667950 :=
  join_chunk (f := 283) (a := 1) (b := 1) (u := 419342560464) (v := 416853107486) oneChunk283 oneChunk284

theorem range282To285 : chunk 282 3 = 1258030806920 :=
  join_chunk (f := 282) (a := 1) (b := 2) (u := 421835138970) (v := 836195667950) oneChunk282 range283To285

theorem range280To285 : chunk 280 5 = 2109199444348 :=
  join_chunk (f := 280) (a := 2) (b := 3) (u := 851168637428) (v := 1258030806920) range280To282 range282To285

theorem range285To287 : chunk 285 2 = 826258628330 :=
  join_chunk (f := 285) (a := 1) (b := 1) (u := 414369527570) (v := 411889100760) oneChunk285 oneChunk286

theorem range288To290 : chunk 288 2 = 811421075568 :=
  join_chunk (f := 288) (a := 1) (b := 1) (u := 406943238882) (v := 404477836686) oneChunk288 oneChunk289

theorem range287To290 : chunk 287 3 = 1220835654670 :=
  join_chunk (f := 287) (a := 1) (b := 2) (u := 409414579102) (v := 811421075568) oneChunk287 range288To290

theorem range285To290 : chunk 285 5 = 2047094283000 :=
  join_chunk (f := 285) (a := 2) (b := 3) (u := 826258628330) (v := 1220835654670) range285To287 range287To290

theorem range280To290 : chunk 280 10 = 4156293727348 :=
  join_chunk (f := 280) (a := 5) (b := 5) (u := 2109199444348) (v := 2047094283000) range280To285 range285To290

theorem range290To292 : chunk 290 2 = 801575070046 :=
  join_chunk (f := 290) (a := 1) (b := 1) (u := 402015645018) (v := 399559425028) oneChunk290 oneChunk291

theorem range293To295 : chunk 293 2 = 786875241290 :=
  join_chunk (f := 293) (a := 1) (b := 1) (u := 394659471908) (v := 392215769382) oneChunk293 oneChunk294

theorem range292To295 : chunk 292 3 = 1183981686702 :=
  join_chunk (f := 292) (a := 1) (b := 2) (u := 397106445412) (v := 786875241290) oneChunk292 range293To295

theorem range290To295 : chunk 290 5 = 1985556756748 :=
  join_chunk (f := 290) (a := 2) (b := 3) (u := 801575070046) (v := 1183981686702) range290To292 range292To295

theorem range295To297 : chunk 295 2 = 777121857508 :=
  join_chunk (f := 295) (a := 1) (b := 1) (u := 389778108184) (v := 387343749324) oneChunk295 oneChunk296

theorem range298To300 : chunk 298 2 = 762562208446 :=
  join_chunk (f := 298) (a := 1) (b := 1) (u := 382490520710) (v := 380071687736) oneChunk298 oneChunk299

theorem range297To300 : chunk 297 3 = 1147477676236 :=
  join_chunk (f := 297) (a := 1) (b := 2) (u := 384915467790) (v := 762562208446) oneChunk297 range298To300

theorem range295To300 : chunk 295 5 = 1924599533744 :=
  join_chunk (f := 295) (a := 2) (b := 3) (u := 777121857508) (v := 1147477676236) range295To297 range297To300

theorem range290To300 : chunk 290 10 = 3910156290492 :=
  join_chunk (f := 290) (a := 5) (b := 5) (u := 1985556756748) (v := 1924599533744) range290To295 range295To300

theorem range280To300 : chunk 280 20 = 8066450017840 :=
  join_chunk (f := 280) (a := 10) (b := 10) (u := 4156293727348) (v := 3910156290492) range280To290 range290To300

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch280

section Pack_Z6970PlateauChunkedBatch300

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range300To302 : chunk 300 2 = 752903130196 :=
  join_chunk (f := 300) (a := 1) (b := 1) (u := 377656222088) (v := 375246908108) oneChunk300 oneChunk301

theorem range303To305 : chunk 303 2 = 738486256468 :=
  join_chunk (f := 303) (a := 1) (b := 1) (u := 370441272070) (v := 368044984398) oneChunk303 oneChunk304

theorem range302To305 : chunk 302 3 = 1111327251552 :=
  join_chunk (f := 302) (a := 1) (b := 2) (u := 372840995084) (v := 738486256468) oneChunk302 range303To305

theorem range300To305 : chunk 300 5 = 1864230381748 :=
  join_chunk (f := 300) (a := 2) (b := 3) (u := 752903130196) (v := 1111327251552) range300To302 range302To305

theorem range305To307 : chunk 305 2 = 728923263668 :=
  join_chunk (f := 305) (a := 1) (b := 1) (u := 365654925860) (v := 363268337808) oneChunk305 oneChunk306

theorem range308To310 : chunk 308 2 = 714651909436 :=
  join_chunk (f := 308) (a := 1) (b := 1) (u := 358511206168) (v := 356140703268) oneChunk308 oneChunk309

theorem range307To310 : chunk 307 3 = 1075539928232 :=
  join_chunk (f := 307) (a := 1) (b := 2) (u := 360888018796) (v := 714651909436) oneChunk307 range308To310

theorem range305To310 : chunk 305 5 = 1804463191900 :=
  join_chunk (f := 305) (a := 2) (b := 3) (u := 728923263668) (v := 1075539928232) range305To307 range307To310

theorem range300To310 : chunk 300 10 = 3668693573648 :=
  join_chunk (f := 300) (a := 5) (b := 5) (u := 1864230381748) (v := 1804463191900) range300To305 range305To310

theorem range310To312 : chunk 310 2 = 705186878154 :=
  join_chunk (f := 310) (a := 1) (b := 1) (u := 353773743408) (v := 351413134746) oneChunk310 oneChunk311

theorem range313To315 : chunk 313 2 = 691063927408 :=
  join_chunk (f := 313) (a := 1) (b := 1) (u := 346705471774) (v := 344358455634) oneChunk313 oneChunk314

theorem range312To315 : chunk 312 3 = 1040120033944 :=
  join_chunk (f := 312) (a := 1) (b := 2) (u := 349056106536) (v := 691063927408) oneChunk312 range313To315

theorem range310To315 : chunk 310 5 = 1745306912098 :=
  join_chunk (f := 310) (a := 2) (b := 3) (u := 705186878154) (v := 1040120033944) range310To312 range312To315

theorem range315To317 : chunk 315 2 = 681698829836 :=
  join_chunk (f := 315) (a := 1) (b := 1) (u := 342017875974) (v := 339680953862) oneChunk315 oneChunk316

theorem range318To320 : chunk 318 2 = 667727315214 :=
  join_chunk (f := 318) (a := 1) (b := 1) (u := 335023767456) (v := 332703547758) oneChunk318 oneChunk319

theorem range317To320 : chunk 317 3 = 1005077827258 :=
  join_chunk (f := 317) (a := 1) (b := 2) (u := 337350512044) (v := 667727315214) oneChunk317 range318To320

theorem range315To320 : chunk 315 5 = 1686776657094 :=
  join_chunk (f := 315) (a := 2) (b := 3) (u := 681698829836) (v := 1005077827258) range315To317 range317To320

theorem range310To320 : chunk 310 10 = 3432083569192 :=
  join_chunk (f := 310) (a := 5) (b := 5) (u := 1745306912098) (v := 1686776657094) range310To315 range315To320

theorem range300To320 : chunk 300 20 = 7100777142840 :=
  join_chunk (f := 300) (a := 10) (b := 10) (u := 3668693573648) (v := 3432083569192) range300To310 range310To320

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch300

section Pack_Z6970PlateauChunkedBatch320

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range320To322 : chunk 320 2 = 658464219694 :=
  join_chunk (f := 320) (a := 1) (b := 1) (u := 330387065728) (v := 328077153966) oneChunk320 oneChunk321

theorem range323To325 : chunk 323 2 = 644647313536 :=
  join_chunk (f := 323) (a := 1) (b := 1) (u := 323471504596) (v := 321175808940) oneChunk323 oneChunk324

theorem range322To325 : chunk 322 3 = 970418334604 :=
  join_chunk (f := 322) (a := 1) (b := 2) (u := 325771021068) (v := 644647313536) oneChunk322 range323To325

theorem range320To325 : chunk 320 5 = 1628882554298 :=
  join_chunk (f := 320) (a := 2) (b := 3) (u := 658464219694) (v := 970418334604) range320To322 range322To325

theorem range325To327 : chunk 325 2 = 635488384536 :=
  join_chunk (f := 325) (a := 1) (b := 1) (u := 318886776650) (v := 316601607886) oneChunk325 oneChunk326

theorem range328To330 : chunk 328 2 = 621829407954 :=
  join_chunk (f := 328) (a := 1) (b := 1) (u := 312048599524) (v := 309780808430) oneChunk328 oneChunk329

theorem range327To330 : chunk 327 3 = 936152558164 :=
  join_chunk (f := 327) (a := 1) (b := 2) (u := 314323150210) (v := 621829407954) oneChunk327 range328To330

theorem range325To330 : chunk 325 5 = 1571640942700 :=
  join_chunk (f := 325) (a := 2) (b := 3) (u := 635488384536) (v := 936152558164) range325To327 range327To330

theorem range320To330 : chunk 320 10 = 3200523496998 :=
  join_chunk (f := 320) (a := 5) (b := 5) (u := 1628882554298) (v := 1571640942700) range320To325 range325To330

theorem range330To332 : chunk 330 2 = 612776906092 :=
  join_chunk (f := 330) (a := 1) (b := 1) (u := 307516968548) (v := 305259937544) oneChunk330 oneChunk331

theorem range333To335 : chunk 333 2 = 599279319776 :=
  join_chunk (f := 333) (a := 1) (b := 1) (u := 300760726860) (v := 298518592916) oneChunk333 oneChunk334

theorem range332To335 : chunk 332 3 = 902286222506 :=
  join_chunk (f := 332) (a := 1) (b := 2) (u := 303006902730) (v := 599279319776) oneChunk332 range333To335

theorem range330To335 : chunk 330 5 = 1515063128598 :=
  join_chunk (f := 330) (a := 2) (b := 3) (u := 612776906092) (v := 902286222506) range330To332 range332To335

theorem range335To337 : chunk 335 2 = 590335601794 :=
  join_chunk (f := 335) (a := 1) (b := 1) (u := 296283368764) (v := 294052233030) oneChunk335 oneChunk336

theorem range338To340 : chunk 338 2 = 577003015332 :=
  join_chunk (f := 338) (a := 1) (b := 1) (u := 289608020072) (v := 287394995260) oneChunk338 oneChunk339

theorem range337To340 : chunk 337 3 = 868831074050 :=
  join_chunk (f := 337) (a := 1) (b := 2) (u := 291828058718) (v := 577003015332) oneChunk337 range338To340

theorem range335To340 : chunk 335 5 = 1459166675844 :=
  join_chunk (f := 335) (a := 2) (b := 3) (u := 590335601794) (v := 868831074050) range335To337 range337To340

theorem range330To340 : chunk 330 10 = 2974229804442 :=
  join_chunk (f := 330) (a := 5) (b := 5) (u := 1515063128598) (v := 1459166675844) range330To335 range335To340

theorem range320To340 : chunk 320 20 = 6174753301440 :=
  join_chunk (f := 320) (a := 10) (b := 10) (u := 3200523496998) (v := 2974229804442) range320To330 range330To340

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch320

section Pack_Z6970PlateauChunkedBatch340

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range340To342 : chunk 340 2 = 568170534122 :=
  join_chunk (f := 340) (a := 1) (b := 1) (u := 285186154118) (v := 282984380004) oneChunk340 oneChunk341

theorem range343To345 : chunk 343 2 = 555006696554 :=
  join_chunk (f := 343) (a := 1) (b := 1) (u := 278596417642) (v := 276410278912) oneChunk343 oneChunk344

theorem range342To345 : chunk 342 3 = 835793534876 :=
  join_chunk (f := 342) (a := 1) (b := 2) (u := 280786838322) (v := 555006696554) oneChunk342 range343To345

theorem range340To345 : chunk 340 5 = 1403964068998 :=
  join_chunk (f := 340) (a := 2) (b := 3) (u := 568170534122) (v := 835793534876) range340To342 range342To345

theorem range345To347 : chunk 345 2 = 546288001134 :=
  join_chunk (f := 345) (a := 1) (b := 1) (u := 274231315940) (v := 272056685194) oneChunk345 oneChunk346

theorem range348To350 : chunk 348 2 = 533296810522 :=
  join_chunk (f := 348) (a := 1) (b := 1) (u := 267726269550) (v := 265570540972) oneChunk348 oneChunk349

theorem range347To350 : chunk 347 3 = 803186096266 :=
  join_chunk (f := 347) (a := 1) (b := 2) (u := 269889285744) (v := 533296810522) oneChunk347 range348To350

theorem range345To350 : chunk 345 5 = 1349474097400 :=
  join_chunk (f := 345) (a := 2) (b := 3) (u := 546288001134) (v := 803186096266) range345To347 range347To350

theorem range340To350 : chunk 340 10 = 2753438166398 :=
  join_chunk (f := 340) (a := 5) (b := 5) (u := 1403964068998) (v := 1349474097400) range340To345 range345To350

theorem range350To352 : chunk 350 2 = 524694546060 :=
  join_chunk (f := 350) (a := 1) (b := 1) (u := 263419247438) (v := 261275298622) oneChunk350 oneChunk351

theorem range353To355 : chunk 353 2 = 511880039794 :=
  join_chunk (f := 353) (a := 1) (b := 1) (u := 257003778766) (v := 254876261028) oneChunk353 oneChunk354

theorem range352To355 : chunk 352 3 = 771015877188 :=
  join_chunk (f := 352) (a := 1) (b := 2) (u := 259135837394) (v := 511880039794) oneChunk352 range353To355

theorem range350To355 : chunk 350 5 = 1295710423248 :=
  join_chunk (f := 350) (a := 2) (b := 3) (u := 524694546060) (v := 771015877188) range350To352 range352To355

theorem range355To357 : chunk 355 2 = 503396947582 :=
  join_chunk (f := 355) (a := 1) (b := 1) (u := 252756204554) (v := 250640743028) oneChunk355 oneChunk356

theorem range358To360 : chunk 358 2 = 490763312200 :=
  join_chunk (f := 358) (a := 1) (b := 1) (u := 246429511158) (v := 244333801042) oneChunk358 oneChunk359

theorem range357To360 : chunk 357 3 = 739296114412 :=
  join_chunk (f := 357) (a := 1) (b := 2) (u := 248532802212) (v := 490763312200) oneChunk357 range358To360

theorem range355To360 : chunk 355 5 = 1242693061994 :=
  join_chunk (f := 355) (a := 2) (b := 3) (u := 503396947582) (v := 739296114412) range355To357 range357To360

theorem range350To360 : chunk 350 10 = 2538403485242 :=
  join_chunk (f := 350) (a := 5) (b := 5) (u := 1295710423248) (v := 1242693061994) range350To355 range355To360

theorem range340To360 : chunk 340 20 = 5291841651640 :=
  join_chunk (f := 340) (a := 10) (b := 10) (u := 2753438166398) (v := 2538403485242) range340To350 range350To360

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch340

section Pack_Z6970PlateauChunkedBatch360

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range360To362 : chunk 360 2 = 482402229680 :=
  join_chunk (f := 360) (a := 1) (b := 1) (u := 242242796258) (v := 240159433422) oneChunk360 oneChunk361

theorem range363To365 : chunk 363 2 = 469953790922 :=
  join_chunk (f := 363) (a := 1) (b := 1) (u := 236009934808) (v := 233943856114) oneChunk363 oneChunk364

theorem range362To365 : chunk 362 3 = 708034623168 :=
  join_chunk (f := 362) (a := 1) (b := 2) (u := 238080832246) (v := 469953790922) oneChunk362 range363To365

theorem range360To365 : chunk 360 5 = 1190436852848 :=
  join_chunk (f := 360) (a := 2) (b := 3) (u := 482402229680) (v := 708034623168) range360To362 range362To365

theorem range365To367 : chunk 365 2 = 461717651662 :=
  join_chunk (f := 365) (a := 1) (b := 1) (u := 231885543730) (v := 229832107932) oneChunk365 oneChunk366

theorem range368To370 : chunk 368 2 = 449458884540 :=
  join_chunk (f := 368) (a := 1) (b := 1) (u := 225745830846) (v := 223713053694) oneChunk368 oneChunk369

theorem range367To370 : chunk 367 3 = 677245386338 :=
  join_chunk (f := 367) (a := 1) (b := 2) (u := 227786501798) (v := 449458884540) oneChunk367 range368To370

theorem range365To370 : chunk 365 5 = 1138963038000 :=
  join_chunk (f := 365) (a := 2) (b := 3) (u := 461717651662) (v := 677245386338) range365To367 range367To370

theorem range360To370 : chunk 360 10 = 2329399890848 :=
  join_chunk (f := 360) (a := 5) (b := 5) (u := 1190436852848) (v := 1138963038000) range360To365 range365To370

theorem range370To372 : chunk 370 2 = 441350718258 :=
  join_chunk (f := 370) (a := 1) (b := 1) (u := 221685271078) (v := 219665447180) oneChunk370 oneChunk371

theorem range373To375 : chunk 373 2 = 429286236862 :=
  join_chunk (f := 373) (a := 1) (b := 1) (u := 215643933092) (v := 213642303770) oneChunk373 oneChunk374

theorem range372To375 : chunk 372 3 = 646936914790 :=
  join_chunk (f := 372) (a := 1) (b := 2) (u := 217650677928) (v := 429286236862) oneChunk372 range373To375

theorem range370To375 : chunk 370 5 = 1088287633048 :=
  join_chunk (f := 370) (a := 2) (b := 3) (u := 441350718258) (v := 646936914790) range370To372 range372To375

theorem range375To377 : chunk 375 2 = 421309169400 :=
  join_chunk (f := 375) (a := 1) (b := 1) (u := 211648765344) (v := 209660404056) oneChunk375 oneChunk376

theorem range378To380 : chunk 378 2 = 409443737218 :=
  join_chunk (f := 378) (a := 1) (b := 1) (u := 205705237314) (v := 203738499904) oneChunk378 oneChunk379

theorem range377To380 : chunk 377 3 = 617123938144 :=
  join_chunk (f := 377) (a := 1) (b := 2) (u := 207680200926) (v := 409443737218) oneChunk377 range378To380

theorem range375To380 : chunk 375 5 = 1038433107544 :=
  join_chunk (f := 375) (a := 2) (b := 3) (u := 421309169400) (v := 617123938144) range375To377 range377To380

theorem range370To380 : chunk 370 10 = 2126720740592 :=
  join_chunk (f := 370) (a := 5) (b := 5) (u := 1088287633048) (v := 1038433107544) range370To375 range375To380

theorem range360To380 : chunk 360 20 = 4456120631440 :=
  join_chunk (f := 360) (a := 10) (b := 10) (u := 2329399890848) (v := 2126720740592) range360To370 range370To380

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch360
