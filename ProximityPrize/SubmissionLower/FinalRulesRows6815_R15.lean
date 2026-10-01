import ProximityPrize.SubmissionLower.MergedInfra6815_54
namespace ProximityPrize.SubmissionLower.FinalRulesRows6815_R15
open FinalCurves6815 FinalRulesRowCheck6815 FinalRulesCached6815 FinalRulesCompact6815 SingletonCertificate6815 CompactAllN6815
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private abbrev D : ℕ → List Piece := FinalRulesRowCheck6815.decode
def row (v : ℕ) : List Piece := (#[D 0x22baa00157d500112d700052ae40041219500402db0006,D 0x22ba900157b600112c0000529640041204500403b70006,D 0x22ba8001579600112a9000527f400411f0500403b70006,D 0x22ba7001577600112920005268400411db500403b70006,D 0x22ba60015755001127a0005250400411c6500403b60006,D 0x22ba5001573400112620005238400411b1500403b50006,D 0x22ba40015712001124a00052204004119b500403b40006,D 0x22ba300156f00011232000520740041186500403b30006,D 0x22ba200156cf001121900051ee40041170500403b10006,D 0x22ba100156ae001120000051d64004115a500403b00006,D 0x22ba0001568c00111e700051bc40041144500403ae0006,D 0x22b9f001566a00111ce00051a34004112e500403ad0006,D 0x22b9e001564700111b4000518940041117500403ab0006,D 0x22b9d0015623001119a000516f40041101500403e80006,D 0x22b9c00155ff00111800005155400410ea500404810006,D 0x22b9b00155da0011166000513b300410d3400410d2500404de6004001e0008,D 0x22b9a00155b5001114b0005120300410bb400410ba500405186004004c0008,D 0x22b99001558f00111300005105400410a4500405506004007a0007,D 0x22b980015569001111500050e9000108c4004108b50040587600400a70008,D 0x22b97001554300110f900050cd000107440041073500405bd600400d50008,D 0x22b96001551d00110dd00050b14004105b500405f0600401030007,D 0x22b9500154f500110c1000509500010434004104250040623600401300008,D 0x22b9400154cd00110a400050784004102a500406536004015d0007,D 0x22b9300154a50011087000505a000101040040fea5004066d6004018b0008,D 0x22b92001547b001106a000503d10040ff7f0040f8b40040f8950040670600401b80009,D 0x22b910015451001104c1004101f40040f2e5004066e600401e50007,D 0x22b900015426001102d1004100040040ed65004066a600402120007,D 0x22b8f00153fb001100f10040fe1f0040e8240040e80500406616004023f0008,D 0x22b8e00153cf0010fef10040fc240040e30500406556004026b0007,D 0x22b8d00153a30010fd010040fa21f0080de340040de150040646600402980008,D 0x22b8c00153750010fb010040f8140040d725004065b600402c50007,D 0x22b8b001955800153460010f8f10040f602f0080d2c40040d2a50040645600402f10009,D 0x22b8a001952c00153170010f6e10040f3f40040ce75004062d6004031e0008,D 0x22b8900194ff00152e70010f4c10040f1d40040ca5500406126004034a0008,D 0x22b88001936c00152b50010f2910040efa3f0080c6740040c65500405f6600403760009,D 0x22b8700152830010f060008ed6000cec410040ec020040d214f0080c2a40040c28500405d7600403a2000b,D 0x22b8600152500010ee30008eb2001ce7620040ddc30040bd440040bc2500405d2600403c270040007000b,D 0x22b85001521b0010ebe0008e8d001ce2620040cbb4f0080b9240040b90500405b5600403c17004001d000b,D 0x22b8400151e50010e990008e68001cdd420040c8c40040b5b50040590600403bf70040034000a,D 0x22b8300151ae0010e73000ce410008db120040da340040b5b50040534600403bf7004004a000a,D 0x22b82001517520040e7740040b5b500404d8600403be700400600007,D 0x22b81001513b20040e8340040b5b5004047d600403bc700400770007,D 0x22b80002543700150ff0010dfc001cdc920040d6730040cc340040ba45004042b600403bc7004008d000b,D 0x22b7f00253ff00150c10010dd2001cd9f20040d3630040c8a40040b7b50040401600403bb700400a3000b,D 0x22b7e00253fe00150820010da8001cd7320040d0830040c5440040b51500403d6600403b9700400b9000b,D 0x22b7d00261930031195003116e002d041002ce27002ce120034de920040ce730040c1f40040b85500403d6600403b9700400b8000e,D 0x22b7c00263a700311950031131002cffe002ce27002ce120034de920040caf30040be740040bbe500403d6600403b9700400b7000e,D 0x22b7b002660f003119500310f2002cfb8002ce27002cdf90034de920040caf30040be740040bbe500403d6600403b9700400b6000e,D 0x22b7a002662f003119500310b0002cf71002ce270034de930040c4b40040bbe500403d6600403b9700400b4000c,D 0x22b7900266180031195003106d002cf27002ce270034de90028caf0034c8830040c4b40040b84600403b5700400c4000d,D 0x22b78002660300311950031027002cedb002ce270034de9002ccaf0028cae0034c5430040c4a40040b84600403b5700400c3000e,D 0x22b7700265f00031195003102700310200030fde002ce8c002ce270034de9002ccaf0028cae30040c4a40040b84600403b5700400c2000f,D 0x22b7600265d90031195003102700310210030fde0030fc70030f93002ce3b002ce270034de930040c4a40040b84600403b5700400c0000f,D 0x22b75002547e0031195003102700310220030fde0030fc80030f930030f6d0030f450030e270034e010034de930040c4a40040b84600403b5700400bf0011,D 0x22b7400255eb0031195003102700310230030fde0030fc80030f930030f6e0030f450030f120030ef40030e270034de930040c4a40040b84600403b5700400be0012,D 0x22b7300257550031195003102700310240030fde0030fc90030f930030f6e0030f450030f120030ef40030eb50030ea00030e270034de930040c4a40040b84600403b5700400bc0014,D 0x22b7200258bc0031195003102700310250030fde0030fca0030f930030f6e0030f450030f130030ef40030eb50030ea00030e560030e490030e270034de90028c4a30040c4940040b84600403b5700400bb0017,D 0x22b710025a22003119500310260030fde0030fca0030f930030f6f0030f450030f130030ef40030eb60030ea00030e570030e490030e270034de90028c4a30040c4940040b85600403b5700400b90016,D 0x22b700025b850031195003105a0030fde0030fcb0030f930030f6f0030f450030f130030ef40030eb60030ea00030e570030e490030e270034de90028c4a30040c4940040b85600403b5700400b80016,D 0x22b6f0025ce60024d6330040c5140040b85600403b5700400b60007,D 0x22b6e0025e440024d6230040c5140040b85600403b5700400b50007,D 0x22b6d0025f9f0024d6130040c5040040b85600403b5700400b30007,D 0x22b6c00261060024d6030040c5040040b85600403b5700400b20007,D 0x22b6b00262700024d5f30040c5040040b86600403b5700400b00007,D 0x22b6a00263dd0024d5e30040c5040040b86600403b5700400ae0007,D 0x22b6900264f50024d5d30040c260024bcd30040bb940040baf600403b5700400ad0009,D 0x22b6800264de0024d5c40040bea0024bcc40040bb4600403b5700400ab0008,D 0x22b6700264c70024d5b40040bea0024bcb40040bb4600403b5700400a90008,D 0x22b6600264af0024d5a40040bea0024bca40040bb4600403b5700400a80008,D 0x22b6500264980024d5940040bea0024bc940040bb4600403b5700400a60008,D 0x22b6400264800024d5840040bea0024bc840040bb4600403b5700400a40008,D 0x22b6300264690024d5740040bea0024bc740040bb4600403b5700400a30008,D 0x22b6200264520024d5640040bea0024bc640040bb3600403b5700400a10008,D 0x22b61002643a0024d5540040bea0024bc540040bb3600403b57004009f0008,D 0x22b6000264230024d5440040be90024bc440040bb3600403b57004009d0008,D 0x22b5f002640a0024d5340040be90024bc340040bb3600403b57004009b0008,D 0x22b5e00263f10024d5240040be90024bc240040bb3600403b5700400990008,D 0x22b5d00263d80024d5140040be90024bc140040bb3600403b5700400980008,D 0x22b5c00263c00024d5040040be90024bc040040bb3600403b5700400960008,D 0x22b5b00263a70024d4f40040be80024bbf40040bb2600403b5700400930008,D 0x22b5a00263900024d4e40040be80024bbe40040bb2600403b5700400910008,D 0x22b5900257110024d4d40040be80024bbd40040bb2600403b5700400910008,D 0x22b5800257bd0024d4c40040be80024bbc40040bb2600403b5700400910008,D 0x22b5700258670024d4b40040be70024bbb40040bb2600403b5700400910008,D 0x22b5600259100024d4a40040be70024bba40040bb1600403b5700400910008,D 0x22b5500259b70024d4940040be70024bb940040bb1600403b5700400910008,D 0x22b540025a5d0024d4840040be70024bb840040bb1600403b5700400910008,D 0x22b530025b020024d4740040be60024bb740040bb1600403b5700400920008,D 0x22b520025ba60024d4640040be60024bb640040bb0600403b5700400920008,D 0x22b510025c490024d4540040be60024bb540040bb0600403b5700400920008,D 0x22b500025ce90024d4440040be50024bb440040bb0600403b5700400920008,D 0x22b4f0025d870024d4340040be50024bb340040baf600403b5700400920008,D 0x22b4e0025e250024d4240040be50024bb240040baf600403b5700400920008,D 0x22b4d0025ec30024d4140040be40024bb140040baf600403b5700400920008,D 0x22b4c0025f5d0024d4040040be40024bb040040bae600403b5700400920008,D 0x22b4b0025ff70024d3f40040be440040bb00024baf40040bae600403b5700400920009,D 0x22b4a002608e0024d3e40040be3600403b5700400930006,D 0x22b4900261240024d3d40040be3600403b5700400930006,D 0x22b4800261890024d3c40040bcb0024bac40040b96500403cc600403b6700400930009,D 0x22b4700261950024d3b0024bab40040b5150040411600403b6700400930008,D 0x22b4600261790024d3a0024baa40040afa50040467600403b6700400930008,D 0x22b45002615d0024d390024ba940040aa5500404bd600403b6700400930008,D 0x22b44002613f0024d380024ba840040a5050040510600403b6700400930008,D 0x22b4300261210024d370024ba7400409fe50040563600403b6700400930008,D 0x22b4200261020024d360024ba6400409ab500405b5600403b6700400940008,D 0x22b4100260e10024d350024ba54004095a50040606600403b6700400940008,D 0x22b4000260bf0024d340024ba44004090a50040655600403b6700400940008,D 0x22b3f002609f0024d330024ba3400408bb500406a4600403b6700400940008,D 0x22b3e002607f0024d320024ba24004086e500406f0600403b6700400940008,D 0x22b3d002605f0024d310024ba1400408235004073b600403b6700400940008,D 0x22b3c002603e0024d300024ba0400407d950040784600403b6700400950008,D 0x22b3b002601c0024d2f0024b9f500407ae600403b6700400950007,D 0x22b3a0025ff70024d2e0024b9e500407ae600403b6700400950007,D 0x22b390025fb50024d2d0024b9d500407ae600403b6700400950007,D 0x22b380025f740024d2c0024b9c500407ad600403b6700400950007,D 0x22b370025f350024d2b0024b9b500407ad600403b6700400950007,D 0x22b360025ef90024d2a0024b9a500407ad600403b6700400960007,D 0x22b350025ebe0024d290024b99500407ad600403b6700400960007,D 0x22b340025e840024d280024b98500407ac600403b6700400960007,D 0x22b330025e4c0024d270024b97500407ac600403b6700400960007,D 0x22b320025e140024d260024b96500407ac600403b6700400960007,D 0x22b310025dde0024d250024b95500407ab600403b6700400960007,D 0x22b300025da70024d240024b94500407ab600403b6700400970007,D 0x22b2f0025d710024d230024b93500407ab600403b6700400970007,D 0x22b2e0025d1e0024d220024b92500407aa600403b6700400970007,D 0x22b2d0025ce30024d210024b91500407aa600403b6700400970007,D 0x22b2c0025ca70024d200024b90500407aa600403b6700400970007,D 0x22b2b0025c600024d1f0024b8f500407a9600403b6700400970007,D 0x22b2a0025c8f0024d1e0024b8e500407a9600403b6700400970007,D 0x22b290025c8f0024d1d0024b8d500407a9600403b6700400970007,D 0x22b280025c8f0024d1c0024b8c500407a8600403b6700400970007,D 0x22b2700261180024d1b0024b8b500407a8600403b6700400980007,D 0x22b2600262cc0024d1a0024b8a500407a8600403b6700400980007,D 0x22b2500264750024d190024b89500407a7600403b6700400980007,D 0x22b24002661e0024d180024b88500407a7600403b6700400980007,D 0x22b2300267c70024d170024b87500407a7600403b6700400980007,D 0x22b2200269640024d160024b86500407a6600403b6700400980007,D 0x22b210026b020024d150024b85500407a6600403b6700400980007,D 0x26b200024d140024b84500407a5600403b6700400980006,D 0x26b1f0024d130024b83500407a5600403b6700400980006,D 0x26b1e0024d120024b82500407a5600403b6700400980006,D 0x26b1d0024d110024b81500407a4600403b6700400980006,D 0x26b1c0024d100024b80500407a4600403b6700400990006,D 0x26b1b0024d0f0024b7f500407a3600403b6700400990006,D 0x26b1a0024d0e0024b7e500407a3600403b6700400990006,D 0x26b190024d0d0024b7d500407a2600403b6700400990006,D 0x22b180025eb50024d0c0024b7c500407a2600403b6700400990007,D 0x22b170025faf0024d0b0024b7b500407a2600403b6700400990007,D 0x22b1600260a80024d0a0024b7a500407a1600403b6700400990007,D 0x22b1500261a10024d090024b79500407a1600403b6700400990007,D 0x22b14002629b0024d080024b78500407a0600403b6700400990007,D 0x22b13002638d0024d070024b77500407a0600403b6700400990007,D 0x22b12002647f0024d060024b765004079f600403b6700400990007,D 0x22b1100265720024d050024b755004079f600403b6700400990007,D 0x22b10002665d0024d040024b745004079e600403b67004009a0007,D 0x22b0f00267500024d030024b735004079e600403b67004009a0007,D 0x22b0e00268470024d020024b725004079d600403b67004009a0007,D 0x22b0d00269350024d010024b715004079d600403b67004009a0007,D 0x22b0c0026a230024d000024b705004079c600403b67004009a0007,D 0x26b0b0024cff0024b6f5004079c600403b67004009a0006,D 0x26b0a0024cfe0024b6e5004079b600403b67004009a0006,D 0x26b090024cfd0024b6d5004079b600403b67004009a0006,D 0x26b080024cfc0024b6c5004079b600403b67004009a0006,D 0x26b070024cfb0024b6b5004079b600403b67004009a0006,D 0x26b060024cfa0024b6a5004079b600403b67004009a0006,D 0x26b050024cf90024b695004079b600403b6700400990006,D 0x26b040024cf80024b685004079b600403b6700400990006,D 0x26b030024cf70024b675004079b600403b6700400990006][v]?).getD []
private abbrev C (v : ℕ) : List Piece := FinalLedgerData6815.row 15 v
private def nb (v : ℕ) : ℕ := (#[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,2,1,1,2,2,2,2,2,2,1,1,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1][v]?).getD 0
private def H : List ℕ := [24,27,29,31,34,35,37,45,46,47,48,49,50,51,52,53,54,55,56,57,58]
private def ok (v : ℕ) : Bool := if v∈H ∨ 168≤v then true else rowL 15 v (C v) (row v) (nb v)
private abbrev I (v i : ℕ) : Prop := indexL 15 v (C v) (row v) i=true
private theorem g0 : allN (fun j => ok (16*0+j)) 16=true := by decide +kernel
private theorem g1 : allN (fun j => ok (16*1+j)) 16=true := by decide +kernel
private theorem g2 : allN (fun j => ok (16*2+j)) 16=true := by decide +kernel
private theorem g3 : allN (fun j => ok (16*3+j)) 16=true := by decide +kernel
private theorem g4 : allN (fun j => ok (16*4+j)) 16=true := by decide +kernel
private theorem g5 : allN (fun j => ok (16*5+j)) 16=true := by decide +kernel
private theorem g6 : allN (fun j => ok (16*6+j)) 16=true := by decide +kernel
private theorem g7 : allN (fun j => ok (16*7+j)) 16=true := by decide +kernel
private theorem g8 : allN (fun j => ok (16*8+j)) 16=true := by decide +kernel
private theorem g9 : allN (fun j => ok (16*9+j)) 16=true := by decide +kernel
private theorem g10 : allN (fun j => ok (16*10+j)) 16=true := by decide +kernel
private theorem a24_0 : I 24 0 := by decide +kernel
private theorem a24_1 : I 24 1 := by decide +kernel
private theorem a24_2 : I 24 2 := by decide +kernel
private theorem a24_3 : I 24 3 := by decide +kernel
private theorem a24_4 : I 24 4 := by decide +kernel
private theorem a24_5 : I 24 5 := by decide +kernel
private theorem a24_6 : I 24 6 := by decide +kernel
private theorem a24_7 : I 24 7 := by decide +kernel
private theorem h24 : checkRow 15 24 (C 24) (row 24)=true := row_of_blocks 15 24 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 24 _ _ 0 (by decide) (by decide) a24_0 a24_1 a24_2 a24_3 a24_4 a24_5 a24_6 a24_7)) (blk 15 24 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a27_0 : I 27 0 := by decide +kernel
private theorem a27_1 : I 27 1 := by decide +kernel
private theorem a27_2 : I 27 2 := by decide +kernel
private theorem a27_3 : I 27 3 := by decide +kernel
private theorem a27_4 : I 27 4 := by decide +kernel
private theorem a27_5 : I 27 5 := by decide +kernel
private theorem a27_6 : I 27 6 := by decide +kernel
private theorem a27_7 : I 27 7 := by decide +kernel
private theorem h27 : checkRow 15 27 (C 27) (row 27)=true := row_of_blocks 15 27 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 15 27 _ _ 0 (by decide) (by decide) a27_0 a27_1 a27_2 a27_3 a27_4 a27_5 a27_6 a27_7))
private theorem a29_0 : I 29 0 := by decide +kernel
private theorem a29_1 : I 29 1 := by decide +kernel
private theorem a29_2 : I 29 2 := by decide +kernel
private theorem a29_3 : I 29 3 := by decide +kernel
private theorem a29_4 : I 29 4 := by decide +kernel
private theorem a29_5 : I 29 5 := by decide +kernel
private theorem a29_6 : I 29 6 := by decide +kernel
private theorem a29_7 : I 29 7 := by decide +kernel
private theorem h29 : checkRow 15 29 (C 29) (row 29)=true := row_of_blocks 15 29 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 15 29 _ _ 0 (by decide) (by decide) a29_0 a29_1 a29_2 a29_3 a29_4 a29_5 a29_6 a29_7))
private theorem a31_0 : I 31 0 := by decide +kernel
private theorem a31_1 : I 31 1 := by decide +kernel
private theorem a31_2 : I 31 2 := by decide +kernel
private theorem a31_3 : I 31 3 := by decide +kernel
private theorem a31_4 : I 31 4 := by decide +kernel
private theorem a31_5 : I 31 5 := by decide +kernel
private theorem a31_6 : I 31 6 := by decide +kernel
private theorem a31_7 : I 31 7 := by decide +kernel
private theorem h31 : checkRow 15 31 (C 31) (row 31)=true := row_of_blocks 15 31 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 31 _ _ 0 (by decide) (by decide) a31_0 a31_1 a31_2 a31_3 a31_4 a31_5 a31_6 a31_7)) (blk 15 31 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a34_0 : I 34 0 := by decide +kernel
private theorem a34_1 : I 34 1 := by decide +kernel
private theorem a34_2 : I 34 2 := by decide +kernel
private theorem a34_3 : I 34 3 := by decide +kernel
private theorem a34_4 : I 34 4 := by decide +kernel
private theorem a34_5 : I 34 5 := by decide +kernel
private theorem a34_6 : I 34 6 := by decide +kernel
private theorem a34_7 : I 34 7 := by decide +kernel
private theorem h34 : checkRow 15 34 (C 34) (row 34)=true := row_of_blocks 15 34 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 34 _ _ 0 (by decide) (by decide) a34_0 a34_1 a34_2 a34_3 a34_4 a34_5 a34_6 a34_7)) (blk 15 34 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a35_0 : I 35 0 := by decide +kernel
private theorem a35_1 : I 35 1 := by decide +kernel
private theorem a35_2 : I 35 2 := by decide +kernel
private theorem a35_3 : I 35 3 := by decide +kernel
private theorem a35_4 : I 35 4 := by decide +kernel
private theorem a35_5 : I 35 5 := by decide +kernel
private theorem a35_6 : I 35 6 := by decide +kernel
private theorem a35_7 : I 35 7 := by decide +kernel
private theorem h35 : checkRow 15 35 (C 35) (row 35)=true := row_of_blocks 15 35 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 35 _ _ 0 (by decide) (by decide) a35_0 a35_1 a35_2 a35_3 a35_4 a35_5 a35_6 a35_7)) (blk 15 35 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a37_0 : I 37 0 := by decide +kernel
private theorem a37_1 : I 37 1 := by decide +kernel
private theorem a37_2 : I 37 2 := by decide +kernel
private theorem a37_3 : I 37 3 := by decide +kernel
private theorem a37_4 : I 37 4 := by decide +kernel
private theorem a37_5 : I 37 5 := by decide +kernel
private theorem a37_6 : I 37 6 := by decide +kernel
private theorem a37_7 : I 37 7 := by decide +kernel
private theorem h37 : checkRow 15 37 (C 37) (row 37)=true := row_of_blocks 15 37 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 37 _ _ 0 (by decide) (by decide) a37_0 a37_1 a37_2 a37_3 a37_4 a37_5 a37_6 a37_7)) (blk 15 37 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a45_0 : I 45 0 := by decide +kernel
private theorem a45_1 : I 45 1 := by decide +kernel
private theorem a45_2 : I 45 2 := by decide +kernel
private theorem a45_3 : I 45 3 := by decide +kernel
private theorem a45_4 : I 45 4 := by decide +kernel
private theorem a45_5 : I 45 5 := by decide +kernel
private theorem a45_6 : I 45 6 := by decide +kernel
private theorem a45_7 : I 45 7 := by decide +kernel
private theorem a45_8 : I 45 8 := by decide +kernel
private theorem a45_9 : I 45 9 := by decide +kernel
private theorem a45_10 : I 45 10 := by decide +kernel
private theorem a45_11 : I 45 11 := by decide +kernel
private theorem a45_12 : I 45 12 := by decide +kernel
private theorem a45_13 : I 45 13 := by decide +kernel
private theorem a45_14 : I 45 14 := by decide +kernel
private theorem a45_15 : I 45 15 := by decide +kernel
private theorem h45 : checkRow 15 45 (C 45) (row 45)=true := row_of_blocks 15 45 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 45 _ _ 0 (by decide) (by decide) a45_0 a45_1 a45_2 a45_3 a45_4 a45_5 a45_6 a45_7)) (blk8 15 45 _ _ 1 (by decide) (by decide) a45_8 a45_9 a45_10 a45_11 a45_12 a45_13 a45_14 a45_15))
private theorem a46_0 : I 46 0 := by decide +kernel
private theorem a46_1 : I 46 1 := by decide +kernel
private theorem a46_2 : I 46 2 := by decide +kernel
private theorem a46_3 : I 46 3 := by decide +kernel
private theorem a46_4 : I 46 4 := by decide +kernel
private theorem a46_5 : I 46 5 := by decide +kernel
private theorem a46_6 : I 46 6 := by decide +kernel
private theorem a46_7 : I 46 7 := by decide +kernel
private theorem a46_8 : I 46 8 := by decide +kernel
private theorem a46_9 : I 46 9 := by decide +kernel
private theorem a46_10 : I 46 10 := by decide +kernel
private theorem a46_11 : I 46 11 := by decide +kernel
private theorem a46_12 : I 46 12 := by decide +kernel
private theorem a46_13 : I 46 13 := by decide +kernel
private theorem a46_14 : I 46 14 := by decide +kernel
private theorem a46_15 : I 46 15 := by decide +kernel
private theorem h46 : checkRow 15 46 (C 46) (row 46)=true := row_of_blocks 15 46 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 46 _ _ 0 (by decide) (by decide) a46_0 a46_1 a46_2 a46_3 a46_4 a46_5 a46_6 a46_7)) (blk8 15 46 _ _ 1 (by decide) (by decide) a46_8 a46_9 a46_10 a46_11 a46_12 a46_13 a46_14 a46_15))
private theorem a47_0 : I 47 0 := by decide +kernel
private theorem a47_1 : I 47 1 := by decide +kernel
private theorem a47_2 : I 47 2 := by decide +kernel
private theorem a47_3 : I 47 3 := by decide +kernel
private theorem a47_4 : I 47 4 := by decide +kernel
private theorem a47_5 : I 47 5 := by decide +kernel
private theorem a47_6 : I 47 6 := by decide +kernel
private theorem a47_7 : I 47 7 := by decide +kernel
private theorem a47_8 : I 47 8 := by decide +kernel
private theorem a47_9 : I 47 9 := by decide +kernel
private theorem a47_10 : I 47 10 := by decide +kernel
private theorem a47_11 : I 47 11 := by decide +kernel
private theorem a47_12 : I 47 12 := by decide +kernel
private theorem a47_13 : I 47 13 := by decide +kernel
private theorem a47_14 : I 47 14 := by decide +kernel
private theorem a47_15 : I 47 15 := by decide +kernel
private theorem h47 : checkRow 15 47 (C 47) (row 47)=true := row_of_blocks 15 47 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 47 _ _ 0 (by decide) (by decide) a47_0 a47_1 a47_2 a47_3 a47_4 a47_5 a47_6 a47_7)) (blk8 15 47 _ _ 1 (by decide) (by decide) a47_8 a47_9 a47_10 a47_11 a47_12 a47_13 a47_14 a47_15))
private theorem a48_0 : I 48 0 := by decide +kernel
private theorem a48_1 : I 48 1 := by decide +kernel
private theorem a48_2 : I 48 2 := by decide +kernel
private theorem a48_3 : I 48 3 := by decide +kernel
private theorem a48_4 : I 48 4 := by decide +kernel
private theorem a48_5 : I 48 5 := by decide +kernel
private theorem a48_6 : I 48 6 := by decide +kernel
private theorem a48_7 : I 48 7 := by decide +kernel
private theorem a48_8 : I 48 8 := by decide +kernel
private theorem a48_9 : I 48 9 := by decide +kernel
private theorem a48_10 : I 48 10 := by decide +kernel
private theorem a48_11 : I 48 11 := by decide +kernel
private theorem a48_12 : I 48 12 := by decide +kernel
private theorem a48_13 : I 48 13 := by decide +kernel
private theorem a48_14 : I 48 14 := by decide +kernel
private theorem a48_15 : I 48 15 := by decide +kernel
private theorem h48 : checkRow 15 48 (C 48) (row 48)=true := row_of_blocks 15 48 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 48 _ _ 0 (by decide) (by decide) a48_0 a48_1 a48_2 a48_3 a48_4 a48_5 a48_6 a48_7)) (blk8 15 48 _ _ 1 (by decide) (by decide) a48_8 a48_9 a48_10 a48_11 a48_12 a48_13 a48_14 a48_15))
private theorem a49_0 : I 49 0 := by decide +kernel
private theorem a49_1 : I 49 1 := by decide +kernel
private theorem a49_2 : I 49 2 := by decide +kernel
private theorem a49_3 : I 49 3 := by decide +kernel
private theorem a49_4 : I 49 4 := by decide +kernel
private theorem a49_5 : I 49 5 := by decide +kernel
private theorem a49_6 : I 49 6 := by decide +kernel
private theorem a49_7 : I 49 7 := by decide +kernel
private theorem a49_8 : I 49 8 := by decide +kernel
private theorem a49_9 : I 49 9 := by decide +kernel
private theorem a49_10 : I 49 10 := by decide +kernel
private theorem a49_11 : I 49 11 := by decide +kernel
private theorem a49_12 : I 49 12 := by decide +kernel
private theorem a49_13 : I 49 13 := by decide +kernel
private theorem a49_14 : I 49 14 := by decide +kernel
private theorem a49_15 : I 49 15 := by decide +kernel
private theorem h49 : checkRow 15 49 (C 49) (row 49)=true := row_of_blocks 15 49 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 49 _ _ 0 (by decide) (by decide) a49_0 a49_1 a49_2 a49_3 a49_4 a49_5 a49_6 a49_7)) (blk8 15 49 _ _ 1 (by decide) (by decide) a49_8 a49_9 a49_10 a49_11 a49_12 a49_13 a49_14 a49_15))
private theorem a50_0 : I 50 0 := by decide +kernel
private theorem a50_1 : I 50 1 := by decide +kernel
private theorem a50_2 : I 50 2 := by decide +kernel
private theorem a50_3 : I 50 3 := by decide +kernel
private theorem a50_4 : I 50 4 := by decide +kernel
private theorem a50_5 : I 50 5 := by decide +kernel
private theorem a50_6 : I 50 6 := by decide +kernel
private theorem a50_7 : I 50 7 := by decide +kernel
private theorem a50_8 : I 50 8 := by decide +kernel
private theorem a50_9 : I 50 9 := by decide +kernel
private theorem a50_10 : I 50 10 := by decide +kernel
private theorem a50_11 : I 50 11 := by decide +kernel
private theorem a50_12 : I 50 12 := by decide +kernel
private theorem a50_13 : I 50 13 := by decide +kernel
private theorem a50_14 : I 50 14 := by decide +kernel
private theorem a50_15 : I 50 15 := by decide +kernel
private theorem h50 : checkRow 15 50 (C 50) (row 50)=true := row_of_blocks 15 50 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 50 _ _ 0 (by decide) (by decide) a50_0 a50_1 a50_2 a50_3 a50_4 a50_5 a50_6 a50_7)) (blk8 15 50 _ _ 1 (by decide) (by decide) a50_8 a50_9 a50_10 a50_11 a50_12 a50_13 a50_14 a50_15))
private theorem a51_0 : I 51 0 := by decide +kernel
private theorem a51_1 : I 51 1 := by decide +kernel
private theorem a51_2 : I 51 2 := by decide +kernel
private theorem a51_3 : I 51 3 := by decide +kernel
private theorem a51_4 : I 51 4 := by decide +kernel
private theorem a51_5 : I 51 5 := by decide +kernel
private theorem a51_6 : I 51 6 := by decide +kernel
private theorem a51_7 : I 51 7 := by decide +kernel
private theorem a51_8 : I 51 8 := by decide +kernel
private theorem a51_9 : I 51 9 := by decide +kernel
private theorem a51_10 : I 51 10 := by decide +kernel
private theorem a51_11 : I 51 11 := by decide +kernel
private theorem a51_12 : I 51 12 := by decide +kernel
private theorem a51_13 : I 51 13 := by decide +kernel
private theorem a51_14 : I 51 14 := by decide +kernel
private theorem a51_15 : I 51 15 := by decide +kernel
private theorem h51 : checkRow 15 51 (C 51) (row 51)=true := row_of_blocks 15 51 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 51 _ _ 0 (by decide) (by decide) a51_0 a51_1 a51_2 a51_3 a51_4 a51_5 a51_6 a51_7)) (blk8 15 51 _ _ 1 (by decide) (by decide) a51_8 a51_9 a51_10 a51_11 a51_12 a51_13 a51_14 a51_15))
private theorem a52_0 : I 52 0 := by decide +kernel
private theorem a52_1 : I 52 1 := by decide +kernel
private theorem a52_2 : I 52 2 := by decide +kernel
private theorem a52_3 : I 52 3 := by decide +kernel
private theorem a52_4 : I 52 4 := by decide +kernel
private theorem a52_5 : I 52 5 := by decide +kernel
private theorem a52_6 : I 52 6 := by decide +kernel
private theorem a52_7 : I 52 7 := by decide +kernel
private theorem a52_8 : I 52 8 := by decide +kernel
private theorem a52_9 : I 52 9 := by decide +kernel
private theorem a52_10 : I 52 10 := by decide +kernel
private theorem a52_11 : I 52 11 := by decide +kernel
private theorem a52_12 : I 52 12 := by decide +kernel
private theorem a52_13 : I 52 13 := by decide +kernel
private theorem a52_14 : I 52 14 := by decide +kernel
private theorem a52_15 : I 52 15 := by decide +kernel
private theorem h52 : checkRow 15 52 (C 52) (row 52)=true := row_of_blocks 15 52 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 52 _ _ 0 (by decide) (by decide) a52_0 a52_1 a52_2 a52_3 a52_4 a52_5 a52_6 a52_7)) (blk8 15 52 _ _ 1 (by decide) (by decide) a52_8 a52_9 a52_10 a52_11 a52_12 a52_13 a52_14 a52_15))
private theorem a53_0 : I 53 0 := by decide +kernel
private theorem a53_1 : I 53 1 := by decide +kernel
private theorem a53_2 : I 53 2 := by decide +kernel
private theorem a53_3 : I 53 3 := by decide +kernel
private theorem a53_4 : I 53 4 := by decide +kernel
private theorem a53_5 : I 53 5 := by decide +kernel
private theorem a53_6 : I 53 6 := by decide +kernel
private theorem a53_7 : I 53 7 := by decide +kernel
private theorem a53_8 : I 53 8 := by decide +kernel
private theorem a53_9 : I 53 9 := by decide +kernel
private theorem a53_10 : I 53 10 := by decide +kernel
private theorem a53_11 : I 53 11 := by decide +kernel
private theorem a53_12 : I 53 12 := by decide +kernel
private theorem a53_13 : I 53 13 := by decide +kernel
private theorem a53_14 : I 53 14 := by decide +kernel
private theorem a53_15 : I 53 15 := by decide +kernel
private theorem h53 : checkRow 15 53 (C 53) (row 53)=true := row_of_blocks 15 53 _ _ 3 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 2 (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 53 _ _ 0 (by decide) (by decide) a53_0 a53_1 a53_2 a53_3 a53_4 a53_5 a53_6 a53_7)) (blk8 15 53 _ _ 1 (by decide) (by decide) a53_8 a53_9 a53_10 a53_11 a53_12 a53_13 a53_14 a53_15)) (blk 15 53 _ _ 2 (by decide) (by decide) (by decide +kernel)))
private theorem a54_0 : I 54 0 := by decide +kernel
private theorem a54_1 : I 54 1 := by decide +kernel
private theorem a54_2 : I 54 2 := by decide +kernel
private theorem a54_3 : I 54 3 := by decide +kernel
private theorem a54_4 : I 54 4 := by decide +kernel
private theorem a54_5 : I 54 5 := by decide +kernel
private theorem a54_6 : I 54 6 := by decide +kernel
private theorem a54_7 : I 54 7 := by decide +kernel
private theorem a54_8 : I 54 8 := by decide +kernel
private theorem a54_9 : I 54 9 := by decide +kernel
private theorem a54_10 : I 54 10 := by decide +kernel
private theorem a54_11 : I 54 11 := by decide +kernel
private theorem a54_12 : I 54 12 := by decide +kernel
private theorem a54_13 : I 54 13 := by decide +kernel
private theorem a54_14 : I 54 14 := by decide +kernel
private theorem a54_15 : I 54 15 := by decide +kernel
private theorem h54 : checkRow 15 54 (C 54) (row 54)=true := row_of_blocks 15 54 _ _ 3 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 2 (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 54 _ _ 0 (by decide) (by decide) a54_0 a54_1 a54_2 a54_3 a54_4 a54_5 a54_6 a54_7)) (blk8 15 54 _ _ 1 (by decide) (by decide) a54_8 a54_9 a54_10 a54_11 a54_12 a54_13 a54_14 a54_15)) (blk 15 54 _ _ 2 (by decide) (by decide) (by decide +kernel)))
private theorem a55_0 : I 55 0 := by decide +kernel
private theorem a55_1 : I 55 1 := by decide +kernel
private theorem a55_2 : I 55 2 := by decide +kernel
private theorem a55_3 : I 55 3 := by decide +kernel
private theorem a55_4 : I 55 4 := by decide +kernel
private theorem a55_5 : I 55 5 := by decide +kernel
private theorem a55_6 : I 55 6 := by decide +kernel
private theorem a55_7 : I 55 7 := by decide +kernel
private theorem a55_8 : I 55 8 := by decide +kernel
private theorem a55_9 : I 55 9 := by decide +kernel
private theorem a55_10 : I 55 10 := by decide +kernel
private theorem a55_11 : I 55 11 := by decide +kernel
private theorem a55_12 : I 55 12 := by decide +kernel
private theorem a55_13 : I 55 13 := by decide +kernel
private theorem a55_14 : I 55 14 := by decide +kernel
private theorem a55_15 : I 55 15 := by decide +kernel
private theorem a55_16 : I 55 16 := by decide +kernel
private theorem a55_17 : I 55 17 := by decide +kernel
private theorem a55_18 : I 55 18 := by decide +kernel
private theorem a55_19 : I 55 19 := by decide +kernel
private theorem a55_20 : I 55 20 := by decide +kernel
private theorem a55_21 : I 55 21 := by decide +kernel
private theorem a55_22 : I 55 22 := by decide +kernel
private theorem a55_23 : I 55 23 := by decide +kernel
private theorem h55 : checkRow 15 55 (C 55) (row 55)=true := row_of_blocks 15 55 _ _ 3 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 2 (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 55 _ _ 0 (by decide) (by decide) a55_0 a55_1 a55_2 a55_3 a55_4 a55_5 a55_6 a55_7)) (blk8 15 55 _ _ 1 (by decide) (by decide) a55_8 a55_9 a55_10 a55_11 a55_12 a55_13 a55_14 a55_15)) (blk8 15 55 _ _ 2 (by decide) (by decide) a55_16 a55_17 a55_18 a55_19 a55_20 a55_21 a55_22 a55_23))
private theorem a56_0 : I 56 0 := by decide +kernel
private theorem a56_1 : I 56 1 := by decide +kernel
private theorem a56_2 : I 56 2 := by decide +kernel
private theorem a56_3 : I 56 3 := by decide +kernel
private theorem a56_4 : I 56 4 := by decide +kernel
private theorem a56_5 : I 56 5 := by decide +kernel
private theorem a56_6 : I 56 6 := by decide +kernel
private theorem a56_7 : I 56 7 := by decide +kernel
private theorem a56_8 : I 56 8 := by decide +kernel
private theorem a56_9 : I 56 9 := by decide +kernel
private theorem a56_10 : I 56 10 := by decide +kernel
private theorem a56_11 : I 56 11 := by decide +kernel
private theorem a56_12 : I 56 12 := by decide +kernel
private theorem a56_13 : I 56 13 := by decide +kernel
private theorem a56_14 : I 56 14 := by decide +kernel
private theorem a56_15 : I 56 15 := by decide +kernel
private theorem a56_16 : I 56 16 := by decide +kernel
private theorem a56_17 : I 56 17 := by decide +kernel
private theorem a56_18 : I 56 18 := by decide +kernel
private theorem a56_19 : I 56 19 := by decide +kernel
private theorem a56_20 : I 56 20 := by decide +kernel
private theorem a56_21 : I 56 21 := by decide +kernel
private theorem a56_22 : I 56 22 := by decide +kernel
private theorem a56_23 : I 56 23 := by decide +kernel
private theorem h56 : checkRow 15 56 (C 56) (row 56)=true := row_of_blocks 15 56 _ _ 3 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 2 (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 56 _ _ 0 (by decide) (by decide) a56_0 a56_1 a56_2 a56_3 a56_4 a56_5 a56_6 a56_7)) (blk8 15 56 _ _ 1 (by decide) (by decide) a56_8 a56_9 a56_10 a56_11 a56_12 a56_13 a56_14 a56_15)) (blk8 15 56 _ _ 2 (by decide) (by decide) a56_16 a56_17 a56_18 a56_19 a56_20 a56_21 a56_22 a56_23))
private theorem a57_0 : I 57 0 := by decide +kernel
private theorem a57_1 : I 57 1 := by decide +kernel
private theorem a57_2 : I 57 2 := by decide +kernel
private theorem a57_3 : I 57 3 := by decide +kernel
private theorem a57_4 : I 57 4 := by decide +kernel
private theorem a57_5 : I 57 5 := by decide +kernel
private theorem a57_6 : I 57 6 := by decide +kernel
private theorem a57_7 : I 57 7 := by decide +kernel
private theorem a57_8 : I 57 8 := by decide +kernel
private theorem a57_9 : I 57 9 := by decide +kernel
private theorem a57_10 : I 57 10 := by decide +kernel
private theorem a57_11 : I 57 11 := by decide +kernel
private theorem a57_12 : I 57 12 := by decide +kernel
private theorem a57_13 : I 57 13 := by decide +kernel
private theorem a57_14 : I 57 14 := by decide +kernel
private theorem a57_15 : I 57 15 := by decide +kernel
private theorem a57_16 : I 57 16 := by decide +kernel
private theorem a57_17 : I 57 17 := by decide +kernel
private theorem a57_18 : I 57 18 := by decide +kernel
private theorem a57_19 : I 57 19 := by decide +kernel
private theorem a57_20 : I 57 20 := by decide +kernel
private theorem a57_21 : I 57 21 := by decide +kernel
private theorem a57_22 : I 57 22 := by decide +kernel
private theorem a57_23 : I 57 23 := by decide +kernel
private theorem h57 : checkRow 15 57 (C 57) (row 57)=true := row_of_blocks 15 57 _ _ 3 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 2 (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 57 _ _ 0 (by decide) (by decide) a57_0 a57_1 a57_2 a57_3 a57_4 a57_5 a57_6 a57_7)) (blk8 15 57 _ _ 1 (by decide) (by decide) a57_8 a57_9 a57_10 a57_11 a57_12 a57_13 a57_14 a57_15)) (blk8 15 57 _ _ 2 (by decide) (by decide) a57_16 a57_17 a57_18 a57_19 a57_20 a57_21 a57_22 a57_23))
private theorem a58_0 : I 58 0 := by decide +kernel
private theorem a58_1 : I 58 1 := by decide +kernel
private theorem a58_2 : I 58 2 := by decide +kernel
private theorem a58_3 : I 58 3 := by decide +kernel
private theorem a58_4 : I 58 4 := by decide +kernel
private theorem a58_5 : I 58 5 := by decide +kernel
private theorem a58_6 : I 58 6 := by decide +kernel
private theorem a58_7 : I 58 7 := by decide +kernel
private theorem a58_8 : I 58 8 := by decide +kernel
private theorem a58_9 : I 58 9 := by decide +kernel
private theorem a58_10 : I 58 10 := by decide +kernel
private theorem a58_11 : I 58 11 := by decide +kernel
private theorem a58_12 : I 58 12 := by decide +kernel
private theorem a58_13 : I 58 13 := by decide +kernel
private theorem a58_14 : I 58 14 := by decide +kernel
private theorem a58_15 : I 58 15 := by decide +kernel
private theorem a58_16 : I 58 16 := by decide +kernel
private theorem a58_17 : I 58 17 := by decide +kernel
private theorem a58_18 : I 58 18 := by decide +kernel
private theorem a58_19 : I 58 19 := by decide +kernel
private theorem a58_20 : I 58 20 := by decide +kernel
private theorem a58_21 : I 58 21 := by decide +kernel
private theorem a58_22 : I 58 22 := by decide +kernel
private theorem a58_23 : I 58 23 := by decide +kernel
private theorem h58 : checkRow 15 58 (C 58) (row 58)=true := row_of_blocks 15 58 _ _ 3 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 2 (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 15 58 _ _ 0 (by decide) (by decide) a58_0 a58_1 a58_2 a58_3 a58_4 a58_5 a58_6 a58_7)) (blk8 15 58 _ _ 1 (by decide) (by decide) a58_8 a58_9 a58_10 a58_11 a58_12 a58_13 a58_14 a58_15)) (blk8 15 58 _ _ 2 (by decide) (by decide) a58_16 a58_17 a58_18 a58_19 a58_20 a58_21 a58_22 a58_23))
private theorem okAt (v : ℕ) (hv : v<176) : ok v=true := by
  rcases (show (0≤v ∧ v<16) ∨ (16≤v ∧ v<32) ∨ (32≤v ∧ v<48) ∨ (48≤v ∧ v<64) ∨ (64≤v ∧ v<80) ∨ (80≤v ∧ v<96) ∨ (96≤v ∧ v<112) ∨ (112≤v ∧ v<128) ∨ (128≤v ∧ v<144) ∨ (144≤v ∧ v<160) ∨ (160≤v ∧ v<176) by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · exact allN_block ok 0 g0 v (by omega) (by omega)
  · exact allN_block ok 1 g1 v (by omega) (by omega)
  · exact allN_block ok 2 g2 v (by omega) (by omega)
  · exact allN_block ok 3 g3 v (by omega) (by omega)
  · exact allN_block ok 4 g4 v (by omega) (by omega)
  · exact allN_block ok 5 g5 v (by omega) (by omega)
  · exact allN_block ok 6 g6 v (by omega) (by omega)
  · exact allN_block ok 7 g7 v (by omega) (by omega)
  · exact allN_block ok 8 g8 v (by omega) (by omega)
  · exact allN_block ok 9 g9 v (by omega) (by omega)
  · exact allN_block ok 10 g10 v (by omega) (by omega)
theorem checked (v : ℕ) (hv : v≤167) : checkRow 15 v (FinalLedgerData6815.row 15 v) (row v)=true := by
  by_cases e24 : v=24
  · subst e24; exact h24
  by_cases e27 : v=27
  · subst e27; exact h27
  by_cases e29 : v=29
  · subst e29; exact h29
  by_cases e31 : v=31
  · subst e31; exact h31
  by_cases e34 : v=34
  · subst e34; exact h34
  by_cases e35 : v=35
  · subst e35; exact h35
  by_cases e37 : v=37
  · subst e37; exact h37
  by_cases e45 : v=45
  · subst e45; exact h45
  by_cases e46 : v=46
  · subst e46; exact h46
  by_cases e47 : v=47
  · subst e47; exact h47
  by_cases e48 : v=48
  · subst e48; exact h48
  by_cases e49 : v=49
  · subst e49; exact h49
  by_cases e50 : v=50
  · subst e50; exact h50
  by_cases e51 : v=51
  · subst e51; exact h51
  by_cases e52 : v=52
  · subst e52; exact h52
  by_cases e53 : v=53
  · subst e53; exact h53
  by_cases e54 : v=54
  · subst e54; exact h54
  by_cases e55 : v=55
  · subst e55; exact h55
  by_cases e56 : v=56
  · subst e56; exact h56
  by_cases e57 : v=57
  · subst e57; exact h57
  by_cases e58 : v=58
  · subst e58; exact h58
  have hH : ¬(v∈H ∨ 168≤v) := by simp only [H,List.mem_cons,List.not_mem_nil,or_false,false_or]; omega
  have h := okAt v (by omega)
  simp only [ok,if_neg hH] at h
  exact row_of_rowL 15 v _ _ (nb v) (by omega) (by omega) h
end ProximityPrize.SubmissionLower.FinalRulesRows6815_R15
