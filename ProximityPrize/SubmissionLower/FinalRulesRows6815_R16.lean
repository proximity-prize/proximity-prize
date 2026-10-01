import ProximityPrize.SubmissionLower.MergedInfra6815_54
namespace ProximityPrize.SubmissionLower.FinalRulesRows6815_R16
open FinalCurves6815 FinalRulesRowCheck6815 FinalRulesCached6815 FinalRulesCompact6815 SingletonCertificate6815 CompactAllN6815
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private abbrev D : ℕ → List Piece := FinalRulesRowCheck6815.decode
def row (v : ℕ) : List Piece := (#[D 0x22ba900157060011247000521c4004119d500405980006,D 0x22ba800156e6001122f000520440041188500406790006,D 0x22ba700156c5001121700051ec40041173500406790006,D 0x22ba600156a400111ff00051d34004115d500406790006,D 0x22ba5001568300111e600051bb40041148500406790006,D 0x22ba4001566100111cd00051a240041132500406780006,D 0x22ba3001563f00111b400051894004111c500406770006,D 0x22ba2001561c001119b000516f40041106500406750006,D 0x22ba100155f800111810005155400410ef500406740006,D 0x22ba000155d40011168000513b400410d9500406720006,D 0x22b9f00155b0001114d0005121400410c2500406700006,D 0x22b9e001558b00111330005107400410ab5004066f0006,D 0x22b9d0015566001111800050ec400410945004066d0006,D 0x22b9c001554100110fd00050d14004107c500406386004001a0007,D 0x22b9b001551b00110e200050b540041064500405d46004004b0007,D 0x22b9a00154f500110c600050994004104c500405866004007c0007,D 0x22b9900154ce00110aa000507d40041034500405ba600400ad0007,D 0x22b9800154a6001108e00050614004101b500405ed600400de0007,D 0x22b97001547e00110720005044400410035004061f6004010e0007,D 0x22b9600154540011054000502740040fe95004064d6004013f0007,D 0x22b95001542b0011037000500940040fd05004067b600401700007,D 0x22b94001540100110190004feb10040fb640040f9850040695600401a00008,D 0x22b9300153d70010ffb0004fcd10040f9c40040f3750040693600401d00008,D 0x22b9200153ab0010fdc10040fae40040eda5004068c600402010007,D 0x22b91001537f0010fbd10040f8e40040e8250040682600402310007,D 0x22b9000153520010f9e10040f6e40040e2d50040674600402610007,D 0x22b8f00153240010f7d10040f4e30040ddb40040dce50040668600402910008,D 0x22b8e00152f50010f5d10040f2d40040d6750040672600402c00007,D 0x22b8d00194ef00152c60010f3c10040f0c40040d1e5004065a600402f00008,D 0x22b8c00194c300152950010f1a10040ee940040cd75004063e600403200008,D 0x22b8b00152640010ef810040ed340040c925004061e6004034f0007,D 0x22b8a001939d001523110040ef140040c92500405bc6004037f0007,D 0x22b89001943400151fd0010eb10008e800008dfd0008df6001cdc820040dbb40040c9250040559600403ae000c,D 0x22b88001940700151c90010e8d0008e5b0008df420040dca40040c92500404f7600403c47004000d000b,D 0x22b8700193d500151930010e680008e350008dec20040dac1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004f3500c6740040c65500404c2600403c370040025000c,D 0x22b86001515b0010e42000ce0f20040de91000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005f3680c2a40040c285004049d600403c27004003d000a,D 0x22b8500151230010e1c20040e0530040bd440040bc250040492600403c1700400550009,D 0x22b8400150e90010df420040dc01000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005f3980b9240040b905004046f600403c07004006d0009,D 0x22b8300150ad0010dcc20040d9840040b5b5004047b600403a9700400820008,D 0x22b8200253a2001507020040dd240040b5b5004047b600403a9700400810008,D 0x22b810025390001503220040e8b40040b5b5004047b600403a9700400800008,D 0x22b8000253560014ff220040e9740040b5b5004047b600403a97004007f0008,D 0x22b7f0024fe40014fb020040d8130040cc340040ba45004042b600403bc7004008a0009,D 0x22b7e0024ff30014f6d0010cf430040cee40040b7b50040401600403bb700400a00009,D 0x22b7d0024fb30014f270010cc530040cbc40040b51500403d6600403b9700400b60009,D 0x22b7c002660400311950031041002cee0002ce27002cdf50034de90028ce730040c8340040b85500403d6600403b9700400b5000e,D 0x22b7b00265eb00311950030ffe002ce97002ce270034de90028caf30040c4b40040bbe500403d6600403b9700400b4000d,D 0x22b7a00265d8003119500311550030fb8002ce4c002ce270034de9002ccaf0028cae30040c4b40040bbe500403d6600403b9700400b3000f,D 0x22b7900265c500311950030fb80030fae0030f710030e27002cdff0034de930040c4b40040bbe500403d6600403b9700400b1000e,D 0x22b7800265b200311950030fb80030faf0030f710030f590030f270030e270034de930040c4b40040b84600403b5700400c1000e,D 0x22b77002566400311950030fb80030faf0030f710030f5a0030f270030f040030edb0030e270034de930040c4a40040b84600403b5700400c00010,D 0x22b7600257d100311950030fb80030fb00030f710030f5a0030f270030f040030edb0030eac0030e8c0030e270034de930040c4a40040b84600403b5700400be0012,D 0x22b75002593b00311950030fb80030fb10030f710030f5b0030f270030f040030edb0030ead0030e8c0030e540030e3b0030e270034de930040c4a40040b84600403b5700400bd0014,D 0x22b740025aa400311950030fb80030fb10030f710030f5b0030f270030f050030edb0030ead0030e8c0030e540030e3b0030e270034de930040c4a40040b84600403b5700400bb0014,D 0x22b730025c210024d6730040c5240040b84600403b5700400ba0007,D 0x22b720025d9c0024d6630040c5240040b84600403b5700400b80007,D 0x22b710025f160024d6530040c5240040b85600403b5700400b70007,D 0x22b70002608c0024d6430040c5240040b85600403b5700400b50007,D 0x22b6f00262040024d6330040c5140040b85600403b5700400b40007,D 0x22b6e00263810024d6230040c5140040b85600403b5700400b20007,D 0x22b6d00264fc0024d6130040c4f40040b87600403b5700400b00007,D 0x22b6c00264ee0024d6040040beb0024bd040040bb5600403b5700400af0008,D 0x22b6b00264db0024d5f40040beb0024bcf40040bb5600403b5700400ad0008,D 0x22b6a00264c40024d5e40040beb0024bce40040bb5600403b5700400ab0008,D 0x22b6900264ad0024d5d40040bea0024bcd40040bb5600403b5700400aa0008,D 0x22b6800264960024d5c40040bea0024bcc40040bb5600403b5700400a80008,D 0x22b67002647f0024d5b40040bea0024bcb40040bb5600403b5700400a60008,D 0x22b6600264680024d5a40040bea0024bca40040bb4600403b5700400a40008,D 0x22b6500264510024d5940040bea0024bc940040bb4600403b5700400a20008,D 0x22b6400264390024d5840040bea0024bc840040bb4600403b5700400a10008,D 0x22b6300264210024d5740040be90024bc740040bb4600403b57004009f0008,D 0x22b6200264090024d5640040be90024bc640040bb4600403b57004009d0008,D 0x22b6100263f10024d5540040be90024bc540040bb4600403b57004009b0008,D 0x22b6000263d90024d5440040be90024bc440040bb3600403b5700400990008,D 0x22b5f00263c10024d5340040be90024bc340040bb3600403b5700400960008,D 0x22b5e00263a80024d5240040be80024bc240040bb3600403b5700400940008,D 0x22b5d002638f0024d5140040be80024bc140040bb3600403b5700400910008,D 0x22b5c00263760024d5040040be80024bc040040bb2600403b57004008f0008,D 0x22b5b00258e90024d4f40040be70024bbf40040bb2600403b57004008f0008,D 0x22b5a002599b0024d4e40040be70024bbe40040bb2600403b57004008f0008,D 0x22b590025a4d0024d4d40040be70024bbd40040bb1600403b57004008f0008,D 0x22b580025afd0024d4c40040be60024bbc40040bb1600403b57004008f0008,D 0x22b570025bad0024d4b40040be60024bbb40040bb1600403b57004008f0008,D 0x22b560025c590024d4a40040be60024bba40040bb0600403b57004008f0008,D 0x22b550025d050024d4940040be50024bb940040bb0600403b5700400900008,D 0x22b540025daf0024d4840040be50024bb840040bb0600403b5700400900008,D 0x22b530025e580024d4740040be40024bb740040baf600403b5700400900008,D 0x22b520025efe0024d4640040be40024bb640040baf600403b5700400900008,D 0x22b510025fa30024d4540040be30024bb540040bae600403b5700400900008,D 0x22b5000260480024d4440040be30024bb440040bae600403b5700400900008,D 0x22b4f00260ed0024d4340040be20024bb340040bae600403b5700400900008,D 0x22b4e00261750024d4240040bd70024bb240040ba2500403c1600403b6700400910009,D 0x22b4d00261c20024d410024bb140040b78500403ea600403b6700400910008,D 0x22b4c00261d40024d400024bb040040b3150040430600403b6700400910008,D 0x22b4b00261b90024d3f0024baf40040ad45004048d600403b6700400910008,D 0x22b4a002619d0024d3e0024bae40040a79500404e8600403b6700400910008,D 0x22b4900261810024d3d0024bad40040a1d50040543600403b6700400910008,D 0x22b4800261640024d3c0024bac400409c35004059c600403b6700400910008,D 0x22b4700261470024d3b0024bab4004096a500405f5600403b6700400920008,D 0x22b46002612a0024d3a0024baa400409115004064d600403b6700400920008,D 0x22b45002610d0024d390024ba9400408b9500406a5600403b6700400920008,D 0x22b4400260e60024d380024ba840040866500406f7600403b6700400920008,D 0x22b4300260bf0024d370024ba74004081450040748600403b6700400920008,D 0x22b42002607d0024d360024ba6400407d25004078a600403b6700400930008,D 0x22b41002603b0024d350024ba5500407ae600403b6700400930007,D 0x22b400025ffa0024d340024ba4500407ad600403b6700400930007,D 0x22b3f0025fb90024d330024ba3500407ad600403b6700400930007,D 0x22b3e0025f7a0024d320024ba2500407ad600403b6700400930007,D 0x22b3d0025f3b0024d310024ba1500407ac600403b6700400930007,D 0x22b3c0025eff0024d300024ba0500407ac600403b6700400940007,D 0x22b3b0025ec30024d2f0024b9f500407ac600403b6700400940007,D 0x22b3a0025e870024d2e0024b9e500407ab600403b6700400940007,D 0x22b390025e4c0024d2d0024b9d500407ab600403b6700400940007,D 0x22b380025e120024d2c0024b9c500407aa600403b6700400950007,D 0x22b370025dd90024d2b0024b9b500407aa600403b6700400950007,D 0x22b360025da10024d2a0024b9a500407aa600403b6700400950007,D 0x22b350025d690024d290024b99500407a9600403b6700400950007,D 0x26b340024d280024b98500407a9600403b6700400950006,D 0x26b330024d270024b97500407a8600403b6700400960006,D 0x26b320024d260024b96500407a8600403b6700400960006,D 0x26b310024d250024b95500407a8600403b6700400960006,D 0x26b300024d240024b94500407a7600403b6700400960006,D 0x26b2f0024d230024b93500407a7600403b6700400970006,D 0x22b2e0025f2a0024d220024b92500407a6600403b6700400970007,D 0x22b2d002609d0024d210024b91500407a6600403b6700400970007,D 0x22b2c002625e0024d200024b90500407a5600403b6700400970007,D 0x22b2b002641b0024d1f0024b8f500407a5600403b6700400970007,D 0x22b2a00265da0024d1e0024b8e500407a4600403b6700400980007,D 0x22b2900267990024d1d0024b8d500407a4600403b6700400980007,D 0x22b2800269550024d1c0024b8c500407a3600403b6700400980007,D 0x22b270026b0a0024d1b0024b8b500407a3600403b6700400980007,D 0x26b260024d1a0024b8a500407a2600403b6700400980006,D 0x26b250024d190024b89500407a2600403b6700400980006,D 0x26b240024d180024b88500407a1600403b6700400980006,D 0x26b230024d170024b8750040794600403c3700400990006,D 0x26b220024d160024b865004077c600403da700400990006,D 0x26b210024d150024b8550040764600403f1700400990006,D 0x26b200024d140024b8450040764600403f0700400990006,D 0x26b1f0024d130024b8350040765600403f0700400990006,D 0x26b1e0024d120024b8250040765600403ef700400990006,D 0x26b1d0024d110024b8150040765600403ee7004009a0006,D 0x26b1c0024d100024b8050040765600403ee7004009a0006,D 0x22b1b00260cc0024d0f0024b7f50040765600403ed7004009a0007,D 0x22b1a00261d20024d0e0024b7e50040765600403ed7004009a0007,D 0x22b1900262d20024d0d0024b7d50040765600403ec7004009a0007,D 0x22b1800263d30024d0c0024b7c50040765600403eb7004009a0007,D 0x22b1700264d20024d0b0024b7b50040765600403eb7004009b0007,D 0x22b1600265d00024d0a0024b7a50040765600403ea7004009b0007,D 0x22b1500266c90024d090024b7950040765600403e97004009b0007,D 0x22b1400267c30024d080024b7850040765600403e97004009b0007,D 0x22b1300268bd0024d070024b7750040765600403e87004009b0007,D 0x22b1200269b60024d060024b7650040765600403e77004009b0007,D 0x22b110026aac0024d050024b7550040765600403e67004009c0007,D 0x26b100024d040024b7450040765600403e67004009c0006,D 0x26b0f0024d030024b7350040765600403e57004009c0006,D 0x26b0e0024d020024b7250040765600403e47004009c0006,D 0x26b0d0024d010024b7150040766600403e37004009c0006,D 0x26b0c0024d000024b7050040766600403e37004009c0006,D 0x26b0b0024cff0024b6f50040766600403e27004009d0006,D 0x26b0a0024cfe0024b6e50040766600403e17004009d0006,D 0x26b090024cfd0024b6d50040766600403e17004009d0006,D 0x26b080024cfc0024b6c50040766600403e17004009c0006,D 0x26b070024cfb0024b6b50040766600403e17004009c0006,D 0x26b060024cfa0024b6a50040766600403e17004009c0006,D 0x26b050024cf90024b6950040766600403e17004009b0006,D 0x26b040024cf80024b6850040766600403e17004009b0006,D 0x26b030024cf70024b6750040766600403e17004009b0006][v]?).getD []
private abbrev C (v : ℕ) : List Piece := FinalLedgerData6815.row 16 v
private def nb (v : ℕ) : ℕ := (#[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,1,1,1,1,2,2,2,2,2,2,2,2,2,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1][v]?).getD 0
private def H : List ℕ := [34,35,37,45,46,47,48,49,50,51,52,53]
private def ok (v : ℕ) : Bool := if v∈H ∨ 167≤v then true else rowL 16 v (C v) (row v) (nb v)
private abbrev I (v i : ℕ) : Prop := indexL 16 v (C v) (row v) i=true
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
private theorem a34_0 : I 34 0 := by decide +kernel
private theorem a34_1 : I 34 1 := by decide +kernel
private theorem a34_2 : I 34 2 := by decide +kernel
private theorem a34_3 : I 34 3 := by decide +kernel
private theorem a34_4 : I 34 4 := by decide +kernel
private theorem a34_5 : I 34 5 := by decide +kernel
private theorem a34_6 : I 34 6 := by decide +kernel
private theorem a34_7 : I 34 7 := by decide +kernel
private theorem h34 : checkRow 16 34 (C 34) (row 34)=true := row_of_blocks 16 34 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 16 34 _ _ 0 (by decide) (by decide) a34_0 a34_1 a34_2 a34_3 a34_4 a34_5 a34_6 a34_7)) (blk 16 34 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a35_0 : I 35 0 := by decide +kernel
private theorem a35_1 : I 35 1 := by decide +kernel
private theorem a35_2 : I 35 2 := by decide +kernel
private theorem a35_3 : I 35 3 := by decide +kernel
private theorem a35_4 : I 35 4 := by decide +kernel
private theorem a35_5 : I 35 5 := by decide +kernel
private theorem a35_6 : I 35 6 := by decide +kernel
private theorem a35_7 : I 35 7 := by decide +kernel
private theorem h35 : checkRow 16 35 (C 35) (row 35)=true := row_of_blocks 16 35 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 16 35 _ _ 0 (by decide) (by decide) a35_0 a35_1 a35_2 a35_3 a35_4 a35_5 a35_6 a35_7)) (blk 16 35 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a37_0 : I 37 0 := by decide +kernel
private theorem a37_1 : I 37 1 := by decide +kernel
private theorem a37_2 : I 37 2 := by decide +kernel
private theorem a37_3 : I 37 3 := by decide +kernel
private theorem a37_4 : I 37 4 := by decide +kernel
private theorem a37_5 : I 37 5 := by decide +kernel
private theorem a37_6 : I 37 6 := by decide +kernel
private theorem a37_7 : I 37 7 := by decide +kernel
private theorem h37 : checkRow 16 37 (C 37) (row 37)=true := row_of_blocks 16 37 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 16 37 _ _ 0 (by decide) (by decide) a37_0 a37_1 a37_2 a37_3 a37_4 a37_5 a37_6 a37_7)) (blk 16 37 _ _ 1 (by decide) (by decide) (by decide +kernel)))
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
private theorem h45 : checkRow 16 45 (C 45) (row 45)=true := row_of_blocks 16 45 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 16 45 _ _ 0 (by decide) (by decide) a45_0 a45_1 a45_2 a45_3 a45_4 a45_5 a45_6 a45_7)) (blk8 16 45 _ _ 1 (by decide) (by decide) a45_8 a45_9 a45_10 a45_11 a45_12 a45_13 a45_14 a45_15))
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
private theorem h46 : checkRow 16 46 (C 46) (row 46)=true := row_of_blocks 16 46 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 16 46 _ _ 0 (by decide) (by decide) a46_0 a46_1 a46_2 a46_3 a46_4 a46_5 a46_6 a46_7)) (blk8 16 46 _ _ 1 (by decide) (by decide) a46_8 a46_9 a46_10 a46_11 a46_12 a46_13 a46_14 a46_15))
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
private theorem h47 : checkRow 16 47 (C 47) (row 47)=true := row_of_blocks 16 47 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 16 47 _ _ 0 (by decide) (by decide) a47_0 a47_1 a47_2 a47_3 a47_4 a47_5 a47_6 a47_7)) (blk8 16 47 _ _ 1 (by decide) (by decide) a47_8 a47_9 a47_10 a47_11 a47_12 a47_13 a47_14 a47_15))
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
private theorem h48 : checkRow 16 48 (C 48) (row 48)=true := row_of_blocks 16 48 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 16 48 _ _ 0 (by decide) (by decide) a48_0 a48_1 a48_2 a48_3 a48_4 a48_5 a48_6 a48_7)) (blk8 16 48 _ _ 1 (by decide) (by decide) a48_8 a48_9 a48_10 a48_11 a48_12 a48_13 a48_14 a48_15))
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
private theorem h49 : checkRow 16 49 (C 49) (row 49)=true := row_of_blocks 16 49 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 16 49 _ _ 0 (by decide) (by decide) a49_0 a49_1 a49_2 a49_3 a49_4 a49_5 a49_6 a49_7)) (blk8 16 49 _ _ 1 (by decide) (by decide) a49_8 a49_9 a49_10 a49_11 a49_12 a49_13 a49_14 a49_15))
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
private theorem h50 : checkRow 16 50 (C 50) (row 50)=true := row_of_blocks 16 50 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 16 50 _ _ 0 (by decide) (by decide) a50_0 a50_1 a50_2 a50_3 a50_4 a50_5 a50_6 a50_7)) (blk8 16 50 _ _ 1 (by decide) (by decide) a50_8 a50_9 a50_10 a50_11 a50_12 a50_13 a50_14 a50_15))
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
private theorem h51 : checkRow 16 51 (C 51) (row 51)=true := row_of_blocks 16 51 _ _ 3 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 2 (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 16 51 _ _ 0 (by decide) (by decide) a51_0 a51_1 a51_2 a51_3 a51_4 a51_5 a51_6 a51_7)) (blk8 16 51 _ _ 1 (by decide) (by decide) a51_8 a51_9 a51_10 a51_11 a51_12 a51_13 a51_14 a51_15)) (blk 16 51 _ _ 2 (by decide) (by decide) (by decide +kernel)))
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
private theorem a52_16 : I 52 16 := by decide +kernel
private theorem a52_17 : I 52 17 := by decide +kernel
private theorem a52_18 : I 52 18 := by decide +kernel
private theorem a52_19 : I 52 19 := by decide +kernel
private theorem a52_20 : I 52 20 := by decide +kernel
private theorem a52_21 : I 52 21 := by decide +kernel
private theorem a52_22 : I 52 22 := by decide +kernel
private theorem a52_23 : I 52 23 := by decide +kernel
private theorem h52 : checkRow 16 52 (C 52) (row 52)=true := row_of_blocks 16 52 _ _ 3 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 2 (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 16 52 _ _ 0 (by decide) (by decide) a52_0 a52_1 a52_2 a52_3 a52_4 a52_5 a52_6 a52_7)) (blk8 16 52 _ _ 1 (by decide) (by decide) a52_8 a52_9 a52_10 a52_11 a52_12 a52_13 a52_14 a52_15)) (blk8 16 52 _ _ 2 (by decide) (by decide) a52_16 a52_17 a52_18 a52_19 a52_20 a52_21 a52_22 a52_23))
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
private theorem a53_16 : I 53 16 := by decide +kernel
private theorem a53_17 : I 53 17 := by decide +kernel
private theorem a53_18 : I 53 18 := by decide +kernel
private theorem a53_19 : I 53 19 := by decide +kernel
private theorem a53_20 : I 53 20 := by decide +kernel
private theorem a53_21 : I 53 21 := by decide +kernel
private theorem a53_22 : I 53 22 := by decide +kernel
private theorem a53_23 : I 53 23 := by decide +kernel
private theorem h53 : checkRow 16 53 (C 53) (row 53)=true := row_of_blocks 16 53 _ _ 3 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 2 (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 16 53 _ _ 0 (by decide) (by decide) a53_0 a53_1 a53_2 a53_3 a53_4 a53_5 a53_6 a53_7)) (blk8 16 53 _ _ 1 (by decide) (by decide) a53_8 a53_9 a53_10 a53_11 a53_12 a53_13 a53_14 a53_15)) (blk8 16 53 _ _ 2 (by decide) (by decide) a53_16 a53_17 a53_18 a53_19 a53_20 a53_21 a53_22 a53_23))
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
theorem checked (v : ℕ) (hv : v≤166) : checkRow 16 v (FinalLedgerData6815.row 16 v) (row v)=true := by
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
  have hH : ¬(v∈H ∨ 167≤v) := by simp only [H,List.mem_cons,List.not_mem_nil,or_false,false_or]; omega
  have h := okAt v (by omega)
  simp only [ok,if_neg hH] at h
  exact row_of_rowL 16 v _ _ (nb v) (by omega) (by omega) h
end ProximityPrize.SubmissionLower.FinalRulesRows6815_R16
