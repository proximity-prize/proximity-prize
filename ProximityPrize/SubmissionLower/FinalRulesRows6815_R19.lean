import ProximityPrize.SubmissionLower.MergedInfra6815_54
namespace ProximityPrize.SubmissionLower.FinalRulesRows6815_R19
open FinalCurves6815 FinalRulesRowCheck6815 FinalRulesCached6815 FinalRulesCompact6815 SingletonCertificate6815 CompactAllN6815
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private abbrev D : ℕ → List Piece := FinalRulesRowCheck6815.decode
def row (v : ℕ) : List Piece := (#[D 0x22ba600153f20011034000d0020008fd5001cfcd10040f60f0040dbe40040dbc50040bcb000a,D 0x22ba500153c900110180008fe50008fc90008fa3001cf9210040f6bf0040d4c40040d4a50040c3d000b,D 0x22ba4001539f0010ffb0008fc80008fb710040f7af0040d4c40040d4a50040c3d0009,D 0x22ba300153750010fdd10040faaf0040d4c40040d4a50040c3d0007,D 0x22ba2001534a0010fc010040f8cf0040d4c40040d4a50040c3d0007,D 0x22ba1001531e0010fa210040f6df0040d4c40040d4a50040c3c0007,D 0x22ba000152f20010f8310040f52f0040d4c40040d4a50040c3a0007,D 0x22b9f00152c510040f64f0040d4c40040d4a50040c380006,D 0x22b9e001529710040f54f0040d4c40040d4a50040c196004000f0007,D 0x22b9d00152690010f25000ceef20040e4ef0040d4c40040d4a50040ba16004004a0009,D 0x22b9c001523a0010f04000cece20040e63f0040d4c40040d4a50040b2a600400850009,D 0x22b9b001520a0010ee4000cead20040e77f0040d4c40040d4a50040ab2600400bf0009,D 0x22b9a00151da0010ec220040e8b10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f1b00d4c40040d4a50040a3b600400fa0008,D 0x22b9900151a90010ea020040e691000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f1d00d4c40040d4a50040a126004010d0008,D 0x22b98001918f00151770010e7e20040e46100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f1f00d4c40040d4a50040a126004010b0009,D 0x22b97001918e00151440010e5b20040e3421000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f2100d4c40040d4a500409a86004013f0009,D 0x22b96001918d001511020040e372100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f2300d4c40040d4a50040937600401760008,D 0x22b95001918b00150dc20040e35210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f2500d4c40040d4a500408c7600401ad0008,D 0x22b94001918a00150a720040e3932000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f2700d4c40040d4a50040856600401e30008,D 0x22b930019189001507120040e3e3200000000000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f2900d4c40040d4a500407e66004021a0008,D 0x22b920019188001503a20040e42320000000000000000000210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f2b00d4c40040d4a50040776600402500008,D 0x22b910019187001500220040e4733000000000000000000002200000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002f2d00d4c40040d4a50040706600402860008,D 0x22b9000191850014fc930040dc840040d4a50040696600402bc0007,D 0x22b8f00191840014f8f30040dca40040d4a50040696600402bb0007,D 0x22b8e00191830014f5530040dcc40040d4a50040696600402b90007,D 0x22b8d00191de0014f1930040dce40040d4a50040650600402d7700400020008,D 0x22b8c00191a70014edc30040dd140040d4a500405e760040305700400040008,D 0x22b8b001916e0014e9e30040dd840040d4a5004057e60040332700400070008,D 0x22b8a0018fa40014ecc30040db840040d1e5004054460040360700400090008,D 0x22b890018f5d0018f480014e6d30040d7940040cd7500405226004038e7004000b0009,D 0x22b8800190bd0014dde30040d4140040c92500404fd600403bc7004000d0008,D 0x22b8700190800014d9c30040d4340040c92500404fd600403997004001d0008,D 0x22b8600191950014e1f30040d4740040c92500404fd60040390700400210008,D 0x22b8500191950014de530040d4f40040c92500404f7600403937004001f0008,D 0x22b84002535330040d2a40040c65500404c2600403c37004001f0007,D 0x22b83002533b30040d2240040c285004049d600403c2700400370007,D 0x22b82002532930040d0140040bc250040492600403c17004004f0007,D 0x22b81002530d30040cbc40040b905004046f600403c0700400660007,D 0x22b8000252f130040c8c40040b5b5004047b600403a97004007b0007,D 0x22b7f00250eb30040ca940040b5b5004047c600403a9700400790007,D 0x22b7e002547930040cfe40040b5b5004047b600403a9700400780007,D 0x22b7d002565430040d0140040b5b5004047c600403a9700400760007,D 0x22b7c00256ac0024d7030040d1d40040ba45004042b600403bc700400820008,D 0x22b7b00256690024d6f30040cf140040b7b50040401600403bb700400980008,D 0x22b7a00256230024d6e30040cbf40040b51500403d6600403b9700400ae0008,D 0x22b7900262280024d6d30040c8a40040b86500403d6600403b9700400ac0008,D 0x22b7800262c80024d6c30040c5140040bbe500403d6600403b9700400aa0008,D 0x22b7700263d60024d6b30040c5140040bbe500403d6600403b9700400a90008,D 0x22b7600264c80024d6a30040c0d40040c080024bda40040bd5500403d6600403b9700400a7000a,D 0x22b7500264d30024d6940040bee0024bd940040bb8600403b5700400b70008,D 0x22b7400264bd0024d6840040bee0024bd840040bb8600403b5700400b50008,D 0x22b7300264a60024d6740040bee0024bd740040bb8600403b5700400b30008,D 0x22b7200264900024d6640040bee0024bd640040bb8600403b5700400b10008,D 0x22b7100264790024d6540040bee0024bd540040bb8600403b5700400b00008,D 0x22b7000264630024d6440040bee0024bd440040bb8600403b5700400ae0008,D 0x22b6f002644c0024d6340040bee0024bd340040bb8600403b5700400ac0008,D 0x22b6e00264360024d6240040bed0024bd240040bb8600403b5700400aa0008,D 0x22b6d002641f0024d6140040bed0024bd140040bb8600403b5700400a80008,D 0x22b6c00264080024d6040040bed0024bd040040bb8600403b5700400a60008,D 0x22b6b00263f10024d5f40040bed0024bcf40040bb7600403b5700400a30008,D 0x22b6a00263d90024d5e40040bec0024bce40040bb7600403b5700400a10008,D 0x22b6900263c10024d5d40040bec0024bcd40040bb7600403b57004009e0008,D 0x22b6800263ab0024d5c40040bec0024bcc40040bb6600403b57004009b0008,D 0x22b6700263930024d5b40040beb0024bcb40040bb6600403b5700400980008,D 0x22b66002637b0024d5a40040beb0024bca40040bb6600403b5700400960008,D 0x22b6500263630024d5940040beb0024bc940040bb5600403b5700400930008,D 0x22b64002634a0024d5840040bea0024bc840040bb5600403b5700400900008,D 0x22b6300263320024d5740040bea0024bc740040bb4600403b5700400900008,D 0x22b620025c7a0024d5640040be90024bc640040bb4600403b5700400910008,D 0x22b610025d410024d5540040be90024bc540040bb4600403b5700400910008,D 0x22b600025e070024d5440040be80024bc440040bb3600403b57004008f0008,D 0x22b5f0025ecc0024d5340040be70024bc340040bb2600403b57004008f0008,D 0x22b5e0025f900024d5240040be70024bc240040bb2600403b57004008f0008,D 0x22b5d002601b0024d5140040bcb0024bc140040b96500403d0600403b67004008f0009,D 0x22b5c00260940024d500024bc040040b73500403f3600403b6700400900008,D 0x22b5b002610d0024d4f0024bbf40040b4f50040417600403b6700400900008,D 0x22b5a00261830024d4e0024bbe40040b2b5004043a600403b6700400900008,D 0x22b5900261f60024d4d0024bbd40040b075004045c600403b6700400900008,D 0x22b58002621f0024d4c0024bbc40040ac1500404a2600403b6700400900008,D 0x22b5700262050024d4b0024bbb40040a5a50040509600403b6700400910008,D 0x22b5600261eb0024d4a0024bba400409f45004056e600403b6700400910008,D 0x22b5500261d10024d490024bb94004098f500405d1600403b6700400910008,D 0x22b5400261ae0024d480024bb84004093050040630600403b6700400910008,D 0x22b5300261790024d470024bb7400408d05004068f600403b6700400920008,D 0x22b52002612a0024d460024bb640040881500406dd600403b6700400920008,D 0x22b5100260dd0024d450024bb54004083450040729600403b6700400920008,D 0x22b5000260930024d440024bb4400407e950040773600403b6700400920008,D 0x22b4f00260480024d430024bb3500407ad600403b6700400920007,D 0x22b4e00260000024d420024bb2500407ad600403b6700400930007,D 0x22b4d0025fb70024d410024bb1500407ac600403b6700400930007,D 0x22b4c0025f720024d400024bb0500407ac600403b6700400930007,D 0x22b4b0025f2d0024d3f0024baf500407ab600403b6700400940007,D 0x22b4a00268670024d3e0024bae500407ab600403b6700400940007,D 0x22b490026a8f0024d3d0024bad500407aa600403b6700400940007,D 0x26b480024d3c0024bac500407a9600403b6700400940006,D 0x26b470024d3b0024bab500407a9600403b6700400950006,D 0x26b460024d3a0024baa500407a8600403b6700400950006,D 0x26b450024d390024ba9500407a7600403b6700400950006,D 0x26b440024d380024ba8500407a7600403b6700400950006,D 0x26b430024d370024ba7500407a6600403b6700400960006,D 0x26b420024d360024ba6500407a5600403b6700400960006,D 0x26b410024d350024ba5500407a5600403b6700400960006,D 0x26b400024d340024ba4500407a4600403b6700400970006,D 0x26b3f0024d330024ba3500407a3600403b6700400970006,D 0x26b3e0024d320024ba2500407a2600403b6700400970006,D 0x26b3d0024d310024ba1500407a2600403b6700400980006,D 0x26b3c0024d300024ba0500407a1600403b6700400980006,D 0x22b3b00261670024d2f0024b9f5004079c600403b9700400980007,D 0x22b3a00262ff0024d2e0024b9e50040784600403d0700400990007,D 0x22b3900264a60024d2d0024b9d5004076c600403e8700400990007,D 0x22b3800266990024d2c0024b9c50040754600403ff700400990007,D 0x22b3700268540024d2b0024b9b5004073c600404167004009a0007,D 0x22b360026a420024d2a0024b9a500407246004042d7004009a0007,D 0x26b350024d290024b995004070c600404447004009a0006,D 0x26b340024d280024b98500406f46004045b7004009b0006,D 0x26b330024d270024b97500406dc600404727004009b0006,D 0x26b320024d260024b96500406c4600404897004009c0006,D 0x26b310024d250024b95500406ac600404a07004009c0006,D 0x26b300024d240024b9450040691600404ba7004009c0006,D 0x26b2f0024d230024b9350040676600404d47004009d0006,D 0x26b2e0024d220024b925004065b600404ee7004009d0006,D 0x26b2d0024d210024b9150040640600405087004009d0006,D 0x26b2c0024d200024b9050040626600405227004009e0006,D 0x26b2b0024d1f0024b8f5004060b6004053c7004009e0006,D 0x26b2a0024d1e0024b8e500405f0600405567004009e0006,D 0x26b290024d1d0024b8d500405d56004056f7004009f0006,D 0x26b280024d1c0024b8c500405ba600405897004009f0006,D 0x22b2700263e60024d1b0024b8b600405a17004009f0006,D 0x22b26002650f0024d1a0024b8a600405a1700400a00006,D 0x22b2500266340024d190024b89600405a0700400a00006,D 0x22b2400267590024d180024b8800245a1500405a06004059f700400a10008,D 0x22b23002687b0024d170024b87500405a06004059e700400a10007,D 0x22b22002699e0024d160024b86500405a06004059d700400a10007,D 0x22b210026abf0024d150024b85500405a06004059b700400a20007,D 0x26b200024d140024b84500405a06004059a700400a20006,D 0x26b1f0024d130024b83500405a060040599700400a30006,D 0x26b1e0024d120024b82500405a060040597700400a30006,D 0x26b1d0024d110024b81500405a060040596700400a30006,D 0x26b1c0024d100024b80500405a060040595700400a40006,D 0x26b1b0024d0f0024b7f500405a060040594700400a40006,D 0x26b1a0024d0e0024b7e500405a060040592700400a50006,D 0x22b190026b0d0024d0d0024b7d500405a060040591700400a50007,D 0x22b180026ace0024d0c0024b7c500405a16004058f700400a50007,D 0x22b170026a900024d0b0024b7b500405a16004058e700400a50007,D 0x22b160026a520024d0a0024b7a500405a16004058d700400a60007,D 0x22b150026a140024d090024b79500405a16004058b700400a60007,D 0x22b1400269d60024d080024b78500405a16004058a700400a60007,D 0x22b1300269980024d070024b77500405a160040588700400a60007,D 0x22b1200269590024d060024b76500405a160040587700400a70007,D 0x22b11002691b0024d050024b75500405a160040585700400a70007,D 0x22b1000268dd0024d040024b74500405a160040584700400a70007,D 0x22b0f002689f0024d030024b73500405a160040582700400a70007,D 0x22b0e00268610024d020024b72500405a160040581700400a80007,D 0x22b0d00268230024d010024b71500405a16004057f700400a80007,D 0x22b0c00267e40024d000024b70500405a16004057f700400a70007,D 0x22b0b00267a60024cff0024b6f500405a16004057f700400a70007,D 0x22b0a00267680024cfe0024b6e500405a16004057f700400a60007,D 0x22b09002672a0024cfd0024b6d500405a16004057f700400a60007,D 0x22b0800266ec0024cfc0024b6c500405a16004057f700400a50007,D 0x26b0700266ad0024cfb0024b6b500405a26004057f700400a40007,D 0x26b06002666f0024cfa0024b6a500405a26004057f700400a30007,D 0x26b0500266310024cf90024b69500405a26004057f700400a30007,D 0x26b0400265f30024cf80024b68500405a26004057f700400a20007,D 0x26b0300265b50024cf70024b67500405a26004057f700400a10007][v]?).getD []
private abbrev C (v : ℕ) : List Piece := FinalLedgerData6815.row 19 v
private def nb (v : ℕ) : ℕ := (#[2,2,2,1,1,1,1,1,1,2,2,2,1,1,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1][v]?).getD 0
private def H : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
private def ok (v : ℕ) : Bool := if v∈H ∨ 164≤v then true else rowL 19 v (C v) (row v) (nb v)
private abbrev I (v i : ℕ) : Prop := indexL 19 v (C v) (row v) i=true
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
private theorem a0_0 : I 0 0 := by decide +kernel
private theorem a0_1 : I 0 1 := by decide +kernel
private theorem a0_2 : I 0 2 := by decide +kernel
private theorem a0_3 : I 0 3 := by decide +kernel
private theorem a0_4 : I 0 4 := by decide +kernel
private theorem a0_5 : I 0 5 := by decide +kernel
private theorem a0_6 : I 0 6 := by decide +kernel
private theorem a0_7 : I 0 7 := by decide +kernel
private theorem h0 : checkRow 19 0 (C 0) (row 0)=true := row_of_blocks 19 0 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 19 0 _ _ 0 (by decide) (by decide) a0_0 a0_1 a0_2 a0_3 a0_4 a0_5 a0_6 a0_7)) (blk 19 0 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a1_0 : I 1 0 := by decide +kernel
private theorem a1_1 : I 1 1 := by decide +kernel
private theorem a1_2 : I 1 2 := by decide +kernel
private theorem a1_3 : I 1 3 := by decide +kernel
private theorem a1_4 : I 1 4 := by decide +kernel
private theorem a1_5 : I 1 5 := by decide +kernel
private theorem a1_6 : I 1 6 := by decide +kernel
private theorem a1_7 : I 1 7 := by decide +kernel
private theorem h1 : checkRow 19 1 (C 1) (row 1)=true := row_of_blocks 19 1 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 19 1 _ _ 0 (by decide) (by decide) a1_0 a1_1 a1_2 a1_3 a1_4 a1_5 a1_6 a1_7)) (blk 19 1 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a2_0 : I 2 0 := by decide +kernel
private theorem a2_1 : I 2 1 := by decide +kernel
private theorem a2_2 : I 2 2 := by decide +kernel
private theorem a2_3 : I 2 3 := by decide +kernel
private theorem a2_4 : I 2 4 := by decide +kernel
private theorem a2_5 : I 2 5 := by decide +kernel
private theorem a2_6 : I 2 6 := by decide +kernel
private theorem a2_7 : I 2 7 := by decide +kernel
private theorem h2 : checkRow 19 2 (C 2) (row 2)=true := row_of_blocks 19 2 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 19 2 _ _ 0 (by decide) (by decide) a2_0 a2_1 a2_2 a2_3 a2_4 a2_5 a2_6 a2_7)) (blk 19 2 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a3_0 : I 3 0 := by decide +kernel
private theorem a3_1 : I 3 1 := by decide +kernel
private theorem a3_2 : I 3 2 := by decide +kernel
private theorem a3_3 : I 3 3 := by decide +kernel
private theorem a3_4 : I 3 4 := by decide +kernel
private theorem a3_5 : I 3 5 := by decide +kernel
private theorem a3_6 : I 3 6 := by decide +kernel
private theorem a3_7 : I 3 7 := by decide +kernel
private theorem h3 : checkRow 19 3 (C 3) (row 3)=true := row_of_blocks 19 3 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 3 _ _ 0 (by decide) (by decide) a3_0 a3_1 a3_2 a3_3 a3_4 a3_5 a3_6 a3_7))
private theorem a4_0 : I 4 0 := by decide +kernel
private theorem a4_1 : I 4 1 := by decide +kernel
private theorem a4_2 : I 4 2 := by decide +kernel
private theorem a4_3 : I 4 3 := by decide +kernel
private theorem a4_4 : I 4 4 := by decide +kernel
private theorem a4_5 : I 4 5 := by decide +kernel
private theorem a4_6 : I 4 6 := by decide +kernel
private theorem a4_7 : I 4 7 := by decide +kernel
private theorem h4 : checkRow 19 4 (C 4) (row 4)=true := row_of_blocks 19 4 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 4 _ _ 0 (by decide) (by decide) a4_0 a4_1 a4_2 a4_3 a4_4 a4_5 a4_6 a4_7))
private theorem a5_0 : I 5 0 := by decide +kernel
private theorem a5_1 : I 5 1 := by decide +kernel
private theorem a5_2 : I 5 2 := by decide +kernel
private theorem a5_3 : I 5 3 := by decide +kernel
private theorem a5_4 : I 5 4 := by decide +kernel
private theorem a5_5 : I 5 5 := by decide +kernel
private theorem a5_6 : I 5 6 := by decide +kernel
private theorem a5_7 : I 5 7 := by decide +kernel
private theorem h5 : checkRow 19 5 (C 5) (row 5)=true := row_of_blocks 19 5 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 5 _ _ 0 (by decide) (by decide) a5_0 a5_1 a5_2 a5_3 a5_4 a5_5 a5_6 a5_7))
private theorem a6_0 : I 6 0 := by decide +kernel
private theorem a6_1 : I 6 1 := by decide +kernel
private theorem a6_2 : I 6 2 := by decide +kernel
private theorem a6_3 : I 6 3 := by decide +kernel
private theorem a6_4 : I 6 4 := by decide +kernel
private theorem a6_5 : I 6 5 := by decide +kernel
private theorem a6_6 : I 6 6 := by decide +kernel
private theorem a6_7 : I 6 7 := by decide +kernel
private theorem h6 : checkRow 19 6 (C 6) (row 6)=true := row_of_blocks 19 6 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 6 _ _ 0 (by decide) (by decide) a6_0 a6_1 a6_2 a6_3 a6_4 a6_5 a6_6 a6_7))
private theorem a7_0 : I 7 0 := by decide +kernel
private theorem a7_1 : I 7 1 := by decide +kernel
private theorem a7_2 : I 7 2 := by decide +kernel
private theorem a7_3 : I 7 3 := by decide +kernel
private theorem a7_4 : I 7 4 := by decide +kernel
private theorem a7_5 : I 7 5 := by decide +kernel
private theorem a7_6 : I 7 6 := by decide +kernel
private theorem a7_7 : I 7 7 := by decide +kernel
private theorem h7 : checkRow 19 7 (C 7) (row 7)=true := row_of_blocks 19 7 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 7 _ _ 0 (by decide) (by decide) a7_0 a7_1 a7_2 a7_3 a7_4 a7_5 a7_6 a7_7))
private theorem a8_0 : I 8 0 := by decide +kernel
private theorem a8_1 : I 8 1 := by decide +kernel
private theorem a8_2 : I 8 2 := by decide +kernel
private theorem a8_3 : I 8 3 := by decide +kernel
private theorem a8_4 : I 8 4 := by decide +kernel
private theorem a8_5 : I 8 5 := by decide +kernel
private theorem a8_6 : I 8 6 := by decide +kernel
private theorem a8_7 : I 8 7 := by decide +kernel
private theorem h8 : checkRow 19 8 (C 8) (row 8)=true := row_of_blocks 19 8 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 8 _ _ 0 (by decide) (by decide) a8_0 a8_1 a8_2 a8_3 a8_4 a8_5 a8_6 a8_7))
private theorem a9_0 : I 9 0 := by decide +kernel
private theorem a9_1 : I 9 1 := by decide +kernel
private theorem a9_2 : I 9 2 := by decide +kernel
private theorem a9_3 : I 9 3 := by decide +kernel
private theorem a9_4 : I 9 4 := by decide +kernel
private theorem a9_5 : I 9 5 := by decide +kernel
private theorem a9_6 : I 9 6 := by decide +kernel
private theorem a9_7 : I 9 7 := by decide +kernel
private theorem h9 : checkRow 19 9 (C 9) (row 9)=true := row_of_blocks 19 9 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 19 9 _ _ 0 (by decide) (by decide) a9_0 a9_1 a9_2 a9_3 a9_4 a9_5 a9_6 a9_7)) (blk 19 9 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a10_0 : I 10 0 := by decide +kernel
private theorem a10_1 : I 10 1 := by decide +kernel
private theorem a10_2 : I 10 2 := by decide +kernel
private theorem a10_3 : I 10 3 := by decide +kernel
private theorem a10_4 : I 10 4 := by decide +kernel
private theorem a10_5 : I 10 5 := by decide +kernel
private theorem a10_6 : I 10 6 := by decide +kernel
private theorem a10_7 : I 10 7 := by decide +kernel
private theorem h10 : checkRow 19 10 (C 10) (row 10)=true := row_of_blocks 19 10 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 19 10 _ _ 0 (by decide) (by decide) a10_0 a10_1 a10_2 a10_3 a10_4 a10_5 a10_6 a10_7)) (blk 19 10 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a11_0 : I 11 0 := by decide +kernel
private theorem a11_1 : I 11 1 := by decide +kernel
private theorem a11_2 : I 11 2 := by decide +kernel
private theorem a11_3 : I 11 3 := by decide +kernel
private theorem a11_4 : I 11 4 := by decide +kernel
private theorem a11_5 : I 11 5 := by decide +kernel
private theorem a11_6 : I 11 6 := by decide +kernel
private theorem a11_7 : I 11 7 := by decide +kernel
private theorem h11 : checkRow 19 11 (C 11) (row 11)=true := row_of_blocks 19 11 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 19 11 _ _ 0 (by decide) (by decide) a11_0 a11_1 a11_2 a11_3 a11_4 a11_5 a11_6 a11_7)) (blk 19 11 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a12_0 : I 12 0 := by decide +kernel
private theorem a12_1 : I 12 1 := by decide +kernel
private theorem a12_2 : I 12 2 := by decide +kernel
private theorem a12_3 : I 12 3 := by decide +kernel
private theorem a12_4 : I 12 4 := by decide +kernel
private theorem a12_5 : I 12 5 := by decide +kernel
private theorem a12_6 : I 12 6 := by decide +kernel
private theorem a12_7 : I 12 7 := by decide +kernel
private theorem h12 : checkRow 19 12 (C 12) (row 12)=true := row_of_blocks 19 12 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 12 _ _ 0 (by decide) (by decide) a12_0 a12_1 a12_2 a12_3 a12_4 a12_5 a12_6 a12_7))
private theorem a13_0 : I 13 0 := by decide +kernel
private theorem a13_1 : I 13 1 := by decide +kernel
private theorem a13_2 : I 13 2 := by decide +kernel
private theorem a13_3 : I 13 3 := by decide +kernel
private theorem a13_4 : I 13 4 := by decide +kernel
private theorem a13_5 : I 13 5 := by decide +kernel
private theorem a13_6 : I 13 6 := by decide +kernel
private theorem a13_7 : I 13 7 := by decide +kernel
private theorem h13 : checkRow 19 13 (C 13) (row 13)=true := row_of_blocks 19 13 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 13 _ _ 0 (by decide) (by decide) a13_0 a13_1 a13_2 a13_3 a13_4 a13_5 a13_6 a13_7))
private theorem a14_0 : I 14 0 := by decide +kernel
private theorem a14_1 : I 14 1 := by decide +kernel
private theorem a14_2 : I 14 2 := by decide +kernel
private theorem a14_3 : I 14 3 := by decide +kernel
private theorem a14_4 : I 14 4 := by decide +kernel
private theorem a14_5 : I 14 5 := by decide +kernel
private theorem a14_6 : I 14 6 := by decide +kernel
private theorem a14_7 : I 14 7 := by decide +kernel
private theorem h14 : checkRow 19 14 (C 14) (row 14)=true := row_of_blocks 19 14 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 19 14 _ _ 0 (by decide) (by decide) a14_0 a14_1 a14_2 a14_3 a14_4 a14_5 a14_6 a14_7)) (blk 19 14 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a15_0 : I 15 0 := by decide +kernel
private theorem a15_1 : I 15 1 := by decide +kernel
private theorem a15_2 : I 15 2 := by decide +kernel
private theorem a15_3 : I 15 3 := by decide +kernel
private theorem a15_4 : I 15 4 := by decide +kernel
private theorem a15_5 : I 15 5 := by decide +kernel
private theorem a15_6 : I 15 6 := by decide +kernel
private theorem a15_7 : I 15 7 := by decide +kernel
private theorem h15 : checkRow 19 15 (C 15) (row 15)=true := row_of_blocks 19 15 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 19 15 _ _ 0 (by decide) (by decide) a15_0 a15_1 a15_2 a15_3 a15_4 a15_5 a15_6 a15_7)) (blk 19 15 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a16_0 : I 16 0 := by decide +kernel
private theorem a16_1 : I 16 1 := by decide +kernel
private theorem a16_2 : I 16 2 := by decide +kernel
private theorem a16_3 : I 16 3 := by decide +kernel
private theorem a16_4 : I 16 4 := by decide +kernel
private theorem a16_5 : I 16 5 := by decide +kernel
private theorem a16_6 : I 16 6 := by decide +kernel
private theorem a16_7 : I 16 7 := by decide +kernel
private theorem h16 : checkRow 19 16 (C 16) (row 16)=true := row_of_blocks 19 16 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 16 _ _ 0 (by decide) (by decide) a16_0 a16_1 a16_2 a16_3 a16_4 a16_5 a16_6 a16_7))
private theorem a17_0 : I 17 0 := by decide +kernel
private theorem a17_1 : I 17 1 := by decide +kernel
private theorem a17_2 : I 17 2 := by decide +kernel
private theorem a17_3 : I 17 3 := by decide +kernel
private theorem a17_4 : I 17 4 := by decide +kernel
private theorem a17_5 : I 17 5 := by decide +kernel
private theorem a17_6 : I 17 6 := by decide +kernel
private theorem a17_7 : I 17 7 := by decide +kernel
private theorem h17 : checkRow 19 17 (C 17) (row 17)=true := row_of_blocks 19 17 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 17 _ _ 0 (by decide) (by decide) a17_0 a17_1 a17_2 a17_3 a17_4 a17_5 a17_6 a17_7))
private theorem a18_0 : I 18 0 := by decide +kernel
private theorem a18_1 : I 18 1 := by decide +kernel
private theorem a18_2 : I 18 2 := by decide +kernel
private theorem a18_3 : I 18 3 := by decide +kernel
private theorem a18_4 : I 18 4 := by decide +kernel
private theorem a18_5 : I 18 5 := by decide +kernel
private theorem a18_6 : I 18 6 := by decide +kernel
private theorem a18_7 : I 18 7 := by decide +kernel
private theorem h18 : checkRow 19 18 (C 18) (row 18)=true := row_of_blocks 19 18 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 18 _ _ 0 (by decide) (by decide) a18_0 a18_1 a18_2 a18_3 a18_4 a18_5 a18_6 a18_7))
private theorem a19_0 : I 19 0 := by decide +kernel
private theorem a19_1 : I 19 1 := by decide +kernel
private theorem a19_2 : I 19 2 := by decide +kernel
private theorem a19_3 : I 19 3 := by decide +kernel
private theorem a19_4 : I 19 4 := by decide +kernel
private theorem a19_5 : I 19 5 := by decide +kernel
private theorem a19_6 : I 19 6 := by decide +kernel
private theorem a19_7 : I 19 7 := by decide +kernel
private theorem h19 : checkRow 19 19 (C 19) (row 19)=true := row_of_blocks 19 19 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 19 _ _ 0 (by decide) (by decide) a19_0 a19_1 a19_2 a19_3 a19_4 a19_5 a19_6 a19_7))
private theorem a20_0 : I 20 0 := by decide +kernel
private theorem a20_1 : I 20 1 := by decide +kernel
private theorem a20_2 : I 20 2 := by decide +kernel
private theorem a20_3 : I 20 3 := by decide +kernel
private theorem a20_4 : I 20 4 := by decide +kernel
private theorem a20_5 : I 20 5 := by decide +kernel
private theorem a20_6 : I 20 6 := by decide +kernel
private theorem a20_7 : I 20 7 := by decide +kernel
private theorem h20 : checkRow 19 20 (C 20) (row 20)=true := row_of_blocks 19 20 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 20 _ _ 0 (by decide) (by decide) a20_0 a20_1 a20_2 a20_3 a20_4 a20_5 a20_6 a20_7))
private theorem a21_0 : I 21 0 := by decide +kernel
private theorem a21_1 : I 21 1 := by decide +kernel
private theorem a21_2 : I 21 2 := by decide +kernel
private theorem a21_3 : I 21 3 := by decide +kernel
private theorem a21_4 : I 21 4 := by decide +kernel
private theorem a21_5 : I 21 5 := by decide +kernel
private theorem a21_6 : I 21 6 := by decide +kernel
private theorem a21_7 : I 21 7 := by decide +kernel
private theorem h21 : checkRow 19 21 (C 21) (row 21)=true := row_of_blocks 19 21 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 19 21 _ _ 0 (by decide) (by decide) a21_0 a21_1 a21_2 a21_3 a21_4 a21_5 a21_6 a21_7))
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
theorem checked (v : ℕ) (hv : v≤163) : checkRow 19 v (FinalLedgerData6815.row 19 v) (row v)=true := by
  by_cases e0 : v=0
  · subst e0; exact h0
  by_cases e1 : v=1
  · subst e1; exact h1
  by_cases e2 : v=2
  · subst e2; exact h2
  by_cases e3 : v=3
  · subst e3; exact h3
  by_cases e4 : v=4
  · subst e4; exact h4
  by_cases e5 : v=5
  · subst e5; exact h5
  by_cases e6 : v=6
  · subst e6; exact h6
  by_cases e7 : v=7
  · subst e7; exact h7
  by_cases e8 : v=8
  · subst e8; exact h8
  by_cases e9 : v=9
  · subst e9; exact h9
  by_cases e10 : v=10
  · subst e10; exact h10
  by_cases e11 : v=11
  · subst e11; exact h11
  by_cases e12 : v=12
  · subst e12; exact h12
  by_cases e13 : v=13
  · subst e13; exact h13
  by_cases e14 : v=14
  · subst e14; exact h14
  by_cases e15 : v=15
  · subst e15; exact h15
  by_cases e16 : v=16
  · subst e16; exact h16
  by_cases e17 : v=17
  · subst e17; exact h17
  by_cases e18 : v=18
  · subst e18; exact h18
  by_cases e19 : v=19
  · subst e19; exact h19
  by_cases e20 : v=20
  · subst e20; exact h20
  by_cases e21 : v=21
  · subst e21; exact h21
  have hH : ¬(v∈H ∨ 164≤v) := by simp only [H,List.mem_cons,List.not_mem_nil,or_false,false_or]; omega
  have h := okAt v (by omega)
  simp only [ok,if_neg hH] at h
  exact row_of_rowL 19 v _ _ (nb v) (by omega) (by omega) h
end ProximityPrize.SubmissionLower.FinalRulesRows6815_R19
