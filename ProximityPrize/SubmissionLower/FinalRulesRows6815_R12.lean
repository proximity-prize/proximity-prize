import ProximityPrize.SubmissionLower.MergedInfra6815_54
namespace ProximityPrize.SubmissionLower.FinalRulesRows6815_R12
open FinalCurves6815 FinalRulesRowCheck6815 FinalRulesCached6815 FinalRulesCompact6815 SingletonCertificate6815 CompactAllN6815
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private abbrev D : ℕ → List Piece := FinalRulesRowCheck6815.decode
def row (v : ℕ) : List Piece := (#[D 0x22bad00159e60011454000542c30041363400409520006,D 0x22bac00159c9001143f000541700013503004134f40040abf0007,D 0x22bab00159ad001142900054013004133d40040abf0006,D 0x22baa0015990001141300053eb3004132a40040abf0006,D 0x22ba9001597200113fe00053d63004131640040abe0006,D 0x22ba8001595400113e800053bf3004130240040abd0006,D 0x22ba7001593600113d100053a9300412ee40040abb0006,D 0x22ba6001591700113bb0005393300412da40040ab90006,D 0x22ba500158f800113a4000537c300412c640040bbb500400060007,D 0x22ba400158d8001138e0005365300412b240040c31500400590007,D 0x22ba300158b80011377000534e3004129d40040cc65004009b0007,D 0x22ba20015898001135f00053373004128940040d51500400e00007,D 0x22ba1001587800113480005320100412743004127340040dd2500401290008,D 0x22ba00015859001133000053083004125f40040e51500401720007,D 0x22b9f001583a001131900052f0000124a3004124940040ecd500401bb0008,D 0x22b9e001581a001130100052d8100412353004123440040f48500402040008,D 0x22b9d00157fa00112e800052c03004121f40040fbe5004024d0007,D 0x22b9c00157d900112d000052a7100412093004120840041033500402950008,D 0x22b9b00157b700112b7000528e100411f3300411f2400410a5500402dd0008,D 0x22b9a0015795001129e0005275300411dd40041114500403260007,D 0x22b9900157730011285000525c300411c7400411825004036e0007,D 0x22b98001574f001126c0005242400411b0500403d30006,D 0x22b97001572b001125200052293004119a4004119950040430600400160008,D 0x22b9600157070011238000520f400411835004046c6004003a0007,D 0x22b9500156e2001121e00051f44004116b500404a86004005e0007,D 0x22b9400156be001120300051d940041154500404e2600400820007,D 0x22b93001569a00111e800051be3004113c4004113b5004051b600400a60008,D 0x22b92001567500111cd00051a300011244004112350040552600400ca0008,D 0x22b91001565000111b10005187000110c4004110b50040588600400ee0008,D 0x22b9000156290011195000516b00010f4400410f3500405bd600401120008,D 0x22b8f00156020011179000514f400410db500405f0600401360007,D 0x22b8e00155da001115c000513200010c2f00410a14004109f500406116004015a0009,D 0x22b8d00155b1001113f000511500010a8f004104840041046500406206004017d0009,D 0x22b8c0015588001112200050f7000108f10040ff740040ff15004062c600401a10009,D 0x22b8b001555e001110400050d910041075f0040fa040040f9e50040634600401c40009,D 0x22b8a001553500110e6100410bb00050681004105a40040f505004063a600401e80009,D 0x22b89001550b00110c71004109cf0040f0440040f025004063d6004020b0008,D 0x22b8800154df00110a81004107c40040eb95004063d6004022e0007,D 0x22b8700154b300110881004105c30040eb940040e855004060d600402510008,D 0x22b8600154851004106830040eb940040e0850040602600402740007,D 0x22b8500154561004107b30040eb940040dc1500405dc600402970007,D 0x22b840015427100410ab30040eb840040da8500405a0600402ba0007,D 0x22b8300153f7100410a020040e8b30040e4540040d5d500405a4600402dd0008,D 0x22b8200153c6100410ac20040e8b30040de040040c9b500405d5600403000008,D 0x22b8100256820015394100410b820040dfb3f0080c9c40040c9a500405f3600403230009,D 0x22b80002565100153610010f9a0004f6c10040f3d20040cee40040c9a5004061260040345000a,D 0x22b7f001532b0010f750004f471111100000000000000000000000000000000000000000000000000000000000000000000000000000000000003f1700f1e3f0080cd93f0080ccc40040cc05004066d60040368000a,D 0x22b7e00152f51000011222111000000000000000000000000000000000000001110000000000000000000000000000000000000000003f1880f4f1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f1880dd53f0080ca33f0080c9640040c8a5004065a6004038a0009,D 0x22b7d00152be10000122332211000000000000000000000000000000000000011221111000000000000000000000000000000000000003f18c0f7f10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f18c0dd53f0080ca33f0080c9640040c8a50040611600403ad0009,D 0x22b7c0015284100112233333221110000000000000000000000000000000000112333322211100000000000000000000000000000000004f1900fcc100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004f1900dd54f0080ca34f0080c9630040c7140040c6c500405e4600403b87004000c000b,D 0x22b7b00152492111123222110000000000000000000000000000000000000001121111100000000000000000000000000000000000000004f1940ed92111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004f1940dd54f0080ca34f0080c9630040c7140040c0e500405ca600403b67004001e000b,D 0x22b7a001520c21112332221100000000000000000000000000000000000000011222111100000000000000000000000000000000000000004f1980ebe21111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004f1980dd54f0080ca34f0080c9630040c7140040bb2500405b0600403b670040030000b,D 0x22b7900151cd1222223333221110000000000000000000000000000000000000122332222111100000000000000000000000000000000000004f1a00ed91222211100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004f1a00dd54f0080ca34f0080c9630040c7140040b5b50040593600403b570040041000b,D 0x22b78001518b113222232221100000000000000000000000000000000000000001222222111100000000000000000000000000000000000000005f1a80e59113222211100000000000000000000000000000000000000000001111100000000000000000000000000000000000000000000005f1a80dd55f0080ca35f0080c9630040c7140040b5b5004054b600403b370040053000b,D 0x22b77001514711132233333333221100000000000000000000000000000000000012233333333322221110000000000000000000000000000000005f1b00ee311132222221100000000000000000000000000000000000000000012111111000000000000000000000000000000000000000000005f1b00dd511000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005f1b00ca311000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005f1b00c9630040c7140040b5b50040502600403b370040064000b,D 0x22b7600151001112333333333333221110000000000000000000000000000000000122333333333333222211110000000000000000000000000000005f1b80eee1112333332211100000000000000000000000000000000000000000122222211111000000000000000000000000000000000000000005f1b80dd51111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005f1b80ca31111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005f1b80c9630040c7140040b5b500404ba600403b270040076000b,D 0x22b7500150b6111223333334433333221110000000000000000000000000000000001223333444333333333222111100000000000000000000000000006f1c00ef9111223333332211100000000000000000000000000000000000000001223322222111110000000000000000000000000000000000000005f1c00dd5112111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005f1c00ca3112111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005f1c00c9630040c7140040b5b50040472600403b070040087000b,D 0x22b7400250c000150691122333333443333322111000000000000000000000000000000000011233334443333333322221111000000000000000000000000000006f1c40ea711122343333433333221110000000000000000000000000000000000012233333333333333222211100000000000000000000000000000006f1c80e7a11122343333322211100000000000000000000000000000000000000012233333222222111110000000000000000000000000000000000006f1c80dd511222211110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006f1c80ca311222211110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006f1c80c9630040c7140040b5b50040472600403a87004008a000d,D 0x22b7300250d700150181112233433334443333322110000000000000000000000000000000000122333344444433333333222211100000000000000000000000000006f1d00e9e1112233433333332211100000000000000000000000000000000000000122333333333222221111100000000000000000000000000000000006f1d00dd51122222211100000000000000000000000000000000000000000000001111111100000000000000000000000000000000000000000000000006f1d00ca31122222211100000000000000000000000000000000000000000000001111111100000000000000000000000000000000000000000000000006f1d00c9630040c7140040b5b50040472600403a870040089000c,D 0x22b7200250ee0014fc40010d2f20040d1630040ca340040b5b50040472600403a870040088000a,D 0x22b7100251060014f6d20040d1530040ca340040b5b50040472600403a8700400860009,D 0x22b70002511d0014f1320040d1a30040ca340040b5b50040472600403a8700400850009,D 0x22b6f00251350014eb530040cdf40040b5b50040472600403a8700400840008,D 0x22b6e002514c0014e5330040ce240040b5b50040472600403a8700400830008,D 0x22b6d00251630014dee30040ce440040b5b50040472600403a8700400810008,D 0x22b6c002517b0014d8630040ce640040b5b50040472600403a8700400800008,D 0x22b6b00251920014d1b30040ce840040b5b50040472600403a87004007f0008,D 0x22b6a00251aa30040ccf40040b5b50040472600403a87004007d0007,D 0x22b6900251c130040ccf40040b5b50040472600403a87004007c0007,D 0x22b6800251d930040cd040040b5b50040472600403a87004007b0007,D 0x22b6700251f030040cd040040b5b50040472600403a8700400790007,D 0x22b66002520730040cd040040b5b50040472600403a8700400780007,D 0x22b65002521f30040cd040040b5b50040472600403a8700400760007,D 0x22b64002523630040cd040040b5b50040472600403a8700400750007,D 0x22b63002524e30040cd040040b5b50040472600403a8700400730007,D 0x22b62002526530040cd140040b5b50040472600403a8700400720007,D 0x22b61002527c30040cd140040b5b50040472600403a8700400700007,D 0x22b60002529430040cd140040b5b50040472600403a87004006f0007,D 0x22b5f00252ab30040cd140040b5b50040472600403a87004006d0007,D 0x22b5e00252c330040cd140040b5b50040472600403a87004006c0007,D 0x22b5d00252da30040cd140040b5b50040472600403a87004006a0007,D 0x22b5c00252f130040ca340040b8950040472600403a8700400690007,D 0x22b5b002530940040c160024bbf40040ba950040472600403a8700400670008,D 0x22b5a002532040040c160024bbe40040ba950040472600403a8700400650008,D 0x22b59002533840040c160024bbd40040ba950040472600403a8700400640008,D 0x22b58002534f40040c160024bbc40040ba950040472600403a8700400620008,D 0x22b57002536740040c160024bbb40040ba950040472600403a8700400600008,D 0x22b56002537e40040c160024bba40040ba950040472600403a87004005f0008,D 0x22b55002539540040c160024bb940040ba950040472600403a87004005d0008,D 0x22b5400253ad40040c170024bb840040baa50040472600403a87004005d0008,D 0x22b5300253c440040c170024bb740040baa50040472600403a87004005d0008,D 0x22b5200253dc40040c170024bb640040baa50040472600403a87004005d0008,D 0x22b5100253f340040c170024bb540040baa50040472600403a87004005d0008,D 0x22b50002540a40040c170024bb440040baa50040472600403a87004005d0008,D 0x22b4f002542240040c170024bb340040baa50040472600403a87004005d0008,D 0x22b4e002543940040c170024bb240040baa50040472600403a87004005d0008,D 0x22b4d002545140040c170024bb140040baa50040472600403a87004005d0008,D 0x22b4c002546840040c170024bb040040bab50040472600403a87004005d0008,D 0x22b4b002547f40040c170024baf40040bab50040472600403a87004005d0008,D 0x22b4a002549740040c170024bae40040bab50040472600403a87004005d0008,D 0x22b4900254ae40040c170024bad40040bab50040472600403a87004005d0008,D 0x22b4800254c640040c1840040bad0024bac40040bab50040472600403a87004005d0009,D 0x22b4700254dd40040c1850040472600403a87004005d0006,D 0x22b4600254f540040c1850040472600403a87004005d0006,D 0x22b45002550c40040c1850040472600403a87004005d0006,D 0x22b44002552340040c1850040472600403a87004005d0006,D 0x22b43002553b40040c1850040472600403a87004005d0006,D 0x22b42002555240040c1850040472600403a87004005d0006,D 0x22b41002556a40040c1850040472600403a87004005d0006,D 0x22b40002558140040c1850040472600403a87004005d0006,D 0x22b3f002559840040c1850040472600403a87004005d0006,D 0x22b3e00255b040040c1850040472600403a87004005d0006,D 0x22b3d00255c740040c1950040472600403a87004005d0006,D 0x22b3c00255df40040c1950040472600403a87004005d0006,D 0x22b3b00255f640040c1950040472600403a87004005d0006,D 0x22b3a002560d40040c1950040472600403a87004005d0006,D 0x22b39002562540040c1950040472600403a87004005d0006,D 0x22b38002563c40040c1950040472600403a87004005d0006,D 0x22b37002565440040c1950040472600403a87004005d0006,D 0x22b36002566b40040c1950040472600403a87004005d0006,D 0x22b35002568240040bec0024b9940040b805004049f600403a87004005d0008,D 0x22b34002569a40040ba50024b9840040b39500404e6600403a87004005d0008,D 0x22b3300256b10024b9740040af35004052d600403a87004005d0007,D 0x22b3200256c90024b9640040aae50040572600403a87004005d0007,D 0x22b3100256e00024b9540040a69500405b7600403a87004005d0007,D 0x22b3000256f80024b9440040a26500405fa600403a87004005d0007,D 0x22b2f002570f0024b93400409e35004063d600403a87004005d0007,D 0x22b2e00257260024b92400409a15004067f600403a87004005d0007,D 0x22b2d002573e0024b914004095f500406c1600403a87004005d0007,D 0x22b2c00257550024b904004092050040700600403a87004005d0007,D 0x22b2b002576d0024b8f400408e050040740600403a87004005d0007,D 0x22b2a00257840024b8e400408a25004077e600403a87004005d0007,D 0x22b29002579b0024b8d40040864500407bc600403a87004005d0007,D 0x22b2800257b30024b8c40040841500407df600403a87004005d0007,D 0x22b2700257ca0024b8b4004081e50040802600403a87004005d0007,D 0x22b2600257e20024b8a4004081f50040802600403a87004005d0007,D 0x22b2500257f90024b894004081f50040802600403a87004005d0007,D 0x22b2400258100024b884004081f50040802600403a87004005d0007,D 0x22b2300258280024b874004081f50040802600403a87004005d0007,D 0x22b22002583f0024b864004081f50040802600403a87004005d0007,D 0x22b2100258570024b854004081f50040802600403a87004005d0007,D 0x22b20002586e0024b844004081f50040802600403a87004005d0007,D 0x22b1f00258860024b834004081f50040802600403a87004005d0007,D 0x22b1e002589d0024b824004081f50040802600403a87004005d0007,D 0x22b1d00258b40024b814004082050040802600403a87004005d0007,D 0x22b1c00258cc0024b804004082050040802600403a87004005d0007,D 0x22b1b00258e30024b7f4004082050040802600403a87004005d0007,D 0x22b1a00258fb0024b7e4004082050040802600403a87004005d0007,D 0x22b1900259120024b7d4004082050040802600403a87004005d0007,D 0x22b1800259290024b7c4004082050040802600403a87004005d0007,D 0x22b1700259410024b7b4004082050040802600403a87004005d0007,D 0x22b1600259580024b7a4004082050040802600403a87004005d0007,D 0x22b1500259700024b794004082150040802600403a87004005d0007,D 0x22b1400259870024b784004082150040802600403a87004005d0007,D 0x22b13002599e0024b774004082150040802600403a87004005c0007,D 0x22b1200259b60024b764004082150040802600403a87004005c0007,D 0x22b1100259cd0024b754004082150040802600403a87004005c0007,D 0x22b1000259e50024b744004082150040802600403a87004005c0007,D 0x22b0f00259fc0024b734004082150040802600403a87004005c0007,D 0x22b0e0025a140024b724004082150040802600403a87004005c0007,D 0x22b0d0025a2b0024b714004082150040802600403a87004005b0007,D 0x22b0c0025a420024b704004082250040802600403a87004005b0007,D 0x22b0b0025a5a0024b6f4004082250040802600403a87004005b0007,D 0x22b0a0025a710024b6e4004082250040802600403a87004005b0007,D 0x22b090025a890024b6d4004082250040802600403a87004005b0007,D 0x22b080025aa00024b6c4004082250040802600403a87004005a0007,D 0x22b070025ab70024b6b4004082250040802600403a87004005a0007,D 0x22b060025acf0024b6a4004082250040802600403a87004005a0007,D 0x22b050025ae60024b694004082250040802600403a87004005a0007,D 0x22b040025afe0024b684004082350040802600403a87004005a0007,D 0x22b030025b150024b674004082350040802600403a8700400590007][v]?).getD []
private abbrev C (v : ℕ) : List Piece := FinalLedgerData6815.row 12 v
private def nb (v : ℕ) : ℕ := (#[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1][v]?).getD 0
private def H : List ℕ := [31,32,34,36,44,46,47,48,49,50,51,52,53,54,55,56,57,58]
private def ok (v : ℕ) : Bool := if v∈H ∨ 171≤v then true else rowL 12 v (C v) (row v) (nb v)
private abbrev I (v i : ℕ) : Prop := indexL 12 v (C v) (row v) i=true
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
private theorem a31_0 : I 31 0 := by decide +kernel
private theorem a31_1 : I 31 1 := by decide +kernel
private theorem a31_2 : I 31 2 := by decide +kernel
private theorem a31_3 : I 31 3 := by decide +kernel
private theorem a31_4 : I 31 4 := by decide +kernel
private theorem a31_5 : I 31 5 := by decide +kernel
private theorem a31_6 : I 31 6 := by decide +kernel
private theorem a31_7 : I 31 7 := by decide +kernel
private theorem h31 : checkRow 12 31 (C 31) (row 31)=true := row_of_blocks 12 31 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 31 _ _ 0 (by decide) (by decide) a31_0 a31_1 a31_2 a31_3 a31_4 a31_5 a31_6 a31_7)) (blk 12 31 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a32_0 : I 32 0 := by decide +kernel
private theorem a32_1 : I 32 1 := by decide +kernel
private theorem a32_2 : I 32 2 := by decide +kernel
private theorem a32_3 : I 32 3 := by decide +kernel
private theorem a32_4 : I 32 4 := by decide +kernel
private theorem a32_5 : I 32 5 := by decide +kernel
private theorem a32_6 : I 32 6 := by decide +kernel
private theorem a32_7 : I 32 7 := by decide +kernel
private theorem h32 : checkRow 12 32 (C 32) (row 32)=true := row_of_blocks 12 32 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 32 _ _ 0 (by decide) (by decide) a32_0 a32_1 a32_2 a32_3 a32_4 a32_5 a32_6 a32_7)) (blk 12 32 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a34_0 : I 34 0 := by decide +kernel
private theorem a34_1 : I 34 1 := by decide +kernel
private theorem a34_2 : I 34 2 := by decide +kernel
private theorem a34_3 : I 34 3 := by decide +kernel
private theorem a34_4 : I 34 4 := by decide +kernel
private theorem a34_5 : I 34 5 := by decide +kernel
private theorem a34_6 : I 34 6 := by decide +kernel
private theorem a34_7 : I 34 7 := by decide +kernel
private theorem h34 : checkRow 12 34 (C 34) (row 34)=true := row_of_blocks 12 34 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 34 _ _ 0 (by decide) (by decide) a34_0 a34_1 a34_2 a34_3 a34_4 a34_5 a34_6 a34_7)) (blk 12 34 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a36_0 : I 36 0 := by decide +kernel
private theorem a36_1 : I 36 1 := by decide +kernel
private theorem a36_2 : I 36 2 := by decide +kernel
private theorem a36_3 : I 36 3 := by decide +kernel
private theorem a36_4 : I 36 4 := by decide +kernel
private theorem a36_5 : I 36 5 := by decide +kernel
private theorem a36_6 : I 36 6 := by decide +kernel
private theorem a36_7 : I 36 7 := by decide +kernel
private theorem h36 : checkRow 12 36 (C 36) (row 36)=true := row_of_blocks 12 36 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 12 36 _ _ 0 (by decide) (by decide) a36_0 a36_1 a36_2 a36_3 a36_4 a36_5 a36_6 a36_7))
private theorem a44_0 : I 44 0 := by decide +kernel
private theorem a44_1 : I 44 1 := by decide +kernel
private theorem a44_2 : I 44 2 := by decide +kernel
private theorem a44_3 : I 44 3 := by decide +kernel
private theorem a44_4 : I 44 4 := by decide +kernel
private theorem a44_5 : I 44 5 := by decide +kernel
private theorem a44_6 : I 44 6 := by decide +kernel
private theorem a44_7 : I 44 7 := by decide +kernel
private theorem h44 : checkRow 12 44 (C 44) (row 44)=true := row_of_blocks 12 44 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 44 _ _ 0 (by decide) (by decide) a44_0 a44_1 a44_2 a44_3 a44_4 a44_5 a44_6 a44_7)) (blk 12 44 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a46_0 : I 46 0 := by decide +kernel
private theorem a46_1 : I 46 1 := by decide +kernel
private theorem a46_2 : I 46 2 := by decide +kernel
private theorem a46_3 : I 46 3 := by decide +kernel
private theorem a46_4 : I 46 4 := by decide +kernel
private theorem a46_5 : I 46 5 := by decide +kernel
private theorem a46_6 : I 46 6 := by decide +kernel
private theorem a46_7 : I 46 7 := by decide +kernel
private theorem h46 : checkRow 12 46 (C 46) (row 46)=true := row_of_blocks 12 46 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 46 _ _ 0 (by decide) (by decide) a46_0 a46_1 a46_2 a46_3 a46_4 a46_5 a46_6 a46_7)) (blk 12 46 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a47_0 : I 47 0 := by decide +kernel
private theorem a47_1 : I 47 1 := by decide +kernel
private theorem a47_2 : I 47 2 := by decide +kernel
private theorem a47_3 : I 47 3 := by decide +kernel
private theorem a47_4 : I 47 4 := by decide +kernel
private theorem a47_5 : I 47 5 := by decide +kernel
private theorem a47_6 : I 47 6 := by decide +kernel
private theorem a47_7 : I 47 7 := by decide +kernel
private theorem h47 : checkRow 12 47 (C 47) (row 47)=true := row_of_blocks 12 47 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 47 _ _ 0 (by decide) (by decide) a47_0 a47_1 a47_2 a47_3 a47_4 a47_5 a47_6 a47_7)) (blk 12 47 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a48_0 : I 48 0 := by decide +kernel
private theorem a48_1 : I 48 1 := by decide +kernel
private theorem a48_2 : I 48 2 := by decide +kernel
private theorem a48_3 : I 48 3 := by decide +kernel
private theorem a48_4 : I 48 4 := by decide +kernel
private theorem a48_5 : I 48 5 := by decide +kernel
private theorem a48_6 : I 48 6 := by decide +kernel
private theorem a48_7 : I 48 7 := by decide +kernel
private theorem h48 : checkRow 12 48 (C 48) (row 48)=true := row_of_blocks 12 48 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 48 _ _ 0 (by decide) (by decide) a48_0 a48_1 a48_2 a48_3 a48_4 a48_5 a48_6 a48_7)) (blk 12 48 _ _ 1 (by decide) (by decide) (by decide +kernel)))
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
private theorem h49 : checkRow 12 49 (C 49) (row 49)=true := row_of_blocks 12 49 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 49 _ _ 0 (by decide) (by decide) a49_0 a49_1 a49_2 a49_3 a49_4 a49_5 a49_6 a49_7)) (blk8 12 49 _ _ 1 (by decide) (by decide) a49_8 a49_9 a49_10 a49_11 a49_12 a49_13 a49_14 a49_15))
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
private theorem h50 : checkRow 12 50 (C 50) (row 50)=true := row_of_blocks 12 50 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 50 _ _ 0 (by decide) (by decide) a50_0 a50_1 a50_2 a50_3 a50_4 a50_5 a50_6 a50_7)) (blk8 12 50 _ _ 1 (by decide) (by decide) a50_8 a50_9 a50_10 a50_11 a50_12 a50_13 a50_14 a50_15))
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
private theorem h51 : checkRow 12 51 (C 51) (row 51)=true := row_of_blocks 12 51 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 51 _ _ 0 (by decide) (by decide) a51_0 a51_1 a51_2 a51_3 a51_4 a51_5 a51_6 a51_7)) (blk8 12 51 _ _ 1 (by decide) (by decide) a51_8 a51_9 a51_10 a51_11 a51_12 a51_13 a51_14 a51_15))
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
private theorem h52 : checkRow 12 52 (C 52) (row 52)=true := row_of_blocks 12 52 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 52 _ _ 0 (by decide) (by decide) a52_0 a52_1 a52_2 a52_3 a52_4 a52_5 a52_6 a52_7)) (blk8 12 52 _ _ 1 (by decide) (by decide) a52_8 a52_9 a52_10 a52_11 a52_12 a52_13 a52_14 a52_15))
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
private theorem h53 : checkRow 12 53 (C 53) (row 53)=true := row_of_blocks 12 53 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 53 _ _ 0 (by decide) (by decide) a53_0 a53_1 a53_2 a53_3 a53_4 a53_5 a53_6 a53_7)) (blk8 12 53 _ _ 1 (by decide) (by decide) a53_8 a53_9 a53_10 a53_11 a53_12 a53_13 a53_14 a53_15))
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
private theorem h54 : checkRow 12 54 (C 54) (row 54)=true := row_of_blocks 12 54 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 54 _ _ 0 (by decide) (by decide) a54_0 a54_1 a54_2 a54_3 a54_4 a54_5 a54_6 a54_7)) (blk8 12 54 _ _ 1 (by decide) (by decide) a54_8 a54_9 a54_10 a54_11 a54_12 a54_13 a54_14 a54_15))
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
private theorem h55 : checkRow 12 55 (C 55) (row 55)=true := row_of_blocks 12 55 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 55 _ _ 0 (by decide) (by decide) a55_0 a55_1 a55_2 a55_3 a55_4 a55_5 a55_6 a55_7)) (blk8 12 55 _ _ 1 (by decide) (by decide) a55_8 a55_9 a55_10 a55_11 a55_12 a55_13 a55_14 a55_15))
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
private theorem h56 : checkRow 12 56 (C 56) (row 56)=true := row_of_blocks 12 56 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 56 _ _ 0 (by decide) (by decide) a56_0 a56_1 a56_2 a56_3 a56_4 a56_5 a56_6 a56_7)) (blk8 12 56 _ _ 1 (by decide) (by decide) a56_8 a56_9 a56_10 a56_11 a56_12 a56_13 a56_14 a56_15))
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
private theorem h57 : checkRow 12 57 (C 57) (row 57)=true := row_of_blocks 12 57 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 57 _ _ 0 (by decide) (by decide) a57_0 a57_1 a57_2 a57_3 a57_4 a57_5 a57_6 a57_7)) (blk8 12 57 _ _ 1 (by decide) (by decide) a57_8 a57_9 a57_10 a57_11 a57_12 a57_13 a57_14 a57_15))
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
private theorem h58 : checkRow 12 58 (C 58) (row 58)=true := row_of_blocks 12 58 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 12 58 _ _ 0 (by decide) (by decide) a58_0 a58_1 a58_2 a58_3 a58_4 a58_5 a58_6 a58_7)) (blk8 12 58 _ _ 1 (by decide) (by decide) a58_8 a58_9 a58_10 a58_11 a58_12 a58_13 a58_14 a58_15))
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
theorem checked (v : ℕ) (hv : v≤170) : checkRow 12 v (FinalLedgerData6815.row 12 v) (row v)=true := by
  by_cases e31 : v=31
  · subst e31; exact h31
  by_cases e32 : v=32
  · subst e32; exact h32
  by_cases e34 : v=34
  · subst e34; exact h34
  by_cases e36 : v=36
  · subst e36; exact h36
  by_cases e44 : v=44
  · subst e44; exact h44
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
  have hH : ¬(v∈H ∨ 171≤v) := by simp only [H,List.mem_cons,List.not_mem_nil,or_false,false_or]; omega
  have h := okAt v (by omega)
  simp only [ok,if_neg hH] at h
  exact row_of_rowL 12 v _ _ (nb v) (by omega) (by omega) h
end ProximityPrize.SubmissionLower.FinalRulesRows6815_R12
