import ProximityPrize.SubmissionLower.FinalRulesCompact6815
namespace ProximityPrize.SubmissionLower.FinalRulesRows6815_R11
open FinalCurves6815 FinalRulesRowCheck6815 FinalRulesCached6815 FinalRulesCompact6815 SingletonCertificate6815 CompactAllN6815
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private abbrev D : ℕ → List Piece := FinalRulesRowCheck6815.decode
def row (v : ℕ) : List Piece := (#[D 0x22bae0015a7d00114c6000549f200413c8300413c7400404d20007,D 0x22bad0015a6100114b1000548a00013b5300413b4400406290007,D 0x22bac0015a46001149c0005474300413a2400406290006,D 0x22bab0015a2b0011487000545f3004138f400406290006,D 0x22baa0015a0f0011471000544a3004137c400406280006,D 0x22ba900159f2001145c000543430041368400406270006,D 0x22ba800159d60011446000541e000135530041354400407070007,D 0x22ba700159b900114300005408300413414004081f0006,D 0x22ba6001599b001141a00053f23004132d400409340006,D 0x22ba5001597d001140400053dc100413193004131840040a460007,D 0x22ba4001595f00113ed00053c53004130540040b2c500400160007,D 0x22ba3001594000113d600053af300412f140040bba500400560007,D 0x22ba2001592100113c00005398100412dd300412dc40040c40500400990008,D 0x22ba1001590100113a90005381300412c840040cc3500400dc0007,D 0x22ba000158e000113910005369100412b3300412b240040d445004011e0008,D 0x22b9f00158bf001137a00053523004129e40040dc2500401610007,D 0x22b9e001589e0011362000533a200412893004128840040e3f500401a30008,D 0x22b9d001587e001134a0005322100412743004127340040eb9500401e60008,D 0x22b9c001585e0011332000530a000125f3004125e40040f31500402280008,D 0x22b9b001583e001131a00052f2200412493004124840040fa65004026a0008,D 0x22b9a001581e001130100052d900012333004123240041019500402ac0008,D 0x22b9900157fd00112e900052c02004121d3004121c4004108a500402ee0008,D 0x22b9800157db00112cf00052a7000120730041206400410f8500403300008,D 0x22b9700157b800112b6000528d100411f1300411f040041164500403710008,D 0x22b960015795001129d0005274200411da300411d9400411cc500403b20008,D 0x22b9500157720011283000525a200411c3400411c250040408600400120008,D 0x22b94001574d00112680005240300411ac400411ab50040445600400330008,D 0x22b930015728001124e0005225100411954004119450040480600400540008,D 0x22b9200157030011233000520a3004117d4004117c500404ba600400750008,D 0x22b9100156dd001121800051ef3004116540041164500404f2600400960008,D 0x22b9000156b800111fd00051d34004114d50040529600400b70007,D 0x22b8f001569300111e100051b80001135400411345004055f600400d70008,D 0x22b8e001566d00111c5000519b3004111c4004111b50040594600400f80008,D 0x22b8d001564600111a9000517f40041103500405c7600401190007,D 0x22b8c001561e001118c0005162400410ea500405f8600401390007,D 0x22b8b00155f6001116e000514400010d0f004109d4004109b500406106004015a0009,D 0x22b8a00155cc0011151000512700010b61004104b40041048500406206004017a0009,D 0x22b8900155a100111330005108000109cf0040ff940040ff75004062d6004019a0009,D 0x22b880015576001111400050ea1004108240040fa950040638600401bb0008,D 0x22b87001554b00110f5100410ca00050b510041067f0040f6040040f5e50040640600401db000a,D 0x22b86001552000110d6100410ab40040f1650040645600401fb0007,D 0x22b8500154f400110b61004108a40040ed0500406486004021b0007,D 0x22b8400154c600110951004106a40040e8b500406496004023b0007,D 0x22b83001549700110741004104830040e8b40040e4e500406246004025b0008,D 0x22b82001546700110521004102620040e8b30040e7b40040dd9500406206004027b0009,D 0x22b8100154361004103e20040e5d3f0080db440040db25004062a6004029b0008,D 0x22b800015404001100d0004fe010040f9f20040da340040d9e5004064c600402ba0009,D 0x22b7f00153d20010fe90004fbc1f0080f801f0080dd51f0080dc840040dbd50040694600402da000a,D 0x22b7e001539d0010fc40004f971100000000000000000000000000000000000000000002f0bc0f612f0080dd52f0080dc840040dbd50040651600402f9000a,D 0x22b7d00153680010f9f0004f7111100000000000000000000000000000000000000000002f0c00f412f0080dd52f0080dc830040da340040d7a5004063c60040319000b,D 0x22b7c00153300010f790004f4b111100000000000000000000000000000000000000000003f0c40f213f0080dd53f0080dc830040da340040d125004062e60040338000b,D 0x22b7b00152f70010f520004f231111100000000000000000000000000000000000000000003f0c80f003f0080dd53f0080dc830040da340040cac5004061e60040358000b,D 0x22b7a00152bd0010f2a0004efb11111110000000000000000000000000000000000000000003f0cc0edf3f0080dd53f0080dc830040da340040c495004060d60040377000b,D 0x22b7900152800010f000008ed1000cec90004ec1111211110000000000000000000000000000000000000000003f0d00ebc3f0080dd53f0080dc830040d8840040bf05004060560040396000d,D 0x22b7800152420010ed60008ea6001ce5f1111111000000000000000000000000000000000000000000004f0d40e5e1000000000000000000000000000000000000000000000000004f0d40dd51000000000000000000000000000000000000000000000000004f0d40dc820040d7130040cff40040ba650040610600403b3111222333334444455555666667777788888888889999999999aaaacf0e40002000e,D 0x22b7700152000010eaa0008e790008e500008e11001cdf120040cb230040cab40040b78500405f9600403b370040012000d,D 0x22b7600151bd0010e7d000ce4c0008db3001cd7f30040c2240040b78500405b7600403b270040022000b,D 0x22b7500151760010e4f000ce1c0008d52001cd0830040c9440040b7850040575600403b170040032000b,D 0x22b74001512c0010e1f000cdeb0008ced30040c8d40040b7850040533600403af70040041000a,D 0x22b7300150df0010dec000cdb830040c8740040b78500404f1600403ae700400510009,D 0x22b72001508e0010db8000cd8330040c9040040b78500404f1600403937004005e0009,D 0x22b71001503a0010d82000cd4b30040c9940040b78500404f1600403937004005d0009,D 0x22b700014fe30010d49000cd1130040ca140040b78500404f1600403937004005c0009,D 0x22b6f0018f940014f880010d0e000ccd530040caa40040b78500404f1600403937004005a000a,D 0x22b6e0018f930014f2a0010cd030040c9640040b78500404f160040393700400590009,D 0x22b6d0018f910014ec830040c9940040b78500404f160040393700400580008,D 0x22b6c0018f900014e6330040c9b40040b78500404f160040393700400570008,D 0x22b6b0018f8f0014dfa30040c9d40040b78500404f160040393700400560008,D 0x22b6a0018f8e0014d8d30040ca040040b78500404f160040393700400540008,D 0x22b690018f8d0014d1d30040ca240040b78500404f160040393700400530008,D 0x22b680018f8c0014caa30040ca440040b78500404f160040393700400520008,D 0x22b670018f8a30040c8c40040b78500404f160040393700400510007,D 0x22b660018f8930040c8c40040b78500404f1600403937004004f0007,D 0x22b650018f8830040c8c40040b78500404f1600403937004004e0007,D 0x22b640018f8730040c8d40040b78500404f1600403937004004d0007,D 0x22b630018f8630040c8d40040b78500404f1600403937004004b0007,D 0x22b620018f8430040c8d40040b78500404f1600403937004004a0007,D 0x22b610018f8330040c8d40040b78500404f160040393700400490007,D 0x22b600018f8230040c8d40040b78500404f160040393700400470007,D 0x22b5f0018f8130040c8e40040b78500404f160040393700400460007,D 0x22b5e0018f8030040c8e40040b78500404f160040393700400440007,D 0x22b5d0018f7f30040c8e40040b78500404f160040393700400430007,D 0x22b5c0018f7d30040c8e40040b78500404f160040393700400410007,D 0x22b5b0018f7c30040c8f40040b78500404f160040393700400400007,D 0x22b5a0018f7b30040c8f40040b78500404f1600403937004003f0007,D 0x22b590018f7a30040c8f40040b78500404f1600403937004003d0007,D 0x22b580018f7930040c8f40040b78500404f1600403937004003b0007,D 0x22b570018f7730040c4c40040bbc500404f1600403937004003a0007,D 0x22b560018f7640040c04500404f160040393700400380006,D 0x22b550018f7540040c04500404f160040393700400370006,D 0x22b540018f7440040c04500404f160040393700400350006,D 0x22b530018f7340040c04500404f160040393700400350006,D 0x22b520018f7240040c04500404f160040393700400350006,D 0x22b510018f7040040c05500404f160040393700400350006,D 0x22b500018f6f40040c05500404f160040393700400350006,D 0x22b4f0018f6e40040c05500404f160040393700400350006,D 0x22b4e0018f6d40040c05500404f160040393700400350006,D 0x22b4d0018f6c40040c05500404f160040393700400350006,D 0x22b4c0018f6a40040c05500404f160040393700400350006,D 0x22b4b0018f6940040c05500404f160040393700400350006,D 0x22b4a0018f6840040c05500404f160040393700400350006,D 0x22b490018f6740040c05500404f160040393700400350006,D 0x22b480018f6640040c06500404f160040393700400350006,D 0x22b470018f6540040c06500404f160040393700400350006,D 0x22b460018f6340040c06500404f160040393700400350006,D 0x22b450018f6240040c06500404f160040393700400350006,D 0x22b440018f6140040c06500404f160040393700400350006,D 0x22b430018f6040040c06500404f160040393700400350006,D 0x22b420018f5f40040c06500404f160040393700400350006,D 0x22b410018f5d40040c06500404f160040393700400350006,D 0x22b400018f5c40040c07500404f160040393700400350006,D 0x22b3f0018f5b40040c07500404f160040393700400350006,D 0x22b3e0018f5a40040c07500404f160040393700400350006,D 0x22b3d0018f5940040c07500404f160040393700400350006,D 0x22b3c0018f5840040c07500404f160040393700400350006,D 0x22b3b0018f5640040c07500404f160040393700400350006,D 0x22b3a0018f5540040c07500404f160040393700400350006,D 0x22b390018f5440040c07500404f160040393700400350006,D 0x22b380018f5340040c08500404f160040393700400350006,D 0x22b370018f5240040c08500404f160040393700400350006,D 0x22b360018f5040040c08500404f160040393700400350006,D 0x22b350018f4f40040c08500404f160040393700400350006,D 0x22b340018f4e40040c08500404f160040393700400350006,D 0x22b330018f4d40040c08500404f160040393700400350006,D 0x22b320018f4c40040c08500404f160040393700400350006,D 0x22b310018f4a40040c08500404f160040393700400350006,D 0x22b300018f4940040c08500404f160040393700400350006,D 0x22b2f0018f4840040c09500404f160040393700400350006,D 0x22b2e0018f4740040bdd5004051c60040393700400350006,D 0x22b2d0018f4640040b9d5004055d60040393700400350006,D 0x22b2c0018f4540040b5d5004059c60040393700400350006,D 0x22b2b0018f4340040b1e500405db60040393700400350006,D 0x22b2a0018f4240040ae05004061a60040393700400350006,D 0x22b290018f4140040aa35004065760040393700400350006,D 0x22b280018f4040040a675004069360040393700400350006,D 0x22b270018f3f40040a38500406c260040393700400350006,D 0x22b260018f3d40040a15500406e560040393700400350006,D 0x22b250018f3c40040a15500406e560040393700400350006,D 0x22b240018f3b40040a0a500406f060040393700400350006,D 0x22b230018f3a400409ef5004070b60040393700400350006,D 0x22b220018f39400409ef5004070b60040393700400350006,D 0x22b210018f38400409ef5004070b60040393700400350006,D 0x22b200018f36400409ef5004070b60040393700400350006,D 0x22b1f0018f35400409ef5004070b60040393700400350006,D 0x22b1e0018f34400409ef5004070b60040393700400350006,D 0x22b1d0018f33400409ef5004070b60040393700400350006,D 0x22b1c0018f32400409ef5004070b60040393700400350006,D 0x22b1b0018f30400409ef5004070b60040393700400350006,D 0x22b1a0018f2f400409f05004070b60040393700400350006,D 0x22b190018f2e400409f05004070b60040393700400350006,D 0x22b180018f2d400409f05004070b60040393700400350006,D 0x22b170018f2c400409f05004070b60040393700400340006,D 0x22b160018f2b400409f05004070b60040393700400340006,D 0x22b150018f29400409f05004070b60040393700400340006,D 0x22b140018f28400409f05004070b60040393700400340006,D 0x22b130018f27400409f05004070b60040393700400340006,D 0x22b120018f26400409f15004070b60040393700400340006,D 0x22b110018f25400409f15004070b60040393700400330006,D 0x22b100018f23400409f15004070b60040393700400330006,D 0x22b0f0018f22400409f15004070b60040393700400330006,D 0x22b0e0018f21400409f15004070b60040393700400330006,D 0x22b0d0018f20400409f15004070b60040393700400330006,D 0x22b0c0018f1f400409f15004070b60040393700400330006,D 0x22b0b0018f1e400409f15004070b60040393700400320006,D 0x22b0a0018f1c400409f25004070b60040393700400320006,D 0x22b090018f1b400409f25004070b60040393700400320006,D 0x22b080018f1a400409f25004070b60040393700400320006,D 0x22b070018f19400409f25004070b60040393700400320006,D 0x22b060018f18400409f25004070b60040393700400320006,D 0x22b050018f16400409f25004070b60040393700400310006,D 0x22b040018f15400409f25004070b60040393700400310006,D 0x22b030018f14400409f25004070b60040393700400310006][v]?).getD []
private abbrev C (v : ℕ) : List Piece := FinalLedgerData6815.row 11 v
private def nb (v : ℕ) : ℕ := (#[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,1,2,1,1,1,1,2,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1][v]?).getD 0
private def H : List ℕ := [35,37,39,45,47,48,49,50,51,52,53,54]
private def ok (v : ℕ) : Bool := if v∈H ∨ 172≤v then true else rowL 11 v (C v) (row v) (nb v)
private abbrev I (v i : ℕ) : Prop := indexL 11 v (C v) (row v) i=true
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
private theorem a35_0 : I 35 0 := by decide +kernel
private theorem a35_1 : I 35 1 := by decide +kernel
private theorem a35_2 : I 35 2 := by decide +kernel
private theorem a35_3 : I 35 3 := by decide +kernel
private theorem a35_4 : I 35 4 := by decide +kernel
private theorem a35_5 : I 35 5 := by decide +kernel
private theorem a35_6 : I 35 6 := by decide +kernel
private theorem a35_7 : I 35 7 := by decide +kernel
private theorem h35 : checkRow 11 35 (C 35) (row 35)=true := row_of_blocks 11 35 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 11 35 _ _ 0 (by decide) (by decide) a35_0 a35_1 a35_2 a35_3 a35_4 a35_5 a35_6 a35_7)) (blk 11 35 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a37_0 : I 37 0 := by decide +kernel
private theorem a37_1 : I 37 1 := by decide +kernel
private theorem a37_2 : I 37 2 := by decide +kernel
private theorem a37_3 : I 37 3 := by decide +kernel
private theorem a37_4 : I 37 4 := by decide +kernel
private theorem a37_5 : I 37 5 := by decide +kernel
private theorem a37_6 : I 37 6 := by decide +kernel
private theorem a37_7 : I 37 7 := by decide +kernel
private theorem h37 : checkRow 11 37 (C 37) (row 37)=true := row_of_blocks 11 37 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 11 37 _ _ 0 (by decide) (by decide) a37_0 a37_1 a37_2 a37_3 a37_4 a37_5 a37_6 a37_7)) (blk 11 37 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a39_0 : I 39 0 := by decide +kernel
private theorem a39_1 : I 39 1 := by decide +kernel
private theorem a39_2 : I 39 2 := by decide +kernel
private theorem a39_3 : I 39 3 := by decide +kernel
private theorem a39_4 : I 39 4 := by decide +kernel
private theorem a39_5 : I 39 5 := by decide +kernel
private theorem a39_6 : I 39 6 := by decide +kernel
private theorem a39_7 : I 39 7 := by decide +kernel
private theorem h39 : checkRow 11 39 (C 39) (row 39)=true := row_of_blocks 11 39 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 11 39 _ _ 0 (by decide) (by decide) a39_0 a39_1 a39_2 a39_3 a39_4 a39_5 a39_6 a39_7)) (blk 11 39 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a45_0 : I 45 0 := by decide +kernel
private theorem a45_1 : I 45 1 := by decide +kernel
private theorem a45_2 : I 45 2 := by decide +kernel
private theorem a45_3 : I 45 3 := by decide +kernel
private theorem a45_4 : I 45 4 := by decide +kernel
private theorem a45_5 : I 45 5 := by decide +kernel
private theorem a45_6 : I 45 6 := by decide +kernel
private theorem a45_7 : I 45 7 := by decide +kernel
private theorem h45 : checkRow 11 45 (C 45) (row 45)=true := row_of_blocks 11 45 _ _ 1 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 0 (allN_zero _) (blk8 11 45 _ _ 0 (by decide) (by decide) a45_0 a45_1 a45_2 a45_3 a45_4 a45_5 a45_6 a45_7))
private theorem a47_0 : I 47 0 := by decide +kernel
private theorem a47_1 : I 47 1 := by decide +kernel
private theorem a47_2 : I 47 2 := by decide +kernel
private theorem a47_3 : I 47 3 := by decide +kernel
private theorem a47_4 : I 47 4 := by decide +kernel
private theorem a47_5 : I 47 5 := by decide +kernel
private theorem a47_6 : I 47 6 := by decide +kernel
private theorem a47_7 : I 47 7 := by decide +kernel
private theorem h47 : checkRow 11 47 (C 47) (row 47)=true := row_of_blocks 11 47 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 11 47 _ _ 0 (by decide) (by decide) a47_0 a47_1 a47_2 a47_3 a47_4 a47_5 a47_6 a47_7)) (blk 11 47 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a48_0 : I 48 0 := by decide +kernel
private theorem a48_1 : I 48 1 := by decide +kernel
private theorem a48_2 : I 48 2 := by decide +kernel
private theorem a48_3 : I 48 3 := by decide +kernel
private theorem a48_4 : I 48 4 := by decide +kernel
private theorem a48_5 : I 48 5 := by decide +kernel
private theorem a48_6 : I 48 6 := by decide +kernel
private theorem a48_7 : I 48 7 := by decide +kernel
private theorem h48 : checkRow 11 48 (C 48) (row 48)=true := row_of_blocks 11 48 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 11 48 _ _ 0 (by decide) (by decide) a48_0 a48_1 a48_2 a48_3 a48_4 a48_5 a48_6 a48_7)) (blk 11 48 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a49_0 : I 49 0 := by decide +kernel
private theorem a49_1 : I 49 1 := by decide +kernel
private theorem a49_2 : I 49 2 := by decide +kernel
private theorem a49_3 : I 49 3 := by decide +kernel
private theorem a49_4 : I 49 4 := by decide +kernel
private theorem a49_5 : I 49 5 := by decide +kernel
private theorem a49_6 : I 49 6 := by decide +kernel
private theorem a49_7 : I 49 7 := by decide +kernel
private theorem h49 : checkRow 11 49 (C 49) (row 49)=true := row_of_blocks 11 49 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 11 49 _ _ 0 (by decide) (by decide) a49_0 a49_1 a49_2 a49_3 a49_4 a49_5 a49_6 a49_7)) (blk 11 49 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a50_0 : I 50 0 := by decide +kernel
private theorem a50_1 : I 50 1 := by decide +kernel
private theorem a50_2 : I 50 2 := by decide +kernel
private theorem a50_3 : I 50 3 := by decide +kernel
private theorem a50_4 : I 50 4 := by decide +kernel
private theorem a50_5 : I 50 5 := by decide +kernel
private theorem a50_6 : I 50 6 := by decide +kernel
private theorem a50_7 : I 50 7 := by decide +kernel
private theorem h50 : checkRow 11 50 (C 50) (row 50)=true := row_of_blocks 11 50 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 11 50 _ _ 0 (by decide) (by decide) a50_0 a50_1 a50_2 a50_3 a50_4 a50_5 a50_6 a50_7)) (blk 11 50 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a51_0 : I 51 0 := by decide +kernel
private theorem a51_1 : I 51 1 := by decide +kernel
private theorem a51_2 : I 51 2 := by decide +kernel
private theorem a51_3 : I 51 3 := by decide +kernel
private theorem a51_4 : I 51 4 := by decide +kernel
private theorem a51_5 : I 51 5 := by decide +kernel
private theorem a51_6 : I 51 6 := by decide +kernel
private theorem a51_7 : I 51 7 := by decide +kernel
private theorem h51 : checkRow 11 51 (C 51) (row 51)=true := row_of_blocks 11 51 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 11 51 _ _ 0 (by decide) (by decide) a51_0 a51_1 a51_2 a51_3 a51_4 a51_5 a51_6 a51_7)) (blk 11 51 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a52_0 : I 52 0 := by decide +kernel
private theorem a52_1 : I 52 1 := by decide +kernel
private theorem a52_2 : I 52 2 := by decide +kernel
private theorem a52_3 : I 52 3 := by decide +kernel
private theorem a52_4 : I 52 4 := by decide +kernel
private theorem a52_5 : I 52 5 := by decide +kernel
private theorem a52_6 : I 52 6 := by decide +kernel
private theorem a52_7 : I 52 7 := by decide +kernel
private theorem h52 : checkRow 11 52 (C 52) (row 52)=true := row_of_blocks 11 52 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 11 52 _ _ 0 (by decide) (by decide) a52_0 a52_1 a52_2 a52_3 a52_4 a52_5 a52_6 a52_7)) (blk 11 52 _ _ 1 (by decide) (by decide) (by decide +kernel)))
private theorem a53_0 : I 53 0 := by decide +kernel
private theorem a53_1 : I 53 1 := by decide +kernel
private theorem a53_2 : I 53 2 := by decide +kernel
private theorem a53_3 : I 53 3 := by decide +kernel
private theorem a53_4 : I 53 4 := by decide +kernel
private theorem a53_5 : I 53 5 := by decide +kernel
private theorem a53_6 : I 53 6 := by decide +kernel
private theorem a53_7 : I 53 7 := by decide +kernel
private theorem h53 : checkRow 11 53 (C 53) (row 53)=true := row_of_blocks 11 53 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 11 53 _ _ 0 (by decide) (by decide) a53_0 a53_1 a53_2 a53_3 a53_4 a53_5 a53_6 a53_7)) (blk 11 53 _ _ 1 (by decide) (by decide) (by decide +kernel)))
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
private theorem h54 : checkRow 11 54 (C 54) (row 54)=true := row_of_blocks 11 54 _ _ 2 (by decide +kernel) (by decide +kernel)
  (allN_snoc _ 1 (allN_snoc _ 0 (allN_zero _) (blk8 11 54 _ _ 0 (by decide) (by decide) a54_0 a54_1 a54_2 a54_3 a54_4 a54_5 a54_6 a54_7)) (blk8 11 54 _ _ 1 (by decide) (by decide) a54_8 a54_9 a54_10 a54_11 a54_12 a54_13 a54_14 a54_15))
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
theorem checked (v : ℕ) (hv : v≤171) : checkRow 11 v (FinalLedgerData6815.row 11 v) (row v)=true := by
  by_cases e35 : v=35
  · subst e35; exact h35
  by_cases e37 : v=37
  · subst e37; exact h37
  by_cases e39 : v=39
  · subst e39; exact h39
  by_cases e45 : v=45
  · subst e45; exact h45
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
  have hH : ¬(v∈H ∨ 172≤v) := by simp only [H,List.mem_cons,List.not_mem_nil,or_false,false_or]; omega
  have h := okAt v (by omega)
  simp only [ok,if_neg hH] at h
  exact row_of_rowL 11 v _ _ (nb v) (by omega) (by omega) h
end ProximityPrize.SubmissionLower.FinalRulesRows6815_R11
