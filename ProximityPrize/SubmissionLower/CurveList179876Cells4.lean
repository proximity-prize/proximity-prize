import ProximityPrize.SubmissionLower.CurveList179876Defs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace CurveList179876
private def b39_17 : CJ1.Block where
  bank := .leftLow
  cap := 120
  free := [(10,0)]
  vectors := [
    [[1,36,630,7140,58905,376992,0x1db890,0x7f6020,0x1cdbc74,0x59c8330,0xf269568,0x23cf8fb0,0x4a9b1604,0xabbd9df,0x6346e5ef,0x4ddf735e,0x3695476b,0x4736314,0x20eb9340,0x4736314,0x3695476b],[1,35,595,6545,52360,324632,0x18c478,0x669ba8,0x16720cc,0x4356264,0xaf13304,0x18de5cac,0x31bcb958,0x57ff2088,0xb47c567,0x4297adf7,0x72fd9975,0x1075c9a0,0x1075c9a0],[1,34,561,5984,46376,278256,0x148588,0x521620,0x1150aac,0x32057b8,0x7d0db4c,0x110d8160,0x20af37f8,0x374fe890,0x52f7dcd8,0x6e9fd120,0x45dc855],[1,33,528,5456,40920,237336,0x10e670,0x412fb0,0xd3dafc,0x24c7cbc,0x5845e90,0xb8922d0,0x15261528,0x2229d368,0x30ce0970],[1,32,496,4960,35960,201376,906192,0x335be0,0xa07f1c,0x1abfda0,0x3d860f0,0x7b0c1e0,0xd755348],[1,31,465,4495,31465,169911,736281,0x281fc7,0x785f55,0x1339e4b,0x2a4c2a5],[1,30,435,4060,27405,142506,593775,0x1f1058,0x594efd],[1,29,406,3654,23751,118755,475020],[1,28,378,3276,20475],[1,27,351],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_39_17 : (CJ0.blockMatrix source 39 ((17 : ℤ)-22)).rank ≤ 120 :=
  Fast.cell (z := b39_17) (Fast.bands [(17,17,1),(18,18,2),(19,19,3),(20,20,4),(21,21,5),(22,22,6),(23,23,7),(24,24,8),(25,25,9),(26,26,10),(27,27,11),(28,28,11),(29,29,11),(30,30,10),(31,31,9),(32,32,8),(33,33,7),(34,34,6),(35,36,4),(36,38,2)]) (by decide +kernel) (by decide +kernel)

private def b43_12 : CJ1.Block where
  bank := .rightLow
  cap := 112
  free := [(22,0)]
  vectors := [
    [[0,0,0,0,0,1],[0,0,0,0,10,0x7effffff],[0,0,0,0,45,0x7effffe3,1],[0,0,0,120,0x7effff4d,30],[0,0,0,210,0x7efffda9,270,0x7efffff7],[0,0,252,0x7efffb15,1200,0x7effff4d],[0,0,210,0x7efff91d,3150,0x7efffb51,45],[0,120,0x7efff971,5292,0x7effef99,600],[0,45,0x7efffbc9,5880,0x7effdd8d,3150,0x7effff89],[10,0x7efffe3f,4320,0x7effd211,8820,0x7efffb15],[1,0x7effff93,2025,0x7effd8a1,14700,0x7effeb55,210],[0x7efffff5,550,0x7effeae9,15120,0x7effd211,1764],[66,0x7efff98f,9450,0x7effc4f1,5880,0x7effff05],[0x7effff25,3300,0x7effd3b5,10080,0x7efff971],[495,0x7effedf5,9450,0x7effef21,210],[0x7efffce9,4620,0x7effeae9,1080],[924,0x7efff31d,2025,0x7effff89],[0x7efffce9,1650,0x7efffe3f],[495,0x7efffddb,45],[0x7effff25,110],[66,0x7efffff7],[0x7efffff5],[1]]]
theorem rank_43_12 : (CJ0.blockMatrix source 43 ((12 : ℤ)-22)).rank ≤ 112 :=
  Fast.cell (z := b43_12) (Fast.bands [(0,22,22),(1,23,20),(2,24,18),(3,25,16),(4,26,14),(5,27,12),(6,28,10),(7,29,8),(8,30,6),(9,31,4),(10,32,2)]) (by decide +kernel) (by decide +kernel)

private def b46_11 : CJ1.Block where
  bank := .rightLow
  cap := 101
  free := [(17,2),(18,2),(19,1),(20,1),(21,0),(22,0)]
  vectors := [
    [[0,0,0,1,1],[0,0,0,7,4,0x7effffff],[0,0,21,0x7efffffa,0x7effffef,1],[0,0,35,0x7effffbb,0x7effffd7,20],[0,35,0x7effff52,35,98,0x7efffffa],[0,21,0x7effff21,315,140,0x7effffb4],[7,0x7effff60,588,0x7effff52,0x7effff0c,21],[1,0x7effffc3,532,0x7efffcf1,0x7effff52,154],[0x7efffff7,243,0x7efffc2d,490,315,0x7effffde],[0,45,0x7efffdd9,1078,0,0x7effff52],[0,0x7effff89,798,0x7efffd53,0x7effff3d,35],[0,0,210,0x7efffd0d,196,112],[0,0,0x7effff05,462,28,0x7effffec],[0,0,210,0x7effff59,0x7effffde],[0,0,0x7effff89,27,7],[0,0,45,2],[0,0,0x7efffff7,0x7f000000],[0,0,1],[0,0,0],[0,0],[0,0],[0],[0]],
    [[0,0,0,10,11],[0,0,0,70,48,0x7effffeb],[0,0,210,0x7effffd7,0x7effff35,11],[0,0,350,0x7efffd7d,0x7efffded,224],[0,350,0x7efff971,70,1148,0x7effffb3],[0,210,0x7efff779,2730,1960,0x7efffc8f],[70,0x7efff9d3,5488,0x7efffd45,0x7efff43f,238],[10,0x7efffd9d,5096,0x7effe5f9,0x7efff3b3,1820],[0x7effff9e,2358,0x7effdcc9,2940,4200,0x7efffe6b],[0,440,0x7effeb91,9212,1960,0x7efff787],[0,0x7efffb7e,7308,0x7effecdd,0x7efff3c1,420],[0,0,1980,0x7effe669,392,1512],[0,0,0x7efff6fb,3612,1064,0x7efffef7],[0,0,1848,0x7efffc11,0x7efffdc3],[0,0,0x7efffc23,0x7effffef,98],[0,0,330,92],[0,0,0x7effffca,0x7effffef],[0,0,0],[0,0,1],[0,0],[0,0],[0],[0]],
    [[0,0,0,9,10],[0,0,0,63,45,0x7effffee],[0,0,189,0x7effffe6,0x7effff4d,9],[0,0,315,0x7efffddf,0x7efffe1b,189],[0,315,0x7efffa58,0x7effffec,990,0x7effffc2],[0,189,0x7efff89f,2205,1764,0x7efffd28],[63,0x7efffaac,4536,0x7efffec6,0x7efff614,189],[9,0x7efffdf7,4200,0x7effebd3,0x7efff4ee,1470],[0x7effffb0,1899,0x7effe471,1890,3465,0x7efffec6],[1,324,0x7efff089,6762,1890,0x7efff95c],[0x7efffff7,0x7efffd0d,5166,0x7efff35f,0x7efff629,315],[0,45,1134,0x7effef45,0,1134],[0,0x7effff89,0x7efffb93,2142,840,0x7effff44],[0,210,756,0x7efffe09,0x7efffe72],[0,0x7effff05,0x7efffebd,0x7effffd4,63],[0,210,81,54],[0,0x7effff89,0x7efffff8,0x7efffff8],[0,45,0],[0,0x7efffff7,0],[0,1],[0,0],[0],[0]],
    [[0,0,0,99,118],[0,0,0,693,558,0x7effff20],[0,0,2079,0x7effffb0,0x7efff788,107],[0,0,3465,0x7effea2f,0x7effe7bf,2268],[0,3465,0x7effc3b6,0x7efff6e6,12186,0x7efffd0d],[0,2079,0x7effb045,21231,23604,0x7effdd4e],[693,0x7effc602,47250,4095,0x7eff826a,2295],[99,0x7effe9b7,44856,0x7eff4109,0x7eff5ed0,18270],[0x7efffc86,20565,0x7efee331,7560,45675,0x7efff0d4],[10,3564,0x7eff5ae9,64974,34020,0x7effab1a],[0x7effff9e,0x7effdf85,53802,0x7effa2fb,0x7eff74b7,3969],[0,440,12474,0x7eff59a5,0x7effdb41,15120],[0,0x7efffb7e,0x7effcf47,19026,13944,0x7efff668],[0,1980,8316,0x7efff629,0x7effe99c],[0,0x7efff6fb,0x7efff215,0x7efff902,861],[0,1848,891,918],[0,0x7efffc23,0x7effff9e,0x7effff7a],[0,330,0],[0,0x7effffca,0],[0,0],[0,1],[0],[0]],
    [[0,0,0,45,55],[0,0,0,315,270,0x7effff9e],[0,0,945,45,0x7efffc2d,45],[0,0,1575,0x7efff6fb,0x7efff494,980],[0,1575,0x7effe62a,0x7efff980,5400,0x7efffec6],[0,945,0x7effdd8d,8085,10980,0x7efff13d],[315,0x7effe6fc,19152,3885,0x7effc938,945],[45,0x7efff683,18270,0x7effbb19,0x7effb4f2,7650],[0x7efffe99,8175,0x7eff93b9,0x7efffd8b,19635,0x7efff9da],[10,1260,0x7effc311,22260,16380,0x7effdd24],[0x7effffa7,0x7efff629,18270,0x7effe9db,0x7effc4f1,1575],[1,360,3150,0x7effcd25,0x7effe9db,6048],[0x7efffff7,0x7efffcb9,0x7efff629,4830,5880,0x7efffc50],[45,1260,1260,0,0x7efff764],[0x7effff89,0x7efffb15,0x7efffe99,0x7efffcc8,315],[210,840,45,330],[0x7effff05,0x7efffe99,0,0x7effffd4],[210,90,0],[0x7effff89,0x7efffff7,0],[45,0],[0x7efffff7,0],[1],[0]],
    [[0,0,0,540,695],[0,0,0,3780,3510,0x7efffb15],[0,0,11340,1440,0x7effced3,576],[0,0,18900,0x7eff9a49,0x7eff687b,12600],[0,18900,0x7efed14f,0x7eff9035,70425,0x7efff025],[0,11340,0x7efe677d,85260,149400,0x7eff400d],[3780,0x7efed569,220500,76860,0x7efd28bd,12285],[540,0x7eff8e19,215460,0x7efd3751,0x7efbda85,100800],[0x7effeef4,97860,0x7efb253b,0x7eff1d99,266910,0x7effaf25],[110,15480,0x7efd2bc9,236040,248220,0x7efe2c6d],[0x7efffc23,0x7eff84f5,213360,0x7eff962f,0x7efcc035,21000],[10,3960,40320,0x7efdc859,0x7efe7155,83160],[0x7effff9e,0x7effdbe9,0x7eff7d93,45360,87990,0x7effcdcd],[440,13860,17640,9240,0x7eff84f5],[0x7efffb7e,0x7effc9dd,0x7effea35,0x7effc8ed,4410],[1980,9240,900,5040],[0x7efff6fb,0x7efff089,0x7effffd4,0x7efffd6d],[1848,990,0],[0x7efffc23,0x7effff93,0],[330,0],[0x7effffca,0],[0],[1]]]
theorem rank_46_11 : (CJ0.blockMatrix source 46 ((11 : ℤ)-22)).rank ≤ 101 :=
  Fast.cell (z := b46_11) (Fast.bands [(0,27,20),(1,28,18),(2,29,16),(3,30,14),(4,31,12),(5,32,10),(6,33,8),(7,34,6),(8,35,4),(9,36,2)]) (by decide +kernel) (by decide +kernel)

private def b50_9 : CJ1.Block where
  bank := .leftLow
  cap := 86
  free := [(7,2),(7,3),(8,0),(8,1)]
  vectors := [
    [[0x14950d37,0x54d1b253,0x68dae375,0x12ad254b,0x54c11f9c,0x466d62d8,0x3d4d4aa1,0x32ec95d6,0x3b84d635,0x77e5d997,0x1a96441b,0x432a446e,0x7621b0de,0x5e8044c2,0x238ac3bb,0x1075d90d,0x6358d9fe,0x788572fd],[0x51bb56c5,0x3100e573,0x4da40833,0x3b4b6697,0x25129573,0x46cfbf0f,0x48f5d38d,0x118613e6,0x7042d1b0,0x547eb85e,0x79944506,0x6b4c49f4,0x2f334cc3,0x2bab671b,0x556e8558,0x4e08c5f],[0x41b5ef68,0x66742ad,0x4acb78eb,0x21ffadb1,0x1cd087ee,0x36a0a3b1,0x5d81a930,0x295041fe,0x238be3a2,0x21392277,0x409dc6a6,0xbfdacb0,0x77ac2e4b,0x4e8ba269],[0x6384d721,0x3d87dcc1,0x52b5c7e7,0x1a9aba73,0x2fffdc61,0x604fcaa,0x90db6b8,0x1b1d911f,0x3fad83ad,0x4215c97f,0x7ec9a0f3,0x1793e9dc],[0x38280def,0x40e5c66d,0x5c161f2,0x6276e0bc,0x16d4b1a9,0x5ab672b0,0x1fbd446f,0xb9a6d06,0x29d3efaa,0x5dd2717a],[0x3e9f93d3,0x79041271,0x2f468e5b,0x2c2cf196,0x562db067,0x1fbfc877,0x6850c540,0x3ed14aaa],[0x76eb68cd,0x5065d38b,0x4a976ef0,0x24492463,0x3f7ffd79,0x24490bac],[0x620b8cdc,0x2f8e1c7b,1,0],[0,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x4c8676cb,0x4761da05,0x297f51a8,0x17a828d8,0xc01a3f5,0x668698e7,0xc6bc138,0x1fdd4991,0x5d9445ee,0x5546f198,0x6e34f2da,0x6c6f896d,0x243b42f2,0x168336ea,0x36fb2a53,0x318ed28f,0x3c4a794a,0x68a8a4a9],[0x1b9b08c,0x46bd466c,0x438089b8,0x5870a94f,0x5e3f123d,0x563f6d1c,0x2a98a60c,0x45847afb,0x44224242,0x140fb0b8,0x59a77a43,0x58b3a3e7,0x4e21dfb8,0x7e65d717,0x376ffec9,0x1c1b7846],[0x31e29eb4,0x422b0675,0x4c6549e3,0x1deee4c5,0x2bc1a044,0xa829152,0xbde79b4,0x65186601,0x12351618,0x5afaedc0,0x7706889d,0x57cc0a2e,0x1291626d,0x509de6f6],[0x5e014142,0x45c9fcee,0x263e0730,0xb68bf28,0x27423c70,0x8aa44c3,0x51a4fad6,0x2d5dab74,0x72baea01,0x473add49,0x864df35,0x59402ae9],[0x7159835,0x5db90ca5,0x19dd710b,0x3a76b75,0x76db26ce,0x4fd426e9,0x2c7372c6,0x11e399ab,0x32b234f6,0x6375dcc1],[0x2b1fa38f,0x17171867,0x57d87144,0x4f5e5fbe,0x4d1b6e5a,0x130cd219,0x57fe5002,0x8af90d9],[0x4b1f634f,0x7c030304,0x79862c0e,0x4892492b,0x3f800047,0x15c57ede],[0x6714d775,0x1b9baf47,0,1],[0,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x24492507,0x1224a51f,98612,0x14446c,0xca44eb,0x63b34d0,0x28700df8,0x3aaf3009,0x1112f4ec,0x28aa20a6,0x7c7cfaf7,0x73238e50,0x2d1225c1,912667,0x11684a09,0x3a1b81d5,0x30817164,0x4f45a106],[87,3533,70971,0x1232ec28,0x491f6d8a,0x7125fec4,0x6417340a,0x28919960,0x417fe9d2,0x52090297,0x2a500c3,0x68dab6a8,0x6f4db26d,0x213631a6,0x6e538f5d,0x4ce2ad0],[0x48924963,2466,48745,0x6ce52672,0x5e81b6,0x6fb3ef66,0x243ef9b9,0x4f7cddb1,0x49ea3e0c,0x4ecb47ec,0xbc24502,0x7859676,0x2de1982b,0x588f67e6],[41,0x48924f6d,31370,0x3673e8e7,0x1260651d,0x13efd71d,0xb63e6aa,0x3d656af2,0xdfb78d8,0x18deae80,0x2948489e,0x24b44310],[0x244924ab,0x122495fb,0x1224d9cd,0x367151cd,0x124770a9,0x10d28fc,0x6bb47f6,0x5b147dcd,0x94cbc8a,0x27ba9b1d],[0x366db6e8,0x1224941c,0x5ab6fec4,0x12265ebe,0x11b539,0x8c145f,0x39b24a3,0x26622cbc],[0x366db6e0,158,0x12249e62,41820,437325,0x39157e],[0x24492493,0x12249250,0,0],[1,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x4621ce34,0x6cb46582,0x35e51133,0x2cd241e6,0x34ce41ab,0x3863b549,0x102b201,0x3f84ea05,0x76597e2c,0x6bb83fe,0x42d8e2d,0x78da6576,0x3d45010c,0x5d4ed958,0x2c88bba4,0x23b35500,0x6f47b565,0xf4d1895],[0x22af53e4,0x19146f7a,0x119bef93,0x3c24ef7f,0x7b2c486d,0xab455f6,0x1d29a78,0x176e9aae,0x19e71e5e,0x4a9a2ddd,0x933107,0x20e4b129,0x590d633,0x6563a92d,0x5fe12e2a,0x7e895cad],[0x73b7c773,0x7898bd0a,0x691f2c0c,0x6f249a21,0x622ca5b6,0x3018e72a,0x4e5023f4,0x64f04fd8,0x4e06aaa1,0x272405e6,0x339db238,0x4c054a53,0x3952d603,0x4392b243],[0x3b3b28df,0x2dd08495,0x6bca3462,0x6d775eb1,0x52046e25,0x2748a561,0x361b0f6c,0x228e3ac1,0x68ba19ea,0x79a892e0,0x45b46a54,0x7bcfcb5c],[0x7739782a,0x564afc83,0x7da098f,0x7a45f6b6,0x75c5ab50,0x244160cb,0x3f4eb713,0x7b5e4952,0x548ea985,0x605910e],[0x29b2b552,0x13975b38,0x696d3fc4,0x606e6daa,0x911c293,0x3f7be67d,0x75d3089d,0xdad2a38],[0x50a6e059,0x444d71b,0x283fe61,0x5ab6d64f,0x7effcbea,0x5ab527f0],[0x6d15f93e,0x47e2a692,0,0],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_50_9 : (CJ0.blockMatrix source 50 ((9 : ℤ)-22)).rank ≤ 86 :=
  Fast.cell (z := b50_9) (Fast.bands [(28,28,1),(29,29,2),(30,30,3),(31,31,4),(32,32,5),(33,33,6),(34,34,7),(35,35,8),(36,36,9),(37,37,10),(38,39,10),(39,41,9),(40,43,8),(41,45,6),(42,47,4),(43,49,2)]) (by decide +kernel) (by decide +kernel)

private def b57_5 : CJ1.Block where
  bank := .rightLow
  cap := 59
  free := [(8,2),(10,2),(12,2)]
  vectors := [
    [[0,0x7f000000],[0,0x7efffffe,2],[0x7efffffe,9,0x7f000000],[0x7f000000,12,0x7efffff8],[5,0x7effffef,3],[0,0x7efffff7,12],[0,10,0x7efffffe],[0,0,0x7efffffc],[0,0,1],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0],[0,0],[0],[0]],
    [[0,0x7efffffd],[0,0x7efffff5,7],[0x7efffff5,32,0x7efffffe],[0x7efffffd,42,0x7effffe5],[16,0x7effffcb,8],[0x7f000000,0x7effffe9,30],[5,16,0x7efffffb],[0,0x7efffff7,0x7efffffd],[0,10,0],[0,0,0x7efffffc],[0,0,1],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0],[0,0],[0],[0]],
    [[0,0x7efffff7],[0,0x7effffe3,15],[0x7effffe3,70,0x7efffffb],[0x7efffff7,90,0x7effffca],[30,0x7effff9d,15],[0x7efffffc,0x7effffe3,50],[20,10,0x7efffff7],[0x7f000000,0x7effffe3,0],[5,20,0],[0,0x7efffff7,0x7efffffc],[0,10,0],[0,0,0x7efffffc],[0,0,1],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0],[0,0],[0],[0]]]
theorem rank_57_5 : (CJ0.blockMatrix source 57 ((5 : ℤ)-22)).rank ≤ 59 :=
  Fast.cell (z := b57_5) (Fast.bands [(0,43,15),(1,44,13),(2,45,11),(3,46,9),(4,47,7),(5,48,5),(6,49,3),(7,50,1)]) (by decide +kernel) (by decide +kernel)

private def b62_4 : CJ1.Block where
  bank := .leftLow
  cap := 35
  free := [(5,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0x7eef6dc9],[0,0,0,0,0,0,0,0,123410],[0,0,0,0,0,0,0x7effd329],[0,0,0,0,820],[0,0,0x7effffd9],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_62_4 : (CJ0.blockMatrix source 62 ((4 : ℤ)-22)).rank ≤ 35 :=
  Fast.cell (z := b62_4) (Fast.bands [(40,40,1),(41,41,2),(42,42,3),(43,43,4),(44,44,5),(45,46,5),(46,48,5),(47,50,5),(48,52,5),(49,54,5),(50,56,5),(51,58,4),(52,60,3),(53,62,1)]) (by decide +kernel) (by decide +kernel)

private def b66_1 : CJ1.Block where
  bank := .rightLow
  cap := 18
  free := [(1,0),(2,0),(4,0),(6,0)]
  vectors := [
    [[],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]],
    [[],[0],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]],
    [[],[0],[0],[0x7f000000],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]],
    [[],[0],[0],[0x7f000000],[0],[0x7f000000],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]]]
theorem rank_66_1 : (CJ0.blockMatrix source 66 ((1 : ℤ)-22)).rank ≤ 18 :=
  Fast.cell (z := b66_1) (Fast.bands [(0,57,10),(1,58,8),(2,59,6),(3,60,4),(4,61,2)]) (by decide +kernel) (by decide +kernel)

private def b69_0 : CJ1.Block where
  bank := .rightLow
  cap := 8
  free := [(2,0),(4,0),(6,0)]
  vectors := [
    [[],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]],
    [[],[],[0],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]],
    [[],[],[0],[],[0],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]]]
theorem rank_69_0 : (CJ0.blockMatrix source 69 ((0 : ℤ)-22)).rank ≤ 8 :=
  Fast.cell (z := b69_0) (Fast.bands [(0,62,8),(1,63,6),(2,64,4),(3,65,2)]) (by decide +kernel) (by decide +kernel)

private def b74_0 : CJ1.Block where
  bank := .leftLow
  cap := 3
  free := [(1,0)]
  vectors := [
    [[0,0,0x7effffcd],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_74_0 : (CJ0.blockMatrix source 74 ((0 : ℤ)-22)).rank ≤ 3 :=
  Fast.cell (z := b74_0) (Fast.bands [(52,52,1),(53,54,1),(54,56,1),(55,58,1),(56,60,1),(57,62,1),(58,64,1),(59,66,1),(60,68,1),(61,70,1),(62,72,1)]) (by decide +kernel) (by decide +kernel)

end CurveList179876
