import ProximityPrize.SubmissionLower.CurveList179876Defs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace CurveList179876
private def b37_18 : CJ1.Block where
  bank := .leftLow
  cap := 130
  free := [(10,0),(10,1)]
  vectors := [
    [[0x7effff85,0x7effefee,0x7efefc06,0x7ef5540d,0x7eae0cf1,0x7d159ab9,0x75b2c939,0x5952d851,0x7c22ff62,0x796a8d90,0xae1d674,0x6ee0c673,0x17b3f1d5,0x30c1a40b,0x1a3ea934,0x51f0dead,0x3192cdd4,0x641ae6dd,0x4e9e66b9,0x5c29abc5,0xbba0698,0x5307d120],[0x3f7fff91,0x7efff1fa,0x7eff23d5,0x7ef73aa1,0x7ebea05d,0x7d843f09,0x7801caa9,0x637fe1c1,0x22fb4eef,0x732b55cf,0x5bad1eae,0x2465daec,0x7caa1f5c,0x61225741,0x1f2bc7e7,0x3d8356d8,0x5f657f11,0x700b6fe1,0x685136eb,0x59e7eace],[0x7effff9e,0x7efff3ed,0x7eff4821,0x7ef8e4b1,0x7ecc9789,0x7dde1051,0x79d09201,0x6b314c31,0x3ea0379d,0x49710082,0x424cd9e4,0x423a7878,0x63aa37e7,0x24860e8,0x7e229b65,0x66dfc721,0x3b5cb458,0x5d2dc736],[0x3f7fffaa,0x7efff5c7,0x3f7f690f,0x7efa571e,0x3f5840cc,0x7e2637f5,0x3bb6c945,0x70f01024,0x1310cf20,0x5e56c0b,0x1df2eee7,0x23dd7ff2,0x69715297,0x7202b53f,0x1333739f,0x7517d1b6],[0x7effffb7,0x7efff788,0x7eff86c6,0x7efb9697,0x7ee1e459,0x7e5f81ea,0x7c488848,0x752bd429,0x60c15653,0x2eccf508,0x45089b9f,0x78838f5,0x62da5fa2,0x6862b68a],[0x3f7fffc3,0x7efff930,0x7effa16a,0x7efca799,0x3f69c478,0x7e8c6408,0x7d16be97,0x783ec789,0x2b35382f,0x4a8df2c4,0x96714b0,0x17e80d12],[0x7effffd0,0x7efffabf,0x7effb921,0x7efd8e6f,0x7ef01dcc,0x7eaf0511,0x7daf9509,0x7a7108f5,0x7195022c,0x5d1e5393],[0x3f7fffdc,0x7efffc35,0x3f7fce10,0x7efe4f32,0x7ef5278a,0x7ec9436d,0x7e1ec73a,0x7bfba293],[0x7effffe9,0x7efffd92,0x7effe05e,0x7efeedc9,0x7ef913bd,0x7edcbb9b],[0x3f7ffff5,0x7efffed6,0x7efff02f,0x7eff6de9],[1,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[5,166,2686,28237,216920,0x13d060,0x603d40,0x185e918,0x5402a4c,0xfa1b698,0x28a47458,0x5d14622c,0x3e0059e7,0x57edfabe,0x2d1f159c,0x2806ac22,0x1c044596,0x4def27cb,0xcc0ef7a,0x42f3ff45,0x7464e60,0xc5eb7da],[0x3f800005,145,2277,23232,173228,0xf5c28,0x486de0,0x11ce360,0x3b9596e,0xac21ecc,0x1b202644,0x3c2faa80,0x763da4d4,0x4f9b6c37,0x441ca4ae,0x4401239d,0x343d21a7,0x75ec05d2,0x75ec05d2,0x33a0f4bc],[4,125,1904,18848,136400,769544,0x35c5f0,0xcd6f80,0x29baa60,0x750759c,0x11e38030,0x2673c960,0x490f31d0,0x7b31fa58,0x39dde5af,0x78471ebf,0x290c21c6,0x3c03c4dc],[0x3f800004,106,0x3f80061e,15035,0x3f819ca1,578956,0x3fa75258,0x920d45,0x414d6d71,0x4e93906,0x4b27e5d8,0x1845e3eb,0x6c14a3df,0x4877c070,0x28fef6a1,0x6d3378c],[3,88,1260,11745,80185,427518,0x1c44a2,0x664077,0x13a857b,0x3418be4,0x7812048,0xf23fdb1,0x1adcc219,0x2a094c62],[0x3f800003,71,986,8932,0x3f80e7f2,308763,0x13eec1,0x466950,0x40535d13,0x221c643,0x4c688e8,0x9557ff4],[2,55,742,6552,42588,217035,900900,0x2fa198,0x8c04f6,0x1610f43],[0x3f800002,40,0x3f80020f,4563,29250,147420,605475,0x1f9e06],[1,26,338,2925,18850,95680],[0x3f800001,13,175,1600],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_37_18 : (CJ0.blockMatrix source 37 ((18 : ℤ)-22)).rank ≤ 130 :=
  Fast.cell (z := b37_18) (Fast.bands [(15,15,1),(16,16,2),(17,17,3),(18,18,4),(19,19,5),(20,20,6),(21,21,7),(22,22,8),(23,23,9),(24,24,10),(25,25,11),(26,26,11),(27,27,11),(28,28,10),(29,29,9),(30,30,8),(31,31,7),(32,32,6),(33,33,5),(34,35,3),(35,37,1)]) (by decide +kernel) (by decide +kernel)

private def b42_13 : CJ1.Block where
  bank := .rightLow
  cap := 116
  free := [(21,0),(22,0)]
  vectors := [
    [[0,0,0,0,1,1],[0,0,0,0,9,6,0x7effffff],[0,0,0,36,0,0x7effffe9,1],[0,0,0,84,0x7effffa1,0x7effffa7,26],[0,0,126,0x7efffe87,0x7effffc5,180,0x7efffff8],[0,0,126,0x7efffd0d,504,480,0x7effff7a],[0,84,0x7efffc65,1764,210,0x7efffd6d,36],[0,36,0x7efffd31,2856,0x7efff91d,0x7efffb15,384],[9,0x7efffea2,2700,0x7effeda1,0,1386,0x7effffad],[1,0x7effff9f,1530,0x7effe981,4116,1764,0x7efffd61],[0x7efffff5,484,0x7efff0b6,7560,0x7efffb69,0x7efff91d,126],[66,0x7efffa6b,6480,0x7effe861,0x7efffb69,756],[0x7effff25,2805,0x7effe3f3,2520,1344,0x7effff83],[495,0x7efff10d,5292,0,0x7efffddf],[0x7efffce9,3696,0x7efff683,0x7efffde5,84],[924,0x7efff635,540,240],[0x7efffce9,1155,45,0x7effffdd],[495,0x7efffeb7,0x7effffcb],[0x7effff25,44,9],[66,2],[0x7efffff5,0x7f000000],[1],[0]],
    [[0,0,0,0,12,13],[0,0,0,0,108,82,0x7effffe7],[0,0,0,432,45,0x7efffec3,13],[0,0,0,1008,0x7efffbf9,0x7efffb15,342],[0,0,1512,0x7effef1b,0x7efffad9,2430,0x7effff8b],[0,0,1512,0x7effdd8d,4788,6960,0x7efff8f9],[0,1008,0x7effd583,19404,5670,0x7effdc61,477],[0,432,0x7effdeb9,32592,0x7effc1fd,0x7effb489,5208],[108,0x7effefba,31320,0x7eff3a79,0x7effdd8d,19782,0x7efffb99],[12,0x7efffb73,17910,0x7eff02e1,37632,29988,0x7effdb95],[0x7effff72,5698,0x7eff5066,80640,588,0x7eff98a5,1722],[780,0x7effbf1f,72360,0x7eff1f91,0x7eff9af1,10836],[0x7efff5f3,32010,0x7efed443,15120,22008,0x7efff91d],[5720,0x7eff5975,52164,10080,0x7effdfd9],[0x7effdcd0,39732,0x7effb303,0x7effd5d1,1218],[10296,0x7eff9c7d,1080,3960],[0x7effde7d,10560,2565,0x7efffdd9],[5148,0x7efff6fb,0x7efffbb7],[0x7efff7a0,0x7effffeb,153],[572,134],[0x7effffb3,0x7effffeb],[0],[1]]]
theorem rank_42_13 : (CJ0.blockMatrix source 42 ((13 : ℤ)-22)).rank ≤ 116 :=
  Fast.cell (z := b42_13) (Fast.bands [(0,21,22),(1,22,20),(2,23,18),(3,24,16),(4,25,14),(5,26,12),(6,27,10),(7,28,8),(8,29,6),(9,30,4),(10,31,2)]) (by decide +kernel) (by decide +kernel)

private def b45_11 : CJ1.Block where
  bank := .rightLow
  cap := 105
  free := [(20,1),(22,0)]
  vectors := [
    [[0,0,0,0,0x7f000000],[0,0,0,0,0x7efffff8,2],[0,0,0,0x7effffdd,27,0x7f000000],[0,0,0,0x7effffad,144,0x7effffe6],[0,0,0x7effff83,420,0x7effff29,9],[0,0,0x7effff83,756,0x7efffcb9,144],[0,0x7effffad,882,0x7efff89f,840,0x7effffdd],[0,0x7effffdd,672,0x7efff5ab,2520,0x7efffe5d],[0x7efffff8,324,0x7efff6d1,4410,0x7efff89f,84],[0x7f000000,90,0x7efffaf1,4704,0x7effeec7,756],[11,0x7efffe6c,3024,0x7effe909,2646,0x7effff83],[0,0x7effffca,1080,0x7effee49,4704,0x7efffc8f],[0,165,0x7efff89f,4536,0x7efff6d1,126],[0,0x7efffeb7,2268,0x7efff431,672],[0,462,0x7efff89f,1296,0x7effffad],[0,0x7efffe33,1080,0x7efffebd],[0,330,0x7efffe6c,36],[0,0x7effff5c,90],[0,55,0x7efffff8],[0,0x7efffff6],[0,1],[0],[0]],
    [[0,0,0,0,0x7efffff7],[0,0,0,0,0x7effffa7,19],[0,0,0,0x7efffe99,260,0x7efffff8],[0,0,0,0x7efffcb9,1395,0x7effff07],[0,0,0x7efffb15,4080,0x7efff818,80],[0,0,0x7efffb15,7350,0x7effe111,1305],[0,0x7efffcb9,8568,0x7effba47,7680,0x7efffec6],[0,0x7efffe99,6510,0x7eff9e8d,23100,0x7efff179],[0x7effffa7,3120,0x7effa9df,40320,0x7effbe61,720],[0x7efffff7,855,0x7effd121,42630,0x7eff676d,6510],[100,0x7efff1c4,26880,0x7eff3707,22680,0x7efffbe7],[0x7f000000,0x7efffe3f,9180,0x7eff6911,39690,0x7effe375],[11,1200,0x7effc4f1,36960,0x7effb55b,1008],[0x7effffca,0x7efff7cd,17010,0x7effa421,5250],[165,2520,0x7effcc53,9600,0x7efffd8b],[0x7efffeb7,0x7efff7cd,7020,0x7efff719],[462,1200,0x7efff683,240],[0x7efffe33,0x7efffe3f,495],[330,100,0x7effffd4],[0x7effff5c,0x7efffff7],[55,0],[0x7efffff6],[1]]]
theorem rank_45_11 : (CJ0.blockMatrix source 45 ((11 : ℤ)-22)).rank ≤ 105 :=
  Fast.cell (z := b45_11) (Fast.bands [(0,25,21),(1,26,19),(2,27,17),(3,28,15),(4,29,13),(5,30,11),(6,31,9),(7,32,7),(8,33,5),(9,34,3),(10,35,1)]) (by decide +kernel) (by decide +kernel)

private def b48_11 : CJ1.Block where
  bank := .leftLow
  cap := 89
  free := [(8,1)]
  vectors := [
    [[0x38078788,0x433c3c3e,0x6c52d2ed,0x59a5a6f8,0x700f1bec,0x59a60762,0x2cd52d83,0x434857c5,0x383c7ffc,0xc81c61,0x42145da7,0x7811070,0x1362bfcc,0x2cbc7f88,0x5cab082c,0x2dfafe2f,0x25e78cef,0x328040f5],[0x38078788,0xb34b4b6,0x611e1e37,0x778788c2,0x7787932b,0x611e7438,0x4ab6b94c,0x77919e7a,0x3faae183,0x401d3adf,0x1f722c8,0x589eda8,0xdd8d224,0x1ee3ad64,0x3dc75ac8,0x6f33a368],[0x38078788,0x522d2d2f,0xef0f108,0x689697ba,0xef0fb71,0x522d78c7,0x77894086,548340,0x3fa2838f,0x7ab750,0x17c6b78,0x40d8230,0x9cb4ff4,0x15185d70],[0x38078788,0x1a25a5a7,0x73cb4b62,0x73cb4c59,0x1a25af19,0x3807c9ae,0x3f8176d8,0x3f86e71d,0x1b9c72,0x5f1ade,0x11d509a,0x2f03196],[0x38078788,0x611e1e20,0x12ad2d42,0x611e1f17,0x38079003,14763,0x3f813d2d,371184,0x15f282,0x49285c],[0x38078788,0x29169698,0x689696ab,0x7787886d,0x3f800797,0x3f803215,68376,302808],[0x38078788,0x700f0f11,0x7787879b,210,0x3f8006c5,11088],[0x38078788,0x38078789,0x3f800012,0x3f8000c1],[0x38078788,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_48_11 : (CJ0.blockMatrix source 48 ((11 : ℤ)-22)).rank ≤ 89 :=
  Fast.cell (z := b48_11) (Fast.bands [(26,26,1),(27,27,2),(28,28,3),(29,29,4),(30,30,5),(31,31,6),(32,32,7),(33,33,8),(34,34,9),(35,35,10),(36,36,11),(37,37,11),(38,39,10),(39,41,8),(40,43,6),(41,45,4),(42,47,2)]) (by decide +kernel) (by decide +kernel)

private def b54_7 : CJ1.Block where
  bank := .leftLow
  cap := 71
  free := [(7,1)]
  vectors := [
    [[0x16cb7cb8,0x20906908,0x61b13b2f,0x4e2763fc,0x4e2772cf,0x61b1c460,0x753ebde1,0x6b8b186f,0x661719,0x5659b6dc,0x5ae58af9,0x14639844,0x3b77d171,0x60ea99ec,0x534d8f62,0x3b2dfeae],[0x16cb7cb8,0x9c4ec50,0x57ec4edf,0x753b151e,0x57ec5db2,0x9c566ae,0x6b795733,0x11c13c,0x5455dd,0x560560ff,0x4e029fa,0xf836e4a,0x2bf46327,0x34f636c5],[0x16cb7cb8,0x71f96f99,0x64f2df47,0x104835d7,0x47a427db,0x41213ed4,0x2a58185f,0x54b9a8de,0x2a9aad00,0x2b6ab3ff,0x587575fc,0x360df84f],[0x16cb7cb8,0x5b2df2e1,0x9c4ec66,0x6834971,0x4120de6a,24682,0x2a57b7f5,0x2a61f0e9,0x38bc17,0x2b31f7e8],[0x16cb7cb8,0x44627629,0x4462763e,0x4120d334,2870,21812,0x2a5762c1,691752],[0x16cb7cb8,0x2d96f971,0x16cb7ccd,0x2a555667,0x54aab4d0,0x2a55a065],[0x16cb7cb8,0x16cb7cb9,20,0x2a555653],[0x16cb7cb8,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_54_7 : (CJ0.blockMatrix source 54 ((7 : ℤ)-22)).rank ≤ 71 :=
  Fast.cell (z := b54_7) (Fast.bands [(32,32,1),(33,33,2),(34,34,3),(35,35,4),(36,36,5),(37,37,6),(38,38,7),(39,39,8),(40,41,8),(41,43,8),(42,45,8),(43,47,7),(44,49,6),(45,51,4),(46,53,2)]) (by decide +kernel) (by decide +kernel)

private def b61_3 : CJ1.Block where
  bank := .rightLow
  cap := 40
  free := [(4,1),(6,1),(8,1)]
  vectors := [
    [[0x7f000000],[0x7f000000,2],[3,0x7f000000],[0,0x7efffffe],[0,1],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0],[0]],
    [[0x7effffff],[0x7effffff,3],[4,0x7f000000],[0x7f000000,0x7effffff],[3,0],[0,0x7efffffe],[0,1],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0],[0]],
    [[0x7efffffe],[0x7efffffe,3],[3,0x7f000000],[0x7efffffe,0],[6,0],[0x7f000000,0x7efffffe],[3,0],[0,0x7efffffe],[0,1],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0],[0]]]
theorem rank_61_3 : (CJ0.blockMatrix source 61 ((3 : ℤ)-22)).rank ≤ 40 :=
  Fast.cell (z := b61_3) (Fast.bands [(0,49,13),(1,50,11),(2,51,9),(3,52,7),(4,53,5),(5,54,3),(6,55,1)]) (by decide +kernel) (by decide +kernel)

private def b65_1 : CJ1.Block where
  bank := .rightLow
  cap := 20
  free := [(2,0),(4,0)]
  vectors := [
    [[],[0x7f000000],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]],
    [[],[0x7f000000],[0],[0x7f000000],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]]]
theorem rank_65_1 : (CJ0.blockMatrix source 65 ((1 : ℤ)-22)).rank ≤ 20 :=
  Fast.cell (z := b65_1) (Fast.bands [(0,55,11),(1,56,9),(2,57,7),(3,58,5),(4,59,3),(5,60,1)]) (by decide +kernel) (by decide +kernel)

private def b68_0 : CJ1.Block where
  bank := .rightLow
  cap := 9
  free := [(2,0),(4,0)]
  vectors := [
    [[],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]],
    [[],[],[0],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]]]
theorem rank_68_0 : (CJ0.blockMatrix source 68 ((0 : ℤ)-22)).rank ≤ 9 :=
  Fast.cell (z := b68_0) (Fast.bands [(0,60,9),(1,61,7),(2,62,5),(3,63,3),(4,64,1)]) (by decide +kernel) (by decide +kernel)

private def b71_1 : CJ1.Block where
  bank := .leftLow
  cap := 8
  free := [(2,0)]
  vectors := [
    [[0,0,0,0,1225],[0,0,0x7effffd0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_71_1 : (CJ0.blockMatrix source 71 ((1 : ℤ)-22)).rank ≤ 8 :=
  Fast.cell (z := b71_1) (Fast.bands [(49,49,1),(50,50,2),(51,52,2),(52,54,2),(53,56,2),(54,58,2),(55,60,2),(56,62,2),(57,64,2),(58,66,2),(59,68,2),(60,70,1)]) (by decide +kernel) (by decide +kernel)

end CurveList179876
