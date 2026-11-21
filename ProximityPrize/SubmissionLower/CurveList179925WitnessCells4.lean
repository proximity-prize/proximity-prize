import ProximityPrize.SubmissionLower.CurveList179925WitnessDefs
import ProximityPrize.SubmissionLower.CurveList179925WitnessCells3

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace CurveList179925Witness
private def b38_16 : CJ1.Block where
  bank := .leftLow
  cap := 109
  free := [(9,1)]
  vectors := [
    [[0x22313b14,0x35bb13b3,0x186c4edc,0xea76372,0x753b1b90,0x753b4478,0x4e285654,0x57f04111,0x7548e3ba,0x61daab2c,0x6bbd0a,0xf4dc2e,0x1e9b85c,0x47c4e3b7,0x70c7aefb,0x384ac1c5,0x269d7236,0x75dd254c,0x75dd254c,0x269d7236],[0x22313b14,0x1389d89f,0x4e2763d,0x9c4ed35,0x6b762e5b,0x9c5161d,0x44634037,0x138d00da,0x61bbe2e0,0x1ec84c,0x4cf4be,0xa7e770,0x141d0ec,0x468312cb,0x2a449c30,0xe062595,0x18974ca1,0x5d45d8ab],[0x22313b14,0x70589d8c,0x1389d8b2,0x753b1484,0x753b19d8,0x1389fc46,0x30d943f1,0x61b3bcea,534006,0x16a256,0x365268,0x719508,0xd03be4,0x45b2d6e7,0x6391c54a,0x2974604c],[0x22313b14,0x4e276278,0x4462763b,0x30d89e49,0x44627b8f,0x4e2780b8,0x61b1c33a,129456,404550,0x107610,0x25dc58,0x4bb8b0,0x848334,0x452e53b3],[0x22313b14,0x2bf62764,0x186c4ed7,0x186c4f72,0x2bf62c1d,0x2231549b,0x3f806e9f,0x3f818b12,0x3f84a135,0x3f8bd4dc,0x3f9a077d,0x3fb1b134],[0x22313b14,0x9c4ec50,0xea76287,0x9c4eceb,0x22313f32,5481,0x3f805936,78300,0x3f836f59,550275],[0x22313b14,0x6693b13d,0x2713b14b,0x61b13ba1,0x3f800392,0x3f8011d8,18270,60030],[0x22313b14,0x44627629,0x61b13b23,126,0x3f800314,3780],[0x22313b14,0x22313b15,0x3f80000e,0x3f800071],[0x22313b14,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_38_16 : (CJ0.blockMatrix source 38 ((16 : ℤ)-21)).rank ≤ 109 :=
  Fast.cell (z := b38_16) (Fast.bands [(17,17,1),(18,18,2),(19,19,3),(20,20,4),(21,21,5),(22,22,6),(23,23,7),(24,24,8),(25,25,9),(26,26,10),(27,27,11),(28,28,11),(29,29,10),(30,30,9),(31,31,8),(32,32,7),(33,33,6),(34,35,4),(35,37,2)]) (by decide +kernel) (by decide +kernel)

private def b42_11 : CJ1.Block where
  bank := .rightLow
  cap := 101
  free := [(21,0)]
  vectors := [
    [[0,0,0,0,0,0x7f000000],[0,0,0,0,0x7efffff7,1],[0,0,0,0,0x7effffd4,20],[0,0,0,0x7effff89,135,0x7efffff7],[0,0,0,0x7effff2f,480,0x7effff7a],[0,0,0x7effff05,1050,0x7efffd31,45],[0,0,0x7effff2f,1512,0x7efff7cd,480],[0,0x7effff89,1470,0x7efff13d,2100,0x7effff89],[0,0x7effffd4,960,0x7effeec7,5040,0x7efffbe7],[0x7efffff7,405,0x7efff2e1,7350,0x7efff13d,210],[0x7f000000,100,0x7efff9ad,6720,0x7effe34b,1512],[11,0x7efffe3f,3780,0x7effdf31,4410,0x7effff05],[0x7effffca,1200,0x7effe9db,6720,0x7efffa43],[165,0x7efff7cd,5670,0x7efff2e1,210],[0x7efffeb7,2520,0x7efff13d,960],[462,0x7efff7cd,1620,0x7effff89],[0x7efffe33,1200,0x7efffe6c],[330,0x7efffe3f,45],[0x7effff5c,100],[55,0x7efffff7],[0x7efffff6],[1]]]
theorem rank_42_11 : (CJ0.blockMatrix source 42 ((11 : ℤ)-21)).rank ≤ 101 :=
  Fast.cell (z := b42_11) (Fast.bands [(0,22,21),(1,23,19),(2,24,17),(3,25,15),(4,26,13),(5,27,11),(6,28,9),(7,29,7),(8,30,5),(9,31,3),(10,32,1)]) (by decide +kernel) (by decide +kernel)

private def b45_10 : CJ1.Block where
  bank := .rightLow
  cap := 91
  free := [(16,2),(17,2),(18,1),(19,1),(21,0)]
  vectors := [
    [[0,0,0,0x7f000000,0x7f000000],[0,0,0,0x7efffffa,0x7efffffc,1],[0,0,0x7effffec,0,13],[0,0,0x7effffde,49,42,0x7efffffa],[0,0x7effffde,140,14,0x7effffc9],[0,0x7effffec,189,0x7effff52,0x7effff83,21],[0x7efffffa,140,0x7efffe72,0,119],[0x7f000000,55,0x7efffe79,385,175,0x7effffde],[9,0x7effff45,588,0x7effff98,0x7effff75],[0,0x7effffdd,364,0x7efffe17,0x7effff98,35],[0,84,0x7efffe4f,196,91],[0,0,0x7effff83,322,0,0x7effffec],[0,0,126,0x7effff75,0x7effffe5],[0,0,0x7effffad,28,7],[0,0,36,1],[0,0,0x7efffff8,0x7f000000],[0,0,1],[0,0,0],[0,0],[0,0],[0],[0]],
    [[0,0,0,0x7efffff8,0x7efffff7],[0,0,0,0x7effffc2,0x7effffcc,10],[0,0,0x7effff44,0x7effffe5,133],[0,0,0x7efffec6,385,462,0x7effffba],[0,0x7efffec6,1190,350,0x7efffdb5],[0,0x7effff44,1645,0x7efffb38,0x7efffa43,217],[0x7effffc2,1232,0x7efff34a,0x7efffd45,1295],[0x7efffff8,487,0x7efff2fd,2625,2275,0x7efffe8e],[80,0x7efff9a5,4704,175,0x7efff9b7],[0,0x7efffec6,3052,0x7efff29b,0x7efff908,385],[0,720,0x7efff27f,784,1155],[0,0,0x7efffbe7,2338,588,0x7effff0c],[0,0,1008,0x7efffcd5,0x7efffe41],[0,0,0x7efffd8b,28,91],[0,0,240,73],[0,0,0x7effffd4,0x7efffff0],[0,0,0],[0,0,1],[0,0],[0,0],[0],[0]],
    [[0,0,0,0x7efffff8,0x7efffff7],[0,0,0,0x7effffc2,0x7effffcb,9],[0,0,0x7effff44,0x7effffdd,126],[0,0,0x7efffec6,357,450,0x7effffc2],[0,0x7efffec6,1134,378,0x7efffde5],[0,0x7effff44,1575,0x7efffbd2,0x7efffa97,189],[0x7effffc2,1176,0x7efff470,0x7efffd0d,1155],[0x7efffff8,459,0x7efff431,2205,2079,0x7efffec6],[72,0x7efffa61,4032,315,0x7efffa97],[0x7f000000,0x7effff05,2520,0x7efff557,0x7efff9da,315],[9,504,0x7efff5ab,504,945],[0,0x7effffdd,0x7efffd8b,1638,504,0x7effff44],[0,84,504,0x7efffe09,0x7efffeb1],[0,0x7effff83,0x7effff05,0,63],[0,126,72,45],[0,0x7effffad,0x7efffff8,0x7efffff8],[0,36,0],[0,0x7efffff8,0],[0,1],[0,0],[0],[0]],
    [[0,0,0,0x7effffa7,0x7effff95],[0,0,0,0x7efffd8b,0x7efffda6,98],[0,0,0x7efff89f,0x7efffdc1,1386],[0,0,0x7efff3b3,3150,5148,0x7efffd4c],[0,0x7efff3b3,10836,5460,0x7effe861],[0,0x7efff89f,15372,0x7effe003,0x7effc005,2106],[0x7efffd8b,11592,0x7eff9533,0x7effcec9,13230],[0x7effffa7,4554,0x7eff8e79,16380,25830,0x7efff20f],[720,0x7effc8e1,36792,10710,0x7effc005],[0x7efffff8,0x7efff629,24192,0x7effac55,0x7effac55,3654],[80,5040,0x7effa085,0x7efffcb9,11718],[0,0x7efffec6,0x7effe765,13860,8568,0x7efff725],[0,720,5040,0x7efff431,0x7effee49],[0,0x7efffbe7,0x7efff629,0x7efffc11,798],[0,1008,720,738],[0,0x7efffd8b,0x7effffa7,0x7effff83],[0,240,0],[0,0x7effffd4,0],[0,0],[0,1],[0],[0]],
    [[0,0,0,0x7effffd4,0x7effffa7],[0,0,0,0x7efffec6,0x7efffdb8,81],[0,0,0x7efffc50,0x7efffb15,1225],[0,0,0x7efff9da,0x7efffec6,5355,0x7efffdae],[0,0x7efff9da,3150,9990,0x7effe9db],[0,0x7efffc50,5985,6825,0x7effb73b,1890],[0x7efffec6,5040,0x7efff0fe,0x7eff955d,13275],[0x7effffd4,2115,0x7effdb17,0x7effc3b6,33075,0x7efff2d2],[360,0x7effe945,3780,35595,0x7effba47],[0,0x7efffb15,7980,12600,0x7eff8144,3675],[0,2520,0x7effeec7,0x7effa769,14175],[1,0,0x7efff3b3,0x7efff6fb,17010,0x7efff668],[0x7efffff7,0,2520,5460,0x7effe765],[45,0,0x7efffb15,0x7efff13d,945],[0x7effff89,0,360,1245],[210,0,0x7effffd4,0x7effff5c],[0x7effff05,0,0],[210,0,0],[0x7effff89,0],[45,0],[0x7efffff7],[1]]]
theorem rank_45_10 : (CJ0.blockMatrix source 45 ((10 : ℤ)-21)).rank ≤ 91 :=
  Fast.cell (z := b45_10) (Fast.bands [(0,27,19),(1,28,17),(2,29,15),(3,30,13),(4,31,11),(5,32,9),(6,33,7),(7,34,5),(8,35,3),(9,36,1)]) (by decide +kernel) (by decide +kernel)

private def b49_8 : CJ1.Block where
  bank := .leftLow
  cap := 77
  free := [(7,0),(7,1),(7,2),(8,0)]
  vectors := [
    [[0x2a555877,0x2a55d4c4,0x2a5f56a9,0x552f1112,0x59bc474a,0x5191385d,0x2609f5e1,0x73755561,0x3a9e57f,0xd43fd15,0x6ab0ade5,0x4ba92a42,0x5055d0e2,0x4fdb358b,0x33281989,0x3afd2836,0x5cf5bd9f],[602,24046,475000,0x2ab3bf8b,0x39042e8,0x1b3accd4,0x569bf816,0x16381519,0x7437ad96,0x756c2f2,0x25742bd8,0x491d68b9,0x67c83d4d,0x4de10130,0x47ca2d70],[431,0x54aaecc0,0x2a5a5af9,0x409313,0x5713cbcb,0x3c95a78f,0x71e702a4,0x5dc8c567,0x4ba3c769,0x7ffa9ce,0x4be762cf,0x1630d1d2,0x450e0f91],[0x2a555676,0x2a5580e3,0x2a589ae1,0x2a7f0b95,0x2be1b26a,0xbaeaaf0,0x48c7dc24,0x3393ce3,0x62fda5fb,0x165c20d4,0x6ba8c9b3],[174,6659,127376,0x2a6e18ab,0xec1af8,0x7013859,0x2c04942a,0x6b921ccb,0x3dd4afa0],[88,0x54aab7cc,0x2a565211,836400,0x7c53da,0x3c98d2e,0x187e669c],[0x2a555574,0x2a5559e7,0x2a55b017,317135,0x32adca],[1,0,0],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x2a555527,0x2a554de9,0x2a54c005,0x54a2f16f,0x545ee9e2,0x280a83d7,0x1bbb7553,0x5abbb5de,0x10556d6b,0x56de303d,0x45bf713b,0x5a85fbf2,0x1c183345,0x233b2046,0x7a205041,0x2db20eb7,0xa19ca01],[0x7effffde,0x7efffa8a,0x7eff93f6,0x2a4fd48f,0x7ecac5df,0x7d68d7ef,0x20519719,0x49aab8e5,0x91c20bb,0x20b065cd,0x42a6c20d,0x12362b27,0x1ccd9389,0x5e55e9c,0x1d1b350],[0x7effffe8,0x54aaa6d5,0x2a550a95,0x7efc3d72,0x5486ae05,0x294479dd,0x7856cdf5,0x5bc3ac0a,0x5d3d7e92,0x78c4412f,0x70010620,0x4bed41d7,0x5ae85cd9],[0x2a555545,0x2a5552d0,0x2a5524bb,0x2a52e84c,0x2a3e3b2a,0x7e51555c,0x7abddd7b,0x687c37a8,0x18543996,0xe522a82,0x29faae6],[0x7efffff7,0x7efffe81,0x7effe335,0x2a53e51e,0x7ef23d7d,0x7e973139,0x7c6bd87b,0x713bc83e,0x3faa20a9],[0x7efffffc,0x54aaa9eb,0x2a5546c4,0x7eff426b,0x7ef8bef4,0x7ec7315e,0x7d8f8b4e],[0x2a555554,0x2a555514,0x2a555023,0x7effb7f4,0x7efd05a9],[0,1,0],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x2a555557,0x2a55558c,0x2a55599b,0x54aae342,0x66d16851,0x72f86f21,0x189bede0,0x7528cf3f,0x1c9b9b47,0x54ce05ec,0x43b59bfe,0x7067ba2e,0x442c3a64,0x39bd52ff,0x7b6d0be2,0x1024b70f,0x37438ac0],[1,40,0x244927aa,0x1830eb64,99970,0x5ac288cb,0x610c9fc8,0x13aca017,0x708ff69,0x52af9655,0x993f921,0x3f13193e,0x7c4ce9f8,0x182b2885,0x28d72e49],[0x1224924a,0x78f3cf5a,0x60c32e7,0x1224ade0,0x30628e6b,0x4ea64fdd,0x12559403,0x5bba4114,0x3b0daf6d,0x5b05fa48,0x71613ce0,0x4096a859,0x757432ad],[0x60c30c32,0x60c30c44,0x1830c471,0x1830d4e0,0x3c7a919e,0x12299907,0x1f65d1,0x12caac5f,0x151a3df3,0x5a68ee89,0x78075e5d],[0x6cdb6db8,11,0x1224931d,0x2a555fef,0x1224f7df,198357,0x131494,0x24af09d2,0x1d4c168],[0x366db6dc,0x1e3cf3d5,0x1830c378,0x122497c7,13805,108256,702372],[0x3c79e79f,0x60c30c5,0x3c79e7c6,545,5780],[0,0,1],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x54aaaad3,0x54aab0fa,0x54ab2997,0x2a5be8d8,0x2a9601c1,0x56a1749e,0x613b2bfc,0x19a2c82f,0x3f073ecf,0x6c176d98,0x33bdb91e,0x6b13dbc5,0x35acf09e,0x10106b53,0x3eb16772,0x4eab1f73,0x5b48e0b9],[29,1160,22985,0x54af419e,0x2c9b2e,0x1572ed0,0x5d299f7c,0x2d8f9aa8,0x53b82b48,0x5a52bd92,0x7da5e37e,0x30689754,0x4c24b6a4,0x65b0ea11,0x10e3ca35],[20,0x2a55586a,0x54aae6f8,200135,0x2a72ccce,0x558c1c68,0x58e6408,0x1dadefef,0x9baaa66,0x2a9311d9,0x5e7a9254,0x31013291,0x5f1c1753],[0x54aaaab8,0x54aaac9a,0x54aad04e,0x54ac9198,0x54bd0711,0x8cc7bc,0x37b000a,0x12a73896,0x562b4649,0x33273a23,0x31473d5c],[7,274,5377,0x54abbd85,688755,0x51d4a6,0x20e1f15,0xb2e4251,0x345589ec],[3,0x2a5555cf,0x54aab453,33660,343315,0x2a7f34,0x11c34e1],[0x54aaaaac,0x54aaaacb,0x54aaad8c,11305,129115],[0,0,0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_49_8 : (CJ0.blockMatrix source 49 ((8 : ℤ)-21)).rank ≤ 77 :=
  Fast.cell (z := b49_8) (Fast.bands [(28,28,1),(29,29,2),(30,30,3),(31,31,4),(32,32,5),(33,33,6),(34,34,7),(35,35,8),(36,36,9),(37,38,9),(38,40,9),(39,42,8),(40,44,6),(41,46,4),(42,48,2)]) (by decide +kernel) (by decide +kernel)

private def b56_4 : CJ1.Block where
  bank := .rightLow
  cap := 49
  free := [(7,2),(9,2)]
  vectors := [
    [[0,1],[0,3,0x7f000000],[3,0x7efffffb],[1,0x7efffff8,3],[0x7efffffd,9],[0,6,0x7efffffe],[0,0x7efffffd],[0,0,1],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0],[0],[0]],
    [[0,4],[0,12,0x7efffffe],[12,0x7effffed],[4,0x7effffe3,8],[0x7efffff5,24],[1,12,0x7efffffb],[0x7efffffd,0x7efffffd],[0,6,0],[0,0x7efffffd],[0,0,1],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0],[0],[0]]]
theorem rank_56_4 : (CJ0.blockMatrix source 56 ((4 : ℤ)-21)).rank ≤ 49 :=
  Fast.cell (z := b56_4) (Fast.bands [(0,43,14),(1,44,12),(2,45,10),(3,46,8),(4,47,6),(5,48,4),(6,49,2)]) (by decide +kernel) (by decide +kernel)

private def b60_3 : CJ1.Block where
  bank := .leftLow
  cap := 32
  free := [(4,0),(4,1),(4,2),(5,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,135751,987280,0x445110],[0,0,0,0,0,0,0x7effcfcc,0x7efef64e,0x7efc3241],[0,0,0,0,861,3198,8881],[0,0,0x7effffd8,0x7effffb4,0x7effff71],[1,0,0],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,0,0,0,0,123410,895440],[0,0,0,0,0,0,0,0x7effd329,0x7eff095d],[0,0,0,0,0,820,3040],[0,0,0,0x7effffd9,0x7effffb6],[0,1,0],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,0,0,0,0,0,111930],[0,0,0,0,0,0,0,0,0x7effd65d],[0,0,0,0,0,0,780],[0,0,0,0,0x7effffda],[0,0,1],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,0,0,0,0,0,0x33ebb0],[0,0,0,0,0,0,0,0,0x7efb5d3f],[0,0,0,0,0,0,19760],[0,0,0,0,0x7efffd1c],[0,0,0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_60_3 : (CJ0.blockMatrix source 60 ((3 : ℤ)-21)).rank ≤ 32 :=
  Fast.cell (z := b60_3) (Fast.bands [(39,39,1),(40,40,2),(41,41,3),(42,42,4),(43,44,4),(44,46,4),(45,48,4),(46,50,4),(47,52,4),(48,54,4),(49,56,4),(50,58,3),(51,60,1)]) (by decide +kernel) (by decide +kernel)

private def b64_0 : CJ1.Block where
  bank := .rightLow
  cap := 10
  free := [(1,0)]
  vectors := [
    [[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]]]
theorem rank_64_0 : (CJ0.blockMatrix source 64 ((0 : ℤ)-21)).rank ≤ 10 :=
  Fast.cell (z := b64_0) (Fast.bands [(0,55,10),(1,56,8),(2,57,6),(3,58,4),(4,59,2)]) (by decide +kernel) (by decide +kernel)

private def b67_0 : CJ1.Block where
  bank := .rightLow
  cap := 7
  free := [(1,0),(3,0),(5,0),(7,0)]
  vectors := [
    [[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]],
    [[],[0],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]],
    [[],[0],[],[0],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]],
    [[],[0],[],[0],[],[0],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]]]
theorem rank_67_0 : (CJ0.blockMatrix source 67 ((0 : ℤ)-21)).rank ≤ 7 :=
  Fast.cell (z := b67_0) (Fast.bands [(0,61,7),(1,62,5),(2,63,3),(3,64,1)]) (by decide +kernel) (by decide +kernel)

end CurveList179925Witness
