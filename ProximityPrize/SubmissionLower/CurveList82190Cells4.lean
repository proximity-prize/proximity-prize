import ProximityPrize.SubmissionLower.CurveList82190Defs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace CurveList82190
private def b36_16 : CJ1.Block where
  bank := .leftLow
  cap := 109
  free := [(9,1)]
  vectors := [
    [[0x250aaaab,0x4f600002,22,0x2a555639,1705,9889,0x54ab5ef0,178002,0x3f88d3cb,0x3f988533,0x3ad946,0x7b0c1e,0xe19637,0x16c68cf,0x20895ba,0x2936852,0x6225d55d,0x6225d55d,0x2936852,0x20895ba],[0x250aaaab,0x2a555557,0x54aaaac0,0x54aaab7a,0x2a555b30,0x54aacb72,37758,140244,0x3f86aff7,0x11d53c,0x29040a,0x520814,0x8f8e23,0xdcdaac,0x12bbb0e,0x167ad44,0x60be2819,0x167ad44],[0x250aaaab,0x54aaaac,0x4f600014,0x54aab66,0x250aafca,0x2fa01ba8,0x4f6077d7,0x2fa1abfe,0xfe503f9,0x6f2cd144,0xffc32c7,0x6f55d54e,0x1039b8d6,0x6fa321d7,0x10889938,0x6fdf140d],[0x250aaaab,0x5f400002,0x6f200013,0x152aab54,0xfe00476,0x1fc01732,0x2fa060a5,84825,0xfe3b8a0,0x5f4918a4,0x2fb31a24,0x3fa2bb2a,0x4f96fdad,0x200c242a],[0x250aaaab,0x3a355557,0x34eaaabc,0x5f400099,0x2fa003de,0x6f201355,0x3f804d51,0x3f80fe09,0x4f62ba98,0xfe65e0c,0x1fccbc18,0x1fd5ff12],[0x250aaaab,0x152aaaac,0x1fc00010,0x3f800089,0x6f200356,4095,0x3f803d52,49335,0x4f61f9e1,0x3f84642c],[0x250aaaab,0x6f200002,0x2fa0000f,0xfe0007a,0x5f4002dc,0x1fc00d24,0x1fc0302e,0x5f40908a],[0x250aaaab,0x4a155557,0x648aaab9,0x2a5555c2,0x34eaad1a,0x69d5600b],[0x250aaaab,0x250aaaac,0x3f80000d,0x69d555b6],[0x250aaaab,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_36_16 : (CJ0.blockMatrix source 36 ((16 : ℤ)-21)).rank ≤ 109 :=
  Fast.cell (z := b36_16) (Fast.bands [(15,15,1),(16,16,2),(17,17,3),(18,18,4),(19,19,5),(20,20,6),(21,21,7),(22,22,8),(23,23,9),(24,24,10),(25,25,11),(26,26,11),(27,27,10),(28,28,9),(29,29,8),(30,30,7),(31,31,6),(32,33,4),(33,35,2)]) (by decide +kernel) (by decide +kernel)

private def b40_11 : CJ1.Block where
  bank := .rightLow
  cap := 101
  free := [(21,0)]
  vectors := [
    [[0,0,0,0,0,0x7f000000],[0,0,0,0,0x7efffff7,1],[0,0,0,0,0x7effffd4,20],[0,0,0,0x7effff89,135,0x7efffff7],[0,0,0,0x7effff2f,480,0x7effff7a],[0,0,0x7effff05,1050,0x7efffd31,45],[0,0,0x7effff2f,1512,0x7efff7cd,480],[0,0x7effff89,1470,0x7efff13d,2100,0x7effff89],[0,0x7effffd4,960,0x7effeec7,5040,0x7efffbe7],[0x7efffff7,405,0x7efff2e1,7350,0x7efff13d,210],[0x7f000000,100,0x7efff9ad,6720,0x7effe34b,1512],[11,0x7efffe3f,3780,0x7effdf31,4410,0x7effff05],[0x7effffca,1200,0x7effe9db,6720,0x7efffa43],[165,0x7efff7cd,5670,0x7efff2e1,210],[0x7efffeb7,2520,0x7efff13d,960],[462,0x7efff7cd,1620,0x7effff89],[0x7efffe33,1200,0x7efffe6c],[330,0x7efffe3f,45],[0x7effff5c,100],[55,0x7efffff7],[0x7efffff6],[1]]]
theorem rank_40_11 : (CJ0.blockMatrix source 40 ((11 : ℤ)-21)).rank ≤ 101 :=
  Fast.cell (z := b40_11) (Fast.bands [(0,20,21),(1,21,19),(2,22,17),(3,23,15),(4,24,13),(5,25,11),(6,26,9),(7,27,7),(8,28,5),(9,29,3),(10,30,1)]) (by decide +kernel) (by decide +kernel)

private def b43_10 : CJ1.Block where
  bank := .rightLow
  cap := 91
  free := [(16,2),(17,2),(18,1),(19,1),(21,0)]
  vectors := [
    [[0,0,0,0x7f000000,0x7f000000],[0,0,0,0x7efffffa,0x7efffffc,1],[0,0,0x7effffec,0,13],[0,0,0x7effffde,49,42,0x7efffffa],[0,0x7effffde,140,14,0x7effffc9],[0,0x7effffec,189,0x7effff52,0x7effff83,21],[0x7efffffa,140,0x7efffe72,0,119],[0x7f000000,55,0x7efffe79,385,175,0x7effffde],[9,0x7effff45,588,0x7effff98,0x7effff75],[0,0x7effffdd,364,0x7efffe17,0x7effff98,35],[0,84,0x7efffe4f,196,91],[0,0,0x7effff83,322,0,0x7effffec],[0,0,126,0x7effff75,0x7effffe5],[0,0,0x7effffad,28,7],[0,0,36,1],[0,0,0x7efffff8,0x7f000000],[0,0,1],[0,0,0],[0,0],[0,0],[0],[0]],
    [[0,0,0,0x7efffff8,0x7efffff7],[0,0,0,0x7effffc2,0x7effffcc,10],[0,0,0x7effff44,0x7effffe5,133],[0,0,0x7efffec6,385,462,0x7effffba],[0,0x7efffec6,1190,350,0x7efffdb5],[0,0x7effff44,1645,0x7efffb38,0x7efffa43,217],[0x7effffc2,1232,0x7efff34a,0x7efffd45,1295],[0x7efffff8,487,0x7efff2fd,2625,2275,0x7efffe8e],[80,0x7efff9a5,4704,175,0x7efff9b7],[0,0x7efffec6,3052,0x7efff29b,0x7efff908,385],[0,720,0x7efff27f,784,1155],[0,0,0x7efffbe7,2338,588,0x7effff0c],[0,0,1008,0x7efffcd5,0x7efffe41],[0,0,0x7efffd8b,28,91],[0,0,240,73],[0,0,0x7effffd4,0x7efffff0],[0,0,0],[0,0,1],[0,0],[0,0],[0],[0]],
    [[0,0,0,0x7efffff8,0x7efffff7],[0,0,0,0x7effffc2,0x7effffcb,9],[0,0,0x7effff44,0x7effffdd,126],[0,0,0x7efffec6,357,450,0x7effffc2],[0,0x7efffec6,1134,378,0x7efffde5],[0,0x7effff44,1575,0x7efffbd2,0x7efffa97,189],[0x7effffc2,1176,0x7efff470,0x7efffd0d,1155],[0x7efffff8,459,0x7efff431,2205,2079,0x7efffec6],[72,0x7efffa61,4032,315,0x7efffa97],[0x7f000000,0x7effff05,2520,0x7efff557,0x7efff9da,315],[9,504,0x7efff5ab,504,945],[0,0x7effffdd,0x7efffd8b,1638,504,0x7effff44],[0,84,504,0x7efffe09,0x7efffeb1],[0,0x7effff83,0x7effff05,0,63],[0,126,72,45],[0,0x7effffad,0x7efffff8,0x7efffff8],[0,36,0],[0,0x7efffff8,0],[0,1],[0,0],[0],[0]],
    [[0,0,0,0x7effffa7,0x7effff95],[0,0,0,0x7efffd8b,0x7efffda6,98],[0,0,0x7efff89f,0x7efffdc1,1386],[0,0,0x7efff3b3,3150,5148,0x7efffd4c],[0,0x7efff3b3,10836,5460,0x7effe861],[0,0x7efff89f,15372,0x7effe003,0x7effc005,2106],[0x7efffd8b,11592,0x7eff9533,0x7effcec9,13230],[0x7effffa7,4554,0x7eff8e79,16380,25830,0x7efff20f],[720,0x7effc8e1,36792,10710,0x7effc005],[0x7efffff8,0x7efff629,24192,0x7effac55,0x7effac55,3654],[80,5040,0x7effa085,0x7efffcb9,11718],[0,0x7efffec6,0x7effe765,13860,8568,0x7efff725],[0,720,5040,0x7efff431,0x7effee49],[0,0x7efffbe7,0x7efff629,0x7efffc11,798],[0,1008,720,738],[0,0x7efffd8b,0x7effffa7,0x7effff83],[0,240,0],[0,0x7effffd4,0],[0,0],[0,1],[0],[0]],
    [[0,0,0,0x7effffd4,0x7effffa7],[0,0,0,0x7efffec6,0x7efffdb8,81],[0,0,0x7efffc50,0x7efffb15,1225],[0,0,0x7efff9da,0x7efffec6,5355,0x7efffdae],[0,0x7efff9da,3150,9990,0x7effe9db],[0,0x7efffc50,5985,6825,0x7effb73b,1890],[0x7efffec6,5040,0x7efff0fe,0x7eff955d,13275],[0x7effffd4,2115,0x7effdb17,0x7effc3b6,33075,0x7efff2d2],[360,0x7effe945,3780,35595,0x7effba47],[0,0x7efffb15,7980,12600,0x7eff8144,3675],[0,2520,0x7effeec7,0x7effa769,14175],[1,0,0x7efff3b3,0x7efff6fb,17010,0x7efff668],[0x7efffff7,0,2520,5460,0x7effe765],[45,0,0x7efffb15,0x7efff13d,945],[0x7effff89,0,360,1245],[210,0,0x7effffd4,0x7effff5c],[0x7effff05,0,0],[210,0,0],[0x7effff89,0],[45,0],[0x7efffff7],[1]]]
theorem rank_43_10 : (CJ0.blockMatrix source 43 ((10 : ℤ)-21)).rank ≤ 91 :=
  Fast.cell (z := b43_10) (Fast.bands [(0,25,19),(1,26,17),(2,27,15),(3,28,13),(4,29,11),(5,30,9),(6,31,7),(7,32,5),(8,33,3),(9,34,1)]) (by decide +kernel) (by decide +kernel)

private def b47_8 : CJ1.Block where
  bank := .leftLow
  cap := 77
  free := [(7,0),(7,1),(7,2),(8,0)]
  vectors := [
    [[712,27560,526344,0x64eaa8,0x4c3cca44,0x2d0cc47f,0x6bd55ad3,0x4047e952,0x43188ed4,0x22f0c7c3,0x4f277eaf,0x3aba090,0x35390ff7,0x4384ec69,0x49c33ad1,0x548e9878,0x4ecc2919],[535,20298,0x5abcaa3c,0x5afea1bf,0x4b23d13d,0x5b2ae656,0x6ebfe24f,0x31663d5c,0x39ea199,0x50e50b1c,0x3baf924f,0x14c4674d,0x4a1c906c,0x3b1b915c,0x51b9314e],[0x366db85b,14270,0x3671bb71,0x30f9cc,0x4a4dc33a,0xc6b65b6,0x49578ed0,0x37c3f64,0x34c6392c,0x66a1d6e1,0x54fc88b6,0x16f2c5d2,0x72d7114c],[0x24492593,0x5ab70027,0x36705423,0x48b1dd90,0x11c32dd,0x7edca40,0x2eb98460,0x2187b3c3,0x3a9b5398,0x5d42c10a,0x465b03b0],[0x489249c0,0x6cdb83a6,0x4893d688,0x12bbb4,0xa92630,0x4c017f0,0x1c3c71e0,0x7c05a369,0x117d9e99],[0x244924e1,0x12249d5d,0x2449ee91,0x36776145,0x24a26176,0x4b2597ac,0xfc3ae18],[0x366db6f7,0x24492870,0x489291ec,0x244cd41e,0x36926a55],[1,0,0],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x7effffd5,0x7efff959,0x7eff80cd,0x7ef9c072,0x5a7cb334,0x34c27aa7,0x50a406e1,0x4ba7dabe,0x1caaf17b,0x1931a6e7,0x7c1917f8,0x18756df5,0x6ac791c7,0x31156edb,0x4ad91710,0xb7f95f8,0x52fdd082],[0x7effffe0,0x7efffb1c,0x1224366b,0x122021b6,0x5a8e22de,0x598fac08,0x781fe773,0x5c5b64ca,0x67a61b3e,0x1cc84443,0x591bb682,0x72cec885,0x55ecaa3f,0x4f9b6b41,0x658adefe],[0x2449247b,0x7efffc92,0x2448e51f,0x7efcf951,0x5a9b68cc,0x7e3ae488,0x7a722fca,0x1fa652d5,0x1cd6e7a5,0x421db68c,0x2cfc3d9e,0x14344898,0x23c7808f],[0x6cdb6da8,0x12249008,0x2448fb60,0x5ab4e88d,0x7eee6b4d,0x7e82255a,0x7c18d6e1,0x15c75ade,0x1c44ee1b,0x49fe609b,0x3c0797ba],[0x5ab6db65,0x489247ce,0x5ab6c30b,0x7efed87a,0x7ef58982,0x7eb48891,0x7d3e4271,0x3fb57c54,0x4664171a],[0x6cdb6db3,0x366db630,0x6cdb6160,0x24488c3f,0x6cd5e6b2,0x5a8dd48b,0x7e041461],[0x24492491,0x6cdb6d7d,0x5ab6d704,0x6cdb337a,0x2446da16],[0,1,0],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x2a555557,0x54aaaadf,988,0x2a5585e6,0x4287dcb6,0x5ac3d88f,0x6d29e114,0x190150f,0x6dca70f,0x44a5ef18,0x2ec37e15,0x32d1f708,0x4de8d70d,0x68d0d2e6,0x39f37e9a,0x485b17c0,0x2b3366b7],[1,38,0x48924bef,0x1e3d1657,0x6cdcaab2,0x6ce46960,0x359a3b,0x10e4116,0x49578ed,0x7e3d2ac2,0x28040e65,0x5255ff65,0x498b73c0,0x55783350,0x58903a3a],[0x1224924a,0x54aaaac6,0x66cf3ee2,6031,0x6cdc43a5,393680,0x238f4d,0x5b68d7ac,0x2ff52bc,0x65fe7073,0x7a152f7a,0x682693df,0x23b9bfea],[0x60c30c32,0x1e3cf3e1,0x1224938a,0x6cdb7cea,35150,251940,0x16b8b9,0x12962f77,0x6ec49c72,0xd38b05d,0x11a5e60f],[0x6cdb6db8,0x2449249d,0x6cdb6e76,0x54aab3b3,20995,151657,0x2a6322db,0x248ecb86,0x379bfa75],[0x366db6dc,0x3061861e,0xc1861e7,0x122496f9,0x60c337d9,0x18320784,510136],[0x3c79e79f,0xc186188,0x6cdb6ddb,0xc18635b,0x3c79fa1a],[0,0,1],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[37,1432,27384,345007,0x247a4ad3,0x49fcd0ea,0x2ce01c74,0x2c05efc3,0x435b3a73,0x72b7ecbb,0xdeea5dc,0x34eefd94,0x45d23a58,0x4b413998,0x7649552a,0x33bc25ce,0x59bf1374],[27,1026,0x6cdbb922,0x6cdf1692,0x246ae42d,0x253f618c,0x5c6f6ee,0x1d563920,0x15939eb,0x12c38bb2,0x2744ebd1,0x3d1b969e,0x14dccb38,0x2914281c,0x6c033f25],[0x5ab6db81,695,0x5ab70de5,158952,0x245f585e,0xa11099,0x3c2d960,0x5b96d3cc,0x52d57c28,0x67911d5,0x26faf490,0x1078220c,0x44b6550f],[0x12249255,0x6cdb6f6a,0x5ab6facd,0x244aa5da,903540,0x6441c0,0x2594460,0x66a0c933,0x584c6e36,0x10714b1a,0x51430758],[0x24492499,0x366db7cb,0x24493600,55495,516120,0x3a3590,0x162d340,0x3d90f22d,0x31b4932b],[0x1224924c,0x4892498e,0x12249a41,0x5ab742f3,0x1228803f,0x246776be,0xc07a80],[0x5ab6db6f,0x12249264,0x244926ee,0x1224b527,0x5ab85963],[0,0,0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_47_8 : (CJ0.blockMatrix source 47 ((8 : ℤ)-21)).rank ≤ 77 :=
  Fast.cell (z := b47_8) (Fast.bands [(26,26,1),(27,27,2),(28,28,3),(29,29,4),(30,30,5),(31,31,6),(32,32,7),(33,33,8),(34,34,9),(35,36,9),(36,38,9),(37,40,8),(38,42,6),(39,44,4),(40,46,2)]) (by decide +kernel) (by decide +kernel)

private def b54_4 : CJ1.Block where
  bank := .rightLow
  cap := 49
  free := [(7,2),(9,2)]
  vectors := [
    [[0,1],[0,3,0x7f000000],[3,0x7efffffb],[1,0x7efffff8,3],[0x7efffffd,9],[0,6,0x7efffffe],[0,0x7efffffd],[0,0,1],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0],[0],[0]],
    [[0,4],[0,12,0x7efffffe],[12,0x7effffed],[4,0x7effffe3,8],[0x7efffff5,24],[1,12,0x7efffffb],[0x7efffffd,0x7efffffd],[0,6,0],[0,0x7efffffd],[0,0,1],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0,0],[0,0],[0,0],[0],[0]]]
theorem rank_54_4 : (CJ0.blockMatrix source 54 ((4 : ℤ)-21)).rank ≤ 49 :=
  Fast.cell (z := b54_4) (Fast.bands [(0,41,14),(1,42,12),(2,43,10),(3,44,8),(4,45,6),(5,46,4),(6,47,2)]) (by decide +kernel) (by decide +kernel)

private def b58_3 : CJ1.Block where
  bank := .leftLow
  cap := 32
  free := [(4,0),(4,1),(4,2),(5,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,111930,810160,0x37c7b0],[0,0,0,0,0,0,0x7effd65d,0x7eff1b7d,0x7efcbe61],[0,0,0,0,780,2886,7981],[0,0,0x7effffda,0x7effffb8,0x7effff79],[1,0,0],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,0,0,0,0,101270,731120],[0,0,0,0,0,0,0,0x7effd969,0x7eff2cb4],[0,0,0,0,0,741,2736],[0,0,0,0x7effffdb,0x7effffba],[0,1,0],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,0,0,0,0,0,91390],[0,0,0,0,0,0,0,0,0x7effdc4e],[0,0,0,0,0,0,703],[0,0,0,0,0x7effffdc],[0,0,1],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,0,0,0,0,0,0x282960],[0,0,0,0,0,0,0,0,0x7efc3c20],[0,0,0,0,0,0,16872],[0,0,0,0,0x7efffd67],[0,0,0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_58_3 : (CJ0.blockMatrix source 58 ((3 : ℤ)-21)).rank ≤ 32 :=
  Fast.cell (z := b58_3) (Fast.bands [(37,37,1),(38,38,2),(39,39,3),(40,40,4),(41,42,4),(42,44,4),(43,46,4),(44,48,4),(45,50,4),(46,52,4),(47,54,4),(48,56,3),(49,58,1)]) (by decide +kernel) (by decide +kernel)

private def b62_0 : CJ1.Block where
  bank := .rightLow
  cap := 10
  free := [(1,0)]
  vectors := [
    [[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]]]
theorem rank_62_0 : (CJ0.blockMatrix source 62 ((0 : ℤ)-21)).rank ≤ 10 :=
  Fast.cell (z := b62_0) (Fast.bands [(0,53,10),(1,54,8),(2,55,6),(3,56,4),(4,57,2)]) (by decide +kernel) (by decide +kernel)

private def b65_0 : CJ1.Block where
  bank := .rightLow
  cap := 7
  free := [(1,0),(3,0),(5,0),(7,0)]
  vectors := [
    [[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]],
    [[],[0],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]],
    [[],[0],[],[0],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]],
    [[],[0],[],[0],[],[0],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]]]
theorem rank_65_0 : (CJ0.blockMatrix source 65 ((0 : ℤ)-21)).rank ≤ 7 :=
  Fast.cell (z := b65_0) (Fast.bands [(0,59,7),(1,60,5),(2,61,3),(3,62,1)]) (by decide +kernel) (by decide +kernel)

end CurveList82190
