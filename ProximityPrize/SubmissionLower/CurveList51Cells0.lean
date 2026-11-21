import ProximityPrize.SubmissionLower.CurveList51Defs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace CurveList51
private def b12_39 : CJ1.Block where
  bank := .leftLow
  cap := 84
  free := [(10,0)]
  vectors := [
    [[0,0,1,0,0,0,0,0,0,0,0,0,0],[0,0,1,0,0,0,0,0,0,0,0,0],[0,0,1,0,0,0,0,0,0,0,0],[0,0,1,0,0,0,0,0,0,0],[0,0,1,0,0,0,0,0,0],[0,0,1,0,0,0,0,0],[0,0,1,0,0,0,0],[0,0,1,0,0,0],[0,0,1,0,0],[0,1,0],[1],[],[]]]
theorem rank_12_39 : (CJ0.blockMatrix source 12 ((39 : ℤ)-21)).rank ≤ 84 :=
  Fast.cell (z := b12_39) (Fast.bands [(0,0,10),(1,1,10),(2,2,10),(3,3,10),(4,4,9),(5,5,8),(6,6,7),(7,7,6),(8,8,5),(9,9,4),(10,10,3),(11,11,2),(12,12,1)]) (by decide +kernel) (by decide +kernel)

private def b20_31 : CJ1.Block where
  bank := .leftLow
  cap := 120
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,0,0,0,0,0,0],[0,0,0,0,0,1,0,0,0,0,0],[0,0,0,0,1,0,0,0,0],[0,0,0,1,0,0,0],[0,0,1,0,0],[0,1,0],[1],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_20_31 : (CJ0.blockMatrix source 20 ((31 : ℤ)-21)).rank ≤ 120 :=
  Fast.cell (z := b20_31) (Fast.bands [(0,0,2),(1,1,3),(2,2,4),(3,3,5),(4,4,6),(5,5,7),(6,6,8),(7,7,9),(8,8,10),(9,9,10),(10,10,10),(11,11,10),(12,12,9),(13,13,8),(14,14,7),(15,15,6),(16,16,5),(17,17,4),(18,18,3),(19,19,2),(20,20,1)]) (by decide +kernel) (by decide +kernel)

private def b28_23 : CJ1.Block where
  bank := .leftLow
  cap := 120
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,0,0,0,0,0,0],[0,0,0,0,0,1,0,0,0,0,0],[0,0,0,0,1,0,0,0,0],[0,0,0,1,0,0,0],[0,0,1,0,0],[0,1,0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_28_23 : (CJ0.blockMatrix source 28 ((23 : ℤ)-21)).rank ≤ 120 :=
  Fast.cell (z := b28_23) (Fast.bands [(7,7,1),(8,8,2),(9,9,3),(10,10,4),(11,11,5),(12,12,6),(13,13,7),(14,14,8),(15,15,9),(16,16,10),(17,17,10),(18,18,10),(19,19,10),(20,20,9),(21,21,8),(22,22,7),(23,23,6),(24,24,5),(25,25,4),(26,26,3),(27,27,2),(28,28,1)]) (by decide +kernel) (by decide +kernel)

private def b36_15 : CJ1.Block where
  bank := .rightLow
  cap := 114
  free := [(18,0),(19,0),(20,0),(21,0)]
  vectors := [
    [[0,0,0,1,3,3,1],[0,0,6,12,3,0x7efffffb,0x7efffffe],[0,0,15,3,0x7effffd1,0x7effffd4,0x7efffffb,3],[0,20,0x7effffc5,0x7effff80,0,75,24,0x7f000000],[0,15,0x7effff7a,0x7efffff2,330,210,0x7efffff2,0x7effffec],[6,0x7effff7d,333,486,0x7effff2f,0x7efffeb1,0x7effffc2,6],[1,0x7effffc2,498,0x7effff24,0x7efffbb7,0x7efffeb1,168,57],[0x7efffff5,297,0x7efffc05,0x7efffd94,1008,672,48,0x7efffff2],[66,0x7efffcc8,1125,1674,0x7effff83,0x7efffe57,0x7effffb6],[0x7effff25,1485,0x7efffe99,0x7efff8f3,0x7efffde5,60,20],[495,0x7efff90b,0x7efffd0d,918,459,45],[0x7efffce9,1386,1224,0x7effffcb,0x7effff7d,0x7efffff2],[924,0x7efffdaf,0x7efffcaa,0x7effff4e,0x7efffffe],[0x7efffce9,0,300,81,6],[495,165,0x7effffe3,0x7efffff8],[0x7effff25,0x7effff9e,0x7efffff5,0x7f000000],[66,27,3],[0x7efffff5,0x7efffffe,0],[1,0],[0,0],[0],[0]],
    [[0,0,0,12,37,38,13],[0,0,72,151,45,0x7effffb8,0x7effffda],[0,0,180,57,0x7efffdc1,0x7efffdbe,0x7effffa9,39],[0,240,0x7efffd54,0x7efff9a8,0x7effff91,925,322,0x7efffff4],[0,180,0x7efff9d0,0x7efffe7b,3946,2800,0x7effff98,0x7efffeeb],[72,0x7efff9e6,3723,6273,0x7efff813,0x7effef6f,0x7efffc80,79],[12,0x7efffd14,5780,0x7efff91e,0x7effcbe1,0x7effec6d,1904,775],[0x7effff72,3489,0x7effd357,0x7effdd12,11214,8848,856,0x7effff38],[780,0x7effdac0,11600,21222,252,0x7effeba7,0x7efffbd5],[0x7efff5f3,16775,0x7efff9f8,0x7effac7f,0x7effe0f3,454,275],[5720,0x7effb435,0x7effd2e9,9546,6012,715],[0x7effdcd0,14058,15780,738,0x7efffa10,0x7effff2a],[10296,0x7effed2f,0x7effd895,0x7efff53c,0x7effff7b],[0x7effde7d,0x7efffa97,3075,1063,93],[5148,2475,0x7effffc5,0x7effffaa],[0x7efff7a0,0x7efffb26,0x7effff27,0x7effffee],[572,291,40],[0x7effffb3,0x7effffec,1],[0,0x7effffff],[1,0],[0],[0]],
    [[0,0,0,78,246,259,91],[0,0,468,1020,350,0x7efffe25,0x7efffef0],[0,0,1170,486,0x7efff17d,0x7efff06b,0x7efffd53,273],[0,1560,0x7effef5d,0x7effd54f,0x7efffa51,6090,2324,0x7effffa6],[0,1170,0x7effd883,0x7efff1dd,25250,19824,0x7effffbb,0x7efff844],[468,0x7effd8c5,22754,42696,0x7effd9ab,0x7eff90e1,0x7effe543,560],[78,0x7effed23,36520,0x7effe47b,0x7efeaf7d,0x7eff69c7,11060,5670],[0x7efffc65,22274,0x7efeedf1,0x7eff03cb,65688,61334,7776,0x7efffa57],[5005,0x7eff1550,66130,140484,13104,0x7eff7e97,0x7effe013],[0x7effc005,103719,2220,0x7efdf9e5,0x7eff1691,410,2036],[36036,0x7efe38ec,0x7efeb901,50436,40674,6044],[0x7eff2509,79695,103200,13596,0x7effdead,0x7efff985],[63063,0x7effaa27,0x7eff1277,0x7effae3b,0x7efff905],[0x7eff36e9,0x7effcbab,15420,6906,776],[30030,16632,1560,0x7effff03],[0x7effd115,0x7effe321,0x7efff931,0x7effff43],[3003,1435,230],[0x7efffe95,0x7effffec,20],[0,0x7effffec],[0,0x7f000000],[1],[0]],
    [[0,0,0,364,1170,1260,455],[0,0,2184,4914,1890,0x7efff764,0x7efffaac],[0,0,5460,2730,0x7effbd11,0x7effb3b7,0x7efff13d,1365],[0,7280,0x7effb55b,0x7eff33bf,0x7effd8f5,28350,11970,0x7efffe3a],[0,5460,0x7eff4ab7,0x7effadf9,115290,98784,3150,0x7effd8a1],[2184,0x7eff4ab7,100590,205380,0x7eff876b,0x7efdf451,0x7eff6ecf,2835],[364,0x7effa88f,166320,0x7effbea7,0x7ef9f689,0x7efceb07,42336,29610],[0x7effef3f,102354,0x7efb3ea9,0x7efb1677,273420,295470,48636,0x7effe2d3],[23100,0x7efbd584,275100,656460,105840,0x7efdd15f,0x7eff51c5],[0x7efedabe,464079,51030,0x7ef7129d,0x7efb62c1,0x7effc767,10766],[163800,0x7ef83c24,0x7ef9b1a1,187740,185220,36120],[0x7efc26a5,331947,473760,91980,0x7eff948b,0x7effdc3d],[280280,0x7efee10f,0x7efc052d,0x7efe733f,0x7effc839],[0x7efc9038,0x7efee10f,55650,27510,4620],[128700,76692,11760,1470],[0x7eff3c7f,0x7eff8549,0x7effe279,0x7efffacf],[12012,5439,420],[0x7efffaac,0x7effffec,210],[0,0x7effffec],[0,0x7effffec],[0],[1]]]
theorem rank_36_15 : (CJ0.blockMatrix source 36 ((15 : ℤ)-21)).rank ≤ 114 :=
  Fast.cell (z := b36_15) (Fast.bands [(0,16,21),(1,17,19),(2,18,17),(3,19,15),(4,20,13),(5,21,11),(6,22,9),(7,23,7),(8,24,5),(9,25,3),(10,26,1)]) (by decide +kernel) (by decide +kernel)

private def b39_14 : CJ1.Block where
  bank := .leftLow
  cap := 99
  free := [(9,0)]
  vectors := [
    [[1,35,595,6545,52360,324632,0x18c478,0x669ba8,0x16720cc,0x4356264,0xaf13304,0x18de5cac,0x31bcb958,0x57ff2088,0xb47c567,0x4297adf7,0x72fd9975,0x1075c9a0,0x1075c9a0],[1,34,561,5984,46376,278256,0x148588,0x521620,0x1150aac,0x32057b8,0x7d0db4c,0x110d8160,0x20af37f8,0x374fe890,0x52f7dcd8,0x6e9fd120,0x45dc855],[1,33,528,5456,40920,237336,0x10e670,0x412fb0,0xd3dafc,0x24c7cbc,0x5845e90,0xb8922d0,0x15261528,0x2229d368,0x30ce0970],[1,32,496,4960,35960,201376,906192,0x335be0,0xa07f1c,0x1abfda0,0x3d860f0,0x7b0c1e0,0xd755348],[1,31,465,4495,31465,169911,736281,0x281fc7,0x785f55,0x1339e4b,0x2a4c2a5],[1,30,435,4060,27405,142506,593775,0x1f1058,0x594efd],[1,29,406,3654,23751,118755,475020],[1,28,378,3276,20475],[1,27,351],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_39_14 : (CJ0.blockMatrix source 39 ((14 : ℤ)-21)).rank ≤ 99 :=
  Fast.cell (z := b39_14) (Fast.bands [(18,18,1),(19,19,2),(20,20,3),(21,21,4),(22,22,5),(23,23,6),(24,24,7),(25,25,8),(26,26,9),(27,27,10),(28,28,10),(29,29,10),(30,30,10),(31,31,9),(32,32,8),(33,34,6),(34,36,4),(35,38,2)]) (by decide +kernel) (by decide +kernel)

private def b43_11 : CJ1.Block where
  bank := .leftLow
  cap := 88
  free := [(8,0),(8,1)]
  vectors := [
    [[0x7effffd2,0x7efff949,0x7eff879c,0x7efa7fb1,0x7ed0c0e8,0x7dc25a19,0x7833963e,0x5fcd6b81,0x4ba8905,0x5cc21424,0x22a7c8b6,0x3790405a,0x233ac4c8,0x2af5a75d,0x5175802e,0x1142e809,0x77eef153,0x6b4c84a1],[0x7effffd8,0x7efffa4a,0x7eff9c17,0x7efb8af3,0x7eda9a8c,0x7e0a434e,0x79dba651,0x67ee05f1,0x269eedcd,0x57ce3977,0x25c10faf,0x69ac8eca,0x7b30ba14,0x6f2c0884,0x39f2db40,0x2d8cc0fa],[0x7effffde,0x7efffb3f,0x7effaecb,0x7efc758f,0x7ee2f02e,0x7e450bb1,0x7b2b3571,0x6e2a7671,0x3fdf3c25,0x312f4baa,0x3638f61d,0x49a9c4b4,0x5df34d6e,0x25337e42],[0x7effffe4,0x7efffc28,0x7effbfca,0x7efd4206,0x7ee9ed19,0x7e749839,0x7c31be69,0x72e53cc9,0x52783f65,0x70791a96,0x73a4ff50,0x3c55cda4],[0x7effffea,0x7efffd05,0x7effcf26,0x7efdf2c1,0x7eefb969,0x7e9a9961,0x7cfc8ba9,0x766fcf41,0x5fff920d,0x1e4474f1],[0x7efffff0,0x7efffdd6,0x7effdcf1,0x7efe8a11,0x7ef47a29,0x7eb88ef9,0x7d96f391,0x790d02f1],[0x7efffff6,0x7efffe9b,0x7effe93d,0x7eff0a2f,0x7ef85171,0x7ecfcbd3],[0x7efffffc,0x7effff54,0x7efff41c,0x7eff753c],[1,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x6599999c,0x659999d5,0x32ccd0e8,0x32ccfcd8,105672,0x4c3e0b28,0x4c6e9e31,0x66aa3d04,0x69c5db14,0xe2a4f34,0x10b7a6eb,0x553490fb,0x37014478,0x514b107a,0x7618ac41,0x2add01a3,0x1b7d345c,0x533d5cd3],[0x19666668,50,0x32ccd038,9996,83895,0x32d53684,0x2d0f90,0x6663b3d4,0x305ce5c,0xa053368,0x367788d5,0x4a6051d0,0x5cb52175,0x5809f6a6,0x6fcd546c,0x76afc959],[0x4c333335,0x32ccccf7,714,7973,65450,0x196cd2d5,0x65bb48a4,0x93e5a8,0x22a1558,0x703a3fc,0x6010743f,0x645697d6,0x6d6bfe28,0x58048b97],[1,34,0x32cccf05,0x19667ea7,0x19672995,0x32d19caa,0x18c478,0x3337832a,0x1aee5cd9,0x1e420265,0x403e45fe,0x20af37f8],[0x32ccccce,0x659999b5,0x65999b4e,0x6599abe4,0x32cd5dba,0x32d05252,0x65ab7744,0x65e568c4,0x66ab61e4,0x3620edf6],[0x6599999b,0x659999ae,0x32ccce0a,0x32ccd9fa,26536,0x659c1a24,0x65a632c4,0x3301bd3a],[0x19666667,13,0x32cccda0,2263,17980,0x19681bf6],[0x4c333334,0x32ccccd4,117,1334],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_43_11 : (CJ0.blockMatrix source 43 ((11 : ℤ)-21)).rank ≤ 88 :=
  Fast.cell (z := b43_11) (Fast.bands [(22,22,1),(23,23,2),(24,24,3),(25,25,4),(26,26,5),(27,27,6),(28,28,7),(29,29,8),(30,30,9),(31,31,10),(32,32,10),(33,33,10),(34,35,9),(35,37,7),(36,39,5),(37,41,3),(38,43,1)]) (by decide +kernel) (by decide +kernel)

private def b51_6 : CJ1.Block where
  bank := .leftLow
  cap := 62
  free := [(6,2),(7,0)]
  vectors := [
    [[0x66005e2a,0x440fd0ec,0x204c2351,0x66bb37fb,0xb502fc6,0xc0b0e3b,0x4c4604cb,0x4046277,0x5193bb18,0x6ccbb22,0x3084e2a7,0x128ea7f4,0x7271535,0x41e70b30,0x5e4c98cb],[0x66005e2a,0x5d0f72c3,0x423cb08f,0x247e876c,0x65d1a85b,0x253965e1,0x270c9eea,0x5bf7c38e,0x749bf78b,0x1130c398,0x1f541f0f,0x723a88e6,0x3ccc250b],[0x66005e2a,0x760f149a,0x4b2d9bf6,0x5850eb77,0xd80bce4,0x17b8a8fd,0xf53f5ed,0x4ca3cda1,0x27f829ea,0x683899af,0x61e68fc5],[0x66005e2a,0x100eb670,0x3b1ee586,0x1d3205f1,0x6f4eb6f4,0x2769f20a,0x66ea03e4,0x64b9c9be,0x1673571e],[0x66005e2a,0x290e5847,0x12108d3f,0xb2178b2,0x642d3e42,0x423cb3c9,0x7acdae4c],[0x66005e2a,0x420dfa1e,0x4f029322,0x3b1ee591,0x6c634fdd],[0x66005e2a,0x5b0d9bf5,1],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0xc0b08d4,0x9da7b98,0x4fec2377,0x21f08f52,0x55659932,0x6b4baae8,0x2348fb8,0x788389f2,0x224fecbd,0x4cfdedfb,0x3a928f87,0x30b7ae94,0x57947c35,0x48134f91,0x227a8794],[0xc0b08d4,0x7ccf72c5,0x521cb0b3,0x4ed3dea0,0x691ba92,0x64b9f056,0x1c7a9f63,0x5c08ea8f,0x4547022f,0x7b6ebcc,0x32dba3bb,0x7cdc0ada,0x2e051bb4],[0xc0b08d4,0x70c469f1,0x605846c3,0x6d7b97de,0x181622b5,0x4ca3cda1,0x4ed6d1c3,0xd3218cc,0x3814e963,0x4ea2026a,0x10009a0f],[0xc0b08d4,0x64b9611d,0x7a9ee5a7,0x71dcb238,0x2539707e,0x276a5d23,0x276c74a0,0x64c5a42d,0x2684d557],[0xc0b08d4,0x58ae5849,0x21f08d5e,0x4fec24da,0x544d4ba5,0x521d117f,0x11a596b],[0xc0b08d4,0x4ca34f75,0x544d3dea,0x7a9ee6f1,0x4ca35d9e],[0xc0b08d4,0x409846a1,0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_51_6 : (CJ0.blockMatrix source 51 ((6 : ℤ)-21)).rank ≤ 62 :=
  Fast.cell (z := b51_6) (Fast.bands [(30,30,1),(31,31,2),(32,32,3),(33,33,4),(34,34,5),(35,35,6),(36,36,7),(37,38,7),(38,40,7),(39,42,7),(40,44,6),(41,46,5),(42,48,4),(43,50,2)]) (by decide +kernel) (by decide +kernel)

private def b59_2 : CJ1.Block where
  bank := .rightLow
  cap := 27
  free := [(3,1),(5,1),(7,1)]
  vectors := [
    [[],[1],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[],[1],[0x7f000000],[1,0],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[],[1],[0],[2,0],[0x7effffff],[1,0],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]]]
theorem rank_59_2 : (CJ0.blockMatrix source 59 ((2 : ℤ)-21)).rank ≤ 27 :=
  Fast.cell (z := b59_2) (Fast.bands [(0,49,11),(1,50,9),(2,51,7),(3,52,5),(4,53,3),(5,54,1)]) (by decide +kernel) (by decide +kernel)

private def b63_0 : CJ1.Block where
  bank := .rightLow
  cap := 9
  free := [(3,0)]
  vectors := [
    [[],[],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]]]
theorem rank_63_0 : (CJ0.blockMatrix source 63 ((0 : ℤ)-21)).rank ≤ 9 :=
  Fast.cell (z := b63_0) (Fast.bands [(0,55,9),(1,56,7),(2,57,5),(3,58,3),(4,59,1)]) (by decide +kernel) (by decide +kernel)

private def b66_1 : CJ1.Block where
  bank := .leftLow
  cap := 8
  free := [(2,0)]
  vectors := [
    [[0,0,0,0,1035],[0,0,0x7effffd4],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_66_1 : (CJ0.blockMatrix source 66 ((1 : ℤ)-21)).rank ≤ 8 :=
  Fast.cell (z := b66_1) (Fast.bands [(45,45,1),(46,46,2),(47,48,2),(48,50,2),(49,52,2),(50,54,2),(51,56,2),(52,58,2),(53,60,2),(54,62,2),(55,64,1)]) (by decide +kernel) (by decide +kernel)

end CurveList51
