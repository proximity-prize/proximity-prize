import ProximityPrize.SubmissionLower.CurveList50Defs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace CurveList50
private def b19_31 : CJ1.Block where
  bank := .leftLow
  cap := 119
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,0,0,0,0,0,0],[0,0,0,0,0,1,0,0,0,0,0],[0,0,0,0,1,0,0,0,0],[0,0,0,1,0,0,0],[0,0,1,0,0],[0,1,0],[1],[],[],[],[],[],[],[],[],[]]]
theorem rank_19_31 : (CJ0.blockMatrix source 19 ((31 : ℤ)-21)).rank ≤ 119 :=
  Fast.cell (z := b19_31) (Fast.bands [(0,0,3),(1,1,4),(2,2,5),(3,3,6),(4,4,7),(5,5,8),(6,6,9),(7,7,10),(8,8,10),(9,9,10),(10,10,10),(11,11,9),(12,12,8),(13,13,7),(14,14,6),(15,15,5),(16,16,4),(17,17,3),(18,18,2),(19,19,1)]) (by decide +kernel) (by decide +kernel)

private def b27_23 : CJ1.Block where
  bank := .leftLow
  cap := 120
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,0,0,0,0,0,0],[0,0,0,0,0,1,0,0,0,0,0],[0,0,0,0,1,0,0,0,0],[0,0,0,1,0,0,0],[0,0,1,0,0],[0,1,0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_27_23 : (CJ0.blockMatrix source 27 ((23 : ℤ)-21)).rank ≤ 120 :=
  Fast.cell (z := b27_23) (Fast.bands [(6,6,1),(7,7,2),(8,8,3),(9,9,4),(10,10,5),(11,11,6),(12,12,7),(13,13,8),(14,14,9),(15,15,10),(16,16,10),(17,17,10),(18,18,10),(19,19,9),(20,20,8),(21,21,7),(22,22,6),(23,23,5),(24,24,4),(25,25,3),(26,26,2),(27,27,1)]) (by decide +kernel) (by decide +kernel)

private def b35_15 : CJ1.Block where
  bank := .rightLow
  cap := 114
  free := [(18,0),(19,0),(20,0),(21,0)]
  vectors := [
    [[0,0,0,1,3,3,1],[0,0,6,12,3,0x7efffffb,0x7efffffe],[0,0,15,3,0x7effffd1,0x7effffd4,0x7efffffb,3],[0,20,0x7effffc5,0x7effff80,0,75,24,0x7f000000],[0,15,0x7effff7a,0x7efffff2,330,210,0x7efffff2,0x7effffec],[6,0x7effff7d,333,486,0x7effff2f,0x7efffeb1,0x7effffc2,6],[1,0x7effffc2,498,0x7effff24,0x7efffbb7,0x7efffeb1,168,57],[0x7efffff5,297,0x7efffc05,0x7efffd94,1008,672,48,0x7efffff2],[66,0x7efffcc8,1125,1674,0x7effff83,0x7efffe57,0x7effffb6],[0x7effff25,1485,0x7efffe99,0x7efff8f3,0x7efffde5,60,20],[495,0x7efff90b,0x7efffd0d,918,459,45],[0x7efffce9,1386,1224,0x7effffcb,0x7effff7d,0x7efffff2],[924,0x7efffdaf,0x7efffcaa,0x7effff4e,0x7efffffe],[0x7efffce9,0,300,81,6],[495,165,0x7effffe3,0x7efffff8],[0x7effff25,0x7effff9e,0x7efffff5,0x7f000000],[66,27,3],[0x7efffff5,0x7efffffe,0],[1,0],[0,0],[0],[0]],
    [[0,0,0,12,37,38,13],[0,0,72,151,45,0x7effffb8,0x7effffda],[0,0,180,57,0x7efffdc1,0x7efffdbe,0x7effffa9,39],[0,240,0x7efffd54,0x7efff9a8,0x7effff91,925,322,0x7efffff4],[0,180,0x7efff9d0,0x7efffe7b,3946,2800,0x7effff98,0x7efffeeb],[72,0x7efff9e6,3723,6273,0x7efff813,0x7effef6f,0x7efffc80,79],[12,0x7efffd14,5780,0x7efff91e,0x7effcbe1,0x7effec6d,1904,775],[0x7effff72,3489,0x7effd357,0x7effdd12,11214,8848,856,0x7effff38],[780,0x7effdac0,11600,21222,252,0x7effeba7,0x7efffbd5],[0x7efff5f3,16775,0x7efff9f8,0x7effac7f,0x7effe0f3,454,275],[5720,0x7effb435,0x7effd2e9,9546,6012,715],[0x7effdcd0,14058,15780,738,0x7efffa10,0x7effff2a],[10296,0x7effed2f,0x7effd895,0x7efff53c,0x7effff7b],[0x7effde7d,0x7efffa97,3075,1063,93],[5148,2475,0x7effffc5,0x7effffaa],[0x7efff7a0,0x7efffb26,0x7effff27,0x7effffee],[572,291,40],[0x7effffb3,0x7effffec,1],[0,0x7effffff],[1,0],[0],[0]],
    [[0,0,0,78,246,259,91],[0,0,468,1020,350,0x7efffe25,0x7efffef0],[0,0,1170,486,0x7efff17d,0x7efff06b,0x7efffd53,273],[0,1560,0x7effef5d,0x7effd54f,0x7efffa51,6090,2324,0x7effffa6],[0,1170,0x7effd883,0x7efff1dd,25250,19824,0x7effffbb,0x7efff844],[468,0x7effd8c5,22754,42696,0x7effd9ab,0x7eff90e1,0x7effe543,560],[78,0x7effed23,36520,0x7effe47b,0x7efeaf7d,0x7eff69c7,11060,5670],[0x7efffc65,22274,0x7efeedf1,0x7eff03cb,65688,61334,7776,0x7efffa57],[5005,0x7eff1550,66130,140484,13104,0x7eff7e97,0x7effe013],[0x7effc005,103719,2220,0x7efdf9e5,0x7eff1691,410,2036],[36036,0x7efe38ec,0x7efeb901,50436,40674,6044],[0x7eff2509,79695,103200,13596,0x7effdead,0x7efff985],[63063,0x7effaa27,0x7eff1277,0x7effae3b,0x7efff905],[0x7eff36e9,0x7effcbab,15420,6906,776],[30030,16632,1560,0x7effff03],[0x7effd115,0x7effe321,0x7efff931,0x7effff43],[3003,1435,230],[0x7efffe95,0x7effffec,20],[0,0x7effffec],[0,0x7f000000],[1],[0]],
    [[0,0,0,364,1170,1260,455],[0,0,2184,4914,1890,0x7efff764,0x7efffaac],[0,0,5460,2730,0x7effbd11,0x7effb3b7,0x7efff13d,1365],[0,7280,0x7effb55b,0x7eff33bf,0x7effd8f5,28350,11970,0x7efffe3a],[0,5460,0x7eff4ab7,0x7effadf9,115290,98784,3150,0x7effd8a1],[2184,0x7eff4ab7,100590,205380,0x7eff876b,0x7efdf451,0x7eff6ecf,2835],[364,0x7effa88f,166320,0x7effbea7,0x7ef9f689,0x7efceb07,42336,29610],[0x7effef3f,102354,0x7efb3ea9,0x7efb1677,273420,295470,48636,0x7effe2d3],[23100,0x7efbd584,275100,656460,105840,0x7efdd15f,0x7eff51c5],[0x7efedabe,464079,51030,0x7ef7129d,0x7efb62c1,0x7effc767,10766],[163800,0x7ef83c24,0x7ef9b1a1,187740,185220,36120],[0x7efc26a5,331947,473760,91980,0x7eff948b,0x7effdc3d],[280280,0x7efee10f,0x7efc052d,0x7efe733f,0x7effc839],[0x7efc9038,0x7efee10f,55650,27510,4620],[128700,76692,11760,1470],[0x7eff3c7f,0x7eff8549,0x7effe279,0x7efffacf],[12012,5439,420],[0x7efffaac,0x7effffec,210],[0,0x7effffec],[0,0x7effffec],[0],[1]]]
theorem rank_35_15 : (CJ0.blockMatrix source 35 ((15 : ℤ)-21)).rank ≤ 114 :=
  Fast.cell (z := b35_15) (Fast.bands [(0,15,21),(1,16,19),(2,17,17),(3,18,15),(4,19,13),(5,20,11),(6,21,9),(7,22,7),(8,23,5),(9,24,3),(10,25,1)]) (by decide +kernel) (by decide +kernel)

private def b38_14 : CJ1.Block where
  bank := .leftLow
  cap := 99
  free := [(9,0)]
  vectors := [
    [[1,34,561,5984,46376,278256,0x148588,0x521620,0x1150aac,0x32057b8,0x7d0db4c,0x110d8160,0x20af37f8,0x374fe890,0x52f7dcd8,0x6e9fd120,0x45dc855,0xc18014b,0x45dc855],[1,33,528,5456,40920,237336,0x10e670,0x412fb0,0xd3dafc,0x24c7cbc,0x5845e90,0xb8922d0,0x15261528,0x2229d368,0x30ce0970,0x3dd1c7b0,0x458c00a6],[1,32,496,4960,35960,201376,906192,0x335be0,0xa07f1c,0x1abfda0,0x3d860f0,0x7b0c1e0,0xd755348,0x14b48020,0x1c198950],[1,31,465,4495,31465,169911,736281,0x281fc7,0x785f55,0x1339e4b,0x2a4c2a5,0x50bff3b,0x869540d],[1,30,435,4060,27405,142506,593775,0x1f1058,0x594efd,0xda4f4e,0x1ca7357],[1,29,406,3654,23751,118755,475020,0x17d0cc,0x417e31],[1,28,378,3276,20475,98280,376740],[1,27,351,2925,17550],[1,26,325],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_38_14 : (CJ0.blockMatrix source 38 ((14 : ℤ)-21)).rank ≤ 99 :=
  Fast.cell (z := b38_14) (Fast.bands [(17,17,1),(18,18,2),(19,19,3),(20,20,4),(21,21,5),(22,22,6),(23,23,7),(24,24,8),(25,25,9),(26,26,10),(27,27,10),(28,28,10),(29,29,10),(30,30,9),(31,31,8),(32,33,6),(33,35,4),(34,37,2)]) (by decide +kernel) (by decide +kernel)

private def b42_11 : CJ1.Block where
  bank := .leftLow
  cap := 88
  free := [(8,0),(8,1)]
  vectors := [
    [[0x6599996d,0x7efff9b1,0x65992ba6,0x7efb1e81,0x7ed74d76,0x4b29b98f,0x797db171,0x33b4ede7,0x22117175,0x4bbdb903,0x7117c873,0x3c38ce92,0x29afd06f,0x57118f30,0x2533501f,0x3bc7bc67,0x30c6bad,0x505a4617],[0x1966663f,0x6599943d,0x7effa4e5,0x7efc0de6,0x7edfe1d9,0x32002c42,0x480d2be7,0x6cfae269,0x3c398079,0x27ed0cce,0x3c6e7d22,0x110737bb,0x3b22654a,0x1e50802a,0x2ee97c17,0x77b46480],[0x4c333312,0x65999524,0x4c32e944,0x7efcdf69,0x32b3e9f2,0x3231af5a,0x6285b63c,0x3f1e12e7,0x4f957845,0x1d465e1b,0x4c7d16f3,0x27720f28,0x52423459,0xeddc3df],[0x7effffe5,0x7efffc66,0x65995f3c,0x4c30c897,0x6586c074,0x7e8cbcd9,0x7cc16521,0x5c3d28c4,0x2af1df37,0x7ea9b8c1,0x6cd31c43,0x7c872336],[0x32ccccb7,0x32ccca02,0x65996d44,0x6597cbb4,0x7ef22379,0x3279389a,0x3131f90a,0x5f01de34,0x4e92e240,0x39c92f21],[0x6599998a,0x7efffdfa,0x659979d4,0x7efeb7b8,0x7ef634a3,0x655eda51,0x7de114e5,0x6109819f],[0x1966665c,0x6599984c,0x7effeb64,0x7eff2851,0x7ef97938,0x193eca8d],[0x4c33332f,0x659998f9,0x4c33286b,0x7eff85e3],[1,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x6599999c,57,0x65999d7c,11298,94248,0x4c3c956c,0x31dac0,0x4d10d557,0x348ada0,0xac827f4,0x5932613,0x4e821d78,0x18443c52,0x64aa1dd2,0x282bd3b,0xcce4c08,0x606d8725,0x2f6ff1cf],[0x19666668,0x659999cb,826,9163,74613,0x32d40df2,0x4c58d8b7,0xa37718,0x25d632c,0x7934ab4,0x2e9c6ac5,0x1aec6cf7,0x726543e4,0x5fab6d07,0x62f5bed,0x5ee70084],[0x4c333335,0x659999c3,0x4c3335d5,7293,0x32cdaf8a,0x32d251d2,0x65b59f64,0x4caa39af,0x1aef428,0x381111ce,0x73fb2d1c,0x228825fc,0x4953ac50,0xb47c567],[1,33,0x65999bb1,0x4c334957,0x659a463c,270072,0x148588,0x65ef1104,0x4d6250f3,0x69390e50,0x9a7a57c,0x1691dff0],[0x32ccccce,0x32cccce7,0x65999b34,0x6599aa44,32736,0x32cfce92,0x32db8c9a,0x65d60ba4,0x666c2be4,0x277494c],[0x6599999b,19,0x65999ac4,3069,23374,0x659bbb53,679644,0x65c3a66d],[0x19666667,0x659999a7,198,2059,15834,0x1967daf0],[0x4c333334,0x659999a1,0x4c3333a2,1218],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_42_11 : (CJ0.blockMatrix source 42 ((11 : ℤ)-21)).rank ≤ 88 :=
  Fast.cell (z := b42_11) (Fast.bands [(21,21,1),(22,22,2),(23,23,3),(24,24,4),(25,25,5),(26,26,6),(27,27,7),(28,28,8),(29,29,9),(30,30,10),(31,31,10),(32,32,10),(33,34,9),(34,36,7),(35,38,5),(36,40,3),(37,42,1)]) (by decide +kernel) (by decide +kernel)

private def b50_6 : CJ1.Block where
  bank := .leftLow
  cap := 62
  free := [(6,2),(7,0)]
  vectors := [
    [[0x577e407d,0x76b69466,0x149ee218,0x699bc694,0xdaed01b,0x35309400,0x4a00e5fe,0x11bb7a3c,0xe1436c6,0x434c5d25,0x38fc002c,0x3ddd17c5,0x2b65d2bc,0x5a612163,0x58ffa817],[0x577e407d,0x1f3853e9,0x74668e30,0x74353865,0x187997b7,0x1cb6fc49,0x2d49e9b5,0x63719088,0x29a2a63f,0x19a9b6e6,0x1f524946,0x1e8ace7f,0x2991f41c],[0x577e407d,0x46ba136d,0x2dac7ac3,0x4688bda2,0x50f0da16,0x4ac62234,0x6183c782,0x1edc906,0x27b4dd39,0x70f4d9ae,0x3eb59f9f],[0x577e407d,0x6e3bd2f1,0x3e70a7d3,0x81815cf,0x48d8c447,0x1ed5ded,0x5f966995,0x21575f72,0x31eb47f5],[0x577e407d,0x16bd9274,0x27b3155f,0x5f650071,0x6873c3d7,0x18799a17,0x21eb1638],[0x577e407d,0x3e3f51f8,0x6873c368,0x75f13d0a,0x1afaf392],[0x577e407d,0x65c1117c,1],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x7c4d4e16,0xdaecf73,0x59ff9cb4,0xea57eac,0xfcd930c,0x1280c3f4,0x721a0db6,0x63cd8c8,0x1b4a346b,0x2ea68d22,0x18c04ef,0x100bb143,0x7388df43,0x5100c823,0x288f6edf],[0x7c4d4e16,0x1061815e,0x499e1b56,0x44076357,0x4ac62fb6,0x46ba943f,0x2b5f7977,0x59dd5f52,0x406cd51a,0x6d39b809,0x13524ce7,0x7bb9645d,0x3e9d2cab],[0x7c4d4e16,0x13143349,0x3689e80d,0xd7d7b4a,0x3d48b46c,0x971dfd3,0x21ed99a4,0x37efc5ae,0x87d0f6c,0x64bca89d,0x288f75dd],[0x7c4d4e16,0x15c6e534,0x20c302d9,0x6bba7872,0x508e3bfb,0x37e3a3d9,0x6909f5cc,0x4de5cfe3,0x32a7b32e],[0x7c4d4e16,0x1879971f,0x8496bba,0x63710cb8,0x6c1d2f44,0x4ac67496,0x5ea172c2],[0x7c4d4e16,0x1b2c490a,0x6c1d22b1,0x7653ea08,0x146d9937],[0x7c4d4e16,0x1ddefaf5,0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_50_6 : (CJ0.blockMatrix source 50 ((6 : ℤ)-21)).rank ≤ 62 :=
  Fast.cell (z := b50_6) (Fast.bands [(29,29,1),(30,30,2),(31,31,3),(32,32,4),(33,33,5),(34,34,6),(35,35,7),(36,37,7),(37,39,7),(38,41,7),(39,43,6),(40,45,5),(41,47,4),(42,49,2)]) (by decide +kernel) (by decide +kernel)

private def b58_2 : CJ1.Block where
  bank := .rightLow
  cap := 27
  free := [(3,1),(5,1),(7,1)]
  vectors := [
    [[],[1],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[],[1],[0x7f000000],[1,0],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[],[1],[0],[2,0],[0x7effffff],[1,0],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]]]
theorem rank_58_2 : (CJ0.blockMatrix source 58 ((2 : ℤ)-21)).rank ≤ 27 :=
  Fast.cell (z := b58_2) (Fast.bands [(0,48,11),(1,49,9),(2,50,7),(3,51,5),(4,52,3),(5,53,1)]) (by decide +kernel) (by decide +kernel)

private def b62_0 : CJ1.Block where
  bank := .rightLow
  cap := 9
  free := [(3,0)]
  vectors := [
    [[],[],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]]]
theorem rank_62_0 : (CJ0.blockMatrix source 62 ((0 : ℤ)-21)).rank ≤ 9 :=
  Fast.cell (z := b62_0) (Fast.bands [(0,54,9),(1,55,7),(2,56,5),(3,57,3),(4,58,1)]) (by decide +kernel) (by decide +kernel)

private def b65_1 : CJ1.Block where
  bank := .leftLow
  cap := 8
  free := [(2,0)]
  vectors := [
    [[0,0,0,0,990],[0,0,0x7effffd5],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_65_1 : (CJ0.blockMatrix source 65 ((1 : ℤ)-21)).rank ≤ 8 :=
  Fast.cell (z := b65_1) (Fast.bands [(44,44,1),(45,45,2),(46,47,2),(47,49,2),(48,51,2),(49,53,2),(50,55,2),(51,57,2),(52,59,2),(53,61,2),(54,63,1)]) (by decide +kernel) (by decide +kernel)

end CurveList50
