import ProximityPrize.SubmissionLower.CurveListRetune57B78J23C11Cells13

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace CurveListRetune57B78J23C11
private def b58_6 : CJ1.Block where
  bank := .leftLow
  cap:=69
  free:=[(6,3),(7,0),(7,1)]
  vectors:=[[[0x44e7a9f3,0x4a578769,0x634b1ca,0xc8ee15c,0x116b1fa1,0x1dc41ca8,0x69e2779,0x45dcde7,0x36ac78fd,0x33837c7f,0x4f0df1fb,0x3ceb9fbe,0x6c3f79d9,0xf036e7b,0x1940bc1e,0x3b9b180c],[0x44e7a9f3,0x56fdd76,0xc4d454,0xbca0d08,0x5a11299,0x18230a0f,0x6d7b1d6b,0x15e2b07d,0x20c9c880,0x12b9b3ff,0x3c543dfc,0x9761c2,0x71295cc,0x3abd6a0d],[0x44e7a9f3,0x3f883384,0x403ca0d1,0x4a8d6c38,0x3a13a662,0x5d0f63ae,0x106bb9bd,0x576f6c0,0x1b52d1c0,0x7666e240,0x34abd2b5,0x55148d62],[0x44e7a9f3,0x79a08992,0x459c1740,0x4f154f8,0x3522516a,0x27ed1244,0x677ea77a,0x1cf84f47,0x62b39a,0x2313bed],[0x44e7a9f3,0x34b8df9f,0x10e337a1,0x730e1d58,0x41143413,0x65d8de32,0x4b21303,0x3cd9b11c],[0x44e7a9f3,0x6ed135ad,0x211201f5,0x51fc1b63,0x4267f7ec,0x1f91b90b],[0x44e7a9f3,0x29e98bba,0x3abc5c54,1],[0,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],[[0x5bea7c9e,0x3ae1da1b,0x102c727d,0x29b856fa,0x62c7e838,469489,0x2a89de3d,0x197379be,0x461e3f25,0x79df1fa7,0x6a7c7e99,0x58e7ef62,0x45de760a,0x47db9eb9,0x5a935f5c,0x710359cb],[0x5bea7c9e,0x5df75d7e,0x31351500,0x778341fb,0x6a44a63e,0x14c283b4,0x15c75a89,0x3ac1f35,0x42721ff0,0x376cffb7,0x330f7ee2,0x25d87080,0x47ea0f01,0x4f0f4cdb],[0x5bea7c9e,0x20ce0e0,0x2f283420,0x485b0ddb,0x21e99863,0x71d8eb52,0x22ee6f38,0x5fbdaffe,0x61b46ff3,0x54b88fc5,0x44eaa2ce,0x6ece006a],[0x5bea7c9e,0x25226443,0xa05cfdd,0x3e553dfe,0x62945a66,0xf4490ec,0x13a9de4c,0x4c13d1b2,0x18ae27cb,0xd579b1b],[0x5bea7c9e,0x4837e7a6,0x40cde838,0x7c8755c7,0x650d04a0,0x29378c4d,0x2e849fca,0x546b9b2e],[0x5bea7c9e,0x6b4d6b09,0x54807d30,0x2806d897,0x3afdfd79,0x736e4bd5],[0x5bea7c9e,0xf62ee6b,0x4c1714bf,0],[1,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],[[0x7dac3c27,0x3df78347,0x5a344e9d,0x3a88cf91,0x65a552ff,0x19cfeaf0,0x689f658a,0x19d32694,0x8948a88,0x18fa054f,0x63e8153c,0x6436d6ea,0x69ada88e,0x11781acd,0x79d9b814,0x34dd3d80],[0x7dac3c27,0x3f4b4721,0x1ae9077c,0x1f9fc815,0x46058aea,0x52ca6007,0x15d50583,0x3fe2111,0x4966977,0x14639bd8,0x4f847964,0x14b25d86,0x788a7ae3,0x18201163],[0x7dac3c27,0x409f0afb,0x5949fc82,0x4555cb94,0xafbf56,0x521aa0b1,0x42ba64d3,0x4043bc3f,0x4352ad39,0x5010eea0,0x417dceb1,0x38c68b42],[0x7dac3c27,0x41f2ced5,0x17572dad,0x2dfe9de7,0x51b12170,0x697f41,0x4250e592,0x7cf2d6ae,0xd7e8e0e,0x4cbc51be],[0x7dac3c27,0x434692af,0x53109aff,0x59ee02e9,0x76c31e88,0x8a660ba,0x25589968,0x61c3186a],[0x7dac3c27,0x449a5689,0xe764476,0x4b77be73,0x2636e532,0x58ec4eef],[0x7dac3c27,0x45ee1a63,0x17c09f6c,0],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_58_6 : (CJ0.blockMatrix source 58 ((6 : ℤ)-23)).rank ≤ 69 :=
  Fast.cell (z:=b58_6) (Fast.bands [(35,35,1),(36,36,2),(37,37,3),(38,38,4),(39,39,5),(40,40,6),(41,41,7),(42,43,7),(43,45,7),(44,47,7),(45,49,7),(46,51,7),(47,53,6),(48,55,4),(49,57,2)]) (by decide +kernel) (by decide +kernel)

private def b59_5 : CJ1.Block where
  bank := .rightLow
  cap:=64
  free:=[(9,2),(11,2)]
  vectors:=[[[0,0,0x7f000000],[0,0x7efffffd,1],[0,0x7efffffb,8],[0x7efffffd,18,0x7efffffd],[0x7f000000,16,0x7effffef],[5,0x7effffe9,6],[0,0x7efffff7,16],[0,10,0x7efffffd],[0,0,0x7efffffc],[0,0,1],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0],[0,0],[0],[0]],[[0,0,0x7efffffc],[0,0x7effffed,4],[0,0x7effffe3,35],[0x7effffed,80,0x7efffff2],[0x7efffffc,70,0x7effffbb],[20,0x7effffa7,20],[0x7f000000,0x7effffe3,50],[5,20,0x7efffff7],[0,0x7efffff7,0x7efffffc],[0,10,0],[0,0,0x7efffffc],[0,0,1],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0],[0,0],[0],[0]]]
theorem rank_59_5 : (CJ0.blockMatrix source 59 ((5 : ℤ)-23)).rank ≤ 64 :=
  Fast.cell (z:=b59_5) (Fast.bands [(0,44,16),(1,45,14),(2,46,12),(3,47,10),(4,48,8),(5,49,6),(6,50,4),(7,51,2)]) (by decide +kernel) (by decide +kernel)

private def b59_6 : CJ1.Block where
  bank := .leftLow
  cap:=63
  free:=[(7,0)]
  vectors:=[[[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x7d6457e9],[0,0,0,0,0,0,0,0,0,0,0,0,0x449c04],[0,0,0,0,0,0,0,0,0,0,0x7ef5f5a9],[0,0,0,0,0,0,0,0,82251],[0,0,0,0,0,0,0x7effdf0d],[0,0,0,0,666],[0,0,0x7effffdd],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_59_6 : (CJ0.blockMatrix source 59 ((6 : ℤ)-23)).rank ≤ 63 :=
  Fast.cell (z:=b59_6) (Fast.bands [(36,36,1),(37,37,2),(38,38,3),(39,39,4),(40,40,5),(41,41,6),(42,42,7),(43,44,7),(44,46,7),(45,48,7),(46,50,7),(47,52,7),(48,54,6),(49,56,4),(50,58,2)]) (by decide +kernel) (by decide +kernel)

end CurveListRetune57B78J23C11
