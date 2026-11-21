import ProximityPrize.SubmissionLower.CurveList179925WitnessDefs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace CurveList179925Witness
private def b39_14 : CJ1.Block where
  bank := .rightLow
  cap := 112
  free := [(18,0),(19,0),(20,0),(21,0)]
  vectors := [
    [[0,0,0,0x7f000000,0x7efffffe,0x7efffffe,0x7f000000],[0,0,0,0x7efffffa,0x7efffff0,0x7efffff5,0x7f000000,1],[0,0,0x7effffec,0x7effffe5,15,33,11],[0,0,0x7effffde,21,140,95,3,0x7efffffa],[0,0x7effffde,140,210,0x7effffbb,0x7effff66,0x7effffd7],[0,0x7effffec,217,0x7effffc2,0x7efffddf,0x7efffee9,21,21],[0x7efffffa,168,0x7efffe10,0x7efffddf,336,392,77],[0x7f000000,67,0x7efffdc7,363,1176,336,0x7effff91,0x7effffde],[11,0x7efffee4,1035,498,0x7efffc8f,0x7efffddf,0x7effffbb],[0x7effffca,705,0x7efffc23,0x7efffaeb,0,210,35],[165,0x7efffbab,252,1134,378,21],[0x7efffeb7,1134,504,0x7efffe87,0x7effff44,0x7effffec],[462,0x7efffd37,0x7efffd8b,0x7effffc2,14],[0x7efffe33,210,315,77,7],[330,45,0x7effffc5,0x7efffff4],[0x7effff5c,0x7effffc0,0x7efffffb,0x7f000000],[55,23,3],[0x7efffff6,0x7efffffe,0],[1,0],[0,0],[0],[0]],
    [[0,0,0,0x7efffff6,0x7effffdf,0x7effffde,0x7efffff5],[0,0,0,0x7effffb4,0x7effff3e,0x7effff70,0x7efffff2,12],[0,0,0x7effff1a,0x7efffeb1,141,380,135],[0,0,0x7efffe80,175,1568,1165,70,0x7effffac],[0,0x7efffe80,1470,2506,0x7efffdd1,0x7efff908,0x7efffdef],[0,0x7effff1a,2331,0x7efffec6,0x7effe853,0x7efff20f,111,259],[0x7effffb4,1820,0x7effec2e,0x7effe5c1,3052,4592,1015],[0x7efffff6,729,0x7effe86f,2865,13230,4816,0x7efffbd9,0x7efffe48],[120,0x7efff410,10520,7110,0x7effdd8d,0x7effe607,0x7efffc11],[0x7efffdaf,7415,0x7effdc70,0x7effc41f,0x7efffa43,2254,455],[1760,0x7effd3b5,552,12138,5040,427],[0x7efff278,11034,7140,0x7efff3b3,0x7efff764,0x7efffee2],[4752,0x7effe78f,0x7effe321,0x7efffaac,70],[0x7effedf5,1134,3255,1015,105],[3168,1035,0x7efffe5d,0x7effff7a],[0x7efffa34,0x7efffcbe,0x7effff6f,0x7effffee],[440,243,40],[0x7effffbf,0x7effffec,1],[0,0x7effffff],[1,0],[0],[0]],
    [[0,0,0,0x7effffbf,0x7effff30,0x7effff24,0x7effffb3],[0,0,0,0x7efffe33,0x7efffb47,0x7efffc51,0x7effff8c,78],[0,0,0x7efffa97,0x7efff795,690,2356,897],[0,0,0x7efff6fb,770,9464,7650,686,0x7efffdd2],[0,0x7efff6fb,8470,15890,0x7efff821,0x7effd513,0x7efff1de],[0,0x7efffa97,13706,0x7effff83,0x7eff734b,0x7effa1f1,0x7efffedb,1730],[0x7efffe33,10780,0x7eff9063,0x7eff57ad,13958,28532,7230],[0x7effffbf,4334,0x7eff770d,12186,78792,35126,0x7effeda1,0x7efff43f],[715,0x7effb9d8,59110,48756,0x7eff4cd9,0x7eff5a07,0x7effe199],[0x7efff24b,42879,0x7eff48b9,0x7efe9375,0x7effbb19,12110,3206],[10296,0x7eff05ac,0x7effec21,67284,34356,4172],[0x7effb1cd,60039,47040,0x7effd265,0x7effcd4f,0x7efff7b1],[27027,0x7eff8597,0x7eff5705,0x7effd193,0x7efffe33],[0x7eff9b75,2982,16590,6594,854],[17160,7272,0x7efffcf5,0x7efffdcb],[0x7effe1d7,0x7effed7d,0x7efffb05,0x7effff43],[2145,1123,230],[0x7efffee3,0x7effffec,20],[0,0x7effffec],[0,0x7f000000],[1],[0]],
    [[0,0,0,0x7efffee3,0x7efffc65,0x7efffc18,0x7efffe95],[0,0,0,0x7efff82f,0x7effeaf3,0x7effeedc,0x7efffd84,364],[0,0,0x7effe88b,0x7effd981,2310,10416,4277],[0,0,0x7effd8e7,2310,40964,35630,4326,0x7efff5b2],[0,0x7effd8e7,35420,71610,0x7efff3c1,0x7eff453f,0x7effbac5],[0,0x7effe88b,58366,5544,0x7efda9ab,0x7efe43f1,0x7effe63f,8295],[0x7efff82f,46200,0x7efe3637,0x7efd0769,42630,123872,36890],[0x7efffee3,18634,0x7efdbe81,36246,334572,173166,0x7effda7d,0x7effc663],[3080,0x7efed554,242340,228396,0x7efd6a81,0x7efd26bf,0x7eff58e1],[0x7effc55a,180159,0x7efd478f,0x7ef9df3d,0x7efe6291,40110,16226],[43680,0x7efbf7a4,0x7eff4ae1,266364,155736,27384],[0x7efeb78d,240219,211680,0x7eff9a9d,0x7eff437f,0x7effd3b5],[112112,0x7efe366f,0x7efd4519,0x7eff182f,0x7effe065],[0x7efe6570,2982,61110,26054,4984],[68640,33012,840,14],[0x7eff8ab3,0x7effb5a1,0x7effeb01,0x7efffacf],[8008,3983,420],[0x7efffc18,0x7effffec,210],[0,0x7effffec],[0,0x7effffec],[0],[1]]]
theorem rank_39_14 : (CJ0.blockMatrix source 39 ((14 : ℤ)-21)).rank ≤ 112 :=
  Fast.cell (z := b39_14) (Fast.bands [(0,19,21),(1,20,19),(2,21,17),(3,22,15),(4,23,13),(5,24,11),(6,25,9),(7,26,7),(8,27,5),(9,28,3),(10,29,1)]) (by decide +kernel) (by decide +kernel)

private def b42_12 : CJ1.Block where
  bank := .rightLow
  cap := 101
  free := [(17,1),(18,1),(19,0),(19,1),(20,0),(21,0)]
  vectors := [
    [[0,0,0,1,2,1],[0,0,0,7,11,3,0x7f000000],[0,0,21,14,0x7effffef,0x7efffff5],[0,0,35,0x7effffde,0x7effffa6,0x7effffeb,7],[0,35,0x7effff75,0x7effff98,84,49],[0,21,0x7effff36,126,315,49,0x7effffec],[7,0x7effff67,448,224,0x7effff0c,0x7effff9f],[1,0x7effffc4,477,0x7efffe79,0x7efffdd1,0x7effffec,35],[0x7efffff7,234,0x7efffce9,0x7effff9f,420,105],[0,45,0x7efffdfd,714,490,0x7effffbb,0x7effffde],[0,0x7effff89,714,0x7effff05,0x7efffe79,0x7effffc9],[0,210,0x7efffd8b,0x7effff83,112,21],[0,0x7effff05,336,168,7],[0,210,0x7effffad,0x7effffc2,0x7efffffa],[0,0x7effff89,0x7efffff8,6],[0,45,11,1],[0,0x7efffff7,0x7effffff],[0,1,0],[0,0],[0,0],[0],[0]],
    [[0,0,0,10,21,11],[0,0,0,70,118,36,0x7efffff6],[0,0,210,168,0x7effff51,0x7effff7a],[0,0,350,0x7efffedb,0x7efffc3b,0x7efffee9,78],[0,350,0x7efffacf,0x7efffb15,784,566],[0,210,0x7efff84b,896,3360,714,0x7effff13],[70,0x7efffa19,4116,2954,0x7efff6fb,0x7efffb69],[10,0x7efffda7,4554,0x7efff485,0x7effe7f1,0x7efffd8b,406],[0x7effff9e,2269,0x7effe3e1,0x7efff6d1,4130,1344],[0,440,0x7effecf0,5796,5880,0x7efffee9,0x7efffe5d],[0,0x7efffb7e,6504,0x7efffc11,0x7effefed,0x7efffcc7],[0,1980,0x7effeb01,0x7efff725,924,266],[0,0x7efff6fb,2478,2016,210],[0,1848,0x7efffedb,0x7efffd8b,0x7effff9f],[0,0x7efffc23,0x7efffedb,24],[0,330,146,18],[0,0x7effffca,0x7effffee],[0,0,0x7f000000],[0,1],[0,0],[0],[0]],
    [[0,0,0,10,22,12],[0,0,0,70,127,44,0x7efffff6],[0,0,210,204,0x7effff63,0x7effff71],[0,0,350,0x7effff2f,0x7efffc23,0x7efffeaa,78],[0,350,0x7efffb4d,0x7efffa43,640,602],[0,210,0x7efff8c9,392,3360,930,0x7effff13],[70,0x7efffa6d,3444,3584,0x7efff89f,0x7efffb15],[10,0x7efffdcb,4002,0x7efff9ef,0x7effe7f1,0x7efffbe7,406],[0x7effffa7,1990,0x7effe9c9,0x7efff1e5,3500,1470],[1,360,0x7efff098,3612,6090,224,0x7efffe5d],[0x7efffff7,0x7efffcb9,4740,672,0x7efff1e5,0x7efffc49],[45,1260,0x7efff2e1,0x7efff52d,546,266],[0x7effff89,0x7efffb15,1092,1848,294],[210,840,210,0x7efffe33,0x7effff9f],[0x7effff05,0x7efffe99,0x7efffeb7,0x7efffff5],[210,90,110,18],[0x7effff89,0x7efffff7,0x7efffff7],[45,0,0x7f000000],[0x7efffff7,0],[1,0],[0],[0]],
    [[0,0,0,55,120,66],[0,0,0,385,685,234,0x7effffbf],[0,0,1155,1050,0x7efffc6f,0x7efffcc5],[0,0,1925,0x7efffaac,0x7effea98,0x7efff883,474],[0,1925,0x7effe4a9,0x7effe1bc,3724,3563],[0,1155,0x7effd694,3416,18795,5439,0x7efffa42],[385,0x7effe003,21084,18704,0x7effd5c2,0x7effe1fb],[55,0x7efff336,24111,0x7effcfc5,0x7eff7933,0x7effe62a,2569],[0x7efffde5,12169,0x7eff70d9,0x7effbc3f,19880,9345],[0,2376,0x7eff9bba,26838,33810,2240,0x7efff542],[0,0x7effe7f1,33234,0x7efffd0d,0x7effaf9d,0x7effe6a1],[0,10395,0x7eff99cb,0x7effc767,2436,1841],[0,0x7effd199,10794,10584,2373],[0,9240,0x7efffedb,0x7efff668,0x7efffd14],[0,0x7effed71,0x7efff90e,0x7efffec3],[0,1485,641,171],[0,0x7effff25,0x7effffee],[0,0,0x7effffee],[0,0],[0,1],[0],[0]],
    [[0,0,0,110,250,141],[0,0,0,770,1460,540,0x7effff7f],[0,0,2310,2460,0x7efff976,0x7efff949],[0,0,3850,0x7efff89f,0x7effd40f,0x7effef0d,930],[0,3850,0x7effce3d,0x7effbb19,6320,7315],[0,2310,0x7effb213,1792,38010,12390,0x7efff4cb],[770,0x7effc34d,35490,43960,0x7effb6ff,0x7effc2d5],[110,0x7effe7d3,42750,0x7effd559,0x7efeed79,0x7effc27b,4970],[0x7efffc23,21575,0x7eff1bb9,0x7eff45cb,35980,18900],[10,3960,0x7eff5b3d,32340,71400,7000,0x7effeb7f],[0x7effff9e,0x7effdbe9,49440,15120,0x7eff683f,0x7effcd41],[440,13860,0x7eff7e65,0x7eff77d5,3360,3430],[0x7efffb7e,0x7effc9dd,8610,21000,4620],[1980,9240,4200,0x7effeec7,0x7efffacf],[0x7efff6fb,0x7efff089,0x7effefb7,0x7efffde5],[1848,990,1210,270],[0x7efffc23,0x7effff93,0x7effffc0],[330,0,0x7effffed],[0x7effffca,0],[0,0],[1],[0]],
    [[0,0,0,660,1540,900],[0,0,0,4620,9075,3600,0x7efffcbf],[0,0,13860,15840,0x7effdb35,0x7effd469],[0,0,23100,0x7effdbe9,0x7efef41d,0x7eff8b85,6020],[0,23100,0x7efedf41,0x7efe49f5,31440,48300],[0,13860,0x7efe33cf,0x7efffcb9,228060,89460,0x7effb696],[4620,0x7efe9711,201600,280392,0x7efe9bfd,0x7efe6291],[660,0x7eff6fa1,250380,0x7eff676d,0x7ef99aa9,0x7efe13d1,33060],[0x7effe8cd,127920,0x7efaef71,0x7efb3b61,183120,132300],[55,23760,0x7efc398f,163800,428400,79800,0x7eff748d],[0x7efffde5,0x7eff2771,284760,115920,0x7efcd8d1,0x7efe86a9],[2376,83160,0x7efd3169,0x7efcbb49,0x7effe765,24108],[0x7effe7f1,0x7efebb29,40320,115920,39060],[10395,55440,28980,0x7effc005,0x7effd973],[0x7effd199,0x7effa331,0x7effa27d,0x7effe3e1],[9240,5940,5640,2220],[0x7effed71,0x7efffd6d,240],[1485,0,0x7effff2f],[0x7effff25,0],[0,0],[0],[1]]]
theorem rank_42_12 : (CJ0.blockMatrix source 42 ((12 : ℤ)-21)).rank ≤ 101 :=
  Fast.cell (z := b42_12) (Fast.bands [(0,23,20),(1,24,18),(2,25,16),(3,26,14),(4,27,12),(5,28,10),(6,29,8),(7,30,6),(8,31,4),(9,32,2)]) (by decide +kernel) (by decide +kernel)

private def b45_11 : CJ1.Block where
  bank := .leftLow
  cap := 88
  free := [(8,0),(8,1)]
  vectors := [
    [[0x32cccc9b,0x19665ed5,0x7eff70cd,0x6592aeec,0x328def98,0x4a7365df,0x28a1fe06,0x4d704649,0x7b8f10d6,0x73d65b5a,0x26592903,0x51a753e2,0x2f4756ec,0x4580d3bb,0x6b314c9e,0x135c730f,0x1001b109,0x99c1951],[0x4c333308,0x19665ff4,0x32cc559f,0x4c2d929a,0x6567925f,0x1809a4da,0x2b0c5899,0x409ac67d,0x168d272,0x319ca3e7,0x43785368,0x296a24dd,0x62e243ee,0x1da8b38a,0x532cfd77,0x7b03496b],[0x65999975,0x6599943a,0x65993873,0x65951c68,0x7ed8e918,0x4b2819fd,0x4660dfd0,0x30f41e47,0x5e2f04ac,0x2e269bb,0x5fdced79,0x448157fc,0x71dd39,0x763008c7],[0x7effffe2,0x7efffba6,0x65994c8e,0x7efc825b,0x7ee2275e,0x7e37903a,0x7ab45331,0x386eff17,0x314b2215,0x7480f5a7,0x65b94d9f,0x5e5ed529],[0x1966664e,0x65999638,0x7effc537,0x7efd60c5,0x7ee9e39a,0x323a2d3a,0x4918a8f7,0x70e70721,0x485e8675,0x4711b1b2],[0x32ccccbb,0x196663f0,0x7effd5b4,0x6597ba45,0x32bd1722,0x18fea8e5,0x1736f045,0x7523d7a9],[0x4c333328,0x196664cf,0x32ccb14b,0x4c31f7c7,0x658f1e5c,0x4bed1e57],[0x65999995,0x659998d5,0x65998b44,0x6598e884],[1,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x6599999c,0x32cccd0b,1170,0x4c336bbe,0x659b9bac,0x1974b524,0x65ecc49e,0x19561a1,0x20003341,0x6413afeb,0x4bc968e8,0x9b11fb4,0x18cdca3c,0x65dca9,0x5f7062c9,0x6da0cd8,0x50da2a28,0x29f2046a],[0x19666668,0x32cccd02,0x65999d6b,0x19669489,0x4c34cd78,0x32d7f922,0x65d92b81,0x4d627f5b,0x37a20fa6,0x2a80276d,0x4e736309,0x454be389,0x4ba1be25,0x2603cd67,0x4527723f,0x743fbfb],[0x4c333335,0x4c333360,0x4c333653,0x4c335825,82362,0x196efc76,0x19964a01,0x1a46639d,0x1ce5d985,0xc1ea794,0x70fa8357,0x2fb9bf2e,0x389f776d,0x41ec8c67],[1,36,0x4c3335b1,7392,63189,424116,0x237930,0x1a0970cd,0x2800fd4,0x87f4a50,0x19404e58,0x421cba80],[0x32ccccce,0x4c333350,490,5593,47124,0x659e5c9c,0x1980287d,0x74c2c8,0x1c379b0,0x5e4568c],[0x6599999b,0x32cccce2,357,0x4c3342fb,0x659a1dac,0x32d0325a,0x32df0ea2,0x521620],[0x19666667,0x32ccccdb,0x65999a88,0x196670fd,0x4c338cb7,0x1968b905],[0x4c333334,0x4c33333b,0x4c3333b7,0x4c333967],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_45_11 : (CJ0.blockMatrix source 45 ((11 : ℤ)-21)).rank ≤ 88 :=
  Fast.cell (z := b45_11) (Fast.bands [(24,24,1),(25,25,2),(26,26,3),(27,27,4),(28,28,5),(29,29,6),(30,30,7),(31,31,8),(32,32,9),(33,33,10),(34,34,11),(35,35,11),(36,37,9),(37,39,7),(38,41,5),(39,43,3),(40,45,1)]) (by decide +kernel) (by decide +kernel)

private def b50_7 : CJ1.Block where
  bank := .rightLow
  cap := 74
  free := [(13,3),(15,3)]
  vectors := [
    [[0,0,0,0x7f000000],[0,0,0x7efffffb,1],[0,0,0x7efffff2,12],[0,0x7effffed,45,0x7efffffb],[0,0x7efffff2,80,0x7effffd4],[0x7efffffb,75,0x7effff89,15],[0x7f000000,36,0x7effff6b,80],[7,0x7effffa7,150,0x7effffed],[0,0x7effffec,120,0x7effffb6],[0,35,0x7effffa7,15],[0,0,0x7effffde,36],[0,0,21,0x7efffffb],[0,0,0,0x7efffffa],[0,0,0,1],[0,0,0,0],[0,0,0,0],[0,0,0],[0,0,0],[0,0],[0,0],[0],[0]],
    [[0,0,0,0x7efffffa],[0,0,0x7effffd7,6],[0,0,0x7effff98,77],[0,0x7effff75,294,0x7effffde],[0,0x7effff98,525,0x7efffef0],[0x7effffd7,490,0x7efffd22,84],[0x7efffffa,231,0x7efffc73,455],[42,0x7efffdf4,840,0x7effff98],[0x7f000000,0x7effff98,630,0x7efffe80],[7,140,0x7efffe5d,70],[0,0x7effffec,0x7effff98,147],[0,35,42,0x7effffec],[0,0,0x7effffde,0x7efffffa],[0,0,21,0],[0,0,0,0x7efffffa],[0,0,0,1],[0,0,0],[0,0,0],[0,0],[0,0],[0],[0]]]
theorem rank_50_7 : (CJ0.blockMatrix source 50 ((7 : ℤ)-21)).rank ≤ 74 :=
  Fast.cell (z := b50_7) (Fast.bands [(0,34,17),(1,35,15),(2,36,13),(3,37,11),(4,38,9),(5,39,7),(6,40,5),(7,41,3),(8,42,1)]) (by decide +kernel) (by decide +kernel)

private def b56_5 : CJ1.Block where
  bank := .leftLow
  cap := 48
  free := [(6,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0,0,0x3a91ac],[0,0,0,0,0,0,0,0,0,0,0x7ef736f4],[0,0,0,0,0,0,0,0,73815],[0,0,0,0,0,0,0x7effe1a7],[0,0,0,0,630],[0,0,0x7effffde],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_56_5 : (CJ0.blockMatrix source 56 ((5 : ℤ)-21)).rank ≤ 48 :=
  Fast.cell (z := b56_5) (Fast.bands [(35,35,1),(36,36,2),(37,37,3),(38,38,4),(39,39,5),(40,40,6),(41,42,6),(42,44,6),(43,46,6),(44,48,6),(45,50,6),(46,52,5),(47,54,3),(48,56,1)]) (by decide +kernel) (by decide +kernel)

private def b61_2 : CJ1.Block where
  bank := .rightLow
  cap := 27
  free := [(1,1),(2,0),(3,1),(5,1),(7,1)]
  vectors := [
    [[0x7f000000],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[0x7f000000],[0x7f000000,0],[1],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[0x7effffff],[0x7f000000,0],[0],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[0x7f000000],[0,0],[0],[1,0],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[0],[1,0],[0],[2,0],[0x7effffff],[1,0],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]]]
theorem rank_61_2 : (CJ0.blockMatrix source 61 ((2 : ℤ)-21)).rank ≤ 27 :=
  Fast.cell (z := b61_2) (Fast.bands [(0,51,11),(1,52,9),(2,53,7),(3,54,5),(4,55,3),(5,56,1)]) (by decide +kernel) (by decide +kernel)

private def b64_1 : CJ1.Block where
  bank := .rightLow
  cap := 16
  free := [(0,0),(1,0),(2,0),(3,0),(5,0),(7,0)]
  vectors := [
    [[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]],
    [[0],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]],
    [[0],[0],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]],
    [[0],[0],[0],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]],
    [[0],[0],[0],[0],[0x7f000000],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]],
    [[0],[0],[0],[0],[0x7f000000],[0],[0x7f000000],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]]]
theorem rank_64_1 : (CJ0.blockMatrix source 64 ((1 : ℤ)-21)).rank ≤ 16 :=
  Fast.cell (z := b64_1) (Fast.bands [(0,56,9),(1,57,7),(2,58,5),(3,59,3),(4,60,1)]) (by decide +kernel) (by decide +kernel)

private def b67_1 : CJ1.Block where
  bank := .leftLow
  cap := 10
  free := [(2,0),(2,1)]
  vectors := [
    [[0,0,0,0,1128,4324],[0,0,0x7effffd2,0x7effffa6],[1,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,1081],[0,0,0,0x7effffd3],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_67_1 : (CJ0.blockMatrix source 67 ((1 : ℤ)-21)).rank ≤ 10 :=
  Fast.cell (z := b67_1) (Fast.bands [(46,46,1),(47,47,2),(48,49,2),(49,51,2),(50,53,2),(51,55,2),(52,57,2),(53,59,2),(54,61,2),(55,63,2),(56,65,2),(57,67,1)]) (by decide +kernel) (by decide +kernel)

end CurveList179925Witness
