import ProximityPrize.SubmissionLower.CurveList82190Defs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace CurveList82190
private def b37_14 : CJ1.Block where
  bank := .rightLow
  cap := 112
  free := [(18,0),(19,0),(20,0),(21,0)]
  vectors := [
    [[0,0,0,0x7f000000,0x7efffffe,0x7efffffe,0x7f000000],[0,0,0,0x7efffffa,0x7efffff0,0x7efffff5,0x7f000000,1],[0,0,0x7effffec,0x7effffe5,15,33,11],[0,0,0x7effffde,21,140,95,3,0x7efffffa],[0,0x7effffde,140,210,0x7effffbb,0x7effff66,0x7effffd7],[0,0x7effffec,217,0x7effffc2,0x7efffddf,0x7efffee9,21,21],[0x7efffffa,168,0x7efffe10,0x7efffddf,336,392,77],[0x7f000000,67,0x7efffdc7,363,1176,336,0x7effff91,0x7effffde],[11,0x7efffee4,1035,498,0x7efffc8f,0x7efffddf,0x7effffbb],[0x7effffca,705,0x7efffc23,0x7efffaeb,0,210,35],[165,0x7efffbab,252,1134,378,21],[0x7efffeb7,1134,504,0x7efffe87,0x7effff44,0x7effffec],[462,0x7efffd37,0x7efffd8b,0x7effffc2,14],[0x7efffe33,210,315,77,7],[330,45,0x7effffc5,0x7efffff4],[0x7effff5c,0x7effffc0,0x7efffffb,0x7f000000],[55,23,3],[0x7efffff6,0x7efffffe,0],[1,0],[0,0],[0],[0]],
    [[0,0,0,0x7efffff6,0x7effffdf,0x7effffde,0x7efffff5],[0,0,0,0x7effffb4,0x7effff3e,0x7effff70,0x7efffff2,12],[0,0,0x7effff1a,0x7efffeb1,141,380,135],[0,0,0x7efffe80,175,1568,1165,70,0x7effffac],[0,0x7efffe80,1470,2506,0x7efffdd1,0x7efff908,0x7efffdef],[0,0x7effff1a,2331,0x7efffec6,0x7effe853,0x7efff20f,111,259],[0x7effffb4,1820,0x7effec2e,0x7effe5c1,3052,4592,1015],[0x7efffff6,729,0x7effe86f,2865,13230,4816,0x7efffbd9,0x7efffe48],[120,0x7efff410,10520,7110,0x7effdd8d,0x7effe607,0x7efffc11],[0x7efffdaf,7415,0x7effdc70,0x7effc41f,0x7efffa43,2254,455],[1760,0x7effd3b5,552,12138,5040,427],[0x7efff278,11034,7140,0x7efff3b3,0x7efff764,0x7efffee2],[4752,0x7effe78f,0x7effe321,0x7efffaac,70],[0x7effedf5,1134,3255,1015,105],[3168,1035,0x7efffe5d,0x7effff7a],[0x7efffa34,0x7efffcbe,0x7effff6f,0x7effffee],[440,243,40],[0x7effffbf,0x7effffec,1],[0,0x7effffff],[1,0],[0],[0]],
    [[0,0,0,0x7effffbf,0x7effff30,0x7effff24,0x7effffb3],[0,0,0,0x7efffe33,0x7efffb47,0x7efffc51,0x7effff8c,78],[0,0,0x7efffa97,0x7efff795,690,2356,897],[0,0,0x7efff6fb,770,9464,7650,686,0x7efffdd2],[0,0x7efff6fb,8470,15890,0x7efff821,0x7effd513,0x7efff1de],[0,0x7efffa97,13706,0x7effff83,0x7eff734b,0x7effa1f1,0x7efffedb,1730],[0x7efffe33,10780,0x7eff9063,0x7eff57ad,13958,28532,7230],[0x7effffbf,4334,0x7eff770d,12186,78792,35126,0x7effeda1,0x7efff43f],[715,0x7effb9d8,59110,48756,0x7eff4cd9,0x7eff5a07,0x7effe199],[0x7efff24b,42879,0x7eff48b9,0x7efe9375,0x7effbb19,12110,3206],[10296,0x7eff05ac,0x7effec21,67284,34356,4172],[0x7effb1cd,60039,47040,0x7effd265,0x7effcd4f,0x7efff7b1],[27027,0x7eff8597,0x7eff5705,0x7effd193,0x7efffe33],[0x7eff9b75,2982,16590,6594,854],[17160,7272,0x7efffcf5,0x7efffdcb],[0x7effe1d7,0x7effed7d,0x7efffb05,0x7effff43],[2145,1123,230],[0x7efffee3,0x7effffec,20],[0,0x7effffec],[0,0x7f000000],[1],[0]],
    [[0,0,0,0x7efffee3,0x7efffc65,0x7efffc18,0x7efffe95],[0,0,0,0x7efff82f,0x7effeaf3,0x7effeedc,0x7efffd84,364],[0,0,0x7effe88b,0x7effd981,2310,10416,4277],[0,0,0x7effd8e7,2310,40964,35630,4326,0x7efff5b2],[0,0x7effd8e7,35420,71610,0x7efff3c1,0x7eff453f,0x7effbac5],[0,0x7effe88b,58366,5544,0x7efda9ab,0x7efe43f1,0x7effe63f,8295],[0x7efff82f,46200,0x7efe3637,0x7efd0769,42630,123872,36890],[0x7efffee3,18634,0x7efdbe81,36246,334572,173166,0x7effda7d,0x7effc663],[3080,0x7efed554,242340,228396,0x7efd6a81,0x7efd26bf,0x7eff58e1],[0x7effc55a,180159,0x7efd478f,0x7ef9df3d,0x7efe6291,40110,16226],[43680,0x7efbf7a4,0x7eff4ae1,266364,155736,27384],[0x7efeb78d,240219,211680,0x7eff9a9d,0x7eff437f,0x7effd3b5],[112112,0x7efe366f,0x7efd4519,0x7eff182f,0x7effe065],[0x7efe6570,2982,61110,26054,4984],[68640,33012,840,14],[0x7eff8ab3,0x7effb5a1,0x7effeb01,0x7efffacf],[8008,3983,420],[0x7efffc18,0x7effffec,210],[0,0x7effffec],[0,0x7effffec],[0],[1]]]
theorem rank_37_14 : (CJ0.blockMatrix source 37 ((14 : ℤ)-21)).rank ≤ 112 :=
  Fast.cell (z := b37_14) (Fast.bands [(0,17,21),(1,18,19),(2,19,17),(3,20,15),(4,21,13),(5,22,11),(6,23,9),(7,24,7),(8,25,5),(9,26,3),(10,27,1)]) (by decide +kernel) (by decide +kernel)

private def b40_12 : CJ1.Block where
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
theorem rank_40_12 : (CJ0.blockMatrix source 40 ((12 : ℤ)-21)).rank ≤ 101 :=
  Fast.cell (z := b40_12) (Fast.bands [(0,21,20),(1,22,18),(2,23,16),(3,24,14),(4,25,12),(5,26,10),(6,27,8),(7,28,6),(8,29,4),(9,30,2)]) (by decide +kernel) (by decide +kernel)

private def b43_11 : CJ1.Block where
  bank := .leftLow
  cap := 88
  free := [(8,0),(8,1)]
  vectors := [
    [[0x7effffd2,0x7efff949,0x7eff879c,0x7efa7fb1,0x7ed0c0e8,0x7dc25a19,0x7833963e,0x5fcd6b81,0x4ba8905,0x5cc21424,0x22a7c8b6,0x3790405a,0x233ac4c8,0x2af5a75d,0x5175802e,0x1142e809,0x77eef153,0x6b4c84a1],[0x7effffd8,0x7efffa4a,0x7eff9c17,0x7efb8af3,0x7eda9a8c,0x7e0a434e,0x79dba651,0x67ee05f1,0x269eedcd,0x57ce3977,0x25c10faf,0x69ac8eca,0x7b30ba14,0x6f2c0884,0x39f2db40,0x2d8cc0fa],[0x7effffde,0x7efffb3f,0x7effaecb,0x7efc758f,0x7ee2f02e,0x7e450bb1,0x7b2b3571,0x6e2a7671,0x3fdf3c25,0x312f4baa,0x3638f61d,0x49a9c4b4,0x5df34d6e,0x25337e42],[0x7effffe4,0x7efffc28,0x7effbfca,0x7efd4206,0x7ee9ed19,0x7e749839,0x7c31be69,0x72e53cc9,0x52783f65,0x70791a96,0x73a4ff50,0x3c55cda4],[0x7effffea,0x7efffd05,0x7effcf26,0x7efdf2c1,0x7eefb969,0x7e9a9961,0x7cfc8ba9,0x766fcf41,0x5fff920d,0x1e4474f1],[0x7efffff0,0x7efffdd6,0x7effdcf1,0x7efe8a11,0x7ef47a29,0x7eb88ef9,0x7d96f391,0x790d02f1],[0x7efffff6,0x7efffe9b,0x7effe93d,0x7eff0a2f,0x7ef85171,0x7ecfcbd3],[0x7efffffc,0x7effff54,0x7efff41c,0x7eff753c],[1,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x6599999c,0x659999d5,0x32ccd0e8,0x32ccfcd8,105672,0x4c3e0b28,0x4c6e9e31,0x66aa3d04,0x69c5db14,0xe2a4f34,0x10b7a6eb,0x553490fb,0x37014478,0x514b107a,0x7618ac41,0x2add01a3,0x1b7d345c,0x533d5cd3],[0x19666668,50,0x32ccd038,9996,83895,0x32d53684,0x2d0f90,0x6663b3d4,0x305ce5c,0xa053368,0x367788d5,0x4a6051d0,0x5cb52175,0x5809f6a6,0x6fcd546c,0x76afc959],[0x4c333335,0x32ccccf7,714,7973,65450,0x196cd2d5,0x65bb48a4,0x93e5a8,0x22a1558,0x703a3fc,0x6010743f,0x645697d6,0x6d6bfe28,0x58048b97],[1,34,0x32cccf05,0x19667ea7,0x19672995,0x32d19caa,0x18c478,0x3337832a,0x1aee5cd9,0x1e420265,0x403e45fe,0x20af37f8],[0x32ccccce,0x659999b5,0x65999b4e,0x6599abe4,0x32cd5dba,0x32d05252,0x65ab7744,0x65e568c4,0x66ab61e4,0x3620edf6],[0x6599999b,0x659999ae,0x32ccce0a,0x32ccd9fa,26536,0x659c1a24,0x65a632c4,0x3301bd3a],[0x19666667,13,0x32cccda0,2263,17980,0x19681bf6],[0x4c333334,0x32ccccd4,117,1334],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_43_11 : (CJ0.blockMatrix source 43 ((11 : ℤ)-21)).rank ≤ 88 :=
  Fast.cell (z := b43_11) (Fast.bands [(22,22,1),(23,23,2),(24,24,3),(25,25,4),(26,26,5),(27,27,6),(28,28,7),(29,29,8),(30,30,9),(31,31,10),(32,32,11),(33,33,11),(34,35,9),(35,37,7),(36,39,5),(37,41,3),(38,43,1)]) (by decide +kernel) (by decide +kernel)

private def b48_7 : CJ1.Block where
  bank := .rightLow
  cap := 74
  free := [(13,3),(15,3)]
  vectors := [
    [[0,0,0,0x7f000000],[0,0,0x7efffffb,1],[0,0,0x7efffff2,12],[0,0x7effffed,45,0x7efffffb],[0,0x7efffff2,80,0x7effffd4],[0x7efffffb,75,0x7effff89,15],[0x7f000000,36,0x7effff6b,80],[7,0x7effffa7,150,0x7effffed],[0,0x7effffec,120,0x7effffb6],[0,35,0x7effffa7,15],[0,0,0x7effffde,36],[0,0,21,0x7efffffb],[0,0,0,0x7efffffa],[0,0,0,1],[0,0,0,0],[0,0,0,0],[0,0,0],[0,0,0],[0,0],[0,0],[0],[0]],
    [[0,0,0,0x7efffffa],[0,0,0x7effffd7,6],[0,0,0x7effff98,77],[0,0x7effff75,294,0x7effffde],[0,0x7effff98,525,0x7efffef0],[0x7effffd7,490,0x7efffd22,84],[0x7efffffa,231,0x7efffc73,455],[42,0x7efffdf4,840,0x7effff98],[0x7f000000,0x7effff98,630,0x7efffe80],[7,140,0x7efffe5d,70],[0,0x7effffec,0x7effff98,147],[0,35,42,0x7effffec],[0,0,0x7effffde,0x7efffffa],[0,0,21,0],[0,0,0,0x7efffffa],[0,0,0,1],[0,0,0],[0,0,0],[0,0],[0,0],[0],[0]]]
theorem rank_48_7 : (CJ0.blockMatrix source 48 ((7 : ℤ)-21)).rank ≤ 74 :=
  Fast.cell (z := b48_7) (Fast.bands [(0,32,17),(1,33,15),(2,34,13),(3,35,11),(4,36,9),(5,37,7),(6,38,5),(7,39,3),(8,40,1)]) (by decide +kernel) (by decide +kernel)

private def b54_5 : CJ1.Block where
  bank := .leftLow
  cap := 48
  free := [(6,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0,0,0x2a1fe9],[0,0,0,0,0,0,0,0,0,0,0x7ef95948],[0,0,0,0,0,0,0,0,58905],[0,0,0,0,0,0,0x7effe670],[0,0,0,0,561],[0,0,0x7effffe0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_54_5 : (CJ0.blockMatrix source 54 ((5 : ℤ)-21)).rank ≤ 48 :=
  Fast.cell (z := b54_5) (Fast.bands [(33,33,1),(34,34,2),(35,35,3),(36,36,4),(37,37,5),(38,38,6),(39,40,6),(40,42,6),(41,44,6),(42,46,6),(43,48,6),(44,50,5),(45,52,3),(46,54,1)]) (by decide +kernel) (by decide +kernel)

private def b59_2 : CJ1.Block where
  bank := .rightLow
  cap := 27
  free := [(1,1),(2,0),(3,1),(5,1),(7,1)]
  vectors := [
    [[0x7f000000],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[0x7f000000],[0x7f000000,0],[1],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[0x7effffff],[0x7f000000,0],[0],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[0x7f000000],[0,0],[0],[1,0],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[0],[1,0],[0],[2,0],[0x7effffff],[1,0],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]]]
theorem rank_59_2 : (CJ0.blockMatrix source 59 ((2 : ℤ)-21)).rank ≤ 27 :=
  Fast.cell (z := b59_2) (Fast.bands [(0,49,11),(1,50,9),(2,51,7),(3,52,5),(4,53,3),(5,54,1)]) (by decide +kernel) (by decide +kernel)

private def b62_1 : CJ1.Block where
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
theorem rank_62_1 : (CJ0.blockMatrix source 62 ((1 : ℤ)-21)).rank ≤ 16 :=
  Fast.cell (z := b62_1) (Fast.bands [(0,54,9),(1,55,7),(2,56,5),(3,57,3),(4,58,1)]) (by decide +kernel) (by decide +kernel)

private def b65_1 : CJ1.Block where
  bank := .leftLow
  cap := 10
  free := [(2,0),(2,1)]
  vectors := [
    [[0,0,0,0,1035,3960],[0,0,0x7effffd4,0x7effffaa],[1,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,990],[0,0,0,0x7effffd5],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_65_1 : (CJ0.blockMatrix source 65 ((1 : ℤ)-21)).rank ≤ 10 :=
  Fast.cell (z := b65_1) (Fast.bands [(44,44,1),(45,45,2),(46,47,2),(47,49,2),(48,51,2),(49,53,2),(50,55,2),(51,57,2),(52,59,2),(53,61,2),(54,63,2),(55,65,1)]) (by decide +kernel) (by decide +kernel)

end CurveList82190
