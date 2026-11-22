import ProximityPrize.SubmissionLower.CurveList179876Defs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace CurveList179876
private def b40_15 : CJ1.Block where
  bank := .rightLow
  cap := 123
  free := [(19,0),(20,0),(21,0),(22,0)]
  vectors := [
    [[0,0,0,1,3,3,1],[0,0,0,7,16,9,0x7effffff,0x7effffff],[0,0,21,21,0x7effffe1,0x7effffd4,0x7efffff5,1],[0,0,35,0x7effffd7,0x7effff59,0x7effffb1,30,18],[0,35,0x7effff52,0x7effff44,210,250,45,0x7efffffa],[0,21,0x7effff05,203,756,210,0x7effff51,0x7effffc2],[7,0x7effff44,714,483,0x7efffc8f,0x7efffd61,0x7effffc9,21],[1,0x7effffb7,738,0x7efffca5,0x7efff947,0,504,112],[0x7efffff5,352,0x7efff9bc,0x7effff7a,2058,882,0x7effffd7,0x7effffde],[66,0x7efffc23,2025,1800,0x7efffc8f,0x7efffd0d,0x7effff98],[0x7effff25,1815,0x7efffb27,0x7efff67d,0x7efffe87,189,35],[495,0x7efff73d,0x7effff05,1512,567,42],[0x7efffce9,1848,1134,0x7efffec6,0x7effff36,0x7effffec],[924,0x7efffc65,0x7efffc50,0x7effff75,7],[0x7efffce9,165,375,90,7],[495,110,0x7effffcb,0x7efffff5],[0x7effff25,0x7effffa9,0x7efffff8,0x7f000000],[66,26,3],[0x7efffff5,0x7efffffe,0],[1,0],[0,0],[0],[0]],
    [[0,0,0,12,37,38,13],[0,0,0,84,200,120,0x7effffeb,0x7effffe7],[0,0,252,280,0x7efffe91,0x7efffdc7,0x7effff5f,13],[0,0,420,0x7efffe41,0x7efff7e9,0x7efffbb1,340,238],[0,420,0x7efff813,0x7efff629,2338,3200,645,0x7effffa5],[0,252,0x7efff469,1988,9324,3220,0x7efff7e9,0x7efffcad],[84,0x7efff741,8120,6888,0x7effd8f5,0x7effdd7f,0x7efffc41,280],[12,0x7efffc91,8592,0x7effdda1,0x7effab59,0x7efff91d,6160,1568],[0x7effff72,4138,0x7effb912,0x7effeee5,24108,12348,0x7effff9f,0x7efffe25],[780,0x7effd33b,21650,24240,0x7effdfd9,0x7effda45,0x7efff9e1],[0x7efff5f3,20570,0x7effd56e,0x7eff8b31,0x7effe519,2016,490],[5720,0x7eff9fd7,0x7effe549,16800,7812,756],[0x7effdcd0,19140,15666,0x7efff7cd,0x7efff653,0x7efffecd],[10296,0x7effdf85,0x7effd2b9,0x7efff629,0x7effffe5],[0x7effde7d,264,4050,1240,112],[5148,1980,0x7efffeb9,0x7effff81],[0x7efff7a0,0x7efffb73,0x7effff3e,0x7effffed],[572,290,42],[0x7effffb3,0x7effffeb,1],[0,0x7effffff],[1,0],[0],[0]],
    [[0,0,0,78,246,259,91],[0,0,0,546,1344,855,0x7effff83,0x7effff4b],[0,0,1638,1974,0x7efff725,0x7efff0e3,0x7efffb69,91],[0,0,2730,0x7efff5d5,0x7effca85,0x7effe081,2010,1694],[0,2730,0x7effcdf7,0x7effbb19,13818,21840,4950,0x7efffd76],[0,1638,0x7effb5d9,10584,61236,25284,0x7effce21,0x7effe7c8],[546,0x7effc7bb,50400,49854,0x7eff15b9,0x7eff0ffb,0x7effdedd,2010],[78,0x7effe9d5,54432,0x7eff3e69,0x7efdcf3d,0x7effa66d,39396,11808],[0x7efffc65,26433,0x7efe4938,0x7eff600b,148764,89964,2982,0x7efff263],[5005,0x7efee593,127680,166320,0x7eff7199,0x7eff04fd,0x7effcef3],[0x7effc005,127534,0x7eff3206,0x7efd17d1,0x7eff19fd,9954,3696],[36036,0x7efdbafb,0x7eff19a9,95760,55146,7056],[0x7eff2509,110517,105966,0x7efff89f,0x7effc56f,0x7efff67d],[63063,0x7eff5975,0x7efee8ef,0x7effadf9,0x7efffac1],[0x7eff36e9,0x7efff047,21420,8400,966],[30030,13992,168,0x7efffe09],[0x7effd115,0x7effe48c,0x7efff95c,0x7effff2f],[3003,1434,252],[0x7efffe95,0x7effffeb,21],[0,0x7effffeb],[0,0x7f000000],[1],[0]],
    [[0,0,0,364,1170,1260,455],[0,0,0,2548,6448,4320,0x7efffe17,0x7efffc73],[0,0,7644,9828,0x7effd911,0x7effb70e,0x7effe837,455],[0,0,12740,0x7effd559,0x7eff0401,0x7eff5e59,8100,8610],[0,12740,0x7eff1c81,0x7efeac65,57918,105280,27000,0x7efff327],[0,7644,0x7efeaac1,40460,286020,135828,0x7eff2d21,0x7eff8225],[2548,0x7efefbcd,225960,250110,0x7efc18dd,0x7efb700b,0x7eff3501,10305],[364,0x7eff9939,248472,0x7efce709,0x7ef5bbb9,0x7efda885,172872,63448],[0x7effef3f,121528,0x7ef85514,0x7efc7175,652680,449820,36162,0x7effb8c5],[23100,0x7efafb27,548310,796320,0x7efe7989,0x7efb8f0d,0x7efee871],[0x7efedabe,571978,0x7efd2eb4,0x7ef2e691,0x7efb1c35,22680,19922],[163800,0x7ef60843,0x7efb29a9,388080,259140,45780],[0x7efc26a5,467874,496566,31500,0x7eff2889,0x7effca31],[280280,0x7efd843d,0x7efb3f51,0x7efe6061,0x7effc7ad],[0x7efc9038,0x7eff7af9,81690,34440,5950],[128700,66044,6384,840],[0x7eff3c7f,0x7eff8a9d,0x7effe2b8,0x7efff9fd],[12012,5438,462],[0x7efffaac,0x7effffeb,231],[0,0x7effffeb],[0,0x7effffeb],[0],[1]]]
theorem rank_40_15 : (CJ0.blockMatrix source 40 ((15 : ℤ)-22)).rank ≤ 123 :=
  Fast.cell (z := b40_15) (Fast.bands [(0,19,22),(1,20,20),(2,21,18),(3,22,16),(4,23,14),(5,24,12),(6,25,10),(7,26,8),(8,27,6),(9,28,4),(10,29,2)]) (by decide +kernel) (by decide +kernel)

private def b43_13 : CJ1.Block where
  bank := .rightLow
  cap := 112
  free := [(18,1),(19,1),(20,0),(20,1),(21,0),(22,0)]
  vectors := [
    [[0,0,0,0x7f000000,0x7effffff,0x7f000000],[0,0,0,0x7efffffa,0x7efffff7,0x7f000000,2],[0,0,0x7effffec,0x7efffffa,29,15,0x7f000000],[0,0,0x7effffde,56,105,4,0x7effffee],[0,0x7effffde,175,70,0x7effff52,0x7effffba,7],[0,0x7effffec,238,0x7efffef7,0x7efffe5d,35,70],[0x7efffffa,175,0x7efffd76,0x7effff9f,560,147,0x7effffec],[0x7f000000,68,0x7efffd8a,840,784,0x7effff21,0x7effff7c],[11,0x7efffeda,1269,0x7efffedb,0x7efffc2d,0x7effff83,35],[0,0x7effffca,750,0x7efffa1f,0x7efffdb5,490,140],[0,165,0x7efffb33,966,882,0x7efffff3,0x7effffde],[0,0x7efffeb7,1344,0x7effff83,0x7efffe09,0x7effffb4],[0,462,0x7efffc3b,0x7efffedb,105,21],[0,0x7efffe33,420,231,14],[0,330,0x7effffb6,0x7effffbc,0x7efffffa],[0,0x7effff5c,0x7effffed,5],[0,55,13,1],[0,0x7efffff6,0x7effffff],[0,1,0],[0,0],[0,0],[0],[0]],
    [[0,0,0,0x7efffff6,0x7effffea,0x7efffff5],[0,0,0,0x7effffb4,0x7effff8b,0x7efffff1,24],[0,0,0x7effff1a,0x7effff98,323,186,0x7efffff5],[0,0,0x7efffe80,560,1239,108,0x7effff19],[0,0x7efffe80,1855,1036,0x7efff87c,0x7efffc6c,85],[0,0x7effff1a,2562,0x7efff645,0x7effec51,105,874],[0x7effffb4,1897,0x7effe5ac,0x7efff795,6230,2037,0x7efffefe],[0x7efffff6,740,0x7effe5d8,7896,9898,0x7efff891,0x7efff94e],[120,0x7efff3a3,13023,0x7efffc8f,0x7effd3fb,0x7efff7cd,441],[0,0x7efffdaf,7900,0x7effc75b,0x7effdd8d,4900,1904],[0,1760,0x7effceba,7770,10878,532,0x7efffe3a],[0,0x7efff278,13224,1134,0x7effea59,0x7efffb70],[0,4752,0x7effdd8d,0x7effee1f,819,287],[0,0x7effedf5,3192,2877,322],[0,3168,0x7effffb6,0x7efffd2e,0x7effff98],[0,0x7efffa34,0x7efffe35,11],[0,440,178,19],[0,0x7effffbf,0x7effffed],[0,0,0x7f000000],[0,1],[0,0],[0],[0]],
    [[0,0,0,0x7efffff7,0x7effffeb,0x7efffff5],[0,0,0,0x7effffbb,0x7effff8c,0x7effffeb,23],[0,0,0x7effff2f,0x7effff7b,285,188,0x7efffff6],[0,0,0x7efffea3,420,1194,185,0x7effff23],[0,0x7efffea3,1554,1260,0x7efff9a3,0x7efffc50,78],[0,0x7effff2f,2198,0x7efff9c5,0x7effed23,0x7efffedf,840],[0x7effffbb,1638,0x7effeb55,0x7efff389,5250,2190,0x7effff13],[0x7efffff7,636,0x7effeacb,4998,9744,0x7efffcb9,0x7efff97f],[100,0x7efff605,9690,2058,0x7effda45,0x7efff629,406],[0x7f000000,0x7efffe3f,5935,0x7effdbad,0x7effda1b,3276,1890],[11,1200,0x7effde14,2940,9702,1176,0x7efffe5d],[0x7effffca,0x7efff7cd,8100,3444,0x7effefc3,0x7efffb3f],[165,2520,0x7effee9d,0x7effedf5,252,266],[0x7efffeb7,0x7efff7cd,882,2310,392],[462,1200,540,0x7efffe3f,0x7effff9f],[0x7efffe33,0x7efffe3f,0x7efffe49,0x7effffe3],[330,100,120,18],[0x7effff5c,0x7efffff7,0x7efffff8],[55,0,0x7f000000],[0x7efffff6,0],[1,0],[0],[0]],
    [[0,0,0,0x7effffbf,0x7effff72,0x7effffb3],[0,0,0,0x7efffe33,0x7efffd15,0x7effff7f,156],[0,0,0x7efffa97,0x7efffcff,1922,1248,0x7effffb3],[0,0,0x7efff6fb,3080,7770,1112,0x7efffa03],[0,0x7efff6fb,10780,7420,0x7effd487,0x7effe703,559],[0,0x7efffa97,15092,0x7effcd95,0x7eff84a1,0x7efff9b7,5908],[0x7efffe33,11242,0x7eff69e3,0x7effbbdd,35840,15162,0x7efff93f],[0x7effffbf,4400,0x7eff67ab,41328,63112,0x7effe829,0x7effd13f],[715,0x7effb74f,73782,4116,0x7efeff85,0x7effb975,3010],[0,0x7efff24b,45740,0x7efecf5d,0x7eff15b9,22540,14000],[0,10296,0x7efee8a1,35364,65268,9268,0x7efff37b],[0,0x7effb1cd,72624,14868,0x7eff9071,0x7effdadf],[0,27027,0x7eff4d2d,0x7eff8c2d,882,2128],[0,0x7eff9b75,14280,15918,3444],[0,17160,1410,0x7efff4d3,0x7efffcab],[0,0x7effe1d7,0x7efff4c1,0x7efffe23],[0,2145,838,190],[0,0x7efffee3,0x7effffed],[0,0,0x7effffed],[0,0],[0,1],[0],[0]],
    [[0,0,0,0x7effff89,0x7efffef1,0x7effff68],[0,0,0,0x7efffcb9,0x7efffa46,0x7efffec9,294],[0,0,0x7efff629,0x7efff8e1,3420,2448,0x7effff74],[0,0,0x7effef99,4620,14904,2850,0x7efff4c9],[0,0x7effef99,18144,17010,0x7effb501,0x7effcec9,1008],[0,0x7efff629,25998,0x7effc101,0x7eff13c1,0x7effe729,11025],[0x7efffcb9,19488,0x7eff12c5,0x7eff4ed1,61950,30240,0x7efff3dd],[0x7effff89,7596,0x7eff0719,51408,123984,0x7efff13d,0x7effa8e9],[1200,0x7eff8990,110880,38808,0x7efe3b31,0x7eff6ecf,5376],[0x7efffff6,0x7effeae9,69690,0x7efe7911,0x7efe08fd,32256,26040],[120,14400,0x7efe7830,20160,119952,21168,0x7effe9db],[0x7efffdaf,0x7eff9d91,90720,53424,0x7eff4ae1,0x7effbb19],[1760,30240,0x7eff4b5f,0x7eff13c1,0x7efffc11,3696],[0x7efff278,0x7eff9d91,5292,27720,6342],[4752,14400,8910,0x7effef21,0x7efffa6d],[0x7effedf5,0x7effeae9,0x7effe945,0x7efffcb9],[3168,1200,1395,288],[0x7efffa34,0x7effff89,0x7effffcb],[440,0,0x7effffec],[0x7effffbf,0],[0,0],[1],[0]],
    [[0,0,0,0x7efffcf5,0x7efff8ed,0x7efffbe4],[0,0,0,0x7effeaad,0x7effd967,0x7efff6bd,2028],[0,0,0x7effc005,0x7effcd0d,21915,17208,0x7efffc32],[0,0,0x7eff955d,27720,99324,23250,0x7effb1ad],[0,0x7eff955d,115164,119910,0x7efe2e4d,0x7efe9da1,7028],[0,0x7effc005,166908,0x7efea389,0x7ef9e2d9,0x7eff0485,78120],[0x7effeaad,125748,0x7efa3313,0x7efb0441,381150,225540,0x7effaa72],[0x7efffcf5,49176,0x7ef9cc1d,292068,823536,31080,0x7efd8a55],[7800,0x7efd0580,693180,312228,0x7ef50a89,0x7efb7dd3,38436],[0x7effffbf,0x7eff76e5,445020,0x7ef6e8a9,0x7ef2baed,135576,194040],[715,93600,0x7ef65966,68040,754992,197568,0x7eff5e67],[0x7efff24b,0x7efd8029,559440,383544,0x7efc3c4d,0x7efde395],[10296,196560,0x7efbdf47,0x7efa0a39,0x7eff4ae1,27804],[0x7effb1cd,0x7efd8029,16632,160020,55272],[27027,93600,61830,0x7effcb45,0x7effd3df],[0x7eff9b75,0x7eff76e5,0x7eff75b9,0x7effd7ed],[17160,7800,6795,2508],[0x7effe1d7,0x7efffcf5,396],[2145,0,0x7effff1a],[0x7efffee3,0],[0,0],[0],[1]]]
theorem rank_43_13 : (CJ0.blockMatrix source 43 ((13 : ℤ)-22)).rank ≤ 112 :=
  Fast.cell (z := b43_13) (Fast.bands [(0,23,21),(1,24,19),(2,25,17),(3,26,15),(4,27,13),(5,28,11),(6,29,9),(7,30,7),(8,31,5),(9,32,3),(10,33,1)]) (by decide +kernel) (by decide +kernel)

private def b46_12 : CJ1.Block where
  bank := .leftLow
  cap := 98
  free := [(8,2),(9,0)]
  vectors := [
    [[0x776e82fb,0x7b1fa0c0,0x76e0be8e,0x6a53615,0x64c9b153,0x5d679343,0x32f36667,0xc10001,0x2295d781,0x7c1bc26a,0x35f7426f,0x22ce126e,0x133fc46d,0x67d1ea25,0x285567c9,0xf15a86a,0x45c82671,0x4f0ea557,0x28f7ce5c],[0x7623b89,0x3fde82fb,0x55777127,0x2ad359b8,0x9c892ac,0x5e9e10,0x2c7d44b3,0x5ad4e101,0x65058d49,0x631ee727,0x37f27159,0x3cac09cc,0x167a044b,0x39c008b0,0x53e90d83,0xf62bd97,0x35b69ce1],[0x1655f418,0x65b5f419,0x51094d6d,0x7127d0b7,0x4e15389d,0x26948c47,0xa860df5,0x5342a335,0x2d13b0b3,0x66c321db,0x5917a28,0x5488cdb1,0x63694238,0x1b46ddb2,0x5905c701],[0x2549aca7,0x6da5f419,0x17717d0c,0x3e05f45e,0x62341a33,0x6586c2f5,0x6764faa,0x6d491f0b,0x399e8cc8,0x6308855b,0x20072f30,0x5371a22c,0x137fa7fe],[0x343d6536,0x57ae82fb,0x548b29b2,0x37023bc0,0x2fcf4353,0x53406ba2,0x7623fcb3,0x52b3d52f,0x52fffe2,0x75772d78,0x106f941c],[0x43311dc5,0x23cfa0bf,0x37317d0a,0x46e23bb3,0x2578ef84,0xec4803a,0x4b509106,57970,0x2ad6c770],[0x5224d654,0x51094d66,0x6b3fa0c2,0x1c9ca6d1,0x46e24b7,0x6ec1839c,0x5a14f9e0],[0x61188ee3,0x605b88ef,0x1f90be85,0x29594d7a,0x29594e14],[0x700c4772,0x51c6535a,1],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x3b11dc42,0xec47629,0x61770043,0x2f409e70,0x7c03d20a,0x556bb6ab,0x16416868,0x6f470a08,0x20a579d5,0x17a0d8f1,0x14d99a80,0x634b8e00,0x5646c845,0x514a1ca0,0x6c540098,0x7305951,0x2115bc14,0x3aee9a54,0x43c088e4],[0x26653590,0x3b11db82,0x55a6a400,0x79171bcb,0x2952e267,0x3ae4095a,0x4dce135,0x300c69d2,0x5221401,0x48f99cc,0x657c7f49,0x6af7169c,0x1657c413,0x462a7ecb,0x491c8d2,0x73f706de,0x17a366c4],[0x11b88ede,0x11b88e3e,0xbd05366,0x46e1ac1a,0x2f3c7ec0,0x4ca7773e,0x1fb4ff7b,0x6c7a15d4,0x4f0e56b0,0x6e2bbf78,0x12d8c20b,0x2abe5a3b,0x44017698,0x33f921b2,0x7b30d4a8],[0x7c0be82d,0x11b88e5e,0x43ee1a61,0x11b82016,0x5b8b18c0,0x7315910d,0x1125d164,0x52f08cf7,0x3be7d9b4,0x2c245224,0x85c05c1,0x525ac44b,0x1a164f3c],[0x675f417b,0x3b11dbe2,0x40fa04da,0x2664e33f,0x1d862794,0x7028a9f4,0x69ea49ec,0x15b56918,0x394d5a8a,0x589c7a0d,0x69a19f1d],[0x52b29ac9,0xec476c9,0x43ee1ebc,0x2664fbdb,0x1a92e675,0x4cbd493e,0x6ff29d6a,0x7dac5501,0x73d26627],[0x3e05f417,0xbd05f14,0xec473f1,0x5e80af8,0x49d5132b,0x43e58425,0x3dd567ef],[0x29594d65,0x323594c3,0x61771065,0xbd04c6c,0xbcfac94],[0x14aca6b3,0x2f417d5,0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_46_12 : (CJ0.blockMatrix source 46 ((12 : ℤ)-22)).rank ≤ 98 :=
  Fast.cell (z := b46_12) (Fast.bands [(24,24,1),(25,25,2),(26,26,3),(27,27,4),(28,28,5),(29,29,6),(30,30,7),(31,31,8),(32,32,9),(33,33,10),(34,34,11),(35,35,11),(36,36,11),(37,38,9),(38,40,7),(39,42,5),(40,44,3),(41,46,1)]) (by decide +kernel) (by decide +kernel)

private def b51_8 : CJ1.Block where
  bank := .rightLow
  cap := 84
  free := [(14,4),(16,3),(18,2)]
  vectors := [
    [[0,0,0,1],[0,0,6,0x7effffff],[0,0,15,0x7effffef,1],[0,20,0x7effffc5,18],[0,15,0x7effff9d,90,0x7efffffb],[6,0x7effffa7,200,0x7effffc5],[1,0x7effffd7,225,0x7effff39,15],[0x7efffff9,126,0x7efffed5,100],[0,28,0x7effff2f,225,0x7effffed],[0,0x7effffc9,210,0x7effffa7],[0,0,70,0x7effff83,15],[0,0,0x7effffc9,42],[0,0,0,28,0x7efffffb],[0,0,0,0x7efffff9],[0,0,0,0,1],[0,0,0,0],[0,0,0,0],[0,0,0],[0,0,0],[0,0],[0,0],[0],[0]],
    [[0,0,0,7],[0,0,42,0x7efffff4],[0,0,105,0x7effff8a,6],[0,140,0x7efffe72,112],[0,105,0x7efffd68,567,0x7effffde],[42,0x7efffdae,1260,0x7efffe9c],[7,0x7efffef0,1400,0x7efffb5b,84],[0x7effffd0,756,0x7efff92b,560],[1,147,0x7efffb7e,1225,0x7effff98],[0x7efffff9,0x7effff0c,1050,0x7efffe3a],[0,28,245,0x7efffdca,70],[0,0x7effffc9,0x7effff6e,168],[0,0,70,49,0x7effffec],[0,0,0x7effffc9,0x7efffffa],[0,0,0,28,0],[0,0,0,0x7efffff9],[0,0,0,1],[0,0,0],[0,0,0],[0,0],[0,0],[0],[0]],
    [[0,0,0,28],[0,0,168,0x7effffd1],[0,0,420,0x7efffe41,21],[0,560,0x7efffa19,400],[0,420,0x7efff629,2044,0x7effff89],[168,0x7efff741,4536,0x7efffb31],[28,0x7efffc11,4970,0x7efff009,280],[0x7effff59,2576,0x7effe909,1848],[8,420,0x7efff1c9,3920,0x7efffeb1],[0x7effffc9,0x7efffdd1,3080,0x7efffa89],[1,168,420,0x7efff9e1,210],[0x7efffff9,0x7efffee9,0x7effff59,448],[0,28,280,28,0x7effffc9],[0,0x7effffc9,0x7effff59,0],[0,0,70,56,0],[0,0,0x7effffc9,0x7efffff9],[0,0,28,0],[0,0,0x7efffff9],[0,0,1],[0,0],[0,0],[0],[0]]]
theorem rank_51_8 : (CJ0.blockMatrix source 51 ((8 : ℤ)-22)).rank ≤ 84 :=
  Fast.cell (z := b51_8) (Fast.bands [(0,34,18),(1,35,16),(2,36,14),(3,37,12),(4,38,10),(5,39,8),(6,40,6),(7,41,4),(8,42,2)]) (by decide +kernel) (by decide +kernel)

private def b58_5 : CJ1.Block where
  bank := .leftLow
  cap := 54
  free := [(6,0),(6,1)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0,0,0x500b5a,0x3375030],[0,0,0,0,0,0,0,0,0,0,0x7ef490ab,0x7e9cfd8f],[0,0,0,0,0,0,0,0,91390,639730],[0,0,0,0,0,0,0x7effdc4e,0x7eff4286],[0,0,0,0,703,2516],[0,0,0x7effffdc,0x7effffbe],[1,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,0,0,0,0,0,0,0,0,0x449c04],[0,0,0,0,0,0,0,0,0,0,0,0x7ef5f5a9],[0,0,0,0,0,0,0,0,0,82251],[0,0,0,0,0,0,0,0x7effdf0d],[0,0,0,0,0,666],[0,0,0,0x7effffdd],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_58_5 : (CJ0.blockMatrix source 58 ((5 : ℤ)-22)).rank ≤ 54 :=
  Fast.cell (z := b58_5) (Fast.bands [(36,36,1),(37,37,2),(38,38,3),(39,39,4),(40,40,5),(41,41,6),(42,43,6),(43,45,6),(44,47,6),(45,49,6),(46,51,6),(47,53,5),(48,55,4),(49,57,2)]) (by decide +kernel) (by decide +kernel)

private def b63_2 : CJ1.Block where
  bank := .rightLow
  cap := 30
  free := [(2,1),(4,1),(6,1)]
  vectors := [
    [[1],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[1],[0x7f000000],[1,0],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]],
    [[1],[0],[2,0],[0x7effffff],[1,0],[0x7effffff],[0,1],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0,0],[0],[0]]]
theorem rank_63_2 : (CJ0.blockMatrix source 63 ((2 : ℤ)-22)).rank ≤ 30 :=
  Fast.cell (z := b63_2) (Fast.bands [(0,52,12),(1,53,10),(2,54,8),(3,55,6),(4,56,4),(5,57,2)]) (by decide +kernel) (by decide +kernel)

private def b66_2 : CJ1.Block where
  bank := .leftLow
  cap := 21
  free := [(3,0),(3,1),(3,2),(4,0)]
  vectors := [
    [[0,0,0,0,0,0,0x7effbc71,0x7efe83f7,0x7efa70e1],[0,0,0,0,1081,4094,11610],[0,0,0x7effffd3,0x7effffa9,0x7effff59],[1,0,0],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,0,0,0x7effc0aa,0x7efe9c39],[0,0,0,0,0,1035,3915],[0,0,0,0x7effffd4,0x7effffab],[0,1,0],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,0,0,0,0x7effc4b5],[0,0,0,0,0,0,990],[0,0,0,0,0x7effffd5],[0,0,1],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,0,0,0,0x7ef887ae],[0,0,0,0,0,0,28380],[0,0,0,0,0x7efffc4f],[0,0,0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_66_2 : (CJ0.blockMatrix source 66 ((2 : ℤ)-22)).rank ≤ 21 :=
  Fast.cell (z := b66_2) (Fast.bands [(44,44,1),(45,45,2),(46,46,3),(47,48,3),(48,50,3),(49,52,3),(50,54,3),(51,56,3),(52,58,3),(53,60,3),(54,62,3),(55,64,2),(56,66,1)]) (by decide +kernel) (by decide +kernel)

private def b69_1 : CJ1.Block where
  bank := .leftLow
  cap := 12
  free := [(2,0),(2,1),(2,2),(3,0)]
  vectors := [
    [[0,0,0,0,1225,4704,13536],[0,0,0x7effffd0,0x7effffa2,0x7effff49],[1,0,0],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,1176,4512],[0,0,0,0x7effffd1,0x7effffa4],[0,1,0],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,0,1128],[0,0,0,0,0x7effffd2],[0,0,1],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0,0,0,0,0,0,34592],[0,0,0,0,0x7efffbc8],[0,0,0],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_69_1 : (CJ0.blockMatrix source 69 ((1 : ℤ)-22)).rank ≤ 12 :=
  Fast.cell (z := b69_1) (Fast.bands [(47,47,1),(48,48,2),(49,50,2),(50,52,2),(51,54,2),(52,56,2),(53,58,2),(54,60,2),(55,62,2),(56,64,2),(57,66,2),(58,68,1)]) (by decide +kernel) (by decide +kernel)

end CurveList179876
