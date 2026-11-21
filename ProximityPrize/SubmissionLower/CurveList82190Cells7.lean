import ProximityPrize.SubmissionLower.CurveList82190Defs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace CurveList82190
private def b38_13 : CJ1.Block where
  bank := .rightLow
  cap := 109
  free := [(19,0),(20,0),(21,0)]
  vectors := [
    [[0,0,0,0,0x7f000000,0x7effffff,0x7f000000],[0,0,0,0x7efffff9,0x7efffff4,0x7efffffd,1],[0,0,0,0x7effffe5,0x7effffe9,17,14],[0,0,0x7effffc9,28,120,37,0x7efffff9],[0,0,0x7effffbb,196,210,0x7effffb1,0x7effffbd],[0,0x7effffc9,378,0x7effffc9,0x7efffe17,0x7effff89,28],[0,0x7effffe5,392,0x7efffd37,0x7efffd7d,280,168],[0x7efffff9,236,0x7efffb99,294,1120,168,0x7effffc9],[0x7f000000,78,0x7efffca0,1632,882,0x7efffd7d,0x7effff13],[11,0x7efffead,1785,0x7efffc11,0x7efffa43,0x7effffc9,70],[0x7effffca,870,0x7efff755,0x7efffeb1,882,196],[165,0x7efffa61,1596,1008,0x7effff83,0x7effffc9],[0x7efffeb7,1596,0x7efffe33,0x7efffd61,0x7effffad],[462,0x7efffb69,0x7effff2f,168,28],[0x7efffe33,540,240,8],[330,0x7effff89,0x7effffb1,0x7efffff9],[0x7effff5c,0x7efffff7,7],[55,12,1],[0x7efffff6,0x7effffff],[1,0],[0],[0]],
    [[0,0,0,0,0x7efffff6,0x7effffea,0x7efffff5],[0,0,0,0x7effffa9,0x7effff69,0x7effffce,12],[0,0,0,0x7efffecd,0x7efffed5,178,171],[0,0,0x7efffd99,224,1380,488,0x7effffa0],[0,0,0x7efffcff,2030,2604,0x7efffd09,0x7efffcb2],[0,0x7efffd99,4032,14,0x7effea21,0x7efff971,344],[0,0x7efffecd,4228,0x7effe471,0x7effdfe7,2660,2148],[0x7effffa9,2560,0x7effd205,1176,12950,2688,0x7efffd45],[0x7efffff6,849,0x7effdc11,15888,12348,0x7effe6cb,0x7efff3a5],[120,0x7efff1be,18420,0x7effe321,0x7effbb19,0x7efff92b,896],[0x7efffdaf,9175,0x7effab29,0x7effe279,9408,2786],[1760,0x7effc62c,13776,13272,0x7efffe09,0x7efffd1b],[0x7efff278,15786,0x7efff971,0x7effe1d1,0x7efffa97],[4752,0x7effd583,0x7effef99,1512,392],[0x7effedf5,4302,3180,292],[3168,0x7efffe3f,0x7efffc91,0x7effff85],[0x7efffa34,0x7efffe76,32],[440,177,20],[0x7effffbf,0x7effffec],[0,0x7f000000],[1],[0]],
    [[0,0,0,0,0x7effffbf,0x7effff72,0x7effffb3],[0,0,0,0x7efffdf1,0x7efffc44,0x7efffea2,78],[0,0,0,0x7efff8c9,0x7efff845,978,1131],[0,0,0x7efff191,924,8460,3468,0x7efffd84],[0,0,0x7effedf5,11550,16884,0x7efff269,0x7effe9b1],[0,0x7efff191,23562,2982,0x7eff7cc1,0x7effcec9,2289],[0,0x7efff8c9,24948,0x7eff6965,0x7eff2f27,11760,14868],[0x7efffdf1,15180,0x7efef80d,0x7efff91d,77070,22428,0x7effed7d],[0x7effffbf,5049,0x7eff2e5b,85968,82908,0x7eff88bb,0x7effa715],[715,0x7effac22,104850,0x7eff8dd1,0x7efe6291,0x7effb213,6216],[0x7efff24b,53175,0x7efe3159,0x7eff1d99,47628,21378],[10296,0x7efeb778,67536,82152,5796,0x7effeb2b],[0x7effb1cd,87066,1260,0x7eff5e91,0x7effd0c1],[27027,0x7eff210b,0x7eff8ecd,4032,2982],[0x7eff9b75,20142,18000,3732],[17160,0x7efffe3f,0x7efff1b5,0x7efffbed],[0x7effe1d7,0x7efff5de,0x7efffe4b],[2145,837,210],[0x7efffee3,0x7effffec],[0,0x7effffec],[0],[1]]]
theorem rank_38_13 : (CJ0.blockMatrix source 38 ((13 : ℤ)-21)).rank ≤ 109 :=
  Fast.cell (z := b38_13) (Fast.bands [(0,18,21),(1,19,19),(2,20,17),(3,21,15),(4,22,13),(5,23,11),(6,24,9),(7,25,7),(8,26,5),(9,27,3),(10,28,1)]) (by decide +kernel) (by decide +kernel)

private def b41_11 : CJ1.Block where
  bank := .rightLow
  cap := 98
  free := [(18,1),(19,1),(20,0),(21,0)]
  vectors := [
    [[0,0,0,0,1,1],[0,0,0,8,6,0x7f000000],[0,0,0,28,4,0x7efffff2],[0,0,56,0x7effffc9,0x7effffc5,8],[0,0,70,0x7effff2f,0x7effffc9,76],[0,56,0x7efffe95,210,224,0x7effffe5],[0,28,0x7efffe95,714,140,0x7effff3d],[8,0x7effff29,980,0x7efffdd1,0x7efffe5d,56],[1,0x7effffba,720,0x7efffaa5,0x7effffbb,294],[0x7efffff7,279,0x7efffac1,980,420,0x7effffbb],[0,45,0x7efffd85,1512,0x7effff3d,0x7efffef7],[0,0x7effff89,924,0x7efffc11,0x7effff3d,56],[0,210,0x7efffc8f,336,140],[0,0x7effff05,546,0,0x7effffe5],[0,210,0x7effff35,0x7effffdd],[0,0x7effff89,36,8],[0,45,1],[0,0x7efffff7,0x7f000000],[0,1],[0,0],[0],[0]],
    [[0,0,0,0,10,11],[0,0,0,80,69,0x7efffff6],[0,0,0,280,76,0x7effff59],[0,0,560,0x7efffe25,0x7efffd3d,89],[0,0,700,0x7efff84b,0x7efffc81,868],[0,560,0x7efff247,1470,2744,0x7efffec5],[0,280,0x7efff21d,6384,2660,0x7efff709],[80,0x7efff7b5,9212,0x7efff183,0x7effeaad,644],[10,0x7efffd44,6912,0x7effd14d,0x7efff36d,3570],[0x7effff9e,2709,0x7effcf71,6860,6090,0x7efffcc7],[0,440,0x7effe86d,13104,980,0x7efff2a9],[0,0x7efffb7e,8484,0x7effe279,0x7efff175,686],[0,1980,0x7effe1fb,1344,1988],[0,0x7efff6fb,4326,1008,0x7efffe95],[0,1848,0x7efffafd,0x7efffd79],[0,0x7efffc23,36,116],[0,330,91],[0,0x7effffca,0x7effffee],[0,0],[0,1],[0],[0]],
    [[0,0,0,0,10,11],[0,0,0,80,70,0x7efffff7],[0,0,0,280,85,0x7effff61],[0,0,560,0x7efffe49,0x7efffd4f,80],[0,0,700,0x7efff89f,0x7efffc69,805],[0,560,0x7efff2c5,1260,2600,0x7efffee9],[0,280,0x7efff29b,5880,2660,0x7efff7e1],[80,0x7efff809,8540,0x7efff3f9,0x7effec51,560],[10,0x7efffd68,6360,0x7effd6b7,0x7efff36d,3150],[0x7effffa7,2430,0x7effd559,5600,5460,0x7efffd45],[1,360,0x7effec15,10920,1190,0x7efff4a1],[0x7efffff7,0x7efffcb9,6720,0x7effe909,0x7efff36d,560],[45,1260,0x7effe9db,840,1610],[0x7effff89,0x7efffb15,2940,840,0x7efffee9],[210,840,0x7efffcf5,0x7efffe21],[0x7effff05,0x7efffe99,0,80],[210,90,55],[0x7effff89,0x7efffff7,0x7efffff7],[45,0],[0x7efffff7,0],[1],[0]],
    [[0,0,0,0,110,130],[0,0,0,880,850,0x7effff8a],[0,0,0,3080,1250,0x7efff881],[0,0,6160,0x7effefe9,0x7effdeaa,960],[0,0,7700,0x7effb2e5,0x7effcd39,9800],[0,6160,0x7eff725d,8610,32920,0x7efff2be],[0,3080,0x7eff6f15,58632,39760,0x7eff9b61],[880,0x7effa949,89530,0x7effb6b9,0x7efefe6d,6880],[110,0x7effe39b,68040,0x7efe6d81,0x7eff26e5,39900],[0x7efffc23,26325,0x7efe4509,39550,75180,0x7effddd3],[10,3960,0x7eff2b31,106680,35140,0x7eff6b41],[0x7effff9e,0x7effdbe9,70140,0x7eff44f9,0x7eff41f7,7168],[440,13860,0x7eff2285,0x7effef99,22120],[0x7efffb7e,0x7effc9dd,26670,15960,0x7efff183],[1980,9240,0x7effed41,0x7effe3e1],[0x7efff6fb,0x7efff089,0x7efff9ad,1120],[1848,990,1010],[0x7efffc23,0x7effff93,0x7effff66],[330,0],[0x7effffca,0],[0],[1]]]
theorem rank_41_11 : (CJ0.blockMatrix source 41 ((11 : ℤ)-21)).rank ≤ 98 :=
  Fast.cell (z := b41_11) (Fast.bands [(0,22,20),(1,23,18),(2,24,16),(3,25,14),(4,26,12),(5,27,10),(6,28,8),(7,29,6),(8,30,4),(9,31,2)]) (by decide +kernel) (by decide +kernel)

private def b44_10 : CJ1.Block where
  bank := .leftLow
  cap := 86
  free := [(7,2),(7,3),(8,0),(8,1)]
  vectors := [
    [[0x55bd2c65,0x77cb9a98,0x285d6fe4,0x4cd917c,0x40fb7978,0x34f0bee2,0x1d34182b,0x522f2986,0x7a456d8d,0x278b5c6b,0x4353b87f,0x3b9159ce,0xcb238d7,0x6da1cbf2,0x42f6bee4,0x56e5eebd,0x60d5f4d8,0x7ef9399c],[0x166ef15d,0x23acc618,0x58ffb6aa,0x3c09f257,0x7d29afe5,0x689e5791,0x75b4f507,0x2355bec9,0x7e7ecf4d,0x7d32d891,0x68667c93,0x55c6a2a4,0x578bdc8d,0x26cf4941,0x4cb9708a,0x3bd757e3],[0xef97354,0x101ac478,0x748bd103,0x364b4239,0x2308b712,0x1b135f2,0x75304d71,0x7eebbac1,0x7ead7ad9,0x5385f05e,0x7b6e8c81,0x7522f3c1,0x66b88289,0x4993c9d9],[0x3f5cb24a,0x148b5ebc,0x20d02e62,0x75ba36f9,0x47b7298e,0x1d9e0b7d,0x2a52ad83,0x2b7e5c44,0x50d653d7,0x68b896e,0x465b7d40,0xc108ba7],[0x2898ae3e,0x8745de8,0x52afac34,0x6331c37e,0x450868aa,0x1966208d,0x1964d5dd,0x3edda2a4,0x56f6d218,0x23da0afe],[0x49ad6731,0x424b8b01,0x542195da,0x17c7b5d1,0x7efffb09,0x4c330e87,0x54a9ced6,0x3a0a5710],[0x239add22,0x1a86af0a,0x3f31a4ae,0x2a55552b,0x7efffe11,0x6e1100b3],[0x35611012,0x669b9309,1,0],[0,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x3c4d2128,0x5c6ae635,0x5cabffe,0x30747859,0x39eb85d2,0x53a4471,0x26c492b1,0x7573ec7d,0x394a65d7,0x46f260,0xe1164c,0x68147f34,0x641d4b0,0xe2f6a58,0xada22ed,0x3591b088,0x599c74c8,0x8e05037],[0x70c29b07,0x735c08e4,0x2e31d555,0x222fd784,0x43628b77,0x3726ca3f,0x485c313d,0x11cfeafa,848232,0x2e07ec,0x6629dbc4,0x345e3462,0x3e54d30,0x8adc71c,0x1163e2a8,0x1f68fab0],[0x1513c32d,0x66b3af22,0x336becab,0x6c361b1e,0x5bf72f1a,0x21898f93,0x69633f96,134640,545292,0x1d5dfc,0x65f4cbf8,0xfaf0e0,0x2670c24,0x543e6d0],[0x2740999c,0x69dece17,0x2e78188f,0x7d4f0f01,0x546e0e1c,0x41f8ee19,17952,0x2b8c431c,0x7b644f6a,0x75438c2,0x48cb1d94,0x12bfb0bb],[0x28491e53,0x314a5aea,0x507b8141,0x620937f7,0x1a8ef444,0x32ccd43a,0x6599c39c,0x366e7f05,0x707f889d,0x24546d66],[0x182d5152,0x6f634ac4,0x63c164b1,0x722504e8,144,1032,0x6599b134,0x6cdbe15a],[0x75ed329a,0x599692cb,0x4abb1680,6,62,0x65999b83],[0x4388c229,0x23512827,0,1],[0,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x2449250b,4356,77646,909756,0x784bff,0x3365e3e,0x120a0c3e,0xcf67a56,0x5f3c5772,0x66b9c397,0x7209281a,0x5272f84a,0x52c31d13,0x7285e6dd,0x336acf76,0x382405fc,0x4ce8eacc,0xcb54a4b],[90,3180,55476,637380,0x52cd1c,0x22d14bc,0xc0b7672,0x385bf1e0,0x6442c117,0x26d2d92a,0x4e73872d,0x25374e3a,0x338bb67a,0x67986406,0x26c842a2,0x793d42e8],[64,2211,37815,427100,0x36af1a,0x16b72ba,0x7c724c8,0x2412b910,0x114ae43f,0x7b6c3561,0x1fd59938,0x47ed2e3f,0xc56bdb6,0x6bdaa23d],[0x244924bd,0x122497e5,0x5ab739c1,0x1228adef,0x246b4b08,0xe193f0,0x4cf4be0,0x2867b6f7,0x2280138f,0x26306e2f,0xaa7838c,0x4d785183],[0x6cdb6dd1,0x48924c6e,0x48927fc2,0x6cddcb2c,0x13a778,0x825f60,0x2cd0c90,0x43841505,0x59108d22,0x5eeb7e15],[0x5ab6db7b,0x366db879,0x5ab6f635,76576,647280,0x432960,0x17c9520,0x74063d2a],[0x6cdb6dbc,0x6cdb6e43,2331,26970,242730,0x1b5de1],[0x24492493,6,0,0],[1,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[0x23fe670f,0x302c22c4,0x7768b74c,0x348ccbc5,0x8be59de,0x7703b1d9,0x75aa4896,0x71e38b65,0x32355336,0x2d2bc3fa,0x35ba84df,0x4c586c62,0x46910811,0x48a8eef4,0x3aa707b5,0x17e0209e,0x42105509,0x77fb6689],[0x54152fa9,0x73e7dea5,0x118462e9,0x15e533d9,0x5bf47f8e,0x435f0be3,0x29a78c39,0x14178f09,0x77bf8095,0x65887f79,0x40f8fc63,0x3d98418f,0x61853bf9,0x4eaa1d22,0x22739c57,0x203fc222],[0x15e58468,0x4611a33,0x2308cf05,0x449bbdab,0x5bf563d6,0x64ad9444,0x42e5e21a,0x7dd6ca61,0x7a60782d,0x1a3dea6b,0x4d9303ad,0x771b8a4a,0x344ab3d7,0x2c5f6512],[0x676f654e,0x2c6b30ff,0x6ba5c739,0x39d91b43,0x2dea71ca,0x1bb4edf5,0x54829126,0x7705b30b,0x3d3e36ed,0x49866435,0x2a307eec,0x3ec04668],[0x4ab2d259,0x3ad97e96,0x11646000,0x6a3aafc8,0x7351bbb9,0x6595477c,0x65820c4c,0x2d891c6e,0x6ec781bd,0x1e530032],[0x3eafcb8a,0x7c7f5e87,0x1ba6f6bc,0x21931601,0x7effa9c9,0x32ca8b0a,0x2a48b543,0x206c08a3],[0x436650e1,0x40302c5f,0x792931b0,0x54aaa6e0,0x7effded3,0x10edff67],[0x58d6625e,0x51bf43ae,0,0],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_44_10 : (CJ0.blockMatrix source 44 ((10 : ℤ)-21)).rank ≤ 86 :=
  Fast.cell (z := b44_10) (Fast.bands [(23,23,1),(24,24,2),(25,25,3),(26,26,4),(27,27,5),(28,28,6),(29,29,7),(30,30,8),(31,31,9),(32,32,10),(33,33,11),(34,35,10),(35,37,8),(36,39,6),(37,41,4),(38,43,2)]) (by decide +kernel) (by decide +kernel)

private def b49_7 : CJ1.Block where
  bank := .leftLow
  cap := 70
  free := [(7,0),(7,1)]
  vectors := [
    [[0x7effffdf,0x7efffa90,0x7eff9275,0x7efa5b65,0x7ec92f1d,0x7d5dda73,0x74d0d769,0x49aab8e5,0xece1410,0x53e6195b,0x6f36ecbe,0x65da7c1d,0x70b6a55f,0xee6644c,0x34884324,0x4bec39fa],[0x7effffe4,0x7efffb75,0x7effa63d,0x7efb7621,0x7ed4b1f3,0x7dbb5c39,0x773a538d,0x56fec961,0x4dbaa751,0x57a92d2a,0x162d1d42,0x6a5d2b5,0x7813eaa5,0x340085ec],[0x7effffe9,0x7efffc50,0x7effb867,0x7efc703a,0x7ede8831,0x7e08c14a,0x792a7d5f,0x6169c4f0,0x7da6c616,0x192a3e80,0x3b7a6505,0x41ac5b49],[0x7effffee,0x7efffd21,0x7effc902,0x7efd4bfd,0x7ee6dde8,0x7e482ef1,0x7ab4edfc,0x6977b055,0x22c22015,0x26fceb83],[0x7efffff3,0x7efffde8,0x7effd81d,0x7efe0ba3,0x7eeddc37,0x7e7b9458,0x7beab795,0x6f9e7431],[0x7efffff8,0x7efffea5,0x7effe5c7,0x7efeb151,0x7ef3a964,0x7ea4ae15],[0x7efffffd,0x7effff58,0x7efff20f,0x7eff3f18],[1,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
    [[1,41,0x48924c5f,0x6cdb9846,0x5ab878dd,0x5ac32cd1,0x6d2834b0,0x4a242418,0x708ff69,0x93f79ee,0x2f4f520,0x6659e08a,0x4d4c14ae,0x739a9648,0x5fc6d2d2,0x6bcfd0b2],[0x48924926,0x244924b5,680,0x48926b88,83980,0x2452beb8,0x48cd1804,0x6e09d606,0x3ba0aa67,0x13dd0c03,0x30727169,0x46813fef,0x4413e2b1,0x48105b78],[0x1224924a,0x366db6f8,546,0x6cdb88df,0x5ab7da6d,0x4899a301,0x2c585a,0x5b976446,0x15f0e08a,0xe42cd8c,0x53338a16,0x51e3a06f],[0x5ab6db6f,0x366db6f2,0x2449263a,0x1224a714,0x48930a28,360639,0x20d30c,0x49367c63,0x14e21367,0x408facf9],[0x24492493,0x244924a3,0x48924a5d,0x48925862,36075,262293,0x17c127,0x36e3b7b5],[0x6cdb6db8,11,0x489249f8,2670,24990,183447],[0x366db6dc,0x4892492b,120,1615],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_49_7 : (CJ0.blockMatrix source 49 ((7 : ℤ)-21)).rank ≤ 70 :=
  Fast.cell (z := b49_7) (Fast.bands [(28,28,1),(29,29,2),(30,30,3),(31,31,4),(32,32,5),(33,33,6),(34,34,7),(35,35,8),(36,37,8),(37,39,8),(38,41,8),(39,43,7),(40,45,5),(41,47,3),(42,49,1)]) (by decide +kernel) (by decide +kernel)

private def b56_3 : CJ1.Block where
  bank := .rightLow
  cap := 40
  free := [(5,1),(7,1)]
  vectors := [
    [[0,0x7f000000],[0x7effffff,1],[0x7f000000,4],[3,0x7effffff],[0,0x7efffffe],[0,1],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0],[0]],
    [[0,0x7efffffe],[0x7efffffb,2],[0x7efffffe,9],[6,0x7efffffe],[0x7f000000,0x7efffffe],[3,0],[0,0x7efffffe],[0,1],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0],[0]]]
theorem rank_56_3 : (CJ0.blockMatrix source 56 ((3 : ℤ)-21)).rank ≤ 40 :=
  Fast.cell (z := b56_3) (Fast.bands [(0,44,13),(1,45,11),(2,46,9),(3,47,7),(4,48,5),(5,49,3),(6,50,1)]) (by decide +kernel) (by decide +kernel)

private def b60_1 : CJ1.Block where
  bank := .rightLow
  cap := 20
  free := [(1,0),(3,0)]
  vectors := [
    [[0x7f000000],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]],
    [[0x7f000000],[0],[0x7f000000],[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]]]
theorem rank_60_1 : (CJ0.blockMatrix source 60 ((1 : ℤ)-21)).rank ≤ 20 :=
  Fast.cell (z := b60_1) (Fast.bands [(0,50,11),(1,51,9),(2,52,7),(3,53,5),(4,54,3),(5,55,1)]) (by decide +kernel) (by decide +kernel)

private def b63_0 : CJ1.Block where
  bank := .rightLow
  cap := 9
  free := [(1,0),(3,0)]
  vectors := [
    [[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]],
    [[],[0],[],[1],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0],[],[0]]]
theorem rank_63_0 : (CJ0.blockMatrix source 63 ((0 : ℤ)-21)).rank ≤ 9 :=
  Fast.cell (z := b63_0) (Fast.bands [(0,55,9),(1,56,7),(2,57,5),(3,58,3),(4,59,1)]) (by decide +kernel) (by decide +kernel)

private def b66_1 : CJ1.Block where
  bank := .leftLow
  cap := 8
  free := [(2,0)]
  vectors := [
    [[0,0,0,0,1035],[0,0,0x7effffd4],[1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]
theorem rank_66_1 : (CJ0.blockMatrix source 66 ((1 : ℤ)-21)).rank ≤ 8 :=
  Fast.cell (z := b66_1) (Fast.bands [(45,45,1),(46,46,2),(47,48,2),(48,50,2),(49,52,2),(50,54,2),(51,56,2),(52,58,2),(53,60,2),(54,62,2),(55,64,2),(56,66,1)]) (by decide +kernel) (by decide +kernel)

end CurveList82190
