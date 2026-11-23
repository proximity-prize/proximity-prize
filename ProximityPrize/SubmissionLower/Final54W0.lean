import ProximityPrize.SubmissionLower.FadicVarCert

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace FadicGate.Final54W0

open FadicGate

private def unpackBox (w : ℕ) : Entry :=
  cond (Nat.beq w 0) none
    (let n := Nat.sub w 1
     some (Nat.mod n 4096, Nat.mod (Nat.div n 4096) 2048, Nat.div n 8388608))

private def unpackBoxes : ℕ → ℕ → List Entry
  | 0, _ => []
  | n+1, w => unpackBox (Nat.mod w 8589934592) :: unpackBoxes n (Nat.div w 8589934592)

def lvl1 : List Entry := unpackBoxes 1 0x3018045
def lvl2 : List Entry := unpackBoxes 2 0x401805832080
def lvl3 : List Entry := unpackBoxes 3 0x8030080440c8090490c8
def lvl4 : List Entry := unpackBoxes 4 0x10060020140481008014e0c863100
def lvl5 : List Entry := unpackBoxes 5 0x200c0040280901a0d4248170b81ec1007b143
def lvl6 : List Entry := unpackBoxes 6 0x4018008050120080400c8241203001e0ec27e13093187
def lvl7 : List Entry := unpackBoxes 7 0x80300100a024010080190381e84c0361b84682611e2f6168ab1ca
def lvl8 : List Entry := unpackBoxes 8 0x1006002014048020100320100b02105c2d8770442045582c14e3a01a8c4206
def lvl9 : List Entry := unpackBoxes 9 0x200c00402809004020064020160420783e0a906c3509305628468c341863f81d8da255
def lvl10 : List Entry := unpackBoxes 10 0x4018008050120080400c80402c0840301a05a0d86a12609c4b0c50622e079c3b1b4488210f428d
def lvl11 : List Entry := unpackBoxes 11 0x80300100a02401008019008058108060340b40f08215e0f87e14c0b4560e40743548b8421e851a2510d2c9
def lvl12 : List Entry := unpackBoxes 12 0x1006002014048020100320100b02100c068168080440b01e0ea25e130911770d4618ff0823b09d84a21a5922892530c
def lvl13 : List Entry := unpackBoxes 13 0x200c00402809004020064020160420180d02d010088160221102d0261222ee190ba1ef0f471137090418afc5124a6182c93e348
def lvl14 : List Entry := unpackBoxes 14 0x4018008050120080400c80402c0840301a05a0201102c0140981c03c1dc4f02a1443621d8d923c1187e94f0a047cbec5927c6902f95638c
def lvl15 : List Entry := unpackBoxes 15 0x80300100a02401008019008058108060340b404022058028130380442385e0542886c4301683c6208ed2741308996e0ae4e4d105f2ac7183316e3cf
def lvl16 : List Entry := unpackBoxes 16 0x1006002014048020100320100b02100c068168080440b0050260700281604007c3c8a40602d078c3c1bc492231022b9154991948be548e00662dc79e3718740b
def lvl17 : List Entry := unpackBoxes 17 0x200c00402809004020064020160420180d02d0100881600a04c0e00502c080090490c80b8568e406a31483c4620457229127314170a49b88cc5b0f246e30e8163a19d45a
def lvl18 : List Entry := unpackBoxes 18 0x4018008050120080400c80402c0840301a05a0201102c0140981c00a0581000603208c1087d1480d4629078743608e44d2305ca2c13d36318cb09da0d860901c7433a8b43e1b6496
def lvl19 : List Entry := unpackBoxes 19 0x80300100a02401008019008058108060340b404022058028130380140b02000c0641181309c188170b01ce0e86c11c88c404ac45425a64e3015938f1a8bea018e46691707c36c92c409cd4e1
def lvl20 : List Entry := unpackBoxes 20 0x1006002014048020100320100b02100c068168080440b005026070028160400180c82300e070134210fe2a61d0d82390fc7413b8a64b0c745b28a6b23396e3d11c8cb21f8f66d52308139a9c2451e8511
def lvl21 : List Entry := unpackBoxes 21 0x200c00402809004020064020160420180d02d0100881600a04c0e00502c0800301904601c0e02682813c34c301663a61f8e82771147e14f0b6514d64632d277e3899042e1e4d72389027353848a3d0a22489ff559
def lvl22 : List Entry := unpackBoxes 22 0x4018008050120080400c80402c0840301a05a0201102c0140981c00a0581000603208c0381c04d01c0f02c04220856c3e1ca4be228fc29e148939850c2564e446d30881e3b1a5473204e4a621147a1444913feab24ba18598
def lvl23 : List Entry := unpackBoxes 23 0x80300100a02401008019008058108060340b404022058028130380140b02000c0641180703809a0381e0580502906d8622d477c451f853c2590e2d0174a79be0ce5bcf3c743388a43f9c04a3224f12801227fd56497430b30502305d8
def lvl24 : List Entry := unpackBoxes 24 0x1006002014048020100320100b02100c068168080440b005026070028160400180c82300e0701340703c0b00482205808c430ad87e39c9ac4b21c5a02811f2fc19cb79e78da60d01c7b368908419d54fa23cfc2a792e861660a0460bb053a4a610
def lvl25 : List Entry := unpackBoxes 25 0x200c00402809004020064020160420180d02d0100881600a04c0e00502c0800301904601c0e02680e078160090440b00b0550e00c45c0f3896438b405023e5f82d94936c1b4c1a038f06a51bc81394984479f65382610aac29408c1760a7494c2057262653
def lvl26 : List Entry := unpackBoxes 26 0x4018008050120080400c80402c0840301a05a0201102c0140981c00a0581000603208c0381c04d01c0f02c0120881600904a0c011886173104759358a047cbf05526464c341743d81c8cc226102729308893d2a6449a0c57927915aea14e929840ae4c4ca65aa7969b
def lvl27 : List Entry := unpackBoxes 27 0x80300100a02401008019008058108060340b404022058028130380140b02000c0641180703809a0381e0580241102c012094180160b01d0190ba1f31388d9808aa4c8c98592866c03919844c1e8d7a4111077d4109440eac04e2245b929522b0615c98994cb54f2d365da8f6ea
def lvl28 : List Entry := unpackBoxes 28 0x1006002014048020100320100b02100c068168080440b005026070028160400180c82300e0701340703c0b0048220580241283001409c1b0241142e8208ed276154991930b250cd80652d87b03d1af4821fce225b11e7dd51c99436b545223d5f52b12e33296a9e5a6cbb51edd461aab716
def lvl29 : List Entry := unpackBoxes 29 0x200c00402809004020064020160420180d02d0100881600a04c0e00502c0800301904601c0e02680e078160090440b0048250600281383602e1683d03317c3e42791f302164a19b00bc54ce787232e8883f9c44b6224f429512c83d5e4a0466bda55a596442d13c348976a3dba8c3556e2c63ac076d
def lvl30 : List Entry := unpackBoxes 30 0x4018008050120080400c80402c0840301a05a0201102c0140981c00a0581000603208c0381c04d01c0f02c0120881600904a0c00502706c02c158368482345e8411e04fc2c943360178a99cf0ca5a4ee47e38095e439db4ec25907abc9388956dca949cc3a5827068f2e546376186aadc58c7580eda68ada7a1
def lvl31 : List Entry := unpackBoxes 31 0x100a02401008019008058108060340b404022058028130380140b02000c0641180703809a0381e0580241102c0120941800a04e0d80582b06d0602f0798663047e8512466042f15339e194b49dc8e26410bc873b69d8469ef52427112adb94c91d894b14dacf85d28a6c330d55b8b18eb01db4d15b4f426caf37dd
def lvl32 : List Entry := unpackBoxes 31 0x20100320100b02100c068168080440b005026070028160400180c82300e0701340703c0b0048220580241283001409c1b00b0560da0582e073098480bf8843c8a285f2aa71c329693b91a8bd1f28fa6f124c8d3dea4849a055622891db0315e99196cb850ad5c60aa170b31d603b69a2b69e84d95e6fba6eb0b824
def lvl33 : List Entry := unpackBoxes 31 0x20160420180d02d0100881600a04c0e00502c0800301904601c0e02680e078160090440b004825060028138360160ac1b40b05c0e60c0610fb0d4620ff8a2498c28652d27723517a3e51bcc520f91279542c9340aac44f22b5ca2a529b1c1689eda98be536dfa64abf74e3456d3d09b2bcdf74dd61704873b25858
def lvl34 : List Entry := unpackBoxes 31 0x301a0500201102c0140981c00a0581000603208c0381c04d01c0f02c0120881600904a0c00502706c02c158368160b81cc0b0601001309318710c7b1458c055ce686a2f47ca3798a41f1f0daa4592681558897436b465324c6402c535337178a49b70c6568e7266ad47a536579bee9bac2e090e764b0b07733c8a0
def lvl35 : List Entry := unpackBoxes 31 0x4022050028130380140b02000c0641180703809a0381e0580241102c0120941800a04e0d80582b06d02c170398160c0200190c620e1b0c620b144931910d45e8f946f31483e3a19d44d21cefa7f92e86d68c9d45ebb658a6a66e2dd40356188aadc60cb590f286aaeb7db37585c121cec96160ee6791407a3528ef
def lvl36 : List Entry := unpackBoxes 31 0x5026050028160400180c82300e0701340703c0b0048220580241283001409c1b00b0560da0582e07302c180400180c82302712a326220f8297184ad9cc8de62907c7433a89a3c9ad48b251052b593a8bd76ca648ac2a5ba806ac30151b8b192b09d8cd35d0fba6f30680b39d92c2c1dccf2280f46a51de7eb6d91f
def lvl37 : List Entry := unpackBoxes 31 0x502c0500301904601c0e02680e078160090440b004825060028138360160ac1b40b05c0e6058300800301904603419c420361924262992c3151bcc520f8e86751347935a916421da4ef27517aed94c915854b14d6cd85ea966fb325613b19a6b89ee8db6050067332185e3b99e4501e8d4a3bcfd6db23e80b82976
def lvl38 : List Entry := unpackBoxes 31 0x60320500381c04d01c0f02c0120881600904a0c00502706c02c158368160b81cc0b0601000603208c0381b04604e26066c431f25523115d3a51d0cea268f26b522c7f38296449a0355629922b0a956969924bc522da8622ae72d3456cbcc9b6bedfd8e46350867733a89a3d1a94779fadb647d017052ec8539d9a6
def lvl39 : List Entry := unpackBoxes 31 0x70380500381e0580241102c0120941800a04e0d80582b06d02c170398160c02000c0641180703608c06c3488a06c32c8785325865a389914251e4d6a458fe7052c8843a49bc4f22d5c62ad2d3249669c59fcc455ce5a65ac675f36179be89bec4e0f4e865f1347934f8f13f5b6c8fa02e0a5d90a73b34c893b69e2
def lvl40 : List Entry := unpackBoxes 31 0x703c050048220580241283001409c1b00b0560da0582e07302c180400180c82300e06c118070390940a44d8cf08c3f8a88622c075a3c9ad48b1fce0a59108749378913faa8c542536512cd38b3f972a1daf4cb58cebe692dc7a137d844099d4cb21d4f269319c7e36c915405c14bb214e766991276d3c48bbcda2d
def lvl41 : List Entry := unpackBoxes 31 0x904405004825060028138360160ac1b40b05c0e6058300800301904601c0d82300e0721280d86b11f0e06790f0a84c0cb87132885a3f9c14b2210e926f1127954209d44cb7c59a7167f2e543b5e986aa5cacd25b8f426dafe80b39590c291e0d122e4f86cd23280b82976429cecd3224eda7891779b45a90be7a61
def lvl42 : List Entry := unpackBoxes 31 0x904a0500502706c02c158368160b81cc0b0601000603208c0381b04601c0e42500e07613e1489e1a6118809550c6590eb87f382964421d24de224f2a8411e7dd4e8a94a4c4c5ca876bd2fd4db7a99eb4ddf0d85e2fe072b218523b99cc491e8d6a3e90270129a8539d9a6449db4f122ef368b5217cf4c2923faac4
def lvl43 : List Entry := unpackBoxes 31 0xa04e0500582b06d02c170398160c02000c0641180703608c0381c84a01c0ec27c1d0de23e1c0d22261589a1970e46550f8843a49bc449e550823cfba9d1368816c8b54f6d3c5fa9b6f530d573a31b0bc5fc0df613044773398923d9ac4789fcdea54508731322893b69e245de6d16a42f9e985247f558897417ae8
def lvl44 : List Entry := unpackBoxes 31 0xb0560500582e07302c180400180c82300e06c118070390940381d84f8200fc27c2b142356239032b6190b31dd1027252f0893caa10479f753a24d042ba15092d878bf536dea61aae746325613bf1bec26088e66430a878b4a8ef3f9ba497210e526150f75b3c88bbcda2d485f3d30a48feab112e82f5d09a42cb3c
def lvl45 : List Entry := unpackBoxes 31 0xb05c050058300800301904601c0d82300e0721280703b09f0401f84f83a1c849c391a646e2b1373361c8cc2221127954208f3eea7449a085742610c2d91649c5a70c355ce8c64ac277e35d76be39ccc86150ea66d1567d36890f415c5cbb21ceaa70d1779342090be7a61491fd56225d05eba1348596789dc44b7f
def lvl46 : List Entry := unpackBoxes 31 0xb0600500603208c0381b04601c0e42500e07613e0803f09f040208560562906cc4820e56e3296a3b9208e5a6411e7dd4e893410ae84c2185b229922b0297ea71c10c9584efc68adc7a438588c1d9d4cda2acf66b320080b7d95142dd0ce2a26efa8791e7c14d2923faac44ba0bd742690b2cf13b8896fea1c60bab
def lvl47 : List Entry := unpackBoxes 31 0xc0640500703608c0381c84a01c0ec27c1007e13e080410ac0783a09987635c8dc5727068a3919845c23cfba9d1268215d098430b644f22d5c72c93733c992b09df8d15b8f486caf37da3b59b44b1e4d36385016fb2a282b929a8449dccfba3af6e909267f952a97417ae84d21659e277112dfd438c1756a3c75c02
def lvl48 : List Entry := unpackBoxes 31 0xe06c050070390940381d84f8200fc27c10082158080440b40b0530df892424b04662d878a409cc4dc24d042ba1308616c89e45ab8e5223f5f52f94bb789a2b71e90d95e6fb46fb078123c9a6c709f4d9e41d0572535087bac9dc469e9519a48fcaa292a8235d89a42cb3c4ee225bfa87182ead478eb804a8c8fc36
def lvl49 : List Entry := unpackBoxes 31 0xe0720500703b09f0401f84f8201042b0100881680f8781340ec6c9210b04f4d047433c8a249a054f92610c2c113c8b571ca447ebea5826866d32961bac9b2bcdf68df60f02473b2d87e3e9b3c83a02df25250f7593b88cbcfa23481f454125b046b5d348576409dc44b7f50e305d5a8f1d70095191f86cacca8c72
def lvl50 : List Entry := unpackBoxes 31 0xe0760500803f09f040208560201102d01108c180168aa1be1208516a8ce5b8f44843a88e04e2284f927d17ac11488fd7d4a94a4c465ea936d936179bd31bcc22038e563b0a07a3518dd405be4a4a0ae466811678941c903e8a824a604d6aa650a2c893c8896b8a1c60bab51e3ae012a323f0d9599518e4aecc0cb9
def lvl51 : List Entry := unpackBoxes 31 0x1007e050080410ac0402205a022118300200f427c1d8dc24a15c9f1aa8ec694f9c9f4328e0522414f9299242c115294982cae4c4cc2652c171d38d8bbd31cac9a080ec6670f88137f916421cb4c0a22ed27d51e7bb49494c03ab24ca12582a7710ed49438c1756a3c75c0254647e1b2b32a31c95d981972b3cdaced
def lvl52 : List Entry := unpackBoxes 31 0x10082050080440b1044230600241282fc2e1583942590f2ce19cb99af142790f9cb34328e06224e4f92b930ac11609a182cbc522d286dafc71d3b59bbd31ded060b4f369d13c86ba592a449da4c7a38f7a899247ed4f09841bae44de1c5b0285162e51478eb804a8c8fc36566546392bb3032e5679b59dab5cecd54
def lvl53 : List Entry := unpackBoxes 31 0x10088050088460b10482505f83e1ec5483d1c04942c9442d523cd79af142790f9cb34328e06224e4f92d93e2c116ea0982ccc596d2885b2271d3d5aabd31f0d820bd0170516e8bbc6928465e94d0a530168852e82d5189c43ab005022b5c028d1c2f6d5191f86cacca8c725766065cacf36b3b56b9d9aa8ba50ad74
def lvl54 : List Entry := unpackBoxes 31 0x120900500904a0b104c2606585c2bc70c4b22a4983f17a2d523cd79af142790f9cb34328e06224e4f935941ac117ea6d82cf95dad2885b2271d475abbd3206e0a0b91377115e903e7927485fa4d6a670a289539871528a145ab1452a3b5c1aa1236ffd5a95b8acaecc0cb959e6d676ad73b355174a15ae8bed22db4
def lvl55 : List Entry := unpackBoxes 31 0x130960500984c0b10803f89d08039470c6c28a4983f17a2d523cd79af142790f9cb34328e06224e4f935941ac11d0ae182cf95dad2885b2271d475abbd324ae320bd407831709e3f69414b60acd427b12e8a5468cd538a5c7bb245564c5c5ab72db00d639978ecb34decd95ba78e9aae942b5d17da45b68c0d37e0b
def lvl56 : List Entry := unpackBoxes 31 0x1409e0500984f0b10c85b09d0b444070c6c28a4983f17a2d523cd79af142790f9cb34328e06224e4f935941ac11d0ae182cf95dad2885b2271d475abbd325ce320bd40783170a93f694158e15ce529318294d5392553cabca1b155765d5cbad13630216b9db904b7cfccf95de87eaaafb48b6d181a6fc16c5552e3b
def lvl57 : List Entry := unpackBoxes 31 0x140a8050118870b11246d89d0b444070c6c28a4983f17a2d523cd79af142790f9cb34328e06224e4f935941ac11d0ae182cf95dad2885b2271d475abbd325ce320bd40783170a93f694158e15ce52eb18294d8792b5b8b24cab275aa735ccae53ef03178a1f90ebe51ecfe602986b2b0d5037518aaabc56c956be77
def lvl58 : List Entry := unpackBoxes 31 0x150b00501b8a60b11246d89d0b444070c6c28a4983f17a2d523cd79af142790f9cb34328e06224e4f935941ac11d0ae182cf95dad2885b2271d475abbd325ce320bd40783170a93f694158e15ce52eb18294d8792b5b8cc4cab655d67fde8af747f03182a65916c3541d0262aa86bcb1f58779193ae7c96cbd82ec2
def lvl59 : List Entry := unpackBoxes 31 0x250e20501b8a60b11246d89d0b444070c6c28a4983f17a2d523cd79af142790f9cb34328e06224e4f935941ac11d0ae182cf95dad2885b2271d475abbd325ce320bd40783170a93f694158e15ce52eb18294d8792b5b8cc4cab656aa7fdf730f4d31618baad916c7d65d0264eba6bcb3160b7d19cb23cd6d05a0ee2
def lvl60 : List Entry := unpackBoxes 31 0x250e20501b8a60b11246d89d0b444070c6c28a4983f17a2d523cd79af142790f9cb34328e06224e4f935941ac11d0ae182cf95dad2885b2271d475abbd325ce320bd40783170a93f694158e15ce52eb18294d8792b5b8cc4cab656aa7fdf73794d31dd96ad39c6cd586d0f66ecb6c2b3f6977f1a4b61d0ed45c2eee
def lvl61 : List Entry := unpackBoxes 31 0x250e20501b8a60b11246d89d0b444070c6c28a4983f17a2d523cd79af142790f9cb34328e06224e4f935941ac11d0ae182cf95dad2885b2271d475abbd325ce320bd40783170a93f694158e15ce52eb18294d8792b5b8cc4cab656aa7fdf73794d31ddcdad3a00d359ed4b6aadcec135d7237e5b2bafce0db5e6ee7
def lvl62 : List Entry := unpackBoxes 31 0x250e20501b8a60b11246d89d0b444070c6c28a4983f17a2d523cd79af142790f9cb34328e06224e4f935941ac11d0ae182cf95dad2885b2271d475abbd325ce320bd40783170a93f694158e15ce52eb18294d8792b5b8cc4cab656aa7fdf73794d31ddcdad3a00efd9ed896d2e9edb36f7b37e5bcbf5ce8e0609eeb
def lvl63 : List Entry := unpackBoxes 31 0x250e20501b8a60b11246d89d0b444070c6c28a4983f17a2d523cd79af142790f9cb34328e06224e4f935941ac11d0ae182cf95dad2885b2271d475abbd325ce320bd40783170a93f694158e15ce52eb18294d8792b5b8cc4cab656aa7fdf73794d31ddcdad3a00efd9ed897c6e9f0937f823895c3c3bcf8e462bef7
def lvl64 : List Entry := unpackBoxes 31 0x250e20501b8a60b11246d89d0b444070c6c28a4983f17a2d523cd79af142790f9cb34328e06224e4f935941ac11d0ae182cf95dad2885b2271d475abbd325ce320bd40783170a93f694158e15ce52eb18294d8792b5b8cc4cab656aa7fdf73794d31ddcdad3a00efd9ed897c6e9f093ef823a6dd2c7bd12ea64eef8
def lvl65 : List Entry := unpackBoxes 0 0x0
def lvl66 : List Entry := unpackBoxes 0 0x0

def boxes : ℕ → List Entry
  | 1 => lvl1
  | 2 => lvl2
  | 3 => lvl3
  | 4 => lvl4
  | 5 => lvl5
  | 6 => lvl6
  | 7 => lvl7
  | 8 => lvl8
  | 9 => lvl9
  | 10 => lvl10
  | 11 => lvl11
  | 12 => lvl12
  | 13 => lvl13
  | 14 => lvl14
  | 15 => lvl15
  | 16 => lvl16
  | 17 => lvl17
  | 18 => lvl18
  | 19 => lvl19
  | 20 => lvl20
  | 21 => lvl21
  | 22 => lvl22
  | 23 => lvl23
  | 24 => lvl24
  | 25 => lvl25
  | 26 => lvl26
  | 27 => lvl27
  | 28 => lvl28
  | 29 => lvl29
  | 30 => lvl30
  | 31 => lvl31
  | 32 => lvl32
  | 33 => lvl33
  | 34 => lvl34
  | 35 => lvl35
  | 36 => lvl36
  | 37 => lvl37
  | 38 => lvl38
  | 39 => lvl39
  | 40 => lvl40
  | 41 => lvl41
  | 42 => lvl42
  | 43 => lvl43
  | 44 => lvl44
  | 45 => lvl45
  | 46 => lvl46
  | 47 => lvl47
  | 48 => lvl48
  | 49 => lvl49
  | 50 => lvl50
  | 51 => lvl51
  | 52 => lvl52
  | 53 => lvl53
  | 54 => lvl54
  | 55 => lvl55
  | 56 => lvl56
  | 57 => lvl57
  | 58 => lvl58
  | 59 => lvl59
  | 60 => lvl60
  | 61 => lvl61
  | 62 => lvl62
  | 63 => lvl63
  | 64 => lvl64
  | 65 => lvl65
  | 66 => lvl66
  | _ => []

def plainT : ℕ → ℕ × ℕ × ℕ
  | 65 => (3926,1640,446)
  | 66 => (4012,1629,543)
  | _ => (0,0,0)

def terminal:ℕ:=67

private abbrev lossAt:=varCertLoss ((((406807694511:ℕ)):ℤ)) 48 106 137 48 53 4 2756 4437 67 plainT boxes
private abbrev verifyLevel:=varCertLoss_row 406807694511 48 106 137 48 53 4 2756 4437 67 plainT boxes

theorem row0 : lossAt 0 = ((406807668927 : ℕ) : ℤ) :=
  verifyLevel 0 0 0 0 lvl1 406807668927
    (by decide) rfl rfl (by decide +kernel)
theorem row1 : lossAt 1 = ((406807366433 : ℕ) : ℤ) :=
  verifyLevel 1 0 0 0 lvl2 406807366433
    (by decide) rfl rfl (by decide +kernel)
theorem row2 : lossAt 2 = ((406805840769 : ℕ) : ℤ) :=
  verifyLevel 2 0 0 0 lvl3 406805840769
    (by decide) rfl rfl (by decide +kernel)
theorem row3 : lossAt 3 = ((406801828613 : ℕ) : ℤ) :=
  verifyLevel 3 0 0 0 lvl4 406801828613
    (by decide) rfl rfl (by decide +kernel)
theorem row4 : lossAt 4 = ((406792529630 : ℕ) : ℤ) :=
  verifyLevel 4 0 0 0 lvl5 406792529630
    (by decide) rfl rfl (by decide +kernel)
theorem row5 : lossAt 5 = ((406776364206 : ℕ) : ℤ) :=
  verifyLevel 5 0 0 0 lvl6 406776364206
    (by decide) rfl rfl (by decide +kernel)
theorem row6 : lossAt 6 = ((406747513947 : ℕ) : ℤ) :=
  verifyLevel 6 0 0 0 lvl7 406747513947
    (by decide) rfl rfl (by decide +kernel)
theorem row7 : lossAt 7 = ((406704966049 : ℕ) : ℤ) :=
  verifyLevel 7 0 0 0 lvl8 406704966049
    (by decide) rfl rfl (by decide +kernel)
theorem row8 : lossAt 8 = ((406643039114 : ℕ) : ℤ) :=
  verifyLevel 8 0 0 0 lvl9 406643039114
    (by decide) rfl rfl (by decide +kernel)
theorem row9 : lossAt 9 = ((406550006013 : ℕ) : ℤ) :=
  verifyLevel 9 0 0 0 lvl10 406550006013
    (by decide) rfl rfl (by decide +kernel)
theorem row10 : lossAt 10 = ((406430780074 : ℕ) : ℤ) :=
  verifyLevel 10 0 0 0 lvl11 406430780074
    (by decide) rfl rfl (by decide +kernel)
theorem row11 : lossAt 11 = ((406280548509 : ℕ) : ℤ) :=
  verifyLevel 11 0 0 0 lvl12 406280548509
    (by decide) rfl rfl (by decide +kernel)
theorem row12 : lossAt 12 = ((406058725241 : ℕ) : ℤ) :=
  verifyLevel 12 0 0 0 lvl13 406058725241
    (by decide) rfl rfl (by decide +kernel)
theorem row13 : lossAt 13 = ((405805481591 : ℕ) : ℤ) :=
  verifyLevel 13 0 0 0 lvl14 405805481591
    (by decide) rfl rfl (by decide +kernel)
theorem row14 : lossAt 14 = ((405499867725 : ℕ) : ℤ) :=
  verifyLevel 14 0 0 0 lvl15 405499867725
    (by decide) rfl rfl (by decide +kernel)
theorem row15 : lossAt 15 = ((405103912903 : ℕ) : ℤ) :=
  verifyLevel 15 0 0 0 lvl16 405103912903
    (by decide) rfl rfl (by decide +kernel)
theorem row16 : lossAt 16 = ((404594894134 : ℕ) : ℤ) :=
  verifyLevel 16 0 0 0 lvl17 404594894134
    (by decide) rfl rfl (by decide +kernel)
theorem row17 : lossAt 17 = ((404071354563 : ℕ) : ℤ) :=
  verifyLevel 17 0 0 0 lvl18 404071354563
    (by decide) rfl rfl (by decide +kernel)
theorem row18 : lossAt 18 = ((403387605849 : ℕ) : ℤ) :=
  verifyLevel 18 0 0 0 lvl19 403387605849
    (by decide) rfl rfl (by decide +kernel)
theorem row19 : lossAt 19 = ((402612228476 : ℕ) : ℤ) :=
  verifyLevel 19 0 0 0 lvl20 402612228476
    (by decide) rfl rfl (by decide +kernel)
theorem row20 : lossAt 20 = ((401673594564 : ℕ) : ℤ) :=
  verifyLevel 20 0 0 0 lvl21 401673594564
    (by decide) rfl rfl (by decide +kernel)
theorem row21 : lossAt 21 = ((400601679115 : ℕ) : ℤ) :=
  verifyLevel 21 0 0 0 lvl22 400601679115
    (by decide) rfl rfl (by decide +kernel)
theorem row22 : lossAt 22 = ((399417087128 : ℕ) : ℤ) :=
  verifyLevel 22 0 0 0 lvl23 399417087128
    (by decide) rfl rfl (by decide +kernel)
theorem row23 : lossAt 23 = ((398108539546 : ℕ) : ℤ) :=
  verifyLevel 23 0 0 0 lvl24 398108539546
    (by decide) rfl rfl (by decide +kernel)
theorem row24 : lossAt 24 = ((396486665372 : ℕ) : ℤ) :=
  verifyLevel 24 0 0 0 lvl25 396486665372
    (by decide) rfl rfl (by decide +kernel)
theorem row25 : lossAt 25 = ((394671174016 : ℕ) : ℤ) :=
  verifyLevel 25 0 0 0 lvl26 394671174016
    (by decide) rfl rfl (by decide +kernel)
theorem row26 : lossAt 26 = ((392713258401 : ℕ) : ℤ) :=
  verifyLevel 26 0 0 0 lvl27 392713258401
    (by decide) rfl rfl (by decide +kernel)
theorem row27 : lossAt 27 = ((390580239024 : ℕ) : ℤ) :=
  verifyLevel 27 0 0 0 lvl28 390580239024
    (by decide) rfl rfl (by decide +kernel)
theorem row28 : lossAt 28 = ((388068397197 : ℕ) : ℤ) :=
  verifyLevel 28 0 0 0 lvl29 388068397197
    (by decide) rfl rfl (by decide +kernel)
theorem row29 : lossAt 29 = ((385325725111 : ℕ) : ℤ) :=
  verifyLevel 29 0 0 0 lvl30 385325725111
    (by decide) rfl rfl (by decide +kernel)
theorem row30 : lossAt 30 = ((382203926480 : ℕ) : ℤ) :=
  verifyLevel 30 0 0 0 lvl31 382203926480
    (by decide) rfl rfl (by decide +kernel)
theorem row31 : lossAt 31 = ((378956309467 : ℕ) : ℤ) :=
  verifyLevel 31 0 0 0 lvl32 378956309467
    (by decide) rfl rfl (by decide +kernel)
theorem row32 : lossAt 32 = ((375276582145 : ℕ) : ℤ) :=
  verifyLevel 32 0 0 0 lvl33 375276582145
    (by decide) rfl rfl (by decide +kernel)
theorem row33 : lossAt 33 = ((371243230398 : ℕ) : ℤ) :=
  verifyLevel 33 0 0 0 lvl34 371243230398
    (by decide) rfl rfl (by decide +kernel)
theorem row34 : lossAt 34 = ((367035665174 : ℕ) : ℤ) :=
  verifyLevel 34 0 0 0 lvl35 367035665174
    (by decide) rfl rfl (by decide +kernel)
theorem row35 : lossAt 35 = ((362235956609 : ℕ) : ℤ) :=
  verifyLevel 35 0 0 0 lvl36 362235956609
    (by decide) rfl rfl (by decide +kernel)
theorem row36 : lossAt 36 = ((356683635121 : ℕ) : ℤ) :=
  verifyLevel 36 0 0 0 lvl37 356683635121
    (by decide) rfl rfl (by decide +kernel)
theorem row37 : lossAt 37 = ((351185104866 : ℕ) : ℤ) :=
  verifyLevel 37 0 0 0 lvl38 351185104866
    (by decide) rfl rfl (by decide +kernel)
theorem row38 : lossAt 38 = ((345241334469 : ℕ) : ℤ) :=
  verifyLevel 38 0 0 0 lvl39 345241334469
    (by decide) rfl rfl (by decide +kernel)
theorem row39 : lossAt 39 = ((338825956114 : ℕ) : ℤ) :=
  verifyLevel 39 0 0 0 lvl40 338825956114
    (by decide) rfl rfl (by decide +kernel)
theorem row40 : lossAt 40 = ((331515950450 : ℕ) : ℤ) :=
  verifyLevel 40 0 0 0 lvl41 331515950450
    (by decide) rfl rfl (by decide +kernel)
theorem row41 : lossAt 41 = ((323847739260 : ℕ) : ℤ) :=
  verifyLevel 41 0 0 0 lvl42 323847739260
    (by decide) rfl rfl (by decide +kernel)
theorem row42 : lossAt 42 = ((315338178743 : ℕ) : ℤ) :=
  verifyLevel 42 0 0 0 lvl43 315338178743
    (by decide) rfl rfl (by decide +kernel)
theorem row43 : lossAt 43 = ((306770751605 : ℕ) : ℤ) :=
  verifyLevel 43 0 0 0 lvl44 306770751605
    (by decide) rfl rfl (by decide +kernel)
theorem row44 : lossAt 44 = ((297616053489 : ℕ) : ℤ) :=
  verifyLevel 44 0 0 0 lvl45 297616053489
    (by decide) rfl rfl (by decide +kernel)
theorem row45 : lossAt 45 = ((287265413179 : ℕ) : ℤ) :=
  verifyLevel 45 0 0 0 lvl46 287265413179
    (by decide) rfl rfl (by decide +kernel)
theorem row46 : lossAt 46 = ((276344800906 : ℕ) : ℤ) :=
  verifyLevel 46 0 0 0 lvl47 276344800906
    (by decide) rfl rfl (by decide +kernel)
theorem row47 : lossAt 47 = ((265444419908 : ℕ) : ℤ) :=
  verifyLevel 47 0 0 0 lvl48 265444419908
    (by decide) rfl rfl (by decide +kernel)
theorem row48 : lossAt 48 = ((253090797709 : ℕ) : ℤ) :=
  verifyLevel 48 0 0 0 lvl49 253090797709
    (by decide) rfl rfl (by decide +kernel)
theorem row49 : lossAt 49 = ((240163988425 : ℕ) : ℤ) :=
  verifyLevel 49 0 0 0 lvl50 240163988425
    (by decide) rfl rfl (by decide +kernel)
theorem row50 : lossAt 50 = ((226872846235 : ℕ) : ℤ) :=
  verifyLevel 50 0 0 0 lvl51 226872846235
    (by decide) rfl rfl (by decide +kernel)
theorem row51 : lossAt 51 = ((213733065358 : ℕ) : ℤ) :=
  verifyLevel 51 0 0 0 lvl52 213733065358
    (by decide) rfl rfl (by decide +kernel)
theorem row52 : lossAt 52 = ((200502414739 : ℕ) : ℤ) :=
  verifyLevel 52 0 0 0 lvl53 200502414739
    (by decide) rfl rfl (by decide +kernel)
theorem row53 : lossAt 53 = ((187943604741 : ℕ) : ℤ) :=
  verifyLevel 53 0 0 0 lvl54 187943604741
    (by decide) rfl rfl (by decide +kernel)
theorem row54 : lossAt 54 = ((175978562480 : ℕ) : ℤ) :=
  verifyLevel 54 0 0 0 lvl55 175978562480
    (by decide) rfl rfl (by decide +kernel)
theorem row55 : lossAt 55 = ((165045540417 : ℕ) : ℤ) :=
  verifyLevel 55 0 0 0 lvl56 165045540417
    (by decide) rfl rfl (by decide +kernel)
theorem row56 : lossAt 56 = ((155066797428 : ℕ) : ℤ) :=
  verifyLevel 56 0 0 0 lvl57 155066797428
    (by decide) rfl rfl (by decide +kernel)
theorem row57 : lossAt 57 = ((146226212082 : ℕ) : ℤ) :=
  verifyLevel 57 0 0 0 lvl58 146226212082
    (by decide) rfl rfl (by decide +kernel)
theorem row58 : lossAt 58 = ((138279185205 : ℕ) : ℤ) :=
  verifyLevel 58 0 0 0 lvl59 138279185205
    (by decide) rfl rfl (by decide +kernel)
theorem row59 : lossAt 59 = ((131183730148 : ℕ) : ℤ) :=
  verifyLevel 59 0 0 0 lvl60 131183730148
    (by decide) rfl rfl (by decide +kernel)
theorem row60 : lossAt 60 = ((124920014358 : ℕ) : ℤ) :=
  verifyLevel 60 0 0 0 lvl61 124920014358
    (by decide) rfl rfl (by decide +kernel)
theorem row61 : lossAt 61 = ((119520995933 : ℕ) : ℤ) :=
  verifyLevel 61 0 0 0 lvl62 119520995933
    (by decide) rfl rfl (by decide +kernel)
theorem row62 : lossAt 62 = ((115007790969 : ℕ) : ℤ) :=
  verifyLevel 62 0 0 0 lvl63 115007790969
    (by decide) rfl rfl (by decide +kernel)
theorem row63 : lossAt 63 = ((111453906383 : ℕ) : ℤ) :=
  verifyLevel 63 0 0 0 lvl64 111453906383
    (by decide) rfl rfl (by decide +kernel)
theorem row64 : lossAt 64 = ((21916193987 : ℕ) : ℤ) :=
  verifyLevel 64 3926 1640 446 lvl65 21916193987
    (by decide) rfl rfl (by decide +kernel)
theorem row65 : lossAt 65 = ((17107102763 : ℕ) : ℤ) :=
  verifyLevel 65 4012 1629 543 lvl66 17107102763
    (by decide) rfl rfl (by decide +kernel)
theorem row66 : lossAt 66 = ((0 : ℕ) : ℤ) :=
  varCertLoss_terminal _ 48 106 137 48 53 4 2756 4437 67 plainT boxes 66 (by decide)

private def losses : List ℕ := [
  406807668927, 406807366433, 406805840769, 406801828613, 406792529630, 406776364206, 406747513947, 406704966049,
  406643039114, 406550006013, 406430780074, 406280548509, 406058725241, 405805481591, 405499867725, 405103912903,
  404594894134, 404071354563, 403387605849, 402612228476, 401673594564, 400601679115, 399417087128, 398108539546,
  396486665372, 394671174016, 392713258401, 390580239024, 388068397197, 385325725111, 382203926480, 378956309467,
  375276582145, 371243230398, 367035665174, 362235956609, 356683635121, 351185104866, 345241334469, 338825956114,
  331515950450, 323847739260, 315338178743, 306770751605, 297616053489, 287265413179, 276344800906, 265444419908,
  253090797709, 240163988425, 226872846235, 213733065358, 200502414739, 187943604741, 175978562480, 165045540417,
  155066797428, 146226212082, 138279185205, 131183730148, 124920014358, 119520995933, 115007790969, 111453906383,
  21916193987, 17107102763, 0]

private theorem lossAt_eq (i : ℕ) (hi : i < 67) :
    lossAt i = ((losses.getD i 0 : ℕ) : ℤ) := by
  interval_cases i
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19
  · exact row20
  · exact row21
  · exact row22
  · exact row23
  · exact row24
  · exact row25
  · exact row26
  · exact row27
  · exact row28
  · exact row29
  · exact row30
  · exact row31
  · exact row32
  · exact row33
  · exact row34
  · exact row35
  · exact row36
  · exact row37
  · exact row38
  · exact row39
  · exact row40
  · exact row41
  · exact row42
  · exact row43
  · exact row44
  · exact row45
  · exact row46
  · exact row47
  · exact row48
  · exact row49
  · exact row50
  · exact row51
  · exact row52
  · exact row53
  · exact row54
  · exact row55
  · exact row56
  · exact row57
  · exact row58
  · exact row59
  · exact row60
  · exact row61
  · exact row62
  · exact row63
  · exact row64
  · exact row65
  · exact row66

theorem total : ∑ i ∈ Finset.range 67, lossAt i = ((20841972639983 : ℕ) : ℤ) := by
  calc
    _ = ∑ i ∈ Finset.range 67, ((losses.getD i 0 : ℕ) : ℤ) :=
      Finset.sum_congr rfl fun i hi => lossAt_eq i (Finset.mem_range.mp hi)
    _ = _ := by decide +kernel

/-- Gate loss on width 106 through 137 and index 48 through 53. -/
theorem loss (N : ℕ) :
    ∑ i ∈ Finset.range N, max 0 ((((406807694511 : ℕ)) : ℤ) - varGateDim ((((406807694511 : ℕ)) : ℤ)) 106 137 48 53 4 2756 4437 67 plainT
      (fun r => (boxes r).length) (fun r a => (boxes r).getD a none) (i+1))≤((20841972639983:ℕ):ℤ) :=
  loss_of_varCert ((((406807694511:ℕ)):ℤ)) 48 106 137 48 53 4 2756 4437 67 plainT boxes ((20841972639983:ℕ):ℤ) (by norm_num) total N

end FadicGate.Final54W0

#print axioms FadicGate.Final54W0.loss
