import ProximityPrize.SubmissionLower.SixRows4
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_2
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
private def l1v0 : List Lane := [⟨19,0,0,0,0⟩,⟨20,0,0,0,0⟩,⟨21,16,3,31,0x7f7fffff80000001⟩,⟨22,14,4,31,0xfdffffec000000340000002fefffffa⟩,⟨23,12,5,31,0x37fdffffdbfbfffef0000000700000015⟩,⟨24,10,6,31,0x3f7fffae7effffb6000001ce000001a7f7fffda7effffde⟩,⟨25,8,7,31,0x52800000d27efffedbfdfffc13fbffffcc000004600000023⟩,⟨26,6,8,31,0xfdfffc67fbfff0eff7fffc180000372000003d5fbfffe0ff7fffbe7effffec⟩,⟨27,4,9,31,0x1ce00000a8000000f1bf7ffedafefffc2dfdfffe420000024c000002300000007⟩,⟨28,2,10,31,0x3f7fff5bfefffb33fdfff43ffbfffb6c00001880000023000000047fbfffeebf7ffff77f000000⟩,⟨29,1,10,31,0x52800002ee000009ea00000d23f7fffcffefffe5dfdfffea400000010000000780000002⟩,⟨30,0,10,31,0x3f7fffe57efffedafdfffb15fbfff5dbf7fff7b80000046000000d200000077f8000007f000000⟩,⟨31,0,9,31,0xb00000088000002bc0000077000000af00000071fbffffebf7ffffbfeffffff⟩,⟨32,0,8,31,0xfe000001fbffffebf7ffff67effffdefdffffbdfbffffb3f7ffffd7f000000⟩,⟨33,0,0,0,0⟩,⟨34,0,0,0,0⟩,⟨35,0,0,0,0⟩]
private def l1v1 : List Lane := [⟨19,0,0,0,0⟩,⟨20,18,2,31,0xff000000⟩,⟨21,16,2,31,0x3f7ffff680000013⟩,⟨22,14,4,31,0xfdffff7e000002c80000005feffff98⟩,⟨23,12,5,31,0x1b8fdfffc6bfbfff4b800000a10000011f⟩,⟨24,10,6,31,0x3f7ffd1a7effffb60000167a00000ccff7ffdb87efffe3a⟩,⟨25,8,7,31,0x3180000063c7effee1ffdffd4b20000085000003b8000001b9⟩,⟨26,6,8,31,0xfdffdbebfbff7634000023700002a7e00002649fbffdf37f7ffca77efffefe⟩,⟨27,4,9,31,0x1290000067500000796bf7feec6feffd3fbfdfff12200001fd400001b500000055⟩,⟨28,2,10,31,0x3f7ff93c7effcebafdff8eb7fbfff23c000135500001856000000d3fbfff1b3f7fff8cfefffff5⟩,⟨29,1,10,31,0x37000001edc000065be00007b63f7ffbcafeffec51fdfff0f8000001b0000005d00000018⟩,⟨30,0,10,31,0x3f7ffed7fefff3a3fdffcbb1fbff96b3f7ffb228000040c000009ae0000050ff7ffff8fefffff5⟩,⟨31,0,9,31,0x78000005c800001da400005010000073f00000461fbfffe63f7fffc5feffffea⟩,⟨32,0,8,31,0xfdffffedfbfffed3f7fff8d7efffe80fdfffd01fbfffc6bf7fffda7efffff6⟩,⟨33,0,0,0,0⟩,⟨34,0,0,0,0⟩,⟨35,0,0,0,0⟩]
private def l1v2 : List Lane := [⟨19,20,1,1,1⟩,⟨20,18,1,31,0x7effffed⟩,⟨21,16,2,31,0x3f7ffff6800000be⟩,⟨22,14,4,31,0xfdfffdc600000d1bf7fff11fefffcab⟩,⟨23,12,5,31,0x861fdffe983fbffd34c00006ba00000850⟩,⟨24,10,6,31,0x3f7ff0eb8000058200007c5c00000dcbf7fed6ffefff37b⟩,⟨25,8,7,31,0x10c200001be47eff8c2dfdff20e2000090d00001b5800000bc2⟩,⟨26,6,8,31,0xfdff36ebfbfd34b40001d0a0000fef40000b019fbfee5d7f7fe89ffefff93f⟩,⟨27,4,9,31,0x69930002376000022893f7f8adcfefeff85fdffd0520000ece80000b8a0000022f⟩,⟨28,2,10,31,0x3f7fd8e6fefee8a1fdfd9eba000040500007b4400008c00fdfff36ffbff9c0ff7ffd01feffffb3⟩,⟨29,1,10,31,0x141c0000b2ac0002406c000285c3f7fddeefeff84a1fdffa90e0000116000002700000009c⟩,⟨30,0,10,31,0x3f7ff925feffb74ffdfecf57fbfda78ff7fe6ca80001cfc00003cb400001e0bf7fffbffeffffb3⟩,⟨31,0,9,31,0x2cb000022600000afa80001d7a00002a1c00001811fbfff3fff7ffe8afeffff72⟩,⟨32,0,8,31,0xfdffff7ffbfff8cff7ffd4bfefff6fbfdffedf7fbffea5ff7fff19feffffbf⟩,⟨33,0,0,0,0⟩,⟨34,0,0,0,0⟩,⟨35,0,0,0,0⟩]
private def z1 : CJ1.Block where
  bank := .rightHigh
  cap := 101
  free := [(18,0),(19,0),(20,0)]
  vectors := [l1v0,l1v1,l1v2].map (vectorData false 39 13)
private def b1 := bands [(0,20,20),(1,21,18),(2,22,16),(3,23,14),(4,24,12),(5,25,10),(6,26,8),(7,27,6),(8,28,4),(9,29,2)]
private theorem k1v0 : good false 39 l1v0 b1 := rfl
private theorem v1j0 : CJ6.VectorDots 39 13 z1 0 := v! false, 39, b1, l1v0, k1v0
private theorem k1v1 : good false 39 l1v1 b1 := rfl
private theorem v1j1 : CJ6.VectorDots 39 13 z1 1 := v! false, 39, b1, l1v1, k1v1
private theorem k1v2 : good false 39 l1v2 b1 := rfl
private theorem v1j2 : CJ6.VectorDots 39 13 z1 2 := v! false, 39, b1, l1v2, k1v2
theorem r1 : (CJ0.blockMatrix CJ6.source 39 ((13 : ℤ)-20)).rank ≤ 101 :=
  (CJ6.block_rank_le 39 13).trans (CJ6.rank_of_dots (z := z1) (by decide) (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v1j0) v1j1) v1j2))
private def l2v0 : List Lane := [⟨9,0,0,0,0⟩,⟨8,8,3,30,0x37e41d0166ed98440000001⟩,⟨7,7,5,31,0x6fc83a02855d244355fca75f6c8c8d218e6e764⟩,⟨6,6,7,31,0xa2b15c0ae34fc1946008ecb4267bd49ac505340c737579700f2141⟩,⟨5,5,9,31,0x60907403cddb3089e4c2178389531b6ce06b266956974fc8b73dc90778aa480ef23176⟩,⟨4,4,11,31,0x65d2440f11cb92b99bb6616982dbc5a2f972b09099f3494d325750cc3350a69570c13a8aeeee8419ff9ba⟩,⟨3,3,13,31,0x5158ae049c9b0cd7393619c7f15c08c046d52c0008dbfe755fd74fe41c00f7c839df87cc4194d7b9e5d73685789a4d77bcc01⟩,⟨2,2,15,31,0x28f32c11594ea4041933df17055e4c31d8ae9f81a90592100c8b2e337901af8487aaa6d42b692a07c9ac7a9da7c6db50c710e0d7241f7409a17a⟩,⟨1,1,17,31,0x4220e805ef9cb92e70e38e604b426202f097e5e1c3909732d0af302f0a3dd64693965d71044869c43c96c2a8874571d0d4c921f4a25f2b374b06f341b8efa129b7a2⟩,⟨0,0,19,31,0x1e8141419b1d8f5706eace68c58e39dfd65ee035784c9d754ab26fe2f0d9cfe96a2b232352d8ea9c79340e39a877a4ae88dc2f2a1800f925b2ff10d03be413e129b7e3d93f7ebbb00e3f⟩]
private def l2v1 : List Lane := [⟨9,9,1,1,1⟩,⟨8,9,2,31,0x29169697344b4b4f⟩,⟨7,7,5,31,0x255a5a5a867878550cf0ec7f80781b2f00eb36a⟩,⟨6,6,7,31,0x1de1e1e1fbc3c3af522d2ac62cd2a42e9566c4b3805a1d0bbb1f6c3⟩,⟨5,5,9,31,0x4ab4b4b3a45a59d4956959e8b34a1f7611d1136a44e751477194566168a1aa41db5746⟩,⟨4,4,11,31,0x7787877e9169667b44b45c186780ba32acca8a0b304fb79db8e8961ca1a5059a04b1835093cb9d9a1a510⟩,⟨3,3,13,31,0x700f0f0cef0f0e1bde1e0081de1bcac689470662cb9e4970c04e1a43472ad0845fce7d0bc337dc74b1bc9fc0354fbe35adcb3⟩,⟨2,2,15,31,0x10cf0f0e219e1dd1e8968d1bd12c699d0ce55fc476fe5e91d8f03cc65f7b1efcc02391260e98122ed451d75b7f4d421a5df93fbfc9ee423bf700d⟩,⟨1,1,17,31,0x1669696468969525fbffd0e3f7fc1977efc3649fdd1f633fa384767e940064f87b1c4dd617dc8b264e39d4073665ef519aa1b20823a191ad2983d9c0c5f1196474a3⟩,⟨0,0,19,31,0x1a25a5a4655a59ed344b3cfbfdfec84bfbec911bf70d920fe662681f8e4f1c3d6fbd8b70f9f7c0af2fb91178de77e56c574122be6d6a392a21c4b3e37fc637edb8c4a871f12c4cf68aec⟩]
private def z2 : CJ1.Block where
  bank := .leftHigh
  cap := 98
  free := [(8,2),(9,0)]
  vectors := [l2v0,l2v1].map (vectorData true 39 14)
private def b2 := bands [(36,39,1),(35,37,3),(34,35,5),(33,33,7),(32,32,8),(31,31,9),(30,30,10),(29,29,10),(28,28,10),(27,27,9),(26,26,8),(25,25,7),(24,24,6),(23,23,5),(22,22,4),(21,21,3),(20,20,2),(19,19,1)]
private theorem k2v0 : good true 39 l2v0 b2 := rfl
private theorem v2j0 : CJ6.VectorDots 39 14 z2 0 := v! true, 39, b2, l2v0, k2v0
private theorem k2v1 : good true 39 l2v1 b2 := rfl
private theorem v2j1 : CJ6.VectorDots 39 14 z2 1 := v! true, 39, b2, l2v1, k2v1
theorem r2 : (CJ0.blockMatrix CJ6.source 39 ((14 : ℤ)-20)).rank ≤ 98 :=
  (CJ6.block_rank_le 39 14).trans (CJ6.rank_of_dots (z := z2) (by decide) (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v2j0) v2j1))
private def l3v0 : List Lane := [⟨20,0,0,0,0⟩,⟨21,18,2,31,0xff000000⟩,⟨22,16,3,31,0x1fbffffd8000000100000008⟩,⟨23,14,4,31,0x6e0000008ff7fffeafeffffe5⟩,⟨24,12,5,31,0x7effff5cfdfffe2200000090000005400000038⟩,⟨25,10,6,31,0xa5000002ee000002a1fbfffac7f7fff5ffeffffbb⟩,⟨26,8,7,31,0x1fbfff8cff7ffd36fefffac10000000000000ab800000b600000038⟩,⟨27,6,8,31,0x39c00001c3800004ec00000498fdfffc2ffbfff4dff7fff82feffffe5⟩,⟨28,4,9,31,0x7efffeb7fdfff3d3fbffd367f7ffb68fefffe170000046000000690000003400000008⟩,⟨29,2,10,31,0x528000039300001020000024c0000027d00000046fdfffdd3fbfffde7f7ffff57f000000⟩,⟨30,1,10,31,0x3f7fffe57efffea3fdfff8b3fbffeb07f7ffde5fefffe5d0000000000000100000000a80000002⟩,⟨31,0,10,31,0x58000004f000001e80000069000000d90000010a000000a800000013f7ffffe7f000000⟩,⟨32,0,9,31,0x7f000000fdfffff3fbffff97f7fffe4feffffbbfdffff93fbffff97f7ffffcff000000⟩,⟨33,0,0,0,0⟩,⟨34,0,0,0,0⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩]
private def l3v1 : List Lane := [⟨20,20,1,1,1⟩,⟨21,18,1,31,0x7effffed⟩,⟨22,16,3,31,0x1fbfffefc00000380000007c⟩,⟨23,14,4,31,0x371fbffffb7f7ffe6cfefffe79⟩,⟨24,12,5,31,0x7efffa34fdfff3d200001a7000004ec000002e6⟩,⟨25,10,6,31,0x630000018d800000541fbffa187f7ff75cfefffc81⟩,⟨26,8,7,31,0x1fbffb7d7f7fe5c0feffd7f9000024c000009f40000094c000002bc⟩,⟨27,6,8,31,0x2520000118e00002d4800001b90fdffb373fbff67c7f7ff9c4fefffea9⟩,⟨28,4,9,31,0x7efff278fdff8263fbfe4467f7fd6a8fefffc2d000043d000005550000028400000061⟩,⟨29,2,10,31,0x370000025bc0000a74000016f8000016347efffba1fdffe163fbffe547f7fff74fefffff5⟩,⟨30,1,10,31,0x3f7ffed7fefff151fdffb21bfbff2387f7fea90fefff0e90000034800000d40000008100000018⟩,⟨31,0,10,31,0x3c0000035c000014b0000046e0000091400000af00000069000000023f7fffe0fefffff5⟩,⟨32,0,9,31,0x7efffff6fdffff53fbfffb37f7ffeccfefffcfffdfffb33fbfffb37f7fffd4fefffff6⟩,⟨33,0,0,0,0⟩,⟨34,0,0,0,0⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩]
private def z3 : CJ1.Block where
  bank := .rightHigh
  cap := 98
  free := [(19,0),(20,0)]
  vectors := [l3v0,l3v1].map (vectorData false 40 12)
private def b3 := bands [(0,21,20),(1,22,18),(2,23,16),(3,24,14),(4,25,12),(5,26,10),(6,27,8),(7,28,6),(8,29,4),(9,30,2)]
private theorem k3v0 : good false 40 l3v0 b3 := rfl
private theorem v3j0 : CJ6.VectorDots 40 12 z3 0 := v! false, 40, b3, l3v0, k3v0
private theorem k3v1 : good false 40 l3v1 b3 := rfl
private theorem v3j1 : CJ6.VectorDots 40 12 z3 1 := v! false, 40, b3, l3v1, k3v1
theorem r3 : (CJ0.blockMatrix CJ6.source 40 ((12 : ℤ)-20)).rank ≤ 98 :=
  (CJ6.block_rank_le 40 12).trans (CJ6.rank_of_dots (z := z3) (by decide) (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v3j0) v3j1))
end CJ6_2
end
section
namespace CJ6_2
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
private def l4v0 : List Lane := [⟨9,0,0,0,0⟩,⟨8,10,1,1,1⟩,⟨7,7,5,22,0x41001dfc0726f12d57a65677⟩,⟨6,6,7,28,0xc000016230014a3c00cf693062852a2599341bef2102⟩,⟨5,5,9,31,0x17e00005952000a705800d030b80c2729d090dd11259628cf2ec77febd3595da9⟩,⟨4,4,11,31,0x9ec00025e700047e26005a4ccc054827543eca580a682ee50420946bf033695dc4925a92c82c918c⟩,⟨3,3,13,31,0x3b70000e89e001c203c023e2a8021f9dc81973a750fb2960203f67d1733cf015d34fcafdbfa133115273ed1a3da1be65⟩,⟨2,2,15,31,0x14c80005374800a52ee00d6fcde0cf0c3009d5d9ec6244936042d556cbaaf649f5e4501cbbf4e8db085e5ccc4a9a8339b326d181e25589b8⟩,⟨1,1,17,31,0x6ec0001c8b20039e56804d0ece84bbbf6f3aa1141057a845fc1634de1be5c75e65fb28362128200817c969cb2aa326309edb42c659de307a76afe27c78f6d76⟩,⟨0,0,19,31,0x239400096ae0013976401ab42d41ad63ed15369307dcc5c0cf8b9921b296462ac1ce726be2266a1b68a18667e0cb3040372bf93e8c23d0d7e704cb421e9a0f0d278017ea4fbe3ae⟩]
private def l4v1 : List Lane := [⟨9,0,0,0,0⟩,⟨8,9,1,1,1⟩,⟨7,7,5,31,0x2a555551fdfffeedfbffde93f7fd39ffefd2989⟩,⟨6,6,7,31,0x1fbffffcea555486feffe7c9fdfe17c5fbe2eecff69c4787e1ddaf1⟩,⟨5,5,9,31,0x7effffe5fdfff975fbff3ba3f7f0ad17ef1aa42fd54e2d5f564b593c0a15c9660751ee⟩,⟨4,4,11,31,0xa955549ff7ffd377effab5d54a403effb9c4e4ff35db29fc27c1e1e6579a235286949fce01346126b8317⟩,⟨3,3,13,31,0x7effffbba9554437fbfdeda3f7d5ae8d4829316fc1f24f3e973b7a75d29798b971480947f7bd5c8680aea5b7a46ae6e75b5fa⟩,⟨2,2,15,31,0x1fbfffe7ff7ff9da7eff3d2dfdf02571fb0b9ac7ec6292cf7be50e1c0c3e8323f68c1a4e87c113a2546858dd62c311925562eea984f4e3d73b7b4⟩,⟨1,1,17,31,0x2a5554d3fdffde55fbfbbad2a4fa5fcfea693d8f9ac04127d58658e7f11fdcd072b8da9b04f9e323337e46ffba3d269c048dbad0b09cc183d0ca196fe525573924ff⟩,⟨0,0,19,31,0x1fbfffd66a554a37fefe8de9fde07796a75a3197def09706ec4d1e11bab2c4dcdc37c4ca852735a7920d54969299d72dc3933290887ad05fdc118703898a38029cff3987db93a8e99ab7⟩]
private def l4v2 : List Lane := [⟨9,0,0,0,0⟩,⟨8,8,1,1,1⟩,⟨7,7,5,30,0x152aaaab00000017f80004e00000cebf801a75⟩,⟨6,6,7,31,0xfe0000074eaaab2bf8000df7f001190fe010c09fc0cd2ebf88277e⟩,⟨5,5,9,31,0x10000003c0000070800008ca3f8083b100062540003cc60c01fd7274065be36⟩,⟨4,4,11,31,0x152aaaab4000001980000307a955924afe039245fc2a865801a1e5000d949a10414d0fa21f6f4c0d024d85⟩,⟨3,3,13,31,0x3f80000354aaab48fe0012f800018382a56c4a7001137d000aa1950058c7d8027e48460fa1b698563d3029a54da98726543e4⟩,⟨2,2,15,31,0xfe000011fc00038bf8006f77f00911c0008bdd0006a65600427f5c023153880fec8e8864dd027232bdad6ae1488b50435bcafe8ff999241101bf⟩,⟨1,1,17,31,0x54aaaab0000001340000271152adeafbf83327e0027a0c1543d8cf80d7d4a806366cac27ebc290e20eee2078d9b0fc125a5480f83f1765446d67fc866da17e436053⟩,⟨0,0,19,31,0x1952aab1080000d390001207a54bccb5dfce560f00949ad059bc027626021270f880fae59805fa4cc58f2e642e8f3d9f9de4b15f6b5c515dcc2f8dd51e6da6c46f4dd6704ebbb⟩]
private def l4v3 : List Lane := [⟨9,9,1,1,1⟩,⟨8,0,0,0,0⟩,⟨7,7,5,31,0x54aaaaaf000000e000001b90000253e00026b6b⟩,⟨6,6,7,30,0xca9555aec000150e000358680066e34009ecac00cbacde⟩,⟨5,5,9,29,0x1900001770000b00c00372a800cf693026e3b9060a1a6ccb9f9d171730bf⟩,⟨4,4,11,31,0x152aaab58000028c00004d64a95b6cb4005b853804445d302a0eee015f1df409dd69aabdd732d1568302aa⟩,⟨3,3,13,31,0x4154aaba8e0001ebb800273f02a7a8da301bf23801148c40090a7130412a415c9bbbf75eeb921553ba6252b6b1e3231⟩,⟨2,2,15,31,0x17000005c40000b67a000ed7fc00e4df800ae29c006cf0bd0398c1961a29e3e4270cb26f2785c471231608ac406547e1b41eb18fcdda7e4⟩,⟨1,1,17,31,0x54aaab2700001fd4000407f5530078180545446041506e17c2d8e7964083d02521fd3b280fa4a9919563c6c88e4d1ea7b8fbee51b6415b7fad191925e9c826b1e718⟩,⟨0,0,19,31,0x28152ab53d80015f88001deca1548ba8b017c334f0f646c20db112517f47ff63df6faa455d39476e08274060485d2eeba1f6fd32ddba7fbbd0b363c403a72033201e28a91eb2ac⟩]
private def z4 : CJ1.Block where
  bank := .leftHigh
  cap := 96
  free := [(8,0),(8,1),(8,2),(9,0)]
  vectors := [l4v0,l4v1,l4v2,l4v3].map (vectorData true 40 13)
private def b4 := bands [(36,39,2),(35,37,4),(34,35,6),(33,33,8),(32,32,9),(31,31,10),(30,30,10),(29,29,10),(28,28,9),(27,27,8),(26,26,7),(25,25,6),(24,24,5),(23,23,4),(22,22,3),(21,21,2),(20,20,1)]
private theorem k4v0 : good true 40 l4v0 b4 := rfl
private theorem v4j0 : CJ6.VectorDots 40 13 z4 0 := v! true, 40, b4, l4v0, k4v0
private theorem k4v1 : good true 40 l4v1 b4 := rfl
private theorem v4j1 : CJ6.VectorDots 40 13 z4 1 := v! true, 40, b4, l4v1, k4v1
private theorem k4v2 : good true 40 l4v2 b4 := rfl
private theorem v4j2 : CJ6.VectorDots 40 13 z4 2 := v! true, 40, b4, l4v2, k4v2
private theorem k4v3 : good true 40 l4v3 b4 := rfl
private theorem v4j3 : CJ6.VectorDots 40 13 z4 3 := v! true, 40, b4, l4v3, k4v3
theorem r4 : (CJ0.blockMatrix CJ6.source 40 ((13 : ℤ)-20)).rank ≤ 96 :=
  (CJ6.block_rank_le 40 13).trans (CJ6.rank_of_dots (z := z4) (by decide) (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v4j0) v4j1) v4j2) v4j3))
end CJ6_2
end
section
namespace CJ6_2
theorem proof : CJ6.c2 := ⟨r1, r2, r3, r4, trivial⟩
end CJ6_2
end
